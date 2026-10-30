"""App Broker: the language-agnostic orchestration layer.

    app_broker.py
        |-- command-line arguments, repository path, --entry handling
        |-- language detection  (file_detector: file -> language name)
        |-- language selection  (LANGUAGE_BROKERS: language name -> broker class)
        +-- dispatch to the selected language broker
              +-- python_broker.py   PythonBroker
              +-- html_broker.py     HTMLBroker (HTML / Django templates, design v0.1 M1-M3)
              +-- (future) c_broker.py / cpp_broker.py / java_broker.py

No language-specific analysis lives here: no AST parsing and no source-file scanning.
An entry point is a source file only (``main.py``, ``src/game.py``, ``Game.cpp``,
``src/Main.java`` ...).  The entry file path is handed to the selected broker, which analyses
the program starting from that file.

Lifecycle per entry: detect language -> construct broker -> broker.run() (language-specific analysis)
-> broker.normalized_result() -> validate (normalized.py) -> shared processing -> App Broker writes ALL
output files (OutputWriter) -> optional language hooks (functionality, top-down, report) -> summary.

Broker contract (see python_broker.py):

    broker = BrokerClass(root, entry_file, internal_hints)
    broker.run()
    broker.normalized_result()      # dict, schema patchplus.normalized (normalized.py)
    broker.reachable_count
    broker.summary_lines()
    # optional hooks: attach_trace_tree, functionality_document, topdown_document, report_text,
    #                 and the static topdown_from_trace(doc) for --from-trace
Brokers never write files.

Contract v0.3: a broker may carry its fidelity layer (ordered source lines, a broker-defined document tree, structured
issues) under ``result["extensions"][<name>]``.  App Broker writes that layer, once, as ``<name>_document.json``
(e.g. ``html_document.json``) next to the shared outputs; brokers still never touch the disk.

Cross-file traversal (default; ``--no-follow-references`` analyses only the entry files, as before):
App Broker owns ONE ``file_collector.FileCollector`` for the analysed project and shares it with the brokers.  The
entry files are queued; App Broker pops the oldest pending file (``get_next_path``), detects its language, hands it to
the matching broker, lets that broker run its existing analysis, then submits the references the broker discovered
(links, Django routes resolved through the real URLconf, imports, rendered templates) to the same collector, and asks
for the next file - until the queue is empty.  The queue never processes anything by itself and a file is analysed
at most once.  When the project root passed on the command line is only a sub-folder of a Django project (e.g. its
``templates`` directory), the nearest parent holding ``manage.py`` becomes the project root.  The results of all files
are added together (combine.py) and written ONCE: the usual output files for the whole traversal, plus
``traversal.json`` (order, why each file was visited, unresolved references).

To add a language, write ``<lang>_broker.py`` with a class following that contract and register
it in LANGUAGE_BROKERS below, e.g. ``from c_broker import CBroker`` + ``"C": CBroker``.
"""
import argparse
import json
import os
import re
import sys
from collections import OrderedDict

from broker_common import EXCLUDE_DIRS
from normalized import NormalizationError, call_site_map, ensure_valid, parse_trace, render_trace_svg, render_trace_text
from combine import CombinedBroker, merge_results
from file_collector import FileCollector
from html_broker import HTMLBroker
from python_broker import PythonBroker

# Language name (canonical, as returned by _detect_language) -> broker class.
LANGUAGE_BROKERS = {
    "Python": PythonBroker,
    "HTML": HTMLBroker,
}

# Source-file stems that conventionally start a program.  Only used when no --entry is given;
# the extension is deliberately NOT part of this list - the language detector decides it.
_ENTRY_NAME_STEMS = {"main", "__main__", "app", "index", "program", "game", "run", "server", "cli", "manage"}


class UnsupportedLanguageError(Exception):
    pass


# The Language collection stores its own spellings (e.g. "cpp"); map them onto the canonical names
# the brokers are registered under.  Unknown spellings pass through unchanged.
_LANGUAGE_ALIASES = {
    "python": "Python", "py": "Python",
    "c++": "C++", "cpp": "C++", "cxx": "C++", "cplusplus": "C++",
    "c": "C",
    "java": "Java",
    "javascript": "JavaScript", "js": "JavaScript",
    "html": "HTML", "htm": "HTML",
}

# Used only when the detector reports nothing for the file.
_EXTENSION_FALLBACK = {".html": "HTML", ".htm": "HTML"}


def detect_language(path):
    """Answer one question only: which language does this file belong to?  Returns a normalized
    name ("Python", "C", "C++", "Java", ...) or None.  No analysis of the file is performed."""
    # Imported lazily so `--from-trace` keeps working without a MongoDB connection.
    from file_detector import detect_file_type
    language = detect_file_type(path)
    if language is None:
        return _EXTENSION_FALLBACK.get(os.path.splitext(path)[1].lower())
    return _LANGUAGE_ALIASES.get(str(language).strip().lower(), language)


def discover_entry_files(root):
    """No --entry supplied: collect conventional entry files from the repository.

    A file qualifies if its stem is a conventional entry name AND the detector reports a language
    that has a registered broker.  No file extension is assumed here."""
    found = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = sorted(d for d in dirnames if d not in EXCLUDE_DIRS)
        for fn in sorted(filenames):
            if os.path.splitext(fn)[0].lower() not in _ENTRY_NAME_STEMS:
                continue
            full = os.path.join(dirpath, fn)
            try:
                lang = detect_language(full)
            except (OSError, ValueError):
                continue
            if lang in LANGUAGE_BROKERS or lang in _KNOWN_UNIMPLEMENTED:
                found.append(os.path.relpath(full, root).replace(os.sep, "/"))
    return found


# Languages the detector may report that have no broker yet.  They are still discovered/reported
# (so the user sees "<lang> broker is not implemented yet") but never analysed.
_KNOWN_UNIMPLEMENTED = {"C", "C++", "Java", "JavaScript"}


def discover_framework_roots(root):
    """Framework-aware discovery, delegated to the language brokers (no AST work here).  Each broker class
    may expose ``discover_framework_entries(root)`` returning dicts {file, role, framework, settings_module,
    covered_by}; roles are kept apart (process_entry / configuration_root) and never substituted."""
    out, seen = [], set()
    for cls in LANGUAGE_BROKERS.values():
        hook = getattr(cls, "discover_framework_entries", None)
        if hook is not None and cls not in seen:
            seen.add(cls)
            out.extend(hook(root))
    return out


def obtain_entry_specs(args):
    """Entry file paths exactly as supplied (args.entry is never modified); discovered if none given."""
    if args.entry:
        return list(args.entry)
    root = os.path.abspath(args.root)
    found = discover_entry_files(root)
    if getattr(args, "framework", "auto") != "none":
        # Framework roots: a process entry (manage.py / wsgi.py / asgi.py) is a normal executable entry; a settings
        # module is a configuration root and is only added when no discovered process entry already leads to it.
        roots = discover_framework_roots(root)
        for r in roots:
            if r["file"] in found:
                continue
            if r["role"] == "process_entry" or (r["role"] == "configuration_root" and not r["covered_by"]):
                found.append(r["file"])
        if roots:
            print("App Broker: framework roots: " + "; ".join(
                f"{r['file']} [{r['framework']} {r['role'].replace('_', ' ')}"
                + (f", reached via {r['covered_by']}" if r.get("covered_by") else "") + "]" for r in roots))
    if not found:
        raise SystemExit("No entry file found. Pass one or more --entry <source file> "
                         "(any supported language, e.g. main.py, Game.cpp, Main.java).")
    print(f"App Broker: no --entry given; discovered {len(found)} candidate entry file(s): {', '.join(found)}")
    return found


def _entry_outdir(base, entry_file, multiple):
    if not multiple:
        return base
    return os.path.join(base, re.sub(r"[^\w.-]+", "_", entry_file))


# ----------------------------------------------------------------------------------------------
# Shared processing and output writing (consumes ONLY the normalised result - see normalized.py)
# ----------------------------------------------------------------------------------------------
class OutputWriter:
    """The one authoritative writer of every output file; writing the same file twice is an error."""

    def __init__(self, outdir):
        self.outdir, self.written = outdir, []
        os.makedirs(outdir, exist_ok=True)

    def _open(self, name):
        if name in self.written:
            raise RuntimeError(f"output {name} written twice")
        self.written.append(name)
        return open(os.path.join(self.outdir, name), "w", encoding="utf-8")

    def json(self, name, obj, ensure_ascii=True):
        with self._open(name) as f:
            json.dump(obj, f, indent=2, ensure_ascii=ensure_ascii)

    def text(self, name, text):
        with self._open(name) as f:
            f.write(text)


def build_index(res):
    """index.json: one entry per symbol (ids are '<file>:<name>'; unreached function-local symbols are left out)."""
    out = {}
    for s in res["symbols"]:
        if s["scope"] == "local" and not s["reachable"]:
            continue
        key = s["id"].split(":", 1)[-1]
        okey = key + ("" if key not in out else f"@{s['file']}")
        out[okey] = {"module": s["module"], "file": s["file"], "line": s["line"], "type": s["kind"],
                     "class": s["parent"].split(":", 1)[-1] if s["parent"] else None,
                     "reachable": s["reachable"], "referenced": s["referenced"],
                     "dispatch_target": s["dispatch_target"], "reachability": s["reachability"]}
        if "configured" in s:
            out[okey]["configured"] = s["configured"]
    return out


def build_graph(res):
    edges = []
    for r in res["relationships"]:
        e = {"source": r["source"], "target": r["target"], "type": r["type"], "line": r["line"],
             **r.get("attributes", {})}
        e["file"] = r["file"]                        # keeps the position of a pre-existing 'file' attribute
        edges.append(e)
    return {"nodes": [dict(n) for n in res["nodes"]], "edges": edges}


def build_architecture(res):
    """architecture_tree.json: per participating file its classes / functions / imports."""
    rel_of = {}
    for r in res["relationships"]:
        rel_of.setdefault((r["source"], r["type"]), []).append(r)
    targets = lambda sid, ty: [r["target"] for r in rel_of.get((sid, ty), [])]
    imports = {}
    for i in res.get("imports", []):
        imports.setdefault(i["file"], []).append({k: v for k, v in i.items() if k != "file"})
    arch = {}
    for f in res["files"]:
        rel = f["path"]
        entry = {"module": f["module"], "classes": {}, "functions": {}, "imports": imports.get(rel, [])}
        if "discovered_via" in f:                    # additive, only when a framework analysis ran
            entry["execution_reached"] = f["execution_reached"]
            entry["discovered_via"] = f["discovered_via"]
        for s in res["symbols"]:
            if s["file"] != rel or s["scope"] == "local":
                continue
            if s["kind"] == "class":
                entry["classes"][s["name"]] = {
                    "line": s["line"], "inherits": targets(s["id"], "INHERITS"),
                    "methods": {m["name"]: {"line": m["line"], "calls": targets(m["id"], "CALLS")}
                                for m in res["symbols"] if m["parent"] == s["id"]}}
            elif s["kind"] == "function":
                entry["functions"][s["name"]] = {
                    "line": s["line"], "calls": targets(s["id"], "CALLS"),
                    "dispatches": [{"target": r["target"], "via": r["attributes"].get("via"),
                                    "conditions": r["attributes"].get("conditions", []),
                                    "resolution": r["attributes"].get("resolution")}
                                   for r in rel_of.get((s["id"], "DISPATCHES_TO"), [])],
                    "references": targets(s["id"], "REFERENCES")}
        if f["analysis_mode"] == "text":             # no symbols: what the text scan recognised (low confidence)
            defs = f.get("text_definitions", [])
            entry["analysis_mode"] = "text"
            entry["classes"] = {d["name"]: {"line": d["line"], "inherits": [],
                                            "methods": {m["name"]: {"line": m["line"], "calls": []}
                                                        for m in defs if m["parent"] == d["name"]}}
                                for d in defs if d["kind"] == "class"}
            entry["functions"] = {d["name"]: {"line": d["line"], "calls": []} for d in defs if d["kind"] == "function"}
            if "main_block_line" in f:
                entry["main_block_line"] = f["main_block_line"]
        arch[rel] = entry
    return arch


def build_source_documents(res):
    """Contract v0.3: per-language fidelity documents carried in ``res["extensions"]``.

    A payload qualifies when it holds ``source`` (every source line, in order) and/or ``document_tree``.  Returns
    {file name: document}; the document repeats no relationship data - that lives in graph.json."""
    docs = OrderedDict()
    for name, payload in (res.get("extensions") or {}).items():
        if not isinstance(payload, dict) or not ({"source", "document_tree"} & set(payload)):
            continue
        doc = OrderedDict([("language", res["language"]), ("project", res["project"]["name"]),
                           ("entry", res["entry"]["file"])])
        for key in ("contract", "parser", "stats", "source", "document_tree", "issues"):
            if key in payload:
                doc[key] = payload[key]
        docs[re.sub(r"[^\w.-]+", "_", str(name)) + "_document.json"] = doc
    return docs


def build_trace_document(res):
    """Language-neutral trace-tree processing: normalised trace entries -> (trace_tree document, expanded text)."""
    text = render_trace_text(res["trace"]["entries"])
    root, stats = parse_trace(text, call_site_map(res))
    doc = OrderedDict([("project", res["project"]["name"]), ("entry_point", res["entry"]["label"]),
                       ("statistics", stats), ("root", root),
                       ("language", res["language"])])        # additive: lets --from-trace pick the broker
    return doc, text


def build_source_inventory(res):
    """Complete source inventory carried by the broker(s) under ``res["extensions"][<name>]["source_inventory"]``
    (see ``PythonBroker.source_inventory``).  Independent of ``res["trace"]``: it lists every discovered
    file whether or not execution reached it.  Returns None when the broker provides no inventory."""
    files, skipped, seen = [], [], set()
    for payload in (res.get("extensions") or {}).values():
        inv = payload.get("source_inventory") if isinstance(payload, dict) else None
        if not isinstance(inv, dict):
            continue
        for f in inv.get("files", []):
            if f["path"] not in seen:
                seen.add(f["path"])
                files.append(f)
        skipped.extend(inv.get("skipped", []))
    if not files and not skipped:
        return None
    return OrderedDict([("files", files), ("skipped", skipped)])


# SVG layout of the complete source tree (monospace; one row per original source line)
_SVG_FONT, _SVG_CHAR_W, _SVG_LINE_H = 12, 7.22, 16
_SVG_PAD, _SVG_INDENT, _SVG_HEAD_H = 16, 18, 22
_XML_INVALID = re.compile(r"[\x00-\x08\x0b\x0c\x0e-\x1f\x7f\ufffe\uffff]")


def _svg_code(s):
    """Source line -> display text: tabs expanded like Python does (8), characters XML cannot carry shown as
    their control picture, markup escaped.  Nothing else is changed."""
    s = _XML_INVALID.sub(lambda m: (chr(0x2400 + ord(m.group())) if ord(m.group()) < 0x20
                                    else "\u2421" if m.group() == "\x7f" else "\ufffd"), s.expandtabs(8))
    return s.replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;")


def _svg_label(s):
    return _svg_code(str(s))


def render_source_tree_svg(res, inventory):
    """The COMPLETE source tree as SVG: project directory tree -> files -> every original line with its line
    number.  Built only from ``inventory`` (build_source_inventory); the execution trace plays no part."""
    tree = {"dirs": OrderedDict(), "files": []}
    for f in sorted(inventory["files"], key=lambda f: f["path"].split("/")):
        node = tree
        for d in f["path"].split("/")[:-1]:
            node = node["dirs"].setdefault(d, {"dirs": OrderedDict(), "files": []})
        node["files"].append(f)
    rows = []                                                  # ("dir" | "file", depth, payload)

    def walk(node, depth):
        for name, sub in node["dirs"].items():
            rows.append(("dir", depth, name + "/"))
            walk(sub, depth + 1)
        for f in node["files"]:
            rows.append(("file", depth, f))
    walk(tree, 1)

    n_files = len(inventory["files"])
    n_lines = sum(f["line_count"] for f in inventory["files"])
    title = f"{res['project']['name']} - complete source tree"
    summary = f"{n_files} file(s), {n_lines} line(s); entry: {res['entry']['label']}"
    heads = {}                                                 # id(file) -> header text
    width = max(len(title) * _SVG_CHAR_W * 1.3, len(summary) * _SVG_CHAR_W) + 2 * _SVG_PAD
    for kind, depth, p in rows:
        x0 = _SVG_PAD + depth * _SVG_INDENT
        if kind == "dir":
            width = max(width, x0 + len(p) * _SVG_CHAR_W + _SVG_PAD)
            continue
        heads[id(p)] = (f"{p['path']}   {p['line_count']} line(s)   {p['analysis_mode']}   "
                        + ("reached by execution" if p["reached"] else "not reached by execution"))
        gutter = len(str(max(p["line_count"], 1))) * _SVG_CHAR_W
        longest = max((len(l.expandtabs(8)) for l in p["lines"]), default=0)
        width = max(width, x0 + gutter + 14 + longest * _SVG_CHAR_W + _SVG_PAD,
                    x0 + len(heads[id(p)]) * _SVG_CHAR_W + 2 * _SVG_PAD)
    width = int(width) + 1

    out, y = [], _SVG_PAD + 2 * _SVG_LINE_H + 8
    for kind, depth, p in rows:
        x0 = _SVG_PAD + depth * _SVG_INDENT
        if kind == "dir":
            out.append(f'<text class="dir" x="{x0 - _SVG_INDENT // 2}" y="{y + 12}">+ {_svg_label(p)}</text>')
            y += _SVG_LINE_H + 4
            continue
        out.append(f'<rect class="head" x="{x0}" y="{y}" width="{width - x0 - _SVG_PAD}" height="{_SVG_HEAD_H}" rx="3"/>')
        out.append(f'<text class="file" x="{x0 + 8}" y="{y + 15}">{_svg_label(heads[id(p)])}</text>')
        y += _SVG_HEAD_H
        n = p["line_count"]
        if n == 0:
            out.append(f'<text class="note" x="{x0 + 8}" y="{y + 12}">(empty file)</text>')
            y += _SVG_LINE_H + 8
            continue
        gutter = len(str(n)) * _SVG_CHAR_W
        code_x = x0 + gutter + 14
        out.append(f'<rect class="panel" x="{x0}" y="{y}" width="{width - x0 - _SVG_PAD}" height="{n * _SVG_LINE_H}"/>')
        out.append(f'<line class="rule" x1="{code_x - 6:.1f}" y1="{y}" x2="{code_x - 6:.1f}" y2="{y + n * _SVG_LINE_H}"/>')
        for i, text in enumerate(p["lines"], 1):
            base = y + (i - 1) * _SVG_LINE_H + 12
            out.append(f'<text class="ln" x="{x0 + gutter + 2:.1f}" y="{base}" text-anchor="end">{i}</text>')
            if text.strip():
                out.append(f'<text class="src" x="{code_x:.1f}" y="{base}">{_svg_code(text)}</text>')
        y += n * _SVG_LINE_H + 8
    if inventory["skipped"]:
        out.append(f'<text class="dir" x="{_SVG_PAD}" y="{y + 12}">Found but not readable (not in the tree):</text>')
        y += _SVG_LINE_H + 4
        for s in inventory["skipped"]:
            out.append(f'<text class="note" x="{_SVG_PAD + _SVG_INDENT}" y="{y + 12}">{_svg_label(s["file"])}: {_svg_label(s["error"])}</text>')
            y += _SVG_LINE_H
    height = int(y + _SVG_PAD)
    head = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height}" viewBox="0 0 {width} {height}" '
        f'xml:space="preserve" font-family="DejaVu Sans Mono, Menlo, Consolas, monospace" font-size="{_SVG_FONT}">',
        f'<title>{_svg_label(title)}</title>',
        '<style>',
        '.bg{fill:#ffffff}.panel{fill:#f7f8fa;stroke:#d5d9e0}.head{fill:#e4e9f2}.rule{stroke:#d5d9e0}',
        '.ln{fill:#8a93a3}.src,.file,.dir,.sum{fill:#1f2430;white-space:pre}.file{font-weight:bold}.dir{font-weight:bold;fill:#2b4c8c}',
        '.note{fill:#6b7280;font-style:italic}.ttl{font-size:15px;font-weight:bold;fill:#1f2430}',
        '@media (prefers-color-scheme: dark){.bg{fill:#14161b}.panel{fill:#1b1e25;stroke:#2d323d}.head{fill:#262b36}',
        '.rule{stroke:#2d323d}.ln{fill:#6b7385}.src,.file,.sum,.ttl{fill:#e3e6ec}.dir{fill:#8fb2ff}.note{fill:#9aa3b2}}',
        '.src{white-space:pre}',
        '</style>',
        f'<rect class="bg" x="0" y="0" width="{width}" height="{height}"/>',
        f'<text class="ttl" x="{_SVG_PAD}" y="{_SVG_PAD + 12}">{_svg_label(title)}</text>',
        f'<text class="sum" x="{_SVG_PAD}" y="{_SVG_PAD + 12 + _SVG_LINE_H}">{_svg_label(summary)}</text>',
    ]
    return "\n".join(head + out + ["</svg>", ""])


def render_basic_report(res):
    """Schema-only report, used when a broker offers no report_text() of its own."""
    bar = "=" * 78
    a = res["analysis"]
    reached = sum(1 for s in res["symbols"] if s["reachable"])
    o = [bar, "PATCHPLUS APP BROKER - EXECUTION MAP", bar,
         f"Language      : {res['language']}", f"Project root  : {res['project']['root']}",
         f"Entry point   : {res['entry']['label']}  [{res['entry']['kind']}]",
         f"Analysis mode : {a['mode']}" + ("  (partial)" if a["partial"] else ""),
         f"Files         : {len(res['files'])}", f"Reachable symbols : {reached} of {len(res['symbols'])}",
         f"Relationships : {len(res['relationships'])}", f"Unresolved references : {len(res.get('unresolved', []))}"]
    o += [f"  note: {n}" for n in a["notes"]]
    return "\n".join(o) + "\n"


def _guarded(label, fn):
    """Additive stages must never break the other outputs."""
    try:
        return fn()
    except Exception:
        import traceback
        print(f"WARNING: {label} failed; other outputs are unaffected.", file=sys.stderr)
        traceback.print_exc()
        return None


def _write_topdown(w, out):
    w.json("topdown_functionalities.json", out["result"], ensure_ascii=False)
    w.text("topdown_functionalities.txt", out["text"])
    st = out["result"]["statistics"]
    print("PATCHPLUS TOP-DOWN FUNCTIONALITY EXTRACTION")
    print("-------------------------------------------")
    print(f"Functionalities      : {st['functionalities']}")
    print(f"Child operations     : {st['child_operations']}")
    print(f"Code nodes accounted : {st['code_nodes_accounted']} / {st['code_nodes']}")
    print(f"Maximum path depth   : {st['max_path_depth']}")


def write_outputs(res, broker, outdir):
    """Steps 6-8 of the lifecycle: shared processing, shared outputs, then the language hooks' outputs."""
    w = OutputWriter(outdir)
    w.json("index.json", build_index(res))
    w.json("graph.json", build_graph(res))
    w.json("execution_tree.json", res.get("execution_tree", []))
    w.json("architecture_tree.json", build_architecture(res))
    if "framework" in res:                           # framework-specific document, written verbatim
        w.json("framework_architecture.json", res["framework"]["document"])

    def source_documents():
        for fname, sdoc in build_source_documents(res).items():
            w.json(fname, sdoc, ensure_ascii=False)
            src, nodes = sdoc.get("source", {}), sdoc.get("document_tree", {}).get("node_counts", {})
            print(f"PATCHPLUS SOURCE + TREE ({fname})")
            print("-" * (len(fname) + 26))
            print(f"Source lines         : {src.get('line_count', 0)} ({src.get('encoding', '?')})")
            print(f"Tree nodes           : {sum(nodes.values())}")
            print(f"Issues               : {len(sdoc.get('issues', []))}")
    _guarded("source/tree documents", source_documents)

    doc, text = build_trace_document(res)
    w.text("expanded_trace.txt", text)
    w.json("trace_tree.json", doc)
    w.text("trace_tree.svg", render_trace_svg(doc))          # execution trace only (unchanged)

    def source_tree():                                       # complete source tree: NOT derived from the trace
        inv = build_source_inventory(res)
        if inv is None:
            return
        w.text("source_tree.svg", render_source_tree_svg(res, inv))
        print("PATCHPLUS SOURCE TREE (source_tree.svg)")
        print("---------------------------------------")
        print(f"Files                : {len(inv['files'])}")
        print(f"Source lines         : {sum(f['line_count'] for f in inv['files'])}")
        print(f"Not readable         : {len(inv['skipped'])}")
    _guarded("source tree SVG", source_tree)
    st = doc["statistics"]
    print("PATCHPLUS TRACE TREE")
    print("--------------------")
    print(f"Trace entries        : {st['trace_entries']}")
    print(f"Code nodes           : {st['code_nodes']}")
    print(f"References           : {st['references']}")
    print(f"Maximum depth        : {st['max_depth']}")
    print(f"Root nodes           : {st['root_nodes']}")
    if hasattr(broker, "attach_trace_tree"):
        broker.attach_trace_tree(doc["root"], st)

    def functionality():
        res["functionality"] = broker.functionality_document()
        w.json("functionality.json", res["functionality"])
    if hasattr(broker, "functionality_document"):
        _guarded("functionality analysis", functionality)

    def topdown():
        res["topdown"] = broker.topdown_document()
        _write_topdown(w, res["topdown"])
    if hasattr(broker, "topdown_document"):
        _guarded("top-down functionality extraction", topdown)

    def project_graph():
        w.json("project_graph.json", broker.project_graph_document())
    if hasattr(broker, "project_graph_document"):
        _guarded("project graph", project_graph)

    w.text("report.txt", broker.report_text() if hasattr(broker, "report_text") else render_basic_report(res))
    return w.written


def run_from_trace(trace_tree_json, outdir):
    """--from-trace: top-down extraction on an existing trace_tree.json, through the broker for its language."""
    with open(trace_tree_json, "r", encoding="utf-8") as fh:
        doc = json.load(fh)
    if not isinstance(doc, dict) or not isinstance(doc.get("root"), dict) or "children" not in doc["root"]:
        raise SystemExit(f"{trace_tree_json} is not a trace_tree.json document")
    language = doc.get("language", "Python")          # files written before the key existed are Python traces
    hook = getattr(LANGUAGE_BROKERS.get(language), "topdown_from_trace", None)
    if hook is None:
        raise SystemExit(f"App Broker: no top-down extraction is available for {language} traces")
    _write_topdown(OutputWriter(outdir), hook(doc))


def _run_broker(broker, outdir):
    """Shared tail of a single-file dispatch: run -> normalise -> validate -> write outputs -> summary."""
    broker.run()
    result = ensure_valid(broker.normalized_result())
    write_outputs(result, broker, outdir)
    print(f"App Broker: outputs written to {outdir}/")
    for line in broker.summary_lines():
        print(line)
    return broker.reachable_count


def dispatch_entry(root, entry_file, internal, outdir, framework="auto", arch_depth=1):
    """One entry: file -> language (file_detector) -> broker class (LANGUAGE_BROKERS) -> run."""
    path = os.path.join(root, entry_file)
    if not os.path.isfile(path):
        path = entry_file                      # fall back to a cwd-relative path
    if not os.path.isfile(path):
        raise SystemExit(f"Entry file not found: {entry_file} (looked under {root})")

    language = detect_language(path)
    if language is None:
        raise UnsupportedLanguageError(f"Could not determine the programming language of {entry_file}")

    print(f"App Broker: {entry_file} -> {language}")
    broker_class = LANGUAGE_BROKERS.get(language)
    if broker_class is None:
        raise UnsupportedLanguageError(f"{language} broker is not implemented yet")

    print(f"App Broker: using {language} broker")
    kwargs = {}
    if getattr(broker_class, "SUPPORTS_FRAMEWORK_ANALYSIS", False):     # additive options, only for brokers that take them
        kwargs = dict(framework=framework, arch_depth=arch_depth)
    return _run_broker(broker_class(root, entry_file, internal, **kwargs), outdir)


def _dispatch_entry_guarded(entry_file, multiple, **kw):
    """dispatch_entry with the established per-entry error reporting.  True = analysed, False = failed."""
    try:
        dispatch_entry(entry_file=entry_file, **kw)
        return True
    except NormalizationError as e:
        print(f"App Broker: failed {entry_file}: {e}", file=sys.stderr)
    except UnsupportedLanguageError as e:
        print(f"App Broker: {e}" if "not implemented yet" in str(e) else f"App Broker: skipped {entry_file}: {e}",
              file=sys.stderr)
    except SystemExit as e:
        if multiple and e.code not in (None, 0):
            print(f"App Broker: failed {entry_file}: {e.code}", file=sys.stderr)
        else:
            raise
    return False


# ----------------------------------------------------------------------------------------------
# Cross-file traversal: App Broker owns the loop, the FileCollector owns the queue
# ----------------------------------------------------------------------------------------------
DEFAULT_MAX_FILES = 500                      # safety cap on files analysed in one traversal
_PROJECT_MARKERS = ("manage.py",)            # a Django project root


def find_project_root(root, limit=6):
    """The directory that holds the whole project.  ``root`` itself when it has a project marker; otherwise the
    nearest parent that has one (the user passed e.g. the ``templates`` folder of a Django project, whose URLconf
    and views live above it); otherwise ``root`` unchanged."""
    d = os.path.abspath(root)
    for _ in range(limit):
        if any(os.path.isfile(os.path.join(d, m)) for m in _PROJECT_MARKERS):
            return d
        parent = os.path.dirname(d)
        if parent == d:
            break
        d = parent
    return os.path.abspath(root)


def rebase_entries(old_root, new_root, entry_files):
    """Entry paths given relative to ``old_root`` -> relative to ``new_root`` ('/' separators)."""
    out = []
    for spec in entry_files:
        full = spec if os.path.isabs(spec) else os.path.join(old_root, spec)
        try:
            inside = os.path.isfile(full) and os.path.commonpath([os.path.abspath(full), new_root]) == new_root
        except ValueError:                                    # different drives (Windows)
            inside = False
        out.append(os.path.relpath(os.path.abspath(full), new_root).replace(os.sep, "/") if inside else spec)
    return out


class _BrokerFactory:
    """Builds the broker for a file taken from the queue.  A broker class that offers ``fork_for_file``
    (PythonBroker) is indexed ONCE on an index-only owner and every file gets a fork that shares that index, so a
    repository with N files is not re-indexed N times."""

    def __init__(self, root, internal, collector, framework, arch_depth):
        self.root, self.internal, self.collector = root, internal, collector
        self.framework, self.arch_depth = framework, arch_depth
        self._owners = {}

    def _kwargs(self, broker_class):
        kwargs = {}
        if getattr(broker_class, "SUPPORTS_FRAMEWORK_ANALYSIS", False):
            kwargs = dict(framework=self.framework, arch_depth=self.arch_depth)
        if getattr(broker_class, "SUPPORTS_COLLECTOR", False):
            kwargs["collector"] = self.collector                      # the ONE collector owned by App Broker
        return kwargs

    def make(self, broker_class, rel, focus=None):
        kwargs = self._kwargs(broker_class)
        if hasattr(broker_class, "fork_for_file"):
            owner = self._owners.get(broker_class)
            if owner is None:
                owner = broker_class(self.root, rel, self.internal, **kwargs)
                owner.index_repository()
                self._owners[broker_class] = owner
            return owner.fork_for_file(rel, focus=focus)
        return broker_class(self.root, rel, self.internal, **kwargs)


def _focus_names(collector, path):
    """Functions / classes of ``path`` that URL routes point at (from the origins of the queued file)."""
    names = []
    for o in collector.origins_of(path):
        m = o.get("meta") or {}
        if m.get("role") == "view" and m.get("view_symbol") and m["view_symbol"] not in names:
            names.append(m["view_symbol"])
    return names


def _analyse_queued(factory, root, rel, record, focus):
    """Dispatch ONE file taken from the queue; fills ``record`` and returns (broker, validated result) or None.
    Never raises for a bad file: it is recorded and the traversal continues."""
    try:
        language = detect_language(os.path.join(root, rel))
        record["language"] = language
        if language is None:
            record.update(status="skipped", reason="no broker handles this file type (language not detected)")
            return None
        broker_class = LANGUAGE_BROKERS.get(language)
        if broker_class is None:
            record.update(status="skipped", reason=f"{language} broker is not implemented yet")
            print(f"App Broker: {language} broker is not implemented yet ({rel})", file=sys.stderr)
            return None
        print(f"App Broker: {rel} -> {language}" + (" (entry)" if record["entry"] else " (discovered)"))
        broker = factory.make(broker_class, rel, focus=focus)
        broker.run()
        result = ensure_valid(broker.normalized_result())
        for line in broker.summary_lines():
            print(line)
        if hasattr(broker, "discovered_references"):
            record["references"] = broker.discovered_references()
            before = len(factory.collector.rejected())
            record["queued_references"] = broker.submit_discovered_references()   # -> the same collector
            refs = record["references"]
            print(f"  queue: +{record['queued_references']} new file(s) from {len(refs)} reference(s); "
                  f"{sum(r['disposition'] == 'unresolved' for r in refs)} unresolved, "
                  f"{sum(r['disposition'] in ('external', 'static_asset', 'ignored') for r in refs)} external/static/ignored; "
                  f"{factory.collector.pending_count()} waiting")
            for rej in factory.collector.rejected()[before:]:                     # never lose a refusal silently
                print(f"  REJECTED by collector: {rej['reference']!r} - {rej['reason']}", file=sys.stderr)
            for r in refs:
                if r["disposition"] == "queue" and r["files"]:
                    print(f"  line {r['line']}: {r['reference']}  ->  " + "  ->  ".join(r["files"]))
                elif r["disposition"] == "unresolved":
                    print(f"  line {r['line']}: {r['reference']}  ->  UNRESOLVED: {r['reason']}")
        record["status"] = "analysed"
        return broker, result
    except (NormalizationError, UnsupportedLanguageError) as e:
        record.update(status="failed", reason=str(e))
    except SystemExit as e:                                   # brokers report some conditions this way
        record.update(status="failed", reason=str(e.code))
    except Exception as e:                                    # one bad file must not stop the traversal
        record.update(status="failed", reason=f"{type(e).__name__}: {e}")
    print(f"App Broker: failed {rel}: {record['reason']}", file=sys.stderr)
    return None


def traverse(root, entry_files, internal, outdir, framework="auto", arch_depth=1, max_files=DEFAULT_MAX_FILES,
             requested_root=None):
    """The traversal loop.  Returns (failed entry specs, traversal document).

    1. ONE FileCollector for the project.   2. Queue the entry files.   3. get_next_path() -> oldest pending file.
    4. Detect the language and hand the file to its broker.   5. The broker runs its existing analysis.
    6. Its discovered references go to the same collector.   7. Repeat until get_next_path() is None.
    8. Add all results together and write the usual outputs once."""
    collector = FileCollector(root)
    multiple = len(entry_files) > 1
    entries, outside, failures, records, members = OrderedDict(), [], [], [], []

    for spec in entry_files:
        full = os.path.join(root, spec)
        resolved = collector.resolve_path(full if os.path.isfile(full) else spec)
        if resolved is None:
            outside.append(spec)                              # not a project file: handled like before, no traversal
        else:
            entries.setdefault(resolved, spec)
            collector.add_path(resolved, source_broker="python", original_reference=spec)

    for spec in outside:
        if not _dispatch_entry_guarded(spec, multiple, root=root, internal=internal, outdir=_entry_outdir(outdir, spec, multiple),
                                       framework=framework, arch_depth=arch_depth):
            failures.append(spec)

    factory = _BrokerFactory(root, internal, collector, framework, arch_depth)
    limited = False
    while True:
        if len(records) >= max_files and collector.has_pending_paths():
            limited = True
            print(f"App Broker: stopped after {max_files} files (--max-files); "
                  f"{collector.pending_count()} reference(s) still pending", file=sys.stderr)
            break
        path = collector.get_next_path()
        if path is None:
            break
        rel = path.relative_to(collector.project_root).as_posix()
        record = OrderedDict(file=rel, entry=path in entries, status=None, language=None, reason=None,
                             discovered_via=collector.origins_of(path), queued_references=0, references=[])
        records.append(record)
        got = _analyse_queued(factory, root, rel, record, None if record["entry"] else _focus_names(collector, path) or None)
        if got is None:
            if record["entry"] and record["status"] == "failed":
                failures.append(entries[path])
            continue
        record["broker"], record["result"] = got
        members.append(record)

    unresolved = [OrderedDict(file=r["source_file"], line=r.get("line"), reference=r["reference"], kind=r.get("kind"),
                              reason=r.get("reason")) for rec in records for r in rec["references"]
                  if r.get("disposition") == "unresolved"]
    links = [OrderedDict(source_file=o.get("source_file"), line=(o.get("meta") or {}).get("line"),
                         reference=o.get("reference"), via=o.get("source_broker"), target=rec["file"],
                         role=(o.get("meta") or {}).get("role")) for rec in records for o in rec["discovered_via"]
             if o.get("source_file")]
    clean = [OrderedDict((k, v) for k, v in rec.items() if k not in ("broker", "result")) for rec in records]
    doc = OrderedDict(
        root=root, requested_root=requested_root or root, entries=list(entry_files), files=clean, links=links,
        unresolved=unresolved, rejected=collector.rejected(),
        not_analysed=collector.snapshot()["pending"] if limited else [],
        statistics=OrderedDict(
            files_visited=len(records), analysed=sum(r["status"] == "analysed" for r in records),
            skipped=sum(r["status"] == "skipped" for r in records), failed=sum(r["status"] == "failed" for r in records),
            discovered=sum(not r["entry"] for r in records), unresolved_references=len(unresolved),
            rejected_references=len(collector.rejected()), stopped_by_max_files=limited))

    if members:                                               # 8. one result, one set of outputs
        if len(members) == 1:
            broker, result = members[0]["broker"], members[0]["result"]
        else:
            result = ensure_valid(merge_results(members))
            broker = CombinedBroker(members, result, doc, build_trace_document, render_basic_report)
        write_outputs(result, broker, outdir)
        print(f"App Broker: outputs written to {outdir}/")
    OutputWriter(outdir).json("traversal.json", doc, ensure_ascii=False)
    st = doc["statistics"]
    print("PATCHPLUS TRAVERSAL (traversal.json)")
    print("------------------------------------")
    print(f"Files visited        : {st['files_visited']} ({st['discovered']} discovered by references)")
    print(f"Analysed / skipped / failed : {st['analysed']} / {st['skipped']} / {st['failed']}")
    print(f"Unresolved references: {st['unresolved_references']}")
    print(f"Rejected by collector: {st['rejected_references']}"
          + ("  (see 'rejected' in traversal.json)" if st['rejected_references'] else ""))
    return failures, doc


def main():
    ap = argparse.ArgumentParser(description="PatchPlus App Broker v2")
    ap.add_argument("root", nargs="?", default=".")
    ap.add_argument("--entry", action="append", default=None, metavar="SOURCE_FILE",
                    help="a source file in any supported language (main.py, Game.cpp, main.c, Main.java, "
                         "app.js, ...) used as the starting point of the analysis; repeat the option for "
                         "several entry points. The language is detected automatically. If omitted, "
                         "conventional entry files are discovered in the repository")
    ap.add_argument("--internal", nargs="*", default=[],
                    help="top-level names that belong to this project (even if files are missing)")
    ap.add_argument("--framework", default="auto", choices=["auto", "django", "none"],
                    help="configuration-driven architecture analysis (settings / URL includes / installed apps / "
                         "middleware), recorded separately from the execution trace. auto = only when the entry "
                         "file shows framework configuration; none = disabled; django = require Django")
    ap.add_argument("--arch-depth", type=int, default=1, metavar="N",
                    help="import hops followed from configuration-discovered files (default 1)")
    ap.add_argument("--follow-references", action=argparse.BooleanOptionalAction, default=True,
                    help="cross-file traversal (default on): files referenced by analysed files (links, Django routes "
                         "resolved through the real URL configuration, imports, rendered templates) are queued in ONE "
                         "shared FileCollector and analysed in FIFO order, each at most once; the results are added "
                         "together and written once, plus <outdir>/traversal.json. --no-follow-references analyses "
                         "only the entry files")
    ap.add_argument("--max-files", type=int, default=DEFAULT_MAX_FILES, metavar="N",
                    help=f"with --follow-references: stop after N files (default {DEFAULT_MAX_FILES})")
    ap.add_argument("--outdir", default="patchplus_broker")
    ap.add_argument("--from-trace", metavar="TRACE_TREE_JSON",
                    help="skip the repository analysis; run ONLY the top-down functionality extraction "
                         "on an existing trace_tree.json")
    args = ap.parse_args()

    if args.from_trace:
        run_from_trace(args.from_trace, args.outdir)
        print(f"App Broker: top-down functionalities written to {args.outdir}/")
        return

    root = os.path.abspath(args.root)
    entry_files = obtain_entry_specs(args)
    multiple = len(entry_files) > 1

    if args.follow_references:
        project_root = find_project_root(root)
        if project_root != root:
            print(f"App Broker: project root is {project_root} (found {_PROJECT_MARKERS[0]} above {root}); "
                  f"references are resolved against the whole project")
            entry_files = rebase_entries(root, project_root, entry_files)
        failures, _doc = traverse(project_root, entry_files, args.internal, args.outdir, framework=args.framework,
                                  arch_depth=args.arch_depth, max_files=args.max_files, requested_root=root)
    else:
        failures = []
        for entry_file in entry_files:                 # each entry file is detected + routed independently
            if not _dispatch_entry_guarded(entry_file, multiple, root=root, internal=args.internal,
                                           outdir=_entry_outdir(args.outdir, entry_file, multiple),
                                           framework=args.framework, arch_depth=args.arch_depth):
                failures.append(entry_file)
    if failures:
        raise SystemExit(f"App Broker: {len(failures)} of {len(entry_files)} entry file(s) not analysed")


if __name__ == "__main__":
    main()
