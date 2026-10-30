"""Combine the per-file results of a cross-file traversal into ONE result (and one set of output documents).

App Broker analyses the files of a traversal one at a time, each with the broker of its language.  Every broker
hands back its normalised result (schema ``patchplus.normalized``, see normalized.py).  This module adds those
results together; it contains no language-specific analysis and no file writing:

    merge_results(records)         -> one normalised result (symbols / relationships / nodes / files / imports /
                                      dependencies / unresolved / extensions ... unioned, trace nested by reference)
    CombinedBroker(records, ...)   -> the optional broker hooks App Broker's write_outputs() calls
                                      (attach_trace_tree, functionality_document, topdown_document,
                                      project_graph_document, report_text), each one delegating to the member
                                      brokers and adding their documents together.

A *record* is a dict: file (project-relative), entry (bool), result (normalised), broker, language,
discovered_via ([{reference, source_broker, source_file, meta}]), status.
"""
import copy
from collections import OrderedDict, defaultdict


# ----------------------------------------------------------------------------------------------
# normalised results
# ----------------------------------------------------------------------------------------------
def _union(target, items, key):
    seen = {key(x) for x in target}
    for x in items:
        k = key(x)
        if k not in seen:
            seen.add(k)
            target.append(x)


def _merge_python_payload(dst, src):
    for k, v in src.items():
        if k == "fallback_resolutions":
            _union(dst.setdefault(k, []), v, lambda x: (x.get("module"), x.get("from"), x.get("target")))
        elif k == "source_inventory":
            inv = dst.setdefault(k, {"files": [], "skipped": []})
            by_path = {f["path"]: f for f in inv["files"]}
            for f in v.get("files", []):
                if f["path"] in by_path:
                    by_path[f["path"]]["reached"] = bool(by_path[f["path"]].get("reached") or f.get("reached"))
                else:
                    inv["files"].append(copy.deepcopy(f))
                    by_path[f["path"]] = inv["files"][-1]
            _union(inv["skipped"], v.get("skipped", []), lambda x: (x.get("file"), x.get("error")))
        else:
            dst.setdefault(k, copy.deepcopy(v))


def merge_traces(records):
    """Trace entries of every file as ONE tree: a discovered file's entries hang below the line of the file
    that referenced it (the REFERENCE line of a template, the import / render call of a view)."""
    by_file = {r["file"]: r for r in records}
    kids = defaultdict(list)                                  # (parent file, line | None) -> [child files]
    parent_of = {}
    for r in records:
        if r["entry"]:
            continue
        for o in r.get("discovered_via") or []:
            src = o.get("source_file")
            if src in by_file and src != r["file"]:
                kids[(src, (o.get("meta") or {}).get("line"))].append(r["file"])
                parent_of[r["file"]] = src
                break
    entries_of = {r["file"]: r["result"]["trace"]["entries"] for r in records}
    out, emitted = [], set()

    def emit(file, base):
        if file in emitted:
            return
        emitted.add(file)
        ents = entries_of[file]
        last = {}
        for i, e in enumerate(ents):
            if e.get("file") == file:
                last[e.get("line")] = i
        attach = defaultdict(list)
        for (pf, line), children in kids.items():
            if pf == file:
                attach[last.get(line, len(ents) - 1)] += children
        for i, e in enumerate(ents):
            out.append(dict(e, depth=e["depth"] + base))
            for child in attach.get(i, []):
                emit(child, base + e["depth"] + 1)

    for r in records:
        if r["file"] not in parent_of:
            emit(r["file"], 0)
    for r in records:                                         # anything still unplaced (cycle): keep it, at the top
        emit(r["file"], 0)
    return out


def merge_results(records):
    """Add the normalised results of all analysed files together (see module docstring)."""
    first = records[0]["result"]
    res = copy.deepcopy(first)
    for key in ("files", "symbols", "relationships", "nodes", "dependencies", "unresolved", "execution_tree"):
        res[key] = []
    res["imports"] = []
    res["extensions"] = {}
    res["trace"] = {"entries": [], "call_categories": []}
    notes, text_files, parse_errors, modes, partial = [], set(), [], set(), False
    html_seen = 0
    sym_at = {}

    for rec in records:
        r = copy.deepcopy(rec["result"])
        for f in r["files"]:
            old = next((x for x in res["files"] if x["path"] == f["path"]), None)
            if old is None:
                res["files"].append(f)
            else:
                old["reached"] = bool(old.get("reached") or f.get("reached"))
        for s in r["symbols"]:
            old = sym_at.get(s["id"])
            if old is None:
                sym_at[s["id"]] = s
                res["symbols"].append(s)
            else:
                for flag in ("reachable", "referenced", "dispatch_target"):
                    old[flag] = bool(old.get(flag) or s.get(flag))
                if s.get("reachable") and not old.get("reachability") in ("direct",):
                    old["reachability"] = s.get("reachability", old.get("reachability"))
                if s.get("configured"):
                    old["configured"] = True
        _union(res["relationships"], r["relationships"],
               lambda x: (x["source"], x["target"], x["type"], x.get("line"), x.get("file")))
        _union(res["nodes"], r["nodes"], lambda x: x["id"])
        _union(res["imports"], r.get("imports", []),
               lambda x: (x["file"], x.get("alias"), x.get("module"), x.get("name"), x.get("level"), x.get("line")))
        for d in r["dependencies"]:
            old = next((x for x in res["dependencies"] if (x["module"], x["category"]) == (d["module"], d["category"])), None)
            if old is None:
                res["dependencies"].append(d)
            else:
                old["references"] = sorted(set(old["references"]) | set(d["references"]))
        _union(res["unresolved"], r["unresolved"], lambda x: (x["file"], x.get("line"), x["reference"]))
        res["execution_tree"].extend(r.get("execution_tree", []))
        _union(res["trace"]["call_categories"], r["trace"].get("call_categories", []),
               lambda x: (x["file"], x["line"]))
        for name, payload in (r.get("extensions") or {}).items():
            if name == "python" and isinstance(payload, dict):
                _merge_python_payload(res["extensions"].setdefault("python", {}), payload)
            elif name == "html":
                html_seen += 1
                res["extensions"]["html" if html_seen == 1 else f"html:{rec['file']}"] = payload
            else:
                res["extensions"][name if name not in res["extensions"] else f"{name}:{rec['file']}"] = payload
        a = r.get("analysis", {})
        modes.add(a.get("mode"))
        partial = partial or bool(a.get("partial"))
        notes += [n for n in a.get("notes", []) if n not in notes]
        text_files |= set(a.get("text_files", []))
        _union(parse_errors, a.get("parse_errors", []), lambda x: (x["file"], x["error"]))
        if "framework" in r and "framework" not in res:
            res["framework"] = r["framework"]
    res["trace"]["entries"] = merge_traces(records)
    res["analysis"].update(mode=(modes.pop() if len(modes) == 1 else "mixed"), partial=partial, notes=notes)
    if text_files:
        res["analysis"]["text_files"] = sorted(text_files)
    if parse_errors:
        res["analysis"]["parse_errors"] = parse_errors
    res["extensions"]["traversal"] = {"files": [{"file": r["file"], "language": r["language"], "entry": r["entry"]}
                                                for r in records]}
    return res


# ----------------------------------------------------------------------------------------------
# top-down functionalities, functionality analysis, report, project graph
# ----------------------------------------------------------------------------------------------
def _links(records):
    """(source file, line) -> [files it led to]"""
    out = defaultdict(list)
    for r in records:
        for o in r.get("discovered_via") or []:
            line = (o.get("meta") or {}).get("line")
            if o.get("source_file") and line is not None and r["file"] not in out[(o["source_file"], line)]:
                out[(o["source_file"], line)].append(r["file"])
    return out


def combine_topdown(parts, links, project, entry_point):
    """parts: [(file, language, {"result","text"})] -> one document with every file's functionalities, numbered
    in traversal order; operations that led to another file say so (``leads_to``)."""
    funcs, files, texts = [], [], []
    by_kind, accounting = OrderedDict(), {}
    ops = nodes = accounted = depth = 0
    for file, language, doc in parts:
        res, offset = doc["result"], len(funcs)
        for f in res["functionalities"]:
            g = copy.deepcopy(f)
            g["local_number"] = g["functionality_number"]
            g["functionality_number"] += offset
            g["functionality_id"] = f"TDF_{g['functionality_number']:06d}"
            for k in ("parent_functionality",):
                if g.get(k):
                    g[k] += offset
            g["child_functionalities"] = [n + offset for n in g.get("child_functionalities", [])]
            g["source_file"], g["language"] = file, language
            for op in g.get("children", []):
                to = links.get((op.get("file"), op.get("line")))
                if to:
                    op["leads_to"] = list(to)
            by_kind[g["kind"]] = by_kind.get(g["kind"], 0) + 1
            funcs.append(g)
        st = res["statistics"]
        ops += st.get("child_operations", 0)
        nodes += st.get("code_nodes", 0)
        accounted += st.get("code_nodes_accounted", 0)
        depth = max(depth, st.get("max_path_depth", 0))
        for k, v in (st.get("accounting") or {}).items():
            accounting[k] = accounting.get(k, 0) + v
        files.append(OrderedDict(file=file, language=language, functionalities=st.get("functionalities", 0)))
        texts.append((file, language, doc["text"]))
    stats = OrderedDict([("functionalities", len(funcs)), ("by_kind", by_kind), ("child_operations", ops),
                         ("code_nodes", nodes), ("code_nodes_accounted", accounted),
                         ("accounting", OrderedDict(sorted(accounting.items()))), ("max_path_depth", depth),
                         ("files", len(files))])
    result = OrderedDict([("project", project), ("entry_point", entry_point),
                          ("traversal", "files in the order App Broker analysed them; each file top-down from its own ROOT"),
                          ("statistics", stats), ("files", files), ("functionalities", funcs)])
    bar = "=" * 100
    o = [bar, "TOP-DOWN FUNCTIONALITY EXTRACTION - CROSS-FILE TRAVERSAL (HTML + Python)", bar,
         f"Project        : {project}", f"Entry point    : {entry_point}",
         f"Files          : {len(files)}   Functionalities: {len(funcs)}", "", "FILES (traversal order)", "-" * 100]
    o += [f"  {i}. {x['file']}  [{x['language']}]  {x['functionalities']} functionality(ies)" for i, x in enumerate(files, 1)]
    if links:
        o += ["", "LINKS between files (source file:line -> files it led to)", "-" * 100]
        o += [f"  {src}:{ln} -> {', '.join(to)}" for (src, ln), to in sorted(links.items(), key=lambda kv: (kv[0][0], kv[0][1]))]
    for file, language, text in texts:
        o += ["", bar, f"FILE: {file}   [{language}]", bar, text]
    return {"result": result, "text": "\n".join(o)}


class CombinedBroker:
    """The broker-shaped object App Broker's write_outputs() works with for a multi-file traversal."""
    LANGUAGE = "mixed"

    def __init__(self, records, result, traversal, trace_doc_builder, basic_report):
        self.records, self.result, self.traversal = records, result, traversal
        self._build, self._basic_report = trace_doc_builder, basic_report
        self.members = [r for r in records if r.get("broker") is not None]
        self.notes = []

    @property
    def reachable_count(self):
        return sum(getattr(r["broker"], "reachable_count", 0) for r in self.members)

    def summary_lines(self):
        out = []
        for r in self.members:
            out.append(f"  {r['file']} [{r['language']}]")
            out += ["  " + ln for ln in r["broker"].summary_lines()]
        return out

    def _member(self, hook):
        return [r for r in self.members if hasattr(r["broker"], hook)]

    def attach_trace_tree(self, root, stats):
        """Called by write_outputs with the COMBINED tree; every member analysis needs ITS OWN tree."""
        self.trace_tree_root, self.trace_tree_stats = root, stats
        for r in self._member("attach_trace_tree"):
            doc, _ = self._build(r["result"])
            r["broker"].attach_trace_tree(doc["root"], doc["statistics"])

    def _each(self, hook, label):
        for r in self._member(hook):
            try:
                yield r, getattr(r["broker"], hook)()
            except Exception as e:                                   # one file must not cost the others
                import traceback
                self.notes.append(f"{label} failed for {r['file']}: {type(e).__name__}: {e}")
                traceback.print_exc()

    def functionality_document(self):
        docs = list(self._each("functionality_document", "functionality analysis"))
        if len(docs) == 1:
            return docs[0][1]
        return OrderedDict([("project", self.result["project"]["name"]), ("entry_point", self.result["entry"]["label"]),
                            ("statistics", {"files": len(docs)}),
                            ("files", [OrderedDict(file=r["file"], language=r["language"], document=d) for r, d in docs])])

    def topdown_document(self):
        parts = [(r["file"], r["language"], d) for r, d in self._each("topdown_document", "top-down extraction")]
        return combine_topdown(parts, _links(self.records), self.result["project"]["name"], self.result["entry"]["label"])

    def project_graph_document(self):
        html = [r for r in self.members if r["language"] == "HTML" and hasattr(r["broker"], "project_graph_document")]
        if not html:
            raise RuntimeError("no HTML file in this traversal")
        return html[0]["broker"].project_graph_document(files=[r["file"] for r in html])

    def report_text(self):
        o = [self._basic_report(self.result), "TRAVERSAL", "-" * 78,
             f"Files analysed : {len(self.members)} (entry: {', '.join(r['file'] for r in self.records if r['entry'])})"]
        for i, r in enumerate(self.records, 1):
            via = (r.get("discovered_via") or [{}])[0]
            why = "entry file" if r["entry"] else (
                f"{via.get('source_file')}:{(via.get('meta') or {}).get('line', '?')}  {via.get('reference')}")
            o.append(f"  {i:>3}. {r['file']}  [{r['language']}]  {r['status']}  <- {why}"
                     + (f"  ({r['reason']})" if r.get("reason") else ""))
        unresolved = self.traversal.get("unresolved", [])
        if unresolved:
            o += ["", f"Unresolved references ({len(unresolved)})", "-" * 78]
            o += [f"  {u['file']}:{u['line']}  {u['reference']}  - {u['reason']}" for u in unresolved]
        for r in self.members:
            if hasattr(r["broker"], "report_text"):
                try:
                    o += ["", "=" * 78, f"FILE REPORT: {r['file']}  [{r['language']}]", "=" * 78, r["broker"].report_text()]
                except Exception as e:
                    o.append(f"(report for {r['file']} failed: {type(e).__name__}: {e})")
        o += [f"note: {n}" for n in self.notes]
        return "\n".join(o) + "\n"
