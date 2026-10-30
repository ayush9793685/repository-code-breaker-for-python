"""Normalised, language-neutral analysis result shared by App Broker and every language broker.

This module imports neither ``app_broker`` nor any language broker (no circular imports) and holds no
language-specific analysis.  It contains

  * the versioned schema (``SCHEMA_NAME`` / ``SCHEMA_VERSION``), documented below, and ``validate()``;
  * the language-neutral trace-tree processing: ``parse_trace`` (trace text -> tree) and
    ``render_trace_svg`` (tree -> SVG), moved verbatim from the Python broker.

SCHEMA  patchplus.normalized  1.0          (a plain JSON-serialisable dict; no AST / language objects)
---------------------------------------------------------------------------------------------------
Compatibility: consumers accept the same MAJOR version and ignore unknown keys; a MINOR bump only adds
optional keys.  A missing optional value is absent or ``null`` (= unknown), never a made-up default.

REQUIRED  schema, schema_version, language, project{name, root}, entry{file, label, kind},
          analysis{mode, partial}, files[], symbols[], relationships[], nodes[], trace{entries[]}
OPTIONAL  imports[], execution_tree[], dependencies[], unresolved[], framework{name, active, document},
          extensions{<language>: {...}}                 (language-private metadata, never interpreted)
ATTACHED BY APP BROKER AFTER SHARED TRACE PROCESSING (produced by the broker's optional hooks)
          functionality{...}, topdown{result, text}

files[]          {path, module, analysis_mode "ast"|"text", reached, [parse_error, main_block_line, discovered_via,
                  execution_reached]}
symbols[]        {id (stable, unique), kind class|function|method|..., name, file, line, parent|null, module,
                  scope "module"|"local", reachable, referenced, dispatch_target, reachability, confidence
                  "high"|"low"|null, [configured]}
relationships[]  {source, target, type, origin "static"|"framework", line|null, file, attributes{}}
                  attributes keeps relationship-specific keys (conditions, via, resolution, confidence ...)
nodes[]          {id, type, file|null, line|null}      graph nodes, ids are symbol ids / file paths
trace            {entries[{depth, file, line, text}]   execution trace, depth-first, one entry per trace line
                  call_categories[{file, line, category "external"|"stdlib"}]}
analysis         {mode "ast"|"text"|"mixed", partial bool, text_files[], parse_errors[{file, error}], notes[]}
dependencies[]   {module, category "external"|"stdlib"|"missing", references[]}
unresolved[]     {file, line, reference, reason}
framework        {name, active, document}  document = framework/configuration analysis, kept apart from the trace
"""
import re
import sys
from collections import OrderedDict
from xml.sax.saxutils import escape as _xml_escape

SCHEMA_NAME = "patchplus.normalized"
SCHEMA_VERSION = "1.0"

_REQUIRED = {"schema": str, "schema_version": str, "language": str, "project": dict, "entry": dict,
             "analysis": dict, "files": list, "symbols": list, "relationships": list, "nodes": list,
             "trace": dict}
_SYMBOL_KEYS = ("id", "kind", "name", "file", "line", "module", "scope", "reachable")


class NormalizationError(Exception):
    """The normalised result a broker produced does not follow the schema."""


def new_result(language, project, root, entry):
    """Skeleton with every required key present (brokers fill it in)."""
    return OrderedDict([
        ("schema", SCHEMA_NAME), ("schema_version", SCHEMA_VERSION), ("language", language),
        ("project", {"name": project, "root": root}), ("entry", dict(entry)),
        ("analysis", {"mode": "ast", "partial": False, "text_files": [], "parse_errors": [], "notes": []}),
        ("files", []), ("symbols", []), ("relationships", []), ("nodes", []),
        ("trace", {"entries": [], "call_categories": []})])


def validate(res):
    """Return a list of problems (empty = valid)."""
    if not isinstance(res, dict):
        return ["result is not a dict"]
    bad = [f"missing or mistyped '{k}'" for k, t in _REQUIRED.items() if not isinstance(res.get(k), t)]
    if bad:
        return bad
    if res["schema"] != SCHEMA_NAME:
        bad.append(f"unknown schema {res['schema']!r}")
    if res["schema_version"].split(".")[0] != SCHEMA_VERSION.split(".")[0]:
        bad.append(f"incompatible major version {res['schema_version']} (supported {SCHEMA_VERSION})")
    for k in ("name", "root"):
        if k not in res["project"]:
            bad.append(f"project.{k} missing")
    for k in ("file", "label", "kind"):
        if k not in res["entry"]:
            bad.append(f"entry.{k} missing")
    for k in ("mode", "partial"):
        if k not in res["analysis"]:
            bad.append(f"analysis.{k} missing")
    ids = set()
    for s in res["symbols"]:
        miss = [k for k in _SYMBOL_KEYS if k not in s]
        if miss:
            bad.append(f"symbol {s.get('id')!r} lacks {miss}")
        elif s["id"] in ids:
            bad.append(f"duplicate symbol id {s['id']!r}")
        ids.add(s.get("id"))
    for r in res["relationships"]:
        if not all(k in r for k in ("source", "target", "type", "origin")):
            bad.append(f"relationship incomplete: {r}")
    for n in res["nodes"]:
        if "id" not in n or "type" not in n:
            bad.append(f"node incomplete: {n}")
    for i, e in enumerate(res["trace"].get("entries", [])):
        if not all(k in e for k in ("depth", "file", "line", "text")):
            bad.append(f"trace entry {i} incomplete")
            break
    return bad


def ensure_valid(res):
    problems = validate(res)
    if problems:
        raise NormalizationError("invalid normalised result: " + "; ".join(problems[:5])
                                 + (f" (+{len(problems) - 5} more)" if len(problems) > 5 else ""))
    return res


def render_trace_text(entries):
    """Trace entries -> the expanded_trace.txt format ('<indent>file:line | code')."""
    return "".join(f"{'    ' * e['depth']}{e['file']}:{e['line']:<4}| {e['text']}\n" for e in entries)


def call_site_map(res):
    return {(c["file"], c["line"]): c["category"] for c in res["trace"].get("call_categories", [])}


# ----------------------------------------------------------------------
# Trace tree
#
#   expanded_trace.txt --parse_trace()--> tree --+--> trace_tree.json
#                                                 +--> trace_tree.svg
#
# The tree is built ONLY from the trace (indentation = parent/child).  Every
# trace line that carries code becomes its own node - the same file:line
# reached twice is two nodes, because each is a different point in the
# traversal.  "(expanded above)" / "(recursive call ...)" lines are not code;
# they are stored as `references` on the node they belong to.
# ----------------------------------------------------------------------
_TRACE_RE = re.compile(r"^( *)(\S.*?):(\d+)\s*\|\s?(.*)$")
_REF_EXPANDED = "(expanded above)"
_REF_RECURSIVE = "(recursive call to"


def parse_trace(text, call_sites=None):
    """Turn expanded_trace.txt text into (root_node, statistics). Fails loudly on bad input."""
    call_sites = call_sites or {}
    root = OrderedDict([("id", "root"), ("type", "root"), ("children", [])])
    stack = []                       # [(indent, node)] - the currently open ancestors
    entries = code_nodes = references = max_depth = 0

    for lineno, raw in enumerate(text.splitlines(), 1):
        if not raw.strip():
            continue
        m = _TRACE_RE.match(raw.expandtabs(4))
        if not m:
            raise ValueError(f"expanded_trace.txt line {lineno} is not 'file:line | code': {raw!r}")
        entries += 1
        indent, file, line, code = len(m.group(1)), m.group(2).strip(), int(m.group(3)), m.group(4).strip()

        # indentation-relative (no fixed width assumed): close every open node at this indent or deeper
        while stack and stack[-1][0] >= indent:
            stack.pop()
        parent = stack[-1][1] if stack else root

        if code == _REF_EXPANDED or code.startswith(_REF_RECURSIVE):
            parent.setdefault("references", []).append(OrderedDict([
                ("type", "reference"),
                ("target", f"{file}:{line}"),
                ("status", "expanded_above" if code == _REF_EXPANDED else "recursive_call"),
            ]))
            references += 1
            continue

        code_nodes += 1
        node = OrderedDict([("id", f"node_{code_nodes:06d}"), ("type", "code"),
                            ("file", file), ("line", line), ("code", code)])
        kind = call_sites.get((file, line))
        if kind:
            node["category"] = kind           # only present for external / stdlib call lines
        node["children"] = []
        parent["children"].append(node)
        stack.append((indent, node))
        max_depth = max(max_depth, len(stack))

    # validation: every trace entry is exactly one code node or one reference
    walked = 0
    todo = list(root["children"])
    while todo:
        n = todo.pop()
        walked += 1
        todo.extend(n["children"])
    if walked != code_nodes or code_nodes + references != entries:
        raise ValueError(f"trace tree validation failed: entries={entries} code={code_nodes} "
                         f"refs={references} walked={walked}")
    stats = OrderedDict([("trace_entries", entries), ("code_nodes", code_nodes),
                         ("references", references), ("max_depth", max_depth),
                         ("root_nodes", len(root["children"]))])
    return root, stats





# SVG look: left-to-right tree, dark rounded cards, accent bar on the left,
# orthogonal connectors with arrowheads.
_SVG = dict(W=200, H=80, COL=280, ROW=100, PAD=40, GAP_LINES=3, CODE_CHARS=25,
            FONT="Consolas, 'SFMono-Regular', Menlo, 'DejaVu Sans Mono', monospace")
_ACCENT = {"code": "#38bdf8", "external": "#f59e0b", "stdlib": "#34d399"}
_XML_BAD = re.compile(r"[\x00-\x08\x0b\x0c\x0e-\x1f]")


def _x(s):
    return _xml_escape(_XML_BAD.sub("", str(s)))


# Zoom / pan UI embedded in trace_tree.svg (works when the SVG is opened directly in a browser;
# viewers that ignore <script> just show the static, fit-to-window tree).
_SVG_CONTROLS = r'''<g id="hud" font-family="Arial, Helvetica, sans-serif" font-size="14">
  <g data-act="in"><rect width="32" height="28" rx="6" fill="#161f33" stroke="#4b5a73"/><text x="16" y="19" text-anchor="middle" fill="#fff" font-size="18">+</text></g>
  <g data-act="out" transform="translate(38 0)"><rect width="32" height="28" rx="6" fill="#161f33" stroke="#4b5a73"/><text x="16" y="19" text-anchor="middle" fill="#fff" font-size="18">&#8722;</text></g>
  <g data-act="fit" transform="translate(76 0)"><rect width="44" height="28" rx="6" fill="#161f33" stroke="#4b5a73"/><text x="22" y="19" text-anchor="middle" fill="#fff">Fit</text></g>
  <g data-act="actual" transform="translate(126 0)"><rect width="52" height="28" rx="6" fill="#161f33" stroke="#4b5a73"/><text x="26" y="19" text-anchor="middle" fill="#fff">100%</text></g>
  <text x="0" y="46" font-size="11" fill="#64748b">wheel = zoom &#183; drag = pan &#183; + / - / 0 (fit) / 1 (100%)</text>
</g>
<script type="text/ecmascript"><![CDATA[
(function () {
  var svg = document.documentElement, vp = document.getElementById('viewport'),
      hud = document.getElementById('hud'), s = {k: 1, x: 0, y: 0}, MIN = 0.02, MAX = 8;
  function base() { return svg.getScreenCTM(); }
  function toUser(cx, cy) { var p = svg.createSVGPoint(); p.x = cx; p.y = cy; return p.matrixTransform(base().inverse()); }
  function placeHud() {
    var m = base(), r = svg.getBoundingClientRect(), u = toUser(r.left + 12, r.top + 12);
    hud.setAttribute('transform', 'translate(' + u.x + ' ' + u.y + ') scale(' + (1 / m.a) + ')');
  }
  function apply() { vp.setAttribute('transform', 'translate(' + s.x + ' ' + s.y + ') scale(' + s.k + ')'); placeHud(); }
  function zoomAt(cx, cy, f) {
    var u = toUser(cx, cy), k = Math.min(MAX, Math.max(MIN, s.k * f)); f = k / s.k;
    s.x = u.x - (u.x - s.x) * f; s.y = u.y - (u.y - s.y) * f; s.k = k; apply();
  }
  function zoomCentre(f) { var r = svg.getBoundingClientRect(); zoomAt(r.left + r.width / 2, r.top + r.height / 2, f); }
  function fit() { s = {k: 1, x: 0, y: 0}; apply(); }
  function actual() {          /* 1 svg px = 1 screen px, root card at the left, vertically centred */
    var r = svg.getBoundingClientRect(), k = 1 / base().a, t = toUser(r.left + 40, r.top + r.height / 2);
    s.k = k; s.x = t.x - k * parseFloat(svg.getAttribute('data-root-x'));
    s.y = t.y - k * parseFloat(svg.getAttribute('data-root-y')); apply();
  }
  svg.addEventListener('wheel', function (e) { e.preventDefault(); zoomAt(e.clientX, e.clientY, Math.exp(-e.deltaY * 0.0015)); }, {passive: false});
  var drag = null;
  svg.addEventListener('pointerdown', function (e) {
    if (hud.contains(e.target)) return;
    drag = {x: e.clientX, y: e.clientY}; svg.setPointerCapture(e.pointerId); svg.style.cursor = 'grabbing';
  });
  svg.addEventListener('pointermove', function (e) {
    if (!drag) return; var a = base().a;
    s.x += (e.clientX - drag.x) / a; s.y += (e.clientY - drag.y) / a; drag = {x: e.clientX, y: e.clientY}; apply();
  });
  function up() { drag = null; svg.style.cursor = 'grab'; }
  svg.addEventListener('pointerup', up); svg.addEventListener('pointercancel', up);
  hud.addEventListener('click', function (e) {
    var g = e.target; while (g && g !== hud && !g.getAttribute('data-act')) g = g.parentNode;
    var a = g && g.getAttribute && g.getAttribute('data-act');
    if (a === 'in') zoomCentre(1.25); else if (a === 'out') zoomCentre(0.8);
    else if (a === 'fit') fit(); else if (a === 'actual') actual();
  });
  document.addEventListener('keydown', function (e) {
    if (e.key === '+' || e.key === '=') zoomCentre(1.25); else if (e.key === '-') zoomCentre(0.8);
    else if (e.key === '0') fit(); else if (e.key === '1') actual();
  });
  window.addEventListener('resize', placeHud);
  actual();
})();
]]></script>'''


def render_trace_svg(doc):
    """Render the tree held in `doc` (the same dict that is written to JSON) as an SVG string."""
    c = _SVG
    W, H, COL, ROW, PAD = c["W"], c["H"], c["COL"], c["ROW"], c["PAD"]
    root = doc["root"]
    sys.setrecursionlimit(max(sys.getrecursionlimit(), 10000))

    # --- layout: x by depth, leaves stacked top-to-bottom, parents centred on children
    pos, cursor, max_depth = {}, [0], [0]

    def place(n, depth):
        max_depth[0] = max(max_depth[0], depth)
        kids = n["children"]
        if not kids:
            cy = PAD + cursor[0] * ROW + H / 2
            cursor[0] += 1
        else:
            for k in kids:
                place(k, depth + 1)
            cy = (pos[kids[0]["id"]][1] + pos[kids[-1]["id"]][1]) / 2
        pos[n["id"]] = (PAD + depth * COL, cy)

    place(root, 0)
    width = PAD * 2 + max_depth[0] * COL + W
    height = PAD * 2 + max(cursor[0], 1) * ROW - (ROW - H)

    rx, ry = pos["root"]
    out = [f'<svg xmlns="http://www.w3.org/2000/svg" width="100%" height="100%" '
           f'viewBox="0 0 {width} {height}" font-family="{_x(c["FONT"])}" '
           f'data-root-x="{rx:g}" data-root-y="{ry:g}" style="touch-action:none;cursor:grab">',
           f'<title>PatchPlus trace tree - {_x(doc.get("project", ""))} ({_x(doc.get("entry_point", ""))})</title>',
           '<defs><marker id="arrow" viewBox="0 0 8 8" refX="8" refY="4" markerWidth="8" markerHeight="8" '
           'markerUnits="userSpaceOnUse" orient="auto"><path d="M0,0 L8,4 L0,8 z" fill="#64748b"/></marker></defs>',
           f'<rect width="{width}" height="{height}" fill="#ffffff"/>']

    out.append('<g id="viewport">')
    # --- connectors
    edges = []
    todo = [root]
    while todo:
        n = todo.pop()
        kids = n["children"]
        if not kids:
            continue
        px, py = pos[n["id"]]
        px += W
        mid = px + (COL - W) / 2
        ys = [pos[k["id"]][1] for k in kids]
        trunk = f"M{px:g},{py:g}H{mid:g}"
        if len(kids) > 1:
            trunk += f"M{mid:g},{min(ys):g}V{max(ys):g}"
        edges.append(f'<path d="{trunk}"/>')
        for k in kids:
            kx, ky = pos[k["id"]]
            edges.append(f'<path d="M{mid:g},{ky:g}H{kx:g}" marker-end="url(#arrow)"/>')
            todo.append(k)
    out.append('<g fill="none" stroke="#64748b" stroke-width="2" stroke-linejoin="round">')
    out.extend(edges)
    out.append('</g>')

    # --- nodes
    def card(n, label, code, category, tip):
        x, cy = pos[n["id"]]
        y = cy - H / 2
        accent = _ACCENT[category]
        tag = {"external": "EXTERNAL", "stdlib": "STDLIB"}.get(category, "")
        lab_max = 17 if tag else 29
        if len(label) > lab_max:
            label = "\u2026" + label[-(lab_max - 1):]
        n_chars = c["CODE_CHARS"]
        chunks = [code[i:i + n_chars] for i in range(0, len(code), n_chars)] or [""]
        if len(chunks) > c["GAP_LINES"]:
            chunks = chunks[:c["GAP_LINES"]]
            chunks[-1] = chunks[-1][:-1] + "\u2026"
        s = [f'<g data-id="{n["id"]}" data-category="{category}"><title>{_x(tip)}</title>',
             f'<rect x="{x:g}" y="{y:g}" width="{W}" height="{H}" rx="8" fill="#161f33" stroke="#4b5a73" stroke-width="1.5"/>',
             f'<rect x="{x:g}" y="{y:g}" width="6" height="{H}" rx="3" fill="{accent}"/>',
             f'<text x="{x + 16:g}" y="{y + 20:g}" font-size="10" fill="#7dd3fc" xml:space="preserve">{_x(label)}</text>']
        if tag:
            s.append(f'<text x="{x + W - 10:g}" y="{y + 20:g}" font-size="8" text-anchor="end" '
                     f'fill="{accent}" font-weight="700">{tag}</text>')
        for i, ch in enumerate(chunks):
            s.append(f'<text x="{x + 16:g}" y="{y + 40 + i * 14:g}" font-size="11" font-weight="600" '
                     f'fill="#ffffff" xml:space="preserve">{_x(ch)}</text>')
        s.append('</g>')
        return "".join(s)

    root_node = {"id": "root"}
    out.append(card(root_node, "PATCHPLUS TRACE", f"entry: {doc.get('entry_point', '')}", "code",
                    "PATCHPLUS TRACE\nentry: " + str(doc.get("entry_point", ""))))
    todo = list(reversed(root["children"]))
    while todo:
        n = todo.pop()
        cat = n.get("category", "code")
        out.append(card(n, f'{n["file"]}:{n["line"]}', n["code"], cat,
                        f'{n["file"]}:{n["line"]}\n{n["code"]}'))
        todo.extend(reversed(n["children"]))
    out.append('</g>')
    out.append(_SVG_CONTROLS)
    out.append('</svg>')
    return "\n".join(out) + "\n"

