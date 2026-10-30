"""TXT and SVG reports of ONE merged traversal document (``TraversalCoordinator.document()``).

Both renderers consume only the document, never the coordinator, so TXT, JSON and SVG cannot disagree: they print
and draw the same node ids, edge statuses and counts.  Discovery, resolution and tracing are reported separately.
"""
import re
from collections import OrderedDict

_BAD = re.compile(r"[\x00-\x08\x0b\x0c\x0e-\x1f\x7f\ufffe\uffff]")
_ARROW = {"contains", "imports"}                      # structure edges: not part of a functionality path


def _e(s):
    return _BAD.sub("\ufffd", str(s)).replace("&", "&amp;").replace("<", "&lt;").replace(">", "&gt;").replace('"', "&quot;")


def _t(s, n):
    s = str(s)
    return s if len(s) <= n else s[:n - 1] + "\u2026"


def _tail(s, n):
    s = str(s)
    return s if len(s) <= n else "\u2026" + s[-(n - 1):]


def _loc(n):
    f, l = n.get("file"), n.get("line")
    if n.get("end_line") and n.get("end_line") != l:
        l = f"{l}-{n['end_line']}"
    return f"{f}:{l}" if f and l else (f or "")


def _label(n):
    t = n["type"]
    if t == "html_element":
        return f"{_loc(n)} <{n.get('tag')}>" + (f" \"{n['text']}\"" if n.get("text") else "")
    if t == "template_tag":
        return f"{_loc(n)} {{% {n.get('tag')} %}}"
    if t == "url_pattern":
        return f"route {n.get('pattern') or n['id']!r} ({_loc(n)})"
    if t in ("template", "python_file", "static_file"):
        return f"{t.replace('_', ' ')} {n['id']}"
    if t == "template_name":
        return f"template {n['id'].split(':', 1)[-1]}"
    if t in ("function", "class", "method", "view", "external_view", "symbol"):
        return n["id"] + (f" [{n['python_trace']}]" if n.get("python_trace") else "")
    return n["id"]


def _index(doc):
    nodes = {n["id"]: n for n in doc["nodes"]}
    out = OrderedDict()
    for e in doc["edges"]:
        out.setdefault(e["source"], []).append(e)
    return nodes, out


def paths(doc, limit=300, max_depth=12):
    """Cross-broker paths, one per root-to-leaf chain, starting at every HTML element / template tag / seed."""
    nodes, out = _index(doc)
    roots = [n["id"] for n in doc["nodes"] if n["type"] in ("html_element", "template_tag", "seed") and out.get(n["id"])]
    res = []

    def go(nid, chain, seen):
        if len(res) >= limit:
            return
        nxt = [e for e in out.get(nid, []) if e["type"] not in _ARROW and e["target"] not in seen]
        if not nxt or len(chain) >= max_depth:
            if chain:
                res.append(chain)
            return
        for e in nxt:
            go(e["target"], chain + [e], seen | {e["target"]})
    for r in roots:
        go(r, [], {r})
    return res, len(res) >= limit


def render_txt(doc):
    nodes, out = _index(doc)
    st, bar = doc["statistics"], "=" * 78
    o = [bar, "PATCHPLUS CROSS-BROKER TRACE REPORT", bar, f"Project root : {doc['meta']['root']}",
         f"Seeds        : {', '.join(doc['meta']['seeds']) or '(every template under the root)'}",
         f"Django       : {'yes' if doc['meta']['django'] else 'no'}"
         + (f"  settings={doc['meta']['settings']}  ROOT_URLCONF={doc['meta']['root_urlconf']}" if doc['meta']['django'] else "")]
    o += [f"Note         : {n}" for n in doc["meta"]["notes"]]
    d, t, r, g = st["discovery"], st["tracing"], st["resolution"], st["graph"]
    o += ["", "SUMMARY (the same numbers appear in the JSON and the SVG)", "-" * 56,
          f"Discovery  : {d['templates']} template file(s), {d['python_files']} Python file(s) found",
          f"Tracing    : templates traversed {t['templates_traced']}/{d['templates']}, Python files traced "
          f"{t['python_files_traced']}/{d['python_files']}; views traced {t['views_traced']}, partial {t['views_partial']}, "
          f"failed {t['views_failed']}",
          f"Resolution : {r['references']} reference(s): " + (", ".join(f"{k} {v}" for k, v in sorted(r['by_status'].items())) or "none"),
          f"Graph      : {g['nodes']} nodes, {g['edges']} edges, {g['unresolved']} unresolved/failed record(s)"]

    o += ["", "1. DISCOVERY - every file found, whether or not a functionality path reached it", "-" * 56]
    for n in doc["nodes"]:
        if n["type"] in ("template", "python_file"):
            o.append(f"  [{'configuration' if n.get('role') else 'traced' if n.get('traced') else 'discovered only':15}] {n['type'].replace('_', ' '):12} {n['id']}"
                     + (f"  ({n['line_count']} lines)" if n.get("line_count") else ""))

    o += ["", "2. RESOLUTION - one line per extracted reference", "-" * 56]
    for ref in doc["references"]:
        if ref["target_type"] in ("html_file", "python_view"):
            continue
        where = f"{ref['source_file']}:{ref['source_line']}" if ref["source_file"] else "(seed)"
        o.append(f"  [{ref['resolution_status']:14}] {where}  {ref['relationship']} {ref['target_type']} {ref['target']}"
                 + (f"  -> {ref['resolved_file']}" + (f":{ref['resolved_symbol']}" if ref['resolved_symbol'] else "") if ref["resolved_file"] else "")
                 + (f"\n{'':20}reason: {ref['reason']}" if ref.get("reason") else ""))
        n = nodes.get(next((e["source"] for e in doc["edges"] if e.get("traversal_id") == ref["traversal_id"]
                            and nodes.get(e["source"], {}).get("type") in ("html_element", "template_tag")), ""), None)
        if n and n.get("source_text"):
            o.append(f"{'':20}source: " + n["source_text"].replace("\n", "\n" + " " * 28))

    o += ["", "3. TRACING - Python views handed to the Python broker", "-" * 56]
    for s in doc["traversal"]["python_traces"]:
        o.append(f"  [{s['status']:7}] {s['file']}:{s['line'] or '?'} {s['kind'] or ''} {s['symbol']}"
                 + (f"  methods: {', '.join(s['dispatch_methods'])}" if s["dispatch_methods"] else "")
                 + (f"  bases: {', '.join(s['bases'])}" if s["bases"] else "") + f"  calls recorded: {s['calls']}"
                 + (f"\n{'':12}reason: {s['reason']}" if s.get("reason") else ""))
    if not doc["traversal"]["python_traces"]:
        o.append("  (no view was traced)")

    ps, capped = paths(doc)
    o += ["", "4. CROSS-BROKER PATHS - HTML element -> route -> view -> calls / template -> ...", "-" * 56]
    for chain in ps:
        line = _label(nodes[chain[0]["source"]])
        for e in chain:
            tag = "" if e["status"] == "resolved" else f"[{e['status']}]"
            line += f"\n      --{e['type']}{tag}--> {_label(nodes[e['target']])}"
        o.append("  " + line)
    if capped:
        o.append("  ... path list capped; the JSON holds every edge")

    o += ["", "5. UNRESOLVED, PARTIAL AND FAILED - nothing is dropped silently", "-" * 56]
    for u in doc["unresolved"]:
        o.append(f"  [{u.get('status') or 'unresolved':10}] {u.get('category') or '-':20} {u.get('source')}:{u.get('line')}  "
                 f"{u.get('reference')}\n{'':16}reason: {u.get('reason')}")
    if not doc["unresolved"]:
        o.append("  (none)")
    return "\n".join(o) + "\n"


# ---------------------------------------------------------------------------------------------- SVG
_COLORS = {"resolved": "#16a34a", "partial": "#d97706", "unresolved": "#dc2626", "failed": "#7f1d1d",
           "not_applicable": "#9ca3af", "discovered": "#9ca3af"}
_W, _H, _GAP, _PAD, _HEAD = 300, 44, 110, 24, 70
_COLS = ("HTML source (elements)", "references", "Django routes", "Python code", "templates / static")
_MAX_PER_FILE = 14


def _col(n):
    t = n["type"]
    if t in ("template", "html_element", "template_tag", "seed"):
        return 0
    if t == "url_pattern":
        return 2
    if t in ("python_file", "function", "class", "method", "view", "external_view", "symbol"):
        return 3
    if t in ("template_name", "static_file", "static_ref"):
        return 4
    return 1


def render_svg(doc):
    nodes = {n["id"]: n for n in doc["nodes"]}
    # visibility: references that need no resolution (external URLs, mailto, ...) are counted, not drawn
    hidden_na = {}
    visible = set()
    for e in doc["edges"]:
        if e["type"] == "contains":
            continue
        for end in (e["source"], e["target"]):
            visible.add(end)
    for e in doc["edges"]:
        if e["status"] == "not_applicable" and e["type"] != "contains":
            visible.discard(e["target"])
            src = nodes.get(e["source"], {})
            hidden_na[src.get("file")] = hidden_na.get(src.get("file"), 0) + 1
    for e in doc["edges"]:                                           # a node still referenced by a drawn edge stays
        if e["type"] != "contains" and e["status"] != "not_applicable":
            visible.update((e["source"], e["target"]))
    pos, rows, collapsed = {}, [0] * 5, OrderedDict()
    y0 = _PAD + _HEAD

    def place(nid, col, y):
        pos[nid] = (_PAD + col * (_W + _GAP), y)

    def stack(col, items):
        for nid in items:
            place(nid, col, y0 + rows[col])
            rows[col] += _H + 10

    by_file = OrderedDict()
    for n in doc["nodes"]:
        c = _col(n)
        if n["id"] not in visible and n["type"] not in ("template", "python_file"):
            continue
        if c in (0, 3):                              # a traced file always heads its group
            by_file.setdefault((c, n["file"] if n["type"] not in ("template", "python_file") else n["id"]), []).append(n)
        else:
            by_file.setdefault((c, None), []).append(n)
    for c in (1, 2, 4):
        stack(c, [n["id"] for n in sorted(by_file.get((c, None), []), key=lambda n: (n.get("file") or "", n.get("line") or 0, n["id"]))])
    for c in (0, 3):
        files = sorted({f for (cc, f) in by_file if cc == c and f}, key=lambda f: (not nodes.get(f, {}).get("traced", True), f))
        traced = [f for f in files if nodes.get(f, {}).get("traced") or nodes.get(f, {}).get("traced") is None]
        idle = [f for f in files if f not in traced]
        stack(c, [n["id"] for n in by_file.get((c, None), [])])      # nodes with no file (external views, seeds) still drawn
        for label, group in (("", traced), ("Discovered, not traced by any functionality path", idle)):
            if group and label:
                rows[c] += 8
                place(f"~hdr{c}", c, y0 + rows[c])
                pos[f"~hdr{c}"] = pos[f"~hdr{c}"] + (label,)
                rows[c] += 24
            for f in group:
                members = by_file[(c, f)]
                head = [m for m in members if m["id"] == f]
                kids = sorted([m for m in members if m["id"] != f], key=lambda m: (m.get("line") or 0, m["id"]))
                if len(kids) > _MAX_PER_FILE:
                    collapsed[f] = len(kids) - _MAX_PER_FILE
                    kids = kids[:_MAX_PER_FILE]
                stack(c, [m["id"] for m in head + kids])
                rows[c] += 12
    height = max(rows) + y0 + _PAD
    width = _PAD * 2 + 5 * _W + 4 * _GAP
    o = []
    drawn = skipped = 0
    for e in doc["edges"]:
        if e["type"] in ("contains", "defined_in") or e["status"] == "not_applicable":
            continue                                   # structure edges are in the JSON / TXT, not drawn
        if e["source"] not in pos or e["target"] not in pos:
            skipped += 1
            continue
        (xs, ys), (xd, yd) = pos[e["source"]][:2], pos[e["target"]][:2]
        ys, yd = ys + _H / 2, yd + _H / 2
        cs, cd = _col(nodes[e["source"]]), _col(nodes[e["target"]])
        if cs < cd:
            x1, x2, k = xs + _W, xd, (xd - xs - _W) / 2
            d = f"M{x1},{ys} C{x1 + k},{ys} {x2 - k},{yd} {x2},{yd}"
        elif cs == cd:
            x1 = xs + _W
            d = f"M{x1},{ys} C{x1 + 70},{ys} {x1 + 70},{yd} {x1},{yd}"
        else:
            x1, x2 = xs, xd + _W
            d = f"M{x1},{ys} C{x1 - 70},{ys} {x2 + 70},{yd} {x2},{yd}"
        cls = e["status"] + (" py" if e.get("origin") == "python_broker" else "") + (" back" if cs > cd else "")
        tip = f"{e['type']} [{e['status']}] {e['source']} -> {e['target']}" + (f" ({e['file']}:{e['line']})" if e.get("file") and e.get("line") else "") \
            + (f" - {e['reason']}" if e.get("reason") else "")
        o.append(f'<path class="edge {cls}" d="{d}" marker-end="url(#arrow-{e["status"]})"><title>{_e(tip)}</title></path>')
        drawn += 1
    for nid, p in pos.items():
        if nid.startswith("~hdr"):
            o.append(f'<text class="grp" x="{p[0]}" y="{p[1] + 14}">{_e(p[2])}</text>')
            continue
        n, x, y = nodes[nid], p[0], p[1]
        stat = n["status"]
        t = n["type"]
        if t == "html_element":
            l1 = f"<{n.get('tag')}> {n.get('text') or ''}".strip()
            l2 = f"{n['file']}:" + (f"{n['line']}-{n['end_line']}" if n.get("end_line") != n.get("line") else f"{n['line']}")
        elif t == "template_tag":
            l1, l2 = n.get("source_text") or "{% " + str(n.get("tag")) + " %}", f"{n['file']}:{n['line']}"
        elif t in ("template", "python_file"):
            l1 = _tail(n["id"], 40)
            l2 = ("URL configuration (route resolution)" if n.get("role") else "traced" if n.get("traced") else "discovered, not traced") + (f" \u00b7 {n['line_count']} lines" if n.get("line_count") else "")
        elif t == "url_pattern":
            l1, l2 = f"route /{n.get('pattern')}", _loc(n) + (f" \u00b7 view {n.get('view_status')}" if n.get("view_status") else "")
        else:
            l1 = n["id"].split(":", 1)[-1] if t in ("function", "class", "method", "view") else n["id"]
            l2 = (_loc(n) or "") + (f" \u00b7 trace {n['python_trace']}" if n.get("python_trace") else "")
        tip = "\n".join(x for x in (n["id"], f"status: {stat}", n.get("reason"), n.get("source_text")) if x)
        o.append(f'<g class="node {stat}{" idle" if (t in ("template", "python_file") and not n.get("traced")) else ""}">'
                 f'<title>{_e(tip)}</title><rect x="{x}" y="{y}" width="{_W}" height="{_H}" rx="6"/>'
                 f'<text class="l1" x="{x + 8}" y="{y + 18}">{_e(_t(l1, 44))}</text>'
                 f'<text class="l2" x="{x + 8}" y="{y + 35}">{_e(_t(l2, 50))}</text></g>')
    for f, k in collapsed.items():
        last = max((pos[i][1] for i in pos if not i.startswith("~") and nodes[i].get("file") == f), default=0)
        o.append(f'<text class="grp" x="{pos[f][0] + 8}" y="{last + _H + 14}">+{k} more symbol(s) in {_e(_tail(f, 30))} (see JSON)</text>')
    cols = "".join(f'<text class="col" x="{_PAD + i * (_W + _GAP)}" y="{_PAD + 40}">{_e(c)}</text>' for i, c in enumerate(_COLS))
    st = doc["statistics"]
    foot = (f"{drawn} edge(s) drawn; {skipped} edge(s) to collapsed nodes not drawn; "
            f"{sum(hidden_na.values())} external/non-resolvable reference(s) counted, not drawn (not_applicable)")
    legend = "".join(f'<rect x="{width - 640 + i * 150}" y="{_PAD - 4}" width="14" height="14" class="lg {s}"/>'
                     f'<text class="col" x="{width - 620 + i * 150}" y="{_PAD + 8}">{s}</text>'
                     for i, s in enumerate(("resolved", "partial", "unresolved", "failed")))
    markers = "".join(f'<marker id="arrow-{s}" viewBox="0 0 10 10" refX="9" refY="5" markerWidth="7" markerHeight="7" orient="auto">'
                      f'<path d="M0,0 L10,5 L0,10 z" fill="{c}"/></marker>' for s, c in _COLORS.items())
    css = "".join(f".node.{s} rect{{stroke:{c}}}.edge.{s}{{stroke:{c}}}.lg.{s}{{fill:{c}}}" for s, c in _COLORS.items())
    head = [
        '<?xml version="1.0" encoding="UTF-8"?>',
        f'<svg xmlns="http://www.w3.org/2000/svg" width="{width}" height="{height + 24}" viewBox="0 0 {width} {height + 24}" '
        'font-family="DejaVu Sans, Arial, sans-serif" font-size="12">',
        "<title>PatchPlus cross-broker traversal</title>",
        f"<style>.bg{{fill:#fff}}.node rect{{fill:#f7f8fa;stroke-width:2}}.node.idle rect{{stroke-dasharray:5 3;fill:#fff}}"
        f".edge{{fill:none;stroke-width:1.6;opacity:.85}}.edge.unresolved,.edge.failed{{stroke-dasharray:6 4}}.edge.py{{stroke-width:1.2}}.edge.back{{opacity:.4}}"
        f".l1{{fill:#1f2430;font-weight:bold}}.l2{{fill:#6b7280;font-size:11px}}.col{{fill:#2b4c8c;font-weight:bold}}.grp{{fill:#6b7280;font-style:italic}}"
        f".ttl{{font-size:16px;font-weight:bold;fill:#1f2430}}.sum{{fill:#374151}}{css}"
        "@media (prefers-color-scheme: dark){.bg{fill:#14161b}.node rect{fill:#1b1e25}.node.idle rect{fill:#14161b}.l1,.ttl{fill:#e3e6ec}"
        ".l2,.grp,.sum{fill:#9aa3b2}.col{fill:#8fb2ff}}</style>",
        f"<defs>{markers}</defs>", f'<rect class="bg" width="{width}" height="{height + 24}"/>',
        f'<text class="ttl" x="{_PAD}" y="{_PAD + 8}">PatchPlus cross-broker traversal</text>',
        f'<text class="sum" x="{_PAD}" y="{_PAD + 26}">{_e(_summary(st))}</text>', legend, cols]
    return "\n".join(head + o + [f'<text class="sum" x="{_PAD}" y="{height + 12}">{_e(foot)}</text>', "</svg>", ""])


def _summary(st):
    d, t, r = st["discovery"], st["tracing"], st["resolution"]
    return (f"{d['templates']} templates ({t['templates_traced']} traversed), {d['python_files']} Python files "
            f"({t['python_files_traced']} traced), {r['references']} references: "
            + ", ".join(f"{k} {v}" for k, v in sorted(r["by_status"].items())))
