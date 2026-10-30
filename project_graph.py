"""Project graph (design milestone M6): verified HTML / Django / Python relationships in one queryable graph.

Combines
  * HTML broker records           (template --navigates_to / submits_to / extends / includes / ... --> reference)
  * django_resolver verification  (reference --resolves_to--> pattern / template file / static file)
  * view findings                 (pattern --dispatches_to--> view, view --renders--> template)
  * optional Python broker output (nodes / edges of a Python broker graph.json, merged by node id)

Edge types are never collapsed into a generic "connects to" (design section 8).  Every edge carries ``status``;
``verified`` is true only for status ``resolved``.  Anything unverified stays in ``unresolved`` with a reason.

CLI:  python project_graph.py ROOT [--file F ...] [--python-graph graph.json ...] [--outdir DIR]
                                   [--from NODE] [--to NODE] [--chain NODE] [--no-resolve]
"""
import argparse
import json
import os
import sys
from collections import OrderedDict

from html_broker import analyze_files, discover_templates

SCHEMA = "patchplus.project_graph"
VERSION = "0.1"
_SKIP_REL = ("has_control", "uses_variable", "defines_block", "loads_library")


def ref_node_id(target_type, target, source=None):
    """Typed node ids: a URL, a URL name and a template name that look alike never collide."""
    if target_type == "control":
        return f"{source}#{target}"
    if str(target).startswith(target_type + ":"):
        return str(target)
    prefix = {"template": "template_name", "static_file": "static", "static_resource": "static_url"}.get(target_type, target_type)
    return f"{prefix}:{target}"


class ProjectGraph:
    def __init__(self):
        self.nodes, self.edges, self.unresolved, self.meta = OrderedDict(), [], [], OrderedDict()
        self._seen = set()

    # -- building -------------------------------------------------------
    def node(self, nid, type_, file=None, line=None, **attrs):
        n = self.nodes.setdefault(nid, OrderedDict(id=nid, type=type_, file=file, line=line))
        if n.get("file") is None and file is not None:
            n["file"], n["line"] = file, line
        n.update({k: v for k, v in attrs.items() if v is not None})
        return n

    def edge(self, src, tgt, type_, status="resolved", origin="static", **attrs):
        key = (src, tgt, type_)
        if key in self._seen:
            for e in self.edges:
                if (e["source"], e["target"], e["type"]) == key:
                    e.setdefault("occurrences", []).append({k: v for k, v in attrs.items() if v is not None})
                    return e
        self._seen.add(key)
        e = OrderedDict(source=src, target=tgt, type=type_, status=status, verified=status == "resolved", origin=origin)
        e.update({k: v for k, v in attrs.items() if v is not None})
        self.edges.append(e)
        return e

    # -- queries ----------------------------------------------------------
    def out(self, node, type=None, verified_only=False):
        return [e for e in self.edges if e["source"] == node and (type is None or e["type"] == type)
                and (not verified_only or e["verified"])]

    def into(self, node, type=None, verified_only=False):
        return [e for e in self.edges if e["target"] == node and (type is None or e["type"] == type)
                and (not verified_only or e["verified"])]

    def find(self, type=None, contains=None):
        return [n for n in self.nodes.values() if (type is None or n["type"] == type)
                and (contains is None or contains in n["id"])]

    def chain(self, start, verified_only=False, max_depth=12):
        """All edge paths leaving ``start`` (cycle-safe), e.g. home.html -> /accounts/login/ -> pattern -> view -> template."""
        paths = []

        def go(node, path, seen):
            nxt = [e for e in self.out(node, verified_only=verified_only) if e["target"] not in seen]
            if not nxt or len(path) >= max_depth:
                if path:
                    paths.append(list(path))
                return
            for e in nxt:
                go(e["target"], path + [e], seen | {e["target"]})
        go(start, [], {start})
        return paths

    def path(self, src, dst, verified_only=False):
        """Shortest edge path src -> dst, or None."""
        from collections import deque
        q, seen = deque([(src, [])]), {src}
        while q:
            n, p = q.popleft()
            if n == dst:
                return p
            for e in self.out(n, verified_only=verified_only):
                if e["target"] not in seen:
                    seen.add(e["target"])
                    q.append((e["target"], p + [e]))
        return None

    def to_json(self):
        stats = OrderedDict(nodes=len(self.nodes), edges=len(self.edges),
                            verified_edges=sum(1 for e in self.edges if e["verified"]),
                            unverified_edges=sum(1 for e in self.edges if not e["verified"]),
                            unresolved=len(self.unresolved))
        stats["edge_types"] = OrderedDict(sorted(
            ((t, sum(1 for e in self.edges if e["type"] == t)) for t in {e["type"] for e in self.edges})))
        return OrderedDict(schema=SCHEMA, schema_version=VERSION, meta=self.meta, statistics=stats,
                           nodes=list(self.nodes.values()), edges=self.edges, unresolved=self.unresolved)

    @classmethod
    def from_json(cls, doc):
        g = cls()
        g.meta = OrderedDict(doc.get("meta", {}))
        for n in doc["nodes"]:
            g.nodes[n["id"]] = OrderedDict(n)
        for e in doc["edges"]:
            g.edges.append(OrderedDict(e))
            g._seen.add((e["source"], e["target"], e["type"]))
        g.unresolved = list(doc.get("unresolved", []))
        return g


def _view_node(g, view):
    """Graph node for a view.  Repository views use the Python broker's '<file>:<name>' id, so they merge with it."""
    if view.get("external"):
        nid = f"external_view:{view.get('symbol')}"
        g.node(nid, "external_view", symbol=view.get("symbol"))
        return nid
    name = view.get("symbol") or view["text"].split(".as_view")[0].split("(")[0].split(".")[-1]
    nid = f"{view['file']}:{name}"
    g.node(nid, view.get("kind") or "view", view["file"], view["line"])
    return nid


def add_resolution(g, proj, ref_id, res, source_file=None, line=None):
    """Turn ONE verified/unverified resolution into the design-section-8 chain below ``ref_id``.  Returns status."""
    from django_resolver import view_templates
    st = res["status"]
    if st in ("not_applicable", "dynamic"):
        return st
    if st != "resolved":
        g.unresolved.append(OrderedDict(source=source_file, line=line, reference=ref_id, reason=res.get("reason")))
        for c in res.get("candidates", []) if res.get("kind") in ("url_pattern", "template") else []:
            key = c.get("route_id") or c.get("file")
            g.edge(ref_id, key if c.get("route_id") else c["file"], "candidate", status="unresolved",
                   reason="ambiguous: candidate preserved, none chosen")
            if c.get("route_id"):
                g.node(key, "url_pattern", c.get("pattern_file"), c.get("pattern_line"), pattern=c.get("pattern"))
            else:
                g.node(c["file"], "template", c["file"], 1)
        return st
    kind = res.get("kind")
    if kind == "url_pattern":
        rid = res["route_id"]
        g.node(rid, "url_pattern", res["pattern_file"], res["pattern_line"], pattern=res["pattern"], url_name=res.get("name"))
        g.edge(ref_id, rid, "resolves_to", pattern=res["pattern"], file=res["pattern_file"], line=res["pattern_line"])
        v = res.get("view") or {}
        if v.get("status") == "resolved":
            vid = _view_node(g, v)
            g.edge(rid, vid, "dispatches_to", via=v.get("text"), file=res["pattern_file"], line=res["pattern_line"])
            for t in view_templates(proj, v):
                if t.get("dynamic") or not t.get("template"):
                    g.unresolved.append(OrderedDict(source=v.get("file"), line=t.get("line"),
                                                    reference=t.get("expression", ""), reason="dynamic template name in view"))
                    continue
                tr = _resolve_t(proj, t["template"])
                tid = f"template_name:{t['template']}"
                g.node(tid, "template_name")
                g.edge(vid, tid, "renders", status=tr["status"], based_on=t["how"], file=t.get("file"), line=t.get("line"))
                add_resolution(g, proj, tid, tr, t.get("file"), t.get("line"))
        else:                                              # unknown view: no Python destination is invented
            g.unresolved.append(OrderedDict(source=res["pattern_file"], line=res["pattern_line"], reference=v.get("text"),
                                            reason=v.get("reason") or "view not resolved"))
    elif kind in ("template", "static_file"):
        g.node(res["file"], "template" if kind == "template" else "static_file", res["file"], 1)
        extra = {}
        if kind == "template":
            extra = dict(loader=res.get("loader"), duplicate=res.get("duplicate") or None, shadowed=res.get("shadowed") or None)
        g.edge(ref_id, res["file"], "resolves_to", **extra)
    return st


def _resolve_t(proj, name):
    from django_resolver import resolve_reference
    return resolve_reference(proj, "template", name)


def build_project_graph(root, files=None, python_graphs=None, resolve=True):
    """Build the graph for ``files`` (default: every template under root)."""
    from django_resolver import DjangoProject, resolve_reference
    root = os.path.abspath(root)
    g = ProjectGraph()
    proj = DjangoProject.discover(root) if resolve else None
    analysed = analyze_files(root, files)
    g.meta.update(root=root, templates=list(analysed), django=bool(proj), resolver=(proj.to_document() if proj else None))
    done = {}
    for rel, a in analysed.items():
        g.node(rel, "template", rel, 1)
        if a["error"]:
            g.unresolved.append(OrderedDict(source=rel, line=None, reference=rel, reason=f"read error: {a['error']}"))
            continue
        for iss in a["issues"]:
            g.unresolved.append(OrderedDict(source=rel, line=None, reference=rel, reason=f"parse issue: {iss}"))
        forms = {r["line"]: r for r in a["records"] if r["element_type"] == "form"}
        for r in a["records"]:
            rel_t, tgt = r.get("relationship"), r.get("target")
            if rel_t and tgt is None and r.get("target_type") == "dynamic" and rel_t not in _SKIP_REL \
                    and not r.get("in_html_comment"):
                g.unresolved.append(OrderedDict(source=rel, line=r["line"], reference=r.get("expression") or "",
                                                reason=f"dynamic {rel_t} expression: not evaluated"))
                continue
            if not rel_t or tgt is None or rel_t in ("defines_block",) or r.get("in_html_comment") or r.get("also_in_element"):
                continue
            if rel_t in ("uses_variable", "loads_library"):
                continue
            src = rel
            if rel_t == "has_control":
                f = forms.get(r.get("form_line"))
                src = f"{rel}:form@{f['line']}" if f else rel
                g.node(src, "form", rel, r.get("form_line"))
            rid = ref_node_id(r["target_type"], tgt, src)
            status = r["resolution_status"]
            g.node(rid, r["target_type"])
            if proj and status not in ("not_applicable", "dynamic") and rel_t != "has_control":
                key = (r["target_type"], tgt)
                if key not in done:
                    done[key] = resolve_reference(proj, r["target_type"], tgt, rel_t, rel)
                    add_resolution(g, proj, rid, done[key], rel, r["line"])
                status = done[key]["status"]
            elif status == "unresolved":
                g.unresolved.append(OrderedDict(source=rel, line=r["line"], reference=tgt,
                                                reason=f"{rel_t} {r['target_type']} awaits a resolver"
                                                       + ("" if resolve else " (resolution disabled)")))
            elif status == "dynamic":
                g.unresolved.append(OrderedDict(source=rel, line=r["line"], reference=r.get("expression") or "",
                                                reason="dynamic expression: not evaluated"))
            g.edge(src, rid, rel_t, status=status, file=rel, line=r["line"], element=r["element_type"],
                   attribute=r.get("attribute"), text=r.get("text") or None, method=r.get("method"),
                   target_type=r["target_type"], resource_type=r.get("resource_type"),
                   arguments=r.get("arguments") or None)
    for doc in python_graphs or []:
        _merge_python(g, doc)
    return g


def _merge_python(g, doc):
    """Merge a Python broker graph (graph.json: {nodes, edges}) or normalised result by node id."""
    nodes = doc.get("nodes", [])
    edges = doc.get("edges") or [dict(source=r["source"], target=r["target"], type=r["type"], line=r.get("line"),
                                      file=r.get("file")) for r in doc.get("relationships", [])]
    for n in nodes:
        g.node(n["id"], n.get("type", "symbol"), n.get("file"), n.get("line"))
    for e in edges:
        g.node(e["source"], "symbol")
        g.node(e["target"], "symbol")
        status = e.get("resolution") or e.get("status") or "resolved"
        g.edge(e["source"], e["target"], str(e["type"]), status="resolved" if status == "resolved" else "unresolved",
               origin="python_broker", file=e.get("file"), line=e.get("line"))


def _fmt(e):
    return f"--{e['type']}{'' if e['verified'] else ' [' + e['status'] + ']'}--> {e['target']}"


def main(argv=None):
    ap = argparse.ArgumentParser(description="PatchPlus project graph (HTML broker design M6)")
    ap.add_argument("root", nargs="?", default=".")
    ap.add_argument("--file", action="append", help="template file(s) to include (default: all templates)")
    ap.add_argument("--python-graph", action="append", default=[], help="Python broker graph.json to merge")
    ap.add_argument("--outdir", default="patchplus_broker")
    ap.add_argument("--no-resolve", action="store_true")
    ap.add_argument("--chain", metavar="NODE", help="print every edge chain leaving NODE")
    ap.add_argument("--from", dest="src", metavar="NODE")
    ap.add_argument("--to", dest="dst", metavar="NODE")
    a = ap.parse_args(argv)
    pys = []
    for p in a.python_graph:
        with open(p, "r", encoding="utf-8") as f:
            pys.append(json.load(f))
    g = build_project_graph(a.root, a.file, pys, resolve=not a.no_resolve)
    os.makedirs(a.outdir, exist_ok=True)
    out = os.path.join(a.outdir, "project_graph.json")
    with open(out, "w", encoding="utf-8") as f:
        json.dump(g.to_json(), f, indent=2, ensure_ascii=False)
    st = g.to_json()["statistics"]
    print(f"project graph: {st['nodes']} nodes, {st['edges']} edges ({st['verified_edges']} verified), "
          f"{st['unresolved']} unresolved -> {out}")
    if a.chain:
        for p in g.chain(a.chain):
            print("  " + a.chain + " " + " ".join(_fmt(e) for e in p))
    if a.src and a.dst:
        p = g.path(a.src, a.dst)
        print("  path: " + (a.src + " " + " ".join(_fmt(e) for e in p) if p else "none"))
    return g


if __name__ == "__main__":
    main()
