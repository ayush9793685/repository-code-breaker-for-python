"""Cross-broker traversal: HTML -> Django URL resolution -> Python view tracing -> template re-entry.

App Broker owns the invocation and writes every output file (see ``app_broker.run_traversal``); this module
only builds ONE merged result and never touches the disk (except to read sources).  Everything is STATIC:
no view is executed, no template rendered, no HTTP request made.

    TraversalCoordinator(root, seeds).run()      -> traversal over a queue of structured references
    coordinator.document()                       -> the single merged result (JSON-serialisable dict)
    traversal_report.render_txt(doc) / render_svg(doc)  -> the TXT and SVG reports, built ONLY from that document

Brokers are reused, not re-implemented:
    html_broker.analyze_text / complete_html_extraction / read_text     (extraction, source lines, logical elements)
    django_resolver.DjangoProject / resolve_reference / view_templates  (route -> view -> template names)
    python_broker.PythonBroker.trace_view                               (ONE shared repository index; each symbol once)
    project_graph.ProjectGraph / ref_node_id / _view_node               (node ids compatible with existing graphs)

Reference contract (every queued reference, kept in ``document()["references"]``)
    source_file, source_line, target, target_type, relationship, resolved, resolved_file, resolved_symbol,
    traversal_id, resolution_status (resolved | partial | unresolved | failed | not_applicable), reason
Edges reuse the existing project-graph fields (type, status, verified, origin, file, line) and add only
``traversal_id``, ``target_type``, ``reason`` (and ``resolved_file`` / ``resolved_symbol`` where they apply).
"""
import os
import re
from collections import OrderedDict, deque
from xml.sax.saxutils import escape as _esc

from django_resolver import DjangoProject, resolve_reference, view_templates
from html_broker import analyze_text, complete_html_extraction, discover_templates, read_text
from project_graph import ProjectGraph, _view_node, ref_node_id
from python_broker import PythonBroker

SCHEMA = "patchplus.traversal"
VERSION = "1.0"
STATUSES = ("resolved", "partial", "unresolved", "failed")       # + "not_applicable" (external / mailto / fragment ...)
_SEVERITY = {"failed": 4, "unresolved": 3, "partial": 2, "resolved": 1, "not_applicable": 0}
_SKIP_REL = ("has_control", "uses_variable", "defines_block", "loads_library")
_HTML_EXT = (".html", ".htm", ".xhtml")
_REF_NODE_TYPE = {"template": "template_name", "static_file": "static_ref", "static_resource": "static_ref"}   # never collide with FILE nodes
_CATEGORY = {"url": "unresolved_route", "url_name": "unresolved_route", "template": "missing_template",
             "static_file": "missing_static", "static_resource": "missing_static", "relative_url": "relative_url",
             "dynamic": "dynamic_reference"}


def _worst(statuses):
    statuses = [s for s in (statuses or []) if s]
    return max(statuses, key=lambda s: _SEVERITY.get(s, 0)) if statuses else None


class TraversalCoordinator:
    def __init__(self, root, seeds=None, python_broker=None, max_references=100000):
        self.root = os.path.abspath(root)
        self.seeds = list(seeds or [])
        self.graph = ProjectGraph()
        self.proj = None                           # DjangoProject, discovered ONCE
        self.py = python_broker                    # ONE PythonBroker: one repository index for every view
        self.max_references = max_references
        self.queue = deque()
        self.references = []                       # every reference ever queued (document()["references"])
        self.notes = []
        self.visited_files = OrderedDict()         # template file -> "analysed" | "failed"
        self.visited_symbols = set()               # view symbols already handed to the Python broker
        self.python_traces = OrderedDict()         # view symbol -> trace summary
        self._tid = 0
        self._res = {}                             # (target_type, target) -> cached resolution entry
        self._routes_done = set()
        self._tscan = set()                        # symbols already scanned for rendered templates
        self._seen_reached = set()
        self._py_files = set()
        self._ek = {}                              # (source, target, type) -> edge

    # ------------------------------------------------------------------ graph helpers
    def _edge(self, src, tgt, type_, status="resolved", origin="static", **attrs):
        key = (src, tgt, type_)
        attrs = {k: v for k, v in attrs.items() if v is not None}
        e = self._ek.get(key)
        if e is not None:                          # same relationship reached again: keep ONE edge, count the occurrence
            e.setdefault("occurrences", []).append(attrs)
            return e
        e = OrderedDict(source=src, target=tgt, type=type_, status=status, verified=status == "resolved", origin=origin)
        e.update(attrs)
        self.graph.edges.append(e)
        self._ek[key] = e
        return e

    def _set_status(self, src, tgt, type_, status, reason=None):
        e = self._ek.get((src, tgt, type_))
        if e is not None:
            e["status"], e["verified"] = status, status == "resolved"
            if reason:
                e["reason"] = reason

    def _unresolved(self, **kw):
        self.graph.unresolved.append(OrderedDict((k, v) for k, v in kw.items()))

    # ------------------------------------------------------------------ references
    def _push(self, **kw):
        self._tid += 1
        r = OrderedDict(source_file=None, source_line=None, target=None, target_type=None, relationship=None,
                        resolved=False, resolved_file=None, resolved_symbol=None, traversal_id=f"t{self._tid}",
                        resolution_status="unresolved", reason=None)
        r.update(kw)
        r["_source_node"] = kw.get("_source_node")
        self.queue.append(r)
        self.references.append(r)
        return r

    # ------------------------------------------------------------------ run
    def run(self):
        try:
            self.proj = DjangoProject.discover(self.root)
        except Exception as e:
            self.notes.append(f"Django project discovery failed: {type(e).__name__}: {e}")
        if self.proj is None:
            self.notes.append("no Django project found: routes, views and template names stay unresolved")
        if self.py is None:
            self.py = PythonBroker(self.root, "manage.py", [], framework="none")
        try:
            if not self.py._index_ready:
                self.py.index_repository()          # the ONLY indexing pass, shared by every traced view
        except Exception as e:
            self.notes.append(f"Python indexing failed: {type(e).__name__}: {e}")
        for s in (self.seeds or [t for t in discover_templates(self.root)]):
            self._seed(s)
        processed = 0
        while self.queue:
            if processed >= self.max_references:
                self.notes.append(f"stopped after {processed} references (max_references); pending references remain")
                break
            ref = self.queue.popleft()
            processed += 1
            try:
                if ref["target_type"] == "html_file":
                    self._do_html(ref)
                elif ref["target_type"] == "python_view":
                    self._do_view(ref)
                else:
                    self._do_resolve(ref)
            except Exception as e:                  # a failed reference is recorded; the traversal goes on
                self._fail(ref, e)
        self._finalize()
        return self

    def _seed(self, s):
        s = s.replace("\\", "/")
        if s.startswith("/"):
            nid = f"seed:{s}"
            self.graph.node(nid, "seed", None, None)
            self._push(target=s, target_type="url", relationship="seed", _source_node=nid)
        elif s.lower().endswith(_HTML_EXT):
            self._push(target=os.path.relpath(os.path.join(self.root, s), self.root).replace(os.sep, "/")
                       if os.path.isabs(s) else s, target_type="html_file", relationship="seed", resolved_file=s)
        elif ":" in s and s.split(":")[0].endswith(".py"):
            f, name = s.split(":", 1)
            nid = f"seed:{s}"
            self.graph.node(nid, "seed", None, None)
            self._push(target=s, target_type="python_view", relationship="seed", resolved_file=f,
                       resolved_symbol=name, _source_node=nid, _view={"file": f, "line": None, "status": "resolved"})
        else:
            self.notes.append(f"seed {s!r} ignored: expected an HTML template, a URL path, or <file.py>:<symbol>")

    def _fail(self, ref, exc):
        reason = f"{type(exc).__name__}: {exc}"
        ref.update(resolution_status="failed", reason=reason)
        self._unresolved(source=ref["source_file"], line=ref["source_line"], reference=ref["target"],
                         reason=reason, category="traversal_error", traversal_id=ref["traversal_id"], status="failed")

    # ------------------------------------------------------------------ HTML
    def _do_html(self, ref):
        rel = ref["target"]
        if rel in self.visited_files:               # visited-file registry: also what terminates include cycles
            ref.update(resolved=True, resolved_file=rel, resolution_status="resolved")
            return
        full = os.path.join(self.root, rel)
        text, issues, err = read_text(full)
        if err:
            self.visited_files[rel] = "failed"
            self.graph.node(rel, "template", rel, 1, status="failed", reason=err, discovered=True)
            self._unresolved(source=ref["source_file"], line=ref["source_line"], reference=rel, reason=err,
                             category="missing_file", traversal_id=ref["traversal_id"], status="failed")
            ref.update(resolution_status="failed", reason=err)
            return
        self.visited_files[rel] = "analysed"
        records, iss, stats = analyze_text(rel, text)
        comp = complete_html_extraction(rel, text)
        n_lines = len(comp.get("source_lines", []))
        self.graph.node(rel, "template", rel, 1, discovered=True, line_count=n_lines, issues=len(issues + iss) or None)
        for i in issues + iss + comp.get("issues", []):
            self._unresolved(source=rel, line=None, reference=rel, reason=f"parse issue: {i}",
                             category="parse_issue", status="partial")
        elements = {}
        stack = [comp.get("document_tree") or {}]
        while stack:
            n = stack.pop()
            if n.get("node_type") == "element":
                elements.setdefault(n["start_line"], []).append(n)
            stack.extend(n.get("children", []))
        ref.update(resolved=True, resolved_file=rel, resolution_status="resolved")
        for r in records:
            rt = r.get("relationship")
            if not rt or rt in _SKIP_REL or r.get("in_html_comment") or r.get("also_in_element"):
                continue
            target = r.get("target") if r.get("target") is not None else r.get("expression")
            if target is None or r.get("target_type") is None:
                continue
            src = self._source_node(rel, r, elements)
            self._push(source_file=rel, source_line=r["line"], target=target, target_type=r["target_type"],
                       relationship=rt, _source_node=src)

    def _source_node(self, rel, r, elements):
        """The logical HTML element (or Django template tag) a reference sits on; multiline elements keep every line."""
        line = r["line"]
        el = next((e for e in elements.get(line, []) if e.get("tag") == r["element_type"]), None)
        if el is not None:
            nid = el["node_id"]
            if nid not in self.graph.nodes:
                self.graph.node(nid, "html_element", rel, el["start_line"], end_line=el["end_line"], tag=el["tag"],
                                text=r.get("text") or None, source_text=(el.get("open_source") or "")[:400])
                self._edge(rel, nid, "contains", file=rel, line=el["start_line"])
            return nid
        nid = f"{rel}#L{line}:{{%{r['element_type']}%}}"
        if nid not in self.graph.nodes:
            self.graph.node(nid, "template_tag", rel, line, tag=r["element_type"], source_text=r.get("raw") or r.get("expression"))
            self._edge(rel, nid, "contains", file=rel, line=line)
        return nid

    # ------------------------------------------------------------------ reference resolution
    @staticmethod
    def _map(res):
        return {"resolved": "resolved", "not_applicable": "not_applicable"}.get(res["status"], "unresolved")

    def _do_resolve(self, ref):
        ttype, target, rel = ref["target_type"], ref["target"], ref["relationship"]
        src = ref["_source_node"]
        key = (ttype, target)
        ent = self._res.get(key)
        if ent is None:
            if self.proj is None and ttype not in ("dynamic", "external_url", "mailto", "tel", "javascript", "data_uri", "fragment"):
                res = OrderedDict(status="unresolved", reason="no Django project found: reference cannot be verified")
            else:
                res = resolve_reference(self.proj, ttype, target, rel, ref["source_file"])
            ent = self._res[key] = {"res": res, "rid": ref_node_id(ttype, target, src), "expanded": False}
        res, rid = ent["res"], ent["rid"]
        status = self._map(res)
        reason = res.get("reason")
        ref.update(resolved=status == "resolved", resolution_status=status, reason=reason)
        self.graph.node(rid, _REF_NODE_TYPE.get(ttype, ttype))
        self._edge(src, rid, rel, status, file=ref["source_file"], line=ref["source_line"],
                   traversal_id=ref["traversal_id"], target_type=ttype, reason=reason)
        if status == "unresolved":
            self._unresolved(source=ref["source_file"], line=ref["source_line"], reference=target, reason=reason,
                             category=_CATEGORY.get(ttype, "unresolved"), traversal_id=ref["traversal_id"], status=status)
        if status != "resolved":
            return
        kind = res.get("kind")
        if kind == "url_pattern":
            self._expand_route(ref, ent, res, rid)
        elif kind == "template":
            ref["resolved_file"] = res["file"]
            if not ent["expanded"]:
                ent["expanded"] = True
                self.graph.node(res["file"], "template", res["file"], 1, discovered=True)
                self._edge(rid, res["file"], "resolves_to", loader=res.get("loader"), traversal_id=ref["traversal_id"],
                           duplicate=res.get("duplicate") or None, shadowed=res.get("shadowed") or None)
                self._push(source_file=ref["source_file"], source_line=ref["source_line"], target=res["file"],
                           target_type="html_file", relationship=rel, resolved_file=res["file"], _source_node=rid)
        elif kind == "static_file":
            ref["resolved_file"] = res["file"]
            if not ent["expanded"]:
                ent["expanded"] = True
                self.graph.node(res["file"], "static_file", res["file"], 1, discovered=True, traced=True)
                self._edge(rid, res["file"], "resolves_to", traversal_id=ref["traversal_id"])
        v = res.get("view") or {}
        if v.get("symbol") and ref["resolved_symbol"] is None:
            ref.update(resolved_file=v.get("file"), resolved_symbol=v["symbol"])

    def _expand_route(self, ref, ent, res, rid):
        route = res["route_id"]
        self.graph.node(route, "url_pattern", res["pattern_file"], res["pattern_line"], pattern=res["pattern"],
                        url_name=res.get("name"))
        self._edge(rid, route, "resolves_to", pattern=res["pattern"], file=res["pattern_file"], line=res["pattern_line"],
                   traversal_id=ref["traversal_id"])
        if route in self._routes_done:              # several links reach one route: its view is handled once
            return
        self._routes_done.add(route)
        self._url_configuration(route, res)
        v = res.get("view") or {}
        rn = self.graph.nodes[route]
        loc = dict(file=res["pattern_file"], line=res["pattern_line"])
        if v.get("status") == "resolved" and not v.get("external") and v.get("file"):
            vid = _view_node(self.graph, v)
            rn["view_status"] = "identified"
            self._edge(route, vid, "dispatches_to", "partial", via=v.get("text"), wrapper=v.get("wrapper"),
                       traversal_id=ref["traversal_id"], resolved_file=v["file"], resolved_symbol=v.get("symbol"),
                       reason="view identified; Python tracing pending", **loc)
            self._push(source_file=res["pattern_file"], source_line=res["pattern_line"], target=vid,
                       target_type="python_view", relationship="dispatches_to", resolved_file=v["file"],
                       resolved_symbol=v.get("symbol"), _source_node=route, _view=v)
        elif v.get("status") == "resolved" and v.get("external"):
            vid = _view_node(self.graph, v)
            why = f"view {v.get('symbol')} is provided outside the repository; it cannot be traced"
            self.graph.nodes[vid].update(python_trace="external", reason=why)
            rn["view_status"] = "external"
            self._edge(route, vid, "dispatches_to", "partial", via=v.get("text"), reason=why,
                       traversal_id=ref["traversal_id"], **loc)
        else:
            why = v.get("reason") or "view not resolved"
            rn["view_status"] = "unresolved"
            rn["reason"] = why
            self._unresolved(source=res["pattern_file"], line=res["pattern_line"], reference=v.get("text"), reason=why,
                             category="unresolved_view", traversal_id=ref["traversal_id"], status="partial")

    def _url_configuration(self, route, res):
        """URL configuration files that produced a route (root urls.py -> include() -> app urls.py)."""
        r = next((x for x in self.proj.routes if x.id == route), None)
        chain = list(getattr(r, "include_chain", None) or [res["pattern_file"]])
        for f in chain:
            self.graph.node(f, "python_file", f, 1, discovered=True, role="url_configuration")
        for a, b in zip(chain, chain[1:]):
            self._edge(a, b, "includes_urls", file=a)
        self._edge(route, res["pattern_file"], "defined_in", file=res["pattern_file"], line=res["pattern_line"])

    # ------------------------------------------------------------------ Python tracing + template hand-off
    def _do_view(self, ref):
        sid, route, view = ref["target"], ref["_source_node"], ref.get("_view") or {}
        if sid in self.visited_symbols:             # visited-symbol registry: a view reached by many links is traced once
            summ = self.python_traces.get(sid)
            if summ:
                self._apply_view_status(route, sid, summ)
                ref.update(resolved=True, resolution_status=_TRACE_TO_STATUS.get(summ["status"], "partial"))
            return
        self.visited_symbols.add(sid)
        f, name = ref["resolved_file"], ref["resolved_symbol"]
        tr = self.py.trace_view(f, name) if name else OrderedDict(status="failed", reason="view symbol unknown", edges=[],
                                                                  dispatch_methods=[], bases=[], kind=None, line=None)
        summ = OrderedDict(status=tr["status"], reason=tr.get("reason"), file=f, symbol=name,
                           kind=tr.get("kind"), line=tr.get("line"), dispatch_methods=tr.get("dispatch_methods", []),
                           bases=tr.get("bases", []), calls=len(tr.get("edges", [])))
        self.python_traces[sid] = summ
        self.graph.node(sid, tr.get("kind") or "view", f, tr.get("line") or view.get("line"))
        self.graph.nodes[sid].update({k: v for k, v in dict(
            python_trace=tr["status"], reason=tr.get("reason"), dispatch_methods=tr.get("dispatch_methods") or None,
            bases=tr.get("bases") or None).items() if v is not None})
        self._apply_view_status(route, sid, summ)
        ref.update(resolved=tr["status"] != "failed", resolution_status=_TRACE_TO_STATUS.get(tr["status"], "partial"),
                   reason=tr.get("reason"))
        if tr["status"] == "failed":
            self._unresolved(source=f, line=view.get("line"), reference=sid, reason=tr.get("reason"),
                             category="python_trace_failed", traversal_id=ref["traversal_id"], status="failed")
            return
        for e in tr["edges"]:
            self._py_edge(e)
        self._py_file(f)
        new = (self.py.reached | {sid}) - self._seen_reached      # symbols the Python broker reached for the first time
        self._seen_reached |= new
        for s in sorted(new):
            sym = self.py.symbols.get(s)
            if sym is None:
                continue
            self.graph.node(s, sym.kind, sym.file, sym.line)
            self._py_file(sym.file)
            if s in self._tscan:
                continue
            self._tscan.add(s)
            vd = view if s == sid and view.get("file") else {"file": sym.file, "line": sym.line, "status": "resolved"}
            self._templates_of(vd, s)

    def _apply_view_status(self, route, sid, summ):
        st = _TRACE_TO_STATUS.get(summ["status"], "partial")
        self._set_status(route, sid, "dispatches_to", st, summ.get("reason") or ("Python tracing succeeded" if st == "resolved" else None))

    def _py_file(self, rel):
        if rel in self._py_files or not rel:
            return
        self._py_files.add(rel)
        self.graph.node(rel, "python_file", rel, 1, discovered=True)
        for alias, imp in sorted(self.py.imports.get(rel, {}).items()):    # one import hop from every traced file
            mod, name, lvl = imp.get("module") or "", imp.get("name"), imp.get("level", 0)
            for cand in ([f"{mod}.{name}" if mod else name] if name else []) + [mod]:
                try:
                    tgt = self.py.find_module_file(cand, lvl, rel) if cand else None
                except Exception:
                    tgt = None
                if tgt and tgt != rel and tgt in self.py.py_files:
                    self.graph.node(tgt, "python_file", tgt, 1, discovered=True)
                    self._edge(rel, tgt, "imports", origin="python_broker", file=rel, line=imp.get("line"))
                    break

    def _py_edge(self, e):
        for nid in (e["source"], e["target"]):
            sym = self.py.symbols.get(nid)
            self.graph.node(nid, sym.kind if sym else "symbol", sym.file if sym else None, sym.line if sym else None)
            if sym:
                self._py_file(sym.file)
        self._edge(e["source"], e["target"], str(e["type"]), origin="python_broker", file=e.get("file"), line=e.get("line"))

    def _templates_of(self, view, sid):
        """Templates rendered by a traced view / function -> back to the HTML Broker through the same queue."""
        if self.proj is None:
            return
        found = view_templates(self.proj, view)
        named = [t for t in found if t.get("template") and not t.get("dynamic")]
        for t in found:
            if t.get("dynamic") or not t.get("template"):
                expr = t.get("expression") or ""
                if named and expr.startswith("self.template_name"):      # already covered by the class attribute
                    continue
                self._unresolved(source=t.get("file"), line=t.get("line"), reference=expr or None,
                                 reason="dynamic template name: expression not evaluated (static analysis only)",
                                 category="dynamic_template", status="unresolved")
                continue
            self._push(source_file=t.get("file") or view.get("file"), source_line=t.get("line"), target=t["template"],
                       target_type="template", relationship="renders", _source_node=sid)

    # ------------------------------------------------------------------ results
    def _finalize(self):
        g = self.graph
        for rel in discover_templates(self.root):                  # discovered files stay represented
            g.node(rel, "template", rel, 1, discovered=True)
        for rel in sorted(self.py.py_files):
            g.node(rel, "python_file", rel, 1, discovered=True)
        for n in g.nodes.values():
            if n["type"] == "template":
                n["traced"] = self.visited_files.get(n["id"]) == "analysed"
            elif n["type"] == "python_file":
                n["traced"] = n["id"] in self.py.reached_files or n.get("role") == "url_configuration"
        incoming = {}
        for e in g.edges:
            if e["type"] not in ("contains",):
                incoming.setdefault(e["target"], []).append(e["status"])
        for n in g.nodes.values():                                  # node status: the same vocabulary as edges
            if n.get("status"):
                continue
            t = n["type"]
            if t in ("template", "python_file"):
                n["status"] = "resolved" if n["traced"] else "discovered"
            elif n.get("python_trace"):
                n["status"] = _TRACE_TO_STATUS.get(n["python_trace"], "partial")
            elif t == "url_pattern":
                vs = n.get("view_status")
                n["status"] = "resolved" if vs == "identified" else "partial"
            else:
                n["status"] = _worst(incoming.get(n["id"])) or "resolved"
        # a link is only "resolved" when its route AND view were found and the view was traced
        route_ok = {}
        for e in g.edges:
            if e["type"] == "dispatches_to":
                route_ok[e["source"]] = e["status"]
        for e in g.edges:
            if e["type"] == "resolves_to" and e["target"] in route_ok and e["status"] == "resolved":
                rs = route_ok[e["target"]]
                if rs != "resolved":
                    e["status"], e["verified"] = "partial", False
                    e["reason"] = e.get("reason") or "route matched, but its view was not fully traced"
        for e in g.edges:
            if e["type"] not in ("contains", "resolves_to", "dispatches_to") and e.get("target_type") in ("url", "url_name") \
                    and e["status"] == "resolved":
                out = next((x for x in g.edges if x["source"] == e["target"] and x["type"] == "resolves_to"), None)
                if out and out["status"] != "resolved":
                    e["status"], e["verified"] = "partial", False
                    e["reason"] = "route matched, but its view was not identified or fully traced"
        for r in self.references:
            if r["target_type"] in ("url", "url_name") and r["resolution_status"] == "resolved":
                ent = self._res.get((r["target_type"], r["target"]))
                if ent:
                    out = self._ek.get((ent["rid"], (ent["res"] or {}).get("route_id"), "resolves_to"))
                    if out and out["status"] != "resolved":
                        r["resolution_status"] = "partial"

    def document(self):
        d = self.graph.to_json()
        refs = [OrderedDict((k, v) for k, v in r.items() if not k.startswith("_")) for r in self.references]
        node_status = {}
        for n in d["nodes"]:
            node_status[n["status"]] = node_status.get(n["status"], 0) + 1
        edge_status = {}
        for e in d["edges"]:
            if e["type"] != "contains":
                edge_status[e["status"]] = edge_status.get(e["status"], 0) + 1
        ref_status = {}
        for r in refs:
            ref_status[r["resolution_status"]] = ref_status.get(r["resolution_status"], 0) + 1
        nodes = d["nodes"]
        tpl = [n for n in nodes if n["type"] == "template"]
        pyf = [n for n in nodes if n["type"] == "python_file"]
        stats = OrderedDict(
            discovery=OrderedDict(templates=len(tpl), python_files=len(pyf)),
            tracing=OrderedDict(templates_traced=sum(1 for n in tpl if n.get("traced")),
                                python_files_traced=sum(1 for n in pyf if n.get("traced")),
                                views_traced=sum(1 for s in self.python_traces.values() if s["status"] == "traced"),
                                views_partial=sum(1 for s in self.python_traces.values() if s["status"] == "partial"),
                                views_failed=sum(1 for s in self.python_traces.values() if s["status"] == "failed")),
            resolution=OrderedDict(references=len(refs), by_status=ref_status, edges_by_status=edge_status),
            graph=OrderedDict(nodes=len(nodes), edges=len(d["edges"]), node_status=node_status,
                              unresolved=len(d["unresolved"])))
        return OrderedDict(
            schema=SCHEMA, schema_version=VERSION,
            meta=OrderedDict(root=self.root, seeds=self.seeds, django=bool(self.proj),
                             settings=getattr(self.proj, "settings_file", None), root_urlconf=getattr(self.proj, "urlconf", None),
                             notes=self.notes),
            statistics=stats,
            traversal=OrderedDict(visited_files=list(self.visited_files.items()),
                                  visited_symbols=sorted(self.visited_symbols), python_traces=list(self.python_traces.values())),
            references=refs, nodes=nodes, edges=d["edges"], unresolved=d["unresolved"])


_TRACE_TO_STATUS = {"traced": "resolved", "partial": "partial", "failed": "failed", "external": "partial"}
