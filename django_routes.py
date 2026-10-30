"""Static Django route / template resolution for PatchPlus brokers.

Nothing here executes project code and nothing here depends on a broker (so there are no circular imports).
It answers two questions from the project's real configuration, never from folder-name conventions:

    DjangoRouteResolver(root).resolve_path("/accounts/login/")   -> which urlpattern / view file handles it
    DjangoRouteResolver(root).resolve_name("accounts:login")     -> the same for {% url 'accounts:login' %}
    TemplateIndex(root).lookup("accounts/login.html")            -> the template file(s) with that name

How a route is resolved
-----------------------
1. ROOT_URLCONF is read from the project's settings module(s) (a module-level string assignment).
2. That URLconf's ``urlpatterns`` is evaluated statically: ``path()`` / ``re_path()`` / ``url()`` items,
   ``include("dotted.module")``, ``include((patterns, app_name))``, inline ``include([...])``, namespaces,
   ``urlpatterns += [...]`` and list concatenation.  Prefixes of nested includes are joined, so the full
   route is matched exactly the way Django matches it (first match wins).
3. The matched view expression (``views.login``, ``LoginView.as_view()``, ``login_required(views.x)``) is
   followed through the URLconf file's imports to the project file that defines it.  Views that live
   outside the project (``django.contrib.auth.views.LoginView``) are reported as ``external``; a
   ``template_name=`` given to ``as_view()`` is still returned as a template hint.

Anything that cannot be evaluated statically (``router.urls``, conditionals, computed routes, custom path
converters) is counted in ``notes`` and reported as the reason when a route does not match -- a route that
cannot be resolved confidently is returned as ``unresolved``; a target is never invented.
"""
from __future__ import annotations

import ast
import os
import posixpath
import re
from urllib.parse import urlsplit

EXCLUDE_DIRS = {".git", "__pycache__", "node_modules", ".venv", "venv", "build", "dist", ".tox"}
TEMPLATE_EXTENSIONS = (".html", ".htm", ".xhtml")

_CONVERTERS = {
    "int": r"[0-9]+", "str": r"[^/]+", "slug": r"[-a-zA-Z0-9_]+", "path": r".+",
    "uuid": r"[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}",
}
_PATH_PARAM = re.compile(r"<(?:(?P<conv>[^>:]+):)?(?P<name>[^>]+)>")
_URL_FUNCS = {"path", "re_path", "url"}


def _walk_files(root, suffixes):
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = sorted(d for d in dirnames if d not in EXCLUDE_DIRS)
        for fn in sorted(filenames):
            if fn.lower().endswith(suffixes):
                yield os.path.relpath(os.path.join(dirpath, fn), root).replace(os.sep, "/")


def _dotted(node):
    """Name / Attribute chain -> ['a', 'b', 'c'] or None."""
    parts = []
    while isinstance(node, ast.Attribute):
        parts.append(node.attr)
        node = node.value
    if isinstance(node, ast.Name):
        parts.append(node.id)
        return parts[::-1]
    return None


def _str(node):
    return node.value if isinstance(node, ast.Constant) and isinstance(node.value, str) else None


# ----------------------------------------------------------------------------------------------------
# templates
# ----------------------------------------------------------------------------------------------------
class TemplateIndex:
    """Template name -> candidate files, from every ``templates`` directory of the project.

    The name is the path below that directory (``accounts/login.html``).  All candidates are returned
    (nothing is discarded): Django's real choice depends on settings TEMPLATES / INSTALLED_APPS order.
    """

    def __init__(self, root):
        self.root = os.path.abspath(root)
        self._index = None

    def _build(self):
        idx = {}
        for rel in _walk_files(self.root, TEMPLATE_EXTENSIONS):
            parts = rel.split("/")
            for i, part in enumerate(parts[:-1]):
                if part == "templates":
                    idx.setdefault("/".join(parts[i + 1:]), []).append(rel)
        self._index = idx

    def lookup(self, name):
        if self._index is None:
            self._build()
        name = (name or "").strip().lstrip("/")
        return list(dict.fromkeys(self._index.get(name, [])))


# ----------------------------------------------------------------------------------------------------
# routes
# ----------------------------------------------------------------------------------------------------
class DjangoRouteResolver:
    def __init__(self, root):
        self.root = os.path.abspath(root)
        self.notes = []                       # constructs that could not be evaluated statically
        self._py = None
        self._trees = {}
        self._table = None
        self._roots = None
        self._bases = None
        self.unavailable_reason = None

    # -- files ----------------------------------------------------------
    @property
    def py_files(self):
        if self._py is None:
            self._py = set(_walk_files(self.root, (".py",)))
        return self._py

    def _tree(self, rel):
        if rel not in self._trees:
            try:
                with open(os.path.join(self.root, rel), "rb") as fh:
                    self._trees[rel] = ast.parse(fh.read(), filename=rel)
            except (OSError, SyntaxError, ValueError):
                self._trees[rel] = None
        return self._trees[rel]

    @property
    def bases(self):
        """Directories from which dotted module names are resolved: the project root and every directory
        holding a manage.py (Django's sys.path root)."""
        if self._bases is None:
            b = [""]
            for f in sorted(self.py_files):
                if posixpath.basename(f) == "manage.py" and posixpath.dirname(f) not in b:
                    b.append(posixpath.dirname(f))
            self._bases = b
        return self._bases

    def module_file(self, dotted, from_file=None, level=0):
        """Dotted module name -> project-relative .py file, or None (exact match only, no basename guessing)."""
        parts = [p for p in (dotted or "").split(".") if p]
        if level:
            base = posixpath.dirname(from_file or "")
            for _ in range(level - 1):
                base = posixpath.dirname(base)
            bases = [base]
        else:
            bases = self.bases
        for base in bases:
            stem = posixpath.join(base, *parts) if parts else base
            for cand in ([stem + ".py", posixpath.join(stem, "__init__.py")] if parts
                         else [posixpath.join(stem, "__init__.py")]):
                cand = cand.lstrip("/")
                if cand in self.py_files:
                    return cand
        return None

    # -- ROOT_URLCONF -------------------------------------------------------
    def root_urlconfs(self):
        if self._roots is None:
            found = []
            for rel in sorted(self.py_files):
                try:
                    with open(os.path.join(self.root, rel), "rb") as fh:
                        if b"ROOT_URLCONF" not in fh.read():
                            continue
                except OSError:
                    continue
                tree = self._tree(rel)
                for st in (tree.body if tree else []):
                    if isinstance(st, ast.Assign) and any(isinstance(t, ast.Name) and t.id == "ROOT_URLCONF"
                                                          for t in st.targets):
                        target = _str(st.value)
                        f = self.module_file(target) if target else None
                        if f and f not in found:
                            found.append(f)
            self._roots = found
            if not found:
                self.unavailable_reason = "no ROOT_URLCONF that names a project file was found"
        return self._roots

    @property
    def available(self):
        return bool(self.root_urlconfs())

    # -- imports of one file ---------------------------------------------------
    def _imports(self, rel):
        out = {}
        tree = self._tree(rel)
        if tree is None:
            return out
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for a in node.names:
                    out[a.asname or a.name.split(".")[0]] = ("module", a.name if a.asname else a.name.split(".")[0])
            elif isinstance(node, ast.ImportFrom):
                for a in node.names:
                    out[a.asname or a.name] = ("from", node.module or "", a.name, node.level)
        return out

    def _defines(self, rel, name):
        tree = self._tree(rel)
        for st in (tree.body if tree else []):
            if isinstance(st, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)) and st.name == name:
                return st.lineno
        return None

    def _find_symbol(self, rel, name, depth=0):
        """(file, line) where ``name`` is defined, following simple ``from x import name`` re-exports."""
        line = self._defines(rel, name)
        if line:
            return rel, line
        if depth < 3:
            for alias, b in self._imports(rel).items():
                if alias == name and b[0] == "from":
                    f = self.module_file(b[1], rel, b[3])
                    if f:
                        hit = self._find_symbol(f, b[2], depth + 1)
                        if hit:
                            return hit
        return None

    # -- view expression -> file ----------------------------------------------
    def _lookup(self, rel, parts):
        """Follow a dotted name used in ``rel`` to the project file defining it."""
        first, rest = parts[0], parts[1:]
        binding = self._imports(rel).get(first)
        if binding is None:
            line = self._defines(rel, first)
            if line:
                return dict(status="resolved", view_file=rel, view_symbol=first, view_line=line)
            return dict(status="unresolved", reason=f"name '{first}' is neither imported nor defined in {rel}")
        if binding[0] == "from":
            _, module, name, level = binding
            sub = self.module_file((module + "." if module else "") + name, rel, level)   # name is a submodule
            if sub:                                                # `from pkg import views` ; views.func
                if rest:
                    return self._symbol_result(sub, rest[0])
                return dict(status="unresolved", reason=f"'{name}' is a module, not a view")
            mod_file = self.module_file(module, rel, level)
            if mod_file is None:
                if level:
                    return dict(status="unresolved", reason=f"relative import of '{name}' does not resolve to a file")
                return dict(status="external", reason=f"view '{name}' comes from '{module}', outside the project",
                            view_symbol=name)
            return self._symbol_result(mod_file, name)
        dotted = binding[1]                                        # plain `import a.b` / `import a.b as x`
        for i in range(len(rest), -1, -1):
            f = self.module_file(".".join([dotted] + rest[:i]), rel)
            if f and i < len(rest):
                return self._symbol_result(f, rest[i])
        return dict(status="external", reason=f"'{'.'.join(parts)}' is outside the project")

    def _symbol_result(self, mod_file, symbol):
        hit = self._find_symbol(mod_file, symbol)
        if hit:
            return dict(status="resolved", view_file=hit[0], view_symbol=symbol, view_line=hit[1])
        return dict(status="resolved", view_file=mod_file, view_symbol=symbol, view_line=None,
                    note=f"symbol '{symbol}' not found by static lookup in {mod_file}; module file is certain")

    def _module_of_expr(self, rel, parts):
        """``include(accounts_urls)`` / ``include(accounts.urls)``: dotted expression -> project module file."""
        b = self._imports(rel).get(parts[0])
        if b is None:
            return None
        if b[0] == "from":
            dotted, level, rest = (b[1] + "." if b[1] else "") + b[2], b[3], parts[1:]
        else:
            dotted, level, rest = b[1], 0, parts[1:]
        f = self.module_file(dotted, rel, level)
        for part in rest:
            dotted += "." + part
            f = self.module_file(dotted, rel, level)
        return f

    def _view_target(self, rel, node, hints):
        if isinstance(node, ast.Call):
            parts = _dotted(node.func)
            if parts and parts[-1] == "as_view" and isinstance(node.func, ast.Attribute):
                for kw in node.keywords:
                    if kw.arg == "template_name":
                        tn = _str(kw.value)
                        if tn:
                            hints.append(tn)
                return self._view_target(rel, node.func.value, hints)
            if node.args:                                           # decorator-style wrapper: wrapper(view)
                return self._view_target(rel, node.args[0], hints)
            return dict(status="unresolved", reason="view is a call expression that cannot be followed")
        parts = _dotted(node)
        if not parts:
            return dict(status="unresolved", reason=f"view expression ({type(node).__name__}) is not a name")
        return self._lookup(rel, parts)

    # -- urlpatterns evaluation ------------------------------------------------
    def _module_assigns(self, rel, name):
        tree = self._tree(rel)
        for st in (tree.body if tree else []):
            if isinstance(st, ast.Assign) and any(isinstance(t, ast.Name) and t.id == name for t in st.targets):
                return st.value
        return None

    def _flatten(self, rel, expr, depth=0):
        """List / tuple / `a + b` / simple name -> the url Call nodes, in order."""
        if isinstance(expr, (ast.List, ast.Tuple)):
            out = []
            for e in expr.elts:
                out += self._flatten(rel, e, depth + 1) if isinstance(e, (ast.List, ast.Tuple, ast.BinOp, ast.Name)) \
                    else [e]
            return out
        if isinstance(expr, ast.BinOp) and isinstance(expr.op, ast.Add):
            return self._flatten(rel, expr.left, depth + 1) + self._flatten(rel, expr.right, depth + 1)
        if isinstance(expr, ast.Name) and depth < 4:
            val = self._module_assigns(rel, expr.id)
            if val is not None:
                return self._flatten(rel, val, depth + 1)
        self.notes.append(f"{rel}: urlpatterns expression ({ast.unparse(expr)[:60]}) not evaluated statically")
        return []

    def _urlpatterns(self, rel):
        tree = self._tree(rel)
        items = []
        for st in (tree.body if tree else []):
            if isinstance(st, ast.Assign) and any(isinstance(t, ast.Name) and t.id == "urlpatterns" for t in st.targets):
                items = self._flatten(rel, st.value)
            elif isinstance(st, ast.AnnAssign) and isinstance(st.target, ast.Name) and st.target.id == "urlpatterns" \
                    and st.value is not None:
                items = self._flatten(rel, st.value)
            elif isinstance(st, ast.AugAssign) and isinstance(st.target, ast.Name) and st.target.id == "urlpatterns" \
                    and isinstance(st.op, ast.Add):
                items += self._flatten(rel, st.value)
            elif isinstance(st, ast.Expr) and isinstance(st.value, ast.Call) and isinstance(st.value.func, ast.Attribute) \
                    and _dotted(st.value.func.value) == ["urlpatterns"] and st.value.func.attr in ("append", "extend"):
                if st.value.func.attr == "append" and st.value.args:
                    items.append(st.value.args[0])
                elif st.value.args:
                    items += self._flatten(rel, st.value.args[0])
        return items

    @staticmethod
    def _segment(kind, route):
        """(kind, route text) -> a regex fragment without anchors or named groups, or None."""
        if kind == "path":
            rx, pos = "", 0
            for m in _PATH_PARAM.finditer(route):
                rx += re.escape(route[pos:m.start()])
                rx += "(" + _CONVERTERS.get(m.group("conv") or "str", r"[^/]+") + ")"
                pos = m.end()
            return rx + re.escape(route[pos:])
        rx = route[1:] if route.startswith("^") else route
        return re.sub(r"\(\?P<\w+>", "(", rx)

    def _pattern_items(self, rel, calls, segments, raws, ns, app_ns, chain, stack, out):
        for call in calls:
            if not isinstance(call, ast.Call):
                self.notes.append(f"{rel}: urlpatterns item ({ast.unparse(call)[:60]}) is not a path()/re_path() call")
                continue
            fparts = _dotted(call.func)
            fname = fparts[-1] if fparts else None
            if fname not in _URL_FUNCS:
                self.notes.append(f"{rel}:{call.lineno}: urlpatterns item '{fname or ast.unparse(call.func)}(...)' "
                                  f"is not path()/re_path()")
                continue
            kind = "path" if fname == "path" else "re_path"
            route = _str(call.args[0]) if call.args else None
            if route is None:
                self.notes.append(f"{rel}:{call.lineno}: route is not a string literal")
                continue
            seg = self._segment(kind, route)
            try:
                re.compile(seg)
            except re.error:
                self.notes.append(f"{rel}:{call.lineno}: route regex {route!r} could not be compiled")
                continue
            view = call.args[1] if len(call.args) > 1 else next((k.value for k in call.keywords if k.arg == "view"), None)
            name = next((_str(k.value) for k in call.keywords if k.arg == "name"), None)
            if view is None:
                continue
            if isinstance(view, ast.Call) and (_dotted(view.func) or [""])[-1] == "include":
                self._include(rel, call, view, segments + [seg], raws + [route], ns, app_ns, chain, stack, out)
                continue
            if not isinstance(view, ast.Call) and (_dotted(view) or [""])[-1] == "urls":
                # `path("admin/", admin.site.urls)` / `path("x/", some_app.urls)`: an include in disguise
                synthetic = ast.copy_location(ast.Call(func=ast.Name(id="include", ctx=ast.Load()),
                                                       args=[view], keywords=[]), call)
                self._include(rel, call, synthetic, segments + [seg], raws + [route], ns, app_ns, chain, stack, out)
                continue
            hints = []
            target = self._view_target(rel, view, hints)
            out.append(dict(segments=segments + [seg], route="".join(raws + [route]), name=name,
                            ns=list(ns), app_ns=list(app_ns), urlconf=rel, line=call.lineno, chain=list(chain),
                            prefix_only=False, template_hints=hints, **target))

    def _include(self, rel, call, inc, segments, raws, ns, app_ns, chain, stack, out):
        arg = inc.args[0] if inc.args else None
        namespace = next((_str(k.value) for k in inc.keywords if k.arg == "namespace"), None)
        app_name = None
        patterns, target_file, external = None, None, None
        if isinstance(arg, ast.Tuple) and len(arg.elts) == 2:
            app_name = _str(arg.elts[1])
            arg = arg.elts[0]
        if _str(arg) is not None:
            target_file = self.module_file(_str(arg), rel)
            external = _str(arg) if target_file is None else None
        elif isinstance(arg, (ast.List,)):
            patterns = self._flatten(rel, arg)
        elif arg is not None and _dotted(arg):
            parts = _dotted(arg)
            target_file = self._module_of_expr(rel, parts)
            if target_file is None:
                external = ".".join(parts)
        else:
            self.notes.append(f"{rel}:{call.lineno}: include() argument not understood")
            return
        if external is not None:                                    # e.g. admin.site.urls, django.contrib.auth.urls
            out.append(dict(segments=segments, route="".join(raws), name=None, ns=list(ns), app_ns=list(app_ns), urlconf=rel,
                            line=call.lineno, chain=list(chain), prefix_only=True, template_hints=[],
                            status="external", reason=f"route is handled by include('{external}'), outside the project"))
            return
        if target_file is not None:
            if target_file in stack:
                self.notes.append(f"{rel}:{call.lineno}: include cycle through {target_file}")
                return
            if app_name is None:
                v = self._module_assigns(target_file, "app_name")
                app_name = _str(v) if v is not None else None
            patterns = self._urlpatterns(target_file)
            sub_file, sub_stack, sub_chain = target_file, stack + (target_file,), chain + [target_file]
        else:
            sub_file, sub_stack, sub_chain = rel, stack, chain
        eff_ns = namespace or app_name
        self._pattern_items(sub_file, patterns or [], segments, raws, ns + ([eff_ns] if eff_ns else []),
                            app_ns + ([app_name] if app_name else ([namespace] if namespace else [])),
                            sub_chain, sub_stack, out)

    @property
    def table(self):
        if self._table is None:
            self._table = []
            for rf in self.root_urlconfs():
                self._pattern_items(rf, self._urlpatterns(rf), [], [], [], [], [rf], (rf,), self._table)
        return self._table

    # -- public API -----------------------------------------------------------------
    def resolve_path(self, url):
        """URL path (``/accounts/login/``; query / fragment ignored) -> resolution dict."""
        if not self.available:
            return dict(status="unresolved", reason=self.unavailable_reason or "not a Django project")
        path = urlsplit(url).path.lstrip("/")
        for e in self.table:
            try:
                rx = re.compile("".join(f"(?:{s})" for s in e["segments"]))
            except re.error:
                continue
            ok = rx.match(path) if e["prefix_only"] else rx.fullmatch(path)
            if ok:
                return self._public(e, url)
        why = f"no urlpattern in {', '.join(self.root_urlconfs())} matches '/{path}'"
        if self.notes:
            why += f" ({len(self.notes)} urlpattern construct(s) could not be evaluated statically)"
        return dict(status="unresolved", reason=why)

    def resolve_name(self, url_name):
        """``name`` or ``namespace:name`` (as in {% url %}) -> resolution dict (status may be 'ambiguous')."""
        if not self.available:
            return dict(status="unresolved", reason=self.unavailable_reason or "not a Django project")
        *spaces, leaf = (url_name or "").strip().split(":")
        hits = [e for e in self.table if e.get("name") == leaf and not e["prefix_only"]
                and (e["ns"] == spaces or e["app_ns"] == spaces)]
        if not hits:
            return dict(status="unresolved", reason=f"no urlpattern named '{url_name}' found in the URL configuration")
        results = [self._public(e, None) for e in hits]
        files = {r.get("view_file") for r in results}
        if len(files) > 1 or any(r["status"] == "unresolved" for r in results):
            first = dict(results[0])
            first.update(status="ambiguous", candidates=results,
                         reason=f"{len(results)} urlpatterns are named '{url_name}'")
            return first
        return results[0]

    @staticmethod
    def _public(e, url):
        keys = ("status", "reason", "note", "view_file", "view_symbol", "view_line", "name", "template_hints",
                "prefix_only")
        res = {k: e[k] for k in keys if k in e}
        res.update(route=e["route"], namespace=":".join(e["ns"]) or None, urlconf=e["urlconf"], urlconf_line=e["line"],
                   urlconf_chain=e["chain"], matched_url=url)
        return res
