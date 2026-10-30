"""Django route / template resolver (design milestones M4 and M5).  A component SEPARATE from the HTML parser.

Reads Django configuration STATICALLY (``ast`` only: nothing is imported or executed, no HTTP) and verifies
references that the HTML broker extracted:

  M4  url path / url name  -> URL pattern (project + app URL configs, include() prefixes, namespaces) -> view
  M5  template name        -> template file (TEMPLATES DIRS, then APP_DIRS of INSTALLED_APPS, in loader order)
      static file          -> file under STATICFILES_DIRS / <app>/static

Rules taken from the design (sections 7, 9, 10):
  * a reference is ``resolved`` only after it was verified against the configuration;
  * dynamic / unknown things stay ``unresolved`` or ``dynamic`` with a reason - nothing is guessed;
  * an unknown route is kept as such and no Python destination is invented;
  * duplicate template names keep every candidate path; the loader order picks the first only when the
    loader configuration is known.
Result dicts: {status: resolved|unresolved|dynamic|not_applicable, reason, ...kind-specific keys}.
"""
import ast
import os
import posixpath
import re
from collections import OrderedDict

try:
    from broker_common import EXCLUDE_DIRS
except ImportError:                                     # pragma: no cover
    EXCLUDE_DIRS = {".git", "__pycache__", "node_modules", ".venv", "venv", "build", "dist"}

URL_FUNCS = ("path", "re_path", "url")
_CONVERTERS = {"str": "[^/]+", "int": "[0-9]+", "slug": "[-a-zA-Z0-9_]+", "path": ".+",
               "uuid": "[0-9a-f]{8}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{4}-[0-9a-f]{12}"}
_ROUTE_PARAM = re.compile(r"<(?:(?P<conv>[^>:]+):)?(?P<name>[^>]+)>")
_RENDER_FUNCS = {"render": 1, "render_to_string": 0, "get_template": 0, "select_template": 0,
                 "TemplateResponse": 1, "render_to_response": 0}
# django.contrib.auth.urls is part of Django, not of the repository: its pattern table is fixed by Django.
_BUILTIN_INCLUDES = {
    "django.contrib.auth.urls": [
        ("login/", "login", "LoginView"), ("logout/", "logout", "LogoutView"),
        ("password_change/", "password_change", "PasswordChangeView"),
        ("password_change/done/", "password_change_done", "PasswordChangeDoneView"),
        ("password_reset/", "password_reset", "PasswordResetView"),
        ("password_reset/done/", "password_reset_done", "PasswordResetDoneView"),
        ("reset/<uidb64>/<token>/", "password_reset_confirm", "PasswordResetConfirmView"),
        ("reset/done/", "password_reset_complete", "PasswordResetCompleteView")]}


def _r(status, reason=None, **kw):
    d = OrderedDict(status=status)
    if reason:
        d["reason"] = reason
    d.update(kw)
    return d


def _const_str(n):
    if isinstance(n, ast.Constant) and isinstance(n.value, str):
        return n.value
    if isinstance(n, ast.Call) and len(n.args) == 1 and isinstance(n.func, (ast.Name, ast.Attribute)):
        nm = n.func.id if isinstance(n.func, ast.Name) else n.func.attr
        if nm in ("_", "gettext", "gettext_lazy", "ugettext", "ugettext_lazy"):     # translated route
            return _const_str(n.args[0])
    return None


def _kw(call, name):
    return next((k.value for k in call.keywords if k.arg == name), None)


class Route:
    """One fully expanded URL pattern (all include() prefixes applied)."""

    def __init__(self, **kw):
        self.__dict__.update(kw)

    def to_json(self):
        return {k: v for k, v in self.__dict__.items() if not k.startswith("_") and k != "regex_obj"}


class DjangoProject:
    def __init__(self, root):
        self.root = os.path.abspath(root)
        self.source_roots = [self.root]
        self.settings_file = self.urlconf = None
        self.settings_candidates, self.issues = [], []
        self.installed_apps, self.app_dirs = [], OrderedDict()
        self.template_dirs, self.app_dirs_enabled, self.loaders_known = [], True, True
        self.static_url = self.media_url = None
        self.staticfiles_dirs = []
        self.routes, self.dynamic_entries, self.names = [], [], {}
        self._ast, self._env, self._files = {}, {}, None

    # ------------------------------------------------------------ files / modules
    def _all_py(self):
        if self._files is None:
            self._files = []
            for dp, dn, fn in os.walk(self.root):
                dn[:] = sorted(d for d in dn if d not in EXCLUDE_DIRS)
                self._files += [os.path.relpath(os.path.join(dp, f), self.root).replace(os.sep, "/")
                                for f in sorted(fn) if f.endswith(".py")]
        return self._files

    def parse(self, rel):
        if rel not in self._ast:
            try:
                with open(os.path.join(self.root, rel), "rb") as f:
                    self._ast[rel] = ast.parse(f.read().decode("utf-8", "replace"))
            except (OSError, SyntaxError, ValueError) as e:
                self._ast[rel] = None
                self.issues.append(f"{rel}: cannot parse ({type(e).__name__})")
        return self._ast[rel]

    def module_file(self, dotted):
        """dotted module name -> repo-relative file, or None (external / missing)."""
        p = dotted.replace(".", "/")
        for sr in self.source_roots:
            for cand in (f"{p}.py", f"{p}/__init__.py"):
                rel = posixpath.normpath(posixpath.join(sr, cand))
                if os.path.isfile(os.path.join(self.root, rel)):
                    return rel
        return None

    def dotted_of(self, rel):
        for sr in sorted(self.source_roots, key=len, reverse=True):
            pre = "" if sr == "." else sr + "/"
            if rel.startswith(pre):
                d = rel[len(pre):][:-3]
                return d[:-9].rstrip("/").replace("/", ".") if d.endswith("__init__") else d.replace("/", ".")
        return rel[:-3].replace("/", ".")

    def _package_of(self, rel):
        d = self.dotted_of(rel)
        return d if rel.endswith("__init__.py") else d.rpartition(".")[0]

    def imports(self, rel):
        """alias -> ('module', dotted) | ('name', dotted_module, name) for one file (relative imports resolved)."""
        key = ("imports", rel)
        if key in self._env:
            return self._env[key]
        out, tree = {}, self.parse(rel)
        for n in (ast.walk(tree) if tree else ()):
            if isinstance(n, ast.Import):
                for a in n.names:
                    out[a.asname or a.name.split(".")[0]] = ("module", a.name if a.asname else a.name.split(".")[0])
            elif isinstance(n, ast.ImportFrom):
                mod = n.module or ""
                if n.level:
                    pkg = self._package_of(rel).split(".") if self._package_of(rel) else []
                    pkg = pkg[:len(pkg) - (n.level - 1)] if n.level > 1 else pkg
                    mod = ".".join(pkg + ([n.module] if n.module else []))
                for a in n.names:
                    if a.name == "*":
                        continue
                    sub = f"{mod}.{a.name}" if mod else a.name
                    out[a.asname or a.name] = ("module", sub) if self.module_file(sub) else ("name", mod, a.name)
        self._env[key] = out
        return out

    def find_def(self, rel, name, depth=0):
        """Top-level class / function ``name`` in file ``rel`` (following re-exports) -> (file, line, kind) | None."""
        tree = self.parse(rel)
        for n in (tree.body if tree else ()):
            if isinstance(n, ast.ClassDef) and n.name == name:
                return rel, n.lineno, "class"
            if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef)) and n.name == name:
                return rel, n.lineno, "function"
        imp = self.imports(rel).get(name) if depth < 4 else None
        if imp and imp[0] == "name":
            f = self.module_file(imp[1])
            if f:
                return self.find_def(f, imp[2], depth + 1)
        if tree and depth < 4:                                       # from .x import *
            for n in tree.body:
                if isinstance(n, ast.ImportFrom) and any(a.name == "*" for a in n.names):
                    mod = n.module or ""
                    if n.level:
                        pkg = self._package_of(rel).split(".")
                        pkg = pkg[:len(pkg) - (n.level - 1)] if n.level > 1 else pkg
                        mod = ".".join(pkg + ([n.module] if n.module else []))
                    f = self.module_file(mod)
                    hit = f and self.find_def(f, name, depth + 1)
                    if hit:
                        return hit
        return None

    # ------------------------------------------------------------ settings
    def module_env(self, rel, depth=0):
        """Top-level assignments of a module -> {name: ast node}; ``from x import *`` is merged."""
        key = ("env", rel)
        if key in self._env:
            return self._env[key]
        env, tree = {}, self.parse(rel)
        for n in (tree.body if tree else ()):
            if isinstance(n, ast.ImportFrom) and any(a.name == "*" for a in n.names) and depth < 4:
                mod = n.module or ""
                if n.level:
                    pkg = self._package_of(rel).split(".") if self._package_of(rel) else []
                    pkg = pkg[:len(pkg) - (n.level - 1)] if n.level > 1 else pkg
                    mod = ".".join(pkg + ([n.module] if n.module else []))
                f = self.module_file(mod)
                if f:
                    env.update(self.module_env(f, depth + 1))
            elif isinstance(n, ast.Assign):
                for t in n.targets:
                    if isinstance(t, ast.Name):
                        env[t.id] = n.value
            elif isinstance(n, ast.AnnAssign) and isinstance(n.target, ast.Name) and n.value is not None:
                env[n.target.id] = n.value
            elif isinstance(n, ast.AugAssign) and isinstance(n.target, ast.Name) and isinstance(n.op, ast.Add) \
                    and n.target.id in env:
                env[n.target.id] = ast.BinOp(left=env[n.target.id], op=ast.Add(), right=n.value)
        self._env[key] = env
        return env

    def _seq(self, node, env):
        """list / tuple / a + b / name -> list of element nodes, or None if not statically known."""
        if isinstance(node, (ast.List, ast.Tuple)):
            return list(node.elts)
        if isinstance(node, ast.Name) and node.id in env:
            return self._seq(env[node.id], env)
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
            a, b = self._seq(node.left, env), self._seq(node.right, env)
            return a + b if a is not None and b is not None else None
        return None

    def _str(self, node, env, depth=0):
        s = _const_str(node)
        if s is not None:
            return s
        if isinstance(node, ast.Name) and node.id in env and depth < 5:
            return self._str(env[node.id], env, depth + 1)
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Add):
            a, b = self._str(node.left, env, depth + 1), self._str(node.right, env, depth + 1)
            return a + b if a is not None and b is not None else None
        return None

    def _path(self, node, env, file, depth=0):
        """Path expression (BASE_DIR / 'x', os.path.join, Path(__file__).resolve().parent...) -> repo-relative posix."""
        if depth > 8:
            return None
        s = _const_str(node)
        if s is not None:
            return s
        if isinstance(node, ast.Name):
            if node.id == "__file__":
                return file
            return self._path(env[node.id], env, file, depth + 1) if node.id in env else None
        if isinstance(node, ast.BinOp) and isinstance(node.op, ast.Div):
            a, b = self._path(node.left, env, file, depth + 1), self._path(node.right, env, file, depth + 1)
            return posixpath.normpath(posixpath.join(a, b)) if a is not None and b is not None else None
        if isinstance(node, ast.Attribute) and node.attr == "parent":
            a = self._path(node.value, env, file, depth + 1)
            return posixpath.dirname(a) or "." if a is not None else None
        if isinstance(node, ast.Subscript) and isinstance(node.value, ast.Attribute) and node.value.attr == "parents":
            a = self._path(node.value.value, env, file, depth + 1)
            k = node.slice.value if isinstance(node.slice, ast.Constant) else None
            for _ in range((k if isinstance(k, int) else -1) + 1):
                if a is None:
                    break
                a = posixpath.dirname(a) or "."
            return a if isinstance(k, int) else None
        if isinstance(node, ast.Call):
            f = node.func
            nm = f.attr if isinstance(f, ast.Attribute) else (f.id if isinstance(f, ast.Name) else "")
            if nm in ("resolve", "absolute", "abspath", "realpath", "normpath", "str", "Path", "PurePath") and node.args:
                return self._path(node.args[0], env, file, depth + 1)
            if nm in ("resolve", "absolute") and isinstance(f, ast.Attribute):
                return self._path(f.value, env, file, depth + 1)
            if nm == "dirname" and node.args:
                a = self._path(node.args[0], env, file, depth + 1)
                return (posixpath.dirname(a) or ".") if a is not None else None
            if nm == "join" and node.args:
                parts = [self._path(x, env, file, depth + 1) for x in node.args]
                return posixpath.normpath(posixpath.join(*parts)) if None not in parts else None
        return None

    def _app_dir(self, dotted):
        parts = dotted.split(".")
        for i in range(len(parts), 0, -1):
            sub = ".".join(parts[:i])
            for sr in self.source_roots:
                d = posixpath.normpath(posixpath.join(sr, sub.replace(".", "/")))
                if os.path.isdir(os.path.join(self.root, d)):
                    return d
        return None

    def _load_settings(self, rel):
        env = self.module_env(rel)
        self.settings_file = rel
        u = self._str(env["ROOT_URLCONF"], env) if "ROOT_URLCONF" in env else None
        self.urlconf = u
        if "ROOT_URLCONF" not in env:
            self.issues.append(f"{rel}: ROOT_URLCONF is not defined (a Django default is not assumed)")
        elif u is None:
            self.issues.append(f"{rel}: ROOT_URLCONF is not a static string")
        apps = self._seq(env.get("INSTALLED_APPS"), env) if "INSTALLED_APPS" in env else []
        if apps is None:
            self.issues.append(f"{rel}: INSTALLED_APPS is not statically known")
            apps = []
        for a in apps:
            s = self._str(a, env)
            if s is None:
                self.issues.append(f"{rel}: non-constant INSTALLED_APPS entry skipped")
                continue
            self.installed_apps.append(s)
            self.app_dirs[s] = self._app_dir(s)                      # None = external package
        t = self._seq(env.get("TEMPLATES"), env) if "TEMPLATES" in env else None
        if t is None:
            self.loaders_known = "TEMPLATES" not in env
            if "TEMPLATES" not in env:
                self.issues.append(f"{rel}: TEMPLATES is not defined; template loader order is unknown")
            self.loaders_known = False
        for d in (t or []):
            if not isinstance(d, ast.Dict):
                self.loaders_known = False
                continue
            cfg = {self._str(k, env): v for k, v in zip(d.keys, d.values) if k is not None}
            if "django.template.backends.django.DjangoTemplates" not in (self._str(cfg["BACKEND"], env) or "") \
                    if "BACKEND" in cfg else True:
                continue
            for e in (self._seq(cfg["DIRS"], env) or [] if "DIRS" in cfg else []):
                p = self._path(e, env, rel)
                if p is None:
                    self.loaders_known = False
                    self.issues.append(f"{rel}: a TEMPLATES DIRS entry is not statically known")
                else:
                    self.template_dirs.append(p)
            if "APP_DIRS" in cfg:
                self.app_dirs_enabled = not (isinstance(cfg["APP_DIRS"], ast.Constant) and cfg["APP_DIRS"].value is False)
            opts = cfg.get("OPTIONS")
            if isinstance(opts, ast.Dict) and any(_const_str(k) == "loaders" for k in opts.keys if k):
                self.loaders_known = False
                self.issues.append(f"{rel}: custom template loaders are configured; loader order is not modelled")
            break                                                    # first DjangoTemplates engine decides
        self.static_url = self._str(env["STATIC_URL"], env) if "STATIC_URL" in env else None
        self.media_url = self._str(env["MEDIA_URL"], env) if "MEDIA_URL" in env else None
        for e in (self._seq(env.get("STATICFILES_DIRS"), env) or [] if "STATICFILES_DIRS" in env else []):
            if isinstance(e, (ast.Tuple, ast.List)) and len(e.elts) == 2:
                e = e.elts[1]
            p = self._path(e, env, rel)
            if p is not None:
                self.staticfiles_dirs.append(p)

    @classmethod
    def discover(cls, root):
        """Find the Django settings / URL configuration of a repository.  None when it is not a Django project."""
        p = cls(root)
        for rel in p._all_py():                                      # import roots: dirs holding manage.py
            if posixpath.basename(rel) == "manage.py":
                d = posixpath.dirname(rel) or "."
                if d not in p.source_roots:
                    p.source_roots.insert(0, d)
        named = []
        for rel in p._all_py():
            if posixpath.basename(rel) in ("manage.py", "wsgi.py", "asgi.py"):
                t = p.parse(rel)
                for n in (ast.walk(t) if t else ()):
                    if isinstance(n, ast.Call) and len(n.args) >= 2 and _const_str(n.args[0]) == "DJANGO_SETTINGS_MODULE":
                        s = _const_str(n.args[1])
                        f = s and p.module_file(s)
                        if f and f not in named:
                            named.append(f)
        cands = list(named)
        for rel in p._all_py():
            if rel in cands:
                continue
            try:
                with open(os.path.join(p.root, rel), "r", encoding="utf-8", errors="replace") as f:
                    txt = f.read()
            except OSError:
                continue
            if "ROOT_URLCONF" in txt or "INSTALLED_APPS" in txt:
                env = p.module_env(rel)
                if "ROOT_URLCONF" in env or "INSTALLED_APPS" in env:
                    cands.append(rel)
        p.settings_candidates = cands
        if not cands:
            return None
        pick = next((c for c in cands if "ROOT_URLCONF" in p.module_env(c)), cands[0])
        if len(cands) > 1:
            p.issues.append(f"several settings modules found {cands}; using {pick} "
                            f"({'named by DJANGO_SETTINGS_MODULE' if pick in named else 'first with ROOT_URLCONF'})")
        p._load_settings(pick)
        if p.urlconf:
            f = p.module_file(p.urlconf)
            if f:
                p._expand(f, "", [], [], [f], f"^")
            else:
                p.issues.append(f"ROOT_URLCONF {p.urlconf!r} is not a module of the repository")
        for r in p.routes:
            if r.name:
                p.names.setdefault(r.full_name, []).append(r)
        return p

    def describe(self):
        return (f"settings={self.settings_file} urlconf={self.urlconf} routes={len(self.routes)} "
                f"apps={len(self.installed_apps)}")

    # ------------------------------------------------------------ URL configuration (M4)
    @staticmethod
    def _route_regex(route, endpoint):
        out, last = "", 0
        for m in _ROUTE_PARAM.finditer(route):
            out += re.escape(route[last:m.start()])
            conv = m.group("conv") or "str"
            out += "(?:" + _CONVERTERS.get(conv, ".+?") + ")"
            last = m.end()
        out += re.escape(route[last:])
        return out + (r"\Z" if endpoint else "")

    def _convs(self, route):
        return [(m.group("name"), m.group("conv") or "str") for m in _ROUTE_PARAM.finditer(route)]

    def _import_target(self, rel, node):
        """Module/name node in a URL conf -> ('module', dotted) | ('name', module, name) | None."""
        imp = self.imports(rel)
        if isinstance(node, ast.Name):
            return imp.get(node.id)
        if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name):
            base = imp.get(node.value.id)
            if base and base[0] == "module":
                sub = f"{base[1]}.{node.attr}"
                return ("module", sub) if self.module_file(sub) else ("name", base[1], node.attr)
        return None

    def _view(self, rel, node):
        """View expression -> OrderedDict(text, status, kind, file, line, symbol, external, template_name?, reason?)."""
        text = ast.unparse(node)
        v = OrderedDict(text=text)
        if isinstance(node, ast.Lambda):
            v.update(status="dynamic", reason="view is a lambda")
            return v
        if isinstance(node, ast.Call):
            f = node.func
            if isinstance(f, ast.Attribute) and f.attr == "as_view":
                inner = self._view(rel, f.value)
                tn = _kw(node, "template_name")
                if tn is not None:
                    inner["as_view_template_name"] = _const_str(tn)
                    inner["as_view_template_line"] = node.lineno
                inner["text"] = text
                return inner
            if node.args:                                            # login_required(view) style wrappers
                inner = self._view(rel, node.args[0])
                inner["wrapper"] = ast.unparse(f)
                inner["text"] = text
                return inner
            v.update(status="unresolved", reason="view call without a resolvable argument")
            return v
        tgt = self._import_target(rel, node)
        name = node.id if isinstance(node, ast.Name) else (node.attr if isinstance(node, ast.Attribute) else None)
        if isinstance(node, ast.Name) and not tgt:                   # defined in the URL module itself
            hit = self.find_def(rel, node.id)
            if hit:
                return self._found(v, hit, node.id)
        if tgt and tgt[0] == "name":
            f = self.module_file(tgt[1])
            if not f:
                v.update(status="resolved", external=True, symbol=f"{tgt[1]}.{tgt[2]}",
                         reason=f"{tgt[1]} is not part of the repository")
                return v
            hit = self.find_def(f, tgt[2])
            if hit:
                return self._found(v, hit, tgt[2])
            v.update(status="unresolved", reason=f"{tgt[2]} is not defined in {f}")
            return v
        if isinstance(node, ast.Attribute) and isinstance(node.value, ast.Name):
            base = imp = self.imports(rel).get(node.value.id)
            if base and base[0] == "module":
                f = self.module_file(base[1])
                if not f:
                    v.update(status="resolved", external=True, symbol=f"{base[1]}.{node.attr}",
                             reason=f"{base[1]} is not part of the repository")
                    return v
                hit = self.find_def(f, node.attr)
                if hit:
                    return self._found(v, hit, node.attr)
                v.update(status="unresolved", reason=f"{node.attr} is not defined in {f}")
                return v
        v.update(status="unresolved", reason=f"cannot resolve view reference {text!r}")
        return v

    @staticmethod
    def _found(v, hit, name=None):
        f, line, kind = hit
        v.update(status="resolved", file=f, line=line, kind=kind)
        if name:                                  # the callable's own name (wrappers / as_view() keep it intact)
            v["symbol"] = name
        return v

    def _expand(self, rel, prefix_display, prefix_regex, ns, stack, _root):
        tree = self.parse(rel)
        if tree is None:
            return
        env = self.module_env(rel)
        app_name = self._str(env["app_name"], env) if "app_name" in env else None
        elts = []
        for n in tree.body:                                          # urlpatterns = [...]; urlpatterns += [...]
            tgt = None
            if isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == "urlpatterns" for t in n.targets):
                tgt = n.value
            elif isinstance(n, ast.AugAssign) and isinstance(n.target, ast.Name) and n.target.id == "urlpatterns":
                tgt = n.value
            if tgt is not None:
                seq = self._seq(tgt, env)
                if seq is None:
                    self.dynamic_entries.append({"file": rel, "line": n.lineno, "reason": "urlpatterns is not a static list",
                                                 "expression": ast.unparse(tgt)[:120]})
                else:
                    elts += seq
        if not elts and "urlpatterns" not in env:
            self.issues.append(f"{rel}: no urlpatterns")
        self._walk(rel, elts, prefix_display, prefix_regex, ns, stack, env)

    def _walk(self, rel, elts, pdisp, pregex, ns, stack, env):
        for e in elts:
            if not (isinstance(e, ast.Call) and isinstance(e.func, (ast.Name, ast.Attribute))):
                self.dynamic_entries.append({"file": rel, "line": getattr(e, "lineno", 0),
                                             "reason": "urlpatterns entry is not a path()/re_path() call",
                                             "expression": ast.unparse(e)[:120]})
                continue
            fn = e.func.id if isinstance(e.func, ast.Name) else e.func.attr
            if fn not in URL_FUNCS or len(e.args) < 2:
                self.dynamic_entries.append({"file": rel, "line": e.lineno, "reason": f"unrecognised registration {fn}()",
                                             "expression": ast.unparse(e)[:120]})
                continue
            route = self._str(e.args[0], env)
            if route is None:
                self.dynamic_entries.append({"file": rel, "line": e.lineno, "reason": "route is not a static string",
                                             "expression": ast.unparse(e.args[0])[:120]})
                continue
            is_re = fn in ("re_path", "url")
            view = e.args[1]
            name_node = _kw(e, "name")
            name = _const_str(name_node) if name_node is not None else None
            if isinstance(view, ast.Call) and isinstance(view.func, (ast.Name, ast.Attribute)) and \
                    (view.func.id if isinstance(view.func, ast.Name) else view.func.attr) == "include":
                self._include(rel, e, view, route, is_re, pdisp, pregex, ns, stack, env)
                continue
            regex = "".join(pregex) + (route if is_re and not pregex else (route.lstrip("^") if is_re else
                                       self._route_regex(route, True)))
            if ast.unparse(view).endswith("site.urls"):               # admin.site.urls: Django's own include
                self.routes.append(Route(
                    id=f"route:{len(self.routes)}", file=rel, line=e.lineno, kind="path", route=route,
                    full_route=pdisp + route, name=None, full_name=None, namespaces=list(ns), params=[],
                    view=OrderedDict(text=ast.unparse(view), status="resolved", external=True,
                                     symbol="django.contrib.admin.sites.AdminSite.urls",
                                     reason="Django admin; not part of the repository"),
                    regex="^" + "".join(pregex) + self._route_regex(route, False), is_regex=False,
                    include_chain=list(stack), prefix=True))
                continue
            vd = self._view(rel, view)
            full_name = ":".join(ns + [name]) if name else None
            self.routes.append(Route(
                id=f"route:{len(self.routes)}", file=rel, line=e.lineno, kind="re_path" if is_re else "path",
                route=route, full_route=pdisp + route.lstrip("^") if is_re else pdisp + route, name=name,
                full_name=full_name, namespaces=list(ns), params=self._convs(route) if not is_re else
                re.findall(r"\(\?P<(\w+)>", route), view=vd, regex="^" + regex if not regex.startswith("^") else regex,
                is_regex=is_re, include_chain=list(stack)))

    def _include(self, rel, e, view, route, is_re, pdisp, pregex, ns, stack, env):
        arg = view.args[0] if view.args else None
        ns_kw = _kw(view, "namespace")
        namespace = _const_str(ns_kw) if ns_kw is not None else None
        part = (route.lstrip("^") if is_re else self._route_regex(route, False))
        newdisp = pdisp + route.lstrip("^")
        newreg = pregex + [part if is_re else part]
        if arg is None:
            self.dynamic_entries.append({"file": rel, "line": e.lineno, "reason": "include() without an argument",
                                         "expression": ast.unparse(e)[:120]})
            return
        target_rel, app_name = None, None
        if isinstance(arg, ast.Tuple) and len(arg.elts) == 2:        # include((patterns, app_name))
            app_name = _const_str(arg.elts[1])
            arg = arg.elts[0]
        mod = _const_str(arg)
        if mod is None and isinstance(arg, (ast.Name, ast.Attribute)):
            t = self._import_target(rel, arg)
            if t and t[0] == "module":
                mod = t[1]
            elif isinstance(arg, ast.Name) and arg.id in env:        # include(extra_patterns) - list in this file
                seq = self._seq(env[arg.id], env)
                if seq is not None:
                    self._walk(rel, seq, newdisp, newreg, ns + ([namespace or app_name] if (namespace or app_name) else []),
                               stack, env)
                    return
        if mod is None:
            self.dynamic_entries.append({"file": rel, "line": e.lineno, "reason": "include() target is not statically known "
                                         "(e.g. router.urls)", "expression": ast.unparse(e)[:120]})
            return
        if mod in _BUILTIN_INCLUDES:
            nsx = ns + ([namespace] if namespace else [])
            for r, nm, vcls in _BUILTIN_INCLUDES[mod]:
                pre = "".join(newreg)
                self.routes.append(Route(
                    id=f"route:{len(self.routes)}", file=rel, line=e.lineno, kind="path", route=r, full_route=newdisp + r,
                    name=nm, full_name=":".join(nsx + [nm]), namespaces=nsx, params=self._convs(r),
                    view=OrderedDict(text=f"django.contrib.auth.views.{vcls}.as_view()", status="resolved", external=True,
                                     symbol=f"django.contrib.auth.views.{vcls}",
                                     reason="Django built-in; not part of the repository"),
                    regex="^" + pre + self._route_regex(r, True), is_regex=False, include_chain=list(stack) + [mod],
                    builtin_include=mod))
            return
        target_rel = self.module_file(mod)
        if target_rel is None:
            self.dynamic_entries.append({"file": rel, "line": e.lineno,
                                         "reason": f"included module {mod!r} is not part of the repository",
                                         "expression": ast.unparse(e)[:120], "external": True})
            return
        if target_rel in stack:
            self.issues.append(f"{rel}:{e.lineno}: include cycle through {target_rel}")
            return
        tenv = self.module_env(target_rel)
        app_name = app_name or (self._str(tenv["app_name"], tenv) if "app_name" in tenv else None)
        label = namespace or app_name
        self._expand_included(target_rel, newdisp, newreg, ns + ([label] if label else []), stack + [target_rel])

    def _expand_included(self, rel, pdisp, pregex, ns, stack):
        tree, env = self.parse(rel), self.module_env(rel)
        elts = []
        for n in (tree.body if tree else ()):
            tgt = n.value if (isinstance(n, ast.Assign) and any(isinstance(t, ast.Name) and t.id == "urlpatterns"
                                                                for t in n.targets)) or \
                (isinstance(n, ast.AugAssign) and isinstance(n.target, ast.Name) and n.target.id == "urlpatterns") else None
            if tgt is not None:
                seq = self._seq(tgt, env)
                if seq is None:
                    self.dynamic_entries.append({"file": rel, "line": n.lineno, "reason": "urlpatterns is not a static list",
                                                 "expression": ast.unparse(tgt)[:120]})
                else:
                    elts += seq
        self._walk(rel, elts, pdisp, pregex, ns, stack, env)

    # ------------------------------------------------------------ lookups
    @staticmethod
    def _route_info(r):
        return OrderedDict(route_id=r.id, pattern=r.full_route, pattern_file=r.file, pattern_line=r.line,
                           name=r.full_name, route_kind=r.kind, view=r.view)

    def match_path(self, path):
        for r in self.routes:
            try:
                rx = re.compile(re.sub(r"\(\?P<\w+>", "(?:", r.regex))
            except re.error:
                continue
            if rx.match(path):
                return r
        return None

    # M5 -------------------------------------------------------------
    def template_loader_dirs(self):
        """Candidate template directories in Django loader order: DIRS, then each installed app's templates/."""
        dirs = [(d, "DIRS") for d in self.template_dirs]
        if self.app_dirs_enabled:
            for app, d in self.app_dirs.items():
                if d:
                    dirs.append((posixpath.join(d, "templates"), f"app:{app}"))
        return dirs

    def find_template(self, name):
        cands = []
        for d, origin in self.template_loader_dirs():
            rel = posixpath.normpath(posixpath.join(d, name))
            if os.path.isfile(os.path.join(self.root, rel)):
                cands.append({"file": rel, "loader": origin})
        return cands

    def to_document(self):
        return OrderedDict(
            settings=self.settings_file, settings_candidates=self.settings_candidates, root_urlconf=self.urlconf,
            installed_apps=[{"app": a, "dir": d} for a, d in self.app_dirs.items()],
            templates={"dirs": self.template_dirs, "app_dirs": self.app_dirs_enabled,
                       "loader_order_known": bool(self.loaders_known),
                       "search_order": [{"dir": d, "origin": o} for d, o in self.template_loader_dirs()]},
            static={"static_url": self.static_url, "media_url": self.media_url, "dirs": self.staticfiles_dirs},
            routes=[r.to_json() for r in self.routes], dynamic_entries=self.dynamic_entries, issues=self.issues)


def view_templates(proj, view, _depth=0):
    """Templates a resolved repository view names: [{template, line, file, how} | {dynamic ...}].  Class-based views
    also inherit ``template_name`` from repository base classes.  Nothing is executed."""
    out = []
    if view.get("as_view_template_name"):
        out.append({"template": view["as_view_template_name"], "file": None, "line": view.get("as_view_template_line"),
                    "how": "as_view(template_name=...)"})
    f, line = view.get("file"), view.get("line")
    if not f or view.get("status") != "resolved" or view.get("external") or _depth > 3:
        return out
    tree = proj.parse(f)
    node = next((n for n in (tree.body if tree else ()) if getattr(n, "lineno", None) == line
                 and isinstance(n, (ast.ClassDef, ast.FunctionDef, ast.AsyncFunctionDef))), None)
    if node is None:
        return out
    env = proj.module_env(f)

    def add_call(c):
        fn = c.func.id if isinstance(c.func, ast.Name) else (c.func.attr if isinstance(c.func, ast.Attribute) else None)
        if fn in _RENDER_FUNCS and len(c.args) > _RENDER_FUNCS[fn]:
            a = c.args[_RENDER_FUNCS[fn]]
            s = proj._str(a, env)
            tn = _kw(c, "template_name")
            if s is not None:
                out.append({"template": s, "file": f, "line": c.lineno, "how": f"{fn}()"})
            else:
                out.append({"template": None, "dynamic": True, "expression": ast.unparse(a)[:80], "file": f,
                            "line": c.lineno, "how": f"{fn}()"})

    for n in ast.walk(node):
        if isinstance(n, ast.Call):
            add_call(n)
    if isinstance(node, ast.ClassDef):
        for b in node.body:
            if isinstance(b, ast.Assign) and any(isinstance(t, ast.Name) and t.id == "template_name" for t in b.targets):
                s = proj._str(b.value, env)
                out.append({"template": s, "dynamic": s is None, "file": f, "line": b.lineno, "how": "template_name",
                            **({"expression": ast.unparse(b.value)[:80]} if s is None else {})})
            if isinstance(b, (ast.FunctionDef,)) and b.name == "get_template_names":
                for r in ast.walk(b):
                    if isinstance(r, ast.Return) and r.value is not None:
                        for el in (r.value.elts if isinstance(r.value, (ast.List, ast.Tuple)) else [r.value]):
                            s = proj._str(el, env)
                            out.append({"template": s, "dynamic": s is None, "file": f, "line": r.lineno,
                                        "how": "get_template_names()"})
        if not any(o["how"] == "template_name" for o in out):
            for base in node.bases:
                bv = proj._view(f, base)
                if bv.get("status") == "resolved" and bv.get("file"):
                    out += view_templates(proj, bv, _depth + 1)
    return out


def resolve_reference(proj, target_type, target, relationship=None, source_file=None):
    """Verify ONE extracted reference.  Never guesses: see module docstring."""
    if target_type in ("mailto", "tel", "javascript", "data_uri", "fragment", "external_url", "control",
                       "block", "variable"):
        return _r("not_applicable")
    if target_type == "dynamic":
        return _r("dynamic", "dynamic expression: not evaluated")
    if target_type == "relative_url":
        return _r("unresolved", "relative URL: no reliable base URL; original value preserved")
    if target_type == "template_library":
        return _r("unresolved", "template library is not resolved by this component")
    if target_type == "url":
        return _resolve_url(proj, target)
    if target_type == "url_name":
        return _resolve_name(proj, target)
    if target_type == "template":
        return _resolve_template(proj, target)
    if target_type in ("static_file", "static_resource"):
        return _resolve_static(proj, target, target_type)
    return _r("unresolved", f"no resolver for target type {target_type!r}")


def _resolve_url(proj, url):
    path = re.split(r"[?#]", url, 1)[0].lstrip("/")
    r = proj.match_path(path)
    if r is not None:
        return _r("resolved", None, kind="url_pattern", **proj._route_info(r))
    if not proj.routes and not proj.urlconf:
        return _r("unresolved", "no URL configuration found (ROOT_URLCONF unknown)")
    why = "no URL pattern in the URL configuration matches this path"
    if proj.dynamic_entries:
        why += f"; {len(proj.dynamic_entries)} dynamic/external URL entries could not be inspected"
    return _r("unresolved", why, kind="url_pattern")


def _resolve_name(proj, name):
    rs = proj.names.get(name, [])
    if not rs:
        why = f"URL name {name!r} is not defined in the URL configuration"
        if proj.dynamic_entries:
            why += f"; {len(proj.dynamic_entries)} dynamic/external URL entries could not be inspected"
        return _r("unresolved", why, kind="url_pattern")
    if len(rs) > 1:
        return _r("unresolved", f"URL name {name!r} is defined by {len(rs)} patterns; which one applies depends on arguments",
                  kind="url_pattern", candidates=[proj._route_info(r) for r in rs])
    return _r("resolved", None, kind="url_pattern", **proj._route_info(rs[0]))


def _resolve_template(proj, name):
    cands = proj.find_template(name)
    order = [d for d, _ in proj.template_loader_dirs()]
    if cands and proj.loaders_known:
        return _r("resolved", None, kind="template", file=cands[0]["file"], loader=cands[0]["loader"],
                  candidates=cands, duplicate=len(cands) > 1,
                  shadowed=[c["file"] for c in cands[1:]])
    if cands:
        return _r("unresolved", "template loader configuration is not fully known; candidates preserved, none chosen",
                  kind="template", candidates=cands)
    return _r("unresolved", "no template with this name in the configured template directories "
              "(it may come from an installed third-party app)", kind="template", searched=order)


def _resolve_static(proj, target, target_type):
    rel = target
    if target_type == "static_resource":
        pref = [u for u in (proj.static_url, proj.media_url) if u and target.startswith(u)]
        if not pref:
            return _r("unresolved", "path is not under a configured STATIC_URL / MEDIA_URL", kind="static_file")
        if proj.media_url and target.startswith(proj.media_url) and not (proj.static_url and target.startswith(proj.static_url)):
            return _r("unresolved", "MEDIA files are uploaded at runtime; not verifiable statically", kind="static_file")
        rel = target[len(pref[0]):]
    dirs = list(proj.staticfiles_dirs) + [posixpath.join(d, "static") for d in proj.app_dirs.values() if d]
    cands = [posixpath.normpath(posixpath.join(d, rel)) for d in dirs
             if os.path.isfile(os.path.join(proj.root, posixpath.normpath(posixpath.join(d, rel))))]
    if cands:
        return _r("resolved", None, kind="static_file", file=cands[0], candidates=cands)
    return _r("unresolved", "file not found in STATICFILES_DIRS or an app static/ directory", kind="static_file",
              searched=dirs)
