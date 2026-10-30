"""Python broker: the Python-specific analysis behind ``app_broker.py``.

Everything that depends on the Python language lives here: ``ast`` parsing, import and symbol
resolution, Python entry-point resolution (``setup.py`` / ``pyproject.toml`` console scripts,
``__main__`` block), execution tracing, graph /
architecture / trace-tree generation and the functionality extraction.  ``app_broker.py`` only
detects the language of an entry file and dispatches to a broker such as ``PythonBroker``.

Broker contract used by the dispatcher (every language broker follows it):

    broker = XBroker(root, entry_file, internal_hints)
    broker.run()                    # language-specific analysis
    broker.normalized_result()      # -> dict following normalized.py (schema patchplus.normalized)
    broker.reachable_count          # number of reachable symbols
    broker.summary_lines()          # short human readable result lines

Optional hooks, called by app_broker after ITS shared trace-tree processing (all of them need language
semantics, so they stay in the language broker): ``attach_trace_tree(root, stats)``,
``functionality_document()``, ``topdown_document()``, ``report_text()`` and the static
``topdown_from_trace(trace_tree_doc)`` used by ``--from-trace``.  A broker writes NO files: every output
file is written by app_broker (one authoritative writer).

``entry_file`` is a source/configuration FILE chosen by the user (never a function).  Which
function (if any) execution starts from is decided here, by ``PythonBroker.resolve_entry()``.

Legacy sources: a ``.py`` file that exists but cannot be parsed by the running interpreter's
``ast`` (typically Python 2 syntax) is still discovered, indexed and usable as an entry file.  It is
analysed by a conservative, line-based text scanner (``scan_legacy_source``) and labelled
``analysis_mode = "text"`` (lower confidence) instead of ``"ast"``.  No Python 2 interpreter is
used and no source file is ever modified.

This module deliberately does not import ``app_broker`` (no circular import).
"""
import ast
import builtins
import fnmatch
import hashlib
import io
import json
import os
import posixpath
import re
import sys
import tokenize
from collections import OrderedDict, defaultdict, namedtuple
from datetime import datetime

from broker_common import EXCLUDE_DIRS
from project_tree import build_project_tree, render_project_tree
from normalized import new_result, parse_trace

try:                                    # pyproject.toml entry declarations (Python >= 3.11)
    import tomllib
except ImportError:                     # pragma: no cover
    tomllib = None

EXCLUDE_FILES = ["test_*.py", "*_test.py"]
MAX_DEPTH = 100

STDLIB = set(getattr(sys, "stdlib_module_names", ())) or {
    "os", "sys", "json", "re", "ast", "math", "time", "datetime", "traceback",
    "subprocess", "collections", "itertools", "functools", "random", "logging",
}

# kind: symbol | module | missing | external | stdlib | builtin
Target = namedtuple("Target", "kind ref label")


class Symbol:
    def __init__(self, sid, kind, name, file, node, parent=None):
        self.id = sid
        self.kind = kind          # class | function | method
        self.name = name
        self.file = file
        self.node = node
        self.line = node.lineno
        self.parent = parent      # class id for methods


class Scope:
    def __init__(self, file, cls, owner):
        self.file = file
        self.cls = cls            # enclosing class id (or None)
        self.owner = owner        # id of function/method/entry being traced
        self.vars = {}            # local var -> Target (instance type)
        self.local_funcs = {}     # nested def name -> symbol id
        self.bindings = None      # name -> Binding (function-reference tables / aliases); None = module level
        self.multi = {}           # local var -> [Target]: SEVERAL statically possible values (no runtime input needed)


class Binding:
    """What a *name* statically stands for, as far as function references are concerned.

      kind "table"    a dict / list / tuple / set (literal) whose elements may be functions
      kind "alias"    a name that stands for one or more known functions (``h = add_task``,
                      ``h = options.get(k)``, ``for h in handlers``)
      kind "dynamic"  anything else (parameters, call results, ...).  Kept so that it SHADOWS a
                      module-level binding of the same name.

    ``entries`` holds ``(key, symbol id, line)``: ``key`` is ``("const", value)`` / ``("expr", text)`` for
    containers (the dispatch condition) and ``None`` for plain aliases.  ``partial`` means the full set of
    targets could NOT be determined statically (reassignment, mutation by unknown values, escape, ...);
    ``reasons`` says why.  Only functions defined in the analysed project are ever recorded."""

    def __init__(self, name, kind, owner, file, line):
        self.name, self.kind, self.owner, self.file, self.line = name, kind, owner, file, line
        self.entries = []
        self.partial = False
        self.reasons = []
        self.assigns = 1          # number of assignments seen for the name in its scope
        self.container = None     # "dict" | "list" | "set" for tables
        self.lookup = False       # derived from container[key] / .get(key) / iteration
        self.via = None           # name of the container a derived alias came from
        self.origin = None        # the container Binding itself (derived aliases)

    def add(self, key, sid, line):
        if not any(k == key and i == sid for k, i, _ in self.entries):
            self.entries.append((key, sid, line))

    def mark_partial(self, why):
        self.partial = True
        if why not in self.reasons:
            self.reasons.append(why)


# element kinds that can never be (or hide) a project function
_ORDINARY_NODES = (ast.Constant, ast.JoinedStr, ast.Dict, ast.List, ast.Tuple, ast.Set, ast.BinOp,
                   ast.UnaryOp, ast.Compare, ast.ListComp, ast.DictComp, ast.SetComp, ast.GeneratorExp)
# callees that receive a container but cannot mutate it in a way that matters here
_SAFE_CALLEES = {"len", "print", "sorted", "list", "tuple", "set", "frozenset", "dict", "str", "repr", "bool",
                 "any", "all", "min", "max", "enumerate", "iter", "isinstance", "sum", "reversed", "zip",
                 "next", "id", "type", "hash"}
_DEF_NODES = (ast.FunctionDef, ast.AsyncFunctionDef)
_RESOLUTION_RANK = {"resolved": 0, "possible": 1, "partial": 2}
_CONFIDENCE = {"resolved": "high", "possible": "medium", "partial": "low"}


def _key_of(node):
    """Dispatch key of a subscript / dict key: ("const", value) when literal, else ("expr", source)."""
    if isinstance(node, ast.Constant):
        v = node.value
        return ("const", v if isinstance(v, (str, int, float, bool, type(None))) else repr(v))
    if (isinstance(node, ast.UnaryOp) and isinstance(node.op, ast.USub) and isinstance(node.operand, ast.Constant)
            and isinstance(node.operand.value, (int, float))):
        return ("const", -node.operand.value)
    return ("expr", ast.unparse(node))


def _condition(key):
    """JSON form of a dispatch key (None for keyless aliases)."""
    if key is None:
        return None
    return {"key": key[1]} if key[0] == "const" else {"key_expr": key[1]}


def _iter_stmts(body):
    """Statements of a scope in source order, descending into compound statements but never into
    nested function / class definitions."""
    for st in body:
        if isinstance(st, _DEF_NODES + (ast.ClassDef,)):
            continue
        yield st
        for fld in ("body", "orelse", "finalbody"):
            sub_ = getattr(st, fld, None)
            if isinstance(sub_, list):
                yield from _iter_stmts(sub_)
        for h in getattr(st, "handlers", []):
            yield from _iter_stmts(h.body)
        for c in getattr(st, "cases", []):
            yield from _iter_stmts(c.body)


def _walk_no_defs(nodes):
    """Every AST node of a scope (lambdas included, nested defs / classes excluded)."""
    stack = list(nodes)
    while stack:
        n = stack.pop()
        yield n
        for c in ast.iter_child_nodes(n):
            if not isinstance(c, _DEF_NODES + (ast.ClassDef,)):
                stack.append(c)


def normalize_graph(doc):
    """Older graph.json documents lack the dispatch fields.  Returns a copy in which every edge has
    ``conditions`` / ``via`` / ``resolution`` / ``confidence`` (defaulted) so consumers can treat old and
    new records alike."""
    out = dict(doc)
    edges = []
    for e in doc.get("edges", []):
        e = dict(e)
        e.setdefault("conditions", [])
        e.setdefault("via", None)
        e.setdefault("resolution", "resolved" if e.get("type") in ("CALLS", "INSTANTIATES", "INHERITS", "CONTAINS")
                     else None)
        e.setdefault("confidence", "high" if e["resolution"] == "resolved" else None)
        edges.append(e)
    out["edges"] = edges
    return out


# ----------------------------------------------------------------------
# Functionality extraction (stage after trace_tree.json)
#
#   trace tree -> function registry -> leaf backtracking -> functionality units
#              -> signatures -> clusters -> functionality.json
#
# Vocabulary (kept strictly separate in the output):
#   FUNCTION      FUNC_xxxxxx  a source-level definition (file + line), one per definition
#   OCCURRENCE    OCC_xxxxxx   one place in the trace where a function appears
#   OPERATION     OP_xxxxxx    one statement executed inside a function body
#   FUNCTIONALITY F_xxxxxx     what a function (as a whole) implements, derived from its operations
#
# EXTENDING THE KNOWLEDGE BASE: add entries to CLUSTER_TAXONOMY and FUNCTIONALITY_RULES below.
# A rule scores a functionality from its *signature* (APIs, method calls, attribute names,
# callee clusters) - the function name is only a weak supporting hint, never sufficient alone.
# ----------------------------------------------------------------------
_CONTROL_RE = re.compile(r"^(?:async\s+)?(if|elif|else|for|while|try|except|finally|with)\b")
_FUNC_FILE_ENTRY = "<__main__>"
_FUNC_FILE_TOPLEVEL = "<top-level execution>"
_FUNC_FILE_FUNCENTRY = "<entry>"
_PY_KEYWORDS_CALLLIKE = {"if", "elif", "while", "for", "with", "def", "class", "return", "not", "and",
                         "or", "in", "is", "lambda", "await", "yield", "except", "assert", "del", "raise"}
_BUILTIN_NAMES = set(dir(builtins))

CLUSTER_TAXONOMY = OrderedDict([
    ("RESOURCE.IMAGE",     "Image / sprite resource handling"),
    ("UI.RENDERING",       "User-interface and screen rendering"),
    ("AUDIO.PLAYBACK",     "Audio channels, sounds and playback"),
    ("INPUT.EVENTS",       "Input and event handling"),
    ("PERSISTENCE.STORAGE", "Reading / writing persistent data"),
    ("DISPLAY.WINDOW",     "Display surface / window management"),
    ("TIMING.FRAME",       "Frame timing and clocks"),
    ("PHYSICS.COLLISION",  "Collision detection"),
    ("ENTITY.ANIMATION",   "Sprite animation state"),
    ("ENTITY.MOTION",      "Entity movement and position updates"),
    ("STATE.INIT",         "Object state initialisation"),
    ("ORCHESTRATION",      "Coordination of other functions (little own behaviour)"),
    ("UNCLASSIFIED",       "No supported semantic classification"),
])

# apis: canonical API prefixes   methods: last segment of API / object-method calls
# tokens: words of the function/class name (weak)   attr_tokens: words of attributes read/written (weak)
# callee_clusters: clusters of already-classified callees (used from the 2nd pass on)
FUNCTIONALITY_RULES = [
    # optional gates: require_apis_all (prefixes that must ALL be present), require_tokens_any (name words,
    # at least one), evidence_attr (attribute words count as evidence, needs a name-token hit)
    dict(id="image.load", cluster="RESOURCE.IMAGE",
         name=lambda s: ("image loading with transparency (colorkey) setup"
                         if "set_colorkey" in s["method_names"] else "image resource loading"),
         apis=("pygame.image.load",), methods=set(), tokens={"load", "init", "sheet", "spritesheet", "image"}),
    dict(id="image.sprite_extract", cluster="RESOURCE.IMAGE", name="sprite image extraction and scaling",
         apis=("pygame.transform.scale", "pygame.Surface", "pygame.Rect"),
         require_apis_all=("pygame.Surface", "pygame.Rect", "pygame.transform.scale"),
         methods={"subsurface", "blit", "set_colorkey"}, tokens={"image", "sprite", "extract", "at"}),
    dict(id="image.transform", cluster="RESOURCE.IMAGE", name="image transformation",
         apis=("pygame.transform.",), methods=set(), tokens={"scale", "flip", "rotate", "transform"},
         require_tokens_any={"scale", "flip", "rotate", "transform"}),
    dict(id="ui.border", cluster="UI.RENDERING", name="UI border rendering",
         apis=("pygame.draw.",), methods=set(), tokens={"border", "frame", "box", "outline"},
         require_tokens_any={"border", "frame", "box", "outline"}),
    dict(id="ui.shapes", cluster="UI.RENDERING", name="primitive shape drawing",
         apis=("pygame.draw.",), methods=set(), tokens={"draw", "render"}),
    dict(id="ui.text", cluster="UI.RENDERING", name="text rendering",
         apis=("pygame.transform.scale",), methods={"blit", "render"},
         tokens={"text", "font", "char", "string", "message", "label"},
         require_tokens_any={"text", "font", "char", "string", "message", "label"}),
    dict(id="ui.menu_background", cluster="UI.RENDERING", name="menu background rendering",
         apis=(), methods={"blit", "fill"}, tokens={"background", "menu"}, callee_clusters={"UI.RENDERING"},
         require_tokens_any={"background"}),
    dict(id="ui.level_chooser", cluster="UI.RENDERING", name="level selection UI rendering",
         apis=(), methods={"blit", "fill"}, tokens={"level", "chooser", "choose", "select"},
         callee_clusters={"UI.RENDERING"}, require_tokens_any={"level"}),
    dict(id="ui.generic_render", cluster="UI.RENDERING", name="screen rendering",
         apis=(), methods={"blit", "fill", "draw"}, tokens={"draw", "render", "show", "display", "update"},
         callee_clusters={"UI.RENDERING"}),
    dict(id="audio.music_state", cluster="AUDIO.PLAYBACK", name="music state management",
         apis=("pygame.mixer.",), methods={"play", "stop", "pause", "unpause", "fadeout"},
         tokens={"music", "toggle", "mute"}, attr_tokens={"music"}, require_tokens_any={"music", "toggle", "mute"}),
    dict(id="audio.init", cluster="AUDIO.PLAYBACK", name="audio channel and sound resource initialization",
         apis=("pygame.mixer.",), methods={"set_volume", "Channel", "Sound"},
         tokens={"init", "sound", "audio", "mixer"}),
    dict(id="audio.play", cluster="AUDIO.PLAYBACK", name="audio playback control",
         apis=("pygame.mixer.",), methods={"play", "stop", "pause", "unpause", "fadeout", "set_volume"},
         tokens={"play", "sfx", "sound", "audio", "music"}),
    dict(id="persist.save", cluster="PERSISTENCE.STORAGE",
         name=lambda s: ("persist application audio settings"
                         if s["attr_token_set"] & {"music", "sfx", "sound", "volume", "audio"}
                         else "persist application data"),
         apis=("builtins.open", "json.dump", "pickle.dump"), methods={"write", "dump", "close"},
         tokens={"save", "settings", "config", "persist", "store", "write"},
         require_tokens_any={"save", "persist", "store", "write"}),
    dict(id="persist.load", cluster="PERSISTENCE.STORAGE",
         name=lambda s: ("load persisted application audio settings"
                         if s["attr_token_set"] & {"music", "sfx", "sound", "volume", "audio"}
                         else "load persisted data"),
         apis=("builtins.open", "json.load", "pickle.load"), methods={"read", "load"},
         tokens={"load", "read", "parse", "level", "settings"}, require_tokens_any={"load", "read", "parse"}),
    dict(id="input.events", cluster="INPUT.EVENTS", name="input event handling",
         apis=("pygame.event.", "pygame.key.", "pygame.mouse."), methods={"get_pressed", "get"},
         tokens={"input", "key", "event", "mouse", "check"}),
    dict(id="display.window", cluster="DISPLAY.WINDOW", name="display surface management",
         apis=("pygame.display.",), methods=set(), tokens={"display", "screen", "window"},
         require_tokens_any={"display", "screen", "window", "init", "setup"}),
    dict(id="timing.frame", cluster="TIMING.FRAME", name="frame timing control",
         apis=("pygame.time.",), methods={"tick"}, tokens={"clock", "tick", "frame", "time"}),
    dict(id="physics.collision", cluster="PHYSICS.COLLISION", name="collision detection",
         apis=(), methods={"colliderect", "collidepoint", "collidelist", "collidelistall", "collidedict"},
         tokens={"collision", "collide", "check", "hit"}),
    dict(id="entity.animation", cluster="ENTITY.ANIMATION", name="animation state update",
         apis=(), methods=set(), tokens={"animation", "animate", "frame", "sprite"},
         attr_tokens={"frame", "animation", "image", "spriteframe"}, evidence_attr=True),
    dict(id="entity.motion", cluster="ENTITY.MOTION", name="movement and position update",
         apis=(), methods=set(), tokens={"move", "update", "velocity", "gravity", "jump", "speed"},
         attr_tokens={"vel", "rect", "x", "y", "speed", "velocity"}, evidence_attr=True,
         require_tokens_any={"move", "velocity", "gravity", "jump", "speed"}),
]
_RULE_THRESHOLD = 2.0


def _split_words(s):
    s = re.sub(r"([a-z0-9])([A-Z])", r"\1 \2", s)
    return {w.lower() for w in re.split(r"[^A-Za-z0-9]+", s) if w}


def _dotted(node):
    """a.b.c / a.b().c / a[].b -> text, or None when not a simple chain."""
    if isinstance(node, ast.Name):
        return node.id
    if isinstance(node, ast.Attribute):
        base = _dotted(node.value)
        return f"{base}.{node.attr}" if base else f"<expr>.{node.attr}"
    if isinstance(node, ast.Call):
        base = _dotted(node.func)
        return f"{base}()" if base else None
    if isinstance(node, ast.Subscript):
        base = _dotted(node.value)
        return f"{base}[]" if base else None
    return None


class _OpVisitor(ast.NodeVisitor):
    """Collects calls / attribute reads / writes from one statement or control header."""

    def __init__(self):
        self.calls, self.reads, self.writes = [], [], []
        self.returns = False

    def _target(self, t):
        if isinstance(t, (ast.Tuple, ast.List)):
            for e in t.elts:
                self._target(e)
        elif isinstance(t, ast.Starred):
            self._target(t.value)
        else:
            d = _dotted(t)
            if d:
                self.writes.append(d)
            if isinstance(t, ast.Subscript):
                self.visit(t.slice)

    def visit_Assign(self, n):
        for t in n.targets:
            self._target(t)
        self.visit(n.value)

    def visit_AugAssign(self, n):
        self._target(n.target)
        d = _dotted(n.target)
        if d:
            self.reads.append(d)
        self.visit(n.value)

    def visit_AnnAssign(self, n):
        self._target(n.target)
        if n.value:
            self.visit(n.value)

    def visit_For(self, n):
        self._target(n.target)
        self.visit(n.iter)

    def visit_withitem(self, n):
        if n.optional_vars is not None:
            self._target(n.optional_vars)
        self.visit(n.context_expr)

    def visit_Return(self, n):
        self.returns = True
        if n.value is not None:
            self.visit(n.value)

    def visit_Call(self, n):
        d = _dotted(n.func)
        if d:
            self.calls.append(d)
            if isinstance(n.func, ast.Attribute):
                base = _dotted(n.func.value)
                if base and "." in base:
                    self.reads.append(base)
        for a in n.args:
            self.visit(a)
        for k in n.keywords:
            self.visit(k.value)
        if isinstance(n.func, ast.Attribute):
            self.visit(n.func.value) if _dotted(n.func.value) is None else None

    def visit_Attribute(self, n):
        d = _dotted(n)
        if d and isinstance(n.ctx, ast.Load):
            self.reads.append(d)
        else:
            self.generic_visit(n)


def _analyze_op_text(text):
    """-> dict(calls, reads, writes, returns, parsed). Tolerates fragments / control headers."""
    t = text.strip()
    cands = []
    if t.startswith("elif "):
        cands.append("if " + t[5:] + " pass")
    if t.startswith("except"):
        cands.append("try:\n pass\n" + t + " pass")
    if t.endswith(":") and _CONTROL_RE.match(t):
        cands.append(t + " pass")
    cands.insert(0, t)
    for c in cands:
        try:
            tree = ast.parse(c)
        except SyntaxError:
            continue
        v = _OpVisitor()
        v.visit(tree)
        return dict(calls=v.calls, reads=v.reads, writes=v.writes, returns=v.returns, parsed=True)
    # regex fallback (partial statements, odd syntax)
    calls = [m for m in re.findall(r"([A-Za-z_][\w.]*)\s*\(", t) if m.split(".")[0] not in _PY_KEYWORDS_CALLLIKE]
    wm = re.match(r"^\s*([A-Za-z_][\w.\[\]]*)\s*(?:[-+*/%|&^]|//|\*\*)?=(?!=)", t)
    reads = [m for m in re.findall(r"\b[A-Za-z_]\w*(?:\.\w+)+\b(?!\s*\()", t)]
    return dict(calls=calls, reads=reads, writes=[wm.group(1)] if wm else [],
                returns=t.startswith("return"), parsed=False)


def _uniq(seq):
    seen, out = set(), []
    for x in seq:
        if x not in seen:
            seen.add(x)
            out.append(x)
    return out


# ----------------------------------------------------------------------
# Legacy / text-based analysis (files that exist but cannot be parsed by ``ast``)
#
# Deliberately conservative: imports, def/class headers, the ``__main__`` block, module-level
# statements and "name(" call sites.  It never builds a fake AST and never rewrites a source file.
# Everything it produces is lower-confidence than the AST pipeline (analysis_mode == "text").
# ----------------------------------------------------------------------
ANALYSIS_AST = "ast"
ANALYSIS_TEXT = "text"

_RE_IMPORT = re.compile(r"^\s*import\s+(.+)$")
_RE_FROM = re.compile(r"^\s*from\s+(\.*)\s*([\w.]*)\s+import\s+(.+)$")
_RE_IMPORT_NAME = re.compile(r"^\s*([\w.]+)(?:\s+as\s+(\w+))?\s*$")
_RE_DEF = re.compile(r"^(\s*)def\s+([A-Za-z_]\w*)\s*\(")
_RE_CLASS = re.compile(r"^(\s*)class\s+([A-Za-z_]\w*)\s*[(:]")
_RE_MAIN = re.compile(r"""^if\s+\(?\s*(?:__name__\s*==\s*['"]__main__['"]|['"]__main__['"]\s*==\s*__name__)\s*\)?\s*:""")
_RE_CALL = re.compile(r"(?<![\w.])([A-Za-z_]\w*(?:\s*\.\s*[A-Za-z_]\w*)*)\s*\(")
_TEXT_NOT_CALLS = _PY_KEYWORDS_CALLLIKE | {"print", "exec", "elif", "else", "try", "finally", "yield", "from",
                                           "import", "global", "nonlocal", "pass", "break", "continue"}


def split_source_lines(src):
    """Lines numbered exactly like Python numbers them (\\n, \\r\\n, \\r only; str.splitlines() would
    also split on form feeds and other separators and shift every later line number)."""
    return re.split(r"\r\n|\r|\n", src)


def _blank_strings_and_comments(lines):
    """Same number of lines; comments removed and string contents dropped (the quotes stay as ``""``),
    so a regex never matches inside a string or a docstring.  Line numbers are preserved."""
    out, triple = [], None
    for raw in lines:
        buf, i, n = [], 0, len(raw)
        while i < n:
            if triple:
                end = raw.find(triple, i)
                if end < 0:
                    i = n
                else:
                    i, triple = end + 3, None
                continue
            ch = raw[i]
            if ch == "#":
                break
            if ch in ("'", '"'):
                q3 = raw[i:i + 3]
                if q3 in ("'''", '"""'):
                    triple = q3
                    buf.append('""')
                    i += 3
                    continue
                j = i + 1
                while j < n and raw[j] != ch:
                    j += 2 if raw[j] == "\\" else 1
                buf.append(ch + ch)
                i = j + 1
                continue
            buf.append(ch)
            i += 1
        out.append("".join(buf))
    return out


def _indent_of(text):
    t = text.expandtabs(8)               # Python 2 treats a tab as up to the next multiple of 8
    return len(t) - len(t.lstrip())


def scan_legacy_source(src):
    """Line-based scan of a Python source that ``ast`` cannot parse.  Returns a dict (all line
    numbers are 1-based and refer to the ORIGINAL source):
        lines     original lines                code      the same lines, strings/comments blanked
        imports   [dict(module, name, alias, level, line)]
        defs      [dict(name, kind, line, end, indent, parent)]   kind: function | class | method | nested
        funcs / classes   top-level name -> def record
        main      None | dict(line, end, inline)  the ``if __name__ == '__main__':`` block
        toplevel  executable module-level line numbers (no def/class/import/main block)
        analysis_mode  "text"
    """
    raw = split_source_lines(src)
    code = _blank_strings_and_comments(raw)
    n = len(raw)
    ind = [_indent_of(c) if c.strip() else -1 for c in code]

    def block_end(i, k):                 # last non-blank line (0-based) of the block opened at line i
        last = i
        for j in range(i + 1, n):
            if ind[j] < 0:
                continue
            if ind[j] <= k:
                break
            last = j
        return last

    # --- imports (statements may continue with a backslash or an open parenthesis) -------------
    imports, i = [], 0
    while i < n:
        c = code[i]
        if re.match(r"^\s*(?:import|from)\b", c):
            stmt, j = c, i
            while (stmt.rstrip().endswith("\\") or stmt.count("(") > stmt.count(")")) and j + 1 < n:
                j += 1
                stmt = stmt.rstrip().rstrip("\\") + " " + code[j].strip()
            for part in stmt.split(";"):
                m = _RE_FROM.match(part)
                if m:
                    dots, module, names = m.group(1), m.group(2), m.group(3).strip().strip("()")
                    for nm in names.split(","):
                        nm = nm.strip()
                        if nm == "*":
                            imports.append(dict(module=module, name="*", alias=None, level=len(dots), line=i + 1))
                            continue
                        mm = _RE_IMPORT_NAME.match(nm)
                        if mm:
                            imports.append(dict(module=module, name=mm.group(1), alias=mm.group(2),
                                                level=len(dots), line=i + 1))
                    continue
                m = _RE_IMPORT.match(part)
                if m:
                    for nm in m.group(1).split(","):
                        mm = _RE_IMPORT_NAME.match(nm)
                        if mm:
                            imports.append(dict(module=mm.group(1), name=None, alias=mm.group(2),
                                                level=0, line=i + 1))
            i = j
        i += 1

    # --- def / class headers -------------------------------------------------------------------
    defs, stack = [], []                 # stack: [(indent, "class" | "def", name)]
    for i, c in enumerate(code):
        md, mc = _RE_DEF.match(c), _RE_CLASS.match(c)
        if not (md or mc):
            continue
        k = ind[i]
        while stack and stack[-1][0] >= k:
            stack.pop()
        parent = stack[-1] if stack else None
        if mc:
            kind = "class" if parent is None else "nested"
        elif parent is None:
            kind = "function"
        elif parent[1] == "class":
            kind = "method"
        else:
            kind = "nested"
        name = (md or mc).group(2)
        defs.append(dict(name=name, kind=kind, line=i + 1, end=block_end(i, k) + 1, indent=k,
                         parent=parent[2] if kind == "method" else None))
        stack.append((k, "class" if mc else "def", name))
    funcs = {d["name"]: d for d in defs if d["kind"] == "function"}
    classes = {d["name"]: d for d in defs if d["kind"] == "class"}

    # --- __main__ block + executable module-level lines ----------------------------------------
    main, toplevel, cur = None, [], None
    for i, c in enumerate(code):
        if ind[i] < 0:
            continue
        if ind[i] == 0:
            if main is None and c.startswith("if") and _RE_MAIN.match(raw[i].strip()):
                main = dict(line=i + 1, end=block_end(i, 0) + 1, inline=bool(c.partition(":")[2].strip()))
                cur = "main"
            elif re.match(r"^(?:def|class|import|from)\b|^@", c):
                cur = "skip"
            else:
                cur = "exec"
                if c.strip() != '""':
                    toplevel.append(i + 1)
        elif cur == "exec" and c.strip() != '""':
            toplevel.append(i + 1)

    return dict(lines=raw, code=code, imports=imports, defs=defs, funcs=funcs, classes=classes,
                main=main, toplevel=toplevel, analysis_mode=ANALYSIS_TEXT)


def legacy_code_lines(info, start, end):
    """1-based line numbers in [start, end] that carry code (no blank / comment-only / string-only)."""
    return [ln for ln in range(max(start, 1), min(end, len(info["code"])) + 1)
            if info["code"][ln - 1].strip() and info["code"][ln - 1].strip() != '""']


def legacy_calls_on_line(info, ln):
    """Dotted names that look like calls (``name(`` / ``a.b.c(``) on one line of a legacy source."""
    c = info["code"][ln - 1]
    if _RE_DEF.match(c) or _RE_CLASS.match(c) or c.lstrip().startswith("@"):
        return []
    out = []
    for m in _RE_CALL.finditer(c):
        dotted = re.sub(r"\s+", "", m.group(1))
        if dotted.split(".")[0] not in _TEXT_NOT_CALLS:
            out.append(dotted)
    return out


def _synthetic_call(dotted, line):
    """A one-node ``ast.Call`` for ``dotted()``, only so the existing call handling can be reused."""
    try:
        node = ast.parse(dotted + "()", mode="eval").body
    except SyntaxError:
        return None
    for n in ast.walk(node):
        if hasattr(n, "lineno"):
            n.lineno = n.end_lineno = line
    return node


def legacy_setup_entry_points(src):
    """Fallback parser for setup.py when AST parsing cannot extract metadata.

    Returns:
        (
            scripts,      # [(group, script_name, "module:attr"), ...]
            package_dir,  # {package_prefix: directory}
            wheres        # directories supplied to find_packages(...)
        )
    """
    text = "\n".join(
        line for line in split_source_lines(src)
        if not line.lstrip().startswith("#")
    )

    scripts = []

    # ------------------------------------------------------------
    # 1. Parse [console_scripts] / [gui_scripts] sections
    # ------------------------------------------------------------

    # Handles setuptools-style string:
    #
    # entry_points = """
    # [console_scripts]
    # foo = package.foo:main
    # bar = package.bar:main
    # """
    #
    # Also handles dictionary/list forms containing console_scripts.
    section_pattern = re.compile(
        r"\[(console_scripts|gui_scripts)\](.*?)(?=\n\s*\[[^\]]+\]|\Z)",
        re.DOTALL,
    )

    for section_match in section_pattern.finditer(text):
        group = section_match.group(1)
        section = section_match.group(2)

        for match in re.finditer(
            r"^\s*([A-Za-z0-9_.-]+)\s*=\s*"
            r"([A-Za-z_][\w.]*)\s*:\s*([A-Za-z_][\w]*)"
            r"(?:\s*\[[^\]]*\])?\s*$",
            section,
            re.MULTILINE,
        ):
            script_name = match.group(1)
            module = match.group(2)
            attr = match.group(3)

            scripts.append(
                (group, script_name, f"{module}:{attr}")
            )

    # ------------------------------------------------------------
    # 2. Parse list/dict-style entry_points definitions
    # ------------------------------------------------------------

    # Example:
    #
    # entry_points={
    #     "console_scripts": [
    #         "foo = package.foo:main",
    #         "bar = package.bar:main",
    #     ]
    # }

    for group_match in re.finditer(
        r"""["'](console_scripts|gui_scripts)["']\s*:\s*\[(.*?)\]""",
        text,
        re.DOTALL,
    ):
        group = group_match.group(1)
        body = group_match.group(2)

        for item in re.finditer(
            r"""["']\s*([A-Za-z0-9_.-]+)\s*=\s*"""
            r"""([A-Za-z_][\w.]*)\s*:\s*([A-Za-z_][\w]*)\s*["']""",
            body,
        ):
            script_name = item.group(1)
            module = item.group(2)
            attr = item.group(3)

            candidate = (group, script_name, f"{module}:{attr}")

            if candidate not in scripts:
                scripts.append(candidate)

    # ------------------------------------------------------------
    # 3. Parse package_dir
    # ------------------------------------------------------------

    package_dir = {}

    pm = re.search(
        r"package_dir\s*=\s*\{(.*?)\}",
        text,
        re.DOTALL,
    )

    if pm:
        package_dir = dict(
            re.findall(
                r"""['"]([^'"]*)['"]\s*:\s*['"]([^'"]+)['"]""",
                pm.group(1),
            )
        )

    # ------------------------------------------------------------
    # 4. Parse find_packages(... where="...")
    # ------------------------------------------------------------

    wheres = re.findall(
        r"""find_(?:namespace_)?packages\s*\([^)]*?
        \bwhere\s*=\s*['"]([^'"]+)['"]""",
        text,
        re.DOTALL | re.VERBOSE,
    )

    return scripts, package_dir, wheres

class PythonBroker:
    SUPPORTS_FRAMEWORK_ANALYSIS = True      # app_broker passes framework= / arch_depth= only to brokers that say so
    SUPPORTS_COLLECTOR = True               # app_broker passes collector= (its ONE shared FileCollector) to such brokers

    def __init__(self, root, entry_file, internal_hints, entry_override=None, framework="auto",
                 arch_depth=1, arch_max_files=5000, collector=None, focus=None):
        self.collector = collector            # shared file_collector.FileCollector owned by App Broker (never created here)
        self.focus = list(focus or [])        # symbols of the entry file to analyse (e.g. the view a URL route resolved to)
        self._focus_extra = []                # further focused symbols, traced after the first
        self._discovered = None               # cached result of discovered_references()
        self.root = os.path.abspath(root)
        self.entry = posixpath.normpath(entry_file.replace("\\", "/"))   # the user-selected FILE
        self.entry_info = None    # resolved execution entry (see resolve_entry)
        self._entry_override = entry_override   # (group, name, target): analyse exactly this declared script
        self._index_ready = False               # True once the repository index exists (or was shared)
        self.package_map = []     # [(package prefix, directory)] from package_dir / find_packages(where=)
        self.import_bases = ["", os.path.dirname(self.entry)]   # top-level import search directories
        self.internal_hints = set(internal_hints)
        self.files = {}           # rel -> ast.Module
        self.sources = {}         # rel -> raw source text (original, never rewritten)
        self.parse_errors = []
        self.py_files = set()     # EVERY discovered .py file (parseable or not)
        self.legacy_files = set() # discovered .py files that ast cannot parse -> text-based analysis
        self.legacy_reasons = {}  # rel -> why ast.parse failed
        self.analysis_mode = {}   # rel -> "ast" | "text"  (text = lower confidence)
        self.text_info = {}       # rel -> scan_legacy_source() result (legacy files only)
        self.imports = {}         # rel -> {alias: dict(module,name,level,line)}
        self.symbols = OrderedDict()
        self.nodes = {}           # graph nodes: id -> dict
        self.edges = OrderedDict()  # (src,tgt,type) -> dict
        self.import_edges = OrderedDict()
        self.lines = []           # rendered execution tree (text)
        self.tree_root = {"text": "ROOT", "children": []}
        self._tree_stack = [(-1, self.tree_root)]
        self.trace = []           # expanded source trace lines
        self.trace_entries = []   # the same lines, structured: (depth, file, line, text)
        self._normalized = None
        self.trace_done = set()
        self.call_sites = {}      # (file, line) -> 'external' | 'stdlib'  (for trace-tree colouring)
        self.trace_tree_stats = None
        self.trace_tree_root = None      # parsed trace tree, reused by the functionality analysis
        self.functionality_stats = None
        self.topdown_result = None       # top-down functionality extraction (see extract_topdown_functionalities)
        self.expanded = set()
        self.class_expanded = set()
        self.reached = set()
        self.reached_files = set()
        self.external_calls = defaultdict(set)   # root module -> {labels}
        self.stdlib_calls = defaultdict(set)
        self.missing_calls = defaultdict(set)
        self.unresolved = OrderedDict()
        self.fallback_resolutions = {}
        self._attr_cache = {}
        self._attr_busy = set()
        self.module_bindings = {}   # rel -> {name: Binding}: module-level function-reference tables / aliases
        self._fn_bindings = {}      # function symbol id -> {name: Binding}
        self.referenced = set()     # function ids mentioned (not called) in a container, alias or argument
        self.dispatch_targets = set()   # function ids reached through an indirect (dispatch) call
        self._param_hints = {}      # callee symbol id -> {param: [Target]} taken from the arguments at its call sites
        # framework / configuration architecture (additive; see "Framework / configuration architecture traversal")
        self.framework_mode = framework           # "auto" | "none" | a name in FRAMEWORK_ANALYZERS
        self.arch_depth = arch_depth              # import hops followed from configuration-discovered files
        self.arch_max_files = arch_max_files
        self.framework_info = None                # result dict, or None when no framework analysis ran
        self.framework_error = None
        self.arch_symbols = set()                 # symbol ids named by configuration (ROUTES_TO); NOT in `reached`

    # ------------------------------------------------------------------
    # Broker contract (see module docstring)
    # ------------------------------------------------------------------
    @property
    def reachable_count(self):
        return len(self.reached)

    def summary_lines(self):
        lines = [f"  reachable symbols: {len(self.reached)}  edges: {len(self.edges)}"]
        n_disp = sum(1 for e in self.edges.values() if e["type"] == "DISPATCHES_TO")
        if n_disp or self.referenced:
            lines.append(f"  dispatch edges: {n_disp}  referenced functions: {len(self.referenced)}")
        if self.legacy_files:
            lines.append(f"  text-based (legacy) files: {len(self.legacy_files)} of {len(self.py_files)} .py files")
        fi = self.framework_info
        if fi and fi.get("active"):
            st = fi["statistics"]
            lines.append(f"  {fi['framework']} architecture: executed files {st['execution_reached_files']}, "
                         f"import-reached {st['import_reached_files']}, configuration {st['configuration_files']} "
                         f"(not executed: {st['configuration_only_files']}), architecture imports "
                         f"{st['architecture_import_files']}, unresolved {st['unresolved']}")
        return lines

    # ------------------------------------------------------------------
    # Stage 1 + 2: indexing
    # ------------------------------------------------------------------
    def index_repository(self):
        for dirpath, dirnames, filenames in os.walk(self.root):
            dirnames[:] = [d for d in dirnames if d not in EXCLUDE_DIRS]
            for fn in filenames:
                if not fn.endswith(".py"):
                    continue
                if any(fnmatch.fnmatch(fn, p) for p in EXCLUDE_FILES):
                    continue
                full = os.path.join(dirpath, fn)
                rel = os.path.relpath(full, self.root).replace(os.sep, "/")
                # 1. discovery: read the source.  Reading is independent of parsing.
                try:
                    src = self._read_source(full)
                except OSError as e:
                    self.parse_errors.append((rel, str(e)))      # unreadable: the only way a file is lost
                    continue
                self.sources[rel] = src
                self.py_files.add(rel)
                # 2. parsing: success -> normal AST pipeline; failure -> keep the file, text analysis
                try:
                    self.files[rel] = ast.parse(src, filename=rel)
                    self.analysis_mode[rel] = ANALYSIS_AST
                except (SyntaxError, ValueError, RecursionError) as e:
                    self.parse_errors.append((rel, str(e)))
                    self.legacy_reasons[rel] = str(e)
                    self.legacy_files.add(rel)
                    self.analysis_mode[rel] = ANALYSIS_TEXT
        for rel, tree in self.files.items():
            self._index_symbols(rel, tree)
            self._index_imports(rel, tree)
        for rel in sorted(self.legacy_files):
            self._index_legacy(rel)
        self._index_bindings()               # after ALL definitions are known: forward references resolve
        self._index_ready = True

    @staticmethod
    def _read_source(full):
        """Original source text.  UTF-8 first; legacy sources are often latin-1, which decodes any byte
        sequence one-to-one, so line numbers and the displayed code stay faithful.  The file on disk is
        only ever read."""
        with open(full, "rb") as f:
            data = f.read()
        try:
            return data.decode("utf-8-sig")
        except UnicodeDecodeError:
            return data.decode("latin-1")

    def _index_legacy(self, rel):
        """Text-based counterpart of _index_symbols + _index_imports for a file ast cannot parse.
        Imports go into the same `self.imports` table shape the AST path produces, so module
        resolution and import edges work unchanged.  Functions/classes stay in `self.text_info`
        (not in `self.symbols`: there is no AST node behind them)."""
        info = scan_legacy_source(self.sources[rel])
        self.text_info[rel] = info
        table = {}
        for imp in info["imports"]:
            if imp["name"] is None:                               # import a.b [as c]
                if imp["alias"]:
                    table[imp["alias"]] = dict(module=imp["module"], name=None, level=0, line=imp["line"])
                else:
                    top = imp["module"].split(".")[0]
                    table[top] = dict(module=top, name=None, level=0, line=imp["line"])
            else:                                                 # from x import y [as z]
                table[imp["alias"] or imp["name"]] = dict(module=imp["module"], name=imp["name"],
                                                          level=imp["level"], line=imp["line"])
        self.imports[rel] = table

    def _index_symbols(self, rel, tree):
        for node in tree.body:
            if isinstance(node, ast.ClassDef):
                cid = f"{rel}:{node.name}"
                self.symbols[cid] = Symbol(cid, "class", node.name, rel, node)
                for item in node.body:
                    if isinstance(item, (ast.FunctionDef, ast.AsyncFunctionDef)):
                        mid = f"{cid}.{item.name}"
                        self.symbols[mid] = Symbol(mid, "method", item.name, rel, item, parent=cid)
                        self._edge(cid, mid, "CONTAINS", item.lineno)
            elif isinstance(node, (ast.FunctionDef, ast.AsyncFunctionDef)):
                fid = f"{rel}:{node.name}"
                self.symbols[fid] = Symbol(fid, "function", node.name, rel, node)

    def _index_imports(self, rel, tree):
        table = {}
        for node in ast.walk(tree):
            if isinstance(node, ast.Import):
                for a in node.names:
                    if a.asname:
                        table[a.asname] = dict(module=a.name, name=None, level=0, line=node.lineno)
                    else:
                        top = a.name.split(".")[0]
                        table[top] = dict(module=top, name=None, level=0, line=node.lineno)
            elif isinstance(node, ast.ImportFrom):
                for a in node.names:
                    table[a.asname or a.name] = dict(module=node.module or "", name=a.name,
                                                     level=node.level, line=node.lineno)
        self.imports[rel] = table

    # ------------------------------------------------------------------
    # Module / name resolution
    # ------------------------------------------------------------------
    def find_module_file(self, module, level, from_rel, strict=False):
        """strict=True disables the flat-layout basename fallback: configuration analysis must never
        resolve a dotted name to a file that merely has the same basename."""
        parts = module.split(".") if module else []
        if level:
            base = os.path.dirname(from_rel)
            for _ in range(level - 1):
                base = os.path.dirname(base)
            bases = [base]
        else:
            mapped = self._mapped_module_file(parts)
            if mapped:
                return mapped
            bases = self.import_bases
        for base in bases:
            stem = os.path.join(base, *parts) if parts else base
            cands = [stem + ".py", os.path.join(stem, "__init__.py")] if parts else [os.path.join(stem, "__init__.py")]
            for c in cands:
                c = c.replace(os.sep, "/").lstrip("/")
                if c in self.py_files:
                    return c
        # Fallback for flat layouts: unique file whose basename matches the last part
        if parts and not strict:
            matches = [f for f in self.py_files if os.path.basename(f) == parts[-1] + ".py"]
            if len(matches) == 1:
                self.fallback_resolutions[(module, from_rel)] = matches[0]
                return matches[0]
        return None

    def _strict_module_file(self, module, level, from_rel):
        """Exact module resolution for configuration analysis (no basename fallback).  Besides the regular import
        bases, the sys.path root implied by the Django-style layout is tried: the directory above the top-most
        package that contains the file (the entry file's directory is already in import_bases)."""
        saved = self.import_bases
        d = posixpath.dirname(from_rel)
        while d and f"{d}/__init__.py" in self.py_files:
            d = posixpath.dirname(d)
        self.import_bases = list(saved) + ([d] if d not in saved else [])
        try:
            return self.find_module_file(module, level, from_rel, strict=True)
        finally:
            self.import_bases = saved

    def _submodule_file(self, rel, name):
        """`name` as a submodule of the package whose __init__.py is `rel` (file-system based, base independent)."""
        if posixpath.basename(rel) != "__init__.py":
            return None
        d = posixpath.dirname(rel)
        for cand in (f"{d}/{name}.py" if d else f"{name}.py", f"{d}/{name}/__init__.py" if d else f"{name}/__init__.py"):
            if cand in self.py_files:
                return cand
        return None

    def classify_module(self, module, level, from_rel):
        f = self.find_module_file(module, level, from_rel)
        if f:
            return "internal", f
        top = module.split(".")[0] if module else ""
        if level or top in self.internal_hints:
            return "missing", module or "."
        if top in STDLIB:
            return "stdlib", top
        return "external", top

    def resolve_name(self, name, file_rel, depth=0, prefer_import=False):
        sid = f"{file_rel}:{name}"
        if not prefer_import and sid in self.symbols and self.symbols[sid].parent is None:
            return Target("symbol", sid, name)
        imp = self.imports.get(file_rel, {}).get(name)
        if imp:
            kind, ref = self.classify_module(imp["module"], imp["level"], file_rel)
            if imp["name"] is None:                       # import x [as y]
                if kind == "internal":
                    return Target("module", ref, name)
                return Target(kind, None, imp["module"])
            full = f"{imp['module']}.{imp['name']}" if imp["module"] else imp["name"]
            if kind == "internal":                        # from x import y
                tf = ref
                tsid = f"{tf}:{imp['name']}"
                if tsid in self.symbols:
                    return Target("symbol", tsid, imp["name"])
                sub = self.find_module_file(full, imp["level"], file_rel)
                if sub:
                    return Target("module", sub, imp["name"])
                if depth < 5 and imp["name"] in self.imports.get(tf, {}):
                    return self.resolve_name(imp["name"], tf, depth + 1)
                return Target("unknown", None, full)
            return Target(kind, None, full if kind != "missing" else full)
        if hasattr(builtins, name):
            return Target("builtin", None, name)
        return Target("unknown", None, name)

    def resolve_expr(self, node, scope):
        if isinstance(node, ast.Name):
            if node.id in ("self", "cls") and scope.cls:
                return Target("symbol", scope.cls, scope.cls.split(":")[1])
            if node.id in scope.vars:
                return scope.vars[node.id]
            if node.id in scope.local_funcs:
                return Target("symbol", scope.local_funcs[node.id], node.id)
            b = self._lookup_name_binding(node.id, scope)
            if (b is not None and b.kind == "alias" and len(b.entries) == 1 and not b.partial
                    and not b.lookup):
                return Target("symbol", b.entries[0][1], node.id)       # handler = add_task; handler()
            t = self.resolve_name(node.id, scope.file)
            return None if t.kind == "unknown" else t
        if isinstance(node, ast.Attribute):
            base = self.resolve_expr(node.value, scope)
            return self._resolve_attr(base, node.attr) if base else None
        if isinstance(node, ast.Call):
            t = self.resolve_expr(node.func, scope)
            if t is None:
                return None
            if t.kind == "symbol" and self.symbols[t.ref].kind == "class":
                return t                                   # instance of class
            if t.kind in ("external", "stdlib", "missing"):
                return t                                   # assume returns object of that lib
            return None
        return None

    def _resolve_attr(self, base, attr):
        if base.kind == "module":
            sid = f"{base.ref}:{attr}"
            if sid in self.symbols:
                return Target("symbol", sid, attr)
            t = self.resolve_name(attr, base.ref)
            return None if t.kind == "unknown" else t
        if base.kind == "symbol":
            sym = self.symbols[base.ref]
            if sym.kind != "class":
                return None
            m = self.find_method(base.ref, attr)
            if m:
                return Target("symbol", m, attr)
            return self.class_attrs(base.ref).get(attr)
        if base.kind in ("external", "stdlib", "missing"):
            return Target(base.kind, None, f"{base.label}.{attr}")
        return None

    def _bind_local_imports(self, scope, sym):
        """A function-local `import x` shadows a same-named module-level symbol of the file (Python
        scoping), e.g. `def main(): import main; main.main(argv)`.  Only that collision is handled;
        every other name keeps the normal resolution."""
        stack = list(sym.node.body)
        while stack:
            n = stack.pop()
            if isinstance(n, (ast.Import, ast.ImportFrom)):
                for a in n.names:
                    name = a.asname or (a.name.split(".")[0] if isinstance(n, ast.Import) else a.name)
                    if f"{scope.file}:{name}" in self.symbols and name not in scope.vars:
                        t = self.resolve_name(name, scope.file, prefer_import=True)
                        if t.kind != "unknown":
                            scope.vars[name] = t
            elif not isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda)):
                stack.extend(ast.iter_child_nodes(n))

    # ------------------------------------------------------------------
    # Input-independent resolution: when a value depends on runtime input (``LANGUAGE_BROKERS.get(language)``,
    # ``getattr(table[key], "name")``, a parameter ...) EVERY statically possible target is followed.  Nothing is
    # executed and nothing is invented: candidates come only from tables / aliases / call sites in the code.
    # ------------------------------------------------------------------
    def resolve_candidates(self, node, scope, depth=0):
        """All statically possible Targets of an expression (a superset of ``resolve_expr``; [] when unknown)."""
        if depth > 6:
            return []
        t = self.resolve_expr(node, scope)
        if t is not None:
            return [t]
        out = []

        def add(x):
            if x is not None and not any((x.kind, x.ref, x.label) == (y.kind, y.ref, y.label) for y in out):
                out.append(x)
        sym_target = lambda sid: Target("symbol", sid, self.symbols[sid].name)
        if isinstance(node, ast.Name):
            for x in scope.multi.get(node.id, ()):
                add(x)
            b = self._lookup_name_binding(node.id, scope)
            if not out and b is not None and b.kind == "alias":
                for _, sid, _ in b.entries:
                    add(sym_target(sid))
        elif isinstance(node, ast.Attribute):
            for base in self.resolve_candidates(node.value, scope, depth + 1):
                add(self._resolve_attr(base, node.attr))
        elif isinstance(node, (ast.Subscript, ast.Call)):
            look = self._lookup_target(node, scope)             # table[key] / table.get(key): every entry
            if look is not None:
                src, key_node = look
                for _, sid, _ in self._select(src, key_node):
                    add(sym_target(sid))
            elif isinstance(node, ast.Call):
                f = node.func
                if (isinstance(f, ast.Name) and f.id == "getattr" and len(node.args) >= 2
                        and _const_str(node.args[1])):          # getattr(x, "name"[, default]) -> x.name
                    for base in self.resolve_candidates(node.args[0], scope, depth + 1):
                        add(self._resolve_attr(base, _const_str(node.args[1])))
                else:                                           # Class(...) -> instance; library call -> library object
                    for fc in self.resolve_candidates(f, scope, depth + 1):
                        if ((fc.kind == "symbol" and self.symbols[fc.ref].kind == "class")
                                or fc.kind in ("external", "stdlib", "missing")):
                            add(fc)
        return out

    def _bind_candidates(self, targets, value, scope):
        """x = <expr with several possible values>: remember them all for the later calls on x."""
        cands = self.resolve_candidates(value, scope)
        if not cands:
            return
        for tg in targets:
            if isinstance(tg, ast.Name):
                if len(cands) == 1:
                    scope.vars[tg.id] = cands[0]
                    scope.multi.pop(tg.id, None)
                else:
                    scope.multi[tg.id] = cands
                    scope.vars.pop(tg.id, None)

    def _note_param_types(self, sym, call, scope):
        """Argument values of one call site become the candidate values of the callee's parameters."""
        if not isinstance(sym.node, _DEF_NODES):
            return
        a = sym.node.args
        params = [p.arg for p in list(a.posonlyargs) + list(a.args)]
        static = any(isinstance(d, ast.Name) and d.id == "staticmethod" for d in sym.node.decorator_list)
        if sym.kind == "method" and not static:
            params = params[1:]                                 # self / cls
        known = set(params) | {p.arg for p in a.kwonlyargs}
        named = {}
        for p, arg in zip(params, call.args):
            if isinstance(arg, ast.Starred):
                break
            named[p] = arg
        for kw in call.keywords:
            if kw.arg in known:
                named[kw.arg] = kw.value
        hints = self._param_hints.setdefault(sym.id, {})
        for p, arg in named.items():
            for t in self.resolve_candidates(arg, scope):
                if t.kind == "symbol":
                    lst = hints.setdefault(p, [])
                    if not any((t.ref, t.label) == (x.ref, x.label) for x in lst):
                        lst.append(t)

    def _apply_param_hints(self, scope, sym):
        for name, ts in self._param_hints.get(sym.id, {}).items():
            if len(ts) == 1:
                scope.vars[name] = ts[0]
            else:
                scope.multi[name] = list(ts)

    def class_bases(self, cls_id):
        sym = self.symbols[cls_id]
        sc = Scope(sym.file, None, cls_id)
        return [(b, self.resolve_expr(b, sc)) for b in sym.node.bases]

    def find_method(self, cls_id, name, seen=None):
        seen = seen or set()
        if cls_id in seen:
            return None
        seen.add(cls_id)
        mid = f"{cls_id}.{name}"
        if mid in self.symbols:
            return mid
        for _, t in self.class_bases(cls_id):
            if t and t.kind == "symbol" and self.symbols[t.ref].kind == "class":
                m = self.find_method(t.ref, name, seen)
                if m:
                    return m
        return None

    def class_attrs(self, cls_id):
        """self.x = SomeClass(...) inside any method -> attribute type."""
        if cls_id in self._attr_cache:
            return self._attr_cache[cls_id]
        if cls_id in self._attr_busy:
            return {}
        self._attr_busy.add(cls_id)
        attrs = {}
        sym = self.symbols[cls_id]
        sc = Scope(sym.file, cls_id, cls_id)
        for n in ast.walk(sym.node):
            if isinstance(n, ast.Assign) and isinstance(n.value, ast.Call):
                for tg in n.targets:
                    if (isinstance(tg, ast.Attribute) and isinstance(tg.value, ast.Name)
                            and tg.value.id == "self"):
                        t = self.resolve_expr(n.value, sc)
                        if t:
                            attrs[tg.attr] = t
        self._attr_busy.discard(cls_id)
        self._attr_cache[cls_id] = attrs
        return attrs

    # ------------------------------------------------------------------
    # Function references, aliases and indirect (dispatch) calls
    #
    # Pure AST, no execution.  Definitions are indexed first (_index_symbols), bindings second
    # (_index_bindings), so a function defined AFTER the dict that mentions it resolves normally.
    #   * _make_binding / _scan_body   which names hold function references (dict / list / tuple / set
    #                                  literals, aliases, container[key] / .get(key) / for-loop variables)
    #   * _scan_effects                container mutation (x[k] = f, update, append, ...) and escape
    #                                  (container passed to project code) -> entries added or the table
    #                                  marked partial; nothing is ever invented
    #   * resolve_dispatch             indirect call -> possible targets with their dispatch keys
    # A reference is NOT an invocation: REFERENCES edges are separate from CALLS / DISPATCHES_TO edges.
    # ------------------------------------------------------------------
    def _index_bindings(self):
        self.module_bindings = {rel: {} for rel in self.files}
        self._fn_bindings = {}
        for rel, tree in self.files.items():
            mb = self.module_bindings[rel]
            owner = f"file:{rel}"
            for node in tree.body:                         # names already taken by defs / classes / imports
                if isinstance(node, _DEF_NODES + (ast.ClassDef,)):
                    mb[node.name] = Binding(node.name, "dynamic", owner, rel, node.lineno)
            for alias in self.imports.get(rel, {}):
                mb.setdefault(alias, Binding(alias, "dynamic", owner, rel, 0))
            scope = Scope(rel, None, owner)
            scope.bindings = mb
            self._scan_body(tree.body, scope, mb, owner, skip=())
        for rel, tree in self.files.items():               # module containers mutated from function bodies
            self._effects_in_defs(rel, tree.body, None, frozenset())

    def _function_bindings(self, sym):
        cached = self._fn_bindings.get(sym.id)
        if cached is not None:
            return cached
        bindings = {}
        self._fn_bindings[sym.id] = bindings
        scope = Scope(sym.file, sym.parent if sym.kind == "method" else None, sym.id)
        for stmt in sym.node.body:                         # nested defs, same ids trace_symbol registers
            if isinstance(stmt, _DEF_NODES):
                nid = f"{sym.id}.<local>{stmt.name}"
                if nid not in self.symbols:
                    self.symbols[nid] = Symbol(nid, "function", stmt.name, sym.file, stmt)
                scope.local_funcs[stmt.name] = nid
        scope.bindings = bindings
        a = sym.node.args
        params = list(a.posonlyargs) + list(a.args) + list(a.kwonlyargs) + [x for x in (a.vararg, a.kwarg) if x]
        for arg in params:                                 # parameters shadow module-level bindings
            bindings[arg.arg] = Binding(arg.arg, "dynamic", sym.id, sym.file, sym.line)
        skip = {n for st in _walk_no_defs(sym.node.body) if isinstance(st, (ast.Global, ast.Nonlocal))
                for n in st.names}
        self._scan_body(sym.node.body, scope, bindings, sym.id, skip)
        return bindings

    def _lookup_name_binding(self, name, scope):
        b = scope.bindings.get(name) if scope.bindings else None
        if b is not None:
            return b
        if name in scope.vars or name in scope.local_funcs:
            return None
        mb = self.module_bindings.get(scope.file, {})
        imp = self.imports.get(scope.file, {}).get(name)
        # a single-assignment placeholder for an imported name does not hide the imported table
        if name in mb and not (imp and imp["name"] and mb[name].kind == "dynamic" and mb[name].assigns == 1):
            return mb[name]
        if imp and imp["name"]:                            # from other_module import table
            kind, ref = self.classify_module(imp["module"], imp["level"], scope.file)
            if kind == "internal":
                return self.module_bindings.get(ref, {}).get(imp["name"])
        return None

    def _binding_of_expr(self, expr, scope):
        if isinstance(expr, ast.Name):
            return self._lookup_name_binding(expr.id, scope)
        if isinstance(expr, ast.Attribute):                # module.table
            base = self.resolve_expr(expr.value, scope)
            if base is not None and base.kind == "module":
                return self.module_bindings.get(base.ref, {}).get(expr.attr)
        return None

    # --- binding construction ---------------------------------------------------------------
    def _element_refs(self, expr, scope):
        """One container element / assigned value -> (function symbol ids, reason it is opaque or None)."""
        if isinstance(expr, ast.IfExp):
            a, b = self._element_refs(expr.body, scope), self._element_refs(expr.orelse, scope)
            return a[0] + b[0], a[1] or b[1]
        if isinstance(expr, (ast.Name, ast.Attribute)):
            t = self.resolve_expr(expr, scope)
            if t is not None and t.kind == "symbol" and self.symbols[t.ref].kind in ("function", "method", "class"):
                return [t.ref], None                       # classes too: LANGUAGE_BROKERS = {"Python": PythonBroker}
            if t is not None:                              # class / module / builtin / library: not a project function
                return [], None
            return [], f"unresolved reference {ast.unparse(expr)}"
        if isinstance(expr, ast.Lambda):
            return [], "lambda expression"
        if isinstance(expr, ast.Call):
            fn = expr.func
            name = fn.id if isinstance(fn, ast.Name) else fn.attr if isinstance(fn, ast.Attribute) else None
            if name == "partial" and expr.args:            # functools.partial(f, ...) still refers to f
                return self._element_refs(expr.args[0], scope)
            return [], f"call result {ast.unparse(expr)}"
        if isinstance(expr, _ORDINARY_NODES):
            return [], None
        return [], f"expression {ast.unparse(expr)}"

    def _fill_table(self, b, pairs, scope, line):
        for key, value in pairs:
            sids, why = self._element_refs(value, scope)
            for sid in sids:
                b.add(key, sid, getattr(value, "lineno", line))
            if why:
                b.mark_partial(f"{why} (line {getattr(value, 'lineno', line)})")

    def _make_binding(self, name, value, scope, owner, line):
        mk = lambda kind: Binding(name, kind, owner, scope.file, line)
        if isinstance(value, ast.Dict):
            b = mk("table")
            b.container = "dict"
            pairs = []
            for k, v in zip(value.keys, value.values):
                if k is None:                              # {**other}
                    b.mark_partial(f"dict unpacking (line {value.lineno})")
                    continue
                pairs.append((_key_of(k), v))
            self._fill_table(b, pairs, scope, line)
            return b
        if isinstance(value, (ast.List, ast.Tuple, ast.Set)):
            b = mk("table")
            b.container = "set" if isinstance(value, ast.Set) else "list"
            self._fill_table(b, [(None if b.container == "set" else ("const", i), v)
                                 for i, v in enumerate(value.elts)], scope, line)
            return b
        if (isinstance(value, ast.Call) and isinstance(value.func, ast.Name) and value.func.id == "dict"
                and not value.args and value.keywords and all(k.arg for k in value.keywords)):
            b = mk("table")
            b.container = "dict"
            self._fill_table(b, [(("const", k.arg), k.value) for k in value.keywords], scope, line)
            return b
        if isinstance(value, ast.Name):                    # x = other_table / x = other_alias
            src = self._lookup_name_binding(value.id, scope)
            if src is not None and src.kind in ("table", "alias"):
                b = mk(src.kind)
                b.entries, b.partial, b.reasons = list(src.entries), src.partial, list(src.reasons)
                b.container, b.lookup, b.via, b.origin = src.container, src.lookup, src.via, src.origin
                if src.kind == "table":
                    b.via = src.name
                return b
        look = self._lookup_target(value, scope)           # x = table[key] / x = table.get(key)
        if look is not None:
            src, key_node = look
            b = mk("alias")
            b.lookup, b.via, b.origin = True, src.name, src
            b.partial, b.reasons = src.partial, list(src.reasons)
            b.entries = self._select(src, key_node)
            return b
        if isinstance(value, (ast.Name, ast.Attribute, ast.IfExp)):
            sids, why = self._element_refs(value, scope)
            if sids and not why:                           # x = some_function
                b = mk("alias")
                for sid in sids:
                    b.add(None, sid, getattr(value, "lineno", line))
                return b
        return mk("dynamic")

    def _lookup_target(self, value, scope):
        """`table[key]` / `table.get(key)` / `table.pop(key)` -> (table Binding, key node or None)."""
        if isinstance(value, ast.Subscript):
            src = self._binding_of_expr(value.value, scope)
            if src is not None and src.kind == "table":
                return src, value.slice
        elif (isinstance(value, ast.Call) and isinstance(value.func, ast.Attribute)
              and value.func.attr in ("get", "pop") and value.args):
            src = self._binding_of_expr(value.func.value, scope)
            if src is not None and src.kind == "table":
                return src, value.args[0]
        return None

    def _select(self, table, key_node):
        """Entries of `table` that `table[key_node]` can yield (all of them when the key is not a literal)."""
        if key_node is not None:
            key = _key_of(key_node)
            if key[0] == "const":
                hit = [e for e in table.entries if e[0] == key]
                return hit[-1:] if hit else []             # a later duplicate key wins at runtime
        return list(table.entries)

    def _merge(self, bindings, name, new):
        old = bindings.get(name)
        if old is None:
            bindings[name] = new
            return
        old.assigns += 1
        old.mark_partial(f"'{name}' is assigned more than once (line {new.line})")
        if old.kind == "dynamic" and new.kind != "dynamic":
            old.kind, old.container, old.lookup, old.via, old.origin = (new.kind, new.container, new.lookup,
                                                                       new.via, new.origin)
        for k, sid, line in new.entries:
            old.add(k, sid, line)
        for r in new.reasons:
            old.mark_partial(r)
        if new.partial:
            old.partial = True

    def _bind_target(self, target, value, scope, bindings, owner, skip):
        if isinstance(target, ast.Name):
            if target.id not in skip:
                self._merge(bindings, target.id, self._make_binding(target.id, value, scope, owner, target.lineno))
        elif isinstance(target, (ast.Tuple, ast.List)):    # unpacking: names become unknown values
            for el in target.elts:
                if isinstance(el, ast.Starred):
                    el = el.value
                if isinstance(el, ast.Name) and el.id not in skip:
                    self._merge(bindings, el.id, Binding(el.id, "dynamic", owner, scope.file, el.lineno))

    def _bind_loop(self, st, scope, bindings, owner, skip):
        """for h in handlers / for h in table.values() / for k, h in table.items()."""
        it, tg = st.iter, st.target
        src, items = None, False
        if isinstance(it, ast.Call) and isinstance(it.func, ast.Attribute) and not it.args:
            if it.func.attr in ("values", "items"):
                src, items = self._binding_of_expr(it.func.value, scope), it.func.attr == "items"
        elif isinstance(it, (ast.Name, ast.Attribute)):
            cand = self._binding_of_expr(it, scope)
            if cand is not None and cand.container in ("list", "set"):   # iterating a dict yields keys
                src = cand
        name_node = None
        if src is not None and src.kind == "table":
            if items and isinstance(tg, ast.Tuple) and len(tg.elts) == 2 and isinstance(tg.elts[1], ast.Name):
                name_node = tg.elts[1]
            elif not items and isinstance(tg, ast.Name):
                name_node = tg
        if name_node is not None and name_node.id not in skip:
            b = Binding(name_node.id, "alias", owner, scope.file, name_node.lineno)
            b.lookup, b.via, b.origin = True, src.name, src
            b.entries, b.partial, b.reasons = list(src.entries), src.partial, list(src.reasons)
            self._merge(bindings, name_node.id, b)
            return
        self._bind_target(tg, None, scope, bindings, owner, skip)

    def _scan_body(self, body, scope, bindings, owner, skip):
        for st in _iter_stmts(body):
            if isinstance(st, ast.Assign):
                for tg in st.targets:
                    self._bind_target(tg, st.value, scope, bindings, owner, skip)
            elif isinstance(st, ast.AnnAssign) and st.value is not None:
                self._bind_target(st.target, st.value, scope, bindings, owner, skip)
            elif isinstance(st, (ast.For, ast.AsyncFor)):
                self._bind_loop(st, scope, bindings, owner, skip)
            elif isinstance(st, (ast.With, ast.AsyncWith)):
                for item in st.items:
                    if item.optional_vars is not None:
                        self._bind_target(item.optional_vars, None, scope, bindings, owner, skip)
        self._scan_effects(body, scope, bindings.get)

    # --- mutation / escape ---------------------------------------------------------------------
    def _scan_effects(self, body, scope, lookup, globals_=frozenset(), where=None):
        """Apply container mutation to the table `lookup(name)` returns.  Unknown values or escapes make the
        table partial instead of guessing."""
        nodes = sorted((n for n in _walk_no_defs(body) if isinstance(n, (ast.Assign, ast.AugAssign, ast.Call))),
                       key=lambda n: (n.lineno, n.col_offset))
        table = lambda n: (lookup(n) if lookup(n) is not None and lookup(n).kind == "table" else None)
        for n in nodes:
            if isinstance(n, ast.Assign):
                for tg in n.targets:
                    if isinstance(tg, ast.Subscript) and isinstance(tg.value, ast.Name) and table(tg.value.id):
                        self._fill_table(table(tg.value.id), [(_key_of(tg.slice), n.value)], scope, n.lineno)
                    elif isinstance(tg, ast.Name) and tg.id in globals_:     # `global x; x = ...` inside a function
                        self._merge_global(tg.id, n.value, scope, n.lineno, where)
            elif isinstance(n, ast.AugAssign):
                tb = (table(n.target.value.id) if isinstance(n.target, ast.Subscript)
                      and isinstance(n.target.value, ast.Name) else
                      table(n.target.id) if isinstance(n.target, ast.Name) else None)
                if tb is None:
                    continue
                if isinstance(n.target, ast.Name) and isinstance(n.value, (ast.List, ast.Tuple, ast.Dict)):
                    self._extend_table(tb, n.value, scope, n.lineno)
                else:
                    tb.mark_partial(f"augmented assignment (line {n.lineno})")
            else:
                self._scan_call_effects(n, scope, table)

    def _extend_table(self, tb, lit, scope, line):
        if isinstance(lit, ast.Dict):
            for k, v in zip(lit.keys, lit.values):
                if k is None:
                    tb.mark_partial(f"dict unpacking (line {line})")
                else:
                    self._fill_table(tb, [(_key_of(k), v)], scope, line)
        else:
            for v in lit.elts:
                self._fill_table(tb, [(("expr", "<extended>"), v)], scope, line)

    def _scan_call_effects(self, call, scope, table):
        fn = call.func
        if isinstance(fn, ast.Attribute) and isinstance(fn.value, ast.Name) and table(fn.value.id):
            tb, m, line = table(fn.value.id), fn.attr, call.lineno
            if m == "update":
                if call.args and isinstance(call.args[0], ast.Dict) and len(call.args) == 1:
                    self._extend_table(tb, call.args[0], scope, line)
                elif call.args:
                    tb.mark_partial(f"update() with a non-literal argument (line {line})")
                for kw in call.keywords:
                    if kw.arg:
                        self._fill_table(tb, [(("const", kw.arg), kw.value)], scope, line)
                    else:
                        tb.mark_partial(f"update(**...) (line {line})")
            elif m == "setdefault" and len(call.args) == 2:
                self._fill_table(tb, [(_key_of(call.args[0]), call.args[1])], scope, line)
            elif m in ("append", "add") and len(call.args) == 1:
                self._fill_table(tb, [(("expr", "<appended>"), call.args[0])], scope, line)
            elif m == "insert" and len(call.args) == 2:
                self._fill_table(tb, [(("expr", "<inserted>"), call.args[1])], scope, line)
            elif m == "extend" and call.args and isinstance(call.args[0], (ast.List, ast.Tuple)):
                self._extend_table(tb, call.args[0], scope, line)
            elif m in ("extend", "__setitem__", "__ior__", "__iadd__"):
                tb.mark_partial(f"{m}() with a non-literal argument (line {line})")
            return                                         # get / keys / values / items / pop ... only read
        if isinstance(fn, ast.Name) and fn.id in _SAFE_CALLEES:
            return
        args = list(call.args) + [k.value for k in call.keywords]
        escaping = [a.value if isinstance(a, ast.Starred) else a for a in args]
        escaping = [a for a in escaping if isinstance(a, ast.Name) and table(a.id)]
        if not escaping:
            return
        callee = self.resolve_expr(fn, scope)
        if callee is not None and callee.kind != "symbol":
            return                                         # library / builtin callee: assumed not to mutate
        for a in escaping:
            table(a.id).mark_partial(f"passed to {ast.unparse(fn)}() which may mutate it (line {call.lineno})")

    def _merge_global(self, name, value, scope, line, where):
        mb = self.module_bindings.get(scope.file)
        if mb is None:
            return
        new = self._make_binding(name, value, scope, f"file:{scope.file}", line)
        new.mark_partial(f"reassigned in {where or 'a function'}() through `global` (line {line})")
        self._merge(mb, name, new)

    def _effects_in_defs(self, rel, body, cls_id, outer_shadow):
        """Mutation of MODULE-level containers from inside function bodies (nested defs inherit the
        enclosing shadow set, so a closure over a same-named local is not mistaken for the module table)."""
        mb = self.module_bindings[rel]
        stack = list(body)
        while stack:
            node = stack.pop(0)
            if isinstance(node, ast.ClassDef):
                self._effects_in_defs(rel, node.body, f"{rel}:{node.name}", outer_shadow)
                continue
            if isinstance(node, _DEF_NODES):
                a = node.args
                params = list(a.posonlyargs) + list(a.args) + list(a.kwonlyargs) + [x for x in (a.vararg, a.kwarg) if x]
                globals_ = {n for st in _walk_no_defs(node.body) if isinstance(st, ast.Global) for n in st.names}
                local = ({p.arg for p in params}
                         | {n.id for n in _walk_no_defs(node.body)
                            if isinstance(n, ast.Name) and isinstance(n.ctx, ast.Store)}
                         | {d.name for d in node.body if isinstance(d, _DEF_NODES + (ast.ClassDef,))}) - globals_
                shadow = outer_shadow | local
                scope = Scope(rel, cls_id, f"{rel}:{node.name}")
                self._scan_effects(node.body, scope, lambda n, s=shadow: None if n in s else mb.get(n),
                                   globals_, node.name)
                self._effects_in_defs(rel, node.body, None, shadow)
                continue
            for fld in ("body", "orelse", "finalbody"):
                sub_ = getattr(node, fld, None)
                if isinstance(sub_, list):
                    stack.extend(sub_)
            for h in getattr(node, "handlers", []):
                stack.extend(h.body)
            for c in getattr(node, "cases", []):
                stack.extend(c.body)

    # --- indirect calls ----------------------------------------------------------------------------
    def resolve_dispatch(self, call, scope):
        """Is `call` an indirect call through a known container / alias?  None when it is not (the normal
        resolution applies).  Otherwise a dict: binding, via, entries [(key, sid, line)], status
        (resolved | possible | partial | unresolved) and reasons."""
        f = call.func
        key_node = None
        if isinstance(f, ast.Subscript):                   # table[key]()
            b = self._binding_of_expr(f.value, scope)
            if b is None or b.kind != "table":
                return None
            key_node = f.slice
        elif (isinstance(f, ast.Call) and isinstance(f.func, ast.Attribute) and f.func.attr in ("get", "pop")
              and f.args):                                 # table.get(key)()
            b = self._binding_of_expr(f.func.value, scope)
            if b is None or b.kind != "table":
                return None
            key_node = f.args[0]
        elif isinstance(f, ast.Name):                      # handler()   with handler = table.get(k) / loop variable
            b = self._lookup_name_binding(f.id, scope)
            if b is None or b.kind != "alias" or (len(b.entries) == 1 and not b.partial and not b.lookup):
                return None                                # single, certain alias -> ordinary CALLS (resolve_expr)
        else:
            return None
        reasons = list(b.reasons)
        entries = self._select(b, key_node) if b.kind == "table" else list(b.entries)
        if b.kind == "table" and key_node is not None and not entries:
            k = _key_of(key_node)
            if k[0] == "const":
                reasons.append(f"key {k[1]!r} is not in the container")
        if not entries:
            if not b.entries:
                reasons.append("the container holds no statically known function")
            status = "unresolved"
        elif b.partial:
            status = "partial"
        elif b.kind == "table" and key_node is not None and _key_of(key_node)[0] == "const":
            status = "resolved"
        elif b.kind == "alias" and not b.lookup:
            status = "resolved"
        else:
            status = "possible"
        return dict(binding=b, via=b.via or b.name, entries=entries, status=status, reasons=reasons)

    def handle_dispatch(self, node, d, scope, depth):
        """Graph + execution-tree side of an indirect call: DISPATCHES_TO edges (one per distinct target;
        dispatch keys accumulate as `conditions`), then the targets are traced like any callee."""
        loc = f"{scope.file}:{node.lineno}"
        label = ast.unparse(node.func)
        self._emit_binding_refs(d["binding"].origin or d["binding"])
        if not d["entries"]:
            self._unresolved(scope, node, "indirect call: " + "; ".join(d["reasons"]))
            return
        by_sid = OrderedDict()
        for key, sid, _ in d["entries"]:
            by_sid.setdefault(sid, []).append(key)
        for sid, keys in by_sid.items():
            sym = self.symbols[sid]
            conds = [c for c in (_condition(k) for k in keys) if c]
            self._register_sym_node(sym)
            self.dispatch_targets.add(sid)
            again = sid in self.expanded
            self._edge(scope.owner, sid, "DISPATCHES_TO", node.lineno, via=d["via"], resolution=d["status"],
                       confidence=_CONFIDENCE[d["status"]], conditions=conds)
            shown = f"{sym.parent.split(':')[1]}.{sym.name}" if sym.parent else sym.name
            when = ("; ".join(f"key {c.get('key', c.get('key_expr'))!r}" for c in conds) + "; ") if conds else ""
            self._emit(depth, f"DISPATCHES {label}()   @{loc}  ->  {sym.file}:{sym.line} {shown}   "
                              f"[{when}{d['status']} target]" + ("   (already expanded)" if again else ""),
                       type="DISPATCHES_TO", target=sid, file=scope.file, line=node.lineno,
                       target_file=sym.file, target_line=sym.line, already_visited=again,
                       resolution=d["status"], conditions=conds)
            if sym.kind == "class":
                self.handle_call(node, Target("symbol", sid, sym.name), scope, depth + 1)
            else:
                self._note_param_types(sym, node, scope)
                self.trace_symbol(sid, depth + 1)
        if d["status"] == "partial":
            self._unresolved(scope, node, "dispatch partially resolved (more targets possible): "
                                          + "; ".join(d["reasons"]))

    def _emit_binding_refs(self, b):
        """REFERENCES edges: the scope that holds the container / alias -> every function it mentions."""
        if b is None or b.kind not in ("table", "alias") or b.lookup:
            return
        extra = {"file": b.file} if b.owner.startswith("file:") else {}
        if extra:
            self._node(b.owner, "file", b.file)
        for key, sid, line in b.entries:
            sym = self.symbols[sid]
            self._node(sid, sym.kind, sym.file, sym.line)
            self.referenced.add(sid)
            c = _condition(key)
            self._edge(b.owner, sid, "REFERENCES", line, via=b.name, conditions=[c] if c else [], **extra)

    def note_binding_refs(self, target, scope):
        for tg in (target.elts if isinstance(target, (ast.Tuple, ast.List)) else [target]):
            if isinstance(tg, ast.Name):
                self._emit_binding_refs(self._lookup_name_binding(tg.id, scope))

    def note_arg_references(self, call, scope):
        """f(..., handler, ...) / f(cb=handler): the function is REFERENCED (not called) by this scope."""
        for a in list(call.args) + [k.value for k in call.keywords]:
            if isinstance(a, ast.Starred):
                a = a.value
            if not isinstance(a, (ast.Name, ast.Attribute)):
                continue
            t = self.resolve_expr(a, scope)
            if t is not None and t.kind == "symbol" and self.symbols[t.ref].kind in ("function", "method"):
                sym = self.symbols[t.ref]
                self._node(sym.id, sym.kind, sym.file, sym.line)
                self.referenced.add(sym.id)
                self._edge(scope.owner, sym.id, "REFERENCES", call.lineno,
                           via=f"argument of {ast.unparse(call.func)}()", conditions=[])

    # ------------------------------------------------------------------
    # Graph helpers
    # ------------------------------------------------------------------
    def _node(self, nid, ntype, file=None, line=None):
        self.nodes.setdefault(nid, {"id": nid, "type": ntype, "file": file, "line": line})

    def _edge(self, src, tgt, etype, line=None, **attrs):
        """One edge per (source, target, type).  Optional attributes (dispatch edges): `conditions` (dispatch
        keys, merged without duplicates), `via`, `resolution`, `confidence`; on a repeat the weaker
        resolution wins."""
        key = (src, tgt, etype)
        cur = self.edges.get(key)
        if cur is None:
            cur = self.edges[key] = {"source": src, "target": tgt, "type": etype, "line": line}
            for k, v in attrs.items():
                cur[k] = list(v) if k == "conditions" else v
            return
        for c in attrs.get("conditions", ()):
            if c not in cur.setdefault("conditions", []):
                cur["conditions"].append(c)
        new = attrs.get("resolution")
        if new and _RESOLUTION_RANK.get(new, 0) > _RESOLUTION_RANK.get(cur.get("resolution"), 0):
            cur["resolution"], cur["confidence"] = new, attrs.get("confidence")

    def _emit(self, depth, text, **meta):
        self.lines.append("    " * depth + text)
        node = {"text": text, **meta, "children": []}
        while self._tree_stack[-1][0] >= depth:
            self._tree_stack.pop()
        self._tree_stack[-1][1]["children"].append(node)
        self._tree_stack.append((depth, node))

    def _unresolved(self, scope, node, reason):
        label = ast.unparse(node.func) if hasattr(node, "func") else ast.unparse(node)
        key = (scope.file, node.lineno, label)
        self.unresolved.setdefault(key, reason)

    def _register_sym_node(self, sym):
        self._node(sym.id, sym.kind, sym.file, sym.line)
        self.reached.add(sym.id)
        self.reached_files.add(sym.file)

    # ------------------------------------------------------------------
    # Stage 3: traversal
    # ------------------------------------------------------------------
    def find_main_block(self, tree):
        for node in tree.body:
            if isinstance(node, ast.If) and isinstance(node.test, ast.Compare):
                t = node.test
                names = [ast.unparse(t.left)] + [ast.unparse(c) for c in t.comparators]
                if "__name__" in names and any("__main__" in n for n in names):
                    return node
        return None

    # --- execution-entry resolution -----------------------------------
    @property
    def entry_label(self):
        """Value reported as `entry_point` in the outputs: the file the user selected."""
        return self.entry

    def _is_docstring_stmt(self, stmt):
        return (isinstance(stmt, ast.Expr) and isinstance(stmt.value, ast.Constant)
                and isinstance(stmt.value.value, str))

    def toplevel_statements(self, tree):
        """Executable module-level statements: no def / class / import / docstring / pass."""
        return [st for st in tree.body
                if not isinstance(st, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef,
                                       ast.Import, ast.ImportFrom, ast.Pass))
                and not self._is_docstring_stmt(st)]

    def _internal_call_targets(self, stmt, scope):
        """Calls in `stmt` that enter internal project code (functions / classes / methods),
        found with the existing name-resolution machinery. Walks the statement in source order
        and tracks `x = Class()` so that `x.method()` resolves."""
        found = []
        for call in self._calls_in(stmt):
            t = self.resolve_expr(call.func, scope)
            if t is not None and t.kind == "symbol":
                found.append((call, t.ref))
            if isinstance(stmt, ast.Assign) and call is stmt.value:
                tv = self.resolve_expr(stmt.value, scope)
                if tv:
                    for tg in stmt.targets:
                        if isinstance(tg, ast.Name):
                            scope.vars[tg.id] = tv
        return found

    def resolve_entry(self):
        """Decide where application execution starts for the user-selected entry FILE.  Priority:
             A. the file explicitly declares an executable entry (`setup.py` / `pyproject.toml`
                console_scripts, `name = package.module:function`) -> that function
             B. `if __name__ == "__main__":` in the file
             C. executable module-level statements of the file (triggers = calls into internal code)
        The user only ever names a file; a function is chosen here, from a declaration inside it.
        Returns a dict: kind (function | main_block | module), file (the file whose code runs),
        line, owner, pseudo, kind-specific data, and `via` when resolved from a declaration."""
        if self.entry.endswith(".py"):
            self._announce_entry()               # missing file vs. AST failed vs. AST ok - kept apart
        scripts = self._declared_entry_points()                          # A
        if self._entry_override is not None:                             # multi-entry: one declared script
            scripts = [s for s in scripts if tuple(s) == tuple(self._entry_override)]
        if scripts:
            info = self._resolve_declared_entry(scripts)
            if info:
                return info
        if self._entry_override is not None:                             # never fall back to the descriptor
            raise SystemExit(f"Declared entry point {self._entry_override[1]}={self._entry_override[2]} "
                             f"does not resolve to a repository file")
        if self.focus and self.entry in self.files:                      # D. a file reached through a URL route
            info = self._resolve_focus_entry()
            if info:
                return info
        if self.entry not in self.py_files:
            raise SystemExit(f"No Python entry point declared in {self.entry}")
        return self._resolve_file_entry(self.entry)                      # B, C (AST or text)

    def _resolve_focus_entry(self):
        """Cross-file traversal: the file was reached because something (a Django route) points at specific
        functions / classes in it.  Those are the entry: a function as is, a class through its own methods
        (class-based view).  Returns None when none of them is defined in the file (-> B / C as usual)."""
        syms = []
        for name in self.focus:
            base = self.symbols.get(f"{self.entry}:{name}")
            if base is None:
                continue
            found = ([s for s in self.symbols.values() if s.parent == base.id and s.kind == "method"]
                     if base.kind == "class" else [base])
            syms += [s for s in found if s not in syms]
        if not syms:
            return None
        self._focus_extra = syms[1:]
        first = syms[0]
        via = dict(declared_in="URL configuration", group="route view", script=", ".join(self.focus),
                   target=f"{self.entry}:{first.name}", file=self.entry,
                   alternatives=[f"{s.name}={self.entry}:{s.name}" for s in syms[1:]])
        return dict(kind="function", sym=first, file=first.file, line=first.line, owner=first.id,
                    pseudo=_FUNC_FILE_FUNCENTRY, via=via)

    def _announce_entry(self):
        """Three distinct situations for the selected .py entry file."""
        if self.entry in self.files:
            print(f"Entry file found:\n    {self.entry}\n\nUsing AST-based Python analysis.\n")
        elif self.entry in self.legacy_files:
            print(f"Entry file found:\n    {self.entry}\n\nAST parsing failed:\n    {self.legacy_reasons[self.entry]}"
                  f"\n\nFalling back to text-based Python analysis (lower confidence).\n")
        else:
            why = ""
            if os.path.isfile(os.path.join(self.root, self.entry)):      # exists, but was never indexed
                why = "\n(the file exists but is excluded from indexing: excluded directory, test-file pattern or unreadable)"
            raise SystemExit(f"Entry file not found:\n    {self.entry}{why}")

    def _resolve_file_entry(self, file):
        """B / C for any discovered file: AST pipeline when it parsed, text analysis when it did not."""
        if file in self.legacy_files:
            return self._resolve_legacy_file_entry(file)
        return self._resolve_python_file_entry(file)

    def _resolve_legacy_file_entry(self, file, func=None):
        """Text-based B / C for a file ast cannot parse (lower confidence).  `func` = a function the
        file's setup.py / pyproject declared (`module:func`).  `main()` is NOT assumed to be the entry:
        a function is only followed when the `__main__` block / module-level code calls it."""
        ti = self.text_info[file]
        common = dict(kind="legacy", file=file, analysis_mode=ANALYSIS_TEXT, reason=self.legacy_reasons.get(file, ""))
        if file != self.entry:
            print(f"Entry target found:\n    {file}\n\nAST parsing failed:\n    {common['reason']}"
                  f"\n\nFalling back to text-based Python analysis (lower confidence).\n")
        d = ti["funcs"].get(func.split(".")[-1]) if func else None
        if d is not None:
            return dict(common, sub="function", line=d["line"], owner=f"{file}:{d['name']}",
                        pseudo=_FUNC_FILE_FUNCENTRY, header=d["line"],
                        lines=legacy_code_lines(ti, d["line"] + 1, d["end"]))
        if ti["main"]:
            m = ti["main"]
            body = [m["line"]] if m["inline"] else legacy_code_lines(ti, m["line"] + 1, m["end"])
            return dict(common, sub="main_block", line=m["line"], owner=f"{file}:<__main__>",
                        pseudo=_FUNC_FILE_ENTRY, header=m["line"], lines=body, inline=m["inline"])
        return dict(common, sub="module", line=(ti["toplevel"] or [1])[0], owner=f"{file}:{_FUNC_FILE_TOPLEVEL}",
                    pseudo=_FUNC_FILE_TOPLEVEL, header=None, lines=list(ti["toplevel"]))

    def _resolve_python_file_entry(self, file):
        """B / C: start from the file itself (its `__main__` block, else its module-level code)."""
        tree = self.files[file]
        block = self.find_main_block(tree)                               # B
        if block is not None:
            return dict(kind="main_block", block=block, file=file, line=block.lineno,
                        owner=f"{file}:<__main__>", pseudo=_FUNC_FILE_ENTRY)
        stmts = self.toplevel_statements(tree)                           # C
        owner = f"{file}:{_FUNC_FILE_TOPLEVEL}"
        probe = Scope(file, None, owner)
        triggers = []                                                    # (stmt, call, symbol id)
        for st in stmts:
            for call, ref in self._internal_call_targets(st, probe):
                triggers.append((st, call, ref))
        line = stmts[0].lineno if stmts else 1
        return dict(kind="module", stmts=stmts, triggers=triggers, file=file, line=line,
                    owner=owner, pseudo=_FUNC_FILE_TOPLEVEL)

    def _declared_entry_points(self):
        """Executable entries declared by the selected file: [(group, script name, "module:attr")].
        Also records package_dir / find_packages(where=) so modules map to repository files."""
        if self.entry.endswith(".toml"):
            return self._pyproject_entry_points()
        tree = self.files.get(self.entry)
        if tree is not None:
            return self._setup_entry_points(tree)
        if self.entry in self.legacy_files:                              # ast failed: text fallback
            return self._legacy_setup_entry_points(self.entry)
        return []

    def _legacy_setup_entry_points(self, rel):
        """`console_scripts` / `name=module:func` recognised in the raw text of an unparseable setup.py."""
        scripts, package_dir, wheres = legacy_setup_entry_points(self.sources[rel])
        if scripts:
            self._set_package_map(package_dir, wheres)
        return self._normalize_entry_points({g: [f"{n}={t}" for gg, n, t in scripts if gg == g]
                                             for g in ("console_scripts", "gui_scripts")})

    def _setup_entry_points(self, tree):
        """`setup(entry_points=..., package_dir=...)` in a setuptools / distutils style script."""
        setup = next((n for n in ast.walk(tree) if isinstance(n, ast.Call)
                      and (_dotted(n.func) or "").split(".")[-1] == "setup"), None)
        if setup is None:
            return []
        consts = {t.id: st.value for st in tree.body if isinstance(st, ast.Assign)
                  for t in st.targets if isinstance(t, ast.Name)}

        def const(n, depth=0):               # literal value (module-level names followed); None if unknown
            if isinstance(n, ast.Name) and n.id in consts and depth < 3:
                return const(consts[n.id], depth + 1)
            try:
                return ast.literal_eval(n)
            except (ValueError, TypeError, SyntaxError):
                pass
            if isinstance(n, ast.Dict):
                items = ((const(k, depth + 1), const(v, depth + 1)) for k, v in zip(n.keys, n.values))
                return {k: v for k, v in items if isinstance(k, str) and v is not None}
            if isinstance(n, (ast.List, ast.Tuple)):
                return [v for v in (const(e, depth + 1) for e in n.elts) if v is not None]
            return None

        kw = {k.arg: k.value for k in setup.keywords if k.arg}
        wheres = []                          # find_packages(where="src") -> packages live under src/
        for n in ast.walk(tree):
            if isinstance(n, ast.Call) and (_dotted(n.func) or "").split(".")[-1].startswith("find_") \
                    and "packages" in (_dotted(n.func) or ""):
                node = next((k.value for k in n.keywords if k.arg == "where"), n.args[0] if n.args else None)
                where = const(node) if node is not None else "."
                if isinstance(where, str):
                    wheres.append(where)
        package_dir = const(kw["package_dir"]) if "package_dir" in kw else {}
        self._set_package_map(package_dir if isinstance(package_dir, dict) else {}, wheres)
        return self._normalize_entry_points(const(kw["entry_points"]) if "entry_points" in kw else None)

    def _pyproject_entry_points(self):
        """`[project.scripts]`, `[project.gui-scripts]`, `[tool.poetry.scripts]` in pyproject.toml."""
        if tomllib is None:
            return []
        try:
            with open(os.path.join(self.root, self.entry), "rb") as f:
                data = tomllib.load(f)
        except (OSError, tomllib.TOMLDecodeError):
            return []
        proj, poetry = data.get("project", {}), data.get("tool", {}).get("poetry", {})
        setuptools = data.get("tool", {}).get("setuptools", {})
        wheres = list((setuptools.get("packages") or {}).get("find", {}).get("where", [])
                      if isinstance(setuptools.get("packages"), dict) else [])
        wheres += [p["from"] for p in poetry.get("packages", []) if isinstance(p, dict) and p.get("from")]
        self._set_package_map(setuptools.get("package-dir", {}), wheres)
        out = []
        for group, table in (("console_scripts", proj.get("scripts")), ("gui_scripts", proj.get("gui-scripts")),
                             ("console_scripts", poetry.get("scripts"))):
            for name, target in (table or {}).items():
                if isinstance(target, str):
                    out.append((group, name, target.split("[")[0].strip()))
        return out

    @staticmethod
    def _normalize_entry_points(value):
        """`entry_points` (dict of lists, or setuptools ini text) -> [(group, name, target)] for the
        executable groups only (console_scripts, gui_scripts); plugin groups are not entry points."""
        if isinstance(value, str):                                       # "[console_scripts]\nname = mod:func"
            groups, cur = {}, None
            for line in value.splitlines():
                line = line.strip()
                if line.startswith("[") and line.endswith("]"):
                    cur = groups.setdefault(line[1:-1].strip(), [])
                elif cur is not None and "=" in line and not line.startswith("#"):
                    cur.append(line)
            value = groups
        out = []
        for group in ("console_scripts", "gui_scripts"):
            items = (value or {}).get(group) or []
            for item in (items.splitlines() if isinstance(items, str) else items):
                name, _, target = str(item).partition("=")
                target = target.split("[")[0].strip()                    # drop `[extras]`
                if name.strip() and target:
                    out.append((group, name.strip(), target))
        return out

    def _set_package_map(self, package_dir, wheres=()):
        """package_dir={"pkg": "code"} / {"": "src"} / find_packages(where="src") -> [(prefix, dir)],
        directories made relative to the repository root (the declaring file's directory is the base)."""
        base = os.path.dirname(self.entry)
        pairs = [(p, d) for p, d in package_dir.items() if isinstance(p, str) and isinstance(d, str)]
        pairs += [("", w) for w in wheres if isinstance(w, str)]
        mapped = []
        for pkg, d in pairs:
            d = posixpath.normpath(posixpath.join(base, d))
            mapped.append((pkg, "" if d == "." else d))
        self.package_map = [m for m in mapped if m != ("", "")]

    def _mapped_module_file(self, parts):
        """Dotted module (as parts) -> repository file through the package map; None if not mapped."""
        for pkg, d in self.package_map:
            prefix = pkg.split(".") if pkg else []
            if not parts or parts[:len(prefix)] != prefix:
                continue
            rest = parts[len(prefix):]
            stem = posixpath.join(d, *rest)
            for c in ([stem + ".py"] if rest else []) + [posixpath.join(stem, "__init__.py")]:
                if c in self.py_files:
                    return c
        return None

    def _resolve_declared_entry(self, scripts):
        """`name = package.module:function` -> that function in the repository.  The first declaration
        that resolves to a repository file wins; the others are only reported.  Returns None (after a
        warning) when nothing resolves, so the selected file is analysed itself (B / C)."""
        resolved = []
        for group, name, target in scripts:
            module, _, attr = target.partition(":")
            module_file = self.find_module_file(module.strip(), 0, self.entry) if module.strip() else None
            if module_file:
                resolved.append((group, name, target, module_file, attr.strip()))
        if not resolved:
            print(f"App Broker: {self.entry} declares entry point(s) "
                  f"({', '.join(f'{n}={t}' for _, n, t in scripts)}) but none resolves to a repository "
                  f"file; analysing {self.entry} itself", file=sys.stderr)
            return None
        group, name, target, module_file, attr = resolved[0]
        via = dict(declared_in=self.entry, group=group, script=name, target=target, file=module_file,
                   alternatives=[f"{n}={t}" for _, n, t, _, _ in resolved[1:]])
        where = os.path.dirname(module_file)
        if where not in self.import_bases:       # a started script's directory is on sys.path
            self.import_bases.append(where)
        if module_file in self.legacy_files:     # `module:function` inside a file ast cannot parse
            info = self._resolve_legacy_file_entry(module_file, func=attr or None)
            info["via"] = via
            return info
        sym = self._find_entry_symbol(module_file, attr) if attr else None
        if sym is not None:
            info = dict(kind="function", sym=sym, file=sym.file, line=sym.line,
                        owner=sym.id, pseudo=_FUNC_FILE_FUNCENTRY)
        else:                                    # no such function: continue from the module itself
            info = self._resolve_python_file_entry(module_file)
        info["via"] = via
        return info

    def discover_declared_entries(self):
        """EVERY executable entry declared by the selected descriptor (setup.py / pyproject.toml), in
        declaration order, each with its own metadata.  Needs the repository index.  An entry whose module
        is not a repository file stays in the list with status ERROR (it is never dropped)."""
        if not self._index_ready:
            self.index_repository()
        out = []
        for group, name, target in self._declared_entry_points():
            module, _, attr = target.partition(":")
            module = module.strip()
            mfile = self.find_module_file(module, 0, self.entry) if module else None
            out.append(OrderedDict([
                ("entry_point_name", name), ("group", group), ("target", target), ("module", module),
                ("callable", attr.strip() or None), ("entry_file", mfile), ("language", "python"),
                ("source", self.entry), ("parent_setup", self.entry),
                ("status", "SUCCESS" if mfile else "ERROR"),
                ("error", None if mfile else f"module '{module}' (entry point {name}={target}) "
                                             f"does not resolve to a repository file")]))
        return out

    def fork_for_entry(self, entry):
        """A fresh broker for ONE discovered entry that reuses this broker's repository index, so a repository
        with N entries is indexed once.  All analysis state (trace, graph, expanded set ...) is new."""
        b = PythonBroker(self.root, self.entry, self.internal_hints,
                         entry_override=(entry["group"], entry["entry_point_name"], entry["target"]),
                         framework=self.framework_mode, arch_depth=self.arch_depth,
                         arch_max_files=self.arch_max_files)
        b.files, b.sources, b.py_files = self.files, self.sources, self.py_files
        b.legacy_files, b.legacy_reasons = self.legacy_files, self.legacy_reasons
        b.analysis_mode, b.text_info, b.imports = self.analysis_mode, self.text_info, self.imports
        b.parse_errors, b.package_map = list(self.parse_errors), list(self.package_map)
        b.symbols = OrderedDict((k, v) for k, v in self.symbols.items() if "<local>" not in k)
        b._index_ready = True
        return b

    def _find_entry_symbol(self, file, attr):
        """`function`, `Class` (-> its __init__) or `Class.method` defined in `file`; re-exports followed."""
        sym = self.symbols.get(f"{file}:{attr}")
        if sym is None and "." not in attr:
            t = self.resolve_name(attr, file)
            sym = self.symbols.get(t.ref) if t.kind == "symbol" else None
        if sym is not None and sym.kind == "class":
            init = self.find_method(sym.id, "__init__")
            sym = self.symbols[init] if init else None
        return sym

    def _via_note(self, info):
        via = info.get("via")
        return f"declared in {via['declared_in']}: {via['group']} {via['script']}={via['target']}" if via else ""

    def _entry_report_lines(self):
        via = (self.entry_info or {}).get("via")
        if not via:
            return []
        alt = f"   (other declared scripts: {', '.join(via['alternatives'])})" if via["alternatives"] else ""
        return [f"Resolved from : {self._via_note(self.entry_info)}  ->  {via['file']}{alt}"]

    def _ensure_entry(self):
        if self.entry_info is None:
            self.entry_info = self.resolve_entry()
        return self.entry_info

    # ------------------------------------------------------------------
    # Cross-file discovery (shared FileCollector, owned by App Broker)
    #
    # The broker only REPORTS what it found (discovered_references) and, when App Broker asks, hands it to the
    # one shared collector (submit_discovered_references).  It never creates a collector, never decides when a
    # discovered file is analysed, and never changes the analysis output above.
    # ------------------------------------------------------------------
    # template-loading calls -> position of the template-name argument
    _TEMPLATE_CALLS = {"render": 1, "render_to_response": 0, "render_to_string": 0, "get_template": 0,
                       "select_template": 0, "TemplateResponse": 1, "SimpleTemplateResponse": 0}
    _TEMPLATE_RE = re.compile(r"""(?:template_name\s*=\s*|\b(?:render|get_template|render_to_string|select_template)"""
                              r"""\(\s*(?:request\s*,\s*)?)['"]([^'"\n]+)['"]""")
    _IMPORT_LINE_RE = re.compile(r"^[ \t]*(?:from[ \t]+(\.*)([\w.]*)[ \t]+import[ \t]+([^#\n]+)|import[ \t]+([^#\n]+))", re.M)

    def fork_for_file(self, file, focus=None):
        """A fresh broker for ONE discovered file that reuses this broker's repository index (so N discovered
        files cost one indexing pass, not N).  Meant to be called on an index-only broker (index_repository()
        done, run() never called); all analysis state of the fork is new."""
        if not self._index_ready:
            self.index_repository()
        b = type(self)(self.root, file, self.internal_hints, framework=self.framework_mode,
                         arch_depth=self.arch_depth, arch_max_files=self.arch_max_files, collector=self.collector,
                         focus=focus)
        b.files, b.sources, b.py_files = self.files, self.sources, self.py_files
        b.legacy_files, b.legacy_reasons = self.legacy_files, self.legacy_reasons
        b.analysis_mode, b.text_info, b.imports = self.analysis_mode, self.text_info, self.imports
        b.parse_errors, b.package_map = list(self.parse_errors), list(self.package_map)
        b.symbols = OrderedDict((k, v) for k, v in self.symbols.items() if "<local>" not in k)
        b._index_ready = True
        return b

    def _scan_files(self):
        """Files whose references are reported: the entry and every file the analysis reached."""
        files = set(self.reached_files) | {self.entry}
        if self.entry_info:
            files.add(self.entry_info["file"])
        return sorted(f for f in files if f in self.py_files)

    def _import_target(self, rel, module, level, names, line, add):
        """One import statement -> project files (strict, exact module lookup; no basename guessing)."""
        found = False
        for name in (names or [None]):
            dotted = f"{module}.{name}" if (module and name) else (name or module)
            f = self._strict_module_file(dotted, level, rel) if (dotted or level) else None
            shown = ("." * level) + (dotted or "")                # the module as written in the source
            if f is None and name is not None:                    # `from pkg import symbol`: the file is pkg itself
                f = self._strict_module_file(module, level, rel) if (module or level) else None
                shown = ("." * level) + (module or "")
            if f is not None:
                found = True
                if f != rel:
                    add(reference=shown or ".", source_file=rel, line=line, relationship="imports", kind="import",
                        disposition="queue", files=[f], reason=None)
        if not found:
            top = (module or "").split(".")[0] or (names or [""])[0].split(".")[0]
            if level or (top and top in self.internal_hints):
                add(reference=("." * level) + (module or "") + (f" import {', '.join(names)}" if names else ""),
                    source_file=rel, line=line, relationship="imports", kind="import", disposition="unresolved",
                    files=[], reason="project-local module does not resolve to a file in the repository")
            # standard-library and third-party imports are intentionally not reported / not queued

    def _template_names(self, node):
        """Template-name argument -> ([constant names], dynamic expression text or None)."""
        if isinstance(node, ast.Constant) and isinstance(node.value, str):
            return [node.value], None
        if isinstance(node, (ast.List, ast.Tuple)):
            names = [e.value for e in node.elts if isinstance(e, ast.Constant) and isinstance(e.value, str)]
            return names, (None if len(names) == len(node.elts) else ast.unparse(node)[:60])
        return [], ast.unparse(node)[:60]

    def _module_ref(self, rel, dotted, line, relationship, add):
        """A dotted module name written as a STRING (settings / URLconf wiring) -> project file, or unresolved."""
        f = self._strict_module_file(dotted, 0, rel)
        if f and f != rel:
            add(reference=dotted, source_file=rel, line=line, relationship=relationship, kind="import",
                disposition="queue", files=[f], reason=None)
        elif not f and dotted.split(".")[0] in self.internal_hints:
            add(reference=dotted, source_file=rel, line=line, relationship=relationship, kind="import",
                disposition="unresolved", files=[], reason="project-local module does not resolve to a file")

    def _config_references(self, rel, node, add):
        """Django wiring that is not an import statement: ``DJANGO_SETTINGS_MODULE``, ``ROOT_URLCONF`` and
        ``include("pkg.urls")`` name project modules as strings.  Following them lets a traversal that starts at
        manage.py / settings.py reach the URLconfs and, through their imports, the views."""
        def const(n):
            return n.value if isinstance(n, ast.Constant) and isinstance(n.value, str) else None
        if isinstance(node, ast.Call):
            last = (_dotted(node.func) or "").rsplit(".", 1)[-1]
            if last == "setdefault" and len(node.args) >= 2 and const(node.args[0]) == "DJANGO_SETTINGS_MODULE" \
                    and const(node.args[1]):
                self._module_ref(rel, const(node.args[1]), node.lineno, "settings_module", add)
            elif last == "include" and node.args and const(node.args[0]):
                self._module_ref(rel, const(node.args[0]), node.lineno, "includes_urlconf", add)
        elif isinstance(node, ast.Assign) and const(node.value):
            for t in node.targets:
                if isinstance(t, ast.Name) and t.id == "ROOT_URLCONF":
                    self._module_ref(rel, const(node.value), node.lineno, "root_urlconf", add)
                elif isinstance(t, ast.Subscript) and const(t.slice) == "DJANGO_SETTINGS_MODULE":
                    self._module_ref(rel, const(node.value), node.lineno, "settings_module", add)

    def discovered_references(self):
        """Project-local files referenced by the analysed code, for the shared FileCollector.

        Each item: reference, source_file, line, relationship ("imports" | "renders_template" | "template_name"),
        kind ("import" | "template"), disposition ("queue" | "unresolved"), files ([project-relative paths]), reason.
        Standard-library and third-party imports are neither reported nor queued; nothing outside the repository
        or nonexistent is ever placed in ``files``.  Template names are looked up in the project's ``templates``
        directories (django_routes.TemplateIndex); every candidate is kept when several match (ambiguous)."""
        if self._discovered is not None:
            return self._discovered
        from django_routes import TemplateIndex
        templates = TemplateIndex(self.root)
        refs, seen = [], set()

        def add(**r):
            key = (r["kind"], r["reference"], r["source_file"], r["line"], r["disposition"])
            if key not in seen:
                seen.add(key)
                refs.append(r)

        def template(rel, name, line, relationship):
            files = templates.lookup(name)
            if files:
                add(reference=name, source_file=rel, line=line, relationship=relationship, kind="template",
                    disposition="queue", files=files,
                    reason=(f"ambiguous: {len(files)} templates share this name" if len(files) > 1 else None))
            else:
                add(reference=name, source_file=rel, line=line, relationship=relationship, kind="template",
                    disposition="unresolved", files=[],
                    reason="no HTML template with this name under any 'templates' directory")

        for rel in self._scan_files():
            tree = self.files.get(rel)
            if tree is not None:
                for node in ast.walk(tree):
                    self._config_references(rel, node, add)
                    if isinstance(node, ast.Import):
                        for a in node.names:
                            self._import_target(rel, a.name, 0, None, node.lineno, add)
                    elif isinstance(node, ast.ImportFrom):
                        self._import_target(rel, node.module or "", node.level,
                                            [a.name for a in node.names if a.name != "*"] or None, node.lineno, add)
                    elif isinstance(node, ast.Call):
                        text = _dotted(node.func)
                        parts = text.split(".") if text and "(" not in text and "[" not in text else []
                        fname = parts[-1] if parts else None
                        idx = self._TEMPLATE_CALLS.get(fname)
                        if idx is not None and len(node.args) > idx:
                            names, dyn = self._template_names(node.args[idx])
                            for n in names:
                                template(rel, n, node.lineno, "renders_template")
                            if dyn and (len(parts) == 1 or parts[-2] in ("shortcuts", "loader")):
                                add(reference=dyn, source_file=rel, line=node.lineno, relationship="renders_template",
                                    kind="template", disposition="unresolved", files=[],
                                    reason="dynamic template name: not evaluated")
                        for kw in node.keywords:
                            if kw.arg == "template_name":
                                for n in self._template_names(kw.value)[0]:
                                    template(rel, n, node.lineno, "template_name")
                    elif isinstance(node, ast.Assign) and any(isinstance(t, ast.Name) and t.id == "template_name"
                                                              for t in node.targets):
                        for n in self._template_names(node.value)[0]:
                            template(rel, n, node.lineno, "template_name")
            else:                                                  # text-analysed (legacy) file: regex fallback
                src = self.sources.get(rel, "")
                for m in self._IMPORT_LINE_RE.finditer(src):
                    line = src.count("\n", 0, m.start()) + 1
                    if m.group(3) is not None:
                        names = [n.strip().split(" as ")[0].strip("() ") for n in m.group(3).split(",")]
                        self._import_target(rel, m.group(2), len(m.group(1)), [n for n in names if n and n != "*"] or None,
                                            line, add)
                    else:
                        for part in m.group(4).split(","):
                            mod = part.strip().split(" as ")[0].strip()
                            if mod:
                                self._import_target(rel, mod, 0, None, line, add)
                for m in self._TEMPLATE_RE.finditer(src):
                    template(rel, m.group(1), src.count("\n", 0, m.start()) + 1, "template_name")
        self._discovered = refs
        return refs

    def submit_discovered_references(self):
        """Hand discovered project-local files to the shared collector (App Broker calls this after run()).
        Returns the number of NEW files queued; 0 when no collector was injected."""
        if self.collector is None:
            return 0
        added = 0
        for r in self.discovered_references():
            if r["disposition"] != "queue":
                continue
            for f in r["files"]:
                meta = {"line": r["line"], "kind": r["kind"], "relationship": r["relationship"]}
                if r["kind"] == "template":
                    meta["role"] = "template"
                if self.collector.add_path(os.path.join(self.root, f), source_broker="python",
                                           source_file=r["source_file"], original_reference=r["reference"], meta=meta):
                    added += 1
        return added

    def run(self):
        if not self._index_ready:                  # a forked broker shares its parent's index
            self.index_repository()                # unchanged: never depends on an entry
        info = self._ensure_entry()
        efile, via = info["file"], self._via_note(info)
        self.reached_files.add(self.entry)
        self.reached_files.add(efile)
        if info["kind"] == "function":
            sym = info["sym"]
            self._node(info["owner"], "entry", sym.file, sym.line)
            self._emit(0, f"ENTRY  {sym.file}:{sym.line}  def {sym.name}   ({via})",
                       type="ENTRY", target=sym.id, file=sym.file, line=sym.line)
            self.trace_symbol(sym.id, 1)
            for extra in self._focus_extra:                  # further route views of the same file
                self._node(extra.id, "entry", extra.file, extra.line)
                self._emit(0, f"ENTRY  {extra.file}:{extra.line}  def {extra.name}   ({via})",
                           type="ENTRY", target=extra.id, file=extra.file, line=extra.line)
                self.trace_symbol(extra.id, 1)
        elif info["kind"] == "legacy":              # text-based analysis (lower confidence)
            self._run_legacy(info, via)
        elif info["kind"] == "main_block":
            block = info["block"]
            self._node(info["owner"], "entry", efile, block.lineno)
            self._emit(0, f"ENTRY  {efile}:{block.lineno}  if __name__ == \"__main__\"" + (f"   ({via})" if via else ""))
            scope = Scope(efile, None, info["owner"])
            for stmt in block.body:
                Visitor(self, scope, 1).visit(stmt)
        else:
            self._node(info["owner"], "entry", efile, info["line"])
            trig = info["triggers"]
            note = (f"first trigger: {self.symbols[trig[0][2]].name}() @{efile}:{trig[0][1].lineno}"
                    if trig else "no internal call found at module level")
            self._emit(0, f"ENTRY  {efile}:{info['line']}  {_FUNC_FILE_TOPLEVEL}   ({note}" + (f"; {via}" if via else "") + ")")
            scope = Scope(efile, None, info["owner"])
            for stmt in info["stmts"]:
                Visitor(self, scope, 1).visit(stmt)
        # With a shared FileCollector (App Broker's cross-file traversal) the files this one points at are queued
        # and analysed one by one by App Broker, so the two internal multi-file walks are not run here:
        #   _include_legacy_imports  - pulled imported modules into reached_files
        #   analyze_frameworks       - walked settings -> URLconfs -> views -> apps on its own
        # Without a collector (single-file runs, --no-follow-references) both run exactly as before.
        if self.collector is None:
            self._include_legacy_imports()
        self._build_import_edges()
        if self.collector is None:
            self.analyze_frameworks()           # architecture-only; never changes reached / reached_files

    def analyze_frameworks(self):
        """Configuration-driven architecture traversal (Django first).  Additive and isolated: it only adds
        architecture edges / nodes and `framework_info`; a failure here never breaks the execution outputs."""
        self.framework_info = None
        mode = (self.framework_mode or "none").lower()
        if mode == "none":
            return
        names = list(FRAMEWORK_ANALYZERS) if mode == "auto" else [mode]
        for name in names:
            cls = FRAMEWORK_ANALYZERS.get(name)
            if cls is None:
                raise SystemExit(f"Unknown framework '{name}' (supported: {', '.join(FRAMEWORK_ANALYZERS)})")
            before = (set(self.reached), set(self.reached_files), set(self.expanded))
            try:
                an = cls(self)
                seed = an.detect()
                if seed is None:
                    continue
                self.framework_info = an.analyze(seed)
            except Exception as e:               # defensive: the execution outputs must survive
                import traceback
                self.framework_error = f"{type(e).__name__}: {e}"
                print(f"WARNING: {name} architecture analysis failed; execution outputs are unaffected: "
                      f"{self.framework_error}", file=sys.stderr)
                traceback.print_exc()
            if before != (self.reached, self.reached_files, self.expanded):
                raise AssertionError("architecture pass altered execution state")
            if self.framework_info:
                return
        if mode != "auto":
            self.framework_info = OrderedDict(framework=mode, active=False,
                                              reason=f"entry {self.entry} shows no {mode} settings / URL configuration")

    @staticmethod
    def discover_framework_entries(root):
        """Framework-aware discovery for app_broker (no --entry given).  Returns dicts
        {file, role, framework, settings_module, covered_by}.  `process_entry` = file that starts the framework
        (calls execute_from_command_line / get_wsgi_application / get_asgi_application and names the settings
        module); `configuration_root` = settings module (assigns ROOT_URLCONF / INSTALLED_APPS).  Request-routing
        roots are NOT listed: they are derived from ROOT_URLCONF during analysis.  A configuration root already
        named by a discovered process entry has `covered_by` set (it is analysed through that entry)."""
        root = os.path.abspath(root)
        found, rels = [], set()
        for dirpath, dirnames, filenames in os.walk(root):
            dirnames[:] = sorted(d for d in dirnames if d not in EXCLUDE_DIRS)
            for fn in sorted(filenames):
                if fn.endswith(".py") and not any(fnmatch.fnmatch(fn, p) for p in EXCLUDE_FILES):
                    rels.add(os.path.relpath(os.path.join(dirpath, fn), root).replace(os.sep, "/"))
        for rel in sorted(rels):
            try:
                text = PythonBroker._read_source(os.path.join(root, rel))
            except OSError:
                continue
            if not any(k in text for k in ("DJANGO_SETTINGS_MODULE", "ROOT_URLCONF", "INSTALLED_APPS")):
                continue
            try:
                tree = ast.parse(text, filename=rel)
            except (SyntaxError, ValueError, RecursionError):
                continue
            ref = DjangoAnalyzer.settings_module_reference(tree)
            starters = ("execute_from_command_line", "get_wsgi_application", "get_asgi_application")
            starter = any(isinstance(n, ast.Call) and (n.func.id if isinstance(n.func, ast.Name)
                                                       else getattr(n.func, "attr", "")) in starters
                          for n in ast.walk(tree))
            if ref and starter:
                found.append(dict(file=rel, role="process_entry", framework="django",
                                  settings_module=ref[0], covered_by=None))
                continue
            names = set()
            for st in _toplevel_stmts(tree.body):
                if isinstance(st, ast.Assign):
                    names.update(t.id for t in st.targets if isinstance(t, ast.Name))
                elif isinstance(st, (ast.AugAssign, ast.AnnAssign)) and isinstance(st.target, ast.Name):
                    names.add(st.target.id)
            if names & {"ROOT_URLCONF", "INSTALLED_APPS"}:
                found.append(dict(file=rel, role="configuration_root", framework="django",
                                  settings_module=None, covered_by=None))
        for p in (f for f in found if f["role"] == "process_entry" and f["settings_module"]):
            parts = p["settings_module"].split(".")
            for base in ("", posixpath.dirname(p["file"])):
                for cand in (posixpath.join(base, *parts) + ".py", posixpath.join(base, *parts, "__init__.py")):
                    for c in found:
                        if (c["role"] == "configuration_root" and c["file"] == cand.lstrip("/")
                                and c["covered_by"] is None):
                            c["covered_by"] = p["file"]
        return found

    # ------------------------------------------------------------------
    # Text-based (legacy) traversal: same outputs, lower confidence
    # ------------------------------------------------------------------
    def _legacy_resolve_call(self, file, dotted):
        """One text-detected call -> ("local", def record) | ("class", class record) | ("target", Target) | None.
        Local functions/classes are matched by name; everything else goes through the regular import-table
        resolution, which works because legacy files have an `imports` table like parsed files do."""
        ti = self.text_info[file]
        if "." not in dotted:
            if dotted in ti["funcs"]:
                return "local", ti["funcs"][dotted]
            if dotted in ti["classes"]:
                return "class", ti["classes"][dotted]
        parts = dotted.split(".")
        t = self.resolve_name(parts[0], file)
        if t.kind == "unknown":
            return None
        for part in parts[1:]:
            t = self._resolve_attr(t, part) if t else None
        return ("target", t) if t is not None else None

    def _legacy_init(self, file, cls):
        ti = self.text_info[file]
        return next((d for d in ti["defs"] if d["kind"] == "method" and d["parent"] == cls["name"]
                     and d["name"] == "__init__"), None)

    def _run_legacy(self, info, via):
        file = info["file"]
        self._node(info["owner"], "entry", file, info["line"])
        what = {"function": f"def {info['owner'].split(':')[1]}", "main_block": 'if __name__ == "__main__"',
                "module": _FUNC_FILE_TOPLEVEL}[info["sub"]]
        self._emit(0, f"ENTRY  {file}:{info['line']}  {what}   [text-based analysis, lower confidence]"
                   + (f"   ({via})" if via else ""), type="ENTRY", file=file, line=info["line"],
                   analysis_mode=ANALYSIS_TEXT)
        scope = Scope(file, None, info["owner"])
        self._legacy_walk(file, info["lines"], scope, 1, {info["owner"]})

    def _legacy_walk(self, file, linenos, scope, depth, active):
        ti = self.text_info[file]
        for ln in linenos:
            for dotted in legacy_calls_on_line(ti, ln):
                kind, what = (self._legacy_resolve_call(file, dotted) or (None, None))
                if kind in ("local", "class"):
                    d = what if kind == "local" else self._legacy_init(file, what)
                    name = what["name"]
                    sid = f"{file}:{name}"
                    again = sid in self.expanded
                    self._node(sid, "function" if kind == "local" else "class", file, what["line"])
                    self._edge(scope.owner, sid, "CALLS" if kind == "local" else "INSTANTIATES", ln)
                    self.reached.add(sid)
                    self.reached_files.add(file)
                    self._emit(depth, f"{'CALLS' if kind == 'local' else 'INSTANTIATES'} {dotted}()   @{file}:{ln}"
                               f"  ->  {file}:{what['line']} {name}   [text]" + ("   (already expanded)" if again else ""),
                               type="CALLS" if kind == "local" else "INSTANTIATES", target=sid, file=file,
                               line=ln, target_file=file, target_line=what["line"], already_visited=again,
                               analysis_mode=ANALYSIS_TEXT)
                    if not again and sid not in active and d is not None:
                        self.expanded.add(sid)
                        sub = Scope(file, None, sid)
                        self._legacy_walk(file, legacy_code_lines(ti, d["line"] + 1, d["end"]), sub, depth + 1,
                                          active | {sid})
                elif kind == "target":
                    node = _synthetic_call(dotted, ln)
                    if node is not None:
                        self.handle_call(node, what, scope, depth)

    def _include_legacy_imports(self):
        """Repository discovery through legacy files: internal modules imported from a legacy file (and
        legacy modules imported from anywhere) join the reached files, so their imports become edges
        too.  Does nothing when the repository has no legacy file."""
        if not self.legacy_files:
            return
        queue, seen = list(self.reached_files), set(self.reached_files)
        while queue:
            rel = queue.pop()
            for imp in self.imports.get(rel, {}).values():
                kind, ref = self.classify_module(imp["module"], imp["level"], rel)
                if kind != "internal":
                    continue
                targets = [ref]
                if imp["name"] and imp["name"] != "*":      # `from pkg import submodule`
                    full = f"{imp['module']}.{imp['name']}" if imp["module"] else imp["name"]
                    sub = self.find_module_file(full, imp["level"], rel)
                    if sub:
                        targets.append(sub)
                for t in targets:
                    if t in seen or not (rel in self.legacy_files or t in self.legacy_files):
                        continue
                    seen.add(t)
                    self.reached_files.add(t)
                    if t in self.legacy_files:
                        queue.append(t)

    def trace_symbol(self, sid, depth):
        if sid in self.expanded or depth > MAX_DEPTH:
            return
        self.expanded.add(sid)
        sym = self.symbols[sid]
        self._register_sym_node(sym)
        scope = Scope(sym.file, sym.parent if sym.kind == "method" else None, sid)
        for stmt in sym.node.body:                      # pre-register nested defs
            if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef)):
                nid = f"{sid}.<local>{stmt.name}"
                if nid not in self.symbols:
                    self.symbols[nid] = Symbol(nid, "function", stmt.name, sym.file, stmt)
                scope.local_funcs[stmt.name] = nid
        self._bind_local_imports(scope, sym)
        scope.bindings = self._function_bindings(sym)
        self._apply_param_hints(scope, sym)
        for stmt in sym.node.body:
            Visitor(self, scope, depth).visit(stmt)

    def handle_call(self, node, target, scope, depth):
        label = ast.unparse(node.func)
        loc = f"{scope.file}:{node.lineno}"
        if target is None:
            if not isinstance(getattr(node.func, "value", None), ast.Constant):
                self._unresolved(scope, node, "receiver type unknown (dynamic / parameter / builtin result)")
            return
        k = target.kind
        if k in ("builtin", "module", "unknown"):
            return
        if k in ("external", "stdlib"):
            root = target.label.split(".")[0]
            (self.external_calls if k == "external" else self.stdlib_calls)[root].add(target.label)
            if self.call_sites.get((scope.file, node.lineno)) != "external":
                self.call_sites[(scope.file, node.lineno)] = k
            self._emit(depth, f"[{k.upper()}] {target.label}()   @{loc}   (not followed)",
                       type=k.upper(), target=target.label, file=scope.file, line=node.lineno)
            return
        if k == "missing":
            root = target.label.split(".")[0]
            self.missing_calls[root].add(target.label)
            self._emit(depth, f"[MISSING FILE] {target.label}()   @{loc}   (internal, source not in repository)")
            self._node(f"missing:{target.label}", "missing")
            self._edge(scope.owner, f"missing:{target.label}", "CALLS", node.lineno)
            return

        sym = self.symbols[target.ref]
        self._register_sym_node(sym)
        if sym.kind == "class":
            self._edge(scope.owner, sym.id, "INSTANTIATES", node.lineno)
            self._emit(depth, f"INSTANTIATES {sym.name}(...)   @{loc}  ->  {sym.file}:{sym.line}",
                       type="INSTANTIATES", target=sym.id, file=scope.file, line=node.lineno,
                       target_file=sym.file, target_line=sym.line)
            self._show_inheritance(sym, depth + 1)
            init = self.find_method(sym.id, "__init__")
            if init:
                again = init in self.expanded
                self._emit(depth + 1, f"CALLS {self.symbols[init].file}:{self.symbols[init].line}  "
                                      f"{sym.name}.__init__" + ("   (already expanded)" if again else ""),
                           type="CALLS", target=init, file=self.symbols[init].file,
                           line=self.symbols[init].line, already_visited=again)
                self._edge(sym.id, init, "CALLS", self.symbols[init].line)
                self._note_param_types(self.symbols[init], node, scope)
                self.trace_symbol(init, depth + 2)
        else:
            again = sym.id in self.expanded
            self._edge(scope.owner, sym.id, "CALLS", node.lineno)
            shown = f"{sym.parent.split(':')[1]}.{sym.name}" if sym.parent else sym.name
            self._emit(depth, f"CALLS {label}()   @{loc}  ->  {sym.file}:{sym.line} {shown}"
                       + ("   (already expanded)" if again else ""),
                       type="CALLS", target=sym.id, file=scope.file, line=node.lineno,
                       target_file=sym.file, target_line=sym.line, already_visited=again)
            self._note_param_types(sym, node, scope)
            self.trace_symbol(sym.id, depth + 1)

    def _show_inheritance(self, cls, depth):
        if cls.id in self.class_expanded:
            return
        self.class_expanded.add(cls.id)
        for bnode, t in self.class_bases(cls.id):
            bl = ast.unparse(bnode)
            if t and t.kind == "symbol":
                b = self.symbols[t.ref]
                self._register_sym_node(b)
                self._edge(cls.id, b.id, "INHERITS", cls.line)
                self._emit(depth, f"INHERITS {bl}  ->  {b.file}:{b.line}",
                           type="INHERITS", target=b.id, file=cls.file, line=cls.line,
                           target_file=b.file, target_line=b.line)
            elif t and t.kind == "missing":
                self._node(f"missing:{t.label}", "missing")
                self._edge(cls.id, f"missing:{t.label}", "INHERITS", cls.line)
                self._emit(depth, f"INHERITS {bl}  ->  [MISSING FILE] {t.label}")
                self.missing_calls[t.label.split('.')[0]].add(t.label)
            elif t:
                self._emit(depth, f"INHERITS {bl}  ->  [{t.kind.upper()}] {t.label}")
            else:
                self._emit(depth, f"INHERITS {bl}  ->  [unresolved]")

    def _build_import_edges(self):
        for rel in sorted(self.reached_files):
            self._node(f"file:{rel}", "file", rel)
            if rel in self.legacy_files:
                self.nodes[f"file:{rel}"]["analysis_mode"] = ANALYSIS_TEXT
            for alias, imp in self.imports.get(rel, {}).items():
                kind, ref = self.classify_module(imp["module"], imp["level"], rel)
                if kind == "internal":
                    self._node(f"file:{ref}", "file", ref)
                    self.import_edges[(rel, ref)] = ("internal", imp["line"])
                elif kind == "missing":
                    self.import_edges[(rel, f"MISSING:{ref}")] = ("missing", imp["line"])
                else:
                    self.import_edges[(rel, f"{kind}:{ref}")] = (kind, imp["line"])

    def code_lines(self, rel):
        """(lineno, text) for every code line: no blank lines, no comment-only lines.
        Lines inside multi-line strings/docstrings are kept untouched."""
        src = self.sources[rel]
        lines = src.splitlines()
        in_string, kinds = set(), defaultdict(list)
        try:
            for t in tokenize.generate_tokens(io.StringIO(src).readline):
                if t.type == tokenize.STRING and t.end[0] > t.start[0]:
                    in_string.update(range(t.start[0] + 1, t.end[0] + 1))
                if t.type not in (tokenize.NL, tokenize.NEWLINE, tokenize.INDENT,
                                  tokenize.DEDENT, tokenize.ENDMARKER):
                    kinds[t.start[0]].append(t.type)
        except (tokenize.TokenError, IndentationError):
            pass
        out = []
        for n, text in enumerate(lines, 1):
            if n in in_string:
                out.append((n, text.rstrip()))
            elif not text.strip():
                continue
            elif kinds.get(n) and all(k == tokenize.COMMENT for k in kinds[n]):
                continue
            else:
                out.append((n, text.rstrip()))
        return out


    # ------------------------------------------------------------------
    # Structured outputs
    # ------------------------------------------------------------------
    def source_inventory(self):
        """Complete inventory of EVERY discovered project source file with its original lines.

        Independent of the execution trace: it is built from the repository index (``py_files`` /
        ``sources``), so a file is listed whether or not it is imported, called or reached from the
        entry point - parseable files and legacy (text-analysed) files alike.  Lines are the original
        lines, numbered exactly like Python numbers them (see ``split_source_lines``); blank lines,
        comments and docstrings are kept.  ``skipped`` lists files that were found but could not be
        read.  Nothing here is derived from ``trace_entries``."""
        if not self._index_ready:
            self.index_repository()
        files, total = [], 0
        for rel in sorted(self.py_files):
            src = self.sources.get(rel)
            if src is None:
                continue
            lines = split_source_lines(src)
            if lines and lines[-1] == "":        # a trailing newline ends the last line, it does not start a new one
                lines.pop()
            total += len(lines)
            files.append(OrderedDict([
                ("path", rel), ("module", self._module_of(rel)),
                ("analysis_mode", self.analysis_mode.get(rel, ANALYSIS_AST)),
                ("reached", rel in self.reached_files),
                ("line_count", len(lines)), ("lines", lines)]))
        skipped = [OrderedDict([("file", f), ("error", e)]) for f, e in self.parse_errors if f not in self.py_files]
        return OrderedDict([("contract", "source_inventory/1"), ("files", files), ("skipped", skipped),
                            ("stats", OrderedDict([("files", len(files)), ("lines", total),
                                                   ("reached_files", sum(1 for x in files if x["reached"]))]))])

    def _module_of(self, rel):
        return rel[:-3].replace("/", ".") if rel.endswith(".py") else rel

    def index_json(self):
        out = {}
        for s in self.symbols.values():
            if "<local>" in s.id and s.id not in self.reached:
                continue
            key = s.id.split(":", 1)[1]
            okey = key + ("" if key not in out else f"@{s.file}")
            out[okey] = {
                "module": self._module_of(s.file), "file": s.file, "line": s.line,
                "type": s.kind,
                "class": s.parent.split(":", 1)[1] if s.parent else None,
                "reachable": s.id in self.reached,
                # additive: discovered (every entry here) vs reachable vs reached only through dispatch
                "referenced": s.id in self.referenced,
                "dispatch_target": s.id in self.dispatch_targets,
                "reachability": self._reachability(s.id),
            }
            if self.framework_info and self.framework_info.get("active"):    # additive: named by configuration
                out[okey]["configured"] = s.id in self.arch_symbols
        return out

    def _reachability(self, sid):
        """direct | indirect (only via a dispatch edge) | referenced_only | unreached.  Possible call
        paths only: nothing here says a function actually executed."""
        if sid in self.reached:
            direct = any(t == sid and ty in ("CALLS", "INSTANTIATES") for (_, t, ty) in self.edges)
            dispatched = sid in self.dispatch_targets
            return "indirect" if dispatched and not direct and not self._is_entry_symbol(sid) else "direct"
        return "referenced_only" if sid in self.referenced else "unreached"

    def _is_entry_symbol(self, sid):
        info = self.entry_info or {}
        return info.get("kind") == "function" and info["sym"].id == sid

    def graph_json(self):
        edges = [dict(e) for e in self.edges.values()]
        for e in edges:
            src = self.symbols.get(e["source"])
            e["file"] = src.file if src else e.get("file", self.entry)
        return {"nodes": list(self.nodes.values()), "edges": edges}

    def _framework_files(self):
        fi = self.framework_info
        return set(fi["files"]) if fi and fi.get("active") else set()

    def architecture_json(self):
        arch = {}
        fw = self._framework_files()
        for rel in sorted(self.reached_files | fw):
            entry = {"module": self._module_of(rel), "classes": {}, "functions": {},
                     "imports": [{"alias": a, **i} for a, i in self.imports.get(rel, {}).items()]}
            if fw:                                   # additive, only when a framework analysis ran
                entry["execution_reached"] = rel in self.reached_files
                entry["discovered_via"] = ([VIA_EXECUTION] if rel in self.reached_files else []) + \
                    (self.framework_info["files"][rel]["discovered_via"] if rel in fw else [])
            for s in self.symbols.values():
                if s.file != rel or "<local>" in s.id:
                    continue
                if s.kind == "class":
                    entry["classes"][s.name] = {
                        "line": s.line,
                        "inherits": [e["target"] for e in self.edges.values()
                                     if e["source"] == s.id and e["type"] == "INHERITS"],
                        "methods": {m.name: {"line": m.line,
                                             "calls": [e["target"] for e in self.edges.values()
                                                       if e["source"] == m.id and e["type"] == "CALLS"]}
                                    for m in self.symbols.values() if m.parent == s.id}}
                elif s.kind == "function":
                    entry["functions"][s.name] = {"line": s.line,
                        "calls": [e["target"] for e in self.edges.values()
                                  if e["source"] == s.id and e["type"] == "CALLS"],
                        "dispatches": [{"target": e["target"], "via": e.get("via"),
                                        "conditions": e.get("conditions", []), "resolution": e.get("resolution")}
                                       for e in self.edges.values()
                                       if e["source"] == s.id and e["type"] == "DISPATCHES_TO"],
                        "references": [e["target"] for e in self.edges.values()
                                       if e["source"] == s.id and e["type"] == "REFERENCES"]}
            if rel in self.legacy_files:       # no AST symbols: report what the text scan recognised
                ti = self.text_info[rel]
                entry["analysis_mode"] = ANALYSIS_TEXT
                entry["classes"] = {d["name"]: {"line": d["line"], "inherits": [],
                                                "methods": {m["name"]: {"line": m["line"], "calls": []}
                                                            for m in ti["defs"] if m["parent"] == d["name"]}}
                                    for d in ti["defs"] if d["kind"] == "class"}
                entry["functions"] = {d["name"]: {"line": d["line"], "calls": []}
                                      for d in ti["defs"] if d["kind"] == "function"}
                if ti["main"]:
                    entry["main_block_line"] = ti["main"]["line"]
            arch[rel] = entry
        return arch

    # ------------------------------------------------------------------
    # Inline execution trace (source of executed code only, callees expanded
    # right under the line that calls them)
    # ------------------------------------------------------------------
    def _t(self, depth, file, line, text):
        self.trace.append(f"{'    ' * depth}{file}:{line:<4}| {text}")
        self.trace_entries.append((depth, file, line, text))

    def _stmt_lines(self, rel, stmt):
        src = self.sources[rel].splitlines()
        end = getattr(stmt, "end_lineno", stmt.lineno)
        return [(n, src[n - 1].strip()) for n in range(stmt.lineno, end + 1) if src[n - 1].strip()]

    def _calls_in(self, node):
        calls = []
        stack = [node]
        while stack:
            n = stack.pop()
            for c in ast.iter_child_nodes(n):
                if isinstance(c, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef, ast.Lambda)):
                    continue
                stack.append(c)
                if isinstance(c, ast.Call):
                    calls.append(c)
        if isinstance(node, ast.Call):
            calls.append(node)
        return sorted(calls, key=lambda c: (c.lineno, c.col_offset))

    def trace_body(self, stmts, scope, depth, active):
        for stmt in stmts:
            if isinstance(stmt, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                continue
            compound = isinstance(stmt, (ast.If, ast.While, ast.For, ast.AsyncFor, ast.With,
                                         ast.AsyncWith, ast.Try))
            if compound:
                first = stmt.body[0].lineno
                header_nodes = [getattr(stmt, "test", None), getattr(stmt, "iter", None)]
                for n, t in self._stmt_lines(scope.file, stmt):
                    if n < first:
                        self._t(depth, scope.file, n, t)
                for h in header_nodes:
                    if h is not None:
                        self._inline_calls(h, scope, depth, active)
                self.trace_body(stmt.body, scope, depth + 1, active)
                for h in getattr(stmt, "handlers", []):
                    self._t(depth, scope.file, h.lineno, self.sources[scope.file].splitlines()[h.lineno - 1].strip())
                    self.trace_body(h.body, scope, depth + 1, active)
                for extra in ("orelse", "finalbody"):
                    blk = getattr(stmt, extra, [])
                    if blk:
                        ln = blk[0].lineno - 1
                        self._t(depth, scope.file, ln, self.sources[scope.file].splitlines()[ln - 1].strip())
                        self.trace_body(blk, scope, depth + 1, active)
            else:
                for n, t in self._stmt_lines(scope.file, stmt):
                    self._t(depth, scope.file, n, t)
                self._inline_calls(stmt, scope, depth, active)
                if isinstance(stmt, ast.Assign) and isinstance(stmt.value, ast.Call):
                    t = self.resolve_expr(stmt.value, scope)
                    if t:
                        for tg in stmt.targets:
                            if isinstance(tg, ast.Name):
                                scope.vars[tg.id] = t
                    else:
                        self._bind_candidates(stmt.targets, stmt.value, scope)

    def _inline_calls(self, node, scope, depth, active):
        for call in self._calls_in(node):
            d = self.resolve_dispatch(call, scope)
            if d is not None:                              # indirect call: every possible target, once
                for sid in OrderedDict((e[1], None) for e in d["entries"]):
                    self._inline_target(self.symbols[sid], depth + 1, active)
                continue
            t = self.resolve_expr(call.func, scope)
            for t in ([t] if t else self.resolve_candidates(call.func, scope)):   # several possible values: all
                if t.kind == "symbol":
                    self._inline_target(self.symbols[t.ref], depth + 1, active)

    def _inline_target(self, sym, depth, active):
        """A class is entered through its __init__ (the class line is shown); anything else directly."""
        if sym.kind == "class":
            init = self.find_method(sym.id, "__init__")
            self._t(depth, sym.file, sym.line, self.sources[sym.file].splitlines()[sym.line - 1].strip())
            if not init:
                return
            sym = self.symbols[init]
        self._inline_symbol(sym, depth, active)

    def _inline_symbol(self, sym, depth, active):
        if sym.id in active:
            self._t(depth, sym.file, sym.line, f"(recursive call to {sym.name} - not re-entered)")
            return
        src = self.sources[sym.file].splitlines()
        self._t(depth, sym.file, sym.line, src[sym.line - 1].strip())
        if sym.id in self.trace_done:
            self._t(depth + 1, sym.file, sym.line, "(expanded above)")
            return
        self.trace_done.add(sym.id)
        scope = Scope(sym.file, sym.parent if sym.kind == "method" else None, sym.id)
        self._bind_local_imports(scope, sym)
        scope.bindings = self._function_bindings(sym)
        self._apply_param_hints(scope, sym)
        self.trace_body(sym.node.body, scope, depth + 1, active | {sym.id})

    def build_trace(self):
        info = self._ensure_entry()
        if info["kind"] == "function":              # root = the entry function's own `def` line + body
            self._inline_symbol(info["sym"], 0, set())
        elif info["kind"] == "legacy":              # text-based: original source lines, calls inlined by name
            self._legacy_trace(info)
        elif info["kind"] == "main_block":
            block = info["block"]
            scope = Scope(info["file"], None, info["owner"])
            self._t(0, info["file"], block.lineno, "if __name__ == \"__main__\":")
            self.trace_body(block.body, scope, 1, set())
        else:                                        # module-level execution; calls are inlined at the call site
            scope = Scope(info["file"], None, info["owner"])
            self._t(0, info["file"], info["line"], _FUNC_FILE_TOPLEVEL)
            self.trace_body(info["stmts"], scope, 1, set())
        return "\n".join(self.trace) + "\n"

    def _legacy_trace(self, info):
        file = info["file"]
        ti = self.text_info[file]
        head = info["header"]
        self._t(0, file, head if head else info["line"],
                ti["lines"][head - 1].strip() if head else _FUNC_FILE_TOPLEVEL)
        shown = {head} if info.get("inline") else set()      # `if __name__ == "__main__": main()` on ONE line
        self._legacy_trace_lines(file, info["lines"], 1, {info["owner"]}, shown)

    def _legacy_trace_lines(self, file, linenos, depth, active, already_shown=()):
        ti = self.text_info[file]
        for ln in linenos:
            if ln not in already_shown:
                self._t(depth, file, ln, ti["lines"][ln - 1].strip())
            for dotted in legacy_calls_on_line(ti, ln):
                kind, what = (self._legacy_resolve_call(file, dotted) or (None, None))
                if kind in ("local", "class"):
                    d = what if kind == "local" else self._legacy_init(file, what)
                    sid = f"{file}:{what['name']}"
                    self._t(depth + 1, file, what["line"], ti["lines"][what["line"] - 1].strip())
                    if sid in active:
                        self._t(depth + 2, file, what["line"], f"(recursive call to {what['name']} - not re-entered)")
                    elif sid in self.trace_done:
                        self._t(depth + 2, file, what["line"], "(expanded above)")
                    elif d is not None:
                        self.trace_done.add(sid)
                        self._legacy_trace_lines(file, legacy_code_lines(ti, d["line"] + 1, d["end"]),
                                                 depth + 2, active | {sid})
                elif kind == "target" and what.kind == "symbol":
                    sym = self.symbols[what.ref]
                    target = sym
                    if sym.kind == "class":
                        init = self.find_method(sym.id, "__init__")
                        self._t(depth + 1, sym.file, sym.line, self.sources[sym.file].splitlines()[sym.line - 1].strip())
                        if not init:
                            continue
                        target = self.symbols[init]
                    self._inline_symbol(target, depth + 1, set())

    # ------------------------------------------------------------------
    # Normalised result (schema: normalized.py) and the hooks app_broker calls.  No file is written here.
    # ------------------------------------------------------------------
    LANGUAGE = "Python"

    def normalized_result(self):
        """Python-specific results -> the shared schema.  Built once (it also builds the execution trace,
        after the graph / architecture data, exactly as the former write_outputs did)."""
        if self._normalized is not None:
            return self._normalized
        info = self._ensure_entry()
        fi = self.framework_info
        fw_files = self._framework_files()
        res = new_result(self.LANGUAGE, os.path.basename(self.root) or self.root, self.root,
                         {"file": self.entry, "label": self.entry_label, "kind": info["kind"],
                          "resolved_file": info["file"], "via": self._via_note(info) or None,
                          "reason": info.get("reason")})
        n_ast = len(self.files)
        res["analysis"].update(
            mode="text" if self.legacy_files and not n_ast else ("mixed" if self.legacy_files else "ast"),
            partial=bool(self.legacy_files or self.parse_errors or self.framework_error),
            text_files=sorted(self.legacy_files),
            parse_errors=[{"file": f, "error": e} for f, e in self.parse_errors],
            notes=[f"{f}: ast could not parse ({why})" for f, why in sorted(self.legacy_reasons.items())]
                  + ([f"framework analysis failed: {self.framework_error}"] if self.framework_error else []))
        for rel in sorted(self.reached_files | fw_files):
            f = {"path": rel, "module": self._module_of(rel), "reached": rel in self.reached_files,
                 "analysis_mode": ANALYSIS_TEXT if rel in self.legacy_files else ANALYSIS_AST}
            if fw_files:
                f["execution_reached"] = rel in self.reached_files
                f["discovered_via"] = ([VIA_EXECUTION] if rel in self.reached_files else []) + \
                    (fi["files"][rel]["discovered_via"] if rel in fw_files else [])
            if rel in self.legacy_files:
                ti = self.text_info[rel]
                f["text_definitions"] = [{"name": d["name"], "kind": d["kind"], "line": d["line"],
                                         "parent": d["parent"], "confidence": "low"} for d in ti["defs"]]
                if ti["main"]:
                    f["main_block_line"] = ti["main"]["line"]
            res["files"].append(f)
        configured = bool(fi and fi.get("active"))
        for s in self.symbols.values():
            d = {"id": s.id, "kind": s.kind, "name": s.name, "file": s.file, "line": s.line, "parent": s.parent,
                 "module": self._module_of(s.file), "scope": "local" if "<local>" in s.id else "module",
                 "reachable": s.id in self.reached, "referenced": s.id in self.referenced,
                 "dispatch_target": s.id in self.dispatch_targets, "reachability": self._reachability(s.id),
                 "confidence": "high"}
            if configured:
                d["configured"] = s.id in self.arch_symbols
            res["symbols"].append(d)
        for rel, table in self.imports.items():
            res["imports"] = res.get("imports", []) + [{"file": rel, "alias": a, **i} for a, i in table.items()]
        for e in self.edges.values():
            src = self.symbols.get(e["source"])
            res["relationships"].append({
                "source": e["source"], "target": e["target"], "type": e["type"],
                "origin": "framework" if e["type"] in ARCHITECTURE_EDGE_TYPES else "static",
                "line": e.get("line"), "file": src.file if src else e.get("file", self.entry),
                "attributes": {k: v for k, v in e.items() if k not in ("source", "target", "type", "line")}})
        res["nodes"] = [dict(n) for n in self.nodes.values()]
        res["execution_tree"] = self.tree_root["children"]
        res["dependencies"] = [{"module": m, "category": cat, "references": sorted(lbl)}
                               for cat, tbl in (("external", self.external_calls), ("stdlib", self.stdlib_calls),
                                                ("missing", self.missing_calls)) for m, lbl in sorted(tbl.items())]
        res["unresolved"] = [{"file": f, "line": l, "reference": r, "reason": why}
                             for (f, l, r), why in self.unresolved.items()]
        if fi is not None:
            res["framework"] = {"name": fi.get("framework"), "active": bool(fi.get("active")), "document": fi}
        res["extensions"] = {"python": {
            "internal_hints": sorted(self.internal_hints),
            "fallback_resolutions": [{"module": m, "from": f, "target": t}
                                     for (m, f), t in sorted(self.fallback_resolutions.items())]}}
        self.build_trace()                      # built exactly once (appends to self.trace / self.trace_entries)
        res["trace"] = {"entries": [{"depth": d, "file": f, "line": l, "text": t} for d, f, l, t in self.trace_entries],
                        "call_categories": [{"file": f, "line": l, "category": k}
                                            for (f, l), k in self.call_sites.items()]}
        # complete source inventory: separate from (and not limited to) the execution trace above
        res["extensions"]["python"]["source_inventory"] = self.source_inventory()
        self._normalized = res
        return res

    def attach_trace_tree(self, root, stats):
        """app_broker built the trace tree from the normalised trace; the Python analyses reuse it."""
        self.trace_tree_root, self.trace_tree_stats = root, stats

    def functionality_document(self):
        self.analyze_functionalities(self.trace_tree_root)
        return self.functionality_json()

    def topdown_document(self):
        if self.entry.endswith((".py", ".toml")) and self._declared_entry_points():
            # a descriptor with declared entries: ALL of them hang below it (ROOT -> setup.py -> entries)
            result = build_setup_hierarchy(self.root, self.entry, self.internal_hints, broker=self)
        else:
            result = extract_topdown_functionalities(
                self.trace_tree_root, project=os.path.basename(self.root) or self.root, entry_point=self.entry_label)
        self.topdown_result = result
        return {"result": result, "text": render_topdown_text(result)}

    @staticmethod
    def topdown_from_trace(doc):
        """``--from-trace``: top-down extraction from an existing trace_tree.json document (no repository analysis)."""
        result = extract_topdown_functionalities(doc["root"], project=doc.get("project", ""),
                                                 entry_point=doc.get("entry_point", ""))
        return {"result": result, "text": render_topdown_text(result)}

    def report_text(self):
        return self.report()

    # ------------------------------------------------------------------
    # Functionality extraction: trace tree -> functionality.json
    # ------------------------------------------------------------------
    @staticmethod
    def _is_def_node(n):
        return n.get("type") == "code" and re.match(r"^(?:async\s+)?def\s", n.get("code", "")) is not None

    @staticmethod
    def _is_class_node(n):
        return n.get("type") == "code" and re.match(r"^class\s", n.get("code", "")) is not None

    @staticmethod
    def _label(n):
        """Readable label for a trace node in a backtracked path (def -> name, header -> no colon)."""
        code = n.get("code", "")
        m = re.match(r"^(?:async\s+)?def\s+(\w+)", code)
        if m:
            return m.group(1)
        return code[:-1].rstrip() if code.endswith(":") else code

    def _sym_by_location(self):
        if getattr(self, "_sym_loc", None) is None:
            self._sym_loc = {}
            for s in self.symbols.values():
                if s.kind in ("function", "method"):
                    self._sym_loc[(s.file, s.line)] = s
        return self._sym_loc

    def _qualified_name(self, sym, code):
        if sym is not None:
            if ".<local>" in sym.id:
                outer = sym.id.split(".<local>")[0].split(":", 1)[1]
                return f"{outer}.<locals>.{sym.name}"
            if sym.kind == "method" and sym.parent:
                return f"{sym.parent.split(':', 1)[1]}.{sym.name}"
            return sym.name
        m = re.match(r"^(?:async\s+)?def\s+(\w+)", code)
        return m.group(1) if m else code

    def _fa_index(self, file):
        """line -> grouping key, so multi-line statements / headers are treated as ONE unit."""
        cache = self.__dict__.setdefault("_fa_cache", {})
        if file in cache:
            return cache[file]
        idx = {}
        tree = self.files.get(file)
        if tree is not None:
            for n in ast.walk(tree):
                if isinstance(n, ast.ExceptHandler):
                    idx[n.lineno] = (file, n.lineno, "hdr")
                elif isinstance(n, ast.stmt):
                    end = getattr(n, "end_lineno", n.lineno)
                    body = getattr(n, "body", None)
                    if isinstance(n, (ast.FunctionDef, ast.AsyncFunctionDef, ast.ClassDef)):
                        continue
                    if isinstance(body, list) and body and isinstance(body[0], ast.stmt):
                        for ln in range(n.lineno, body[0].lineno):       # compound header lines
                            idx.setdefault(ln, (file, n.lineno, "hdr"))
                    else:
                        for ln in range(n.lineno, end + 1):              # simple statement lines
                            idx[ln] = (file, n.lineno, "stmt")
        cache[file] = idx
        return idx

    # ---- A. function registry -------------------------------------------------
    def extract_function_registry(self, trace_root):
        """One FUNC id per definition (file+line); one OCC id per place a function appears.

        The trace root itself is the pseudo-function of the resolved entry (<__main__> for the
        `__main__` block, <top-level execution> for module-level code, <entry> for a function resolved
        from an explicit entry declaration such as console_scripts)."""
        self._fa_funcs = OrderedDict()        # (file,line,kind) -> function record
        self._fa_occs = []                    # occurrence records, DFS order
        self._fa_occ_of_node = {}             # id(def node) -> occurrence record
        sym_loc = self._sym_by_location()

        def func_for(node, prev=None):
            key = (node["file"], node["line"])
            if key not in self._fa_funcs:
                sym = sym_loc.get(key)
                fid = f"FUNC_{len(self._fa_funcs) + 1:06d}"
                qn = self._qualified_name(sym, node["code"])
                if sym is None and prev is not None and self._is_class_node(prev):   # no symbol table: class line precedes def
                    cm = re.match(r"^class\s+(\w+)", prev["code"])
                    qn = f"{cm.group(1)}.{qn}" if cm else qn
                self._fa_funcs[key] = dict(
                    function_id=fid, qualified_name=qn,
                    file=node["file"], line=node["line"], symbol_id=sym.id if sym else None,
                    kind=(sym.kind if sym else "function"),
                    end_line=getattr(getattr(sym, "node", None), "end_lineno", None), _node=node)
            return self._fa_funcs[key]

        # pseudo entry function
        first = trace_root["children"][0] if trace_root["children"] else None
        info = self._ensure_entry()
        efile, eline = (first["file"], first["line"]) if first else (info["file"], 0)
        entry = dict(function_id="FUNC_000001", qualified_name=info["pseudo"], file=efile, line=eline,
                     symbol_id=f"{info['file']}:{info['pseudo']}", kind="entry", end_line=None, _node=trace_root)
        self._fa_funcs[(efile, eline, "entry")] = entry

        def new_occ(func, node, parent_occ, call_node, kind):
            path = (parent_occ["execution_path"] if parent_occ else []) + [func["qualified_name"]]
            occ = dict(occurrence_id=f"OCC_{len(self._fa_occs) + 1:06d}", function_id=func["function_id"],
                       kind=kind, node_id=node.get("id"), _node=node, parent=parent_occ,
                       caller=parent_occ["function_name"] if parent_occ else None,
                       caller_function_id=parent_occ["function_id"] if parent_occ else None,
                       call_line=call_node.get("line") if call_node else None,
                       call_file=call_node.get("file") if call_node else None,
                       function_name=func["qualified_name"], execution_path=path)
            self._fa_occs.append(occ)
            return occ

        root_occ = new_occ(entry, trace_root, None, None, "entry")
        self._fa_occ_of_node[id(trace_root)] = root_occ

        def walk(node, occ):
            prev = None
            for ch in node["children"]:
                if self._is_def_node(ch):
                    func = func_for(ch, prev)
                    refs = ch.get("references", [])
                    kind = "expanded" if ch["children"] else (
                        "repeat" if any(r["status"] == "expanded_above" for r in refs) else "expanded")
                    o = new_occ(func, ch, occ, node, kind)
                    self._fa_occ_of_node[id(ch)] = o
                    walk(ch, o)
                else:
                    for r in ch.get("references", []):
                        if r["status"] == "recursive_call":
                            f, l = r["target"].rsplit(":", 1)
                            fn = self._fa_funcs.get((f, int(l)))
                            if fn:
                                self._fa_occs.append(dict(
                                    occurrence_id=f"OCC_{len(self._fa_occs) + 1:06d}", function_id=fn["function_id"],
                                    kind="recursive_reference", node_id=ch.get("id"), _node=ch, parent=occ,
                                    caller=occ["function_name"], caller_function_id=occ["function_id"],
                                    call_line=ch.get("line"), call_file=ch.get("file"),
                                    function_name=fn["qualified_name"],
                                    execution_path=occ["execution_path"] + [fn["qualified_name"]]))
                    walk(ch, occ)
                prev = ch

        walk(trace_root, root_occ)
        return self._fa_funcs

    # ---- B. leaf backtracking ---------------------------------------------------
    def backtrack_leaf(self, leaf, ancestors):
        """Complete root->leaf path for one leaf (ancestors = code nodes above it, root excluded)."""
        owner = None
        for a in reversed(ancestors):
            if id(a) in self._fa_occ_of_node:
                owner = self._fa_occ_of_node[id(a)]
                break
        owner = owner or self._fa_occ_of_node[id(self._fa_trace_root)]
        if self._is_def_node(leaf):
            kind = "reference_only_function"       # def line whose body is '(expanded above)'
        elif self._is_class_node(leaf):
            kind = "class_declaration"
        else:
            kind = "operation"
        path = ancestors + [leaf]
        return dict(leaf_id=leaf["id"], kind=kind, file=leaf["file"], line=leaf["line"], code=leaf["code"],
                    path=[(self._fa_occ_of_node[id(n)]["function_name"] if id(n) in self._fa_occ_of_node
                           else self._label(n)) for n in path],
                    node_path=[n["id"] for n in path],
                    execution_path=owner["execution_path"], occurrence_id=owner["occurrence_id"],
                    function_id=owner["function_id"])

    def backtrack_all_leaves(self, trace_root):
        out, stack = [], [(c, []) for c in reversed(trace_root["children"])]
        while stack:
            node, anc = stack.pop()
            if not node["children"]:
                out.append(self.backtrack_leaf(node, anc))
            else:
                for c in reversed(node["children"]):
                    stack.append((c, anc + [node]))
        out.sort(key=lambda r: r["leaf_id"])
        return out

    # ---- C. grouping of leaves into functionality units ---------------------------
    def _units(self, nodes):
        """Merge consecutive sibling trace lines belonging to one statement / header (AST-based)."""
        units = []
        for n in nodes:
            if self._is_def_node(n):
                units.append(dict(kind="def", nodes=[n]))
                continue
            key = self._fa_index(n["file"]).get(n["line"]) if n.get("type") == "code" else None
            if key and units and units[-1].get("key") == key and units[-1]["kind"] != "def":
                units[-1]["nodes"].append(n)
            else:
                units.append(dict(kind="other", key=key, nodes=[n]))
        return units

    def group_leaf_functionalities(self, occ):
        """Aggregate every operation of ONE function execution into a single functionality unit body."""
        func_body = occ["_node"]
        ops, branches, headers = OrderedDict(), OrderedDict(), []
        callees = []                                   # [(function_id, qualified, call_text, line)]
        state = dict(seq=0)

        def ctx_key(ctx):
            return tuple((c["kind"], c["condition"]) for c in ctx)

        def branch_for(ctx):
            k = ctx_key(ctx)
            if k not in branches:
                branches[k] = dict(control=[dict(kind=c["kind"], condition=c["condition"]) for c in ctx]
                                   or [dict(kind="sequence", condition=None)], operations=[])
            return branches[k]

        def visit(nodes, ctx):
            chain = []                                  # preceding if/elif conditions (for else)
            for u in self._units(nodes):
                if u["kind"] == "def":
                    continue                            # callee: handled through the call unit below
                first = u["nodes"][0]
                text = " ".join(n["code"] for n in u["nodes"])
                kids = [c for n in u["nodes"] for c in n["children"]]
                defs = [c for c in kids if self._is_def_node(c)]
                rest = [c for c in kids if not self._is_def_node(c)]
                m = _CONTROL_RE.match(text)
                call_info = []
                for d in defs:
                    o = self._fa_occ_of_node.get(id(d))
                    if o:
                        call_info.append(o)
                        callees.append((o["function_id"], o["function_name"], text, first["line"]))
                if m:
                    kw = m.group(1)
                    body = text[m.end():].rstrip().rstrip(":").strip()
                    if kw in ("if", "elif"):
                        cond = body
                    elif kw == "else":
                        prev = [f"not {c}" if re.match(r"^[\w.]+$", c) else f"not ({c})" for c in chain]
                        cond = " and ".join(prev) if prev else "else"
                    elif kw == "except":
                        cond = f"except {body}" if body else "except"
                    else:
                        cond = body or kw
                    if kw == "if":
                        chain = [cond]
                    elif kw == "elif":
                        chain = chain + [cond]
                    else:
                        chain = []
                    a = _analyze_op_text(text)
                    headers.append(dict(kind=kw, condition=cond, analysis=a, calls_internal=call_info,
                                        node_ids=[n["id"] for n in u["nodes"]]))
                    branch_for(ctx + [dict(kind=kw, condition=cond)])
                    visit(rest, ctx + [dict(kind=kw, condition=cond)])
                    continue
                chain = []
                if self._is_class_node(first):
                    continue                            # class line: structural, not behaviour
                key = (first["file"], u["key"][1] if u["key"] else first["line"], u["key"][2] if u["key"] else "")
                if key in ops:                          # same source statement seen again: add evidence only
                    ops[key]["node_ids"].extend(n["id"] for n in u["nodes"])
                else:
                    state["seq"] += 1
                    ops[key] = dict(text=text, file=first["file"], start_line=first["line"],
                                    end_line=u["nodes"][-1]["line"], node_ids=[n["id"] for n in u["nodes"]],
                                    analysis=_analyze_op_text(text), callees=call_info,
                                    kind="call" if call_info else "leaf", ctx=list(ctx))
                    branch_for(ctx)["operations"].append(key)
                if rest:                                # non-def children of a plain statement: same context
                    visit(rest, ctx)

        visit(func_body["children"], [])
        return dict(ops=ops, branches=branches, headers=headers, callees=callees)

    # ---- signature / classification ----------------------------------------------
    def _canonical_api(self, dotted, file):
        """Canonical API name when the call is rooted in an external/stdlib import or a builtin, else None."""
        root = re.split(r"[.\[(]", dotted, 1)[0]
        info = self.imports.get(file, {}).get(root)
        if info:
            kind, _ = self.classify_module(info["module"], info["level"], file)
            if kind in ("external", "stdlib"):
                rest = dotted[len(root):]
                if info["name"]:
                    return f"{info['module']}.{info['name']}{rest}"
                return f"{info['module']}{rest}"
            return None
        if root in _BUILTIN_NAMES and root == dotted.split("(")[0] and root not in ("self", "cls"):
            return f"builtins.{dotted}"
        return None

    def build_signature(self, func, body):
        apis, method_calls, internal_calls, reads, writes, returns = [], [], [], [], [], []
        flow = ["sequence"]
        callee_short = {q.split(".")[-1] for _, q, _, _ in body["callees"]} | \
                       {q.split(".")[0] for _, q, _, _ in body["callees"]}

        def absorb(a, file):
            for c in a["calls"]:
                last = re.split(r"[.]", c)[-1].rstrip("()[]")
                if last in callee_short or c.split(".")[0] in callee_short:
                    continue
                api = self._canonical_api(c, file)
                (apis if api else method_calls).append(api or c)
            reads.extend(a["reads"])
            writes.extend(a["writes"])

        for op in body["ops"].values():
            absorb(op["analysis"], op["file"])
            if op["analysis"]["returns"]:
                returns.append(op["text"][:120])
        for h in body["headers"]:
            absorb(h["analysis"], func["file"])
            if h["kind"] not in flow:
                flow.append(h["kind"])
        calls = _uniq(q for _, q, _, _ in body["callees"])
        wset = set(writes)
        reads = [r for r in _uniq(reads) if r not in wset or r.startswith("self.")]
        apis, method_calls = _uniq(apis), _uniq(method_calls)
        return dict(operations=[o["text"] for o in body["ops"].values()], apis=apis, calls=calls,
                    method_calls=method_calls, reads=reads, writes=_uniq(writes), returns=_uniq(returns),
                    control_flow=flow)

    def classify_functionality(self, func, sig, callee_clusters=()):
        meth = {c.split(".")[-1].rstrip("()[]") for c in sig["method_calls"]} | \
               {a.split(".")[-1] for a in sig["apis"]}
        name_tok = _split_words(func["qualified_name"])
        attr_tok = set()
        for a in sig["reads"] + sig["writes"]:
            attr_tok |= _split_words(a)
        feat = dict(method_names=meth, attr_token_set=attr_tok)
        passing = []
        for r in FUNCTIONALITY_RULES:
            api_hits = {a for a in sig["apis"] if any(a == p or a.startswith(p) for p in r["apis"])}
            if any(not any(a.startswith(p) for a in sig["apis"]) for p in r.get("require_apis_all", ())):
                continue
            if r.get("require_tokens_any") and not (name_tok & r["require_tokens_any"]):
                continue
            if r.get("evidence_attr") and func["qualified_name"].endswith(".__init__"):
                continue                                # constructors initialise state; attribute words alone don't classify them
            m_hits = meth & r["methods"]
            c_hits = set(callee_clusters) & r.get("callee_clusters", set())
            t_hits = name_tok & r["tokens"]
            at_hits = attr_tok & r.get("attr_tokens", set())
            evidence_score = 2.0 * len(api_hits) + 1.5 * len(m_hits) + 1.5 * len(c_hits)
            if r.get("evidence_attr"):
                evidence_score += 1.5 * len(at_hits)
            if evidence_score == 0:
                continue                                # names/attribute words alone never classify
            score = evidence_score + 1.0 * len(t_hits) + (0.0 if r.get("evidence_attr") else 0.5 * len(at_hits))
            if score >= _RULE_THRESHOLD:
                passing.append((score, r, dict(apis=sorted(api_hits), methods=sorted(m_hits),
                                               callee_clusters=sorted(c_hits), name_tokens=sorted(t_hits),
                                               attr_tokens=sorted(at_hits))))
        best = None
        if passing:
            passing.sort(key=lambda p: -p[0])           # stable: earlier rule wins ties
            best = passing[0]
        if best:
            score, r, ev = best
            alts = [dict(rule=p[1]["id"], cluster=p[1]["cluster"], score=round(p[0], 2))
                    for p in passing[1:] if p[1]["cluster"] != r["cluster"] and p[0] >= 0.6 * score][:3]
            name = r["name"](feat) if callable(r["name"]) else r["name"]
            conf = "high" if score >= 4 else "medium"
            if alts:
                conf = "mixed"                          # evidence from several domains: primary is a best guess
            return dict(rule=r["id"], cluster=r["cluster"], name=name, score=round(score, 2),
                        confidence=conf, evidence=ev, alternatives=alts)
        # structural, signature-based fallbacks (conservative)
        short = func["qualified_name"].split(".")[-1]
        non_builtin = [a for a in sig["apis"] if not a.startswith("builtins.")]
        if non_builtin:
            pkg = non_builtin[0].split(".")[0]
            return dict(rule="fallback.api", cluster=f"MISC.API.{pkg}", score=0.0, confidence="low",
                        name=f"operations via {pkg} API (no specific semantic rule matched)", evidence=dict(apis=non_builtin[:6]), alternatives=[])
        if short == "__init__" and sig["writes"]:
            cls = func["qualified_name"].split(".")[0]
            return dict(rule="fallback.init", cluster="STATE.INIT", score=0.0, confidence="medium",
                        name=f"{cls} state initialisation", evidence=dict(writes=sig["writes"][:6]), alternatives=[])
        if sig["calls"] and not sig["writes"]:
            return dict(rule="fallback.orchestration", cluster="ORCHESTRATION", score=0.0, confidence="low",
                        name="coordination of: " + ", ".join(sig["calls"][:4]), evidence=dict(calls=sig["calls"][:6]), alternatives=[])
        return dict(rule="fallback.none", cluster="UNCLASSIFIED", score=0.0, confidence="low",
                    name=f"unclassified behaviour of {func['qualified_name']}", evidence={}, alternatives=[])

    def _describe(self, func, sig, cls, body):
        parts = [f"{func['qualified_name']} ({func['file']}:{func['line']}) executes "
                 f"{len(body['ops'])} operation(s) in the traced run"]
        if sig["calls"]:
            parts.append("calls " + ", ".join(sig["calls"][:5]))
        if sig["apis"]:
            parts.append("uses APIs " + ", ".join(sig["apis"][:5]))
        if sig["writes"]:
            parts.append("writes " + ", ".join(sig["writes"][:5]))
        if sig["returns"]:
            parts.append("returns a value")
        parts.append(f"control flow: {', '.join(sig['control_flow'])}")
        if cls["confidence"] == "low":
            parts.append("semantic classification is tentative")
        if cls.get("alternatives"):
            parts.append("also shows evidence of: " + ", ".join(a["cluster"] for a in cls["alternatives"]))
        return "; ".join(parts) + "."

    # ---- orchestration -----------------------------------------------------------
    def analyze_functionalities(self, trace_root):
        """Consumes the in-memory trace tree (no re-parsing of expanded_trace.txt)."""
        self._fa_trace_root = trace_root
        self._fa_cache = {}
        self.extract_function_registry(trace_root)
        funcs = list(self._fa_funcs.values())
        by_id = {f["function_id"]: f for f in funcs}

        leaves = self.backtrack_all_leaves(trace_root)

        # one functionality unit per function, built from its (single) fully expanded occurrence
        bodies = {}
        for o in self._fa_occs:
            if o["kind"] in ("expanded", "entry") and o["function_id"] not in bodies:
                bodies[o["function_id"]] = (o, self.group_leaf_functionalities(o))
        units = OrderedDict()
        for fid, (occ, body) in bodies.items():
            f = by_id[fid]
            sig = self.build_signature(f, body)
            units[fid] = dict(func=f, occ=occ, body=body, signature=sig, cls=None)

        # classification: pass 1 on own evidence, then propagate callee clusters to unclassified ones
        for u in units.values():
            u["cls"] = self.classify_functionality(u["func"], u["signature"])
        for _ in range(3):
            changed = False
            for u in units.values():
                if u["cls"]["rule"].startswith("fallback"):
                    cc = {units[c[0]]["cls"]["cluster"] for c in u["body"]["callees"] if c[0] in units}
                    new = self.classify_functionality(u["func"], u["signature"], cc)
                    if not new["rule"].startswith("fallback"):
                        u["cls"], changed = new, True
            if not changed:
                break

        # assemble records
        occ_by_func = defaultdict(list)
        for o in self._fa_occs:
            occ_by_func[o["function_id"]].append(o)
        node_to_op = {}
        self._fa_all_ops = []
        functionalities = []
        for n, (fid, u) in enumerate(units.items(), 1):
            f, body, sig, cls = u["func"], u["body"], u["signature"], u["cls"]
            fn_id = f"F_{n:06d}"
            op_id_of = {}
            op_details = []
            for key, op in body["ops"].items():
                oid = f"OP_{len(self._fa_all_ops) + 1:06d}"
                self._fa_all_ops.append(oid)
                op_id_of[key] = oid
                for nid in op["node_ids"]:
                    node_to_op[nid] = (fn_id, oid)
                op_details.append(dict(
                    operation_id=oid, kind=op["kind"], text=op["text"], file=op["file"],
                    start_line=op["start_line"], end_line=op["end_line"], node_ids=op["node_ids"],
                    control=[dict(kind=c["kind"], condition=c["condition"]) for c in op["ctx"]] or
                            [dict(kind="sequence", condition=None)],
                    callees=[c["function_id"] for c in op["callees"]]))
            branches = []
            for i, (k, b) in enumerate(body["branches"].items(), 1):
                branches.append(dict(branch_id=f"B_{i:03d}", control=b["control"],
                                     condition=" > ".join(c["condition"] for c in b["control"] if c["condition"]) or None,
                                     operations=[body["ops"][x]["text"] for x in b["operations"]],
                                     operation_ids=[op_id_of[x] for x in b["operations"]]))
            end = f.get("end_line") or max([o["end_line"] for o in body["ops"].values()] or [f["line"]])
            leaf_ids = [nid for op in body["ops"].values() if op["kind"] == "leaf" for nid in op["node_ids"]]
            occs = []
            for o in occ_by_func[fid]:
                occs.append(dict(
                    occurrence_id=o["occurrence_id"], kind=o["kind"], caller=o["caller"],
                    caller_function_id=o["caller_function_id"], call_line=o["call_line"],
                    call_file=o["call_file"], execution_path=o["execution_path"],
                    leaf_nodes=leaf_ids if o is u["occ"] else []))
            functionalities.append(OrderedDict([
                ("functionality_id", fn_id), ("function_id", fid),
                ("name", cls["name"]), ("description", self._describe(f, sig, cls, body)),
                ("source", dict(file=f["file"], start_line=f["line"], end_line=end)),
                ("operations", sig["operations"]), ("operation_details", op_details),
                ("branches", branches),
                ("signature", dict(operations=_uniq(sig["apis"] + sig["method_calls"]),
                                   apis=sig["apis"], calls=sig["calls"], method_calls=sig["method_calls"],
                                   reads=sig["reads"], writes=sig["writes"], returns=sig["returns"],
                                   control_flow=sig["control_flow"])),
                ("classification", dict(rule=cls["rule"], score=cls["score"], confidence=cls["confidence"],
                                        evidence=cls["evidence"], alternatives=cls.get("alternatives", []))),
                ("execution_occurrences", occs), ("cluster_id", cls["cluster"]),
            ]))
        fn_of_func = {x["function_id"]: x["functionality_id"] for x in functionalities}

        for lf in leaves:                                  # link leaves to functionality / operation
            lf["functionality_id"] = fn_of_func.get(lf["function_id"])
            if lf["leaf_id"] in node_to_op:
                lf["functionality_id"], lf["operation_id"] = node_to_op[lf["leaf_id"]]

        self.build_functionality_evidence(functionalities, by_id)
        clusters = self.build_functionality_clusters(functionalities)
        self._fa_result = dict(funcs=funcs, occs=occ_by_func, functionalities=functionalities,
                               clusters=clusters, leaves=leaves)
        stats = OrderedDict([
            ("functions", len(funcs)), ("functionality_units", len(functionalities)),
            ("leaf_nodes", len(leaves)), ("execution_occurrences", len(self._fa_occs)),
            ("clusters", len(clusters)),
            ("expanded_occurrences", sum(1 for o in self._fa_occs if o["kind"] in ("expanded", "entry"))),
            ("repeat_occurrences", sum(1 for o in self._fa_occs if o["kind"] == "repeat")),
            ("operations", len(self._fa_all_ops))])
        self.functionality_stats = stats
        print("PATCHPLUS FUNCTIONALITY EXTRACTION")
        print("----------------------------------")
        for k, v in stats.items():
            print(f"{k.replace('_', ' ').capitalize():<22}: {v}")
        return self._fa_result

    def build_functionality_evidence(self, functionalities, by_id):
        """Neutral evidence for the NEXT stage. Nothing here labels code dead/redundant/unneeded."""
        def sigset(x):
            s = x["signature"]
            return set(s["apis"]) | {m.split(".")[-1] for m in s["method_calls"]}
        def sighash(x):
            s = x["signature"]
            payload = json.dumps([sorted(s["apis"]), sorted({m.split(".")[-1] for m in s["method_calls"]}),
                                  sorted(s["control_flow"])])
            return hashlib.sha1(payload.encode()).hexdigest()[:12]
        hashes = {x["functionality_id"]: sighash(x) for x in functionalities}
        sets = {x["functionality_id"]: sigset(x) for x in functionalities}
        callers = defaultdict(set)
        for x in functionalities:
            for o in x["execution_occurrences"]:
                if o["caller_function_id"]:
                    callers[x["function_id"]].add(o["caller_function_id"])
        for x in functionalities:
            fid = x["functionality_id"]
            occs = x["execution_occurrences"]
            similar = []
            for y in functionalities:
                if y is x:
                    continue
                a, b = sets[fid], sets[y["functionality_id"]]
                if a and b:
                    j = len(a & b) / len(a | b)
                    if j >= 0.6 or hashes[fid] == hashes[y["functionality_id"]]:
                        similar.append(dict(functionality_id=y["functionality_id"], function_id=y["function_id"],
                                            similarity=round(j, 2),
                                            same_signature_hash=hashes[fid] == hashes[y["functionality_id"]]))
            x["evidence"] = dict(
                signature_hash=hashes[fid], occurrence_count=len(occs),
                repeat_occurrences=sum(1 for o in occs if o["kind"] == "repeat"),
                distinct_callers=sorted(callers[x["function_id"]]),
                call_lines=sorted({(o["call_file"], o["call_line"]) for o in occs if o["call_line"]}),
                similar_functionalities=similar,
                calls_functions=sorted({c for od in x["operation_details"] for c in od["callees"]}))

    def build_functionality_clusters(self, functionalities):
        """Preliminary clustering from classification of the SIGNATURE (extensible via the rule table)."""
        groups = OrderedDict()
        for x in functionalities:
            groups.setdefault(x["cluster_id"], []).append(x)
        out = []
        for cid, xs in groups.items():
            name = CLUSTER_TAXONOMY.get(cid) or (f"Operations via {cid.split('.', 2)[-1]} API"
                                                 if cid.startswith("MISC.API.") else cid)
            out.append(OrderedDict([
                ("cluster_id", cid), ("name", name),
                ("functionalities", [x["functionality_id"] for x in xs]),
                ("signature_summary", dict(
                    apis=sorted({a for x in xs for a in x["signature"]["apis"]}),
                    rules=sorted({x["classification"]["rule"] for x in xs}))),
            ]))
        return out

    def functionality_json(self):
        r = getattr(self, "_fa_result", None)
        if r is None:
            raise RuntimeError("analyze_functionalities() has not been run")
        functions = []
        for f in r["funcs"]:
            occs = r["occs"].get(f["function_id"], [])
            functions.append(OrderedDict([
                ("function_id", f["function_id"]), ("qualified_name", f["qualified_name"]),
                ("file", f["file"]), ("line", f["line"]), ("end_line", f.get("end_line")),
                ("kind", f["kind"]), ("symbol_id", f["symbol_id"]),
                ("occurrences", [dict(occurrence_id=o["occurrence_id"], kind=o["kind"], caller=o["caller"],
                                      caller_function_id=o["caller_function_id"], call_line=o["call_line"],
                                      execution_path=o["execution_path"]) for o in occs]),
            ]))
        evidence = {}
        if self.symbols:
            traced = {f["symbol_id"] for f in r["funcs"] if f["symbol_id"]}
            evidence["indexed_functions_not_observed_in_trace"] = sorted(
                s.id for s in self.symbols.values() if s.kind in ("function", "method") and s.id not in traced)
        return OrderedDict([
            ("project", os.path.basename(self.root) or self.root), ("entry_point", self.entry_label),
            ("statistics", self.functionality_stats),
            ("functions", functions), ("functionalities", r["functionalities"]),
            ("clusters", r["clusters"]), ("leaf_backtracks", r["leaves"]),
            ("evidence", evidence),
        ])

    # ------------------------------------------------------------------
    # Report
    # ------------------------------------------------------------------
    def report(self):
        o = []
        bar = "=" * 78
        sub = "-" * 78
        o += [bar, "PATCHPLUS APP BROKER - EXECUTION MAP", bar,
              f"Generated     : {datetime.now().isoformat(timespec='seconds')}",
              f"Project root  : {self.root}",
              f"Entry point   : {self.entry_label}" + (f"  [{self.entry_info['kind']}]" if (self.entry_info or {}).get("kind") not in (None, "main_block") else ""),
              *([f"Analysis mode : text-based (lower confidence) - ast could not parse {self.entry_info['file']}: "
                 f"{self.entry_info['reason']}"] if (self.entry_info or {}).get("kind") == "legacy" else []),
              *self._entry_report_lines(),
              f"Internal hints: {', '.join(sorted(self.internal_hints)) or '(none)'}",
              f"Files indexed : {len(self.files)}  ({', '.join(sorted(self.files))})", ""]
        if self.legacy_files:
            o.append(f"Legacy files  : {len(self.legacy_files)} analysed as text (lower confidence): "
                     f"{', '.join(sorted(self.legacy_files))}")
        if self.parse_errors:
            o.append("Parse errors: " + "; ".join(f"{f}: {e}" for f, e in self.parse_errors))
        if self.fallback_resolutions:
            o.append("Note: these imports were resolved by file-name fallback (flat layout):")
            for (m, f), t in sorted(self.fallback_resolutions.items()):
                o.append(f"   {m}  (from {f})  ->  {t}")
            o.append("")

        by_type = defaultdict(int)
        for e in self.edges.values():
            by_type[e["type"]] += 1
        o += [bar, "1. SUMMARY", bar,
              f"Reachable symbols     : {len(self.reached)}",
              f"Reachable files       : {len(self.reached_files)}",
              f"Graph nodes / edges   : {len(self.nodes)} / {len(self.edges)}",
              "Edges by type         : " + ", ".join(f"{k}={v}" for k, v in sorted(by_type.items())),
              f"External libraries    : {', '.join(sorted(self.external_calls)) or '(none)'}",
              f"Stdlib modules used   : {', '.join(sorted(self.stdlib_calls)) or '(none)'}",
              f"Missing internal refs : {', '.join(sorted(self.missing_calls)) or '(none)'}", ""]

        o += [bar, "2. EXECUTION TREE (from entry point)", bar,
              "Legend: CALLS / INSTANTIATES / INHERITS = followed internally",
              "        [EXTERNAL]/[STDLIB] = traversal stops   [MISSING FILE] = internal code not provided", ""]
        o += self.lines + [""]

        o += [bar, "3. ARCHITECTURE (reachable files -> classes -> methods; no source copied)", bar]
        for rel in sorted(self.reached_files):
            o.append(f"  {rel}")
            for sym in self.symbols.values():
                if sym.file == rel and sym.kind in ("class", "function") and "<local>" not in sym.id:
                    o.append(f"      {sym.kind:<9}{sym.name}   (line {sym.line})")
                    for m in self.symbols.values():
                        if m.parent == sym.id:
                            o.append(f"          method   {m.name}   (line {m.line})")
        o.append("")

        o += [bar, "4. RELATIONSHIPS (edges)", bar]
        for etype in ("INSTANTIATES", "INHERITS", "CALLS", "DISPATCHES_TO", "REFERENCES", "CONTAINS"):
            es = [e for e in self.edges.values() if e["type"] == etype]
            o.append(f"\n{etype} ({len(es)})")
            for e in es:
                extra = ""
                if etype == "DISPATCHES_TO":
                    keys = ", ".join(str(c.get("key", c.get("key_expr"))) for c in e.get("conditions", []))
                    extra = f"   [via {e.get('via')}; {e.get('resolution')}" + (f"; key {keys}" if keys else "") + "]"
                o.append(f"  {e['source']}  -->  {e['target']}" + (f"   (line {e['line']})" if e["line"] else "") + extra)
        o.append("")

        o += [bar, "5. FILE IMPORT GRAPH (reachable files only)", bar]
        for (src, tgt), (kind, line) in sorted(self.import_edges.items()):
            o.append(f"  {src}:{line}  IMPORTS  {tgt}   [{kind}]")
        o.append("")

        o += [bar, "6. SYMBOL TABLE (whole repository)", bar,
              f"{'reach':<6}{'kind':<10}{'location':<28}symbol", sub]
        for s in self.symbols.values():
            if "<local>" in s.id and s.id not in self.reached:
                continue
            o.append(f"{'YES' if s.id in self.reached else 'no':<6}{s.kind:<10}"
                     f"{s.file + ':' + str(s.line):<28}{s.id.split(':', 1)[1]}")
        o.append("")

        o += [bar, "7. EXTERNAL / STDLIB CALLS (traversal stopped)", bar]
        for title, d in (("External (third-party)", self.external_calls), ("Standard library", self.stdlib_calls)):
            o.append(f"\n{title}")
            for root in sorted(d):
                o.append(f"  {root}")
                for lab in sorted(d[root]):
                    o.append(f"      {lab}")
        o.append("")

        o += [bar, "8. MISSING INTERNAL CODE (referenced but file not in repository)", bar]
        for root in sorted(self.missing_calls):
            o.append(f"  {root}")
            for lab in sorted(self.missing_calls[root]):
                o.append(f"      {lab}")
        if not self.missing_calls:
            o.append("  (none)")
        o.append("")

        o += [bar, "9. UNRESOLVED CALLS (receiver type / dispatch targets could not be inferred)", bar]
        for (f, ln, lab), why in self.unresolved.items():
            o.append(f"  {f}:{ln}  {lab}()   - {why}")
        if not self.unresolved:
            o.append("  (none)")
        o.append("")

        o += [bar, "10. OUTPUT FILES", bar,
              "  index.json, graph.json, execution_tree.json, architecture_tree.json, expanded_trace.txt,",
              "  trace_tree.json, trace_tree.svg, source_tree.svg, functionality.json,",
              "  topdown_functionalities.json, topdown_functionalities.txt", ""]
        st = self.trace_tree_stats
        if st:
            o += [bar, "11. TRACE TREE (expanded_trace.txt -> trace_tree.json / trace_tree.svg)", bar,
                  f"Trace entries        : {st['trace_entries']}",
                  f"Code nodes           : {st['code_nodes']}",
                  f"References           : {st['references']}",
                  f"Maximum depth        : {st['max_depth']}",
                  f"Root nodes           : {st['root_nodes']}", ""]
        td = self.topdown_result
        if td:
            ts = td["statistics"]
            o += [bar, "12. TOP-DOWN FUNCTIONALITIES (trace_tree.json -> topdown_functionalities.json / .txt)", bar,
                  f"Functionalities      : {ts['functionalities']}  (by kind: "
                  + ", ".join(f"{k}={v}" for k, v in ts["by_kind"].items()) + ")",
                  f"Child operations     : {ts['child_operations']}",
                  f"Code nodes accounted : {ts['code_nodes_accounted']} / {ts['code_nodes']}",
                  f"Maximum path depth   : {ts['max_path_depth']}", ""]
        o += framework_report_lines(self.framework_info)       # additive section; empty without a framework analysis
        return "\n".join(o)


# ----------------------------------------------------------------------
# Top-down functionality extraction
#
#   trace_tree.json (root) --walk ROOT -> children--> functionalities
#                                                     (topdown_functionalities.json / .txt)
#
# Uses ONLY the trace tree (file / line / code / children / references). Nothing is
# looked up in the sources and nothing is invented: every path, root and child
# operation below is a node that exists in the tree, with its file, line and code
# copied verbatim.
#
# Traversal: start at ROOT, follow `children` recursively, depth-first, in tree order.
#
# What is ONE functionality?   parent construct + its child operations.
#   * A CONSTRUCT is a node that has body children: a control header (if / elif / else /
#     for / while / try / except / finally / with), a `def`, or any other statement that
#     carries children in the tree.
#   * A CHILD OPERATION is a direct child of the construct that is a plain statement
#     (no children of its own) or a call statement (its only children are the `def` /
#     `class` lines of what it calls - the cross-file link).
#   * Direct children that are constructs themselves are NOT folded in; the walk goes
#     down into them and they become their own functionality (so nothing is listed twice).
#     A construct with no child operations of its own (e.g. `for row in rows:` that only
#     holds another `for`) is a pass-through node: it stays in every path below it but is
#     not a functionality by itself.
#   * Call statements are operations of the construct that contains them AND the walk
#     continues into the callee `def` (possibly in another file), exactly as the tree shows.
#   * Multi-line headers: the trace stores the first lines of `if (\n ... \n):` as leaf
#     siblings and hangs the body under the LAST header line. Those leading lines are
#     recognised (contiguous lines, first one opens a bracket / ends with `\`) and
#     reported as the root + `header_lines` of that one functionality.
#
# Worked example (see the task description): reaching classes/Collider.py:58
#   `if self.entity.vel.y < 0:` yields ONE functionality = line 58 + lines 59 and 60.
# ----------------------------------------------------------------------
_TD_DEF_RE = re.compile(r"^(?:async\s+)?def\s")
_TD_CLASS_RE = re.compile(r"^class\s")
_TD_STR_RE = re.compile(r"'(?:[^'\\\n]|\\.)*'|" + r'"(?:[^"\\\n]|\\.)*"')
_TD_OPEN, _TD_CLOSE = "([{", ")]}"


def _td_ref(n):
    return OrderedDict([("node_id", n["id"]), ("file", n["file"]), ("line", n["line"]), ("code", n["code"])])


def _td_role(n):
    """def | class | leaf | call | compound   (derived from the node's own text and children only)."""
    code = n.get("code", "")
    if _TD_DEF_RE.match(code):
        return "def"
    if _TD_CLASS_RE.match(code):
        return "class"
    kids = n["children"]
    if not kids:
        return "leaf"
    if any(_td_role(k) not in ("def", "class") for k in kids):
        return "compound"
    return "call"                      # children are only the def / class lines of what is called


def _td_opens_header(code):
    """True for the first line of a multi-line control header: `if (`, `if a and \\`, `while f(`."""
    c = code.rstrip()
    if not _CONTROL_RE.match(c) or c.endswith(":"):
        return False
    bare = _TD_STR_RE.sub("", c)
    depth = sum(bare.count(ch) for ch in _TD_OPEN) - sum(bare.count(ch) for ch in _TD_CLOSE)
    return depth > 0 or c.endswith("\\")


def _td_header_runs(kids):
    """{id of a compound child: [leaf siblings that start its multi-line header]} (may be empty)."""
    runs = {}
    for j, x in enumerate(kids):
        if _td_role(x) != "compound":
            continue
        run, expect, k = [], x["line"], j - 1
        x_comment = x["code"].lstrip().startswith("#")
        while k >= 0:
            s = kids[k]
            if s["file"] != x["file"] or s["line"] != expect - 1 or _td_role(s) != "leaf":
                break
            # header opener: unclosed bracket / trailing backslash, OR a complete `...:` header that is followed
            # only by comment lines up to a comment node that carries the body (the trace keeps those comments
            # as header lines and hangs the body under the last one)
            comment_tail = (x_comment and _CONTROL_RE.match(s["code"]) and s["code"].rstrip().endswith(":")
                            and all(r["code"].lstrip().startswith("#") for r in run))
            run.insert(0, s)
            if _td_opens_header(s["code"]) or comment_tail:
                runs[x["id"]] = run
                break
            expect, k = s["line"], k - 1
    return runs


def _td_operation(n, kind):
    d = _td_ref(n)
    d["kind"] = kind
    d["depth"] = 1
    if n.get("category"):
        d["category"] = n["category"]
    if n.get("references"):
        d["references"] = [dict(r) for r in n["references"]]
    if kind == "call":
        d["calls"] = []
        for k in n["children"]:
            if _td_role(k) == "def":
                c = _td_ref(k)
                c["expanded_above"] = any(r.get("status") == "expanded_above" for r in k.get("references", []))
                d["calls"].append(c)
    return d


def _td_code_block(root, header_lines, ops):
    """Reconstructed functionality code. Indentation is derived from tree depth (the tree stores stripped code)."""
    lines = [root["code"]]
    for i, h in enumerate(header_lines):
        closing = h["code"].lstrip()[:1] in _TD_CLOSE
        lines.append(("" if (i == len(header_lines) - 1 and closing) else "    ") + h["code"])
    lines += ["    " + o["code"] for o in ops]
    return "\n".join(lines)


def _td_tree_lines(path, header_lines, children):
    """ASCII tree ROOT -> ... -> functionality root -> child operations (the format of the task example)."""
    out, prefix = ["ROOT", "\u2502"], ""
    for i, n in enumerate(path):
        last = i == len(path) - 1
        out.append(f"{prefix}\u2514\u2500\u2500 {n['file']}:{n['line']}")
        out.append(f"{prefix}    {n['code']}")
        if last:
            for h in header_lines:
                out.append(f"{prefix}    {h['code']}    [header line {h['file']}:{h['line']}]")
        if not last or children:
            out.append(f"{prefix}    \u2502")
        prefix += "    "
    for j, c in enumerate(children):
        end = j == len(children) - 1
        cont = "    " if end else "\u2502   "
        branch = "\u2514\u2500\u2500 " if end else "\u251c\u2500\u2500 "
        out.append(f"{prefix}{branch}{c['file']}:{c['line']}")
        out.append(f"{prefix}{cont}{c['code']}")
        for cl in c.get("calls", []):
            out.append(f"{prefix}{cont}\u21b3 calls {cl['file']}:{cl['line']}  {cl['code']}"
                       + ("  (expanded above)" if cl["expanded_above"] else ""))
        if not end:
            out.append(f"{prefix}\u2502")
    return out


def extract_topdown_functionalities(trace_root, project="", entry_point=""):
    """Top-down walk of the trace tree from ROOT -> ordered list of functionalities (see section comment)."""
    sys.setrecursionlimit(max(sys.getrecursionlimit(), 10000))
    funcs, accounted, by_anchor = [], {}, {}

    def mark(n, how):
        accounted.setdefault(n["id"], how)

    def visit(node, ancestors, header=None, prev=None):
        """ancestors = tree nodes above `node` (ROOT excluded). `header` = leading lines of its multi-line header.
        `prev` = the sibling directly before the construct (or before its multi-line header)."""
        role = _td_role(node)
        if role == "class":
            mark(node, "declaration")
            return
        if role == "leaf":
            return                                       # claimed as an operation by its construct
        if role == "call":                               # follow the call into the callee, as the tree does
            for k in node["children"]:
                if _td_role(k) == "class":
                    mark(k, "declaration")
                else:
                    visit(k, ancestors + [node])
            return

        # role is `def` or `compound`: a construct
        kids = node["children"]
        runs = _td_header_runs(kids)
        in_header = {s["id"] for run in runs.values() for s in run}
        ops = []
        for k in kids:
            r = _td_role(k)
            if k["id"] in in_header:
                continue
            if r == "class":
                mark(k, "declaration")
            elif r == "leaf":
                ops.append(_td_operation(k, "operation"))
            elif r == "call":
                ops.append(_td_operation(k, "call"))
        header = header or []
        if not ops:                                      # pass-through: stays in paths, no functionality of its own
            mark(node, "definition" if role == "def" else "pass_through")
            for h in header:
                mark(h, "pass_through")
        else:
            root = header[0] if header else node
            header_lines = [_td_ref(h) for h in header[1:]] + ([_td_ref(node)] if header else [])
            path = [_td_ref(a) for a in ancestors] + [_td_ref(root)]
            m = _CONTROL_RE.match(root["code"])
            kind, construct = (("control", m.group(1)) if m else
                               ("function_body", "def") if role == "def" else ("structural", "statement"))
            number = len(funcs) + 1
            f = OrderedDict([
                ("functionality_number", number), ("functionality_id", f"TDF_{number:06d}"),
                ("kind", kind), ("construct", construct),
                ("root", _td_ref(root)), ("header_lines", header_lines),
                ("tree_node_id", node["id"]),
                ("previous_sibling", _td_ref(prev) if (prev is not None and construct in
                                                       ("elif", "else", "except", "finally")) else None),
                ("path", path),
                ("path_text", "ROOT -> " + " -> ".join(f"{p['file']}:{p['line']}" for p in path)),
                ("children", ops),
                ("called_functions", [c for o in ops for c in o.get("calls", [])]),
                ("parent_functionality", None), ("child_functionalities", []),
                ("code", _td_code_block(root, header_lines, ops)),
            ])
            f["tree_path"] = "\n".join(_td_tree_lines(path, header_lines, ops))
            f["_ancestor_ids"] = [a["id"] for a in ancestors]
            funcs.append(f)
            by_anchor[node["id"]] = number
            mark(root, "root")
            for h in header:
                if h is not root:
                    mark(h, "header")
            if header:
                mark(node, "header")
            for k in kids:
                if k["id"] not in in_header and _td_role(k) in ("leaf", "call"):
                    mark(k, "operation")
        pos = {k["id"]: i for i, k in enumerate(kids)}
        for k in kids:                                   # continue top-down, in tree order
            if k["id"] not in in_header:
                run = runs.get(k["id"])
                start = pos[run[0]["id"]] if run else pos[k["id"]]
                visit(k, ancestors + [node], run, kids[start - 1] if start > 0 else None)

    for top in trace_root["children"]:
        visit(top, [])

    for f in funcs:                                      # functionality nesting (via the tree path)
        for aid in reversed(f.pop("_ancestor_ids")):
            if aid in by_anchor:
                f["parent_functionality"] = by_anchor[aid]
                funcs[by_anchor[aid] - 1]["child_functionalities"].append(f["functionality_number"])
                break

    total, walked = 0, [n for n in trace_root["children"]]
    while walked:
        n = walked.pop()
        total += 1
        walked.extend(n["children"])
    by_kind = OrderedDict()
    for f in funcs:
        by_kind[f["kind"]] = by_kind.get(f["kind"], 0) + 1
    stats = OrderedDict([
        ("functionalities", len(funcs)), ("by_kind", by_kind),
        ("child_operations", sum(len(f["children"]) for f in funcs)),
        ("code_nodes", total), ("code_nodes_accounted", len(accounted)),
        ("accounting", OrderedDict(sorted(
            ((k, sum(1 for v in accounted.values() if v == k)) for k in set(accounted.values()))))),
        ("max_path_depth", max([len(f["path"]) for f in funcs] or [0]))])
    return OrderedDict([("project", project), ("entry_point", entry_point),
                        ("traversal", "top-down from ROOT, depth-first, children in tree order"),
                        ("statistics", stats), ("functionalities", funcs)])


def render_topdown_text(result):
    """Human-readable report: for every functionality the 6 requested parts, in order."""
    bar, sub = "=" * 100, "-" * 100
    st = result["statistics"]
    o = [bar, "TOP-DOWN FUNCTIONALITY EXTRACTION", bar,
         f"Project        : {result['project']}", f"Entry point    : {result['entry_point']}",
         f"Traversal      : {result['traversal']}",
         f"Functionalities: {st['functionalities']}   (" + ", ".join(f"{k}={v}" for k, v in st["by_kind"].items()) + ")",
         f"Code nodes     : {st['code_nodes_accounted']} accounted of {st['code_nodes']}   "
         + "(" + ", ".join(f"{k}={v}" for k, v in st["accounting"].items()) + ")", "",
         "Rule: a construct node (control header / def / statement with children) + its direct child operations",
         "      = ONE functionality. Child constructs are walked into and become their own functionality.",
         "      Source: trace_tree.json only; file names, line numbers and code are copied verbatim.", "",
         "INDEX", sub]
    if result.get("hierarchy"):
        o[o.index("INDEX"):o.index("INDEX")] = ["PROJECT HIERARCHY", sub,
                                                render_project_tree(result["hierarchy"]), "", sub]
    for f in result["functionalities"]:
        r = f["root"]
        o.append(f"  #{f['functionality_number']:<4} {r['file']}:{r['line']:<5} {f['kind']:<14} "
                 f"{len(f['children']):>3} op(s)   {r['code'][:60]}"
                 + (f"   [entry {f['entry_file']}]" if f.get("entry_file") else ""))
    o.append("")
    for f in result["functionalities"]:
        r = f["root"]
        o += [bar, f"FUNCTIONALITY {f['functionality_number']}   [{f['functionality_id']}]", bar,
              f"Kind: {f['kind']} ({f['construct']})", "",
              "2. TOP-DOWN PATH (ROOT -> functionality)", "   ROOT"]
        o += [f"   -> {p['file']}" + (f":{p['line']:<5}" if p["line"] is not None else "") + f" {p['code']}"
              for p in f["path"]]
        o += ["", "3. FUNCTIONALITY ROOT", f"   file : {r['file']}", f"   line : {r['line']}", f"   code : {r['code']}"]
        for h in f["header_lines"]:
            o.append(f"   header line {h['file']}:{h['line']}: {h['code']}")
        if f["previous_sibling"]:
            ps = f["previous_sibling"]
            o.append(f"   previous sibling in tree: {ps['file']}:{ps['line']}: {ps['code']}")
        o += ["", "4. CHILD OPERATIONS"]
        for c in f["children"]:
            o += [f"   file : {c['file']}", f"   line : {c['line']}", f"   code : {c['code']}"]
            for cl in c.get("calls", []):
                o.append(f"   calls: {cl['file']}:{cl['line']}  {cl['code']}" + ("  (expanded above)" if cl["expanded_above"] else ""))
            o.append("")
        o += ["5. RECONSTRUCTED FUNCTIONALITY CODE"]
        o += ["   " + ln for ln in f["code"].splitlines()]
        o += ["", "6. COMPLETE TREE PATH"] + ["   " + ln for ln in f["tree_path"].splitlines()]
        rel = []
        if f["parent_functionality"]:
            rel.append(f"enclosing functionality: #{f['parent_functionality']}")
        if f["child_functionalities"]:
            rel.append("deeper functionalities reached below: " + ", ".join(f"#{n}" for n in f["child_functionalities"]))
        if rel:
            o += ["", "   " + "; ".join(rel)]
        o.append("")
    return "\n".join(o)


def _merge_hierarchy_statistics(h):
    """Statistics of a hierarchy in the shape the single-entry result (and report()) already uses."""
    fs = h["functionalities"]
    by_kind, accounting = OrderedDict(), {}
    child_ops = code_nodes = accounted = 0
    for e in h["entries"]:
        st = e.get("statistics") or {}
        child_ops += st.get("child_operations", 0)
        code_nodes += st.get("code_nodes", 0)
        accounted += st.get("code_nodes_accounted", 0)
        for k, v in (st.get("accounting") or {}).items():
            accounting[k] = accounting.get(k, 0) + v
    for f in fs:
        by_kind[f["kind"]] = by_kind.get(f["kind"], 0) + 1
    return OrderedDict([
        ("functionalities", len(fs)), ("by_kind", by_kind), ("child_operations", child_ops),
        ("code_nodes", code_nodes), ("code_nodes_accounted", accounted), ("accounting", OrderedDict(sorted(accounting.items()))),
        ("max_path_depth", max([len(f["path"]) for f in fs] or [0])), ("hierarchy", h["statistics"])])


def build_setup_hierarchy(root, descriptor, internal_hints, broker=None):
    """ROOT -> descriptor (setup.py) -> one node per declared entry file -> that entry's functionalities.

    Every declared entry is analysed independently (one forked PythonBroker each).  `broker` may be an
    already indexed PythonBroker for `descriptor`; otherwise one is created.  Returns a top-down result
    (same keys as extract_topdown_functionalities, plus `hierarchy`)."""
    disc = broker or PythonBroker(root, descriptor, internal_hints)
    entries = disc.discover_declared_entries()
    project = os.path.basename(disc.root) or disc.root

    def analyze(entry):
        b = disc.fork_for_entry(entry)
        b.run()
        trace_root, _stats = parse_trace(b.build_trace(), b.call_sites)
        return extract_topdown_functionalities(trace_root, project=project, entry_point=entry["entry_file"])

    h = build_project_tree(project, disc.entry, entries, analyze)
    result = OrderedDict([
        ("project", project), ("entry_point", disc.entry), ("traversal", h["traversal"]),
        ("statistics", _merge_hierarchy_statistics(h)), ("hierarchy", h), ("functionalities", h["functionalities"])])
    return result


# ======================================================================
# Framework / configuration-driven architecture traversal
#
# Execution tracing (above) follows CALLS.  Frameworks wire applications together through
# configuration values instead: a settings module names its URL module as a string, URL modules
# `include()` other URL modules by dotted name and hand view references to `path()`, settings list
# application packages and middleware classes as strings.  None of that is a call into project code,
# so none of it is reached by the execution trace.
#
# This layer reads those relationships STATICALLY (AST only; no repository code is imported or run)
# and records them as explicit architecture edges in the same graph.  It never touches
# `reached` / `reached_files` / `expanded` and never writes into the execution tree or trace, so
# execution statistics are unaffected.  Anything that cannot be resolved is reported as unresolved
# (with a reason) or external - a target is never invented.
# ======================================================================
EDGE_CONFIGURES = "CONFIGURES"
EDGE_REGISTERS_APP = "REGISTERS_APP"
EDGE_INCLUDES_URLS = "INCLUDES_URLS"
EDGE_ROUTES_TO = "ROUTES_TO"
EDGE_USES_MIDDLEWARE = "USES_MIDDLEWARE"
EDGE_IMPORTS = "IMPORTS"
ARCHITECTURE_EDGE_TYPES = (EDGE_CONFIGURES, EDGE_REGISTERS_APP, EDGE_INCLUDES_URLS, EDGE_ROUTES_TO,
                           EDGE_USES_MIDDLEWARE, EDGE_IMPORTS)

VIA_EXECUTION = "execution"
VIA_IMPORT = "import"                        # imported by an execution-reached file (no call needed)
VIA_CONFIGURATION = "configuration"          # named by configuration / registration
VIA_ARCH_IMPORT = "architecture_import"      # imported (bounded depth) by a configuration-discovered file


class _Item:
    """One statically known value (or the reason it is not known)."""
    __slots__ = ("kind", "value", "node", "file", "line", "conditional", "reason")

    def __init__(self, kind, value=None, node=None, file=None, line=None, conditional=False, reason=None):
        # kind: str | other | call | dict | dyn | module | external
        self.kind, self.value, self.node, self.file = kind, value, node, file
        self.line, self.conditional, self.reason = line, conditional, reason


class _Seq(list):
    """A statically evaluated list / tuple / set of _Item."""


def _const_str(node):
    return node.value if isinstance(node, ast.Constant) and isinstance(node.value, str) else None


def _toplevel_stmts(body):
    """Module-level statements, descending into if / try / with (not into def / class)."""
    for st in body:
        yield st
        if isinstance(st, ast.If):
            yield from _toplevel_stmts(st.body)
            yield from _toplevel_stmts(st.orelse)
        elif isinstance(st, ast.Try):
            yield from _toplevel_stmts(st.body)
            for h in st.handlers:
                yield from _toplevel_stmts(h.body)
            yield from _toplevel_stmts(st.orelse)
            yield from _toplevel_stmts(st.finalbody)
        elif isinstance(st, (ast.With, ast.AsyncWith)):
            yield from _toplevel_stmts(st.body)


class _StaticConfig:
    """Module-level constant evaluator: no execution, no imports of repository code.

    Handles string literals, lists / tuples / sets, `+` and `+=`, `.append` / `.extend`, names, imported
    names (from other repository modules, incl. `from x import *`), if / else and try / except (branches
    are unioned and flagged `conditional`).  Everything else becomes a `dyn` item carrying a reason."""
    _MAX_DEPTH = 40

    def __init__(self, broker):
        self.b = broker
        self._envs = {}
        self._busy = set()

    # -- environments ---------------------------------------------------
    def module_env(self, rel):
        if rel in self._envs:
            return self._envs[rel]
        if rel in self._busy:                    # import cycle: the partial environment is empty
            return {}
        tree = self.b.files.get(rel)
        if tree is None:
            self._envs[rel] = {}
            return {}
        self._busy.add(rel)
        env = {}
        try:
            self._exec(rel, tree.body, env, False)
        finally:
            self._busy.discard(rel)
        self._envs[rel] = env
        return env

    def _exec(self, rel, body, env, cond):
        for st in body:
            if isinstance(st, ast.Assign):
                val = self.eval(st.value, rel, env, cond)
                for t in st.targets:
                    if isinstance(t, ast.Name):
                        env[t.id] = val
            elif isinstance(st, ast.AnnAssign) and st.value is not None and isinstance(st.target, ast.Name):
                env[st.target.id] = self.eval(st.value, rel, env, cond)
            elif isinstance(st, ast.AugAssign) and isinstance(st.op, ast.Add) and isinstance(st.target, ast.Name):
                cur = self._lookup(st.target.id, rel, env, cond, st)
                env[st.target.id] = self._concat(cur, self.eval(st.value, rel, env, cond), rel, st, cond)
            elif (isinstance(st, ast.Expr) and isinstance(st.value, ast.Call)
                  and isinstance(st.value.func, ast.Attribute) and isinstance(st.value.func.value, ast.Name)
                  and st.value.func.attr in ("append", "extend", "insert")):
                self._mutate(st.value, rel, env, cond)
            elif isinstance(st, ast.ImportFrom) and any(a.name == "*" for a in st.names):
                target = self.b._strict_module_file(st.module or "", st.level, rel)
                if target:
                    env.update(self.module_env(target))
            elif isinstance(st, ast.If):
                self._exec_branches(rel, [st.body, st.orelse], env)
            elif isinstance(st, ast.Try):
                self._exec_branches(rel, [st.body + st.orelse] + [h.body for h in st.handlers], env)
                self._exec(rel, st.finalbody, env, True)
            elif isinstance(st, (ast.With, ast.AsyncWith)):
                self._exec(rel, st.body, env, cond)

    def _exec_branches(self, rel, branches, env):
        envs = []
        for br in branches:
            e = dict(env)
            self._exec(rel, br, e, True)
            envs.append(e)
        merged = {}
        for name in {n for e in envs for n in e}:
            vals, seen = [], set()
            for e in envs:
                if name in e and id(e[name]) not in seen:
                    seen.add(id(e[name]))
                    vals.append(e[name])
            if len(vals) == 1:
                merged[name] = vals[0]
                continue
            out, ids = _Seq(), set()
            for v in vals:
                for it in (v if isinstance(v, _Seq) else [v]):
                    if id(it) not in ids:
                        ids.add(id(it))
                        out.append(it)
            merged[name] = out
        env.clear()
        env.update(merged)

    def _mutate(self, call, rel, env, cond):
        name = call.func.value.id
        cur = self._lookup(name, rel, env, cond, call)
        cur = cur if isinstance(cur, _Seq) else _Seq([cur])
        if call.func.attr == "append" and call.args:
            env[name] = _Seq(list(cur) + [self._elem(call.args[0], rel, env, cond)])
        elif call.func.attr == "extend" and call.args:
            env[name] = self._concat(cur, self.eval(call.args[0], rel, env, cond), rel, call, cond)
        elif call.func.attr == "insert" and len(call.args) == 2:
            new = list(cur)
            idx = call.args[0].value if isinstance(call.args[0], ast.Constant) and isinstance(call.args[0].value, int) else 0
            new.insert(idx, self._elem(call.args[1], rel, env, cond))
            env[name] = _Seq(new)

    # -- expressions ----------------------------------------------------
    def _dyn(self, node, rel, cond, reason):
        return _Item("dyn", None, node, rel, getattr(node, "lineno", None), cond, reason)

    def _as_seq(self, v):
        return v if isinstance(v, _Seq) else _Seq([v])

    def _concat(self, left, right, rel, node, cond):
        if left is None:
            left = _Seq([self._dyn(node, rel, cond, "left operand is not statically known")])
        return _Seq(list(self._as_seq(left)) + list(self._as_seq(right)))

    def _elem(self, el, rel, env, cond):
        if isinstance(el, ast.Call):
            return _Item("call", None, el, rel, el.lineno, cond)
        v = self.eval(el, rel, env, cond)
        return v

    def eval(self, e, rel, env, cond, depth=0):
        if depth > self._MAX_DEPTH:
            return self._dyn(e, rel, cond, "expression nesting too deep")
        if isinstance(e, ast.Constant):
            return _Item("str" if isinstance(e.value, str) else "other", e.value, e, rel, e.lineno, cond)
        if isinstance(e, (ast.List, ast.Tuple, ast.Set)):
            out = _Seq()
            for el in e.elts:
                if isinstance(el, ast.Starred):
                    out.extend(self._as_seq(self.eval(el.value, rel, env, cond, depth + 1)))
                else:
                    v = self._elem(el, rel, env, cond)
                    out.extend(v) if isinstance(v, _Seq) else out.append(v)
            return out
        if isinstance(e, ast.BinOp) and isinstance(e.op, ast.Add):
            l, r = self.eval(e.left, rel, env, cond, depth + 1), self.eval(e.right, rel, env, cond, depth + 1)
            if (isinstance(l, _Item) and isinstance(r, _Item) and l.kind == "str" and r.kind == "str"):
                return _Item("str", l.value + r.value, e, rel, e.lineno, cond)
            return _Seq(list(self._as_seq(l)) + list(self._as_seq(r)))
        if isinstance(e, ast.Name):
            return self._lookup(e.id, rel, env, cond, e)
        if isinstance(e, ast.Attribute):
            return self._attr_value(e, rel, cond)
        if isinstance(e, ast.IfExp):
            a, b = self.eval(e.body, rel, env, True, depth + 1), self.eval(e.orelse, rel, env, True, depth + 1)
            return _Seq(list(self._as_seq(a)) + list(self._as_seq(b)))
        if isinstance(e, ast.Dict):
            return _Item("dict", None, e, rel, e.lineno, cond)
        if isinstance(e, ast.Call):
            fn = e.func.id if isinstance(e.func, ast.Name) else (e.func.attr if isinstance(e.func, ast.Attribute) else "")
            if fn in ("list", "tuple", "set", "sorted") and len(e.args) == 1 and not e.keywords:
                return self.eval(e.args[0], rel, env, cond, depth + 1)
            if fn == "patterns" and e.args:                       # old django.conf.urls.patterns(prefix, *urls)
                return _Seq(self._elem(a, rel, env, cond) for a in e.args[1:])
            return self._dyn(e, rel, cond, f"call to {ast.unparse(e.func)}() is evaluated at runtime")
        return self._dyn(e, rel, cond, f"{type(e).__name__} expression cannot be evaluated statically")

    def _lookup(self, name, rel, env, cond, node):
        if name in env:
            return env[name]
        imp = self.b.imports.get(rel, {}).get(name)
        if imp:
            target = self.b._strict_module_file(imp["module"], imp["level"], rel)
            if imp["name"] is None:
                return (_Item("module", target, node, rel, imp["line"], cond) if target
                        else _Item("external", imp["module"], node, rel, imp["line"], cond))
            if target:
                tenv = self.module_env(target)
                if imp["name"] in tenv:
                    return tenv[imp["name"]]
                return self._dyn(node, rel, cond, f"'{imp['name']}' is not a statically known value in {target}")
            return _Item("external", f"{imp['module']}.{imp['name']}", node, rel, imp["line"], cond)
        return self._dyn(node, rel, cond, f"name '{name}' is not statically known")

    def _attr_value(self, e, rel, cond):
        chain = []
        n = e
        while isinstance(n, ast.Attribute):
            chain.append(n.attr)
            n = n.value
        if isinstance(n, ast.Name):
            base = self._lookup(n.id, rel, {}, cond, n)
            if isinstance(base, _Item) and base.kind == "module":
                cur = base.value
                for attr in reversed(chain[1:]):
                    nxt = self.b._submodule_file(cur, attr)
                    if nxt is None:
                        break
                    cur = nxt
                else:
                    tenv = self.module_env(cur)
                    if chain[0] in tenv:
                        return tenv[chain[0]]
        return self._dyn(e, rel, cond, f"attribute '{ast.unparse(e)}' cannot be evaluated statically")


class FrameworkAnalyzer:
    """Base class of a framework-aware architecture analyzer.  A subclass recognises its framework from
    the selected entry file (`detect`) and then records configuration relationships on the broker
    (`analyze`).  Register new frameworks in FRAMEWORK_ANALYZERS."""
    framework = None

    def __init__(self, broker):
        self.b = broker
        self.cfg = _StaticConfig(broker)

    def detect(self):                       # -> seed dict | None
        raise NotImplementedError

    def analyze(self, seed):                # -> JSON-serialisable dict
        raise NotImplementedError


class DjangoAnalyzer(FrameworkAnalyzer):
    """Django: DJANGO_SETTINGS_MODULE -> settings -> ROOT_URLCONF -> nested include() -> views, plus
    INSTALLED_APPS and MIDDLEWARE.  Four roles are kept apart and never substituted for each other:

      process entry         manage.py / wsgi.py / asgi.py (names DJANGO_SETTINGS_MODULE)
      configuration root    the settings module (defines ROOT_URLCONF / INSTALLED_APPS / MIDDLEWARE)
      request-routing root  the module named by ROOT_URLCONF
      registered apps       packages listed in INSTALLED_APPS"""
    framework = "django"
    SETTINGS_SIGNALS = ("ROOT_URLCONF", "INSTALLED_APPS", "MIDDLEWARE", "MIDDLEWARE_CLASSES")
    DOTTED_SETTINGS = ("WSGI_APPLICATION", "ASGI_APPLICATION", "AUTHENTICATION_BACKENDS")
    HANDLERS = ("handler400", "handler403", "handler404", "handler500")
    URL_FUNCS = ("path", "re_path", "url")

    def __init__(self, broker):
        super().__init__(broker)
        self.files = OrderedDict()           # rel -> {"via": [...], "reasons": [...], "depth": n}
        self.unresolved, self.external = [], []
        self.apps, self.middleware, self.other_settings = [], [], []
        self.includes, self.routes, self.handlers, self.cycles = [], [], [], []
        self.settings_imports = []
        self._url_stack, self._url_done = [], set()
        self._seen_unres = set()
        self.capped = False

    # -- seed -----------------------------------------------------------
    @staticmethod
    def settings_module_reference(tree):
        """(dotted | None, line, expression text) when the file sets DJANGO_SETTINGS_MODULE, else None."""
        for n in ast.walk(tree):
            if (isinstance(n, ast.Call) and isinstance(n.func, ast.Attribute)
                    and n.func.attr in ("setdefault", "putenv") and len(n.args) >= 2
                    and _const_str(n.args[0]) == "DJANGO_SETTINGS_MODULE"):
                return _const_str(n.args[1]), n.lineno, ast.unparse(n.args[1])
            if isinstance(n, ast.Assign):
                for t in n.targets:
                    if isinstance(t, ast.Subscript) and _const_str(t.slice) == "DJANGO_SETTINGS_MODULE":
                        return _const_str(n.value), n.lineno, ast.unparse(n.value)
        return None

    def detect(self):
        b = self.b
        if b.entry not in b.files:
            return None
        ref = self.settings_module_reference(b.files[b.entry])
        if ref:
            return {"role": "process_entry", "settings_ref": ref}
        env = self.cfg.module_env(b.entry)
        if any(n in env for n in self.SETTINGS_SIGNALS):
            return {"role": "configuration_root"}
        if "urlpatterns" in env:
            return {"role": "request_routing_root"}
        return None

    # -- recording helpers ----------------------------------------------
    def _add_file(self, rel, via, reason=None, depth=0):
        d = self.files.setdefault(rel, {"via": [], "reasons": [], "depth": depth})
        if via not in d["via"]:
            d["via"].append(via)
        if reason and reason not in d["reasons"]:
            d["reasons"].append(reason)
        d["depth"] = min(d["depth"], depth)

    def _edge(self, src_file, tgt, etype, line, tgt_is_file=True, **attrs):
        b = self.b
        s = f"file:{src_file}"
        b._node(s, "file", src_file)
        if tgt_is_file:
            t = f"file:{tgt}"
            b._node(t, "file", tgt)
        else:
            t = tgt
            sym = b.symbols.get(tgt)
            b._node(t, sym.kind if sym else "symbol", sym.file if sym else None, sym.line if sym else None)
        b._edge(s, t, etype, line, origin="architecture", resolution="resolved", confidence="high",
                file=src_file, **attrs)

    def _unres(self, category, reference, reason, file, line, setting=None):
        key = (category, reference, reason, file, line)
        if key in self._seen_unres:
            return
        self._seen_unres.add(key)
        self.unresolved.append(OrderedDict(category=category, reference=reference, reason=reason,
                                           file=file, line=line, setting=setting))

    def _ext(self, reference, file, line, setting=None, reason="third-party / non-repository module"):
        self.external.append(OrderedDict(reference=reference, reason=reason, file=file, line=line, setting=setting))

    def _item_problem(self, it, setting, reference=None):
        """Record a non-string settings item (dynamic / call / ...) as unresolved with its reason."""
        reason = it.reason or (f"call to {ast.unparse(it.node.func)}() is evaluated at runtime"
                               if it.kind == "call" else f"{it.kind} value cannot be used as a dotted path")
        ref = reference or (ast.unparse(it.node) if it.node is not None else setting)
        self._unres("dynamic", ref, reason, it.file, it.line, setting)

    def _classify_missing(self, dotted, file):
        top = dotted.split(".")[0]
        if self.b._strict_module_file(top, 0, file) is not None or top in self.b.internal_hints:
            return "missing", (f"'{dotted}' not found under the import bases although top-level package "
                               f"'{top}' is part of the repository")
        return "external", f"top-level package '{top}' is not part of the repository"

    def _dotted(self, dotted, file):
        """Dotted path -> {status, file, symbol, reason}.  status: resolved | resolved_module_only |
        external | missing."""
        b = self.b
        mod = b._strict_module_file(dotted, 0, file)
        if mod:
            return dict(status="resolved", file=mod, symbol=None, reason=None)
        if "." in dotted:
            head, attr = dotted.rsplit(".", 1)
            mf = b._strict_module_file(head, 0, file)
            if mf:
                sid = f"{mf}:{attr}"
                if sid in b.symbols and b.symbols[sid].parent is None:
                    return dict(status="resolved", file=mf, symbol=sid, reason=None)
                t = b.resolve_name(attr, mf)
                if t.kind == "symbol":
                    return dict(status="resolved", file=b.symbols[t.ref].file, symbol=t.ref, reason="via re-export")
                if t.kind == "module":
                    return dict(status="resolved", file=t.ref, symbol=None, reason=None)
                return dict(status="resolved_module_only", file=mf, symbol=None,
                            reason=f"'{attr}' is not defined in {mf}")
        st, why = self._classify_missing(dotted, file)
        return dict(status=st, file=None, symbol=None, reason=why)

    # -- analysis -------------------------------------------------------
    def analyze(self, seed):
        b = self.b
        roles = OrderedDict(process_entry=None, configuration_root=None, request_routing_root=None,
                            registered_apps=[])
        notes = []
        settings_rel = routing_rel = None
        settings_module = None
        if seed["role"] == "process_entry":
            roles["process_entry"] = b.entry
            dotted, line, expr = seed["settings_ref"]
            self._add_file(b.entry, VIA_CONFIGURATION, "process entry")
            if dotted is None:
                self._unres("dynamic", expr, "DJANGO_SETTINGS_MODULE value is not a string literal", b.entry, line,
                            "DJANGO_SETTINGS_MODULE")
                notes.append("configuration root not determined: DJANGO_SETTINGS_MODULE is dynamic")
            else:
                r = self._dotted(dotted, b.entry)
                settings_module = OrderedDict(reference=dotted, status=r["status"], file=r["file"], line=line)
                if r["file"] and r["status"] in ("resolved", "resolved_module_only"):
                    settings_rel = r["file"]
                    self._edge(b.entry, settings_rel, EDGE_CONFIGURES, line, setting="DJANGO_SETTINGS_MODULE")
                    self._add_file(settings_rel, VIA_CONFIGURATION, "DJANGO_SETTINGS_MODULE")
                elif r["status"] == "external":
                    self._ext(dotted, b.entry, line, "DJANGO_SETTINGS_MODULE", r["reason"])
                else:
                    self._unres("missing", dotted, r["reason"], b.entry, line, "DJANGO_SETTINGS_MODULE")
        elif seed["role"] == "configuration_root":
            settings_rel = b.entry
            notes.append("process entry not derived: the selected entry is the settings module itself")
        else:
            routing_rel = b.entry
            notes.append("configuration root not determined: the selected entry is a URL module, not a "
                         "settings module (no settings are substituted)")
        if settings_rel:
            roles["configuration_root"] = settings_rel
            self._add_file(settings_rel, VIA_CONFIGURATION, "settings module")
            routing_rel = self._process_settings(settings_rel, roles)
        if routing_rel:
            roles["request_routing_root"] = routing_rel
            self._add_file(routing_rel, VIA_CONFIGURATION, "request-routing root")
            self._walk_urlconf(routing_rel, root=True)
            self._handlers(routing_rel)
        self._close_imports()
        return self._result(seed, roles, settings_module, notes)

    # settings ----------------------------------------------------------
    def _settings_sources(self, srel):
        """Settings split over several modules: follow `from x import *` / `from x import UPPER_NAME`."""
        seen, queue = {srel}, [srel]
        while queue:
            rel = queue.pop(0)
            tree = self.b.files.get(rel)
            if tree is None:
                continue
            for st in _toplevel_stmts(tree.body):
                if not isinstance(st, ast.ImportFrom):
                    continue
                if not any(a.name == "*" or a.name.isupper() for a in st.names):
                    continue
                target = self.b._strict_module_file(st.module or "", st.level, rel)
                if not target or target == rel:
                    continue
                self._edge(rel, target, EDGE_IMPORTS, st.lineno, via="settings import")
                self._add_file(target, VIA_CONFIGURATION, "imported settings")
                self.settings_imports.append(OrderedDict(source=rel, target=target, line=st.lineno))
                if target not in seen:
                    seen.add(target)
                    queue.append(target)

    def _scalar_items(self, val):
        return [] if val is None else (list(val) if isinstance(val, _Seq) else [val])

    def _process_settings(self, srel, roles):
        env = self.cfg.module_env(srel)
        self._settings_sources(srel)
        routing = None
        # ROOT_URLCONF ----------------------------------------------------
        if "ROOT_URLCONF" not in env:
            self._unres("dynamic", "ROOT_URLCONF", "ROOT_URLCONF is not defined in the settings (a Django "
                        "default is not assumed)", srel, None, "ROOT_URLCONF")
        for it in self._scalar_items(env.get("ROOT_URLCONF")):
            if it.kind != "str":
                self._item_problem(it, "ROOT_URLCONF", "ROOT_URLCONF")
                continue
            r = self._dotted(it.value, it.file)
            if r["status"] in ("resolved", "resolved_module_only") and r["symbol"] is None:
                self._edge(it.file, r["file"], EDGE_CONFIGURES, it.line, setting="ROOT_URLCONF",
                           conditional=it.conditional)
                self._add_file(r["file"], VIA_CONFIGURATION, "ROOT_URLCONF")
                routing = routing or r["file"]
            elif r["status"] == "external":
                self._ext(it.value, it.file, it.line, "ROOT_URLCONF", r["reason"])
            else:
                self._unres("missing", it.value, r["reason"] or "ROOT_URLCONF does not name a module",
                            it.file, it.line, "ROOT_URLCONF")
        # INSTALLED_APPS --------------------------------------------------
        for it in self._scalar_items(env.get("INSTALLED_APPS")):
            self._register_app(it, roles)
        # MIDDLEWARE ------------------------------------------------------
        for setting in ("MIDDLEWARE", "MIDDLEWARE_CLASSES"):
            for it in self._scalar_items(env.get(setting)):
                self._register_dotted(it, setting, EDGE_USES_MIDDLEWARE, self.middleware, "middleware")
        # other dotted-path settings -------------------------------------------
        for setting in self.DOTTED_SETTINGS:
            for it in self._scalar_items(env.get(setting)):
                self._register_dotted(it, setting, EDGE_CONFIGURES, self.other_settings, setting)
        return routing

    def _record(self, bucket, it, setting, r, **extra):
        rec = OrderedDict(setting=setting, entry=it.value, status=r["status"], file=r["file"],
                          symbol=r["symbol"], defined_in=it.file, line=it.line,
                          conditional=it.conditional, reason=r["reason"])
        rec.update(extra)
        bucket.append(rec)
        return rec

    def _register_dotted(self, it, setting, etype, bucket, reason_label):
        if it.kind != "str":
            self._item_problem(it, setting)
            return
        r = self._dotted(it.value, it.file)
        self._record(bucket, it, setting, r)
        if r["status"] in ("resolved", "resolved_module_only"):
            self._edge(it.file, r["file"], etype, it.line, setting=setting, entry=it.value,
                       symbol=r["symbol"], conditional=it.conditional)
            self._add_file(r["file"], VIA_CONFIGURATION, setting)
            if r["status"] == "resolved_module_only":
                self._unres("missing", it.value, r["reason"], it.file, it.line, setting)
        elif r["status"] == "external":
            self._ext(it.value, it.file, it.line, setting, r["reason"])
        else:
            self._unres("missing", it.value, r["reason"], it.file, it.line, setting)

    def _register_app(self, it, roles):
        if it.kind != "str":
            self._item_problem(it, "INSTALLED_APPS")
            return
        r = self._dotted(it.value, it.file)
        rec = self._record(self.apps, it, "INSTALLED_APPS", r)
        if r["status"] == "external":
            self._ext(it.value, it.file, it.line, "INSTALLED_APPS", r["reason"])
            return
        if r["status"] == "missing":
            self._unres("missing", it.value, r["reason"], it.file, it.line, "INSTALLED_APPS")
            return
        app_file = r["file"]
        self._edge(it.file, app_file, EDGE_REGISTERS_APP, it.line, setting="INSTALLED_APPS", app=it.value,
                   symbol=r["symbol"], conditional=it.conditional)
        self._add_file(app_file, VIA_CONFIGURATION, "INSTALLED_APPS")
        roles["registered_apps"].append(app_file)
        if r["status"] == "resolved_module_only":
            self._unres("missing", it.value, r["reason"], it.file, it.line, "INSTALLED_APPS")
        # Django loads <app>.models (and the AppConfig module) itself when it starts the app registry.
        pkg = posixpath.dirname(app_file) if (posixpath.basename(app_file) == "__init__.py" or r["symbol"]) else None
        implicit = []
        if pkg is not None:
            for name in ("models", "apps"):
                for cand in (f"{pkg}/{name}.py", f"{pkg}/{name}/__init__.py"):
                    if cand in self.b.py_files and cand != app_file:
                        implicit.append(cand)
                        self._edge(app_file, cand, EDGE_CONFIGURES, it.line, via=f"django app loading ({name} module)",
                                   setting="INSTALLED_APPS", implicit=True)
                        self._add_file(cand, VIA_CONFIGURATION, f"loaded by Django for app {it.value}")
                        break
        rec["implicit_modules"] = implicit

    # URL configuration -------------------------------------------------
    def _origin(self, file, node):
        if isinstance(node, ast.Name):
            imp = self.b.imports.get(file, {}).get(node.id)
            if not imp:
                return None
            return f"{imp['module']}.{imp['name']}" if imp["name"] else imp["module"]
        if isinstance(node, ast.Attribute):
            o = self._origin(file, node.value)
            return f"{o}.{node.attr}" if o else None
        return None

    def _django_func(self, file, node):
        o = self._origin(file, node)
        return o.rsplit(".", 1)[-1] if o and o.startswith("django.") else None

    def _walk_urlconf(self, rel, root=False, name="urlpatterns"):
        key = (rel, name)
        self._url_stack.append(key)
        try:
            if rel in self.b.legacy_files:
                self._unres("dynamic", rel, "file is analysed as text (not parseable): URL patterns not extracted",
                            rel, None, "urlpatterns")
                return
            pats = self.cfg.module_env(rel).get(name)
            if pats is None:
                self._unres("dynamic", f"{rel}:{name}", f"no statically evaluable '{name}' defined in {rel}",
                            rel, None, "urlpatterns")
                return
            self._walk_items(rel, self._scalar_items(pats))
        finally:
            self._url_stack.pop()
            self._url_done.add(key)

    def _walk_items(self, rel, items):
        for it in items:
            if it.kind == "call":
                self._url_call(it.file, it.node)
            elif it.kind == "dyn":
                self._unres("dynamic", f"{it.file}: urlpatterns", it.reason, it.file, it.line, "urlpatterns")
            elif it.kind in ("external", "module"):
                self._ext(str(it.value), it.file, it.line, "urlpatterns")

    def _url_call(self, file, call):
        fn = self._django_func(file, call.func)
        env = self.cfg.module_env(file)
        if fn in self.URL_FUNCS:
            self._route(file, call, fn)
        elif fn == "i18n_patterns":
            for a in call.args:
                self._walk_items(file, self._scalar_items(self.cfg.eval(a, file, env, False)))
        elif fn == "patterns":
            for a in call.args[1:]:
                if isinstance(a, ast.Call):
                    self._url_call(file, a)
        else:
            t = self._resolve(file, call.func)
            extra = f" (internal function {self.b.symbols[t.ref].id})" if t is not None and t.kind == "symbol" else ""
            self._unres("dynamic", f"{ast.unparse(call.func)}()",
                        f"URL patterns produced by {ast.unparse(call.func)}(){extra} are built at runtime; "
                        f"not a recognised registration function", file, call.lineno, "urlpatterns")

    def _resolve(self, file, node):
        try:
            return self.b.resolve_expr(node, Scope(file, None, f"file:{file}"))
        except (KeyError, RecursionError, AttributeError):
            return None

    def _route(self, file, call, kind):
        route = _const_str(call.args[0]) if call.args else None
        if route is None and call.args:
            route = ast.unparse(call.args[0])
        view = call.args[1] if len(call.args) > 1 else next((k.value for k in call.keywords if k.arg == "view"), None)
        if view is None:
            self._unres("dynamic", ast.unparse(call), "no view argument", file, call.lineno, "urlpatterns")
            return
        if isinstance(view, ast.Call) and self._django_func(file, view.func) == "include":
            self._include(file, view, route)
        else:
            self._view(file, view, route, call.lineno, kind)

    # include() ---------------------------------------------------------
    def _submodule(self, rel, name):
        return self.b._submodule_file(rel, name)

    def _chain(self, file, node):
        """Reference to a module / value through imports.  Returns ("module", rel) | ("value", rel, name) |
        ("local", name) | ("external", dotted) | ("missing", dotted, reason) | None."""
        names = []
        n = node
        while isinstance(n, ast.Attribute):
            names.append(n.attr)
            n = n.value
        if not isinstance(n, ast.Name):
            return None
        names.reverse()
        imp = self.b.imports.get(file, {}).get(n.id)
        if imp is None:
            return ("local", n.id) if not names else None
        if imp["name"] is None:
            mod = self.b._strict_module_file(imp["module"], imp["level"], file)
            if mod is None:
                return self._no_module(imp["module"], file, imp["level"])
            state = ("module", mod)
        else:
            mod = self.b._strict_module_file(imp["module"], imp["level"], file)
            if mod is None:
                return self._no_module(f"{imp['module']}.{imp['name']}" if imp["module"] else imp["name"],
                                       file, imp["level"])
            sub = self._submodule(mod, imp["name"])
            if sub:
                state = ("module", sub)
            elif imp["name"] in self.cfg.module_env(mod):
                state = ("value", mod, imp["name"])
            else:
                return ("missing", f"{imp['module']}.{imp['name']}", f"'{imp['name']}' is neither a submodule nor a "
                                                                       f"statically known value of {mod}")
        for attr in names:
            if state[0] != "module":
                return None
            sub = self._submodule(state[1], attr)
            if sub:
                state = ("module", sub)
            elif attr in self.cfg.module_env(state[1]):
                state = ("value", state[1], attr)
            else:
                return ("missing", f"{state[1]}.{attr}", f"'{attr}' is not defined in {state[1]}")
        return state

    def _no_module(self, dotted, file, level):
        if level:
            return ("missing", dotted or ".", "relative import does not resolve to a repository file")
        st, why = self._classify_missing(dotted, file)
        return (st, dotted, why)

    def _urlconf_ref(self, file, node):
        s = _const_str(node)
        if s is not None:
            r = self._dotted(s, file)
            if r["status"] in ("resolved", "resolved_module_only") and r["symbol"] is None:
                return ("module", r["file"])
            return (r["status"] if r["status"] in ("external", "missing") else "missing", s,
                    r["reason"] or "dotted name does not name a module")
        if isinstance(node, ast.Tuple) and node.elts:                  # include((patterns, app_name))
            return self._urlconf_ref(file, node.elts[0])
        if isinstance(node, (ast.List,)):
            return ("inline", self._scalar_items(self.cfg.eval(node, file, self.cfg.module_env(file), False)))
        if isinstance(node, ast.Name) and node.id in self.cfg.module_env(file):
            v = self.cfg.module_env(file)[node.id]
            if isinstance(v, _Seq):
                return ("inline", list(v))
        if isinstance(node, (ast.Name, ast.Attribute)):
            res = self._chain(file, node)
            if res is not None and res[0] != "local":
                return res
        return ("dynamic", ast.unparse(node), "include() argument is not a literal dotted name, an imported "
                                              "module or a statically known list")

    def _include(self, file, inc, route):
        arg = inc.args[0] if inc.args else next((k.value for k in inc.keywords if k.arg == "urlconf_module"), None)
        ns = next((_const_str(k.value) for k in inc.keywords if k.arg == "namespace"), None)
        rec = OrderedDict(source=file, line=inc.lineno, route=route, reference=ast.unparse(arg) if arg else None,
                          namespace=ns, status=None, target=None)
        if arg is None:
            rec["status"] = "dynamic"
            self._unres("dynamic", ast.unparse(inc), "include() without an argument", file, inc.lineno, "urlpatterns")
            self.includes.append(rec)
            return
        res = self._urlconf_ref(file, arg)
        kind = res[0]
        if kind in ("module", "value"):
            rel = res[1]
            name = res[2] if kind == "value" else "urlpatterns"
            rec["status"], rec["target"] = "resolved", rel
            self._edge(file, rel, EDGE_INCLUDES_URLS, inc.lineno, route=route, namespace=ns)
            self._add_file(rel, VIA_CONFIGURATION, "included URL module")
            key = (rel, name)
            if key in self._url_stack:
                rec["cycle"] = True
                self.cycles.append(OrderedDict(source=file, target=rel, line=inc.lineno,
                                               chain=[k[0] for k in self._url_stack] + [rel]))
            elif key in self._url_done:
                rec["already_walked"] = True
            else:
                self.includes.append(rec)
                self._walk_urlconf(rel, name=name)
                return
        elif kind == "inline":
            rec["status"] = "resolved_inline"
            self.includes.append(rec)
            self._walk_items(file, res[1])
            return
        elif kind == "external":
            rec["status"] = "external"
            self._ext(res[1], file, inc.lineno, "urlpatterns", res[2] if len(res) > 2 else "non-repository module")
        else:                                           # missing | dynamic
            rec["status"] = kind
            self._unres(kind, res[1], res[2], file, inc.lineno, "urlpatterns")
        self.includes.append(rec)

    # views -------------------------------------------------------------
    def _view(self, file, node, route, line, kind, wrapped=None):
        rec = OrderedDict(source=file, line=line, route=route, kind=kind, reference=ast.unparse(node),
                          status=None, target=None, wrapped_by=wrapped)
        self.routes.append(rec)
        if isinstance(node, ast.Call):
            f = node.func
            if isinstance(f, ast.Attribute) and f.attr == "as_view":
                node = f.value
            else:
                t = self._resolve(file, f)
                if t is not None and t.kind == "symbol":
                    rec["status"] = "dynamic"
                    self._unres("dynamic", ast.unparse(node), f"view built at runtime by internal call "
                                f"{self.b.symbols[t.ref].id}()", file, line, "urlpatterns")
                    return
                if node.args and isinstance(node.args[0], (ast.Name, ast.Attribute, ast.Call)):
                    self.routes.pop()                        # replaced by the wrapped view's record
                    self._view(file, node.args[0], route, line, kind, wrapped=ast.unparse(f))
                    return
                rec["status"] = "dynamic"
                self._unres("dynamic", ast.unparse(node), "view is produced by a call that is not a recognised "
                            "wrapper", file, line, "urlpatterns")
                return
        if isinstance(node, ast.Lambda):
            rec["status"] = "dynamic"
            self._unres("dynamic", "<lambda>", "view is a lambda", file, line, "urlpatterns")
            return
        s = _const_str(node)
        if s is not None:                                    # legacy string view 'pkg.views.name'
            r = self._dotted(s, file)
            self._finish_view(rec, file, line, route, r["status"], r["file"], r["symbol"], s, r["reason"])
            return
        if isinstance(node, (ast.Name, ast.Attribute)):
            t = self._resolve(file, node)
            if t is None:
                rec["status"] = "dynamic"
                self._unres("dynamic", ast.unparse(node), "view reference could not be resolved to a definition",
                            file, line, "urlpatterns")
            elif t.kind == "symbol":
                sym = self.b.symbols[t.ref]
                self._finish_view(rec, file, line, route, "resolved", sym.file, sym.id, ast.unparse(node), None)
            elif t.kind == "module":
                rec["status"] = "dynamic"
                self._unres("dynamic", ast.unparse(node), "reference names a module, not a view", file, line,
                            "urlpatterns")
            elif t.kind == "missing":
                rec["status"] = "missing"
                self._unres("missing", ast.unparse(node), f"internal module '{t.label}' is not in the repository",
                            file, line, "urlpatterns")
            else:                                            # external / stdlib / builtin
                rec["status"] = "external"
                self._ext(t.label or ast.unparse(node), file, line, "urlpatterns")
            return
        rec["status"] = "dynamic"
        self._unres("dynamic", ast.unparse(node), f"{type(node).__name__} view expression is not resolvable",
                    file, line, "urlpatterns")

    def _finish_view(self, rec, file, line, route, status, vfile, sid, text, reason, handler=None):
        if status in ("resolved", "resolved_module_only") and sid:
            rec["status"], rec["target"] = "resolved", sid
            attrs = dict(route=route)
            if handler:
                attrs["handler"] = handler
            self._edge(file, sid, EDGE_ROUTES_TO, line, tgt_is_file=False, **attrs)
            self.b.arch_symbols.add(sid)
            self._add_file(vfile, VIA_CONFIGURATION, "routed view")
        elif status in ("resolved", "resolved_module_only"):
            rec["status"] = "dynamic"
            self._unres("dynamic", text, reason or "dotted name does not name a view callable", file, line,
                        "urlpatterns")
        elif status == "external":
            rec["status"] = "external"
            self._ext(text, file, line, "urlpatterns", reason or "non-repository view")
        else:
            rec["status"] = "missing"
            self._unres("missing", text, reason, file, line, "urlpatterns")

    def _handlers(self, rel):
        env = self.cfg.module_env(rel)
        for name in self.HANDLERS:
            for it in self._scalar_items(env.get(name)):
                rec = OrderedDict(source=it.file, line=it.line, route=name, kind="handler", reference=it.value,
                                  status=None, target=None, wrapped_by=None)
                if it.kind != "str":
                    rec["status"] = "dynamic"
                    self._item_problem(it, name)
                else:
                    r = self._dotted(it.value, it.file)
                    self._finish_view(rec, it.file, it.line, name, r["status"], r["file"], r["symbol"], it.value,
                                      r["reason"], handler=name)
                self.handlers.append(rec)

    # bounded import closure --------------------------------------------
    def _internal_imports(self, rel):
        out = []
        for imp in self.b.imports.get(rel, {}).values():
            mod = self.b._strict_module_file(imp["module"], imp["level"], rel)
            if mod is None:
                continue
            if imp["name"] and imp["name"] != "*":
                sub = self.b._submodule_file(mod, imp["name"])
                if sub:
                    out.append((sub, imp["line"]))
                    continue
            out.append((mod, imp["line"]))
        return out

    def _close_imports(self):
        """Internal imports of configuration-discovered files, to `arch_depth` hops.  This is what lets a routed
        view reach the models it imports.  Bounded in depth and in file count; never touches reached_files."""
        depth_limit, cap = self.b.arch_depth, self.b.arch_max_files
        queue = [(rel, 0) for rel, d in self.files.items() if VIA_CONFIGURATION in d["via"]]
        seen = {rel for rel, _ in queue}
        while queue:
            rel, depth = queue.pop(0)
            if depth >= depth_limit:
                continue
            for target, line in self._internal_imports(rel):
                if target == rel:
                    continue
                self._edge(rel, target, EDGE_IMPORTS, line, via="architecture import", depth=depth + 1)
                if target in seen:
                    continue
                if len(self.files) >= cap:
                    self.capped = True
                    return
                seen.add(target)
                self._add_file(target, VIA_ARCH_IMPORT, f"imported by {rel}", depth + 1)
                queue.append((target, depth + 1))

    # result ------------------------------------------------------------
    def _result(self, seed, roles, settings_module, notes):
        b = self.b
        executed = set(b.reached_files)
        by_cfg = {r for r, d in self.files.items() if VIA_CONFIGURATION in d["via"]}
        by_arch_imp = {r for r, d in self.files.items() if d["via"] == [VIA_ARCH_IMPORT]}
        exec_imports = {t for (s, t), (k, _l) in b.import_edges.items()
                        if k == "internal" and s in executed and t in b.py_files} - executed
        related = executed | exec_imports | by_cfg | by_arch_imp
        unrelated = sorted(b.py_files - related)
        for rel, d in self.files.items():
            node = b.nodes.setdefault(f"file:{rel}", {"id": f"file:{rel}", "type": "file", "file": rel, "line": None})
            node["discovered_via"] = list(d["via"])
        file_entries = OrderedDict()
        for rel in sorted(self.files):
            d = self.files[rel]
            via = list(d["via"]) + ([VIA_EXECUTION] if rel in executed else [])
            file_entries[rel] = OrderedDict(discovered_via=via, execution_reached=rel in executed,
                                            reasons=d["reasons"], depth=d["depth"])
        stats = OrderedDict(
            indexed_files=len(b.py_files), execution_reached_files=len(executed),
            import_reached_files=len(exec_imports), configuration_files=len(by_cfg),
            architecture_import_files=len(by_arch_imp), unrelated_files=len(unrelated),
            configuration_only_files=len(by_cfg - executed),
            registered_apps=len(roles["registered_apps"]), middleware=len(self.middleware),
            url_includes=len(self.includes), routes=len(self.routes),
            routes_resolved=sum(1 for r in self.routes if r["status"] == "resolved"),
            unresolved=len(self.unresolved), external=len(self.external), cycles=len(self.cycles),
            architecture_symbols=len(b.arch_symbols), capped=self.capped)
        return OrderedDict([
            ("framework", self.framework), ("active", True), ("seed_role", seed["role"]),
            ("roles", roles), ("settings_module", settings_module), ("notes", notes),
            ("installed_apps", self.apps), ("middleware", self.middleware), ("other_settings", self.other_settings),
            ("settings_imports", self.settings_imports), ("url_includes", self.includes), ("routes", self.routes),
            ("handlers", self.handlers), ("cycles", self.cycles),
            ("unresolved", self.unresolved), ("external", self.external),
            ("classification", OrderedDict([
                ("execution", sorted(executed)), ("import_of_execution", sorted(exec_imports)),
                ("configuration", sorted(by_cfg)), ("architecture_import", sorted(by_arch_imp)),
                ("unrelated_count", len(unrelated)),
                ("unrelated_files", unrelated[:500]), ("unrelated_files_truncated", len(unrelated) > 500)])),
            ("files", file_entries), ("statistics", stats)])


FRAMEWORK_ANALYZERS = OrderedDict([("django", DjangoAnalyzer)])


def framework_report_lines(info):
    """Text rendering of the framework result (report.txt section)."""
    if not info:
        return []
    bar = "=" * 78
    o = [bar, "13. FRAMEWORK / CONFIGURATION ARCHITECTURE (static; separate from the execution trace)", bar]
    if not info.get("active"):
        return o + [f"  framework '{info['framework']}' requested but not detected: {info.get('reason')}", ""]
    r, st = info["roles"], info["statistics"]
    o += [f"Framework             : {info['framework']}",
          f"Process entry         : {r['process_entry'] or '(not derived)'}",
          f"Configuration root    : {r['configuration_root'] or '(not determined)'}",
          f"Request-routing root  : {r['request_routing_root'] or '(not determined)'}",
          f"Registered apps       : {st['registered_apps']}",
          *[f"Note                  : {n}" for n in info["notes"]], "",
          "Files by how they were reached (execution is NOT inflated by configuration discovery):",
          f"  indexed                 : {st['indexed_files']}",
          f"  execution (calls)       : {st['execution_reached_files']}",
          f"  imported by executed    : {st['import_reached_files']}",
          f"  configuration           : {st['configuration_files']}  (of which not executed: {st['configuration_only_files']})",
          f"  architecture imports    : {st['architecture_import_files']}",
          f"  unrelated to the root   : {st['unrelated_files']}",
          f"Routes: {st['routes']} ({st['routes_resolved']} resolved)   URL includes: {st['url_includes']}   "
          f"Middleware: {st['middleware']}   Cycles: {st['cycles']}   Unresolved: {st['unresolved']}   "
          f"External: {st['external']}", ""]
    for title, key in (("INSTALLED_APPS", "installed_apps"), ("MIDDLEWARE", "middleware")):
        o.append(title)
        for a in info[key]:
            o.append(f"  [{a['status']}] {a['entry']}  ->  {a['file'] or '-'}  ({a['defined_in']}:{a['line']})")
    o.append("URL INCLUDES")
    for i in info["url_includes"]:
        o.append(f"  [{i['status']}] {i['source']}:{i['line']}  include({i['reference']})  ->  {i['target'] or '-'}"
                 + ("   (cycle)" if i.get("cycle") else ""))
    o.append("UNRESOLVED")
    for u in info["unresolved"]:
        o.append(f"  [{u['category']}] {u['file']}:{u['line']}  {u['reference']}  - {u['reason']}")
    if not info["unresolved"]:
        o.append("  (none)")
    o.append("")
    return o


class Visitor(ast.NodeVisitor):
    """Walks a body in source order; nested defs/lambdas are not entered."""

    def __init__(self, broker, scope, depth):
        self.b, self.scope, self.depth = broker, scope, depth

    def visit_FunctionDef(self, node): pass
    visit_AsyncFunctionDef = visit_FunctionDef
    visit_ClassDef = visit_FunctionDef
    visit_Lambda = visit_FunctionDef

    def visit_Assign(self, node):
        self.visit(node.value)
        if isinstance(node.value, ast.Call):
            t = self.b.resolve_expr(node.value, self.scope)
            if t:
                for tg in node.targets:
                    if isinstance(tg, ast.Name):
                        self.scope.vars[tg.id] = t
            else:
                self.b._bind_candidates(node.targets, node.value, self.scope)
        for tg in node.targets:                            # x = {..: f} / x = f  -> REFERENCES edges
            self.b.note_binding_refs(tg, self.scope)

    def visit_AnnAssign(self, node):
        if node.value is not None:
            self.visit(node.value)
            self.b.note_binding_refs(node.target, self.scope)

    def visit_Call(self, node):
        d = self.b.resolve_dispatch(node, self.scope)
        if d is not None:                                  # table[key]() / handler() through an alias set
            self.b.handle_dispatch(node, d, self.scope, self.depth)
        else:
            t = self.b.resolve_expr(node.func, self.scope)
            cands = [t] if t is not None else self.b.resolve_candidates(node.func, self.scope)
            if cands:                                      # several possible receivers / targets: follow every one
                for c in cands:
                    self.b.handle_call(node, c, self.scope, self.depth)
            else:
                self.b.handle_call(node, None, self.scope, self.depth)
        self.b.note_arg_references(node, self.scope)
        self.generic_visit(node)
