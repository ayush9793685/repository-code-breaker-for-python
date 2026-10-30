"""HTML broker (design: "HTML Broker - Design Document" v0.1, milestones M1-M3; M4-M6 live in separate components).

Parses ONE HTML / Django template file with ``html.parser`` (no execution, no HTTP) and reports what the
file itself proves.  Parsing is kept apart from resolution (design section 2): every reference is recorded with its
source file, line, relationship type and target, and stays ``unresolved`` (or ``dynamic`` / ``not_applicable``)
in the parse records.  Route / template resolution (M4, M5) is the separate ``django_resolver`` component and the
project-wide graph (M6) is ``project_graph``; the broker only *asks* them, after parsing, to verify references.
A relationship is marked ``resolved`` only when that component verified it against the Django configuration.

Pipeline (design section 4): discovery (``discover_templates`` / ``analyze_files`` accept a path or a list of
candidate files) -> read (UTF-8, latin-1 fallback is reported) -> html.parser pass -> element extraction ->
separate Django template pass -> normalised records -> (separate) resolution -> (separate) graph.

Broker contract (see app_broker.py): HTMLBroker(root, entry_file, internal_hints), run(), normalized_result(),
reachable_count, summary_lines().  It writes no files.  Optional hook: project_graph_document().

Record schema (design section 7; flat, JSON-serialisable): source_file, element_type, relationship, attribute,
target, text, target_type, resolution_status, plus line / column and element-specific keys.
Relationship types: navigates_to, submits_to, has_control, loads_script, loads_stylesheet, links_resource,
loads_image, embeds, extends, includes, uses_url_name, uses_static, uses_variable, defines_block, loads_library.
"""
import os
import posixpath
import re
from collections import OrderedDict
from html.parser import HTMLParser
from urllib.parse import urlsplit

from normalized import new_result

try:                                                    # shared directory exclusions
    from broker_common import EXCLUDE_DIRS
except ImportError:                                     # pragma: no cover
    EXCLUDE_DIRS = {".git", "__pycache__", "node_modules", ".venv", "venv", "build", "dist"}

TEMPLATE_EXTENSIONS = (".html", ".htm", ".xhtml")
PARSER_NAME = "html.parser"                              # design section 3: replaceable, see PARSERS

_TAG_RE = re.compile(r"\{%-?\s*(\w+)\s*(.*?)\s*-?%\}", re.S)
_VAR_RE = re.compile(r"\{\{(.*?)\}\}", re.S)
_QUOTED = re.compile(r"""^\s*(['"])(.*?)\1""")
_BARE_TAG = re.compile(r"^\s*\{%\s*(url|static)\s+(.*?)\s*%\}\s*$", re.S)
_DJ_COMMENT = re.compile(r"\{#[^\n]*?#\}|\{%\s*comment\b.*?\{%\s*endcomment\s*%\}", re.S)
_HTML_COMMENT = re.compile(r"<!--.*?-->", re.S)
_CONTROLS = {"input", "select", "textarea", "button"}
_REFS = {("a", "href"): "navigates_to", ("form", "action"): "submits_to", ("script", "src"): "loads_script",
         ("img", "src"): "loads_image", ("iframe", "src"): "embeds"}
_RESOURCE_TYPE = {"a": "hyperlink", "form": "form", "script": "script", "img": "image", "iframe": "document"}
_NO_TARGET_STATUS = "not_applicable"
RESOLUTION_STATUSES = ("unresolved", "resolved", "dynamic", "not_applicable")
# files the brokers can analyse; anything else a reference points at (images, css, ...) is recorded, never queued
ANALYZABLE_EXTENSIONS = TEMPLATE_EXTENSIONS + (".py",)
_IGNORED_TARGETS = {"fragment": "anchor", "mailto": "mailto", "tel": "tel", "javascript": "javascript", "data_uri": "data_uri"}


def classify_target(value):
    """-> (target_type, resolution_status).  Only what the text proves."""
    v = value.strip()
    low = v.lower()
    if "{{" in v or "{%" in v:
        return "dynamic", "dynamic"
    if low.startswith("mailto:"):
        return "mailto", "not_applicable"
    if low.startswith(("tel:", "sms:")):
        return "tel", "not_applicable"
    if low.startswith("javascript:"):
        return "javascript", "not_applicable"
    if low.startswith("data:"):
        return "data_uri", "not_applicable"
    if v.startswith("#"):
        return "fragment", "not_applicable"
    if low.startswith(("http://", "https://", "//")):
        return "external_url", "not_applicable"
    if v.startswith("/static/") or v.startswith("/media/"):
        return "static_resource", "unresolved"
    if v.startswith("/"):
        return "url", "unresolved"
    return "relative_url", "unresolved"                  # relative: original value kept, never resolved here


def _mask(pattern, text):
    """Blank out matches but keep every newline, so line numbers stay true."""
    return pattern.sub(lambda m: re.sub(r"[^\n]", " ", m.group(0)), text)


class _Extractor(HTMLParser):
    """Element extraction pass (design section 4, step 3-4)."""

    def __init__(self, source_file):
        super().__init__(convert_charrefs=True)
        self.source_file = source_file
        self.records, self.issues = [], []
        self._forms, self._open_a, self._skip = [], [], 0       # open <form>/<a>, depth inside <script>/<style>
        self.tags_seen = 0
        self.has_doctype = False

    def _rec(self, tag, **kw):
        line, col = self.getpos()
        r = OrderedDict(source_file=self.source_file, element_type=tag, line=line, column=col)
        r.update(kw)
        self.records.append(r)
        return r

    def handle_decl(self, decl):
        self.has_doctype = self.has_doctype or decl.lower().startswith("doctype")

    def handle_starttag(self, tag, attrs):
        self.tags_seen += 1
        a = {k: (v if v is not None else "") for k, v in attrs}
        has = {k for k, _ in attrs}
        if tag in ("script", "style"):
            self._skip += 1
        if tag == "form":
            r = self._rec("form", relationship="submits_to", attribute="action", method=(a.get("method") or "get").lower(),
                          attributes=a, form_id=a.get("id"), resource_type="form")
            self._finish_ref(r, a.get("action") if "action" in has else None)
            self._forms.append(r)
        elif tag in _CONTROLS:
            r = self._rec(tag, relationship="has_control", attribute="name", name=a.get("name"), type=a.get("type"),
                          id=a.get("id"), form_line=self._forms[-1]["line"] if self._forms else None,
                          form_id=self._forms[-1].get("form_id") if self._forms else None,
                          attributes=a, target_type="control", resolution_status=_NO_TARGET_STATUS,
                          resource_type="control")
            r["target"] = a.get("name") or a.get("id")
        elif tag == "link" and "href" in has:
            rel = (a.get("rel") or "").lower()
            as_ = (a.get("as") or "").lower()
            is_css = "stylesheet" in rel.split() or (("preload" in rel.split() or "prefetch" in rel.split()) and as_ == "style")
            r = self._rec("link", relationship="loads_stylesheet" if is_css else "links_resource",
                          attribute="href", rel=a.get("rel"),
                          resource_type="stylesheet" if is_css else (rel.split()[0] if rel.split() else "link"),
                          attributes=a)
            self._finish_ref(r, a.get("href"))
        elif tag in ("a", "img", "script", "iframe"):
            attr = "href" if tag == "a" else "src"
            r = self._rec(tag, relationship=_REFS[(tag, attr)], attribute=attr, attributes=a,
                          resource_type=_RESOURCE_TYPE[tag])
            if tag == "img":
                r.update(alt=a.get("alt"), width=a.get("width"), height=a.get("height"))
            if tag == "script":
                r["inline"] = attr not in has
                if a.get("type"):
                    r["script_type"] = a["type"]
            if tag == "a":
                r["text"] = ""
                self._open_a.append(r)
            self._finish_ref(r, a.get(attr) if attr in has else None)

    def _finish_ref(self, r, value):
        if value is None or not value.strip():          # missing / empty href, action, src: no target reference
            r["relationship"], r["target"] = None, None
            return
        m = _BARE_TAG.match(value)
        q = _QUOTED.match(m.group(2)) if m else None
        if m and q:                                      # href="{% url 'name' %}" / src="{% static 'x' %}"
            r["target"], r["expression"] = q.group(2), value.strip()
            r["target_type"] = "url_name" if m.group(1) == "url" else "static_file"
            r["resolution_status"] = "unresolved"
            if m.group(1) == "url":
                r["arguments"] = m.group(2)[q.end():].strip()
        else:
            r["target"] = value.strip()
            r["target_type"], r["resolution_status"] = classify_target(value)
            if r["target_type"] == "dynamic":
                r["expression"] = value.strip()

    def handle_endtag(self, tag):
        if tag in ("script", "style") and self._skip:
            self._skip -= 1
        elif tag == "form":
            if self._forms:
                self._forms.pop()
        elif tag == "a" and self._open_a:
            r = self._open_a.pop()
            r["text"] = " ".join(r["text"].split())

    def handle_data(self, data):
        if self._open_a and not self._skip:
            self._open_a[-1]["text"] += data

    def close(self):
        super().close()
        for r in self._forms:
            self.issues.append(f"line {r['line']}: <form> is never closed")
        for r in self._open_a:
            self.issues.append(f"line {r['line']}: <a> is never closed")
            r["text"] = " ".join(r["text"].split())




# Complete source-preserving extraction layer.  The existing semantic records above remain
# backward compatible; this layer additionally preserves every source line and every HTML
# token/node, including tags that have no special relationship type.
_VOID_ELEMENTS = {
    "area", "base", "br", "col", "embed", "hr", "img", "input", "link", "meta",
    "param", "source", "track", "wbr",
}
_TEMPLATE_TOKEN_RE = re.compile(
    r"\{%.*?%\}|\{\{.*?\}\}|\{#.*?#\}", re.S
)


class _CompleteHTMLExtractor(HTMLParser):
    """Build a best-effort hierarchical tree while preserving source spans.

    HTMLParser is tolerant, not a browser's full HTML5 tree builder. Exact original source
    is therefore also stored separately and is the source of truth for lossless extraction.
    """

    def __init__(self, source_file, text):
        super().__init__(convert_charrefs=False)
        self.source_file = source_file
        self.text = text
        self.lines = text.splitlines(keepends=True)
        if text and (not self.lines or not self.lines[-1].endswith(("\n", "\r"))):
            pass
        self._line_offsets = [0]
        for match in re.finditer("\n", text):
            self._line_offsets.append(match.end())
        self.nodes = []
        self.issues = []
        self._stack = []
        self._serial = 0
        self.root = {
            "node_id": f"{source_file}#document", "node_type": "document",
            "source_file": source_file, "parent_id": None, "children": [],
            "start_line": 1, "start_column": 0, "end_line": max(1, text.count("\n") + 1),
            "end_column": 0, "source_span": {"start_offset": 0, "end_offset": len(text)},
        }

    def _offset(self, line, column):
        index = max(0, min(line - 1, len(self._line_offsets) - 1))
        return min(len(self.text), self._line_offsets[index] + column)

    def _loc(self, offset):
        line, col = _line_col(self.text, max(0, min(offset, len(self.text))))
        return line, col

    def _add(self, node_type, start, end, **fields):
        start = max(0, min(start, len(self.text)))
        end = max(start, min(end, len(self.text)))
        line, col = self._loc(start)
        end_line, end_col = self._loc(end)
        self._serial += 1
        parent = self._stack[-1] if self._stack else self.root
        node = {
            "node_id": f"{self.source_file}#n{self._serial:06d}",
            "node_type": node_type,
            "source_file": self.source_file,
            "parent_id": parent["node_id"],
            "children": [],
            "start_line": line,
            "start_column": col,
            "end_line": end_line,
            "end_column": end_col,
            "source_span": {"start_offset": start, "end_offset": end},
            "source_text": self.text[start:end],
        }
        node.update(fields)
        parent["children"].append(node["node_id"])
        self.nodes.append(node)
        return node

    def _start_element(self, tag, attrs, self_closing=False):
        start = self._offset(*self.getpos())
        raw = self.get_starttag_text() or ""
        end = start + len(raw)
        # Keep duplicate attributes in ordered form as well as a convenient map.
        attr_list = [{"name": k, "value": v, "has_value": v is not None} for k, v in attrs]
        attr_map = {}
        for k, v in attrs:
            attr_map[k] = v
        node = self._add("element", start, end, tag=tag, attributes=attr_map,
                         attribute_list=attr_list, self_closing=bool(self_closing or tag in _VOID_ELEMENTS),
                         open_source=raw, close_source=None)
        if not node["self_closing"]:
            self._stack.append(node)

    def handle_starttag(self, tag, attrs):
        self._start_element(tag, attrs, False)

    def handle_startendtag(self, tag, attrs):
        self._start_element(tag, attrs, True)

    def handle_endtag(self, tag):
        start = self._offset(*self.getpos())
        raw = self.get_starttag_text() or ""
        # HTMLParser doesn't expose the raw end-tag via get_starttag_text; locate it at the
        # callback offset, preserving its source spelling and spacing.
        match = re.match(r"</\s*" + re.escape(tag) + r"\s*[^>]*>", self.text[start:], re.I)
        raw = match.group(0) if match else f"</{tag}>"
        end = start + len(raw)
        self._add("end_tag", start, end, tag=tag, source_text=raw)
        # Pop through the matching element so malformed nesting doesn't strand the stack.
        found = None
        for i in range(len(self._stack) - 1, -1, -1):
            if self._stack[i].get("tag", "").lower() == tag.lower():
                found = i
                break
        if found is None:
            self.issues.append(f"line {_line_col(self.text, start)[0]}: unmatched closing tag </{tag}>")
            return
        for unclosed in self._stack[found + 1:]:
            self.issues.append(f"line {unclosed['start_line']}: <{unclosed.get('tag')}> implicitly closed before </{tag}>")
        element = self._stack[found]
        element["end_line"], element["end_column"] = self._loc(end)
        element["source_span"]["end_offset"] = end
        element["source_text"] = self.text[element["source_span"]["start_offset"]:end]
        element["close_source"] = raw
        del self._stack[found:]

    def handle_data(self, data):
        if not data:
            return
        start = self._offset(*self.getpos())
        # With convert_charrefs=False, normal data is source text. Use callback length and
        # source offsets, rather than decoded data, to preserve exact whitespace/entities.
        self._add("text", start, start + len(data), text=self.text[start:start + len(data)])

    def handle_entityref(self, name):
        start = self._offset(*self.getpos())
        raw = f"&{name};"
        self._add("entity_reference", start, start + len(raw), name=name, text=raw)

    def handle_charref(self, name):
        start = self._offset(*self.getpos())
        raw = f"&#{name};"
        self._add("character_reference", start, start + len(raw), value=name, text=raw)

    def handle_comment(self, data):
        start = self._offset(*self.getpos())
        raw = "<!--" + data + "-->"
        self._add("comment", start, start + len(raw), text=data)

    def handle_decl(self, decl):
        start = self._offset(*self.getpos())
        raw = "<!" + decl + ">"
        self._add("declaration", start, start + len(raw), declaration=decl)

    def handle_pi(self, data):
        start = self._offset(*self.getpos())
        raw = "<?" + data + ">"
        self._add("processing_instruction", start, start + len(raw), data=data)

    def unknown_decl(self, data):
        start = self._offset(*self.getpos())
        raw = "<![" + data + "]>"
        self._add("unknown_declaration", start, start + len(raw), data=data)

    def finish(self):
        for node in self._stack:
            self.issues.append(f"line {node['start_line']}: <{node.get('tag')}> has no closing tag")
            node["end_line"] = max(1, self.text.count("\n") + 1)
            node["end_column"] = 0
            node["source_span"]["end_offset"] = len(self.text)
            node["source_text"] = self.text[node["source_span"]["start_offset"]:]
        return self.root, self.nodes


def complete_html_extraction(source_file, text):
    """Return lossless source lines, all HTML parser nodes, and all Django template tokens.

    The original source is preserved verbatim in ``source_lines``. The tree is a tolerant
    structural representation; template tokens are a parallel overlay because Django syntax
    is not standard HTML and can occur inside attributes or text.
    """
    parser = _CompleteHTMLExtractor(source_file, text)
    try:
        parser.feed(text)
        parser.close()
    except Exception as exc:
        parser.issues.append(f"complete parser stopped early: {type(exc).__name__}: {exc}")
    root, nodes = parser.finish()
    template_nodes = []
    for i, match in enumerate(_TEMPLATE_TOKEN_RE.finditer(text), 1):
        raw = match.group(0)
        line, col = _line_col(text, match.start())
        if raw.startswith("{{"):
            token_type, expression = "django_variable", raw[2:-2].strip()
        elif raw.startswith("{#"):
            token_type, expression = "django_comment", raw[2:-2]
        else:
            inner = raw[2:-2].strip().strip("- ")
            name = inner.split(None, 1)[0] if inner else ""
            token_type, expression = "django_tag", inner
        template_nodes.append({
            "node_id": f"{source_file}#tpl{i:06d}", "node_type": token_type,
            "source_file": source_file, "line": line, "column": col,
            "source_span": {"start_offset": match.start(), "end_offset": match.end()},
            "source_text": raw, "tag_name": name if token_type == "django_tag" else None,
            "expression": expression,
        })
    # Keep both representations: a flat node index for stable references and a nested
    # document tree for consumers that need to traverse the complete HTML hierarchy.
    by_id = {node["node_id"]: node for node in nodes}

    def nested(node_id):
        node = by_id[node_id]
        result = {k: v for k, v in node.items() if k != "children"}
        result["children"] = [nested(child_id) for child_id in node.get("children", []) if child_id in by_id]
        return result

    source_lines = [
        {"line_number": i, "text": line}
        for i, line in enumerate(text.splitlines(keepends=True), 1)
    ]
    line_count = len(source_lines)
    document_tree = {
        "node_id": root["node_id"],
        "node_type": "document",
        "source_file": source_file,
        "start_line": 1,
        "end_line": max(1, line_count),
        "source_span": dict(root["source_span"]),
        "children": [nested(child_id) for child_id in root.get("children", []) if child_id in by_id],
    }
    return {
        "source_file": source_file,
        "source_text": text,
        "source_lines": source_lines,
        "line_count": line_count,
        "root": root,
        "document_tree": document_tree,
        "nodes": nodes,
        "template_nodes": template_nodes,
        "issues": parser.issues,
        "stats": {
            "html_nodes": len(nodes),
            "template_nodes": len(template_nodes),
            "source_lines": line_count,
        },
    }


# design section 3: the parser is replaceable - anything with the _Extractor interface can be registered here
PARSERS = {"html.parser": _Extractor}


def _line_col(text, pos):
    line = text.count("\n", 0, pos) + 1
    return line, pos - (text.rfind("\n", 0, pos) + 1)


def template_references(text, source_file):
    """Conservative pass over raw template text (separate from the HTML parse).  Dynamic expressions are
    retained with a null target and resolution_status 'dynamic'.  Django comments are ignored; constructs inside
    HTML comments are kept but flagged ``in_html_comment``."""
    text = _mask(_DJ_COMMENT, text)
    html_comments = [m.span() for m in _HTML_COMMENT.finditer(text)]
    in_c = lambda pos: any(s <= pos < e for s, e in html_comments)
    recs = []

    def base(el, pos, **kw):
        line, col = _line_col(text, pos)
        r = OrderedDict(source_file=source_file, element_type=el, line=line, column=col)
        r.update(kw)
        if in_c(pos):
            r["in_html_comment"] = True
        return r

    for m in _TAG_RE.finditer(text):
        name, rest = m.group(1), m.group(2)
        rel = {"extends": "extends", "include": "includes", "url": "uses_url_name", "static": "uses_static"}.get(name)
        if name == "block":
            recs.append(base("block", m.start(), relationship="defines_block", attribute="name",
                             target=rest.split()[0] if rest.split() else None, target_type="block",
                             resolution_status=_NO_TARGET_STATUS, source="django_tag"))
        elif name == "load":
            recs.append(base("load", m.start(), relationship="loads_library", attribute="libraries",
                             target=rest or None, target_type="template_library",
                             resolution_status="unresolved", source="django_tag"))
        elif rel:
            q = _QUOTED.match(rest)
            ttype = {"extends": "template", "includes": "template", "uses_url_name": "url_name",
                     "uses_static": "static_file"}[rel]
            r = base(name, m.start(), relationship=rel, source="django_tag", raw=m.group(0))
            if q:
                r.update(target=q.group(2), target_type=ttype, resolution_status="unresolved")
                if name in ("url", "include"):
                    r["arguments"] = rest[q.end():].strip()
            else:                                         # variable template name / expression: keep it, do not guess
                r.update(target=None, target_type="dynamic", resolution_status="dynamic", expression=rest)
            recs.append(r)
    for m in _VAR_RE.finditer(text):
        expr = m.group(1).strip()
        recs.append(base("variable", m.start(), relationship="uses_variable", attribute="expression", target=expr,
                         target_type="variable", resolution_status="dynamic", expression=m.group(0),
                         source="django_variable"))
    return recs


def analyze_text(source_file, text, parser_name=PARSER_NAME):
    """Parse text -> (records, issues, stats).  Never raises; recovered findings are kept."""
    issues = []
    masked = _mask(_DJ_COMMENT, text)
    p = PARSERS[parser_name](source_file)
    try:
        p.feed(masked)
        p.close()
    except Exception as e:                                # malformed HTML: keep what was recovered, flag the limitation
        issues.append(f"parser stopped early ({parser_name}): {type(e).__name__}: {e}; "
                      f"findings after that point may be missing")
    issues += p.issues
    tags = template_references(text, source_file)
    # a tag inside an element attribute ({% url %} in href=) is the same occurrence: mark it, never count twice
    seen = {(r["line"], r.get("expression")) for r in p.records if r.get("expression")}
    for t in tags:
        if t.get("raw") and (t["line"], t["raw"]) in seen:
            t["also_in_element"] = True
    records = p.records + tags
    records.sort(key=lambda r: (r["line"], r.get("column", 0)))
    stats = OrderedDict(tags_parsed=p.tags_seen, doctype=p.has_doctype,
                        django_comment_blocks_ignored=len(_DJ_COMMENT.findall(text)))
    for k, el in (("forms", "form"), ("links", "a"), ("scripts", "script"), ("images", "img"), ("iframes", "iframe")):
        stats[k] = sum(1 for r in p.records if r["element_type"] == el)
    stats["stylesheets"] = sum(1 for r in p.records if r.get("resource_type") == "stylesheet")
    stats["controls"] = sum(1 for r in p.records if r.get("relationship") == "has_control")
    stats["has_form"] = stats["forms"] > 0
    return records, issues, stats


def read_text(path):
    """-> (text, issues, error).  Unreadable files are reported, never silently skipped."""
    try:
        with open(path, "rb") as f:
            raw = f.read()
    except OSError as e:
        return "", [], f"{type(e).__name__}: {e}"
    try:
        return raw.decode("utf-8"), [], None
    except UnicodeDecodeError:
        return raw.decode("latin-1"), ["file is not valid UTF-8; decoded as latin-1"], None


def discover_templates(root, paths=None):
    """Design section 4, step 1: an explicit file path, a directory, or a list of candidate files."""
    root = os.path.abspath(root)
    out = []
    for p in ([paths] if isinstance(paths, str) else (paths or [root])):
        full = p if os.path.isabs(p) else os.path.join(root, p)
        if os.path.isdir(full):
            for dp, dn, fn in os.walk(full):
                dn[:] = sorted(d for d in dn if d not in EXCLUDE_DIRS)
                out += [os.path.relpath(os.path.join(dp, f), root).replace(os.sep, "/")
                        for f in sorted(fn) if f.lower().endswith(TEMPLATE_EXTENSIONS)]
        else:
            out.append(os.path.relpath(full, root).replace(os.sep, "/") if os.path.isabs(full) or os.path.exists(full)
                       else p.replace("\\", "/"))
    return list(OrderedDict.fromkeys(out))


def analyze_files(root, paths=None):
    """Analyse a list of candidate files; one unreadable file never stops the others.
    -> OrderedDict rel_path -> {records, issues, stats, error}"""
    root = os.path.abspath(root)
    res = OrderedDict()
    for rel in discover_templates(root, paths):
        full = os.path.join(root, rel)
        text, issues, err = read_text(full if os.path.isfile(full) else rel)
        if err:
            res[rel] = dict(records=[], issues=[], stats={}, error=err)
            continue
        recs, iss, stats = analyze_text(rel, text)
        complete = complete_html_extraction(rel, text)
        res[rel] = dict(records=recs, issues=issues + iss + complete.get("issues", []),
                        stats=stats, complete_extraction=complete, error=None)
    return res


def template_name_index(root, template_dirs=None):
    """Duplicate template names (design section 9): name -> every candidate path, none discarded."""
    idx = {}
    for rel in discover_templates(root):
        parts = rel.split("/")
        for i, part in enumerate(parts[:-1]):
            if part == "templates":
                idx.setdefault("/".join(parts[i + 1:]), []).append(rel)
    return idx


# ----------------------------------------------------------------------------------------------
# Top-down functionality extraction for templates (HTML-specific counterpart of the Python extractor).
#
# Built ONLY from the trace tree (ROOT -> <template> -> one node per source line -> REFERENCE children), so it
# also works for ``--from-trace``.  A construct is a landmark element (form, header, nav, main, section, ...),
# an inline <script>/<style>, a {% block %}, or the template itself.  A construct + its direct child
# operations (references, form controls, inline script lines) = ONE functionality; nested constructs become
# their own functionality.  File names, line numbers and code are copied verbatim from the tree.
# ----------------------------------------------------------------------------------------------
_TD_LINE = re.compile(r"^L(\d+):\s?(.*)$", re.S)
_TD_OPEN_TAG = re.compile(r"<(form|header|nav|main|section|footer|aside|head|body)\b[^>]*?(/?)>?", re.I)
_TD_CLOSE_TAG = re.compile(r"</(form|header|nav|main|section|footer|aside|head|body)\s*>", re.I)
_TD_BLOCK = re.compile(r"\{%-?\s*block\s+(\w+)")
_TD_ENDBLOCK = re.compile(r"\{%-?\s*endblock\b")
_TD_CONTROL = re.compile(r"<(input|select|textarea|button)\b", re.I)
_TD_REFERENCE = re.compile(r"^REFERENCE:\s*<(\w+)>\s+(\w+)\s*(.*)$", re.S)


def _tdh_ref(n):
    return OrderedDict([("node_id", n["id"]), ("file", n["file"]), ("line", n["line"]), ("code", n["code"])])


def _tdh_text(n):
    m = _TD_LINE.match(n.get("code", ""))
    return m.group(2) if m else n.get("code", "")


def _tdh_op(n, kind):
    d = _tdh_ref(n)
    d["kind"], d["depth"] = kind, 1
    m = _TD_REFERENCE.match(n.get("code", ""))
    if m:
        d["element"], d["relationship"], d["target"] = m.group(1), m.group(2), m.group(3).strip()
        d["category"] = m.group(2)
    d["calls"] = []
    return d


def extract_html_topdown(trace_root, project="", entry_point=""):
    """Top-down walk of an HTML / Django template trace tree -> the same result shape as the Python extractor."""
    funcs_raw, accounted, total = [], {}, 0

    def walk(nodes):
        nonlocal total
        for n in nodes:
            total += 1
            walk(n.get("children", []))
    walk(trace_root.get("children", []))

    for tmpl in trace_root.get("children", []):
        lines = tmpl.get("children", [])
        top = {"label": "template", "kind": "template", "construct": "template", "node": tmpl, "ops": [],
               "ancestors": [], "name": entry_point}
        constructs, stack = [top], [top]
        accounted.setdefault(tmpl["id"], "root")

        def open_construct(kind, construct, node, name):
            c = {"kind": kind, "construct": construct, "node": node, "ops": [], "name": name,
                 "ancestors": [x for x in stack]}
            constructs.append(c)
            stack.append(c)
            return c

        def close(match_construct, name=None):
            for i in range(len(stack) - 1, 0, -1):
                if stack[i]["construct"] == match_construct and (name is None or stack[i]["name"] == name):
                    del stack[i:]
                    return

        for ln in lines:
            text = _tdh_text(ln)
            refs = [k for k in ln.get("children", []) if k.get("code", "").startswith("REFERENCE:")]
            inline_script = re.search(r"<(script|style)\b(?![^>]*\bsrc=)[^>]*>(?!.*</\1>)", text, re.I)
            if stack[-1]["construct"] in ("script", "style"):
                cur = stack[-1]
                if re.search(r"</%s\s*>" % cur["construct"], text, re.I):
                    del stack[-1]
                    accounted.setdefault(ln["id"], "markup")
                else:
                    cur["ops"].append(_tdh_op(ln, "script_line" if cur["construct"] == "script" else "style_line"))
                    accounted.setdefault(ln["id"], "operation")
                continue
            for m in _TD_CLOSE_TAG.finditer(text):
                close(m.group(1).lower())
            if _TD_ENDBLOCK.search(text):
                close("block")
            opened = None
            for m in _TD_OPEN_TAG.finditer(text):
                tag = m.group(1).lower()
                if m.group(2) == "/" or re.search(r"</%s\s*>" % tag, text[m.end():], re.I):
                    continue
                opened = open_construct("form" if tag == "form" else "element", tag, ln, tag)
                accounted.setdefault(ln["id"], "root")
            bm = _TD_BLOCK.search(text)
            if bm and not _TD_ENDBLOCK.search(text[bm.end():]):
                opened = open_construct("block", "block", ln, bm.group(1))
                accounted.setdefault(ln["id"], "root")
            if inline_script:
                opened = open_construct("script", inline_script.group(1).lower(), ln, inline_script.group(1).lower())
                accounted.setdefault(ln["id"], "root")
            owner = stack[-1]
            if _TD_CONTROL.search(text) and owner["construct"] == "form" and opened is not owner:
                owner["ops"].append(_tdh_op(ln, "control"))
                accounted.setdefault(ln["id"], "operation")
            for k in refs:                                   # a reference belongs to the construct the line sits in
                tgt = opened if (opened is not None and opened["construct"] == "form"
                                 and "submits_to" in k["code"]) else owner
                tgt["ops"].append(_tdh_op(k, "reference"))
                accounted.setdefault(k["id"], "operation")
            accounted.setdefault(ln["id"], "markup")

        for c in constructs:
            funcs_raw.append(c)

    funcs, number_of = [], {}
    for c in funcs_raw:
        if not c["ops"]:
            accounted[c["node"]["id"]] = "pass_through"       # a construct with no operations of its own
            continue
        number = len(funcs) + 1
        number_of[id(c)] = number
        root = c["node"]
        anc = [a for a in c["ancestors"] if a is not c]
        path = [_tdh_ref(x["node"]) for x in anc if x["node"] is not root and x["construct"] != "template"]
        path = [_tdh_ref(funcs_raw[0]["node"])] + path if c is not funcs_raw[0] else []
        path.append(_tdh_ref(root))
        code = "\n".join([root["code"]] + ["    " + o["code"] for o in c["ops"]])
        tree = ["ROOT", "│"]
        prefix = ""
        for i, n in enumerate(path):
            tree += [f"{prefix}└── {n['file']}:{n['line']}", f"{prefix}    {n['code']}"]
            prefix += "    "
        for j, o in enumerate(c["ops"]):
            br = "└── " if j == len(c["ops"]) - 1 else "├── "
            tree += [f"{prefix}{br}{o['file']}:{o['line']}", f"{prefix}    {o['code']}"]
        parent = next((number_of[id(a)] for a in reversed(anc) if id(a) in number_of), None)
        f = OrderedDict([
            ("functionality_number", number), ("functionality_id", f"TDF_{number:06d}"),
            ("kind", c["kind"]), ("construct", c["construct"]),
            ("root", _tdh_ref(root)), ("header_lines", []), ("tree_node_id", root["id"]), ("previous_sibling", None),
            ("path", path), ("path_text", "ROOT -> " + " -> ".join(f"{p['file']}:{p['line']}" for p in path)),
            ("children", c["ops"]), ("called_functions", []),
            ("parent_functionality", parent), ("child_functionalities", []), ("code", code),
            ("tree_path", "\n".join(tree)), ("language", "HTML")])
        funcs.append(f)
        if parent:
            funcs[parent - 1]["child_functionalities"].append(number)
    for f in funcs:
        accounted[f["root"]["node_id"]] = "root"
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
    return OrderedDict([("project", project), ("entry_point", entry_point), ("language", "HTML"),
                        ("traversal", "top-down from ROOT, depth-first, children in tree order"),
                        ("statistics", stats), ("functionalities", funcs)])


def render_html_topdown_text(result):
    bar, sub = "=" * 100, "-" * 100
    st = result["statistics"]
    o = [bar, "TOP-DOWN FUNCTIONALITY EXTRACTION (HTML / Django template)", bar,
         f"Project        : {result['project']}", f"Entry point    : {result['entry_point']}",
         f"Traversal      : {result['traversal']}",
         f"Functionalities: {st['functionalities']}   (" + ", ".join(f"{k}={v}" for k, v in st["by_kind"].items()) + ")",
         f"Code nodes     : {st['code_nodes_accounted']} accounted of {st['code_nodes']}", "",
         "Rule: a construct (template, landmark element, form, block, inline script) + its direct child operations",
         "      (references, form controls, script lines) = ONE functionality. Nested constructs are their own.", "",
         "INDEX", sub]
    for f in result["functionalities"]:
        r = f["root"]
        o.append(f"  #{f['functionality_number']:<4} {r['file']}:{r['line']:<5} {f['kind']:<10} "
                 f"{len(f['children']):>3} op(s)   {r['code'][:60]}")
    o.append("")
    for f in result["functionalities"]:
        r = f["root"]
        o += [bar, f"FUNCTIONALITY {f['functionality_number']}   [{f['functionality_id']}]", bar,
              f"Kind: {f['kind']} ({f['construct']})", "", "2. TOP-DOWN PATH (ROOT -> functionality)", "   ROOT"]
        o += [f"   -> {p['file']}:{p['line']:<5} {p['code']}" for p in f["path"]]
        o += ["", "3. FUNCTIONALITY ROOT", f"   file : {r['file']}", f"   line : {r['line']}", f"   code : {r['code']}",
              "", "4. CHILD OPERATIONS"]
        for c in f["children"]:
            o += [f"   file : {c['file']}", f"   line : {c['line']}", f"   code : {c['code']}"]
            if c.get("leads_to"):
                o.append("   leads to: " + ", ".join(c["leads_to"]))
            o.append("")
        o += ["5. RECONSTRUCTED FUNCTIONALITY CODE"] + ["   " + ln for ln in f["code"].splitlines()]
        o += ["", "6. COMPLETE TREE PATH"] + ["   " + ln for ln in f["tree_path"].splitlines()]
        rel = []
        if f["parent_functionality"]:
            rel.append(f"enclosing functionality: #{f['parent_functionality']}")
        if f["child_functionalities"]:
            rel.append("deeper functionalities: " + ", ".join(f"#{n}" for n in f["child_functionalities"]))
        if rel:
            o += ["", "   " + "; ".join(rel)]
        o.append("")
    return "\n".join(o)


class HTMLBroker:
    LANGUAGE = "HTML"
    SUPPORTS_COLLECTOR = True              # app_broker passes collector= (its ONE shared FileCollector) to such brokers

    def __init__(self, root, entry_file, internal_hints, resolve=True, collector=None, **_ignored):
        self.collector = collector         # shared file_collector.FileCollector owned by App Broker (never created here)
        self._discovered = None
        self.root = os.path.abspath(root)
        self.entry = posixpath.normpath(entry_file.replace("\\", "/"))
        self.internal_hints = set(internal_hints)
        self.resolve = resolve
        self.records, self.issues, self.read_error, self.stats = [], [], None, {}
        self.text = ""
        self.complete_document = None
        self._result = None
        self._resolution = None

    @property
    def reachable_count(self):
        return 1 + sum(1 for r in self.records if r.get("relationship") == "defines_block") if self.text else 0

    def _path(self):
        p = os.path.join(self.root, self.entry)
        return p if os.path.isfile(p) else self.entry

    def run(self):
        self.text, issues, err = read_text(self._path())
        if err:
            self.read_error = err
            return
        self.issues += issues
        self.records, iss, self.stats = analyze_text(self.entry, self.text)
        self.complete_document = complete_html_extraction(self.entry, self.text)
        self.issues += iss + self.complete_document.get("issues", [])
        seen = set()
        for r in self.records:                            # duplicate block names are a template defect worth flagging
            if r.get("relationship") == "defines_block" and r["target"] and not r.get("in_html_comment"):
                if r["target"] in seen:
                    self.issues.append(f"line {r['line']}: duplicate block name {r['target']!r}")
                seen.add(r["target"])

    # -- summary ------------------------------------------------------
    def _refs(self):
        return [r for r in self.records if r.get("target") is not None and not r.get("also_in_element")
                and r["relationship"] not in ("has_control", "uses_variable", "defines_block", "loads_library")]

    def summary_lines(self):
        if self.read_error:
            return [f"  could not read {self.entry}: {self.read_error}"]
        refs = self._refs()
        res = self._resolve()
        unresolved = sum(1 for r in refs if self._status(r) == "unresolved")
        resolved = sum(1 for r in refs if self._status(r) == "resolved")
        forms = self.stats.get("forms", 0)
        out = [f"  references: {len(refs)} (resolved: {resolved}, unresolved: {unresolved})  forms: {forms}"
               f"{'' if forms else ' (no form element)'}  controls: {self.stats.get('controls', 0)}",
               f"  template tags: {sum(1 for r in self.records if r.get('source') == 'django_tag')}  "
               f"parser issues: {len(self.issues)}"]
        if res is not None:
            out.append(f"  django project: {res['project'].describe()}")
        return out

    # -- resolution (separate components; optional) ----------------------
    def _resolve(self):
        """Ask django_resolver to verify references.  Returns {project, by_record} or None (not a Django project)."""
        if self._resolution is not None:
            return self._resolution or None
        self._resolution = False
        if not self.resolve or self.read_error:
            return None
        try:
            from django_resolver import DjangoProject, resolve_reference
            proj = DjangoProject.discover(self.root)
            if proj is None:
                return None
            by = {}
            for i, r in enumerate(self.records):
                if r.get("target") is not None and r.get("target_type") and not r.get("in_html_comment") \
                        and r["relationship"] not in ("has_control", "uses_variable", "defines_block", "loads_library"):
                    by[i] = resolve_reference(proj, r["target_type"], r["target"], r["relationship"], self.entry)
            self._resolution = {"project": proj, "by_record": by}
        except Exception as e:                            # resolution must never break parsing
            self.issues.append(f"resolver failed: {type(e).__name__}: {e}")
            return None
        return self._resolution

    def _status(self, r):
        res = self._resolve()
        if res is not None:
            i = next((k for k, x in enumerate(self.records) if x is r), None)
            if i in res["by_record"]:
                return res["by_record"][i]["status"]
        return r.get("resolution_status")

    # -- cross-file discovery (shared FileCollector, owned by App Broker) -------------
    def discovered_references(self):
        """Every reference of this file, classified, with the project files it leads to.

        Item keys: reference (exactly as written), source_file, line, relationship, target_type, kind, disposition,
        files ([project-relative paths to queue]), reason, via (how it was resolved).
          kind        django_route | url_name | template | direct_file | static_asset | external_url | anchor |
                      mailto | tel | javascript | data_uri | dynamic
          disposition queue (files is non-empty) | external | static_asset | ignored | unresolved
        A reference is only given ``files`` when a real project file was found: Django routes through the project's
        URL configuration (django_routes), template names through its ``templates`` directories, plain paths by
        checking the file system.  Anything else is ``unresolved`` with the reason -- no target is invented, and
        a URL is never mapped to a Python file because of a folder name."""
        if self._discovered is not None:
            return self._discovered
        from django_routes import DjangoRouteResolver, TemplateIndex          # local import: no cycles
        routes, templates = DjangoRouteResolver(self.root), TemplateIndex(self.root)
        out = []
        skip = ("has_control", "uses_variable", "defines_block", "loads_library")
        for r in self.records:
            rel = r.get("relationship")
            if not rel or rel in skip or r.get("in_html_comment") or r.get("also_in_element"):
                continue
            ttype, tgt = r.get("target_type"), r.get("target")
            item = OrderedDict(reference=tgt if tgt is not None else (r.get("expression") or ""),
                               source_file=self.entry, line=r.get("line"), relationship=rel, target_type=ttype,
                               kind=ttype, disposition="unresolved", files=[], reason=None, via=None, file_meta={})
            self._classify_reference(item, tgt, ttype, routes, templates)
            out.append(item)
        self._discovered = out
        return out

    def _project_file(self, rel_path):
        """Existing project file (project-relative, '/'-separated) or None; never leaves the project root."""
        rel_path = posixpath.normpath(rel_path)
        if rel_path.startswith("../") or rel_path in ("..", ".") or posixpath.isabs(rel_path):
            return None
        return rel_path if os.path.isfile(os.path.join(self.root, rel_path)) else None

    def _from_route(self, item, res, templates):
        """A Django route / url name -> the files it passes through, in the order a request reaches them:
        the URLconf file(s) that define the matching pattern (root URLconf -> included ``urls.py``), then the
        view file, then any template named by ``as_view(template_name=...)``.  Everything comes from the
        project's real ``urlpatterns``; ``file_meta`` says what role each file plays (urlconf / view / template)."""
        status = res.get("status")
        files, meta = [], {}
        via = {k: res[k] for k in ("route", "namespace", "urlconf", "urlconf_line", "urlconf_chain", "view_symbol",
                                   "view_line", "template_hints", "note") if res.get(k) is not None}

        def add(path, **m):
            if path and path not in files:
                files.append(path)
            if path:
                meta.setdefault(path, {}).update({k: v for k, v in m.items() if v is not None})

        cands = res.get("candidates") or [res]
        matched = [c for c in cands if c.get("urlconf") and not c.get("prefix_only")]
        if status in ("resolved", "ambiguous", "external") and matched:
            for c in matched:                                   # URLconf files first (the route is defined there)
                for uf in c.get("urlconf_chain") or [c["urlconf"]]:
                    add(uf, role="urlconf", route=c.get("route"), url_name=c.get("name"))
        if status in ("resolved", "ambiguous"):
            for c in cands:
                if c.get("view_file"):
                    add(c["view_file"], role="view", view_symbol=c.get("view_symbol"), view_line=c.get("view_line"),
                        route=c.get("route"), url_name=c.get("name"))
        for hint in res.get("template_hints") or []:           # as_view(template_name=...) given in the URLconf
            for t in templates.lookup(hint):
                add(t, role="template", template_name=hint)
        item["via"] = via or None
        item["file_meta"] = meta
        if files:
            item.update(disposition="queue", files=files,
                        reason=res.get("reason") if status == "ambiguous" else None)
        elif status == "external":
            item.update(disposition="external", reason=res.get("reason"))
        else:
            item.update(disposition="unresolved", reason=res.get("reason") or "route could not be resolved")

    def _classify_reference(self, item, tgt, ttype, routes, templates):
        src_dir = posixpath.dirname(self.entry)
        if ttype == "dynamic" or tgt is None:
            item.update(kind="dynamic", disposition="unresolved", reason="dynamic expression: not evaluated")
        elif ttype in _IGNORED_TARGETS:
            item.update(kind=_IGNORED_TARGETS[ttype], disposition="ignored", reason="not a project file")
        elif ttype == "external_url":
            item.update(disposition="external", reason="external URL")
        elif ttype in ("static_resource", "static_file"):
            item.update(kind="static_asset", disposition="static_asset", reason="static asset: nothing to analyse")
        elif ttype == "template":                               # {% extends %} / {% include %}
            files = templates.lookup(tgt)
            if files:
                item.update(disposition="queue", files=files,
                            reason=f"ambiguous: {len(files)} templates share this name" if len(files) > 1 else None)
            else:
                item.update(reason="no HTML template with this name under any 'templates' directory")
        elif ttype == "url_name":                               # {% url 'ns:name' %}
            item["kind"] = "url_name"
            self._from_route(item, routes.resolve_name(tgt), templates)
        elif ttype in ("url", "relative_url"):
            path = urlsplit(tgt).path
            ext = posixpath.splitext(path)[1].lower()
            rel = (path.lstrip("/") if ttype == "url" else posixpath.join(src_dir, path)) if path else ""
            found = self._project_file(rel) if rel and ext else None
            if found and ext in ANALYZABLE_EXTENSIONS:
                item.update(kind="direct_file", disposition="queue", files=[found])
            elif found:
                item.update(kind="static_asset", disposition="static_asset", reason="static asset: nothing to analyse")
            elif ttype == "url":
                item["kind"] = "django_route"
                self._from_route(item, routes.resolve_path(tgt), templates)
            else:
                item.update(kind="direct_file", reason="relative reference does not name a project file "
                                                       "(a relative URL is not resolved as a Django route)")
        else:
            item.update(reason=f"unsupported reference type '{ttype}'")

    def submit_discovered_references(self):
        """Hand resolved project files to the shared collector (App Broker calls this after run()).
        The original reference text and this HTML file travel with each submission.  Returns the number of NEW
        files queued; 0 when no collector was injected."""
        if self.collector is None:
            return 0
        added = 0
        for r in self.discovered_references():
            if r["disposition"] != "queue":
                continue
            for f in r["files"]:
                meta = dict((r.get("file_meta") or {}).get(f, {}), line=r["line"])
                if self.collector.add_path(os.path.join(self.root, f), source_broker="html",
                                           source_file=r["source_file"], original_reference=r["reference"], meta=meta):
                    added += 1
        return added

    # ------------------------------------------------------------------
    def normalized_result(self):
        if self._result is not None:
            return self._result
        name = os.path.basename(self.root) or self.root
        res = new_result(self.LANGUAGE, name, self.root,
                         {"file": self.entry, "label": self.entry, "kind": "template",
                          "resolved_file": self.entry, "via": None, "reason": self.read_error})
        mod = self.entry
        resolution = self._resolve()
        res["files"] = [{"path": self.entry, "module": mod, "reached": True, "analysis_mode": "ast"}]
        tid = f"{self.entry}:<template>"
        base = dict(file=self.entry, module=mod, scope="module", reachable=True, referenced=False,
                    dispatch_target=False, reachability="direct", confidence="high")
        res["symbols"].append(dict(base, id=tid, kind="template", name=os.path.basename(self.entry), line=1, parent=None))
        seen = set()
        for r in self.records:
            if r.get("relationship") == "defines_block" and r["target"] and not r.get("in_html_comment"):
                sid = f"{self.entry}:block:{r['target']}"
                if sid in seen:
                    continue
                seen.add(sid)
                res["symbols"].append(dict(base, id=sid, kind="block", name=r["target"], line=r["line"], parent=tid))
        # imported late: project_graph imports this module at the top
        from project_graph import ref_node_id
        rels, nodes = OrderedDict(), OrderedDict()
        nodes[tid] = {"id": tid, "type": "template", "file": self.entry, "line": 1}
        for i, r in enumerate(self.records):
            rel, tgt = r.get("relationship"), r.get("target")
            if not rel or tgt is None or rel == "defines_block" or r.get("in_html_comment"):
                continue
            src = tid
            if rel == "has_control" and r.get("form_line") is not None:
                f = next((x for x in self.records if x["element_type"] == "form" and x["line"] == r["form_line"]), None)
                src = f"{self.entry}:form@{f['line']}" if f else tid
                nodes.setdefault(src, {"id": src, "type": "form", "file": self.entry, "line": r["form_line"]})
            nid = ref_node_id(r["target_type"], tgt, src)
            nodes.setdefault(nid, {"id": nid, "type": r["target_type"], "file": None, "line": None})
            status = r["resolution_status"]
            rr = resolution["by_record"].get(i) if resolution else None
            if rr:
                status = rr["status"]
            occ = {k: v for k, v in r.items() if k not in ("relationship", "target", "attributes", "source", "source_file")
                   and v is not None}
            occ["resolution_status"] = status
            e = rels.setdefault((src, nid, rel), {
                "source": src, "target": nid, "type": rel, "origin": "static", "line": r["line"], "file": self.entry,
                "attributes": {"resolution_status": status, "occurrences": []}})
            e["attributes"]["occurrences"].append(occ)
            if status == "resolved" and e["attributes"]["resolution_status"] != "resolved":
                e["attributes"]["resolution_status"] = "resolved"
        res["relationships"] = list(rels.values())
        res["nodes"] = list(nodes.values())
        res["dependencies"] = []
        # unresolved list = references the resolvers could not verify (design sections 7, 9)
        unresolved = []
        for i, r in enumerate(self.records):
            if r.get("in_html_comment") or r.get("also_in_element"):
                continue
            status = (resolution["by_record"][i]["status"] if resolution and i in resolution["by_record"]
                      else r.get("resolution_status"))
            if r.get("target") is not None and status == "unresolved" and r["relationship"] not in (
                    "defines_block", "loads_library"):
                why = (resolution["by_record"][i].get("reason") if resolution and i in resolution["by_record"] else None) \
                    or f"{r['relationship']} {r['target_type']} awaits a resolver"
                unresolved.append({"file": self.entry, "line": r["line"], "reference": r["target"], "reason": why})
            elif status == "dynamic" and r["relationship"] != "uses_variable":
                unresolved.append({"file": self.entry, "line": r["line"], "reference": r.get("expression") or "",
                                   "reason": "dynamic expression: not evaluated"})
        res["unresolved"] = unresolved
        # Preserve every source line in the execution tree. Semantic references are
        # attached to their source line instead of replacing ordinary HTML content.
        source_lines = (self.complete_document or {}).get("source_lines", [])
        records_by_line = {}
        for r in self.records:
            if r.get("in_html_comment") or r.get("also_in_element"):
                continue
            if r.get("relationship") in (None, "uses_variable"):
                continue
            label = (f"<{r['element_type']}> {r['relationship']} {r.get('target')}"
                     if r.get("target") is not None
                     else f"<{r['element_type']}> {r.get('expression', '')}".strip())
            records_by_line.setdefault(r.get("line", 1), []).append({
                "text": f"REFERENCE: {label}", "file": self.entry,
                "line": r.get("line", 1), "children": [],
            })

        root_label = f"<template {os.path.basename(self.entry)}> ({len(source_lines)} source lines)"
        line_nodes = []
        entries = [{"depth": 0, "file": self.entry, "line": 1, "text": root_label}]
        for source_line in source_lines:
            number = source_line["line_number"]
            raw = source_line["text"]
            # Keep the original newline in source_lines/source_text; omit it only in the
            # human-readable label so the renderer doesn't create an accidental blank row.
            display = raw.rstrip("\r\n")
            node = {
                "text": f"L{number}: {display}", "file": self.entry,
                "line": number, "source_text": raw,
                "children": records_by_line.get(number, []),
            }
            line_nodes.append(node)
            entries.append({"depth": 1, "file": self.entry, "line": number, "text": node["text"]})
            for child in node["children"]:
                entries.append({"depth": 2, "file": self.entry, "line": number, "text": child["text"]})

        res["trace"] = {"entries": entries, "call_categories": []}
        res["execution_tree"] = [{
            "text": root_label, "file": self.entry, "line": 1,
            "children": line_nodes,
        }]
        res["analysis"].update(
            mode="static", partial=bool(self.issues or self.read_error),
            notes=(["trace holds a document outline of the template, not an execution trace",
                    "parse records keep references unresolved until django_resolver verifies them (design sections 2, 7)"]
                   + ([f"read error: {self.read_error}"] if self.read_error else []) + self.issues))
        res["extensions"] = {"html": {"parser": PARSER_NAME, "stats": self.stats,
                                      "complete_extraction": self.complete_document,
                                      "document_tree": (self.complete_document or {}).get("document_tree"),
                                      "source_lines": (self.complete_document or {}).get("source_lines", []),
                                      "records": [dict(r) for r in self.records],
                                      "resolution": ({str(i): {k: v for k, v in d.items()} for i, d in resolution["by_record"].items()}
                                                     if resolution else None)}}
        if self.collector is not None:                    # cross-file traversal: record what the references resolved to
            self._apply_traversal_resolution(res)
        self._result = res
        return res

    def _apply_traversal_resolution(self, res):
        """References that the URL configuration / template index resolved to project files are marked ``resolved``
        (with the files and the route that proves it) on their relationship, and leave the ``unresolved`` list."""
        done = set()
        for item in self.discovered_references():
            if item["disposition"] != "queue" or not item["files"]:
                continue
            for e in res["relationships"]:
                a = e["attributes"]
                hits = [o for o in a.get("occurrences", []) if o.get("line") == item["line"]]
                if e["type"] != item["relationship"] or not hits:
                    continue
                a["resolution_status"] = "resolved"
                a.setdefault("resolved_to", [])
                a["resolved_to"] += [f for f in item["files"] if f not in a["resolved_to"]]
                if item.get("via"):
                    a["resolved_via"] = item["via"]
                for o in hits:
                    o["resolution_status"] = "resolved"
                done.add((item["line"], item["reference"]))
        res["unresolved"] = [u for u in res["unresolved"] if (u["line"], u["reference"]) not in done]

    # -- optional App Broker hooks: top-down functionality extraction (HTML-specific) ----
    def attach_trace_tree(self, root, stats):
        """app_broker built the trace tree from the normalised trace; the top-down extraction reuses it."""
        self.trace_tree_root, self.trace_tree_stats = root, stats

    def topdown_document(self):
        result = extract_html_topdown(self.trace_tree_root, project=os.path.basename(self.root) or self.root,
                                      entry_point=self.entry)
        return {"result": result, "text": render_html_topdown_text(result)}

    @staticmethod
    def topdown_from_trace(doc):
        """``--from-trace``: top-down extraction from an existing trace_tree.json (no repository analysis)."""
        result = extract_html_topdown(doc["root"], project=doc.get("project", ""), entry_point=doc.get("entry_point", ""))
        return {"result": result, "text": render_html_topdown_text(result)}

    # -- optional App Broker hook: M6 ----------------------------------
    def project_graph_document(self, files=None):
        """``files``: every template of a cross-file traversal (App Broker passes them); default = this entry."""
        from project_graph import build_project_graph
        return build_project_graph(self.root, files=list(files) if files else [self.entry], resolve=self.resolve).to_json()
