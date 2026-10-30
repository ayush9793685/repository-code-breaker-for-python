# Cross-broker traversal: File Collector + App Broker + Python Broker + HTML Broker

Everything below was verified by running it; see "Test results" for exactly what that does and does not cover.

## Modified / new files

| File | Status | Diff vs. uploaded |
|---|---|---|
| `file_collector.py` | revised (same public API) | +134 / -88 |
| `app_broker.py` | modified | +203 / -30 |
| `html_broker.py` | modified (additive) | +124 / -1 |
| `python_broker.py` | modified (additive, CRLF kept) | +168 / -1 |
| `django_routes.py` | **new** (no broker imports, so no cycles) | - |
| `tests/` | **new**: 29 tests, Django fixture, stand-ins for modules not uploaded | - |

## What changed in each file

**file_collector.py** - API unchanged (`FileCollector(root)`, `add_path`, `add_paths`, `get_next_path`,
`has_pending_paths`, `pending_count`, FIFO, dedupe, root validation, thread-safe). Fixed while validating it:
- Removed the URL-to-file guessing (`/accounts/login/` -> `accounts/urls.py`, `accounts/views.py`, `urls.py`...).
  That was the folder-name assumption the spec forbids. A route is not a file; the collector now takes files.
- Rejects excluded directories (`venv`, `.git`, `node_modules`...) and records every rejection with a reason
  (`rejected()`), instead of silently returning False.
- Keeps traceability: `add_path(..., source_file=, original_reference=)`, `origins_of(path)`.
- Still never runs a broker or analyses anything.

**django_routes.py (new)** - static resolver, nothing is executed. Reads `ROOT_URLCONF`, evaluates `urlpatterns`
(`path/re_path/url`, `include()` by module / tuple / inline list, namespaces + `app_name`, `+=`, list concatenation,
`X.urls`), matches URLs exactly like Django (first match, prefixes joined), follows the view through the URLconf's
imports (incl. `Class.as_view()`, decorator wrappers, one level of re-export), reads `as_view(template_name=)`.
`TemplateIndex` maps template names to files under every `templates/` directory.

**python_broker.py** - existing analysis untouched. Added: `collector=` ctor argument (injected, never created);
`discovered_references()` (project-local imports resolved with the existing strict resolver, plus templates from
`render()/get_template()/render_to_string()/TemplateResponse()`, `template_name =` and `as_view(template_name=)`);
`submit_discovered_references()`; `fork_for_file()` so N discovered files share one repository index.
Stdlib / third-party imports are neither reported nor queued; unresolvable local imports are reported as unresolved.

**html_broker.py** - existing parsing, records, normalized result untouched. Added: `collector=` ctor argument;
`discovered_references()` classifying every reference (django_route, url_name, template, direct_file, static_asset,
external_url, anchor, mailto/tel/javascript/data_uri, dynamic) with the files it leads to; `submit_discovered_references()`.
Original reference text and source HTML file travel with each submission.

**app_broker.py** - default behaviour unchanged. New opt-in `--follow-references` (+ `--max-files`, default 500):
`traverse()` creates exactly one `FileCollector`, queues the entries, and owns the loop
(`get_next_path()` -> detect language -> dispatch -> run existing analysis -> submit discovered references -> repeat
until `None`). Entry outputs are written exactly as before; other files go to `<outdir>/discovered/<file>/`;
`traversal.json` records order, why each file was visited, and all unresolved references. Per-entry error handling was
moved into `_dispatch_entry_guarded` (same messages) so both paths share it.

## Final traversal flow (verified on the fixture)

```
templates/home.html              (entry, HTML Broker)
  -> base.html                   {% extends %}      -> templates/base.html           (HTML)
  -> /accounts/login/            mysite/urls.py -> include("accounts.urls") -> login_view
                                                                           -> accounts/views.py   (Python)
  -> {% url 'accounts:profile' %} resolved by namespace                    -> accounts/views.py   (already queued)
  -> /help/faq/                  mysite/urls.py                            -> pages/views.py      (Python)
  -> about.html                  relative file                             -> templates/about.html (HTML)
accounts/views.py                -> .helpers  -> accounts/helpers.py
                                 -> render(..., "accounts/login.html") / template_name -> both templates (HTML)
pages/views.py                   -> render(..., "faq.html")                -> templates/faq.html  (HTML)
```
9 files, each analysed once. Starting from `accounts/views.py` instead, the traversal goes through the templates,
follows `<a href="/">` back through the URLconf to `pages/views.py`, and reaches `home.html` (Python -> HTML -> route -> Python).

## Test results

`python -m pytest tests -v` -> **29 passed**. They cover all 10 required behaviours (FIFO, dedupe, no reprocessing,
HTML submits, Python submits, dispatch to the right broker, real-URLconf route resolution, templates found via views
then analysed, missing/external/unsafe references, unchanged reports/graphs), plus thread safety, one shared
collector instance, one shared Python index, `--max-files`, and failure isolation. Against the original
`file_collector.py` 18 of them fail, so they do detect the behaviours they claim to.

Baseline comparison (original vs. modified `app_broker.py`, same fixture): outputs for `templates/home.html` and
`accounts/views.py` are byte-identical with and without `--follow-references`; the only diff is the `Generated:` timestamp.

## Limitations - please read

1. **The tests ran against stand-ins.** `normalized`, `broker_common`, `project_tree`, `project_graph`, `file_detector`
   (and `django_resolver`, optional) were not uploaded. `tests/stubs/` provides minimal versions placed at the END of
   `sys.path`, so your real modules win in your checkout. Cross-broker traversal is confirmed with those stand-ins;
   it is **not yet confirmed against your real modules**. Run `python -m pytest tests` in your repo; the baseline
   comparison above is also worth repeating there. Report content produced through stub renderers (trace tree, SVG,
   functionality) is not representative.
2. `--follow-references` is opt-in because it analyses every referenced file separately (an entry that imports 50
   modules yields 50 extra output folders). Flip the default in `main()` if you want it always on.
3. Route resolution happens when a reference is discovered (the queue always holds real files), not when it is dequeued.
   The outcome is the same; it keeps FIFO/dedupe semantics simple.
4. Static analysis limits: `router.urls`, conditional/computed `urlpatterns`, custom path converters, and
   `settings.TEMPLATES["DIRS"]` outside a `templates/` folder are not evaluated; they come back unresolved (the reason
   mentions how many constructs were skipped). Several templates with the same name are all queued and flagged ambiguous.
5. `HTMLBroker`'s existing optional `django_resolver` is untouched and still decides the `resolution_status` in its own
   output; the new `django_routes.py` only feeds the collector. If you prefer one resolver, `_classify_reference` is
   the single place to swap.
6. New code needs Python 3.9+ (`ast.unparse`, `Path.is_relative_to`); tested on 3.12.
7. Only HTML and Python brokers exist; other file types found by references are recorded as skipped.

## References that stay unresolved in the fixture (on purpose)

- `/billing/invoices/` - `billing/` has `urls.py` and `views.py`, but no URLconf includes it. A folder-name rule would
  have queued it; it is reported unresolved: "no urlpattern in mysite/urls.py matches".
- `missing.html` - relative reference that names no file.
- Not queued by design: `https://example.com/...` (external), `#top`, `mailto:`, `/static/...` (assets), `/admin/...`
  (handled by `include(admin.site.urls)`, outside the project).
