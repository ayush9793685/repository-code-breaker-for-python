# PatchPlus App Broker

**Turn a code repository into machine-readable, LLM-ready context.**

Large language models struggle with repositories because understanding one function often means
opening five other files and mentally linking imports, calls, and class hierarchies. The App Broker
does that linking *ahead of time*. You point it at an entry file; it statically traces the program
from there and writes out a structured description of what runs, in what order, and what each
piece does. You hand that output to Claude, ChatGPT, or any other LLM instead of the raw source tree.

No code is executed and no source file is ever modified. Analysis is purely static.

---

## What it produces

For each entry file, the broker writes a set of files into the output directory (default `patchplus_broker/`):

| File | Contents | Best used for |
|---|---|---|
| `trace_tree.json` | The whole reachable program as one nested tree. Each node holds `file`, `line`, and the actual `code` line, with children for the calls it makes. Repeated or recursive calls become `reference` entries instead of being re-expanded. | **The main "give this to an LLM" file.** Execution flow and source lines in one place, no file-hopping. |
| `trace_tree.svg` | Visual rendering of the trace tree | Human review |
| `expanded_trace.txt` | Indented `file:line \| code` listing of the execution trace | Plain-text prompts, diffing |
| `functionality.json` | Functions grouped into semantic clusters (e.g. `UI.RENDERING`, `INPUT.EVENTS`, `PHYSICS.COLLISION`), with the operations that justify each label | High-level "what does this app do" questions |
| `topdown_functionalities.json` / `.txt` | Top-down breakdown of the program's functionality, derived from the trace tree | Architecture summaries |
| `graph.json` | Nodes and edges: calls, imports, inheritance, dynamic dispatch (`DISPATCHES_TO`), each with a resolution status and confidence | Programmatic analysis |
| `index.json` | Index of files and symbols | Lookup |
| `architecture_tree.json` | Project / module structure | Orientation |
| `execution_tree.json` | Raw execution tree | Tooling |
| `report.txt` | Human-readable summary | Quick check |

> **Note:** the output is a *set* of files, with `trace_tree.json` as the closest thing to a single
> consolidated file. If you want one literal file for pasting into a chat, see
> [Roadmap](#roadmap).

### Example `trace_tree.json` shape

```json
{
  "project": "my_game",
  "entry_point": "main.py",
  "statistics": { "trace_entries": 412, "code_nodes": 380, "references": 32 },
  "root": {
    "id": "root",
    "type": "root",
    "children": [
      {
        "id": "node_000001",
        "type": "code",
        "file": "main.py",
        "line": 12,
        "code": "game = Game()",
        "children": [ "..." ]
      }
    ]
  }
}
```

---

## How it works

```
app_broker.py                 language-agnostic orchestration
  ├── CLI arguments, repo path, --entry handling
  ├── language detection      (file_detector: file -> language name)
  ├── language selection      (LANGUAGE_BROKERS: language -> broker class)
  └── dispatch to the selected language broker
        └── python_broker.py  PythonBroker
        └── (future) c_broker.py / cpp_broker.py / java_broker.py
```

`app_broker.py` contains **no language-specific logic**. It detects the language of each entry file
and hands it to the matching broker.

### What the Python broker does

1. **Index** every `.py` file in the repo: symbols (functions, classes, methods) and imports.
2. **Resolve** names across files: imports, relative imports, class bases, method lookup, attribute
   access, and simple dynamic dispatch (dict/list-of-functions tables, callbacks).
3. **Find the entry**: a `__main__` block, or console scripts declared in `setup.py` / `pyproject.toml`.
4. **Trace** execution from the entry, following internal calls and marking stdlib / third-party calls.
5. **Emit** the trace tree, graph, and architecture outputs.
6. **Classify** functions into functionality clusters using API calls, method names, and callee
   behaviour (function names are only a weak hint).

Files that cannot be parsed by the running interpreter's `ast` (typically Python 2 code) are not
skipped: they fall back to a conservative line-based scanner and are labelled
`analysis_mode: "text"` with lower confidence.

Every resolved edge carries a confidence level (`high` / `medium` / `low`) so an LLM can tell what
was proven from what was guessed.

---

## Requirements

- Python 3.8+ (3.11+ recommended; enables `pyproject.toml` entry-point parsing via `tomllib`)
- Local modules the brokers import: `broker_common`, `project_tree`, `file_detector`
- A MongoDB connection for `file_detector` (the language collection). This is imported lazily, so
  `--from-trace` works without it.

> Replace this section with your actual dependency list / `requirements.txt` once finalised.

---

## Usage

```bash
# Analyse a repository from an explicit entry file
python app_broker.py /path/to/repo --entry main.py

# Several entry points; each gets its own subfolder in the output directory
python app_broker.py /path/to/repo --entry main.py --entry src/cli.py

# No --entry: conventional entry files (main, app, index, game, server, cli, manage, ...)
# are discovered automatically
python app_broker.py /path/to/repo

# Mark top-level names as project-internal even if their files are missing
python app_broker.py /path/to/repo --entry main.py --internal mylib helpers

# Custom output directory
python app_broker.py /path/to/repo --entry main.py --outdir out/

# Skip repo analysis; rerun only the top-down functionality extraction on an existing trace
python app_broker.py --from-trace patchplus_broker/trace_tree.json --outdir out/
```

### Options

| Option | Description |
|---|---|
| `root` | Repository path (default `.`) |
| `--entry SOURCE_FILE` | Source file to start analysis from. Repeatable. Language is auto-detected. |
| `--internal NAME ...` | Top-level names that belong to the project |
| `--outdir DIR` | Output directory (default `patchplus_broker`) |
| `--from-trace JSON` | Run only top-down functionality extraction on an existing `trace_tree.json` |

An entry point is always a **source file**, never a function. The broker decides where execution
begins inside it.

---

## Using the output with an LLM

1. Run the broker on your repo.
2. Paste or upload `trace_tree.json` (plus `topdown_functionalities.txt` for a summary) into Claude or ChatGPT.
3. Ask your question, e.g.:

```
The attached trace_tree.json is a static execution trace of my project, starting at main.py.
Each node has file, line, and the source line. Explain how the game loop works, and
where input events are handled.
```

For big repositories, the full tree may exceed a model's context window. In that case start with
`topdown_functionalities.txt` and `functionality.json`, then drill into specific subtrees of
`trace_tree.json`.

---

## Language support

| Language | Status |
|---|---|
| Python | Supported (`python_broker.py`) |
| C, C++, Java, JavaScript | Detected and reported as *"broker not implemented yet"* |

### Adding a language

1. Create `<lang>_broker.py` with a class following the broker contract:

   ```python
   class XBroker:
       def __init__(self, root, entry_file, internal_hints): ...
       def run(self): ...                 # analyse
       def write_outputs(self, outdir): ...   # write the common output files
       @property
       def reachable_count(self): ...     # number of reachable symbols
       def summary_lines(self): ...       # short human-readable result lines
   ```

2. Register it in `LANGUAGE_BROKERS` in `app_broker.py`:

   ```python
   from c_broker import CBroker
   LANGUAGE_BROKERS = {"Python": PythonBroker, "C": CBroker}
   ```

3. Remove the language from `_KNOWN_UNIMPLEMENTED`.

### Extending the functionality classifier

Add entries to `CLUSTER_TAXONOMY` and `FUNCTIONALITY_RULES` in `python_broker.py`. A rule scores
a functionality from its signature (APIs, method calls, attributes, callee clusters).

---

## Limitations

- **Static analysis only.** Highly dynamic code (`eval`, `getattr` with computed names, monkey-patching,
  runtime-generated classes) may be unresolved. These are recorded as unresolved or low-confidence
  rather than silently dropped.
- Test files (`test_*.py`, `*_test.py`) are excluded by default.
- Maximum trace depth is 100.
- Only Python is implemented today.

---

## Roadmap

- [ ] Single-file export (`--bundle`): trace tree, functionality summary, and a project map merged into one document, sized to a token budget
- [ ] C / C++ / Java / JavaScript brokers
- [ ] Make the MongoDB-backed language detector optional (extension-based fallback)
- [ ] `requirements.txt` and tests

---

## License

Add your license here.
