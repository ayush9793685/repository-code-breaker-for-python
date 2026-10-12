"""App Broker: the language-agnostic orchestration layer.

    app_broker.py
        |-- command-line arguments, repository path, --entry handling
        |-- language detection  (file_detector: file -> language name)
        |-- language selection  (LANGUAGE_BROKERS: language name -> broker class)
        +-- dispatch to the selected language broker
              +-- python_broker.py   PythonBroker
              +-- (future) c_broker.py / cpp_broker.py / java_broker.py

No language-specific analysis lives here: no AST parsing and no source-file scanning.
An entry point is a source file only (``main.py``, ``src/game.py``, ``Game.cpp``,
``src/Main.java`` ...).  The entry file path is handed to the selected broker, which analyses
the program starting from that file.

Broker contract (see python_broker.py):

    broker = BrokerClass(root, entry_file, internal_hints)
    broker.run()
    broker.write_outputs(outdir)
    broker.reachable_count
    broker.summary_lines()

To add a language, write ``<lang>_broker.py`` with a class following that contract and register
it in LANGUAGE_BROKERS below, e.g. ``from c_broker import CBroker`` + ``"C": CBroker``.
"""
import argparse
import os
import re
import sys

from broker_common import EXCLUDE_DIRS
from python_broker import PythonBroker, run_topdown_from_trace

# Language name (canonical, as returned by _detect_language) -> broker class.
LANGUAGE_BROKERS = {
    "Python": PythonBroker,
}

# Source-file stems that conventionally start a program.  Only used when no --entry is given;
# the extension is deliberately NOT part of this list - the language detector decides it.
_ENTRY_NAME_STEMS = {"main", "__main__", "app", "index", "program", "game", "run", "server", "cli", "manage"}


class UnsupportedLanguageError(Exception):
    pass


# The Language collection stores its own spellings (e.g. "cpp"); map them onto the canonical names
# the brokers are registered under.  Unknown spellings pass through unchanged.
_LANGUAGE_ALIASES = {
    "python": "Python", "py": "Python",
    "c++": "C++", "cpp": "C++", "cxx": "C++", "cplusplus": "C++",
    "c": "C",
    "java": "Java",
    "javascript": "JavaScript", "js": "JavaScript",
}


def detect_language(path):
    """Answer one question only: which language does this file belong to?  Returns a normalized
    name ("Python", "C", "C++", "Java", ...) or None.  No analysis of the file is performed."""
    # Imported lazily so `--from-trace` keeps working without a MongoDB connection.
    from file_detector import detect_file_type
    language = detect_file_type(path)
    if language is None:
        return None
    return _LANGUAGE_ALIASES.get(str(language).strip().lower(), language)


def discover_entry_files(root):
    """No --entry supplied: collect conventional entry files from the repository.

    A file qualifies if its stem is a conventional entry name AND the detector reports a language
    that has a registered broker.  No file extension is assumed here."""
    found = []
    for dirpath, dirnames, filenames in os.walk(root):
        dirnames[:] = sorted(d for d in dirnames if d not in EXCLUDE_DIRS)
        for fn in sorted(filenames):
            if os.path.splitext(fn)[0].lower() not in _ENTRY_NAME_STEMS:
                continue
            full = os.path.join(dirpath, fn)
            try:
                lang = detect_language(full)
            except (OSError, ValueError):
                continue
            if lang in LANGUAGE_BROKERS or lang in _KNOWN_UNIMPLEMENTED:
                found.append(os.path.relpath(full, root).replace(os.sep, "/"))
    return found


# Languages the detector may report that have no broker yet.  They are still discovered/reported
# (so the user sees "<lang> broker is not implemented yet") but never analysed.
_KNOWN_UNIMPLEMENTED = {"C", "C++", "Java", "JavaScript"}


def obtain_entry_specs(args):
    """Entry file paths exactly as supplied (args.entry is never modified); discovered if none given."""
    if args.entry:
        return list(args.entry)
    root = os.path.abspath(args.root)
    found = discover_entry_files(root)
    if not found:
        raise SystemExit("No entry file found. Pass one or more --entry <source file> "
                         "(any supported language, e.g. main.py, Game.cpp, Main.java).")
    print(f"App Broker: no --entry given; discovered {len(found)} candidate entry file(s): {', '.join(found)}")
    return found


def _entry_outdir(base, entry_file, multiple):
    if not multiple:
        return base
    return os.path.join(base, re.sub(r"[^\w.-]+", "_", entry_file))


def dispatch_entry(root, entry_file, internal, outdir):
    """One entry: file -> language (file_detector) -> broker class (LANGUAGE_BROKERS) -> run."""
    path = os.path.join(root, entry_file)
    if not os.path.isfile(path):
        path = entry_file                      # fall back to a cwd-relative path
    if not os.path.isfile(path):
        raise SystemExit(f"Entry file not found: {entry_file} (looked under {root})")

    language = detect_language(path)
    if language is None:
        raise UnsupportedLanguageError(f"Could not determine the programming language of {entry_file}")

    print(f"App Broker: {entry_file} -> {language}")
    broker_class = LANGUAGE_BROKERS.get(language)
    if broker_class is None:
        raise UnsupportedLanguageError(f"{language} broker is not implemented yet")

    print(f"App Broker: using {language} broker")
    broker = broker_class(root, entry_file, internal)
    broker.run()
    broker.write_outputs(outdir)
    print(f"App Broker: outputs written to {outdir}/")
    for line in broker.summary_lines():
        print(line)
    return broker.reachable_count


def main():
    ap = argparse.ArgumentParser(description="PatchPlus App Broker v2")
    ap.add_argument("root", nargs="?", default=".")
    ap.add_argument("--entry", action="append", default=None, metavar="SOURCE_FILE",
                    help="a source file in any supported language (main.py, Game.cpp, main.c, Main.java, "
                         "app.js, ...) used as the starting point of the analysis; repeat the option for "
                         "several entry points. The language is detected automatically. If omitted, "
                         "conventional entry files are discovered in the repository")
    ap.add_argument("--internal", nargs="*", default=[],
                    help="top-level names that belong to this project (even if files are missing)")
    ap.add_argument("--outdir", default="patchplus_broker")
    ap.add_argument("--from-trace", metavar="TRACE_TREE_JSON",
                    help="skip the repository analysis; run ONLY the top-down functionality extraction "
                         "on an existing trace_tree.json")
    args = ap.parse_args()

    if args.from_trace:
        run_topdown_from_trace(args.from_trace, args.outdir)
        print(f"App Broker: top-down functionalities written to {args.outdir}/")
        return

    root = os.path.abspath(args.root)
    entry_files = obtain_entry_specs(args)
    multiple = len(entry_files) > 1

    failures = []
    for entry_file in entry_files:                 # each entry file is detected + routed independently
        outdir = _entry_outdir(args.outdir, entry_file, multiple)
        try:
            dispatch_entry(root, entry_file, args.internal, outdir)
        except UnsupportedLanguageError as e:
            print(f"App Broker: {e}" if "not implemented yet" in str(e) else f"App Broker: skipped {entry_file}: {e}",
                  file=sys.stderr)
            failures.append(entry_file)
        except SystemExit as e:
            if multiple and e.code not in (None, 0):
                print(f"App Broker: failed {entry_file}: {e.code}", file=sys.stderr)
                failures.append(entry_file)
            else:
                raise
    if failures:
        raise SystemExit(f"App Broker: {len(failures)} of {len(entry_files)} entry file(s) not analysed")


if __name__ == "__main__":
    main()
