"""
Central FIFO file collector for App Broker.

Purpose:
- Brokers submit file paths they discover (HTML Broker, Python Broker).
- The collector resolves each reference to an existing file inside the project root.
- It deduplicates queued / processed paths.
- App Broker explicitly requests the next path with get_next_path().
- This module does NOT run brokers, execute files, or analyse anything.

Resolution policy (deliberately conservative):
- Route resolution is NOT done here.  A Django URL such as /accounts/login/ cannot be mapped to a file by
  looking at folder names; that needs the project's real urlpatterns (see django_routes.py, used by the HTML
  Broker).  Brokers therefore submit the *files* they resolved (an absolute path or a project-relative path).
- For source_broker="html" a reference is also accepted as a plain relative file reference, resolved against
  the directory of ``source_file`` (when given) and then against the project root.  Query strings and
  fragments are stripped.  URLs with a scheme or host (http:, mailto:, ...) are rejected.
- Anything that is missing, outside project_root, inside an excluded directory, or not a regular file is
  rejected and recorded in ``rejected()`` so that nothing disappears silently.

Traceability: every accepted path remembers who submitted it and the original reference text
(``origins_of``), so App Broker can report why a file was analysed.
"""

from __future__ import annotations

from collections import deque
from pathlib import Path
from threading import Lock
from typing import Iterable, Optional
from urllib.parse import urlsplit

DEFAULT_EXCLUDE_DIRS = frozenset({
    ".git", "__pycache__", "node_modules", ".venv", "venv", "build", "dist", ".tox", ".mypy_cache",
})


def _looks_like_local_path(reference: str) -> bool:
    """True for a filesystem path that urlsplit() would misread as a URL: a Windows drive path (``C:\\x``, ``C:/x``)
    or a UNC path.  Real URL schemes are two or more letters (http, mailto, ...), so a one-letter "scheme" is a drive."""
    ref = reference.strip()
    if len(ref) >= 3 and ref[0].isalpha() and ref[1] == ":" and ref[2] in "\\/":
        return True
    return ref.startswith("\\\\")


class FileCollector:
    """Thread-safe FIFO queue of project files waiting for App Broker."""

    def __init__(self, project_root: str | Path, exclude_dirs: Iterable[str] = DEFAULT_EXCLUDE_DIRS):
        self.project_root = Path(project_root).expanduser().resolve()
        self.exclude_dirs = frozenset(exclude_dirs)
        self._queue: deque[Path] = deque()
        self._queued: set[Path] = set()
        self._processed: set[Path] = set()
        self._origins: dict[Path, list[dict]] = {}
        self._rejected: list[dict] = []
        self._lock = Lock()

    # ------------------------------------------------------------------
    # submitting
    # ------------------------------------------------------------------
    def add_path(
        self,
        reference: str | Path,
        source_broker: str = "python",
        *,
        source_file: str | Path | None = None,
        original_reference: str | None = None,
        meta: dict | None = None,
    ) -> bool:
        """
        Resolve and enqueue a discovered reference.

        Args:
            reference: absolute or project-relative file path; for source_broker="html" also a relative
                file reference as written in the HTML.
            source_broker: "html" or "python" (who found it).
            source_file: the file in which the reference was found (traceability; also the base directory
                for relative HTML references).
            original_reference: the reference as originally written, if ``reference`` is a derived path.
            meta: free-form facts about why the file was submitted (e.g. {"role": "view", "view_symbol": "login"});
                kept with the origin so App Broker can hand them to the broker that analyses the file.

        Returns:
            True if a new existing file was queued; False if it was rejected (see rejected()),
            already queued, or already processed.
        """
        original = original_reference if original_reference is not None else str(reference)
        resolved, reason = self._resolve(reference, source_broker, source_file)
        if resolved is None:
            self._reject(original, source_broker, source_file, reason)
            return False

        origin = {"reference": original, "source_broker": source_broker,
                  "source_file": self._rel(source_file) if source_file else None}
        if meta:
            origin["meta"] = dict(meta)
        with self._lock:
            if resolved in self._queued or resolved in self._processed:
                # still remember that another file also pointed here (traceability), but never re-queue
                self._origins.setdefault(resolved, [])
                if origin not in self._origins[resolved]:
                    self._origins[resolved].append(origin)
                return False
            self._queue.append(resolved)
            self._queued.add(resolved)
            self._origins.setdefault(resolved, []).append(origin)
            return True

    def add_paths(
        self, references: Iterable[str | Path], source_broker: str = "python", **kwargs
    ) -> int:
        """Enqueue multiple references; return the number newly queued."""
        added = 0
        for reference in references:
            if self.add_path(reference, source_broker=source_broker, **kwargs):
                added += 1
        return added

    # ------------------------------------------------------------------
    # resolution
    # ------------------------------------------------------------------
    def resolve_path(
        self, reference: str | Path, source_broker: str = "python",
        source_file: str | Path | None = None,
    ) -> Optional[Path]:
        """Resolve a reference to an existing file inside project_root (None if it cannot be)."""
        return self._resolve(reference, source_broker, source_file)[0]

    def _resolve(self, reference, source_broker, source_file) -> tuple[Optional[Path], str]:
        raw = str(reference).strip()
        if not raw:
            return None, "empty reference"

        if (source_broker or "").lower() == "html":
            candidates, why = self._html_reference_candidates(raw, source_file)
            if not candidates:
                return None, why
        else:
            path = Path(raw).expanduser()
            candidates = [path if path.is_absolute() else self.project_root / path]

        reason = "file does not exist"
        for candidate in candidates:
            try:
                resolved = candidate.resolve()
            except (OSError, RuntimeError, ValueError):
                continue
            if not resolved.is_relative_to(self.project_root):
                reason = "outside the project root"
                continue
            if any(part in self.exclude_dirs for part in resolved.relative_to(self.project_root).parts[:-1]):
                reason = "inside an excluded directory"
                continue
            if resolved.is_file():
                return resolved, ""
        return None, reason

    def _html_reference_candidates(self, reference: str, source_file) -> tuple[list[Path], str]:
        """Plain file-reference candidates for a reference written in HTML.

        No Django/URL guessing: a route is not a file.  Candidates, in order: relative to the directory of the
        referencing file, then relative to the project root.  An absolute filesystem path is used as-is.
        """
        if _looks_like_local_path(reference):
            # A Windows path such as C:\\proj\\accounts\\urls.py parses as a URL with scheme "c": it is a file path
            route = reference.strip()
        else:
            parsed = urlsplit(reference)
            if parsed.scheme or parsed.netloc:
                return [], "external or non-file URL"
            route = parsed.path.strip()
        if not route:
            return [], "fragment-only or empty reference"
        as_path = Path(route)
        if as_path.is_absolute() and (as_path == self.project_root or self.project_root in as_path.parents):
            return [as_path], ""
        candidates: list[Path] = []
        if source_file is not None and not route.startswith("/"):
            base = Path(source_file)
            if not base.is_absolute():
                base = self.project_root / base
            candidates.append(base.parent / route)
        candidates.append(self.project_root / route.lstrip("/"))
        return candidates, ""

    def _rel(self, path) -> str:
        p = Path(path)
        if not p.is_absolute():
            return p.as_posix()
        try:
            return p.resolve().relative_to(self.project_root).as_posix()
        except (ValueError, OSError):
            return p.as_posix()

    def _reject(self, reference, source_broker, source_file, reason) -> None:
        with self._lock:
            self._rejected.append({
                "reference": reference, "source_broker": source_broker,
                "source_file": self._rel(source_file) if source_file else None, "reason": reason})

    # ------------------------------------------------------------------
    # queue access (App Broker only)
    # ------------------------------------------------------------------
    def get_next_path(self) -> Optional[Path]:
        """
        Pop the oldest queued path and mark it processed.

        App Broker calls this when it is ready to dispatch the next file to the appropriate broker.
        Returns None when the queue is empty.
        """
        with self._lock:
            if not self._queue:
                return None
            path = self._queue.popleft()
            self._queued.discard(path)
            self._processed.add(path)
            return path

    def has_pending_paths(self) -> bool:
        with self._lock:
            return bool(self._queue)

    def pending_count(self) -> int:
        with self._lock:
            return len(self._queue)

    def is_processed(self, reference: str | Path) -> bool:
        resolved = self.resolve_path(reference, source_broker="python")
        if resolved is None:
            try:
                candidate = Path(reference).expanduser()
                if not candidate.is_absolute():
                    candidate = self.project_root / candidate
                resolved = candidate.resolve()
            except (OSError, RuntimeError, ValueError):
                return False
        with self._lock:
            return resolved in self._processed

    def mark_processed(self, reference: str | Path) -> bool:
        """Mark an existing project file processed without dequeuing it."""
        resolved = self.resolve_path(reference, source_broker="python")
        if resolved is None:
            return False
        with self._lock:
            self._queued.discard(resolved)
            try:
                self._queue.remove(resolved)
            except ValueError:
                pass
            self._processed.add(resolved)
        return True

    # ------------------------------------------------------------------
    # diagnostics / traceability
    # ------------------------------------------------------------------
    def origins_of(self, path: str | Path) -> list[dict]:
        """Who submitted this path: [{reference, source_broker, source_file}, ...] (oldest first)."""
        resolved = self.resolve_path(path, source_broker="python")
        if resolved is None:
            return []
        with self._lock:
            return [dict(o) for o in self._origins.get(resolved, [])]

    def rejected(self) -> list[dict]:
        """References that could not be queued (missing / outside root / excluded / external)."""
        with self._lock:
            return [dict(r) for r in self._rejected]

    def snapshot(self) -> dict[str, object]:
        """Return a read-only-style diagnostic snapshot useful for logging."""
        with self._lock:
            return {
                "project_root": str(self.project_root),
                "pending": [str(path) for path in self._queue],
                "processed_count": len(self._processed),
                "queued_count": len(self._queued),
                "rejected_count": len(self._rejected),
            }


if __name__ == "__main__":
    import argparse

    parser = argparse.ArgumentParser(description="Test the central file collector.")
    parser.add_argument("project_root", help="Path to the project being analyzed")
    parser.add_argument(
        "--add",
        action="append",
        default=[],
        metavar="PATH",
        help="Project-relative path to enqueue (may be supplied more than once)",
    )
    args = parser.parse_args()

    collector = FileCollector(args.project_root)
    for item in args.add:
        print(f"queued={collector.add_path(item, source_broker='python')} path={item}")

    print("snapshot:", collector.snapshot())
    while collector.has_pending_paths():
        print("next:", collector.get_next_path())
