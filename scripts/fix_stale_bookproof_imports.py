#!/usr/bin/env python3
"""Repair `import BookProof.…` lines whose target module lives at another path.

The Phase-1 chapter move (commit 896e994, "phase-1 chapter moves into topical
namespaces") rewrote importer lists to foldered namespaces (`BookProof.Probability.ChapterU`)
for every chapter, but only relocated *some* of the files: the rest are still at
`BookProof/ChapterU.lean`.  Every import naming a foldered path that does not exist is
therefore unresolvable, and `lake build BookProof` cannot start.

This script rewrites such an import to the module's actual path when the file's
**basename** identifies exactly one module in the tree.  Ambiguous or unresolvable
names are reported and left untouched — no guessing.

Usage:
    python3 scripts/fix_stale_bookproof_imports.py --check   # report only, exit 1 on drift
    python3 scripts/fix_stale_bookproof_imports.py           # rewrite in place
"""

from __future__ import annotations

import re
import sys
from collections import defaultdict
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
SCAN_ROOTS = ("BookProof", "Work", "Book", "Singularity", "UsedRoute", "UnusedRoute",
              "RandomMap", "PnpProof", "RiemannProof", "converted", "Audits")
IMPORT_RE = re.compile(r"^import (BookProof\.[A-Za-z0-9_.']+)\s*$")


def module_path(module: str) -> Path:
    return ROOT / (module.replace(".", "/") + ".lean")


def build_index() -> dict[str, list[str]]:
    """basename stem -> every module name in the tree with that stem."""
    index: dict[str, list[str]] = defaultdict(list)
    for base in SCAN_ROOTS:
        top = ROOT / base
        if not top.is_dir():
            continue
        for path in top.rglob("*.lean"):
            if ".lake" in path.parts:
                continue
            rel = path.relative_to(ROOT).with_suffix("")
            module = ".".join(rel.parts)
            index[path.stem].append(module)
    return index


def lean_files() -> list[Path]:
    files: list[Path] = []
    for path in ROOT.rglob("*.lean"):
        if ".lake" in path.parts or ".git" in path.parts:
            continue
        files.append(path)
    return sorted(files)


def main(argv: list[str]) -> int:
    check = "--check" in argv
    index = build_index()

    rewrites: list[tuple[Path, int, str, str]] = []
    unresolved: list[tuple[Path, int, str]] = []
    ambiguous: list[tuple[Path, int, str, list[str]]] = []

    for path in lean_files():
        try:
            text = path.read_text(encoding="utf-8")
        except UnicodeDecodeError:
            continue
        if not text.startswith("import") and "\nimport BookProof" not in text:
            continue
        for lineno, line in enumerate(text.splitlines(), start=1):
            m = IMPORT_RE.match(line)
            if not m:
                continue
            module = m.group(1)
            if module_path(module).is_file():
                continue
            stem = module.rsplit(".", 1)[-1]
            candidates = index.get(stem, [])
            if len(candidates) == 1:
                rewrites.append((path, lineno, module, candidates[0]))
            elif not candidates:
                unresolved.append((path, lineno, module))
            else:
                ambiguous.append((path, lineno, module, candidates))

    for path, lineno, old, cands in ambiguous:
        print(f"[ambiguous] {path.relative_to(ROOT)}:{lineno} {old} -> {cands}")
    for path, lineno, module in unresolved:
        print(f"[unresolved] {path.relative_to(ROOT)}:{lineno} {module}")

    by_file: dict[Path, list[tuple[int, str, str]]] = defaultdict(list)
    for path, lineno, old, new in rewrites:
        by_file[path].append((lineno, old, new))

    print(f"{len(rewrites)} import line(s) in {len(by_file)} file(s) name a moved module")

    if check:
        return 1 if (rewrites or ambiguous or unresolved) else 0

    for path, edits in by_file.items():
        lines = path.read_text(encoding="utf-8").splitlines()
        for lineno, old, new in edits:
            assert lines[lineno - 1].strip() == f"import {old}", (path, lineno)
            lines[lineno - 1] = f"import {new}"
        path.write_text("\n".join(lines) + "\n", encoding="utf-8")
    print(f"rewrote {len(by_file)} file(s)")
    return 0 if not (ambiguous or unresolved) else 2


if __name__ == "__main__":
    sys.exit(main(sys.argv[1:]))
