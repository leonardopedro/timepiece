#!/usr/bin/env python3
"""Comment out helper declarations that a converted solution repeats verbatim from a converted
module it imports (prove2.me conversion; see `converted/README.md`).

On the platform a solution that imports `Theorems.Thm_X` sees only the statement stub of `X`; in
the conversion the import is re-pointed at the converted *solution* of `X`, whose helper lemmas
then become visible and can clash ("has already been declared").  Usage:

    python3 scripts/prove2me_dedup.py BUILD_LOG

For every such error the clashing block is located; if an identical block (same text) occurs in
one of the converted modules the file imports, the duplicate is commented out with a note.
Otherwise the clash is reported and left alone.
"""
import os
import re
import sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CONV = os.path.join(ROOT, "converted")


def block(text, short):
    m = re.search(r"(?m)^(/--(?:(?!-/)[\s\S])*-/\n)?(?:@\[[^\]]*\]\s*)?(?:private |protected |noncomputable )*"
                  r"(?:theorem|lemma|def|abbrev|instance) " + re.escape(short) + r"\b[\s\S]*?(?=\n\n|\n(?=\S)(?!  ))",
                  text)
    return m


def imports(text):
    return [l.split()[1] for l in text.split("\n") if l.startswith("import ")]


def closure(mod, seen):
    if mod in seen:
        return
    path = os.path.join(CONV, *mod.split(".")) + ".lean"
    if not os.path.exists(path):
        return
    seen.add(mod)
    for m in imports(open(path, encoding="utf-8").read()):
        closure(m, seen)


def main(log):
    errs = re.findall(r"error: (converted/\S+\.lean):\d+:\d+: `([^`]+)` has already been declared",
                      open(log, encoding="utf-8").read())
    for rel, full in errs:
        path = os.path.join(ROOT, rel)
        text = open(path, encoding="utf-8").read()
        short = full.split(".")[-1]
        m = block(text, short)
        if not m:
            print("no block", rel, full)
            continue
        blk = m.group(0)
        seen = set()
        for imp in imports(text):
            closure(imp, seen)
        src = None
        for mod in sorted(seen):
            p = os.path.join(CONV, *mod.split(".")) + ".lean"
            t = open(p, encoding="utf-8").read()
            mm = block(t, short)
            is_def = re.search(r"\b(def|abbrev|instance) " + re.escape(short) + r"\b", blk) is not None
            same = (mm.group(0).strip() == blk.strip()) if (mm and is_def) else \
                (mm is not None and mm.group(0).split(":=")[0].strip() == blk.split(":=")[0].strip())
            if same:
                src = mod
                break
        if not src:
            print("not identical, left alone:", rel, full)
            continue
        new = (f"-- conversion: `{short}` is already declared, with the same statement, by the imported converted\n"
               f"-- module `{src}`; the duplicate is commented out.\n/-\n" + blk + "\n-/")
        text = text[:m.start()] + new + text[m.end():]
        open(path, "w", encoding="utf-8").write(text)
        print("deduplicated", rel, full, "<-", src)


if __name__ == "__main__":
    main(sys.argv[1])
