#!/usr/bin/env python3
"""Split a long Lean module into sequential parts, keeping the original module
name as a thin re-export.

A module `BookProof/ChapterFoo.lean` becomes

    BookProof/ChapterFoo/Part1.lean   -- header + first slice  (+ closing `end`s)
    BookProof/ChapterFoo/Part2.lean   -- header + second slice (imports Part1)
    ...
    BookProof/ChapterFoo.lean         -- module docstring + imports of the parts

so that editing one part only recompiles that part and the parts after it,
instead of the whole file.  Nothing moves: the parts are verbatim slices of the
original, and the original module name still re-exports all of them.

To keep every slice self-contained the script simulates the scope structure of
the file (`namespace`/`section`/`noncomputable section` and their `end`s) and,
for each part, emits

* the original *header* (imports, docstring, namespace, `open`s, …),
* a prologue that re-opens the scopes that are open at the split point and
  repeats the `open`s and the (mentioned) `variable`s still in scope there,
* the slice itself,
* an epilogue closing whatever is still open at the end of the slice.

Usage:
    split_module.py FILE HEADER_END SPLIT_LINE [SPLIT_LINE ...]

`HEADER_END` is the last line (1-indexed, inclusive) of the header and each
`SPLIT_LINE` the first line of a new part.
"""

import os
import re
import sys

BINDER = re.compile(r"[({\[]\s*([^:()\[\]{}]+?)\s*:")
SCOPE_OPEN = re.compile(r"^(?:noncomputable\s+)?(namespace|section)\b\s*([^\s]*)")


def binder_names(var_line: str) -> list[str]:
    names: list[str] = []
    for group in BINDER.findall(var_line):
        names.extend(n for n in group.split() if n != "_")
    return names


class Frame:
    def __init__(self, opener: str, name: str) -> None:
        self.opener = opener          # the source line that opened the scope
        self.name = name              # "" for an anonymous section
        self.opens: list[str] = []    # `open …` commands issued in this scope
        self.vars: list[str] = []     # `variable …` commands issued in this scope


def simulate(lines: list[str], upto: int) -> list[Frame]:
    """The scope stack after elaborating `lines[:upto]` (a list of `Frame`s)."""
    stack: list[Frame] = [Frame("", "<file>")]
    in_doc = False
    for line in lines[:upto]:
        stripped = line.rstrip("\n")
        if in_doc:
            if stripped.endswith("-/"):
                in_doc = False
            continue
        if stripped.startswith("/-"):
            if not stripped.endswith("-/"):
                in_doc = True
            continue
        m = SCOPE_OPEN.match(stripped)
        if m:
            stack.append(Frame(stripped + "\n", m.group(2)))
        elif stripped.startswith("end"):
            if len(stack) > 1:
                stack.pop()
        elif stripped.startswith("open ") and " in" not in stripped:
            stack[-1].opens.append(stripped + "\n")
        elif stripped.startswith("variable"):
            stack[-1].vars.append(stripped + "\n")
    return stack


def main() -> int:
    if len(sys.argv) < 4:
        print(__doc__)
        return 1
    path = sys.argv[1]
    hdr_end = int(sys.argv[2])
    splits = [int(a) for a in sys.argv[3:]]

    with open(path) as f:
        lines = f.readlines()

    header = lines[:hdr_end]
    imports = [l for l in header if l.startswith("import ")]
    rest = [l for l in header if not l.startswith("import ")]

    base = path[: -len(".lean")]           # e.g. BookProof/ChapterFoo
    mod = base.replace("/", ".")           # e.g. BookProof.ChapterFoo
    os.makedirs(base, exist_ok=True)

    hdr_stack = simulate(lines, hdr_end)
    bounds = [hdr_end + 1] + splits + [len(lines) + 1]
    nparts = len(bounds) - 1
    for i in range(nparts):
        start, stop = bounds[i], bounds[i + 1]
        body = lines[start - 1: stop - 1]
        text = "".join(body)
        part_imports = list(imports)
        if i > 0:
            part_imports.append(f"import {mod}.Part{i}\n")

        start_stack = simulate(lines, start - 1)
        prologue: list[str] = []
        # close the header scopes that the earlier slices have already closed
        for frame in reversed(hdr_stack[len(start_stack):]):
            prologue.append(f"end {frame.name}\n" if frame.name else "end\n")
        # re-open the scopes opened by the earlier slices, with their `open`s …
        for depth, frame in enumerate(start_stack):
            if depth >= len(hdr_stack):
                prologue.append(frame.opener)
            if depth == 0:
                continue
            prologue.extend(o for o in frame.opens if o not in rest)
            prologue.extend(
                v for v in frame.vars
                if v not in rest and any(
                    re.search(rf"(?<![\w']){re.escape(n)}(?![\w'])", text)
                    for n in binder_names(v)))

        end_stack = simulate(lines, stop - 1)
        epilogue = [f"end {f.name}\n" if f.name else "end\n"
                    for f in reversed(end_stack[1:])]

        out = part_imports + rest
        if prologue:
            out += ["\n"] + prologue
        out += body
        if epilogue:
            out += ["\n"] + epilogue
        with open(f"{base}/Part{i + 1}.lean", "w") as f:
            f.writelines(out)

    root = [f"import {mod}.Part{i + 1}\n" for i in range(nparts)]
    # keep the original module docstring (the first `/-! … -/` block of the header)
    doc: list[str] = []
    inside = False
    for l in rest:
        if l.startswith("/-!"):
            inside = True
        if inside:
            doc.append(l)
        if inside and l.rstrip().endswith("-/"):
            break
    with open(path, "w") as f:
        f.writelines(root + ["\n"] + doc)
    print(f"split {path} into {nparts} parts")
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
