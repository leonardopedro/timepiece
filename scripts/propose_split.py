#!/usr/bin/env python3
"""Propose a `split_module.py` invocation for a long Lean module.

The header is everything before the first declaration or section comment
(imports, module docstring, `namespace`, `open`s, `noncomputable section` and
the leading `variable`s); the footer is the trailing block of `end`s; the split
points are the top-level `/-! ## …` section comments closest to an even
division of the body.

Usage:  propose_split.py FILE [TARGET_LINES_PER_PART]
"""

import sys

DECL_START = ("/--", "theorem ", "lemma ", "def ", "abbrev ", "structure ",
              "instance ", "class ", "section ", "/-! ", "noncomputable ",
              "local ", "private ", "protected ", "@[")


def main() -> int:
    path = sys.argv[1]
    target = int(sys.argv[2]) if len(sys.argv) > 2 else 300
    lines = open(path).readlines()
    n = len(lines)

    # the header runs to the first declaration or section comment *after* the
    # module's `namespace` (the module docstring sits above it)
    start_at = 0
    for i, l in enumerate(lines, start=1):
        if l.startswith("namespace "):
            start_at = i
            break
    hdr_end = 0
    for i, l in enumerate(lines[start_at:], start=start_at + 1):
        if l.startswith("noncomputable section"):
            continue
        if any(l.startswith(p) for p in DECL_START):
            hdr_end = i - 1
            break
    while hdr_end > 0 and lines[hdr_end - 1].strip() == "":
        hdr_end -= 1

    foot_start = n + 1
    i = n
    while i > 0:
        s = lines[i - 1].strip()
        if s == "" or s.startswith("end"):
            foot_start = i
            i -= 1
        else:
            break

    # candidate split points: top-level `/-! ##` comments
    depth = 0
    cands = []
    for i in range(hdr_end + 1, foot_start):
        l = lines[i - 1]
        if l.startswith("section") or l.startswith("namespace") or l.startswith("noncomputable section"):
            depth += 1
        elif l.startswith("end"):
            depth = max(0, depth - 1)
        elif depth == 0 and l.startswith("/-! ##"):
            cands.append(i)

    body = foot_start - hdr_end - 1
    nparts = max(2, min(5, round(body / target)))
    splits = []
    for k in range(1, nparts):
        want = hdr_end + round(k * body / nparts)
        ok = [c for c in cands if c not in splits]
        if not ok:
            break
        splits.append(min(ok, key=lambda c: abs(c - want)))
    splits = sorted(set(splits))
    if not splits:
        print(f"# {path}: no top-level section comments — split by hand")
        return 0
    print(f"python3 scripts/split_module.py {path} {hdr_end} "
          + " ".join(str(s) for s in splits))
    return 0


if __name__ == "__main__":
    raise SystemExit(main())
