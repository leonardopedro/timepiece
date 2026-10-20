#!/usr/bin/env python3
"""Make helper declarations that several converted prove2.me solutions repeat verbatim
`private`, so that all conversions can be imported together by the aggregator `Prove2me`.

The prove2.me platform compiles each solution on its own, so two solutions of the same author can
both declare a helper with the same name (`RPL2.g`, `SVDProbe.gram`, `gexp_add`, ...).  Imported
together, these clash ("environment already contains ...").  For each clashing name the first module
(in sorted order) keeps the public declaration; in every other module the declaration is made
`private` (visible in its own file only), which does not change any statement or proof.

Usage: python3 scripts/prove2me_privatize.py CLASHES
where each line of CLASHES is `<full.decl.name> #[Mod.A, Mod.B, ...]` (module names relative to
`converted/`, without the `Prove2me.` prefix), as produced by listing duplicate constant names of
the compiled `.olean` files.
"""
import os, re, sys

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
CONV = os.path.join(ROOT, "converted", "Prove2me")
KW = r"(?:theorem|lemma|def|abbrev|instance|structure|class|inductive)"

def main(path):
    edits = {}
    for line in open(path, encoding="utf-8"):
        line = line.strip()
        if not line:
            continue
        name, mods = line.split(" ", 1)
        mods = [m.strip() for m in mods.strip("#[]").split(",")]
        mods.sort()
        parts = name.split(".")
        suffixes = [".".join(parts[i:]) for i in range(len(parts))]
        for mod in mods[1:]:
            edits.setdefault(mod, []).append((name, suffixes))
    for mod, items in sorted(edits.items()):
        f = os.path.join(CONV, *mod.split(".")) + ".lean"
        text = open(f, encoding="utf-8").read()
        for name, suffixes in items:
            alt = "|".join(re.escape(s) for s in suffixes)
            rx = re.compile(r"(?m)^(\s*(?:@\[[^\]]*\]\s*)?)((?:noncomputable |protected |nonrec )*" + KW +
                            r" (?:" + alt + r"))(?=[\s:({\[])")
            ms = list(rx.finditer(text))
            if len(ms) != 1:
                print(f"SKIP {mod}: {name}: {len(ms)} matches")
                continue
            m = ms[0]
            text = text[:m.start(2)] + "private " + text[m.start(2):]
            print(f"private {mod}: {name}")
        open(f, "w", encoding="utf-8").write(text)

if __name__ == "__main__":
    main(sys.argv[1])
