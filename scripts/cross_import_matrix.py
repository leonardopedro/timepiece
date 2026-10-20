#!/usr/bin/env python3
"""BOOKPROOF_SPLIT_PLAN.md Phase 2.1: the domain x domain cross-import matrix of
`BookProofOperatorCore`.

Each module of the operator core is classified into one of the §2 domains by its
name (first matching rule wins).  The matrix counts direct first-party imports
`importer domain -> imported domain`.  A domain can become an independent lake part
without moving modules only if no other domain's module imports it *and* it imports
nothing but `Toolbox` (and the toolbox imports nothing from it): the seams are where
the off-diagonal entries vanish.

Usage:  python3 scripts/cross_import_matrix.py            (markdown to stdout)
"""
import collections
import os
import re
import sys

sys.path.insert(0, os.path.dirname(os.path.abspath(__file__)))
import import_components as ic  # noqa: E402

# (domain, regex on the module name without the `BookProof.` prefix); first match wins.
RULES = [
    ("RoadmapAudit", r"^ChapterRoadmapAudit$"),
    ("Ns", r"^(ChapterNavierStokes|ChapterNs|NavierStokes)"),
    ("Qg", r"^(ChapterQg|ChapterQuantumGravity|ChapterScalaron|ChapterVielbein|Starobinsky|ChapterGravity|ChapterStarobinsky)"),
    ("Qym", r"^(ChapterYangMills|YangMills)"),
    ("Sm", r"^(ChapterSm|ChapterParity|ChapterElectroweak|ChapterYukawa|ChapterHiggs)"),
    ("Qed", r"^(ChapterQed|ChapterFreeEMField)"),
    ("Sirk", r"^(ChapterSirk|ChapterHashimoto|Hashimoto|Sirk|ChapterRitz|ChapterCrouzeix|ChapterTemple|ChapterKrylov|ChapterGram)"),
    ("Ode", r"^ChapterOde"),
    ("Attention", r"^(ChapterAttention|ChapterCoherent|ChapterSoftmax|ChapterDeepLearning|ChapterThermalMax|ChapterLayerNorm|ChapterMarkovEntropy|ChapterConsciousness|ChapterComputableScarcity)"),
    ("Textbook", r"^Chapter[A-H][0-9]*[a-z]?(Prop[0-9]+)?$"),
    # `Probability/` has no name family: its modules were assigned by reading (Phase 2.2b,
    # `scripts/bookproof_phase2b_move.py`); the rule never matches a flat name.
    ("Probability", r"(?!)"),
    ("Toolbox", r"^(ChapterFarisLavine|FarisLavine|ChapterEsaClosure|EsaClosure|ChapterHermes|ChapterStone|ChapterFriedrichs|ChapterResolvent|ChapterCarleman|ChapterComparison|ChapterKato|ChapterKvnKato|ChapterTensor|ChapterWeyl|ChapterSL2|ChapterFock|ChapterFermionFock|Phys|ChapterPrelude|Prelude|Substrate|ChapterComplexification|ChapterHermite|Hermite|ChapterDegSchrodinger)"),
]
DOMAINS = [d for d, _ in RULES] + ["Other"]


def domain_of(mod):
    parts = mod[len("BookProof."):].split(".")
    if len(parts) > 1 and parts[0] in DOMAINS:
        return parts[0]  # already foldered (Phase 2.2)
    rest = parts[0]
    for d, rx in RULES:
        if re.search(rx, rest):
            return d
    return "Other"


def main():
    core = None
    for comp, _roots in ic.components("BookProof"):
        if ic.component_name(comp) == "BookProofOperatorCore":
            core = comp
    mods = ic.module_files("BookProof")
    inside = set(core)
    dom = {m: domain_of(m) for m in core}
    size = collections.Counter(dom.values())
    mat = collections.Counter()
    for m in core:
        for i in ic.imports_of(mods[m], inside):
            mat[(dom[m], dom[i])] += 1
    used = [d for d in DOMAINS if size[d]]
    print(f"Operator core: {len(core)} modules. Rows import columns (direct imports).\n")
    print("| importer \\ imported | " + " | ".join(f"{d} ({size[d]})" for d in used) + " |")
    print("|---|" + "---|" * len(used))
    for r in used:
        print(f"| **{r}** | " + " | ".join(str(mat[(r, c)] or "·") for c in used) + " |")
    print()
    print("Seam test per domain. The audit gate `RoadmapAudit` imports every area by design "
          "and is ignored as an importer; `Other` is the residue the §2 name families do not "
          "classify:\n")
    print("| domain | modules | inbound from other domains | outbound to non-Toolbox domains | clean cut? |")
    print("|---|---:|---:|---:|---|")
    for d in used:
        inbound = sum(v for (r, c), v in mat.items()
                      if c == d and r not in (d, "RoadmapAudit"))
        out = sum(v for (r, c), v in mat.items() if r == d and c not in (d, "Toolbox"))
        clean = "yes" if inbound == 0 and out == 0 and d != "Toolbox" else "no"
        print(f"| {d} | {size[d]} | {inbound} | {out} | {clean} |")


if __name__ == "__main__":
    main()
