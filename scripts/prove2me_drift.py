#!/usr/bin/env python3
"""Mechanical API-drift repairs for the prove2.me conversion (idempotent).

The platform elaborated its modules against a newer Mathlib than this repository's
pin.  The token replacements below map syntax/names of the platform environment to
their equivalents in the pinned Mathlib.  They are applied to every converted module
(`converted/Definitions/`, `converted/Theorems/`, `converted/Prove2me/`); the hand
repairs that need more than a token replacement are listed in `converted/README.md`.
"""
import glob
import os
import re

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))

# (regex, replacement, reason)
DRIFT = [
    (r"(?<![\w.'])convert!", "convert",
     "`convert!` is not a tactic of the pinned Mathlib; `convert` is its pinned equivalent"),
    (r"(?<![\w'])Filter\.limUnder(?![\w'])", "limUnder",
     "`Filter.limUnder` is `limUnder` (root namespace) in the pinned Mathlib"),
    (r"orthogonalProjectionOnto", "orthogonalProjection",
     "`Submodule.orthogonalProjectionOnto` (`E →L K`) is `Submodule.orthogonalProjection` in the pinned Mathlib"),
    (r"(?m)^import Mathlib\.Analysis\.InnerProductSpace\.SingularValues\b.*$",
     "import Prove2me.Shim.SingularValues  -- was `Mathlib.Analysis.InnerProductSpace.SingularValues`",
     "the platform Mathlib file is absent from the pinned Mathlib; see the shim module"),
    (r"(?<![\w'])((?:[\w']+\.)*)(fun_|coe_|mapDomain_|totalDegree_|eval_|continuous_)?finset(Sum|Prod)(_apply|_coeff)?(?![\w'])",
     lambda m: (m.group(0) if (m.group(2), m.group(4)) in ((None, None), ("totalDegree_", None)) and m.group(3) == "Sum"
                else m.group(1) + (m.group(2) or "") + "finset_" + m.group(3).lower() + (m.group(4) or "")),
     "`*finsetSum*` / `*finsetProd*` lemma names of the platform Mathlib are `*finset_sum*` / `*finset_prod*` in the pinned one"),
    (r"(?<![\w'])((?:[\w']+\.)*[\w']*)(setOfPred|ofPred)(?=[_\w']*)", lambda m: m.group(1) + "setOf",
     "`Set.ofPred` names (`mem_ofPred_eq`, `ofPred_mem_eq`, `isCompact_setOfPred_*`) are `setOf` names in the pinned Mathlib"),
    (r"(?<![\w'])(Set\.mem_sdiff|Set\.union_sdiff_cancel|measure_sdiff_null)(?![\w'])",
     lambda m: m.group(1).replace("sdiff", "diff"),
     "set-difference lemmas are named `diff`, not `sdiff`, in the pinned Mathlib"),
    (r"(?<![\w.'])continuous_add_const(?![\w'])", "continuous_add_right",
     "`continuous_add_const` is `continuous_add_right` in the pinned Mathlib"),
    (r"(?<![\w'])PiLp\.norm_single(?![\w'])", "EuclideanSpace.norm_single",
     "`PiLp.norm_single` (for `p = 2`) is `EuclideanSpace.norm_single` in the pinned Mathlib"),
    (r"(?<=\S) using! ", " using ",
     "`simpa ... using!` is platform syntax; the pinned `simpa ... using` is its equivalent"),
    (r"(?<![\w'])continuousOn_iff_continuous_domRestrict(?![\w'])", "continuousOn_iff_continuous_restrict",
     "renamed in the pinned Mathlib"),
    (r"(?<=\))\.domRestrict(?![\w'])", ".restrict",
     "`ContinuousOn.domRestrict` is `ContinuousOn.restrict` in the pinned Mathlib"),
    (r"(?<=[\w'])\.domRestrict⟩", ".restrict⟩",
     "`ContinuousOn.domRestrict` is `ContinuousOn.restrict` in the pinned Mathlib"),
    (r"@\[instance_reducible\]", "@[reducible]",
     "the `instance_reducible` attribute of newer Lean is `reducible` in Lean 4.28.0"),
    (r"ℕ∞ω", "WithTop ℕ∞",
     "the `ℕ∞ω` notation of the platform Mathlib is `WithTop ℕ∞` in the pinned one"),
    (r"set_option backward\.isDefEq\.respectTransparency false in\n", "",
     "the option is unknown to Lean 4.28.0, whose unifier already behaves as with `false`"),
]

# Conversion shims (`converted/Prove2me/Shim/`): platform-Mathlib declarations missing from
# the pinned Mathlib, re-created under their platform names.  A module that mentions one of
# them gets the shim import appended to its import block.
SHIMS = {
    "Prove2me.Shim.MvPolynomial": [r"(?<![\w.'])(MvPolynomial\.)?coeff_pderiv(?![\w'])"],
    "Prove2me.Shim.Poisson": [r"(?<![\w.'])(herglotzRieszKernel|poissonKernel)(?![\w'])"],
    "Prove2me.Shim.SingularValues": [r"\bsingularValues"],
    "Prove2me.Shim.Schwartz": [r"\bcompSubConstCLM"],
    "Prove2me.Shim.Summation": [r"\b(hasSum|tsum)_ite_eq'"],
    "Prove2me.Shim.Integrability": [r"\bintegrableOn_ball_of_norm_le_rpow\b"],
    "Prove2me.Shim.Harmonic": [r"\bhv\.continuousOn\b"],
    "Prove2me.Shim.Discriminant": [r"\b(ModularForm|CuspForm)\.discriminant\b"],
    "Prove2me.Shim.ExteriorAlgebra": [r"\)\.ExteriorAlgebra\b", r"Basis\.ExteriorAlgebra\b"],
    "Prove2me.Shim.Spectrum": [r"roots_charpoly_eq_eigenvalues hn"],
    "Prove2me.Shim.Misc": [r"\blp\.norm_mono\b", r"\bMemℓp\.mono\b", r"memℓp [^\n]*\)\.norm\b",
                           r"\.ringInverse\b", r"\bmul_apply_eq_comp\b", r"\bone_apply_eq_self\b",
                           r"\)\.const_mul [a-zA-Z]\)\.aestronglyMeasurable", r"\)\.norm\.mul_const B\)",
                           r"pvm_projection hP hS\)\.norm_le",
                           r"\bnegMulLog_le_one_sub_self\b", r"\bContinuousLinearMap\.toLinearMap_(one|add|smul|comp)\b",
                           r"\bReal\.sqrt_le_self_iff\b", r"\bisCompactOperator_of_locallyCompactSpace_rng\b",
                           r"\bintervalIntegral_intervalIntegral_swap\b"],
}


def add_shim_imports(path: str, text: str) -> str:
    if "/Prove2me/Shim/" in path:
        return text
    lines = text.split("\n")
    imp = [i for i, l in enumerate(lines) if l.startswith("import ")]
    if not imp:
        return text
    for mod, pats in SHIMS.items():
        if any(l.split()[1] == mod for l in lines if l.startswith("import ")):
            continue
        if any(re.search(p, text) for p in pats):
            lines.insert(imp[-1] + 1, f"import {mod}  -- conversion shim (platform Mathlib API)")
            imp.append(imp[-1] + 1)
    return "\n".join(lines)


def main() -> None:
    n = 0
    for sub in ("Definitions", "Theorems", "Prove2me"):
        for f in glob.glob(os.path.join(ROOT, "converted", sub, "**", "*.lean"), recursive=True):
            s = open(f, encoding="utf-8").read()
            t = s
            for pat, rep, _ in DRIFT:
                t = re.sub(pat, rep, t)
            t = add_shim_imports(f, t)
            if t != s:
                open(f, "w", encoding="utf-8").write(t)
                n += 1
    print(f"patched {n} files")


if __name__ == "__main__":
    main()
