import BookProof.ChapterBddBelowWallEsa.Part1
import BookProof.ChapterBddBelowWallEsa.Part2

/-!
# `−d²/dx² + V` is essentially self-adjoint for every smooth potential **bounded below**

`BookProof/ChapterScalaronWallEsa.lean` proves essential self-adjointness of `−d²/dx² + V` on
the compactly supported smooth core of `L²(ℝ)` for every smooth `V ≥ 0`, by a convexity
argument: for `V ≥ 0` and `Re z = 0` the modulus square of a classical `L²` solution of
`W'' = (V − z)W` is convex, non-negative and integrable, hence zero.  The convexity breaks as
soon as `V` dips below `0`, and `BookProof/ChapterLimitCircleExample.lean` and
`BookProof/ChapterConformalFiberDeficiency.lean` show the conclusion itself is false for
potentials unbounded below.

This module closes the remaining gap between the two: **bounded below is enough.**  It is the
one-dimensional input of `CONSOLIDATED_PLAN.md`'s QG-2 **Case A** (a potential carried by a
positive-kinetic direction), and together with the Case B counterexamples it makes the sign
dichotomy sharp — for smooth real potentials on the line, boundedness below is what decides
essential self-adjointness on the compactly supported smooth core, and no growth condition
enters on either side.

## The argument (a cutoff energy estimate)

Let `W` be a classical `L²` solution of `W'' = (V − z)W` with `Re z = 0`, `Im z ≠ 0` and
`V ≥ −K`.  For a real `C¹` cutoff `ζ` of compact support, the function `ζ²·conj(W)·W'` has
compact support, so the integral of its derivative vanishes:

`∫ 2ζζ'·conj(W)W' + ∫ ζ²|W'|² + ∫ ζ²(V − z)|W|² = 0`.

* **Real part.**  `∫ ζ²|W'|² + ∫ ζ²V|W|² = −2∫ ζζ'·Re(conj(W)W')`, and the pointwise Young
  inequality `2|ζζ'||W||W'| ≤ ½ζ²|W'|² + 2ζ'²|W|²` turns this into a *uniform* bound
  `∫ ζ_r²|W'|² ≤ 4M²‖W‖² + 2K‖W‖²` for the scaled cutoffs `ζ_r(x) = g(x/r)` (`|ζ_r'| ≤ M/r`).
  This is where `V ≥ −K` is used, and it is the only place.
* **Imaginary part.**  `|Im z|·∫ ζ_r²|W|² = |2∫ ζ_rζ_r'·Im(conj(W)W')| ≤ (1/r)∫ζ_r²|W'|²
  + r∫ζ_r'²|W|² ≤ (C + M²‖W‖²)/r → 0`, while `∫ ζ_r²|W|² ≥ ∫_{[−r,r]}|W|² → ‖W‖²`.  Hence
  `W = 0`.

## What is proved

* `bumpG`, `zeta` — the scaled cutoff family, with `zeta_one`, `hasCompactSupport_zeta` and
  the derivative bound `abs_zeta'_le`;
* `ode_solution_eq_zero_of_bddBelow` — the ODE step: a square-integrable classical solution of
  `W'' = (V − z)W` with `V ≥ −K`, `Re z = 0` and `Im z ≠ 0` vanishes identically;
* `wallHam_deficiencyTrivialAt_of_bddBelow` — hence the deficiency space at such a `z` is
  trivial;
* **`wallHam_essentiallySelfAdjoint_of_bddBelow`** — `−d²/dx² + V` is essentially self-adjoint
  on the compactly supported smooth core for every smooth `V` bounded below;
* `wallHam_essentiallySelfAdjoint_of_bddBelow'` — the same with the hypothesis phrased as
  `BddBelow (Set.range V)`;
* `esa_iff_dichotomy_examples` is *not* claimed: the converse direction is false in general
  (boundedness below is sufficient, not necessary), and no such claim is made here.
-/
