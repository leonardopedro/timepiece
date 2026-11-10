import Mathlib
import BookProof.Sm.ChapterSmFormDomainComparison

/-!
# The quadratic weight: the reverse estimate the corpus already proves

Work order: `SM_ESA_COMPLETION_PLAN.md` §33.

## 1. The question

`FormDomainComparison` (§32) is not proved for the SM's quartic `W`.  Is the *quadratic* case
available, so that the difference between the two is visible?  It is, and the answer is that the
corpus already proves both halves for the harmonic weight, in `ChapterGaussCoreQuadBounds`:

| ingredient | corpus lemma |
| :--- | :--- |
| the graph norm of the comparison | `shiftNorm p = ‖pgLp (harmP p) + pgLp p‖`, with
  `harmP = kinPoly + harmPoly * ·` |
| the potential is bounded by the graph norm |
  `norm_harmPoly_mul_le_shiftNorm : ‖pgLp (harmPoly * p)‖ ≤ 2 * shiftNorm p` |
| the identity is bounded by the graph norm | `norm_pgLp_le_shiftNorm : ‖pgLp p‖ ≤ shiftNorm p` |
| **the reverse (H²) estimate** |
  `norm_kinPoly_le_shiftNorm : ‖pgLp (kinPoly p)‖ ≤ 3 * shiftNorm p` |
| coercivity | `dim_mul_norm_le_shiftNorm : (D/2 + 1) ‖pgLp p‖ ≤ shiftNorm p` |

So for a quadratic weight the whole §31/§32 package is a theorem, not an input.  This section
records the three statements in one place, with the same names and shape as the SM ones, so that
the gap between the two cases is a comparison of hypotheses rather than of prose.

* `reverseEstimate_harm` — the `FormDomainComparison` of §32 at the harmonic weight, `c = 3`;
* `selfBound_harm` — the `PotSelfBound` of §22 at the harmonic weight, `β = 3`;
* `coercive_harm` — the coercivity that §32's `norm_le_shiftNorm_of_coercive` proves for the SM
  comparison, here as the corpus states it.

## 2. Why it does not transfer

The harmonic instance is a statement about the operator `−Δ + harmPoly + 1`, not about
`−Δ_S + W + 1`.  Transferring it needs `‖N_harm p‖ ≤ κ ‖N_W p‖` — a comparison of two graph norms,
which is the same kind of form-domain statement §32 names.  The corpus gives the harmonic instance
because `harmPoly` is quadratic and `norm_sq_harmPoly_mul_le` — the uncertainty bound — controls it
against the oscillator's graph norm; that bound has **no quartic analogue**, and `W` is not
pointwise dominated by `harmPoly` (degree four against degree two).  So nothing here is a step
towards `PotSelfBound` for the SM weight: it is the shape of the argument, complete in the only
case where the corpus's uncertainty bound applies.

Everything here is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmHarmonicReverseEstimate

open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.DegSchrodinger BookProof.GaussCoreQuadBounds BookProof.QgHermiteOscillator

noncomputable section

variable {D : ℕ}

/-! ## 1. The reverse estimate at the harmonic weight -/

/-- **The `H²` estimate at the quadratic weight**: the Laplacian is dominated by the graph norm of
`−Δ + harmPoly + 1` with constant `3`.  This is the harmonic instance of §32's
`FormDomainComparison`, and it is the statement that fails to transfer to the quartic `W`. -/
theorem reverseEstimate_harm (p : MvPolynomial (Fin D) ℂ) :
    ‖pgLp (kinPoly p)‖ ≤ 3 * shiftNorm p :=
  norm_kinPoly_le_shiftNorm p

/-- **The potential term is dominated by the graph norm** with constant `2`. -/
theorem potentialBound_harm (p : MvPolynomial (Fin D) ℂ) :
    ‖pgLp (harmPoly * p)‖ ≤ 2 * shiftNorm p :=
  norm_harmPoly_mul_le_shiftNorm p

/-- **The identity is dominated by the graph norm** with constant `1`. -/
theorem identityBound_harm (p : MvPolynomial (Fin D) ℂ) :
    ‖pgLp p‖ ≤ shiftNorm p :=
  norm_pgLp_le_shiftNorm p

/-! ## 2. The self-bound at the harmonic weight -/

/-- **The `PotSelfBound` of §22 at the quadratic weight**: the potential plus the identity is
dominated by the graph norm of the harmonic comparison with constant `3`.  This is what
`PotSelfBound` would be for a quadratic weight, and it is proved, not assumed. -/
theorem selfBound_harm (p : MvPolynomial (Fin D) ℂ) :
    ‖pgLp (harmPoly * p) + pgLp p‖ ≤ 3 * shiftNorm p := by
  refine (norm_add_le _ _).trans ?_
  have h1 := potentialBound_harm p
  have h2 := identityBound_harm p
  linarith

/-- **Coercivity at the quadratic weight**, with the explicit constant `D/2 + 1`. -/
theorem coercive_harm (p : MvPolynomial (Fin D) ℂ) :
    ((D : ℝ) / 2 + 1) * ‖pgLp p‖ ≤ shiftNorm p :=
  dim_mul_norm_le_shiftNorm p

end

end BookProof.SmHarmonicReverseEstimate
