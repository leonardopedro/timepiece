import Mathlib
import BookProof.Sm.ChapterSmDegenerateDoubletConstant

/-!
# The quartic analogue of the uncertainty bound, and why it is not a new input

Work order: `SM_ESA_COMPLETION_PLAN.md` §35.

## 1. What the quadratic bound says

The harmonic case works because of one inequality, `norm_sq_harmPoly_mul_le`:

```text
‖harmPoly · p‖²  ≤  ‖(−Δ + harmPoly) p‖²  +  (d/2) ‖p‖²,
```

i.e. the quadratic potential is controlled by the graph norm of the oscillator **plus an `L²`
remainder**.  The natural quartic analogue, in the same shape, is

```text
‖W · p‖²  ≤  ‖(−Δ_S + W) p‖²  +  C ∑_j ‖∇_j p‖²        (QuarticUncertainty C),
```

with the `L²` remainder of the quadratic case replaced by the Dirichlet energy — the honest
replacement, because `W` has degree four and no `L²` remainder can absorb its growth.

## 2. What can be proved, and the one-sidedness that stops the rest

Expanding `‖(−Δ_S + W)p‖²` turns `QuarticUncertainty` into a statement about the cross term
`2 ℜ⟪W p, −Δ_S p⟫`, and §23's sign identity gives a **lower** bound on that term only.  Hence:

* `quarticUncertainty_of_gradResidual` — §31's gradient-residual condition implies the quartic bound
  with `C = 2`.  So the quartic analogue is *weaker* than the condition §31 isolated: proving it
  is a strictly smaller ask, not the same one.
* The converse **is not available and is not claimed**.  `QuarticUncertainty` supplies a *lower*
  bound on `2 ℜ⟪W p, −Δ_S p⟫`; deriving §31's condition from it requires an *upper* bound with the
  same constant, `2 ℜ⟪W p, −Δ_S p⟫ ≤ −∑_j ‖∇_j p‖² + ∑_j ‖(∂_j W)p‖²`, which the sign identity does
  not give in any module of the corpus.  This is the precise sense in which the sign route is
  one-sided, and it is the obstruction to closing `PotSelfBound` by it.

Two consequences, both worth recording:

1. **The transfer does not happen for free.**  Even with `QuarticUncertainty` in hand, the remainder
   `2 ∑_j ‖∇_j p‖²` has to be absorbed by the graph norm of `−Δ_S + W + 1`, which is §32's
   `FormDomainComparison`.  The quartic analogue of the *uncertainty bound* is therefore not the
   quartic analogue of the *transfer*: the first is weaker than §31's condition, the second is
   exactly `PotSelfBound`.
2. **The `L²` remainder is what the quadratic case really costs.**  For a quadratic weight the
   remainder `(d/2)‖p‖²` is absorbable by the graph norm of `−Δ + harmPoly + 1` (§33's
   `potentialBound_harm`), because that graph norm dominates `‖p‖`.  For the quartic weight the
   remainder is `2 ∑_j ‖∇_j p‖²`, one derivative higher, and that is the whole difference.

Everything here is `sorry`-free and `axiom`-free.  `QuarticUncertainty` is **not** proved, and
`FormDomainComparison` is not derived from it.
-/

namespace BookProof.SmQuarticUncertainty

open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.DegSchrodinger BookProof.GaussCoreQuadBounds
open BookProof.SmComparisonEsa BookProof.SmOneParticle BookProof.SmHamiltonian
open BookProof.SmFarisLavine BookProof.SmKineticElliptic BookProof.SmKineticGarding
open BookProof.SmGaussWeightedIbp BookProof.SmGradInterpolation BookProof.QuadratureEsa

noncomputable section

/-! ## 1. The quartic analogue, stated -/

/-- **The quartic analogue of the harmonic uncertainty bound**: the quartic potential is controlled
by the graph norm of `−Δ_S + W` plus a multiple of the Dirichlet energy.  It is
`norm_sq_harmPoly_mul_le`
with `harmPoly` replaced by `W` and the `L²` remainder replaced by `∑_j ‖∇_j p‖²`, which is the only
remainder available at degree four. -/
def QuarticUncertainty (P : SmParams) (c0 C : ℝ) : Prop :=
  ∀ p : MvPolynomial (Fin 163) ℂ,
    ‖pgLp (smPotPoly P c0 * p)‖ ^ 2
      ≤ ‖pgLp (kinPolyS smS p + smPotPoly P c0 * p)‖ ^ 2
        + C * ∑ j ∈ smS, ‖pgLp (coreD j p)‖ ^ 2

/-! ## 2. The equivalence with §31's residual condition -/

/-! ## 3. The one direction the sign identity does give -/

/-- **§31's residual condition gives the quartic bound with `C = 2`**, by expanding
`‖(−Δ_S + W)p‖²` and applying §26's interpolation to the cross term.  This is the only direction
available: the converse would need an upper bound on `ℜ⟪W p, −Δ_S p⟫` with the same constant, which
the sign identity does not supply. -/
theorem quarticUncertainty_of_gradResidual (P : SmParams) {c0 : ℝ} (hc0 : 1 ≤ c0)
    (h : ∀ p : MvPolynomial (Fin 163) ℂ,
      ∑ j ∈ smS, ‖pgLp (pderiv j (smPotPoly P c0) * p)‖ ^ 2
        ≤ ‖pgLp (kinPolyS smS p)‖ ^ 2
          + 3 * ∑ j ∈ smS, ‖pgLp (coreD j p)‖ ^ 2) :
    QuarticUncertainty P c0 2 := by
  intro p
  have hres := h p
  have hinterp : (∑ j ∈ smS, ‖pgLp (coreD j p)‖ ^ 2)
      ≤ 2 * (inner ℂ (pgLp (smPotPoly P c0 * p)) (pgLp (kinPolyS smS p))).re
        + ∑ j ∈ smS, ‖pgLp (pderiv j (smPotPoly P c0) * p)‖ ^ 2 :=
    dirichlet_le_weighted_form smS (smPotPoly P c0) p
      (realCoeff_smPotPoly P c0) (one_le_polyW_smPotPoly P hc0)
  set G : ℝ := ∑ j ∈ smS, ‖pgLp (coreD j p)‖ ^ 2 with hG
  set Cc : ℝ := ∑ j ∈ smS, ‖pgLp (pderiv j (smPotPoly P c0) * p)‖ ^ 2 with hCc
  set R : ℝ := (inner ℂ (pgLp (smPotPoly P c0 * p)) (pgLp (kinPolyS smS p))).re with hR
  have hres' : Cc ≤ ‖pgLp (kinPolyS smS p)‖ ^ 2 + 3 * G := by
    rw [hCc, hG]
    exact hres
  have hinterp' : G ≤ 2 * R + Cc := by
    rw [hG, hR, hCc]
    exact hinterp
  change ‖pgLp (smPotPoly P c0 * p)‖ ^ 2
    ≤ ‖pgLp (kinPolyS smS p + smPotPoly P c0 * p)‖ ^ 2 + 2 * G
  rw [pgLp_add', norm_add_sq (𝕜 := ℂ), hG]
  simp only [RCLike.re_to_complex]
  have hsym : (inner ℂ (pgLp (kinPolyS smS p)) (pgLp (smPotPoly P c0 * p))).re
      = (inner ℂ (pgLp (smPotPoly P c0 * p)) (pgLp (kinPolyS smS p))).re :=
    inner_re_symm (𝕜 := ℂ) _ _
  rw [hsym]
  linarith

end

end BookProof.SmQuarticUncertainty
