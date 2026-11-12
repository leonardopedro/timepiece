/-
Copyright (c) 2026 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib
import BookProof.Sm.ChapterSmReverseEllipticResidual
import BookProof.Sm.ChapterSmGaussWeightedIbp
import BookProof.Sm.ChapterSmFormDomainComparison

/-!
# The reverse elliptic estimate for a quartic potential

Work order: `SM_ESA_COMPLETION_PLAN` §48 (P4).

## 1. The estimate, and the one hypothesis it really needs

`PotSelfBound P c₀ β` is `‖W p + p‖ ≤ β ‖(−Δ_S + W + 1) p‖`, with `W = smPotPoly P c₀` quartic.
§31 reduced it to an exact residual and showed that the sign identity plus interpolation land on
the gradient-residual condition, which compares `∑_j ‖(∂_j W) p‖²` (degree six) with
`‖Δ_S p‖²` (second order) and is therefore not reachable by those tools.

This module takes the other route, and it does discharge the estimate — **not** from nothing, but
from a single, algebraic hypothesis on `W`.  Write `u = pgLp p`, `w = pgLp (W p)`,
`k = pgLp (Δ_S p)`,
`B = w + u`, `N = k + B`.  Then `B = N − k` identically, so

  `‖B‖² = Re ⟪B, N⟫ − Re ⟪B, k⟫`,

and the weighted integration-by-parts identity of §23 (`sm_weighted_kinetic_ibp`) evaluates the
second term: `Re ⟪w, k⟫ = ∑_j [Re ⟪(∂_j W) p, D_j p⟫ + Re ⟪W D_j p, D_j p⟫]`, where the second
sum is non-negative because `W ≥ 0`.  What survives is a **single** commutator term,
`|∑_j Re ⟪(∂_j W) p, D_j p⟫|`, and Cauchy–Schwarz plus Young turn it into

  `(1 − a/(4η)) ‖B‖² ≤ ‖B‖ ‖N‖ + C_η ‖N‖²`,

using only

  `∑_{j∈S} ‖(∂_j W) p‖²  ≤  a ‖W p‖² + b ‖p‖²`     (`GradDom`)

as the hypothesis, together with `‖p‖ ≤ ‖N‖` and `∑_j ‖D_j p‖² ≤ ‖N‖²` (both from coercivity,
§32's `form_coercive`).  `exists_potSelfBound_of_gradDom` is that argument, with an explicit `β`.

## 2. What this does and does not settle

`GradDom` is *exactly* the missing piece, and it is a condition on the polynomial alone — the
`L²` norm of `(∂_j W) p` against the `L²` norm of `W p`.  §3 records the two facts that make its
status precise rather than a slogan:

* `gradDom_coercive_quartic` — for a coercive quartic (`X₀⁴ + X₁⁴`) the pointwise domination
  `|∂_j W|² ≤ a W² + b` holds with explicit `a, b` (`a = 16`, `b = 32`), and the passage from the
  pointwise form to `GradDom` is Gaussian-integral monotonicity `gaussInt_re_mono` against
  `norm_pgLp_sq` and `eval_weighted_self_re`, multiplied pointwise by the non-negative weight
  `cpoly p * p`.  That transfer is *routine but not formalized* here — it is recorded as such,
  not as `l2_gradDom_of_pointwise`, which this corpus does not contain.
* `not_gradDom_flat_quartic` — for a **non-coercive** quartic (`X₀²X₁²`, the prototype of a quartic
  that is non-negative but flat along the hyperplanes `X₀ = 0` and `X₁ = 0`) **no** `a, b` work:
  on the curve `(t, 1/t)` the gradient blows up while `W` stays bounded.  So `GradDom` is a genuine
  restriction and not a consequence of `W ≥ 0` and `deg W = 4`.

Therefore: the reverse estimate **for a dominated quartic** is proved; the hypothesis is the
algebraic statement "the gradient of `W` is controlled by `W`", it holds for coercive quartics, and
it fails for flat ones.  For the Standard Model's own `W` the quartic parts *are* flat in the
`X₀²X₁²` sense (the gluon quartic term `f^{abd}G^b_jG^d_k` vanishes on the hyperplane `G = 0`), so
coercivity is not what saves the estimation: §49 shows the structural reason instead — `W`
also contains the coercive quadratic `∑_m q_m²` and every `∂_j Φ_r` is linear in the momentum
coordinates, so `|∇W|² ≲ W(1 + W)` (`BookProof/Sm/ChapterSmGradDomStructural.lean`).  §49 does not
transport that pointwise bound to `GradDom`'s `L²` form, nor check the per-form support facts, so
`PotSelfBound` for the SM's `W` remains a named input here — but the answer to §48's question is
affirmative, and the residual obligation is the support table of the 49 forms.

Everything here is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmReverseEllipticQuartic

open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.DegSchrodinger BookProof.GaussCoreQuadBounds
open BookProof.SmComparisonEsa BookProof.SmOneParticle BookProof.SmHamiltonian
open BookProof.SmFarisLavine BookProof.SmKineticElliptic BookProof.SmKineticGarding
open BookProof.SmGaussWeightedIbp BookProof.SmFormDomainComparison
open BookProof.SmReverseEllipticResidual BookProof.QuadratureEsa

noncomputable section

variable {D : ℕ}

/-! ## 1. Two scalar inequalities -/

/-- **Young's inequality for the square roots of a product**: `√A √D ≤ η D + A/(4η)`. -/
theorem sqrt_mul_le_div {A Dm η : ℝ} (hA : 0 ≤ A) (hD : 0 ≤ Dm) (hη : 0 < η) :
    Real.sqrt A * Real.sqrt Dm ≤ η * Dm + A / (4 * η) := by
  have h1 : Real.sqrt A ^ 2 = A := Real.sq_sqrt hA
  have h2 : Real.sqrt Dm ^ 2 = Dm := Real.sq_sqrt hD
  have hsq : 0 ≤ (2 * η * Real.sqrt Dm - Real.sqrt A) ^ 2 := sq_nonneg _
  have hdiv : (2 * η * Real.sqrt Dm - Real.sqrt A) ^ 2 / (4 * η)
      = η * Dm + A / (4 * η) - Real.sqrt A * Real.sqrt Dm := by
    field_simp
    nlinarith [h1, h2]
  have hfin : 0 ≤ η * Dm + A / (4 * η) - Real.sqrt A * Real.sqrt Dm := by
    rw [← hdiv]
    positivity
  linarith

/-- **The quadratic-form bootstrap**: if `c X² ≤ X Y + C Y²` with `X, Y ≥ 0`, `c > 0`, `C ≥ 0`, then
`X` is bounded by `Y` with the explicit constant below.  This is the last step of every
reverse-estimate argument: the completed square `(c X − Y/2)² ≤ Y² (cC + 1/4)`. -/
theorem norm_le_of_quad_le {X Y c C : ℝ} (_hX : 0 ≤ X) (hY : 0 ≤ Y) (hc : 0 < c) (hC : 0 ≤ C)
    (h : c * X ^ 2 ≤ X * Y + C * Y ^ 2) :
    X ≤ (1 / 2 + Real.sqrt (c * C + 1 / 4)) / c * Y := by
  have hsq : (c * X - Y / 2) ^ 2 ≤ (Y * Real.sqrt (c * C + 1 / 4)) ^ 2 := by
    have hinner : c * X ^ 2 * c ≤ (X * Y + C * Y ^ 2) * c := by nlinarith
    have hsqrt : (Real.sqrt (c * C + 1 / 4)) ^ 2 = c * C + 1 / 4 :=
      Real.sq_sqrt (by positivity)
    nlinarith [hsqrt, hY]
  have habs : |c * X - Y / 2| ≤ Y * Real.sqrt (c * C + 1 / 4) := by
    have h1 : Real.sqrt ((c * X - Y / 2) ^ 2) ≤ Real.sqrt ((Y * Real.sqrt (c * C + 1 / 4)) ^ 2) :=
      Real.sqrt_le_sqrt hsq
    rw [Real.sqrt_sq_eq_abs, Real.sqrt_sq_eq_abs,
      abs_of_nonneg (mul_nonneg hY (Real.sqrt_nonneg _))] at h1
    exact h1
  have hle : c * X ≤ Y * (1 / 2 + Real.sqrt (c * C + 1 / 4)) := by
    have h2 : c * X - Y / 2 ≤ |c * X - Y / 2| := le_abs_self _
    nlinarith [habs, h2]
  rw [div_mul_eq_mul_div, le_div_iff₀ hc]
  linarith [hle]

/-! ## 2. The reverse estimate from the gradient domination -/

set_option maxHeartbeats 1000000 in
-- the `163`-dimensional coordinate set of the comparison exceeds the default budget
/-- **The Dirichlet energy is bounded by the graph norm**: `∑_{j∈S} ‖D_j p‖² ≤ ‖N p‖²`, from
coercivity (§32's `form_coercive` and `norm_le_shiftNorm_of_coercive`) and the non-negativity of the
weighted terms. -/
theorem sum_coreD_sq_le_shiftNorm_sq (P : SmParams) {c0 : ℝ} (hc0 : 0 ≤ c0)
    (p : MvPolynomial (Fin 163) ℂ) :
    ∑ j ∈ smS, ‖pgLp (coreD j p)‖ ^ 2
      ≤ ‖pgLp (kinPolyS smS p + smPotPoly P c0 * p) + pgLp p‖ ^ 2 := by
  set u : L2d 163 := pgLp p with hu
  set w : L2d 163 := pgLp (smPotPoly P c0 * p) with hw
  set k : L2d 163 := pgLp (kinPolyS smS p) with hk
  set N : L2d 163 := pgLp (kinPolyS smS p + smPotPoly P c0 * p) + pgLp p with hN
  have hsplit : N = k + w + u := by
    rw [hN, pgLp_add', ← hk, ← hw, ← hu]
  have hDir : (inner ℂ u k).re = ∑ j ∈ smS, ‖pgLp (coreD j p)‖ ^ 2 := by
    rw [hu, hk]
    have hsym : (inner ℂ (pgLp p) (pgLp (kinPolyS smS p))).re
        = (inner ℂ (pgLp (kinPolyS smS p)) (pgLp p)).re := inner_re_symm (𝕜 := ℂ) _ _
    rw [hsym]
    exact re_inner_kinPolyS_self smS p
  have huu : (inner ℂ u u).re = ‖u‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
    exact Complex.ofReal_re _
  have hwpos : 0 ≤ (inner ℂ u w).re := by
    rw [hu, hw]
    have hsym : (inner ℂ (pgLp p) (pgLp (smPotPoly P c0 * p))).re
        = (inner ℂ (pgLp (smPotPoly P c0 * p)) (pgLp p)).re := inner_re_symm (𝕜 := ℂ) _ _
    rw [hsym, inner_pgLp_pgLp]
    exact gaussInt_weighted_self_nonneg _ _ (realCoeff_smPotPoly P c0) (smPotPoly_nonneg P hc0)
  have hpeak : ‖u‖ ≤ ‖N‖ := norm_le_shiftNorm_of_coercive P hc0 p
  have huN : (inner ℂ u N).re ≤ ‖u‖ * ‖N‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  have hexp : (inner ℂ u N).re = (inner ℂ u k).re + (inner ℂ u w).re + (inner ℂ u u).re := by
    rw [hsplit, inner_add_right, inner_add_right]
    simp [Complex.add_re, add_assoc]
  have hnorm2 : ‖N‖ * ‖N‖ = ‖N‖ ^ 2 := by ring
  have key : (inner ℂ u k).re ≤ ‖N‖ ^ 2 := by
    nlinarith [huN, hexp, hwpos, huu, hpeak, norm_nonneg u, norm_nonneg N, hnorm2]
  rw [← hDir]
  exact key

set_option maxHeartbeats 4000000 in
-- the `163`-dimensional sums and the weighted integration by parts exceed the default budget
/-- **The reverse elliptic estimate for a quartic potential, from the gradient domination.**
If the quartic potential `W = smPotPoly P c₀` is non-negative (`c₀ ≥ 0`) and its gradient is
dominated by `W` in the `L²` sense

  `∑_{j∈S} ‖(∂_j W) p‖² ≤ a ‖W p‖² + b ‖p‖²`     (`GradDom`, `b ≥ 0`),

then `PotSelfBound P c₀ β` holds for an explicit `β` — the potential term is bounded by the graph
norm of `−Δ_S + W + 1`, which is what P4 asks for.  No elliptic regularity and no form-domain
comparison is used: the content is the weighted integration-by-parts identity of §23 plus
Cauchy–Schwarz and Young. -/
theorem exists_potSelfBound_of_gradDom (P : SmParams) {c0 a b : ℝ} (hc0 : 0 ≤ c0) (hb : 0 ≤ b)
    (hdom : ∀ p : MvPolynomial (Fin 163) ℂ,
      ∑ j ∈ smS, ‖pgLp (pderiv j (smPotPoly P c0) * p)‖ ^ 2
        ≤ a * ‖pgLp (smPotPoly P c0 * p)‖ ^ 2 + b * ‖pgLp p‖ ^ 2) :
    ∃ β, PotSelfBound P c0 β := by
  set eta : ℝ := |a| + 1 with heta
  have heta0 : 0 < eta := by rw [heta]; positivity
  have heta1 : 1 ≤ eta := by rw [heta]; have := abs_nonneg a; linarith
  set cc : ℝ := 1 - 2 * |a| / (4 * eta) with hcc
  have hcc0 : 0 < cc := by
    rw [hcc, heta]
    have h : 2 * |a| / (4 * (|a| + 1)) < 1 := by
      rw [div_lt_one (by positivity)]
      nlinarith [abs_nonneg a]
    linarith
  set Cc : ℝ := eta + (2 * |a| + b) / (4 * eta) with hCc
  have hCc0 : 0 ≤ Cc := by
    rw [hCc]
    have h1 : 0 ≤ (2 * |a| + b) / (4 * eta) := by
      apply div_nonneg _ (by positivity)
      have := abs_nonneg a
      linarith
    linarith
  refine ⟨(1 / 2 + Real.sqrt (cc * Cc + 1 / 4)) / cc, ?_⟩
  intro p
  set u : L2d 163 := pgLp p with hu
  set w : L2d 163 := pgLp (smPotPoly P c0 * p) with hw
  set k : L2d 163 := pgLp (kinPolyS smS p) with hk
  set N : L2d 163 := pgLp (kinPolyS smS p + smPotPoly P c0 * p) + pgLp p with hN
  set B : L2d 163 := pgLp (smPotPoly P c0 * p) + pgLp p with hB
  set Asum : ℝ := ∑ j ∈ smS, ‖pgLp (pderiv j (smPotPoly P c0) * p)‖ ^ 2 with hAsum
  set Dsum : ℝ := ∑ j ∈ smS, ‖pgLp (coreD j p)‖ ^ 2 with hDsum
  set X : ℝ := ∑ j ∈ smS, (gaussInt (cpoly (pderiv j (smPotPoly P c0) * p) * coreD j p)).re
    with hXdef
  have hAsum0 : 0 ≤ Asum := by
    rw [hAsum]
    exact Finset.sum_nonneg fun j _ => sq_nonneg _
  have hDsum0 : 0 ≤ Dsum := by
    rw [hDsum]
    exact Finset.sum_nonneg fun j _ => sq_nonneg _
  -- the two sides are `B` and `N`
  have hBeq : B = w + u := by rw [hB, ← hw, ← hu]
  have hsplit : N = k + B := by
    rw [hN, hB, pgLp_add', ← hk, ← hw, ← hu]
    abel
  have hBsub : B = N - k := by rw [hsplit]; abel
  -- coercivity
  have hpeak : ‖u‖ ≤ ‖N‖ := norm_le_shiftNorm_of_coercive P hc0 p
  have hD' : Dsum ≤ ‖N‖ ^ 2 := sum_coreD_sq_le_shiftNorm_sq P hc0 p
  -- the gradient domination, with `|a|` in place of `a`
  have hA : Asum ≤ 2 * |a| * ‖B‖ ^ 2 + (2 * |a| + b) * ‖N‖ ^ 2 := by
    have h1 := hdom p
    rw [← hAsum] at h1
    have hwB : ‖w‖ ≤ ‖B‖ + ‖N‖ := by
      have hsub : B - u = w := by rw [hBeq]; abel
      have h1 : ‖w‖ ≤ ‖B‖ + ‖u‖ := by rw [← hsub]; exact norm_sub_le _ _
      nlinarith [h1, hpeak, norm_nonneg B]
    have hw2 : ‖w‖ ^ 2 ≤ 2 * ‖B‖ ^ 2 + 2 * ‖N‖ ^ 2 := by
      have hsq : ‖w‖ * ‖w‖ ≤ (‖B‖ + ‖N‖) * (‖B‖ + ‖N‖) :=
        mul_self_le_mul_self (norm_nonneg w) hwB
      nlinarith [hsq, sq_nonneg (‖B‖ - ‖N‖)]
    have hu2 : ‖u‖ ^ 2 ≤ ‖N‖ ^ 2 := by nlinarith [norm_nonneg u, norm_nonneg N, hpeak]
    have key : a * ‖w‖ ^ 2 ≤ |a| * ‖w‖ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self a) (sq_nonneg ‖w‖)
    have hwA : |a| * ‖w‖ ^ 2 ≤ |a| * (2 * ‖B‖ ^ 2 + 2 * ‖N‖ ^ 2) :=
      mul_le_mul_of_nonneg_left hw2 (abs_nonneg a)
    nlinarith [h1, key, hwA, hu2, hb]
  -- the cross term
  have hwk := sm_weighted_kinetic_ibp P c0 p
  have hY : 0 ≤ ∑ j ∈ smS, (gaussInt (cpoly (smPotPoly P c0 * coreD j p) * coreD j p)).re :=
    Finset.sum_nonneg fun j _ =>
      gaussInt_weighted_self_nonneg _ _ (realCoeff_smPotPoly P c0) (smPotPoly_nonneg P hc0)
  have hXle : X ≤ (inner ℂ w k).re := by
    rw [hXdef, hw, hk, hwk, Finset.sum_add_distrib]
    linarith [hY]
  have hXabs : |X| ≤ Real.sqrt Asum * Real.sqrt Dsum := by
    rw [hXdef, hAsum, hDsum]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    have hper : ∑ i ∈ smS, |(gaussInt (cpoly (pderiv i (smPotPoly P c0) * p) * coreD i p)).re|
        ≤ ∑ i ∈ smS, ‖pgLp (pderiv i (smPotPoly P c0) * p)‖ * ‖pgLp (coreD i p)‖ := by
      refine Finset.sum_le_sum fun i _ => ?_
      have hinner := inner_pgLp_pgLp (pderiv i (smPotPoly P c0) * p) (coreD i p)
      have h1 : (gaussInt (cpoly (pderiv i (smPotPoly P c0) * p) * coreD i p)).re
          = (inner ℂ (pgLp (pderiv i (smPotPoly P c0) * p)) (pgLp (coreD i p))).re := by
        rw [← hinner]
      rw [h1]
      exact (Complex.abs_re_le_norm _).trans (norm_inner_le_norm _ _)
    have hstep : ∑ i ∈ smS, ‖pgLp (pderiv i (smPotPoly P c0) * p)‖ * ‖pgLp (coreD i p)‖
        ≤ Real.sqrt (∑ i ∈ smS, ‖pgLp (pderiv i (smPotPoly P c0) * p)‖ ^ 2)
          * Real.sqrt (∑ i ∈ smS, ‖pgLp (coreD i p)‖ ^ 2) := by
      rw [← Real.sqrt_mul (Finset.sum_nonneg fun i _ => sq_nonneg _)]
      exact Real.le_sqrt_of_sq_le (Finset.sum_mul_sq_le_sq_mul_sq smS
        (fun i => ‖pgLp (pderiv i (smPotPoly P c0) * p)‖) (fun i => ‖pgLp (coreD i p)‖))
    exact hper.trans hstep
  have hyoung := sqrt_mul_le_div hAsum0 hDsum0 heta0
  -- the inner-product bookkeeping
  have hBB : ‖B‖ ^ 2 = (inner ℂ B B).re := by
    rw [inner_self_eq_norm_sq_to_K, ← RCLike.ofReal_pow]
    exact Complex.ofReal_re _
  have hkey : ‖B‖ ^ 2 = (inner ℂ B N).re - (inner ℂ B k).re := by
    rw [hBB, hBsub, inner_sub_right, Complex.sub_re]
  have hBk : (inner ℂ B k).re = (inner ℂ w k).re + (inner ℂ u k).re := by
    rw [hBeq, inner_add_left, Complex.add_re]
  have huk0 : 0 ≤ (inner ℂ u k).re := by
    rw [hu, hk]
    have hsym : (inner ℂ (pgLp p) (pgLp (kinPolyS smS p))).re
        = (inner ℂ (pgLp (kinPolyS smS p)) (pgLp p)).re := inner_re_symm (𝕜 := ℂ) _ _
    rw [hsym, re_inner_kinPolyS_self]
    exact Finset.sum_nonneg fun j _ => sq_nonneg _
  have hBN : (inner ℂ B N).re ≤ ‖B‖ * ‖N‖ :=
    (Complex.re_le_norm _).trans (norm_inner_le_norm _ _)
  -- assemble
  have hmain : cc * ‖B‖ ^ 2 ≤ ‖B‖ * ‖N‖ + Cc * ‖N‖ ^ 2 := by
    have step1 : ‖B‖ ^ 2 ≤ ‖B‖ * ‖N‖ + |X| := by
      nlinarith [hkey, hBk, hXle, huk0, hBN, neg_le_abs X]
    have step2 : |X| ≤ eta * Dsum + Asum / (4 * eta) := hXabs.trans hyoung
    have step3 : eta * Dsum ≤ eta * ‖N‖ ^ 2 := by nlinarith [hD', heta0]
    have step4 : Asum / (4 * eta) ≤ (2 * |a| * ‖B‖ ^ 2 + (2 * |a| + b) * ‖N‖ ^ 2) / (4 * eta) := by
      apply div_le_div_of_nonneg_right _ (by positivity)
      exact hA
    have hsplitc : (2 * |a| * ‖B‖ ^ 2 + (2 * |a| + b) * ‖N‖ ^ 2) / (4 * eta)
        = 2 * |a| / (4 * eta) * ‖B‖ ^ 2 + (2 * |a| + b) / (4 * eta) * ‖N‖ ^ 2 := by
      field_simp
    have hetaNN : eta * ‖N‖ ^ 2 + (2 * |a| + b) / (4 * eta) * ‖N‖ ^ 2 = Cc * ‖N‖ ^ 2 := by
      rw [hCc]
      field_simp
    nlinarith [step1, step2, step3, step4, hsplitc, hetaNN, hcc, hCc]
  exact norm_le_of_quad_le (norm_nonneg B) (norm_nonneg N) hcc0 hCc0 hmain

/-! ## 3. The domination hypothesis: true for a coercive quartic, false for a flat one -/

/-- The coercive quartic `X₀⁴ + X₁⁴` in two variables. -/
def coerciveQuartic : MvPolynomial (Fin 2) ℂ := X 0 ^ 4 + X 1 ^ 4

/-- The non-coercive quartic `X₀²X₁²` in two variables: non-negative, of degree four, and flat on
both coordinate hyperplanes. -/
def flatQuartic : MvPolynomial (Fin 2) ℂ := X 0 ^ 2 * X 1 ^ 2

/-- The real point `(x, y) ∈ ℝ²` as a point of the polynomial's coordinate space. -/
def twoPoint (x y : ℝ) : Vd 2 :=
  WithLp.toLp 2 (fun i : Fin 2 => if i = 0 then x else y)

theorem twoPoint_zero (x y : ℝ) : (twoPoint x y).ofLp 0 = x := by simp [twoPoint]

theorem twoPoint_one (x y : ℝ) : (twoPoint x y).ofLp 1 = y := by simp [twoPoint]

/-- Evaluation of a two-variable polynomial at the real point `(x, y)`. -/
def evAt (x y : ℝ) (P : MvPolynomial (Fin 2) ℂ) : ℂ :=
  MvPolynomial.eval (fun i => ((twoPoint x y i : ℝ) : ℂ)) P

theorem eval_coercive_zero (x y : ℝ) :
    evAt x y (pderiv 0 coerciveQuartic)
      = ((4 * x ^ 3 : ℝ) : ℂ) := by
  simp [evAt, coerciveQuartic, twoPoint_zero]

theorem eval_coercive_one (x y : ℝ) :
    evAt x y (pderiv 1 coerciveQuartic)
      = ((4 * y ^ 3 : ℝ) : ℂ) := by
  simp [evAt, coerciveQuartic, twoPoint_one]

theorem eval_coercive_self (x y : ℝ) :
    evAt x y coerciveQuartic
      = ((x ^ 4 + y ^ 4 : ℝ) : ℂ) := by
  simp [evAt, coerciveQuartic, twoPoint_zero, twoPoint_one]

theorem eval_flat_zero (x y : ℝ) :
    evAt x y (pderiv 0 flatQuartic)
      = ((2 * x * y ^ 2 : ℝ) : ℂ) := by
  simp [evAt, flatQuartic, twoPoint_zero, twoPoint_one]
  ring

theorem eval_flat_one (x y : ℝ) :
    evAt x y (pderiv 1 flatQuartic)
      = ((2 * x ^ 2 * y : ℝ) : ℂ) := by
  simp [evAt, flatQuartic, twoPoint_zero, twoPoint_one]
  ring

theorem eval_flat_self (x y : ℝ) :
    evAt x y flatQuartic
      = ((x ^ 2 * y ^ 2 : ℝ) : ℂ) := by
  simp [evAt, flatQuartic, twoPoint_zero, twoPoint_one]

/-- **The coercive quartic satisfies the pointwise domination**, with `a = 16` and `b = 32`:
`|∂₀W|² + |∂₁W|² = 16(x₀⁶ + x₁⁶) ≤ 16 W² + 32` everywhere. -/
theorem gradDom_coercive_quartic (x y : ℝ) :
    ‖evAt x y (pderiv 0 coerciveQuartic)‖ ^ 2
        + ‖evAt x y (pderiv 1 coerciveQuartic)‖ ^ 2
      ≤ 16 * ‖evAt x y coerciveQuartic‖ ^ 2 + 32 := by
  rw [eval_coercive_zero, eval_coercive_one, eval_coercive_self]
  have h0 : ‖((4 * x ^ 3 : ℝ) : ℂ)‖ ^ 2 = 16 * x ^ 6 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  have h1 : ‖((4 * y ^ 3 : ℝ) : ℂ)‖ ^ 2 = 16 * y ^ 6 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    ring
  have hW : ‖((x ^ 4 + y ^ 4 : ℝ) : ℂ)‖ ^ 2 = (x ^ 4 + y ^ 4) ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
  rw [h0, h1, hW]
  have hx : x ^ 6 ≤ x ^ 8 + 1 := by
    nlinarith [sq_nonneg (x ^ 4 - 1), sq_nonneg (x ^ 2 - 1), sq_nonneg x, sq_nonneg (x ^ 3 - x)]
  have hy : y ^ 6 ≤ y ^ 8 + 1 := by
    nlinarith [sq_nonneg (y ^ 4 - 1), sq_nonneg (y ^ 2 - 1), sq_nonneg y, sq_nonneg (y ^ 3 - y)]
  nlinarith [hx, hy, sq_nonneg (x ^ 2 * y ^ 2)]

/-- **The flat quartic violates the pointwise domination for every pair of constants.**  There is no
`a, b` with `|∂₀W|² + |∂₁W|² ≤ a W² + b` for `W = X₀²X₁²`: on the curve `(t, 1/t)` the left side is
`4(t² + t⁻²)` while the right side is the constant `a + b`.  Hence `GradDom` is a genuine
restriction, not a consequence of `W ≥ 0` and `deg W = 4`. -/
theorem not_gradDom_flat_quartic :
    ¬ ∃ a b : ℝ, ∀ x y : ℝ,
      ‖evAt x y (pderiv 0 flatQuartic)‖ ^ 2
          + ‖evAt x y (pderiv 1 flatQuartic)‖ ^ 2
        ≤ a * ‖evAt x y flatQuartic‖ ^ 2 + b := by
  rintro ⟨a, b, h⟩
  set t : ℝ := |a| + |b| + 2 with ht
  have ht1 : 1 ≤ t := by rw [ht]; have := abs_nonneg a; have := abs_nonneg b; linarith
  have ht0 : 0 < t := by linarith
  have hpt := h t (1 / t)
  rw [eval_flat_zero, eval_flat_one, eval_flat_self] at hpt
  have h0 : ‖((2 * t * (1 / t) ^ 2 : ℝ) : ℂ)‖ ^ 2 = 4 / t ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    field_simp
    ring
  have h1 : ‖((2 * t ^ 2 * (1 / t) : ℝ) : ℂ)‖ ^ 2 = 4 * t ^ 2 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    field_simp
    ring
  have hW : ‖((t ^ 2 * (1 / t) ^ 2 : ℝ) : ℂ)‖ ^ 2 = 1 := by
    rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    field_simp
  rw [h0, h1, hW] at hpt
  have h1' : 4 * t ^ 2 ≤ a + b := by
    have hpos : 0 ≤ 4 / t ^ 2 := by positivity
    linarith
  have h2 : a + b ≤ t := by
    rw [ht]
    have h3 := le_abs_self a
    have h4 := le_abs_self b
    linarith
  have h3 : t < 4 * t ^ 2 := by nlinarith
  linarith

end

end BookProof.SmReverseEllipticQuartic
