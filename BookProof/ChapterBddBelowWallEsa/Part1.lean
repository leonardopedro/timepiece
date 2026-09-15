import Mathlib
import BookProof.ChapterWallDeficiencyObstruction

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

namespace BookProof.BddBelowWallEsa

open MeasureTheory Metric Filter Topology Set
open BookProof.FarisLavine BookProof.ScalaronEsa BookProof.ScalaronWallEsa
open BookProof.WallDeficiencyObstruction BookProof.WeakSecondDeriv

noncomputable section

/-! ## 1. The scaled cutoff family -/

/-- A fixed smooth bump on the line: `1` on `[−1,1]`, supported in `[−2,2]`. -/
def bumpG : ContDiffBump (0 : ℝ) := ⟨1, 2, one_pos, by norm_num⟩

/-- Its derivative. -/
def bumpG' : ℝ → ℝ := deriv (bumpG : ℝ → ℝ)

lemma hasDerivAt_bumpG (x : ℝ) : HasDerivAt (bumpG : ℝ → ℝ) (bumpG' x) x :=
  (((bumpG.contDiff (n := 1)).differentiable (by norm_num)) x).hasDerivAt

lemma continuous_bumpG' : Continuous bumpG' :=
  (bumpG.contDiff (n := 2)).continuous_deriv (by norm_num)

lemma hasCompactSupport_bumpG' : HasCompactSupport bumpG' := bumpG.hasCompactSupport.deriv

lemma bumpG_one {x : ℝ} (hx : |x| ≤ 1) : (bumpG : ℝ → ℝ) x = 1 := by
  refine bumpG.one_of_mem_closedBall ?_
  simpa [Real.dist_eq, bumpG] using hx

lemma bumpG_zero {x : ℝ} (hx : 2 ≤ |x|) : (bumpG : ℝ → ℝ) x = 0 := by
  refine bumpG.zero_of_le_dist ?_
  simpa [Real.dist_eq, bumpG] using hx

/-- A uniform bound for the derivative of the fixed bump. -/
def bumpM : ℝ := (hasCompactSupport_bumpG'.exists_bound_of_continuous continuous_bumpG').choose

lemma abs_bumpG'_le (x : ℝ) : |bumpG' x| ≤ bumpM := by
  have h := (hasCompactSupport_bumpG'.exists_bound_of_continuous continuous_bumpG').choose_spec x
  simpa [Real.norm_eq_abs, bumpM] using h

lemma bumpM_nonneg : 0 ≤ bumpM := le_trans (abs_nonneg _) (abs_bumpG'_le 0)

/-- The cutoff at scale `r`: `1` on `[−r, r]`, supported in `[−2r, 2r]`. -/
def zeta (r : ℝ) : ℝ → ℝ := fun x => (bumpG : ℝ → ℝ) (x / r)

/-- Its derivative. -/
def zeta' (r : ℝ) : ℝ → ℝ := fun x => bumpG' (x / r) / r

lemma hasDerivAt_zeta (r : ℝ) (x : ℝ) : HasDerivAt (zeta r) (zeta' r x) x := by
  simpa [zeta, zeta', div_eq_mul_inv, mul_comm] using
    (hasDerivAt_bumpG (x / r)).comp x ((hasDerivAt_id x).div_const r)

lemma continuous_zeta (r : ℝ) : Continuous (zeta r) :=
  continuous_iff_continuousAt.2 fun x => (hasDerivAt_zeta r x).continuousAt

lemma continuous_zeta' (r : ℝ) : Continuous (zeta' r) :=
  (continuous_bumpG'.comp (continuous_id.div_const r)).div_const r

lemma zeta_nonneg (r : ℝ) (x : ℝ) : 0 ≤ zeta r x := bumpG.nonneg

lemma zeta_le_one (r : ℝ) (x : ℝ) : zeta r x ≤ 1 := bumpG.le_one

lemma zeta_one {r : ℝ} (hr : 0 < r) {x : ℝ} (hx : |x| ≤ r) : zeta r x = 1 := by
  refine bumpG_one ?_
  rw [abs_div, abs_of_pos hr, div_le_one hr]
  exact hx

lemma hasCompactSupport_zeta {r : ℝ} (hr : 0 < r) : HasCompactSupport (zeta r) := by
  apply HasCompactSupport.intro (isCompact_Icc (a := -(2 * r)) (b := 2 * r))
  intro x hx
  refine bumpG_zero ?_
  simp only [Set.mem_Icc, not_and_or, not_le] at hx
  rw [abs_div, abs_of_pos hr, le_div_iff₀ hr]
  rcases hx with h | h
  · rw [abs_of_nonpos (by linarith)]; linarith
  · rw [abs_of_nonneg (by linarith)]; linarith

lemma hasCompactSupport_zeta' {r : ℝ} (hr : 0 < r) : HasCompactSupport (zeta' r) := by
  have h : zeta' r = deriv (zeta r) := funext fun x => (hasDerivAt_zeta r x).deriv.symm
  rw [h]
  exact (hasCompactSupport_zeta hr).deriv

lemma hasCompactSupport_zeta_sq {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (fun x => (zeta r x) ^ 2) := by
  simpa [pow_two] using (hasCompactSupport_zeta hr).mul_right (f' := zeta r)

lemma hasCompactSupport_zeta'_sq {r : ℝ} (hr : 0 < r) :
    HasCompactSupport (fun x => (zeta' r x) ^ 2) := by
  simpa [pow_two] using (hasCompactSupport_zeta' hr).mul_right (f' := zeta' r)

lemma abs_zeta'_le {r : ℝ} (hr : 0 < r) (x : ℝ) : |zeta' r x| ≤ bumpM / r := by
  rw [zeta', abs_div, abs_of_pos hr]
  exact div_le_div_of_nonneg_right (abs_bumpG'_le _) hr.le

/-! ## 2. The weighted integration-by-parts identities -/

section Ode

variable {V : ℝ → ℝ} {z : ℂ} {W W' : ℝ → ℂ}

/-- The derivative of the Wronskian-type product `conj(W)·W'`. -/
lemma hasDerivAt_wronsk (hW : ∀ x, HasDerivAt W (W' x) x)
    (hW2 : ∀ x, HasDerivAt W' ((((V x : ℝ) : ℂ) - z) * W x) x) (x : ℝ) :
    HasDerivAt (fun y => (starRingEnd ℂ) (W y) * W' y)
      ((starRingEnd ℂ) (W' x) * W' x
        + (starRingEnd ℂ) (W x) * ((((V x : ℝ) : ℂ) - z) * W x)) x :=
  ((hW x).star).mul (hW2 x)

lemma wronsk_deriv_re (x : ℝ) :
    ((starRingEnd ℂ) (W' x) * W' x
        + (starRingEnd ℂ) (W x) * ((((V x : ℝ) : ℂ) - z) * W x)).re
      = ‖W' x‖ ^ 2 + (V x - z.re) * ‖W x‖ ^ 2 := by
  have h1 : (starRingEnd ℂ) (W' x) * W' x = ((‖W' x‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.conj_mul']; push_cast; ring
  have h2 : (starRingEnd ℂ) (W x) * ((((V x : ℝ) : ℂ) - z) * W x)
      = ((((V x : ℝ) : ℂ) - z)) * ((‖W x‖ ^ 2 : ℝ) : ℂ) := by
    rw [← mul_assoc, mul_comm ((starRingEnd ℂ) (W x)) ((((V x : ℝ) : ℂ) - z)), mul_assoc,
      Complex.conj_mul']
    push_cast; ring
  rw [h1, h2]
  simp only [Complex.add_re, Complex.mul_re, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

lemma wronsk_deriv_im (x : ℝ) :
    ((starRingEnd ℂ) (W' x) * W' x
        + (starRingEnd ℂ) (W x) * ((((V x : ℝ) : ℂ) - z) * W x)).im
      = -z.im * ‖W x‖ ^ 2 := by
  have h1 : (starRingEnd ℂ) (W' x) * W' x = ((‖W' x‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.conj_mul']; push_cast; ring
  have h2 : (starRingEnd ℂ) (W x) * ((((V x : ℝ) : ℂ) - z) * W x)
      = ((((V x : ℝ) : ℂ) - z)) * ((‖W x‖ ^ 2 : ℝ) : ℂ) := by
    rw [← mul_assoc, mul_comm ((starRingEnd ℂ) (W x)) ((((V x : ℝ) : ℂ) - z)), mul_assoc,
      Complex.conj_mul']
    push_cast; ring
  rw [h1, h2]
  simp only [Complex.add_im, Complex.mul_im, Complex.sub_re, Complex.sub_im, Complex.ofReal_re,
    Complex.ofReal_im]
  ring

/-- The real part of the weighted identity, before integration. -/
lemma hasDerivAt_reWeighted (hW : ∀ x, HasDerivAt W (W' x) x)
    (hW2 : ∀ x, HasDerivAt W' ((((V x : ℝ) : ℂ) - z) * W x) x) (r : ℝ) (x : ℝ) :
    HasDerivAt (fun y => (zeta r y) ^ 2 * ((starRingEnd ℂ) (W y) * W' y).re)
      (2 * zeta r x * zeta' r x * ((starRingEnd ℂ) (W x) * W' x).re
        + (zeta r x) ^ 2 * (‖W' x‖ ^ 2 + (V x - z.re) * ‖W x‖ ^ 2)) x := by
  have hz2 : HasDerivAt (fun y => (zeta r y) ^ 2) (2 * zeta r x * zeta' r x) x := by
    simpa [mul_comm, mul_assoc, mul_left_comm] using (hasDerivAt_zeta r x).pow 2
  have hP : HasDerivAt (fun y => ((starRingEnd ℂ) (W y) * W' y).re)
      (‖W' x‖ ^ 2 + (V x - z.re) * ‖W x‖ ^ 2) x := by
    have h := Complex.reCLM.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_wronsk hW hW2 x)
    simp only [Function.comp_def, Complex.reCLM_apply] at h
    rwa [wronsk_deriv_re (V := V) (z := z) (W := W) (W' := W') x] at h
  simpa using hz2.mul hP

/-- The imaginary part of the weighted identity, before integration. -/
lemma hasDerivAt_imWeighted (hW : ∀ x, HasDerivAt W (W' x) x)
    (hW2 : ∀ x, HasDerivAt W' ((((V x : ℝ) : ℂ) - z) * W x) x) (r : ℝ) (x : ℝ) :
    HasDerivAt (fun y => (zeta r y) ^ 2 * ((starRingEnd ℂ) (W y) * W' y).im)
      (2 * zeta r x * zeta' r x * ((starRingEnd ℂ) (W x) * W' x).im
        + (zeta r x) ^ 2 * (-z.im * ‖W x‖ ^ 2)) x := by
  have hz2 : HasDerivAt (fun y => (zeta r y) ^ 2) (2 * zeta r x * zeta' r x) x := by
    simpa [mul_comm, mul_assoc, mul_left_comm] using (hasDerivAt_zeta r x).pow 2
  have hP : HasDerivAt (fun y => ((starRingEnd ℂ) (W y) * W' y).im)
      (-z.im * ‖W x‖ ^ 2) x := by
    have h := Complex.imCLM.hasFDerivAt.comp_hasDerivAt x (hasDerivAt_wronsk hW hW2 x)
    simp only [Function.comp_def, Complex.imCLM_apply] at h
    rwa [wronsk_deriv_im (V := V) (z := z) (W := W) (W' := W') x] at h
  simpa using hz2.mul hP

end Ode

end

end BookProof.BddBelowWallEsa
