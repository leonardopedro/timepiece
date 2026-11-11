/-
Copyright (c) 2026.  All rights reserved.

# The annulus estimate

The graph-norm approximation of a polynomial class `p` by a compactly supported `C²` class splits
into a cutoff term and an annulus term.  `ChapterYangMillsPolyTail` supplies the first of the two
*inputs* (the vanishing Gaussian tail); this module supplies the second, and then assembles both
into `PolyGraphApprox`.

The estimate is one pointwise identity and one pointwise bound.  The identity is

`T (χ_R · p) − T p = −χ_R'' p − 2 χ_R' p' + x χ_R' p + (χ_R − 1) T p`,

`T = −d² + x d` being the Dirichlet operator; it is the product rule twice, with `T p` collected.
The bound is what makes the right-hand side integrable: each coefficient vanishes off the annulus
`R² < x² < 2R²` (or, for `χ_R − 1`, off the ball), and on the annulus the derivative bounds of
`ChapterYangMillsPolyCutoff` collapse to constants,

* `|χ_R'| ≤ 4 C₁ / R` and `|x χ_R'| ≤ 4 C₁` — uniform in `x`,
* `|χ_R''| ≤ 8 C₂ + 2 C₁` for `R ≥ 1`,

so the whole difference is dominated by a *fixed* multiple of `p²`, `p'²` and `(T p)²` on a tail,
and the three Gaussian tail integrals of those polynomials are finite and small.

The finiteness is the second half of the file's input: `T p = −p'' + x p'` is dominated by `|p''|`
and `|x p'|`, and the Gaussian mass of the square of any polynomial is finite
(`lintegral_ofReal_sq_lt_top`), which is what lets the tail lemma be applied to `p`, `p'` and
`T p` without extra hypotheses.

The file closes the loop: `lintegral_sq_sub_le` integrates the pointwise bound,
`exists_cutFn_tail` picks one radius for all three tails, `approximable_polyLp` assembles the two
`ε`-estimates of `Approximable`, and `polyGraphApprox_holds` propagates them to every Hermite-span
class through `polyGraphApprox_of_hermite`.  The inclusion `polyOp ≤ gaussOp.closure` therefore has
no analytic input left.
-/
import BookProof.Qym.ChapterYangMillsPolyLpNorm
import BookProof.Qym.ChapterYangMillsPolyCutoff

open MeasureTheory Polynomial
open scoped ENNReal InnerProductSpace

namespace BookProof.YangMillsPolyAnnulus

open BookProof.YangMillsPolyCore BookProof.YangMillsPolyGraphNorm
open BookProof.YangMillsPolyTail BookProof.YangMillsPolyCutoff
open BookProof.YangMillsPolyLpNorm BookProof.YangMillsHermiteAnalytic
open BookProof.YangMillsHermiteSpectrum BookProof.YangMillsMehlerLp
open BookProof.YangMillsMehlerBridge BookProof.YangMillsGaussForm BookProof.HermiteCore

noncomputable section

/-! ## Smoothness and size of the cutoff times a polynomial -/

/-- **Polynomial functions are twice continuously differentiable.**  Mathlib has no `ContDiff`
statement for `Polynomial.eval`, so this is the induction over the polynomial ring: constants,
sums, and multiplication by `X`. -/
theorem contDiff_eval_two (p : Polynomial ℝ) : ContDiff ℝ 2 (fun x : ℝ => p.eval x) := by
  induction p using Polynomial.induction_on with
  | C a => simpa using contDiff_const
  | add p q hp hq => simpa using hp.add hq
  | monomial n a ih =>
    have h : (fun x : ℝ => (Polynomial.C a * Polynomial.X ^ n).eval x * x)
        = fun x : ℝ => (Polynomial.C a * Polynomial.X ^ (n + 1)).eval x := by
      funext x
      simp [pow_succ]
      ring
    rw [← h]
    simpa using ih.mul contDiff_id

/-- **The cutoff is bounded by `1`**: `smoothTransition` takes values in `[0, 1]`. -/
theorem abs_cutFn_le_one (R x : ℝ) : |cutFn R x| ≤ 1 := by
  rw [cutFn, abs_le]
  exact ⟨by linarith [Real.smoothTransition.nonneg (2 - x ^ 2 / R ^ 2)],
    Real.smoothTransition.le_one _⟩

/-- **`χ_R · p` is an `L²(γ dx)` class.**  It is dominated by `p`, which is square-integrable
(`memLp_eval`), and it is measurable because both factors are continuous. -/
theorem memLp_cutFn_mul_eval (R : ℝ) (p : Polynomial ℝ) :
    MemLp (fun y : ℝ => cutFn R y * p.eval y) 2 gaussMeasure := by
  refine MemLp.of_le (memLp_eval p) ?_ ?_
  · exact ((contDiff_cutFn R).continuous.mul p.continuous).aestronglyMeasurable
  · filter_upwards with x
    rw [norm_mul]
    calc ‖cutFn R x‖ * ‖p.eval x‖ ≤ 1 * ‖p.eval x‖ :=
          mul_le_mul_of_nonneg_right (by rw [Real.norm_eq_abs]; exact abs_cutFn_le_one R x)
            (norm_nonneg _)
      _ = ‖p.eval x‖ := one_mul _

/-- **`χ_R · p` is a `C²`-compactly-supported representative**: it is in the core `gaussCore`
whenever `R > 0`. -/
theorem contDiff_cutFn_mul_eval (R : ℝ) (p : Polynomial ℝ) :
    ContDiff ℝ 2 (fun y : ℝ => cutFn R y * p.eval y) :=
  (contDiff_cutFn R).mul (contDiff_eval_two p)

/-- The core representative `χ_R · p` is compactly supported for `R > 0`. -/
theorem hasCompactSupport_cutFn_mul_eval {R : ℝ} (hR : 0 < R) (p : Polynomial ℝ) :
    HasCompactSupport (fun y : ℝ => cutFn R y * p.eval y) :=
  (hasCompactSupport_cutFn hR).mul_right

/-- **`χ_R · p` as a core class.**  This is the approximant in `Approximable`, and the three
membership facts above are exactly what `gaussCore` asks for.  The positivity of `R` is a real
hypothesis and not bookkeeping: for `R = 0` the cutoff is the constant `smoothTransition 2`, which
is not compactly supported. -/
def cutCore {R : ℝ} (hR : 0 < R) (p : Polynomial ℝ) : gaussCore :=
  ⟨(memLp_cutFn_mul_eval R p).toLp (fun y : ℝ => cutFn R y * p.eval y),
    ⟨fun y : ℝ => cutFn R y * p.eval y, contDiff_cutFn_mul_eval R p,
      hasCompactSupport_cutFn_mul_eval hR p,
      MemLp.coeFn_toLp (memLp_cutFn_mul_eval R p)⟩⟩

/-- The core class `cutCore hR p` has `χ_R · p` as its representative. -/
theorem cutCore_coeFn {R : ℝ} (hR : 0 < R) (p : Polynomial ℝ) :
    ((cutCore hR p : gaussCore) : Lp ℝ 2 gaussMeasure)
      =ᵐ[gaussMeasure] fun y : ℝ => cutFn R y * p.eval y :=
  MemLp.coeFn_toLp (memLp_cutFn_mul_eval R p)


/-! ## The pointwise bound on `T p`, and finiteness of its Gaussian mass -/

/-- **`T` of a polynomial, term by term**: `T p = −p'' + x p'`. -/
theorem dirichletPoly_eval_apply (p : Polynomial ℝ) (x : ℝ) :
    (dirichletPoly p).eval x
      = -((derivative (derivative p)).eval x) + x * (derivative p).eval x := by
  simp [dirichletPoly_apply]

/-- **`T p` and `gaussDirichlet` of `p` agree at every point.**  The polynomial identity
`dirichletPoly_eval` is a statement about functions; this is its pointwise form, which is what a
pointwise estimate can consume. -/
theorem gaussDirichlet_eval (p : Polynomial ℝ) (x : ℝ) :
    gaussDirichlet (fun y : ℝ => p.eval y) x = (dirichletPoly p).eval x :=
  congrFun (dirichletPoly_eval p).symm x

/-- **The pointwise bound on `T p`.**  `T p = −p'' + x p'` is dominated by the absolute values of
its two terms, which is what makes the annulus estimate a statement about polynomials. -/
theorem abs_dirichletPoly_eval_le (p : Polynomial ℝ) (x : ℝ) :
    |(dirichletPoly p).eval x|
      ≤ |(derivative (derivative p)).eval x| + |x| * |(derivative p).eval x| := by
  rw [dirichletPoly_eval_apply]
  have h := abs_add_le (-((derivative (derivative p)).eval x))
    (x * (derivative p).eval x)
  rw [abs_neg, abs_mul] at h
  exact h

/-- **The Gaussian mass of a squared polynomial is finite.**  This is the `htot` computation of
`exists_lintegral_tail_lt`, isolated: it is what makes a tail bound *small* rather than merely
finite, and it is needed for every polynomial the annulus estimate produces, not just for `p`. -/
theorem lintegral_ofReal_sq_lt_top (q : Polynomial ℝ) :
    ∫⁻ y, ENNReal.ofReal ((q.eval y) ^ 2) ∂gaussMeasure ≠ ∞ := by
  have hfin : ∫⁻ y, ‖q.eval y‖ₑ ^ (2 : ℝ) ∂gaussMeasure < ∞ := by
    simpa using lintegral_rpow_enorm_lt_top_of_eLpNorm_lt_top (p := 2)
      (f := fun y => q.eval y) (μ := gaussMeasure) (by norm_num) (by norm_num)
      (memLp_eval q).2
  rw [show ∫⁻ y, ‖q.eval y‖ₑ ^ (2 : ℝ) ∂gaussMeasure
      = ∫⁻ y, ENNReal.ofReal ((q.eval y) ^ 2) ∂gaussMeasure from
    lintegral_congr fun y => enorm_sq_eq_ofReal_sq _] at hfin
  exact hfin.ne

/-- **Every annulus term is Gaussian-finitely integrable.**  The estimate below dominates the
difference `T(χ_R p) − T p` by a fixed combination of `p²`, `p'²` and `(T p)²`; all three have
finite `γ`-mass, uniformly in `R`, which is exactly the domination the tail lemma needs. -/
theorem annulus_terms_finite (p : Polynomial ℝ) :
    (∫⁻ y, ENNReal.ofReal ((p.eval y) ^ 2) ∂gaussMeasure ≠ ∞) ∧
    (∫⁻ y, ENNReal.ofReal (((derivative p).eval y) ^ 2) ∂gaussMeasure ≠ ∞) ∧
    (∫⁻ y, ENNReal.ofReal (((derivative (derivative p)).eval y) ^ 2) ∂gaussMeasure ≠ ∞) ∧
    (∫⁻ y, ENNReal.ofReal ((y * (derivative p).eval y) ^ 2) ∂gaussMeasure ≠ ∞) ∧
    (∫⁻ y, ENNReal.ofReal (((dirichletPoly p).eval y) ^ 2) ∂gaussMeasure ≠ ∞) := by
  refine ⟨lintegral_ofReal_sq_lt_top p, lintegral_ofReal_sq_lt_top (derivative p),
    lintegral_ofReal_sq_lt_top (derivative (derivative p)), ?_,
    lintegral_ofReal_sq_lt_top (dirichletPoly p)⟩
  have h := lintegral_ofReal_sq_lt_top ((Polynomial.X : Polynomial ℝ) * derivative p)
  simpa only [Polynomial.eval_mul, Polynomial.eval_X] using h

/-- **`T p` has finite Gaussian mass.**  The pointwise bound and the finiteness of its two terms
combine: this is the third of the three tail integrals the annulus estimate bounds. -/
theorem lintegral_ofReal_dirichletPoly_sq_lt_top (p : Polynomial ℝ) :
    ∫⁻ y, ENNReal.ofReal (((dirichletPoly p).eval y) ^ 2) ∂gaussMeasure ≠ ∞ :=
  (annulus_terms_finite p).2.2.2.2

/-! ## The cutoff, uniformly in `x` -/

/-- The cutoff is nonnegative: `smoothTransition` takes values in `[0, 1]`. -/
theorem cutFn_nonneg (R x : ℝ) : 0 ≤ cutFn R x :=
  Real.smoothTransition.nonneg _

/-- **`χ_R'` vanishes where `x² > 2R²`.**  There the argument `2 − x²/R²` of `smoothTransition` is
negative, and `smoothTransition` is constant there. -/
theorem deriv_cutFn_eq_zero_of_two_mul_sq_lt {R x : ℝ} (hR : 0 < R) (hx : 2 * R ^ 2 < x ^ 2) :
    deriv (cutFn R) x = 0 := by
  have hdiv : 2 < x ^ 2 / R ^ 2 := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < R ^ 2)]
    linarith
  have hu : 2 - x ^ 2 / R ^ 2 < 0 := by linarith
  rw [deriv_cutFn, deriv_smoothTransition_eq_zero_of_notMem (fun hmem => ?_), zero_mul]
  exact absurd hmem.1 (not_le.mpr hu)

/-- **`χ_R''` vanishes where `x² > 2R²`**, for the same reason. -/
theorem deriv_deriv_cutFn_eq_zero_of_two_mul_sq_lt {R x : ℝ} (hR : 0 < R)
    (hx : 2 * R ^ 2 < x ^ 2) : deriv (deriv (cutFn R)) x = 0 := by
  have hdiv : 2 < x ^ 2 / R ^ 2 := by
    rw [lt_div_iff₀ (by positivity : (0 : ℝ) < R ^ 2)]
    linarith
  have hu : 2 - x ^ 2 / R ^ 2 < 0 := by linarith
  have hnot : 2 - x ^ 2 / R ^ 2 ∉ Set.Icc (0 : ℝ) 1 := fun hmem =>
    absurd hmem.1 (not_le.mpr hu)
  rw [(hasDerivAt_deriv_cutFn R x).deriv,
    deriv_smoothTransition_eq_zero_of_notMem hnot,
    deriv_deriv_smoothTransition_eq_zero_of_notMem hnot]
  ring

/-- **`χ_R'` vanishes where `x² < R²`**: there the argument is bigger than `1`. -/
theorem deriv_cutFn_eq_zero_of_sq_lt {R x : ℝ} (hR : 0 < R) (hx : x ^ 2 < R ^ 2) :
    deriv (cutFn R) x = 0 := by
  have hdiv : x ^ 2 / R ^ 2 < 1 := by
    rw [div_lt_one (by positivity : (0 : ℝ) < R ^ 2)]
    exact hx
  have hu : 1 < 2 - x ^ 2 / R ^ 2 := by linarith
  rw [deriv_cutFn, deriv_smoothTransition_eq_zero_of_notMem (fun hmem => ?_), zero_mul]
  exact absurd hmem.2 (not_le.mpr hu)

/-- **`χ_R''` vanishes where `x² < R²`**, for the same reason. -/
theorem deriv_deriv_cutFn_eq_zero_of_sq_lt {R x : ℝ} (hR : 0 < R) (hx : x ^ 2 < R ^ 2) :
    deriv (deriv (cutFn R)) x = 0 := by
  have hdiv : x ^ 2 / R ^ 2 < 1 := by
    rw [div_lt_one (by positivity : (0 : ℝ) < R ^ 2)]
    exact hx
  have hu : 1 < 2 - x ^ 2 / R ^ 2 := by linarith
  have hnot : 2 - x ^ 2 / R ^ 2 ∉ Set.Icc (0 : ℝ) 1 := fun hmem =>
    absurd hmem.2 (not_le.mpr hu)
  rw [(hasDerivAt_deriv_cutFn R x).deriv,
    deriv_smoothTransition_eq_zero_of_notMem hnot,
    deriv_deriv_smoothTransition_eq_zero_of_notMem hnot]
  ring

/-- **The first derivative of the cutoff is `O(1/R)`.**  On the annulus `|x| ≤ √2 R` turns
`|χ_R'| ≤ C₁ · 2|x|/R²` into `C₁ · 2√2/R`, and off it the derivative vanishes; `2√2 ≤ 4` makes
the constant integral. -/
theorem abs_deriv_cutFn_le {R : ℝ} (hR : 1 ≤ R) (x : ℝ) :
    |deriv (cutFn R) x| ≤ 4 * sDerivBound / R := by
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  by_cases hx : x ^ 2 ≤ 2 * R ^ 2
  · have hxabs : |x| ≤ Real.sqrt 2 * R := by
      have h2 : (Real.sqrt 2 * R) ^ 2 = 2 * R ^ 2 := by
        rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
      calc |x| = Real.sqrt (x ^ 2) := (Real.sqrt_sq_eq_abs x).symm
        _ ≤ Real.sqrt ((Real.sqrt 2 * R) ^ 2) := Real.sqrt_le_sqrt (by rw [h2]; exact hx)
        _ = Real.sqrt 2 * R := Real.sqrt_sq (by positivity)
    have hstep : 2 * |x| / R ^ 2 ≤ 2 * (Real.sqrt 2 * R) / R ^ 2 := by
      have hmul : 2 * |x| ≤ 2 * (Real.sqrt 2 * R) := by linarith
      exact div_le_div_of_nonneg_right hmul (by positivity)
    have hsqrt : Real.sqrt 2 ≤ 2 := by
      nlinarith [Real.sq_sqrt (show (0 : ℝ) ≤ 2 by norm_num), Real.sqrt_nonneg 2]
    calc |deriv (cutFn R) x| ≤ sDerivBound * (2 * |x| / R ^ 2) := cutFn_deriv_bound R x
      _ ≤ sDerivBound * (2 * (Real.sqrt 2 * R) / R ^ 2) :=
          mul_le_mul_of_nonneg_left hstep sDerivBound_nonneg
      _ = sDerivBound * (2 * Real.sqrt 2 / R) := by
          congr 1
          field_simp
      _ ≤ sDerivBound * (4 / R) := by
          have h4 : 2 * Real.sqrt 2 / R ≤ 4 / R := by
            have hm : 2 * Real.sqrt 2 ≤ 4 := by linarith
            exact div_le_div_of_nonneg_right hm hR0.le
          exact mul_le_mul_of_nonneg_left h4 sDerivBound_nonneg
      _ = 4 * sDerivBound / R := by ring
  · have hx' : 2 * R ^ 2 < x ^ 2 := lt_of_not_ge hx
    rw [deriv_cutFn_eq_zero_of_two_mul_sq_lt hR0 hx', abs_zero]
    exact div_nonneg (by nlinarith [sDerivBound_nonneg]) hR0.le

/-- **`x χ_R'` is uniformly bounded.**  On the annulus `|x χ_R'| ≤ 4C₁`, and off it `χ_R' = 0`, so
the bound is global in `x` and `R` — this is the one term of the identity that does not decay. -/
theorem abs_mul_deriv_cutFn_le {R : ℝ} (hR : 0 < R) (x : ℝ) :
    |x * deriv (cutFn R) x| ≤ 4 * sDerivBound := by
  by_cases hx : x ^ 2 ≤ 2 * R ^ 2
  · have hb := cutFn_deriv_bound R x
    have hstep : |x| * (2 * |x| / R ^ 2) ≤ 4 := by
      have hx2 : |x| ^ 2 ≤ 2 * R ^ 2 := by
        rw [sq_abs]
        exact hx
      have heq : |x| * (2 * |x| / R ^ 2) = 2 * |x| ^ 2 / R ^ 2 := by
        field_simp
      rw [heq, div_le_iff₀ (by positivity : (0 : ℝ) < R ^ 2)]
      linarith
    rw [abs_mul]
    calc |x| * |deriv (cutFn R) x| ≤ |x| * (sDerivBound * (2 * |x| / R ^ 2)) :=
          mul_le_mul_of_nonneg_left hb (abs_nonneg _)
      _ = sDerivBound * (|x| * (2 * |x| / R ^ 2)) := by ring
      _ ≤ sDerivBound * 4 := mul_le_mul_of_nonneg_left hstep sDerivBound_nonneg
      _ = 4 * sDerivBound := by ring
  · have hx' : 2 * R ^ 2 < x ^ 2 := lt_of_not_ge hx
    rw [deriv_cutFn_eq_zero_of_two_mul_sq_lt hR hx', mul_zero, abs_zero]
    nlinarith [sDerivBound_nonneg]

/-- **The second derivative of the cutoff is bounded uniformly in `x`**, with an `R`-independent
constant once `R ≥ 1`. -/
theorem abs_deriv2_cutFn_le {R : ℝ} (hR : 1 ≤ R) (x : ℝ) :
    |deriv (deriv (cutFn R)) x| ≤ 8 * sDerivBound2 + 2 * sDerivBound := by
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  by_cases hx : x ^ 2 ≤ 2 * R ^ 2
  · have hb := cutFn_deriv2_bound R x
    have hx2 : (2 * |x| / R ^ 2) ^ 2 ≤ 8 := by
      have hsq : |x| ^ 2 ≤ 2 * R ^ 2 := by
        rw [sq_abs]
        exact hx
      have hR2 : (1 : ℝ) ≤ R ^ 2 := by nlinarith
      rw [div_pow, mul_pow, sq_abs]
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < (R ^ 2) ^ 2)]
      nlinarith
    have hR2inv : 2 / R ^ 2 ≤ 2 := by
      rw [div_le_iff₀ (by positivity : (0 : ℝ) < R ^ 2)]
      nlinarith
    calc |deriv (deriv (cutFn R)) x|
        ≤ sDerivBound2 * (2 * |x| / R ^ 2) ^ 2 + sDerivBound * (2 / R ^ 2) :=
          cutFn_deriv2_bound R x
      _ ≤ sDerivBound2 * 8 + sDerivBound * 2 := by
          have h1 := mul_le_mul_of_nonneg_left hx2 sDerivBound2_nonneg
          have h2 := mul_le_mul_of_nonneg_left hR2inv sDerivBound_nonneg
          linarith
      _ = 8 * sDerivBound2 + 2 * sDerivBound := by ring
  · have hx' : 2 * R ^ 2 < x ^ 2 := lt_of_not_ge hx
    rw [deriv_deriv_cutFn_eq_zero_of_two_mul_sq_lt hR0 hx', abs_zero]
    nlinarith [sDerivBound2_nonneg, sDerivBound_nonneg]

/-! ## The product rule twice, and the annulus identity -/

/-- **The derivative of `χ_R · p`.** -/
theorem deriv_cutFn_mul_eval (R : ℝ) (p : Polynomial ℝ) (x : ℝ) :
    deriv (fun y : ℝ => cutFn R y * p.eval y) x
      = deriv (cutFn R) x * p.eval x + cutFn R x * (derivative p).eval x := by
  have hχ : DifferentiableAt ℝ (cutFn R) x :=
    ((contDiff_cutFn R).differentiable (by norm_num)).differentiableAt
  have hp : DifferentiableAt ℝ (fun y : ℝ => p.eval y) x := p.differentiable.differentiableAt
  have h := deriv_mul hχ hp
  simpa only [Pi.mul_apply, (p.hasDerivAt x).deriv] using h

/-- **The second derivative of `χ_R · p`.**  Two product rules, with the mixed terms collected:
`(χ p)'' = χ'' p + 2 χ' p' + χ p''`. -/
theorem deriv_deriv_cutFn_mul_eval (R : ℝ) (p : Polynomial ℝ) (x : ℝ) :
    deriv (fun y : ℝ => deriv (fun z : ℝ => cutFn R z * p.eval z) y) x
      = deriv (deriv (cutFn R)) x * p.eval x
        + 2 * (deriv (cutFn R) x * (derivative p).eval x)
        + cutFn R x * (derivative (derivative p)).eval x := by
  have hcongr : (fun y : ℝ => deriv (fun z : ℝ => cutFn R z * p.eval z) y)
      = fun y : ℝ => deriv (cutFn R) y * p.eval y + cutFn R y * (derivative p).eval y :=
    funext fun y => deriv_cutFn_mul_eval R p y
  have hχ' : DifferentiableAt ℝ (deriv (cutFn R)) x :=
    (((contDiff_cutFn R).deriv' (n := 1)).differentiable (by norm_num)).differentiableAt
  have hp : DifferentiableAt ℝ (fun y : ℝ => p.eval y) x := p.differentiable.differentiableAt
  have hχ : DifferentiableAt ℝ (cutFn R) x :=
    ((contDiff_cutFn R).differentiable (by norm_num)).differentiableAt
  have hp' : DifferentiableAt ℝ (fun y : ℝ => (derivative p).eval y) x :=
    (derivative p).differentiable.differentiableAt
  have hadd : deriv (fun y : ℝ => deriv (cutFn R) y * p.eval y
        + cutFn R y * (derivative p).eval y) x
      = deriv (fun y : ℝ => deriv (cutFn R) y * p.eval y) x
        + deriv (fun y : ℝ => cutFn R y * (derivative p).eval y) x := by
    simpa only [Pi.add_apply] using deriv_add
      (f := fun y : ℝ => deriv (cutFn R) y * p.eval y)
      (g := fun y : ℝ => cutFn R y * (derivative p).eval y) (hχ'.mul hp) (hχ.mul hp')
  have hmul1 : deriv (fun y : ℝ => deriv (cutFn R) y * p.eval y) x
      = deriv (deriv (cutFn R)) x * p.eval x
        + deriv (cutFn R) x * (derivative p).eval x := by
    have h := deriv_mul hχ' hp
    rw [(p.hasDerivAt x).deriv] at h
    simpa only [Pi.mul_apply] using h
  have hmul2 : deriv (fun y : ℝ => cutFn R y * (derivative p).eval y) x
      = deriv (cutFn R) x * (derivative p).eval x
        + cutFn R x * (derivative (derivative p)).eval x := by
    have h := deriv_mul hχ hp'
    rw [((derivative p).hasDerivAt x).deriv] at h
    simpa only [Pi.mul_apply] using h
  rw [hcongr, hadd, hmul1, hmul2]
  ring

/-- **The action of `T` on `χ_R · p`**, with `T p` collected: this is the identity the annulus
estimate integrates. -/
theorem gaussDirichlet_cutFn_mul (R : ℝ) (p : Polynomial ℝ) (x : ℝ) :
    gaussDirichlet (fun y : ℝ => cutFn R y * p.eval y) x
      = cutFn R x * gaussDirichlet (fun y : ℝ => p.eval y) x
        - (deriv (deriv (cutFn R)) x * p.eval x
            + 2 * (deriv (cutFn R) x * (derivative p).eval x)
            - x * (deriv (cutFn R) x * p.eval x)) := by
  have hT : gaussDirichlet (fun y : ℝ => p.eval y) x
      = -((derivative (derivative p)).eval x) + x * (derivative p).eval x := by
    rw [gaussDirichlet_eval, dirichletPoly_eval_apply]
  rw [hT, gaussDirichlet, deriv_cutFn_mul_eval R p x, deriv_deriv_cutFn_mul_eval R p x]
  ring

/-- **The annulus identity**: the difference of the two operators on `χ_R p` and on `p`.  The
coefficient of `T p` is `χ_R − 1`, which vanishes on the ball, and the other three terms carry
derivatives of the cutoff, which vanish off the annulus. -/
theorem gaussDirichlet_cutFn_mul_sub (R : ℝ) (p : Polynomial ℝ) (x : ℝ) :
    gaussDirichlet (fun y : ℝ => cutFn R y * p.eval y) x
        - gaussDirichlet (fun y : ℝ => p.eval y) x
      = -(deriv (deriv (cutFn R)) x * p.eval x)
        - 2 * (deriv (cutFn R) x * (derivative p).eval x)
        + x * (deriv (cutFn R) x * p.eval x)
        + (cutFn R x - 1) * gaussDirichlet (fun y : ℝ => p.eval y) x := by
  rw [gaussDirichlet_cutFn_mul R p x]
  ring

/-! ## The pointwise bound, with the tail indicators -/

/-- The constant of the annulus estimate.  It is `2 (8C₂ + 6C₁)² + (16C₁)² + 4`: the first term is
the square of the coefficient of `p` (both `χ_R'' p` and `x χ_R' p` contribute), the second of `p'`,
and the last of `T p`.  It does not depend on `R` once `R ≥ 1`. -/
def annulusConst : ℝ :=
  2 * (8 * sDerivBound2 + 6 * sDerivBound) ^ 2 + 256 * sDerivBound ^ 2 + 4

/-- The annulus constant is positive. -/
theorem annulusConst_pos : 0 < annulusConst := by
  unfold annulusConst
  positivity

/-- The triangle inequality for four terms. -/
theorem abs_four_le (a b c d : ℝ) : |a + b + c + d| ≤ |a| + |b| + |c| + |d| := by
  have h1 := abs_add_le (a + b + c) d
  have h2 := abs_add_le (a + b) c
  have h3 := abs_add_le a b
  have h4 : |a + b + c| ≤ |a| + |b| + |c| := by linarith
  linarith

-- The final arithmetic is `nlinarith` over the four cutoff constants and the four absolute values;
-- normalizing those monomials exceeds the default heartbeat budget, while the estimate itself is a
-- fixed sequence of ring inequalities with no search.
set_option maxHeartbeats 800000 in
/-- **The pointwise annulus bound.**  Off the ball of radius `R` the derivative terms of the
identity are dominated by fixed multiples of `p` and `p'`, and `χ_R − 1` by `T p`; each of those
coefficients is supported on the tail, so the bound is stated against the three tail indicators.
Inside the ball the difference vanishes and the right-hand side is nonnegative. -/
theorem sq_gaussDirichlet_cutFn_mul_sub_le {R : ℝ} (hR : 1 ≤ R) (p : Polynomial ℝ) (x : ℝ) :
    (gaussDirichlet (fun y : ℝ => cutFn R y * p.eval y) x
        - gaussDirichlet (fun y : ℝ => p.eval y) x) ^ 2
      ≤ annulusConst *
          ((tailSet R).indicator (fun y : ℝ => (p.eval y) ^ 2) x
            + (tailSet R).indicator (fun y : ℝ => ((derivative p).eval y) ^ 2) x
            + (tailSet R).indicator
                (fun y : ℝ => (gaussDirichlet (fun z : ℝ => p.eval z) y) ^ 2) x) := by
  have hR0 : (0 : ℝ) < R := lt_of_lt_of_le zero_lt_one hR
  by_cases hx : R ≤ |x|
  · have hmem : x ∈ tailSet R := hx
    rw [Set.indicator_of_mem hmem, Set.indicator_of_mem hmem, Set.indicator_of_mem hmem]
    have h1 : |deriv (deriv (cutFn R)) x| ≤ 8 * sDerivBound2 + 2 * sDerivBound :=
      abs_deriv2_cutFn_le hR x
    have h2 : |deriv (cutFn R) x| ≤ 4 * sDerivBound := by
      calc |deriv (cutFn R) x| ≤ 4 * sDerivBound / R := abs_deriv_cutFn_le hR x
        _ ≤ 4 * sDerivBound := div_le_self (by nlinarith [sDerivBound_nonneg]) hR
    have h3 : |x * deriv (cutFn R) x| ≤ 4 * sDerivBound := abs_mul_deriv_cutFn_le hR0 x
    have h4 : |cutFn R x - 1| ≤ 1 := by
      rw [abs_le]
      exact ⟨by linarith [cutFn_nonneg R x],
        by linarith [(abs_le.mp (abs_cutFn_le_one R x)).2]⟩
    have hb : |gaussDirichlet (fun y : ℝ => cutFn R y * p.eval y) x
        - gaussDirichlet (fun y : ℝ => p.eval y) x|
        ≤ (8 * sDerivBound2 + 6 * sDerivBound) * |p.eval x|
          + 8 * sDerivBound * |(derivative p).eval x|
          + |gaussDirichlet (fun y : ℝ => p.eval y) x| := by
      have hid := gaussDirichlet_cutFn_mul_sub R p x
      have htri := abs_four_le (-(deriv (deriv (cutFn R)) x * p.eval x))
        (-(2 * (deriv (cutFn R) x * (derivative p).eval x)))
        (x * (deriv (cutFn R) x * p.eval x))
        ((cutFn R x - 1) * gaussDirichlet (fun y : ℝ => p.eval y) x)
      have hAsum : (-(deriv (deriv (cutFn R)) x * p.eval x))
          + (-(2 * (deriv (cutFn R) x * (derivative p).eval x)))
          + (x * (deriv (cutFn R) x * p.eval x))
          + ((cutFn R x - 1) * gaussDirichlet (fun y : ℝ => p.eval y) x)
          = -(deriv (deriv (cutFn R)) x * p.eval x)
            - 2 * (deriv (cutFn R) x * (derivative p).eval x)
            + x * (deriv (cutFn R) x * p.eval x)
            + (cutFn R x - 1) * gaussDirichlet (fun y : ℝ => p.eval y) x := by ring
      rw [hAsum] at htri
      have e1 : |-(deriv (deriv (cutFn R)) x * p.eval x)|
          = |deriv (deriv (cutFn R)) x| * |p.eval x| := by rw [abs_neg, abs_mul]
      have e2 : |-(2 * (deriv (cutFn R) x * (derivative p).eval x))|
          = 2 * (|deriv (cutFn R) x| * |(derivative p).eval x|) := by
        rw [abs_neg, abs_mul, abs_two, abs_mul]
      have e3 : |x * (deriv (cutFn R) x * p.eval x)|
          = |x * deriv (cutFn R) x| * |p.eval x| := by
        rw [show x * (deriv (cutFn R) x * p.eval x)
          = (x * deriv (cutFn R) x) * p.eval x from by ring, abs_mul]
      have e4 : |(cutFn R x - 1) * gaussDirichlet (fun y : ℝ => p.eval y) x|
          = |cutFn R x - 1| * |gaussDirichlet (fun y : ℝ => p.eval y) x| := abs_mul _ _
      rw [hid]
      rw [e1, e2, e3, e4] at htri
      have t1 : |deriv (deriv (cutFn R)) x| * |p.eval x|
          ≤ (8 * sDerivBound2 + 2 * sDerivBound) * |p.eval x| :=
        mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
      have t2 : 2 * (|deriv (cutFn R) x| * |(derivative p).eval x|)
          ≤ 8 * sDerivBound * |(derivative p).eval x| := by
        have := mul_le_mul_of_nonneg_right h2 (abs_nonneg ((derivative p).eval x))
        linarith
      have t3 : |x * deriv (cutFn R) x| * |p.eval x|
          ≤ 4 * sDerivBound * |p.eval x| :=
        mul_le_mul_of_nonneg_right h3 (abs_nonneg _)
      have t4 : |cutFn R x - 1| * |gaussDirichlet (fun y : ℝ => p.eval y) x|
          ≤ |gaussDirichlet (fun y : ℝ => p.eval y) x| := by
        have := mul_le_mul_of_nonneg_right h4 (abs_nonneg (gaussDirichlet
          (fun y : ℝ => p.eval y) x))
        simpa using this
      linarith
    set P := p.eval x with hP
    set Q := (derivative p).eval x with hQ
    set T := gaussDirichlet (fun y : ℝ => p.eval y) x with hT
    have hP' : |P| ^ 2 = P ^ 2 := sq_abs P
    have hQ' : |Q| ^ 2 = Q ^ 2 := sq_abs Q
    have hT' : |T| ^ 2 = T ^ 2 := sq_abs T
    have hnn : 0 ≤ (8 * sDerivBound2 + 6 * sDerivBound) * |P| + 8 * sDerivBound * |Q| + |T| := by
      have hc : 0 ≤ 8 * sDerivBound2 + 6 * sDerivBound := by
        nlinarith [sDerivBound_nonneg, sDerivBound2_nonneg]
      have hc' : 0 ≤ 8 * sDerivBound := by nlinarith [sDerivBound_nonneg]
      have h1 : 0 ≤ (8 * sDerivBound2 + 6 * sDerivBound) * |P| := mul_nonneg hc (abs_nonneg _)
      have h2 : 0 ≤ 8 * sDerivBound * |Q| := mul_nonneg hc' (abs_nonneg _)
      have h3 : 0 ≤ |T| := abs_nonneg _
      linarith
    have hsq : (gaussDirichlet (fun y : ℝ => cutFn R y * p.eval y) x - T) ^ 2
        ≤ ((8 * sDerivBound2 + 6 * sDerivBound) * |P| + 8 * sDerivBound * |Q| + |T|) ^ 2 := by
      rw [sq_le_sq, abs_of_nonneg hnn]
      exact hb
    have hA : ((8 * sDerivBound2 + 6 * sDerivBound) * |P|) ^ 2
        = (8 * sDerivBound2 + 6 * sDerivBound) ^ 2 * P ^ 2 := by
      rw [mul_pow, hP']
    have hB : (8 * sDerivBound * |Q| + |T|) ^ 2
        ≤ 2 * (8 * sDerivBound * |Q|) ^ 2 + 2 * |T| ^ 2 := by
      nlinarith [sq_nonneg (8 * sDerivBound * |Q| - |T|)]
    have hBsum : ((8 * sDerivBound2 + 6 * sDerivBound) * |P|
          + 8 * sDerivBound * |Q| + |T|) ^ 2
        ≤ 2 * ((8 * sDerivBound2 + 6 * sDerivBound) * |P|) ^ 2
          + 2 * (8 * sDerivBound * |Q| + |T|) ^ 2 := by
      nlinarith [sq_nonneg ((8 * sDerivBound2 + 6 * sDerivBound) * |P|
        - (8 * sDerivBound * |Q| + |T|))]
    have hQ'2 : (8 * sDerivBound * |Q|) ^ 2 = 64 * sDerivBound ^ 2 * Q ^ 2 := by
      rw [mul_pow, mul_pow, hQ']
      norm_num
    have hT'2 : |T| ^ 2 = T ^ 2 := hT'
    calc (gaussDirichlet (fun y : ℝ => cutFn R y * p.eval y) x - T) ^ 2
        ≤ ((8 * sDerivBound2 + 6 * sDerivBound) * |P| + 8 * sDerivBound * |Q| + |T|) ^ 2 := hsq
      _ ≤ 2 * ((8 * sDerivBound2 + 6 * sDerivBound) * |P|) ^ 2
            + 2 * (8 * sDerivBound * |Q| + |T|) ^ 2 := hBsum
      _ ≤ 2 * ((8 * sDerivBound2 + 6 * sDerivBound) ^ 2 * P ^ 2)
            + 2 * (2 * (64 * sDerivBound ^ 2 * Q ^ 2) + 2 * T ^ 2) := by
          rw [hA]
          nlinarith [hB, hQ'2, hT'2]
      _ ≤ annulusConst * (P ^ 2 + Q ^ 2 + T ^ 2) := by
          unfold annulusConst
          nlinarith [sq_nonneg P, sq_nonneg Q, sq_nonneg T,
            sq_nonneg (8 * sDerivBound2 + 6 * sDerivBound), sq_nonneg sDerivBound]
  · have habs : |x| < R := lt_of_not_ge hx
    have hsq : x ^ 2 < R ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
    have hz1 : deriv (cutFn R) x = 0 := deriv_cutFn_eq_zero_of_sq_lt hR0 hsq
    have hz2 : deriv (deriv (cutFn R)) x = 0 := deriv_deriv_cutFn_eq_zero_of_sq_lt hR0 hsq
    have hone : cutFn R x = 1 := cutFn_eq_one hR0 hsq.le
    have hzero : gaussDirichlet (fun y : ℝ => cutFn R y * p.eval y) x
        - gaussDirichlet (fun y : ℝ => p.eval y) x = 0 := by
      rw [gaussDirichlet_cutFn_mul_sub R p x, hz1, hz2, hone]
      ring
    rw [hzero, zero_pow (by norm_num : (2 : ℕ) ≠ 0)]
    refine mul_nonneg annulusConst_pos.le ?_
    refine add_nonneg (add_nonneg ?_ ?_) ?_
    · by_cases h : x ∈ tailSet R
      · rw [Set.indicator_of_mem h]; exact sq_nonneg _
      · rw [Set.indicator_of_notMem h]
    · by_cases h : x ∈ tailSet R
      · rw [Set.indicator_of_mem h]; exact sq_nonneg _
      · rw [Set.indicator_of_notMem h]
    · by_cases h : x ∈ tailSet R
      · rw [Set.indicator_of_mem h]; exact sq_nonneg _
      · rw [Set.indicator_of_notMem h]


/-! ## From the pointwise bound to the `L²` estimates -/

/-- `ofReal` commutes with a tail indicator, in the direction the `lintegral` computation needs. -/
theorem ofReal_indicator (R : ℝ) (g : ℝ → ℝ) (x : ℝ) :
    ENNReal.ofReal ((tailSet R).indicator g x)
      = (tailSet R).indicator (fun y : ℝ => ENNReal.ofReal (g y)) x := by
  by_cases hx : x ∈ tailSet R
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    simp

/-- **The real indicator sum of the pointwise bound is the `ENNReal` indicator sum.**  All three
indicators are cut by the same tail, so the pointwise bound can be integrated term by term. -/
theorem ofReal_indicator_sum_eq (R : ℝ) (p : Polynomial ℝ) (x : ℝ) :
    ENNReal.ofReal
        ((tailSet R).indicator (fun y : ℝ => (p.eval y) ^ 2) x
          + (tailSet R).indicator (fun y : ℝ => ((derivative p).eval y) ^ 2) x
          + (tailSet R).indicator
              (fun y : ℝ => (gaussDirichlet (fun z : ℝ => p.eval z) y) ^ 2) x)
      = (tailSet R).indicator (fun y : ℝ => ENNReal.ofReal ((p.eval y) ^ 2)) x
        + (tailSet R).indicator (fun y : ℝ => ENNReal.ofReal (((derivative p).eval y) ^ 2)) x
        + (tailSet R).indicator
            (fun y : ℝ => ENNReal.ofReal ((gaussDirichlet (fun z : ℝ => p.eval z) y) ^ 2)) x := by
  by_cases hx : x ∈ tailSet R
  · rw [Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.indicator_of_mem hx,
      Set.indicator_of_mem hx, Set.indicator_of_mem hx, Set.indicator_of_mem hx]
    rw [ENNReal.ofReal_add (add_nonneg (sq_nonneg _) (sq_nonneg _)) (sq_nonneg _),
      ENNReal.ofReal_add (sq_nonneg _) (sq_nonneg _)]
  · rw [Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx,
      Set.indicator_of_notMem hx, Set.indicator_of_notMem hx, Set.indicator_of_notMem hx]
    simp

-- The final arithmetic is `nlinarith` over the four cutoff constants and the four absolute values;
-- normalizing those monomials exceeds the default heartbeat budget, while the estimate itself is a
-- fixed sequence of ring inequalities with no search.
set_option maxHeartbeats 800000 in
/-- **The `L²` annulus estimate.**  Integrating the pointwise bound: the squared difference of the
two images is dominated by a fixed constant times the three tail integrals of `p`, `p'` and `T p`.
This is the estimate that turns the tail lemma into a statement about graph-norm closeness. -/
theorem lintegral_sq_sub_le {R : ℝ} (hR : 1 ≤ R) (p : Polynomial ℝ) :
    ∫⁻ x, ENNReal.ofReal ((gaussDirichlet (fun y : ℝ => cutFn R y * p.eval y) x
        - gaussDirichlet (fun y : ℝ => p.eval y) x) ^ 2) ∂gaussMeasure
      ≤ ENNReal.ofReal annulusConst *
          (∫⁻ x in tailSet R, ENNReal.ofReal ((p.eval x) ^ 2) ∂gaussMeasure
            + ∫⁻ x in tailSet R, ENNReal.ofReal (((derivative p).eval x) ^ 2) ∂gaussMeasure
            + ∫⁻ x in tailSet R,
                ENNReal.ofReal ((gaussDirichlet (fun z : ℝ => p.eval z) x) ^ 2) ∂gaussMeasure) := by
  have hm1 : Measurable fun x : ℝ =>
      (tailSet R).indicator (fun y : ℝ => ENNReal.ofReal ((p.eval y) ^ 2)) x :=
    (ENNReal.measurable_ofReal.comp ((Polynomial.continuous p).pow 2).measurable).indicator
      (measurableSet_tailSet R)
  have hm2 : Measurable fun x : ℝ =>
      (tailSet R).indicator (fun y : ℝ => ENNReal.ofReal (((derivative p).eval y) ^ 2)) x :=
    (ENNReal.measurable_ofReal.comp
      ((Polynomial.continuous (derivative p)).pow 2).measurable).indicator
      (measurableSet_tailSet R)
  have hcont3 : Continuous fun y : ℝ => gaussDirichlet (fun z : ℝ => p.eval z) y := by
    have hfun : (fun y : ℝ => gaussDirichlet (fun z : ℝ => p.eval z) y)
        = fun y : ℝ => (dirichletPoly p).eval y := funext (gaussDirichlet_eval p)
    rw [hfun]
    exact (contDiff_eval_two (dirichletPoly p)).continuous
  have hm3 : Measurable fun x : ℝ =>
      (tailSet R).indicator
        (fun y : ℝ => ENNReal.ofReal ((gaussDirichlet (fun z : ℝ => p.eval z) y) ^ 2)) x :=
    (ENNReal.measurable_ofReal.comp (hcont3.pow 2).measurable).indicator
      (measurableSet_tailSet R)
  calc ∫⁻ x, ENNReal.ofReal ((gaussDirichlet (fun y : ℝ => cutFn R y * p.eval y) x
        - gaussDirichlet (fun y : ℝ => p.eval y) x) ^ 2) ∂gaussMeasure
      ≤ ∫⁻ x, (ENNReal.ofReal annulusConst *
          ((tailSet R).indicator (fun y : ℝ => ENNReal.ofReal ((p.eval y) ^ 2)) x
            + (tailSet R).indicator (fun y : ℝ => ENNReal.ofReal (((derivative p).eval y) ^ 2)) x
            + (tailSet R).indicator
                (fun y : ℝ => ENNReal.ofReal ((gaussDirichlet (fun z : ℝ => p.eval z) y) ^ 2)) x))
          ∂gaussMeasure := by
        refine lintegral_mono fun x => ?_
        refine le_trans (ENNReal.ofReal_le_ofReal (sq_gaussDirichlet_cutFn_mul_sub_le hR p x)) ?_
        rw [ENNReal.ofReal_mul annulusConst_pos.le]
        exact mul_le_mul_right (ofReal_indicator_sum_eq R p x).le _
    _ = ENNReal.ofReal annulusConst *
          (∫⁻ x, (tailSet R).indicator (fun y : ℝ => ENNReal.ofReal ((p.eval y) ^ 2)) x
            ∂gaussMeasure)
        + ENNReal.ofReal annulusConst *
          (∫⁻ x, (tailSet R).indicator (fun y : ℝ => ENNReal.ofReal (((derivative p).eval y) ^ 2)) x
            ∂gaussMeasure)
        + ENNReal.ofReal annulusConst *
          (∫⁻ x, (tailSet R).indicator
            (fun y : ℝ => ENNReal.ofReal ((gaussDirichlet (fun z : ℝ => p.eval z) y) ^ 2)) x
            ∂gaussMeasure) := by
        rw [show (fun x : ℝ => ENNReal.ofReal annulusConst *
            ((tailSet R).indicator (fun y : ℝ => ENNReal.ofReal ((p.eval y) ^ 2)) x
              + (tailSet R).indicator
                  (fun y : ℝ => ENNReal.ofReal (((derivative p).eval y) ^ 2)) x
              + (tailSet R).indicator
                  (fun y : ℝ => ENNReal.ofReal ((gaussDirichlet (fun z : ℝ => p.eval z) y) ^ 2)) x))
            = fun x : ℝ => ENNReal.ofReal annulusConst *
                (tailSet R).indicator (fun y : ℝ => ENNReal.ofReal ((p.eval y) ^ 2)) x
              + ENNReal.ofReal annulusConst *
                (tailSet R).indicator (fun y : ℝ => ENNReal.ofReal (((derivative p).eval y) ^ 2)) x
              + ENNReal.ofReal annulusConst *
                (tailSet R).indicator
                  (fun y : ℝ => ENNReal.ofReal ((gaussDirichlet (fun z : ℝ => p.eval z) y) ^ 2)) x
            from by funext x; ring]
        have hC1 : Measurable fun x : ℝ => ENNReal.ofReal annulusConst *
            (tailSet R).indicator (fun y : ℝ => ENNReal.ofReal ((p.eval y) ^ 2)) x :=
          hm1.const_mul _
        have hC2 : Measurable fun x : ℝ => ENNReal.ofReal annulusConst *
            (tailSet R).indicator (fun y : ℝ => ENNReal.ofReal (((derivative p).eval y) ^ 2)) x :=
          hm2.const_mul _
        have hC3 : Measurable fun x : ℝ => ENNReal.ofReal annulusConst *
            (tailSet R).indicator
              (fun y : ℝ => ENNReal.ofReal ((gaussDirichlet (fun z : ℝ => p.eval z) y) ^ 2)) x :=
          hm3.const_mul _
        rw [lintegral_add_right
          (f := fun x : ℝ => ENNReal.ofReal annulusConst *
              (tailSet R).indicator (fun y : ℝ => ENNReal.ofReal ((p.eval y) ^ 2)) x
            + ENNReal.ofReal annulusConst *
              (tailSet R).indicator (fun y : ℝ => ENNReal.ofReal (((derivative p).eval y) ^ 2)) x)
          (g := fun x : ℝ => ENNReal.ofReal annulusConst *
              (tailSet R).indicator
                (fun y : ℝ => ENNReal.ofReal ((gaussDirichlet (fun z : ℝ => p.eval z) y) ^ 2)) x)
          (μ := gaussMeasure) hC3]
        rw [lintegral_add_left (f := fun x : ℝ => ENNReal.ofReal annulusConst *
            (tailSet R).indicator (fun y : ℝ => ENNReal.ofReal ((p.eval y) ^ 2)) x)
          (μ := gaussMeasure) hC1
          (fun x : ℝ => ENNReal.ofReal annulusConst *
            (tailSet R).indicator (fun y : ℝ => ENNReal.ofReal (((derivative p).eval y) ^ 2)) x)]
        rw [lintegral_const_mul'' (μ := gaussMeasure) _ hm1.aemeasurable,
          lintegral_const_mul'' (μ := gaussMeasure) _ hm2.aemeasurable,
          lintegral_const_mul'' (μ := gaussMeasure) _ hm3.aemeasurable]
    _ = ENNReal.ofReal annulusConst *
          ((∫⁻ x, (tailSet R).indicator (fun y : ℝ => ENNReal.ofReal ((p.eval y) ^ 2)) x
              ∂gaussMeasure)
            + (∫⁻ x, (tailSet R).indicator
                (fun y : ℝ => ENNReal.ofReal (((derivative p).eval y) ^ 2)) x ∂gaussMeasure)
            + (∫⁻ x, (tailSet R).indicator
                (fun y : ℝ => ENNReal.ofReal ((gaussDirichlet (fun z : ℝ => p.eval z) y) ^ 2)) x
                ∂gaussMeasure)) := by
        ring
    _ = ENNReal.ofReal annulusConst *
          (∫⁻ x in tailSet R, ENNReal.ofReal ((p.eval x) ^ 2) ∂gaussMeasure
            + ∫⁻ x in tailSet R, ENNReal.ofReal (((derivative p).eval x) ^ 2) ∂gaussMeasure
            + ∫⁻ x in tailSet R,
                ENNReal.ofReal ((gaussDirichlet (fun z : ℝ => p.eval z) x) ^ 2) ∂gaussMeasure) := by
        rw [lintegral_indicator (measurableSet_tailSet R) _,
          lintegral_indicator (measurableSet_tailSet R) _,
          lintegral_indicator (measurableSet_tailSet R) _]

/-- **The cutoff term of the graph-norm approximation.**  `p − χ_R p = (1 − χ_R) p` is supported
off the ball, so its squared `γ`-mass is bounded by the tail integral of `p²`. -/
theorem lintegral_one_sub_cutFn_sq_le {R : ℝ} (hR : 0 < R) (p : Polynomial ℝ) :
    ∫⁻ x, ENNReal.ofReal ((p.eval x - cutFn R x * p.eval x) ^ 2) ∂gaussMeasure
      ≤ ∫⁻ x in tailSet R, ENNReal.ofReal ((p.eval x) ^ 2) ∂gaussMeasure := by
  have hpt : ∀ x : ℝ, ENNReal.ofReal ((p.eval x - cutFn R x * p.eval x) ^ 2)
      ≤ (tailSet R).indicator (fun y : ℝ => ENNReal.ofReal ((p.eval y) ^ 2)) x := by
    intro x
    by_cases hx : x ∈ tailSet R
    · rw [Set.indicator_of_mem hx]
      refine ENNReal.ofReal_le_ofReal ?_
      have h1 : |1 - cutFn R x| ≤ 1 := by
        rw [abs_le]
        exact ⟨by linarith [(abs_le.mp (abs_cutFn_le_one R x)).2],
          by linarith [cutFn_nonneg R x]⟩
      have hsq1 : (1 - cutFn R x) ^ 2 ≤ 1 := by
        rw [← sq_abs (1 - cutFn R x)]
        nlinarith [abs_nonneg (1 - cutFn R x)]
      have h2 : p.eval x - cutFn R x * p.eval x = (1 - cutFn R x) * p.eval x := by ring
      rw [h2, mul_pow]
      nlinarith [sq_nonneg (p.eval x)]
    · rw [Set.indicator_of_notMem hx]
      have habs : |x| < R := lt_of_not_ge hx
      have hsq : x ^ 2 < R ^ 2 := by nlinarith [sq_abs x, abs_nonneg x]
      have hone : cutFn R x = 1 := cutFn_eq_one hR hsq.le
      rw [hone]
      simp
  calc ∫⁻ x, ENNReal.ofReal ((p.eval x - cutFn R x * p.eval x) ^ 2) ∂gaussMeasure
      ≤ ∫⁻ x, (tailSet R).indicator (fun y : ℝ => ENNReal.ofReal ((p.eval y) ^ 2)) x
          ∂gaussMeasure := lintegral_mono hpt
    _ = ∫⁻ x in tailSet R, ENNReal.ofReal ((p.eval x) ^ 2) ∂gaussMeasure :=
        lintegral_indicator (measurableSet_tailSet R) _

/-- **A squared `ofReal` bound becomes a norm bound.** -/
theorem norm_lt_of_ofReal_sq_lt {u : Lp ℝ 2 gaussMeasure} {ε : ℝ} (hε : 0 < ε)
    (h : ENNReal.ofReal (‖u‖ ^ 2) < ENNReal.ofReal (ε ^ 2)) : ‖u‖ < ε := by
  have hsq : ‖u‖ ^ 2 < ε ^ 2 := (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mp h
  nlinarith [norm_nonneg u]

/-- **A radius beyond which all three tails are small.**  `exists_lintegral_tail_lt` for `p`, `p'`
and `T p`, taken at a common radius `R ≥ 1` by monotonicity of the tail integrals. -/
theorem exists_cutFn_tail (p : Polynomial ℝ) {δ : ℝ≥0∞} (hδ : 0 < δ) :
    ∃ R : ℝ, 1 ≤ R ∧
      (∫⁻ x in tailSet R, ENNReal.ofReal ((p.eval x) ^ 2) ∂gaussMeasure < δ) ∧
      (∫⁻ x in tailSet R, ENNReal.ofReal (((derivative p).eval x) ^ 2) ∂gaussMeasure < δ) ∧
      (∫⁻ x in tailSet R, ENNReal.ofReal ((gaussDirichlet (fun z : ℝ => p.eval z) x) ^ 2)
        ∂gaussMeasure < δ) := by
  obtain ⟨R1, h1⟩ := exists_lintegral_tail_lt p hδ
  obtain ⟨R2, h2⟩ := exists_lintegral_tail_lt (derivative p) hδ
  obtain ⟨R3, h3⟩ := exists_lintegral_tail_lt (dirichletPoly p) hδ
  set R : ℝ := max (max (max R1 R2) R3) 1 with hRdef
  have hR1R : R1 ≤ R := by
    rw [hRdef]
    exact le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) (le_max_left _ _)
  have hR2R : R2 ≤ R := by
    rw [hRdef]
    exact le_trans (le_max_right _ _) (le_trans (le_max_left _ _) (le_max_left _ _))
  have hR3R : R3 ≤ R := by
    rw [hRdef]
    exact le_trans (le_max_right _ _) (le_max_left _ _)
  refine ⟨R, by rw [hRdef]; exact le_max_right _ _, ?_, ?_, ?_⟩
  · exact lt_of_le_of_lt (lintegral_mono_set (tailSet_antitone hR1R)) h1
  · exact lt_of_le_of_lt (lintegral_mono_set (tailSet_antitone hR2R)) h2
  · rw [show (∫⁻ x in tailSet R,
        ENNReal.ofReal ((gaussDirichlet (fun z : ℝ => p.eval z) x) ^ 2) ∂gaussMeasure)
        = ∫⁻ x in tailSet R, ENNReal.ofReal (((dirichletPoly p).eval x) ^ 2) ∂gaussMeasure from
      setLIntegral_congr_fun (measurableSet_tailSet _)
        (fun x _ => by rw [gaussDirichlet_eval])]
    exact lt_of_le_of_lt (lintegral_mono_set (tailSet_antitone hR3R)) h3

/-! ## The graph-norm approximation -/

-- The assembly threads the three tail bounds, the `ENNReal` arithmetic of the threshold and the
-- norm bridge through one proof; the heartbeat budget is raised for the `field_simp` normalization
-- of the threshold, not for any search.
set_option maxHeartbeats 1200000 in
/-- **The graph-norm approximation of a polynomial class.**  For every `ε` the compactly supported
class `χ_R p` is within `ε` of `p` in norm, and its image under `T` is within `ε` of `T p`, once `R`
is large enough that the three tails of `p`, `p'` and `T p` are below a threshold chosen from
`ε` and the annulus constant.  The two `ε`-bounds are the two halves of `Approximable`, and the
threshold is `ε² / (12 (C + 1))`: the annulus constant multiplies three of those, and `C < 4(C+1)`
keeps the product below `ε²`. -/
theorem approximable_polyLp (p : Polynomial ℝ) (hp : polyLp p ∈ hermiteSpan) :
    Approximable (polyLp p) hp := by
  intro ε hε
  set K : ℝ := annulusConst + 1 with hKdef
  have hKpos : 0 < K := by rw [hKdef]; linarith [annulusConst_pos]
  have hK1 : 1 ≤ K := by rw [hKdef]; linarith [annulusConst_pos]
  have hdpos : 0 < ε ^ 2 / (12 * K) := by positivity
  set δ : ℝ≥0∞ := ENNReal.ofReal (ε ^ 2 / (12 * K)) with hδdef
  have hδpos : 0 < δ := ENNReal.ofReal_pos.mpr hdpos
  have hδle : δ ≤ ENNReal.ofReal (ε ^ 2) := by
    rw [hδdef]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [div_le_iff₀ (by positivity)]
    nlinarith [sq_nonneg ε, hε.le]
  obtain ⟨R, hR1, ht1, ht2, ht3⟩ := exists_cutFn_tail p hδpos
  have hR0 : 0 < R := lt_of_lt_of_le zero_lt_one hR1
  refine ⟨cutCore hR0 p, ?_, ?_⟩
  · -- the cutoff term: `p` and `χ_R p` are close
    have hF : MemLp (fun x : ℝ => p.eval x) 2 gaussMeasure := memLp_eval p
    have hG : MemLp (fun x : ℝ => cutFn R x * p.eval x) 2 gaussMeasure := memLp_cutFn_mul_eval R p
    have hcoe : ((cutCore hR0 p : gaussCore) : Lp ℝ 2 gaussMeasure)
        = hG.toLp (fun x : ℝ => cutFn R x * p.eval x) := rfl
    have hpoly : polyLp p = hF.toLp (fun x : ℝ => p.eval x) := rfl
    have hlt : ENNReal.ofReal
        (‖hF.toLp (fun x : ℝ => p.eval x) - hG.toLp (fun x : ℝ => cutFn R x * p.eval x)‖ ^ 2)
        < ENNReal.ofReal (ε ^ 2) := by
      rw [ofReal_norm_toLp_sub_sq (fun x : ℝ => p.eval x)
        (fun x : ℝ => cutFn R x * p.eval x) hF hG]
      exact lt_of_lt_of_le (lt_of_le_of_lt (lintegral_one_sub_cutFn_sq_le hR0 p) ht1) hδle
    have hnorm := norm_lt_of_ofReal_sq_lt hε hlt
    rw [hpoly, hcoe]
    exact hnorm
  · -- the annulus term: `T p` and `T (χ_R p)` are close
    have hFcon : ContDiff ℝ 2 (fun x : ℝ => cutFn R x * p.eval x) := contDiff_cutFn_mul_eval R p
    have hFc : HasCompactSupport (fun x : ℝ => cutFn R x * p.eval x) :=
      hasCompactSupport_cutFn_mul_eval hR0 p
    have hFd : MemLp (fun x : ℝ => (dirichletPoly p).eval x) 2 gaussMeasure :=
      memLp_eval (dirichletPoly p)
    have hGd : MemLp (gaussDirichlet (fun x : ℝ => cutFn R x * p.eval x)) 2 gaussMeasure :=
      memLp_gaussDirichlet hFcon hFc
    have hpOp : (polyOp ⟨polyLp p, hp⟩ : Lp ℝ 2 gaussMeasure) = polyLp (dirichletPoly p) :=
      polyOpH_coe p hp
    have hgOp : gaussOpFun (cutCore hR0 p)
        = hGd.toLp (gaussDirichlet (fun x : ℝ => cutFn R x * p.eval x)) :=
      gaussOpFun_eq_toLp (f := cutCore hR0 p) (F := fun x : ℝ => cutFn R x * p.eval x)
        hFcon hFc (cutCore_coeFn hR0 p)
    have hfld : polyLp (dirichletPoly p) = hFd.toLp (fun x : ℝ => (dirichletPoly p).eval x) := rfl
    have hflip : (∫⁻ x, ENNReal.ofReal (((dirichletPoly p).eval x
          - gaussDirichlet (fun y : ℝ => cutFn R y * p.eval y) x) ^ 2) ∂gaussMeasure)
        = ∫⁻ x, ENNReal.ofReal ((gaussDirichlet (fun y : ℝ => cutFn R y * p.eval y) x
            - gaussDirichlet (fun y : ℝ => p.eval y) x) ^ 2) ∂gaussMeasure := by
      refine lintegral_congr fun x => ?_
      rw [gaussDirichlet_eval]
      ring_nf
    have hsum_lt : (∫⁻ x in tailSet R, ENNReal.ofReal ((p.eval x) ^ 2) ∂gaussMeasure)
          + (∫⁻ x in tailSet R, ENNReal.ofReal (((derivative p).eval x) ^ 2) ∂gaussMeasure)
          + (∫⁻ x in tailSet R,
              ENNReal.ofReal ((gaussDirichlet (fun z : ℝ => p.eval z) x) ^ 2) ∂gaussMeasure)
        < δ + δ + δ := ENNReal.add_lt_add (ENNReal.add_lt_add ht1 ht2) ht3
    have hCne : ENNReal.ofReal annulusConst ≠ 0 := (ENNReal.ofReal_pos.mpr annulusConst_pos).ne'
    have hCtop : ENNReal.ofReal annulusConst ≠ ∞ := ENNReal.ofReal_ne_top
    have hmul : ENNReal.ofReal annulusConst *
          ((∫⁻ x in tailSet R, ENNReal.ofReal ((p.eval x) ^ 2) ∂gaussMeasure)
            + (∫⁻ x in tailSet R, ENNReal.ofReal (((derivative p).eval x) ^ 2) ∂gaussMeasure)
            + (∫⁻ x in tailSet R,
                ENNReal.ofReal ((gaussDirichlet (fun z : ℝ => p.eval z) x) ^ 2) ∂gaussMeasure))
        < ENNReal.ofReal annulusConst * (δ + δ + δ) :=
      ENNReal.mul_lt_mul_right hCne hCtop hsum_lt
    have hfin : ENNReal.ofReal annulusConst * (δ + δ + δ) < ENNReal.ofReal (ε ^ 2) := by
      have hd3 : δ + δ + δ
          = ENNReal.ofReal (ε ^ 2 / (12 * K) + ε ^ 2 / (12 * K) + ε ^ 2 / (12 * K)) := by
        rw [hδdef, ← ENNReal.ofReal_add hdpos.le hdpos.le,
          ← ENNReal.ofReal_add (by positivity) hdpos.le]
      rw [hd3, ← ENNReal.ofReal_mul annulusConst_pos.le]
      refine (ENNReal.ofReal_lt_ofReal_iff (by positivity)).mpr ?_
      have hval : annulusConst *
            (ε ^ 2 / (12 * K) + ε ^ 2 / (12 * K) + ε ^ 2 / (12 * K))
          = ε ^ 2 * (annulusConst / (4 * K)) := by
        field_simp
        ring
      rw [hval]
      have hq : annulusConst / (4 * K) < 1 := by
        rw [div_lt_one (by positivity), hKdef]
        linarith [annulusConst_pos]
      nlinarith [mul_lt_mul_of_pos_left hq (by positivity : (0 : ℝ) < ε ^ 2)]
    have hlt : ENNReal.ofReal
        (‖hFd.toLp (fun x : ℝ => (dirichletPoly p).eval x)
          - hGd.toLp (gaussDirichlet (fun x : ℝ => cutFn R x * p.eval x))‖ ^ 2)
        < ENNReal.ofReal (ε ^ 2) := by
      rw [ofReal_norm_toLp_sub_sq (fun x : ℝ => (dirichletPoly p).eval x)
        (gaussDirichlet (fun x : ℝ => cutFn R x * p.eval x)) hFd hGd, hflip]
      exact lt_of_le_of_lt (lintegral_sq_sub_le hR1 p) (lt_trans hmul hfin)
    have hnorm := norm_lt_of_ofReal_sq_lt hε hlt
    rw [hpOp, hgOp, hfld]
    exact hnorm

/-- **The graph-norm approximation holds for every Hermite-span class**: the approximation is
additive, homogeneous and vanishes at `0`, so it propagates from the Hermite generators
(`polyGraphApprox_of_hermite`), which `approximable_polyLp` supplies. -/
theorem polyGraphApprox_holds : PolyGraphApprox :=
  polyGraphApprox_of_hermite fun n =>
    approximable_polyLp (hermiteR n) (Submodule.subset_span ⟨n, rfl⟩)

end

end BookProof.YangMillsPolyAnnulus
