/-
Copyright (c) 2026.  All rights reserved.

# A smooth cutoff with the right derivative scaling

The annulus estimate in `ChapterYangMillsPolyGraphNorm` needs a cutoff `χ_R` that is `1` on
`[-R, R]`, vanishes off `[-√2 R, √2 R]`, and whose derivatives scale as `‖χ_R'‖ ≤ C/R`,
`‖χ_R''‖ ≤ C/R²`.  The natural candidate is `smoothTransition` composed with `2 - x²/R²`: the
argument is a polynomial in `x`, so no absolute value has to be differentiated, `χ_R = 1` is
`2 - x²/R² ≥ 1` i.e. `x² ≤ R²`, and vanishing is `2 - x²/R² ≤ 0` i.e. `x² ≥ 2R²`.  On the tail
`R² < x²` one has `|x| ≤ √2 R` *only* on the annulus, which is exactly the region where `χ_R` is
neither `1` nor `0`; there the factor `2|x|/R²` from the chain rule is `O(1/R)`.

The derivative bounds are not available in closed form (`smoothTransition` has no `deriv` formula in
the library), and they do not have to be: `deriv smoothTransition` and `deriv (deriv
smoothTransition)` are continuous and vanish off `[0, 1]`, so compactness bounds them.
`exists_deriv_bound` and `exists_deriv2_bound` extract the constants once, `sDerivBound` and
`sDerivBound2` name them, and `cutFn_deriv_bound` / `cutFn_deriv2_bound` transfer them to `χ_R`.
-/
import BookProof.Qym.ChapterYangMillsPolyTail

open Filter MeasureTheory Topology

namespace BookProof.YangMillsPolyCutoff

noncomputable section

/-! ## Boundedness of the derivatives of `smoothTransition` -/

/-- `smoothTransition` is constant off `[0, 1]`, so its derivative vanishes there. -/
theorem deriv_smoothTransition_eq_zero_of_notMem {x : ℝ} (hx : x ∉ Set.Icc (0 : ℝ) 1) :
    deriv Real.smoothTransition x = 0 := by
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  rcases hx with hleft | hright
  · have hev : Real.smoothTransition =ᶠ[nhds x] fun _ => (0 : ℝ) := by
      filter_upwards [Iio_mem_nhds hleft] with y hy
      exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
    rw [hev.deriv_eq, deriv_const]
  · have hev : Real.smoothTransition =ᶠ[nhds x] fun _ => (1 : ℝ) := by
      filter_upwards [Ioi_mem_nhds hright] with y hy
      exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
    rw [hev.deriv_eq, deriv_const]

/-- `deriv smoothTransition` vanishes off `[0, 1]`, hence so does its derivative. -/
theorem deriv_deriv_smoothTransition_eq_zero_of_notMem {x : ℝ}
    (hx : x ∉ Set.Icc (0 : ℝ) 1) : deriv (deriv Real.smoothTransition) x = 0 := by
  have hev : deriv Real.smoothTransition =ᶠ[nhds x] fun _ => (0 : ℝ) := by
    rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
    rcases hx with hleft | hright
    · filter_upwards [Iio_mem_nhds hleft] with y hy
      exact deriv_smoothTransition_eq_zero_of_notMem fun hmem => absurd hmem.1 (not_le.mpr hy)
    · filter_upwards [Ioi_mem_nhds hright] with y hy
      exact deriv_smoothTransition_eq_zero_of_notMem fun hmem => absurd hmem.2 (not_le.mpr hy)
  rw [hev.deriv_eq, deriv_const]

/-- The derivative of `smoothTransition` is continuous. -/
theorem continuous_deriv_smoothTransition : Continuous (deriv Real.smoothTransition) :=
  (Real.smoothTransition.contDiff (n := 2)).continuous_deriv (by norm_num)

/-- The second derivative of `smoothTransition` is continuous. -/
theorem continuous_deriv_deriv_smoothTransition :
    Continuous (deriv (deriv Real.smoothTransition)) :=
  ((Real.smoothTransition.contDiff (n := 2)).deriv').continuous_deriv le_rfl

/-- **A bound for the derivative of `smoothTransition`.** -/
theorem exists_deriv_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |deriv Real.smoothTransition x| ≤ C := by
  obtain ⟨x₀, -, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1))
    continuous_deriv_smoothTransition.abs.continuousOn
  refine ⟨|deriv Real.smoothTransition x₀|, abs_nonneg _, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · exact hmax hx
  · rw [deriv_smoothTransition_eq_zero_of_notMem hx, abs_zero]
    exact abs_nonneg _

/-- **A bound for the second derivative of `smoothTransition`.** -/
theorem exists_deriv2_bound :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ x : ℝ, |deriv (deriv Real.smoothTransition) x| ≤ C := by
  obtain ⟨x₀, -, hmax⟩ := isCompact_Icc.exists_isMaxOn
    (Set.nonempty_Icc.mpr (by norm_num : (0 : ℝ) ≤ 1))
    continuous_deriv_deriv_smoothTransition.abs.continuousOn
  refine ⟨|deriv (deriv Real.smoothTransition) x₀|, abs_nonneg _, fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · exact hmax hx
  · rw [deriv_deriv_smoothTransition_eq_zero_of_notMem hx, abs_zero]
    exact abs_nonneg _

/-- A uniform bound for `|smoothTransition'|`. -/
noncomputable def sDerivBound : ℝ := Classical.choose exists_deriv_bound

/-- A uniform bound for `|smoothTransition''|`. -/
noncomputable def sDerivBound2 : ℝ := Classical.choose exists_deriv2_bound

theorem sDerivBound_nonneg : 0 ≤ sDerivBound := (Classical.choose_spec exists_deriv_bound).1

theorem sDerivBound2_nonneg : 0 ≤ sDerivBound2 := (Classical.choose_spec exists_deriv2_bound).1

theorem abs_deriv_smoothTransition_le (x : ℝ) :
    |deriv Real.smoothTransition x| ≤ sDerivBound :=
  (Classical.choose_spec exists_deriv_bound).2 x

theorem abs_deriv_deriv_smoothTransition_le (x : ℝ) :
    |deriv (deriv Real.smoothTransition) x| ≤ sDerivBound2 :=
  (Classical.choose_spec exists_deriv2_bound).2 x

end

end BookProof.YangMillsPolyCutoff
namespace BookProof.YangMillsPolyCutoff

open Filter MeasureTheory Topology

noncomputable section

/-! ## The cutoff `χ_R` -/

/-- **The cutoff `χ_R(x) = smoothTransition (2 - x²/R²)`**: `1` for `x² ≤ R²`, `0` for
`x² ≥ 2R²`, and smooth, because its argument is a polynomial in `x`. -/
noncomputable def cutFn (R : ℝ) : ℝ → ℝ :=
  fun x => Real.smoothTransition (2 - x ^ 2 / R ^ 2)

/-- The cutoff is `1` on the ball of radius `R`. -/
theorem cutFn_eq_one {R : ℝ} (hR : 0 < R) {x : ℝ} (hx : x ^ 2 ≤ R ^ 2) : cutFn R x = 1 := by
  refine Real.smoothTransition.one_of_one_le ?_
  have hR2 : (0 : ℝ) < R ^ 2 := by positivity
  have h := (div_le_one hR2).2 hx
  linarith

/-- The cutoff vanishes where `x² ≥ 2R²`. -/
theorem cutFn_eq_zero {R : ℝ} {x : ℝ} (hx : 2 ≤ x ^ 2 / R ^ 2) : cutFn R x = 0 :=
  Real.smoothTransition.zero_of_nonpos (by linarith)

/-- The cutoff is compactly supported. -/
theorem hasCompactSupport_cutFn {R : ℝ} (hR : 0 < R) : HasCompactSupport (cutFn R) := by
  refine HasCompactSupport.intro
    (isCompact_Icc (a := -(Real.sqrt 2 * |R|)) (b := Real.sqrt 2 * |R|)) ?_
  intro x hx
  refine cutFn_eq_zero ?_
  have hD : (0 : ℝ) ≤ Real.sqrt 2 * |R| := by positivity
  have hD2 : (Real.sqrt 2 * |R|) ^ 2 = 2 * R ^ 2 := by
    rw [mul_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), sq_abs]
  rw [Set.mem_Icc, not_and_or, not_le, not_le] at hx
  have hsq : (Real.sqrt 2 * |R|) ^ 2 < x ^ 2 := by
    rcases hx with h | h
    · nlinarith [h, hD]
    · nlinarith [h, hD]
  rw [le_div_iff₀ (by positivity : (0 : ℝ) < R ^ 2), hD2] at *
  linarith

/-- The cutoff is twice continuously differentiable. -/
theorem contDiff_cutFn (R : ℝ) : ContDiff ℝ 2 (cutFn R) := by
  have h : ContDiff ℝ 2 (fun x : ℝ => 2 - x ^ 2 / R ^ 2) := by fun_prop
  exact (Real.smoothTransition.contDiff (n := 2)).comp h

/-- `deriv smoothTransition` is still `C¹`. -/
theorem contDiff_deriv_smoothTransition : ContDiff ℝ 1 (deriv Real.smoothTransition) :=
  (Real.smoothTransition.contDiff (n := 2)).deriv'

/-- The derivative of the argument `x ↦ 2 - x²/R²`. -/
theorem hasDerivAt_cutArg (R x : ℝ) :
    HasDerivAt (fun y : ℝ => 2 - y ^ 2 / R ^ 2) (-(2 * x / R ^ 2)) x := by
  have h : HasDerivAt (fun y : ℝ => y ^ 2 / R ^ 2) (2 * x / R ^ 2) x := by
    simpa using (hasDerivAt_pow 2 x).div_const (R ^ 2)
  simpa using (hasDerivAt_const (x := x) (c := (2 : ℝ))).sub h

/-- The chain rule, written out. -/
theorem deriv_cutFn (R x : ℝ) :
    deriv (cutFn R) x
      = deriv Real.smoothTransition (2 - x ^ 2 / R ^ 2) * (-(2 * x / R ^ 2)) := by
  have hd : DifferentiableAt ℝ Real.smoothTransition (2 - x ^ 2 / R ^ 2) :=
    ((Real.smoothTransition.contDiff (n := 2)).differentiable (by norm_num)).differentiableAt
  have hu : DifferentiableAt ℝ (fun y : ℝ => 2 - y ^ 2 / R ^ 2) x :=
    (hasDerivAt_cutArg R x).differentiableAt
  have hcomp := deriv_comp x hd hu
  rw [(hasDerivAt_cutArg R x).deriv] at hcomp
  exact hcomp

/-- The derivative of `χ_R`, as a function, is `s'(u)·u'`. -/
theorem deriv_cutFn_fun (R : ℝ) :
    deriv (cutFn R)
      = fun y : ℝ => deriv Real.smoothTransition (2 - y ^ 2 / R ^ 2) * (-(2 * y / R ^ 2)) :=
  funext (deriv_cutFn R)

/-- The second derivative of `χ_R`, from the product and chain rules. -/
theorem hasDerivAt_deriv_cutFn (R x : ℝ) :
    HasDerivAt (deriv (cutFn R))
      (deriv (deriv Real.smoothTransition) (2 - x ^ 2 / R ^ 2) * (-(2 * x / R ^ 2)) ^ 2
        + deriv Real.smoothTransition (2 - x ^ 2 / R ^ 2) * (-(2 / R ^ 2))) x := by
  have hu := hasDerivAt_cutArg R x
  have hA : HasDerivAt (fun y : ℝ => deriv Real.smoothTransition (2 - y ^ 2 / R ^ 2))
      (deriv (deriv Real.smoothTransition) (2 - x ^ 2 / R ^ 2) * (-(2 * x / R ^ 2))) x := by
    have hd : DifferentiableAt ℝ (deriv Real.smoothTransition) (2 - x ^ 2 / R ^ 2) :=
      (contDiff_deriv_smoothTransition.differentiable (by norm_num)).differentiableAt
    simpa using hd.hasDerivAt.comp x hu
  have hB : HasDerivAt (fun y : ℝ => -(2 * y / R ^ 2)) (-(2 / R ^ 2)) x := by
    have h1 : HasDerivAt (fun y : ℝ => (2 : ℝ) * y) 2 x := by
      simpa using (hasDerivAt_id x).const_mul (2 : ℝ)
    simpa using (h1.div_const (R ^ 2)).neg
  have hmul := hA.mul hB
  rw [deriv_cutFn_fun]
  convert hmul using 1
  ring

/-- **The first derivative of the cutoff is `O(|x|/R²)`.** -/
theorem cutFn_deriv_bound (R x : ℝ) :
    |deriv (cutFn R) x| ≤ sDerivBound * (2 * |x| / R ^ 2) := by
  rw [deriv_cutFn, abs_mul]
  have h1 : |deriv Real.smoothTransition (2 - x ^ 2 / R ^ 2)| ≤ sDerivBound :=
    abs_deriv_smoothTransition_le _
  have h2 : |-(2 * x / R ^ 2)| = 2 * |x| / R ^ 2 := by
    rw [abs_neg, abs_div, abs_mul, abs_two, abs_pow, sq_abs]
  rw [h2]
  exact mul_le_mul_of_nonneg_right h1 (by positivity)

/-- **The second derivative of the cutoff is `O(|x|²/R⁴) + O(1/R²)`.** -/
theorem cutFn_deriv2_bound (R x : ℝ) :
    |deriv (deriv (cutFn R)) x|
      ≤ sDerivBound2 * (2 * |x| / R ^ 2) ^ 2 + sDerivBound * (2 / R ^ 2) := by
  have hsplit : |deriv (deriv (cutFn R)) x|
      ≤ |deriv (deriv Real.smoothTransition) (2 - x ^ 2 / R ^ 2) * (-(2 * x / R ^ 2)) ^ 2|
        + |deriv Real.smoothTransition (2 - x ^ 2 / R ^ 2) * (-(2 / R ^ 2))| := by
    rw [(hasDerivAt_deriv_cutFn R x).deriv]
    exact abs_add_le _ _
  have h2 : |(-(2 * x / R ^ 2)) ^ 2| = (2 * |x| / R ^ 2) ^ 2 := by
    rw [abs_pow, abs_neg, abs_div, abs_mul, abs_two, abs_pow, sq_abs]
  have h3 : |-(2 / R ^ 2)| = 2 / R ^ 2 := by
    rw [abs_neg]
    exact abs_of_nonneg (by positivity)
  have hA : |deriv (deriv Real.smoothTransition) (2 - x ^ 2 / R ^ 2) * (-(2 * x / R ^ 2)) ^ 2|
      ≤ sDerivBound2 * (2 * |x| / R ^ 2) ^ 2 := by
    rw [abs_mul, h2]
    exact mul_le_mul_of_nonneg_right (abs_deriv_deriv_smoothTransition_le _) (by positivity)
  have hB : |deriv Real.smoothTransition (2 - x ^ 2 / R ^ 2) * (-(2 / R ^ 2))|
      ≤ sDerivBound * (2 / R ^ 2) := by
    rw [abs_mul, h3]
    exact mul_le_mul_of_nonneg_right (abs_deriv_smoothTransition_le _) (by positivity)
  linarith

end

end BookProof.YangMillsPolyCutoff
