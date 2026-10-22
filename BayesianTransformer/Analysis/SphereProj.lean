module

public import Mathlib.Analysis.InnerProductSpace.Calculus
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Analysis.Calculus.Deriv.Inv

/-!
# Milestone 1: The hyperspherical projection and its differential

We formalize the metric projection `Π(v) = v / ‖v‖` onto the unit sphere of a real inner
product space, compute its Fréchet derivative

  `dΠ(v) = ‖v‖⁻¹ • (I - (v ⊗ v) / ‖v‖²)`,

and prove the operator-norm bounds `‖dΠ(v)‖ ≤ ‖v‖⁻¹` and, on an `ε`-separated domain,
`‖dΠ(v)‖ ≤ ε⁻¹`.

Note: the plan wrote the coefficient as `‖v‖⁻³`, which is not valid Lean syntax; we write it as
`(‖v‖ ^ 3)⁻¹`. The `[CompleteSpace E]` assumption of the plan is not needed and is omitted.
-/

@[expose] public section

namespace BayesianTransformer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- The hyperspherical projection onto the unit sphere. -/
noncomputable def sphereProj (v : E) : E := (‖v‖)⁻¹ • v

/-- The norm of `sphereProj v` is `1` for `v ≠ 0`. -/
theorem norm_sphereProj {v : E} (hv : v ≠ 0) : ‖sphereProj v‖ = 1 := by
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  rw [sphereProj, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn), inv_mul_cancel₀ hn.ne']

/-- Derivative of `x ↦ ‖x‖⁻¹` away from the origin. -/
theorem norm_inv_hasFDerivAt {v : E} (hv : v ≠ 0) :
    HasFDerivAt (fun x : E => ‖x‖⁻¹) (-((‖v‖ ^ 3)⁻¹) • innerSL ℝ v) v := by
  have hn : ‖v‖ ≠ 0 := norm_ne_zero_iff.mpr hv
  have h1 : HasFDerivAt (fun x : E => Real.sqrt (‖x‖ ^ 2))
      ((1 / (2 * Real.sqrt (‖v‖ ^ 2))) •
        (2 • (innerSL ℝ v).comp (ContinuousLinearMap.id ℝ E))) v :=
    ((hasFDerivAt_id v).norm_sq).sqrt (by positivity)
  have h2 := (hasDerivAt_inv (x := Real.sqrt (‖v‖ ^ 2)) (by positivity)).comp_hasFDerivAt v h1
  simp only [Real.sqrt_sq (norm_nonneg _)] at h2
  convert h2 using 1
  ext x
  simp [smul_smul]
  field_simp

/-- Differential of `sphereProj`: `dΠ(v) = ‖v‖⁻¹ • I - ‖v‖⁻³ • (v ⊗ v)`. -/
theorem sphereProj_hasFDerivAt {v : E} (hv : v ≠ 0) :
    HasFDerivAt sphereProj
      ((‖v‖⁻¹ • ContinuousLinearMap.id ℝ E) -
       ((‖v‖ ^ 3)⁻¹ • (ContinuousLinearMap.smulRight (innerSL ℝ v) v))) v := by
  have h := (norm_inv_hasFDerivAt hv).smul (hasFDerivAt_id v)
  convert h using 1
  ext x
  simp [sub_eq_add_neg, neg_smul, smul_smul]

/-- `sphereProj` is differentiable away from the origin. -/
theorem sphereProj_differentiableAt {v : E} (hv : v ≠ 0) : DifferentiableAt ℝ sphereProj v :=
  (sphereProj_hasFDerivAt hv).differentiableAt

/-- The map `h ↦ h - (⟪v, h⟫ / ‖v‖²) • v` (the orthogonal projection onto `v⟂`) does not
increase norms. -/
theorem norm_sub_orthProj_le (v h : E) (hv : v ≠ 0) :
    ‖h - (inner ℝ v h / ‖v‖ ^ 2) • v‖ ≤ ‖h‖ := by
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have key : ‖h - (inner ℝ v h / ‖v‖ ^ 2) • v‖ ^ 2 = ‖h‖ ^ 2 - inner ℝ v h ^ 2 / ‖v‖ ^ 2 := by
    rw [norm_sub_sq_real, norm_smul, inner_smul_right, real_inner_comm, Real.norm_eq_abs, mul_pow,
      sq_abs]
    field_simp
    ring
  have : ‖h - (inner ℝ v h / ‖v‖ ^ 2) • v‖ ^ 2 ≤ ‖h‖ ^ 2 := by
    rw [key]
    have : 0 ≤ inner ℝ v h ^ 2 / ‖v‖ ^ 2 := by positivity
    linarith
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (norm_nonneg _) two_ne_zero).mp this

/-- The explicit differential has operator norm at most `‖v‖⁻¹`. -/
theorem sphereProj_deriv_opNorm_le {v : E} (hv : v ≠ 0) :
    ‖(‖v‖⁻¹ • ContinuousLinearMap.id ℝ E) -
       ((‖v‖ ^ 3)⁻¹ • (ContinuousLinearMap.smulRight (innerSL ℝ v) v))‖ ≤ ‖v‖⁻¹ := by
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun h => ?_
  have : ((‖v‖⁻¹ • ContinuousLinearMap.id ℝ E) -
       ((‖v‖ ^ 3)⁻¹ • (ContinuousLinearMap.smulRight (innerSL ℝ v) v))) h
       = ‖v‖⁻¹ • (h - (inner ℝ v h / ‖v‖ ^ 2) • v) := by
    simp only [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.id_apply, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply,
      smul_sub, smul_smul]
    congr 2
    field_simp
  rw [this, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hn)]
  exact mul_le_mul_of_nonneg_left (norm_sub_orthProj_le v h hv) (by positivity)

/-- The operator norm bound: `‖dΠ(v)‖_op ≤ 1 / ‖v‖`. -/
theorem sphereProj_fderiv_opNorm_le {v : E} (hv : v ≠ 0) :
    ‖fderiv ℝ sphereProj v‖ ≤ ‖v‖⁻¹ := by
  rw [(sphereProj_hasFDerivAt hv).fderiv]
  exact sphereProj_deriv_opNorm_le hv

/-- Uniform operator norm bound on an `ε`-separated domain. -/
theorem sphereProj_fderiv_opNorm_uniform {ε : ℝ} (hε : 0 < ε) {v : E} (hv : ε ≤ ‖v‖) :
    ‖fderiv ℝ sphereProj v‖ ≤ ε⁻¹ := by
  have hv0 : v ≠ 0 := norm_pos_iff.mp (hε.trans_le hv)
  exact (sphereProj_fderiv_opNorm_le hv0).trans (inv_anti₀ hε hv)

end BayesianTransformer
