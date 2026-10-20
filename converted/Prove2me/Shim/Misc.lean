import Mathlib

/-!
# Shim: small platform-Mathlib lemmas missing from the pinned Mathlib

Each declaration below has the name and (as used by the converted modules) the statement of
a lemma of the prove2.me platform Mathlib that the pinned Mathlib does not provide.  All are
proved here from the pinned API.
-/

open scoped ENNReal NNReal

section Continuity

variable {α M : Type*} [TopologicalSpace α] [TopologicalSpace M] [Mul M] [ContinuousMul M]
  {f : α → M}

theorem Continuous.const_mul (hf : Continuous f) (c : M) : Continuous fun x => c * f x :=
  continuous_const.mul hf

theorem Continuous.mul_const (hf : Continuous f) (c : M) : Continuous fun x => f x * c :=
  hf.mul continuous_const

end Continuity

section Lp

variable {α : Type*} {E : α → Type*} [∀ i, NormedAddCommGroup (E i)] {p : ℝ≥0∞}

/-- An `ℓᵖ` family stays in `ℓᵖ` after taking norms. -/
theorem Memℓp.norm {f : ∀ i, E i} (hf : Memℓp f p) : Memℓp (fun i => ‖f i‖) p := by
  rcases p.trichotomy with rfl | rfl | hp
  · rw [memℓp_zero_iff] at hf ⊢
    simpa using hf
  · rw [memℓp_infty_iff] at hf ⊢
    simpa using hf
  · rw [memℓp_gen_iff hp] at hf ⊢
    simpa using hf

/-- Domination by a real `ℓᵖ` family: if `‖f i‖ ≤ g i` and `g ∈ ℓᵖ`, then `f ∈ ℓᵖ`. -/
theorem Memℓp.mono {f : ∀ i, E i} {g : α → ℝ} (hg : Memℓp g p) (hfg : ∀ i, ‖f i‖ ≤ g i) :
    Memℓp f p := by
  rcases p.trichotomy with rfl | rfl | hp
  · rw [memℓp_zero_iff] at hg ⊢
    refine hg.subset fun i hi => ?_
    have h1 : 0 < ‖f i‖ := norm_pos_iff.mpr hi
    exact (ne_of_gt (h1.trans_le (hfg i)))
  · rw [memℓp_infty_iff] at hg ⊢
    obtain ⟨C, hC⟩ := hg
    refine ⟨C, ?_⟩
    rintro _ ⟨i, rfl⟩
    exact (hfg i).trans ((le_abs_self _).trans (by simpa using hC ⟨i, rfl⟩))
  · rw [memℓp_gen_iff hp] at hg ⊢
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) hg
    exact Real.rpow_le_rpow (norm_nonneg _) ((hfg i).trans (le_abs_self _) |>.trans_eq
      (Real.norm_eq_abs _).symm) hp.le

/-- Monotonicity of the `ℓᵖ` norm (`p ≠ 0`) under pointwise domination of the norms. -/
theorem lp.norm_mono (hp : p ≠ 0) {x y : lp E p} (h : ∀ i, ‖x i‖ ≤ ‖y i‖) : ‖x‖ ≤ ‖y‖ := by
  rcases p.trichotomy with rfl | rfl | hp'
  · exact absurd rfl hp
  · exact lp.norm_le_of_forall_le (lp.norm_nonneg' y) fun i => (h i).trans (lp.norm_apply_le_norm
      ENNReal.top_ne_zero y i)
  · refine lp.norm_le_of_tsum_le hp' (lp.norm_nonneg' y) ?_
    rw [lp.norm_rpow_eq_tsum hp' y]
    exact Summable.tsum_le_tsum (fun i => Real.rpow_le_rpow (norm_nonneg _) (h i) hp'.le)
      ((memℓp_gen_iff hp').mp (lp.memℓp x)) ((memℓp_gen_iff hp').mp (lp.memℓp y))

end Lp

/-- The ring inverse of a self-adjoint element is self-adjoint. -/
theorem IsSelfAdjoint.ringInverse {R : Type*} [Semiring R] [StarRing R] {a : R}
    (ha : IsSelfAdjoint a) : IsSelfAdjoint (Ring.inverse a) := by
  rw [IsSelfAdjoint, ← Ring.inverse_star, ha.star_eq]

/-- Application of a product of continuous linear endomorphisms. -/
theorem mul_apply_eq_comp {R M : Type*} [Semiring R] [TopologicalSpace M]
    [AddCommMonoid M] [Module R M] (f g : M →L[R] M) (x : M) : (f * g) x = f (g x) := rfl

/-- Application of the identity continuous linear endomorphism. -/
theorem one_apply_eq_self {R M : Type*} [Semiring R] [TopologicalSpace M]
    [AddCommMonoid M] [Module R M] (x : M) : (1 : M →L[R] M) x = x := rfl

/-- The operator norm of a star projection in a C⋆-ring is at most `1`. -/
theorem IsStarProjection.norm_le {A : Type*} [NonUnitalNormedRing A] [StarRing A] [CStarRing A]
    {p : A} (hp : IsStarProjection p) : ‖p‖ ≤ 1 := by
  have h : ‖p‖ * ‖p‖ = ‖p‖ := by
    rw [← CStarRing.norm_star_mul_self, hp.isSelfAdjoint.star_eq, hp.isIdempotentElem.eq]
  by_contra hc
  push_neg at hc
  nlinarith [norm_nonneg p]

/-- `-x log x ≤ 1 - x` for `x ≥ 0`. -/
theorem Real.negMulLog_le_one_sub_self {x : ℝ} (hx : 0 ≤ x) : Real.negMulLog x ≤ 1 - x := by
  rcases hx.eq_or_lt with rfl | hx
  · simp
  have := Real.one_sub_inv_le_log_of_pos hx
  rw [Real.negMulLog]
  have h2 : x * (1 - x⁻¹) ≤ x * Real.log x := mul_le_mul_of_nonneg_left this hx.le
  rw [mul_sub, mul_inv_cancel₀ hx.ne'] at h2
  linarith

namespace ContinuousLinearMap

variable {R M : Type*} [Semiring R] [TopologicalSpace M] [AddCommMonoid M] [Module R M]

/-- The underlying linear map of `1`. -/
theorem toLinearMap_one : ((1 : M →L[R] M) : M →ₗ[R] M) = 1 := rfl

/-- Platform names of `coe_add` / `coe_smul` / `coe_comp`. -/
alias toLinearMap_add := coe_add
alias toLinearMap_smul := coe_smul
alias toLinearMap_comp := coe_comp

end ContinuousLinearMap

/-- `√x ≤ x` exactly when `x = 0` or `1 ≤ x`. -/
theorem Real.sqrt_le_self_iff {x : ℝ} : √x ≤ x ↔ x = 0 ∨ 1 ≤ x := by
  constructor
  · intro h
    rcases lt_trichotomy x 0 with hx | hx | hx
    · linarith [Real.sqrt_nonneg x]
    · exact Or.inl hx
    · right
      have h1 := Real.sq_sqrt hx.le
      have h2 := Real.sqrt_pos.mpr hx
      nlinarith
  · rintro (rfl | h)
    · simp
    · have h1 := Real.sq_sqrt (by linarith : (0:ℝ) ≤ x)
      have h2 := Real.sqrt_nonneg x
      nlinarith

/-- A continuous linear map out of a proper (e.g. finite-dimensional) space is compact. -/
theorem isCompactOperator_of_locallyCompactSpace_rng {𝕜 E F : Type*} [NontriviallyNormedField 𝕜]
    [NormedAddCommGroup E] [NormedSpace 𝕜 E] [ProperSpace E] [TopologicalSpace F]
    [AddCommMonoid F] [Module 𝕜 F] (f : E →L[𝕜] F) : IsCompactOperator f :=
  ⟨f '' Metric.closedBall 0 1, (isCompact_closedBall 0 1).image f.continuous,
    Filter.mem_of_superset (Metric.closedBall_mem_nhds 0 one_pos) (Set.subset_preimage_image _ _)⟩

open MeasureTheory Set in
/-- Fubini for iterated interval integrals over the same interval. -/
theorem intervalIntegral_intervalIntegral_swap {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] {a b : ℝ} {F : ℝ → ℝ → E}
    (hF : IntegrableOn (Function.uncurry F) (uIoc a b ×ˢ uIoc a b)) :
    (∫ x in a..b, ∫ y in a..b, F x y) = ∫ y in a..b, ∫ x in a..b, F x y := by
  have key : ∀ {a b : ℝ}, a ≤ b → IntegrableOn (Function.uncurry F) (uIoc a b ×ˢ uIoc a b) →
      (∫ x in a..b, ∫ y in a..b, F x y) = ∫ y in a..b, ∫ x in a..b, F x y := by
    intro a b hab h
    rw [uIoc_of_le hab] at h
    simp only [intervalIntegral.integral_of_le hab]
    apply MeasureTheory.integral_integral_swap
    rw [Measure.prod_restrict, ← Measure.volume_eq_prod]
    exact h
  rcases le_total a b with hab | hab
  · exact key hab hF
  · have := key hab (by rwa [uIoc_comm])
    simp only [intervalIntegral.integral_symm b a, intervalIntegral.integral_neg, neg_neg] at this ⊢
    exact this
