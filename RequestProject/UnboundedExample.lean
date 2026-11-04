module

public import RequestProject.HeatSemigroup

/-!
# A genuinely unbounded example

The hypothesis `IsSemibounded H m σ R` used for unbounded Hamiltonians is satisfied by operators
that are not bounded. We give a general construction of `H` from a bounded self-adjoint
injective `R` (`H = R⁻¹ + σ` on the range of `R`), and a concrete instance on `ℓ²(ℕ)`:
`R = diag(1/(k+1))`, giving `H = diag(k)`, which is unbounded.
-/

@[expose] public section

open scoped InnerProductSpace

noncomputable section

namespace CftCheck

section General

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- The operator `H = R⁻¹ + σ`, defined on the range of an injective bounded operator `R`. -/
def pmapOfShiftInvert (R : E →L[ℂ] E) (hinj : Function.Injective R) (σ : ℝ) : E →ₗ.[ℂ] E where
  domain := LinearMap.range (R : E →ₗ[ℂ] E)
  toFun := ((LinearMap.id : E →ₗ[ℂ] E) + (σ : ℂ) • (R : E →ₗ[ℂ] E)) ∘ₗ
    (LinearEquiv.ofInjective (R : E →ₗ[ℂ] E) hinj).symm.toLinearMap

omit [CompleteSpace E] in
theorem pmapOfShiftInvert_apply (R : E →L[ℂ] E) (hinj : Function.Injective R) (σ : ℝ) (y : E)
    (hy : R y ∈ (pmapOfShiftInvert R hinj σ).domain) :
    pmapOfShiftInvert R hinj σ ⟨R y, hy⟩ = y + (σ : ℂ) • R y := by
  have : (LinearEquiv.ofInjective (R : E →ₗ[ℂ] E) hinj).symm ⟨R y, hy⟩ = y :=
    (LinearEquiv.ofInjective (R : E →ₗ[ℂ] E) hinj).symm_apply_eq.mpr rfl
  simp only [pmapOfShiftInvert, LinearPMap.mk_apply, LinearMap.coe_comp, Function.comp_apply,
    LinearEquiv.coe_coe]
  erw [this]
  rfl

omit [CompleteSpace E] in
theorem mem_domain_pmapOfShiftInvert (R : E →L[ℂ] E) (hinj : Function.Injective R) (σ : ℝ)
    (y : E) : R y ∈ (pmapOfShiftInvert R hinj σ).domain := ⟨y, rfl⟩

/-- `H = R⁻¹ + σ` is semibounded with shift-invert operator `R`, provided `R` is self-adjoint,
injective and satisfies `(m - σ)‖Ry‖² ≤ Re⟪Ry, y⟫`. -/
theorem isSemibounded_pmapOfShiftInvert (R : E →L[ℂ] E) (hR : IsSelfAdjoint R)
    (hinj : Function.Injective R) {m σ : ℝ} (hσ : σ < m)
    (hpos : ∀ y : E, (m - σ) * ‖R y‖ ^ 2 ≤ RCLike.re ⟪R y, y⟫_ℂ) :
    IsSemibounded (pmapOfShiftInvert R hinj σ) m σ R := by
  have hsym : ∀ a b : E, ⟪R a, b⟫_ℂ = ⟪a, R b⟫_ℂ := fun a b => by
    rw [← ContinuousLinearMap.adjoint_inner_right, hR.adjoint_eq]
  have hdom : ∀ x : (pmapOfShiftInvert R hinj σ).domain, ∃ a : E, (x : E) = R a := by
    rintro ⟨x, a, rfl⟩; exact ⟨a, rfl⟩
  have happ : ∀ x : (pmapOfShiftInvert R hinj σ).domain, ∀ a : E, (x : E) = R a →
      pmapOfShiftInvert R hinj σ x = a + (σ : ℂ) • R a := by
    intro x a hxa
    have : x = ⟨R a, mem_domain_pmapOfShiftInvert R hinj σ a⟩ := Subtype.ext hxa
    rw [this, pmapOfShiftInvert_apply]
  refine ⟨fun x y => ?_, fun x => ?_, hσ, ⟨mem_domain_pmapOfShiftInvert R hinj σ, fun x => ?_,
    fun y => ?_⟩⟩
  · obtain ⟨a, ha⟩ := hdom x
    obtain ⟨b, hb⟩ := hdom y
    rw [happ x a ha, happ y b hb, ha, hb, inner_add_left, inner_add_right, inner_smul_left,
      inner_smul_right, Complex.conj_ofReal, hsym a b]
  · obtain ⟨a, ha⟩ := hdom x
    rw [happ x a ha, ha, inner_add_right, inner_smul_right, inner_self_eq_norm_sq_to_K, map_add]
    have h1 := hpos a
    have h2 : RCLike.re ((σ : ℂ) * ((‖R a‖ : ℂ) ^ 2)) = σ * ‖R a‖ ^ 2 := by
      simp only [RCLike.re_to_complex]
      rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
    erw [h2]
    linarith
  · rw [pmapOfShiftInvert_apply]; abel
  · obtain ⟨a, ha⟩ := hdom y
    rw [happ y a ha, ha, add_sub_cancel_right]

end General

/-! ### The concrete example on `ℓ²(ℕ)` -/

/-- The Hilbert space `ℓ²(ℕ)`. -/
abbrev L2 := lp (fun _ : ℕ => ℂ) 2

theorem memℓp_diag (x : L2) : Memℓp (fun k : ℕ => x k / ((k : ℂ) + 1)) 2 := by
  refine Memℓp.mono' x.2 (fun k => ?_)
  rw [norm_div]
  have : 1 ≤ ‖(k : ℂ) + 1‖ := by
    rw [show (k : ℂ) + 1 = ((k + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    exact_mod_cast Nat.succ_pos k
  exact div_le_self (norm_nonneg _) this

/-- The diagonal operator `diag(1/(k+1))` on `ℓ²(ℕ)`, as a linear map. -/
def diagLin : L2 →ₗ[ℂ] L2 where
  toFun x := ⟨fun k => x k / ((k : ℂ) + 1), memℓp_diag x⟩
  map_add' x y := by
    ext k
    change (x k + y k) / ((k : ℂ) + 1) = x k / ((k : ℂ) + 1) + y k / ((k : ℂ) + 1)
    rw [add_div]
  map_smul' c x := by
    ext k
    change (c * x k) / ((k : ℂ) + 1) = c * (x k / ((k : ℂ) + 1))
    rw [mul_div_assoc]

theorem diagLin_apply (x : L2) (k : ℕ) : (diagLin x : ℕ → ℂ) k = x k / ((k : ℂ) + 1) := rfl

theorem norm_diagLin_le (x : L2) : ‖diagLin x‖ ≤ 1 * ‖x‖ := by
  rw [one_mul]
  have h2 : (0 : ℝ) < (2 : ENNReal).toReal := by norm_num
  refine lp.norm_le_of_tsum_le h2 (norm_nonneg x) ?_
  rw [lp.norm_rpow_eq_tsum h2]
  refine Summable.tsum_le_tsum (fun k => ?_) ((diagLin x).2.summable h2) (x.2.summable h2)
  rw [diagLin_apply, norm_div]
  have : 1 ≤ ‖(k : ℂ) + 1‖ := by
    rw [show (k : ℂ) + 1 = ((k + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    exact_mod_cast Nat.succ_pos k
  gcongr
  exact div_le_self (norm_nonneg _) this

/-- The bounded operator `R = diag(1/(k+1))` on `ℓ²(ℕ)`. -/
def diagR : L2 →L[ℂ] L2 := diagLin.mkContinuous 1 norm_diagLin_le

theorem diagR_apply (x : L2) (k : ℕ) : (diagR x : ℕ → ℂ) k = x k / ((k : ℂ) + 1) := rfl

theorem natCast_add_one_ne_zero (k : ℕ) : (k : ℂ) + 1 ≠ 0 := by
  rw [show (k : ℂ) + 1 = ((k + 1 : ℕ) : ℂ) by push_cast; ring]
  exact_mod_cast Nat.succ_ne_zero k

theorem diagR_injective : Function.Injective diagR := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  ext k
  have := congrArg (fun y : L2 => (y : ℕ → ℂ) k) hx
  simp only [diagR_apply, lp.coeFn_zero, Pi.zero_apply] at this
  simp only [lp.coeFn_zero, Pi.zero_apply]
  rw [div_eq_zero_iff] at this
  rcases this with h | h
  · exact h
  · exact absurd h (natCast_add_one_ne_zero k)

theorem diagR_isSelfAdjoint : IsSelfAdjoint diagR := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  simp only [ContinuousLinearMap.coe_coe]
  rw [lp.inner_eq_tsum, lp.inner_eq_tsum]
  refine tsum_congr (fun k => ?_)
  rw [diagR_apply, diagR_apply]
  have hc : (starRingEnd ℂ) ((k : ℂ) + 1) = (k : ℂ) + 1 := by
    rw [map_add, map_natCast, map_one]
  simp only [inner, map_div₀, hc, Complex.star_def]
  ring

theorem diagR_pos (y : L2) : (0 - (-1 : ℝ)) * ‖diagR y‖ ^ 2 ≤ RCLike.re ⟪diagR y, y⟫_ℂ := by
  rw [zero_sub, neg_neg, one_mul, ← inner_self_eq_norm_sq (𝕜 := ℂ), ← sub_nonneg, ← map_sub,
    ← inner_sub_right, lp.inner_eq_tsum]
  have hterm : ∀ k : ℕ, ⟪(diagR y : ℕ → ℂ) k, ((y - diagR y : L2) : ℕ → ℂ) k⟫_ℂ
      = ((‖y k‖ ^ 2 * (k / ((k + 1) ^ 2)) : ℝ) : ℂ) := by
    intro k
    simp only [lp.coeFn_sub, Pi.sub_apply, diagR_apply]
    have hk := natCast_add_one_ne_zero k
    have hc : (starRingEnd ℂ) ((k : ℂ) + 1) = (k : ℂ) + 1 := by
      rw [map_add, map_natCast, map_one]
    simp only [inner, Complex.star_def, map_div₀, hc]
    have hyc : y k * (starRingEnd ℂ) (y k) = ((‖y k‖ ^ 2 : ℝ) : ℂ) := by
      rw [Complex.mul_conj']; push_cast; rfl
    calc (y k - y k / ((k : ℂ) + 1)) * ((starRingEnd ℂ) (y k) / ((k : ℂ) + 1))
        = (y k * (starRingEnd ℂ) (y k)) * ((k : ℂ) / ((k : ℂ) + 1) ^ 2) := by
          field_simp; ring
      _ = _ := by rw [hyc]; push_cast; ring
  simp_rw [hterm]
  rw [← Complex.ofReal_tsum, RCLike.re_to_complex, Complex.ofReal_re]
  exact tsum_nonneg (fun k => by positivity)

/-- The operator `H = diag(k)` on `ℓ²(ℕ)`, defined as `R⁻¹ - 1` on the range of
`R = diag(1/(k+1))`. -/
def diagH : L2 →ₗ.[ℂ] L2 := pmapOfShiftInvert diagR diagR_injective (-1)

/-- `H = diag(k)` is semibounded (`H ≥ 0`) with shift-invert operator `diag(1/(k+1))` at
`σ = -1`. So it satisfies the hypotheses of the results on `exp(-τH)`. -/
theorem diagH_isSemibounded : IsSemibounded diagH 0 (-1) diagR :=
  isSemibounded_pmapOfShiftInvert diagR diagR_isSelfAdjoint diagR_injective (by norm_num)
    diagR_pos

/-- **`H = diag(k)` is unbounded:** no constant `C` satisfies `‖Hx‖ ≤ C‖x‖` on its domain. -/
theorem diagH_unbounded (C : ℝ) : ∃ x : diagH.domain, C * ‖(x : L2)‖ < ‖diagH x‖ := by
  obtain ⟨k, hk⟩ := exists_nat_gt C
  let e : L2 := lp.single 2 k 1
  have hRe : diagR e = lp.single 2 k (1 / ((k : ℂ) + 1)) := by
    ext j
    rw [diagR_apply]
    by_cases hj : j = k
    · subst hj; simp [e]
    · simp [e, lp.single_apply, hj]
  have hHx := pmapOfShiftInvert_apply diagR diagR_injective (-1) e
    (mem_domain_pmapOfShiftInvert _ _ _ e)
  refine ⟨⟨diagR e, mem_domain_pmapOfShiftInvert _ _ _ e⟩, ?_⟩
  change C * ‖diagR e‖ < ‖pmapOfShiftInvert diagR diagR_injective (-1)
    ⟨diagR e, mem_domain_pmapOfShiftInvert _ _ _ e⟩‖
  rw [hHx, hRe]
  have hsum : e + ((-1 : ℝ) : ℂ) • lp.single 2 k (1 / ((k : ℂ) + 1))
      = lp.single 2 k ((k : ℂ) / ((k : ℂ) + 1)) := by
    ext j
    by_cases hj : j = k
    · subst hj
      simp only [e, lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply, lp.single_apply_self,
        smul_eq_mul]
      have := natCast_add_one_ne_zero j
      field_simp
      push_cast; ring
    · simp [e, lp.single_apply, hj]
  rw [hsum, lp.norm_single (by norm_num), lp.norm_single (by norm_num), norm_div, norm_div,
    norm_one, Complex.norm_natCast]
  have hk1 : ‖(k : ℂ) + 1‖ = (k : ℝ) + 1 := by
    rw [show (k : ℂ) + 1 = ((k + 1 : ℕ) : ℂ) by push_cast; ring, Complex.norm_natCast]
    push_cast; ring
  rw [hk1]
  have hpos : (0 : ℝ) < k + 1 := by positivity
  rw [mul_one_div, div_lt_div_iff_of_pos_right hpos]
  exact hk

/-- For the unbounded `H = diag(k)`, `τ ↦ exp(-τH) x` solves `dψ/dτ = -Hψ` for every `x` in
the domain, and every solution is of this form. -/
theorem diagH_heat_exists :
    (∀ x : diagH.domain, IsHeatSolution diagH (fun τ => heatSG (-1) diagR τ x)) ∧
      ∀ ψ : ℝ → L2, IsHeatSolution diagH ψ → ∀ τ, 0 ≤ τ → ψ τ = heatSG (-1) diagR τ (ψ 0) :=
  ⟨heatSG_isHeatSolution diagH_isSemibounded,
    fun _ hψ _ hτ => hψ.eq_heatSG diagH_isSemibounded hτ⟩

end CftCheck
