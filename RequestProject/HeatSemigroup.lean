module

public import RequestProject.Unbounded

/-!
# The Euclidean transfer operators `exp(-τH)` of an unbounded Hamiltonian

`IsSemibounded H m σ R`: `H` is a symmetric operator on its domain, bounded below by `m`, and
`R = (H - σ)⁻¹` is its bounded shift-invert (SIRK) operator at a shift `σ < m`.

Since `H = σ + R⁻¹`, the transfer operator is defined through the continuous functional calculus
of the bounded self-adjoint `R`: `heatSG σ R τ = e^{-τσ} f_τ(R)` with `f_τ(r) = e^{-τ/r}`. We
prove that it is a strongly continuous semigroup of self-adjoint operators with generator `-H`,
that `τ ↦ exp(-τH) x` solves `dψ/dτ = -Hψ` (existence), that every solution is of this form
(uniqueness, by an energy estimate), and that `exp(-τH)` depends only on `H`.
-/

@[expose] public section

open scoped InnerProductSpace

noncomputable section

namespace CftCheck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- `H` is a symmetric operator bounded below by `m`, and `R` is its shift-invert operator
`(H - σ)⁻¹` at a real shift `σ < m`. -/
structure IsSemibounded (H : E →ₗ.[ℂ] E) (m σ : ℝ) (R : E →L[ℂ] E) : Prop where
  symm : ∀ x y : H.domain, ⟪H x, (y : E)⟫_ℂ = ⟪(x : E), H y⟫_ℂ
  lower : ∀ x : H.domain, m * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪(x : E), H x⟫_ℂ
  shift_lt : σ < m
  inv : IsShiftInvert H (σ : ℂ) R

namespace IsSemibounded

variable {H : E →ₗ.[ℂ] E} {m σ : ℝ} {R : E →L[ℂ] E}

theorem isSelfAdjoint_R (hH : IsSemibounded H m σ R) : IsSelfAdjoint R := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric]
  intro x y
  simp only [ContinuousLinearMap.coe_coe]
  have hx := hH.inv.right_inv x
  have hy := hH.inv.right_inv y
  have hs := hH.symm ⟨R x, hH.inv.mem_domain x⟩ ⟨R y, hH.inv.mem_domain y⟩
  simp only at hs
  conv_lhs => rw [← hy]
  conv_rhs => rw [← hx]
  rw [inner_sub_right, inner_sub_left, hs, inner_smul_right, inner_smul_left,
    Complex.conj_ofReal]

omit [CompleteSpace E] in
theorem lower_R (hH : IsSemibounded H m σ R) (x : E) :
    (m - σ) * ‖R x‖ ^ 2 ≤ RCLike.re ⟪R x, x⟫_ℂ := by
  have hx := hH.inv.right_inv x
  have hl := hH.lower ⟨R x, hH.inv.mem_domain x⟩
  simp only at hl
  have key : ⟪R x, x⟫_ℂ = ⟪R x, H ⟨R x, hH.inv.mem_domain x⟩ - (σ : ℂ) • R x⟫_ℂ := by
    rw [hx]
  rw [key, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, map_sub]
  simp only [RCLike.re_to_complex] at hl ⊢
  have : ((σ : ℂ) * ((‖R x‖ : ℂ) ^ 2)).re = σ * ‖R x‖ ^ 2 := by
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  erw [this]; nlinarith

omit [CompleteSpace E] in
theorem norm_R_le (hH : IsSemibounded H m σ R) : ‖R‖ ≤ (m - σ)⁻¹ := by
  have hpos : 0 < m - σ := sub_pos.mpr hH.shift_lt
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) (fun x => ?_)
  have h1 := hH.lower_R x
  have h2 : RCLike.re ⟪R x, x⟫_ℂ ≤ ‖R x‖ * ‖x‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  rw [inv_mul_eq_div, le_div_iff₀ hpos]
  rcases eq_or_lt_of_le (norm_nonneg (R x)) with h | h
  · rw [← h, zero_mul]; exact norm_nonneg _
  · nlinarith

theorem spectrum_R_subset (hH : IsSemibounded H m σ R) :
    spectrum ℝ R ⊆ Set.Icc 0 (m - σ)⁻¹ := by
  intro r hr
  have hpos : 0 < m - σ := sub_pos.mpr hH.shift_lt
  have hnn : 0 ≤ R := by
    rw [ContinuousLinearMap.nonneg_iff_isPositive, ContinuousLinearMap.isPositive_def']
    refine ⟨hH.isSelfAdjoint_R, fun x => ?_⟩
    have := hH.lower_R x
    simp only [ContinuousLinearMap.reApplyInnerSelf]
    nlinarith [sq_nonneg ‖R x‖]
  refine ⟨spectrum_nonneg_of_nonneg hnn hr, ?_⟩
  have h1 := IsometricContinuousFunctionalCalculus.norm_spectrum_le (𝕜 := ℝ) R hr
    hH.isSelfAdjoint_R
  have h2 := hH.norm_R_le
  have : r ≤ ‖r‖ := le_abs_self r
  linarith

omit [CompleteSpace E] in
theorem R_injective (hH : IsSemibounded H m σ R) : Function.Injective R := by
  rw [injective_iff_map_eq_zero]
  intro x hx
  have h := hH.inv.right_inv x
  have h0 : (⟨R x, hH.inv.mem_domain x⟩ : H.domain) = 0 := by ext; simpa using hx
  rw [h0, LinearPMap.map_zero, hx, smul_zero, sub_zero] at h
  exact h.symm

theorem denseRange_R (hH : IsSemibounded H m σ R) : DenseRange R := by
  have hsa := hH.isSelfAdjoint_R
  have hK : (LinearMap.range (R : E →ₗ[ℂ] E))ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro y hy
    have h1 : ∀ x, ⟪R x, y⟫_ℂ = 0 := fun x =>
      (Submodule.mem_orthogonal' _ _).mp hy _ ⟨x, rfl⟩ |> fun h => by
        rw [← inner_conj_symm]; simp only [ContinuousLinearMap.coe_coe] at h; rw [h, map_zero]
    have h2 : R y = 0 := by
      have := h1 (R y)
      rw [← ContinuousLinearMap.adjoint_inner_right, hsa.adjoint_eq] at this
      exact inner_self_eq_zero.mp this
    exact hH.R_injective (by rw [h2, map_zero])
  have := (Submodule.topologicalClosure_eq_top_iff).mpr hK
  rw [← Submodule.dense_iff_topologicalClosure_eq_top] at this
  rw [DenseRange]
  convert this using 1
  ext; simp

end IsSemibounded

/-! ### The function `r ↦ exp(-τ/r)` -/

/-- `heatFun τ r = exp(-τ/r)` for `r > 0` and `0` otherwise. Applied to `R = (H - σ)⁻¹` it gives
`exp(-τ (H - σ))`, since `1/r = λ - σ` when `r = (λ - σ)⁻¹`. -/
def heatFun (τ r : ℝ) : ℝ := if 0 < r then Real.exp (-τ / r) else 0

theorem continuous_heatFun {τ : ℝ} (hτ : 0 < τ) : Continuous (heatFun τ) := by
  rw [continuous_iff_continuousAt]
  intro r
  rcases lt_trichotomy r 0 with hr | rfl | hr
  · have : heatFun τ =ᶠ[nhds r] fun _ => 0 := by
      filter_upwards [Iio_mem_nhds hr] with s hs
      simp [heatFun, not_lt.mpr (le_of_lt hs)]
    exact (continuousAt_congr this).mpr continuousAt_const
  · have h0 : heatFun τ 0 = 0 := by simp [heatFun]
    rw [continuousAt_iff_continuous_left_right, ← continuousWithinAt_Ioi_iff_Ici]
    simp only [ContinuousWithinAt, h0]
    constructor
    · have : heatFun τ =ᶠ[nhdsWithin 0 (Set.Iic 0)] fun _ => 0 := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        simp [heatFun, not_lt.mpr (Set.mem_Iic.mp hs)]
      exact (Filter.tendsto_congr' this).mpr tendsto_const_nhds
    · have : heatFun τ =ᶠ[nhdsWithin 0 (Set.Ioi 0)] fun s => Real.exp (-τ * s⁻¹) := by
        filter_upwards [self_mem_nhdsWithin] with s hs
        simp [heatFun, Set.mem_Ioi.mp hs, div_eq_mul_inv]
      refine (Filter.tendsto_congr' this).mpr ?_
      refine Real.tendsto_exp_atBot.comp ?_
      exact Filter.Tendsto.const_mul_atTop_of_neg (by linarith) tendsto_inv_nhdsGT_zero
  · have : heatFun τ =ᶠ[nhds r] fun s => Real.exp (-τ / s) := by
      filter_upwards [Ioi_mem_nhds hr] with s hs
      simp [heatFun, Set.mem_Ioi.mp hs]
    refine (continuousAt_congr this).mpr ?_
    exact (continuousAt_const.div continuousAt_id hr.ne').rexp

theorem heatFun_add (s t r : ℝ) : heatFun (s + t) r = heatFun s r * heatFun t r := by
  unfold heatFun
  split_ifs with h
  · rw [← Real.exp_add]; congr 1; ring
  · simp

theorem heatFun_nonneg (τ r : ℝ) : 0 ≤ heatFun τ r := by
  unfold heatFun; split_ifs <;> positivity

theorem heatFun_le {τ a r : ℝ} (hτ : 0 ≤ τ) (ha : 0 < a) (hr : r ≤ a⁻¹) :
    heatFun τ r ≤ Real.exp (-(τ * a)) := by
  unfold heatFun
  split_ifs with h
  · apply Real.exp_le_exp.mpr
    have : a ≤ r⁻¹ := by
      rw [le_inv_comm₀ ha h]; exact hr
    rw [neg_div, neg_le_neg_iff, div_eq_mul_inv]
    exact mul_le_mul_of_nonneg_left this hτ
  · positivity

/-! ### The semigroup `exp(-τH)` -/

/-- The Euclidean transfer operator `exp(-τH)` of a semibounded `H`, built from its
shift-invert operator `R = (H - σ)⁻¹` by the continuous functional calculus of the bounded
self-adjoint `R`: `exp(-τH) = exp(-τσ) · heatFun τ (R)` for `τ > 0`, and `1` for `τ ≤ 0`. -/
def heatSG (σ : ℝ) (R : E →L[ℂ] E) (τ : ℝ) : E →L[ℂ] E :=
  if 0 < τ then Real.exp (-(τ * σ)) • cfc (heatFun τ) R else 1

variable {H : E →ₗ.[ℂ] E} {m σ : ℝ} {R : E →L[ℂ] E}

theorem heatSG_of_nonpos (σ : ℝ) (R : E →L[ℂ] E) {τ : ℝ} (hτ : τ ≤ 0) : heatSG σ R τ = 1 := by
  simp [heatSG, not_lt.mpr hτ]

@[simp] theorem heatSG_zero (σ : ℝ) (R : E →L[ℂ] E) : heatSG σ R 0 = 1 :=
  heatSG_of_nonpos σ R le_rfl

theorem heatSG_add {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) :
    heatSG σ R (s + t) = heatSG σ R s * heatSG σ R t := by
  rcases eq_or_lt_of_le hs with rfl | hs
  · simp
  rcases eq_or_lt_of_le ht with rfl | ht
  · simp
  have hst : 0 < s + t := by linarith
  simp only [heatSG, hs, ht, hst, ite_true]
  rw [smul_mul_smul_comm, ← Real.exp_add, ← cfc_mul (heatFun s) (heatFun t) R
    (continuous_heatFun hs).continuousOn (continuous_heatFun ht).continuousOn]
  congr 1
  · congr 1; ring
  · congr 1; funext r; exact heatFun_add s t r

theorem isSelfAdjoint_heatSG (σ : ℝ) (R : E →L[ℂ] E) (τ : ℝ) :
    IsSelfAdjoint (heatSG σ R τ) := by
  unfold heatSG
  split_ifs
  · exact IsSelfAdjoint.smul (IsSelfAdjoint.all _) (cfc_predicate (heatFun τ) R)
  · exact IsSelfAdjoint.one _

theorem norm_heatSG_le (hH : IsSemibounded H m σ R) {τ : ℝ} (hτ : 0 ≤ τ) :
    ‖heatSG σ R τ‖ ≤ Real.exp (-(τ * m)) := by
  rcases eq_or_lt_of_le hτ with rfl | hτ'
  · simp only [heatSG_zero, zero_mul, neg_zero, Real.exp_zero]
    exact ContinuousLinearMap.norm_id_le
  have hpos : 0 < m - σ := sub_pos.mpr hH.shift_lt
  simp only [heatSG, hτ', ite_true]
  rw [norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le]
  have hc : ‖cfc (heatFun τ) R‖ ≤ Real.exp (-(τ * (m - σ))) := by
    refine norm_cfc_le (Real.exp_pos _).le (fun r hr => ?_)
    have hr' := hH.spectrum_R_subset hr
    rw [Real.norm_of_nonneg (heatFun_nonneg _ _)]
    exact heatFun_le hτ hpos hr'.2
  calc Real.exp (-(τ * σ)) * ‖cfc (heatFun τ) R‖
      ≤ Real.exp (-(τ * σ)) * Real.exp (-(τ * (m - σ))) := by gcongr
    _ = Real.exp (-(τ * m)) := by rw [← Real.exp_add]; congr 1; ring

theorem heatSG_commute_R (hR : IsSelfAdjoint R) (τ : ℝ) : Commute (heatSG σ R τ) R := by
  unfold heatSG
  split_ifs
  · refine Commute.smul_left ?_ _
    have := cfc_commute_cfc (heatFun τ) id R
    rwa [cfc_id ℝ R hR] at this
  · exact Commute.one_left R

theorem heatSG_R_apply (hR : IsSelfAdjoint R) (τ : ℝ) (y : E) :
    heatSG σ R τ (R y) = R (heatSG σ R τ y) := by
  have := (heatSG_commute_R (σ := σ) hR τ).eq
  exact congrArg (fun T : E →L[ℂ] E => T y) this

/-- `exp(-τH)` maps the domain of `H` into itself. -/
theorem heatSG_mem_domain (hH : IsSemibounded H m σ R) (τ : ℝ) (x : H.domain) :
    heatSG σ R τ x ∈ H.domain := by
  have hx := hH.inv.left_inv x
  rw [← hx, heatSG_R_apply hH.isSelfAdjoint_R]
  exact hH.inv.mem_domain _

/-- `exp(-τH)` commutes with `H` on the domain of `H`. -/
theorem H_heatSG (hH : IsSemibounded H m σ R) (τ : ℝ) (x : H.domain) :
    H ⟨heatSG σ R τ x, heatSG_mem_domain hH τ x⟩ = heatSG σ R τ (H x) := by
  set z : E := H x - (σ : ℂ) • (x : E) with hz
  have hx : R z = x := hH.inv.left_inv x
  have e : (⟨heatSG σ R τ x, heatSG_mem_domain hH τ x⟩ : H.domain)
      = ⟨R (heatSG σ R τ z), hH.inv.mem_domain _⟩ := by
    ext; simp only; rw [← heatSG_R_apply hH.isSelfAdjoint_R, hx]
  rw [e]
  have h1 := hH.inv.right_inv (heatSG σ R τ z)
  rw [sub_eq_iff_eq_add] at h1
  rw [h1, ← heatSG_R_apply hH.isSelfAdjoint_R, hx, hz, map_sub, map_smul]
  abel

/-! ### Strong continuity and the generator -/

omit [CompleteSpace E] in
/-- Uniformly bounded operators that tend to `0` on the dense range of `R` tend to `0`
strongly. -/
theorem tendsto_apply_of_dense {ι : Type*} {l : Filter ι} (K : ι → E →L[ℂ] E) (C : ℝ)
    (hC : ∀ᶠ i in l, ‖K i‖ ≤ C) (hR : DenseRange R)
    (h : ∀ y, Filter.Tendsto (fun i => K i (R y)) l (nhds 0)) (x : E) :
    Filter.Tendsto (fun i => K i x) l (nhds 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hC1 : 0 < |C| + 1 := by positivity
  obtain ⟨y, hy⟩ : ∃ y, dist x (R y) < ε / 2 / (|C| + 1) :=
    hR.exists_dist_lt x (by positivity)
  have h2 := Metric.tendsto_nhds.mp (h y) (ε / 2) (by positivity)
  filter_upwards [hC, h2] with i hi hi2
  rw [dist_zero_right] at hi2 ⊢
  rw [dist_eq_norm] at hy
  have : K i x = K i (x - R y) + K i (R y) := by rw [map_sub]; abel
  rw [this]
  calc ‖K i (x - R y) + K i (R y)‖ ≤ ‖K i (x - R y)‖ + ‖K i (R y)‖ := norm_add_le _ _
    _ ≤ ‖K i‖ * ‖x - R y‖ + ‖K i (R y)‖ := by gcongr; exact (K i).le_opNorm _
    _ < (|C| + 1) * (ε / 2 / (|C| + 1)) + ε / 2 :=
        add_lt_add_of_le_of_lt (mul_le_mul (hi.trans ((le_abs_self C).trans (by linarith)))
          hy.le (norm_nonneg _) hC1.le) hi2
    _ = ε := by rw [mul_div_cancel₀ _ hC1.ne']; ring

theorem exp_neg_le_quad {v : ℝ} (hv : 0 ≤ v) : Real.exp (-v) ≤ 1 - v + v ^ 2 := by
  rcases le_or_gt v 1 with h1 | h1
  · have := Real.abs_exp_sub_one_sub_id_le (x := -v) (by rw [abs_neg, abs_of_nonneg hv]; exact h1)
    have := (abs_le.mp this).2
    nlinarith
  · have : Real.exp (-v) ≤ 1 := Real.exp_le_one_iff.mpr (by linarith)
    nlinarith

theorem heat_pt_aux {h r : ℝ} (hh : 0 < h) (hr : 0 < r) :
    r - h ≤ r * Real.exp (-h / r) ∧ r * Real.exp (-h / r) ≤ r ∧
      r ^ 2 * Real.exp (-h / r) ≤ r ^ 2 - h * r + h ^ 2 := by
  have hv : 0 ≤ h / r := by positivity
  have e1 : 1 - h / r ≤ Real.exp (-h / r) := by
    have := Real.add_one_le_exp (-h / r); rw [neg_div] at this ⊢; linarith
  have e2 : Real.exp (-h / r) ≤ 1 := Real.exp_le_one_iff.mpr (by
    rw [neg_div]; linarith)
  have e3 := exp_neg_le_quad hv
  rw [← neg_div] at e3
  refine ⟨?_, ?_, ?_⟩
  · have := mul_le_mul_of_nonneg_left e1 hr.le
    rw [mul_sub, mul_one, mul_div_cancel₀ _ hr.ne'] at this; exact this
  · nlinarith
  · have := mul_le_mul_of_nonneg_left e3 (sq_nonneg r)
    have h4 : r ^ 2 * (1 - h / r + (h / r) ^ 2) = r ^ 2 - h * r + h ^ 2 := by
      field_simp
    linarith

theorem heat_pt1 {h r : ℝ} (hh : 0 < h) (hr : 0 ≤ r) : |heatFun h r * r - r| ≤ h := by
  rcases eq_or_lt_of_le hr with rfl | hr
  · simp [hh.le]
  obtain ⟨a1, a2, -⟩ := heat_pt_aux hh hr
  simp only [heatFun, hr, ite_true]
  rw [abs_le]; constructor <;> nlinarith

theorem heat_pt2 {h r : ℝ} (hh : 0 < h) (hr : 0 ≤ r) :
    |h⁻¹ * (heatFun h r * r - r) + 1| ≤ 1 := by
  rcases eq_or_lt_of_le hr with rfl | hr
  · simp
  obtain ⟨a1, a2, -⟩ := heat_pt_aux hh hr
  simp only [heatFun, hr, ite_true]
  have hi : 0 < h⁻¹ := inv_pos.mpr hh
  have k : h⁻¹ * h = 1 := inv_mul_cancel₀ hh.ne'
  rw [abs_le]; constructor <;> nlinarith

theorem heat_pt3 {h r : ℝ} (hh : 0 < h) (hr : 0 ≤ r) :
    |(h⁻¹ * (heatFun h r * r - r) + 1) * r| ≤ h := by
  rcases eq_or_lt_of_le hr with rfl | hr
  · simp [hh.le]
  obtain ⟨a1, a2, a3⟩ := heat_pt_aux hh hr
  simp only [heatFun, hr, ite_true]
  have hi : 0 < h⁻¹ := inv_pos.mpr hh
  have k : h⁻¹ * h = 1 := inv_mul_cancel₀ hh.ne'
  have eq : (h⁻¹ * (Real.exp (-h / r) * r - r) + 1) * r
      = h⁻¹ * (r ^ 2 * Real.exp (-h / r) - r ^ 2 + h * r) := by
    rw [mul_add h⁻¹ _ (h * r), ← mul_assoc, k]; ring
  rw [eq, abs_le]
  constructor
  · have : 0 ≤ r ^ 2 * Real.exp (-h / r) - r ^ 2 + h * r := by nlinarith
    nlinarith
  · have : r ^ 2 * Real.exp (-h / r) - r ^ 2 + h * r ≤ h ^ 2 := by linarith
    calc h⁻¹ * (r ^ 2 * Real.exp (-h / r) - r ^ 2 + h * r) ≤ h⁻¹ * h ^ 2 := by gcongr
      _ = h := by field_simp

theorem norm_cfc_le_of_Icc (hH : IsSemibounded H m σ R) {f : ℝ → ℝ} {c : ℝ} (hc : 0 ≤ c)
    (hf : ∀ r, 0 ≤ r → |f r| ≤ c) : ‖cfc f R‖ ≤ c :=
  norm_cfc_le hc (fun r hr => by
    rw [Real.norm_eq_abs]; exact hf r (hH.spectrum_R_subset hr).1)

theorem cfc_heat_mul_R_sub (hR : IsSelfAdjoint R) {h : ℝ} (hh : 0 < h) :
    cfc (heatFun h) R * R - R = cfc (fun r => heatFun h r * r - r) R := by
  have hc := (continuous_heatFun hh).continuousOn (s := spectrum ℝ R)
  rw [cfc_sub (fun r => heatFun h r * r) (fun r => r) R
    ((continuous_heatFun hh).mul continuous_id).continuousOn continuous_id.continuousOn,
    cfc_mul (heatFun h) (fun r => r) R hc continuous_id.continuousOn, cfc_id' ℝ R hR]

theorem genOp_eq (hR : IsSelfAdjoint R) {h : ℝ} (hh : 0 < h) :
    h⁻¹ • (cfc (heatFun h) R * R - R) + 1
      = cfc (fun r => h⁻¹ * (heatFun h r * r - r) + 1) R := by
  have hc : Continuous (fun r => heatFun h r * r - r) :=
    ((continuous_heatFun hh).mul continuous_id).sub continuous_id
  rw [cfc_add (a := R) (fun r => h⁻¹ * (heatFun h r * r - r)) (fun _ => (1 : ℝ))
    (continuous_const.mul hc).continuousOn continuousOn_const, cfc_const_one ℝ R hR,
    cfc_const_mul _ _ R hc.continuousOn, cfc_heat_mul_R_sub hR hh]

theorem genOp_mul_R_eq (hR : IsSelfAdjoint R) {h : ℝ} (hh : 0 < h) :
    (h⁻¹ • (cfc (heatFun h) R * R - R) + 1) * R
      = cfc (fun r => (h⁻¹ * (heatFun h r * r - r) + 1) * r) R := by
  have hc : Continuous (fun r => h⁻¹ * (heatFun h r * r - r) + 1) :=
    (continuous_const.mul (((continuous_heatFun hh).mul continuous_id).sub continuous_id)).add
      continuous_const
  rw [genOp_eq hR hh, cfc_mul _ (fun r => r) R hc.continuousOn continuous_id.continuousOn,
    cfc_id' ℝ R hR]

/-- Strong continuity at `0` of `heatFun h (R)`. -/
theorem tendsto_cfc_heat (hH : IsSemibounded H m σ R) (x : E) :
    Filter.Tendsto (fun h => cfc (heatFun h) R x) (nhdsWithin 0 (Set.Ioi 0)) (nhds x) := by
  have hR := hH.isSelfAdjoint_R
  have hpos : 0 < m - σ := sub_pos.mpr hH.shift_lt
  have key := tendsto_apply_of_dense (l := nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (fun h => cfc (heatFun h) R - 1) 2 ?_ hH.denseRange_R ?_ x
  · have := key.add (tendsto_const_nhds (x := x))
    simpa using this
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hh : 0 < h := hh
    calc ‖cfc (heatFun h) R - 1‖ ≤ ‖cfc (heatFun h) R‖ + ‖(1 : E →L[ℂ] E)‖ := norm_sub_le _ _
      _ ≤ 1 + 1 := by
        gcongr
        · refine norm_cfc_le one_pos.le (fun r hr => ?_)
          rw [Real.norm_of_nonneg (heatFun_nonneg _ _)]
          refine (heatFun_le hh.le hpos (hH.spectrum_R_subset hr).2).trans ?_
          rw [Real.exp_le_one_iff]; nlinarith
        · exact ContinuousLinearMap.norm_id_le
      _ = 2 := by norm_num
  · intro y
    have hlim : Filter.Tendsto (fun h : ℝ => h * ‖y‖) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have : Filter.Tendsto (fun h : ℝ => h * ‖y‖) (nhds 0) (nhds (0 * ‖y‖)) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh : 0 < h := hh
    have e : (cfc (heatFun h) R - 1) (R y) = (cfc (heatFun h) R * R - R) y := by simp
    rw [e, cfc_heat_mul_R_sub hR hh]
    refine ((cfc _ R).le_opNorm y).trans ?_
    gcongr
    exact norm_cfc_le_of_Icc hH hh.le (fun r hr => heat_pt1 hh hr)

/-- The generator of `heatFun h (R)` on the range of `R`:
`(heatFun h (R) (R y) - R y)/h → -y` as `h → 0⁺`. -/
theorem tendsto_cfc_heat_gen (hH : IsSemibounded H m σ R) (y : E) :
    Filter.Tendsto (fun h => h⁻¹ • (cfc (heatFun h) R (R y) - R y)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-y)) := by
  have hR := hH.isSelfAdjoint_R
  have key := tendsto_apply_of_dense (l := nhdsWithin (0 : ℝ) (Set.Ioi 0))
    (fun h => h⁻¹ • (cfc (heatFun h) R * R - R) + 1) 1 ?_ hH.denseRange_R ?_ y
  · have := key.sub (tendsto_const_nhds (x := y))
    simp only [zero_sub] at this
    refine this.congr (fun h => ?_)
    simp
  · filter_upwards [self_mem_nhdsWithin] with h hh
    have hh : 0 < h := hh
    rw [genOp_eq hR hh]
    exact norm_cfc_le_of_Icc hH one_pos.le (fun r hr => heat_pt2 hh hr)
  · intro z
    have hlim : Filter.Tendsto (fun h : ℝ => h * ‖z‖) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have : Filter.Tendsto (fun h : ℝ => h * ‖z‖) (nhds 0) (nhds (0 * ‖z‖)) :=
        (continuous_id.mul continuous_const).tendsto 0
      rw [zero_mul] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    refine squeeze_zero_norm' ?_ hlim
    filter_upwards [self_mem_nhdsWithin] with h hh
    have hh : 0 < h := hh
    have e : (h⁻¹ • (cfc (heatFun h) R * R - R) + 1) (R z)
        = ((h⁻¹ • (cfc (heatFun h) R * R - R) + 1) * R) z := rfl
    rw [e, genOp_mul_R_eq hR hh]
    refine ((cfc _ R).le_opNorm z).trans ?_
    gcongr
    exact norm_cfc_le_of_Icc hH hh.le (fun r hr => heat_pt3 hh hr)

theorem heatSG_of_pos (σ : ℝ) (R : E →L[ℂ] E) {τ : ℝ} (hτ : 0 < τ) :
    heatSG σ R τ = Real.exp (-(τ * σ)) • cfc (heatFun τ) R := by
  simp [heatSG, hτ]

theorem tendsto_exp_shift (σ : ℝ) :
    Filter.Tendsto (fun h : ℝ => Real.exp (-(h * σ))) (nhdsWithin 0 (Set.Ioi 0)) (nhds 1) := by
  have : Continuous (fun h : ℝ => Real.exp (-(h * σ))) := by fun_prop
  have := this.tendsto 0
  simp only [zero_mul, neg_zero, Real.exp_zero] at this
  exact tendsto_nhdsWithin_of_tendsto_nhds this

theorem tendsto_exp_shift_slope (σ : ℝ) :
    Filter.Tendsto (fun h : ℝ => h⁻¹ * (Real.exp (-(h * σ)) - 1)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-σ)) := by
  have hd : HasDerivAt (fun h : ℝ => Real.exp (-(h * σ))) (-σ) 0 := by
    have := ((hasDerivAt_id (0 : ℝ)).mul_const σ).neg.exp
    simpa using this
  have := (hasDerivAt_iff_tendsto_slope.mp hd).mono_left
    (nhdsWithin_mono _ (fun x (hx : 0 < x) => (ne_of_gt hx)))
  refine this.congr (fun h => ?_)
  simp [slope_def_field, div_eq_inv_mul]

/-- **Strong continuity at `0`:** `exp(-hH) x → x` as `h → 0⁺`, for every `x`. -/
theorem tendsto_heatSG_zero (hH : IsSemibounded H m σ R) (x : E) :
    Filter.Tendsto (fun h => heatSG σ R h x) (nhdsWithin 0 (Set.Ioi 0)) (nhds x) := by
  have := (tendsto_exp_shift σ).smul (tendsto_cfc_heat hH x)
  rw [one_smul] at this
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  rw [heatSG_of_pos σ R hh]; rfl

/-- **The generator of `exp(-τH)` is `-H`:** for `x` in the domain of `H`,
`(exp(-hH) x - x)/h → -Hx` as `h → 0⁺`. -/
theorem tendsto_heatSG_gen (hH : IsSemibounded H m σ R) (x : H.domain) :
    Filter.Tendsto (fun h => h⁻¹ • (heatSG σ R h x - x)) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (-(H x))) := by
  set y : E := H x - (σ : ℂ) • (x : E) with hy
  have hx : R y = x := hH.inv.left_inv x
  have h1 := (tendsto_exp_shift σ).smul (tendsto_cfc_heat_gen hH y)
  have h2 := (tendsto_exp_shift_slope σ).smul (tendsto_const_nhds (x := (x : E)))
  have h3 := h1.add h2
  have hlim : (1 : ℝ) • -y + (-σ) • (x : E) = -(H x) := by
    rw [hy, one_smul, neg_smul, ← Complex.coe_smul]; abel
  rw [hlim, hx] at h3
  refine h3.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with h hh
  have hh : 0 < h := hh
  rw [heatSG_of_pos σ R hh]
  simp only [smul_apply]
  module

theorem heatSG_add_apply {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t)
    (x : E) : heatSG σ R (s + t) x = heatSG σ R s (heatSG σ R t x) := by
  rw [heatSG_add hs ht]; rfl

theorem norm_heatSG_le_of_le (hH : IsSemibounded H m σ R) {s T : ℝ} (hs : 0 ≤ s)
    (hsT : s ≤ T) : ‖heatSG σ R s‖ ≤ Real.exp (|m| * T) := by
  refine (norm_heatSG_le hH hs).trans (Real.exp_le_exp.mpr ?_)
  have : -(s * m) ≤ s * |m| := by
    rw [neg_le]; nlinarith [neg_abs_le m]
  nlinarith [abs_nonneg m]

/-- **Strong continuity:** `τ ↦ exp(-τH) x` is continuous on `[0, ∞)` for every `x`. -/
theorem continuousOn_heatSG (hH : IsSemibounded H m σ R) (x : E) :
    ContinuousOn (fun τ => heatSG σ R τ x) (Set.Ici 0) := by
  intro τ0 hτ0
  have hτ0 : 0 ≤ τ0 := hτ0
  rw [Metric.continuousWithinAt_iff]
  intro ε hε
  set C := Real.exp (|m| * (τ0 + 1)) with hCdef
  have hC : 0 < C := Real.exp_pos _
  obtain ⟨δ, hδ, hd⟩ := Metric.tendsto_nhdsWithin_nhds.mp (tendsto_heatSG_zero hH x) (ε / C)
    (by positivity)
  refine ⟨min δ 1, by positivity, fun {τ} hτ hdist => ?_⟩
  have hτ : 0 ≤ τ := hτ
  rw [Real.dist_eq] at hdist
  have hd1 : |τ - τ0| < δ := lt_of_lt_of_le hdist (min_le_left _ _)
  have hd2 : |τ - τ0| < 1 := lt_of_lt_of_le hdist (min_le_right _ _)
  rcases lt_trichotomy τ τ0 with hlt | rfl | hgt
  · have hh : 0 < τ0 - τ := by linarith
    have e : heatSG σ R τ0 x = heatSG σ R τ (heatSG σ R (τ0 - τ) x) := by
      rw [← heatSG_add_apply hτ hh.le, add_sub_cancel]
    have hd1' : τ0 - τ < δ := by rw [abs_sub_comm, abs_of_pos hh] at hd1; exact hd1
    have hdd := hd hh (by rwa [Real.dist_eq, sub_zero, abs_of_pos hh])
    rw [e, dist_eq_norm, ← map_sub]
    calc ‖heatSG σ R τ (x - heatSG σ R (τ0 - τ) x)‖
        ≤ ‖heatSG σ R τ‖ * ‖x - heatSG σ R (τ0 - τ) x‖ := (heatSG σ R τ).le_opNorm _
      _ ≤ C * ‖x - heatSG σ R (τ0 - τ) x‖ := by
          gcongr; exact norm_heatSG_le_of_le hH hτ (by linarith)
      _ < C * (ε / C) := by
          gcongr; rw [norm_sub_rev, ← dist_eq_norm]; exact hdd
      _ = ε := by field_simp
  · simpa using hε
  · have hh : 0 < τ - τ0 := by linarith
    have e : heatSG σ R τ x = heatSG σ R τ0 (heatSG σ R (τ - τ0) x) := by
      rw [← heatSG_add_apply hτ0 hh.le, add_sub_cancel]
    have hd1' : τ - τ0 < δ := by rw [abs_of_pos hh] at hd1; exact hd1
    have hdd := hd hh (by rwa [Real.dist_eq, sub_zero, abs_of_pos hh])
    rw [e, dist_eq_norm, ← map_sub]
    calc ‖heatSG σ R τ0 (heatSG σ R (τ - τ0) x - x)‖
        ≤ ‖heatSG σ R τ0‖ * ‖heatSG σ R (τ - τ0) x - x‖ := (heatSG σ R τ0).le_opNorm _
      _ ≤ C * ‖heatSG σ R (τ - τ0) x - x‖ := by
          gcongr; exact norm_heatSG_le_of_le hH hτ0 (by linarith)
      _ < C * (ε / C) := by
          gcongr; rw [← dist_eq_norm]; exact hdd
      _ = ε := by field_simp

/-- **Right derivative:** for `x` in the domain of `H`, `τ ↦ exp(-τH) x` has right derivative
`-H exp(-τH) x` at every `τ ≥ 0`. -/
theorem hasDerivWithinAt_heatSG (hH : IsSemibounded H m σ R) (x : H.domain) {τ0 : ℝ}
    (hτ0 : 0 ≤ τ0) :
    HasDerivWithinAt (fun τ => heatSG σ R τ x)
      (-(H ⟨heatSG σ R τ0 x, heatSG_mem_domain hH τ0 x⟩)) (Set.Ici τ0) τ0 := by
  rw [← hasDerivWithinAt_Ioi_iff_Ici, hasDerivWithinAt_iff_tendsto_slope,
    Set.sdiff_singleton_eq_self (fun h => lt_irrefl _ (Set.mem_Ioi.mp h)), H_heatSG hH, ← map_neg]
  have hcomp : Filter.Tendsto (fun τ => τ - τ0) (nhdsWithin τ0 (Set.Ioi τ0))
      (nhdsWithin 0 (Set.Ioi 0)) := by
    rw [tendsto_nhdsWithin_iff]
    constructor
    · have : Filter.Tendsto (fun τ => τ - τ0) (nhds τ0) (nhds (τ0 - τ0)) :=
        (continuous_id.sub continuous_const).tendsto τ0
      rw [sub_self] at this
      exact tendsto_nhdsWithin_of_tendsto_nhds this
    · filter_upwards [self_mem_nhdsWithin] with τ hτ
      exact sub_pos.mpr hτ
  have := ((heatSG σ R τ0).continuous.tendsto _).comp ((tendsto_heatSG_gen hH x).comp hcomp)
  refine this.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  have hτ : τ0 < τ := hτ
  have e : heatSG σ R τ x = heatSG σ R τ0 (heatSG σ R (τ - τ0) x) := by
    rw [← heatSG_add_apply hτ0 (by linarith), add_sub_cancel]
  simp only [Function.comp_apply, slope_def_module]
  rw [e, ContinuousLinearMap.map_smul_of_tower, map_sub]

/-! ### Existence and uniqueness for `dψ/dτ = -Hψ` -/

/-- `ψ` is a strong solution on `[0, ∞)` of the Euclidean evolution equation
`dψ/dτ = -Hψ`: `ψ τ` stays in the domain of `H`, `ψ` is continuous, and its right
derivative at every `τ ≥ 0` is `-H ψ τ`. -/
structure IsHeatSolution (H : E →ₗ.[ℂ] E) (ψ : ℝ → E) : Prop where
  mem : ∀ t, 0 ≤ t → ψ t ∈ H.domain
  cont : ContinuousOn ψ (Set.Ici 0)
  deriv : ∀ t (ht : 0 ≤ t), HasDerivWithinAt ψ (-(H ⟨ψ t, mem t ht⟩)) (Set.Ici t) t

/-- **Existence.** For `x` in the domain of `H`, `τ ↦ exp(-τH) x` solves `dψ/dτ = -Hψ`. -/
theorem heatSG_isHeatSolution (hH : IsSemibounded H m σ R) (x : H.domain) :
    IsHeatSolution H (fun τ => heatSG σ R τ x) where
  mem t _ := heatSG_mem_domain hH t x
  cont := continuousOn_heatSG hH x
  deriv _ ht := hasDerivWithinAt_heatSG hH x ht

omit [CompleteSpace E] in
/-- **Energy estimate.** If a solution satisfies `Re⟪ψ, Hψ⟫ ≥ c‖ψ‖²` along its trajectory,
then `‖ψ τ‖² ≤ ‖ψ 0‖² e^{-2cτ}`. -/
theorem IsHeatSolution.norm_sq_le {ψ : ℝ → E} (hψ : IsHeatSolution H ψ) (c : ℝ)
    (hc : ∀ t (ht : 0 ≤ t), c * ‖ψ t‖ ^ 2 ≤ RCLike.re ⟪ψ t, H ⟨ψ t, hψ.mem t ht⟩⟫_ℂ)
    {t : ℝ} (ht : 0 ≤ t) : ‖ψ t‖ ^ 2 ≤ ‖ψ 0‖ ^ 2 * Real.exp (-2 * c * t) := by
  classical
  let f' : ℝ → ℝ := fun s =>
    if hs : 0 ≤ s then -2 * RCLike.re ⟪ψ s, H ⟨ψ s, hψ.mem s hs⟩⟫_ℂ else 0
  have hderiv : ∀ s (hs : 0 ≤ s), HasDerivWithinAt (fun u => ‖ψ u‖ ^ 2) (f' s) (Set.Ici s) s := by
    intro s hs
    have h1 := (hψ.deriv s hs).inner ℂ (hψ.deriv s hs)
    have h2 := Complex.reCLM.hasFDerivAt.comp_hasDerivWithinAt s h1
    refine (h2.congr_of_mem (fun u _ => ?_) (Set.mem_Ici.mpr le_rfl)).congr_deriv ?_
    · simp only [Function.comp_apply, Complex.reCLM_apply]
      rw [← RCLike.re_to_complex, inner_self_eq_norm_sq]
    · simp only [Complex.reCLM_apply, f', dite_eq_left hs, inner_neg_left, inner_neg_right,
        Complex.add_re, Complex.neg_re]
      rw [← RCLike.re_to_complex, ← RCLike.re_to_complex, ← inner_conj_symm (ψ s), RCLike.conj_re]
      ring
  have key := le_gronwallBound_of_liminf_deriv_right_le (f := fun u => ‖ψ u‖ ^ 2) (f' := f')
    (δ := ‖ψ 0‖ ^ 2) (K := -2 * c) (ε := 0) (a := 0) (b := t)
    ((hψ.cont.mono Set.Icc_subset_Ici_self).norm.pow 2) ?_ le_rfl ?_ t
    ⟨ht, le_rfl⟩
  · rwa [gronwallBound_ε0, sub_zero] at key
  · intro s hs r hr
    have hd := hderiv s hs.1
    rw [← hasDerivWithinAt_Ioi_iff_Ici, hasDerivWithinAt_iff_tendsto_slope,
      Set.sdiff_singleton_eq_self (fun h => lt_irrefl _ (Set.mem_Ioi.mp h))] at hd
    have := hd.eventually (gt_mem_nhds hr)
    refine this.frequently.mono (fun z hz => ?_)
    rwa [slope_def_field, div_eq_inv_mul] at hz
  · intro s hs
    have := hc s hs.1
    simp only [f', dite_eq_left hs.1]
    nlinarith

omit [CompleteSpace E] in
theorem IsHeatSolution.sub {ψ φ : ℝ → E} (hψ : IsHeatSolution H ψ) (hφ : IsHeatSolution H φ) :
    IsHeatSolution H (fun t => ψ t - φ t) where
  mem t ht := H.domain.sub_mem (hψ.mem t ht) (hφ.mem t ht)
  cont := hψ.cont.sub hφ.cont
  deriv t ht := by
    have := (hψ.deriv t ht).sub (hφ.deriv t ht)
    convert this using 1
    have e : (⟨ψ t - φ t, H.domain.sub_mem (hψ.mem t ht) (hφ.mem t ht)⟩ : H.domain)
        = ⟨ψ t, hψ.mem t ht⟩ - ⟨φ t, hφ.mem t ht⟩ := rfl
    rw [e, LinearPMap.map_sub]; abel

omit [CompleteSpace E] in
/-- **Uniqueness.** If `H` is bounded below (`Re⟪x, Hx⟫ ≥ m‖x‖²` on its domain), two solutions
of `dψ/dτ = -Hψ` with the same initial value agree for all `τ ≥ 0`. -/
theorem IsHeatSolution.unique (hlow : ∀ x : H.domain, m * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪(x : E), H x⟫_ℂ)
    {ψ φ : ℝ → E} (hψ : IsHeatSolution H ψ) (hφ : IsHeatSolution H φ) (h0 : ψ 0 = φ 0)
    {t : ℝ} (ht : 0 ≤ t) : ψ t = φ t := by
  have hd := hψ.sub hφ
  have := hd.norm_sq_le m (fun s hs => hlow ⟨_, _⟩) ht
  simp only [h0, sub_self, norm_zero, ne_eq, OfNat.ofNat_ne_zero, not_false_eq_true,
    zero_pow, zero_mul] at this
  have : ‖ψ t - φ t‖ = 0 := by nlinarith [norm_nonneg (ψ t - φ t)]
  exact sub_eq_zero.mp (norm_eq_zero.mp this)

/-- Every solution of `dψ/dτ = -Hψ` is given by the semigroup: `ψ τ = exp(-τH) ψ 0`. -/
theorem IsHeatSolution.eq_heatSG (hH : IsSemibounded H m σ R) {ψ : ℝ → E}
    (hψ : IsHeatSolution H ψ) {t : ℝ} (ht : 0 ≤ t) :
    ψ t = heatSG σ R t (ψ 0) := by
  have := IsHeatSolution.unique hH.lower hψ
    (heatSG_isHeatSolution hH ⟨ψ 0, hψ.mem 0 le_rfl⟩) (by simp) ht
  exact this

/-- **Eigenvectors.** If `Hx = λx` then `exp(-τH) x = e^{-τλ} x` for `τ ≥ 0`. -/
theorem heatSG_eigen (hH : IsSemibounded H m σ R) (x : H.domain) (l : ℝ)
    (hx : H x = (l : ℂ) • (x : E)) {τ : ℝ} (hτ : 0 ≤ τ) :
    heatSG σ R τ x = Real.exp (-(τ * l)) • (x : E) := by
  have hsol : IsHeatSolution H (fun t => Real.exp (-(t * l)) • (x : E)) := by
    refine ⟨fun t _ => H.domain.smul_of_tower_mem _ x.2, by fun_prop, fun t ht => ?_⟩
    have hd : HasDerivAt (fun t : ℝ => Real.exp (-(t * l))) (Real.exp (-(t * l)) * -l) t := by
      have := ((hasDerivAt_id t).mul_const l).neg.exp
      simpa using this
    refine (hd.smul_const (x : E)).hasDerivWithinAt.congr_deriv ?_
    have e : (⟨Real.exp (-(t * l)) • (x : E), H.domain.smul_of_tower_mem _ x.2⟩ : H.domain)
        = ((Real.exp (-(t * l)) : ℝ) : ℂ) • x := by
      ext; simp only [SetLike.val_smul]; exact (Complex.coe_smul _ _).symm
    rw [e, LinearPMap.map_smul, hx, smul_smul, ← Complex.ofReal_mul, Complex.coe_smul,
      ← neg_smul, mul_neg]
  have := (hsol.eq_heatSG hH hτ).symm
  simpa using this

/-- **The semigroup depends only on `H`**, not on the shift `σ` or the lower bound used to
build it. -/
theorem heatSG_unique {m' σ' : ℝ} {R' : E →L[ℂ] E} (hH : IsSemibounded H m σ R)
    (hH' : IsSemibounded H m' σ' R') {τ : ℝ} (hτ : 0 ≤ τ) :
    heatSG σ R τ = heatSG σ' R' τ := by
  have : (heatSG σ R τ : E → E) = heatSG σ' R' τ := by
    refine hH.denseRange_R.equalizer (heatSG σ R τ).continuous (heatSG σ' R' τ).continuous ?_
    funext y
    have := (heatSG_isHeatSolution hH' ⟨R y, hH.inv.mem_domain y⟩).eq_heatSG hH hτ
    simpa using this.symm
  exact ContinuousLinearMap.ext (congrFun this)

/-! ### Polynomial approximation inside the functional calculus -/

theorem norm_cfc_sub_aeval_le {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) {a b : ℝ}
    (hspec : spectrum ℝ A ⊆ Set.Icc a b) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b))
    {ε : ℝ} (hε : 0 < ε) (p : Polynomial ℝ) (hp : ∀ x ∈ Set.Icc a b, |p.eval x - f x| < ε) :
    ‖cfc f A - Polynomial.aeval A p‖ ≤ ε := by
  rw [← cfc_polynomial p A hA, ← cfc_sub (a := A) f (fun x => p.eval x) (hf.mono hspec)
    (p.continuous.continuousOn)]
  refine norm_cfc_le hε.le (fun x hx => ?_)
  rw [Real.norm_eq_abs, abs_sub_comm]
  exact (hp x (hspec hx)).le

theorem exists_poly_near_cfc {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) {a b : ℝ}
    (hspec : spectrum ℝ A ⊆ Set.Icc a b) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b))
    {ε : ℝ} (hε : 0 < ε) : ∃ p : Polynomial ℝ, ‖cfc f A - Polynomial.aeval A p‖ ≤ ε := by
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b f hf ε hε
  exact ⟨p, norm_cfc_sub_aeval_le hA hspec hf hε p hp⟩

omit [CompleteSpace E] in
theorem aeval_apply_mem (A : E →L[ℂ] E) (V : Submodule ℂ E) (hAV : ∀ v ∈ V, A v ∈ V)
    (p : Polynomial ℝ) {v : E} (hv : v ∈ V) : Polynomial.aeval A p v ∈ V := by
  have hpow : ∀ n : ℕ, ∀ v ∈ V, (A ^ n) v ∈ V := by
    intro n
    induction n with
    | zero => intro v hv; simpa using hv
    | succ n ih => intro v hv; rw [pow_succ]; exact ih _ (hAV v hv)
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, add_apply]; exact V.add_mem hp hq
  | monomial n c =>
    rw [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul,
      smul_apply]
    exact V.smul_of_tower_mem c (hpow n v hv)

omit [CompleteSpace E] in
theorem aeval_apply_eq (A B : E →L[ℂ] E) (v : E) (hAB : ∀ n : ℕ, (A ^ n) v = (B ^ n) v)
    (p : Polynomial ℝ) : Polynomial.aeval A p v = Polynomial.aeval B p v := by
  induction p using Polynomial.induction_on' with
  | add p q hp hq => rw [map_add, map_add, add_apply,
      add_apply, hp, hq]
  | monomial n c =>
    simp only [Polynomial.aeval_monomial, Algebra.algebraMap_eq_smul_one, smul_mul_assoc,
      one_mul, smul_apply, hAB n]

/-- The functional calculus of a self-adjoint `A` preserves every closed subspace that `A`
preserves. -/
theorem cfc_apply_mem {A : E →L[ℂ] E} (hA : IsSelfAdjoint A) {a b : ℝ}
    (hspec : spectrum ℝ A ⊆ Set.Icc a b) {f : ℝ → ℝ} (hf : ContinuousOn f (Set.Icc a b))
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E)) (hAV : ∀ v ∈ V, A v ∈ V) {v : E}
    (hv : v ∈ V) : cfc f A v ∈ V := by
  show cfc f A v ∈ (V : Set E)
  rw [← hV.closure_eq, Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨p, hp⟩ := exists_poly_near_cfc hA hspec hf (ε := ε / 2 / (‖v‖ + 1)) (by positivity)
  refine ⟨Polynomial.aeval A p v, aeval_apply_mem A V hAV p hv, ?_⟩
  rw [dist_eq_norm, ← sub_apply]
  calc ‖(cfc f A - Polynomial.aeval A p) v‖ ≤ ‖cfc f A - Polynomial.aeval A p‖ * ‖v‖ :=
        ContinuousLinearMap.le_opNorm _ _
    _ ≤ ε / 2 / (‖v‖ + 1) * (‖v‖ + 1) := by gcongr; linarith
    _ = ε / 2 := by field_simp
    _ < ε := by linarith

/-- If `Aⁿ v = Bⁿ v` for all `n`, then `f(A) v = f(B) v` for the functional calculi of the
self-adjoint operators `A` and `B`. -/
theorem cfc_apply_eq {A B : E →L[ℂ] E} (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B) {a b : ℝ}
    (hspecA : spectrum ℝ A ⊆ Set.Icc a b) (hspecB : spectrum ℝ B ⊆ Set.Icc a b) {f : ℝ → ℝ}
    (hf : ContinuousOn f (Set.Icc a b)) (v : E) (hAB : ∀ n : ℕ, (A ^ n) v = (B ^ n) v) :
    cfc f A v = cfc f B v := by
  refine eq_of_forall_dist_le (fun ε hε => ?_)
  have hε' : 0 < ε / 2 / (‖v‖ + 1) := by positivity
  obtain ⟨p, hp⟩ := exists_polynomial_near_of_continuousOn a b f hf _ hε'
  have hA' := norm_cfc_sub_aeval_le hA hspecA hf hε' p hp
  have hB' := norm_cfc_sub_aeval_le hB hspecB hf hε' p hp
  have e : cfc f A v - cfc f B v
      = (cfc f A - Polynomial.aeval A p) v - (cfc f B - Polynomial.aeval B p) v := by
    simp only [sub_apply, aeval_apply_eq A B v hAB p]; abel
  rw [dist_eq_norm, e]
  calc ‖(cfc f A - Polynomial.aeval A p) v - (cfc f B - Polynomial.aeval B p) v‖
      ≤ ‖(cfc f A - Polynomial.aeval A p) v‖ + ‖(cfc f B - Polynomial.aeval B p) v‖ :=
        norm_sub_le _ _
    _ ≤ ‖cfc f A - Polynomial.aeval A p‖ * ‖v‖ + ‖cfc f B - Polynomial.aeval B p‖ * ‖v‖ :=
        add_le_add (ContinuousLinearMap.le_opNorm _ _) (ContinuousLinearMap.le_opNorm _ _)
    _ ≤ ε / 2 / (‖v‖ + 1) * (‖v‖ + 1) + ε / 2 / (‖v‖ + 1) * (‖v‖ + 1) := by
        gcongr <;> linarith
    _ = ε := by field_simp; ring

/-! ### Changing the shift -/

omit [CompleteSpace E] in
/-- The shift-invert operator at a given shift is unique. -/
theorem IsShiftInvert.unique {H : E →ₗ.[ℂ] E} {z : ℂ} {R₁ R₂ : E →L[ℂ] E}
    (h₁ : IsShiftInvert H z R₁) (h₂ : IsShiftInvert H z R₂) : R₁ = R₂ := by
  ext x
  have := h₁.left_inv ⟨R₂ x, h₂.mem_domain x⟩
  simp only at this
  rw [h₂.right_inv x] at this
  exact this

omit [CompleteSpace E] in
theorem shift_factor_pos (hH : IsSemibounded H m σ R) {σ' : ℝ} (hσ' : σ' < m) {r : ℝ}
    (hr : r ∈ Set.Icc 0 (m - σ)⁻¹) : 0 < 1 - (σ' - σ) * r := by
  have hpos : 0 < m - σ := sub_pos.mpr hH.shift_lt
  rcases le_or_gt (σ' - σ) 0 with hc | hc
  · nlinarith [hr.1]
  · have h1 : r * (m - σ) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hr.2 hpos.le
      rwa [inv_mul_cancel₀ hpos.ne'] at this
    nlinarith [hr.1]

/-- **The resolvent exists at every shift below the lower bound.** If `H` is semibounded with
shift-invert operator at one shift `σ < m`, then it has one at every shift `σ' < m`, namely
`R (1 - (σ' - σ) R)⁻¹`. This operator preserves every closed subspace preserved by `R`. -/
theorem IsSemibounded.exists_shift (hH : IsSemibounded H m σ R) {σ' : ℝ} (hσ' : σ' < m) :
    ∃ R' : E →L[ℂ] E, IsSemibounded H m σ' R' ∧
      ∀ V : Submodule ℂ E, IsClosed (V : Set E) → (∀ v ∈ V, R v ∈ V) → ∀ v ∈ V, R' v ∈ V := by
  have hR := hH.isSelfAdjoint_R
  set c := σ' - σ with hc
  set g : ℝ → ℝ := fun r => (1 - c * r)⁻¹ with hg
  have hspec := hH.spectrum_R_subset
  have hgI : ContinuousOn g (Set.Icc 0 (m - σ)⁻¹) := by
    refine ((continuous_const.sub (continuous_const.mul continuous_id)).continuousOn).inv₀ ?_
    intro r hr; exact (shift_factor_pos hH hσ' hr).ne'
  have hgc : ContinuousOn g (spectrum ℝ R) := hgI.mono hspec
  set G := cfc g R with hG
  have h1c : 1 - c • R = cfc (fun r => 1 - c * r) R := by
    rw [cfc_sub (a := R) (fun _ => (1 : ℝ)) (fun r => c * r) continuousOn_const
      (continuous_const.mul continuous_id).continuousOn, cfc_const_one ℝ R hR,
      cfc_const_mul c (fun r => r) R continuous_id.continuousOn, cfc_id' ℝ R hR]
  have hinvL : (1 - c • R) * G = 1 := by
    rw [h1c, hG, ← cfc_mul (a := R) (fun r => 1 - c * r) g
      ((continuous_const.sub (continuous_const.mul continuous_id)).continuousOn) hgc]
    rw [← cfc_const_one ℝ R hR]
    refine cfc_congr (fun r hr => ?_)
    exact mul_inv_cancel₀ (shift_factor_pos hH hσ' (hspec hr)).ne'
  have hcomm : Commute G R := by
    have := cfc_commute_cfc g id R
    rwa [cfc_id ℝ R hR] at this
  have hinvR : G * (1 - c • R) = 1 := by
    exact ((Commute.one_right G).sub_right (hcomm.smul_right c)).eq.trans hinvL
  have hsplit : ∀ w : E, ((σ' : ℝ) : ℂ) • w = (σ : ℂ) • w + c • w := by
    intro w; rw [← Complex.coe_smul, ← add_smul]; congr 1; rw [hc]; push_cast; ring
  refine ⟨R * G, ⟨hH.symm, hH.lower, hσ', ?_, ?_, ?_⟩, ?_⟩
  · intro x; exact hH.inv.mem_domain (G x)
  · intro x
    have h := hH.inv.right_inv (G x)
    have hx : (1 - c • R) (G x) = x := by
      rw [← mul_apply_eq_comp, hinvL]; rfl
    show H ⟨R (G x), hH.inv.mem_domain (G x)⟩ - ((σ' : ℝ) : ℂ) • R (G x) = x
    rw [hsplit, ← sub_sub, h]
    conv_rhs => rw [← hx]
    simp
  · intro y
    have hz := hH.inv.left_inv y
    set z : E := H y - (σ : ℂ) • (y : E) with hzdef
    have e : H y - ((σ' : ℝ) : ℂ) • (y : E) = (1 - c • R) z := by
      rw [hsplit, ← sub_sub, ← hzdef]
      simp [hz]
    rw [e, mul_apply_eq_comp, ← mul_apply_eq_comp G, hinvR]
    exact hz
  · intro V hV hRV v hv
    exact hRV _ (cfc_apply_mem hR hspec hgI V hV hRV hv)

end CftCheck
