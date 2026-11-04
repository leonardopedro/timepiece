import RequestProject.HeatSemigroup
import RequestProject.NestedFock

/-!
# Claims A and B for unbounded `H` and `N`

The transfer operators `exp(-τH)` and `exp(-τ(H + μN))` of `HeatSemigroup.lean` are used to
redo the Euclidean statements of claims A and B without assuming bounded operators:
factorisation of the shifted dynamics on a sector, `μ`-independence of normalised correlations,
the inner-vacuum correlations, coercivity and contraction on `Ω^⊥`, and the equivalence between
a Hamiltonian gap and exponential decay of the transfer operator.
-/

open scoped InnerProductSpace

noncomputable section

namespace CftCheck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-! ## Claim B for unbounded `H` and `N` -/

/-- **On a fixed outer sector the shift is a scalar (unbounded version).**
Let `H`, `N` be unbounded, `Hμ = H + μN` on `D(H) ∩ D(N)`, and suppose `H` and `Hμ` are
semibounded self-adjoint (each has a shift-invert operator). Let `V` be a closed subspace of the
sector `N = n` that is preserved by the shift-invert operator of `H` (this is what `[H, N] = 0`
means for unbounded operators). Then for all `τ ≥ 0` and `ψ ∈ V`,
`exp(-τ(H + μN)) ψ = e^{-τμn} exp(-τH) ψ`. -/
theorem heat_shifted_on_sector (H N Hμ : E →ₗ.[ℂ] E) (μ n : ℝ)
    (hdom : ∀ y : E, y ∈ H.domain → y ∈ N.domain → y ∈ Hμ.domain)
    (hsum : ∀ (y : E) (hH : y ∈ H.domain) (hN : y ∈ N.domain),
      Hμ ⟨y, hdom y hH hN⟩ = H ⟨y, hH⟩ + (μ : ℂ) • N ⟨y, hN⟩)
    {m σ mμ σμ : ℝ} {R Rμ : E →L[ℂ] E} (hH : IsSemibounded H m σ R)
    (hHμ : IsSemibounded Hμ mμ σμ Rμ)
    (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
    (hVN : ∀ v ∈ V, ∃ h : v ∈ N.domain, N ⟨v, h⟩ = (n : ℂ) • v)
    (hRV : ∀ v ∈ V, R v ∈ V) {τ : ℝ} (hτ : 0 ≤ τ) {ψ : E} (hψ : ψ ∈ V) :
    heatSG σμ Rμ τ ψ = Real.exp (-(τ * μ * n)) • heatSG σ R τ ψ := by
  -- a common shift `s` below both lower bounds
  obtain ⟨s, hs1, hs2⟩ : ∃ s : ℝ, s < mμ ∧ s - μ * n < m :=
    ⟨min (mμ - 1) (m + μ * n - 1), by have := min_le_left (mμ - 1) (m + μ * n - 1); linarith,
      by have := min_le_right (mμ - 1) (m + μ * n - 1); linarith⟩
  obtain ⟨Rμ', hRμ', -⟩ := hHμ.exists_shift hs1
  obtain ⟨R', hR', hR'V⟩ := hH.exists_shift hs2
  have hR'V := hR'V V hV hRV
  -- on `V` the two shift-invert operators agree
  have hagree : ∀ v ∈ V, Rμ' v = R' v := by
    intro v hv
    obtain ⟨hNd, hNv⟩ := hVN _ (hR'V v hv)
    refine shifted_shiftInvert_on_sector H N Hμ μ n s hdom hsum Rμ' R' hRμ'.inv ?_ v hNd hNv
    have := hR'.inv
    push_cast at this ⊢
    exact this
  have hpow : ∀ k : ℕ, ∀ v ∈ V, (Rμ' ^ k) v = (R' ^ k) v ∧ (R' ^ k) v ∈ V := by
    intro k
    induction k with
    | zero => intro v hv; simpa using hv
    | succ k ih =>
      intro v hv
      obtain ⟨h1, h2⟩ := ih (R' v) (hR'V v hv)
      refine ⟨?_, ?_⟩
      · rw [pow_succ, mul_apply_eq_comp, hagree v hv, pow_succ,
          mul_apply_eq_comp, h1]
      · rw [pow_succ, mul_apply_eq_comp]; exact h2
  rw [heatSG_unique hHμ hRμ' hτ, heatSG_unique hH hR' hτ]
  rcases eq_or_lt_of_le hτ with rfl | hτ'
  · simp
  rw [heatSG_of_pos _ _ hτ', heatSG_of_pos _ _ hτ']
  simp only [smul_apply]
  have hcfc : cfc (heatFun τ) Rμ' ψ = cfc (heatFun τ) R' ψ := by
    refine cfc_apply_eq hRμ'.isSelfAdjoint_R hR'.isSelfAdjoint_R
      (b := max (mμ - s)⁻¹ (m - (s - μ * n))⁻¹)
      (hRμ'.spectrum_R_subset.trans (Set.Icc_subset_Icc le_rfl (le_max_left _ _)))
      (hR'.spectrum_R_subset.trans (Set.Icc_subset_Icc le_rfl (le_max_right _ _)))
      (continuous_heatFun hτ').continuousOn ψ (fun k => (hpow k ψ hψ).1)
  rw [hcfc, smul_smul, ← Real.exp_add]
  congr 2
  ring

section Sector

variable (H N Hμ : E →ₗ.[ℂ] E) (μ n : ℝ)
  (hdom : ∀ y : E, y ∈ H.domain → y ∈ N.domain → y ∈ Hμ.domain)
  (hsum : ∀ (y : E) (hH : y ∈ H.domain) (hN : y ∈ N.domain),
    Hμ ⟨y, hdom y hH hN⟩ = H ⟨y, hH⟩ + (μ : ℂ) • N ⟨y, hN⟩)
  {m σ mμ σμ : ℝ} {R Rμ : E →L[ℂ] E} (hH : IsSemibounded H m σ R)
  (hHμ : IsSemibounded Hμ mμ σμ Rμ)
  (V : Submodule ℂ E) (hV : IsClosed (V : Set E))
  (hVN : ∀ v ∈ V, ∃ h : v ∈ N.domain, N ⟨v, h⟩ = (n : ℂ) • v)
  (hRV : ∀ v ∈ V, R v ∈ V)

include hsum hH hHμ hV hVN hRV

/-- Every matrix element of `exp(-τ(H + μN))` into the sector factorises as `e^{-τμn}` times
the corresponding matrix element of `exp(-τH)` (unbounded version). -/
theorem heat_shifted_correlation_factorizes {τ : ℝ} (hτ : 0 ≤ τ) (χ : E) {ψ : E} (hψ : ψ ∈ V) :
    ⟪χ, heatSG σμ Rμ τ ψ⟫_ℂ = (Real.exp (-(τ * μ * n)) : ℂ) * ⟪χ, heatSG σ R τ ψ⟫_ℂ := by
  rw [heat_shifted_on_sector H N Hμ μ n hdom hsum hH hHμ V hV hVN hRV hτ hψ, ← Complex.coe_smul,
    inner_smul_right]

/-- **Normalised correlations do not see `μ` (unbounded version).** For `ψ` and `Bψ` in the
sector and any bounded `A`,
`⟪ψ, A e^{-τ(H+μN)} B ψ⟫ / ⟪ψ, e^{-τ(H+μN)} ψ⟫ = ⟪ψ, A e^{-τH} B ψ⟫ / ⟪ψ, e^{-τH} ψ⟫`. -/
theorem heat_shifted_normalized_correlation_invariant {τ : ℝ} (hτ : 0 ≤ τ) (A B : E →L[ℂ] E)
    {ψ : E} (hψ : ψ ∈ V) (hBψ : B ψ ∈ V) :
    ⟪ψ, A (heatSG σμ Rμ τ (B ψ))⟫_ℂ / ⟪ψ, heatSG σμ Rμ τ ψ⟫_ℂ
      = ⟪ψ, A (heatSG σ R τ (B ψ))⟫_ℂ / ⟪ψ, heatSG σ R τ ψ⟫_ℂ := by
  rw [heat_shifted_on_sector H N Hμ μ n hdom hsum hH hHμ V hV hVN hRV hτ hψ,
    heat_shifted_on_sector H N Hμ μ n hdom hsum hH hHμ V hV hVN hRV hτ hBψ,
    ← Complex.coe_smul, ← Complex.coe_smul, map_smul, inner_smul_right, inner_smul_right]
  exact mul_div_mul_left _ _ (by exact_mod_cast (Real.exp_pos _).ne')

/-- **Inner-vacuum correlations under the shift (unbounded version).** Take `ω`, `φ` in the
sector, `Hω = 0`, `Hφ = eφ`, `ω ⊥ φ`, `‖ω‖ = 1`, and `O = |φ⟩⟨ω|`, `A = |ω⟩⟨φ|`. The
unnormalised correlation is `e^{-τ(μn + e)}‖φ‖²`, while the normalised truncated correlation is
`e^{-τe}‖φ‖²`, for every `μ`. -/
theorem heat_inner_vacuum_shifted_correlation {τ : ℝ} (hτ : 0 ≤ τ) (ω φ : H.domain)
    (hωV : (ω : E) ∈ V) (hφV : (φ : E) ∈ V) (hHω : H ω = 0) (e : ℝ)
    (hHφ : H φ = (e : ℂ) • (φ : E)) (horth : ⟪(ω : E), (φ : E)⟫_ℂ = 0) (hω1 : ‖(ω : E)‖ = 1) :
    ⟪(ω : E), rankOne (φ : E) ω (heatSG σμ Rμ τ (rankOne (ω : E) φ ω))⟫_ℂ
        = (Real.exp (-(τ * (μ * n + e))) * ‖(φ : E)‖ ^ 2 : ℝ) ∧
      truncCorr (heatSG σμ Rμ τ) (rankOne (φ : E) ω) (rankOne (ω : E) φ) ω
        = (Real.exp (-(τ * e)) * ‖(φ : E)‖ ^ 2 : ℝ) := by
  have hωω : ⟪(ω : E), (ω : E)⟫_ℂ = 1 := by rw [inner_self_eq_norm_sq_to_K]; simp [hω1]
  have hφω : ⟪(φ : E), (ω : E)⟫_ℂ = 0 := by rw [← inner_conj_symm, horth, map_zero]
  have hOω : rankOne (ω : E) φ ω = φ := by simp [hω1]
  have hφφ : ⟪(φ : E), (φ : E)⟫_ℂ = ((‖(φ : E)‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]; push_cast; rfl
  have hUφ : heatSG σμ Rμ τ φ
      = ((Real.exp (-(τ * μ * n)) * Real.exp (-(τ * e)) : ℝ) : ℂ) • (φ : E) := by
    rw [heat_shifted_on_sector H N Hμ μ n hdom hsum hH hHμ V hV hVN hRV hτ hφV,
      heatSG_eigen hH φ e hHφ hτ, smul_smul, Complex.coe_smul]
  have hUω : heatSG σμ Rμ τ ω = ((Real.exp (-(τ * μ * n)) : ℝ) : ℂ) • (ω : E) := by
    rw [heat_shifted_on_sector H N Hμ μ n hdom hsum hH hHμ V hV hVN hRV hτ hωV,
      heatSG_eigen hH ω 0 (by simp [hHω]) hτ, Complex.coe_smul]
    simp
  have hnum : ⟪(ω : E), rankOne (φ : E) ω (heatSG σμ Rμ τ (rankOne (ω : E) φ ω))⟫_ℂ
      = (Real.exp (-(τ * (μ * n + e))) * ‖(φ : E)‖ ^ 2 : ℝ) := by
    rw [hOω, hUφ, rankOne_apply, inner_smul_right, inner_smul_right, hωω, hφφ, mul_one,
      ← Complex.ofReal_mul, ← Real.exp_add]
    congr 3; ring
  refine ⟨hnum, ?_⟩
  rw [truncCorr, hnum, hUω, inner_smul_right, hωω, hOω]
  simp only [rankOne_apply, hφω, zero_smul, inner_zero_right, zero_mul, sub_zero, mul_one]
  rw [div_eq_iff (by exact_mod_cast (Real.exp_pos _).ne'), ← Complex.ofReal_mul]
  congr 1
  rw [mul_right_comm, ← Real.exp_add]
  congr 2; ring

/-- **The artificial gap does not give clustering at rate `μ` in the inner vacuum (unbounded
version).** In the setting of `heat_inner_vacuum_shifted_correlation`, if `φ ≠ 0` and `e < μ`,
the normalised truncated correlation in `ω` is not bounded by `C e^{-μτ}` for any `C`. -/
theorem heat_inner_vacuum_no_rate_mu_clustering (ω φ : H.domain)
    (hωV : (ω : E) ∈ V) (hφV : (φ : E) ∈ V) (hHω : H ω = 0) (e : ℝ)
    (hHφ : H φ = (e : ℂ) • (φ : E)) (horth : ⟪(ω : E), (φ : E)⟫_ℂ = 0) (hω1 : ‖(ω : E)‖ = 1)
    (hφ0 : (φ : E) ≠ 0) (he : e < μ) :
    ¬ ∃ C : ℝ, ∀ τ : ℝ, 0 ≤ τ →
      ‖truncCorr (heatSG σμ Rμ τ) (rankOne (φ : E) ω) (rankOne (ω : E) φ) ω‖
        ≤ C * Real.exp (-(μ * τ)) := by
  rintro ⟨C, hC⟩
  have hpos : 0 < ‖(φ : E)‖ ^ 2 := by positivity
  have hb : ∀ τ : ℝ, 0 ≤ τ → ‖(φ : E)‖ ^ 2 ≤ C * Real.exp (-((μ - e) * τ)) := by
    intro τ hτ
    have h := hC τ hτ
    rw [(heat_inner_vacuum_shifted_correlation H N Hμ μ n hdom hsum hH hHμ V hV hVN hRV hτ ω φ
      hωV hφV hHω e hHφ horth hω1).2, Complex.norm_real, Real.norm_of_nonneg (by positivity)] at h
    have he' : Real.exp (-((μ - e) * τ)) = Real.exp (-(μ * τ)) * Real.exp (τ * e) := by
      rw [← Real.exp_add]; ring_nf
    have hx : Real.exp (-(τ * e)) * Real.exp (τ * e) = 1 := by
      rw [← Real.exp_add]; simp
    rw [he', ← mul_assoc]
    have := mul_le_mul_of_nonneg_right h (Real.exp_pos (τ * e)).le
    calc ‖(φ : E)‖ ^ 2 = Real.exp (-(τ * e)) * ‖(φ : E)‖ ^ 2 * Real.exp (τ * e) := by
          rw [mul_right_comm, hx, one_mul]
      _ ≤ _ := this
  have hlim : Filter.Tendsto (fun τ : ℝ => C * Real.exp (-((μ - e) * τ))) Filter.atTop
      (nhds 0) := by
    have h1 : Filter.Tendsto (fun τ : ℝ => (μ - e) * τ) Filter.atTop Filter.atTop :=
      Filter.tendsto_id.const_mul_atTop (sub_pos.2 he)
    simpa using (Real.tendsto_exp_neg_atTop_nhds_zero.comp h1).const_mul C
  have hle : ‖(φ : E)‖ ^ 2 ≤ 0 :=
    ge_of_tendsto hlim (Filter.eventually_atTop.2 ⟨0, fun τ hτ => hb τ hτ⟩)
  linarith

end Sector

/-! ## Coercivity, vacuum invariance and contraction for unbounded `H + μN` -/

omit [CompleteSpace E] in
/-- **Coercivity (unbounded version).** If `H ≥ 0` on `D(H)`, `N ≥ 1` on `D(N) ∩ Ω^⊥` and
`Hμ = H + μN` on `D(H) ∩ D(N)` with `μ ≥ 0`, then `Re⟪y, Hμ y⟫ ≥ μ‖y‖²` for
`y ∈ D(H) ∩ D(N)`, `y ⊥ Ω`. -/
theorem shifted_coercive_unbounded (H N Hμ : E →ₗ.[ℂ] E) (μ : ℝ) (hμ : 0 ≤ μ)
    (hdom : ∀ y : E, y ∈ H.domain → y ∈ N.domain → y ∈ Hμ.domain)
    (hsum : ∀ (y : E) (hH : y ∈ H.domain) (hN : y ∈ N.domain),
      Hμ ⟨y, hdom y hH hN⟩ = H ⟨y, hH⟩ + (μ : ℂ) • N ⟨y, hN⟩) (Ω : E)
    (hH0 : ∀ x : H.domain, 0 ≤ RCLike.re ⟪(x : E), H x⟫_ℂ)
    (hN1 : ∀ x : N.domain, ⟪Ω, (x : E)⟫_ℂ = 0 → ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪(x : E), N x⟫_ℂ)
    (y : E) (hyH : y ∈ H.domain) (hyN : y ∈ N.domain) (hy : ⟪Ω, y⟫_ℂ = 0) :
    μ * ‖y‖ ^ 2 ≤ RCLike.re ⟪y, Hμ ⟨y, hdom y hyH hyN⟩⟫_ℂ := by
  rw [hsum y hyH hyN, inner_add_right, inner_smul_right, map_add]
  have h1 := hH0 ⟨y, hyH⟩
  have h2 := hN1 ⟨y, hyN⟩ hy
  simp only at h1 h2
  have : RCLike.re ((μ : ℂ) * ⟪y, N ⟨y, hyN⟩⟫_ℂ) = μ * RCLike.re ⟪y, N ⟨y, hyN⟩⟫_ℂ := by
    simp
  rw [this]; nlinarith

omit [CompleteSpace E] in
/-- **Resolvent-type bound (unbounded version):** `‖Hμ y‖ ≥ μ‖y‖` for `y ∈ D(H) ∩ D(N)`,
`y ⊥ Ω`. -/
theorem shifted_resolvent_bound_unbounded (H N Hμ : E →ₗ.[ℂ] E) (μ : ℝ) (hμ : 0 ≤ μ)
    (hdom : ∀ y : E, y ∈ H.domain → y ∈ N.domain → y ∈ Hμ.domain)
    (hsum : ∀ (y : E) (hH : y ∈ H.domain) (hN : y ∈ N.domain),
      Hμ ⟨y, hdom y hH hN⟩ = H ⟨y, hH⟩ + (μ : ℂ) • N ⟨y, hN⟩) (Ω : E)
    (hH0 : ∀ x : H.domain, 0 ≤ RCLike.re ⟪(x : E), H x⟫_ℂ)
    (hN1 : ∀ x : N.domain, ⟪Ω, (x : E)⟫_ℂ = 0 → ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪(x : E), N x⟫_ℂ)
    (y : E) (hyH : y ∈ H.domain) (hyN : y ∈ N.domain) (hy : ⟪Ω, y⟫_ℂ = 0) :
    μ * ‖y‖ ≤ ‖Hμ ⟨y, hdom y hyH hyN⟩‖ := by
  have h := shifted_coercive_unbounded H N Hμ μ hμ hdom hsum Ω hH0 hN1 y hyH hyN hy
  have hcs : RCLike.re ⟪y, Hμ ⟨y, hdom y hyH hyN⟩⟫_ℂ ≤ ‖y‖ * ‖Hμ ⟨y, hdom y hyH hyN⟩‖ :=
    (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
  rcases (norm_nonneg y).eq_or_lt with h0 | hpos
  · rw [← h0]; simp
  · nlinarith

/-- The projection `z ↦ z - (⟪Ω, z⟫/‖Ω‖²) Ω` onto `Ω^⊥`. -/
def projOrth (Ω z : E) : E := z - (⟪Ω, z⟫_ℂ / ((‖Ω‖ ^ 2 : ℝ) : ℂ)) • Ω

omit [CompleteSpace E] in
theorem inner_projOrth (Ω z : E) : ⟪Ω, projOrth Ω z⟫_ℂ = 0 := by
  rcases eq_or_ne Ω 0 with rfl | hΩ
  · simp
  rw [projOrth, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K]
  push_cast
  exact sub_eq_zero.mpr (div_mul_cancel₀ _ (by simpa using hΩ)).symm

omit [CompleteSpace E] in
theorem projOrth_of_orth {Ω z : E} (hz : ⟪Ω, z⟫_ℂ = 0) : projOrth Ω z = z := by
  simp [projOrth, hz]

omit [CompleteSpace E] in
theorem continuous_projOrth (Ω : E) : Continuous (projOrth Ω) := by
  unfold projOrth; fun_prop

/-- **Exponential decay of the transfer operator on `Ω^⊥`.** Let `K` be semibounded
self-adjoint with `KΩ = 0` and `Re⟪x, Kx⟫ ≥ c‖x‖²` for `x ∈ D(K)`, `x ⊥ Ω`. Then
`‖exp(-τK) x‖ ≤ e^{-cτ}‖x‖` for every `x ⊥ Ω` and `τ ≥ 0`. -/
theorem heatSG_contraction_orth {K : E →ₗ.[ℂ] E} {m σ : ℝ} {R : E →L[ℂ] E}
    (hK : IsSemibounded K m σ R) (Ω : K.domain) (hKΩ : K Ω = 0) (c : ℝ)
    (hc : ∀ x : K.domain, ⟪(Ω : E), (x : E)⟫_ℂ = 0 → c * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪(x : E), K x⟫_ℂ)
    {τ : ℝ} (hτ : 0 ≤ τ) (x : E) (hx : ⟪(Ω : E), x⟫_ℂ = 0) :
    ‖heatSG σ R τ x‖ ≤ Real.exp (-(c * τ)) * ‖x‖ := by
  have hTΩ : ∀ t, 0 ≤ t → heatSG σ R t Ω = Ω := fun t ht => by
    simpa using heatSG_eigen hK Ω 0 (by simp [hKΩ]) ht
  have horth : ∀ t, 0 ≤ t → ∀ y : E, ⟪(Ω : E), y⟫_ℂ = 0 → ⟪(Ω : E), heatSG σ R t y⟫_ℂ = 0 := by
    intro t ht y hy
    rw [← ContinuousLinearMap.adjoint_inner_left, (isSelfAdjoint_heatSG σ R t).adjoint_eq,
      hTΩ t ht, hy]
  -- the estimate on `D(K) ∩ Ω^⊥`
  have hdom : ∀ y : K.domain, ⟪(Ω : E), (y : E)⟫_ℂ = 0 →
      ‖heatSG σ R τ y‖ ≤ Real.exp (-(c * τ)) * ‖(y : E)‖ := by
    intro y hy
    have hsol := heatSG_isHeatSolution hK y
    have h := hsol.norm_sq_le c (fun t ht => hc ⟨_, _⟩ (horth t ht y hy)) hτ
    simp only [heatSG_zero, one_apply_eq_self] at h
    have he : Real.exp (-2 * c * τ) = Real.exp (-(c * τ)) ^ 2 := by
      rw [← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [he, ← mul_pow, mul_comm ‖(y : E)‖] at h
    exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) two_ne_zero).mp h
  -- extend by density
  have key : ∀ z : E, ‖heatSG σ R τ (projOrth (Ω : E) z)‖
      ≤ Real.exp (-(c * τ)) * ‖projOrth (Ω : E) z‖ := by
    intro z
    refine hK.denseRange_R.induction_on z ?_ ?_
    · exact isClosed_le ((heatSG σ R τ).continuous.comp (continuous_projOrth _)).norm
        (continuous_const.mul (continuous_projOrth _).norm)
    · intro y
      have hmem : projOrth (Ω : E) (R y) ∈ K.domain :=
        K.domain.sub_mem (hK.inv.mem_domain y) (K.domain.smul_mem _ Ω.2)
      exact hdom ⟨_, hmem⟩ (inner_projOrth _ _)
  simpa [projOrth_of_orth hx] using key x

/-- **Converse: decay of the transfer operator gives a gap for eigenvalues.** If
`‖exp(-τK) x‖ ≤ e^{-gτ}‖x‖` for all `x ⊥ Ω` at some `τ > 0`, then every eigenvalue of `K` with
an eigenvector `v ⊥ Ω`, `v ≠ 0`, is at least `g`. -/
theorem gap_of_heatSG_decay {K : E →ₗ.[ℂ] E} {m σ : ℝ} {R : E →L[ℂ] E}
    (hK : IsSemibounded K m σ R) (Ω : E) (g : ℝ) {τ : ℝ} (hτ : 0 < τ)
    (hdecay : ∀ x : E, ⟪Ω, x⟫_ℂ = 0 → ‖heatSG σ R τ x‖ ≤ Real.exp (-(g * τ)) * ‖x‖)
    (v : K.domain) (hv : (v : E) ≠ 0) (hvΩ : ⟪Ω, (v : E)⟫_ℂ = 0) (e : ℝ)
    (hev : K v = (e : ℂ) • (v : E)) : g ≤ e := by
  have h := hdecay v hvΩ
  rw [heatSG_eigen hK v e hev hτ.le, norm_smul, Real.norm_of_nonneg (Real.exp_pos _).le] at h
  have hn : 0 < ‖(v : E)‖ := norm_pos_iff.mpr hv
  have := le_of_mul_le_mul_right h hn
  rw [Real.exp_le_exp] at this
  nlinarith

/-- **The artificial-gap transfer operator, unbounded version.** Suppose `H ≥ 0`, `N ≥ 1` on
`Ω^⊥`, `HΩ = NΩ = 0`, `μ ≥ 0`, and `Hμ = H + μN` on `D(H) ∩ D(N)` is semibounded self-adjoint
with `D(Hμ) = D(H) ∩ D(N)`. Then `exp(-τHμ)` fixes `Ω` and
`‖exp(-τHμ) x‖ ≤ e^{-μτ}‖x‖` for every `x ⊥ Ω`. -/
theorem shifted_heat_contraction (H N Hμ : E →ₗ.[ℂ] E) (μ : ℝ) (hμ : 0 ≤ μ)
    (hdom : ∀ y : E, y ∈ H.domain → y ∈ N.domain → y ∈ Hμ.domain)
    (hdom' : ∀ y : E, y ∈ Hμ.domain → y ∈ H.domain ∧ y ∈ N.domain)
    (hsum : ∀ (y : E) (hH : y ∈ H.domain) (hN : y ∈ N.domain),
      Hμ ⟨y, hdom y hH hN⟩ = H ⟨y, hH⟩ + (μ : ℂ) • N ⟨y, hN⟩)
    {mμ σμ : ℝ} {Rμ : E →L[ℂ] E} (hHμ : IsSemibounded Hμ mμ σμ Rμ) (Ω : E)
    (hΩH : Ω ∈ H.domain) (hΩN : Ω ∈ N.domain) (hHΩ : H ⟨Ω, hΩH⟩ = 0) (hNΩ : N ⟨Ω, hΩN⟩ = 0)
    (hH0 : ∀ x : H.domain, 0 ≤ RCLike.re ⟪(x : E), H x⟫_ℂ)
    (hN1 : ∀ x : N.domain, ⟪Ω, (x : E)⟫_ℂ = 0 → ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪(x : E), N x⟫_ℂ)
    {τ : ℝ} (hτ : 0 ≤ τ) :
    heatSG σμ Rμ τ Ω = Ω ∧
      ∀ x : E, ⟪Ω, x⟫_ℂ = 0 → ‖heatSG σμ Rμ τ x‖ ≤ Real.exp (-(μ * τ)) * ‖x‖ := by
  have hHμΩ : Hμ ⟨Ω, hdom Ω hΩH hΩN⟩ = 0 := by rw [hsum Ω hΩH hΩN, hHΩ, hNΩ, smul_zero, add_zero]
  refine ⟨by simpa using heatSG_eigen hHμ ⟨Ω, hdom Ω hΩH hΩN⟩ 0 (by simp [hHμΩ]) hτ, ?_⟩
  intro x hx
  refine heatSG_contraction_orth hHμ ⟨Ω, hdom Ω hΩH hΩN⟩ hHμΩ μ (fun y hy => ?_) hτ x hx
  obtain ⟨hyH, hyN⟩ := hdom' y y.2
  have := shifted_coercive_unbounded H N Hμ μ hμ hdom hsum Ω hH0 hN1 y hyH hyN hy
  simpa using this

/-! ## Claim A for unbounded `H` -/

omit [CompleteSpace E] in
/-- **Temple enclosure with a uniform separation input (unbounded version).** -/
theorem temple_enclosure_unbounded (H : E →ₗ.[ℂ] E) (l₀ β c : ℝ) (hc : 0 < c)
    (hspec : ∀ x : H.domain, 0 ≤ RCLike.re ⟪H x - (β : ℂ) • (x : E), H x - (l₀ : ℂ) • (x : E)⟫_ℂ)
    (hbot : ∀ x : H.domain, l₀ * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪(x : E), H x⟫_ℂ)
    (ψ : H.domain) (hψ : ‖(ψ : E)‖ = 1) (hsep : c ≤ β - RCLike.re ⟪(ψ : E), H ψ⟫_ℂ) :
    RCLike.re ⟪(ψ : E), H ψ⟫_ℂ
        - ‖H ψ - ((RCLike.re ⟪(ψ : E), H ψ⟫_ℂ : ℝ) : ℂ) • (ψ : E)‖ ^ 2 / c ≤ l₀ ∧
      l₀ ≤ RCLike.re ⟪(ψ : E), H ψ⟫_ℂ := by
  have hpos : 0 < β - RCLike.re ⟪(ψ : E), H ψ⟫_ℂ := lt_of_lt_of_le hc hsep
  have ht := temple_lower_bound_unbounded H l₀ β hspec ψ hψ (by linarith)
  refine ⟨le_trans ?_ ht, by simpa [hψ] using hbot ψ⟩
  gcongr

omit [CompleteSpace E] in
/-- **Algebraic form of the `dΓ` lift (unbounded version).** If each of the (possibly unbounded)
summands `h i` satisfies `Re⟪y, h i y⟫ ≥ μ‖y‖²` on its domain, then on the common domain the sum
satisfies `Re⟪x, ∑ h i x⟫ ≥ |s| μ ‖x‖²`. -/
theorem second_quantized_edge_unbounded {ι : Type*} (s : Finset ι) (h : ι → E →ₗ.[ℂ] E) (μ : ℝ)
    (hh : ∀ i ∈ s, ∀ y : (h i).domain, μ * ‖(y : E)‖ ^ 2 ≤ RCLike.re ⟪(y : E), h i y⟫_ℂ)
    (x : E) (hx : ∀ i, x ∈ (h i).domain) :
    (s.card * μ) * ‖x‖ ^ 2 ≤ RCLike.re ⟪x, ∑ i ∈ s, h i ⟨x, hx i⟩⟫_ℂ := by
  rw [inner_sum, map_sum]
  calc (s.card * μ) * ‖x‖ ^ 2 = ∑ i ∈ s, μ * ‖x‖ ^ 2 := by
        rw [Finset.sum_const, nsmul_eq_mul]; ring
    _ ≤ _ := Finset.sum_le_sum fun i hi => hh i hi ⟨x, hx i⟩

end CftCheck
