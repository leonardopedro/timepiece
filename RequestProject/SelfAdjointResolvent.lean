module

public import RequestProject.HeatSemigroup

/-!
# Self-adjoint operators bounded below have a shift-invert operator

For a self-adjoint (in the sense of Mathlib's `LinearPMap` adjoint, `LinearPMap.adjoint H = H`) operator `H` with
`Re⟪x, Hx⟫ ≥ m‖x‖²`, the operator `H - σ` is a bijection from the domain of `H` onto the whole
space for every `σ < m`, with bounded inverse. So such an `H` satisfies `IsSemibounded`, and all
the results about `exp(-τH)` in `HeatSemigroup.lean` apply to it.
-/

@[expose] public section

open scoped InnerProductSpace

noncomputable section

namespace CftCheck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Range criterion.** A closed symmetric operator `H` bounded below by `m`, such that no
nonzero vector is orthogonal to the range of `H - σ` (for some `σ < m`), has a bounded
shift-invert operator at `σ`. -/
theorem exists_isSemibounded_of_closed {H : E →ₗ.[ℂ] E} {m σ : ℝ}
    (hsymm : ∀ x y : H.domain, ⟪H x, (y : E)⟫_ℂ = ⟪(x : E), H y⟫_ℂ)
    (hlow : ∀ x : H.domain, m * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪(x : E), H x⟫_ℂ)
    (hclosed : H.IsClosed) (hσ : σ < m)
    (hdef : ∀ z : E, (∀ x : H.domain, ⟪z, H x - (σ : ℂ) • (x : E)⟫_ℂ = 0) → z = 0) :
    ∃ R : E →L[ℂ] E, IsSemibounded H m σ R := by
  have hpos : 0 < m - σ := sub_pos.mpr hσ
  -- the operator `B = H - σ` on the domain
  let B : H.domain →ₗ[ℂ] E := H.toFun - (σ : ℂ) • H.domain.subtype
  have hB : ∀ x : H.domain, B x = H x - (σ : ℂ) • (x : E) := fun x => rfl
  have hbound : ∀ x : H.domain, (m - σ) * ‖(x : E)‖ ≤ ‖B x‖ := by
    intro x
    have h1 := hlow x
    have h2 : RCLike.re ⟪(x : E), B x⟫_ℂ ≤ ‖(x : E)‖ * ‖B x‖ :=
      (RCLike.re_le_norm _).trans (norm_inner_le_norm _ _)
    have h3 : RCLike.re ⟪(x : E), B x⟫_ℂ = RCLike.re ⟪(x : E), H x⟫_ℂ - σ * ‖(x : E)‖ ^ 2 := by
      rw [hB, inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K, map_sub]
      simp only [RCLike.re_to_complex]
      have h4 : ((σ : ℂ) * ((‖(x : E)‖ : ℂ) ^ 2)).re = σ * ‖(x : E)‖ ^ 2 := by
        rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
      erw [h4]
    rcases (norm_nonneg (x : E)).eq_or_lt with h0 | h0
    · rw [← h0, mul_zero]; exact norm_nonneg _
    · nlinarith
  have hinj : Function.Injective B := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro x hx
    have := hbound x
    rw [hx, norm_zero] at this
    have : ‖(x : E)‖ = 0 := le_antisymm (by nlinarith [norm_nonneg (x : E)]) (norm_nonneg _)
    exact Subtype.ext (norm_eq_zero.mp this)
  -- the range of `B` is closed
  have hclosedRange : IsClosed (LinearMap.range B : Set E) := by
    rw [← closure_subset_iff_isClosed]
    intro y hy
    obtain ⟨u, hu, hlim⟩ := mem_closure_iff_seq_limit.mp hy
    choose x hx using hu
    have hBx : ∀ n, B (x n) = u n := hx
    have hcB := hlim.cauchySeq
    have hcx : CauchySeq (fun n => (x n : E)) := by
      rw [Metric.cauchySeq_iff] at hcB ⊢
      intro ε hε
      obtain ⟨N, hN⟩ := hcB (ε * (m - σ)) (by positivity)
      refine ⟨N, fun p hp q hq => ?_⟩
      have h := hN p hp q hq
      rw [dist_eq_norm, ← hBx, ← hBx, ← map_sub] at h
      have := hbound (x p - x q)
      rw [dist_eq_norm]
      simp only [Submodule.coe_sub] at this
      by_contra hc
      push Not at hc
      nlinarith
    obtain ⟨x₀, hx₀⟩ := cauchySeq_tendsto_of_complete hcx
    have hAx : Filter.Tendsto (fun n => H (x n)) Filter.atTop (nhds (y + (σ : ℂ) • x₀)) := by
      have : ∀ n, H (x n) = u n + (σ : ℂ) • (x n : E) := fun n => by
        rw [← hBx, hB]; abel
      simp_rw [this]
      exact hlim.add (hx₀.const_smul _)
    have hgraph : (x₀, y + (σ : ℂ) • x₀) ∈ H.graph :=
      hclosed.mem_of_tendsto (hx₀.prodMk_nhds hAx)
        (Filter.Eventually.of_forall fun n => H.mem_graph (x n))
    obtain ⟨w, hw1, hw2⟩ := (H.mem_graph_iff).mp hgraph
    refine ⟨w, ?_⟩
    simp only at hw1 hw2
    rw [hB, hw2, hw1]; abel
  -- the range of `B` is dense
  have hdense : (LinearMap.range B)ᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro z hz
    refine hdef z (fun x => ?_)
    have := (Submodule.mem_orthogonal _ _).mp hz (B x) ⟨x, rfl⟩
    rw [← inner_conj_symm, ← hB, this, map_zero]
  have hsurj : Function.Surjective B := by
    have h1 := (Submodule.topologicalClosure_eq_top_iff).mpr hdense
    rw [IsClosed.submodule_topologicalClosure_eq hclosedRange] at h1
    exact LinearMap.range_eq_top.mp h1
  -- the inverse
  let e : H.domain ≃ₗ[ℂ] E := LinearEquiv.ofBijective B ⟨hinj, hsurj⟩
  have he : ∀ x, e x = B x := fun x => rfl
  let R₀ : E →ₗ[ℂ] E := H.domain.subtype ∘ₗ e.symm.toLinearMap
  have hR₀ : ∀ y, ‖R₀ y‖ ≤ (m - σ)⁻¹ * ‖y‖ := by
    intro y
    have h := hbound (e.symm y)
    rw [← he, LinearEquiv.apply_symm_apply] at h
    rw [inv_mul_eq_div, le_div_iff₀ hpos, mul_comm]
    exact h
  let R : E →L[ℂ] E := R₀.mkContinuous ((m - σ)⁻¹) hR₀
  have hRy : ∀ y, R y = (e.symm y : E) := fun y => rfl
  refine ⟨R, hsymm, hlow, hσ, ⟨fun y => (e.symm y).2, fun y => ?_, fun y => ?_⟩⟩
  · have h := LinearEquiv.apply_symm_apply e y
    rw [he, hB] at h
    exact h
  · have h := LinearEquiv.symm_apply_apply e y
    rw [hRy, ← hB, ← he, h]

/-- **Self-adjoint operators bounded below are semibounded.** If `LinearPMap.adjoint H = H` and
`Re⟪x, Hx⟫ ≥ m‖x‖²` on the domain, then for every `σ < m` there is a bounded shift-invert
operator `R = (H - σ)⁻¹`, so `H` satisfies `IsSemibounded H m σ R`. -/
theorem IsSelfAdjoint.exists_isSemibounded {H : E →ₗ.[ℂ] E} (hH : IsSelfAdjoint H) {m : ℝ}
    (hlow : ∀ x : H.domain, m * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪(x : E), H x⟫_ℂ) {σ : ℝ}
    (hσ : σ < m) : ∃ R : E →L[ℂ] E, IsSemibounded H m σ R := by
  have hdense := hH.dense_domain
  have hadj : LinearPMap.adjoint H = H := hH
  have hformal := LinearPMap.adjoint_isFormalAdjoint hdense
  rw [hadj] at hformal
  refine exists_isSemibounded_of_closed (fun x y => hformal x y) hlow hH.isClosed hσ ?_
  intro z hz
  have hzdom : z ∈ (LinearPMap.adjoint H).domain := by
    refine LinearPMap.mem_adjoint_domain_of_exists z ⟨(σ : ℂ) • z, fun x => ?_⟩
    have := hz x
    rw [inner_sub_right, inner_smul_right, sub_eq_zero] at this
    rw [inner_smul_left, Complex.conj_ofReal, this]
  have happ : LinearPMap.adjoint H ⟨z, hzdom⟩ = (σ : ℂ) • z := by
    refine LinearPMap.adjoint_apply_eq hdense _ (fun x => ?_)
    have := hz x
    rw [inner_sub_right, inner_smul_right, sub_eq_zero] at this
    rw [inner_smul_left, Complex.conj_ofReal, this]
  have key : ∃ hz : z ∈ H.domain, H ⟨z, hz⟩ = (σ : ℂ) • z := by
    rw [← hadj]; exact ⟨hzdom, happ⟩
  obtain ⟨hz, hHz⟩ := key
  have h := hlow ⟨z, hz⟩
  simp only at h
  rw [hHz, inner_smul_right, inner_self_eq_norm_sq_to_K] at h
  have h4 : RCLike.re ((σ : ℂ) * ((‖z‖ : ℂ) ^ 2)) = σ * ‖z‖ ^ 2 := by
    simp only [RCLike.re_to_complex]
    rw [← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re]
  erw [h4] at h
  have : ‖z‖ ^ 2 = 0 := by nlinarith [sq_nonneg ‖z‖]
  simpa using this

omit [CompleteSpace E] in
/-- The lower bound `Re⟪x, Hx⟫ ≥ m‖x‖²` passes to the closure of `H`. -/
theorem lower_bound_closure {H : E →ₗ.[ℂ] E} {m : ℝ}
    (hlow : ∀ x : H.domain, m * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪(x : E), H x⟫_ℂ)
    (x : H.closure.domain) : m * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪(x : E), H.closure x⟫_ℂ := by
  by_cases hcl : H.IsClosable
  · let S : Set (E × E) := {p | m * ‖p.1‖ ^ 2 ≤ RCLike.re ⟪p.1, p.2⟫_ℂ}
    have hS : IsClosed S := isClosed_le (by fun_prop) (by fun_prop)
    have hgS : (H.graph : Set (E × E)) ⊆ S := by
      rintro ⟨a, b⟩ hab
      obtain ⟨y, hy1, hy2⟩ := (H.mem_graph_iff).mp hab
      simp only at hy1 hy2
      show m * ‖a‖ ^ 2 ≤ RCLike.re ⟪a, b⟫_ℂ
      rw [← hy1, ← hy2]; exact hlow y
    have hmem : ((x : E), H.closure x) ∈ (H.graph.topologicalClosure : Set (E × E)) := by
      rw [hcl.graph_closure_eq_closure_graph]; exact H.closure.mem_graph x
    rw [Submodule.topologicalClosure_coe] at hmem
    exact closure_minimal hgS hS hmem
  · have h := LinearPMap.closure_def' hcl
    revert x
    rw [h]
    exact hlow

/-- **Essentially self-adjoint operators bounded below.** If `H` is bounded below by `m` and
essentially self-adjoint (its closure is self-adjoint), then its closure has a bounded
shift-invert operator at every `σ < m`; so `exp(-τ H̄)` is defined and all results of
`HeatSemigroup.lean` apply to it. -/
theorem exists_isSemibounded_closure {H : E →ₗ.[ℂ] E} {m : ℝ}
    (hlow : ∀ x : H.domain, m * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪(x : E), H x⟫_ℂ)
    (hesa : IsSelfAdjoint H.closure) {σ : ℝ} (hσ : σ < m) :
    ∃ R : E →L[ℂ] E, IsSemibounded H.closure m σ R :=
  IsSelfAdjoint.exists_isSemibounded hesa (lower_bound_closure hlow) hσ

end CftCheck
