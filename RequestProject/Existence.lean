import RequestProject.UnboundedPhysics
import RequestProject.SelfAdjointResolvent

/-!
# Existence of the Euclidean dynamics for unbounded Hamiltonians

Summary theorems for claims A and B, stated for self-adjoint (in Mathlib's `LinearPMap` sense)
unbounded operators. They package the construction of `exp(-τH)` from `HeatSemigroup.lean`, the
resolvent existence from `SelfAdjointResolvent.lean` and the estimates from
`UnboundedPhysics.lean`.
-/

open scoped InnerProductSpace

noncomputable section

namespace CftCheck

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- **Existence and uniqueness of the Euclidean evolution of a self-adjoint Hamiltonian bounded
below.** If `H† = H` and `Re⟪x, Hx⟫ ≥ m‖x‖²`, there is a family of bounded self-adjoint
operators `T τ` (`τ ≥ 0`, this is `exp(-τH)`) with `T 0 = 1`, `T (s + t) = T s T t`,
`‖T τ‖ ≤ e^{-mτ}`, `τ ↦ T τ x` continuous, such that for `x` in the domain `τ ↦ T τ x` solves
`dψ/dτ = -Hψ`, and every solution of `dψ/dτ = -Hψ` is of this form. -/
theorem euclidean_evolution_exists {H : E →ₗ.[ℂ] E} (hH : IsSelfAdjoint H) {m : ℝ}
    (hlow : ∀ x : H.domain, m * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪(x : E), H x⟫_ℂ) :
    ∃ T : ℝ → E →L[ℂ] E,
      T 0 = 1 ∧
      (∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = T s * T t) ∧
      (∀ τ, IsSelfAdjoint (T τ)) ∧
      (∀ τ, 0 ≤ τ → ‖T τ‖ ≤ Real.exp (-(τ * m))) ∧
      (∀ x : E, ContinuousOn (fun τ => T τ x) (Set.Ici 0)) ∧
      (∀ x : H.domain, IsHeatSolution H (fun τ => T τ x)) ∧
      (∀ ψ : ℝ → E, IsHeatSolution H ψ → ∀ τ, 0 ≤ τ → ψ τ = T τ (ψ 0)) := by
  obtain ⟨R, hR⟩ := IsSelfAdjoint.exists_isSemibounded hH hlow (sub_one_lt m)
  exact ⟨heatSG (m - 1) R, heatSG_zero _ _, fun s t hs ht => heatSG_add hs ht,
    isSelfAdjoint_heatSG _ _, fun τ hτ => norm_heatSG_le hR hτ, continuousOn_heatSG hR,
    heatSG_isHeatSolution hR, fun ψ hψ τ hτ => hψ.eq_heatSG hR hτ⟩

/-- **Claim A, Euclidean form, for an unbounded self-adjoint Hamiltonian.** Let `H† = H`,
`H ≥ 0`, `HΩ = 0`. Then the transfer operator `T τ = exp(-τH)` exists, fixes `Ω`, and:
* a spectral gap `Re⟪x, Hx⟫ ≥ g‖x‖²` on `D(H) ∩ Ω^⊥` gives `‖T τ x‖ ≤ e^{-gτ}‖x‖` on `Ω^⊥`;
* conversely, such a decay at one `τ > 0` forces every eigenvalue with eigenvector `⊥ Ω` to be
  `≥ g`.
So exponential decay of the transfer matrix and the Hamiltonian gap are the same input. -/
theorem transfer_decay_iff_gap {H : E →ₗ.[ℂ] E} (hH : IsSelfAdjoint H)
    (hpos : ∀ x : H.domain, 0 ≤ RCLike.re ⟪(x : E), H x⟫_ℂ) (Ω : H.domain) (hHΩ : H Ω = 0) :
    ∃ T : ℝ → E →L[ℂ] E,
      (∀ ψ : ℝ → E, IsHeatSolution H ψ → ∀ τ, 0 ≤ τ → ψ τ = T τ (ψ 0)) ∧
      (∀ τ, 0 ≤ τ → T τ Ω = Ω) ∧
      (∀ g : ℝ, (∀ x : H.domain, ⟪(Ω : E), (x : E)⟫_ℂ = 0 →
          g * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪(x : E), H x⟫_ℂ) →
        ∀ τ, 0 ≤ τ → ∀ x : E, ⟪(Ω : E), x⟫_ℂ = 0 → ‖T τ x‖ ≤ Real.exp (-(g * τ)) * ‖x‖) ∧
      (∀ g τ : ℝ, 0 < τ →
        (∀ x : E, ⟪(Ω : E), x⟫_ℂ = 0 → ‖T τ x‖ ≤ Real.exp (-(g * τ)) * ‖x‖) →
        ∀ (v : H.domain), (v : E) ≠ 0 → ⟪(Ω : E), (v : E)⟫_ℂ = 0 →
          ∀ e : ℝ, H v = (e : ℂ) • (v : E) → g ≤ e) := by
  have hlow : ∀ x : H.domain, 0 * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪(x : E), H x⟫_ℂ := by
    intro x; rw [zero_mul]; exact hpos x
  obtain ⟨R, hR⟩ := IsSelfAdjoint.exists_isSemibounded hH hlow (by norm_num : (-1 : ℝ) < 0)
  refine ⟨heatSG (-1) R, fun ψ hψ τ hτ => hψ.eq_heatSG hR hτ, fun τ hτ => ?_,
    fun g hg τ hτ x hx => heatSG_contraction_orth hR Ω hHΩ g hg hτ x hx,
    fun g τ hτ hdec v hv hvΩ e hev => gap_of_heatSG_decay hR Ω g hτ hdec v hv hvΩ e hev⟩
  simpa using heatSG_eigen hR Ω 0 (by simp [hHΩ]) hτ

/-- **Claim B: the artificial-gap theory exists for unbounded `H` and `N`.** Let `H ≥ 0`,
`N ≥ 0`, `N ≥ 1` on `Ω^⊥`, `HΩ = NΩ = 0`, `μ ≥ 0`, and let `Hμ` be a self-adjoint operator
with domain `D(H) ∩ D(N)` that equals `H + μN` there. Then the Euclidean evolution
`T τ = exp(-τHμ)` exists: it is a semigroup of self-adjoint contractions, every solution of
`dψ/dτ = -Hμψ` is `T τ ψ(0)` and the solutions exist for every initial value in the domain, `T τ`
fixes the vacuum `Ω`, and `‖T τ x‖ ≤ e^{-μτ}‖x‖` on `Ω^⊥`. -/
theorem artificial_gap_theory_exists (H N Hμ : E →ₗ.[ℂ] E) (μ : ℝ) (hμ : 0 ≤ μ)
    (hdom : ∀ y : E, y ∈ H.domain → y ∈ N.domain → y ∈ Hμ.domain)
    (hdom' : ∀ y : E, y ∈ Hμ.domain → y ∈ H.domain ∧ y ∈ N.domain)
    (hsum : ∀ (y : E) (hH : y ∈ H.domain) (hN : y ∈ N.domain),
      Hμ ⟨y, hdom y hH hN⟩ = H ⟨y, hH⟩ + (μ : ℂ) • N ⟨y, hN⟩)
    (hsa : IsSelfAdjoint Hμ) (Ω : E)
    (hΩH : Ω ∈ H.domain) (hΩN : Ω ∈ N.domain) (hHΩ : H ⟨Ω, hΩH⟩ = 0) (hNΩ : N ⟨Ω, hΩN⟩ = 0)
    (hH0 : ∀ x : H.domain, 0 ≤ RCLike.re ⟪(x : E), H x⟫_ℂ)
    (hN0 : ∀ x : N.domain, 0 ≤ RCLike.re ⟪(x : E), N x⟫_ℂ)
    (hN1 : ∀ x : N.domain, ⟪Ω, (x : E)⟫_ℂ = 0 → ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪(x : E), N x⟫_ℂ) :
    ∃ T : ℝ → E →L[ℂ] E,
      T 0 = 1 ∧
      (∀ s t, 0 ≤ s → 0 ≤ t → T (s + t) = T s * T t) ∧
      (∀ τ, IsSelfAdjoint (T τ)) ∧
      (∀ τ, 0 ≤ τ → ‖T τ‖ ≤ 1) ∧
      (∀ x : Hμ.domain, IsHeatSolution Hμ (fun τ => T τ x)) ∧
      (∀ ψ : ℝ → E, IsHeatSolution Hμ ψ → ∀ τ, 0 ≤ τ → ψ τ = T τ (ψ 0)) ∧
      (∀ τ, 0 ≤ τ → T τ Ω = Ω) ∧
      (∀ τ, 0 ≤ τ → ∀ x : E, ⟪Ω, x⟫_ℂ = 0 → ‖T τ x‖ ≤ Real.exp (-(μ * τ)) * ‖x‖) := by
  have hlow : ∀ x : Hμ.domain, 0 * ‖(x : E)‖ ^ 2 ≤ RCLike.re ⟪(x : E), Hμ x⟫_ℂ := by
    intro x
    obtain ⟨hxH, hxN⟩ := hdom' x x.2
    have e : x = ⟨(x : E), hdom x hxH hxN⟩ := rfl
    rw [zero_mul, e, hsum _ hxH hxN, inner_add_right, inner_smul_right, map_add]
    have h1 := hH0 ⟨x, hxH⟩
    have h2 := hN0 ⟨x, hxN⟩
    simp only at h1 h2
    have : RCLike.re ((μ : ℂ) * ⟪(x : E), N ⟨x, hxN⟩⟫_ℂ) = μ * RCLike.re ⟪(x : E), N ⟨x, hxN⟩⟫_ℂ := by
      simp
    rw [this]; positivity
  obtain ⟨R, hR⟩ := IsSelfAdjoint.exists_isSemibounded hsa hlow (by norm_num : (-1 : ℝ) < 0)
  refine ⟨heatSG (-1) R, heatSG_zero _ _, fun s t hs ht => heatSG_add hs ht,
    isSelfAdjoint_heatSG _ _, fun τ hτ => by simpa using norm_heatSG_le hR hτ,
    heatSG_isHeatSolution hR, fun ψ hψ τ hτ => hψ.eq_heatSG hR hτ,
    fun τ hτ => (shifted_heat_contraction H N Hμ μ hμ hdom hdom' hsum hR Ω hΩH hΩN hHΩ hNΩ hH0
      hN1 hτ).1,
    fun τ hτ => (shifted_heat_contraction H N Hμ μ hμ hdom hdom' hsum hR Ω hΩH hΩN hHΩ hNΩ hH0
      hN1 hτ).2⟩

end CftCheck
