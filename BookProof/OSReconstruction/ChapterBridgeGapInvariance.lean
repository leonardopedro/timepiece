import Mathlib
import BookProof.OSReconstruction.FockIntertwining

/-!
# Chapter BridgeGapInvariance — H7/C8, the gap transported by the cyclic unitary

An `OsFockBridge` is an isometry intertwining the OS transfer semigroup with the physical
one. A fixed-vector contraction estimate transfers unchanged between the two presentations.
Testing the zero vector shows how restrictive that estimate is for a linear flow.

For a linear heat flow with ground degeneracy the relevant observable is the
operator norm of the heat operator minus the full stationary projection. The final
two lemmas identify that projection and preserve its exact error at every time.
-/

set_option maxHeartbeats 400000

noncomputable section

namespace BookProof.BridgeGapInvariance

open Filter Topology
open BookProof.OSReconstruction

variable {Λ : OSState} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]

/-- Exponential contraction of a one-parameter contraction family toward a fixed point. -/
def FlowGap (P : ℝ → Hphys Λ →L[ℝ] Hphys Λ) (x : Hphys Λ) (m C : ℝ) : Prop :=
  ∀ τ : ℝ, 0 ≤ τ → ∀ y : Hphys Λ,
    ‖P τ y - x‖ ≤ C * Real.exp (-m * τ) * ‖y - x‖

/-- The same estimate on the physical side. -/
def FlowGapOn (Q : ℝ → F →L[ℝ] F) (z : F) (m C : ℝ) : Prop :=
  ∀ τ : ℝ, 0 ≤ τ → ∀ y : F,
    ‖Q τ y - z‖ ≤ C * Real.exp (-m * τ) * ‖y - z‖

/-- The flow gap is invariant under the cyclic unitary bridge. -/
theorem flowGap_bridge_iff (B : OsFockBridge F P Q) {x : Hphys Λ} {m C : ℝ} :
    FlowGap P x m C ↔ FlowGapOn Q (B.U x) m C := by
  constructor
  · intro h τ hτ y
    have hpre := h τ hτ (B.toIsometryEquiv.symm y)
    have hq : Q τ y = B.U (B.toIsometryEquiv.symm (Q τ y)) := by simp
    have hi : B.toIsometryEquiv.symm (Q τ y) = (P τ) (B.toIsometryEquiv.symm y) :=
      B.intertwines_symm hτ y
    have hdiff : Q τ y - B.U x = B.U ((P τ) (B.toIsometryEquiv.symm y) - x) := by
      rw [hq, hi, B.U.map_sub]
    rw [hdiff, B.U.norm_map]
    have hnorm : ‖y - B.U x‖ = ‖B.toIsometryEquiv.symm y - x‖ := by
      rw [← show B.U (B.toIsometryEquiv.symm y - x) = y - B.U x by simp]
      exact B.U.norm_map _
    rw [hnorm]
    exact hpre
  · intro h τ hτ y
    have hpre := h τ hτ (B.U y)
    have hi : B.U ((P τ) y) = Q τ (B.U y) := B.intertwines τ hτ y
    have hnorm : ‖B.U y - B.U x‖ = ‖y - x‖ := by
      rw [← B.U.map_sub]
      exact B.U.norm_map _
    have hleft : ‖Q τ (B.U y) - B.U x‖ = ‖(P τ) y - x‖ := by
      rw [← hi, ← B.U.map_sub, B.U.norm_map]
    rw [hnorm] at hpre
    rw [hleft] at hpre
    exact hpre

/-- A strict contraction toward a single vector, tested on the zero input, forces
the proposed vector to vanish. This matters for a heat flow fixing a vacuum. -/
theorem fixed_vector_estimate_forces_zero {P : ℝ → Hphys Λ →L[ℝ] Hphys Λ}
    {x : Hphys Λ} {m C t : ℝ} (h : FlowGap P x m C) (ht : 0 ≤ t)
    (hstrict : C * Real.exp (-m * t) < 1) : x = 0 := by
  have hzero := h t ht 0
  simp only [map_zero, zero_sub, norm_neg] at hzero
  by_contra hx
  nlinarith [mul_pos (sub_pos.mpr hstrict) (norm_pos_iff.mpr hx)]

/-- If membership in each candidate ground space means stationarity for every
positive time, the bridge carries the entire subspace across, including multiplicities. -/
theorem map_stationary_space (B : OsFockBridge F P Q)
    (G : Submodule ℝ (Hphys Λ)) (J : Submodule ℝ F)
    (hG : ∀ x, x ∈ G ↔ ∀ t : ℝ, 0 ≤ t → P t x = x)
    (hJ : ∀ y, y ∈ J ↔ ∀ t : ℝ, 0 ≤ t → Q t y = y) :
    G.map B.U.toLinearMap = J := by
  ext y
  obtain ⟨x, rfl⟩ := B.surjective y
  constructor
  · rintro ⟨z, hz, he⟩
    have hzx : z = x := B.injective he
    subst z
    exact (hJ _).2 fun t ht => (B.fixed_iff ht x).1 ((hG _).1 hz t ht)
  · intro hy
    exact ⟨x, (hG _).2 (fun t ht => (B.fixed_iff ht x).2 ((hJ _).1 hy t ht)), rfl⟩

/-- Exact whole-space heat error under the bridge, for any transported closed
subspace. Taking G and J to be the stationary spaces gives the gap test. -/
theorem ground_projection_error_eq (B : OsFockBridge F P Q)
    (G : Submodule ℝ (Hphys Λ)) (J : Submodule ℝ F)
    [G.HasOrthogonalProjection] [J.HasOrthogonalProjection]
    (hmap : G.map B.U.toLinearMap = J) (t : ℝ) (ht : 0 ≤ t) :
    ‖P t - G.starProjection‖ = ‖Q t - J.starProjection‖ := by
  subst J
  have h (x : Hphys Λ) :
      ‖(Q t - (G.map B.U.toLinearMap).starProjection) (B.U x)‖ =
        ‖(P t - G.starProjection) x‖ := by
    simp only [ContinuousLinearMap.sub_apply, ← B.intertwines t ht,
      ← B.U.map_starProjection G x, ← B.U.map_sub, B.U.norm_map]
  apply le_antisymm
  · apply ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _)
    intro x
    rw [← h x, ← B.U.norm_map x]
    exact ContinuousLinearMap.le_opNorm _ _
  · refine (Q t - (G.map B.U.toLinearMap).starProjection).opNorm_le_bound
      (norm_nonneg (P t - G.starProjection)) ?_
    intro y
    obtain ⟨x, rfl⟩ := B.surjective y
    rw [h, B.U.norm_map]
    exact ContinuousLinearMap.le_opNorm _ _

end BookProof.BridgeGapInvariance
