import Mathlib
import BookProof.OSReconstruction.FockIntertwining

/-!
# Chapter BridgeGapInvariance — H7/C8, the gap transported by the cyclic unitary

An `OsFockBridge` is an isometry intertwining the OS transfer semigroup with the physical
one.  This module proves that an exponential contraction estimate toward a fixed point — the
quantitative form of a spectral gap — transfers unchanged between the two presentations.  It is
the contract C7/C8 needs to identify the continuum generator without changing the gap.

No continuum limit, cutoff removal or positive gap of the physical theory is claimed.
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

end BookProof.BridgeGapInvariance
