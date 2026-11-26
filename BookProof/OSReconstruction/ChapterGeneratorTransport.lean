import Mathlib
import BookProof.OSReconstruction.FockIntertwining

/-!
# Chapter GeneratorTransport — H7/C7, generators agree under the OS bridge

An `OsFockBridge` intertwines two strongly continuous contraction flows for `τ ≥ 0`.  At a
vector where the right derivative at `0` exists, the generator on the OS side is carried by the
bridge to the generator on the physical side.  This is the operator-level identification C7
needs, complementing the gap transport in `ChapterBridgeGapInvariance`.
-/

set_option maxHeartbeats 400000

noncomputable section

namespace BookProof.GeneratorTransport

open Filter Topology
open BookProof.OSReconstruction

variable {Λ : OSState} {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {P : ℝ → Hphys Λ →L[ℝ] Hphys Λ} {Q : ℝ → F →L[ℝ] F}

/-- The image under the bridge of a right derivative of the OS orbit is a right derivative of
    the physical orbit. -/
theorem generator_image {B : OsFockBridge F P Q} {x : Hphys Λ} {g : Hphys Λ}
    (hx : HasDerivWithinAt (fun t : ℝ => P t x) g (Set.Ici 0) 0) :
    HasDerivWithinAt (fun t : ℝ => Q t (B.U x)) (B.U g) (Set.Ici 0) 0 := by
  have hcomp := HasFDerivAt.comp_hasDerivWithinAt 0
    (B.U.toContinuousLinearMap.hasFDerivAt (x := (P 0) x)) hx
  have heq : (fun t : ℝ => Q t (B.U x)) =ᶠ[𝓝[Set.Ici (0 : ℝ)] 0]
      fun t : ℝ => B.U (P t x) := by
    filter_upwards [self_mem_nhdsWithin] with t ht
    exact (B.intertwines t ht x).symm
  have h0 : Q 0 (B.U x) = B.U (P 0 x) := (B.intertwines 0 le_rfl x).symm
  exact hcomp.congr_of_eventuallyEq heq h0

/-- Uniqueness of the right derivative on `Ici 0`: the two candidate generator values agree. -/
theorem generator_eq {x : Hphys Λ} {g h : Hphys Λ}
    (hg : HasDerivWithinAt (fun t : ℝ => P t x) g (Set.Ici 0) 0)
    (hh : HasDerivWithinAt (fun t : ℝ => P t x) h (Set.Ici 0) 0) : g = h := by
  exact UniqueDiffWithinAt.eq_deriv (Set.Ici 0) (uniqueDiffWithinAt_Ici 0) hg hh

/-- The transported generator value is unique. -/
theorem generator_image_unique {B : OsFockBridge F P Q} {x : Hphys Λ} {g : Hphys Λ}
    (hx : HasDerivWithinAt (fun t : ℝ => P t x) g (Set.Ici 0) 0) {y : F}
    (hy : HasDerivWithinAt (fun t : ℝ => Q t (B.U x)) y (Set.Ici 0) 0) : B.U g = y := by
  exact UniqueDiffWithinAt.eq_deriv (Set.Ici 0) (uniqueDiffWithinAt_Ici 0)
    (generator_image (B := B) hx) hy

end BookProof.GeneratorTransport
