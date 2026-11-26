import Mathlib
import BookProof.ChapterSmHiggsVacuum

/-!
# Chapter ShiftedVacuumEquivalence — H6 Route A, finite-volume shift

`cftproof.md` H6 Route A shifts the field to a vacuum `φ = v + h` and requires that the
fluctuation `h` sees strictly positive radial curvature and zero Goldstone curvature at
`v`.  This module proves exactly that finite-volume algebraic input from the existing Higgs
lemmas: at a vacuum `v`, the potential is at its minimum, the radial second-order coefficient
is strictly positive (`μ²‖v‖² > 0`), and a transverse shift has no quadratic term.

The field redefinition at the level of the full Mehler/SIRK Hamiltonian and the infinite-volume
sector inequivalence are separate work.
-/

set_option maxHeartbeats 400000

noncomputable section

namespace BookProof.ShiftedVacuumEquivalence

open BookProof.SmHiggsVacuum

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
omit [InnerProductSpace ℝ E] in

/-- At a vacuum the radial curvature `μ²‖v‖²` is strictly positive when `μ² > 0` and `v ≠ 0`. -/
theorem radial_curvature_pos {lam mu2 : ℝ} {v : E} (hlam : 0 < lam) (hmu : 0 < mu2)
    (hv : lam * ‖v‖ ^ 2 = mu2) : 0 < mu2 * ‖v‖ ^ 2 := by
  have hvpos : 0 < ‖v‖ ^ 2 := by nlinarith [norm_nonneg v]
  exact mul_pos hmu hvpos

omit [InnerProductSpace ℝ E] in
/-- The shifted vacuum is a minimum: `h = 0` is the ground of the fluctuation potential. -/
theorem shifted_vacuum_min {lam mu2 : ℝ} (hlam : 0 < lam) {v : E}
    (hv : lam * ‖v‖ ^ 2 = mu2) :
    higgsV lam mu2 v = -(mu2 ^ 2 / (4 * lam)) := by
  apply (higgsV_eq_min_iff hlam v).2
  have hlam0 : lam ≠ 0 := ne_of_gt hlam
  rw [eq_div_iff hlam0]
  simpa [mul_comm] using hv

/-- Along a Goldstone direction the fluctuation potential has no quadratic term. -/
theorem goldstone_no_quadratic {lam mu2 : ℝ} {v w : E} (hv : lam * ‖v‖ ^ 2 = mu2)
    (hperp : (inner ℝ v w : ℝ) = 0) (t : ℝ) :
    higgsV lam mu2 (v + t • w) = higgsV lam mu2 v +
      (lam / 4) * t ^ 4 * ‖w‖ ^ 4 := by
  exact higgs_goldstone hv hperp t

end BookProof.ShiftedVacuumEquivalence
