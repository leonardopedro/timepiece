import Mathlib
import BookProof.Attention.ChapterCoherentOverlap
import BookProof.Attention.ChapterCoherentGeometry

/-!
# Chapter OverlapCollapse — H5's infinite-volume overlap bound

The coherent overlap kernel is `exp(−‖q−k‖²/2)`.  For a spatially constant field shift `v`
across `N` modes the squared distance is `N·v²`, so the overlap of the unshifted reference with
the shifted one is `exp(−N·v²/2)`, which tends to zero as `N → ∞` whenever `v ≠ 0`.  This is the
Kakutani-orthogonality bound H5 asks for, at the Gaussian/coherent-state level; the lift to the
physical Higgs/φ⁴ ground states and the symmetric-average/tachyonic failure modes are separate
work.
-/

set_option maxHeartbeats 400000

noncomputable section

namespace BookProof.OverlapCollapse

open Filter Topology
open BookProof.ChapterCoherentOverlap
open BookProof.ChapterCoherentGeometry

/-- The overlap between the zero configuration and the constant shift `v` on `N` modes. -/
theorem coherentOverlap_zero_const (N : ℕ) (v : ℝ) :
    coherentOverlap (0 : EuclideanSpace ℝ (Fin N))
      (WithLp.toLp 2 (fun _ : Fin N => v) : EuclideanSpace ℝ (Fin N)) =
      Real.exp (-(N : ℝ) * v ^ 2 / 2) := by
  rw [coherentOverlap_eq_gaussian]
  congr 1
  have hnorm :
      ‖(0 : EuclideanSpace ℝ (Fin N)) -
        (WithLp.toLp 2 (fun _ : Fin N => v) : EuclideanSpace ℝ (Fin N))‖ ^ 2 =
        (N : ℝ) * v ^ 2 := by
    simp [EuclideanSpace.norm_eq, mul_pow, Real.sq_sqrt, Real.norm_eq_abs, sq_abs,
      Real.sqrt_sq_eq_abs]
  rw [hnorm]
  ring

/-- The overlap collapses to zero in the infinite-volume limit for any nonzero shift. -/
theorem coherentOverlap_const_tendsto_zero {v : ℝ} (hv : v ≠ 0) :
    Tendsto (fun N : ℕ => coherentOverlap (0 : EuclideanSpace ℝ (Fin N))
      (WithLp.toLp 2 (fun _ : Fin N => v) : EuclideanSpace ℝ (Fin N))) atTop (𝓝 0) := by
  simp_rw [coherentOverlap_zero_const]
  have hvpos : 0 < v ^ 2 := sq_pos_of_ne_zero hv
  have hlin : Tendsto (fun N : ℕ => -(↑N * v ^ 2 / 2)) atTop atBot := by
    have hmul : Tendsto (fun N : ℕ => (N : ℝ) * (v ^ 2 / 2)) atTop atTop :=
      tendsto_natCast_atTop_atTop.atTop_mul_const (by positivity)
    have hmul' : Tendsto (fun N : ℕ => (N : ℝ) * v ^ 2 / 2) atTop atTop := by
      convert hmul using 1
      funext N
      ring
    simpa only [Function.comp_apply, neg_mul, one_div] using
      (tendsto_neg_atTop_atBot.comp hmul')
  have hlin'' : Tendsto (fun N : ℕ => -↑N * v ^ 2 / 2) atTop atBot := by
    convert hlin using 1
    funext N
    ring
  simpa only [Function.comp_apply] using (Real.tendsto_exp_atBot.comp hlin'')

end BookProof.OverlapCollapse
