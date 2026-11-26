import Mathlib
import BookProof.OSReconstruction.ChapterStrangPotentialWeight

/-!
# Chapter ContinuousTimeWeight — the Strang factor at fixed total time

For the time schedule `ε = T/N`, the Strang weight of a constant potential is exactly
`exp(−(T·c))` for every `N > 0`: the endpoint half-steps and the `N−1` interior steps add to the
total Euclidean time `T`.  This removes any `N`-dependence from the potential factor in H3's
continuum transfer; the remaining convergence is in the kernel measure alone.
-/

noncomputable section

namespace BookProof.ContinuousTimeWeight

open BookProof.StrangPotentialWeight

/-- The constant-potential Strang weight depends only on the total time `T = εN`. -/
theorem strangWeight_const_time {T c : ℝ} {N : ℕ} (hN : 0 < N) (z : ℕ → ℝ) :
    strangWeight (T / N) (fun _ => c) N z = Real.exp (-(T * c)) := by
  rw [strangWeight_const (T / N) c hN z]
  congr 1
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  field_simp [hN0]

end BookProof.ContinuousTimeWeight
