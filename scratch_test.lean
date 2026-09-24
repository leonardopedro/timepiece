import Mathlib

namespace ScratchTest

open MeasureTheory Filter Set
open scoped Topology ENNReal

noncomputable def classicalSol (x₀ t : ℝ) : ℝ := x₀ / (1 - t * x₀)

-- simp both sides then exact
theorem v5 (x₀ t : ℝ) (ht : 1 - t * x₀ ≠ 0) :
    HasDerivAt (classicalSol x₀) ((classicalSol x₀ t) ^ 2) t := by
  have hnum : HasDerivAt (fun t : ℝ => 1 - t * x₀) (-x₀) t := by
    simpa using ((hasDerivAt_id t).mul_const x₀).const_sub 1
  have h := (hasDerivAt_const t x₀).div hnum ht
  have heq : (0 * (1 - t * x₀) - x₀ * -x₀) / (1 - t * x₀) ^ 2 = (classicalSol x₀ t) ^ 2 := by
    simp only [classicalSol, div_pow]
    ring
  simp only [classicalSol, Pi.div_def, heq] at h ⊢
  exact h

end ScratchTest
