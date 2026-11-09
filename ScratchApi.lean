import BookProof.Qym.ChapterYangMillsMehlerBridge
open MeasureTheory
open scoped ENNReal
example (y : ℝ) : ‖y‖ₑ ^ (2:ℝ) = ENNReal.ofReal (y^2) := by
  rw [Real.enorm_eq_ofReal_abs]
  rw [← ENNReal.ofReal_pow (abs_nonneg y) 2, sq_abs, sq]
#check @norm_toLp
#check @MeasureTheory.Lp.norm_def
