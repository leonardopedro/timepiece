import BookProof.ChapterNumericalRangeSemigroup

/-!
Axiom audit for Crouzeix's inequality on a **half-plane**, with constant `1`, for the
exponentials of an operator whose numerical range has bounded real part.  This continues the
thread of `BookProof.ChapterNumericalRangeCrouzeix`, which settles the disc with a larger
constant.

Every result below must report only `propext`, `Classical.choice` and `Quot.sound`.
-/

#print axioms BookProof.ChapterNumericalRangeSemigroup.numReLE_iff_numRange_subset
#print axioms BookProof.ChapterNumericalRangeSemigroup.hasDerivAt_expApply
#print axioms BookProof.ChapterNumericalRangeSemigroup.hasDerivAt_normSq
#print axioms BookProof.ChapterNumericalRangeSemigroup.norm_exp_apply_le
#print axioms BookProof.ChapterNumericalRangeSemigroup.norm_exp_le
#print axioms BookProof.ChapterNumericalRangeSemigroup.norm_exp_le_one
#print axioms BookProof.ChapterNumericalRangeSemigroup.norm_cexp_le_of_re_le

-- The resolvent estimate to the right of the half-plane.
#print axioms BookProof.ChapterNumericalRangeSemigroup.shift_ker_eq_bot
#print axioms BookProof.ChapterNumericalRangeSemigroup.shift_range_eq_top
#print axioms BookProof.ChapterNumericalRangeSemigroup.shift_symm_apply
#print axioms BookProof.ChapterNumericalRangeSemigroup.norm_resolvent_le
