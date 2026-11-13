import BookProof.ChapterNumericalRangeSemigroup
import BookProof.RoadmapAudit.AxiomAudit

/-!
Axiom audit for Crouzeix's inequality on a **half-plane**, with constant `1`, for the
exponentials of an operator whose numerical range has bounded real part.  This continues the
thread of `BookProof.ChapterNumericalRangeCrouzeix`, which settles the disc with a larger
constant.

Every result below must report only `propext`, `Classical.choice` and `Quot.sound`.
-/

#audit_axioms BookProof.ChapterNumericalRangeSemigroup.numReLE_iff_numRange_subset
#audit_axioms BookProof.ChapterNumericalRangeSemigroup.hasDerivAt_expApply
#audit_axioms BookProof.ChapterNumericalRangeSemigroup.hasDerivAt_normSq
#audit_axioms BookProof.ChapterNumericalRangeSemigroup.norm_exp_apply_le
#audit_axioms BookProof.ChapterNumericalRangeSemigroup.norm_exp_le
#audit_axioms BookProof.ChapterNumericalRangeSemigroup.norm_exp_le_one
#audit_axioms BookProof.ChapterNumericalRangeSemigroup.norm_cexp_le_of_re_le

-- The resolvent estimate to the right of the half-plane.
#audit_axioms BookProof.ChapterNumericalRangeSemigroup.shift_ker_eq_bot
#audit_axioms BookProof.ChapterNumericalRangeSemigroup.shift_range_eq_top
#audit_axioms BookProof.ChapterNumericalRangeSemigroup.shift_symm_apply
#audit_axioms BookProof.ChapterNumericalRangeSemigroup.norm_resolvent_le
