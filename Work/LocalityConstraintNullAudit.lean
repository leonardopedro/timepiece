import BookProof.ChapterLocalityConstraintNull

/-!
# Axiom audit for `BookProof.ChapterLocalityConstraintNull`

Run with `lake build Work.LocalityConstraintNullAudit`.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

#print axioms BookProof.LocalityConstraint.measurableSet_graphSet
#print axioms BookProof.LocalityConstraint.preimage_mk_graphSet
#print axioms BookProof.LocalityConstraint.graphSet_null
#print axioms BookProof.LocalityConstraint.graphSet_volume_null
#print axioms BookProof.LocalityConstraint.graphSet_gaussian_null
#print axioms BookProof.LocalityConstraint.restrict_graphSet_eq_zero
#print axioms BookProof.LocalityConstraint.not_isProbabilityMeasure_restrict_graphSet
