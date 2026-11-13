import BookProof.ChapterLocalityConstraintNull
import BookProof.RoadmapAudit.AxiomAudit

/-!
# Axiom audit for `BookProof.ChapterLocalityConstraintNull`

Run with `lake build Work.LocalityConstraintNullAudit`.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

#audit_axioms BookProof.LocalityConstraint.measurableSet_graphSet
#audit_axioms BookProof.LocalityConstraint.preimage_mk_graphSet
#audit_axioms BookProof.LocalityConstraint.graphSet_null
#audit_axioms BookProof.LocalityConstraint.graphSet_volume_null
#audit_axioms BookProof.LocalityConstraint.graphSet_gaussian_null
#audit_axioms BookProof.LocalityConstraint.restrict_graphSet_eq_zero
#audit_axioms BookProof.LocalityConstraint.not_isProbabilityMeasure_restrict_graphSet
