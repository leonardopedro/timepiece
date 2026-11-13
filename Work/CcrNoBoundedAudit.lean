import BookProof.ChapterCcrNoBounded
import BookProof.RoadmapAudit.AxiomAudit

/-!
# Axiom audit for `BookProof.ChapterCcrNoBounded`

Run with `lake build Work.CcrNoBoundedAudit`.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

#audit_axioms BookProof.CcrNoBounded.commutator_eq_zero_of_momentum_zero
#audit_axioms BookProof.CcrNoBounded.ccr_fails_of_momentum_zero
#audit_axioms BookProof.CcrNoBounded.matrix_no_ccr
#audit_axioms BookProof.CcrNoBounded.ccr_pow
#audit_axioms BookProof.CcrNoBounded.ccr_pow_ne_zero
#audit_axioms BookProof.CcrNoBounded.no_ccr_one
#audit_axioms BookProof.CcrNoBounded.no_ccr_smul
