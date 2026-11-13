import BookProof.Reconstruction.ChapterSymmetryEntropy
import BookProof.RoadmapAudit.AxiomAudit

/-!
# Axiom audit for `BookProof.ChapterSymmetryEntropy`

Run with `lake build Work.SymmetryEntropyAudit`.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

#audit_axioms BookProof.SymmetryEntropy.negMulLog_eq_zero_iff
#audit_axioms BookProof.SymmetryEntropy.entropy_nonneg
#audit_axioms BookProof.SymmetryEntropy.entropy_eq_zero_iff
#audit_axioms BookProof.SymmetryEntropy.entropy_pointMass
#audit_axioms BookProof.SymmetryEntropy.bornCol_le_one
#audit_axioms BookProof.SymmetryEntropy.exists_eq_one_of_isDeterministicCol
#audit_axioms BookProof.SymmetryEntropy.isDeterministicCol_of_entropy_eq_zero
#audit_axioms BookProof.SymmetryEntropy.isDeterministicCol_iff_entropy_eq_zero
#audit_axioms BookProof.SymmetryEntropy.entropy_bornCol_pos_iff_not_isDeterministicCol
