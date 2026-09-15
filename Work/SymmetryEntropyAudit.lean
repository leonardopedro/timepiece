import BookProof.ChapterSymmetryEntropy

/-!
# Axiom audit for `BookProof.ChapterSymmetryEntropy`

Run with `lake build Work.SymmetryEntropyAudit`.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

#print axioms BookProof.SymmetryEntropy.negMulLog_eq_zero_iff
#print axioms BookProof.SymmetryEntropy.entropy_nonneg
#print axioms BookProof.SymmetryEntropy.entropy_eq_zero_iff
#print axioms BookProof.SymmetryEntropy.entropy_pointMass
#print axioms BookProof.SymmetryEntropy.bornCol_le_one
#print axioms BookProof.SymmetryEntropy.exists_eq_one_of_isDeterministicCol
#print axioms BookProof.SymmetryEntropy.isDeterministicCol_of_entropy_eq_zero
#print axioms BookProof.SymmetryEntropy.isDeterministicCol_iff_entropy_eq_zero
#print axioms BookProof.SymmetryEntropy.entropy_bornCol_pos_iff_not_isDeterministicCol
