import BookProof.ChapterCcrNoBounded

/-!
# Axiom audit for `BookProof.ChapterCcrNoBounded`

Run with `lake build Work.CcrNoBoundedAudit`.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

#print axioms BookProof.CcrNoBounded.commutator_eq_zero_of_momentum_zero
#print axioms BookProof.CcrNoBounded.ccr_fails_of_momentum_zero
#print axioms BookProof.CcrNoBounded.matrix_no_ccr
#print axioms BookProof.CcrNoBounded.ccr_pow
#print axioms BookProof.CcrNoBounded.ccr_pow_ne_zero
#print axioms BookProof.CcrNoBounded.no_ccr_one
#print axioms BookProof.CcrNoBounded.no_ccr_smul
