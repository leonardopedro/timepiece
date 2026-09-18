import BookProof.ChapterNsFieldMomentumInverse

/-!
# Axiom audit — the inverse field momentum

Every headline result of `BookProof/ChapterNsFieldMomentumInverse.lean` (item 2 of the
Navier–Stokes plan items) must rest on the standard axioms only: `propext`, `Classical.choice`,
`Quot.sound`.
-/

#print axioms BookProof.NsFieldMomentumInverse.volume_momSymbol_zero
#print axioms BookProof.NsFieldMomentumInverse.momSymbol_ne_zero_ae
#print axioms BookProof.NsFieldMomentumInverse.momentum_kernel_trivial
#print axioms BookProof.NsFieldMomentumInverse.isMomInverse_unique
#print axioms BookProof.NsFieldMomentumInverse.isMomInverse_of_memLp
#print axioms BookProof.NsFieldMomentumInverse.cut_mem_momDomain
#print axioms BookProof.NsFieldMomentumInverse.momDomain_dense
#print axioms BookProof.NsFieldMomentumInverse.isMomInverse_smul
#print axioms BookProof.NsFieldMomentumInverse.eq_div_of_mul_eq_ae
#print axioms BookProof.NsFieldMomentumInverse.isMomInverse_momentumOp
