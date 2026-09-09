import BookProof.ChapterClosureUniqueness

/-!
# Axiom audit for `BookProof.ChapterClosureUniqueness`

Run with `lake build Work.ClosureUniquenessAudit`.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

#print axioms BookProof.ClosureUniqueness.clExt_isClosureOf
#print axioms BookProof.ClosureUniqueness.closure_unique
#print axioms BookProof.ClosureUniqueness.eq_clExt_of_isClosureOf
#print axioms BookProof.ClosureUniqueness.not_isSelfAdjointExtension_clExt_of_deficiency
#print axioms BookProof.ClosureUniqueness.clGraph_eq_of_isCoreOf_pair
#print axioms BookProof.ClosureUniqueness.adjGraph_eq_adjPairs_clGraph
#print axioms BookProof.ClosureUniqueness.adjGraph_eq_of_isCoreOf
#print axioms BookProof.ClosureUniqueness.compGraph_eq_of_isClosureOf
#print axioms BookProof.ClosureUniqueness.factorGraph_eq_of_isCoreOf_pair
#print axioms BookProof.ClosureUniqueness.exists_linearIsometry_of_inner_eq
#print axioms BookProof.ClosureUniqueness.eqOn_topologicalClosure_range_of_eqOn_range
#print axioms BookProof.ClosureUniqueness.mem_factorGraph_sqOp
#print axioms BookProof.ClosureUniqueness.factorGraph_symmetric
#print axioms BookProof.ClosureUniqueness.factorGraph_quadForm
#print axioms BookProof.ClosureUniqueness.factorGraph_quadForm_nonneg
#print axioms BookProof.ClosureUniqueness.positive_factor_unique
#print axioms BookProof.ClosureUniqueness.positive_sqrt_unique
#print axioms BookProof.ClosureUniqueness.farisLavine_closure_isSelfAdjoint_unique
#print axioms BookProof.ClosureUniqueness.farisLavine_clGraph_eq_of_cores
