import BookProof.ChapterFriedrichsSquareFactorization

/-!
# Axiom audit for `BookProof.ChapterFriedrichsSquareFactorization`

Run with `lake build Work.FriedrichsSquareFactorizationAudit`.  Each line must
report only `propext`, `Classical.choice`, `Quot.sound`.
-/

#print axioms BookProof.FriedrichsSquare.clGraph_le_adjGraph
#print axioms BookProof.FriedrichsSquare.fst_mem_clDom_of_mem_factorRel
#print axioms BookProof.FriedrichsSquare.flipGraph_isClosed
#print axioms BookProof.FriedrichsSquare.mem_flipGraph_orthogonal_iff
#print axioms BookProof.FriedrichsSquare.exists_mem_factorRel_add
#print axioms BookProof.FriedrichsSquare.factorRel_le_adjPairs
#print axioms BookProof.FriedrichsSquare.IsFriedrichsSqExtension.symmetric
#print axioms BookProof.FriedrichsSquare.adjPairs_factorRel
#print axioms BookProof.FriedrichsSquare.le_factorRel_of_symmetric_extension
#print axioms BookProof.FriedrichsSquare.isFriedrichsSqExtension_factorRel
#print axioms BookProof.FriedrichsSquare.isFriedrichsSqExtension_iff_eq_factorRel
#print axioms BookProof.FriedrichsSquare.friedrichsSqExtension_unique
#print axioms BookProof.FriedrichsSquare.factorRel_quadForm_nonneg
#print axioms BookProof.FriedrichsSquare.factorRel_snd_eq_zero_of_fst_eq_zero
#print axioms BookProof.FriedrichsSquare.opGraph_frExt
#print axioms BookProof.FriedrichsSquare.frDom_le_clDom
#print axioms BookProof.FriedrichsSquare.isSelfAdjointExtension_frExt
#print axioms BookProof.FriedrichsSquare.frExt_quadForm_nonneg
#print axioms BookProof.FriedrichsSquare.eq_frExt_of_isSelfAdjointExtension
