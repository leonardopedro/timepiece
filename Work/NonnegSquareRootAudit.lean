import BookProof.ChapterNonnegSquareRoot

/-!
# Axiom audit for `BookProof.ChapterNonnegSquareRoot`

Run with `lake build Work.NonnegSquareRootAudit`.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

#print axioms BookProof.NonnegSquareRoot.sqrtB
#print axioms BookProof.NonnegSquareRoot.sqrtC
#print axioms BookProof.NonnegSquareRoot.sqrtRel
#print axioms BookProof.NonnegSquareRoot.mem_sqrtRel_iff
#print axioms BookProof.NonnegSquareRoot.mem_sqrtRel
#print axioms BookProof.NonnegSquareRoot.sqrtB_mul_sqrtB
#print axioms BookProof.NonnegSquareRoot.sqrtC_mul_sqrtC
#print axioms BookProof.NonnegSquareRoot.sqrtB_mul_sqrtC
#print axioms BookProof.NonnegSquareRoot.sqrtC_mul_sqrtB
#print axioms BookProof.NonnegSquareRoot.isSelfAdjoint_sqrtB
#print axioms BookProof.NonnegSquareRoot.isSelfAdjoint_sqrtC
#print axioms BookProof.NonnegSquareRoot.sqrtB_sqrtB_apply
#print axioms BookProof.NonnegSquareRoot.sqrtC_sqrtC_apply
#print axioms BookProof.NonnegSquareRoot.sqrtB_sqrtC_apply
#print axioms BookProof.NonnegSquareRoot.sqrtRel_le_adjPairs
#print axioms BookProof.NonnegSquareRoot.exists_mem_sqrtRel_add
#print axioms BookProof.NonnegSquareRoot.adjPairs_sqrtRel
#print axioms BookProof.NonnegSquareRoot.sqrtRel_isClosed
#print axioms BookProof.NonnegSquareRoot.sqrtRel_quadForm_nonneg
#print axioms BookProof.NonnegSquareRoot.isNonnegSelfAdjoint_sqrtRel
#print axioms BookProof.NonnegSquareRoot.sqrtRel_comp_self
#print axioms BookProof.NonnegSquareRoot.invCLM_mul_den
#print axioms BookProof.NonnegSquareRoot.invCLM_eq_cfc_of_sq
#print axioms BookProof.NonnegSquareRoot.eq_sqrtRel_of_isNonnegSelfAdjoint
#print axioms BookProof.NonnegSquareRoot.sqrtRel_unique_nonneg_sqrt
#print axioms BookProof.NonnegSquareRoot.invCLM_injective
#print axioms BookProof.NonnegSquareRoot.sqrtRel_snd_eq_zero_of_fst_eq_zero
#print axioms BookProof.NonnegSquareRoot.exists_mem_sqrtRel_of_mem
#print axioms BookProof.NonnegSquareRoot.inner_eq_norm_sq_of_mem
#print axioms BookProof.NonnegSquareRoot.norm_sq_eq_inner_of_mem
#print axioms BookProof.NonnegSquareRoot.mem_of_commute
#print axioms BookProof.NonnegSquareRoot.mem_sqrtRel_of_commute
#print axioms BookProof.NonnegSquareRoot.smulSnd
#print axioms BookProof.NonnegSquareRoot.smulRel
#print axioms BookProof.NonnegSquareRoot.mem_smulRel_iff
#print axioms BookProof.NonnegSquareRoot.mem_smulRel
#print axioms BookProof.NonnegSquareRoot.adjPairs_smulRel
#print axioms BookProof.NonnegSquareRoot.isNonnegSelfAdjoint_smulRel
#print axioms BookProof.NonnegSquareRoot.isNonnegSelfAdjoint_invSmulRel
#print axioms BookProof.NonnegSquareRoot.invCLMAt
#print axioms BookProof.NonnegSquareRoot.invCLMAt_apply
#print axioms BookProof.NonnegSquareRoot.invCLMAt_mem
#print axioms BookProof.NonnegSquareRoot.invCLMAt_eq_of_mem
#print axioms BookProof.NonnegSquareRoot.norm_invCLMAt_le
#print axioms BookProof.NonnegSquareRoot.existsUnique_smul_add_mem
#print axioms BookProof.NonnegSquareRoot.isNonnegSelfAdjoint_factorRel
#print axioms BookProof.NonnegSquareRoot.absRel_eq_sqrtRel
