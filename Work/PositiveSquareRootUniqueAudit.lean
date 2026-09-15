import BookProof.ChapterPositiveSquareRootUnique

/-!
# Axiom audit for `BookProof.ChapterPositiveSquareRootUnique`

Run with `lake build Work.PositiveSquareRootUniqueAudit`.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

#print axioms BookProof.PositiveSquareRoot.IsNonnegSelfAdjoint
#print axioms BookProof.PositiveSquareRoot.symm_inner
#print axioms BookProof.PositiveSquareRoot.norm_sq_add_le
#print axioms BookProof.PositiveSquareRoot.norm_fst_le
#print axioms BookProof.PositiveSquareRoot.norm_snd_le
#print axioms BookProof.PositiveSquareRoot.eq_of_add_eq
#print axioms BookProof.PositiveSquareRoot.isClosed_rel
#print axioms BookProof.PositiveSquareRoot.sumMap
#print axioms BookProof.PositiveSquareRoot.isClosed_rangeSum
#print axioms BookProof.PositiveSquareRoot.rangeSum_orthogonal_eq_bot
#print axioms BookProof.PositiveSquareRoot.exists_add_eq
#print axioms BookProof.PositiveSquareRoot.inner_im_eq_zero
#print axioms BookProof.PositiveSquareRoot.invPair
#print axioms BookProof.PositiveSquareRoot.invLin
#print axioms BookProof.PositiveSquareRoot.invCLM
#print axioms BookProof.PositiveSquareRoot.invCLM_mem
#print axioms BookProof.PositiveSquareRoot.invCLM_eq_of_mem
#print axioms BookProof.PositiveSquareRoot.inner_invCLM_left
#print axioms BookProof.PositiveSquareRoot.isSelfAdjoint_invCLM
#print axioms BookProof.PositiveSquareRoot.invCLM_nonneg
#print axioms BookProof.PositiveSquareRoot.invCLM_le_one
#print axioms BookProof.PositiveSquareRoot.rel_eq_of_invCLM_eq
#print axioms BookProof.PositiveSquareRoot.resCLM_mul_den
#print axioms BookProof.PositiveSquareRoot.gFun
#print axioms BookProof.PositiveSquareRoot.psiFun
#print axioms BookProof.PositiveSquareRoot.den_pos
#print axioms BookProof.PositiveSquareRoot.continuous_gFun
#print axioms BookProof.PositiveSquareRoot.continuous_psiFun
#print axioms BookProof.PositiveSquareRoot.psi_gFun
#print axioms BookProof.PositiveSquareRoot.cfc_den
#print axioms BookProof.PositiveSquareRoot.isUnit_den
#print axioms BookProof.PositiveSquareRoot.cfc_gFun_mul_den
#print axioms BookProof.PositiveSquareRoot.eq_cfc_gFun
#print axioms BookProof.PositiveSquareRoot.eq_cfc_psiFun
#print axioms BookProof.PositiveSquareRoot.invCLM_eq_cfc
#print axioms BookProof.PositiveSquareRoot.isNonnegSelfAdjoint_absRel
#print axioms BookProof.PositiveSquareRoot.eq_absRel_of_isNonnegSelfAdjoint
#print axioms BookProof.PositiveSquareRoot.absRel_unique_nonneg_sqrt
