import BookProof.ChapterNonnegUnitaryGroup

/-!
# Axiom audit for `BookProof.ChapterNonnegUnitaryGroup`

Run with `lake build Work.NonnegUnitaryGroupAudit`.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

#print axioms BookProof.NonnegUnitaryGroup.hasDerivAt_apply
#print axioms BookProof.NonnegUnitaryGroup.expU
#print axioms BookProof.NonnegUnitaryGroup.smul_neg_I_mem_skewAdjoint
#print axioms BookProof.NonnegUnitaryGroup.expU_mem_unitary
#print axioms BookProof.NonnegUnitaryGroup.expU_zero
#print axioms BookProof.NonnegUnitaryGroup.expU_add
#print axioms BookProof.NonnegUnitaryGroup.norm_expU_apply
#print axioms BookProof.NonnegUnitaryGroup.expU_zero_op
#print axioms BookProof.NonnegUnitaryGroup.hasDerivAt_expU
#print axioms BookProof.NonnegUnitaryGroup.hasDerivAt_expU_apply
#print axioms BookProof.NonnegUnitaryGroup.norm_expU_sub_apply_le
#print axioms BookProof.NonnegUnitaryGroup.norm_expU_sub_self_le
#print axioms BookProof.NonnegUnitaryGroup.cauchySeq_of_dense_of_isometry
#print axioms BookProof.NonnegUnitaryGroup.commute_invCLMAt
#print axioms BookProof.NonnegUnitaryGroup.commute_yosidaCLM
#print axioms BookProof.NonnegUnitaryGroup.commute_yosidaCLM_invCLMAt
#print axioms BookProof.NonnegUnitaryGroup.commute_yosidaAt
#print axioms BookProof.NonnegUnitaryGroup.isSelfAdjoint_yosidaAt
#print axioms BookProof.NonnegUnitaryGroup.approxU
#print axioms BookProof.NonnegUnitaryGroup.approxU_zero
#print axioms BookProof.NonnegUnitaryGroup.approxU_add
#print axioms BookProof.NonnegUnitaryGroup.norm_approxU_apply
#print axioms BookProof.NonnegUnitaryGroup.norm_approxU_sub_apply_le
#print axioms BookProof.NonnegUnitaryGroup.approxU_cauchy_of_mem
#print axioms BookProof.NonnegUnitaryGroup.approxU_cauchy
#print axioms BookProof.NonnegUnitaryGroup.unitaryFun
#print axioms BookProof.NonnegUnitaryGroup.tendsto_unitaryFun
#print axioms BookProof.NonnegUnitaryGroup.norm_unitaryFun
#print axioms BookProof.NonnegUnitaryGroup.unitaryLinear
#print axioms BookProof.NonnegUnitaryGroup.unitaryU
#print axioms BookProof.NonnegUnitaryGroup.unitaryU_apply
#print axioms BookProof.NonnegUnitaryGroup.tendsto_unitaryU
#print axioms BookProof.NonnegUnitaryGroup.norm_unitaryU_apply
#print axioms BookProof.NonnegUnitaryGroup.unitaryU_zero
#print axioms BookProof.NonnegUnitaryGroup.unitaryU_add
#print axioms BookProof.NonnegUnitaryGroup.unitaryU_apply_unitaryU
#print axioms BookProof.NonnegUnitaryGroup.unitaryU_surjective
#print axioms BookProof.NonnegUnitaryGroup.unitaryU_mem_unitary
#print axioms BookProof.NonnegUnitaryGroup.norm_unitaryU_sub_approxU_le
#print axioms BookProof.NonnegUnitaryGroup.norm_unitaryU_sub_of_mem
#print axioms BookProof.NonnegUnitaryGroup.tendsto_unitaryU_zero
#print axioms BookProof.NonnegUnitaryGroup.continuous_unitaryU_apply
#print axioms BookProof.NonnegUnitaryGroup.tendstoUniformlyOn_approxU
#print axioms BookProof.NonnegUnitaryGroup.unitaryU_invCLMAt
#print axioms BookProof.NonnegUnitaryGroup.mem_unitaryU
#print axioms BookProof.NonnegUnitaryGroup.hasDerivAt_unitaryU
#print axioms BookProof.NonnegUnitaryGroup.inner_unitaryU
#print axioms BookProof.NonnegUnitaryGroup.inner_unitaryU_of_mem
#print axioms BookProof.NonnegUnitaryGroup.inner_mem_conj_eq
#print axioms BookProof.NonnegUnitaryGroup.eq_unitaryU_of_hasDerivAt
#print axioms BookProof.NonnegUnitaryGroup.unitaryU_neg_eq_star
