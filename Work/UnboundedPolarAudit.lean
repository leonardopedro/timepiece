import BookProof.ChapterUnboundedPolar

/-!
# Axiom audit for `BookProof.ChapterUnboundedPolar`

Run with `lake build Work.UnboundedPolarAudit`.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

#print axioms BookProof.UnboundedPolar.adjPairs_eq_self_of_symmetric_of_surjective
#print axioms BookProof.UnboundedPolar.adjPairs_isClosed
#print axioms BookProof.UnboundedPolar.sqrtOp
#print axioms BookProof.UnboundedPolar.coSqrtOp
#print axioms BookProof.UnboundedPolar.midOp
#print axioms BookProof.UnboundedPolar.spectrum_subset_Icc
#print axioms BookProof.UnboundedPolar.sqrtOp_mul_self
#print axioms BookProof.UnboundedPolar.coSqrtOp_mul_self
#print axioms BookProof.UnboundedPolar.sqrtOp_mul_coSqrtOp
#print axioms BookProof.UnboundedPolar.coSqrtOp_mul_sqrtOp
#print axioms BookProof.UnboundedPolar.sqrtOp_nonneg
#print axioms BookProof.UnboundedPolar.coSqrtOp_nonneg
#print axioms BookProof.UnboundedPolar.midOp_nonneg
#print axioms BookProof.UnboundedPolar.isSelfAdjoint_sqrtOp
#print axioms BookProof.UnboundedPolar.isSelfAdjoint_coSqrtOp
#print axioms BookProof.UnboundedPolar.one_le_sqrtOp_add_coSqrtOp
#print axioms BookProof.UnboundedPolar.isUnit_sqrtOp_add_coSqrtOp
#print axioms BookProof.UnboundedPolar.exists_sqrtOp_add_coSqrtOp_eq
#print axioms BookProof.UnboundedPolar.sqrtOp_injective
#print axioms BookProof.UnboundedPolar.inner_isSelfAdjoint_left
#print axioms BookProof.UnboundedPolar.inner_resCLM_self
#print axioms BookProof.UnboundedPolar.resCLM_nonneg
#print axioms BookProof.UnboundedPolar.resCLM_le_one
#print axioms BookProof.UnboundedPolar.resCLM_injective
#print axioms BookProof.UnboundedPolar.absB
#print axioms BookProof.UnboundedPolar.absC
#print axioms BookProof.UnboundedPolar.absRel
#print axioms BookProof.UnboundedPolar.mem_absRel_iff
#print axioms BookProof.UnboundedPolar.mem_absRel
#print axioms BookProof.UnboundedPolar.absB_mul_absB
#print axioms BookProof.UnboundedPolar.absC_mul_absC
#print axioms BookProof.UnboundedPolar.absB_mul_absC
#print axioms BookProof.UnboundedPolar.absC_mul_absB
#print axioms BookProof.UnboundedPolar.isSelfAdjoint_absB
#print axioms BookProof.UnboundedPolar.isSelfAdjoint_absC
#print axioms BookProof.UnboundedPolar.absB_absB_apply
#print axioms BookProof.UnboundedPolar.absC_absC_apply
#print axioms BookProof.UnboundedPolar.absB_absC_apply
#print axioms BookProof.UnboundedPolar.absB_injective
#print axioms BookProof.UnboundedPolar.absRel_le_adjPairs
#print axioms BookProof.UnboundedPolar.exists_mem_absRel_add
#print axioms BookProof.UnboundedPolar.adjPairs_absRel
#print axioms BookProof.UnboundedPolar.absRel_isClosed
#print axioms BookProof.UnboundedPolar.absRel_snd_eq_zero_of_fst_eq_zero
#print axioms BookProof.UnboundedPolar.absRel_quadForm_nonneg
#print axioms BookProof.UnboundedPolar.absRel_comp_self
#print axioms BookProof.UnboundedPolar.absDom
#print axioms BookProof.UnboundedPolar.mem_absDom_iff
#print axioms BookProof.UnboundedPolar.mem_absDom_iff_range
#print axioms BookProof.UnboundedPolar.absFun
#print axioms BookProof.UnboundedPolar.absFun_spec
#print axioms BookProof.UnboundedPolar.absFun_unique
#print axioms BookProof.UnboundedPolar.absOp
#print axioms BookProof.UnboundedPolar.opGraph_absOp
#print axioms BookProof.UnboundedPolar.clGraph_absOp
#print axioms BookProof.UnboundedPolar.absDom_dense
#print axioms BookProof.UnboundedPolar.symmetricOn_absOp
#print axioms BookProof.UnboundedPolar.adjGraph_absOp
#print axioms BookProof.UnboundedPolar.factorRel_absOp
#print axioms BookProof.UnboundedPolar.frDom_absOp
#print axioms BookProof.UnboundedPolar.topologicalClosure_coreGraph_absOp
#print axioms BookProof.UnboundedPolar.norm_eq_of_mem_frDom
#print axioms BookProof.UnboundedPolar.exists_of_mem_topologicalClosure
#print axioms BookProof.UnboundedPolar.exists_mem_absRel_of_mem_clGraph
#print axioms BookProof.UnboundedPolar.exists_mem_clGraph_of_mem_absRel
#print axioms BookProof.UnboundedPolar.absDom_eq_clDom
#print axioms BookProof.UnboundedPolar.norm_absFun_eq_norm_clFun
#print axioms BookProof.UnboundedPolar.inner_eq_of_norm_eq
#print axioms BookProof.UnboundedPolar.absOn
#print axioms BookProof.UnboundedPolar.absOn_spec
#print axioms BookProof.UnboundedPolar.norm_absOn
#print axioms BookProof.UnboundedPolar.inner_absOn
#print axioms BookProof.UnboundedPolar.exists_polar_isometry
