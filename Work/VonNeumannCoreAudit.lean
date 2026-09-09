import BookProof.ChapterVonNeumannCore

/-!
# Axiom audit for `BookProof.ChapterVonNeumannCore`

Run with `lake build Work.VonNeumannCoreAudit`.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

#print axioms BookProof.VonNeumannCore.inner_fst_add_self
#print axioms BookProof.VonNeumannCore.eq_zero_of_mem_factorRel_add_eq_zero
#print axioms BookProof.VonNeumannCore.eq_of_mem_factorRel_add_eq
#print axioms BookProof.VonNeumannCore.norm_le_of_mem_factorRel_add
#print axioms BookProof.VonNeumannCore.factorRel_witness
#print axioms BookProof.VonNeumannCore.resPair_unique
#print axioms BookProof.VonNeumannCore.resLin_mem_factorRel
#print axioms BookProof.VonNeumannCore.norm_resLin_le
#print axioms BookProof.VonNeumannCore.norm_resCLM_le_one
#print axioms BookProof.VonNeumannCore.resCLM_mem_frDom
#print axioms BookProof.VonNeumannCore.resLin_left_inverse
#print axioms BookProof.VonNeumannCore.resLin_right_inverse
#print axioms BookProof.VonNeumannCore.eq_zero_of_inner_frDom_eq_zero
#print axioms BookProof.VonNeumannCore.frDom_dense
#print axioms BookProof.VonNeumannCore.clLp_isClosed
#print axioms BookProof.VonNeumannCore.eq_zero_of_mem_clLp_of_orthogonal
#print axioms BookProof.VonNeumannCore.clLp_le_topologicalClosure_coreLp
#print axioms BookProof.VonNeumannCore.topologicalClosure_coreGraph
#print axioms BookProof.VonNeumannCore.opGraph_coreRes
#print axioms BookProof.VonNeumannCore.clGraph_coreRes
#print axioms BookProof.VonNeumannCore.isCoreOf_coreRes
#print axioms BookProof.VonNeumannCore.adjGraph_coreRes
#print axioms BookProof.VonNeumannCore.factorGraph_coreRes
