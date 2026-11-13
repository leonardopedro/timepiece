import BookProof.ChapterVonNeumannCore
import BookProof.RoadmapAudit.AxiomAudit

/-!
# Axiom audit for `BookProof.ChapterVonNeumannCore`

Run with `lake build Work.VonNeumannCoreAudit`.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

#audit_axioms BookProof.VonNeumannCore.inner_fst_add_self
#audit_axioms BookProof.VonNeumannCore.eq_zero_of_mem_factorRel_add_eq_zero
#audit_axioms BookProof.VonNeumannCore.eq_of_mem_factorRel_add_eq
#audit_axioms BookProof.VonNeumannCore.norm_le_of_mem_factorRel_add
#audit_axioms BookProof.VonNeumannCore.factorRel_witness
#audit_axioms BookProof.VonNeumannCore.resPair_unique
#audit_axioms BookProof.VonNeumannCore.resLin_mem_factorRel
#audit_axioms BookProof.VonNeumannCore.norm_resLin_le
#audit_axioms BookProof.VonNeumannCore.norm_resCLM_le_one
#audit_axioms BookProof.VonNeumannCore.resCLM_mem_frDom
#audit_axioms BookProof.VonNeumannCore.resLin_left_inverse
#audit_axioms BookProof.VonNeumannCore.resLin_right_inverse
#audit_axioms BookProof.VonNeumannCore.eq_zero_of_inner_frDom_eq_zero
#audit_axioms BookProof.VonNeumannCore.frDom_dense
#audit_axioms BookProof.VonNeumannCore.clLp_isClosed
#audit_axioms BookProof.VonNeumannCore.eq_zero_of_mem_clLp_of_orthogonal
#audit_axioms BookProof.VonNeumannCore.clLp_le_topologicalClosure_coreLp
#audit_axioms BookProof.VonNeumannCore.topologicalClosure_coreGraph
#audit_axioms BookProof.VonNeumannCore.opGraph_coreRes
#audit_axioms BookProof.VonNeumannCore.clGraph_coreRes
#audit_axioms BookProof.VonNeumannCore.isCoreOf_coreRes
#audit_axioms BookProof.VonNeumannCore.adjGraph_coreRes
#audit_axioms BookProof.VonNeumannCore.factorGraph_coreRes
