import BookProof.ChapterNonnegResolvent
import BookProof.RoadmapAudit.AxiomAudit

/-!
# Axiom audit for `BookProof.ChapterNonnegResolvent`

Run with `lake build Work.NonnegResolventAudit`.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

#audit_axioms BookProof.NonnegResolvent.invCLMAt_sub
#audit_axioms BookProof.NonnegResolvent.invCLMAt_comm
#audit_axioms BookProof.NonnegResolvent.inner_invCLMAt_left
#audit_axioms BookProof.NonnegResolvent.isSelfAdjoint_invCLMAt
#audit_axioms BookProof.NonnegResolvent.invCLMAt_nonneg
#audit_axioms BookProof.NonnegResolvent.norm_smul_invCLMAt_le
#audit_axioms BookProof.NonnegResolvent.smul_invCLMAt_le_one
#audit_axioms BookProof.NonnegResolvent.smul_invCLMAt_sub_of_mem
#audit_axioms BookProof.NonnegResolvent.norm_smul_invCLMAt_sub_le
#audit_axioms BookProof.NonnegResolvent.dense_domain
#audit_axioms BookProof.NonnegResolvent.tendsto_smul_invCLMAt
#audit_axioms BookProof.NonnegResolvent.yosidaCLM
#audit_axioms BookProof.NonnegResolvent.yosidaCLM_apply
#audit_axioms BookProof.NonnegResolvent.yosidaCLM_mem
#audit_axioms BookProof.NonnegResolvent.yosidaCLM_of_mem
#audit_axioms BookProof.NonnegResolvent.norm_yosidaCLM_le_of_mem
#audit_axioms BookProof.NonnegResolvent.isSelfAdjoint_yosidaCLM
#audit_axioms BookProof.NonnegResolvent.smul_nonneg_of_nonneg
#audit_axioms BookProof.NonnegResolvent.yosidaCLM_nonneg
#audit_axioms BookProof.NonnegResolvent.re_inner_yosidaCLM_le
#audit_axioms BookProof.NonnegResolvent.invCLMAt_sub_eq
#audit_axioms BookProof.NonnegResolvent.yosidaCLM_sub
#audit_axioms BookProof.NonnegResolvent.yosidaCLM_mono
#audit_axioms BookProof.NonnegResolvent.tendsto_yosidaCLM
#audit_axioms BookProof.NonnegResolvent.resAt
#audit_axioms BookProof.NonnegResolvent.yosidaAt
#audit_axioms BookProof.NonnegResolvent.tendsto_smul_resAt
#audit_axioms BookProof.NonnegResolvent.tendsto_yosidaAt
