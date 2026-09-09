import BookProof.ChapterNonnegResolvent

/-!
# Axiom audit for `BookProof.ChapterNonnegResolvent`

Run with `lake build Work.NonnegResolventAudit`.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

#print axioms BookProof.NonnegResolvent.invCLMAt_sub
#print axioms BookProof.NonnegResolvent.invCLMAt_comm
#print axioms BookProof.NonnegResolvent.inner_invCLMAt_left
#print axioms BookProof.NonnegResolvent.isSelfAdjoint_invCLMAt
#print axioms BookProof.NonnegResolvent.invCLMAt_nonneg
#print axioms BookProof.NonnegResolvent.norm_smul_invCLMAt_le
#print axioms BookProof.NonnegResolvent.smul_invCLMAt_le_one
#print axioms BookProof.NonnegResolvent.smul_invCLMAt_sub_of_mem
#print axioms BookProof.NonnegResolvent.norm_smul_invCLMAt_sub_le
#print axioms BookProof.NonnegResolvent.dense_domain
#print axioms BookProof.NonnegResolvent.tendsto_smul_invCLMAt
#print axioms BookProof.NonnegResolvent.yosidaCLM
#print axioms BookProof.NonnegResolvent.yosidaCLM_apply
#print axioms BookProof.NonnegResolvent.yosidaCLM_mem
#print axioms BookProof.NonnegResolvent.yosidaCLM_of_mem
#print axioms BookProof.NonnegResolvent.norm_yosidaCLM_le_of_mem
#print axioms BookProof.NonnegResolvent.isSelfAdjoint_yosidaCLM
#print axioms BookProof.NonnegResolvent.smul_nonneg_of_nonneg
#print axioms BookProof.NonnegResolvent.yosidaCLM_nonneg
#print axioms BookProof.NonnegResolvent.re_inner_yosidaCLM_le
#print axioms BookProof.NonnegResolvent.invCLMAt_sub_eq
#print axioms BookProof.NonnegResolvent.yosidaCLM_sub
#print axioms BookProof.NonnegResolvent.yosidaCLM_mono
#print axioms BookProof.NonnegResolvent.tendsto_yosidaCLM
#print axioms BookProof.NonnegResolvent.resAt
#print axioms BookProof.NonnegResolvent.yosidaAt
#print axioms BookProof.NonnegResolvent.tendsto_smul_resAt
#print axioms BookProof.NonnegResolvent.tendsto_yosidaAt
