import BookProof.ChapterRelationShiftInvert

/-!
# Axiom audit for `BookProof.ChapterRelationShiftInvert`

Run with `lake build Work.RelationShiftInvertAudit`.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

#print axioms BookProof.RelationShiftInvert.relDomain
#print axioms BookProof.RelationShiftInvert.mem_relDomain_iff
#print axioms BookProof.RelationShiftInvert.snd_unique
#print axioms BookProof.RelationShiftInvert.relOpFun
#print axioms BookProof.RelationShiftInvert.relOpFun_mem
#print axioms BookProof.RelationShiftInvert.relOpFun_eq
#print axioms BookProof.RelationShiftInvert.relOp
#print axioms BookProof.RelationShiftInvert.relOp_mem
#print axioms BookProof.RelationShiftInvert.isShiftInvert_invCLMAt
#print axioms BookProof.RelationShiftInvert.unitaryU_eq_of_invCLM_eq
#print axioms BookProof.RelationShiftInvert.unitaryU_mem_relDomain
#print axioms BookProof.RelationShiftInvert.relOp_unitaryU
#print axioms BookProof.RelationShiftInvert.hasDerivAt_unitaryU_relOp
