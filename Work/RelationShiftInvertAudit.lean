import BookProof.ChapterRelationShiftInvert
import BookProof.RoadmapAudit.AxiomAudit

/-!
# Axiom audit for `BookProof.ChapterRelationShiftInvert`

Run with `lake build Work.RelationShiftInvertAudit`.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

#audit_axioms BookProof.RelationShiftInvert.relDomain
#audit_axioms BookProof.RelationShiftInvert.mem_relDomain_iff
#audit_axioms BookProof.RelationShiftInvert.snd_unique
#audit_axioms BookProof.RelationShiftInvert.relOpFun
#audit_axioms BookProof.RelationShiftInvert.relOpFun_mem
#audit_axioms BookProof.RelationShiftInvert.relOpFun_eq
#audit_axioms BookProof.RelationShiftInvert.relOp
#audit_axioms BookProof.RelationShiftInvert.relOp_mem
#audit_axioms BookProof.RelationShiftInvert.isShiftInvert_invCLMAt
#audit_axioms BookProof.RelationShiftInvert.unitaryU_eq_of_invCLM_eq
#audit_axioms BookProof.RelationShiftInvert.unitaryU_mem_relDomain
#audit_axioms BookProof.RelationShiftInvert.relOp_unitaryU
#audit_axioms BookProof.RelationShiftInvert.hasDerivAt_unitaryU_relOp
