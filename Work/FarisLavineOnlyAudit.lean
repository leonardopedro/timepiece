import BookProof.ChapterEsaFarisLavineIndex
import BookProof.RoadmapAudit.AxiomAudit

/-!
Axiom audit for the 2026-09-11 wave: essential self-adjointness **only through
Faris–Lavine**, and the Yang–Mills outer Fock space.  Every result below must report only
`propext`, `Classical.choice` and `Quot.sound`.
-/

-- The abstract step: Faris–Lavine on the graph core itself.
#audit_axioms BookProof.QgOuterFockCoreFL.CoreData.ext_graph_approx
#audit_axioms BookProof.QgOuterFockCoreFL.CoreData.esa_on_core

-- The Faris–Lavine replacement for the Carleman route.
#audit_axioms BookProof.FarisLavineOnly.sqSumOp_esa_farisLavine
#audit_axioms BookProof.FarisLavineOnly.secHam_esa_fl
#audit_axioms BookProof.FarisLavineOnly.outerHam_esa_fl

-- Yang–Mills.
#audit_axioms BookProof.YmOuterFockFL.ymAbelian_eq_sqSumOp
#audit_axioms BookProof.YmOuterFockFL.ymAbelian_esa_farisLavine
#audit_axioms BookProof.YmOuterFockFL.linForm_ymMag
#audit_axioms BookProof.YmOuterFockFL.linForm_ymGauss
#audit_axioms BookProof.YmOuterFockFL.linForm_ymTie
#audit_axioms BookProof.YmOuterFockFL.ym_interaction_nontrivial
#audit_axioms BookProof.YmOuterFockFL.ymVec_row_le
#audit_axioms BookProof.YmOuterFockFL.ymVec_col_le
#audit_axioms BookProof.YmOuterFockFL.ymOuterHam_esa_fl
#audit_axioms BookProof.YmOuterFockFL.ymOuterFock_esa_farisLavine

-- The index.
#audit_axioms BookProof.EsaFarisLavineIndex.qg_sector_esa_fl
#audit_axioms BookProof.EsaFarisLavineIndex.qg_outerHam_esa_fl
#audit_axioms BookProof.EsaFarisLavineIndex.QgInt.qgInt_outerHam_esa_fl
#audit_axioms BookProof.EsaFarisLavineIndex.Ns.ns_outerHam_esa_fl
#audit_axioms BookProof.EsaFarisLavineIndex.Scalaron.scalaron_esa_core_fl
