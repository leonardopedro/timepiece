import BookProof.ChapterEsaFarisLavineIndex

/-!
Axiom audit for the 2026-09-11 wave: essential self-adjointness **only through
Faris–Lavine**, and the Yang–Mills outer Fock space.  Every result below must report only
`propext`, `Classical.choice` and `Quot.sound`.
-/

-- The abstract step: Faris–Lavine on the graph core itself.
#print axioms BookProof.QgOuterFockCoreFL.CoreData.ext_graph_approx
#print axioms BookProof.QgOuterFockCoreFL.CoreData.esa_on_core

-- The Faris–Lavine replacement for the Carleman route.
#print axioms BookProof.FarisLavineOnly.sqSumOp_esa_farisLavine
#print axioms BookProof.FarisLavineOnly.secHam_esa_fl
#print axioms BookProof.FarisLavineOnly.outerHam_esa_fl

-- Yang–Mills.
#print axioms BookProof.YmOuterFockFL.ymAbelian_eq_sqSumOp
#print axioms BookProof.YmOuterFockFL.ymAbelian_esa_farisLavine
#print axioms BookProof.YmOuterFockFL.linForm_ymMag
#print axioms BookProof.YmOuterFockFL.linForm_ymGauss
#print axioms BookProof.YmOuterFockFL.linForm_ymTie
#print axioms BookProof.YmOuterFockFL.ym_interaction_nontrivial
#print axioms BookProof.YmOuterFockFL.ymVec_row_le
#print axioms BookProof.YmOuterFockFL.ymVec_col_le
#print axioms BookProof.YmOuterFockFL.ymOuterHam_esa_fl
#print axioms BookProof.YmOuterFockFL.ymOuterFock_esa_farisLavine

-- The index.
#print axioms BookProof.EsaFarisLavineIndex.qg_sector_esa_fl
#print axioms BookProof.EsaFarisLavineIndex.qg_outerHam_esa_fl
#print axioms BookProof.EsaFarisLavineIndex.QgInt.qgInt_outerHam_esa_fl
#print axioms BookProof.EsaFarisLavineIndex.Ns.ns_outerHam_esa_fl
#print axioms BookProof.EsaFarisLavineIndex.Scalaron.scalaron_esa_core_fl
