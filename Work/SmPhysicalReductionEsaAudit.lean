import BookProof.Sm.ChapterSmPhysicalReductionEsa

/-!
# Axiom audit for `BookProof.Sm.ChapterSmPhysicalReductionEsa`

Run with `lake build Work.SmPhysicalReductionEsaAudit`.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

#print axioms BookProof.SmPhysicalReduction.evenPart_add_oddPart
#print axioms BookProof.SmPhysicalReduction.evenPart_mem
#print axioms BookProof.SmPhysicalReduction.oddPart_mem
#print axioms BookProof.SmPhysicalReduction.inner_map_map_of_norm_map
#print axioms BookProof.SmPhysicalReduction.inner_map_left_eq
#print axioms BookProof.SmPhysicalReduction.inner_eq_zero_of_mem_even_of_mem_odd
#print axioms BookProof.SmPhysicalReduction.inner_eq_zero_of_mem_odd_of_mem_even
#print axioms BookProof.SmPhysicalReduction.evenOp_mem
#print axioms BookProof.SmPhysicalReduction.oddOp_mem
#print axioms BookProof.SmPhysicalReduction.deficiency_at_of_even_deficiency
#print axioms BookProof.SmPhysicalReduction.deficiency_at_of_odd_deficiency
#print axioms BookProof.SmPhysicalReduction.deficiencyTrivialAt_iff_sectors
#print axioms BookProof.SmPhysicalReduction.coupledParity_inner
#print axioms BookProof.SmPhysicalReduction.smNormalForm_parity_core
#print axioms BookProof.SmPhysicalReduction.smNormalForm_esd_iff_parity_sectors
#print axioms BookProof.SmPhysicalReduction.topologicalClosure_evenCore
#print axioms BookProof.SmPhysicalReduction.topologicalClosure_oddCore
