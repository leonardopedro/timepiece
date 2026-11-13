/-
Axiom audit for `BookProof.SmBrstQuotient` (SM_ESA_COMPLETION_PLAN §46).

Every declaration below must rest on `propext`, `Classical.choice`, `Quot.sound` only.
`PhysicalPositivity` is a definition (a named input), not a theorem.
-/
import BookProof.Sm.ChapterSmBrstQuotient
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.SmBrstQuotient

#audit_axioms IsBrst
#audit_axioms gauge
#audit_axioms closed
#audit_axioms gauge_le_ker
#audit_axioms mem_closed_of_mem_gauge
#audit_axioms kform
#audit_axioms kform_add_right
#audit_axioms kform_smul_right
#audit_axioms kform_add_left
#audit_axioms kform_zero_right
#audit_axioms kform_ghost_null
#audit_axioms kform_ghost_null_right
#audit_axioms kform_well_defined
#audit_axioms U_mem_closed
#audit_axioms U_mem_gauge
#audit_axioms kform_eq_zero_of_mem_even_of_mem_odd
#audit_axioms kform_eq_zero_of_mem_odd_of_mem_even
#audit_axioms kform_quadForm_split
#audit_axioms kform_quadForm_nonneg
#audit_axioms PhysicalPositivity
#audit_axioms physicalPositivity_nonneg_of_sectors
