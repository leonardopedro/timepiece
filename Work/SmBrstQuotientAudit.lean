/-
Axiom audit for `BookProof.SmBrstQuotient` (SM_ESA_COMPLETION_PLAN §46).

Every declaration below must rest on `propext`, `Classical.choice`, `Quot.sound` only.
`PhysicalPositivity` is a definition (a named input), not a theorem.
-/
import BookProof.Sm.ChapterSmBrstQuotient

open BookProof.SmBrstQuotient

#print axioms IsBrst
#print axioms gauge
#print axioms closed
#print axioms gauge_le_ker
#print axioms mem_closed_of_mem_gauge
#print axioms kform
#print axioms kform_add_right
#print axioms kform_smul_right
#print axioms kform_add_left
#print axioms kform_zero_right
#print axioms kform_ghost_null
#print axioms kform_ghost_null_right
#print axioms kform_well_defined
#print axioms U_mem_closed
#print axioms U_mem_gauge
#print axioms kform_eq_zero_of_mem_even_of_mem_odd
#print axioms kform_eq_zero_of_mem_odd_of_mem_even
#print axioms kform_quadForm_split
#print axioms kform_quadForm_nonneg
#print axioms PhysicalPositivity
#print axioms physicalPositivity_nonneg_of_sectors
