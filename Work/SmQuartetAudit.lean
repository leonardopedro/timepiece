/-
Axiom audit for `BookProof.SmQuartet` (SM_ESA_COMPLETION_PLAN §47).

Every declaration below must rest on `propext`, `Classical.choice`, `Quot.sound` only.
`BrstQuartet` is data (the model's b-ghost and physical projector), not a theorem.
-/
import BookProof.Sm.ChapterSmQuartet

open BookProof.SmQuartet

#print axioms BrstQuartet
#print axioms apply_apply_eq_zero
#print axioms quartet_QPQ
#print axioms quartet_physProj_comp_Q
#print axioms quartet_decompose
#print axioms kform_quartet_reduce
#print axioms kform_quartet_reduce_sectors
#print axioms inner_self_re_eq_norm_sq
#print axioms physicalPositivity_of_quartet
#print axioms physicalPositivity_of_quartet_sectors
#print axioms isBrst_of_mul_eq_zero
#print axioms exQuartet'
#print axioms exPhysicalPositivity
#print axioms exE2_not_exact
