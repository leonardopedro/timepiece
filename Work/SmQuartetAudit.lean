/-
Axiom audit for `BookProof.SmQuartet` (SM_ESA_COMPLETION_PLAN §47).

Every declaration below must rest on `propext`, `Classical.choice`, `Quot.sound` only.
`PhysicalPositivity` is *derived* here (`physicalPositivity_of_quartet`) rather than assumed.
-/
import BookProof.Sm.ChapterSmQuartet

open BookProof.SmQuartet

#print axioms BrstQuartet
#print axioms BrstQuartet.Q_apply_apply
#print axioms BrstQuartet.quartet_physProj_comp_Q
#print axioms BrstQuartet.mem_closed_physProj
#print axioms BrstQuartet.quartet_decompose
#print axioms BrstQuartet.kform_exact_self
#print axioms BrstQuartet.kform_quartet_reduce
#print axioms BrstQuartet.physicalPositivity_of_quartet
#print axioms BrstQuartet.kform_quartet_reduce_sectors
#print axioms BrstQuartet.physicalPositivity_of_quartet_sectors
#print axioms exQ
#print axioms exP
#print axioms exV
#print axioms exEta
#print axioms exQ_nil
#print axioms exQuartet
#print axioms exEta_physProj
#print axioms exKrein
#print axioms exSymm
#print axioms exPhysicalPositivity
#print axioms exE2_closed
#print axioms exE2_not_exact
#print axioms isBrst_smBrstCharge
