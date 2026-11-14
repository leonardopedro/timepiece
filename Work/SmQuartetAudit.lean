/-
Axiom audit for `BookProof.SmQuartet` (SM_ESA_COMPLETION_PLAN §47).

Every declaration below must rest on `propext`, `Classical.choice`, `Quot.sound` only.
`PhysicalPositivity` is *derived* here (`physicalPositivity_of_quartet`) rather than assumed.
-/
import BookProof.Sm.ChapterSmQuartet
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.SmQuartet

#audit_axioms BrstQuartet
#audit_axioms BrstQuartet.Q_apply_apply
#audit_axioms BrstQuartet.quartet_physProj_comp_Q
#audit_axioms BrstQuartet.mem_closed_physProj
#audit_axioms BrstQuartet.quartet_decompose
#audit_axioms BrstQuartet.kform_exact_self
#audit_axioms BrstQuartet.kform_quartet_reduce
#audit_axioms BrstQuartet.physicalPositivity_of_quartet
#audit_axioms BrstQuartet.kform_quartet_reduce_sectors
#audit_axioms BrstQuartet.physicalPositivity_of_quartet_sectors
#audit_axioms exQ
#audit_axioms exP
#audit_axioms exV
#audit_axioms exEta
#audit_axioms exQ_nil
#audit_axioms exQuartet
#audit_axioms exEta_physProj
#audit_axioms exKrein
#audit_axioms exSymm
#audit_axioms exPhysicalPositivity
#audit_axioms exE2_closed
#audit_axioms exE2_not_exact
#audit_axioms isBrst_smBrstCharge
#audit_axioms exQuartet3
#audit_axioms kform_exEtah_Q
#audit_axioms kform_exEtah_symm
#audit_axioms exNotPhysicalPositivity
