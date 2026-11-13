/-
Axiom audit for `BookProof.SmSectorFormDomain` (SM_ESA_COMPLETION_PLAN §45).

Every declaration below must rest on `propext`, `Classical.choice`, `Quot.sound` only.
-/
import BookProof.Sm.ChapterSmSectorFormDomain
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.SmSectorFormDomain

#audit_axioms deltaFun
#audit_axioms deltaFun_ofLp_self
#audit_axioms deltaFun_ofLp_ne
#audit_axioms deltaFun_norm
#audit_axioms deltaFun_mem_core
#audit_axioms coreComp_deltaFun
#audit_axioms coreComp_deltaFun_ne
#audit_axioms coupledParity_deltaFun
#audit_axioms deltaFun_mem_evenSpace_iff
#audit_axioms coupledOp_one_deltaFun
#audit_axioms coupledOp_one_add_deltaFun
#audit_axioms fockSign_empty
#audit_axioms fockSign_singleton
#audit_axioms scalarBound_of_evenSectorBound
#audit_axioms scalarBound_of_oddSectorBound
#audit_axioms sectorComparison_iff_formDomainComparison
#audit_axioms sectorComparison_const_in_sector
