/-
Axiom audit for `BookProof.SmSectorFormDomain` (SM_ESA_COMPLETION_PLAN §45).

Every declaration below must rest on `propext`, `Classical.choice`, `Quot.sound` only.
-/
import BookProof.Sm.ChapterSmSectorFormDomain

open BookProof.SmSectorFormDomain

#print axioms deltaFun
#print axioms deltaFun_ofLp_self
#print axioms deltaFun_ofLp_ne
#print axioms deltaFun_norm
#print axioms deltaFun_mem_core
#print axioms coreComp_deltaFun
#print axioms coreComp_deltaFun_ne
#print axioms coupledParity_deltaFun
#print axioms deltaFun_mem_evenSpace_iff
#print axioms coupledOp_one_deltaFun
#print axioms coupledOp_one_add_deltaFun
#print axioms fockSign_empty
#print axioms fockSign_singleton
#print axioms scalarBound_of_evenSectorBound
#print axioms scalarBound_of_oddSectorBound
#print axioms sectorComparison_iff_formDomainComparison
#print axioms sectorComparison_const_in_sector
