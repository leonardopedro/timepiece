import BookProof.ChapterFockStatisticsEsa
import BookProof.ChapterFockStatisticsCompletion

/-!
# Axiom audit for the bosonic and fermionic Fock space

Every result of `BookProof/ChapterFockStatisticsEsa.lean` and
`BookProof/ChapterFockStatisticsCompletion.lean` should report only the three standard
axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

-- descent along an isometry and the sector hypothesis
#print axioms BookProof.FockStatistics.deficiencyTrivialAt_of_pushOp
#print axioms BookProof.FockStatistics.essentiallySelfAdjointOn_of_pushOp
#print axioms BookProof.FockStatistics.essentiallySelfAdjointOn_sectorDom_of_esa

-- the two sectors of `H^{⊗n}`, unconditionally
#print axioms BookProof.FockStatistics.essentiallySelfAdjointOn_bosonic_of_esa
#print axioms BookProof.FockStatistics.essentiallySelfAdjointOn_fermionic_of_esa
#print axioms BookProof.FockStatistics.essentiallySelfAdjointOn_bosonic_core_of_esa
#print axioms BookProof.FockStatistics.essentiallySelfAdjointOn_fermionic_core_of_esa

-- the direct sum over the particle number
#print axioms BookProof.FockStatistics.bosonicFock_symmetricOn
#print axioms BookProof.FockStatistics.fermionicFock_symmetricOn
#print axioms BookProof.FockStatistics.bosonicFock_esa
#print axioms BookProof.FockStatistics.fermionicFock_esa
#print axioms BookProof.FockStatistics.bosonicFockCore_esa
#print axioms BookProof.FockStatistics.fermionicFockCore_esa
#print axioms BookProof.FockStatistics.bosonicFockOp_single
#print axioms BookProof.FockStatistics.fermionicFockOp_single

-- the completion of a unitary representation
#print axioms BookProof.GroupAverage.UnitaryRep.norm_act
#print axioms BookProof.GroupAverage.UnitaryRep.completionRep
#print axioms BookProof.GroupAverage.UnitaryRep.completionRep_act_coe
#print axioms BookProof.GroupAverage.UnitaryRep.isClosed_sector_completionRep

-- the complete `n`-particle sectors
#print axioms BookProof.FockStatistics.cbosonicProj_sectorEmb
#print axioms BookProof.FockStatistics.cfermionicProj_sectorEmb
#print axioms BookProof.FockStatistics.mem_cbosonicSector_iff
#print axioms BookProof.FockStatistics.mem_cfermionicSector_iff
#print axioms BookProof.FockStatistics.cpermRep_commutes_fockSectorDom
#print axioms BookProof.FockStatistics.csignRep_commutes_fockSectorDom
#print axioms BookProof.FockStatistics.symmetricOn_cbosonic
#print axioms BookProof.FockStatistics.symmetricOn_cfermionic
#print axioms BookProof.FockStatistics.essentiallySelfAdjointOn_cbosonic
#print axioms BookProof.FockStatistics.essentiallySelfAdjointOn_cfermionic

-- the two Hilbert Fock spaces
#print axioms BookProof.FockStatistics.hbosonicFock_symmetricOn
#print axioms BookProof.FockStatistics.hfermionicFock_symmetricOn
#print axioms BookProof.FockStatistics.hbosonicFock_esa
#print axioms BookProof.FockStatistics.hfermionicFock_esa
#print axioms BookProof.FockStatistics.exists_ne_zero_cbosonic
#print axioms BookProof.FockStatistics.exists_ne_zero_cfermionic
#print axioms BookProof.FockStatistics.exists_ne_zero_hbosonicFockDom
#print axioms BookProof.FockStatistics.exists_ne_zero_hfermionicFockDom
