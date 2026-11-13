import BookProof.Toolbox.ChapterFockStatisticsEsa
import BookProof.Toolbox.ChapterFockStatisticsCompletion
import BookProof.RoadmapAudit.AxiomAudit

/-!
# Axiom audit for the bosonic and fermionic Fock space

Every result of `BookProof/Toolbox/ChapterFockStatisticsEsa.lean` and
`BookProof/Toolbox/ChapterFockStatisticsCompletion.lean` should report only the three standard
axioms `propext`, `Classical.choice`, `Quot.sound`.
-/

-- descent along an isometry and the sector hypothesis
#audit_axioms BookProof.FockStatistics.deficiencyTrivialAt_of_pushOp
#audit_axioms BookProof.FockStatistics.essentiallySelfAdjointOn_of_pushOp
#audit_axioms BookProof.FockStatistics.essentiallySelfAdjointOn_sectorDom_of_esa

-- the two sectors of `H^{⊗n}`, unconditionally
#audit_axioms BookProof.FockStatistics.essentiallySelfAdjointOn_bosonic_of_esa
#audit_axioms BookProof.FockStatistics.essentiallySelfAdjointOn_fermionic_of_esa
#audit_axioms BookProof.FockStatistics.essentiallySelfAdjointOn_bosonic_core_of_esa
#audit_axioms BookProof.FockStatistics.essentiallySelfAdjointOn_fermionic_core_of_esa

-- the direct sum over the particle number
#audit_axioms BookProof.FockStatistics.bosonicFock_symmetricOn
#audit_axioms BookProof.FockStatistics.fermionicFock_symmetricOn
#audit_axioms BookProof.FockStatistics.bosonicFock_esa
#audit_axioms BookProof.FockStatistics.fermionicFock_esa
#audit_axioms BookProof.FockStatistics.bosonicFockCore_esa
#audit_axioms BookProof.FockStatistics.fermionicFockCore_esa
#audit_axioms BookProof.FockStatistics.bosonicFockOp_single
#audit_axioms BookProof.FockStatistics.fermionicFockOp_single

-- the completion of a unitary representation
#audit_axioms BookProof.GroupAverage.UnitaryRep.norm_act
#audit_axioms BookProof.GroupAverage.UnitaryRep.completionRep
#audit_axioms BookProof.GroupAverage.UnitaryRep.completionRep_act_coe
#audit_axioms BookProof.GroupAverage.UnitaryRep.isClosed_sector_completionRep

-- the complete `n`-particle sectors
#audit_axioms BookProof.FockStatistics.cbosonicProj_sectorEmb
#audit_axioms BookProof.FockStatistics.cfermionicProj_sectorEmb
#audit_axioms BookProof.FockStatistics.mem_cbosonicSector_iff
#audit_axioms BookProof.FockStatistics.mem_cfermionicSector_iff
#audit_axioms BookProof.FockStatistics.cpermRep_commutes_fockSectorDom
#audit_axioms BookProof.FockStatistics.csignRep_commutes_fockSectorDom
#audit_axioms BookProof.FockStatistics.symmetricOn_cbosonic
#audit_axioms BookProof.FockStatistics.symmetricOn_cfermionic
#audit_axioms BookProof.FockStatistics.essentiallySelfAdjointOn_cbosonic
#audit_axioms BookProof.FockStatistics.essentiallySelfAdjointOn_cfermionic

-- the two Hilbert Fock spaces
#audit_axioms BookProof.FockStatistics.hbosonicFock_symmetricOn
#audit_axioms BookProof.FockStatistics.hfermionicFock_symmetricOn
#audit_axioms BookProof.FockStatistics.hbosonicFock_esa
#audit_axioms BookProof.FockStatistics.hfermionicFock_esa
#audit_axioms BookProof.FockStatistics.exists_ne_zero_cbosonic
#audit_axioms BookProof.FockStatistics.exists_ne_zero_cfermionic
#audit_axioms BookProof.FockStatistics.exists_ne_zero_hbosonicFockDom
#audit_axioms BookProof.FockStatistics.exists_ne_zero_hfermionicFockDom
