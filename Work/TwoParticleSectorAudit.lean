import BookProof.ChapterReducingSubspaceEsa
import BookProof.ChapterTwoParticleSectorEsa
import BookProof.ChapterGroupAverageEsa

/-!
# Axiom audit for the sector-reduction wave

Every result of `BookProof/ChapterReducingSubspaceEsa.lean` and
`BookProof/ChapterTwoParticleSectorEsa.lean` should report only the three standard axioms
`propext`, `Classical.choice`, `Quot.sound`.
-/

-- the reduction principle
#print axioms BookProof.ReducedEsa.IsReducingProjection.apply_of_mem_range
#print axioms BookProof.ReducedEsa.map_mem_sector
#print axioms BookProof.ReducedEsa.symmetricOn_redOp
#print axioms BookProof.ReducedEsa.deficiencyTrivialAt_red
#print axioms BookProof.ReducedEsa.essentiallySelfAdjointOn_red

-- the two sectors of a self-inverse isometry
#print axioms BookProof.ReducedEsa.symmetric_of_involutive_isometry
#print axioms BookProof.ReducedEsa.isReducingProjection_symProj
#print axioms BookProof.ReducedEsa.isReducingProjection_asymProj
#print axioms BookProof.ReducedEsa.commutes_symProj
#print axioms BookProof.ReducedEsa.commutes_asymProj
#print axioms BookProof.ReducedEsa.essentiallySelfAdjointOn_symSector
#print axioms BookProof.ReducedEsa.essentiallySelfAdjointOn_asymSector
#print axioms BookProof.ReducedEsa.mem_sector_symProj_iff
#print axioms BookProof.ReducedEsa.mem_sector_asymProj_iff

-- the swap of the two-particle space
#print axioms BookProof.TwoParticleSector.swapTwo_tmul
#print axioms BookProof.TwoParticleSector.swapTwo_involutive
#print axioms BookProof.TwoParticleSector.swapTwo_inner
#print axioms BookProof.TwoParticleSector.inclPow_swapDom
#print axioms BookProof.TwoParticleSector.derPow_two_tmul
#print axioms BookProof.TwoParticleSector.derPow_swapDom
#print axioms BookProof.TwoParticleSector.swapH_mem_sectorDom
#print axioms BookProof.TwoParticleSector.swapDom_mem_corePow
#print axioms BookProof.TwoParticleSector.swapH_mem_sectorCore
#print axioms BookProof.TwoParticleSector.sectorOp_swapH
#print axioms BookProof.TwoParticleSector.restrictOp_sectorOp_swapH

-- the bosonic and fermionic sectors
#print axioms BookProof.TwoParticleSector.isReducingProjection_bosonicProj
#print axioms BookProof.TwoParticleSector.isReducingProjection_fermionicProj
#print axioms BookProof.TwoParticleSector.mem_bosonic_iff
#print axioms BookProof.TwoParticleSector.mem_fermionic_iff
#print axioms BookProof.TwoParticleSector.essentiallySelfAdjointOn_bosonic
#print axioms BookProof.TwoParticleSector.essentiallySelfAdjointOn_fermionic
#print axioms BookProof.TwoParticleSector.essentiallySelfAdjointOn_bosonic_core
#print axioms BookProof.TwoParticleSector.essentiallySelfAdjointOn_fermionic_core
#print axioms BookProof.TwoParticleSector.exists_ne_zero_bosonic
#print axioms BookProof.TwoParticleSector.exists_ne_zero_fermionic
#print axioms BookProof.TwoParticleSector.symmetricOn_bosonic
#print axioms BookProof.TwoParticleSector.symmetricOn_fermionic

-- averaging over a finite group of symmetries
#print axioms BookProof.GroupAverage.UnitaryRep.inner_act_left
#print axioms BookProof.GroupAverage.UnitaryRep.act_sum
#print axioms BookProof.GroupAverage.UnitaryRep.act_avgProj
#print axioms BookProof.GroupAverage.UnitaryRep.avgProj_of_invariant
#print axioms BookProof.GroupAverage.UnitaryRep.mem_range_avgProj_iff
#print axioms BookProof.GroupAverage.UnitaryRep.isReducingProjection_avgProj
#print axioms BookProof.GroupAverage.UnitaryRep.avgProj_mem
#print axioms BookProof.GroupAverage.UnitaryRep.commutes_avgProj
#print axioms BookProof.GroupAverage.UnitaryRep.essentiallySelfAdjointOn_invariantSector
#print axioms BookProof.GroupAverage.UnitaryRep.symmetricOn_invariantSector
#print axioms BookProof.GroupAverage.avgProj_repOfInvolution
