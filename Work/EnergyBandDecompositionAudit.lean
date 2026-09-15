import BookProof.ChapterEnergyBandDecomposition

/-!
# Axiom audit for `BookProof.ChapterEnergyBandDecomposition`

Run with `lake build Work.EnergyBandDecompositionAudit`.  Each line must report
only `propext`, `Classical.choice`, `Quot.sound`.
-/

#print axioms BookProof.EnergyBandDecomposition.mem_band_iff_floor
#print axioms BookProof.EnergyBandDecomposition.band_pairwise_disjoint
#print axioms BookProof.EnergyBandDecomposition.iUnion_band
#print axioms BookProof.EnergyBandDecomposition.energy_sub_scalar_lt
#print axioms BookProof.EnergyBandDecomposition.tsum_bandPart
#print axioms BookProof.EnergyBandDecomposition.lintegral_eq_tsum_band
#print axioms BookProof.EnergyBandDecomposition.norm_mul_energy_sub_scalar_le
#print axioms BookProof.EnergyBandDecomposition.norm_evolution_sub_scalar_le
#print axioms BookProof.EnergyBandDecomposition.evolution_preserves_band
