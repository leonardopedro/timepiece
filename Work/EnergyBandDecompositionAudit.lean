import BookProof.EnergyBand.ChapterEnergyBandDecomposition
import BookProof.RoadmapAudit.AxiomAudit

/-!
# Axiom audit for `BookProof.ChapterEnergyBandDecomposition`

Run with `lake build Work.EnergyBandDecompositionAudit`.  Each line must report
only `propext`, `Classical.choice`, `Quot.sound`.
-/

#audit_axioms BookProof.EnergyBandDecomposition.mem_band_iff_floor
#audit_axioms BookProof.EnergyBandDecomposition.band_pairwise_disjoint
#audit_axioms BookProof.EnergyBandDecomposition.iUnion_band
#audit_axioms BookProof.EnergyBandDecomposition.energy_sub_scalar_lt
#audit_axioms BookProof.EnergyBandDecomposition.tsum_bandPart
#audit_axioms BookProof.EnergyBandDecomposition.lintegral_eq_tsum_band
#audit_axioms BookProof.EnergyBandDecomposition.norm_mul_energy_sub_scalar_le
#audit_axioms BookProof.EnergyBandDecomposition.norm_evolution_sub_scalar_le
#audit_axioms BookProof.EnergyBandDecomposition.evolution_preserves_band
