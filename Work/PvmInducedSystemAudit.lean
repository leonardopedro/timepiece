import BookProof.ChapterPvmScalarMeasure
import BookProof.ChapterPvmInducedSystem
import BookProof.ChapterPvmFibreInducedSystem

/-!
Axiom audit for the assembly of the cyclic pieces of a projection-valued measure into a
single induced system with a multiplicity (fibre) index space — the boundary recorded in
`BookProof.ChapterPvmCyclicDecomposition`.

Every result below must report only `propext`, `Classical.choice` and `Quot.sound`.
-/

-- Transport of a projection-valued measure along a unitary.
#print axioms BookProof.ChapterPvmInducedSystem.conjPvm_apply

-- The model of a cyclic piece has range exactly the cyclic subspace.
#print axioms BookProof.ChapterPvmInducedSystem.range_swIsom
#print axioms BookProof.ChapterPvmInducedSystem.cyclicSubspace_le_orthogonal

-- The Hilbert sum of the pieces.
#print axioms BookProof.ChapterPvmInducedSystem.isHilbertSum_swIsom
#print axioms BookProof.ChapterPvmInducedSystem.pvm_direct_sum_model

-- The single induced system and its fibrewise description.
#print axioms BookProof.ChapterPvmInducedSystem.linearIsometryEquiv_swIsom_pvm
#print axioms BookProof.ChapterPvmInducedSystem.pvm_induced_system
#print axioms BookProof.ChapterPvmInducedSystem.pvm_induced_system_conj
#print axioms BookProof.ChapterPvmInducedSystem.pvm_induced_system_separable

-- The general fibrewise-action principle for a Hilbert sum.
#print axioms BookProof.ChapterHilbertSumIntertwine.linearIsometryEquiv_intertwine

-- `L²(X, μ; ℓ²(ι))` is the Hilbert sum of copies of `L²(X, μ)`, compatibly with
-- multiplication by indicators.
#print axioms BookProof.ChapterL2FibreSum.isHilbertSum_fibreEmb
#print axioms BookProof.ChapterL2FibreSum.orthogonal_iSup_range_fibreEmb
#print axioms BookProof.ChapterL2FibreSum.fibreEquiv_proj

-- The induced system with a multiplicity (fibre) Hilbert space.
#print axioms BookProof.ChapterPvmFibreInducedSystem.induced_system_of_isHilbertSum
#print axioms BookProof.ChapterPvmFibreInducedSystem.pvm_induced_system_homogeneous

-- The scalar spectral measure and quasi-invariance without a cyclic vector.
#print axioms BookProof.ChapterPvmScalarMeasure.p_eq_zero_of_forall_measure_zero
#print axioms BookProof.ChapterPvmScalarMeasure.scalarMeasure_eq_zero_iff_p_eq_zero
#print axioms BookProof.ChapterPvmScalarMeasure.exists_scalarMeasure
#print axioms BookProof.ChapterPvmScalarMeasure.exists_quasiInvariant_scalarMeasure
#print axioms BookProof.ChapterPvmScalarMeasure.exists_induced_system_in_measure_class
