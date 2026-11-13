import BookProof.InducedSystems.ChapterPvmCyclicDecomposition
import BookProof.RoadmapAudit.AxiomAudit

/-!
Axiom audit for the cyclic decomposition of a projection-valued measure — the step that
removes the "multiplicity-one" boundary recorded by the converse of Mackey's imprimitivity
theorem over a continuous base (`BookProof.ChapterMackeyConverse`), whose statement is the
cyclic case and whose docstring says that the general case follows by decomposing the
Hilbert space into cyclic subspaces.

Every result below must report only `propext`, `Classical.choice` and `Quot.sound`.
-/

-- Orthogonality of two cyclic subspaces and its elementary consequences.
#audit_axioms BookProof.ChapterPvmCyclicDecomposition.orthOrbit_pairs
#audit_axioms BookProof.ChapterPvmCyclicDecomposition.OrthOrbit.symm
#audit_axioms BookProof.ChapterPvmCyclicDecomposition.orthonormal_of_orthCyclicFamily

-- Zorn: a maximal family of cyclic-orthogonal unit vectors is total.
#audit_axioms BookProof.ChapterPvmCyclicDecomposition.exists_orthCyclicFamily

-- The restriction to a closed invariant subspace is a projection-valued measure, and on the
-- cyclic subspace of `ψ` the vector `ψ` is cyclic for it.
#audit_axioms BookProof.ChapterPvmCyclicDecomposition.cyclicSubspace_invariant
#audit_axioms BookProof.ChapterPvmCyclicDecomposition.restrictSub_apply
#audit_axioms BookProof.ChapterPvmCyclicDecomposition.isCyclic_restrictCyclic
#audit_axioms BookProof.ChapterPvmCyclicDecomposition.pvmMeasure_restrictCyclic

-- The decomposition itself.
#audit_axioms BookProof.ChapterPvmCyclicDecomposition.exists_cyclic_decomposition

-- Countability of the family on a separable space.
#audit_axioms BookProof.ChapterPvmCyclicDecomposition.countable_of_orthCyclicFamily
#audit_axioms BookProof.ChapterPvmCyclicDecomposition.exists_countable_cyclic_decomposition
