import BookProof.ChapterPvmCyclicDecomposition

/-!
Axiom audit for the cyclic decomposition of a projection-valued measure — the step that
removes the "multiplicity-one" boundary recorded by the converse of Mackey's imprimitivity
theorem over a continuous base (`BookProof.ChapterMackeyConverse`), whose statement is the
cyclic case and whose docstring says that the general case follows by decomposing the
Hilbert space into cyclic subspaces.

Every result below must report only `propext`, `Classical.choice` and `Quot.sound`.
-/

-- Orthogonality of two cyclic subspaces and its elementary consequences.
#print axioms BookProof.ChapterPvmCyclicDecomposition.orthOrbit_pairs
#print axioms BookProof.ChapterPvmCyclicDecomposition.OrthOrbit.symm
#print axioms BookProof.ChapterPvmCyclicDecomposition.orthonormal_of_orthCyclicFamily

-- Zorn: a maximal family of cyclic-orthogonal unit vectors is total.
#print axioms BookProof.ChapterPvmCyclicDecomposition.exists_orthCyclicFamily

-- The restriction to a closed invariant subspace is a projection-valued measure, and on the
-- cyclic subspace of `ψ` the vector `ψ` is cyclic for it.
#print axioms BookProof.ChapterPvmCyclicDecomposition.cyclicSubspace_invariant
#print axioms BookProof.ChapterPvmCyclicDecomposition.restrictSub_apply
#print axioms BookProof.ChapterPvmCyclicDecomposition.isCyclic_restrictCyclic
#print axioms BookProof.ChapterPvmCyclicDecomposition.pvmMeasure_restrictCyclic

-- The decomposition itself.
#print axioms BookProof.ChapterPvmCyclicDecomposition.exists_cyclic_decomposition

-- Countability of the family on a separable space.
#print axioms BookProof.ChapterPvmCyclicDecomposition.countable_of_orthCyclicFamily
#print axioms BookProof.ChapterPvmCyclicDecomposition.exists_countable_cyclic_decomposition
