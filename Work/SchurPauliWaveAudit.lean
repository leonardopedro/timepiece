import BookProof.ChapterSchurIrreducible
import BookProof.ChapterSchurRepresentation
import BookProof.ChapterSchurTrichotomy
import BookProof.ChapterPauliFundamental
import BookProof.ChapterPauliConsequences

/-!
Axiom audit for the wave that discharges the two representation-theoretic `EXTERNAL`
inputs of book chapter A: **Schur's lemma for irreducible normal systems** (Lemma 28 /
Lemma 34, the `IsSchurFull` / `IsSchurUnitary` hypotheses) and **Pauli's fundamental
theorem of the γ-matrices** (Note 36, the `PauliFundamental` hypothesis).
Every result below must report only `propext`, `Classical.choice` and `Quot.sound`.
-/

-- Schur's lemma on an arbitrary complex Hilbert space.
#print axioms BookProof.ChapterSchurIrreducible.rangeClosure_invariant
#print axioms BookProof.ChapterSchurIrreducible.rangeClosure_ne_bot
#print axioms BookProof.ChapterSchurIrreducible.rangeClosure_ne_top
#print axioms BookProof.ChapterSchurIrreducible.cfc_ne_zero_of_mem_spectrum
#print axioms BookProof.ChapterSchurIrreducible.spectrum_subsingleton_of_irreducible
#print axioms BookProof.ChapterSchurIrreducible.selfAdjoint_commutant_scalar
#print axioms BookProof.ChapterSchurIrreducible.commutant_scalar_of_irreducible
#print axioms BookProof.ChapterSchurIrreducible.isSchurFull_of_irreducible
#print axioms BookProof.ChapterSchurIrreducible.isSchurUnitary_of_irreducible
#print axioms BookProof.ChapterSchurIrreducible.commutant_eq_scalars_of_irreducible
#print axioms BookProof.ChapterSchurIrreducible.isIrreducible_iff_schur

-- Lemma 28 and Lemma 34.
#print axioms BookProof.ChapterSchurRepresentation.adjoint_uCLM
#print axioms BookProof.ChapterSchurRepresentation.repSystem_isNormal
#print axioms BookProof.ChapterSchurRepresentation.schur_unitary_representation
#print axioms BookProof.ChapterSchurRepresentation.schur_unitary_representation_apply
#print axioms BookProof.ChapterSchurRepresentation.imprimitivitySystem_isNormal
#print axioms BookProof.ChapterSchurRepresentation.schur_imprimitivity

-- The §A.2 trichotomy with the Schur hypothesis discharged.
#print axioms BookProof.ChapterSchurTrichotomy.antiisometry_unique_up_to_phase'
#print axioms BookProof.ChapterSchurTrichotomy.Rreal_commutant_eq_real_scalars'
#print axioms BookProof.ChapterSchurTrichotomy.Rcomplex_realCommutant_eq_complex'
#print axioms BookProof.ChapterSchurTrichotomy.Rpseudoreal_realCommutant_eq_quaternion'

-- Pauli's fundamental theorem.
#print axioms BookProof.ChapterPauliFundamental.clifford_key
#print axioms BookProof.ChapterPauliFundamental.G_orthogonal
#print axioms BookProof.ChapterPauliFundamental.G_traceOrth
#print axioms BookProof.ChapterPauliFundamental.G_linearIndependent
#print axioms BookProof.ChapterPauliFundamental.G_span
#print axioms BookProof.ChapterPauliFundamental.inter_intertwines
#print axioms BookProof.ChapterPauliFundamental.exists_inter_ne_zero
#print axioms BookProof.ChapterPauliFundamental.intertwiner_isUnit
#print axioms BookProof.ChapterPauliFundamental.exists_intertwiner
#print axioms BookProof.ChapterPauliFundamental.pauli_exists
#print axioms BookProof.ChapterPauliFundamental.pauli_unique
#print axioms BookProof.ChapterPauliFundamental.pauliFundamental
#print axioms BookProof.ChapterPauliFundamental.real_pauli'

-- Prop 46 with no external input.
#print axioms BookProof.ChapterPauliConsequences.lambda_surjective'
#print axioms BookProof.ChapterPauliConsequences.lambda_two_to_one'
