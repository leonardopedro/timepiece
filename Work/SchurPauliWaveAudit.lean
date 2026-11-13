import BookProof.Realification.ChapterSchurIrreducible
import BookProof.Realification.ChapterSchurRepresentation
import BookProof.Realification.ChapterSchurTrichotomy
import BookProof.ChapterPauliFundamental
import BookProof.ChapterPauliConsequences
import BookProof.RoadmapAudit.AxiomAudit

/-!
Axiom audit for the wave that discharges the two representation-theoretic `EXTERNAL`
inputs of book chapter A: **Schur's lemma for irreducible normal systems** (Lemma 28 /
Lemma 34, the `IsSchurFull` / `IsSchurUnitary` hypotheses) and **Pauli's fundamental
theorem of the γ-matrices** (Note 36, the `PauliFundamental` hypothesis).
Every result below must report only `propext`, `Classical.choice` and `Quot.sound`.
-/

-- Schur's lemma on an arbitrary complex Hilbert space.
#audit_axioms BookProof.ChapterSchurIrreducible.rangeClosure_invariant
#audit_axioms BookProof.ChapterSchurIrreducible.rangeClosure_ne_bot
#audit_axioms BookProof.ChapterSchurIrreducible.rangeClosure_ne_top
#audit_axioms BookProof.ChapterSchurIrreducible.cfc_ne_zero_of_mem_spectrum
#audit_axioms BookProof.ChapterSchurIrreducible.spectrum_subsingleton_of_irreducible
#audit_axioms BookProof.ChapterSchurIrreducible.selfAdjoint_commutant_scalar
#audit_axioms BookProof.ChapterSchurIrreducible.commutant_scalar_of_irreducible
#audit_axioms BookProof.ChapterSchurIrreducible.isSchurFull_of_irreducible
#audit_axioms BookProof.ChapterSchurIrreducible.isSchurUnitary_of_irreducible
#audit_axioms BookProof.ChapterSchurIrreducible.commutant_eq_scalars_of_irreducible
#audit_axioms BookProof.ChapterSchurIrreducible.isIrreducible_iff_schur

-- Lemma 28 and Lemma 34.
#audit_axioms BookProof.ChapterSchurRepresentation.adjoint_uCLM
#audit_axioms BookProof.ChapterSchurRepresentation.repSystem_isNormal
#audit_axioms BookProof.ChapterSchurRepresentation.schur_unitary_representation
#audit_axioms BookProof.ChapterSchurRepresentation.schur_unitary_representation_apply
#audit_axioms BookProof.ChapterSchurRepresentation.imprimitivitySystem_isNormal
#audit_axioms BookProof.ChapterSchurRepresentation.schur_imprimitivity

-- The §A.2 trichotomy with the Schur hypothesis discharged.
#audit_axioms BookProof.ChapterSchurTrichotomy.antiisometry_unique_up_to_phase'
#audit_axioms BookProof.ChapterSchurTrichotomy.Rreal_commutant_eq_real_scalars'
#audit_axioms BookProof.ChapterSchurTrichotomy.Rcomplex_realCommutant_eq_complex'
#audit_axioms BookProof.ChapterSchurTrichotomy.Rpseudoreal_realCommutant_eq_quaternion'

-- Pauli's fundamental theorem.
#audit_axioms BookProof.ChapterPauliFundamental.clifford_key
#audit_axioms BookProof.ChapterPauliFundamental.G_orthogonal
#audit_axioms BookProof.ChapterPauliFundamental.G_traceOrth
#audit_axioms BookProof.ChapterPauliFundamental.G_linearIndependent
#audit_axioms BookProof.ChapterPauliFundamental.G_span
#audit_axioms BookProof.ChapterPauliFundamental.inter_intertwines
#audit_axioms BookProof.ChapterPauliFundamental.exists_inter_ne_zero
#audit_axioms BookProof.ChapterPauliFundamental.intertwiner_isUnit
#audit_axioms BookProof.ChapterPauliFundamental.exists_intertwiner
#audit_axioms BookProof.ChapterPauliFundamental.pauli_exists
#audit_axioms BookProof.ChapterPauliFundamental.pauli_unique
#audit_axioms BookProof.ChapterPauliFundamental.pauliFundamental
#audit_axioms BookProof.ChapterPauliFundamental.real_pauli'

-- Prop 46 with no external input.
#audit_axioms BookProof.ChapterPauliConsequences.lambda_surjective'
#audit_axioms BookProof.ChapterPauliConsequences.lambda_two_to_one'
