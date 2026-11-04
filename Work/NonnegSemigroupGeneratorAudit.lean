import BookProof.ChapterNonnegSemigroupGenerator

/-!
Axiom audit for the operator-thread wave that identifies the **generator** of the
contraction semigroup `e^{-tT}` of a non-negative self-adjoint linear relation
(`CONSOLIDATED_PLAN.md`).  Every result below must report only `propext`,
`Classical.choice` and `Quot.sound`.
-/

-- Positivity.
#print axioms BookProof.NonnegSemigroupGenerator.expNeg_nonneg
#print axioms BookProof.NonnegSemigroupGenerator.semigroupS_nonneg

-- Strong continuity in the time variable.
#print axioms BookProof.NonnegSemigroupGenerator.semigroupS_congr
#print axioms BookProof.NonnegSemigroupGenerator.norm_semigroupS_sub_semigroupS_le
#print axioms BookProof.NonnegSemigroupGenerator.semigroupS_uniformly_continuous

-- Commutation with the resolvent and invariance of the domain.
#print axioms BookProof.NonnegSemigroupGenerator.commute_yosidaAt_invCLMAt
#print axioms BookProof.NonnegSemigroupGenerator.commute_approxS_invCLMAt
#print axioms BookProof.NonnegSemigroupGenerator.semigroupS_invCLMAt_comm
#print axioms BookProof.NonnegSemigroupGenerator.semigroupS_mem_of_mem

-- The generator.
#print axioms BookProof.NonnegSemigroupGenerator.norm_expNeg_sub_add_smul_le
#print axioms BookProof.NonnegSemigroupGenerator.norm_semigroupS_sub_add_smul_le
#print axioms BookProof.NonnegSemigroupGenerator.tendsto_semigroupS_difference_quotient
#print axioms BookProof.NonnegSemigroupGenerator.tendsto_semigroupS_difference_quotient_at

-- Exponential decay from a spectral lower bound.
#print axioms BookProof.NonnegSemigroupGenerator.norm_expNeg_le_exp
#print axioms BookProof.NonnegSemigroupGenerator.yosidaCLM_ge
#print axioms BookProof.NonnegSemigroupGenerator.norm_semigroupS_le_exp
