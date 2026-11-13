import BookProof.ChapterNonnegSemigroupGenerator
import BookProof.RoadmapAudit.AxiomAudit

/-!
Axiom audit for the operator-thread wave that identifies the **generator** of the
contraction semigroup `e^{-tT}` of a non-negative self-adjoint linear relation
(`CONSOLIDATED_PLAN.md`).  Every result below must report only `propext`,
`Classical.choice` and `Quot.sound`.
-/

-- Positivity.
#audit_axioms BookProof.NonnegSemigroupGenerator.expNeg_nonneg
#audit_axioms BookProof.NonnegSemigroupGenerator.semigroupS_nonneg

-- Strong continuity in the time variable.
#audit_axioms BookProof.NonnegSemigroupGenerator.semigroupS_congr
#audit_axioms BookProof.NonnegSemigroupGenerator.norm_semigroupS_sub_semigroupS_le
#audit_axioms BookProof.NonnegSemigroupGenerator.semigroupS_uniformly_continuous

-- Commutation with the resolvent and invariance of the domain.
#audit_axioms BookProof.NonnegSemigroupGenerator.commute_yosidaAt_invCLMAt
#audit_axioms BookProof.NonnegSemigroupGenerator.commute_approxS_invCLMAt
#audit_axioms BookProof.NonnegSemigroupGenerator.semigroupS_invCLMAt_comm
#audit_axioms BookProof.NonnegSemigroupGenerator.semigroupS_mem_of_mem

-- The generator.
#audit_axioms BookProof.NonnegSemigroupGenerator.norm_expNeg_sub_add_smul_le
#audit_axioms BookProof.NonnegSemigroupGenerator.norm_semigroupS_sub_add_smul_le
#audit_axioms BookProof.NonnegSemigroupGenerator.tendsto_semigroupS_difference_quotient
#audit_axioms BookProof.NonnegSemigroupGenerator.tendsto_semigroupS_difference_quotient_at

-- Exponential decay from a spectral lower bound.
#audit_axioms BookProof.NonnegSemigroupGenerator.norm_expNeg_le_exp
#audit_axioms BookProof.NonnegSemigroupGenerator.yosidaCLM_ge
#audit_axioms BookProof.NonnegSemigroupGenerator.norm_semigroupS_le_exp
