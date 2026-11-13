/-
Axiom audit for `BookProof.SmGradDomTransfer` (SM_ESA_COMPLETION_PLAN §52 / P4).

Every declaration below must rest on `propext`, `Classical.choice`, `Quot.sound` only.  The module
carries the pointwise gradient domination to the `L²` inequality `GradDom` by Gaussian-integral
monotonicity, and `exists_potSelfBound_of_gradBound` composes that with the per-form `GradBound`
table, so `PotSelfBound` is a hypothesis on one finite algebraic input.
-/
import BookProof.Sm.ChapterSmGradDomTransfer
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.SmGradDomTransfer

#audit_axioms eval_real_of_realCoeff
#audit_axioms norm_eval_sq_eq_polyW_sq
#audit_axioms eval_cpoly_self_re
#audit_axioms eval_cpoly_mul_re
#audit_axioms eval_sum_cpoly_re
#audit_axioms l2_gradDom_of_pointwise
#audit_axioms exists_potSelfBound_of_pointwise
#audit_axioms exists_potSelfBound_of_gradBound
