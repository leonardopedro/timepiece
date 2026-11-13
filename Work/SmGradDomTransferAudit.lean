/-
Axiom audit for `BookProof.SmGradDomTransfer` (SM_ESA_COMPLETION_PLAN §52 / P4).

Every declaration below must rest on `propext`, `Classical.choice`, `Quot.sound` only.  The module
carries the pointwise gradient domination to the `L²` inequality `GradDom` by Gaussian-integral
monotonicity, and `exists_potSelfBound_of_gradBound` composes that with the per-form `GradBound`
table, so `PotSelfBound` is a hypothesis on one finite algebraic input.
-/
import BookProof.Sm.ChapterSmGradDomTransfer

open BookProof.SmGradDomTransfer

#print axioms eval_real_of_realCoeff
#print axioms norm_eval_sq_eq_polyW_sq
#print axioms eval_cpoly_self_re
#print axioms eval_cpoly_mul_re
#print axioms eval_sum_cpoly_re
#print axioms l2_gradDom_of_pointwise
#print axioms exists_potSelfBound_of_pointwise
#print axioms exists_potSelfBound_of_gradBound
