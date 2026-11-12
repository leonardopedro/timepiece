/-
Axiom audit for `BookProof.SmGradDomStructural` (SM_ESA_COMPLETION_PLAN §49 / P4).

Every declaration below must rest on `propext`, `Classical.choice`, `Quot.sound` only.
The module proves the *structural* reason `GradDom` holds — a sum of squares plus a coercive
quadratic with linear form-gradients — and the model case `X₀²X₁² + X₀² + X₁²`.  It does **not**
check the per-form support facts for the 49 `smPhi` forms, nor transport the pointwise bound to
`GradDom`'s `L²` form, so `PotSelfBound` stays a hypothesis for the SM's own quartic.
-/
import BookProof.Sm.ChapterSmGradDomStructural

open BookProof.SmGradDomStructural

#print axioms polyW_add
#print axioms polyW_sum
#print axioms polyW_mul
#print axioms polyW_C_eq
#print axioms polyW_X_eq
#print axioms realCoeff_pderiv'
#print axioms polyW_pderiv_sq
#print axioms pderiv_sum_sq_X
#print axioms wsSum
#print axioms realCoeff_wsSum
#print axioms polyW_wsSum
#print axioms polyW_pderiv_wsSum
#print axioms GradBound
#print axioms sq_pderiv_le
#print axioms pointwise_dom_of_sq_sum
#print axioms flatPlusQuad
#print axioms wsSum_unit_eq
#print axioms gradBound_flatPlusQuad
#print axioms gradDom_flat_plus_quadratic
