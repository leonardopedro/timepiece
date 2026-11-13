/-
Axiom audit for `BookProof.SmGradDomStructural` (SM_ESA_COMPLETION_PLAN §49 / P4).

Every declaration below must rest on `propext`, `Classical.choice`, `Quot.sound` only.
The module proves the *structural* reason `GradDom` holds — a sum of squares plus a coercive
quadratic with linear form-gradients — and the model case `X₀²X₁² + X₀² + X₁²`.  It does **not**
check the per-form support facts for the 49 `smPhi` forms, nor transport the pointwise bound to
`GradDom`'s `L²` form — which is now done: the linear-form bridge (`linForm`,
`sq_polyW_linForm_le`, `gradBound_of_linear`) reduces the table to a `pderiv` computation, and
`BookProof.SmGradDomTransfer` carries the pointwise bound to the `L²` form (audited in
`SmGradDomTransferAudit`), and `smPotPoly_eq_wsSum` is the identification that lets the two meet.  So `PotSelfBound` stays a hypothesis for exactly one reason: the support table itself is not
written down.
-/
import BookProof.Sm.ChapterSmGradDomStructural
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.SmGradDomStructural

#audit_axioms polyW_add
#audit_axioms polyW_sum
#audit_axioms polyW_mul
#audit_axioms polyW_C_eq
#audit_axioms polyW_X_eq
#audit_axioms realCoeff_pderiv'
#audit_axioms polyW_pderiv_sq
#audit_axioms pderiv_sum_sq_X
#audit_axioms wsSum
#audit_axioms realCoeff_wsSum
#audit_axioms polyW_wsSum
#audit_axioms polyW_pderiv_wsSum
#audit_axioms GradBound
#audit_axioms sq_pderiv_le
#audit_axioms pointwise_dom_of_sq_sum
#audit_axioms flatPlusQuad
#audit_axioms wsSum_unit_eq
#audit_axioms gradBound_flatPlusQuad
#audit_axioms gradDom_flat_plus_quadratic
#audit_axioms realCoeff_C_const
#audit_axioms linForm
#audit_axioms realCoeff_linForm
#audit_axioms polyW_linForm
#audit_axioms sq_polyW_linForm_le
#audit_axioms gradBound_of_linear
#audit_axioms linForm_unit_eq
#audit_axioms sq_polyW_linForm_le_model
#audit_axioms smPotPoly_eq_wsSum
