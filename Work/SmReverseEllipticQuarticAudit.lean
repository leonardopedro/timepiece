/-
Axiom audit for `BookProof.SmReverseEllipticQuartic` (SM_ESA_COMPLETION_PLAN §48 / P4).

Every declaration below must rest on `propext`, `Classical.choice`, `Quot.sound` only.
The module proves `PotSelfBound` *from* the gradient domination `GradDom`; it does **not** prove
`GradDom` for `smPotPoly`, so `PotSelfBound` stays a hypothesis for the SM's own quartic.
-/
import BookProof.Sm.ChapterSmReverseEllipticQuartic
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.SmReverseEllipticQuartic

#audit_axioms sqrt_mul_le_div
#audit_axioms norm_le_of_quad_le
#audit_axioms sum_coreD_sq_le_shiftNorm_sq
#audit_axioms exists_potSelfBound_of_gradDom
#audit_axioms coerciveQuartic
#audit_axioms flatQuartic
#audit_axioms twoPoint
#audit_axioms evAt
#audit_axioms eval_coercive_zero
#audit_axioms eval_coercive_one
#audit_axioms eval_coercive_self
#audit_axioms eval_flat_zero
#audit_axioms eval_flat_one
#audit_axioms eval_flat_self
#audit_axioms gradDom_coercive_quartic
#audit_axioms not_gradDom_flat_quartic
