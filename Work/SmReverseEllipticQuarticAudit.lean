/-
Axiom audit for `BookProof.SmReverseEllipticQuartic` (SM_ESA_COMPLETION_PLAN §48 / P4).

Every declaration below must rest on `propext`, `Classical.choice`, `Quot.sound` only.
The module proves `PotSelfBound` *from* the gradient domination `GradDom`; it does **not** prove
`GradDom` for `smPotPoly`, so `PotSelfBound` stays a hypothesis for the SM's own quartic.
-/
import BookProof.Sm.ChapterSmReverseEllipticQuartic

open BookProof.SmReverseEllipticQuartic

#print axioms sqrt_mul_le_div
#print axioms norm_le_of_quad_le
#print axioms sum_coreD_sq_le_shiftNorm_sq
#print axioms exists_potSelfBound_of_gradDom
#print axioms coerciveQuartic
#print axioms flatQuartic
#print axioms twoPoint
#print axioms evAt
#print axioms eval_coercive_zero
#print axioms eval_coercive_one
#print axioms eval_coercive_self
#print axioms eval_flat_zero
#print axioms eval_flat_one
#print axioms eval_flat_self
#print axioms gradDom_coercive_quartic
#print axioms not_gradDom_flat_quartic
