/-
Axiom audit for `BookProof.OSReconstruction.HalfSpaceInfiniteVolumePositivity`.

That module proves **reflection positivity of the infinite-volume free-field state**: the state is
written in half coordinates (`splitFreeField`), the reflection swaps the halves of every block
(`chainReflect`), and for a positive-time cylinder observable (a finite product over time slices of
functions of the positive half) the OS form is nonnegative — `posCylinder_reflectionPositive`, via
`integral_restrict_infinitePi`.  Every theorem below must rest on `propext`, `Classical.choice`,
`Quot.sound` only.

The final three entries cover the widening from slice products to the whole positive-time algebra:
`map_pi_prod_pi` (a finite product of pair laws separates into the product of the two
half-marginals) and `posCyl_reflectionPositive` (arbitrary measurable cylinder observables).
-/
import BookProof.OSReconstruction.HalfSpaceInfiniteVolumePositivity
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.OSReconstruction

#audit_axioms splitFreeField_isProbability
#audit_axioms chainReflect_involutive
#audit_axioms measurable_chainReflect
#audit_axioms posCylinder_reflect
#audit_axioms posCylinder_reflectionPositive
#audit_axioms map_pi_prod_pi
#audit_axioms posCyl_reflect
#audit_axioms posCyl_reflectionPositive
