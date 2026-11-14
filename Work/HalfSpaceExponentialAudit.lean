/-
Axiom audit for `BookProof.OSReconstruction.HalfSpaceExponential`.

`cftproof.md` E3 lists "the exponential `e^{−τH}`" as a missing concrete input:
`HalfSpaceGenerator` can only identify the half-space generator conditionally on the `hflow`
hypothesis, the local form of
`P(τ) = e^{−τH}`.  The module constructs that exponential for a bounded `H` and proves the semigroup
law, self-adjointness, contractivity under a nonnegative quadratic form, strong continuity at `0⁺`,
and the generator statement in the exact shape `hsGenerator_eq_neg` consumes.  Every theorem below
must rest on `propext`, `Classical.choice`, `Quot.sound` only.
-/
import BookProof.OSReconstruction.HalfSpaceExponential
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.OSReconstruction

#audit_axioms hsExpOp_apply
#audit_axioms hsExpOp_zero
#audit_axioms commute_smul_neg
#audit_axioms hsExpOp_add
#audit_axioms hsExpOp_isSelfAdjoint
#audit_axioms hasDerivAt_hsExpOp
#audit_axioms hasDerivAt_hsExpOp_apply
#audit_axioms hsExpOp_hasDerivWithinAt_zero
#audit_axioms norm_hsExpOp_antitone
#audit_axioms norm_hsExpOp_le
#audit_axioms continuous_hsExpOp
#audit_axioms tendsto_hsExpOp_zero
