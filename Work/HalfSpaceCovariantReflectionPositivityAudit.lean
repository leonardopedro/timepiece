/-
Axiom audit for `BookProof.OSReconstruction.HalfSpaceCovariantReflectionPositivity`.

That module proves **reflection positivity for a covariant state**: the two halves are white noise
shifted by a common random vector `T`, so they are coupled (the coupling map `covMap` mixes `T` into
both halves).  For a bounded measurable observable of one half the OS form is the `ν`-average of
`(∫ F (t + x) ∂γ)²`, hence nonnegative — `covState_reflectionPositive`.  Every theorem below must
rest on `propext`, `Classical.choice`, `Quot.sound` only.
-/
import BookProof.OSReconstruction.HalfSpaceCovariantReflectionPositivity
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.OSReconstruction

#audit_axioms measurable_covMap
#audit_axioms covState_isProbability
#audit_axioms covState_reflectionPositive
