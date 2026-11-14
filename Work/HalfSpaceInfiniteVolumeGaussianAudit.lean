/-
Axiom audit for `BookProof.OSReconstruction.HalfSpaceInfiniteVolumeGaussian`.

That module builds the infinite-volume free-field Gaussian state on `ℕ → Config` as the
Ionescu–Tulcea product `Measure.infinitePi` of the one-block Gaussian reference law, proves that
it coincides with Mathlib's explicit Ionescu–Tulcea tower `Measure.infinitePiNat`, records its
finite cylinder marginals, and identifies the one-block marginal
(`map_blockProj_freeFieldInfinite`) as the pushforward along the block projection.  Every theorem
below must rest on `propext`, `Classical.choice`, `Quot.sound` only.
-/
import BookProof.OSReconstruction.HalfSpaceInfiniteVolumeGaussian
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.OSReconstruction

#audit_axioms freeFieldInfinite_eq_infinitePiNat
#audit_axioms freeFieldInfinite_restrict
#audit_axioms freeFieldInfinite_pi
#audit_axioms freeFieldMeasure_pi
#audit_axioms map_blockProj_freeFieldInfinite
