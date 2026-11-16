/-
Axiom audit for `BookProof.OSReconstruction.GaussianMehlerControl` (C1 of `cftproof.md`).

The module claims: a finite-cutoff massive 4D Gaussian control in Mehler coordinates is a
normalized probability law; every one-mode cylinder is a centered Gaussian with the Mehler
variance; the one-mode characteristic functional and smeared second moment match that
variance; the Euclidean covariance form is invariant under the time reflection; reflected
covariance is nonnegative on positive-time half-space tests; and a positive-definite
diagonal covariance can still have a negative reflected form, so positivity of the matrix is
insufficient.  The cutoff cylinder laws agree on the common modes.  Every declaration below
must rest on `propext`, `Classical.choice`, `Quot.sound` only.

Run with the project toolchain: `lake build Work.GaussianMehlerAudit` (or
`lake env lean Work/GaussianMehlerAudit.lean`).
-/
import BookProof.OSReconstruction.GaussianMehlerControl
import BookProof.OSReconstruction.GaussianMehlerCylinderRP
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.OSReconstruction

#audit_axioms spatialEigenvalue_nonneg
#audit_axioms variance_pos
#audit_axioms variance_symm_ge_antisymm
#audit_axioms law_isProbability
#audit_axioms marginal
#audit_axioms charFun_one_mode
#audit_axioms second_moment

#audit_axioms covBilin_self_nonneg
#audit_axioms reflectMehler_involutive
#audit_axioms reflection_invariant
#audit_axioms rp_covariance

#audit_axioms badVariance_pos
#audit_axioms bad_rp_fails

#audit_axioms spatialEigenvalue_embed
#audit_axioms variance_embed
#audit_axioms marginal_embed

/-! ## The all-degree lift (`GaussianMehlerCylinderRP`) -/

#audit_axioms shiftVariance_nonneg
#audit_axioms noiseVariance_pos
#audit_axioms measurable_kernelMap
#audit_axioms kernelLaw_isProbability
#audit_axioms kernelLaw_reflectionPositive
#audit_axioms kernelLaw_reflectionPositive_of_integrable
#audit_axioms timeZero_reflect
#audit_axioms timeOne_reflect
#audit_axioms sliceVariance_eq
