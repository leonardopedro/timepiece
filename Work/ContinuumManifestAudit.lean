/-
Axiom audit for `BookProof.OSReconstruction.ContinuumManifest` (C0 of `cftproof.md`).

The module claims: `dΓ` determines its inner matrix (`dGamma_injective`); an inner scalar
shift lifts to `c • N_out` and to nothing else (`finalHamiltonian_shift`,
`relativeGenerator_shift`); the reference subtraction leaves the vacuum as `-E_ref`;
and the negative controls reject a shifted constant, a dropped interaction, an enlarged
solver budget read as a continuum limit, and an archive adapter on a foreign family or
mismatched bases.  Every declaration below must rest on `propext`, `Classical.choice`,
`Quot.sound` only.

Run with the project toolchain: `lake build Work.ContinuumManifestAudit` (or
`lake env lean Work/ContinuumManifestAudit.lean`).
-/
import BookProof.OSReconstruction.ContinuumManifest
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.OSReconstruction.ContinuumManifest

#audit_axioms oneVec_ne_zero
#audit_axioms creA_vac
#audit_axioms dGamma_oneVec
#audit_axioms onePartVec_apply
#audit_axioms dGamma_injective

#audit_axioms NestedSpec.finalHamiltonian_shift
#audit_axioms NestedSpec.relativeGenerator_shift
#audit_axioms NestedSpec.relativeGenerator_vac
#audit_axioms NestedSpec.inner_eq_of_finalHamiltonian_eq

#audit_axioms shift_changes_model
#audit_axioms droppedInteraction_rejected
#audit_axioms physicalCutoff_withSolver
#audit_axioms krylov_not_continuum

#audit_axioms unrelatedAdapter_rejected
#audit_axioms mismatchedBasis_rejected

#audit_axioms FieldLabel.scale_ne_zero
#audit_axioms HalfSpaceData.labels_mem_positiveTime
#audit_axioms HalfSpaceData.theta_labels_dependsOn_negTime
#audit_axioms HalfSpaceData.label_outside_algebra_rejected
#audit_axioms ObservableDictionary.labels_mem_positiveTime
#audit_axioms ObservableDictionary.prior_prop_normalized
#audit_axioms ObservableDictionary.prior_corr_eq
#audit_axioms ObservableDictionary.label_outside_rejected

#audit_axioms ContinuumWitness.family_eq
#audit_axioms ContinuumWitness.basis_eq
#audit_axioms ContinuumWitness.labels_mem_positiveTime
#audit_axioms ContinuumWitness.prior_prop_normalized
#audit_axioms ContinuumWitness.label_outside_rejected
#audit_axioms ContinuumWitness.family_unique
