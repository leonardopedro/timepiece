/-
Axiom audit for `BookProof.OSReconstruction.HalfSpaceChainBandReflectionPositivity`.

That module is the finite-volume counterpart of the infinite-volume doubled-state reflection
positivity `bandedCovZ_doubled_reflectionPositive`.  It proves that `bandCov` is positive
semidefinite, being the covariance matrix of the probability measure `bandLaw`
(`bandCov_posSemidef`); defines the OS form `doubledBandForm` of the doubled state with blocks
`[[C + 1, C ∘ θ], [θ ∘ C, C + 1]]`; rewrites it as the quadratic form of `bandCov` at the folded
test function `H p = f p + g (θ⁻¹ p)` plus the two white-noise sums
(`doubledBandForm_eq_folded`); and concludes `0 ≤ doubledBandForm σ ρ k θ f g` for every reflection
`θ` preserving `bandCov` (`bandCov_doubled_reflectionPositive`).  The shift is such a symmetry
(`iterate_apply_perm_apply`, `bandCov_shift_apply_apply`), which supplies the concrete instance
`bandCov_doubled_reflectionPositive_shift`.  Every theorem must rest on `propext`,
`Classical.choice`, `Quot.sound` only.
-/
import BookProof.OSReconstruction.HalfSpaceChainBandReflectionPositivity
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.OSReconstruction

#audit_axioms doubledBandForm
#audit_axioms bandCov_posSemidef
#audit_axioms doubledBandForm_eq_folded
#audit_axioms bandCov_doubled_reflectionPositive
#audit_axioms iterate_apply_perm_apply
#audit_axioms bandCov_shift_apply_apply
#audit_axioms bandCov_doubled_reflectionPositive_shift
