/-
Axiom audit for `BookProof.OSReconstruction.HalfSpaceChainCovariance`.

That module extends the two-site non-diagonal covariance to an `n`-site chain: white noise pushed
forward by the band matrix `1 + ρ·P_σ` has the covariance
`δ_{ij} + ρ(δ_{σ i,j} + δ_{i,σ j}) + ρ²δ_{ij}`, which vanishes off the band `{i, σ i, σ⁻¹ i}`
(`chainCov_eq_zero`) and has squared Hilbert–Schmidt norm `card ι · ((1+ρ²)² + 2ρ²)`
(`chainCov_hsNormSq`), instantiated on the `(n+1)`-site cycle by `cycleChain_cov_hsNormSq`.  Every
theorem below must rest on `propext`, `Classical.choice`, `Quot.sound` only.
-/
import BookProof.OSReconstruction.HalfSpaceChainCovariance
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.OSReconstruction

#audit_axioms covariance_eval_eval
#audit_axioms integral_eval_sq
#audit_axioms chainLaw_cov
#audit_axioms chainCov_diag
#audit_axioms chainCov_neighbour_right
#audit_axioms chainCov_neighbour_left
#audit_axioms chainCov_eq_zero
#audit_axioms chainCov_row_sum
#audit_axioms chainCov_hsNormSq
#audit_axioms cycleChain_cov_hsNormSq
#audit_axioms cycleChain_cov_eq_zero
