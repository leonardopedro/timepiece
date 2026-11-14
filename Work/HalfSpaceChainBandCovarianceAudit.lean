/-
Axiom audit for `BookProof.OSReconstruction.HalfSpaceChainBandCovariance`.

That module widens the one-step band matrix of `HalfSpaceChainCovariance` to a width-`k` band:
white noise pushed forward by `1 + ρ ∑_{a=1}^{k} P_σ^a` has covariance
`δ_{ij} + ρ ∑_a (δ_{σ^a i,j} + δ_{i,σ^a j}) + ρ² ∑_{a,b} δ_{σ^a i,σ^b j}` (`bandLaw_cov`),
supported on the band `{σ^d i : |d| ≤ k}` (`bandCov_eq_zero`), with diagonal `1 + ρ²k` on a site
with no short cycle (`bandCov_diag`) and recovering `chainCov` at `k = 1` (`bandCov_one`).  Fed into
coupled state, the off-diagonal block of `covState (bandLaw σ ρ k)` is that band
(`covState_bandLaw_cov_fst_snd`, `covState_bandLaw_cov_fst_snd_eq_zero`).  Every theorem below must
rest on `propext`, `Classical.choice`, `Quot.sound` only.
-/
import BookProof.OSReconstruction.HalfSpaceChainBandCovariance
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.OSReconstruction

#audit_axioms bandLaw_cov
#audit_axioms bandCov_eq_zero
#audit_axioms iterate_inj_of_no_short_cycle
#audit_axioms bandCov_diag
#audit_axioms bandCov_one
#audit_axioms memLp_eval_bandLaw
#audit_axioms covState_bandLaw_cov_fst_snd
#audit_axioms covState_bandLaw_cov_fst_snd_eq_zero
