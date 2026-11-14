/-
Axiom audit for `BookProof.OSReconstruction.HalfSpaceCovStateCovariance`.

That module proves the covariance matrix of the shared-shift state `covState ν` — the law of
`(T + X, T + Y)` with `T ~ ν` and `X`, `Y` independent white noise — is
`[[Cov T + 1, Cov T], [Cov T, Cov T + 1]]` (`covState_cov_fst_fst`, `covState_cov_snd_snd`,
`covState_cov_fst_snd`), and instantiates it at the banded chain law: the off-diagonal block of
`covState (chainLaw σ ρ)` is `chainCov σ ρ` and vanishes off the star `{i, σ i, σ⁻¹ i}`
(`covState_chainLaw_cov_fst_snd_eq_zero`).  Every theorem below must rest on `propext`,
`Classical.choice`, `Quot.sound` only.
-/
import BookProof.OSReconstruction.HalfSpaceCovStateCovariance
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.OSReconstruction

#audit_axioms covariance_add_add_gen
#audit_axioms covariance_fst_fst_prod
#audit_axioms covariance_snd_snd_prod
#audit_axioms covState_cov_fst_fst
#audit_axioms covState_cov_snd_snd
#audit_axioms covState_cov_fst_snd
#audit_axioms memLp_eval_chainLaw
#audit_axioms covState_chainLaw_cov_fst_fst
#audit_axioms covState_chainLaw_cov_snd_snd
#audit_axioms covState_chainLaw_cov_fst_snd
#audit_axioms covState_chainLaw_cov_fst_snd_eq_zero
