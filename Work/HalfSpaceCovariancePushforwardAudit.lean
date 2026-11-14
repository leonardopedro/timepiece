/-
Axiom audit for `BookProof.OSReconstruction.HalfSpaceCovariancePushforward`.

That module builds a **non-diagonal covariance pushforward** on the two-site truncation: the
Cholesky map `p ↦ (p.1, ρ p.1 + s p.2)` pushes the product of two unit Gaussians to a state whose
covariance is `ρ` off the diagonal and `1` on it (`corrLaw_cov`, `corrLaw_var`), whose covariance
matrix has finite Hilbert–Schmidt norm `2 + 2ρ²` (`covMatrix_hsNormSq`), and which for
`ρ = 1/(1+m²)` equals `λ • (−Δ+m²)⁻¹` (`covMatrix_eq_lapInv`).  Every theorem below must rest on
`propext`, `Classical.choice`, `Quot.sound` only.
-/
import BookProof.OSReconstruction.HalfSpaceCovariancePushforward
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.OSReconstruction

#audit_axioms cov_fst_snd_refPair
#audit_axioms integral_sq_gaussUnit
#audit_axioms cov_fst_fst_refPair
#audit_axioms cov_mix_refPair
#audit_axioms corrLaw_cov
#audit_axioms corrLaw_var
#audit_axioms covMatrix_hsNormSq
#audit_axioms covMatrix_eq_lapInv
