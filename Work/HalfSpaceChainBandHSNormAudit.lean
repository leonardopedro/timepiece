/-
Axiom audit for `BookProof.OSReconstruction.HalfSpaceChainBandHSNorm`.

That module proves the off-diagonal coefficients of the width-`k` banded chain covariance and its
Hilbert–Schmidt norm: symmetry (`bandCov_comm`), the forward coefficient `ρ + ρ² (k - d)`
(`bandCov_forward`), the backward coefficient (`bandCov_backward`), the row sum over the `2k + 1`
band sites (`bandCov_row_sum`), its closed-form evaluation (`band_sum_closed`), and the squared HS
norm `card ι * ((1 + ρ²k)² + 2ρ²(k + ρk(k-1) + ρ²(k-1)k(2k-1)/6))` (`bandCov_hsNormSq`), which at
`k = 1` is `chainCov_hsNormSq` (`bandCov_hsNormSq_one`).  Every theorem must rest on `propext`,
`Classical.choice`, `Quot.sound` only.
-/
import BookProof.OSReconstruction.HalfSpaceChainBandHSNorm
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.OSReconstruction

#audit_axioms bandCov_comm
#audit_axioms bandCov_forward
#audit_axioms bandCov_backward
#audit_axioms bandCov_row_sum
#audit_axioms band_sum_closed
#audit_axioms bandCov_hsNormSq
#audit_axioms bandCov_hsNormSq_one
