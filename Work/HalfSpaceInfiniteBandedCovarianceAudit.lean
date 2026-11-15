/-
Axiom audit for `BookProof.OSReconstruction.HalfSpaceInfiniteBandedCovariance`.

That module records the bi-infinite width-`k` kernel `bandedCovZ` on `ℤ` — the local limit
of the finite-volume banded chain covariance — and proves its diagonal `1 + ρ² k`
(`bandedCovZ_self`), the entries at forward and backward distance `r` (`bandedCovZ_forward`,
`bandedCovZ_back`), symmetry (`bandedCovZ_comm`), that it vanishes off the band
`|j - i| ≤ k` (`bandedCovZ_banded`), and the squared `ℓ²` row norm: the `2k + 1` window sum
(`bandedCovZ_row_sum`), the full sum over `ℤ` (`bandedCovZ_row_tsum`), its closed form — the
same per-site factor as `bandCov_hsNormSq` (`bandedCovZ_row_tsum_closed`) — the widths `1` and `0`
(`bandedCovZ_row_tsum_one`, `bandedCovZ_row_tsum_zero`), and agreement of the row norm with the
finite-volume `bandCov_row_sum` (`bandedCovZ_row_tsum_eq_bandCov_row_sum`).  It also proves the
kernel's positive semidefiniteness: the autocorrelation identity for the one-sided weight
(`weight_conv`), the weight-sum representation of the kernel (`bandedCovZ_eq_weight_sum`), the
quadratic form as an explicit sum of squares (`bandedCovZ_quadForm_eq_sum_sq`) and hence
nonnegativity (`bandedCovZ_posSemidef`).  Positivity is strict off zero
(`bandedCovZ_quadForm_eq_zero_iff`, `bandedCovZ_posDef`), the kernel is Toeplitz
(`bandedCovZ_translate`, `bandedCovZ_row_tsum_translate`, `bandedCovZ_quadForm_translate`), and
it is **not** reflection positive on a half-line for `θ i = -i`
(`bandedCovZ_reflectionForm_neg`, `bandedCovZ_not_reflectionPositive`).
The module docstring states the boundary honestly: no Gaussian measure on `ℤ → ℝ` is built
(no Kolmogorov consistency in this Mathlib), and a banded Toeplitz matrix is not
Hilbert–Schmidt on `ℓ²(ℤ)`, so the finite-volume HS square root does not survive the limit.
Every theorem must rest on `propext`, `Classical.choice`, `Quot.sound` only.
-/
import BookProof.OSReconstruction.HalfSpaceInfiniteBandedCovariance
import BookProof.RoadmapAudit.AxiomAudit

open BookProof.OSReconstruction

#audit_axioms bandedCovZ_self
#audit_axioms bandedCovZ_forward
#audit_axioms bandedCovZ_back
#audit_axioms bandedCovZ_comm
#audit_axioms bandedCovZ_banded
#audit_axioms bandedCovZ_row_sum
#audit_axioms bandedCovZ_row_tsum
#audit_axioms bandedCovZ_row_tsum_closed
#audit_axioms bandedCovZ_row_tsum_one
#audit_axioms bandedCovZ_row_tsum_zero
#audit_axioms bandedCovZ_row_tsum_eq_bandCov_row_sum
#audit_axioms weight_conv
#audit_axioms bandedCovZ_eq_weight_sum
#audit_axioms bandedCovZ_quadForm_eq_sum_sq
#audit_axioms bandedCovZ_posSemidef
#audit_axioms bandedCovZ_quadForm_eq_zero_iff
#audit_axioms bandedCovZ_posDef
#audit_axioms bandedCovZ_translate
#audit_axioms bandedCovZ_row_tsum_translate
#audit_axioms bandedCovZ_quadForm_translate
#audit_axioms bandedCovZ_reflectionForm_neg
#audit_axioms bandedCovZ_not_reflectionPositive
