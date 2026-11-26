import Mathlib
import Mathlib.Probability.Distributions.Gaussian.Real

/-!
# Chapter SymmetrizedGaussianMean — H5's symmetric-boundary ⟨φ⟩ = 0 at density level

The readiness ledger of `cftproof.md` records H5's symmetric-boundary theorem
`⟨φ⟩ = 0` as an open item.  This chapter proves its finite-dimensional density-level form: the
equally weighted mixture of the Gaussian centered at `v` and the Gaussian centered at `−v` is a
probability measure whose first moment vanishes.  This is the expectation-level content of
symmetrizing over the two degenerate vacua before the infinite-volume limit.

No physical Higgs/φ⁴ ground state, no infinite-volume superselection sector and no cluster or
positive-overlap statement is claimed.
-/

noncomputable section

namespace BookProof.SymmetrizedGaussianMean

open MeasureTheory ProbabilityTheory Filter Topology

/-- The equally weighted mixture of the two Gaussians centered at `±v`. -/
def symmetrizedGaussian (v : ℝ) (σ : NNReal) : Measure ℝ :=
  (1 / 2 : ENNReal) • gaussianReal v σ + (1 / 2 : ENNReal) • gaussianReal (-v) σ

/-- The symmetrized mixture is a probability measure. -/
instance symmetrizedGaussian_isProbability (v : ℝ) (σ : NNReal) :
    IsProbabilityMeasure (symmetrizedGaussian v σ) := by
  constructor
  dsimp [symmetrizedGaussian]
  simpa using ENNReal.inv_two_add_inv_two

/-- The symmetric average kills the first moment, independently of `v` and `σ`. -/
theorem symmetrizedGaussian_expectation (v : ℝ) (σ : NNReal) :
    (∫ x : ℝ, x ∂symmetrizedGaussian v σ) = 0 := by
  dsimp [symmetrizedGaussian]
  rw [integral_add_measure]
  · rw [integral_smul_measure, integral_smul_measure]
    simp
  · exact ((memLp_id_gaussianReal (μ := v) (v := σ) 1).integrable le_rfl).smul_measure
      (by norm_num)
  · exact ((memLp_id_gaussianReal (μ := -v) (v := σ) 1).integrable le_rfl).smul_measure
      (by norm_num)

end BookProof.SymmetrizedGaussianMean
