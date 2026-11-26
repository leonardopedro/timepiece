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

/-- The square of the identity is integrable under a Gaussian. -/
lemma integrable_sq_gaussian (m : ℝ) (σ : NNReal) :
    Integrable (fun x : ℝ => x ^ 2) (gaussianReal m σ) := by
  have h := (memLp_id_gaussianReal (μ := m) (v := σ) 2).integrable_norm_rpow
    (by norm_num : (2 : ENNReal) ≠ 0) (by norm_num : (2 : ENNReal) ≠ ⊤)
  simpa [Real.norm_eq_abs, sq_abs] using h

/-- The second moment of a probability measure is its variance plus the square of its mean. -/
lemma integral_sq_eq_variance_add_sq_mean {μ : Measure ℝ} [IsProbabilityMeasure μ]
    (h2 : MemLp (fun x : ℝ => x) 2 μ) :
    (∫ x, x ^ 2 ∂μ) = Var[fun x : ℝ => x; μ] + (∫ x, x ∂μ) ^ 2 := by
  let m : ℝ := ∫ x, x ∂μ
  have h1 : Integrable (fun x : ℝ => x) μ := h2.integrable (by norm_num)
  have hsq : Integrable (fun x : ℝ => x ^ 2) μ := by
    have h := h2.integrable_norm_rpow (by norm_num : (2 : ENNReal) ≠ 0)
      (by norm_num : (2 : ENNReal) ≠ ⊤)
    simpa [Real.norm_eq_abs, sq_abs] using h
  have hvar := variance_eq_integral (μ := μ) (X := fun x : ℝ => x) (by fun_prop)
  rw [hvar]
  have hexpand : (fun x : ℝ => (x - m) ^ 2) = fun x => x ^ 2 - (2 * m) * x + m ^ 2 := by
    funext x
    ring
  rw [hexpand]
  rw [integral_add]
  · rw [integral_sub]
    · rw [integral_const_mul]
      simp [m]
      ring
    · exact hsq
    · exact h1.const_mul _
  · exact hsq.sub (h1.const_mul _)
  · exact integrable_const _

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

/-- The second moment of the symmetric mixture is `σ + v²`: the common Gaussian fluctuation
    plus the squared separation of the two centers. -/
theorem symmetrizedGaussian_second_moment (v : ℝ) (σ : NNReal) :
    (∫ x : ℝ, x ^ 2 ∂symmetrizedGaussian v σ) = (σ : ℝ) + v ^ 2 := by
  dsimp [symmetrizedGaussian]
  rw [integral_add_measure]
  · rw [integral_smul_measure, integral_smul_measure]
    rw [integral_sq_eq_variance_add_sq_mean (memLp_id_gaussianReal (μ := v) (v := σ) 2)]
    rw [integral_sq_eq_variance_add_sq_mean (memLp_id_gaussianReal (μ := -v) (v := σ) 2)]
    simp
    ring
  · exact (integrable_sq_gaussian v σ).smul_measure (by norm_num)
  · exact (integrable_sq_gaussian (-v) σ).smul_measure (by norm_num)

/-- The variance of the symmetric mixture is `σ + v²`, since its mean is zero. -/
theorem symmetrizedGaussian_variance (v : ℝ) (σ : NNReal) :
    Var[fun x : ℝ => x; symmetrizedGaussian v σ] = (σ : ℝ) + v ^ 2 := by
  have hp : Integrable (fun x : ℝ => x ^ 2) ((1 / 2 : ENNReal) • gaussianReal v σ) :=
    (integrable_sq_gaussian v σ).smul_measure (by norm_num)
  have hm : Integrable (fun x : ℝ => x ^ 2) ((1 / 2 : ENNReal) • gaussianReal (-v) σ) :=
    (integrable_sq_gaussian (-v) σ).smul_measure (by norm_num)
  have h2 : MemLp (fun x : ℝ => x) 2 (symmetrizedGaussian v σ) := by
    apply (memLp_two_iff_integrable_sq (by fun_prop)).2
    dsimp [symmetrizedGaussian]
    exact hp.add_measure hm
  have h := integral_sq_eq_variance_add_sq_mean h2
  rw [symmetrizedGaussian_second_moment, symmetrizedGaussian_expectation] at h
  simpa using h.symm

end BookProof.SymmetrizedGaussianMean
