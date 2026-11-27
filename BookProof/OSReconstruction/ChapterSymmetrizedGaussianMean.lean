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

/-- The symmetric mixture is invariant under the sign flip `x ↦ −x`: it swaps the two
    Gaussian components.  This is the distribution-level form of `⟨φ⟩ = 0`. -/
theorem symmetrizedGaussian_neg_invariant (v : ℝ) (σ : NNReal) :
    (symmetrizedGaussian v σ).map (fun x : ℝ => -x) = symmetrizedGaussian v σ := by
  dsimp [symmetrizedGaussian]
  rw [Measure.map_add _ _ measurable_neg, Measure.map_smul, Measure.map_smul]
  rw [gaussianReal_map_neg, gaussianReal_map_neg]
  simp [add_comm]

/-- Every power of the identity is integrable under the symmetrized mixture. -/
lemma integrable_pow_symmetrized (v : ℝ) (σ : NNReal) (n : ℕ) :
    Integrable (fun x : ℝ => x ^ n) (symmetrizedGaussian v σ) := by
  have hgauss (m : ℝ) : Integrable (fun x : ℝ => x ^ n) (gaussianReal m σ) := by
    by_cases hn : n = 0
    · subst n
      simp
    · have hmem : MemLp (id : ℝ → ℝ) (n : ENNReal) (gaussianReal m σ) := by
        simpa using (memLp_id_gaussianReal (μ := m) (v := σ) (n : NNReal))
      have hi : Integrable (fun x : ℝ => ‖x‖ ^ n) (gaussianReal m σ) :=
        hmem.integrable_norm_pow hn
      have hae : AEStronglyMeasurable (fun x : ℝ => x ^ n) (gaussianReal m σ) := by fun_prop
      rw [← integrable_norm_iff hae]
      simpa [Real.norm_eq_abs, abs_pow] using hi
  dsimp [symmetrizedGaussian]
  exact (hgauss v).smul_measure (by norm_num) |>.add_measure
    ((hgauss (-v)).smul_measure (by norm_num))

/-- Every odd moment of the symmetric mixture vanishes, by sign-flip invariance. -/
theorem symmetrizedGaussian_odd_moment_eq_zero (v : ℝ) (σ : NNReal) (k : ℕ) :
    (∫ x : ℝ, x ^ (2 * k + 1) ∂symmetrizedGaussian v σ) = 0 := by
  let μ := symmetrizedGaussian v σ
  have hinv : Measure.map (fun x : ℝ => -x) μ = μ := symmetrizedGaussian_neg_invariant v σ
  have hmap := integral_map (by fun_prop : AEMeasurable (fun x : ℝ => -x) μ)
    (by fun_prop : AEStronglyMeasurable (fun x : ℝ => x ^ (2 * k + 1))
      (Measure.map (fun x : ℝ => -x) μ))
  have hneg : (fun x : ℝ => (-x) ^ (2 * k + 1)) = fun x => -x ^ (2 * k + 1) := by
    funext x
    rw [neg_pow]
    simp [show Odd (2 * k + 1) from ⟨k, by ring⟩]
  rw [hinv, hneg] at hmap
  have hI : Integrable (fun x : ℝ => x ^ (2 * k + 1)) μ := by
    exact integrable_pow_symmetrized v σ (2 * k + 1)
  have hnegint : (∫ x : ℝ, -x ^ (2 * k + 1) ∂μ) = -(∫ x : ℝ, x ^ (2 * k + 1) ∂μ) :=
    integral_neg (fun x : ℝ => x ^ (2 * k + 1))
  rw [hnegint] at hmap
  change (∫ x : ℝ, x ^ (2 * k + 1) ∂μ) = 0
  linarith

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
