module

public import Mathlib.Analysis.InnerProductSpace.Basic

/-!
# Milestone 5: Bounded stochastic-gradient noise covariance

Under a uniform gradient bound `‖∇ℓ(w)‖ ≤ M` (Milestone 4), the mini-batch gradient estimator
`g_batch` (scaled by `N / B`) deviates from the full gradient by at most `(N/B + 1) M`
everywhere (`sg_pcnl_noise_covariance_bound`).

For the covariance statement we model the randomness of the mini-batch by a finite probability
distribution `p` on a set `ι` of batch realizations (e.g. all size-`B` subsets of the data),
each realization `i` giving an estimator `sg i`. The trace of the noise covariance at `w` is
`Tr Σ(w) = 𝔼 ‖g − 𝔼 g‖² = ∑ᵢ pᵢ ‖gᵢ(w) − ∑ⱼ pⱼ gⱼ(w)‖²` (`noiseCovTrace`). We prove
`Tr Σ(w) ≤ ((N/B + 1) M)²` for every `w` (`sg_pcnl_noise_trace_bound`), a finite constant
independent of `w`.
-/

@[expose] public section

namespace BayesianTransformer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Stochastic mini-batch gradient estimator properties. -/
structure StochasticGradientEstimator (N B : ℕ) (hB : 0 < B) (hBN : B ≤ N) where
  full_grad : E → E
  batch_grad : E → E  -- Random realization
  grad_bound : ℝ
  h_bound : ∀ (w : E), ‖full_grad w‖ ≤ grad_bound
  h_batch_bound : ∀ (w : E), ‖batch_grad w‖ ≤ (N : ℝ) / (B : ℝ) * grad_bound

omit [InnerProductSpace ℝ E] in
/-- Main variance-ceiling theorem: the mini-batch noise is bounded everywhere by
`(N / B + 1) * M`. -/
theorem sg_pcnl_noise_covariance_bound
    {N B : ℕ} (hB : 0 < B) (hBN : B ≤ N)
    (sg : StochasticGradientEstimator (E := E) N B hB hBN) (w : E) :
    ‖sg.batch_grad w - sg.full_grad w‖ ≤ ((N : ℝ) / (B : ℝ) + 1) * sg.grad_bound := by
  calc ‖sg.batch_grad w - sg.full_grad w‖
      ≤ ‖sg.batch_grad w‖ + ‖sg.full_grad w‖ := norm_sub_le _ _
    _ ≤ (N : ℝ) / (B : ℝ) * sg.grad_bound + sg.grad_bound :=
        add_le_add (sg.h_batch_bound w) (sg.h_bound w)
    _ = ((N : ℝ) / (B : ℝ) + 1) * sg.grad_bound := by ring

/-- Mean of a finitely supported random vector `g` with probability weights `p`. -/
noncomputable def weightedMean {ι : Type*} [Fintype ι] (p : ι → ℝ) (g : ι → E) : E :=
  ∑ i, p i • g i

/-- Trace of the covariance of a finitely supported random vector:
`Tr Σ = 𝔼 ‖g − 𝔼 g‖²`. -/
noncomputable def noiseCovTrace {ι : Type*} [Fintype ι] (p : ι → ℝ) (g : ι → E) : ℝ :=
  ∑ i, p i * ‖g i - weightedMean p g‖ ^ 2

/-- The mean minimizes the mean-squared deviation: `𝔼 ‖g − 𝔼 g‖² ≤ 𝔼 ‖g − c‖²` for every `c`. -/
theorem noiseCovTrace_le {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp1 : ∑ i, p i = 1)
    (g : ι → E) (c : E) :
    noiseCovTrace p g ≤ ∑ i, p i * ‖g i - c‖ ^ 2 := by
  set m := weightedMean p g
  have hdecomp : ∀ i, ‖g i - c‖ ^ 2 =
      ‖g i - m‖ ^ 2 + 2 * inner ℝ (g i - m) (m - c) + ‖m - c‖ ^ 2 := by
    intro i
    rw [show g i - c = (g i - m) + (m - c) by abel, norm_add_sq_real]
  have hcross : ∑ i, p i * inner ℝ (g i - m) (m - c) = 0 := by
    have : ∑ i, p i • (g i - m) = 0 := by
      simp only [smul_sub, Finset.sum_sub_distrib, ← Finset.sum_smul, hp1, one_smul]
      exact sub_self _
    simp_rw [← real_inner_smul_left, ← sum_inner, this, inner_zero_left]
  have : ∑ i, p i * ‖g i - c‖ ^ 2 =
      noiseCovTrace p g + 2 * ∑ i, p i * inner ℝ (g i - m) (m - c) + ‖m - c‖ ^ 2 := by
    simp_rw [hdecomp, mul_add, Finset.sum_add_distrib, ← Finset.sum_mul, hp1, Finset.mul_sum]
    simp only [noiseCovTrace, one_mul, m]
    congr 2
    refine Finset.sum_congr rfl fun i _ => by ring
  rw [this, hcross]
  nlinarith [sq_nonneg ‖m - c‖]

/-- **Uniformly bounded SG-pCNL noise covariance.** Let the mini-batch be drawn from a finite
distribution `p` over batch realizations `ι`, realization `i` giving the estimator `sg i`, all
sharing the full gradient `full` and the gradient ceiling `M`. Then the trace of the noise
covariance satisfies `Tr Σ(w) ≤ ((N/B + 1) M)²` for every parameter `w`. -/
theorem sg_pcnl_noise_trace_bound
    {N B : ℕ} {hB : 0 < B} {hBN : B ≤ N}
    {ι : Type*} [Fintype ι] (p : ι → ℝ) (hp : ∀ i, 0 ≤ p i) (hp1 : ∑ i, p i = 1)
    (sg : ι → StochasticGradientEstimator (E := E) N B hB hBN)
    (full : E → E) (hfull : ∀ i, (sg i).full_grad = full)
    (M : ℝ) (hM : ∀ i, (sg i).grad_bound = M) (w : E) :
    noiseCovTrace p (fun i => (sg i).batch_grad w) ≤ (((N : ℝ) / (B : ℝ) + 1) * M) ^ 2 := by
  refine (noiseCovTrace_le p hp1 _ (full w)).trans ?_
  have hpt : ∀ i, ‖(sg i).batch_grad w - full w‖ ^ 2 ≤ (((N : ℝ) / (B : ℝ) + 1) * M) ^ 2 := by
    intro i
    have h := sg_pcnl_noise_covariance_bound hB hBN (sg i) w
    rw [hfull i, hM i] at h
    exact pow_le_pow_left₀ (norm_nonneg _) h 2
  calc ∑ i, p i * ‖(sg i).batch_grad w - full w‖ ^ 2
      ≤ ∑ i, p i * (((N : ℝ) / (B : ℝ) + 1) * M) ^ 2 :=
        Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (hpt i) (hp i)
    _ = (((N : ℝ) / (B : ℝ) + 1) * M) ^ 2 := by rw [← Finset.sum_mul, hp1, one_mul]

end BayesianTransformer
