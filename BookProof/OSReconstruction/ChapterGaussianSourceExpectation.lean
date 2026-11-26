import Mathlib
import Mathlib.Probability.Distributions.Gaussian.Real
import BookProof.ChapterExternalSourceLimitOrder

/-!
# Chapter GaussianSourceExpectation — H6 Route B at the measure level

`ChapterExternalSourceLimitOrder` proves the non-commuting limit order of the finite-volume
benchmark magnetization `m_V(J) = v·(VJ)/(1+VJ)`.  This chapter lifts that benchmark from a
number to an expectation: `sourceGaussian V J v σ` is the Gaussian whose mean is `m_V(J)`, so
its expectation is exactly the benchmark value and inherits both limit orders.

This is a measure-valued benchmark, not the physical Higgs/φ⁴ expectation in infinite volume.
No conditional prior refinement, nested-Fock lift or phase-disintegration match is claimed.
-/

noncomputable section

namespace BookProof.GaussianSourceExpectation

open MeasureTheory ProbabilityTheory Filter Topology
open BookProof.ExternalSourceLimitOrder

/-- The Gaussian whose mean is the finite-volume benchmark magnetization at source `J`. -/
def sourceGaussian (V : ℕ) (J v : ℝ) (σ : NNReal) : Measure ℝ :=
  gaussianReal (finiteMagnet V J v) σ

/-- Its expectation is exactly the benchmark magnetization. -/
theorem sourceGaussian_expectation (V : ℕ) (J v : ℝ) (σ : NNReal) :
    (∫ x : ℝ, x ∂sourceGaussian V J v σ) = finiteMagnet V J v := by
  simp [sourceGaussian]

/-- At fixed positive source, the Gaussian expectation tends to `v` as the volume grows. -/
theorem sourceGaussian_tendsto_volume {J v : ℝ} (hJ : 0 < J) (σ : NNReal) :
    Tendsto (fun V : ℕ => ∫ x : ℝ, x ∂sourceGaussian V J v σ) atTop (𝓝 v) := by
  simpa [sourceGaussian] using (tendsto_finiteMagnet_atTop (v := v) hJ)

/-- At fixed volume, the Gaussian expectation tends to zero as the source is removed. -/
theorem sourceGaussian_tendsto_source (V : ℕ) (v : ℝ) (σ : NNReal) :
    Tendsto (fun J : ℝ => ∫ x : ℝ, x ∂sourceGaussian V J v σ) (𝓝[>] 0) (𝓝 0) := by
  simpa [sourceGaussian] using (tendsto_finiteMagnet_nhdsWithin_zero V v)

/-- The two limit orders disagree at the level of Gaussian expectations. -/
theorem sourceGaussian_limit_order_noncommute {v : ℝ} (hv : v ≠ 0) (σ : NNReal) :
    (∀ J : ℝ, 0 < J →
      Tendsto (fun V : ℕ => ∫ x : ℝ, x ∂sourceGaussian V J v σ) atTop (𝓝 v)) ∧
      (∀ V : ℕ,
        Tendsto (fun J : ℝ => ∫ x : ℝ, x ∂sourceGaussian V J v σ) (𝓝[>] 0) (𝓝 0)) ∧
        (0 : ℝ) ≠ v := by
  exact ⟨fun J hJ => sourceGaussian_tendsto_volume hJ σ,
    fun V => sourceGaussian_tendsto_source V v σ, hv.symm⟩

end BookProof.GaussianSourceExpectation
