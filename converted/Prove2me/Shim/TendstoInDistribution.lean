import Mathlib

/-!
# Shim: convergence in distribution with varying probability spaces

The platform Mathlib's `MeasureTheory.TendstoInDistribution X l Z μ ν` lets each random variable
`X i` live on its own probability measure `μ i` and the limit `Z` live on a separate probability
space `(Ω', ν)`.  The pinned Mathlib has the same name for the special case of a single
probability space (`TendstoInDistribution X l Z μ`), so the general form is re-created here under
the name `Prove2me.Shim.TendstoInDistribution`, with the same fields: every `X i` is
`μ i`-a.e. measurable, `Z` is `ν`-a.e. measurable, and the laws `(μ i).map (X i)` converge to
`ν.map Z` in the topology of weak convergence of probability measures.
-/

open MeasureTheory Filter Topology

namespace Prove2me.Shim

/-- Convergence in distribution of `X i : Ω → E` under the probability measures `μ i` to
`Z : Ω' → E` under the probability measure `ν`. -/
structure TendstoInDistribution {Ω Ω' E ι : Type*} [MeasurableSpace Ω] [MeasurableSpace Ω']
    [TopologicalSpace E] [MeasurableSpace E] [OpensMeasurableSpace E]
    (X : ι → Ω → E) (l : Filter ι) (Z : Ω' → E) (μ : ι → Measure Ω)
    [∀ i, IsProbabilityMeasure (μ i)] (ν : Measure Ω') [IsProbabilityMeasure ν] : Prop where
  forall_aemeasurable : ∀ i, AEMeasurable (X i) (μ i)
  aemeasurable_limit : AEMeasurable Z ν
  tendsto : Tendsto (β := ProbabilityMeasure E)
      (fun n ↦ ⟨(μ n).map (X n), Measure.isProbabilityMeasure_map (forall_aemeasurable n)⟩) l
      (𝓝 ⟨ν.map Z, Measure.isProbabilityMeasure_map aemeasurable_limit⟩)

end Prove2me.Shim
