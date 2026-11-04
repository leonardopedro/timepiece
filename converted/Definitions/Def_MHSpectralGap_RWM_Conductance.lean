import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MHSpectralGap.RWM

/-- The conductance (2.6), p. 14:
`C = inf_{μ(A) ≤ 1/2} ∫_A P(x, Aᶜ) dμ(x) / μ(A)`, the infimum taken over measurable `A`
with `0 < μ(A) ≤ 1/2`, computed in `[0, ∞]` (equal to `∞` if no such `A` exists). -/
noncomputable def conductance {X : Type*} [MeasurableSpace X] (P : ProbabilityTheory.Kernel X X)
    (μ : Measure X) : ℝ≥0∞ :=
  ⨅ (A : Set X) (_ : MeasurableSet A) (_ : 0 < μ A) (_ : μ A ≤ 1 / 2),
    (∫⁻ x in A, P x Aᶜ ∂μ) / μ A

/-- The expected acceptance probability of a proposal from `x`, p. 14:
`α(x) = ∫ α(x, y) Q(x, dy)`. -/
noncomputable def accBar {X : Type*} [MeasurableSpace X] (Q : ProbabilityTheory.Kernel X X)
    (α : X → X → ℝ≥0∞) (x : X) : ℝ≥0∞ :=
  ∫⁻ y, α x y ∂(Q x)

end MHSpectralGap.RWM
