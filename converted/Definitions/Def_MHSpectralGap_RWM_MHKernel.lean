import Mathlib

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace MHSpectralGap.RWM

/-- The Metropolis–Hastings transition kernel (1.3) of Hairer–Stuart–Vollmer (p. 3):
`P(x, dz) = Q(x, dz) α(x, z) + δ_x(dz) ∫ (1 − α(x, u)) Q(x, du)`,
for a proposal kernel `Q` and an acceptance probability `α : X → X → [0, ∞]`.
It is a Markov kernel whenever `Q` is Markov, `α` is jointly measurable and `α ≤ 1`
(otherwise `Kernel.withDensity` returns the zero kernel). -/
noncomputable def mhKernel {X : Type*} [MeasurableSpace X] (Q : ProbabilityTheory.Kernel X X)
    [ProbabilityTheory.IsSFiniteKernel Q] (α : X → X → ℝ≥0∞) : ProbabilityTheory.Kernel X X :=
  Q.withDensity (fun x y => α x y) +
    ProbabilityTheory.Kernel.withDensity ProbabilityTheory.Kernel.id
      (fun x _ => ∫⁻ u, (1 - α x u) ∂(Q x))

end MHSpectralGap.RWM
