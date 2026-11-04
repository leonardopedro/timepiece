import Mathlib
import Definitions.Def_MHSpectralGap_RWM_MHKernel

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace MHSpectralGap.RWM

/-- The target (2.5), p. 14: `μ_m = γ_m = L(∑_{i=1}^m (1/i) ξ_i e_i)` with `ξ_i` i.i.d. `N(0,1)`,
as a measure on `ℝ^m = Fin m → ℝ`. Coordinate `i : Fin m` is the paper's `x_{i+1}`, so it is
`N(0, 1/(i+1)²)`, independently across coordinates. -/
noncomputable def gammaM (m : ℕ) : Measure (Fin m → ℝ) :=
  Measure.pi (fun i : Fin m => gaussianReal 0 (1 / ((i : ℝ≥0) + 1) ^ 2))

/-- The RWM proposal of Algorithm 2, p. 8: from `x`, propose `x + √(2δ) ξ` with `ξ ∼ γ_m`. -/
noncomputable def rwmProposal (m : ℕ) (δ : ℝ) :
    ProbabilityTheory.Kernel (Fin m → ℝ) (Fin m → ℝ) :=
  (ProbabilityTheory.Kernel.id ×ₖ ProbabilityTheory.Kernel.const _ (gammaM m)).map
    (fun p => p.1 + Real.sqrt (2 * δ) • p.2)

instance (m : ℕ) : IsProbabilityMeasure (gammaM m) := by
  unfold gammaM; infer_instance

instance (m : ℕ) (δ : ℝ) : ProbabilityTheory.IsMarkovKernel (rwmProposal m δ) :=
  ProbabilityTheory.Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- The RWM acceptance probability of Algorithm 2, p. 8, for the target (2.5) (`Φ = 0`,
`⟨x, C⁻¹x⟩ = ∑_{i=1}^m i² x_i²`):
`α(x, y) = 1 ∧ exp(½⟨x, C⁻¹x⟩ − ½⟨y, C⁻¹y⟩) = 1 ∧ exp(∑_i (i²/2)(x_i² − y_i²))`. -/
noncomputable def rwmAccept (m : ℕ) (x y : Fin m → ℝ) : ℝ≥0∞ :=
  ENNReal.ofReal (min 1 (Real.exp (∑ i : Fin m, ((i : ℝ) + 1) ^ 2 / 2 * (x i ^ 2 - y i ^ 2))))

/-- The RWM Markov kernel `P_m` with step size `δ` for the target `γ_m`: the
Metropolis–Hastings kernel (1.3) with proposal `rwmProposal m δ` and acceptance `rwmAccept m`. -/
noncomputable def rwmKernel (m : ℕ) (δ : ℝ) : ProbabilityTheory.Kernel (Fin m → ℝ) (Fin m → ℝ) :=
  mhKernel (rwmProposal m δ) (rwmAccept m)

end MHSpectralGap.RWM
