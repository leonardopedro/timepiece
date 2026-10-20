/-
prove2.me platform library module `Definitions.Def_MarkovChainPathMeasure`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_MarkovChainPathMeasure.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_MarkovChainKernel
import Mathlib.Probability.Kernel.Composition.MeasureComp
import Mathlib.MeasureTheory.Function.ConvergenceInDistribution
import Mathlib.Probability.Distributions.Gaussian.Real
import Prove2me.Shim.TendstoInDistribution  -- conversion shim (platform Mathlib API)

/-!
The law of a time-homogeneous Markov chain started from an initial
distribution, sample averages of a functional along the chain, and the Markov
chain central limit theorem property.

Source: Galin L. Jones, *On the Markov Chain Central Limit Theorem*,
Probability Surveys 1 (2004) 299-320 (arXiv math/0409112v2), §1: the sample
average `f̄_n` (Section 1) and the CLT of eq. (1).

Builds on the platform's Ionescu-Tulcea infrastructure
(`BanditAlgorithm.markovChainKernel`, itself built on
`BanditAlgorithm.markovChainStep` and `ProbabilityTheory.Kernel.traj`).
-/

open MeasureTheory ProbabilityTheory Filter
open scoped NNReal

namespace MarkovChainCLT

/-- The law of the trajectory `(X₀, X₁, X₂, …)` of the time-homogeneous Markov chain
with transition kernel `P` and **initial distribution** `lam` (coordinate `0` has law
`lam`), as a measure on the path space `ℕ → X`.  Built from the platform's
Ionescu-Tulcea infrastructure: `BanditAlgorithm.markovChainKernel P` is the kernel
sending a starting point to the law of the trajectory from that point. -/
noncomputable def chainMeasure {X : Type*} [MeasurableSpace X] (P : Kernel X X)
    [IsMarkovKernel P] (lam : Measure X) : Measure (ℕ → X) :=
  (BanditAlgorithm.markovChainKernel P) ∘ₘ lam

instance chainMeasure.instIsProbabilityMeasure {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P] (lam : Measure X) [IsProbabilityMeasure lam] :
    IsProbabilityMeasure (chainMeasure P lam) :=
  inferInstanceAs (IsProbabilityMeasure ((BanditAlgorithm.markovChainKernel P) ∘ₘ lam))

/-- The sample average `f̄_n = n⁻¹ ∑_{i=1}^n f(X_i)` of a functional `f` along the
first `n` steps of a trajectory `ω` (the initial point `ω 0` is not included,
matching Jones 2004, Section 1). -/
noncomputable def sampleAvg {X : Type*} (f : X → ℝ) (n : ℕ) (ω : ℕ → X) : ℝ :=
  (n : ℝ)⁻¹ * ∑ i ∈ Finset.range n, f (ω (i + 1))

/-- `SatisfiesCLT P π f` says: there is an asymptotic variance `v ≥ 0` such that for
**every** initial distribution `lam`, under the chain law started from `lam`,
`√n (f̄_n - E_π f)` converges in distribution to `N(0, v)` (Jones 2004 eq. (1); the
degenerate case `v = 0` means convergence to the point mass at `0`). -/
def SatisfiesCLT {X : Type*} [MeasurableSpace X] (P : Kernel X X) [IsMarkovKernel P]
    (π : Measure X) (f : X → ℝ) : Prop :=
  ∃ v : ℝ≥0, ∀ (lam : Measure X) [IsProbabilityMeasure lam],
    Prove2me.Shim.TendstoInDistribution  -- conversion: platform (general) form, see the shim
      (fun (n : ℕ) (ω : ℕ → X) => Real.sqrt n * (sampleAvg f n ω - ∫ x, f x ∂π))
      atTop (id : ℝ → ℝ) (fun _ => chainMeasure P lam) (gaussianReal 0 v)

end MarkovChainCLT
