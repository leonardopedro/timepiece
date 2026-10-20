/-
prove2.me platform library module `Definitions.Def_TotalVariationDist`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TotalVariationDist.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Mathlib.MeasureTheory.Measure.MeasureSpace

/-!
Total variation distance between measures, in the Markov-chain-theory
normalization.

Source: Galin L. Jones, *On the Markov Chain Central Limit Theorem*,
Probability Surveys 1 (2004) 299-320 (arXiv math/0409112v2), §2: the norm
`‖·‖` appearing in eqs. (2)-(3).
-/

namespace MarkovChainCLT

/-- **Total variation distance** between two measures, in the Markov-chain-theory
normalization: `tvDist μ ν = sup_A |μ(A) - ν(A)|` over measurable sets `A`.
For probability measures this lies in `[0, 1]`. (Jones 2004, §2: the norm `‖·‖`
of eqs. (2)-(3).) -/
noncomputable def tvDist {X : Type*} [MeasurableSpace X]
    (μ ν : MeasureTheory.Measure X) : ℝ :=
  sSup {r | ∃ A : Set X, MeasurableSet A ∧ r = |(μ A).toReal - (ν A).toReal|}

end MarkovChainCLT
