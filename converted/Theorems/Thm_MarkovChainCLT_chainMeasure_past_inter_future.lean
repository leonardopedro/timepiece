/-
prove2.me platform library module `Theorems.Thm_MarkovChainCLT_chainMeasure_past_inter_future`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_MarkovChainCLT_chainMeasure_past_inter_future.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_MarkovChainPathMeasure
import Definitions.Def_MarkovIterKernel

open Filter Finset Function MeasurableEquiv MeasurableSpace MeasureTheory Preorder ProbabilityTheory
open scoped ENNReal NNReal Topology
open MarkovChainCLT

theorem MarkovChainCLT.chainMeasure_past_inter_future {X : Type*} [MeasurableSpace X]
    (P : Kernel X X) [IsMarkovKernel P]
    (lam : Measure X) [IsProbabilityMeasure lam] (k n : ℕ)
    (A₀ : Set (Π _i : Finset.Iic k, X)) (hA₀ : MeasurableSet A₀)
    (B₀ : Set (ℕ → X)) (hB₀ : MeasurableSet B₀) :
    (chainMeasure P lam) ((frestrictLe (π := fun _ : ℕ => X) k ⁻¹' A₀)
        ∩ ((fun ω : ℕ → X => fun l => ω (k + n + l)) ⁻¹' B₀))
      = ∫⁻ u in A₀, ((BanditAlgorithm.markovChainKernel P)
          ∘ₘ (iterKernel P n (u ⟨k, Finset.mem_Iic.2 le_rfl⟩))) B₀
          ∂((chainMeasure P lam).map (frestrictLe (π := fun _ : ℕ => X) k)) := by sorry
