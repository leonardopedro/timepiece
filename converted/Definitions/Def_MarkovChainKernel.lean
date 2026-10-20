/-
prove2.me platform library module `Definitions.Def_MarkovChainKernel`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_MarkovChainKernel.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_GittinsIndex

open MeasureTheory ProbabilityTheory

namespace BanditAlgorithm

/-- The Markov kernel sending an initial state to the law of the full
time-homogeneous Markov-chain trajectory started from that state. -/
noncomputable def markovChainKernel
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] : Kernel S (ℕ → S) :=
  (Kernel.traj (markovChainStep P) 0).comap
    (fun x (_ : Finset.Iic 0) ↦ x) (by fun_prop)

instance
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] :
    IsMarkovKernel (markovChainKernel P) := by
  rw [markovChainKernel]
  infer_instance

@[simp]
lemma markovChainKernel_apply
    {S : Type*} [MeasurableSpace S]
    (P : Kernel S S) [IsMarkovKernel P] (x : S) :
    markovChainKernel P x = markovChainMeasure P x := by
  ext A hA
  rw [markovChainKernel, markovChainMeasure, Kernel.trajMeasure]
  rw [Measure.bind_apply hA (Kernel.aemeasurable _)]
  rw [Measure.map_dirac (by fun_prop)]
  rw [lintegral_dirac' _
    ((Kernel.traj (markovChainStep P) 0).measurable_coe hA)]
  change
    Kernel.traj (markovChainStep P) 0 (fun _ ↦ x) A =
      Kernel.traj (markovChainStep P) 0
        ((MeasurableEquiv.piUnique (fun _ : Finset.Iic 0 ↦ S)).symm x) A
  congr 2

end BanditAlgorithm
