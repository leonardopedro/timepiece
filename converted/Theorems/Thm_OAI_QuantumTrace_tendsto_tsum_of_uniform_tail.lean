/-
prove2.me platform library module `Theorems.Thm_OAI_QuantumTrace_tendsto_tsum_of_uniform_tail`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_OAI_QuantumTrace_tendsto_tsum_of_uniform_tail.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Gibbs
import Definitions.Def_OAI_Analysis_TensorLp
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamTrace
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Functions
import Definitions.Def_OAI_Analysis_DiagonalForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_ThermalMetric
import Definitions.Def_OAI_InformationTheory_PhotonNumber_BeamForms
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Generator
import Definitions.Def_OAI_InformationTheory_PhotonNumber_SpectralLog
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Continuity
import Definitions.Def_OAI_InformationTheory_PhotonNumber_Entropy

open OAI OAI.QuantumTrace
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open Filter Topology

theorem OAI.QuantumTrace.tendsto_tsum_of_uniform_tail {α ι : Type*} {l : Filter α}
    {f : α → ι → ℝ} {g : ι → ℝ}
    (hf : ∀ a, Summable (f a)) (hg : Summable g)
    (hfp : ∀ a i, 0 ≤ f a i) (hgp : ∀ i, 0 ≤ g i)
    (hlim : ∀ i, Tendsto (fun a => f a i) l (𝓝 (g i)))
    (htail : ∀ ε > 0, ∃ s : Finset ι,
      (∀ a, (∑' i : {i // i ∉ s}, f a i) < ε) ∧
      (∑' i : {i // i ∉ s}, g i) < ε) :
    Tendsto (fun a => ∑' i, f a i) l (𝓝 (∑' i, g i)) := by sorry
