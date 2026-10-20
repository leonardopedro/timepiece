/-
prove2.me platform library module `Theorems.Thm_OAI_QuantumTrace_energySet_limit`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_OAI_QuantumTrace_energySet_limit.lean` (platform Mathlib rev 0df444a360ea).
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
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

theorem OAI.QuantumTrace.energySet_limit {α : Type*} {l : Filter α} [NeBot l] {n : ℕ}
    (b : HilbertBasis (Fin n → ℕ) ℂ H) {E : ℝ}
    {T : α → H →L[ℂ] H} {A : H →L[ℂ] H}
    (hT : ∀ a, T a ∈ energySet b E) (hlim : Tendsto T l (𝓝 A)) : A ∈ energySet b E := by sorry
