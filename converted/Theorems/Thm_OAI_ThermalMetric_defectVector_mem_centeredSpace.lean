/-
prove2.me platform library module `Theorems.Thm_OAI_ThermalMetric_defectVector_mem_centeredSpace`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_OAI_ThermalMetric_defectVector_mem_centeredSpace.lean` (platform Mathlib rev 0df444a360ea).
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

open OAI OAI.ThermalMetric
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped ComplexConjugate
variable {J : Type*}

theorem OAI.ThermalMetric.defectVector_mem_centeredSpace (r : ℝ) (hr : 0<r) (p : J → ℝ)
    (hp : ∀ j, 0<p j) (hs : Summable p) (d : J × J → ℂ) (hd)
    (hc : HasSum (fun j => (p j:ℂ)*d (j,j)) 0) :
    defectVector r hr p hp d hd ∈ centeredSpace r hr p hp hs := by sorry
