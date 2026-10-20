/-
prove2.me platform library module `Theorems.Thm_OAI_EntropyPhotonNumber_regularizedOutput_energy_bound`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_OAI_EntropyPhotonNumber_regularizedOutput_energy_bound.lean` (platform Mathlib rev 0df444a360ea).
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

open OAI OAI.EntropyPhotonNumber
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open scoped ENNReal
open QuantumTrace Filter Topology

theorem OAI.EntropyPhotonNumber.regularizedOutput_energy_bound {n : ℕ} (η δ κ : ℝ) (hη : η ∈ Set.Icc 0 1)
    (hδ : δ ∈ Set.Icc 0 1) (hκ : κ ∈ Set.Icc 0 1) {τD τ0 ρ σ : State n}
    (hD : FiniteEnergy τD) (h0 : FiniteEnergy τ0) (hρ : FiniteEnergy ρ) (hσ : FiniteEnergy σ) :
    energy (regularizedOutput η δ κ hη hδ hκ τD τ0 ρ σ) ≤
      energy ρ+energy σ+energy τD+energy τ0 := by sorry
