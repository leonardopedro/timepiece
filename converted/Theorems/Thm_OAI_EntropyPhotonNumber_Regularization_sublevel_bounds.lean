/-
prove2.me platform library module `Theorems.Thm_OAI_EntropyPhotonNumber_Regularization_sublevel_bounds`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_OAI_EntropyPhotonNumber_Regularization_sublevel_bounds.lean` (platform Mathlib rev 0df444a360ea).
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

open OAI OAI.EntropyPhotonNumber OAI.EntropyPhotonNumber.Regularization
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
variable {n : ℕ} (R : Regularization n)

theorem OAI.EntropyPhotonNumber.Regularization.sublevel_bounds (C : ℝ) (ρ σ : State n) (hρ : FiniteEnergy ρ) (hσ : FiniteEnergy σ)
    (h : R.objective ρ σ ≤ C) :
    0 ≤ C+R.entropyConstant ∧
    energy ρ ≤ 2*(C+R.entropyConstant)/R.b1 ∧
    energy σ ≤ 2*(C+R.entropyConstant)/R.b2 ∧
    numberMoment 4 ρ ≤ (C+R.entropyConstant)/R.ζ ∧
    numberMoment 4 σ ≤ (C+R.entropyConstant)/R.ζ := by sorry
