/-
prove2.me platform library module `Theorems.Thm_OAI_QuantumTrace_spectral_form_representation`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_OAI_QuantumTrace_spectral_form_representation.lean` (platform Mathlib rev 0df444a360ea).
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

open OAI OAI.QuantumTrace
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open ContinuousLinearMap
open scoped ENNReal
open Set Filter Topology Complex MeasureTheory
open Set Filter Topology Complex Metric
open MeasureTheory Set Filter Topology Complex Metric InnerProductSpace
open scoped ENNReal NNReal
open Filter Topology
open scoped ComplexConjugate
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {J : Type*}

theorem OAI.QuantumTrace.spectral_form_representation (b : HilbertBasis J ℂ E) (c : J → ℝ)
    (hc : ∀ j, 0≤c j) (V : E →L[ℂ] E) (hV : V.IsSymmetric)
    (hs : ∀ y, Summable (fun j => c j*‖inner ℂ (b j) (V y)‖^2))
    {C : ℝ} (hC : 0≤C)
    (hb : ∀ y, (∑' j, c j*‖inner ℂ (b j) (V y)‖^2)≤C*‖y‖^2) :
    ∃ B : E →L[ℂ] E, B.IsPositive ∧
      (∀ y, HasSum (fun j => c j*‖inner ℂ (b j) (V y)‖^2) (inner ℂ y (B y)).re) ∧
      ∀ (j : J) (y : E) (z : ℂ), V y=z • b j → B y=(c j:ℂ) • V (z • b j) := by sorry
