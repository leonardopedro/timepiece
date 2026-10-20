/-
prove2.me platform library module `Theorems.Thm_OAI_EntropyPhotonNumber_spectral_weighted_columns`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_OAI_EntropyPhotonNumber_spectral_weighted_columns.lean` (platform Mathlib rev 0df444a360ea).
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

open OAI OAI.EntropyPhotonNumber
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
open QuantumTrace Annihilation
variable {n : ℕ} {J : Type} {ρ : State n}

theorem OAI.EntropyPhotonNumber.spectral_weighted_columns (b : HilbertBasis J ℂ (Fock n)) (p : J → ℝ)
    (hp : ∀ j, 0≤p j) (he : ∀ j, ρ.op (b j)=(p j:ℂ) • b j)
    (hm : FiniteMoment 6 ρ) :
    ∃ x : J → Fock n, Summable (fun j => ‖x j‖^2) ∧
      ∀ j, inverseWeight 3 (x j)=CrossEnsemble.eigenEnsemble b p j := by sorry
