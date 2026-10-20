/-
prove2.me platform library module `Theorems.Thm_OAI_BeamLadder_radial_covariance`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_OAI_BeamLadder_radial_covariance.lean` (platform Mathlib rev 0df444a360ea).
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

open OAI OAI.BeamLadder
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open scoped BigOperators ComplexConjugate
open scoped BigOperators
open MvPolynomial
open scoped BigOperators ComplexConjugate Classical
open Submodule
open EntropyPhotonNumber QuantumTrace Annihilation
open scoped ComplexConjugate
variable {n : ℕ}

theorem OAI.BeamLadder.radial_covariance (η : ℝ) (hη : η ∈ Set.Icc 0 1)
    (f : ℝ → ℝ) (C : ℝ) (hC : 0≤C)
    (hf : ∀ ke : NumberIndex n × NumberIndex n, |f (W ke)|≤C) :
    radial f C hC hf ∘L (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap =
      (beamUnitary η hη).toContinuousLinearEquiv.toContinuousLinearMap ∘L radial f C hC hf := by sorry
