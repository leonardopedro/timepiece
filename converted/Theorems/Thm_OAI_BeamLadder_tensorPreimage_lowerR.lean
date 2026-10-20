/-
prove2.me platform library module `Theorems.Thm_OAI_BeamLadder_tensorPreimage_lowerR`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_OAI_BeamLadder_tensorPreimage_lowerR.lean` (platform Mathlib rev 0df444a360ea).
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
open EntropyPhotonNumber QuantumTrace Annihilation TensorLp
variable {n : ℕ}

theorem OAI.BeamLadder.tensorPreimage_lowerR (j : Fin n) (x y : Fock n) :
    lowerR j (tensorPreimage x y)=tensor (inverseWeight 3 x) (sandwich 0 3 (by omega) j y) := by sorry
