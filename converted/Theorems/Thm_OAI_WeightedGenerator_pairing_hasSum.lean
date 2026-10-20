/-
prove2.me platform library module `Theorems.Thm_OAI_WeightedGenerator_pairing_hasSum`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_OAI_WeightedGenerator_pairing_hasSum.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic
import Definitions.Def_OAI_MathematicalPhysics_Fock_Operators

open OAI OAI.WeightedGenerator
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
open scoped ComplexConjugate
open EntropyPhotonNumber Annihilation
open scoped BigOperators
variable {n : ℕ} {I J : Type*}

theorem OAI.WeightedGenerator.pairing_hasSum (b : HilbertBasis J ℂ (Fock n)) (r : ℝ) (x : I → Fock n)
    (hx : Summable (fun i => ‖x i‖^2)) (Z : Fock n →L[ℂ] Fock n) :
    HasSum (fun k => inner ℂ (b k) (Z (generator r x (b k)))) (pairing r x Z) := by sorry
