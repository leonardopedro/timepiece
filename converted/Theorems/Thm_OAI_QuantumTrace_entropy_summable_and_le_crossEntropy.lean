/-
prove2.me platform library module `Theorems.Thm_OAI_QuantumTrace_entropy_summable_and_le_crossEntropy`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_OAI_QuantumTrace_entropy_summable_and_le_crossEntropy.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic

open OAI OAI.QuantumTrace
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory

theorem OAI.QuantumTrace.entropy_summable_and_le_crossEntropy {ι : Type*} (p q : ι → ℝ)
    (hp : ∀ i, 0 ≤ p i) (hq : ∀ i, 0 < q i)
    (hp1 : HasSum p 1) (hq1 : HasSum q 1)
    (hcross : Summable (fun i => p i * (-Real.log (q i)))) :
    Summable (fun i => Real.negMulLog (p i)) ∧
      (∑' i, Real.negMulLog (p i)) ≤ ∑' i, p i * (-Real.log (q i)) := by sorry
