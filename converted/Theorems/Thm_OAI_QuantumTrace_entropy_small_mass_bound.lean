/-
prove2.me platform library module `Theorems.Thm_OAI_QuantumTrace_entropy_small_mass_bound`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_OAI_QuantumTrace_entropy_small_mass_bound.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic

open OAI OAI.QuantumTrace
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory

theorem OAI.QuantumTrace.entropy_small_mass_bound {n : ℕ} (p : (Fin n → ℕ) → ℝ)
    (hp : ∀ k, 0 ≤ p k) (hpu : ∀ k, p k ≤ 1) {q : ℝ} (hq : HasSum p q)
    (hE : Summable (fun k => (∑ j, (k j : ℝ)) * p k)) :
    Summable (fun k => Real.negMulLog (p k)) ∧
    (∑' k, Real.negMulLog (p k)) ≤
      (n + 1 : ℝ) * Real.negMulLog q + n * q ^ 2 +
        (∑' k, (∑ j, (k j : ℝ)) * p k) * q := by sorry
