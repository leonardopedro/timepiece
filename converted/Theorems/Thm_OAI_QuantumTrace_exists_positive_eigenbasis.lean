/-
prove2.me platform library module `Theorems.Thm_OAI_QuantumTrace_exists_positive_eigenbasis`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_OAI_QuantumTrace_exists_positive_eigenbasis.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_EntropyPhotonNumber
import Definitions.Def_OAI_MathematicalPhysics_Fock_Beam
import Definitions.Def_OAI_Analysis_QuantumTrace_Basic

open OAI OAI.QuantumTrace
open scoped BigOperators ComplexConjugate ENNReal Topology
open MeasureTheory
universe u
variable {E : Type u} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]
variable {ι κ : Type*}

theorem OAI.QuantumTrace.exists_positive_eigenbasis (b : HilbertBasis ι ℂ E)
    {T : E →L[ℂ] E} (hp : T.IsPositive) {τ : ℝ}
    (ht : HasSum (fun i => (inner ℂ (b i) (T (b i))).re) τ) :
    ∃ (J : Type u) (c : HilbertBasis J ℂ E) (p : J → ℝ),
      (∀ j, 0 ≤ p j) ∧ HasSum p τ ∧ ∀ j, T (c j) = (p j : ℂ) • c j := by sorry
