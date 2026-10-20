/-
prove2.me platform library module `Definitions.Def_InteractiveConsistency_Authenticated_Procedure`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_InteractiveConsistency_Authenticated_Procedure.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_InteractiveConsistency_Authenticated_Scenario
set_option autoImplicit false

namespace InteractiveConsistency.Authenticated

/-- The non-NIL values obtained for `q` from paths with distinct intermediate
processors, excluding the receiver `p` and the originator `q`. -/
def S {α V : Type*} [DecidableEq α] (m : ℕ) (P : Finset α)
    (τ : List α → Option V) (p q : α) : Set V :=
  {v | ∃ w : List α, w.Nodup ∧ w.length ≤ m ∧
    (∀ x ∈ w, x ∈ P ∧ x ≠ p ∧ x ≠ q) ∧ τ (w ++ [q]) = some v}

/-- Record the unique non-NIL value when there is one, and NIL otherwise. -/
noncomputable def record {α V : Type*} [DecidableEq α] (m : ℕ) (P : Finset α)
    (τ : List α → Option V) (p q : α) : Option V := by
  classical
  exact if h : ∃ v : V, S m P τ p q = {v} then some h.choose else none

end InteractiveConsistency.Authenticated
