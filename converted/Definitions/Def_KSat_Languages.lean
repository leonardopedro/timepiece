/-
prove2.me platform library module `Definitions.Def_KSat_Languages`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_KSat_Languages.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_CookLevin_Complexity

set_option autoImplicit false

namespace KSat

/-- Every clause has at most `k` literal occurrences. Empty clauses and
repeated literals retain their ordinary meanings from `CookLevin`. -/
def IsKCNF (k : Nat) (φ : CookLevin.Formula) : Prop :=
  ∀ c ∈ φ, c.length ≤ k

/-- The language of encodings of satisfiable CNF formulas of clause width
at most `k`. Invalid strings and formulas wider than `k` are rejected. -/
def KSAT (k : Nat) : CookLevin.Language := fun x =>
  ∃ φ : CookLevin.Formula,
    x = CookLevin.encodeFormula φ ∧ IsKCNF k φ ∧ CookLevin.Satisfiable φ

end KSat
