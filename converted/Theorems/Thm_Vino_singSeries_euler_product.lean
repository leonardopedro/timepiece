/-
prove2.me platform library module `Theorems.Thm_Vino_singSeries_euler_product`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_Vino_singSeries_euler_product.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_Vino_ramanujan
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.BigOperators.Ring.Finset
open Finset

namespace Vino

theorem singSeries_euler_product {s : Finset ℕ} (hs : ∀ p ∈ s, Nat.Prime p) (n : ℤ) :
    ∑ T ∈ s.powerset, singTerm (∏ p ∈ T, p) n
      = ∏ p ∈ s, ((threePrimeFactor p n : ℝ) : ℂ) := by sorry

end Vino
