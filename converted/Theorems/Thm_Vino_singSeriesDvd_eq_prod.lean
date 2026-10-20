/-
prove2.me platform library module `Theorems.Thm_Vino_singSeriesDvd_eq_prod`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_Vino_singSeriesDvd_eq_prod.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_Vino_ramanujan
import Mathlib.Data.Nat.Totient
import Mathlib.Algebra.BigOperators.Ring.Finset
open Finset

namespace Vino

theorem singSeriesDvd_eq_prod {Q : ℕ} (hQ : Squarefree Q) (n : ℤ) :
    singSeriesDvd Q n = ∏ p ∈ Q.primeFactors, ((threePrimeFactor p n : ℝ) : ℂ) := by sorry

end Vino
