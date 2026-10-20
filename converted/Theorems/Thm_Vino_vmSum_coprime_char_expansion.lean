/-
prove2.me platform library module `Theorems.Thm_Vino_vmSum_coprime_char_expansion`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_Vino_vmSum_coprime_char_expansion.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_Vino_dirichlet
import Definitions.Def_Vino_primes
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Data.ZMod.Units
open Finset

namespace Vino

theorem vmSum_coprime_char_expansion (q : ℕ) [NeZero q] {b : ℕ} (hb : IsUnit ((b : ℕ) : ZMod q)) (N : ℕ) :
    (Nat.totient q : ℂ) * ∑ n ∈ (Finset.range N).filter (fun n => Nat.Coprime n q),
        ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ)
          * CircleMethod.e ((b : ℝ) / (q : ℝ) * (n : ℝ))
      = ∑ χ : DirichletCharacter ℂ q,
          χ⁻¹ ((b : ℕ) : ZMod q) * gaussE q χ * vmSumChar q χ⁻¹ N := by sorry

end Vino
