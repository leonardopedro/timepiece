/-
prove2.me platform library module `Theorems.Thm_Vino_three_primes_count`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_Vino_three_primes_count.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_Vino_primes
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open Finset

namespace Vino

theorem three_primes_count (N n : ℕ) :
    (∫ α in (0:ℝ)..1, (vmSum α N) ^ 3 * CircleMethod.e (-(n : ℝ) * α))
      = ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ c ∈ Finset.range N,
          if a + b + c = n then
            ((ArithmeticFunction.vonMangoldt a : ℝ) : ℂ)
              * ((ArithmeticFunction.vonMangoldt b : ℝ) : ℂ)
              * ((ArithmeticFunction.vonMangoldt c : ℝ) : ℂ)
          else 0 := by sorry

end Vino
