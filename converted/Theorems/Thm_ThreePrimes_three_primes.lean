/-
prove2.me platform library module `Theorems.Thm_ThreePrimes_three_primes`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_ThreePrimes_three_primes.lean` (platform Mathlib rev c5ea00351c28).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_Vino_threeprimes
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Nat.Totient

open CircleMethod Vino Finset Filter Asymptotics MeasureTheory
open scoped Topology

namespace ThreePrimes

theorem three_primes (hSW : SiegelWalfisz) :
    ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Odd n →
      ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ p₁ + p₂ + p₃ = n := by sorry

end ThreePrimes
