/-
prove2.me platform library module `Theorems.Thm_Vino_vmSum_split_coprime`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_Vino_vmSum_split_coprime.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_Vino_dirichlet
import Definitions.Def_Vino_primes
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.Data.ZMod.Units
open Finset

namespace Vino

theorem vmSum_split_coprime (q : ℕ) (α : ℝ) (N : ℕ) :
    vmSum α N
      = (∑ n ∈ (Finset.range N).filter (fun n => Nat.Coprime n q),
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * CircleMethod.e (α * (n : ℝ)))
        + ∑ n ∈ (Finset.range N).filter (fun n => ¬ Nat.Coprime n q),
            ((ArithmeticFunction.vonMangoldt n : ℝ) : ℂ) * CircleMethod.e (α * (n : ℝ)) := by sorry

end Vino
