/-
prove2.me platform library module `Theorems.Thm_Vino_integral_cube_orthogonality`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_Vino_integral_cube_orthogonality.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_CircleMethod_char
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
open Finset

namespace Vino

theorem integral_cube_orthogonality (w : ℕ → ℂ) (N : ℕ) (n : ℕ) :
    (∫ α in (0:ℝ)..1,
        (∑ a ∈ Finset.range N, w a * CircleMethod.e (α * (a : ℝ))) ^ 3
          * CircleMethod.e (-(n : ℝ) * α))
      = ∑ a ∈ Finset.range N, ∑ b ∈ Finset.range N, ∑ c ∈ Finset.range N,
          if a + b + c = n then w a * w b * w c else 0 := by sorry

end Vino
