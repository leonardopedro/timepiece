/-
prove2.me platform library module `Theorems.Thm_ZudilinZeta_zudilin_numeric_C0_bounds`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_ZudilinZeta_zudilin_numeric_C0_bounds.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_ZudilinZetaAsymp
import Definitions.Def_ZudilinZetaParams13

namespace ZudilinZeta
theorem zudilin_numeric_C0_bounds (τ : ℂ) (hroot : charPoly params13 τ = 0) (him : 0 < τ.im)
    (hmax : ∀ σ : ℂ, charPoly params13 σ = 0 → 0 < σ.im → σ.re ≤ τ.re) :
    227.58019641 ≤ C0 params13 τ ∧ C0 params13 τ < 227.58019642 := by sorry
end ZudilinZeta
