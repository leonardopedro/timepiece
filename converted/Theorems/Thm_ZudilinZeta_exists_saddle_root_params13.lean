/-
prove2.me platform library module `Theorems.Thm_ZudilinZeta_exists_saddle_root_params13`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_ZudilinZeta_exists_saddle_root_params13.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_ZudilinZetaAsymp
import Definitions.Def_ZudilinZetaParams13

namespace ZudilinZeta
theorem exists_saddle_root_params13 :
    ∃ τ₀ : ℂ, charPoly params13 τ₀ = 0 ∧ 0 < τ₀.im ∧
      (∀ τ : ℂ, charPoly params13 τ = 0 → 0 < τ.im → τ.re ≤ τ₀.re) ∧
      τ₀.re < (params13.eta 0 : ℝ) ∧
      (∀ k : ℤ, (f0 params13 τ₀).im ≠ (k : ℝ) * Real.pi) := by sorry
end ZudilinZeta
