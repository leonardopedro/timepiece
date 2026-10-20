/-
prove2.me platform library module `Theorems.Thm_ZudilinZeta_zetaR_eq_riemannZeta`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_ZudilinZeta_zetaR_eq_riemannZeta.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_ZudilinZetaSetup

namespace ZudilinZeta
theorem zetaR_eq_riemannZeta (k : ℕ) (hk : 2 ≤ k) :
    riemannZeta (k : ℂ) = (zetaR k : ℂ) := by sorry
end ZudilinZeta
