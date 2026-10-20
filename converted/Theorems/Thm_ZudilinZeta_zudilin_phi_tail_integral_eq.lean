/-
prove2.me platform library module `Theorems.Thm_ZudilinZeta_zudilin_phi_tail_integral_eq`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_ZudilinZeta_zudilin_phi_tail_integral_eq.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_ZudilinZetaAsymp

namespace ZudilinZeta

theorem zudilin_phi_tail_integral_eq (P : Params) :
    (∫ x in Set.Ioi (1 / (m P (P.q - P.r) : ℝ)), (phi P x : ℝ) / x ^ 2) =
      (∫ x in (0 : ℝ)..1, (phi P x : ℝ) * deriv digamma x) -
        ∫ x in (0 : ℝ)..(1 / (m P (P.q - P.r) : ℝ)),
          (phi P x : ℝ) / x ^ 2 := by sorry

end ZudilinZeta
