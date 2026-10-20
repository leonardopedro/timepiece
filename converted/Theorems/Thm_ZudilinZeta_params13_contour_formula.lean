/-
prove2.me platform library module `Theorems.Thm_ZudilinZeta_params13_contour_formula`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_ZudilinZeta_params13_contour_formula.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_ZudilinZetaContourKernel
set_option autoImplicit false

theorem ZudilinZeta.params13_contour_formula (τ : ℂ) (hτ : 87 ≤ τ.re ∧ τ.re ≤ 175 / 2) (n : ℕ) (hn : 2 ≤ n) :
    |ZudilinZeta.F ZudilinZeta.params13 n| = (n : ℝ) / (2 * Real.pi) *
      |(ZudilinZeta.params13KernelIntegral n τ).re| := by sorry
