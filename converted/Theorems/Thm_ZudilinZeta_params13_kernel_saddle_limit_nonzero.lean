/-
prove2.me platform library module `Theorems.Thm_ZudilinZeta_params13_kernel_saddle_limit_nonzero`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_ZudilinZeta_params13_kernel_saddle_limit_nonzero.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_ZudilinZetaContourKernel
import Definitions.Def_ZudilinZetaAsymp
set_option autoImplicit false

theorem ZudilinZeta.params13_kernel_saddle_limit_nonzero (τ : ℂ)
    (hroot : ZudilinZeta.charPoly ZudilinZeta.params13 τ = 0) (him : 0 < τ.im)
    (hmax : ∀ σ : ℂ, ZudilinZeta.charPoly ZudilinZeta.params13 σ = 0 →
      0 < σ.im → σ.re ≤ τ.re) :
    (87 ≤ τ.re ∧ τ.re ≤ 175 / 2) ∧ ∃ c : ℂ, c ≠ 0 ∧
      Filter.Tendsto (fun n : ℕ =>
        ((n : ℂ) ^ 7 * (Real.sqrt (n : ℝ) : ℂ) / (2 * (Real.pi : ℂ)) ^ 5) *
          Complex.exp (-(n : ℂ) * ZudilinZeta.f0 ZudilinZeta.params13 τ) *
            ZudilinZeta.params13KernelIntegral n τ) Filter.atTop (nhds c) := by sorry
