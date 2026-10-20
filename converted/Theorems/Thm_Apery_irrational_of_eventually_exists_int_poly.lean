/-
prove2.me platform library module `Theorems.Thm_Apery_irrational_of_eventually_exists_int_poly`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_Apery_irrational_of_eventually_exists_int_poly.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

open Polynomial Filter Topology MeasureTheory

namespace Apery

theorem irrational_of_eventually_exists_int_poly (ξ : ℝ) (d : ℕ → ℕ) (ε : ℕ → ℝ)
    (hε : ∀ b : ℕ, 0 < b → Tendsto (fun n => (b : ℝ) ^ d n * ε n) atTop (𝓝 0))
    (h : ∀ᶠ n in atTop, ∃ Q : ℤ[X], Q.natDegree ≤ d n ∧ 0 < aeval ξ Q ∧ aeval ξ Q ≤ ε n) :
    Irrational ξ := by sorry

end Apery
