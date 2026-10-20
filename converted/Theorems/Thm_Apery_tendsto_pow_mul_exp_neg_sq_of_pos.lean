/-
prove2.me platform library module `Theorems.Thm_Apery_tendsto_pow_mul_exp_neg_sq_of_pos`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_Apery_tendsto_pow_mul_exp_neg_sq_of_pos.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

open Polynomial Filter Topology MeasureTheory

namespace Apery

theorem tendsto_pow_mul_exp_neg_sq_of_pos {c : ℝ} (hc : 0 < c) (b : ℕ) (hb : 0 < b) :
    Tendsto (fun n : ℕ => (b : ℝ) ^ (37 * n) * Real.exp (-c * (n : ℝ) ^ 2)) atTop (𝓝 0) := by sorry

end Apery
