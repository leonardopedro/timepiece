/-
prove2.me platform library module `Definitions.Def_Zeta5_SourceValue`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_Zeta5_SourceValue.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

/-!
# `ζ(5)` as a real number
-/

namespace Apery

/-- `ζ(5)` as a real number. -/
noncomputable def zeta5 : ℝ := ∑' n : ℕ, 1 / (n : ℝ) ^ 5

/-- Mathlib's `riemannZeta 5` is the real number `zeta5`. -/
theorem riemannZeta_five : riemannZeta 5 = (zeta5 : ℂ) := by
  have h := zeta_nat_eq_tsum_of_gt_one (k := 5) (by norm_num)
  rw [Nat.cast_ofNat] at h
  rw [h, zeta5, Complex.ofReal_tsum]
  push_cast
  rfl

end Apery
