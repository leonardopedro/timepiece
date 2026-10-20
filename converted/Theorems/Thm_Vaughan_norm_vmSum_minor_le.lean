/-
prove2.me platform library module `Theorems.Thm_Vaughan_norm_vmSum_minor_le`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_Vaughan_norm_vmSum_minor_le.lean` (platform Mathlib rev c5ea00351c28).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_Vino_vaughan
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.NumberTheory.ArithmeticFunction.Misc
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Algebra.Order.Interval.Finset.SuccPred
import Mathlib.Algebra.Order.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
import Mathlib.NumberTheory.Harmonic.Bounds
import Theorems.Thm_CircleMethod_e_neg
import Theorems.Thm_Vino_psi_le
import Theorems.Thm_CircleMethod_aux_sum_min_le
import Theorems.Thm_CircleMethod_nrm_le
import Theorems.Thm_CircleMethod_nrm_triangle
import Theorems.Thm_CircleMethod_nrm_neg
import Theorems.Thm_CircleMethod_nrm_nonneg
import Theorems.Thm_CircleMethod_nrm_eq_zero_iff
import Theorems.Thm_CircleMethod_nrm_pos_of_not_int
import Theorems.Thm_CircleMethod_norm_sum_e_le_inv_nrm
import Theorems.Thm_CircleMethod_norm_sum_e_le
import Theorems.Thm_CircleMethod_e_add
import Theorems.Thm_CircleMethod_norm_e

open Finset ArithmeticFunction

open CircleMethod

namespace Vaughan

theorem norm_vmSum_minor_le :
    ∃ C : ℝ, 0 < C ∧ ∀ (N q : ℕ) (a : ℤ) (α : ℝ), 2 ≤ N → 0 < q →
      Nat.Coprime a.natAbs q → |α - (a : ℝ) / (q : ℝ)| ≤ 1 / (q : ℝ) ^ 2 →
      ‖Vino.vmSum α N‖
        ≤ C * ((N : ℝ) / Real.sqrt q + (N : ℝ) ^ (4 / 5 : ℝ) + Real.sqrt ((N : ℝ) * q))
            * Real.log N ^ 4 := by sorry

end Vaughan
