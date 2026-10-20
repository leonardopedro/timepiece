/-
prove2.me platform library module `Theorems.Thm_Helfgott_rankin_sharp_coprime_coupled_weight_excluded_upper`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_Helfgott_rankin_sharp_coprime_coupled_weight_excluded_upper.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott
theorem rankin_sharp_coprime_coupled_weight_excluded_upper (q D : ℕ) (s t : ℝ)
    (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1) (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1) (hst : 1 < s+t) :
    let J : ℕ → ℝ → ℝ := fun n u =>
      ∏ p∈n.primeFactors, ((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-u))
    let H : ℝ := ∏ p∈q.primeFactors,(1+(p : ℝ)^(-s-t)/
      ((1-(p : ℝ)^(-s)+(p : ℝ)^(-1:ℝ))*(1-(p : ℝ)^(-t)+(p : ℝ)^(-1:ℝ))))
    (∑ d∈Icc 1 D,if Nat.Coprime d q then
      |((moebius d : ℤ) : ℝ)|/(∏ p∈d.primeFactors,((p : ℝ)+1))^2*
        (d : ℝ)^(2-s-t)*J (d*q) s*J (d*q) t else 0) ≤
      J q s*J q t *
        ((((∑' n : ℕ,(n : ℝ)^(-s-t))*(∑' n : ℕ,(n : ℝ)^(-s-2*t))*(∑' n : ℕ,(n : ℝ)^(-2*s-t)))/
          ((∑' n : ℕ,(n : ℝ)^(-3:ℝ))^2*(∑' n : ℕ,(n : ℝ)^(-4:ℝ))))/H) := by sorry
end Helfgott
