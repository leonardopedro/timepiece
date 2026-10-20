/-
prove2.me platform library module `Theorems.Thm_Helfgott_mobius_sigma_coprime_real_two_power_rankin_upper`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Theorems/Thm_Helfgott_mobius_sigma_coprime_real_two_power_rankin_upper.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.Algebra.Order.Floor.Semifield
import Mathlib.Analysis.SpecialFunctions.Pow.Real
open Finset Nat Real ArithmeticFunction
open scoped BigOperators Classical

namespace Helfgott
theorem mobius_sigma_coprime_real_two_power_rankin_upper
    (q : ℕ) (X L T a b s t : ℝ)
    (hq : 1 ≤ q) (hX : 1 ≤ X) (hL : 0 ≤ L) (hT : 0 ≤ T)
    (ha : 0 ≤ a) (hb : 0 ≤ b) (hs0 : 1/2 ≤ s) (hs1 : s ≤ 1)
    (ht0 : 1/2 ≤ t) (ht1 : t ≤ 1)
    (hM : ∀ z : ℝ, 1 ≤ z → z ≤ X →
      |∑ r∈Icc 1 ⌊z⌋₊, ((moebius r : ℤ) : ℝ)/(r : ℝ)| ≤
        a*(L/z)^(1-s)+b*(T/z)^(1-t)) :
    let R : ℝ → ℝ := fun u => (((∑' n : ℕ,(n : ℝ)^(-u-1))*(∑' n : ℕ,(n : ℝ)^(-2*u-1)))/(∑' n : ℕ,(n : ℝ)^(-3:ℝ))) *
      (∏ p∈q.primeFactors, ((p : ℝ)+1)/((p : ℝ)+1-(p : ℝ)*(p : ℝ)^(-u)))
    |∑ r∈Icc 1 ⌊X⌋₊, if Nat.Coprime r q then
      ((moebius r : ℤ) : ℝ)/(∏ p∈r.primeFactors, ((p : ℝ)+1)) else 0| ≤
      a*(L/X)^(1-s)*R s +
        b*(T/X)^(1-t)*R t := by sorry
end Helfgott
