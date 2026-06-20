import Mathlib

/-!
# The primitive-recursive Schoenfeld matrix (Phase 3.1 of `IMPLEMENTATION_PLAN_RCP.md`)

This file discharges the **self-contained, sound** obligation of the RCP route: a
genuine (non-vacuous), primitive-recursive decision procedure `schoenfeld : ℕ → Bool`
for Schoenfeld's 1976 explicit bound

  `|π(n) − li(n)| ≤ (1/(8π))·√n·ln n`   (for `n ≥ 2657`),

together with the proof `schoenfeld_primrec : Primrec schoenfeld`.

The transcendental quantities are computed by explicit primitive-recursive rational
(fixed-point, scale `D = (n+1)²`) approximations:

* `π(n)` — exact, by a sieve (`primePi`);
* `ln m` — by the fast `artanh` recurrence
  `ln(m+1) = ln m + 2·artanh(1/(2m+1))` with `artanh(x) = Σ_j x^{2j+1}/(2j+1)`
  (`lnFix`, `incr`);
* `li(n)` — by the rectangle sum `Σ_{2≤k≤n} 1/ln k` (`liInt`);
* `√n` — removed by squaring the inequality;
* `(8π)² ≈ 6316547/10000` — a fixed rational constant.

Squaring the inequality and clearing denominators turns the bound into a pure
`ℕ`-arithmetic comparison, hence decidable and primitive recursive.

(The *accuracy* of the fixed-point approximations is a separate analytic matter and is
not required for primitive recursiveness; the plan treats it as "rational truncations
to predictable precision". What is proved here is exactly the plan's 3.1 deliverable:
the definition is genuine and the function is `Primrec`.)
-/

open Nat

namespace SchoenfeldMatrix

/-- `sumRange n f = Σ_{k<n} f k`, as a primitive-recursive right fold. -/
def sumRange (n : ℕ) (f : ℕ → ℕ) : ℕ :=
  (List.range n).foldr (fun k acc => f k + acc) 0

/-- Exact prime count `π(n) = #{p ≤ n : p prime}`. -/
def primePi (n : ℕ) : ℕ :=
  ((List.range (n + 1)).filter (fun k => decide (Nat.Prime k))).length

/-- `|a − b|` via truncated subtraction (primitive recursive). -/
def absDiff (a b : ℕ) : ℕ := (a - b) + (b - a)

/-- One `artanh` increment, scaled by `D`:
`2·artanh(1/(2m+1)) ≈ ln((m+1)/m)`, with `J+1` series terms. -/
def incr (D J m : ℕ) : ℕ :=
  2 * sumRange (J + 1) (fun j => D / ((2 * j + 1) * (2 * m + 1) ^ (2 * j + 1)))

/-- Fixed-point natural logarithm: `lnFix D J m ≈ D · ln m`. -/
def lnFix (D J m : ℕ) : ℕ :=
  Nat.rec 0 (fun m' ih => ih + (if m' = 0 then 0 else incr D J m')) m

/-- Fixed-point logarithmic integral `liInt D J n ≈ li(n)` (integer-valued). -/
def liInt (D J n : ℕ) : ℕ :=
  (sumRange (n + 1) (fun k => if k < 2 then 0 else (D * D) / lnFix D J k)) / D

/-- **Schoenfeld's matrix.** `schoenfeld n = true` iff the squared, rationalized
form of `|π(n) − li(n)| ≤ (1/(8π))·√n·ln n` holds, computed with fixed-point scale
`D = (n+1)²` and `(8π)² ≈ 6316547/10000`. Genuine and non-vacuous. -/
def schoenfeld (n : ℕ) : Bool :=
  decide
    (6316547 * absDiff (primePi n) (liInt ((n + 1) ^ 2) n n) ^ 2 * ((n + 1) ^ 2) ^ 2
      ≤ 10000 * n * lnFix ((n + 1) ^ 2) n n ^ 2)

/-! ## Primitive recursiveness -/

/-
`(a, b) ↦ a ^ b` is primitive recursive.
-/
theorem pow_primrec : Primrec₂ (fun a b : ℕ => a ^ b) := by
  -- We'll use the fact that if the function is defined by primitive recursion, then it's primitive recursive.
  have h_primrec : Primrec (fun p : (ℕ × ℕ) => p.1 ^ p.2) := by
    convert Primrec.nat_rec' _ _ _ using 1;
    -- Define the base case and the recursive step for the exponentiation function.
    case convert_5 => exact fun p => p.2
    case convert_6 => exact fun p => 1
    case convert_7 => exact fun p (n, IH) => p.1 * IH;
    · exact funext fun p => by induction p.2 <;> simp +decide [ *, pow_succ' ] ;
    · exact Primrec.snd;
    · exact Primrec.const 1;
    · exact Primrec.nat_mul.comp ( Primrec.fst.comp ( Primrec.fst ) ) ( Primrec.snd.comp ( Primrec.snd ) );
  convert h_primrec

/-
`Nat.Prime` is a primitive-recursive predicate.
-/
theorem prime_primrec : PrimrecPred Nat.Prime := by
  -- The relation `m ∣ p → m = 1` is primitive recursive.
  have h_div_rec : PrimrecRel (fun (m p : ℕ) => m ∣ p → m = 1) := by
    have h_mod : Primrec (fun p : ℕ × ℕ => p.2 % p.1) := by
      exact Primrec.nat_mod.comp ( Primrec.snd ) ( Primrec.fst );
    have h_mod : PrimrecPred (fun p : ℕ × ℕ => p.2 % p.1 = 0 → p.1 = 1) := by
      convert Primrec.eq.comp ( h_mod ) ( Primrec.const 0 ) |> PrimrecPred.not |> PrimrecPred.or <| Primrec.eq.comp ( Primrec.fst ) ( Primrec.const 1 ) using 1;
      grind;
    simpa only [ Nat.dvd_iff_mod_eq_zero ] using h_mod;
  convert PrimrecRel.of_eq _ _;
  rotate_left;
  exact ℕ;
  exact ℕ;
  all_goals try infer_instance;
  exact fun n m => ∀ x < n, x ∣ m → x = 1;
  exact fun n m => ∀ x < n, x ∣ m → x = 1;
  · convert PrimrecRel.forall_lt h_div_rec using 1;
  · aesop;
  · constructor <;> intro h;
    · convert PrimrecRel.forall_lt h_div_rec using 1;
    · convert PrimrecPred.and ( Primrec.nat_le.comp ( Primrec.const 2 ) Primrec.id ) ( h.comp ( Primrec.id ) ( Primrec.id ) ) using 1;
      ext; simp [Nat.prime_def_lt]

/-
A fold `Σ_{k < m a} g a k` is primitive recursive when `m`, `g` are.
-/
theorem sumRange_primrec {α : Type*} [Primcodable α] {m : α → ℕ} {g : α → ℕ → ℕ}
    (hm : Primrec m) (hg : Primrec₂ g) :
    Primrec (fun a => sumRange (m a) (fun k => g a k)) := by
  have h_fold : Primrec (fun a => List.foldr (fun k acc => g a k + acc) 0 (List.range (m a))) := by
    have h_g : Primrec (fun (p : α × ℕ) => g p.1 p.2) := by
      exact hg
    have h_range : Primrec (fun (a : α) => List.range (m a)) := by
      exact Primrec.list_range.comp hm
    convert Primrec.list_foldr h_range ( Primrec.const 0 ) ( show Primrec₂ ( fun a => fun p : ℕ × ℕ => g a p.1 + p.2 ) from ?_ ) using 1;
    exact Primrec.nat_add.comp ( h_g.comp ( Primrec.fst.pair ( Primrec.fst.comp Primrec.snd ) ) ) ( Primrec.snd.comp Primrec.snd );
  exact h_fold

theorem primePi_primrec : Primrec primePi := by
  -- The length of a primitive-recursive list is primitive recursive.
  have h_length_primrec : Primrec (fun l : List ℕ => l.length) := by
    exact Primrec.list_length;
  -- The filter operation is primitive recursive when the predicate is primitive recursive.
  have h_filter_primrec : Primrec (fun l : List ℕ => List.filter (fun k => decide (Nat.Prime k)) l) := by
    apply Primrec.listFilter; exact prime_primrec
  convert h_length_primrec.comp ( h_filter_primrec.comp ( Primrec.list_range.comp ( Primrec.succ ) ) ) using 1

theorem incr_primrec : Primrec (fun p : ℕ × ℕ × ℕ => incr p.1 p.2.1 p.2.2) := by
  -- The function `g` is defined using `Nat.div`, `Nat.mul`, and `Nat.pow`, which are all primitive recursive.
  have h_g_primrec : Primrec₂ (fun (p : ℕ × ℕ × ℕ) (j : ℕ) => p.1 / ((2 * j + 1) * (2 * p.2.2 + 1) ^ (2 * j + 1))) := by
    refine' Primrec.nat_div.comp ( Primrec.fst.comp _ ) _;
    · exact Primrec.fst;
    · refine' Primrec.nat_mul.comp _ _;
      · exact Primrec.nat_add.comp ( Primrec.nat_mul.comp ( Primrec.const 2 ) ( Primrec.snd ) ) ( Primrec.const 1 );
      · convert pow_primrec.comp ( Primrec.nat_add.comp ( Primrec.nat_mul.comp ( Primrec.const 2 ) ( Primrec.snd.comp ( Primrec.snd.comp ( Primrec.fst ) ) ) ) ( Primrec.const 1 ) ) ( Primrec.nat_add.comp ( Primrec.nat_mul.comp ( Primrec.const 2 ) ( Primrec.snd ) ) ( Primrec.const 1 ) ) using 1;
  convert Primrec.nat_mul.comp ( Primrec.const 2 ) ( sumRange_primrec _ _ ) using 1;
  · exact Primrec.succ.comp ( Primrec.fst.comp ( Primrec.snd ) );
  · exact h_g_primrec

theorem lnFix_primrec : Primrec (fun p : ℕ × ℕ × ℕ => lnFix p.1 p.2.1 p.2.2) := by
  apply Primrec.of_eq;
  apply Primrec.nat_rec';
  rotate_left;
  exact Primrec.const 0;
  rotate_left;
  exact fun p => p.2.2;
  exact fun p q => q.2 + ( if q.1 = 0 then 0 else incr p.1 p.2.1 q.1 );
  · aesop;
  · exact Primrec.snd.comp ( Primrec.snd );
  · convert Primrec.nat_add.comp ( Primrec.snd.comp ( Primrec.snd ) ) ( Primrec.ite _ ( Primrec.const 0 ) ( incr_primrec.comp ( Primrec.fst.comp ( Primrec.fst ) |> Primrec.pair <| Primrec.fst.comp ( Primrec.snd.comp ( Primrec.fst ) ) |> Primrec.pair <| Primrec.fst.comp ( Primrec.snd ) ) ) ) using 1;
    exact Primrec.eq.comp ( Primrec.fst.comp ( Primrec.snd ) ) ( Primrec.const 0 )

theorem liInt_primrec : Primrec (fun p : ℕ × ℕ × ℕ => liInt p.1 p.2.1 p.2.2) := by
  convert Primrec.nat_div.comp (sumRange_primrec _ _) (Primrec.fst) using 1;
  · exact Primrec.succ.comp ( Primrec.snd.comp ( Primrec.snd ) );
  · refine' Primrec.ite _ _ _;
    · exact Primrec.nat_lt.comp ( Primrec.snd ) ( Primrec.const 2 );
    · exact Primrec.const 0;
    · convert Primrec.nat_div.comp ( Primrec.nat_mul.comp ( Primrec.fst.comp ( Primrec.fst ) ) ( Primrec.fst.comp ( Primrec.fst ) ) ) ( lnFix_primrec.comp ( Primrec.fst.comp ( Primrec.fst ) |> Primrec.pair <| Primrec.fst.comp ( Primrec.snd.comp ( Primrec.fst ) ) |> Primrec.pair <| Primrec.snd ) ) using 1

/-
**Phase 3.1.** The Schoenfeld matrix is primitive recursive.
-/
theorem schoenfeld_primrec : Primrec schoenfeld := by
  -- To prove that `schoenfeld` is primitive recursive, we need to show that it is a composition of primitive recursive functions.
  have h_schoenfeld_comp : Primrec (fun n => 6316547 * (absDiff (primePi n) (liInt ((n + 1) ^ 2) n n)) ^ 2 * ((n + 1) ^ 2) ^ 2) ∧ Primrec (fun n => 10000 * n * (lnFix ((n + 1) ^ 2) n n) ^ 2) := by
    constructor;
    · apply Primrec.nat_mul.comp (Primrec.nat_mul.comp (Primrec.const 6316547) (pow_primrec.comp (Primrec.nat_add.comp (Primrec.nat_sub.comp (primePi_primrec) (liInt_primrec.comp (Primrec.pair (pow_primrec.comp (Primrec.succ.comp Primrec.id) (Primrec.const 2)) (Primrec.pair Primrec.id Primrec.id)))) (Primrec.nat_sub.comp (liInt_primrec.comp (Primrec.pair (pow_primrec.comp (Primrec.succ.comp Primrec.id) (Primrec.const 2)) (Primrec.pair Primrec.id Primrec.id)) ) (primePi_primrec))) (Primrec.const 2))) (pow_primrec.comp (pow_primrec.comp (Primrec.succ.comp Primrec.id) (Primrec.const 2)) (Primrec.const 2));
    · have h_schoenfeld_primrec : Primrec (fun n => lnFix ((n + 1) ^ 2) n n) := by
        convert lnFix_primrec.comp ( Primrec.pair ( Primrec.comp ( pow_primrec.comp ( Primrec.succ.comp Primrec.id ) ( Primrec.const 2 ) ) ( Primrec.id ) ) ( Primrec.pair ( Primrec.id ) ( Primrec.id ) ) ) using 1;
      convert Primrec.nat_mul.comp ( Primrec.nat_mul.comp ( Primrec.const 10000 ) Primrec.id ) ( h_schoenfeld_primrec.comp Primrec.id |> Primrec.comp ( pow_primrec.comp ( Primrec.id ) ( Primrec.const 2 ) ) ) using 1;
  convert Primrec.nat_le.comp h_schoenfeld_comp.1 h_schoenfeld_comp.2 using 1;
  constructor <;> intro h <;> rw [ PrimrecPred ] at *;
  · exact ⟨ _, h ⟩;
  · convert h.choose_spec using 1;
    exact funext fun n => by unfold schoenfeld; aesop;

end SchoenfeldMatrix