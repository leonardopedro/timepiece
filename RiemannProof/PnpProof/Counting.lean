import Mathlib

/-!
# Part 2: Computability and counting

This file formalizes the computability/counting facts (C1, C3–C5) of the
`pnp.tex` formalization plan. (C2, the digit-null statement, lives in
`Counting.lean` as well.)
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

namespace PnpProof

/-! ### C1. Computable functions are countable -/

theorem countable_computable : {f : ℕ → ℕ | Computable f}.Countable := by
  convert Set.countable_range ( fun c : Nat.Partrec.Code => fun n => ( Nat.Partrec.Code.eval c n |> Part.toOption |> Option.getD <| 0 ) ) |> Set.Countable.mono fun f hf => ?_;
  obtain ⟨ c, hc ⟩ := Nat.Partrec.Code.exists_code.1 hf;
  use c;
  ext n; simp [hc];
  exact fun _ _ => Classical.propDecidable _

/-
Variant used downstream: computable functions `ℕ → Bool` are countable.
-/
theorem countable_computable_bool : {f : ℕ → Bool | Computable f}.Countable := by
  convert PnpProof.countable_computable;
  constructor <;> intro h;
  · convert PnpProof.countable_computable;
  · refine' Set.Countable.mono _ ( h.image _ );
    swap;
    exact fun f n => if f n = 0 then Bool.true else Bool.false;
    intro f hf; use fun n => if f n = Bool.true then 0 else 1; simp +decide [ hf ] ;
    convert Computable.cond ( hf ) ( Computable.const 0 ) ( Computable.const 1 ) using 1;
    exact funext fun n => by cases f n <;> rfl;

/-! ### C3. Boolean circuits -/

/-- A gate reading from `m` available nodes. `copy` enables padding. -/
inductive Gate (m : ℕ)
  | and (i j : Fin m) | or (i j : Fin m) | not (i : Fin m) | copy (i : Fin m)
  deriving DecidableEq, Fintype

/-- A circuit with `n` inputs and `s` gates, output = last gate.
    Node `k` (a gate) may only read nodes `< n + k`. -/
def Circuit (n s : ℕ) := (k : Fin s) → Gate (n + k)

/-- Value of node `k` (inputs `0..n-1` then gates), by well-founded recursion. -/
def Circuit.nodeValNat {n s : ℕ} (C : Circuit n s) (x : Fin n → Bool) (k : ℕ) : Bool :=
  if hk : k < n then x ⟨k, hk⟩
  else if hks : k - n < s then
    match _h : C ⟨k - n, hks⟩ with
    | .and i j => (C.nodeValNat x i.val) && (C.nodeValNat x j.val)
    | .or i j => (C.nodeValNat x i.val) || (C.nodeValNat x j.val)
    | .not i => !(C.nodeValNat x i.val)
    | .copy i => (C.nodeValNat x i.val)
  else false
termination_by k
decreasing_by
  all_goals (
    have hi := i.isLt
    have hj := not_lt.mp hk
    simp only [Nat.add_sub_cancel' hj] at hi
    omega)

/-- The function computed by a circuit with `s+1` gates (output is the last node). -/
def Circuit.eval {n s : ℕ} (C : Circuit n (s + 1)) (x : Fin n → Bool) : Bool :=
  C.nodeValNat x (n + s)

/-- Functions on `n` bits computable by some circuit with `s+1` gates. -/
def computableBySize (n s : ℕ) : Set ((Fin n → Bool) → Bool) :=
  {f | ∃ C : Circuit n (s+1), C.eval = f}

instance (n s : ℕ) : Fintype (Circuit n s) := by
  unfold Circuit; infer_instance

/-! ### C4. Circuit counting -/

theorem card_gate (m : ℕ) : Fintype.card (Gate m) = 2 * m^2 + 2 * m := by
  rw [ Fintype.card_eq_nat_card ];
  rw [ Nat.card_congr ( Equiv.ofBijective _ ⟨ _, _ ⟩ ) ];
  any_goals exact ( Fin m × Fin m ) ⊕ ( Fin m × Fin m ) ⊕ ( Fin m ) ⊕ ( Fin m );
  rotate_left;
  exact fun x => match x with | .and i j => Sum.inl ( i, j ) | .or i j => Sum.inr ( Sum.inl ( i, j ) ) | .not i => Sum.inr ( Sum.inr ( Sum.inl i ) ) | .copy i => Sum.inr ( Sum.inr ( Sum.inr i ) );
  · intro x y; aesop;
  · intro x;
    rcases x with ( ⟨ i, j ⟩ | ⟨ i, j ⟩ | i | i ) <;> [ exact ⟨ Gate.and i j, rfl ⟩ ; exact ⟨ Gate.or i j, rfl ⟩ ; exact ⟨ Gate.not i, rfl ⟩ ; exact ⟨ Gate.copy i, rfl ⟩ ];
  · norm_num ; ring

/-
If two circuits agree on all common gate indices, their node values agree
    on every node below `n + s`.
-/
theorem Circuit.nodeValNat_agree {n s t : ℕ} (C : Circuit n s) (D : Circuit n t)
    (x : Fin n → Bool) (hst : s ≤ t)
    (hagree : ∀ (j : ℕ) (hjs : j < s) (hjt : j < t), C ⟨j, hjs⟩ = D ⟨j, hjt⟩)
    (k : ℕ) (hk : k < n + s) : D.nodeValNat x k = C.nodeValNat x k := by
  induction' k using Nat.strong_induction_on with k ih;
  unfold Circuit.nodeValNat;
  split_ifs <;> try omega;
  · rfl;
  · rw [ hagree _ ‹_› ‹_› ];
    rcases h : D ⟨ k - n, by linarith ⟩ with ( _ | _ | _ | _ ) <;> simp +decide [ h ];
    · grind +qlia;
    · grind;
    · grind;
    · exact ih _ ( by linarith [ Fin.is_lt ‹_›, Nat.sub_add_cancel ( by linarith : n ≤ k ) ] ) ( by linarith [ Fin.is_lt ‹_›, Nat.sub_add_cancel ( by linarith : n ≤ k ) ] )

theorem computableBySize_mono (n : ℕ) {s t : ℕ} (h : s ≤ t) :
    computableBySize n s ⊆ computableBySize n t := by
  intro f hf
  obtain ⟨C, hC⟩ := hf
  by_cases hs : s = t;
  · subst hs; exact ⟨ C, hC ⟩ ;
  · -- Since $s < t$, we can build a new circuit $D$ with $t+1$ gates by appending $t-s$ copy gates to $C$.
    obtain ⟨D, hD⟩ : ∃ D : Circuit n (t + 1), (∀ j (hj : j < s + 1), D ⟨j, by linarith⟩ = C ⟨j, hj⟩) ∧ (∀ j (hj : s + 1 ≤ j ∧ j < t + 1), D ⟨j, by linarith⟩ = Gate.copy ⟨n + s, by linarith⟩) := by
      use fun ⟨j, hj⟩ => if h : j < s + 1 then C ⟨j, h⟩ else Gate.copy ⟨n + s, by linarith⟩;
      grind;
    -- By definition of $D$, we know that $D.nodeValNat x (n+t) = D.nodeValNat x (n+s)$ for all $x$.
    have hD_nodeValNat : ∀ x : Fin n → Bool, D.nodeValNat x (n + t) = D.nodeValNat x (n + s) := by
      intro x;
      rw [ Circuit.nodeValNat ];
      split_ifs <;> norm_num at *;
      · grind;
      · rw [ hD.2 _ ( by omega ) ( by omega ) ];
    -- By definition of $D$, we know that $D.nodeValNat x (n+s) = C.nodeValNat x (n+s)$ for all $x$.
    have hD_nodeValNat_eq : ∀ x : Fin n → Bool, D.nodeValNat x (n + s) = C.nodeValNat x (n + s) := by
      intros x
      apply Circuit.nodeValNat_agree C D x (by linarith) (by
      exact fun j hj₁ hj₂ => hD.1 j hj₁ ▸ rfl) (n + s) (by linarith);
    exact ⟨ D, funext fun x => by unfold Circuit.eval at *; aesop ⟩

theorem card_circuit_le (n s : ℕ) (hns : 1 ≤ n) :
    Fintype.card (Circuit n s) ≤ (4 * (n + s)^2)^s := by
  erw [ Fintype.card_pi ];
  refine' le_trans ( Finset.prod_le_prod' fun i _ => show Fintype.card ( Gate ( n + i ) ) ≤ 4 * ( n + s ) ^ 2 from _ ) _;
  · rw [ card_gate ] ; nlinarith [ show ( i : ℕ ) < s from i.2 ];
  · norm_num

/-! ### C5. Shannon: almost all Boolean functions need many gates -/

/-
The number of functions computable by `s+1` gates is at most the number of
    circuits with `s+1` gates.
-/
theorem card_computableBySize_le_card_circuit (n s : ℕ) :
    Nat.card (computableBySize n s) ≤ Fintype.card (Circuit n (s + 1)) := by
  rw [ ← Nat.card_eq_fintype_card ];
  apply_rules [ Nat.card_le_card_of_surjective ];
  swap;
  exact fun C => ⟨ _, ⟨ C, rfl ⟩ ⟩;
  exact fun x => by cases x; aesop;

/-
Base bound: `4*(n+s+1)^2 ≤ 2^(2n+2)` where `s = 2^n/(4n)`.
-/
theorem shannon_aux_base (n : ℕ) (hn : 8 ≤ n) :
    4 * (n + (2^n / (4*n) + 1))^2 ≤ 2^(2*n + 2) := by
  -- First show n + s + 1 ≤ 2^n.
  have h_base : n + (2^n / (4 * n) + 1) ≤ 2^n := by
    have h_base : 4 * (n + 1) ≤ 3 * 2^n := by
      exact Nat.le_induction ( by decide ) ( fun k hk ih ↦ by rw [ pow_succ' ] ; linarith ) _ hn;
    nlinarith [ Nat.div_mul_le_self ( 2 ^ n ) ( 4 * n ) ];
  convert Nat.mul_le_mul_left 4 ( Nat.pow_le_pow_left h_base 2 ) using 1 ; ring

/-
Exponent bound: `(2n+2)*(s+1) ≤ 3*2^n/4` where `s = 2^n/(4n)`.
-/
theorem shannon_aux_exp (n : ℕ) (hn : 8 ≤ n) :
    (2*n + 2) * (2^n / (4*n) + 1) ≤ 3 * 2^n / 4 := by
  -- We'll use that $2^n \geq 16n$ for $n \geq 8$.
  have h_exp : 2^n ≥ 16 * n := by
    exact Nat.le_induction ( by decide ) ( fun k hk ih => by rw [ pow_succ' ] ; linarith ) n hn;
  nlinarith [ Nat.div_mul_le_self ( 2 ^ n ) ( 4 * n ), Nat.div_add_mod ( 3 * 2 ^ n ) 4, Nat.mod_lt ( 3 * 2 ^ n ) zero_lt_four ]

theorem card_computableBySize_le (n : ℕ) (hn : 8 ≤ n) :
    Nat.card (computableBySize n (2^n / (4*n))) ≤ 2^(3 * 2^n / 4) := by
  refine le_trans ( card_computableBySize_le_card_circuit n _ ) ?_;
  refine le_trans ( card_circuit_le n _ ?_ ) ?_;
  · grind;
  · refine le_trans ( Nat.pow_le_pow_left ( shannon_aux_base n hn ) _ ) ?_;
    rw [ ← pow_mul ];
    exact pow_le_pow_right₀ ( by decide ) ( shannon_aux_exp n hn )

theorem shannon_fraction (n : ℕ) (hn : 8 ≤ n) :
    Nat.card (computableBySize n (2^n / (4*n))) * 2^(2^n / 4)
      ≤ Fintype.card ((Fin n → Bool) → Bool) := by
  refine' le_trans ( Nat.mul_le_mul_right _ ( card_computableBySize_le n hn ) ) _;
  norm_num [ ← pow_add ];
  gcongr <;> omega

/-! ### C2. Computably-coded reals form a Lebesgue-null set -/

/-- The `k`-th binary digit of `x ∈ [0,1)` (digit just after scaling by `2^k`). -/
def binDigit (k : ℕ) (x : ℝ) : Bool := decide (1 ≤ Int.fract (2^k * x) * 2)

/-
Floor-doubling identity.
-/
theorem floor_two_mul (a : ℝ) :
    ⌊2 * a⌋ = 2 * ⌊a⌋ + (if 1 ≤ Int.fract a * 2 then 1 else 0) := by
  split_ifs <;> [ exact Int.floor_eq_iff.mpr ⟨ by push_cast; linarith [ Int.fract_add_floor a, Int.fract_nonneg a, Int.fract_lt_one a ], by push_cast; linarith [ Int.fract_add_floor a, Int.fract_nonneg a, Int.fract_lt_one a ] ⟩ ; exact Int.floor_eq_iff.mpr ⟨ by push_cast; linarith [ Int.fract_add_floor a, Int.fract_nonneg a, Int.fract_lt_one a ], by push_cast; linarith [ Int.fract_add_floor a, Int.fract_nonneg a, Int.fract_lt_one a ] ⟩ ]

/-
The floor of `2^(k+1) * x` in terms of the floor of `2^k * x` and the digit.
-/
theorem floor_succ (k : ℕ) (x : ℝ) :
    ⌊2^(k+1) * x⌋ = 2 * ⌊2^k * x⌋ + (if binDigit k x then 1 else 0) := by
  convert floor_two_mul ( 2 ^ k * x ) using 1 ; ring;
  unfold binDigit; aesop;

/-
If two reals have the same integer part and the same binary digits, their
    `2^k`-scaled floors agree for every `k`.
-/
theorem floor_eq_of_digits_eq (x y : ℝ) (hx : ⌊x⌋ = ⌊y⌋)
    (h : ∀ k, binDigit k x = binDigit k y) (k : ℕ) :
    ⌊2^k * x⌋ = ⌊2^k * y⌋ := by
  induction' k with k ih <;> simp_all +decide [ pow_succ', mul_assoc ];
  rw [ floor_two_mul ( 2 ^ k * x ), floor_two_mul ( 2 ^ k * y ) ];
  unfold binDigit at h; aesop;

/-
The digit map is injective on `[0,1)`.
-/
theorem binDigit_injOn :
    Set.InjOn (fun x => (fun k => binDigit k x)) (Ico (0:ℝ) 1) := by
  intro x hx y hy; have := Real.pi_ne_zero; simp_all +decide [ funext_iff ];
  intro h
  have h_floor : ∀ k : ℕ, ⌊2^k * x⌋ = ⌊2^k * y⌋ := by
    exact fun k => floor_eq_of_digits_eq x y ( by norm_num [ show ⌊x⌋ = 0 by exact Int.floor_eq_iff.mpr ⟨ by norm_num; linarith, by norm_num; linarith ⟩, show ⌊y⌋ = 0 by exact Int.floor_eq_iff.mpr ⟨ by norm_num; linarith, by norm_num; linarith ⟩ ] ) h k;
  -- For each k, by Int.floor_le and Int.lt_floor_add_one, both 2^k*x and 2^k*y lie in [c, c+1) with c = ⌊2^k*x⌋ = ⌊2^k*y⌋, so |2^k*x - 2^k*y| < 1, i.e. 2^k * |x - y| < 1, hence |x - y| < (2^k)⁻¹ (divide; 2^k > 0).
  have h_diff : ∀ k : ℕ, |x - y| < (2^k : ℝ)⁻¹ := by
    intro k; have := h_floor k; rw [ Int.floor_eq_iff ] at this; norm_num at *;
    rw [ abs_lt ] ; constructor <;> nlinarith [ pow_pos ( zero_lt_two' ℝ ) k, mul_inv_cancel₀ ( ne_of_gt ( pow_pos ( zero_lt_two' ℝ ) k ) ), Int.floor_le ( 2 ^ k * y ), Int.lt_floor_add_one ( 2 ^ k * y ) ];
  exact sub_eq_zero.mp ( by simpa using le_antisymm ( le_of_tendsto_of_tendsto' tendsto_const_nhds ( tendsto_inv_atTop_zero.comp ( tendsto_pow_atTop_atTop_of_one_lt one_lt_two ) ) fun k => le_of_lt ( h_diff k ) ) ( abs_nonneg _ ) )

theorem null_computable_digits :
    volume {x : ℝ | x ∈ Ico (0:ℝ) 1 ∧ Computable fun k => binDigit k x} = 0 := by
  -- The set of computable reals in [0,1) is countable.
  have h_countable : Set.Countable {x : ℝ | x ∈ Set.Ico 0 1 ∧ Computable (fun k => binDigit k x)} := by
    have h_image_countable : Set.Countable (Set.image (fun x : ℝ => fun k : ℕ => binDigit k x) {x : ℝ | x ∈ Ico 0 1 ∧ Computable (fun k => binDigit k x)}) := by
      exact Set.Countable.mono ( by aesop_cat ) ( countable_computable_bool );
    have h_inj : Set.InjOn (fun x : ℝ => fun k : ℕ => binDigit k x) (Set.Ico 0 1) := by
      convert binDigit_injOn using 1;
    exact Set.MapsTo.countable_of_injOn ( Set.mapsTo_image _ _ ) ( h_inj.mono fun x hx => hx.1 ) h_image_countable;
  exact h_countable.measure_zero MeasureTheory.MeasureSpace.volume

end PnpProof