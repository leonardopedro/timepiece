import Mathlib
import PnpProof.Counting

/-!
# Part 4 / N1: the explicit `O(k)` comparator circuit

This file builds, for each `k ≥ 1`, an explicit Boolean `Circuit (3*k) (s+1)`
with `s ≤ 50*k + 50` that decides the §3 verifier
`(glo ≤ u ∧ u ≤ ghi)` on three `k`-bit numbers packed little-endian by `bitsOf`.

The construction is a standard big-endian ripple comparator built from the
`Circuit` theory of `Counting.lean`:

* `Gate.eval`, `Circuit.snoc` and the two evaluation lemmas
  `snoc_nodeValNat_lt` / `snoc_nodeValNat_top` give a clean way to append one
  gate and reason about node values.
* `step` appends one comparator stage (9 gates) updating an `eq`/`lt` register
  pair; `buildLT` folds `step` over the bit positions, MSB first.
* `baseSt` provides the `TRUE`/`FALSE` constant nodes seeding the registers.
* `fullCircuit` chains two comparators (for `u<glo` and `ghi<u`) and a final
  `¬·∧¬·` to output the verifier.

See `PNP_IMPLEMENTATION_PLAN.md`, Part 4 (M5) step N1, for the English proof.
-/

open scoped BigOperators

noncomputable section

namespace PnpProof

/-! ### Generic single-gate append infrastructure -/

/-- Evaluate a gate against a node-value function. -/
def Gate.eval {m : ℕ} (g : Gate m) (vals : ℕ → Bool) : Bool :=
  match g with
  | .and i j => vals i.val && vals j.val
  | .or i j => vals i.val || vals j.val
  | .not i => !(vals i.val)
  | .copy i => vals i.val

/-- Append one gate to a circuit (the gate may read any earlier node). -/
def Circuit.snoc {n s : ℕ} (C : Circuit n s) (g : Gate (n + s)) : Circuit n (s+1) :=
  Fin.snoc C g

theorem nodeValNat_input {n s : ℕ} (C : Circuit n s) (x : Fin n → Bool) (k : ℕ)
    (hk : k < n) : C.nodeValNat x k = x ⟨k, hk⟩ := by
  rw [Circuit.nodeValNat]; rw [dif_pos hk]

theorem nodeValNat_gate {n s : ℕ} (C : Circuit n s) (x : Fin n → Bool) (k : ℕ)
    (hk : ¬ k < n) (hks : k - n < s) :
    C.nodeValNat x k = (C ⟨k - n, hks⟩).eval (C.nodeValNat x) := by
  conv_lhs => rw [Circuit.nodeValNat]
  rw [dif_neg hk, dif_pos hks]
  cases C ⟨k - n, hks⟩ <;> simp [Gate.eval]

theorem snoc_nodeValNat_lt {n s : ℕ} (C : Circuit n s) (g : Gate (n + s))
    (x : Fin n → Bool) (k : ℕ) (hk : k < n + s) :
    (C.snoc g).nodeValNat x k = C.nodeValNat x k := by
  apply Circuit.nodeValNat_agree C (C.snoc g) x (Nat.le_succ s)
  · intro j hjs hjt
    exact (Fin.snoc_castSucc (α := fun i => Gate (n + i)) g C ⟨j, hjs⟩).symm
  · exact hk

theorem snoc_nodeValNat_top {n s : ℕ} (C : Circuit n s) (g : Gate (n + s))
    (x : Fin n → Bool) :
    (C.snoc g).nodeValNat x (n + s) = g.eval (C.nodeValNat x) := by
  rw [nodeValNat_gate (C.snoc g) x (n+s) (by omega) (by simp)]
  rw [show (⟨(n+s)-n, by simp⟩ : Fin (s+1)) = Fin.last s from Fin.ext (by simp)]
  rw [show (C.snoc g) (Fin.last s) = g from
    Fin.snoc_last (α := fun i => Gate (n + i)) g C]
  cases g with
  | and i j => simp [Gate.eval, snoc_nodeValNat_lt _ _ x i.val i.isLt,
      snoc_nodeValNat_lt _ _ x j.val j.isLt]
  | or i j => simp [Gate.eval, snoc_nodeValNat_lt _ _ x i.val i.isLt,
      snoc_nodeValNat_lt _ _ x j.val j.isLt]
  | not i => simp [Gate.eval, snoc_nodeValNat_lt _ _ x i.val i.isLt]
  | copy i => simp [Gate.eval, snoc_nodeValNat_lt _ _ x i.val i.isLt]

/-- Clamp a nat to a valid wire index (the fallback `0` is never reached when
    the index is in range). -/
def clampFin (m : ℕ) (hm : 0 < m) (p : ℕ) : Fin m :=
  if h : p < m then ⟨p, h⟩ else ⟨0, hm⟩

theorem clampFin_val {m : ℕ} (hm : 0 < m) {p : ℕ} (h : p < m) :
    (clampFin m hm p).val = p := by
  simp [clampFin, h]

/-! ### Comparator builder state and one stage -/

/-- Builder state: a circuit so far, plus the two register node indices
    (`eqN`, the eq-flag; `ltN`, the lt-flag). -/
structure St (n : ℕ) where
  s : ℕ
  C : Circuit n s
  eqN : ℕ
  ltN : ℕ

/-- One ripple-comparator stage for the bit at nodes `aN` (for `a`) and `bN`
    (for `b`). Appends 9 gates and points the registers at the new
    `eq'`/`lt'` nodes. -/
def step {n : ℕ} (hn : 0 < n) (st : St n) (aN bN : ℕ) : St n :=
  let s := st.s
  let C0 := st.C
  let na : Gate (n + s) := Gate.not (clampFin (n + s) (by omega) aN)
  let C1 := C0.snoc na
  let nb : Gate (n + (s+1)) := Gate.not (clampFin (n + (s+1)) (by omega) bN)
  let C2 := C1.snoc nb
  let t1 : Gate (n + (s+2)) := Gate.and (clampFin (n + (s+2)) (by omega) aN)
                                        (clampFin (n + (s+2)) (by omega) bN)
  let C3 := C2.snoc t1
  let t2 : Gate (n + (s+3)) := Gate.and (clampFin (n + (s+3)) (by omega) (n + s))
                                        (clampFin (n + (s+3)) (by omega) (n + s + 1))
  let C4 := C3.snoc t2
  let xnor : Gate (n + (s+4)) := Gate.or (clampFin (n + (s+4)) (by omega) (n + s + 2))
                                         (clampFin (n + (s+4)) (by omega) (n + s + 3))
  let C5 := C4.snoc xnor
  let eq' : Gate (n + (s+5)) := Gate.and (clampFin (n + (s+5)) (by omega) st.eqN)
                                         (clampFin (n + (s+5)) (by omega) (n + s + 4))
  let C6 := C5.snoc eq'
  let la : Gate (n + (s+6)) := Gate.and (clampFin (n + (s+6)) (by omega) (n + s))
                                        (clampFin (n + (s+6)) (by omega) bN)
  let C7 := C6.snoc la
  let t4 : Gate (n + (s+7)) := Gate.and (clampFin (n + (s+7)) (by omega) st.eqN)
                                        (clampFin (n + (s+7)) (by omega) (n + s + 6))
  let C8 := C7.snoc t4
  let lt' : Gate (n + (s+8)) := Gate.or (clampFin (n + (s+8)) (by omega) st.ltN)
                                        (clampFin (n + (s+8)) (by omega) (n + s + 7))
  let C9 := C8.snoc lt'
  { s := s + 9, C := C9, eqN := n + s + 5, ltN := n + s + 8 }

theorem step_s {n : ℕ} (hn : 0 < n) (st : St n) (aN bN : ℕ) :
    (step hn st aN bN).s = st.s + 9 := rfl

theorem step_eqN {n : ℕ} (hn : 0 < n) (st : St n) (aN bN : ℕ) :
    (step hn st aN bN).eqN = n + st.s + 5 := rfl

theorem step_ltN {n : ℕ} (hn : 0 < n) (st : St n) (aN bN : ℕ) :
    (step hn st aN bN).ltN = n + st.s + 8 := rfl

theorem step_preserves {n : ℕ} (hn : 0 < n) (st : St n) (aN bN : ℕ)
    (x : Fin n → Bool) (k : ℕ) (hk : k < n + st.s) :
    (step hn st aN bN).C.nodeValNat x k = st.C.nodeValNat x k := by
  change (((((((((st.C.snoc _).snoc _).snoc _).snoc _).snoc _).snoc _).snoc _).snoc
    _).snoc _).nodeValNat x k = _
  rw [snoc_nodeValNat_lt _ _ x k (by omega)]
  rw [snoc_nodeValNat_lt _ _ x k (by omega)]
  rw [snoc_nodeValNat_lt _ _ x k (by omega)]
  rw [snoc_nodeValNat_lt _ _ x k (by omega)]
  rw [snoc_nodeValNat_lt _ _ x k (by omega)]
  rw [snoc_nodeValNat_lt _ _ x k (by omega)]
  rw [snoc_nodeValNat_lt _ _ x k (by omega)]
  rw [snoc_nodeValNat_lt _ _ x k (by omega)]
  rw [snoc_nodeValNat_lt _ _ x k (by omega)]

/-- Value at the new `eq'` register after one stage:
    `eq' = oldEq ∧ (aᵢ ↔ bᵢ)`. -/
theorem step_eqN_val {n : ℕ} (hn : 0 < n) (st : St n) (aN bN : ℕ)
    (x : Fin n → Bool)
    (haN : aN < n + st.s) (hbN : bN < n + st.s)
    (heN : st.eqN < n + st.s) (_hlN : st.ltN < n + st.s) :
    (step hn st aN bN).C.nodeValNat x (n + st.s + 5) =
      ((st.C.nodeValNat x st.eqN) &&
        ((st.C.nodeValNat x aN && st.C.nodeValNat x bN) ||
         (!(st.C.nodeValNat x aN) && !(st.C.nodeValNat x bN)))) := by
  change (((((((((st.C.snoc _).snoc _).snoc _).snoc _).snoc _).snoc _).snoc _).snoc
    _).snoc _).nodeValNat x (n + st.s + 5) = _
  simp only [show n + st.s + 5 = n + (st.s + 5) from by omega,
    show n + st.s + 4 = n + (st.s + 4) from by omega,
    show n + st.s + 3 = n + (st.s + 3) from by omega,
    show n + st.s + 2 = n + (st.s + 2) from by omega,
    show n + st.s + 1 = n + (st.s + 1) from by omega]
  simp (disch := omega) only [snoc_nodeValNat_top, snoc_nodeValNat_lt, Gate.eval,
    clampFin_val]

/-
Value at the new `lt'` register after one stage:
    `lt' = oldLt ∨ (oldEq ∧ ¬aᵢ ∧ bᵢ)`.
-/
theorem step_ltN_val {n : ℕ} (hn : 0 < n) (st : St n) (aN bN : ℕ)
    (x : Fin n → Bool)
    (haN : aN < n + st.s) (hbN : bN < n + st.s)
    (heN : st.eqN < n + st.s) (hlN : st.ltN < n + st.s) :
    (step hn st aN bN).C.nodeValNat x (n + st.s + 8) =
      ((st.C.nodeValNat x st.ltN) ||
        ((st.C.nodeValNat x st.eqN) &&
          (!(st.C.nodeValNat x aN) && st.C.nodeValNat x bN))) := by
  change (((((((((st.C.snoc _).snoc _).snoc _).snoc _).snoc _).snoc _).snoc _).snoc
    _).snoc _).nodeValNat x (n + st.s + 8) = _
  simp only [show n + st.s + 8 = n + (st.s + 8) from by omega,
    show n + st.s + 7 = n + (st.s + 7) from by omega,
    show n + st.s + 6 = n + (st.s + 6) from by omega,
    show n + st.s + 5 = n + (st.s + 5) from by omega,
    show n + st.s + 4 = n + (st.s + 4) from by omega,
    show n + st.s + 3 = n + (st.s + 3) from by omega,
    show n + st.s + 2 = n + (st.s + 2) from by omega,
    show n + st.s + 1 = n + (st.s + 1) from by omega]
  simp (disch := omega) only [snoc_nodeValNat_top, snoc_nodeValNat_lt, Gate.eval,
    clampFin_val]

/-! ### Folding the stages -/

/-- Process bits `m-1, …, 0` (MSB first), descending the prefix levels. -/
def buildLT {n : ℕ} (hn : 0 < n) (aPos bPos : ℕ → ℕ) : ℕ → St n → St n
  | 0, st => st
  | m+1, st => buildLT hn aPos bPos m (step hn st (aPos m) (bPos m))

theorem buildLT_s {n : ℕ} (hn : 0 < n) (aPos bPos : ℕ → ℕ) (m : ℕ) (st : St n) :
    (buildLT hn aPos bPos m st).s = st.s + 9 * m := by
  induction m generalizing st with
  | zero => simp [buildLT]
  | succ m ih => rw [buildLT, ih, step_s]; ring

theorem buildLT_preserves {n : ℕ} (hn : 0 < n) (aPos bPos : ℕ → ℕ) (m : ℕ)
    (st : St n) (x : Fin n → Bool) (k : ℕ) (hk : k < n + st.s) :
    (buildLT hn aPos bPos m st).C.nodeValNat x k = st.C.nodeValNat x k := by
  induction m generalizing st with
  | zero => simp [buildLT]
  | succ m ih =>
      rw [buildLT]
      rw [ih (step hn st (aPos m) (bPos m)) (by rw [step_s]; omega)]
      exact step_preserves hn st (aPos m) (bPos m) x k hk

/-- The bit-recursion identity driving the big-endian ripple comparator. -/
theorem div_pow_succ_compare (a b j : ℕ) :
    (a / 2^j = b / 2^j ↔
        (a / 2^(j+1) = b / 2^(j+1)) ∧ (a.testBit j = b.testBit j)) ∧
    (a / 2^j < b / 2^j ↔
        (a / 2^(j+1) < b / 2^(j+1)) ∨
          ((a / 2^(j+1) = b / 2^(j+1)) ∧ a.testBit j = false ∧ b.testBit j = true)) := by
  simp +decide [ Nat.testBit, pow_succ, ← Nat.div_div_eq_div_mul ]
  constructor <;> constructor <;> intro h <;> omega

/-
The comparator correctness invariant: starting from a state whose registers
    hold the level-`m` prefix comparisons of `a` and `b`, after processing `m`
    bits the registers hold the level-`0` comparisons (`a = b`, `a < b`).
-/
theorem buildLT_spec {n : ℕ} (hn : 0 < n) (aPos bPos : ℕ → ℕ) (a b : ℕ)
    (x : Fin n → Bool) (m : ℕ) : ∀ st : St n,
    st.eqN < n + st.s → st.ltN < n + st.s →
    st.C.nodeValNat x st.eqN = decide (a / 2^m = b / 2^m) →
    st.C.nodeValNat x st.ltN = decide (a / 2^m < b / 2^m) →
    (∀ j, j < m → aPos j < n ∧ bPos j < n ∧
       st.C.nodeValNat x (aPos j) = a.testBit j ∧
       st.C.nodeValNat x (bPos j) = b.testBit j) →
    (buildLT hn aPos bPos m st).eqN < n + (buildLT hn aPos bPos m st).s ∧
    (buildLT hn aPos bPos m st).ltN < n + (buildLT hn aPos bPos m st).s ∧
    (buildLT hn aPos bPos m st).C.nodeValNat x (buildLT hn aPos bPos m st).eqN
      = decide (a / 2^0 = b / 2^0) ∧
    (buildLT hn aPos bPos m st).C.nodeValNat x (buildLT hn aPos bPos m st).ltN
      = decide (a / 2^0 < b / 2^0) := by
  induction' m with m ih generalizing a b x <;> simp_all +decide [ Nat.pow_succ' ];
  · exact fun st he hl hev hlv => ⟨ he, hl, hev, hlv ⟩;
  · intro st he hl hev hlv hbits
    specialize ih a b x (step hn st (aPos m) (bPos m)) (by
    rw [ step_eqN, step_s ] ; omega) (by
    rw [ step_ltN, step_s ] ; omega) (by
    have := div_pow_succ_compare a b m; simp_all +decide [ Nat.pow_succ', Nat.div_div_eq_div_mul ] ;
    convert step_eqN_val hn st ( aPos m ) ( bPos m ) x ( by linarith [ hbits m le_rfl ] ) ( by linarith [ hbits m le_rfl ] ) he hl using 1 ; simp +decide [ *, step_eqN ];
    cases a.testBit m <;> cases b.testBit m <;> simp +decide [ * ]) (by
    convert step_ltN_val hn st ( aPos m ) ( bPos m ) x _ _ he hl using 1 <;> norm_num [ hbits m le_rfl ];
    · have := div_pow_succ_compare a b m; simp_all +decide [ Nat.pow_succ', Nat.div_div_eq_div_mul ] ;
    · linarith [ hbits m le_rfl ];
    · linarith [ hbits m le_rfl ]) (by
    grind +suggestions);
    exact ih

/-! ### The base state with TRUE / FALSE constant nodes -/

/-- The empty circuit (no gates). -/
def Circuit.empty {n : ℕ} : Circuit n 0 := fun k => k.elim0

/-- Three constant gates from input node `0`: `¬x₀` at node `n`,
    `TRUE = x₀ ∨ ¬x₀` at node `n+1`, `FALSE = x₀ ∧ ¬x₀` at node `n+2`. The
    registers start at `eqN := n+1` (TRUE) and `ltN := n+2` (FALSE). -/
def baseSt {n : ℕ} (hn : 0 < n) : St n :=
  let g0 : Gate (n + 0) := Gate.not (clampFin n (by omega) 0)
  let C1 := Circuit.empty.snoc g0
  let g1 : Gate (n + 1) := Gate.or (clampFin (n+1) (by omega) 0) (clampFin (n+1) (by omega) n)
  let C2 := C1.snoc g1
  let g2 : Gate (n + 2) := Gate.and (clampFin (n+2) (by omega) 0) (clampFin (n+2) (by omega) n)
  let C3 := C2.snoc g2
  { s := 3, C := C3, eqN := n + 1, ltN := n + 2 }

theorem baseSt_s {n : ℕ} (hn : 0 < n) : (baseSt hn).s = 3 := rfl
theorem baseSt_eqN {n : ℕ} (hn : 0 < n) : (baseSt hn).eqN = n + 1 := rfl
theorem baseSt_ltN {n : ℕ} (hn : 0 < n) : (baseSt hn).ltN = n + 2 := rfl

/-
The TRUE register node evaluates to `true`.
-/
theorem baseSt_eqN_val {n : ℕ} (hn : 0 < n) (x : Fin n → Bool) :
    (baseSt hn).C.nodeValNat x (n + 1) = true := by
  -- Apply the lemma `snoc_nodeValNat_lt` to peel off the last gate.
  have h_peel : (baseSt hn).C.nodeValNat x (n + 1) = ((Circuit.empty.snoc (Gate.not (clampFin n hn 0))).snoc (Gate.or (clampFin (n + 1) (by omega) 0) (clampFin (n + 1) (by omega) n))).nodeValNat x (n + 1) := by
    convert snoc_nodeValNat_lt _ _ _ _ _ using 1;
    grind;
  -- Apply the lemma `snoc_nodeValNat_top` to the circuit after the first gate.
  have h_top : ((Circuit.empty.snoc (Gate.not (clampFin n hn 0))).snoc (Gate.or (clampFin (n + 1) (by omega) 0) (clampFin (n + 1) (by omega) n))).nodeValNat x (n + 1) = (Gate.or (clampFin (n + 1) (by omega) 0) (clampFin (n + 1) (by omega) n)).eval (Circuit.empty.snoc (Gate.not (clampFin n hn 0)) |>.nodeValNat x) := by
    convert snoc_nodeValNat_top _ _ _ using 1;
  -- Apply the lemma `snoc_nodeValNat_lt` to the circuit after the first gate.
  have h_peel2 : ((Circuit.empty.snoc (Gate.not (clampFin n hn 0))).nodeValNat x 0) = x ⟨0, hn⟩ ∧ ((Circuit.empty.snoc (Gate.not (clampFin n hn 0))).nodeValNat x n) = !(x ⟨0, hn⟩) := by
    convert snoc_nodeValNat_top Circuit.empty ( Gate.not ( clampFin n hn 0 ) ) x using 1;
    unfold Gate.eval; simp +decide [ clampFin ] ;
    unfold Circuit.nodeValNat; aesop;
  cases x ⟨ 0, hn ⟩ <;> simp_all +decide [ Gate.eval ]; all_goals unfold clampFin at * ; aesop

/-
The FALSE register node evaluates to `false`.
-/
theorem baseSt_ltN_val {n : ℕ} (hn : 0 < n) (x : Fin n → Bool) :
    (baseSt hn).C.nodeValNat x (n + 2) = false := by
  convert snoc_nodeValNat_top ( ( Circuit.empty.snoc ( Gate.not ( clampFin n hn 0 ) ) ).snoc ( Gate.or ( clampFin ( n + 1 ) ( by omega ) 0 ) ( clampFin ( n + 1 ) ( by omega ) n ) ) ) ( Gate.and ( clampFin ( n + 2 ) ( by omega ) 0 ) ( clampFin ( n + 2 ) ( by omega ) n ) ) x;
  unfold Gate.eval; simp +decide [ clampFin ] ;
  convert snoc_nodeValNat_top Circuit.empty ( Gate.not ( clampFin n hn 0 ) ) x;
  unfold clampFin; simp +decide [ hn ] ;
  convert Iff.rfl using 2;
  constructor <;> intro h <;> simp_all +decide [ snoc_nodeValNat_lt, snoc_nodeValNat_top ];
  · unfold Gate.eval; simp +decide [ Circuit.empty ] ;
  · convert snoc_nodeValNat_top Circuit.empty ( Gate.not ⟨ 0, hn ⟩ ) x using 1

/-! ### The packed input and the two comparators -/

/-- Pack three `k`-bit numbers little-endian into `Fin (3*k) → Bool`:
    `glo` on `[0,k)`, `ghi` on `[k,2k)`, `u` on `[2k,3k)`. -/
def bitsOf (k : ℕ) (glo ghi u : Fin (2^k)) : Fin (3*k) → Bool := fun i =>
  if i.val < k then (glo : ℕ).testBit i.val
  else if i.val < 2*k then (ghi : ℕ).testBit (i.val - k)
  else (u : ℕ).testBit (i.val - 2*k)

/-- First comparator: compares `a = u` (bits at `[2k,3k)`) against
    `b = glo` (bits at `[0,k)`). -/
def cmp1 (k : ℕ) (hk : 1 ≤ k) : St (3*k) :=
  buildLT (by omega) (fun j => 2*k + j) (fun j => j) k (baseSt (by omega))

/-- Second comparator: compares `a = ghi` (bits at `[k,2k)`) against
    `b = u` (bits at `[2k,3k)`), reusing the constant nodes for its registers. -/
def cmp2 (k : ℕ) (hk : 1 ≤ k) : St (3*k) :=
  buildLT (by omega) (fun j => k + j) (fun j => 2*k + j) k
    { (cmp1 k hk) with eqN := 3*k + 1, ltN := 3*k + 2 }

theorem cmp1_s (k : ℕ) (hk : 1 ≤ k) : (cmp1 k hk).s = 3 + 9 * k := by
  rw [cmp1, buildLT_s, baseSt_s]

theorem cmp2_s (k : ℕ) (hk : 1 ≤ k) : (cmp2 k hk).s = 3 + 18 * k := by
  rw [cmp2, buildLT_s]; show (cmp1 k hk).s + 9 * k = _; rw [cmp1_s]; ring

/-
The lt-register of the first comparator decides `u < glo`.
-/
theorem cmp1_ltN_val (k : ℕ) (hk : 1 ≤ k) (glo ghi u : Fin (2^k)) :
    (cmp1 k hk).ltN < 3*k + (cmp1 k hk).s ∧
    (cmp1 k hk).C.nodeValNat (bitsOf k glo ghi u) (cmp1 k hk).ltN
      = decide ((u : ℕ) < (glo : ℕ)) := by
  have := buildLT_spec ( by omega : 0 < 3 * k ) ( fun j => 2 * k + j ) ( fun j => j ) u glo ( bitsOf k glo ghi u ) k ( baseSt ( by omega ) ) ?_ ?_ ?_ ?_ ?_;
  all_goals norm_num [ cmp1, baseSt_s, baseSt_eqN, baseSt_ltN ] at *;
  · exact ⟨ this.2.1, this.2.2.2 ⟩;
  · rw [ Nat.div_eq_of_lt, Nat.div_eq_of_lt ] <;> norm_num [ Fin.is_lt ];
    convert baseSt_eqN_val ( by omega : 0 < 3 * k ) ( bitsOf k glo ghi u ) using 1;
  · rw [ Nat.div_eq_of_lt, Nat.div_eq_of_lt ] <;> norm_num [ baseSt_ltN_val ];
  · intro j hj
    constructor;
    · grind;
    · refine' ⟨ by linarith, _, _ ⟩;
      · rw [ nodeValNat_input ];
        all_goals norm_num [ bitsOf ];
        · grind;
        · linarith;
      · rw [ nodeValNat_input ];
        all_goals norm_num [ bitsOf ]; all_goals grind

/-
The lt-register of the second comparator decides `ghi < u`.
-/
theorem cmp2_ltN_val (k : ℕ) (hk : 1 ≤ k) (glo ghi u : Fin (2^k)) :
    (cmp2 k hk).ltN < 3*k + (cmp2 k hk).s ∧
    (cmp2 k hk).C.nodeValNat (bitsOf k glo ghi u) (cmp2 k hk).ltN
      = decide ((ghi : ℕ) < (u : ℕ)) := by
  have := buildLT_spec ( by omega : 0 < 3 * k ) ( fun j => k + j ) ( fun j => 2 * k + j ) ( ghi : ℕ ) ( u : ℕ ) ( bitsOf k glo ghi u ) k ( { ( cmp1 k hk ) with eqN := 3 * k + 1, ltN := 3 * k + 2 } ) ?_ ?_ ?_ ?_ ?_;
  all_goals norm_num [ cmp2, cmp1_s, baseSt_s, baseSt_eqN, baseSt_ltN ] at *;
  any_goals omega;
  · exact ⟨ this.2.1, this.2.2.2 ⟩;
  · rw [ Nat.div_eq_of_lt, Nat.div_eq_of_lt ] <;> norm_num [ Fin.is_lt ];
    convert buildLT_preserves ( by omega : 0 < 3 * k ) ( fun j => 2 * k + j ) ( fun j => j ) k ( baseSt ( by omega ) ) ( bitsOf k glo ghi u ) ( 3 * k + 1 ) ( by linarith [ baseSt_s ( by omega : 0 < 3 * k ) ] ) using 1;
    convert baseSt_eqN_val ( by omega : 0 < 3 * k ) ( bitsOf k glo ghi u ) |> Eq.symm using 1;
  · convert baseSt_ltN_val ( by omega : 0 < 3 * k ) ( bitsOf k glo ghi u ) using 1;
    · convert buildLT_preserves ( by omega : 0 < 3 * k ) ( fun j => 2 * k + j ) ( fun j => j ) k ( baseSt ( by omega ) ) ( bitsOf k glo ghi u ) ( 3 * k + 2 ) ( by linarith [ baseSt_s ( by omega : 0 < 3 * k ) ] ) using 1;
    · rw [ Nat.div_eq_of_lt, Nat.div_eq_of_lt ] <;> norm_num [ Fin.is_lt ];
  · intro j hj
    have h_preserve : (cmp1 k hk).C.nodeValNat (bitsOf k glo ghi u) (k + j) = (bitsOf k glo ghi u) ⟨k + j, by linarith⟩ ∧ (cmp1 k hk).C.nodeValNat (bitsOf k glo ghi u) (2 * k + j) = (bitsOf k glo ghi u) ⟨2 * k + j, by linarith⟩ := by
      have h_preserve : ∀ (i : ℕ), i < 3 * k + 3 → (cmp1 k hk).C.nodeValNat (bitsOf k glo ghi u) i = (baseSt (by omega)).C.nodeValNat (bitsOf k glo ghi u) i := by
        convert buildLT_preserves ( by omega : 0 < 3 * k ) ( fun j => 2 * k + j ) ( fun j => j ) k ( baseSt ( by omega ) ) ( bitsOf k glo ghi u ) using 1;
      constructor <;> rw [ h_preserve ];
      · convert nodeValNat_input _ _ _ _ using 1;
      · grind +revert;
      · rw [ nodeValNat_input ];
      · grind;
    simp_all +decide [ bitsOf ];
    grind

/-! ### The full circuit -/

/-- The complete comparator circuit: chain `cmp1`, `cmp2`, then
    `¬(u<glo) ∧ ¬(ghi<u)`. -/
def fullCircuit (k : ℕ) (hk : 1 ≤ k) : Circuit (3*k) ((cmp2 k hk).s + 2 + 1) :=
  let s2 := cmp2 k hk
  let S2 := s2.s
  let gA : Gate (3*k + S2) := Gate.not (clampFin (3*k + S2) (by omega) (cmp1 k hk).ltN)
  let CA := s2.C.snoc gA
  let gB : Gate (3*k + (S2+1)) := Gate.not (clampFin (3*k + (S2+1)) (by omega) s2.ltN)
  let CB := CA.snoc gB
  let gC : Gate (3*k + (S2+2)) := Gate.and (clampFin (3*k + (S2+2)) (by omega) (3*k + S2))
                                           (clampFin (3*k + (S2+2)) (by omega) (3*k + S2 + 1))
  CB.snoc gC

/-
**N1.** The §3 verifier is decided by an explicit `O(k)`-size circuit.
-/
theorem verify_circuit_cheap (k : ℕ) (hk : 1 ≤ k) :
    ∃ s, s ≤ 50 * k + 50 ∧ ∃ C : Circuit (3*k) (s+1),
      ∀ glo ghi u : Fin (2^k),
        C.eval (bitsOf k glo ghi u) = decide ((glo : ℕ) ≤ (u : ℕ) ∧ (u : ℕ) ≤ (ghi : ℕ)) := by
  use (cmp2 k hk).s + 2, by
    rw [ cmp2_s ] ; linarith, fullCircuit k hk, by
    intro glo ghi u;
    unfold fullCircuit Circuit.eval; simp +decide [ snoc_nodeValNat_top, snoc_nodeValNat_lt ] ;
    have := cmp1_ltN_val k hk glo ghi u; have := cmp2_ltN_val k hk glo ghi u; simp_all +decide [ Gate.eval, clampFin_val ] ;
    convert congr_arg₂ ( · && · ) _ _ using 1;
    · convert snoc_nodeValNat_top ( cmp2 k hk |> St.C ) ( Gate.not ( clampFin ( 3 * k + ( cmp2 k hk |> St.s ) ) ( by omega ) ( cmp1 k hk |> St.ltN ) ) ) ( bitsOf k glo ghi u ) using 1;
      · apply snoc_nodeValNat_lt;
        linarith;
      · convert congr_arg ( fun x : Bool => !x ) ‹ ( cmp1 k hk ).ltN < 3 * k + ( cmp1 k hk ).s ∧ ( cmp1 k hk ).C.nodeValNat ( bitsOf k glo ghi u ) ( cmp1 k hk ).ltN = decide ( u < glo ) ›.2 using 1;
        · lia;
        · unfold Gate.eval; simp +decide [ cmp1_s, cmp2_s ] ;
          convert ‹ ( cmp1 k hk ).ltN < 3 * k + ( cmp1 k hk ).s ∧ ( cmp1 k hk ).C.nodeValNat ( bitsOf k glo ghi u ) ( cmp1 k hk ).ltN = decide ( u < glo ) ›.2 using 1;
          convert buildLT_preserves ( by omega : 0 < 3 * k ) ( fun j => k + j ) ( fun j => 2 * k + j ) k ( { ( cmp1 k hk ) with eqN := 3 * k + 1, ltN := 3 * k + 2 } ) ( bitsOf k glo ghi u ) ( cmp1 k hk |> St.ltN ) ( by linarith [ cmp1_s k hk, cmp2_s k hk ] ) using 1;
          unfold cmp2; simp +decide [ cmp1_s, cmp2_s ] ;
          grind +suggestions;
    · convert snoc_nodeValNat_top ( ( cmp2 k hk ).C.snoc ( Gate.not ( clampFin ( 3 * k + ( cmp2 k hk ).s ) ( by omega ) ( cmp1 k hk ).ltN ) ) ) ( Gate.not ( clampFin ( 3 * k + ( ( cmp2 k hk ).s + 1 ) ) ( by omega ) ( cmp2 k hk ).ltN ) ) ( bitsOf k glo ghi u ) using 1;
      · unfold clampFin; simp +decide [ Nat.add_assoc ] ;
      · unfold Gate.eval; simp +decide [ clampFin ] ;
        split_ifs <;> simp_all +decide [ snoc_nodeValNat_lt, snoc_nodeValNat_top ];
        · grind;
        · grind;
        · grind;
        · grind +extAll

end PnpProof
