/-
prove2.me platform library module `Definitions.Def_CookLevin_Cost`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_CookLevin_Cost.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_CookLevin_Basic
set_option autoImplicit true
abbrev TapeIdx := Nat
/-
  CookLevinLean/Cost.lean

  The cost model.

  Time is measured as the number of `exe` steps taken by the step-indexed
  interpreter `execute` of `CookLevinLean.Basic`: running `M` for `t` steps
  means evaluating `execute M cfg t`.  This is the cost model of Frank J.
  Balbach's Isabelle/AFP entry *The Cook-Levin Theorem*, of which this library
  is a translation, so "polynomial time" here has a fixed, citable meaning.

  Every complexity notion in this development (`IsPolyTimeComputable`,
  `IsNPVerifier`, `InNP`, `PolyReducible`) is defined in terms of this step
  count.  In particular **no** definition in this file bounds only the length
  of an output or of a witness.
-/


namespace CookLevin

/-! ## Accessing a configuration tape-by-tape -/

/-- The tape used for out-of-range tape indices: all blanks, head at `0`. -/
def defaultTape : Tape := (fun _ => blankSymbol, 0)

/-- Tape `j` of a configuration (all blanks when `j` is out of range). -/
def tapeAt (cfg : Config) (j : TapeIdx) : Tape := cfg.2.getD j defaultTape

/-- The contents of tape `j` of a configuration. -/
def tapeFun (cfg : Config) (j : TapeIdx) : Nat → Symbol := (tapeAt cfg j).1

/-- The head position on tape `j` of a configuration. -/
def headPos (cfg : Config) (j : TapeIdx) : Nat := (tapeAt cfg j).2

theorem tapeFun_eq (cfg : Config) (j : TapeIdx) : tapeFun cfg j = (tapeAt cfg j).1 := rfl

theorem headPos_eq (cfg : Config) (j : TapeIdx) : headPos cfg j = (tapeAt cfg j).2 := rfl

/-- The symbol currently under the head of tape `j`. -/
def scanned (cfg : Config) (j : TapeIdx) : Symbol :=
  tapeFun cfg j (headPos cfg j)

/-! ## Bit strings on tapes -/

/-- A bit as a tape symbol. -/
def boolSym (b : Bool) : Symbol := if b then oneSymbol else zeroSymbol

/-- A bit string as a list of tape symbols. -/
def boolsToSymbols (x : List Bool) : List Symbol := x.map boolSym

@[simp] theorem length_boolsToSymbols (x : List Bool) :
    (boolsToSymbols x).length = x.length := by
  simp [boolsToSymbols]

theorem boolSym_lt_four (b : Bool) : boolSym b < 4 := by
  cases b <;> decide

theorem boolsToSymbols_lt {x : List Bool} {s : Symbol} (h : s ∈ boolsToSymbols x) :
    s < 4 := by
  simp only [boolsToSymbols, List.mem_map] at h
  obtain ⟨b, _, rfl⟩ := h
  exact boolSym_lt_four b

/-! ## Start configurations with an input and a witness

The reduction of the Cook-Levin theorem needs a machine whose input is split
into a *fixed* part (the instance `x`) and a *free* part (the certificate
`w`).  Keeping them on two separate tapes means the tableau can pin down the
cells of tape `0` at time `0` and leave the cells of tape `1` unconstrained,
which is exactly what the reduction requires. -/

/-- Start configuration of a `k`-tape machine with `xs` on tape `0`, `ws` on
tape `1` and blanks everywhere else.  All heads are at cell `0`. -/
def startConfig2 (k : Nat) (xs ws : List Symbol) : Config :=
  (0, (contents xs, 0) :: (contents ws, 0) :: List.replicate (k - 2) (contents [], 0))

@[simp] theorem startConfig2_fst (k : Nat) (xs ws : List Symbol) :
    (startConfig2 k xs ws).1 = 0 := rfl

theorem startConfig2_length {k : Nat} (hk : 2 ≤ k) (xs ws : List Symbol) :
    (startConfig2 k xs ws).2.length = k := by
  simp [startConfig2]
  omega

/-! ## Time-bounded acceptance

A machine *accepts* when it reaches its halting state (`M.length`) **and** has
written `𝟭` in cell `1` of its last tape; it *rejects* when it halts with `𝟬`
there.  Without such an output convention every halting computation would
count as accepting and verifiers could not reject anything. -/

/-- The verdict tape of a `k`-tape machine is its last tape. -/
def verdictTape (k : Nat) : TapeIdx := k - 1

/-- `M` halts within `t` steps on `(xs, ws)` and its verdict is `b`. -/
def DecidesIn (M : Machine) (k : Nat) (xs ws : List Symbol) (t : Nat) (b : Bool) : Prop :=
  (execute M (startConfig2 k xs ws) t).1 = M.length ∧
  tapeFun (execute M (startConfig2 k xs ws) t) (verdictTape k) 1 = boolSym b

/-- `M` accepts `(xs, ws)` within `t` steps. -/
def AcceptsIn (M : Machine) (k : Nat) (xs ws : List Symbol) (t : Nat) : Prop :=
  DecidesIn M k xs ws t true

/-! ## Polynomial bounds -/

/-- The polynomial `n ↦ c * (n+1)^d`.  Using `n+1` rather than `n` keeps the
bound non-trivial on the empty input. -/
def polyBound (c d n : Nat) : Nat := c * (n + 1) ^ d

theorem polyBound_mono {c d : Nat} {m n : Nat} (h : m ≤ n) :
    polyBound c d m ≤ polyBound c d n := by
  unfold polyBound
  exact Nat.mul_le_mul_left c (Nat.pow_le_pow_left (Nat.succ_le_succ h) d)

/-! ## Reading a bit string off a tape -/

/-- Decode a tape symbol as a bit, if it is one. -/
def symBool? (s : Symbol) : Option Bool :=
  if s = oneSymbol then some true
  else if s = zeroSymbol then some false
  else none

@[simp] theorem symBool?_boolSym (b : Bool) : symBool? (boolSym b) = some b := by
  cases b <;> rfl

/-- Read bits from a tape starting at cell `i`, stopping at the first cell that
does not hold a bit.  `fuel` bounds the number of cells inspected. -/
def readBits : Nat → (Nat → Symbol) → Nat → List Bool
  | 0, _, _ => []
  | fuel + 1, tape, i =>
    match symBool? (tape i) with
    | none => []
    | some b => b :: readBits fuel tape (i + 1)

/-- The output of a halted configuration: the bit string starting in cell `1`
of the last tape.  (Cell `0` always holds the start symbol `▷`.) -/
def outputOf (k : Nat) (cfg : Config) (fuel : Nat) : List Bool :=
  readBits fuel (tapeFun cfg (verdictTape k)) 1

/-! ## Time-bounded computation of a function -/

/-- `M`, a `k`-tape machine, computes `f` in at most `T n` steps on inputs of
length `n`: after exactly `T n` steps it is in its halting state and its last
tape holds `f x`.

Evaluating at exactly `T n` steps rather than "at some `t ≤ T n`" is harmless:
`execute_of_halting` says a halted configuration is a fixed point of `exe`. -/
def ComputesInTime (M : Machine) (k : Nat) (T : Nat → Nat)
    (f : List Bool → List Bool) : Prop :=
  ∀ x : List Bool,
    (execute M (startConfig2 k (boolsToSymbols x) []) (T x.length)).1 = M.length ∧
    outputOf k (execute M (startConfig2 k (boolsToSymbols x) []) (T x.length))
      (T x.length + 2) = f x

/-! ## The step semantics, one tape at a time

`sem` is defined by zipping a list of actions against a list of tapes; both the
tableau and the machine-construction files need to talk about one tape at a
time. -/

/-- The action that `cmd` performs on tape `j` in configuration `cfg`. -/
def actAt (cmd : Command) (cfg : Config) (j : TapeIdx) : Action :=
  (cmd (read cfg.2)).2.getD j (blankSymbol, Direction.Stay)

/-- Where a head at cell `p` ends up after moving in direction `d`. -/
def movePos (d : Direction) (p : Nat) : Nat :=
  match d with
  | .Left => p - 1
  | .Stay => p
  | .Right => p + 1

@[simp] theorem act_fst (a : Action) (tp : Tape) (i : Nat) :
    (act a tp).1 i = if i = tp.2 then a.1 else tp.1 i := rfl

@[simp] theorem act_snd (a : Action) (tp : Tape) :
    (act a tp).2 = movePos a.2 tp.2 := by
  cases a with
  | mk s d => cases d <;> rfl

/-- Indexing into a zipped-then-mapped list. -/
theorem getElem?_zip_map {α β γ : Type} (f : α × β → γ) (as : List α) (bs : List β) (i : Nat) :
    ((as.zip bs).map f)[i]? = (as[i]?).bind fun a => (bs[i]?).map fun b => f (a, b) := by
  induction as generalizing bs i with
  | nil => simp
  | cons a as ih =>
    cases bs with
    | nil => simp
    | cons b bs =>
      cases i with
      | zero => simp
      | succ i => simpa using ih bs i

theorem tapeAt_sem (cmd : Command) (cfg : Config) {k j : Nat}
    (hlen : cfg.2.length = k) (hact : (cmd (read cfg.2)).2.length = k) (hj : j < k) :
    tapeAt (sem cmd cfg) j = act (actAt cmd cfg j) (tapeAt cfg j) := by
  have h1 : (cmd (read cfg.2)).2[j]? = some ((cmd (read cfg.2)).2[j]'(by omega)) :=
    List.getElem?_eq_getElem _
  have h2 : cfg.2[j]? = some (cfg.2[j]'(by omega)) := List.getElem?_eq_getElem _
  unfold tapeAt actAt sem
  simp only [List.getD_eq_getElem?_getD]
  rw [getElem?_zip_map, h1, h2]
  simp [List.getD_eq_getElem?_getD, h1, h2]

theorem sem_fst (cmd : Command) (cfg : Config) :
    (sem cmd cfg).1 = (cmd (read cfg.2)).1 := rfl

theorem length_sem (cmd : Command) (cfg : Config) {k : Nat}
    (hlen : cfg.2.length = k) (hact : (cmd (read cfg.2)).2.length = k) :
    (sem cmd cfg).2.length = k := by
  unfold sem
  simp [hlen, hact]

theorem getD_of_lt {α : Type} (l : List α) (d : α) {i : Nat} (h : i < l.length) :
    l.getD i d = l[i] := by
  rw [List.getD_eq_getElem?_getD, List.getElem?_eq_getElem h]
  rfl

/-- The symbol read at the head of tape `j`.  Out-of-range tape indices give
the blank symbol on both sides, so no hypothesis is needed. -/
theorem read_getD (cfg : Config) (j : TapeIdx) :
    (read cfg.2).getD j blankSymbol = scanned cfg j := by
  unfold read scanned tapeFun headPos tapeAt
  simp only [List.getD_eq_getElem?_getD, List.getElem?_map]
  cases h : cfg.2[j]? <;> simp [h, defaultTape]

theorem length_read' (cfg : Config) : (read cfg.2).length = cfg.2.length :=
  read_length _

/-- The symbols under the heads, written as a map over `List.range k`.  This is
the form the transition clauses enumerate over. -/
def readList (cfg : Config) (k : Nat) : List Symbol :=
  (List.range k).map (scanned cfg)

@[simp] theorem length_readList (cfg : Config) (k : Nat) : (readList cfg k).length = k := by
  simp [readList]

theorem readList_getD (cfg : Config) {k j : Nat} (hj : j < k) :
    (readList cfg k).getD j blankSymbol = scanned cfg j := by
  rw [getD_of_lt _ _ (by simp [hj])]
  simp [readList]

theorem read_eq_readList (cfg : Config) {k : Nat} (hlen : cfg.2.length = k) :
    read cfg.2 = readList cfg k := by
  refine List.ext_getElem (by rw [length_read', hlen, length_readList]) ?_
  intro i h1 h2
  have hik : i < k := by simpa using h2
  rw [← getD_of_lt (read cfg.2) blankSymbol h1, ← getD_of_lt (readList cfg k) blankSymbol h2,
    read_getD, readList_getD cfg hik]

theorem mem_read_lt {cfg : Config} {G : Nat}
    (h : ∀ j, j < cfg.2.length → ∀ p, tapeFun cfg j p < G) {s : Symbol}
    (hs : s ∈ read cfg.2) : s < G := by
  unfold read at hs
  simp only [List.mem_map] at hs
  obtain ⟨tp, htp, rfl⟩ := hs
  obtain ⟨j, hj, rfl⟩ := List.mem_iff_getElem.mp htp
  have : tapeAt cfg j = cfg.2[j] := getD_of_lt _ _ hj
  have hval := h j hj (cfg.2[j]).2
  rw [tapeFun_eq, this] at hval
  exact hval


/-- Once halted, running longer changes nothing. -/
theorem execute_of_halted_le {M : Machine} {cfg : Config} {t T : Nat}
    (h : (execute M cfg t).1 = M.length) (hle : t ≤ T) :
    execute M cfg T = execute M cfg t := by
  have hT : T = t + (T - t) := by omega
  rw [hT, execute_add]
  exact execute_of_halting (Nat.le_of_eq h.symm) _

end CookLevin
