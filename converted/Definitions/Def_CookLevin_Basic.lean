/-
prove2.me platform library module `Definitions.Def_CookLevin_Basic`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_CookLevin_Basic.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

/-
  CookLevinLean/Basic.lean

  Foundational definitions of multi-tape Turing machines, translated from
  the Isabelle/HOL theory `Basics.thy` of the Cook–Levin formalization.
-/

namespace CookLevin

/-! ## Directions, states and symbols -/

/-- The direction a tape head can move after writing a symbol. -/
inductive Direction
  | Left
  | Stay
  | Right
  deriving DecidableEq, Repr, Inhabited

/-- States are natural numbers. -/
abbrev State := Nat

/-- Tape symbols are natural numbers. -/
abbrev Symbol := Nat

/-- The blank symbol `□`. -/
abbrev blankSymbol : Symbol := 0

/-- The start symbol `▷`. -/
abbrev startSymbol : Symbol := 1

/-- The symbol `𝟬` representing the bit zero. -/
abbrev zeroSymbol : Symbol := 2

/-- The symbol `𝟭` representing the bit one. -/
abbrev oneSymbol : Symbol := 3

/-! ## Tapes, actions, commands, machines, configurations -/

/-- A tape is a (total) content function together with a head position. -/
abbrev Tape := (Nat → Symbol) × Nat

/-- An action writes a symbol and moves the head in some direction. -/
abbrev Action := Symbol × Direction

/-- A command maps the symbols under the heads to a new state and a list of
actions, one per tape. -/
abbrev Command := List Symbol → State × List Action

/-- A machine is a list of commands, the `q`-th command being executed in
state `q`.  The halting state is `M.length`. -/
abbrev Machine := List Command

/-- A configuration is a state together with the list of tapes. -/
abbrev Config := State × List Tape

/-! ## Well-formedness -/

/-- A command is well-formed for `k` tapes and states `≤ Q` if, on every
input of length `k`, it produces `k` actions and a state at most `Q`. -/
def WfCommand (k Q : Nat) (cmd : Command) : Prop :=
  ∀ gs : List Symbol, gs.length = k → (cmd gs).2.length = k ∧ (cmd gs).1 ≤ Q

/-- A Turing command for `k` tapes, states `≤ Q`, and alphabet size `G`:
well-formed, respects the alphabet, and never writes on the input tape. -/
def TuringCommand (k Q G : Nat) (cmd : Command) : Prop :=
  WfCommand k Q cmd ∧
  ∀ gs : List Symbol, gs.length = k →
    ((∀ i, i < k → gs[i]! < G) → (∀ i, i < k → ((cmd gs).2[i]!).1 < G)) ∧
    (0 < k → ((cmd gs).2[0]!).1 = gs[0]!)

/-- A Turing machine with `k` tapes over an alphabet of size `G`. -/
def TuringMachine (k G : Nat) (M : Machine) : Prop :=
  2 ≤ k ∧ 4 ≤ G ∧ ∀ cmd ∈ M, TuringCommand k M.length G cmd

/-! ## Semantics -/

/-- Perform one action on a tape: write the symbol at the head position and
move the head. Moving left from position `0` stays at `0` (truncated
subtraction). -/
def act (a : Action) (tp : Tape) : Tape :=
  ((fun i => if i = tp.2 then a.1 else tp.1 i),
   match a.2 with
   | .Left  => tp.2 - 1
   | .Stay  => tp.2
   | .Right => tp.2 + 1)

/-- Read the symbols under all tape heads. -/
def read (tps : List Tape) : List Symbol :=
  tps.map fun tp => tp.1 tp.2

/-- Semantics of a single command applied to a configuration. -/
def sem (cmd : Command) (cfg : Config) : Config :=
  let (newstate, actions) := cmd (read cfg.2)
  (newstate, (actions.zip cfg.2).map fun p => act p.1 p.2)

/-- One step of the machine: execute the command of the current state, or do
nothing if the machine is in the halting state (or beyond). -/
def exe (M : Machine) (cfg : Config) : Config :=
  if h : cfg.1 < M.length then sem (M[cfg.1]'h) cfg else cfg

/-- Run the machine for `t` steps. -/
def execute (M : Machine) (cfg : Config) : Nat → Config
  | 0     => cfg
  | t + 1 => exe M (execute M cfg t)

/-- `cfg1` reaches `cfg2` within at most `t` steps. -/
def Transits (M : Machine) (cfg1 : Config) (t : Nat) (cfg2 : Config) : Prop :=
  ∃ t' ≤ t, execute M cfg1 t' = cfg2

/-- Starting in state `0` on tapes `tps`, the machine halts (state
`M.length`) with tapes `tps'` within `t` steps. -/
def Transforms (M : Machine) (tps : List Tape) (t : Nat) (tps' : List Tape) : Prop :=
  Transits M (0, tps) t (M.length, tps')

/-! ## Initial configurations -/

/-- Tape contents for an input string: start symbol at cell `0`, then the
symbols of `xs`, then blanks. -/
def contents (xs : List Symbol) : Nat → Symbol := fun i =>
  if i = 0 then startSymbol
  else if i ≤ xs.length then xs[i - 1]!
  else blankSymbol

/-- The start configuration of a `k`-tape machine on input `xs`: state `0`,
the input on the first tape, and `k - 1` empty tapes, all heads at `0`. -/
def startConfig (k : Nat) (xs : List Symbol) : Config :=
  (0, (contents xs, 0) :: List.replicate (k - 1) (contents [], 0))

/-! ## Basic lemmas -/

@[simp] theorem execute_zero (M : Machine) (cfg : Config) :
    execute M cfg 0 = cfg := rfl

@[simp] theorem execute_succ (M : Machine) (cfg : Config) (t : Nat) :
    execute M cfg (t + 1) = exe M (execute M cfg t) := rfl

theorem execute_add (M : Machine) (cfg : Config) (s t : Nat) :
    execute M cfg (s + t) = execute M (execute M cfg s) t := by
  induction t with
  | zero => rfl
  | succ t ih =>
    show exe M (execute M cfg (s + t)) = exe M (execute M (execute M cfg s) t)
    rw [ih]

@[simp] theorem read_length (tps : List Tape) : (read tps).length = tps.length := by
  simp [read]

theorem exe_of_halting {M : Machine} {cfg : Config} (h : M.length ≤ cfg.1) :
    exe M cfg = cfg := by
  simp [exe, Nat.not_lt.mpr h]

theorem execute_of_halting {M : Machine} {cfg : Config} (h : M.length ≤ cfg.1) (t : Nat) :
    execute M cfg t = cfg := by
  induction t with
  | zero => rfl
  | succ t ih => rw [execute_succ, ih, exe_of_halting h]

/-- Every configuration reaches itself in zero steps. -/
theorem transits_refl (M : Machine) (cfg : Config) (t : Nat) : Transits M cfg t cfg :=
  ⟨0, Nat.zero_le t, rfl⟩

/-- Increasing the time bound preserves `Transits`. -/
theorem transits_mono {M : Machine} {cfg1 cfg2 : Config} {t t' : Nat} (h : t ≤ t')
    (ht : Transits M cfg1 t cfg2) : Transits M cfg1 t' cfg2 := by
  obtain ⟨s, hs, hsE⟩ := ht
  exact ⟨s, Nat.le_trans hs h, hsE⟩

/-- Once the machine halts, it stays halted; hence `Transits` to a halting
configuration is preserved when adding more steps. -/
theorem transits_trans {M : Machine} {cfg1 cfg2 cfg3 : Config} {t t' : Nat}
    (_h1 : Transits M cfg1 t cfg2) (h2 : Transits M cfg2 t' cfg3)
    (hexact : execute M cfg1 t = cfg2) :
    Transits M cfg1 (t + t') cfg3 := by
  obtain ⟨s', hs', hE'⟩ := h2
  refine ⟨t + s', Nat.add_le_add_left hs' t, ?_⟩
  rw [execute_add, hexact, hE']

/-- Increasing the time bound preserves `Transforms`. -/
theorem transforms_mono {M : Machine} {tps tps' : List Tape} {t t' : Nat} (h : t ≤ t')
    (ht : Transforms M tps t tps') : Transforms M tps t' tps' :=
  transits_mono h ht

@[simp] theorem contents_zero (xs : List Symbol) : contents xs 0 = startSymbol := by
  simp [contents]

theorem contents_of_lt (xs : List Symbol) {i : Nat} (h0 : 0 < i) (h : i ≤ xs.length) :
    contents xs i = xs[i - 1]! := by
  have hi : i ≠ 0 := by omega
  simp [contents, hi, h]

theorem contents_of_gt (xs : List Symbol) {i : Nat} (h : xs.length < i) :
    contents xs i = blankSymbol := by
  have hi : i ≠ 0 := by omega
  have hle : ¬(i ≤ xs.length) := by omega
  simp [contents, hi, hle]

/-- The empty input tape is the start symbol followed by blanks. -/
theorem contents_nil (i : Nat) :
    contents [] i = if i = 0 then startSymbol else blankSymbol := by
  by_cases hi : i = 0 <;> simp [contents, hi]

@[simp] theorem startConfig_fst (k : Nat) (xs : List Symbol) :
    (startConfig k xs).1 = 0 := rfl

/-- The start configuration has `k` tapes (for `k ≥ 1`). -/
theorem startConfig_length (k : Nat) (xs : List Symbol) (hk : 1 ≤ k) :
    (startConfig k xs).2.length = k := by
  simp [startConfig]
  omega

/-- All heads are at position `0` in the start configuration. -/
theorem startConfig_heads (k : Nat) (xs : List Symbol) :
    ∀ tp ∈ (startConfig k xs).2, tp.2 = 0 := by
  intro tp htp
  simp [startConfig] at htp
  rcases htp with h | ⟨_, h⟩ <;> subst h <;> rfl

end CookLevin
