/-
prove2.me platform library module `Definitions.Def_CookLevin_Tableau`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_CookLevin_Tableau.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_CookLevin_Complexity
set_option autoImplicit true
/-
  CookLevinLean/Tableau.lean

  The tableau CNF of the Cook-Levin theorem.

  The tape-by-tape step semantics this file runs on live in
  `CookLevinLean.Cost`, so that the machine-construction files can use them too.

  Part B establishes the invariants a tableau of width `T` relies on: after
  `t ≤ T` steps the number of tapes is unchanged, every head is at a cell
  `≤ t`, the state is `≤ M.length`, and every tape cell holds a symbol `< G`.

  Part C indexes the propositional variables; Part D builds the clauses; Part
  E proves `Satisfiable (tableauCNF ...) ↔ AcceptsIn ...` in both directions.
-/


namespace CookLevin

/-! # Part B. Invariants of a `T`-step computation -/

/-- What the tableau construction needs of a machine.  Derived below from the
`TuringMachine` predicate of `CookLevinLean.Basic`. -/
structure WellFormed (k G : Nat) (M : Machine) : Prop where
  /-- At least an input and an output tape. -/
  two_le : 2 ≤ k
  /-- The alphabet contains `□`, `▷`, `𝟬`, `𝟭`. -/
  four_le : 4 ≤ G
  /-- Every command produces one action per tape. -/
  actLen : ∀ cmd ∈ M, ∀ gs : List Symbol, gs.length = k → (cmd gs).2.length = k
  /-- Every command lands in a state of `M` or in the halting state. -/
  stateLe : ∀ cmd ∈ M, ∀ gs : List Symbol, gs.length = k → (cmd gs).1 ≤ M.length
  /-- Every command writes symbols of the alphabet. -/
  symLt : ∀ cmd ∈ M, ∀ gs : List Symbol, gs.length = k → (∀ s ∈ gs, s < G) →
    ∀ j, j < k → ((cmd gs).2.getD j (blankSymbol, Direction.Stay)).1 < G

theorem TuringMachine.wellFormed {k G : Nat} {M : Machine} (h : TuringMachine k G M) :
    WellFormed k G M := by
  obtain ⟨hk, hG, hcmd⟩ := h
  refine ⟨hk, hG, ?_, ?_, ?_⟩
  · intro cmd hc gs hgs; exact ((hcmd cmd hc).1 gs hgs).1
  · intro cmd hc gs hgs; exact ((hcmd cmd hc).1 gs hgs).2
  · intro cmd hc gs hgs hsym j hj
    have hlen : (cmd gs).2.length = k := ((hcmd cmd hc).1 gs hgs).1
    have hpre : ∀ i, i < k → gs[i]! < G := by
      intro i hi
      rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      exact hsym _ (List.getElem_mem _)
    have hpost := ((hcmd cmd hc).2 gs hgs).1 hpre j hj
    rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)] at hpost
    rwa [getD_of_lt _ _ (by omega)]

/-- The invariants that a tableau of width `T` relies on: after `t` steps the
tape count is unchanged, every head is within reach of its start cell, the
state is a state of `M` or the halting state, and every cell holds a symbol of
the alphabet. -/
structure Regular (k G Q t : Nat) (cfg : Config) : Prop where
  /-- The number of tapes never changes. -/
  len : cfg.2.length = k
  /-- The state is at most the halting state. -/
  st : cfg.1 ≤ Q
  /-- A head moves at most one cell per step, from cell `0`. -/
  hd : ∀ j, j < k → headPos cfg j ≤ t
  /-- Every cell holds a symbol of the alphabet. -/
  sym : ∀ j, j < k → ∀ p, tapeFun cfg j p < G

theorem Regular.mono {k G Q t t' : Nat} {cfg : Config} (h : Regular k G Q t cfg)
    (ht : t ≤ t') : Regular k G Q t' cfg :=
  ⟨h.len, h.st, fun j hj => Nat.le_trans (h.hd j hj) ht, h.sym⟩

theorem Regular.step {k G Q t : Nat} {M : Machine} (hM : WellFormed k G M)
    (hQ : M.length = Q) {cfg : Config} (h : Regular k G Q t cfg) :
    Regular k G Q (t + 1) (exe M cfg) := by
  unfold exe
  by_cases hlt : cfg.1 < M.length
  · rw [dif_pos hlt]
    obtain ⟨cmd, hcmd⟩ : ∃ c, M[cfg.1]'hlt = c := ⟨_, rfl⟩
    rw [hcmd]
    have hmem : cmd ∈ M := hcmd ▸ List.getElem_mem hlt
    have hgs : (read cfg.2).length = k := by rw [length_read', h.len]
    have hact : (cmd (read cfg.2)).2.length = k := hM.actLen cmd hmem _ hgs
    have hsymIn : ∀ s ∈ read cfg.2, s < G := by
      intro s hs
      exact mem_read_lt (by rw [h.len]; exact h.sym) hs
    refine ⟨length_sem cmd cfg h.len hact, ?_, ?_, ?_⟩
    · rw [sem_fst, ← hQ]; exact hM.stateLe cmd hmem _ hgs
    · intro j hj
      have hhd : (tapeAt cfg j).2 ≤ t := h.hd j hj
      rw [headPos_eq, tapeAt_sem cmd cfg h.len hact hj, act_snd]
      cases hd : (actAt cmd cfg j).2 <;> simp only [movePos] <;> omega
    · intro j hj p
      rw [tapeFun_eq, tapeAt_sem cmd cfg h.len hact hj, act_fst]
      by_cases hp : p = (tapeAt cfg j).2
      · rw [if_pos hp]
        exact hM.symLt cmd hmem _ hgs hsymIn j hj
      · rw [if_neg hp]
        exact h.sym j hj p
  · rw [dif_neg hlt]
    exact h.mono (Nat.le_succ t)

theorem regular_execute {k G Q : Nat} {M : Machine} (hM : WellFormed k G M)
    (hQ : M.length = Q) {cfg0 : Config} (h0 : Regular k G Q 0 cfg0) (t : Nat) :
    Regular k G Q t (execute M cfg0 t) := by
  induction t with
  | zero => exact h0
  | succ t ih => exact Regular.step hM hQ ih

/-! # Part C. Indexing the propositional variables

Four families of variables are needed, and they must live in disjoint parts of
`Nat`.  We use a mixed-radix packing with a two-bit tag in the low bits, and
prove injectivity in the form that is actually used later: an explicit decoder
together with round-trip equations.  (The previous version of this file defined
`cellVar`, `stateVar` and `headVar` all as the constant `0`.) -/

/-- `pack b hi lo` is the number with high digits `hi` and low digit `lo < b`. -/
def pack (b hi lo : Nat) : Nat := lo + b * hi

theorem pack_div {b hi lo : Nat} (h : lo < b) : pack b hi lo / b = hi := by
  unfold pack
  rw [Nat.add_mul_div_left _ _ (Nat.lt_of_le_of_lt (Nat.zero_le lo) h), Nat.div_eq_of_lt h]
  omega

theorem pack_mod {b hi lo : Nat} (h : lo < b) : pack b hi lo % b = lo := by
  unfold pack
  rw [Nat.add_mul_mod_self_left, Nat.mod_eq_of_lt h]

/-- The shape of a tableau: `k` tapes, alphabet size `G`, states `0, …, Q`
(with `Q` the halting state), and width `T` (both the number of steps and the
number of tracked cells). -/
structure Shape where
  /-- Number of tapes. -/
  k : Nat
  /-- Alphabet size. -/
  G : Nat
  /-- The halting state; states run over `0, …, Q`. -/
  Q : Nat
  /-- Time bound, and also the highest tracked cell index. -/
  T : Nat

namespace Shape

/-- Radix for cell positions.  Positions `0, …, T` are tracked; `T+1` is
reachable only by the (vacuous) right-move clauses at `t = T`, so the radix is
`T+2`. -/
def P (sh : Shape) : Nat := sh.T + 2

/-- Radix for states: `0, …, Q`. -/
def QQ (sh : Shape) : Nat := sh.Q + 1

theorem P_pos (sh : Shape) : 0 < sh.P := by unfold P; omega
theorem QQ_pos (sh : Shape) : 0 < sh.QQ := by unfold QQ; omega

/-- "At time `t`, cell `p` of tape `j` holds symbol `s`." -/
def cellVar (sh : Shape) (t : Nat) (j : TapeIdx) (p : Nat) (s : Symbol) : Nat :=
  4 * pack sh.G (pack sh.P (pack sh.k t j) p) s

/-- "At time `t`, the head of tape `j` is on cell `p`." -/
def headVar (sh : Shape) (t : Nat) (j : TapeIdx) (p : Nat) : Nat :=
  4 * pack sh.P (pack sh.k t j) p + 1

/-- "At time `t`, the machine is in state `q`." -/
def stateVar (sh : Shape) (t : Nat) (q : State) : Nat :=
  4 * pack sh.QQ t q + 2

/-- "At time `t`, the symbol under the head of tape `j` is `s`." -/
def readVar (sh : Shape) (t : Nat) (j : TapeIdx) (s : Symbol) : Nat :=
  4 * pack sh.G (pack sh.k t j) s + 3

end Shape

/-- What a variable index denotes. -/
inductive VarKind
  | cell (t : Nat) (j : TapeIdx) (p : Nat) (s : Symbol)
  | head (t : Nat) (j : TapeIdx) (p : Nat)
  | state (t : Nat) (q : State)
  | read (t : Nat) (j : TapeIdx) (s : Symbol)
  deriving DecidableEq, Repr

namespace Shape

/-- The decoder witnessing that the four variable families are injective and
pairwise disjoint. -/
def decode (sh : Shape) (n : Nat) : VarKind :=
  let m := n / 4
  match n % 4 with
  | 0 =>
    let s := m % sh.G; let m1 := m / sh.G
    let p := m1 % sh.P; let m2 := m1 / sh.P
    VarKind.cell (m2 / sh.k) (m2 % sh.k) p s
  | 1 =>
    let p := m % sh.P; let m1 := m / sh.P
    VarKind.head (m1 / sh.k) (m1 % sh.k) p
  | 2 =>
    VarKind.state (m / sh.QQ) (m % sh.QQ)
  | _ =>
    let s := m % sh.G; let m1 := m / sh.G
    VarKind.read (m1 / sh.k) (m1 % sh.k) s

@[simp] theorem decode_cellVar (sh : Shape) {t j p s : Nat}
    (hj : j < sh.k) (hp : p < sh.P) (hs : s < sh.G) :
    sh.decode (sh.cellVar t j p s) = VarKind.cell t j p s := by
  have h4 : sh.cellVar t j p s % 4 = 0 := by unfold cellVar; omega
  have hd : sh.cellVar t j p s / 4 = pack sh.G (pack sh.P (pack sh.k t j) p) s := by
    unfold cellVar; omega
  simp only [decode, h4, hd, pack_div hs, pack_mod hs, pack_div hp, pack_mod hp,
    pack_div hj, pack_mod hj]

@[simp] theorem decode_headVar (sh : Shape) {t j p : Nat} (hj : j < sh.k) (hp : p < sh.P) :
    sh.decode (sh.headVar t j p) = VarKind.head t j p := by
  have h4 : sh.headVar t j p % 4 = 1 := by unfold headVar; omega
  have hd : sh.headVar t j p / 4 = pack sh.P (pack sh.k t j) p := by
    unfold headVar; omega
  simp only [decode, h4, hd, pack_div hp, pack_mod hp, pack_div hj, pack_mod hj]

@[simp] theorem decode_stateVar (sh : Shape) {t q : Nat} (hq : q < sh.QQ) :
    sh.decode (sh.stateVar t q) = VarKind.state t q := by
  have h4 : sh.stateVar t q % 4 = 2 := by unfold stateVar; omega
  have hd : sh.stateVar t q / 4 = pack sh.QQ t q := by unfold stateVar; omega
  simp only [decode, h4, hd, pack_div hq, pack_mod hq]

@[simp] theorem decode_readVar (sh : Shape) {t j s : Nat} (hj : j < sh.k) (hs : s < sh.G) :
    sh.decode (sh.readVar t j s) = VarKind.read t j s := by
  have h4 : sh.readVar t j s % 4 = 3 := by unfold readVar; omega
  have hd : sh.readVar t j s / 4 = pack sh.G (pack sh.k t j) s := by
    unfold readVar; omega
  simp only [decode, h4, hd, pack_div hs, pack_mod hs, pack_div hj, pack_mod hj]

end Shape

/-! # Part D. The clauses

All clause groups are built with `List.flatMap` over `List.range`, so that
satisfaction can be reduced group-by-group with `satisfies_flatMap` below
instead of by characterising clause membership. -/

theorem satisfies_flatMap {β : Type} (α : Assignment) (l : List β) (f : β → Formula) :
    Satisfies α (l.flatMap f) ↔ ∀ b ∈ l, Satisfies α (f b) := by
  induction l with
  | nil => simp [Satisfies]
  | cons b l ih =>
    rw [List.flatMap_cons, satisfies_append, ih]
    constructor
    · rintro ⟨h1, h2⟩ c hc
      cases List.mem_cons.mp hc with
      | inl h => exact h ▸ h1
      | inr h => exact h2 _ h
    · intro h
      exact ⟨h b List.mem_cons_self, fun c hc => h c (List.mem_cons_of_mem _ hc)⟩

theorem satisfies_single (α : Assignment) (c : Clause) :
    Satisfies α [c] ↔ satisfiesClause α c = true := by
  simp [Satisfies]

/-! ## Exactly-one constraints -/

/-- `exactlyOneOf l v` says that exactly one of the variables `v b`, `b ∈ l`,
is true: one clause demanding at least one, and a binary clause for each pair
of distinct variables. -/
def exactlyOneOf {β : Type} (l : List β) (v : β → Nat) : Formula :=
  [l.map fun b => Literal.Pos (v b)] ++
  l.flatMap fun a => l.flatMap fun b =>
    if v a = v b then [] else [[Literal.Neg (v a), Literal.Neg (v b)]]

theorem satisfies_exactlyOneOf {β : Type} {α : Assignment} {l : List β} {v : β → Nat}
    {a : β} (ha : a ∈ l) (hva : α (v a) = true)
    (hother : ∀ b ∈ l, v b ≠ v a → α (v b) = false) :
    Satisfies α (exactlyOneOf l v) := by
  unfold exactlyOneOf
  rw [satisfies_append]
  constructor
  · rw [satisfies_single, satisfiesClause_iff]
    exact ⟨Literal.Pos (v a), List.mem_map_of_mem ha, hva⟩
  · rw [satisfies_flatMap]
    intro b hb
    rw [satisfies_flatMap]
    intro c hc
    by_cases hvc : v b = v c
    · simp [hvc, Satisfies]
    · rw [if_neg hvc, satisfies_single, satisfiesClause_iff]
      by_cases hb' : v b = v a
      · refine ⟨Literal.Neg (v c), by simp, ?_⟩
        have : v c ≠ v a := fun h => hvc (hb'.trans h.symm)
        simp [satisfiesLiteral, hother c hc this]
      · exact ⟨Literal.Neg (v b), by simp, by simp [satisfiesLiteral, hother b hb hb']⟩

theorem atMostOne_of_satisfies {β : Type} {α : Assignment} {l : List β} {v : β → Nat}
    (h : Satisfies α (exactlyOneOf l v)) {a b : β} (ha : a ∈ l) (hb : b ∈ l)
    (hne : v a ≠ v b) (hva : α (v a) = true) : α (v b) = false := by
  unfold exactlyOneOf at h
  rw [satisfies_append] at h
  have h2 := (satisfies_flatMap _ _ _).mp h.2 a ha
  have h3 := (satisfies_flatMap _ _ _).mp h2 b hb
  rw [if_neg hne, satisfies_single, satisfiesClause_iff] at h3
  obtain ⟨x, hx, hxt⟩ := h3
  simp only [List.mem_cons, List.mem_singleton, List.not_mem_nil, or_false] at hx
  rcases hx with rfl | rfl
  · simp [satisfiesLiteral, hva] at hxt
  · simpa [satisfiesLiteral] using hxt

/-! ## Symbol tuples

The transition clauses range over *all* symbol tuples the heads could be
reading, and consult `M`'s command on each of them.  Nothing is supplied by
the caller. -/

/-- All lists of length `n` with entries `< G`. -/
def tuples : Nat → Nat → List (List Nat)
  | 0, _ => [[]]
  | n + 1, G => (List.range G).flatMap fun s => (tuples n G).map fun ts => s :: ts

theorem mem_tuples {n G : Nat} {ts : List Nat} :
    ts ∈ tuples n G ↔ ts.length = n ∧ ∀ s ∈ ts, s < G := by
  induction n generalizing ts with
  | zero =>
    simp only [tuples, List.mem_singleton]
    constructor
    · rintro rfl; exact ⟨rfl, by simp⟩
    · rintro ⟨h, -⟩; exact List.length_eq_zero_iff.mp h
  | succ n ih =>
    simp only [tuples, List.mem_flatMap, List.mem_map, List.mem_range]
    constructor
    · rintro ⟨s, hs, us, hus, rfl⟩
      obtain ⟨hlen, hlt⟩ := ih.mp hus
      refine ⟨by simp [hlen], ?_⟩
      intro x hx
      cases List.mem_cons.mp hx with
      | inl h => exact h ▸ hs
      | inr h => exact hlt x h
    · rintro ⟨hlen, hlt⟩
      cases ts with
      | nil => simp at hlen
      | cons s us =>
        refine ⟨s, hlt s List.mem_cons_self, us, ih.mpr ⟨by simpa using hlen, ?_⟩, rfl⟩
        intro x hx
        exact hlt x (List.mem_cons_of_mem _ hx)

/-! ## The clause groups -/

/-- The command used for out-of-range states (never reached). -/
def defaultCommand : Command := fun _ => (0, [])

/-- **Start clauses.**  `init j p` lists the symbols cell `p` of tape `j` is
allowed to hold at time `0`.  A singleton pins the cell; a longer list leaves a
choice, which is how the certificate tape is left free by the reduction. -/
def startClauses (sh : Shape) (init : TapeIdx → Nat → List Symbol) : Formula :=
  [[Literal.Pos (sh.stateVar 0 0)]] ++
  ((List.range sh.k).flatMap fun j => [[Literal.Pos (sh.headVar 0 j 0)]]) ++
  ((List.range sh.k).flatMap fun j =>
    (List.range (sh.T + 1)).flatMap fun p =>
      [(init j p).map fun s => Literal.Pos (sh.cellVar 0 j p s)])

/-- **Exactly one symbol per cell**, at every time, tape and position. -/
def cellClauses (sh : Shape) : Formula :=
  (List.range (sh.T + 1)).flatMap fun t =>
  (List.range sh.k).flatMap fun j =>
  (List.range (sh.T + 1)).flatMap fun p =>
    exactlyOneOf (List.range sh.G) fun s => sh.cellVar t j p s

/-- **Exactly one head position per tape**, at every time. -/
def headClauses (sh : Shape) : Formula :=
  (List.range (sh.T + 1)).flatMap fun t =>
  (List.range sh.k).flatMap fun j =>
    exactlyOneOf (List.range (sh.T + 1)) fun p => sh.headVar t j p

/-- **Exactly one state**, at every time. -/
def stateClauses (sh : Shape) : Formula :=
  (List.range (sh.T + 1)).flatMap fun t =>
    exactlyOneOf (List.range sh.QQ) fun q => sh.stateVar t q

/-- **Exactly one scanned symbol per tape**, at every time. -/
def readClauses (sh : Shape) : Formula :=
  (List.range (sh.T + 1)).flatMap fun t =>
  (List.range sh.k).flatMap fun j =>
    exactlyOneOf (List.range sh.G) fun s => sh.readVar t j s

/-- **Link clauses**: the scanned symbol of a tape is the symbol in the cell
under its head. -/
def linkClauses (sh : Shape) : Formula :=
  (List.range (sh.T + 1)).flatMap fun t =>
  (List.range sh.k).flatMap fun j =>
  (List.range (sh.T + 1)).flatMap fun p =>
  (List.range sh.G).flatMap fun s =>
    [[Literal.Neg (sh.headVar t j p), Literal.Neg (sh.cellVar t j p s),
      Literal.Pos (sh.readVar t j s)]]

/-- The guard "at time `t` the state is `q` and the tapes read `rs`". -/
def guardClause (sh : Shape) (t q : Nat) (rs : List Symbol) : Clause :=
  Literal.Neg (sh.stateVar t q) ::
    (List.range sh.k).map fun j => Literal.Neg (sh.readVar t j (rs.getD j blankSymbol))

/-- The action `M`'s command in state `q` performs on tape `j` when the heads
read `rs`. -/
def cmdAction (M : Machine) (q : Nat) (rs : List Symbol) (j : TapeIdx) : Action :=
  ((M.getD q defaultCommand) rs).2.getD j (blankSymbol, Direction.Stay)

/-- The clauses forcing the effect of `M`'s command in state `q` on the symbol
tuple `rs` at time `t`.  The command is *evaluated*: the next state, the
written symbols and the head movements all come from `M` itself. -/
def transitionStep (sh : Shape) (M : Machine) (t q : Nat) (rs : List Symbol) : Formula :=
  [guardClause sh t q rs ++
    [Literal.Pos (sh.stateVar (t + 1) ((M.getD q defaultCommand) rs).1)]] ++
  ((List.range sh.k).flatMap fun j =>
    (List.range (sh.T + 1)).flatMap fun p =>
      [guardClause sh t q rs ++
         [Literal.Neg (sh.headVar t j p),
          Literal.Pos (sh.headVar (t + 1) j (movePos (cmdAction M q rs j).2 p))],
       guardClause sh t q rs ++
         [Literal.Neg (sh.headVar t j p),
          Literal.Pos (sh.cellVar (t + 1) j p (cmdAction M q rs j).1)]])

/-- **Transition clauses.**  For every time, every state `q` of `M` and every
symbol tuple the heads could be reading, the clauses of `transitionStep`.
Nothing here is supplied by the caller: the clauses are read off `M`'s own
step function. -/
def transitionClauses (sh : Shape) (M : Machine) : Formula :=
  (List.range sh.T).flatMap fun t =>
  (List.range M.length).flatMap fun q =>
  (tuples sh.k sh.G).flatMap fun rs => transitionStep sh M t q rs

/-- **Inertia clauses**: a cell that is not under a head keeps its symbol. -/
def inertiaClauses (sh : Shape) : Formula :=
  (List.range sh.T).flatMap fun t =>
  (List.range sh.k).flatMap fun j =>
  (List.range (sh.T + 1)).flatMap fun p =>
  (List.range sh.G).flatMap fun s =>
    [[Literal.Pos (sh.headVar t j p), Literal.Neg (sh.cellVar t j p s),
      Literal.Pos (sh.cellVar (t + 1) j p s)]]

/-- **Halting clauses**: in the halting state nothing changes any more. -/
def haltClauses (sh : Shape) : Formula :=
  (List.range sh.T).flatMap fun t =>
    [[Literal.Neg (sh.stateVar t sh.Q), Literal.Pos (sh.stateVar (t + 1) sh.Q)]] ++
    ((List.range sh.k).flatMap fun j =>
      (List.range (sh.T + 1)).flatMap fun p =>
        [[Literal.Neg (sh.stateVar t sh.Q), Literal.Neg (sh.headVar t j p),
          Literal.Pos (sh.headVar (t + 1) j p)]] ++
        ((List.range sh.G).flatMap fun s =>
          [[Literal.Neg (sh.stateVar t sh.Q), Literal.Neg (sh.cellVar t j p s),
            Literal.Pos (sh.cellVar (t + 1) j p s)]]))

/-- **Acceptance clauses**: at time `T` the machine has halted and cell `1` of
its verdict tape holds `𝟭`. -/
def acceptClauses (sh : Shape) : Formula :=
  [[Literal.Pos (sh.stateVar sh.T sh.Q)],
   [Literal.Pos (sh.cellVar sh.T (verdictTape sh.k) 1 (boolSym true))]]

/-- The tableau CNF of `M` for the start condition `init`. -/
def tableauCNF (sh : Shape) (M : Machine) (init : TapeIdx → Nat → List Symbol) : Formula :=
  startClauses sh init ++ cellClauses sh ++ headClauses sh ++ stateClauses sh ++
    readClauses sh ++ linkClauses sh ++ transitionClauses sh M ++ inertiaClauses sh ++
    haltClauses sh ++ acceptClauses sh

/-! # Part E. Correctness of the tableau -/

namespace Shape

/-! ## Injectivity, in the form the proofs use -/

theorem cellVar_ne (sh : Shape) {t j p s s' : Nat} (hj : j < sh.k) (hp : p < sh.P)
    (hs : s < sh.G) (hs' : s' < sh.G) (h : s ≠ s') :
    sh.cellVar t j p s ≠ sh.cellVar t j p s' := by
  intro heq
  apply h
  have := congrArg sh.decode heq
  rw [decode_cellVar sh hj hp hs, decode_cellVar sh hj hp hs'] at this
  injection this

theorem headVar_ne (sh : Shape) {t j p p' : Nat} (hj : j < sh.k) (hp : p < sh.P)
    (hp' : p' < sh.P) (h : p ≠ p') : sh.headVar t j p ≠ sh.headVar t j p' := by
  intro heq
  apply h
  have := congrArg sh.decode heq
  rw [decode_headVar sh hj hp, decode_headVar sh hj hp'] at this
  injection this

theorem stateVar_ne (sh : Shape) {t q q' : Nat} (hq : q < sh.QQ) (hq' : q' < sh.QQ)
    (h : q ≠ q') : sh.stateVar t q ≠ sh.stateVar t q' := by
  intro heq
  apply h
  have := congrArg sh.decode heq
  rw [decode_stateVar sh hq, decode_stateVar sh hq'] at this
  injection this

theorem readVar_ne (sh : Shape) {t j s s' : Nat} (hj : j < sh.k) (hs : s < sh.G)
    (hs' : s' < sh.G) (h : s ≠ s') : sh.readVar t j s ≠ sh.readVar t j s' := by
  intro heq
  apply h
  have := congrArg sh.decode heq
  rw [decode_readVar sh hj hs, decode_readVar sh hj hs'] at this
  injection this

end Shape

/-! ## The assignment encoding a run -/

/-- The assignment that reads off a run of the machine. -/
def runAssign (sh : Shape) (run : Nat → Config) : Assignment := fun n =>
  match sh.decode n with
  | .cell t j p s => decide (tapeFun (run t) j p = s)
  | .head t j p => decide (headPos (run t) j = p)
  | .state t q => decide ((run t).1 = q)
  | .read t j s => decide (scanned (run t) j = s)

theorem runAssign_cell (sh : Shape) (run : Nat → Config) {t j p s : Nat}
    (hj : j < sh.k) (hp : p < sh.P) (hs : s < sh.G) :
    runAssign sh run (sh.cellVar t j p s) = decide (tapeFun (run t) j p = s) := by
  unfold runAssign
  rw [sh.decode_cellVar hj hp hs]

theorem runAssign_head (sh : Shape) (run : Nat → Config) {t j p : Nat}
    (hj : j < sh.k) (hp : p < sh.P) :
    runAssign sh run (sh.headVar t j p) = decide (headPos (run t) j = p) := by
  unfold runAssign
  rw [sh.decode_headVar hj hp]

theorem runAssign_state (sh : Shape) (run : Nat → Config) {t q : Nat} (hq : q < sh.QQ) :
    runAssign sh run (sh.stateVar t q) = decide ((run t).1 = q) := by
  unfold runAssign
  rw [sh.decode_stateVar hq]

theorem runAssign_read (sh : Shape) (run : Nat → Config) {t j s : Nat}
    (hj : j < sh.k) (hs : s < sh.G) :
    runAssign sh run (sh.readVar t j s) = decide (scanned (run t) j = s) := by
  unfold runAssign
  rw [sh.decode_readVar hj hs]

/-! ## Clause helpers -/

theorem satisfiesClause_append_of_right {α : Assignment} {c1 c2 : Clause}
    (h : satisfiesClause α c2 = true) : satisfiesClause α (c1 ++ c2) = true := by
  rw [satisfiesClause_iff] at h ⊢
  obtain ⟨x, hx, hxt⟩ := h
  exact ⟨x, List.mem_append_right _ hx, hxt⟩

theorem satisfiesClause_of_mem {α : Assignment} {c : Clause} {x : Literal}
    (hx : x ∈ c) (h : satisfiesLiteral α x = true) : satisfiesClause α c = true := by
  rw [satisfiesClause_iff]
  exact ⟨x, hx, h⟩

theorem satisfiesClause_append_right {α : Assignment} {c1 c2 : Clause}
    (h : satisfiesClause α (c1 ++ c2) = true)
    (hc1 : ∀ x ∈ c1, satisfiesLiteral α x = false) :
    satisfiesClause α c2 = true := by
  rw [satisfiesClause_iff] at h ⊢
  obtain ⟨x, hx, hxt⟩ := h
  cases List.mem_append.mp hx with
  | inl hl => rw [hc1 x hl] at hxt; exact absurd hxt (by simp)
  | inr hr => exact ⟨x, hr, hxt⟩

/-! ## The situation: start configurations and acceptance -/

/-- A start configuration allowed by `init`: `k` tapes, state `0`, every head
on cell `0`, cell `p ≤ T` of tape `j` holding one of the symbols listed by
`init j p`, blanks beyond cell `T`, and only alphabet symbols anywhere.

Cells beyond `T` are pinned to blank so that the configuration is determined by
the tableau: a head starting at cell `0` cannot reach cell `T+1` in `T` steps,
so those cells are invisible to the computation anyway. -/
structure StartOK (sh : Shape) (init : TapeIdx → Nat → List Symbol) (cfg : Config) : Prop where
  /-- The right number of tapes. -/
  len : cfg.2.length = sh.k
  /-- The machine starts in state `0`. -/
  st : cfg.1 = 0
  /-- Every head starts on cell `0`. -/
  hd : ∀ j, j < sh.k → headPos cfg j = 0
  /-- Tracked cells hold a symbol allowed by `init`. -/
  cells : ∀ j, j < sh.k → ∀ p, p ≤ sh.T → tapeFun cfg j p ∈ init j p
  /-- Untracked cells are blank. -/
  blank : ∀ j, j < sh.k → ∀ p, sh.T < p → tapeFun cfg j p = blankSymbol
  /-- Every cell holds an alphabet symbol. -/
  alpha : ∀ j, j < sh.k → ∀ p, tapeFun cfg j p < sh.G

/-- `M` started in `cfg` halts within `T` steps with verdict `𝟭`. -/
def AcceptsCfg (M : Machine) (k : Nat) (cfg : Config) (T : Nat) : Prop :=
  (execute M cfg T).1 = M.length ∧
  tapeFun (execute M cfg T) (verdictTape k) 1 = boolSym true

section Correctness

variable {M : Machine} {sh : Shape} {init : TapeIdx → Nat → List Symbol} {cfg0 : Config}

theorem regular_run (hM : WellFormed sh.k sh.G M) (hQ : M.length = sh.Q)
    (hstart : StartOK sh init cfg0) (t : Nat) :
    Regular sh.k sh.G sh.Q t (execute M cfg0 t) :=
  regular_execute hM hQ
    ⟨hstart.len, by rw [hstart.st]; exact Nat.zero_le _,
      fun j hj => by rw [hstart.hd j hj], hstart.alpha⟩ t

/-! ## Completeness: an accepting run yields a satisfying assignment -/

theorem satisfies_start (hM : WellFormed sh.k sh.G M) (hQ : M.length = sh.Q)
    (hstart : StartOK sh init cfg0) :
    Satisfies (runAssign sh (execute M cfg0)) (startClauses sh init) := by
  have hreg := regular_run hM hQ hstart
  have h0 : execute M cfg0 0 = cfg0 := rfl
  unfold startClauses
  simp only [satisfies_append]
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · rw [satisfies_single]
    refine satisfiesClause_of_mem List.mem_cons_self ?_
    rw [show satisfiesLiteral (runAssign sh (execute M cfg0)) (Literal.Pos (sh.stateVar 0 0))
        = runAssign sh (execute M cfg0) (sh.stateVar 0 0) from rfl,
      runAssign_state sh _ (by unfold Shape.QQ; omega), h0, hstart.st]
    simp
  · rw [satisfies_flatMap]
    intro j hj
    rw [List.mem_range] at hj
    rw [satisfies_single]
    refine satisfiesClause_of_mem List.mem_cons_self ?_
    rw [show satisfiesLiteral (runAssign sh (execute M cfg0)) (Literal.Pos (sh.headVar 0 j 0))
        = runAssign sh (execute M cfg0) (sh.headVar 0 j 0) from rfl,
      runAssign_head sh _ hj (by unfold Shape.P; omega), h0, hstart.hd j hj]
    simp
  · rw [satisfies_flatMap]
    intro j hj
    rw [List.mem_range] at hj
    rw [satisfies_flatMap]
    intro p hp
    rw [List.mem_range] at hp
    have hpT : p ≤ sh.T := by omega
    rw [satisfies_single]
    refine satisfiesClause_of_mem
      (List.mem_map_of_mem (hstart.cells j hj p hpT) (f := fun s => Literal.Pos (sh.cellVar 0 j p s))) ?_
    rw [show ∀ v, satisfiesLiteral (runAssign sh (execute M cfg0)) (Literal.Pos v)
        = runAssign sh (execute M cfg0) v from fun _ => rfl,
      runAssign_cell sh _ hj (by unfold Shape.P; omega) (hstart.alpha j hj p), h0]
    simp

theorem satisfies_cellClauses
    (hreg : ∀ t, Regular sh.k sh.G sh.Q t (execute M cfg0 t)) :
    Satisfies (runAssign sh (execute M cfg0)) (cellClauses sh) := by
  unfold cellClauses
  rw [satisfies_flatMap]; intro t ht; rw [List.mem_range] at ht
  rw [satisfies_flatMap]; intro j hj; rw [List.mem_range] at hj
  rw [satisfies_flatMap]; intro p hp; rw [List.mem_range] at hp
  have hpP : p < sh.P := by unfold Shape.P; omega
  have hsym := (hreg t).sym j hj p
  refine satisfies_exactlyOneOf (a := tapeFun (execute M cfg0 t) j p) ?_ ?_ ?_
  · rw [List.mem_range]; exact hsym
  · rw [runAssign_cell sh _ hj hpP hsym]; simp
  · intro s hs hne
    rw [List.mem_range] at hs
    rw [runAssign_cell sh _ hj hpP hs]
    simp only [decide_eq_false_iff_not]
    intro heq
    exact hne (by rw [heq])

theorem satisfies_headClauses
    (hreg : ∀ t, Regular sh.k sh.G sh.Q t (execute M cfg0 t)) :
    Satisfies (runAssign sh (execute M cfg0)) (headClauses sh) := by
  unfold headClauses
  rw [satisfies_flatMap]; intro t ht; rw [List.mem_range] at ht
  rw [satisfies_flatMap]; intro j hj; rw [List.mem_range] at hj
  have hhd : headPos (execute M cfg0 t) j ≤ t := (hreg t).hd j hj
  have hlt : headPos (execute M cfg0 t) j < sh.T + 1 := by omega
  have hP : headPos (execute M cfg0 t) j < sh.P := by unfold Shape.P; omega
  refine satisfies_exactlyOneOf (a := headPos (execute M cfg0 t) j) ?_ ?_ ?_
  · rw [List.mem_range]; exact hlt
  · rw [runAssign_head sh _ hj hP]; simp
  · intro p hp hne
    rw [List.mem_range] at hp
    rw [runAssign_head sh _ hj (by unfold Shape.P; omega)]
    simp only [decide_eq_false_iff_not]
    intro heq
    exact hne (by rw [heq])

theorem satisfies_stateClauses
    (hreg : ∀ t, Regular sh.k sh.G sh.Q t (execute M cfg0 t)) :
    Satisfies (runAssign sh (execute M cfg0)) (stateClauses sh) := by
  unfold stateClauses
  rw [satisfies_flatMap]; intro t ht; rw [List.mem_range] at ht
  have hst : (execute M cfg0 t).1 ≤ sh.Q := (hreg t).st
  have hQQ : (execute M cfg0 t).1 < sh.QQ := Nat.lt_succ_of_le hst
  refine satisfies_exactlyOneOf (a := (execute M cfg0 t).1) ?_ ?_ ?_
  · rw [List.mem_range]; exact hQQ
  · rw [runAssign_state sh _ hQQ]; simp
  · intro q hq hne
    rw [List.mem_range] at hq
    rw [runAssign_state sh _ hq]
    simp only [decide_eq_false_iff_not]
    intro heq
    exact hne (by rw [heq])

theorem satisfies_readClauses
    (hreg : ∀ t, Regular sh.k sh.G sh.Q t (execute M cfg0 t)) :
    Satisfies (runAssign sh (execute M cfg0)) (readClauses sh) := by
  unfold readClauses
  rw [satisfies_flatMap]; intro t ht; rw [List.mem_range] at ht
  rw [satisfies_flatMap]; intro j hj; rw [List.mem_range] at hj
  have hsc : scanned (execute M cfg0 t) j < sh.G :=
    (hreg t).sym j hj (headPos (execute M cfg0 t) j)
  refine satisfies_exactlyOneOf (a := scanned (execute M cfg0 t) j) ?_ ?_ ?_
  · rw [List.mem_range]; exact hsc
  · rw [runAssign_read sh _ hj hsc]; simp
  · intro s hs hne
    rw [List.mem_range] at hs
    rw [runAssign_read sh _ hj hs]
    simp only [decide_eq_false_iff_not]
    intro heq
    exact hne (by rw [heq])

theorem satisfies_linkClauses
    (hreg : ∀ t, Regular sh.k sh.G sh.Q t (execute M cfg0 t)) :
    Satisfies (runAssign sh (execute M cfg0)) (linkClauses sh) := by
  unfold linkClauses
  rw [satisfies_flatMap]; intro t ht; rw [List.mem_range] at ht
  rw [satisfies_flatMap]; intro j hj; rw [List.mem_range] at hj
  rw [satisfies_flatMap]; intro p hp; rw [List.mem_range] at hp
  rw [satisfies_flatMap]; intro s hs; rw [List.mem_range] at hs
  have hpP : p < sh.P := by unfold Shape.P; omega
  rw [satisfies_single]
  by_cases hhd : headPos (execute M cfg0 t) j = p
  · by_cases hcl : tapeFun (execute M cfg0 t) j p = s
    · refine satisfiesClause_of_mem (x := Literal.Pos (sh.readVar t j s)) (by simp) ?_
      show runAssign sh (execute M cfg0) (sh.readVar t j s) = true
      rw [runAssign_read sh _ hj hs]
      simp only [scanned, hhd, hcl, decide_eq_true_eq]
    · refine satisfiesClause_of_mem (x := Literal.Neg (sh.cellVar t j p s)) (by simp) ?_
      show (!runAssign sh (execute M cfg0) (sh.cellVar t j p s)) = true
      rw [runAssign_cell sh _ hj hpP hs]
      simp [hcl]
  · refine satisfiesClause_of_mem (x := Literal.Neg (sh.headVar t j p)) (by simp) ?_
    show (!runAssign sh (execute M cfg0) (sh.headVar t j p)) = true
    rw [runAssign_head sh _ hj hpP]
    simp [hhd]

end Correctness

/-! ## One step of the machine, tape by tape -/

/-- The command executed in configuration `cfg` (the default command when the
machine has halted; that case is never used). -/
def cmdOf (M : Machine) (cfg : Config) : Command := M.getD cfg.1 defaultCommand

/-- The next state and the actions produced in configuration `cfg`. -/
def stepRes (M : Machine) (cfg : Config) : State × List Action := cmdOf M cfg (read cfg.2)

/-- The action performed on tape `j` in configuration `cfg`. -/
def writeOf (M : Machine) (cfg : Config) (j : TapeIdx) : Action :=
  (stepRes M cfg).2.getD j (blankSymbol, Direction.Stay)

theorem cmdOf_eq {M : Machine} {cfg : Config} (hlt : cfg.1 < M.length) :
    cmdOf M cfg = M[cfg.1]'hlt := getD_of_lt _ _ hlt

theorem exe_running {M : Machine} {cfg : Config} (hlt : cfg.1 < M.length) :
    exe M cfg = sem (cmdOf M cfg) cfg := by
  unfold exe
  rw [dif_pos hlt, cmdOf_eq hlt]

theorem exe_fst_running {M : Machine} {cfg : Config} (hlt : cfg.1 < M.length) :
    (exe M cfg).1 = (stepRes M cfg).1 := by
  rw [exe_running hlt, sem_fst]
  rfl

section Step

variable {M : Machine} {k G : Nat} {cfg : Config}

theorem length_stepRes (hM : WellFormed k G M) (hlen : cfg.2.length = k)
    (hlt : cfg.1 < M.length) : (stepRes M cfg).2.length = k := by
  unfold stepRes
  rw [cmdOf_eq hlt]
  exact hM.actLen _ (List.getElem_mem hlt) _ (by rw [length_read', hlen])

theorem tapeAt_exe_running (hM : WellFormed k G M) (hlen : cfg.2.length = k)
    (hlt : cfg.1 < M.length) {j : TapeIdx} (hj : j < k) :
    tapeAt (exe M cfg) j = act (writeOf M cfg j) (tapeAt cfg j) := by
  rw [exe_running hlt]
  exact tapeAt_sem (cmdOf M cfg) cfg hlen (length_stepRes hM hlen hlt) hj

theorem headPos_exe_running (hM : WellFormed k G M) (hlen : cfg.2.length = k)
    (hlt : cfg.1 < M.length) {j : TapeIdx} (hj : j < k) :
    headPos (exe M cfg) j = movePos (writeOf M cfg j).2 (headPos cfg j) := by
  rw [headPos_eq, tapeAt_exe_running hM hlen hlt hj, act_snd, headPos_eq]

theorem tapeFun_exe_running (hM : WellFormed k G M) (hlen : cfg.2.length = k)
    (hlt : cfg.1 < M.length) {j : TapeIdx} (hj : j < k) (p : Nat) :
    tapeFun (exe M cfg) j p =
      if p = headPos cfg j then (writeOf M cfg j).1 else tapeFun cfg j p := by
  rw [tapeFun_eq, tapeAt_exe_running hM hlen hlt hj, act_fst, headPos_eq, tapeFun_eq]

theorem exe_halted {M : Machine} {cfg : Config} (hlt : ¬ cfg.1 < M.length) :
    exe M cfg = cfg := by
  unfold exe
  rw [dif_neg hlt]

end Step

/-- The tuple of scanned symbols is one of the tuples the transition clauses
range over. -/
theorem readList_mem_tuples {cfg : Config} {k G : Nat}
    (hsym : ∀ j, j < k → ∀ p, tapeFun cfg j p < G) :
    readList cfg k ∈ tuples k G := by
  refine mem_tuples.mpr ⟨length_readList cfg k, ?_⟩
  intro s hs
  unfold readList at hs
  simp only [List.mem_map, List.mem_range] at hs
  obtain ⟨j, hj, rfl⟩ := hs
  exact hsym j hj _

/-- A tuple that agrees with the scanned symbols *is* the list of scanned
symbols. -/
theorem eq_read_of_getD {cfg : Config} {k : Nat} {rs : List Symbol}
    (hlen : cfg.2.length = k) (hrs : rs.length = k)
    (h : ∀ j, j < k → rs.getD j blankSymbol = scanned cfg j) :
    rs = read cfg.2 := by
  rw [read_eq_readList cfg hlen]
  refine List.ext_getElem (by rw [hrs, length_readList]) ?_
  intro i h1 h2
  have hik : i < k := by rw [hrs] at h1; exact h1
  rw [← getD_of_lt rs blankSymbol h1, ← getD_of_lt (readList cfg k) blankSymbol h2,
    h i hik, readList_getD cfg hik]

/-- A `Bool`-valued predicate that is not uniformly `false` on a list is `true`
somewhere on it.  (Used instead of `push_neg`, which lives in Mathlib.) -/
theorem exists_of_not_forall_mem {β : Type} {l : List β} {p : β → Bool}
    (h : ¬ ∀ x ∈ l, p x = false) : ∃ x ∈ l, p x = true := by
  induction l with
  | nil => exact absurd (fun x hx => absurd hx (by simp)) h
  | cons a l ih =>
    cases ha : p a with
    | true => exact ⟨a, List.mem_cons_self, ha⟩
    | false =>
      have hnot : ¬ ∀ x ∈ l, p x = false := by
        intro hall
        refine h fun x hx => ?_
        cases List.mem_cons.mp hx with
        | inl he => exact he ▸ ha
        | inr he => exact hall x he
      obtain ⟨x, hx, hxt⟩ := ih hnot
      exact ⟨x, List.mem_cons_of_mem _ hx, hxt⟩

section Correctness2

variable {M : Machine} {sh : Shape} {init : TapeIdx → Nat → List Symbol} {cfg0 : Config}

/-- If no literal of the guard is satisfied, the guard has pinned down the
configuration at time `t`: the state is `q` and the heads read exactly `rs`. -/
theorem guard_falsified (hreg : ∀ t, Regular sh.k sh.G sh.Q t (execute M cfg0 t))
    {t q : Nat} (hqQQ : q < sh.QQ) {rs : List Symbol} (hrs : rs ∈ tuples sh.k sh.G)
    (hg : ∀ x ∈ guardClause sh t q rs,
      satisfiesLiteral (runAssign sh (execute M cfg0)) x = false) :
    (execute M cfg0 t).1 = q ∧ rs = read (execute M cfg0 t).2 := by
  obtain ⟨hrslen, hrslt⟩ := mem_tuples.mp hrs
  have hstl := hg (Literal.Neg (sh.stateVar t q)) List.mem_cons_self
  rw [show satisfiesLiteral (runAssign sh (execute M cfg0)) (Literal.Neg (sh.stateVar t q))
      = !(runAssign sh (execute M cfg0) (sh.stateVar t q)) from rfl,
    runAssign_state sh _ hqQQ] at hstl
  have hst : (execute M cfg0 t).1 = q := by simpa using hstl
  refine ⟨hst, eq_read_of_getD (hreg t).len hrslen ?_⟩
  intro j hj
  have hjr : j < rs.length := by omega
  have hslt : rs.getD j blankSymbol < sh.G := by
    rw [getD_of_lt rs blankSymbol hjr]
    exact hrslt _ (List.getElem_mem _)
  have hmem : Literal.Neg (sh.readVar t j (rs.getD j blankSymbol)) ∈ guardClause sh t q rs :=
    List.mem_cons_of_mem _ (List.mem_map_of_mem (List.mem_range.mpr hj))
  have hrdl := hg _ hmem
  rw [show satisfiesLiteral (runAssign sh (execute M cfg0))
        (Literal.Neg (sh.readVar t j (rs.getD j blankSymbol)))
      = !(runAssign sh (execute M cfg0) (sh.readVar t j (rs.getD j blankSymbol))) from rfl,
    runAssign_read sh _ hj hslt] at hrdl
  have : scanned (execute M cfg0 t) j = rs.getD j blankSymbol := by simpa using hrdl
  exact this.symm

theorem satisfies_transitionClauses (hM : WellFormed sh.k sh.G M) (hQ : M.length = sh.Q)
    (hreg : ∀ t, Regular sh.k sh.G sh.Q t (execute M cfg0 t)) :
    Satisfies (runAssign sh (execute M cfg0)) (transitionClauses sh M) := by
  unfold transitionClauses
  rw [satisfies_flatMap]; intro t ht; rw [List.mem_range] at ht
  rw [satisfies_flatMap]; intro q hq; rw [List.mem_range] at hq
  rw [satisfies_flatMap]; intro rs hrs
  have hqQQ : q < sh.QQ := by unfold Shape.QQ; omega
  by_cases hg : ∀ x ∈ guardClause sh t q rs,
      satisfiesLiteral (runAssign sh (execute M cfg0)) x = false
  · -- the guard holds of the actual configuration: the consequents must be forced
    obtain ⟨hst, hrseq⟩ := guard_falsified hreg hqQQ hrs hg
    have hlt : (execute M cfg0 t).1 < M.length := by rw [hst]; exact hq
    have hcmd : M.getD q defaultCommand = cmdOf M (execute M cfg0 t) := by
      unfold cmdOf; rw [hst]
    have hres : (M.getD q defaultCommand) rs = stepRes M (execute M cfg0 t) := by
      unfold stepRes; rw [hcmd, hrseq]
    have hact : ∀ j, cmdAction M q rs j = writeOf M (execute M cfg0 t) j := by
      intro j; unfold cmdAction writeOf; rw [hres]
    have hnext : execute M cfg0 (t + 1) = exe M (execute M cfg0 t) := rfl
    unfold transitionStep
    simp only [satisfies_append]
    refine ⟨?_, ?_⟩
    · -- the next state
      rw [satisfies_single]
      refine satisfiesClause_append_of_right ?_
      refine satisfiesClause_of_mem List.mem_cons_self ?_
      have hb : ((M.getD q defaultCommand) rs).1 < sh.QQ := by
        have : ((M.getD q defaultCommand) rs).1 = (execute M cfg0 (t + 1)).1 := by
          rw [hres, hnext, exe_fst_running hlt]
        rw [this]
        exact Nat.lt_succ_of_le (hreg (t + 1)).st
      show runAssign sh (execute M cfg0) (sh.stateVar (t + 1) _) = true
      rw [runAssign_state sh _ hb, hres, hnext, exe_fst_running hlt]
      simp
    · rw [satisfies_flatMap]; intro j hj; rw [List.mem_range] at hj
      rw [satisfies_flatMap]; intro p hp; rw [List.mem_range] at hp
      have hpP : p < sh.P := by unfold Shape.P; omega
      have hheadNe : ∀ (c : Clause),
          headPos (execute M cfg0 t) j ≠ p →
          satisfiesClause (runAssign sh (execute M cfg0))
            (guardClause sh t q rs ++ (Literal.Neg (sh.headVar t j p) :: c)) = true := by
        intro c hne
        refine satisfiesClause_append_of_right ?_
        refine satisfiesClause_of_mem List.mem_cons_self ?_
        show (!runAssign sh (execute M cfg0) (sh.headVar t j p)) = true
        rw [runAssign_head sh _ hj hpP]
        simp [hne]
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      by_cases hhd : headPos (execute M cfg0 t) j = p
      · rcases hc with rfl | rfl
        · -- the head moves as `M` says
          refine satisfiesClause_append_of_right ?_
          refine satisfiesClause_of_mem (List.mem_cons_of_mem _ List.mem_cons_self) ?_
          have hmv : movePos (cmdAction M q rs j).2 p < sh.P := by
            rw [hact j]
            cases hd : (writeOf M (execute M cfg0 t) j).2 <;>
              simp only [movePos] <;> unfold Shape.P <;> omega
          show runAssign sh (execute M cfg0) (sh.headVar (t + 1) j _) = true
          rw [runAssign_head sh _ hj hmv, hnext,
            headPos_exe_running hM (hreg t).len hlt hj, hhd, hact j]
          simp
        · -- the cell under the head is overwritten as `M` says
          refine satisfiesClause_append_of_right ?_
          refine satisfiesClause_of_mem (List.mem_cons_of_mem _ List.mem_cons_self) ?_
          have hvalue : tapeFun (execute M cfg0 (t + 1)) j p = (cmdAction M q rs j).1 := by
            rw [hnext, tapeFun_exe_running hM (hreg t).len hlt hj p, hhd, hact j]
            simp
          have hlt' : (cmdAction M q rs j).1 < sh.G := by
            rw [← hvalue]; exact (hreg (t + 1)).sym j hj p
          show runAssign sh (execute M cfg0) (sh.cellVar (t + 1) j p _) = true
          rw [runAssign_cell sh _ hj hpP hlt', hvalue]
          simp
      · rcases hc with rfl | rfl
        · exact hheadNe _ hhd
        · exact hheadNe _ hhd
  · -- some guard literal is satisfied: every clause of this group contains it
    obtain ⟨x, hx, hxt⟩ :=
      exists_of_not_forall_mem (p := fun x => satisfiesLiteral (runAssign sh (execute M cfg0)) x) hg
    unfold transitionStep
    simp only [satisfies_append]
    refine ⟨?_, ?_⟩
    · rw [satisfies_single]
      exact satisfiesClause_of_mem (List.mem_append_left _ hx) hxt
    · rw [satisfies_flatMap]; intro j _
      rw [satisfies_flatMap]; intro p _
      intro c hc
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
      rcases hc with rfl | rfl <;>
        exact satisfiesClause_of_mem (List.mem_append_left _ hx) hxt

/-- A cell that is not under a head keeps its symbol, whether or not the
machine is still running. -/
theorem tapeFun_step_of_ne {M : Machine} {k G : Nat} {cfg : Config}
    (hM : WellFormed k G M) (hlen : cfg.2.length = k) {j : TapeIdx} (hj : j < k)
    {p : Nat} (hne : p ≠ headPos cfg j) :
    tapeFun (exe M cfg) j p = tapeFun cfg j p := by
  by_cases hlt : cfg.1 < M.length
  · rw [tapeFun_exe_running hM hlen hlt hj p, if_neg hne]
  · rw [exe_halted hlt]

theorem satisfies_inertiaClauses (hM : WellFormed sh.k sh.G M)
    (hreg : ∀ t, Regular sh.k sh.G sh.Q t (execute M cfg0 t)) :
    Satisfies (runAssign sh (execute M cfg0)) (inertiaClauses sh) := by
  unfold inertiaClauses
  rw [satisfies_flatMap]; intro t ht; rw [List.mem_range] at ht
  rw [satisfies_flatMap]; intro j hj; rw [List.mem_range] at hj
  rw [satisfies_flatMap]; intro p hp; rw [List.mem_range] at hp
  rw [satisfies_flatMap]; intro s hs; rw [List.mem_range] at hs
  have hpP : p < sh.P := by unfold Shape.P; omega
  rw [satisfies_single]
  by_cases hhd : headPos (execute M cfg0 t) j = p
  · refine satisfiesClause_of_mem List.mem_cons_self ?_
    show runAssign sh (execute M cfg0) (sh.headVar t j p) = true
    rw [runAssign_head sh _ hj hpP]
    simp [hhd]
  · by_cases hcl : tapeFun (execute M cfg0 t) j p = s
    · refine satisfiesClause_of_mem
        (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) ?_
      show runAssign sh (execute M cfg0) (sh.cellVar (t + 1) j p s) = true
      rw [runAssign_cell sh _ hj hpP hs,
        show execute M cfg0 (t + 1) = exe M (execute M cfg0 t) from rfl,
        tapeFun_step_of_ne hM (hreg t).len hj (fun h => hhd h.symm), hcl]
      simp
    · refine satisfiesClause_of_mem (List.mem_cons_of_mem _ List.mem_cons_self) ?_
      show (!runAssign sh (execute M cfg0) (sh.cellVar t j p s)) = true
      rw [runAssign_cell sh _ hj hpP hs]
      simp [hcl]

theorem satisfies_haltClauses (hM : WellFormed sh.k sh.G M) (hQ : M.length = sh.Q)
    (hreg : ∀ t, Regular sh.k sh.G sh.Q t (execute M cfg0 t)) :
    Satisfies (runAssign sh (execute M cfg0)) (haltClauses sh) := by
  have hQQ : sh.Q < sh.QQ := by unfold Shape.QQ; omega
  unfold haltClauses
  rw [satisfies_flatMap]; intro t ht; rw [List.mem_range] at ht
  by_cases hst : (execute M cfg0 t).1 = sh.Q
  · -- the machine has halted: nothing changes
    have hnot : ¬ (execute M cfg0 t).1 < M.length :=
      Nat.not_lt.mpr (Nat.le_of_eq (by rw [hQ, hst]))
    have hfix : execute M cfg0 (t + 1) = execute M cfg0 t := by
      show exe M (execute M cfg0 t) = execute M cfg0 t
      exact exe_halted hnot
    simp only [satisfies_append]
    refine ⟨?_, ?_⟩
    · rw [satisfies_single]
      refine satisfiesClause_of_mem (List.mem_cons_of_mem _ List.mem_cons_self) ?_
      show runAssign sh (execute M cfg0) (sh.stateVar (t + 1) sh.Q) = true
      rw [runAssign_state sh _ hQQ, hfix, hst]
      simp
    · rw [satisfies_flatMap]; intro j hj; rw [List.mem_range] at hj
      rw [satisfies_flatMap]; intro p hp; rw [List.mem_range] at hp
      have hpP : p < sh.P := by unfold Shape.P; omega
      simp only [satisfies_append]
      refine ⟨?_, ?_⟩
      · rw [satisfies_single]
        by_cases hhd : headPos (execute M cfg0 t) j = p
        · refine satisfiesClause_of_mem
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) ?_
          show runAssign sh (execute M cfg0) (sh.headVar (t + 1) j p) = true
          rw [runAssign_head sh _ hj hpP, hfix, hhd]
          simp
        · refine satisfiesClause_of_mem (List.mem_cons_of_mem _ List.mem_cons_self) ?_
          show (!runAssign sh (execute M cfg0) (sh.headVar t j p)) = true
          rw [runAssign_head sh _ hj hpP]
          simp [hhd]
      · rw [satisfies_flatMap]; intro s hs; rw [List.mem_range] at hs
        rw [satisfies_single]
        by_cases hcl : tapeFun (execute M cfg0 t) j p = s
        · refine satisfiesClause_of_mem
            (List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)) ?_
          show runAssign sh (execute M cfg0) (sh.cellVar (t + 1) j p s) = true
          rw [runAssign_cell sh _ hj hpP hs, hfix, hcl]
          simp
        · refine satisfiesClause_of_mem (List.mem_cons_of_mem _ List.mem_cons_self) ?_
          show (!runAssign sh (execute M cfg0) (sh.cellVar t j p s)) = true
          rw [runAssign_cell sh _ hj hpP hs]
          simp [hcl]
  · -- the machine has not halted: every clause of this group is guarded
    have hneg : satisfiesLiteral (runAssign sh (execute M cfg0))
        (Literal.Neg (sh.stateVar t sh.Q)) = true := by
      show (!runAssign sh (execute M cfg0) (sh.stateVar t sh.Q)) = true
      rw [runAssign_state sh _ hQQ]
      simp [hst]
    simp only [satisfies_append]
    refine ⟨?_, ?_⟩
    · rw [satisfies_single]
      exact satisfiesClause_of_mem List.mem_cons_self hneg
    · rw [satisfies_flatMap]; intro j _
      rw [satisfies_flatMap]; intro p _
      simp only [satisfies_append]
      refine ⟨?_, ?_⟩
      · rw [satisfies_single]
        exact satisfiesClause_of_mem List.mem_cons_self hneg
      · rw [satisfies_flatMap]; intro s _
        rw [satisfies_single]
        exact satisfiesClause_of_mem List.mem_cons_self hneg

theorem satisfies_acceptClauses (hM : WellFormed sh.k sh.G M) (hQ : M.length = sh.Q)
    (hreg : ∀ t, Regular sh.k sh.G sh.Q t (execute M cfg0 t))
    (hacc : AcceptsCfg M sh.k cfg0 sh.T) :
    Satisfies (runAssign sh (execute M cfg0)) (acceptClauses sh) := by
  obtain ⟨haccSt, haccOut⟩ := hacc
  have hQQ : sh.Q < sh.QQ := by unfold Shape.QQ; omega
  have hk : verdictTape sh.k < sh.k := by
    have h2 := hM.two_le
    show sh.k - 1 < sh.k
    omega
  have h1P : 1 < sh.P := by unfold Shape.P; omega
  have hG : boolSym true < sh.G := by
    have h4 := hM.four_le
    show 3 < sh.G
    omega
  unfold acceptClauses
  intro c hc
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hc
  rcases hc with rfl | rfl
  · refine satisfiesClause_of_mem List.mem_cons_self ?_
    show runAssign sh (execute M cfg0) (sh.stateVar sh.T sh.Q) = true
    rw [runAssign_state sh _ hQQ, haccSt, hQ]
    simp
  · refine satisfiesClause_of_mem List.mem_cons_self ?_
    show runAssign sh (execute M cfg0) (sh.cellVar sh.T (verdictTape sh.k) 1 (boolSym true)) = true
    rw [runAssign_cell sh _ hk h1P hG, haccOut]
    simp

/-- **Completeness of the reduction.**  An accepting run of `M` from a start
configuration allowed by `init` yields a satisfying assignment of the tableau,
namely the assignment that simply reads the run off. -/
theorem satisfies_tableauCNF (hM : WellFormed sh.k sh.G M) (hQ : M.length = sh.Q)
    (hstart : StartOK sh init cfg0) (hacc : AcceptsCfg M sh.k cfg0 sh.T) :
    Satisfies (runAssign sh (execute M cfg0)) (tableauCNF sh M init) := by
  have hreg := regular_run hM hQ hstart
  unfold tableauCNF
  simp only [satisfies_append]
  exact ⟨⟨⟨⟨⟨⟨⟨⟨⟨satisfies_start hM hQ hstart, satisfies_cellClauses hreg⟩,
      satisfies_headClauses hreg⟩, satisfies_stateClauses hreg⟩,
      satisfies_readClauses hreg⟩, satisfies_linkClauses hreg⟩,
      satisfies_transitionClauses hM hQ hreg⟩, satisfies_inertiaClauses hM hreg⟩,
      satisfies_haltClauses hM hQ hreg⟩, satisfies_acceptClauses hM hQ hreg hacc⟩

end Correctness2

/-! ## Soundness: a satisfying assignment yields an accepting run -/

theorem find?_eq_of_unique {β : Type} {l : List β} {p : β → Bool} {a : β}
    (ha : a ∈ l) (hpa : p a = true) (huniq : ∀ b ∈ l, p b = true → b = a) :
    l.find? p = some a := by
  induction l with
  | nil => cases ha
  | cons x xs ih =>
    cases hx : p x with
    | true =>
      have hxa : x = a := huniq x List.mem_cons_self hx
      rw [List.find?_cons, hx]
      exact congrArg some hxa
    | false =>
      have hane : x ≠ a := by
        intro h
        rw [h, hpa] at hx
        exact absurd hx (by simp)
      have ha' : a ∈ xs := by
        cases List.mem_cons.mp ha with
        | inl h => exact absurd h.symm hane
        | inr h => exact h
      rw [List.find?_cons, hx]
      simp only []
      exact ih ha' fun b hb => huniq b (List.mem_cons_of_mem _ hb)

/-- The symbol that a satisfying assignment puts in cell `p` of tape `j` at
time `t`. -/
def extractCell (sh : Shape) (α : Assignment) (t : Nat) (j : TapeIdx) (p : Nat) : Symbol :=
  ((List.range sh.G).find? fun s => α (sh.cellVar t j p s)).getD blankSymbol

/-- The start configuration that a satisfying assignment describes. -/
def extractStart (sh : Shape) (α : Assignment) : Config :=
  (0, (List.range sh.k).map fun j =>
    ((fun p => if p ≤ sh.T then extractCell sh α 0 j p else blankSymbol), 0))

@[simp] theorem extractStart_fst (sh : Shape) (α : Assignment) :
    (extractStart sh α).1 = 0 := rfl

@[simp] theorem extractStart_length (sh : Shape) (α : Assignment) :
    (extractStart sh α).2.length = sh.k := by simp [extractStart]

theorem tapeAt_extractStart (sh : Shape) (α : Assignment) {j : TapeIdx} (hj : j < sh.k) :
    tapeAt (extractStart sh α) j =
      ((fun p => if p ≤ sh.T then extractCell sh α 0 j p else blankSymbol), 0) := by
  unfold tapeAt
  rw [getD_of_lt _ _ (by simp [hj])]
  simp [extractStart]

theorem headPos_extractStart (sh : Shape) (α : Assignment) {j : TapeIdx} (hj : j < sh.k) :
    headPos (extractStart sh α) j = 0 := by
  rw [headPos_eq, tapeAt_extractStart sh α hj]

theorem tapeFun_extractStart (sh : Shape) (α : Assignment) {j : TapeIdx} (hj : j < sh.k)
    (p : Nat) :
    tapeFun (extractStart sh α) j p =
      if p ≤ sh.T then extractCell sh α 0 j p else blankSymbol := by
  rw [tapeFun_eq, tapeAt_extractStart sh α hj]

section Sound

variable {M : Machine} {sh : Shape} {init : TapeIdx → Nat → List Symbol} {α : Assignment}

/-! ### Projecting the tableau onto its clause groups -/

theorem tableau_groups (h : Satisfies α (tableauCNF sh M init)) :
    Satisfies α (startClauses sh init) ∧ Satisfies α (cellClauses sh) ∧
    Satisfies α (headClauses sh) ∧ Satisfies α (stateClauses sh) ∧
    Satisfies α (readClauses sh) ∧ Satisfies α (linkClauses sh) ∧
    Satisfies α (transitionClauses sh M) ∧ Satisfies α (inertiaClauses sh) ∧
    Satisfies α (haltClauses sh) ∧ Satisfies α (acceptClauses sh) := by
  unfold tableauCNF at h
  simp only [satisfies_append] at h
  exact ⟨h.1.1.1.1.1.1.1.1.1, h.1.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.1.2, h.1.1.1.1.1.1.2,
    h.1.1.1.1.1.2, h.1.1.1.1.2, h.1.1.1.2, h.1.1.2, h.1.2, h.2⟩

/-! ### Reading a cell off the assignment -/

theorem extractCell_eq (hcell : Satisfies α (cellClauses sh)) {t j p s : Nat}
    (ht : t ≤ sh.T) (hj : j < sh.k) (hp : p ≤ sh.T) (hs : s < sh.G)
    (hα : α (sh.cellVar t j p s) = true) : extractCell sh α t j p = s := by
  have hpP : p < sh.P := by unfold Shape.P; omega
  have hone : Satisfies α (exactlyOneOf (List.range sh.G) fun s => sh.cellVar t j p s) := by
    have h1 := (satisfies_flatMap _ _ _).mp hcell t (List.mem_range.mpr (by omega))
    have h2 := (satisfies_flatMap _ _ _).mp h1 j (List.mem_range.mpr hj)
    exact (satisfies_flatMap _ _ _).mp h2 p (List.mem_range.mpr (by omega))
  unfold extractCell
  rw [find?_eq_of_unique (List.mem_range.mpr hs) hα ?_]
  · rfl
  · intro b hb hbt
    rw [List.mem_range] at hb
    by_cases hne : b = s
    · exact hne
    · exfalso
      have hvne : sh.cellVar t j p s ≠ sh.cellVar t j p b :=
        sh.cellVar_ne hj hpP hs hb fun h => hne h.symm
      have hfalse :=
        atMostOne_of_satisfies hone (List.mem_range.mpr hs) (List.mem_range.mpr hb) hvne hα
      rw [hfalse] at hbt
      exact absurd hbt (by simp)

end Sound

/-! ### Small clause helpers -/

theorem satisfiesLiteral_neg_false {α : Assignment} {v : Nat} (h : α v = true) :
    satisfiesLiteral α (Literal.Neg v) = false := by
  show (!α v) = false
  rw [h]; rfl

theorem satisfiesClause_two {α : Assignment} {x y : Literal}
    (h : satisfiesClause α [x, y] = true) (hx : satisfiesLiteral α x = false) :
    satisfiesLiteral α y = true := by
  rw [satisfiesClause_iff] at h
  obtain ⟨w, hw, hwt⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl
  · rw [hx] at hwt; exact absurd hwt (by simp)
  · exact hwt

theorem satisfiesClause_three {α : Assignment} {x y z : Literal}
    (h : satisfiesClause α [x, y, z] = true) (hx : satisfiesLiteral α x = false)
    (hy : satisfiesLiteral α y = false) : satisfiesLiteral α z = true := by
  rw [satisfiesClause_iff] at h
  obtain ⟨w, hw, hwt⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  rcases hw with rfl | rfl | rfl
  · rw [hx] at hwt; exact absurd hwt (by simp)
  · rw [hy] at hwt; exact absurd hwt (by simp)
  · exact hwt

theorem satisfiesClause_one {α : Assignment} {x : Literal}
    (h : satisfiesClause α [x] = true) : satisfiesLiteral α x = true := by
  rw [satisfiesClause_iff] at h
  obtain ⟨w, hw, hwt⟩ := h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at hw
  exact hw ▸ hwt

section Sound2

variable {M : Machine} {sh : Shape} {init : TapeIdx → Nat → List Symbol} {α : Assignment}

/-- The assignment `α` describes the configuration `cfg` at time `t`. -/
structure Agrees (sh : Shape) (α : Assignment) (t : Nat) (cfg : Config) : Prop where
  /-- The state variable of `cfg.1` is set. -/
  st : α (sh.stateVar t cfg.1) = true
  /-- The head variable of each actual head position is set. -/
  hd : ∀ j, j < sh.k → α (sh.headVar t j (headPos cfg j)) = true
  /-- The cell variable of each actual symbol is set. -/
  cl : ∀ j, j < sh.k → ∀ p, p ≤ sh.T → α (sh.cellVar t j p (tapeFun cfg j p)) = true

theorem start_state (hs : Satisfies α (startClauses sh init)) : α (sh.stateVar 0 0) = true := by
  unfold startClauses at hs
  simp only [satisfies_append] at hs
  rw [satisfies_single] at hs
  exact satisfiesClause_one hs.1.1

theorem start_head (hs : Satisfies α (startClauses sh init)) {j : Nat} (hj : j < sh.k) :
    α (sh.headVar 0 j 0) = true := by
  unfold startClauses at hs
  simp only [satisfies_append] at hs
  have h1 := (satisfies_flatMap _ _ _).mp hs.1.2 j (List.mem_range.mpr hj)
  rw [satisfies_single] at h1
  exact satisfiesClause_one h1

theorem exists_start_symbol (hs : Satisfies α (startClauses sh init))
    {j p : Nat} (hj : j < sh.k) (hp : p ≤ sh.T) :
    ∃ s ∈ init j p, α (sh.cellVar 0 j p s) = true := by
  unfold startClauses at hs
  simp only [satisfies_append] at hs
  have h1 := (satisfies_flatMap _ _ _).mp hs.2 j (List.mem_range.mpr hj)
  have h2 := (satisfies_flatMap _ _ _).mp h1 p (List.mem_range.mpr (by omega))
  rw [satisfies_single, satisfiesClause_iff] at h2
  obtain ⟨x, hx, hxt⟩ := h2
  simp only [List.mem_map] at hx
  obtain ⟨s, hsmem, rfl⟩ := hx
  exact ⟨s, hsmem, hxt⟩

/-- Reading the start configuration off a satisfying assignment gives a start
configuration allowed by `init`. -/
theorem startOK_extractStart (hG4 : 4 ≤ sh.G)
    (hstartCl : Satisfies α (startClauses sh init)) (hcell : Satisfies α (cellClauses sh))
    (hinit : ∀ j, j < sh.k → ∀ p, p ≤ sh.T → ∀ s ∈ init j p, s < sh.G) :
    StartOK sh init (extractStart sh α) := by
  have key : ∀ j, j < sh.k → ∀ p, p ≤ sh.T →
      tapeFun (extractStart sh α) j p ∈ init j p ∧ tapeFun (extractStart sh α) j p < sh.G := by
    intro j hj p hp
    obtain ⟨s, hsmem, hα⟩ := exists_start_symbol hstartCl hj hp
    have hsG := hinit j hj p hp s hsmem
    rw [tapeFun_extractStart sh α hj, if_pos hp,
      extractCell_eq hcell (Nat.zero_le _) hj hp hsG hα]
    exact ⟨hsmem, hsG⟩
  refine ⟨by simp, rfl, fun j hj => headPos_extractStart sh α hj,
    fun j hj p hp => (key j hj p hp).1, ?_, ?_⟩
  · intro j hj p hp
    rw [tapeFun_extractStart sh α hj, if_neg (by omega)]
  · intro j hj p
    by_cases hp : p ≤ sh.T
    · exact (key j hj p hp).2
    · rw [tapeFun_extractStart sh α hj, if_neg hp]
      show 0 < sh.G
      omega

theorem agrees_zero (hstartCl : Satisfies α (startClauses sh init))
    (hcell : Satisfies α (cellClauses sh))
    (hinit : ∀ j, j < sh.k → ∀ p, p ≤ sh.T → ∀ s ∈ init j p, s < sh.G) :
    Agrees sh α 0 (extractStart sh α) := by
  refine ⟨start_state hstartCl, ?_, ?_⟩
  · intro j hj
    rw [headPos_extractStart sh α hj]
    exact start_head hstartCl hj
  · intro j hj p hp
    obtain ⟨s, hsmem, hα⟩ := exists_start_symbol hstartCl hj hp
    have hsG := hinit j hj p hp s hsmem
    rw [tapeFun_extractStart sh α hj, if_pos hp,
      extractCell_eq hcell (Nat.zero_le _) hj hp hsG hα]
    exact hα

end Sound2

section Sound3

variable {M : Machine} {sh : Shape} {α : Assignment} {cfg0 : Config}

/-- At most one head variable per tape and time is set, so a head variable for
a cell the head is *not* on is false. -/
theorem head_false_of_ne (hhead : Satisfies α (headClauses sh))
    (hreg : ∀ t, Regular sh.k sh.G sh.Q t (execute M cfg0 t))
    {t : Nat} (ht : t ≤ sh.T) (hag : Agrees sh α t (execute M cfg0 t))
    {j : Nat} (hj : j < sh.k) {p : Nat} (hp : p ≤ sh.T)
    (hne : p ≠ headPos (execute M cfg0 t) j) : α (sh.headVar t j p) = false := by
  have hhdT : headPos (execute M cfg0 t) j ≤ t := (hreg t).hd j hj
  have hone : Satisfies α (exactlyOneOf (List.range (sh.T + 1)) fun p => sh.headVar t j p) := by
    have h1 := (satisfies_flatMap _ _ _).mp hhead t (List.mem_range.mpr (by omega))
    exact (satisfies_flatMap _ _ _).mp h1 j (List.mem_range.mpr hj)
  refine atMostOne_of_satisfies hone (List.mem_range.mpr (by omega))
    (List.mem_range.mpr (by omega)) ?_ (hag.hd j hj)
  exact sh.headVar_ne hj (by unfold Shape.P; omega) (by unfold Shape.P; omega)
    fun heq => hne heq.symm

/-- The link clauses force the read variable of the actually scanned symbol. -/
theorem read_true (hlink : Satisfies α (linkClauses sh))
    (hreg : ∀ t, Regular sh.k sh.G sh.Q t (execute M cfg0 t))
    {t : Nat} (ht : t ≤ sh.T) (hag : Agrees sh α t (execute M cfg0 t))
    {j : Nat} (hj : j < sh.k) :
    α (sh.readVar t j (scanned (execute M cfg0 t) j)) = true := by
  have hhdT : headPos (execute M cfg0 t) j ≤ t := (hreg t).hd j hj
  have hsG : scanned (execute M cfg0 t) j < sh.G :=
    (hreg t).sym j hj (headPos (execute M cfg0 t) j)
  have h1 := (satisfies_flatMap _ _ _).mp hlink t (List.mem_range.mpr (by omega))
  have h2 := (satisfies_flatMap _ _ _).mp h1 j (List.mem_range.mpr hj)
  have h3 := (satisfies_flatMap _ _ _).mp h2 (headPos (execute M cfg0 t) j)
    (List.mem_range.mpr (by omega))
  have h4 := (satisfies_flatMap _ _ _).mp h3 (scanned (execute M cfg0 t) j)
    (List.mem_range.mpr hsG)
  rw [satisfies_single] at h4
  refine satisfiesClause_three h4 (satisfiesLiteral_neg_false (hag.hd j hj))
    (satisfiesLiteral_neg_false ?_)
  exact hag.cl j hj _ (by omega)

/-- **The induction step of soundness.**  If `α` describes the configuration at
time `t`, the transition, inertia and halting clauses force it to describe the
successor configuration at time `t+1`. -/
theorem agrees_succ (hM : WellFormed sh.k sh.G M) (hQ : M.length = sh.Q)
    (hreg : ∀ t, Regular sh.k sh.G sh.Q t (execute M cfg0 t))
    (hhead : Satisfies α (headClauses sh)) (hlink : Satisfies α (linkClauses sh))
    (htrans : Satisfies α (transitionClauses sh M))
    (hinertia : Satisfies α (inertiaClauses sh)) (hhalt : Satisfies α (haltClauses sh))
    {t : Nat} (ht : t < sh.T) (hag : Agrees sh α t (execute M cfg0 t)) :
    Agrees sh α (t + 1) (execute M cfg0 (t + 1)) := by
  have htT : t ≤ sh.T := Nat.le_of_lt ht
  have hnext : execute M cfg0 (t + 1) = exe M (execute M cfg0 t) := rfl
  by_cases hlt : (execute M cfg0 t).1 < M.length
  · -- the machine is still running: use the transition and inertia clauses
    have hrd : ∀ j, j < sh.k → α (sh.readVar t j (scanned (execute M cfg0 t) j)) = true :=
      fun j hj => read_true hlink hreg htT hag hj
    have hguard : ∀ x ∈ guardClause sh t (execute M cfg0 t).1
        (readList (execute M cfg0 t) sh.k), satisfiesLiteral α x = false := by
      intro x hx
      unfold guardClause at hx
      simp only [List.mem_cons, List.mem_map, List.mem_range] at hx
      rcases hx with rfl | ⟨j, hj, rfl⟩
      · exact satisfiesLiteral_neg_false hag.st
      · rw [readList_getD _ hj]
        exact satisfiesLiteral_neg_false (hrd j hj)
    have hts : Satisfies α (transitionStep sh M t (execute M cfg0 t).1
        (readList (execute M cfg0 t) sh.k)) := by
      have h1 := (satisfies_flatMap _ _ _).mp htrans t (List.mem_range.mpr ht)
      have h2 := (satisfies_flatMap _ _ _).mp h1 (execute M cfg0 t).1 (List.mem_range.mpr hlt)
      exact (satisfies_flatMap _ _ _).mp h2 _
        (readList_mem_tuples fun j hj p => (hreg t).sym j hj p)
    -- the command evaluated in the clauses is the command actually executed
    have hres : (M.getD (execute M cfg0 t).1 defaultCommand) (readList (execute M cfg0 t) sh.k)
        = stepRes M (execute M cfg0 t) := by
      unfold stepRes cmdOf
      rw [read_eq_readList _ (hreg t).len]
    have hactEq : ∀ j, cmdAction M (execute M cfg0 t).1 (readList (execute M cfg0 t) sh.k) j
        = writeOf M (execute M cfg0 t) j := by
      intro j; unfold cmdAction writeOf; rw [hres]
    unfold transitionStep at hts
    simp only [satisfies_append] at hts
    refine ⟨?_, ?_, ?_⟩
    · -- next state
      rw [satisfies_single] at hts
      have hcl := satisfiesClause_append_right hts.1 hguard
      have := satisfiesClause_one hcl
      rw [hnext, exe_fst_running hlt, ← hres]
      exact this
    · -- head positions
      intro j hj
      have hhdT : headPos (execute M cfg0 t) j ≤ t := (hreg t).hd j hj
      have h1 := (satisfies_flatMap _ _ _).mp hts.2 j (List.mem_range.mpr hj)
      have h2 := (satisfies_flatMap _ _ _).mp h1 (headPos (execute M cfg0 t) j)
        (List.mem_range.mpr (by omega))
      have h3 := h2 _ List.mem_cons_self
      have h4 := satisfiesClause_append_right h3 hguard
      have h5 := satisfiesClause_two h4 (satisfiesLiteral_neg_false (hag.hd j hj))
      rw [hnext, headPos_exe_running hM (hreg t).len hlt hj, ← hactEq j]
      exact h5
    · -- cell contents
      intro j hj p hp
      have hhdT : headPos (execute M cfg0 t) j ≤ t := (hreg t).hd j hj
      by_cases hhd : p = headPos (execute M cfg0 t) j
      · -- the cell under the head: written as `M` says
        have h1 := (satisfies_flatMap _ _ _).mp hts.2 j (List.mem_range.mpr hj)
        have h2 := (satisfies_flatMap _ _ _).mp h1 p (List.mem_range.mpr (by omega))
        have h3 := h2 _ (List.mem_cons_of_mem _ List.mem_cons_self)
        have h4 := satisfiesClause_append_right h3 hguard
        have h5 := satisfiesClause_two h4
          (satisfiesLiteral_neg_false (hhd ▸ hag.hd j hj))
        rw [hnext, tapeFun_exe_running hM (hreg t).len hlt hj p, if_pos hhd, ← hactEq j]
        exact h5
      · -- any other cell: unchanged, by inertia
        have hsG : tapeFun (execute M cfg0 t) j p < sh.G := (hreg t).sym j hj p
        have h1 := (satisfies_flatMap _ _ _).mp hinertia t (List.mem_range.mpr ht)
        have h2 := (satisfies_flatMap _ _ _).mp h1 j (List.mem_range.mpr hj)
        have h3 := (satisfies_flatMap _ _ _).mp h2 p (List.mem_range.mpr (by omega))
        have h4 := (satisfies_flatMap _ _ _).mp h3 (tapeFun (execute M cfg0 t) j p)
          (List.mem_range.mpr hsG)
        rw [satisfies_single] at h4
        have h5 := satisfiesClause_three h4
          (head_false_of_ne hhead hreg htT hag hj hp hhd)
          (satisfiesLiteral_neg_false (hag.cl j hj p hp))
        rw [hnext, tapeFun_step_of_ne hM (hreg t).len hj hhd]
        exact h5
  · -- the machine has halted: use the halting clauses
    have hstQ : (execute M cfg0 t).1 = sh.Q := by
      have h1 : (execute M cfg0 t).1 ≤ sh.Q := (hreg t).st
      have h2 : M.length ≤ (execute M cfg0 t).1 := Nat.not_lt.mp hlt
      rw [hQ] at h2
      exact Nat.le_antisymm h1 h2
    have hfix : execute M cfg0 (t + 1) = execute M cfg0 t := by
      rw [hnext]; exact exe_halted hlt
    have hnegState : satisfiesLiteral α (Literal.Neg (sh.stateVar t sh.Q)) = false :=
      satisfiesLiteral_neg_false (hstQ ▸ hag.st)
    have hgroup := (satisfies_flatMap _ _ _).mp hhalt t (List.mem_range.mpr ht)
    simp only [satisfies_append] at hgroup
    refine ⟨?_, ?_, ?_⟩
    · rw [satisfies_single] at hgroup
      have := satisfiesClause_two hgroup.1 hnegState
      rw [hfix, hstQ]
      exact this
    · intro j hj
      have hhdT : headPos (execute M cfg0 t) j ≤ t := (hreg t).hd j hj
      have h1 := (satisfies_flatMap _ _ _).mp hgroup.2 j (List.mem_range.mpr hj)
      have h2 := (satisfies_flatMap _ _ _).mp h1 (headPos (execute M cfg0 t) j)
        (List.mem_range.mpr (by omega))
      simp only [satisfies_append] at h2
      rw [satisfies_single] at h2
      have h3 := satisfiesClause_three h2.1 hnegState
        (satisfiesLiteral_neg_false (hag.hd j hj))
      rw [hfix]
      exact h3
    · intro j hj p hp
      have hsG : tapeFun (execute M cfg0 t) j p < sh.G := (hreg t).sym j hj p
      have h1 := (satisfies_flatMap _ _ _).mp hgroup.2 j (List.mem_range.mpr hj)
      have h2 := (satisfies_flatMap _ _ _).mp h1 p (List.mem_range.mpr (by omega))
      simp only [satisfies_append] at h2
      have h3 := (satisfies_flatMap _ _ _).mp h2.2 (tapeFun (execute M cfg0 t) j p)
        (List.mem_range.mpr hsG)
      rw [satisfies_single] at h3
      have h4 := satisfiesClause_three h3 hnegState
        (satisfiesLiteral_neg_false (hag.cl j hj p hp))
      rw [hfix]
      exact h4

end Sound3

section Main

variable {M : Machine} {sh : Shape} {init : TapeIdx → Nat → List Symbol} {α : Assignment}

theorem agrees_of_le (hM : WellFormed sh.k sh.G M) (hQ : M.length = sh.Q)
    (hsat : Satisfies α (tableauCNF sh M init))
    (hinit : ∀ j, j < sh.k → ∀ p, p ≤ sh.T → ∀ s ∈ init j p, s < sh.G) :
    ∀ t, t ≤ sh.T → Agrees sh α t (execute M (extractStart sh α) t) := by
  obtain ⟨hstartCl, hcell, hhead, hstateCl, hreadCl, hlink, htrans, hinertia, hhalt, haccept⟩ :=
    tableau_groups hsat
  have hstart := startOK_extractStart hM.four_le hstartCl hcell hinit
  have hreg := regular_run hM hQ hstart
  intro t
  induction t with
  | zero => intro _; exact agrees_zero hstartCl hcell hinit
  | succ t ih =>
    intro hle
    exact agrees_succ hM hQ hreg hhead hlink htrans hinertia hhalt (by omega) (ih (by omega))

theorem accepts_of_satisfies (hM : WellFormed sh.k sh.G M) (hQ : M.length = sh.Q)
    (h1T : 1 ≤ sh.T) (hsat : Satisfies α (tableauCNF sh M init))
    (hinit : ∀ j, j < sh.k → ∀ p, p ≤ sh.T → ∀ s ∈ init j p, s < sh.G) :
    AcceptsCfg M sh.k (extractStart sh α) sh.T := by
  obtain ⟨hstartCl, hcell, hhead, hstateCl, hreadCl, hlink, htrans, hinertia, hhalt, haccept⟩ :=
    tableau_groups hsat
  have hstart := startOK_extractStart hM.four_le hstartCl hcell hinit
  have hreg := regular_run hM hQ hstart
  have hagT := agrees_of_le hM hQ hsat hinit sh.T (Nat.le_refl _)
  have hacc1 : α (sh.stateVar sh.T sh.Q) = true :=
    satisfiesClause_one (haccept _ List.mem_cons_self)
  have hacc2 : α (sh.cellVar sh.T (verdictTape sh.k) 1 (boolSym true)) = true :=
    satisfiesClause_one (haccept _ (List.mem_cons_of_mem _ List.mem_cons_self))
  have hk : verdictTape sh.k < sh.k := by
    have h2 := hM.two_le
    show sh.k - 1 < sh.k
    omega
  have h1P : 1 < sh.P := by unfold Shape.P; omega
  have hbG : boolSym true < sh.G := by
    have h4 := hM.four_le
    show 3 < sh.G
    omega
  have hstate : (execute M (extractStart sh α) sh.T).1 = sh.Q := by
    by_cases he : (execute M (extractStart sh α) sh.T).1 = sh.Q
    · exact he
    · exfalso
      have hone : Satisfies α (exactlyOneOf (List.range sh.QQ) fun q => sh.stateVar sh.T q) :=
        (satisfies_flatMap _ _ _).mp hstateCl sh.T (List.mem_range.mpr (by omega))
      have hb1 : (execute M (extractStart sh α) sh.T).1 < sh.QQ :=
        Nat.lt_succ_of_le (hreg sh.T).st
      have hb2 : sh.Q < sh.QQ := Nat.lt_succ_self _
      have hfalse := atMostOne_of_satisfies hone (List.mem_range.mpr hb1)
        (List.mem_range.mpr hb2) (sh.stateVar_ne hb1 hb2 he) hagT.st
      rw [hacc1] at hfalse
      exact absurd hfalse (by simp)
  have hverdict :
      tapeFun (execute M (extractStart sh α) sh.T) (verdictTape sh.k) 1 = boolSym true := by
    by_cases he : tapeFun (execute M (extractStart sh α) sh.T) (verdictTape sh.k) 1 = boolSym true
    · exact he
    · exfalso
      have hsG : tapeFun (execute M (extractStart sh α) sh.T) (verdictTape sh.k) 1 < sh.G :=
        (hreg sh.T).sym _ hk 1
      have hone : Satisfies α
          (exactlyOneOf (List.range sh.G) fun s => sh.cellVar sh.T (verdictTape sh.k) 1 s) := by
        have g1 := (satisfies_flatMap _ _ _).mp hcell sh.T (List.mem_range.mpr (by omega))
        have g2 := (satisfies_flatMap _ _ _).mp g1 (verdictTape sh.k) (List.mem_range.mpr hk)
        exact (satisfies_flatMap _ _ _).mp g2 1 (List.mem_range.mpr (by omega))
      have hfalse := atMostOne_of_satisfies hone (List.mem_range.mpr hsG)
        (List.mem_range.mpr hbG) (sh.cellVar_ne hk h1P hsG hbG he)
        (hagT.cl _ hk 1 h1T)
      rw [hacc2] at hfalse
      exact absurd hfalse (by simp)
  exact ⟨by rw [hstate, hQ], hverdict⟩

/-- **Correctness of the tableau reduction.**

`tableauCNF sh M init` is satisfiable exactly when `M`, started in some
configuration allowed by `init`, accepts within `sh.T` steps.

Soundness (left to right) extracts a start configuration from the assignment
and shows by induction on time that the assignment describes the *actual* run
of `M` on it; completeness (right to left) exhibits the assignment that reads
the accepting run off. -/
theorem tableau_correct (hM : WellFormed sh.k sh.G M) (hQ : M.length = sh.Q) (h1T : 1 ≤ sh.T)
    (hinit : ∀ j, j < sh.k → ∀ p, p ≤ sh.T → ∀ s ∈ init j p, s < sh.G) :
    Satisfiable (tableauCNF sh M init) ↔
      ∃ cfg0, StartOK sh init cfg0 ∧ AcceptsCfg M sh.k cfg0 sh.T := by
  constructor
  · rintro ⟨α, hα⟩
    obtain ⟨hstartCl, hcell, -⟩ := tableau_groups hα
    exact ⟨extractStart sh α, startOK_extractStart hM.four_le hstartCl hcell hinit,
      accepts_of_satisfies hM hQ h1T hα hinit⟩
  · rintro ⟨cfg0, hstart, hacc⟩
    exact ⟨runAssign sh (execute M cfg0), satisfies_tableauCNF hM hQ hstart hacc⟩

end Main

/-! ## Certificates of unbounded length

The reduction leaves the certificate tape free, but a *free* cell may hold a
blank as well as a bit, and an assignment could scatter blanks through the
middle of the certificate, which corresponds to no bit string at all.  The
clauses below rule that out: once a cell of tape `j` is blank at time `0`, so is
the next one.  The allowed tape contents are then exactly
`contents (boolsToSymbols w)` for bit strings `w` of length at most the free
region -- certificates of *every* length up to the bound, which is what the
textbook definition of NP requires. -/

/-- "At time `0`, if cell `p` of tape `j` is blank then so is cell `p+1`." -/
def blankSuffixClauses (sh : Shape) (j : TapeIdx) : Formula :=
  (List.range sh.T).flatMap fun p =>
    [[Literal.Neg (sh.cellVar 0 j p blankSymbol),
      Literal.Pos (sh.cellVar 0 j (p + 1) blankSymbol)]]

/-- The corresponding property of a configuration. -/
def BlankSuffix (sh : Shape) (cfg : Config) (j : TapeIdx) : Prop :=
  ∀ p, p < sh.T → tapeFun cfg j p = blankSymbol → tapeFun cfg j (p + 1) = blankSymbol

theorem BlankSuffix.mono {sh : Shape} {cfg : Config} {j : TapeIdx}
    (h : BlankSuffix sh cfg j) {p q : Nat} (hpq : p ≤ q) (hq : q ≤ sh.T)
    (hp : tapeFun cfg j p = blankSymbol) : tapeFun cfg j q = blankSymbol := by
  induction q with
  | zero => have : p = 0 := by omega
            exact this ▸ hp
  | succ q ih =>
    by_cases hpq' : p = q + 1
    · exact hpq' ▸ hp
    · exact h q (by omega) (ih (by omega) (by omega))

section Cert

variable {M : Machine} {sh : Shape} {init : TapeIdx → Nat → List Symbol} {α : Assignment}

/-- The symbol `extractCell` produces really is the one the assignment sets.
(The `find?` cannot fail: the at-least-one clause of `cellClauses` guarantees a
hit.) -/
theorem extractCell_spec (hcell : Satisfies α (cellClauses sh)) {t j p : Nat}
    (ht : t ≤ sh.T) (hj : j < sh.k) (hp : p ≤ sh.T) :
    extractCell sh α t j p < sh.G ∧ α (sh.cellVar t j p (extractCell sh α t j p)) = true := by
  have hone : Satisfies α (exactlyOneOf (List.range sh.G) fun s => sh.cellVar t j p s) := by
    have h1 := (satisfies_flatMap _ _ _).mp hcell t (List.mem_range.mpr (by omega))
    have h2 := (satisfies_flatMap _ _ _).mp h1 j (List.mem_range.mpr hj)
    exact (satisfies_flatMap _ _ _).mp h2 p (List.mem_range.mpr (by omega))
  unfold exactlyOneOf at hone
  rw [satisfies_append, satisfies_single, satisfiesClause_iff] at hone
  obtain ⟨x, hx, hxt⟩ := hone.1
  simp only [List.mem_map, List.mem_range] at hx
  obtain ⟨s, hs, rfl⟩ := hx
  have hnone : (List.range sh.G).find? (fun s => α (sh.cellVar t j p s)) ≠ none := by
    intro hn
    exact (List.find?_eq_none.mp hn s (List.mem_range.mpr hs)) hxt
  cases hfind : (List.range sh.G).find? (fun s => α (sh.cellVar t j p s)) with
  | none => exact absurd hfind hnone
  | some s0 =>
    have hval : extractCell sh α t j p = s0 := by unfold extractCell; rw [hfind]; rfl
    rw [hval]
    refine ⟨List.mem_range.mp (List.mem_of_find?_eq_some hfind), ?_⟩
    have := List.find?_some hfind
    simpa using this

/-- Soundness of the blank-suffix clauses. -/
theorem blankSuffix_extractStart (hcell : Satisfies α (cellClauses sh))
    (hG : 4 ≤ sh.G) (hbs : Satisfies α (blankSuffixClauses sh j)) (hj : j < sh.k) :
    BlankSuffix sh (extractStart sh α) j := by
  intro p hp hblank
  have hpT : p ≤ sh.T := by omega
  have hp1T : p + 1 ≤ sh.T := by omega
  have hbG : blankSymbol < sh.G := by show 0 < sh.G; omega
  -- the assignment sets the blank variable at `p`
  have hset : α (sh.cellVar 0 j p blankSymbol) = true := by
    have := (extractCell_spec hcell (Nat.zero_le _) hj hpT).2
    rwa [show extractCell sh α 0 j p = blankSymbol by
      rw [tapeFun_extractStart sh α hj, if_pos hpT] at hblank; exact hblank] at this
  -- the clause propagates it to `p+1`
  have hcl := (satisfies_flatMap _ _ _).mp hbs p (List.mem_range.mpr hp)
  rw [satisfies_single] at hcl
  have hnext : α (sh.cellVar 0 j (p + 1) blankSymbol) = true :=
    satisfiesClause_two hcl (satisfiesLiteral_neg_false hset)
  rw [tapeFun_extractStart sh α hj, if_pos hp1T,
    extractCell_eq hcell (Nat.zero_le _) hj hp1T hbG hnext]

/-- Completeness of the blank-suffix clauses. -/
theorem satisfies_blankSuffixClauses (hG : 4 ≤ sh.G) {cfg0 : Config} {j : TapeIdx}
    (hj : j < sh.k) (h : BlankSuffix sh cfg0 j) :
    Satisfies (runAssign sh (execute M cfg0)) (blankSuffixClauses sh j) := by
  have hbG : blankSymbol < sh.G := by show 0 < sh.G; omega
  unfold blankSuffixClauses
  rw [satisfies_flatMap]
  intro p hp
  rw [List.mem_range] at hp
  rw [satisfies_single]
  have h0 : execute M cfg0 0 = cfg0 := rfl
  by_cases hb : tapeFun cfg0 j p = blankSymbol
  · refine satisfiesClause_of_mem (List.mem_cons_of_mem _ List.mem_cons_self) ?_
    show runAssign sh (execute M cfg0) (sh.cellVar 0 j (p + 1) blankSymbol) = true
    rw [runAssign_cell sh _ hj (by unfold Shape.P; omega) hbG, h0, h p hp hb]
    simp
  · refine satisfiesClause_of_mem List.mem_cons_self ?_
    show (!runAssign sh (execute M cfg0) (sh.cellVar 0 j p blankSymbol)) = true
    rw [runAssign_cell sh _ hj (by unfold Shape.P; omega) hbG, h0]
    simp [hb]

/-- **Correctness of the tableau with a variable-length certificate region.** -/
theorem tableau_correct_blank (hM : WellFormed sh.k sh.G M) (hQ : M.length = sh.Q)
    (h1T : 1 ≤ sh.T) {j : TapeIdx} (hj : j < sh.k)
    (hinit : ∀ i, i < sh.k → ∀ p, p ≤ sh.T → ∀ s ∈ init i p, s < sh.G) :
    Satisfiable (tableauCNF sh M init ++ blankSuffixClauses sh j) ↔
      ∃ cfg0, StartOK sh init cfg0 ∧ BlankSuffix sh cfg0 j ∧ AcceptsCfg M sh.k cfg0 sh.T := by
  constructor
  · rintro ⟨α, hα⟩
    rw [satisfies_append] at hα
    obtain ⟨hstartCl, hcell, -⟩ := tableau_groups hα.1
    exact ⟨extractStart sh α, startOK_extractStart hM.four_le hstartCl hcell hinit,
      blankSuffix_extractStart hcell hM.four_le hα.2 hj,
      accepts_of_satisfies hM hQ h1T hα.1 hinit⟩
  · rintro ⟨cfg0, hstart, hbs, hacc⟩
    refine ⟨runAssign sh (execute M cfg0), ?_⟩
    rw [satisfies_append]
    exact ⟨satisfies_tableauCNF hM hQ hstart hacc,
      satisfies_blankSuffixClauses hM.four_le hj hbs⟩

end Cert

end CookLevin
