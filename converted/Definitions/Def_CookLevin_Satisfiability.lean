/-
prove2.me platform library module `Definitions.Def_CookLevin_Satisfiability`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_CookLevin_Satisfiability.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

/-
  CookLevinLean/Satisfiability.lean

  CNF formulas, satisfiability, encoding of formulas as numbers / binary
  strings, and the language SAT.  Translated from the Isabelle/HOL theory
  `Satisfiability.thy` of the Cook–Levin formalization.
-/
import Definitions.Def_CookLevin_Basic
set_option autoImplicit true

namespace CookLevin

/-! ## Literals, clauses, formulas, assignments -/

/-- A set of elements of type α -/
def Set (α : Type) := α → Prop

/-- Set membership -/
def Set.mem (x : α) (s : Set α) : Prop := s x

/-- A literal is a negated or a positive propositional variable. -/
inductive Literal
  | Neg (n : Nat)
  | Pos (n : Nat)
  deriving DecidableEq, Repr, Inhabited

/-- The variable occurring in a literal. -/
def Literal.var : Literal → Nat
  | .Neg n => n
  | .Pos n => n

/-- The negation of a literal. -/
def Literal.negate : Literal → Literal
  | .Neg n => .Pos n
  | .Pos n => .Neg n

/-- A clause is a disjunction of literals, represented as a list. -/
abbrev Clause := List Literal

/-- A CNF formula is a conjunction of clauses, represented as a list. -/
abbrev Formula := List Clause

/-- An assignment maps variable indices to truth values. -/
abbrev Assignment := Nat → Bool

/-! ## Satisfaction -/

/-- Truth value of a literal under an assignment. -/
def satisfiesLiteral (α : Assignment) : Literal → Bool
  | .Neg n => !α n
  | .Pos n => α n

/-- A clause is satisfied if at least one of its literals is. -/
def satisfiesClause (α : Assignment) (c : Clause) : Bool :=
  c.any (satisfiesLiteral α)

/-- A formula is satisfied if all of its clauses are (`α ⊨ φ`). -/
def Satisfies (α : Assignment) (φ : Formula) : Prop :=
  ∀ c ∈ φ, satisfiesClause α c = true

/-- Notation `α ⊨ φ` for `Satisfies α φ`. -/
scoped infix:60 " ⊨ " => Satisfies

instance (α : Assignment) (φ : Formula) : Decidable (Satisfies α φ) := by
  unfold Satisfies; infer_instance

/-- Boolean version of `Satisfies`. -/
def satisfiesB (α : Assignment) (φ : Formula) : Bool :=
  φ.all (satisfiesClause α)

theorem satisfiesB_eq_true_iff (α : Assignment) (φ : Formula) :
    satisfiesB α φ = true ↔ Satisfies α φ := by
  simp [satisfiesB, Satisfies, List.all_eq_true]

theorem satisfiesClause_iff (α : Assignment) (c : Clause) :
    satisfiesClause α c = true ↔ ∃ x ∈ c, satisfiesLiteral α x = true := by
  simp [satisfiesClause, List.any_eq_true]

/-- A formula is satisfiable if some assignment satisfies it. -/
def Satisfiable (φ : Formula) : Prop :=
  ∃ α : Assignment, Satisfies α φ

/-- The set of variables occurring in a formula. -/
def «variables» (φ : Formula) : Set Nat :=
  fun n => ∃ c ∈ φ, Literal.Neg n ∈ c ∨ Literal.Pos n ∈ c

/-- The list of variables occurring in a formula (with repetitions). -/
def variablesList (φ : Formula) : List Nat :=
  φ.foldr (fun c acc => c.map Literal.var ++ acc) []

/-- The size of a formula: the total number of literal occurrences. -/
def fsize (φ : Formula) : Nat :=
  (φ.map List.length).sum

/-! ## Encoding literals, clauses and formulas as natural numbers -/

/-- Literals as numbers: `Neg i ↦ 2i`, `Pos i ↦ 2i + 1`. -/
def literalN : Literal → Nat
  | .Neg i => 2 * i
  | .Pos i => 2 * i + 1

/-- Numbers as literals: even numbers are negative, odd ones positive. -/
def nLiteral (n : Nat) : Literal :=
  if n % 2 = 0 then .Neg (n / 2) else .Pos (n / 2)

/-- Clauses as lists of numbers. -/
def clauseN (cl : Clause) : List Nat :=
  cl.map literalN

/-- Lists of numbers as clauses. -/
def nClause (ns : List Nat) : Clause :=
  ns.map nLiteral

/-- Formulas as lists of lists of numbers. -/
def formulaN (φ : Formula) : List (List Nat) :=
  φ.map clauseN

/-- Lists of lists of numbers as formulas. -/
def nFormula (nss : List (List Nat)) : Formula :=
  nss.map nClause

/-! ### Round-trip properties of the numeric encoding -/

@[simp] theorem nLiteral_literalN (x : Literal) : nLiteral (literalN x) = x := by
  cases x with
  | Neg i =>
    have h1 : (2 * i) % 2 = 0 := by omega
    have h2 : (2 * i) / 2 = i := by omega
    simp [nLiteral, literalN, h1, h2]
  | Pos i =>
    have _h1 : ¬ (2 * i + 1) % 2 = 0 := by omega
    have h2 : (2 * i + 1) / 2 = i := by omega
    simp [nLiteral, literalN, h2]

@[simp] theorem literalN_nLiteral (n : Nat) : literalN (nLiteral n) = n := by
  unfold nLiteral
  by_cases h : n % 2 = 0
  · simp [h, literalN]; omega
  · simp [h, literalN]; omega

@[simp] theorem nClause_clauseN (cl : Clause) : nClause (clauseN cl) = cl := by
  simp [nClause, clauseN, List.map_map, Function.comp_def]

@[simp] theorem clauseN_nClause (ns : List Nat) : clauseN (nClause ns) = ns := by
  simp [nClause, clauseN, List.map_map, Function.comp_def]

@[simp] theorem nFormula_formulaN (φ : Formula) : nFormula (formulaN φ) = φ := by
  simp [nFormula, formulaN, List.map_map, Function.comp_def]

@[simp] theorem formulaN_nFormula (nss : List (List Nat)) : formulaN (nFormula nss) = nss := by
  simp [nFormula, formulaN, List.map_map, Function.comp_def]

theorem literalN_injective : Function.Injective literalN :=
  Function.LeftInverse.injective nLiteral_literalN

theorem clauseN_injective : Function.Injective clauseN :=
  Function.LeftInverse.injective nClause_clauseN

theorem formulaN_injective : Function.Injective formulaN :=
  Function.LeftInverse.injective nFormula_formulaN

theorem length_clauseN (cl : Clause) : (clauseN cl).length = cl.length := by
  simp [clauseN]

theorem length_formulaN (φ : Formula) : (formulaN φ).length = φ.length := by
  simp [formulaN]

/-! ### Basic facts about `fsize` -/

@[simp] theorem fsize_nil : fsize [] = 0 := rfl

@[simp] theorem fsize_cons (c : Clause) (φ : Formula) :
    fsize (c :: φ) = c.length + fsize φ := by
  simp [fsize]

theorem fsize_append (φ ψ : Formula) : fsize (φ ++ ψ) = fsize φ + fsize ψ := by
  simp [fsize]

/-! ## Encoding formulas as binary strings -/

/-- A language is a set of binary strings. -/
abbrev Language := List Bool → Prop

/-- Encode a natural number as a list of Bools (unary: `n` true's followed by a false). -/
def encodeNat : Nat → List Bool
  | 0 => [false]
  | n + 1 => true :: encodeNat n

@[simp] theorem encodeNat_length (n : Nat) : (encodeNat n).length = n + 1 := by
  induction n with
  | zero => rfl
  | succ n ih => simp [encodeNat, ih]

theorem encodeNat_append (n : Nat) (rest : List Bool) :
    encodeNat n ++ rest = match n with
      | 0 => false :: rest
      | n + 1 => true :: (encodeNat n ++ rest) := by
  cases n <;> rfl

/-- Decode a natural number from a list of Bools using fuel. -/
def decodeNatFuel : Nat → List Bool → Nat × List Bool
  | 0, bs => (0, bs)
  | _fuel + 1, false :: bs => (0, bs)
  | fuel + 1, true :: bs => let (r, rest) := decodeNatFuel fuel bs; (r + 1, rest)
  | _fuel + 1, [] => (0, [])

theorem decodeNatFuel_encodeNat (fuel : Nat) (n : Nat) (rest : List Bool) (h : n < fuel) :
    decodeNatFuel fuel (encodeNat n ++ rest) = (n, rest) := by
  induction n generalizing fuel with
  | zero =>
    cases fuel with
    | zero => omega
    | succ fuel => rfl
  | succ n ih =>
    cases fuel with
    | zero => omega
    | succ fuel =>
      have h1 : n < fuel := by omega
      rw [encodeNat_append]
      simp [decodeNatFuel, ih fuel h1]

/-- Encode a list of natural numbers. -/
def encodeListNat : List Nat → List Bool
  | [] => [false]
  | n :: ns => true :: (encodeNat n ++ encodeListNat ns)

@[simp] theorem encodeListNat_length (ns : List Nat) : (encodeListNat ns).length ≥ 1 := by
  cases ns <;> simp [encodeListNat]

theorem encodeListNat_append (ns : List Nat) (rest : List Bool) :
    encodeListNat ns ++ rest = match ns with
      | [] => false :: rest
      | n :: ns' => true :: (encodeNat n ++ (encodeListNat ns' ++ rest)) := by
  cases ns <;> simp [encodeListNat]

/-- Decode a list of natural numbers using fuel. -/
def decodeListNatFuel : Nat → List Bool → List Nat × List Bool
  | 0, bs => ([], bs)
  | _fuel + 1, false :: bs => ([], bs)
  | fuel + 1, true :: bs =>
    let (n, bs1) := decodeNatFuel fuel bs
    let (ns, bs2) := decodeListNatFuel fuel bs1
    (n :: ns, bs2)
  | _fuel + 1, [] => ([], [])

theorem decodeListNatFuel_encodeListNat (fuel : Nat) (ns : List Nat) (rest : List Bool)
    (h : (encodeListNat ns ++ rest).length ≤ fuel) :
    decodeListNatFuel fuel (encodeListNat ns ++ rest) = (ns, rest) := by
  induction ns generalizing fuel with
  | nil =>
    cases fuel with
    | zero =>
      rw [encodeListNat_append] at h
      simp at h
    | succ fuel =>
      rw [encodeListNat_append]
      rfl
  | cons n ns ih =>
    cases fuel with
    | zero =>
      rw [encodeListNat_append] at h
      simp at h
    | succ fuel =>
      rw [encodeListNat_append]
      have hlen : (encodeListNat (n :: ns) ++ rest).length = (encodeNat n).length + (encodeListNat ns ++ rest).length + 1 := by
        simp [encodeListNat]
      have hn : n < fuel := by
        rw [hlen, encodeNat_length] at h
        omega
      have hrest : (encodeListNat ns ++ rest).length ≤ fuel := by
        rw [hlen, encodeNat_length] at h
        omega
      simp [decodeListNatFuel, decodeNatFuel_encodeNat fuel n _ hn, ih fuel hrest]

/-! ### The encoding as a stream

A machine writes the encoding left to right, one piece per turn of a loop, so
what it needs is not the recursive definition but a *flat* description: the bits
of `encodeListNat (l.map f)` are exactly one `true` and one `encodeNat` per
element of `l`, then a closing `false`.  These two lemmas are the bridge between
"the bits a loop emits" and "`encodeFormula` of the CNF". -/

theorem encodeListNat_map {β : Type} (f : β → Nat) : ∀ l : List β,
    encodeListNat (l.map f) = l.flatMap (fun x => true :: encodeNat (f x)) ++ [false]
  | [] => rfl
  | x :: l => by
    rw [List.map_cons, encodeListNat, List.flatMap_cons, encodeListNat_map f l]
    simp [List.append_assoc]

/-- Encode a list of lists of natural numbers (`formulaN`). -/
def encodeFormulaN : List (List Nat) → List Bool
  | [] => [false]
  | ns :: nss => true :: (encodeListNat ns ++ encodeFormulaN nss)

theorem encodeFormulaN_map {β : Type} (f : β → List Nat) : ∀ l : List β,
    encodeFormulaN (l.map f) = l.flatMap (fun x => true :: encodeListNat (f x)) ++ [false]
  | [] => rfl
  | x :: l => by
    rw [List.map_cons, encodeFormulaN, List.flatMap_cons, encodeFormulaN_map f l]
    simp [List.append_assoc]

theorem encodeFormulaN_append (nss : List (List Nat)) (rest : List Bool) :
    encodeFormulaN nss ++ rest = match nss with
      | [] => false :: rest
      | ns :: nss' => true :: (encodeListNat ns ++ (encodeFormulaN nss' ++ rest)) := by
  cases nss <;> simp [encodeFormulaN]

/-- Decode a list of lists of natural numbers using fuel. -/
def decodeFormulaNFuel : Nat → List Bool → List (List Nat) × List Bool
  | 0, bs => ([], bs)
  | _fuel + 1, false :: bs => ([], bs)
  | fuel + 1, true :: bs =>
    let (ns, bs1) := decodeListNatFuel fuel bs
    let (nss, bs2) := decodeFormulaNFuel fuel bs1
    (ns :: nss, bs2)
  | _fuel + 1, [] => ([], [])

theorem decodeFormulaNFuel_encodeFormulaN (fuel : Nat) (nss : List (List Nat)) (rest : List Bool)
    (h : (encodeFormulaN nss ++ rest).length ≤ fuel) :
    (decodeFormulaNFuel fuel (encodeFormulaN nss ++ rest)).1 = nss := by
  induction nss generalizing fuel with
  | nil =>
    cases fuel with
    | zero =>
      rw [encodeFormulaN_append] at h
      simp at h
    | succ fuel =>
      rw [encodeFormulaN_append]
      rfl
  | cons ns nss ih =>
    cases fuel with
    | zero =>
      rw [encodeFormulaN_append] at h
      simp at h
    | succ fuel =>
      rw [encodeFormulaN_append]
      have hlen : (encodeFormulaN (ns :: nss) ++ rest).length = (encodeListNat ns).length + (encodeFormulaN nss ++ rest).length + 1 := by
        simp [encodeFormulaN]
      have hns : (encodeListNat ns ++ (encodeFormulaN nss ++ rest)).length ≤ fuel := by
        rw [hlen] at h
        simp at h ⊢
        omega
      have hnss : (encodeFormulaN nss ++ rest).length ≤ fuel := by
        rw [hlen] at h
        have := encodeListNat_length ns
        omega
      simp [decodeFormulaNFuel, decodeListNatFuel_encodeListNat fuel ns _ hns, ih fuel hnss]

/-- Decoding formula from binary string. -/
def decodeFormula (bs : List Bool) : Formula :=
  nFormula (decodeFormulaNFuel (bs.length + 1) bs).1

/-- Encoding of a formula as a binary string. -/
def encodeFormula (φ : Formula) : List Bool :=
  encodeFormulaN (formulaN φ)

theorem decodeFormula_encodeFormula (φ : Formula) :
    decodeFormula (encodeFormula φ) = φ := by
  dsimp [decodeFormula, encodeFormula]
  have hlen : (encodeFormulaN (formulaN φ) ++ []).length ≤ (encodeFormulaN (formulaN φ)).length + 1 := by
    simp
  have hdec := decodeFormulaNFuel_encodeFormulaN ((encodeFormulaN (formulaN φ)).length + 1) (formulaN φ) [] hlen
  simp at hdec
  rw [hdec]
  exact nFormula_formulaN φ

theorem encodeFormula_injective : Function.Injective encodeFormula :=
  Function.LeftInverse.injective decodeFormula_encodeFormula

/-- A binary string is a (valid) encoding of some formula. -/
def IsFormulaString (x : List Bool) : Prop :=
  ∃ φ : Formula, x = encodeFormula φ

/-! ## The language SAT -/

/-- The language SAT: the encodings of satisfiable CNF formulas, and nothing
else.  A string that encodes no formula is *not* in SAT. -/
def SAT : Language := fun x => ∃ φ : Formula, x = encodeFormula φ ∧ Satisfiable φ

theorem SAT_of_satisfiable {φ : Formula} (h : Satisfiable φ) : SAT (encodeFormula φ) :=
  ⟨φ, rfl, h⟩

/-- A string that encodes no formula is not in SAT. -/
theorem not_SAT_of_not_formulaString {x : List Bool} (h : ¬ IsFormulaString x) : ¬ SAT x := by
  rintro ⟨φ, rfl, -⟩
  exact h ⟨φ, rfl⟩

/-- Every member of SAT is an encoding. -/
theorem isFormulaString_of_SAT {x : List Bool} (h : SAT x) : IsFormulaString x := by
  obtain ⟨φ, rfl, -⟩ := h
  exact ⟨φ, rfl⟩

/-- On valid encodings, membership in SAT is exactly satisfiability of the
encoded formula. -/
theorem SAT_encodeFormula_iff (φ : Formula) : SAT (encodeFormula φ) ↔ Satisfiable φ := by
  constructor
  · rintro ⟨ψ, hψ, hsat⟩
    have hψφ : ψ = φ := encodeFormula_injective hψ.symm
    exact hψφ ▸ hsat
  · exact SAT_of_satisfiable

/-! ## Basic facts about satisfaction -/

@[simp] theorem satisfies_nil (α : Assignment) : Satisfies α [] := by
  intro c hc
  simp at hc

theorem satisfies_cons (α : Assignment) (c : Clause) (φ : Formula) :
    Satisfies α (c :: φ) ↔ satisfiesClause α c = true ∧ Satisfies α φ := by
  simp [Satisfies]

theorem satisfies_append (α : Assignment) (φ ψ : Formula) :
    Satisfies α (φ ++ ψ) ↔ Satisfies α φ ∧ Satisfies α ψ := by
  simp [Satisfies, or_imp, forall_and]

@[simp] theorem satisfiesClause_nil (α : Assignment) : satisfiesClause α [] = false := rfl

theorem satisfiesClause_cons (α : Assignment) (x : Literal) (c : Clause) :
    satisfiesClause α (x :: c) = (satisfiesLiteral α x || satisfiesClause α c) := by
  simp [satisfiesClause]

theorem satisfiesLiteral_negate (α : Assignment) (x : Literal) :
    satisfiesLiteral α x.negate = !satisfiesLiteral α x := by
  cases x <;> simp [satisfiesLiteral, Literal.negate]

/-- The empty formula is satisfiable. -/
theorem satisfiable_nil : Satisfiable [] :=
  ⟨fun _ => true, satisfies_nil _⟩

/-- A formula containing the empty clause is unsatisfiable. -/
theorem not_satisfiable_of_nil_mem {φ : Formula} (h : [] ∈ φ) : ¬ Satisfiable φ := by
  rintro ⟨α, hα⟩
  have := hα [] h
  simp at this

/-- Removing clauses preserves satisfaction. -/
theorem satisfies_of_subset {α : Assignment} {φ ψ : Formula} (hsub : ∀ c ∈ ψ, c ∈ φ)
    (h : Satisfies α φ) : Satisfies α ψ :=
  fun c hc => h c (hsub c hc)

theorem satisfiable_of_subset {φ ψ : Formula} (hsub : ∀ c ∈ ψ, c ∈ φ)
    (h : Satisfiable φ) : Satisfiable ψ := by
  obtain ⟨α, hα⟩ := h
  exact ⟨α, satisfies_of_subset hsub hα⟩

/-! ## Variables -/

theorem var_mem_variables {φ : Formula} {c : Clause} {x : Literal}
    (hc : c ∈ φ) (hx : x ∈ c) : «variables» φ x.var := by
  exact ⟨c, hc, by cases x with | Neg n => exact Or.inl hx | Pos n => exact Or.inr hx⟩

theorem satisfiesLiteral_congr {α β : Assignment} {x : Literal} (h : α x.var = β x.var) :
    satisfiesLiteral α x = satisfiesLiteral β x := by
  cases x <;> simp [satisfiesLiteral, Literal.var] at h ⊢ <;> rw [h]

theorem satisfiesClause_congr {α β : Assignment} {c : Clause}
    (h : ∀ x ∈ c, α x.var = β x.var) :
    satisfiesClause α c = satisfiesClause β c := by
  induction c with
  | nil => rfl
  | cons x c ih =>
    rw [satisfiesClause_cons, satisfiesClause_cons,
      satisfiesLiteral_congr (h x (by simp)),
      ih (fun y hy => h y (by simp [hy]))]

/-- Satisfaction of a formula only depends on the assignment's values on the
formula's variables. -/
theorem satisfies_congr {α β : Assignment} {φ : Formula}
    (h : ∀ n, «variables» φ n → α n = β n) : Satisfies α φ ↔ Satisfies β φ := by
  have key : ∀ c ∈ φ, satisfiesClause α c = satisfiesClause β c := fun c hc =>
    satisfiesClause_congr fun x hx => h x.var (var_mem_variables hc hx)
  constructor
  · intro hα c hc; rw [← key c hc]; exact hα c hc
  · intro hβ c hc; rw [key c hc]; exact hβ c hc

theorem mem_variablesList_iff (φ : Formula) (n : Nat) :
    n ∈ variablesList φ ↔ ∃ c ∈ φ, ∃ x ∈ c, x.var = n := by
  induction φ with
  | nil => simp [variablesList]
  | cons c φ ih =>
    simp only [variablesList, List.foldr_cons, List.mem_append, List.mem_map]
    change (∃ x ∈ c, x.var = n) ∨ n ∈ variablesList φ ↔ ∃ c' ∈ c :: φ, ∃ x ∈ c', x.var = n
    rw [ih]
    constructor
    · rintro (⟨x, hx, rfl⟩ | ⟨c', hc', x, hx, rfl⟩)
      · exact ⟨c, List.mem_cons_self, x, hx, rfl⟩
      · exact ⟨c', List.mem_cons_of_mem _ hc', x, hx, rfl⟩
    · rintro ⟨c', hc', x, hx, rfl⟩
      cases List.mem_cons.mp hc' with
      | inl hhead =>
        subst hhead
        left
        exact ⟨x, hx, rfl⟩
      | inr htail =>
        right
        exact ⟨c', htail, x, hx, rfl⟩

/-- The set of variables of a formula is finite. -/
theorem variables_finite (φ : Formula) : ∃ (L : List Nat), ∀ n, «variables» φ n ↔ n ∈ L := by
  refine ⟨variablesList φ, ?_⟩
  intro n
  constructor
  · rintro ⟨c, hc, hx | hx⟩
    · rw [mem_variablesList_iff]
      exact ⟨c, hc, Literal.Neg n, hx, rfl⟩
    · rw [mem_variablesList_iff]
      exact ⟨c, hc, Literal.Pos n, hx, rfl⟩
  · intro hn
    rw [mem_variablesList_iff] at hn
    rcases hn with ⟨c, hc, x, hx, rfl⟩
    cases x with
    | Neg m => exact ⟨c, hc, Or.inl hx⟩
    | Pos m => exact ⟨c, hc, Or.inr hx⟩

def listBound : List Nat → Nat
  | [] => 0
  | a :: bs => max (a + 1) (listBound bs)

theorem le_listBound {L : List Nat} {n : Nat} (h : n ∈ L) : n < listBound L := by
  induction L with
  | nil => contradiction
  | cons a bs ih =>
    cases h with
    | head =>
      dsimp [listBound]
      omega
    | tail _ h' =>
      dsimp [listBound]
      have := ih h'
      omega

/-- Every variable of a formula is bounded by the numeric encoding of the
formula (used later for bounding the size of assignments). -/
theorem variables_bounded (φ : Formula) : ∃ N, ∀ n, «variables» φ n → n < N := by
  obtain ⟨L, hL⟩ := variables_finite φ
  refine ⟨listBound L, ?_⟩
  intro n hn
  rw [hL] at hn
  exact le_listBound hn

/-! ## Bounding variable indices by the length of the encoding

The SAT verifier of `CookLevinLean.Theorem` accepts only certificates of
length at most `|x|`.  For that bound to be attainable we must know that every
variable index occurring in `φ` is smaller than `|encodeFormula φ|`: the index
`n` is written out in *unary* inside the encoding, so it costs at least `2n+1`
bits there. -/

theorem le_length_encodeListNat {ns : List Nat} {m : Nat} (h : m ∈ ns) :
    m + 2 ≤ (encodeListNat ns).length := by
  induction ns with
  | nil => cases h
  | cons n ns ih =>
    have hlen : (encodeListNat (n :: ns)).length
        = 1 + (n + 1) + (encodeListNat ns).length := by
      simp [encodeListNat]
      omega
    cases h with
    | head => omega
    | tail _ h' => have := ih h'; omega

theorem le_length_encodeFormulaN {nss : List (List Nat)} {ns : List Nat} (h : ns ∈ nss) :
    (encodeListNat ns).length + 1 ≤ (encodeFormulaN nss).length := by
  induction nss with
  | nil => cases h
  | cons ms nss ih =>
    have hlen : (encodeFormulaN (ms :: nss)).length
        = 1 + (encodeListNat ms).length + (encodeFormulaN nss).length := by
      simp [encodeFormulaN]
      omega
    cases h with
    | head => omega
    | tail _ h' => have := ih h'; omega

/-- Every variable of `φ` has an index strictly below the length of the
encoding of `φ`. -/
theorem variables_lt_length_encodeFormula {φ : Formula} {n : Nat}
    (h : «variables» φ n) : n < (encodeFormula φ).length := by
  obtain ⟨c, hc, hlit⟩ := h
  -- the literal on `n` occurring in `c` encodes to a number `≥ 2 * n`
  obtain ⟨v, hv, hvn⟩ : ∃ v ∈ clauseN c, 2 * n ≤ v := by
    cases hlit with
    | inl hneg =>
      exact ⟨literalN (Literal.Neg n), List.mem_map_of_mem hneg, by simp [literalN]⟩
    | inr hpos =>
      exact ⟨literalN (Literal.Pos n), List.mem_map_of_mem hpos, by simp [literalN]⟩
  have h1 : v + 2 ≤ (encodeListNat (clauseN c)).length := le_length_encodeListNat hv
  have h2 : (encodeListNat (clauseN c)).length + 1 ≤ (encodeFormulaN (formulaN φ)).length :=
    le_length_encodeFormulaN (List.mem_map_of_mem hc)
  have h3 : (encodeFormula φ).length = (encodeFormulaN (formulaN φ)).length := rfl
  omega

/-- A bound on all variable indices of `φ`, computed from `φ` itself. -/
def assignmentBound (φ : Formula) : Nat := listBound (variablesList φ)

theorem lt_assignmentBound {φ : Formula} {n : Nat} (h : «variables» φ n) :
    n < assignmentBound φ := by
  obtain ⟨c, hc, hlit⟩ := h
  refine le_listBound ?_
  rw [mem_variablesList_iff]
  cases hlit with
  | inl hneg => exact ⟨c, hc, Literal.Neg n, hneg, rfl⟩
  | inr hpos => exact ⟨c, hc, Literal.Pos n, hpos, rfl⟩

theorem listBound_le {L : List Nat} {B : Nat} (h : ∀ n ∈ L, n < B) : listBound L ≤ B := by
  induction L with
  | nil => exact Nat.zero_le _
  | cons a bs ih =>
    have ha : a < B := h a List.mem_cons_self
    have hb : listBound bs ≤ B := ih fun n hn => h n (List.mem_cons_of_mem _ hn)
    dsimp [listBound]
    omega

theorem assignmentBound_le_length_encodeFormula (φ : Formula) :
    assignmentBound φ ≤ (encodeFormula φ).length := by
  refine listBound_le ?_
  intro n hn
  rw [mem_variablesList_iff] at hn
  obtain ⟨c, hc, x, hx, rfl⟩ := hn
  exact variables_lt_length_encodeFormula (var_mem_variables hc hx)

end CookLevin
