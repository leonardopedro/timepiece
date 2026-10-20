/-
prove2.me platform library module `Definitions.Def_CookLevin_Complexity`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_CookLevin_Complexity.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_CookLevin_Satisfiability
import Definitions.Def_CookLevin_Cost
set_option autoImplicit true
/-
  CookLevinLean/Complexity.lean

  Computability, the complexity classes P and NP, and Karp reductions.

  Every notion below is defined against the cost model of
  `CookLevinLean.Cost`: a *step* is one application of `exe`, and a bound is a
  bound on the number of steps the interpreter `execute` is run for.  None of
  these definitions bounds only the length of an output or of a witness --
  that was the defect of the previous version of this file, which made
  `IsPolyTimeComputable f` true of every function with short output (including
  uncomputable ones) and `IsNPVerifier V` true of every predicate with short
  witnesses.
-/




namespace CookLevin

/-- Membership of a string `x` in language `L`. -/
def InLang (x : List Bool) (L : Language) : Prop := L x

/-- `f` is computable in polynomial time: some multi-tape Turing machine
computes `f` and **halts within `c * (n+1)^d` steps** on every input of
length `n`. -/
def IsPolyTimeComputable (f : List Bool → List Bool) : Prop :=
  ∃ (M : Machine) (k G c d : Nat),
    TuringMachine k G M ∧
    ComputesInTime M k (polyBound c d) f

/-- Polynomial-time many-one (Karp) reduction from `L₁` to `L₂`. -/
def PolyReducible (L₁ L₂ : Language) : Prop :=
  ∃ f : List Bool → List Bool,
    IsPolyTimeComputable f ∧ ∀ x : List Bool, InLang x L₁ ↔ InLang (f x) L₂

infix:50 " ≤p " => PolyReducible

/-- `V` is decided by some multi-tape Turing machine **within
`c * (|x|+|w|+1)^d` steps**, with `x` on tape `0` and `w` on tape `1`.

This isolates the one ingredient of `IsNPVerifier` that is about *implementing*
a decision procedure, as opposed to its input/output behaviour. -/
def PolyTimeDecidable (V : List Bool → List Bool → Bool) : Prop :=
  ∃ (M : Machine) (k G c d : Nat),
    TuringMachine k G M ∧
    ∀ x w : List Bool,
      DecidesIn M k (boolsToSymbols x) (boolsToSymbols w)
        (polyBound c d (x.length + w.length)) (V x w)

/-- `V` is a polynomial-time verifier: it is decided by a machine running in
polynomially many *steps*, and it only accepts certificates of length at most
`polyBound c d |x|`.

This is the textbook definition, with `≤` rather than `=`: no normal-form
assumption is made anywhere in this development, and the reduction of
`CookLevinLean/Reduction.lean` handles certificates of every length up to the
bound (see `blankSuffixClauses` there). -/
def IsNPVerifier (c d : Nat) (V : List Bool → List Bool → Bool) : Prop :=
  PolyTimeDecidable V ∧
    ∀ x w : List Bool, V x w = true → w.length ≤ polyBound c d x.length

/-- The data exhibited by `PolyTimeDecidable`, packaged so that a proof of
`InNP L` hands the Cook-Levin reduction an *actual machine* to build a tableau
for.  This is what lets `cook_levin_nphard` construct its reduction without
ever consulting `L` itself. -/
structure VerifierMachine (V : List Bool → List Bool → Bool) where
  /-- The machine computing the verdict. -/
  M : Machine
  /-- Its number of tapes. -/
  k : Nat
  /-- Its alphabet size. -/
  G : Nat
  /-- Leading coefficient of the time bound. -/
  c : Nat
  /-- Degree of the time bound. -/
  d : Nat
  /-- `M` is a well-formed `k`-tape machine over an alphabet of size `G`. -/
  wf : TuringMachine k G M
  /-- `M` decides `V` within the step bound. -/
  decides : ∀ x w : List Bool,
    DecidesIn M k (boolsToSymbols x) (boolsToSymbols w)
      (polyBound c d (x.length + w.length)) (V x w)

theorem PolyTimeDecidable.nonempty {V : List Bool → List Bool → Bool}
    (h : PolyTimeDecidable V) : Nonempty (VerifierMachine V) := by
  obtain ⟨M, k, G, c, d, hwf, hdec⟩ := h
  exact ⟨⟨M, k, G, c, d, hwf, hdec⟩⟩

theorem VerifierMachine.polyTimeDecidable {V : List Bool → List Bool → Bool}
    (vm : VerifierMachine V) : PolyTimeDecidable V :=
  ⟨vm.M, vm.k, vm.G, vm.c, vm.d, vm.wf, vm.decides⟩

/-- Membership of `L` in NP: a polynomial-time verifier whose accepted
certificates characterise `L`. -/
def InNP (L : Language) : Prop :=
  ∃ (V : List Bool → List Bool → Bool) (c d : Nat),
    IsNPVerifier c d V ∧ ∀ x : List Bool, InLang x L ↔ ∃ w : List Bool, V x w = true

/-- `L` is NP-hard if every language in NP polynomial-time reduces to it. -/
def NPHard (L : Language) : Prop :=
  ∀ L' : Language, InNP L' → L' ≤p L

/-- `L` is NP-complete if it is in NP and NP-hard. -/
def NPComplete (L : Language) : Prop := InNP L ∧ NPHard L

end CookLevin
