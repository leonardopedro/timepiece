/-
prove2.me platform library module `Definitions.Def_InteractiveConsistency_Impossibility_Construction`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_InteractiveConsistency_Impossibility_Construction.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_InteractiveConsistency_Impossibility_Scenario

namespace InteractiveConsistency.Impossibility

/-- The three scenarios `α`, `β`, `σ` of the proof of the THEOREM (p. 232). -/
inductive Which
  | alpha
  | beta
  | sigma
  deriving DecidableEq

/-- `true` iff the string `s` is nonempty and its last letter (the originator) lies in `C`. -/
def lastIn {α : Type*} [DecidableEq α] (C : Finset α) (s : List α) : Bool :=
  s.getLast?.any (fun c => decide (c ∈ C))

/-- The recursion (i)–(iii) of p. 232, on nonempty strings, for a partition `A, B, C` of `P` and
values `v, v'`. Each letter `a`, `b`, `c` of the page ranges over `A`, `B`, `C` independently.

* (i) a string not ending in a member of `C` gets `v` in all three scenarios;
* (ii) strings of length one or two ending in `c ∈ C`:
  `α(c) = α(ac) = α(bc) = α(cc) = v`, `β(c) = β(ac) = β(bc) = β(cc) = v'`,
  `σ(c) = σ(ac) = σ(cc) = v`, `σ(bc) = v'`;
* (iii) for `p ∈ P` and `w` ending in a member of `C` (here `y :: z :: w` has length at least two):
  `α(paw) = α(aw)`, `α(pbw) = β(bw)`, `α(pcw) = α(cw)`;
  `β(paw) = α(aw)`, `β(pbw) = β(bw)`, `β(pcw) = β(cw)`;
  `σ(paw) = σ(aw)`, `σ(pbw) = σ(bw)`, `σ(acw) = α(cw)`, `σ(bcw) = β(cw)`.

The page leaves `σ(c'cw)` (`c, c' ∈ C`, `w ≠` empty) unspecified; it is set here to `σ(cw)`.
The empty string, which is not in `P⁺`, gets `v`. -/
def core {α V : Type*} [DecidableEq α] (A B C : Finset α) (v v' : V) : Which → List α → V
  | _, [] => v
  | .alpha, [_] => v
  | .beta, [x] => if x ∈ C then v' else v
  | .sigma, [_] => v
  | .alpha, [_, _] => v
  | .beta, [_, y] => if y ∈ C then v' else v
  | .sigma, [x, y] => if y ∈ C then (if x ∈ B then v' else v) else v
  | .alpha, _ :: y :: z :: w =>
      if lastIn C (z :: w) then
        (if y ∈ B then core A B C v v' .beta (y :: z :: w)
          else core A B C v v' .alpha (y :: z :: w))
      else v
  | .beta, _ :: y :: z :: w =>
      if lastIn C (z :: w) then
        (if y ∈ A then core A B C v v' .alpha (y :: z :: w)
          else core A B C v v' .beta (y :: z :: w))
      else v
  | .sigma, p :: y :: z :: w =>
      if lastIn C (z :: w) then
        (if y ∈ C then
          (if p ∈ A then core A B C v v' .alpha (y :: z :: w)
            else if p ∈ B then core A B C v v' .beta (y :: z :: w)
            else core A B C v v' .sigma (y :: z :: w))
          else core A B C v v' .sigma (y :: z :: w))
      else v

/-- The scenario `k ∈ {α, β, σ}` of p. 232 as a total function on `List α`: on strings over `P`
it is given by the recursion `core`; on strings with a letter outside `P` (which are not in `P⁺`
and are never constrained) all three scenarios take the same value `v`. -/
def scen {α V : Type*} [DecidableEq α] (P A B C : Finset α) (v v' : V) (k : Which)
    (s : List α) : V :=
  if IsString P s then core A B C v v' k s else v

/-- The scenario `α` of p. 232. -/
abbrev alphaScen {α V : Type*} [DecidableEq α] (P A B C : Finset α) (v v' : V) : List α → V :=
  scen P A B C v v' .alpha

/-- The scenario `β` of p. 232. -/
abbrev betaScen {α V : Type*} [DecidableEq α] (P A B C : Finset α) (v v' : V) : List α → V :=
  scen P A B C v v' .beta

/-- The scenario `σ` of p. 232. -/
abbrev sigmaScen {α V : Type*} [DecidableEq α] (P A B C : Finset α) (v v' : V) : List α → V :=
  scen P A B C v v' .sigma

end InteractiveConsistency.Impossibility
