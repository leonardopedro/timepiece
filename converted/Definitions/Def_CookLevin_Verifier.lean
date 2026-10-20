/-
prove2.me platform library module `Definitions.Def_CookLevin_Verifier`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_CookLevin_Verifier.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_CookLevin_Complexity
set_option autoImplicit true
/-
  CookLevinLean/Verifier.lean

  The SAT verifier, and the fact that it verifies SAT.

  The previous version of this file defined

      noncomputable def satVerifier (x w : List Bool) : Bool :=
        decide (w.length ≤ 2) && decide (SAT x)

  which decides SAT by *calling* SAT.  The verifier below never mentions `SAT`
  or `Satisfiable`: it decodes `x` into a CNF formula with `decodeFormula`,
  decodes the certificate `w` into a truth assignment, and evaluates the one
  against the other with `satisfiesB`.  It is computable (no `Classical`,
  no `noncomputable`) and `#eval`-able.
-/



namespace CookLevin

/-! ## Decoding a certificate into an assignment -/

/-- Decode a certificate into a truth assignment: bit `n` of `w` gives the
value of variable `n`, and variables beyond the end of `w` are `false`. -/
def decodeAssignment (w : List Bool) : Assignment := fun n => w.getD n false

theorem decodeAssignment_range {N : Nat} (α : Assignment) {n : Nat} (hn : n < N) :
    decodeAssignment ((List.range N).map α) n = α n := by
  have hlen : ((List.range N).map α).length = N := by simp
  unfold decodeAssignment
  rw [List.getD_eq_getElem?_getD, List.getElem?_map, List.getElem?_range hn]
  rfl

/-! ## Recognising well-formed instances

`SAT` contains every string that is *not* a valid encoding of a formula, so a
verifier for `SAT` has to recognise those.  Decoding and re-encoding does it,
and both halves are polynomial-time. -/

/-- Decidable test for "`x` encodes a formula". -/
def isFormulaStringB (x : List Bool) : Bool :=
  decide (encodeFormula (decodeFormula x) = x)

theorem isFormulaStringB_eq_true_iff (x : List Bool) :
    isFormulaStringB x = true ↔ IsFormulaString x := by
  unfold isFormulaStringB IsFormulaString
  simp only [decide_eq_true_eq]
  constructor
  · intro h
    exact ⟨decodeFormula x, h.symm⟩
  · rintro ⟨φ, rfl⟩
    rw [decodeFormula_encodeFormula]

/-! ## The verifier -/

/-- The SAT verifier.

The certificate is a truth assignment, given as at most `|x|` bits.

* `x` must encode a formula `φ` — strings encoding nothing are not in `SAT`
  and are rejected outright;
* the assignment the certificate encodes must satisfy `φ`.

Both the decoding of `φ` and the evaluation are ordinary list computations.
Note what is *absent*: no occurrence of `SAT`, of `Satisfiable`, or of any
classical choice. -/
def satVerifier (x w : List Bool) : Bool :=
  isFormulaStringB x && decide (w.length ≤ x.length) &&
    satisfiesB (decodeAssignment w) (decodeFormula x)

/-- Accepted certificates have length at most `polyBound 1 1 |x| = |x| + 1`. -/
theorem satVerifier_length {x w : List Bool} (h : satVerifier x w = true) :
    w.length ≤ polyBound 1 1 x.length := by
  unfold satVerifier at h
  simp only [Bool.and_eq_true, decide_eq_true_eq] at h
  rw [show polyBound 1 1 x.length = x.length + 1 by simp [polyBound]]
  omega

/-- **The verifier really verifies SAT.**  Derived from `Satisfies`/`satisfiesB`
and the encoding round-trip, with no appeal to `SAT` inside `satVerifier`. -/
theorem satVerifier_correct (x : List Bool) :
    SAT x ↔ ∃ w : List Bool, satVerifier x w = true := by
  by_cases hx : IsFormulaString x
  · obtain ⟨φ, rfl⟩ := hx
    have hdec : decodeFormula (encodeFormula φ) = φ := decodeFormula_encodeFormula φ
    have hform : isFormulaStringB (encodeFormula φ) = true :=
      isFormulaStringB_eq_true_iff _ |>.mpr ⟨φ, rfl⟩
    rw [SAT_encodeFormula_iff]
    constructor
    · rintro ⟨α, hα⟩
      -- spell `α` out on the variables of `φ`; they all fit below `|x|`
      refine ⟨(List.range (assignmentBound φ)).map α, ?_⟩
      unfold satVerifier
      rw [hdec, hform]
      have hlen : ((List.range (assignmentBound φ)).map α).length ≤ (encodeFormula φ).length := by
        rw [show ((List.range (assignmentBound φ)).map α).length = assignmentBound φ by simp]
        exact assignmentBound_le_length_encodeFormula φ
      simp only [Bool.and_eq_true, decide_eq_true_eq, true_and]
      refine ⟨hlen, ?_⟩
      rw [satisfiesB_eq_true_iff]
      refine (satisfies_congr
        (β := decodeAssignment ((List.range (assignmentBound φ)).map α)) ?_).mp hα
      intro n hn
      exact (decodeAssignment_range α (lt_assignmentBound hn)).symm
    · rintro ⟨w, hw⟩
      unfold satVerifier at hw
      rw [hdec] at hw
      simp only [Bool.and_eq_true] at hw
      exact ⟨decodeAssignment w, (satisfiesB_eq_true_iff _ _).mp hw.2⟩
  · have hform : isFormulaStringB x = false := by
      cases hb : isFormulaStringB x
      · rfl
      · exact absurd ((isFormulaStringB_eq_true_iff x).mp hb) hx
    constructor
    · intro h
      exact absurd h (not_SAT_of_not_formulaString hx)
    · rintro ⟨w, hw⟩
      unfold satVerifier at hw
      rw [hform] at hw
      simp at hw

/-- `satVerifier` meets the certificate-length requirement of `IsNPVerifier`
and characterises `SAT`; what remains for `InNP SAT` is a Turing machine that
evaluates it within a polynomial number of steps. -/
theorem satVerifier_isNPVerifier (h : PolyTimeDecidable satVerifier) :
    IsNPVerifier 1 1 satVerifier :=
  ⟨h, fun _ _ hw => satVerifier_length hw⟩

end CookLevin
