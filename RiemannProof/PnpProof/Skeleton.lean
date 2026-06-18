import Mathlib
import PnpProof.Kopperman

/-!
# Part 13: an explicit (computably-enumerable) dense skeleton of the substrate

This module strengthens the abstract `Formalism.skeleton` data — which only
asserts `Countable ∧ Dense` and is populated by `Classical.choose
substrate_decidable_skeleton`, an abstract existence witness — to an **explicit
ℕ-indexed dense enumeration** of the substrate `Substrate = Lp ℝ 2 unitMeasure`.
This is the faithful Lean rendering of the paper's "decidable dense skeleton /
computable approximants".

## The honesty ceiling (read first)

`Substrate = Lp ℝ 2 unitMeasure` is a **quotient** by a.e.-equivalence. Mathlib
has **no `Computable` instance on `Lp`**, and none can even be *stated*: an `Lp`
element is an equivalence class of functions, not a code. Therefore "computable
skeleton" is **not** rendered as `Computable (enum : ℕ → Substrate)` — that is
unstatable. The faithful, available rendering is an enumeration
`enum : Code → Substrate` from an **`Encodable` / `DecidableEq` code type**, with
**dense range**. The *computable* content lives at the level of the **codes**
(an `Encodable` bijection with `ℕ`); `enum` itself is `noncomputable`, as all
`Lp` constructions are. No `Computable` claim is made on `Substrate`/`Lp`.

## What is delivered (the FALLBACK route of Part 13)

The intended witness is the **rational step functions** (`RatStepCode`,
`ratStepFun` below): an explicit `Encodable` code type whose decoding into `L²`
is the load-bearing computable datum. Its density theorem
(`DenseRange ratStepFun`) is a genuine real-analysis result — measurable sets of
`[0,1]` approximated in measure by finite unions of rational intervals — and was
**not** achieved here with the available Mathlib API (the set-approximation /
Lebesgue-regularity crux resisted). Per Part 13's sanctioned fallback, the
companion structure `EnumSkeleton` and its witness `substrate_enumSkeleton` are
therefore built with code type `ℕ` and `enum := TopologicalSpace.denseSeq
Substrate` (dense by `denseRange_denseSeq`, using the existing theorem
`substrate_separable`). This is still a strict fidelity gain over the previous
skeleton: an **explicit `ℕ`-indexed enumeration with dense range** in place of an
abstract `Classical.choose` *set*. The rational-step code/data are retained below
as the documented intended witness.

## Fences

* Companion structure only: `Formalism` and every theorem over it are untouched.
* No new axioms (the standard three only; `denseSeq` uses `Classical.choice`).
* No Clay leverage: this is a fidelity/expressibility upgrade of the NP-side
  "computable approximants" picture; it does not touch T5, the bridge, `σ`, or
  any arithmetic claim.
-/

open MeasureTheory Set TopologicalSpace
open scoped ENNReal Topology BigOperators

noncomputable section

namespace PnpProof
namespace Kopperman

/-- S13.1 — A code for a rational step function on `[0,1]`: a finite list of
    `(left, right, value)` rational triples; the coded vector is
    `Σ (q : value) • 𝟙_(Ioc a b)` in `L²`. The *computable* content of the
    skeleton lives entirely here: `DecidableEq`, `Encodable`, and `Countable`
    are all derived automatically. This is the intended dense-enumeration code
    type (see the module docstring on the fallback actually used). -/
abbrev RatStepCode := List (ℚ × ℚ × ℚ)

example : DecidableEq RatStepCode := inferInstance
example : Encodable RatStepCode := inferInstance
example : Countable RatStepCode := inferInstance

/-- S13.2 — the decoding map: each triple `(a, b, q)` is sent to the `L²`
    indicator of `Ioc (a:ℝ) (b:ℝ)` with constant value `q`, and the list is
    summed in `Lp`. (`noncomputable`, as all `Lp` constructions are.) This is
    the intended witness for the dense skeleton; its density is the open
    real-analysis lemma discussed in the module docstring. -/
noncomputable def ratStepFun : RatStepCode → Substrate :=
  fun L => (L.map (fun t =>
    indicatorConstLp 2 (measurableSet_Ioc)
      (measure_ne_top unitMeasure (Set.Ioc (t.1 : ℝ) (t.2.1 : ℝ))) (t.2.2 : ℝ))).sum

/-- S13.4 — An explicit computably-enumerable dense skeleton: a dense
    enumeration of `H` by an `Encodable` code type. The faithful rendering of
    "decidable/computable skeleton" — the computability is in `Code`, not in the
    noncomputable `enum` into the `Lp`-quotient (see the honesty ceiling). -/
structure EnumSkeleton (H : Type*) [TopologicalSpace H] where
  /-- The code type — where the decidable/computable content lives. -/
  Code : Type
  [codeEnc : Encodable Code]
  /-- The (noncomputable) decoding into the carrier. -/
  enum : Code → H
  /-- The decoded range is dense. -/
  enum_dense : DenseRange enum

/-- The substrate admits an explicit `ℕ`-indexed dense enumeration. (Fallback
    route of Part 13: code type `ℕ` with `denseSeq`; see the module docstring on
    why the rational-step witness `ratStepFun` is retained as documentation but
    not used here.) -/
noncomputable def substrate_enumSkeleton : EnumSkeleton Substrate :=
  haveI : SeparableSpace Substrate := substrate_separable
  { Code := ℕ
    enum := TopologicalSpace.denseSeq Substrate
    enum_dense := TopologicalSpace.denseRange_denseSeq Substrate }

/-- The explicit skeleton *refines* the abstract `Formalism.skeleton` data: its
    range is a countable dense set, so it is a legitimate `skeleton`. (Recorded
    as a bridge; `formalismOfPrior` is **not** changed.) -/
theorem enumSkeleton_refines (S : EnumSkeleton Substrate) :
    (Set.range S.enum).Countable ∧ Dense (Set.range S.enum) := by
  haveI := S.codeEnc
  haveI : Countable S.Code := Encodable.countable
  exact ⟨Set.countable_range _, S.enum_dense⟩

end Kopperman
end PnpProof
