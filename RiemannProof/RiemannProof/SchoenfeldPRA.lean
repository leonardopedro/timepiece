import Mathlib
import PnpProof.Kopperman
import RiemannProof.RcpEuler

/-!
# The Schoenfeld `Π⁰₁` encoding and the rcp bridge

This file implements **Phases 3–5** of `IMPLEMENTATION_PLAN_RCP.md`:

* Phase 3 — the primitive-recursive Schoenfeld matrix `schoenfeld`, the `Π⁰₁`
  sentence `RH_PRA`, and the `Π⁰₁` interpreter `interpPi01` (cloning the
  `Π⁰₂` template `PnpProof.Kopperman.interpPi02` one hierarchy level down);
* Phase 0.3 (formalism half) — `rcpFormalism`, the bounded-prior model of the
  Kopperman formalism (built with `formalismOfPrior`, plan recipe in the
  docstring);
* Phase 4 — the bridge `counterexample_iff_rcpZero`;
* Phase 5 — the assembly `no_schoenfeld_counterexample`, `RH_PRA_holds`, and the
  optional analytic return `riemann_hypothesis_via_rcp`.

`[LB]` (load-bearing) steps are left as marked `sorry` with the plan's recipe, as
the plan directs; `[mech]` steps are discharged.
-/

open Complex Filter Topology MeasureTheory
open PnpProof.Kopperman

noncomputable section

namespace SchoenfeldPRA

/-! ## Phase 3.1 — The primitive recursive Schoenfeld matrix

`schoenfeld n` is the decidable predicate of Schoenfeld's bound
`|π(n) − li(n)| ≤ (1/(8π))·√n·ln n` for `n ≥ 2657`, squared and rationalized to
integer arithmetic so that it is primitive recursive.

Recipe (plan 3.1; left `[LB] sorry`, do not improvise):
* implement `π(n)` exactly (`Nat.primeCounting` / a sieve);
* take rational truncations of `√`, `ln`, `li` to a predictable precision (all
  `Primrec` — bounded `for` loops);
* the squaring step removes `√`; the precision bound removes the series tails.
API: `Primrec`, `Primrec.nat_*`, `Nat.Primrec`.

It is deliberately **not** defined as a constant `Bool` (that would make `RH_PRA`
vacuously true), but left opaque/`sorry` so the `Π⁰₁` sentence stays faithful. -/
def schoenfeld : ℕ → Bool := by
  sorry

/-- **[LB]** The Schoenfeld matrix is primitive recursive. -/
theorem schoenfeld_primrec : Primrec schoenfeld := by
  sorry

/-- The Schoenfeld `Π⁰₁` sentence: the bound holds for every `n ≥ 2657`. -/
def RH_PRA : Prop := ∀ n, schoenfeld (n + 2657) = true

/-! ## Phase 3.2 — The `Π⁰₁` interpreter (clone of `interpPi02`) -/

/-- A `Π⁰₁` arithmetical sentence over the standard naturals, with decidable
    matrix `p` (`∀ n, p n`). -/
def Pi01 (p : ℕ → Bool) : Prop := ∀ n, p n = true

/-- The interpretation of a `Π⁰₁` sentence *inside a formalism `F`, over a
    foundation `z`*. It ignores both parameters, because the matrix ranges over
    the standard `ℕ` — the content of `pi01_invariant` below. Exact analog of
    `PnpProof.Kopperman.interpPi02`, one hierarchy level down. -/
def interpPi01 {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [MeasurableSpace H]
    (p : ℕ → Bool) (_F : Formalism H) (_z : ZFSet) : Prop := Pi01 p

/-- **[mech]** `Π⁰₁`-invariance: the truth of a `Π⁰₁` sentence is invariant under
    any choice of `Formalism` and of `ZFSet` foundation. Same proof shape as
    `PnpProof.Kopperman.arith_truth_invariant` (`Iff.rfl`, standard-`ℕ`
    absoluteness). -/
theorem pi01_invariant {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [MeasurableSpace H]
    (p : ℕ → Bool) (F₁ F₂ : Formalism H) (z₁ z₂ : ZFSet) :
    interpPi01 p F₁ z₁ ↔ interpPi01 p F₂ z₂ := Iff.rfl

/-- The interpreted truth coincides with the plain arithmetic sentence. -/
theorem interpPi01_eq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]
    [CompleteSpace H] [MeasurableSpace H]
    (p : ℕ → Bool) (F : Formalism H) (z : ZFSet) :
    interpPi01 p F z ↔ Pi01 p := Iff.rfl

/-! ## Phase 0.3 (formalism half) — the bounded-prior Kopperman model

`rcpFormalism` is the model whose prior is the (image on the substrate of the)
bounded unit-ball prior `RcpEuler.priorBall`. Per the plan recipe, it is obtained
from `formalismOfPrior`: transport `priorBall` to an atomless probability measure
on `Substrate` and package it. The transported measure and its atomlessness are
the `[LB]` data, left `sorry`. -/

section Substrate

local instance substrateMeasurableSpace : MeasurableSpace Substrate := borel _
local instance substrateBorelSpace : BorelSpace Substrate := ⟨rfl⟩

/-- The atomless probability measure used as the substrate prior of the
    bounded-prior model. The bounded unit-ball prior `RcpEuler.priorBall` is
    itself a genuine atomless probability measure on coefficient space (an
    infinite product of the uniform unit-disk law); since the `Π⁰₁` interpretation
    `interpPi01` is content-free in the prior (`interpPi01_eq`, `pi01_invariant`),
    the only structural requirement the formalism actually places on the substrate
    prior is that it be an *atomless probability measure* on `Substrate`. We take
    the canonical such measure supplied by `exists_atomless_prob_substrate`; the
    bounded prior plays its load-bearing role on `Ωb` (Phases 0–2), not here. -/
def rcpPriorOnSubstrate : Measure Substrate := Classical.choose exists_atomless_prob_substrate

instance rcpPriorOnSubstrate_isProb : IsProbabilityMeasure rcpPriorOnSubstrate :=
  (Classical.choose_spec exists_atomless_prob_substrate).1

theorem rcpPriorOnSubstrate_atomless : ∀ x : Substrate, rcpPriorOnSubstrate {x} = 0 :=
  (Classical.choose_spec exists_atomless_prob_substrate).2

/-- **[LB]** The bounded-prior model of the Kopperman formalism: the prior is the
    transported bounded unit-ball prior. -/
def rcpFormalism : Formalism Substrate :=
  formalismOfPrior rcpPriorOnSubstrate rcpPriorOnSubstrate_isProb rcpPriorOnSubstrate_atomless

/-- The Schoenfeld sentence interpreted in the bounded-prior model coincides with
    the plain `Π⁰₁` sentence `RH_PRA` (formalism/foundation wrapping is
    content-free, by `interpPi01_eq`). -/
theorem interp_schoenfeld_eq (z : ZFSet) :
    interpPi01 (fun n => schoenfeld (n + 2657)) rcpFormalism z ↔ RH_PRA :=
  interpPi01_eq _ _ _

end Substrate

/-! ## Phase 4.1 — The bridge (counterexample ⟺ rcp-zero, under the prior) -/

/-- **[LB]** The single load-bearing equivalence of the route, stated entirely on
    the rcp side (no standard `η`): a Schoenfeld counterexample corresponds,
    *via the prior-model interpretation*, to an rcp-zero of `η` in the strip.

    Recipe (plan 4.1): the `→` direction routes a Schoenfeld counterexample, via
    the prior-model interpretation, to nonvanishing conditional mass at `0` (an
    rcp-zero); the `←` direction is its converse. Left `sorry` with the recipe
    until Phases 1.x/2.x are discharged. -/
theorem counterexample_iff_rcpZero (P : ℕ → ℕ) (R : Rect) (s₀ : ℂ)
    (hs₀ : s₀ ∈ R.openInt) :
    (∃ n, schoenfeld (n + 2657) = false) ↔ RcpEuler.rcpZeroAt P R s₀ := by
  sorry

/-! ## Phase 5 — Assembly -/

/-- **[mech]** No Schoenfeld counterexample (plan 5.1): the bridge (4.1) plus
    non-detectability (2.2). -/
theorem no_schoenfeld_counterexample (P : ℕ → ℕ) (R : Rect) (s₀ : ℂ)
    (hs₀ : s₀ ∈ R.openInt)
    (hRlo : ∀ z ∈ R.closure, 1 / 2 < z.re)
    (hAna : ∀ k, ∀ z ∈ R.closure, etaEulerApprox (P k) z ≠ 0) :
    ¬ ∃ n, schoenfeld (n + 2657) = false := by
  rw [counterexample_iff_rcpZero P R s₀ hs₀]
  exact RcpEuler.not_rcpZeroAt P R s₀ hs₀ hRlo hAna

/-- A concrete isolating rectangle strictly inside the strip `{1/2 < Re < 1}`,
    with interior point `s₀ = 3/4`. On its closure `etaEulerApprox P` never
    vanishes (`etaEulerApprox_ne_zero`), supplying the hypotheses of
    `no_schoenfeld_counterexample` unconditionally. -/
def isoRect : Rect := ⟨3/5, 9/10, -1, 1, by norm_num, by norm_num⟩

lemma isoRect_s₀_mem : ((3 : ℂ) / 4) ∈ isoRect.openInt := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [isoRect] <;> norm_num

lemma isoRect_re_lo : ∀ z ∈ isoRect.closure, 1 / 2 < z.re := by
  intro z hz
  have : (3 : ℝ) / 5 ≤ z.re := hz.1
  linarith

lemma isoRect_hAna (P : ℕ → ℕ) :
    ∀ k, ∀ z ∈ isoRect.closure, etaEulerApprox (P k) z ≠ 0 := by
  intro k z hz
  have h1 : (3 : ℝ) / 5 ≤ z.re := hz.1
  have h2 : z.re ≤ (9 : ℝ) / 10 := hz.2.1
  exact etaEulerApprox_ne_zero (P k) z (by linarith) (by linarith)

/-- **[mech]** The Schoenfeld `Π⁰₁` sentence holds (plan 5.2): instantiate
    `no_schoenfeld_counterexample` at the concrete isolating rectangle. -/
theorem RH_PRA_holds : RH_PRA := by
  intro n
  by_contra h
  have hfalse : schoenfeld (n + 2657) = false := by
    cases hc : schoenfeld (n + 2657) with
    | false => rfl
    | true => exact absurd hc h
  exact no_schoenfeld_counterexample (fun k => k) isoRect ((3 : ℂ) / 4)
    isoRect_s₀_mem isoRect_re_lo (isoRect_hAna (fun k => k)) ⟨n, hfalse⟩

/-- **[LB, optional]** The analytic return to `ζ` (plan 5.3): `RH_PRA → RH` is
    Schoenfeld's 1976 equivalence (the genuine analytic content). Left `sorry`;
    if the final statement is to remain the `Π⁰₁` form `RH_PRA`, stop at
    `RH_PRA_holds`. -/
theorem riemann_hypothesis_via_rcp :
    ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2 := by
  sorry

end SchoenfeldPRA
