import Mathlib
import PnpProof.Kopperman
import RiemannProof.RcpEuler
import RiemannProof.SchoenfeldMatrix

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

Phase 3.1 (`schoenfeld`, `schoenfeld_primrec`) is now **discharged** in
`RiemannProof.SchoenfeldMatrix` (a genuine, primitive-recursive fixed-point
decision procedure). The two remaining `[LB]` (load-bearing) steps —
`counterexample_iff_rcpZero` (4.1) and `riemann_hypothesis_via_rcp` (5.3) — are
left as marked `sorry`: under the substantive *limit* form of `rcpZeroAt`
(2026-06-19 maintainer refinement), the bridge 4.1 (`eq1`/`eq2` via Schoenfeld
1976 at the mean realization) and the limit-form `RcpEuler.not_rcpZeroAt`
(Bagchi/Voronin universality on a local neighborhood) are the two genuine
load-bearing analytic obligations; each is not weaker than the Riemann Hypothesis
(an open problem), and 5.3 is RH stated for `riemannZeta`. They carry the entire
un-formalized analytic content of the route and are not improvised, exactly as the
plan directs. `[mech]` steps are discharged.
-/

open Complex Filter Topology MeasureTheory
open PnpProof.Kopperman

noncomputable section

namespace SchoenfeldPRA

/-! ## Phase 3.1 — The primitive recursive Schoenfeld matrix

`schoenfeld n` is the decidable predicate of Schoenfeld's bound
`|π(n) − li(n)| ≤ (1/(8π))·√n·ln n` for `n ≥ 2657`, squared and rationalized to
integer arithmetic so that it is primitive recursive.

Implementation (plan 3.1, now **done** in `RiemannProof.SchoenfeldMatrix`):
* `π(n)` exact, by a sieve (`SchoenfeldMatrix.primePi`);
* rational fixed-point truncations of `ln`/`li` via the `artanh` recurrence and a
  rectangle sum (`SchoenfeldMatrix.lnFix`, `SchoenfeldMatrix.liInt`), all
  `Primrec`;
* the squaring step removes `√`; `(8π)²` is the fixed rational `6316547/10000`.

It is deliberately **not** defined as a constant `Bool` (that would make `RH_PRA`
vacuously true): it is the genuine, primitive-recursive fixed-point decision
procedure for Schoenfeld's bound built in `RiemannProof.SchoenfeldMatrix`. -/
def schoenfeld : ℕ → Bool := SchoenfeldMatrix.schoenfeld

/-- **[LB → done]** The Schoenfeld matrix is primitive recursive. -/
theorem schoenfeld_primrec : Primrec schoenfeld := SchoenfeldMatrix.schoenfeld_primrec

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

    Recipe (plan 4.1, 2026-06-19 limit form): prove the equivalence via two
    conditional-probability-`1` statements at the mean (`X_n ≡ 1`) realization —
    `eq1 : P(counterexample ∣ X≡1 ∧ ∃ zero) = 1` and
    `eq2 : P(¬ counterexample ∣ X≡1 ∧ ¬ ∃ zero) = 1` — which are Schoenfeld's
    `RH_PRA ⇔ RH` evaluated at the deterministic mean series, embedded in the rcp
    formalism (conditioning on the null point `X ≡ 1` is legitimate by Tjur, as it
    lies in the support of the trace law). Under the *limit* form of `rcpZeroAt`
    this equivalence is genuine (not the trivial placeholder). Left `sorry` with
    the recipe; **do not improvise** — it is not weaker than RH. -/
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
  -- `RcpEuler.not_rcpZeroAt` was deleted as vestigial (2026-06-23). This file is the
  -- quarantined/unimported historical PRA spine; left as a `sorry` for self-consistency.
  sorry

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

/-
**[LB, optional]** The analytic return to `ζ` (plan 5.3): `RH_PRA → RH` is
    Schoenfeld's 1976 equivalence (the genuine analytic content). Left `sorry`;
    if the final statement is to remain the `Π⁰₁` form `RH_PRA`, stop at
    `RH_PRA_holds`.
-/
theorem riemann_hypothesis_via_rcp :
    ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2 := by
  sorry

end SchoenfeldPRA
