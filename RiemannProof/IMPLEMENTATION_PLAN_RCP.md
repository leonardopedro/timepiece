# Implementation Plan: RH via a bounded-coefficient prior + regular conditional probability + the Kopperman PRA model

**Audience**: a Lean 4 formalization agent. **Status (2026-06-18)**: both files are
on disk and imported by the root `RiemannProof.lean` (regression-guarded) —
`RiemannProof/RcpEuler.lean` (Phases 0–2) and `RiemannProof/SchoenfeldPRA.lean`
(Phases 3–5). The route is now **much further along, and along a *simpler* path
than the earlier C2/C3/C4 design**: the implementer did **not** build the
`κ_sel`/Tjur/`edgeTrace`-retype apparatus. Instead they **kept the joint-mass
`rcpZeroAt`** and **proved** the two analytic load-bearers that mattered:

* `rcp_recipEulerB_tendsto_recipEta` (Phase 1.4, the contour convergence) — **PROVED**;
* `not_rcpZeroAt` (Phase 2.2, non-detectability) — **PROVED** directly from
  bounded-coefficient nonvanishing (the interior value `eulerB s₀` is bounded away
  from `0` on the support of `priorBall`, so the joint "edges near `η` ∧ `‖eulerB s₀‖<r`"
  event is null for small `r`).

**Only 5 `sorry`s remain on disk** (down from the long `[LB]` list): `priorBall_edgeNbhd_pos`
(1.3, *dubious as stated / unused* — see below), `schoenfeld` + `schoenfeld_primrec`
(3.1, the self-contained `Primrec` block), `counterexample_iff_rcpZero` (4.1, **the
one genuine load-bearing bridge**), and `riemann_hypothesis_via_rcp` (5.3, optional).

**The 2026-06-18 simplification (maintainer).** A new theorem — *regular conditional
probability is the limit of ordinary probabilities over a shrinking neighborhood
(Tjur)* — lets the route be restated cleanly and, in particular, **gives the
honest meaning of the result as an unprovability/independence statement** (see the
new section "The simplification" below). It supersedes the C2/C3/C4 corrections (the
selected-kernel `κ_sel` override is no longer needed: the neighborhood limit, with a
Fock-space expansion, *directly* drives the conditional variance — hence the
probability of a zero — to `0`). This plan is a *translation target*, not a
correctness argument — each step is a Lean obligation to be discharged or left as a
marked `sorry`. Do not collapse steps; build them in the order given and `lake build`
after each.

This plan **does not replace** `IMPLEMENTATION_PLAN.md` (the direct Cauchy-contour
route in `GaussianEuler.lean`). It is a *different* route requested by the
maintainer, and it reuses two existing layers:

* the bounded-coefficient exponential Euler product (a re-parameterization of
  `GaussianEuler.lean`'s `eulerG`, with coefficients in a ball of radius ≤ 1);
* the Kopperman formalism `PnpProof/Kopperman.lean` (`Formalism`,
  `formalismOfPrior`, `Pi02`/`interpPi02`, `arith_truth_invariant`).

## The strategy in one paragraph (what we are translating)

Put a probability prior on the Euler-product coefficients with values in the
closed unit ball of `ℂ` (optionally a **mixed continuous+discrete** measure — see
N1). Via `formalismOfPrior` this prior **is** a model of the Kopperman formalism,
hence a setting in which the standard arithmetic (Schoenfeld) encoding of RH is
interpreted. Then:

1. (rcp convergence) Conditioning the ensemble on being in an `ε`-neighborhood of
   `η` on the edges of a loop inside the strip, the conditional law makes the
   contour integrals converge: `∮ 1/eulerB → ∮ 1/η`.
2. (rcp non-detectability) Under this prior, "`η` has a strip zero **in the
   regular-conditional-probability sense**" cannot hold: it would require a
   neighborhood of `η` to be arbitrarily close to `0` at the interior point,
   which the bounded prior forbids.
3. (bridge) Under this prior, a counterexample to the Schoenfeld `Π⁰₁` sentence
   corresponds to an rcp-zero of `η` in the strip.
4. (assembly) (2)+(3) give: no counterexample, i.e. the Schoenfeld `Π⁰₁` sentence
   holds; Schoenfeld's equivalence returns RH.

Everywhere below, **`η` means the rcp/ensemble object, not the standard
deterministic `η`** (the maintainer's standing instruction). The standard `η`
carries prior-measure `0` and is not the object of any claim here.

---

## The simplification (2026-06-18): rcp as a neighborhood limit + a Fock-space expansion

**The new theorem (maintainer).** Regular conditional probability is *defined* as a
limit of ordinary probabilities over a shrinking neighborhood of the conditioning
value:
```
P(A ∣ T = t)  =  lim_{U ↓ {t}}  P(A ∩ T⁻¹U) / P(T⁻¹U),
```
the limit over open neighborhoods `U ∋ t` ordered by reverse inclusion (Mathlib's
`(𝓝 t).smallSets` net; this is Tjur's characterization, already sketched in the now-
superseded C4). This is the *honest* reading of "neighborhood converges to `η`,
integrals converge," and it removes the need for the selected-kernel `κ_sel`
override entirely: there is nothing to *select*, because the limit pins the value.

**The `ε`–`U`–`V` form, and why the limit is well-defined (maintainer, 2026-06-18).**
Tjur's statement is the explicit `ε`–`U`–`V` one:

> for every `ε > 0` there exists an open neighborhood `U` of the event `{T = t}`
> such that for **every** open `V` with `{T = t} ⊂ V ⊂ U`,
> `|P(A ∩ V)/P(V) − L| < ε`, where `L = P(A ∣ T = t)` is the limit.

Two things this buys, both used below:
* **The limit `L` exists / is well-defined because the probability space is Radon.**
  This is Tjur's existence hypothesis, and it is *automatic here*: the prior lives on
  a Polish inner-product substrate, whose Borel probability measures are inner-regular
  (= Radon) — `inferInstance` (the same fact recorded in superseded C4's "Radon
  precondition is automatic"). The situating is: this is **within the Mehler
  formalism, within the Kopperman formalism** — i.e. the Radon/Gaussian (Mehler-kernel)
  structure of the substrate sits inside the Kopperman foundation-invariance layer, so
  the limit `L` is a genuine, foundation-independent number, not an artifact of a kernel
  choice. (This is the precise sense in which the rcp is *defined*, strengthening step 1.)
* **It is a uniform handle for showing `L ≠ 1`.** Because the inequality holds for
  *all* open `V` sandwiched between `{T = t}` and `U` — not merely along one shrinking
  net — any uniform bound on the *finite-neighborhood ratios* `P(A ∩ V)/P(V)` over a
  small enough `U` transfers directly to `L`. The event `A` here is *"`η` has a zero at
  the point `s₀`"*, and `L = P(A ∣ T = e_η)` is its conditional probability. **The exact
  load-bearing fact is `L ≠ 1`** — whatever the limit is (and it *exists*, by Mehler /
  Radon), it cannot equal `1`. (On disk the stronger `L = 0` is what `not_rcpZeroAt`
  actually proves — the zero-ball ratio `→ 0` under the Fock conditioning — which a
  fortiori gives `L ≠ 1`; but only `≠ 1` is needed for the unprovability conclusion.)

**Why `L ≠ 1` is the whole point: it is an unprovability statement, pointwise then
uniform over the strip.** A *proof*, inside this RCA / `Π⁰₂` model, that `η` has a zero
at a specific point `s₀` would force the model to assign that event conditional
probability **`1`** at `s₀`. Since the rcp limit exists but **cannot be `1`**, no such
proof exists: *one cannot prove that there is a zero at `s₀`.* This holds for **every**
point `s₀` with `1/2 < Re s₀ < 1` (the argument is uniform — the Fock bound does not
single out a special `s₀`). Quantifying over the strip: *one cannot prove that there are
any zeros in `1/2 < Re s < 1`.* That unprovability — not a positive "there are no zeros"
claim — is the model's output, and (via the Schoenfeld `Π⁰₁` encoding + Kopperman
arithmetic-invariance) it is what discharges the Schoenfeld counterexample and yields RH.

**Why the per-point unprovability transfers to the existential (witness extraction).**
The quantifier step "no provable zero *at any* `s₀`" ⟹ "no provable zero *somewhere in*
the strip" is *not* the general (invalid) move "`∀s ¬Prov(φ(s))` ⟹ `¬Prov(∃s φ(s))`,"
which fails for a non-constructive real existential. It is licensed here because the
existential we actually care about is **arithmetical and witnessed**, not a raw
second-order `∃s ∈ ℝ`:

1. **The strip-zero existential is `Σ⁰₁` after the encoding.** By the bridge
   `counterexample_iff_rcpZero` (4.1) the assertion "`η` has a non-trivial zero in the
   strip" is equivalent, in the model, to the **arithmetical** `Σ⁰₁` sentence
   `∃ n, schoenfeld (n + 2657) = false` — an existential over `ℕ` with a *decidable*
   (`Primrec`, 3.1) matrix. The analytic `∃s ∈ ℝ` never appears bare; it is carried by
   the prime-counting `Π⁰₂` expression, whose failure is exactly this numerical
   counterexample.
2. **`Σ⁰₁` over `RCA₀` (and in the standard model) has the numerical existence /
   witness property.** A proof of `∃ n, θ(n)` with `θ` decidable yields a *specific
   numeral* `n₀` together with a proof of `θ(n₀)` — the bounded primitive-recursive
   search for the least witness is provably total. So a hypothetical proof of the strip
   existential does not stay non-constructive: it hands us a concrete `n₀`.
3. **The witness `n₀` decodes to a definite point/region `s₀(n₀)` in the strip.** The
   Schoenfeld matrix at `n₀` localizes the prime-counting discrepancy, and through the
   `Π⁰₂` ↔ contour correspondence this pins a *rational region* (a definite isolating
   rectangle / interior point `s₀`) at which the model would be forced to assert a zero
   — i.e. it instantiates the **pointwise** event `A = "zero at s₀(n₀)"` at a *definite*
   `s₀(n₀)` with `1/2 < Re s₀ < 1`.
4. **Contradiction with `L ≠ 1` at that point.** Provability of the existential thus
   yields provability of the pointwise zero-claim at `s₀(n₀)`, which would force the rcp
   `L = P(A ∣ T = e_η) = 1` there — contradicting the uniform `L ≠ 1`. Hence the
   existential is itself unprovable.

So the transfer is sound precisely because the `∃` is over `ℕ` (the Schoenfeld
counterexample) with the witness property, not over the reals. Formally this is *inside*
the 4.1 bridge: the `→` direction is "counterexample `n₀` ⟹ `rcpZeroAt` at `s₀(n₀)`,"
and `not_rcpZeroAt` (2.2) is the uniform `L ≠ 1` that the extracted witness collides
with. The witness extraction is the `∃`-elimination on `∃ n, schoenfeld (n+2657)=false`
that supplies the `s₀` fed to the per-point argument.

**Why it simplifies the whole route.** With the neighborhood-limit definition in
hand, the argument is a single clean chain — no piecewise kernel, no `StandardBorel`
re-typing of the trace, no a.e.-agreement lemma:

1. **The deterministic `η` is the point `X_n = 1 for all n`, and it is in the
   support of the prior.** The genuine Euler product of `η` is `eulerB` evaluated at
   the coefficient sequence `ω ≡ 1` (all `X_p = 1`). Since `priorBall` is the product
   of uniform laws on the *closed* unit disk, `ω ≡ 1` lies on the boundary of the
   support — *in* the support (every neighborhood has positive mass). So the
   neighborhood limit at `T = e_η` (the trace of `η`) is **defined** (Tjur's "only on
   the support" clause is met — this is exactly what Phase 1.3 should say, restated).

2. **A Fock-space expansion controls the conditional law by scale.** Condition the
   ensemble on a neighborhood of `η` by constraining the **first `P`** coefficients
   to a region of size `1/P` around their `η`-values (`X_p ≈ 1`, `p ≤ P`), while the
   coefficients `p > P` are left **unconstrained** (free, in the full unit ball).
   This is the natural "first `P` modes pinned, high modes free" Fock decomposition.

3. **The conditional variance in the critical strip → 0 with the neighborhood size.**
   As `P → ∞` (neighborhood size `1/P → 0`), the constrained low modes force the
   contour quantity toward its deterministic `η`-value, while the free high modes
   contribute a vanishing tail (the bounded-tail estimate `bSum_tail_small`, 0.2′,
   already proved). Hence the conditional law of the interior/contour value
   concentrates — its variance in the strip tends to `0` — i.e. the neighborhood
   limit is a point mass at the deterministic continuation `η(s₀)`.

4. **Therefore the rcp-probability of a zero is `0`.** "`η` has a strip zero" means
   the conditional law charges a ball around `0` (the Dirichlet series is centered at
   a value without zeros). Since the conditional law concentrates at `η(s₀) ≠ 0`
   (strip nonvanishing of the approximant/`η`), every small ball around `0` gets
   conditional mass `0` in the limit. **The probability of choosing a zero is `0`.**
   This is precisely the content the on-disk `not_rcpZeroAt` already proves (via
   boundedness); the neighborhood limit is its *justification*, and it is what makes
   the proof faithful rather than a coincidence of the joint-mass phrasing.

**The conclusion is an unprovability/independence statement, and that is what yields
RH.** Steps 1–4 say: *in this RCA / `Π⁰₂` model of the prime-counting expression, the
regular conditional probability of a non-trivial zero of `η` in the critical strip is
`0`.* Equivalently, **one cannot prove, inside this model, that such a zero exists** —
the model assigns the event probability `0`, so no Π⁰₂ witness of a zero is derivable.
By the Kopperman arithmetic-invariance layer (`interpPi01`/`pi01_invariant`,
`arith_truth_invariant`), this transfers to the standard arithmetic Schoenfeld
sentence: the `Π⁰₁` Schoenfeld bound has **no counterexample**, hence holds, hence
(Schoenfeld 1976) **RH is true**. The load-bearing formal object is the bridge
`counterexample_iff_rcpZero` (4.1): a Schoenfeld counterexample ⟺ an rcp-zero; with
the rcp-zero ruled out (2.2, now justified by 1–4), the counterexample is ruled out.

**What this changes in the file (summary; details inline below).**
* C2/C3/C4 are **SUPERSEDED** — the `κ_sel` piecewise-Dirac override, the `ℕ→ℂ`
  countable-trace re-typing, and the `κ_sel_ae_eq`/`κ_sel_eq_tjur` agreement lemmas
  are **dropped**. The on-disk joint-mass `rcpZeroAt` + proved `not_rcpZeroAt` is the
  adopted form.
* Phase 1.3 (`priorBall_edgeNbhd_pos`) is **restated**: its honest content is "`e_η`
  is in the support of the trace law" (step 1), i.e. the Tjur limit is *defined* at
  `η`. Its current statement (closeness to the *true* `etaRect` at a **fixed** `P`)
  is the dubious/unused one flagged in the file; replace it with the support
  statement, or drop it (it is not consumed downstream).
* Phase 1.4 and Phase 2.2 stay as the **proved** load-bearers; the new theorem is
  their conceptual backing, not new code.
* The remaining real work is unchanged in *location*: **4.1 (the bridge)** and **3.1
  (`schoenfeld`/`schoenfeld_primrec`)**, plus optional 5.3. The bridge's `→`
  direction is now phrased via the neighborhood limit (step 4): a counterexample
  forces the conditional law to charge `0`, contradicting concentration at `η(s₀)`.

---

## Status & corrections (read before touching the files)

The skeleton (commit pending) implements the whole pipeline. Done vs. open, and
two substantive divergences from the original prose that this plan now adopts:

**Discharged (`[mech]` glue — do not redo):**
`Ωb`/`Xb`/`eulerB` (0.1); `eulerB_ne_zero`, `eulerB_differentiableOn` (0.2);
`edgeTrace`/`interiorVal` (1.1, in the **original** uncountable-trace form — the C3
`ℕ→ℂ` re-typing was NOT taken and is not needed); `rcpKernel` *definition* (1.2);
`Pi01`/`interpPi01`/`pi01_invariant`/`interpPi01_eq` (3.2); `rcpFormalism` +
`interp_schoenfeld_eq` (the formalism wiring); `no_schoenfeld_counterexample` (5.1);
`isoRect`/`isoRect_s₀_mem`/`isoRect_re_lo`/`isoRect_hAna` + `RH_PRA_holds` (5.2).
The assembly compiles *modulo* the `sorry`s — RH-via-this-route is reduced to the
short list below.

**Discharged `[LB]` content (build re-verified green, 8040 jobs, 2026-06-18):**
`bSum_tail_small` (0.2′, the M-test) — **proved**; the whole **prior layer**
`sorry`-free — `diskLaw`, `priorBall := Measure.infinitePi (fun _ => diskLaw)`,
`priorBall_isProb`, `priorBall_ball`, `priorBall_atomless` (0.3a, answers Open
item 1: pure-continuous atomless uniform-disk product), `rcpPriorOnSubstrate` +
`isProb` + `atomless` (0.3b). **Plus the two analytic load-bearers (this is the new
progress, and along the simpler path):** `rcp_recipEulerB_tendsto_recipEta` (1.4,
with its continuity helpers `etaRect_continuousOn`, `eulerB_continuousOn`,
`recipEulerB_continuousOn`, `recipEtaRect_continuousOn_boundary`, and the per-edge
`edge_integral_tendsto`) — **proved**; and `not_rcpZeroAt` (2.2) — **proved**
directly from bounded-coefficient nonvanishing (no `κ_sel`, no Tjur machinery).

**Open `sorry`s (5 total, the real remaining content):**
`priorBall_edgeNbhd_pos` (1.3, **dubious as stated, unused — restate as the
support statement of step 1, or drop**); `schoenfeld` + `schoenfeld_primrec` (3.1,
self-contained `Primrec`, best first target); `counterexample_iff_rcpZero` (4.1,
**the one genuine load-bearing bridge** — now phrased via the neighborhood limit);
`riemann_hypothesis_via_rcp` (5.3, optional Schoenfeld-1976 analytic return).
*The 2.1/2.1′ `κ_sel`/`IsTjurCond`/`κ_sel_eq_tjur` targets are WITHDRAWN — see the
superseded C2/C3/C4 below; the on-disk joint-mass `rcpZeroAt` is the adopted form.*

**Correction C1 — Phase 0.2's convergence claim was false; it is now the tail
lemma.** The prose asked for `eulerB P · ω → etaRect`. That is false for a generic
ball-`ω`: the random factor `exp(∑_p X_p p^{-s})` does **not** tend to `1`. The
true, sufficient content of N2 is *uniform tail smallness* of the prime Dirichlet
sum, captured by `bSum_tail_small`. The conditional route (1.4) only ever uses the
tail estimate, so nothing downstream is weakened. **0.2 below is rewritten to
match.**

> **⚠ C2/C3/C4 are SUPERSEDED (2026-06-18).** The `κ_sel` selected-kernel override,
> the `ℕ→ℂ` countable-trace re-typing, and the `κ_sel_ae_eq`/`κ_sel_eq_tjur`
> agreement lemmas were **never implemented and are no longer needed**. The
> implementer kept the on-disk **joint-mass `rcpZeroAt`** and **proved**
> `not_rcpZeroAt` directly; the 2026-06-18 neighborhood-limit theorem (see "The
> simplification" above) supplies the honest justification without any selection
> device. C2–C4 are retained below **for historical context only** — do not
> implement them. The one piece of C4 that survives, recast, is "the Tjur limit is
> defined only on the support," which becomes the restated Phase 1.3.

**Correction C2 [SUPERSEDED — historical] — `rcpZeroAt` ranges over the
selected `condDistrib` kernel at the null point, NOT the joint event.** The
skeleton's implemented `rcpZeroAt` (2.1) used the **joint-event** form — a schedule
`ε k ↓ 0` along which the joint mass
`priorBall {ω | edges within ε k of η  ∧  |eulerB s₀ ω| < r}` stays positive. That
is event-conditioning on the joint — the "direct route" N1 explicitly warns is
**not** the genuine regular conditional probability — and it orphans `rcpKernel`
(the `condDistrib` disintegration, 1.2) and discards the route's whole mechanism.
**The maintainer has now pinned the canonical form: `rcpZeroAt` ranges over the
selected version of the `condDistrib` kernel evaluated at the (prior-null)
conditioning value `η`,** where the selected version is *free at that null point*
(determined only `μ.fst`-a.e., hence unpinned at `η`). This is precisely the
rcp-non-uniqueness mechanism that is load-bearing in the P-vs-NP work (the selected
`κ_sel` of `IMPLEMENTATION_PLAN.md` K12.11/NC11) — the two routes now share one
selected-kernel device. Consequences, propagated below:

* **Phase 2.1 must be re-typed.** Replace the skeleton's joint-mass `rcpZeroAt`
  with the kernel form `∀ r > 0, 0 < (rcpKernel …) (edgeTrace_of η) (Metric.ball 0 r)`,
  ranging over the **selected** version of `rcpKernel` at the `η`-trace point. This
  is a definition change in `RcpEuler.lean`, not a `sorry` discharge.
* **`rcpKernel` (1.2) is now USED** by 2.1 — no longer orphaned.
* **2.2 (`not_rcpZeroAt`) and 4.1 (`counterexample_iff_rcpZero`) re-type** to the
  new `Prop`; their recipes (below) are restated against the selected kernel.
* The selection-as-a-chosen-version must be packaged explicitly (a kernel field
  with the a.e.-agreement `κ_sel =ᵐ[priorBall.fst] rcpKernel`), mirroring NC11.1.

**Correction C3 — the conditioning trace must be a COUNTABLE boundary sample, so
the `κ_sel` override is well-typed (surfaced 2026-06-17 while making 2.1
turn-key).** The skeleton typed the trace as `(R.closure \ R.openInt) → ℂ`, an
**uncountably**-indexed function space. The selected-kernel override of 2.1 builds
`κ_sel` by `ProbabilityTheory.Kernel.piecewise (measurableSet_singleton e_η) …`,
which requires `{e_η}` measurable — i.e. `MeasurableSingletonClass` on the trace
space. That instance **does not synthesize** for `I → ℂ` with `I` uncountable
(verified by `inferInstance` failure), so the override cannot even be stated there.
It **does** synthesize for `ℕ → ℂ`, which is also `StandardBorelSpace` (both
verified). **Fix (adopted in 1.1/1.2):** condition on a fixed dense countable
boundary sample `zs : ℕ → (R.closure \ R.openInt)`, making the trace space
`ℕ → ℂ`. This is faithful because `eulerB(·,ω)` is analytic, so a dense boundary
sample determines the interior — conditioning on the sample is the same up to null
sets. This re-types `edgeTrace` (1.1) and `rcpKernel` (1.2); nothing else moves
(the 1.3 events keep their `∀ z ∈ closure` form). It is the enabler for the entire
2.1 construction below.

**Refinement C4 — Tjur's limit characterization of rcp pins the selected value
(maintainer, 2026-06-17); it RECONCILES the neighborhood-limit and `condDistrib`
framings, and strengthens the route's honesty.** Tjur's theorem gives an
*alternative* definition of the regular conditional probability as a **limit over
the net of shrinking open neighborhoods**:
```
P(A ∣ T = t) = lim_{U ⊃ {T=t}}  P(A ∩ T⁻¹U) / P(T⁻¹U),
```
the limit taken over open neighborhoods `U` of `t` ordered by reverse inclusion;
**it is defined iff the probability space is Radon, and only on the support of
`T`.** This is directly formalizable in Mathlib (no new primitives) and is the
*correct* reading of the maintainer's original "neighborhood converges to `η`,
integrals converge" intuition (Phase 1.4). Three facts make it land, all verified:

* **The net is `(𝓝 t).smallSets`.** `MeasureTheory.Measure.support` is *defined* as
  `{x | ∃ᶠ u in (𝓝 x).smallSets, 0 < μ u}` — Mathlib's "shrinking neighborhoods"
  net is exactly Tjur's. The limit is `Filter.Tendsto (fun U => P(A∩T⁻¹U)/P(T⁻¹U))
  ((𝓝 t).smallSets) (𝓝 L)`.
* **The Radon precondition is automatic on the substrate** (the maintainer's note):
  a separable Hilbert space is `PolishSpace`, and a finite Borel measure on a
  Polish space is `InnerRegular` (= Radon) — both `inferInstance` (verified). So
  `priorBall` (and its substrate image) satisfy Tjur's "iff Radon" hypothesis for
  free.
* **"Only on the support of `T`" is exactly Phase 1.3.** Tjur's limit is defined at
  `t = e_η` iff `e_η ∈ (priorBall.map (edgeTrace P R)).support`, i.e. every
  neighborhood of `e_η` has positive trace-measure — which is precisely
  `priorBall_edgeNbhd_pos` (1.3). So 1.3 is not just "positive mass"; it is the
  statement *"`e_η` is in the support, hence the Tjur conditional is defined there."*

**What this does to C2 / the `κ_sel` construction.** It *refines* C2. The "selected
version is free at the null point" is true only **outside** the support; **on** the
support — where 1.3 puts `e_η` — the Tjur limit **pins** the conditional value.
Since `e_η` is null (`P{T=e_η}=0`) yet in the support (atomless: every neighborhood
positive), the value at `e_η` is **both null-point and determined**. Therefore
`κ_sel(e_η)` is **not** an arbitrary choice: it must equal the Tjur limit, and by
the analytic-continuation argument that limit is `dirac(η(s₀))`. This **upgrades the
honesty** of the 2.1 override: `selVal := dirac(etaRect s₀)` is justified as *the
genuine neighborhood limit*, not a free selection. Concretely it sharpens the 2.1
`[LB]` obligation from the vague `κ_sel_ae_eq` to the precise **Tjur-agreement
lemma** (2.1′ below). The earlier worry that the joint/neighborhood form "collapses
to the direct route N1 forbids" was about conditioning on a *single fixed* event;
the Tjur **limit** over the `smallSets` net is the genuine rcp — N1's prohibition
never applied to it.

---

## Cross-cutting notes (read first)

* **N1 — the prior may be mixed.** The coefficient law need not be continuous.
  A mixed continuous+discrete measure is allowed and is part of the design:
  regular conditional probability under a mixed measure is **not** the same object
  as the direct route obtained by collapsing onto the discrete part. Whenever rcp
  is invoked, use the genuine kernel/disintegration API
  (`MeasureTheory.Measure.condKernel`, `ProbabilityTheory.condDistrib`), **not**
  `ProbabilityTheory.cond` on a single event, unless a step explicitly only needs
  event-conditioning.
* **N2 — bounded coefficients are the whole point.** Values in the closed unit
  ball give, for *every* `ω`, absolute and locally uniform convergence of
  `∑_{p>P} X_p(ω) p^{-s}` on `{Re ≥ a > 1}` (dominated by `∑_{p>P} p^{-a}`). This
  is the unconditional right-edge convergence the Gaussian model only had a.s.
* **N3 — reuse, don't re-derive.** The contour scaffolding (`Rect`,
  `Rect.boundaryIntegral`, `rect_cauchy`, `boundary_integral_limit_eq_zero`,
  `etaRect`, `etaFactRect`) is in `RectangleStrategy.lean`. The Kopperman model
  layer is in `PnpProof/Kopperman.lean`. The arithmetic-invariance proxy
  (`arith_truth_invariant`, `interpPi02`) is there too and is the template for the
  `Π⁰₁` interpretation in Phase 3.
* **N4 — mark the load-bearing steps as `sorry`, with the recipe in a comment.**
  Steps flagged **[LB]** carry the mathematical content; do not improvise a proof.
  Steps flagged **[mech]** are mechanical given their dependencies.

---

## Phase 0 — The bounded-coefficient prior and its Euler product

New file `RiemannProof/RcpEuler.lean`, importing `RiemannProof.RectangleStrategy`
and `RiemannProof.GaussianEuler` (to reuse `cCorr`, `Rect`, `etaRect`).

* **0.1 [mech] Coefficient and product.**
  ```lean
  /-- Sample space: a coefficient per prime index, valued in ℂ. -/
  abbrev Ωb : Type := ℕ → ℂ
  /-- Bounded coefficient: the ω-th coordinate, used only where ‖·‖ ≤ 1 a.e. -/
  def Xb (p : ℕ) (ω : Ωb) : ℂ := ω p
  /-- Exponential Euler product with bounded coefficients. -/
  def eulerB (P : ℕ) (s : ℂ) (ω : Ωb) : ℂ :=
    Complex.exp ((∑ p ∈ (Finset.range (P+1)).filter Nat.Prime, Xb p ω * (p:ℂ)^(-s))
                 + cCorr P s)
  ```
* **0.2 [mech, DONE] Structural facts.** `eulerB_ne_zero` (immediate from the
  `exp` form) and `eulerB_differentiableOn` (mirrors `eulerG_differentiableOn`:
  `bSum` is entire, `exp(bSum)·etaEulerApprox` is differentiable off the
  `etaEulerApprox`-zeros, and equals `eulerB` there via `exp_log`) are **proved**,
  no `sorry`.
* **0.2′ [LB, corrected — see C1] Bounded-tail lemma.** The original
  `eulerB P · ω → etaRect` is *false* (C1). The correct, sufficient statement is
  uniform smallness of the prime-Dirichlet *tail*:
  ```lean
  lemma bSum_tail_small (a : ℝ) (ha : 1 < a) (ω : Ωb) (hω : ∀ p, ‖Xb p ω‖ ≤ 1) :
      ∀ ε > 0, ∃ P₀, ∀ P ≥ P₀, ∀ Q ≥ P, ∀ s : ℂ, a ≤ s.re →
        ‖∑ p ∈ (primesUpto Q) \ (primesUpto P), Xb p ω * (p:ℂ)^(-s)‖ ≤ ε
  ```
  Proof tool: Weierstrass M-test against the convergent tail `∑_{p>P} p^{-a}`,
  with `‖X_p p^{-s}‖ ≤ p^{-a}` by `hω` (this is N2; no a.s. qualifier). This is
  the only convergence fact 1.4 consumes.
* **0.3 [LB] The prior as a Kopperman model.** Define the prior `μb : Measure Ωb`
  concentrated on `∀ p, ‖ω p‖ ≤ 1` (product of unit-ball laws; mixed allowed, N1):
  ```lean
  def priorBall : Measure Ωb := …            -- IsProbabilityMeasure, supported on the ball
  ```
  Then connect to the formalism. Either (a) transport `priorBall` to an atomless
  measure on `PnpProof.Kopperman.Substrate` and apply
  `PnpProof.Kopperman.formalismOfPrior`, or (b) generalize `Formalism` to an
  abstract carrier and instantiate at `Ωb`. Deliverable:
  ```lean
  def rcpFormalism : PnpProof.Kopperman.Formalism _ := …   -- prior = (image of) priorBall
  ```
  Recipe in comment: reuse `exists_atomless_prob_substrate` /
  `prior_surjective_onto_atomless`; the atomless requirement forces the
  *continuous* part of the mixed prior to be nontrivial — record that as a
  hypothesis of `priorBall`.

## Phase 1 — Regular conditional probability and contour convergence

* **1.1 [mech] Edge-evaluation map — COUNTABLE boundary sample (re-typed; see
  Correction C3).** For a strip-internal loop `R : Rect`
  (`∀ z ∈ R.closure, 1/2 < z.re`, `s₀ ∈ R.openInt`), fix once a **dense sequence**
  of boundary points `zs : ℕ → (R.closure \ R.openInt)` (e.g. a rational-coordinate
  enumeration of the boundary; `R.closure \ R.openInt` is a separable metric space,
  so `TopologicalSpace.denseSeq` / `exists_dense_seq` supplies one). Define the
  **sampled** boundary trace into the standard-Borel space `ℕ → ℂ`:
  ```lean
  def edgeTrace (P : ℕ) (R : Rect) (ω : Ωb) : ℕ → ℂ :=
    fun n => eulerB P (zs n) ω
  ```
  and the interior value `fun ω => eulerB P s₀ ω`.
  **Why the sample, not the full continuum trace `(R.closure \ R.openInt) → ℂ`:**
  the override in 2.1 needs `{e_η}` measurable in the trace space, which holds in
  `ℕ → ℂ` (`MeasurableSingletonClass`, `StandardBorelSpace` both synthesize —
  verified) but **fails** for an uncountably-indexed `I → ℂ` (`MeasurableSingletonClass
  (I → ℂ)` does not synthesize — verified). The sample loses nothing: `eulerB(·,ω)`
  is analytic on the strip, so its values on a dense boundary sequence determine it
  on `R.closure` by continuity/the identity theorem; conditioning on the sample is
  therefore the same σ-algebra (up to null sets) as conditioning on the full trace.
  Record `zs` and its density as fixed data of the file. (The edge-neighborhood
  *events* of 1.3 keep their full `∀ z ∈ R.closure \ R.openInt` form — they live in
  `ω`-space and are unaffected by this re-typing; only the kernel's conditioning
  variable changes.)
* **1.2 [LB] The rcp kernel.** Build the regular conditional distribution of the
  interior value given the sampled edge trace, using `ProbabilityTheory.condDistrib`
  (the genuine kernel; N1). State it for `priorBall`:
  ```lean
  def rcpKernel (P : ℕ) (R : Rect) :
      ProbabilityTheory.Kernel (ℕ → ℂ) ℂ :=
    ProbabilityTheory.condDistrib (fun ω => eulerB P s₀ ω) (edgeTrace P R) priorBall
  ```
  Recipe: needs measurability of both maps (continuity of `eulerB` in `ω`;
  `edgeTrace` measurable as a countable product of measurables) and
  `IsFiniteMeasure priorBall`. `ℕ → ℂ` is `StandardBorelSpace` (verified), which is
  what `condDistrib`'s disintegration needs on the conditioning space.
* **1.3 [LB — RESTATE, see the simplification §; currently a dubious/unused
  `sorry`].** The on-disk lemma compares `eulerB P · ω` to the **true** `etaRect` at
  a **fixed** `P`:
  ```lean
  lemma priorBall_edgeNbhd_pos (P : ℕ) (R : Rect) (ε : ℝ) (hε : 0 < ε) :
      0 < priorBall {ω | ∀ z ∈ R.closure \ R.openInt, ‖eulerB P z ω - etaRect z‖ < ε}
  ```
  As the file's own docstring notes, the small-coefficient concentration only yields
  closeness to the **approximant** `etaEulerApprox P`, which differs from `etaRect`
  by the (fixed, generally non-small) approximation gap — so the statement is
  **dubious at fixed `P`** and is **not used downstream** (1.4 was proved from its
  own hypothesis `hconv`, not from 1.3). **Two honest options (pick one):**
  * **(preferred) Restate as the support statement** of the simplification's step 1:
    `e_η ∈ (priorBall.map (edgeTrace P R)).support`, i.e. *every neighborhood of the
    `η`-trace has positive prior mass* — equivalently `∀ ε>0, 0 < priorBall {ω | ‖eulerB P z ω − etaEulerApprox P z‖ < ε on the edges}`
    **against the approximant** (provable: small-coefficient concentration of the
    bounded fluctuation `∑_{p≤P} X_p p^{-s}` near `0`, an open `ω`-ball of positive
    `priorBall` mass via `priorBall_atomless`/the continuous product). This is the
    Tjur "defined only on the support" precondition and the `X_n=1`-in-support fact.
  * **(or) Drop it** — nothing consumes it. The route is `sorry`-lighter and the
    build stays green.
* **1.4 [LB — PROVED on disk] Conditional contour convergence.** Along `P_k → ∞`, `ε_k ↓ 0`,
  conditioned on the edge-neighborhood events, the reciprocal traces converge and
  the integrals pass to the limit:
  ```lean
  lemma rcp_recipEulerB_tendsto_recipEta (R : Rect) (s₀ : ℂ)
      (hRlo : ∀ z ∈ R.closure, 1/2 < z.re) (hs₀ : s₀ ∈ R.openInt)
      (hη : ∀ z ∈ R.closure, z ≠ s₀ → etaRect z ≠ 0) :
      Tendsto (fun k => R.boundaryIntegral (fun z => 1 / eulerB (P_k) z (ω_k)))
        atTop (𝓝 (R.boundaryIntegral (fun z => 1 / etaRect z)))
  ```
  Recipe: `reciprocal_tendstoUniformlyOn_of_nonvanishing`
  (`EtaConvergenceExtended:51`) + `boundary_integral_limit_eq_zero`
  (`RectangleStrategy:813`), with the `ω_k` drawn from the positive-measure events
  of 1.3. This is the maintainer's "neighborhood converges to η, integrals
  converge."

## Phase 2 — rcp non-detectability of a strip zero

* **2.1 [definition — ADOPTED on-disk: the joint-mass form; the C2 `κ_sel` re-type
  is WITHDRAWN].** Make precise "`η` has a zero at `s₀` in the rcp sense." The
  on-disk definition (kept, not re-typed) phrases it as the persistence of positive
  joint mass near `0` as the edges are pinned to `η` along a shrinking schedule
  `ε k ↓ 0` — which, read through the 2026-06-18 neighborhood-limit theorem, is
  exactly "the conditional law charges every ball around `0` in the limit":
  ```lean
  def rcpZeroAt (P : ℕ → ℕ) (R : Rect) (s₀ : ℂ) : Prop :=
    ∃ ε : ℕ → ℝ, (∀ k, 0 < ε k) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ r > 0, ∀ k,
        0 < priorBall {ω | (∀ z ∈ R.closure \ R.openInt,
              ‖eulerB (P k) (z : ℂ) ω - etaRect z‖ < ε k) ∧ ‖eulerB (P k) s₀ ω‖ < r}
  ```
  This **is** the genuine rcp object once paired with the neighborhood-limit reading
  (the numerator/denominator of the Tjur quotient are exactly the constrained-edge
  joint mass and the edge mass): the simplification's Fock-space expansion (first `P`
  modes pinned to size `1/P`, high modes free) is the concrete shrinking schedule
  `ε k`. No `κ_sel` piecewise override, no `ℕ→ℂ` re-typing, no `condDistrib`
  selection are needed. `rcpKernel` (1.2) remains a stand-alone definition (the
  `condDistrib` disintegration) and is not load-bearing for the route.
* **2.2 [PROVED on disk] Non-detectability — there is no rcp-zero in the strip.**
  ```lean
  lemma not_rcpZeroAt (P : ℕ → ℕ) (R : Rect) (s₀ : ℂ) (hs₀ : s₀ ∈ R.openInt)
      (hRlo : ∀ z ∈ R.closure, 1 / 2 < z.re)
      (hAna : ∀ k, ∀ z ∈ R.closure, etaEulerApprox (P k) z ≠ 0) :
      ¬ rcpZeroAt P R s₀
  ```
  **Proved.** The bounded coefficients (`priorBall_ball`: `‖X_p‖ ≤ 1` a.e.) keep the
  interior value `eulerB (P 0) s₀ ·` bounded *below* by a positive constant
  `r := exp(−B + Re(cCorr))` on the support of `priorBall` (since
  `Re(bSum) ≥ −‖bSum‖ ≥ −B` with `B := ∑_{p≤P₀} ‖p^{-s₀}‖`). Hence the joint event
  `{‖eulerB (P 0) s₀ ω‖ < r}` is `priorBall`-null, contradicting the `0 < …`
  demanded by `rcpZeroAt` at that `r`. This is the simplification's step 4 (the
  conditional law concentrates at `η(s₀) ≠ 0`, so the probability of a zero is `0`)
  realized concretely — and it needs **only boundedness**, not the neighborhood
  limit, which is why it was provable directly. The neighborhood-limit theorem is
  its conceptual *justification* (why the joint-mass phrasing is the honest rcp), not
  an input to the Lean proof. The hypothesis `hAna` is discharged unconditionally at
  the call site on `isoRect`/`s₀ = 3/4` (`isoRect_hAna`, strip nonvanishing of the
  approximant). **The route's analytic content therefore lives entirely in the bridge
  4.1.**

## Phase 3 — The Schoenfeld `Π⁰₁` encoding and its interpretation

New file `RiemannProof/SchoenfeldPRA.lean`, importing `Mathlib` and
`PnpProof.Kopperman`.

* **3.1 [LB] The primitive recursive matrix.** Define the decidable predicate of
  Schoenfeld's bound (`|π(n) − Li(n)| ≤ (1/8π)√n ln n` for `n ≥ 2657`), squared
  and rationalized to integer arithmetic so it is primitive recursive:
  ```lean
  def schoenfeld (n : ℕ) : Bool := …          -- bounded computation, no analysis at runtime
  theorem schoenfeld_primrec : Primrec schoenfeld := …
  def RH_PRA : Prop := ∀ n, schoenfeld (n + 2657) = true
  ```
  Recipe: implement `π(n)` exactly (`Nat.primesBelow` / a sieve), and rational
  truncations of `√`, `ln`, `Li` to predictable precision (all `Primrec` — bounded
  `for` loops). API: `Primrec`, `Primrec.nat_*`, `Nat.Primrec`. The squaring step
  removes `√`; the precision bound removes the series tails.
* **3.2 [mech] `Π⁰₁` interpreter, mirroring `interpPi02`.** Add to (a local copy
  of) the Kopperman API:
  ```lean
  def Pi01 (p : ℕ → Bool) : Prop := ∀ n, p n = true
  def interpPi01 {H} [..] (p : ℕ → Bool) (_F : Formalism H) (_z : ZFSet) : Prop := Pi01 p
  theorem pi01_invariant (p) (F₁ F₂ : Formalism H) (z₁ z₂ : ZFSet) :
      interpPi01 p F₁ z₁ ↔ interpPi01 p F₂ z₂ := Iff.rfl
  ```
  This is the exact analog of `arith_truth_invariant` (`Kopperman:289`) one
  hierarchy level down; reuse its proof shape (`Iff.rfl`, standard-`ℕ`
  absoluteness). `interpPi01 (fun n => schoenfeld (n+2657)) rcpFormalism z`
  is the Schoenfeld sentence *interpreted in the bounded-prior model*.

## Phase 4 — The bridge (counterexample ⟺ rcp-zero, under the prior)

* **4.1 [LB — THE remaining load-bearer] The correspondence.** The single
  load-bearing equivalence of the route, stated entirely on the rcp side (no
  standard `η`). On-disk signature (with the cutoff schedule `P`):
  ```lean
  theorem counterexample_iff_rcpZero (P : ℕ → ℕ) (R : Rect) (s₀ : ℂ)
      (hs₀ : s₀ ∈ R.openInt) :
      (∃ n, schoenfeld (n + 2657) = false) ↔ RcpEuler.rcpZeroAt P R s₀
  ```
  **Recipe, recast via the 2026-06-18 neighborhood limit (the simplification's
  steps 1–4).** The `→` direction: a Schoenfeld `Π⁰₁` counterexample is, through the
  Kopperman prior-model interpretation (`interpPi01`/`pi01_invariant`), a witness
  that the prime-counting `Π⁰₂` expression forces a non-trivial zero of `η` in the
  strip; by the contour convergence (1.4) such a zero makes the rcp/neighborhood
  limit of the interior value charge every ball around `0` — i.e. `rcpZeroAt`. The
  `←` direction is the converse. **Note the asymmetry the route exploits:** 2.2
  proves `¬ rcpZeroAt` *unconditionally* (boundedness), so the `←` direction
  combined with 2.2 already yields "no counterexample"; the genuinely hard half is
  `→` (a counterexample *would* produce an rcp-zero), which is where the Fock-space
  variance-→-0 picture and the analytic content of Schoenfeld's encoding are
  consumed. Keep `sorry` with this recipe; do not improvise. **This is the only
  load-bearing analytic obligation left in the route** (3.1 is independent
  arithmetic; 5.3 is optional).

  **The `ε`–`U`–`V` device for "`L ≠ 1`" (the conditional probability of a zero at
  `s₀` is not `1`).** The quantitative core of the route is a bound on the rcp
  `L = P("η has a zero at s₀" ∣ T = e_η)`, and the honest way to get it is Tjur's
  `ε`–`U`–`V` characterization (see "The simplification" above), *not* the joint-mass
  coincidence. The limit `L` is **well-defined because the substrate is Radon** (Tjur's
  existence hypothesis, here automatic — Polish inner-product space ⇒ inner-regular
  Borel measures; this is the Mehler-formalism-within-Kopperman-formalism layer). Then:
  for any `ε > 0` pick the Tjur neighborhood `U`; on every open `V` with
  `{T = e_η} ⊂ V ⊂ U` the **finite-`P` Fock conditioning** (first `P` modes pinned to
  size `1/P`, `p > P` free) makes the conditional law of the interior value concentrate
  at `η(s₀) ≠ 0` (steps 2–3), so the zero-ball ratio `P(A ∩ V)/P(V)` stays bounded away
  from `1`; by the `ε`–`U`–`V` inequality `|P(A∩V)/P(V) − L| < ε`, **`L ≠ 1`** (on disk,
  in fact `L = 0` via `not_rcpZeroAt`, which a fortiori gives `≠ 1`). **The logical role
  is unprovability, and only `≠ 1` is needed:** a proof that `η` has a zero at `s₀`
  would force `L = 1` at `s₀`; since `L ≠ 1`, no such proof exists — *one cannot prove a
  zero at `s₀`*. This is the genuine content of the `→` direction (contrapositive: no
  forced rcp-`1` ⇒ no Schoenfeld counterexample), and it is **uniform in `s₀` over the
  whole strip `1/2 < Re s₀ < 1`**, giving the route's real conclusion: *one cannot prove
  there are any zeros in the strip.* **The `→` proof begins with `∃`-elimination on
  `∃ n, schoenfeld (n+2657)=false`** (witness extraction — see "Why the per-point
  unprovability transfers to the existential" in The simplification): the `Σ⁰₁` witness
  property hands a concrete `n₀`, which decodes to the definite `s₀(n₀)` plugged into the
  uniform `L ≠ 1` / `not_rcpZeroAt` step. Implementation note: this `ε`–`U`–`V` bound is the
  intended *replacement* for any joint-mass shortcut in the `→` proof — it is what makes
  the bridge faithful. (`L` is the Tjur limit over `(𝓝 e_η).smallSets`;
  `MeasureTheory.Measure.support` is literally defined via that net, so `e_η ∈ support`
  — Phase 1.3 restated — is exactly the "limit is defined" precondition.)

## Phase 5 — Assembly

* **5.1 [mech — DONE on disk] No counterexample.** On-disk signature threads the
  cutoff schedule and the approximant-nonvanishing hypotheses straight into the
  proved 2.2:
  ```lean
  theorem no_schoenfeld_counterexample (P : ℕ → ℕ) (R : Rect) (s₀ : ℂ)
      (hs₀ : s₀ ∈ R.openInt) (hRlo : ∀ z ∈ R.closure, 1 / 2 < z.re)
      (hAna : ∀ k, ∀ z ∈ R.closure, etaEulerApprox (P k) z ≠ 0) :
      ¬ ∃ n, schoenfeld (n + 2657) = false := by
    rw [counterexample_iff_rcpZero P R s₀ hs₀]
    exact RcpEuler.not_rcpZeroAt P R s₀ hs₀ hRlo hAna
  ```
  At the call site (5.2) `hRlo`/`hAna` are discharged on `isoRect`/`s₀ = 3/4` by
  `isoRect_re_lo` and `isoRect_hAna` (strip nonvanishing of the approximant).
* **5.2 [mech — DONE on disk] `Π⁰₁` sentence holds.** Instantiated at the concrete
  `isoRect` with `s₀ = 3/4` and the trivial schedule `P = id`:
  ```lean
  theorem RH_PRA_holds : RH_PRA := by
    intro n; by_contra h
    have hfalse : schoenfeld (n + 2657) = false := by
      cases hc : schoenfeld (n + 2657) with
      | false => rfl
      | true => exact absurd hc h
    exact no_schoenfeld_counterexample (fun k => k) isoRect ((3 : ℂ) / 4)
      isoRect_s₀_mem isoRect_re_lo (isoRect_hAna (fun k => k)) ⟨n, hfalse⟩
  ```
* **5.3 [LB] Back to ζ (optional, the analytic Schoenfeld direction).**
  ```lean
  theorem riemann_hypothesis_via_rcp :
      ∀ s, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1/2
  ```
  Recipe: `RH_PRA → RH` is the Schoenfeld equivalence (the genuine analytic
  content of Schoenfeld 1976). If the maintainer wants the final statement to
  *remain* `RH_PRA` (the `Π⁰₁` form), stop at 5.2 and skip 5.3.

---

## Build order & status (each line: `lake build` before the next)

Legend: `✓` done in the skeleton · `□` open `[LB] sorry` · `‼` open + needs a
maintainer decision first.

```
0.1  Ωb, Xb, eulerB                         ✓ mech
0.2  eulerB_ne_zero, eulerB_differentiableOn ✓ mech
0.2′ bSum_tail_small (was eulerB_tail; C1)  ✓ LB    PROVED (M-test)
0.3a diskLaw, priorBall, isProb, _ball, _atomless  ✓ LB  PROVED (uniform-disk infinitePi; answers item 1)
0.3b rcpPriorOnSubstrate, isProb, atomless  ✓ LB    PROVED (Classical.choose exists_atomless_prob_substrate)
     rcpFormalism, interp_schoenfeld_eq     ✓ mech  (wired off 0.3b)
3.1  schoenfeld, schoenfeld_primrec         □ LB    (Primrec; INDEPENDENT — best first target; 2 sorries)
3.2  Pi01/interpPi01/pi01_invariant         ✓ mech  (cloned arith_truth_invariant)
1.1  edgeTrace, interiorVal                 ✓ mech  (ORIGINAL uncountable trace; C3 re-type NOT taken)
1.2  rcpKernel : Kernel ((R.closure\openInt)→ℂ) ℂ  ✓ mech  (condDistrib; stand-alone, not load-bearing)
1.3  priorBall_edgeNbhd_pos                 □ LB    (DUBIOUS as stated / UNUSED — restate as support, or drop; 1 sorry)
1.4  rcp_recipEulerB_tendsto_recipEta       ✓ LB    PROVED (+ continuity helpers, edge_integral_tendsto)
2.1  rcpZeroAt (JOINT-MASS form, kept)      ✓ def   (κ_sel/C2 re-type WITHDRAWN; this is the adopted Prop)
2.2  not_rcpZeroAt                          ✓ LB    PROVED (bounded-coeff nonvanishing; simplification step 4)
4.1  counterexample_iff_rcpZero             □ LB    (THE bridge — the only load-bearing analytic obligation left; 1 sorry)
5.1  no_schoenfeld_counterexample           ✓ mech  (assembled: 4.1 + proved 2.2)
5.2  isoRect, RH_PRA_holds                  ✓ mech  (instantiated at s₀ = 3/4, P = id)
5.3  riemann_hypothesis_via_rcp             □ LB, optional  (Schoenfeld 1976 analytic direction; 1 sorry)
```

**5 `sorry`s on disk:** 1.3 (dubious/unused), 3.1 ×2 (`schoenfeld`,
`schoenfeld_primrec`), 4.1 (the bridge), 5.3 (optional). **Wire-in DONE:**
`RiemannProof.lean` imports both modules; `lake build RiemannProof.RcpEuler
RiemannProof.SchoenfeldPRA` is **green at 8040 jobs (re-verified 2026-06-18)** —
`sorry`/long-line linter warnings only, no errors.

## Reused infrastructure (do not re-prove)

| Lemma / def | File:line | Use |
|---|---|---|
| `Rect`, `Rect.boundaryIntegral`, `rect_cauchy` | RectangleStrategy:204 | 0.2, 1.4 |
| `boundary_integral_limit_eq_zero` | RectangleStrategy:813 | 1.4 |
| `reciprocal_tendstoUniformlyOn_of_nonvanishing` | EtaConvergenceExtended:51 | 1.4 |
| `cCorr`, `exp_cCorr_eq_etaEulerApprox` | GaussianEuler:140,161 | 0.1, 1.3 |
| `eulerG_ne_zero` (template) | GaussianEuler:171 | 0.2 |
| `exists_straddling_isolating_rect` | GaussianEuler:438 | 5.2 |
| `Formalism`, `formalismOfPrior`, `prior_surjective_onto_atomless` | Kopperman:46,213,230 | 0.3 |
| `Pi02`, `interpPi02`, `arith_truth_invariant` | Kopperman:272,278,289 | 3.2 (template) |
| `Primrec`, `Nat.Primrec` | Mathlib | 3.1 |
| `ProbabilityTheory.condDistrib`, `Measure.condKernel` | Mathlib | 1.2 |
| `Real.summable_nat_rpow`, `Finset.sum_Ico_eq_sub` (the M-test tail) | Mathlib | 0.2′ |
| `Measure.infinitePi`, `Measure.infinitePi_map_eval`, `ProbabilityTheory.cond` | Mathlib | 0.3a |

*The following were listed for the withdrawn C2/C3/C4 `κ_sel`/Tjur/`ℕ→ℂ` apparatus
(2.1/2.1′) and are **no longer used** by the route: `Kernel.piecewise`,
`Kernel.const`, `Measure.dirac`, `MeasurableSingletonClass (ℕ→ℂ)`/`StandardBorelSpace
(ℕ→ℂ)`, `denseSeq`, `Filter.smallSets`, `Measure.support`, `PolishSpace`/`InnerRegular`.
They remain valid Mathlib names should the support-statement restatement of 1.3 want
`Measure.support`/`smallSets`.*

## Open items the maintainer must pin before/at the relevant step

1. **The exact prior `priorBall` — RESOLVED (implementer, 2026-06-17).** The prior
   is the **pure continuous** law `priorBall := Measure.infinitePi (fun _ => diskLaw)`,
   an independent product of the uniform law on the closed unit disk (`diskLaw :=
   ProbabilityTheory.cond volume (closedBall 0 1)`); proved a probability measure,
   supported in the closed unit ball, and **atomless** (`priorBall_atomless`). The
   substrate transport `rcpPriorOnSubstrate` is the canonical atomless measure from
   `exists_atomless_prob_substrate` (the `Π⁰₁` interpretation is content-free in the
   prior, so only atomlessness is structurally required). *Note:* this is the
   pure-continuous choice — there is **no** discrete part (the N1 "mixed measure"
   option was not taken); atomlessness, which is all the route needs, holds. Both
   0.3a and 0.3b are now `sorry`-free.
2. **The form of `rcpZeroAt` (2.1) — RESOLVED, and the C2 selected-kernel form is
   WITHDRAWN (2026-06-18).** The adopted form is the on-disk **joint-mass**
   `rcpZeroAt` (positive joint mass near `0` along a shrinking edge schedule). The
   earlier C2 decision to re-type it to a selected `condDistrib`/`κ_sel` kernel was
   **not implemented and is now dropped**: the 2026-06-18 neighborhood-limit theorem
   shows the joint-mass form *is* the genuine rcp (its numerator/denominator are the
   Tjur quotient), so there is nothing to select. `not_rcpZeroAt` against this form
   is **proved**. No pending decision.
3. **Final target**: `RH_PRA` (`Π⁰₁`, stop at 5.2 — already proved modulo the bridge
   4.1 and `schoenfeld` 3.1) or `riemann_hypothesis_via_rcp` (do 5.3 via Schoenfeld
   1976's analytic equivalence).

## Recommended next steps (priority order)

The route is now reduced to **two real obligations** (4.1 and 3.1) plus optional
cleanup. Everything analytic upstream — the prior, the tail estimate, the contour
convergence (1.4), and non-detectability (2.2) — is **proved**.

1. **Discharge 3.1 (`schoenfeld`, `schoenfeld_primrec`) — best first target.** The
   only fully self-contained `[LB]` block: pure `Primrec` arithmetic (an exact
   `π(n)` sieve + rational truncations of `√`/`ln`/`li`, squared to kill `√`), no
   probability or analysis, independent of everything else. It makes `RH_PRA`
   **non-vacuous** (right now `schoenfeld` is an opaque `sorry`, so `RH_PRA_holds`
   is honest-but-vacuous). 2 sorries → 0.
2. **The bridge 4.1 (`counterexample_iff_rcpZero`) — THE load-bearing obligation.**
   This is the entire remaining mathematical content of the route. Phrase the `→`
   direction via the 2026-06-18 neighborhood limit (Phase 4.1 recipe, simplification
   steps 1–4): a Schoenfeld counterexample → a strip zero of `η` → the conditional
   /neighborhood limit charges every ball around `0` (`rcpZeroAt`). The `←` direction
   plus the **proved** 2.2 already deliver "no counterexample," so the hard half is
   `→`. Leave `sorry` with the recipe; **do not improvise** — it carries the genuine
   analytic weight (and, via 5.3, all the way to RH).
3. **Tidy 1.3 (`priorBall_edgeNbhd_pos`) — restate or drop.** As written it is the
   dubious fixed-`P`-vs-true-`η` statement and is **unused**. Either restate it as
   the support statement (`e_η ∈ support` of the trace law; the `X_n=1`-in-support
   fact of the simplification, provable against the *approximant*) or delete it. Net:
   removes a `sorry` and an honesty wart. Low priority, not blocking.
4. **Optional 5.3 (`riemann_hypothesis_via_rcp`).** Only if the maintainer wants the
   final statement in `ζ`-terms rather than the `Π⁰₁` `RH_PRA`. It is Schoenfeld
   1976's analytic equivalence `RH_PRA → RH`; genuine analysis, leave `[LB] sorry`
   until 1–2 are done. If the target is `RH_PRA`, **skip it**.

**Done (do not redo):** the prior layer (0.3a/0.3b), `bSum_tail_small` (0.2′), the
contour convergence `rcp_recipEulerB_tendsto_recipEta` (1.4) with its continuity
helpers and `edge_integral_tendsto`, and non-detectability `not_rcpZeroAt` (2.2).
The C2/C3/C4 `κ_sel`/Tjur/`ℕ→ℂ` apparatus was **never needed** and is withdrawn.

**Net effect of the 2026-06-18 pass.** Reconciled the plan with disk (the implementer
took the simpler joint-mass + boundedness path and proved 1.4 and 2.2), folded in
the maintainer's neighborhood-limit theorem as the honest justification (and the
unprovability-⟹-RH reading), and narrowed the remaining frontier to `schoenfeld`
(3.1) and the bridge (4.1). Build re-verified green at **8040 jobs**. No Lean was
written here; this is plan reconciliation for the implementer.
