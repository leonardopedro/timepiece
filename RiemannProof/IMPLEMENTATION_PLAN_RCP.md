# Implementation Plan: RH via a bounded-coefficient prior + regular conditional probability (radius-2 ball, non-multiplicative Dirichlet series, ZFC-direct)

**Audience**: a Lean 4 formalization agent. **Status (2026-06-22 — REDESIGN).**
The maintainer has retargeted the route along three changes (see the authoritative master
section "**The 2026-06-22 redesign**" immediately below, which supersedes the PRA/Schoenfeld
spine of Phases 3–5 and the radius-1 / Euler-product choices of Phase 0):

* **(R)** the coefficient prior moves to the **radius-2** disk, so the mean realization
  `X_n ≡ 1` sits in the *interior* of the support — killing the boundary pathology that
  radius 1 created at the conditioning point;
* **(M)** the model is the **general, non-multiplicative** random Dirichlet series
  `η_X(s) = ∑ X_n n^{-s}` (independent, bounded coefficients, mean 1, chosen covariance —
  **no Euler product, no multiplicativity**);
* **(Z)** the route is **ZFC-direct**: the target is the standard analytic RH, the bridge
  is a measure-theoretic **transfer equality** `P(std η zero) = P(η_X zero | X_n=1)`, and
  there is **no PRA/Schoenfeld encoding, no Π⁰₁/witness machinery, no unprovability hedge**.

**On-disk state (unchanged this session; Lean files not edited).** `RiemannProof/RcpEuler.lean`
(radius-1, `eulerB` Euler product) is `sorry`-free; `RiemannProof/SchoenfeldPRA.lean` carries the
*old* PRA spine with 4 `sorry`s. The redesign **retargets** these — radius 1→2,
`eulerB`→general series, and the `SchoenfeldPRA` bridge **replaced** by the transfer equality
(so `schoenfeld`/`schoenfeld_primrec` 3.1 and the Π⁰₁ layer are *dropped*, not discharged).
Build last green at 8040 jobs (not rebuilt this pass; static read only — no `lake`/`pdflatex`).

**New obligation set (supersedes the three-load-bearer PRA accounting):** (1) the **transfer
equality** `P(std η zero at s₀) = P(η_X zero at s₀ | X_n=1)` (Mehler rcp at the *interior* mean
realization); (2) **`not_rcpZeroAt^{limit}` = Bagchi/Voronin universality**, local form
(`L ≠ 1`); (3) general-series convergence/holomorphy (assembly from `EtaConvergence` +
`SphereGaussian`); (4) final assembly to RH. The conclusion is now a **positive** RH in ZFC —
the deterministic zero-indicator is `{0,1}`, so `L ≠ 1 ⟹ = 0` — **not** the PRA route's
unprovability statement.

---

## The 2026-06-22 redesign (maintainer): radius-2 ball, non-multiplicative coefficients, ZFC-direct

Three maintainer changes **supersede the PRA/Schoenfeld spine (Phases 3–5) and the
radius-1 / Euler-product choices (Phase 0)**. The earlier sections — and the on-disk
`SchoenfeldPRA.lean` — are kept below for historical context, but the route's target and
bridge are now as stated here. None of this is on disk yet; it is the retargeting the
implementer must carry out.

**(R) Ball radius 2, not 1 — to put the mean realization in the INTERIOR of the support.**
`diskLaw` becomes the uniform law on the closed disk of radius **2** (`closedBall 0 2`), so
`priorBall := Measure.infinitePi (fun _ => diskLaw)` is supported on the radius-2 ball and the
mean realization `X_n ≡ 1` lies in the **open interior** of the support, not on its boundary.
This removes the radius-1 pathology: with radius 1, `ω ≡ 1` sat on `∂(unit ball)`, so the Tjur
neighborhood limit at the conditioning point was one-sided / degenerate; with radius 2 every
neighborhood of `ω ≡ 1` is a genuine two-sided interior neighborhood with positive mass in all
directions, so the regular-conditional limit at `X_n ≡ 1` is unambiguously well-defined.
Boundedness is preserved (`‖X_n‖ ≤ 2`), so the M-test / absolute convergence on `Re > 1` and
every downstream estimate go through with the constant `1 → 2`; nothing else in Phases 0–2
changes structurally. **Action:** `diskLaw` on `closedBall 0 2`; `priorBall_ball` becomes
`‖ω n‖ ≤ 2`; the support note in "The simplification" step 1 changes from "on the boundary —
in the support" to "in the *interior* of the support."

**(M) Non-multiplicative, general random Dirichlet series — the primary model, not optional.**
The object is `η_X(s) = ∑ X_n n^{-s}` (η-normalized) with **independent, uniformly bounded**
coefficients `‖X_n‖ ≤ 2`, mean `E[X_n] = 1`, and a chosen covariance — **no Euler product, no
multiplicativity**. The mean realization `X_n ≡ 1` is the standard `η`. `eulerB` (the
exponential Euler product) is now only a legacy special case; every claim is a property of
`(mean, covariance)`. Convergence/holomorphy on `1/2 < Re ≤ 1` is the Kolmogorov-one-series /
`L²` assembly detailed under "The general model" below (independent + centered + summable
variance `∑ Var(X_n) n^{-2σ} < ∞` for `σ > 1/2`), reusing `EtaConvergence.lean` (mean series)
and `SphereGaussian.lean` (independence/variance). This **replaces `bSum_tail_small`/`eulerB_*`
as the convergence layer.**

**(Z) Drop PRA — work directly in standard ZFC complex analysis; the bridge becomes a
measure-theoretic transfer EQUALITY.** The target is the **standard** Riemann Hypothesis stated
analytically (`∀ s, η s = 0 → 1/2 < Re s < 1 → Re s = 1/2`, or the `ζ` form), **not** the
Schoenfeld `Π⁰₁` sentence `RH_PRA`. There is **no** `schoenfeld`/`schoenfeld_primrec` (3.1
dropped), no `Σ⁰₁` witness extraction, no `interpPi01`/arithmetic-invariance, and **no
unprovability hedge**. The role of the Mehler probability measure is exactly one theorem — the
**transfer equality**:
```
P( standard η has a zero at s₀ )  =  P( η_X has a zero at s₀  |  X_n = 1 for all n )
```
where the right side is the regular-conditional (Tjur neighborhood) limit at the mean
realization — well-defined because (R) puts `X_n ≡ 1` in the *interior* of the support and the
substrate is Radon/Mehler. The **left side is a deterministic `{0,1}` indicator** (the standard
`η` either vanishes at `s₀` or not). The route's existing non-detectability result then applies
to the RIGHT side:

* `not_rcpZeroAt^{limit}` = **Bagchi/Voronin universality** (local form, max-modulus dodge)
  gives `L := P(η_X zero at s₀ | X_n=1) ≠ 1` — a positive-mass set of zero-free realizations
  matches the conditioning but is nonzero at `s₀` (full support of the chosen law; no Euler
  product needed).
* By the transfer equality `P(std η zero at s₀) = L ≠ 1`; since the left side is a `{0,1}`
  indicator, `≠ 1 ⟹ = 0`, i.e. **standard `η` has no zero at `s₀`**.
* Uniform over `1/2 < Re s₀ < 1` ⟹ **RH** — a positive theorem in ZFC, not an unprovability
  statement.

**Why the transfer equality holds (the one new load-bearer).** Conditioning the random series
on `X_n ≡ 1` (the Tjur limit at the mean) recovers the deterministic series `η`: the rcp at an
*interior* support point of an atomless Radon measure returns the deterministic value of any
measurable functional that is continuous at that point. "Has a zero at `s₀`" is such a
functional (evaluation is continuous in the locally-uniform-convergence/holomorphy topology),
so its conditional probability equals the deterministic indicator `1{η(s₀)=0}`. The Mehler
measure makes this rcp well-defined (Radon); the interior radius-2 support makes the limit
two-sided/unambiguous. This `P(zero | X=1) = 1{η(s₀)=0}` equality is the **replacement for the
old Schoenfeld bridge 4.1** (`counterexample_iff_rcpZero`).

**New obligation set (replaces the three-load-bearer PRA accounting).**
1. **Transfer equality** `P(std η zero at s₀) = P(η_X zero at s₀ | X_n=1)` — the new bridge.
   LOAD-BEARING. (Mehler rcp at the interior mean realization; replaces `counterexample_iff_rcpZero`.)
2. **`not_rcpZeroAt^{limit}` = Bagchi universality, local form** — `L ≠ 1`. LOAD-BEARING.
   (Unchanged from the PRA plan except the conclusion is now positive, not unprovability.)
3. **General-series convergence/holomorphy** — assembly from `EtaConvergence` + `SphereGaussian`.
   Assembly, not fresh debt.
4. **Final assembly** — (1)+(2)+two-valuedness of the indicator ⟹ RH; uniform over the strip.

**Dropped relative to the PRA plan:** `schoenfeld`/`schoenfeld_primrec` (3.1), `RH_PRA`/
`RH_PRA_holds` as the target, the `interpPi01`/`pi01_invariant` Π⁰₁ layer, the `Σ⁰₁`
witness-extraction argument, the `counterexample_iff_rcpZero` bridge, and the
unprovability/independence framing. The Kopperman formalism remains available for the
foundation-invariance of the rcp, but the route no longer routes through a Π⁰₁ arithmetic
sentence.

**★ DESIGN NOTE (2026-06-22) — the two load-bearers MUST share one rcp object `L`, or the
final assembly does not type-check.** This is the single most important thing to get right
when implementing the redesign, and it is the subtlety the `zetanew.tex` reframe surfaced.
Define **one** conditional-probability object
```lean
-- T = local edge trace on a non-s₀-enclosing arc Λ ⊂ ∂R; e_η = trace of the mean realization X_n≡1
noncomputable def L (s₀ : ℂ) : ℝ≥0∞ :=   -- the rcp at the interior mean realization
  rcpKernel s₀ Λ e_η {z | z = 0}          -- = rcp(η_X(s₀)=0 | T = e_η)
```
and state **both** load-bearers against *this same* `L`:
* **(1) transfer equality:** `L s₀ = (if etaStd s₀ = 0 then 1 else 0)`  — `L` *equals* the
  deterministic `{0,1}` indicator;
* **(2) Bagchi non-detection:** `L s₀ ≠ 1`.
Then the **final assembly is a three-line `by_contra`**: assume `etaStd s₀ = 0`; (1) gives
`L s₀ = 1`; (2) gives `L s₀ ≠ 1`; contradiction ⇒ `etaStd s₀ ≠ 0`; generalize over the strip ⇒ RH.
**Pitfall to avoid:** do *not* let (1) condition on the *full/global* `X_n≡1` (all coordinates)
while (2) conditions on a *local* arc — that would make them two different objects `L_full`,
`L_local` and the contradiction would be a non-sequitur. Both must condition on the **same local,
non-`s₀`-enclosing** edge trace `T` at the **same** value `e_η`. The transfer equality is the
*nontrivial* claim that *even this local conditioning* recovers the deterministic value
(rcp-at-interior-support principle); Bagchi is the claim that it does *not* reach `1`. Their
**conjunction** is what forces `etaStd s₀ ≠ 0` — neither input alone is suspicious, and the
tension between them *is* the theorem. State `L` once, in `RcpEuler.lean`, and import it into both
lemmas. (`max-modulus dodge`: the locality of `Λ` is what keeps (2) from collapsing to `L = 1`;
the radius-2 interiority of `e_η` is what makes (1)'s Tjur limit two-sided/well-defined.)

**`zetanew.tex` is now ALIGNED with this redesign (reframed 2026-06-22).** The paper presents
exactly this ZFC-direct, transfer-equality route (general non-multiplicative `η_X`, radius-2 prior,
`L = 1{η(s₀)=0}` ∧ `L ≠ 1` ⇒ positive RH); §3 is the transfer equality, §4 Bagchi, §5 the
`by_contra` assembly, §6 the recast Kopperman/Mehler tutorial (no Π⁰₁/unprovability), §7 the honest
Lean status. Static-checked only (no `pdflatex`). Keep plan and paper in sync on the shared-`L`
framing above.

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

1. **The deterministic `η` is the point `X_n = 1 for all n`, and it is in the INTERIOR
   of the support of the prior (radius-2 redesign (R)).** The genuine series for `η` is
   `η_X` evaluated at the coefficient sequence `ω ≡ 1` (all `X_n = 1`). Since `priorBall`
   is now the product of uniform laws on the closed disk of radius **2**, `ω ≡ 1` lies in
   the **open interior** of the support — every two-sided neighborhood has positive mass in
   all directions (the radius-1 boundary pathology is gone). So the neighborhood limit at
   `T = e_η` (the trace of `η`) is **defined and unambiguous** (Tjur's "only on the support"
   clause is met with room to spare — this is exactly what Phase 1.3 should say, restated).

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
* **N2 — bounded coefficients are the whole point (radius 2, see redesign (R)).** Values
  in the closed disk of radius **2** give, for *every* `ω`, absolute and locally uniform
  convergence of `∑_{n>N} X_n(ω) n^{-s}` on `{Re ≥ a > 1}` (dominated by `2·∑_{n>N} n^{-a}`).
  This is the unconditional right-edge convergence the Gaussian model only had a.s. The
  bound `2` (not `1`) is what places the mean realization `X_n ≡ 1` in the *interior* of the
  support; boundedness — not the value of the radius — is what is critical.
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

> **⚠ PHASE 3 IS DROPPED FROM THE SPINE (2026-06-22 redesign (Z)).** The route no longer
> encodes RH as a `Π⁰₁` Schoenfeld sentence: `schoenfeld`/`schoenfeld_primrec` (3.1) and the
> `Pi01`/`interpPi01`/`pi01_invariant` layer (3.2) are **not** part of the new ZFC-direct
> route, whose bridge is the measure-theoretic transfer equality (redesign (Z), Phase 4
> banner). The on-disk `SchoenfeldPRA.lean` retains this material; it is no longer a load-
> bearing obligation (3.1's two `sorry`s are *dropped, not discharged*). Everything below is
> **historical** — do not implement it for the new target.

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

## Phase 4 — The bridge

> **⚠ THE BRIDGE IS REPLACED BY THE TRANSFER EQUALITY (2026-06-22 redesign (Z)).** The
> load-bearing bridge is **no longer** `counterexample_iff_rcpZero` (a `Π⁰₁`-counterexample
> ⟺ rcp-zero). It is the measure-theoretic **transfer equality**
> ```lean
> theorem transfer_equality (s₀ : ℂ) (hs₀ : 1/2 < s₀.re) (hs₀' : s₀.re < 1) :
>     (P { ω | η_X s₀ ω = 0 } ∣ T = e_η)   -- rcp at the interior mean realization X_n ≡ 1
>       = (if etaStd s₀ = 0 then 1 else 0)  -- the deterministic {0,1} indicator
> ```
> i.e. `P(η_X zero at s₀ | X_n=1) = 1{etaStd s₀ = 0}`. **Recipe:** the rcp at an *interior*
> support point (redesign (R)) of the atomless Radon Mehler measure returns the deterministic
> value of any functional continuous there; "zero at `s₀`" is continuous in the locally-
> uniform/holomorphy topology (Phase 1.4-style convergence), so the conditional probability
> collapses to the deterministic indicator. Combined with `not_rcpZeroAt^{limit}` (`L ≠ 1`,
> Phase 2.2 = Bagchi) and the two-valuedness of the indicator, this yields **`etaStd s₀ ≠ 0`**
> directly — a *positive* RH in ZFC, with no `Σ⁰₁` witness extraction and no unprovability
> hedge. The eq1/eq2 / `interpPi01` / Schoenfeld material below is **historical**; the
> *general-model*, *substrate-via-Mehler*, *Bagchi-universality*, and *max-modulus-dodge*
> paragraphs below remain in force (they describe load-bearers (2)–(3) of the new set).

* **4.1 [HISTORICAL — replaced by `transfer_equality`] The correspondence.** The single
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

  **2026-06-19 maintainer refinement — the LIMIT notion of `rcpZeroAt`, the eq1/eq2
  proof of 4.1, and the `not_rcpZeroAt` re-statement (supersedes the "2.2 proved / 4.1
  sole load-bearer" framing above).** Three corrections settled in discussion:

  1. **`rcpZeroAt` is the LIMIT (eventual-`k`) notion, NOT the on-disk `∀k` joint-mass
     `Prop`.** The on-disk `rcpZeroAt` (2.1) quantifies `∀ r>0, ∀ k, 0 < priorBall{… eulerB
     (P k) …}`. That `∀k` includes the fixed first cutoff `k=0`, where `eulerB (P 0) s₀ ·`
     is a finite product bounded below by a positive constant `r₀` on the prior support —
     so the `k=0` event is null and `rcpZeroAt^{∀k}` is **unconditionally false**,
     regardless of whether `η(s₀)=0`. Hence the on-disk pair (`∀k`-`rcpZeroAt`,
     `not_rcpZeroAt` proved by selecting `k=0`) is **trivial**: it loads *all* content onto
     the bridge, making 4.1 literally equivalent to `RH_PRA`. The substantive object is the
     **eventual/limit** form — positive mass for large `k` (as `P k → ∞`). Restate
     `rcpZeroAt` as `∀ r>0, ∀ᶠ k in atTop, 0 < priorBall{…}` (or a `liminf`/subsequence
     form).

  2. **Under the limit notion the detection is genuine, in the exponential model, through
     the centering.** `Re cCorr_P(s₀) = log|η^E_P(s₀)| → log|η(s₀)|`. If `η(s₀)=0` (a true
     zero = counterexample, via Schoenfeld at the mean realization), then `|η^E_P(s₀)|→0`,
     so `Re cCorr_P(s₀)→−∞`, and the threshold in `‖eulerB(P)s₀ω‖<r` (i.e.
     `Re bSum_P(s₀,ω) < log r − Re cCorr_P(s₀) → +∞`) is satisfiable on a set of mass `→1`;
     jointly with edge-closeness near the mean realization this gives positive mass at large
     `k`. So `rcpZeroAt^{limit} ⟺ η(s₀)=0 ⟺ counterexample` — the bridge 4.1 is **real** for
     the limit notion.

  3. **`not_rcpZeroAt` (2.2) must be RE-STATED for the limit notion, and is then
     LOAD-BEARING — not the proved one-liner.** The on-disk proof of `not_rcpZeroAt` picks
     `k=0`; that works *only* for the `∀k` form. For the limit form, `¬ rcpZeroAt^{limit}`
     asserts "no large-`k` mass accumulates at `s₀`," i.e. `η(s₀)≠0` — **RH itself**, uniform
     in `s₀`. The analytic content does not vanish; the quantifier choice merely moves it:
     `∀k` trivializes 2.2 and loads 4.1; eventual-`k` makes 4.1 genuine and loads 2.2.
     **Treat the on-disk `not_rcpZeroAt` as a PLACEHOLDER** (correct for the trivial form,
     not the substantive one); its limit restatement is a second load-bearing obligation
     alongside 3.1 and the bridge.

  **The 4.1 proof structure (eq1/eq2), confirmed.** Prove `counterexample_iff_rcpZero`
  via two conditional-probability-`1` statements, conditioned on the mean (`X_n≡1`)
  realization:
  - `P(counterexample ∣ X_n≡1 ∧ ∃ s₀, η_X(s₀)=0) = 1`
  - `P(¬counterexample ∣ X_n≡1 ∧ ¬∃ s₀, η_X(s₀)=0) = 1`

  These are Schoenfeld's `RH_PRA ⟺ RH` evaluated at the mean realization (deterministic,
  value in `{0,1}`), embedded in the rcp formalism. Legitimacy of conditioning on the null
  point `X_n≡1`: Tjur, since `X_n≡1` is in the *support* of the trace law (Radon/Mehler
  substrate — the surviving content of Phase 1.3). The counterexample event is
  `ω`-independent — that is the *enabling* fact (it is why `interpPi01` is content-free /
  `Iff.rfl`, and why the prior law is free to choose); writing `P(event)=1` for the
  deterministic event is the correct Kopperman move.

  **The general model (maintainer).** The `X_p` need NOT come from an Euler product, and
  need NOT be **multiplicative**. The substrate is any random **Dirichlet series**
  `∑ X_n n^{-s}` whose coefficients are **uniformly bounded `‖X_n‖≤1` (CRITICAL, not
  optional)** — boundedness gives absolute every-`ω` convergence on `Re s > 1` (the
  `M`-test `bSum_tail_small`), which anchors the series to the genuine `η` (whose Dirichlet
  series converges there); WITHOUT it nothing about `η` can be concluded. Inside the strip
  `1/2<Re≤1` absolute convergence fails — there it's Kolmogorov one-series (summable
  variance, bounded ⇒ var bounded ⇒ summable for σ>1/2). Multiplicativity / `X_2=1` is kept
  for exposition only. The model is specified, Mehler/Kopperman-style, by two moments:
  - **mean** = the `X_n≡1` realization (the deterministic target series), used as the
    conditioning center;
  - **variance/covariance** = `E[(series − mean)²]`, the chosen law.

  "Choosing the law = choosing the model." The Fock-space variance-→-0 picture (first `P`
  modes pinned, `p>P` free) is one admissible covariance; the route's conclusion is a
  property of `(mean, covariance)`, not of any Euler product.

  **Substrate via the Mehler formalism — existence is GIVEN; only the rcp-limit family is
  needed (maintainer, 2026-06-19).** Do **not** build a basis. The **Mehler formalism already
  guarantees** the separable Hilbert substrate and the existence of its basis — even in the
  NON-Gaussian (uniform-on-disk, bounded) case `H = L²(priorBall)`
  (`priorBall = Measure.infinitePi (fun _ => diskLaw)`); this is exactly what the Mehler
  construction (`SphereGaussian.lean`) plus separability (`l2_separable`-style) supply, with no
  need for Gaussian-specific Hermite/Zernike polynomials. So there is **no ONB-construction
  obligation, no orthonormal-pair exhibition, no completeness, no separability proof**.
  - **What is actually needed: a family of vectors usable in the rcp limit.** The only concrete
    requirement is the family that populates the Tjur neighborhoods of `e_η` and supplies the
    alternative averages — the **finite indicator-tensor approximants** (`⊗_n φ_{α_n}`, `α`
    finitely supported, `φ_k` indicator functions of subsets of the disk = uniform distributions
    on subsets of the original ball; trivial factors `= 1`). These are just the conditioning /
    skeleton vectors already in play in the rcp machinery (`rcpKernel`, `edgeNbhd`); they need
    no orthonormality or completeness property — only to be available as the vectors over which
    the rcp limit `L = lim_V P(A∩V)/P(V)` is taken.
  - **Consistency to the original uniform law (the one fact to keep).** The finite-coordinate
    marginals of these indicator tensors reconstruct the original uniform-on-ball law: their
    Kolmogorov extension is exactly `priorBall`, and the unconstrained coordinates always carry
    the *original* `diskLaw`. Formally `Measure.infinitePi` + `Measure.infinitePi_pi`, already
    used in `RcpEuler`. (This is what the maintainer's "a basis vector is a tensor product of
    uniform-on-subsets, and it is always the original uniform on the ball" amounts to.)
  - **Payoff:** `H` is separable (countable ONB = finitely-supported multi-indices over the
    countable single-coordinate indicator basis) and carries a **decidable dense skeleton**
    (finite rational combinations of indicator tensors with rational subsets — computable),
    satisfying `Formalism.separable` / `skeleton_*`. This *replaces* the current
    `rcpFormalism`'s abstract `Classical.choose exists_atomless_prob_substrate` with the
    concrete bounded-prior substrate. Template: `SphereGaussian.lean` (the Mehler/Gaussian
    construction to mirror); ONB technique: `Kopperman.substrate_orthonormal_pair`; measure:
    `priorBall`. The indicator (Haar/martingale) basis is the right choice precisely because it
    is **measure-agnostic** (works for the non-Gaussian uniform law) and **computable** (fits
    the decidable-skeleton requirement) — whereas a polynomial ONB would be measure-specific.

  **Scaffolding cost of the general model — convergence via Kolmogorov's one-series theorem
  (maintainer, 2026-06-19).** Dropping the Euler product means `bSum_tail_small` (the
  `M`-test), `eulerB_differentiableOn` (analyticity), and the contour lemma
  `rcp_recipEulerB_tendsto_recipEta` no longer come for free from product structure; the
  general random Dirichlet series `∑ X_n n^{-s}` needs its own convergence/analyticity
  scaffolding. **What makes it work: the `X_n` are uncorrelated** (independent under
  `priorBall`), with mean `E[X_n]=1` and bounded variance, so the centered series
  `∑ (X_n − 1) n^{-s}` has term-variances `Var(X_n)·n^{-2σ}`, which are **summable for
  `σ = Re s > 1/2`** — exactly the strip threshold (same `Re > 1/2` boundary as the Gaussian
  route's `∑ p^{-2σ}`). Two convergence routes, with their Mathlib status:
  - **L² route (the natural one for a second-order `(mean,covariance)` model).** Uncorrelated
    ⇒ orthogonal increments ⇒ partial sums Cauchy in `L²` ⇒ converges in `L²` on `Re s > 1/2`.
    Supported by Mathlib's inner-product / `Mathlib.Analysis.InnerProductSpace.l2Space`
    orthogonal-series API. This is sufficient because the model is specified by two moments.
  - **a.s. route (Kolmogorov's one-series theorem).** Independent + centered + `∑ Var < ∞`
    ⇒ `∑` converges a.s. **Mathlib has no named three-/one-series theorem**, but the partial
    sums form an `L²`-bounded martingale, so Mathlib's **martingale convergence**
    (`Submartingale.ae_tendsto` / a.e. martingale convergence) yields the a.s. limit — the
    modern proof of Kolmogorov's theorem. (Merely-uncorrelated a.s. convergence instead needs
    Rademacher–Menshov, `∑ Var·(log n)² < ∞`; `priorBall` gives independence, so the martingale
    route is cleaner.)
  - **Holomorphy of the limit** on `Re > 1/2`: upgrade the above to locally-uniform
    convergence (Dirichlet-series convergence-abscissa argument) then `TendstoLocallyUniformly
    ⇒ DifferentiableOn`. Mathlib has the local-uniform ⇒ holomorphic implication; the
    local-uniformity itself is the work.

  **PRIOR ART — this scaffolding is LARGELY ALREADY IN THE PROJECT (maintainer: "used before";
  reuse, do not re-prove).** The two ingredients of the Kolmogorov-one-series argument are each
  already discharged here:
  - **Deterministic Dirichlet-series side (the mean `X_n≡1` series), on `Re > 1/2`:**
    `RiemannProof/EtaConvergence.lean` — `summable_etaPairedTerm` (summability for `Re s > 1/2`,
    the exact `n^{-σ}` bound that doubles as the summable-variance estimate via
    `norm_etaPairedTerm_le`), `paired_tendstoUniformlyOn` (locally-uniform convergence on
    compacts), and `analyticOnNhd_paired_tsum` (analyticity on `{Re > 1/2}`). This is the mean
    series and the local-uniform/holomorphy upgrade, done.
  - **Independent-product / variance side (the Mehler law):** `PnpProof/SphereGaussian.lean` —
    `gammaMeasure` (the i.i.d. infinite Gaussian product = the Mehler measure), `iIndepFun_infinitePi`
    (independence of coordinates), `variance_id_gaussianReal` (the per-coordinate variance), and
    `poincare_borel_ae` (the a.s. sphere→Gaussian convergence, the SLLN-flavored a.s. machinery).
  So the random-series convergence is an **assembly of existing results** (mean from
  `EtaConvergence`, summable variance from the same `n^{-σ}` bound, independence/variance from
  `SphereGaussian`), not a from-scratch obligation. This scaffolding **replaces** `0.2′
  bSum_tail_small` for the general model. (`not_rcpZeroAt` uses universality, not the Euler
  product — see the correction in the next paragraph.)

  **`not_rcpZeroAt^{limit}` = Bagchi universality, on a LOCAL neighborhood (maintainer,
  2026-06-19).** The limit form of `not_rcpZeroAt` is `L ≠ 1`, i.e. among the realizations
  consistent with the conditioning there is a **positive-mass subset bounded away from `0`
  at `s₀`** — an *alternative average*: a zero-free random Dirichlet series that matches
  the conditioning data but does **not** vanish at `s₀`. Its existence is **Bagchi/Voronin
  universality** (the random series' support is all zero-free holomorphic functions on a
  connected-complement compact). The closest existing formal statement is the deprecated
  Gaussian route's `univ-core` (`eulerG_universality_threeLeftEdges`) — reuse it as a
  starting point. **The Euler product is NOT actually required, and neither is
  multiplicativity (maintainer, 2026-06-19, correcting the previous note):** Bagchi-type
  universality applies to general random Dirichlet series, so what supplies the zero-free
  alternative is the **full support of the chosen prior law** (its covariance), not any
  Euler-product/multiplicative structure. Multiplicativity / `X_2=1` is kept for exposition
  only; it would matter solely if the proof *relied* on the Euler product — which it does
  not, here or in the bridge.

  **The max-modulus constraint, and the dodge.** If one conditioned on the *full* rectangle
  boundary `∂R` with holomorphic realizations, max-modulus would force `|f − η| < ε` on the
  whole interior, hence `|f(s₀)| < ε` — pinning the interior to `η(s₀)=0`, giving `L → 1`,
  and `not_rcpZeroAt` would be `≡` RH. The dodge (maintainer): **condition only on a LOCAL
  neighborhood of a point** — no enclosing contour, so max-modulus never pins `s₀`. **No
  specific shape or size is required** (the three-edge `threeLeftEdges` "U"-arc is one
  instance, but any local, non-`s₀`-enclosing, connected-complement set works). Re-type the
  on-disk `rcpZeroAt` (which conditions on the full `R.closure \ R.openInt`) to such a local
  set.

  **Conclusion is UNPROVABILITY only.** `L ≠ 1` says a zero at `s₀` *cannot be forced to
  conditional-probability `1`*, i.e. **cannot be proved** in the model — NOT that there is no
  zero. Via the bridge + the `Σ⁰₁` witness property this gives "no counterexample is
  provable," i.e. the `Π⁰₁` Schoenfeld sentence has no disproof; the further step to "`RH_PRA`
  is *true*" is the model/T-conservativity reading (already flagged). The route's two deep,
  un-formalized analytic inputs are therefore **Schoenfeld 1976** (bridge 4.1) and **Bagchi
  1981 universality** (non-detection 2.2, local form).

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

## Build order & status — REDESIGNED MAP (2026-06-22)

Legend: `✓` on disk / done · `□` open `[LB] sorry` · `↻` on disk but **retargeted** by the
redesign (def change) · `✗` **dropped** from the spine (historical, not discharged).

```
(R) diskLaw radius 1→2; priorBall_ball ‖ω n‖≤2     ↻ def   FIRST mechanical change (redesign R)
(M) eulerB → general η_X = ∑ X_n n^{-s}            ↻ def   non-multiplicative; eulerB now legacy special case
0.2′/conv  general-series convergence/holomorphy   □ LB    ASSEMBLY: EtaConvergence (mean) + SphereGaussian (var); replaces bSum_tail_small
0.3a diskLaw, priorBall, isProb, _ball, _atomless  ↻ LB    PROVED at radius 1; re-prove at radius 2 (mechanical)
0.3b rcpPriorOnSubstrate (Mehler substrate)        ✓ LB    existence GIVEN by Mehler — no construction obligation
2.1  rcpZeroAt — LIMIT notion, LOCAL neighborhood  ↻ def   eventual-k + non-s₀-enclosing set (max-modulus dodge)
2.2  not_rcpZeroAt^{limit} = Bagchi local form     □ LB    LOAD-BEARER (2): L ≠ 1; reuse univ-core; full-support alternative average
4.1  transfer_equality  P(η_X 0 | X=1)=1{ηStd=0}   □ LB    LOAD-BEARER (1): rcp at INTERIOR mean realization; replaces counterexample_iff_rcpZero
5.x  riemann_hypothesis (standard, ZFC)            □ LB    ASSEMBLY: transfer_equality + (L≠1) + {0,1} two-valuedness, uniform over strip
---- dropped from the spine (historical, on disk in SchoenfeldPRA.lean) -------------------
3.1  schoenfeld, schoenfeld_primrec                ✗       Π⁰₁ encoding dropped (redesign Z) — 2 sorries removed, not discharged
3.2  Pi01/interpPi01/pi01_invariant                ✗       Π⁰₁ interpreter layer dropped
4.1' counterexample_iff_rcpZero                    ✗       PRA bridge replaced by transfer_equality
5.1/5.2  no_schoenfeld_counterexample, RH_PRA_holds ✗      RH_PRA target dropped
1.2/1.4  rcpKernel, rcp_recipEulerB_tendsto_recipEta ✓     reusable: 1.4-style locally-uniform convergence backs transfer_equality's continuity
```

**Load-bearing `[LB]` obligations after the redesign (two, + two assemblies):** (1)
`transfer_equality` (the new bridge), (2) `not_rcpZeroAt^{limit}` = Bagchi local form; plus
the general-series **convergence assembly** (`EtaConvergence` + `SphereGaussian`) and the
**final RH assembly**. **Dropped (not discharged):** `schoenfeld`/`schoenfeld_primrec` (3.1),
the Π⁰₁ layer (3.2), `counterexample_iff_rcpZero`, `RH_PRA`/`RH_PRA_holds`. **No substrate
construction obligation** — Mehler guarantees existence; only the indicator-tensor rcp-limit
family + `Measure.infinitePi`/`infinitePi_pi` consistency is used. **Wire-in / build:**
`RiemannProof.lean` imports both modules; last green at **8040 jobs (2026-06-18)** for the
*old* PRA spine — **not rebuilt this pass**; the redesign's def changes (radius, general
series, transfer equality) are **not yet on disk** (static read only — no `lake`/`pdflatex`).

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

1. **The exact prior `priorBall` — RESOLVED, but RADIUS 1→2 (redesign (R), 2026-06-22).** The
   prior is the **pure continuous** law `priorBall := Measure.infinitePi (fun _ => diskLaw)`,
   an independent product of the uniform law on the closed disk of radius **2** (`diskLaw :=
   ProbabilityTheory.cond volume (closedBall 0 2)`; was `closedBall 0 1`); a probability
   measure, supported in the radius-2 ball, and **atomless** (`priorBall_atomless`). The
   radius-2 choice puts the mean realization `X_n ≡ 1` in the *interior* of the support
   (well-defined two-sided Tjur limit at the conditioning point). The on-disk file still uses
   radius 1 — the `closedBall 0 1 → closedBall 0 2` change is the first mechanical action. The
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
3. **Final target — RESET to standard ZFC RH (redesign (Z), 2026-06-22).** The target is the
   **standard analytic RH**, `∀ s, η s = 0 → 1/2 < Re s < 1 → Re s = 1/2` (or the `ζ` form),
   proved directly from the transfer equality + `not_rcpZeroAt^{limit}` (`L ≠ 1`) +
   two-valuedness of the deterministic zero-indicator. `RH_PRA`/`Π⁰₁`/Schoenfeld is **no
   longer** the target; `riemann_hypothesis_via_rcp` is now reached *without* the Schoenfeld
   1976 analytic equivalence (the conclusion is already in `η`/`ζ` terms).

## Recommended next steps (priority order) — REDESIGN (2026-06-22)

**State after the 2026-06-22 redesign.** The PRA three-load-bearer accounting (3.1 +
limit-form 2.2 + bridge 4.1) is **superseded**. The route is now ZFC-direct with **two
load-bearers** — the **transfer equality** and **`not_rcpZeroAt^{limit}` = Bagchi** — plus
two assemblies (general-series convergence; final RH). `schoenfeld`/Π⁰₁ (3.1/3.2) and the
`counterexample_iff_rcpZero` bridge are **dropped**, not discharged. The substrate is still
**not** an obligation (Mehler guarantees the separable `L²(priorBall)` and basis exist —
non-Gaussian included; only the indicator-tensor rcp-limit family is used).

1. **Apply (R) + (M) — the first mechanical def changes.** In `RcpEuler.lean`: (R) move
   `diskLaw` to `closedBall 0 2` and re-prove `priorBall_*` (radius-2; mechanical — the
   uniform-disk `infinitePi` proofs port verbatim with the constant), and (M) generalize the
   object from `eulerB` (Euler product) to the general random Dirichlet series
   `η_X s ω = ∑ X_n n^{-s}` with `‖X_n‖ ≤ 2`, mean 1. These two definition changes unblock
   everything else and put `X_n ≡ 1` in the *interior* of the support. No new `sorry` content.
2. **Define the shared object `L` ONCE, then state both load-bearers against it (★ DESIGN NOTE).**
   In `RcpEuler.lean` define `L s₀ := rcpKernel s₀ Λ e_η {0}` = `rcp(η_X(s₀)=0 | T = e_η)` for a
   **local, non-`s₀`-enclosing** edge arc `Λ` and the mean-realization trace `e_η`. Both 3 and 4
   below are stated against *this same* `L` — otherwise the final `by_contra` is a non-sequitur.
3. **Transfer equality (LOAD-BEARER 1) — the new bridge.**
   `transfer_equality : L s₀ = (if etaStd s₀ = 0 then 1 else 0)`. Recipe: the rcp at an
   *interior* support point (radius-2) of the atomless Radon Mehler measure returns the
   deterministic value of a functional continuous there; "zero at `s₀`" is continuous in the
   locally-uniform/holomorphy topology (reuse the 1.4-style convergence
   `rcp_recipEulerB_tendsto_recipEta` machinery — now phrased for `η_X`). The *nontrivial* claim
   is that **even the local conditioning** recovers the deterministic value. Leave `[LB] sorry`
   with this recipe; **do not improvise**. Replaces `counterexample_iff_rcpZero`.
4. **`not_rcpZeroAt^{limit}` (LOAD-BEARER 2) = Bagchi/Voronin universality, local form.**
   `L s₀ ≠ 1` (the SAME `L` as step 3): a positive-mass zero-free *alternative average* matching
   the conditioning data but nonzero at `s₀`. Reuse the deprecated Gaussian route's `univ-core`
   (`eulerG_universality_threeLeftEdges`) as the starting point. The **locality** of `Λ`
   (max-modulus dodge) is exactly what stops this collapsing to `L = 1`; **no Euler product or
   multiplicativity** (full support of the chosen prior law supplies the zero-free realization).
   Re-type `rcpZeroAt` (2.1) to the **eventual/limit** form on that local set. Leave `[LB] sorry`.
5. **General-series convergence/holomorphy — ASSEMBLY, not fresh debt.** Replacing `eulerB`
   means `η_X = ∑ X_n n^{-s}` needs its own convergence on `1/2 < Re ≤ 1`: independent +
   centered + summable variance `∑ Var(X_n) n^{-2σ} < ∞` (σ>1/2) ⇒ `L²`/martingale convergence,
   then locally-uniform ⇒ holomorphic. Assemble from `EtaConvergence.lean`
   (`summable_etaPairedTerm`, `paired_tendstoUniformlyOn`, `analyticOnNhd_paired_tsum` — mean
   series + holomorphy) and `SphereGaussian.lean` (`iIndepFun_infinitePi`,
   `variance_id_gaussianReal` — independence/variance). Replaces `bSum_tail_small`.
6. **Final RH assembly (ZFC) — the three-line `by_contra` (★ DESIGN NOTE).** Assume `etaStd s₀=0`;
   transfer equality (step 3) gives `L s₀ = 1`; Bagchi (step 4) gives `L s₀ ≠ 1`; contradiction ⇒
   `etaStd s₀ ≠ 0`. Generalize over `1/2 < Re s₀ < 1` ⟹ standard RH (`∀ s, η s = 0 → 1/2 < Re s < 1
   → Re s = 1/2`, or the `ζ` form). Pure assembly — no `Σ⁰₁` witness extraction, no Schoenfeld 1976.
7. **Quarantine the PRA spine.** `SchoenfeldPRA.lean` (`schoenfeld`, `schoenfeld_primrec`,
   `Pi01`/`interpPi01`, `counterexample_iff_rcpZero`, `RH_PRA`/`RH_PRA_holds`,
   `riemann_hypothesis_via_rcp`) is **not** part of the new route. Either keep it isolated/
   unimported (historical) or remove it; do **not** spend effort discharging its 4 `sorry`s.

**Done / reusable (do not redo):** `rcpPriorOnSubstrate` Mehler substrate (existence GIVEN —
no construction obligation); the 1.4-style locally-uniform contour convergence (backs the
transfer equality's continuity step); `EtaConvergence` + `SphereGaussian` (the convergence
assembly's inputs). **Superseded / dropped:** the entire Π⁰₁/Schoenfeld spine, the
`counterexample_iff_rcpZero` bridge, the C2/C3/C4 `κ_sel`/Tjur/`ℕ→ℂ` apparatus, and the
unprovability framing — the conclusion is now a **positive** RH in ZFC.

**Net effect of the 2026-06-22 redesign.** Three maintainer changes: **(R)** radius 1→2 puts
the mean realization `X_n ≡ 1` in the *interior* of the support (kills the boundary pathology
at the conditioning point); **(M)** the model becomes the general **non-multiplicative** random
Dirichlet series `∑ X_n n^{-s}` (no Euler product); **(Z)** the route is **ZFC-direct** — target
is standard analytic RH, the bridge is the measure-theoretic **transfer equality**
`P(std η zero) = P(η_X zero | X_n=1)`, and the Π⁰₁/Schoenfeld/witness/unprovability machinery is
**dropped**. Obligation count: two load-bearers (transfer equality + Bagchi `L ≠ 1`) + two
assemblies (general-series convergence; final RH). The conclusion **strengthens** from the PRA
route's unprovability statement to a positive RH, because the deterministic zero-indicator is
`{0,1}` and `L ≠ 1 ⟹ = 0`. None of the (R)/(M)/(Z) def changes are on disk yet; build last
green at **8040 jobs** for the *old* PRA spine (not rebuilt this pass; static read only — no
`lake`/`pdflatex`). No Lean was written here; this is plan retargeting.
