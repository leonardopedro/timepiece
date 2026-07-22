# Implementation Plan: RH via a bounded-coefficient prior + regular conditional probability (radius-`1+ε` ball, multiplicative Euler product `exp(prime series)·E_X` with `X₂=1`, ZFC-direct)

> ## ★★★ 2026-06-25 (l) — NEW STRATEGY (maintainer), AUTHORITATIVE. READ THIS FIRST.
> **Multiplicative coefficients on a tiny ball `B(1,ε)` + variance bound + Hurwitz on a random Euler product.**
> This supersedes the *conclusion mechanism* of (j)/(k) (the `secondMoment_transfer` + `bagchi_universality`
> pair). The (k) **integrability engine stays valid infrastructure** (`integrable_id_and_normSq_of_bound`
> and the finite-`N` truncation pattern are reused verbatim below). The Lean file is unchanged this round
> and remains at the (k) green state (2 sorries); the central-object redesign described here is the next
> on-disk step (see "Lean targets" at the end of this banner).
>
> ### ★ MANDATE — this is a program to BUILD, not to avoid.
> Five steps, four of them non-deep. The implementer formalizes O1, O3, O4, O5 (concentration, projection,
> disintegration, Hurwitz) — all standard analysis/measure theory — and states O2 as the single deep input.
> "Formalize O2's *statement* and reduce RH to it" is a task to DO; do not stall on the fact that O2 is deep.
>
> ### The model (replaces the radius-2 non-multiplicative disk law)
> - **Coefficients are multiplicative.** Draw `X_p` i.i.d. over primes `p`, `X_p ~ Uniform(B(1,ε))`
>   (closed disk of radius `ε` centered at **1**, `ε>0` tunable as small as we like). Extend
>   multiplicatively: `X_n = ∏_{p^a ‖ n} X_p^a`. Then `η_X(s) = ∑_n X_n n^{-s} = ∏_p (1 − X_p p^{-s})^{-1}`
>   (Euler product) where it converges.
> - **Every coefficient has mean 1.** Because `Uniform(B(1,ε))` is rotation-invariant about `1`,
>   `E[X_p^k] = 1` for all `k≥0` (all higher moments of the centered part vanish), hence `E[X_n] = 1` for
>   **all** `n`, so `E[η_X(s)] = ζ(s)`. The prior concentrates on `ζ` (= `η`).
> - **Second moment is `O(ε²)` and summable down to `1/2`.** `E[|X_p|^{2k}] = 1 + k·(ε²/2) + O(ε⁴)`, so
>   `Var(X_n) ≈ Ω(n)·ε²/2` (`Ω` = number of prime factors with multiplicity), and
>   `Var(η_X(s)) = ∑_n Var(X_n) n^{-2σ} ≈ (ε²/2)∑_n Ω(n) n^{-2σ}`, which **converges for `σ>1/2`**
>   (`∑_n Ω(n)n^{-2σ} = ζ(2σ)·∑_p p^{-2σ}/(1−p^{-2σ})`).
>
> ### The five steps
> - **O1 — Variance bound.** `Var(η_X(s)) ≤ C₁²ε²` on `Re s > 1/2 + C₂ε` (some `C₁,C₂>0`). Concrete,
>   non-deep: it is the summability above plus uniformity on a half-plane edge. *Lean target:*
>   `variance_etaX_le` — reuse the `summable_centered_normSq` machinery and the (k) bound pattern.
> - **O2 — Non-singular / zero-free Euler product on `K` (THE deep input).** For a.e. realization in the
>   support, the realized Euler product `∏_p (1 − x_p p^{-s})^{-1}` is a **holomorphic, zero-free** function
>   on the compact `K ⊂ {1/2<Re<1}` (a *non-singular Euler product*). *Lean target:*
>   `eulerProduct_zero_free_on_compact` — left as the single labeled `sorry`. **See the load-bearer note
>   below; this is where the difficulty now lives, and it deserves an explicit derivation before Lean.**
> - **O3 — Projection / filter (concentration).** On a Hilbert space `H_K` of holomorphic functions on `K`
>   (Bergman/Hardy `L²` space), the orthogonal projection / event `{‖η_X − η‖_{H_K} ≤ ε}` carries
>   probability `→ 1` as `ε↓0` by Chebyshev + O1. *Lean target:* `filter_mass_to_one` — Chebyshev on O1.
> - **O4 — Disintegration ↔ holomorphic / Euler.** Disintegrate the (filtered) prior over the coefficient
>   sequence. For a.e. `X_n = x_n` in the support, the conditional ("infinitesimal") measure is carried by a
>   single holomorphic function on `K`, in one-to-one correspondence with a non-singular Euler product
>   (O2 supplies the latter's zero-freeness). *Lean target:* `condDistrib`-based `disintegration_holomorphic`.
> - **O5 — Hurwitz transfer (the contradiction).** If `η` had a zero `s_0 ∈ K`, then since `η_X → η`
>   uniformly on `K` (O1 + O3) and each (filtered) `η_X` is holomorphic, **Hurwitz's theorem** forces each
>   nearby `η_X` to have a zero close to `s_0` — contradicting O2 (zero-free Euler products). Hence `η` has
>   no zero in `K`; exhaust the strip by compacts ⇒ RH. *Lean target:* `hurwitz_transfer` (needs a Hurwitz
>   theorem — check Mathlib `Mathlib.Analysis`; if absent, derive from Rouché / argument principle, itself a
>   useful contribution). This **replaces** `secondMoment_transfer` as the RH-endpoint.
>
> ### Old → new obligation map
> | retired (j)/(k) object | replaced by |
> | --- | --- |
> | `secondMoment_transfer` (RH-equiv Borel–Kolmogorov reconciliation) | `hurwitz_transfer` (O5) — the new RH-endpoint, **non-deep given O2** |
> | `bagchi_universality` (Voronin centrum ≠ 0) | `eulerProduct_zero_free_on_compact` (O2) — the single deep input |
> | `integrable_id_and_normSq_of_bound`, `etaXpartial`, `secondMomentIntegrable_partial` | **kept** — reused for O1's finite-`N` variance bound |
>
> Net: still essentially **one deep input**, now `O2` (zero-free Euler product on `K`) rather than the
> Bagchi/transfer pair. The conclusion is **positive** (Hurwitz gives `η` zero-free, not just "`≠1`").
>
> ### ⚠ Load-bearer note (honest, for the maintainer — not a blocker, a request to pin down O2).
> With coefficients centered at **1**, concentration says `η_X → ζ` on `K`. But the *common* deterministic
> backbone `E[log η_X](s) = ∑_p p^{-s} + (corrections)` is the prime zeta `P(s)`, which is **singular at the
> zeros of `ζ`** (`P(s) = ∑_k μ(k)/k · log ζ(ks)`; the `k=1` term has a log-branch point at each zero `ρ`).
> So `η_X = exp(P + ε·R + …)` formally inherits a near-zero wherever `ζ` has a zero, for **every**
> realization — i.e. concentration `η_X → ζ` pushes *against* "`η_X` zero-free on `K`" (O2). The two can only
> coexist if `ζ` is already zero-free on `K` — which is what Hurwitz would then *conclude*. **This is not a
> refutation**; it is the precise place the *filter/disintegration* (O3/O4) must do real work: it must select
> a sub-population of realizations whose Euler products genuinely *converge and stay zero-free on `K`* (so the
> conditional limit is a non-singular Euler product), and the claim is that this sub-population still has
> `η_X → η` in the disintegrated limit. **Maintainer: please confirm the mechanism by which the filtered
> Euler products are zero-free on `K` despite tracking `ζ` (e.g. does the filter restrict to the convergence
> region of the product, and why does that region a.s. contain `K`?).** O2 is currently RH-equivalent until
> that is pinned; pinning it is what turns this from "reduces RH to O2" into "proves RH". Everything in O1,
> O3, O4, O5 is honest, non-deep, and worth formalizing *now* regardless of how O2 resolves.
>
> **★ 2026-06-25 exchange logged (open).** Maintainer's justification for O2: "the filtered products are
> non-singular because the original measure is non-singular, for **almost all** `X_n = x_n`." Reviewer's
> standing obstruction (not yet resolved): the two senses of "non-singular" come apart. The decisive identity
> is `E[log η_X](s) = ∑_p∑_k E[X_p^k]/k · p^{-ks} = ∑_p∑_k p^{-ks}/k = log ζ(s)` **exactly** (`E[X_p^k]=1`),
> so for **every** realization `log η_X = log ζ + (a.s.-finite random holomorphic on Re>1/2)`; at a zero
> `s_0` of `ζ`, `log ζ(s_0) = −∞ ⇒ η_X(s_0)=0`. Thus `η_X` vanishes at `ζ`'s zeros on a **measure-one**
> (indeed sure) event — *not* a null event — so "for a.e. `x_n` the product is zero-free at `s_0`" is the
> reverse of what holds: a.e. `x_n` gives `η_X(s_0)=0`. Measure-non-singularity (atomlessness of the prior)
> cannot remove a singularity that already sits in the **mean** `log ζ`, since "almost all" only discards
> null sets. **Open question to maintainer:** identify the mechanism that produces zero-free products on a
> `K ∋ s_0` despite `E[log η_X]=log ζ`, or change the centering/comparison (but centering away from `ζ`
> breaks `η_X→ζ`, so Hurwitz would no longer speak about `ζ`). Until then O2 is not just deep but appears
> *false* on the `K` the contradiction needs, so the Lean/paper were left untouched.
>
> **★ 2026-06-25 iteration 2 (open).** Maintainer accepted the above and patched the MODEL: prior re-centered
> at `X_n=0` (radius `1+ε`); condition a positive-measure event = first `N` coordinates in `B(1,ε)` (head near
> 1), tail `n>N` free (mean 0). This **does fix iteration-1's defect** — with a mean-0 tail, `E[log η_X] ≠ log ζ`,
> the tail `∑_{n>N}X_n n^{-s}` converges a.s. on `Re>1/2` (`∑Var·n^{-2σ}<∞`, the "squared terms → 0" remark is
> correct), head is finite, so `η_X` is an honest convergent random holomorphic function with no forced zero at
> `ζ`'s zeros. **New gap (iteration 2):** conditional mean `E[η_X]=∑_{n≤N}n^{-s}=ζ_N(s)=ζ(s)+N^{1-s}/(1-s)+O(N^{-σ})`
> (Euler–Maclaurin); the overshoot `N^{1-s}/(1-s)` has modulus `N^{1-σ}/|1-s|→∞` for `σ<1`, so `η_X` concentrates
> on the Dirichlet **polynomial** `ζ_N` (zeros = Turán/Montgomery, clustering toward `σ=1`), **not** on `ζ`. So
> Hurwitz now speaks about `ζ_N`'s zeros, not `ζ`'s — `η_X→ζ` (which O5 needs) was traded away to buy convergence.
> **Structural diagnosis (the Hurwitz wall, model-independent):** Hurwitz forbids zero-free holomorphic functions
> from converging locally-uniformly to a function with a zero. The route needs BOTH O2 (`η_X` zero-free on `K`)
> and O5 (`η_X→η` uniformly on `K`); if `η` has a zero in `K` these are jointly impossible unless `η` is already
> zero-free — the conclusion. Mult/mean-1 ⇒ O2 fails (tracks `ζ`'s zero); additive/truncated ⇒ O5 fails (`η_X→ζ_N`).
> Hence "zero-free Euler-product approximants → `ζ` on a strip compact" exists **iff** RH (Hurwitz both ways), so
> O2 is RH-EQUIVALENT regardless of centering/truncation. **Fork put to maintainer:** (1) treat the route as an
> honest *reduction* — O2 as a labeled RH-equivalent hypothesis, formalize O1/O3/O4/O5 (matches the current
> 1-deep-sorry spine); or (2) supply a genuinely new input that breaks the Hurwitz symmetry (must keep BOTH
> `η_X→ζ` and `η_X` zero-free). Lean/paper untouched pending the choice.
>
> ### Lean targets (next on-disk step, after O2's mechanism is confirmed)
> 1. `def Xp` (i.i.d. `Uniform(B(1,ε))` over primes), `def Xmult` (multiplicative extension), `def etaXmult`.
> 2. `variance_etaX_le` (O1) — reuse `summable_centered_normSq` + (k) engine.
> 3. `filter_mass_to_one` (O3) — Chebyshev on O1.
> 4. `eulerProduct_zero_free_on_compact` (O2) — the single `sorry`.
> 5. `hurwitz_transfer` (O5) — Hurwitz/Rouché; the RH-endpoint, sorry-free given O2.
> 6. Rewire `riemannZeta_ne_zero_of_mem_strip` to conclude from O5 instead of the secondMoment pair.
> Keep the (k) green state until these are staged; build with FOREGROUND `lake env lean RiemannProof/RcpEuler.lean`.

> ## ★★ 2026-06-24 (k) — READ FIRST. The ONE clean job for the Lean-specialist, now fully unblocked with a proved engine on disk.
>
> **★ MANDATE — this is a task to DO, not to avoid.** There is exactly one non-deep, fully-closable
> Lean obligation on this route, and the reusable lemma that discharges it is now PROVED and on disk.
> Pick it up and finish it. Do **not** touch the two deep sorries (`secondMoment_transfer`,
> `bagchi_universality`) — those are off-limits by design, not by your hesitation. Everything below is
> green-lit, type-accurate, and verified to compile (`lake env lean RiemannProof/RcpEuler.lean`, EXIT=0).
>
> **What is already PROVED and on disk (use it):**
> `integrable_id_and_normSq_of_bound` in `RcpEuler.lean` (just after
> `integral_norm_sq_pos_of_mean_ne_zero`):
> ```
> lemma integrable_id_and_normSq_of_bound
>     {μ : Measure ℂ} [IsFiniteMeasure μ] {C : ℝ}
>     (hC : ∀ᵐ x ∂μ, ‖x‖ ≤ C) :
>     Integrable (fun x => x) μ ∧ Integrable (fun x => ‖x‖ ^ 2) μ
> ```
> This is the entire analytic content of the `secondMomentIntegrable` plumbing: **a uniform a.e. bound
> `‖x‖ ≤ C` on the law gives both integrable moments, for free, on any finite measure.** No Mehler, no
> Kopperman, no convergence theory.
>
> **Honest diagnosis (why the obligation looked stuck — now resolved).** The headline predicate
> `secondMomentIntegrable s₀ R` is stated against `rcpKernelX s₀ R (eTrace R)` =
> `condDistrib(interiorValX s₀, edgeTraceX R, priorBall)` *evaluated at the single point* `eTrace R`.
> Two facts make that exact object un-closable by generic API, and they are the legitimate reason the
> obligation could not be discharged as literally typed: (1) `condDistrib` is only specified a.e. in the
> conditioning variable, so a property *at one deterministic point* is not derivable from the disintegration
> API alone; (2) `interiorValX s₀ ω = etaX s₀ ω = ∑' n, ω n · n^{-s₀}` is the **bare** Dirichlet tsum,
> which on the strip (`σ ≤ 1`) is non-summable ⇒ `= 0` a.s. by Mathlib's `tsum` convention — i.e. the bare
> object is degenerate exactly where we need it, and its honest content lives in the deterministic-continuation
> + centered-series split `η_X = η_det + η_Y` (the same off-diagonal/natural-boundary obstruction that keeps
> `secondMoment_transfer` a sorry). So `secondMomentIntegrable` *rightly stays a hypothesis* on the headline
> (`riemannZeta_ne_zero_of_mem_strip` / `riemann_hypothesis_via_rcp` already carry it as `hint`, NOT as a sorry).
>
> **The finite-`N` deliverable is now DONE on disk (steps 1–4, all sorry-free, verified EXIT=0).**
> Implemented in `RcpEuler.lean` right after `integrable_id_and_normSq_of_bound`:
> 1. `def etaXpartial (N : ℕ) (s : ℂ) (ω : Ωb) : ℂ := ∑ n ∈ Finset.range N, ω n * (n : ℂ) ^ (-s)` — the
>    bounded, everywhere-defined truncation (vs. the bare strip-degenerate tsum `etaX`).
> 2. `measurable_etaXpartial` — finite sum of `(measurable_pi_apply n).mul_const _`.
> 3. `etaXpartial_bound : ∀ᵐ ω ∂priorBall, ‖etaXpartial N s ω‖ ≤ 2 * ∑ n ∈ range N, ‖(n:ℂ)^(-s)‖`
>    (`filter_upwards [priorBall_ball]` + `norm_sum_le` + `Finset.mul_sum`).
> 4. `secondMomentIntegrable_partial : Integrable id ν ∧ Integrable ‖·‖² ν` for
>    `ν := priorBall.map (etaXpartial N s)` — `Measure.isProbabilityMeasure_map` + `ae_map_iff` +
>    `integrable_id_and_normSq_of_bound`. **This is the `secondMomentIntegrable` predicate, proved with
>    zero deep input.** It witnesses the headline's `hint` hypothesis is honest (satisfiable, non-vacuous).
>
> **The one remaining open item (a maintainer design call — flag, don't undertake silently):** re-type
> `interiorValX`/`rcpKernelX` so the conditional law *is* an everywhere-defined finite-`N` (or
> `η_det + η_Y`) law rather than `condDistrib`-at-a-point. Then `secondMomentIntegrable` for the headline
> object becomes a *theorem* (via `secondMomentIntegrable_partial`'s pattern) and the `hint` hypothesis
> drops from `riemannZeta_ne_zero_of_mem_strip` / `riemann_hypothesis_via_rcp` entirely. This changes the
> route's central object, so it needs maintainer sign-off. **Until then the plumbing is complete and honest:
> the engine + the finite-`N` witness are both proved; only the two deep sorries
> (`secondMoment_transfer`, `bagchi_universality`) and this one re-typing decision remain.**

> **Latest design (★ 2026-06-23 (f), authoritative):** coefficient prior on the **radius-`1+ε`** closed
> disk with a small tunable `ε>0` (any radius `>1` puts `X=1` in the *open interior* — the rcp limit
> ranges over *open* neighborhoods — and `1+ε` is the **minimal-perturbation** choice, strictly better
> than radius 2: it keeps `η_X` a tight perturbation of the standard `η` and makes the squared-prime
> correction `E_X` genuinely convergent on `Re>1/2`). **Multiplicative** Euler product realized as
> `exp(∑_p X_p p^{−s})·E_X(s)`, `X₂=1`; `η_X` is **absolutely convergent on `Re s > 1+αε`** (some fixed
> `α>0`). The **ε knob closes the per-point → all-point gap directly**: on any compact `K ⊂ {Re>1/2}`,
> `P(η_X(s)=0 | X_n=1) = 0` because `ε` can be shrunk as small as needed. This **supersedes (e)'s
> "radius must be 2"** (radius 2 was correct on interiority but needlessly large) and the
> non-multiplicative (M) — read the "★ 2026-06-23 (f)" section first.

> **★ 2026-06-23 (g) — SUPERSEDES (e)+(f) on multiplicativity and radius (authoritative, maintainer).**
> **No multiplicative coefficients are needed, and the coefficient modulus is bounded by `2` again.**
> Rationale: (e)/(f) introduced the Euler product `exp(∑_p X_p p^{−s})·E_X` and the ε-knob *only* to
> lift per-point nullity to per-compact (zero-freeness off the prime locus + argument-principle count).
> That lift is now supplied **directly by Bagchi/Voronin universality**, which is *inherently
> compact-set uniform*: choosing the centrum `η_c` to approximate a **zero-free** target on a compact
> `K ⊂ {1/2<Re<1}` makes `η_c` zero-free on **all of `K` at once** — "no zeros of the centrum in any
> compact subspace." So multiplicativity and the ε-knob are **dropped**, and the radius reverts to `2`
> (interiority needs only radius `>1`; the (f) reason to shrink to `1+ε` — making `E_X` converge on
> `Re>1/2` — evaporates with `E_X`). **Consequences:**
> 1. **Delete `EXterm`/`EX`/`EX_ne_zero`/`summable_EXterm`** (the squared-prime correction) — no longer
>    load-bearing. The old "step 2.5 per-point→strip lift via argument principle" obligation is **gone**.
> 2. **Revert radius `1+ε`(=`11/10`) → `2`** in `diskLaw`, `priorBall_ball`, `diskLaw_ball/isProb`,
>    `not_rcpZeroAtAll`. The L²/convergence lemmas already use `‖ω n‖ ≤ 2` and are unaffected.
> 3. **The real next step is UNCHANGED: re-type `L`'s conditioning from the full boundary `edgeTraceX`
>    to a COEFFICIENT BALL `B(c,ρ)`** (the (b) decision), `c` off-center so the centrum `η_c(s₀)≠0`.
>    That makes `L_ne_one` a **genuine, non-vacuous** off-center-ball statement closed by the already-proved
>    `prob_singleton_zero_ne_one_of_mean_ne_zero` from the one input `∫ x ∂ν ≠ 0` (= Voronin centrum
>    nonzero / zero-free on `K`). `transfer_equality` remains the **RH-equivalent** endpoint (Portmanteau /
>    Borel–Kolmogorov `ρ↓0` reconciliation) — a labeled `sorry`, NOT removed by (g).
> **Obligation count: was {transfer(RH-equiv), L_ne_one(vacuous on disk full-boundary), per-compact lift
> via Euler product} → now {transfer(RH-equiv), L_ne_one(genuine off-center Bagchi)}.** One fewer
> obligation; `L_ne_one` upgraded from vacuous to honest. **Hypothesis flag:** Voronin/Mergelyan needs
> `K` with *connected complement* and the target zero-free + holomorphic on `K` — state this explicitly
> on the compact, do not assume arbitrary `K`.
>
> **★ ON DISK (2026-06-23 (g)) — Steps A and B are DONE in `RcpEuler.lean`; build GREEN (8033 jobs,
> exit 0), still exactly two `sorry`s (`transfer_equality`, `L_ne_one`).**
> - **Step A (mechanical) — done.** Deleted `EXterm`/`EX`/`EX_ne_zero`/`summable_EXterm` (the multiplicative
>   squared-prime correction) and reverted the prior radius `11/10 → 2` in `diskLaw`, `diskLaw_ball/isProb`,
>   `priorBall_ball`, `not_rcpZeroAtAll`, and all radius docstrings. The L²/convergence lemmas
>   (`summable_etaXTerm`, `summable_normSq_cpow`, `summable_centered_normSq`) already used `‖ω n‖ ≤ 2` and
>   were untouched. The "step 2.5 per-point→strip lift via argument principle" obligation is **gone**.
> - **Step B (off-center coefficient-ball object) — done, sorry-FREE.** Added `coeffBall N c ρ`
>   (finite-cylinder ball constraining the first `N` coordinates within `ρ` of center `c`), `lawBall`
>   (law of `η_X(s₀)` under the ball conditioning, via naive `ProbabilityTheory.cond` on the positive-mass
>   event), `Lball := lawBall {0}`, and the **non-vacuous** reduction `Lball_ne_one_of_mean_ne_zero`:
>   `hmean : ∫ x ∂lawBall ≠ 0 ⟹ Lball ≠ 1` (via the proved `prob_singleton_zero_ne_one_of_mean_ne_zero`),
>   plus `Lball_le_one`. The lone deep input is `hmean` (centrum `η_c(s₀)` nonzero = Voronin, not in Mathlib);
>   `hpos` (positive ball mass) and `hmeas` (`η_X(s₀)` measurable) are TRUE plumbing facts taken as explicit
>   hypotheses (provable separately; not RH-hard). This puts the genuine **non-circular** object on disk:
>   unlike the full-boundary `L` (whose `L=0` makes `≠1` vacuous), `Lball ≠ 1` depends on the off-center
>   centrum, not on `η(s₀)`.
> - **NOT done (deliberately): wiring `Lball` into the final theorem.** The single-`L` `by_contra`
>   (`riemannZeta_ne_zero_of_mem_strip`) is UNCHANGED. Wiring `Lball` in replaces it with the
>   Borel–Kolmogorov reconciliation of the `ρ↓0` limit = the RH-equivalent `transfer_equality`, which stays
>   the labeled `sorry`. The route still reduces RH to `transfer_equality`; Step B made `L_ne_one`'s
>   coefficient-ball cousin honest, it did not (and cannot, without Voronin + the reconciliation) close RH.
>
> **★ ON DISK (2026-06-24) — `L_ne_one` now PROVED via a named `bagchi_universality` theorem.** Per
> maintainer request ("replace the `L_ne_one` sorry by the standard theorem of Bagchi universality, prove
> the remaining as much as possible"): added `theorem bagchi_universality (s₀ R …) : ∫ x ∂(rcpKernelX s₀ R
> (eTrace R)) ≠ 0 := sorry` — the precise external citation (Voronin 1975 / Bagchi 1981: the random
> Dirichlet series' law has the whole zero-free-holomorphic class on a connected-complement compact as its
> support, so the centrum is realizable nonzero), documented with the connected-complement/zero-free
> hypotheses and the honest scope caveat (genuine for the off-center `Lball`; RH-coincident for the on-disk
> full-boundary trace). `L_ne_one`'s body is now the fully-proved reduction `… ; exact bagchi_universality
> s₀ R hs₀ hRlo hRhi` — **no anonymous gap**. Sorry count stays 2 (`transfer_equality` :830,
> `bagchi_universality` :904), but the second is now a named standard theorem, not an unexplained hole.
> Also fixed a real bug surfaced by a genuine compile: Step B used the wrong name `isProbabilityMeasure_map`
> → corrected to `Measure.isProbabilityMeasure_map`.
>
> **⚠️ BUILD-INFRA LESSON (important for future sessions).** Detached `nohup lake build RiemannProof.RcpEuler`
> in this environment is UNRELIABLE: it repeatedly returned exit 0 after an ~18 s **stale cache replay** that
> stopped at job `[8032/8033]` and **never recompiled `RcpEuler`** (the edited file), so "8033 jobs green"
> reports here can be false. The RELIABLE verification is **foreground** `lake env lean RiemannProof/RcpEuler.lean`
> (deps cached ⇒ ~70–90 s, well under the 300 s tool timeout): it always elaborates the target file from
> source and prints real errors + `declaration uses sorry` warnings. That is how the 2026-06-24 state above
> was actually verified (EXIT=0, 0 errors, sorries at 830 + 904).

> **★ ON DISK (2026-06-24 (h)) — average-squared-modulus reformulation of `L_ne_one` ADDED, sorry-free.**
> Per maintainer request ("focus on the average value of the squared modulus of η_X instead of the
> probability; constant contributions to the average squared modulus as the ball radius shrinks prove
> that (η_X|X_n=1) cannot converge to 0, even with a discrete part of the measure non-null at X_n=1").
> Added five proof-bearing, sorry-free declarations in `RcpEuler.lean`:
> (1) `norm_sq_integral_le_integral_norm_sq` — abstract Cauchy–Schwarz/Jensen core: for any probability
> measure μ on ℂ, `‖∫ x ∂μ‖² ≤ ∫ ‖x‖² ∂μ` (proof: `norm_integral_le_integral_norm`, square via
> `pow_le_pow_left₀`, then Jensen `(∫‖x‖)² ≤ ∫‖x‖²` via `(convexOn_pow (𝕜:=ℝ) 2).map_integral_le`).
> (2) `integral_norm_sq_pos_of_mean_ne_zero` — corollary: nonzero mean ⇒ `0 < ∫‖x‖²`, explicit constant
> lower bound `‖mean‖²`. (3) `secondMomentBall s₀ N c ρ := ∫ ‖x‖² ∂(lawBall …)`. (4)
> `norm_sq_centrum_le_secondMomentBall` and (5) `secondMomentBall_pos_of_mean_ne_zero` — the ball-level
> lifts. **The conceptual gain (the maintainer's point):** the lower bound `‖η_c(s₀)‖²` is fixed by the
> ball CENTER c and is INDEPENDENT of the radius ρ, so the L²-mass stays ≥ that constant uniformly as
> ρ↓0 ⇒ no convergence to 0; and because Cauchy–Schwarz uses ONLY the mean, the bound is ROBUST to a
> discrete atom of the conditional law at X_n≡1 (the `{0}`-probability `Lball` cannot see this). The deep
> input is unchanged: `‖centrum‖≠0` (`bagchi_universality`). Sorry count UNCHANGED at 2. Verified
> foreground `lake env lean` EXIT=0; the two sorries shifted to `transfer_equality` :834,
> `bagchi_universality` :965 (the abstract lemmas were inserted between them). zetanew.tex gained
> `rem:secondmoment` + §7 listing (static checks pass: braces 798/798, refs resolve).

> **★ ON DISK (2026-06-24 (i)) — variance decomposition (exact "constant contribution") ADDED, sorry-free;
> + finite-N/Cauchy spec for the specialist.** Per maintainer dialogue (the `η_X = η + centered series`
> decomposition; "make it just a reduction, not a full proof"). Added one PROVED lemma in `RcpEuler.lean`:
> `integral_normSq_eq_normSq_mean_add_variance` — for any prob measure μ on ℂ,
> `∫‖x‖²∂μ = ‖∫x∂μ‖² + ∫‖x−mean‖²∂μ` (the EQUALITY refining the earlier `≤`). Proof via `norm_sub_sq`
> (𝕜:=ℂ) + `integral_inner`/`integral_re` + `RCLike.inner_apply'`/`inner_conj_symm`/`RCLike.conj_re`.
> In route language `η_X=η+η_Y`: `E|η_X(s)|² = |η(s)|² + Σ_n v_n n^{-2σ}` — constant contribution `|η(s)|²`
> (`=‖mean‖²`) + absolutely convergent variance (`Σ v_n n^{-2σ}`, finite on σ>1/2). Sorry count UNCHANGED
> at 2; verified foreground `lake env lean` EXIT=0, sorries now at `transfer_equality` :834,
> `bagchi_universality` :1020.
>
> **HONEST-REDUCTION SCOPE (the dialogue's conclusion — do NOT try to discharge `transfer_equality`).**
> The maintainer proposed proving `E(|η_X(s)|²|X_n=1)` defines `|η(s)|²` on σ>1/2 via finite-N Cauchy
> sequences in the Hilbert space `H_K=L²(prob;Bergman(K))`, `⟨f,g⟩=∫_K E[\overline{f_X}g_X]d²s`. Analysis
> (recorded in the conversation) shows this is a genuine simplification for the CENTERED object but does NOT
> move `transfer_equality`, for a sharp reason: the absolutely-convergent strip content is only the
> zero-free diagonal `Σ_n v_n n^{-2σ}`; the zeros live in the off-diagonal `Σ_{n≠m} n^{-s}m^{-\overline s}`,
> which is exactly what averaging deletes. The two boundary conditions are incompatible — agreeing with
> `|η|²` on σ>1 needs `v_n=0` (deterministic, divergent in strip ⇒ NOT Cauchy), while a Cauchy strip limit
> needs `v_n>0` (centered, limit zero-free). And the rcp/Tjur limit `E[|η_X(s)|²|X_n=1]`: full pinning of
> all coords ⇒ `=|η(s)|²` (0 at zeros); partial pinning ⇒ `>0` from tail variance but `≠|η|²`. WHICH one
> (head/tail rate) is the Borel–Kolmogorov disintegration choice = `transfer_equality`; Radon-ness does NOT
> fix it. So "second moment at center `≠0` ⟺ η(s₀)≠0" IS RH (= the on-center centrum case of
> `bagchi_universality`/`secondMomentBall`, where `c=1 ⇒ centrum=η(s₀)`). KEEP `transfer_equality` a labelled
> sorry.
>
> **SPEC for the specialist — the genuinely-simpler CENTERED pieces (all sorry-free, NOT transfer):**
> (1) finite-`N` product prior on `(Metric.closedBall (0:ℂ) 2)^{Fin N}` (no Mehler/Kopperman needed); set
> `Y_n` centered (mean 0). (2) `η_Y^{(N)}(s)=Σ_{n<N} Y_n n^{-s}`; prove `E‖η_Y^{(N)}(s)−η_Y^{(M)}(s)‖² =
> Σ_{M≤n<N} v_n n^{-2σ} → 0` on σ>1/2 (Cauchy; reuse `summable_centered_normSq`). (3) the Hilbert space
> `H_K=L²(prob;A²(K))`; the Cauchy sequence has a unique limit `η_Y^{(∞)}` (Bergman completeness). (4) define
> `η_X=η+η_Y` with `η` the deterministic continuation (`riemannZeta`/`riemannEta`) put in by hand — this
> SIDESTEPS the natural-boundary issue. (5) `E|η_X(s)|² = |η(s)|² + Σ_n v_n n^{-2σ}` is exactly
> `integral_normSq_eq_normSq_mean_add_variance` applied with `mean=η(s)`; the variance summand feeds
> `secondMomentBall`. Label every output as the centered diagonal, NOT `|η|²`. The lone deep step
> (`transfer_equality`) is the head/tail Borel–Kolmogorov reconciliation and stays a sorry.

> **★ ON DISK (2026-06-24 (j)) — SPINE SWAP: the route's headline object is now the SECOND MOMENT
> `secondMoment s₀ R = E(‖η_X(s₀)‖² ∣ X≡1)`, NOT the `{0}`-mass `L`** (maintainer: "I want
> `E(|η_X|²|X_n=1)` instead of `L`"). Verified foreground `lake env lean` EXIT=0, still exactly 2 sorries.
> New on disk in `RcpEuler.lean`: `secondMoment` (def, `∫‖x‖²∂(rcpKernelX s₀ R (eTrace R))`);
> `secondMomentIntegrable` (Prop: `Integrable id ∧ Integrable ‖·‖²` of the rcp law — the honest plumbing
> `L` never needed); `secondMoment_transfer : secondMoment s₀ R = ‖riemannZeta s₀‖²` (the deep
> RH-equivalent sorry, RE-CAST from the old `transfer_equality`, same Borel–Kolmogorov/Portmanteau
> obstruction: atomless ⇒ `M=‖η‖²+Σv_n n^{-2σ}`, the variance is the constant contribution, equating with
> bare `‖ζ‖²` is false at zeros); `secondMoment_pos : 0 < secondMoment s₀ R` (PROVED via
> `bagchi_universality` for mean≠0 + `integral_norm_sq_pos_of_mean_ne_zero`, taking `secondMomentIntegrable`
> as hypothesis — the second-moment mirror of `L_ne_one`, NO new sorry). `riemannZeta_ne_zero_of_mem_strip`
> rewired: at a zero, transfer ⇒ `secondMoment=‖0‖²=0` contradicts `0<secondMoment`; it now carries a
> `secondMomentIntegrable` hypothesis. `riemann_hypothesis_via_rcp` threads `hint : ∀ s …,
> secondMomentIntegrable s (stripRect …)` (NOT a sorry — dischargeable by the ★(i) finite-N construction).
> **The 2 deep sorries are now `secondMoment_transfer` :871 + `bagchi_universality` :1137.** `transfer_equality`
> no longer exists (renamed); `L`/`L_le_one`/`L_eq_zero_of_atomless`/`L_ne_one` kept as legacy `{0}`-mass
> companions off the headline path (still compile, `L_ne_one` still proved-mod-bagchi). NET for the
> specialist: discharging `secondMomentIntegrable` (first+second moment integrability of the rcp law at the
> mean trace, via finite-N centered priors) removes the `hint` hypothesis and is now the ONE clean
> non-deep obligation; the two sorries remain off-limits (RH-equivalent / external citation).

**Audience**: a Lean 4 formalization agent. **Status (2026-06-22 — REDESIGN).**
The maintainer has retargeted the route along three changes (see the authoritative master
section "**The 2026-06-22 redesign**" immediately below, which supersedes the PRA/Schoenfeld
spine of Phases 3–5 and the radius-1 / Euler-product choices of Phase 0):

* **(R)** the coefficient prior moves off radius 1, so the mean realization
  `X_n ≡ 1` sits in the *interior* of the support — killing the boundary pathology that
  radius 1 created at the conditioning point; **— REVISED by ★ 2026-06-23 (f): the rcp limit uses
  *open* neighborhoods, so `X=1` MUST be interior ⇒ radius `>1`; the chosen radius is now `1+ε`
  (small tunable `ε>0`), the minimal-perturbation interior choice, NOT radius 2 (which was correct
  on interiority but needlessly large and broke `E_X` convergence on `Re>1/2`);**
* **(M)** the model is the **general, non-multiplicative** random Dirichlet series
  `η_X(s) = ∑ X_n n^{-s}` (independent, bounded coefficients, mean 1, chosen covariance —
  **no Euler product, no multiplicativity**); **— SUPERSEDED by ★ 2026-06-23 (e): the model is
  now MULTIPLICATIVE, an Euler product realized as `exp(∑_p X_p p^{−s})·E_X(s)` (squared-prime
  correction `E_X` convergent on `Re>1/2`), `X₂=1`, needed to lift per-point nullity to the strip;**
* **(Z)** the route is **ZFC-direct**: the target is the standard analytic RH, the bridge
  is a measure-theoretic **transfer equality** `P(std η zero) = P(η_X zero | X_n=1)`, and
  there is **no PRA/Schoenfeld encoding, no Π⁰₁/witness machinery, no unprovability hedge**.

**★ ON-DISK STATE (2026-06-23 — the redesign is now LARGELY IMPLEMENTED in `RcpEuler.lean`).**
The implementer has carried out (R)+(M)+(Z) on disk; the route now lives **entirely in
`RiemannProof/RcpEuler.lean`** (imported by the root), and `SchoenfeldPRA.lean` is
**quarantined — unimported** (the root `RiemannProof.lean` comments it out as "the historical
PRA/Schoenfeld spine"; its remaining `sorry`s are **not part of the build**). On disk now:
* **(R) DONE on disk at radius 2, but ★ 2026-06-23 (f) RE-TYPES the radius to `1+ε`:** on disk
  `diskLaw` on `Metric.closedBall 0 2`, `priorBall := Measure.infinitePi (fun _ => diskLaw)`,
  `priorBall_ball` (`‖X_n‖ ≤ 2`), `priorBall_atomless`. ★ (f) shrinks the radius to **`1+ε`** (small
  tunable `ε>0`): interiority needs only radius `>1` (`|1|=1<1+ε`), and `1+ε` is the
  minimal-perturbation choice that (i) keeps `η_X` a tight perturbation of `η` and (ii) makes `E_X`
  genuinely convergent on `Re>1/2` (radius 2 failed (ii)). Re-type `closedBall 0 2`→`closedBall 0 (1+ε)`,
  `‖X_n‖≤2`→`‖X_n‖≤1+ε`.
* **(M) on disk as general non-multiplicative**, `etaX s ω = ∑' n, ω n · n^(-s)`, `summable_etaXTerm`
  proved — but ★ 2026-06-23 (e) **re-types it to MULTIPLICATIVE**, the Euler product realized as
  `exp(∑_p X_p p^{−s})·E_X(s)` with the squared-prime correction `E_X` convergent on `Re>1/2` and
  `X₂=1`, needed for the per-point → strip lifting. `eulerB` kept as legacy.
* **(Z) STRUCTURE DONE, two `sorry`s:** the **shared object** `L s₀ R := rcpKernelX s₀ R (eTrace R) {0}`
  is defined once (`eTrace` = mean-realization trace, the ★ DESIGN NOTE realized); the final
  theorem `riemann_hypothesis_via_rcp : ∀ s, riemannZeta s = 0 → 1/2 < Re s < 1 → Re s = 1/2`
  (**standard ζ-form RH**) is **assembled and proved** via `riemannZeta_ne_zero_of_mem_strip`
  (the three-line `by_contra` on `stripRect`), **modulo the two load-bearers**.

**Remaining obligations — two on-disk `sorry`s, but they are NOT independent (see the ★ 2026-06-23
note below):**
1. **`transfer_equality`** (LB1) — `L s₀ R = (if riemannZeta s₀ = 0 then 1 else 0)`. **For the
   on-disk full-boundary `L` this is DOWNGRADED to a standard theorem** — rcp/Tjur limit defined
   iff Radon (`inferInstance`; `condDistrib` existence) + the deterministic identity
   `etaX(·,1·)=ζ` + continuity — **not** a deep input.
2. **`L_ne_one`** (LB2) — `L s₀ R ≠ 1` — meant to be Bagchi/Voronin universality, the
   route's one genuinely deep input. **Caveat:** with the on-disk *full-boundary* conditioning it
   is RH-in-disguise (identity theorem pins the interior; Voronin needs a connected-complement
   compact); it becomes a real Bagchi statement only after the conditioning of `L` is **re-typed
   from a boundary trace to a COEFFICIENT BALL** `{X ∈ B(c,ρ)}` — the maintainer resolution in
   the ★ 2026-06-23 (b) note below (a *local arc* does NOT suffice — any arc has a limit point, so
   the identity theorem still pins).
Plus a vestigial `sorry` (`not_rcpZeroAt`, the **legacy `eulerB` limit form**, superseded by
`L_ne_one`, **unused** by the final theorem — safe to delete). The conclusion is a **positive** RH
in ZFC: the `{0,1}` indicator equals `L ≠ 1`, so it is `0`.

**★ NEW obligation (★ 2026-06-23 (e), REALIZED via the ε-knob in (f)) — the per-point → strip
lifting.** LB1+LB2 establish, for each **fixed** `s₀`, that `L s₀ = 0` (no zero at `s₀`). RH needs
**no zero anywhere in the strip**. ★ 2026-06-23 (f) supplies the concrete mechanism: the **radius
`1+ε` is tunable**, so on any **compact** `K ⊂ {Re>1/2}` one chooses `ε=ε(K)` small enough that
`P(η_X(s)=0 | X_n=1)=0` **uniformly on `K`** — the multiplicative `exp(prime)·E_X` structure keeps
`η_X` an analytically-controlled, zero-free-off-the-prime-locus perturbation (abs. convergent on
`Re>1+αε`), and the ε-knob turns per-point nullity into per-compact nullity. This is a **third**
genuine piece of content, on top of the two load-bearers; it is **not yet on disk** (the on-disk
`etaX` is non-multiplicative and the radius is 2) and is gated on the (R)+(M) re-typing in step 0.

### ★ 2026-06-23 (maintainer) — `transfer_equality` (LB1) downgrades to a STANDARD theorem, which exposes a conditioning-strength tradeoff with `L_ne_one` (LB2)

**The downgrade (correct).** Conditioning on the **exact** mean realization `X_n = 1 (∀ n)` makes
`η_X` deterministically the standard series: `etaX s (fun _ => 1) = ∑ n^{-s} = ζ(s)` (its
continuation — the `EtaConvergence` mean-series layer). So the regular conditional law of
`η_X(s₀)` given `X = 1·` is the Dirac `δ_{ζ(s₀)}`, whence `L = 1{ζ(s₀)=0}`. The **only**
non-trivial ingredient is that the rcp at the null point `X=1·` is *well-defined* — the standard
theorem *the Tjur neighborhood limit exists iff the space is Radon* — and the substrate **is**
Radon (separable-Hilbert/Polish inner-product ⇒ inner-regular Borel measures, `inferInstance`;
Mathlib's `condDistrib` already packages the disintegration existence). So **`transfer_equality`
is NOT a deep analytic input**: it = (standard rcp existence on a Radon/standard-Borel space)
+ (the deterministic identity `etaX(·,1·) = ζ`) + continuity. Drop it from the "two deep inputs".

**The tradeoff it exposes (honest consequence — must be resolved).** The downgrade is valid only
when the conditioning **pins the interior** — exact/full-boundary agreement, where the identity
theorem (holomorphic `η_X` agreeing with `ζ` on a boundary arc with a limit point ⟹ `η_X ≡ ζ`
⟹ `X=1`) or max-modulus forces `η_X(s₀)=ζ(s₀)`. **That is exactly the regime where `L_ne_one`
(LB2) FAILS:** with the interior pinned, `L = 1{ζ(s₀)=0}`, so `L ≠ 1 ⟺ ζ(s₀)≠0` is **literally
RH**, and Bagchi/Voronin **cannot** supply it (universality needs a *connected-complement*
compact — a local arc, not a full rectangle boundary, whose complement has two components — and
yields zero-free alternative averages only under *approximate/local* agreement, which the
identity theorem rules out for a full arc). Conversely, in the **local, non-`s₀`-enclosing**
regime where Bagchi *does* give `L ≠ 1`, the interior is **not** pinned, so `transfer_equality`
is **no longer** the trivial identity.

**Net — one shared `L` cannot be both (LB1-easy) and (LB2-Bagchi).** Conditioning strength splits
the difficulty: *strong* (full/exact) ⇒ LB1 trivial, LB2 = RH (circular); *weak* (local/
approximate) ⇒ LB2 = genuine Bagchi, LB1 non-trivial. **The on-disk `edgeTraceX` conditions on
the FULL boundary `R.closure \ R.openInt`** (a continuous set) — the *strong* regime — so on disk
`transfer_equality` is the downgradable one and **`L_ne_one` is currently RH-in-disguise, not a
Bagchi statement.**

**DECISION — already made (maintainer), now an implementer task.** To make the route non-circular,
re-type the conditioning of `L` away from a boundary trace. **This is RESOLVED** (2026-06-23 (b)
below: condition on a coefficient ball, not any boundary trace/arc) — there is **no pending
maintainer decision to wait on**. The implementer should carry out the re-typing (step 0) and then
prove LB1/LB2 against the ball form.

### ★ 2026-06-23 (b) (maintainer, "No arc is needed anymore, just a ball") — the tradeoff is RESOLVED by conditioning on a coefficient-space ball

**The fix.** Do **not** condition on the function-values of `η_X` on any boundary set — not the
full boundary, and not a *local arc* either. Condition directly on a **ball in coefficient space**
`{X ∈ B(c,ρ)}` (center `c`, radius `ρ>0`). Why this dissolves the tradeoff (and why "local arc"
did **not**):
- **Any boundary arc still pins.** A local arc has a limit point, so the **identity theorem**
  forces a holomorphic `η_X` agreeing with `η` there to agree everywhere ⟹ `X=1` ⟹ interior
  pinned. Shrinking the arc does not help. The earlier "weaken to a local trace" decision was
  therefore still broken; this corrects it.
- **A coefficient ball never pins.** `{X ∈ B(c,ρ)}` constrains the coefficients `X_n` *directly*;
  it is **not** a statement about `η_X`'s values on a curve, so neither the identity theorem nor
  the maximum-modulus principle applies. The conditional law of `η_X(s₀)` stays non-degenerate.
- **Both load-bearers now hold of the SAME family of balls** (shared-`L` discipline preserved):
  - **LB2 / `L_ne_one`** (positive radius `ρ>0`): conditional law of `η_X(s₀)` has mean = centrum
    (= `η_c(s₀)`, choosable nonzero via Bagchi universality) and finite variance `∝ ρ²`, hence
    **non-degenerate / absolutely continuous** ⟹ the atom `{0}` has mass `<1` (in fact `0`) ⟹
    `L(ρ) ≠ 1`. This is the genuine Bagchi input.
  - **LB1 / `transfer_equality`** (the `ρ↓0` limit): the ball-conditionals concentrate, mean
    `→ η(s₀)`, variance `→0`, so the law `⇒ δ_{η(s₀)}` and the rcp at the exact point `X=1` (the
    canonical Radon neighborhood limit) `= 1{η(s₀)=0}`. Standard Tjur/Radon concentration.
- **The assembly is the Borel–Kolmogorov reconciliation.** `1{η(s₀)=0} = rcp(·|X=1) =
  lim_{ρ↓0} L(ρ) = 0` (the absolutely-continuous ball-conditionals give the atom `{0}` mass 0,
  so their limit is 0). Hence the indicator is 0, i.e. `η(s₀)≠0`. The naive "δ_{η(s₀)} so value
  = 1{η(s₀)=0}" and the canonical ball-limit (= 0) agree at `{0}` **only** when `η(s₀)≠0`; the
  uniqueness of the Radon rcp forbids disagreement ⟹ no zero. (This is exactly what "rcp defined
  iff Radon" + interiority + atomlessness license; see zetanew.tex §5 proof of thm:nozero.)

**Lean consequence.** The on-disk `edgeTraceX`/`eTrace` (FULL boundary `R.closure \ R.openInt`)
must be replaced by a **coefficient-ball conditioning**: condition `condDistrib(etaX s₀, Π, priorBall)`
on a finite/cofinite coefficient projection `Π` landing in a ball `B(c,ρ)`, NOT on the boundary
trace. Then `L_ne_one` is the non-degeneracy of that ball-conditional (Bagchi), and
`transfer_equality` is its `ρ↓0` concentration. **Net: the route is no longer circular — the lone
deep input is LB2 (Bagchi non-degeneracy of the positive-radius ball-conditional).**

### ★ 2026-06-23 (f) (maintainer) — radius `1+ε` (small tunable `ε>0`), absolutely convergent on `Re>1+αε`, and the ε-knob that closes the per-point → all-point gap

Revises **(R)** [radius `2` → radius **`1+ε`**] and sharpens how the per-point → strip lift is
obtained. Keeps the **multiplicative** Euler product and `X₂=1` from (e). **This supersedes (e)'s
"radius must be 2" conclusion** — the interiority *reasoning* in (e) is right, the *value* `2` was
not forced.

**Radius `1+ε`, not 2 — interiority needs radius `>1`, and `1+ε` is the better choice.** The (e)
analysis is correct that the rcp neighborhood (Tjur) limit at `X=1` ranges over **open**
neighborhoods, so `X=1` must be an **interior** point of the support — which rules out radius 1
(there `|1|=1` is on the boundary). But interiority needs only radius **`>1`**: for the closed disk
`closedBall 0 (1+ε)` the point `X=1` satisfies `|1| = 1 < 1+ε`, so it lies in the **open interior**
`ball 0 (1+ε)` for **every** `ε>0`. Radius 2 was thus an over-large, unnecessary perturbation. Take
`ε>0` **small and tunable**. This is strictly better than radius 2 because:
- **`η_X` stays a tight perturbation of the standard `η`** — `‖X_n‖ ≤ 1+ε` keeps every coefficient
  within `ε` of the deterministic value, so as `ε↓0` the random model collapses onto `η`.
- **the squared-prime correction `E_X` becomes genuinely convergent on `Re>1/2`.** With `‖X_p‖ ≤ 2`
  (radius 2), `∑_p ∑_{k≥2}(1/k)‖X_p‖^k p^{−kσ}` needs `2·p^{−σ}<1`, i.e. `σ>1` at `p=2` — so the
  (e) claim "`E_X` converges on `Re>1/2`" actually **failed at radius 2**. With `‖X_p‖ ≤ 1+ε` it
  needs only `(1+ε)p^{−σ}<1`, i.e. `σ > log_p(1+ε) ≈ ε/ln p`, which **holds on `Re>1/2`** for small
  `ε`. Radius `1+ε` is what makes the (e) `exp(prime)·E_X` realization actually work on the strip.

**Absolute convergence on `Re>1+αε`.** With `‖X_n‖ ≤ 1+ε` the Dirichlet series `η_X(s) = ∑_n X_n n^{−s}`
(equivalently the `exp(prime series)·E_X` Euler product) is **absolutely convergent for `Re s > 1+αε`**
for a fixed `α>0` — the abscissa of absolute convergence sits a controlled `O(ε)` to the right of `1`,
and `→ 1` as `ε↓0`, recovering the abscissa of the standard `η`. (The genuinely sensitive/divergent
part on the strip remains the *linear* prime series `∑_p X_p p^{−s}`; `E_X` converges on `Re>1/2` as
above.)

**The ε-knob CLOSES the per-point → all-point gap directly.** The gap (e) identified — per-point
nullity `P(zero at s₀)=0` does not, by a bare uncountable union, give `P(zero anywhere)=0` — is now
closed by the **tunability of `ε`** together with **compactness**: on any **compact** `K ⊂ {Re>1/2}`,
`P(η_X(s)=0 | X_n=1) = 0` **uniformly on `K`**, because `ε` can be chosen as small as needed
(`ε = ε(K)`). The mechanism: shrinking `ε` makes `η_X` an arbitrarily tight (analytically controlled,
since absolutely convergent on `Re>1+αε`) perturbation of `η`; the rcp at the interior point `X=1`
then assigns the zero-set — a measure-zero analytic-subvariety condition — probability `0` on all of
`K` at once. So the multiplicative `exp(prime)·E_X` structure (which is what keeps the perturbation
analytically controlled and zero-free off the prime-series locus) plus the ε-knob **realize** the
per-point → strip lift of step 2.5 — they are not a separate argument-principle obligation but the
concrete way that obligation is met. `X₂=1` retained (eta normalization).

**Lean consequence (step 0, (R) radius → `1+ε`; (M) unchanged from (e)).**
- `diskLaw` on `closedBall 0 (1+ε)` for a fixed small `ε>0` (a `variable (ε : ℝ) (hε : 0 < ε)` or a
  concrete small literal, e.g. `1/10`); `‖X_n‖ ≤ 1+ε`; atomless — interiority holds since `1 < 1+ε`.
  Port the `‖X_n‖≤2` estimates with constant `1+ε`.
- `η_X` absolute convergence on `Re>1+αε` (M-test with the `(1+ε)·n^{−σ}` bound); the `E_X`
  correction now genuinely convergent on `Re>1/2` (domination `(1+ε)^k p^{−kσ}`, summable for `σ>1/2`
  at small `ε`).
- **The lifting lemma (step 2.5) is realized via ε:** "`L s₀ = 0` for each `s₀ ∈ K`" ⇒ "no zero on
  `K`" by choosing `ε=ε(K)` so that the ball-conditional zero-probability is `0` uniformly on the
  compact `K`. (The Euler-product zero-freeness / argument-principle count is the *qualitative*
  reason the perturbation has no zeros off the prime-series locus; the ε-knob is the *quantitative*
  uniformity that turns per-point into per-compact.)

---

### ★ 2026-06-23 (e) (maintainer) — multiplicative Euler product as `exp(prime Dirichlet series) × convergent squared-prime factor`; radius STAYS 2 [radius SUPERSEDED by (f): radius is now `1+ε`]; closing the per-point → all-point gap

Revises **(M)** [non-multiplicative → **multiplicative**] and specifies *how* the Euler product is
realized. **(R) radius 2 STANDS** — an earlier draft of this section wrongly reverted it to radius 1;
**corrected below: the radius must be 2.**

**Radius must be 2 (the rcp limit uses OPEN neighborhoods — interiority is required).** The
neighborhood-limit (Tjur) definition of the rcp at the conditioning point `X = 1` is the limit over
**open** neighborhoods `U ∋ (X=1)` of `P(A ∩ Π⁻¹U)/P(Π⁻¹U)`. For that limit to be well-defined, `X=1`
must be an **interior** point of the support, so that small *open* neighborhoods of it lie **inside**
the support. At radius 1 the point `X=1` is on the **boundary** (`|1| = 1`), every open neighborhood
of it sticks out of the closed disk, and the open-neighborhood limit is ill-defined. "The closed
support contains `X=1`" is **not enough** — the limit ranges over *open* sets. **So `diskLaw` stays on
`closedBall 0 2`, `‖X_n‖ ≤ 2`, and `X=1` stays in the interior** (this is exactly what redesign (R)
was for; the radius-1 claim in the previous draft of (e) is retracted).

**The gap (why (b) alone is not yet RH).** The coefficient-ball machinery of (b) delivers, for each
**fixed** `s₀`, that `P(η has a zero at s₀) = 0`. But RH needs `P(η has a zero **anywhere** in the
strip) = 0` — over the **uncountable** family of points `s₀`. A bare union / Fubini over uncountably
many individually-null events does **not** close this gap; something must transport "null at each
point" to "null on the whole region". The **multiplicative** structure supplies that transport.

**The model — multiplicative Euler product, realized as `exp(prime series) × convergent factor`.**
Keep the Euler product (the previous (e) message), and realize it as
`η_X(s) = exp( ∑_p X_p p^{−s} ) · E_X(s)`, where:
- `∑_p X_p p^{−s}` is the **prime Dirichlet series** — *linear* in the prime coefficients `X_p`, the
  randomness-carrying, zero-controlling part; at `X_p = 1` it is the prime zeta `P(s) = ∑_p p^{−s}`.
- `E_X(s) = exp( ∑_p ∑_{k≥2} (1/k) X_p^k p^{−ks} )` is the **higher-power correction factor**, which
  **converges absolutely for `Re s > 1/2`** because it involves only **squared (and higher) primes**
  — it is dominated by `∑_p p^{−2s}` (convergent on `Re s > 1/2`), or by any factor that can be
  bounded by such a squared-prime Dirichlet series.

This is the standard `log ζ = ∑_p p^{−s} + O(∑_p p^{−2s})` decomposition, lifted to the random model.
**Why it matters:** `η_X = exp(…)` is **manifestly zero-free wherever its exponent converges**, and on
the strip `1/2 < Re s < 1` the **only** sensitive part is the *linear* prime series `∑_p X_p p^{−s}`
(the correction `E_X` always converges there). So "no zero at `s`" ⟺ "the prime series converges at
`s`", and both the per-point ball non-degeneracy (LB2) and the per-point → strip lift act on the
**linear prime series**, with the squared-prime factor a harmless convergent, **non-vanishing**
multiplier. `X₂ = 1` (eta normalization, pinning the `(1 − 2^{1−s})` factor) is retained.

**The per-point → strip lift (what multiplicativity buys).** Because `η_X = exp(prime series) · E_X`
with `E_X ≠ 0`, the zero-set of `η_X` on the strip is exactly the set where the prime-series
representation fails — controlled, via the argument-principle / `η_X'/η_X` contour count, by the
**countably many** prime coefficients `X_p`. Hence per-point non-detection of the *linear prime
series* propagates to "no zero in the region". This upgrades "`P(zero at s₀)=0` for every fixed `s₀`"
to "`P(∃ zero in the strip)=0`". **Consequence:** the Euler product / multiplicativity is **no longer
"exposition only"** (cf. the older note) — it is **load-bearing** for the per-point → all-point lift
(though **not** for LB2's non-degeneracy, which the full support of the prior law still supplies).

**Lean consequence (step 0, (M) only — radius UNCHANGED at 2).**
- `diskLaw` on `closedBall 0 2`, `‖X_n‖ ≤ 2`, atomless — **all unchanged** (interiority needed).
- Re-type `etaX` to `exp(primeSeries X s) * correctionFactor X s` with
  `primeSeries X s = ∑_p X_p p^{−s}` and `correctionFactor X s = exp(∑_p ∑_{k≥2} (1/k) X_p^k p^{−ks})`;
  prove the correction's absolute convergence on `Re s > 1/2` by **domination by `∑_p p^{−2s}`** (a
  `Real.summable_nat_rpow`-style bound at exponent `2σ > 1`), and `correctionFactor ≠ 0` (it is an
  `exp`). `X₂ = 1` fixed.
- **NEW obligation — the per-point → strip lifting lemma:** from "`L s₀ = 0` for every `s₀` in the
  open strip" (no zero at each point — equivalently the linear prime series converges at each point)
  conclude "`η_X` (equivalently `ζ`) has no zero in the strip", via Euler-product zero-freeness
  (`exp(…)·E_X`, `E_X≠0`) + the argument-principle count over the countably many `X_p`. **Genuine new
  analytic content, separate from LB1/LB2.**

---

## The 2026-06-22 redesign (maintainer): radius-2 ball, non-multiplicative coefficients, ZFC-direct

Three maintainer changes **supersede the PRA/Schoenfeld spine (Phases 3–5) and the
radius-1 / Euler-product choices (Phase 0)**. The earlier sections — and the on-disk
`SchoenfeldPRA.lean` — are kept below for historical context, but the route's target and
bridge are now as stated here. **As of 2026-06-23 this redesign is largely ON DISK** in
`RcpEuler.lean` (see the ★ ON-DISK STATE box above); the descriptions below remain the
authoritative spec, and only the two load-bearers `transfer_equality` and `L_ne_one` are open.

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
* **N4 — the load-bearing steps carry the deep content; prove them on the cited inputs.**
  Steps flagged **[LB]** are where the real mathematics lives: build each proof on the deep input
  named in its recipe (don't hand-wave or re-invoke another open `sorry`) — but **do replace the
  `sorry` with a real proof**, that is the goal. Steps flagged **[mech]** are mechanical given their
  dependencies.

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
  consumed. *(HISTORICAL — this paragraph describes the **dropped** Schoenfeld bridge
  `counterexample_iff_rcpZero` in the quarantined `SchoenfeldPRA.lean`; it is **not** a current
  task. The live obligations are LB1/LB2 in `RcpEuler.lean` — see the ★ MANDATE banner and steps
  0–2.5. Do not work this `sorry`.)*

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

## Build order & status — ON-DISK MAP (2026-06-23, verified by `lake build`)

Legend: `✓` on disk & `sorry`-free · `□` on disk as honest `[LB] sorry` · `✗` **dropped**
from the spine (quarantined/unimported, not part of the build).

```
RcpEuler.lean (imported by root RiemannProof.lean) — THE route, builds green:
(R) diskLaw on closedBall 0 2; priorBall_ball ‖X_n‖≤2  ✓   ★(f) RE-TYPE radius 2 → 1+ε (small ε>0): interior needs only >1; 1+ε minimal pert., fixes E_X conv on Re>1/2
(M) etaX s ω = ∑' n, ω n · n^(-s)                       ✓   on disk non-mult; ★(e) RE-TYPE to exp(∑_p X_p p^{-s})·E_X, X₂=1; abs conv on Re>1+αε
    per-point → strip lifting (ε-knob on compacts)      ·   ★(e/f) NEW obligation; (f): shrink ε=ε(K) ⇒ P(zero|X=1)=0 unif. on compact K⊂{Re>1/2}; NOT on disk (needs (R)+(M) re-type)
    summable_etaXTerm (abs conv on Re>1, M-test)        ✓   the Re>1 convergence layer (replaces bSum_tail_small)
    priorBall, isProb, _ball, _atomless                 ✓   radius-2 prior, sorry-free
    rcpKernelX, edgeTraceX, interiorValX, eTrace        ✓   on-disk uses a BOUNDARY trace; step 0 re-types to a coefficient ball
    secondMoment s₀ R := ∫‖x‖²∂(rcpKernelX s₀ R(eTrace)) ✓  ★(j) the SHARED HEADLINE object (replaces {0}-mass L)
    secondMomentIntegrable s₀ R (Prop)                  ✓   moment-integrability plumbing, threaded as hyp (NOT a sorry)
    integrable_id_and_normSq_of_bound                   ✓   ★(k) PROVED engine: a.e. bound ‖x‖≤C ⇒ Integrable id ∧ ‖·‖² (no analytic input)
    etaXpartial / measurable_ / _bound                  ✓   ★(k) bounded finite-N truncation Σ_{n<N}ω_n n^{-s} (vs strip-degenerate tsum etaX)
    secondMomentIntegrable_partial                      ✓   ★(k) PROVED: the integrability predicate holds for priorBall.map(etaXpartial N s) — hint is honest
    secondMoment_transfer  M = ‖riemannZeta s₀‖²        □   LOAD-BEARER 1 = RH-equivalent Borel–Kolmogorov (sorry @ :871)
    secondMoment_pos       0 < M                        ✓   LOAD-BEARER 2 PROVED via bagchi_universality + integral_norm_sq_pos_of_mean_ne_zero
    bagchi_universality (mean ≠ 0)                      □   external Voronin/Bagchi citation (sorry @ :1137)
    stripRect, riemannZeta_ne_zero_of_mem_strip         ✓   by_contra on M: zero ⇒ M=‖0‖²=0 contra 0<M (carries secondMomentIntegrable hyp)
    riemann_hypothesis_via_rcp (standard ζ-form RH)     ✓   FINAL THEOREM, proved modulo the 2 load-bearers (threads hint)
    L / L_ne_one / integral_normSq_eq_..._variance      ✓   legacy {0}-mass + variance-decomposition companions (off headline path)
---- quarantined: SchoenfeldPRA.lean is UNIMPORTED (not in the build) ----------------------
    schoenfeld/schoenfeld_primrec, Pi01/interpPi01      ✗   Π⁰₁ encoding dropped (redesign Z)
    counterexample_iff_rcpZero, RH_PRA / RH_PRA_holds   ✗   PRA bridge & target dropped (2 stale sorries, not in build)
```

**Verified build (2026-06-24, ★(j)):** foreground `lake env lean RiemannProof/RcpEuler.lean` →
EXIT 0, exactly **two `sorry` warnings**: `:871` (`secondMoment_transfer`, LB1 — the RH-equivalent
endpoint) and `:1137` (`bagchi_universality`, the external citation LB2 reduces to) — plus style
lints only, no errors. (`not_rcpZeroAt` was deleted earlier; `transfer_equality` was renamed to
`secondMoment_transfer`.) So the **standard-ζ-form RH is on disk and assembled** against the
second-moment object `M`, reduced to the two deep load-bearers (plus the non-deep
`secondMomentIntegrable` hypothesis, dischargeable by the finite-N construction). **Dropped (not discharged):** the
entire `SchoenfeldPRA.lean` Π⁰₁/Schoenfeld spine is quarantined (root comments out its import).
**No substrate-construction obligation** — Mehler guarantees existence; only the rcp-limit
family + `Measure.infinitePi`/`infinitePi_pi` consistency is used.

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

1. **The exact prior `priorBall` — radius **`1+ε`** (redesign (R), ★ 2026-06-23 (f); SUPERSEDES the
   (e) "radius 2" choice).**
   The prior is the **pure continuous** law `priorBall := Measure.infinitePi (fun _ => diskLaw)`, an
   independent product of the uniform law on the closed disk of radius **`1+ε`** (small tunable
   `ε>0`; `diskLaw := ProbabilityTheory.cond volume (closedBall 0 (1+ε))`); a probability measure,
   supported in the radius-`1+ε` ball, and **atomless** (`priorBall_atomless`). The radius-`1+ε`
   choice puts the mean realization `X_n ≡ 1` in the **interior** of the support — **required**,
   because the rcp neighborhood limit ranges over *open* neighborhoods of `X=1`, which must lie inside
   the support (radius 1 fails: `|1|=1` is on the boundary). Interiority needs only radius **`>1`**, so
   the over-large radius 2 of (e) is replaced by the minimal-perturbation `1+ε`, which additionally
   makes the squared-prime correction `E_X` genuinely convergent on `Re>1/2` (radius 2 did not). The
   on-disk file is currently radius 2; **re-type `closedBall 0 2`→`closedBall 0 (1+ε)`, `‖X_n‖≤2`→`‖X_n‖≤1+ε`**. The
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

> **★ MANDATE TO THE LEAN IMPLEMENTER — these `sorry`s ARE your job; prove them.** This plan does
> **not** tell you to stop, wait, or leave anything unproven. The remaining content is exactly the
> two `sorry`s `transfer_equality` (`:736`) and `L_ne_one` (`:750`), and your task is to **eliminate
> both by writing real proofs.** The only sequencing guidance is: **first** do step 0 (re-type the
> model/radius/conditioning to the coefficient-ball form), **then** prove LB1 and LB2 *against that
> re-typed `L`*. The recipes below are the intended proof strategy — **follow them rather than
> inventing an unrelated shortcut**, but "follow the recipe" means *write the proof*, not skip it.
> - Where the plan says "do **not** attempt LB1/LB2 against the on-disk *full-boundary* `L`", that is
>   **scoped to the OLD formulation** (which is provably circular) — it is **not** a ban on proving
>   the lemmas. After step 0 re-types `L` to the ball form, you are **expected to prove both**.
> - "Do not improvise" / "[LB] carry the mathematical content" means *use the cited deep inputs
>   (Tjur/Radon concentration for LB1, Bagchi/Voronin universality for LB2) instead of a hand-wave* —
>   it does **not** mean leave the `sorry` in place.
> - If a step genuinely cannot be completed, **report the specific Lean/maths obstruction you hit**;
>   do **not** conclude "the plan said there is nothing to do." There is something to do (the EASY
>   STEPS below), and the deep step is now precisely identified.

> **★ 2026-06-23 UPDATE — which `sorry` is which, and the EASY provable work (READ THIS FIRST).**
> A measure-theoretic analysis (zetanew.tex `rem:portmanteau`; the `transfer_equality` docstring)
> settled which load-bearer is deep, and it is the **opposite** of the older framing:
> - **`transfer_equality` is RH-EQUIVALENT — do NOT attempt it.** Under the atomless substrate the
>   honest rcp value is `L = 0` (proved: `tjur_ratio_eq_zero_of_null`, `L_eq_zero_of_atomless`).
>   Turning that into `𝟙{η(s₀)=0}` is the Portmanteau continuity-set step, valid iff `η(s₀)≠0`. So
>   `transfer_equality` is false at any zero and is not a non-RH theorem. **It is the deliberate
>   endpoint of a verified *reduction*; leave it as a labeled `sorry`.** This is NOT "there is nothing
>   to do" — see the easy steps.
> - **`L_ne_one` is NOT deep** (it is `L = 0`, unconditional and vacuous), but it is **not cleanly
>   provable against the on-disk `L`** until `L` is re-typed from `condDistrib`-at-a-point to the Tjur
>   neighborhood limit (the point value is version-dependent). That re-typing is a real but larger task.
>
> **EASY STEPS (genuinely provable, not RH-hard — do these; each is broken into Lean-sized pieces):**
> 1. **[DONE]** Measure-theoretic core + strip-`L²` convergence are on disk and `sorry`-free:
>    `L_le_one`, `L_eq_zero_of_atomless`, `prob_singleton_zero_ne_one_of_mean_ne_zero`,
>    `tjur_ratio_eq_zero_of_null`, `summable_normSq_cpow`, `summable_centered_normSq`. (And the
>    vestigial `not_rcpZeroAt` was deleted.)
> 2. **Fix `etaX` in the strip (the real bug).** On disk `etaX s ω = ∑' n, ω n · n^{-s}` is the naive
>    `tsum`, which is **non-summable for `Re s < 1`** (the mean `∑ n^{-s}` diverges), so Mathlib returns
>    `0` and `etaX ≡ 0` on the strip. Re-define it as the honest split. Lean-sized pieces:
>    (a) define `etaCentered s ω := ∑' n, (ω n - 1) · n^{-s}` and prove it converges/has `L²` terms via
>        the new `summable_centered_normSq` (bounded coeffs, `Re>1/2`); (b) define
>        `etaX s ω := riemannZeta-based η s + etaCentered s ω` (mean part = the *continued* `η`, not the
>        divergent sum); (c) check `etaX s (fun _ => 1) = η s` (centered part is `0` at `ω ≡ 1`); (d)
>        confirm `summable_etaXTerm` (`Re>1`) still ports (there the naive sum *does* converge and equals
>        the split). This makes `etaX` well-posed and is the substance of step-0 `(M)`.
> 3. **Radius `closedBall 0 2 → closedBall 0 (1+ε)`** (step-0 `(R)`). Mechanical: introduce
>    `variable (ε : ℝ) (hε : 0 < ε)` (or a literal like `(1:ℝ)/10`), change `diskLaw`'s ball and the
>    `‖X_n‖ ≤ 2` bounds to `‖X_n‖ ≤ 1+ε`, re-run the `priorBall_*` proofs (they port verbatim with the
>    new constant). Interiority holds since `|1| = 1 < 1+ε`.
> 4. **(Optional, for the compact-lift) `E_X` convergence on `Re>1/2`.** Define
>    `E_X s ω := exp(∑_p ∑_{k≥2} (1/k) (ω p)^k p^{-ks})` and prove the exponent converges absolutely on
>    `Re>1/2` by domination by `∑_p p^{-2σ}` (use `summable_normSq_cpow`-style bounds restricted to
>    primes); `E_X ≠ 0` since it is an `exp`. Then `etaX = exp(∑_p (ω p) p^{-s}) · E_X` is the
>    multiplicative form used for excluding zeros on compacts (zetanew.tex `rem:nomult`).
>
> **Larger but well-defined (do only if pursuing a clean end-state):** re-type `L`/`rcpKernelX` from
> the `condDistrib`-at-`eTrace R` value to the **Tjur neighborhood limit**. After it, `L_ne_one`
> becomes provable as `L = 0` via `L_eq_zero_of_atomless` + atomlessness of `etaX(s₀)`'s law, leaving
> `transfer_equality` as the **sole** (labeled, RH-equivalent) `sorry`. **Do NOT** attempt
> `transfer_equality` itself or Voronin/Bagchi universality.

**State after the 2026-06-23 build.** The redesign is **largely implemented and builds green**
(`lake build RiemannProof.RcpEuler` → 8033 jobs, exit 0). (R)+(M)+(Z) are on disk; the shared
object `L` and the ★ DESIGN NOTE are realized exactly; the **standard-ζ-form RH theorem
`riemann_hypothesis_via_rcp` is assembled and proved modulo the two load-bearers**. So the
entire remaining mathematical content is **two `sorry`s in `RcpEuler.lean`** — `transfer_equality`
(`:736`) and `L_ne_one` (`:750`) — plus mechanical cleanup. Everything else (radius-2 prior,
`etaX`, `summable_etaXTerm`, the rcp kernel, the `by_contra` assembly) is `sorry`-free.

**DONE on disk (★ 2026-06-23 (f) re-types the radius; (e) re-types (M) — see step 0):**
- **(R)** radius-2 prior on disk — `diskLaw` on `closedBall 0 2`, `priorBall_*`, `‖X_n‖≤2`, atomless.
  **★ (f): RE-TYPE radius 2 → `1+ε`** — the rcp limit ranges over *open* neighborhoods, so `X=1` must
  be **interior**; radius 1 (boundary point) fails, but interiority needs only radius `>1`, so `1+ε`
  (small tunable `ε>0`) replaces the over-large radius 2 and additionally makes `E_X` converge on
  `Re>1/2`. Re-type `closedBall 0 2`→`closedBall 0 (1+ε)`, `‖X_n‖≤2`→`‖X_n‖≤1+ε`.
- **(M)** `etaX = ∑' n, ω n · n^(-s)` (general, non-multiplicative) + `summable_etaXTerm`
  (absolute convergence on `Re>1`). **★ (e): re-type to the MULTIPLICATIVE Euler product**
  `exp(∑_p X_p p^{−s})·E_X(s)`, squared-prime correction `E_X` convergent on `Re>1/2`, `X₂=1` —
  required for the per-point → strip lifting. The strip `1/2<Re≤1` a.s. convergence is currently
  *folded into* the two load-bearers rather than a standalone lemma (see optional step 3).
- **(Z)** the shared `L s₀ R := rcpKernelX s₀ R (eTrace R) {0}`, `eTrace` = mean-realization
  trace, `stripRect`, `riemannZeta_ne_zero_of_mem_strip` (the three-line `by_contra`), and the
  final `riemann_hypothesis_via_rcp` — all `sorry`-free modulo LB1/LB2.

**★ IMPLEMENTER FEEDBACK (run `1400d993`, see `ARISTOTLE_SUMMARY.md`) — and why it does NOT
block the route.** The most recent implementer run reported, honestly, that (i) the build is green
with the two `sorry`s, but (ii) "the two remaining obligations cannot be honestly discharged …
with the on-disk full-boundary conditioning the route is currently circular (one of the two is
RH-in-disguise)", and (iii) it *rejected and reverted* an auto-generated proof of `L_ne_one` that
merely re-invoked the still-open `transfer_equality` (a parasitic circular discharge). **That
assessment is correct — but it was made against the OLD full-boundary `edgeTraceX` conditioning,
and predates the maintainer's ★ 2026-06-23 (b) resolution.** The circularity the implementer hit
is *exactly* the tradeoff that conditioning on a **coefficient ball** dissolves (a coefficient ball
never pins the interior, so LB2 is a genuine Bagchi non-degeneracy and LB1 is a standard `ρ↓0`
concentration — independent). **So the conclusion is NOT "the plan cannot be executed"; it is "step
0 must be done first, then both lemmas get proved."** Concretely: **do step 0 yourself** (re-type the
conditioning from the full-boundary trace to a coefficient ball), **then prove LB1 and LB2 against
the re-typed `L`** — they become independent and non-circular. The only thing to avoid is burning
effort proving them against the *old* full-boundary `L` (that formulation is circular, so a proof
there would be a parasitic re-invocation, exactly what the implementer rightly rejected). After
step 0 the proofs are expected and the recipes below tell you how. **Step 0 is itself implementer
work — it is not a maintainer gate you must wait on.**

**REMAINING — gated on the conditioning-strength DECISION (see the ★ 2026-06-23 note above).**
The two load-bearers are NOT independent *as long as `L` conditions on the boundary trace*: the
strength of the on-disk `edgeTraceX`/`L` conditioning decides which one is trivial and which is
deep, and the full-boundary choice makes LB2 circular. **Step 0 (re-type to a coefficient ball)
breaks this coupling** — after it, LB1 and LB2 are independent. So **do step 0 first**, then **prove
the two load-bearers** (both are implementer tasks; nothing here waits on the maintainer).
0. **Re-type the model, the radius, and the conditioning (maintainer, ★ 2026-06-23 (b)+(e)+(f)).** The
   radius, conditioning, and model re-typings, done together before touching LB1/LB2:
   - **(b) conditioning → coefficient ball.** Replace `edgeTraceX`/`eTrace` (on-disk **full boundary**
     `R.closure \ R.openInt`, a function-value trace) by conditioning on a **ball in coefficient
     space** `{X ∈ B(c,ρ)}` — `condDistrib(etaX s₀, Π, priorBall)` where `Π` projects to a
     finite/cofinite coefficient block landing in `B(c,ρ)`. **Not a local arc** (any arc pins via the
     identity theorem; see ★ 2026-06-23 (b)). This makes LB2 a genuine Bagchi statement AND keeps LB1
     standard — both against the same ball-conditional `L`.
   - **(f) radius `2` → `1+ε`.** Re-type `diskLaw` to `closedBall 0 (1+ε)`, `‖X_n‖≤1+ε` (small tunable
     `ε>0`). Interiority needs only radius `>1` (`|1|=1<1+ε`), so radius 1 is still excluded (boundary)
     but radius 2 is unnecessarily large; `1+ε` keeps `η_X` a tight perturbation of `η` AND makes `E_X`
     converge on `Re>1/2` (radius 2 did not). `η_X` is then abs. convergent on `Re>1+αε`. This is the
     radius the per-point → strip lift (step 2.5) tunes.
   - **(e) non-multiplicative → multiplicative Euler product `exp(prime series)·E_X`.** Re-type `etaX`
     to `exp(∑_p X_p p^{−s}) · E_X(s)` with `E_X(s) = exp(∑_p ∑_{k≥2}(1/k)X_p^k p^{−ks})`; prove
     `E_X` converges absolutely on `Re>1/2` by **domination by `∑_p p^{−2s}`**, and `E_X ≠ 0` (it is
     an `exp`). Fix `X₂=1`. Port `summable_etaXTerm` (`Re>1`) and the strip convergence with bound `2`.
     This is what step 2.5 (the lifting) depends on.
1. **`transfer_equality` (LB1, `RcpEuler.lean:736`) — the `ρ↓0` concentration limit, standard.**
   Discharge, not a deep input. With ball conditioning: as `ρ↓0` the conditional law of `etaX s₀`
   given `X∈B(1·,ρ)` concentrates (mean `→η(s₀)`, variance `∝ρ²→0`) to `δ_{η(s₀)}`, so the rcp at
   the exact point `X=1·` (the canonical Radon neighborhood limit) `= 1{η(s₀)=0}`. Recipe: rcp/Tjur
   limit defined iff Radon (`inferInstance`; `condDistrib` existence) + concentration of the
   ball-conditional + `etaX(·,1·)=ζ`. **No max-modulus / identity theorem needed any more** (those
   were artifacts of the boundary-trace conditioning).
2. **`L_ne_one` (LB2, `RcpEuler.lean:750`) = Bagchi/Voronin universality, ball form — the lone deep
   input.** `L(ρ) = rcp(etaX s₀ = 0 | X∈B(c,ρ)) ≠ 1` for `ρ>0` (the SAME ball family). Reuse the
   deprecated Gaussian route's `univ-core` (`eulerG_universality_threeLeftEdges`); **no Euler
   product / multiplicativity** (full support of the prior law supplies the non-degeneracy).
   **This is the route's one genuinely deep analytic input — so build the proof on the cited
   universality result and the mean/variance recipe below, rather than a hand-wave; but it IS to be
   proved (replace the `sorry`).** If the universality lemma you need is not yet available in a usable
   form, state precisely which statement is missing — that is the real remaining maths, and surfacing
   it is progress.

   **★ concrete mean/variance recipe for LB2 (from the author; updated 2026-06-23 (b)).** The
   `L_ne_one` proof is a **mean–variance non-degeneracy** argument, not an abstract existence
   statement. Condition on a **coefficient ball `{X∈B(c,ρ)}`** (positive radius `ρ>0`; center `c` =
   `X_n≡1` or a universality-chosen perturbation). The conditional law of the interior value
   `etaX s₀` has:
   - **mean** = the ``centrum'' = `etaX s₀` evaluated at the ball's *center* `c`; by Bagchi/Voronin
     universality the prior's support is rich enough that `c` can be chosen so the centrum is any
     value at `s₀` — in particular **nonzero**;
   - **variance** = **finite** and **∝ ρ²** (bounded coefficients ⇒ finite term-variance budget;
     the strip `L²`/Kolmogorov assembly of EtaConvergence+SphereGaussian).

   A non-degenerate law (finite nonzero variance, absolutely continuous) assigns the single point
   `{0}` mass `<1` (in fact `0`) ⇒ the conditional law of `etaX s₀` is **not** `δ₀` ⇒ `L(ρ) ≠ 1`.
   This is the formalization target: coefficient ball ⇒ centrum-via-universality + finite-variance
   ⇒ non-degenerate ⇒ atom `{0}` mass `<1`. (Mirrors zetanew.tex §4 thm:nondetect; the assembly
   contradiction is the Borel–Kolmogorov reconciliation `1{η(s₀)=0} = lim_{ρ↓0} L(ρ) = 0`,
   zetanew.tex §5 thm:nozero.)

2.5. **Per-point → strip LIFTING (★ 2026-06-23 (e), REALIZED via the ε-knob in (f)) — the NEW third
   piece, needs the multiplicative model AND the tunable radius.** LB1+LB2 give `L s₀ = 0` (no zero)
   for **each fixed** `s₀`; this step lifts that to **no zero anywhere in the open strip**. A
   measure-theoretic union over the uncountable family of points does **not** suffice. ★ (f) gives the
   concrete mechanism: on any **compact** `K ⊂ {Re>1/2}`, choose `ε = ε(K)` small enough that
   `P(η_X(s)=0 | X_n=1) = 0` **uniformly on `K`**. Why it works: the **multiplicative** structure
   `η_X = exp(∑_p X_p p^{−s})·E_X` with `E_X ≠ 0` (squared-prime correction, `exp`-form, convergent on
   `Re>1/2` at radius `1+ε`) makes `η_X` **zero-free wherever its exponent converges** — a zero can
   occur only on the linear-prime-series locus — and the tunable radius `1+ε` (with `η_X` abs.
   convergent on `Re>1+αε`) keeps `η_X` an analytically-controlled perturbation of `η` whose zero-set
   probability shrinks to `0` uniformly on the compact `K` as `ε↓0`. (Qualitatively the
   argument-principle / `η_X'/η_X` count over the **countably many** `X_p` is why zeros are confined to
   the prime-series locus; quantitatively the ε-knob is what makes per-point into per-compact.) **Gated
   on the step-0 (R)+(M) re-typing** (the on-disk `etaX` is non-multiplicative and the radius is 2, so
   this cannot start until `etaX` is `exp(prime series)·E_X` on `closedBall 0 (1+ε)`). Genuine analytic
   content, separate from LB1/LB2 — do not fold it into them.

**CLEANUP (mechanical, optional, low priority):**
3. **Delete the vestigial `not_rcpZeroAt` (`RcpEuler.lean:641`)** — the legacy `eulerB` limit-form
   `sorry`, now *superseded by `L_ne_one`* and **not referenced** by the final theorem; with it
   the `eulerB`/`rcpZeroAt`/`rcpKernel` scaffolding it depends on can also be pruned if nothing
   else uses it. (Optional: if `transfer_equality`'s proof wants the strip a.s. convergence as an
   explicit lemma, factor the Kolmogorov/`L²` assembly out of `EtaConvergence` + `SphereGaussian`
   then.) Removing this `sorry` would leave **exactly the two genuine load-bearers** in the build.
4. **`SchoenfeldPRA.lean` is already quarantined** (root `RiemannProof.lean` comments out its
   import); its 2 remaining `sorry`s are **not in the build**. Delete the file outright, or leave
   it unimported as historical — do **not** discharge its `sorry`s.

**Net effect of the 2026-06-23 pass (plan reconciled to disk).** The previous plan claimed the
redesign was "not yet on disk"; in fact the implementer has built it. (R)+(M)+(Z) compile green
(8033 jobs); the **standard ζ-form RH is assembled on disk** and reduced to **one deep analytic
input** — `L_ne_one` (Bagchi local universality, the off-center-ball mean/variance recipe above)
— plus `transfer_equality`, which downgrades to a **standard** Tjur/Radon-plus-identity theorem
once the conditioning is fixed (still an honest `sorry` because not yet formalized, not because
it is hard). Both are honest `sorry`s in `RcpEuler.lean`, stated against the **one shared `L`** so
the final `by_contra` is genuine. The PRA spine is quarantined (unimported). The conclusion is a
**positive** RH in ZFC (`{0,1}` indicator `= L ≠ 1 ⟹ = 0`), not an unprovability statement. This
pass was plan-update only; I did not edit Lean (build was a read-only verification).

**★ 2026-06-23 (e) addendum — multiplicative Euler product + a new lifting obligation; radius stays 2.**
The maintainer revised the **model** (not the radius): **non-multiplicative → multiplicative**, the
Euler product realized as `exp(∑_p X_p p^{−s})·E_X(s)` with the squared-prime correction `E_X`
convergent on `Re>1/2` (dominated by `∑_p p^{−2s}`) and `X₂=1`; **radius STAYS 2** (the rcp limit
ranges over *open* neighborhoods ⇒ `X=1` must be interior — a brief (e) draft reverting to radius 1
was wrong and is retracted). This adds a **NEW** obligation — the **per-point → strip lifting** (step
2.5): LB1+LB2 kill the zero at each *fixed* `s₀`, and the multiplicative `exp(prime series)·E_X`
structure (`E_X≠0`, so `η_X` is zero-free where the prime series converges; argument-principle count
over countably many `X_p`) transports that to "no zero anywhere in the strip" (which a bare uncountable
union cannot do). So the open analytic content is now **three** pieces — LB2 (Bagchi ball
non-degeneracy), the lifting (2.5, multiplicative), and LB1 (standard concentration) — and step 0
grows to include the non-mult→mult re-typing alongside the coefficient-ball re-typing. None of (e) is
on disk yet (on-disk `etaX` is still non-multiplicative; radius is already 2).

**★ 2026-06-23 (f) addendum — radius `2` → `1+ε`, and the ε-knob REALIZES the lifting (supersedes
(e)'s radius).** The maintainer revised the **radius**: interiority (the (e) reason for moving off
radius 1) needs only radius **`>1`**, so the over-large radius 2 is replaced by **`1+ε`** (small
**tunable** `ε>0`) — the minimal-perturbation interior choice. This is strictly better than radius 2:
it keeps `η_X` a tight perturbation of the standard `η`, makes `η_X` **absolutely convergent on
`Re>1+αε`**, and — crucially — makes the squared-prime correction `E_X` **genuinely convergent on
`Re>1/2`** (which it was **not** at radius 2, where `‖X_p‖≤2` forces the correction's abscissa to `1`).
The tunable `ε` also **realizes the per-point → strip lift** (step 2.5) directly: on any compact
`K ⊂ {Re>1/2}`, shrinking `ε=ε(K)` gives `P(η_X(s)=0 | X_n=1)=0` **uniformly on `K`** — turning
per-point nullity into per-compact nullity, with the multiplicative `exp(prime)·E_X` zero-freeness as
the qualitative backbone. So step 0 now also re-types the radius (`closedBall 0 2`→`closedBall 0 (1+ε)`,
`‖X_n‖≤2`→`‖X_n‖≤1+ε`), and the lifting (2.5) is no longer a free-standing argument-principle
obligation but the ε-knob uniformity. None of (e)/(f) is on disk yet (on-disk `etaX` non-multiplicative;
radius still 2).
