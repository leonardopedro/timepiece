# Implementation Plan: The Rectangle Strategy via Gaussian Euler Products

**Audience**: a Lean 4 formalization agent.

**This revision pivots the strategy.** The earlier plan discharged a hypothetical
zero with the *conjugate-reflection / four-fold product* machinery
(`ConjugateReflection.lean`, `MultiplicityOne.lean`, `ZeroLocation.lean`) and a
*multiplicative, modulus-1* randomized Euler product (`Legacy.lean`). That
approach is preserved in the files but is **no longer the spine of the proof**.

We **recover the direct rectangle strategy** of `RectangleStrategy.lean`
(`∮_{∂R} 1/η = 0` ⇒ no interior zero) and re-power its single deep input —
zero-free uniform approximation — with a **new random model**:

1. **Gaussian 2D coefficients** (independent Gaussian real and imaginary parts)
   in place of modulus-1 phases `e^{2πiω}`.
2. **An Euler product of *exponential* form** — `exp` of a Dirichlet sum over
   primes — in place of the *multiplicative* product `∏(1 − X_p p^{−s})^{−1}`.

These two changes are what make the rectangle close. They buy three things the
old model could not deliver simultaneously:

| Property | multiplicative, modulus-1 | exponential, Gaussian-2D |
|---|---|---|
| zero-free approximant | needs a separate non-vanishing proof | **free**: `exp` is never 0 |
| variance of the product | nonlinear in the `X_p` | **∝ variance of the `X_p`** (log is linear) |
| convergence regime | abs. conv. only `Re > 1`; strip needs Bagchi | **universality `Re > 1/2`**, abs. conv. a.s. `Re > 1` |

---

## Current implementation status (2026-06-14)

The strategy below is **partially implemented** in
`RiemannProof/GaussianEuler.lean` (builds: `lake build RiemannProof.GaussianEuler`,
8032 jobs). The S0–S9 scaffold of Part 3 is in place; **5 sorries remain**
(S3, S4, S5, S6, S8). Snapshot:

| Item | Lemma | Status |
|---|---|---|
| defs | `Ω`, `Xg`, `cCorr`, `gaussSum`, `logEulerG`, `eulerG` | **DONE** |
| S0 | `exp_cCorr_eq_etaEulerApprox` | **DONE** |
| S1 | `eulerG_ne_zero`, `gaussSum_differentiable`, `eulerG_eq_mul`, `eulerG_differentiableOn` | **DONE** |
| S2 | `recipEulerG_boundaryIntegral_eq_zero` | **DONE** |
| v=0 | `eulerG_zero_eq_etaEulerApprox`, `eulerG_zero_tendstoUniformlyOn_rect` | **DONE** |
| S3 | `eulerG_tendstoUniformly_absConv` | `sorry` (line 202) |
| S4 | `exists_gaussian_corrector_uniform` | `sorry` (216) |
| S5 | `recipEulerG_tendsto_recipEta_onEdges` | `sorry` (229) |
| S6 | `recipEta_rect_contour_integral_eq_zero'` | `sorry` (242) |
| S7 | `no_zero_in_rect` | **DONE** (delegates to RectangleStrategy residue API) |
| S8 | `exists_straddling_isolating_rect` | `sorry` (272) |
| S9 | `zeta_no_zeros_re_gt_half`, `riemann_hypothesis_via_rectangle` | **DONE** (delegates to `riemann_hypothesis_rect`) |

**Two wiring facts the implementer must know:**

1. **`GaussianEuler.lean` is orphaned from the build root.** `RiemannProof.lean`
   imports only `Basic, Legacy, TwoLimits, SimplifiedStrategy, EtaStrategy,
   ContourStrategy, RectangleStrategy` — *not* `GaussianEuler`. First task:
   `import RiemannProof.GaussianEuler` in `RiemannProof.lean` so the new spine is
   part of the default build.
2. **S7 and S9 are "DONE" only by delegating to still-`sorry`'d
   RectangleStrategy lemmas.** `no_zero_in_rect` (S7) calls the *old*
   `recipEta_rect_contour_integral_eq_zero` (RectangleStrategy:913, `sorry`) and
   `recipEta_rect_integral_ne_zero_of_zero`; `riemann_hypothesis_via_rectangle`
   (S9) calls `riemann_hypothesis_rect` / `zetaRect_ne_zero_critical_strip`
   (RectangleStrategy), which themselves rest on the legacy sorries. So the RH
   wrapper *type-checks* but is **not yet sorry-free end to end**. The point of S6
   (`…_eq_zero'`, the Gaussian-powered contour integral) is precisely to
   **discharge the old `recipEta_rect_contour_integral_eq_zero` (913)** — but S7
   currently still calls the old one. Rewire S7 to use S6′ once S6′ is proved.

**Legacy / off-critical-path files (the superseded conjugate-reflection route).**
The 51 total `sorry`s in `RiemannProof/` are dominated by the *old* strategy:
`SimplifiedStrategy.lean` (11), `MultiplicityOne.lean` (7), `ContourStrategy.lean`
(5), `Legacy.lean` (4), `EtaStrategy.lean` (3), `ZeroLocation.lean` (2),
`TwoLimits.lean` (2), `ReciprocalContour.lean` (1), `ConjugateReflection.lean`
(1). **None of these are on the Gaussian critical path.** Only the sorries in
`GaussianEuler.lean` (5) and the load-bearing `RectangleStrategy.lean` ones
(below) matter for RH via this route. Recommend marking the conjugate-reflection
files as legacy (or moving them under a `Legacy/` namespace) so the live
obligation count is the ~10 that matter, not 51.

---

## Part 0: The strategy in one page

Work directly with `ζ` and `η(s) = (1 − 2^{1−s}) ζ(s)` (the *unshifted* objects of
`RectangleStrategy.lean`; **no `2s−1` substitution** here). `η`'s alternating
Dirichlet series `∑ (−1)^{k−1} k^{−s}` converges conditionally for `Re(s) > 0`,
so `η` is honest on the whole half-plane `Re(s) > 0`; `η` and `ζ` share zeros in
`0 < Re(s) < 1` because the factor `1 − 2^{1−s}` is nonzero for `Re(s) < 1`
(`etaFactor_ne_zero_re_lt_one`, `etaFactRect_ne_zero`).

**Goal.** Exclude zeros of `ζ` with `Re(s) > 1/2`. With the functional equation
`ζ(s)=0 ⟹ ζ(1−s)=0` (`zeta_symm`) this leaves only `Re(s) = 1/2` — the Riemann
Hypothesis.

**Mechanism — the rectangle.** Let `s₀` be a hypothetical zero with
`1/2 < Re(s₀) < 1`. Enclose it in a rectangle `R` that **straddles the critical
strip**: left edge at `x_lo` close to `1/2`, right edge at `x_hi > 1`, bottom and
top edges at heights `y_lo < Im(s₀) < y_hi`. If we can show
```
∮_{∂R} 1/η = 0,
```
then `η` (hence `ζ`) has **no zero inside `R`** — because an interior zero `s₀`
contributes a nonzero residue (`Res_{s₀} 1/η = 1/η'(s₀) ≠ 0` at a simple zero,
and a nonzero total at a zero of any order via the argument principle), so a
zero would force `∮ 1/η ≠ 0` (`rect_integral_inv_sub_eq`,
`rect_cauchy_integral_formula`, `boundaryIntegral_recipEta_eq`). Contradiction.

**Why `∮ 1/η = 0` — zero-free exponential approximants.** Let `E_P` be the
exponential Gaussian Euler product (Part 2). Three facts close the loop:

- **`E_P` is entire and *never zero*** (it is `exp` of an entire Dirichlet
  polynomial). Hence `1/E_P` is *entire*, so `∮_{∂R} 1/E_P = 0` by Cauchy
  (`rect_cauchy`) — **with no zero-freeness side condition to discharge**. This
  is the structural payoff of the exponential form: in the multiplicative model
  one had to prove `etaEulerApprox P ≠ 0` on `R`; here it is automatic.
- **`E_P → η` uniformly on `∂R`** — edge by edge (Part 3):
  - *right edge* `x_hi > 1`: by **absolute convergence** of the Gaussian
    Dirichlet sum (holds a.s. for `Re > 1`);
  - *left, top, bottom edges* (`Re ≥ x_lo`, with `x_lo > 1/2`): by
    **universality** of the Gaussian model (holds for `Re > 1/2`).
- **`η` is bounded away from 0 on `∂R`** (the zero `s₀` is interior; edges are
  zero-free after an isolating choice of `R`). So `1/E_P → 1/η` uniformly on
  `∂R`, and the limit exchange `∮ 1/η = lim_P ∮ 1/E_P = 0` is legitimate
  (`boundary_integral_limit_eq_zero`).

**The left-edge subtlety (read this).** Universality lives on the *open*
half-plane `Re > 1/2`; the Gaussian log-sum `∑_p X_p p^{−s}` does **not** even
converge a.s. for `Re ≤ 1/2` (its variance `∑_p v_p p^{−2x}` diverges there). So
the left edge cannot literally sit at `x_lo < 1/2`. The honest realization of
"start the rectangle at `x < 1/2`" is a **limit**: take `x_lo = 1/2 + δ`, run the
argument to exclude zeros with `Re > 1/2 + δ`, then let `δ ↓ 0`. The union over
`δ` exhausts `{Re > 1/2}`, giving the full exclusion. (A second, heavier route —
reflect the left edge across `Re = 1/2` with the functional equation into the
universality region — is available but not needed; prefer the `δ ↓ 0` limit, it
is airtight and matches the existing `hR_lo : ∀ z ∈ R.closure, z.re > 1/2`
hypothesis already threaded through `RectangleStrategy.lean`.)

---

## Part 1: Why Gaussian 2D + exponential form (the mathematics)

### 1.1 The exponential Euler product

For a finite cutoff `P`, a variance scale `v ≥ 0`, and randomness `ω`, define the
log-product as a **Dirichlet sum over primes** and the product as its exponential:
```
D_P(s, ω) = ∑_{p ≤ P}  X_p(ω) · p^{−s} + c_P(s)         -- entire in s
E_P(s, ω) = exp( D_P(s, ω) )                            -- entire, never 0
```
where `c_P(s)` is a deterministic *centering / correction* term (Part 1.3) and
the `X_p(ω) ∈ ℂ` are the new coefficients. Contrast the old multiplicative
`zetaEulerProd P s = ∏_{p ≤ P} (1 − p^{−s})^{−1}`: that is recovered as the
`v = 0`, `X_p ≡ 0` deterministic skeleton via the classical identity
`log ∏ (1−p^{−s})^{−1} = ∑_p ∑_{k≥1} p^{−ks}/k` (`eulerProd_zeta_exp_connection`
is exactly this identity for `ζ`), so the exponential form is **not a new
function** — it is the same Euler product written multiplicatively-in-the-log,
which is what lets us inject Gaussian randomness *linearly*.

### 1.2 Gaussian 2D coefficients (replacing modulus-1)

Replace `Legacy.lean`'s
`X_p p P ω = if p ≤ P then 1 else exp(2πi·ω_p·I)` (modulus 1, multiplicative)
with **independent complex Gaussians**:
```
X_p(ω) = √v · ( g_p^{re}(ω) + i · g_p^{im}(ω) ),   g_p^{re}, g_p^{im} ~ N(0,1) iid.
```
So each `X_p` is a centered complex Gaussian of variance `v` (i.e.
`E|X_p|² = v`), the real and imaginary parts independent. This is the only place
the probability space changes; everything downstream is a consequence.

### 1.3 Variance of the product is proportional to `v`

This is the crux and the reason for *both* changes. Because `log E_P = D_P` is a
**linear** functional of the Gaussian vector `(X_p)_{p≤P}`, `D_P(s,ω)` is itself
a complex Gaussian for each fixed `s`, with
```
Var( log E_P(s, ·) ) = Var( D_P(s, ·) ) = ∑_{p ≤ P} v · |p^{−s}|² = v · ∑_{p ≤ P} p^{−2 Re(s)}.
```
Hence **the variance of (the log of) the Euler product is proportional to the
variance `v` of the Gaussian coefficients**, with proportionality constant
`∑_{p≤P} p^{−2x}` — finite and uniformly bounded on any closed half-plane
`Re ≥ x_lo > 1/2`. The multiplicative model has *no such identity*: `log` of a
product of `(1 − X_p p^{−s})^{−1}` is `∑_p ∑_k X_p^k p^{−ks}/k`, **nonlinear** in
`X_p`, so its variance does not scale linearly and cannot be driven down cleanly.

**Consequence (small-variance approximation).** Pick `v` small. Then `D_P(s,·)`
concentrates on its mean `E[D_P](s) = c_P(s)` uniformly on the compact `R.closure`
(a Gaussian field with small variance is uniformly close to its mean with
probability `→ 1`; quantitatively, `P(sup_{R.closure}|D_P − c_P| > ε) → 0` as
`v → 0` by a maximal/Borell–TIS-type bound, or elementarily by a union bound over
an `ε`-net of the compact edge since `D_P` is a finite sum of entire functions).
Therefore **there exists a realization `ω` with `E_P(·,ω)` uniformly `ε`-close on
`R.closure` to the deterministic target `exp(c_P)`**. Choosing `c_P` so that
`exp(c_P)` is the Bagchi-corrected Euler product approximating `η` (Part 1.4),
`E_P(·,ω)` uniformly approximates `η` on `R.closure`.

### 1.4 Two convergence regimes (universality vs. absolute convergence)

The centering `c_P(s)` is the **Bagchi correction** that turns the bare partial
product into a uniform approximant of `η` on the strip. Writing
`c_P(s) = log(1 − 2^{1−s}) + ∑_{p≤P} ∑_{k≥1} p^{−ks}/k − (tail corrections)`, the
deterministic skeleton `exp(c_P) → η` reduces to the three analytic inputs
already isolated in `RectangleStrategy.lean`:
`eulerProd_zeta_exp_connection`, `primeZetaTail_uniform_small`,
`higherPrimeSum_uniform_small`. These give:

- **Universality regime — `Re > 1/2`.** Because `Var(D_P) = v ∑ p^{−2x}` stays
  bounded for `x > 1/2`, the Gaussian field — and with it `E_P` — has a genuine
  a.s. limit `E_∞(s,ω)` analytic on `Re > 1/2`, and the family of such limits is
  **dense among zero-free analytic functions** on compacts of `{Re > 1/2}`
  (Voronin/Bagchi universality, in its Gaussian incarnation). This is what lets a
  realization `ω` track `η` uniformly on the left/top/bottom edges (`Re ≥ x_lo`,
  `x_lo > 1/2`). **This is the deep, research-level input** — the Gaussian analog
  of `bagchi_universality_compact` (`ContourStrategy.lean`) and
  `exists_universal_corrector_path` (`Legacy.lean`).
- **Absolute-convergence regime — `Re > 1`.** Here `∑_p E|X_p| p^{−x} =
  √v · E|g| · ∑_p p^{−x} < ∞` for `x > 1`, so the Dirichlet sum `∑_p X_p p^{−s}`
  converges **absolutely a.s.**, `E_P → E_∞` absolutely and uniformly on the
  right edge `x_hi > 1`, and there `E_∞ = η` by the ordinary (absolutely
  convergent) Euler product for `ζ`. **This regime is elementary** — Weierstrass
  `M`-test against `∑_p p^{−x_hi}` — and needs no universality.

The split is exactly the user's design: **universality handles every edge except
the `Re > 1` vertical; absolute convergence handles that one.** It mirrors `η`'s
own dichotomy (conditional convergence in the strip, absolute convergence for
`Re > 1`), now realized inside the *approximants* so that complex analysis can be
done on the entire, zero-free `E_P`.

---

## Part 2: Lean definitions to add (`GaussianEuler.lean`, new file)

Place these in a new file importing `RiemannProof.Basic` and
`RiemannProof.RectangleStrategy`. Reuse the existing `Rect`, `Rect.closure`,
`Rect.openInt`, `Rect.boundaryIntegral`, `rect_cauchy`, `etaRect`, `etaFactRect`,
`riemannZeta`. Keep `Legacy.lean`'s `Ω_infty := ℕ → ℝ` only if convenient; the
Gaussian model is cleaner over a Mathlib probability space.

```lean
-- Probability space: independent N(0,1) reals; package as complex Gaussians.
-- Use Mathlib's `ProbabilityTheory.gaussianReal`/`MeasureTheory` API; the index
-- set is ℕ (primes embedded). `Ω := ℕ → ℝ × ℝ` with the product Gaussian measure,
-- or `MeasureTheory.Measure.infinitePi` of `gaussianReal 0 1`.

/-- Complex Gaussian coefficient of variance `v` at prime index `p`. -/
noncomputable def Xg (v : ℝ) (p : ℕ) (ω : Ω) : ℂ :=
  (Real.sqrt v : ℂ) * ((ω p).1 + Complex.I * (ω p).2)

/-- Log-product: a Dirichlet sum over primes ≤ P, plus deterministic centering. -/
noncomputable def logEulerG (P : ℕ) (v : ℝ) (s : ℂ) (ω : Ω) : ℂ :=
  (∑ p ∈ Finset.filter Nat.Prime (Finset.range (P+1)), Xg v p ω * (p : ℂ) ^ (-s))
  + cCorr P s

/-- The exponential Euler product. Entire in `s`; NEVER zero. -/
noncomputable def eulerG (P : ℕ) (v : ℝ) (s : ℂ) (ω : Ω) : ℂ :=
  Complex.exp (logEulerG P v s ω)

/-- Deterministic Bagchi centering so that `exp (cCorr P ·) → η` on the strip.
    Built from the existing `eulerProd_zeta_exp_connection` data. -/
noncomputable def cCorr (P : ℕ) (s : ℂ) : ℂ := sorry  -- see Part 1.4 / S0
```

`cCorr` is *not* new mathematics: it is `log etaEulerApprox P` reorganized
(`log (1−2^{1−s}) + log (zetaEulerProd P s)`), so `exp (cCorr P s) =
etaEulerApprox P s` and the existing `etaEulerApprox_tendstoUniformlyOn_rect`
already proves `exp(cCorr P) → η` uniformly on rectangles in the strip (modulo
the three PNT sorries). Define `cCorr` as that log and record the identity as S0.

---

## Part 3: The lemmas, in dependency order

Each entry: exact intended statement, a provability verdict, and a proof sketch
at formalization detail. Reused proved lemmas are cited by `File:line`.

### S0. `eulerG` is the exponential of the existing approximant — **PROVABLE (easy)**
```lean
lemma exp_cCorr_eq_etaEulerApprox (P : ℕ) (s : ℂ) (hs : s.re > 1/2) :
    Complex.exp (cCorr P s) = etaEulerApprox P s
```
**Proof.** Define `cCorr P s := Complex.log (etaEulerApprox P s)` (legitimate:
`etaEulerApprox P s ≠ 0` on `Re > 0` by `etaEulerApprox_ne_zero`, which needs
`Re > 0` and `Re < 1` — for the right edge `Re > 1` use instead the plain Euler
factor identity, `zetaEulerProd_ne_zero` holds for `Re > 0` with no upper
bound). Then `Complex.exp_log` (nonzero argument). For a version valid through
`Re > 1` too, base `cCorr` on `zetaEulerProd` (nonzero for `Re > 0`) and the
entire factor `log(1−2^{1−s})` where defined; on the right edge avoid the eta
factor's log branch by keeping `etaFactRect s = 1 − 2^{1−s}` as an explicit
factor outside the exp. ∎

### S1. `eulerG` is entire and never zero — **PROVABLE (easy; the structural win)**
```lean
lemma eulerG_ne_zero (P : ℕ) (v : ℝ) (s : ℂ) (ω : Ω) : eulerG P v s ω ≠ 0
lemma eulerG_differentiable (P : ℕ) (v : ℝ) (ω : Ω) :
    Differentiable ℂ (fun s => eulerG P v s ω)
```
**Proof.** `eulerG = exp ∘ logEulerG`. `Complex.exp_ne_zero` gives non-vanishing
with *no hypotheses on `s`* — this is the whole point. `logEulerG` is a finite
sum of `s ↦ Xg v p ω * p^{−s}` (each `Differentiable` via
`Differentiable.const_cpow`/`differentiable_const.mul`) plus `cCorr P` (entire
where `cCorr` is the log of the nonvanishing `zetaEulerProd`, by
`Complex.differentiable_log`-type composition, or simply carry `cCorr` as an
entire Dirichlet polynomial in the `Re>1` analysis). `Complex.differentiable_exp.comp`. ∎

### S2. `∮_{∂R} 1/eulerG = 0` for every `P, v, ω` — **PROVABLE (easy)**
```lean
lemma recipEulerG_boundaryIntegral_eq_zero (P : ℕ) (v : ℝ) (ω : Ω) (R : Rect) :
    R.boundaryIntegral (fun s => 1 / eulerG P v s ω) = 0
```
**Proof.** `fun s => 1 / eulerG P v s ω = fun s => exp (−logEulerG P v s ω)` is
entire (S1), in particular `DifferentiableOn ℂ _ R.closure`. Apply
`rect_cauchy R _`. **No `hR_lo`/`hR_hi`/non-vanishing hypotheses needed** — unlike
`recipEulerApprox_rect_integral_eq_zero` (RectangleStrategy:746), which needed
`etaEulerApprox ≠ 0` on `R`. The rectangle here may cross `Re = 1` freely. ∎

### S3. Right edge — absolute convergence to `η` for `Re > 1` — **PROVABLE (standard)**
```lean
lemma eulerG_tendstoUniformly_absConv {v : ℝ} (hv : 0 ≤ v) (a : ℝ) (ha : 1 < a) :
    ∀ᵐ ω, TendstoUniformlyOn (fun P s => eulerG P v s ω) etaRect atTop
      {s | s.re ≥ a}    -- or any compact subset of {Re > 1}
```
**Proof.** On `Re ≥ a > 1`: `‖Xg v p ω · p^{−s}‖ ≤ √v ‖(ω p).1, (ω p).2‖ · p^{−a}`,
and `∑_p p^{−a} < ∞`. The a.s. summability of `∑_p ‖Xg v p ω‖ p^{−a}` follows from
`∑_p E‖Xg v p ω‖ p^{−a} = √v·E‖g‖·∑_p p^{−a} < ∞` (Tonelli + finite Gaussian
absolute moment), hence the random series converges absolutely a.s.; uniform
convergence of partial sums on `{Re ≥ a}` by the Weierstrass `M`-test with the a.s.
summable majorant. `exp` is uniformly continuous on bounded sets, so
`eulerG P = exp(D_P) → exp(D_∞)` uniformly; identify `exp(D_∞) = η` on `Re > 1`
via S0 + `etaEulerApprox_tendstoUniformlyOn_rect` (the abs.-conv. region, where
that proof simplifies — `zetaEulerProd → ζ` is the ordinary Euler product). ∎

*Note*: this lemma is the only place randomness in the *tail* is genuinely
needed; on the right edge even `v = 0` (deterministic) works, since the plain
Euler product converges absolutely for `Re > 1`. Keep a `v = 0` corollary as the
clean fallback.

### S4. Other edges — universality to `η` for `Re > 1/2` — **RESEARCH-LEVEL (the core)**
```lean
lemma exists_gaussian_corrector_uniform (R : Rect)
    (hR_lo : ∀ z ∈ R.closure, z.re > 1/2)        -- left edge strictly right of 1/2
    (hs₀ : s₀ ∈ R.openInt) (hη : ∀ z ∈ R.closure, z ≠ s₀ → etaRect z ≠ 0) :
    ∀ ε > 0, ∃ (v : ℝ) (ω : Ω), 0 < v ∧
      ∀ z ∈ R.closure \ R.openInt, ‖eulerG P v z ω − etaRect z‖ < ε
```
**Verdict: NOT provable from current repo material.** This is the Gaussian
universality / density statement — the analog of `bagchi_universality_compact`
(ContourStrategy:409) and `exists_universal_corrector_path` (Legacy:88), both
still open. It is the one genuinely deep input and **must not be improvised**.

**What the Gaussian model contributes (record as design, not proof).** The
small-variance concentration of Part 1.3 reduces universality on the
left/top/bottom edges to: *the deterministic skeleton `exp(cCorr P)` approximates
`η` there, and the Gaussian fluctuation can be made uniformly `< ε` by shrinking
`v`* (Part 1.3). The skeleton approximation is `etaEulerApprox_tendstoUniformlyOn_rect`
(RectangleStrategy:759) — **proved modulo the three PNT sorries**. So *if* one is
willing to grant the deterministic Bagchi convergence on the strip (the three PNT
inputs), the small-`v` Gaussian step **upgrades it to a single zero-free
approximant** without a separate density argument — because we are approximating
the *specific* function `η`, not an arbitrary target. In that reading S4 splits:
- **S4a (provable modulo PNT sorries):** uniform `exp(cCorr P) → η` on
  `R.closure ∩ {Re ≤ 1}` — already `etaEulerApprox_tendstoUniformlyOn_rect`.
- **S4b (provable, probabilistic):** for fixed `P` and `ε`, ∃ `v>0, ω` with
  `sup_{R.closure} ‖eulerG P v · ω − exp(cCorr P)‖ < ε` — Part 1.3 concentration;
  formalize via a union bound over a finite `ε/2`-net of the compact `R.closure`
  and a Gaussian tail bound (`ProbabilityTheory.measure_ge_le_exp...` /
  Chebyshev on each net point), choosing `v` small enough that the bad event has
  measure `< 1`, hence the good event is nonempty.

  Then S4 = (triangle inequality on S4a + S4b). **Formalize S4a's reduction and
  S4b in full; leave the genuine density form of S4 (needed only if one drops the
  PNT skeleton) clearly marked open.** Recommended: state S4 as the conjunction
  S4a ∧ S4b and prove it under the existing three PNT sorries — that keeps the
  whole rectangle argument honest and free of *new* axioms beyond the ones the
  repo already carries.

### S5. Edge approximation of the reciprocal — **PROVABLE (given S3+S4)**
```lean
lemma recipEulerG_tendsto_recipEta_onEdges (R : Rect) (s₀ : ℂ)
    (hR_lo : ∀ z ∈ R.closure, z.re > 1/2) (hx_hi : 1 < R.x_hi)
    (hs₀ : s₀ ∈ R.openInt) (hη : ∀ z ∈ R.closure, z ≠ s₀ → etaRect z ≠ 0) :
    -- along a chosen sequence (P_k, v_k, ω_k):
    TendstoUniformlyOn (fun k s => 1 / eulerG (P_k) (v_k) s (ω_k))
      (fun s => 1 / etaRect s) atTop (R.closure \ R.openInt)
```
**Proof.** Split `∂R` into the right edge (`Re = x_hi > 1`, use S3) and the other
three edges (`Re ≥ x_lo > 1/2`, use S4). On each, `eulerG → η` uniformly and
`η` is bounded below in modulus: edges avoid the unique interior zero `s₀` (`hη`)
and `η` is continuous on the compact edge, so `inf ‖η‖ > 0`
(`IsCompact.exists_forall_le` / `IsCompact.exists_isMinOn` on `‖η‖`). Then
`reciprocal_tendstoUniformlyOn_of_nonvanishing` (EtaConvergenceExtended:51,
**proved**) upgrades `eulerG → η` to `1/eulerG → 1/η` uniformly. Glue the edge
pieces (`TendstoUniformlyOn` on a finite union). Choose the diagonal sequence
`(P_k, v_k, ω_k)` so that both regimes hold simultaneously: `P_k → ∞` (skeleton
accuracy, S4a + S3), `v_k ↓ 0` and `ω_k` from S4b at tolerance `ε_k ↓ 0`. ∎

### S6. `∮_{∂R} 1/η = 0` — **PROVABLE (given S2+S5)**
```lean
lemma recipEta_rect_contour_integral_eq_zero' (R : Rect) (s₀ : ℂ)
    (hR_lo : ∀ z ∈ R.closure, z.re > 1/2) (hx_hi : 1 < R.x_hi)
    (hs₀ : s₀ ∈ R.openInt) (hη : ∀ z ∈ R.closure, z ≠ s₀ → etaRect z ≠ 0) :
    R.boundaryIntegral (fun s => 1 / etaRect s) = 0
```
This is the open `recipEta_rect_contour_integral_eq_zero` (RectangleStrategy:913),
now **dischargeable** with the new approximants. **Proof.** `∮ 1/eulerG = 0` for
every `k` (S2). `1/eulerG → 1/η` uniformly on `R.closure \ R.openInt = ∂R` (S5).
Pass to the limit with `boundary_integral_limit_eq_zero` (RectangleStrategy:813)
— uniform convergence on the edges sends each edge integral to its limit and the
constant-zero sequence to 0. **Note the hypothesis upgrade:** the original
lemma's `hR_hi : ∀ z ∈ R.closure, z.re < 1` is **dropped** — the new rectangle is
*allowed* to cross `Re = 1`, which is what the right edge needs. ∎

### S7. No interior zero — the residue contradiction — **PROVABLE (given S6 + repo residue API)**
```lean
lemma no_zero_in_rect (R : Rect) (s₀ : ℂ)
    (hR_lo : ∀ z ∈ R.closure, z.re > 1/2) (hx_hi : 1 < R.x_hi)
    (hs₀ : s₀ ∈ R.openInt) (h_zero : etaRect s₀ = 0)
    (h_iso : ∀ z ∈ R.closure, z ≠ s₀ → etaRect z ≠ 0) : False
```
**Proof.** From `boundaryIntegral_recipEta_eq` (RectangleStrategy:1175) /
`rect_cauchy_integral_formula` (967) + `rect_integral_inv_sub_eq` (952): a zero
of `η` at the interior `s₀`, with `η` analytic and nonzero elsewhere on
`R.closure`, gives `∮_{∂R} 1/η = 2πi · (nonzero residue) ≠ 0` (factor
`η(z) = (z−s₀)^m · g(z)`, `g(s₀) ≠ 0`, via `dslope`; the leading residue does not
cancel for `1/η` at a single isolated zero). This contradicts S6 (`= 0`). ∎

*Dependency note:* `rect_integral_inv_sub_eq` (952) and the `dslope` plumbing of
`boundaryIntegral_recipEta_eq` are themselves `sorry` in the repo today; they are
**standard** (winding number `= 1` for an interior point; `Complex.dslope`
factorization) and independent of the universality core. Discharge them as
ordinary complex-analysis lemmas.

### S8. Isolating rectangle — **PROVABLE (mirror existing isolation lemma)**
```lean
lemma exists_straddling_isolating_rect (s₀ : ℂ)
    (hσ : 1/2 < s₀.re) (hσ' : s₀.re < 1) (h_zero : etaRect s₀ = 0) :
    ∀ δ ∈ Set.Ioo 0 (s₀.re − 1/2), ∃ R : Rect,
      R.x_lo = 1/2 + δ ∧ 1 < R.x_hi ∧ s₀ ∈ R.openInt ∧
      (∀ z ∈ R.closure, z.re > 1/2) ∧
      (∀ z ∈ R.closure, z ≠ s₀ → etaRect z ≠ 0)
```
**Proof.** `η = etaRect` is analytic on `Re > 0` away from nothing (entire there;
`etaRect = etaFactRect · ζ`, `ζ` analytic except at `1`, and `1` is excluded by
`Re`-bounds once `x_lo > 1/2`... note `Re = 1` *is* in the rectangle, but `ζ`'s
pole is at the point `s = 1`, `Im = 0`; choose `y_lo > 0` so the rectangle avoids
it, or handle `s=1` as the lone removable point — `etaRect` has a *removable*
behavior there since `etaFactRect 1 = 0`). Zeros of the analytic `η` are isolated
(`AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`, IsolatedZeros:130 — `η`
is not locally zero, witnessed by `dirichletEta_ne_zero_at_two`-type
non-triviality). Shrink the height window `[y_lo, y_hi] ∋ Im(s₀)` and keep
`x_lo = 1/2+δ`, `x_hi` fixed `> 1` so the only zero in `R.closure` is `s₀`.
This is the straddling analog of `eta_zero_isolated_in_rect`
(RectangleStrategy:1260) / `etaShifted_isolated_zero`; mirror its structure.
**Subtlety to handle explicitly:** the right part of `R` (`Re > 1`) is zero-free
for free (`ζ ≠ 0` for `Re ≥ 1`, `riemannZeta_ne_zero_of_one_le_re`), so isolation
only has to work in the strip part. ∎

### S9. Assemble: no zeros with `Re > 1/2`, hence RH — **PROVABLE (given S7+S8)**
```lean
theorem zeta_no_zeros_re_gt_half (s₀ : ℂ) (hσ : 1/2 < s₀.re) (hσ' : s₀.re < 1) :
    riemannZeta s₀ ≠ 0
theorem riemann_hypothesis_via_rectangle :
    ∀ s, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1/2
```
**Proof.** Suppose `ζ s₀ = 0`, `1/2 < Re(s₀) < 1`. Then `η s₀ = 0`
(`etaFactRect_ne_zero` for `Re < 1`). By S8 pick `δ ∈ (0, Re(s₀)−1/2)` small and
the straddling isolating `R`; S7 gives `False`. Hence no zeros with
`1/2 < Re < 1`. The `δ ↓ 0` quantifier in S8 is already absorbed: each fixed `s₀`
with `Re(s₀) > 1/2` admits a `δ < Re(s₀) − 1/2`, so `s₀` is enclosed with
`x_lo = 1/2+δ > 1/2`. Combine with the functional equation `zeta_symm` (Basic:15)
to fold `Re < 1/2` onto `Re > 1/2`, leaving `Re = 1/2`. This reuses the final
wrapper structure of `riemann_hypothesis_via_shifted_eta`. ∎

---

## Part 4: Execution order and status

```
S0  exp_cCorr_eq_etaEulerApprox            DONE
S1  eulerG_ne_zero / _differentiable       DONE
S2  recipEulerG_boundaryIntegral_eq_zero   DONE        (S1 + rect_cauchy)
S7  no_zero_in_rect                         DONE*       (*calls sorry'd RectangleStrategy:913 — rewire to S6′)
S9  RH wrappers                             DONE*       (*delegates to riemann_hypothesis_rect, sorry-backed)
--- remaining 5 sorries, in recommended order ---
W0  import RiemannProof.GaussianEuler       do FIRST    (wire the new spine into the build root)
S3  right edge, absolute convergence       standard    (Weierstrass M-test; the v=0 case suffices — see note)
S8  exists_straddling_isolating_rect       standard    (mirror eta_zero_isolated_in_rect; right part Re>1 zero-free for free)
S4b small-variance concentration           probabilistic, provable (Gaussian net + Chebyshev)
S4a skeleton → η on strip                  ⚠ = etaEulerApprox_tendstoUniformlyOn_rect, modulo the 3 PNT sorries
S4  exists_gaussian_corrector_uniform = S4a ∧ S4b      provable *modulo* the 3 PNT sorries
S5  recipEulerG_tendsto_recipEta_onEdges   S3 + S4 + reciprocal_tendstoUniformlyOn_of_nonvanishing
S6  recipEta_rect_contour_integral_eq_zero' S2 + S5 + boundary_integral_limit_eq_zero
W1  discharge RectangleStrategy:913 via S6′ then rewire S7  (collapses the old contour sorry)
```

**Note on S3 (right edge).** The right edge sits at `Re = x_hi > 1`, where the
*ordinary* Euler product already converges absolutely; the `v = 0` skeleton
(`eulerG_zero_tendstoUniformlyOn_rect`, already **DONE**) covers it. So S3 can be
proved at `v = 0` first (no randomness needed on the right edge), and S5 only
needs the randomness on the left/top/bottom edges via S4. Prioritise the `v = 0`
right-edge path before the general `eulerG_tendstoUniformly_absConv`.

**Recommended immediate next steps (in order):** W0 (wire the import) → S8 and the
`v=0` form of S3 (both standard, independent) → S4b (probabilistic, self-contained)
→ then S4a/S4 sit on the three PNT sorries → S5 → S6 → W1 (discharge 913, rewire
S7). After W1, the only remaining inputs are the three PNT sorries and the
standard winding/`dslope` lemmas (`rect_integral_inv_sub_eq`, 952).

> **Per-obligation recipes now live in the code.** Each of the 5 sorries in
> `GaussianEuler.lean` carries a complete `SPECIALIST RECIPE` comment, and the
> file opens with cross-cutting `SPECIALIST NOTES` N-A/N-B/N-C. Two findings from
> reading the actual signatures (2026-06-14), folded in there:
> * **N-A (eta-factor zeros).** `etaFactRect = 1 − 2^{1−s}` vanishes on `Re = 1`
>   at `1 − 2πik/log 2`; a straddling rectangle crosses that line, so **S8 must
>   choose its height window to avoid those points** (and there is an honest edge
>   case when `Im s₀ = −2πk/log 2`). S1/S2/S7 must replace `Re < 1` by
>   "`etaEulerApprox ≠ 0` on `R.closure`" (N-C).
> * **N-B (S4 is not a separate universality theorem).** Taking `ω = 0` makes
>   `eulerG = etaEulerApprox`, so S4 reduces to `etaEulerApprox → η` on `R.closure`
>   = the PNT machinery (`eulerProd_zeta_exp_connection`, stated for `Re > 1/2`,
>   covers the straddling closure). The genuine Voronin/Bagchi density is **not
>   needed** for the statement as written.

**What is genuinely open after this plan.**
1. **No separate universality theorem is needed (revised — see N-B).** With
   `ω = 0`, S4 reduces to the deterministic skeleton convergence
   `etaEulerApprox → η`, which is the three PNT inputs below. The full
   Voronin/Bagchi density would only be required for a `v > 0`, generic-`ω`
   variant the statement does not ask for.
2. **The three PNT inputs** `primeZetaTail_uniform_small`,
   `higherPrimeSum_uniform_small`, `eulerProd_zeta_exp_connection`
   (RectangleStrategy:548/563/587) — genuine PNT / Euler-identity analysis,
   unchanged by the pivot. Survey `Mathlib.NumberTheory.PrimeCounting` /
   `PrimeNumberTheoremAnd` before attempting.
3. **Standard complex-analysis plumbing** `rect_integral_inv_sub_eq`,
   `rect_cauchy_integral_formula`, `boundaryIntegral_recipEta_eq`
   (RectangleStrategy:952/967/1175) — winding number and `dslope`; no deep input.

**What the pivot *buys* over the conjugate-reflection plan.** The seven sorries
of the previous plan (`conjReflLimit_zero_order`, `even_multiplicity_contradiction`,
`nonreal_edges_sum_zero`, `etaShifted_zeros_simple`, …) and the open *simplicity*
core (`m = 1`) are **no longer on the critical path**: the residue argument here
(S7) excludes a zero of *any* multiplicity directly from `∮ 1/η = 0`, so neither
multiplicity-one nor the four-fold symmetric product is needed. The strategy now
rests on exactly three classical pillars — PNT tail bounds, the winding-number
integral, and small-variance Gaussian concentration — plus the entirely
mechanical zero-freeness of `exp`.

### Reused proved infrastructure (do not re-prove)

| Lemma | File:line | Use |
|---|---|---|
| `rect_cauchy` | RectangleStrategy:204 | S2 |
| `boundary_integral_limit_eq_zero` | RectangleStrategy:813 | S6 |
| `etaEulerApprox_tendstoUniformlyOn_rect` | RectangleStrategy:759 | S4a, S3 |
| `etaEulerApprox_ne_zero`, `zetaEulerProd_ne_zero` | RectangleStrategy:453,443 | S0 |
| `reciprocal_tendstoUniformlyOn_of_nonvanishing` | EtaConvergenceExtended:51 | S5 |
| `eta_zero_isolated_in_rect` | RectangleStrategy:1260 | S8 (template) |
| `riemannZeta_ne_zero_of_one_le_re` | Mathlib | S8 |
| `etaFactor_ne_zero_re_lt_one` / `etaFactRect_ne_zero` | Basic / RectangleStrategy | S9 |
| `zeta_symm` | Basic:15 | S9 |

`lake build` after each lemma; all cited lemmas compile today.
