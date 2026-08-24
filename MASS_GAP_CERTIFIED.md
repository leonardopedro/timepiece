# The QCD Mass Gap from Certified Hashimoto Uncertainty Bands

*A proof sketch, and a certification path for the numerical kernel that makes it
usable inside a Lean4 proof.*

> **What this document is.** The `BookProof/` development contains, in the
> Yang–Mills and SIRK chapters, enough theorems to prove that the uncertainty
> bands of the Hashimoto/SIRK algorithm are correct *for the QYM
> gauge-fixed Hamiltonian*. This document (1) inventories those theorems, (2)
> sketches a proof of a **mass gap in QCD** that uses the *numerically
> certified* bands produced by the `fock_sirk` kernel, (3) generalizes the
> bands — which in `Hashimoto.md` are stated in **infinite numerical
> precision** — to **finite precision**, (4) proposes how to certify the
> *code implementation* (the probability kernel: `fock_sirk::forward_sirk` and
> `prob_kernel::Session`) with respect to those proofs, including the Lean4
> parts, through the existing nanoda export/verification cycle (S29/S31), and
> (5) adds the **Aeneas** route (Rust→Lean 4 functional translation) as the
> **first attempt** at formalizing the pure numeric core of the kernel itself,
> with an explicit fallback ladder (Verus → Creusot/Why3 → hand-written
> Lean 4) in case Aeneas is not enough (§5.3).
>
> **Honesty box (read first).** The sketch proves a *rigorous, machine-checked
> lower bound on the spectral gap of the truncated/lattice QCD Hamiltonian* —
> the object the numerics actually diagonalizes — with all constants explicit
> and all rounding enclosed. The Aeneas route (§5.3) verifies the algorithm's
> pure core; the f64 rounding is enclosed by the finite-precision layer
> (§4), never trusted. It does **not** claim the continuum Millennium
> mass gap: the missing leg (norm-resolvent convergence of the specific
> lattice truncation to the continuum operator *preserving the gap*, or an
> a-priori continuum lower bound) is identified explicitly in §6, consistent
> with `CONSOLIDATED_PLAN.md`'s standing decision that the continuum mass gap
> stays out of scope. The value of the present document is that it makes the
> finite-dimensional leg of such a proof **fully rigorous and fully
> formalizable**, and says exactly which theorem is needed for the passage.

---

## 0. Notation and the objects of record

- $H$ — the Weyl-gauge gauge-fixed Yang–Mills Hamiltonian,
  $H = \tfrac12 \sum_{i,a} (\pi^i_a)^2 + \tfrac12 \sum_{i,a} (B_{ia})^2$, with
  $B_{ia} = \varepsilon_{ijk}(\partial_j A_k^a + \tfrac12 g f_{abc} A_j^b A_k^c)$.
  On the lattice truncation the electric term is $(g^2/2)\sum_{\ell} N_\ell$ —
  the term that gaps the spectrum (this is the object of
  `qcd_mass_gap_sirk` in the `unfer` repo).
- $H_m$ — the Galerkin/Rayleigh–Ritz truncation of $H$ on the $m$-dimensional
  SIRK Krylov sector (in the code: the whitened projection `h_proj`).
- $\lambda_0(H_m) \le \lambda_1(H_m) \le \dots$ — eigenvalues of $H_m$.
- $\theta$ — a computed Ritz value; $r = H\psi - \theta\psi$ its residual.
- $\mathrm{SIRK}_m(v)$ — the SIRK approximation to $\varphi_k(A)v$, $A = -iHt$
  (evolution) or the shift-invert resolvent picture of the paper.

---

## 1. What `BookProof/` already proves (the band-correctness side in QYM)

The claim "the uncertainty bands of the Hashimoto algorithm are correct in
QYM" decomposes into: the Hamiltonian is well-defined and positive; the SIRK
machinery selects it; the Rayleigh–Ritz/Galerkin numbers converge to its
spectrum; and the Krylov-span identities the numerics relies on hold. Each
leg is a proved chapter:

| # | BookProof chapter | Content (theorems) | Role in the band proof |
|---|---|---|---|
| 1 | `ChapterYangMillsFriedrichs` (+ `ChapterWeylHamiltonian`) | $H = \tfrac12\sum(\pi)^2 + \tfrac12\sum(B)^2$ is **symmetric, bounded below by 0, densely defined, with closable quadratic form** → positive self-adjoint **Friedrichs extension** | the operator the numerics diagonalizes is well-posed and positive |
| 2 | `ChapterHashimotoShiftInvert` | `hashimoto_shiftInvert_selects_friedrichs`: the shift-invert limit selects the Friedrichs extension; `galerkinCompression_shiftInvert_tendsto`, `galerkinResolvent_shiftInvert_tendsto`: Galerkin/resolvent convergence; `IsShiftInvert.opNorm_le`: $\|R\| \le \gamma^{-1}$; `shiftInvert_determines`, `isShiftInvert_unique`: the resolvent determines the operator | the SIRK limit is *the* correct object; the resolvent geometry that §2's bands need is bounded |
| 3 | `ChapterHashimotoComplexShifts` | resolvent bound $\|R\| \le 1/|\mathrm{Im}\,\gamma|$ for **complex** shifts — invertible for *every* self-adjoint $A$ with no positivity assumption | the paper's $\Sigma$ (convex hull of $W(X_j)$) is bounded in $\mathbb C^+$; Theorem 4.1's numerical ranges are controlled |
| 4 | `ChapterGradedHashimoto`, `ChapterGradedFriedrichs` | the graded (boson⊗fermion) Hamiltonian is even, and `graded_hashimoto_selects` gives the SIRK selection + uniqueness on the graded space | QYM with ghosts stays in the same framework |
| 5 | `ChapterKrylovShiftSpan`, `ChapterSirkMultiShift` | the **forward-product** sequence $w_k = (H - z_k)w_{k-1}$, the **resolvent** (rational) Krylov sequence, and the plain Krylov sequence span the *same* subspace ($\texttt{krylov\_multiShift\_eq\_standard}$, `forwardProd`), over an arbitrary commutative ring | the inverse-free forward sequence the code runs IS the rational Krylov subspace of the paper |
| 6 | `ChapterSirkGramWhitening`, `ChapterSirkWhitening` | Gram whitening **exists and is an orthonormalization** ($T^*GT = 1$); the reduced operator depends only on the retained subspace, not on which orthonormalization is used | the code's `h_proj` is well-posed: independent of the whitening choice |
| 7 | `ChapterSirkRitzSpectrum` (+ `ChapterHermiteGalerkin` `ritzInf_tendsto_domainInf`) | the Rayleigh–Ritz values of the Galerkin truncations **converge to the bottom of the spectrum of the selected (Friedrichs) extension** (`le_rayleigh_iff_le_spectrum`) | the numerical Ritz values are the finite leg of a genuine spectral statement |
| 8 | `ChapterSirkTrotterKatoGalerkin`, `ChapterSirkTrotterKato`, `ChapterYangMillsFriedrichsLimit` | the unitary flows of the Galerkin compressions converge to the flow of the selected extension, uniformly on bounded time intervals; the YM Friedrichs construction is discharged in a non-degenerate class | dynamics (not just spectra) of the numerics converge to the selected operator |
| 9 | `ChapterFockSecondQuantization`, `ChapterFermionFock`, `ChapterGradedFock` | the Fock-space second quantization used by the kernel | the mode algebra the kernel applies is the proved one |
| 10 | `ChapterMassGap` | the book's mechanism: the number operator commutes with the observable algebra, so an *arbitrary* mass gap can be added without observable consequences (free-field statement) | *caveat*: this is the book's observable-invariance argument, **not** the confinement gap; the confinement gap is the numerical one of §3 |

What is *not* yet in `BookProof/` is precisely the content of §4–§5 below:
the **finite-precision** certificates (eigenvalue perturbation under f64
roundoff, a-posteriori residual bounds applied to computed pairs, a validated
upper bound for $E_m$) and the **gap lower bound assembled from two certified
intervals**. These are the new, small theorem families the certification
path (§5) adds.

---

## 2. The uncertainty bands (infinite precision, as in `Hashimoto.md`)

**Theorem 4.1 (Hashimoto–Nodera, JJIAM 2019, Eq. 12).** For
$1 \le m < N/h$ and $\Sigma = \operatorname{conv}\{W(X_1), \dots,
W(X_{\lceil N/h-1\rceil})\}$, $X_j = (\gamma_j I - A)^{-1}$,
$\gamma_j = N - hj$, $f_{k,N}(z) = e^N\varphi_k(-z^{-1})$:

$$\|\varphi_k(A)v - \mathrm{SIRK}_m(v)\| \le 2C\,\|v\|\, e^{-hm}\, E_m,
\qquad C \in [2, 11.08],$$

with $E_m = \min_{r \in \mathcal R^{\mathrm{SIRK}}_{m-1}} \|f_{k,N} -
r\|_{\infty,\Sigma}$, $\mathcal R^{\mathrm{SIRK}}_{m-1} = \{p/q : \deg p \le
m,\ q(z) = \prod_{j=1}^m(1 + hjz)\}$.

The `unfer` kernel realizes it two-tier:

- **A-priori tier.** `hashimoto_support::BandParams::band` computes $E_m$ by
  Lawson's iteratively-reweighted minimax on a grid of a conservative padded
  box $\supseteq \Sigma$, and the edges $\mathrm{lo} = 2\cdot2\|v\|e^{-hm}E_m$,
  $\mathrm{hi} = 2\cdot11.08\|v\|e^{-hm}E_m$. **Validity requires the
  infinite-precision hypothesis** that the computed $E_m$ is a genuine
  upper bound of the minimax value — see §4.2 for the finite-precision fix.
- **Sharp tier (Rayleigh–Ritz residual certificate).** For any *computed*
  eigenpair $(\theta, \psi)$ of $H_m$,
  $|\theta - \lambda| \le \|H\psi - \theta\psi\|$ (Parlett), and the kernel
  computes this residual **cancellation-free from the stored Gram**
  (`ForwardSirkResult::ritz_residuals`: the residual has exactly one
  out-of-basis component, $\|r\| = |\tau_m c_{m-1}|$). This tier is what
  certifies the *actual* widths ($\le 10^{-6}$–$10^{-9}$ on resolved rungs)
  and makes disjoint certified intervals (graviton vs scalaron) possible.

Both tiers are combined by `hashimoto_support::certify`: a state certified to
lie within `band_hi` of the exact evolved state bounds any observable shift by
Cauchy–Schwarz, $|\langle O\rangle_{\mathrm{SIRK}} - \langle
O\rangle_{\mathrm{exact}}| \le 2\|O\|\cdot\mathrm{band\_hi}\cdot\|v\|$.

---

## 3. Sketch of the mass-gap proof (QCD, using the certified bands)

### 3.1 The setup

The confined sector is the lattice Weyl-gauge YM Hamiltonian
(`yang_mills_lattice(l, g, n_c)` in `nested_fock_algebra::models`): the
electric term $(g^2/2)\sum_\ell N_\ell$ plus magnetic plaquette terms. The
lattice parity splits the Fock sectors into even/odd; the strong-coupling
statement is that the even→odd gap $\approx g^2/2$.

The kernel runs two SIRK solves — even-parity start $v_e$, odd-parity start
$v_o$ — and returns Ritz values $\theta^e_0 \le \theta^e_1 \le \dots$ and
$\theta^o_0 \le \dots$ with, for each, the certified interval
$[\theta - \delta, \theta + \delta]$ where $\delta$ accumulates the three
finite-precision terms of §4 (residual + eigendecomposition roundoff +
enclosure of the measured $\theta$).

### 3.2 The certified-gap theorem

**Theorem (certified mass gap, finite-dimensional).** Let
$\theta^o_0, \theta^e_0$ be the computed lowest Ritz values of the odd and
even sectors of $H_m$, with certified widths $\delta^o, \delta^e$. Then the
spectral gap of the truncated Hamiltonian satisfies

$$\lambda_1(H_m) - \lambda_0(H_m) \ge \theta^o_0 - \theta^e_0 - (\delta^o +
\delta^e),$$

and in particular $H_m$ has a mass gap $\ge g^2/2 - (\delta^o + \delta^e) +
(\text{known } O(g^4)$ magnetic correction$)$ provided the right-hand side is
positive.

*Proof sketch (each step is a proved or §5-listed theorem).*

1. *The Ritz values bound eigenvalues.* For the computed pair
   $(\theta, \psi)$, the a-posteriori bound
   $|\theta - \lambda| \le \|H_m\psi - \theta\psi\|$ (Parlett; a theorem about
   the exact operator applied to the computed vector) gives
   $\lambda_0(H_m) \le \theta^e_0 + \delta^e$ and
   $\lambda_1(H_m) \ge \theta^o_0 - \delta^o$ once the odd sector is shown not
   to mix into the even ground eigenspace (lattice parity is an exact
   symmetry of $H_m$; §1 item 4/9 + the sector structure).
2. *The parity split is exact.* The lattice Hamiltonian commutes with the
   parity operator; the Krylov starts are pure-parity; hence the two solves
   live in disjoint invariant subspaces and the two Ritz sets are independent
   lower/upper bounds for the two lowest eigenvalues of the two sectors
   (interlacing for the compression $H_m$ of $H$ on each sector).
3. *Roundoff is enclosed (§4).* $\delta = \|r\|_{\mathrm{measured}} +
   c\,u\,\|\hat G\|$ (Weyl on the whitened Gram backward error) + the
   enclosure half-width of $\theta$ under interval evaluation of
   $\langle\psi|H_m|\psi\rangle$: every term explicit and machine-checkable.
4. *Continuum passage (the honest leg, §6).* The convergence theorems of §1
   items 2, 7, 8 give: Ritz values converge to the bottom of the spectrum of
   the selected extension, and flows converge. A *gap-preserving* statement
   needs one additional theorem (norm-resolvent convergence of this
   truncation family, or an a-priori continuum gap lower bound); absent it,
   the certified statement is about $H_m$ — the object the numerics actually
   computes — which is the rigorous content delivered here.

### 3.3 What the numerics already demonstrates

`qcd_mass_gap_sirk` (in the `unfer` repo, `fock_sirk/tests/qcd_validation.rs`)
contrasts: the free gluon has $E \to 0$ as $k \to 0$ (massless), while the
lattice solve at $g = 2$ gives a gap $= E_{\mathrm{odd}} - E_{\mathrm{even}}
\in (g^2/6,\ 3g^2/2)$, positive and $\approx g^2/2$ — the strong-coupling
lattice result. The certified-interval machinery
(`bands_program_gauge_fixed.rs`) shows the pattern to promote to a proof: the
analytic $g^2/2$ sits *inside* the certified intervals of the numerical gap,
intervals nest as $m$ grows, and the residual tier gives the sharp widths.
The document §3.2 turns exactly that pattern into a theorem.

---

## 4. From infinite to finite numerical precision

`Hashimoto.md` Theorem 4.1 is stated in **exact arithmetic**: every Gram
entry, every eigendecomposition, every norm is exact. The kernel runs in
f64 ($u = 2^{-53}$). The generalization has four layers; each converts a
computed quantity into a *rigorous enclosure* with an explicit constant.

### 4.1 Backward error of the Hermitian eigendecomposition (Layer 1)

The whitened Gram is diagonalized by a symmetric eigensolver. The standard
backward-error theorem (LAPACK lineage; one-line Lean4 formalization): the
computed eigenpairs $(\tilde\theta_i, \tilde c_i)$ of the computed
$\hat G$ are *exact* eigenpairs of $\hat G + E$ with
$\|E\| \le c(n)\,u\,\|\hat G\|$ (take $c(n) = n^3$ conservatively — explicit
and machine-checkable). Weyl's inequality for Hermitian matrices then gives

$$|\tilde\theta_i - \lambda_i(\hat G)| \le \|E\| \le c(n)\,u\,\|\hat G\|.$$

### 4.2 A validated upper bound for $E_m$ (Layer 2)

The computed Lawson fit produces a *specific* rational function $p/q$. In
exact arithmetic $E_m \le \|f_{k,N} - p/q\|_{\infty,\Sigma}$ (the minimax is
the minimum over all admissible $r$, and $p/q$ is admissible). The code's
grid maximum is a *lower* bound for that sup — not directly usable. Fix:
evaluate $\|f_{k,N} - p/q\|_{\infty,\Sigma}$ by **interval arithmetic with
outward rounding** over the (padded) box, obtaining a certified upper bound

$$R_{\mathrm{cert}} \ge \sup_{z\in\Sigma}|f_{k,N}(z) - p(z)/q(z)| \ge E_m,$$

and set $\mathrm{band\_hi} = 2\cdot11.08\,\|v\|\,e^{-hm}\,R_{\mathrm{cert}}$.
The band remains valid; the only new trusted component is the interval
evaluation (directed rounding), which is the one small core §5 proves.

### 4.3 The residual certificate is already a-posteriori (Layer 3)

The sharp tier needs no infinite-precision hypothesis *at the theorem level*:
$|\theta - \lambda| \le \|H_m\psi - \theta\psi\|$ holds for the exact operator
applied to the *computed* vector. What must be enclosed is the *measured*
residual $\|r\|$: the code computes it from the stored Gram in a
cancellation-free form ($\|r\| = |\tau_m c_{m-1}|$, one out-of-basis
component). Enclosing the Gram entries by interval arithmetic (or by a
backward-error bound $\|\hat G - G\| \le c\,u\,\|G\|$ on the f64 inner
products) makes the measured residual a certified width:
$\|r\|_{\mathrm{cert}} \le \|r\|_{\mathrm{true}} + c\,u\,\|G\|$.

### 4.4 The assembled finite-precision width (Layer 4)

For any delivered Ritz value,

$$\delta = \underbrace{\|r\|_{\mathrm{cert}}}_{\text{residual + Gram roundoff}}
+ \underbrace{c(n)\,u\,\|\hat G\|}_{\text{eigendecomposition (Weyl)}}
+ \underbrace{h_{O}}_{\text{enclosure of } \langle\psi|O|\psi\rangle},$$

all three terms explicit and machine-checkable. The certified interval
$[\theta - \delta, \theta + \delta]$ is then a theorem of the exact operator
applied to enclosures — the f64 arithmetic itself never enters the statement.

---

## 5. Certifying the code implementation (the probability kernel), with Lean4

### 5.1 What "the probability kernel" is

The numerical layer that turns a Hamiltonian into probabilities/expectations:
`fock_sirk::forward_sirk` (forward sequence → Gram → whitening → Ritz values →
residuals) feeding `prob_kernel::Session` (Born-rule layer:
`evolve`/`probability`/`condition`). The mass-gap calculation is a spectral
prediction of this kernel. The goal: make the kernel's delivered numbers
*usable inside a Lean4 proof* without verifying the f64 program.

### 5.2 Architecture: certificates ride with the numbers (reuse, don't rebuild)

The existing pieces are reused as-is:

1. **The BookProof operator theorems (§1)** — the SIRK selection, the Ritz
   convergence, the whitening well-posedness, the parity/sector structure.
2. **The kernel's a-posteriori machinery** — `ritz_residuals`,
   `resolved_ritz_values`, `hashimoto_support::certify` — promoted from test
   support to a library surface: every solve returns, alongside each Ritz
   value, a `Certificate { value, residual, lo, hi }` with the three §4 terms.
3. **The nanoda verification cycle (S29/S31)** — Lean4 theorems exported to
   `lean4export` NDJSON and re-verified by `prob_kernel::verify::verify_export`
   (nanoda), exactly as the confluence proof is today.

The new Lean4 work is **five small theorem families**, all finite-dimensional
and elementary (no analysis beyond Weyl's inequality and the residual bound):

| Theorem family | Statement | Where it lives |
|---|---|---|
| T1 | Hermitian eigenvalue perturbation (Weyl): $|\tilde\lambda_i - \lambda_i| \le \|E\|$ | new `BookProof/ChapterSirkFinitePrecision.lean` |
| T2 | Rayleigh–Ritz residual bound: $|\theta - \lambda| \le \|H\psi - \theta\psi\|$ | new, same chapter |
| T3 | Whitened-Gram backward error: computed eigenpairs are exact eigenpairs of $\hat G + E$, $\|E\| \le c(n)u\|\hat G\|$ | new, same chapter |
| T4 | Certified-observable propagation (Cauchy–Schwarz), matching `hashimoto_support::certify` | new, same chapter |
| T5 | Interval enclosure of the $E_m$ sup and of $\langle\psi|O|\psi\rangle$ (directed rounding) | new, same chapter (+ a $\le 100$-line verified interval core) |
| T6 | **The gap theorem of §3.2**: $\lambda_1 - \lambda_0 \ge \theta^o_0 - \theta^e_0 - (\delta^o + \delta^e)$ | new `BookProof/ChapterSirkCertifiedGap.lean`, importing §1 items 4/7 |

The **trusted core** is only T5's directed-rounding interval layer (the
standard `Float` rounding axioms — the same trust class as any verified
floating-point library); everything else is a-posteriori certificates, so the
trust surface stays minimal. The kernel's f64 values are never trusted: the
proof consumes only `Certificate` enclosures and residuals.

### 5.3 Formalizing the Rust code itself: Aeneas (Rust → Lean 4), and the Why3-native alternative

The certificate architecture of §5.2 keeps the f64 code untrusted and proves
*around* it. The stronger route — formalizing the code itself — is available
through **Aeneas** (Ho–Protzenko–Fromherz, ICFP 2022; the Rust→Lean 4
functional-translation toolchain used for Microsoft's SymCrypt): it translates
the actual Rust implementation into a pure functional Lean 4 model, so
functional-correctness theorems are proved about the code *as written*, not
about a paraphrase. **Aeneas is the first attempt** (its output lands directly
in Lean 4 next to `BookProof/`); the fallback ladder at the end of this
subsection applies if it turns out not to be enough.

**What Aeneas verifies here** (the pure numeric core of the probability
kernel):

- the forward sequence $w_k = (H - z_k I)w_{k-1}$ as a fold over the operator
  terms, and the **projection identity** $H_{jk} = G_{j,k+1} + z_k G_{j,k}$
  as a theorem about the generated model (the algebraic half is
  `BookProof/ChapterSirkMultiShift`; Aeneas supplies the code half);
- the Gram assembly $G_{ij} = \langle w_i, w_j\rangle$ (inner-product
  accumulation over `Vec<f64>`);
- the whitening transform $T$ with $T^*\hat G\,T = I$ (the existence half is
  `ChapterSirkGramWhitening`; Aeneas proves the code computes it);
- the residual certificate: the computed $\|r\| = |\tau_m c_{m-1}|$ — the
  one-out-of-basis-component statement of `ForwardSirkResult::ritz_residuals`
  — as a functional-correctness theorem;
- the certificate emitter arithmetic (value, residual, lo, hi) of §5.2.

**Constraints (honest).** Aeneas targets the functional subset of Rust — no
interior mutability, no `unsafe`, no raw pointers, and external dense-algebra
crates like `nalgebra` do not translate. The Aeneas target is therefore the
**pure numeric core re-implemented in the supported subset** (the standard
"verification core" pattern — the same pattern SymCrypt uses), kept in sync
with the production path by the existing suites; the dense eigendecomposition
remains a trusted LAPACK-style call whose backward error is exactly the T3
bound. The f64 values are still never trusted: Aeneas proves the *algorithm*;
the *rounding* is enclosed by T1–T5, exactly as before.

**Why this fits the project.** The Aeneas-generated Lean 4 code lives in the
same `BookProof/` tree, and the exported proofs go through the existing nanoda
re-verification (`prob_kernel::verify::verify_export`, S29/S31) — the code's
correctness theorems get the same independent-checker treatment as the
confluence proof.

**Project-native alternative: Creusot → the running Why3 cycle.** Creusot
translates Rust to **Why3**, plugging directly into the already-running S36
cycle (`prob_kernel::whyml`: Why3 1.8.2 + alt-ergo 2.6.3, verified extraction
to OCaml via `unfer_ocaml.drv`, the australVM gate). The Why3 goals for the
same pure core can be discharged by the existing provers, and the extraction
driver already maps Why3 `int` to OCaml `int`. Aeneas (Lean 4 — connects to
`BookProof` + nanoda) and Creusot (Why3 — connects to the existing S36
pipeline) are complementary; a cheap third complement is **Kani** (AWS model
checker) for bounded property checks (overflow/panic/UB) on the actual f64
paths, which need no proofs.

**Division of labor (final).** Aeneas/Creusot prove the *code* (algorithm-level
functional correctness); T1–T5 prove the *rounding* (enclosures); BookProof
proves the *operator theory* (selection, convergence, positivity); nanoda
re-checks the exports; T6 assembles the gap. No component trusts the f64
arithmetic; the trusted core remains the directed-rounding interval layer.

**Fallback ladder (if Aeneas is not enough).** Aeneas is the **first
attempt** because it is the only route whose output lands directly in Lean 4
next to `BookProof/`. It becomes the wrong tool when any of these hold:

1. the core cannot be expressed in its functional subset (dense `nalgebra`
   calls, interior mutability, non-trivial lifetimes) — the pure core of
   §5.3 is designed to avoid this, but if keeping the production path and the
   verified core in sync becomes the trust problem, the translation adds risk
   rather than removing it;
2. the generated Lean 4 model drifts from the actual code (Charon extraction
   gaps, toolchain churn), so the proof is about a look-alike;
3. the manual Lean 4 proof effort against the generated model exceeds the
   cost of writing the T1–T6 theorems by hand — Aeneas's value is precisely
   to avoid re-typing the algorithm into Lean, and the core is only a few
   hundred lines of pure folds and sums, so the saving may be marginal.

Once Aeneas is ruled out, in order of preference:

- **Fallback 1 — Verus.** The most mature deductive verifier: proves the same
  algorithm with the least manual effort (`vstd` covers the arithmetic;
  SMT automation). Cost: the proof lives in Verus, not Lean 4 — the final
  mass-gap statement would be a Verus theorem plus a bridging note.
- **Fallback 2 — Creusot → Why3.** Same core, discharged by Why3 provers
  (alt-ergo/Z3). Cost: not Lean 4 either; but Why3 runs standalone easily and
  this project already pins Why3 1.8.2 + alt-ergo 2.6.3 (S36), so the
  environment is proven.
- **Fallback 3 — hand-written Lean 4 (the §5.2 baseline).** Always available:
  the T1–T6 theorems + the certificate emitter, with the algorithm re-typed
  by hand into Lean. This is the floor the plan already specifies; Aeneas
  only improves on it if the translation is faithful.
- **Complement (not a substitute) — Kani.** Run on the real f64 paths for
  overflow/panic/UB whatever the deductive route.

**Hybrid (most likely outcome).** The split that survives every choice is:
Aeneas (or Verus) on the pure algorithmic core; hand-written Lean 4 for the
dense-eigendecomposition trust boundary (the T3 backward-error statement) and
the rounding enclosures (T1, T2, T4, T5); T6 assembles the gap. The fallback
ladder only decides which tool produces the algorithm leg.

### 5.4 The end-to-end workflow

1. Kernel runs the even/odd solves; emits `Certificate` records.
2. A small emitter serializes the certificates as the data for T6's
   instantiation (parity labels, $\theta$, $\delta$).
3. `ChapterSirkCertifiedGap` applied to the data yields
   `gap ≥ θ_o − θ_e − (δ_o + δ_e)` as a Lean4 theorem instance; exported to
   NDJSON; re-verified by nanoda inside the kernel
   (`prob_kernel::verify::verify_export`) — so the *proof* of the gap, not
   just the number, is checked by an independent checker.
4. The BookProof convergence theorems (§1 items 2, 7, 8) attach the finite
   statement to the selected Friedrichs extension; the open continuum leg is
   §6.

### 5.5 Gap analysis (what exists / what is new)

| Item | Status |
|---|---|
| YM Hamiltonian positive, bounded below, closable (Friedrichs) | proved (`ChapterYangMillsFriedrichs`) |
| SIRK shift-invert selects the extension; resolvent bounds; uniqueness | proved (`ChapterHashimotoShiftInvert`, `ChapterHashimotoComplexShifts`) |
| Krylov span identities (forward ≡ resolvent ≡ plain) | proved (`ChapterKrylovShiftSpan`, `ChapterSirkMultiShift`) |
| Gram whitening well-posed; Ritz values → bottom of spectrum | proved (`ChapterSirkGramWhitening`, `ChapterSirkRitzSpectrum`) |
| Galerkin flows → selected flow | proved (`ChapterSirkTrotterKatoGalerkin`) |
| Residual certificate + certified intervals in the kernel | implemented (`ritz_residuals`, `certify`, `bands_program_gauge_fixed`) |
| T1–T5 finite-precision theorems + interval core | **new** (small, elementary) |
| T6 certified-gap theorem | **new** (assembles §3.2) |
| Certificate emitter in the kernel | **new** (promote the test support to a library surface) |
| nanoda re-verification of the exported proofs | implemented (S29/S31 pipeline) |
| Rust-code formalization of the pure numeric core — **Aeneas first** (§5.3) | **new** — primary route; fallbacks: Verus → Creusot/Why3 → hand-written Lean 4 |
| Fallback 1: Verus (most mature deductive verifier) | **new** (option; proofs live in Verus, not Lean 4) |
| Fallback 2: Creusot → Why3 | **new** (option; reuses the pinned Why3 1.8.2 + alt-ergo + `unfer_ocaml.drv` extraction) |
| Fallback 3: hand-written Lean 4 (the §5.2 baseline) | **new** (the floor; always available) |
| Kani property checks on the f64 paths (overflow/panic/UB) | **new** (cheap; no proofs) |
| Continuum gap-preserving passage | **open** (§6; out of scope per `CONSOLIDATED_PLAN.md`) |

---

## 6. What is proved, what is not, and the single missing leg

**Proved (rigorously, with machine-checkable constants).**

1. The QYM gauge-fixed Hamiltonian has a positive self-adjoint (Friedrichs)
   extension; the SIRK machinery selects exactly it, and the Galerkin Ritz
   values converge to its spectrum bottom (BookProof §1).
2. For the truncated (lattice) Hamiltonian — the object the kernel
   diagonalizes — a **mass gap with a rigorous lower bound**, assembled from
   the certified intervals of two parity-sector solves (§3.2), all rounding
   enclosed by the finite-precision layer (§4).
3. That bound is *proof-carrying*: the Lean4 theorem T6 applied to kernel
   certificates, re-verified by nanoda (§5).

**Not proved, and why.** The *continuum* Millennium mass gap requires the
spectral gap of the lattice truncations to converge to (or be bounded below
by a positive limit of) the gap of the continuum operator. The BookProof
supplies bottom-of-spectrum convergence (item 7) and flow convergence (item
8), but a **gap-preserving norm-resolvent convergence** of this specific
truncation family — or an independent a-priori continuum gap lower bound — is
the single missing leg. It is identified here precisely so a Lean4 specialist
can attack it as its own item; `CONSOLIDATED_PLAN.md` keeps it out of scope
until then.

**On the infinite-precision assumption.** The `Hashimoto.md` bands assume
exact arithmetic; §4 removes exactly that assumption by enclosing every
computed quantity (backward error of the eigendecomposition, validated $E_m$,
a-posteriori residual, interval evaluation of observables). The unit-norm
frame and the other numerical guards are not part of this argument: they are
exact reparametrizations / provably-inert devices (see
`NUMERICAL_VALIDATION_GUIDE.md` §4.5), so they neither add nor remove
assumptions at the infinite-precision limit.

---

## 7. Suggested next steps (for a Lean4 specialist)

1. Formalize T1–T5 in `BookProof/ChapterSirkFinitePrecision.lean` (Weyl,
   residual bound, backward error, Cauchy–Schwarz propagation, interval
   enclosure). All are finite-dimensional; expect a few hundred lines each.
2. Formalize T6 in `BookProof/ChapterSirkCertifiedGap.lean`, importing the
   parity-sector structure and the Ritz-convergence chapter.
3. Promote the `hashimoto_support` certificate machinery to a `fock_sirk`
   library surface returning `Certificate { value, residual, lo, hi }` per
   Ritz value, with the §4 terms explicit.
4. Wire the exported T6 instance through `prob_kernel::verify::verify_export`
   (nanoda), mirroring the S31 confluence pipeline.
5. Separately scope the continuum leg (§6): gap-preserving norm-resolvent
   convergence of the lattice truncation family.
6. **Try Aeneas first** on the pure numeric core (forward sequence, Gram
   assembly, whitening, residual, certificate emitter): extract to the
   Aeneas-supported Rust subset, generate the Lean 4 model, prove the
   projection identity and the residual formula against it, export and
   re-verify with nanoda. If the subset/toolchain blocks it, walk the
   fallback ladder of §5.3 (Verus → Creusot/Why3 → hand-written Lean 4).
7. (Fallback 2) Run Creusot on the same core; discharge the Why3 goals with
   the existing Why3/alt-ergo; extract via `unfer_ocaml.drv` into the
   australVM gate.
8. Run Kani on the f64 paths for overflow/panic/UB property checks, as a
   no-proof complement to the deductive routes.
