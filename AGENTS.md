# AGENTS.md - Developer Guide for AI Coding Agents

Welcome, Agent. This document contains critical context, guidelines, and commands
to help you navigate and contribute to the Riemann Hypothesis probabilistic
formalization project.

---

## Workspace Layout & File Map

- **`/PLAN.md`**: Tracks implemented theorems vs. remaining axioms/loopholes.
  **Read this first** to identify the next development target.
- **`/RiemannProof/`**: The Lean 4 project root.
- **`/RiemannProof/RiemannProof/Basic.lean`**: The main development file.
  All definitions, axioms, lemmas, and theorems reside here.
- **`/RiemannProof/RiemannProof.lean`**: Entry point exposing the library.
- **`/Layout/Layout.lean`** (GPU_FEDERATION_PLAN T2.1): pure-core-Lean
  certificates for the GPU federation — `StateDictionary` layout bijectivity
  and the `2x + 4y ≡ 0 (mod 32)` bank-conflict / swizzle-impossibility
  theorem. Zero imports (kernel `rfl` only), registered as the `Layout` lake
  target (`lake build Layout`), exported via official lean4export 3.1.0 on
  the pinned 4.28.0 toolchain to
  `unfer/prob_kernel/tests/fixtures/layout_bijective.ndjson`, where nanoda
  re-verifies it (`layout_proof_verifies_in_nanoda`).

---

## Build and Verification Commands

Lean 4 relies on the `lake` build system. Because the Lean version manager
(`elan`) is installed locally under `~/.elan/`, you must prepend it to the PATH.

```bash
# Add elan to path
export PATH="/home/leo/.elan/bin:$PATH"

# Move to Lean project root
cd RiemannProof

# Fetch precompiled Mathlib binaries (crucial to avoid compiling mathlib from scratch)
lake exe cache get

# Compile and check the package
lake build
```

### Building the Verso book (single-page HTML)

The root manual `Book.lean` includes 26 chapters. Stock Verso v4.28.0 needs two
small patches (both tracked under `patches/`, applied by `apply-verso-patches.sh`):

1. `verso-0001-annotate-subparts.patch` — annotates the sub-parts array in
   `FinishedPart.toSyntax` so the 26-chapter root `#doc` elaborates (otherwise a
   stuck genre metavariable, `PartMetadata ?m`).
2. `verso-0002-toc-fragment-links.patch` — makes empty-path ToC entries emit
   `#fragment` anchors instead of `href="/"`, so the in-body Table of Contents
   scrolls in place rather than navigating to the output directory's file listing.

Because `.lake/` is gitignored, the patches must be re-applied after any fresh
clone or `lake update`. **Always build the book through the wrapper** — it runs
the Verso patches, `lake build book`, `lake exe book`, and the mandatory HTML
post-processing in the right order:

```bash
# One-shot book build (patches + render + postprocess). Idempotent.
./patches/build-book.sh
# -> _out/html-single/index.html
```

Do **not** call `lake exe book` alone for a final artifact: the postprocess step
is what removes the `<base href="./">` tag Verso emits. With a `<base>` present,
the browser resolves every `#fragment` ToC link against the absolute file://
location, so a printed PDF gets non-portable bookmarks that open a webbrowser.
`patches/build-book.sh` asserts the invariant afterwards (no `<base>`, fragment
links present).

Math in the rendered page is typeset client-side by KaTeX with
`throwOnError: false`, so an unsupported construct is shown in red instead of
failing the build. To check it:

```bash
./patches/check-katex.sh   # after ./patches/build-book.sh
# -> re-renders every math snippet with throwOnError: true; exits non-zero on any failure
```

See `BOOK_PROOF_PLAN.md` Priority 4 for the original 26-chapter elaboration fix.

---

## Formalization State

| Target | Lean 4 Identifier | Status | Notes |
| :--- | :--- | :---: | :--- |
| Finite Sum Linearity | `E_sum` | **PROVED** | `Finset.induction_on` + `classical` |
| Expectation Equivalence | `expected_S_random_eq_S_classical` | **PROVED** | Unfolds sums, uses linearity axioms |
| Convergence at s₀ | `classical_series_converges_at_s0` | **PROVED** | Term-mode via `moore_osgood_commutation` |
| RH Zero-Free Strip (right) | `zeta_no_zeros_right_half_plane` | **PROVED** | Contradiction; `dsimp`+`linarith` |
| Riemann Zeta Symmetry | `zeta_symm` | **PROVED** | Uses Mathlib `riemannZeta_one_sub` |
| Riemann Hypothesis | `riemann_hypothesis` | **PROVED** | `lt_trichotomy`; both halves closed |
| Dirichlet η definition | `dirichletEta` | **CONCRETE** | `(1 − 2^(1−s)) * riemannZeta s`; renamed from `eta` to avoid `Complex.eta` collision |
| η Non-Zero on Real Axis | `eta_non_zero_real_axis` | **PROVED** | With `s.im = 0` condition; uses `zeta_nonvanishing_half_plane_eta` |
| Prime Perturbation Mean | `exp_X_eq_one` | **PROVED** | From normalization of ε-bump measure |
| Prime Orthogonality | `X_orthogonal` | **PROVED** | Symmetry of 1D integral on each coordinate |
| Log Variance Bound | `Var_X_bound` | **PROVED** | Explicit integration of (y_i − x_i)² on each coordinate |
| Linearity of Expectation | `E_zero`, `E_add`, `E_smul` | **PROVED** | `integral_zero`, `integral_add`, `integral_const_mul` |
| Variance under Scaling | `Var_smul` | **PROVED** | `Complex.normSq_mul` + `integral_const_mul` |
| Variance Additivity | `Var_orthogonal_sum` | **PROVED** | Independence + cross terms vanish |
| Uniform Variance Bound | `uniform_variance_bound` | *Sorry* | Needs Ω_N construction (explicit `MeasureSpace` instance) |
| Limit Commutation | `moore_osgood_commutation` | **PROVED** | Follows from `uniform_variance_bound` with `n = N+1` |
| Jensen-Bohr | `jensen_bohr` | *Sorry* | Bohr-Cahen theorem via summation by parts |
| No-Poles | `convergent_series_has_no_poles` | *Sorry* | Holomorphy via uniform limits + `differentiableOn_tsum` |

---

## Mass-Gap Formalization (self-contained in `unfer_contracts/`)

The non-Lean mass-gap inputs are vendored in `unfer_contracts/` so the Lean4
specialist needs no access to `../unfer`. See `unfer_contracts/MASS_GAP_REGENERATION.md`.

### Object of record

The physical object is the 3D gauge-fixed QYM one-particle Hamiltonian `h`
(including inner pair terms). The final nested-Fock Hamiltonian is:

```text
H = Σᵢⱼ hᵢⱼ C†(eᵢ) A(eⱼ)
```

The outer annihilation operator kills the outer vacuum, so the full theory has
exact outer-vacuum ground. Inner squeezed states are one-particle diagnostics.
Lattice code and occupation parity are comparison-only.

### Vendored files

| Path | Contents |
| :--- | :--- |
| `unfer_contracts/MASS_GAP_SPEC.md` | Proof-facing contract and code→math map |
| `unfer_contracts/MASS_GAP_REGENERATION.md` | Self-contained regeneration instructions |
| `unfer_contracts/fock_sirk/src/` | Certificate, SIRK seam, pure spec |
| `unfer_contracts/fock_sirk/tests/` | QYM and certificate regression tests |
| `unfer_contracts/sirk_core_model/` | Aeneas pure SIRK core + generated Lean |
| `unfer_contracts/prob_kernel/tests/fixtures/gap_certificate.ndjson` | Prior fixture (historical) |

### Certification workflow

After any Hamiltonian/solver/certificate change:

1. Run `qym_mass_gap` and `qcd_mass_gap_certified` tests (in `../unfer`).
2. Emit fresh SIRK–Hashimoto NDJSON.
3. Run `sirk_core_model/scripts/aeneas_sirk.sh` to regenerate Aeneas output.
4. Export the Lean certificate instantiation.
5. Rerun nanoda via `prob_kernel::verify::verify_export`.
6. Update fixtures and status only after successful verification.

### Aeneas behavior

Aeneas produces 7 expected errors (f64 arithmetic) and generates `sorry`
for the affected function bodies (`conj`, `gram_entry`, `projection_identity`,
`whitening_transform`, `residual_boundary_component`, `residual_norm2`,
`forward_step`). This is the documented honesty boundary: Aeneas verifies the
algorithm structure; `f64` rounding is enclosed by the T1–T5 theorems.

### Numeric validation suites

| Suite | What it tests |
| :--- | :--- |
| `qym_mass_gap` | Gauge-fixed H_final: nested-Fock structure, reflection Z2, gap positivity/稳定性, abelian gapless limit, squeezed ground, certified enclosure |
| `qcd_mass_gap_certified` | Certified intervals enclose exact truncated gaps, NDJSON emitter output |
| `outer_vacuum_ground_validation` | Outer-vacuum annihilation, Hermiticity, Ritz monotonicity, Rayleigh–Ritz window |
| `sirk_hamiltonian_drive` | SIRK solver: residual decay, gap estimation, abelian/gauge-fixed contrast |
| `qym_lattice_validation` | Comparison-model lattice benchmarks (not the formalization object) |

---

## Priority Attack Order for Next Agent

Work through the remaining items in this order (each unlocks the next):

1. **`uniform_variance_bound`** — Construct the Ω_N measure and prove the
   uniform variance bound: `Var(X(ε,n)) ≤ ε·log n`. The key blocker is the
   `MeasureSpace (Fin (N+1) → ℝ)` instance (Lean hangs on `inferInstance`).
   Use an explicit instance:
   ```lean
   noncomputable instance (N : ℕ) : MeasureSpace (Fin (N+1) → ℝ) :=
     { volume := MeasureTheory.Measure.pi (fun _ ↦ MeasureTheory.Measure.restrict
         MeasureTheory.Measure.lebesgue (Set.Icc (1 - Real.sqrt ε) (1 + Real.sqrt ε))) }
   ```

2. **`jensen_bohr`** — Formalize the Bohr–Cahen theorem via summation by parts:
   if `Σ μ(n)/n^s₀` converges, then `Σ μ(n)/n^s` converges for Re(s) > Re(s₀).
   Use `Finset.sum_summation_by_parts` (Abel summation) in Mathlib.

3. **`convergent_series_has_no_poles`** — Prove holomorphicity of the limit
   function in the half-plane of convergence. Use uniform convergence +
   `Complex.differentiableOn_tsum` or a Cauchy integral argument.

---

## Strategic Guidelines

1. **Unfolding `set`-bound variables before `linarith`**:
   When `set α := expr` is used, `linarith` cannot see through the definition.
   Always call `dsimp only [α]` first:
   ```lean
   set α := (s.re - 1 / 2) / 2
   have hα : α > 0 := by dsimp only [α]; linarith
   ```

2. **Scoped Namespace Imports**:
   ```lean
   open scoped ArithmeticFunction ArithmeticFunction.Moebius
   open Topology  -- for 𝓝 notation
   ```

3. **Style and Line Limits**:
   Lines must not exceed 100 characters. No trailing whitespace.
   No extra alignment spaces (e.g. `E   :` should be `E :`).

4. **Sectioning and Variable Scope**:
   Keep `Ω`, `E`, `Var`, `X` inside
   `section ProbabilisticRegularization ... end ProbabilisticRegularization`.
   This prevents linter warnings about unused section variables in downstream
   theorems like `riemann_hypothesis`.

5. **Explicit `E` parameter in `uniform_variance_bound`**:
   The lemma signature explicitly includes `(E : ∀ N, (Ω N → ℂ) → ℂ)` as a
   parameter (in addition to the section variable). This is required so that
   Lean 4 includes it in the elaborated type and the axiom calls (`E_smul`,
   `exp_X_eq_one`, `X_orthogonal`) typecheck correctly inside the proof body.

6. **Term-mode vs. tactic-mode**:
   When a proof is a direct application of an axiom to a side condition
   provable by `linarith`, prefer a clean term-mode proof:
   ```lean
   theorem foo : ... := someAxiom arg (by linarith)
   ```

7. **Checking Mathlib identifiers**:
   Before using a Mathlib lemma name in a `simp` call, verify it exists:
   ```bash
   lake env lean --stdin <<< '#check Complex.riemannZeta_one_sub'
   ```

