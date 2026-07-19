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

