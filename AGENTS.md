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
| Uniform Variance Bound | `uniform_variance_bound` | **PROVED** | `Var_orthogonal_sum` → `Var_smul` → `Var_X_bound`; explicit `E` parameter |
| Convergence at s₀ | `classical_series_converges_at_s0` | **PROVED** | Term-mode via `moore_osgood_commutation` |
| RH Zero-Free Strip (right) | `zeta_no_zeros_right_half_plane` | **PROVED** | Contradiction; `dsimp`+`linarith` |
| Riemann Zeta Symmetry | `zeta_symm` | **PROVED** | Uses Mathlib `riemannZeta_one_sub` |
| Riemann Hypothesis | `riemann_hypothesis` | **PROVED** | `lt_trichotomy`; both halves closed |
| Prime Perturbation Mean | `exp_X_eq_one` | *Axiom* | E[X(ε,n)] = 1 |
| Prime Orthogonality | `X_orthogonal` | *Axiom* | Mean-zero orthogonality |
| Log Variance Bound | `Var_X_bound` | *Axiom* | Var(X(ε,n)) ≤ ε·log n |
| Linearity of Expectation | `E_zero`, `E_add`, `E_smul` | *Axiom* | Abstract operator properties |
| Variance under Scaling | `Var_smul` | *Axiom* | Var(c·f) = ‖c‖²·Var(f) |
| Variance Additivity | `Var_orthogonal_sum` | *Axiom* | Var of orthogonal sum = sum of Vars |
| Limit Commutation | `moore_osgood_commutation` | *Axiom* | Chebyshev + Menchov-Rademacher |
| Eta Non-Zero | `eta_non_zero_real_axis` | *Sorry* | Needs concrete η definition |
| Jensen-Bohr | `jensen_bohr` | *Axiom* | Dirichlet series half-plane extension |
| No-Poles | `convergent_series_has_no_poles` | *Axiom* | Holomorphy of limit |

---

## Priority Attack Order for Next Agent

Work through the remaining items in this order (each unlocks the next):

1. **Construct concrete Ω_N** — This is the master unlock. Define `Ω N` as
   `∀ p : {p : ℕ // p.Prime ∧ p ≤ N}, ℝ` with the product ε-bump measure.
   Then prove `E_zero`/`E_add`/`E_smul`/`exp_X_eq_one`/`X_orthogonal`/
   `Var_X_bound`/`Var_smul`/`Var_orthogonal_sum` from
   `MeasureTheory.integral` properties.
   ```lean
   -- Sketch:
   noncomputable def Ω (N : ℕ) := ∀ p : {p : ℕ // p.Prime ∧ p ≤ N}, ℝ
   -- Then equip with MeasureSpace using MeasureTheory.Measure.pi
   ```

2. **`moore_osgood_commutation`** — Use `uniform_variance_bound` together with
   Chebyshev's inequality from `MathLib.Probability.Variance` to derive a.s.
   convergence of `S_random` as N → ∞ for Re(s) > 1/2, then pass to the
   deterministic limit `S_classical`.

3. **`eta_non_zero_real_axis`** — Remove the `sorry`. Either:
   - Connect to Mathlib's `riemannZeta` material via the relation
     `η(s) = (1 - 2^(1-s)) * ζ(s)` and the known non-vanishing of `(1 - 2^(1-s))`
     on the real axis, or
   - Provide a direct Dirichlet-series absolute-convergence argument for real s > 1/2.

4. **`jensen_bohr`** — Formalize the Bohr–Cahen theorem: convergence of a
   Dirichlet series at s₀ implies holomorphic continuation to Re(s) > Re(s₀).
   Use `DifferentiableOn` + Cauchy integrals from Mathlib.

5. **`convergent_series_has_no_poles`** — Prove holomorphicity of the limit
   function in the half-plane of convergence.

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
