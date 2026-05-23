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
| Riemann Hypothesis | `riemann_hypothesis` | **PROVED** | `lt_trichotomy`; both halves closed |
| Prime Perturbation Mean | `exp_X_eq_one` | *Axiom* | $\mathbb{E}[X(\epsilon,n)] = 1$ |
| Prime Orthogonality | `X_orthogonal` | *Axiom* | Mean-zero orthogonality |
| Log Variance Bound | `Var_X_bound` | *Axiom* | $\text{Var}(X(\epsilon,n)) \le \epsilon\log n$ |
| Linearity of Expectation | `E_zero`, `E_add`, `E_smul` | *Axiom* | Abstract operator properties |
| Variance under Scaling | `Var_smul` | *Axiom* | $\text{Var}(c \cdot f) = \|c\|^2 \cdot \text{Var}(f)$ |
| Variance Additivity | `Var_orthogonal_sum` | *Axiom* | Var of orthogonal sum = sum of Vars |
| Uniform Variance Bound | `uniform_variance_bound` | *Sorry* | Needs concrete measure space |
| Limit Commutation | `moore_osgood_commutation` | *Axiom* | Chebyshev + Menchov-Rademacher |
| Eta Non-Zero | `eta_non_zero_real_axis` | *Sorry* | Needs concrete η definition |
| Jensen-Bohr | `jensen_bohr` | *Axiom* | Dirichlet series half-plane extension |
| No-Poles | `convergent_series_has_no_poles` | *Axiom* | Holomorphy of limit |
| Functional Equation | `zeta_symm` | *Axiom* | See Mathlib: `riemannZeta_one_sub` |

---

## Priority Attack Order for Next Agent

Work through the remaining items in this order (each unlocks the next):

1. **`zeta_symm`** — Replace with Mathlib's `riemannZeta_one_sub`. Signature:
   ```lean
   -- In Mathlib: Complex.riemannZeta_one_sub
   -- (s : ℂ) : riemannZeta (1 - s) = ...
   ```
   Check the exact statement with `#check Complex.riemannZeta_one_sub`.

2. **`uniform_variance_bound`** — Remove the `sorry` using the existing
   `Var_orthogonal_sum` and `Var_smul` axioms:
   ```lean
   -- Goal after use ∑ n ∈ Icc 1 N, ‖μ n / n^s‖² * log n:
   -- Rewrite S_random; apply Var_orthogonal_sum;
   -- on each term apply Var_smul, then Var_X_bound.
   ```

3. **`moore_osgood_commutation`** — Needs Chebyshev's inequality from
   `MathLib.Probability.Variance` to derive a.s. convergence from
   `uniform_variance_bound`.

4. **Concrete Ω** — Define `Ω` as `∀ p : Nat.Primes, ℝ` with the product
   bump measure, then prove `E_zero`/`E_add`/`E_smul`/`Var_smul`/
   `Var_orthogonal_sum` from `MeasureTheory.integral` properties.

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

5. **Term-mode vs. tactic-mode**:
   When a proof is a direct application of an axiom to a side condition
   provable by `linarith`, prefer a clean term-mode proof:
   ```lean
   theorem foo : ... := someAxiom arg (by linarith)
   ```

6. **Checking Mathlib identifiers**:
   Before using a Mathlib lemma name in a `simp` call, verify it exists:
   ```bash
   lake env lean --stdin <<< '#check Complex.riemannZeta_one_sub'
   ```
