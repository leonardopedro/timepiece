# AGENTS.md - Developer Guide for AI Coding Agents

Welcome, Agent. This document contains critical context, guidelines, and commands to help you navigate and contribute to the Riemann Hypothesis probabilistic formalization project.

---

## Workspace Layout & File Map

- **`/PLAN.md`**: Tracks implemented theorems vs. remaining axioms/loopholes. **Read this first** to identify the next development target.
- **`/RiemannProof/`**: The Lean 4 project root.
- **`/RiemannProof/RiemannProof/Basic.lean`**: The main development file. All definitions, axioms, lemmas, and theorems reside here.
- **`/RiemannProof/RiemannProof.lean`**: Entry point exposing the library.

---

## Build and Verification Commands

Lean 4 relies on the `lake` build system. Because the Lean version manager (`elan`) is installed locally under `~/.elan/`, you must prepend it to the `PATH`.

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

Use this checklist to understand what is postulated (via `axiom`) and what is proven (via `lemma` or `theorem` without `sorry`):

| Target | Lean 4 Identifier | Status | Notes |
| :--- | :--- | :---: | :--- |
| Finite Sum Linearity | `E_sum` | **PROVED** | Proved using `classical` and `Finset.induction_on` |
| Expectation Equivalence | `expected_S_random_eq_S_classical` | **PROVED** | Unfolds sums and uses linearity axioms |
| RH Zero-Free Strip | `riemann_hypothesis` | **PROVED** | Proved for $Re(s) > 1/2$; symmetric case is `sorry`'d |
| Prime Perturbation Mean | `exp_X_eq_one` | *Axiom* | Postulates $\mathbb{E}[X(\epsilon, n)] = 1$ |
| Prime Orthogonality | `X_orthogonal` | *Axiom* | Postulates orthogonality of error modes |
| Log Variance Bound | `Var_X_bound` | *Axiom* | Postulates $Var(X(\epsilon, n)) \le \epsilon \log(n)$ |
| Linearity of Expectation | `E_zero`, `E_add`, `E_smul` | *Axiom* | Abstract expectation operator properties |
| Uniform Variance Bound | `uniform_variance_bound` | *Sorry* | uniform variance bound $Var(S_{N,\epsilon}) \le \epsilon M$ |
| Limit Commutation | `moore_osgood_commutation` | *Axiom* | Limit commutation via uniform variance bounds |
| Analytical Continuations | `eta_non_zero_real_axis`, `jensen_bohr`, `convergent_series_has_no_poles` | *Axiom* / *Sorry* | Standard boundary and pole properties |

---

## Strategic Guidelines for Future Edits

1. **Unfolding Let-Bindings before `linarith`**:
   Lean 4's linear arithmetic tactic (`linarith`) does not automatically look through let-bound variables (e.g. `set β := s.re - 1 / 2`). You must explicitly unfold or simplify them using `dsimp only [β, α]` before calling `linarith`.
   *Example*:
   ```lean
   have hs_gt_s0 : s.re > s_0.re := by
     rw [hs0_re]
     dsimp only [α, β]
     linarith
   ```

2. **Scoped Namespace Imports**:
   To use the Möbius function notation `μ`, you must open the scoped Moebius namespace:
   ```lean
   open scoped ArithmeticFunction.Moebius
   ```
   For the limit notation `𝓝`, open `Topology`:
   ```lean
   open Topology
   ```

3. **Style and Line Limits**:
   The mathlib style guidelines require that lines do not exceed 100 characters. Break long lines of code and type signatures appropriately. Do not leave trailing whitespaces or add unnecessary empty line breaks.

4. **Sectioning and Variable Scope**:
   Keep variables related to the probability space (`Ω`, `E`, `Var`, `X`) scoped inside `section ProbabilisticRegularization ... end ProbabilisticRegularization`. This prevents the linter from warning about unused section variables in downstream deterministic theorems like `riemann_hypothesis`.

5. **Resolving the Measure Space**:
   To resolve the expectation/variance axioms, you must construct a concrete probability space $\Omega$ and define $E$ and $Var$ using Mathlib's Bochner integral (`MeasureTheory.integral`). You will then prove the expectation linearity axioms directly from integration properties.
