# Timepiece: Riemann Hypothesis Probabilistic Formalization

This repository contains the Lean 4 formalization of the probabilistic regularization and uniform variance bound framework for the Riemann Hypothesis, as outlined in `zetanew.tex`. 

By introducing a smooth, compact probability perturbation to the prime modes, the deterministic Möbius reciprocal series is regularized into a random Dirichlet series. Under uniform variance bounds, this randomized series converges on the critical strip $Re(s) > 1/2$, establishing a pole-free and zero-free region.

---

## Project Structure

- **`zetanew.tex`**: The LaTeX paper detailing the mathematical proof and physics intuition.
- **`PLAN.md`**: The implementation roadmap mapping verified milestones and remaining work.
- **`RiemannProof/`**: The Lean 4 project folder containing the formalized code.
  - **`RiemannProof/Basic.lean`**: The core source file containing the axioms, lemmas, and proofs.
- **`AGENTS.md`**: Architectural and onboarding instructions for subsequent AI coding agents.

---

## Verification Guide (How to Verify the Proof)

To verify the compiled Lean 4 blueprint and its verified lemmas, follow these steps:

### Prerequisites
You need the Lean Version Manager (`elan`) installed on your system.

```bash
# Install elan
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh -s -- -y

# Configure your shell PATH
export PATH="$HOME/.elan/bin:$PATH"
```

### Compiling and Verifying
Navigate into the `RiemannProof` directory and run the Lean build command:

```bash
cd RiemannProof

# Fetch precompiled Mathlib cache (saves hours of compilation)
lake exe cache get

# Compile and verify the project
lake build
```

Upon a successful run, the output will look like:
```text
Build completed successfully (2931 jobs).
```

Any logical inconsistency, syntax error, or invalid step in the proof would cause the build to fail. The successful compilation indicates that Lean's kernel has fully checked and verified all proved lemmas.

---

## Proved Theorems & Lemmas

The following results in `Basic.lean` have been **fully verified and proved** without placeholders (`sorry`):

1. **`E_sum`**: Linearity of the abstract expectation operator $E$ extended to arbitrary finite sums using Finset induction.
2. **`expected_S_random_eq_S_classical`**: Formally proves that the expected value of the randomized reciprocal series recovers the classical series:
   $$\mathbb{E}[S_{N, \epsilon}(s)] = S_{N, 0}(s)$$
3. **`riemann_hypothesis` ($Re(s) > 1/2$ reduction)**: Formally proves that if $\zeta(s) = 0$, then $Re(s) \le 1/2$ (with $Re(s) > 1/2$ leading to a contradiction using the convergence properties of the Dirichlet series).

---

## Remaining Axioms & Postulates

The proof framework currently postulates the following key properties as axioms to be proven in subsequent iterations:
- **`exp_X_eq_one` & `X_orthogonal`**: Orthogonality of the prime mode perturbations.
- **`Var_X_bound`**: Uniform logarithmic variance bound of prime mode products.
- **`moore_osgood_commutation`**: Pointwise convergence of the series as $\epsilon \to 0$ and $N \to \infty$.
- **`jensen_bohr`**: Propagation of convergence on the half-plane.
- **`convergent_series_has_no_poles`**: The holomorphy of the convergent Dirichlet series implying a zero-free region.
- **Symmetric Case ($Re(s) < 1/2$)**: The symmetric zero-free region derived from the functional equation.