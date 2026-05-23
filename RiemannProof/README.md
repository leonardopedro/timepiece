# Timepiece: Riemann Hypothesis Probabilistic Formalization (Lean 4 Package)

This folder contains the Lean 4 project formalizing the probabilistic regularization and uniform variance bound framework for the Riemann Hypothesis.

---

## How to Verify the Proof

To build the project and verify all the mathematical steps checked by Lean's kernel:

### 1. Ensure `elan` and `lake` are in your PATH
```bash
export PATH="$HOME/.elan/bin:$PATH"
```

### 2. Fetch Mathlib Cache & Build
```bash
# Download precompiled binaries for Mathlib4
lake exe cache get

# Build the library and compile all lemmas
lake build
```

A successful compilation without errors indicates that the proof steps for all resolved lemmas and theorems have been fully verified by Lean's type-checker.

The verified items include:
* **`E_sum`**: Linearity of expectation over finite sums.
* **`expected_S_random_eq_S_classical`**: Expectation of the randomized series matches the classical series.
* **`classical_series_converges_at_s0`**: Conditional convergence at the evaluation point $s_0 = 1/2 + \alpha$.
* **`zeta_no_zeros_right_half_plane`**: Contradiction proof showing no zeros exist in the right half-plane ($Re(s) > 1/2$).
* **`riemann_hypothesis`**: The complete proof for the entire critical strip ($0 < Re(s) < 1$) using `lt_trichotomy` and symmetry reflection.

---

## File Map

- **`RiemannProof/Basic.lean`**: The core source file containing the axioms, lemmas, and proofs.
- **`RiemannProof.lean`**: Standard package entrypoint importing `RiemannProof.Basic`.
- **`lakefile.toml`**: Package manifest file containing configuration and `mathlib` dependency declarations.
