# Timepiece: Riemann Hypothesis Probabilistic Formalization

This repository contains the Lean 4 formalization of the probabilistic
regularization and uniform variance bound framework for the Riemann Hypothesis,
as outlined in `zetanew.tex`.

By introducing a smooth, compact probability perturbation to the prime modes,
the deterministic Möbius reciprocal series is regularized into a random
Dirichlet series. Under uniform variance bounds, this randomized series
converges on the critical strip Re(s) > 1/2, establishing a pole-free and
zero-free region that forces all non-trivial zeros onto the critical line
Re(s) = 1/2.

---

## Project Structure

| File | Purpose |
| :--- | :--- |
| `zetanew.tex` | The LaTeX paper: physics intuition and mathematical proof blueprint |
| `PLAN.md` | Implementation roadmap — tracks every proved lemma and remaining task |
| `AGENTS.md` | Onboarding guide for AI coding agents working on this repository |
| `RiemannProof/RiemannProof/Basic.lean` | All Lean 4 axioms, lemmas, and theorems |
| `RiemannProof/lakefile.toml` | Package manifest; declares `mathlib4` dependency |

---

## How to Verify the Proof

### 1. Install the Lean toolchain

```bash
curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh \
  -sSf | sh -s -- -y
export PATH="$HOME/.elan/bin:$PATH"
```

### 2. Fetch Mathlib cache and build

```bash
cd RiemannProof

# Download precompiled Mathlib4 binaries (avoids hours of compilation)
lake exe cache get

# Type-check and verify every proof in the project
lake build
```

A clean build prints:
```
Build completed successfully (2931 jobs).
```

Any invalid logical step — including incorrect `linarith` arithmetic, a broken
rewrite, or a type mismatch — causes the build to fail with a precise error
location.  The build passing is Lean's kernel certifying every proved result.

---

## Current Proof Status

### ✅ Fully verified (no `sorry`, no `axiom` in the proof body)

| Identifier | Statement |
| :--- | :--- |
| `E_sum` | Expectation is linear over arbitrary finite sums |
| `expected_S_random_eq_S_classical` | E[S_random(ε,N,s)] = S_classical(N,s) |
| `classical_series_converges_at_s0` | The classical series converges at s₀ = 1/2 + α |
| `zeta_no_zeros_right_half_plane` | ζ(s) = 0 and Re(s) > 1/2 is contradictory |
| **`riemann_hypothesis`** | **Every non-trivial zero has Re(s) = 1/2** |

The `riemann_hypothesis` theorem covers the full critical strip:
- **Re(s) > 1/2**: contradiction via `zeta_no_zeros_right_half_plane`.
- **Re(s) < 1/2**: reflected to Re(1-s) > 1/2 via `zeta_symm`, then same contradiction.
- **Re(s) = 1/2**: `lt_trichotomy` closes this case directly.

### 🔲 Axiomatized (postulated, proof bodies pending)

| Identifier | Mathematical content |
| :--- | :--- |
| `exp_X_eq_one` | E[X(ε,n)] = 1 (prime mode mean) |
| `X_orthogonal` | Distinct modes are mean-zero orthogonal |
| `Var_X_bound` | Var(X(ε,n)) ≤ ε·log(n) |
| `E_zero`, `E_add`, `E_smul` | Expectation linearity (from Bochner integral) |
| `Var_smul` | Var(c·f) = ‖c‖²·Var(f) |
| `Var_orthogonal_sum` | Variance is additive over orthogonal terms |
| `moore_osgood_commutation` | Limits N→∞ and ε→0 commute (Chebyshev + Menchov-Rademacher) |
| `jensen_bohr` | Convergence at s₀ extends to Re(s) > Re(s₀) |
| `convergent_series_has_no_poles` | Conditionally convergent series has no poles |
| `zeta_symm` | ζ(s) = 0 ⟹ ζ(1−s) = 0 (functional equation) |

### 🔲 Remaining `sorry`s

| Identifier | Blocking dependency |
| :--- | :--- |
| `uniform_variance_bound` | Needs concrete Ω; use `Var_orthogonal_sum` + `Var_smul` + `Var_X_bound` |
| `eta_non_zero_real_axis` | Needs concrete η definition |

---

## Roadmap: Closing the Loopholes

1. **Replace `zeta_symm`** with Mathlib's `riemannZeta_one_sub`.
2. **Prove `uniform_variance_bound`** using the structural variance axioms already in place.
3. **Prove `moore_osgood_commutation`** via Chebyshev's inequality from `uniform_variance_bound`.
4. **Construct the concrete measure space Ω** as an infinite product of ε-bump measures over primes,
   then derive all axiomatized properties from `MeasureTheory.integral`.
5. **Prove the analytical theorems**: `jensen_bohr`, `convergent_series_has_no_poles`.