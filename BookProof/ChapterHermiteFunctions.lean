import BookProof.ChapterHermiteFunctions.Part1
import BookProof.ChapterHermiteFunctions.Part2

/-!
# The Hermite functions: orthonormality, completeness, and the Hermite core of `L²(ℝ)`

This chapter supplies the concrete object that the abstract Galerkin/Friedrichs
chapter (`BookProof/ChapterHermiteGalerkinFriedrichs.lean`) and the quantum
gravity chapter (`BookProof/ChapterQuantumGravityDensitized.lean`) so far only
used *abstractly*: a genuine **Hilbert basis of Hermite functions** of `L²(ℝ)`,
and hence a genuine **Hermite core** — the space of finite linear combinations of
Hermite functions, i.e. "polynomials times the Gaussian".

The convention is the probabilists' one: `H_{n+1} = X H_n − H_n'`
(`Polynomial.hermite` of Mathlib), and the Hermite *functions* are

  `ψ_n(x) = H_n(x) e^{-x²/4}`,   `∫ ψ_m ψ_n = δ_{mn} n! √(2π)`.

Contents:

* `hermiteR`, `derivative_hermiteR`, `hermiteR_ode` — the polynomials, the
  derivative rule `H_{n+1}' = (n+1) H_n` and the Hermite differential equation;
* `gint_ibp` — integration by parts against the Gaussian weight on all of `ℝ`;
* `hermiteInner_eq` — the orthogonality relations
  `∫ H_m H_n e^{-x²/2} = δ_{mn} n! √(2π)`;
* `orthonormal_hermiteLp` — the normalized Hermite functions are orthonormal in
  `L²(ℝ, ℂ)`;
* `hermiteLp_span_dense`, `hermiteBasis` — completeness: they form a Hilbert
  basis (proved from scratch: orthogonality to all `xⁿ e^{-x²/4}` forces the
  Fourier transform of `e^{-x²/4} u` to vanish identically);
* `hermiteFun_oscillator` — each Hermite function is an eigenfunction of the
  harmonic oscillator `-d²/dx² + x²/4` with eigenvalue `n + 1/2`.
-/
