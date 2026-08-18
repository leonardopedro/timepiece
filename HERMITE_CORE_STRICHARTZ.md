# The Hermite core of `L²(ℝ)` and a Strichartz-type theorem on it

Two new chapters, both fully proved (no `sorry`, only the standard axioms
`propext`, `Classical.choice`, `Quot.sound`):

* `BookProof/ChapterHermiteFunctions.lean` — the Hermite functions themselves;
* `BookProof/ChapterStrichartzHermiteQG.lean` — the Hermite core, diagonal
  operators on it, and the 3D gauge-fixed quantum-gravity Hamiltonian.

Both are imported from `BookProof.lean`, and the whole library builds.

## 1. `ChapterHermiteFunctions` — the Hermite orthonormal basis

Working with the probabilists' Hermite polynomials `Hₙ` (`hermiteR n`, the
`ℝ`-coefficient image of Mathlib's `Polynomial.hermite`) and the Gaussians
`gaussW x = e^{-x²/2}`, `gaussH x = e^{-x²/4}`:

* `derivative_hermiteR`, `hermiteR_ode` — `H'_{n+1} = (n+1) Hₙ` and
  `H'' − x H' + n H = 0`.
* `integrable_poly_mul_gaussW`, `integrable_poly_mul_gaussH`, `gint_ibp` —
  integrability of polynomials against the Gaussian weights, and integration by
  parts on all of `ℝ`.
* `hermiteInner_eq` — the **orthogonality relations**
  `∫ Hₘ Hₙ e^{-x²/2} = δₘₙ · n! · √(2π)`.
* `hermiteFun n x = Hₙ(x) e^{-x²/4}`, `hermiteLp n` its normalization in `L²`,
  and `orthonormal_hermiteLp` — the Hermite functions are orthonormal in
  `L²(ℝ, ℂ)`.
* `poly_mul_gaussH_mem_span` — every `p(x) e^{-x²/4}` lies in the span of the
  Hermite functions.
* `integral_fourier_mul_comm`, `ae_eq_zero_of_fourier_eq_zero`,
  `fourier_gaussH_mul_eq_zero`, `ae_eq_zero_of_moments` — the Fourier route to
  completeness: the multiplication formula `∫ (𝓕f) g = ∫ f (𝓕g)`, Fourier
  uniqueness for `L¹` functions, and the fact that a `u ∈ L²` orthogonal to
  every `xᵏ e^{-x²/4}` vanishes a.e. (the exponential series for
  `e^{i a x} e^{-x²/4} u` is dominated by `e^{|a||x|} e^{-x²/4} |u|`).
* `hermiteLp_span_dense`, `hermiteBasis` — **completeness**: the Hermite
  functions form a Hilbert basis `HilbertBasis ℕ ℂ (L²(ℝ))`.
* `hermiteFun_oscillator` — `−ψₙ'' + (x²/4) ψₙ = (n + ½) ψₙ`.

## 2. `ChapterStrichartzHermiteQG` — the core and the Hamiltonians

* `hermiteCore = span_ℂ {ψ₀, ψ₁, …} ⊆ L²(ℝ)` — the **Hermite core**: the finite
  linear combinations of Hermite functions, i.e. polynomials times `e^{-x²/4}`;
  `hermiteCore_dense` says it is dense.
* `hermiteDiagDomain`, `hermiteDiagOp`, `hermiteCoreOp lam` — the operator that
  is diagonal in the Hermite basis with real symbol `lam : ℕ → ℝ`, on its
  maximal domain and restricted to the core; `hermiteCoreOp_hermiteLp` gives
  `H ψₙ = lam n · ψₙ`.
* `hermiteCoreOp_symmetric` — symmetry on the core.
* `hermiteCoreOp_deficiencyTrivialAt` — the **Strichartz input**, proved: the
  deficiency space of the adjoint is trivial at every non-real `z`.
* `hermiteCoreOp_essentiallySelfAdjoint` — hence **essential self-adjointness on
  the core**, via `strichartz_esa_of_finiteSpeed`.
* `hermiteCoreOp_not_bounded` — for an unbounded symbol the operator is
  unbounded, so nothing here is a bounded-operator triviality.
* `oscillatorSymbol`, `oscillator_eigenfunction`,
  `oscillator_essentiallySelfAdjoint_on_hermiteCore` — the harmonic oscillator
  `−d²/dx² + x²/4` on the Hermite core.
* `qg3DModeSymbol`, `qg3DHermiteHamiltonian` — the **3D gauge-fixed
  quantum-gravity mode symbol**: mode by mode the hyperbolic principal symbol
  `qgSymbol ξ ξ_y = (1/16) Σ_{a<3} ξ_a² − (1/24) ξ_y²` of
  `ChapterQuantumGravityDensitized`, plus a real potential.
* `qg3D_symmetric`, `qg3D_deficiencyTrivialAt`,
  `qg3D_essentiallySelfAdjoint_on_hermiteCore`, `qg3D_not_bounded` — the
  Strichartz-type conclusion for that Hamiltonian on the Hermite core, and the
  fact that it is unbounded.
* `qgMode_essentiallySelfAdjoint_on_hermiteCore` — the same for the one-mode
  symbol `qgModeSymbol a b V` of the earlier chapter, now realized on `L²(ℝ)`
  rather than abstractly on `ℓ²(ℕ)`.
