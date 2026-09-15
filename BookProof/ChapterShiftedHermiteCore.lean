import BookProof.ChapterShiftedHermiteCore.Part1
import BookProof.ChapterShiftedHermiteCore.Part2

/-!
# The translated, modulated Gauss–polynomial core of `L²(ℝᵈ)`

`BookProof.ChapterHermiteProductCore` builds the Gauss–polynomial (product Hermite) core
`polyGaussCore = { p · e^{-‖x‖²/4} }` of `L²(ℝᵈ)` and proves it dense, and
`BookProof.ChapterHyperbolicQuadraticEsa` uses it to diagonalize the diagonal quadratic
Hamiltonians `H_c = ∑ᵢ cᵢ(πᵢ² + xᵢ²/4)`.

This module builds the **phase-space translate** of that core: for a translation vector
`a ∈ ℝᵈ` and a wave vector `k ∈ ℝᵈ`,

`D_{a,k} = { x ↦ p(x − a) · e^{-‖x−a‖²/4} · e^{i⟨k,x⟩} : p ∈ ℂ[X₀,…,X_{d-1}] }`.

This is the image of `polyGaussCore` under the Weyl (phase-space translation) unitary
`f ↦ e^{i⟨k,x⟩} f(x − a)`, and it is the natural core for a quadratic Hamiltonian that has
been *completed to a square*: it is the Hermite core recentred at the classical
equilibrium `x = a` and boosted to the classical momentum `k`.

## What is proved

* `pgFunT`, `memLp_pgFunT`, `pgLpT`, `pgMapT`, `pgMapT_injective` — the translated,
  modulated Gauss–polynomial functions are square integrable and depend injectively on the
  polynomial;
* `inner_pgLpT` — the map is **isometric**: `⟪pgLpT a k p, pgLpT a k q⟫ = ⟪pgLp p, pgLp q⟫`
  (translation invariance of Lebesgue measure and `|e^{i⟨k,x⟩}| = 1`);
* `polyGaussCoreT`, `polyGaussCoreT_dense` — the resulting core is dense in `L²(ℝᵈ)`;
* `hermiteTLp`, `orthonormal_hermiteTLp`, `span_hermiteTLp`, `hermiteTLp_total` — the
  translated, modulated product Hermite functions are an orthonormal family spanning the
  core, and total in `L²(ℝᵈ)`;
* `coreEquivT`, `coreOpT` — the core coordinatized by polynomials, and operators on it
  given by operators on the polynomial coordinates;
* `mulXTPoly`, `momTPoly`, `pgFunT_mulXTPoly`, `pgFunT_momTPoly` — **the canonical pair in
  the translated frame**: on `D_{a,k}` multiplication by `xᵢ` is `Xᵢ + aᵢ` and the momentum
  `πᵢ = −i∂/∂xᵢ` is `momPolyᵢ + kᵢ` in the polynomial coordinates, the second identity
  being an honest statement about Mathlib's `deriv` along the `i`-th coordinate line.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/
