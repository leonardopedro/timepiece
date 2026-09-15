import BookProof.ChapterQuadratureEsa.Part1
import BookProof.ChapterQuadratureEsa.Part2

/-!
# The quadrature operator `∑ᵢ (bᵢ xᵢ + b'ᵢ πᵢ)` on the Hermite core

`BookProof.ChapterHermiteRelativeBound` proves that the first-order operator
`B = ∑ᵢ (bᵢ xᵢ + b'ᵢ πᵢ)` (`foOp b b'`) is symmetric on the Gauss–polynomial
(product Hermite) core of `L²(ℝᵈ)`, and that `H_c + B` is essentially self-adjoint
whenever the quadratic part `H_c` is *elliptic*.  The shifted-core modules
(`ChapterShiftedQuadraticEsa`, `ChapterShiftedQuadraticMatrixEsa`,
`ChapterShiftedQuadraticDegenerate`) remove the sign and the invertibility
conditions by completing the square, but need a classical equilibrium — which does
not exist in a kernel direction carrying both a linear potential `bᵢxᵢ` and a
momentum term `b'ᵢπᵢ`.  There the operator has no quadratic part at all, and the
two routes used elsewhere both fail: it has no `L²` eigenvector (so the
Hermite-eigenbasis argument does not see it) and it is not constant-coefficient
(so the Fourier-multiplier argument does not see it either).
`BookProof.ChapterMixedLinearEsa` settles that operator on the **Schwartz** core, by
a quadratic gauge.  This module settles it on the **Gauss–polynomial core** — the
core the whole quadratic family lives on — by the metaplectic rotation, which on
that core is nothing but a phase.

## What is proved

* `fourier_eq_zero_of_moments`, `ae_eq_zero_of_moments'` — **a moment lemma without
  an `L²` hypothesis**: a function all of whose exponentially weighted moments are
  finite and all of whose polynomial moments vanish is zero almost everywhere.
  This strengthens `BookProof.HermiteProductCore.ae_eq_zero_of_moments`, which
  needs the function to be a Gaussian times an `L²` function, and is what lets the
  deficiency equation of a *multiplication* operator be treated on the
  Gauss–polynomial core (there the natural function is `e^{-‖x‖²/4}(ℓ − z)u`, which
  is not of that shape);
* `foOp_pos_deficiencyTrivialAt`, `foOp_pos_essentiallySelfAdjoint` — multiplication
  by the real linear function `x ↦ ⟪x, b⟫` is essentially self-adjoint on the core;
* `phaseBasis`, `phaseU`, `phaseU_hermiteMvLp` — **the instrument**: a unimodular
  multiplier on a Hilbert basis is a unitary of the space, sending each basis vector
  to its phase multiple;
* `posL_hermiteCore`, `momL_hermiteCore`, `foOp_hermiteCore` — the ladder form of the
  canonical pair on the product Hermite basis: the quadrature raises the `i`-th
  excitation number with amplitude `wᵢ = bᵢ + ib'ᵢ/2` and lowers it with `conj wᵢ`;
* `phaseU_foOp_hermiteCore` — the phase unitary rotates the canonical pair: it carries
  `foOp r 0` onto `foOp b b'` when `ζᵢ = wᵢ/|wᵢ|`, `rᵢ = |wᵢ|`.  This is the metaplectic
  rotation `e^{iθ·N}`, realized diagonally on the Hermite basis;
* HEADLINE `foOp_essentiallySelfAdjoint` — for **arbitrary** real coefficients
  `b, b'` the quadrature `∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)` is essentially self-adjoint on the
  Gauss–polynomial core of `L²(ℝᵈ)`, and `foOp_stone_flow` turns that into a
  complete unitary flow.

A reusable by-product is `linearMap_ext_of_span`: two linear maps out of a submodule
spanned by a family agree as soon as they agree on that family.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/
