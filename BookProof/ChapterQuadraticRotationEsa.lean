import BookProof.ChapterQuadraticRotationEsa.Part1
import BookProof.ChapterQuadraticRotationEsa.Part2

/-!
# General (non-diagonal) quadratic Hamiltonians of arbitrary signature

`BookProof.ChapterHyperbolicQuadraticEsa` proves that the *diagonal* quadratic operator

`H_c = ∑ᵢ cᵢ (−∂ᵢ² + xᵢ²/4)`,  `c : Fin d → ℝ` arbitrary (hyperbolic signatures included),

is essentially self-adjoint on the Gauss–polynomial (product Hermite) core of `L²(ℝᵈ)`.
This module removes the diagonality restriction: for an **arbitrary real symmetric matrix**
`A` the operator

`H_A = ∑_{k,l} A_{kl} (π_k π_l + x_k x_l / 4)`,  `π_k = −i ∂/∂x_k`,

— the general quadratic Hamiltonian whose kinetic and potential forms share the matrix
`A`, of arbitrary signature — is symmetric and essentially self-adjoint on the same core.
With `A = diag(c)` this is the diagonal theorem; with `A` a rotated Minkowski form it is
`□ + V` written in rotated coordinates, where neither the kinetic form nor the potential
is diagonal.

## The route

An orthogonal change of coordinates.  The Gaussian `e^{−‖x‖²/4}` is rotation invariant, so
composition with an orthogonal matrix `O` maps the Gauss–polynomial core onto itself; on
the polynomial coordinates it is the substitution `rotPoly O`, an algebra automorphism.
The canonical pair transforms contravariantly with the *same* matrix
(`rotPoly_mulXPoly`, `rotPoly_momPoly`), so the diagonal operator `H_c` is carried onto
`H_A` with `A = O diag(c) Oᵀ` (`quadPolyMat_rotPoly`).  The rotated product Hermite
functions are therefore an orthonormal family of joint eigenvectors of `H_A` spanning the
core (`orthonormal_rotHermiteLp`, `span_rotHermiteLp`, `quadOpMat_rotHermiteLp`), and the
diagonal instruments of `BookProof.ChapterHyperbolicQuadraticEsa`
(`symmetricOn_of_diagonal`, `deficiencyTrivialAt_of_diagonal`) finish the argument.
The spectral theorem for real symmetric matrices supplies `O` and `c` for an arbitrary
symmetric `A`.

## What is proved

* `rotPoly`, `pderiv_rotPoly`, `rotPoly_mulXPoly`, `rotPoly_momPoly` — the orthogonal
  substitution on polynomial coordinates and its action on the canonical pair;
* `rotIso`, `gaussInt_rotPoly`, `inner_pgLp_rotPoly` — the rotation as a
  measure-preserving linear isometry of `ℝᵈ`, and the resulting unitarity on the core;
* `quadPolyMat`, `quadPolyMat_rotPoly` — the general quadratic operator and the
  conjugation identity `H_{O diag(c) Oᵀ} ∘ R = R ∘ H_c`;
* `rotHermiteLp`, `orthonormal_rotHermiteLp`, `span_rotHermiteLp` — the rotated product
  Hermite functions are an orthonormal family whose span is the core;
* `quadOpMat_rotConj_symmetric`, `quadOpMat_rotConj_essentiallySelfAdjoint` — the headline
  for `A = O diag(c) Oᵀ`;
* `quadOpMat_symmetric`, `quadOpMat_essentiallySelfAdjoint` — **the headline**: for every
  real symmetric matrix `A`, `H_A` is symmetric and essentially self-adjoint on the
  Gauss–polynomial core of `L²(ℝᵈ)`;
* `quadOpMat_not_bounded`, `polyGaussCore_dense_L2` — non-vacuity: the operator is
  genuinely unbounded whenever `A ≠ 0`, and its domain is dense.

## Honest boundary

The potential is quadratic and its matrix is *the same* as the matrix of the kinetic form:
that matched pair is what a single rotation diagonalizes.  A general Faris–Lavine
potential bounded above by a quadratic remains out of reach by this argument, exactly as
recorded in `BookProof.ChapterHyperbolicQuadraticEsa`.
-/
