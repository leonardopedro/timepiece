import BookProof.ChapterShiftedQuadraticMatrixEsa.Part1
import BookProof.ChapterShiftedQuadraticMatrixEsa.Part2

/-!
# The indefinite quadratic Hamiltonian **with cross terms** and an unbounded
first-order perturbation

`BookProof.ChapterQuadraticRotationPerturbed` proves that for a **positive definite** real
symmetric matrix `A` and arbitrary real `b, b'` the operator
`H_A + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)`, `H_A = ∑_{k,l} A_{kl}(π_kπ_l + x_kx_l/4)`, is essentially
self-adjoint on the Gauss–polynomial core; positive definiteness is used exactly once, to
produce the relative bound, and the indefinite case was the recorded boundary.
`BookProof.ChapterShiftedQuadraticEsa` removes the sign condition for **diagonal** weights,
by completing the square on a translated, modulated core.

This module combines the two: for **every** real symmetric **invertible** `A` — no sign
condition, so the signature may be elliptic, hyperbolic or anything in between — and
arbitrary real `b, b'`, the operator

`H = ∑_{k,l} A_{kl}(π_kπ_l + x_kx_l/4) + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)`,  `πᵢ = −i∂/∂xᵢ`,

is symmetric and essentially self-adjoint on the translated, modulated Gauss–polynomial
core `D_{a,k}` of `BookProof.ChapterShiftedHermiteCore`, where `a = −2A⁻¹b` and
`k = −A⁻¹b'/2` are the classical equilibrium position and momentum.

The mechanism is again completing the square, now in matrix form:

`∑_{p,q} A_{pq}((π_p + k_p)(π_q + k_q) + (x_p + a_p)(x_q + a_q)/4)
   + ∑ᵢ (bᵢ(xᵢ + aᵢ) + b'ᵢ(πᵢ + kᵢ)) = H_A + const`

as soon as `A a = −2b` and `A k = −b'/2`, and `H_A` is diagonal on the *rotated* Hermite
polynomials, so the *translated, modulated, rotated* Hermite functions are an orthonormal
total family of eigenvectors of `H` in `D_{a,k}`.  No relative bound and no domination is
used; the only hypothesis is invertibility of `A`, which is exactly what is needed to
solve for the classical equilibrium.

## What is proved

* `quadPolyMatT`, `foTPoly`, `shiftedHMatPoly` — the Hamiltonian in the polynomial
  coordinates of the translated, modulated frame;
* `quadPolyMatT_apply_expand` — the expansion of the quadratic part into `H_A`, a
  first-order part and a constant;
* `shiftedHMatPoly_eq_quadPolyMat` — **completing the square** in matrix form;
* `hermiteTRLp`, `orthonormal_hermiteTRLp`, `span_hermiteTRLp`, `hermiteTRLp_total` — the
  translated, modulated, rotated product Hermite functions are an orthonormal family whose
  span is the core and which is total in `L²(ℝᵈ)`;
* `shiftedHMatOp`, `shiftedHMatOp_hermiteTRLp` — the operator and its diagonal action;
* `shiftedHMatOp_symmetric`, `shiftedHMatOp_essentiallySelfAdjoint` — **the headline**, for
  every real symmetric invertible `A` of arbitrary signature;
* `shiftedHMatOp_not_bounded`, `shiftedHMatCore_dense` — non-vacuity: the operator is
  genuinely unbounded (an invertible `A` has no zero eigenvalue) and its domain is dense;
* `shiftedHMatOp_stone_flow` — the resulting complete unitary Schrödinger flow;
* `wave_rotated_linear_essentiallySelfAdjoint` — the corollary: the rotated Minkowski
  quadratic (indefinite, with cross terms) plus an arbitrary constant external field and
  boost.

## Honest boundary

Invertibility of `A` is used exactly once, to solve `A a = −2b`, `A k = −b'/2`; if `A` is
singular and `b` has a component in the kernel the square cannot be completed (the motion
is free in that direction).  Nothing here claims a general Faris–Lavine potential.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/
