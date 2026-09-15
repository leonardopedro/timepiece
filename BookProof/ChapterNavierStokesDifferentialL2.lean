import BookProof.ChapterNavierStokesDifferentialL2.Part1
import BookProof.ChapterNavierStokesDifferentialL2.Part2

/-!
# The differential realization of the Navier–Stokes quadratic symbol on `L²(du₁du₂du₃)`

`BookProof.ChapterNavierStokesThreeComponent` proves that the coupled three-component
fiber Hamiltonian `H = ∑ᵢ ½(πᵢVᵢ + Vᵢπᵢ)`, `Vᵢ(u) = ∑ₖ A_{ik}u_k + c_i`, is essentially
self-adjoint on the finite-mode core of `ℓ²(Vel)`, `Vel = Fin 3 → ℕ`, and
`BookProof.ChapterNavierStokesCanonicalVector` shows that this sequence-space matrix *is*
the Weyl-ordered expression in the abstract ladder operators of that space.  What both
modules record as the honest open step is the **differential realization**: the operator
written with `πᵢ = −i ∂/∂uᵢ` and `uᵢ` a genuine multiplication operator, on the Hermite
core of `L²(du₁du₂du₃)`.  This module takes that step.

## The setting

The Hilbert space is `L²(ℝ³)` and the dense domain is the Gauss–polynomial (product
Hermite) core `polyGaussCore` of `BookProof.ChapterHermiteProductCore`: the functions
`p(u)·e^{-‖u‖²/4}` with `p` a polynomial.  Since `pgMap` is injective, the core carries the
polynomial coordinates `coreEquiv`, and an operator on the core is given by a polynomial
operator (`coreOp`).  Two such operators are the physical ones:

* `posOp i` — multiplication by the coordinate `uᵢ` (`pgFun_mulXPoly`);
* `momOp i` — the differential operator `πᵢ = −i ∂/∂uᵢ`.  That it *is* the derivative is
  `momOp_apply_eq_differential`: the value of `momOp i` at `p·e^{-‖u‖²/4}` is, pointwise,
  `−i` times the honest derivative `deriv (fun t => f (u with uᵢ := t)) uᵢ` of the function
  along the `i`-th coordinate (Mathlib's `deriv`, `hasDerivAt_pgFun_sec`).

`comm_momOp_posOp` is the canonical commutation relation `[πᵢ, u_k] = −i δ_{ik}` for these
genuinely differential operators.

## The Hamiltonian and the transport

`nsDiffH A c = ∑ᵢ ½(πᵢ Vᵢ + Vᵢ πᵢ)` with `Vᵢ` the multiplication operator by the affine
field `∑ₖ A_{ik}u_k + c_i` is the Weyl quantization of the Navier–Stokes quadratic symbol
`A_i(u) = u_j u_{i,j} − ν u_{i,jj}` at one Eulerian fiber (linear part the velocity
gradient, constant part `−ν` times the velocity Laplacian).

The **unitary transport** is `velUnitary : ℓ²(Vel) ≃ₗᵢ L²(ℝ³)`, the Hilbert-basis
isomorphism given by the product Hermite functions
(`BookProof.ChapterHermiteProductBasis`).  It carries the finite-mode core onto the
Gauss–polynomial core (`map_finiteModes`) and the abstract ladder operators onto the
differential ones (`intertwine_ann`, `intertwine_cre`), hence the abstract canonical
Hamiltonian onto the differential one (`conj_canH`).  The conclusions:

* `nsDiffH_essentiallySelfAdjointOn_core` — the **differentially written** Navier–Stokes
  quadratic symbol is essentially self-adjoint on the Hermite core of `L²(ℝ³)`, for every
  real velocity gradient and every constant part;
* `nsQuadraticDiffH_essentiallySelfAdjointOn_core` — the same with the coefficients spelled
  out as `(ν, u_{i,j}, u_{i,jj})`;
* `nsDiffH_not_bounded`, `polyGaussCore_dense_L2` — the operator is genuinely unbounded and
  the domain is dense, so the statement is not a bounded-operator artefact.

## Honest boundary

Nothing here claims global regularity of the *classical* Navier–Stokes PDE (Contention D5,
the deliberate scope cut): the theorem is about the Hilbert-space operator at one Eulerian
fiber, where the derivative fields `u_{i,j}`, `u_{i,jj}` are independent canonical
coordinates.
-/
