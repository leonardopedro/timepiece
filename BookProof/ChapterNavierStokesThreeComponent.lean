import BookProof.ChapterNavierStokesThreeComponent.Part1
import BookProof.ChapterNavierStokesThreeComponent.Part2

/-!
# The three coupled velocity components

The Navier–Stokes fiber analysis carried out in
`BookProof.ChapterNavierStokesAffineFiberEsa` and
`BookProof.ChapterNavierStokesAffineBlockEsa` carries **one** velocity
component: the fiber Hilbert space is `ℓ²(ℕ)`, the Hermite representation of a
single degree of freedom `u`, and the fiber field is the affine
`V(u) = κ u + c`.  The recorded boundary was the coupling of the three velocity
components.

This module removes it.  At one fiber the velocity is now the vector
`u = (u₁, u₂, u₃)`, the Hermite basis is indexed by `Vel = Fin 3 → ℕ`, the fiber
fields are the affine

`V_i(u) = ∑_k A_{ik} u_k + c_i`,

with `A` an **arbitrary real** `3 × 3` matrix (the negative velocity gradient at
the fiber, with no symmetry, positivity or sign assumption) and `c` an arbitrary
real vector, and the fiber Hamiltonian is

`H = ∑_i ½(π_i V_i + V_i π_i)`.

## The Hermite matrix of `H`

Writing `u_i = (a_i + a_i†)/√2` and `π_i = i(a_i† − a_i)/√2`, the terms are

* `A_{ii} ½(π_i u_i + u_i π_i) = (i A_{ii}/2)(a_i†² − a_i²)` — a `±2`-hopping in
  the coordinate `i`, amplitude `(A_{ii}/2)√((β_i+1)(β_i+2))`;
* for `i ≠ k`, `A_{ik} π_i u_k + A_{ki} π_k u_i = i S_{ik}(a_i†a_k† − a_i a_k)
  + i D_{ik}(a_i† a_k − a_i a_k†)` with `S = (A_{ik}+A_{ki})/2` and
  `D = (A_{ik}−A_{ki})/2` — a **double-raising** hopping `β ↦ β + e_i + e_k` of
  amplitude `S√((β_i+1)(β_k+1))` (the strain part) and a **number-conserving**
  hopping `β ↦ β + e_i − e_k` of amplitude `D√((β_i+1)β_k)` (the vorticity
  part);
* `c_i π_i = (i c_i/√2)(a_i† − a_i)` — a `±1`-hopping, amplitude
  `(c_i/√2)√(β_i+1)`.

The vorticity hopping has an amplitude that is *not* monotone along its shift,
and the strain rates and constants have arbitrary signs, so neither
`ShiftHamiltonian.ShiftData` nor its two-shift version applies.  The instrument
used here is `SignedShift.listH_essentiallySelfAdjointOn_core`, which needs
neither positivity nor monotonicity.

## What is proved

* `velH` — the coupled three-component fiber Hamiltonian on the maximal domain
  of the comparison symbol `N = μ(2|β| + 3) + 1` in `ℓ²(Vel)`;
* `velH_symmetricOn` — it is symmetric;
* `velH_essentiallySelfAdjointOn_core` — **the headline**: it is essentially
  self-adjoint on the finite-mode core of `ℓ²(Vel)`, for every real matrix `A`
  and every real vector `c`;
* `velH_coord_pair`, `velH_coord_rot`, `velH_coord_shear`, `velH_coord_diag` —
  the matrix entries: the coupling between distinct components really is
  present;
* `velH_not_bounded` — the operator is unbounded.

## Honest boundary

The setting is the abstract sequence space `ℓ²(Vel)` with the operator given by
its matrix in the Hermite basis of the fiber.  The canonical reading of that
matrix — the ladder pairs, the canonical commutation relations, and the identity
`∑_i ½(π_i V_i + V_i π_i) = velH A c` — is supplied by
`BookProof.ChapterNavierStokesCanonicalVector`; the unitary transport of that
picture to `L²(du₁du₂du₃)` is not built here, and nothing here claims global
regularity for the classical Navier–Stokes equation.
-/
