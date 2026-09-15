import BookProof.ChapterNavierStokesSignFlip.Part1
import BookProof.ChapterNavierStokesSignFlip.Part2

/-!
# The sign-flip unitary: removing the `c ≥ 0` hypothesis

`BookProof.ChapterNavierStokesAffineFiberEsa` proves that the affine
Navier–Stokes fiber Hamiltonian `H = ½(π V + V π)` with `V(u) = κ u + c` is
essentially self-adjoint on the finite-mode core of `ℓ²(ℕ)`, but only for
`c ≥ 0`: the `±1`-hopping amplitude `(c/√2)√(n+1)` of a `ShiftData` is required
to be non-negative.  The recorded remedy was the **sign-flip unitary**
`(U x)_n = (−1)ⁿ x_n`, which reverses the sign of a `±1`-hopping and preserves a
`±2`-hopping.  This module formalizes it and removes the hypothesis.

## What is proved

* `deficiencyTrivialAt_of_intertwine`, `essentiallySelfAdjointOn_of_intertwine` —
  essential self-adjointness is a unitary invariant: if a unitary `U` of the
  ambient Hilbert space preserves the core and intertwines two operators on it,
  `U ∘ T = T' ∘ U`, then `T` is essentially self-adjoint iff `T'` is;
* `flipU` — the sign-flip unitary `(U x)_β = (−1)^{p β} x_β` attached to a parity
  function `p : ι → ℕ`, a `LinearIsometryEquiv` of `ℓ²(ι)` preserving the
  finite-mode core and every maximal domain;
* `hFun_flip`, `shiftH_flip` — the conjugation rule: a shift Hamiltonian whose
  shift changes the parity by `k` is conjugated by `U` into `(−1)^k` times
  itself;
* `saffH` — the affine fiber Hamiltonian for an **arbitrary real** constant `c`
  (the `±1`-hopping amplitude is the signed `(c/√2)√(n+1)`);
* `saffH_conj_flip` — the unitary equivalence `U (affH κ |c|) U = saffH κ c` for
  `c < 0`;
* `saffH_essentiallySelfAdjointOn_core` — **the headline for one fiber**: for
  every `κ ≥ 0` and **every** `c ∈ ℝ`, the affine fiber Hamiltonian is
  essentially self-adjoint on the finite-mode core;
* `saffBlockH_essentiallySelfAdjointOn_core` — the same over the strain-rate
  spectrum: on `ℓ²(ℕ × J)`, for arbitrary families `κ ≥ 0` and `c : J → ℝ` of
  **arbitrary sign**.

## Honest boundary

`κ ≥ 0` is still assumed (the sign-flip unitary preserves the `±2`-hopping, so
it cannot remove that one; it is removed instead in
`BookProof.ChapterNavierStokesSignedShift`).  As in the modules quoted above,
everything is stated on the abstract sequence space with the operator given by
its matrix in the Hermite basis, and nothing here claims global regularity for
the classical Navier–Stokes equation.
-/
