import BookProof.ChapterNavierStokesSignedShift.Part1
import BookProof.ChapterNavierStokesSignedShift.Part2

/-!
# Hopping Hamiltonians with **signed**, non-monotone amplitudes

`BookProof.ChapterNavierStokesShiftHamiltonian` proves the two Faris–Lavine
inequalities for a hopping (shift) Hamiltonian whose amplitude `w` is
*non-negative* and *non-decreasing along the shift*.  Both restrictions are
artefacts of the bookkeeping — they are used only to produce a majorant for the
two terms of `(H x)_β = i(w(s⁻¹β) x_{s⁻¹β} − w(β) x_{sβ})` — and both are
obstacles for the coupled Navier–Stokes symbol:

* a negative amplitude occurs whenever a strain rate or a fiber constant is
  negative, and
* a non-monotone amplitude occurs for the *number-conserving* hoppings
  `a_i† a_k` produced by the antisymmetric (vorticity) part of the velocity
  gradient, whose amplitude `√((β_i+1) β_k)` increases in one coordinate and
  decreases in the other.

This module removes both.  The observation is that the estimates never need the
amplitude itself: they need a **majorant** which is non-negative, monotone along
the shift and dominated by the comparison symbol.  The canonical such majorant
is `¼ σ + K`, which is monotone as soon as the symbol increases along the shift.

## The data

A `SignedHop ι σ` consists of an injective shift `s`, an **arbitrary real**
amplitude `w` with `|w| ≤ ¼ σ + K`, and a constant, non-negative symbol
increment `σ (s β) = σ β + Δ`.  Its `maj` is the majorant `ShiftData` with the
same shift and symbol and amplitude `¼ σ + K`, so all the transport lemmas of
`ShiftData` are available.

## What is proved

* `SignedHop.hopH` — the signed hopping Hamiltonian on the maximal domain of
  the comparison symbol, and `SignedHop.hopH_symmetricOn`;
* `SignedHop.hopH_relative_bound` — `‖Hx‖² ≤ ½‖Nx‖² + 8K²‖x‖²`;
* `SignedHop.hopH_commForm_bound` — `|⟪x, i[H, N]x⟫| ≤ 2Δ(¼+K) ⟪x, Nx⟫`;
* `SignedHop.hopH_essentiallySelfAdjointOn_core` — essential self-adjointness on
  the finite-mode core;
* `listH` and `listH_essentiallySelfAdjointOn_core` — **the instrument**: a
  finite family of signed hops sharing one comparison symbol sums to an operator
  that is again essentially self-adjoint on the finite-mode core;
* `gaffH` and `gaffH_essentiallySelfAdjointOn_core` — the affine fiber
  Hamiltonian `½(π V + V π)` for `V(u) = κ u + c` with **no sign hypothesis at
  all** on `κ` and `c`.
-/
