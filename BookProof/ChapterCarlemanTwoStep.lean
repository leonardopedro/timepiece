import BookProof.ChapterCarlemanTwoStep.Part1
import BookProof.ChapterCarlemanTwoStep.Part2

/-!
# A two-step Carleman criterion on the multi-index lattice

`BookProof.ChapterHermiteCarlemanEsa` proves a Carleman criterion for a *nearest
neighbour* recursion on the lattice of multi-indices: the hops are `α ↦ α ± eᵢ`, with
amplitudes of size `O(√αᵢ)`.  That is exactly the ladder structure of a **diagonal**
quadratic Hamiltonian `∑ᵢ cᵢ(πᵢ² + xᵢ²/4)` plus a first-order term.

A general **mode-diagonal** quadratic Hamiltonian

`H = ∑ᵢ (pᵢπᵢ² + qᵢxᵢ² + sᵢ·½(xᵢπᵢ + πᵢxᵢ)) + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)`

is not of that form: `xᵢ²`, `πᵢ²` and the squeezing generator `½(xᵢπᵢ + πᵢxᵢ)` all
contain `aᵢ†²` and `aᵢ²`, which move the `i`-th excitation number by **two**, with an
amplitude of size `O(αᵢ)`.  This module proves the Carleman criterion for such a
recursion: hops `α ↦ α ± eᵢ` *and* `α ↦ α ± 2eᵢ`, with amplitudes `O(N)` on the boundary
of the cube `{α : ∀ i, αᵢ ≤ N}`.

## What is proved

* `innK`, `faceK` — the interior and the `k`-thick boundary face of a cube in a fixed
  direction; `sum_shiftK`, `sum_cube_splitK` — the reindexing and splitting identities.
* `rtermG`, `ltermG`, `sum_cube_hop_im` — **the abstract flux cancellation**: for a
  single Hermitian hop family of step `k`, the interior contributions occur in conjugate
  pairs, so the imaginary part of the total contribution over a cube is carried entirely
  by the `k`-thick boundary face.
* `LadderRec2`, `flux_identity2` — the two-step recursion and its flux identity.
* `flux_boundG` — the flux through a face is at most the amplitude bound there times the
  `ℓ²`-mass carried by the face and its shift.
* `sum_range_of_multiplicity`, `faceK_multiplicity`, `shiftedK_multiplicity` — Bessel's
  inequality with multiplicity: a `k`-thick face meets at most `k` cubes, so the total
  face mass is at most `k` times the total mass.  (For `k = 1` the faces are disjoint;
  for `k = 2` they are not, and this is what replaces disjointness.)
* `ladder2_eq_zero` — **the criterion.**  A square-summable family satisfying the
  two-step recursion with a real diagonal and constant amplitudes, at a point off the
  real axis, vanishes.  The Carleman divergence used is `∑ 1/(N+1) = ∞`.

Everything is `sorry`-free and `axiom`-free.
-/
