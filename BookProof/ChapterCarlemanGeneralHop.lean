import BookProof.ChapterCarlemanGeneralHop.Part1
import BookProof.ChapterCarlemanGeneralHop.Part2

/-!
# A Carleman criterion for general lattice hops

`BookProof.ChapterHermiteCarlemanEsa` and `BookProof.ChapterCarlemanTwoStep` prove
Carleman (flux) criteria for recursions whose hops move a **single** excitation number,
by one or by two.  That covers every **mode-diagonal** quadratic Hamiltonian.  A quadratic
Hamiltonian which couples two *distinct* modes — `xᵢxⱼ`, `πᵢπⱼ`, `xᵢπⱼ` with `i ≠ j` —
produces hops `α ↦ α ± (eᵢ + eⱼ)` and `α ↦ α ± (eᵢ − eⱼ)`, and the second kind is **not**
monotone: the shift lowers one coordinate while raising another.

This module runs the flux argument for a hop of the completely general shape
`α ↦ α + p − m` (`hshift`), with `p` and `m` multi-indices.

## What is proved

* `hshift`, `hshift_hshift` — the shift and its inverse on the set where it is defined.
* `rtG`, `ltG`, `hopB`, `sum_ltG`, `sum_hop_im` — **the abstract flux cancellation.**  For
  a Hermitian hop family, the contributions from pairs `α, α + p − m` which both lie in a
  finite set `A` cancel in the imaginary part, so the imaginary part of the total is
  carried by two boundary layers: the *outgoing* layer `A \ B` (points of `A` whose image
  leaves `A`) and the *incoming* layer `B \ A` (points outside `A` whose image lands in
  `A`).  For a monotone hop (`m = 0`) the incoming layer is empty and this specialises to
  the situation of the two earlier modules.
-/
