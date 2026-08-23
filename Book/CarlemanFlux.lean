import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Carleman Flux Criteria for Lattice Hops" =>
%%%
tag := "carleman-flux"
%%%

# The Problem

:::paragraph
Essential self-adjointness of a quadratic Hamiltonian on the Hermite core can be
proved by a *flux* (Carleman) argument: write the operator on the occupation
basis $`\\alpha \\in \\mathbb N^d`$ and show that the recursion it generates has
bounded flux across every finite box — the probability current crossing the
boundary of a large box must stay controlled as the box grows. The classical
criterion covers hops that move a *single* excitation number, by one or by two,
which is what every mode-diagonal quadratic Hamiltonian produces.
:::

:::paragraph
A quadratic Hamiltonian that couples two *distinct* modes — $`x_i x_j`$,
$`\\pi_i \\pi_j`$, $`x_i \\pi_j`$ with $`i \\neq j`$ — produces the hops
$`\\alpha \\mapsto \\alpha \\pm (e_i + e_j)`$ and $`\\alpha \\mapsto \\alpha \\pm (e_i - e_j)`$.
The second kind is not monotone: the shift raises one coordinate while
lowering another. The general flux criterion must handle that. The module
`BookProof/ChapterCarlemanGeneralHop.lean` (namespace `BookProof.CarlemanGeneralHop`)
runs the argument for a hop of the completely general shape
$`\\alpha \\mapsto \\alpha + p - m`$, with $`p`$ and $`m`$ multi-indices, and is the
last ingredient of the Hermite-core analysis used by the Navier–Stokes and
Yang–Mills generators.
:::

# A Concrete Look at the Two Hop Kinds

:::paragraph
To see why the second kind is genuinely harder, write a two-mode occupation as
a pair $`\\alpha = (a_1, a_2)`$. A mode-diagonal term $`x_1^2` produces the hops
$`(a_1, a_2) \\mapsto (a_1 \\pm 2, a_2)` and $`(a_1 \\pm 1, a_2)` — the excitation
number of mode $`1` changes, mode $`2` is untouched. This is *monotone* in the
total $`|\\alpha| = a_1 + a_2`$: the current crossing a box boundary moves in one
direction only, and the incoming boundary layer is empty, which is exactly the
situation of the earlier single-mode criteria.
:::

:::paragraph
A cross-mode term $`x_1 x_2` produces the hop
$`(a_1, a_2) \\mapsto (a_1 + 1, a_2 + 1)` — both coordinates rise together — but
the pair $`x_1 \\pi_2` (or its Hermitian partner) produces
$`(a_1, a_2) \\mapsto (a_1 + 1, a_2 - 1)`: mode $`1` gains one quantum, mode $`2`$
loses one. The total $`a_1 + a_2` is *unchanged*, so the hop can cross the box
boundary in either direction, and a naive one-sided estimate fails. This is the
$`p - m` shape with $`p = e_1`$, $`m = e_2`$. The general theorem must bound the
flux through *both* boundary layers — the outgoing one and the incoming one —
and show their contributions cancel up to a controlled remainder.
:::

# The Abstract Flux Cancellation

:::paragraph
The heart of the argument is a cancellation that has nothing to do with the
specific Hamiltonian. For a Hermitian hop family, the contributions from pairs
$`\\alpha, \\alpha + p - m`$ that both lie inside a finite set $`A`$ cancel in the
imaginary part. The imaginary part of the total flux is therefore carried by two
*boundary layers*: the outgoing layer $`A \\setminus B`$ — points of $`A`$ whose
image leaves $`A`$ — and the incoming layer $`B \\setminus A`$ — points outside
$`A`$ whose image lands in $`A`$. For a monotone hop ($`m = 0`$) the incoming
layer is empty, which is exactly the situation of the earlier single-mode
criteria.
:::

```
#check @BookProof.CarlemanGeneralHop.hshift
#check @BookProof.CarlemanGeneralHop.hshift_hshift
#check @BookProof.CarlemanGeneralHop.rtG
#check @BookProof.CarlemanGeneralHop.ltG
#check @BookProof.CarlemanGeneralHop.sum_ltG
#check @BookProof.CarlemanGeneralHop.sum_hop_im
#check @BookProof.CarlemanGeneralHop.mem_hopB
```

:::paragraph
Reading the statements: `hshift p m a` is the hop $`a + p - m`$; `hshift_hshift`
records that the map is injective enough to run the counting argument (two
successive hops with the same image coincide); `rtG` and `ltG` are the two halves
of a Hermitian pair — `ltG_eq_conj_rtG` says one is the complex conjugate of the
other, which is exactly what makes the interior contributions cancel in the
imaginary part; `sum_hop_im` is the boundary-layer decomposition itself. The
cancellation is *structural*: it holds for any Hermitian hop family, before any
specific coefficients are chosen.
:::

:::paragraph
The flux criterion is what converts the algebraic (Gauss) symmetry of a
polynomial-level operator — the starting point of
`BookProof.ChapterHermiteCarlemanEsa` and `BookProof.ChapterCarlemanTwoStep` —
into a genuine essential-self-adjointness statement on the Hermite core: the
boundary layers are controlled by the polynomial growth of the coefficients, so
the truncations converge strongly and the closure is self-adjoint. The general
hop closes the last gap for cross-mode quadratic terms.
:::

# Why This Underpins the Physics

:::paragraph
The cross-mode hops are not a curiosity: they are what the physical generators
are made of. The Navier–Stokes fiber Hamiltonian contains the products
$`u_i u_j` and $`\\pi_i u_j` with $`i \\neq j` — the strain and vorticity content
of the velocity-gradient matrix $`A` — and the Yang–Mills quadratic sector
contains the analogous cross-color terms. Each such term generates exactly the
non-monotone $`p - m` hops that the general criterion bounds. So the Carleman
flux argument is the analytic engine that turns the algebraic symmetry theorems
(`nsDiffPoly_polySym`, the Yang–Mills analogue) into the essential
self-adjointness statements on which the Hashimoto selection theorem
(`Book/NavierStokesHashimoto.lean`) and, through it, the SIRK numerical
validation rest.
:::
