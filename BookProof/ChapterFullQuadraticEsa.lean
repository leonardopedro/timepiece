import BookProof.ChapterFullQuadraticEsa.Part1
import BookProof.ChapterFullQuadraticEsa.Part2

/-!
# The general real quadratic Hamiltonian on the Gauss–polynomial core

`BookProof.ChapterModeQuadraticEsa` proves essential self-adjointness, on the plain
Gauss–polynomial (product Hermite) core of `L²(ℝᵈ)`, of the general **mode-diagonal**
quadratic Hamiltonian

`∑ᵢ (pᵢπᵢ² + qᵢxᵢ² + sᵢ·½(xᵢπᵢ + πᵢxᵢ)) + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)`

for arbitrary real `p, q, s, b, b'`.  What that leaves open is the coupling of **distinct**
modes: `xᵢxⱼ`, `πᵢπⱼ` and `xᵢπⱼ` with `i ≠ j`.

This module removes that restriction.  For arbitrary real matrices `P, Q, S` and arbitrary
real vectors `b, b'` the Weyl-ordered operator

`H = ∑_{i,j} (Pᵢⱼ πᵢπⱼ + Qᵢⱼ xᵢxⱼ + Sᵢⱼ·½(xᵢπⱼ + πⱼxᵢ)) + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)`

— i.e. *every* real quadratic-plus-linear Hamiltonian in `d` degrees of freedom, with no
ellipticity, no definiteness, no non-degeneracy and no classical equilibrium — is
essentially self-adjoint on the plain Gauss–polynomial core, and hence generates a
complete unitary flow.

## The mechanism

In the ladder variables `xᵢ = aᵢ† + aᵢ`, `πᵢ = (i/2)(aᵢ† − aᵢ)` a product of two of them
is a sum of four hops of the multi-index `α`:

* `α ↦ α + eᵢ + eⱼ` (pair creation), amplitude `√((αᵢ+1)(αⱼ+1))`;
* `α ↦ α − eᵢ − eⱼ` (pair annihilation), amplitude `√(αᵢαⱼ)`;
* `α ↦ α + eᵢ − eⱼ` (mode exchange), amplitude `√(αⱼ(αᵢ+1))`;

plus, when `i = j`, a constant diagonal.  The first two change the total degree `|α|` by
`±2`, the third preserves it.  `BookProof.ChapterCarlemanSimplex` runs the Carleman flux
argument on the simplex shells `{|α| ≤ N}`, which is exactly adapted to this grading: the
mode-exchange hops carry no flux at all (their contribution over a shell is real, because
their amplitude matrix is Hermitian), and the degree-changing hops leak only through a
two-thick boundary shell.

## What is proved

* `lop_lop_hermiteMv_gen`, `weyl_hermiteMv_gen` — the two-index ladder algebra, uniform in
  `i` and `j` (the diagonal `i = j` differs only by an extra constant).
* `fqQuadPoly`, `fqPoly`, `fqOp` — the Hamiltonian, assembled from Weyl-ordered products
  of the canonical pair, hence symmetric on the core (`fqOp_symmetric`).
* `fqQuadPoly_hermiteMv`, `fqOp_hermiteCore` — its ladder form: a real constant diagonal,
  the pair amplitude `Qᵢⱼ − Pᵢⱼ/4 + i Sᵢⱼ/2`, the Hermitian exchange matrix
  `fqExch`, and the one-step amplitude `bᵢ + i b'ᵢ/2` of the first-order part.
* `fqOp_deficiencyTrivialAt`, `fqOp_essentiallySelfAdjoint` — **the headline**, by the
  simplex Carleman criterion `BookProof.CarlemanSimplex.ladderQ_eq_zero`.
* `fqOp_stone_flow` — the resulting complete unitary flow, by Stone's theorem.
* `crossTerm_essentiallySelfAdjoint`, `crossTerm_stone_flow` — the corollary for the
  purely off-diagonal cross term `½(xᵢπⱼ + πⱼxᵢ) + ½(xⱼπᵢ + πᵢxⱼ)`.
* `rotMat`, `fqQuadPoly_rotMat`, `angularMomentum_essentiallySelfAdjoint`,
  `angularMomentum_stone_flow` — an *antisymmetric* exchange matrix realizes the
  angular-momentum generator `xₖπ_l − x_lπₖ`, the compact counterpart of the dilation
  generator; it too is essentially self-adjoint on the core, with a complete flow.

Everything is `sorry`-free and `axiom`-free.
-/
