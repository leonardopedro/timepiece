import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Null-Measure Sets Need Not Be Small" =>
%%%
tag := "null-measure"
%%%

# A Null Event Is Not Automatically Special

A recurring intuitive error is to treat a *measure-zero* event as negligible in a
strong, geometric sense — as if a null subset of a space must be "one dimension
smaller," or as if a null point must be a special, distinguished point. The
manuscript argues, in its discussion of consciousness and Bayesian priors (and of
the Fermi paradox), that both inferences are false. This chapter makes the
measure-theoretic core precise.

# No Point Is Special

Under Lebesgue measure on $`\mathbb{R}`, *every* single point has measure zero, and
all singletons have the *same* measure:

```
#check @ConsciousnessNullMeasure.singleton_volume_zero
#check @ConsciousnessNullMeasure.singletons_equal_measure
```

So a point having measure zero carries no information about its being special: in the
uniform measure on an interval, _every_ point is null. Singling out one null point
(as a "chosen" outcome, or a "conscious" observer) is not justified by the measure.

# Countable Sets Are Null

More generally, every *countable* set has Lebesgue measure zero, by countable
additivity (a countable union of null singletons is null). In particular the
rationals, though dense, are null:

```
#check @ConsciousnessNullMeasure.countable_volume_zero
#check @ConsciousnessNullMeasure.rat_range_volume_zero
```

# But Null Does Not Mean Countable: the Cantor Set

Here is the key counterexample to "null means small." The *ternary Cantor set*
$`C \subset [0,1]` — obtained by repeatedly removing the open middle third — is
simultaneously:

 * *uncountable*, and
 * of Lebesgue *measure zero*.

Its uncountability follows from Cantor's theorem (it is in bijection with
$`\{0,1\}^{\mathbb{N}}`, so $`\aleph_0 < 2^{\aleph_0}`):

```
#check @ConsciousnessNullMeasure.cantorSet_uncountable
```

Its null measure follows from self-similarity: $`C` is the disjoint union of two
scaled copies of itself, each by factor $`1/3`, so $`\mu(C) \le (2/3)\,\mu(C)`,
which (since $`\mu(C) < \infty`) forces $`\mu(C) = 0`:

```
#check @ConsciousnessNullMeasure.cantorSet_volume_zero
```

# The Headline

Putting these together, there exists an *uncountable* subset of $`[0,1]` with
Lebesgue measure *zero*:

```
#check @ConsciousnessNullMeasure.exists_uncountable_null_subset
```

This is exactly the manuscript's point: "a subset with null measure does not imply
that the subset has one less dimension than the set, since there are subsets of a
real interval which have a fractal dimension (which can be very close to one, but
not one) and thus are also uncountable." Measure zero is a statement about
_probability_, not about _cardinality_ or _dimension_. A null set can be as large as
the whole interval in cardinality (uncountable) and can have fractal dimension
arbitrarily close to one.

# Why This Matters for Priors

The consequence for the Bayesian thread of the book is direct. On a continuous space
there is *no uniform probability measure* that makes every point equally likely
(each point would have to be null, yet the whole space has measure one — and there is
no countably-additive way to spread mass uniformly over uncountably many points).
Worse, the "special" outcomes one might want to privilege (a particular observed
value, a particular observer) are null and *indistinguishable*, by the measure,
from every other point. On a general continuous space, then, a prior that looks
non-informative in one parametrization becomes informative in another: a change of
coordinates multiplies the density by a Jacobian, and there is no coordinate-invariant
"uniform" prior to be had. This is the precise sense of the manuscript's slogan
"there are no non-informative priors" — the coordinate argument of
{ref "sequential-bayes"}[the Bayesian-updating chapter]. It connects back to
{ref "max-entropy"}[the maximum-entropy chapter], where a uniform prior existed only
because the space was *finite* (and even there only relative to a labeling), and
forward to the one exception in this book: the
{ref "solovay-tensor"}[Solovay–Kopperman tail], where the restricted decidable
language forbids the very reparametrizations that would break uniformity, so the
Mehler prior on the infinite-dimensional hypersphere stays genuinely uniform.

# Atomic and Continuous Parts: the Five Types

The distinction between a *continuous* prior and a *discrete* (mixed) one can be
made completely precise. Every measure splits into a continuous part and a part
carried by its atoms — the points of positive mass — and the atoms are always a
countable set:

```
#check @BookProof.ChapterAtomicDecomposition.atoms_countable
#check @BookProof.ChapterAtomicDecomposition.noAtoms_continuousPart
#check @BookProof.ChapterAtomicDecomposition.eq_continuousPart_add_atomicPart
```

The atomic part is literally a countable sum of point masses $`\sum_x \mu\{x\}\,
\delta_x`:

```
#check @BookProof.ChapterAtomicDecomposition.atomicPart_eq_sum_dirac
```

Since a probability measure cannot have both parts trivial, exactly five
combinations remain — continuous part present or absent, crossed with no atoms,
finitely many atoms, or countably infinitely many atoms. These are precisely the
five types of the manuscript's list of abelian von Neumann algebras
($`\ell^\infty(\{1,\dots,n\})`, $`\ell^\infty(\mathbb{N})`, $`L^\infty([0,1])`,
and the two mixtures):

```
#check @BookProof.ChapterAtomicDecomposition.not_continuousPart_zero_and_atoms_empty
#check @BookProof.ChapterAtomicDecomposition.probability_measure_five_types
```

The first type is a theorem, not just a label: for a Hermitian matrix with
distinct eigenvalues, the algebra of matrices commuting with it is exactly a
unitary conjugate of the diagonal matrices, i.e. a faithful copy of
$`\ell^\infty(\{1,\dots,n\})`:

```
#check @BookProof.ChapterAbelianVonNeumannFinite.commutant_eq_range_conjDiagonal
#check @BookProof.ChapterAbelianVonNeumannFinite.abelian_commutant_isomorphic_ellInfty
```

In fact the diagonal algebra is *maximal* abelian in the strongest concrete
sense: the embedding $`\ell^\infty(\{1,\dots,n\}) \to \mathrm{Mat}(n,\mathbb{C})`
given by $`d \mapsto \operatorname{diag}(d)` is an injective $`*`-algebra map whose
image is exactly its own commutant — any matrix commuting with *every* diagonal
matrix is itself diagonal. This is the finite (type $`\mathrm{I}_n`) case of von
Neumann's classification, proved outright in `BookProof.ChapterAbelianDiagonal`:

```
#check @BookProof.AbelianDiagonal.diagonalStarAlgHom_injective
#check @BookProof.AbelianDiagonal.diagonal_commute
#check @BookProof.AbelianDiagonal.commutant_diagonal_eq_diagonal
#check @BookProof.AbelianDiagonal.vonNeumann_abelian_typeI_case
```

The next case on the list — the countable one, $`\ell^\infty(\mathbb{N})` — is now
proved as well, on the separable Hilbert space $`\ell^2(\mathbb{N})` built in
`BookProof.ChapterRieszFischer`. Each bounded sequence $`d \in \ell^\infty(\mathbb{N})`
acts as a diagonal multiplication operator of norm at most $`\|d\|`; the
assignment is a faithful unital $`*`-algebra map (`diagOp_injective`,
`diagOp_mul`, `diagOp_one`, `diagOp_star`); its image is abelian; and a bounded
operator commutes with every diagonal operator exactly when it is itself diagonal
(`commutes_diagOp_iff`). So $`\ell^\infty(\mathbb{N})` is a maximal abelian
self-adjoint subalgebra of $`B(\ell^2(\mathbb{N}))`:

```
#check @BookProof.ChapterAbelianDiagonalCountable.diagOp
#check @BookProof.ChapterAbelianDiagonalCountable.norm_diagOp_le
#check @BookProof.ChapterAbelianDiagonalCountable.diagOp_mul
#check @BookProof.ChapterAbelianDiagonalCountable.diagOp_star
#check @BookProof.ChapterAbelianDiagonalCountable.diagOp_injective
#check @BookProof.ChapterAbelianDiagonalCountable.diagOp_comm
#check @BookProof.ChapterAbelianDiagonalCountable.commutes_diagOp_iff
#check @BookProof.ChapterAbelianDiagonalCountable.vonNeumann_abelian_class_countable
```

The third class, the diffuse model $`L^\infty(\mu)` acting on $`L^2(\mu)` by
multiplication, is now proved as well. For an essentially bounded symbol
$`\varphi` the multiplication operator $`M_\varphi f = \varphi\cdot f` is bounded
by the essential supremum, and $`\varphi \mapsto M_\varphi` is unital,
multiplicative, abelian, star-closed (the adjoint of $`M_\varphi` is
$`M_{\bar\varphi}`) and — on a finite measure space — faithful. Lebesgue measure
on $`[0,1]` is atomless, which is exactly what distinguishes this class from the
atomic $`\ell^\infty` models:

```
#check @BookProof.ChapterLinftyMultiplication.multOp
#check @BookProof.ChapterLinftyMultiplication.norm_multOp_le
#check @BookProof.ChapterLinftyMultiplication.multOp_mul
#check @BookProof.ChapterLinftyMultiplication.multOp_one
#check @BookProof.ChapterLinftyMultiplication.multOp_comm
#check @BookProof.ChapterLinftyMultiplication.multOp_inner_adjoint
#check @BookProof.ChapterLinftyMultiplication.multOp_eq_zero_iff
#check @BookProof.ChapterLinftyMultiplication.vonNeumann_abelian_class_Linfty
#check @BookProof.ChapterLinftyMultiplication.unitInterval_atomless
```

The mixed class — an atomic part alongside a diffuse one — is realized too, by
the finite measure $`\mathrm{vol}|_{[0,1]} + \delta_2` on the line: it has a
genuine atom at $`2` and a diffuse part of mass $`1` every point of which is
null, and its multiplication algebra is again unital, abelian, star-closed and
faithful:

```
#check @BookProof.ChapterAbelianMixture.mixtureMeasure
#check @BookProof.ChapterAbelianMixture.mixtureMeasure_atom
#check @BookProof.ChapterAbelianMixture.mixtureMeasure_diffuse_point
#check @BookProof.ChapterAbelianMixture.mixtureMeasure_not_purely_atomic_on_Icc
#check @BookProof.ChapterAbelianMixture.vonNeumann_abelian_class_mixture
```

Exhaustiveness is provable in the *purely atomic* case, and there it collapses the
list to a single model. A bounded operator on $`\ell^2(\mathbb{N})` commutes with
every minimal (rank-one) projection exactly when it is diagonal — the atoms alone
force diagonality — so an algebra that contains all the atomic projections and is
abelian consists of diagonal operators, and if it is in addition maximal abelian it
*is* the diagonal algebra $`\ell^\infty(\mathbb{N})`. On the measure side the atom
set of a probability measure is countable, so a purely atomic index set is either
$`\mathrm{Fin}\,n` or $`\mathbb{N}`: the two purely atomic types of the list, and no
other:

```
#check @BookProof.ChapterAbelianAtomicCondensation.commutes_atomProj_iff
#check @BookProof.ChapterAbelianAtomicCondensation.atomic_abelian_subset_diagonal
#check @BookProof.ChapterAbelianAtomicCondensation.atomic_abelian_maximal_eq_diagonal
#check @BookProof.ChapterAbelianAtomicCondensation.atomic_measure_index_dichotomy
```

At the *diffuse* end the matching structural fact is now proved as well: the
multiplication algebra is *its own commutant*. On a finite measure space, if a
bounded operator $`T` on $`L^2(\mu)` commutes with every multiplication operator,
then $`T` is itself multiplication by a symbol, namely by $`\psi = T(1)`, and that
symbol is essentially bounded with $`\|\psi\|_\infty \le \|T\|`. The argument is the
classical one: commutation gives $`T(\varphi) = \varphi\,\psi` for every bounded
$`\varphi`; testing on the indicator of $`\{\|\psi\| \ge \|T\| + \varepsilon\}` and
comparing the two $`L^2` norms forces that set to be null; and the two continuous
operators $`T` and $`M_\psi`, agreeing on indicators, agree everywhere. So the
diffuse model $`L^\infty[0,1]` on $`L^2[0,1]` is *maximal abelian* — nothing can
be adjoined to it without breaking commutativity — exactly as the diagonal
$`\ell^\infty` is at the atomic end:

```
#check @BookProof.ChapterLinftyMaximalAbelian.symbol
#check @BookProof.ChapterLinftyMaximalAbelian.symbol_mul
#check @BookProof.ChapterLinftyMaximalAbelian.symbol_ae_norm_le
#check @BookProof.ChapterLinftyMaximalAbelian.commutant_eq_multOp
#check @BookProof.ChapterLinftyMaximalAbelian.multOp_algebra_maximal_abelian
#check @BookProof.ChapterLinftyMaximalAbelian.unitInterval_multOp_maximal_abelian
```

The passage in the opposite direction — from an *abstract* abelian algebra to a
concrete *measure* model — is now available at the C\*-level, and it is the
classical two-step route. Gelfand duality identifies a commutative unital
C\*-algebra $`A` with the continuous functions $`C(X,\mathbb{C})` on its character
space $`X`, a compact Hausdorff space. A *state* of $`A` — a linear functional that
is nonnegative on the squares $`a^*a` and sends the unit to $`1` — is then, by the
Riesz–Markov–Kakutani theorem, integration against a Borel *probability measure*
$`\mu` on $`X`: the real part of the state is a positive functional on
$`C(X,\mathbb{R})` (because $`f = |\sqrt f|^2` for $`f \ge 0`), it is real-valued
(because $`f = f^+ - f^-`), and $`\mu` is its Riesz measure. Finally
$`C(X,\mathbb{C})` acts on $`L^2(\mu)` by multiplication operators — a unital
$`*`-homomorphism, injective as soon as $`\mu` charges every nonempty open set — and
the constant function $`1` is a unit vector implementing the state we began with.
So every state of a commutative unital C\*-algebra is the vector state of a
representation of that algebra by multiplication operators on the $`L^2` space of a
probability measure: the abelian Gelfand–Naimark–Segal model.

```
#check @BookProof.ChapterAbelianGelfandModel.rieszStateMeasure
#check @BookProof.ChapterAbelianGelfandModel.integral_rieszStateMeasure
#check @BookProof.ChapterAbelianGelfandModel.exists_probabilityMeasure_of_state
#check @BookProof.ChapterAbelianGelfandModel.mulRepHom
#check @BookProof.ChapterAbelianGelfandModel.mulRepHom_injective
#check @BookProof.ChapterAbelianGelfandModel.inner_oneVec_mulRep
#check @BookProof.ChapterAbelianGelfandModel.gelfandModel
#check @BookProof.ChapterAbelianGelfandModel.state_is_vector_state_of_multiplication
```

For a *single* operator the model can be upgraded from a $`*`-homomorphism to a
*unitary equivalence*, and then it is the spectral theorem itself. Let $`T` be a
normal bounded operator on a complex Hilbert space and let $`\xi` be a cyclic unit
vector, meaning that the vectors $`f(T)\xi`, $`f` continuous on the spectrum, are
dense. Then $`f \mapsto \langle \xi, f(T)\xi\rangle` is a state of
$`C(\sigma(T),\mathbb{C})`, so by the previous paragraph it is integration against
a Borel probability measure $`\mu` on the spectrum; the identity
$`\|f(T)\xi\|^2 = \langle \xi, (\bar f f)(T)\xi\rangle = \int |f|^2\,d\mu` says that
$`f \mapsto f(T)\xi` is an $`L^2(\mu)`-isometry, and since continuous functions are
dense in $`L^2(\mu)` and the $`f(T)\xi` are dense in the space, it extends to a
unitary $`U : L^2(\mu) \to H`. That unitary carries multiplication by the coordinate
function to $`T`: $`U M_z = T U`, and more generally multiplication by any
continuous symbol $`g` into $`g(T)`, so the whole abelian algebra generated by
$`T` becomes an algebra of multiplication operators. A normal operator with a cyclic vector *is*
multiplication by $`z` on the $`L^2` space of a probability measure carried by its
spectrum — the abstract algebra has become a measure model, unitarily.

```
#check @BookProof.ChapterSpectralMultiplication.vectorState
#check @BookProof.ChapterSpectralMultiplication.spectralMeasure
#check @BookProof.ChapterSpectralMultiplication.integral_spectralMeasure
#check @BookProof.ChapterSpectralMultiplication.norm_cfcHom_apply
#check @BookProof.ChapterSpectralMultiplication.spectralUnitary
#check @BookProof.ChapterSpectralMultiplication.spectralUnitary_intertwines_cfc
#check @BookProof.ChapterSpectralMultiplication.spectralUnitary_intertwines
#check @BookProof.ChapterSpectralMultiplication.spectral_multiplication_model
```

In the presence of a cyclic vector one can go one step further and reach the *von
Neumann* level, by computing the commutant. The point is that continuous symbols
already suffice: if a bounded operator $`S` on $`L^2(\mu)` commutes with
multiplication by every *continuous* function on a compact space carrying a finite
regular Borel measure, then $`S` is itself multiplication by an essentially bounded
symbol. Writing $`\psi = S(1)`, commutation gives $`S g = g\,\psi` for continuous
$`g`; truncating $`\psi` to the set where $`\|S\| + \varepsilon \le |\psi| \le m` turns
the inequality $`\|\psi g\|_2 \le \|S\|\,\|g\|_2` into a bound on a genuine
multiplication operator, which extends from the continuous functions to all of
$`L^2(\mu)` by density and, tested on the indicator of that set, forces the set to be
null. So $`\psi \in L^\infty(\mu)` and $`S = M_\psi` by density again.

Transported through the spectral unitary, this says that the commutant of
$`\{f(T)\}` — every bounded operator commuting with all continuous functions of a
normal $`T` with a cyclic vector — is *exactly* the unitary copy of
$`L^\infty(\mu)` acting by multiplication. Since the multiplication algebra is its
own commutant, the *bicommutant* of $`\{f(T)\}`, that is the von Neumann algebra
generated by $`T`, is that same copy of $`L^\infty(\mu)`; in particular the commutant
is abelian, so the algebra generated by a normal operator with a cyclic vector is
*maximal* abelian. For the singly generated, cyclic case this is the von Neumann
form of the classification, obtained without any appeal to a general bicommutant
theorem.

```
#check @BookProof.ChapterSpectralCommutant.multAlgebra
#check @BookProof.ChapterSpectralCommutant.centralizer_multAlgebra
#check @BookProof.ChapterSpectralCommutant.bicommutant_multAlgebra
#check @BookProof.ChapterSpectralCommutant.contCommutant_eq_multOp
#check @BookProof.ChapterSpectralCommutant.centralizer_cfcSet
#check @BookProof.ChapterSpectralCommutant.bicommutant_cfcSet
#check @BookProof.ChapterSpectralCommutant.commutant_cfcSet_isCommutative
```

The hypothesis that carries all of this is the existence of a *cyclic vector*, and
that hypothesis can now be removed from the geometry, if not yet from the assembly.
For a normal $`T` the closed subspace generated by a single vector $`\xi` under the
continuous functional calculus — the closed span of the $`f(T)\xi` — is invariant
under the whole algebra, and because that algebra is closed under adjoints
($`f(T)^* = \bar f(T)`), the orthogonal complement of an invariant subspace is
invariant too. So a vector orthogonal to everything collected so far generates a
cyclic subspace that stays orthogonal to it, and Zorn's lemma produces a maximal
family of unit vectors with pairwise orthogonal cyclic subspaces. Maximality forces
the span of that family to be dense: otherwise its orthogonal complement would
contain a unit vector, which could be added to the family. Every complex Hilbert
space is therefore the orthogonal direct sum of subspaces on each of which $`T` has
a cyclic vector — and on each of those the multiplication model and its commutant
computation apply verbatim.

```
#check @BookProof.ChapterCyclicDecomposition.cyclicSubspace
#check @BookProof.ChapterCyclicDecomposition.invariant_cyclicSubspace
#check @BookProof.ChapterCyclicDecomposition.invariant_orthogonal
#check @BookProof.ChapterCyclicDecomposition.cyclicSubspace_le_orthogonal
#check @BookProof.ChapterCyclicDecomposition.exists_cyclic_decomposition
```

That decomposition can be stated as an identification rather than a list. The
cyclic subspaces of such a maximal family are an orthogonal family in the technical
sense, and since they are jointly total the space *is* their Hilbert sum: there is a
unitary between $`H` and the $`\ell^2`-sum of the summands. The operator respects
the splitting for the sharpest possible reason — the orthogonal projection onto an
invariant subspace commutes with $`f(T)` for every continuous $`f`, because the
complement is invariant too, so each of those projections lies in the *commutant* of
the algebra generated by $`T`. Applied to a vector, the projections onto the cyclic
summands sum back to it. So $`T` is the direct sum of its restrictions to the
summands, on each of which the multiplication model and the commutant computation
above apply verbatim.

```
#check @BookProof.ChapterCyclicDirectSum.orthogonalFamily_cyclicSubspace
#check @BookProof.ChapterCyclicDirectSum.isHilbertSum_cyclicSubspace
#check @BookProof.ChapterCyclicDirectSum.cyclicHilbertEquiv
#check @BookProof.ChapterCyclicDirectSum.exists_isHilbertSum_cyclicSubspace
#check @BookProof.ChapterCyclicDirectSum.commute_starProjection_cfcHom
#check @BookProof.ChapterCyclicDirectSum.starProjection_cyclicSubspace_commutes
#check @BookProof.ChapterCyclicDirectSum.hasSum_starProjection_cyclicSubspace
```

The assembly can then be carried out, and it removes the cyclic-vector hypothesis
from the model itself. The trick is to build the model of a summand *inside* the
ambient space, so that no functional calculus of a restricted operator is ever
needed: the identity $`\|f(T)\xi\| = \|f\|_{L^2(\mu_\xi)}` holds for any vector
$`\xi`, cyclic or not, so the map $`f \mapsto f(T)\xi` extends to a unitary from
$`L^2(\mu_\xi)` onto the cyclic subspace of $`\xi` — in which $`\xi` is cyclic by
construction — and, read in $`H`, to an isometric embedding of $`L^2(\mu_\xi)` with
range that subspace, carrying multiplication by a continuous symbol $`g` into
$`g(T)` and multiplication by $`z` into $`T`. Running this over a maximal orthogonal
cyclic family gives the general form of the spectral theorem: for *every* normal
operator on a complex Hilbert space there are Borel probability measures $`\mu_x` on
its spectrum and isometric embeddings $`V_x : L^2(\mu_x) \to H` exhibiting $`H` as
the Hilbert sum of the $`L^2(\mu_x)`, with $`T` acting on each summand as
multiplication by the coordinate function. Every normal operator is a direct sum of
multiplication operators; no cyclic vector and no separability are assumed.

```
#check @BookProof.ChapterSpectralDirectSum.cyclicUnitary
#check @BookProof.ChapterSpectralDirectSum.cyclicEmbedding
#check @BookProof.ChapterSpectralDirectSum.range_cyclicEmbedding
#check @BookProof.ChapterSpectralDirectSum.cyclicEmbedding_intertwines_cfc
#check @BookProof.ChapterSpectralDirectSum.cyclicEmbedding_intertwines
#check @BookProof.ChapterSpectralDirectSum.spectral_multiplication_model_general
```

If the space is separable the decomposition is moreover *countable*: distinct members
of the family are unit vectors with orthogonal cyclic subspaces, hence orthogonal, so
they sit at distance $`\sqrt 2` from one another and the balls of radius $`1/2` around
them are disjoint — a separable space admits only countably many such. So on a
separable space every normal operator is a countable direct sum of multiplication
operators, which is the form in which the classification of abelian algebras on
separable $`L^2` is usually stated.

```
#check @BookProof.ChapterSpectralDirectSum.countable_orthogonalCyclicFamily
#check @BookProof.ChapterSpectralDirectSum.spectral_multiplication_model_separable
```

The single-generator hypothesis can be dropped as well, and dropping it does not
require producing a generator. Nothing in the argument above used that the algebra
was the one generated by *one* operator: what was used is that a unital
$`*`-representation $`\pi` of the continuous functions on a compact Hausdorff space
turns the vector $`\xi` into a state $`f \mapsto \langle \xi, \pi(f)\xi\rangle`,
that positivity of that state is the identity
$`\langle \xi, \pi(\bar f f)\xi\rangle = \|\pi(f)\xi\|^2`, and that the same identity
makes $`f \mapsto \pi(f)\xi` an $`L^2(\mu)`-isometry. So for an *arbitrary* abelian
algebra, presented as such a representation, a cyclic unit vector already gives a
Borel probability measure $`\mu` and a unitary $`U : L^2(\mu) \to H` carrying
multiplication by every continuous symbol $`g` into $`\pi(g)`. (No continuity of
$`\pi` is assumed anywhere; it is not needed.) Through Gelfand duality this is a
statement about the abstract algebra: every representation of a commutative unital
C\*-algebra with a cyclic unit vector is unitarily the representation by
multiplication operators on the $`L^2` space of a Borel probability measure on the
character space.

```
#check @BookProof.ChapterAbelianCyclicModel.repState
#check @BookProof.ChapterAbelianCyclicModel.repMeasure
#check @BookProof.ChapterAbelianCyclicModel.norm_rep_apply
#check @BookProof.ChapterAbelianCyclicModel.cyclicRepUnitary
#check @BookProof.ChapterAbelianCyclicModel.cyclicRepUnitary_intertwines
#check @BookProof.ChapterAbelianCyclicModel.cyclic_representation_multiplication_model
#check @BookProof.ChapterAbelianCyclicModel.abelian_algebra_multiplication_model
```

The commutant computation transports through that unitary just as it did for a
single operator, so the von Neumann statement comes with it: the commutant of the
represented algebra is exactly the unitary copy of $`L^\infty(\mu)`, that copy is its
own commutant, hence the *bicommutant* — the von Neumann algebra generated by the
algebra — is the same copy, and the commutant is abelian. An arbitrary abelian
C\*-algebra acting with a cyclic vector is therefore maximal abelian and is
$`L^\infty(\mu)` acting on $`L^2(\mu)`, with no generator produced anywhere.

```
#check @BookProof.ChapterAbelianCyclicCommutant.centralizer_repSet
#check @BookProof.ChapterAbelianCyclicCommutant.centralizer_multModelRep
#check @BookProof.ChapterAbelianCyclicCommutant.bicommutant_repSet
#check @BookProof.ChapterAbelianCyclicCommutant.commutant_repSet_isCommutative
#check @BookProof.ChapterAbelianCyclicCommutant.abelian_algebra_maximal_abelian_of_cyclic
```

The cyclic-vector hypothesis can be removed here too, and for the same reason as
before: the decomposition argument used only that the algebra of operators is
$`*`-closed, never that it came from one operator. So for an arbitrary abelian
algebra the cyclic subspaces are invariant, the orthogonal complement of an
invariant subspace is invariant, Zorn's lemma produces a maximal family of unit
vectors with pairwise orthogonal cyclic subspaces, the space is the Hilbert sum of
those subspaces, and the projections onto them lie in the commutant. Building each
summand's model inside the ambient space then glues the pieces: *every* abelian
algebra of operators on a complex Hilbert space — presented as a unital
$`*`-representation of the continuous functions on a compact Hausdorff space, or
through Gelfand duality as a representation of a commutative unital C\*-algebra — is
a direct sum of multiplication algebras. There are Borel probability measures
$`\mu_x` and isometric embeddings $`V_x : L^2(\mu_x) \to H` exhibiting $`H` as their
Hilbert sum, with each $`\pi(g)` acting on the summand as multiplication by $`g`. No
cyclic vector, no generator and no separability are assumed; on a separable space
the family is moreover countable.

```
#check @BookProof.ChapterAbelianDirectSum.exists_rep_cyclic_decomposition
#check @BookProof.ChapterAbelianDirectSum.exists_isHilbertSum_repCyclicSubspace
#check @BookProof.ChapterAbelianDirectSum.starProjection_commutes_rep
#check @BookProof.ChapterAbelianDirectSum.repEmbedding
#check @BookProof.ChapterAbelianDirectSum.repEmbedding_intertwines
#check @BookProof.ChapterAbelianDirectSum.abelian_multiplication_model_general
#check @BookProof.ChapterAbelianDirectSum.abelian_multiplication_model_separable
#check @BookProof.ChapterAbelianDirectSum.abelian_algebra_multiplication_model_general
```

The measures produced by that decomposition can be sorted into the manuscript's
classes as well. The atoms of a finite measure are countable, because the singletons
are pairwise disjoint and only countably many disjoint sets can carry positive mass;
restricting to the atoms gives a purely atomic measure, a countable sum of point
masses $`\mu\{x\}\,\delta_x`, and restricting to their complement gives a measure with
no atoms at all. Every summand of the model is therefore an atomic piece, a diffuse
piece, or a mixture of the two — the manuscript's three-way alternative, with the
atomic case the $`I_n` / $`\ell^\infty(\mathbb N)` models and the diffuse case the
$`L^\infty(\mu)` one.

```
#check @BookProof.ChapterMeasureAtomicDiffuse.countable_atomSet
#check @BookProof.ChapterMeasureAtomicDiffuse.restrict_atomSet_add_restrict_compl
#check @BookProof.ChapterMeasureAtomicDiffuse.restrict_atomSet_eq_sum_dirac
#check @BookProof.ChapterMeasureAtomicDiffuse.exists_atomic_diffuse_decomposition
#check @BookProof.ChapterMeasureAtomicDiffuse.abelian_multiplication_model_atomic_diffuse
```

The diffuse case can be pinned down further, at least on the line. A diffuse
probability measure $`\mu` on $`\mathbb R` has a *continuous* distribution function
$`F(x) = \mu(-\infty, x]`: the function is monotone and right continuous in any case,
and its jump at a point is exactly the mass of that point, which is zero. Being
continuous and running from $`0` at $`-\infty` to $`1` at $`+\infty`, it attains every
intermediate level, and the sublevel set $`\{F \le t\}` then has mass exactly $`t`
for $`0 \le t < 1` — it contains a half line $`(-\infty, x]` with $`F(x) = t` and is
contained in every half line $`(-\infty, y]` with $`F(y) > t`. Comparing the two
measures on the half lines, which generate the Borel sets, gives the statement in
closed form: $`F` pushes $`\mu` forward to Lebesgue measure on the unit interval.
So every diffuse probability measure on the line is a copy of the uniform measure,
read through its own distribution function — the $`L^\infty[0,1]` entry of the
classification list.

```
#check @BookProof.ChapterDiffuseCdfModel.continuous_cdf_of_noAtoms
#check @BookProof.ChapterDiffuseCdfModel.exists_cdf_eq
#check @BookProof.ChapterDiffuseCdfModel.measure_cdf_le
#check @BookProof.ChapterDiffuseCdfModel.map_cdf_eq_volume_Icc
```

That is a statement about measures; the classification list makes a statement about
operators, and the two are separated by exactly one step. Composing with $`F` is an
isometry of $`L^2` of the uniform measure into $`L^2(\mu)`, because $`F` is measure
preserving. It is *onto* because the sets that agree, up to a $`\mu`-null set, with a
preimage under $`F` form an algebra of sets, and that algebra contains every half
line — the half line $`(-\infty, x]` differs from $`\{F \le F(x)\}` by a null set,
since the two have the same mass. An algebra of sets that generates the Borel sets is
measure dense, so the indicator of *any* measurable set is an $`L^2` limit of
indicators of such sets, hence lies in the range; the range is closed and contains all
indicators, and indicators span a dense subspace of $`L^2`, so the range is
everything. Composition with $`F` is therefore a unitary, and it carries
multiplication by an essentially bounded symbol $`g` to multiplication by $`g \circ F`.
The multiplication algebra of an arbitrary diffuse probability measure on the line is
thus unitarily the multiplication algebra of the unit interval.

```
#check @BookProof.ChapterDiffuseUnitaryModel.measurePreserving_cdf
#check @BookProof.ChapterDiffuseUnitaryModel.measureDense_cdfAlgebra
#check @BookProof.ChapterDiffuseUnitaryModel.cdfRange_eq_top
#check @BookProof.ChapterDiffuseUnitaryModel.cdfUnitary_intertwines
#check @BookProof.ChapterDiffuseUnitaryModel.diffuse_multiplication_model_uniform
```

The atomic alternative is the other standard type, and it is settled by the same kind
of argument in a much simpler setting. If $`\mu` is carried by its atoms, the
normalised indicators $`\delta_a / \sqrt{\mu\{a\}}` of the atoms are an orthonormal
family in $`L^2(\mu)`, and nothing is orthogonal to all of them: a function orthogonal
to the indicator of an atom vanishes at that atom, and a function vanishing at every
atom vanishes almost everywhere, because the complement of the atoms is null. So the
normalised point masses are a Hilbert basis indexed by the atoms, and multiplication
by a symbol $`g` is *diagonal* in that basis, scaling the basis vector at $`a` by
$`g(a)`. An atomic summand of the model is therefore a diagonal algebra whose size is
the number of atoms — the $`I_n` and $`\ell^\infty(\mathbb N)` entries of the
classification list.

```
#check @BookProof.ChapterAtomicDiagonalModel.orthonormal_atomVec
#check @BookProof.ChapterAtomicDiagonalModel.atomBasis
#check @BookProof.ChapterAtomicDiagonalModel.multOp_atomVec
#check @BookProof.ChapterAtomicDiagonalModel.atomic_multiplication_model_diagonal
```

The two models are glued together by the Hilbert-space counterpart of the splitting
of the measure. For a measurable set $`A`, extension by zero embeds $`L^2(\mu|_A)`
isometrically into $`L^2(\mu)`, the embeddings along $`A` and its complement have
orthogonal ranges, and every vector is the sum of its two pieces; so $`L^2(\mu)` is
the Hilbert sum of $`L^2(\mu|_A)` and $`L^2(\mu|_{A^c})`, and the embeddings
intertwine the multiplication operators — the splitting is a splitting of the
algebra, not just of the space.

```
#check @BookProof.ChapterLpRestrictSplit.restrictEmbed_add_restrictEmbed_compl
#check @BookProof.ChapterLpRestrictSplit.isHilbertSum_splitEmbed
#check @BookProof.ChapterLpRestrictSplit.restrictEmbed_intertwines
```

One mismatch remains: the diffuse model is stated for a probability measure, while
the diffuse part of a mixed measure has some intermediate mass. Rescaling a measure
by a nonzero finite constant changes the $`L^2` norm by a constant factor and nothing
else, so a scalar multiple of the identity is a unitary between the two $`L^2`
spaces, and it carries multiplication by a symbol to multiplication by the same
symbol. Total mass is therefore invisible to the multiplication algebra.

```
#check @BookProof.ChapterLpScaleMeasure.scaleUnitary_intertwines
#check @BookProof.ChapterLpScaleMeasure.normalized_multiplication_model
```

Assembling the pieces gives the classification list itself. Let $`\mu` be a Borel
probability measure on the line and $`S` its (countable) set of atoms. Then
$`L^2(\mu)` is the Hilbert sum of the atomic piece $`L^2(\mu|_S)` and the diffuse
piece $`L^2(\mu|_{S^c})`; multiplication is diagonal on the first, in the basis of
normalised point masses; and the second, when it is nonzero, is unitarily
$`L^2[0,1]`, with multiplication by $`g` becoming multiplication by $`g \circ F`
for the distribution function $`F` of the normalised diffuse part. Splitting on
whether $`S` carries all, none or part of the mass, and on whether $`S` is finite or
infinite, gives exactly the manuscript's five types: $`I_n`,
$`\ell^\infty(\mathbb N)`, $`L^\infty[0,1]`, $`L^\infty[0,1] \oplus I_n` and
$`L^\infty[0,1] \oplus \ell^\infty(\mathbb N)`.

```
#check @BookProof.ChapterAbelianClassificationList.diffuse_finite_multiplication_model
#check @BookProof.ChapterAbelianClassificationList.abelian_summand_standard_model
#check @BookProof.ChapterAbelianClassificationList.vonNeumann_abelian_classification_list
```

The list above classifies a *summand* — a measure on the line — and the last step is
to get an arbitrary summand there. That is the Borel isomorphism theorem: an
uncountable standard Borel space is Borel isomorphic to $`\mathbb R`. A measurable
equivalence is measure preserving onto the pushforward measure in both directions, so
composition with it is a *unitary* between the two $`L^2` spaces, and it turns
multiplication by $`g` into multiplication by $`g \circ e`. A countable space needs
no transport at all: there every measure is carried by its atoms, and multiplication
is already diagonal. So a Borel probability measure on *any* standard Borel space
realises one of the five standard types, and — for a compact metrizable spectrum —
every summand of the general abelian model does.

```
#check @BookProof.ChapterStandardBorelClassification.transportUnitary_intertwines
#check @BookProof.ChapterStandardBorelClassification.purelyAtomic_of_countable
#check @BookProof.ChapterStandardBorelClassification.standardBorel_classification_list
#check @BookProof.ChapterStandardBorelClassification.abelian_multiplication_model_classified
```

For a *normal operator* the metrizability hypothesis is automatic, because its
spectrum is a compact subset of $`\mathbb C`. So the classification is unconditional
there: every normal operator on a complex Hilbert space is a direct sum of
multiplication operators, each summand of which realises one of the five standard
types.

```
#check @BookProof.ChapterStandardBorelClassification.spectral_multiplication_model_classified
```

The metrizability hypothesis in the general representation-theoretic form is not a
topological accident either: for a compact Hausdorff spectrum $`Y` it is *equivalent*
to separability of the algebra $`C(Y, \mathbb C)`. In one direction, a countable dense
family of continuous functions separates the points of $`Y` — two points it does not
separate are separated by no continuous function at all, and Urysohn's lemma separates
distinct points of a compact Hausdorff space — so the family embeds $`Y` into a
countable power of $`\mathbb C`, a continuous injection out of a compact space into a
Hausdorff space being an embedding. In the other direction, a compact metrizable space
is second countable and its algebra of continuous functions is separable.

```
#check @BookProof.ChapterSeparableSpectrum.metrizableSpace_of_separable_continuousMap
#check @BookProof.ChapterSeparableSpectrum.separableSpace_continuousMap_of_metrizable
#check @BookProof.ChapterSeparableSpectrum.metrizableSpace_iff_separableSpace_continuousMap
```

Through Gelfand duality this discharges the hypothesis in the standard setting. The
Gelfand transform is an isometric $`*`-isomorphism of a commutative unital
C\*-algebra $`A` with $`C(\Omega(A), \mathbb C)`, so if $`A` is separable then so is
that algebra, and the character space $`\Omega(A)` is metrizable — a compact metric,
hence standard Borel, space. Consequently every unital $`*`-representation of a
*separable* commutative unital C\*-algebra on a complex Hilbert space is a direct sum
of multiplication algebras, each of which realises one of the five standard types, with
no hypothesis on the spectrum at all.

```
#check @BookProof.ChapterSeparableSpectrum.metrizableSpace_characterSpace
#check @BookProof.ChapterSeparableSpectrum.abelian_multiplication_model_classified_separable
#check @BookProof.ChapterSeparableSpectrum.abelian_algebra_multiplication_model_classified
```

The remaining case — an algebra that is not norm-separable, for instance
$`L^\infty[0,1]` acting on $`L^2[0,1]` — is settled by looking at the Hilbert space
instead of at the algebra. If the algebra acts on a *separable* Hilbert space then each
summand $`L^2(\mu_x)` is separable, so a *countable* family $`D` of continuous functions
is already dense in it. Evaluating that family, $`y \mapsto (f(y))_{f \in D}`, maps the
spectrum into the countable power $`\mathbb{C}^D`, a Polish and hence standard Borel
space. Composition with the evaluation map is isometric, its range is closed and contains
the dense family, so it is a *unitary* onto $`L^2(\mu_x)`, and it turns multiplication by
$`g` into multiplication by $`g` composed with the evaluation. The summand is therefore
unitarily a Borel probability measure on a standard Borel space, and the classification
applies to it.

```
#check @BookProof.ChapterSeparableL2Model.exists_countable_dense_continuous
#check @BookProof.ChapterSeparableL2Model.separable_Lp_realizes_standard_type
#check @BookProof.ChapterSeparableL2Model.abelian_multiplication_model_classified_separable_hilbert
#check @BookProof.ChapterSeparableL2Model.abelian_algebra_multiplication_model_classified_separable_hilbert
```

So for a separably acting abelian algebra the classification is unconditional: no
metrizability of the spectrum, and no separability of the algebra, has to be assumed.

The same statement is packaged, against the manuscript's five-type list, in
`BookProof.ChapterSelectingEvents`:

```
#check @BookProof.ChapterSelectingEvents.vonNeumann_abelian_classification_typeI
```

# Continuous Priors Are Out of Reach of Discrete Ones

The splitting also settles the manuscript's "worst-case versus best-case prior"
argument. Rescaling the continuous part of a mixed prior (conditioning on the
complement of its atoms) yields a genuine *continuous* probability measure, and no
purely atomic prior can reproduce it:

```
#check @BookProof.ChapterMixedPrior.atomless_prior_not_purelyAtomic
#check @BookProof.ChapterMixedPrior.noAtoms_normalizedContinuousPart
#check @BookProof.ChapterMixedPrior.exists_continuous_prior_beyond_atomic
```
