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
