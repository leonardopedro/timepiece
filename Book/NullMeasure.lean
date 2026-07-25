import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Null-Measure Sets Need Not Be Small" =>
%%%
tag := "null-measure"
%%%

# A Null Event Is Not Automatically Special

A recurring intuitive error is to treat a **measure-zero** event as negligible in a
strong, geometric sense — as if a null subset of a space must be "one dimension
smaller," or as if a null point must be a special, distinguished point. The
manuscript argues, in its discussion of consciousness and Bayesian priors (and of
the Fermi paradox), that both inferences are false. This chapter makes the
measure-theoretic core precise.

# No Point Is Special

Under Lebesgue measure on $`\mathbb{R}`, **every** single point has measure zero, and
all singletons have the **same** measure:

```
#check @ChapterConsciousnessNullMeasure.singleton_volume_zero
#check @ChapterConsciousnessNullMeasure.singletons_equal_measure
```

So a point having measure zero carries no information about its being special: in the
uniform measure on an interval, _every_ point is null. Singling out one null point
(as a "chosen" outcome, or a "conscious" observer) is not justified by the measure.

# Countable Sets Are Null

More generally, every **countable** set has Lebesgue measure zero, by countable
additivity (a countable union of null singletons is null). In particular the
rationals, though dense, are null:

```
#check @ChapterConsciousnessNullMeasure.countable_volume_zero
#check @ChapterConsciousnessNullMeasure.rat_range_volume_zero
```

# But Null Does Not Mean Countable: the Cantor Set

Here is the key counterexample to "null means small." The **ternary Cantor set**
$`C \subset [0,1]` — obtained by repeatedly removing the open middle third — is
simultaneously:

 * **uncountable**, and
 * of Lebesgue **measure zero**.

Its uncountability follows from Cantor's theorem (it is in bijection with
$`\{0,1\}^{\mathbb{N}}`, so $`\aleph_0 < 2^{\aleph_0}`):

```
#check @ChapterConsciousnessNullMeasure.cantorSet_uncountable
```

Its null measure follows from self-similarity: $`C` is the disjoint union of two
scaled copies of itself, each by factor $`1/3`, so $`\mu(C) \le (2/3)\,\mu(C)`,
which (since $`\mu(C) < \infty`) forces $`\mu(C) = 0`:

```
#check @ChapterConsciousnessNullMeasure.cantorSet_volume_zero
```

# The Headline

Putting these together, there exists an **uncountable** subset of $`[0,1]` with
Lebesgue measure **zero**:

```
#check @ChapterConsciousnessNullMeasure.exists_uncountable_null_subset
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
there is **no uniform probability measure** that makes every point equally likely
(each point would have to be null, yet the whole space has measure one — and there is
no countably-additive way to spread mass uniformly over uncountably many points).
Worse, the "special" outcomes one might want to privilege (a particular observed
value, a particular observer) are null and **indistinguishable**, by the measure,
from every other point. Any prior on a continuous space is therefore necessarily
_informative_: it must break the symmetry that the (nonexistent) uniform measure
would have preserved. This is the rigorous content of the manuscript's slogan "there
are no non-informative priors," and it connects back to
{ref "max-entropy"}[the maximum-entropy chapter], where the uniform prior existed
precisely because the space was **finite**.
