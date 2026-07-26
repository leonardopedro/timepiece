import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The Solovay–Kopperman Tensor Product" =>
%%%
tag := "solovay-tensor"
%%%

# The Question

:::paragraph
The Introduction posed a concrete open problem. Engineering needs a probability
space over real functions of real variables, but:
:::

:::paragraph
"no one has found yet a systematic way to define a separable probability space with
an arbitrary probability measure over real functions of real variables (and
infinite-dimensional spaces in general)."
:::

:::paragraph
The difficulty is the infinite-dimensional part. A separable space is one whose
elements can be approximated by a countable set; a non-separable space has elements
that "cannot be approximated by a finite set of elements, up to an arbitrarily small
error" — and then they cannot be distinguished, named, or computed. So we want a
space that is infinite-dimensional (to carry a field, or a trajectory, or a
wave-function) yet still separable (so its elements remain approximable), and on
which we may still choose a probability measure.
:::

:::paragraph
The manuscript also repeatedly forms **tensor products of sample spaces**. A joint
probability density lives on a product $`X \times Y`; the prior wave-function can be
"redefined as a tensor product of two Fock-spaces"; and often "we are interested in a
tensor product of sample spaces, some of which have finite degrees of freedom," for
instance $`\mathbb{Z}_2^n \times \mathbb{R}^m`. The construction below answers the
Introduction's problem precisely by building such a tensor product: a
**finite-dimensional** factor that carries an **arbitrary** probability law, tensored
with a **separable infinite-dimensional** factor that carries a **forced** law.
:::

# The Two Factors

:::paragraph
The total sample space splits as a finite **head** times an infinite **tail**:
:::

```
#check @InnerSpace
#check @InnerHead
#check @InnerTail
```

:::paragraph
The head $`\mathrm{InnerHead}\,N = \mathrm{Fin}\,N \to \mathbb{R} \cong \mathbb{R}^N`
is an ordinary finite-dimensional Euclidean Hilbert space. The tail
$`\mathrm{InnerTail}` is the Kopperman **substrate**, the standard separable real
Hilbert space $`L^2([0,1])`. Its separability is the topological precondition for
everything that follows, and it is verified directly:
:::

```
#check @kopperman_substrate_separable
#check @substrate_decidable_skeleton
```

:::paragraph
Thus the tail is infinite-dimensional but **separable**: it possesses a countable
dense skeleton of computable approximants. This is exactly the property the
Introduction asked for. The finite head is the part we _know_; the separable infinite
tail is the part we are _uncertain_ about.
:::

# Decidable Languages Close Under Tensor Product

:::paragraph
A **language** here is an explicit Boolean decision procedure: a classifier
$`\mathrm{decide} : \alpha \to \mathrm{Bool}`. The tensor product of two languages is
conjunction on pairs — a point of the product carrier is accepted exactly when both
components accept it:
:::

```
#check @tensor_decide_apply
```

:::paragraph
Because a conjunction of two decidable propositions is decidable, membership in the
tensor language is decidable for every point of the product carrier:
:::

```
#check @tensor_language_membership_decidable
```

:::paragraph
This is the first half of the author's goal: **the tensor product of two decidable
languages is a decidable language.** The same closure holds for the
Hilbert-space languages used in this book. The "cylindrical" observables — those that
depend only on the finite head — form a decidable language, because the head is
finite-dimensional and hence Tarski-decidable. A tensor product of two such
finite-head observables is again a finite-head observable on the combined head:
:::

```
#check @tensorHeadObservable_dependsOnlyOnHead
#check @tensor_language_decidable
```

:::paragraph
The combined head is split into its two finite blocks by an explicit equivalence, so
"tensor product of languages" and "concatenation of finite heads" are the same
operation:
:::

```
#check @headSumEquiv
```

# The Tensor-Product Hilbert Space

:::paragraph
The tensor product of the two factors is the total space
$`\mathrm{InnerSpace}\,N = \mathrm{InnerHead}\,N \times \mathrm{InnerTail}`, and its
Hilbert completion is the **Solovay–Hilbert space**:
:::

```
#check @SolovayHilbertSpace
```

:::paragraph
The infinite tail itself tensors with a copy of itself back into a single tail: two
infinite Gaussian coordinate sequences interleave into one, and the product Mehler
law is carried exactly to the Mehler law. This is the measure-theoretic content of
$`\Gamma \otimes \Gamma \cong \Gamma` for the infinite factor:
:::

```
#check @tailTensorEquiv
#check @tailTensorEquiv_map
```

:::paragraph
The embedding of a wave-function into the completed space preserves the inner
product, so the completion is a genuine Hilbert-space tensor product rather than a
mere product of sets:
:::

```
#check @toSolovay_inner
```

:::paragraph
The decisive simplification is the **decoupling theorem**: because the cylindrical
wave-functions depend only on the finite head, and the tail measure is an independent
probability measure, the $`L^2` inner product over the infinite-dimensional total
space collapses exactly to a finite-dimensional integral over the head
$`\mathbb{R}^N`:
:::

```
#check @inner_reduces_to_head
```

:::paragraph
This is the dimensional reduction that makes the whole construction _decidable_: an
a-priori infinite-dimensional computation reduces to a finite Tarski-decidable
integral. It is the formal version of the manuscript's claim that probabilities let
us relate arbitrarily complex random events to standard, intuitive ones.
:::

# An Arbitrary Law on the Finite Part

:::paragraph
On the finite head we may choose **any** probability law. Given any probability
measure $`\mathrm{headDist}` on $`\mathbb{R}^N`, the product with the tail law is a
probability measure on the total space, and its finite marginal is exactly the law we
chose:
:::

```
#check @stateMeasure_isProbability
#check @stateMeasure_finite_marginal
```

:::paragraph
The same statement in the explicit coordinate model, where the tail is a countable
product of standard Gaussians:
:::

```
#check @coordinateStateMeasure
#check @coordinateStateMeasure_isProbability
```

:::paragraph
This is the finite-dimensional freedom the author wants: **our knowledge of the
finite-dimensional part is an arbitrary probability distribution.** Nothing
constrains it; it is the part we are free to choose.
:::

# Only the Mehler Measure on the Infinite Part

:::paragraph
The infinite tail is different. The Kopperman language is **cylindrical**: it can
query only finitely many coordinates at a time. Consequently it cannot distinguish
two tail points that agree on every finite set of coordinates — no individual element
of the infinite-dimensional Hilbert space can be named or singled out. (This is the
same mechanism as {ref "pa-free-chapter"}[Completeness without Peano Arithmetic]:
adding a named infinite element to the language would destroy decidability.)
:::

:::paragraph
A probability law on the tail that respects this blindness must be **atomless** (no
single state carries mass) and **invariant** under the symmetries the language can
express. The selected Mehler/Kopperman prior has precisely these admissibility
properties:
:::

```
#check @TailPriorAdmissible
#check @only_mehler_on_tail
```

:::paragraph
Concretely, the tail prior is atomless, and it is invariant under every admitted
finite orthogonal symmetry:
:::

```
#check @tailMeasure_singleton
#check @mehler_invariant_under_finite_orthogonal
```

:::paragraph
And it really lives on the infinite-dimensional sphere: the normalized empirical
squared norm of the first $`k` coordinates converges to $`1` almost surely
(Poincaré–Borel / the strong law), which is Mehler's 1866 limit of the uniform
measure on the high-dimensional sphere:
:::

```
#check @mehler_concentrates_on_unit_sphere
```

:::paragraph
In the coordinate model the forcing is explicit. The language sees only finite
coordinate sets, and restriction to any finite set has the corresponding finite
product Gaussian law:
:::

```
#check @finiteCoordinateMarginal
```

:::paragraph
So the only data the language can observe is the family of finite-dimensional
marginals, and a probability measure on $`\mathbb{N} \to \mathbb{R}` is determined by
its finite marginals. The intended conclusion — that the Mehler measure is the
_unique_ probability law whose every finite marginal is the standard Gaussian product,
and hence the **only** law the blind language can use — is stated as the next target
in {ref "proof-plans"}[the appendix] (`mehler_unique_by_finite_marginals`). The
verified content above is the admissibility half: the Mehler law is probability,
atomless, and invariant. The two halves together give the author's classification:
:::

```
#check @head_vs_tail_admissibility
```

:::paragraph
**Heads admit an arbitrary law; the tail admits the Mehler law.** That single
statement is the probabilistic content of the Solovay–Kopperman tensor product.
:::

# The Cross-Dimensional Inner Product

:::paragraph
Because the Mehler tail **splits** — the first $`k` Gaussian coordinates separate off
as an independent finite Gaussian block, leaving a fresh copy of the tail — we may
enlarge the finite head by adjoining $`k` tail coordinates:
:::

```
#check @tailSplitEquiv
#check @enlargeEquiv
```

:::paragraph
This makes the inner product well-defined **across dimensions**: an element with
$`N` head-coordinates and an element with $`N+k` head-coordinates can be compared
after padding the smaller one with $`k` fresh Gaussian coordinates, and the result
does not depend on the padding, because the added coordinates integrate to $`1`. The
finite dimensions "match" precisely because the Mehler measure is a product. The
measure-preservation of this enlargement (the theorem that the padding leaves the
state law unchanged) is the in-progress companion to the tail-split above; see
{ref "proof-plans"}[the appendix].
:::

# What Is Proved and What Is Planned

:::paragraph
This edition separates the verified layer from the open one.
:::

:::paragraph
**Verified.** The two factors and their separability; closure of decidable languages
under tensor product; the tensor-product Hilbert space and the decoupling theorem;
the arbitrary finite-head law and its marginal; the admissibility of the Mehler tail
(probability, atomlessness, invariance, concentration on the sphere); and the
self-interleaving of the infinite tail. Every theorem cited above is `sorry`-free.
:::

:::paragraph
**Planned.** Two statements are made precise and quarantined in
{ref "proof-plans"}[the appendix]: the **uniqueness** of the Mehler tail law from its
finite marginals (`mehler_unique_by_finite_marginals`, the forcing half of "only the
Mehler measure"), and the **measure-preservation** of the coordinate tail-split
(`tailSplitEquiv_map`) from which the cross-dimensional inner product follows. They
are the content of the next formalization pass, not assertions of this edition.
:::

# Why This Matters Here

:::paragraph
The construction answers the Introduction directly: it is a systematic separable
probability space carrying an arbitrary law on a finite part and a controlled
(forced) law on an infinite part. It also explains the recurring tensor products of
the manuscript — a joint density on $`X \times Y`, a prior as a tensor product of two
Fock-spaces, a sample space $`\mathbb{Z}_2^n \times \mathbb{R}^m` — as instances of a
single principle: tensor a finite, freely-chosen factor with a separable infinite
factor whose law is forced by the very fact that the language cannot distinguish its
elements. Probability on the infinite part is not a choice; it is the Mehler measure.
:::
