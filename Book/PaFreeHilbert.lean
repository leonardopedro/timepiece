import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Completeness without Peano Arithmetic" =>
%%%
tag := "pa-free-chapter"
%%%

This chapter replaces the manuscript's chapters on _P versus NP_ and on the _Riemann
Hypothesis_. Those chapters both turned on a single metamathematical point, isolated
here in self-contained form: a completed Hilbert space can be *topologically
complete* and yet *decidable*, provided its infinite elements are kept
_internally unselectable_. The chapter is careful to separate what is a verified
theorem of analysis from what is a metamathematical interpretation.

# Kopperman's Warning

In Section V of his 1967 paper, Kopperman proved a striking negative result about
the logic of Hilbert spaces:

"If even one constant $`c_0` is added to the language of Hilbert systems, the new theory is no longer compact. This results from the fact that it is possible to introduce a predicate into the language which is satisfied by only a single complex number."

The mechanism is important. A *named constant vector* $`c_0` lets you write a
first-order formula that isolates a specific complex number. From one named complex
number you can reconstruct the integers; from the integers you get *Peano
Arithmetic (PA)*; and PA is undecidable and non-compact (by Gödel's theorem). So the
moment you add a single infinite constant to the language, the clean decidable
geometry is contaminated by undecidable arithmetic.

The goal is therefore to have a *complete* Hilbert space — one that contains its
limits — *without* adding any infinite element to the language as a primitive
constant. The space should be complete _ontologically_ (its limits exist) but
_epistemologically unselectable_ (no infinite element can be named).

The verified formalization of Kopperman's setting confirms that the substrate
Hilbert space is *separable* (has a countable dense subset), which is the
topological precondition for his model-theoretic analysis:

```
#check @kopperman_substrate_separable
#check @all_formalism_models_separable
```

# The Construction

The construction has three layers.

: The dense, decidable core

  Start with the *finitely-supported* vectors
  $`\mathcal{H}_0 = P \to_0 \mathbb{R}_{\mathrm{alg}}` (a `Finsupp`). Every vector in
  $`\mathcal{H}_0` has *finite support* by definition, so its representation is
  strictly finite and decidable. There is no infinite object here at all.

: The metric completion

  Define the completed Hilbert space $`\mathcal{H}` as the *metric completion* of
  $`\mathcal{H}_0`: Cauchy sequences of finite vectors, modulo the equivalence
  relation of converging to the same limit. This is a standard, purely topological
  construction; it adds limit points without naming any of them.

: Existence of elements = absolute convergence

  By the Banach-space characterization below, every element of the completion
  corresponds to an *absolutely convergent series* of finite vectors. So the
  infinite elements exist (as equivalence classes of Cauchy sequences / convergent
  series) but are never introduced as primitive constants.

# The Verified Core: Riesz–Fischer / Banach by Summable Series

The mathematical engine of the whole argument is a genuine, verified theorem of
functional analysis, present in Mathlib as `completeSpace_iff_summable_norm`:

*A normed space $`E` is complete (a Banach space) if and only if every absolutely convergent series in $`E` converges.*

This is the standard tool for proving that $`L^p` spaces are complete, and it is the
fact that lets the completion be characterized by convergent series of finite
vectors. The Mathlib statement:

```
#check @completeSpace_iff_summable_norm
```

and the completeness of the metric completion itself:

```
#check @UniformSpace.Completion.completeSpace
```

# Sketch Proof of the Characterization

Because this theorem is the verified core, it is worth seeing the proof in full.

*($`\Rightarrow`) Complete $`\Rightarrow` absolutely convergent series converge.*
Let $`\sum_{n} u_n` be absolutely convergent, $`\sum_n \|u_n\| < \infty`, and let
$`s_N = \sum_{n < N} u_n` be the partial sums. For $`M > N`, the triangle inequality
gives

$$`\|s_M - s_N\| = \Big\|\sum_{N \le n < M} u_n\Big\| \le \sum_{N \le n < M} \|u_n\|.`

Since the real series $`\sum \|u_n\|` converges, its partial sums are Cauchy, so the
right-hand side is $`< \varepsilon` for all large $`N`. Hence $`(s_N)` is Cauchy in
$`E`, and completeness makes it converge.

*($`\Leftarrow`) Absolutely convergent $`\Rightarrow` complete.* Let $`(x_n)` be a
Cauchy sequence. Choose a subsequence $`x_{k(j)}` with
$`\|x_p - x_q\| < 2^{-(j+2)}` for all $`p,q \ge k(j)`, and set

$$`u_0 = x_{k(0)}, \qquad u_j = x_{k(j)} - x_{k(j-1)} \;\;(j \ge 1).`

The partial sums *telescope* to the subsequence:
$`u_0 + \sum_{j=1}^{M} u_j = x_{k(M)}`. And the series is absolutely convergent,
because

$$`\sum_j \|u_j\| \le \|x_{k(0)}\| + \sum_{j\ge 1} 2^{-j} = \|x_{k(0)}\| + 1 < \infty.`

By hypothesis the series converges to some $`x`, so the subsequence
$`x_{k(M)} \to x`; and a Cauchy sequence with a convergent subsequence converges to
the same limit. Hence $`E` is complete. $`\blacksquare`

# The Verifiable "Unselectability" Facts

Two pieces of the safety argument are themselves ordinary, verifiable mathematics.

*Every writable vector has finite support.* This is immediate from the definition
of `Finsupp`: a term of type $`P \to_0 \mathbb{R}` carries an explicit finite
support, so anything you can actually write down is finitely supported and decidable.

```
#check @Finsupp.finite_support
```

*The completion adds exactly the limit points, and nothing else.* This is the
Riesz–Fischer half of the construction, now proved rather than asserted: the
sequence space $`\ell^2(\mathbb{N})` is complete; every one of its vectors is the
norm-limit of its finitely-supported truncations; the image of the writable core
$`\mathbb{N} \to_0 \mathbb{R}` is *exactly* the set of finitely-supported vectors;
and that image is a *proper* subset, so the completion is not a vacuous
operation.

```
#check @riesz_fischer
#check @range_ofCore
#check @denseCore_dense
#check @denseCore_proper
#check @completion_conservative_over_core
```

The Riesz–Fischer facts themselves live in `BookProof.ChapterRieszFischer`: the
completeness of $`\ell^2(\mathbb{N})` (`ell2_completeSpace`), the unconditional
sum representation of every vector (`riesz_fischer_hasSum`), and the properness
witness that the completion genuinely adds elements — the geometric vector
$`n \mapsto 2^{-n}` is square-summable but has infinite support:

```
#check @BookProof.ChapterRieszFischer.ell2_completeSpace
#check @BookProof.ChapterRieszFischer.riesz_fischer_hasSum
#check @BookProof.ChapterRieszFischer.finSupport_dense
#check @BookProof.ChapterRieszFischer.finSupport_ne_univ
#check @BookProof.ChapterRieszFischer.geomVec_not_mem_finSupport
#check @BookProof.ChapterRieszFischer.core_proper_and_dense
```

*Infinite elements are null events under a diffuse prior.* Since the infinite
elements cannot be named as constants, the manuscript represents them as measurable
sets under a diffuse probability prior. Under any *diffuse* measure (every
singleton has measure zero), any particular infinite vector — being a single point of
the completed space — has probability zero:

```
#check @MeasureTheory.Measure.noAtoms
```

This is the measure-theoretic form of "the infinite elements are unselectable": no
single one of them can be picked out with positive probability.

*Only countably many elements are definable.* A countable formal language can
name only countably many reals, so *most* reals — and hence most elements of the
completed space — are not definable in the base language:

```
#check @definable_reals_countable
#check @exists_nondefinable_real
```

This is the definability-theoretic form of unselectability: the elements that
Kopperman's trap would need to isolate simply cannot be named.

Moreover the completed space $`\ell^2(\mathbb{N})` is *separable* — a countable
language suffices to name a *dense* fragment of it. The finitely-supported
*rational* vectors form a countable set (`ratVec_range_countable`) which is still
dense (`ratVec_dense`), so the whole completion is the closure of a countable set
of nameable vectors:

```
#check @BookProof.ChapterEll2Separable.ratVec_range_countable
#check @BookProof.ChapterEll2Separable.ratVec_dense
#check @BookProof.ChapterEll2Separable.ell2_separable
```

# The Metamathematical Interpretation (Not a Theorem)

We must now be precise about what has and has not been proved.

: Proved (verified mathematics)

  The completion $`\mathcal{H}` is a complete space; its elements are absolutely
  convergent series of finite vectors (Riesz–Fischer). Every _writable_ vector is
  finitely supported and decidable. Under a diffuse prior, individual infinite
  elements are null events.

  Additionally, a *bounded-arithmetic prior* on any finite type is a genuine
  probability measure, and its "certain extension" to known propositions is
  verified:

  ```
  #check @prior_is_probability
  #check @certainExtension_known
  ```

: Interpretation (metamathematics, not a Lean theorem)

  The claim that "the completed space *does not leak Peano Arithmetic*" / "is a
  *conservative, decidable extension* of the base theories" is a statement about
  *formal languages and definability*, not an internal statement of analysis. It
  says: because we never add an infinite element as a primitive constant, no
  first-order formula of the base language can isolate one, so Kopperman's
  reconstruction of the integers never gets started.

This interpretation is mathematically reasonable and is exactly the point the
manuscript's _P vs NP_ and _Riemann Hypothesis_ chapters were making, but it is
*not* a single theorem that Lean can state and prove inside the theory. Making it
fully rigorous would require formalizing a notion of "definable constant in the base
language" and proving a conservativity / non-definability result about the
completion — a model-theoretic task well beyond the verified analysis above. We
record what _is_ formalizable in the proof-plan appendix and flag the rest as
interpretation.

# Why This Replaces the Two Chapters

Both replaced chapters relied on the same maneuver: an apparently undecidable or
intractable object (the complexity of a decision problem; the zeros of the zeta
function) is represented not as a *named infinite constant* but as a *limit /
expectation over a measure space* — an element of a completion that exists
ontologically but is kept unselectable, so that Kopperman's trap never springs. The
verified content is always the same analytic fact, the Riesz–Fischer characterization
of completeness by absolutely convergent series; the rest is the disciplined refusal
to add the infinite object to the language as a constant.

# Tensor Products of Decidable Languages

The construction above gives a single decidable language. The manuscript's quantum
chapters require *composing* two such languages — the tensor product of two
Hilbert spaces — and the question is whether decidability survives composition.

## Head ⊗ Tail Decomposition

Every state in the Solovay–Kopperman space decomposes as a *finite head* (the
first $`N` coordinates, carrying the observable content) tensored with an
*infinite tail* (the remaining coordinates, carrying the measure-theoretic
substrate). The verified equivalence:

```
#check @headSumEquiv
```

splits $`\mathbb{R}^{N_1 + N_2} \times \text{Tail}` into
$`\mathbb{R}^{N_1} \times (\mathbb{R}^{N_2} \times \text{Tail})`, showing that
tensoring two finite heads simply concatenates their coordinates while the tail
is shared. The state measure respects this:

```
#check @coordinateStateMeasure
```

takes an *arbitrary* probability distribution on the finite head and pairs it
with the fixed Mehler (Gaussian) measure on the tail.

## Decidability is Preserved

The central theorem: if two observables each depend only on their respective
finite heads, then their tensor product depends only on the concatenated head,
and the expectation over the product state is decidable.

```
#check @tensor_language_decidable
```

This is the formal content of "the tensor product of two decidable languages is
decidable": the infinite tail never needs to be inspected to compute any
observable expectation.

## The Tail Admits the Mehler Measure

While the head carries an arbitrary probability law, the tail is rigid. The
verified theorem:

```
#check @only_mehler_on_tail
```

states that the Mehler (standard Gaussian product) measure is an admissible prior
on the tail: it is a probability measure, atomless (no singleton is distinguishable),
and invariant under every measure-preserving transformation of the tail. These three
properties are the admissibility criteria; the theorem confirms the Mehler prior
satisfies all of them. (Full uniqueness — that no other measure can satisfy them — is
not asserted; the formal docstring explicitly disclaims it.) The contrast with the
head is made explicit:

```
#check @head_vs_tail_admissibility
```

Any probability distribution whatsoever is admissible on the finite head; the
Mehler measure is the canonical admissible prior on the infinite tail.

## Cross-Dimensional Inner Products

A subtle point: the Solovay inner product of two states with *different*
finite-part dimensions is well-defined, because the uniform Mehler measure on
the tail *splits* so that the finite coordinates match. The coordinate-level
realization:

```
#check @tailSplitEquiv
```

is a measure-preserving equivalence that peels off the first $`k` coordinates
from the tail, and:

```
#check @tailTensorEquiv
```

identifies the product of two tails with a single tail (via a bijection
$`\text{Fin}\,2 \times \mathbb{N} \simeq \mathbb{N}`). Together they show that
padding a state with extra zero coordinates does not change its measure class:

```
#check @enlargeEquiv
```

## Invariance Under Finite Orthogonal Symmetries

The Mehler measure is invariant under any measure-preserving transformation of
the tail coordinates:

```
#check @mehler_invariant_under_finite_orthogonal
```

At the current certificate layer, "finite-orthogonal symmetry" is defined as
measure-preservation of the tail prior, so this theorem confirms the interface is
consistent (the conclusion is exactly the hypothesis). A coordinate-level
finite-rank orthogonal group on the substrate is future work; the physical content
— no finite rotation of the unselectable tail can be detected by any observable,
because observables depend only on the finite head — is captured by the
head-only decidability predicate.

## Summary of the Tensor-Product Layer

: Verified (Lean theorems)

  Head–tail decomposition (`headSumEquiv`); tensor closure and decidability
  (`tensor_language_decidable`); admissibility of the Mehler tail prior
  (`only_mehler_on_tail`); head/tail asymmetry (`head_vs_tail_admissibility`);
  coordinate splitting (`tailSplitEquiv`, `tailTensorEquiv`); enlargement
  invariance (`enlargeEquiv`); measure-preserving invariance
  (`mehler_invariant_under_finite_orthogonal`).

: Structural consequence (metamathematical)

  Because every observable in the tensor-product language still depends only on
  a finite head, Kopperman's trap never springs: no infinite constant is ever
  named, and the completed tensor-product space remains a conservative,
  decidable extension of the base theories.
