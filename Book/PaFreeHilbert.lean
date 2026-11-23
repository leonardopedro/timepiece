import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Completeness without Peano Arithmetic" =>
%%%
tag := "pa-free-chapter"
%%%

# Orientation and Status

:::paragraph
This is the first chapter of the tour, and its foundation: the only place where
the *sample space* itself is built. Nothing from the rest of the book is
assumed beyond the Introduction.
:::

:::paragraph
The chapter runs: Kopperman's choice of language, the construction of the
completed space, the verified core — the
Riesz–Fischer characterization of completeness by absolutely convergent series —
the *verifiable* unselectability facts, the metamathematical interpretation that
is deliberately **not** claimed as a theorem, why this chapter replaces the
manuscript's P-versus-NP and Riemann-hypothesis chapters, and the tensor products
of decidable languages that the next chapter generalizes.
:::

:::paragraph
The verified core lives in `BookProof/ChapterRieszFischer` and
`BookProof/ChapterEll`; everything else in the chapter is the analysis of those
results and is labelled as such. The continuation is
{ref "solovay-tensor"}[the Solovay–Kopperman tensor product], which needs
precisely the tensor-product section at the end here.
:::

This chapter replaces the manuscript's chapters on _P versus NP_ and on the _Riemann
Hypothesis_. Those chapters both turned on a single metamathematical point, isolated
here in self-contained form: topological completeness and the decidability of
a specified logical theory are different properties. A completed Hilbert space
can support a restricted decidable language. The chapter distinguishes the
verified analytic construction from the still-needed formal account of that
language and its decision procedure.

# Kopperman and the Choice of Language

Kopperman's [1967 paper](https://doi.org/10.2307/2270770) studies Hilbert
systems using infinitary $`L_{\omega_1,\omega_1}` logic. The manuscript draws
from this a useful discipline: specify what the language can name and quantify
over, rather than treating every operation available in the ambient mathematics
as part of an effective query language.

Three distinctions matter. A Hilbert space is *complete* when its Cauchy
sequences converge. A logical theory is *complete* when it settles every
sentence of its language. It is *decidable* when a terminating algorithm decides
those sentences from finite codes. None of these definitions implies the other
two without further hypotheses.

Adding a named vector is not a general proof of undecidability. Any proposed
arithmetic encoding must specify the expanded language and exhibit its
interpretation of arithmetic. Likewise, first-order PA is subject to the
compactness theorem; Gödel incompleteness is not noncompactness. Claims about
compactness in an infinitary logic must be stated in that logic. We therefore
use “unselectability” as a restriction on permitted descriptions, rather than as
a theorem that every completed Hilbert-space theory is decidable.

The existing Kopperman chapter proves separability of the concrete substrate
and of the packaged models. Its header explicitly leaves full infinitary
syntax, semantics, completeness and compactness outside the formalized scope:

```
#check @kopperman_substrate_separable
#check @all_formalism_models_separable
```

Separability supplies countable dense approximants. An effective presentation
also needs a computable enumeration, coefficient operations and approximation
bounds. Existence of a countable dense subset alone supplies none of those
algorithms.

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

*Every vector in the chosen finite-support core has finite support.* This
follows from `Finsupp`. Effective computation also requires effective coefficients
and indices. The restriction is on this chosen representation: an infinite
vector can have a finite description, such as the square-summable sequence
$`(2^{-n})_{n\ge0}`. Finite description and finite support are different notions.

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

*Singletons are null under a diffuse prior.* Under a diffuse probability
measure, every particular vector has singleton probability zero, including a
vector with an explicit finite description. This is a property of the measure,
independent of logical definability:

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

This counts definitions in the fixed language. It establishes the existence
of undefinable elements; it does not prohibit all named infinite vectors.

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
  convergent series of core approximants (Riesz–Fischer). Core vectors have
  finite support. Under a diffuse prior, every singleton is a null event.
  Effective approximation of a specified completed vector needs further data.

  Additionally, a *bounded-arithmetic prior* on any finite type is a genuine
  probability measure, and its "certain extension" to known propositions is
  verified:

  ```
  #check @prior_is_probability
  #check @certainExtension_known
  ```

: Interpretation (metamathematics, not a Lean theorem)

  The proposed “conservative, decidable extension” is a claim about a specified
  formal language, its models and an effective interpretation. Restricting
  primitive constants is a design choice; further definability and conservativity
  arguments are needed to establish the claim.

This model-theoretic claim can itself be formulated and proved in Lean once its
syntax and semantics have been encoded. It has not been supplied by the analytic
completion proofs. Countability of definable elements shows that some elements
are undefinable relative to a fixed language; it does not make every infinite
vector undefinable or establish a decision procedure. The
{ref "proof-plans"}[appendix] separates these formalization tasks.

# Why This Replaces the Two Chapters

The manuscript's complexity and zeta discussions motivate a common question:
which finite descriptions and effective operations survive completion? The
analytic completion results provide a setting for that question. They do not
by themselves settle a complexity separation, a zeta claim, or the decidability
of an expanded language. The present foundation develops the reusable geometry
and specifies the additional logical work separately.

# Tensor Products and Finite Queries

For a detector with two channels, a state is a pair of amplitudes in the
completed Hilbert space $`K`. Asking for a unit state with a prescribed first
amplitude leaves one unknown vector, the second amplitude. Its squared norm
must supply the missing part of one. The
{ref "solovay-tensor"}[tensor-product chapter] works out this decision for a
Gaussian coordinate amplitude, starting from the uniform finite sphere.
With $`d` channels the same decomposition gives $`V\widehat\otimes K\cong K^d`.

## Products of Carriers and Tensors of Wave-Functions

The formal head–tail carrier is a product
$`\mathbb R^N\times\mathrm{Tail}`. `headSumEquiv` splits a finite coordinate
block; it is not itself a Hilbert tensor product:

```
#check @headSumEquiv
#check @coordinateStateMeasure
```

On the coordinate carrier the law is
$`\mu\otimes\gamma`, with arbitrary head law $`\mu` and product Gaussian
tail $`\gamma`. The associated wave-function space is
$`L^2(\mu)\widehat\otimes L^2(\gamma)` by the pure-tensor density results
in {ref "solovay-tensor"}[the next chapter]. A finite discrete head gives a
finite-dimensional first Hilbert factor; a finite number of continuous head
coordinates need not do so.

## The Formal Finite-Head Reduction

```
#check @tensor_language_decidable
```

This theorem states that inner products of head-only wave-functions reduce to
a head integral. Tensor products of such observables remain head-only. The
statement is an exact analytic reduction, not an algorithm deciding arbitrary
sentences or computing integrals against every head law. Boolean classifiers
also close under conjunction on pairs; that separate elementary fact does not
establish closure of arbitrary decidable theories under tensor constructions.

## Two Prior Constructions

```
#check @only_mehler_on_tail
#check @head_vs_tail_admissibility
```

These abstract-substrate theorems package probability, atomlessness and invariance
under transformations already assumed measure preserving. They assert no
uniqueness of the abstract prior. The explicit sequence-space model separately
has a product Gaussian law; `ChapterMehlerUniqueness` proves uniqueness among
laws with the same Gaussian finite marginals. A cylindrical language alone does
not force those marginals. The sphere scaling and the Gaussian model provide
them, and a measure-preserving bridge to a differently constructed substrate
prior would require its own proof.

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
$`\text{Fin}\,2 \times \mathbb{N} \simeq \mathbb{N}`). Together they
describe enlargement by independent Gaussian coordinates.
A head-only wave-function is extended constantly in the added variables, whose
probability integrates to one. Setting a new Gaussian variable to zero would
instead impose a null event:

```
#check @enlargeEquiv
```

## Invariance Under Finite Orthogonal Symmetries

The Mehler measure is invariant under any measure-preserving transformation of
the tail coordinates:

```
#check @mehler_invariant_under_finite_orthogonal
```

At the abstract certificate layer, “finite-orthogonal symmetry” is defined
through measure preservation. The coordinate Gaussian model separately proves
invariance under actual finite orthogonal rotations. Identifying this action
with a substrate action requires a bridge. Head-only queries ignore tail
coordinates; cylindrical queries may inspect a finite tail block, whose law
is unchanged by the stated rotations.

## Scope of the Tensor-Product Layer

The verified layer supplies analytic completion, finite-head reduction,
Gaussian splitting and the product-measure tensor structure. The intended
logical layer needs an encoded effective language and a sound, complete,
terminating decision procedure. These tasks complement the analytic proofs;
they are not consequences of refusing to name infinite constants.
