import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Completeness without Peano Arithmetic" =>
%%%
tag := "pa-free-chapter"
%%%

This chapter replaces the manuscript's chapters on _P versus NP_ and on the _Riemann
Hypothesis_. Those chapters both turned on a single metamathematical point, isolated
here in self-contained form: a completed Hilbert space can be **topologically
complete** and yet **decidable**, provided its infinite elements are kept
_internally unselectable_. The chapter is careful to separate what is a verified
theorem of analysis from what is a metamathematical interpretation.

# Kopperman's Warning

In Section V of his 1967 paper, Kopperman proved a striking negative result about
the logic of Hilbert spaces:

"If even one constant $`c_0` is added to the language of Hilbert systems, the new theory is no longer compact. This results from the fact that it is possible to introduce a predicate into the language which is satisfied by only a single complex number."

The mechanism is important. A **named constant vector** $`c_0` lets you write a
first-order formula that isolates a specific complex number. From one named complex
number you can reconstruct the integers; from the integers you get **Peano
Arithmetic (PA)**; and PA is undecidable and non-compact (by Gödel's theorem). So the
moment you add a single infinite constant to the language, the clean decidable
geometry is contaminated by undecidable arithmetic.

The goal is therefore to have a **complete** Hilbert space — one that contains its
limits — **without** adding any infinite element to the language as a primitive
constant. The space should be complete _ontologically_ (its limits exist) but
_epistemologically unselectable_ (no infinite element can be named).

# The Construction

The construction has three layers.

: The dense, decidable core

  Start with the **finitely-supported** vectors
  $`\mathcal{H}_0 = P \to_0 \mathbb{R}_{\mathrm{alg}}` (a `Finsupp`). Every vector in
  $`\mathcal{H}_0` has **finite support** by definition, so its representation is
  strictly finite and decidable. There is no infinite object here at all.

: The metric completion

  Define the completed Hilbert space $`\mathcal{H}` as the **metric completion** of
  $`\mathcal{H}_0`: Cauchy sequences of finite vectors, modulo the equivalence
  relation of converging to the same limit. This is a standard, purely topological
  construction; it adds limit points without naming any of them.

: Existence of elements = absolute convergence

  By the Banach-space characterization below, every element of the completion
  corresponds to an **absolutely convergent series** of finite vectors. So the
  infinite elements exist (as equivalence classes of Cauchy sequences / convergent
  series) but are never introduced as primitive constants.

# The Verified Core: Riesz–Fischer / Banach by Summable Series

The mathematical engine of the whole argument is a genuine, verified theorem of
functional analysis, present in Mathlib as `completeSpace_iff_summable_norm`:

**A normed space $`E` is complete (a Banach space) if and only if every absolutely convergent series in $`E` converges.**

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

**($`\Rightarrow`) Complete $`\Rightarrow` absolutely convergent series converge.**
Let $`\sum_{n} u_n` be absolutely convergent, $`\sum_n \|u_n\| < \infty`, and let
$`s_N = \sum_{n < N} u_n` be the partial sums. For $`M > N`, the triangle inequality
gives

$$`\|s_M - s_N\| = \Big\|\sum_{N \le n < M} u_n\Big\| \le \sum_{N \le n < M} \|u_n\|.`

Since the real series $`\sum \|u_n\|` converges, its partial sums are Cauchy, so the
right-hand side is $`< \varepsilon` for all large $`N`. Hence $`(s_N)` is Cauchy in
$`E`, and completeness makes it converge.

**($`\Leftarrow`) Absolutely convergent $`\Rightarrow` complete.** Let $`(x_n)` be a
Cauchy sequence. Choose a subsequence $`x_{k(j)}` with
$`\|x_p - x_q\| < 2^{-(j+2)}` for all $`p,q \ge k(j)`, and set

$$`u_0 = x_{k(0)}, \qquad u_j = x_{k(j)} - x_{k(j-1)} \;\;(j \ge 1).`

The partial sums **telescope** to the subsequence:
$`u_0 + \sum_{j=1}^{M} u_j = x_{k(M)}`. And the series is absolutely convergent,
because

$$`\sum_j \|u_j\| \le \|x_{k(0)}\| + \sum_{j\ge 1} 2^{-j} = \|x_{k(0)}\| + 1 < \infty.`

By hypothesis the series converges to some $`x`, so the subsequence
$`x_{k(M)} \to x`; and a Cauchy sequence with a convergent subsequence converges to
the same limit. Hence $`E` is complete. $`\blacksquare`

# The Verifiable "Unselectability" Facts

Two pieces of the safety argument are themselves ordinary, verifiable mathematics.

**Every writable vector has finite support.** This is immediate from the definition
of `Finsupp`: a term of type $`P \to_0 \mathbb{R}` carries an explicit finite
support, so anything you can actually write down is finitely supported and decidable.

```
#check @Finsupp.finite_support
```

**Infinite elements are null events under a diffuse prior.** Since the infinite
elements cannot be named as constants, the manuscript represents them as measurable
sets under a diffuse probability prior. Under any **diffuse** measure (every
singleton has measure zero), any particular infinite vector — being a single point of
the completed space — has probability zero:

```
#check @MeasureTheory.Measure.noAtoms
```

This is the measure-theoretic form of "the infinite elements are unselectable": no
single one of them can be picked out with positive probability.

# The Metamathematical Interpretation (Not a Theorem)

We must now be precise about what has and has not been proved.

: Proved (verified mathematics)

  The completion $`\mathcal{H}` is a complete space; its elements are absolutely
  convergent series of finite vectors (Riesz–Fischer). Every _writable_ vector is
  finitely supported and decidable. Under a diffuse prior, individual infinite
  elements are null events.

: Interpretation (metamathematics, not a Lean theorem)

  The claim that "the completed space **does not leak Peano Arithmetic**" / "is a
  **conservative, decidable extension** of the base theories" is a statement about
  **formal languages and definability**, not an internal statement of analysis. It
  says: because we never add an infinite element as a primitive constant, no
  first-order formula of the base language can isolate one, so Kopperman's
  reconstruction of the integers never gets started.

This interpretation is mathematically reasonable and is exactly the point the
manuscript's _P vs NP_ and _Riemann Hypothesis_ chapters were making, but it is
**not** a single theorem that Lean can state and prove inside the theory. Making it
fully rigorous would require formalizing a notion of "definable constant in the base
language" and proving a conservativity / non-definability result about the
completion — a model-theoretic task well beyond the verified analysis above. We
record what _is_ formalizable in the proof-plan appendix and flag the rest as
interpretation.

# Why This Replaces the Two Chapters

Both replaced chapters relied on the same maneuver: an apparently undecidable or
intractable object (the complexity of a decision problem; the zeros of the zeta
function) is represented not as a **named infinite constant** but as a **limit /
expectation over a measure space** — an element of a completion that exists
ontologically but is kept unselectable, so that Kopperman's trap never springs. The
verified content is always the same analytic fact, the Riesz–Fischer characterization
of completeness by absolutely convergent series; the rest is the disciplined refusal
to add the infinite object to the language as a constant.
