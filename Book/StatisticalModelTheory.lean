import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Statistical Model Theory, and Statements as Operators" => %%%
tag := "statistical-model-theory"
%%%

This chapter formalizes the model-theoretic content of the manuscript's closing
chapter, *Statistical Model Theory and Bayesian priors where the Riemann
Hypothesis is true* — everything of it except the Riemann-hypothesis prior, which
stays out of scope by construction. It has two halves that answer one question
from opposite sides. The first asks what a *theory* can pin down: over a countable
language, first-order axioms never select a single uncountable structure, while
second-order axioms can. The second asks what a *statement* is when the models it
talks about form a Hilbert space: an orthogonal projection, with a truth value
that is a number rather than a bit.

Both halves are `sorry`-free and `axiom`-free, in
`BookProof/ChapterStatisticalModelTheory.lean` and
`BookProof/ChapterStatementOperator.lean`. They are the only chapters of the
manuscript's closing section with a counterpart in the proof library, and they
deliberately stop at the boundary the manuscript itself draws: no infinitary
$`L_{\omega_1\omega_1}` logic, no Abstraction Logic, no completeness claim for
either, and no Bayesian prior on the Möbius function.

# What First-Order Logic Cannot Do

:::paragraph
The chapter opens with the upward Löwenheim–Skolem theorem, and it is worth
seeing why that theorem is the engine of everything below. If a first-order
theory has an infinite model, it has models of *every* infinite cardinality large
enough for the language (`upward_lowenheim_skolem`); in particular a theory with
an infinite model has an uncountable one (`exists_uncountable_model`), and over a
countable language it has one of cardinality exactly the continuum
(`exists_uncountable_model_of_countable_language`) — the "monster" model
(`monster_model_continuum`) that model theorists reason with.

The negative consequence is the one the manuscript quotes as a slogan: *you cannot
filter out the uncountable models using first-order axioms*
(`countability_not_first_order_axiomatizable`). Whatever countable first-order
axioms you write, if they have an infinite model at all they have uncountable
ones, and pairwise non-isomorphic ones (`exists_nonisomorphic_models`) — which is
exactly why Presburger arithmetic, for instance, has non-standard models
(`exists_nonstandard_model`) rather than being pinned down to $`\mathbb{N}`.
Every countable model of a countable theory is embeddable
(`exists_countable_model`), and no uncountable model is bijective with a
countable one under those hypotheses
(`exists_model_not_bijective_of_uncountable`).

The contrast that gives the section its point is the second-order case:
`secondOrder_categoricity_real` states that every conditionally complete linear
ordered field is order-ring-isomorphic to $`\mathbb{R}`, uniquely — the
second-order completeness axiom *is* categorical where the first-order scheme is
not. The two results together are the manuscript's contrast between the two
logics made precise: first-order axioms over a countable language never pin down
an uncountable structure, while a second-order axiom can.
:::

```
#check @BookProof.ChapterStatisticalModelTheory.upward_lowenheim_skolem
#check @BookProof.ChapterStatisticalModelTheory.exists_uncountable_model
#check @BookProof.ChapterStatisticalModelTheory.monster_model_continuum
#check @BookProof.ChapterStatisticalModelTheory.exists_uncountable_model_of_countable_language
#check @BookProof.ChapterStatisticalModelTheory.countability_not_first_order_axiomatizable
#check @BookProof.ChapterStatisticalModelTheory.exists_nonisomorphic_models
#check @BookProof.ChapterStatisticalModelTheory.exists_nonstandard_model
#check @BookProof.ChapterStatisticalModelTheory.exists_countable_model
#check @BookProof.ChapterStatisticalModelTheory.exists_model_not_bijective_of_uncountable
#check @BookProof.ChapterStatisticalModelTheory.secondOrder_categoricity_real
```

# Statements as Operators in a Hilbert Space

:::paragraph
The second half implements the chapter's other image: *statements become operators
in a Hilbert space*. A `ModelStatement` is an orthogonal projection — a bounded,
self-adjoint, idempotent operator `S.op` on the Hilbert space of models — and its
**truth value** on a model vector $`\psi` is $`\operatorname{Re}\langle\psi, S\psi\rangle`,
a real number in $`[0, \lVert\psi\rangle^2]`
(`truthValue_nonneg`, `truthValue_le_norm_sq`, `truthValue_mem_unitInterval`).
The extreme cases are identified exactly: the value vanishes precisely on the
models in the kernel (`truthValue_eq_zero_iff`) and reaches the norm squared
precisely on the range (`truthValue_eq_norm_sq_iff`). So "true", "false" and
"undecidable" are no longer three colors of a bit but positions of a spectrum —
which is what the manuscript means by statements becoming "more than
true/false/undecidable".

The propositional calculus is then the operator calculus: negation is
$`1 - S` with `truthValue_not` making the values complementary, and conjunction
of two *commuting* statements is the composition of their projections, with
`truthValue_and_le_left` and `truthValue_and_le_right` the monotonicity the
reader expects. An **undecidable** statement is precisely a projection with a
proper nonzero range (`Undecidable`, `undecidable_iff`). The chapter then steps
outside projections: `UncertainStatement` is the book's "operators but not
projections", with `halfUncertain_not_idempotent` as the witness that a
half-true statement is not idempotent, and `approximate_proof_error` bounds how
well an operator within $`\varepsilon` of a statement evaluates every model:
$`|\langle A\rangle - \langle P\rangle| \le \lVert A - P\rVert\cdot\lVert\psi\rVert^2`,
the "approximated proof" of the manuscript.
:::

```
#check @BookProof.ChapterStatementOperator.ModelStatement
#check @BookProof.ChapterStatementOperator.ModelStatement.truthValue
#check @BookProof.ChapterStatementOperator.ModelStatement.truthValue_nonneg
#check @BookProof.ChapterStatementOperator.ModelStatement.truthValue_mem_unitInterval
#check @BookProof.ChapterStatementOperator.ModelStatement.truthValue_eq_zero_iff
#check @BookProof.ChapterStatementOperator.ModelStatement.truthValue_eq_norm_sq_iff
#check @BookProof.ChapterStatementOperator.ModelStatement.not
#check @BookProof.ChapterStatementOperator.ModelStatement.truthValue_not
#check @BookProof.ChapterStatementOperator.ModelStatement.and
#check @BookProof.ChapterStatementOperator.ModelStatement.truthValue_and_le_left
#check @BookProof.ChapterStatementOperator.ModelStatement.Undecidable
#check @BookProof.ChapterStatementOperator.ModelStatement.undecidable_iff
#check @BookProof.ChapterStatementOperator.UncertainStatement
#check @BookProof.ChapterStatementOperator.halfUncertain_not_idempotent
#check @BookProof.ChapterStatementOperator.approximate_proof_error
```

:::paragraph
**Honest boundary.** Nothing above is claimed about infinitary
$`L_{\omega_1\omega_1}` logic, about Abstraction Logic, or about the completeness
of either; and nothing is claimed about the Bayesian prior on the Möbius
function, which is the part of the manuscript's closing chapter this chapter
does not touch. The projection model of a statement is a *model* — it formalizes
the chapter's image, not a thesis about the foundations of mathematics.
:::

# Summary

:::paragraph
* `upward_lowenheim_skolem`, `monster_model_continuum`,
  `countability_not_first_order_axiomatizable` — first-order theories with an
  infinite model have models of every sufficiently large cardinality, so
  countability is not first-order axiomatizable.
* `exists_nonisomorphic_models`, `exists_nonstandard_model` — the non-uniqueness
  that Presburger arithmetic's non-standard models exemplify.
* `secondOrder_categoricity_real` — the second-order completeness axiom is
  categorical: $`\mathbb{R}` is unique up to order-ring isomorphism.
* `ModelStatement.truthValue`, `truthValue_not`, `truthValue_and_le_left` —
  statements as projections, with truth values in $`[0, \lVert\psi\rVert^2]` and
  the propositional calculus as the operator calculus.
* `undecidable_iff`, `halfUncertain_not_idempotent`,
  `approximate_proof_error` — undecidability as a proper nonzero range,
  uncertainty as non-idempotence, and the error bound of an approximated proof.
* open: infinitary and Abstraction Logic, their completeness, and the Bayesian
  prior on the Möbius function — out of scope by construction.
:::
