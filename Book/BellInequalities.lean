import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The Bell Inequalities" =>
%%%
tag := "bell-inequalities"
%%%

# What the Inequality Bounds

The CHSH inequality is a constraint that any *local* theory must satisfy. Two
parties, Alice and Bob, each choose one of two measurements, labelled
$`a_0, a_1` and $`b_0, b_1`, each returning a value $`\pm 1`. The CHSH combination is

$$`S = a_0 b_0 + a_0 b_1 + a_1 b_0 - a_1 b_1.`

If the outcomes are determined by a shared local hidden variable — that is, if each
of $`a_0, a_1, b_0, b_1` is a definite number $`\pm 1` before measurement — then a
pointwise algebraic bound gives $`|S| \le 2`. The verified pointwise bound and its
expectation-value form (module `BookProof.ChapterBell`):

```
#check @ChapterBell.chsh_pointwise
#check @ChapterBell.chsh_local
```

The first is the elementary fact that for any four numbers $`\pm 1` the combination
$`S` lies in $`[-2, 2]`; the second lifts it to the *local bound* on the
expectation value, $`\langle S \rangle \le 2`, for any local (hidden-variable)
model.

# Quantum Mechanics Violates It

Quantum mechanics does not assign definite values to all four measurements at once.
Take two qubits in the *Bell state* and the Pauli observables

$$`A_0 = \sigma_z, \quad A_1 = \sigma_x, \quad B_0 = \frac{\sigma_z + \sigma_x}{\sqrt 2}, \quad B_1 = \frac{\sigma_z - \sigma_x}{\sqrt 2}.`

The expectation of the CHSH operator in the Bell state is then $`2\sqrt 2`, which
exceeds the local bound $`2`. The verified statements (module
`BookProof.ChapterBell`):

```
#check @ChapterBell.chsh_quantum_value
#check @ChapterBell.chsh_quantum_violates_local_bound
```

The first computes the quantum value $`\langle S \rangle = 2\sqrt 2` exactly; the
second is the bare inequality $`2 < 2\sqrt 2` that records the violation.

# The Tsirelson Bound

The value $`2\sqrt 2` is not arbitrary: it is the *maximum* quantum violation, the
*Tsirelson bound*. The verified statements (module `BookProof.ChapterTsirelson`):

```
#check @ChapterTsirelson.chshTuple_isCHSHTuple
#check @ChapterTsirelson.tsirelson_value_eq
#check @ChapterTsirelson.tsirelson_bound_tight
```

The first checks that the four observables above form a valid CHSH tuple (self-adjoint
involutions with Alice's observables commuting with Bob's); the second records the
identity $`2\sqrt 2 = (\sqrt 2)^3`; the third proves the bound is *tight*: the
Bell state is an eigenvector of the CHSH operator with eigenvalue $`2\sqrt 2`, so
this concrete tuple saturates the Tsirelson bound. (The universal upper bound — no
quantum state can exceed $`2\sqrt 2` — is Mathlib's `tsirelson_inequality`.) So
quantum mechanics sits strictly between the local bound $`2` and the algebraic
maximum $`4`, at exactly $`2\sqrt 2`.

# The Manuscript's Reading

The standard reading is that the Bell violation rules out *local hidden-variable*
theories. The manuscript offers a more specific reading, tied to
{ref "time-translation-stochastic"}[the stochastic-process theorem]: the Bell
assumptions implicitly treat the time-evolution as a *stochastic process* — a
probability distribution at each time, glued by conditionals. But that theorem shows
the time-evolution is a stochastic process *if and only if it is deterministic*.

On this reading, what the Bell inequalities actually distinguish is quantum
mechanics from a theory whose time-evolution _is_ a stochastic process — not from
"any complete statistical theory." A complete statistical theory whose time-evolution
is non-deterministic does not define a probability distribution at each intermediate
time, so it need not satisfy the Bell assumptions. The inequalities are
mathematically valid; the question is whether their assumptions are physically
mandatory. The manuscript's claim is that they are not — that they encode the
extra, optional assumption that the evolution is a stochastic process.

This is a *interpretive* claim about the physical meaning of the Bell assumptions;
the machine-verified content is the mathematics above: the local bound $`2`, the
quantum value $`2\sqrt 2`, and the tight Tsirelson bound.

# Summary

 * Any local hidden-variable model satisfies the CHSH bound $`\langle S \rangle \le 2`
   (a pointwise algebraic fact).
 * Quantum mechanics, with the Bell state and Pauli observables, achieves
   $`2\sqrt 2 > 2`.
 * $`2\sqrt 2` is the *Tsirelson bound*: the tight quantum maximum.
 * The manuscript reads the violation as distinguishing quantum mechanics from
   theories whose time-evolution is a stochastic process — an interpretation built
   on the theorem that such an evolution is stochastic iff deterministic.
