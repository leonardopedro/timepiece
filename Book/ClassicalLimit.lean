import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Ensemble Forecasting and the Classical Limit" =>
%%%
tag := "classical-limit"
%%%

# No Uniform Measure on a Countable Space

We begin with a negative fact that shapes everything below. There is *no uniform
probability measure on a countable space*: the rationals are not enough for
probability theory. The verified statements (module
`BookProof.ChapterNoUniformCountable`):

```
#check @ChapterNoUniformCountable.no_uniform_countable_measure
#check @ChapterNoUniformCountable.no_uniform_measure_nat
```

A standard probability space — which mixes a countable part and a continuous part —
is therefore *irreducible*: it cannot be replaced by a countable model carrying a
uniform measure. This is the measure-theoretic reason the wave-function
parametrization lives on a genuine continuum.

# Ensemble Forecasting: Many Models as One

The rules for updating a probability measure are not obvious, because one can always
consider a *probability space of probability spaces* — an ensemble of statistical
models, which the manuscript calls *ensemble forecasting*. Assuming a quantum
(linear) time-evolution for the ensemble imposes essentially no restriction on the
time-evolution of the individual models, which may still be non-linear.

Using the free-field parametrization, one can *diagonalize* the quantum
time-evolution, decomposing a non-linear infinite-dimensional model into a direct
integral of *linear models with a single Boolean variable*. A direct integral can
still be uncomputable, so the next step is to decompose a continuous spectrum into a
direct *sum* of small energy intervals, each described by *few variables*. The
manuscript presents this as a mathematical definition of *renormalization*: for
reasonable initial conditions (we never have access to an infinite range of energies
in a real experiment) one can predict the time-evolution using a model with few
variables, using different unrelated models for different energy ranges.

The key conceptual point: the wave-function defines an *ensemble of deterministic
transformations* (functions). When few variables are relevant, each such function
can be studied and computed individually. This is why deterministic logic and
deterministic mathematics find application in a world full of uncomputable functions
— not because the functions are computable, but because the _relevant_ ones, in a
given energy range, are.

# The Classical Limit: When Probabilities Become Calculable

When can one discard probabilities in coordinate space and recover classical
mechanics? The manuscript's answer is deliberately non-rigorous — it often works,
but not always, so *classical mechanics is never enough at any energy scale; quantum
mechanics is always needed*. The mechanism is the density of calculable functions.

Step functions, polynomials, and smooth functions are *dense* in the $`L^2`
measure: any bounded function on a compact domain can be approximated, in the
average over that domain, by calculable functions. The verified density theorems
(module `BookProof.ChapterClassicalLimit`):

```
#check @ChapterClassicalLimit.simpleFunc_dense_L2
#check @ChapterClassicalLimit.continuousMap_denseRange_L2
#check @ChapterClassicalLimit.polynomial_denseRange_L2
#check @ChapterClassicalLimit.exists_polynomial_approx_L2
```

Reading them: simple (step) functions are dense in $`L^2`; continuous functions are
dense; polynomial functions are dense; and concretely, every $`L^2` function admits
a polynomial approximation within any prescribed $`\varepsilon > 0`.

The crucial caveat: approximating a function *in the average over a compact domain*
does not make the function itself calculable. In macroscopic phenomena one usually
_does_ average over a large domain (partitioning it for a numerical approximation),
so calculable functions suffice. In *microscopic* phenomena — the double-slit
experiment is the example — opening one slit or two makes a macroscopic difference,
and averaging destroys exactly the effect one wants. There, only the
*probabilities* admit calculable $`L^2` approximations, not the underlying
function. Chaos and finite-time singularities of ODEs are phenomena of _computable_
functions (computable for a small finite time); genuinely uncomputable functions are
uncomputable for _any_ finite time.

# Markov Processes Are Monotone in Entropy

Finally, the structural reason a Markov process cannot produce an arbitrary function
of time: there is an *ordering*, related to entropy, with respect to which all
continuous-time Markov processes are monotone. A doubly stochastic (Markov) map
*increases* entropy, while a mere permutation of outcomes preserves it. The
verified statements (module `BookProof.ChapterMarkovEntropy`):

```
#check @ChapterMarkovEntropy.entropy_applyMarkov_ge
#check @ChapterMarkovEntropy.permMatrix_doublyStochastic
#check @ChapterMarkovEntropy.entropy_applyMarkov_permMatrix
```

Reading them: applying a doubly stochastic matrix to a distribution does not
decrease its entropy; a permutation matrix is doubly stochastic; and a permutation
leaves the entropy *unchanged*. This is the precise sense in which Bayesian
inference (a Markov process) is *irreversible*, and why the reversible unitary
models of this book are a genuine generalization of it: a unitary evolution can be
non-deterministic without being entropy-increasing in the Markov sense.

# Summary

 * There is no uniform measure on a countable space; the standard (countable +
   continuous) probability space is irreducible.
 * Ensemble forecasting + the free-field parametrization decompose a non-linear
   infinite-dimensional model into linear models with few variables — a mathematical
   definition of renormalization, and the reason deterministic mathematics applies to
   a world of uncomputable functions.
 * The classical limit rests on the $`L^2`-density of step, continuous, and
   polynomial functions: calculable on average over a compact domain, but not
   pointwise — which is why microscopic phenomena still need probabilities.
 * Markov processes are monotone in entropy (doubly stochastic maps increase it,
   permutations preserve it), so they are irreversible; unitary evolution
   generalizes them.
