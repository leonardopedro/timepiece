import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Measurements Reproduce the Distribution" =>
%%%
tag := "measurement-lln"
%%%

# Frequencies Converge to Probabilities

A probability distribution makes a testable promise: if you repeat an experiment
many times, the *relative frequency* of each outcome converges to its probability.
This is the *law of large numbers*, and it is the bridge between the abstract
measure of Part I and the empirical content of the whole programme. The manuscript
relies on it in its discussion of *ensemble forecasting* (§10): repeated
measurements reproduce the probability distribution in the infinite-measurement
limit.

# The Setup

Model a sequence of measurements as functions
$`M_i : \Omega \to \{0,\dots,k-1\}` on a probability space $`(\Omega, \mu)`, each
returning one of $`k` outcomes. For an outcome $`a`, the *indicator*
$`\mathbf{1}_{M_i = a}` is the random variable that is $`1` when the $`i`-th
measurement yields $`a` and $`0` otherwise. Its expectation is exactly the
probability of $`a`:

$$`\int_\Omega \mathbf{1}_{M_i = a}\, d\mu = \mu(M_i = a).`

```
#check @ChapterMeasurementLLN.outcomeIndicator_integral
```

# The Frequency Converges

The empirical *frequency* of outcome $`a` in the first $`N` measurements is the
average of the indicators,

$$`f_N(a) = \frac{1}{N}\sum_{i < N} \mathbf{1}_{M_i = a},`

and the law of large numbers says it converges (in the appropriate sense) to the
probability $`\mu(M_i = a)`:

```
#check @ChapterMeasurementLLN.measurement_frequency_tendsto
```

More generally, the empirical average of *any* bounded function $`f` of the
outcome converges to its expectation:

```
#check @ChapterMeasurementLLN.measurement_average_tendsto
```

# Connection to the Variance Decomposition

This is where {ref "total-variance"}[the law of total variance] pays off. Recall the
decomposition $`\mathrm{Var}[Y] = \mathrm{within} + \mathrm{between}`. The
*epistemic* (between-group) part of the uncertainty is precisely what repeated
measurement reduces: as the number of measurements grows, the empirical frequency
concentrates around the true probability, and the variance of the estimator shrinks.
The *aleatoric* (within-group) part — the irreducible randomness of each individual
outcome — does not disappear; it is what the limiting distribution still describes.

So the law of large numbers and the law of total variance are two views of the same
story: the former says the empirical distribution converges to the true one, and the
latter quantifies how the residual uncertainty splits into a part that averaging
removes and a part it cannot.

# Why This Closes the Loop

The Born-rule parametrization of Part II assigns probabilities
$`p_k = |\psi_k|^2` to outcomes. The law of large numbers is the operational
meaning of those numbers: they are exactly the limiting relative frequencies of
repeated preparation-and-measurement. A wave-function is therefore not a mysterious
object; it is a *parametrization of the long-run statistics* of an experiment, and
{ref "born-reproduces"}[the surjectivity of the Born map] says that every conceivable
set of long-run statistics is reachable by some wave-function. The probabilistic
foundation of Part I, the wave-function parametrization of Part II, and the
frequentist interpretation meet here.
