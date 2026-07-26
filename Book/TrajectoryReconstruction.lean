import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Reconstructing the Trajectory" =>
%%%
tag := "trajectory-reconstruction"
%%%

# The Question

:::paragraph
A quantum trajectory can be measured directly only at its **final** time. The
manuscript asks whether the intermediate instants can nevertheless be recovered. The
answer is **post-selection**: "using probabilities conditional on the final state and
the same quantum time-evolution," we can "repeat the experiment in the same conditions
and predict the results of a measurement at another time between the initial and final
times." The trajectory is reconstructed at intermediate instants from the statistics
of runs that ended in a chosen final outcome. This is the
Aharonov–Bergmann–Lebowitz (two-state) reconstruction.
:::

# The Three-Instant Collapsed Process

:::paragraph
Model three instants — initial, intermediate, final — on a finite phase space. A unit
initial wave-function $`\Psi` is evolved by a unitary $`U` to the intermediate time,
where a measurement in the standard basis yields outcome $`a` with the Born
probability and **collapses** the state to $`e_a`:
:::

```
#check @midProb
```

:::paragraph
The collapsed state is then evolved by a unitary $`V` to the final time, where outcome
$`f` occurs with probability
:::

```
#check @transProb
```

:::paragraph
Both are genuine probabilities — non-negative, and each sums to one over its outcomes:
:::

```
#check @midProb_nonneg
#check @midProb_sum
#check @transProb_sum
```

# The Joint and Marginal Laws

:::paragraph
The joint law of the intermediate outcome $`a` and the final outcome $`f` is the
product of the two Born factors:
:::

```
#check @jointProb
```

:::paragraph
Summing over the intermediate outcome gives the marginal law of the final outcome:
:::

```
#check @finalProb
```

:::paragraph
The collapsed three-instant process is a genuine probability law: the marginal final
probabilities sum to one. This uses only the unitarity of $`U` and $`V` and the
normalization $`\|\Psi\| = 1`:
:::

```
#check @finalProb_total
```

# Post-Selection: the Reconstruction Formula

:::paragraph
Now condition on the final outcome $`f`. The **post-selected** law of the intermediate
outcome — the probability that the trajectory passed through $`a`, given that it ended
at $`f` — is the conditional probability
:::

$$`\mathrm{condProb}(f, a) = \frac{\mathrm{jointProb}(f, a)}{\mathrm{finalProb}(f)}.`

```
#check @condProb
#check @condProb_nonneg
```

:::paragraph
For each fixed final outcome $`f`, this is again a probability distribution over the
intermediate outcomes:
:::

```
#check @condProb_sum
```

:::paragraph
This is the reconstruction: although $`a` was not recorded, its conditional
distribution is determined by the final outcome and the same unitary evolution, and it
is a honest probability law.
:::

# Consistency of the Reconstruction

:::paragraph
The reconstruction does not depend on which final outcome one post-selects. Summing
the post-selected joint law over **all** final outcomes recovers the original
intermediate Born distribution:
:::

```
#check @jointProb_sum_final_eq_midProb
```

:::paragraph
So the intermediate statistics are stable: marginalizing the reconstructed joint law
back over the final outcomes returns exactly the Born probabilities one would have
measured directly at the intermediate time. The post-selection adds information about
individual runs without distorting the ensemble.
:::

# The Double-Slit Instance

:::paragraph
The worked example is the double-slit experiment, where the intermediate "which slit"
measurement and the final screen position are related by Hadamard evolutions; the
post-selected law reproduces the interference pattern. That concrete computation is
carried out in {ref "double-slit"}[the double-slit chapter].
:::

# Why This Matters Here

:::paragraph
Trajectory reconstruction is the constructive face of two ideas already in the book.
It is why {ref "time-translation-stochastic"}[time-translation is a stochastic
process if and only if it is deterministic]: the off-diagonal Born terms vanish, and
the conditional laws are well-defined, exactly in the deterministic case. And it is
the probabilistic content of "selecting events is not rewriting history": conditioning
on a final outcome selects a sub-ensemble without altering the underlying measure —
the marginal consistency theorem above is precisely that statement in finite form.
:::
