import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean


#doc (Manual) "Maximum Entropy Selects the Uniform Prior" =>
%%%
tag := "max-entropy"
%%%

# Measuring Ignorance

:::paragraph
The previous chapter singled out the uniform prior as the unique
_relabeling-invariant_ one. There is a second, independent route to the same
destination, due to Jaynes: the uniform prior is the distribution that
*maximizes the Shannon entropy*. Within a fixed parametrization this is the prior
that assumes the least — but, as we stress at the end, "least" is measured relative
to the chosen coordinates, and the conclusion is no more objective than the
parametrization it rests on.
:::

:::paragraph
For a probability distribution $`p` on a finite non-empty space $`\alpha` with
$`n = |\alpha|` outcomes, the *entropy* is
:::

$$`H(p) = \sum_{i} -p_i \log p_i,`

:::paragraph
with the convention $`0 \log 0 = 0`. Entropy measures spread: it is small when the
distribution is concentrated on a few outcomes and large when the mass is spread
out. The claim we prove is:
:::

:::paragraph
*Among all distributions on $`n` outcomes, the uniform distribution $`u_i = 1/n` uniquely maximizes the entropy, and the maximum value is $`\log n`.*
:::

:::paragraph
This is the *maximum-entropy principle*: _relative to a fixed set of labeled
outcomes_, if the only thing you know is the set of possibilities, the prior with
the largest entropy is the uniform one, and any other prior assumes extra
information beyond the labeling. The italicized clause is essential. Entropy is
computed against the counting measure on the chosen labels; change the
parametrization and a different prior becomes the maximum-entropy one. The principle
selects the uniform prior within a coordinate system — it does not certify the
uniform prior as objectively non-informative.
:::

# Sketch Proof (Gibbs' Inequality)

:::paragraph
The whole argument rests on the elementary bound $`\log t \le t - 1` for
$`t > 0`, with equality only at $`t = 1`. Apply it with
$`t = 1/(n\,p_i)`:
:::

$$`-\log(n\,p_i) \le \frac{1}{n\,p_i} - 1.`

:::paragraph
Multiplying by $`p_i \ge 0` and rearranging gives the *pointwise Gibbs bound*
:::

$$`-p_i \log p_i \;-\; p_i \log n \;\le\; \frac{1}{n} - p_i.`

:::paragraph
Now sum over all $`i`. The left-hand side becomes $`H(p) - \log n \sum_i p_i =
H(p) - \log n`. The right-hand side becomes $`\sum_i \frac{1}{n} - \sum_i p_i =
1 - 1 = 0`, because there are $`n` terms each equal to $`1/n` and
$`\sum_i p_i = 1`. Therefore
:::

$$`H(p) - \log n \le 0, \qquad\text{i.e.}\qquad H(p) \le \log n.`

:::paragraph
For the uniform distribution $`u_i = 1/n` one computes directly
$`H(u) = \sum_i -\tfrac{1}{n}\log\tfrac{1}{n} = \log n`, so the bound is attained.
:::

:::paragraph
Finally, equality in $`H(p) \le \log n` requires equality in $`\log t \le t - 1`
for *every* $`i`, which forces $`1/(n p_i) = 1`, i.e. $`p_i = 1/n`, for every
$`i`. So the uniform distribution is the *unique* maximizer.
:::

# The Verified Statement

:::paragraph
The maximum-entropy bound and its sharpness are proved in
`BookProof.ChapterMaxEntropy`. The headline is that every distribution has entropy
at most that of the uniform one:
:::

```
#check @ChapterMaxEntropy.entropy_le_entropy_uniform
```

:::paragraph
The stronger statement, that equality holds *only* for the uniform distribution:
:::

```
#check @ChapterMaxEntropy.entropy_eq_log_card_iff
```

:::paragraph
and the supporting facts — the bound $`H(p) \le \log n`, the value
$`H(u) = \log n`, and the non-negativity of entropy:
:::

```
#check @ChapterMaxEntropy.entropy_le_log_card
#check @ChapterMaxEntropy.entropy_uniform
#check @ChapterMaxEntropy.entropy_nonneg
```

:::paragraph
The pointwise Gibbs bound that drives the proof is itself verified:
:::

```
#check @ChapterMaxEntropy.negMulLog_sub_le
```

# Two Roads, One Prior — Both Within a Parametrization

:::paragraph
We now have two independent characterizations of the uniform prior: it is the unique
_relabeling-invariant_ distribution ({ref "sequential-bayes"}[previous chapter]) and
the unique _maximum-entropy_ distribution. That a symmetry principle and an
optimization principle agree makes the uniform prior a natural default *within a
fixed parametrization*. It is not evidence that the uniform prior is objectively
"the" non-informative prior. Both characterizations are parametrization-dependent:
relabeling-invariance privileges a labeling, and entropy privileges the counting
measure on that labeling, and {ref "sequential-bayes"}[the previous chapter] showed
that any non-null finite prior can be reparametrized into the uniform one — which
then becomes the maximum-entropy prior in the new coordinates.
:::

:::paragraph
The source manuscript leans on the uniform prior as a convenient default while
insisting it is never objectively forced. Citing Eaton and Freedman
({ref "dutch-book"}[Dutch book against some 'objective' priors]), it holds that
"there is no prior which is better for all cases" and that "there are no
non-informative priors in Bayesian inference." On a _continuous_ space the point is
sharper still: there is in general *no* non-informative prior at all
({ref "null-measure"}[Null-measure sets need not be small]). The maximum-entropy
principle is a rule for choosing a prior once coordinates are fixed — not a proof
that any prior, uniform or otherwise, is written into the problem.
:::
