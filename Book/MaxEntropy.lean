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
**maximizes the Shannon entropy**, and so it is the prior that assumes the least.
:::

:::paragraph
For a probability distribution $`p` on a finite non-empty space $`\alpha` with
$`n = |\alpha|` outcomes, the **entropy** is
:::

$$`H(p) = \sum_{i} -p_i \log p_i,`

:::paragraph
with the convention $`0 \log 0 = 0`. Entropy measures spread: it is small when the
distribution is concentrated on a few outcomes and large when the mass is spread
out. The claim we prove is:
:::

:::paragraph
**Among all distributions on $`n` outcomes, the uniform distribution $`u_i = 1/n` uniquely maximizes the entropy, and the maximum value is $`\log n`.**
:::

:::paragraph
This is the **maximum-entropy principle**: if the only thing you know about a
system is the set of possibilities, the honest prior is the one with the largest
entropy, namely the uniform one. Any other prior is secretly assuming extra
information that you do not have.
:::

# Sketch Proof (Gibbs' Inequality)

:::paragraph
The whole argument rests on the elementary bound $`\log t \le t - 1` for
$`t > 0`, with equality only at $`t = 1`. Apply it with
$`t = 1/(n\,p_i)`:
:::

$$`-\log(n\,p_i) \le \frac{1}{n\,p_i} - 1.`

:::paragraph
Multiplying by $`p_i \ge 0` and rearranging gives the **pointwise Gibbs bound**
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
for **every** $`i`, which forces $`1/(n p_i) = 1`, i.e. $`p_i = 1/n`, for every
$`i`. So the uniform distribution is the **unique** maximizer.
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
The stronger statement, that equality holds **only** for the uniform distribution:
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

# Two Roads, One Prior

:::paragraph
We now have two independent characterizations of the uniform prior: it is the unique
_relabeling-invariant_ distribution ({ref "sequential-bayes"}[previous chapter]) and
the unique _maximum-entropy_ distribution. That two such different principles — a
symmetry principle and an optimization principle — agree is strong evidence that the
uniform prior is the correct formalization of "assuming nothing." The source
manuscript leans on this repeatedly, while also cautioning (in its discussion of
consciousness and priors) that on a _continuous_ space there is in general **no**
non-informative prior at all — a subtlety we meet again in
{ref "null-measure"}[Null-measure sets need not be small].
:::
