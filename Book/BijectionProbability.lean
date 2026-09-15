import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "A Random Map Is Almost Surely Non-Invertible" =>
%%%
tag := "bijection-probability"
%%%

# Counting Maps and Bijections

The previous chapter showed that an irreversible deterministic dynamics is an
injective-but-not-surjective self-map, possible only on an infinite state space. A
natural quantitative question, raised directly in the manuscript, is: if you pick a
"discrete function" at random, how likely is it to be invertible at all?

Model a discrete function on an $`n`-cell partition as an arbitrary map
$`\mathrm{Fin}\, n \to \mathrm{Fin}\, n`. There are

$$`n^n`

such maps (each of the $`n` inputs chooses one of $`n` outputs independently), and
exactly

$$`n!`

of them are bijections (the permutations). The verified counts:

```
#check @ChapterBijectionProbability.card_fun_fin
#check @ChapterBijectionProbability.card_bijective_fin
```

# The Probability of Invertibility

The probability that a uniformly random map is invertible is therefore the ratio

$$`\mathrm{bijProb}(n) = \frac{n!}{n^n}.`

```
#check @ChapterBijectionProbability.bijProb_eq_card_ratio
```

This probability is tiny and gets tinier. The elementary bound
$`(n+1)! \le (n+1)^n` gives $`\mathrm{bijProb}(n) \le 1/n`, and in fact:

```
#check @ChapterBijectionProbability.bijProb_le_one_div
#check @ChapterBijectionProbability.bijProb_tendsto_zero
```

So the probability of invertibility *converges to zero* as the partition is
refined. A random discrete dynamics is, with overwhelming probability,
*non-invertible* — i.e. irreversible in the sense of the previous chapter.

# The Sharp Asymptotic: Stirling

The manuscript quotes the precise rate. By *Stirling's formula*
$`n! \sim \sqrt{2\pi n}\,(n/e)^n`,

$$`\mathrm{bijProb}(n) = \frac{n!}{n^n} \sim \sqrt{2\pi n}\, e^{-n}.`

The verified asymptotic equivalence:

```
#check @ChapterBijectionProbability.bijProb_isEquivalent_stirling
```

The decay is *exponential* in $`n` (the $`\sqrt{2\pi n}` prefactor is negligible
next to $`e^{-n}`). Invertibility is not merely unlikely; it is
_exponentially_ unlikely.

# Why This Matters

Combine this with {ref "irreversibility"}[the previous chapter]. There we saw that
irreversibility is _possible_ only on a continuum and _impossible_ on a finite set.
Here we see the complementary statistical fact: as a finite approximation is refined
($`n \to \infty`), the fraction of dynamics that are invertible collapses to zero
exponentially. So in the continuum limit, *almost every* deterministic dynamics is
irreversible. The arrow of time is not a special, fine-tuned feature of particular
systems; it is the *generic* case, and reversible (bijective) dynamics is the
measure-zero exception. This is the rigorous backbone of the manuscript's claim that
an irreversible deterministic time-evolution is the rule, not the accident.
