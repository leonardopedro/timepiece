import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The Law of Total Variance" =>
%%%
tag := "total-variance"
%%%

# Two Kinds of Uncertainty

When a model makes a prediction, its error has two conceptually distinct sources:

 * **Aleatoric uncertainty** — the noise _inside_ the data-generating process,
   which no amount of extra information about the model would remove.
 * **Epistemic uncertainty** — the ignorance about _which_ model (or which group,
   or which ensemble member) generated the data.

The source manuscript frames this distinction in the language of **ensemble
forecasting**: a forecast is a _probability distribution over probability
distributions_, and its total spread combines the variability _within_ each member
with the variability _between_ members.

The exact mathematical statement underlying this picture is the **law of total
variance**: the total variance of a quantity splits, with no remainder, into a
within-group part and a between-group part.

# The Setup

Take a finite sample space $`\Omega` with non-negative weights
$`w : \Omega \to \mathbb{R}` (think of a probability distribution, though the
algebraic identity needs only non-negativity), a real-valued quantity
$`Y : \Omega \to \mathbb{R}`, and a **grouping** $`X : \Omega \to \kappa` that
assigns each outcome to one of finitely many groups. Define:

 * the **mean** $`\mathbb{E}[Y] = \sum_\omega w_\omega\, Y_\omega`;
 * the **total variance** $`\mathrm{Var}[Y] = \sum_\omega w_\omega\,(Y_\omega - \mathbb{E}[Y])^2`;
 * the **conditional mean** in group $`g`, $`\mu_g = \mathbb{E}[Y \mid X = g]`;
 * the **within-group variance** $`\mathrm{within} = \mathbb{E}[\mathrm{Var}(Y \mid X)]`,
   the average of the variances inside each group;
 * the **between-group variance** $`\mathrm{between} = \mathrm{Var}(\mathbb{E}[Y \mid X])`,
   the variance of the group means.

The claim is the clean identity

$$`\mathrm{Var}[Y] \;=\; \underbrace{\mathbb{E}[\mathrm{Var}(Y\mid X)]}_{\text{within (aleatoric)}} \;+\; \underbrace{\mathrm{Var}(\mathbb{E}[Y\mid X])}_{\text{between (epistemic)}}.`

# Sketch Proof (Pythagoras for Conditional Expectation)

The proof is a single orthogonal decomposition. Write each value as

$$`Y_\omega - \mathbb{E}[Y] = \underbrace{(Y_\omega - \mu_{X(\omega)})}_{\text{residual within its group}} + \underbrace{(\mu_{X(\omega)} - \mathbb{E}[Y])}_{\text{group mean vs.\ overall mean}}.`

Square and sum with weights $`w_\omega`. The two squared terms give exactly
$`\mathrm{within}` and $`\mathrm{between}`. The only thing to check is that the
**cross term vanishes**:

$$`2\sum_\omega w_\omega\,(Y_\omega - \mu_{X(\omega)})\,(\mu_{X(\omega)} - \mathbb{E}[Y]) = 0.`

Factor out the group-level quantity $`(\mu_g - \mathbb{E}[Y])`, which is constant
within group $`g`. What remains in each group is
$`\sum_{\omega : X(\omega)=g} w_\omega\,(Y_\omega - \mu_g)`, which is **zero by the
definition of the conditional mean** $`\mu_g` as the $`w`-weighted average of
$`Y` over the group. This is the **balance** (orthogonality) property of conditional
expectation: the residuals sum to zero within every group. With the cross term gone,
the identity follows.

Geometrically, conditional expectation is an orthogonal projection, and the law of
total variance is the Pythagorean theorem for that projection.

# The Verified Statement

The decomposition and its ingredients are proved in `BookProof.ChapterTotalVariance`.
The headline identity:

```
#check @ChapterTotalVariance.total_variance
```

The two facts that make the cross term disappear — the within-group balance of the
residuals, and the resulting vanishing of the cross term:

```
#check @ChapterTotalVariance.groupBalance
#check @ChapterTotalVariance.crossTerm_zero
```

Because both summands are non-negative, each is bounded by the total variance — a
fact the manuscript uses to control epistemic error:

```
#check @ChapterTotalVariance.within_nonneg
#check @ChapterTotalVariance.between_nonneg
#check @ChapterTotalVariance.within_le_variance
#check @ChapterTotalVariance.between_le_variance
```

# Reading the Decomposition

The identity is an _equality_, not an inequality: there is no leftover term. If a
prediction is uncertain, the law tells you precisely how much of that uncertainty
would disappear if you learned the group $`X` (the between-group part) and how much
is irreducible noise (the within-group part). This is the quantitative backbone of
the manuscript's discussion of **systematic uncertainties as Bayesian priors** and
of **ensemble forecasting**, and it reappears in
{ref "measurement-lln"}[the law of large numbers] when we ask how repeated
measurement reduces the epistemic part.
