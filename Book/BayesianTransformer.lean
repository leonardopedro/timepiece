import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Dimension-Robust Bayesian Adaptation: Hyperspherical nGPT Geometry and SG-pCNL" =>
%%%
tag := "bayesian-transformer"
%%%

# Orientation and Status

This chapter reads the `BayesianTransformer/` development pedagogically: a
formalization of *Dimension-Robust Bayesian Adaptation of Transformers via
Hyperspherical Geometry and Unadjusted SG-pCNL* (Milestones 1–5), imported into
this repository on 2026-10-21 from the specialist's export. The tree is a Lean
library in its own right (Lake target `BayesianTransformer`, namespace
`BayesianTransformer`), *not* a `BookProof/` chapter: it has not been compiled
in this snapshot, and step 0 of the specialist work order in
`CONSOLIDATED_PLAN.md` is its name-level check.

:::paragraph
In the tour this chapter is the *learned-systems* face of the same thesis the
{ref "aligned-deep-learning"}[aligned-deep-learning] and
{ref "coherent-state-attention"}[coherent-state-attention] chapters state in
other registers: a system you train is a system you put a prior on. What is new
here is that the architecture itself — normalized embeddings, cosine attention,
geodesic residuals — is designed so that the *geometry* does the statistical
work: every weight lives on a sphere, every logit is clamped, and every
stochastic-gradient step stays in a ball of radius $`\sigma\sqrt{P}`. The proofs
below are the exact content of those three sentences.
:::

:::paragraph
The sibling import `math28/` (Lake target `Math28`) is unrelated in subject —
named hypotheses transcribed from the `math/OAI` snapshot, with proved bridges
into this repository's chapters — and is not discussed here.
:::

# Scale Invariance and the Sphere

The foundational observation (`Analysis/ScaleInvariance.lean`) is that
normalization makes the loss *blind to radius*: if $`\Phi` is scale-invariant
(`IsScaleInvariant`) then its gradient is orthogonal to the position
(`scaleInvariant_gradient_orthogonal`, `scaleInvariant_inner_grad_zero`). The
radial direction carries no information, so a gradient flow on the sphere is
not a restriction of the flow — it *is* the flow, up to the discarded radial
gauge.

`Analysis/SphereProj.lean` makes the projection onto the unit sphere a
differentiable map with sharp constants: `norm_sphereProj` (the image is on the
sphere), `sphereProj_hasFDerivAt` and `sphereProj_deriv_opNorm_le` (its
derivative is the tangent-space projection, with a $`1/\|v\|` bound that blows up
exactly at the origin), and `sphereProj_smul_pos` (the map is homogeneous of
degree zero — the invariance again, now as a identity).

# Cosine Attention Is a Clamped, Lipschitz Kernel

The attention mechanism (`Transformer/CosineAttention.lean`) replaces
dot-product logits with cosine logits. The verified facts are the ones a
probabilist needs: on the sphere the logit $`q\cdot k` is bounded
(`cosineSimilarity_bounds`), so the scaled logit lies in a fixed window
$`[-\tau,\tau]` (`scaled_logit_bounds`); the softmax is a genuine distribution
(`softmax_pos`, `softmax_sum_eq_one`, `softmax_le_one`); and the softmax map is
Lipschitz with constant 2 in the $`\ell^\infty\to\ell^1` comparison
(`softmax_lipschitzWith_two`, `softmax_lipschitz`). Clamping is what makes the
subsequent noise and Lipschitz bookkeeping *uniform in the context length*: no
logit can spike, so no attention row can concentrate harder than $`e^{2\tau}`
permits.

# The Gradient-Noise Channel

`Probability/GradientNoise.lean` is the formal face of the stochastic-gradient
hypothesis that the sampler plan rests on. For a mini-batch of size $`B` drawn
from a dataset of size $`N`, the covariance of the stochastic gradient is
bounded by the full-gradient covariance scaled by $`N/B`
(`sg_pcnl_noise_covariance_bound`), and the *trace* of that covariance — the
quantity that actually enters a Langevin step's mean-square displacement — is
bounded by `sg_pcnl_noise_trace_bound` / `noiseCovTrace_le`. This is the
milestone the sibling repository's numerics test directly: the $`N/B` scaling is
what lets one backward pass per step stand in for the exact gradient without
changing the invariant measure to first order.

# The Whole Network, Lipschitz-Uniformly

Two chapters compose the local bounds into global ones.
`Transformer/LipschitzCalculus.lean` bounds each building block — contractions
(`norm_clm_apply_le_one`), attention (`norm_attnOut_le`), the geodesic residual
step (`norm_residualNorm`, `norm_ngptLayer`), the hidden-state stack
(`norm_hiddenStates`) — and then the loss itself as a function of the logits
(`dist_crossEntropy_le`). `Transformer/GlobalLipschitz.lean` upgrades these to
one constant for the entire architecture: `lipOn_ngptLayer` and
`lipOn_hiddenStates` exhibit the network as Lipschitz with an explicit constant
built from the per-layer moduli (`attnConst_nonneg`, `layerConst_nonneg`).

:::paragraph
The honest boundary: a global Lipschitz constant bounds *perturbations of the
loss*, not commutators of unbounded operators. It is therefore the analyst's
input to the numerical layer — step-size ceilings, noise ceilings, robustness
of the BMA estimate — and not an ingredient of any Faris–Lavine argument in
this book. The distinction is the same one the field-theory chapters make
between a relative bound and a comparison operator.
:::

# Where This Sits Under the Final-Hamiltonian Convention

Nothing in `BayesianTransformer/` is a Hamiltonian statement: no operator is
enclosed in creation and annihilation ladders, and none should be read in. The
convention the rest of the book states — the final Hamiltonian of each theory
is the *one-particle* operator enclosed creation-left / annihilation-right
($`d\Gamma(h) = \sum_{i,j} h_{ij}\,C^\dagger(e_i)A(e_j)`), with quantum gravity
in its $`R^2` vielbein form carrying the exact exponential Einstein-frame wall
(no Taylor truncation) and the interaction terms inside $`h`, and with the
NS/QG products-involving-field-derivatives disposed of by momentum-space
convolution ({ref "ns-one-particle-hamiltonian"}[the one-particle chapter],
{ref "second-quantization-esa"}[second quantization], the
{ref "qg-elimination"}[gravity elimination chapter]) — constrains only the
*bridges*: any future lemma placing a Bayesian prior over field configurations,
or comparing a learned sampler's invariant measure with a Fock-space state,
must enclose $`h` in that form, and must not re-derive a convolution identity in
coordinates where the momentum-space form is the one with the uniform bound.

What the two developments genuinely share is structural. The nGPT architecture
achieves its uniform constants by making every weight a *bounded* object (a
point on the sphere, a logit in a window) and every layer a *contraction-like*
map; the Faris–Lavine certificates in `BookProof/` achieve theirs by making the
comparison operator a *positive* object whose commutator is bounded in its
quadratic form. In both cases the uniformity is bought at the definition, not
extracted from a perturbative estimate — which is why both survive composition
over arbitrarily many layers (or particle-number sectors).

# The Numerical Face of the Same Plan

The sibling repository `../unfer/pcnl` implements the sampler this
formalization accompanies — unadjusted stochastic-gradient pCNL on the flat
parameter vector of the normalized architecture — and its milestone tests
(`pcnl/tests/numerics.rs`) are the empirical counterparts of the statements
above: the prior draws sit on the shell $`\sigma\sqrt{P}`
(`prior_draws_sit_on_the_shell_sigma_sqrt_p`), the OU drift term matches the
second-moment identity (`drift_term_matches_the_ou_second_moment_identity`), the
mini-batch gradient recovers the full potential at rate $`N/B`
(`n_over_b_scaling_recovers_the_full_potential_gradient` — the numeric twin of
`sg_pcnl_noise_covariance_bound`), and the schedule satisfies the
Robbins–Monro conditions (`robbins_monro_partial_sums_diverge_and_converge`).
The full comparison run (seed 20261020, $`P = 16672`, $`10^4` steps × 4 chains)
reports the plan's central empirical claim: Bayesian model averaging over the
thinned posterior beats every point estimate on the shifted task — 54.7 % for
pCNL and 58.2 % for the SGLD comparator against 41.3 % for the last chain state
and 32.4 % for Adam — while the two samplers' loss chains agree across
algorithms (`cross-Rhat` 1.110, one target), the cosine variant holds the shell
(45.7 against $`\sigma\sqrt{P} = 45.2`), and the standard softmax variant
explodes at step 3. The book's claim is not that these numbers are theorem and
proof; it is that the theorem side now names, one for one, the properties the
numbers depend on.
