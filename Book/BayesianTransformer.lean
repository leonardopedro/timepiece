import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Bayesian Adaptation: Geometry, Mehler Modes, and the Sampler Proof" =>
%%%
tag := "bayesian-transformer"
%%%

# Three Questions, Three Different Proofs

Normalized transformer geometry, Gaussian proposal mixing, and posterior sampling
ask different questions. `BayesianTransformer/` supplies conditional geometric
and gradient-noise estimates. `BookProof/MCMC/` supplies Gaussian eigenfunctions,
coefficient estimates, and convergence implications. The remaining task is to
identify the actual kernel in `../unfer/pcnl` with an operator satisfying those
implications. This chapter records a source audit; the new citations and prose
await the specialist's compilation and book-render checks.

Normalization removes a radial degree of freedom where the normalization map is
defined. `scaleInvariant_gradient_orthogonal` expresses gradient tangency.
`sphereProj_deriv_opNorm_le` has a reciprocal-radius bound, which grows near zero.
Cosine logits have bounded range; `softmax_lipschitzWith_two` bounds softmax.
Network estimates still carry their layer constants and domain hypotheses. They
neither keep a flat Gaussian parameter vector on a sphere nor establish a
uniform gradient bound for every transformer. The noise estimates similarly
require their sampling and covariance hypotheses. An unbiased gradient does
not imply that a finite-step unadjusted sampler preserves the posterior.

# The Gaussian Benchmark: Mehler Diagonalization

For a centered Gaussian reference the proposal is
$`Y=\rho X+\sqrt{1-\rho^2}\,\xi`, with an independent reference draw $`\xi`.
Hermite degree $`n` has eigenvalue $`\rho^n`. This holds already in finite
Gaussian dimension. `MehlerEigenfunction` uses the physicists' Gaussian
$`e^{-x^2}/\sqrt\pi`, of variance $`1/2`; a variance-one implementation needs
an explicit change of variables.

```
#check @BookProof.MCMC.mehlerOp_physHermite
#check @BookProof.MCMC.UnadjustedPCN.pcn_gap_uniform
#check @BookProof.MCMC.UnadjustedPCN.pcn_norm_le
```

The coefficient model bounds the squared norm by $`\rho^2` off the constant
mode. For $`0\le\rho<1`, the contraction factor is $`\rho`, the Markov gap
is $`1-\rho`, and the squared-norm defect is $`1-\rho^2`. Tensorization and
completeness must connect the integral identity to a Hilbert-space realization.

Spherical kernels require a separate construction. The Gegenbauer ratios have
the expected fixed-degree limit, but the degree-two ratio differs from
$`\rho^2` at finite dimension. These polynomial identities do not construct a
spherical Markov kernel or prove its complete spectrum.

```
#check @BookProof.MCMC.pcnZonalEigen_two_ne_pow_two
#check @BookProof.MCMC.pcnZonalEigen_tendsto
```

# What the New Ladder Proofs Achieve

On finitely supported occupation coefficients, polynomial multiplication is a
finite sum of ladder words. `polyMul_mul` proves multiplicativity;
`polyMul_derivative` expands derivative polynomials. Composing with `diffHermite`
gives `polyDrift`, the differential core expression
$`-\sum_j(\partial_j\Phi)\partial_j` in the module's Hermite dictionary.

```
#check @BookProof.MCMC.FockLangevin.polyMul_mul
#check @BookProof.MCMC.FockLangevin.polyMul_derivative
#check @BookProof.MCMC.FockLangevin.polyDrift_band
#check @BookProof.MCMC.FockLangevin.polyDrift_l1_le
```

For a potential of degree at most $`K`, the drift sends degrees at most $`N_0`
into degrees at most $`N_0+K`. A finite band specifies which entries can be
nonzero, not a global norm bound. The proved $`\ell^1` bound depends on the
sector cutoff. The oscillator identity supplies the analytic input
$`\sum_j(\|a_jc\|^2+\|a_j^\dagger c\|^2)
=2\langle c,Nc\rangle+d\|c\|^2`.

```
#check @BookProof.MCMC.FockLangevin.oscillator_identity
#check @BookProof.MCMC.FockLangevin.driftOpCoeff_form_bound
#check @BookProof.MCMC.FockLangevin.driftFormBound_holds
```

The last two results concern constant coefficients
$`b:\mathrm{Fin}\ d\to\mathbb R`. When $`|b_j|\le B`, they give
$`|\langle c,K_bc\rangle|\le\delta\langle c,Nc\rangle+
(B^2d/(2\delta)+Bd)\|c\|^2` for $`\delta>0`.
A general loss gradient is an operator-valued multiplication coefficient; it
cannot be substituted for the scalar $`b_j`. Nonpolynomial normalization and
cross-entropy need further estimates.

For real couplings the field $`a^\dagger(f)-a(f)` is skew-symmetric. A bound
on its quadratic pairing does not make $`N+K` a symmetric KLMN perturbation.
A reversible Langevin generator needs a verified ground-state transform,
including domains, potential and divergence terms. `pcnlPolyHamiltonian`
names a core model; it does not assert these identifications.

# Mixing and Correctness Are Separate

Take reference $`N(0,1)`, potential $`\Phi(x)=-x`, and update
$`X'=\rho X-h\Phi'(X)+\beta\xi`, with $`\rho^2+\beta^2=1`.
For $`\rho=0.8`, $`\beta=0.6`, $`h=0.18`, the chain converges geometrically
to $`N(0.9,1)`, whereas the intended posterior is $`N(1,1)`.
Its stationary mean solves $`m=\rho m+h`. A positive mixing gap therefore
coexists with posterior bias; read each implementation's step convention first.

`pcnl.md` packets T0–T5 start with affine and quadratic Gaussian benchmarks,
then require the measurable kernel, invariance or its defect, adjoint and
Dirichlet form, and an actual comparison estimate. Metropolis correction needs
the full forward/reverse proposal density ratio. Rejection includes both an
accepted-move integral and a holding term; only the holding term is simply
multiplication. An infinitesimal differential drift is not an exact additive
decomposition of the finite-step transition.

```
#check @BookProof.MCMC.norm_iterate_sub_invariant_le
#check @BookProof.MCMC.tvDist_le_half_l2
#check @BookProof.MCMC.pcnl_mcmc_geometric_convergence
```

These theorems transfer an assumed absolute contraction to iteration decay,
then an assumed density decay to total variation. A top spectral gap alone
does not exclude eigenvalues near $`-1`. The specialist must supply the
probability measure, density evolution, invariance and absolute contraction.

# Relation to the Physical Nested Fock Space

Gaussian chaos occupation counts polynomial degree. Physical outer occupation
counts copies of an inner field state. A coefficient isometry does not identify
their generators or vacua. The physical record remains
$`H=d\Gamma(h)=\sum_{i,j}h_{ij}C^\dagger(e_i)A(e_j)`.
QYM retains the full magnetic polynomial inside $`h`; QED retains its massless
infrared boundary. QG uses the $`R^2` vielbein/TEGR operator, exact exponential
wall and scalaron–vielbein interactions. NS uses the positive Fourier-eliminated
sum-of-squares one-particle operator. Momentum convolution for spatial
derivative products belongs to NS and QG only. These conventions constrain
physical bridges; they do not establish a sampler's invariant measure.
See {ref "second-quantization-esa"}[second quantization] for the vacuum,
positivity and scalar-shift consequences.

# Reading the Numerical Evidence

The implementation, experiments and research work order live in `../unfer/pcnl`,
its `RESEARCH_PLAN.md`, and `../test/unfer/ngpt.md`. Read timings, accuracy,
finite-run diagnostics and stationarity tests separately. Gaussian shell
concentration is probabilistic, not a bound on every sampler step. Agreement of
selected loss traces does not prove equality of stationary laws. The earlier
single-run accuracy comparison is superseded by the controlled comparisons and
budget ledger in those documents; no new numerical run is claimed here.
