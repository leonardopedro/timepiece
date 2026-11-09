# pCNL: Mehler operators, nested Fock representations and convergence certificates

## Revised research and formalization work order (2026-11-08)

This section supersedes the architecture, milestone ordering and completion claims below
**as a reading guide for this file**. Earlier dated notes remain implementation history.
It does not change the programme ordering in `CURRENT_WORK_ORDER.md`. The task is to
identify a concrete Markov operator, prove its gap under explicit assumptions, and connect
that result to the correct implementation. No full transformer pCNL gap is claimed here.
This revision inspects source statements; it does not rerun Lean or numerical experiments.

**Implementation refinement (2026-11-08, subsequent review):** the “Executable proof
packets” below turn P0–P6 into concrete interfaces, analytic benchmarks and acceptance
artifacts. They refine this work order without superseding its mathematical corrections.

### Sources and division of responsibilities

* [book.tex](book.tex), the recursive second-quantization paragraph beginning “Since the
  second-quantization procedure can be applied recursively”: an inner interacting operator
  can be enclosed in outer creation/annihilation operators. That operation is not a proof
  of reversibility or a spectral gap for a statistical sampler.
* [Book/FreeField.lean](Book/FreeField.lean), the Mehler-limit section, and
  [Book/SolovayTensor.lean](Book/SolovayTensor.lean), “Only the Mehler Measure on the
  Infinite Part”: Gaussian coordinates and representation. Coordinate-law uniqueness
  does not imply uniqueness of a posterior or of its invariant transition kernel.
* [Book/BayesianTransformer.lean](Book/BayesianTransformer.lean): the geometry/noise
  development and its operator-bridge boundary. Its old reported BMA values and compile
  status must be checked against the current implementation before being reused.
* [Hashimoto–Nodera](../papers/Hashimoto.md), Definition 2.4 and Theorem 4.1: resolvent
  functional calculus and rational approximation errors, not automatic gap certificates.
* [softmodes.md](softmodes.md), “Revised work package (2026-11-08)”: form/operator
  identification, ground-sector alignment and independent spectral exclusion.
* [ngpt.md](../test/unfer/ngpt.md), §3.2, §4.3, §6.5.9, §6.6 and §9: the experimental
  motivation, epsilon/schedule corrections, dimension-budget hypothesis and readout tasks.
* [unfer/pcnl/RESEARCH_PLAN.md](../unfer/pcnl/RESEARCH_PLAN.md): the crate execution
  plan R0–R6. It owns numerical audits and experiments; this file owns the mathematical
  operator/representation contracts and Lean targets. Keep their conclusions consistent.

Use **U** for an existing result within its stated model, **C** for an unproved bridge
or hypothesis, **N** for an invalid inference, and **B** for a scope boundary. Read theorem
types rather than names or headers. Several module comments still repeat older claims
that their actual declarations do not prove.

### P0 — fix the kernel, measure and convergence target first

For a finite-dimensional Gaussian reference `mu0 = N(0,C)`, define
$q=d\pi/d\mu_0=Z^{-1}e^{-\Phi}$ with $0<Z<\infty$. State the covariance, energy
scaling, dimension, batch law, epsilon normalization and parameter domain. An
infinite-dimensional Hilbert Gaussian additionally needs trace-class covariance; white
product coordinates live on a different measure space, not almost surely in $\ell^2$.

There are four different operator problems:

| Kernel | Invariant measure / symmetry | Initial theorem target |
|---|---|---|
| Gaussian pCN proposal | `mu0`, reversible | Exact Mehler benchmark |
| Fixed-angle sphere walk | Haar, reversible | Spherical operator identity and gap |
| Correct MH-pCNL | `pi`, reversible | Target-specific absolute gap |
| Fixed-step unadjusted SG-pCNL | Must establish its own invariant law | Bias and contraction |

For a kernel $K$, use $(Pf)(x)=\int f(y)K(x,dy)$ on **observables** in $L^2(\pi)$.
Prove stationarity and detailed balance before asserting self-adjointness. Density ratios
evolve by $P^*$; only in the reversible case can they be written as $P^m g_0$.
A nonreversible Markov contraction need not be normal. Its analysis may use a norm bound
on the centred subspace, $P^*P$, or a multi-step contraction; do not apply a self-adjoint
spectral theorem solely because the transition is linear.

Unadjusted fixed-step and mini-batch kernels do not automatically preserve `pi`, and
there is no generic $O(\beta)$ bias statement without assumptions, a metric and a proof.
Annealed/cyclical steps define time-inhomogeneous products, not powers of one operator.
State these targets separately from a fixed-step MH theorem.

**Acceptance:** a proposed `BookProof/MCMC/KernelContract.lean` with a measurable kernel,
stationary law, associated $L^2$ operator, adjoint/density action and reversibility lemma
for a concrete benchmark. This is new work, not an existing module. Follow crate R0's
gradient, exact-ratio and diagnostic audits before binding the contract to Rust.

### P1 — establish the Gaussian Mehler benchmark without a spherical detour

In finite dimension, $x'=\rho x+\sqrt{1-\rho^2}\xi$, $\xi\sim N(0,C)$,
already has a Gaussian/Hermite diagonalization. For $0\le\rho<1$, its degree-$n$
chaos eigenvalue is $\rho^n$ and its norm on mean-zero observables is $\rho$.
This identity does **not** require $d\to\infty$. Complete the finite-product tensor
argument, normalization and basis-isometry bridge from the existing one-dimensional
Mehler integral to a bounded operator on the chosen Gaussian $L^2$ space.

`MehlerEigenfunction.mehlerOp_physHermite` uses density $e^{-x^2}/\sqrt\pi$
(variance $1/2$). Record the rescaling to standard normals and the actual prior `C`.
Hermite polynomials in Gaussian $L^2$ and Hermite functions in Lebesgue $L^2$ are related
by multiplication by the square root of the Gaussian density; they are not the same basis.
For variance one, Gaussian adjoints satisfy $D_j^*=x_j-D_j$, with
$N=\sum_jD_j^*D_j$; numerical ladder factors must follow that convention.

The fixed-angle **spherical** proposal instead takes uniform unit tangent noise and has
the candidate zonal eigenvalues
$\Lambda_n^{(d)}=C_n^{((d-2)/2)}(\rho)/C_n^{((d-2)/2)}(1)$ for $d>2$.
`GegenbauerEigenvalue` proves quotient identities and fixed-degree limits; it does not
construct the spherical Markov operator or prove its addition theorem/completeness.
The circle needs its own Fourier/Chebyshev treatment. Random geodesic step lengths in
the implemented sphere sampler are yet another kernel, not this fixed-angle proposal.

**N:** fixed-degree convergence $\Lambda_n^{(d)}\to\rho^n$ cannot interchange
$d\to\infty$ with $\sup_{n\ge1}|\Lambda_n^{(d)}|$. A polynomial marginal limit
also does not prove strong convergence of unbounded generators on changing spaces.
For a spherical-generator limit specify radius, time scaling, embeddings, common cores
and a semigroup/resolvent convergence theorem. Keep that optional work off the critical
path of the finite-dimensional Gaussian pCN theorem.

**Acceptance:** proposed `GaussianKernelBridge.lean` linking the real transition to
`UnadjustedPCNGap`'s coefficient norm estimate. Its `pcn_gap_uniform` concerns the
defined weights $\rho^{2N}$; the squared-norm loss $1-\rho^2$ and the absolute
operator gap $1-\rho$ must remain distinct.

### P2 — use the correct density-ratio convergence theorem

Let $\Pi f=\int f\,d\pi$ and prove
$\|P-\Pi\|_{L^2(\pi)\to L^2(\pi)}\le1-\gamma$, $0<\gamma\le1$.
For self-adjoint $P$, this controls the **absolute** spectrum on the mean-zero subspace:
both its upper edge and negative edge matter. A Poincare bound on $I-P$ controls only
the upper edge. One clean option is explicit lazification $P_L=(I+P)/2$, which changes
the implementation's clock and must be reported; it puts the spectrum in $[0,1]$.

With $g_0=d\nu_0/d\pi\ge0$, $\int g_0d\pi=1$ and $g_0-1\in L^2(\pi)$,
reversibility and the gap give

$$\|\nu_0K^m-\pi\|_{TV}\le\tfrac12\|g_0-1\|_{L^2(\pi)}(1-\gamma)^m.$$

`GeometricErgodicity.norm_iterate_sub_invariant_le` proves the Hilbert-space decay
**given** the contraction. `ConvergenceTheorem.tvDist_le_half_l2` and
`pcnl_mcmc_geometric_convergence` provide the density-ratio-to-TV receiver. Connect
them through an actual kernel and its density evolution; the receiver does not prove
the invariant law, gap or smoothing of a point initialization.

In $L^2(\pi)$ the invariant vector is $1$. When $q>0$ almost everywhere for $\mu_0$,
the unitary $Uf=\sqrt q\,f$ onto $L^2(\mu_0)$ sends it to $\sqrt q$. For a
restricted-support target use its supported range instead of asserting surjectivity. Thus
$T=UPU^{-1}$ fixes $\sqrt q$, but $U g_0=g_0\sqrt q$ is generally **not** the
square root of $d\nu_0/d\mu_0$. Markov evolution is linear on densities; it does
not generally evolve Born square-root amplitudes by the same linear map.
Normalization gives $\langle\sqrt q,U g_0\rangle=1$, not a statement about arbitrary
unit wavefunctions. Use spectral measures for a general operator, not an assumed
countable eigenbasis/discrete spectrum.

**B:** $\delta_x$ need not have an $L^2$ density. A rejected MH chain can retain an
atom at its initial state at finite time. Provide a warm-start or minorization/smoothing
argument before claiming the bound for every deterministic `u0`.

**Acceptance:** a kernel-level convergence theorem carrying its warm-start constant,
ground projection, absolute gap and density-action identity explicitly.

### P3 — derive a target gap, not merely a drift-size estimate

Start with exact MH-pCN as a tractable benchmark, separate from MH-pCNL's drifted
proposal. When $\operatorname{osc}\Phi\le B<\infty$, prior reversibility gives
$\pi(dx)K_{MH}(x,dy)=\min(q(x),q(y))\mu_0(dx)K_0(x,dy)$ off the diagonal.
Derive a Dirichlet-form comparison and target-variance comparison to obtain the
Poincare gap bound $e^{-B}(1-\rho)$. For its lazy version this yields an absolute
gap at least $\tfrac12e^{-B}(1-\rho)$. Formalize the assumptions and comparisons;
these are proposed proofs, not current declarations. The constant may be unusably small
or depend strongly on dataset size, architecture and dimension.

For unbounded potentials or drifted proposals, supply the appropriate target-specific
Dirichlet-form comparison, conductance, Lyapunov/minorization or other quantitative
argument. The [pCN construction](https://arxiv.org/abs/1202.0709) and
[Hairer–Stuart–Vollmer](https://arxiv.org/abs/1112.1392) are primary references to audit
for their exact hypotheses and notion of gap before porting a theorem. Do not transfer
a theorem about pCN, a Wasserstein metric or a function-space discretization directly
to finite-sphere MH-pCNL or unadjusted transformer sampling.

**N:** bounded $\nabla\Phi$ alone supplies neither a small operator-norm perturbation
of the pCN transition nor a useful gap. On the current `FockLangevinOperator` core,
`driftOpCoeff` takes **constant coefficients** `b : Fin d → R`.
`driftFormBound_holds` does not replace them by state-dependent multiplication operators.
`polyDrift` separately expands polynomial coefficients, with sector-dependent estimates.
An nGPT cross-entropy potential is not a polynomial; an approximation needs tail,
derivative and operator/form-error control, not just a finite-band truncation.

**N:** the KLMN conclusion in the history needs correction. For real couplings the
constant field `creVec - annVec` is skew-symmetric on its natural core, not symmetric.
An absolute bound on its quadratic pairing does not make `N + driftField` self-adjoint
by the symmetric KLMN theorem. A variable-coefficient transport drift is not symmetric
in the Gaussian inner product either. Prove the adjoint/domain relation for the actual
operator before choosing a symmetric-form or sectorial-generator theorem.

The exact MH operator is
$Pf(x)=\int\alpha(x,y)f(y)Q(x,dy)+r(x)f(x)$ with
$r(x)=1-\int\alpha(x,y)Q(x,dy)$. Only the holding term is multiplication.
The accepted off-diagonal term changes too. Writing `P0 + K_drift + K_reject` requires
an actual remainder identity; a first-order differential drift is not an exact additive
correction to a finite-step Markov transition.

**Acceptance:** a proposed `MetropolisGapComparison.lean` for the bounded-oscillation
benchmark, then a separately justified full pCNL target estimate. Following softmodes S2,
do not subtract two lower spectral bounds, confuse a reference vacuum with the true
ground state, or call closability/semiboundedness a positive gap.

### P4 — derive the diffusion/Fock bridge with all Gaussian terms included

For a separate finite-dimensional, whitened, smooth benchmark let
$V(x)=|x|^2/2+\Phi(x)$, $\pi(dx)\propto e^{-V(x)}dx$, and
$Lf=\Delta f-\nabla V\cdot\nabla f$. State the closed Dirichlet form,
domain, integrability and integration-by-parts hypotheses. The ground-state transform
$Wf=Z_V^{-1/2}e^{-V/2}f$ gives, on a verified core,

$$H=-WLW^{-1}=-\Delta+\tfrac14|\nabla V|^2-\tfrac12\Delta V
=N+\tfrac12x\cdot\nabla\Phi+\tfrac14|\nabla\Phi|^2-\tfrac12\Delta\Phi,$$

where $N=-\Delta+|x|^2/4-d/2$. The earlier expression containing only derivatives of
$\Phi$ omits the Gaussian prior and cross term. For nonidentity covariance first prove
the whitening/preconditioning transformation, with its domains and constants.
`N + polyDrift Phi` is not automatically this self-adjoint transformed generator.

A Hessian criterion is $\nabla^2V\ge\kappa I$, $\kappa>0$, with the usual diffusion
assumptions, not an unexplained `Hess Phi` criterion for every discrete pCNL kernel.
If the target is nonconvex, state another justified Poincare estimate. A diffusion
gap gives heat-flow decay; finite-step MH or unadjusted convergence needs a separate
discretization/operator comparison with a quantitative error.

Tests of the formula should include $\Phi=0$, a linear potential (shifted Gaussian,
same diffusion gap), and $\Phi=\eta|x|^2/2$ with $\eta>-1$ (gap $1+\eta$).
Build polynomial matrix elements using `polyMul_mul`, `polyMul_derivative`,
`polyDrift_eq_hopWords`, the band and letter-norm lemmas, but check symmetry of the
**transformed** operator rather than assigning that property to a drift by its name.

Under a Gaussian-chaos isometry, $L^2(\mu_0)$ has a symmetric-Fock representation and
the free OU operator is its number operator. The manuscript's **outer** nested enclosure
of a chosen inner $h$ is another construction:
$H_{out}=d\Gamma(h)=\sum h_{ij}C^\dagger(e_i)A(e_j)$.
Prove the isometry, matrix elements, core transport and restriction to the one-outer-
particle sector before using it for the original chain. Outer quadraticity retains the
inner interactions; it does not diagonalize the posterior operator.

In particular the inner equilibrium has energy zero. Its occupation in an outer
one-particle sector is different from the outer vacuum; arbitrary copies give additional
zero-energy outer states. A gap above the full kernel is not isolation of the outer
vacuum. Do not add $\mu N_{out}$ or silently discard inner equilibrium states to claim
the original chain mixes. Also $d\Gamma(B^2)\ne d\Gamma(B)^2$ in general.

**Acceptance:** proposed `LangevinGroundTransform.lean` with operator/core identity,
correct Gaussian normalization, self-adjoint realization and a named target gap input.
The optional nested lift should state exactly which sector recovers the MCMC problem.

### P5 — make Hashimoto approximation and gap certification separate gates

For a verified positive self-adjoint $H$, use the paper's generator $A=-H$ and bounded
$X_\gamma=(\gamma I+H)^{-1}$ with $\|X_\gamma\|\le1/\gamma$.
Definition 2.4 requires admissibility of $f_\gamma(z)=f(\gamma-z^{-1})$ on the
resolvent's numerical range. Theorem 4.1 additionally needs its projected-matrix
invertibility, real shift schedule $\gamma_j=N_s-sj>0$, and $m<N_s/s$:

$$\|\phi_k(A)v-u_m\|\le2C\|v\|e^{-sm}
\inf_{r\in\mathcal R^{SIRK}_{m-1}}\|f_{k,N_s}-r\|_{\infty,\Sigma}.$$

Keep the approximation factor and finite shift budget. Complex-shift Lean results and
the book's inversion-free polynomial shortcut require their own equivalence hypotheses;
they are not automatically this rational approximation theorem.
For a discrete reversible chain, $H=I-P$ is positive but $e^{-t(I-P)}$ is a
Poissonized chain, not $P^m$. Its decay does not control eigenvalues of $P$ near $-1$;
use lazification or a separate negative-spectrum bound.

Follow softmodes S3: certify the **full** residual, including the omitted basis tail;
distinguish compressed resolvent from inverse compressed Hamiltonian; propagate solve,
rounding, quadrature and operator-approximation errors. A solve defect $r$ yields
inverse-action error at most $\|r\|/\gamma$. Reference eigenvalues and small Ritz
residuals alone do not exclude unseen modes near zero. Deflation requires the actual
ground projection, and Temple separation must be justified independently.

A finite-degree gap needs a uniform tail/coercivity and coupling estimate before it is
a full-operator gap. `ChapterSirkDiffusiveDecay.isCoercive_compress` preserves supplied
coercivity; it does not discover it. Strong resolvent convergence alone or convergence
of each displayed matrix entry does not complete this exclusion.

**Acceptance:** a certificate listing operator, measure, ground sector, cutoff, tail
estimate, absolute/one-sided gap, and the complete error budget. Separate the certified
mathematical model from the floating-point Rust transition. Empirical diagnostics still
check whether that model and its claimed assumptions describe the run.

### P6 — bind the formal result to ngpt experiments without changing the target

Use ngpt §6.5.9's exact cap-law measurements to select **candidate** ranks and radii,
not to assert a theorem about the number of informative directions. Local curvature,
random-ray contrasts and high ESS on observed prior draws do not establish a global
posterior-mass exclusion. The crate plan distinguishes a frozen-complement subspace
posterior from a full posterior sampled with informed proposals; keep that distinction
in the Lean contract. Data-dependent anchors/priors, temperature and cap conditioning
change the statistical target and must appear in the statement.

Carry ngpt §3.2's epsilon and architecture-domain hypotheses explicitly. Exact scale
invariance and tangent-gradient identities do not automatically apply to epsilon-
regularized tensors or stopped-gradient norm calculations. In
`BayesianTransformer/Probability/GradientNoise.lean`,
`sg_pcnl_noise_covariance_bound` is a deterministic norm ceiling for an assumed estimator;
`sg_pcnl_noise_trace_bound` gives a finite-distribution trace ceiling. Neither proves
unbiasedness of the actual loader, a sharp $1/B$ variance law or posterior invariance.
The architecture proof's operator-norm normalization/domain also needs a bridge to the
Rust Frobenius-normalized implementation.

For an annealed schedule use its **actual** floored/clamped steps. The ideal power law
with $1/4<\kappa\le1/2$ satisfies the stated sums on $\beta_t^2$ and $\beta_t^4$;
a positive floor eventually changes those sums. Even if each kernel shares a target,
product contraction needs a bound such as $\prod_t(1-\gamma_t)$ and its accumulated
gap. If invariant laws differ, add a proved bias/perturbation term instead. A cyclical
schedule requires another analysis, and scalar ESS/Rhat does not certify any of these.

For ngpt §9's chain readout, prove predictive precision separately from posterior
mixing and model quality. Finite-mixture Brier inflation is `tr Cov/m` for independent
draws; correlated stationary chains need the full autocovariance sum, and nonstationary
draws also have bias. Parameter wandering, a stable Gaussian shell, or finite gradient
noise does not by itself imply useful predictions or calibrated decisions.

**Acceptance:** a proposed `ImplementedKernelBridge.lean` hypothesis list mirrored by
crate R0–R3 tests and manifests. Formal sampling statements stay conditional until those
data/gradient/transition identities and the target-specific gap are supplied.

### Executable proof packets

All declarations in this subsection are **proposed targets**, not completed theorems.
They are specifications for the Lean specialist and the crate's R0–R3 work. Implement
them as small modules with explicit probability, integrability and domain assumptions;
do not introduce axioms to fill the missing identifications.

#### T0 — reuse the actual kernel API, then build its `L2` action

The pinned Mathlib already supplies `ProbabilityTheory.Kernel`, `IsMarkovKernel`,
`Kernel.Invariant`, `Kernel.IsReversible` and `Kernel.IsReversible.invariant` in
`Mathlib/Probability/Kernel/Invariance.lean`. Reuse these definitions. Reversibility is
equality of the two setwise flows; invariance is `pi.bind K = pi`. A second bespoke
stationarity predicate would create an unnecessary translation obligation.

For a probability measure `pi`, first define the integral action on bounded measurable
test functions. Prove Jensen's estimate and integrate against the invariant measure:

$$|Pf(x)|^2\le P(|f|^2)(x),\qquad
\int|Pf|^2d\pi\le\int|f|^2d\pi.$$

Then descend to almost-everywhere equivalence classes and extend to `Lp complex 2 pi`.
This must prove that changing a representative does not change the resulting `L2` class;
writing the Bochner integral for an arbitrary representative is not sufficient. Establish
`P 1 = 1`, preservation of the mean, and the integral duality identifying density
evolution with the adjoint. Derive self-adjointness from detailed balance on a dense
test class and continuity. Complete the product-Gaussian kernel instance before any
posterior or outer-Fock lift.

**Deliverable:** `KernelContract.lean` plus `GaussianKernelBridge.lean`, with an actual
`Kernel`-to-continuous-linear-map construction. Any finite-state tests should use the
same observable/density orientation. `ChapterAttentionMarkov`'s stochastic-matrix
contraction is a useful finite-state check, but an attention-position kernel is not the
parameter-space sampling kernel.

**Receiver audit:** `ConvergenceTheorem.pcnl_mcmc_geometric_convergence` accepts a
density-decay bound and only `gamma < 1`; the wrapper must additionally require
`0 < gamma`. Handle `gamma = 1` separately if needed. Its `tvDist` uses `toReal` on
measure values, so retain probability/finite-measure instances for every `nu_m` when
identifying that expression with standard total variation. Prove normalization and
nonnegativity from kernel pushforward; do not merely assume unrelated functions `d_m`
have the desired decay. These bridges make P2 an MCMC theorem rather than a theorem
about an arbitrary sequence of densities.

#### T1 — exact Gaussian targets that distinguish a gap from posterior accuracy

Use the scalar whitened prior `N(0,1)` and
$\Phi(x)=\kappa x^2/2-bx$ with $\kappa>-1$. The intended posterior is

$$\pi=\mathcal N\left(\frac{b}{1+\kappa},\frac1{1+\kappa}\right).$$

For the full-gradient unadjusted update in this crate's coefficient convention, fix
$0<\beta\le1$, set $\rho=\sqrt{1-\beta^2}$, $h=\beta^2/2$, and obtain

$$x_{t+1}=a x_t+h b+\beta\xi_t,\qquad
a=\rho-h\kappa,\quad\xi_t\sim\mathcal N(0,1).$$

When $|a|<1$, its invariant distribution is exactly

$$\pi_\beta=\mathcal N\left(m_\beta,s_\beta^2\right),\qquad
m_\beta=\frac{h b}{1-a},\quad s_\beta^2=\frac{\beta^2}{1-a^2}.$$

This is the first canary: the chain has a Hermite absolute gap `1-|a|` in
`L2(pi_beta)` while generally sampling a law different from `pi`. Even the linear
case $\kappa=0$ gives $m_\beta=b(1+\rho)/2$, not $b$, at finite step.
For fixed $\kappa,b$, the mean and variance errors vanish as $O(\beta^2)$ as
$\beta\to0$; prove constants/ranges instead of repeating a generic $O(\beta)$ claim.
Also include a parameter cell with $\kappa>-1$ but $|a|\ge1$: a normalizable
target does not imply stability of an unadjusted discretization.

For a simple hand-check, take `beta = 0.6`, hence `rho = 0.8`, `h = 0.18`, and `b = 1`.
At `kappa = 0` the invariant mean is `0.9` instead of `1`, although the invariant
variance is exactly `1`. At `kappa = 11` the intended posterior still exists but
`a = -1.18`, so the update is unstable. These cells detect target/bias conflation and
the erroneous inference that a prior-preserving noise term stabilizes every drift.

For an independent Gaussian gradient error $\zeta_t\sim N(0,v)$, replace the
innovation by $\beta\xi_t-h\zeta_t$. The invariant mean is unchanged and its
variance is $(\beta^2+h^2v)/(1-a^2)$. This isolates mini-batch-noise inflation from
drift discretization bias. For non-Gaussian independent errors only the corresponding
moment formulas follow; do not call the invariant law Gaussian. State independence
from the current state, which a real state-dependent minibatch oracle need not satisfy.

**Deliverable:** proposed `GaussianARBenchmark.lean` with stationary-law identities,
stability conditions, Hermite contraction for Gaussian innovations, and explicit bias
formulas; corresponding crate tests compare moments and projected gradients at matched
coefficients. Choose analytic tolerances before simulation. Do not tune the intended
posterior parameters to the measured stationary law after the fact.

#### T2 — a genuine dimension-robust informed-subspace benchmark

For `P >= r >= 1`, split standard Gaussian coordinates as `(z,q)` with `r` informed
coordinates and `P-r` uninformed coordinates. Set
$\Phi(z,q)=\tfrac12 z^T\Lambda z-b^Tz$, with diagonal
$\Lambda=\operatorname{diag}(\lambda_i)$ and $\lambda_i>-1$.
Then `pi = pi_z tensor N(0,I_(P-r))`, where
$\pi_z=N((I+\Lambda)^{-1}b,(I+\Lambda)^{-1})$.

Construct a **posterior-aware Gaussian reference kernel** by whitening with these known
posterior moments and applying independent Mehler steps with factors `rho_z` and
`rho_q`. This is an exact reference kernel, not a claim that prior-based MH-pCNL has
that form. For nonempty blocks and `0 <= rho_z,rho_q < 1`, tensorization gives the
absolute gap `1-max(rho_z,rho_q)`, independent of the number of uninformed coordinates.
For an empty complement use only `rho_z`. Verify the full law, not just its restriction
to the informed coordinates. Frozen-complement sampling of `pi_z` is a different model.

Hold `r`, `Lambda`, `b` and the two factors fixed while varying `P`. This creates the
controlled dimension family that the neural experiments currently lack. A dimension-free
operator gap still does not make the warm-start prefactor dimension free. For example,
in the scalar centred case the prior-to-posterior density ratio fails to lie in
`L2(pi)` when `kappa >= 1`; use an explicitly justified warm distribution instead.

**Deliverable:** proposed `GaussianSubspaceBenchmark.lean` with product measure, chaos
isometry, exact invariant law and tensor norm bound, followed by a test of the crate's
restricted and full-target arms. Only after this benchmark passes should the measured
cap budget select ranks for a nonquadratic transformer experiment.

#### T3 — turn P3's bounded-oscillation comparison into a short proof chain

Work first with a prior-reversible proposal `K0` and a density satisfying
$0<q_-\le q\le q_+<\infty$ almost everywhere. Let
$\mathcal E_K(f)=\tfrac12\int\pi(dx)K(x,dy)|f(y)-f(x)|^2$.
For the MH correction of **this** proposal, the detailed-balance measure identity in
P3 gives

$$\mathcal E_{MH,\pi}(f)\ge q_-\mathcal E_{K0,\mu_0}(f),\qquad
\operatorname{Var}_\pi f\le q_+\operatorname{Var}_{\mu_0}f.$$

Prove the variance inequality using its infimum over constant centres; a `pi`-centred
function need not be `mu0`-centred. Thus a prior Poincare gap `g0` transfers as
`g_pi >= (q_minus/q_plus) g0`. With `osc Phi <= B`, use
`q_plus/q_minus <= exp B`, then lazify for the absolute contraction. This proof needs
no assertion that the two measures share the same mean-zero subspace.

**Deliverable:** lemmas for density bounds, variance comparison, MH Dirichlet comparison
and lazy absolute contraction, ending in the warm-start TV theorem of T0/P2. The output
is an exact MH-pCN benchmark with a possibly conservative constant. Extending to a
drifted proposal requires a new comparison of its flow measure, not a change of name.

#### T4 — specify a full-space spectral certificate before finite truncation

On the true mean-zero space use `H = I-P_lazy`, with the equilibrium vector already
removed. Split that space orthogonally into a retained subspace and its complement.
For bounded `H`, write its blocks as `A, B*, B, D`; for an unbounded diffusion
generator state the corresponding common form-domain and cross-form bounds instead.
Require verified constants

$$A\ge\alpha I,\qquad D\ge\delta I,\qquad\|B\|\le c,\qquad
\alpha>0,\quad\delta>0,\quad c^2<\alpha\delta.$$

Then the block estimate supplies the explicit positive full-space bound

$$g_{cert}=\frac{\alpha+\delta-
\sqrt{(\alpha-\delta)^2+4c^2}}2>0.$$

Enclose the retained block, tail and coupling separately; use outward error bounds in
all three inputs. For pure Gaussian pCN, chaos degrees above `M` give the exact tail
bound `1-rho^(M+1)` for `I-P0`, with zero coupling. For an interacting MH kernel
neither finite band nor zero coupling follows from the polynomial diffusion expansion.
The retained basis must be centred/orthonormal for the **target** measure, or transported
with its verified Gram matrix and ground projection.

This supplies a concrete softmodes-style tail/coupling route. When these block bounds
are proved, no Temple argument is needed to manufacture a separation that is already
contained in them. Hashimoto approximation can help compute operator actions; it does
not replace the tail estimate. Reject a certificate with an unknown tail, omitted
coupling, or nonpositive `g_cert` rather than reporting a finite-matrix gap as full-space.

**Deliverable:** proposed `MarkovGapCertificate.lean` with the block inequality and a
certificate record containing the target/kernel revision, equilibrium projection,
cutoff, `alpha/delta/c` enclosures, all approximation errors and the resulting rate.
Use the exact Gaussian case to test the record end to end before a nonpolynomial model.

#### T5 — connect an operator gap to predictive precision and approximate updates

For a stationary chain with absolute contraction factor `r=1-gamma`, and a centred
square-integrable vector prediction `p-p_bar`, prove the covariance estimate
$|\operatorname{Tr}\Gamma_k|\le r^k\operatorname{Tr}\Gamma_0$. It yields

$$E\|\widehat p_m-\bar p\|^2
\le\frac{\operatorname{Tr}\Gamma_0}{m}\frac{1+r}{1-r}
=\frac{\operatorname{Tr}\Gamma_0}{m}\frac{2-\gamma}{\gamma}.$$

Use this in ngpt's correlated Brier calculation, stating stationarity and finite second
moments. Do not infer calibration of `p_bar` or superiority to an optimizer: the bound
only controls Monte Carlo error for the specified target. A useful posterior and a
precisely computed weak posterior remain distinct outcomes.

For approximate dynamics on the same density-ratio space, define the residual explicitly:
$e_t=g_t-1$, $e_{t+1}=P^*e_t+R_t$. If `||R_t||_2 <= epsilon_t` and `P*`
contracts mean-zero vectors by `r`, induction gives

$$\|e_m\|_2\le r^m\|e_0\|_2+
\sum_{j=0}^{m-1}r^{m-1-j}\varepsilon_j.$$

For constant residual ceiling `epsilon`, the second term is at most `epsilon/gamma`.
State how the actual approximate kernel supplies that residual and preserves probability;
a minibatch covariance ceiling alone does not bound it. This provides a precise location
for discretization, biased gradients and numerical errors, rather than claiming that
annealing or unconditional acceptance erases them. Extend to inhomogeneous reference
factors only with their product bound and explicit target-change terms.

**Deliverable:** proposed `PredictiveErrorFromGap.lean` and `ApproximateKernelError.lean`,
with scalar Gaussian checks from T1. Couple these to predictive MCSE/bias reports in
crate R2–R3, not to loss-only ESS or unvalidated radial-shell diagnostics.

### Lean reuse ledger and execution order

All paths in this ledger are under `BookProof/MCMC/` unless stated otherwise.

| Existing result | Status within its model | Missing bridge |
|---|---|---|
| `MehlerEigenfunction.mehlerOp_physHermite` | U: 1D Gaussian identity | Product `L2` operator |
| `GegenbauerEigenvalue.pcnZonalEigen_tendsto` | U: quotient limit | Sphere operator/tail |
| `UnadjustedPCNGap.pcn_gap_uniform` | U: defined coefficient-form bound | Gaussian kernel map |
| `FockLangevinOperator.polyMul_mul` | U: polynomial ladder algebra | Posterior transform |
| `FockLangevinOperator.polyDrift_band` | U: polynomial core band | Nonpolynomial/error bound |
| `FockLangevinOperator.driftFormBound_holds` | U: constant drift bound | Actual symmetric form |
| `GeometricErgodicity.norm_iterate_sub_invariant_le` | U: decay from gap | Concrete gap |
| `ConvergenceTheorem.tvDist_le_half_l2` | U: density-ratio TV bound | Kernel density evolution |
| `BayesianTransformer/` | Geometry/noise source statements | Local compile/model audit |

Execute **T0 → T1 → T2 → T3** for the first concrete kernel, bias benchmarks and
exact MH-pCN theorem. These implement P0–P3; the scalar algebra in T1 can be prepared
while T0's integration/quotient bridge is being built. T4 implements P5 only after its
tail and coupling hypotheses are available. T5 connects the proof to P6 and the crate.
P4 remains a separate diffusion/Fock branch, with its ground-transform identity required
before reusing polynomial band estimates. Preserve the historical notes below, but use
this packet order rather than their old “Module 3 is the sole remaining blocker” claim.

| Review gate | Artifact | Failure interpretation |
|---|---|---|
| T0 | Actual reversible kernel and `L2` density action | Representation still unconnected |
| T1 | Exact stationary moments and finite-step bias | Kernel accuracy/stability failure |
| T2 | Controlled rank/complement tensor example | Dimension claim lacks a reference |
| T3 | Density/variance/Dirichlet comparison to TV | Target gap remains an assumption |
| T4 | Positive full-space block certificate | Tail/coupling exclusion missing |
| T5 | Predictive variance and residual budget | Precision/bias claim remains empirical |

For later Lean changes use the pinned local toolchain, build the affected MCMC modules
and audit binders/axioms. Audit the `BayesianTransformer` target separately rather than
inheriting prose compile claims. Tests should include the three analytic diffusion
benchmarks, Gaussian pCN moments, negative-spectrum/lazy examples and density-ratio
normalization. Documentation checks for this revision are relative links, whitespace and
doc-index freshness. No numerical or Lean result is newly claimed by editing this plan.

## Historical architecture and implementation notes

The revised work order above governs every “DONE”, convergence, symmetry and gap claim
below. In particular the spherical/Gaussian identification, KLMN inference, omitted
Gaussian potential, wavefunction evolution and general unadjusted-bias claims are
superseded by P0–P6. The new polynomial and constant-coefficient Lean lemmas remain
useful within their actual types; their existence does not discharge those bridges.

The original proposal sought a linear spectral formulation of the **pCNL MCMC convergence
theorem** using a **nested Fock-space representation**.

In this setting, the MCMC transition kernel is treated as a **self-adjoint/normal linear operator** acting on a Hilbert space of densities [1.1]. The finite-dimensional spherical harmonics (Gegenbauer polynomials) diagonalize the base diffusion, and their scaling limit yields the Fock-space number states (Hermite polynomials) as verified in *Timepiece* (`PhysHSGaussian`) [1.1].

---

### The Mathematical Architecture

```
 Finite Dimension d = α + 1 (S^{d-1})             Infinite Dimension (Fock Space S^∞)
 ────────────────────────────────────             ───────────────────────────────────
 Spherical Laplace–Beltrami Δ_{S^{d-1}}   ──────►   Ornstein–Uhlenbeck / Number Op N
                  │                                                  │
 Diagonalized by Gegenbauer C_n^{(λ)}     ──────►   Diagonalized by Hermite H_n / n!
 (PhysHSGaussian.gegenbauer)                      (PhysHSGaussian.physHermite)
                  │                                                  │
 Unadjusted pCN Spectrum: Λ_n^{(d)} → ρ^n ──────►   Fock Semigroup: e^{-t N}
                  │                                                  │
 Perturbation by Langevin Drift / Target ──────►   Linear Perturbation on Nested Fock
                  │                                                  │
 Certified Finite-d Spectral Gap γ_d      ──────►   Continuum Spectral Gap γ_∞ > 0
                  │                                                  │
                  └────────► MCMC Exponential Convergence ◄──────────┘
                              ‖P^m ν₀ - ν_∞‖ ≤ C (1 - γ)^m
```

---

### 1. The Diagonal Base: Gegenbauer at Finite $d$ and Hermite at $\infty$

#### A. Finite Dimension: The Hyperspherical Harmonic Decomposition
In any actual computer implementation, pCN operates on a large but finite number of coordinates $d = \alpha + 1$ (points on the hypersphere $S^{d-1}$) [1.1].
* The unadjusted pCN step $v = \rho u + \sqrt{1 - \rho^2}\, \xi$, with $\xi$ uniform on the unit sphere of $u^{\perp}$, is the isotropic rotation kernel on $S^{d-1}$ [1.1]: it commutes with $O(d)$ and preserves the uniform measure $d\sigma_{d-1}$.
* Because it commutes with the orthogonal group $O(d)$, **Schur’s lemma** forces the step to act on each space of hyperspherical harmonics by a single scalar.  The step is a *zonal* (convolution) kernel, so those scalars are fixed by the **zonal** harmonics alone — the ones that see a single coordinate projection $\langle y, e\rangle$.
* The zonal harmonic of degree $n$ is the **Gegenbauer polynomial** $C_n^{(\lambda)}$, with the degree parameter determined by the dimension,
  $$\lambda = \frac{d - 2}{2} = \frac{\alpha - 1}{2},$$
  orthogonal with respect to the weight $(1 - x^2)^{\lambda - 1/2} = (1 - x^2)^{(d-3)/2}$ (PDF Ch. 4.11, 24.5) [1.1].  This parameter is genuinely dimension-dependent: on $S^2$ ($d = 3$) it is the Legendre case $\lambda = 1/2$.  (Writing the exponent as $\alpha/2 = (d-1)/2$ is off by $1/2$ and would give $\lambda = 1$ instead of $\lambda = 1/2$ at $d = 3$; the eigenvalue below is not invariant under that relabelling.)
* **The eigenvalue is the zonal value at $\rho$.**  One step is the average over the sphere $\{y : \langle y, u\rangle = \rho\}$ — centre $\rho u$, radius $\sqrt{1 - \rho^2}$.  On the zonal harmonic $y \mapsto C_n^{(\lambda)}(\langle y, e\rangle)$ that average is the zonal addition theorem, and it carries the harmonic to itself with the factor the zonal function takes where the step's centre sits:
  $$P_0^{(d)} C_n^{(\lambda)}\big(\langle \cdot, e\rangle\big) = \Lambda_n^{(d)} \cdot C_n^{(\lambda)}\big(\langle \cdot, e\rangle\big), \qquad \Lambda_n^{(d)} = \frac{C_n^{(\lambda)}(\rho)}{C_n^{(\lambda)}(1)}$$
  (`BookProof.MCMC.pcnZonalEigen`, `BookProof/MCMC/GegenbauerEigenvalue.lean`).  **The finite-$d$ spectrum is $\Lambda_n^{(d)}$ — not $\rho^n$.**  The addition theorem is the one ingredient not in the corpus (§4 status); the eigenvalue `pcnZonalEigen`, its exact values below, and its limit are what is formalised.
* The spectrum, exactly (no `sorry`):
  - $\Lambda_0 = 1$ (`pcnZonalEigen_zero`): the uniform measure is invariant;
  - $\Lambda_1 = \rho$ **at every $d$** (`pcnZonalEigen_one`, for $\lambda \neq 0$ — the normalisation $C_n^{(\lambda)}(1)$ degenerates at $d = 2$): the first excited level is the Euclidean factor of the step, so the naive guess is exactly right here;
  - $\Lambda_2 = \dfrac{2\lambda(\lambda+1)\rho^2 - \lambda}{2\lambda(\lambda+1) - \lambda} = \dfrac{2(\lambda+1)\rho^2 - 1}{2\lambda + 1}$ (`pcnZonalEigen_two`), which is $\dfrac{3\rho^2 - 1}{2}$ on $S^2$ and equals $-\tfrac{1}{8}$ at $\rho = \tfrac{1}{2}$, while $\rho^2 = \tfrac{1}{4}$ (`pcnZonalEigen_two_ne_pow_two`).
* **$\rho^n$ is the $d \to \infty$ limit, not a finite-$d$ identity**: $\Lambda_n^{(d)} \to \rho^n$ (`pcnZonalEigen_tendsto`), through $\lambda^{-n} C_n^{(\lambda)}(x) \to (2x)^n / n!$ (`gegenbauer_div_pow_tendsto`).  That limit is §1.B, and at $d = \infty$ it is exact rather than asymptotic (`MehlerEigenfunction.mehlerOp_physHermite`).
* **The gap this leaves.**  The unadjusted gap is
  $$\operatorname{gap}\big(P_0^{(d)}\big) = 1 - \sup_{n \ge 1} \big|\Lambda_n^{(d)}\big|,$$
  whose degree-one contribution is $1 - \Lambda_1^{(d)} = 1 - \rho = 1 - \sqrt{1 - \beta^2} \approx \tfrac{1}{2}\beta^2$.  Two consequences of the formula above.  First, the higher levels are **not** smaller in modulus than the first — on $S^2$, $|\Lambda_2| = |3\rho^2 - 1|/2$ exceeds $\rho$ exactly when $\rho < 1/3$ — so the finite-$d$ gap is *strictly smaller* than $1 - \rho$.  Second, and unlike $\Lambda_1 = \rho$, the higher eigenvalues **do depend on $d$**.  So $1 - \rho$, and the gap used downstream, are statements about the limit spectrum $\rho^n$: they are what `BookProof.MCMC.UnadjustedPCNGap.pcn_gap_uniform` certifies for the Fock weight $\rho^{2N}$, and that constancy in $d$ is precisely what makes the $d \to \infty$ step of §1.B meaningful.

#### B. The Infinite-Dimensional Limit via `PhysHSGaussian`
As the number of modes $d \to \infty$ ($\alpha \to \infty$), *Timepiece* has already formalized the exact scaling limit in Lean 4 [1.1]:
1. **Weight Convergence:**
   $$\lim_{\alpha \to \infty} \left(1 - \frac{x^2}{\alpha}\right)^{(\alpha-1)/2} = e^{-x^2/2}$$
   (`BookProof.PhysHSGaussian.weight_tendsto_gaussian`) [1.1].
2. **Polynomial Convergence:**
   $$\lim_{\alpha \to \infty} \left(\frac{\alpha}{2}\right)^{-n/2} C_n^{(\alpha/2)}\left(\sqrt{\frac{2}{\alpha}} x\right) = \frac{H_n(x)}{n!}$$
   (`BookProof.PhysHSGaussian.gegenbauerScaled_tendsto_hermite`) [1.1].
3. **Operator Limit:**
   The spherical generator $\Delta_{S^{d-1}}$ converges strongly to the **Fock number operator** $N = \sum a_k^\dagger a_k$, and the base pCN operator converges to the free second-quantized contraction semigroup:
   $$P_0^{(\infty)} = \rho^N = e^{-t N}$$
   which is completely diagonalized by the multi-mode Hermite basis (`hermiteMvBasis`) [1.1].

---

### 2. Formulating pCNL as a Linear Perturbation in Nested Fock Space

The full pCNL algorithm modifies the base diffusion by adding the Langevin drift derived from the target potential $\Phi(u)$ and a Metropolis acceptance filter [1.1].

Instead of treating this as a non-linear trajectory, *Timepiece* allows us to express the **entire transition operator $P_{\text{pCNL}}$ as a linear matrix operator** on the Fock space:

1. **The State Space:**
   Represent probability densities as vectors in the Hilbert space $L^2(\mu_{\text{Mehler}})$ [1.1]. The Hermite states $|n\rangle$ (or finite-dimensional Gegenbauer states $|n\rangle_d$) form an orthonormal basis [1.1].
2. **The Linear Expansion:**
   The full pCNL operator splits into three linear components:
   $$P_{\text{pCNL}} = P_0 + K_{\text{drift}} + K_{\text{reject}}$$
   * $P_0$ is diagonal: $\langle m | P_0 | n \rangle = \rho^n \delta_{mn}$.
   * $K_{\text{drift}}$ represents the gradient drift $-\frac{\beta^2}{2} \nabla \Phi$. In the Hermite basis, $\nabla \Phi(x)$ is a polynomial operator; using the canonical creation/annihilation relations ($a, a^\dagger$), it acts as a **finite-band hopping matrix** (PDF Ch. 33.1, `ChapterCarlemanGeneralHop`) [1.1]:
     $$x_j = \frac{a_j + a_j^\dagger}{\sqrt{2}}, \quad \partial_j = \frac{a_j - a_j^\dagger}{\sqrt{2}}$$
   * $K_{\text{reject}}$ accounts for the Metropolis acceptance step $\alpha(u, v) = \min(1, \dots)$.
3. **The Symmetrized Generator:**
   Under the ground-state transformation $\psi = \sqrt{\pi_{\text{target}}} f$, the continuous-time limit of $P_{\text{pCNL}}$ becomes a **self-adjoint Schrödinger operator**:
   $$H_{\text{pCNL}} = N_{\text{Fock}} + V_{\text{eff}}(a, a^\dagger)$$
   where $V_{\text{eff}}$ is expressed directly in the ladder operators of the nested Fock space [1.1].

---

### 3. The MCMC Convergence Theorem via Spectral Decomposition

With $P_{\text{pCNL}}$ formulated as a self-adjoint contraction on $L^2(\pi)$, the MCMC convergence theorem becomes an exact corollary of spectral theory:

> **Scope of the word "self-adjoint".**  This requires a kernel reversible with respect to $\pi$:
> true for the Metropolis-filtered pCNL (detailed balance is enforced by the filter) and for the
> pure pCN step at *every* $\beta$ (the Gaussian prior is exactly invariant), but **not** for the
> unadjusted SG-pCNL chain, whose invariant measure is $\pi$ only up to $O(\beta)$.  Everything
> below is therefore a fixed-$\beta$ statement about the kernel's own invariant measure; the
> annealed version used in the experiments is a separate theorem, and is where the schedule
> correction of the review note at the end of this document applies.

#### A. Spectral Resolution
By the spectral theorem for self-adjoint operators (formalized in `BookProof.ChapterSpectralMultiplication`) [1.1]:
$$P_{\text{pCNL}} = |\Psi_0\rangle\langle \Psi_0| + \int_{-1}^{1 - \gamma} \lambda \, dE(\lambda)$$
* $\Psi_0 = \sqrt{\pi_{\text{target}}}$ is the unique invariant ground state with eigenvalue $\lambda_0 = 1$.
* The spectral gap is:
  $$\gamma = 1 - \sup \{ |\lambda| : \lambda \in \sigma(P_{\text{pCNL}}), \; \lambda \ne 1 \} > 0$$

#### B. The Complete Linear Convergence Proof
For any initial probability distribution $p_0$ whose wave-function is $\Psi_{\text{init}} = \sum_{k=0}^\infty c_k |k\rangle$:
$$P_{\text{pCNL}}^m \Psi_{\text{init}} = c_0 \Psi_0 + \sum_{k=1}^\infty \lambda_k^m c_k |k\rangle$$
Subtracting the target equilibrium distribution $\Psi_0$ (where $c_0 = 1$ by normalization):
$$\|P_{\text{pCNL}}^m \Psi_{\text{init}} - \Psi_0\|^2 = \sum_{k=1}^\infty |\lambda_k|^{2m} |c_k|^2 \le (1 - \gamma)^{2m} \sum_{k=1}^\infty |c_k|^2 \le (1 - \gamma)^{2m} \|\Psi_{\text{init}}\|^2$$
By the Born-to-variation bound, the total variation distance satisfies:
$$\|\mathcal{P}^m(u_0, \cdot) - \pi_{\text{target}}\|_{\text{TV}} \le C(u_0) (1 - \gamma)^m = C(u_0) e^{-m \log\left(\frac{1}{1-\gamma}\right)}$$
**Convergence is established as an expansion in the complete basis of Fock/Gegenbauer modes.**

---

### 4. Research & Formalization Plan for Lean 4

```
[Module 1: Gegenbauer Spectrum of Spherical pCN]
Prove: P₀^{(d)} C_n^{(λ)} = Λ_n^{(d)} C_n^{(λ)} on S^{d-1},  λ = (d-2)/2
                         │
                         ▼
[Module 2: Scaled Limit to Fock Space Semigroup]
Connect Gegenbauer eigenvalues to Fock number states using:
PhysHSGaussian.gegenbauerScaled_tendsto_hermite
                         │
                         ▼
[Module 3: Ladder-Operator Representation of pCNL Drift]
Expand Langevin drift as a polynomial in (a, a†) on the Hermite core
using BookProof.ChapterCarlemanGeneralHop
                         │
                         ▼
[Module 4: Coercivity and Spectral Gap Certification]
Apply BookProof.ChapterSirkDiffusiveDecay.isCoercive_compress
to certify that the gap γ_d ≥ γ_min > 0 uniformly in d
                         │
                         ▼
[Module 5: Spectral MCMC Convergence Theorem]
Deduce geometric ergodicity in total variation from the operator gap
```

#### Detailed Milestone Targets in `BookProof`

* **Milestone 1 (`BookProof/MCMC/GegenbauerEigenvalue.lean`):**
  Formalize the action of the spherical convolution operator on the Gegenbauer basis, with the
  degree parameter `λ = (d − 2)/2` fixed by the dimension.  The eigenvalue is the Gegenbauer
  quotient at `ρ`, i.e. `Λ_n^{(d)}` (§1.A) — not `ρ^n`:
  ```lean
  theorem pcn_gegenbauer_eigenvalue (d : ℕ) (n : ℕ) (ρ : ℝ) :
    sphericalMarkovStep d ρ (gegenbauer n ((d - 2) / 2)) =
      pcnZonalEigen n ((d - 2) / 2) ρ • (gegenbauer n ((d - 2) / 2))
  ```
  (`pcnZonalEigen n lam ρ` in `BookProof.MCMC.GegenbauerEigenvalue`; the `ρ^n` form is the
  `d → ∞` limit of this — `pcnZonalEigen_tendsto` — not a finite-`d` identity.)
* **Milestone 2 (`BookProof/MCMC/GegenbauerToHermiteLimit.lean`):**
  Prove that the finite-dimensional transition matrix elements converge to the Fock matrix elements:
  ```lean
  theorem pcn_matrix_elements_tendsto_fock (m n : ℕ) :
    Tendsto (fun d => pcnGegenbauerMatrix d m n) atTop (𝓝 (fockNumberMatrix m n))
  ```
* **Milestone 3 (`BookProof/MCMC/FockLangevinOperator.lean`):**
  Represent the Langevin drift operator on the Hermite core using the creation and annihilation operators `ccr_annA_creA` [1.1]:
  ```lean
  def pcnlHamiltonian (V : Polynomial ℝ) : Operator (ℓ²(ℕ)) :=
    numberOp + polynomialDrift (creOp + annOp)
  ```
* **Milestone 4 (`BookProof/MCMC/CertifiedMCMCGap.lean`):**
  Use `ChapterSirkDiffusiveDecay` [1.1] to prove that coercivity of the Hamiltonian ensures exponential decay:
  ```lean
  theorem pcnl_spectral_gap_positive (d : ℕ) (V : AdmissiblePotential) :
    ∃ (γ : ℝ), γ > 0 ∧ ∀ ψ ⊥ groundState, ⟪ψ, pcnlOperator ψ⟫ ≤ (1 - γ) * ‖ψ‖²
  ```
* **Milestone 5 (`BookProof/MCMC/ConvergenceTheorem.lean`):**
  Package the final convergence theorem:
  ```lean
  theorem pcnl_mcmc_geometric_convergence (p₀ : ProbabilityDensity) :
    ∃ (C : ℝ) (γ : ℝ), γ > 0 ∧
    ∀ (m : ℕ), totalVariation (iterateMCMC m p₀) targetDensity ≤ C * (1 - γ)^m
  ```

##### Module 3's missing theorem, stated: the `ε`-regularized relative form bound for `K_drift`

The status notes below record "the relative form bound that makes `K_drift` a bounded perturbation
of `P₀`" as the missing piece of Module 3.  It can be stated exactly, and stating it is worth doing
because the statement pins down both the hypothesis and — through its constant — why the gap cannot
come from it.  *(Stated 2026-11-03, and now also stated in Lean.*  `FockLangevinOperator.lean` §5
carries the target as `DriftFormBound : Prop` over the same `CoreCoeff d` and the same ladder words
as the rest of that module, together with the `ℓ²` pairing `corePair`, the number form `numberForm`
and the coefficient drift `driftOpCoeff` (`K_drift = −Σⱼ bⱼ ∂ⱼ`, `∂ⱼ = (aⱼ − aⱼ†)/√2`), with the
constant `B²d/(2δ) + Bd` and `d` the mode count `P`.  It **compiles and is a `def` returning a
`Prop`**, so the development stays `sorry`-free — but at that date it was a *target*, not a theorem:
what a proof still needed was the Hermite expansion of `∇Φ_ε` into those ladder coefficients, plus
the three core identities the chain uses (adjoint pairing, Cauchy–Schwarz in `ℓ²`, and
`Σⱼ(‖aⱼc‖² + ‖aⱼ†c‖²) = 2⟪c,Nc⟫ + d‖c‖²`).

*(Proved 2026-11-08: §10 of the chapter supplies the three identities and §11 the assembly, so
`DriftFormBound` is a theorem — `driftFormBound_holds`; §12 then supplies the coefficient family
`bⱼ = (β²σ²/2)·∂ⱼΦ` with the `ε` isolated in `B = (β²σ²/2)M_ε`, and §13 the semiboundedness
corollary, `−C‖c‖² ≤ ⟪c, (N + K_drift)c⟫`.  The hypothesis's `M_ε` is itself a theorem for the
additive normalization: `BayesianTransformer.epsProj_fderiv_le` proves `‖∇(g ∘ Ŵ)‖ ≤ 2K/ε` on
`‖W‖ ≥ ε`, and `driftScale_eps_arch` reads it as `B = β²σ²K/ε`.  What remains outside the
formalization is the *core-side* realization of that gradient as the multiplication operator
`polyMul (∂ⱼΦ_ε)` with the same bound.)*

**Hypothesis.**  Let `Φ_ε` be the potential of the `ε`-regularized architecture,
`Ŵ = W/(‖W‖_F + ε)` with `ε > 0`, so that the implementation's Theorem 1 applies to it with
constant
$$
M_\varepsilon = K/\varepsilon ,
$$
`K` depending only on the depth, the sequence length and the `ε`-scaled hyperparameters.  In Lean
this is `BayesianTransformer.epsProj_fderiv_le` for the additive form `Ŵ = W/(‖W‖ + ε)`, with the
constant `2K/ε` (`K` absorbing the factor 2 — the sphere projection `W/‖W‖` costs `1/ε` because it
is scale invariant, the additive map does not), and `normalized_fderiv_le_uniform` for the
scale-invariant form on `‖W‖ ≥ ε`.  The
*exact* normalization (`ε = 0`) is excluded: `d(W/‖W‖_F)` carries a factor `1/‖W‖`, unbounded at
`W = 0`, so there `M = ∞` (the implementation's M4+ test records the NaN at `θ = 0`).  Write
$$
B := \frac{\beta^2\sigma^2}{2} M_\varepsilon
$$
for the coefficient of the drift in the SG-pCNL step (`K_drift = −Σ_j b_j ∂_j` with
`|b_j| ≤ B`, `b_j = (β²σ²/2)·∂_jΦ_ε`, `∂_j = (a_j − a_j†)/√2`), and let `N = Σ_j a_j†a_j` be the
Fock number operator with form domain `Q(N^{1/2})`.

**Statement (zero relative bound).**  For every `δ > 0` and every `ψ ∈ Q(N^{1/2})`,
$$
\big|\langle\psi, K_{\mathrm{drift}}\,\psi\rangle\big|
  \;\le\; \delta\,\|N^{1/2}\psi\|^2 \;+\; C_\delta\,\|\psi\|^2 ,
\qquad
C_\delta = \frac{B^2P}{2\delta} + BP
  = \frac{(\beta^2\sigma^2 M_\varepsilon)^2 P}{8\delta} + \frac{(\beta^2\sigma^2M_\varepsilon)P}{2} .
$$
`δ` is arbitrary, i.e. the relative bound is zero — the perturbation is *infinitesimally* form-small
with respect to `N`.

**Proof.**  (i) `|b_j| ≤ B` by the hypothesis.  (ii) Cauchy–Schwarz over the `P` coordinates,
$$\Big|\sum_j \langle\psi, b_j\,\partial_j\psi\rangle\Big|
  \le B \sum_j \|\psi\|\,\|\partial_j\psi\|
  \le B\sqrt{P}\,\|\psi\|\,\|\nabla\psi\|,
\qquad \|\nabla\psi\|^2 = \sum_j \|\partial_j\psi\|^2 ,$$
and the oscillator identity `−Δ = 2N + P − |x|²` gives
`‖∇ψ‖² = ⟨ψ,(−Δ)ψ⟩ = 2‖N^{1/2}ψ‖² + P‖ψ‖² − ⟨ψ,|x|²ψ⟩ ≤ 2‖N^{1/2}ψ‖² + P‖ψ‖²` (`|x|² ≥ 0`).
(iii) `√(2‖N^{1/2}ψ‖² + P‖ψ‖²) ≤ √2‖N^{1/2}ψ‖ + √P‖ψ‖` and `2ab ≤ δa² + b²/δ` on the two
thereby produced terms.

**Status (2026-11-03): proved — in the corpus Fock model, which is where the analytic machinery
lives.**  `FockLangevinOperator.lean` §6 now proves the bound as a theorem, not a target:
`driftField f = creVec f − annVec f` is the plan's `−Σⱼ bⱼ ∂ⱼ` (with `f = b/√2`),
`abs_re_inner_driftField_le` is the `N^{1/2}` estimate `|Re⟪u, K u⟫| ≤ 2‖f‖·⟪u,Nu⟫^{1/2}·‖u‖`, and
**`driftField_relative_form_bound`** is
`|Re⟪u, K u⟫| ≤ t·⟪u,Nu⟫ + (‖f‖²/t)·‖u‖²` for every `t > 0` — relative bound zero, on
`FockAlg = Conf →₀ ℂ`, reusing `BookProof.FockFieldPerturbation`'s `numberQuad_eq_sum`,
`norm_annVec_le` and `two_mul_sqrt_le`.  With `|bⱼ| ≤ B` and `f = b/√2` one has `‖f‖² ≤ B²d/2`, so
this gives the displayed `C_δ` with **no linear `Bd` term** — the `N^{1/2}` estimate is exact, and
the plan's constant was the cruder ℓ¹-over-modes version.  So KLMN's hypothesis is met at the
operator level for the drift as the corpus models it.

What is *not* done, and is the reason the `CoreCoeff` statement above stays a `Prop`: no transport
of a form bound along the identification exists.  This is the same *kind* of gap `cftproof.md` item
3 records for the OS identity: mathematics done in one modelling of configuration space, a
transport missing between it and the model the surrounding development uses.

**The index half of that identification is now proved (2026-11-04)**, in `FockLangevinOperator` §7:
`idxEquiv d : (Fin d → ℕ) ≃ (Fin d →₀ ℕ)` is `Finsupp.equivFunOnFinite.symm` — on a *finite* mode
set an occupation vector and a finite multiset of modes are the same data, since every `Fin d → ℕ`
is finitely supported — and `natDeg_idxEquiv` shows the grading is read through it,
`(idxEquiv d n).sum (fun _ m => m) = natDeg n`.  So the sector structure of §4's band lemmas
(`hopWord_band`, `driftOp_band`, `pcnlHamiltonian_band`) is the sector structure of the Fock model,
not merely analogous to it.

The remaining half is the mode *set*: the toolbox's modes are all of `ℕ` (`Conf = ℕ →₀ ℕ`, and
`creVec`/`annVec` take `ℕ →₀ ℂ`), while the chapter's are `Fin d`.  A bound proved there must first
be restricted to the sector carried by the first `d` modes (i.e. `f` supported in `Fin d`), and the
`ℓ²` spaces reindexed along `idxEquiv`; neither is done, and both are transport rather than
analysis.

**Correction (2026-11-08):** the KLMN inference below is superseded by P3. The real
constant field `creVec - annVec` is skew-symmetric; its size bound does not prove that
its sum with `N` is self-adjoint. A transformed generator needs its own symmetric form.

**Historical claim.** `K_drift` is symmetric and `N^{1/2}`-form-bounded with relative bound zero, so
**KLMN** applies: the form `q(ψ) = ‖N^{1/2}ψ‖² + ⟪ψ, K_drift ψ⟫` is closed and bounded below on
`Q(N^{1/2})`, hence `pcnlHamiltonian = N + K_drift` is a self-adjoint operator bounded below.  That
is what makes §2's "linear perturbation" an operator at all, and it is independent of the
Metropolis filter.

**What it does not buy — and why Module 4 must not use it for the gap.**  `C_δ` scales like
`ε^{-2}`, the drift entering the energy quadratically.  At the implementation's numbers
(`P = 16 672`, `β = 0.3`, `σ = 0.35`, `M_ε = 10⁶`, `δ = 1/2`) it is `≈ 5.1×10¹¹`.  The gap is
`inf{⟪ψ,(N + K_drift)ψ⟫ : ψ ⊥ φ₀, ‖ψ‖ = 1}` minus the bottom of the spectrum, and a form bound
locates the numerator only to within `±C_δ`; no choice of `δ` makes that informative, because
enlarging `δ` shrinks `C_δ` only by moving the estimate into the `‖N^{1/2}ψ‖²` term that the gap
bound needs.  So a relative-form argument of this shape certifies self-adjointness and semiboundedness
and **nothing about `γ`**.

The gap has to come from the *sign structure* of the drift, not its size.  After
`ψ = √π_target · f` the form is a Dirichlet form with effective potential
$$
V_{\mathrm{eff}} = \tfrac14|\nabla\Phi_\varepsilon|^2 - \tfrac12\,\Delta\Phi_\varepsilon ,
$$
so the correct Module 4 hypothesis is Bakry–Émery (`Hess Φ_ε ≥ λ I` gives gap `λ`), or the
coercivity of `V_eff` that `ChapterSirkDiffusiveDecay.isCoercive_compress` consumes — **not** a
uniform gradient bound.  Revised target:

```lean
-- Module 4 target, revised: the gap comes from V_eff, not from ‖∇Φ‖ ≤ M
-- (the Hop/band structure of FockLangevinOperator is what makes V_eff a well-defined
--  multiplication operator on the core; it says nothing about its sign, which is why the
--  Hessian hypothesis below cannot be dropped)
theorem pcnl_spectral_gap_of_hessian (λ : ℝ) (hλ : 0 < λ)
    (hHess : ∀ θ, λ • (1 : H) ≤ Hessian Φ_ε θ) :
    ∃ γ, γ = λ ∧ ∀ ψ ⊥ groundState,
      ⟪ψ, pcnlHamiltonian ψ⟫ ≥ γ * ‖ψ‖ ^ 2
```

The ε-regularized bound above then remains what it is: the operator-theoretic _license_ for
`pcnlHamiltonian`, with the constant that shows the licence is not a gap certificate.

#### Status (2026-10-30)

Three of the five milestones are covered — **Module 1** (both its finite-`d` spectrum and, in the
`d → ∞` form, the eigenfunction identity itself), **its limit with Module 2**, and **Modules 4–5**
— and all are `sorry`-free, with `#print axioms` showing only `propext`, `Classical.choice`, `Quot.sound`.

* **Module 1, its output** — `BookProof.MCMC.UnadjustedPCN`
  (`BookProof/MCMC/UnadjustedPCNGap.lean`).  On the core `CoreCoeff d = (Fin d → ℕ) →₀ ℂ` of
  `BookProof.ReferenceGap`, a multi-index `n` has **degree** `natDeg n = ∑ i, nᵢ` (the
  hyperspherical-harmonic order) and pCN eigenvalue `ρ ^ N`, so its `L²` weight is
  `pcnWeight ρ n = ρ ^ (2N)` and the unadjusted step's form is `pcnForm ρ c = ∑ n, ρ^(2N)‖c n‖²`.
  The certified statements: `pcnWeight_le_gap` (every excited mode carries at most `ρ²`, from
  `ρ^(2N) ≤ ρ²` for `0 ≤ ρ ≤ 1`), **`pcnForm_le`** (`‖P₀ c‖² ≤ ρ²‖c‖²` off the vacuum), and
  **`pcn_gap_uniform`**: `(1 − ρ²)‖c‖² ≤ ‖c‖² − ‖P₀ c‖²` with **no dependence on `d`** — §1.A's
  "the eigenvalues `λ_n^{(d)}` are completely independent of `d`", together with
  `pcn_norm_le` (`‖P₀ c‖ ≤ ρ‖c‖`, via `√(ρ²) = ρ`) and `pcnWeight_degree_one` (`λ₁ = ρ`, so the
  gap is `1 − ρ`).  This is the constancy in `d` that makes the `d → ∞` limit in §1.B meaningful.
* **Modules 4–5** — `BookProof.MCMC.GeometricErgodicity`
  (`BookProof/MCMC/GeometricErgodicity.lean`): `iterate_orthogonal_of_fixed`,
  `norm_iterate_le_of_orthogonal` (the gap propagates to every iterate),
  **`norm_iterate_sub_invariant_le`** (`‖P^m ψ − ⟪φ,ψ⟫φ‖ ≤ (1−γ)^m ‖ψ − ⟪φ,ψ⟫φ‖`) and
  `tendsto_iterate`.  The two halves are joined by `pcn_geometric_ergodicity`, which is that bound
  with the gap `γ = 1 − ρ` that `pcn_gap_uniform` supplies, i.e. §3.B's expansion
  `‖P^m Ψ − Ψ₀‖ ≤ ρ^m ‖Ψ − Ψ₀‖` in the basis of modes.

* **Module 3, its structural half** — `BookProof.MCMC.FockLangevin`
  (`BookProof/MCMC/FockLangevinOperator.lean`).  On the same core, `raiseIdx`/`lowerIdx`/`stepIdx`
  are `a_j†`/`a_j` as operations on occupations, with `natDeg_raiseIdx` (`N ↦ N + 1`) and
  `natDeg_lowerIdx_le` (`N ↦ ≤ N`); `stepAmp` is the Hermite/Fock matrix element `√(n_j+1)`,
  `√(n_j)`, and `stepAmp_norm_le` bounds every step amplitude by `√(N+1)` on the degree-`N`
  sector — the growth the plan's relative-bound argument needs.  `hopStep`, `hopWord` and
  `driftOp` are the one-step, word and drift-monomial operators, and the **finite-band property**
  is `hopStep_band`, **`hopWord_band`** (a word of length `k` maps `{N ≤ N₀}` into
  `{N ≤ N₀ + k}`) and **`driftOp_band`** (a monomial family of degree `≤ K` maps into
  `{N ≤ N₀ + K}`).  `numberOp` is the diagonal `N`, and `pcnlHamiltonian_band` states the §2.2
  operator shape `P₀`-diagonal-plus-finite-band-drift on the core.
  **§9 adds the Hermite multiplication law**, the letter-level dictionary Module 3's expansion
  consumes: `mulHermite` is the symmetrised one-mode word `(1/√2)(a_j† + a_j)` on the coefficient
  core, **`mulHermite_eq_ladderWords`** splits it into its two ladder words `(1/√2)a_j†` and
  `(1/√2)a_j`, and **`driftOpCoeff_eq_ladderWords`** separates `∇Φ`'s coefficient operator
  symmetrically into the lowering sum `−(b_j/√2)` and the raising sum `+(b_j/√2)`.  What is *not*
  The linear structure the expansion needs is proved too: `hopStep_add`/`hopStep_smul` make a
  ladder letter `ℂ`-linear on the core (`hopStep_sum` for finite families), `hopWord_append`
  composes words (`hopWord (w₁ ++ w₂) = hopWord w₂ ∘ hopWord w₁`, with `hopWord_two`/`hopWord_single`
  the spelled-out cases), and `mulHermite_add`/`mulHermite_smul` give the same for the
  multiplication law.  **`mulHermite_comp`** is the first multimode case: `x_k x_j` is `1/2` times
  the sum of the four length-two ladder words `hopWord [(j,ε),(k,δ)]`, i.e. the `2^2` word family
  with the amplitudes carried by the `hopStep`s.
  **§9.2 closes the general case (2026-11-04).**  `mulWords js` is the word family of a mode list
  (one ladder letter per mode, both raise and lower), **`sum_mulWords_cons`** splits its sum at a
  leading mode — the two words are distinct and the families over different tails are disjoint
  because `List.tail` recovers the tail, so the `Finset.biUnion` is a genuine direct sum and no
  reindexing is assumed — **`mulWords_card`** is the `2^k` count
  `(mulWords js).card = 2 ^ js.length`, `hopWord_add`/`hopWord_smul` are linearity of a word, and
  **`mulHermiteList_eq_ladderWords`** is the expansion itself: for every mode list `js`,
  `mulHermiteList js c = (2^{-length js/2}) • ∑_{w ∈ mulWords js} hopWord w c`.
  So a product of `k` multiplication laws — hence every monomial of the potential `Φ` — is the
  `2^k`-word family, with the Hermite amplitudes `√(nⱼ+1)`, `√(nⱼ)` carried by the letters
  (`mulHermiteList_pair` recovers the `k = 2` case of §9.1).  What remains of Module 3's expansion
  is the induction that *feeds* it: a general `Φ` is a sum of monomials `∏ⱼ xⱼ^{mⱼ}`, so
  interpolating a polynomial from its monomial expansions is an `MvPolynomial` induction the
  corpus does not yet carry — bookkeeping of the same kind, on a different object.
  **§9.3–9.4 carry it out (2026-11-08), so that sentence is now closed.**  §9.3 proves the
  *mathematical* input the bookkeeping needs — that distinct modes commute: `stepIdx_comm` (the
  two occupation updates touch disjoint coordinates), `stepAmp_stepIdx_of_ne` (a letter's
  amplitude is untouched by a letter at another mode), hence `hopStep_comm` and
  **`mulHermite_comm`**; then `mulHermiteList_perm` (a product of laws depends only on the
  *multiset* of its modes, by `List.Perm.recOnSwap'`), the mode list `monomialList` (mode `j`
  repeated `m j` times), `monomialList_append_perm` / `mulHermiteList_monomialList_add`
  (exponents add: `m + n` is `m` then `n`), `mulHermiteList_monomialList_comm`, and
  `monomialList_single` (`X j ↦ mulHermite j` at the generators).  §9.4 is the `MvPolynomial`
  induction itself: `polyMul Φ` is the weighted sum of the monomial word families over
  `Φ.support` — Module 3's `xⱼ = (aⱼ + aⱼ†)/√2` expansion for an arbitrary potential, with every
  monomial expanded into its `2^{deg}` ladder words by §9.2 — and `polyMul_add`, `polyMul_sum`,
  `polyMul_monomial`, `polyMul_X`, `polyMul_add_arg`, `polyMul_smul_arg` are its structural
  lemmas, culminating in **`polyMul_mul`**: `polyMul` is multiplicative, i.e. the algebra
  homomorphism `X j ↦ mulHermite j` on `MvPolynomial (Fin d) ℂ`.  §9.4 states as its boundary
  the same interpolation for the *derivative* polynomials `∂ⱼ Φ` that `K_drift = −Σⱼ bⱼ ∂ⱼ`
  needs, and `K_reject`, which is not finite-band at all.
  **§9.5 closes the derivative boundary (2026-11-08).**  Mathlib's algebraic `∂ⱼ` is
  `MvPolynomial.pderiv` (there is no `MvPolynomial.derivative` in this pin), and `polyMul`
  applies to it verbatim: `pderiv_monomial` sends `monomial m a` to `monomial (m − single j 1)
  (a · m j)`, so `polyMul_derivative_monomial` expands one monomial of the gradient with the
  exponent lowered (`lowerExp m j`, an `abbrev` — `Finsupp` subtraction on `ℕ`-valued families is
  truncated, which is right: an absent mode leaves the exponent and `m j = 0` kills the term),
  **`polyMul_derivative`** is the full `Φ.support` interpolation
  `polyMul (pderiv j Φ) c = ∑ m ∈ Φ.support, (coeff m Φ · m j) • mulHermiteList (monomialList
  (lowerExp m j)) c`, **`polyMul_derivative_eq_ladderWords`** spells the same sum out as §9.2's
  explicit `∑_{w ∈ mulWords js} hopWord w c` family, and `polyMul_derivative_X` checks
  `∂ⱼ xₖ = δⱼₖ` against `polyMul_X`'s `X j ↦ mulHermite j`.  So `∂ⱼ Φ` — like `Φ` itself — is a
  finite sum of ladder words, with `polyMul_C`/`polyMul_one`/`monomialList_zero` for the constant
  case.  The chapter remains `sorry`-free — `lake build BookProof.MCMC.FockLangevinOperator` is
  green and `#print axioms` on the new theorems gives only `propext, Classical.choice,
  Quot.sound` — and **Module 3's expansion is now complete in both directions**.  What was still
  missing after that turn: the *composition* `−Σⱼ (β²σ²/2)(∂ⱼ Φ)(x)·∂ⱼ` of §9.5's operator with the
  ladder letter `∂ⱼ = (aⱼ − aⱼ†)/√2` of §5, and `K_reject`.
  **§9.6–9.7 close the composition (2026-11-08, same day).**  §9.6 is the *band* half of the
  expansion — `mulHermite_band` (one law is two ladder letters), `mulHermiteList_band` (a product
  of `k` laws maps `{N ≤ N₀}` into `{N ≤ N₀ + k}`), `monomialList_length` (a monomial's mode list
  has one letter per unit of degree, via `Fin.sum_univ_def`), `natDeg_ofFinsupp`,
  `polyMul_monomial_band`, and **`polyMul_band`**: a potential of degree `≤ K` maps `{N ≤ N₀}`
  into `{N ≤ N₀ + K}` (`polyMul_band_sector` is the sector form), so truncating at degree `N₀`
  couples only to degrees `≤ N₀ + K` — §2.2's finite-band property for an *arbitrary* `Φ`, not only
  for the linear potentials of §5.  §9.7 is the operator itself: `diffHermite` is the letter
  `∂ⱼ = (aⱼ − aⱼ†)/√2` on the core, **`polyDrift Φ`** is the composition
  `−Σⱼ polyMul (∂ⱼ Φ) ∘ diffHermite j` (the derivative applied first, then multiplication by
  `∂ⱼ Φ`), and its ladder-word family is proved twice — `polyDrift_eq_ladderWords` (one sum per
  mode and monomial, the derivative's letters still inside `hopWord w (diffHermite j c)`) and
  **`polyDrift_eq_hopWords`** (genuine ladder words, via `hopWord_diffHermite`: the letter `∂ⱼ` at
  the head of the derivative's word `w`, the two halves subtracting with the `1/√2`
  normalizations explicit).  `driftOpCoeff_eq_neg_sum_diffHermite` shows the linear case collapses
  to §5's `driftOpCoeff`, so §9.7 generalizes that drift rather than replacing it.  **§9.8 is the
  band of the drift itself (2026-11-08, third landing that day).**  `diffHermite_band` (the letter
  moves `N` by at most one), `natDeg_lowerExp` (a *lowered* exponent loses exactly one degree —
  the equality form `natDeg_lowerIdx_of_pos` of §1's `natDeg_lowerIdx_le`), and
  **`polyDrift_band`**: a potential of degree `≤ K` maps `{N ≤ N₀}` into `{N ≤ N₀ + K}`, the
  derivative's loss and the letter's gain cancelling, so `K_drift` has band `K`
  (`polyDrift_band_sector` is the sector form).  That is §2.2's finite-band property for the drift
  the plan actually uses, with the sharp constant — a truncation at `N₀` couples only to
  `≤ N₀ + K`, not `≤ N₀ + K + 1`.
  **§9.9–9.10 add the estimate and the operator (2026-11-08, fourth landing that day).**  §9.9 is
  the *size* of the drift, in the `ℓ¹` mass `coreL1 c = ∑ₙ ‖c n‖`: `hopStep_l1_le` (one letter
  multiplies the mass by at most `√(N+1)` on `{N ≤ N}`, straight from `stepAmp_norm_le`),
  `hopWord_l1_sector` (a word of length `k` multiplies it by at most `(√(M+1))^k`, where
  `M ≥ N + k` bounds the degrees the word meets), and **`polyDrift_l1_le`**:
  `coreL1 (polyDrift Φ c) ≤ driftL1Bound Φ M * coreL1 c` with an *explicit* sector constant,
  built from §9.2's `2^k` word count and the degree bound `k ≤ deg Φ`.  §9.10 is the pCNL shape
  for a polynomial potential: **`pcnlPolyHamiltonian Φ = numberOp + polyDrift Φ`** with
  **`pcnlPolyHamiltonian_band`** (degree `≤ K` maps `{N ≤ N₀}` into `{N ≤ N₀ + K}` — the same
  finite-band property §4 proves for a word list, now for the drift operator itself) and
  `polyDrift_linear` (a linear `Φ` gives exactly §5's `driftOpCoeff b`, so the new Hamiltonian
  generalizes the `driftOpCoeff` one rather than replacing it).  What is still missing is the
  *`ℓ²`* step that would turn that size estimate into `DriftFormBound`.
  **§10 supplies the analytic half of that step (same day).**  The *coordinates* of one letter come
  first — `hopStep_coord_lower` (`(aⱼc)(m) = √(mⱼ+1)·c(m+eⱼ)`, with the saturation case `mⱼ = 0`
  folded in because the extra preimage carries amplitude `√0 = 0`) and `hopStep_coord_raise`
  (`√(mⱼ)·c(m−eⱼ)`, one preimage since raising is injective, `raiseIdx_injective`) — then the
  letter norms, by a support bijection in each direction: **`coreNormSq_hopStep_lower`**
  (`‖aⱼc‖² = ∑ₙ nⱼ‖c n‖²`) and **`coreNormSq_hopStep_raise`** (`∑ₙ (nⱼ+1)‖c n‖²`).  Their mode
  sums give `∑ⱼ ‖aⱼc‖² = ⟪c, Nc⟫` and `∑ⱼ ‖aⱼ†c‖² = ⟪c, Nc⟫ + d‖c‖²`, and hence the
  **oscillator identity** `Σⱼ (‖aⱼc‖² + ‖aⱼ†c‖²) = 2⟪c, Nc⟫ + d‖c‖²` — the input the plan's chain
  calls analytic rather than bookkeeping.  What remains of `DriftFormBound` is therefore only the
  assembly: Cauchy–Schwarz in the core pairing `corePair` and the `2ab ≤ δa² + b²/δ` step with the
  plan's constant.  `K_reject`, a multiplication operator and not finite-band at all, stays outside
  the model.
  **§11 supplies the assembly, so `DriftFormBound` is a theorem (2026-11-08, fifth landing that
  day).**  `coreNorm` is the core `ℓ²` norm, `corePair_eq_sum` makes the pairing's ambient finset
  bookkeeping, `corePair_smul`/`corePair_add`/`corePair_finset_sum` give conjugate-linearity in the
  second slot, and **`norm_corePair_le`** is Cauchy–Schwarz, `‖⟪c, c'⟫‖ ≤ ‖c‖·‖c'‖`.  Cauchy–Schwarz
  in the *mode* index (`sum_coreNorm_hopStep_le`) reads §10's oscillator identity as
  `∑ⱼ ‖aⱼc‖ ≤ √d·√⟪c, Nc⟫`, and `sqrt_add_le` with `two_mul_le_add_div`
  (`√(x+y) ≤ √x + √y`, `2uv ≤ δu² + v²/δ`) spend the free parameter on the number form.
  **`driftOpCoeff_form_bound`** is the estimate with the plan's constant,
  `‖⟪c, K_drift c⟫‖ ≤ δ·⟪c, Nc⟫ + (B²d/(2δ) + Bd)·‖c‖²` for every `δ > 0`, and
  **`driftFormBound_holds`** is §5's `DriftFormBound` itself: `K_drift` is infinitesimally
  form-small with respect to `N`, the KLMN hypothesis that makes `N + K_drift` self-adjoint and
  bounded below.  **§12 supplies the coefficient family and §13 the boundedness below (sixth landing
  that day).**  `driftWeight` is the SG-pCNL weight `β²σ²/2` and `driftScale β σ M = (β²σ²/2)M` the
  constant the form bound consumes; `driftOperator β σ Φ` is `polyDrift Φ` scaled by that weight,
  and **`driftOperator_linear`** says a linear `Φ` is exactly §5's `driftOpCoeff` with
  `bⱼ = (β²σ²/2)·∂ⱼΦ` — the identification `bⱼ = (β²σ²/2)·∂ⱼΦ_ε` closed on the operator side, where
  the assumed `|bⱼ| ≤ B` becomes the potential's gradient bound `M`.  **`driftOperator_form_bound`**
  carries that `M` into the constant, and **`driftOperator_form_bound_eps`** with `M_ε = K/ε` is the
  formula this document displays, `(β²σ²M_ε)²/(8δ) + β²σ²M_ε/2` times `d‖c‖²`: the `ε` enters
  through `M_ε` and nowhere else.  §13 then takes the KLMN step the bound exists for:
  `corePair_numberOp_re` identifies the pairing with the number form,
  **`semibounded_of_form_bound`** turns a form bound with `δ ≤ 1` into
  `−C‖c‖² ≤ ⟪c, (N + K)c⟫`, and **`pcnlDrift_semibounded_eps`** instantiates it, so `N + K_drift`
  is bounded below by a constant of order `ε⁻²`.  The `M_ε` that enters that constant is itself a
  theorem for the concrete potential: `BayesianTransformer.epsProj_fderiv_le` gives
  `‖∇(g ∘ Ŵ)‖ ≤ 2K/ε` on `‖W‖ ≥ ε` for `Ŵ = W/(‖W‖ + ε)`, and `driftScale_eps_arch` turns it into
  `B = β²σ²K/ε`.  Outside the model only `K_reject` (a multiplication operator, not finite-band)
  and the core-side realization of that gradient as `polyMul (∂ⱼΦ_ε)` remain.

* **Module 1 proper, in the `α → ∞` Gaussian form — DONE (2026-10-30)** — `BookProof.MCMC.MehlerEigenfunction`
  (`BookProof/MCMC/MehlerEigenfunction.lean`, no `sorry`).  This is the eigenfunction identity the
  status note above recorded as missing, in the form §1.B actually uses (the `d → ∞` limit whose
  eigenfunctions are the Fock number states rather than the hyperspherical harmonics):
  **`mehler_hermite`** — for `ρ² ≤ 1`,
  `∫ Hₙ(ρ x + √(1 − ρ²) y) e^{−y²} dy = √π · ρⁿ · Hₙ(x)`, with `Hₙ = PhysHSGaussian.physHermite`
  the physicists' Hermite polynomials of the Fock-number model.  The proof is a two-step
  induction on the Hermite recurrence: `stein_mehler` (the Stein/Mehler recursion
  `∫ y Hₙ(ρx+√(1−ρ²)y) e^{−y²} = √(1−ρ²) n ∫ Hₙ₋₁(ρx+√(1−ρ²)y) e^{−y²}`, from the line-derivative
  integration by parts `integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable`), then
  `physHermite_succ_succ` closes the recurrence with
  `mehlerCoupling_sq` (`ρ² + (√(1 − ρ²))² = 1`).  Supporting lemmas: `exists_physHermite_abs_bound`
  (`|Hₙ z| ≤ C (1 + |z|)ⁿ`), `integrable_pow_mehler` (every Gaussian moment of a shifted Hermite
  polynomial is finite), `integral_exp_neg_sq`.  The operator form is `mehlerOp` with
  **`mehlerOp_physHermite`** (`T_ρ Hₙ = ρⁿ Hₙ`, one pCN step at `d = ∞`), `mehlerOp_vacuum`
  (`T_ρ 1 = 1`) and **`mehler_gap`** (`1 − ρ ≤ 1 − ρⁿ` for `0 ≤ ρ ≤ 1`, `n ≠ 0`): §1.A's gap
  `1 − √(1 − β²)` survives the limit, so the two halves of §1 now meet — the Fock weight `ρ^{2N}`
  is `d`-independent (`pcn_gap_uniform`) and its spectrum is `ρⁿ`, which is the limit of the
  finite-`d` spectrum `Λₙ^{(d)}` (`pcnZonalEigen_tendsto`), and the eigenfunction converges to `Hₙ`
  (`gegenbauerScaled_tendsto_hermite`).  Consequently Module 2's matrix elements `⟨n|P₀^{(d)}|n⟩`
  are equal to the Fock value `ρⁿ` *in the limit*, which is the statement proved.

* **Module 1, the finite-`d` spectrum — DONE, superseding the plan's `ρⁿ` claim (2026-10-30)** —
  `BookProof.MCMC.GegenbauerEigenvalue` (`BookProof/MCMC/GegenbauerEigenvalue.lean`, no `sorry`).
  This is the finite-`d` half: the plan's `λₙ^{(d)} = ρⁿ` holds only at `n ≤ 1`, and fails for `n ≥ 2`:
  **`pcnZonalEigen`** is `Λₙ^{(d)} = Cₙ^{(λ)}(ρ)/Cₙ^{(λ)}(1)`, `λ = (d−2)/2`, the value the zonal
  harmonic takes at the point a rotation carries the pole to.  Proved exactly:
  `pcnZonalEigen_zero` (`Λ₀ = 1`), **`pcnZonalEigen_one`** (`Λ₁ = ρ` at every `d` — the plan's `λ₁`
  is right), `pcnZonalEigen_two` (`Λ₂ = (2λ(λ+1)ρ² − λ)/(2λ(λ+1) − λ)`), and
  **`pcnZonalEigen_two_ne_pow_two`** (`Λ₂ = −1/8 ≠ ρ² = 1/4` on `S²` at `ρ = 1/2`, the Legendre
  case `λ = 1/2`), which *refutes* the finite-`d` `ρⁿ` form the plan states.  The bridge to §1.B is
  **`gegenbauer_div_pow_tendsto`** (`λ⁻ⁿCₙ^{(λ)}(x) → (2x)ⁿ/n!`, by two-step induction on the
  Gegenbauer recurrence) and **`pcnZonalEigen_tendsto`** (`Λₙ^{(d)} → ρⁿ`), so the two forms are
  `Λₙ^{(d)}` at finite `d` and `ρⁿ` in the limit, and they agree exactly where `MehlerEigenfunction`
  says they do.  **Module 1 is therefore complete in both forms**: the finite-`d` spectrum is
  `Λₙ^{(d)}` (not `ρⁿ`), and its `d → ∞` limit is the Fock spectrum `ρⁿ`, with the plan's former
  `ρⁿ` claim replaced by `Λₙ^{(d)}` rather than annotated.  The one thing not formalised is the
  *operator* identity on the sphere — `P₀^{(d)} Cₙ^{(λ)} = Λₙ^{(d)} Cₙ^{(λ)}` as an identity of
  functions on `S^{d−1}` — which needs the spherical measure and the Gegenbauer product formula
  (the zonal addition theorem); `pcnZonalEigen` states its eigenvalue, and the eigenvalue's closed
  form, its limit, and the refutation are what the gap argument uses.

**Not proved, and how the files say so.**  The finite-`d` *operator* diagonalisation (the Gegenbauer
product formula on the sphere) is not formalised, and — as `pcnZonalEigen_two_ne_pow_two` shows —
its eigenvalue cannot be `ρⁿ`.  For Module 3, the Hermite expansion of a given potential's `∇Φ`
into a concrete ladder-word family (needing `x_j = (a_j + a_j†)/√2` and the Mehler measure) is no
longer missing: both expansions are proved (`polyMul_mul` for the multiplication laws, §9.4;
`polyMul_derivative` and `polyMul_derivative_eq_ladderWords` for the derivative polynomials, §9.5),
and their *composition* is `polyDrift` (§9.7), weighted to `driftOperator` (§12).  The relative
form bound that makes `K_drift` a bounded perturbation of `P₀` is stated for the `ε`-regularized
potential in the subsection above, with the constant `(β²σ²M_ε)²P/(8δ) + (β²σ²M_ε)P/2` and the
reason that constant cannot supply the gap; stated in Lean as `DriftFormBound`
(  `FockLangevinOperator` §5, a `Prop` on the coefficient core), **proved** in Lean on the core in
  `FockLangevinOperator` §11 (`driftFormBound_holds`, 2026-11-08) and independently in the Fock
  model as `driftField_relative_form_bound` (`FockLangevinOperator` §6), with the model
  identification now carried out as well (§7–§8, 2026-11-04: `idxEquiv` (occupation vectors on
  `d` modes *are* finite multisets), `natDeg_idxEquiv` (the grading is the particle number),
  `reindex` / `sum_sq_reindex` / `numberForm_reindex` (the core `ℓ²` and its number form read in
  the multiset indexing), `sectorVec` / `l2norm_sectorVec` (a `Fin d` coupling as a one-particle
  vector on the first `d` modes) and **`driftField_sector_relative_form_bound`** (the §6 bound with
  the `Fin d` constants), plus `InSector`, `numberQuad_eq_sum_fin`, `annA_eq_zero_of_sector` and
  `InSector.driftField` for the sector).  The gradient bound itself is in Lean:
`BayesianTransformer.epsProj_fderiv_le` proves `‖∇(g ∘ Ŵ)‖ ≤ 2K/ε` on `‖W‖ ≥ ε` for the additive
normalization `Ŵ = W/(‖W‖ + ε)`, and `driftScale_eps_arch` reads it as the drift's
`B = β²σ²K/ε`.  What is *not* in Lean is its core-side realization — that the same number bounds
the multiplication operator `polyMul (∂ⱼΦ_ε)` on `CoreCoeff`, which is the explicit hypothesis
`hgrad` of §12 and §13 —
and the Metropolis filter
`K_reject` — the last is a multiplication operator and is not finite-band at all, so nothing in
`FockLangevinOperator` describes it.  The pCNL operator's own gap therefore remains a hypothesis
of the Module 4–5 bound, as §2 anticipates; and no total-variation bound is derived — §3.B's
Born-to-variation step `‖ν − π‖_TV ≤ ½‖dν/dπ − 1‖_{L²}` is stated as the boundary in
`GeometricErgodicity`'s docstring.

#### Review of the implementation's empirical claims (2026-11-03)

An external review of the implementation write-up (`test/unfer/ngpt.md`; the review calls it
`test/unfer/pcnl.md`, which does not exist) was checked against that document and against the
engine (`unfer/pcnl/src/{sampler,model,normalize,task,experiment}.rs`).  Three of its five points
are confirmed (one with a sharper fix than the review gives), one is overstated, and one is partly
right but rests on a factual error that has to be corrected before it can be used; the checked
verdicts are below.  Nothing in the Lean status above changes; what changes is what the empirical
artifacts may be cited *for*, and two hypotheses this plan carries.

**(1) The step-size schedule is applied to the wrong quantity.**  The engine's update is
`θ' = √(1−β²)θ + βξ − (β²σ²/2)g` (`sampler.rs`: `drift_coeff = β·β·σ·σ/2`, noise `βξ`), so the
coefficient multiplying the gradient is `h_t = β_t²σ²/2`, not `β_t`.  With
`β_t = β₀(1+γt)^{−κ}` and `κ ∈ (0.5, 1]` one gets `Σ h_t < ∞`: the chain has finite total
mobility and freezes before reaching the target, so the write-up's "asymptotic convergence to the
true posterior" does **not** follow from its Robbins–Monro conditions — they are imposed on `β_t`
while the drift and the injected variance are both `O(β_t²)`.  The write-up's own schedule test is
the evidence: it reports `Σ β_t²` saturating at the analytic ceiling `β₀²/(γ(2κ−1)) = 900`, i.e.
confirming the sum is *finite*.  (Checked: with `β₀ = 0.3, γ = 10⁻³` the partial sum is `479` at
`t = 2×10⁶` and converges to `900` from below; at `κ = 1/2` it follows `(β₀²/γ)·ln(1+γt) = 684` at
the same horizon, i.e. it grows.)  (*Adaptation:* the review's fix "κ ≤ 0.5" is right for divergence
of the mobility, but the variance condition needs the other end too — the correct window is
`Σβ_t² = ∞` and `Σβ_t⁴ < ∞`, i.e. `κ ∈ (1/4, 1/2]`, e.g. `κ = 1/2`.  Only the bias of the drift
term needs `β_t → 0`; the pCN proposal itself is exactly invariant at every `β`, which is why the
condition lands on `h_t` and not on `β_t`.)  **Consequence for this plan:** the gap `γ` of §3 is a
*fixed-`β`* statement about the kernel; an annealed chain converging to `π` is a different theorem
with its own hypotheses, and the implementation's run is not evidence for it.

**(2) The uniform gradient bound is finite but empty in practice.**  Verified: `normalize.rs` uses
`W/(‖W‖+ε)` with `EPS = 1e-6`, and the crate's own M4+ test asserts that the exact normalization's
gradient grows like `1/‖W‖` while the `ε`-regularized one stays below `1/ε`.  So Theorem 1's
"universal finite `M`" is at best `K/ε ≈ 10⁶K` against a shell radius `σ√P ≈ 45`, and at `W = 0`
the exact normalization is undefined (the same M4+ test records the NaN), so "sup over all of
`ℝ^P`" is false without the `ε`.  Per step that permits a drift of `(β²σ²/2)M ≈ 5.5×10³` at
`β = 0.3, σ = 0.35`, two orders above the shell it is supposed to confine.  (*Adaptation:*
"vacuous" is too strong — the bound is finite; what fails is that it is not small where it
matters, and it is attained only in the compact region `‖W‖ ≲ ε`.)  **Consequence for this plan:** `K_drift` cannot be called a *small* bounded
perturbation of `P₀` on the strength of a gradient bound.  Module 3's relative form bound — now
proved in `BookProof.MCMC.FockLangevinOperator` §11 — is the load-bearing item, and it holds for the
`ε`-regularized potential with a constant `∝ 1/ε`; relative *to the number operator* it is the
sharper reading, useful in the low-number sector.

**(3) The prior-width sweep measures nothing about the posterior.**  Verified: `σ` enters only
through the noise scale `βξ` and the drift coefficient `β²σ²/2`, and because the potential is
scale-invariant (up to the `ε`), `g(σu) = (1/σ)g(u)`; the update in `u = θ/σ` is then `σ`-free,
`u' = √(1−β²)u + βξ' − (β²/2)g(u)` with `ξ' ~ N(0, I)`.  The four
runs agreeing to "28.5 % / 1.3848" is therefore a consistency check of the implementation's scale
invariance (the crate's M2 test asserts the same for `θ → 0.5θ`), not a property of the target.
(*Measured 2026-11-03, four widths `σ ∈ {0.35, 2, 4, 8}` × three seeds at `κ = 1/2`: within a seed
the pCNL predictive is identical to four decimals at all four widths (`Δ`NLL `= 0.0000`, twelve of
twelve cells), and so are `R̂`(loss), ESS and the acceptance rate — the whole report differs only in
the radius (`∝ σ`) and the *reported* `θ`-gradient (`∝ 1/σ`: 4 460 → 390, ratio 11.43 = 4/0.35) —
while between seeds the same configuration moves by 0.018 nats and 5.5 points.  The standard
softmax stack, whose potential is not scale-invariant, does *not* enjoy the identity: it explodes
at step 3 at `σ = 0.35` and step 2 at `σ = 4`.  So the identity is a property of the architecture,
which is exactly the write-up's §6.5.1(a).*)
**Consequence for this plan:** `σ` is a units parameter and no `σ`-sweep can be cited for or
against the gap; consistently, `pcn_gap_uniform` is independent of both `σ` and `d`.

**(4) The `P/2` "entropy wall" is a category error, and the write-up's own table refutes it.**
Since the likelihood depends on `ŵ` alone and the prior induces Haar measure on directions (§3.3 of
the write-up), there is no directional prior pull: the posterior's *radial* marginal equals the
prior's `χ_P` because the likelihood is constant along each ray (exactly so for the scale-invariant
potential, up to the `ε` in `W/(‖W‖+ε)` for the implementation's), and the chain starts and stays on
the shell — so "`P/2` nats from mode to shell" is not a cost the sampler ever pays.  The rule is
also contradicted by its own shift cell (`2048·(ln 4 − 0.894) = 1008 > 276` predicts learnable;
measured 28.5 %, the uniform predictor).  The correct statement is two-part: whether the
*posterior* concentrates in direction is a volume question — the favourable directions occupy a
fraction `≈ exp(−N·KL)` of `S^{P−1}` — and whether the *chain* finds them is a reachability
question from the shell (which the write-up also identifies: burn-in erases `θ_A`'s direction).
**Consequence for this plan:** "does the posterior concentrate" is a property of the target and
"does the chain find it" a property of the kernel at fixed `β`; neither is a `P/2` threshold, and
the plan should not adopt the heuristic.  (*Adopted 2026-11-03:* the write-up's §6.4 now withdraws
the rule and states the two-part version — the radial marginal is the prior's `σχ_P` unchanged
because the likelihood is constant on rays, and concentration in direction is a log-volume
competition `NΔ ≳ N·D(Δ)` against Haar measure — with §6.4.2 read as the experiment that
discriminates target-side from reachability, in favour of reachability.)

**(5) The baseline comparison is weak, but for a different reason than the review gives.**  The
review's diagnosis — "no normalization" — is **wrong**: `model.rs`'s standard variant uses affine-
free pre-LN `(x−μ)/√(var+1e-5)`, residual addition, `1/√d` logit scaling and the same attention, i.e.
an ordinary pre-LN transformer in miniature.  What does weaken the comparison is the optimizer: the
deterministic pre-train is heavy-ball SGD at `lr = 0.6` with clip `5.0` for *both* variants
(`experiment.rs: pretrain_lr 0.6`; `task.rs: PRETRAIN_CLIP`), which diverges on the unnormalized
variant (loss 851) *before* the sampler starts — so "explodes at step 3" tests the sampler from a
broken `θ_A`, confounding architecture with pre-train stability, as the write-up says itself
("its deterministic pre-train had already blown up to loss 851").  A fair Phase-0 comparison needs
both variants pre-trained to a comparable loss (e.g. Adam at the `0.05` the Task-B baseline already
uses).  (*Run 2026-11-03, three seeds:* with Adam at `lr = 0.05` the standard variant's pre-train is fixed
in 3/3 (`2.1850 → 1.7453`, `2.2037 → 2.0435`, `2.2016 → 2.3151`; `acc_A` 17.2–28.9 % against
chance 12.9 %) and its unadjusted chain still explodes in 3/3, at steps 4–5, while the cosine
variant survives 3/3 with BMA 11.7–13.3 % and NLL 2.189–2.198.  So Phase 0 survives the confound
being removed, and the write-up's §6.5.1(b) records it.  The σ-sweep was likewise re-run at
`κ = 1/2` on the same three seeds (§6.5.1(a)): within a seed `σ` changes the predictive by 0.0000
nats in all three, while between seeds it moves by 0.018 nats — one order of magnitude more than
any `σ` effect, which is what makes the σ row a units check rather than a posterior measurement.)  The citation is misattributed as well: Kim, Papamakarios & Mnih (ICML 2021) bounds the
Lipschitz constant of self-attention *as a function of its input* `X`; it says nothing about
weight-space Hessians, and nothing about them diverging exponentially during sampling — the write-
up's §2.3 attributes that second claim to the paper.

**(5b) The step-size confound underneath (5), measured (2026-11-04).**  The review's "sensible learning
rate" phrasing pointed at a real second confound that (5) did not remove: the drift is `h_t·g_t`, so
the standard stack was run at a step size nobody chose, and "it explodes" could be a statement about
that number rather than about the geometry.  `unfer/pcnl/examples/step_scale_control.rs` measures the
normalized arm's own maximum scaled gradient `C` per seed and re-runs the standard stack with its
drift capped at `C` (`SgPcnlState::grad_norm_cap`, default `None`; a unit test pins that the cap is
exactly `h_t·cap` and bit-identical when non-binding).  Reference configuration, 1 000 steps, two
chains, three seeds: the uncapped standard gradient reaches `2.9×10¹²–1.5×10²¹ × C` and the chain
dies at step 5–6; capped, it survives 3/3 (reduced configuration too, 2 000 steps), so **the
numerical explosion is a step-size claim and "an unnormalized transformer cannot be sampled" is
withdrawn.**  Three things keep this from rescuing the baseline: a capped gradient is not a gradient
field, so the capped chain has no Gibbs target and no posterior reading; it still overshoots the
shell `3.6×` (radial max 110–164 against 45.19); and its kept-draw NLL is `4.11–5.72` nats against
`2.08` for the uniform predictor — overconfident-and-wrong, where the cosine arm is
calibrated-uniform.  **Consequence for this plan:** the architectural claim that survives is
step-scale invariance (the reason `β` needs no tuning, and the same property `pcn_gap_uniform` has
in `σ` and `d`), not unsamplability; the write-up's §6.5.2, §6.4/§6.5.1(b) and §2.3 now say so, and
its Theorem 1 is restated for `Π_ε` with `M(ε) = Θ(1/ε)` plus a proposition that the exact
normalization is unbounded — which is (2)'s adaptation applied to the theorem's hypothesis rather
than to its use.  The Lee-Yang/`K_drift` priority list is untouched: this is empirical scope, not
analysis.

**(6) The headline predictive is the chain's, not the posterior's (2026-11-06).**  The write-up's
§6.3–§6.4 read the 11.7 % BMA (chance 12.5 %) as the posterior having "retreated to the calibrated
near-uniform predictor".  Measured with no chain at all (`pcnl/examples/basin_posterior`:
self-normalized importance sampling, 128 isotropic tangent probes per width, weights
`exp(−N·ΔL)`), the cosine target's own predictive is **48.3–49.0 %** at anchor NLL 1.3136 — four
times chance and 6.1 points below the Adam fine-tune — with the weights flat to 2.3 mrad and the
ESS collapsing by the 5 mrad grid point (one-nat radius `8.6 × 10⁻⁴` rad).  The 11.7 % / 2.1863 is
instead indistinguishable from the 11.72 % / 2.1818 a Haar-typical direction predicts (the row in
(4)), i.e. kept draws at Haar-typical separations (`√(2/P) ≈ 11` mrad) where the target has no
mass — absence, not dilution.  A chain that *does* start in the mass still reports a diluted value:
49.02 % at 400 steps → 46.39 % at 10 000, per-draw NLL 14 nats above the target's (≈ 3 mrad out,
3.5× the one-nat radius), and a fixed-radius shell jump accepting 78 % reaches 36.40 % per draw
after diffusing `7.6 × 10⁻²` rad.  Four independent chains measure that creep as a random walk —
growth exponent 0.509 (0.504–0.513), pairwise angle 89.7°, split-`R̂` 1.50 — i.e. a budget inside
the relaxation time `P/(K r₁²) ≈ 8 × 10³` steps, not a biased kernel.  **Consequence for this
plan:** (4) is strengthened rather than weakened — the posterior *does* concentrate in direction, so
"does the posterior concentrate" is settled for this toy and "does the chain reach it" is the whole
question, now with a measured scale: the mass sits in a cap a few milliradians across, a fixed-`β`
ambient step of 0.3 rad never enters it, and an `R̂` on the loss is blind to the failure because the
region those chains mix over is flat.  Modules 1–5 are untouched: the fixed-`β` gap is a statement
about a kernel on a space the chains were not on.

**What this leaves standing.**  Modules 1–5 and the `sorry`-free status are untouched: the finite-`d`
spectrum `Λ_n^{(d)}`, its `ρ^n` limit, the Mehler eigenfunction identity and the quotient-norm bound
are theorems about the pCN kernel at fixed `β` (and, for the decomposition, about `Ω`), none of
which the review disputes.  The load-bearing open item is unchanged and is now sharper: `K_drift`'s
relative form bound, stated for the `ε`-regularized potential and with the `1/ε` made explicit,
because the implementation's numbers cannot supply a small `M`.  The plan should also say plainly
that its §3 spectral resolution needs a *reversible* kernel — true for the Metropolis-filtered
pCNL and for pure pCN at every `β`, not for the unadjusted SG-pCNL chain of the write-up's §4.1 —
so the fixed-`β` gap of the unadjusted chain is a statement about a measure that is `π` only up to
`O(β)` — which is exactly the gap the schedule correction is meant to close.

**One measurement sharpens the plan's own priority list (2026-11-03).**  The write-up's
§6.5.1(c) diagnoses the reduced configuration's mixing: `R̂`(loss) ≈ 1 there marks chains that found
the *same* mode, and that mode is usually poor (23–28.5 % against a best found 54.7 %); with 8
chains or 30 000 steps the ensembles split (`R̂` 1.7–6.7) and the BMA *rises* to 48.8–54.7 %.  In
seven seeds the family that splits changes (pCNL max 1.235, SGLD 4.385, MH 2.816), so it is the
noise stream, not the transition.  For this plan the consequence is that "chain mixing across
modes" is the binding open item — not a footnote to the gap: a fixed-`β` spectral gap of §3 says
nothing about an ensemble that has not left its mode, and the BMA numbers the plan quotes must be
read as "one mode" values.  Nothing in Modules 1–5 changes, and `DriftFormBound` (stated in
`FockLangevinOperator` §5, proved in §11) is unaffected: it is a statement about the operator, not
about where the chain sits.

---

### Summary of Advantages of this Approach

1. **No Non-Linear Trajectory Tracking:** MCMC convergence is proven strictly through **linear algebra and functional analysis** in the nested Fock space [1.1].
2. **Explicit Basis Functions:** The convergence rate is decomposed along the **Gegenbauer harmonics at finite $d$** and along the **Hermite/Fock number states as $d \to \infty$** [1.1].
3. **Conditional certification via SIRK:** a verified operator, tail estimate, ground
   projection and independent spectral exclusion can support a rate certificate. Ladder
   expansion alone does not establish those inputs or replace implementation diagnostics;
   use P5's acceptance criteria.
