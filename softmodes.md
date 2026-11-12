# Soft modes in the Mehler / nested-Fock Yang–Mills formalism

## External-source audit for the nested Hamiltonian (2026-11-11)

This section replaces the earlier external-source commentary. The mathematical work order
remains S0–S4 below, in the nested-Fock/Mehler/Hashimoto/SIRK formalism. Its endpoints are
an absolute inner form bound (target 1), or separation above an identified inner ground
space (target 2), followed by the appropriate outer lift and certified approximation.
Neither target requires a Wightman construction or a four-dimensional Euclidean measure.
The optional comparison with those theories belongs to [cftproof.md](cftproof.md), B0–B3.

### Physical state: one outer particle per informed spatial point

The empty outer vacuum represents mathematical emptiness. The physical prior has one
outer particle at each point of 3D space about which field information is specified;
information at several points can give a many-outer-particle state. `N_out = 1` is a
single spatial contribution, not a global restriction on the real-world model. The
outer-free Hamiltonian retains the interacting field content inside each inner state.

Read [book.tex](book.tex), “Free field parametrization in Statistical Field Theory”:
recursive second quantization; the number-density proposition at finitely many distinct
spatial points; and its normalization using local tensor factors with at most one point.
Specify joint priors and spatial localization as well as the local occupation. In a
finite resolved implementation use stated spatial supports and embeddings into the
existing spatial/field/jet coordinates; refinement is a separate representation task.

Physical expectations are taken in that populated prior, not in empty outer space.
`dΓ(O)` and products of number densities can have nonzero expectations there. Their
annihilation of `Ω_out` is not an obstruction and requires no number-changing repair.
Distinguish the energy to populate empty outer space (target 1) from an excitation gap
inside a populated physical sector (target 2 with the relevant sector and ground space).
Neither identifies a generic information prior with a ground or stationary state.

### What the three folders contribute

For snapshot revisions and the exact scope of the review, see `cftproof.md`,
“Sources, versions and what was actually inspected”. We inspected the
[October source](../OpenAI-YM-20261028/README.md), the
[independent review](../YM/README.md), and the
[Balaban drafts](../Yang--Mills-LLM-experiment/README.md), including the YM4 assembly PDF.
These provide proof-contract examples and candidate analytic techniques. No external
construction is identified with our inner operator, physical space or outer Hamiltonian.
In particular, absence of a gap theorem there does not prove or refute coercivity here.
The draft corpus warns that its claims remain tentative, including QED3/YM3.

* The October `PublicTheory.lean` separates positivity from a spectral gap, and
  `ChallengeSpec.lean` binds multiple properties to the same witness. Reuse the discipline,
  without adding its Wightman axioms to S2's assumptions or acceptance criteria.
* The review's `AcceptanceSpec.lean` fixes normalization and observable identities before
  accepting conclusions. For S0–S4 the corresponding contract is the **actual nested**
  `h`, its Mehler realization, core, physical sector and outer lift, held fixed throughout.
* The Balaban conditional-law checklist suggests how to audit a future Gaussian
  comparison, but its CP box is not closed. Its volume-first scalar SU(2) construction
  and its reflection hypotheses are not hypotheses of this Hamiltonian programme.

### Corrections to the earlier analogy

**The two targets are not the external open-question list.** An inner Hilbert space used
as the one-particle input to `dΓ_out` need not be a relativistic one-particle mass-shell
subspace. Identifying such a space would require translations, dispersion and observable
intertwiners. Our target 2 is an inner excitation separation; it is not construction of
Wightman single-particle states. Target 1 gives an outer-vacuum gap within the nested
model, independently of whether any Euclidean/Wightman identification can be proved.

**Retain the vacuum in gap statements.** For `H = dΓ(h)` a successful target 1 yields
`H ≥ m N_out ≥ m(I − P_Ω)`, and therefore no spectrum in `(0,m)`.
A claim that the joint energy–momentum projection of a ball containing zero vanishes
would incorrectly remove the vacuum. For a degenerate ground space use its full
projection. Positive energy and non-freeness are neither replacement bounds nor evidence
for either S2 target. A short-distance exclusion of finite Wick profiles is not a spectral
exclusion suitable for Temple's inequality.

**Coordinate degree and local-field weight are different.** The source-present
`totalDegree_magPoly_le ≤ 2` and `totalDegree_magWeight_le ≤ 4` count ordinary polynomial
degree in 99 independent coordinates. `idxD` is one such coordinate, of polynomial
degree one; it is not an extra differentiation operation on a spacetime label. The
external curvature/derivative filtration and its gauge/Bianchi quotient require a new
dictionary in cftproof B0. No OPE exponent or stress-trace coefficient follows from our
degree bounds. Retain the bounds as growth-class inputs to S2, not as analytic domination.

### Refined S0–S4 deliverables

1. **S0 contract:** record the normalized Mehler measure, unitary, actual momentum action,
   common core and closure. Match `B = L + Q` and all constants to that same operator.
   Existing conjugation/norm identities are reusable; Gaussian representation alone adds
   no confinement and does not identify the physical kinetic form with Hermite degree.
2. **S1 channel audit:** classify zero/flat directions of the complete magnetic form and
   kinetic operator together. For each proposed confinement mechanism state which variables
   carry derivatives, which are parameters, and whether a physical reduction is used.
   This is the relevant lesson from separating background construction, linear inversion
   and Gaussian integration in the Balaban diagram: a local Hessian bound does not yet
   control the global physical operator. Prove any averaging or Schur-complement error.
3. **S2 estimate packet:** choose target 1 or 2 before estimating. Supply the positive
   constant, invariant sector/ground projection, dependence on coupling and dimension,
   extension from core to closed form, and an explicit theorem for the unchanged `h`.
   Keep graph-norm domination and absolute lower-edge coercivity separate: each needs
   its own proof. Quartic degree, ESA and nonnegative form data alone prove neither gap.
4. **S3 approximation packet:** bind Hashimoto/SIRK's generator and bounded resolvent
   to that same closure. Retain rational approximation, solve defects, orthogonality,
   rounding and full basis tails separately. Select shifts from the actual spectral or
   numerical-range bounds; retain the paper's finite shift-budget restrictions below.
   Keep an independently proved separation threshold for Temple; a positive lattice
   probe or short-distance coefficient from the external construction cannot provide it.
   Record the populated spatial prior used as initial data and its outer occupation;
   the empty outer start alone cannot test physical field predictions. A multi-point
   prior requires the corresponding many-particle evolution and joint observables.
5. **S4 acceptance packet:** use one identified operator/core/sector for both the
   analytic bound and numerical certificate. Check the outer lift and full ground space,
   then follow §M4.9 before §M4.3. Record endpoint binders, axiom closure and source hashes.
   Give reference-model diagnostics their own labels rather than calling them physical
   certificates. No Euclidean reconstruction is an additional S4 completion requirement.

The next task remains the QYM analytic row of
[CURRENT_WORK_ORDER.md](CURRENT_WORK_ORDER.md). A useful candidate method may be adapted
from a draft only after its hypotheses are proved for this inner operator. If the method
also gives the SM graph estimate, pass its precise statement and constants to P4 of
[SM_ESA_COMPLETION_PLAN.md](SM_ESA_COMPLETION_PLAN.md); a QYM gap alone does not supply it.

## Revised work package (2026-11-08)

This revision supersedes the roadmap and completion claims of the dated phases below **as a
reading guide for this file**. Those notes remain implementation history. It does not replace
the programme ordering in `CURRENT_WORK_ORDER.md`: the non-abelian one-particle form bound
remains open, and the mass-gap certificate route still has its sector gate (§M4.9 before M4.3).
No Lean proof was compiled for this revision. **U** below denotes an existing mathematical
interface/result within its stated model, **C** a missing hypothesis or bridge, **N** an invalid
inference, and **B** a scope boundary. A theorem's binders, not its name, determine its scope.

### Sources and the object to be bounded

Read these sources by heading rather than by mutable line number:

* [book.tex](book.tex): the recursive second-quantization paragraph beginning “Since the
  second-quantization procedure can be applied recursively”; “Relation with the BRST
  formalism”; “Pure SU(3) Yang-Mills theory”. These fix the nested construction, the
  auxiliary role of BRST, and the $99=3+24+72$ continuous coordinates with ghost grading.
* [Book/FreeField.lean](Book/FreeField.lean): “Why the Gaussian Is the Uniform Measure on
  the Infinite Sphere: the Mehler Limit”; [Book/SolovayTensor.lean](Book/SolovayTensor.lean):
  “Only the Mehler Measure on the Infinite Part”. These supply the Gaussian coordinate
  substrate, not a dynamical Yang–Mills gap.
* [Book/YangMillsQuantization.lean](Book/YangMillsQuantization.lean): “The Weyl-Gauge
  Quadratic Form and the Friedrichs Route”. Read its energy-origin discussion together
  with the $\mu N$ boundary below; a change of one-particle origin changes outer dynamics.
* [Hashimoto–Nodera](../papers/Hashimoto.md), Definition 2.4, §4 and Theorem 4.1:
  bounded resolvents and rational approximation of operator $\phi$-functions.
* [BookProof.lean](BookProof.lean): the live proof-source inventory. The generated
  `YANG_MILLS_MASS_GAP_LEAN.md` corpus snapshot is produced on demand, is not tracked in this
  repository and is absent from this tree; check its declarations against the source modules and
  distinguish abstract implications from concrete instantiations.

Use $\mathcal K$ for the inner field/configuration Hilbert space and $h$ for its
gauge-fixed Hamiltonian. Its implemented bosonic core is the Gauss–polynomial core in
$L^2(\mathbb R^{99})$. The manuscript also has discrete ghost/graded factors; the bosonic
core alone does not implement the entire graded theory. Use $C^\dagger,A$ for the **outer**
ladders, $\Omega_{\rm out}$ for their vacuum, and $Q$ for the BRST charge. The final
number-preserving operator of record is

$$H=d\Gamma(h)=\sum_{j,k}\langle e_j,h e_k\rangle C^\dagger(e_j)A(e_k),
\qquad H\Omega_{\rm out}=0.$$

The inner Hamiltonian retains its pair terms and interactions. Making the outer expression
quadratic does not diagonalize $h$. On the implemented core its positive convention is
$q_h(u)=\tfrac12\sum\|\pi u\|^2+\tfrac12\sum\|B u\|^2$; reconcile signs and coupling
normalizations with the manuscript when identifying operators.

There are **two distinct targets**:

1. **Outer-vacuum gap:** prove $q_h(u)\ge m\|u\|^2$ for **all** inner core vectors,
   with $m>0$, extend to the Friedrichs form domain, then lift to
   $H\ge m N_{\rm out}\ge m(I-P_{\Omega_{\rm out}})$. Here the target is the absolute
   bottom of $h$, including any inner ground/squeezed state.
2. **Inner excitation separation:** identify a ground eigenspace $G$ at $E_0$ and prove
   $q_h(u)-E_0\|u\|^2\ge\Delta\|u\|^2$ for $u\perp G$, $\Delta>0$.
   This can support Temple certificates for that inner sector. It does not imply target 1
   when $E_0=0$: an inner zero mode is a non-vacuum zero-energy outer one-particle state.

**B:** replacing $h$ by $h+\mu I$ replaces $H$ by $H+\mu N_{\rm out}$, not by a scalar
vacuum offset. The resulting artificial gap must be labeled a modified model.
`RequestProject/NestedFock.lean` makes this distinction explicit. Even/odd Ritz separation
also requires a proof that those sectors exhaust the relevant low spectral subspace;
reflection symmetry alone does not establish this.

### Corrections that gate every later phase

**N — lower bounds cannot be subtracted.** From
$\lambda_0(h)\ge L_0=c_1\mu_0-c_2$ and
$\lambda_1(h)\ge L_1=c_1\mu_1-c_2$, one cannot conclude
$\lambda_1(h)-\lambda_0(h)\ge L_1-L_0$. For example,
$h_{\rm ref}=\operatorname{diag}(0,1)$ and $h=\operatorname{diag}(M,M+\varepsilon)$
with $M\ge1$, $0<\varepsilon<1$ satisfy $h\ge h_{\rm ref}$ but have gap $\varepsilon$.
In `BookProof/YangMillsFormDomination.lean`, `certified_separation` is an algebraic equality
between comparison thresholds and `certified_gap_pos` proves positivity of their difference.
Neither identifies the actual interacting ground level or its orthogonal complement.

Valid alternatives are: an absolute bound $L_0>0$ for target 1; a min–max lower bound $L_1$
and independent ground **upper** bound $U_0<L_1$ for target 2; or a direct coercive estimate
on the complement of an identified invariant ground space. If using the reference vacuum's
complement, prove that it is the correct invariant sector. A condition `c 0 = 0` alone does
not identify the interacting ground complement.

**N — Gaussian representation is not confinement.** Multiplication by the square root of
a Gaussian density is a unitary representation change. In one coordinate, with
$d\gamma=(2\pi)^{-1/2}e^{-x^2/2}dx$ and $Uf=\gamma^{1/2}f$,
$U\partial U^{-1}=\partial+x/2$. Thus the Gaussian Dirichlet operator
$\partial^*\partial=-\partial^2+x\partial$ transports to
$-\partial^2+x^2/4-1/2$, an oscillator number operator, **not** the free Laplacian.
The Hermite degree form is not automatically the physical $\tfrac12\sum\pi^2$ form.
Prove the conjugation identity for the actual momentum convention before comparing forms.

**N — lift products after inner composition.** On the outer one-particle sector
$d\Gamma(M)d\Gamma(N)=d\Gamma(MN)$, but on general bosonic sectors their difference
has a normally ordered two-particle contribution. Already
$d\Gamma(I)^2=N_{\rm out}^2\ne N_{\rm out}=d\Gamma(I^2)$.
Use $d\Gamma(B^2)$ when lifting an inner magnetic square; do not replace it by
$d\Gamma(B)^2$. A defined inner-composition algebra must be explicitly distinguished
from ordinary outer operator multiplication. The historical sandwich statements below
do not remove this obligation.

**C — a diagonal surrogate needs an intertwiner.** The occupation forms `degreeForm`,
`quarticDegreeForm` and `yangMillsForm T g`, and the identity
`sandwich_diag_magComp`, are useful models. The split of the concrete `magPoly` into
derivative and commutator pieces does not prove that its square is diagonal, or equal to
$:N^2:$. Require a unitary/core map $J$, its domain properties, and either
$q_h(Jc)=q_{\rm model}(c)$ or a proved inequality with explicit error constants.
No equality of those forms follows just from both being called “Yang–Mills”.

### Work package S0 — identify the Mehler realization and its domains (first)

Specify the Gaussian finite-coordinate measures, inner Hilbert space, graded factors,
cylindrical core and the Lebesgue/Gaussian/Hermite unitary maps. Distinguish a Hermite
**basis cutoff** $\Lambda$ in a fixed $99$-coordinate realization from adding field/spatial
degrees of freedom, changing volume $L$, or removing a regulator $a$. Give embeddings
and a form core for each limit actually claimed. Infinite product Gaussian sequences are
not an identity-covariance Gaussian probability on $\ell^2$; use the coordinate measure
space and its $L^2$ space rather than asserting that its samples lie in $\ell^2$.

**Existing U:** `ChapterMehlerUniqueness.mehler_unique_by_finite_marginals` identifies the
coordinate law under its Gaussian-marginal hypothesis. It is not uniqueness of a vacuum,
a Hamiltonian, or its self-adjoint extension. A Mehler/Ornstein–Uhlenbeck reference semigroup
can organize estimates, but its reference gap is not yet a gap of $h$.

**Acceptance:** a diagram of the concrete core embeddings with norm, momentum and magnetic
operator identities; an explicit list of form-domain and self-adjoint-extension inputs.
Proposed deliverable: `BookProof/Qym/ChapterYangMillsMehlerBridge.lean` (new work, not
an existing declaration). Reuse `ChapterHermiteProductCore` and `ChapterYangMillsHermite`.

### Work package S1 — classify soft directions on the actual configuration space

Work with the full $B=B_{\rm deriv}+gB_{\rm comm}$, independent derivative coordinates
and any imposed tie/compatibility conditions. For a non-abelian theory a general pure
gauge is a gauge transform of zero, not an arbitrary $A_i=\partial_i\phi$; the latter
description is abelian/linearized. Commuting constant Cartan fields are candidate valleys
only after boundary conditions and the derivative constraints have been specified.

The book uses BRST primarily to simplify **observable** equivalence classes, without
quotienting its gauge-variant wave-function. Do not impose a Hilbert cohomology quotient
as an automatic definition of the manuscript's state space. If choosing that route, state
the additional realization, positive Hilbert norm, closed charge, domain invariance and
strong commutation assumptions. Algebraic nilpotency and constant-gauge commutators alone
do not prove those analytic assumptions for the full dynamics.

For a channel argument, separate Cartan, root, spatial translation and jet directions.
Prove a transverse oscillator estimate on each chart, including root hyperplanes with
enhanced stabilizer; then an IMS/localization bound paying for partition gradients.
Do not assume
$\|B_{\rm deriv}+gB_{\rm comm}\|^2\ge g^2\|B_{\rm comm}\|^2$:
the cross term can be negative. A valid starting estimate is
$\|X+Y\|^2\ge(1-\epsilon)\|X\|^2-(\epsilon^{-1}-1)\|Y\|^2$
for $0<\epsilon<1$, with the loss controlled separately.

**Acceptance:** a global estimate for the concrete $q_h$, with all localization and
domain errors accounted for. Finite-dimensional channel confinement can prove compactness
only under its extra hypotheses; it supplies neither an explicit separation constant nor
uniformity under new degrees of freedom or infinite volume. Spatial translations may
leave continuous spectrum even when internal channels are confined.

### Work package S2 — prove the bound needed by the chosen target

For target 1 seek $q_h\ge m\|\cdot\|^2$ on the entire inner core. For target 2 seek
$q_h-E_0\|\cdot\|^2\ge\Delta\|(I-P_G)\cdot\|^2$, with $G$ identified and reducing.
A reference estimate $q_h\ge c_1q_{\rm ref}-c_2\|\cdot\|^2$ gives
$m=c_1\mu_0-c_2$ for target 1 only if this number is positive. For target 2 one may use
$\Delta\ge c_1\mu_1-c_2-U_0>0$ under the min–max hypotheses and a certified $U_0$.
Record dependence on coupling, volume, coordinate count and cutoffs; fix the physical
energy origin before interpreting $m$ as an outer mass scale.

Retain the oscillator reference with the consistent normalization
$h_{\rm ref}=\sum_i\omega_i(N_i+1/2)$, gap $\min_i\omega_i$. Its Schrödinger realization
is $\tfrac12\sum_i(-\partial_i^2+\omega_i^2x_i^2)$ in units $\hbar=1$.
Do not add a parity penalty or oscillator potential to $h$ to obtain the desired answer.
For off-diagonal terms a bound $|q_K|\le a q_{\rm ref}+b\|\cdot\|^2$, $a<1$, must
apply to the **actual** interaction; the ladder model's sharp constants are not yet that
estimate. Extend core inequalities to closed forms and identify their Friedrichs operators.
ESA and a commutator estimate establish operator control, not a positive gap by themselves.

**Acceptance:** a concrete positive $m$, or $L_1-U_0$, with a theorem connecting it to
the selected operator and sector. This is the analytic gate before claiming Temple separation.

### Work package S3 — use Hashimoto for approximation, with a separate spectral gate

Take the paper's generator to be $A=-h_F$ (or a declared rescaling $-t h_F$), where $h_F$
is the chosen positive self-adjoint realization. For $\gamma>0$,
$X_\gamma=(\gamma I-A)^{-1}=(\gamma I+h_F)^{-1}$ is bounded with norm at most
$1/\gamma$, irrespective of whether a positive mass gap has been proved.
The paper's Definition 2.4 uses $f_\gamma(z)=f(\gamma-z^{-1})$ on the bounded
resolvent; verify the functional-calculus admissibility for the function being used.
For Theorem 4.1 retain the real shifts $\gamma_j=N_{\rm shift}-sj>0$ and
$m_{\rm Krylov}<N_{\rm shift}/s$. Use different notation for these parameters and
the outer number operator. Its estimate has the form

$$\|\phi_k(A)v-u_m\|\le
2C\|v\|e^{-sm}\inf_{r\in\mathcal R^{\rm SIRK}_{m-1}}
\|f_{k,N_{\rm shift}}-r\|_{\infty,\Sigma}.$$

This includes the rational best-approximation factor and invertibility/numerical-range
hypotheses. The exponential factor alone is not a convergence proof as $m\to\infty$:
the fixed shift budget bounds admissible $m$. A changing budget requires new uniform
estimates. Complex shifts in the Lean corpus are a separate extension, not this paper's
§4 schedule. Neither a $\phi_k(A)v$ error nor a semigroup approximation error is
automatically a Temple eigenvector residual or a certificate excluding unseen spectrum.

For an approximate resolvent solve $(h_F+\gamma)y\approx v$ with defect $r$, use
$\|y-X_\gamma v\|\le\|r\|/\gamma$. Carry these solve errors, orthogonality loss,
rounding enclosures and basis tails into the final residual bound. For a Galerkin vector,
$\|(h_F-\theta)u\|$ includes $(I-P_\Lambda)h_Fu$; the residual inside the compressed
matrix omits that tail. Also distinguish $P_\Lambda X_\gamma P_\Lambda$ from
$(P_\Lambda h_F P_\Lambda+\gamma)^{-1}$; their equality is not automatic.

After S2 supplies a genuine lower bound $\beta$ for the rest of the relevant spectrum,
verify $\theta<\beta$ and apply Temple:

$$\theta-\frac{\eta^2}{\beta-\theta}\le E_0\le\theta.$$

Use an independently established $\beta-\theta\ge d>0$ for a uniform error estimate.
Never define $\beta=\theta+c_1\Delta_{\rm ref}$ solely from reference domination.
Strong resolvent convergence alone does not turn a finite matrix gap into a limit gap;
transfer a uniform continuum form/spectral estimate with its explicit hypotheses.

### Work package S4 — lift and verify without changing the model

Use `ym_fock_gap_of_one_particle_form_gap` and the Friedrichs extension machinery only
after the concrete S2 bound covers all inner states used by that lift. If a physical
reduction is used, prove its compatibility with the outer lift. A zero inner ground space
requires an explicitly changed one-particle space or a different ground-sector theorem;
it cannot be silently removed to obtain the outer-vacuum statement.

For the certificate campaign, retain the current §M4.9 sector gate and label existing
finite-truncation results as diagnostics until the sector and continuum inputs are met.
Keep an error budget by source (form comparison, basis tail, rational approximation,
linear solve, floating-point enclosure). Numerical agreement checks the implementation;
it does not discharge S2. Follow the repository regeneration/nanoda workflow only when
solver, Hamiltonian or certificate artifacts change.

### Lean reuse and completion ledger

Source paths below are relative to `BookProof/`.

* `ChapterMehlerUniqueness.mehler_unique_by_finite_marginals`: U, Gaussian coordinate
  law; C, concrete dynamical intertwiner.
* `Qym/ChapterYangMillsHermite.lean`, `ymHamiltonian`: U, positive symmetric concrete
  core operator; C, coercive bound for this operator.
* `ChapterReferenceGap.lean`, `href_spectral_gap`: U, oscillator reference form gap;
  C, sector alignment and comparison margin.
* `YangMillsFormDomination.lean`, `ground_bound`, `excited_bound`: U, model form
  inequalities; N, subtracting their lower thresholds as actual levels.
* `YangMillsFormClosureNonDiagonal.lean`: U, model relative-form estimates;
  C, identify physical kernel and close its realization.
* `Qym/ChapterYangMillsFieldStrengthSplit.lean`: U, concrete polynomial split;
  C, global channel estimate, not equality to a diagonal symbol.
* `Sirk/ChapterHashimotoShiftInvert.lean`, `exists_isShiftInvert`: U, bounded inverse
  under extension hypotheses; C, verified rational approximation/solve errors.
* `Sirk/ChapterTempleSeparationNecessary.lean`: N, residual-only edge inference;
  C, independent full-space separation.
* `Qym/ChapterYangMillsFockGapChain.lean`: U, conditional concrete outer lift;
  C, positive one-particle form input.
* `Qym/ChapterYangMillsOuterFockFL.lean`: U, abelian parcel ESA result;
  B, not the non-abelian gap theorem.
* `Qym/ChapterYangMillsHermiteAnalytic.lean`, `dirichletPoly`,
  `norm_polyLp_iterate_hermiteR`: U, the polynomial form core of `gaussDirichlet`, diagonal in the
  Hermite basis, with `TᵐH_n = nᵐH_n` and the `L²(γ dx)` norm bound; C, an operator on
  `Lp ℝ 2 gaussMeasure` whose *domain* is that core (`gaussOp`'s domain is the `C²` core).
* `Toolbox/ChapterNelsonAnalyticVectors.lean`, `essentiallySelfAdjointOn_of_dense_geometric`: U,
  Nelson's criterion for a dense set of vectors with a common geometric ratio, on the Faris–Lavine
  deficiency propagation; N, Nelson's theorem with per-vector radii.  The eigenbasis criteria
  `essentiallySelfAdjointOn_of_dense_span_eigenvectors` (dense *span*, the usable one) and
  `…_of_dense_eigenvectors` (dense set) need neither summability nor symmetry.  For per-vector data
  the module proves Nussbaum's reduction instead,
  `essentiallySelfAdjointOn_of_dense_vectorsOfUniqueness` (dense set of vectors of uniqueness at
  `±i`); U there is Carleman's analytic ⟹ vector of uniqueness, which is the missing theorem.
* `Qym/ChapterYangMillsPolyCore.lean`: U, nothing — the polynomial core of `gaussDirichlet` as an
  operator on classes is now proved self-adjoint at the closure (`isSelfAdjoint_polyOp_closure`,
  `isSelfAdjoint_gaussOp_closure` in `Qym/ChapterYangMillsPolySelfAdjoint.lean`).  Its earlier ℂ
  specialization (`polyDomC`/`polyOpC`/`polyCore_essentiallySelfAdjoint`) is retired and removed; the
  remaining open item is the S0 *book* prose, not a theorem.
* `Toolbox/ChapterDiagonalSelfAdjoint.lean`, `isSelfAdjoint_closure_diagOp_symm`: U, nothing — a
  symmetric, densely defined operator diagonal in an orthonormal Hilbert basis with real eigenvalues
  has self-adjoint closure (closability is derived, not assumed).  This is the reusable form of the
  S0 argument; `Qym/ChapterYangMillsPolySelfAdjoint` is its instance at `hermiteBasisR` with
  eigenvalues `n`.

Execution order is **S0 → S1 → S2 → S3 → S4**; approximation bookkeeping in S3 can proceed
while S2 remains open. The next reviewable deliverable is the S0 representation bridge
and an explicit S2 theorem signature for the selected target, not another abstract
“domination implies gap” wrapper. For any later Lean change, build the affected modules
and audit final theorem axioms and binders. For this documentation revision, verify paths,
formula consistency, relative links and doc-index freshness; no book HTML build is needed.

### Status after the S0 bridge (2026-11-08)

`BookProof/Qym/ChapterYangMillsMehlerBridge.lean` now carries the part of S0 that the
“Corrections” section gates on, together with the S2 signature (the next section records the
second-order and multiplication identities and the norm identity added afterwards):

* **U** — `gaussRoot_sq` (`(γ^{1/2})² = γ`, the isometry input), `hasDerivAt_gaussRoot`,
  `deriv_gaussRoot`, `hasDerivAt_invGauss`, `hasDerivAt_invGauss_mul`, **`conj_deriv`**
  (`U ∂ U⁻¹ = ∂ + x/2`), **`gaussRoot_vacuum`** (`a = ∂ + x/2` kills the weight, so the corpus's
  `momOp = −i • (pderiv − ½ X ·)` is the Gaussian convention), `hasDerivAt_deriv_gaussRoot`, and
  **`gaussRoot_oscillator_ground`** (`−(γ^{1/2})'' + x²/4·γ^{1/2} − ½·γ^{1/2} = 0`): the Gaussian
  Dirichlet operator is unitarily the oscillator, so the reference gap `½` is the oscillator's and
  never a gap of `q_h`.
* **S2 signature** — `HasOneParticleFormGap e fabc m` states target 1 as a named `Prop` on the
  concrete Gauss–polynomial core. `abelian_no_one_particle_form_gap` shows it is false for
  `fabc = 0`, so it is not a vacuous wrapper, and `no_absolute_gap_of_kernel_vector` records that a
  nonzero kernel vector defeats every positive constant: target 2 does not imply target 1.
* **C, unchanged by this module** — the second-order identity `U (−∂² + x∂) U⁻¹ = −∂² + x²/4 − ½`
  on a dense core and its `99`-coordinate product form; the `L²` isometry itself (only its
  pointwise input `gaussRoot_sq` is here); the form core and the self-adjoint-extension inputs. The
  module is one-coordinate analysis plus one abstract linear-algebra statement: it makes no
  spectral claim about `h` and does not by itself move S2.  (The second-order half of that `C` is
  discharged in the next section; the product form is not, and the reason is recorded there.)

Axioms audited: `propext`, `Classical.choice`, `Quot.sound` only. The module builds with no
warnings and no line over 100 characters.

### Status after the S0 identities and the S1 cross term (2026-11-09)

#### S0 — the remaining one-coordinate identities

`BookProof/Qym/ChapterYangMillsMehlerBridge.lean` now also carries, all `sorry`-free and with axioms
`propext`, `Classical.choice`, `Quot.sound`:

* **U — second order.** `conj_dirichlet` is the plan's formula
  `U (−∂² + x∂) U⁻¹ = −∂² + x²/4 − 1/2` for any `f` with two derivatives (stated through the
  weighted Dirichlet operator `gaussDirichlet f = −f'' + x f'`), and `conj_dirichlet_smooth` is the
  same statement on the smooth core, where the two derivatives are `deriv f` and `deriv (deriv f)`.
  The proof is `conj_deriv` **twice** — the drift `x/2` of the first-order identity supplies the
  `x²/4`, its derivative supplies the `−1/2` — which is a concrete confirmation of the plan's
  correction: the derivation of the oscillator from the Gaussian is a statement about `∂` only.
* **U — multiplication.** `conj_mult` (`U (mult V) U⁻¹ = mult V`) and `conj_mult_deriv` (the drift
  multiplies `V` rather than differentiating it).  Together with the second-order identity these
  are exactly the "momentum and magnetic operator identities" of the S0 acceptance list: the
  transform manufactures `x²/4` out of the derivative and moves no potential, so it can neither
  create nor destroy a magnetic gap.
* **U — norm.** `lintegral_norm_sq_conj`: `∫ |γ^{1/2} f|² dx = ∫ |f|² d(γ dx)` in `∫⁻` form, with
  `γ dx` realized as `volume.withDensity (fun x => ofReal (gaussRoot x ^ 2))`.

**N — a correction to this file's earlier ledger, not to the plan.** The previous section said the
`99`-coordinate product form "follows by applying the one-coordinate identity coordinatewise".
That is an invalid inference as stated: coordinatewise application covers only functions depending
on a single coordinate.  The `99`-coordinate statement needs the operator to be a *sum* of
one-coordinate operators that survives the conjugation, i.e. either the tensor decomposition
`U_{99} = ⨂_i U_i` on `⨂_i L²(γ)` with `D_{99} = Σ_i D_i` commuting with it, or the Laplacian
Leibniz rule `Δ(gF) = gΔF + 2⟨∇g, ∇F⟩ + FΔg` together with the `d`-dimensional Gaussian identity
`Δγ^{1/2} = (|x|²/4 + d/2)γ^{1/2}`.  Neither is assembled, so the coordinate-count factor `−99/2`
is **not** proved here, and the product form stays `C`.

The remaining S0 acceptance items are likewise unchanged: the `Lp`-level statement that
multiplication by `γ^{1/2}` is a `LinearIsometryEquiv` (only the integral identity is proved), the
concrete core-embedding diagram, and the closure/Friedrichs list.  That list, made explicit as the
plan's acceptance asks, is — none of it a consequence of the conjugation identities, all of it a
hypothesis about the *domain*:

1. **Closability.** `−Δ + x·∇` densely defined and closable on `C_c^∞` inside `L²(γ dx)`, with the
   Dirichlet form `∫ γ|∇f|² dx` as its closed form and `H¹(γ)` as the form domain.  The smooth
   core must be shown to be a form core, not merely a set on which the identity holds.
2. **Transport to `L²(dx)`.** The unitary at space level (item `C` above), so that the Friedrichs
   operator is the `L²(dx)` operator of `conj_dirichlet` and not only the integral identity.
3. **Product form.** The `99`-coordinate sum needs item 2's product version; the `−99/2` factor and
   the `99`-coordinate domain are part of that statement, not of the one-coordinate analysis.
4. **Corpus pieces that would carry it.** `Toolbox/ChapterFriedrichsExtension` (closed form →
   self-adjoint operator) and `Qym/ChapterYangMillsFriedrichs` (the concrete Yang–Mills slot);
   `Sirk/ChapterHashimotoShiftInvert.IsShiftInvert` supplies the bounded resolvent and its
   `‖R‖ ≤ γ⁻¹` once the form is closed.

Those are inputs S2 must *assume*, not consequences of the identities; the reference oscillator's
spectrum is not `h`'s.

#### S1 — the cross term of the magnetic split

`BookProof/Qym/ChapterYangMillsSoftDirections.lean` turns the plan's two S1 statements about
`B = B_deriv + g B_comm` into theorems, at the level of two abstract vectors:

* **U.** `norm_add_sq_ge_split`: for `0 < ε < 1`,
  `‖X + Y‖² ≥ (1 − ε)‖X‖² − (ε⁻¹ − 1)‖Y‖²`, proved from Cauchy–Schwarz and AM–GM (the AM–GM step
  is `ε(‖X‖ − ε⁻¹‖Y‖)² ≥ 0`).  `norm_add_smul_sq_ge_split` is the shape the plan uses,
  `‖X + g • Y‖² ≥ (1 − ε)‖X‖² − (ε⁻¹ − 1)g²‖Y‖²`, and `norm_add_sq_ge_half` is the `ε = 1/2` case.
* **N.** `no_norm_add_smul_lower_bound`: `‖X + g Y‖² ≥ g²‖Y‖²` is false already for scalars
  (`X = 1`, `Y = −1`, `g = 2` gives `1 < 4`).  So the plan's "do not assume" is a theorem, and the
  counterexample uses no structure constants — non-abelianity is not the source of the failure.

**The outer algebra itself is now small algebra in the corpus.**
`Toolbox/ChapterFockNumberPreservingGap.lean` carries the S1 identities on `dΓ`:
`dGamma_shiftPlus` is the scalar shift in additive form `dΓ(h + c·1) = dΓ(h) + cN` (the
subtractive `dGamma_shiftCol` was already there), `dGamma_comp_one_particle` is composition on the
one-particle sector, `dΓ(M) dΓ(N)|e_k⟩ = dΓ(M·N)|e_k⟩` with `colMul` the column product, and
`dGamma_comp_defect` is the multi-particle defect as a theorem: on two quanta `N² = 4` while
`dΓ(1·1) = N = 2`, so `N² ≠ N`.  Nothing there is conditional.

**What S1 still needs, and what this does not do.** The estimate is a *norm* inequality between two
vectors, so it inherits every `C` of the concrete split: the derivative and commutator parts of
`magPoly` must be identified as vectors in this shape — the squares now do add up
(`Qym/ChapterYangMillsFieldStrengthSplit.magEnergy_eq_parts`, the full `Σ B²` is quadratic plus
cubic plus quartic), but that is an identity, not a domination — the loss
`(ε⁻¹ − 1)g²‖B_comm‖²` must be dominated by the reference form — the `a < 1` input of
`YangMillsFormClosureNonDiagonal` — and no IMS/localization statement is made, so partition
gradients are still unpaid.  The abelian `A_i = ∂_i φ` description of a pure gauge is untouched:
the inequality is agnostic between the abelian and non-abelian readings, and the corpus's
`BrstLongitudinal.gaussVec_eq_longitudinal_add_comm` remains the record that the orbit is larger for
`f ≠ 0`.

S3 and S4 are untouched; S2 is the next subsection.

#### S2 — the relative bound, and the coercivity constant it leaves

`Qym/ChapterYangMillsFieldStrengthSplit.lean` §3c now applies the norm estimate to the concrete
magnetic split and isolates the remaining analytic input.

* **U, unconditional — the cross term.** `magOps_eq_split` is `B = ∂A + [A,A]` for the magnetic
  *operators* on the core (`magDerivOps`, `magCommOps`), and `magEnergy_form_ge_split` is
  `(1 − ε)Σ‖∂A‖² − (ε⁻¹ − 1)Σ‖[A,A]‖² ≤ Σ‖B‖²` for every `ε > 0`: `norm_add_sq_ge_split` summed
  over the `24` field components.  The cubic cross term is thus charged `ε` of the quadratic
  energy and the remainder to the quartic one, and no information about the interaction enters.
* **U, unconditional — the identity.** `magEnergy_form_eq` is the exact decomposition
  `Σ‖B‖² = Σ‖∂A‖² + 2Σ Re⟪∂A, [A,A]⟫ + Σ‖[A,A]‖²`, and `ymHamiltonian_quadForm_split` is the
  physical-core energy identity `⟪x, H₁x⟫ = ½Σ‖πx‖² + ½(that)`.  This is §3b's decomposition of
  `ΣB²` read component by component, so the comparison calculation now carries the full
  interacting energy in its own slot instead of only the quadratic Cartan part.
* **U, conditional on one input — the assembly.** `magEnergy_form_ge_of_quart_bound`: if the
  quartic part obeys a relative bound `Σ‖[A,A]‖² ≤ κΣ‖∂A‖² + b‖x‖²`, then for `0 < ε < 1`
  `(1 − ε − (ε⁻¹ − 1)κ)Σ‖∂A‖² − (ε⁻¹ − 1)b‖x‖² ≤ Σ‖B‖²`.  `magEnergy_form_ge_quarter` is the
  plan's `ε = 1/2`, `κ = 1/4` case, leaving `¼Σ‖∂A‖² − b‖x‖²`, and
  `ymHamiltonian_quadForm_ge_of_quart_bound` adds the kinetic half, which is the S2 shape
  `c₁q_ref − c₂‖·‖²` on the core.
* **C, isolated rather than claimed.** The relative bound `κ < 1` for the *quartic* part is the
  hypothesis of the assembly, not a theorem of the split.  On the concrete core `[A,A]²` is a
  quartic potential; bounding it by the quadratic energy is the Kato-type estimate the coefficient
  model supplies (`YangMillsMagneticQuartic.magnetic_le_quartic`, and
  `YangMillsEffectiveBarrier.barrierBound_quartic`, which dominates the free degree form plus
  Simon's barrier up to an explicit shift), and what is still missing is the mode identification
  between that model and the `99`-coordinate core — already recorded elsewhere in this file as
  unformalised.  So the algebraic gate of S2 is closed *given that relative bound*: a strict
  relative bound now yields a positive coefficient on the quadratic energy with the shift carried
  explicitly.  No unconditional `m > 0` and no `L₁ − U₀` is claimed, and no cutoff uniformity or
  IMS/localisation statement is made.

Axioms audited on the seven new theorems: `propext`, `Classical.choice`, `Quot.sound` only.

#### S2 — the mode identification, and why the relative bound is not the route

§3c's assembly takes a quartic relative bound as its hypothesis.  That hypothesis is **false** on
the coefficient model, and `Qym/ChapterYangMillsFieldStrengthSplit` §3d proves it:

* **N — `not_quartic_relativeBound`.**  For every `κ` and `b`, some `c : CoreCoeff d` has
  `quarticDegreeForm c > κ · degreeForm c + b · ‖c‖²` (take one mode of occupation `N`:
  quartic `(dN)²` against degree `dN`).  The quartic `:N²:` form grows like `N²` where the degree
  form grows like `N`, so no relative bound in the direction `quartic ≤ κ·quadratic + b‖·‖²`
  exists.  Since §3c needs exactly that direction to pay for the cross term, the norm-inequality
  route cannot produce coercivity; the quartic has to enter through a *lower* bound.

**The genuine half of the mode identification.**  `softmodes.md` and
`YangMillsMagneticQuartic` both recorded "the mode expansion is not formalised".  Two pieces of it
are now proved:

* `modeVec`, `modeIndex`, **`coeffToCore_norm_sq`** — the adapted product-Hermite basis
  `coreBasis e` is indexed by `ℕ ≃ (Fin d →₀ ℕ)`, and the coefficient vector `c` is sent to
  `∑ n, c n · ψ_n`; that map is an isometry, `‖coeffToCore c‖² = coreNormSq c`.  So the model's
  coefficient space *is* a subspace of `L²(ℝᵈ)` with the model's norm, concretely and without
  hypotheses.
* **`totalDegree_occMonomial`** — the monomial of a mode, `∏ i, X i ^ nᵢ`, has total degree
  `∑ i, nᵢ`: the model's multi-index is the field-space degree vector.

**The interface, and what it yields.**

* `ModeIdentification Φ fabc` bundles an isometric map of coefficient vectors into the core whose
  magnetic-energy form is the model's `magneticEnergyForm diagA`.  The form half is the remaining
  mode-expansion step (the Wick/Mehler identification of the multiplication form)
  `∑_m ‖[A,A]_m x‖²` with the diagonal `:N²:` weight `∑_n (∑_a B_a(n)²)‖c n‖²`); the structure has
  no inhabitant in the corpus, and the next subsection shows that the abelian sector provably
  cannot supply one.
* **`magEnergy_ge_of_identification`** — given one, the coefficient model's barrier bound transfers
  to the core: `1/24 · (degreeForm + barrierForm − quarticShift ‖x‖²) ≤ ∑_m ‖B_m x‖²`.  The factor
  `24` is `quarticDegreeForm_le_magnetic` (Cauchy–Schwarz), read in the useful direction.
* **`ymHamiltonian_quadForm_ge_of_identification`** — the S2 shape on the core, with no further
  hypothesis on the interaction: `1/48 · (degreeForm + barrierForm − shift ‖x‖²) ≤ ⟪x, H₁x⟫`.
* **`s2_gap_constant`** — the derived constant: on the identified core
  `c₁/48 · q_ref − ((c₁ μ₀ + quarticShift)/48) ‖x‖² ≤ ⟪x, H₁x⟫`, i.e. the certification ratio is
  `c₁/48` and the shift is `(c₁ μ₀ + K + (1+K)²/4)/48`, `K = rootCount T · g/2`, where `c₁` is
  the free/oscillator ratio with `0 < c₁` and `c₁ωᵢ ≤ 1`; with `c₁ = 1`, `ω ≡ 1` that is
  `m = 1/48 ≈ 0.0208` on the reference form.

So S2's *constant* is now an explicit number rather than an existence claim, and the only missing
input is a single identification statement — not an estimate.  What is still not claimed: that
`ModeIdentification` holds (the form half is unformalised), and hence not any unconditional
`m > 0` for the core.

Axioms audited on the six new theorems: `propext`, `Classical.choice`, `Quot.sound` only.

#### S2 — the abelian sector is a counterexample, not an inhabitant, and the constant as a certificate

The natural try is to inhabit `ModeIdentification` where the commutator vanishes (`fabc = 0`), since
there the magnetic field is only `∂A`.  That is **impossible**, and §3d.1 proves it:

* **`not_modeIdentification_abelian`.**  The `:N²:` magnetic form is normal-ordered, so it vanishes
  on the vacuum mode: `magneticEnergyForm diagA (δ₀) = 0` because `magComp diagA a 0 = 0`.  The
  abelian magnetic operator is not zero there — `magOps_abelian_injective` shows the `0`-th one is
  injective, since its polynomial `∑ j k, levi i j k • X (idxD j k a)` is nonzero
  (`magPoly_zero_ne`, by evaluating at the coordinate `idxD 1 2 0`, where the coefficient is
  `levi 0 1 2 = 1`) and `MvPolynomial` is a domain (`mulOp_eq_zero_imp`).  Combined with the
  isometry of `coeffToCore`/`MI.norm_sq`, `toCore δ₀ ≠ 0`, so the sum of squares cannot be `0`.
  The abelian energy therefore carries exactly the constant that the `:N²:` model has dropped, and
  the identification fails on the vacuum vector — not for an analytic reason, but by normal
  ordering.

**The normal-ordering identity itself.**  Two statements, both unconditional:

* `YangMillsFieldStrength.hopWord_pair_reverse` — the reversed pair `c_j c_j†` acts on `n` by
  `n_j + 1`, while `hopWord_pair_same` gives `n_j` for `c_j†c_j`: the difference is the constant
  `1`, the vacuum subtraction, present per mode in every state.  This is the sandwich-model form of
  the normal-ordering statement, and it is why the ordered pair needs no subtraction.
* `YangMillsMagneticQuartic.quartic_eq_magnetic_add_cross` — the two-component identity
  `quarticDegreeForm c = magneticEnergyForm diagA c + 2 ∑_n n₀n₁‖c n‖²`, i.e.
  `(n₀+n₁)² = n₀² + n₁² + 2n₀n₁`: the `:N²:` weight is the normal-ordered magnetic energy plus the
  cross term, and the cross term is the non-abelian piece.  Dropping it is what makes the model
  coercive, and in the abelian sector it is absent — which is the same fact as
  `not_modeIdentification_abelian`, read in the coefficient model.

**The constant as a certificate (§3d.2).**  `s2FormDomination` is the S2 ratio packaged as a
`BookProof.YangMillsFormDomination.FormDomination` on the identified core, with `c₁ = c₁/48` and
`c₂ = (c₁μ₀ + quarticShift)/48`, so the certificate machinery applies verbatim:
`s2_ground_threshold` is `−(quarticShift/48)‖x‖² ≤ ⟪x, H₁x⟫` on the whole core, and
`s2_excited_threshold` is `((c₁ Δ_ref − quarticShift)/48)‖x‖² ≤ ⟪x, H₁x⟫` on the vacuum-orthogonal
sector.  The excitation threshold is positive exactly when `c₁ Δ_ref > quarticShift`; that is the
honest form of the S2 number, and it shows the shift — the barrier price, not the normal-ordering
constant — is what the constant has to beat.

Axioms audited on the nine new theorems: `propext`, `Classical.choice`, `Quot.sound` only.

#### S2 — the mode expansion on the non-abelian root sector

The identification `ModeIdentification` isolates one statement: `∑_m ‖[A,A]_m x‖²` equals the
diagonal `:N²:` weight on every mode.  Half of it is now unconditional — the *one-pair* amplitude on
the root sector, and with it the split of the weight itself.

**The root pair hops.**  `YangMillsFieldStrength.hopWord_pair_offdiag`: for `i ≠ j` the pair
`c_i† c_j` does not act diagonally.  It moves one quantum from mode `j` to mode `i`,

`c_i† c_j |n⟩ = √((nᵢ+1) nⱼ) |n − eⱼ + eᵢ⟩`,

and `hopWord_pair_offdiag_ne` records that the index really changes when `nⱼ ≠ 0` — so no
off-diagonal component is diagonal in the occupation basis, in contrast with the Cartan
`sandwich_diag_magComp`.  The squared amplitude is `offdiag_amp_normSq`, `(nᵢ+1) nⱼ`, and
`offdiag_amp_decomp` splits it as `nᵢ nⱼ + nⱼ`: the **cross term** of the two distinct occupations
plus the diagonal occupation.  The `+1` is the normal-ordering constant that survives *off* the
diagonal, precisely because the annihilation and the creation act on different modes; on the
diagonal it is absent (`hopWord_pair_same`).  Summed over the ordered pairs,
`sum_offdiag_amp_sq` gives `∑_{i≠j} nᵢ nⱼ + (d−1) ∑_j nⱼ`: the root share of the weight plus
`d − 1` copies of the occupation per quantum.

**The weight splits accordingly.**  `YangMillsMagneticQuartic.rootCrossWeight` is
`∑_{i≠j} nᵢ nⱼ`; `sum_sq_eq_diag_add_root` is `(∑ i, nᵢ)² = ∑ i, nᵢ² + (that)`, and
`quarticDegreeForm_eq_magnetic_add_root` sums it against `‖c n‖²`:

`quarticDegreeForm c = magneticEnergyForm diagA c + ∑_{n∈supp} rootCrossWeight n · ‖c n‖²`.

So the `:N²:` weight is the normal-ordered magnetic weight plus the root-pair weight, with `d`
components at a time; `rootCrossWeight_two` shows the `d = 2` case is exactly
`quartic_eq_magnetic_add_cross` (`2 n₀ n₁`), so the two-component identity is a special case and
not a separate accident.

**Boundary.**  This is the *one-pair* half of the form expansion.  What `ModeIdentification` still
needs is the amplitude of a *product* of two root pairs — `∑_m ‖[A,A]_m ψ_n‖²` — i.e. the passage
from `c_i† c_j` to the commutator square; that is a genuine two-particle (Mehler) computation and
is not done, here or elsewhere.  Nothing about `ModeIdentification`'s inhabitation status changes:
the abelian sector still cannot supply one, and the root-sector amplitude above is why the
non-abelian sector is where one would have to be built.

Axioms audited on the nine theorems of this subsection: `propext`, `Classical.choice`,
`Quot.sound` only.

#### S2 — the abelian vacuum energy is `1/2` per component: the constant, evaluated

§3d.1 showed the abelian sector fails the identification *because* of a constant, but left the
constant unnamed.  It is `1/2` per field component, and that is now a theorem.

`YangMillsFieldStrength` §5 adds the coefficient model's vacuum, `vacuumCoeff`, and the oscillator
chain on it:

* `vacuum_lower_zero` — `a_j Ω = 0`, the `ℓ²` statement (the lowering amplitude is `√(nⱼ) = √0`).
* `vacuum_raise_normSq` — `‖a_j† Ω‖² = 1`.
* `vacuum_field_raw` — hence `(a_j† + a_j) Ω = |e_j⟩` with squared norm `1`, *before* any field
  normalisation is chosen.
* `fieldOp`, `fieldOp_vacuum` — with the standard oscillator normalisation
  `A_j = (a_j + a_j†)/√2` (the `1/√2` is the only place a convention enters, and `‖A_j Ω‖² = 1/2`
  is then a computation, not a definition: `coreNormSq_smul` and `(1/√2)² = 1/2`), the vacuum
  magnetic energy is `1/2` per component.
* `sum_fieldOp_vacuum` — `∑_j ‖A_j Ω‖² = d/2`: one half for each of the `d` components, with no
  cross terms, since the components are independent at the vacuum.
* `magneticEnergyForm_vacuum` (`YangMillsMagneticQuartic`) — the normal-ordered `:N²:` form on the
  *same* state is `0`, because `B_a(n) = n_a` vanishes at zero occupation.
* `abelian_vacuum_energy` — the two side by side: `‖A_j Ω‖² = 1/2` and
  `magneticEnergyForm diagA Ω = 0`.

So the abelian magnetic energy is `1/2` per component and the normal-ordered model gives zero; the
difference is the constant that `not_modeIdentification_abelian` detects, now with its value.  It
also explains the shape of `s2FormDomination`: the `c₂` shift is the *barrier* price, while this
`1/2` per component is the part of the abelian energy that is state-independent and therefore has
to be subtracted before any `:N²:` comparison can be made.

Axioms audited on the eleven theorems of this subsection: `propext`, `Classical.choice`,
`Quot.sound` only.

#### S2 — the certificate driven through the gap chain

`s2FormDomination` is an ordinary `FormDomination`, so it needs no separate development: the
chapter's chain applies to it, and §3d.2 now records the instantiations.

* `s2FormDomination_c₁`, `s2FormDomination_c₂` — the certificate's data are the derived numbers:
  ratio `c₁/48`, shift `(c₁μ₀ + quarticShift)/48`.  (The `rfl`-proofs are the point: no second
  constant is introduced anywhere in the chain.)
* `s2_certified_separation` — `certified_separation` at the S2 certificate: the ground and excited
  comparison thresholds differ by `c₁/48 · Δ_ref`.
* `s2_separation_pos` — that difference is strictly positive, since `c₁ > 0` and `Δ_ref > 0`.
* `s2_certified_gap` — the separation in the same shape as `quartic_certified_gap`: on the
  vacuum-orthogonal sector `c₁Δ_ref/48 · ‖c‖² ≤ q(c) + (quarticShift/48)‖c‖²`.
* `s2_gap_threshold_pos` — the excited threshold is positive **iff the barrier is smaller**:
  `quarticShift < c₁ Δ_ref`.  This is the honest condition; nothing in the chain turns a lower
  comparison bound into a spectral gap, and the chapter is explicit about that.

So the S2 number is no longer a side result: it is the ratio of a certificate the existing chain
consumes, and the only nontrivial quantitative condition left is `quarticShift < c₁ Δ_ref`.

Axioms audited on the six theorems of this subsection: `propext`, `Classical.choice`,
`Quot.sound` only.

#### S2 — the root-sector structure, with the obstruction isolated

The abelian refutation and the vacuum value `1/2` per component say *where* the obstruction lives;
§3d.3 of `Qym/ChapterYangMillsFieldStrengthSplit` turns that into a structure and an isolation
theorem.

* `rootSector c : Prop := c 0 = 0` — no vacuum component: the sector where the `:N²:` weight pays for
  the norm.
* `RootModeIdentification` — the same data as `ModeIdentification` (`toCore`, the isometry), with
  `mag_eq` required only on the root sector.  `toRootModeIdentification` shows every unrestricted
  identification restricts, so the structure is not a weakening invented for convenience: it is
  exactly `ModeIdentification` minus the vacuum case.
* `vacuumCoeff_not_rootSector` — the witness of `not_modeIdentification_abelian` is the vacuum
  coefficient, which is outside the sector.  So the abelian argument cannot be replayed against the
  restricted structure: its only counterexample is excluded by hypothesis.
* `magneticEnergyForm_ge_normSq` (in `YangMillsMagneticQuartic`) — off the vacuum the `:N²:` weight
  dominates the norm, because a nonzero mode has some occupied coordinate, whose square is `≥ 1`.
  Hence `root_sector_magnetic_pos`: no nonzero root-sector state has vanishing weight, i.e. there is
  no root-sector analogue of the obstruction.
* `magEnergy_ge_of_rootIdentification` — the S2 barrier transfer (`1/24` of degree + barrier − shift)
  only ever applies the form identity to one `c`, so it holds on the root sector with the *weaker*
  structure.  The vacuum case is needed only to state the identification globally, not for the
  analytic chain.

The S2 chain then carries the restricted structure to the usable number:
`ymHamiltonian_quadForm_ge_of_rootIdentification` (shape inequality on the root sector),
`s2_gap_constant_root` (ratio `c₁/48`, shift `(c₁ μ₀ + quarticShift)/48`), and
`s2_excited_threshold_root` (`(c₁ Δ_ref − quarticShift)/48 · ‖x‖²`, from `href_spectral_gap`).
The whole-core `FormDomination` certificate `s2FormDomination` is not restated: its `dom` field
quantifies over every coefficient, including vacuum mixtures, so it legitimately needs the
unrestricted structure.  The root-sector theorems are pointwise and therefore sound.

#### S2 — the ℝ²⁴ → ℝ⁹⁹ embedding and the ε contraction

Two of the pieces the inhabitant needed are built (§3d.0 and the energy contract).

* `colourIndex m = idxA (decodeSpace m) (decodeColor m)` is injective: the 24 gauge coordinates sit
  inside the 99.  `embedIndex e n = e.symm (mapDomain colourIndex n)` reads mode `n` into the
  `ℝ⁹⁹` adapted basis, and `modeVec99_orthonormal` follows from injectivity.
* `embedL2 e c = ∑ n, c n • modeVec99 e n` is an **isometry**: `embedL2_norm_sq` gives
  `‖embedL2 e c‖² = coreNormSq c` from orthonormality alone — no Mehler kernel, no Gaussian
  integral.  `embedL2_mem_polyGaussCore` puts the image on the Gauss–polynomial core, so
  `embedCore` is a concrete `toCore` candidate and `embedCore_norm_sq` is its `norm_sq` field.
* `levi_contract` is the sharp `∑_i ε_{ijk}ε_{ilm} = δ_{jl}δ_{km} − δ_{jm}δ_{kl}`.
  `eps_contract_poly` lifts it: `∑_i (εP)(εQ) = ∑_{jk}(P_{jk}Q_{jk} − P_{jk}Q_{kj})` for arbitrary
  bilinear polynomial forms.  `magEnergy_eq_contract` applies it to
  `magFullBilin = ∂A + f[A,A]`: `Σ_{ia}B_{ia}² = Σ_{a,j,k}(P² − P·Pᵀ)`.  The ε weights vanish and
  the f weights are inside `P`; the transposed term is where the commutator survives.
* `RootFormDomination` / `root_ground_bound` / `root_excited_bound` / `s2RootFormDomination` — the
  certificate with `dom` on the root sector only, built from `s2_gap_constant_root`.

#### S2 — the root gap, the colour factor, and the contraction

* **The gap on its domain.**  `rootSector` is linear (kernel of evaluation at the vacuum), so it is a
  submodule `rootDomain`; `rootDomain_ne_top` keeps the vacuum out.  On it the certificate's excited
  threshold applies everywhere and `root_spectral_gap` gives
  `(c₁ Δ_ref − quarticShift)/48 · ‖c‖² ≤ q(c)` — a genuine positive gap, where `s2_ground_threshold`
  is only a whole-core lower bound spoilt by the vacuum.  No closure argument is required: the
  comparison is pointwise on the domain.
* **Structure constants as hypotheses.**  `IsAntisymmetric` and `SatisfiesJacobi` are *added*, since
  the polynomial model carries `fabc` as a free tensor.  Derived: `fabc_self_eq_zero`,
  `colourTensor_cyclic` (Jacobi = cyclic vanishing of `K_{abcd}`), and
  `colour_contraction_double`: `Σ(P² − P·Pᵀ) = 2Σ P²` for antisymmetric `P` — the factor `2` of the
  quartic colour energy.  The numerical Casimir is *not* derived; it needs the `su(N)` constants.
* **The contraction.**  `pderiv_X_mul`: `∂ᵢ(Xᵢ p) = p + Xᵢ ∂ᵢ p`, i.e. `[∂ᵢ, Xᵢ] = 1`
  (`normalOrder_contraction` at operator level).  With `coeff_zero_magPoly` this yields
  `magPoly_mul_monomial_ne`: `B_{ia}` has zero diagonal at every monomial.  So `:N²:` is the
  contracted `Σ B†B − (contraction)`, not the diagonal of `magOps`.

* **The root domain is the excited span, and the gap is closed.**  `rootDomain` is the kernel of
  evaluation at the vacuum, and in the coefficient model that is exactly the vacuum-orthogonal core:
  `norm_sq_apply_zero_le_coreNormSq` bounds the vacuum coefficient by the core norm, and
  `rootDomain_eq_span_excited` shows a core vector has no vacuum component iff it is a finite
  combination of the *excited* occupation basis vectors.  So the density here is **algebraic** — the
  excited span *is* the orthogonal core — not analytic.  The only topology the coefficient model
  supports is `coreNormSq`: `rootDomain_closed_of_tendsto` (a norm limit of root-domain vectors keeps
  the vanishing vacuum coefficient, because `‖c 0‖² ≤ coreNormSq c`) and `closure_rootDomain_iff`
  (the closure is the domain), hence `root_spectral_gap_on_closure`: the S2 gap holds for every point
  of the closure.  No limiting argument on the quartic form is used or claimed —
  `quadForm (ymHamiltonian …)` is not known to be continuous in `coreNormSq`, which is exactly why the
  closure-is-the-domain identification, not a continuity argument, is the honest route here.

* **The completion: density is analytic there, and only the reference gap extends.**  The algebraic
  statement above is not the analytic one, and this bullet is the difference.  `coreLp d` is
  `lp (Fin d → ℕ → ℂ) 2`, `coreToLp` embeds the finitely supported core in it, and
  `norm_coreToLp_sq : ‖coreToLp c‖² = coreNormSq c` says the embedding is isometric — so the
  `coreNormSq` limits of the previous bullet *are* ℓ² limits, and the two closures meet.  `vacuumOrthogonal`
  (`f 0 = 0`) is closed (`isClosed_vacuumOrthogonal`, evaluation at the vacuum is `1`-Lipschitz), and
  finite-support **root-domain** vectors are dense in it (`mem_closure_rootDomain_image`, off
  `lp.hasSum_single`), so `closure_rootDomain_image_eq : closure (coreToLp '' rootDomain) =
  vacuumOrthogonal`.  That density uses completeness, which is exactly what the coefficient model lacks.
  The gap: `refEnergy` is unbounded, so the reference form lives on its own domain, `refFormLp ω f =
  ∑' n, refEnergy ω n ‖f n‖²`, and `ref_spectral_gap_closure` carries `href_spectral_gap` there (a
  `tsum` comparison, summability as hypothesis).  **B:** the quartic form `quadForm (ymHamiltonian …)`
  still has no ℓ² *domain* — it is degree four and unbounded, and no closure of the form is
  constructed.  What is closed is the **bound**, which is the half a Friedrichs-type argument needs:
  `gap_closed_in_coreLp` says `K‖·‖² ≤ q` survives an ℓ² limit whenever the sequence converges in
  `coreLp` and the form values converge to `L` — only convergence *along the sequence* is used, never
  continuity of `q`.  Two corollaries: `root_spectral_gap_closed` (the S2 gap at the limit) and
  `root_ground_bound_closed` (the ground threshold of any `RootFormDomination`).  This is lower
  semicontinuity of the bound, not a self-adjoint extension.

**The `su(2)` instantiation, and the colour factor computed.**  The free tensor is now instantiated:
`su2Struct` is `f_{abc} = ε_{abc}` on the first three colour indices (the `su2Slot`s) and `0` off
them — `su(2) × U(1)⁵` in place of the free `fabc`.  It satisfies both hypotheses
(`su2Struct_antisym`, `su2Struct_jacobi`), so §3b.2 applies with nothing left open, and the colour
quantities become explicit: `K_{abcd} = δ_ac δ_bd − δ_ad δ_bc` (`colourTensor_su2`), the adjoint
Casimir `Σ_{ab} f_{abe}f_{abd} = 2δ_{ed}`, i.e. `C_A = 2` (`su2_casimir_adjoint`,
`su2_casimir_adjoint_value`), and `Σ_{abc} f_{abc}² = C_A·dim(adj) = 6` (`su2_colourWeight_sum`).
The fundamental Casimir is derived too, now that the chapter carries the representation it needs:
§3b.2c defines `pauli` (`σ^a`) and `fundRep` (`T^a = σ^a/2` on `ℂ²`), shows it closes on the same
tensor (`fundRep_commutator_su2Struct`, against `su2Struct`), and computes
`Σ_a T^a T^a = (3/4)·1` (`su2_casimir_fundamental`) plus `tr(T^a T^b) = δ^{ab}/2`
(`fundRep_trace_mul`).  So `C_A = 2` and `C_F = 3/4` are both computed from the instantiating `ε`,
each in its own representation.  And the mode factor is now carried: `fundMode d` is
`lp (fun _ => Fin 2 → ℂ) 2` — the occupation core with a colour fibre — `colourModeVec c v` is a core
vector with a colour vector attached, and `colourEnergy` applies the Casimir on the fibre.  Then
`colourEnergy_colourModeVec` is the statement that had been missing: on `c ⊗ v` the Casimir
multiplies `v` by `C_F = 3/4` and leaves the Fock coefficients `c n` untouched, via
`casimir_mulVec` (`(Σ_a T^a T^a).mulVec v = (3/4) • v`).  The colour energy is also an operator now:
`colourEnergy_eq_smul` gives `colourEnergy f = fun n => (3/4) • f n` for *every* `f` in
`fundMode d`, not only on mode vectors, so `colourEnergyOp` is a continuous linear map on the
completion; its norm is exactly `3/4` (`norm_colourEnergyOp_eq`), the upper bound attained on a
single nonzero mode vector.  The factors are also folded into the *field* form now: the core carries
a colour fibre (`colourSpace N`, `colouredCore N D`), `colouredHamiltonian` is `H ⊗ 1 + 1 ⊗ C`
acting componentwise, and on the elementary tensor `colourFibre x v` the form is
`‖v‖² (quadForm H x + C ‖x‖²)` (`colouredHamiltonian_smul_one_quadForm`); with the two Casimirs this
reads `quadForm (ymHamiltonian …) x + (3/4)‖x‖²` on `ℂ²`
(`colouredHamiltonian_fundamental_quadForm`) and `+ 2‖x‖²` on `ℂ³`
(`colouredHamiltonian_adjoint_quadForm`).  Nor is that an elementary-tensor-only statement: the
colour-diagonal Hamiltonian is diagonal in the components, so the form splits componentwise on the
whole coloured core (`colouredHamiltonian_smul_one_quadForm_core`, and
`colouredHamiltonian_fundamental_quadForm_core`/`..._adjoint_quadForm_core`), every core element is a
finite sum of elementary tensors (`colourFibre_repr`, `colourSum`, with components
`∑ k, v k i • x k` by `colourSum_ofLp`), and the form of such a sum is
`colouredHamiltonian_smul_one_quadForm_sum` — the cross terms live in the mixed components, so it is
not a sum of per-tensor values.  The coloured *actions* are bounded operators too: `‖T^a v‖ = ‖v‖/2`
pointwise (`norm_fundRep_mulVec`), so `colourAct` extends to `colourActCLM` with constant `1/2`
(`colourActCLM_norm_le`) and `colourEnergy` to `colourEnergyCLM = (3/4) • 1`; composing the operators
composes the matrices (`colourActOp_comp_apply`), so `[A^a, A^b] = i ε^{abc} A^c`
(`colourActCLM_commutator`) and `Σ_a (A^a)² = colourEnergyCLM` (`sum_colourActCLM_comp`) hold on
`fundMode d` with no domain hypothesis — the colour factor is a representation of `su(2)`, not just a
scalar.  Closedness of the colour operators is not claimed.

The gluon factor is carried on the same footing: `adjRep` is
the adjoint representation on `ℂ³` (`(T^a)_{bc} = −i ε^{abc}`), it closes on the same algebra
(`adjRep_commutator`: `[T^a, T^b] = i ε^{abc} T^c`) and its Casimir is a matrix identity,
`Σ_a (T^a)² = 2 · 1` (`adjRep_casimir`), i.e. `C_A = 2`; so `adjModeVec c v` carries `2 v`
(`adjColourEnergy_adjModeVec`) and the two factors stand in the ratio `C_A/C_F = 8/3`
(`casimir_ratio`).  **B:** the fold into `quadForm (ymHamiltonian …)` is proved on the whole coloured
core — for a diagonal colour energy `µ • 1` (`colouredHamiltonian_smul_one_quadForm_core`, which
gives `µ.re ∑ᵢ‖uᵢ‖²`) and for a **general** colour matrix, where the colour part is the
double sum `Σ_i Σ_j C_ij ⟨u_i, u_j⟩` (`colouredHamiltonian_inner_core`), whose real part is
the form's colour term (`colouredHamiltonian_quadForm_core`); with `C = [[0, 1], [1, 0]]` that is
`quadForm H u₀ + quadForm H u₁ + 2 Re ⟨u₀, u₁⟩` (`colouredHamiltonian_swap_quadForm`), a
cross term no `µ • 1` can produce.  For a **Hermitian** `C` the colour part is real and
symmetric: the double sum equals its own star (`colourTerm_star_eq`), the `(j, i)` and `(i, j)`
off-diagonal contributions agree (`colourPair_re_symm`), the diagonal coefficient is real
(`colourDiag_re`), and the form splits as `Σ_i (quadForm H u_i + (C_ii).re ‖u_i‖²)` plus the
off-diagonal real parts (`colouredHamiltonian_quadForm_re_split`), with the off-diagonal sum equal
to twice its `i < j` part (`colourPairSum_eq_two_mul_upper`).  That is a statement about the
form; the *operator* is symmetric too, on the whole coloured core
(`colouredHamiltonian_symmetricOn`), but symmetry on a core is not essential self-adjointness.
The route to the latter is the direct-sum instrument `dsOp_essentiallySelfAdjointOn` fed by
`ym_h_esa` — not the nested-Fock lift `ym_dGamma_esa`, which is a different operator, and not a
Faris–Lavine hypothesis, since the colour mixing is bounded.  That is now proved, not just
routed: `colouredHamiltonian_esa` in `Qym/ChapterYangMillsNonAbelianEsa.lean` (single-component
deficiency argument plus `deficiencyTrivialAt_of_symmetric_perturbation`; the `PiLp`/`lp`
isometry is not needed after all).
Nothing is claimed for the norm of the coloured operator,
and the occupation completion carrying `colourEnergyOp` is still a separate model from the field
fibre.  **Singlet:** the `ℂ² ⊗ ℂ³` fibre is built — `colourVec 6` with the row-major colour
index (`pairSlotFst`, `pairSlotSnd`) carries the total action `pairRep a = T^a ⊗ 1 + 1 ⊗ T^a`,
and `colourSinglet` is the set of vectors it annihilates — and its singlet space is **trivial**
(`colourSinglet_eq_bot`): `2 ⊗ 3 = 4 ⊕ 2` has no trivial summand, six diagonal entries of the three
actions pinning every coordinate to zero, so a fundamental mode and an adjoint mode over one field
core are never colour-neutral together (`colourSinglet_fibre_trivial`).  The pairs that do carry a
singlet are the two squares, and both are built: the meson `ℂ² ⊗ ℂ²` (`mesonRep` on
`colourVec 4`, singlet space `mesonSinglet`) with `ε` as the singlet (`mesonCoeff_mem`) and the
glueball `ℂ³ ⊗ ℂ³` (`glueballRep` on `colourVec 9`, `glueballSinglet`) with the trace `δ`
(`glueballCoeff_mem`).  Both spaces are exactly one line (`mesonSinglet_eq_span`,
`glueballSinglet_eq_span`), the singlet vectors are nonzero, and `2 ⊗ 2 = 3 ⊕ 1` versus
`3 ⊗ 3 = 5 ⊕ 3 ⊕ 1` is the content: a colour-neutral state is a property of the pair of irreps.
The glueball's three total actions are given in closed form (`glueballRep_zero_mulVec` and
siblings); no decomposition into the other summands is proved.  **Representation:** the total
action `pairRep` obeys `[A^a, A^b] = i ε^{abc}A^c` (`pairRep_commutator`).  The proof runs on the
product basis `pairRepProd` (`T^a ⊗ 1 + 1 ⊗ T^a` as a Kronecker sum), where `pairRepProd_mul`
expands a product into four terms and the two mixed terms `T^a ⊗ T^b`, `T^b ⊗ T^a` are equal in
the two orders, so they cancel and only the two factor commutators survive
(`pairRepProd_commutator`); `pairEquiv` is the row-major relabelling that carries the identity
to `colourVec 6` (`pairRep_eq_reindex`).  No `6 × 6` entry check is used.

**Why `mag_eq_root` is not derivable (§3b.1).**  The derivative coordinates `∂_j A_{k,a}` are
*independent* coordinates, so `magPoly` is a multiplication operator made of coordinate functions.
`mulOp_X_monomial` (`X i * monomial m z = monomial (m + e_i) z`) and `mulOp_X_monomial_ne` (the
raised exponent differs, so no monomial is an eigenvector) show that `magOps` raises the occupation
of every mode: it is **not** diagonal in the occupation basis.  The `:N²:` identity
`Σ_m ‖B_m ψ_n‖² = (Σ_a n_a²)‖ψ_n‖²` therefore needs the normal-ordered Wick contraction of these
multiplication operators, not their diagonal part — and it already fails in the abelian sector
(§3d.1).  So `RootModeIdentification` stays a hypothesis, with the obstruction now a proved
computation.

**Boundary.**  `RootModeIdentification` still has no inhabitant.  The `f` side of the contraction is
not a Casimir identity — this model hypothesises no antisymmetry or Jacobi identity for `f_{abc}`,
so the contraction stops at the transposed term.

Axioms audited on the theorems of this subsection (including the three S2-carry theorems):
`propext`, `Classical.choice`, `Quot.sound` only.

#### S2 — the mode expectation of `:B²:`, computed for the linear half

`magPoly_mul_monomial_ne` says `B_{ia}` has no eigenmode, so the mode-by-mode expectation has to be
computed for the *normal-ordered* square, and only where the Wick contraction closes.  The linear
half is the case where it does, and it is now exact.

* **The mode expectation.**  In the monomial-orthonormal representation the mode state is the monomial
  `modeState m = monomial m 1`, a unit vector for the coefficient inner product, so the expectation
  of an endomorphism `T` in it is the single coefficient `modeExp m T = (T ψ_m)_m` — no analytic
  inner product and no `ModeIdentification` is needed to *state* it.
* **The contraction.**  `pderiv_X_eq_ite` is `∂_i X_j = δ_{ij}`; `coeff_X_mul_pderiv_monomial` and
  `coeff_X_mul_pderiv_modeState` are annihilation-after-creation (`n`, no `+1`);
  `coeff_pderiv_X_mul` is the ordered product, `⟨ψ_m, ∂_l X_{l'} ψ_m⟩ = δ_{ll'}(1 + m_l)`.  The `1`
  is `[∂, X] = 1` and the `m_l` is the occupation: this single lemma is the whole computation.
* **Linear fields.**  `linField c l = ∑_t c_t X_{l_t}` with real `c_t` and adjoint
  `linFieldAdj c l = ∑_t c_t ∂_{l_t}`.  For injective `l`, the cross terms `l_t ≠ l_{t'}` are
  off-diagonal and `modeExp_linField_adj_comp` gives `∑_t c_t²(1 + m_{l_t})`, whence
  `modeExp_linField_normalOrdered`: subtracting `∑_t c_t²` leaves `∑_t c_t² m_{l_t}`.  **Normal
  ordering is exactly "replace `1 + n` by `n`"**, component by component — the abstract statement
  `magPoly_mul_monomial_ne` only gestures at.
* **The derivative half of `B`.**  `magDeriv = ε_{ijk} ∂_j A_{k,a}` *is* a linear field in `(j,k)`
  (`magDeriv_eq_linField`, injectivity by `idxD_pair_injective`), so
  `modeExp_magDeriv_sq` reads `⟨ψ_m, (B^∂_{ia})† B^∂_{ia} ψ_m⟩ = 2 + ∑_{jk} ε_{ijk}² m_{∂_jA_{k,a}}`:
  the contraction of one magnetic component is `2` (`levi_sq_sum_magnetic`), the two transverse
  polarisations.  Summed: `6` per colour index (`levi_sq_sum_total`) and `48 = 24 · 2` over the
  `24` field components (`levi_sq_sum_all_complex`) — precisely the constant normal ordering
  removes (`modeExp_magSum_normalOrdered`, `modeExp_magAll_normalOrdered`).
* **Boundary, stated as a boundary.**  The derivative half is linear, so its square is quadratic and
  two-field Wick closes.  The commutator half `f_{abc}A_bA_c` is quadratic, so its square is
  quartic, and its normal-ordered expectation is a *four-field* contraction — not the two-field one
  proved here, and not implied by it.  `RootModeIdentification` is untouched by this subsection: it
  needs the quartic contraction.

Axioms audited on all twenty new declarations: `propext`, `Classical.choice`, `Quot.sound` only.

#### S2 — the cross weight is dominated by the count factor `d − 1`

The split `(∑ i, nᵢ)² = ∑ i, nᵢ² + rootCrossWeight n` becomes useful when one weight can pay for
the other.  `YangMillsMagneticQuartic` now has the sharp bound:

* `rootCrossWeight_le_sq_sum` — `rootCrossWeight n ≤ (d − 1) · ∑ a, n_a²`.  The `d − 1` is *not* a
  guess: Cauchy–Schwarz gives `(∑ nᵢ)² ≤ d ∑ nᵢ²`, and the diagonal part of that same bound is
  already `∑ nᵢ²`, so the cross weight inherits exactly `d − 1` copies.  Equivalently it is the
  number of *other* components each pair can hop into, which is what
  `sum_offdiag_amp_sq`'s `nᵢ nⱼ + nⱼ` counts.
* `rootCrossForm_le_magnetic` — summed against `‖c n‖²`:
  `∑_n rootCrossWeight n ‖c n‖² ≤ (d − 1) · magneticEnergyForm diagA c`.
* `magneticEnergyForm_le_quartic`, `magnetic_quartic_count_sandwich` — the two directions together:

  `q_mag ≤ (∑ n)² ≤ d · q_mag`,

  so the magnetic and quartic weights are the same form up to the explicit count factor, and the
  cross weight sits between them.
* `not_sq_sum_le_rootCross` — the converse is **false**: on `d = 2` with one occupied component,
  `∑ a, n_a² = 1` while the cross weight is `0`.  So the count factor cannot be dropped or inverted;
  the diagonal part of the weight is not payable by the cross part.

This is the quantitative form of the earlier observation that dropping the cross term is what makes
the `:N²:` model coercive: on the canonical background the cross weight is a bounded fraction of
the magnetic weight, with the bound `d − 1` improving to `0` exactly when only one component is
occupied.

Axioms audited on the four theorems of this subsection: `propext`, `Classical.choice`,
`Quot.sound` only.

#### S2 — the two-pair amplitude on a single mode

The one-pair amplitude left the *product* of two root pairs as the outstanding piece of the mode
expansion.  `YangMillsFieldStrength` §6 computes it.

* `hopWord_two_pairs` — for four distinct indices, `c_i† c_j c_k† c_l` acts on `|n⟩` by two hops
  with amplitude

  `√((nᵢ+1)nⱼ) · √((n_k+1)n_l)`,

  the **product** of the two one-pair amplitudes (the second evaluated at the mode reached by the
  first).  Distinctness is the only hypothesis: it is what makes the intermediate occupations
  independent of the hops.
* `two_pairs_normSq` — the squared amplitude: `(nᵢ+1)nⱼ · (n_k+1)n_l · ‖z‖²`.  So the quartic weight
  of two distinct pairs **factorises** into the root weights of §4.
* `hopWord_two_pairs_same` — the same pair twice is *not* the square: the second hop sees the
  shifted mode, giving `√((nᵢ+2)(nⱼ−1))·√((nᵢ+1)nⱼ)`, and `two_pairs_same_normSq` squares it.  The
  `−1` is the quantum the first pair removed from mode `j` — this is where the two-particle
  structure actually enters, and where a commutation argument would go wrong.
* `hopWord_two_pairs_diag` — the diagonal pair twice acts by `nⱼ · nⱼ = nⱼ²`, which is exactly one
  summand of the per-mode magnetic weight `∑ a, n_a²` in `magneticEnergyForm_diag`.

So the diagonal part of the mode expansion reproduces the `:N²:` weight *as an operator statement*
(not merely as a formula for a form), and the off-diagonal part contributes the cross weight
`∑_{i≠j} nᵢ nⱼ` of `quarticDegreeForm_eq_magnetic_add_root`.  **Boundary.**  What remains for
`ModeIdentification` is the assembly: summing over the `24` components with the `ε`/`f` weights and
matching to `magneticEnergyForm diagA` through the isometry `coeffToCore`.  The amplitudes are now
proved; the colour contraction over the core is not.

Axioms audited on the six theorems of this subsection: `propext`, `Classical.choice`,
`Quot.sound` only.

### Status after the `99`-coordinate product form and the `Lp`-level identity (2026-11-09)

This section supersedes the previous section on three points: the coordinate-count factor `−99/2`
**is** now proved (so the product form is no longer `C`), acceptance item 2 — the `Lp`-level
statement — now has its bundled `LinearIsometryEquiv`, not merely the integral identity, and
acceptance item 1 is most of the way in: the Dirichlet form **and** its operator identity are now in
the corpus, with only closability proper and core density open.

#### S0 — the product form, with `−99/2`

`BookProof/Qym/ChapterYangMillsMehlerProduct.lean` (namespace
`BookProof.YangMillsMehlerProduct`) builds the `d`-coordinate statement without the Laplacian
Leibniz rule — and therefore without needing `Δγ^{1/2} = (|x|²/4 + d/2)γ^{1/2}` as an input.  It
conjugates a *coordinate derivative* twice, exactly as the one-coordinate chapter does:

* `gaussRootVec` / `invGaussVec` are `exp(−|x|²/4)` and `exp(|x|²/4)` on `Fin d → ℝ`;
  `sum_sq_update` is `Σⱼ (update y i t)ⱼ² = Σⱼ yⱼ² − yᵢ² + t²`, and `gaussRootVec_update` /
  `invGaussVec_update` are the resulting factorization of the weight along a coordinate line into a
  one-dimensional Gaussian root times a constant.
* `pd` / `pd2` are the partial derivatives along the line `xᵢ ↦ t`, so they are ordinary
  one-variable `deriv`s; `pd_update` and `pd_pd` record that moving the base point does not change
  the line and that `pd2` is `pd` of `pd`.
* `conj_partial` is `U ∂ᵢ U⁻¹ = ∂ᵢ + xᵢ/2` in `d` coordinates; `pd2_invGaussVec_mul` is
  `U ∂ᵢ² U⁻¹`; `conj_dirichletVec_coord` is `U (−∂ᵢ² + xᵢ∂ᵢ) U⁻¹ = −∂ᵢ² + xᵢ²/4 − ½`.
* `conj_dirichletVec` sums these: `U (Σᵢ Dᵢ) U⁻¹ = −Δ + |x|²/4 − d/2` with
  `laplaceVec F = Σᵢ ∂ᵢ²F`, and `conj_dirichletVec99` is the `d = 99` instance with its `−99/2`.
  `sum_drift` is the step where the per-coordinate `−½` becomes `−d/2`; the coordinate count enters
  nowhere else.

Hypotheses: one-variable differentiability of `F` along every coordinate line (`h1`) and of `pd F i`
along the same lines (`h2`).  All proofs are `sorry`-free with axioms `propext`,
`Classical.choice`, `Quot.sound`.  The module proves the identity on functions; it is still not a
statement about `L²` domains, form cores or self-adjoint extensions, so acceptance items 1 and 4 of
the list above are untouched, item 3 is discharged, and item 2 is addressed at the level now
noted.

#### S0 — the `Lp` level, now including the bundled equivalence

`BookProof/Qym/ChapterYangMillsMehlerLp.lean` lifts the squared integral identity to `Lp` and
bundles it:

* `gaussMeasure` is `volume.withDensity (ofReal ∘ γ^{1/2}²)`, i.e. `γ dx`;
  `enorm_sq_eq_ofReal_sq` converts `‖y‖ₑ ^ 2` into `ofReal (y²)`.
* `eLpNorm_gaussRoot_mul`: `‖γ^{1/2}f‖_{L²(dx)} = ‖f‖_{L²(γ dx)}`, with no integrability
  hypothesis (both sides are `∞` together); `eLpNorm_gaussRoot_mul_ae` is the a.e.-measurable form.
* `memLp_gaussRoot_mul`: `γ^{1/2}f ∈ L²(dx)` **iff** `f ∈ L²(γ dx)`; `memLp_gaussRoot_mul_lp` and
  `memLp_invGauss_mul_lp` are the two membership maps on `Lp` elements.
* `eLpNorm_invGauss_mul` is the reverse weight identity
  `‖γ^{-1/2}g‖_{L²(γ dx)} = ‖g‖_{L²(dx)}` (the pointwise step is `γ^{1/2}²·(γ^{-1/2}g)² = g²`,
  read through `withDensity`).
* `norm_toLp_mehler` is the norm equality on `Lp` elements, and **`mehlerLpEquiv` is the bundled
  `LinearIsometryEquiv (Lp ℝ 2 gaussMeasure) (Lp ℝ 2 volume)`** — forward map multiplication by
  `γ^{1/2}`, inverse by `γ^{-1/2}`.  Axioms: `propext`, `Classical.choice`, `Quot.sound`.

Acceptance item 2 is discharged at the `Lp` level.  What remains true is that mathlib has no
*generic* density-change isometry: its `Lp` isometry API is the `compMeasurePreserving` family, which
needs a measure-preserving map `α → β` (`ν = μ.map f`), and a density is not an image measure.
So the equivalence here is bespoke, with every field paid for: `Lp.ext` plus pointwise identities
for `map_add'` and `map_smul'` (this mathlib has no `MemLp.toLp_smul`), `gaussRoot * invGauss = 1`
and `invGauss * gaussRoot = 1` on the nose for the inverse laws, and `Lp.norm_def` plus the
`eLpNorm` identity for `norm_map'`.  It says nothing about domains, forms or spectra — items 1 and 4
of the acceptance list are still open.

#### S0 — the Dirichlet form, started (acceptance item 1)

`BookProof/Qym/ChapterYangMillsGaussForm.lean` (namespace `BookProof.YangMillsGaussForm`) begins
item 1 of the acceptance list at the form level, deliberately below any domain choice:

* `gaussWeight` is the density `γ^{1/2}² = exp(−x²/2)` of `γ dx`, with `gaussWeight_pos`, and
  `hasDerivAt_gaussWeight` is `(γ^{1/2}²)' = −x γ^{1/2}²`.  That identity is the reason the drift
  `x·∇` sits in `−Δ + x·∇` at all: the `x` is the weight's, and the sequence is
  `γ^{1/2}² f' g' = −(γ^{1/2}² f')' g + γ^{1/2}² f'' g`, so the operator that the form represents is
  `gaussDirichlet f = −f'' + x f'` (`ChapterYangMillsMehlerBridge`), while the form is the
  *positively* signed `∫ γ^{1/2}² f' g'`.
* `gaussForm f g = ∫ x, γ^{1/2}(x)² · f'(x) · g'(x) dx` is the one-coordinate form;
  `gaussForm_comm` is symmetry and `gaussForm_self_nonneg` the nonnegative diagonal.  Both hold for
  *every* pair of functions, because the Bochner integral is total: symmetry is a pointwise `ring`
  identity under `∫`, and the diagonal integrand is the density times a square.  So these are
  statements about the form, not about a form domain — an integrability hypothesis would be needed
  only to say the value is not the `0`-by-convention integral.
* `MemGaussForm` names that integrability domain (`γ^{1/2}² f'² ∈ L¹`), and `gaussForm_self_of_mem`
  records the finiteness obligation on it.
* **`gaussForm_eq_integral_gaussDirichlet` is the operator identity**: for `f` of class `C²` with
  compact support and `g` of class `C¹`,
  `gaussForm f g = ∫ x, γ^{1/2}(x)² · (−f''(x) + x f'(x)) · g(x) dx`, with `gaussDirichlet` the
  operator of the bridge chapter.  So the form *is* the form of `−Δ + x·∇` on the compactly
  supported core, not merely a quadratic functional; the proof is one
  `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` (integrability of the three products comes
  from compact support of `f`, so no growth condition on `g`), plus `deriv_mul` and
  `deriv_gaussWeight`.
  The regularity is `C²`/`C¹` rather than `C^∞` because the corpus's `ContDiff ℝ ⊤` is mathlib's
  *analytic* order `ω`: an analytic function on `ℝ` with compact support is identically zero, so a
  `ContDiff ℝ ⊤` hypothesis with `HasCompactSupport` would make the identity vacuous.  (The same
  observation applies to `Toolbox/ChapterDegEnergyEstimate.integral_dcoord_mul` and
  `Toolbox/ChapterHermiteGraphApprox.integral_conj_dd_mul`, which do use `ContDiff ℝ ⊤` with a
  compact-support hypothesis; they are not touched here, and it is recorded as an open audit item.)
* **`integral_gaussDirichlet_mul_comm` is the symmetry of the operator** in `L²(γ dx)` on that
  core: `⟨−Δf + x·∇f, g⟩_{L²(γ)} = ⟨f, −Δg + x·∇g⟩_{L²(γ)}`.  It is form symmetry read through the
  operator identity in both orders, and it is the hypothesis a closability argument consumes —
  symmetry of the operator, not only of the form.
* **The operator lives on `L²(γ dx)` classes, not just on functions.**  A closure argument needs
  three things from the core, and all three are now proved:
  `isOpenPosMeasure_gaussMeasure` (the density is strictly positive, so `gaussMeasure` is positive
  on nonempty opens — `AbsolutelyContinuous.isOpenPosMeasure` applied to
  `absolutelyContinuous_volume_gaussMeasure`); `eq_of_ae_eq_gaussMeasure` (a continuous function
  that is zero `γ`-a.e. *is* zero, i.e. `Measure.eq_of_ae_eq` plus that open-positivity, so "zero
  a.e." becomes "zero on a dense set"); and `gaussDirichlet_eq_zero_of_ae_eq_zero`, which is the
  well-definedness statement `T` needs — the operator kills a.e.-zero functions, so its value does
  not depend on the representative chosen.  On the image side, `hasCompactSupport_gaussDirichlet`
  (both summands are supported in `supp f' ∪ supp f''`) and `memLp_gaussDirichlet` put the core
  inside `L²(γ dx)`: multiplying by `γ^{1/2}` swaps the weighted norm for the Lebesgue norm
  (`memLp_gaussRoot_mul`), and `γ^{1/2}·gaussDirichlet f` is continuous with compact support, hence
  square-integrable against `volume`.
* **`gaussOp` is `T` as a `LinearPMap` on `L²(γ dx)`.**  `gaussCore` is the core as a submodule of
  `L²(γ dx)` (a class is in it when it has a `C²`-compactly-supported representative) and
  `gaussCoreRep` chooses a representative; the value on a class is
  `gaussOpFun f = toLp (T (gaussCoreRep f))`.  The choice is invisible:
  `gaussOpFun_eq_toLp` computes `toLp (T F)` for *any* admissible representative `F`, because
  `gaussDirichlet_congr_ae` upgrades a.e. equality of continuous representatives to equality of
  images.  Linearity at the function level is `gaussDirichlet_add`/`gaussDirichlet_smul`; at the
  `Lp` level addition is `MemLp.toLp_add` (in mathlib, `rfl`), and the one glue lemma mathlib lacks
  is `memLp_toLp_const_smul`.  Then `gaussOpFun_add`/`gaussOpFun_smul` make `gaussOpFun` a linear
  map on the core and `gaussOp` the resulting `LinearPMap` (domain `gaussCore`).
* **`gaussOp` is densely defined**: `dense_gaussCore`, i.e. `dense_gaussOp_domain`.  This is the one
  place where genuine analysis is needed, and none of it is specific to `γ`:
  `MemLp.exists_hasCompactSupport_eLpNorm_sub_le` gives a continuous compactly supported
  approximation in `L²(dx)`; such a function is uniformly continuous
  (`Continuous.uniformContinuous_of_tendsto_cocompact`), so
  `UniformContinuous.exists_contDiff_dist_le` smooths it in the sup norm; a `ContDiffBump` that is
  `1` on `tsupport g` (and `≤ 1` everywhere) cuts the smooth approximation back to compact support
  without losing that bound, and `eLpNorm_le_of_forall_notMem` integrates the sup bound to
  `ε · (volume (tsupport χ))^{1/2}` — this is
  `exists_contDiff_hasCompactSupport_eLpNorm_sub_lt`.  Then `mehlerMapInv_toLp_mem_gaussCore` says
  the Mehler isometry's inverse sends those classes into the core (their representative is
  `γ^{-1/2} φ`, smooth and compactly supported because `φ` is), and `dense_gaussCore` carries the
  density across `mehlerLpEquiv` by isometry plus `memLp_of_hasCompactSupport`.
* **`gaussOp` is symmetric as a pairing and closable.**  `gaussOp_inner_comm` is
  `⟪T f, g⟫ = ⟪f, T g⟫` on the core: `integral_gaussDirichlet_mul_comm` read through `L2.inner_def`
  on `toLp` images, with `integral_gaussMeasure_eq_integral_gaussWeight`
  (`∫ · d(γ dx) = ∫ γ · dx`) doing the measure translation.  So
  `gaussOp_isFormalAdjoint : gaussOp.IsFormalAdjoint gaussOp`, hence
  `gaussOp_le_adjoint : gaussOp ≤ gaussOp†`, and since the adjoint of a densely defined operator is
  closed (`LinearPMap.adjoint_isClosed`), `IsClosable.leIsClosable` gives
  `gaussOp_isClosable : gaussOp.IsClosable`.  Note that this route needs **no** weak-derivative or
  `H¹(γ)` API — it is exactly why the adjoint is the cheap way in.

The `99`-coordinate form is the sum of these over coordinates (`laplaceVec`/`pd` in
`ChapterYangMillsMehlerProduct`), so the module is not coordinate-count specific.

**Where S0 acceptance item 1 stands.**  It is closed.  The form is defined, symmetric and
nonnegative; the operator identity holds on the `C²`-compactly-supported core; the operator is
packaged as `gaussOp : Lp ℝ 2 gaussMeasure →ₗ.[ℝ] Lp ℝ 2 gaussMeasure` with domain `gaussCore`;
the domain is dense; the operator is closable, so `LinearPMap.closure` exists; and the closure is
self-adjoint (`isSelfAdjoint_gaussOp_closure`), because it *is* the self-adjoint closure of the
polynomial core (`polyOp_closure_eq_gaussOp_closure'`).

The **polynomial form core** is recorded in `Qym/ChapterYangMillsHermiteAnalytic.lean` (diagonal on
the Hermite classes, `‖TᵐH_n‖ = nᵐ‖H_n‖` in `L²(γ dx)`), and it is a real operator on classes in
`Qym/ChapterYangMillsPolyCore.lean`: the Hermite span with `polyOpH`, whose Hermite classes are
eigenvectors with the real eigenvalues `n`, plus the global extension `coreExt` that makes the
symmetry computation bilinear.  `Qym/ChapterYangMillsPolyBasis.lean` turns the family into the
Hilbert basis `hermiteBasisR`, and `Qym/ChapterYangMillsPolySelfAdjoint.lean` reads the diagonal
structure: `polyOp.closure` is self-adjoint, and the graph-norm approximation of
`ChapterYangMillsPolyAnnulus` identifies it with `gaussOp.closure`.  The core is still *not* the
domain of `gaussOp`, whose core is the compactly supported `C²` one — but their closures agree, which
is the content of the identification.

What the closure itself is known to satisfy (`ChapterYangMillsGaussForm`):

* `gaussOp_closure_isClosed` — it is closed (by construction);
* `dense_gaussOp_closure_domain` — its domain contains the dense core;
* `gaussOp_closure_hasCore` — the `C²` core is a **core for the closure**: the closure of the
  restriction `gaussOp.closure.domRestrict gaussCore` is `gaussOp.closure` itself
  (`LinearPMap.closureHasCore` applied to `gaussOp`);
* `gaussOp_closure_le_adjoint` — it is contained in the adjoint, `gaussOp.closure ≤ gaussOp†`: the
  adjoint is a closed extension and the closure is the smallest one.

**`gaussOp` is bounded below in the form sense** (`gaussOp_inner_self_eq`, `gaussOp_quadForm_nonneg`):
`⟪f, gaussOp f⟫ = gaussForm (gaussCoreRep f) (gaussCoreRep f) ≥ 0` for every `f` in the core, because
the operator identity at `g = f` plus the measure translation `∫ · d(γ dx) = ∫ γ · dx` exhibit the
quadratic form as the Dirichlet form, whose integrand is a density times a square
(`gaussForm_self_nonneg`).  Together with `gaussOp_inner_comm` this is exactly the `SymmetricOn` +
`0 ≤ quadForm` pair that the Friedrichs construction consumes.

### Essential self-adjointness of `−Δ + x·∇` in `L²(γ dx)`: the three classical routes

**The statement.**  `gaussOp.adjoint ≤ gaussOp.closure` — equivalently, every pair `(h, g)` with
`h ∈ D(gaussOp†)` and `g = gaussOp† h` lies in the closure of the graph of `gaussOp`; equivalently
`HasCore gaussOp† gaussCore` (the `C²` core is a core for the **adjoint** as well as for
`gaussOp.closure`); equivalently `gaussOp.closure.IsSelfAdjoint`, i.e.
`gaussOp.closure = gaussOp†`.  One half is elementary: `gaussOp.closure ≤ gaussOp†`
(`gaussOp_closure_le_adjoint`).  The other half is the classical theorem “`−Δ + x·∇` is essentially
self-adjoint on `C_c^∞` in `L²(γ dx)`”; it is now proved (`isSelfAdjoint_gaussOp_closure`) by the
diagonal argument on the polynomial core, without any of the three classical routes below.

The three routes are recorded because they are the textbook proofs and each is blocked by a specific
missing API — useful to know if a proof that does not go through the eigenbasis is ever wanted:

**Route A — deficiency indices (the classical route; Weidmann, *Linear Operators in Hilbert
Spaces*, §3.3).**  Complexify (`L²(γ) ⊗ ℂ`), take `T = −Δ + x·∇` with domain `C_c^∞`, and show
`ker(T† − z) = 0` for `z = ±i`.  Concretely, `f ∈ ker(T† − z)` solves, in the weak sense and then
classically (the coefficients are smooth, so distributional solutions are classical),

    −f'' + x f' = z f,     z = ± i,

and essential self-adjointness is the assertion that the only `L²(γ dx)` solution is `0`.  The
standard reduction: substitute `f = γ^{-1/2} u`, i.e. `u = γ^{1/2} f = e^{-x²/4} f`; then `u ∈ L²(dx)`
and the equation becomes the Hermite-type equation

    −u'' + (x²/4) u = (1/2 + z) u,

whose solutions for `Im z ≠ 0` behave like `exp(∓x²/4)` at `±∞` — one decaying, one growing, so each
end admits a one-dimensional space of `L²` solutions, and both deficiency indices vanish once one
checks that no solution is square-integrable at *both* ends (equivalently `Im z ≠ 0` forces
`Im(z ‖f‖²) = 0` from the integration-by-parts identity for `⟪T†f, f⟫`).  *What is missing to
formalize:* the analytic theory of second-order ODEs with a complex parameter (existence,
uniqueness, asymptotics of the two fundamental solutions), which mathlib does not have at all —
`Mathlib/Analysis/ODE` is only the basic `IsPicardLindelof`/`IsIntegralCurve` layer.

**Route B — elliptic regularity.**  `h ∈ D(gaussOp†)` means `∫ γ h · (−Δφ + x·∇φ) = ∫ γ g φ` for all
test `φ ∈ C_c^∞`: the weak form of `−Δh + x·∇h = g`.  Elliptic regularity gives `h ∈ H²_loc` with the
local estimate `‖h‖²_{H²(K)} ≤ C_K(‖h‖² + ‖g‖²)`, and then a cut-off plus mollification shows
`h` is a graph-norm limit of `C_c^∞` functions, which is exactly
`gaussOp.adjoint ≤ gaussOp.closure`.  *What is missing to formalize:* weak derivatives, `H¹`/`H²`,
`L²`-mollification and the interior `H²` estimate.  Mathlib has **no** weak-derivative or
distribution API, so the hypothesis “`T†h = g` weakly” cannot even be stated; this route is furthest
away.

**Route C — analytic vectors (Nelson's theorem, the route the corpus is closest to).**  In `L²(γ dx)`
the Hermite polynomials are eigenfunctions of `T`: with `A = U T U^{-1} = −∂² + x²/4 − 1/2` under
`U = ` multiplication by `γ^{1/2}` (the conjugation `U ∂ U^{-1} = ∂ + x/2` is
`ChapterYangMillsMehlerBridge.conj_deriv`), the eigenfunctions `H_n` of `A` with eigenvalue `n`
correspond to the polynomials `H_n` in `L²(γ dx)`, and the eigen-relation is exactly the Hermite ODE
`−H_n'' + x H_n' = n H_n` (`ChapterHermiteFunctions.hermiteR_ode`).  Polynomials are dense in
`L²(γ dx)` and they are analytic vectors for `T` (`Σ t^n ‖T^n p‖/n! < ∞` since `T^n p` is a
polynomial of degree `n`), so `T` is essentially self-adjoint by Nelson's analytic-vector theorem.
*What was missing to formalize:* (iii) **Nelson's theorem itself** — mathlib has no analytic-vector or
semigroup-generated self-adjointness theory.  This is the route with the least analysis and the most
bookkeeping.  (iii) is now in the corpus, in the common-radius form, and it turned out *not* to close
the route for this operator — the Hermite radii are unbounded — so the closure is by the eigenbasis
criterion instead; see (iii″) below.

*Done* for (i) and (ii) in `BookProof/Qym/ChapterYangMillsHermiteSpectrum.lean` (no `sorry`; axioms
`propext`, `Classical.choice`, `Quot.sound`): `gaussDirichlet_hermiteR` is the eigen-relation as an
identity of functions on the real weighted Dirichlet operator of `ChapterYangMillsMehlerBridge`, and
`dense_span_polyLp` is the density of the polynomial classes `polyLp p` in `Lp ℝ 2 gaussMeasure`.
`integral_moment_eq` + `ae_eq_zero_of_moments_gaussMeasure` are the moment problem for `γ dx` in
closed form.  Three traps: (a) the eigenvalue is `n` and the eigenfunction is `hermiteR n` itself,
**not** `H_n(x/√2)` with eigenvalue `2n` — that is the physicists' convention, while `hermiteR` is
the probabilists' `Polynomial.hermite`, so no rescaling belongs in the statement; (b) `rw [gaussMeasure]`
*fails* in any goal that mentions an `Lp ℝ 2 gaussMeasure` element (the coercion's instance
arguments carry the measure), so the measure is moved with
`integral_withDensity_eq_integral_toReal_smul` applied to a zero-defeq `volume.withDensity …`;
(c) the moment hypothesis must be moved to `volume` *before*
`HermiteCore.ae_eq_zero_of_moments` applies, and the resulting `γ^{1/2} w = 0` divides through by the
nowhere-vanishing `gaussRoot`.

**(iii) Nelson's criterion, in the form the corpus can prove.**
`BookProof/Toolbox/ChapterNelsonAnalyticVectors.lean` carries the analytic-vector vocabulary —
`InvariantOn`, the iterates `orbitD`/`orbit`, the geometric bound `IsGeometric`, the analytic
condition `IsAnalytic`, and `isAnalytic_of_isGeometric` (a geometric bound makes the factorial series
`Σ rᵐ/m! ‖Tᵐx‖` converge) — plus the two computations the deficiency argument is made of: the orbit
identity `inner_orbit` (`⟪Tᵐx, w⟫ = zᵐ⟪x, w⟫` at a deficiency vector) and
`inner_eq_zero_of_isGeometric` (`x ⟂ w` when the ratio of `x` is below `|z|`).  On top of the
Faris–Lavine lemmas already in the corpus (`dense_range_of_deficiencyTrivialAt`,
`deficiencyTrivialAt_of_dense_range`), which carry triviality from `±d i`, `d > r`, to `±i`, this
gives `essentiallySelfAdjointOn_of_dense_geometric`: Nelson's criterion for a dense set of vectors
with a **common** geometric ratio `r`.  It is deliberately *not* called Nelson's theorem — the
classical statement allows a different radius for each vector, and getting from per-vector radii to a
single one is the constancy of the deficiency index on each half plane, which the corpus does not
have.  Axioms: `propext`, `Classical.choice`, `Quot.sound`.

**(iii\') The quantitative input, and the polynomial form core.**
`BookProof/Qym/ChapterYangMillsHermiteAnalytic.lean` puts `T = −∂² + x∂` on polynomials,
`dirichletPoly p = −p'' + X·p'`; `dirichletPoly_eval` shows it agrees with `gaussDirichlet` on the
representative (so the polynomial classes are a core it maps into itself), and
`dirichletPoly_hermiteR` makes it diagonal there, `dirichletPoly (H_n) = n • H_n`.  Because the
operator is diagonal, nothing grows but the eigenvalue: `dirichletPoly_iterate_hermiteR` is
`Tᵐ(H_n) = nᵐ H_n`, `norm_polyLp_iterate_hermiteR` is the bound `‖Tᵐ(H_n)‖_{L²(γ)} = nᵐ ‖H_n‖`, and
`hermiteR_summable` is the convergence of `Σ rᵐ/m! ‖Tᵐ(H_n)‖` for every `r > 0` — the analytic
vector condition, at radius `n`.  The trap: the radius is `n`, so the Hermite classes have **no
common radius**, and the polynomial core meets Nelson's hypothesis but not the common-radius
sufficiency above.  So Nelson's theorem, in the only form the corpus can prove, does **not** close
Route C for this operator; the eigenbasis route below does.

**(iii″) Route C closed: the polynomial core is self-adjoint, by diagonalization.**
`BookProof/Qym/ChapterYangMillsPolyCore.lean` (no `sorry`; axioms `propext`, `Classical.choice`,
`Quot.sound`) supplies what the two modules above still lacked — an operator *on classes* whose domain
is the Hermite span, and a diagonal structure that needs no radius.  Its inputs are
`polyLp_injective` (a polynomial class that vanishes is a.e. zero by `MemLp.toLp_eq_toLp_iff`, then
everywhere by continuity and `IsOpenPosMeasure gaussMeasure` via `IsOpen.eq_empty_of_measure_zero`,
then by `Polynomial.funext`) and `mem_span_hermiteR` (the Hermite polynomials span `Polynomial ℝ`
because `hermiteR n` is monic of degree `n`), which with `dense_span_polyLp` gives
`dense_hermiteSpan`.  Construction: `polyRange`/`polyEquiv` (the class map as an isomorphism onto its
range), `polyOpRange` (`p ↦ −p'' + X p'` carried across it — well defined precisely because the class
map is injective), `polyOpRange_hermiteR` (`= n • H_n`), then `polyOpH` on the Hermite span and the global extension `coreExt`.
`Qym/ChapterYangMillsPolyBasis.lean` reads `⟪H_m, H_n⟫` as `hermiteInner m n`, normalizes and
turns the family into the Hilbert basis `hermiteBasisR`; `Qym/ChapterYangMillsPolySelfAdjoint.lean`
then proves `IsSelfAdjoint polyOp.closure` from the diagonal basis.  The earlier ℂ specialization
(`polyDomC` with the componentwise operator `polyOpC`, and `polyCore_essentiallySelfAdjoint` by
Nelson's eigenbasis criterion) is **retired and removed**: it was a statement over `ℂ` about a
different operator on a different space, it proved nothing about `gaussOp.closure`, and no
complexification equivalence for `LinearPMap`/adjoint exists to transport it.  Over `ℝ` there is no
`i` to test, so the operator is diagonalized instead.

The criterion itself needed one correction to be usable, and this is the trap of Route C: a *dense set
of eigenvectors* is not what a simple spectrum supplies — the union of the eigenlines `ℂ • v_n` is
nowhere near dense — so `ChapterNelsonAnalyticVectors` also carries
`essentiallySelfAdjointOn_of_dense_span_eigenvectors`, stated for the **span** of the eigenvectors,
where `⟪x, w⟫ = 0` propagates by conjugate-linearity and dense sets are what a complete eigenbasis
actually gives.  It needs no symmetry and no summability.  The criterion remains the right tool when a diagonal
operator is only known on a complex space; for S0 it is no longer on the critical path, since the
real diagonal argument closes the identification directly.

**(iii‴) The per-vector case, and why the deficiency estimate cannot reach it.**
`ChapterNelsonAnalyticVectors` also carries Nussbaum's reduction:
`IsVectorOfUniqueness T z x` (the vector lies in the closure of the range of `T − z`),
`inner_eq_zero_of_isVectorOfUniqueness` (such a vector annihilates the deficiency space at `z̄`),
`deficiencyTrivialAt_of_dense_vectorsOfUniqueness` (Nussbaum's lemma) and
`essentiallySelfAdjointOn_of_dense_vectorsOfUniqueness` — a dense set of vectors, each of which is
one at both `±i`, already forces essential self-adjointness, with **no radius and no summability**
anywhere in the hypothesis.  That is the shape Nelson's theorem takes for per-vector data, and the
reason it is not the geometric theorem with `r_x` in place of `r` is arithmetic: the only decay in
`|⟪x, w⟫| ≤ ‖Tⁿx‖/|z|ⁿ` comes from a *geometric* bound, while an analytic vector satisfies the
factorial bound `‖Tⁿx‖ ≤ C n!/ρⁿ`, for which `C n!/|z|ⁿ` grows at every fixed `z`.  Deficiency-index
constancy does not repair this: it propagates triviality between points of a half plane once one point
is known, and unbounded radii give no first point.  The classical bridge from analyticity to the
hypothesis is Carleman's determinacy criterion (Simon, *The classical moment problem as a
self-adjoint finite difference operator*, Cor. 2.16), which is the one ingredient the corpus does not
have.  So the per-vector statement is formalized *modulo* that step, with the per-vector data in the
hypothesis rather than in a missing theorem.

**The `99`-coordinate lift, and where it already is.**  The `d`-coordinate product of the
one-coordinate statement is already in the corpus, by the same criterion and with the same product
structure: `BookProof/Qg/ChapterQgHermiteOscillatorEsa.harmonicCore_essentiallySelfAdjoint` is
`EssentiallySelfAdjointOn (polyGaussCore d) harmCore` for **every** `d`, so `d = 99` is an
instantiation and not a separate proof.  The eigenbasis is the product Hermite family with
eigenvalues `|α| + d/2` (`harmCore_hermiteMvLp`), the core is dense (`polyGaussCore_dense`), and
the polynomial-side identity is `kinPoly_add_harmPoly_hermiteMv`.  This is the S0 operator in the
**Mehler-conjugated** gauge on `L²(ℝ^d)`: `harmCore = −Δ + ‖x‖²/4 = U (Σᵢ Dᵢ) U⁻¹`, coordinate by
coordinate from `conj_dirichletVec` in `ChapterYangMillsMehlerProduct`, and
`isSelfAdjoint_polyOp_closure` above is its `d = 1` unconjugated twin.  So the lift is not
missing analysis or a criterion.  What a *literal* `99`-coordinate statement in the unconjugated
gauge would still need is bookkeeping mathlib does not package: the `d`-dimensional Mehler isometry
`L²(γ^{⊗d}) ≅ L²(ℝ^d)` — `mehlerLpEquiv` is one-dimensional, and there is no product Gauss measure
in the corpus.

**What identifying the two cores actually costs.**  The identification of `polyOp` with
`gaussOp.closure` is *one* approximation, not two theorems.  `polyOp.closure` is self-adjoint, and a
self-adjoint operator has
no proper symmetric extension — this is now a theorem, not a remark:
`BookProof.SelfAdjointMaximal.eq_of_le_of_isSelfAdjoint` (`BookProof/Toolbox/ChapterSelfAdjointMaximal.lean`)
states that `A ≤ B` with `A` self-adjoint and `B` symmetric forces `A = B`, elementwise through
`B ⊆ B* ⊆ A* = A`; its form for closures, `closure_eq_of_le`, is the one S0 uses.  So it suffices that every
polynomial class lies in the domain of the closure of `gaussOpC` — a graph-norm approximation of a polynomial by compactly supported `C²` classes — and
then `gaussOp.closure = polyOp.closure`, one self-adjoint operator described by both cores.  The
reverse approximation is unnecessary.  That one direction is now half formalized.  `BookProof.YangMillsPolyTail.exists_lintegral_tail_lt`
is the tail bookkeeping that was missing: the `γ`-mass of a squared polynomial on `{R ≤ |x|}` is
arbitrarily small, from antitone indicator integrals and `lintegral_iInf`, with `memLp_eval` supplying
the finiteness that limit needs.  `BookProof.YangMillsPolyGraphNorm` states the approximation for the
actual operators — `polyOp` on the Hermite span, `PolyGraphApprox` the graph-norm condition — and
proves it gives `polyOp ≤ gaussOp.closure` (`polyOp_le_gaussOp_closure`, through
`le_closure_of_forall_approx`), hence `polyOp = gaussOp.closure` once `polyOp` is self-adjoint
(`polyOp_eq_gaussOp_closure`).  The annulus estimate is now proved too: on the support of
`−2χ_R' p' − χ_R'' p + x χ_R' p` the tails of `p`, `p'`, `p''` supply the smallness, and
`|χ_R'| ≤ C/R`, `|χ_R''| ≤ C/R²` turn the fixed cutoff into a uniform-in-`R` bound.
`BookProof.YangMillsPolyCutoff` builds exactly that `χ_R = smoothTransition (2 - x²/R²)`, with the
collar at `x² = R²` and `x² = 2R²` and both derivative bounds.

`BookProof.YangMillsPolyAnnulus` carries out the `L²` assembly.  The identity
`T(χ_R p) − T p = −χ_R'' p − 2χ_R' p' + x χ_R' p + (χ_R − 1) T p` (`gaussDirichlet_cutFn_mul_sub`)
is the product rule twice; the derivative bounds collapse on the annulus to the `R`-independent
constants `|χ_R'| ≤ 4C₁/R`, `|x χ_R'| ≤ 4C₁` and `|χ_R''| ≤ 8C₂ + 2C₁` for `R ≥ 1`
(`abs_deriv_cutFn_le`, `abs_mul_deriv_cutFn_le`, `abs_deriv2_cutFn_le`), so the squared difference
is dominated on the tail by `2(8C₂ + 6C₁)² p² + 256C₁² p'² + 4 (T p)²` — the constant
`annulusConst` (`sq_gaussDirichlet_cutFn_mul_sub_le`).  The pointwise bound on the operator itself,
`|T p| ≤ |p''| + |x p'|` (`abs_dirichletPoly_eval_le`), and the finiteness of the Gaussian mass of
every polynomial (`lintegral_ofReal_sq_lt_top`, `annulus_terms_finite`) are what make the domination
integrable; `exists_cutFn_tail` then picks one radius for all three tails, `lintegral_sq_sub_le`
integrates, and `approximable_polyLp` performs the `ε`-assembly.  So `PolyGraphApprox` holds
outright (`polyGraphApprox_holds`), and the inclusion `polyOp ≤ gaussOp.closure` has no unproved
analytic input left.
`BookProof.YangMillsPolyLpNorm` supplies the two facts that assembly needs: `polyOpH_coe` and
`polyOpH_coeFn` put `T` on polynomial *classes* (`T` of a Hermite-span class is the class of
`dirichletPoly p`, represented by `gaussDirichlet (p.eval)`), and `enorm_toLp_sub` /
`norm_toLp_sub_eq` / `ofReal_norm_toLp_sub_sq` say the norm of a difference of classes only sees the
difference of representatives, squared into a `lintegral` of `ofReal` — the shape
`exists_lintegral_tail_lt` bounds.  `polyOp_closure_le_gaussOp_closure` and
`polyOp_closure_eq_gaussOp_closure` restate the identification over `polyOp.closure`, since
essential self-adjointness makes the *closure* self-adjoint and not `polyOp` itself.  That route
left `IsSelfAdjoint polyOp.closure` as a parameter — the ℂ criterion was a statement about
`polyOpC` on `Cx (Lp ℝ 2 γ)`, while the conclusion is about the real `LinearPMap`, and no
complexification equivalence for `LinearPMap`/adjoint exists to transport one to the other (the ℂ
specialization has since been retired).  The diagonal route closes it, and needs no transport: over `ℝ` there is no `i`
to test against, so the operator is diagonalized instead.  `BookProof.YangMillsPolyBasis` reads
`⟪H_m, H_n⟫` as `hermiteInner m n` (`inner_polyLp_hermiteR`), applies `hermiteInner_eq`
(`inner_polyLp_hermiteR_eq`), normalizes to `orthonormal_hermiteLpR`, notes that rescaling does
not change the span (`span_hermiteLpR`) and hands `dense_hermiteSpanSet` to `HilbertBasis.mk`,
obtaining `hermiteBasisR`.  `BookProof.YangMillsPolySelfAdjoint` then runs the two halves.
Symmetry is the diagonal one — `polyOp b_n = n b_n` in an orthonormal family, so
`⟪T b_m, b_n⟫ = m δ_{mn} = ⟪b_m, T b_n⟫`, and `coreExt_inner_comm_span` propagates it through
`Submodule.span_induction₂`; `closure_isFormalAdjoint` transfers it to the closure by taking two
graph sequences and letting both indices go to infinity in `⟪T xₖ, yₗ⟫`.  The adjoint inclusion is
the diagonal argument: the adjoint relation at `b_n` gives `⟪b_n, T† y⟫ = n ⟪b_n, y⟫`
(`inner_adjoint_hermiteLpR`), so the partial sums of the basis expansion of `y` lie in the domain
and their images are the partial sums of the expansion of `T† y`; both converge, and the closed
graph gives `T† ≤ T` (`closure_adjoint_le`).  Both halves are instances of
`BookProof.DiagonalSelfAdjoint.adjoint_le_closure_of_diag` /
`isSelfAdjoint_closure_of_diag_symm` (`Toolbox/ChapterDiagonalSelfAdjoint.lean`), whose only
inputs are symmetry and a Hilbert basis of real eigenvalues (closability is then derived, since a
densely defined symmetric operator sits inside its adjoint).  With `SymmetricOp.le_adjoint` this is
`isSelfAdjoint_polyOp_closure`, and since `gaussOp.closure` is symmetric by the same sequence
argument (`gaussOp_closure_isSymmetric`), maximality gives
`polyOp_closure_eq_gaussOp_closure'` — the identification of the two cores with no hypotheses at
all — and hence `isSelfAdjoint_gaussOp_closure`.

The `ℂ` form was a transport: `polyOpC` and `gaussOpC` live on
`Cx (Lp ℝ 2 γ)` and `Lp ℂ 2 γ`, and no equivalence between the two has been built, so the
identification is stated over `ℝ`, where `gaussOp` lives.  With the real diagonal proof in place the
transport is not needed, and the ℂ specialization of the core has been removed.

**Why the complexification matters here.**  Deficiency spaces are a complex notion: over `ℝ` there is
no `i`.  So Route A (and the Friedrichs/deficiency vocabulary of `ChapterYangMillsFriedrichs`)
speaks about a complex Hilbert space.  The corpus has its own complexification for this,
`BookProof/Realification/Complexification.lean` (`Cx W`, with `InnerProductSpace ℂ`, `cxMapₗ`, the
`norm_sq` splitting and completeness), and `ChapterYangMillsPolyCore` *was* built on it: the real
operator was extended to a global `coreExt` by a left inverse of the Hermite span's inclusion and
complexified with `cxMapₗ`, so ℂ-linearity of `polyOpC` held by construction.  `coreExt` is still
there and is what the real symmetry proof uses; the complexification layer over it is gone.

**Why the ℂ lift is not just bookkeeping either.**  Mathlib has no complexification of real Hilbert
spaces (`Complexification` does not exist in this version) and no bundled `Lp.re`/`Lp.im` maps, only
the function-level `MeasureTheory.memLp_re_im_iff`.  So `Lp ℂ 2 gaussMeasure` cannot be reached from
`gaussOp` by transport: a ℂ-valued `gaussDirichlet`, ℂ `MemLp` of its image, ℂ-linear well-definedness
and ℂ inner-product symmetry must be built directly.  The derivative decomposition needed is
`(deriv f x).re = deriv (fun y => (f y).re) x` (from `Complex.reCLM.comp_hasDerivAt`), and the ℂ
symmetry then splits into four applications of the real symmetry `integral_gaussDirichlet_mul_comm`;
the ℂ integrals must be split with `integral`-`re`/`im` lemmas and integrability side conditions.

**Done** in `BookProof/Qym/ChapterYangMillsGaussFormComplex.lean` (no `sorry`; the only axioms are
`propext`, `Classical.choice`, `Quot.sound`): `gaussDirichletC`, the componentwise splitting
`gaussDirichletC_re`/`_im`, `memLp_gaussDirichletC`, the weighted ℂ symmetry
`integral_gaussWeight_innerC_comm`, and — on classes — the ℂ-linear partial map `gaussOpC` with
`gaussOpC_inner_comm` (symmetry), `gaussOpC_inner_self_eq_re` + `gaussOpC_quadForm_nonneg`
(positivity) and `gaussOpC_symmetric` + `gaussOpC_form_closable` (the Friedrichs handoff).
Two API traps cost the time: `⟪_,_⟫_ℂ` **does not exist** in this mathlib (the complex notation is
plain `⟪x, y⟫` under `open scoped ComplexInnerProductSpace`, and opening `RealInnerProductSpace`
too makes `⟪gaussDirichletC F x, G x⟫` ambiguous), and `integral_re`/`integral_im` are unusable as
rewrites against `z.re` — `RCLike.re_to_complex` keys on `reC` and `RCLike.re` does not match it
syntactically — so the split uses `Complex.reCLM`/`imCLM.integral_comp_comm` instead.

**Also done, over `ℝ`** — the *other* route of gap 1 below, which turns out to be shorter than the ℂ
lift for everything except the deficiency analysis.  `BookProof.YangMillsFriedrichsReal`
(appended to `ChapterYangMillsFriedrichs`) is Part B at `[InnerProductSpace ℝ F]`:
`SymmetricOn`, `quadForm`, `formInner`, `formNormSq`, the expansions
`formNormSq_add`/`_sub`/`_add_smul`, Cauchy–Schwarz `formInner_sq_le`, and `form_closable`.
Every proof is the complex one with `starRingEnd`, `Complex.add_re` and `continuous_re`
deleted; the two places that do *not* simplify mechanically are the swap `⟪H x, y⟫ = ⟪x, H y⟫`
(this mathlib has `real_inner_comm`, `⟪y,x⟫_ℝ = ⟪x,y⟫_ℝ`, and no `inner_comm`) and the limiting step
of `form_closable`, where `innerSL ℝ v` must be turned into a
*plain* continuity statement (`continuous_const.inner continuous_id`) rather than `simpa`d
through the `ContinuousLinearMap` coercion.  The instantiation lives in
`BookProof/Qym/ChapterYangMillsGaussFormReal.lean`, a separate leaf module because the import graph
already runs `ChapterYangMillsGaussForm → … → ChapterYangMillsFriedrichs`: importing the Gaussian
chapter from inside the Friedrichs chapter is a build cycle, not a style question.  It provides
`gaussOp_symmetricOn_real`, `gaussOp_quadForm_nonneg_real` and `gaussOp_form_closable_real` —
`form_closable` on `gaussOp` with no complexification anywhere in statement or proof.

Item 2 is discharged at the `Lp` level and item 3 is discharged.

**What `ChapterYangMillsFriedrichs` still needs.**  That chapter is a self-contained Friedrichs
construction over an *abstract* complex Hilbert space (`F`, `D : Submodule ℂ F`), with
`formInner H x y = ⟪x,y⟫ + ⟪x, H y⟫`, `formNormSq`, `form_closable`, and the classical Friedrichs
theorem entering as the explicit hypothesis `friedrichs` of
`friedrichs_extension_of_semibounded`.  It has never been instantiated on the Gaussian operator.  The
gap list, in order of difficulty:

1. **Real-to-complex shim.**  `gaussOp` lives on `Lp ℝ 2 gaussMeasure`; the chapter is `ℂ`-valued
   (`SymmetricOn D H`, `quadForm H x = (⟪x, H x⟫ : ℂ).re`, `IsPositiveSelfAdjointExtension`).  Either
   complexify (`Lp ℂ 2 gaussMeasure` with the `ℂ`-linear extension of `gaussOp`) or port Part B of
   the chapter to `ℝ`.  **Closed both ways**: the first by
   `ChapterYangMillsGaussFormComplex.gaussOpC : Lp ℂ 2 gaussMeasure →ₗ.[ℂ] Lp ℂ 2 gaussMeasure`
   with the ℂ-valued `C²` core `gaussCoreC`, the second by `BookProof.YangMillsFriedrichsReal` and
   `ChapterYangMillsGaussFormReal.gaussOp_form_closable_real`.  The real route is kept because
   closability does not need `i` — only the deficiency spaces do.
2. **`SymmetricOn gaussCore gaussOp`** — **closed**: `gaussOpC_inner_comm`, in the `SymmetricOn`
   form as `gaussOpC_symmetric`.
3. **Positivity on the core**, `0 ≤ quadForm gaussOp x`, i.e. `0 ≤ ⟪x, T x⟫_γ` — **closed**:
   `gaussOpC_quadForm_nonneg`, from `gaussOpC_inner_self_eq_re` (the real part of the diagonal is
   `gaussForm F.re F.re + gaussForm F.im F.im`) and the corpus' `gaussForm_self_nonneg`.
4. **Closure of the form** — **closed**: `gaussOpC_form_closable` is `form_closable` applied to
   (2) and (3), already instantiated on this operator.
5. **Identification** — the extension Friedrichs produces is *some* positive self-adjoint extension;
   calling it `gaussOp.closure` needs exactly the essential-self-adjointness statement above (or the
   domain identification “form domain of `gaussForm` = `H¹(γ)`”, which is the same gap in another
   dress).  And the classical theorem itself stays a hypothesis: the chapter documents it as an
   admitted theorem (Reed–Simon II, Thm X.23), never as an axiom.

So `ChapterYangMillsFriedrichs` does not lack closability any more — it lacks the instantiation
(1)–(3) on `gaussOp` and, for the *identification* of its output with `gaussOp.closure`, the same
essential-self-adjointness theorem that S0 item 1 still needs.

#### S3 — the solve-error bookkeeping

`BookProof/Sirk/ChapterShiftInvertBookkeeping.lean` (namespace
`BookProof.HashimotoShiftInvertBookkeeping`) supplies the two S3 pieces that the shift-invert
estimates presuppose, and no spectral claim:

* **Solve error.** `norm_solve_error_le` bounds the error of an inexact linear solve by the
  residual; `IsShiftInvert.solve_error_le` specializes it to the shift-invert operator, so a
  residual-level solve is enough for the approximation S3 asks for.
* **Compressed ≠ compressed resolvent.** `exactSolve` is `(2/3, −1/3)` and `compressedSolve` is
  `(1/2, 0)` for the `2 × 2` model with `X = (A+1)⁻¹`; both solve their own problems
  (`exactSolve_solves`, `compressedSolve_solves`) yet differ by `X` applied to the defect
  (`defect_image_eq_error`, `compressed_solve_error_eq_defect_image`), so
  `compression_ne_resolvent` is not a numerical artifact.  This is the S3 bookkeeping the plan's
  "approximation, with a separate spectral gate" wording depends on: the gate is still separate,
  and no Hashimoto-band statement (S42) is claimed here.

## Historical phases and implementation notes (2026-10-30 to 2026-11-04)

The revised work package above governs their interpretation. In particular, “DONE”,
“unconditional”, “form of record” and “certified gap” below describe the cited model's
actual theorem statements only; they do not discharge its missing physical bridges.

The original motivation is to establish an **analytical lower bound for the spectral
separation $\beta_\infty>\theta_\infty$**. `ChapterTempleSeparationNecessary.lean` shows
that **Rayleigh data and local residuals alone cannot exclude unseen lower eigenvalues.**

To prevent the Temple uncertainty $\delta = \frac{\eta^2}{\beta - \theta}$ from blowing up as the basis/truncation order $n \to \infty$, the separation $\beta_\infty - \theta_\infty \ge c > 0$ must be derived **analytically from the structural geometry of the continuous Hamiltonian**, rather than extracted numerically from truncated matrices.

---

### Research Roadmap Overview

```
[Phase 1: Geometric Characterization]
Identify flat directions of the Weyl potential V(A) = 1/2 B²
                     │
                     ▼
[Phase 2: Quantum Channel Taming (B. Simon Mechanism)]
Prove transverse zero-point energy lifts classical flat directions
                     │
                     ▼
[Phase 3: Construction of Gapped Reference Operator H_ref]
Build solvable comparison operator with certified discrete gap c_ref > 0
                     │
                     ▼
[Phase 4: Relative Form Bounding in Lean 4]
Prove H_YM ≥ c₁ H_ref - c₂ on the BRST physical core
                     │
                     ▼
[Phase 5: Spectral Isolation & Transfer to SIRK/Temple Pipeline]
Discharge hypothesis in ChapterRitzCertificate & SpectralGapStability
```

---

### Phase 1: Isolating the Soft-Mode Degeneracies

#### 1.1. The Origin of the Soft Modes
In the 3D Weyl-gauge Yang–Mills Hamiltonian:
$$H_W = \frac{1}{2} \sum_{i, a} \pi_{ia}^2 + \frac{1}{2} \sum_{i, a} B_{ia}^2$$
the magnetic potential is:
$$V(A) = \frac{1}{2} \sum_{i, a} \left( \epsilon_{ijk} \partial_j A_{ka} - \frac{1}{2} g f_{abc} \epsilon_{ijk} A_{jb} A_{kc} \right)^2$$
The potential $V(A)$ vanishes along the classical **flat directions**:
1. **Longitudinal gradients:** $A_i=\partial_i\phi$ in the abelian/linearized theory.
   A general non-abelian pure gauge is a gauge transform of zero, not an arbitrary gradient.
2. **Abelian constant fields:** $A_i \in \mathfrak{t}$ (the Cartan subalgebra of $\mathfrak{su}(N)$), where $[A_j, A_k] = 0$.

Along the Cartan flat directions, $V(A) = 0$ extends to infinity in configuration space. In naive classical mechanics, this would allow particles to escape to infinity with zero potential energy, threatening a continuous spectrum starting at $\theta_\infty$ (i.e., $\beta_\infty - \theta_\infty = 0$).

#### 1.2. Milestone 1: BRST Reduction of the Pure-Gauge Directions
* **Task:** Show that the physical subspace $\mathcal{H}_{\text{phys}} = \ker \Omega / \overline{\operatorname{ran} \Omega}$ contains no longitudinal soft zero-modes.
* **Formalization:** Use `BookProof.BrstReducedTransfer` and `BookProof.QuantumGravityBrstCharge.glin_sq` to project the state space onto the transverse divergence-free subspace, eliminating the $\partial_i \phi$ flat directions before spectral analysis.

#### 1.3. Status (2026-10-31): the charge exists and is nilpotent; the *reduction* does not

This phase is the one place in the plan where the status line has to be negative, so it is worth
being precise about what is already in the corpus and what Milestone 1 still needs.  Nothing below
is an assumption of the later phases — it is a list of missing inputs.

**What is done** (all `sorry`-free, `axiom`-free; `lake build BookProof` compiles):

* `BookProof/ChapterBookBrstYangMills.lean` — the book's charge is **realized, not assumed**:
  `Ω(x) = π^μ_a ∂_μ ψ†_a − π^μ_a f_{abc} A_{μb} ψ†_c − (i/2) f_{abc} ψ†_a ψ†_b ψ_c` as operators
  on a concrete graded state space, with the canonical relations proved (`bookCCR`, `bookGhostCar`),
  the **Gauss-law algebra derived** from them (`gaussGen_bracket`,
  `[𝒢_c, 𝒢_e] = Σ_h f_{ceh} 𝒢_h`), and **`bookOmega_nilpotent`** = `Ω² = 0` for the full charge.
  `bookOmega_eq_brstCharge` identifies it with `i` times the abstract charge of
  `BookProof.QuantumGravityBrstCharge`, which is where `glin_sq` (the square of the constraint
  part) lives.
* `BookProof/ChapterBRSTNilpotent.lean` — `brst_charge_nilpotent`: the cubic ghost term squares to
  zero from the CAR plus the Jacobi identity alone (normal ordering: a quartic term killed by
  fermionic antisymmetry, two contractions killed by Jacobi).
* `BookProof/ChapterBrstReducedTransfer.lean` — the **descent to cohomology** for an abstract
  *bounded* nilpotent `Ω` commuting with a strongly continuous unitary group: `transfer` is a
  one-parameter group of linear automorphisms of `Cohomology Ω = ker Ω ⧸ closure (range Ω)`
  (`transfer_comp`, `transfer_bijective`), and the quotient norm is preserved
  (`infDist_exactStates_eq_of_comm_explicit`), with the Stone instance `stoneTransfer` for an
  unbounded self-adjoint Hamiltonian.
* `BookProof/ChapterBrstTruncationLeakage.lean` and `ChapterBrstUnboundedLeakage.lean` — the
  *leakage* side: for an unbounded exact generator and the compression `P T P` to a
  finite-dimensional retained subspace, `leakage_le` bounds `‖Ω(e^{-itB}x)‖` by `‖Ωx‖ + ‖Ω‖Kt`,
  and the exact dynamics itself does not leak.

So the algebra of §1.1 is *not* the gap: the non-abelian charge, its nilpotency, and the Gauss law
are all proved.  **What Milestone 1 needs is the passage from that algebra to a statement about
`H_phys` as a Hilbert space**, in four steps.  Step 2 is done, for a bounded charge and for a
closed densely defined one (see its status note); step 1 is done — decomposition *and* descent,
for a closed densely defined `Ω` (see its status note); steps 3 and 4 carry status notes too
(2026-11-02 and 2026-11-01).  All four are therefore addressed below, each with what it proves
*and* what it does not:

1. **An unbounded charge.**  `ChapterBrstReducedTransfer` needs `Ω` *bounded* (it uses `Ω` as an
   element of `H →L[ℂ] H`).  The field-theoretic `Ω` is a cubic differential operator, so the
   reduction lemmas have to be reproved for `Ω` closed and densely defined with `Ω² = 0` on a core
   invariant under the dynamics, and with `[H, Ω]` expressed as strong commutation of `e^{-itH}`
   with `Ω` on that core.  Until then the two chapters do not compose: one has a concrete `Ω` and
   no `H`, the other an abstract bounded `Ω` and an abstract `H`.  (The bounded `Ω` is now only
   needed for the *descent*, not for the decomposition — see the status note below.)

   **Status (2026-10-31): the norm side is done for a closed densely defined `Ω`.**
   `BookProof/ChapterBrstUnbounded.lean` (`BookProof.ChapterBrstUnbounded`, no `sorry`) reproves
   the harmonic decomposition for a partially defined charge `Om : H →ₗ.[ℂ] H` with **closed
   graph** (`HasClosedGraph`), **dense domain** and `Ω² = 0` on its domain (`IsNilpotent`, with the
   domain clause that a partial map needs).  Three things change relative to the bounded chapter:
   `isClosed_physicalStates` — the kernel of a closed operator is closed, by pulling the closed
   graph back along `x ↦ (x, 0)`, where the bounded case used continuity; the adjoint is now built
   by hand (`adjointDomain`, `adjointFun`, `adjoint`) because no bounded adjoint exists, and
   **density** is exactly what makes it a function (`adjoint_unique`: two representing vectors
   differ by a vector orthogonal to the dense domain), giving
   `exactStates_orthogonal` (`(closure (range Ω))ᗮ = ker Ω†`) and
   `range_orthogonal_eq_adjointKernel`; and the quotient-norm machinery carries over verbatim —
   `sup_exact_harmonic`, `disjoint_exact_harmonic`, `hodge_decomposition`
   (`harmonic ⊔ exact ⊔ coexact = ⊤`), `harmonicPart_mem`, `harmonicPart_eq_of_sub_mem_exact`,
   `exists_harmonic_decomposition` and `infDist_eq_norm_harmonicPart`
   (`infDist x (exactStates Ω) = ‖harmonicPart x‖`, still attained).

   **Status (2026-11-01): the descent is now done too.**
   `BookProof/ChapterBrstReducedTransferUnbounded.lean`
   (`BookProof.BrstReducedTransferUnbounded`, no `sorry`) closes what the note below used to call
   the bounded-only remainder.  For a partially defined `Ω` the commutation hypothesis
   `[H, Ω] = 0` cannot be one equation — `Ω (U y)` is not even a term unless `U y` is known to lie
   in the domain — so it splits in two, and neither half can be dropped:
   `DomPreserve Om U` (the evolution maps the domain into itself) and
   `StrongCommute Om U hdom` (`U (Ω y) = Ω (U y)` for `y` in the domain, read at `hdom y`).
   From those two, everything the bounded chapter proved carries over:
   `physicalStates_invariant` (nilpotency *not* needed: `Ω x = 0` is transported to
   `Ω (U x) = U (Ω x) = U 0 = 0`), `exactStates_invariant` (where it is **continuity of `U`**,
   not boundedness of `Ω`, that carries the range into its closure — the evolution is a
   continuous linear map throughout, which is exactly why the argument survives), `reducedMap`,
   the group `transfer` with `transfer_zero`, `transfer_comp`, `transfer_apply_transfer`,
   `transfer_bijective`, the quotient-norm preservation `infDist_exactStates_eq_of_comm_explicit`,
   and the Stone instance `stoneTransfer` with `stoneTransfer_zero` / `stoneTransfer_comp` /
   `stoneTransfer_bijective`, `stoneU_mem_physicalStates_of_comm_explicit`,
   `stoneU_sub_mem_exactStates_of_comm_explicit` and
   `infDist_exactStates_stoneU_eq_of_comm_explicit`.  The binder discipline of the bounded
   chapter (the hypotheses written in each theorem's binder list, so that a textual re-export
   cannot drop them and assert norm preservation for an arbitrary isometric family) is
   reproduced verbatim.

   Von Neumann's closed-range theorem `closure (range Ω†) = (ker Ω)ᵮ` is now proved for the
   unbounded chapter, in `BookProof/ChapterBrstUnbounded.lean` §7:
   `closure_range_adjoint_eq_coexact` (with `range_adjoint_orthogonal`: `(range Ω†)ᵮ = ker Ω`,
   `adjoint_adjoint_eq`: `Ω†† = Ω`, and `adjoint_domain_dense`: closedness and density pass to
   `Ω†`).  The proof is the graph rotation of `Submodule.adjoint` in `WithLp 2 (H × H)`: rotation
   is an involution on closed graphs (`adjoint_adjoint_of_isClosed`) and
   `Ω†.graph = Ω.graph.adjoint` (`graph_adjoint`), so the coexact sector defined as `(ker Ω)ᵮ`
   *is* `closure (range Ω†)`.  The earlier inclusion `range_adjoint_le_coexact` is now the easy
   half of an equality, and the third summand of the Hodge decomposition is named as in the
   bounded chapter.  (The harmonic sector, the exact sector and the quotient norm never depended
   on this identification.)
   The two chapters still do not *compose*, for the reason item 1 states: `[H, Ω] = 0` for a
   concrete `H` is not proved, so `hdom` / `hcomm` are hypotheses, not theorems, in a specific
   model.  The concrete `H` itself is no longer missing: the corpus carries the Yang–Mills and
   Standard-Model Hamiltonians in the nested Fock space — `ymHamiltonian`
   (`BookProof/Qym/ChapterYangMillsHermite.lean`, the Gauss–polynomial core of `L²(ℝ⁹⁹)`) and
   `smHamiltonian` (`BookProof/Sm/ChapterSmHamiltonian.lean`, `d = 163`) — so what is missing is
   the commutation with `Ω`, not the operator to commute with.  (The gauge/BRST symmetry it must
   commute with is in the corpus too: `ChapterBookBrstYangMills` and
   `ChapterBookBrstGaugeFixing`.)

   **Progress on the missing commutation (2026-11-03).**
   `BookProof/ChapterBrstYmCommute.lean` (`BookProof.BrstYmCommute`, no `sorry`, no `axiom`)
   now carries the **constraint half** of `[ymHamiltonian, Ω] = 0` for the concrete model, on
   the `99 = 3 + 24 + 72` coordinate space of `book.tex:7045`:

   * the Gauss generators `𝒢_d` realized as derivations of `ℂ[X_0…X_98]` extended to the **jet
     coordinates** `∂_j A_{ka}` — the extension is not cosmetic: a constraint that rotates only
     the `A`-slots leaves `X_D · (f A A)` cross terms in `[Σ_m B_m², 𝒢_d]` uncancelled;
   * `ymGaussDer_bracket` / `ymGaussPoly_bracket` / `ymGauss_bracket`:
     `[𝒢_c, 𝒢_e] = Σ_h f_{ceh} 𝒢_h`, reduced to the contracted field identity
     `field_identity_C` and applied block-by-block;
   * `ymConstraintAlgebra` and `ymOmega_nilpotent` — `Ω = i • brstCharge G.f 𝒢 χ β` on
     `ℂ[X_0…X_98] ⊗ Λ(ℂ⁸)` and `Ω² = 0`.

   **What this still does not give.**  The two Casimir lemmas the Hamiltonian half needs are
   not there, so `hdom` / `hcomm` remain hypotheses:
   `[Σ_m π_m², 𝒢_d] = 0` (needs the vector relation `[∂_{jc}, 𝒢_d] = Σ_b f_{bcd} ∂_{jb}`,
   hence `∂_i (ymGaussVec G d k)` by coordinate case split) and
   `[Σ_m B_m², 𝒢_d] = 0` (needs `𝒢_d(B_{ia}) = Σ_g f_{agd} B_{ig}`, i.e. the scalar
   contraction `Σ_e f_{aec}f_{ebd} + Σ_e f_{abe}f_{ecd} = Σ_g f_{agd}f_{gbc}` from
   `G.jacobi` + `G.antisymm` + `G.cyclic`).  Given those, `ymOmega_comm_ymH` is one
   application of `brstCharge_comm_of_comm`, and the module header records that route.  The
   regime is the constant gauge algebra `G.D = 0`, the same hypothesis
   `gaussDer_casimirPoly` / `casimir_bookOmega_comm` already carry.
2. **A quotient norm that exists.**  `infDist x (exactStates Ω)` is the norm of the class `[x]` in
   the quotient *only* when `exactStates Ω = closure (range Ω)` is a closed subspace of a Hilbert
   space.  On the ghost sector the natural form is indefinite, so the quotient norm has to come
   from the **harmonic (invariant) representative** — a Hodge-type decomposition
   `H = ker Ω ∩ ker Ω* ⊕ range Ω ⊕ range Ω*` — rather than from `infDist`.  This is the one
   genuinely functional-analytic (not merely bookkeeping) input of the phase; with it,
   `physicalStates_invariant` / `exactStates_invariant` transfer verbatim, without it they do not.

   **Status (2026-10-31): DONE for a bounded nilpotent `Ω`, and the decomposition is a theorem,
   not a redefinition.**  `BookProof.ChapterBrstHarmonicDecomposition`
   (`BookProof/ChapterBrstHarmonicDecomposition.lean`, no `sorry`) proves the Hodge decomposition
   on a complex Hilbert space from `Ω†` alone — the two orthogonal complements are
   `exactStates_orthogonal` (`(closure (range Ω))ᗮ = ker Ω†`, via `orthogonal_range` and
   `orthogonal_closure`) and `coexactStates_orthogonal` (`(closure (range Ω†))ᗮ = ker Ω`), so the
   harmonic states `harmonicStates = ker Ω ⊓ ker Ω†` are a *direct complement* of the exact ones
   inside the physical subspace (`sup_exact_harmonic`: `exact ⊔ harmonic = physicalStates`,
   `disjoint_exact_harmonic`) and the three summands span the space with pairwise orthogonal
   parts (`hodge_decomposition`: `harmonic ⊔ exact ⊔ coexact = ⊤`, with
   `disjoint_exact_coexact`, `disjoint_harmonic_coexact`).  The harmonic representative
   `harmonicPart x = x − P_{exact} x` is explicitly constructed, is harmonic for closed `x`
   (`harmonicPart_mem`), differs from `x` by an exact state (`sub_harmonicPart_mem_exact`), and
   depends only on the class (`harmonicPart_eq_of_sub_mem_exact`).  The plan's point 2 is then the
   **identity** `infDist_eq_norm_harmonicPart`:
   `infDist x (exactStates Ω) = ‖harmonicPart x‖` — the infimum is *attained*, so the harmonic norm
   is a norm on cohomology and agrees with `infDist`; and `exists_harmonic_decomposition` states
   the decomposition of a closed state with its orthogonality explicit.  The passage to a closed
   densely defined charge is now in `ChapterBrstUnbounded` (see the status note of item 1 above),
   which reproves the same statements for `Ω : H →ₗ.[ℂ] H` with closed graph and dense domain.
   The ghost-sector indefiniteness is not addressed in either chapter: both work with the
   Hilbert-space inner product, which is exactly why the decomposition exists.
3. **“Longitudinal = exact”.**  The claim “`H_phys` contains no longitudinal soft zero-mode” is the
   identification `closure (range Ω) = span{∂_i φ}` (the pure-gauge directions are *precisely* the
   BRST-exact states), followed by the observation that a longitudinal plane wave is not harmonic,
   i.e. is not in `ker Ω ∩ ker Ω*`.  At present the charge is realized on a graded polynomial
   algebra and `range Ω` is not identified with any longitudinal span; there is also no
   `H_phys` — no completion, no inner product — to speak of a zero-mode *in*.

   **Status (2026-11-02): the identification is a theorem at the level the algebraic realization
   carries it, and the observation half is a theorem too.**
   `BookProof/ChapterBrstLongitudinal.lean` (`BookProof.BrstLongitudinal`, no `sorry`) closes the
   algebraic half in the realization of `book.tex`, on the graded state space the corpus already
   works on, and sits on the gauge/BRST symmetry work already in `timepiece/BookProof/`:
   `ChapterBookBrstYangMills` (the charge realized with `bookCCR`, the Gauss-law algebra and
   `bookOmega_nilpotent`) and `ChapterBookBrstGaugeFixing` (gauge-invariant observables commute
   with the charge — `bookOmega_comm_of_comm` — and descend to `brstCohomology`,
   `mem_exactStates_of_comm`).

   * The gauge orbit of `A_{μa}` splits into the longitudinal gradient and the non-abelian
     remainder (`gaussVec_eq_longitudinal_add_comm`): `longitudinalGaugeVec` is the
     field-independent `−∂_μ α_a` — constant as a polynomial, which is what makes it a gradient
     (`longitudinalGaugeVec_eq_zero_iff` reads it off `G.D` alone) — and `commGaugeVec` is the
     `Σ_g f_{agc} X (μ, g)` bracket, which vanishes identically for `f = 0`
     (`commGaugeVec_eq_zero_of_abelian`).  So for an abelian gauge algebra the orbit *is* the
     longitudinal span: an equality, not an inclusion.
   * In that case the charge collapses to its derivative term (`bookOmega_abelian`), and the
     canonical relation `bookCCR` then fixes its commutator with the field:
     **`comm_bookOmega_Afield`** is `[Ω, A_{μa}] = −i · dChi G μ a`, with *no* commutator piece —
     the BRST variation of the field *is* the ghost-dressed longitudinal direction
     (`dChi_eq_longitudinal_dress`), so the directions the reduction removes are precisely the
     ones the charge produces.
   * The payoff is `longitudinal_mem_exactStates_of_physical`: applied to a BRST-closed `v`,
     `Ω (A_{μa} v) = −i · dChi G μ a v`, so the ghost-dressed longitudinal direction maps into
     `exactStates` and its class in `brstCohomology` is zero — "no longitudinal soft zero-mode"
     as far as the algebraic realization carries it.  The *observation* half — a longitudinal
     plane wave is not harmonic — is `ChapterBrstHarmonicDecomposition.no_longitudinal_zero_mode`:
     for any `L ≤ exactStates`, a state of `L` lying in `ker Ω ∩ ker Ω†` is zero, from
     `disjoint_exact_harmonic` alone, so it needs no field model.
   * The Hamiltonians this charge would have to commute with are in the corpus as well, in the
     nested Fock space: `ymHamiltonian` (`BookProof/Qym/ChapterYangMillsHermite.lean`, `L²(ℝ⁹⁹)`)
     and `smHamiltonian` (`BookProof/Sm/ChapterSmHamiltonian.lean`, `d = 163`).  `[H, Ω] = 0` for
     either is not proved here; that is the composition item 1 still records as open.

   **Honest boundary.**  What is proved is one direction, in the abelian case, as an identity of
   operators: `longitudinal ⊆ gauge orbit = exact`.  The converse — `closure (range Ω) =
   span{∂ᵢφ}` as an equality of *subspaces* — needs the gauge field to be a function on
   spacetime; `BookState N` carries no inner product and no completion, so it is not an equality
   of closures yet.  For `f ≠ 0` the orbit is strictly larger than the longitudinal span: the
   commutator picks up the `Σ_{bc} f_{abc} A_{μb} ψ†_c` term from applying `bookCCR` to the
   `f`-carrying summand of `bookOmega` — a shape, not a theorem.  And neither half speaks of a
   completed `H_phys`: the realization is algebraic on `BookState`, while the Hilbert-space
   statement lives in `ChapterBrstHarmonicDecomposition` (bounded) / `ChapterBrstUnbounded`
   (closed densely defined).

   **Status (2026-11-06): the equality of closures is now a theorem in a model that has both a
   derivative and a Hilbert space.**  `BookProof/BrstLongitudinalExact.lean` (no `sorry`) works on
   the periodic lattice, fields `Fin (n+1) → ℂ` with the cyclic difference
   `∂f(j) = f(j+1) − f(j)`, and the nilpotent charge `Ω(x, y) = (0, ∂x)` on
   `(fields) × (ghosts)` — the abelian derivative-gauge charge of `ChapterBrstLongitudinal` with
   the ghost dressing kept and the gauge algebra trivialized.

   * **`range_derivLin`**: `range ∂ = {f | ∑ⱼ f(j) = 0}`.  One inclusion is `sum_deriv` (a
     gradient has no zero mode); the other is explicit — the cumulative sum `cumFun f` of a
     mean-zero field satisfies `∂(cumFun f) = f` (`derivLin_cumFun`, with the wrap-around at the
     last site paid for by `∑ f = 0`).  So the right-hand side is genuinely `span{∂ᵢφ}`, not
     merely a space the gradients sit inside.
   * **`brstCharge_nilpotent`**: `Ω² = 0` — the ghost factor raises once and the second
     application differentiates zero.
   * **`exactStates_eq_longitudinal`**: `exactStates Ω = ⊥ × {f | ∑ f = 0}`, i.e. the BRST-exact
     states *are* the ghost-raised longitudinal fields — `closure (range Ω) = span{∂ᵢφ}` in the
     model, with the closure nothing but `topologicalClosure` of a closed range.
   * **`longitudinal_le_exactStates`** and **`physicalStates_eq`**: every longitudinal state is
     exact (hence zero in the cohomology), and the BRST-closed states are those whose gauge-field
     part is constant (`∂x = 0`) — the surviving gauge-field mode is the zero mode, which is
     exactly "no longitudinal soft zero-mode".  `disjoint_exact_constants` records that the
     constant sector and the exact sector meet only at zero.

   **Boundary.**  This is the periodic one-dimensional model with a bounded charge and one ghost.
   The physical statement is about the cubic charge of the 3+1 continuum theory on a field Hilbert
   space, where `Ω` is unbounded and the gauge algebra non-abelian (the `commGaugeVec` term of
   `comm_bookOmega_Afield_nonabelian`).  The identification theorem is now proved where both
   sides are defined objects; the continuum version still needs the field Hilbert space and the
   closed unbounded `Ω`, i.e. the same inputs as item 1, and it says nothing about a continuum
   `H_phys`.
4. **Stability of the bottom under the elimination.**  Phases 2–5 bound the bottom and the first
excited level of the operator on the *unreduced* core (`degreeForm`, `barrierForm`, and the
   `FormDomination` certificate).  For the elimination to be legitimate those numbers must be those
   of the reduced operator: one needs that restriction to the transverse sector does not lower
   `θ∞`, or equivalently that the eliminated directions carry no spectral weight near the bottom.
   Without this, Phase 1 could remove exactly the directions that dominate the bottom and Phases
   2–5 would be bounding a different operator.

   **Status (2026-11-01): the statement is now a theorem for the diagonal forms of this corpus,
   and the reason it is short is itself the content.**  In `BookProof.YangMillsFormClosure`
   (section 5, no `sorry`):

   * `formBottom f = sInf (Set.range f)` is the bottom of the symbol, with
     `formBottom_le_of_bddBelow` reading it off.  `ℝ` is only *conditionally* complete, so there
     is no `⨅` into `ℝ`; every statement is therefore equally available in the "any lower bound
     `θ`" form, which is the form the plan's `c₁Δ_ref` already takes.
   * **`diagonalForm_ge_of_le_symbol`** / **`closedForm_ge_of_le_symbol`** — `θ · ‖·‖² ≤ q(x)`
     for every `θ ≤ f n`, on the core and on `L²`, and hence
     **`diagonalForm_ge_formBottom`** / **`closedForm_ge_formBottom`** at `θ = formBottom f`.
   * **`sector_bottom_ge_of_le_symbol`** / **`sector_bottom_ge_formBottom`** — for *any* set `S`
     of normalised retained states, `ofReal θ ≤ sInf (closedForm f '' S)`: the Rayleigh infimum
     over a sector is bounded below by the *same* constant as over the whole space.  That is
     exactly "restriction to the transverse sector does not lower `θ∞`", and it is where the
     plan's "the eliminated directions carry no spectral weight near the bottom" lands.

   **Why it is short, and what that costs.**  The bound is *symbolwise*: every term of
   `closedForm f x = ∑' n, ofReal (f n) · ofReal (‖x n‖²)` is indexed by one multi-index, so the
   form never mixes retained with eliminated directions and restriction cannot improve on a
   symbolwise estimate.  Diagonality is a property of the free, quartic and barrier forms the
   corpus models — it is the same hypothesis under which `formDomination_closed` transfers, and
   the same one its honest boundary says does not cover a magnetic interaction that mixes
   multi-indices.  So the item is closed *for the forms Phases 2–5 actually bound*; for an
   interacting form with off-diagonal blocks, "no spectral weight near the bottom in the
   eliminated directions" is a genuine statement about those blocks, and it is not proved here.
   The reduced space itself — the quotient `H/(exact ⊕ harmonic)` — is built in
   `ChapterBrstReducedTransfer` / `ChapterBrstUnbounded`; what is missing there is item 3 above,
   the identification `closure (range Ω) = span{∂_i φ}`, not the stability of the bottom.

   **The off-diagonal half (2026-11-04).**  The sentence above leaves one case open: a form whose
   blocks mix multi-indices, where the symbolwise argument has nothing to read.  It is closed for
   any interaction with finite Hilbert–Schmidt constant, in §4 of
   `BookProof.YangMillsFormClosureNonDiagonal`: the form bound `abs_kernelForm_le_of_hs` gives
   `kernelForm_ge_neg_of_hs` (`−σ‖c‖² ≤ qK`), so **`diagonalForm_add_kernelForm_ge`** bounds the
   interacting form below by `θ − σ` on the core whenever `θ` bounds the diagonal symbol, and
   **`sector_bottom_ge_interacting`** is the sector statement: over any nonempty set of
   *normalised* retained core states, `sInf` of the interacting form is at least `θ − σ`, with no
   hypothesis on which indices the kernel couples and no hypothesis on the sector.  So restriction
   cannot lower the bottom by more than the Hilbert–Schmidt constant of the interaction — the same
   constant `hopping_farisLavine` charges to the shift, and for the hopping matrix unit
   (`hopping_sector_bottom`) it is exactly `1`.

   **The `L²` lift (2026-11-04).**  §5 of the same module closes the lift this item was missing.
   Truncations were never the right tool here: `closedForm_eq_iSup_truncate` lifts the diagonal
   part because `closedForm` is the supremum of its truncations, and a non-diagonal kernel form is
   not monotone along truncations.  What replaces it is the operator: `closedKernelForm K x` is the
   weighted double series over **all** of `Idx d × Idx d`, absolutely convergent for every
   `x ∈ ℓ²`, and `abs_closedKernelForm_le` gives `|closedKernelForm K x| ≤ σ‖x‖²` with the *same*
   `σ` — one Cauchy–Schwarz with exponents `2, 2` in `ℓ²(Idx d × Idx d)` between the kernel and the
   product of the two coefficient rows (`tsum_sq_kernel_le`: the `σ²` is the total Hilbert–Schmidt
   mass, not a partial sum; `tsum_sq_weight_le`: the weight mass is `‖x‖⁴`).  On the core it *is*
   the core form (`closedKernelForm_coreEmbed`), so this is an extension and not a different form;
   `closed_diagonal_add_kernelForm_ge` gives `θ − σ ≤ closedForm f x + closedKernelForm K x` on the
   form domain (`closedForm f x ≠ ⊤`), and `closed_sector_bottom_ge_interacting` /
   `closed_hopping_sector_bottom` carry the sector statement to `L²`, so the reduced space itself
   can be a closed subspace of `ℓ²` and not only a set of core states.  Note what the hypothesis
   costs: finiteness of the total Hilbert–Schmidt mass holds at a **fixed cut-off**, where the
   interaction is an honest finite matrix, and it is not uniform in the cut-off — the number of
   coupled multi-indices and the magnetic matrix elements grow with the mode index, so no single
   `σ` survives the continuum limit, where the magnetic term is only relatively form bounded with
   `a < 1`.   Boundedness is a *sufficient* condition for closability (the interaction is then a
   continuous perturbation of the closed diagonal form, and the sum is closed on the same domain),
   the `a = 0` case of the Faris–Lavine branch; it is not the necessary one.  **The comparison is
   now stated on `L²` too (2026-11-04)**: §6 gives `closed_farisLavine_domination` — ratio
   `(1 − a)c₁ > 0`, shift `(1 − a)c₂ + b`, for a relative bound `a < 1` — with the finiteness of
   the closed forms as the only extra hypothesis, and `closed_dom_of_scaled_symbol` *derives* that
   hypothesis from a symbolwise inequality `c₁ f ≤ g + C` rather than assuming it (`toReal` of `⊤`
   is `0`, so the finiteness cannot be dropped).  What neither section supplies is a bound uniform
   in the cut-off: §7 computes it on a model — `magCutoffKernel_hs_mass` gives the magnetic ladder
   mass at most `d² C Λ^(d+1)`, i.e. a constant at most `d √C Λ^{(d+1)/2}` — which is a power of
   the cut-off and not a uniform `σ`, so the continuum still needs the `a < 1` branch with `a`
   bounded away from `1` uniformly.  The **ratio** is in fact uniform for free —
   `ladder_relative_bound_uniform` (§8) takes `a` as a free parameter, so `a(Λ) < 1` at every
   cut-off, because at fixed cut-off the ladder is bounded — so what fails in the continuum is the
   constant, not the ratio.  And the finiteness hypothesis of the comparison is not an extra
   assumption for the Yang–Mills symbol: `closed_dom_of_scaled_symbol_auto` derives it from the
   symbolwise inequality whenever the ratio is positive, and `magnetic_closed_dom_of_scaled` (§9)
   applies it to `magSymbol`, the symbol of `magneticEnergyForm` of `YangMillsMagneticQuartic`.
   One scope note, because the continuum *is* formalized elsewhere: the space-time derivative is an
   outer-Fock operator (`dGamma`, `momOp`) and coincident-point products of outer fields are never
   formed — they are the momentum convolutions of `dft_samePointProduct`,
   `momentumCol_samePointProduct`, `samePointProduct_form_eq_momentum`.  The reduced form here is
   diagonal (`yangMillsForm_eq_diagonalForm`), so the ladder is a model of the coupling rather than
   the eliminated theory's magnetic slot, and carrying `σ(Λ)` across needs the off-diagonal part of
   the reduced Hamiltonian — not done.

   The **sharp** bound is available at the cut-off: `ladder_form_norm_le` (§10) proves
   `‖q_K(x)‖ ≤ ½·Q(x) + ½·(Σᵢ Aᵢ²)·‖x‖²` with `Q(x) = Σₙ (Σᵢ (nᵢ+1))‖x n‖²`, and **no constant
   depends on `Λ`**.  The reason is structural rather than computational: the ladder is a sum of
   `√(nᵢ+1)`-weighted raises, each raise is a partial isometry with `Sᵢ*Sᵢ = Aᵢ²·diag(nᵢ+1)` and
   `SᵢSᵢ* ≤ Aᵢ²·1`, so unit-weight AM–GM puts the occupation piece on the reference form with ratio
   `1/2` and the shift piece is bounded by `Aᵢ²‖x‖²` because raising one occupation is injective
   (`sum_raiseIdx_le`, `update_succ_inj`).  Rescaling the AM–GM weight moves along the family
   `(a, b) = (ε/2, (Σ Aᵢ²)/(2ε))`, so `a = 1/2` is the unit-weight member.

   And the Hilbert–Schmidt constant does transfer to the outer-Fock picture after all, on the
   momentum side: `momentumCol_hs_mass` shows the momentum-transfer matrix of a symbol has *exactly*
   the symbol's `ℓ²` mass (`∑_k ∑_i ‖momentumCol V k i‖² = ∑_x ‖V x‖²`, via `(k,i) ↦ k−i` and
   Plancherel), and `momentumCol_samePointProduct_hs_mass` specialises it to a coincident-point
   product: mass `∑_x ‖F x‖²‖G x‖²`.  So `samePointProduct_form_hs_bound` bounds the form by
   `√(∑_x ‖F x‖²‖G x‖²)·‖f̂‖²` — the position-space `σ`, read on the momentum-transfer form.  On the
   BRST side the identification fails for a stated reason rather than an omission:
   `gaugeReduce_extTorsionCoef` writes every reduced torsion coefficient as `if x.1 = k then …`,
   i.e. the reduced one-particle matrix is *diagonal in momentum* and its off-diagonal block is zero
   (`gaugeReduce_extTorsionCoef_offDiag_eq_zero`), whereas the ladder moves one quantum between
   modes.  Different objects.

   Three refinements of that reading are now also proved.  The weight is visible as a family:
   `amgm_weight_family` shows `2st ≤ ε s² + t²/ε` for every `ε > 0`, so the member used above is
   `ε = 1`; `amgm_weight_half` (`ε = 1/2`) gives the same ladder the bound `|q| ≤ ¼Q + (ΣAᵢ²)‖x‖²`.
   The ratio `1/2` is therefore a choice of weight on the trade-off `(a, b) = (ε/2, ΣAᵢ²/(2ε))`, not
   an optimal constant, and `ε → 0` trades it against a growing shift.  The ratio is also what the
   closed form consumes, not only the cut-off matrix: `ladder_closed_domination_sharp` spells out
   `closed_farisLavine_domination` at `a = 1/2`, i.e. `½c₁·closedForm μ − (½c₂+σ)‖x‖² ≤
   closedForm g + closedKernelForm K` on the `L²` domain.  And the mass identity is not special to
   two factors: `chain_hs_mass`, `momentumCol_chain_hs_mass` and `chain_form_hs_bound` iterate it to
   any finite chain, with mass `∑_x ∏_j ‖F_j x‖²`, so a chain of same-point outer fields reads as a
   momentum-transfer form with the product's Hilbert–Schmidt constant and no distribution product.

   The same results are connected to the closed form and to the four-torus.  The cut-off box
   `Fin d → Fin Λ` embeds componentwise in `Idx d = Fin d → ℕ`, and `boxKernel` continues the ladder
   by zero off the box with the cut-off mass itself as its Hilbert–Schmidt constant
   (`boxKernel_hs_finset`, exact and not a bound), so `ladder_closed_domination_box` applies the `L²`
   domination with ratio `1/2` and shift `½c₂ + √m_Λ` with nothing left to assume about the box,
   the mass or the support.  What is still open is the uniform constant: `m_Λ` grows like
   `Λ^{d+1}`, so the ratio is uniform in the cut-off and the shift is not.  The weight family is a
   genuine frontier rather than a sufficient condition: `amgm_pareto_iff` shows that
   `2st ≤ 2as² + 2bt²` for all `s, t` holds exactly when `ab ≥ 1/4`, `amgm_min_shift` shows `1/(4a)`
   is the least shift admissible at ratio `a` and that it is attained at `s = t/(2a)`, and every `ε`
   member satisfies `(ε/2)·(1/(2ε)) = 1/4` (`amgm_weight_frontier_product`), so no member of the
   family is a weakening of another — choosing `ε` moves along the frontier.  On the four-torus the
   chain is carried as far as that section supplies: `chain_hs_massT4` makes the mass of a chain at
   a point of `(ℤ/n)⁴` multiplicative and `chain_form_eq_momentumT4` identifies the chain's form with
   `momentumColT4 (∏ j, F j)`; there is no `momentumCol_hs_mass` analogue on the 4-torus, so there
   the chain is read through the form rather than through the mass.

   The ladder identity itself is carried past the cut-off box.  `magCutoffOp_eq_sum_cre` is an
   identity of finite sums on `Box d Λ`; on the dense core `CoreCoeff d` of `ℓ²(Idx d)` the ladder
   is an endomorphism `creCore` and `magCore A = ∑ᵢ Aᵢ • creCore i` has matrix elements
   `∑ᵢ Aᵢ·creCoeff i β α` for every `β : Idx d` (`magCore_single_apply`), with no box and no `Λ`.
   The raised vector sits one degree higher (`magCore_support_occDeg`), which is why the
   Hilbert–Schmidt and relative-bound results bound the *form* and not the operator: closing
   `magCore` to a self-adjoint operator on `ℓ²` is not formalized — and cannot be, for `magCore`
   itself: the matrix `magKernel A m n = ∑ᵢ Aᵢ·creCoeff i m n` is not symmetric (`magKernel_asymm`:
   the entry at a raise is `Aᵢ√(nᵢ+1)` while at the corresponding lowering it is `0`), so the
   symmetric object is `magSymKernel A m n = magKernel A m n + magKernel A n m`.  That is the
   kernel whose form `closedKernelForm` sees, and the domination of `ladder_closed_domination_sharp`
   is what a self-adjoint realization would have to consume; turning a closed, bounded-below form
   into its operator is the KLMN step, which the corpus does not have.

   The cut-off dependence of §7 is also settled rather than estimated.  The ladder's entries are
   `Aᵢ√(nᵢ+1)`, so `norm_sq_magCutoffKernel_raise` gives the entry at a raise exactly and
   `magCutoffKernel_hs_mass_unbounded` shows that **no** `σ` bounds the Hilbert–Schmidt mass at every
   cut-off — along the ray family the mass is at least `Aᵢ²·N(N+1)/2` at `Λ = N+2`.  This is a
   statement about the *norm* of the ladder, not its form: the same `nᵢ+1` is charged to `Q` in the
   relative bound, which is exactly why the ratio `1/2` there carries no cut-off.  The bounded-form
   reading (`a = 0`) is cut-off-local, and the continuum needs the relative statement.

   On the four-torus the corresponding gap is closed as well: `momentumColT4_hs_mass` is the
   analogue of `momentumCol_hs_mass` (`∑_k ∑_i ‖momentumColT4 V k i‖² = ∑_x ‖V x‖²`, from Plancherel
   on `(ℤ/n)⁴` and the fact that each transfer is hit `n⁴` times), and
   `momentumColT4_chain_hs_mass` carries it to a chain of coincident-point factors.  So the four-torus
   chain now has an actual Hilbert–Schmidt bound and not only a form identity.

   The frontier of §11 is the frontier of the *weight*, not the ladder's sharp constant, and that
   distinction is now a theorem instead of a caveat.  `ladder_form_norm_le_of_ratio` gives the
   ladder-level bound at **every** ratio `a > 0`, `‖q‖ ≤ a·Q + (Σᵢ Aᵢ²/(4a))·‖x‖²`, and it is a
   dilation: `ladder_form_norm_le` applied to the field strength `A/(2a)` (linearity in `A` is
   `magShiftTerm_smul`, `magCutoffKernel_smul`, `ladder_form_smul`) and multiplied by `2a`.  So the
   curve `(a, S/(4a))` of `amgm_min_shift` is one theorem plus a rescaling, and `a = 1/2` is just
   the `a = 1/2` point of it.  The ladder's actual sharp shift at ratio `a` is smaller, and the
   smallest section where this shows is two modes: `δ_n` and `δ_{n+eᵢ}` with the other occupations
   zero, where `Q = dα² + (d+1)β²`, the form is `2Aᵢαβ`, and the sharp constant is the top of a
   `2 × 2` problem, `twoModeShift A a d = √(A² + a²/4) − a(2d+1)/2` (`twoModeShift_key` its
   determinant identity, `twoModeShift_le` the bound, `twoModeRatio_shift` attainment at
   `(α, β) = (A, ad + γ)`).  At `A = 1`, `a = 1/2`, `d = 1` that is `(√17 − 3)/4 ≈ 0.2808` against
   the termwise `A²/(4a) = 1/2`, so the sum over directions does beat the sum of the termwise
   bounds: `S/(4a)` is the least *termwise* shift, not the global constant.  The comparison is now
   a theorem with no hypothesis on `A`: `twoModeShift_lt_termwise` proves
   `twoModeShift A a d < A²/(4a)` for every `d ≥ 1` and `a > 0`, because
   `√(A² + a²/4) ≤ A²/(4a) + 3a/2` is strict — the gap is
   `((A² − 2a²)² + 28a⁴)/(16a²)` after clearing the positive denominator — and
   `a(2d+1)/2 ≥ 3a/2`.  Since `twoModeShift` is decreasing in `d` (`a > 0`), the bound holds for
   every dimension, not only the smallest sector, so the improvement over the termwise bound is
   uniform in `d`.

   **The global constant on `Q(N^{1/2})`: what the two-mode optimum is, and what it is not
   (2026-11-04).**  §11.2 of `YangMillsFormClosureNonDiagonal` splits the question instead of
   leaving it open, and the split is a theorem.  The ladder form is a sum over directions,
   `q(x) = ∑ᵢ qᵢ(x)` with `qᵢ(x) = ∑ₙ Aᵢ√(nᵢ+1) conj(x(n+eᵢ)) x n` (`ladderDirForm`,
   `ladder_form_eq_sum_dir`), and so is the reference form `Q = ∑ᵢ Qᵢ`, `Qᵢ = ∑ₙ (nᵢ+1)‖x n‖²`
   (`dirWeight`); each `qᵢ` sees only the `i`-th occupation, the other coordinates merely slice it.
   Hence **`ladder_form_le_of_directional`**: any family of directional bounds
   `‖qᵢ‖ ≤ a Qᵢ + Sᵢ‖·‖²` yields `‖q‖ ≤ a Q + (∑ᵢ Sᵢ)‖·‖²`.  So the multidirectional constant —
   the "global constant on `Q(N^{1/2})`" — is **at most the sum of the directional constants**, and
   no improvement can come from the coupling of directions.  The termwise family
   `Sᵢ = Aᵢ²/(4a)` is admissible (`ladderDirForm_norm_le`), which is exactly why §10's AM–GM bound
   is the `∑ᵢ` of the directional shifts; and no admissible directional constant lies below the
   two-mode optimum (**`twoModeShift_le_of_twoModeBound`**: the kernel vector of
   `twoModeRatio_shift` is a directional state, `Qᵢ = α² + 2β²`, form `Aᵢαβ`, i.e. `A = Aᵢ/2`,
   `d = 1` in §11's normalization).  With `twoModeShift_lt_termwise` the directional constant is
   therefore sandwiched, for every `d`,
   `twoModeShift (Aᵢ/2) a 1 ≤ Sᵢ < Aᵢ²/(4a)`,
   and the sum of those gives the corresponding bracket for the whole form.  What the two-mode
   optimum is *not* is the global constant, and the reason is again exact rather than a caveat: the
   sharp `Sᵢ` is the top of the **ray** problem `√(n+1)x_{n+1}x_n` against `a(n+1)x_n²`, which
   carries no ambient dimension, no cut-off and no other coordinate.  That question is now answered
   (2026-11-04): `YangMillsFormClosureNonDiagonal` §11.3 proves the ray constant is
   **`B²/(4a) − a`** — one mass unit below the termwise `B²/(4a)`, because the shift `α = B/(2a)`
   removes exactly one mass unit from the occupation form and `a` is what one mass unit costs — and
   that it is sharp (`rayForm_le_sharp`, `ray_form_bound_iff`): the truncated Poisson vectors
   `α^m/√(m!)` satisfy the recurrence `√(m+1)u_{m+1} = αu_m` term by term, so the sum of squares
   vanishes and only `(B²/(4a))u_N²` is left uncovered, which is `o(‖u‖²)`.  Hence
   `twoModeShift (Aᵢ/2) a 1 ≤ Sᵢ ≤ Aᵢ²/(4a) − a`, and the global constant is at most
   `∑ᵢ (Aᵢ²/(4a) − a)`.  The transfer to the box is §11.4 of the same file: charging every raised
   edge to its head reindexes `Σ_{nᵢ+1<Λ}(nᵢ+1)‖x(n+eᵢ)‖²` as `Σ_m mᵢ‖x m‖² = Qᵢ − ‖x‖²`
   (`raiseWeightSum_eq`, `dirWeight_sub_mass`), which is where the single mass unit comes from, so
   the directional bound holds with `Sᵢ = Aᵢ²/(4a) − a` (`ladderDirForm_norm_le_ray`) and the global
   one with `∑ᵢ (Aᵢ²/(4a) − a)` (`ladder_form_norm_le_ray`).

What Phase 1 does **not** need, and what the plan does not ask of it: any statement about the
*interacting* theory or about the existence of a mass gap.  Those remain Phases 4–5, and the
separation `β∞ − θ∞ ≥ c₁Δ_ref` is still an input there (see the status of Phase 4).

---

### Phase 2: Quantum Channel Taming (The B. Simon Mechanism)

#### 2.1. Analytical Principle
For non-Abelian gauge models, classical flat directions do **not** imply a continuous spectrum in quantum mechanics. 
* By **Barry Simon’s Theorem** (*Some Quantum Mechanical Problems with a Clean Spectrum*, 1983), potentials of the form $V(x, y) = x^2 y^2$ on $L^2(\mathbb{R}^2)$ have **purely discrete spectrum** despite the infinite cross-shaped valleys along the $x$- and $y$-axes.
* **Physical Mechanism:** As $|x| \to \infty$ along a valley, the transverse potential $V_x(y) = x^2 y^2$ becomes an oscillator in $y$ with frequency $\omega(x) = |x|$. By the Heisenberg uncertainty principle, the zero-point energy of the transverse motion is:
  $$E_0(x) = \frac{1}{2} \hbar \omega(x) = \frac{1}{2} g |x| \xrightarrow{|x| \to \infty} \infty$$
* The "cross-sectional width" of the valley shrinks so rapidly ($w(x) \sim 1/\sqrt{g|x|}$) that quantum wave-packets cannot penetrate deeply into the valley without paying an infinite kinetic energy penalty.

#### 2.2. Mathematical Formulation for $SU(N)$ Field Space
**Correction (2026-11-08):** items 2–4 below are the original channel ansatz, not a proved
global inequality for `magPoly`. In particular the derivative/commutator cross term
prevents dropping the derivative piece from the square. S1 specifies the missing
localization, root-chart and error estimates.

For Yang–Mills on the product Hermite core $L^2(\mathbb{R}^{d_N})$:
1. Split the gauge fields into **Cartan modes** $A_{\parallel} \in \mathfrak{t}$ and **off-diagonal root modes** $A_{\perp} \in \mathfrak{su}(N) \setminus \mathfrak{t}$.
2. Expand the magnetic potential:
   $$V(A) = V_{\text{linear}}(A) + \frac{1}{4} g^2 \sum_{j, k} \|[A_j, A_k]\|^2 \ge \frac{1}{4} g^2 \sum_{\alpha \in \text{roots}} (\alpha(A_{\parallel}))^2 \|A_{\perp, \alpha}\|^2$$
3. Treat $A_{\perp}$ as an oscillator in the background of $A_{\parallel}$. The effective zero-point Hamiltonian on the Cartan subspace is:
   $$H_{\text{eff}}(A_{\parallel}) = -\frac{1}{2} \Delta_{\parallel} + \frac{1}{2} g \sum_{\alpha \in \text{roots}} |\alpha(A_{\parallel})|$$
4. Since $\sum_{\alpha} |\alpha(A_{\parallel})| \to \infty$ whenever $\|A_{\parallel}\| \to \infty$ outside the origin, $H_{\text{eff}}$ is **strictly confining** in all directions.

#### 2.3. Milestone 2: Formalizing the Effective Confining Barrier
* **Task:** Prove the functional inequality in Lean 4:
  $$\langle \psi, H_W \psi \rangle \ge \langle \psi, \left( -\frac{1}{2} \Delta + c_g \|A\| - C_0 \right) \psi \rangle \quad \forall \psi \in \mathcal{D}_{\text{Hermite}} \cap \mathcal{H}_{\text{phys}}$$
* **Deliverable:** A Lean module `BookProof.YangMillsEffectiveBarrier.lean` establishing that $H_W$ is bounded below by a globally coercive operator.
* **Status (2026-10-30): the mechanism is DONE; the domination inequality is the input, as an interface.**
  `BookProof.YangMillsEffectiveBarrier` (`BookProof/YangMillsEffectiveBarrier.lean`, no `sorry`)
  carries the Cartan/root split of the degree form of `BookProof.YangMillsFormDomination` —
  `parallelDegree` (the Cartan occupation `N` of a multi-index), `perpDegree`, `rootCount`, with
  `parallelDegree_add_perpDegree` splitting `∑ i, nᵢ` — and Simon's barrier at one root mode:
  `zeroPoint g N = ½ g √(N + ½) = transFreq/2`.  The mechanism's content is the growth, and that
  is proved: `zeroPoint_nonneg`, `zeroPoint_lt` (strictly increasing in the background) and
  **`zeroPoint_coercive`** — for every target `M` there is `K` with `M ≤ zeroPoint g N` for all
  `N ≥ K`.  On the field side this is `effPotential T g N = rootCount · zeroPoint g N` and
  **`simon_valley_lifted`**: with at least one root direction and `g > 0`, the effective energy
  along the Cartan valley exceeds any bound, so the valley is confined.  In its original
  two-dimensional form the model `simonPotential g x y = g²x²y²` has an *exactly* flat valley
  (`simonPotential_flat`) whose effective energy `simonEffective g x = zeroPoint g |x|` is coercive
  (`simonEffective_coercive`) — Simon's theorem's phenomenon, without its discreteness conclusion.
  The barrier is sublinear (`sqrt_le_add_quarter`, `zeroPoint_le_linear`: `√x ≤ x + ¼`), which is
  why it never competes with the kinetic term, and the transverse/longitudinal trade-off is
  `two_mul_sqrt_le`.  On the core the barrier is the quadratic form `barrierForm` (nonnegative for
  `g ≥ 0`, `barrierForm_zero_g` at zero coupling).
  The coupling is not a free parameter here: the quartic `:N²:` interaction contains the Cartan/root
  cross term `2 N_∥ N_⊥` (`crossDegreeForm`, and `quarticDegreeForm_ge_crossDegreeForm` proves the
  quartic form dominates it), which at background occupation `N` is an oscillator of frequency
  `√(2N + 1)` (`transFreq_sqrt_two`); with `g = √2` the barrier is exactly its zero-point energy
  (`zeroPoint_sqrt_two`).  So `zeroPoint (√2)` — not an arbitrary `g` — is the barrier the magnetic
  potential itself produces, which is what §2.2 item 2 (`½g²∑‖[A_j,A_k]‖²`) asserts.
  The §2.3 inequality is packaged as the structure `IsBarrierBound T g q`
  (`q ≥ degreeForm + barrierForm − C‖·‖²` on the Gauss–polynomial core); `formDomination_of_barrier`
  turns it into the Phase-4 `FormDomination` certificate (ratio `c₁`, shift `c₁μ₀ + C`), and
  `barrier_gap` gives the separation `c₁ Δ_ref` with the barrier included.

  **The inequality now holds for the Yang–Mills form `q_W` itself** (2026-10-30) —
  `BookProof.YangMillsMagneticQuartic` (`BookProof/YangMillsMagneticQuartic.lean`, no `sorry`).
  The magnetic energy of the field strength is, per mode, the sum of the squares of its components,
  `q_mag(c) = ∑_n (∑_a B_a(n)²)‖c n‖²` with `B_a(n) = ∑_i A_{a i} nᵢ` (`magComp`,
  `magneticEnergyForm`); in the canonical Cartan basis the components are the occupations
  themselves (`magComp_diag`).  Cauchy–Schwarz and `0 ≤ B_a ≤ N` give the two comparisons with the
  normal-ordered `:N²:` form,
  `quarticDegreeForm c ≤ d · q_mag(c)` (`quarticDegreeForm_le_magnetic`) and
  `q_mag(c) ≤ d · quarticDegreeForm c` (`magnetic_le_quartic`), i.e. the magnetic form *is* the
  quartic `:N²:` form up to the explicit factor `card`.  Since `q_W = degreeForm + q_N² + barrier`
  on the core, `barrierBound_quartic` transfers to `q_W`: **`barrierBound_yangMillsForm`** is
  `IsBarrierBound T g (yangMillsForm T g)` with the *same* explicit shift `C = K + (1 + K)²/4`,
  `K = rootCount T · g/2`, and **`yangMillsForm_certifiedGap`** is the §4.1 separation
  `c₁ Δ_ref ‖c‖² ≤ q_W(c) + C‖c‖²` on the vacuum-orthogonal sector.  So the interface is
  inhabited by `q_W` itself, not by a model of its interaction.  What remains is deriving the
  components `B_a` from the concrete potential (the `∂A + g[A,A]` normal ordering of
  `ChapterFockInteractionStability`) and the root-mode normal form; the form comparison no longer
  depends on either.

  **The Cartan components `B_a` are now derived, not assumed** (2026-10-30) —
  `BookProof.YangMillsFieldStrength` (`BookProof/YangMillsFieldStrength.lean`, no `sorry`).  The
  potential component is a *nested pair* `c† diag(A_a) c` — an outer creation–annihilation pair
  with the inner self-adjoint operator in between (`sandwich`).  **No normal ordering is needed**:
  the nested algebra multiplies pairs by composing the inner operators, so the contraction of
  Wick's theorem *is* the inner matrix product and the double-creation term is not in the algebra;
  and the one constant that could hide — the `+1` distinguishing `c c†` from `c†c` — is absent,
  since **`hopWord_pair_same`** shows the ordered pair acts on `n` by exactly `n_j`, with no
  constant term.  Consequently **`sandwich_diag_single`** gives the diagonal pair's eigenvalue
  `∑ j, m_j n_j` and **`sandwich_diag_magComp`** gives `B_a(n) = magComp A a n`; the energy form
  `½ ∑_a B_a²` is `magneticEnergyForm` read componentwise (`magneticEnergyForm_eq_sum`).

  **The assembly `F = ∂A + g[A,A]` and the root sector are now done, on the corpus's own
  operator** (2026-10-30) — `BookProof.Qym.ChapterYangMillsFieldStrengthSplit`
  (`BookProof/Qym/ChapterYangMillsFieldStrengthSplit.lean`, no `sorry`), which works with the
  field strength already in the repository rather than a model of it: `magPoly` of
  `BookProof.YangMillsHermite` (`B_{ia} = ε_{ijk}(∂_j A_{k,a} + f_{abc}A_{j,b}A_{k,c})` on the
  Gauss–polynomial core of `L²(ℝ⁹⁹)`, the `B` of `ymHamiltonian`) and the same shape in
  `BookProof.Sm.ChapterSmHamiltonian` (`smMagG`, `smMagW`, `smMagB` with the coupling `g_s`
  explicit).  Results: **`magPoly_eq_deriv_add`** splits it into `magDeriv` (linear in the
  configuration) plus `magComm` (the `g[A,A]` term); **`magOps_apply_eq`** is the same identity for
  the operators on the core, and both halves are symmetric (`magOpsDeriv_symmetricOn`,
  `magOpsComm_symmetricOn`) since both have real coefficients; **`two_smul_levi_contract`** shows
  the `ε`-contraction of *any* bilinear form is the contraction of its antisymmetrisation, so the
  non-abelian term is `½ ε_{ijk}[A_j,A_k]` and **`magComm_eq_zero_of_symmetric`** kills it on the
  commuting (Cartan) sector — which is exactly why the components there are the *linear* forms
  `magComp`.  Off the Cartan directions the root sector is quartic: in the `su(2)` root plane
  `[a₁E₊ + b₁E₋, a₂E₊ + b₂E₋] = (a₁b₂ − b₁a₂)H` (**`rootField_commutator`**) and the magnetic
  energy of that component is the **square** of the root determinant, `½‖[A₁,A₂]‖² =
  ‖a₁b₂ − b₁a₂‖²` (`root_energy`, `root_energy_real`), zero exactly on parallel amplitudes
  (`root_energy_eq_zero_iff`) and equal to `4 (Im(a₁\bar a₂))²` for hermitian fields
  (`root_energy_hermitian`).  And the reason no normal ordering arises in the potential is
  explicit: multiplication operators compose exactly, `mulOp (p * q) = mulOp p ∘ mulOp q`
  (`mulOp_mul`), so the quartic `A_{j,b}A_{k,c}` needs no Weyl symmetrisation — unlike the `πA`
  cross terms, where `[A_j, π_j] = i`.  Not claimed: that a general `f_{abc}` decomposes into
  `su(2)` root blocks, or any dynamical statement.

  **The split is carried to the Standard Model field strengths of record** (2026-10-30) —
  `BookProof.Sm.ChapterSmFieldStrengthSplit` (`BookProof/Sm/ChapterSmFieldStrengthSplit.lean`, no
  `sorry`), on `smMagG` (gluons, `f_{abc}` with `g_s`) and `smMagW` (weak bosons, `ε_{mbd}` with
  `g`) — the `B`'s that enter `smHamiltonian = ½ Σ π² + ½ Σ B²`.  **`smMagG_eq_deriv_add`** and
  **`smMagW_eq_deriv_add`** split each into `smDerivG`/`smDerivW` (linear) plus
  `smCommG`/`smCommW` (the `g[A,A]` term).  Each half has real coefficients
  (`realCoeff_smDerivG`, `realCoeff_smCommG`, and the `W` pair), so each is a *symmetric
  multiplication operator* on the Gauss–polynomial core (`smDerivG_symmetricOn`,
  `smCommG_symmetricOn`, `smDerivW_symmetricOn`, `smCommW_symmetricOn`), and the split is an
  identity of operators, not only of polynomials (`smFieldG_apply_eq`, `smFieldW_apply_eq`).
  `two_smul_levi_contract` is proved for the lattice dimension of the Standard Model as well, so
  **`smCommG_eq_quarter_bracket`** / **`smCommW_eq_quarter_bracket`** identify the non-abelian
  terms as `¼ ε_{ijk} g [A_j,A_k]` — the outer `½` is the one in the definition of `B`, the inner
  one comes from antisymmetrising the `ε`-contraction — and
  **`smCommG_eq_zero_of_symmetric`** / **`smCommW_eq_zero_of_symmetric`** kill them on the
  commuting (Cartan) sector, where the field strength is the derivative part alone.  Left as they
  are: the hypercharge `smMagB` (abelian, already linear, no commutator part) and the Higgs
  covariant derivative `smCovD` (a bilinear form whose non-abelian structure is the generator
  action `tgen`/`ygen` on the doublet, a multiplication by given matrices, needing no bracket
  identity).  The fermions are not part of `smHamiltonian`, so they play no role here either.

  **But the §2.3 inequality is now proved unconditionally for the quartic `:N²:` form**
  (2026-10-30) — the form the magnetic potential itself produces (see the cross-term computation
  above).  `barrierForm_le_linear` bounds the barrier linearly in the occupation
  (`rootCount·zeroPoint g N ≤ K (N+1)`, `K = rootCount·g/2`, from `zeroPoint_le_linear`), and
  **`barrierBound_quartic`** (`BookProof/YangMillsEffectiveBarrier` §6) is the instance
  `IsBarrierBound T g (quarticDegreeForm)` with the explicit shift `C = K + (1 + K)²/4`: the quartic
  grows like `N²` and pays for the kinetic degree form *and* the `√N` barrier at once.  Through the
  existing chain this gives `quarticFormDomination` (a `FormDomination` for the pure interaction
  form, ratio `c₁`, shift `c₁μ₀ + C`) and **`quartic_certified_gap`**: on the vacuum-orthogonal
  sector `c₁ Δ_ref · ‖c‖² ≤ q_N²(c) + C‖c‖²`.  So in the `:N²:` model the separation `c₁ Δ_ref` no
  longer depends on the unproved estimate; what remains is the identification `q_W = q_N²` itself.
  Nothing here claims a discrete spectrum for `H_W`.

---

### Phase 3: Construction of a Solvable Gapped Reference Operator $H_{\text{ref}}$

Rather than attempting to calculate the spectrum of $H_W$ exactly, construct a reference operator $H_{\text{ref}}$ that satisfies three conditions:
1. It is explicitly solvable on the product Hermite core (e.g., an anisotropic harmonic oscillator or a radially symmetric gapped system).
2. Its eigenvalues and spectral gaps are known in closed form:
   $$\sigma(H_{\text{ref}}) = \{\mu_0, \mu_1, \mu_2, \dots\}, \quad \mu_1 - \mu_0 \ge \Delta_{\text{ref}} > 0$$
3. It lower-bounds $H_W$ at the quadratic-form level.

#### 3.1. Construction of $H_{\text{ref}}$
On the $d_N$-dimensional Gauss–polynomial core (PDF Ch. 27.9, where $d_3 = 99$ for $SU(3)$):
$$H_{\text{ref}} = \sum_{k=1}^{d_N} \left( -\frac{\partial^2}{\partial x_k^2} + \omega_k^2 x_k^2 \right) + V_0(P)$$
where:
* $\omega_k > 0$ are the harmonic frequencies of the background Gaussian measure (`PhysHSGaussian`).
* $V_0(P)$ is a parity/charge projection that assigns energy $0$ to the vacuum state $\Omega$ and energy at least $\Delta_{\text{ref}} = \min_k \omega_k$ to any state orthogonal to $\Omega$ (or odd under parity).

#### 3.2. Milestone 3: Closed-Form Spectrum of $H_{\text{ref}}$
* **Task:** Formalize the spectrum of $H_{\text{ref}}$ in Lean 4 using the existing harmonic oscillator theorems (`BookProof.HarmonicOscillator.harmonicOscOp`):
  ```lean
  theorem href_spectral_gap (k : ℕ) :
    ∀ ψ ∈ D(H_ref), ψ ⊥ Ω → ⟨ψ, H_ref ψ⟩ ≥ (μ₀ + Δ_ref) ‖ψ‖²
  ```
* **Deliverable:** `BookProof.ChapterReferenceGap.lean`.
* **Status (2026-10-30): DONE**, `BookProof.ReferenceGap` (`BookProof/ChapterReferenceGap.lean`, no `sorry`).
  The `d`-dimensional symbol `refEnergy ω n = ∑ i, ωᵢ (nᵢ + ½)` is a port of physlib's
  `QuantumMechanics.HarmonicOscillator.eigenEnergy` (`ℏ = 1`, general `ω`) together with
  `refEnergy_strictMono`; at `d = 1`, `ω = 1` it is this repository's `harmonicSymbol`
  (`refEnergy_one_eq_harmonicSymbol`), so it sits on `harmonicOscOp`.  The gap is
  `refGap ω = min_k ω_k`, positive and attained (`refGap_pos`, `exists_refGap_eq`), and every
  excited level clears the vacuum by it (`refEnergy_ge_vacuum_add_gap`).  On the
  Gauss–polynomial core (finite coefficient families `(Fin d → ℕ) →₀ ℂ`) the milestone is
  `href_spectral_gap` with `coreNormSq`/`coreForm` as `‖ψ‖²` and `⟨ψ, H_ref ψ⟩`, the parity
  sector is `href_spectral_gap_of_parity`, and the bound is attained at the vacuum
  (`coreForm_vacuum`), so `Δ_ref` is the exact gap there.  Not done here: the `L²` closure
  of the core (basis expansion/summability) and the Phase-4 form domination.

---

### Phase 4: Relative Form Bounding in Lean 4

Once $H_{\text{ref}}$ is constructed, the analytical lower bound on the separation $\beta_\infty$ is derived by proving that $H_W$ dominates $H_{\text{ref}}$ in the sense of quadratic forms.

#### 4.1. The Form-Domination Inequality
Prove that there exist constants $c_1 > 0$ and $c_2 \in \mathbb{R}$ such that on the common core $\mathcal{D}$:
$$q_{H_W}(\psi) \ge c_1 \, q_{H_{\text{ref}}}(\psi) - c_2 \|\psi\|^2 \quad \forall \psi \in \mathcal{D}$$

By the variational minimax principle (Courant–Fischer):
* Ground state: $\lambda_0(H_W) \ge c_1 \mu_0 - c_2$.
* First excited state (or lowest state in the orthogonal/odd sector): 
  $$\lambda_1(H_W) \ge c_1 \mu_1 - c_2$$
* **Correction (2026-11-08): these two lower bounds cannot be subtracted.** With an
  independent ground upper bound $\lambda_0(H_W)\le U_0$, min–max instead gives
  $$\lambda_1(H_W)-\lambda_0(H_W)\ge c_1\mu_1-c_2-U_0.$$
  This is useful only when its right-hand side is positive and the relevant min–max
  levels and invariant sector have been identified. See S2 for the separate absolute
  one-particle bound needed by the outer-vacuum gap theorem.

#### 4.2. Leveraging Existing *Timepiece* Modules
This step directly integrates into existing modules:
* Use `BookProof.ChapterFockFieldPerturbation.lean` to control the cross-terms between linear gradients and the cubic/quartic non-Abelian potential.
* Use `BookProof.ChapterFockInteractionStability.lean` to convert relative form bounds into explicit spectral shift inequalities.

#### 4.3. Milestone 4: Form-Domination Certificate
* **Task:** Prove in Lean 4:
  ```lean
  theorem ym_form_dominates_href :
    ∃ (c₁ : ℝ) (c₂ : ℝ), c₁ > 0 ∧
    ∀ ψ ∈ D_core, quadForm H_W ψ ≥ c₁ * quadForm H_ref ψ - c₂ * ‖ψ‖²
  ```
* **Deliverable:** `BookProof.YangMillsFormDomination.lean`.* **Status (2026-11-04): the implication, the domination inequality on the Gauss–polynomial core,
 the `L²` closure of that core, the Faris–Lavine comparison for a non-diagonal interaction, and
 the `L²` lift of the *interacting* form — its bottom bound *and* its Faris–Lavine comparison
 with relative bound `a < 1`, on the form domain — are DONE** (`BookProof.YangMillsFormClosure`,
 `BookProof.YangMillsFormClosureNonDiagonal`); what remains open is the *uniformity in the
 cut-off* of the Hilbert–Schmidt / relative bound, as described at the end of this item.
  `BookProof.YangMillsFormDomination` (`BookProof/YangMillsFormDomination.lean`, no `sorry`)
  carries the certificate as a structure, `FormDomination ω q` = ratio `c₁ > 0`, shift `c₂`, and
  `∀ c, c₁ · coreForm ω c − c₂ · coreNormSq c ≤ q c` on the Phase-3 core.
  `coreForm_ge_vacuum` puts the vacuum at the bottom of the reference form, so domination also
  bounds the ground level: `ground_bound` gives `c₁μ₀ − c₂`, `excited_bound`
  (`c 0 = 0`) gives `c₁(μ₀ + Δ_ref) − c₂`, and `certified_separation`/`certified_gap_pos` show
  the difference is exactly `c₁ Δ_ref > 0` — the uniform separation `β_∞ − θ_∞`.  The certificate
  is inhabited (`formDomination_self`, `q_ref` dominates itself), so the structure is not
  vacuous.  A **concrete, non-self-referential inhabitant** is `freeFormDomination`: the free
  (quadratic) part's form on the Hermite core — the *degree* form
  `degreeForm c = ∑ n, (∑ i, nᵢ)‖c n‖²`, i.e. the form of `−Δ` in oscillator units — dominates
  the reference form with ratio `c₁` and shift `c₂ = c₁μ₀` whenever `0 < c₁` and `c₁ωᵢ ≤ 1`
  (`scaled_refEnergy_sub_zero_le_degree` is the pointwise inequality; `exists_free_ratio`
  shows such a `c₁` always exists).  That instance yields a concrete gap:
  `degreeForm_ge_gap` — on the vacuum-orthogonal sector the kinetic form is at least
  `c₁Δ_ref · ‖c‖²`.  The **interacting (quartic) part** enters through monotonicity, not through a
  new estimate: the magnetic term is a sum of squares, so its form is nonnegative, and
  `FormDomination.mono` (a certificate for `q` is one for any `q' ≥ q`) shows it cannot spoil the
  comparison — `interactingFormDomination` is the certificate for
  `degreeForm + quarticDegreeForm` (`quarticDegreeForm` is the normal-ordered `:N²:` quartic),
  and `interactingForm_ge_gap` keeps the gap.  The Yang–Mills form itself is the last piece, and it
  is supplied by Phase 2, not by a new estimate: `yangMillsFormDomination`
  (`BookProof/YangMillsMagneticQuartic.lean`, the section “The consequence for `q_W`”) is the certificate
  `BookProof.YangMillsFormDomination.FormDomination ω (yangMillsForm T g)` with ratio `c₁` and shift
  `c₂ = c₁μ₀ + quarticShift T g`, `quarticShift T g = K + (1 + K)²/4`, `K = rootCount T · g/2`, so
  the plan's `ym_form_dominates_href` is inhabited by the Yang–Mills form of record and not by a
  model of it.
  The route that produces it is Phase 2: `BookProof.YangMillsEffectiveBarrier.formDomination_of_barrier`
  shows that a bound `q_W ≥ degreeForm + barrierForm − C‖·‖²` (`IsBarrierBound`, the §2.3 milestone
  with Simon's zero-point barrier included) already yields the certificate, with shift `c₁μ₀ + C`,
  and `barrier_gap` then gives the same `c₁ Δ_ref` separation.  So the remaining inequality may be
  taken in either form; the barrier version is the one the physics argument naturally produces,
  and it is now *proved* for the quartic `:N²:` form (`barrierBound_quartic`) **and for `q_W` itself**
  (`barrierBound_yangMillsForm`, §2.3 above), so neither the interface nor its `q_W` instance is an
  assumption any more; it also holds with shift `0` (`barrierBound_yangMillsForm_zeroShift`: the
  quartic form is nonnegative and sits in `q_W` beside both terms the inequality needs).

  **What the completed inequality does *not* depend on, and what is still open.**  The components
  are derived, not assumed: `B_a` is `magComp` read off the nested pair `c† diag(A_a) c`
  (`sandwich_diag_magComp`, §2.3), `F = ∂A + g[A,A]` splits on the corpus's own `magPoly`
  (`magPoly_eq_deriv_add`, `magComm_eq_zero_of_symmetric`, and the `smMagG`/`smMagW` twins), and
  the root sector is quartic with energy `‖a₁b₂ − b₁a₂‖²` (`rootField_commutator`, `root_energy`,
  `root_energy_eq_zero_iff`) — so the field-strength components and the root-mode structure are not
  inputs of §4.3, and the inequality needs neither the unbounded charge of Phase 1 nor the
  perturbation theory of §4.2.  The **`L²` closure of the Gauss–polynomial core** — the step this
  paragraph used to name as open — is now proved in `BookProof.YangMillsFormClosure`
  (`BookProof/YangMillsFormClosure.lean`, no `sorry`).  `L2 d = ℓ²(Idx d, ℂ)` receives the core by
  `coreEmbed` with `‖coreEmbed c‖² = coreNormSq c` (`norm_sq_coreEmbed`) and dense range
  (`dense_range_coreEmbed`, from `lp.hasSum_single` and the truncations).  All forms of the
  chapter are diagonal in the multi-index, `diagonalForm f c = ∑ n ∈ c.support, f n ‖c n‖²`, and
  the closed form `closedForm f x = ∑' n, ofReal (f n) · ofReal (‖x n‖²)` is *the closure of the
  core form*: it extends it (`closedForm_coreEmbed`), it is lower semicontinuous
  (`lowerSemicontinuous_closedForm`), and it is the supremum of the core forms of the truncations
  (`closedForm_eq_iSup_truncate`).  Domination transfers with no loss: `formDomination_symbol`
  reads a certificate as the symbolwise inequality `c₁μ(n) − c₂ ≤ g(n)`, and
  `formDomination_closed` gives
  `ofReal c₁ · closedForm μ x ≤ closedForm g x + ofReal (max c₂ 0) · closedNormSq x` for every
  `x : L²`.  The form of record is covered: `yangMillsForm T g` is diagonal
  (`Barrier.yangMillsForm_eq_diagonalForm`), so `yangMillsForm_closed` transfers its certificate
  and `closed_yangMillsGap` gives the `c₁Δ_ref` separation on the whole vacuum-orthogonal sector
  of `L²`.  What the closure still does not supply is the statement about the *spectrum* of `H_W`
  — discreteness and a mass gap need the self-adjoint operator, not only its closed form.

  **The non-diagonal interaction, on the core and on `L²` (2026-11-04).**  The second half of that boundary —
  "not for a magnetic interaction mixing multi-indices" — is addressed in
  `BookProof.YangMillsFormClosureNonDiagonal` (`BookProof/YangMillsFormClosureNonDiagonal.lean`, no
  `sorry`), and by the *Faris–Lavine* route rather than the termwise one.  The interaction is a
  kernel `K : (Fin d → ℕ) → (Fin d → ℕ) → ℂ` with kernel form
  `kernelForm K c = ∑ m ∈ supp c, ∑ n ∈ supp c, Re(K m n · c n · conj(c m))`, which couples
  distinct multi-indices whenever `K` is off the diagonal — the magnetic terms the diagonal theory
  cannot see.  The form bound the interaction enters through is a **Hilbert–Schmidt** one:
  `kernelForm_sq_le` is the two-index Cauchy–Schwarz inequality (square of the absolute form ≤
  Hilbert–Schmidt sum × `coreNormSq²`), so a kernel whose finite-square sums are bounded by `σ²`
  obeys `abs_kernelForm_le_of_hs`: `|kernelForm K c| ≤ σ · coreNormSq c` for **every** core state,
  with no support restriction.  `farisLavine_domination` is the comparison itself: if `q'`
  dominates the reference form with ratio `c₁` and shift `c₂`, and `|qK| ≤ a q' + b‖·‖²` with
  relative bound `a < 1`, then the **sum form** `q' + qK` dominates with ratio `(1 − a)c₁ > 0` and
  shift `(1 − a)c₂ + b` — the interaction may lower the form, and the factor `1 − a` is what that
  costs; the ratio never reaches zero, so the certified separation survives.  The bounded case is
  separate and sharper in the ratio: `farisLavine_of_bounded_interaction` (`a = 0`) keeps `c₁`
  unchanged and adds only `b` to the shift.  A concrete, genuinely off-diagonal instance is
  `hoppingKernel m₀ n₀` (the matrix unit at `(m₀, n₀)`): its Hilbert–Schmidt sums are bounded by
  `1` (`hoppingKernel_sq_sum_le`), so `abs_hoppingForm_le` gives the form bound with `σ = 1`, and
  **`hopping_farisLavine`** concludes that the Yang–Mills certificate plus the hopping interaction
  still dominates with the *same* ratio `c₁` and shift `c₂ + 1`.  `hopping_couples` shows the
  interaction really does read a product of coefficients rather than moduli — at `a₀ = b₀ = 1` it is
  `1`, at `a₀ = 1, b₀ = i` it is `0`, although both states have the same coefficient moduli — so no
  diagonal form can represent it.  **The `L²` lift of the interacting form is proved (2026-11-04)**:
  §5 of the same module defines `closedKernelForm K x` as the weighted double series over all of
  `Idx d × Idx d` (absolutely convergent for every `x : L²`), bounds it by `σ‖x‖²` for the *same*
  `σ` (`abs_closedKernelForm_le`, Hölder with exponents `2, 2`), identifies it with `kernelForm` on
  the core (`closedKernelForm_coreEmbed`), and proves the bottom bounds on the form domain:
  `closed_diagonal_add_kernelForm_ge` and `closed_sector_bottom_ge_interacting`.  So, *when the
  total Hilbert–Schmidt mass is finite*, the off-diagonal interaction is a bounded form
  perturbation of the closed diagonal form — continuous, hence closed on the same domain — and
  Phase 5's bottom statements hold on `L²`, not only on the core.  The **ratio** is carried over
  as well, in §6: `closed_farisLavine_domination` states `c₁ (closedForm μ x).toReal ≤
  (closedForm g x).toReal + closedKernelForm K x + shifts` with the relative bound `a < 1` intact,
  the finiteness `closedForm g x ≠ ⊤` being the only extra hypothesis.  **The cut-off uniformity is now
  proved on the box (2026-11-05).**  §11.4's ray decomposition gives the ladder the constant
  `Σᵢ (Aᵢ²/(4a) − a)` with the relative bound `a` *chosen* rather than measured, and §12.1 of the
  same module carries it to the cut-off: `sum_dirWeight_eq` identifies the sum of the directional
  reference forms with the degree symbol `Σₙ (|n| + d)‖x n‖²`, so `ladder_form_le_degree` bounds
  the ladder form by `a · degree + (Σᵢ (Aᵢ²/(4a) − a)) · mass`, and at `a = 1/2`
  (`ladder_form_le_degree_half`) the shift is `(Σᵢ Aᵢ²)/2 − d/2`.  **Neither constant mentions `Λ`**,
  so the relative bound is uniformly bounded away from `1` and the Hilbert–Schmidt branch — whose
  constant was `√(m_Λ)`, of order `Λ^{(d+1)/2}` — is no longer what the cut-off argument rests on.
  The `L²` transfer is proved as well (§12.2 of the same
  module, 2026-11-05): `abs_closedKernelForm_boxKernel_le` bounds
  `closedKernelForm (boxKernel Λ A) x` by `a · (closedForm degree x).toReal
  + max (Σᵢ (Aᵢ²/(4a) − a)) 0 · ‖x‖²`, and `closed_farisLavine_boxKernel` hands that bound to §6's
  `closed_farisLavine_domination`, so the ladder interaction enters the comparison at ratio
  `(1 − a)c₁ > 0` with `a ∈ (0,1)` chosen and a shift free of `Λ`.  **The cut-off uniformity of the
  relative bound is therefore closed end to end, on the closed form.**  So
  Phase 5's `c₁Δ_ref` is certified on the core for the off-diagonal case, and on `L²` for the
  diagonal one at full strength — with the interacting term bounded below on `L²` by `−σ‖x‖²`,
  which preserves the *bottom* and not yet the *ratio* of the separation.

---

### Phase 5: Discharging Hypotheses in the Verification Pipeline

Assume an actual continuum spectral exclusion and positive Temple denominator have
been established analytically (S2–S3), rather than inferred from reference thresholds.
The formulas below require that additional input; they do not construct it.

#### 5.1. Supplying the Missing Input to Temple's Inequality
In `BookProof.ChapterRitzCertificate.lean`, replace the open hypothesis with the analytical bound:
$$\beta_\infty := \theta_\infty + c_1 \Delta_{\text{ref}}$$
The Temple denominator is now uniformly bounded away from zero for **all** approximation orders $n$:
$$\beta_n - \theta_n \ge \frac{1}{2} c_1 \Delta_{\text{ref}} > 0 \quad \forall n \ge n^*$$
Consequently, the Temple uncertainty:
$$\delta_n = \frac{\eta_n^2}{\beta_n - \theta_n} \le \frac{2 \eta_n^2}{c_1 \Delta_{\text{ref}}}$$
is strictly controlled. 

* **Status (2026-10-30): §5.1 is DONE; §5.2's arithmetic is DONE, its analytic transfer is not.**
  `BookProof.TempleSeparationBound` (`BookProof/Sirk/ChapterTempleSeparationBound.lean`) now carries
  the uniform residual bound: `temple_uncertainty_le_of_residual` proves §5.1's
  `δ_n = ε_n²/(β_n − θ_n) ≤ ε_n²/c ≤ η_n²/c` under `β − θ ≥ c`, and
  `certified_edge_of_uniform_residual` is the certificate statement `θ − η²/(c₁Δ_ref) ≤ l` with
  the analytic constant.  §5.2's displayed inequality is
  **`continuum_gap_unconditional`**: with `c₁, Δ_ref > 0`, a uniform residual `η_max` on the
  odd-sector vector and the variational upper bound `l_even ≤ θ_even`, the gap obeys
  `(θ_odd − θ_even) − 2η_max²/(c₁Δ_ref) ≤ l_odd − l_even`, and `continuum_gap_positive` shows it
  is strictly positive once the Ritz separation exceeds the correction — so the denominator no
  longer degrades with the order.  The transfer across the limit is in
  `BookProof.TempleContinuumGap` (`BookProof/Sirk/ChapterTempleContinuumGap.lean`): a spectral
  separation gives a *quantitative* gap at the window centre, `gapAt_of_separation`
  (`((β−l)/2)‖x‖ ≤ ‖(A − (l+β)/2)x‖`, from Pythagoras plus the Temple factor
  `factor_nonneg_of_separation`), at the plan's constant `gapAt_of_form_domination`
  (`c₁Δ_ref/2` at `l + c₁Δ_ref/2`), and by `SpectralGapStability.gapAt_of_tendsto` it survives an
  **operator-norm** limit unchanged (`gap_survives_norm_limit`), leaving a hole
  `c₁Δ_ref/2` in the limit's spectrum (`notMem_spectrum_of_separation_limit`,
  `continuum_gap_of_form_domination`).  The **strong-resolvent** mode of the same hypothesis is
  proved too (§6 of the chapter, 2026-10-31): `certifiedResolvent` is the left inverse of
  `A − λ` the gap guarantees, with `certifiedResolvent_left` and `certifiedResolvent_norm`
  (`‖Rξ‖ ≤ ‖ξ‖/d`); `gap_survives_strongResolvent` turns **pointwise** convergence of those
  certified resolvents to a left inverse of `B − (l+b)/2` into `GapAt B ((l+b)/2) ((b−l)/2)`,
  **without** assuming the uniform bound (it is `certifiedResolvent_norm`, read off the
  separation), and `continuum_gap_of_form_domination_strongResolvent` is the same at the plan's
  constant `c₁Δ_ref/2`, together with the spectral hole
  (`notMem_spectrum_of_strongResolvent_limit`).  The uniform bound is therefore free in both modes;
  what is still conditional is the uniform `SpectralSeparation` at the analytic constant, as §5.1
  assumes, and the fact that the truncation family converges at all — in either mode.

#### 5.2. Transferring Across the Strong-Resolvent Limit
Because $H_n \to H_F$ strongly in the resolvent sense (`weyl_hashimoto_selects_friedrichs`), apply the strong-resolvent spectral theorem (derived from Reed–Simon VIII.24 as discussed in the previous section):
```lean
theorem continuum_gap_unconditional :
  gap(H_F) ≥ (θ_odd - θ_even) - (2 * η_max² / (c₁ * Δ_ref)) > 0
```
**Correction (2026-11-08):** this is a historical schematic target, not an unconditional
continuum theorem. Its separation, residual, sector and limit hypotheses must be supplied.
The outer `dGamma` lift additionally needs a strictly positive absolute one-particle form
bound; an even/odd inner excitation gap alone does not supply it. See S2–S4.

* **Status (2026-10-31): the nested-Fock lift, the coincident-point product and both convergence
modes (operator-norm and strong-resolvent) are now proved; the analytic separation and the fact
that the truncations converge are not.**  `BookProof.TempleContinuumGap`
  (`BookProof/Sirk/ChapterTempleContinuumGap.lean`) §3–4 put the lift on the actual Timepiece
  structure rather than beside it:
  - *nested Fock space / number conservation.*  A separation `spec T ⊆ {l} ∪ [β, ∞)` bounds the
    one-particle operator below (`sub_const_nonneg`, `form_gap_of_separation`), and
    `nestedFock_gap_of_separation` / `nestedFock_gap_of_certified_edge` lift it to the nested Fock
    space: `dΓ(opCol b A)` — built from `a†_j a_k` only, hence outer-particle-conserving —
    annihilates the vacuum and has Fock gap `l` on every vacuum-orthogonal finite-occupation
    state.  At the plan's constant the same theorem also delivers the one-particle `GapAt` of
    §5.1, so the two sides meet in one statement.
  - *the same-point product of outer fields.*  The interaction is a polynomial in the fields, so
    its coefficients contain products at a coincident Euclidean point, where a product of
    distributions is ambiguous.  The formalism never forms it: `dft_samePointProduct` (the
    product-to-convolution theorem) makes the momentum transform of the same-point product the
    convolution `n⁻¹ Σ_p F̂(p) Ĝ(k−p)`; `dft_mul_momentumCol` shows multiplication by a symbol is
    the momentum-transfer matrix `(k,i) ↦ n⁻¹V̂(k−i)` — an ordinary number-preserving
    one-particle matrix; `momentumCol_samePointProduct` shows the coefficient of a product of two
    fields is itself the convolution `n⁻² Σ_{p+q=k−i} F̂(p) Ĝ(q)`, every term carrying conserved
    momentum; `samePointProduct_form_eq_momentum` identifies the *form* the Phase-4 domination
    evaluates with that momentum convolution (Plancherel, `sum_conj_dft_mul_dft`); and
    `samePointProduct_real_self_form_nonneg` gives the positivity of the squared real field, i.e.
    the `IsPosCol`-shaped input the `dΓ` lift consumes.
  - *the strong-resolvent mode of the transfer.*  Both modes of §5.2's hypothesis are now proved:
    the operator-norm one (`gap_survives_norm_limit`) and the strong-resolvent one (§6:
    `gap_survives_strongResolvent`, `notMem_spectrum_of_strongResolvent_limit`,
    `continuum_gap_of_form_domination_strongResolvent`), the latter from pointwise convergence of
    the certified resolvents alone — strong-resolvent convergence is *weaker* than norm
    convergence, so this is the mode a truncation family actually delivers.
  - *the uniform separation at the operator level (2026-11-05).*  `BookProof.YangMillsFormClosureND`
    §13 now builds the operator the cut-off closed forms define: `diagCLM c hM` on `L²`,
    self-adjoint (`diagCLM_isSelfAdjoint`), whose form on the cut-off `s` is exactly
    `diagonalForm c (truncate x s)` (`re_inner_diagCLM_cutoff`) — for a bounded symbol the form is
    closed as it stands, so its Friedrichs extension is the operator itself.  The minimax statement
    is proved pointwise, without any spectrum computation, because the Rayleigh quotients of a
    diagonal operator are the symbol values: a symbol that is `l` or at least `l + c₁Δ` everywhere
    gives `GapAt A (l + c₁Δ/2) (c₁Δ/2)` (`gapAt_diagCLM_of_symbol_separation`), and
    `cutoff_operator_uniform_gap` gives the cut-off family a self-adjoint operator with gap
    `c₁Δ/2` at `c₁Δ/2` whose constants do **not** involve the cut-off `s`.
    `cutoff_operator_interacting` adds a bounded self-adjoint interaction and loses exactly `‖K‖`
    (the Faris–Lavine step in the bounded mode).
  - *the convergence, and the gap of the limit (2026-11-05).*  §14 supplies the left end §5.2 was
    missing.  The cut-off family does **not** converge in operator norm — the symbol changes on an
    ever larger box, so `‖A_s − A‖` is governed by the symbol outside `s` — hence the mode is strong
    convergence.  `coordBox` is a monotone cofinal family of boxes, `tendsto_tail_coordBox` proves
    that the cut-off tail of a state vanishes (the partial sums over a cofinal family converge to
    the whole `∑'`), `tendsto_diagCLM_cutoff` assembles the strong limit, and
    `gapAt_of_strong_tendsto` transfers a uniform `GapAt` because a lower bound valid at every
    approximant passes to the limit of norms.  The result is `gapAt_cutoffLimit` (`GapAt` at
    `c₁Δ/2`) and `notMem_spectrum_cutoffLimit` (the window centre is not in the spectrum), with no
    cut-off in the constants.  §15 then removes §13's global bound: `cutoffBound` bounds a cut-off
    of an unbounded symbol by a finite sum, so the §12.2 degree symbol enters the operator picture
    (`re_inner_diagCLM_cutoffSymbol`), and `gapAt_cutoffDegreeSymbol` reads its box gap `d/2`.
    §16 states Kato–Rellich at a relative bound below one: `katoRellich_gap` turns
    `‖K x‖ ≤ a‖A x‖ + b‖x‖` with `a < 1` into self-adjointness plus a gap
    `(1 − a)dd − (a|lam| + b)`, and `cutoffLimit_interacting` applies it to §14's limit.
  - *the limit operator, and the resolvent mode (2026-11-05).*  §17 constructs the operator the
    cut-offs are cut-offs *of*: multiplication by the unbounded symbol on the states with summable
    weighted squares.  It is symmetric on that domain, and its resolvent is a **bounded** operator
    (`‖R ξ‖ ≤ δ⁻¹‖ξ‖`) because `(c n − lam)⁻¹` is bounded once the symbol keeps its distance from
    `lam`; both inverse identities hold, so the gap holds on the domain and the degree symbol's
    operator is gapped by `d/2` at `d/2` — the same constant as the box gaps of §15.  §18 then
    discharges §5.2's hypothesis *literally*: the cut-off resolvents are the reciprocal-symbol
    operators, they converge pointwise to the limit resolvent (the symbols agree on the box and are
    both bounded off it), and with the limit's left inverse the strong-resolvent transfer lemma
    yields the gap and the spectral hole with **no hypothesis remaining**.  The same convergence
    holds for the degree cut-offs, whose limit is the unbounded resolvent.
  - *self-adjointness of the unbounded operator (2026-11-05).*  §19 supplies what §17 left open, and
    it does so by **Faris–Lavine**, not by a Friedrichs form: the criterion needs a positive `N` on
    the same domain and a commutator bound, and no closability or semiboundedness of a form.  The
    symbol is real, so `N = T` makes the commutator form vanish identically and the bound hold with
    constant `0`; the two hypotheses that remain are the paper's — the form is nonnegative (where
    the symbol is assumed nonnegative) and `T + 1` is onto (the resolvent at `−1` in disguise, the
    reciprocal of `c n + 1` being bounded by `1`).  The conclusion is trivial deficiency, hence a
    self-adjoint operator on a domain containing the operator's own domain and agreeing with it
    there; the finite-support states are dense, so the extension theory applies.  The degree
    symbol's operator is the instance.
  - *the spectrum of the unbounded symbol (2026-11-05).*  §20 needs no extension theory: the
    diagonal operator is self-adjoint on its **maximal** domain.  Testing the representing identity
    of the adjoint domain against coordinate vectors reads off `c n · φ n = η n`, so the adjoint
    domain sits inside the domain (`memDom_of_mem_adjointDomain`) and, by §17's symmetry, equals it:
    `adjointDomain_diagSubLin`.  The bundled `UnboundedSelfAdjoint` `diagUnbSelfAdjoint` is then the
    input of the workspace's unbounded spectral theorem — `unbounded_multiplication_model_general`
    of `BookProof.ChapterUnboundedSpectralModel`, the Cayley route — applied as
    `diagUnb_multiplication_model`.  The concrete spectral statement is elementary and exact:
    `InResolventSet` (bounded two-sided invertibility of `T − lam`) is equivalent to a positive
    distance between `lam` and the symbol's range (`inResolventSet_iff_exists_gap`), so the spectrum
    is the **closure of the range of the symbol** (`closure_range_eq_compl_resolvent`).
  - *form→operator, the Yang–Mills operator, and Källén–Lehmann (2026-11-05).*  §21 supplies the
    step §5–§6 recorded as missing: for a bounded symmetric perturbation the sum form
    `q_c + q_K` **is** the quadratic form of the self-adjoint operator `T + K` on the maximal
    domain (`diagSumLin_isSelfAdjointOn`, `re_inner_diagSum`), its form domain `∑ |c n| ‖x n‖² < ∞`
    contains the operator domain and is dense, and the lower bound `θ − σ` is read off on it.  §22
    then identifies the Yang–Mills one-particle operator: the form of record is diagonal, its symbol
    is `N + N² + rootCount·zeroPoint` in the occupation, and the closed form of that symbol *is*
    `q_W` on the core and the quadratic form of `diagUnb` of it on the domain — so the operator is
    the diagonal one, not an abstract `T` the form merely dominates.  Its spectrum is
    `{B} ∪ [B + 2, ∞)` with `B = rootCount·g/(2√2)` the vacuum barrier: **the gap above the vacuum
    is exactly `2`**, and the barrier shifts the spectrum without changing the spacing.  `OSReconstruction.Clustering` §6 closes
    the Källén–Lehmann direction for atomic spectral measures — masses above `m` decay the
    two-point function at rate `m` with the sharp constant, and decay at rate `m` forces every
    positively weighted mass to be at least `m`, so the rate *is* the bottom of the mass spectrum —
    and turns such a representation of the connected correlators into `SchwingerClustering`.
  - *Kato–Rellich at `a < 1`, non-atomic Källén–Lehmann, and the reduced sector (2026-11-05).*
    `BookProof.YangMillsFormKLMN` §23 proves the **KLMN theorem at form level** for diagonal forms:
    the form norm is finite exactly on `formDom` (`formENN_ne_top_iff`), it is lower semicontinuous
    in `L²` (`formENN_le_of_tendsto`, `formTsum_lsc`, `formDom_of_tendsto` — Fatou on the monotone
    partial sums of the sign-free series), the sum form's domain is the *unperturbed* one whenever
    `|b n| ≤ a c n + β` with `a < 1` (`formDom_add_of_relativeBound`,
    `formDom_of_relativeBound_add`), it is bounded below by `(1 − a)θ − β` on that domain
    (`formSum_ge_formDom`), and it is the quadratic form of the self-adjoint `diagUnb (c + b)`
    (`klmn_selfAdjoint`, `klmn_form_eq_inner`, `klmn`).  So the branch the continuum needs is a
    theorem about the form, not a hypothesis.  §24 identifies the **reduced sector's magnetic
    slot** with §22's diagonal one: the transverse sector is invariant under the diagonal operator
    (`diagUnb_mem_reducedSector` — no coordinate mixing, hence no off-diagonal ladder can appear by
    restriction), the barrier is the constant vacuum value there (`yangMillsSymbol_on_sector`), and
    the gap `2` survives the restriction with a strictly positive rate (`sector_gap`,
    `sector_gap_pos`).  `OSReconstruction.Clustering` §7 removes atomicity from the
    Källén–Lehmann step: for an arbitrary finite Borel measure, `laplace_le_of_massGap` gives decay
    at the gap's rate and `measure_Iio_eq_zero_of_laplace_decay` forces a measure to vanish below
    the rate, so the rate is the bottom of the *support* of `dρ`; `laplace_map_withDensity` gives
    the representation in a multiplication model, `∫ w x e^{−τ f x} ∂μ` — the measurable functional
    calculus `e^{−τM_f} = M_{e^{−τ f}}` as a KL representation, which is the shape
    `ChapterSpectralMultiplication` produces for a normal bounded operator with a cyclic vector, and
    which has no atomicity hypothesis anywhere.  - *The cut-off-uniform relative bound (2026-11-06).*  The relative form bound is uniform in the
    cut-off, and the chapter now says so.  §10's AM–GM pays the ladder in the reference form rather
    than in `‖x‖²` — `Sᵢ^*Sᵢ = Aᵢ²diag(nᵢ+1)` and `SᵢSᵢ^* ≤ Aᵢ²` because a raise is injective
    (`sum_raiseIdx_le`) — giving `‖q_K(x)‖ ≤ ½Q(x) + ½(ΣᵢAᵢ²)‖x‖²` with **no** `Λ` in either
    constant (`ladder_form_norm_le`, `ladder_form_abs_re_le`); §11 records the trade-off
    `(a, b) = (ε/2, ΣAᵢ²/(2ε))` as a Pareto frontier (`amgm_pareto_iff`, `amgm_min_shift`), so
    `1/2` is a weight choice, not a forced ratio.  §12.1–12.2 transfer the bound to the closed form
    with the *degree* symbol as reference (`sum_dirWeight_eq`, `ladder_form_le_degree`,
    `abs_closedKernelForm_boxKernel_le`, `closed_farisLavine_boxKernel`), and
    `closed_farisLavine_boxKernel_half` is the unit-weight member: ratio `1/2`, shift
    `max ((ΣᵢAᵢ²)/2 − d/2) 0`, the same numbers at every `Λ`.  So `a(Λ) = 1/2` is one number below
    `1` rather than a family indexed by the cut-off; what §7's `σ(Λ) ≍ Λ^{(d+1)/2}` shows is only
    that the *bounded-perturbation* reading cannot produce it.
  - *Strong continuity of the transfer semigroup (2026-11-06).*  `ℋ` is assembled
    (`OSReconstruction.HilbertSpace`) and the semigroup on it is now **strongly continuous at
    `0`**: `tendsto_physEvolCompletion` proves `τ ↦ P(τ)z` is continuous at `0` for every
    `z ∈ ℋ` from continuity of the two-point function `τ ↦ ⟨T(τ)F,F⟩` — the OS axiom — together
    with contractivity.  The two ingredients are `osBilin_evol_self`: contractivity at `τ` and at
    `−τ` sandwich `‖T(τ)F‖`, so the evolution is an isometry on `𝔄/𝔑`; and then
    `‖T(τ)x − x‖² = 2(⟨x,x⟩ − ⟨T(τ)x,x⟩)` (`continuous_norm_physEvol_sub`) is continuous in `τ`,
    vanishing at `0`.  Density of `𝔄/𝔑` in `ℋ` plus contractivity finish by `ε/3`.  So strong
    continuity is *derived*, not assumed of `T`.  In the Fock realization of the corpus the
    continuity hypothesis is exactly what the ESA/Faris–Lavine route gives: the inner Hamiltonian
    is sandwiched between outer creation and annihilation operators, the closed form dominates the
    perturbation (`closed_farisLavine_boxKernel`), and the resulting Friedrichs/Stone object is
    strongly continuous by construction, so its matrix elements are continuous.  The Fock side also
    has a *proved* link to the 4d theory, at the level of Hamiltonians: in the Weyl gauge `A₀ = 0`
    the BRST gauge-fixing term vanishes (`BookBrstGaugeFixing.bookGfTerm_eq_zero_of_Afield0`, QYM
    instance `su2_bookGfTerm_eq_zero_of_Afield0`), the 4d Hamiltonian reduces to the 3d sum of
    squares (`YangMillsHermite.ymHamiltonian_quadForm`), and `QymTimeIndependent.ymFock_weylGauge_timeIndependent`
    gives that operator a fixed self-adjoint generator with unitary propagator.  What is missing is
    the Hilbert-space map `ℋ ≅ Γ(H₁)`, not the operator identification.
  - *The generator (2026-11-06).*  `OSReconstruction.Generator` constructs it.  The domain is
    convergence of the difference quotient — `HasGen`/`genDomain`, closed under the vector
    operations because a limit of sums is the sum of limits (`hasGen_add`, `hasGen_smul`).  The
    limit is along `𝓝[≠] 0`, not `𝓝 0`: at `τ = 0` the quotient `τ⁻¹ • (P(τ)z − z)` is junk
    (`0⁻¹ = 0`), so including that point would force the limit to vanish and shrink the domain to
    the common fixed points of the `P(τ)`.  The
    value is `Classical.choose` of the limit, with linearity recovered from
    `tendsto_nhds_unique` (`genValue_add`, `genValue_smul`) rather than from the definition.  The
    result is `generator : ℋ →ₗ.[ℝ] ℋ`, characterised by `generator_apply_tendsto` and unique by
    `generator_apply_eq_of_tendsto`.  That it is the generator *of this family* is
    `generator_evol`: `P(t)` preserves the domain and `A P(t) z = P(t) A z`, because the quotient
    of an evolved vector is the evolved quotient (`diffQuot_evol`, using `P(t)P(τ) = P(τ)P(t)`).
    Given `∀ τ, IsSelfAdjoint (P τ)`, the generator is **symmetric** (`generator_isSymmetric`):
    `⟪τ⁻¹•(P(τ)z − z), w⟫ = ⟪z, τ⁻¹•(P(τ)w − w)⟫` pointwise (`inner_diffQuot_comm`) and the two
    sides pass to the limit, with no integral representation anywhere.  Note the hypothesis: the
    OS axioms give contractivity in both directions, i.e. *unitarity* of `P(τ)`, and a unitary
    need not be symmetric; self-adjointness of the transfer operator is the realization fact
    `P(τ) = e^{−τH}` for the self-adjoint `H` of the ESA/Faris–Lavine route.
  - *Källén–Lehmann on `ℋ` (2026-11-06).*  `OSReconstruction.KallenLehmannModel` attaches §7's
    representation to the physical two-point function instead of leaving it in a model: for an
    isometry `U : ℋ →ₗᵢ[ℝ] L²(ν)` under which `P(τ)` is multiplication by `e^{−τ f}`,
    `kl_physEvol` proves `⟪z, P(τ)z⟫ = laplace (ẑ²dν ∘ f⁻¹) τ` — `L².inner_def` computes the
    matrix element as an integral (`inner_toLp_eq_integral`) and `laplace_map_withDensity` turns it
    into the Laplace transform.  `physEvol_twoPoint_nonneg` reads OS positivity off a Laplace
    transform of a positive measure (`laplace_nonneg`), and the decay/support lemmas of §7 then
    apply to the physical correlator directly.  The multiplication model is the single hypothesis:
    producing it is the spectral theorem for the generator, which §5.2 has only as a symmetric
    `LinearPMap`.
  - *The `L²` multiplier and its generator (2026-11-06).*  `OSReconstruction.L2Multiplier` builds
    the operator the KL model had been postulating.  `mulL2` is bounded multiplication on `L²(ν)` by
    an essentially bounded function — Hölder in the exponent form `(⊤, 2, 2)`, the same
    `ContinuousLinearMap.holderL` construction the wave chapter uses — and `expFlow` is the
    multiplier family `e^{−τf}`, defined for all real `τ` (identity off `τ ≥ 0`) so it can be a
    bridge's `Q`, with `expFlow_zero` and `expFlow_comp` proved from `Real.exp_add` pointwise.  With
    it `kl_physEvol_uniform` gives the KL representation at *every* `τ ≥ 0` from one representative
    and one spectral measure — exactly the `hkl` input of `continuousOn_physEvol_twoPoint` — and
    `osFockBridgeOfMulModel` fills `OsFockBridge` with `Q := expFlow`, so the bridge's flow is
    constructed rather than assumed.  `tendsto_expFlow_slope` identifies the generator of that
    flow: `τ⁻¹(Q(τ)z − z) → −f z` in `L²(ν)` for `f z ∈ L²(ν)`, by dominated convergence on the
    square with the pointwise bound `|(e^{−τc} − 1)/τ| ≤ c` for `c ≥ 0`.  The flow is contractive
    (`expFlow_contractive`, and `‖expFlow τ‖ ≤ 1` from the essential-supremum bound on the
    multiplier), and `tendsto_expFlow_zero` turns the difference quotient into norm strong
    continuity at `0⁺`.  `inner_physEvol_eq_inner_expFlow` and
    `klMeasure_same_for_physEvol_and_expFlow` show that `P` and the flow have the same matrix
    elements, hence one KL measure `klMeasure ν f zh`, and `expFlow_twoPoint_nonneg` reads
    positivity off it.  The measure is finite and supported on `[0, ∞)` (`klMeasure_univ_lt_top`,
    `klMeasure_support`), its mass is `‖z‖²` (`klMeasure_mass_eq_norm_sq`), and `laplace_le_mass` /
    `twoPoint_le_klMass` bound the transform and the two-point function by that mass; with the
    contraction bound this gives `abs_twoPoint_le_norm_sq`, `|⟪z, P(τ)z⟫| ≤ ‖z‖²`, while
    `tendsto_expFlow_at` extends strong continuity to every `τ ≥ 0`; `tendsto_physEvol` carries it
    back to `P` itself through the isometry (for every vector when `f` is essentially bounded), and
    `twoPoint_antitoneOn` makes the two-point function decreasing on `[0, ∞)` from the KL
    representation and `twoPoint_convexOn` makes it convex there; a gap `m` upgrades the mass bound
    to `twoPoint_le_norm_sq_mul_exp`, `⟪z, P(τ)z⟫ ≤ ‖z‖² e^{−mτ}`; `tendsto_physEvol_slope` gives
    the right difference quotient `τ⁻¹(P(τ)y − y) → −M` with `UM = M_f(Uy)`, i.e. the generator is
    `−M_f` in the multiplier model (`hasDerivWithinAt_twoPoint` is its derivative form: `τ ↦ ⟪x,
    P(τ)y⟫` has right derivative `−⟪x, M⟫` at `0`); `klMeasure_absolutelyContinuous` places the KL
    measure under the push-forward `ν.map f`, and `klMeasure_finite` records it as finite and
    supported on `[0, ∞)`. Beyond the mass gap, the support is the essential range of `f` for the
    weight `z² dν`. Unconditional: `support_klMeasure_subset_closure_range` (support inside
    `closure (range f)`), `support_klMeasure_subset_Ici_zero`, and the tail bounds
    `twoPoint_le_norm_sq_mul_exp_of_support` / `_sInf` at or below the support. Dependent on the
    essential-range hypothesis (weight positive on opens meeting `range f`):
    `support_klMeasure_eq_closure_range`, its infimum form `sInf_support_klMeasure_eq` — exponent
    `sInf (closure (range f))` — and `twoPoint_le_norm_sq_mul_exp_range`. That hypothesis is not
    free: `support_klMeasure_eq_closure_range_of_measure` derives it from properties of `ν`
    itself (`z ≠ 0` a.e. and positive `ν`-mass on the preimages of opens meeting the range).
    Not claimed *here*: that the transfer
    semigroup `P` *is* this flow.  That is the theorem for the generator, and it is now proved at the
    generator level — `generatorRight` is the transported generator of the flow — in
    `OSReconstruction.MultiplierGenerator` (2026-11-07, the bullet below); the *flow* itself remains
    the hypothesis of this section.
  - *Time continuity of the KL transform (2026-11-06).*  `Clustering.continuousOn_laplace` proves
    the Laplace transform of a finite measure supported on `[0, ∞)` is Lipschitz in `τ` with the
    first moment `∫ λ dρ` as constant — `e^{−τλ}` is `1`-Lipschitz in the exponent and `λ` is
    integrable, so no dominated convergence is needed — hence continuous on `[0, ∞)`.
    `KallenLehmannModel.continuousOn_physEvol_twoPoint` carries this to `τ ↦ ⟪z, P(τ)z⟫`:
    continuity in time, in matrix-element form, from the spectral measure alone.  Norm continuity of
    `P` and the identification `generatorRight = −M_f` are *not* claimed from this: they need the
    `L²` difference-quotient limit `((e^{−τf} − 1)/τ) z → −f z` for the transfer semigroup itself,
    which `L2Multiplier.tendsto_expFlow_slope` supplies only for the constructed multiplier flow.
  - *Closedness of the generator (2026-11-06).*  `OSReconstruction.GeneratorClosed` proves the graph
    is closed: if `uₙ → z₀` in `ℋ` and `A uₙ → y`, then `z₀` lies in the domain and `A z₀ = y`
    (`generator_isClosed`), by the integral representation the earlier draft recorded as missing.
    The orbit of a domain vector has derivative `P(t)A z` at `t` (`hasDerivAt_physEvol`, from
    `generator_apply_tendsto` and `P(t)P(s) = P(t + s)`), and the fundamental theorem of calculus
    gives `P(τ)z − z = ∫₀^τ P(s)A z ds` (`physEvol_sub_eq_integral`).  No `ℋ`-valued Bochner
    integral is needed: the identity is compared with the difference quotient of a *fixed* `y`,
    where the two integrands differ by `P(s)(A uₙ − y)` and contractivity bounds the integral of
    that difference by `|τ| ‖A uₙ − y‖`; dividing by `τ` and letting `n → ∞` closes the graph.  The
    companion limit statement is `tendsto_average_physEvol`: the average of a strongly continuous
    curve tends to its value at `0`, again by contractivity (`Metric`-`ε`/`δ`, not dominated
    convergence).  Closedness plus symmetry gives a *closed symmetric* operator; self-adjointness
    is the remaining step.
  - *Strong continuity without the negative-time isometry (2026-11-06).*
    `OSReconstruction.SemigroupContinuity` re-derives `tendsto_physEvolCompletion` from the OS
    axiom alone.  Contractivity at the single time being approached gives the inequality
    `‖P(τ)x − x‖² ≤ 2(⟨x,x⟩ − ⟨P(τ)x,x⟩)` (`norm_physEvol_sub_sq_le`) in place of the isometry
    equality, so the right-hand side tends to `0` by matrix element continuity
    (`tendsto_norm_physEvol_sub_right`, then `tendsto_physEvolCompletion_right` on `ℋ`, both along
    `𝓝[>] 0`).  The abstract form is `tendsto_of_contractive_weak`: a contraction family with
    continuous matrix elements is strongly continuous — no isometry and no group law.  This is the
    continuity half of the transfer semi-group; the rest is the open item below.
  - *Two-sided contractivity forces a trivial evolution (2026-11-06).*
    `OSReconstruction.TransferSelfAdjoint` shows that the hypothesis `∀ τ, IsSelfAdjoint (P τ)` is
    satisfiable only by the trivial evolution.  Contractivity at `τ` and at `−τ` makes `P(τ)` an
    isometry (`norm_physEvolCompletion_eq`); a self-adjoint isometry is an involution
    (`comp_self_eq_one_of_isometry_isSelfAdjoint`); and `τ = τ/2 + τ/2` then gives `P(τ) = 1`
    (`physEvolCompletion_eq_one`).  Consequently every vector is in the domain
    (`genDomain_eq_top_of_selfAdjoint`) and the generator vanishes identically
    (`generator_apply_eq_zero_of_selfAdjoint`).  So `P(τ) = e^{−τH}` *is* a theorem in this
    framework, but with `H = 0`: the hypothesis of `generator_isSymmetric` is not merely hard to
    discharge, it is inconsistent with nontrivial dynamics, and so is the KL multiplication model
    with `f ≠ 0` (`KallenLehmannModel`).  The physical input is wrong at negative Euclidean time:
    the OS transfer matrix is `e^{−τH}` for `τ ≥ 0`, a contraction, while `e^{τH}` is unbounded.
    The repair is to assume contractivity for `τ ≥ 0` only, rebuild `physEvolCompletion` as a
    semi-group, and re-derive strong continuity from matrix element continuity without the `−τ`
    sandwich; self-adjointness then comes from positivity (Friedrichs/Faris–Lavine), not from
    Stone's unitary group.  Two of the three layers are now in place: continuity is
    `SemigroupContinuity` (contraction bound, filter `𝓝[>] 0`) and the generator with its closedness
    is `SemigroupGenerator` (`genDomainRight`, `generatorRight`, `generatorRight_isClosed`, driven by
    the right-derivative fundamental theorem of calculus).  That generator is also dissipative,
    `generatorRight_inner_le_zero` -- `⟪A z, z⟫ ≤ 0`, from contractivity and Cauchy–Schwarz -- which
    is the one-sided statement that survives in place of symmetry; its quantitative form is the a
    priori bound `generatorRight_resolvent_bound`, `λ‖z‖ ≤ ‖λ z − A z‖` for `λ > 0`, which makes
    `λ − A` injective (`generatorRight_resolvent_injective`) -- the estimate half of
    Lumer–Phillips.  The type-level half is now done as well: `OSReconstruction.TransferSemigroupRight`
    states contractivity as `HinvRight` (`0 ≤ τ` only), descends the evolution to `𝔄/𝔑` as
    `physEvolRight`, extends it to `ℋ` as `physEvolCompletionRight` with `0 ≤ τ` as an argument,
    and proves `P(0) = 1`, `P(s + t) = P(s)P(t)` for `s, t ≥ 0`, `‖P(τ)‖ ≤ 1` and strong
    continuity at `0⁺` (`tendsto_physEvolCompletionRightFun`) from the contraction inequality
    alone; `physEvolCompletionRight_eq` shows the forward semigroup is the restriction of the old
    one whenever the two-sided hypothesis holds, so nothing is lost.  The generator itself is now built on that semigroup: `SemigroupGenerator` defines `diffQuot` on
    `physEvolCompletionRightFun` with `HinvRight`, so `generatorRight`, `genDomainRight` and
    `HasGenRight` take no two-sided hypothesis; its closedness proof uses the right derivative at
    `t ≥ 0` and orbit continuity on `[0, ∞)` (`continuousOn_physEvolCompletionRightFun`) instead of
    shifting by a negative time.  What remains two-sided is the group-level layer, renamed
    `Generator.diffQuotGroup` (`HasGen`, `genDomain`, `generator`), together with `physEvol` and
    `physEvolCompletion` of `HilbertSpace`, whose subject is the family `P : ℝ → B(ℋ)` itself.
  - *The generator of `P` is `−M_f`, not only the flow's (2026-11-07).*  The sentence that used to
    stand here — `generatorRight = −M_f` is asserted for the flow only — is now superseded, and the
    proof needs no spectral theorem.  `BookProof/OSReconstruction/MultiplierGenerator.lean` (no
    `sorry`, registered in `BookProof.lean`) observes that a bridge is an *isometry*, so the
    difference quotient passes through it exactly:
    `U (τ⁻¹ • (P(τ)z − z)) = τ⁻¹ • (Q(τ)(U z) − U z)` for `τ ≥ 0` (`map_diffQuot`).  Everything else
    is that identity read in two directions:

    * `hasGenRight_of_bridge` — a limit of the `Q`-side quotient pushes forward through the inverse
      unitary, so the forward-time **domain** is the preimage of the flow's generator domain;
      `generatorRight_bridge` — and its **value** is the transported one, `U (generatorRight z) = w`,
      by uniqueness of limits in the target space.  Both are stated for an arbitrary
      `OsFockBridge`, so this is not a multiplier-model accident: a bridge identifies generators,
      not only two-point functions.
    * `exists_generatorRight_mulModel` — the multiplier instance.  With the multiplier law
      `U (P(τ)x) = expFlow τ (U x)` and `f·zy ∈ L²(ν)`, the vector `y` is in `genDomainRight` and
      `U (generatorRight y) = −M_f(U y)`.  The auxiliary vector `M` that
      `tendsto_physEvol_slope` had to be *given* is now produced from the bridge's surjectivity
      (`OsFockBridge.surjective`), which is why that theorem's `hM` hypothesis disappears here.
    * `inner_generatorRight_mulModel` — the quantitative form: on that domain
      `⟪A y, y⟫ = −∫ f |zy|²`, so **dissipativity is exactly `f ≥ 0` a.e.**
      (`inner_generatorRight_mulModel_nonpos`), recovering `generatorRight_inner_le_zero` with its
      value.  The sign convention is now a theorem rather than a convention: `H = M_f ≥ 0` is the
      Hamiltonian and `A = −H` the Euclidean generator, which is *why* the one-sided contractivity
      hypothesis `HinvRight` is the correct one and the two-sided family of `TransferSelfAdjoint`
      cannot be nontrivial.

    * `exists_resolvent_mulModel` / `range_sub_generatorRight_mulModel` — the Lumer–Phillips
      **range condition** `ran(λ − A) = ℋ` for `λ > 0`, the half `SemigroupGenerator` recorded as
      missing.  It is not postulated: the solution is written down.  With
      `g = (λ + f)⁻¹` — bounded by `1/λ` *because* `f ≥ 0` (`inv_anti₀`) — and
      `y = U⁻¹ (g · U x)`, the three things to check are that `g·U x` is in the multiplier domain
      (`f g ≤ 1`, a bilinear `MemLp` with exponents `(⊤,2,2)`), that its preimage is in the
      forward-time domain (the bullet above), and that `(λ + f) g = 1` a.e.  The quadratic-form
      identity gives `λ y − A y = x` directly.
    * `norm_resolvent_mulModel` — and the estimate on the explicit solution, `λ‖y‖ ≤ ‖x‖`, i.e.
      `generatorRight_resolvent_bound` read on it.  So both Lumer–Phillips hypotheses are theorems
      in the multiplier model, and the generator's resolvent is `(λ + f)⁻¹` as an operator
      identity rather than a formal analogy.

    **Boundary.**  The multiplier law is still the hypothesis, and it is the spectral theorem for
    `P`: the module identifies the generator and its resolvent *given* the flow, it does not build
    the flow from the OS axioms.  Also open at the time of writing was the existence of an
    unbounded self-adjoint `H` with `A = −H`; that half is now closed in `MultiplierSelfAdjoint`
    (see the 2026-11-08 bullet), which builds `H` from `(λ + f)⁻¹` and proves `H† = H`, `H ≥ 0`.
    What this module proves on its own is that `λ − A` is onto with a bounded inverse of norm at
    most `1/λ` — the range condition — which is the statement `SemigroupGenerator` needed.
    `../physlib`'s multiplication-operator module was checked first and does not transfer: its
    `mulOperator`/`mulOperator_isSelfAdjoint_ofReal` live on the complex `SpaceDHilbertSpace d μ`
    over `Space d` with no exp flow, so the reusable input was instead the in-repo
    `tendsto_physEvol_slope` of `L2Multiplier`.
  - *The multiplier resolvent is the resolvent of a self-adjoint `H ≥ 0` (2026-11-08).*
    `BookProof/OSReconstruction/MultiplierSelfAdjoint.lean` (no `sorry`, registered in
    `BookProof.lean`) closes the operator-level half of the previous bullet's boundary, by the
    classical shift-invert route in `ℝ`.  `resolventMulModel` is the bounded `R = (λ + f)⁻¹` read
    through the bridge — multiplication by `resolventFun`, with `‖R‖ ≤ 1/λ` from
    `‖(λ + f)⁻¹‖ ≤ 1/λ` in the essential supremum — and `resolventMulModel_law`,
    `λ·U(R x) + f·U(R x) = U x` in `L²(ν)`, is what makes it an inverse.  Symmetry of `R` is the
    real-multiplier calculation `resolventMulModel_inner_comm`; injectivity and dense range follow
    from the same law.

    The Hamiltonian is then `hamiltonianMulModel = R⁻¹ − λ` on `ran R`:
    `hamiltonianMulModel_apply` reads `H (R x) = x − λ R x`, and `hamiltonianMulModel_image` gives
    `U (H (R x)) = mulImage D λ x` — the vector `exists_generatorRight_mulModel` names as
    `−U (generatorRight (R x))`.  So `H` is symmetric (`hamiltonianMulModel_isFormalAdjoint`) with
    dense domain (the range of `R`), i.e. `H ≤ H†`.  The reverse inclusion is the von Neumann
    argument, isolated once for an abstract real Hilbert space:
    `le_adjoint_of_shift_surjective` — a symmetric `T` with `ran(λ + T) = ℋ`, `λ > 0`, satisfies
    `T† ≤ T`, because `z` solving `λ z + T z = T† v + λ v` makes `v − z` orthogonal to
    `ran(λ + T)`.  Instantiated at `hamiltonianMulModel_resolvent` (`λ + H` is onto by
    construction) it gives `hamiltonianMulModel_isSelfAdjoint`, `H† = H`.  The lemma is kept
    generic on purpose: the same argument written against `ℋ` unfolds the
    `UniformSpace.Completion` in every tactic step and hits the heartbeat limit at a million,
    while at the abstract level it is immediate.  Positivity is quantitative:
    `hamiltonianMulModel_inner_nonneg`, `⟪H y, y⟫ = ∫ f (U y)² ≥ 0`, so `H ≥ 0`.  Finally
    `hamiltonianMulModel_resolvent` and `resolvent_hamiltonianMulModel` say `R` is *the* resolvent
    of `H` at `λ` in both directions, so the explicit family `(λ + f)⁻¹` is a genuine resolvent,
    not a formal analogue.

    `generatorRight_eq_neg_hamiltonianMulModel` then puts the two halves together: on `dom H` the
    forward generator exists and `U (generatorRight y) = −U (H y)`, both sides being
    `mulImage D λ a`.  The two modules carried `f · U y` with different membership proofs; the
    theorem exists because those presentations differ only by associativity, so they are a.e. equal
    and `MemLp.toLp_congr` identifies them.

    The flow itself is now *defined* rather than postulated: `flowOfH D τ x = U⁻¹ (e^{−τf} · U x)`,
    with `U_flowOfH`, `flowOfH_zero`, the semigroup law `flowOfH_add`, contractivity
    `flowOfH_contractive`, and `physEvol_eq_flowOfH` — which is exactly the multiplier law read
    back, so the physical semigroup is this flow precisely when `MulModel.hlaw` holds.  The natural
    definition would be the functional calculus of the *bounded* resolvent (`R` is bounded,
    self-adjoint, `‖R‖ ≤ λ⁻¹`, so `e^{−τH} = φ_τ(R)` with `φ_τ r = exp(−τ(1/r − λ))` bounded and
    continuous), but Mathlib has no continuous functional calculus on a real Hilbert space; the
    conjugation above gives the same family and the laws above verify it.

    The flow is now an operator family, not just a family of vectors: `flowOfHCLM D τ : ℋ →L[ℝ] ℋ`,
    with `flowOfHCLM_apply` and `norm_flowOfHCLM_le_one`.  Strong continuity needs no
    generator-domain hypothesis — for *every* `x`, `τ ↦ e^{−τH} x` is continuous at every `τ ≥ 0`
    (`continuousOn_flowOfHCLM`), because `‖e^{−τf}u − u‖ → 0` is dominated convergence with the
    bound `4 (u x)²` (`tendsto_expFlow_nhdsGE_zero`; the older `tendsto_expFlow_zero` needed
    `f·u ∈ L²`, which generic semigroup theory must not assume).  Symmetry is the reality of the
    multiplier: `inner_mulL2_comm` gives `⟪W u, v⟫ = ⟪u, W v⟫` for real `W`, and the bridge is an
    isometry, so `IsSelfAdjoint (flowOfHCLM D τ)` for `τ ≥ 0` (`isSelfAdjoint_flowOfHCLM`) and the
    bundle `flowOfHCLM_isContractionSelfAdjointSemigroup` records identity, semigroup law, norm
    bound and self-adjointness together.  Finally the generator statement now reads from the flow
    side: `tendsto_flowOfH_slope` proves `τ⁻¹ • (e^{−τH}(R a) − R a) → −H (R a)` directly from the
    model's `tendsto_expFlow_slope` carried through the bridge, without passing through
    `physEvolCompletionRightFun` or `HasGenRight`.

    That last point is where the two routes part.  `dom H = ran R` is where the multiplier chart can
    compute the slope itself; the *forward* domain of the transfer generator is larger, and there
    `f · u` need not be square-integrable, so the model slope need not converge.  The flow still
    generates the same operator there: `tendsto_flowOfH_slope_of_hasGenRight` shows the flow's
    quotient converges on every `z` with `HasGenRight D.hinv z`, with limit
    `generatorRight D.hinv z`, and `hasGenRight_iff_tendsto_flowOfH_slope` gives the converse, so
    the flow's forward domain *equals* the transfer generator's — the flow generates nothing
    larger.  `tendsto_flowOfH_slope_of_mem_domainH` then recovers the `dom H` value `−H` from that
    general statement via `generatorRight_eq_neg_hamiltonianMulModel` and injectivity of `U`.
    The single ingredient this route borrows is the multiplier law (`physEvol_eq_flowOfH`); the
    `dom H` route does not borrow it.

    Positivity is the semigroup face of `f ≥ 0`.  On the chart the flow is multiplication by
    `e^{−τf} ≥ 0`, so it preserves the a.e. nonnegative cone (`expFlow_nonneg`, `flowOfH_nonneg`),
    and since `τ ≥ 0` and `f ≥ 0` force `e^{−τf} ≤ 1` it also pulls a nonnegative vector down
    (`expFlow_apply_le_of_nonneg`, `flowOfH_apply_le_of_nonneg`).  Together with
    `hamiltonianMulModel_inner_nonneg` (`H ≥ 0`) this is the order theory of the model; the corpus
    has no order on `ℋ` other than the chart cone, which is why the statement is phrased through
    `U`.

    The forward domain is now *densely defined and closed*, the two structural properties of a
    generator.  Density is `dense_flowForwardDomain`: the domain contains `dom H = ran R`, which is
    dense because `R` has dense range (`dense_range_resolventMulModel`), and `dom H` lies inside it
    by `tendsto_flowOfH_slope`.  Closedness is `closed_flowForwardDomain`: if `uₙ` in the forward
    domain converge and the generator's values `A uₙ` converge, the limit is again in the domain
    with value the limit, and — read flow-side — the flow's quotient at the limit point converges
    to that value.  It is inherited from `generatorRight_isClosed` and keeps that theorem's
    matrix-element continuity hypothesis `hcont` (`∀ F, Continuous (τ ↦ ⟪T τ F, F⟫)`):
    `LinearFunctional` has no continuity field, so `hcont` is an OS input that cannot be read off
    the model.  The flow's *strong* continuity does not replace it, because the graph argument
    integrates the transfer representation `physEvol_sub_eq_integral_right`, which assumes `hcont`.
    `flowGenerator_dense_domain_closed` bundles the two.

    Large time is answered pointwise, which is what the chart can give.  `e^{−τf}` is *strictly*
    positive, so the flow is **not** positivity improving: `expFlow_support` proves the support is
    preserved exactly — `e^{−τH}u` vanishes precisely where `u` did, so mass never spreads into a
    set the initial vector missed.  Strict positivity is preserved (`expFlow_pos_of_pos`,
    `flowOfH_pos`), and where `f x > 0` the chart decreases strictly (`expFlow_apply_lt_of_pos`) and
    decays to zero, `e^{−τ f x} u x → 0` (`tendsto_expFlow_mul_atTop`, a.e. under `0 < f` in
    `tendsto_expFlow_apply_atTop`), while `expFlow_apply_of_f_eq_zero` freezes the part over
    `{f = 0}`.  So the large-time limit is the projection onto the kernel of the density: ergodic on
    `{f > 0}`, trivial on `{f = 0}`.

    The pointwise law upgrades to a norm statement by dominated convergence, and the domination is
    the same estimate as contractivity: `e^{−τf x} ≤ 1` for `τ ≥ 0`, so
    `(e^{−τf x} u x)² ≤ (u x)²`, and `(u x)²` is integrable because `u ∈ L²`.  That gives
    `‖e^{−τH}u‖² = ∫ (e^{−τf}u)² → 0` (`tendsto_norm_sq_expFlow_atTop`), hence
    `‖e^{−τH}u‖ → 0` by `√` of the squared norm (`tendsto_norm_expFlow_atTop`), and on `ℋ` the same
    through the isometry bridge (`tendsto_norm_flowOfH_atTop`).  The one extra hypothesis is
    `0 < f` a.e., and it is not a technical convenience: where `f = 0` the flow freezes
    (`expFlow_apply_of_f_eq_zero`), so a density vanishing on a set of positive measure leaves a
    nonzero part in the limit and the norm cannot tend to `0`.

    That caveat points at the sharper statement, which needs no hypothesis on the density at all:
    the flow's limit is the *projection* rather than `0`.  Pointwise, `e^{−τ f x} → 1` where
    `f x = 0` and `→ 0` where `f x > 0`, so the multiplier converges to the indicator of
    `{f = 0}`, and that indicator is bounded by one, so dominated convergence applies to the
    differences too — with the same bound `(u x)²`, since `|e^{−τ f x} − 1_{f = 0}| ≤ 1`
    (`abs_exp_neg_sub_kernelIndicator_le_one`).  Thus `‖expFlow τ u − limitMulL2 D u‖ → 0`
    (`tendsto_norm_expFlow_sub_limitMulL2_atTop`), where `limitMulL2` is multiplication by the
    indicator class (`kernelIndicator`).  On `ℋ` the same gives
    `tendsto_flowOfHCLM_atTop : flowOfHCLM D τ y → limitProjection D y`, and `limitProjection` is
    an **orthogonal projection**: idempotent (`limitProjection_idem`, from the indicator's `w² = w`)
    and self-adjoint (`isSelfAdjoint_limitProjection`, the same symmetry argument as the flow, via
    `inner_mulL2_comm`), bundled in `limitProjection_isOrthogonalProjection`.  So the large-time
    limit *is* the projection onto the kernel of the density, and the `‖·‖ → 0` statement is its
    special case where that kernel is negligible.

    Self-adjoint plus idempotent does not by itself say *which* subspace is projected onto, so the
    next step identifies it on the chart.  `limitProjection_eq_iff` says `limitProjection D y = y`
    exactly when `U y` vanishes where `f ≠ 0` — the vectors living on the kernel of the density —
    and `limitProjection_eq_zero_iff` says `limitProjection D y = 0` exactly when `U y` vanishes
    where `f = 0`, so the kernel is the complementary part of `ℋ`.  The residual is orthogonal to
    the range (`inner_sub_limitProjection_limitProjection`: on the chart the residual carries
    `1_{f ≠ 0}` and the projection `1_{f = 0}`, so the pointwise product is zero), hence range and
    kernel are orthogonal (`inner_limitProjection_ker`), and the range is characterised as a set in
    `range_limitProjection` with the kernel in `mem_ker_limitProjection`; the residual is itself a
    kernel vector (`residual_mem_ker_limitProjection`), so every vector splits as
    `limitProjection D y` plus a kernel vector — an orthogonal direct sum.
    `limitProjection_isOrthogonalProjectionOntoDensity` bundles the whole operator statement: the
    flow converges strongly to the orthogonal projection onto the part of `ℋ` supported where the
    Hamiltonian density vanishes.

    That subspace is literally `ker H`.  `H` is multiplication by `f` on the chart,
    `U (H (R a)) = f · U (R a)` (`hamiltonianMulModel_image`), so `mulImage_eq_zero_iff` turns
    `H (R a) = 0` into the a.e. condition that `U (R a)` vanish where `f ≠ 0`
    (`hamiltonianMulModel_eq_zero_iff`), which by `limitProjection_eq_iff` is exactly the fixed
    space of the limit (`hamiltonianMulModel_eq_zero_iff_limitProjection`).  So the flow's
    asymptotic state is the `ker H` component, and the `‖·‖ → 0` statement is the case `ker H = 0`.

    Operator-norm convergence is a different matter and needed a correction: it holds with rate
    `e^{−τδ}` when the density has a gap `δ > 0` above zero
    (`norm_flowOfHCLM_sub_limitProjection`, `tendsto_opNorm_flowOfHCLM_sub_limitProjection_atTop`),
    but it is **false** without a gap.  The norm of multiplication by `g_τ = e^{−τf} − 1_{f = 0}` is
    the essential supremum of `|g_τ|`, and a density with values arbitrarily close to zero —
    Lebesgue measure on `(0, 1)` with `f x = x`, for instance — keeps `|g_τ|` at `1` on sets of
    positive measure for every `τ`, so `‖e^{−τH} − P‖ = 1` for all `τ` while `e^{−τH} → P` still
    holds strongly.  The section header records this, so the corpus does not claim an
    unconditional operator-norm limit it cannot have.

    Three follow-ups turn that caveat into theorems about the same operator.  (i) The
    `ker H` identification is now an equality of **submodules**, not a pointwise statement on the
    domain: `kerHamiltonianMulModel` carries the domain in its carrier, and
    `kerHamiltonianMulModel_eq_range_limitProjection` proves `ker H = range P` in
    `Submodule ℝ ℋ`.  The pointwise form alone cannot give this, because `dom H = ran R` is dense
    but proper; the missing half is `range_limitProjection_subset_domain` — a chart living on
    `{f = 0}` satisfies `(λ + f)·U y = λ·U y`, and `λ • U y` is again a chart because the range of
    an isometry is a subspace — so the range of `P` sits inside the domain after all.  The witness
    is explicit (`exists_resolventMulModel_eq_of_limitProjection` records both `R a = y` and
    `U a = λ • U y`), and `resolventFun_mul_smul_of_eq_zero` / `eq_zero_of_eq_mul_resolventFun`
    are the two halves of the scalar arithmetic `(λ + f)⁻¹(λ v) = v` that make it work in both
    directions.

    (ii) The counterexample is now a theorem rather than prose.
    `not_tendsto_opNorm_flowOfHCLM_of_noGap` takes the negation of a gap — every `δ > 0` has a set
    of positive finite measure carrying `0 < f < δ` — and proves that
    `‖flowOfHCLM D τ − limitProjection D‖` does not tend to `0`.  The estimate is
    `norm_expFlow_sub_limitMulL2_ge`: the indicator of that set is a nonzero `L²` class and the
    multiplier is at least `e^{−τδ}` on it, so the model-side norm is at least `e^{−τδ}`; with
    `δ = log 2/(2τ)` the bound is `1/2` at every `τ ≥ 1`.  It transfers to `ℋ` only because the two
    operator norms are equal, `norm_flowOfHCLM_sub_limitProjection_eq`, which needs the density of
    `ran U` (`‖S‖ ≤ ‖T‖` is immediate from the isometry; density upgrades it to equality).  So the
    gap in the rate theorem is a hypothesis on the truth, not on the proof.

    (iii) Strong convergence is quantified.  The two-scale bound splits at `δ > 0`: where `f ≥ δ`
    the multiplier is at most `e^{−τδ}`, where `0 < f < δ` it is at most one, and where `f = 0` it
    vanishes, so `‖e^{−τH}y − P y‖ ≤ e^{−τδ}‖y‖ + ‖1_{0<f<δ}·U y‖`
    (`norm_flowOfHCLM_sub_limitProjection_le_two_scale`, via the pointwise
    `abs_exp_neg_sub_kernelIndicator_le_two_scale` and `Lp.norm_le_norm_of_ae_le`).  The tail
    `tailMul D δ u` is a genuine `L²` class that does not depend on `τ`, and it vanishes as
    `δ ↓ 0` (`tendsto_norm_tailMul`, dominated convergence with `{0 < f < δ} ↓ ∅`, and
    `exists_tailMul_norm_lt` picks the split).  Choosing the split first and then the time gives
    the explicit bound `norm_flowOfHCLM_sub_limitProjection_lt_of_time`: from
    `max 0 (-log (ε / (2(‖y‖+1))) / δ)` on, the flow is within `ε` of the projection, so
    `exists_time_norm_flowOfHCLM_sub_limitProjection_lt` is the quantified form of the asymptotic
    statement.  The rate is explicit in `δ, ε, ‖y‖`; only `δ` comes from a limit, and that is the
    sense in which a rate exists without a gap — pointwise in `y`, never uniformly.

    (iv) Two refinements close the pair.  Sharpness: the two-scale bound is attained, not merely an
    upper estimate.  If the density equals the split on the support of the vector,
    `tailMul_eq_zero_of_eq_on_support` empties the tail and the multiplier is exactly `e^{−τδ}`
    there, so `norm_expFlow_sub_limitMulL2_eq_of_eq_on_support`, and its flow-side form
    `norm_flowOfHCLM_sub_limitProjection_eq_two_scale`, turn the estimate into an equality.  The
    explicit witness is `barrier_sharp`: the barrier density `δ` on `[0,1]`, zero elsewhere
    (`barrierDensity`), tested on the class of its own indicator (`barrierVector`), gives equality
    for every `τ ≥ 0` — the gapped rate is the truth where it applies.  No uniformity:
    `not_exists_uniform_rate_of_noGap` shows there is no rate function `r` with `r τ → 0` bounding
    `‖(e^{−τH} − P)y‖` for every `‖y‖ ≤ 1`, because a unit-ball bound is a bound on the operator
    norm (`opNorm_le_of_unit_ball_bound`, by homogeneity) and such an `r` would make the norm
    converge.  The rate of (iii) is therefore pointwise in `y` by necessity, not because of the
    shape of the proof.

    (v) The two halves are now a single equivalence: `tendsto_opNorm_flowOfHCLM_sub_limitProjection_iff_gap`
    says `‖e^{−τH} − P‖ → 0` iff `∃ δ > 0, f ≠ 0 → δ ≤ f` a.e.  The gap direction is the existing
    `tendsto_opNorm_flowOfHCLM_sub_limitProjection_atTop`; the converse is the contrapositive of
    `not_tendsto_opNorm_flowOfHCLM_of_noGap`, and the only new ingredient is measure-theoretic: the
    a.e. failure of the gap is turned into the split form's positive *finite*-measure set by
    `Measure.exists_subset_measure_lt_top`, which is where `σ`-finiteness of `ν` enters.  This is
    the general spectral fact in the normal form the spectral theorem supplies (multiplication by
    `f` on `L²(X, ν)`, spectrum = essential range of `f`); what is formal is the normal form, not
    the spectral theorem itself — `ChapterSpectralMultiplication` has the multiplication model only
    for a bounded normal operator with a cyclic vector, and Mathlib has no unbounded spectral
    theorem.  Note the direction of the inference this fixes: norm convergence *is* the gap, so a
    proof of norm convergence for Yang–Mills would be a proof of the mass gap, not a consequence of
    the reconstruction.

    **Boundary.**  The multiplier law `U (P(τ)x) = expFlow τ (U x)` remains the
    hypothesis that supplies the flow.  That law is *not* an OS consequence: the axioms supply only
    a one-parameter contractive semigroup on `ℋ` together with its two-point functions, and the
    law says that `U` diagonalizes its generator with the simple spectrum given by `f`.  Two
    different `f` (or a multiplicity `> 1`) give the same OS axioms with different `H`, so the
    identification is model data — the choice of the KL multiplier realization — and the missing
    ingredient for deriving it is the spectral theorem for the generator (equivalently Stone's
    theorem), not another estimate.  What the corpus does derive *from* the law is the whole
    matrix-element layer (`klMeasure`, `inner_physEvol_eq_inner_expFlow`,
    `expFlow_twoPoint_nonneg`), and the 2026-11-08 bullet derives the operator behind it.
  - *What is still open.*  Two things, plus one identification.  (i) **The Euclidean generator**, not the Hamiltonian.  Closedness is proved in the semi-group
    setting (`generatorRight_isClosed` on `genDomainRight`), as are dissipativity
    (`generatorRight_inner_le_zero`), the a priori estimate `λ‖z‖ ≤ ‖λ z − A z‖`
    (`generatorRight_resolvent_bound`) and injectivity of `λ − A`
    (`generatorRight_resolvent_injective`).    Lumer–Phillips would add the range condition
    `ran(λ − A) = ℋ`, which contractivity alone does not supply, but which is `ran(λ + H) = ℋ`
    and therefore follows once `H ≥ 0` is self-adjoint.  That condition is now a theorem *in the
    multiplier model* without passing through self-adjointness of an unbounded operator —
    `range_sub_generatorRight_mulModel`, with the inverse `(λ + f)⁻¹` and the bound `1/λ`
    (`norm_resolvent_mulModel`); see the bullet above.  That is the Wick-rotated picture:
    `A = −H`, while in real time `H` is self-adjoint by positivity plus essential
    self-adjointness (Faris–Lavine / Friedrichs), with the unitary flow from Stone's theorem --
    in this corpus `qgOuterFock_esa`, `smFockHam_esa`, `exists_stone_flow_of_esa`, on the nested
    Fock space whose sector operators are inner Hamiltonians sandwiched between outer creation
    and annihilation (`sandwich`, `secHam_matrix_element`).  The degeneracy of the previous
    bullet concerns the Euclidean family at *all* real times, not `H`, so deficiency indices are
    not needed for `H`.  An earlier version of this bullet added that the adjoint of an unbounded
    operator was *blocked on Mathlib* on real inner product spaces; that is wrong —
    `LinearPMap.adjoint` is real-valued and is what the 2026-11-08 bullet below uses to prove
    `H† = H`.  What Mathlib does lack is the spectral theorem for an unbounded self-adjoint
    operator (equivalently Stone's theorem for a unitary group), which is the step the multiplier
    law needs.    What is genuinely missing is a unitary `U` from the abstract `ℋ` onto the nested Fock space
    intertwining `P(τ)` with `e^{−τH}` for a self-adjoint `H ≥ 0`.  The condition is now a formal
    hypothesis bundle rather than a slogan: `OsFockBridge`
    (`OSReconstruction.FockIntertwining`) has exactly three fields — an isometry
    `U : ℋ →ₗᵢ[ℝ] F`, dense range, and `U (P τ x) = Q τ (U x)` for `τ ≥ 0` — and the module proves
    what they force: `U` is a unitary (`toIsometryEquiv`), the two-point functions agree
    (`⟪x, P τ y⟫ = ⟪U x, Q τ (U y)⟫`, `inner_intertwines`), and contractivity, isometry, fixed
    points, symmetry and the semigroup law transfer in both directions.  The bundle is inhabited
    (`OsFockBridge.id`), so its content is the map, not the axioms.  On the Fock side the nested
    Fock space itself is the target — no Balaban or lattice-observable input is needed: the corpus
    has `ymFock_weylGauge_timeIndependent`, `qgOuterFock_esa` and `smFockHam_esa`, and the object
    that is missing is a map `U`, not a model.  What remains is to *build* `U` from the OS data
    (`ℋ` is a completion of `𝔄 ⧸ 𝔑`, so `U` is defined on the dense image and extended by
    `LinearMap.extendOfNorm`) and to identify `Q(τ)` with `e^{−τH}` for the Friedrichs extension of
    the Fock Hamiltonian.  Without it the KL representation still attaches to a *closed symmetric*
    generator on `ℋ`.  (ii) The
    **identification of the ladder**: `a < 1` is uniform, and the *matrix-entry* half is now
    proved.  `YangMillsLadderTransport` transports the Hermite creation ladder from the
    `Finsupp` multi-indices of `crePoly_hpsi` to the occupation functions `Idx d = Fin d → ℕ` that
    `magCutoffKernel` is indexed by: `creCoeff` is the ladder's matrix element in that index,
    `crePoly_hpsi_apply` restates the ladder relation in it (the only nonvanishing entry out of
    `α` is at `α + eᵢ`, with weight `√(αᵢ+1)`), `boxEmbed_update` carries the cut-off box through
    the raise, and `magCutoffKernel_eq_ladder` / `boxKernel_eq_ladder` identify every entry of the
    cut-off kernel with `Aᵢ` times that matrix element.    So `boxKernel Λ A` *is* the matrix of the ladder in the Hermite basis, not merely shaped like
    it.  The operator-level half is now proved on the cut-off: `YangMillsLadderOperator` defines
    the creation operator `creOp` and the kernel-sum operator `magCutoffOp` on the truncated Fock
    space `Box d Λ = Fin d → Fin Λ`, and proves the identity of operators
    `magCutoffOp Λ A = ∑ i, Aᵢ • a†ᵢ` (`magCutoffOp_eq_sum_cre`) together with the vanishing of
    the degree-preserving part at every degree, `proj_N ∘ magCutoffOp ∘ proj_N = 0`
    (`occProj_comp_magCutoffOp_comp_occProj`) — the operator form of "purely off-diagonal in the
    occupation grading".  Still open: that this operator is a *restriction* of §24's reduced
    second-quantized magnetic operator to the transverse sector, which needs the box-to-continuum
    limit (`ℓ²(Idx d)`, unbounded) and the BRST quotient.  (iii) The **BRST quotient**: `closure (range Ω) =
    span{∂_i φ}` is now a theorem in the periodic-lattice model of
    `BookProof/BrstLongitudinalExact` (`exactStates_eq_longitudinal`, `range_derivLin`), but the
    3+1 continuum version still needs the field Hilbert space and the closed unbounded charge, so
    the identification of §24's transverse sector with `H/(exact ⊕ harmonic)` is model-level on
    both sides.  No strictly positive mass gap of the physical continuum Hamiltonian is claimed: the rate `2`
    is proved for the diagonal one-particle operator of §22 and for its reduced sector, not for the
    physical continuum theory.

---

### Summary of Tasks and Timeline

**Historical summary only:** use S0–S4 above for the revised execution order and acceptance
criteria. In particular Phase 4's shifted comparison is not by itself a spectral gap.

| Phase | Mathematical Objective | Lean 4 Target Module | Key Tools / References |
| :--- | :--- | :--- | :--- |
| **Phase 1** | Project out longitudinal gauge zero-modes via BRST cohomology | `BookProof.BrstReducedTransfer` | Nilpotent BRST charge $\Omega^2 = 0$ |
| **Phase 2** | Prove Simon channel-taming along Cartan flat directions | `BookProof.YangMillsEffectiveBarrier` | Transverse zero-point energy $\sim g|A|$ |
| **Phase 3** | Construct solvable gapped comparison operator $H_{\text{ref}}$ | `BookProof.ChapterReferenceGap` | `HarmonicOscillator.lean`, $SU(N)$ Hermite basis |
| **Phase 4** | Establish form-domination $q_{H_W} \ge c_1 q_{H_{\text{ref}}} - c_2$ | `BookProof.YangMillsFormDomination` | `ChapterFockFieldPerturbation.lean` |
| **Phase 5** | Inject analytical $\beta_\infty$ into SIRK/Temple certificate | `BookProof.SpectralGapStability` | `ChapterRitzCertificate.lean`, Trotter–Kato |

The open task is to derive a coercive estimate for the concrete inner Hamiltonian, with
the sector and margin required by the selected target. The model barrier calculations
and numerical approximations support that task but do not yet provide its constant.
