# Soft modes in the Mehler / nested-Fock YangâMills formalism

## Revised work package (2026-11-08)

This revision supersedes the roadmap and completion claims of the dated phases below **as a
reading guide for this file**. Those notes remain implementation history. It does not replace
the programme ordering in `CURRENT_WORK_ORDER.md`: the non-abelian one-particle form bound
remains open, and the mass-gap certificate route still has its sector gate (Â§M4.9 before M4.3).
No Lean proof was compiled for this revision. **U** below denotes an existing mathematical
interface/result within its stated model, **C** a missing hypothesis or bridge, **N** an invalid
inference, and **B** a scope boundary. A theorem's binders, not its name, determine its scope.

### Sources and the object to be bounded

Read these sources by heading rather than by mutable line number:

* [book.tex](book.tex): the recursive second-quantization paragraph beginning âSince the
  second-quantization procedure can be applied recursivelyâ; âRelation with the BRST
  formalismâ; âPure SU(3) Yang-Mills theoryâ. These fix the nested construction, the
  auxiliary role of BRST, and the $99=3+24+72$ continuous coordinates with ghost grading.
* [Book/FreeField.lean](Book/FreeField.lean): âWhy the Gaussian Is the Uniform Measure on
  the Infinite Sphere: the Mehler Limitâ; [Book/SolovayTensor.lean](Book/SolovayTensor.lean):
  âOnly the Mehler Measure on the Infinite Partâ. These supply the Gaussian coordinate
  substrate, not a dynamical YangâMills gap.
* [Book/YangMillsQuantization.lean](Book/YangMillsQuantization.lean): âThe Weyl-Gauge
  Quadratic Form and the Friedrichs Routeâ. Read its energy-origin discussion together
  with the $\mu N$ boundary below; a change of one-particle origin changes outer dynamics.
* [HashimotoâNodera](../papers/Hashimoto.md), Definition 2.4, Â§4 and Theorem 4.1:
  bounded resolvents and rational approximation of operator $\phi$-functions.
* [BookProof.lean](BookProof.lean): the live proof-source inventory. The former generated
  `YANG_MILLS_MASS_GAP_LEAN.md` snapshot is absent from this tree; follow the actual imported
  declarations and distinguish abstract implications from concrete instantiations.

Use $\mathcal K$ for the inner field/configuration Hilbert space and $h$ for its
gauge-fixed Hamiltonian. Its implemented bosonic core is the Gaussâpolynomial core in
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

**N â lower bounds cannot be subtracted.** From
$\lambda_0(h)\ge L_0=c_1\mu_0-c_2$ and
$\lambda_1(h)\ge L_1=c_1\mu_1-c_2$, one cannot conclude
$\lambda_1(h)-\lambda_0(h)\ge L_1-L_0$. For example,
$h_{\rm ref}=\operatorname{diag}(0,1)$ and $h=\operatorname{diag}(M,M+\varepsilon)$
with $M\ge1$, $0<\varepsilon<1$ satisfy $h\ge h_{\rm ref}$ but have gap $\varepsilon$.
In `BookProof/YangMillsFormDomination.lean`, `certified_separation` is an algebraic equality
between comparison thresholds and `certified_gap_pos` proves positivity of their difference.
Neither identifies the actual interacting ground level or its orthogonal complement.

Valid alternatives are: an absolute bound $L_0>0$ for target 1; a minâmax lower bound $L_1$
and independent ground **upper** bound $U_0<L_1$ for target 2; or a direct coercive estimate
on the complement of an identified invariant ground space. If using the reference vacuum's
complement, prove that it is the correct invariant sector. A condition `c 0 = 0` alone does
not identify the interacting ground complement.

**N â Gaussian representation is not confinement.** Multiplication by the square root of
a Gaussian density is a unitary representation change. In one coordinate, with
$d\gamma=(2\pi)^{-1/2}e^{-x^2/2}dx$ and $Uf=\gamma^{1/2}f$,
$U\partial U^{-1}=\partial+x/2$. Thus the Gaussian Dirichlet operator
$\partial^*\partial=-\partial^2+x\partial$ transports to
$-\partial^2+x^2/4-1/2$, an oscillator number operator, **not** the free Laplacian.
The Hermite degree form is not automatically the physical $\tfrac12\sum\pi^2$ form.
Prove the conjugation identity for the actual momentum convention before comparing forms.

**N â lift products after inner composition.** On the outer one-particle sector
$d\Gamma(M)d\Gamma(N)=d\Gamma(MN)$, but on general bosonic sectors their difference
has a normally ordered two-particle contribution. Already
$d\Gamma(I)^2=N_{\rm out}^2\ne N_{\rm out}=d\Gamma(I^2)$.
Use $d\Gamma(B^2)$ when lifting an inner magnetic square; do not replace it by
$d\Gamma(B)^2$. A defined inner-composition algebra must be explicitly distinguished
from ordinary outer operator multiplication. The historical sandwich statements below
do not remove this obligation.

**C â a diagonal surrogate needs an intertwiner.** The occupation forms `degreeForm`,
`quarticDegreeForm` and `yangMillsForm T g`, and the identity
`sandwich_diag_magComp`, are useful models. The split of the concrete `magPoly` into
derivative and commutator pieces does not prove that its square is diagonal, or equal to
$:N^2:$. Require a unitary/core map $J$, its domain properties, and either
$q_h(Jc)=q_{\rm model}(c)$ or a proved inequality with explicit error constants.
No equality of those forms follows just from both being called âYangâMillsâ.

### Work package S0 â identify the Mehler realization and its domains (first)

Specify the Gaussian finite-coordinate measures, inner Hilbert space, graded factors,
cylindrical core and the Lebesgue/Gaussian/Hermite unitary maps. Distinguish a Hermite
**basis cutoff** $\Lambda$ in a fixed $99$-coordinate realization from adding field/spatial
degrees of freedom, changing volume $L$, or removing a regulator $a$. Give embeddings
and a form core for each limit actually claimed. Infinite product Gaussian sequences are
not an identity-covariance Gaussian probability on $\ell^2$; use the coordinate measure
space and its $L^2$ space rather than asserting that its samples lie in $\ell^2$.

**Existing U:** `ChapterMehlerUniqueness.mehler_unique_by_finite_marginals` identifies the
coordinate law under its Gaussian-marginal hypothesis. It is not uniqueness of a vacuum,
a Hamiltonian, or its self-adjoint extension. A Mehler/OrnsteinâUhlenbeck reference semigroup
can organize estimates, but its reference gap is not yet a gap of $h$.

**Acceptance:** a diagram of the concrete core embeddings with norm, momentum and magnetic
operator identities; an explicit list of form-domain and self-adjoint-extension inputs.
Proposed deliverable: `BookProof/Qym/ChapterYangMillsMehlerBridge.lean` (new work, not
an existing declaration). Reuse `ChapterHermiteProductCore` and `ChapterYangMillsHermite`.

### Work package S1 â classify soft directions on the actual configuration space

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

### Work package S2 â prove the bound needed by the chosen target

For target 1 seek $q_h\ge m\|\cdot\|^2$ on the entire inner core. For target 2 seek
$q_h-E_0\|\cdot\|^2\ge\Delta\|(I-P_G)\cdot\|^2$, with $G$ identified and reducing.
A reference estimate $q_h\ge c_1q_{\rm ref}-c_2\|\cdot\|^2$ gives
$m=c_1\mu_0-c_2$ for target 1 only if this number is positive. For target 2 one may use
$\Delta\ge c_1\mu_1-c_2-U_0>0$ under the minâmax hypotheses and a certified $U_0$.
Record dependence on coupling, volume, coordinate count and cutoffs; fix the physical
energy origin before interpreting $m$ as an outer mass scale.

Retain the oscillator reference with the consistent normalization
$h_{\rm ref}=\sum_i\omega_i(N_i+1/2)$, gap $\min_i\omega_i$. Its SchrÃ¶dinger realization
is $\tfrac12\sum_i(-\partial_i^2+\omega_i^2x_i^2)$ in units $\hbar=1$.
Do not add a parity penalty or oscillator potential to $h$ to obtain the desired answer.
For off-diagonal terms a bound $|q_K|\le a q_{\rm ref}+b\|\cdot\|^2$, $a<1$, must
apply to the **actual** interaction; the ladder model's sharp constants are not yet that
estimate. Extend core inequalities to closed forms and identify their Friedrichs operators.
ESA and a commutator estimate establish operator control, not a positive gap by themselves.

**Acceptance:** a concrete positive $m$, or $L_1-U_0$, with a theorem connecting it to
the selected operator and sector. This is the analytic gate before claiming Temple separation.

### Work package S3 â use Hashimoto for approximation, with a separate spectral gate

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
Â§4 schedule. Neither a $\phi_k(A)v$ error nor a semigroup approximation error is
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

### Work package S4 â lift and verify without changing the model

Use `ym_fock_gap_of_one_particle_form_gap` and the Friedrichs extension machinery only
after the concrete S2 bound covers all inner states used by that lift. If a physical
reduction is used, prove its compatibility with the outer lift. A zero inner ground space
requires an explicitly changed one-particle space or a different ground-sector theorem;
it cannot be silently removed to obtain the outer-vacuum statement.

For the certificate campaign, retain the current Â§M4.9 sector gate and label existing
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
  Hermite basis, with `TáµH_n = náµH_n` and the `LÂ²(Î³ dx)` norm bound; C, an operator on
  `Lp â 2 gaussMeasure` whose *domain* is that core (`gaussOp`'s domain is the `CÂ²` core).
* `Toolbox/ChapterNelsonAnalyticVectors.lean`, `essentiallySelfAdjointOn_of_dense_geometric`: U,
  Nelson's criterion for a dense set of vectors with a common geometric ratio, on the FarisâLavine
  deficiency propagation; N, Nelson's theorem with per-vector radii.  The eigenbasis criteria
  `essentiallySelfAdjointOn_of_dense_span_eigenvectors` (dense *span*, the usable one) and
  `â¦_of_dense_eigenvectors` (dense set) need neither summability nor symmetry.  For per-vector data
  the module proves Nussbaum's reduction instead,
  `essentiallySelfAdjointOn_of_dense_vectorsOfUniqueness` (dense set of vectors of uniqueness at
  `Â±i`); U there is Carleman's analytic â¹ vector of uniqueness, which is the missing theorem.
* `Qym/ChapterYangMillsPolyCore.lean`, `polyCore_essentiallySelfAdjoint`: U, the polynomial core of
  `gaussDirichlet` as an operator on classes, essentially self-adjoint by the eigenbasis criterion;
  C, not yet identified with the closure of `gaussOp`/`gaussOpC`.

Execution order is **S0 â S1 â S2 â S3 â S4**; approximation bookkeeping in S3 can proceed
while S2 remains open. The next reviewable deliverable is the S0 representation bridge
and an explicit S2 theorem signature for the selected target, not another abstract
âdomination implies gapâ wrapper. For any later Lean change, build the affected modules
and audit final theorem axioms and binders. For this documentation revision, verify paths,
formula consistency, relative links and doc-index freshness; no book HTML build is needed.

### Status after the S0 bridge (2026-11-08)

`BookProof/Qym/ChapterYangMillsMehlerBridge.lean` now carries the part of S0 that the
âCorrectionsâ section gates on, together with the S2 signature (the next section records the
second-order and multiplication identities and the norm identity added afterwards):

* **U** â `gaussRoot_sq` (`(Î³^{1/2})Â² = Î³`, the isometry input), `hasDerivAt_gaussRoot`,
  `deriv_gaussRoot`, `hasDerivAt_invGauss`, `hasDerivAt_invGauss_mul`, **`conj_deriv`**
  (`U â Uâ»Â¹ = â + x/2`), **`gaussRoot_vacuum`** (`a = â + x/2` kills the weight, so the corpus's
  `momOp = âi â¢ (pderiv â Â½ X Â·)` is the Gaussian convention), `hasDerivAt_deriv_gaussRoot`, and
  **`gaussRoot_oscillator_ground`** (`â(Î³^{1/2})'' + xÂ²/4Â·Î³^{1/2} â Â½Â·Î³^{1/2} = 0`): the Gaussian
  Dirichlet operator is unitarily the oscillator, so the reference gap `Â½` is the oscillator's and
  never a gap of `q_h`.
* **S2 signature** â `HasOneParticleFormGap e fabc m` states target 1 as a named `Prop` on the
  concrete Gaussâpolynomial core. `abelian_no_one_particle_form_gap` shows it is false for
  `fabc = 0`, so it is not a vacuous wrapper, and `no_absolute_gap_of_kernel_vector` records that a
  nonzero kernel vector defeats every positive constant: target 2 does not imply target 1.
* **C, unchanged by this module** â the second-order identity `U (ââÂ² + xâ) Uâ»Â¹ = ââÂ² + xÂ²/4 â Â½`
  on a dense core and its `99`-coordinate product form; the `LÂ²` isometry itself (only its
  pointwise input `gaussRoot_sq` is here); the form core and the self-adjoint-extension inputs. The
  module is one-coordinate analysis plus one abstract linear-algebra statement: it makes no
  spectral claim about `h` and does not by itself move S2.  (The second-order half of that `C` is
  discharged in the next section; the product form is not, and the reason is recorded there.)

Axioms audited: `propext`, `Classical.choice`, `Quot.sound` only. The module builds with no
warnings and no line over 100 characters.

### Status after the S0 identities and the S1 cross term (2026-11-09)

#### S0 â the remaining one-coordinate identities

`BookProof/Qym/ChapterYangMillsMehlerBridge.lean` now also carries, all `sorry`-free and with axioms
`propext`, `Classical.choice`, `Quot.sound`:

* **U â second order.** `conj_dirichlet` is the plan's formula
  `U (ââÂ² + xâ) Uâ»Â¹ = ââÂ² + xÂ²/4 â 1/2` for any `f` with two derivatives (stated through the
  weighted Dirichlet operator `gaussDirichlet f = âf'' + x f'`), and `conj_dirichlet_smooth` is the
  same statement on the smooth core, where the two derivatives are `deriv f` and `deriv (deriv f)`.
  The proof is `conj_deriv` **twice** â the drift `x/2` of the first-order identity supplies the
  `xÂ²/4`, its derivative supplies the `â1/2` â which is a concrete confirmation of the plan's
  correction: the derivation of the oscillator from the Gaussian is a statement about `â` only.
* **U â multiplication.** `conj_mult` (`U (mult V) Uâ»Â¹ = mult V`) and `conj_mult_deriv` (the drift
  multiplies `V` rather than differentiating it).  Together with the second-order identity these
  are exactly the "momentum and magnetic operator identities" of the S0 acceptance list: the
  transform manufactures `xÂ²/4` out of the derivative and moves no potential, so it can neither
  create nor destroy a magnetic gap.
* **U â norm.** `lintegral_norm_sq_conj`: `â« |Î³^{1/2} f|Â² dx = â« |f|Â² d(Î³ dx)` in `â«â»` form, with
  `Î³ dx` realized as `volume.withDensity (fun x => ofReal (gaussRoot x ^ 2))`.

**N â a correction to this file's earlier ledger, not to the plan.** The previous section said the
`99`-coordinate product form "follows by applying the one-coordinate identity coordinatewise".
That is an invalid inference as stated: coordinatewise application covers only functions depending
on a single coordinate.  The `99`-coordinate statement needs the operator to be a *sum* of
one-coordinate operators that survives the conjugation, i.e. either the tensor decomposition
`U_{99} = â¨_i U_i` on `â¨_i LÂ²(Î³)` with `D_{99} = Î£_i D_i` commuting with it, or the Laplacian
Leibniz rule `Î(gF) = gÎF + 2â¨âg, âFâ© + FÎg` together with the `d`-dimensional Gaussian identity
`ÎÎ³^{1/2} = (|x|Â²/4 + d/2)Î³^{1/2}`.  Neither is assembled, so the coordinate-count factor `â99/2`
is **not** proved here, and the product form stays `C`.

The remaining S0 acceptance items are likewise unchanged: the `Lp`-level statement that
multiplication by `Î³^{1/2}` is a `LinearIsometryEquiv` (only the integral identity is proved), the
concrete core-embedding diagram, and the closure/Friedrichs list.  That list, made explicit as the
plan's acceptance asks, is â none of it a consequence of the conjugation identities, all of it a
hypothesis about the *domain*:

1. **Closability.** `âÎ + xÂ·â` densely defined and closable on `C_c^â` inside `LÂ²(Î³ dx)`, with the
   Dirichlet form `â« Î³|âf|Â² dx` as its closed form and `HÂ¹(Î³)` as the form domain.  The smooth
   core must be shown to be a form core, not merely a set on which the identity holds.
2. **Transport to `LÂ²(dx)`.** The unitary at space level (item `C` above), so that the Friedrichs
   operator is the `LÂ²(dx)` operator of `conj_dirichlet` and not only the integral identity.
3. **Product form.** The `99`-coordinate sum needs item 2's product version; the `â99/2` factor and
   the `99`-coordinate domain are part of that statement, not of the one-coordinate analysis.
4. **Corpus pieces that would carry it.** `Toolbox/ChapterFriedrichsExtension` (closed form â
   self-adjoint operator) and `Qym/ChapterYangMillsFriedrichs` (the concrete YangâMills slot);
   `Sirk/ChapterHashimotoShiftInvert.IsShiftInvert` supplies the bounded resolvent and its
   `âRâ â¤ Î³â»Â¹` once the form is closed.

Those are inputs S2 must *assume*, not consequences of the identities; the reference oscillator's
spectrum is not `h`'s.

#### S1 â the cross term of the magnetic split

`BookProof/Qym/ChapterYangMillsSoftDirections.lean` turns the plan's two S1 statements about
`B = B_deriv + g B_comm` into theorems, at the level of two abstract vectors:

* **U.** `norm_add_sq_ge_split`: for `0 < Îµ < 1`,
  `âX + YâÂ² â¥ (1 â Îµ)âXâÂ² â (Îµâ»Â¹ â 1)âYâÂ²`, proved from CauchyâSchwarz and AMâGM (the AMâGM step
  is `Îµ(âXâ â Îµâ»Â¹âYâ)Â² â¥ 0`).  `norm_add_smul_sq_ge_split` is the shape the plan uses,
  `âX + g â¢ YâÂ² â¥ (1 â Îµ)âXâÂ² â (Îµâ»Â¹ â 1)gÂ²âYâÂ²`, and `norm_add_sq_ge_half` is the `Îµ = 1/2` case.
* **N.** `no_norm_add_smul_lower_bound`: `âX + g YâÂ² â¥ gÂ²âYâÂ²` is false already for scalars
  (`X = 1`, `Y = â1`, `g = 2` gives `1 < 4`).  So the plan's "do not assume" is a theorem, and the
  counterexample uses no structure constants â non-abelianity is not the source of the failure.

**What S1 still needs, and what this does not do.** The estimate is a *norm* inequality between two
vectors, so it inherits every `C` of the concrete split: the derivative and commutator parts of
`magPoly` must be identified as vectors in this shape (`Qym/ChapterYangMillsFieldStrengthSplit.lean`
splits the polynomial, it does not say the squares add cross terms this way), the loss
`(Îµâ»Â¹ â 1)gÂ²âB_commâÂ²` must be dominated by the reference form â the `a < 1` input of
`YangMillsFormClosureNonDiagonal` â and no IMS/localization statement is made, so partition
gradients are still unpaid.  The abelian `A_i = â_i Ï` description of a pure gauge is untouched:
the inequality is agnostic between the abelian and non-abelian readings, and the corpus's
`BrstLongitudinal.gaussVec_eq_longitudinal_add_comm` remains the record that the orbit is larger for
`f â  0`.

S2 is unchanged (no positive `m`, no `Lâ â Uâ`); S3 and S4 are untouched.

### Status after the `99`-coordinate product form and the `Lp`-level identity (2026-11-09)

This section supersedes the previous section on three points: the coordinate-count factor `â99/2`
**is** now proved (so the product form is no longer `C`), acceptance item 2 â the `Lp`-level
statement â now has its bundled `LinearIsometryEquiv`, not merely the integral identity, and
acceptance item 1 is most of the way in: the Dirichlet form **and** its operator identity are now in
the corpus, with only closability proper and core density open.

#### S0 â the product form, with `â99/2`

`BookProof/Qym/ChapterYangMillsMehlerProduct.lean` (namespace
`BookProof.YangMillsMehlerProduct`) builds the `d`-coordinate statement without the Laplacian
Leibniz rule â and therefore without needing `ÎÎ³^{1/2} = (|x|Â²/4 + d/2)Î³^{1/2}` as an input.  It
conjugates a *coordinate derivative* twice, exactly as the one-coordinate chapter does:

* `gaussRootVec` / `invGaussVec` are `exp(â|x|Â²/4)` and `exp(|x|Â²/4)` on `Fin d â â`;
  `sum_sq_update` is `Î£â±¼ (update y i t)â±¼Â² = Î£â±¼ yâ±¼Â² â yáµ¢Â² + tÂ²`, and `gaussRootVec_update` /
  `invGaussVec_update` are the resulting factorization of the weight along a coordinate line into a
  one-dimensional Gaussian root times a constant.
* `pd` / `pd2` are the partial derivatives along the line `xáµ¢ â¦ t`, so they are ordinary
  one-variable `deriv`s; `pd_update` and `pd_pd` record that moving the base point does not change
  the line and that `pd2` is `pd` of `pd`.
* `conj_partial` is `U âáµ¢ Uâ»Â¹ = âáµ¢ + xáµ¢/2` in `d` coordinates; `pd2_invGaussVec_mul` is
  `U âáµ¢Â² Uâ»Â¹`; `conj_dirichletVec_coord` is `U (ââáµ¢Â² + xáµ¢âáµ¢) Uâ»Â¹ = ââáµ¢Â² + xáµ¢Â²/4 â Â½`.
* `conj_dirichletVec` sums these: `U (Î£áµ¢ Dáµ¢) Uâ»Â¹ = âÎ + |x|Â²/4 â d/2` with
  `laplaceVec F = Î£áµ¢ âáµ¢Â²F`, and `conj_dirichletVec99` is the `d = 99` instance with its `â99/2`.
  `sum_drift` is the step where the per-coordinate `âÂ½` becomes `âd/2`; the coordinate count enters
  nowhere else.

Hypotheses: one-variable differentiability of `F` along every coordinate line (`h1`) and of `pd F i`
along the same lines (`h2`).  All proofs are `sorry`-free with axioms `propext`,
`Classical.choice`, `Quot.sound`.  The module proves the identity on functions; it is still not a
statement about `LÂ²` domains, form cores or self-adjoint extensions, so acceptance items 1 and 4 of
the list above are untouched, item 3 is discharged, and item 2 is addressed at the level now
noted.

#### S0 â the `Lp` level, now including the bundled equivalence

`BookProof/Qym/ChapterYangMillsMehlerLp.lean` lifts the squared integral identity to `Lp` and
bundles it:

* `gaussMeasure` is `volume.withDensity (ofReal â Î³^{1/2}Â²)`, i.e. `Î³ dx`;
  `enorm_sq_eq_ofReal_sq` converts `âyââ ^ 2` into `ofReal (yÂ²)`.
* `eLpNorm_gaussRoot_mul`: `âÎ³^{1/2}fâ_{LÂ²(dx)} = âfâ_{LÂ²(Î³ dx)}`, with no integrability
  hypothesis (both sides are `â` together); `eLpNorm_gaussRoot_mul_ae` is the a.e.-measurable form.
* `memLp_gaussRoot_mul`: `Î³^{1/2}f â LÂ²(dx)` **iff** `f â LÂ²(Î³ dx)`; `memLp_gaussRoot_mul_lp` and
  `memLp_invGauss_mul_lp` are the two membership maps on `Lp` elements.
* `eLpNorm_invGauss_mul` is the reverse weight identity
  `âÎ³^{-1/2}gâ_{LÂ²(Î³ dx)} = âgâ_{LÂ²(dx)}` (the pointwise step is `Î³^{1/2}Â²Â·(Î³^{-1/2}g)Â² = gÂ²`,
  read through `withDensity`).
* `norm_toLp_mehler` is the norm equality on `Lp` elements, and **`mehlerLpEquiv` is the bundled
  `LinearIsometryEquiv (Lp â 2 gaussMeasure) (Lp â 2 volume)`** â forward map multiplication by
  `Î³^{1/2}`, inverse by `Î³^{-1/2}`.  Axioms: `propext`, `Classical.choice`, `Quot.sound`.

Acceptance item 2 is discharged at the `Lp` level.  What remains true is that mathlib has no
*generic* density-change isometry: its `Lp` isometry API is the `compMeasurePreserving` family, which
needs a measure-preserving map `Î± â Î²` (`Î½ = Î¼.map f`), and a density is not an image measure.
So the equivalence here is bespoke, with every field paid for: `Lp.ext` plus pointwise identities
for `map_add'` and `map_smul'` (this mathlib has no `MemLp.toLp_smul`), `gaussRoot * invGauss = 1`
and `invGauss * gaussRoot = 1` on the nose for the inverse laws, and `Lp.norm_def` plus the
`eLpNorm` identity for `norm_map'`.  It says nothing about domains, forms or spectra â items 1 and 4
of the acceptance list are still open.

#### S0 â the Dirichlet form, started (acceptance item 1)

`BookProof/Qym/ChapterYangMillsGaussForm.lean` (namespace `BookProof.YangMillsGaussForm`) begins
item 1 of the acceptance list at the form level, deliberately below any domain choice:

* `gaussWeight` is the density `Î³^{1/2}Â² = exp(âxÂ²/2)` of `Î³ dx`, with `gaussWeight_pos`, and
  `hasDerivAt_gaussWeight` is `(Î³^{1/2}Â²)' = âx Î³^{1/2}Â²`.  That identity is the reason the drift
  `xÂ·â` sits in `âÎ + xÂ·â` at all: the `x` is the weight's, and the sequence is
  `Î³^{1/2}Â² f' g' = â(Î³^{1/2}Â² f')' g + Î³^{1/2}Â² f'' g`, so the operator that the form represents is
  `gaussDirichlet f = âf'' + x f'` (`ChapterYangMillsMehlerBridge`), while the form is the
  *positively* signed `â« Î³^{1/2}Â² f' g'`.
* `gaussForm f g = â« x, Î³^{1/2}(x)Â² Â· f'(x) Â· g'(x) dx` is the one-coordinate form;
  `gaussForm_comm` is symmetry and `gaussForm_self_nonneg` the nonnegative diagonal.  Both hold for
  *every* pair of functions, because the Bochner integral is total: symmetry is a pointwise `ring`
  identity under `â«`, and the diagonal integrand is the density times a square.  So these are
  statements about the form, not about a form domain â an integrability hypothesis would be needed
  only to say the value is not the `0`-by-convention integral.
* `MemGaussForm` names that integrability domain (`Î³^{1/2}Â² f'Â² â LÂ¹`), and `gaussForm_self_of_mem`
  records the finiteness obligation on it.
* **`gaussForm_eq_integral_gaussDirichlet` is the operator identity**: for `f` of class `CÂ²` with
  compact support and `g` of class `CÂ¹`,
  `gaussForm f g = â« x, Î³^{1/2}(x)Â² Â· (âf''(x) + x f'(x)) Â· g(x) dx`, with `gaussDirichlet` the
  operator of the bridge chapter.  So the form *is* the form of `âÎ + xÂ·â` on the compactly
  supported core, not merely a quadratic functional; the proof is one
  `integral_mul_fderiv_eq_neg_fderiv_mul_of_integrable` (integrability of the three products comes
  from compact support of `f`, so no growth condition on `g`), plus `deriv_mul` and
  `deriv_gaussWeight`.
  The regularity is `CÂ²`/`CÂ¹` rather than `C^â` because the corpus's `ContDiff â â¤` is mathlib's
  *analytic* order `Ï`: an analytic function on `â` with compact support is identically zero, so a
  `ContDiff â â¤` hypothesis with `HasCompactSupport` would make the identity vacuous.  (The same
  observation applies to `Toolbox/ChapterDegEnergyEstimate.integral_dcoord_mul` and
  `Toolbox/ChapterHermiteGraphApprox.integral_conj_dd_mul`, which do use `ContDiff â â¤` with a
  compact-support hypothesis; they are not touched here, and it is recorded as an open audit item.)
* **`integral_gaussDirichlet_mul_comm` is the symmetry of the operator** in `LÂ²(Î³ dx)` on that
  core: `â¨âÎf + xÂ·âf, gâ©_{LÂ²(Î³)} = â¨f, âÎg + xÂ·âgâ©_{LÂ²(Î³)}`.  It is form symmetry read through the
  operator identity in both orders, and it is the hypothesis a closability argument consumes â
  symmetry of the operator, not only of the form.
* **The operator lives on `LÂ²(Î³ dx)` classes, not just on functions.**  A closure argument needs
  three things from the core, and all three are now proved:
  `isOpenPosMeasure_gaussMeasure` (the density is strictly positive, so `gaussMeasure` is positive
  on nonempty opens â `AbsolutelyContinuous.isOpenPosMeasure` applied to
  `absolutelyContinuous_volume_gaussMeasure`); `eq_of_ae_eq_gaussMeasure` (a continuous function
  that is zero `Î³`-a.e. *is* zero, i.e. `Measure.eq_of_ae_eq` plus that open-positivity, so "zero
  a.e." becomes "zero on a dense set"); and `gaussDirichlet_eq_zero_of_ae_eq_zero`, which is the
  well-definedness statement `T` needs â the operator kills a.e.-zero functions, so its value does
  not depend on the representative chosen.  On the image side, `hasCompactSupport_gaussDirichlet`
  (both summands are supported in `supp f' âª supp f''`) and `memLp_gaussDirichlet` put the core
  inside `LÂ²(Î³ dx)`: multiplying by `Î³^{1/2}` swaps the weighted norm for the Lebesgue norm
  (`memLp_gaussRoot_mul`), and `Î³^{1/2}Â·gaussDirichlet f` is continuous with compact support, hence
  square-integrable against `volume`.
* **`gaussOp` is `T` as a `LinearPMap` on `LÂ²(Î³ dx)`.**  `gaussCore` is the core as a submodule of
  `LÂ²(Î³ dx)` (a class is in it when it has a `CÂ²`-compactly-supported representative) and
  `gaussCoreRep` chooses a representative; the value on a class is
  `gaussOpFun f = toLp (T (gaussCoreRep f))`.  The choice is invisible:
  `gaussOpFun_eq_toLp` computes `toLp (T F)` for *any* admissible representative `F`, because
  `gaussDirichlet_congr_ae` upgrades a.e. equality of continuous representatives to equality of
  images.  Linearity at the function level is `gaussDirichlet_add`/`gaussDirichlet_smul`; at the
  `Lp` level addition is `MemLp.toLp_add` (in mathlib, `rfl`), and the one glue lemma mathlib lacks
  is `memLp_toLp_const_smul`.  Then `gaussOpFun_add`/`gaussOpFun_smul` make `gaussOpFun` a linear
  map on the core and `gaussOp` the resulting `LinearPMap` (domain `gaussCore`).
* **`gaussOp` is densely defined**: `dense_gaussCore`, i.e. `dense_gaussOp_domain`.  This is the one
  place where genuine analysis is needed, and none of it is specific to `Î³`:
  `MemLp.exists_hasCompactSupport_eLpNorm_sub_le` gives a continuous compactly supported
  approximation in `LÂ²(dx)`; such a function is uniformly continuous
  (`Continuous.uniformContinuous_of_tendsto_cocompact`), so
  `UniformContinuous.exists_contDiff_dist_le` smooths it in the sup norm; a `ContDiffBump` that is
  `1` on `tsupport g` (and `â¤ 1` everywhere) cuts the smooth approximation back to compact support
  without losing that bound, and `eLpNorm_le_of_forall_notMem` integrates the sup bound to
  `Îµ Â· (volume (tsupport Ï))^{1/2}` â this is
  `exists_contDiff_hasCompactSupport_eLpNorm_sub_lt`.  Then `mehlerMapInv_toLp_mem_gaussCore` says
  the Mehler isometry's inverse sends those classes into the core (their representative is
  `Î³^{-1/2} Ï`, smooth and compactly supported because `Ï` is), and `dense_gaussCore` carries the
  density across `mehlerLpEquiv` by isometry plus `memLp_of_hasCompactSupport`.
* **`gaussOp` is symmetric as a pairing and closable.**  `gaussOp_inner_comm` is
  `âªT f, gâ« = âªf, T gâ«` on the core: `integral_gaussDirichlet_mul_comm` read through `L2.inner_def`
  on `toLp` images, with `integral_gaussMeasure_eq_integral_gaussWeight`
  (`â« Â· d(Î³ dx) = â« Î³ Â· dx`) doing the measure translation.  So
  `gaussOp_isFormalAdjoint : gaussOp.IsFormalAdjoint gaussOp`, hence
  `gaussOp_le_adjoint : gaussOp â¤ gaussOpâ `, and since the adjoint of a densely defined operator is
  closed (`LinearPMap.adjoint_isClosed`), `IsClosable.leIsClosable` gives
  `gaussOp_isClosable : gaussOp.IsClosable`.  Note that this route needs **no** weak-derivative or
  `HÂ¹(Î³)` API â it is exactly why the adjoint is the cheap way in.

The `99`-coordinate form is the sum of these over coordinates (`laplaceVec`/`pd` in
`ChapterYangMillsMehlerProduct`), so the module is not coordinate-count specific.

**Where S0 acceptance item 1 stands.**  Everything the item asks for except self-adjointness of the
closure is now proved: the form is defined, symmetric and nonnegative; the operator identity holds on
the `CÂ²`-compactly-supported core; the operator is packaged as `gaussOp : Lp â 2 gaussMeasure ââ.[â]
Lp â 2 gaussMeasure` with domain `gaussCore`; the domain is dense; the operator is closable, so
`LinearPMap.closure` exists.

The **polynomial form core** is recorded in `Qym/ChapterYangMillsHermiteAnalytic.lean` (diagonal on
the Hermite classes, `âTáµH_nâ = náµâH_nâ` in `LÂ²(Î³ dx)`), and it is a real operator on classes in
`Qym/ChapterYangMillsPolyCore.lean`: `polyDomC` with the componentwise `polyOpC`, whose Hermite
classes are a complete eigenbasis, so `polyCore_essentiallySelfAdjoint` holds â see the Route C status
below.  It is *not* the domain of `gaussOp`, whose core is the compactly supported `CÂ²` one and
contains no polynomial; identifying the two closures is the step that is still open, and nothing above
uses either.

What the closure itself is known to satisfy (`ChapterYangMillsGaussForm`):

* `gaussOp_closure_isClosed` â it is closed (by construction);
* `dense_gaussOp_closure_domain` â its domain contains the dense core;
* `gaussOp_closure_hasCore` â the `CÂ²` core is a **core for the closure**: the closure of the
  restriction `gaussOp.closure.domRestrict gaussCore` is `gaussOp.closure` itself
  (`LinearPMap.closureHasCore` applied to `gaussOp`);
* `gaussOp_closure_le_adjoint` â it is contained in the adjoint, `gaussOp.closure â¤ gaussOpâ `: the
  adjoint is a closed extension and the closure is the smallest one.

**`gaussOp` is bounded below in the form sense** (`gaussOp_inner_self_eq`, `gaussOp_quadForm_nonneg`):
`âªf, gaussOp fâ« = gaussForm (gaussCoreRep f) (gaussCoreRep f) â¥ 0` for every `f` in the core, because
the operator identity at `g = f` plus the measure translation `â« Â· d(Î³ dx) = â« Î³ Â· dx` exhibit the
quadratic form as the Dirichlet form, whose integrand is a density times a square
(`gaussForm_self_nonneg`).  Together with `gaussOp_inner_comm` this is exactly the `SymmetricOn` +
`0 â¤ quadForm` pair that the Friedrichs construction consumes.

### Open problem: essential self-adjointness of `âÎ + xÂ·â` in `LÂ²(Î³ dx)`

**The statement.**  `gaussOp.adjoint â¤ gaussOp.closure` â equivalently, every pair `(h, g)` with
`h â D(gaussOpâ )` and `g = gaussOpâ  h` lies in the closure of the graph of `gaussOp`; equivalently
`HasCore gaussOpâ  gaussCore` (the `CÂ²` core is a core for the **adjoint** as well as for
`gaussOp.closure`); equivalently `gaussOp.closure.IsSelfAdjoint`, i.e.
`gaussOp.closure = gaussOpâ `.  What is *proved* is one half: `gaussOp.closure â¤ gaussOpâ `
(`gaussOp_closure_le_adjoint`).  The missing half is the classical theorem â`âÎ + xÂ·â` is essentially
self-adjoint on `C_c^â` in `LÂ²(Î³ dx)`â.

Nothing in the repo or in mathlib currently reaches it, and each of the three standard routes is
blocked by a specific missing API.  Recording them precisely, since the gap is one theorem and three
plausible proofs:

**Route A â deficiency indices (the classical route; Weidmann, *Linear Operators in Hilbert
Spaces*, Â§3.3).**  Complexify (`LÂ²(Î³) â â`), take `T = âÎ + xÂ·â` with domain `C_c^â`, and show
`ker(Tâ  â z) = 0` for `z = Â±i`.  Concretely, `f â ker(Tâ  â z)` solves, in the weak sense and then
classically (the coefficients are smooth, so distributional solutions are classical),

    âf'' + x f' = z f,     z = Â± i,

and essential self-adjointness is the assertion that the only `LÂ²(Î³ dx)` solution is `0`.  The
standard reduction: substitute `f = Î³^{-1/2} u`, i.e. `u = Î³^{1/2} f = e^{-xÂ²/4} f`; then `u â LÂ²(dx)`
and the equation becomes the Hermite-type equation

    âu'' + (xÂ²/4) u = (1/2 + z) u,

whose solutions for `Im z â  0` behave like `exp(âxÂ²/4)` at `Â±â` â one decaying, one growing, so each
end admits a one-dimensional space of `LÂ²` solutions, and both deficiency indices vanish once one
checks that no solution is square-integrable at *both* ends (equivalently `Im z â  0` forces
`Im(z âfâÂ²) = 0` from the integration-by-parts identity for `âªTâ f, fâ«`).  *What is missing to
formalize:* the analytic theory of second-order ODEs with a complex parameter (existence,
uniqueness, asymptotics of the two fundamental solutions), which mathlib does not have at all â
`Mathlib/Analysis/ODE` is only the basic `IsPicardLindelof`/`IsIntegralCurve` layer.

**Route B â elliptic regularity.**  `h â D(gaussOpâ )` means `â« Î³ h Â· (âÎÏ + xÂ·âÏ) = â« Î³ g Ï` for all
test `Ï â C_c^â`: the weak form of `âÎh + xÂ·âh = g`.  Elliptic regularity gives `h â HÂ²_loc` with the
local estimate `âhâÂ²_{HÂ²(K)} â¤ C_K(âhâÂ² + âgâÂ²)`, and then a cut-off plus mollification shows
`h` is a graph-norm limit of `C_c^â` functions, which is exactly
`gaussOp.adjoint â¤ gaussOp.closure`.  *What is missing to formalize:* weak derivatives, `HÂ¹`/`HÂ²`,
`LÂ²`-mollification and the interior `HÂ²` estimate.  Mathlib has **no** weak-derivative or
distribution API, so the hypothesis â`Tâ h = g` weaklyâ cannot even be stated; this route is furthest
away.

**Route C â analytic vectors (Nelson's theorem, the route the corpus is closest to).**  In `LÂ²(Î³ dx)`
the Hermite polynomials are eigenfunctions of `T`: with `A = U T U^{-1} = ââÂ² + xÂ²/4 â 1/2` under
`U = ` multiplication by `Î³^{1/2}` (the conjugation `U â U^{-1} = â + x/2` is
`ChapterYangMillsMehlerBridge.conj_deriv`), the eigenfunctions `H_n` of `A` with eigenvalue `n`
correspond to the polynomials `H_n` in `LÂ²(Î³ dx)`, and the eigen-relation is exactly the Hermite ODE
`âH_n'' + x H_n' = n H_n` (`ChapterHermiteFunctions.hermiteR_ode`).  Polynomials are dense in
`LÂ²(Î³ dx)` and they are analytic vectors for `T` (`Î£ t^n âT^n pâ/n! < â` since `T^n p` is a
polynomial of degree `n`), so `T` is essentially self-adjoint by Nelson's analytic-vector theorem.
*What was missing to formalize:* (iii) **Nelson's theorem itself** â mathlib has no analytic-vector or
semigroup-generated self-adjointness theory.  This is the route with the least analysis and the most
bookkeeping.  (iii) is now in the corpus, in the common-radius form, and it turned out *not* to close
the route for this operator â the Hermite radii are unbounded â so the closure is by the eigenbasis
criterion instead; see (iiiâ³) below.

*Done* for (i) and (ii) in `BookProof/Qym/ChapterYangMillsHermiteSpectrum.lean` (no `sorry`; axioms
`propext`, `Classical.choice`, `Quot.sound`): `gaussDirichlet_hermiteR` is the eigen-relation as an
identity of functions on the real weighted Dirichlet operator of `ChapterYangMillsMehlerBridge`, and
`dense_span_polyLp` is the density of the polynomial classes `polyLp p` in `Lp â 2 gaussMeasure`.
`integral_moment_eq` + `ae_eq_zero_of_moments_gaussMeasure` are the moment problem for `Î³ dx` in
closed form.  Three traps: (a) the eigenvalue is `n` and the eigenfunction is `hermiteR n` itself,
**not** `H_n(x/â2)` with eigenvalue `2n` â that is the physicists' convention, while `hermiteR` is
the probabilists' `Polynomial.hermite`, so no rescaling belongs in the statement; (b) `rw [gaussMeasure]`
*fails* in any goal that mentions an `Lp â 2 gaussMeasure` element (the coercion's instance
arguments carry the measure), so the measure is moved with
`integral_withDensity_eq_integral_toReal_smul` applied to a zero-defeq `volume.withDensity â¦`;
(c) the moment hypothesis must be moved to `volume` *before*
`HermiteCore.ae_eq_zero_of_moments` applies, and the resulting `Î³^{1/2} w = 0` divides through by the
nowhere-vanishing `gaussRoot`.

**(iii) Nelson's criterion, in the form the corpus can prove.**
`BookProof/Toolbox/ChapterNelsonAnalyticVectors.lean` carries the analytic-vector vocabulary â
`InvariantOn`, the iterates `orbitD`/`orbit`, the geometric bound `IsGeometric`, the analytic
condition `IsAnalytic`, and `isAnalytic_of_isGeometric` (a geometric bound makes the factorial series
`Î£ ráµ/m! âTáµxâ` converge) â plus the two computations the deficiency argument is made of: the orbit
identity `inner_orbit` (`âªTáµx, wâ« = záµâªx, wâ«` at a deficiency vector) and
`inner_eq_zero_of_isGeometric` (`x â w` when the ratio of `x` is below `|z|`).  On top of the
FarisâLavine lemmas already in the corpus (`dense_range_of_deficiencyTrivialAt`,
`deficiencyTrivialAt_of_dense_range`), which carry triviality from `Â±d i`, `d > r`, to `Â±i`, this
gives `essentiallySelfAdjointOn_of_dense_geometric`: Nelson's criterion for a dense set of vectors
with a **common** geometric ratio `r`.  It is deliberately *not* called Nelson's theorem â the
classical statement allows a different radius for each vector, and getting from per-vector radii to a
single one is the constancy of the deficiency index on each half plane, which the corpus does not
have.  Axioms: `propext`, `Classical.choice`, `Quot.sound`.

**(iii\') The quantitative input, and the polynomial form core.**
`BookProof/Qym/ChapterYangMillsHermiteAnalytic.lean` puts `T = ââÂ² + xâ` on polynomials,
`dirichletPoly p = âp'' + XÂ·p'`; `dirichletPoly_eval` shows it agrees with `gaussDirichlet` on the
representative (so the polynomial classes are a core it maps into itself), and
`dirichletPoly_hermiteR` makes it diagonal there, `dirichletPoly (H_n) = n â¢ H_n`.  Because the
operator is diagonal, nothing grows but the eigenvalue: `dirichletPoly_iterate_hermiteR` is
`Táµ(H_n) = náµ H_n`, `norm_polyLp_iterate_hermiteR` is the bound `âTáµ(H_n)â_{LÂ²(Î³)} = náµ âH_nâ`, and
`hermiteR_summable` is the convergence of `Î£ ráµ/m! âTáµ(H_n)â` for every `r > 0` â the analytic
vector condition, at radius `n`.  The trap: the radius is `n`, so the Hermite classes have **no
common radius**, and the polynomial core meets Nelson's hypothesis but not the common-radius
sufficiency above.  So Nelson's theorem, in the only form the corpus can prove, does **not** close
Route C for this operator; the eigenbasis route below does.

**(iiiâ³) Route C closed: the polynomial core is essentially self-adjoint.**
`BookProof/Qym/ChapterYangMillsPolyCore.lean` (no `sorry`; axioms `propext`, `Classical.choice`,
`Quot.sound`) supplies what the two modules above still lacked â an operator *on classes* whose domain
is the polynomial core, and the spectral criterion that does not care about radii.  Its inputs are
`polyLp_injective` (a polynomial class that vanishes is a.e. zero by `MemLp.toLp_eq_toLp_iff`, then
everywhere by continuity and `IsOpenPosMeasure gaussMeasure` via `IsOpen.eq_empty_of_measure_zero`,
then by `Polynomial.funext`) and `mem_span_hermiteR` (the Hermite polynomials span `Polynomial â`
because `hermiteR n` is monic of degree `n`), which with `dense_span_polyLp` gives
`dense_hermiteSpan`.  Construction: `polyRange`/`polyEquiv` (the class map as an isomorphism onto its
range), `polyOpRange` (`p â¦ âp'' + X p'` carried across it â well defined precisely because the class
map is injective), `polyOpRange_hermiteR` (`= n â¢ H_n`), then the complexified core `polyDomC`, the
pairs whose two real components lie in the Hermite span, with the componentwise operator `polyOpC`.
`polyDomC` is dense (`dense_polyDomC`, through `Cx.norm_sq`), the embedded Hermite classes are
eigenvectors with the real eigenvalues `n` (`polyOpC_eigen`), and their â-span is the whole domain
(`span_eigenClasses_eq_top`, via `z = â¨z.re, 0â© + iâ¨z.im, 0â©`).  Hence
`polyCore_essentiallySelfAdjoint`.

The criterion itself needed one correction to be usable, and this is the trap of Route C: a *dense set
of eigenvectors* is not what a simple spectrum supplies â the union of the eigenlines `â â¢ v_n` is
nowhere near dense â so `ChapterNelsonAnalyticVectors` also carries
`essentiallySelfAdjointOn_of_dense_span_eigenvectors`, stated for the **span** of the eigenvectors,
where `âªx, wâ« = 0` propagates by conjugate-linearity and dense sets are what a complete eigenbasis
actually gives.  It needs no symmetry and no summability.  What remains for Route C is now a
comparison of two operators rather than a missing theorem: identify `polyOpC` with the closure of the
â partial operator `gaussOpC` of `ChapterYangMillsGaussFormComplex`, whose domain is the compactly
supported `CÂ²` core and hence disjoint from the polynomial core.

**(iiiâ´) The per-vector case, and why the deficiency estimate cannot reach it.**
`ChapterNelsonAnalyticVectors` also carries Nussbaum's reduction:
`IsVectorOfUniqueness T z x` (the vector lies in the closure of the range of `T â z`),
`inner_eq_zero_of_isVectorOfUniqueness` (such a vector annihilates the deficiency space at `zÌ`),
`deficiencyTrivialAt_of_dense_vectorsOfUniqueness` (Nussbaum's lemma) and
`essentiallySelfAdjointOn_of_dense_vectorsOfUniqueness` â a dense set of vectors, each of which is
one at both `Â±i`, already forces essential self-adjointness, with **no radius and no summability**
anywhere in the hypothesis.  That is the shape Nelson's theorem takes for per-vector data, and the
reason it is not the geometric theorem with `r_x` in place of `r` is arithmetic: the only decay in
`|âªx, wâ«| â¤ âTâ¿xâ/|z|â¿` comes from a *geometric* bound, while an analytic vector satisfies the
factorial bound `âTâ¿xâ â¤ C n!/Ïâ¿`, for which `C n!/|z|â¿` grows at every fixed `z`.  Deficiency-index
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
eigenvalues `|Î±| + d/2` (`harmCore_hermiteMvLp`), the core is dense (`polyGaussCore_dense`), and
the polynomial-side identity is `kinPoly_add_harmPoly_hermiteMv`.  This is the S0 operator in the
**Mehler-conjugated** gauge on `LÂ²(â^d)`: `harmCore = âÎ + âxâÂ²/4 = U (Î£áµ¢ Dáµ¢) Uâ»Â¹`, coordinate by
coordinate from `conj_dirichletVec` in `ChapterYangMillsMehlerProduct`, and
`polyCore_essentiallySelfAdjoint` above is its `d = 1` unconjugated twin.  So the lift is not
missing analysis or a criterion.  What a *literal* `99`-coordinate statement in the unconjugated
gauge would still need is bookkeeping mathlib does not package: the `d`-dimensional Mehler isometry
`LÂ²(Î³^{âd}) â LÂ²(â^d)` â `mehlerLpEquiv` is one-dimensional, and there is no product Gauss measure
in the corpus.

**What identifying the two cores actually costs.**  The `polyOpC`/`gaussOpC` identification is *one*
approximation, not two theorems.  `closure polyOpC` is self-adjoint, and a self-adjoint operator has
no proper symmetric extension â this is now a theorem, not a remark:
`BookProof.SelfAdjointMaximal.eq_of_le_of_isSelfAdjoint` (`BookProof/Toolbox/ChapterSelfAdjointMaximal.lean`)
states that `A â¤ B` with `A` self-adjoint and `B` symmetric forces `A = B`, elementwise through
`B â B* â A* = A`; its form for closures, `closure_eq_of_le`, is the one S0 uses.  So it suffices that every
polynomial class lies in the domain of the closure of `gaussOpC` â a graph-norm approximation of a polynomial by compactly supported `CÂ²` classes â and
then `closure gaussOpC = closure polyOpC`, one self-adjoint operator described by both cores.  The
reverse approximation is unnecessary.  That one direction is now half formalized.  `BookProof.YangMillsPolyTail.exists_lintegral_tail_lt`
is the tail bookkeeping that was missing: the `Î³`-mass of a squared polynomial on `{R â¤ |x|}` is
arbitrarily small, from antitone indicator integrals and `lintegral_iInf`, with `memLp_eval` supplying
the finiteness that limit needs.  `BookProof.YangMillsPolyGraphNorm` states the approximation for the
actual operators â `polyOp` on the Hermite span, `PolyGraphApprox` the graph-norm condition â and
proves it gives `polyOp â¤ gaussOp.closure` (`polyOp_le_gaussOp_closure`, through
`le_closure_of_forall_approx`), hence `polyOp = gaussOp.closure` once `polyOp` is self-adjoint
(`polyOp_eq_gaussOp_closure`).  What remains is the annulus estimate: on the support of
`â2Ï_R' p' â Ï_R'' p + x Ï_R' p` the tails of `p`, `p'`, `p''` supply the smallness, and
`|Ï_R'| â¤ C/R`, `|Ï_R''| â¤ C/RÂ²` turn the fixed cutoff into a uniform-in-`R` bound.
`BookProof.YangMillsPolyCutoff` builds exactly that `Ï_R = smoothTransition (2 - xÂ²/RÂ²)`, with the
collar at `xÂ² = RÂ²` and `xÂ² = 2RÂ²` and both derivative bounds; what is left is the `LÂ²` assembly of
the three terms on the annulus and the outer tail.  That is analysis, with no spectral input.
`BookProof.YangMillsPolyLpNorm` supplies the two facts that assembly needs: `polyOpH_coe` and
`polyOpH_coeFn` put `T` on polynomial *classes* (`T` of a Hermite-span class is the class of
`dirichletPoly p`, represented by `gaussDirichlet (p.eval)`), and `enorm_toLp_sub` /
`norm_toLp_sub_eq` / `ofReal_norm_toLp_sub_sq` say the norm of a difference of classes only sees the
difference of representatives, squared into a `lintegral` of `ofReal` — the shape
`exists_lintegral_tail_lt` bounds.  `polyOp_closure_le_gaussOp_closure` and
`polyOp_closure_eq_gaussOp_closure` restate the identification over `polyOp.closure`, since
essential self-adjointness makes the *closure* self-adjoint and not `polyOp` itself.

The `â` form is a transport: `polyOpC` and `gaussOpC` live on
`Cx (Lp â 2 Î³)` and `Lp â 2 Î³`, and no equivalence between the two has been built, so the
identification is stated over `â`, where `gaussOp` lives.

**Why the complexification matters here.**  Deficiency spaces are a complex notion: over `â` there is
no `i`.  So Route A (and the Friedrichs/deficiency vocabulary of `ChapterYangMillsFriedrichs`)
speaks about a complex Hilbert space.  The corpus has its own complexification for this,
`BookProof/Realification/Complexification.lean` (`Cx W`, with `InnerProductSpace â`, `cxMapâ`, the
`norm_sq` splitting and completeness), and `ChapterYangMillsPolyCore` is built on it: the real operator
is extended to a global `coreExt` by a left inverse of the Hermite span's inclusion and complexified
with `cxMapâ`, so â-linearity of `polyOpC` holds by construction.

**Why the â lift is not just bookkeeping either.**  Mathlib has no complexification of real Hilbert
spaces (`Complexification` does not exist in this version) and no bundled `Lp.re`/`Lp.im` maps, only
the function-level `MeasureTheory.memLp_re_im_iff`.  So `Lp â 2 gaussMeasure` cannot be reached from
`gaussOp` by transport: a â-valued `gaussDirichlet`, â `MemLp` of its image, â-linear well-definedness
and â inner-product symmetry must be built directly.  The derivative decomposition needed is
`(deriv f x).re = deriv (fun y => (f y).re) x` (from `Complex.reCLM.comp_hasDerivAt`), and the â
symmetry then splits into four applications of the real symmetry `integral_gaussDirichlet_mul_comm`;
the â integrals must be split with `integral`-`re`/`im` lemmas and integrability side conditions.

**Done** in `BookProof/Qym/ChapterYangMillsGaussFormComplex.lean` (no `sorry`; the only axioms are
`propext`, `Classical.choice`, `Quot.sound`): `gaussDirichletC`, the componentwise splitting
`gaussDirichletC_re`/`_im`, `memLp_gaussDirichletC`, the weighted â symmetry
`integral_gaussWeight_innerC_comm`, and â on classes â the â-linear partial map `gaussOpC` with
`gaussOpC_inner_comm` (symmetry), `gaussOpC_inner_self_eq_re` + `gaussOpC_quadForm_nonneg`
(positivity) and `gaussOpC_symmetric` + `gaussOpC_form_closable` (the Friedrichs handoff).
Two API traps cost the time: `âª_,_â«_â` **does not exist** in this mathlib (the complex notation is
plain `âªx, yâ«` under `open scoped ComplexInnerProductSpace`, and opening `RealInnerProductSpace`
too makes `âªgaussDirichletC F x, G xâ«` ambiguous), and `integral_re`/`integral_im` are unusable as
rewrites against `z.re` â `RCLike.re_to_complex` keys on `reC` and `RCLike.re` does not match it
syntactically â so the split uses `Complex.reCLM`/`imCLM.integral_comp_comm` instead.

**Also done, over `â`** â the *other* route of gap 1 below, which turns out to be shorter than the â
lift for everything except the deficiency analysis.  `BookProof.YangMillsFriedrichsReal`
(appended to `ChapterYangMillsFriedrichs`) is Part B at `[InnerProductSpace â F]`:
`SymmetricOn`, `quadForm`, `formInner`, `formNormSq`, the expansions
`formNormSq_add`/`_sub`/`_add_smul`, CauchyâSchwarz `formInner_sq_le`, and `form_closable`.
Every proof is the complex one with `starRingEnd`, `Complex.add_re` and `continuous_re`
deleted; the two places that do *not* simplify mechanically are the swap `âªH x, yâ« = âªx, H yâ«`
(this mathlib has `real_inner_comm`, `âªy,xâ«_â = âªx,yâ«_â`, and no `inner_comm`) and the limiting step
of `form_closable`, where `innerSL â v` must be turned into a
*plain* continuity statement (`continuous_const.inner continuous_id`) rather than `simpa`d
through the `ContinuousLinearMap` coercion.  The instantiation lives in
`BookProof/Qym/ChapterYangMillsGaussFormReal.lean`, a separate leaf module because the import graph
already runs `ChapterYangMillsGaussForm â â¦ â ChapterYangMillsFriedrichs`: importing the Gaussian
chapter from inside the Friedrichs chapter is a build cycle, not a style question.  It provides
`gaussOp_symmetricOn_real`, `gaussOp_quadForm_nonneg_real` and `gaussOp_form_closable_real` â
`form_closable` on `gaussOp` with no complexification anywhere in statement or proof.

Item 2 is discharged at the `Lp` level and item 3 is discharged.

**What `ChapterYangMillsFriedrichs` still needs.**  That chapter is a self-contained Friedrichs
construction over an *abstract* complex Hilbert space (`F`, `D : Submodule â F`), with
`formInner H x y = âªx,yâ« + âªx, H yâ«`, `formNormSq`, `form_closable`, and the classical Friedrichs
theorem entering as the explicit hypothesis `friedrichs` of
`friedrichs_extension_of_semibounded`.  It has never been instantiated on the Gaussian operator.  The
gap list, in order of difficulty:

1. **Real-to-complex shim.**  `gaussOp` lives on `Lp â 2 gaussMeasure`; the chapter is `â`-valued
   (`SymmetricOn D H`, `quadForm H x = (âªx, H xâ« : â).re`, `IsPositiveSelfAdjointExtension`).  Either
   complexify (`Lp â 2 gaussMeasure` with the `â`-linear extension of `gaussOp`) or port Part B of
   the chapter to `â`.  **Closed both ways**: the first by
   `ChapterYangMillsGaussFormComplex.gaussOpC : Lp â 2 gaussMeasure ââ.[â] Lp â 2 gaussMeasure`
   with the â-valued `CÂ²` core `gaussCoreC`, the second by `BookProof.YangMillsFriedrichsReal` and
   `ChapterYangMillsGaussFormReal.gaussOp_form_closable_real`.  The real route is kept because
   closability does not need `i` â only the deficiency spaces do.
2. **`SymmetricOn gaussCore gaussOp`** â **closed**: `gaussOpC_inner_comm`, in the `SymmetricOn`
   form as `gaussOpC_symmetric`.
3. **Positivity on the core**, `0 â¤ quadForm gaussOp x`, i.e. `0 â¤ âªx, T xâ«_Î³` â **closed**:
   `gaussOpC_quadForm_nonneg`, from `gaussOpC_inner_self_eq_re` (the real part of the diagonal is
   `gaussForm F.re F.re + gaussForm F.im F.im`) and the corpus' `gaussForm_self_nonneg`.
4. **Closure of the form** â **closed**: `gaussOpC_form_closable` is `form_closable` applied to
   (2) and (3), already instantiated on this operator.
5. **Identification** â the extension Friedrichs produces is *some* positive self-adjoint extension;
   calling it `gaussOp.closure` needs exactly the essential-self-adjointness statement above (or the
   domain identification âform domain of `gaussForm` = `HÂ¹(Î³)`â, which is the same gap in another
   dress).  And the classical theorem itself stays a hypothesis: the chapter documents it as an
   admitted theorem (ReedâSimon II, Thm X.23), never as an axiom.

So `ChapterYangMillsFriedrichs` does not lack closability any more â it lacks the instantiation
(1)â(3) on `gaussOp` and, for the *identification* of its output with `gaussOp.closure`, the same
essential-self-adjointness theorem that S0 item 1 still needs.

#### S3 â the solve-error bookkeeping

`BookProof/Sirk/ChapterShiftInvertBookkeeping.lean` (namespace
`BookProof.HashimotoShiftInvertBookkeeping`) supplies the two S3 pieces that the shift-invert
estimates presuppose, and no spectral claim:

* **Solve error.** `norm_solve_error_le` bounds the error of an inexact linear solve by the
  residual; `IsShiftInvert.solve_error_le` specializes it to the shift-invert operator, so a
  residual-level solve is enough for the approximation S3 asks for.
* **Compressed â  compressed resolvent.** `exactSolve` is `(2/3, â1/3)` and `compressedSolve` is
  `(1/2, 0)` for the `2 Ã 2` model with `X = (A+1)â»Â¹`; both solve their own problems
  (`exactSolve_solves`, `compressedSolve_solves`) yet differ by `X` applied to the defect
  (`defect_image_eq_error`, `compressed_solve_error_eq_defect_image`), so
  `compression_ne_resolvent` is not a numerical artifact.  This is the S3 bookkeeping the plan's
  "approximation, with a separate spectral gate" wording depends on: the gate is still separate,
  and no Hashimoto-band statement (S42) is claimed here.

## Historical phases and implementation notes (2026-10-30 to 2026-11-04)

The revised work package above governs their interpretation. In particular, âDONEâ,
âunconditionalâ, âform of recordâ and âcertified gapâ below describe the cited model's
actual theorem statements only; they do not discharge its missing physical bridges.

The original motivation is to establish an **analytical lower bound for the spectral
separation $\beta_\infty>\theta_\infty$**. `ChapterTempleSeparationNecessary.lean` shows
that **Rayleigh data and local residuals alone cannot exclude unseen lower eigenvalues.**

To prevent the Temple uncertainty $\delta = \frac{\eta^2}{\beta - \theta}$ from blowing up as the basis/truncation order $n \to \infty$, the separation $\beta_\infty - \theta_\infty \ge c > 0$ must be derived **analytically from the structural geometry of the continuous Hamiltonian**, rather than extracted numerically from truncated matrices.

---

### Research Roadmap Overview

```
[Phase 1: Geometric Characterization]
Identify flat directions of the Weyl potential V(A) = 1/2 BÂ²
                     â
                     â¼
[Phase 2: Quantum Channel Taming (B. Simon Mechanism)]
Prove transverse zero-point energy lifts classical flat directions
                     â
                     â¼
[Phase 3: Construction of Gapped Reference Operator H_ref]
Build solvable comparison operator with certified discrete gap c_ref > 0
                     â
                     â¼
[Phase 4: Relative Form Bounding in Lean 4]
Prove H_YM â¥ câ H_ref - câ on the BRST physical core
                     â
                     â¼
[Phase 5: Spectral Isolation & Transfer to SIRK/Temple Pipeline]
Discharge hypothesis in ChapterRitzCertificate & SpectralGapStability
```

---

### Phase 1: Isolating the Soft-Mode Degeneracies

#### 1.1. The Origin of the Soft Modes
In the 3D Weyl-gauge YangâMills Hamiltonian:
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
is an assumption of the later phases â it is a list of missing inputs.

**What is done** (all `sorry`-free, `axiom`-free; `lake build BookProof` compiles):

* `BookProof/ChapterBookBrstYangMills.lean` â the book's charge is **realized, not assumed**:
  `Î©(x) = Ï^Î¼_a â_Î¼ Ïâ _a â Ï^Î¼_a f_{abc} A_{Î¼b} Ïâ _c â (i/2) f_{abc} Ïâ _a Ïâ _b Ï_c` as operators
  on a concrete graded state space, with the canonical relations proved (`bookCCR`, `bookGhostCar`),
  the **Gauss-law algebra derived** from them (`gaussGen_bracket`,
  `[ð¢_c, ð¢_e] = Î£_h f_{ceh} ð¢_h`), and **`bookOmega_nilpotent`** = `Î©Â² = 0` for the full charge.
  `bookOmega_eq_brstCharge` identifies it with `i` times the abstract charge of
  `BookProof.QuantumGravityBrstCharge`, which is where `glin_sq` (the square of the constraint
  part) lives.
* `BookProof/ChapterBRSTNilpotent.lean` â `brst_charge_nilpotent`: the cubic ghost term squares to
  zero from the CAR plus the Jacobi identity alone (normal ordering: a quartic term killed by
  fermionic antisymmetry, two contractions killed by Jacobi).
* `BookProof/ChapterBrstReducedTransfer.lean` â the **descent to cohomology** for an abstract
  *bounded* nilpotent `Î©` commuting with a strongly continuous unitary group: `transfer` is a
  one-parameter group of linear automorphisms of `Cohomology Î© = ker Î© â§¸ closure (range Î©)`
  (`transfer_comp`, `transfer_bijective`), and the quotient norm is preserved
  (`infDist_exactStates_eq_of_comm_explicit`), with the Stone instance `stoneTransfer` for an
  unbounded self-adjoint Hamiltonian.
* `BookProof/ChapterBrstTruncationLeakage.lean` and `ChapterBrstUnboundedLeakage.lean` â the
  *leakage* side: for an unbounded exact generator and the compression `P T P` to a
  finite-dimensional retained subspace, `leakage_le` bounds `âÎ©(e^{-itB}x)â` by `âÎ©xâ + âÎ©âKt`,
  and the exact dynamics itself does not leak.

So the algebra of Â§1.1 is *not* the gap: the non-abelian charge, its nilpotency, and the Gauss law
are all proved.  **What Milestone 1 needs is the passage from that algebra to a statement about
`H_phys` as a Hilbert space**, in four steps.  Step 2 is done, for a bounded charge and for a
closed densely defined one (see its status note); step 1 is done â decomposition *and* descent,
for a closed densely defined `Î©` (see its status note); steps 3 and 4 carry status notes too
(2026-11-02 and 2026-11-01).  All four are therefore addressed below, each with what it proves
*and* what it does not:

1. **An unbounded charge.**  `ChapterBrstReducedTransfer` needs `Î©` *bounded* (it uses `Î©` as an
   element of `H âL[â] H`).  The field-theoretic `Î©` is a cubic differential operator, so the
   reduction lemmas have to be reproved for `Î©` closed and densely defined with `Î©Â² = 0` on a core
   invariant under the dynamics, and with `[H, Î©]` expressed as strong commutation of `e^{-itH}`
   with `Î©` on that core.  Until then the two chapters do not compose: one has a concrete `Î©` and
   no `H`, the other an abstract bounded `Î©` and an abstract `H`.  (The bounded `Î©` is now only
   needed for the *descent*, not for the decomposition â see the status note below.)

   **Status (2026-10-31): the norm side is done for a closed densely defined `Î©`.**
   `BookProof/ChapterBrstUnbounded.lean` (`BookProof.ChapterBrstUnbounded`, no `sorry`) reproves
   the harmonic decomposition for a partially defined charge `Om : H ââ.[â] H` with **closed
   graph** (`HasClosedGraph`), **dense domain** and `Î©Â² = 0` on its domain (`IsNilpotent`, with the
   domain clause that a partial map needs).  Three things change relative to the bounded chapter:
   `isClosed_physicalStates` â the kernel of a closed operator is closed, by pulling the closed
   graph back along `x â¦ (x, 0)`, where the bounded case used continuity; the adjoint is now built
   by hand (`adjointDomain`, `adjointFun`, `adjoint`) because no bounded adjoint exists, and
   **density** is exactly what makes it a function (`adjoint_unique`: two representing vectors
   differ by a vector orthogonal to the dense domain), giving
   `exactStates_orthogonal` (`(closure (range Î©))á® = ker Î©â `) and
   `range_orthogonal_eq_adjointKernel`; and the quotient-norm machinery carries over verbatim â
   `sup_exact_harmonic`, `disjoint_exact_harmonic`, `hodge_decomposition`
   (`harmonic â exact â coexact = â¤`), `harmonicPart_mem`, `harmonicPart_eq_of_sub_mem_exact`,
   `exists_harmonic_decomposition` and `infDist_eq_norm_harmonicPart`
   (`infDist x (exactStates Î©) = âharmonicPart xâ`, still attained).

   **Status (2026-11-01): the descent is now done too.**
   `BookProof/ChapterBrstReducedTransferUnbounded.lean`
   (`BookProof.BrstReducedTransferUnbounded`, no `sorry`) closes what the note below used to call
   the bounded-only remainder.  For a partially defined `Î©` the commutation hypothesis
   `[H, Î©] = 0` cannot be one equation â `Î© (U y)` is not even a term unless `U y` is known to lie
   in the domain â so it splits in two, and neither half can be dropped:
   `DomPreserve Om U` (the evolution maps the domain into itself) and
   `StrongCommute Om U hdom` (`U (Î© y) = Î© (U y)` for `y` in the domain, read at `hdom y`).
   From those two, everything the bounded chapter proved carries over:
   `physicalStates_invariant` (nilpotency *not* needed: `Î© x = 0` is transported to
   `Î© (U x) = U (Î© x) = U 0 = 0`), `exactStates_invariant` (where it is **continuity of `U`**,
   not boundedness of `Î©`, that carries the range into its closure â the evolution is a
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

   Von Neumann's closed-range theorem `closure (range Î©â ) = (ker Î©)áµ®` is now proved for the
   unbounded chapter, in `BookProof/ChapterBrstUnbounded.lean` Â§7:
   `closure_range_adjoint_eq_coexact` (with `range_adjoint_orthogonal`: `(range Î©â )áµ® = ker Î©`,
   `adjoint_adjoint_eq`: `Î©â â  = Î©`, and `adjoint_domain_dense`: closedness and density pass to
   `Î©â `).  The proof is the graph rotation of `Submodule.adjoint` in `WithLp 2 (H Ã H)`: rotation
   is an involution on closed graphs (`adjoint_adjoint_of_isClosed`) and
   `Î©â .graph = Î©.graph.adjoint` (`graph_adjoint`), so the coexact sector defined as `(ker Î©)áµ®`
   *is* `closure (range Î©â )`.  The earlier inclusion `range_adjoint_le_coexact` is now the easy
   half of an equality, and the third summand of the Hodge decomposition is named as in the
   bounded chapter.  (The harmonic sector, the exact sector and the quotient norm never depended
   on this identification.)
   The two chapters still do not *compose*, for the reason item 1 states: `[H, Î©] = 0` for a
   concrete `H` is not proved, so `hdom` / `hcomm` are hypotheses, not theorems, in a specific
   model.  The concrete `H` itself is no longer missing: the corpus carries the YangâMills and
   Standard-Model Hamiltonians in the nested Fock space â `ymHamiltonian`
   (`BookProof/Qym/ChapterYangMillsHermite.lean`, the Gaussâpolynomial core of `LÂ²(ââ¹â¹)`) and
   `smHamiltonian` (`BookProof/Sm/ChapterSmHamiltonian.lean`, `d = 163`) â so what is missing is
   the commutation with `Î©`, not the operator to commute with.  (The gauge/BRST symmetry it must
   commute with is in the corpus too: `ChapterBookBrstYangMills` and
   `ChapterBookBrstGaugeFixing`.)

   **Progress on the missing commutation (2026-11-03).**
   `BookProof/ChapterBrstYmCommute.lean` (`BookProof.BrstYmCommute`, no `sorry`, no `axiom`)
   now carries the **constraint half** of `[ymHamiltonian, Î©] = 0` for the concrete model, on
   the `99 = 3 + 24 + 72` coordinate space of `book.tex:7045`:

   * the Gauss generators `ð¢_d` realized as derivations of `â[X_0â¦X_98]` extended to the **jet
     coordinates** `â_j A_{ka}` â the extension is not cosmetic: a constraint that rotates only
     the `A`-slots leaves `X_D Â· (f A A)` cross terms in `[Î£_m B_mÂ², ð¢_d]` uncancelled;
   * `ymGaussDer_bracket` / `ymGaussPoly_bracket` / `ymGauss_bracket`:
     `[ð¢_c, ð¢_e] = Î£_h f_{ceh} ð¢_h`, reduced to the contracted field identity
     `field_identity_C` and applied block-by-block;
   * `ymConstraintAlgebra` and `ymOmega_nilpotent` â `Î© = i â¢ brstCharge G.f ð¢ Ï Î²` on
     `â[X_0â¦X_98] â Î(ââ¸)` and `Î©Â² = 0`.

   **What this still does not give.**  The two Casimir lemmas the Hamiltonian half needs are
   not there, so `hdom` / `hcomm` remain hypotheses:
   `[Î£_m Ï_mÂ², ð¢_d] = 0` (needs the vector relation `[â_{jc}, ð¢_d] = Î£_b f_{bcd} â_{jb}`,
   hence `â_i (ymGaussVec G d k)` by coordinate case split) and
   `[Î£_m B_mÂ², ð¢_d] = 0` (needs `ð¢_d(B_{ia}) = Î£_g f_{agd} B_{ig}`, i.e. the scalar
   contraction `Î£_e f_{aec}f_{ebd} + Î£_e f_{abe}f_{ecd} = Î£_g f_{agd}f_{gbc}` from
   `G.jacobi` + `G.antisymm` + `G.cyclic`).  Given those, `ymOmega_comm_ymH` is one
   application of `brstCharge_comm_of_comm`, and the module header records that route.  The
   regime is the constant gauge algebra `G.D = 0`, the same hypothesis
   `gaussDer_casimirPoly` / `casimir_bookOmega_comm` already carry.
2. **A quotient norm that exists.**  `infDist x (exactStates Î©)` is the norm of the class `[x]` in
   the quotient *only* when `exactStates Î© = closure (range Î©)` is a closed subspace of a Hilbert
   space.  On the ghost sector the natural form is indefinite, so the quotient norm has to come
   from the **harmonic (invariant) representative** â a Hodge-type decomposition
   `H = ker Î© â© ker Î©* â range Î© â range Î©*` â rather than from `infDist`.  This is the one
   genuinely functional-analytic (not merely bookkeeping) input of the phase; with it,
   `physicalStates_invariant` / `exactStates_invariant` transfer verbatim, without it they do not.

   **Status (2026-10-31): DONE for a bounded nilpotent `Î©`, and the decomposition is a theorem,
   not a redefinition.**  `BookProof.ChapterBrstHarmonicDecomposition`
   (`BookProof/ChapterBrstHarmonicDecomposition.lean`, no `sorry`) proves the Hodge decomposition
   on a complex Hilbert space from `Î©â ` alone â the two orthogonal complements are
   `exactStates_orthogonal` (`(closure (range Î©))á® = ker Î©â `, via `orthogonal_range` and
   `orthogonal_closure`) and `coexactStates_orthogonal` (`(closure (range Î©â ))á® = ker Î©`), so the
   harmonic states `harmonicStates = ker Î© â ker Î©â ` are a *direct complement* of the exact ones
   inside the physical subspace (`sup_exact_harmonic`: `exact â harmonic = physicalStates`,
   `disjoint_exact_harmonic`) and the three summands span the space with pairwise orthogonal
   parts (`hodge_decomposition`: `harmonic â exact â coexact = â¤`, with
   `disjoint_exact_coexact`, `disjoint_harmonic_coexact`).  The harmonic representative
   `harmonicPart x = x â P_{exact} x` is explicitly constructed, is harmonic for closed `x`
   (`harmonicPart_mem`), differs from `x` by an exact state (`sub_harmonicPart_mem_exact`), and
   depends only on the class (`harmonicPart_eq_of_sub_mem_exact`).  The plan's point 2 is then the
   **identity** `infDist_eq_norm_harmonicPart`:
   `infDist x (exactStates Î©) = âharmonicPart xâ` â the infimum is *attained*, so the harmonic norm
   is a norm on cohomology and agrees with `infDist`; and `exists_harmonic_decomposition` states
   the decomposition of a closed state with its orthogonality explicit.  The passage to a closed
   densely defined charge is now in `ChapterBrstUnbounded` (see the status note of item 1 above),
   which reproves the same statements for `Î© : H ââ.[â] H` with closed graph and dense domain.
   The ghost-sector indefiniteness is not addressed in either chapter: both work with the
   Hilbert-space inner product, which is exactly why the decomposition exists.
3. **âLongitudinal = exactâ.**  The claim â`H_phys` contains no longitudinal soft zero-modeâ is the
   identification `closure (range Î©) = span{â_i Ï}` (the pure-gauge directions are *precisely* the
   BRST-exact states), followed by the observation that a longitudinal plane wave is not harmonic,
   i.e. is not in `ker Î© â© ker Î©*`.  At present the charge is realized on a graded polynomial
   algebra and `range Î©` is not identified with any longitudinal span; there is also no
   `H_phys` â no completion, no inner product â to speak of a zero-mode *in*.

   **Status (2026-11-02): the identification is a theorem at the level the algebraic realization
   carries it, and the observation half is a theorem too.**
   `BookProof/ChapterBrstLongitudinal.lean` (`BookProof.BrstLongitudinal`, no `sorry`) closes the
   algebraic half in the realization of `book.tex`, on the graded state space the corpus already
   works on, and sits on the gauge/BRST symmetry work already in `timepiece/BookProof/`:
   `ChapterBookBrstYangMills` (the charge realized with `bookCCR`, the Gauss-law algebra and
   `bookOmega_nilpotent`) and `ChapterBookBrstGaugeFixing` (gauge-invariant observables commute
   with the charge â `bookOmega_comm_of_comm` â and descend to `brstCohomology`,
   `mem_exactStates_of_comm`).

   * The gauge orbit of `A_{Î¼a}` splits into the longitudinal gradient and the non-abelian
     remainder (`gaussVec_eq_longitudinal_add_comm`): `longitudinalGaugeVec` is the
     field-independent `ââ_Î¼ Î±_a` â constant as a polynomial, which is what makes it a gradient
     (`longitudinalGaugeVec_eq_zero_iff` reads it off `G.D` alone) â and `commGaugeVec` is the
     `Î£_g f_{agc} X (Î¼, g)` bracket, which vanishes identically for `f = 0`
     (`commGaugeVec_eq_zero_of_abelian`).  So for an abelian gauge algebra the orbit *is* the
     longitudinal span: an equality, not an inclusion.
   * In that case the charge collapses to its derivative term (`bookOmega_abelian`), and the
     canonical relation `bookCCR` then fixes its commutator with the field:
     **`comm_bookOmega_Afield`** is `[Î©, A_{Î¼a}] = âi Â· dChi G Î¼ a`, with *no* commutator piece â
     the BRST variation of the field *is* the ghost-dressed longitudinal direction
     (`dChi_eq_longitudinal_dress`), so the directions the reduction removes are precisely the
     ones the charge produces.
   * The payoff is `longitudinal_mem_exactStates_of_physical`: applied to a BRST-closed `v`,
     `Î© (A_{Î¼a} v) = âi Â· dChi G Î¼ a v`, so the ghost-dressed longitudinal direction maps into
     `exactStates` and its class in `brstCohomology` is zero â "no longitudinal soft zero-mode"
     as far as the algebraic realization carries it.  The *observation* half â a longitudinal
     plane wave is not harmonic â is `ChapterBrstHarmonicDecomposition.no_longitudinal_zero_mode`:
     for any `L â¤ exactStates`, a state of `L` lying in `ker Î© â© ker Î©â ` is zero, from
     `disjoint_exact_harmonic` alone, so it needs no field model.
   * The Hamiltonians this charge would have to commute with are in the corpus as well, in the
     nested Fock space: `ymHamiltonian` (`BookProof/Qym/ChapterYangMillsHermite.lean`, `LÂ²(ââ¹â¹)`)
     and `smHamiltonian` (`BookProof/Sm/ChapterSmHamiltonian.lean`, `d = 163`).  `[H, Î©] = 0` for
     either is not proved here; that is the composition item 1 still records as open.

   **Honest boundary.**  What is proved is one direction, in the abelian case, as an identity of
   operators: `longitudinal â gauge orbit = exact`.  The converse â `closure (range Î©) =
   span{âáµ¢Ï}` as an equality of *subspaces* â needs the gauge field to be a function on
   spacetime; `BookState N` carries no inner product and no completion, so it is not an equality
   of closures yet.  For `f â  0` the orbit is strictly larger than the longitudinal span: the
   commutator picks up the `Î£_{bc} f_{abc} A_{Î¼b} Ïâ _c` term from applying `bookCCR` to the
   `f`-carrying summand of `bookOmega` â a shape, not a theorem.  And neither half speaks of a
   completed `H_phys`: the realization is algebraic on `BookState`, while the Hilbert-space
   statement lives in `ChapterBrstHarmonicDecomposition` (bounded) / `ChapterBrstUnbounded`
   (closed densely defined).

   **Status (2026-11-06): the equality of closures is now a theorem in a model that has both a
   derivative and a Hilbert space.**  `BookProof/BrstLongitudinalExact.lean` (no `sorry`) works on
   the periodic lattice, fields `Fin (n+1) â â` with the cyclic difference
   `âf(j) = f(j+1) â f(j)`, and the nilpotent charge `Î©(x, y) = (0, âx)` on
   `(fields) Ã (ghosts)` â the abelian derivative-gauge charge of `ChapterBrstLongitudinal` with
   the ghost dressing kept and the gauge algebra trivialized.

   * **`range_derivLin`**: `range â = {f | ââ±¼ f(j) = 0}`.  One inclusion is `sum_deriv` (a
     gradient has no zero mode); the other is explicit â the cumulative sum `cumFun f` of a
     mean-zero field satisfies `â(cumFun f) = f` (`derivLin_cumFun`, with the wrap-around at the
     last site paid for by `â f = 0`).  So the right-hand side is genuinely `span{âáµ¢Ï}`, not
     merely a space the gradients sit inside.
   * **`brstCharge_nilpotent`**: `Î©Â² = 0` â the ghost factor raises once and the second
     application differentiates zero.
   * **`exactStates_eq_longitudinal`**: `exactStates Î© = â¥ Ã {f | â f = 0}`, i.e. the BRST-exact
     states *are* the ghost-raised longitudinal fields â `closure (range Î©) = span{âáµ¢Ï}` in the
     model, with the closure nothing but `topologicalClosure` of a closed range.
   * **`longitudinal_le_exactStates`** and **`physicalStates_eq`**: every longitudinal state is
     exact (hence zero in the cohomology), and the BRST-closed states are those whose gauge-field
     part is constant (`âx = 0`) â the surviving gauge-field mode is the zero mode, which is
     exactly "no longitudinal soft zero-mode".  `disjoint_exact_constants` records that the
     constant sector and the exact sector meet only at zero.

   **Boundary.**  This is the periodic one-dimensional model with a bounded charge and one ghost.
   The physical statement is about the cubic charge of the 3+1 continuum theory on a field Hilbert
   space, where `Î©` is unbounded and the gauge algebra non-abelian (the `commGaugeVec` term of
   `comm_bookOmega_Afield_nonabelian`).  The identification theorem is now proved where both
   sides are defined objects; the continuum version still needs the field Hilbert space and the
   closed unbounded `Î©`, i.e. the same inputs as item 1, and it says nothing about a continuum
   `H_phys`.
4. **Stability of the bottom under the elimination.**  Phases 2â5 bound the bottom and the first
excited level of the operator on the *unreduced* core (`degreeForm`, `barrierForm`, and the
   `FormDomination` certificate).  For the elimination to be legitimate those numbers must be those
   of the reduced operator: one needs that restriction to the transverse sector does not lower
   `Î¸â`, or equivalently that the eliminated directions carry no spectral weight near the bottom.
   Without this, Phase 1 could remove exactly the directions that dominate the bottom and Phases
   2â5 would be bounding a different operator.

   **Status (2026-11-01): the statement is now a theorem for the diagonal forms of this corpus,
   and the reason it is short is itself the content.**  In `BookProof.YangMillsFormClosure`
   (section 5, no `sorry`):

   * `formBottom f = sInf (Set.range f)` is the bottom of the symbol, with
     `formBottom_le_of_bddBelow` reading it off.  `â` is only *conditionally* complete, so there
     is no `â¨` into `â`; every statement is therefore equally available in the "any lower bound
     `Î¸`" form, which is the form the plan's `câÎ_ref` already takes.
   * **`diagonalForm_ge_of_le_symbol`** / **`closedForm_ge_of_le_symbol`** â `Î¸ Â· âÂ·âÂ² â¤ q(x)`
     for every `Î¸ â¤ f n`, on the core and on `LÂ²`, and hence
     **`diagonalForm_ge_formBottom`** / **`closedForm_ge_formBottom`** at `Î¸ = formBottom f`.
   * **`sector_bottom_ge_of_le_symbol`** / **`sector_bottom_ge_formBottom`** â for *any* set `S`
     of normalised retained states, `ofReal Î¸ â¤ sInf (closedForm f '' S)`: the Rayleigh infimum
     over a sector is bounded below by the *same* constant as over the whole space.  That is
     exactly "restriction to the transverse sector does not lower `Î¸â`", and it is where the
     plan's "the eliminated directions carry no spectral weight near the bottom" lands.

   **Why it is short, and what that costs.**  The bound is *symbolwise*: every term of
   `closedForm f x = â' n, ofReal (f n) Â· ofReal (âx nâÂ²)` is indexed by one multi-index, so the
   form never mixes retained with eliminated directions and restriction cannot improve on a
   symbolwise estimate.  Diagonality is a property of the free, quartic and barrier forms the
   corpus models â it is the same hypothesis under which `formDomination_closed` transfers, and
   the same one its honest boundary says does not cover a magnetic interaction that mixes
   multi-indices.  So the item is closed *for the forms Phases 2â5 actually bound*; for an
   interacting form with off-diagonal blocks, "no spectral weight near the bottom in the
   eliminated directions" is a genuine statement about those blocks, and it is not proved here.
   The reduced space itself â the quotient `H/(exact â harmonic)` â is built in
   `ChapterBrstReducedTransfer` / `ChapterBrstUnbounded`; what is missing there is item 3 above,
   the identification `closure (range Î©) = span{â_i Ï}`, not the stability of the bottom.

   **The off-diagonal half (2026-11-04).**  The sentence above leaves one case open: a form whose
   blocks mix multi-indices, where the symbolwise argument has nothing to read.  It is closed for
   any interaction with finite HilbertâSchmidt constant, in Â§4 of
   `BookProof.YangMillsFormClosureNonDiagonal`: the form bound `abs_kernelForm_le_of_hs` gives
   `kernelForm_ge_neg_of_hs` (`âÏâcâÂ² â¤ qK`), so **`diagonalForm_add_kernelForm_ge`** bounds the
   interacting form below by `Î¸ â Ï` on the core whenever `Î¸` bounds the diagonal symbol, and
   **`sector_bottom_ge_interacting`** is the sector statement: over any nonempty set of
   *normalised* retained core states, `sInf` of the interacting form is at least `Î¸ â Ï`, with no
   hypothesis on which indices the kernel couples and no hypothesis on the sector.  So restriction
   cannot lower the bottom by more than the HilbertâSchmidt constant of the interaction â the same
   constant `hopping_farisLavine` charges to the shift, and for the hopping matrix unit
   (`hopping_sector_bottom`) it is exactly `1`.

   **The `LÂ²` lift (2026-11-04).**  Â§5 of the same module closes the lift this item was missing.
   Truncations were never the right tool here: `closedForm_eq_iSup_truncate` lifts the diagonal
   part because `closedForm` is the supremum of its truncations, and a non-diagonal kernel form is
   not monotone along truncations.  What replaces it is the operator: `closedKernelForm K x` is the
   weighted double series over **all** of `Idx d Ã Idx d`, absolutely convergent for every
   `x â âÂ²`, and `abs_closedKernelForm_le` gives `|closedKernelForm K x| â¤ ÏâxâÂ²` with the *same*
   `Ï` â one CauchyâSchwarz with exponents `2, 2` in `âÂ²(Idx d Ã Idx d)` between the kernel and the
   product of the two coefficient rows (`tsum_sq_kernel_le`: the `ÏÂ²` is the total HilbertâSchmidt
   mass, not a partial sum; `tsum_sq_weight_le`: the weight mass is `âxââ´`).  On the core it *is*
   the core form (`closedKernelForm_coreEmbed`), so this is an extension and not a different form;
   `closed_diagonal_add_kernelForm_ge` gives `Î¸ â Ï â¤ closedForm f x + closedKernelForm K x` on the
   form domain (`closedForm f x â  â¤`), and `closed_sector_bottom_ge_interacting` /
   `closed_hopping_sector_bottom` carry the sector statement to `LÂ²`, so the reduced space itself
   can be a closed subspace of `âÂ²` and not only a set of core states.  Note what the hypothesis
   costs: finiteness of the total HilbertâSchmidt mass holds at a **fixed cut-off**, where the
   interaction is an honest finite matrix, and it is not uniform in the cut-off â the number of
   coupled multi-indices and the magnetic matrix elements grow with the mode index, so no single
   `Ï` survives the continuum limit, where the magnetic term is only relatively form bounded with
   `a < 1`.   Boundedness is a *sufficient* condition for closability (the interaction is then a
   continuous perturbation of the closed diagonal form, and the sum is closed on the same domain),
   the `a = 0` case of the FarisâLavine branch; it is not the necessary one.  **The comparison is
   now stated on `LÂ²` too (2026-11-04)**: Â§6 gives `closed_farisLavine_domination` â ratio
   `(1 â a)câ > 0`, shift `(1 â a)câ + b`, for a relative bound `a < 1` â with the finiteness of
   the closed forms as the only extra hypothesis, and `closed_dom_of_scaled_symbol` *derives* that
   hypothesis from a symbolwise inequality `câ f â¤ g + C` rather than assuming it (`toReal` of `â¤`
   is `0`, so the finiteness cannot be dropped).  What neither section supplies is a bound uniform
   in the cut-off: Â§7 computes it on a model â `magCutoffKernel_hs_mass` gives the magnetic ladder
   mass at most `dÂ² C Î^(d+1)`, i.e. a constant at most `d âC Î^{(d+1)/2}` â which is a power of
   the cut-off and not a uniform `Ï`, so the continuum still needs the `a < 1` branch with `a`
   bounded away from `1` uniformly.  The **ratio** is in fact uniform for free â
   `ladder_relative_bound_uniform` (Â§8) takes `a` as a free parameter, so `a(Î) < 1` at every
   cut-off, because at fixed cut-off the ladder is bounded â so what fails in the continuum is the
   constant, not the ratio.  And the finiteness hypothesis of the comparison is not an extra
   assumption for the YangâMills symbol: `closed_dom_of_scaled_symbol_auto` derives it from the
   symbolwise inequality whenever the ratio is positive, and `magnetic_closed_dom_of_scaled` (Â§9)
   applies it to `magSymbol`, the symbol of `magneticEnergyForm` of `YangMillsMagneticQuartic`.
   One scope note, because the continuum *is* formalized elsewhere: the space-time derivative is an
   outer-Fock operator (`dGamma`, `momOp`) and coincident-point products of outer fields are never
   formed â they are the momentum convolutions of `dft_samePointProduct`,
   `momentumCol_samePointProduct`, `samePointProduct_form_eq_momentum`.  The reduced form here is
   diagonal (`yangMillsForm_eq_diagonalForm`), so the ladder is a model of the coupling rather than
   the eliminated theory's magnetic slot, and carrying `Ï(Î)` across needs the off-diagonal part of
   the reduced Hamiltonian â not done.

   The **sharp** bound is available at the cut-off: `ladder_form_norm_le` (Â§10) proves
   `âq_K(x)â â¤ Â½Â·Q(x) + Â½Â·(Î£áµ¢ Aáµ¢Â²)Â·âxâÂ²` with `Q(x) = Î£â (Î£áµ¢ (náµ¢+1))âx nâÂ²`, and **no constant
   depends on `Î`**.  The reason is structural rather than computational: the ladder is a sum of
   `â(náµ¢+1)`-weighted raises, each raise is a partial isometry with `Sáµ¢*Sáµ¢ = Aáµ¢Â²Â·diag(náµ¢+1)` and
   `Sáµ¢Sáµ¢* â¤ Aáµ¢Â²Â·1`, so unit-weight AMâGM puts the occupation piece on the reference form with ratio
   `1/2` and the shift piece is bounded by `Aáµ¢Â²âxâÂ²` because raising one occupation is injective
   (`sum_raiseIdx_le`, `update_succ_inj`).  Rescaling the AMâGM weight moves along the family
   `(a, b) = (Îµ/2, (Î£ Aáµ¢Â²)/(2Îµ))`, so `a = 1/2` is the unit-weight member.

   And the HilbertâSchmidt constant does transfer to the outer-Fock picture after all, on the
   momentum side: `momentumCol_hs_mass` shows the momentum-transfer matrix of a symbol has *exactly*
   the symbol's `âÂ²` mass (`â_k â_i âmomentumCol V k iâÂ² = â_x âV xâÂ²`, via `(k,i) â¦ kâi` and
   Plancherel), and `momentumCol_samePointProduct_hs_mass` specialises it to a coincident-point
   product: mass `â_x âF xâÂ²âG xâÂ²`.  So `samePointProduct_form_hs_bound` bounds the form by
   `â(â_x âF xâÂ²âG xâÂ²)Â·âfÌâÂ²` â the position-space `Ï`, read on the momentum-transfer form.  On the
   BRST side the identification fails for a stated reason rather than an omission:
   `gaugeReduce_extTorsionCoef` writes every reduced torsion coefficient as `if x.1 = k then â¦`,
   i.e. the reduced one-particle matrix is *diagonal in momentum* and its off-diagonal block is zero
   (`gaugeReduce_extTorsionCoef_offDiag_eq_zero`), whereas the ladder moves one quantum between
   modes.  Different objects.

   Three refinements of that reading are now also proved.  The weight is visible as a family:
   `amgm_weight_family` shows `2st â¤ Îµ sÂ² + tÂ²/Îµ` for every `Îµ > 0`, so the member used above is
   `Îµ = 1`; `amgm_weight_half` (`Îµ = 1/2`) gives the same ladder the bound `|q| â¤ Â¼Q + (Î£Aáµ¢Â²)âxâÂ²`.
   The ratio `1/2` is therefore a choice of weight on the trade-off `(a, b) = (Îµ/2, Î£Aáµ¢Â²/(2Îµ))`, not
   an optimal constant, and `Îµ â 0` trades it against a growing shift.  The ratio is also what the
   closed form consumes, not only the cut-off matrix: `ladder_closed_domination_sharp` spells out
   `closed_farisLavine_domination` at `a = 1/2`, i.e. `Â½câÂ·closedForm Î¼ â (Â½câ+Ï)âxâÂ² â¤
   closedForm g + closedKernelForm K` on the `LÂ²` domain.  And the mass identity is not special to
   two factors: `chain_hs_mass`, `momentumCol_chain_hs_mass` and `chain_form_hs_bound` iterate it to
   any finite chain, with mass `â_x â_j âF_j xâÂ²`, so a chain of same-point outer fields reads as a
   momentum-transfer form with the product's HilbertâSchmidt constant and no distribution product.

   The same results are connected to the closed form and to the four-torus.  The cut-off box
   `Fin d â Fin Î` embeds componentwise in `Idx d = Fin d â â`, and `boxKernel` continues the ladder
   by zero off the box with the cut-off mass itself as its HilbertâSchmidt constant
   (`boxKernel_hs_finset`, exact and not a bound), so `ladder_closed_domination_box` applies the `LÂ²`
   domination with ratio `1/2` and shift `Â½câ + âm_Î` with nothing left to assume about the box,
   the mass or the support.  What is still open is the uniform constant: `m_Î` grows like
   `Î^{d+1}`, so the ratio is uniform in the cut-off and the shift is not.  The weight family is a
   genuine frontier rather than a sufficient condition: `amgm_pareto_iff` shows that
   `2st â¤ 2asÂ² + 2btÂ²` for all `s, t` holds exactly when `ab â¥ 1/4`, `amgm_min_shift` shows `1/(4a)`
   is the least shift admissible at ratio `a` and that it is attained at `s = t/(2a)`, and every `Îµ`
   member satisfies `(Îµ/2)Â·(1/(2Îµ)) = 1/4` (`amgm_weight_frontier_product`), so no member of the
   family is a weakening of another â choosing `Îµ` moves along the frontier.  On the four-torus the
   chain is carried as far as that section supplies: `chain_hs_massT4` makes the mass of a chain at
   a point of `(â¤/n)â´` multiplicative and `chain_form_eq_momentumT4` identifies the chain's form with
   `momentumColT4 (â j, F j)`; there is no `momentumCol_hs_mass` analogue on the 4-torus, so there
   the chain is read through the form rather than through the mass.

   The ladder identity itself is carried past the cut-off box.  `magCutoffOp_eq_sum_cre` is an
   identity of finite sums on `Box d Î`; on the dense core `CoreCoeff d` of `âÂ²(Idx d)` the ladder
   is an endomorphism `creCore` and `magCore A = âáµ¢ Aáµ¢ â¢ creCore i` has matrix elements
   `âáµ¢ Aáµ¢Â·creCoeff i Î² Î±` for every `Î² : Idx d` (`magCore_single_apply`), with no box and no `Î`.
   The raised vector sits one degree higher (`magCore_support_occDeg`), which is why the
   HilbertâSchmidt and relative-bound results bound the *form* and not the operator: closing
   `magCore` to a self-adjoint operator on `âÂ²` is not formalized â and cannot be, for `magCore`
   itself: the matrix `magKernel A m n = âáµ¢ Aáµ¢Â·creCoeff i m n` is not symmetric (`magKernel_asymm`:
   the entry at a raise is `Aáµ¢â(náµ¢+1)` while at the corresponding lowering it is `0`), so the
   symmetric object is `magSymKernel A m n = magKernel A m n + magKernel A n m`.  That is the
   kernel whose form `closedKernelForm` sees, and the domination of `ladder_closed_domination_sharp`
   is what a self-adjoint realization would have to consume; turning a closed, bounded-below form
   into its operator is the KLMN step, which the corpus does not have.

   The cut-off dependence of Â§7 is also settled rather than estimated.  The ladder's entries are
   `Aáµ¢â(náµ¢+1)`, so `norm_sq_magCutoffKernel_raise` gives the entry at a raise exactly and
   `magCutoffKernel_hs_mass_unbounded` shows that **no** `Ï` bounds the HilbertâSchmidt mass at every
   cut-off â along the ray family the mass is at least `Aáµ¢Â²Â·N(N+1)/2` at `Î = N+2`.  This is a
   statement about the *norm* of the ladder, not its form: the same `náµ¢+1` is charged to `Q` in the
   relative bound, which is exactly why the ratio `1/2` there carries no cut-off.  The bounded-form
   reading (`a = 0`) is cut-off-local, and the continuum needs the relative statement.

   On the four-torus the corresponding gap is closed as well: `momentumColT4_hs_mass` is the
   analogue of `momentumCol_hs_mass` (`â_k â_i âmomentumColT4 V k iâÂ² = â_x âV xâÂ²`, from Plancherel
   on `(â¤/n)â´` and the fact that each transfer is hit `nâ´` times), and
   `momentumColT4_chain_hs_mass` carries it to a chain of coincident-point factors.  So the four-torus
   chain now has an actual HilbertâSchmidt bound and not only a form identity.

   The frontier of Â§11 is the frontier of the *weight*, not the ladder's sharp constant, and that
   distinction is now a theorem instead of a caveat.  `ladder_form_norm_le_of_ratio` gives the
   ladder-level bound at **every** ratio `a > 0`, `âqâ â¤ aÂ·Q + (Î£áµ¢ Aáµ¢Â²/(4a))Â·âxâÂ²`, and it is a
   dilation: `ladder_form_norm_le` applied to the field strength `A/(2a)` (linearity in `A` is
   `magShiftTerm_smul`, `magCutoffKernel_smul`, `ladder_form_smul`) and multiplied by `2a`.  So the
   curve `(a, S/(4a))` of `amgm_min_shift` is one theorem plus a rescaling, and `a = 1/2` is just
   the `a = 1/2` point of it.  The ladder's actual sharp shift at ratio `a` is smaller, and the
   smallest section where this shows is two modes: `Î´_n` and `Î´_{n+eáµ¢}` with the other occupations
   zero, where `Q = dÎ±Â² + (d+1)Î²Â²`, the form is `2Aáµ¢Î±Î²`, and the sharp constant is the top of a
   `2 Ã 2` problem, `twoModeShift A a d = â(AÂ² + aÂ²/4) â a(2d+1)/2` (`twoModeShift_key` its
   determinant identity, `twoModeShift_le` the bound, `twoModeRatio_shift` attainment at
   `(Î±, Î²) = (A, ad + Î³)`).  At `A = 1`, `a = 1/2`, `d = 1` that is `(â17 â 3)/4 â 0.2808` against
   the termwise `AÂ²/(4a) = 1/2`, so the sum over directions does beat the sum of the termwise
   bounds: `S/(4a)` is the least *termwise* shift, not the global constant.  The comparison is now
   a theorem with no hypothesis on `A`: `twoModeShift_lt_termwise` proves
   `twoModeShift A a d < AÂ²/(4a)` for every `d â¥ 1` and `a > 0`, because
   `â(AÂ² + aÂ²/4) â¤ AÂ²/(4a) + 3a/2` is strict â the gap is
   `((AÂ² â 2aÂ²)Â² + 28aâ´)/(16aÂ²)` after clearing the positive denominator â and
   `a(2d+1)/2 â¥ 3a/2`.  Since `twoModeShift` is decreasing in `d` (`a > 0`), the bound holds for
   every dimension, not only the smallest sector, so the improvement over the termwise bound is
   uniform in `d`.

   **The global constant on `Q(N^{1/2})`: what the two-mode optimum is, and what it is not
   (2026-11-04).**  Â§11.2 of `YangMillsFormClosureNonDiagonal` splits the question instead of
   leaving it open, and the split is a theorem.  The ladder form is a sum over directions,
   `q(x) = âáµ¢ qáµ¢(x)` with `qáµ¢(x) = ââ Aáµ¢â(náµ¢+1) conj(x(n+eáµ¢)) x n` (`ladderDirForm`,
   `ladder_form_eq_sum_dir`), and so is the reference form `Q = âáµ¢ Qáµ¢`, `Qáµ¢ = ââ (náµ¢+1)âx nâÂ²`
   (`dirWeight`); each `qáµ¢` sees only the `i`-th occupation, the other coordinates merely slice it.
   Hence **`ladder_form_le_of_directional`**: any family of directional bounds
   `âqáµ¢â â¤ a Qáµ¢ + Sáµ¢âÂ·âÂ²` yields `âqâ â¤ a Q + (âáµ¢ Sáµ¢)âÂ·âÂ²`.  So the multidirectional constant â
   the "global constant on `Q(N^{1/2})`" â is **at most the sum of the directional constants**, and
   no improvement can come from the coupling of directions.  The termwise family
   `Sáµ¢ = Aáµ¢Â²/(4a)` is admissible (`ladderDirForm_norm_le`), which is exactly why Â§10's AMâGM bound
   is the `âáµ¢` of the directional shifts; and no admissible directional constant lies below the
   two-mode optimum (**`twoModeShift_le_of_twoModeBound`**: the kernel vector of
   `twoModeRatio_shift` is a directional state, `Qáµ¢ = Î±Â² + 2Î²Â²`, form `Aáµ¢Î±Î²`, i.e. `A = Aáµ¢/2`,
   `d = 1` in Â§11's normalization).  With `twoModeShift_lt_termwise` the directional constant is
   therefore sandwiched, for every `d`,
   `twoModeShift (Aáµ¢/2) a 1 â¤ Sáµ¢ < Aáµ¢Â²/(4a)`,
   and the sum of those gives the corresponding bracket for the whole form.  What the two-mode
   optimum is *not* is the global constant, and the reason is again exact rather than a caveat: the
   sharp `Sáµ¢` is the top of the **ray** problem `â(n+1)x_{n+1}x_n` against `a(n+1)x_nÂ²`, which
   carries no ambient dimension, no cut-off and no other coordinate.  That question is now answered
   (2026-11-04): `YangMillsFormClosureNonDiagonal` Â§11.3 proves the ray constant is
   **`BÂ²/(4a) â a`** â one mass unit below the termwise `BÂ²/(4a)`, because the shift `Î± = B/(2a)`
   removes exactly one mass unit from the occupation form and `a` is what one mass unit costs â and
   that it is sharp (`rayForm_le_sharp`, `ray_form_bound_iff`): the truncated Poisson vectors
   `Î±^m/â(m!)` satisfy the recurrence `â(m+1)u_{m+1} = Î±u_m` term by term, so the sum of squares
   vanishes and only `(BÂ²/(4a))u_NÂ²` is left uncovered, which is `o(âuâÂ²)`.  Hence
   `twoModeShift (Aáµ¢/2) a 1 â¤ Sáµ¢ â¤ Aáµ¢Â²/(4a) â a`, and the global constant is at most
   `âáµ¢ (Aáµ¢Â²/(4a) â a)`.  The transfer to the box is Â§11.4 of the same file: charging every raised
   edge to its head reindexes `Î£_{náµ¢+1<Î}(náµ¢+1)âx(n+eáµ¢)âÂ²` as `Î£_m máµ¢âx mâÂ² = Qáµ¢ â âxâÂ²`
   (`raiseWeightSum_eq`, `dirWeight_sub_mass`), which is where the single mass unit comes from, so
   the directional bound holds with `Sáµ¢ = Aáµ¢Â²/(4a) â a` (`ladderDirForm_norm_le_ray`) and the global
   one with `âáµ¢ (Aáµ¢Â²/(4a) â a)` (`ladder_form_norm_le_ray`).

What Phase 1 does **not** need, and what the plan does not ask of it: any statement about the
*interacting* theory or about the existence of a mass gap.  Those remain Phases 4â5, and the
separation `Î²â â Î¸â â¥ câÎ_ref` is still an input there (see the status of Phase 4).

---

### Phase 2: Quantum Channel Taming (The B. Simon Mechanism)

#### 2.1. Analytical Principle
For non-Abelian gauge models, classical flat directions do **not** imply a continuous spectrum in quantum mechanics. 
* By **Barry Simonâs Theorem** (*Some Quantum Mechanical Problems with a Clean Spectrum*, 1983), potentials of the form $V(x, y) = x^2 y^2$ on $L^2(\mathbb{R}^2)$ have **purely discrete spectrum** despite the infinite cross-shaped valleys along the $x$- and $y$-axes.
* **Physical Mechanism:** As $|x| \to \infty$ along a valley, the transverse potential $V_x(y) = x^2 y^2$ becomes an oscillator in $y$ with frequency $\omega(x) = |x|$. By the Heisenberg uncertainty principle, the zero-point energy of the transverse motion is:
  $$E_0(x) = \frac{1}{2} \hbar \omega(x) = \frac{1}{2} g |x| \xrightarrow{|x| \to \infty} \infty$$
* The "cross-sectional width" of the valley shrinks so rapidly ($w(x) \sim 1/\sqrt{g|x|}$) that quantum wave-packets cannot penetrate deeply into the valley without paying an infinite kinetic energy penalty.

#### 2.2. Mathematical Formulation for $SU(N)$ Field Space
**Correction (2026-11-08):** items 2â4 below are the original channel ansatz, not a proved
global inequality for `magPoly`. In particular the derivative/commutator cross term
prevents dropping the derivative piece from the square. S1 specifies the missing
localization, root-chart and error estimates.

For YangâMills on the product Hermite core $L^2(\mathbb{R}^{d_N})$:
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
  carries the Cartan/root split of the degree form of `BookProof.YangMillsFormDomination` â
  `parallelDegree` (the Cartan occupation `N` of a multi-index), `perpDegree`, `rootCount`, with
  `parallelDegree_add_perpDegree` splitting `â i, náµ¢` â and Simon's barrier at one root mode:
  `zeroPoint g N = Â½ g â(N + Â½) = transFreq/2`.  The mechanism's content is the growth, and that
  is proved: `zeroPoint_nonneg`, `zeroPoint_lt` (strictly increasing in the background) and
  **`zeroPoint_coercive`** â for every target `M` there is `K` with `M â¤ zeroPoint g N` for all
  `N â¥ K`.  On the field side this is `effPotential T g N = rootCount Â· zeroPoint g N` and
  **`simon_valley_lifted`**: with at least one root direction and `g > 0`, the effective energy
  along the Cartan valley exceeds any bound, so the valley is confined.  In its original
  two-dimensional form the model `simonPotential g x y = gÂ²xÂ²yÂ²` has an *exactly* flat valley
  (`simonPotential_flat`) whose effective energy `simonEffective g x = zeroPoint g |x|` is coercive
  (`simonEffective_coercive`) â Simon's theorem's phenomenon, without its discreteness conclusion.
  The barrier is sublinear (`sqrt_le_add_quarter`, `zeroPoint_le_linear`: `âx â¤ x + Â¼`), which is
  why it never competes with the kinetic term, and the transverse/longitudinal trade-off is
  `two_mul_sqrt_le`.  On the core the barrier is the quadratic form `barrierForm` (nonnegative for
  `g â¥ 0`, `barrierForm_zero_g` at zero coupling).
  The coupling is not a free parameter here: the quartic `:NÂ²:` interaction contains the Cartan/root
  cross term `2 N_â¥ N_â¥` (`crossDegreeForm`, and `quarticDegreeForm_ge_crossDegreeForm` proves the
  quartic form dominates it), which at background occupation `N` is an oscillator of frequency
  `â(2N + 1)` (`transFreq_sqrt_two`); with `g = â2` the barrier is exactly its zero-point energy
  (`zeroPoint_sqrt_two`).  So `zeroPoint (â2)` â not an arbitrary `g` â is the barrier the magnetic
  potential itself produces, which is what Â§2.2 item 2 (`Â½gÂ²ââ[A_j,A_k]âÂ²`) asserts.
  The Â§2.3 inequality is packaged as the structure `IsBarrierBound T g q`
  (`q â¥ degreeForm + barrierForm â CâÂ·âÂ²` on the Gaussâpolynomial core); `formDomination_of_barrier`
  turns it into the Phase-4 `FormDomination` certificate (ratio `câ`, shift `câÎ¼â + C`), and
  `barrier_gap` gives the separation `câ Î_ref` with the barrier included.

  **The inequality now holds for the YangâMills form `q_W` itself** (2026-10-30) â
  `BookProof.YangMillsMagneticQuartic` (`BookProof/YangMillsMagneticQuartic.lean`, no `sorry`).
  The magnetic energy of the field strength is, per mode, the sum of the squares of its components,
  `q_mag(c) = â_n (â_a B_a(n)Â²)âc nâÂ²` with `B_a(n) = â_i A_{a i} náµ¢` (`magComp`,
  `magneticEnergyForm`); in the canonical Cartan basis the components are the occupations
  themselves (`magComp_diag`).  CauchyâSchwarz and `0 â¤ B_a â¤ N` give the two comparisons with the
  normal-ordered `:NÂ²:` form,
  `quarticDegreeForm c â¤ d Â· q_mag(c)` (`quarticDegreeForm_le_magnetic`) and
  `q_mag(c) â¤ d Â· quarticDegreeForm c` (`magnetic_le_quartic`), i.e. the magnetic form *is* the
  quartic `:NÂ²:` form up to the explicit factor `card`.  Since `q_W = degreeForm + q_NÂ² + barrier`
  on the core, `barrierBound_quartic` transfers to `q_W`: **`barrierBound_yangMillsForm`** is
  `IsBarrierBound T g (yangMillsForm T g)` with the *same* explicit shift `C = K + (1 + K)Â²/4`,
  `K = rootCount T Â· g/2`, and **`yangMillsForm_certifiedGap`** is the Â§4.1 separation
  `câ Î_ref âcâÂ² â¤ q_W(c) + CâcâÂ²` on the vacuum-orthogonal sector.  So the interface is
  inhabited by `q_W` itself, not by a model of its interaction.  What remains is deriving the
  components `B_a` from the concrete potential (the `âA + g[A,A]` normal ordering of
  `ChapterFockInteractionStability`) and the root-mode normal form; the form comparison no longer
  depends on either.

  **The Cartan components `B_a` are now derived, not assumed** (2026-10-30) â
  `BookProof.YangMillsFieldStrength` (`BookProof/YangMillsFieldStrength.lean`, no `sorry`).  The
  potential component is a *nested pair* `câ  diag(A_a) c` â an outer creationâannihilation pair
  with the inner self-adjoint operator in between (`sandwich`).  **No normal ordering is needed**:
  the nested algebra multiplies pairs by composing the inner operators, so the contraction of
  Wick's theorem *is* the inner matrix product and the double-creation term is not in the algebra;
  and the one constant that could hide â the `+1` distinguishing `c câ ` from `câ c` â is absent,
  since **`hopWord_pair_same`** shows the ordered pair acts on `n` by exactly `n_j`, with no
  constant term.  Consequently **`sandwich_diag_single`** gives the diagonal pair's eigenvalue
  `â j, m_j n_j` and **`sandwich_diag_magComp`** gives `B_a(n) = magComp A a n`; the energy form
  `Â½ â_a B_aÂ²` is `magneticEnergyForm` read componentwise (`magneticEnergyForm_eq_sum`).

  **The assembly `F = âA + g[A,A]` and the root sector are now done, on the corpus's own
  operator** (2026-10-30) â `BookProof.Qym.ChapterYangMillsFieldStrengthSplit`
  (`BookProof/Qym/ChapterYangMillsFieldStrengthSplit.lean`, no `sorry`), which works with the
  field strength already in the repository rather than a model of it: `magPoly` of
  `BookProof.YangMillsHermite` (`B_{ia} = Îµ_{ijk}(â_j A_{k,a} + f_{abc}A_{j,b}A_{k,c})` on the
  Gaussâpolynomial core of `LÂ²(ââ¹â¹)`, the `B` of `ymHamiltonian`) and the same shape in
  `BookProof.Sm.ChapterSmHamiltonian` (`smMagG`, `smMagW`, `smMagB` with the coupling `g_s`
  explicit).  Results: **`magPoly_eq_deriv_add`** splits it into `magDeriv` (linear in the
  configuration) plus `magComm` (the `g[A,A]` term); **`magOps_apply_eq`** is the same identity for
  the operators on the core, and both halves are symmetric (`magOpsDeriv_symmetricOn`,
  `magOpsComm_symmetricOn`) since both have real coefficients; **`two_smul_levi_contract`** shows
  the `Îµ`-contraction of *any* bilinear form is the contraction of its antisymmetrisation, so the
  non-abelian term is `Â½ Îµ_{ijk}[A_j,A_k]` and **`magComm_eq_zero_of_symmetric`** kills it on the
  commuting (Cartan) sector â which is exactly why the components there are the *linear* forms
  `magComp`.  Off the Cartan directions the root sector is quartic: in the `su(2)` root plane
  `[aâEâ + bâEâ, aâEâ + bâEâ] = (aâbâ â bâaâ)H` (**`rootField_commutator`**) and the magnetic
  energy of that component is the **square** of the root determinant, `Â½â[Aâ,Aâ]âÂ² =
  âaâbâ â bâaââÂ²` (`root_energy`, `root_energy_real`), zero exactly on parallel amplitudes
  (`root_energy_eq_zero_iff`) and equal to `4 (Im(aâ\bar aâ))Â²` for hermitian fields
  (`root_energy_hermitian`).  And the reason no normal ordering arises in the potential is
  explicit: multiplication operators compose exactly, `mulOp (p * q) = mulOp p â mulOp q`
  (`mulOp_mul`), so the quartic `A_{j,b}A_{k,c}` needs no Weyl symmetrisation â unlike the `ÏA`
  cross terms, where `[A_j, Ï_j] = i`.  Not claimed: that a general `f_{abc}` decomposes into
  `su(2)` root blocks, or any dynamical statement.

  **The split is carried to the Standard Model field strengths of record** (2026-10-30) â
  `BookProof.Sm.ChapterSmFieldStrengthSplit` (`BookProof/Sm/ChapterSmFieldStrengthSplit.lean`, no
  `sorry`), on `smMagG` (gluons, `f_{abc}` with `g_s`) and `smMagW` (weak bosons, `Îµ_{mbd}` with
  `g`) â the `B`'s that enter `smHamiltonian = Â½ Î£ ÏÂ² + Â½ Î£ BÂ²`.  **`smMagG_eq_deriv_add`** and
  **`smMagW_eq_deriv_add`** split each into `smDerivG`/`smDerivW` (linear) plus
  `smCommG`/`smCommW` (the `g[A,A]` term).  Each half has real coefficients
  (`realCoeff_smDerivG`, `realCoeff_smCommG`, and the `W` pair), so each is a *symmetric
  multiplication operator* on the Gaussâpolynomial core (`smDerivG_symmetricOn`,
  `smCommG_symmetricOn`, `smDerivW_symmetricOn`, `smCommW_symmetricOn`), and the split is an
  identity of operators, not only of polynomials (`smFieldG_apply_eq`, `smFieldW_apply_eq`).
  `two_smul_levi_contract` is proved for the lattice dimension of the Standard Model as well, so
  **`smCommG_eq_quarter_bracket`** / **`smCommW_eq_quarter_bracket`** identify the non-abelian
  terms as `Â¼ Îµ_{ijk} g [A_j,A_k]` â the outer `Â½` is the one in the definition of `B`, the inner
  one comes from antisymmetrising the `Îµ`-contraction â and
  **`smCommG_eq_zero_of_symmetric`** / **`smCommW_eq_zero_of_symmetric`** kill them on the
  commuting (Cartan) sector, where the field strength is the derivative part alone.  Left as they
  are: the hypercharge `smMagB` (abelian, already linear, no commutator part) and the Higgs
  covariant derivative `smCovD` (a bilinear form whose non-abelian structure is the generator
  action `tgen`/`ygen` on the doublet, a multiplication by given matrices, needing no bracket
  identity).  The fermions are not part of `smHamiltonian`, so they play no role here either.

  **But the Â§2.3 inequality is now proved unconditionally for the quartic `:NÂ²:` form**
  (2026-10-30) â the form the magnetic potential itself produces (see the cross-term computation
  above).  `barrierForm_le_linear` bounds the barrier linearly in the occupation
  (`rootCountÂ·zeroPoint g N â¤ K (N+1)`, `K = rootCountÂ·g/2`, from `zeroPoint_le_linear`), and
  **`barrierBound_quartic`** (`BookProof/YangMillsEffectiveBarrier` Â§6) is the instance
  `IsBarrierBound T g (quarticDegreeForm)` with the explicit shift `C = K + (1 + K)Â²/4`: the quartic
  grows like `NÂ²` and pays for the kinetic degree form *and* the `âN` barrier at once.  Through the
  existing chain this gives `quarticFormDomination` (a `FormDomination` for the pure interaction
  form, ratio `câ`, shift `câÎ¼â + C`) and **`quartic_certified_gap`**: on the vacuum-orthogonal
  sector `câ Î_ref Â· âcâÂ² â¤ q_NÂ²(c) + CâcâÂ²`.  So in the `:NÂ²:` model the separation `câ Î_ref` no
  longer depends on the unproved estimate; what remains is the identification `q_W = q_NÂ²` itself.
  Nothing here claims a discrete spectrum for `H_W`.

---

### Phase 3: Construction of a Solvable Gapped Reference Operator $H_{\text{ref}}$

Rather than attempting to calculate the spectrum of $H_W$ exactly, construct a reference operator $H_{\text{ref}}$ that satisfies three conditions:
1. It is explicitly solvable on the product Hermite core (e.g., an anisotropic harmonic oscillator or a radially symmetric gapped system).
2. Its eigenvalues and spectral gaps are known in closed form:
   $$\sigma(H_{\text{ref}}) = \{\mu_0, \mu_1, \mu_2, \dots\}, \quad \mu_1 - \mu_0 \ge \Delta_{\text{ref}} > 0$$
3. It lower-bounds $H_W$ at the quadratic-form level.

#### 3.1. Construction of $H_{\text{ref}}$
On the $d_N$-dimensional Gaussâpolynomial core (PDF Ch. 27.9, where $d_3 = 99$ for $SU(3)$):
$$H_{\text{ref}} = \sum_{k=1}^{d_N} \left( -\frac{\partial^2}{\partial x_k^2} + \omega_k^2 x_k^2 \right) + V_0(P)$$
where:
* $\omega_k > 0$ are the harmonic frequencies of the background Gaussian measure (`PhysHSGaussian`).
* $V_0(P)$ is a parity/charge projection that assigns energy $0$ to the vacuum state $\Omega$ and energy at least $\Delta_{\text{ref}} = \min_k \omega_k$ to any state orthogonal to $\Omega$ (or odd under parity).

#### 3.2. Milestone 3: Closed-Form Spectrum of $H_{\text{ref}}$
* **Task:** Formalize the spectrum of $H_{\text{ref}}$ in Lean 4 using the existing harmonic oscillator theorems (`BookProof.HarmonicOscillator.harmonicOscOp`):
  ```lean
  theorem href_spectral_gap (k : â) :
    â Ï â D(H_ref), Ï â¥ Î© â â¨Ï, H_ref Ïâ© â¥ (Î¼â + Î_ref) âÏâÂ²
  ```
* **Deliverable:** `BookProof.ChapterReferenceGap.lean`.
* **Status (2026-10-30): DONE**, `BookProof.ReferenceGap` (`BookProof/ChapterReferenceGap.lean`, no `sorry`).
  The `d`-dimensional symbol `refEnergy Ï n = â i, Ïáµ¢ (náµ¢ + Â½)` is a port of physlib's
  `QuantumMechanics.HarmonicOscillator.eigenEnergy` (`â = 1`, general `Ï`) together with
  `refEnergy_strictMono`; at `d = 1`, `Ï = 1` it is this repository's `harmonicSymbol`
  (`refEnergy_one_eq_harmonicSymbol`), so it sits on `harmonicOscOp`.  The gap is
  `refGap Ï = min_k Ï_k`, positive and attained (`refGap_pos`, `exists_refGap_eq`), and every
  excited level clears the vacuum by it (`refEnergy_ge_vacuum_add_gap`).  On the
  Gaussâpolynomial core (finite coefficient families `(Fin d â â) ââ â`) the milestone is
  `href_spectral_gap` with `coreNormSq`/`coreForm` as `âÏâÂ²` and `â¨Ï, H_ref Ïâ©`, the parity
  sector is `href_spectral_gap_of_parity`, and the bound is attained at the vacuum
  (`coreForm_vacuum`), so `Î_ref` is the exact gap there.  Not done here: the `LÂ²` closure
  of the core (basis expansion/summability) and the Phase-4 form domination.

---

### Phase 4: Relative Form Bounding in Lean 4

Once $H_{\text{ref}}$ is constructed, the analytical lower bound on the separation $\beta_\infty$ is derived by proving that $H_W$ dominates $H_{\text{ref}}$ in the sense of quadratic forms.

#### 4.1. The Form-Domination Inequality
Prove that there exist constants $c_1 > 0$ and $c_2 \in \mathbb{R}$ such that on the common core $\mathcal{D}$:
$$q_{H_W}(\psi) \ge c_1 \, q_{H_{\text{ref}}}(\psi) - c_2 \|\psi\|^2 \quad \forall \psi \in \mathcal{D}$$

By the variational minimax principle (CourantâFischer):
* Ground state: $\lambda_0(H_W) \ge c_1 \mu_0 - c_2$.
* First excited state (or lowest state in the orthogonal/odd sector): 
  $$\lambda_1(H_W) \ge c_1 \mu_1 - c_2$$
* **Correction (2026-11-08): these two lower bounds cannot be subtracted.** With an
  independent ground upper bound $\lambda_0(H_W)\le U_0$, minâmax instead gives
  $$\lambda_1(H_W)-\lambda_0(H_W)\ge c_1\mu_1-c_2-U_0.$$
  This is useful only when its right-hand side is positive and the relevant minâmax
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
    â (câ : â) (câ : â), câ > 0 â§
    â Ï â D_core, quadForm H_W Ï â¥ câ * quadForm H_ref Ï - câ * âÏâÂ²
  ```
* **Deliverable:** `BookProof.YangMillsFormDomination.lean`.* **Status (2026-11-04): the implication, the domination inequality on the Gaussâpolynomial core,
 the `LÂ²` closure of that core, the FarisâLavine comparison for a non-diagonal interaction, and
 the `LÂ²` lift of the *interacting* form â its bottom bound *and* its FarisâLavine comparison
 with relative bound `a < 1`, on the form domain â are DONE** (`BookProof.YangMillsFormClosure`,
 `BookProof.YangMillsFormClosureNonDiagonal`); what remains open is the *uniformity in the
 cut-off* of the HilbertâSchmidt / relative bound, as described at the end of this item.
  `BookProof.YangMillsFormDomination` (`BookProof/YangMillsFormDomination.lean`, no `sorry`)
  carries the certificate as a structure, `FormDomination Ï q` = ratio `câ > 0`, shift `câ`, and
  `â c, câ Â· coreForm Ï c â câ Â· coreNormSq c â¤ q c` on the Phase-3 core.
  `coreForm_ge_vacuum` puts the vacuum at the bottom of the reference form, so domination also
  bounds the ground level: `ground_bound` gives `câÎ¼â â câ`, `excited_bound`
  (`c 0 = 0`) gives `câ(Î¼â + Î_ref) â câ`, and `certified_separation`/`certified_gap_pos` show
  the difference is exactly `câ Î_ref > 0` â the uniform separation `Î²_â â Î¸_â`.  The certificate
  is inhabited (`formDomination_self`, `q_ref` dominates itself), so the structure is not
  vacuous.  A **concrete, non-self-referential inhabitant** is `freeFormDomination`: the free
  (quadratic) part's form on the Hermite core â the *degree* form
  `degreeForm c = â n, (â i, náµ¢)âc nâÂ²`, i.e. the form of `âÎ` in oscillator units â dominates
  the reference form with ratio `câ` and shift `câ = câÎ¼â` whenever `0 < câ` and `câÏáµ¢ â¤ 1`
  (`scaled_refEnergy_sub_zero_le_degree` is the pointwise inequality; `exists_free_ratio`
  shows such a `câ` always exists).  That instance yields a concrete gap:
  `degreeForm_ge_gap` â on the vacuum-orthogonal sector the kinetic form is at least
  `câÎ_ref Â· âcâÂ²`.  The **interacting (quartic) part** enters through monotonicity, not through a
  new estimate: the magnetic term is a sum of squares, so its form is nonnegative, and
  `FormDomination.mono` (a certificate for `q` is one for any `q' â¥ q`) shows it cannot spoil the
  comparison â `interactingFormDomination` is the certificate for
  `degreeForm + quarticDegreeForm` (`quarticDegreeForm` is the normal-ordered `:NÂ²:` quartic),
  and `interactingForm_ge_gap` keeps the gap.  The YangâMills form itself is the last piece, and it
  is supplied by Phase 2, not by a new estimate: `yangMillsFormDomination`
  (`BookProof/YangMillsMagneticQuartic.lean`, the section âThe consequence for `q_W`â) is the certificate
  `BookProof.YangMillsFormDomination.FormDomination Ï (yangMillsForm T g)` with ratio `câ` and shift
  `câ = câÎ¼â + quarticShift T g`, `quarticShift T g = K + (1 + K)Â²/4`, `K = rootCount T Â· g/2`, so
  the plan's `ym_form_dominates_href` is inhabited by the YangâMills form of record and not by a
  model of it.
  The route that produces it is Phase 2: `BookProof.YangMillsEffectiveBarrier.formDomination_of_barrier`
  shows that a bound `q_W â¥ degreeForm + barrierForm â CâÂ·âÂ²` (`IsBarrierBound`, the Â§2.3 milestone
  with Simon's zero-point barrier included) already yields the certificate, with shift `câÎ¼â + C`,
  and `barrier_gap` then gives the same `câ Î_ref` separation.  So the remaining inequality may be
  taken in either form; the barrier version is the one the physics argument naturally produces,
  and it is now *proved* for the quartic `:NÂ²:` form (`barrierBound_quartic`) **and for `q_W` itself**
  (`barrierBound_yangMillsForm`, Â§2.3 above), so neither the interface nor its `q_W` instance is an
  assumption any more; it also holds with shift `0` (`barrierBound_yangMillsForm_zeroShift`: the
  quartic form is nonnegative and sits in `q_W` beside both terms the inequality needs).

  **What the completed inequality does *not* depend on, and what is still open.**  The components
  are derived, not assumed: `B_a` is `magComp` read off the nested pair `câ  diag(A_a) c`
  (`sandwich_diag_magComp`, Â§2.3), `F = âA + g[A,A]` splits on the corpus's own `magPoly`
  (`magPoly_eq_deriv_add`, `magComm_eq_zero_of_symmetric`, and the `smMagG`/`smMagW` twins), and
  the root sector is quartic with energy `âaâbâ â bâaââÂ²` (`rootField_commutator`, `root_energy`,
  `root_energy_eq_zero_iff`) â so the field-strength components and the root-mode structure are not
  inputs of Â§4.3, and the inequality needs neither the unbounded charge of Phase 1 nor the
  perturbation theory of Â§4.2.  The **`LÂ²` closure of the Gaussâpolynomial core** â the step this
  paragraph used to name as open â is now proved in `BookProof.YangMillsFormClosure`
  (`BookProof/YangMillsFormClosure.lean`, no `sorry`).  `L2 d = âÂ²(Idx d, â)` receives the core by
  `coreEmbed` with `âcoreEmbed câÂ² = coreNormSq c` (`norm_sq_coreEmbed`) and dense range
  (`dense_range_coreEmbed`, from `lp.hasSum_single` and the truncations).  All forms of the
  chapter are diagonal in the multi-index, `diagonalForm f c = â n â c.support, f n âc nâÂ²`, and
  the closed form `closedForm f x = â' n, ofReal (f n) Â· ofReal (âx nâÂ²)` is *the closure of the
  core form*: it extends it (`closedForm_coreEmbed`), it is lower semicontinuous
  (`lowerSemicontinuous_closedForm`), and it is the supremum of the core forms of the truncations
  (`closedForm_eq_iSup_truncate`).  Domination transfers with no loss: `formDomination_symbol`
  reads a certificate as the symbolwise inequality `câÎ¼(n) â câ â¤ g(n)`, and
  `formDomination_closed` gives
  `ofReal câ Â· closedForm Î¼ x â¤ closedForm g x + ofReal (max câ 0) Â· closedNormSq x` for every
  `x : LÂ²`.  The form of record is covered: `yangMillsForm T g` is diagonal
  (`Barrier.yangMillsForm_eq_diagonalForm`), so `yangMillsForm_closed` transfers its certificate
  and `closed_yangMillsGap` gives the `câÎ_ref` separation on the whole vacuum-orthogonal sector
  of `LÂ²`.  What the closure still does not supply is the statement about the *spectrum* of `H_W`
  â discreteness and a mass gap need the self-adjoint operator, not only its closed form.

  **The non-diagonal interaction, on the core and on `LÂ²` (2026-11-04).**  The second half of that boundary â
  "not for a magnetic interaction mixing multi-indices" â is addressed in
  `BookProof.YangMillsFormClosureNonDiagonal` (`BookProof/YangMillsFormClosureNonDiagonal.lean`, no
  `sorry`), and by the *FarisâLavine* route rather than the termwise one.  The interaction is a
  kernel `K : (Fin d â â) â (Fin d â â) â â` with kernel form
  `kernelForm K c = â m â supp c, â n â supp c, Re(K m n Â· c n Â· conj(c m))`, which couples
  distinct multi-indices whenever `K` is off the diagonal â the magnetic terms the diagonal theory
  cannot see.  The form bound the interaction enters through is a **HilbertâSchmidt** one:
  `kernelForm_sq_le` is the two-index CauchyâSchwarz inequality (square of the absolute form â¤
  HilbertâSchmidt sum Ã `coreNormSqÂ²`), so a kernel whose finite-square sums are bounded by `ÏÂ²`
  obeys `abs_kernelForm_le_of_hs`: `|kernelForm K c| â¤ Ï Â· coreNormSq c` for **every** core state,
  with no support restriction.  `farisLavine_domination` is the comparison itself: if `q'`
  dominates the reference form with ratio `câ` and shift `câ`, and `|qK| â¤ a q' + bâÂ·âÂ²` with
  relative bound `a < 1`, then the **sum form** `q' + qK` dominates with ratio `(1 â a)câ > 0` and
  shift `(1 â a)câ + b` â the interaction may lower the form, and the factor `1 â a` is what that
  costs; the ratio never reaches zero, so the certified separation survives.  The bounded case is
  separate and sharper in the ratio: `farisLavine_of_bounded_interaction` (`a = 0`) keeps `câ`
  unchanged and adds only `b` to the shift.  A concrete, genuinely off-diagonal instance is
  `hoppingKernel mâ nâ` (the matrix unit at `(mâ, nâ)`): its HilbertâSchmidt sums are bounded by
  `1` (`hoppingKernel_sq_sum_le`), so `abs_hoppingForm_le` gives the form bound with `Ï = 1`, and
  **`hopping_farisLavine`** concludes that the YangâMills certificate plus the hopping interaction
  still dominates with the *same* ratio `câ` and shift `câ + 1`.  `hopping_couples` shows the
  interaction really does read a product of coefficients rather than moduli â at `aâ = bâ = 1` it is
  `1`, at `aâ = 1, bâ = i` it is `0`, although both states have the same coefficient moduli â so no
  diagonal form can represent it.  **The `LÂ²` lift of the interacting form is proved (2026-11-04)**:
  Â§5 of the same module defines `closedKernelForm K x` as the weighted double series over all of
  `Idx d Ã Idx d` (absolutely convergent for every `x : LÂ²`), bounds it by `ÏâxâÂ²` for the *same*
  `Ï` (`abs_closedKernelForm_le`, HÃ¶lder with exponents `2, 2`), identifies it with `kernelForm` on
  the core (`closedKernelForm_coreEmbed`), and proves the bottom bounds on the form domain:
  `closed_diagonal_add_kernelForm_ge` and `closed_sector_bottom_ge_interacting`.  So, *when the
  total HilbertâSchmidt mass is finite*, the off-diagonal interaction is a bounded form
  perturbation of the closed diagonal form â continuous, hence closed on the same domain â and
  Phase 5's bottom statements hold on `LÂ²`, not only on the core.  The **ratio** is carried over
  as well, in Â§6: `closed_farisLavine_domination` states `câ (closedForm Î¼ x).toReal â¤
  (closedForm g x).toReal + closedKernelForm K x + shifts` with the relative bound `a < 1` intact,
  the finiteness `closedForm g x â  â¤` being the only extra hypothesis.  **The cut-off uniformity is now
  proved on the box (2026-11-05).**  Â§11.4's ray decomposition gives the ladder the constant
  `Î£áµ¢ (Aáµ¢Â²/(4a) â a)` with the relative bound `a` *chosen* rather than measured, and Â§12.1 of the
  same module carries it to the cut-off: `sum_dirWeight_eq` identifies the sum of the directional
  reference forms with the degree symbol `Î£â (|n| + d)âx nâÂ²`, so `ladder_form_le_degree` bounds
  the ladder form by `a Â· degree + (Î£áµ¢ (Aáµ¢Â²/(4a) â a)) Â· mass`, and at `a = 1/2`
  (`ladder_form_le_degree_half`) the shift is `(Î£áµ¢ Aáµ¢Â²)/2 â d/2`.  **Neither constant mentions `Î`**,
  so the relative bound is uniformly bounded away from `1` and the HilbertâSchmidt branch â whose
  constant was `â(m_Î)`, of order `Î^{(d+1)/2}` â is no longer what the cut-off argument rests on.
  The `LÂ²` transfer is proved as well (Â§12.2 of the same
  module, 2026-11-05): `abs_closedKernelForm_boxKernel_le` bounds
  `closedKernelForm (boxKernel Î A) x` by `a Â· (closedForm degree x).toReal
  + max (Î£áµ¢ (Aáµ¢Â²/(4a) â a)) 0 Â· âxâÂ²`, and `closed_farisLavine_boxKernel` hands that bound to Â§6's
  `closed_farisLavine_domination`, so the ladder interaction enters the comparison at ratio
  `(1 â a)câ > 0` with `a â (0,1)` chosen and a shift free of `Î`.  **The cut-off uniformity of the
  relative bound is therefore closed end to end, on the closed form.**  So
  Phase 5's `câÎ_ref` is certified on the core for the off-diagonal case, and on `LÂ²` for the
  diagonal one at full strength â with the interacting term bounded below on `LÂ²` by `âÏâxâÂ²`,
  which preserves the *bottom* and not yet the *ratio* of the separation.

---

### Phase 5: Discharging Hypotheses in the Verification Pipeline

Assume an actual continuum spectral exclusion and positive Temple denominator have
been established analytically (S2âS3), rather than inferred from reference thresholds.
The formulas below require that additional input; they do not construct it.

#### 5.1. Supplying the Missing Input to Temple's Inequality
In `BookProof.ChapterRitzCertificate.lean`, replace the open hypothesis with the analytical bound:
$$\beta_\infty := \theta_\infty + c_1 \Delta_{\text{ref}}$$
The Temple denominator is now uniformly bounded away from zero for **all** approximation orders $n$:
$$\beta_n - \theta_n \ge \frac{1}{2} c_1 \Delta_{\text{ref}} > 0 \quad \forall n \ge n^*$$
Consequently, the Temple uncertainty:
$$\delta_n = \frac{\eta_n^2}{\beta_n - \theta_n} \le \frac{2 \eta_n^2}{c_1 \Delta_{\text{ref}}}$$
is strictly controlled. 

* **Status (2026-10-30): Â§5.1 is DONE; Â§5.2's arithmetic is DONE, its analytic transfer is not.**
  `BookProof.TempleSeparationBound` (`BookProof/Sirk/ChapterTempleSeparationBound.lean`) now carries
  the uniform residual bound: `temple_uncertainty_le_of_residual` proves Â§5.1's
  `Î´_n = Îµ_nÂ²/(Î²_n â Î¸_n) â¤ Îµ_nÂ²/c â¤ Î·_nÂ²/c` under `Î² â Î¸ â¥ c`, and
  `certified_edge_of_uniform_residual` is the certificate statement `Î¸ â Î·Â²/(câÎ_ref) â¤ l` with
  the analytic constant.  Â§5.2's displayed inequality is
  **`continuum_gap_unconditional`**: with `câ, Î_ref > 0`, a uniform residual `Î·_max` on the
  odd-sector vector and the variational upper bound `l_even â¤ Î¸_even`, the gap obeys
  `(Î¸_odd â Î¸_even) â 2Î·_maxÂ²/(câÎ_ref) â¤ l_odd â l_even`, and `continuum_gap_positive` shows it
  is strictly positive once the Ritz separation exceeds the correction â so the denominator no
  longer degrades with the order.  The transfer across the limit is in
  `BookProof.TempleContinuumGap` (`BookProof/Sirk/ChapterTempleContinuumGap.lean`): a spectral
  separation gives a *quantitative* gap at the window centre, `gapAt_of_separation`
  (`((Î²âl)/2)âxâ â¤ â(A â (l+Î²)/2)xâ`, from Pythagoras plus the Temple factor
  `factor_nonneg_of_separation`), at the plan's constant `gapAt_of_form_domination`
  (`câÎ_ref/2` at `l + câÎ_ref/2`), and by `SpectralGapStability.gapAt_of_tendsto` it survives an
  **operator-norm** limit unchanged (`gap_survives_norm_limit`), leaving a hole
  `câÎ_ref/2` in the limit's spectrum (`notMem_spectrum_of_separation_limit`,
  `continuum_gap_of_form_domination`).  The **strong-resolvent** mode of the same hypothesis is
  proved too (Â§6 of the chapter, 2026-10-31): `certifiedResolvent` is the left inverse of
  `A â Î»` the gap guarantees, with `certifiedResolvent_left` and `certifiedResolvent_norm`
  (`âRÎ¾â â¤ âÎ¾â/d`); `gap_survives_strongResolvent` turns **pointwise** convergence of those
  certified resolvents to a left inverse of `B â (l+b)/2` into `GapAt B ((l+b)/2) ((bâl)/2)`,
  **without** assuming the uniform bound (it is `certifiedResolvent_norm`, read off the
  separation), and `continuum_gap_of_form_domination_strongResolvent` is the same at the plan's
  constant `câÎ_ref/2`, together with the spectral hole
  (`notMem_spectrum_of_strongResolvent_limit`).  The uniform bound is therefore free in both modes;
  what is still conditional is the uniform `SpectralSeparation` at the analytic constant, as Â§5.1
  assumes, and the fact that the truncation family converges at all â in either mode.

#### 5.2. Transferring Across the Strong-Resolvent Limit
Because $H_n \to H_F$ strongly in the resolvent sense (`weyl_hashimoto_selects_friedrichs`), apply the strong-resolvent spectral theorem (derived from ReedâSimon VIII.24 as discussed in the previous section):
```lean
theorem continuum_gap_unconditional :
  gap(H_F) â¥ (Î¸_odd - Î¸_even) - (2 * Î·_maxÂ² / (câ * Î_ref)) > 0
```
**Correction (2026-11-08):** this is a historical schematic target, not an unconditional
continuum theorem. Its separation, residual, sector and limit hypotheses must be supplied.
The outer `dGamma` lift additionally needs a strictly positive absolute one-particle form
bound; an even/odd inner excitation gap alone does not supply it. See S2âS4.

* **Status (2026-10-31): the nested-Fock lift, the coincident-point product and both convergence
modes (operator-norm and strong-resolvent) are now proved; the analytic separation and the fact
that the truncations converge are not.**  `BookProof.TempleContinuumGap`
  (`BookProof/Sirk/ChapterTempleContinuumGap.lean`) Â§3â4 put the lift on the actual Timepiece
  structure rather than beside it:
  - *nested Fock space / number conservation.*  A separation `spec T â {l} âª [Î², â)` bounds the
    one-particle operator below (`sub_const_nonneg`, `form_gap_of_separation`), and
    `nestedFock_gap_of_separation` / `nestedFock_gap_of_certified_edge` lift it to the nested Fock
    space: `dÎ(opCol b A)` â built from `aâ _j a_k` only, hence outer-particle-conserving â
    annihilates the vacuum and has Fock gap `l` on every vacuum-orthogonal finite-occupation
    state.  At the plan's constant the same theorem also delivers the one-particle `GapAt` of
    Â§5.1, so the two sides meet in one statement.
  - *the same-point product of outer fields.*  The interaction is a polynomial in the fields, so
    its coefficients contain products at a coincident Euclidean point, where a product of
    distributions is ambiguous.  The formalism never forms it: `dft_samePointProduct` (the
    product-to-convolution theorem) makes the momentum transform of the same-point product the
    convolution `nâ»Â¹ Î£_p FÌ(p) Ä(kâp)`; `dft_mul_momentumCol` shows multiplication by a symbol is
    the momentum-transfer matrix `(k,i) â¦ nâ»Â¹VÌ(kâi)` â an ordinary number-preserving
    one-particle matrix; `momentumCol_samePointProduct` shows the coefficient of a product of two
    fields is itself the convolution `nâ»Â² Î£_{p+q=kâi} FÌ(p) Ä(q)`, every term carrying conserved
    momentum; `samePointProduct_form_eq_momentum` identifies the *form* the Phase-4 domination
    evaluates with that momentum convolution (Plancherel, `sum_conj_dft_mul_dft`); and
    `samePointProduct_real_self_form_nonneg` gives the positivity of the squared real field, i.e.
    the `IsPosCol`-shaped input the `dÎ` lift consumes.
  - *the strong-resolvent mode of the transfer.*  Both modes of Â§5.2's hypothesis are now proved:
    the operator-norm one (`gap_survives_norm_limit`) and the strong-resolvent one (Â§6:
    `gap_survives_strongResolvent`, `notMem_spectrum_of_strongResolvent_limit`,
    `continuum_gap_of_form_domination_strongResolvent`), the latter from pointwise convergence of
    the certified resolvents alone â strong-resolvent convergence is *weaker* than norm
    convergence, so this is the mode a truncation family actually delivers.
  - *the uniform separation at the operator level (2026-11-05).*  `BookProof.YangMillsFormClosureND`
    Â§13 now builds the operator the cut-off closed forms define: `diagCLM c hM` on `LÂ²`,
    self-adjoint (`diagCLM_isSelfAdjoint`), whose form on the cut-off `s` is exactly
    `diagonalForm c (truncate x s)` (`re_inner_diagCLM_cutoff`) â for a bounded symbol the form is
    closed as it stands, so its Friedrichs extension is the operator itself.  The minimax statement
    is proved pointwise, without any spectrum computation, because the Rayleigh quotients of a
    diagonal operator are the symbol values: a symbol that is `l` or at least `l + câÎ` everywhere
    gives `GapAt A (l + câÎ/2) (câÎ/2)` (`gapAt_diagCLM_of_symbol_separation`), and
    `cutoff_operator_uniform_gap` gives the cut-off family a self-adjoint operator with gap
    `câÎ/2` at `câÎ/2` whose constants do **not** involve the cut-off `s`.
    `cutoff_operator_interacting` adds a bounded self-adjoint interaction and loses exactly `âKâ`
    (the FarisâLavine step in the bounded mode).
  - *the convergence, and the gap of the limit (2026-11-05).*  Â§14 supplies the left end Â§5.2 was
    missing.  The cut-off family does **not** converge in operator norm â the symbol changes on an
    ever larger box, so `âA_s â Aâ` is governed by the symbol outside `s` â hence the mode is strong
    convergence.  `coordBox` is a monotone cofinal family of boxes, `tendsto_tail_coordBox` proves
    that the cut-off tail of a state vanishes (the partial sums over a cofinal family converge to
    the whole `â'`), `tendsto_diagCLM_cutoff` assembles the strong limit, and
    `gapAt_of_strong_tendsto` transfers a uniform `GapAt` because a lower bound valid at every
    approximant passes to the limit of norms.  The result is `gapAt_cutoffLimit` (`GapAt` at
    `câÎ/2`) and `notMem_spectrum_cutoffLimit` (the window centre is not in the spectrum), with no
    cut-off in the constants.  Â§15 then removes Â§13's global bound: `cutoffBound` bounds a cut-off
    of an unbounded symbol by a finite sum, so the Â§12.2 degree symbol enters the operator picture
    (`re_inner_diagCLM_cutoffSymbol`), and `gapAt_cutoffDegreeSymbol` reads its box gap `d/2`.
    Â§16 states KatoâRellich at a relative bound below one: `katoRellich_gap` turns
    `âK xâ â¤ aâA xâ + bâxâ` with `a < 1` into self-adjointness plus a gap
    `(1 â a)dd â (a|lam| + b)`, and `cutoffLimit_interacting` applies it to Â§14's limit.
  - *the limit operator, and the resolvent mode (2026-11-05).*  Â§17 constructs the operator the
    cut-offs are cut-offs *of*: multiplication by the unbounded symbol on the states with summable
    weighted squares.  It is symmetric on that domain, and its resolvent is a **bounded** operator
    (`âR Î¾â â¤ Î´â»Â¹âÎ¾â`) because `(c n â lam)â»Â¹` is bounded once the symbol keeps its distance from
    `lam`; both inverse identities hold, so the gap holds on the domain and the degree symbol's
    operator is gapped by `d/2` at `d/2` â the same constant as the box gaps of Â§15.  Â§18 then
    discharges Â§5.2's hypothesis *literally*: the cut-off resolvents are the reciprocal-symbol
    operators, they converge pointwise to the limit resolvent (the symbols agree on the box and are
    both bounded off it), and with the limit's left inverse the strong-resolvent transfer lemma
    yields the gap and the spectral hole with **no hypothesis remaining**.  The same convergence
    holds for the degree cut-offs, whose limit is the unbounded resolvent.
  - *self-adjointness of the unbounded operator (2026-11-05).*  Â§19 supplies what Â§17 left open, and
    it does so by **FarisâLavine**, not by a Friedrichs form: the criterion needs a positive `N` on
    the same domain and a commutator bound, and no closability or semiboundedness of a form.  The
    symbol is real, so `N = T` makes the commutator form vanish identically and the bound hold with
    constant `0`; the two hypotheses that remain are the paper's â the form is nonnegative (where
    the symbol is assumed nonnegative) and `T + 1` is onto (the resolvent at `â1` in disguise, the
    reciprocal of `c n + 1` being bounded by `1`).  The conclusion is trivial deficiency, hence a
    self-adjoint operator on a domain containing the operator's own domain and agreeing with it
    there; the finite-support states are dense, so the extension theory applies.  The degree
    symbol's operator is the instance.
  - *the spectrum of the unbounded symbol (2026-11-05).*  Â§20 needs no extension theory: the
    diagonal operator is self-adjoint on its **maximal** domain.  Testing the representing identity
    of the adjoint domain against coordinate vectors reads off `c n Â· Ï n = Î· n`, so the adjoint
    domain sits inside the domain (`memDom_of_mem_adjointDomain`) and, by Â§17's symmetry, equals it:
    `adjointDomain_diagSubLin`.  The bundled `UnboundedSelfAdjoint` `diagUnbSelfAdjoint` is then the
    input of the workspace's unbounded spectral theorem â `unbounded_multiplication_model_general`
    of `BookProof.ChapterUnboundedSpectralModel`, the Cayley route â applied as
    `diagUnb_multiplication_model`.  The concrete spectral statement is elementary and exact:
    `InResolventSet` (bounded two-sided invertibility of `T â lam`) is equivalent to a positive
    distance between `lam` and the symbol's range (`inResolventSet_iff_exists_gap`), so the spectrum
    is the **closure of the range of the symbol** (`closure_range_eq_compl_resolvent`).
  - *formâoperator, the YangâMills operator, and KÃ¤llÃ©nâLehmann (2026-11-05).*  Â§21 supplies the
    step Â§5âÂ§6 recorded as missing: for a bounded symmetric perturbation the sum form
    `q_c + q_K` **is** the quadratic form of the self-adjoint operator `T + K` on the maximal
    domain (`diagSumLin_isSelfAdjointOn`, `re_inner_diagSum`), its form domain `â |c n| âx nâÂ² < â`
    contains the operator domain and is dense, and the lower bound `Î¸ â Ï` is read off on it.  Â§22
    then identifies the YangâMills one-particle operator: the form of record is diagonal, its symbol
    is `N + NÂ² + rootCountÂ·zeroPoint` in the occupation, and the closed form of that symbol *is*
    `q_W` on the core and the quadratic form of `diagUnb` of it on the domain â so the operator is
    the diagonal one, not an abstract `T` the form merely dominates.  Its spectrum is
    `{B} âª [B + 2, â)` with `B = rootCountÂ·g/(2â2)` the vacuum barrier: **the gap above the vacuum
    is exactly `2`**, and the barrier shifts the spectrum without changing the spacing.  `OSReconstruction.Clustering` Â§6 closes
    the KÃ¤llÃ©nâLehmann direction for atomic spectral measures â masses above `m` decay the
    two-point function at rate `m` with the sharp constant, and decay at rate `m` forces every
    positively weighted mass to be at least `m`, so the rate *is* the bottom of the mass spectrum â
    and turns such a representation of the connected correlators into `SchwingerClustering`.
  - *KatoâRellich at `a < 1`, non-atomic KÃ¤llÃ©nâLehmann, and the reduced sector (2026-11-05).*
    `BookProof.YangMillsFormKLMN` Â§23 proves the **KLMN theorem at form level** for diagonal forms:
    the form norm is finite exactly on `formDom` (`formENN_ne_top_iff`), it is lower semicontinuous
    in `LÂ²` (`formENN_le_of_tendsto`, `formTsum_lsc`, `formDom_of_tendsto` â Fatou on the monotone
    partial sums of the sign-free series), the sum form's domain is the *unperturbed* one whenever
    `|b n| â¤ a c n + Î²` with `a < 1` (`formDom_add_of_relativeBound`,
    `formDom_of_relativeBound_add`), it is bounded below by `(1 â a)Î¸ â Î²` on that domain
    (`formSum_ge_formDom`), and it is the quadratic form of the self-adjoint `diagUnb (c + b)`
    (`klmn_selfAdjoint`, `klmn_form_eq_inner`, `klmn`).  So the branch the continuum needs is a
    theorem about the form, not a hypothesis.  Â§24 identifies the **reduced sector's magnetic
    slot** with Â§22's diagonal one: the transverse sector is invariant under the diagonal operator
    (`diagUnb_mem_reducedSector` â no coordinate mixing, hence no off-diagonal ladder can appear by
    restriction), the barrier is the constant vacuum value there (`yangMillsSymbol_on_sector`), and
    the gap `2` survives the restriction with a strictly positive rate (`sector_gap`,
    `sector_gap_pos`).  `OSReconstruction.Clustering` Â§7 removes atomicity from the
    KÃ¤llÃ©nâLehmann step: for an arbitrary finite Borel measure, `laplace_le_of_massGap` gives decay
    at the gap's rate and `measure_Iio_eq_zero_of_laplace_decay` forces a measure to vanish below
    the rate, so the rate is the bottom of the *support* of `dÏ`; `laplace_map_withDensity` gives
    the representation in a multiplication model, `â« w x e^{âÏ f x} âÎ¼` â the measurable functional
    calculus `e^{âÏM_f} = M_{e^{âÏ f}}` as a KL representation, which is the shape
    `ChapterSpectralMultiplication` produces for a normal bounded operator with a cyclic vector, and
    which has no atomicity hypothesis anywhere.  - *The cut-off-uniform relative bound (2026-11-06).*  The relative form bound is uniform in the
    cut-off, and the chapter now says so.  Â§10's AMâGM pays the ladder in the reference form rather
    than in `âxâÂ²` â `Sáµ¢^*Sáµ¢ = Aáµ¢Â²diag(náµ¢+1)` and `Sáµ¢Sáµ¢^* â¤ Aáµ¢Â²` because a raise is injective
    (`sum_raiseIdx_le`) â giving `âq_K(x)â â¤ Â½Q(x) + Â½(Î£áµ¢Aáµ¢Â²)âxâÂ²` with **no** `Î` in either
    constant (`ladder_form_norm_le`, `ladder_form_abs_re_le`); Â§11 records the trade-off
    `(a, b) = (Îµ/2, Î£Aáµ¢Â²/(2Îµ))` as a Pareto frontier (`amgm_pareto_iff`, `amgm_min_shift`), so
    `1/2` is a weight choice, not a forced ratio.  Â§12.1â12.2 transfer the bound to the closed form
    with the *degree* symbol as reference (`sum_dirWeight_eq`, `ladder_form_le_degree`,
    `abs_closedKernelForm_boxKernel_le`, `closed_farisLavine_boxKernel`), and
    `closed_farisLavine_boxKernel_half` is the unit-weight member: ratio `1/2`, shift
    `max ((Î£áµ¢Aáµ¢Â²)/2 â d/2) 0`, the same numbers at every `Î`.  So `a(Î) = 1/2` is one number below
    `1` rather than a family indexed by the cut-off; what Â§7's `Ï(Î) â Î^{(d+1)/2}` shows is only
    that the *bounded-perturbation* reading cannot produce it.
  - *Strong continuity of the transfer semigroup (2026-11-06).*  `â` is assembled
    (`OSReconstruction.HilbertSpace`) and the semigroup on it is now **strongly continuous at
    `0`**: `tendsto_physEvolCompletion` proves `Ï â¦ P(Ï)z` is continuous at `0` for every
    `z â â` from continuity of the two-point function `Ï â¦ â¨T(Ï)F,Fâ©` â the OS axiom â together
    with contractivity.  The two ingredients are `osBilin_evol_self`: contractivity at `Ï` and at
    `âÏ` sandwich `âT(Ï)Fâ`, so the evolution is an isometry on `ð/ð`; and then
    `âT(Ï)x â xâÂ² = 2(â¨x,xâ© â â¨T(Ï)x,xâ©)` (`continuous_norm_physEvol_sub`) is continuous in `Ï`,
    vanishing at `0`.  Density of `ð/ð` in `â` plus contractivity finish by `Îµ/3`.  So strong
    continuity is *derived*, not assumed of `T`.  In the Fock realization of the corpus the
    continuity hypothesis is exactly what the ESA/FarisâLavine route gives: the inner Hamiltonian
    is sandwiched between outer creation and annihilation operators, the closed form dominates the
    perturbation (`closed_farisLavine_boxKernel`), and the resulting Friedrichs/Stone object is
    strongly continuous by construction, so its matrix elements are continuous.  The Fock side also
    has a *proved* link to the 4d theory, at the level of Hamiltonians: in the Weyl gauge `Aâ = 0`
    the BRST gauge-fixing term vanishes (`BookBrstGaugeFixing.bookGfTerm_eq_zero_of_Afield0`, QYM
    instance `su2_bookGfTerm_eq_zero_of_Afield0`), the 4d Hamiltonian reduces to the 3d sum of
    squares (`YangMillsHermite.ymHamiltonian_quadForm`), and `QymTimeIndependent.ymFock_weylGauge_timeIndependent`
    gives that operator a fixed self-adjoint generator with unitary propagator.  What is missing is
    the Hilbert-space map `â â Î(Hâ)`, not the operator identification.
  - *The generator (2026-11-06).*  `OSReconstruction.Generator` constructs it.  The domain is
    convergence of the difference quotient â `HasGen`/`genDomain`, closed under the vector
    operations because a limit of sums is the sum of limits (`hasGen_add`, `hasGen_smul`).  The
    limit is along `ð[â ] 0`, not `ð 0`: at `Ï = 0` the quotient `Ïâ»Â¹ â¢ (P(Ï)z â z)` is junk
    (`0â»Â¹ = 0`), so including that point would force the limit to vanish and shrink the domain to
    the common fixed points of the `P(Ï)`.  The
    value is `Classical.choose` of the limit, with linearity recovered from
    `tendsto_nhds_unique` (`genValue_add`, `genValue_smul`) rather than from the definition.  The
    result is `generator : â ââ.[â] â`, characterised by `generator_apply_tendsto` and unique by
    `generator_apply_eq_of_tendsto`.  That it is the generator *of this family* is
    `generator_evol`: `P(t)` preserves the domain and `A P(t) z = P(t) A z`, because the quotient
    of an evolved vector is the evolved quotient (`diffQuot_evol`, using `P(t)P(Ï) = P(Ï)P(t)`).
    Given `â Ï, IsSelfAdjoint (P Ï)`, the generator is **symmetric** (`generator_isSymmetric`):
    `âªÏâ»Â¹â¢(P(Ï)z â z), wâ« = âªz, Ïâ»Â¹â¢(P(Ï)w â w)â«` pointwise (`inner_diffQuot_comm`) and the two
    sides pass to the limit, with no integral representation anywhere.  Note the hypothesis: the
    OS axioms give contractivity in both directions, i.e. *unitarity* of `P(Ï)`, and a unitary
    need not be symmetric; self-adjointness of the transfer operator is the realization fact
    `P(Ï) = e^{âÏH}` for the self-adjoint `H` of the ESA/FarisâLavine route.
  - *KÃ¤llÃ©nâLehmann on `â` (2026-11-06).*  `OSReconstruction.KallenLehmannModel` attaches Â§7's
    representation to the physical two-point function instead of leaving it in a model: for an
    isometry `U : â ââáµ¢[â] LÂ²(Î½)` under which `P(Ï)` is multiplication by `e^{âÏ f}`,
    `kl_physEvol` proves `âªz, P(Ï)zâ« = laplace (áºÂ²dÎ½ â fâ»Â¹) Ï` â `LÂ².inner_def` computes the
    matrix element as an integral (`inner_toLp_eq_integral`) and `laplace_map_withDensity` turns it
    into the Laplace transform.  `physEvol_twoPoint_nonneg` reads OS positivity off a Laplace
    transform of a positive measure (`laplace_nonneg`), and the decay/support lemmas of Â§7 then
    apply to the physical correlator directly.  The multiplication model is the single hypothesis:
    producing it is the spectral theorem for the generator, which Â§5.2 has only as a symmetric
    `LinearPMap`.
  - *The `LÂ²` multiplier and its generator (2026-11-06).*  `OSReconstruction.L2Multiplier` builds
    the operator the KL model had been postulating.  `mulL2` is bounded multiplication on `LÂ²(Î½)` by
    an essentially bounded function â HÃ¶lder in the exponent form `(â¤, 2, 2)`, the same
    `ContinuousLinearMap.holderL` construction the wave chapter uses â and `expFlow` is the
    multiplier family `e^{âÏf}`, defined for all real `Ï` (identity off `Ï â¥ 0`) so it can be a
    bridge's `Q`, with `expFlow_zero` and `expFlow_comp` proved from `Real.exp_add` pointwise.  With
    it `kl_physEvol_uniform` gives the KL representation at *every* `Ï â¥ 0` from one representative
    and one spectral measure â exactly the `hkl` input of `continuousOn_physEvol_twoPoint` â and
    `osFockBridgeOfMulModel` fills `OsFockBridge` with `Q := expFlow`, so the bridge's flow is
    constructed rather than assumed.  `tendsto_expFlow_slope` identifies the generator of that
    flow: `Ïâ»Â¹(Q(Ï)z â z) â âf z` in `LÂ²(Î½)` for `f z â LÂ²(Î½)`, by dominated convergence on the
    square with the pointwise bound `|(e^{âÏc} â 1)/Ï| â¤ c` for `c â¥ 0`.  The flow is contractive
    (`expFlow_contractive`, and `âexpFlow Ïâ â¤ 1` from the essential-supremum bound on the
    multiplier), and `tendsto_expFlow_zero` turns the difference quotient into norm strong
    continuity at `0âº`.  `inner_physEvol_eq_inner_expFlow` and
    `klMeasure_same_for_physEvol_and_expFlow` show that `P` and the flow have the same matrix
    elements, hence one KL measure `klMeasure Î½ f zh`, and `expFlow_twoPoint_nonneg` reads
    positivity off it.  The measure is finite and supported on `[0, â)` (`klMeasure_univ_lt_top`,
    `klMeasure_support`), its mass is `âzâÂ²` (`klMeasure_mass_eq_norm_sq`), and `laplace_le_mass` /
    `twoPoint_le_klMass` bound the transform and the two-point function by that mass; with the
    contraction bound this gives `abs_twoPoint_le_norm_sq`, `|âªz, P(Ï)zâ«| â¤ âzâÂ²`, while
    `tendsto_expFlow_at` extends strong continuity to every `Ï â¥ 0`; `tendsto_physEvol` carries it
    back to `P` itself through the isometry (for every vector when `f` is essentially bounded), and
    `twoPoint_antitoneOn` makes the two-point function decreasing on `[0, â)` from the KL
    representation and `twoPoint_convexOn` makes it convex there; a gap `m` upgrades the mass bound
    to `twoPoint_le_norm_sq_mul_exp`, `âªz, P(Ï)zâ« â¤ âzâÂ² e^{âmÏ}`; `tendsto_physEvol_slope` gives
    the right difference quotient `Ïâ»Â¹(P(Ï)y â y) â âM` with `UM = M_f(Uy)`, i.e. the generator is
    `âM_f` in the multiplier model (`hasDerivWithinAt_twoPoint` is its derivative form: `Ï â¦ âªx,
    P(Ï)yâ«` has right derivative `ââªx, Mâ«` at `0`); `klMeasure_absolutelyContinuous` places the KL
    measure under the push-forward `Î½.map f`, and `klMeasure_finite` records it as finite and
    supported on `[0, â)`. Beyond the mass gap, the support is the essential range of `f` for the
    weight `zÂ² dÎ½`. Unconditional: `support_klMeasure_subset_closure_range` (support inside
    `closure (range f)`), `support_klMeasure_subset_Ici_zero`, and the tail bounds
    `twoPoint_le_norm_sq_mul_exp_of_support` / `_sInf` at or below the support. Dependent on the
    essential-range hypothesis (weight positive on opens meeting `range f`):
    `support_klMeasure_eq_closure_range`, its infimum form `sInf_support_klMeasure_eq` â exponent
    `sInf (closure (range f))` â and `twoPoint_le_norm_sq_mul_exp_range`. That hypothesis is not
    free: `support_klMeasure_eq_closure_range_of_measure` derives it from properties of `Î½`
    itself (`z â  0` a.e. and positive `Î½`-mass on the preimages of opens meeting the range).
    Not claimed *here*: that the transfer
    semigroup `P` *is* this flow.  That is the theorem for the generator, and it is now proved at the
    generator level â `generatorRight` is the transported generator of the flow â in
    `OSReconstruction.MultiplierGenerator` (2026-11-07, the bullet below); the *flow* itself remains
    the hypothesis of this section.
  - *Time continuity of the KL transform (2026-11-06).*  `Clustering.continuousOn_laplace` proves
    the Laplace transform of a finite measure supported on `[0, â)` is Lipschitz in `Ï` with the
    first moment `â« Î» dÏ` as constant â `e^{âÏÎ»}` is `1`-Lipschitz in the exponent and `Î»` is
    integrable, so no dominated convergence is needed â hence continuous on `[0, â)`.
    `KallenLehmannModel.continuousOn_physEvol_twoPoint` carries this to `Ï â¦ âªz, P(Ï)zâ«`:
    continuity in time, in matrix-element form, from the spectral measure alone.  Norm continuity of
    `P` and the identification `generatorRight = âM_f` are *not* claimed from this: they need the
    `LÂ²` difference-quotient limit `((e^{âÏf} â 1)/Ï) z â âf z` for the transfer semigroup itself,
    which `L2Multiplier.tendsto_expFlow_slope` supplies only for the constructed multiplier flow.
  - *Closedness of the generator (2026-11-06).*  `OSReconstruction.GeneratorClosed` proves the graph
    is closed: if `uâ â zâ` in `â` and `A uâ â y`, then `zâ` lies in the domain and `A zâ = y`
    (`generator_isClosed`), by the integral representation the earlier draft recorded as missing.
    The orbit of a domain vector has derivative `P(t)A z` at `t` (`hasDerivAt_physEvol`, from
    `generator_apply_tendsto` and `P(t)P(s) = P(t + s)`), and the fundamental theorem of calculus
    gives `P(Ï)z â z = â«â^Ï P(s)A z ds` (`physEvol_sub_eq_integral`).  No `â`-valued Bochner
    integral is needed: the identity is compared with the difference quotient of a *fixed* `y`,
    where the two integrands differ by `P(s)(A uâ â y)` and contractivity bounds the integral of
    that difference by `|Ï| âA uâ â yâ`; dividing by `Ï` and letting `n â â` closes the graph.  The
    companion limit statement is `tendsto_average_physEvol`: the average of a strongly continuous
    curve tends to its value at `0`, again by contractivity (`Metric`-`Îµ`/`Î´`, not dominated
    convergence).  Closedness plus symmetry gives a *closed symmetric* operator; self-adjointness
    is the remaining step.
  - *Strong continuity without the negative-time isometry (2026-11-06).*
    `OSReconstruction.SemigroupContinuity` re-derives `tendsto_physEvolCompletion` from the OS
    axiom alone.  Contractivity at the single time being approached gives the inequality
    `âP(Ï)x â xâÂ² â¤ 2(â¨x,xâ© â â¨P(Ï)x,xâ©)` (`norm_physEvol_sub_sq_le`) in place of the isometry
    equality, so the right-hand side tends to `0` by matrix element continuity
    (`tendsto_norm_physEvol_sub_right`, then `tendsto_physEvolCompletion_right` on `â`, both along
    `ð[>] 0`).  The abstract form is `tendsto_of_contractive_weak`: a contraction family with
    continuous matrix elements is strongly continuous â no isometry and no group law.  This is the
    continuity half of the transfer semi-group; the rest is the open item below.
  - *Two-sided contractivity forces a trivial evolution (2026-11-06).*
    `OSReconstruction.TransferSelfAdjoint` shows that the hypothesis `â Ï, IsSelfAdjoint (P Ï)` is
    satisfiable only by the trivial evolution.  Contractivity at `Ï` and at `âÏ` makes `P(Ï)` an
    isometry (`norm_physEvolCompletion_eq`); a self-adjoint isometry is an involution
    (`comp_self_eq_one_of_isometry_isSelfAdjoint`); and `Ï = Ï/2 + Ï/2` then gives `P(Ï) = 1`
    (`physEvolCompletion_eq_one`).  Consequently every vector is in the domain
    (`genDomain_eq_top_of_selfAdjoint`) and the generator vanishes identically
    (`generator_apply_eq_zero_of_selfAdjoint`).  So `P(Ï) = e^{âÏH}` *is* a theorem in this
    framework, but with `H = 0`: the hypothesis of `generator_isSymmetric` is not merely hard to
    discharge, it is inconsistent with nontrivial dynamics, and so is the KL multiplication model
    with `f â  0` (`KallenLehmannModel`).  The physical input is wrong at negative Euclidean time:
    the OS transfer matrix is `e^{âÏH}` for `Ï â¥ 0`, a contraction, while `e^{ÏH}` is unbounded.
    The repair is to assume contractivity for `Ï â¥ 0` only, rebuild `physEvolCompletion` as a
    semi-group, and re-derive strong continuity from matrix element continuity without the `âÏ`
    sandwich; self-adjointness then comes from positivity (Friedrichs/FarisâLavine), not from
    Stone's unitary group.  Two of the three layers are now in place: continuity is
    `SemigroupContinuity` (contraction bound, filter `ð[>] 0`) and the generator with its closedness
    is `SemigroupGenerator` (`genDomainRight`, `generatorRight`, `generatorRight_isClosed`, driven by
    the right-derivative fundamental theorem of calculus).  That generator is also dissipative,
    `generatorRight_inner_le_zero` -- `âªA z, zâ« â¤ 0`, from contractivity and CauchyâSchwarz -- which
    is the one-sided statement that survives in place of symmetry; its quantitative form is the a
    priori bound `generatorRight_resolvent_bound`, `Î»âzâ â¤ âÎ» z â A zâ` for `Î» > 0`, which makes
    `Î» â A` injective (`generatorRight_resolvent_injective`) -- the estimate half of
    LumerâPhillips.  The type-level half is now done as well: `OSReconstruction.TransferSemigroupRight`
    states contractivity as `HinvRight` (`0 â¤ Ï` only), descends the evolution to `ð/ð` as
    `physEvolRight`, extends it to `â` as `physEvolCompletionRight` with `0 â¤ Ï` as an argument,
    and proves `P(0) = 1`, `P(s + t) = P(s)P(t)` for `s, t â¥ 0`, `âP(Ï)â â¤ 1` and strong
    continuity at `0âº` (`tendsto_physEvolCompletionRightFun`) from the contraction inequality
    alone; `physEvolCompletionRight_eq` shows the forward semigroup is the restriction of the old
    one whenever the two-sided hypothesis holds, so nothing is lost.  The generator itself is now built on that semigroup: `SemigroupGenerator` defines `diffQuot` on
    `physEvolCompletionRightFun` with `HinvRight`, so `generatorRight`, `genDomainRight` and
    `HasGenRight` take no two-sided hypothesis; its closedness proof uses the right derivative at
    `t â¥ 0` and orbit continuity on `[0, â)` (`continuousOn_physEvolCompletionRightFun`) instead of
    shifting by a negative time.  What remains two-sided is the group-level layer, renamed
    `Generator.diffQuotGroup` (`HasGen`, `genDomain`, `generator`), together with `physEvol` and
    `physEvolCompletion` of `HilbertSpace`, whose subject is the family `P : â â B(â)` itself.
  - *The generator of `P` is `âM_f`, not only the flow's (2026-11-07).*  The sentence that used to
    stand here â `generatorRight = âM_f` is asserted for the flow only â is now superseded, and the
    proof needs no spectral theorem.  `BookProof/OSReconstruction/MultiplierGenerator.lean` (no
    `sorry`, registered in `BookProof.lean`) observes that a bridge is an *isometry*, so the
    difference quotient passes through it exactly:
    `U (Ïâ»Â¹ â¢ (P(Ï)z â z)) = Ïâ»Â¹ â¢ (Q(Ï)(U z) â U z)` for `Ï â¥ 0` (`map_diffQuot`).  Everything else
    is that identity read in two directions:

    * `hasGenRight_of_bridge` â a limit of the `Q`-side quotient pushes forward through the inverse
      unitary, so the forward-time **domain** is the preimage of the flow's generator domain;
      `generatorRight_bridge` â and its **value** is the transported one, `U (generatorRight z) = w`,
      by uniqueness of limits in the target space.  Both are stated for an arbitrary
      `OsFockBridge`, so this is not a multiplier-model accident: a bridge identifies generators,
      not only two-point functions.
    * `exists_generatorRight_mulModel` â the multiplier instance.  With the multiplier law
      `U (P(Ï)x) = expFlow Ï (U x)` and `fÂ·zy â LÂ²(Î½)`, the vector `y` is in `genDomainRight` and
      `U (generatorRight y) = âM_f(U y)`.  The auxiliary vector `M` that
      `tendsto_physEvol_slope` had to be *given* is now produced from the bridge's surjectivity
      (`OsFockBridge.surjective`), which is why that theorem's `hM` hypothesis disappears here.
    * `inner_generatorRight_mulModel` â the quantitative form: on that domain
      `âªA y, yâ« = ââ« f |zy|Â²`, so **dissipativity is exactly `f â¥ 0` a.e.**
      (`inner_generatorRight_mulModel_nonpos`), recovering `generatorRight_inner_le_zero` with its
      value.  The sign convention is now a theorem rather than a convention: `H = M_f â¥ 0` is the
      Hamiltonian and `A = âH` the Euclidean generator, which is *why* the one-sided contractivity
      hypothesis `HinvRight` is the correct one and the two-sided family of `TransferSelfAdjoint`
      cannot be nontrivial.

    * `exists_resolvent_mulModel` / `range_sub_generatorRight_mulModel` â the LumerâPhillips
      **range condition** `ran(Î» â A) = â` for `Î» > 0`, the half `SemigroupGenerator` recorded as
      missing.  It is not postulated: the solution is written down.  With
      `g = (Î» + f)â»Â¹` â bounded by `1/Î»` *because* `f â¥ 0` (`inv_antiâ`) â and
      `y = Uâ»Â¹ (g Â· U x)`, the three things to check are that `gÂ·U x` is in the multiplier domain
      (`f g â¤ 1`, a bilinear `MemLp` with exponents `(â¤,2,2)`), that its preimage is in the
      forward-time domain (the bullet above), and that `(Î» + f) g = 1` a.e.  The quadratic-form
      identity gives `Î» y â A y = x` directly.
    * `norm_resolvent_mulModel` â and the estimate on the explicit solution, `Î»âyâ â¤ âxâ`, i.e.
      `generatorRight_resolvent_bound` read on it.  So both LumerâPhillips hypotheses are theorems
      in the multiplier model, and the generator's resolvent is `(Î» + f)â»Â¹` as an operator
      identity rather than a formal analogy.

    **Boundary.**  The multiplier law is still the hypothesis, and it is the spectral theorem for
    `P`: the module identifies the generator and its resolvent *given* the flow, it does not build
    the flow from the OS axioms.  Also open at the time of writing was the existence of an
    unbounded self-adjoint `H` with `A = âH`; that half is now closed in `MultiplierSelfAdjoint`
    (see the 2026-11-08 bullet), which builds `H` from `(Î» + f)â»Â¹` and proves `Hâ  = H`, `H â¥ 0`.
    What this module proves on its own is that `Î» â A` is onto with a bounded inverse of norm at
    most `1/Î»` â the range condition â which is the statement `SemigroupGenerator` needed.
    `../physlib`'s multiplication-operator module was checked first and does not transfer: its
    `mulOperator`/`mulOperator_isSelfAdjoint_ofReal` live on the complex `SpaceDHilbertSpace d Î¼`
    over `Space d` with no exp flow, so the reusable input was instead the in-repo
    `tendsto_physEvol_slope` of `L2Multiplier`.
  - *The multiplier resolvent is the resolvent of a self-adjoint `H â¥ 0` (2026-11-08).*
    `BookProof/OSReconstruction/MultiplierSelfAdjoint.lean` (no `sorry`, registered in
    `BookProof.lean`) closes the operator-level half of the previous bullet's boundary, by the
    classical shift-invert route in `â`.  `resolventMulModel` is the bounded `R = (Î» + f)â»Â¹` read
    through the bridge â multiplication by `resolventFun`, with `âRâ â¤ 1/Î»` from
    `â(Î» + f)â»Â¹â â¤ 1/Î»` in the essential supremum â and `resolventMulModel_law`,
    `Î»Â·U(R x) + fÂ·U(R x) = U x` in `LÂ²(Î½)`, is what makes it an inverse.  Symmetry of `R` is the
    real-multiplier calculation `resolventMulModel_inner_comm`; injectivity and dense range follow
    from the same law.

    The Hamiltonian is then `hamiltonianMulModel = Râ»Â¹ â Î»` on `ran R`:
    `hamiltonianMulModel_apply` reads `H (R x) = x â Î» R x`, and `hamiltonianMulModel_image` gives
    `U (H (R x)) = mulImage D Î» x` â the vector `exists_generatorRight_mulModel` names as
    `âU (generatorRight (R x))`.  So `H` is symmetric (`hamiltonianMulModel_isFormalAdjoint`) with
    dense domain (the range of `R`), i.e. `H â¤ Hâ `.  The reverse inclusion is the von Neumann
    argument, isolated once for an abstract real Hilbert space:
    `le_adjoint_of_shift_surjective` â a symmetric `T` with `ran(Î» + T) = â`, `Î» > 0`, satisfies
    `Tâ  â¤ T`, because `z` solving `Î» z + T z = Tâ  v + Î» v` makes `v â z` orthogonal to
    `ran(Î» + T)`.  Instantiated at `hamiltonianMulModel_resolvent` (`Î» + H` is onto by
    construction) it gives `hamiltonianMulModel_isSelfAdjoint`, `Hâ  = H`.  The lemma is kept
    generic on purpose: the same argument written against `â` unfolds the
    `UniformSpace.Completion` in every tactic step and hits the heartbeat limit at a million,
    while at the abstract level it is immediate.  Positivity is quantitative:
    `hamiltonianMulModel_inner_nonneg`, `âªH y, yâ« = â« f (U y)Â² â¥ 0`, so `H â¥ 0`.  Finally
    `hamiltonianMulModel_resolvent` and `resolvent_hamiltonianMulModel` say `R` is *the* resolvent
    of `H` at `Î»` in both directions, so the explicit family `(Î» + f)â»Â¹` is a genuine resolvent,
    not a formal analogue.

    `generatorRight_eq_neg_hamiltonianMulModel` then puts the two halves together: on `dom H` the
    forward generator exists and `U (generatorRight y) = âU (H y)`, both sides being
    `mulImage D Î» a`.  The two modules carried `f Â· U y` with different membership proofs; the
    theorem exists because those presentations differ only by associativity, so they are a.e. equal
    and `MemLp.toLp_congr` identifies them.

    The flow itself is now *defined* rather than postulated: `flowOfH D Ï x = Uâ»Â¹ (e^{âÏf} Â· U x)`,
    with `U_flowOfH`, `flowOfH_zero`, the semigroup law `flowOfH_add`, contractivity
    `flowOfH_contractive`, and `physEvol_eq_flowOfH` â which is exactly the multiplier law read
    back, so the physical semigroup is this flow precisely when `MulModel.hlaw` holds.  The natural
    definition would be the functional calculus of the *bounded* resolvent (`R` is bounded,
    self-adjoint, `âRâ â¤ Î»â»Â¹`, so `e^{âÏH} = Ï_Ï(R)` with `Ï_Ï r = exp(âÏ(1/r â Î»))` bounded and
    continuous), but Mathlib has no continuous functional calculus on a real Hilbert space; the
    conjugation above gives the same family and the laws above verify it.

    The flow is now an operator family, not just a family of vectors: `flowOfHCLM D Ï : â âL[â] â`,
    with `flowOfHCLM_apply` and `norm_flowOfHCLM_le_one`.  Strong continuity needs no
    generator-domain hypothesis â for *every* `x`, `Ï â¦ e^{âÏH} x` is continuous at every `Ï â¥ 0`
    (`continuousOn_flowOfHCLM`), because `âe^{âÏf}u â uâ â 0` is dominated convergence with the
    bound `4 (u x)Â²` (`tendsto_expFlow_nhdsGE_zero`; the older `tendsto_expFlow_zero` needed
    `fÂ·u â LÂ²`, which generic semigroup theory must not assume).  Symmetry is the reality of the
    multiplier: `inner_mulL2_comm` gives `âªW u, vâ« = âªu, W vâ«` for real `W`, and the bridge is an
    isometry, so `IsSelfAdjoint (flowOfHCLM D Ï)` for `Ï â¥ 0` (`isSelfAdjoint_flowOfHCLM`) and the
    bundle `flowOfHCLM_isContractionSelfAdjointSemigroup` records identity, semigroup law, norm
    bound and self-adjointness together.  Finally the generator statement now reads from the flow
    side: `tendsto_flowOfH_slope` proves `Ïâ»Â¹ â¢ (e^{âÏH}(R a) â R a) â âH (R a)` directly from the
    model's `tendsto_expFlow_slope` carried through the bridge, without passing through
    `physEvolCompletionRightFun` or `HasGenRight`.

    That last point is where the two routes part.  `dom H = ran R` is where the multiplier chart can
    compute the slope itself; the *forward* domain of the transfer generator is larger, and there
    `f Â· u` need not be square-integrable, so the model slope need not converge.  The flow still
    generates the same operator there: `tendsto_flowOfH_slope_of_hasGenRight` shows the flow's
    quotient converges on every `z` with `HasGenRight D.hinv z`, with limit
    `generatorRight D.hinv z`, and `hasGenRight_iff_tendsto_flowOfH_slope` gives the converse, so
    the flow's forward domain *equals* the transfer generator's â the flow generates nothing
    larger.  `tendsto_flowOfH_slope_of_mem_domainH` then recovers the `dom H` value `âH` from that
    general statement via `generatorRight_eq_neg_hamiltonianMulModel` and injectivity of `U`.
    The single ingredient this route borrows is the multiplier law (`physEvol_eq_flowOfH`); the
    `dom H` route does not borrow it.

    Positivity is the semigroup face of `f â¥ 0`.  On the chart the flow is multiplication by
    `e^{âÏf} â¥ 0`, so it preserves the a.e. nonnegative cone (`expFlow_nonneg`, `flowOfH_nonneg`),
    and since `Ï â¥ 0` and `f â¥ 0` force `e^{âÏf} â¤ 1` it also pulls a nonnegative vector down
    (`expFlow_apply_le_of_nonneg`, `flowOfH_apply_le_of_nonneg`).  Together with
    `hamiltonianMulModel_inner_nonneg` (`H â¥ 0`) this is the order theory of the model; the corpus
    has no order on `â` other than the chart cone, which is why the statement is phrased through
    `U`.

    The forward domain is now *densely defined and closed*, the two structural properties of a
    generator.  Density is `dense_flowForwardDomain`: the domain contains `dom H = ran R`, which is
    dense because `R` has dense range (`dense_range_resolventMulModel`), and `dom H` lies inside it
    by `tendsto_flowOfH_slope`.  Closedness is `closed_flowForwardDomain`: if `uâ` in the forward
    domain converge and the generator's values `A uâ` converge, the limit is again in the domain
    with value the limit, and â read flow-side â the flow's quotient at the limit point converges
    to that value.  It is inherited from `generatorRight_isClosed` and keeps that theorem's
    matrix-element continuity hypothesis `hcont` (`â F, Continuous (Ï â¦ âªT Ï F, Fâ«)`):
    `LinearFunctional` has no continuity field, so `hcont` is an OS input that cannot be read off
    the model.  The flow's *strong* continuity does not replace it, because the graph argument
    integrates the transfer representation `physEvol_sub_eq_integral_right`, which assumes `hcont`.
    `flowGenerator_dense_domain_closed` bundles the two.

    Large time is answered pointwise, which is what the chart can give.  `e^{âÏf}` is *strictly*
    positive, so the flow is **not** positivity improving: `expFlow_support` proves the support is
    preserved exactly â `e^{âÏH}u` vanishes precisely where `u` did, so mass never spreads into a
    set the initial vector missed.  Strict positivity is preserved (`expFlow_pos_of_pos`,
    `flowOfH_pos`), and where `f x > 0` the chart decreases strictly (`expFlow_apply_lt_of_pos`) and
    decays to zero, `e^{âÏ f x} u x â 0` (`tendsto_expFlow_mul_atTop`, a.e. under `0 < f` in
    `tendsto_expFlow_apply_atTop`), while `expFlow_apply_of_f_eq_zero` freezes the part over
    `{f = 0}`.  So the large-time limit is the projection onto the kernel of the density: ergodic on
    `{f > 0}`, trivial on `{f = 0}`.

    The pointwise law upgrades to a norm statement by dominated convergence, and the domination is
    the same estimate as contractivity: `e^{âÏf x} â¤ 1` for `Ï â¥ 0`, so
    `(e^{âÏf x} u x)Â² â¤ (u x)Â²`, and `(u x)Â²` is integrable because `u â LÂ²`.  That gives
    `âe^{âÏH}uâÂ² = â« (e^{âÏf}u)Â² â 0` (`tendsto_norm_sq_expFlow_atTop`), hence
    `âe^{âÏH}uâ â 0` by `â` of the squared norm (`tendsto_norm_expFlow_atTop`), and on `â` the same
    through the isometry bridge (`tendsto_norm_flowOfH_atTop`).  The one extra hypothesis is
    `0 < f` a.e., and it is not a technical convenience: where `f = 0` the flow freezes
    (`expFlow_apply_of_f_eq_zero`), so a density vanishing on a set of positive measure leaves a
    nonzero part in the limit and the norm cannot tend to `0`.

    That caveat points at the sharper statement, which needs no hypothesis on the density at all:
    the flow's limit is the *projection* rather than `0`.  Pointwise, `e^{âÏ f x} â 1` where
    `f x = 0` and `â 0` where `f x > 0`, so the multiplier converges to the indicator of
    `{f = 0}`, and that indicator is bounded by one, so dominated convergence applies to the
    differences too â with the same bound `(u x)Â²`, since `|e^{âÏ f x} â 1_{f = 0}| â¤ 1`
    (`abs_exp_neg_sub_kernelIndicator_le_one`).  Thus `âexpFlow Ï u â limitMulL2 D uâ â 0`
    (`tendsto_norm_expFlow_sub_limitMulL2_atTop`), where `limitMulL2` is multiplication by the
    indicator class (`kernelIndicator`).  On `â` the same gives
    `tendsto_flowOfHCLM_atTop : flowOfHCLM D Ï y â limitProjection D y`, and `limitProjection` is
    an **orthogonal projection**: idempotent (`limitProjection_idem`, from the indicator's `wÂ² = w`)
    and self-adjoint (`isSelfAdjoint_limitProjection`, the same symmetry argument as the flow, via
    `inner_mulL2_comm`), bundled in `limitProjection_isOrthogonalProjection`.  So the large-time
    limit *is* the projection onto the kernel of the density, and the `âÂ·â â 0` statement is its
    special case where that kernel is negligible.

    Self-adjoint plus idempotent does not by itself say *which* subspace is projected onto, so the
    next step identifies it on the chart.  `limitProjection_eq_iff` says `limitProjection D y = y`
    exactly when `U y` vanishes where `f â  0` â the vectors living on the kernel of the density â
    and `limitProjection_eq_zero_iff` says `limitProjection D y = 0` exactly when `U y` vanishes
    where `f = 0`, so the kernel is the complementary part of `â`.  The residual is orthogonal to
    the range (`inner_sub_limitProjection_limitProjection`: on the chart the residual carries
    `1_{f â  0}` and the projection `1_{f = 0}`, so the pointwise product is zero), hence range and
    kernel are orthogonal (`inner_limitProjection_ker`), and the range is characterised as a set in
    `range_limitProjection` with the kernel in `mem_ker_limitProjection`; the residual is itself a
    kernel vector (`residual_mem_ker_limitProjection`), so every vector splits as
    `limitProjection D y` plus a kernel vector â an orthogonal direct sum.
    `limitProjection_isOrthogonalProjectionOntoDensity` bundles the whole operator statement: the
    flow converges strongly to the orthogonal projection onto the part of `â` supported where the
    Hamiltonian density vanishes.

    That subspace is literally `ker H`.  `H` is multiplication by `f` on the chart,
    `U (H (R a)) = f Â· U (R a)` (`hamiltonianMulModel_image`), so `mulImage_eq_zero_iff` turns
    `H (R a) = 0` into the a.e. condition that `U (R a)` vanish where `f â  0`
    (`hamiltonianMulModel_eq_zero_iff`), which by `limitProjection_eq_iff` is exactly the fixed
    space of the limit (`hamiltonianMulModel_eq_zero_iff_limitProjection`).  So the flow's
    asymptotic state is the `ker H` component, and the `âÂ·â â 0` statement is the case `ker H = 0`.

    Operator-norm convergence is a different matter and needed a correction: it holds with rate
    `e^{âÏÎ´}` when the density has a gap `Î´ > 0` above zero
    (`norm_flowOfHCLM_sub_limitProjection`, `tendsto_opNorm_flowOfHCLM_sub_limitProjection_atTop`),
    but it is **false** without a gap.  The norm of multiplication by `g_Ï = e^{âÏf} â 1_{f = 0}` is
    the essential supremum of `|g_Ï|`, and a density with values arbitrarily close to zero â
    Lebesgue measure on `(0, 1)` with `f x = x`, for instance â keeps `|g_Ï|` at `1` on sets of
    positive measure for every `Ï`, so `âe^{âÏH} â Pâ = 1` for all `Ï` while `e^{âÏH} â P` still
    holds strongly.  The section header records this, so the corpus does not claim an
    unconditional operator-norm limit it cannot have.

    Three follow-ups turn that caveat into theorems about the same operator.  (i) The
    `ker H` identification is now an equality of **submodules**, not a pointwise statement on the
    domain: `kerHamiltonianMulModel` carries the domain in its carrier, and
    `kerHamiltonianMulModel_eq_range_limitProjection` proves `ker H = range P` in
    `Submodule â â`.  The pointwise form alone cannot give this, because `dom H = ran R` is dense
    but proper; the missing half is `range_limitProjection_subset_domain` â a chart living on
    `{f = 0}` satisfies `(Î» + f)Â·U y = Î»Â·U y`, and `Î» â¢ U y` is again a chart because the range of
    an isometry is a subspace â so the range of `P` sits inside the domain after all.  The witness
    is explicit (`exists_resolventMulModel_eq_of_limitProjection` records both `R a = y` and
    `U a = Î» â¢ U y`), and `resolventFun_mul_smul_of_eq_zero` / `eq_zero_of_eq_mul_resolventFun`
    are the two halves of the scalar arithmetic `(Î» + f)â»Â¹(Î» v) = v` that make it work in both
    directions.

    (ii) The counterexample is now a theorem rather than prose.
    `not_tendsto_opNorm_flowOfHCLM_of_noGap` takes the negation of a gap â every `Î´ > 0` has a set
    of positive finite measure carrying `0 < f < Î´` â and proves that
    `âflowOfHCLM D Ï â limitProjection Dâ` does not tend to `0`.  The estimate is
    `norm_expFlow_sub_limitMulL2_ge`: the indicator of that set is a nonzero `LÂ²` class and the
    multiplier is at least `e^{âÏÎ´}` on it, so the model-side norm is at least `e^{âÏÎ´}`; with
    `Î´ = log 2/(2Ï)` the bound is `1/2` at every `Ï â¥ 1`.  It transfers to `â` only because the two
    operator norms are equal, `norm_flowOfHCLM_sub_limitProjection_eq`, which needs the density of
    `ran U` (`âSâ â¤ âTâ` is immediate from the isometry; density upgrades it to equality).  So the
    gap in the rate theorem is a hypothesis on the truth, not on the proof.

    (iii) Strong convergence is quantified.  The two-scale bound splits at `Î´ > 0`: where `f â¥ Î´`
    the multiplier is at most `e^{âÏÎ´}`, where `0 < f < Î´` it is at most one, and where `f = 0` it
    vanishes, so `âe^{âÏH}y â P yâ â¤ e^{âÏÎ´}âyâ + â1_{0<f<Î´}Â·U yâ`
    (`norm_flowOfHCLM_sub_limitProjection_le_two_scale`, via the pointwise
    `abs_exp_neg_sub_kernelIndicator_le_two_scale` and `Lp.norm_le_norm_of_ae_le`).  The tail
    `tailMul D Î´ u` is a genuine `LÂ²` class that does not depend on `Ï`, and it vanishes as
    `Î´ â 0` (`tendsto_norm_tailMul`, dominated convergence with `{0 < f < Î´} â â`, and
    `exists_tailMul_norm_lt` picks the split).  Choosing the split first and then the time gives
    the explicit bound `norm_flowOfHCLM_sub_limitProjection_lt_of_time`: from
    `max 0 (-log (Îµ / (2(âyâ+1))) / Î´)` on, the flow is within `Îµ` of the projection, so
    `exists_time_norm_flowOfHCLM_sub_limitProjection_lt` is the quantified form of the asymptotic
    statement.  The rate is explicit in `Î´, Îµ, âyâ`; only `Î´` comes from a limit, and that is the
    sense in which a rate exists without a gap â pointwise in `y`, never uniformly.

    (iv) Two refinements close the pair.  Sharpness: the two-scale bound is attained, not merely an
    upper estimate.  If the density equals the split on the support of the vector,
    `tailMul_eq_zero_of_eq_on_support` empties the tail and the multiplier is exactly `e^{âÏÎ´}`
    there, so `norm_expFlow_sub_limitMulL2_eq_of_eq_on_support`, and its flow-side form
    `norm_flowOfHCLM_sub_limitProjection_eq_two_scale`, turn the estimate into an equality.  The
    explicit witness is `barrier_sharp`: the barrier density `Î´` on `[0,1]`, zero elsewhere
    (`barrierDensity`), tested on the class of its own indicator (`barrierVector`), gives equality
    for every `Ï â¥ 0` â the gapped rate is the truth where it applies.  No uniformity:
    `not_exists_uniform_rate_of_noGap` shows there is no rate function `r` with `r Ï â 0` bounding
    `â(e^{âÏH} â P)yâ` for every `âyâ â¤ 1`, because a unit-ball bound is a bound on the operator
    norm (`opNorm_le_of_unit_ball_bound`, by homogeneity) and such an `r` would make the norm
    converge.  The rate of (iii) is therefore pointwise in `y` by necessity, not because of the
    shape of the proof.

    (v) The two halves are now a single equivalence: `tendsto_opNorm_flowOfHCLM_sub_limitProjection_iff_gap`
    says `âe^{âÏH} â Pâ â 0` iff `â Î´ > 0, f â  0 â Î´ â¤ f` a.e.  The gap direction is the existing
    `tendsto_opNorm_flowOfHCLM_sub_limitProjection_atTop`; the converse is the contrapositive of
    `not_tendsto_opNorm_flowOfHCLM_of_noGap`, and the only new ingredient is measure-theoretic: the
    a.e. failure of the gap is turned into the split form's positive *finite*-measure set by
    `Measure.exists_subset_measure_lt_top`, which is where `Ï`-finiteness of `Î½` enters.  This is
    the general spectral fact in the normal form the spectral theorem supplies (multiplication by
    `f` on `LÂ²(X, Î½)`, spectrum = essential range of `f`); what is formal is the normal form, not
    the spectral theorem itself â `ChapterSpectralMultiplication` has the multiplication model only
    for a bounded normal operator with a cyclic vector, and Mathlib has no unbounded spectral
    theorem.  Note the direction of the inference this fixes: norm convergence *is* the gap, so a
    proof of norm convergence for YangâMills would be a proof of the mass gap, not a consequence of
    the reconstruction.

    **Boundary.**  The multiplier law `U (P(Ï)x) = expFlow Ï (U x)` remains the
    hypothesis that supplies the flow.  That law is *not* an OS consequence: the axioms supply only
    a one-parameter contractive semigroup on `â` together with its two-point functions, and the
    law says that `U` diagonalizes its generator with the simple spectrum given by `f`.  Two
    different `f` (or a multiplicity `> 1`) give the same OS axioms with different `H`, so the
    identification is model data â the choice of the KL multiplier realization â and the missing
    ingredient for deriving it is the spectral theorem for the generator (equivalently Stone's
    theorem), not another estimate.  What the corpus does derive *from* the law is the whole
    matrix-element layer (`klMeasure`, `inner_physEvol_eq_inner_expFlow`,
    `expFlow_twoPoint_nonneg`), and the 2026-11-08 bullet derives the operator behind it.
  - *What is still open.*  Two things, plus one identification.  (i) **The Euclidean generator**, not the Hamiltonian.  Closedness is proved in the semi-group
    setting (`generatorRight_isClosed` on `genDomainRight`), as are dissipativity
    (`generatorRight_inner_le_zero`), the a priori estimate `Î»âzâ â¤ âÎ» z â A zâ`
    (`generatorRight_resolvent_bound`) and injectivity of `Î» â A`
    (`generatorRight_resolvent_injective`).    LumerâPhillips would add the range condition
    `ran(Î» â A) = â`, which contractivity alone does not supply, but which is `ran(Î» + H) = â`
    and therefore follows once `H â¥ 0` is self-adjoint.  That condition is now a theorem *in the
    multiplier model* without passing through self-adjointness of an unbounded operator â
    `range_sub_generatorRight_mulModel`, with the inverse `(Î» + f)â»Â¹` and the bound `1/Î»`
    (`norm_resolvent_mulModel`); see the bullet above.  That is the Wick-rotated picture:
    `A = âH`, while in real time `H` is self-adjoint by positivity plus essential
    self-adjointness (FarisâLavine / Friedrichs), with the unitary flow from Stone's theorem --
    in this corpus `qgOuterFock_esa`, `smFockHam_esa`, `exists_stone_flow_of_esa`, on the nested
    Fock space whose sector operators are inner Hamiltonians sandwiched between outer creation
    and annihilation (`sandwich`, `secHam_matrix_element`).  The degeneracy of the previous
    bullet concerns the Euclidean family at *all* real times, not `H`, so deficiency indices are
    not needed for `H`.  An earlier version of this bullet added that the adjoint of an unbounded
    operator was *blocked on Mathlib* on real inner product spaces; that is wrong â
    `LinearPMap.adjoint` is real-valued and is what the 2026-11-08 bullet below uses to prove
    `Hâ  = H`.  What Mathlib does lack is the spectral theorem for an unbounded self-adjoint
    operator (equivalently Stone's theorem for a unitary group), which is the step the multiplier
    law needs.    What is genuinely missing is a unitary `U` from the abstract `â` onto the nested Fock space
    intertwining `P(Ï)` with `e^{âÏH}` for a self-adjoint `H â¥ 0`.  The condition is now a formal
    hypothesis bundle rather than a slogan: `OsFockBridge`
    (`OSReconstruction.FockIntertwining`) has exactly three fields â an isometry
    `U : â ââáµ¢[â] F`, dense range, and `U (P Ï x) = Q Ï (U x)` for `Ï â¥ 0` â and the module proves
    what they force: `U` is a unitary (`toIsometryEquiv`), the two-point functions agree
    (`âªx, P Ï yâ« = âªU x, Q Ï (U y)â«`, `inner_intertwines`), and contractivity, isometry, fixed
    points, symmetry and the semigroup law transfer in both directions.  The bundle is inhabited
    (`OsFockBridge.id`), so its content is the map, not the axioms.  On the Fock side the nested
    Fock space itself is the target â no Balaban or lattice-observable input is needed: the corpus
    has `ymFock_weylGauge_timeIndependent`, `qgOuterFock_esa` and `smFockHam_esa`, and the object
    that is missing is a map `U`, not a model.  What remains is to *build* `U` from the OS data
    (`â` is a completion of `ð â§¸ ð`, so `U` is defined on the dense image and extended by
    `LinearMap.extendOfNorm`) and to identify `Q(Ï)` with `e^{âÏH}` for the Friedrichs extension of
    the Fock Hamiltonian.  Without it the KL representation still attaches to a *closed symmetric*
    generator on `â`.  (ii) The
    **identification of the ladder**: `a < 1` is uniform, and the *matrix-entry* half is now
    proved.  `YangMillsLadderTransport` transports the Hermite creation ladder from the
    `Finsupp` multi-indices of `crePoly_hpsi` to the occupation functions `Idx d = Fin d â â` that
    `magCutoffKernel` is indexed by: `creCoeff` is the ladder's matrix element in that index,
    `crePoly_hpsi_apply` restates the ladder relation in it (the only nonvanishing entry out of
    `Î±` is at `Î± + eáµ¢`, with weight `â(Î±áµ¢+1)`), `boxEmbed_update` carries the cut-off box through
    the raise, and `magCutoffKernel_eq_ladder` / `boxKernel_eq_ladder` identify every entry of the
    cut-off kernel with `Aáµ¢` times that matrix element.    So `boxKernel Î A` *is* the matrix of the ladder in the Hermite basis, not merely shaped like
    it.  The operator-level half is now proved on the cut-off: `YangMillsLadderOperator` defines
    the creation operator `creOp` and the kernel-sum operator `magCutoffOp` on the truncated Fock
    space `Box d Î = Fin d â Fin Î`, and proves the identity of operators
    `magCutoffOp Î A = â i, Aáµ¢ â¢ aâ áµ¢` (`magCutoffOp_eq_sum_cre`) together with the vanishing of
    the degree-preserving part at every degree, `proj_N â magCutoffOp â proj_N = 0`
    (`occProj_comp_magCutoffOp_comp_occProj`) â the operator form of "purely off-diagonal in the
    occupation grading".  Still open: that this operator is a *restriction* of Â§24's reduced
    second-quantized magnetic operator to the transverse sector, which needs the box-to-continuum
    limit (`âÂ²(Idx d)`, unbounded) and the BRST quotient.  (iii) The **BRST quotient**: `closure (range Î©) =
    span{â_i Ï}` is now a theorem in the periodic-lattice model of
    `BookProof/BrstLongitudinalExact` (`exactStates_eq_longitudinal`, `range_derivLin`), but the
    3+1 continuum version still needs the field Hilbert space and the closed unbounded charge, so
    the identification of Â§24's transverse sector with `H/(exact â harmonic)` is model-level on
    both sides.  No strictly positive mass gap of the physical continuum Hamiltonian is claimed: the rate `2`
    is proved for the diagonal one-particle operator of Â§22 and for its reduced sector, not for the
    physical continuum theory.

---

### Summary of Tasks and Timeline

**Historical summary only:** use S0âS4 above for the revised execution order and acceptance
criteria. In particular Phase 4's shifted comparison is not by itself a spectral gap.

| Phase | Mathematical Objective | Lean 4 Target Module | Key Tools / References |
| :--- | :--- | :--- | :--- |
| **Phase 1** | Project out longitudinal gauge zero-modes via BRST cohomology | `BookProof.BrstReducedTransfer` | Nilpotent BRST charge $\Omega^2 = 0$ |
| **Phase 2** | Prove Simon channel-taming along Cartan flat directions | `BookProof.YangMillsEffectiveBarrier` | Transverse zero-point energy $\sim g|A|$ |
| **Phase 3** | Construct solvable gapped comparison operator $H_{\text{ref}}$ | `BookProof.ChapterReferenceGap` | `HarmonicOscillator.lean`, $SU(N)$ Hermite basis |
| **Phase 4** | Establish form-domination $q_{H_W} \ge c_1 q_{H_{\text{ref}}} - c_2$ | `BookProof.YangMillsFormDomination` | `ChapterFockFieldPerturbation.lean` |
| **Phase 5** | Inject analytical $\beta_\infty$ into SIRK/Temple certificate | `BookProof.SpectralGapStability` | `ChapterRitzCertificate.lean`, TrotterâKato |

The open task is to derive a coercive estimate for the concrete inner Hamiltonian, with
the sector and margin required by the selected target. The model barrier calculations
and numerical approximations support that task but do not yet provide its constant.
