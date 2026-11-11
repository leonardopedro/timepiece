# Euclidean fields, Mehler coordinates and nested-Fock reconstruction

## External-source revision (2026-11-11)

Two external trees were read for this revision: `../YM` (the Yang–Mills group's *results and
verification* repository) and `../Yang--Mills-LLM-experiment` (the Balaban-programme draught
corpus). **Neither is an input to any proof in this repository.** Their contents are PDFs and a
separate Lean tree; nothing here was compiled against ours, and no claim of theirs may be used as a
hypothesis in a Lean statement below. What they do supply is a *dated, independently assessed
status* to measure this file's architecture against.

### What the two trees establish, in their own terms

**`../YM` — assessment of OpenAI's 28 October 2026 submission (dated 10 November 2026).**
Judged: proves that a relativistic QFT satisfying the **Wightman axioms** can be constructed as a
scaling limit of four-dimensional Wilson lattice gauge theory, for any simple compact gauge group,
with OS reconstruction proved in the submission. Explicitly *not* proved, and this is the part that
matters for planning: uniqueness of the infinite-volume limit and of the vacuum; a probability
measure for the continuum theory on a state space; a mass gap; Wilson loops and the area law;
construction of single-particle states and their energy–momentum spectrum (their §8, items 1–5).
Their object is **correlation functions of gauge-invariant labels**: curvature carries weight `2`,
each derivative adds `1`, products add weights, and the labels of weight `≤ d` are quotiented by the
linear relations (Bianchi) to give `Fd = Vd/Nd`. The infinite-volume limit is **subsequential**, and
the reconstruction runs through a decomposition of the limit into pure phases.

**`../Yang--Mills-LLM-experiment` — Balaban programme draughts (QED3, YM3, YM4, RP1).** The YM4
assembly outline is a 17-box dependency diagram whose boxes carry their own status: LP (lattice
states and reflection positivity), BA (block averaging), MB (linear lattice PDE), GI (Gaussian block
integration), EM (small-field iteration), RT, SI, FP, CL are marked *complete assuming inputs*;
**NB, RS, LF, RC, B, CP are marked *not closed***. Reflection, angular continuation, reconstruction,
phase decomposition, density and spectral-filter theorems are 91 pages of *external general theory*,
i.e. black boxes relative to that diagram. The one result in that tree aimed at a gap this file
flags is RP1 (*rotation invariance from lattice symmetry and reflection positivity*), which is an
unvetted outline/manuscript.

### Four consequences for this file

**B — reconstruction is an import, not a construction here.** Phase 4's Wick rotation and
Osterwalder–Schrader step now has an independently assessed formal statement to agree with, and this
file should be read as "agrees with, or departs from, that statement", not as building reconstruction
from scratch. What remains *ours* and has no counterpart in either external tree is the Mehler /
nested-Fock identification: both external programmes are about lattice correlation functions and
never identify a Gaussian coordinate law with a mode space. The four-space separation above
(`𝓧_E`, `L²(γ)`, `𝓗_OS`, `𝓕_out`) is therefore the part of the route that is neither supplied nor
refuted by them.

**C — the weight grading is the field-strength degree class, and should be stated in its
vocabulary.** `Vd`/`Fd` is the same grading our QYM chapter reports: `magPoly` is a label of weight
`2` (curvature), a derivative coordinate (`idxD`) adds `1`, and the potential `½Σ B² + 1` is a label
of weight `4` — which is exactly `totalDegree_magWeight_le`. The quotient by the linear relations is
the reason the invariant is a *degree* and not a monomial count: two different polynomial expressions
of the same weight present the same label. Cite the external grading when the degree class is used
downstream, so the invariant is recognisably the standard one.

**N — nothing in either tree produces a mass gap, so this file cannot borrow one.** Their item 4 is
"provide no evidence for or against a mass gap"; the Balaban diagram has no gap box at all, and its
nearest strategy-level input (uniform decay of correlations) is precisely what is not closed. Any
Phase 5 text below must therefore not be read as "continuum Yang–Mills plus gap": the gap stays the
inner-Hamiltonian statement of [softmodes.md](softmodes.md) target 1, and the reconstruction supplies
only the outer operator `dΓ(h)` whose spectrum is determined by `h`.

**C — UV limits are subsequential and the measure is not constructed.** Where the text below writes
"the continuum measure", read "the correlation functions of a subsequential scaling limit at fixed
physical volume". A Borel probability measure on a space of distributions is only claimed where this
repository constructs one, and there the framework is RP1's random-distribution setting — itself
unvetted. Keeping the two modes of statement apart is the same discipline as the "four spaces"
paragraph above.

### Verification discipline worth adopting (structural, not mathematical)

The October package separates five artefacts this repository conflates: an **acceptance
specification** (`AcceptanceSpec.lean`, `CombinedAcceptance`), a **per-declaration axiom audit**
(`AxiomAudit.lean`), **Comparator** re-checks of the endpoint, a **dated evidence ledger**
(`evidence/README.md`, never overwritten), and **provenance hashes** tying the checked source to the
submitted source. Our `scripts/health.sh` and `scripts/verify-invariants` cover documentation and
import drift only: there is no per-declaration axiom audit gate and no evidence ledger. Adding an
axiom-audit gate that prints the axiom set of every exported theorem (and fails on anything outside
`propext`, `Classical.choice`, `Quot.sound`) is the single largest verifiability gain available from
this reading, and it is independent of the QYM row.

### Second reading (2026-11-11): the submission's own Lean source

The revision above was written from `../YM`'s assessment. `../OpenAI-YM-20261028` is the submission
itself: `ChallengeSpec.lean` carries the target type `YangMills.JointExistence`, `Challenge.lean`
contains only its `sorry`, `Solution.lean` is a twelve-line derivation from
`YangMills.constructed`, and `verification/` holds the replay logs. Four statements read at source
level refine the bullets above. All four remain external: none is a hypothesis of a Lean statement
in this file.

**A. W0 is a support condition, and it does not contain target 1.** `PublicTheory.lean` states W0
as three clauses: `spectralRepresentation` (each state's energy–momentum `diagonal` has
characteristic function `momentum ↦ ⟪state, U(momentum) state⟫`), `positiveEnergy`
(`energyMomentum.projection forwardConeᶜ = 0`), and `uniqueVacuum` (every translation-invariant
vector is a scalar multiple of the vacuum). `positiveEnergy` says the joint spectrum *lies in the
closed forward cone*; spectrum accumulating at zero satisfies it. A gap is therefore strictly
stronger than W0 and is not implied by it, which is the same reason the sentence is false
internally. When this file states its own spectrum condition, it should use exactly this
projection-vanishing form: it is the version our modules can state without spectral theory.

**B. Vacuum uniqueness is a statement about one selected phase.** `Hierarchy.correlation` takes an
`Option Character` argument, and the unselected correlations are pinned to the selected ones by the
`mixture` clause `∫ i, correlation (some i) a x ∂phaseMeasure = correlation none a x`. The
`Axioms` field belongs to `theory`, a single `WightmanTheory`, and `uniqueVacuum` quantifies over
that one Hilbert space. So "unique vacuum" and "the limit is a mixture of phases" are compatible:
uniqueness is per phase. This file's four-space paragraph should read the same way — `𝓗_OS` here is
the reconstruction of a *selected* label, and any statement about the mixed limit is a statement
about the integral over `Character`, not about `𝓗_OS`.

**C. The non-freeness theorem is a short-distance coefficient on a weight-4 label.**
`TraceTest.centeredTrace` is a `Field 4` element, and the test is
`r^8 log²(1/r) · ⟨vacuum, T_centered(r)⟩ → 3·dim(g)/π⁴` as `r ↓ 0`, together with exclusion of any
finite sum of `Mode.kernel` mass-shell profiles. Two consequences. First, the discriminator is
ultraviolet: it constrains operator content at short distance and is **not** evidence about a gap,
a mode space, or long-distance decay. Second, its grade-4 slot is the same graded slot as this
repository's `magWeight` (`totalDegree_magWeight_le ≤ 4`), with the stress trace as the named
physical occupant of that slot. The `r^8` is the grading doing work rather than a fitted constant: a
two-point function of two grade-4 labels has `weight = 4 + 4 = 8`, and the normalisation exponent is
that weight. Read literally the exclusion is finite-Wick-sum only — the README
puts general exclusion of continuous-mass generalized free fields out of scope — so "not a finite
free ansatz" must never be written as "not a generalized free field".

**D. The continuum limit is an explicit diagonal, and should be imitated in that form.**
`WilsonFamily.Converges` conjoins three things: the requested volume order eventually makes a test
suitable; a row `row : ℕ → ℂ`, existentially chosen, whose entries are the mesh limits
`lim_N smear N p v t` at every suitable fixed `p`; and convergence of `row` along the volume
subsequence to the smeared `unselected` correlation. The mesh limit is asserted volume by volume,
the volume limit only along a subsequence, and even the row is chosen rather than computed. That is
the precise shape in which "the continuum limit" in this file must be read, and the form Phase 4
targets should take: fixed-volume first, subsequential second.

## Revised work order (2026-11-08)

This section supersedes the architecture, priority list and completion claims below **as a
reading guide for this file**. The earlier dated material is retained as implementation
history. It does not change the programme priorities in `CURRENT_WORK_ORDER.md` or claim
a continuum Yang–Mills construction, a mass gap, or conformal invariance. “4D Euclidean
to 3D” means reconstruction on a spatial slice with real-time evolution in $3+1$
dimensions; it is not a reduction to a three-dimensional spacetime theory.

This is a source-level documentation audit, not a fresh Lean build. Use **U** for an
existing result within its stated model, **C** for a missing hypothesis/identification,
**N** for an invalid inference, and **B** for a boundary of scope. Existing theorem
names such as `continuum` or `unconditional` do not erase their binders.

### Sources and conventions

* [book.tex](book.tex): the recursive second-quantization paragraph beginning “Since the
  second-quantization procedure can be applied recursively”, “Relation with the BRST
  formalism”, and “Pure SU(3) Yang-Mills theory”. These fix the nested field algebra
  and the role of observables; they do not identify an arbitrary Euclidean measure
  with the manuscript's Hamiltonian realization.
* [Book/FreeField.lean](Book/FreeField.lean), the Mehler-limit section, and
  [Book/SolovayTensor.lean](Book/SolovayTensor.lean), “Only the Mehler Measure on the
  Infinite Part”: Gaussian coordinate laws and Hilbert-space parametrization.
* [Book/YangMillsQuantization.lean](Book/YangMillsQuantization.lean), “The Weyl-Gauge
  Quadratic Form and the Friedrichs Route”: the inner Hamiltonian and its outer lift.
* [Hashimoto–Nodera](../papers/Hashimoto.md), Definition 2.4 and Theorem 4.1: bounded
  resolvents and approximation of operator $\phi$-functions, not an infrared gap theorem.
* [softmodes.md](softmodes.md), “Revised work package (2026-11-08)”: representation
  bridges, independent spectral exclusion, and the distinction between the absolute
  inner edge and inner excitation separation. Its S0–S4 obligations apply here too.
* [docs/euclidean_cft_proof.md](docs/euclidean_cft_proof.md): the detailed implementation
  record. Its older absence claims must be read against the newer modules listed here.

Keep four spaces distinct: the Euclidean configuration measure space $\mathscr X_E$;
its reference amplitude space $L^2(\gamma)$; the reconstructed OS space $\mathcal H_{OS}$;
and the manuscript's outer graded Fock space $\mathcal F_{out}$ over an inner space
$\mathcal K$. A Gaussian-chaos Fock representation of $L^2(\gamma)$, when constructed,
is another identification to prove, not a synonym for all four spaces.

Use $\theta$ for geometric reflection and
$\Theta F=\overline{F\circ\theta}$ for its action on complex observables. Reserve
$\Omega_{OS}=[1]$ for the reconstructed vacuum, $\Omega_{out}$ for the outer vacuum,
and $Q_{BRST}$ for the auxiliary charge. Neither vacuum is identified with an inner
ground/squeezed state without a theorem. BRST observable cohomology and the OS null-space
quotient serve different purposes and cannot replace one another.

### Corrections that govern the route

**N — finite coordinate rotation is not Euclidean field invariance.**
`EuclideanFock4D.mehlerMeasure4D = gaussianE 4` is a law on $\mathbb R^4$.
`mehler4D_O4_invariant` proves orthogonal invariance of that law, not invariance of a
random connection $A_\mu(x)$ under spacetime translations and rotations. Specify the
covariance and the action on spacetime, vector and colour indices. Rotational symmetry
alone also says nothing about reflection positivity of that covariance.

**N — nesting, scale decomposition and direct sum are different constructions.**
The manuscript's nested lift is $H=d\Gamma(h)$ with an interacting **inner** $h$.
A decomposition $\mathfrak h=\bigoplus_k\mathfrak h_k$ has a Fock tensor-factorization
only after the appropriate Fock functor and reference vacua have been specified.
It does not identify $\bigoplus_k\mathcal F_k$ with
$\bigotimes_k\mathcal F_k$ or with recursively nested Fock space. In the current
`BalabanRG` model, `Sector k` is the same $64$-dimensional real coordinate space at
every scale. `blockAveragingOp` projects the four component slots at each cell to
their common value; it is not yet physical gauge-covariant spatial block averaging.

**N — contraction does not preserve Born normalization.** Conditional expectation is
an $L^2$ contraction, not generally an isometry. For a coarse sigma-algebra $\mathcal G$,
the coarse density of $|\Psi|^2d\gamma$ is
$E_\gamma[|\Psi|^2\mid\mathcal G]$, not
$|E_\gamma[\Psi\mid\mathcal G]|^2$. The positive square-root amplitude update is
generally nonlinear. RG pushforward is linear on measures, while an effective-action
update involving a logarithm is not linear on amplitudes.

**N — commutation with reflection alone does not preserve RP.** To push RP through a
coarse map, prove its pullback sends the coarse positive-time algebra into the fine
positive-time algebra, intertwines reflection and preserves products/conjugation; then
identify the coarse state with the pushed-forward state. A bounded vector operator
$Q\Theta=\Theta Q$ alone supplies none of these state identities.

**N — the Wick obstruction is not a degree-three threshold.** The historical example
$\theta X=-X$ gives $E[(\theta X)X]=-E[X^2]<0$ already at degree one. For a centred
real Gaussian with compatible reflection symmetry, positivity of the **reflected
covariance on positive-time test functions** supports RP on the whole polynomial
algebra via Wick/chaos decomposition. There is no universal failure at degree three.
For ordinary quadratic monomials retain the same-half/disconnected contractions;
a formula containing only cross-plane contractions needs Wick ordering or centering.
The Markov/Feynman–Kac route remains a useful sufficient proof, not the only possible one.

**N — full-algebra RP is stronger than physical OS positivity.**
`ReflectionPositivity.IsReflectionPositive` quantifies over every `Observable`.
`OSReconstruction.OSState` consumes that stronger predicate and `Hphys` quotients the
full algebra. `ReflectionKernel.mk_thetaObs_eq_mk` shows the reflection becomes the
identity in that quotient under its hypotheses. Physical reconstruction instead uses
$\mathcal A_+$ only. Do not feed a theorem of RP **on** `PositiveTimeAlgebra` into
`OSState` as if it proved the stronger predicate. Reuse the quotient proof patterns
after restricting their carrier and hypotheses.

**N — Euclidean time is a forward semigroup.** Contractivity at every real time plus
the group law forces isometries; adding self-adjoint transfer maps makes the family
trivial (`TransferSelfAdjoint.physEvolCompletion_eq_one`). Use $\tau\ge0$,
$P(\tau)=e^{-\tau H}$ and the right generator $A=-H$, not a two-sided contractive
group or Stone's unitary-group converse. Real-time unitarity comes after identifying $H$.

### E0 — select and identify the concrete Euclidean model

Start with a finite-volume lattice benchmark with a specified compact gauge group,
links, plaquettes, boundary conditions and normalized Haar product measure. Define
$\mu_{a,L}=Z_{a,L}^{-1}e^{-S_{a,L}}\nu_{a,L}$ and the gauge-invariant observable
algebra. Separate this from a scalar Gaussian benchmark with a chosen covariance $C$.
A Gaussian coordinate prior does not by itself define the interacting measure or its
gauge-invariant correlations; a gauge-fixed vector Gaussian need not be RP on all components.

For a Mehler description choose a nuclear test space/cylindrical coordinate system,
a positive covariance and compatible finite marginals. If using a distribution-valued
field, prove the realization there. Standard independent Gaussian coordinates do not
produce identity-covariance Gaussian probability on $\ell^2$, and a pointwise “uniform
measure on the unit sphere of a Hilbert space” is not the needed construction.
At each finite cutoff establish the unitary chart and field identities. Hermite **functions**
need their Gaussian weights and normalization; bare Hermite polynomials are not an
orthonormal basis for Lebesgue $L^2$. A Gaussian chart does not add an oscillator
confinement term to the physical Hamiltonian (softmodes S0).

**Acceptance:** a model contract giving the measure, expectation, reflection, positive-time
test functions, field/loop observables and embeddings. Distinguish spatial volume $L$,
lattice spacing $a$, basis cutoff $\Lambda$ and RG depth $n$.

### E1 — assemble finite-model RP, then preserve it under actual coarse maps

Use a site-reflection/conditional-boundary benchmark first. With past/future conditional
laws matched by reflection, prove

$$d\mu(z,y_-,y_+)=d\rho(z)\,d\nu_z(y_-)\,d\nu_z(y_+),\qquad
\omega((\Theta F)F)=\int\left|\int F(z,y)\,d\nu_z(y)\right|^2d\rho(z)\ge0.$$

Supply integrability, positivity and normalization of the boundary law. For link-plane
reflections or actions with cross-plane plaquettes, prove the appropriate positive-kernel
or character-expansion identity; pointwise positivity of a Boltzmann weight is insufficient.
Transport vector signs for $A_0$ and reversal/inversion of oriented links explicitly.

Existing building blocks are `LatticeFreeField`, `HalfSpaceSplit`, `WilsonLattice`,
`WilsonLinkLattice`, `WilsonPastClass`, `HaarReference`, `GFFNormalization` and
`WilsonPartition` under `BookProof/ReflectionPositivity/`. Read their actual parameters:
`WilsonLinkLattice.Site L = Fin 3 → Fin L` is a three-coordinate box, not yet a
four-dimensional Euclidean gauge lattice. `HaarReference` is parametric in a compact
group and a measurable matrix representation; instantiate the intended non-abelian group
and prove the required a.e. unitarity/integrability. `WilsonPartition` proves normalized
probability and RP under its reference-probability and holonomy hypotheses. A closed-form
partition function is unnecessary; $0<Z<\infty$ suffices.

**Acceptance:** RP on the actual positive-time observable algebra for the normalized
finite model, including its concrete measure/geometry identification. Then prove each RG
pullback satisfies the algebra, support and state identities above. No full-algebra RP
assumption is allowed as a substitute.

### E2 — construct continuum expectations with the right convergence topology

Define coarse-graining maps and gauge transport before invoking Bałaban-type estimates.
State the bare coupling/counterterm trajectory and the precise norm in which the
small-field/large-field polymer estimate is sought. The existing
`BalabanRG.Convergence.balaban_rg_convergence` is the implication from a summable
increment estimate to a limit; it does not prove that estimate for Yang–Mills RG.

Prefer compatible expectations/Schwinger distributions on a common test algebra, with
tightness and uniform moment bounds where needed. A global amplitude $\Psi_\infty$ in
one reference $L^2(\gamma)$ is optional and needs absolute-continuity and embedding
proofs. Infinite-volume or continuum laws may be singular with respect to that reference.
Even when $\Psi_n\to\Psi$ in $L^2$ and all are normalized, the resulting $L^1$ density
convergence controls bounded observables; polynomial observables need additional moment
or uniform-integrability bounds. An unspecified vector norm limit does not imply all
Schwinger-function limits.

Pass RP through convergence of each reflected product $(\Theta F)G$ on a common
positive-time algebra. Prove limiting Euclidean translation/rotation covariance,
regularity and nontriviality separately; a finite regulator generally preserves only a
discrete subgroup. State which order of UV and thermodynamic limits is justified and
which constants are uniform. Existence and uniqueness of the limit for one Cauchy
sequence is not universality across regulators, boundary conditions or RG trajectories.

**Acceptance:** a normalized nontrivial limiting functional with half-space RP and
documented moment, covariance and continuity estimates. UV stability alone is not an
infrared clustering estimate. Keep the missing analytic estimates as named hypotheses.

### E3 — reconstruct on the positive-time algebra and build forward evolution

Construct the complex sesquilinear form
$\langle F,G\rangle_{OS}=\omega((\Theta F)G)$ on $\mathcal A_+$, its null
**subspace** $\mathcal N$, and the completion of $\mathcal A_+/\mathcal N$.
Do not call $\mathcal N$ an algebra ideal without proving ideal stability. Include the
unit to define $\Omega_{OS}=[1]$ and prove $\|\Omega_{OS}\|=1$.
The existing real bilinear quotient/completion is a reusable prototype; complexification
and the restriction to the half-space carrier remain explicit bridge work.

On positive-time smearings prove forward translation preserves support and the null
space. Derive symmetry, contractivity and strong continuity from the concrete state's
translation/reflection/regularity properties. These are inputs beyond RP in isolation.
Require $P(0)=I$, $P(s+t)=P(s)P(t)$ for $s,t\ge0$ and $P(t)^*=P(t)$.
Construct the dense right-generator domain, prove its range condition and identify the
positive self-adjoint $H=-A$. Use the symmetric contraction-semigroup theorem or a
verified resolvent/multiplication model; Hille–Yosida without symmetry gives a generator,
not automatically a self-adjoint Hamiltonian.

**Newer existing results:** `TransferSemigroupRight` and `SemigroupGenerator` provide
forward evolution, right derivatives, closedness/dissipativity and a resolvent estimate
under their bundled hypotheses. `MultiplierGenerator` and `MultiplierSelfAdjoint`
construct a positive self-adjoint `hamiltonianMulModel`, its resolvent and transfer flow
**given `MulModel`**. That bundle assumes a nonnegative measurable density, an isometry
onto a dense range in $L^2(\nu)$ and the exponential multiplier law. Producing those data
for the concrete half-space theory is still required. Thus “no generator exists anywhere
in the corpus” is stale, while “the physical interacting generator is identified” is unproved.

**2026-11-09:** `HalfSpaceState` / `HalfSpaceHilbert` now cover the half-space half of this
list — the quotient of `𝔄₊` with `Ω_OS = [1]`, `‖Ω_OS‖ = 1`, forward support and null-space
preservation (as hypotheses), and `P(0)=I`, `P(s+t)=P(s)P(t)`, `P(t)*=P(t)` with strong
continuity at `0⁺` on the completion. The concrete state (a measure on the lattice
configurations) and the generator domain/resolvent on `𝔄₊/𝔑₊` are still open, and the
constructed space is real.

**Acceptance:** a half-space state/space and a nontrivial strongly continuous symmetric
forward contraction semigroup, with its generator domain and resolvent identified.
Full Wightman reconstruction additionally needs the selected OS theorem's regularity,
Euclidean covariance, permutation/locality and clustering hypotheses, distributional
fields and analytic continuation. A Hilbert space and a heat semigroup alone do not
establish Lorentz covariance or locality.

### E4 — identify the reconstructed theory with the manuscript's nested fields

Construct an isometry with dense range $U:\mathcal H_{OS}\to\mathcal F_{out}$
(or a specified physical cyclic subspace), prove vacuum alignment, and intertwine
the smeared observable representations and heat semigroups:

$$U\Omega_{OS}=\Omega_{out},\qquad
UP(\tau)=e^{-\tau H_{out}}U\quad(\tau\ge0),\qquad
H_{out}=d\Gamma(h_F).$$

`OSReconstruction/FockIntertwining.lean` defines `OsFockBridge` and proves consequences
of an assumed flow intertwiner. It does not construct this $U$. A real-linear bridge
also needs complex-structure compatibility before claiming a complex unitary field
identification. Gauge fixing or agreement of formal Hamiltonian expressions does not
identify the spaces, their domains, vacua or correlations. If the Euclidean construction
is not equivalent to this nested model, retain the two results as separate theories.

Keep inner composition and outer multiplication separate:
$d\Gamma(B^2)\ne d\Gamma(B)^2$ in general; likewise
$d\Gamma(I)=N_{out}$ while its square is $N_{out}^2$.
The inner interactions remain inside $h_F$ when its outer lift is quadratic. A density
for a non-Gaussian interacting measure does not become a free Gaussian field merely
because its Hilbert space has a Fock representation.

**Acceptance:** the concrete unitary/observable/flow diagram, or an explicit statement
that the bridge remains conditional. Do not transfer a gap or clustering rate before it.

### E5 — prove an infrared gap and only then attach certified numerics

Choose the spectral target and vacuum first. For an OS vacuum gap, prove
$\ker H=\mathbb C\Omega_{OS}$ (or state the full ground projection $P_0$) and

$$\|e^{-\tau H}(I-P_0)\|\le e^{-m\tau},\qquad m>0.$$

Equivalently, after constructing the spectral measure, prove it has no support in
$(0,m)$ off the ground space. Pointwise strong convergence of the heat flow to $P_0$
does not give operator-norm convergence or a gap: positive masses can accumulate at zero.
`MultiplierSelfAdjoint` proves both the conditional norm-decay theorem and no-gap
obstructions in the multiplier model. Its symbol gap is an analytic input, not a result
about the Yang–Mills measure.

To infer a gap from clustering require a uniform estimate on a dense vacuum-complement
class, controlled by Hilbert norms, not decay of one chosen two-point function. With
a self-adjoint generator and a fixed finite prefactor, large-time decay excludes spectral
support below $m$. Do not discard that prefactor in a small-time difference quotient.
`Clustering` and `KallenLehmannModel` supply conditional Laplace-transform machinery;
the interacting infrared estimate remains open. Scalar radial time/space transfer requires
actual limiting $O(4)$ covariance; tensor/loop observables must be transformed with it.
The Mehler coordinate rotation theorem alone cannot supply that hypothesis.

If using softmodes S2 to prove $h_F\ge mI$ on **all** inner states, its outer lift
gives the outer-vacuum bound. An inner excitation gap above $E_0$ instead needs the
correct ground projection and the E4 identification. Shifting $h_F\mapsto h_F+\mu I$
adds $\mu N_{out}$, changes the model and does not manufacture physical inner clustering.
Never subtract two lower spectral bounds; use an independent ground upper bound or
direct coercivity. The occupation-diagonal surrogate still needs its physical form bridge.

For Hashimoto set $A=-H$ (or a declared time-rescaled version), so
$X_\gamma=(\gamma I+H)^{-1}$ has norm at most $1/\gamma$ for $\gamma>0$.
For the paper's Theorem 4.1 retain $\gamma_j=N_{shift}-sj>0$,
$m_{Krylov}<N_{shift}/s$, matrix invertibility, numerical-range and function-admissibility
hypotheses, and the full rational approximation factor:

$$\|\phi_k(A)v-u_{m_{Krylov}}\|\le2C\|v\|e^{-s m_{Krylov}}
\inf_{r\in\mathcal R^{SIRK}_{m_{Krylov}-1}}
\|f_{k,N_{shift}}-r\|_{\infty,\Sigma}.$$

The exponential alone is not an unlimited-depth convergence bound with fixed shift budget.
Carry rational approximation, inexact solve, rounding, basis-tail and continuum errors
separately. A solve defect $r$ yields inverse-action error at most $\|r\|/\gamma$;
a compressed-matrix eigenvector residual still omits $(I-P_\Lambda)Hu$.
Resolvent compression is not the inverse of Hamiltonian compression in general.
Strong resolvent convergence does not turn a finite gap into a continuum gap without
the independent uniform exclusion/form estimate. Keep the mass-gap sector gate §M4.9
in `CURRENT_WORK_ORDER.md` before any continuum interpretation of certificates.

**Temple acceptance:** an operator/domain/sector identification, normalized trial vector,
full residual $\eta$, and independently justified $\beta>\theta$ excluding the rest
of that sector's spectrum. Then $\theta-\eta^2/(\beta-\theta)\le E_0\le\theta$.
The operator-function approximation theorem does not supply that exclusion.

### Execution and validation

| Gate | Existing reusable content | Missing concrete input |
|---|---|---|
| E0 | Gaussian laws, Hermite bases | Euclidean field law and chart |
| E1 | Kernel RP, lattice splits, Haar/partition results | One matched 4D gauge model |
| E2 | Summable increments imply convergence | Actual RG estimates and limits |
| E3 | Half-space state/quotient (`HalfSpaceState`), forward semigroup (`HalfSpaceHilbert`), half-space generator with `H = −A` (`HalfSpaceGenerator`), finite-volume Gibbs state and its measure on the split lattice (`HalfSpaceFreeState`), complexification, complex OS form and `HilbertSpace ℂ` carrier (`HalfSpaceComplex`), quotients, multiplier generators | The exponential `e^{−τH}`, an infinite-volume state |
| E4 | `OsFockBridge` consequences | Concrete field/vacuum/flow bridge |
| E5 | Conditional clustering and certificate receivers | Uniform infrared exclusion |

Execute **E0 → E1 → E2 → E3 → E4 → E5** as dependency gates; abstract E3 work and E5
error bookkeeping can progress before the continuum estimates. The first concrete task
is a **half-space state/quotient interface** and a finite-model measure/RP contract;
reuse the existing conditional machinery rather than add another full-algebra wrapper.
Proposed new modules, not existing proofs, are
`BookProof/OSReconstruction/HalfSpaceState.lean` and
`BookProof/OSReconstruction/HalfSpaceHilbert.lean`.

**2026-11-09: both modules exist and build** (`lake build BookProof`).
`HalfSpaceState` supplies the half-space state (`HalfSpaceState`: `θ`-invariant linear
functional, reflection positive on `PositiveTimeAlgebra` only, `ω 1 = 1`), the OS form
`hsBilin` on `𝔄₊ × 𝔄₊` with bilinearity, symmetry (from `θ`-invariance, not positivity),
quadratic expansion and Cauchy–Schwarz, the null **subspace** `HsRadical` (no ideal claim)
with `mem_hsRadical_of_self_eq_zero` and descent, the quotient `HsSpace`, its inner-product
structure, the completion `Hhalf`, and the vacuum `hsVacuum = [1]` with `hsVacuum_norm`.
`HalfSpaceHilbert` supplies `PreservesPositiveTime`, the restricted evolution `hsEvol`, the
one-sided hypothesis `HsHinv`, `hsRadical_invariant` (forward translation preserves the null
space), the descended `hsQuotMap` with contractivity, `P(0) = I`, `P(s+t) = P(s)P(t)`, the
completion `hsEvolCompletion`, strong continuity at `0⁺` from matrix-element continuity, and
`hsEvolCompletion_isSelfAdjoint` — **`P(τ)* = P(τ)`** — from the dense two-point symmetry
hypothesis `HsSymmetric`.

**2026-11-09, follow-up (three modules, all building):** the generator/state/complexification
work listed as missing above now exists.

* `HalfSpaceGenerator` **ports** `SemigroupGenerator` to the half-space carrier: the difference
  quotient `hsDiffQuot`, the one-sided domain `HsHasGen`/`hsGenDomain`/`hsGenValue`, the
  restricted-evolution estimates `hsEvolCompletionFun_zero`, `dist_hsEvolCompletionFun_le`
  (contraction), `continuousOn_hsEvolCompletionFun`, `intervalIntegrable_hsEvolCompletionFun`,
  `hsEvol_sub_eq_integral` and `tendsto_average_hsEvol` (strong continuity in integral form),
  then closedness (`hsGenerator_isClosed`), dissipativity
  (`hsGenerator_inner_le_zero`), the resolvent bound `hsGenerator_resolvent_bound` and
  injectivity, and finally the identification `hsGenerator_eq_neg` / `hsGenerator_inner_eq_neg`:
  **`H = −A`** on the dense domain, self-adjointness carried by the symmetric-contraction
  hypotheses. The `H = −A` identification is conditional on
  `∀ z, HasDerivWithinAt (fun τ => hsEvolCompletionFun Λ hT hinv τ z) (-(H z)) (Ioi 0) 0`, the
  local form of `P(τ) = e^{−τH}`; the exponential itself is not constructed.
* `HalfSpaceFreeState` **instantiates `HalfSpaceState` with a concrete state**: the finite-volume
  Gibbs functional `gibbsFun (V : GibbsVolume)` on the block lattice, with the configuration
  split `Config ≃ (HalfIdx → ℝ) × (HalfIdx → ℝ)` (`cellsPerBlock = 16 = 8 + 8`, no reflection
  slice, so `flipCell` is the half swap), `dependsOn_posTimeCoords_iff` (`𝔄₊` is exactly the
  observables that do not see the negative half), `gibbsFun_one` (`ω 1 = 1`),
  `gibbs_reflectionPositive` from the **finite-volume Feynman–Kac identity as a square**
  `gibbsFun_osForm : ω(θF·F) = (Σ_x ρ(x) F(x,0))²`, and the packaged `gibbsHalfSpaceState`
  with `gibbsVacuum_norm`, and **the state as a genuine measure on `Config`**: `gibbsAtom`,
  `gibbsMeasure` (the finitely supported law `Σ_{x,y} w x · w y · δ_{(x,y)}`), `gibbsMeasure_univ`
  and the `IsProbabilityMeasure` instance, the domination lemmas `gibbsAtom_le_row`/`gibbsRow_le`/
  `gibbsAtom_le`, and `integral_gibbsMeasure : ∫ F d(gibbsMeasure V) = gibbsFun V F` on the
  integrable observables — so the Gibbs functional is the integral state of its measure. The grid
  weights are the samples of the Gaussian density, and `freeFieldMeasure` (the product Gaussian
  `∏ N(0, 1/2)`) is recorded as the block-lattice reference law *without* an identification.
* `HalfSpaceComplex` **complexifies `Hhalf` and restates the OS form as a complex sesquilinear
  form**: carrier `HhalfC Λ = Hhalf Λ × Hhalf Λ` with `ofReal`/`ofImag`, the complex structure
  `cSMul (a+bi)(x+iy) = (ax−by) + i(bx+ay)` and its `Module ℂ` instance; the complex OS form
  `hsComplexForm z w = ⟪z₁,w₁⟫ + ⟪z₂,w₂⟫ + i(⟪z₁,w₂⟫ − ⟪z₂,w₁⟫)`, with the `ℂ`-sesquilinear
  laws (`hsComplexForm_smul_left` in Mathlib's `c̄ ⟪z,w⟫` convention, `hsComplexForm_smul_right`),
  conjugate symmetry `hsComplexForm_conj_symm`, realism of the diagonal
  `hsComplexForm_self_re : (⟪z,z⟫).re = ‖z₁‖² + ‖z₂‖²` with `hsComplexForm_self_nonneg`, and
  definiteness `hsComplexForm_self_eq_zero_iff`; `hsComplexForm_ofReal` records that the real
  OS form is the restriction of the complex one; `hsComplexPreCore`, `hsComplexSeminormed` and
  `instInnerProductSpaceHhalfC` register the complex inner product space; and **the carrier is
  complete**, so `instHilbertSpaceHhalfC : HilbertSpace ℂ (HhalfC Λ)` is attached. The proof is
  for the *core* (ℓ²) norm, not the product max norm: `HhalfC` is a `def`, so no `Prod` instance
  can compete, and `norm_sq_hhalfC : ‖z‖² = ‖z₁‖² + ‖z₂‖²` makes the coordinate bounds
  `norm_fst_le`/`norm_snd_le` and the ℓ¹ reassembly `norm_le_add_coord` available;
  `hhalfC_complete` takes coordinate Cauchy limits from the completeness of `Hhalf` and rebuilds
  the limit with `norm_eq_zero_iff_hhalfC`.

Still missing at E3: the exponential `e^{−τH}` (the generator identification is conditional on
its defining derivative), and an infinite-volume/continuum state — `gibbsMeasure` is supported on
the declared finite grid and is not identified with `freeFieldMeasure`. Separability of the
complexified carrier, support preservation, contractivity and two-point symmetry remain named
hypotheses, as `HinvRight` and `∀ τ, IsSelfAdjoint (P τ)` already are in the corpus.

Use the local `lean-toolchain` (currently v4.28.0). A proof port from another toolchain
must compile here before it is counted as implemented; verify sibling paths rather than
relying on the historical `../timepiee331/` spelling. MM0 export is a separate deliverable
requiring supported statement and proof translation; emitting theorems as new axioms is
not proof conversion.

For a later implementation, build affected modules, audit final theorem binders and
axioms, and distinguish abstract tests from instantiations of the interacting model.
For this documentation-only revision, check relative links, whitespace and doc-index
freshness. No numerical certificate, Lean compilation or book-rendering result is claimed.

## Historical architecture and status (2026-10-29 to 2026-11-05)

The revised work order above controls the interpretation of all completion claims below.
In particular the full-algebra OS receiver, the Wick degree-threshold claim, the old
generator absence claims and the proposed softmodes separation are superseded by the
specific corrections and dependencies above.

The original proposal was a modular research plan for formalizing **Bałaban’s constructive
Euclidean approach** using the **nested Fock-space framework**, constructing a Euclidean
statistical theory before deriving its Hamiltonian by reflection-positive reconstruction.

Note that you can produce the proofs in any version  of Lean4 it is more convenient to you , you can also use the the 4.33.1 version of these proofs in ../timepiee331/ , since the end goal is to convert everything to MM0.

---

### Conceptual Architecture

```
                    4D Euclidean Spacetime (No Hamiltonian)
            ┌────────────────────────────────────────────────────────┐
            │  Configuration space: A ∈ S'(ℝ⁴, 𝔰𝔲(N))                │
            │  Prior: 4D Rotation-Invariant Mehler / Gaussian       │
            │  Nested Fock-Space: ℱ_E = ⨂_{scale k} ℱ_k              │
            └───────────────────────────┬────────────────────────────┘
                                        │
                         Bałaban Multiscale RG Operators
                                        │
            ┌───────────────────────────▼────────────────────────────┐
            │  Block-averaging: Q_k : ℱ_k → ℱ_{k+1}                  │
            │  State sequence: Ψ_N = ⨂_{k=0}^N Q_k Ψ_0              │
            │  Convergence in ℱ_E: Ψ_∞ = lim_{N→∞} Ψ_N (Cauchy)       │
            └───────────────────────────┬────────────────────────────┘
                                        │
                          Reflection Positivity Check
                                        │
            ┌───────────────────────────▼────────────────────────────┐
            │  Time-reflection: θ(x₀, x) = (-x₀, x)                  │
            │  Half-space algebra 𝒜₊ (x₀ > 0)                        │
            │  Theorem: ⟨Ψ_∞, π(θ(F)* F) Ψ_∞⟩ ≥ 0                    │
            └───────────────────────────┬────────────────────────────┘
                                        │
                       Osterwalder–Schrader Reconstruction
                                        │
            ┌───────────────────────────▼────────────────────────────┐
            │  Physical Hilbert Space: ℋ_Mink = 𝒜₊ / 𝒩               │
            │  Emergent Hamiltonian: e^{-τ H} [F] = [T_τ F]          │
            │  Relativistic Wightman Theory on ℝ^{1,3}               │
            └────────────────────────────────────────────────────────┘
```

---

### Phase 1: 4D Euclidean Nested Fock Space & $O(4)$ Invariant Measure
**Goal:** Define the 4D Euclidean field substrate without breaking space and time into a $3+1$ split, using the Mehler measure on an infinite-dimensional sphere.

#### 1.1. 4D Euclidean Configuration Core
* In Hamiltonian field theory, one works with $(A_i, \pi_i)$ on $\mathbb{R}^3$ [1.1]. In the 4D Euclidean theory, the field coordinate is a 4-vector $A_\mu(x) = (A_0, A_1, A_2, A_3)(x)$ on $\mathbb{R}^4$ taking values in $\mathfrak{su}(N)$.
* Construct the configuration space using the 4D product Hermite basis on $L^2(\mathbb{R}^4 \otimes \mathfrak{su}(N))$:
  $$\phi_{\alpha, \mu, a}(x) = H_{\alpha_0}(x_0) H_{\alpha_1}(x_1) H_{\alpha_2}(x_2) H_{\alpha_3}(x_3) T_a$$
* **Lean 4 Target File:** `BookProof/EuclideanFock4D/CoreBasis.lean`
  ```lean
  def EuclideanHermiteBasis4D (N : ℕ) : OrthonormalBasis (ℕ⁴ × Fin 4 × Fin (N^2 - 1)) ℝ (L2 (ℝ⁴ × Fin 4 × Fin (N^2 - 1)))
  ```

#### 1.2. The 4D Mehler Measure and $O(4)$ Invariance
* Generalize `PhysHSGaussian` [1.1] to dimension 4: Define the free Euclidean Gaussian measure $d\gamma_0(A)$ on the sphere $S^\infty$.
* Prove that $d\gamma_0$ is invariant under the full 4D Euclidean rotation/reflection group $O(4)$:
  ```lean
  theorem mehler4D_O4_invariant (R : EuclideanIsometry 4) :
    Measure.map (liftIsometry R) (mehlerMeasure4D) = mehlerMeasure4D
  ```

---

### Phase 2: Bałaban Multiscale RG as Nested Fock Operators
**Goal:** Translate Bałaban’s functional block-spin transformations into bounded linear operators acting between sectors of a nested Fock space.

#### 2.1. Scale Decomposition of the Nested Fock Space
* Instead of treating the multiscale expansion as an infinite sequence of unregularized path integrals, define the total Euclidean space as a **nested, graded Fock space over scales**:
  $$\mathcal{F}_{\text{total}} = \bigoplus_{k=0}^\infty \mathcal{F}_k, \quad \text{where } \mathcal{F}_k \cong \Gamma^s(L^2(\text{Block}_k \times \mathfrak{su}(N)))$$
* Scale $k$ corresponds to effective lattice cells of volume $L^{4k} a^4$.
* **Lean 4 Target File:** `BookProof/BalabanRG/MultiscaleSpace.lean`

#### 2.2. The Block-Averaging Operator
* Bałaban’s block transformation $Q$ averages gauge fields over a 4D hypercube $B_k(y)$ of size $L$:
  $$(Q A)_\mu(y) = \frac{1}{L^4} \int_{B_k(y)} A_\mu(x) \, dx + \text{gauge-connection corrections}$$
* In the wave-function parametrization, this averaging is an **isometric conditional expectation operator**:
  $$\mathbb{Q}_k : \mathcal{F}_k \to \mathcal{F}_{k+1}$$
* Prove that $\mathbb{Q}_k$ is bounded and preserves the Born probability normalization:
  ```lean
  def blockAveragingOp (k : ℕ) : ℱ k →L[ℝ] ℱ (k + 1)
  theorem blockAveragingOp_norm_le (k : ℕ) : ‖blockAveragingOp k‖ ≤ 1
  ```

#### 2.3. The State Sequence and Continuum Convergence
* The regularized state at cutoff $N$ (lattice spacing $a = L^{-N}$) is the product wave-function:
  $$\Psi_N = \left( \prod_{k=0}^{N-1} \mathbb{Q}_k \right) \Psi_{\text{bare}}$$
* Formalize Bałaban’s small-field/large-field polymer contraction as an operator Cauchy estimate:
  $$\|\Psi_{N+1} - \Psi_N\|_{\mathcal{F}_{\text{total}}} \le C \cdot L^{-\epsilon N}$$
* By completeness of the Hilbert space (`completeSpace_iff_summable_norm`) [1.1], deduce that $\Psi_N$ converges to a **unique continuum state vector $\Psi_\infty \in \mathcal{F}_{\text{total}}$**:
  ```lean
  theorem balaban_state_cauchy : CauchySeq (fun N => psiSeq N)
  theorem balaban_continuum_state_exists : ∃ (Ψ_∞ : ℱ_total), Tendsto psiSeq atTop (𝓝 Ψ_∞)
  ```

---

### Phase 3: Reflection Positivity (Osterwalder–Schrader Positivity)
**Goal:** Prove that the 4D static measure $d\mu_\infty(A) = |\Psi_\infty(A)|^2$ satisfies reflection positivity across the $x_0 = 0$ hyperplane.

#### 3.1. Euclidean Time Reflection
* Define the reflection operator $\theta$ on $\mathbb{R}^4$:
  $$\theta(x_0, x_1, x_2, x_3) = (-x_0, x_1, x_2, x_3)$$
* On the gauge connection, $\theta$ acts with the proper parity sign on the temporal component:
  $$(\theta A)_0(x) = -A_0(\theta x), \quad (\theta A)_j(x) = A_j(\theta x) \quad (j=1,2,3)$$
* Lift $\theta$ to a unitary involution $\Theta$ on $\mathcal{F}_{\text{total}}$:
  ```lean
  def timeReflection : ℱ_total →L[ℝ] ℱ_total
  theorem timeReflection_involution : timeReflection ∘L timeReflection = ContinuousLinearMap.id ℝ ℱ_total
  ```

#### 3.2. The Half-Space Observable Algebra $\mathcal{A}_+$
* Define the subalgebra $\mathcal{A}_+$ of cylindrical observables supported strictly on the positive Euclidean time half-space:
  $$\operatorname{supp}(F) \subset \{x \in \mathbb{R}^4 : x_0 > 0\}$$
* **Lean 4 Target File:** `BookProof/ReflectionPositivity/HalfSpaceAlgebra.lean`
  ```lean
  def PositiveTimeAlgebra : Subalgebra ℝ (CylindricalObservables ℱ_total)
  ```

#### 3.3. Proof of Reflection Positivity
* For the bare Wilson lattice action, reflection positivity across site/link boundaries is an established algebraic identity:
  $$\langle \theta(F) F \rangle_a \ge 0 \quad \forall F \in \mathcal{A}_{+, a}$$
* Prove that Bałaban's block-spin averaging $\mathbb{Q}_k$ commutes with time reflection:
  $$\Theta \mathbb{Q}_k = \mathbb{Q}_k \Theta$$
* Conclude that reflection positivity is preserved at every RG step $k$, and passes to the continuum limit:
  ```lean
  theorem reflection_positivity_continuum (F : PositiveTimeAlgebra) :
    0 ≤ innerProduct ℱ_total (timeReflection (observableOp F Ψ_∞)) (observableOp F Ψ_∞)
  ```

---

### Phase 4: Wick Rotation and Osterwalder–Schrader Reconstruction
**Goal:** Reconstruct the physical Minkowski Hilbert space $\mathcal{H}_{\text{Mink}}$, the vacuum state $\Omega$, and the physical Hamiltonian $H_{\text{phys}}$ directly from the reflective Euclidean state $\Psi_\infty$.

#### 4.1. Construction of the Physical Minkowski Hilbert Space
* Define the positive semi-definite form on $\mathcal{A}_+$:
  $$\langle F_1, F_2 \rangle_{\text{phys}} := \langle \Psi_\infty, \pi(\theta(F_1)^* F_2) \Psi_\infty \rangle$$
* Define the null space:
  $$\mathcal{N} = \{ F \in \mathcal{A}_+ : \langle F, F \rangle_{\text{phys}} = 0 \}$$
* Define the physical Minkowski space as the metric completion of the quotient:
  $$\mathcal{H}_{\text{Mink}} := \overline{\mathcal{A}_+ / \mathcal{N}}$$
* **Lean 4 Target File:** `BookProof/OSReconstruction/PhysicalHilbertSpace.lean`
  ```lean
  def PhysicalNullSpace : Submodule ℝ PositiveTimeAlgebra
  def PhysicalPreHilbert := PositiveTimeAlgebra ⧸ PhysicalNullSpace
  def MinkowskiHilbertSpace := UniformSpace.Completion PhysicalPreHilbert
  ```

#### 4.2. Emergence of the Physical Hamiltonian $H_{\text{phys}}$
* Notice that **no Hamiltonian was postulated in 4D Euclidean space**. The physical Hamiltonian emerges through the Euclidean time translation semigroup:
  $$T_\tau(x_0, \mathbf{x}) = (x_0 + \tau, \mathbf{x}) \quad (\tau \ge 0)$$
* For any $F \in \mathcal{A}_+$ and $\tau \ge 0$, $T_\tau F \in \mathcal{A}_+$.
* By reflection positivity and the Cauchy–Schwarz inequality, $T_\tau$ induces a symmetric, contraction semigroup on $\mathcal{H}_{\text{Mink}}$:
  $$P(\tau)[F] = [T_\tau F], \quad \|P(\tau)\| \le 1$$
* Using the Hille–Yosida theorem (or Stone's theorem for symmetric semigroups, already formalizable from `BookProof.ChapterStoneResolvent` [1.1]):
  $$P(\tau) = e^{-\tau H_{\text{phys}}}$$
* Deduce that the infinitesimal generator $H_{\text{phys}}$ is **automatically self-adjoint and positive**:
  ```lean
  theorem emergent_hamiltonian_selfAdjoint : IsSelfAdjoint H_phys
  theorem emergent_hamiltonian_nonnegative (ψ : MinkowskiHilbertSpace) :
    0 ≤ innerProduct MinkowskiHilbertSpace ψ (H_phys ψ)
  ```

---

### Phase 5: Connecting the Mass Gap
With the 4D Euclidean theory reconstructed into Minkowski spacetime, the mass gap is the spectral gap of the emergent operator $H_{\text{phys}}$:

1. **Spatial vs. Temporal Clustering:**
   Because the Euclidean theory has full $O(4)$ invariance (from Phase 1), exponential decay of Schwinger functions in the Euclidean time direction $\tau$:
   $$\langle \mathcal{O}(\tau, \mathbf{0}) \mathcal{O}(0, \mathbf{0}) \rangle - \langle \mathcal{O} \rangle^2 \le C e^{-m \tau}$$
   is strictly equivalent to exponential spatial decay at distance $r = |\mathbf{x}|$.
2. **Transfer to SIRK / Temple:**
   The emergent operator $H_{\text{phys}}$ on the reconstructed space $\mathcal{H}_{\text{Mink}}$ now serves as the input to the existing `BookProof.SirkCertifiedGap` pipeline [1.1], allowing certified interval calculation of the lowest mass $m > 0$.

---

### Lean 4 File Hierarchy for the Project

| Module Path | Primary Theorem / Definition | Proof Mechanism |
| :--- | :--- | :--- |
| `BookProof/EuclideanFock4D/CoreBasis.lean` | `EuclideanHermiteBasis4D` | 4D product Hermite functions [1.1] |
| `BookProof/EuclideanFock4D/MehlerMeasure.lean` | `mehler4D_O4_invariant` | Projective limit of Gaussians on $S^\infty$ [1.1] |
| `BookProof/BalabanRG/BlockOperator.lean` | `blockAveragingOp` | Gauge-covariant kernel on blocks |
| `BookProof/BalabanRG/Convergence.lean` | `balaban_continuum_state_exists` | Cauchy sequence in $\mathcal{F}_{\text{total}}$ via polymer bound |
| `BookProof/ReflectionPositivity/Involution.lean` | `timeReflection` | Parity lift: $A_0 \mapsto -A_0, A_j \mapsto A_j$ |
| `BookProof/ReflectionPositivity/Proof.lean` | `reflection_positivity_continuum` | $\mathbb{Q}_k \Theta = \Theta \mathbb{Q}_k$ + lattice OS identity |
| `BookProof/OSReconstruction/PhysicalSpace.lean` | `MinkowskiHilbertSpace` | Quotient by null ideal + metric completion [1.1] |
| `BookProof/OSReconstruction/Hamiltonian.lean` | `emergent_hamiltonian_selfAdjoint` | Hille–Yosida / Stone generator of time shifts [1.1] |

### Why This Research Plan Works
**Superseded rationale:** the claims in this historical subsection are objectives, not
established compatibility or existence theorems. E0–E5 state their missing inputs.

* **Eliminates the Gauge-Fixing Conflict:** Working in 4D Euclidean space avoids the temporal gauge $A_0 = 0$ (which ruins 4D Euclidean covariance) while avoiding non-local Coulomb gauges [1.1].
* **No Premature Hamiltonian:** The physical Hamiltonian $H_{\text{phys}}$ is not constructed by hand with operator ordering problems; it **emerges dynamically** from the Euclidean translation semigroup via reflection positivity.
* **Direct Compatibility with *Timepiece*:** The entire construction relies solely on objects already validated in `BookProof`: separable Hilbert spaces, the Mehler measure, Riesz–Fischer completions, and Stone's flow machinery [1.1].

---

## Implementation status (2026-10-29)

This section records what of the plan above is actually implemented in **this** repository
(`timepiece`, Lean v4.28.0), with the declaration names to read.  The module-by-module record
lives in `docs/euclidean_cft_proof.md`; this is the plan-side mirror.  `lake build BookProof`
is the verification gate; no module below contains `sorry`.

### Phase → module → declaration

| Phase | Module | Declarations | Status |
| :--- | :--- | :--- | :--- |
| 1.1 | `BookProof/EuclideanFock4D/CoreBasis.lean` | `euclideanHermiteBasis4D`, orthonormality, totality, `euclideanHermiteNet4D`, `colourBasis` | **PROVED** |
| 1.2 | `BookProof/EuclideanFock4D/MehlerMeasure.lean` | `mehlerMeasure4D := gaussianE 4`, `mehler4D_O4_invariant`, `sphereUniform4D` | **PROVED** (the measure is the 4-fold product Gaussian on the Hermite core; no projective limit is built — see Boundary) |
| 2.1 | `BookProof/BalabanRG/MultiscaleSpace.lean` | `Sector k`, `FTotal` (an `ℓ²` sum over scales), `rgOnTotal`, `rgOnTotal_norm_le`, `psiSeq` | **PROVED** |
| 2.2 | `BookProof/BalabanRG/BlockOperator.lean` | `blockConst`, `blockAveragingOp`, **`blockAveragingOp_norm_le`** (`‖Q_k‖ ≤ 1`), idempotence, image in the coarse sector | **PROVED** |
| 2.3 | `BookProof/BalabanRG/Convergence.lean` | `summable_of_increment_bound`, `psiSeq_has_limit`, `psiSeq_cauchy`, **`balaban_rg_convergence`** | **PROVED, conditional** on the geometric increment bound (Bałaban's polymer estimate) — the bound itself is the open analytic input |
| 3.1 | `BookProof/ReflectionPositivity/Involution.lean` | `timeReflection` (`θ² = 1`, coordinate formula), **`timeReflection_measure_invariant`**, `flipCell`, `fieldReflection` | **PROVED** |
| 3.1 | `BookProof/ReflectionPositivity/BlockCommute.lean` | **`blockOf_reflectCoord`**, `mem_blockConst_fieldReflectionSector`, **`theta_commutes_blockAveraging`** (`Θ Q_k = Q_k Θ`) | **PROVED** |
| 3.2 | `BookProof/ReflectionPositivity/HalfSpaceAlgebra.lean` | `PositiveTimeAlgebra`, `CylindricalObservables`, `positiveTimeAlgebra_cylindrical`, `thetaObs`, **`thetaObs_dependsOn_negTime`** | **PROVED** |
| 3.3 | `BookProof/ReflectionPositivity/Proof.lean` | `osForm`, `IsReflectionPositive`, **`reflection_positivity_continuum`**, `psiSeq_component_tendsto` | **PARTIAL**: the passage to the continuum limit from pointwise convergence is proved; the *lattice OS identity itself* is a hypothesis |
| 3.3 | `BookProof/OSReconstruction/MomentumBasis.lean` | `dft_mul_eq_convolution`, **`reflection_positivity_momentum`**, `covarianceForm_eq_dft`, `freePropagator_reflect_eq_transfer`, `freeOSForm_eq_momentum` | **PROVED** for the free field, degree one (two-point function) |
| 3.3 | `BookProof/ReflectionPositivity/FeynmanKac.lean` | `freeTransferKernel` with **`freeTransferKernel_pos`** and **`fkKernelProduct_pos`** (the pointwise positive kernel), `freeAction` with **`freeAction_cross_vanishes`** (the Markov property: no past–future coupling) and **`freeAction_reflect`**, `freeDensity_factorises`, `fkMeasure` (`= ρ ⊗ ν ⊗ ν`), `fkOSForm`, **`fk_integral_eq`** and **`fk_reflectionPositive`** | **NEW (2026-10-30)**: the Feynman–Kac route — the transfer kernel is pointwise positive, the action splits at the reflection slice, and reflection positivity of `ρ ⊗ ν ⊗ ν` holds for *every* integrable half-space observable (polynomials included), with no degree restriction. The identification of the concrete lattice Gaussian with this product form is in the row below |
| 3.3 | `BookProof/ReflectionPositivity/LatticeFreeField.lean` | `fkKernelDensity`, **`fkKernelMeasure`** (`ρ ⊗ ν_z ⊗ ν_z`, boundary-*dependent* half-space law), **`fkKernel_integral_eq`**, **`fkKernel_reflectionPositive`**, `chain`, `halfAction`, `boundaryTerm`, `latticeAction`, `latticeGFFMeasure`, **`latticeGFFMeasure_eq_fkKernelMeasure`**, **`latticeGFF_integral_eq`**, **`latticeGFF_reflectionPositive`** | **NEW (2026-10-30)**: the **identification**. The free field's half-space law depends on the boundary slice (`ν = ν_z`), which `fkMeasure` cannot express, so the FK theorem is proved in kernel form; then the concrete lattice Gaussian free field on `2n+1` slices with the nearest-neighbour action splits as `S = h(z,y₋) + h(z,y₊) + d(z)`, i.e. it *is* `ρ ⊗ ν_z ⊗ ν_z` with `ρ = exp(−d)` and `ν_z = exp(−h(z,·))`. Reflection positivity of the free field therefore holds for every half-space observable with integrable moments. Boundary: the normalising constant `Z` is not evaluated (it cancels), so no `m > 0` and no finiteness is claimed |
| 3.3 | `BookProof/ReflectionPositivity/WilsonLattice.lean` | `plaqDensity`, **`re_trace_le_card`**, `plaqDensity_nonneg`, **`plaqDensity_le_one`**, `plaqWeight`, **`plaqWeight_pos`**, **`plaqWeight_le_one`**, **`wilsonAction`**, **`wilson_mixed_difference_zero`**, **`wilson_density_factorises`**, **`wilsonAction_reflect`**, **`wilsonMeasure_eq_fkKernelMeasure`**, **`wilson_reflectionPositive`** | **NEW (2026-10-30)**: the interaction does **not** spoil the slice split. The plaquette bound `Re tr U ≤ N` (`|tr U| ≤ N` for `U` unitary, from row-orthonormality) makes every plaquette contribute `0 < weight ≤ 1`; a plaquette uses only past, only invariant, or only future links, so `S = A(z,y₋) + A(z,y₊) + b(z)` and the **mixed difference vanishes identically** — the interacting analogue of `freeAction_cross_vanishes`. Hence the Wilson measure *is* `ρ ⊗ ν_z ⊗ ν_z` with the interacting kernel `ν_z = exp(−A(z,·))`, and is reflection positive for every half-space observable with integrable moments. Boundary: the lattice geometry (which links a plaquette uses) is an input, the group measure is not modelled (a fixed reference measure, not Haar), and `Z` of the interacting measure is not evaluated |
| 3.3 | `BookProof/ReflectionPositivity/GFFNormalization.lean` | `sqSum`/`layerSq`/`latticeSq`, **`integral_exp_neg_mul_sqSum`** (`∫ exp(−c‖x‖²) = (√(π/c))^{\|S\|}`), **`integral_exp_neg_mul_layerSq`**, **`integral_exp_neg_mul_latticeSq`** (`= (√(π/c))^{(2n+1)\|S\|}`), `lintegral_exp_neg_mul_latticeSq`, **`latticeAction_ge_mass`**, **`latticeAction_le`**, `latticeGFFMass`, **`latticeGFFMass_le`**, **`latticeGFFMass_ge`**, **`latticeGFFMass_pos`**, **`latticeGFFMass_lt_top`**, `latticeGFFZ_eq_toReal`, **`latticeGFFMass_zero`**, **`latticeGFFProbability`**, **`isProbabilityMeasure_latticeGFFProbability`**, **`latticeGFFProbability_reflectionPositive`** | **NEW (2026-10-30)**: the normalising constant. The reference Gaussians are evaluated exactly, with their constants (Fubini over the sites plus `integral_gaussian`); the action is sandwiched, `(m/2)‖φ‖² ≤ S ≤ (8n + m/2)‖φ‖²`, giving `(√(π/(8n+m/2)))^{(2n+1)\|S\|} ≤ Z ≤ (√(2π/m))^{(2n+1)\|S\|}`, so **`Z` is finite and non-zero** and `latticeGFFMeasure` normalised by it **is a probability measure** (for `m > 0`), still reflection positive because a positive rescaling is. Boundary: *this* chapter proves only the sandwich; the exact closed form `(2π)^{N/2}/√det K` needs the slice recursion `μ₀ = m/2`, `μ_{j+1} = m/2 + μ_j/(1+μ_j)` and is proved in `ChainPartition` (`chainZ_closed_det` + `latticeGFFMass_eq_chainZ`, next rows). The single-slice value `Z = (2π/m)^{\|S\|/2}` is exact here (`latticeGFFMass_zero`) |
| 3.3 | `BookProof/ReflectionPositivity/WilsonLinkLattice.lean` | `Site`, `stepSite`, `Link`, `time`, `theta`, **`theta_involutive`**, **`time_theta`**, `Plaquette` with `c10`/`c01`/`c11`/`siteSet`, **`timeSet_subset`**, `IsPastSide`, `IsFutureSide`, `IsInvariant`, **`plaq_cover`**, **`plaq_classification`**, `reflectTime`, **`pastSide_image_iff`**, **`Plaquette.holonomy`**, **`Plaquette.holonomy_mem_unitaryGroup`**, `re_trace_inv_of_mem_unitaryGroup`, **`Plaquette.plaqDensity_holonomy_inv`**, `Plaquette.plaquetteWeight_holonomy_inv`, **`Plaquette.pastSide_link_time`**, **`Plaquette.futureSide_link_time`**, **`wilsonLatticeAction`**, `pastSideWeight`/`futureSideWeight`/`invariantWeight`, **`wilsonLatticeAction_split`**, **`reflectT_link0`**–**`reflectT_link3`**, **`reflectT2_link0`**–**`reflectT2_link3`**, **`reflectT_c10`/`_c01`/`_c11`**, **`reflectT2_c10`/`_c01`/`_c11`**, **`holonomy_reflectT`**, **`holonomy_reflectT2`**, **`trace_holonomy_reflectT`**, **`trace_holonomy_reflectT2`**, **`trace_holonomy_reflectPlaq`**, **`reflectPlaq_involutive`**, **`wilsonLatticeAction_reflectConfig`** | **NEW (2026-10-30, temporal cases closed 2026-10-31, action invariance 2026-10-31)**: the plaquette classification is now *derived* from an explicit lattice instead of assumed. On the `L × L × L` box with oriented links, every plaquette's time support is contained in `{t, t+1}` (`timeSet_subset`: spatial plaquettes sit at one time, temporal ones span exactly one step); consequently every plaquette is on the past side or the future side of the reflection plane (`plaq_cover`) and the two sides cover while intersecting exactly in the reflection-invariant (boundary) class (`plaq_classification`); and the reflection `t ↦ L−1−t` (an involution, `theta_involutive`, `time_theta`) carries the past side onto the future side (`pastSide_image_iff`) — the input `wilsonAction_reflect` used to take. The four links are now attached to the corner data as genuine `Link` values (`Link.ofStep`, `link0`–`link3`: `base → c10 → c11` and `base → c01 → c11`, with `link_targets`/`link_endpoints_mem` and the square closing at `stepSite_c01`). The holonomy is built from the four links (`U0·U1·U2⁻¹·U3⁻¹`), is unitary for unitary link variables, and its Wilson weight does not see the orientation of the square (`Re tr` of a unitary inverse equals `Re tr`). Past-side plaquettes use only links at time ≤ M, future-side ones only links at time ≥ M (`pastSide_link_time`/`futureSide_link_time`), and the action of the box — summed over *all* plaquettes — splits as `S = past + future − invariant` (`wilsonLatticeAction_split`), the shape `wilsonAction` takes as an input. **All three cases of the reflection are closed**: the four link identities of the reflected square are proved for the spatial case (`reflectS_link0`–`link3`, where the holonomy is *literally* equal, `holonomy_reflectS`) and for both temporal cases (`reflectT_link0`–`link3`, `reflectT2_link0`–`link3`, through the corner lemmas `reflectT_c10`/`_c01`/`_c11`, `reflectT2_c10`/`_c01`/`_c11`), where the reflected holonomy is the cyclic rotation `u₁u₂⁻¹u₃⁻¹u₀` (time first) or `u₃⁻¹u₀u₁u₂⁻¹` (time second) of `u₀u₁u₂⁻¹u₃⁻¹` — one `trace_rot_inv` / `trace_rot` from it, so the **trace identity `Re tr h_{θp} = Re tr h_p` holds in every case** (`trace_holonomy_reflectS`/`_reflectT`/`_reflectT2`, umbrella `trace_holonomy_reflectPlaq`), with the double inverse of a time link unwrapped by `inv_inv_of_mem_unitaryGroup`. The trace identity is lifted to the action: `reflectPlaq` **is an involution** of the plaquette set (`reflectPlaq_involutive`, through `eq_of_data` which reduces a plaquette equality to its base and two directions), so the sum reindexes and **`wilsonLatticeAction_reflectConfig`** gives `S(U_θ) = S(U)` exactly — the reflection invariance the reflection-positivity argument needs. Its remaining gap — identifying the past sum with a measurable function of `(z, y₋)` alone — is closed in the next row. |
| 3.3 | `BookProof/ReflectionPositivity/WilsonPastClass.lean` | **`timeSet_reflectPlaq`**, `siteSet_reflectS`/`_reflectT`/`_reflectT2`, **`IsPastSide_reflectPlaq`**, **`IsInvariant_reflectPlaq`**, **`pastSideWeight_reflectConfig`**, **`futureSideWeight_reflectConfig`**, **`invariantWeight_reflectConfig`**, **`wilsonLatticeAction_reflectConfig_of_split`**, **`measurable_of_inv_apply`**, `PastLink`/`BoundaryLink`/`PastConf`/`BoundConf`, `pastLinkVar`/`pastConfig`/`pastHolonomy`, **`measurable_pastHolonomy_apply`**, **`measurable_weight_pastConfig`**, **`pastSideObservable`**, **`measurable_pastSideObservable`**, **`pastSideWeight_eq_observable_of_eq`** | **NEW (2026-10-31)**: the concrete past-class weight, both halves of the gap recorded in `WilsonLinkLattice`. **Reflection identity.** The reflected plaquette's corner set is the `θ`-image of the original's in all three cases (spatial, time-first, time-second), so its time support is the original's under `t ↦ L−1−t` (`timeSet_reflectPlaq`); with the middle reflection plane `L = 2M+1` the reflection therefore carries the past side onto the future side (`IsPastSide_reflectPlaq`) and preserves the invariant slice (`IsInvariant_reflectPlaq`). Reindexing the sum by the involution `reflectPlaq` and using the trace identity gives **`pastSideWeight β N (reflectConfig U) M = futureSideWeight β N U M`**, with the future (`reflectConfig_involutive`) and invariant companions, and — assembled through `wilsonLatticeAction_split` — `S(U_θ) = S(U)` as an identity between the three class sums (`wilsonLatticeAction_reflectConfig_of_split`), matching the unconditional `wilsonLatticeAction_reflectConfig`. **Measurability packaging.** The half-space configuration space is explicit: past links (time ≤ M), boundary links (time = M), with the link variable `pastLinkVar` reading the past configuration below the slice and the boundary one in it. The entries of `A ↦ A⁻¹` are measurable from `A⁻¹ = det A⁻¹ • adjugate A` (`measurable_of_inv_apply`) — *not* from continuity of the inverse, which fails at singular matrices — and the past-class holonomy's entries are assembled by `measurable_entry_mul` rather than `fun_prop`, so no measurable structure on `Matrix` is needed. The past-class sum is then the measurable function `pastSideObservable` of `(y, z)` (**`measurable_pastSideObservable`**), identified with `pastSideWeight` of any configuration agreeing below the slice (`pastSideWeight_eq_observable_of_eq`) — the `hmeas` input of `wilson_reflectionPositive`. Boundary: the reference measure is instantiated as Haar measure in `HaarReference` (see the next row); gauge invariance is not used, and `Z` is not evaluated |
| 3.3 | `BookProof/ReflectionPositivity/ChainPartition.lean` | `sliceFactor`, `chainForm`, `chainZ`, **`chainForm_cons`**, **`chainForm_linear`**, **`lintegral_exp_neg_mul_sqSum`**, **`lintegral_exp_neg_slice_step`**, **`chainZ_succ`**, `effSeq`, **`effSeq_shift`**, **`chainZ_closed`**, **`chainZ_closed_half`**, `halfAction_split`, **`chainForm_chain`**, **`latticeAction_chain`**, **`lintegral_fkKernel_eq_chainZ`**, `chainMatrix`, **`chainMatrix_zero`**, **`chainMatrix_one`**, **`det_corner_schur`**, **`chainMatrix_succ_det`**, **`chainMatrix_det`**, **`chainMatrix_det_half`**, **`chainZ_closed_det`**, **`chainForm_symm`**, **`chainForm_symm_rev`**, `foldIdx`, **`foldChainEquiv`**, **`volume_preserving_foldChainEquiv`**, **`sum_foldChain_sqSum`**, **`foldChainEquiv_past_chain`**, **`foldChainEquiv_future_chain`**, **`sum_foldChain_diffSq`**, **`latticeAction_eq_chainForm`**, **`latticeGFFMass_eq_chainZ`** | **NEW (2026-10-30, determinant closed 2026-10-31, lattice relabelling closed 2026-10-31)**: the effective-mass recursion itself. The one-slice Gaussian identity (`integral_exp_neg_slice_step`, from `GFFNormalization` §5) is iterated along a chain of `N+1` slices in `ℝ≥0∞` (Tonelli, so no integrability is assumed), giving the recursion `Z_{N+1}(c) = (√(π/(1+c)))^{\|S\|} · Z_N(m/2 + δ(c))` with `δ(c) = c/(1+c)`, and its closed form `Z_N(c) = (∏_{j<N}(√(π/(1+c_j)))^{\|S\|})·(√(π/c_N))^{\|S\|}`, `c₀ = c`, `c_{j+1} = m/2 + δ(c_j)`; with `c = m/2` the `c_j` are exactly `effMass m j`, i.e. `μ₀ = m/2`, `μ_{j+1} = m/2 + μ_j/(1+μ_j)`. The two translations around that recursion are now proved: at the level of measures, `∫⁻ (z,y), ρ(z)·ν_z(y) = chainZ m (m/2) n` (**`lintegral_fkKernel_eq_chainZ`**), and at the level of the operator, the tridiagonal determinant identity `det (chainMatrix m c N) = ∏_{j<N}(1 + c_j)·c_N` (**`chainMatrix_det`**, `= ∏(1+μ_j)μ_N` in **`chainMatrix_det_half`**), by block elimination at the `1 × 1` corner (**`det_corner_schur`**, the Schur complement of the outermost slice) plus induction. **The lattice itself is now a chain**: `foldChainEquiv` presents the `2n+1` slices as a chain (past half backwards, reflection slice, future half; measure preserving by **`volume_preserving_foldChainEquiv`**), the **mass** term matches (**`sum_foldChain_sqSum`**) and so do the **links** (`foldChainEquiv_past_chain`/`_future_chain` slice the two halves, **`sum_foldChain_diffSq`** matches the `2n` links), whence the lattice action *is* the chain form of the folded slices (**`latticeAction_eq_chainForm`**) and **`latticeGFFMass m n = chainZ m (m/2) (2n)`** (**`latticeGFFMass_eq_chainZ`**) — the whole-lattice partition function in closed form, `Z = π^{(2n+1)\|S\|/2}/(det K_{2n})^{\|S\|/2}`. Boundary: this is the *free* (Gaussian) action; the interacting Wilson measure is not relabelled this way, since its density does not factorise along the links |
| 3.3 | `BookProof/ReflectionPositivity/WilsonPartition.lean` | **`plaqDensity_le_two`**, **`wilsonHalfAction_le`**, **`wilsonAction_nonneg`**, **`wilsonAction_le`**, `exp_neg_wilsonAction_le_one`, **`wilsonMass`**, **`wilsonMass_le`**, **`wilsonMass_ge`**, **`wilsonMass_eq_top`**, **`wilsonMass_pos_of_univ_eq_one`**, **`wilsonProbability`**, **`isProbabilityMeasure_wilsonProbability`**, **`wilsonProbability_reflectionPositive`** | **NEW (2026-10-30)**: the interacting partition function. The plaquette density lies in `[0,2]` (`\|Re tr U\| ≤ \|tr U\| ≤ N`), so the action is *bounded*, `0 ≤ S ≤ 4β#P + sup b`, and the Boltzmann weight is squeezed uniformly, `exp(−(4β#P + M)) ≤ exp(−S) ≤ 1`. Hence `Z` is a multiple of the reference volume: `exp(−(4β#P+M))·μ(univ) ≤ Z ≤ μ(univ)`. Against Lebesgue that forces `Z = ⊤` (**`wilsonMass_eq_top`**) — a bounded interaction cannot damp an infinite reference measure, so the model *needs* the finite Haar measure of the compact gauge group; with a normalised reference measure (`μ(univ) = 1`) the same bound gives `0 < Z ≤ 1` and `Z⁻¹ • wilsonMeasure` **is a probability measure**, still reflection positive. Boundary: Haar itself is not constructed and `β, N, P, U` are fixed |
| 3.3 | `BookProof/ReflectionPositivity/QuadraticWick.lean` | `osQuadForm`, `kern`, **`pairing_swap`**, **`osQuadForm_eq_two_mul_kern`**, `kern_transfer`, **`osQuadForm_eq_two_sum_sq`**, **`osQuadForm_nonneg`** | **NEW (2026-10-30)**: the degree-two lift — the Isserlis sum of a quadratic half-space observable equals `2 Σ_{y x} w_x w_y (Σ a_{i j} u_{x i} u_{y j})²`, and is nonnegative for `w ≥ 0`. Degrees ≥ 3 are obstructed (see item 2 below) |
| 3.3 | `BookProof/ReflectionPositivity/HalfSpaceSplit.lean` | `PosTime`/`NegTime`, `negToPos`, `configSplitFun`/`configJoinFun`, **`configSplit`** (`Config ≃ (PosTime → ℝ) × (PosTime → ℝ)`), `configJoin_split`/`configSplit_join`, **`configSplit_fieldReflection`**, **`thetaObs_split`**, **`osForm_split`**, **`osForm_liftHalf_eq`**, **`isReflectionPositive_of_fkOS`**, **`measurable_configSplitFun`**, `splitMap`, **`integral_splitMap`**, **`osForm_eq_integral_splitMap`**, **`isReflectionPositive_of_splitIntegral`**, **`measurable_mk_unit`**, **`mk_unit_snd_eq_id`**, **`map_snd_map_mk`**, **`integral_snd_fkKernel`**, **`isReflectionPositive_of_fkKernelMeasure`**, **`isReflectionPositive_of_wilsonKernelMeasure`** | **NEW (2026-11-04)**: the half-space splitting of the *index set*, so the lattice OS theorems land on the observables `reflection_positivity_continuum` quantifies over. `cellsPerBlock = 16` is even, hence `isPosTime i = (coordOf i).2.val < 8` has no fixed point and every component lies in exactly one half; reading the past half through `θ` indexes both factors by the future half, so the reflection becomes the plain swap `((cs x).2, (cs x).1)` (`configSplit_fieldReflection`) — the same shape as `reflectConf`. Then `ω(θF·F)` for a future-half observable is `ω(fkOSForm f)` in split coordinates, and after pushing the measure (`splitMap ω = ω.map configSplit`) it is the product-model integral `∫ fkOSForm f ∂(splitMap ω)`; `isReflectionPositive_of_splitIntegral` therefore discharges `hRP` from exactly the conclusion of `fkKernel_reflectionPositive`/`wilson_reflectionPositive`. **The identification of `splitMap ω` with the lattice kernel measures is the second half of the row.**  The boundary factor is trivial (`PUnit`, because the reflection has no fixed point), so the index arithmetic `PosTime × PosTime ≃ Z₀ × (Y × Y)` collapses: `map_snd_map_mk` shows that reading the kernel measure on its future half and re-inserting the trivial boundary returns the same measure, `integral_snd_fkKernel` identifies the split-coordinate OS integral with `∫ fkOSForm f ∂(fkKernelMeasure ρd νd)`, and **`isReflectionPositive_of_fkKernelMeasure`** concludes `hRP` from `fkKernel_reflectionPositive` — no hypothesis on the OS form, only measurability of the density and integrability of the OS integrand.  The Wilson case is the same statement with the interacting weights through `wilsonMeasure_eq_fkKernelMeasure` (**`isReflectionPositive_of_wilsonKernelMeasure`**).  Boundary: what is still not constructed is the measure `ω` *itself* on `Config` whose split is that kernel law, and the odd-slice geometry in which the boundary carries a non-trivial law; the reflection has no fixed point here |
| 3.3 | `BookProof/OSReconstruction/ReflectionKernel.lean` | `IsReflectionPositiveOn`, `isReflectionPositiveOn_of_factorization`, `osBilin_sub_theta_self_eq_zero`, **`mk_thetaObs_eq_mk`** | **PROVED**: explains why the hypothesis must be the half-space one. The factorisation route is the uncorrelated (white-noise) case only |
| 4.1 | `BookProof/OSReconstruction/PhysicalSpace.lean` | `osForm` bilinearity, `osForm_expand`, **`osForm_cauchy_schwarz`**, `Radical`, **`osForm_well_defined`**, `osNorm_triangle` | **PROVED** |
| 4.1 | `BookProof/OSReconstruction/HilbertSpace.lean` | `physForm`, **`physCore`**, **`physInnerProductSpace`**, **`Hphys`** (`UniformSpace.Completion`), `physNorm_mk`, `physNorm_eq_zero_iff` | **PROVED** (`Hphys` is the plan's `MinkowskiHilbertSpace`; the plan's `PhysicalNullSpace` is `Radical Λ.ω`) |
| 4.2 | `BookProof/OSReconstruction/Hamiltonian.lean` | `TimeTranslation`, `timeTranslation_semigroup`, **`osNorm_evolution_antitone`**, `radical_invariant`, `timeEvolution_well_defined` | **PROVED** (contractive semigroup part) |
| 4.2 | `BookProof/OSReconstruction/HilbertSpace.lean` | `physEvol`, **`physEvol_contractive`**, `physEvol_zero`, `physEvol_add`, `physEvolCompletion`, **`norm_physEvolCompletion_le`**, **`physEvolCompletion_zero`**, **`physEvolCompletion_add`** | **PROVED** (contractive extension to `Hphys`, and — 2026-11-04 — the semigroup law on it: `P(0) = 1` and `P(s+t) = P(s)∘P(t)` by density of `𝔄/𝔑`, from `timeTranslation_zero` / `timeTranslation_semigroup` through the quotient) |
| 4.2 | — | `emergent_hamiltonian_selfAdjoint`, `emergent_hamiltonian_nonnegative` | **NOT CLAIMED** — but the *reason* has changed, so the row reads: Stone theory is now proved in this repository in both directions (`ChapterStoneResolvent` → `ChapterStoneTheorem`, converse `WeakMeasurableUnitaryGroup.gen_stoneU_eq`), so "Mathlib has no spectral theorem" is no longer accurate. What is missing is the **converse for contraction semigroups** (Lumer–Phillips/Hille–Yosida: symmetric + strongly continuous + contractive ⇒ self-adjoint generator), plus complexification and separability of the real space `Hphys`. Feasibility written up in open item 4 above. The positivity *content* that is proved remains `osNorm_evolution_antitone` |
| 5 | `BookProof/Sirk/ChapterRitzCertificate.lean` | `rayleigh`, `resid`, `SpectralSeparation`, **`temple_lower_bound`**, `temple_band_mem`, `fock_mass_gap_of_temple_certificates` | **PROVED** (the SIRK/Temple receiver) |
| 5 | `BookProof/OSReconstruction/Clustering.lean` | `schwinger`, `connectedCorr`, `SchwingerClustering`, **`schwinger_symm`**, **`osNorm_evol_le_of_clustering`**, `osNorm_evol_iterate_le`, `cluster_decay_tendsto_zero`, **`eNorm_timePoint_eq_spacePoint`**, **`spatial_decay_of_temporal`**, **`osBilin_le_mul_osNorm`**, `osNorm_sub_le`, **`osNorm_sub_evol_ge`**, `genForm`, `one_sub_exp_neg_ge`, **`genForm_ge_of_contraction`**, **`genForm_gap_of_clustering`** | **NEW (2026-10-30)**: Euclidean clustering at mass `m` ⇔ decay of the transfer operator at rate `m` off the vacuum; `O(4)` time→space transfer; and the *separation*: the norm gap `1 − √C e^{−mτ}` of `I − T_τ` and the form gap `m(1 − ε)` of the effective generator `(I − T_τ)/τ`. The clustering bound itself is the hypothesis (see Boundary) |
| 5 (Temple feed) | `BookProof/Sirk/ChapterTempleContinuumGap.lean` | **`gapAt_of_separation`**, `gapAt_of_form_domination`, **`gap_survives_norm_limit`**, `notMem_spectrum_of_separation_limit`, `continuum_gap_of_form_domination` | **NEW (2026-10-30)**: the plan's `SpectralSeparation` becomes a quantitative `GapAt` at the window centre and survives an operator-norm limit, leaving a `c₁Δ_ref/2` hole in the limit's spectrum |
| 4.1′ | `BookProof/OSReconstruction/GaussianMoments.lean` | `productGauss`, **`isserlis_productGauss`**, `integral_prod_coord_productGauss`, `integral_pow_gaussianReal_one_moment` | **NEW (2026-10-29)**: the Gaussian/Wick step the corpus previously lacked — standard covariance only |
| 3.3 + 4.1 (bridge) | `BookProof/OSReconstruction/YangMillsBridge.lean` | `loopProd`, **`thetaObs_loopProd`**, **`osBilin_gram`**, `osBilin_gram_nonneg`, **`complex_sum_quadform`**, **`isReflectionPositive_yangMills`**, `isReflectionPositiveOn_loopProd` | **NEW (2026-10-29)**: the dictionary between the platform's `YangMills.IsReflectionPositive` on correlation functionals of dyadic loops and the state-level `IsReflectionPositiveOn PositiveTimeAlgebra` — the loop observables and their positivity are hypotheses, the equivalence of the two statements is proved |

### Boundary (recorded, never assumed)

* **Phase 2.3**: `balaban_rg_convergence` is the implication *increment bound ⟹ limit*. The
  geometric bound `‖Ψ_{N+1} − Ψ_N‖ ≤ C L^{-εN}` for the actual block operators is Bałaban's
  hard estimate and is not proved (nor is gauge-connection covariance of `Q_k` beyond the
  block-constant model).
* **Phase 3.3**: the lattice Wilson OS identity `⟨θ(F) F⟩_a ≥ 0` for the interacting measure is
  a hypothesis (`IsReflectionPositive`).  For observables supported on one half its *coordinate*
  content is no longer assumed (2026-11-04, `HalfSpaceSplit`): the split of the index set, the
  intertwining `configSplit ∘ θ = swap ∘ configSplit`, and the identity between `osForm` and the
  product-model integral in split coordinates (`osForm_eq_integral_splitMap`, with the
  pushed-forward measure `splitMap ω`, up to the ae-strong-measurability side condition that the
  lattice theorems' `Integrable` hypotheses supply) are proved, so
  `isReflectionPositive_of_splitIntegral`
  reduces the hypothesis to precisely what `fkKernel_reflectionPositive` and
  `wilson_reflectionPositive` prove.  **The identification is proved too** (§6 of the same file):
  the boundary factor is `PUnit`, and `splitMap ω = (fkKernelMeasure ρd νd).map Prod.snd` *is* the
  hypothesis of `isReflectionPositive_of_fkKernelMeasure`, which returns `hRP` from
  `fkKernel_reflectionPositive` alone; the Wilson weights are the same statement via
  `wilsonMeasure_eq_fkKernelMeasure`.  What remained was the construction of the measure itself,
  and a first case is now in place (§7 of the same file, 2026-11-05): `gffConfigMeasure m` is the
  Gibbs measure of the mass (ultralocal) action `S(x) = (m/2) Σ_i (x i)²` on `Config`, written as
  a density against Lebesgue measure on `Config`; `configAction_eq_split` proves `S` separable
  across the halves with the *same* half action on both, Lebesgue measure on `Config` is proved
  invariant under the split (`measurePreserving_configSplitEquiv`), and
  **`splitMap_gffConfigMeasure`** identifies the split law as the product `ν ⊗ ν` of the same
  half-space Gibbs density — the kernel law with a trivial boundary factor.  Two things are still
  open: rewriting that product into the exact `(fkKernelMeasure (Z₀ := PUnit) …).map Prod.snd`
  shape §6 consumes (bookkeeping over the trivial base measure, not carried out), and the coupled
  case — a nearest-neighbour action does *not* split this way, its cross-plane edge couples the
  halves, which is why the free-field theorem uses the `2n+1`-slice model with a boundary slice
  where the boundary carries a non-trivial law. What is proved is its preservation under limit
  (`reflection_positivity_continuum`), the momentum-space form for a free field — degree one in
  `MomentumBasis`, degree two in `QuadraticWick`, and  all degrees in `FeynmanKac` *given* the Markov/product structure of the measure — **that
  structure holding for the concrete lattice free field in the kernel form `ρ ⊗ ν_z ⊗ ν_z`
  (`LatticeFreeField`) and, given the plaquette link classification, for the interacting Wilson
  measure too (`WilsonLattice`)**, and that the full-algebra strengthening would trivialise the
  reflection (`mk_thetaObs_eq_mk`).  What remains an input for the interacting measure is the
  lattice geometry (which links each plaquette uses) and the group measure (a fixed reference
  measure stands in for Haar); the normalisation of the free measure is settled in
  `GFFNormalization` (a probability measure for `m > 0`), the closed-form partition function and
  the interacting normalisation are not.
* **Phase 1.2 / Fock**: `ℱ_k` is modelled by its one-particle content; the `S^∞` projective
  limit and the scale measures `dγ_k` are not built (`dγ₀ = mehlerMeasure4D` only).
* **Phase 4.2**: the emergent generator is not constructed; no self-adjointness or
  nonnegativity of `H_phys` is claimed (see the row above).
* **Phase 5**: the *equivalence machinery* is now proved in `OSReconstruction.Clustering` —
  clustering at mass `m` gives `‖T_τ F‖ ≤ √C e^{−mτ}‖F‖` off the vacuum, iterates to
  `(√C e^{−mτ})^n`, and `O(4)` invariance transfers temporal decay at `(τ,0,0,0)` to spatial
  decay at `(0,r,0,0)` at the same rate.  The step *from* that decay *to* a spectral separation is
  also proved (2026-10-30), on the bounded side: `osNorm_sub_evol_ge` (the gap of `I − T_τ` at fixed
  `τ`) and `genForm_ge_of_contraction` / `genForm_gap_of_clustering` (the form gap `m(1 − ε)` of the
  effective generator `(I − T_τ)/τ`, with `τ → 0` recovering `m`).  What is **not** proved is the
  clustering bound itself (Bałaban's infrared analysis) and the identification of the rate with the
  bottom of the spectrum of the *unbounded* `H_phys`.  Note that the spectral theorem is *not* a missing ingredient: it
  is in this repository (`ChapterSpectralMultiplication`, `ChapterSpectralDirectSum`,
  `ChapterUnboundedSpectralModel`, `ChapterStoneConverse`) and in `physlib/`
  (`SelfAdjointSpectralTheorem.lean`, `CayleySpectralData/SpecTheorem.lean`).  On the bounded
  side, `BookProof/Sirk/ChapterTempleContinuumGap.lean` turns a spectral separation into a
  quantitative gap and carries it across an operator-norm limit; `softmodes.md` Phase 5.2's
  certificate arithmetic (`continuum_gap_unconditional`) is in
  `BookProof/Sirk/ChapterTempleSeparationBound.lean`.

### Current plan / todo list for the contents of this file

Ordered by what unblocks the rest; each item names the module it lands in.

1. **Wick/Isserlis, general covariance** (`BookProof/OSReconstruction/GaussianMoments.lean`) —
   **DONE**: `isserlis_gaussLaw` and `isserlis_multivariateGaussian` prove exactly the pairing
   form `E[∏_k X(p k)] = ∑_{σ ∈ pairings (2m)} ∏_{k < σ k} C (p k) (p σ k)` for a Gaussian of
   covariance `A Aᵀ`, resp. `K ⪰ 0` (see that module's header and `Boundary`).  Kept here for the
   record of the route, which is what item 2 consumes.
   Extend `isserlis_productGauss` from the standard measure (covariance `δ`) to a field
   `X p = Σ_a v a p * y a` with covariance `C p q = Σ_a v a p * v a q`, giving
   `E[∏_k X(p k)] = Σ_{pairings σ} ∏_{pairs {a,b}} C (p a) (p b)`. Two steps: the linear-image
   moment formula (multinomial expansion + the coordinate factorisation already proved), then
   the invariant-theoretic double count. The combinatorics to port are in
   `../physlib/Physlib/Mathematics/ForMathlib/Fin/Involutions.lean`
   (`involutionNoFixedZeroEquivProd`, `involutionNoFixed_card_mul_two : card = (2n−1)‼`) and
   `../physlib/Physlib/QFT/PerturbationTheory/WickContraction/Card.lean` (`cardFun`,
   `card_eq_cardFun`); the Lean versions differ (physlib is v4.35), so this is a port.
2. **Phase 3.3, the RP lift** — **degrees 1 and 2 done; from degree 3 the Isserlis route is
   obstructed, and the obstruction is structural rather than a matter of labour.**  Checked on
   2026-10-30; the route specified for this item (expand, apply Isserlis, match the transfer form)
   is carried out as far as it goes, and where it stops is now a theorem, not an estimate.
   * Degree 1 *is* the transfer form: `freeOSForm_eq_momentum` (with
     `freePropagator_reflect_eq_transfer`, `transferForm_eq`) is exactly "Isserlis sum = Källén–Lehmann
     modulus squares" for a smeared **linear** field.
   * **Degree 2 is now proved** — `BookProof/ReflectionPositivity/QuadraticWick.lean`.  For a
     quadratic half-space observable `F = Σ_{i j} a_{i j} φ_i φ_j` (symmetric `a`) and reflected
     covariance `K_{i k} = ω(φ(θi) φ_k)`, the Isserlis sum is the two pairings
     `Σ a_{i j} a_{k l} (K_{i k}K_{j l} + K_{i l}K_{j k})` (`osQuadForm`).  `pairing_swap` merges
     them (the relabelling `k ↔ l`), `osQuadForm_eq_two_mul_kern` collapses them to
     `2 Σ_{i j} a_{i j}(KAK)_{i j}`, and for a covariance in transfer form
     `K_{i j} = Σ_x w_x u_{x i}u_{x j}`,
     **`osQuadForm_eq_two_sum_sq`** gives
     `ω(θF·F) = 2 Σ_{x y} w_x w_y (Σ_{i j} a_{i j} u_{x i} u_{y j})²`, with **`osQuadForm_nonneg`**
     the `w ≥ 0` positivity.  This is the degree-two match of `transferForm_eq`, but note its
     *form*: the weight multiplies the **square of the bilinear pairing of two modes**, not a single
     `|Σ_p F p u_a p|²`.  The degree-1 statement is the diagonal `x = y` picture; it does not lift
     verbatim, and this is the correct degree-2 statement instead.
   * **Correction (2026-11-08): the following obstruction claim is superseded.**
     Its example fails linear RP already; with a reflection-positive Gaussian covariance,
     an all-degree Wick/chaos proof remains possible. See the revised correction above.
     Historical claim: **from degree 3 the Wick route fails, and cannot be repaired.**
     At degree `2m` the same
     substitution gives products of `m` pairings with no collapse into one square, and positivity
     genuinely fails for a `θ`-invariant Gaussian: on the odd subspace, where the reflection acts
     as `φ(θp) = −φ(p)` and the covariance is `θ`-invariant by construction, the cubic half-space
     monomial `F = φ(p)³` satisfies `θF = −F`, hence `ω(θF·F) = −ω(F²) < 0`.  So
     `IsReflectionPositiveOn PositiveTimeAlgebra ω` is **false** for a θ-invariant free measure in
     general, and no Isserlis/Wick manipulation can prove it.  (Earlier notes put this threshold at
     degree 2; `QuadraticWick` shows degree 2 is in fact positive for symmetric `a` and symmetric
     `K`, so the correction is that the counterexample lives at degree 3 and above.)
   * **The Feynman–Kac structure is now built** — `BookProof/ReflectionPositivity/FeynmanKac.lean`.
     The three inputs the free measure actually uses, none of which is Wick's theorem:
     - the **pointwise positive transfer kernel**: `freeTransferKernel lam z z'` is the Gaussian
       weight `exp(-(lam/2) Σ_i (z' i - z i)²)` of one Euclidean time step, with
       **`freeTransferKernel_pos`** (`0 < K`) and **`fkKernelProduct_pos`** (`0 <` the `n`-step
       product) — positivity of the kernel, not just of the operator;
     - the **Markov property**: `freeAction` is the action `Σ_{i j} φ i A i j φ j`, and
       **`freeAction_cross_vanishes`** shows that block-tridiagonality (no past–future entry in
       the precision matrix) kills every term pairing a past with a future coordinate — so the
       Gibbs weight factorises (`freeDensity_factorises`) and the two half-spaces are
       conditionally independent given the boundary slice;
     - **reflection invariance**: `freeAction_reflect` — the action is symmetric, so the past and
       future conditional laws agree, which is what makes the OS form a *single* square rather
       than a product of two different integrals.
     From these, **`fk_integral_eq`** is the Feynman–Kac identity for the measure
     `fkMeasure ρ ν = ρ ⊗ ν ⊗ ν`: `∫ θF·F d(ρ ⊗ ν ⊗ ν) = ∫ z, (∫ y, F z y ∂ν)² ∂ρ`, and
     **`fk_reflectionPositive`** is its nonnegativity.  That holds for **every** measurable
     half-space observable with integrable moments — every polynomial half-space observable whose
     Gaussian moments are finite — so the degree restriction of `QuadraticWick` is exactly what
     the Markov structure removes.
   * **The identification is now done** — `BookProof.ReflectionPositivity.LatticeFreeField`.  The
     half-space law of the free field depends on the boundary (`ν = ν_z`, a kernel rather than a
     fixed measure), so the FK theorem is restated in kernel form (`fkKernelMeasure ρd νd`, the
     measure with density `ρd z · νd z y₋ · νd z y₊`) with its own Fubini identity
     `fkKernel_integral_eq` and positivity `fkKernel_reflectionPositive`.  The concrete lattice
     Gaussian free field on `2n+1` slices (`latticeGFFMeasure`) satisfies the density identity
     `exp(−S) = exp(−d) · exp(−h(z,y₋)) · exp(−h(z,y₊))` — `fkKernelDensity_lattice`, the Markov
     property in density form, with the *same* half-action on both sides — whence
     **`latticeGFFMeasure_eq_fkKernelMeasure`** and **`latticeGFF_reflectionPositive`**.

     Two of the three follow-ups named here are now closed.  The **interacting Wilson measure**
     does satisfy the same kernel form — not because the quartic term factorises like a Gaussian,
     but because a plaquette can use only past, only invariant or only future links, so the
     mixed difference of the action vanishes identically (`wilson_mixed_difference_zero`) and
     `wilsonMeasure_eq_fkKernelMeasure`, `wilson_reflectionPositive` follow from the plaquette
     bound `Re tr U ≤ N`; and the **normalising constant** of the free field is now pinned:
     `(√(π/(8n+m/2)))^{(2n+1)|S|} ≤ Z ≤ (√(2π/m))^{(2n+1)|S|}`, so `Z ∈ (0,∞)` and
     `latticeGFFProbability` is a probability measure (`GFFNormalization`), and the
     effective-mass recursion `μ₀ = m/2`, `μ_{j+1} = m/2 + μ_j/(1+μ_j)` is now *carried out* along
     a chain of slices (`ChainPartition`: `chainZ_succ`, `chainZ_closed`, `chainZ_closed_half`).
     Both translations around that recursion are now proved: `∫⁻ (z,y), ρ(z)ν_z(y) =
     chainZ m (m/2) n` (`lintegral_fkKernel_eq_chainZ`) and `det K_N = ∏_{j<N}(1 + c_j)·c_N`
     (`chainMatrix_det`, `chainMatrix_det_half`), the latter through the block elimination
     `det_corner_schur` and the peeling step `chainMatrix_succ_det`.  Combining them gives the
     textbook closed form for a chain of `N+1` slices,
     `Z_N = π^{(N+1)|S|/2}/(det K_N)^{|S|/2}` (`chainZ_closed_det`, i.e.
     `(2π)^{(N+1)|S|/2}/√det K` for the standard operator `K = 2·chainMatrix`).  The relabelling
     of the whole `2n+1`-slice `latticeGFFMass` as such a chain is proved as well
     (`latticeGFFMass_eq_chainZ`, through the measure-preserving `foldChainEquiv` and the mass and
     link sums `sum_foldChain_sqSum` / `sum_foldChain_diffSq`), so the free-field partition
     function is closed: `Z = π^{(2n+1)|S|/2}/(det K_{2n})^{|S|/2}`.  Still open: the normalising
     constant of the *interacting* measure.

   Consequence for this file's status table: the `3.3` free-field row now reads "degrees 1 and 2
   proved, higher degrees not", and `isReflectionPositiveOn_of_factorization` stays the
   *uncorrelated* (white-noise) case it says it is.  The hyperlink between the two is the
   independence hypothesis, not a theorem about correlated Gaussians.
3. **Phase 3.3, the interacting identity** (`BookProof/ReflectionPositivity/LatticeOS.lean`).
   The Wilson lattice OS identity for `ω_a(F) = ∫ F dμ_a` on the block-constant algebra, plus
   its preservation under `Q_k` (the commutation `theta_commutes_blockAveraging` is already
   proved). This is the hypothesis `reflection_positivity_continuum` consumes.

   **Feasibility check (2026-11-01).**  The mathematics of this item is done; what is missing is
   an identification between two *different* modelings of "configuration space" that the
   development never made.

   *What is proved.*  Both lattice reflection-positivity theorems exist and are `sorry`-free:
   `latticeGFF_reflectionPositive` (the free field, `GFFNormalization`) and
   `wilson_reflectionPositive` (the interacting Wilson plaquette action).  The second is proved
   from exactly two facts — every plaquette weight is positive (`Re tr U ≤ N`,
   `re_trace_le_card`) and the plaquettes classify into past / invariant / future
   (`wilson_mixed_difference_zero`) — so the measure is `ρ ⊗ ν_z ⊗ ν_z` with a positive kernel
   (`wilsonMeasure_eq_fkKernelMeasure`) and `fkKernel_reflectionPositive` applies.  The `Q_k`
   side of the item is closed as well: `theta_commutes_blockAveraging` is proved
   (`ReflectionPositivity.BlockCommute`).  And the limit passage the item exists to feed,
   `reflection_positivity_continuum`, is proved in `ReflectionPositivity/Proof.lean`.

   *What is missing, precisely.*  `reflection_positivity_continuum` consumes states
   `ω : Observable → ℝ` where `Observable = Config → ℝ`, `Config = Fin latticeDim → ℝ`, with
   `thetaObs F x = F (fieldReflection x)` and `fieldReflection x i = x (reflectCoord i)`.  The
   two lattice theorems, by contrast, are stated on the *product* configuration spaces
   `Z₀ × (Y × Y)` (free) and `Gz × (Gy × Gy)` (Wilson), with the reflection
   `reflectConf γ = (γ.1, (γ.2.2, γ.2.1))` swapping the two half-space factors and leaving the
   boundary factor alone.  Turning `latticeGFF_reflectionPositive` /
   `wilson_reflectionPositive` into the hypothesis `hRP : ∀ N F, 0 ≤ osForm (ω N) F F` therefore
   requires an equivalence `Config ≃ Z₀ × (Y × Y)` (resp. `Gz × (Gy × Gy)`) intertwining
   `fieldReflection` with `reflectConf`, i.e. the lattice-geometry statement that the component
   index splits as *boundary × past-half × future-half* with `reflectCoord` acting as the flip
   on the last two factors.  Nothing in `BalabanRG.MultiscaleSpace` provides that split:
   `coordOf` exposes only the *cell* of a component (`μ`, cell), which is exactly enough for
   `blockOf_reflectCoord` (block stability) and not enough for a half-space factorisation.
   `wilson_reflectionPositive` also carries an integrability hypothesis against *Lebesgue
   volume* on `Gz × (Gy × Gy)`, which the `Config` model does not equip with a measure at all.

   *Consequence.*  `LatticeOS.lean` should not be written as if the OS identity were a Lean
   bookkeeping gap: the identity is a theorem in the product model, and the remaining work is a
   modelling choice (fix the half-space splitting of `Fin latticeDim`, transport the two
   theorems along it, and equip `Config` with the transported measure).  Until that choice is
   made, `reflection_positivity_continuum` keeps `hRP` as a hypothesis — which is the honest
   status, since the RP of the lattice measure *is* the nontrivial theorem of the subject and
   the file that proves it (`WilsonLattice.lean`) proves it in its own model.
4. **Phase 4.2, the generator** (`BookProof/OSReconstruction/Hamiltonian.lean`). From
   `physEvolCompletion` (a *contractive one-parameter semigroup* on the complete space `Hphys` —
   the semigroup law itself is now proved, 2026-11-04: `physEvol_zero` / `physEvol_add` on the
   quotient and `physEvolCompletion_zero` / `physEvolCompletion_add` on `Hphys`, so what stays a
   hypothesis is only strong continuity at `0`, since an arbitrary `TimeTranslation` need not be
   continuous) invoke the Stone/Lumer–Phillips machinery in
   `BookProof/Toolbox/ChapterStoneResolvent.lean` (`UnboundedSelfAdjoint`, `ofBounded`,
   `trotterKato_tendsto`) to obtain `H_phys`, `IsSelfAdjoint H_phys`, `H_phys ≥ 0`.

   **Feasibility check (2026-11-01).**  Two things about this item have changed, in opposite
   directions.

   *The stated blocker is half outdated.*  The reason `Hamiltonian.lean` gives for not claiming
   these theorems is that "(ii)–(iii) [the spectral theorem and Stone/Lumer–Phillips theory do]
   not exist in Mathlib".  Stone's theorem now exists *in this repository*, in full generality
   and `sorry`-free, in both directions: `ChapterStoneResolvent` (resolvents of an unbounded
   self-adjoint `T`, `shift_bijective`, `resCLM`, `‖(A − il)⁻¹‖ ≤ 1/|l|`) →
   `ChapterStoneEvolution`/`ChapterStoneGenerator`/`ChapterStoneUnitary` (the Yosida group
   `stoneU`, strongly continuous and unitary) → `ChapterStoneConverse` (the converse:
   `WeakMeasurableUnitaryGroup.gen_stoneU_eq`) → `ChapterStoneTheorem` (`stone_bijection`), with
   `ChapterStoneBridge` packaging the predicate form.  The non-negative side is there too:
   `ChapterNonnegResolvent` → `ChapterNonnegUnitaryGroup` (`e^{-itT}`) → `ChapterNonnegSemigroup`
   (the heat semigroup `e^{-tT}`), and `ChapterNumericalRangeSemigroup` has the half-plane
   estimate (`NumReLE`, `norm_exp_le_one` = the contraction bound, `norm_resolvent_le` = the
   Hille–Yosida resolvent bound).  So an outdated "no Stone theory" should not be left as the
   recorded reason.

   *What still blocks it.*  Three things, none of them bookkeeping.

   1. **`Hphys` has no topology.**  `OSReconstruction/HilbertSpace.lean`'s physical space is a
      bare `HilbertSpace`-bundled object; the operator it carries is a map into `Hphys` rather
      than a densely defined operator on a complex Hilbert space, so it cannot be fed to
      `UnboundedSelfAdjoint` (which needs a `Submodule ℂ H` domain, `IsSymmetricOn`,
      `IsSelfAdjointOn`).  A Hilbert-space structure with the OS inner product, plus a dense
      domain, would have to be built first.
   2. **No strong continuity.**  `TimeTranslation` is a group of *linear maps on the
      observables* with no continuity hypothesis whatsoever; `physEvolCompletion` therefore
      takes `IsContractive` as a hypothesis, and `ChapterStoneConverse` needs a *weakly
      measurable* one-parameter group (`WeakMeasurableUnitaryGroup`) in the first place.  An
      arbitrary `TimeTranslation` is none of these.  The plan says as much: strong continuity
      is "currently a hypothesis since an arbitrary `TimeTranslation` need not be continuous".
   3. **`H ≥ 0` needs more than contractivity.**  `ChapterNumericalRangeSemigroup`'s
      `norm_exp_le_one` gives `‖e^{-tT}‖ ≤ 1`, i.e. accretivity of the generator.  Nonnegativity
      of the *Hamiltonian* in the OS sense is the positivity of the transfer matrix, and in this
      development that input is `osNorm_evolution_antitone` / `radical_invariant` in
      `Hamiltonian.lean` — already proved, but at the level of the OS seminorm on observables,
      not as `H ≥ 0` on a self-adjoint operator, and bridging the two needs (1) and (2).

   So the honest reading of this item is: the *machinery* is complete and `sorry`-free; the
   gap is that the OS side never produced the analytic objects (a topological physical space, a
      strongly continuous contraction group on it) that the machinery consumes.  Those are
   modelling/analysis tasks on `OSReconstruction/HilbertSpace.lean`, not steps in a proof
   that can be filled from what is here.

   *The actual gap is narrower but real, and it is the wrong direction of the theorem.*  Every
   one of those modules runs **from** a self-adjoint `T` **to** the group or semigroup.  Item 4
   needs the converse **from** `physEvolCompletion` **to** `H_phys`, and there the repo has only
   the *unitary group* converse (`gen_stoneU_eq`).  `physEvolCompletion` is neither:

   * it is a **contraction semigroup on `τ ≥ 0`**, not a unitary group — `gen_stoneU_eq` does not
     apply to it, and the converse for contraction semigroups (Lumer–Phillips / Hille–Yosida:
     symmetric + strongly continuous + contractive ⇒ self-adjoint generator) is not in the
     repository.  `norm_exp_le_one` and `norm_resolvent_le` run in the other direction again
     (bounded generator ⇒ bounds), so they do not substitute for it;
   * `Hphys` is a **real** Hilbert space (`physInnerProductSpace` is an
     `InnerProductSpace ℝ (PhysSpace Λ)`, completed from `Submodule ℝ Observable`), while all of
     the above is over `InnerProductSpace ℂ H`.  No complexification of `Hphys` exists in the
     corpus;
   * `gen_stoneU_eq` additionally needs `TopologicalSpace.SeparableSpace H`, not established for
     `Hphys`;
   * symmetry of the evolution and strong continuity at `0` are still hypotheses, as the plan
     already says.

   So the work item 4 still needs, stated precisely: (a) complexify `Hphys` (or run a
   real-Hilbert-space Stone analogue); (b) prove symmetry of `physEvolCompletion` from OS
   positivity and record strong continuity; (c) supply the contraction-semigroup converse, or
   extend the evolution to a unitary group so that the existing `gen_stoneU_eq` applies.  (c) is
   the missing theorem; (a)–(b) are scaffolding.  Until (c) exists, `emergent_hamiltonian_
   selfAdjoint` and `emergent_hamiltonian_nonnegative` cannot be claimed, and the boundary
   `Hamiltonian.lean` records stays correct — but for *this* reason, not for "Mathlib lacks the
   spectral theorem".
5. **Phase 2.3, the polymer bound** (`BookProof/BalabanRG/Convergence.lean`). Supply the
   increment estimate for the concrete `Q_k` of `BlockOperator.lean`, which is what
   `balaban_rg_convergence` consumes.

   **Done (2026-11-01), in the only form this model permits — and the reason is worth stating.**
   The estimate is supplied, with explicit constants, but its proof is a fact about the *model*
   rather than a proof of Balaban's bound.

   The modelled `Q_k` is `blockConst.starProjection` at every scale, so it is idempotent:
   **`blockAveraging_idempotent`** (`BlockOperator.lean`), from
   `starProjection_eq_self_iff` applied to `blockAveragingOp_mem`.  The recursion
   `Ψ_{N+1} = Q_N Ψ_N` acts componentwise at each scale as `(Q_k)^N`, which is `Q_k` for every
   `N ≥ 1` — **`psiSeq_component_eq`**, `Ψ_{n+1} k = Q_k(ψ₀ k)` — hence
   **`psiSeq_succ_eq_of_idempotent`**: `Ψ_{N+2} = Ψ_{N+1}`, the iteration stabilises after a
   single step.  The increment hypothesis then reads off directly
   (**`psiSeq_increment_bound_of_idempotent`**):

   `‖Ψ_{N+1} − Ψ_N‖ ≤ ‖ψ₀ − Q ψ₀‖ · r^N`  for any `0 ≤ r`,

   with the `N = 0` term the whole of it and every later term zero.  Feeding that into
   `balaban_rg_convergence` gives **`balaban_rg_convergence_blockAveraging`**: for the concrete
   `Q_k`, with `C = ‖ψ₀ − Q ψ₀‖` and `r = 1/2`, `∃ Ψ_∞, Tendsto Ψ_N atTop (𝓝 Ψ_∞)` — the
   convergence of Phase 2.3 is now a theorem about `FTotal`, not an assumption.

   **What it does not say.**  In Balaban's construction the coarse graining genuinely loses
   degrees of freedom at each step (the block lattice is smaller than the fine one), so `Q_k` is
   *not* idempotent and the geometric `C L^{−εN}` decay is analytic — that is the polymer bound.
   In `MultiscaleSpace` every sector carries the same carrier `EuclideanSpace ℝ (Fin latticeDim)`
   by design (see its module docstring, which records why: `Q_k` has to be a map *between*
   sectors that can be iterated inside `F_total`), and that is exactly what makes `Q_k` a
   projection.  So the plan's genuinely geometric content stays the input its boundary names;
   what is added is that for the operator the corpus actually defines, the hypothesis degenerates
   to a single-step estimate and nothing further is needed.  A `Q_k` that carried scale
   information (a genuinely dimension-dependent sector carrier, with transport of norms along
   `dimBlock k → dimBlock (k+1)`) would make this item non-trivial, and is the modelling change
   it would take.
6. **Phase 5, clustering ⇒ mass gap** (`BookProof/OSReconstruction/Clustering.lean`) — *formulated
   and half-proved (2026-10-30).*  `SchwingerClustering ω T m C` is the plan's decay bound, and
   `osNorm_evol_le_of_clustering` / `osNorm_evol_iterate_le` derive from it the operator decay
   `‖T_τ F‖ ≤ √C e^{−mτ}‖F‖` off the vacuum at every iterate; `spatial_decay_of_temporal` is the   `O(4)` step.  **(ii) is now done in bounded form (2026-10-30):** `osNorm_sub_evol_ge` turns the
   contraction into the norm gap `‖(I − T_τ) F‖ ≥ (1 − √C e^{−mτ}) ‖F‖` at every fixed `τ`, and
   `genForm` / **`genForm_ge_of_contraction`** / **`genForm_gap_of_clustering`** turn it into the
   form gap of the *generator*: for every `ε ∈ (0,1)` there is `τ > 0` with
   `m(1 − ε)‖F‖² ≤ (‖F‖² − ⟨F, T_τ F⟩)/τ` off the vacuum (`one_sub_exp_neg_ge` is the elementary
   `1 − e^{−x} ≥ x/(1+x)` behind the `τ → 0` limit).  So the clustering rate `m` *is* the bottom of
   the emergent generator's form spectrum, in the only form the corpus can state it — the operator
   `H_phys` itself is not constructed, so the separation is stated for `(I − T_τ)/τ`.
   Remaining: (i) the decay bound for the actual Bałaban measure, (ii′) the identification of the
   bounded separation with a `SpectralSeparation` of the *unbounded* generator, (iii) the
   Temple feed, whose arithmetic is done in `ChapterTempleSeparationBound.continuum_gap_unconditional`
   with `c₁ Δ_ref` from `softmodes.md`.

   **Correction (2026-11-08):** this paragraph's claim that the physical separation constant
   is established is superseded by softmodes S0–S2. Its comparison thresholds do not
   identify actual spectral levels; the concrete form, sector and margin remain inputs.
   The newer multiplier/operator results also supersede generic absence claims below.

   **Historical (iii) assessment — 2026-11-04.** `softmodes.md` Phase 4 now certifies
   `c₁ Δ_ref` on the `L²` form of record (`closed_yangMillsGap`) *and*, for an off-diagonal
   interaction, on the core (`hopping_farisLavine`), so the constant is no longer the obstruction.
   What `continuum_gap_unconditional` consumes is different in kind: its hypothesis is
   `SpectralSeparation A l b`, i.e. `l ≤ b ∧ ∀ t ∈ spectrum ℝ A, t = l ∨ b ≤ t` for a **bounded
   self-adjoint operator** `A`, while the certificate is about a **quadratic form** on `ℓ²`.  Two
   things are therefore missing, and neither is arithmetic: the operator `A` on `L²` whose
   Rayleigh form is `closedForm (yangMillsSymbol) x` (the diagonal multiplication operator, which
   is bounded only when the symbol is), and the identification
   `spectrum ℝ A = closure (range (symbol))` for that operator, from which a *spectral* gap off the
   vacuum would follow.  Mathlib has no spectrum computation for diagonal operators on `ℓ²`, and a
   form gap does not imply a spectral one without the spectral measure — the form gap holds on the
   vacuum-orthogonal sector, where Rayleigh quotients of *mixtures* `Ω + e` can still take any
   intermediate value.  So item (iii) is blocked on the same operator⇄form bridge as (ii′), and
   `ChapterTempleSeparationBound`'s honest boundary ("the transfer across the strong-resolvent
   limit is not proved") should be read as covering this too.
