import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Appendix: Proof Plans" =>
%%%
tag := "proof-plans"
number := false
%%%

This appendix collects the precise statements that are mathematically relevant to
the book, separating proved results, conditional bridges, and genuinely open
instantiation work. The newest proof wave adds finite Ritz certificates, Temple
separation, band enclosure, one-particle/Fock gap lifts, Friedrichs-form gaps,
and perturbative interaction stability. It is addressed to an LLM Lean specialist
(e.g. Aristotle). A more detailed, machine-oriented version lives in
`CONSOLIDATED_PLAN.md` at the repository root.

# The New Spectral-Gap Proof Layer

The following modules are now part of the proof architecture:

* `ChapterRitzCertificate.lean`: derives a finite spectral interval from a
  Rayleigh quotient, residual, and explicit Temple separation hypothesis.
* `ChapterTempleSeparationNecessary.lean`: proves that separation is necessary;
  Rayleigh quotient and residual alone cannot bound the spectral edge.
* `ChapterBandEnclosure.lean`: packages compatible nested finite bands and their
  intersection/enclosure consequences.
* `ChapterFockOneParticleGap.lean`: states the positive one-particle edge and
  its conditional consequences.
* `ChapterFriedrichsFormGap.lean`: packages the semibounded quadratic-form and
  Friedrichs-extension route.
* `ChapterFockNumberPreservingGap.lean`: lifts a one-particle gap through
  number-preserving second quantization.
* `ChapterFockFieldPerturbation.lean` (now `sorry`-free) and
  `ChapterFockInteractionStability.lean`: control bounded or relatively
  form-bounded perturbations, with the unbounded physical interaction
  explicitly left as a specialist obligation — until the new ladder closed it:
* `ChapterFockPairPerturbation.lean`: the quadratic, pair-creating unbounded
  coupling `P(f,g) = a†(f)a†(g) + a(g)a(f)` keeps the gap
  `(μ − 2√2‖f‖‖g‖)‖u‖²` under the smallness condition `2√2‖f‖‖g‖ < μ`.
* `ChapterFockCubicUnbounded.lean`: the boundary of the route — a bare cubic
  term `(a†)³ + a³` admits no relative form bound, so `dΓ(N) + λC` is
  unbounded below at every coupling strength; adding the normal-ordered
  quartic `(a†)²a²` restores a lower bound along the same trial family.
* `ChapterYangMillsFockGapChain.lean`: instantiates the abstract chain for the
  concrete gauge-fixed QYM one-particle operator `H₁ = ½Σπ² + ½ΣB²` —
  `dΓ(H₁)Ω = 0` unconditionally, the `dΓ` lift of a one-particle *form* gap to
  the nested-Fock mass gap (with the Friedrichs extension), the linear field
  perturbation, and the certified-band route through `BandEnclosure` — all
  conditional on the one-particle form gap.
* `ChapterFockCubicQuarticStability.lean`: the positive companion of
  `ChapterFockCubicUnbounded` — the cubic term `C_k = (a†)³ + (a_k)³` together
  with its normal-ordered quartic partner `Q_k = (a†)²(a_k)²` is bounded below
  on all finite states (no trial family, no vacuum-orthogonality):
  the forms are rewritten as norms (`quart_form_eq`, `cubic_form_eq`), combined
  with the single-mode canonical commutation relation (`norm_creA_sq`) and a
  Cauchy–Schwarz estimate (`sq_norm_annA_le_mul`) that forces a large mode
  occupation to carry a large quartic form, giving the uniform bound
  `−(2λ² + (2λ² + ½ − μ)²/2)‖u‖²`, its multi-mode sums (one copy of the free
  form pays for every mode of a finite set) and the one-particle-gap version.
  Semiboundedness, not a gap — the constant is negative.
* `ChapterScalaronFockGapChain.lean`: the same chain run for the R² (scalaron)
  sector — the cleanest instantiation. For the constant one-particle operator
  `m·1` the form gap is an *identity*, so every chain conclusion becomes a
  theorem with no certificate and no hypothesis: `const_fock_gap` (`dΓ(m·1)Ω = 0`
  and the `m‖u‖²` bound), `const_fock_mass_gap` (positive self-adjoint
  Friedrichs extension, strict positivity of the non-vacuum energy), the
  surviving gap `(m − 2‖f‖)‖u‖²` under the linear field coupling, and
  semiboundedness with the cubic/quartic pair — instantiated at the Starobinsky
  scalaron mass `scalaronMass α = 1/√(12α)` on the Hermite basis of `L²(ℝ)`.
  What is unconditional is the *lift*; that the sector's one-particle energy is
  this constant is the modelling statement of the enclosure doctrine. For the
  full-exponential realization `h_ψ = ½π² + V(φ̂)` (the vielbein/TEGR model,
  exponential as-is) the proved layer transfers fiber by fiber — the scalaron
  fiber via the wall class (`starobinskyWall_esa`: smooth non-negative
  potential, no growth restriction, on the compactly supported smooth core;
  kinetic normalization `½π²` is the same class after the unitary rescaling
  `φ = √2·x`; `wallHamBddBelow_semibounded` for the form; Gauss-core transport
  via `ChapterQgOneParticleCcEsa`), the TEGR shear fibers via the
  constant/diagonal one-particle chains, and the fibrewise direct-sum
  instrument (`ChapterDirectSumEsa`, `fockSmoothPotential_esa`) reassembles
  the nested Fock space — with the caveat that the Fock-level QG theorems
  (`qgScalaronFock_esa`, the densitized route) formalize the *metric-route*
  3+1 gauge fixing, not the vielbein/TEGR one. Only the strict edge `E₀ > 0`
  remains, an elementary confinement estimate (the superlevel set `{V < c}`
  is a bounded interval for `0 < c < M⁴/(16α)`), after which the same `dΓ`
  lift applies verbatim at `μ = E₀`.
* `ChapterFockDiagonalGapChain.lean`: the same chain for a *diagonal*
  one-particle energy `e_k ↦ ω_k e_k` — the shape the free sectors have. Here
  the form gap is *proved* from `ω_k ≥ m` (`diagOnePart_quadForm_ge`), so the
  chain is again hypothesis-free, with the free massive instance
  `freeField_fock_mass_gap` at the relativistic dispersion `√(p² + m²)`
  (massless dispersion gives `m = 0`: positivity, no gap).
* `ChapterSpectralGapStability.lean`: proves stability under suitable operator
  limits and perturbations.

The claim is now conditional but mathematically honest: the finite SIRK
certificate can feed this chain only after its separation and enclosure inputs
are supplied (the one-particle *form* gap is the single outstanding analytic
input), and the continuum QYM result still requires a concrete convergence
theorem. For the sectors whose one-particle energy is a positive constant or a
diagonal dispersion — the scalaron of the R² theory being the flagship example
— the chain is now *unconditional*: no certificate, no Ritz data, no form-gap
hypothesis. The QYM instantiation remains the conditional frontier.

Every plan targets the project's pinned toolchain (*Lean v4.28.0, Mathlib
v4.28.0*), so that the work stays compatible with the existing `sorry`-free
`BookProof` library and with the automated prover.

# A. The ODE Chapter

The `Singularity` library and `BookProof` are both `sorry`-free. All three
headline ODE results are proved: `weyl_symmetrization_self_adjoint` and
`nelson_essential_self_adjoint` in `Singularity/`, and
`ae_no_real_singular_time` in `BookProof/ChapterOdeComplexification.lean`.

## A.1 Self-adjointness of the Weyl Hamiltonian

*Status: PROVED.* `weyl_symmetrization_self_adjoint` (in
`Singularity/Hamiltonian.lean:102`) proves `adj (odeToHamiltonian sys) =
  odeToHamiltonian sys` by `simp` + `ext`. The Wick symmetrization
$`(A + A^\dagger)/2` is therefore self-adjoint at the algebraic level.

## A.2 Nelson's essential-self-adjointness theorem

*Status: PROVED.* `nelson_essential_self_adjoint` (in
`Singularity/Esa.lean:44`) proves the equivalence by `simp` from the certificate
definitions: vanishing deficiency indices iff the classical flow is complete. The
forward direction (flow complete => ESA) is the one needed for the ODE resolution.

## A.3 The complexification resolution

*Status: PROVED.* `ae_no_real_singular_time` (in
`BookProof/ChapterOdeComplexification.lean:70`) proves that for almost every
initial condition, the singular time is non-real. Uses
`MeasureTheory.Measure.addHaar_submodule` for the null-measure argument.

*Goal.* Prove that the flow of $`\dot z = z^2` on $`L^2(\mathbb{R}^2)` has *no
finite-time singularity for almost every initial condition*, because the singular
time $`t = 1/z(0)` is real only when $`\operatorname{Im} z(0) = 0`, a null set.

*Plan.* Work in `Singularity` or a new `BookProof` module. Formalize: the explicit
solution $`z(t) = z(0)/(1 - t z(0))`; the singular-time condition
$`1 - t z(0) = 0 \Rightarrow t = 1/z(0)`; that $`1/z(0) \in \mathbb{R}`
$`\Leftrightarrow \operatorname{Im} z(0) = 0`; and that the line
$`\{y = 0\} \subset \mathbb{R}^2` has Lebesgue measure zero (use
`MeasureTheory` — cf. `ConsciousnessNullMeasure.countable_volume_zero` for the
measure-theoretic style). Conclude the set of initial data with a real singular time
is null.

## A.4 Energy-bounded initial conditions

*Status: PROVED* (in the spectral representation).
`BookProof/ChapterSpectralEnergyBound.lean` works where the spectral theorem has
already been applied, i.e. with $`H` the multiplication operator attached to a real
eigenvalue function $`f`, and proves the whole chain: the spectral-projection bound
$`\|H\psi\| \le E_{\max}\|\psi\|` for $`\psi` supported on $`\{|f| \le E_{\max}\}`
(`norm_diagOp_le`); unitarity of the evolution (`norm_evolve`); the Schrödinger
equation $`\psi'(t) = -iH\psi(t)` (`hasDerivAt_evolve`); the uniform bound
$`\|\partial_t\psi(t)\| \le E_{\max}\|\psi(0)\|` (`norm_deriv_evolve_le`); and hence
global Lipschitz continuity in time (`evolve_lipschitz`) — no finite-time
singularity.

```
#check @ChapterSpectralEnergyBound.norm_diagOp_le
#check @ChapterSpectralEnergyBound.norm_deriv_evolve_le
#check @ChapterSpectralEnergyBound.evolve_lipschitz
```

# B. The PA-Free Chapter

## B.1 The verifiable analytic core (proved)

The Riesz–Fischer characterization `completeSpace_iff_summable_norm` and the
completeness of `UniformSpace.Completion` are in Mathlib. The analytic core is
now fully instantiated in `BookProof.ChapterRieszFischer`: $`\ell^2(\mathbb{N})`
is complete (`ell2_completeSpace`), every vector is the unconditional sum of its
coordinate atoms (`riesz_fischer_hasSum`), the finitely-supported core is dense
(`finSupport_dense`) and proper (`finSupport_ne_univ`), and the rational fragment
is a countable dense subset (`BookProof.ChapterEll2Separable.ell2_separable`), so
the completion is separable.

## B.2 Definability / conservativity (the hard, partly informal part)

*Status.* The claim "the completion does not leak Peano Arithmetic" is a
metamathematical statement about definability in the base language, *not* an
internal theorem of analysis.

*What is formalizable.* The precise, provable fragment is now proved in
`BookProof.ChapterDefinabilityFragment`: inside $`\ell^2(\mathbb{N})` the image of
the term-denotable fragment $`\mathbb{N} \to_0 \mathbb{R}` is *exactly* the set of
finitely-supported vectors, that set is dense, and it is a proper subset
(`completion_conservative_over_core`). The remaining, purely *proof-theoretic*
reading — that the completion is a conservative extension of the base theory —
would require formalizing a first-order language of Hilbert spaces and a
definability predicate, a research-scale task that is not claimed here.

# C. Book Tooling

## C.1 Inline-elaborated Lean blocks

*Current state.* The Lean statements in this book are shown as *plain
(non-elaborated) code blocks*, and verification is anchored on
`lake build BookProof`. The blocks are not yet elaborated inside the book build.

*Goal.* Make the `#check` blocks elaborate (and syntax-highlight with hovers)
during the book build.

*Plan.* Verso elaborates a code block against the module's *exported* interface,
so the chapter modules must re-export the `BookProof` names. This needs
`public import BookProof.<Module>`, which in turn requires Lean's
`experimental.module` feature to be enabled for the `Book` targets. Concretely:
enable `experimental.module` for the `Book` library and `book` executable in
`lakefile.toml`, change each chapter's `BookProof` import to `public import`, and
re-add the imports. Verify a chapter at a time. (This re-introduces Mathlib
elaboration into the book build, so it is slower; it does *not* rebuild Mathlib.)

## C.2 Migration to verso-blueprint

*Current state.* The book is a Verso *manual* on Lean v4.28.0.

*Goal.* Adopt [`verso-blueprint`](https://github.com/leanprover/verso-blueprint)
to sync the exposition with the Lean declarations (proof-status tracking, dependency
graphs, progress summaries).

*Blocker.* verso-blueprint requires Lean *≥ v4.29.0*; this project is on
*v4.28.0* (with Mathlib v4.28.0 and the 198-module `BookProof`). verso-blueprint
elaborates the declarations it documents (it detects `sorry` and builds dependency
graphs), so it must run on the same toolchain as the code.

*Plan (execute only when compatible with the automated prover).*
 1. Bump `lean-toolchain` to a version that is *both* supported by
    verso-blueprint *and* by the automated prover.
 2. Bump Mathlib to the matching version and re-fetch its build cache
    (`lake exe cache get`); re-verify `BookProof` (watch for API drift — the library
    has drifted once before).
 3. Choose a stable *label scheme* mirroring the chapter structure (e.g.
    `dutch_book_coherent_iff`, `euler_sum_one`, `total_variance`).
 4. Tag the featured `BookProof` theorems with `@[blueprint "label"]` (use
    `autoDeps := true` where appropriate).
 5. Port the exposition written here into blueprint blocks
    (`:::theorem "label" (uses := ...)`, `:::proof`, with `{uses ...}` /
    `{bpref ...}` edges), reusing the existing prose and sketch proofs.
 6. Build with `lake exe vbp build` and inspect the progress and dependency views.

The Verso markup already written ports to blueprint blocks with modest edits, so the
prose work in this book is not wasted by the migration.

# D. Weak Measurements and Weak Values

*Status: PROVED (`BookProof.ChapterWeakValue`).*

*Background.* The post-selection / ABL reconstruction that underlies the
trajectory chapter and the double-slit discussion is proved
(`BookProof.ChapterTrajectory`): the three-instant collapsed Born process
(`midProb`, `transProb`, `jointProb`, `finalProb`, `condProb`), the reconstruction
consistency (`jointProb_sum_final_eq_midProb`), and the double-slit capstone
(`dslit_finalProb`, `dslit_condProb`, `dslit_coherentFinal`, `dslit_interference`).

*What is now proved.* The weak value of an observable $`A` given a pre-selection
$`\langle i|` and a post-selection $`|f\rangle`,

$$`\langle A \rangle_w = \frac{\langle f | A | i \rangle}{\langle f | i \rangle},`

is formalized on the finite complex Hilbert space $`\mathrm{Fin}\, n \to
\mathbb{C}` with the standard inner product `ip`:

 * `weakValue i f A = ip f (A *ᵥ i) / ip f i` — the definition;
 * `weakValue_wellDefined` and `weakValue_unique` — if $`\langle f | i \rangle
   \neq 0`, the weak value is the *unique* solution of $`w\,\langle f|i\rangle =
   \langle f|A|i\rangle`;
 * `weakValue_diag` — when $`i = f` (a unit vector) the weak value collapses to
   the ordinary expectation $`\langle i | A | i \rangle`, which
   `weakValue_diag_isReal` shows is real for a Hermitian observable;
 * `weakValue_add`, `weakValue_smul`, `weakValue_linear` — linearity in the
   observable, the algebraic core of "weak measurements are linear in $`A`";
 * `weakValue_proj` and `weakValue_proj_sum` — the weak values of a complete
   family of projectors sum to $`1`, the counterpart of
   `ChapterTrajectory.condProb_sum`;
 * `jointProb_eq_normSq_weakNumerator` and `condProb_eq_weakNumerator_ratio` — the
   ABL joint law is the squared modulus of the weak-value numerator for the
   post-selection covector $`b \mapsto \overline{V_{f b}}`, and the post-selected
   conditional law is its normalization;
 * `dslit_weakValue` — the double-slit capstone: pre-selecting the both-slits
   superposition $`H\Psi` and post-selecting $`\Psi = (1,0)`, the two which-slit
   projectors have weak values $`1` and $`0`.

*Boundary.* The *physical* claim that weak measurements do not disturb the
intermediate state is about the measurement interaction, not about the mathematical
ratio; it is not claimed here. The formal content is the ratio, its well-definedness,
and its agreement with the ordinary expectation in the diagonal case.

*Where it lives.* `BookProof.ChapterWeakValue`, registered in `BookProof.lean`,
certified in `BookProof/ChapterRoadmapAudit.lean`, and `#check`-ed from the
double-slit chapter's "Weak Measurements" section.

# E. The Dynamics-Based Unitary (from a function / conditional probability)

*Status: PROVED (`BookProof.ChapterContinuityUnitary`), in the finite
(discretized) model.*

*Background.* The `ConditionalUnitary` chapter builds the unitary that
parametrizes a conditional probability by *Gram–Schmidt* completion of the
wave-function `Ψ = √p` (`BookProof.ChapterJointUnitary.exists_unitary_column`),
and reads the marginal/conditional back off the operator's Gram matrix
(`BookProof.ChapterConditional`). That construction is correct but *arbitrary*:
the columns after the first are chosen by the completion, not fixed by the
probability data.

*The less arbitrary alternative.* The manuscript's field-theoretic thread (QFM.tex)
defines the unitary from the *dynamics* rather than from a basis choice: a function
(a velocity field `v_t(x)`, or a potential `V(x,z)`) determines a Hermitian
generator by the continuity (Weyl-symmetrized) prescription

$$`\mathbf{H}_t = \tfrac12\bigl[\hat p\cdot v_t(\hat x) + v_t(\hat x)\cdot\hat p\bigr],`

and hence a unitary $`\mathbf{U} = e^{i\mathbf{H}t}` — pinned down by the function,
with no free choice of extra columns. For a conditional probability $`p(y|x)` the
construction needs no Bochner-space machinery: via the tensor–product
identification $`L^2(X,\mu)\otimes L^2(Z,\nu) \cong L^2(X\times Z,\mu\times\nu)`,
$`\mathbf{H}` is a standard Hermitian operator on the scalar space
$`L^2(X\times Z)`, and the conditional is recovered by the ordinary Born rule
$`P(x,B) = \int_B |\Psi_1(x,z)|^2\,d\nu(z)`.

*What is now proved,* on the finite (discretized) model that the rest of
`BookProof` uses — the cyclic lattice $`\mathbb{Z}/N` with the
symmetric-difference momentum $`(\hat p\,\psi)_k = -\tfrac{i}{2}(\psi_{k+1} -
\psi_{k-1})`:

 * `continuityHamiltonian` — the Weyl-symmetrized generator
   $`\mathbf{H} = \tfrac12(\hat p\,v + v\,\hat p)`, with
   `continuityHamiltonian_hermitian`; the symmetrization is *necessary*, since
   `momentum_mul_velocityOp_not_hermitian` exhibits a three-site velocity field
   for which $`\hat p\,v` is not Hermitian;
 * `continuityUnitary` — $`\mathbf{U}_t = e^{i t\mathbf{H}}` is unitary
   (`continuityUnitary_unitary`, from the general `exp_smul_I_unitary`) and a
   one-parameter group (`continuityUnitary_zero`, `continuityUnitary_add`): the
   "function → unitary" translation;
 * `bornRecover` — the map $`B \mapsto \sum_{z\in B} |\Psi_t(z)|^2` is
   nonnegative (`bornRecover_nonneg`), finitely additive (`bornRecover_union`),
   monotone (`bornRecover_mono`) and of total mass $`1` (`bornRecover_univ`, from
   `unitary_preserves_normSq`); `bornPMF` packages it as a distribution;
 * `tensorIsom` / `tensorIsom_tmul` — the finite index-level statement of the
   tensor–product identification (the scalar `L²(X×Z)` is the same object), with
   `bornRecover_product_state` running the recovery on a product wave-function
   $`\Psi_0(x,z) = f(x)\,e_0(z)`; and, as a capstone,
 * `condProb_of_continuity` — the recovered $`P(x,B)` is a genuine conditional
   probability law for every input $`x`, tying the dynamics-based unitary back to
   the `ChapterConditional`/`ChapterJointUnitary` Gram-matrix reading.

*Boundary (updated).* Two of the three deferred layers are now closed.
`BookProof.ChapterContinuityUnitaryInfinite` carries the whole construction to the
*infinite* lattice $`\ell^2(\mathbb Z)`: the translations are unitaries, the
symmetric-difference momentum and a bounded velocity field
$`v\in\ell^\infty(\mathbb Z)` are bounded self-adjoint operators
(`momentum_isSelfAdjoint`, `velocityOp_isSelfAdjoint`), the Weyl-symmetrized
generator is self-adjoint (`continuityHamiltonian_isSelfAdjoint`), $`e^{itH}` is a
one-parameter unitary group of the Banach algebra of bounded operators
(`continuityUnitary_unitary`, `continuityUnitary_add`) and the Born recovery is
countably additive with total mass $`1` (`bornRecover_tsum_univ`,
`condProb_of_continuity_infinite`).  `BookProof.ChapterBornMeasure` removes the
discretization from the probability side: on an arbitrary measure space,
$`P(B) = \int_B|\Psi|^2\,d\mu` is a *measure* (`bornMeasure`), a probability
measure for a normalized state (`isProbabilityMeasure_bornMeasure`), absolutely
continuous with respect to $`\mu` (`bornMeasure_absolutelyContinuous`), and the
capstone `condProb_of_bounded_dynamics` gives it for the evolved state of any
bounded self-adjoint generator on $`L^2(\mu)`.  What is still deferred is
*unboundedness* alone — the continuum $`-\tfrac12\Delta_z`.  Even that layer is now
stated inside the theory: `BookProof.ChapterUnboundedPosition` builds the lattice
position operator on its natural domain and proves the domain dense
(`mulDomain_dense`), the operator symmetric (`mulOp_symmetric`) and genuinely
unbounded (`position_unbounded`, `position_not_boundedOperator`).  It then carries
that operator through the two steps the plan had left open: its adjoint domain is
exactly the natural domain and the adjoint acts by the same multiplication
(`adjointDomain_eq_mulDomain`, `adjoint_eq_mulOp`), so it is *self-adjoint*; and it
generates a strongly continuous one-parameter unitary group (`phaseUnitary`,
`phaseUnitary_add`, `tendsto_phaseUnitary`) of which it is the generator, the
difference quotient converging in $`\ell^2(\mathbb Z)` on the natural domain
(`tendsto_slope_phaseUnitary`, Stone's relation $`dU/dt|_0 = iA`).
`BookProof.ChapterUnitaryTransport` then shows that none of this is special to the
lattice: for a unitary $`W`, the transported operator $`WAW^{-1}` inherits a dense
domain, symmetry, self-adjointness (`transport_isSelfAdjointOn`, via
`transport_adjointDomain`) and the strongly continuous group with Stone's relation
(`tendsto_transportUnitary`, `tendsto_slope_transportUnitary`) — so every operator
unitarily equivalent to a lattice multiplication operator, on any complex Hilbert
space, carries the whole package (`transported_position_isSelfAdjointOn`,
`tendsto_slope_transported_position`).  And the general Stone theorem is now part
of the theory rather than the recorded gap: `BookProof.ChapterStoneResolvent`
through `BookProof.ChapterStoneSeparable` build the resolvent of a self-adjoint
operator, obtain the weakly measurable unitary group `e^{-itA}` (`stoneU`,
`stoneU_mem_domain`, `hasDerivAt_stoneU`, the group law `stoneU_add`), and
prove the bijection between self-adjoint generators and one-parameter groups
(`stone_bijection`, `stoneEquiv`), with a concrete `ℓ²(ℤ)` instance
(`stoneU_mulSA`).  `BookProof.ChapterStoneBridge` then packages a *selected*
self-adjoint extension into the bundled structure Stone's theorem consumes and
presents the whole package as `IsStoneFlow` (`U 0 = 1`, the group law, isometry,
Schrödinger equation on the domain), with `isStoneFlow_stoneU` showing the
abstractly constructed group is such a flow and
`exists_stone_flow_of_selfAdjointExtension` / `of_positive` / `of_esa` as the
entry points.  The spectral half of Stone's theorem — the existence of the
diagonalizing unitary (the spectral theorem for unbounded self-adjoint operators),
the last layer the continuum $`-\tfrac12\Delta_z` would need — is now closed too:
`BookProof.ChapterUnboundedSpectralModel` (wave 2026-08-21h) proves, by the
classical resolvent (Cayley) route, that *every* densely defined self-adjoint
operator on a complex Hilbert space is multiplication by a real function on a
Hilbert sum of $`L^2(\mu_x)` spaces, with no cyclic vector and no separability
assumed (`unbounded_multiplication_model_cyclic` / `_general` / `_separable`).
The *physical* claim that the dynamics
"is" the transition is about the choice of $`\mathbf{H}`; the formal content is
that a Hermitian $`\mathbf{H}` yields a unitary and that the Born rule recovers a
probability law.

*Where it lives.* `BookProof.ChapterContinuityUnitary` (finite lattice),
`BookProof.ChapterContinuityUnitaryInfinite` ($`\ell^2(\mathbb Z)`) and
`BookProof.ChapterBornMeasure` (the Born law as a measure) and
`BookProof.ChapterUnboundedPosition` (the self-adjoint unbounded layer and the
unitary group it generates) and `BookProof.ChapterUnitaryTransport` (unitary
invariance of that whole package) and `BookProof.ChapterStoneResolvent` /
`ChapterStoneSeparable` (the general Stone theorem and its concrete
$`\ell^2(\mathbb Z)` instance) and `BookProof.ChapterStoneBridge` /
`ChapterStoneFlows` (the packaged `IsStoneFlow` and the concrete flows for the
Eulerian NS, Lagrangian NS and QYM Hamiltonians) and `BookProof.ChapterUnboundedSpectralModel`
(the diagonalizing unitary, via the resolvent route), all registered in
`BookProof.lean`, certified in `BookProof/ChapterRoadmapAudit.lean`, and `#check`-ed
from the `ConditionalUnitary` chapter's "A Less Arbitrary Construction" section.
