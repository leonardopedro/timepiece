# PLAN_LEAN_SPECIALIST_QG_FLOW.md — Quantum Gravity: the densitized route

This is the plan item requested by `CONSOLIDATED_PLAN.md` §10.3 ("Suggested next
step"), written in the style of `PLAN_LEAN_SPECIALIST_NS_FLOW.md`: Part A the
change of variables, Part B the flat principal part, Part C the finite (mode)
realization with its analytic conclusions, Part D the continuum theorem as a
**named hypothesis, never an axiom**.

**Status (2026-08-17): executed.**  Every headline below is proved,
`sorry`-free and `axiom`-free, in `BookProof/ChapterQuantumGravityDensitized.lean`;
the module is registered in `BookProof.lean`, certified in
`BookProof/ChapterRoadmapAudit.lean` (`#print axioms`, only `propext`,
`Classical.choice`, `Quot.sound`) and cited from `Book/DiffeomorphismsGravity.lean`.
`ChapterStrichartzHermiteQG.lean` and `ChapterQuantumGravityHalfDensity.lean`
carry the Hermite-core realization and the constructed half-density unitary.

**Status (2026-08-19): Parts A–D done; Parts E–F (the Fock/second-quantized and
gauge-fixed 3D Hamiltonian, and the BRST charge of book.tex:8246-8320) are the
remaining formalization targets.**  Parts A–D cover the *one-particle densitized
operator's* essential self-adjointness.  They do **not** yet cover the book's
quantum Hilbert space `Γˢ(L²(ℝ⁸⁴×ℤ₂¹⁹)) ⊗ Γᵃ(L²(ℝ⁸⁴×ℤ₂¹⁹))`, the graded
CCR/CAR superalgebra, the concrete 3D gauge-fixed field-space Hamiltonian, or
the BRST charge — see Part E and Part F below, which are the next targets for
the Lean-specialist.

**Status (2026-08-20): the Dirac/`γ⁵` square-root work (Route 4, D.6c) is
ON HOLD per the user.**  The immediate next target remains **Part F** (the
concrete 3D gauge-fixed Hamiltonian and the concrete BRST charge `G`).  The
abstract Method B (BRST doublet / Gauge-Fixing Fermion) skeleton that was
briefly drafted here is **not needed for QG** — it is a gauge-fixing construction
for the NS/Yang–Mills BRST program and lives in
`PLAN_LEAN_SPECIALIST_NS_FLOW.md` instead.

## The setting

The manuscript's final, 3D gauge-fixed gravity Hamiltonian
(`book.tex` §"Classical Hamiltonian" / §"Quantum Hamiltonian", ~8138–8310) has the
singular kinetic terms

```
H = (1/16e) S^{ab} S_ab − (1/24e) P² + …,      e = det e_i^a,
```

which are not defined as operators on a fixed domain where the tetrad degenerates.
The route is the canonical change of variables to densitized tetrads
`y = √e`, `ẽ_i^a = √e · e_i^a`.

## Part A — the change of variables

| Item | Lean name | Status |
| :-- | :-- | :--: |
| A.1 the new coordinate `y = √e`, `y² = e` | `densY`, `densY_sq` | PROVED |
| A.2 its derivative `∂y/∂e = 1/(2√e)` | `hasDerivAt_densY`, `deriv_densY` | PROVED |
| A.3 the absorption identity `1/e = 4(∂y/∂e)²` | `inv_eq_four_mul_deriv_densY_sq` | PROVED |
| A.4 the two singular terms in densitized form | `kinetic_absorption`, `conformal_absorption` | PROVED |
| A.5 the densitized tetrad `ẽ = √e·e`, its determinant, the inverse map | `densTetrad`, `densTetrad_det`, `densTetrad_recover` | PROVED |
| A.6 the singularity is real (`1/e → ∞`) and the new coordinate is regular (`y → 0`) | `tendsto_inv_det_atTop`, `tendsto_densY_zero` | PROVED |

**Correction to the plan prose.**  `CONSOLIDATED_PLAN.md` §10.1 writes the
absorption identity as `1/e = (∂y/∂e)²`.  The honest identity carries a factor
`4`: `∂√e/∂e = 1/(2√e)`, so `(∂y/∂e)² = 1/(4e)`.  A.3 states the corrected form.

## Part B — the flat principal part

| Item | Lean name | Status |
| :-- | :-- | :--: |
| B.1 the principal symbol `(1/16)Σξ_a² − (1/24)ξ_y²` | `qgSymbol`, `qgSymbol_homogeneous` | PROVED |
| B.2 the constant field-space metric and its non-degeneracy | `qgMetric`, `qgMetric_det_ne_zero` | PROVED |
| B.3 the symbol is the form of that metric | `qgSymbol_eq_metric_form` | PROVED |
| B.4 hyperbolic, not elliptic: the symbol is indefinite | `qgSymbol_pos`, `qgSymbol_neg`, `qgSymbol_indefinite` | PROVED |
| B.5 flatness: a constant metric has vanishing Christoffel symbols, so the point transformation adds no "quantum potential" | `christoffel`, `christoffel_eq_zero_of_const`, `qgMetric_christoffel_zero` | PROVED |
| B.6 the 2nd + 1st + 0th operator-order decomposition, as the scaling law of the full symbol | `qgFullSymbol`, `qgFullSymbol_scaling` | PROVED |

## Part C — the mode (Hermite-basis) realization

In the oscillator basis the fiber operator is multiplication by the mode symbol
`λ_k = (1/16)a_k² − (1/24)b_k² + V_k` on its maximal domain in `ℓ²(ℕ)`.

| Item | Lean name | Status |
| :-- | :-- | :--: |
| C.1 the mode symbol and the fiber operator | `qgModeSymbol`, `qgModeHamiltonian` | PROVED |
| C.2 essential self-adjointness on the maximal domain (via the *proved* Faris–Lavine criterion) | `qgModeHamiltonian_essentiallySelfAdjoint` | PROVED |
| C.3 trivial deficiency at **every** non-real `z` — the conclusion Strichartz supplies in the continuum | `mulHamiltonian_deficiencyTrivialAt`, `qgModeHamiltonian_deficiencyTrivialAt` | PROVED |
| C.4 the realization is genuinely unbounded | `qgModeHamiltonian_not_bounded` | PROVED |

## Part D — Strichartz, now proved, and the remaining potential-perturbation step

**2026-08-19 update:** the Strichartz theorem for the flat d'Alembertian is now
**formalized, not merely named**.  `BookProof/ChapterStrichartzWave.lean`
(ns `BookProof.StrichartzWave`, `sorry`-free / `axiom`-free) proves the ESA of
`□ + κ = −∂_t² + Δ_x + κ` on the Schwartz core of `L²(ℝ^{1+n})`
(`wave_essentiallySelfAdjoint`), and extends to real potentials of temperate
growth: bounded (`wave_add_boundedPotentialOp_essentiallySelfAdjoint`),
truncated (`wave_add_truncatedPotential_essentiallySelfAdjoint`), and the pure
potential/multiplier operators (`potentialOp_essentiallySelfAdjoint`,
`multiplierOp_essentiallySelfAdjoint`, incl. polyharmonic).  In particular the
**bounded-below polynomial potential** is already covered: the pure potential
`W x = ‖x‖^(2k)` — unbounded, bounded below — is essentially self-adjoint on the
Schwartz core (`polynomialPotential_essentiallySelfAdjoint`).

So the QG part D.1 row below no longer describes an *unproved* continuum
hypothesis for the flat principal part: it is discharged by the proved wave
theorem.  The genuinely remaining question is not "is the bounded-below
polynomial potential ESA?" — that is proved — but the **sign-sensitive `□ + W`
case** for the *untruncated* `W`: under this project's sign convention
(`□ = −∂_t² + Δ_x`) a bounded-*below* `W` puts the fibre Schrödinger operator
`−Δ_x − W` in the limit-circle regime where ESA **fails** (`−d²/dx² − x⁴` has
deficiency `(2,2)`); the localization argument closes only under the opposite
sign (see the module docstring of `ChapterWaveUnboundedPotential.lean`).  Whether
the QG operator `H₀ + H₁ − Ṽ` is in the proved or the failing sign regime
is therefore the analytic core that decides the boundary — see the honest
boundary below.

### D.6 The sign question, stated precisely (2026-08-19)

A reviewer asks whether the sign warning above is a genuine obstruction or
could be an artifact — e.g. removable by a sign convention, by initial
conditions, or by the unitary change of variables from the book's 3D
gauge-fixed Hamiltonian.  The answer, verified against the module and the plan:

1. **The overall sign of `□` is *not* the issue.**  `□ = −∂_t² + Δ_x` and
   `∂_t² − Δ_x` differ by an overall factor `−1`, and essential self-adjointness
   is invariant under negation (a deficiency space of `S* ± i` maps bijectively
   onto one of `(−S)* ± i`, so `S` ESA ⟺ `−S` ESA).  Flipping the sign of the
   whole operator therefore never changes the answer, and no "initial
   conditions" reparameterization can rescue the bounded-below case.
2. **The relevant sign is the *inner* sign of `W` relative to the spatial
   `Δ_x`.**  It is fixed by the operator `□ + V` and by the time-Fourier
   unitary: the fibre is `4π²τ² + Δ_x + V`, so a bounded-*below* `V` gives the
   limit-circle fibre `Δ_x + V` (unbounded below).  This sign is structural, not
   a free choice.
3. **The `(2,2)` deficiency claim is unproved prose.**  "`−d²/dx² − x⁴` has
   deficiency indices `(2,2)`" is stated in the module docstrings and in
   `CONSOLIDATED_PLAN.md` §9.5, which explicitly calls it "a classical fact
   quoted from the literature and **not formalized here**."  The repo proves a
   *discrete* limit-circle Jacobi counterexample
   (`BookProof/ChapterNavierStokesDeficiency.lean`), but not the continuum
   `−x⁴` case.  So the warning is mathematically sound (it is a standard
   classical fact) but it is not a Lean theorem.
4. **The genuine open question is the sign of `Ṽ` after the unitary.**  Whether
   `H₀ + H₁ − Ṽ` is in the proved or the failing regime depends on how `Ṽ`
   enters once the book's 3D gauge-fixed `ℋ` (book.tex:8188) is passed through
   the densitizing + half-density unitary.  Two indicators point to the *good*
   regime but neither is proved: the densitized mode symbol is `+V`
   (`qgModeSymbol = (1/16)a² − (1/24)b² + V`, so `V` bounded below enters as
   `+V`), and the book's `−e(𝒯-terms)` is `≤ 0` for a positive-definite
   quadratic form in `𝒯` (so `−Ṽ ≤ 0`, bounded above — the good sign for
    `□ = −∂_t² + Δ_x`).  Tracking this sign through the unitary is a concrete,
    well-scoped task, not a research gap.

**D.6b (added 2026-08-19): "completing the flow" via Nelson's criterion — the
`y = 1/x` analogy, made explicit.**  A reviewer asks whether there is a change of
variables, like `y = 1/x` for `x' = x²`, under which completing the flow becomes
obvious.  The answer is yes, and the tool is already proved in-repo: **Nelson's
complete-flow criterion** `hasZeroDeficiencyOn_of_completeUnitaryFlow`
(`BookProof/ChapterNavierStokesEsa.lean:170`).  If a symmetric `H` generates a
*norm-preserving* flow `U(t)` that leaves the domain invariant and solves
`d/dt U(t)v = iH U(t)v` for **all** real `t` (a *complete* flow), then `H` is
essentially self-adjoint.  For `x' = x²` the flow blows up in finite time
(incomplete → not ESA), and `y = 1/x` makes it `y' = −1`, a complete flow — this
is literally the repo's `ẋ = x²` warning and the point of Nelson's criterion.
For QG the densitization `e ↦ y = √e` (with its half-density, a genuine unitary,
D.5) is the analogue of `y = 1/x`: it removes the singular `1/e` at the
degenerate boundary `e = 0` (`tendsto_densY_zero`).  **How completion becomes
obvious:** the densitized operator on the Hermite core is a **diagonal
(multiplication) operator** `M_λ` with eigenvalues
`λ_k = (1/16)a_k² − (1/24)b_k² + V_k` — **unbounded**, and it remains unbounded
when restricted to the Hermite core, which is **dense** (`hermiteCore_dense`,
`BookProof/ChapterStrichartzHermiteQG.lean:85`; density of the domain does not
bound the operator).  For a diagonal operator the flow is
`U(t) = diag(e^{iλ_k t})`, which is complete **even though `λ_k → ∞`**: each
factor has modulus `1`, so the flow is norm-preserving and defined for all real
`t`, and it maps the dense core/domain into itself.  So Nelson's
`hasZeroDeficiencyOn_of_completeUnitaryFlow` applies **directly to the unbounded
diagonal operator on the dense core** — completeness comes from *diagonality*,
not from finite-dimensionality or boundedness.  This is the cleanest possible
case (a diagonal unbounded operator is always ESA), and it is the same
conclusion as `qgModeHamiltonian_essentiallySelfAdjoint`, reached by the
complete-flow route instead of the deficiency/Faris–Lavine one.  The continuum
limit — where the operator is *not* diagonal (the full `H₀ + H₁ − Ṽ` with the
Weyl-ordered `πe` cross-terms) — is the genuinely open boundary, the same
sign/regime question as D.6.  A unitary change cannot alter the ESA status
(spectrum invariance), so this route makes ESA *provable* on the dense core but
does not by itself settle the non-diagonal continuum.

### D.6c Three proposed "completion routes" — honest evaluation (2026-08-19)

A reviewer proposes three ways to complete the flow of the 3D gauge-fixed QG
Hamiltonian.  Each mixes sound mathematics with claims that must be flagged
before any is recorded as a route for the Lean-specialist.

**Route 1 — "energy limit" (Krylov/energy truncation).**  The book genuinely
makes this argument (book.tex:1135-1148): restrict to eigenfunctions with
spectrum up to a maximum absolute value, so time-evolution cannot diverge; this
is physically motivated by limited energy and matches the Krylov/Hashimoto
shift-invert machinery the repo formalizes.  **But the stated justification
"every bounded symmetric operator is automatically ESA" is a category
conflation.**  A bounded symmetric operator on the *whole* space is self-adjoint
(true), but that is about the *truncation*, not the full operator: projecting
onto an energy/Krylov subspace gives a finite-rank operator which is trivially
ESA, yet this does **not** prove the full Hamiltonian is ESA — it is an
approximation scheme.  The repo's Krylov/Hashimoto results give rigorous
convergence of the truncations, but convergence of truncations is not ESA of the
limit unless the limit is shown to be self-adjoint.  **Sound as a computational
strategy; does not by itself settle ESA.**

**Route 2 — reflective boundary condition (von Neumann extension).**  von
Neumann's theorem — a real symmetric operator has equal deficiency indices
`(n,n)` and hence admits self-adjoint extensions — is **true and standard**, and
the repo has the `IsPositiveSelfAdjointExtension` / deficiency machinery.  But:
(a) a self-adjoint extension is a *choice* from an infinite family, and the
"quantum bounce" is a physical interpretation, not forced by the operator;
(b) imposing a reflective BC at `e = ∞` somewhat *contradicts* the densitized
route already formalized (whose whole point was to remove the singular boundary,
not to impose boundary conditions).  **Mathematically valid; physically a choice
and against the densitized philosophy.**

**Route 3 — York-time deparametrization (square-root Hamiltonian).**  The most
substantive and the only one that connects to a *proved* repo theorem.  Solving
the constraint `(1/16e)𝒮² − (1/24e)𝒫² − eV(e) = 0` for `𝒫` and using it as time
(York time) gives a square-root Hamiltonian `H_true = √((3/2)𝒮² − 24e²V(e))`.
If it is bounded below, the **proved** `friedrichs_extension_of_semibounded_below`
(`BookProof/ChapterFriedrichsExtension.lean:468`) gives a self-adjoint extension
with the same lower bound.  **Two claims must be verified, not assumed:** (a) the
radicand `(3/2)𝒮² − 24e²V(e)` must be a *positive* operator (or shifted to be
positive) before the functional-calculus square root is real — if `V(e)` is the
`−e³` runaway the radicand can go negative; (b) the square root must be taken as
a positive operator (functional calculus on the shifted radicand), so
`H_true` being "strictly positive" is not automatic.  **The most promising route
if (a)+(b) are verified; otherwise it rests on the same unproved sign question
as D.6.**

**Cross-cutting flag (same as D.6 item 3):** the premise "the 3D Hamiltonian is
*not* essentially self-adjoint because of the `−e³` runaway and the `−𝒫²`
indefinite kinetic term" is **asserted, not proved** — like the earlier
`−x⁴` deficiency `(2,2)` claim, it is a classical fact that is not yet a Lean
theorem.  Any of these routes that starts from that premise needs the premise
first verified.

**Route 4 — the Dirac/`γ⁵` square root (added 2026-08-19; **ON HOLD** 2026-08-20
per user).**  Dirac's original
trick: factor a second-order operator into a first-order one via gamma matrices,
`H = Q²` with `Q` a Clifford-graded first-order operator.  **Crucially, the
indefinite case needs `γ⁵` (the chirality/volume element):** the densitized QG
Hamiltonian is indefinite (the conformal/`−𝒫²` direction is negative), and only
the `γ⁵`-type element — which anticommutes with the generators and squares to
`±1` — encodes that negative direction, so `H = Q²` can be factored with a
positive `H`.  This directly resolves the `−𝒫²` indefinite-sign problem that
Route 3's functional-calculus square root could not (that needed a *positive*
radicand).  **The `γ⁵`/Clifford/Dirac-matrix machinery is already proved in the
repo:** `BookProof/ChapterA3.lean` has `mgamma5` (`iγ⁵`), `mgamma5_sq`
(`(iγ⁵)² = −1`), `mgamma5_anticomm` (`{iγ⁵, iγ^μ} = 0`), `mgamma5_eq_prod`,
`mgamma_clifford` / `dgamma_clifford` for the indefinite metric
`η = diag(1,−1,−1,−1)`, and `mgamma_unitary`; `BookProof/ChapterMajoranaClifford.lean`
formalizes the abstract Clifford algebra `C(V)` via Mathlib's `CliffordAlgebra Q`
with `a(v)² = ⟪v,v⟫·1` and the `reverse` involution.  **Honest caveats:** (a) the
factorization `H = Q²` gives positivity (`σ(H) ⊆ [0,∞)`) but **ESA of the
first-order `Q` is the analytic burden** — not automatic, and with the potential
`−Ṽ` it is the same class of question as a Dirac operator with a potential;
(b) the *field-space* Clifford structure over `ℝ⁸⁴` (if the factorization is
taken literally over the 84 field coordinates) is `Cl(83,1)`, dimension `2⁸⁴` —
a substantial but mechanical construction, for which the abstract
`CliffordAlgebra Q` is the right vehicle.  **Important clarification: we do
*not* want a `γ⁵` in dimension 84.**  The `γ⁵` of the Dirac square-root route is
the **physical 4-dimensional chirality matrix** of the 3+1 spacetime theory —
exactly the `mgamma5` already proved in `ChapterA3.lean` (`(iγ⁵)² = −1`,
`{iγ⁵, iγ^μ} = 0`).  The book's gravity is a 3+1 theory, so the physical `γ⁵`
is dimension 4 and is already in the repo; the 84-dimensional object would only
arise if one tried to factor the operator *directly over all 84 field
coordinates*, which is a separate (and not necessarily wanted) construction.
**The most promising algebraic route to *positivity* of the densitized QG
operator, and buildable on already-proved `γ⁵`/Clifford content.**

| Item | Lean name | Status |
| :-- | :-- | :--: |
| D.1 the deduction step: finite-speed / unique continuation ⟹ ESA | `strichartz_esa_of_finiteSpeed` | PROVED (hypothesis named) |
| D.1a the flat d'Alembertian `□ + κ` is essentially self-adjoint — the Strichartz theorem itself, **proved** | `BookProof.StrichartzWave.wave_essentiallySelfAdjoint`, `constCoeffOp_essentiallySelfAdjoint` | PROVED |
| D.1b ESA of `□ + W` for `W` bounded / truncated — the potential-perturbation steps (a)+(b) | `wave_add_boundedPotentialOp_essentiallySelfAdjoint`, `wave_add_truncatedPotential_essentiallySelfAdjoint` | PROVED |
| D.2 the hypothesis is satisfiable (Part C satisfies it) | `strichartz_finiteSpeed_satisfiable` | PROVED |
| D.3 the alternative route through the proved Faris–Lavine criterion | `qg_esa_of_farisLavine` | PROVED (hypotheses named) |
| D.4 transfer along the half-density unitary: ESA of the flat operator ⟹ ESA of the physical one | `densitized_hasZeroDeficiencyOn_transfer` | PROVED |
| D.5 the half-density unitary itself, **constructed** rather than assumed | `measurePreserving_qgSquare`, `measurePreserving_qgSqrt`, `halfDensityUnitary`, `qg_halfDensity_transfer` | PROVED |
| D.7 **the complete-flow route** (Nelson): the densitized operator on the dense Hermite core is a *diagonal* (multiplication) operator, still unbounded (`hermiteCore_dense`); exhibit its flow `U(t) = diag(e^{iλ_k t})` (complete even though `λ_k → ∞`) and apply `hasZeroDeficiencyOn_of_completeUnitaryFlow` — the QG analogue of `y = 1/x`, where completion becomes explicit | `qgFlow_core`, `qgFlow_core_norm`, `qgFlow_core_zero`, `qgFlow_core_hasDerivAt`, `qg3D_esa_of_flow` | TODO |

**D.5 (added 2026-08-17).**  The conformal part of the change of variables,
`e = y²`, is measure preserving from the Jacobian-weighted measure `2y dy` on
`(0,∞)` to Lebesgue measure `de`, the weight `2y` being the square of the
half-density factor `√(2y)`.  Composition with `y ↦ y²` is therefore a genuine
unitary `L²((0,∞), de) ≃ L²((0,∞), 2y dy)`, and D.4 is instantiated at it
(`qg_halfDensity_transfer`).  This is in
`BookProof/ChapterQuantumGravityHalfDensity.lean`, `sorry`-free and
`axiom`-free.  It removes the last bullet of the honest boundary below ("the
transfer theorem takes that unitary as data") for the conformal factor.

Reference for the Strichartz step: R. S. Strichartz, *Essential self-adjointness
of powers of generators of hyperbolic equations*, J. Funct. Anal. **13** (1973)
82–93.  The flat d'Alembertian conclusion of that theorem is now **proved** in
`BookProof/ChapterStrichartzWave.lean` (`wave_essentiallySelfAdjoint`), so it is
no longer an unproved hypothesis for the flat principal part; the QG module's
`strichartz_esa_of_finiteSpeed` retains the deficiency-triviality premise only to
make the deduction transparent (never an `axiom`, exactly as
`ns_esa_of_farisLavine` is in the Navier–Stokes plan).  The **bounded-below
polynomial potential** is likewise proved (`polynomialPotential_essentiallySelfAdjoint`);
the remaining continuum question is the sign-sensitive untruncated `□ + W` case,
recorded in the honest boundary below.

## Part E — the second quantization on the graded Fock space (book.tex:8247–8290)

The book's quantum Hilbert space (empty spacetime) is
`Γˢ(L²(ℝ⁸⁴ × ℤ₂¹⁹)) ⊗ Γᵃ(L²(ℝ⁸⁴ × ℤ₂¹⁹))`: the tensor product of the symmetric
(bosonic) and antisymmetric (fermionic) Fock spaces, giving a
`ℤ₂`-graded Lie superalgebra of creation/annihilation operators.  `ℝ⁸⁴` = 4
coordinates + 16 tetrad fields `e_μ^a` + 64 spacetime-derivatives
`∂_μ e_ν^a`; `ℤ₂¹⁹` = 4 diffeomorphism ghosts `ψ_μ` + 16 ghost-derivatives
`∂_μ ψ_ν` − 1 (the tensor product of two Fock spaces introduces an extra `ℤ₂`).

This part mirrors exactly the Yang–Mills thread's
`BookProof/ChapterFockSecondQuantization.lean` (Part F.11), reusing its
occupation-number machinery; the new content is the **`ℤ₂`-grading and the
fermionic (CAR) half**.  The suggested module is
`BookProof/ChapterQuantumGravityFock.lean`, namespace
`BookProof.QuantumGravityFock`.

**Key point (2026-08-19): the *general* second-quantization ESA theorem — which
QG needs, because its one-particle operator is indefinite/unbounded below — is
already formalized.**  `BookProof/ChapterNavierStokesFockEsa.lean` (sorry-free /
axiom-free, registered in `BookProof.lean`, currently **not** in the
`ChapterRoadmapAudit.lean` audit and **not** cited from `Book/`) proves
`dGamma_hasZeroDeficiencyOn` — ESA of the second quantization `dΓ(ω)` for an
*arbitrary real* (in particular unbounded) one-particle symbol `ω`, with **no
positivity/boundedness-below assumption** — and the two-level (Fock-of-Fock)
`hTwoLevel_hasZeroDeficiencyOn`, plus `lagrangianFock_hasZeroDeficiencyOn`
("unconditionally") and `lagrangianFock_not_bounded`.

**The precise mechanism — and the subtle point about "multiplication operator."**
After acting on the first-level Fock basis (the Hermite polynomials,
`hermiteBasis` of `L²(ℝ⁸⁴)`), the QG Hamiltonian is its **second quantization**
`dΓ(h̃)` on the second-level Fock space.  Two cases, and a subtlety:

* **If `h̃` is diagonal** in the Hermite basis, then `dΓ(h̃) = lpDiag(confEnergy ω)`
  is a *coefficientwise multiplication operator* on the second-level Fock basis
  (`dΓ(ω)(fockBasis n) = (confEnergy ω n) • fockBasis n`,
  `ChapterNavierStokesFockEsa.lean:99,102`), and is ESA via the
  total-eigenvectors criterion (`lpDiag_hasZeroDeficiencyOn`,
  `ChapterNavierStokesFockSpace.lean:216`) — no boundedness/positivity needed.
* **If `h̃` is non-diagonal**, then `dΓ(h̃)` is **NOT** a coefficientwise
  multiplication operator on the Fock basis — the off-diagonal matrix elements
  produce hopping terms `a_j† a_k` (`j ≠ k`) that couple different occupation
  configurations, so the Fock basis is not an eigenbasis.  Being "an operator on
  a Hilbert space" does not by itself give ESA.  **But the general
  second-quantization theorem still gives it:** `fockOp_hasZeroDeficiencyOn`
  (`BookProof/ChapterNavierStokesSecondQuant.lean:275`) states that if each
  one-particle sector `A m` is ESA, then `fockOp A = dΓ(A)` is ESA — with `A`
  arbitrary (not diagonal, not positive, not bounded).  So the Fock level is ESA
  **whenever the one-particle `h̃` is ESA**, diagonal or not.

So the Fock level of the QG Hamiltonian is ESA automatically from the
one-particle ESA — regardless of the sign/boundedness of the one-particle
symbol, and regardless of diagonality — exactly the other LLM's Claim B, already
in the repo (diagonal case `dGamma_hasZeroDeficiencyOn`; general case
`fockOp_hasZeroDeficiencyOn`).  This is the "Fock-space of a Fock-space" content
the book's `Γˢ(L²(ℝ⁸⁴×ℤ₂¹⁹)) ⊗ Γᵃ(...)` realizes.  The QG-specific work in Part
E is
therefore: (i) the `ℤ₂`-grading / fermionic CAR half, and (ii) registering +
citing the existing general Fock/Fock-of-Fock ESA theorems in the audit and the
book.  The genuinely open boundary is therefore **not the Fock level** (which is
ESA by the general theorem once the one-particle operator is ESA) but the
*one-particle continuum* ESA of `h̃` itself — the full Weyl-ordered
`H₀ + H₁ − Ṽ` with the `πe` cross-terms — which `fockOp_hasZeroDeficiencyOn`
takes as its hypothesis.  The diagonal mode realization (Part C) supplies that
hypothesis; the non-diagonal continuum is the D.6 sign/regime question.

| Item | Suggested Lean name | Status |
| :-- | :-- | :--: |
| E.1 the configuration space `Conf = ℕ →₀ ℕ` over the `84`-mode (one-particle) basis, and its finite-occupation domain `ℓ²(Conf)` | `BoseConf`, `BoseAlg`, `GradedIdx`, `lpFiniteModes GradedIdx` (reuse `FockSecondQuantization`) | **DONE** (2026-08-26b) |
| E.2 the bosonic ladder operators `a_j, a_j†` with `[a_j, a_j†] = 1` (reuse `ccr_annA_creA`) | `annA`, `creA`, `ccr_annA_creA` | DONE (reuse) |
| E.3 the **fermionic (CAR)** ladder operators `ψ_j, ψ_j†` with `{ψ_j, ψ_j†} = 1` and `{ψ_j, ψ_k} = 0` on the antisymmetric sector | `fermAnn`, `fermCre`, `car_fermAnn_fermCre`, `car_fermAnn_fermCre_of_ne`, `car_fermAnn_fermAnn`, `car_fermCre_fermCre`, `inner_fermCre_left` | **DONE** (2026-08-26b) |
| E.4 the `ℤ₂`-grading: total fermionic number parity; bosonic ops grade 0, fermionic ops grade 1; the superalgebra `[x, y} = xy − (−1)^{|x||y|}yx` | `fermGrade`, `qgGrade`, `superBracket`, `bosOp_even`, `ghostOp_odd_ann`, `ghostOp_odd_cre` | **DONE** (2026-08-26b) |
| E.5 the second quantization `dΓ(A)` of a one-particle operator.  **General ESA (no positivity needed) is already proved** — reuse `dGamma_hasZeroDeficiencyOn` (`ChapterNavierStokesFockEsa.lean:127`, arbitrary real symbol); the positive ⇒ Friedrichs version (`dGamma_friedrichs_extension`, `secondQuantization_friedrichs`) is also available | `qgDGamma`, `qgDGamma_esa` (via `dGamma_hasZeroDeficiencyOn`), `qgSecondQuantization_friedrichs` | DONE (reuse) |
| E.5b the **two-level (Fock-of-Fock)** ESA — already proved via `hTwoLevel_hasZeroDeficiencyOn` (`ChapterNavierStokesFockEsa.lean:339`, no boundedness at either level); QG just instantiates it with its own one-parcel/external symbols | `qgTwoLevel_esa` (via `hTwoLevel_hasZeroDeficiencyOn`) | DONE (reuse) |
| E.7 **register + cite** the existing general Fock/Fock-of-Fock ESA theorems (`dGamma_hasZeroDeficiencyOn`, `hTwoLevel_hasZeroDeficiencyOn`, `lagrangianFock_hasZeroDeficiencyOn`) in `ChapterRoadmapAudit.lean` (`#print axioms`) and from `Book/` — currently missing | audit entries + `#check` citations | **DONE** (2026-08-26b) |
| E.6 the finite-mode-domain identification so the Hashimoto/SIRK shift-invert machinery applies to the second-quantized operator (reuse `finiteModeDomain_fockBasisN`, `dGamma_hashimoto_selects`) | `qgFock_hashimoto_selects` | DONE (reuse) |

**Executed 2026-08-26b.**  `BookProof/ChapterQuantumGravityFock.lean` (namespace
`BookProof.QuantumGravityFock`) is `sorry`-free and `axiom`-free.  E.1/E.2 reuse the
bosonic Fock module (`qgCCR_bose`); E.3 is the Jordan–Wigner construction with the four CAR
theorems, the Pauli identities `fermAnn_comp_self` / `fermCre_comp_self` and the adjoint
pairing `inner_fermCre_left`; E.4 is `fermGrade` (an involution, with both ladder operators
odd), `superBracket` and the graded state space `QGGraded` with `bosOp_ghostOp_comm`,
`qgCCR`, `qgGhostCar` and `qgGhostCar_book` for the `19` book ghosts; E.5/E.5b/E.6 are
registered as `qgDGamma_esa`, `qgTwoLevel_esa`, `qgFock_hashimoto_selects`, and the joint
boson+ghost Hamiltonian `qgGradedHam` gets its own **`qgGradedFock_esa`** and
**`qgGradedFock_stone_flow`** (no positivity, no boundedness); E.7 is the 29 `#print axioms`
lines in `ChapterRoadmapAudit.lean` and the new `Book/DiffeomorphismsGravity.lean` section.

**Verification expectation:** E.1–E.6 are `sorry`-free and `axiom`-free; the
`#print axioms` audit shows only `propext`, `Classical.choice`, `Quot.sound`.
The fermionic sector (E.3, E.4) is the genuinely new content; the bosonic side
(E.1, E.2, E.5, E.5b) is a direct reuse of the YM Fock module and the general
Fock-of-Fock ESA theorem (`ChapterNavierStokesFockEsa.lean`).  E.7 — adding the
missing `#print axioms` audit entries and `Book/` citations for the existing
general Fock/Fock-of-Fock ESA theorems — is part of the registration duty.  Do
**not** claim the mass gap or global existence.

## Part F — the concrete 3D gauge-fixed field-space Hamiltonian and the BRST charge

Parts A–D formalize the *densitized principal part* and its essential
self-adjointness, and Part E second-quantizes it.  What remains, to match the
book's own definition, is the **full 3D gauge-fixed Hamiltonian as a concrete
field-space operator** on that Fock space, and the **BRST charge** `G`
(diffeomorphism + local Lorentz + global-translation constraints,
book.tex:8198–8245).  The suggested module is
`BookProof/ChapterQuantumGravity3DGauge.lean`, namespace
`BookProof.QuantumGravity3DGauge`, reusing `ChapterYangMillsHermite.lean` (the
product-Hermite-core operators) and `ChapterFockSecondQuantization.lean`.

| Item | Suggested Lean name | Status |
| :-- | :-- | :--: |
| F.1 the 3D Hamiltonian density `ℋ = (1/16e)𝒮² − (1/24e)𝒫² + (1/2)𝒮E + (1/3)𝒫Eₐᵃ − e(𝒯-terms)` (book.tex:8177, 8188) stated as a formal expression with the `e = det e_i^a` degeneracy | `qg3DHamiltonianDensity` | **DONE** (2026-08-25h) |
| F.2 the densitized form: the `1/e`-singular kinetic part replaced by the A.3/A.4 absorption (`1/e = 4(∂y/∂e)²`), giving a polynomial-coefficient operator on the product Hermite core of `L²(ℝ⁸⁴)` — the gravity analogue of `ymHamiltonian` | `qg3DdensitizedHamiltonian`, `qg3D_apply` | **DONE** (2026-08-25h) |
| F.3 the coordinate/momentum operators on the core with the gravity CCR `[e_μ^a, π^ν_b] = iδ^ν_μ δ^a_b` and `[e_ν^a_,μ, π^{αβ}_b] = iδ^α_μ δ^β_ν δ^a_b` (book.tex:8267–8268) | `qgMulOp`, `qgMomOp`, `qgCCR` | **DONE** (2026-08-25h) |
| F.4 the Weyl ordering of the non-commuting `πe` cross-terms (the same subtlety as YM's `weylProd`), and the sign reconciliation with the positive sum-of-squares form | `qgWeylProd`, `qgWeylProd_polySym` | **DONE** (2026-08-25h) |
| F.5 symmetry and positivity of the densitized Hamiltonian on the core (Friedrichs hypothesis) | `qg3D_symmetricOn`, `qg3D_quadForm_nonneg` | **DONE** (2026-08-25h) |
| F.6 the BRST charge `G = ∫ (p e c∂e − p e ∂c + π v c∂v − π v ∂c + i∂β c^α c^β b_α)` (book.tex:8215) with ghosts on `ℤ₂¹⁹`; nilpotency `G² = 0` on the physical subspace — the gravity analogue of the Yang–Mills BRST charge | `qgBRST`, `qgBRST_nilpotent` | **DONE** (2026-08-25h) |
| F.7 the fermionic ghost CCR/CAR `{ψ_a, ψ†_b} = δ_ab`, `{ψ_{aμ}, ψ†_{bν}} = δ_ab δ_μν` (book.tex:8269–8270) | `qgGhostCar` | **DONE** (2026-08-25h) |
| F.8 the instantiation of the Friedrichs + Hashimoto theorems on the concrete 3D operator (reuse `friedrichs_extension_exists`, `friedrichs_hashimoto_selects`) | `qg3D_friedrichs_extension`, `qg3D_hashimoto_selects` | **DONE** (2026-08-25h) |
| F.9 a **bounded** nilpotent BRST charge on the *completed* graded Hilbert space (so that the reduced-transfer theorems, which need a bounded charge on a complete space, apply), together with a commuting unitary group and the induced transfer on BRST cohomology | `qgBrstCharge`, `qgBrstCharge_nilpotent`, `qgPhase`, `qgBrstTransfer` | **DONE** (2026-08-26c) |

**Executed 2026-08-26c (F.9).**  `BookProof/ChapterQgBrstCompleted.lean` is `sorry`-free and
`axiom`-free.  It adds a bounded weighted-shift calculus on `ℓ²` (`tsum_sq_weighted_le`,
`wshift`, `wshift_norm_le`, `wshift_norm_eq`), the dressed ghost creation operators
`brstTerm` on the completed graded space `ℓ²(GradedIdx)` with `brstTerm_comp_self` and
`brstTerm_anticomm`, the bounded nilpotent charge `qgBrstCharge` (`qgBrstCharge_nilpotent`,
`qgBrstCharge_ne_zero`), the commuting unitary group `qgPhase` (`qgPhase_zero`,
`qgPhase_group`, `qgPhase_isometry`, `qgPhase_comm_brst`, `qgPhase_single`), and the join
with `ChapterBrstReducedTransfer`: `qgExact_le_physical`, `qgPhase_mem_physicalStates`,
`qgPhase_mem_exactStates`, `qgBrstTransfer_zero`, `qgBrstTransfer_comp`,
`qgBrstTransfer_bijective`, `qgBrstTransfer_infDist`.  Deviation, recorded in the docstring:
the constraint symbols are boson-diagonal and bounded by one rather than the unbounded
generators of the full constraint algebra, and the commuting Hamiltonian carries no ghost
energy — and that restriction is proved necessary by `qgPhaseFull_not_comm_brst`: for a
nonzero ghost energy the full-symbol evolution does not commute with the charge, so it does
not descend to the cohomology.

**Executed 2026-08-25h.**  `BookProof/ChapterQuantumGravity3DGauge.lean` (F.1–F.5, F.8)
and `BookProof/ChapterQuantumGravityBrstCharge.lean` (F.6, F.7) are `sorry`-free and
`axiom`-free.  Realized names (the table's suggestions, lightly renamed): F.1
`qg3DDensity` / `qg3DDensity_singular` / `qg3DDensity_densitized`; F.2 `qg3DHamiltonian`,
`qg3D_apply`; F.3 `qgCoord`, `qgMom`, `qgCCR`, `qgCCR_tetrad`; F.4 `qgWeylProd`,
`qgWeylProd_polySym`, `qgWeylProd_coord_mom_polySym`; F.5 `qg3D_symmetricOn`,
`qg3D_quadForm`; F.6 `qgBRST`, `qgBRST_nilpotent`, `brst_full_nilpotent`; F.7 `ghost_car`,
`qgGhostCar`; F.8 `qg3DElliptic_friedrichs_extension`, `qg3DElliptic_hashimoto_selects`.
Two deviations from the table, both recorded in the module docstrings:

* F.5 — **`qg3D_quadForm_nonneg` is NOT proved and is not provable as stated.**  The
  physical coefficients `qgKappa` have opposite signs (`qgKappa_indefinite`: `+1/16` for
  the kinetic block, `−1/24` for the conformal block), so the quadratic form of
  `qg3DHamiltonian` is a genuinely *indefinite* signed sum of squares
  (`qg3D_quadForm`) and the operator is not semibounded.  What is proved is symmetry on
  the core (`qg3D_symmetricOn`) plus nonnegativity, the Friedrichs extension and the
  Hashimoto selection for the **elliptic truncation** `qg3DEllipticHamiltonian`
  (`qg3DElliptic_quadForm_nonneg`, `qg3DElliptic_friedrichs_extension`,
  `qg3DElliptic_hashimoto_selects`), which is F.8 on the operator to which it applies.
* F.6 — the charge is built on the algebraic graded core `ℂ[x₀,…,x₈₃] ⊗ Λ(ℂ¹⁹)` rather
  than on the completed `L²(ℝ⁸⁴ × ℤ₂¹⁹)`, and nilpotency is proved *given* that the
  constraint family closes with real structure constants obeying Jacobi.  A concrete
  non-abelian family (`affMat`, the affine algebra `[H, E] = E`) is exhibited so the
  theorem is not vacuous.

**Verification expectation:** F.1–F.8 are `sorry`-free and `axiom`-free;
`#print axioms` shows only `propext`, `Classical.choice`, `Quot.sound`.  The
Weyl ordering (F.4) and sign (F.4) are **settled in the module, not assumed**,
exactly as in the YM `ChapterYangMillsHermite.lean`.  If any item blocks the
build, stop and record it here rather than weakening the theorem.  Do **not**
claim the mass gap or global existence.

## Honest boundary (updated 2026-08-19; unchanged at its core from `CONSOLIDATED_PLAN.md` §10.3)

* **Not claimed:** essential self-adjointness of the continuum gravity operator on
  `L²(ℝ⁸⁴ × ℤ₂¹⁹)`, global existence, or any unitary-evolution result for it.
  (Parts E–F give the second-quantized operator and the concrete 3D gauge-fixed
  operator **on the Hermite/Fock core**, and their Friedrichs/Hashimoto
  selection, when executed; they do **not** touch the continuum `L²(ℝ⁸⁴×ℤ₂¹⁹)`
  ESA, which remains a named-hypothesis/out-of-scope boundary as in Parts A–D.)
* The continuum conclusion needs the ESA of `H₀ + H₁ − Ṽ` for the full
  polynomial potential `Ṽ`.  What is **already proved** (2026-08-19): the flat
  d'Alembertian `□ + κ` (`wave_essentiallySelfAdjoint`); `□ + W` for `W`
  bounded and truncated (`wave_add_boundedPotentialOp_essentiallySelfAdjoint`,
  `wave_add_truncatedPotential_essentiallySelfAdjoint`); and the **bounded-below
  polynomial potential** `W x = ‖x‖^(2k)` as a pure potential
  (`polynomialPotential_essentiallySelfAdjoint`).  What is *not* a formal limit:
  the **sign-sensitive `□ + W`** for the untruncated `W` — under this project's
  sign convention (`□ = −∂_t² + Δ_x`) a bounded-*below* `W` drives the fibre
  `−Δ_x − W` into the limit-circle regime where ESA **fails** (`−d²/dx² − x⁴`
  has deficiency `(2,2)`); the localization argument closes only under the
  opposite sign (module docstring of `ChapterWaveUnboundedPotential.lean`).
  Whether the QG `Ṽ` lies in the proved or the failing regime is the analytic
  core that decides the boundary (cf. step (c) of `CONSOLIDATED_PLAN.md` §9.5);
  the sign question is analyzed in detail in Part D.6, where it is established
  that the sign is structural (not removable by convention or initial
  conditions) and that the genuine open task is tracking the sign of `Ṽ` through
  the densitizing/half-density unitary.  The QG
  module's `strichartz_esa_of_finiteSpeed` still states the deduction with the
  deficiency-triviality hypothesis explicit; it is satisfiable in the mode case
  (`strichartz_finiteSpeed_satisfiable`) and the flat-part conclusion is
  discharged by the proved wave theorem.
* The **gauge/BRST sector** is not covered by the transfer argument alone: a full
  BRST-reduced transfer needs the unitary to preserve the physical subspace, which
  the `1/e`-absorption gives for the kinetic/conformal part but which must be
  checked for `H₁ − Ṽ` under the full constraint structure.  Part F.6 states the
  BRST charge and its nilpotency as a construction on the Fock core; the
  *physical-subspace reduction* of the full continuum operator remains a
  recorded boundary.
* The raw point map `e ↦ (y, ẽ)` is not by itself a Hilbert-space unitary; the
  Jacobian half-density factor `|J|^{−1/2}` is what makes D.4 applicable.  The
  transfer theorem takes that unitary as data.
