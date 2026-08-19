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
`multiplierOp_essentiallySelfAdjoint`, incl. polyharmonic).  The QG part D.1
row below therefore no longer describes an *unproved* continuum hypothesis for
the flat principal part: it is discharged by the proved wave theorem.  What
remains is the **polynomial-potential perturbation step** — ESA of
`H₀ + H₁ − Ṽ` for the full `Ṽ` (the `R → ∞` limit of the truncated
`wave_add_truncatedPotential` result), recorded as the boundary below.

| Item | Lean name | Status |
| :-- | :-- | :--: |
| D.1 the deduction step: finite-speed / unique continuation ⟹ ESA | `strichartz_esa_of_finiteSpeed` | PROVED (hypothesis named) |
| D.1a the flat d'Alembertian `□ + κ` is essentially self-adjoint — the Strichartz theorem itself, **proved** | `BookProof.StrichartzWave.wave_essentiallySelfAdjoint`, `constCoeffOp_essentiallySelfAdjoint` | PROVED |
| D.1b ESA of `□ + W` for `W` bounded / truncated — the potential-perturbation steps (a)+(b) | `wave_add_boundedPotentialOp_essentiallySelfAdjoint`, `wave_add_truncatedPotential_essentiallySelfAdjoint` | PROVED |
| D.2 the hypothesis is satisfiable (Part C satisfies it) | `strichartz_finiteSpeed_satisfiable` | PROVED |
| D.3 the alternative route through the proved Faris–Lavine criterion | `qg_esa_of_farisLavine` | PROVED (hypotheses named) |
| D.4 transfer along the half-density unitary: ESA of the flat operator ⟹ ESA of the physical one | `densitized_hasZeroDeficiencyOn_transfer` | PROVED |
| D.5 the half-density unitary itself, **constructed** rather than assumed | `measurePreserving_qgSquare`, `measurePreserving_qgSqrt`, `halfDensityUnitary`, `qg_halfDensity_transfer` | PROVED |

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
`ns_esa_of_farisLavine` is in the Navier–Stokes plan).  The remaining continuum
gap is the full-potential step, recorded in the honest boundary below.

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

| Item | Suggested Lean name | Status |
| :-- | :-- | :--: |
| E.1 the configuration space `Conf = ℕ →₀ ℕ` over the `84`-mode (one-particle) basis, and its finite-occupation domain `ℓ²(Conf)` | `qgConf`, `qgFockAlg`, `lpFiniteModes qgConf` (reuse `FockSecondQuantization`) | TODO |
| E.2 the bosonic ladder operators `a_j, a_j†` with `[a_j, a_j†] = 1` (reuse `ccr_annA_creA`) | `annA`, `creA`, `ccr_annA_creA` | DONE (reuse) |
| E.3 the **fermionic (CAR)** ladder operators `ψ_j, ψ_j†` with `{ψ_j, ψ_j†} = 1` and `{ψ_j, ψ_k} = 0` on the antisymmetric sector | `fermAnn`, `fermCre`, `car_fermAnn_fermCre`, `car_fermAnn_fermAnn` | TODO |
| E.4 the `ℤ₂`-grading: total fermionic number parity; bosonic ops grade 0, fermionic ops grade 1; the superalgebra `[x, y} = xy − (−1)^{|x||y|}yx` | `totalFermParity`, `grade`, `superBracket` | TODO |
| E.5 the second quantization `dΓ(A)` of a one-particle operator, symmetric/positive ⇒ Friedrichs (reuse `dGamma`, `dGamma_friedrichs_extension`, `secondQuantization_friedrichs`) | `qgDGamma`, `qgSecondQuantization_friedrichs` | DONE (reuse) |
| E.6 the finite-mode-domain identification so the Hashimoto/SIRK shift-invert machinery applies to the second-quantized operator (reuse `finiteModeDomain_fockBasisN`, `dGamma_hashimoto_selects`) | `qgFock_hashimoto_selects` | DONE (reuse) |

**Verification expectation:** E.1–E.6 are `sorry`-free and `axiom`-free; the
`#print axioms` audit shows only `propext`, `Classical.choice`, `Quot.sound`.
The fermionic sector (E.3, E.4) is the genuinely new content; the bosonic side
(E.1, E.2, E.5, E.6) is a direct reuse of the YM Fock module.  Do **not** claim
the mass gap or global existence.

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
| F.1 the 3D Hamiltonian density `ℋ = (1/16e)𝒮² − (1/24e)𝒫² + (1/2)𝒮E + (1/3)𝒫Eₐᵃ − e(𝒯-terms)` (book.tex:8177, 8188) stated as a formal expression with the `e = det e_i^a` degeneracy | `qg3DHamiltonianDensity` | TODO |
| F.2 the densitized form: the `1/e`-singular kinetic part replaced by the A.3/A.4 absorption (`1/e = 4(∂y/∂e)²`), giving a polynomial-coefficient operator on the product Hermite core of `L²(ℝ⁸⁴)` — the gravity analogue of `ymHamiltonian` | `qg3DdensitizedHamiltonian`, `qg3D_apply` | TODO |
| F.3 the coordinate/momentum operators on the core with the gravity CCR `[e_μ^a, π^ν_b] = iδ^ν_μ δ^a_b` and `[e_ν^a_,μ, π^{αβ}_b] = iδ^α_μ δ^β_ν δ^a_b` (book.tex:8267–8268) | `qgMulOp`, `qgMomOp`, `qgCCR` | TODO |
| F.4 the Weyl ordering of the non-commuting `πe` cross-terms (the same subtlety as YM's `weylProd`), and the sign reconciliation with the positive sum-of-squares form | `qgWeylProd`, `qgWeylProd_polySym` | TODO |
| F.5 symmetry and positivity of the densitized Hamiltonian on the core (Friedrichs hypothesis) | `qg3D_symmetricOn`, `qg3D_quadForm_nonneg` | TODO |
| F.6 the BRST charge `G = ∫ (p e c∂e − p e ∂c + π v c∂v − π v ∂c + i∂β c^α c^β b_α)` (book.tex:8215) with ghosts on `ℤ₂¹⁹`; nilpotency `G² = 0` on the physical subspace — the gravity analogue of the Yang–Mills BRST charge | `qgBRST`, `qgBRST_nilpotent` | TODO |
| F.7 the fermionic ghost CCR/CAR `{ψ_a, ψ†_b} = δ_ab`, `{ψ_{aμ}, ψ†_{bν}} = δ_ab δ_μν` (book.tex:8269–8270) | `qgGhostCar` | TODO |
| F.8 the instantiation of the Friedrichs + Hashimoto theorems on the concrete 3D operator (reuse `friedrichs_extension_exists`, `friedrichs_hashimoto_selects`) | `qg3D_friedrichs_extension`, `qg3D_hashimoto_selects` | TODO |

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
* The continuum conclusion needs the ESA of the flat d'Alembertian **with the
  full polynomial potential** `Ṽ`.  The Strichartz theorem itself (the flat
  d'Alembertian `□ + κ`) is now **proved** (`wave_essentiallySelfAdjoint`), and
  ESA is proved for `□ + W` with `W` bounded and with `W` truncated
  (`wave_add_boundedPotentialOp_essentiallySelfAdjoint`,
  `wave_add_truncatedPotential_essentiallySelfAdjoint`).  What remains is the
  **`R → ∞` limit** — ESA of `H₀ + H₁ − Ṽ` for the full `Ṽ` — which is the
  recorded research boundary (step (c) of `CONSOLIDATED_PLAN.md` §9.5).  The QG
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
