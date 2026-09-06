# Review of the four threads — QYM, NS, QG, and the numerical (SIRK–Hashimoto) layer

*Written at the start of the 2026-09-06 execution wave, as a full re-read of what the
formal development already establishes, ahead of continuing `CONSOLIDATED_PLAN.md`.  Every
declaration named below exists in `BookProof/` and is part of the `BookProof` library
target, which builds `sorry`-free; the audit scripts in `Work/*Audit.lean` re-check the
axiom bases (`propext`, `Classical.choice`, `Quot.sound` only).  Where a statement is
**conditional**, the hypothesis is named.*

---

## 1. Quantum Yang–Mills (3D, gauge-fixed)

**The one-particle Hamiltonian, with all interaction terms.**
`BookProof.YangMillsHermite.ymHamiltonian Φ fabc` is `H₁ = ½Σ_m π_m² + ½Σ_m B_m²` on the
Gauss–polynomial core of `L²(ℝ⁹⁹)`, with `B_{ia} = ε_{ijk}(∂_jA_{k,a} + f_{abc}A_{j,b}A_{k,c})`
— the full cubic magnetic polynomial `magPoly`, so `B²` is quartic in the coordinates, and
the `72 = 3·3·8` coordinates `∂_jA_{k,a}` are carried as independent coordinates of the
configuration space (this is the gauge-fixing of the derivative variables at the
one-particle level).  Proved unconditionally: symmetry (`ymHamiltonian_symmetricOn`), the
sum-of-squares quadratic form (`ymHamiltonian_quadForm`), non-negativity
(`ymHamiltonian_quadForm_nonneg`), closability of the form and the Friedrichs construction
(`BookProof.YangMillsFriedrichs`: `weylOpDom_quadForm_nonneg`, `form_closable`,
`weylForm_closable`).

**Uniqueness of the realization.**  For `f_{abc} = 0` the Hamiltonian is a genuine real
quadratic Hamiltonian and is essentially self-adjoint on the core
(`ymAbelian_essentiallySelfAdjointOn_core`, `ChapterYangMillsAbelianEsa`), so the Friedrichs
extension *is* the closure (`ymAbelian_positiveExtension_eq_closure`), the Hashimoto/SIRK
shift-invert algorithm selects it (`ymAbelian_hashimoto_selects`), and it generates a
complete unitary group (`ymAbelian_stone_flow`).  For `g ≠ 0` the quartic `B²` is **open**.

**The Fock (second-quantized) layer.**  `ym_fock_friedrichs_extension`
(`ChapterFockSecondQuantization`) gives the positive self-adjoint extension of `dΓ(H₁)`
unconditionally, `ym_fock_vacuum_annihilated` the vacuum, and
`ym_fock_hashimoto_selects` the shift-invert selection.  The time-independence package is
`ymFock_weylGauge_timeIndependent` (unconditional) and
`ymFock_timeIndependent_singleTime_of_esa` (conditional on essential self-adjointness of
`dΓ(H₁)` on the finite-occupation core) in `ChapterQymTimeIndependentFlow`.

*New in this wave*: that hypothesis is discharged in the abelian case —
`BookProof.YmAbelianFock.dGamma_ymAbelian_essentiallySelfAdjointOn_core` and the
unconditional `ymAbelianFock_timeIndependent_singleTime`
(`ChapterYangMillsAbelianFockEsa`), via the new graded band calculus (§5).

**The gap chain.**  `ChapterYangMillsFockGapChain` lifts a one-particle form gap to the Fock
gap; `ChapterTruncationGapLift` lifts a certified truncated gap to the infinite operator;
`ChapterSchurGershgorinGap` reduces the one-particle gap to Gershgorin-tail + Schur-coupling
inequalities on the matrix elements (`ym_fock_mass_gap_of_truncated_gap_and_matrix_bounds`);
`ChapterYangMillsCertificateSeam` consumes an emitted certificate record
(`ym_fock_gap_of_matrix_certificate`, `ym_fock_mass_gap_of_matrix_certificate`, with a
parsed NDJSON example).  **No mass gap is claimed**: the chain is conditional on certified
matrix-element bounds for the concrete `qcd_ym_hamiltonian(g)` and on the continuum leg
(norm-resolvent convergence `H_m → H`), which remains a recorded analysis gap.

## 2. Navier–Stokes

Both variable sets are formalized, and the ESA statements of record are indexed in one
place by `ChapterNavierStokesEsaConsolidation`.

* **Eulerian, untruncated**: symmetric unconditionally
  (`NSFullData.hamiltonian_isSymmetricDom`); ESA *conditional* on a complete unitary flow or
  a total family of eigenvectors; and a **sharp negative**,
  `exists_nsFullData_not_hasZeroDeficiencyOn` (`ChapterNavierStokesFullEsa`), which rules out
  any purely structural proof of ESA in this realization.
* **Lagrangian**: the drift is Kato–Rellich-small against the positive second-order part
  (`ChapterNavierStokesLagrangianKatoRellich`), and the Fock-of-Fock transformed Hamiltonian
  is essentially self-adjoint **unconditionally** (`lagrangianFock_hasZeroDeficiencyOn`,
  `ChapterNavierStokesFockEsa`).
* **Momentum / differential realizations**: the Ikebe–Kato comparison operator is proved
  (`ikebeKato_momentum`) and the two Faris–Lavine inequalities give
  `ns_hamiltonian_essentiallySelfAdjointOn_core`; the differential realization carries both
  inequalities and the Hashimoto selection (`nsDiffH_hashimoto_selects`).
* **Outer Fock (parcels), with interactions**: `ChapterNsOuterFockFarisLavine` runs
  Faris–Lavine on the interacting parcel Hamiltonian — advection plus the derivative-gauge,
  Laplacian-gauge and `y`-gauge forms — with uniform, particle-number-independent Schur
  bounds; `nsOuterFock_timeIndependent_singleTime` (`ChapterNsOuterFockSingleTime`) is the
  single-time package there.
* Global regularity of the classical PDE is a deliberate scope cut (Contention D5), not a
  gap in the formalization.

## 3. Quantum gravity (R² action, vielbein variables, full exponential potential)

* **The action and the potential.**  `ChapterStarobinskyPotential` derives the
  scalar–tensor form of the `R²` (Starobinsky) action (`fR_eq_scalarTensor`) and works with
  the **full exponential** potential — `starobinskyV_nonneg`,
  `starobinskyV_tendsto_plateau`, `starobinskyV_tendsto_atBot_atTop`, and the completed
  square `confV_completed_square` / `confV_ge` — with no Taylor truncation.  The
  outer-Fock Faris–Lavine chapters carry the exponential wall as `WallPot`.
* **Vielbein variables and the derivative (jet) coordinates.**
  `ChapterQgVielbeinModeInstance`, `ChapterQgDerivativeRealization` (the `84`-component jet
  of the tetrad, `jetDeriv`, `idx_cases`, and the sharp `exists_not_fixed`),
  `ChapterQuantumGravityHalfDensity` / `ChapterQgMultiHalfDensity` (the densitized
  half-density unitary).
* **Gauge fixing and ghosts.**  `ChapterGaugeFixing`, `ChapterGhostField` (the CAR pair
  `psi`, `psiDag` and the ghost number operator), `ChapterBRSTNilpotent`,
  `ChapterQuantumGravityBrstCharge`, `ChapterQgBrstDerivativeGauge` (`brstGaugeFixed_esa`,
  `starobinsky_brstGaugeFixed_esa`, `gaugeFixedSubset_esa` — gauge fixing imposed on the
  coordinates *and* on the coordinates representing spatial derivatives of the fields),
  `ChapterBrstReducedTransfer`, `ChapterBrstTruncationLeakage`.
* **Self-adjointness.**  One-particle ESA on the Gauss core by the Carleman route
  (`qg3D_essentiallySelfAdjointOn_core`, `ChapterQg3DGaugeEsa`); outer-Fock ESA
  (`qgOuterFock_esa`); **unconditional** Faris–Lavine for the physical hyperbolic signature
  (`qgOuterFock_esa_farisLavine_full`); interacting nearest-neighbour torsion couplings
  (`qgInteracting_esa_farisLavine`); the elliptic-signature self-Friedrichs variant
  (`qgOuterEllipticFock_esa_farisLavine`).
* **Dynamics.**  `qgOuterFock_timeIndependent_singleTime`,
  `starobinsky_brstGaugeFixed_timeIndependent_singleTime`,
  `starobinsky_qgManifold_timeIndependent_singleTime` (`ChapterQgTimeIndependentFlow`).
* **Spectral side.**  `ChapterResolventMinMaxLadder` / `ChapterResolventMinMaxEquality` give
  the Courant–Fischer ladder of an unbounded non-negative self-adjoint relation through its
  resolvent, with equality at every rung and gap transfer.
* **Recorded open items** (unchanged): QG-2 Case A composed into a genuinely
  multi-dimensional `−Δ + V`; QG-3.2(b); the non-derived half of QG-3.4.

## 4. Outer Fock space, Faris–Lavine `N`, and Friedrichs

The outer-Fock construction (`ChapterQgOuterFockEsa`, `ChapterQgOuterFockCoreFL`,
`ChapterQgOuterFockFullFL`, `ChapterQgOuterFockInteractionFL`,
`ChapterQgOuterFockEllipticFL`, `ChapterScalaronOuterFockFL`,
`ChapterNsOuterFockFarisLavine`) is uniform across the sectors: a comparison operator `N`
(the Faris–Lavine number-type operator, in the elliptic case its own Friedrichs extension
via `dsFriedComparison`), the relative bound `‖Hu‖ ≤ K‖Nu‖` and the commutator bound
`|⟪Hu, Nu⟫ − ⟪Nu, Hu⟫| ≤ B⟪u, Nu⟫`, giving essential self-adjointness on the core, hence a
unique self-adjoint realization and a Stone flow.  On the second-quantized side the
comparison operator may now also be the **weighted number operator** `dΓ(diag w²)`
(`ChapterFockWeightedSchurEsa`), and — new in this wave — the weights may be read off a
grading of the one-particle basis (`ChapterGradedBandSchurEsa`).

## 5. The numerical layer: SIRK–Hashimoto bands

* **One shift, one finite time**: `ChapterSirkSingleTimeShift`, `ChapterSirkTrotterKato`,
  `ChapterFiniteSectionSingleTime` — the propagator is evaluated at a single finite time
  through a bounded shift-invert resolvent, with Galerkin/finite-section convergence at
  every nonzero shift; per-system instances exist for QG, NS (fibre and outer Fock) and QYM.
* **Rigorous bands**: `ChapterSirkBandLedger` (nested-compatible enclosures, well-formed
  ledgers over exact decimals), `ChapterSirkCertifiedGap`, `ChapterSirkGapTable`
  (`certified_gap_table`, `certified_gap_table_interval`), `ChapterBandEnclosure`,
  `ChapterSirkFinitePrecision`, `ChapterSirkRitzMinMax` / `ChapterSirkRitzPerturbation`
  (Ritz levels are lower bounds; Galerkin levels converge), and the root
  `GapCertificate.lean`.  A computed Ritz value is never read as a lower bound for the exact
  operator: only the certified direction is used.

## 6. What this wave adds, and what stays open

*Added* (see `ChapterHermiteBandCalculus`, `ChapterGradedBandSchurEsa`,
`ChapterQuadraticFockEsa`, `ChapterYangMillsAbelianFockEsa`): the second quantization of an
**unbounded** one-particle operator — any real quadratic Hamiltonian on `L²(ℝᵈ)` — is
essentially self-adjoint on the finite-occupation core, and the abelian gauge-fixed
Yang–Mills Hamiltonian is an instance, which makes the Yang–Mills single-time package
unconditional there.

*Still open, unchanged*: the quartic (`g ≠ 0`) one-particle Yang–Mills operator; the
certificate data for a concrete mass gap; the continuum leg; the unbounded
Friedrichs-selection conjecture (Part D.4); and the QG items listed in §3.
