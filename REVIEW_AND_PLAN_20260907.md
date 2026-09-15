# Full review and plan — QYM, NS, QG, the gauge-fixed Hamiltonians, the outer Fock layer,
# and the SIRK–Hashimoto bands (2026-09-07)

*This note is a complete re-read of the formal development against the item list of the
current request:*

> *the full formalization of QYM (including mass gap and the abelian/QED version), NS
> (Eulerian and Lagrangian variables), QG (`R²`-action based, full exponential potential
> without Taylor expansion, vielbein variables), all 3D gauge-fixed Hamiltonians including
> all interaction couplings, ghosts and gauge fixing (including for the variables
> representing spatial derivatives of the fields), the outer-Fock-space version of the full
> Hamiltonians using the Faris–Lavine `N` and the Friedrichs extension of `N`, and rigorous
> approximation bands from the SIRK–Hashimoto algorithm.*

Part I is the audit: for every item, the declarations that carry it, and whether the
statement is unconditional, conditional (on what), or absent.  Part II is the gap list with
a feasibility judgement for each gap.  Part III is the plan actually executed in this wave,
with acceptance criteria.  Part IV records what is deliberately **not** attempted and why —
the honesty boundary of the whole development.

Every declaration named in Part I exists in `BookProof/` and is part of the `BookProof`
library target, which builds `sorry`-free; `Work/*Audit.lean` re-check axiom bases
(`propext`, `Classical.choice`, `Quot.sound` only).

---

## Part I — Audit

### 1. Quantum Yang–Mills, 3D, gauge-fixed

| item | status | declarations |
| :-- | :-- | :-- |
| one-particle Hamiltonian `H₁ = ½Σπ² + ½ΣB²` on the Gauss–polynomial core of `L²(ℝ⁹⁹)`, with the **full cubic** magnetic polynomial `B_{ia} = ε_{ijk}(∂_jA_{k,a} + f_{abc}A_{j,b}A_{k,c})` and the 72 derivative coordinates `∂_jA_{k,a}` carried as independent coordinates | **proved, unconditional** | `YangMillsHermite.ymHamiltonian`, `magPoly`, `ymHamiltonian_symmetricOn`, `ymHamiltonian_quadForm`, `ymHamiltonian_quadForm_nonneg` |
| closability of the form; Friedrichs extension; Hashimoto/SIRK selection | **proved, unconditional** | `YangMillsFriedrichs.weylOpDom_quadForm_nonneg`, `form_closable`, `weylForm_closable`, `ym_hermite_friedrichs_extension`, `ym_hermite_hashimoto_selects` |
| uniqueness of the self-adjoint realization for `f_abc = 0` (abelian) | **proved** | `ymAbelian_essentiallySelfAdjointOn_core`, `ymAbelian_positiveExtension_eq_closure`, `ymAbelian_hashimoto_selects`, `ymAbelian_stone_flow` |
| uniqueness of the realization for `f_abc ≠ 0` (quartic `B²`) | **open** | — (see G1) |
| Fock lift `dΓ(H₁)`: positive self-adjoint extension, vacuum, shift-invert selection | **proved, unconditional** | `ym_fock_friedrichs_extension`, `ym_fock_vacuum_annihilated`, `ym_fock_hashimoto_selects` |
| Fock lift: essential self-adjointness on the finite-occupation core | **proved for `f_abc = 0`**, open otherwise | `dGamma_ymAbelian_essentiallySelfAdjointOn_core`, `ymAbelianFock_timeIndependent_singleTime`, `ymAbelianFock_positiveExtension_eq_closure` |
| single-time / time-translation package for general `f_abc` | **conditional** on ESA of `dΓ(H₁)` | `ymFock_weylGauge_timeIndependent` (unconditional), `ymFock_timeIndependent_singleTime_of_esa` |
| mass gap chain: one-particle form gap ⇒ Fock gap; truncated gap ⇒ infinite gap; Gershgorin+Schur ⇒ form gap; certificate reader | **proved as implications** | `ChapterYangMillsFockGapChain`, `ChapterTruncationGapLift`, `ym_fock_mass_gap_of_truncated_gap_and_matrix_bounds`, `ym_fock_gap_of_matrix_certificate` |
| a mass gap for the physical `qcd_ym_hamiltonian(g)` | **not claimed**; needs certified matrix data + the continuum leg | — |
| the abelian instance of the gap chain is **vacuous** (no one-particle form gap) | **proved** | `ym_abelian_no_one_particle_form_gap`, `exists_core_state_small_energy` |
| QED: free-photon second quantization, positivity, and the proof that no positive gap exists in the infrared-accumulating case; regulated/Proca substitutes | **proved** | `photon_fock_positivity`, `photon_no_one_particle_gap`, `irPhoton_fock_mass_gap`, `proca_fock_mass_gap` |
| explicit Hermite matrix-element data (sparsity + entry bounds) of the **non-abelian** `H₁` | **missing before this wave** | see G2 / W2 |
| Faddeev–Popov ghost sector of the gauge-fixed Yang–Mills Hamiltonian | **missing before this wave** (the BRST/ghost algebra exists in `ChapterGhostField`, `ChapterGaugeFixing`, `ChapterBRSTNilpotent`, but no Yang–Mills ghost Hamiltonian) | see G3 / W3 |

### 2. Navier–Stokes

| item | status | declarations |
| :-- | :-- | :-- |
| index of all realizations | proved | `ChapterNavierStokesEsaConsolidation` |
| Eulerian, untruncated: symmetry | unconditional | `NSFullData.hamiltonian_isSymmetricDom` |
| Eulerian: ESA | **conditional** on a complete unitary flow / total eigenvector family, with a **sharp negative** ruling out a purely structural proof | `exists_nsFullData_not_hasZeroDeficiencyOn` |
| Lagrangian: drift Kato–Rellich-small; Fock-of-Fock transformed Hamiltonian ESA | unconditional | `ChapterNavierStokesLagrangianKatoRellich`, `lagrangianFock_hasZeroDeficiencyOn` |
| momentum / differential realizations; Ikebe–Kato comparison; two Faris–Lavine inequalities; Hashimoto selection | unconditional | `ikebeKato_momentum`, `ns_hamiltonian_essentiallySelfAdjointOn_core`, `nsDiffH_hashimoto_selects` |
| outer Fock (parcels) with interactions, uniform particle-number-independent Schur bounds | unconditional | `ChapterNsOuterFockFarisLavine`, `nsOuterFock_timeIndependent_singleTime` |
| global regularity of the classical PDE | deliberate scope cut (Contention D5) | — |

### 3. Quantum gravity (`R²`/Starobinsky, vielbein, full exponential potential)

| item | status | declarations |
| :-- | :-- | :-- |
| `R²` action in scalar–tensor form; **full exponential** potential, no Taylor truncation | proved | `fR_eq_scalarTensor`, `starobinskyV_nonneg`, `starobinskyV_tendsto_plateau`, `starobinskyV_tendsto_atBot_atTop`, `confV_completed_square`, `confV_ge` |
| vielbein variables; the 84-component jet (derivative) coordinates; densitized half-density unitary | proved | `ChapterQgVielbeinModeInstance`, `ChapterQgDerivativeRealization` (`jetDeriv`, `exists_not_fixed`), `ChapterQuantumGravityHalfDensity`, `ChapterQgMultiHalfDensity` |
| gauge fixing and ghosts, including on the derivative coordinates | proved | `ChapterGaugeFixing`, `ChapterGhostField`, `ChapterBRSTNilpotent`, `ChapterQuantumGravityBrstCharge`, `brstGaugeFixed_esa`, `starobinsky_brstGaugeFixed_esa`, `gaugeFixedSubset_esa`, `ChapterBrstReducedTransfer`, `ChapterBrstTruncationLeakage` |
| one-particle ESA on the Gauss core (hyperbolic signature) | unconditional | `qg3D_essentiallySelfAdjointOn_core`, `qgSigned_essentiallySelfAdjointOn_core`, `qg3D_stone_flow` |
| outer-Fock ESA; Faris–Lavine for the physical signature; interacting torsion couplings; elliptic self-Friedrichs variant | unconditional | `qgOuterFock_esa`, `qgOuterFock_esa_farisLavine_full`, `qgInteracting_esa_farisLavine`, `qgOuterEllipticFock_esa_farisLavine` |
| dynamics (single-time packages) | unconditional | `qgOuterFock_timeIndependent_singleTime`, `starobinsky_brstGaugeFixed_timeIndependent_singleTime`, `starobinsky_qgManifold_timeIndependent_singleTime` |
| spectral side: Courant–Fischer ladder of an unbounded non-negative relation through its resolvent, equality at every rung, gap transfer | proved | `ChapterResolventMinMaxLadder`, `ChapterResolventMinMaxEquality` |
| QG-2 Case A composed into a genuinely multi-dimensional `−Δ + V`; QG-3.2(b); spectral half of QG-3.4 | open | — (see G5) |

### 4. Outer Fock space, the Faris–Lavine `N`, and the Friedrichs extension of `N`

The abstract criterion is the real theorem of Faris–Lavine (`ChapterFarisLavineCore`,
`essentiallySelfAdjointOn_of_farisLavine`, `essentiallySelfAdjointOn_core_of_farisLavine`):
`N ≥ 0` with `N + 1` surjective, `± i[H,N] ≤ cN` ⇒ `H` essentially self-adjoint; the caveat
`not_farisLavine_criterion_of_relative_bound` records that the unrestricted form is false.
The outer-Fock chapters (`ChapterQgOuterFockEsa`, `ChapterQgOuterFockCoreFL`,
`ChapterQgOuterFockFullFL`, `ChapterQgOuterFockInteractionFL`, `ChapterQgOuterFockEllipticFL`,
`ChapterScalaronOuterFockFL`, `ChapterNsOuterFockFarisLavine`) instantiate it uniformly: a
number-type comparison operator `N` — in the elliptic case its own Friedrichs extension,
`dsFriedComparison` — the relative bound `‖Hu‖ ≤ K‖Nu‖` and the commutator bound
`|⟪Hu,Nu⟫ − ⟪Nu,Hu⟫| ≤ B⟪u,Nu⟫`, hence ESA on the core, a unique realization and a Stone
flow.  On the second-quantized side the comparison operator may be the weighted number
operator `dΓ(diag w²)` (`ChapterFockWeightedSchurEsa`) with weights read off a grading of
the one-particle basis (`ChapterGradedBandSchurEsa`).

### 5. The numerical layer: SIRK–Hashimoto bands

`ChapterSirkSingleTimeShift`, `ChapterSirkTrotterKato`, `ChapterFiniteSectionSingleTime`
(one shift, one finite time, Galerkin convergence at every nonzero shift, per-system
instances for QG, NS and QYM); `ChapterSirkBandLedger`, `ChapterSirkCertifiedGap`,
`ChapterSirkGapTable`, `ChapterBandEnclosure`, `ChapterSirkFinitePrecision`,
`ChapterSirkRitzMinMax`, `ChapterSirkRitzPerturbation`, `GapCertificate.lean` (rigorous
enclosures over exact decimals; Ritz levels are used only in the certified direction).

---

## Part II — Gap list

**G1 (QYM, `g ≠ 0`): essential self-adjointness of the quartic one-particle operator.**
`H₁ = −Δ + V` with `V = ½ΣB²` a non-negative *quartic* polynomial.  Mathematically this is
Kato's theorem (`V ≥ 0`, `V ∈ L²_loc` ⇒ ESA on `C_c^∞`), whose proof needs Kato's
distributional inequality and elliptic regularity — neither is available in Mathlib, and
building them is a project of its own.  Three instruments in the development were tested
against it and all three provably stop at quadratic symbols:

* the Carleman-flux criterion behind `fqOp_essentiallySelfAdjoint` needs shell growth `O(n)`;
* the weighted Schur gate needs `|A_{kj}|·|w_j²−w_k²|/(w_kw_j)` bounded, which for a band
  operator of order `m` and *any* weight that is a function of the degree forces `m ≤ 2`;
* Faris–Lavine with a comparison operator diagonal in the degree fails for the same reason:
  entries of order `deg^{m/2}` against `|n_j − n_k| ∼ p·deg^{p−1}` and a budget `deg^p`
  require `m ≤ 2`.

So G1 is **not attempted** here; what *is* attainable is the structural data of the quartic
matrix (G2).

**G2 (QYM): the Hermite matrix data of the non-abelian `H₁`.**  The certificate seam
(`ChapterYangMillsCertificateSeam`, `ChapterSchurGershgorinGap`) consumes matrix elements
`a_{ij} = ⟪b_i, H b_j⟫`; nothing in the development says which of them can be non-zero, or
how large they are, for the *physical* `f_abc ≠ 0` Hamiltonian.  Feasible: the graded band
calculus generalises from quadratic to arbitrary degree.

**G3 (QYM): the Faddeev–Popov ghost sector.**  The BRST algebra, the ghost CAR pair, ghost
number and the gauge-fixing fermion exist, and the QG thread carries BRST-gauge-fixed
Hamiltonians, but there is no Yang–Mills Hamiltonian *with* its ghost sector.  Feasible in
the finite-ghost-mode model.

**G4 (QYM/QED): no single place indexes the abelian/QED thread.**  Its statements are spread
over five chapters.  Feasible: a consolidation chapter, in the style of
`ChapterNavierStokesEsaConsolidation`.

**G5 (QG): QG-2 Case A in the genuinely multi-dimensional setting, QG-3.2(b), the spectral
half of QG-3.4.**  Case A needs multi-dimensional elliptic regularity that the fibre route
does not supply — same obstruction family as G1.  Not attempted.

**G6 (all threads): the continuum leg** (norm-resolvent convergence `H_m → H`) and the
**unbounded Friedrichs-selection conjecture** (Part D.4).  Recorded, not attempted.

---

## Part III — The plan of this wave (**executed; `lake build BookProof` completes**)

*Execution record.*  All four items below are done: the four new modules are imported from
`BookProof.lean`, `lake build BookProof Work.YangMillsBandGhostAudit` completes, none of the
new files contains `sorry`, and every audited result reports only `propext`,
`Classical.choice`, `Quot.sound`.  The audit script is
`Work/YangMillsBandGhostAudit.lean`.  Nothing in Part IV changed: G1, G5 and G6 stay open,
and no mass gap is claimed anywhere.

**W1 — `BookProof/ChapterHermiteBandCalculusHigher.lean`: the band calculus of arbitrary
order.**  Generalise `Band`/`IsBand2` from the two fixed growths `√(n+1)`, `n+1` to the
family `gpow m n = √(n+1)^m`, and prove the general composition law

`Band T r₁ M₁ C₁ (gpow m₁) → Band U r₂ M₂ C₂ (gpow m₂) →
   Band (U ∘ T) (r₁+r₂) (M₁M₂) (M₁C₁C₂·√(r₁+1)^{m₂}) (gpow (m₁+m₂))`,

with the closure properties (`add`, `smul`, `sum`, monotonicity in `m`, in `r`, in `M`, `C`)
and the base cases `x_i`, `π_i`, and multiplication by an arbitrary polynomial.
*Acceptance*: `IsBandDeg m` closed under the algebra; `isBandDeg_mulOp` for every
polynomial; the old `IsBand1`/`IsBand2` recovered as `IsBandDeg 1`/`IsBandDeg 2`.

**W2 — `BookProof/ChapterYangMillsBandBounds.lean`: the Hermite matrix of the full
non-abelian gauge-fixed Yang–Mills Hamiltonian.**  Define the polynomial-level `ymPoly fabc`
(the general-`f_abc` analogue of `ymAbelianPoly`), identify it with `ymHamiltonian` on the
Hermite core, prove `IsBandDeg 4 (ymPoly fabc)` and deduce the explicit matrix statement:
there are `M` and `C` with

* every column of the Hermite matrix has at most `M` non-zero entries;
* an entry `⟪ψ_β, H ψ_α⟫` vanishes unless `|deg β − deg α| ≤ 4`;
* `|⟪ψ_β, H ψ_α⟫| ≤ C (deg α + 1)²`.

*Acceptance*: the three bullets as one theorem about `hermCol e (ymPoly fabc)`, for every
real structure-constant family, plus the transport identity to `ymHamiltonian`.  This is the
certificate-data infrastructure of G2: it makes the emission of a *complete* certificate
over a degree window a finite computation.

**W3 — `BookProof/ChapterYangMillsGhostSector.lean`: the ghost sector.**  The
Faddeev–Popov ghost sector of the 3D gauge-fixed Yang–Mills Hamiltonian in the
finite-ghost-mode model: total space `Fin n → L²(ℝ⁹⁹)` (the gauge sector tensored with the
finite-dimensional ghost Fock space), `H_tot = H₁ ⊗ 1 + 1 ⊗ H_gh`, ghost-number
conservation, and — in the abelian case, where `H_gh` is field-independent and bounded —
essential self-adjointness of the total Hamiltonian, its unique realization and its flow.
*Acceptance*: symmetry unconditional; ESA of the total abelian Hamiltonian; `[H_tot,N_gh]=0`.

**W4 — `BookProof/ChapterQedAbelianConsolidation.lean`: the abelian/QED index.**  One
chapter that states, with proofs by re-export, the abelian/QED statements of record:
one-particle ESA, Friedrichs = closure, Fock ESA, the unconditional single-time package, the
absence of a one-particle form gap, the photon positivity/no-gap pair, and the new ghost
statement.  *Acceptance*: builds, no new hypotheses, every entry pointing at the theorem
that carries it.

All four are imported from `BookProof.lean`, audited by a new `Work/*Audit.lean`
`#print axioms` script, and must build `sorry`-free and `axiom`-free.

### What was delivered, declaration by declaration

* `BookProof/ChapterHermiteBandCalculusHigher.lean` — `gpow`, `gpow_mono`, `gpow_add`,
  `Band.monoR`, `Band.monoG`, **`Band.compGen`**, `IsBandR` / `IsBandDeg` with `add`, `smul`,
  `sum`, `monoR`, `le` and **`IsBandR.comp`** (radii and orders add), the base cases
  `isBandR1_mulXPoly`, `isBandR1_momPoly`, `isBandR1_crePoly`, `isBandR1_annPoly`,
  `isBandR_one_op`, the multiplication algebra `mulOp_mul`, `mulOp_add'`, `mulOp_smul`,
  `mulOp_sum`, and **`isBandDeg_mulOp_multiset`**, **`isBandDeg_mulOp_monomial`**,
  **`isBandDeg_mulOp`** (an arbitrary polynomial multiplier is a band operator of its total
  degree).
* `BookProof/ChapterYangMillsBandBounds.lean` — `ymPoly`, `ymHermOp`, **`ymHermOp_eq`**,
  `ymHamiltonian_hermCore_eq'`, `ymHermCol`, `isHermCol_ymHermCol`, `isBandR2_magMulOp`,
  **`isBandR4_ymPoly`**, `gradedBand_of_isBandR` and the headline
  **`ym_hermCol_band_bounds`**.
* `BookProof/ChapterYangMillsGhostSector.lean` — `GConf`, `ghostNum`, `ghostEnergy`,
  `GhostSpace`, `ghostCore`, `ghostCore_dense`, `fibreHam`, **`ymGhostHam`**,
  `fibreHam_symmetricOn`, **`ymGhostHam_symmetricOn`**,
  **`ymGhostHam_preserves_ghostNumber`**, **`ymGhostHam_vacuum_fibre`**,
  `fibreHam_abelian_esa`, **`ymGhostHam_essentiallySelfAdjointOn_core`**,
  `ymGhostHam_stone_flow`, **`ymGhostHam_add_bounded_coupling_esa`**.
* `BookProof/ChapterQedAbelianConsolidation.lean` — `qed_one_particle_esa`,
  `qed_one_particle_stone_flow`, `qed_fock_esa`, `qed_fock_friedrichs_extension`,
  `qed_fock_exists_selfAdjoint_realization`, `qed_fock_time_translation`,
  `qed_no_one_particle_form_gap`, `qed_photon_no_one_particle_gap`, `qed_ghost_symmetric`,
  `qed_ghost_esa`, `qed_ghost_vacuum_decouples`.

---

## Part IV — Deliberately not attempted (the honesty boundary)

* **A mass gap for Yang–Mills.**  The chain is a chain of implications; the certified
  matrix data and the continuum leg are not supplied, and nothing in the development claims
  a gap for the physical Hamiltonian.  `ym_abelian_no_one_particle_form_gap` shows the
  abelian instance is vacuous, so any gap must use the structure constants.
* **G1** (quartic one-particle ESA) and **G5** (multi-dimensional QG-2 Case A): both need
  elliptic-regularity/Kato-inequality machinery absent from Mathlib.
* **G6**: the continuum limit and the unbounded Friedrichs-selection conjecture.
* **Global regularity of classical Navier–Stokes**: a scope cut, not a gap.
