# Self-adjointness of the three Hamiltonians on the outer Fock space — review and execution

*Started 2026‑09‑11.  Revised 2026‑09‑12 (Yang–Mills routed through the direct Friedrichs
extension, and the kinetic-plus-squares claim about the gravity Hamiltonian corrected).
Revised again 2026‑09‑12 (**the Oseen caveat on Navier–Stokes is gone**: the full nonlinear
Hamiltonian is now carried, in Eulerian **and** in Lagrangian variables).  Revised
2026‑09‑15 (**the derivative variables are eliminated by the spatial Fourier transform**,
not fixed by a BRST gauge symmetry, so the Faris–Lavine line runs on the momentum-space
one-body operator — see §0.1).  Revised 2026‑09‑17 (**the elimination applies only to the velocity
jet, not to the Lagrangian deformation gradient, whose mode-wise substitution is degenerate**, and
the Eulerian advection is skew, not a square — §0.1).*

This note reviews the state of the essential-self-adjointness (ESA) / self-adjointness proofs
of the three threads — quantum Yang–Mills, Navier–Stokes, quantum gravity — under the
requirement that the result on the **outer (nested) Fock space** be obtained only by
instruments that lift from the one-particle Hilbert space, and records what was added to
finish them.

## 0. Which instruments lift, and what each thread uses

Exactly two data lift from the one-particle Hilbert space to the `ℓ²`-direct sum
`⊕ₙ L²(ℝ^{d·n})`:

* the **Friedrichs extension** of a positive (or merely bounded below) symmetric operator —
  symmetry, positivity and surjectivity of `N + 1` are *fibrewise*
  (`BookProof.QgOuterFockFL.dsComparison`, `dsCompOp_surj`; and, in the form used for
  Yang–Mills below, `BookProof.DirectSumEsa.dsOp_symmetricOn` together with
  `BookProof.QgOuterFock.dsOp_quadForm_nonneg` and `dsCore_dense`);
* the **commutator with `N`** — the commutator form of the lift is the *sum* of the fibre
  commutator forms (`BookProof.QgOuterFockFL.dsFibOp_hasSum_commForm`), so `±i[H,N] ≤ cN`
  lifts with the *same* constant as soon as the fibre constants are uniform in the particle
  number.

A Faris–Lavine certificate consists of precisely those two data (a Friedrichs comparison
operator `N`, a relative bound `‖Hu‖ ≤ K‖(N+1)u‖` and the commutator bound), which is why the
gravity thread is routed through it.  A Carleman flux estimate and a Schur weight are
statements about the shells of a *fixed* one-particle basis; the number of shells of the
`n`-particle sector grows with `n` and the constants degrade, so neither lifts, and nothing
in the line below depends on them.

**Where the Hamiltonian is bounded below, Faris–Lavine is not needed.**  A positive sum of
squares has a Friedrichs extension outright, and that is one of the two liftable data.  This
applies to Yang–Mills (§3) and — since the exact advection enters squared — to the full
nonlinear Navier–Stokes Hamiltonians (§2).  On the outer Fock space the Faris–Lavine
criterion is then run in its `c = 0` form, with the **lifted Friedrichs extension itself** as
the comparison operator (`Comparison.esa_self`): the commutator vanishes, and the conclusion
is that the lifted realization is essentially self-adjoint on its domain.

The index of the whole line is **`BookProof/ChapterEsaFarisLavineIndex.lean`**, which also
tabulates every Carleman-route statement of the main line against a proof of the *same*
statement by a liftable instrument:

| Carleman-route statement | replacement |
| :-- | :-- |
| `QgOuterFock.sqSumOp_essentiallySelfAdjointOn` | `FarisLavineOnly.sqSumOp_esa_farisLavine` |
| `YangMillsAbelianEsa.ymAbelian_essentiallySelfAdjointOn_core` | `YmOuterFockFL.ymAbelian_esa_farisLavine` |
| `Qg3DGaugeEsa.qgSigned_essentiallySelfAdjointOn_core` | `Qg3DGaugeFL.qgSigned_esa_fl` |
| `Qg3DGaugeEsa.qg3D_essentiallySelfAdjointOn_core` | `Qg3DGaugeFL.qg3D_esa_fl` |
| `QgOuterFock.qgOuterFock_esa` | `EsaFarisLavineIndex.qg_outerHam_esa_fl`, `qg84_outerHam_esa_fl` |

## 0.1 The derivative variables are eliminated, not gauge-fixed (2026‑09‑15 revision)

> **Scope correction, 2026‑09‑17.**  The elimination covers the Eulerian jets (`u_{i,j}`, `w_i`),
> the QG derivative modes (`D_{μν}^i`) and the Lagrangian `V_{ij}` / `S_i`.  It does **not** cover
> the Lagrangian **deformation gradient** `F`: `F_{ij} ⇒ i ℓ_j ξ_i` makes `F` rank one, so the
> eliminated cofactor — and with it the whole Piola pressure coupling — vanishes and `det F`
> collapses the volume constraint to a constant (machine-checked: `B4a–B5b` of
> `DESIGN_COMPARISON_N_20260915.md` §9).  `F` stays an independent scalar mode.  See
> `CONSOLIDATED_PLAN.md` item 6.

The plan of record for the Hamiltonians reviewed here changed after this note was written.
Until 2026‑09‑14 the variables representing the spatial derivatives of the fields were handled
by an *auxiliary independent coordinate plus a gauge condition* — `u_{i,j}` for Navier–Stokes,
`D_{μν}^i` for gravity — with the constraint treated as an abelian first-class constraint
(BRST).  The plan now **eliminates** those variables instead, by the spatial Fourier
transform.  Nothing in the rest of this note is invalidated: the *instruments* of §0 are
unchanged.  What changes is the operator they are applied to.

* **The constraint is solved, not imposed.**  Transforming only the spatial argument,
  `∂_{x_j}` becomes multiplication by `i p_j`, and the constraint
  `D_j = u^{(1)}_j ∂/∂u + i p_j` is solved on physical states by the operator identity
  `u^{(1)}_j = p_j π^{−1}`, with `π = −i ∂/∂u` the field-conjugate momentum
  (`ChapterNsBrstDerivativeGauge.genU`, `genU_ccr_u`).  Local products become continuous
  momentum convolutions, `ℱ[u_j ∂_j u_i](Q) = (i/(2π)^{d/2}) ∫ q_j Û_j(Q − q) Û_i(q) dq`, and
  the one-body generator is `H_sp = H_visc + H_advect` with the advective kernel
  `k_j π^i u_j u_i`.
* **The reviewed lines read as substitutions.**  The gravity form
  `G_{μν}^i = D_{μν}^i − i k_μ e_ν^i` of §1 and the Navier–Stokes forms
  `λ(u_{i,j} + u_i − u_i^{next})` of §2 are the same device; under the new strategy the
  substitution they name is used **when defining the operator**, so `D_{μν}^i` / `u_{i,j}`
  never enter the domain.  The identities that carried the content —
  `torsion_eq_exact_of_gauge_fixed` (gravity) and the exact `u·∇u` residual
  (`nsResPoly_not_affine`, Navier–Stokes) — are unchanged; the BRST charge and the restriction
  principle (`gaugeFixedSubset_esa`, `restrict_essentiallySelfAdjointOn`) stay valid as
  consistency results and as the book's prose, but they are no longer needed for the
  definition.
* **What the Faris–Lavine route still does.**  The two liftable data of §0 — the fibrewise
  Friedrichs comparison (`dsComparison`, `dsCompOp_surj`) and the commutator with `N`
  (`dsFibOp_hasSum_commForm`) — are exactly what the new one-body operator is measured
  against: `nsFullOuterN_esa` / `lagFullOuterN_esa` and `qgFull_esa_farisLavine` /
  `qgFull_esa_core_fl` are the same theorems, run on `dΓ(H_sp)`.
* **The comparison operator, one per version — the load-bearing design.**  The criterion
  consumes exactly one positive self-adjoint `N`: `H` and `N` symmetric on a common dense
  `D = 𝒟(N)`, `N + 1` onto, and `|commForm H N x| ≤ c·quadForm N x`
  (`essentiallySelfAdjointOn_of_farisLavine`; **no smallness of a relative bound is
  required**).  The candidates are `N_E = ι(Friedrichs(H_n^red))` for the Eulerian
  momentum-space operator, the lifted Friedrichs comparison `lagFullOuterN_esa` for the
  Lagrangian model, and the unchanged `qgFull` comparison (the exponential wall inside it) for
  gravity; the criterion holds **with `c = 0`** for the two Navier–Stokes ones.
  **Corrections of 2026‑09‑17 (see `CONSOLIDATED_PLAN.md` items 1 and 6, and §5–§6 of
  `DESIGN_COMPARISON_N_20260915.md`).**  (i) The Eulerian elimination is applied inside the
  squares *of the real pressure–viscous symbol*, so the reduced Hamiltonian is
  `½Σπ² + ½ΣΦ_r² ≥ 0` with `Φ_r = q_r + ν|k|²u_r`: the advection `i (k·u) u_i` is purely
  imaginary, so multiplying by it is **skew-adjoint and its square is negative** — it is *not*
  a square (`½(u·∇u)²` above was the older reading) but the momentum convolution of §0.1,
  bounded against `N_E` by the commutator estimate.  (ii) The Lagrangian determinant statement
  is a statement about the **un-eliminated** `det F` (positive on `‖F − 1‖ < 1`, §6.1): the
  deformation gradient is deliberately **not** eliminated, because `F_{ij} ⇒ i ℓ_j ξ_i` makes
  `F` rank one and annihilates both the Piola coupling and `det F`, collapsing `det F = 1` to a
  constant (machine-checked as B4a–B5b of that §9).  The literal-cubic comparison is recorded as a
  **no-go** (`DESIGN_COMPARISON_N_20260915.md` §4.1): its N-bound holds, but its commutator
  out-grows `n` by one order, and order counting shows no (pseudo)differential comparison of
  order `≥ 3` can repair it.  The candidates, the three rules behind them (positivity; quadratic
  degree closure; the wall inside `N`) and the obligation each still owes are derived in
  **`DESIGN_COMPARISON_N_20260915.md`** (§5 the Eulerian construction, §6 the determinant);
  the leading wave of `CONSOLIDATED_PLAN.md` records them under "The comparison operator
  `N` — one per Hamiltonian".
* **Residual.**  `π = −i ∂/∂u` is not boundedly invertible (its `u`-constant mode is in the
  kernel), so `π^{−1}` is the inverse on the physical (no-`u`-momentum) sector; the continuum
  operator is defined after the finite energy/momentum cutoff (Ch. 2 of `book.tex`); the
  Plancherel gluing and the Faris–Lavine constants remain plan items.  These are honest
  residuals, not axioms, and they are recorded in the leading wave of `CONSOLIDATED_PLAN.md`
  (2026‑09‑15).

## 1. Quantum gravity — vielbein **and** scalaron **and** both gauge fixings

This is the only gravity model of interest: vielbein *and* scalaron with the full exponential
potential (no Taylor expansion) *and* 3D gauge fixing *and* the gauge fixing of the variables
representing spatial derivatives of the fields; no lattice; outer Fock space.  It is
`BookProof/ChapterQgVielbeinScalaronGaugeFL.lean`.  Reviewed again in this revision and
unchanged: it is `sorry`-free and its audit reports only the standard axioms.  (By the §0.1
revision the `D_{μν}^i` are *eliminated* by the substitution `D_{μν}^i = i k_μ e_ν^i` rather
than gauge-fixed; the module and every result below are unchanged.)

* **No lattice.**  The vielbein is expanded in its *exact* Fourier modes, so momenta run over
  all of `ℤ³` and the spatial derivative is the exact symbol `∂_μ ↦ i k_μ`.  The mode set is
  infinite (`infinite_gmode`) and nothing is truncated.
* **Vielbein and derivative variables.**  At each momentum the components are the nine
  `e_ν^i` and the twenty-seven **independent** `D_{μν}^i` representing `∂_μ e_ν^i`
  (`Comp`, `eIdx`, `dIdx`) — the mode-space counterpart of the jet coordinates of the
  `84`-coordinate formulation.
* **Three families of linear forms** (`gCoef`): the torsion `T_{μν}^i = D_{μν}^i − D_{νμ}^i`
  written purely in the derivative variables; the **gauge fixing of the derivative
  variables** `G_{μν}^i = D_{μν}^i − i k_μ e_ν^i`; and the **3D gauge fixing**
  `C^i = Σ_μ i k_μ e_μ^i` (transverse condition on the spatial slice).
  `torsion_eq_exact_of_gauge_fixed` proves that **on the gauge-fixing surface the torsion
  written in the independent derivative variables is the exact torsion**
  `i(k_μ e_ν^i − k_ν e_μ^i)` of the fields — the precise sense in which that gauge fixing
  does what it is meant to do.
* **The scalaron.**  Position representation on the fibre `L²(ℝ_φ)` with the **full
  exponential** Einstein-frame potential (`starobinskyWall`), no Taylor expansion and no
  relative-boundedness hypothesis on the wall, coupled to the trace of the vielbein at
  arbitrary coupling constant `g` (`gCoupling`).
* **The certificate.**  `qgFullModes` supplies all five Faris–Lavine bounds uniformly in the
  momentum, with `κ = 855 + |g|` and band size `36`.  The comparison operator is the
  `ℓ²`-lift of the Friedrichs extension of the positive fibre operator
  `−∂²_φ + φ²/4 + V(φ) + σ_a`: the wall itself sits in the comparison operator.
* **The results.**  `qgFull_esa_farisLavine` (on the domain of the lifted Friedrichs
  extension), `qgFull_esa_core_fl` (on the finite-particle core, where the Hamiltonian is
  defined), the physical instances `starobinsky_qgFull_esa`, `starobinsky_qgFull_esa_core`,
  and the dynamics `qgFull_stone_flow`, `starobinsky_qgFull_stone_flow`.
* **Non-vacuity.**  `gCoef_torsion_ne_zero`, `gCoef_dGauge_ne_zero`, `gCoef_gauge3d_ne_zero`,
  `gGram_diag_ne_zero`, `gCoupling_ne_zero`.

### 1.1 The gravity Hamiltonian with the scalaron is *not* kinetic-plus-squares

The 2026‑09‑11 note said that "the densitized 3D gauge-fixed gravity Hamiltonian on the 84
coordinates (tetrad plus the independent coordinates for its derivatives) is identified as a
kinetic-plus-squares operator".  That sentence is true **only of the pure tetrad/jet model of
`BookProof/ChapterQg3DGaugeFarisLavine.lean`, which carries no scalaron**, and it must not be
read as a statement about the gravity Hamiltonian of §1.  With the full exponential potential
kept, no such identification exists, and the module
**`BookProof/ChapterScalaronNotQuadratic.lean`** proves it:

* `starobinskyV_le_plateau` — on the plateau side the wall is bounded by `M⁴/(16α)`;
* `starobinskyV_pos` — it is not the zero potential;
* **`starobinskyV_not_quadratic`** — there are no reals `a, b, c` with
  `V(φ) = aφ² + bφ + c` for all `φ`: a polynomial of degree `≤ 2` that is non-negative on the
  line and bounded on a half-line is constant, and the wall is not;
* `starobinskyPot_not_quadratic` — the same for the fibre potential `φ²/4 + V(φ) + s`;
* **`starobinskyPot_not_sum_of_squares`** — hence it is not a half-sum of squares
  `½ Σ_r (c_r φ)²` of linear forms, for **any** finite family of linear forms.

Since the potential of a kinetic-plus-squares operator `½ Σ_j κ_j π_j² + ½ Σ_r L_r²` *is* a
half-sum of squares of linear forms, this rules the identification out.  The scope note is in
the docstring of `ChapterQg3DGaugeFarisLavine.lean` as well: the `84`-coordinate model is the
tetrad/jet sub-model without the scalaron, kept because it is the setting in which the two
gauge-fixing families are written coordinate by coordinate (`div3Vec`: `Σ_j E_{jj}^a = 0`;
`timeDerivVec`: `E_{0ν}^a = 0`), and it is *not* the gravity Hamiltonian of interest.  The
Hamiltonian of interest is the one of §1, whose proof uses the Faris–Lavine mode machinery
with a genuine wall in the comparison operator and never the kinetic-plus-squares route.

### 1.2 No lattice, because the particle number is conserved

`dsOp_number_conserving` — every direct-sum (outer) Hamiltonian is block diagonal in the
particle-number sectors — with `qgGaugeOuterHam_sector` identifying the restriction to the
`n`-particle sector as the `n`-particle Hamiltonian.  In the mode model the corresponding
statement is `secHam_number_conserving`: for any number assignment constant on the bands
every number sector is invariant; the bands there are the momentum blocks
(`qgFull_momentum_conserving`, `qgFull_number_conserving`).  The nested Fock space is
decomposed by its number sectors, not by a spatial lattice, and no lattice regularization
occurs anywhere in this line.

## 2. Navier–Stokes — the **full** Hamiltonians, Eulerian and Lagrangian, no approximation

The standing caveat of the earlier revisions ("the advection is the Oseen linearisation") is
**removed**.  Two new modules carry the Hamiltonian with the complete nonlinearity, in the
two sets of variables, each on its own nested Fock space, each with the gauge fixing of the
variables that represent spatial derivatives of the fields (by the §0.1 revision those
derivative variables are eliminated by the spatial Fourier transform; the modules and their
results are unchanged):

### 2.1 Eulerian variables — `BookProof/ChapterNavierStokesFullEulerianFock.lean`

`21` coordinates per parcel: the three velocity modes `u_i`, the nine **independent
coordinates `u_{i,j}` representing `∂_j u_i`**, the three viscous coordinates `w_i`
(representing `Δu_i`), the three pressure-gradient coordinates `q_i`, and the three auxiliary
expansion coordinates `y_j`.  `19` constraint forms per parcel:

* the **full Navier–Stokes residual** `R_i = Σ_j u_j u_{i,j} + q_i − ν w_i` — the advection is
  the exact quadratic `u·∇u`, transported by the dynamical velocity of the same parcel, not
  by a frozen background field.  `nsResPoly_not_affine` **proves** that this residual is not
  an affine form of the coordinates: the model is not, and cannot be rewritten as, an Oseen
  linearisation;
* **incompressibility** `Σ_j u_{j,j} = 0`, the 3D gauge fixing, written in the independent
  derivative coordinates;
* the **gauge fixing of the derivative variables** `λ(u_{i,j} + u_i − u_i^{next})`, which
  couples neighbouring parcels — so the Hamiltonian is genuinely interacting;
* the **gauge fixing of the viscous variables** `μ(w_i + Σ_j u_{i,j} − Σ_j u_{i,j}^{next})`;
* the **`y`-gauge fixing** `g·y_j`.

### 2.2 Lagrangian variables — `BookProof/ChapterNavierStokesFullLagrangianFock.lean`

`36` coordinates per parcel: the material position `ξ_i`, the velocity `v_i`, the material
acceleration `a_i`, the nine **deformation-gradient coordinates `F_{ij}` representing
`∂ξ_i/∂a_j`**, the nine velocity-gradient coordinates `V_{ij}`, the viscous coordinates
`S_i`, the material pressure gradient `q_i` and the auxiliary `y_j`.  `28` constraint forms
per parcel:

* the **Lagrangian momentum equation** `R_i = a_i + Σ_j cof(F)_{ji} q_j − S_i`, with the
  **exact cofactor matrix** of the deformation gradient (`cofPoly`): the pressure term is the
  exact Piola transform, quadratic in the derivative variables, not linearised;
* **volume preservation** `det F − 1 = 0` — the exact, *cubic* incompressibility constraint.
  `volumePoly_not_quadratic` **proves** that along the isotropic line it is `t³ − 1`, hence
  not any quadratic; in particular the usual linearisation `tr F − 3` is a genuine
  approximation and is not what is used here;
* the **gauge fixings of the derivative variables** `λ(F_{ij} − δ_{ij} + ξ_i − ξ_i^{next})`
  and `λ'(V_{ij} + v_i − v_i^{next})`, both coupling neighbouring parcels;
* the **gauge fixing of the viscous variables** and the **`y`-gauge fixing**.

### 2.3 What is proved for both full models

`H_n = ½ Σ_m π_m² + ½ Σ_r Φ_r²` with the `Φ_r` now *polynomial* (quadratic, resp. cubic)
rather than linear.  Hence, exactly as for non-abelian Yang–Mills:

* `nsSectorHam_quadForm_nonneg` / `lagSectorHam_quadForm_nonneg` — every parcel-number sector
  is bounded below, and `nsSector_friedrichs_extension` / `lagSector_friedrichs_extension`
  give a positive self-adjoint (Friedrichs) extension there;
* `nsFullFockHam_quadForm_nonneg` / `lagFullFockHam_quadForm_nonneg` — bounded below **on the
  nested Fock space**, positivity being checked fibrewise, and
  `nsFullFock_friedrichs_extension` / `lagFullFock_friedrichs_extension` give the positive
  self-adjoint extension there;
* **`nsFullOuterN_esa` / `lagFullOuterN_esa` — Faris–Lavine on the outer Fock space.**  The
  comparison operator is the `ℓ²`-lift of the sector Friedrichs extensions (`dsComparison` of
  `friedrichsComparison`), whose positivity, symmetry and surjectivity of `N + 1` are
  fibrewise; the criterion is applied in its `c = 0` form, the commutator vanishing, and the
  conclusion is that the lifted realization is essentially self-adjoint on its domain.
  `nsFullOuterN_isPositiveSelfAdjointExtension` /
  `lagFullOuterN_isPositiveSelfAdjointExtension` say that this realization **extends the
  Hamiltonian defined on the finite-parcel core**;
* `nsFullFock_stone_flow` / `lagFullFock_stone_flow` — the unitary time evolution (Stone);
* `nsFullFockHam_number_conserving` / `lagFullFockHam_number_conserving` — the outer
  Hamiltonian is block diagonal in the parcel-number sectors: **no lattice**.

### 2.4 The two layers, and the honest boundary

The earlier quadratic model (`BookProof/ChapterNsOuterFockFarisLavine.lean`, background
advection) is kept and remains valid where it applies: there the Faris–Lavine relative bound
holds, so one gets the stronger conclusion of *essential* self-adjointness on the
finite-parcel core (`EsaFarisLavineIndex.Ns.ns_outerHam_esa_fl`).

For the **full nonlinear** models that stronger conclusion is *not* claimed: with a quartic
(resp. sextic) potential the relative bound `‖Hu‖ ≤ K‖(N+1)u‖` fails for every comparison
operator built from the harmonic oscillator, exactly as it does for the non-abelian
Yang–Mills magnetic energy.  What is proved is what the positivity gives: a distinguished
positive self-adjoint realization on the outer Fock space, its Faris–Lavine essential
self-adjointness on its own domain, and its unitary flow.  Nothing here bears on classical
Navier–Stokes regularity.

This is consistent with the sharpness result of the thread,
`ChapterNavierStokesFullEsa.exists_nsFullData_not_hasZeroDeficiencyOn`: structural hypotheses
alone (symmetric modes and momenta, degree ≤ 3) never suffice for essential self-adjointness
of a nonlinear Navier–Stokes Hamiltonian, and the analytic input used in the two new modules
is precisely positivity — the constraints enter squared.

## 3. Quantum Yang–Mills — bounded below, so a **direct Friedrichs extension**

**`BookProof/ChapterYangMillsFockFriedrichs.lean`** (as noted in the request, the Yang–Mills
Hamiltonian is bounded below, so no Faris–Lavine certificate is needed here).

`99 = 3 + 24 + 72` coordinates per particle: three spatial coordinates, the `24 = 3 × 8`
gauge-field coordinates `A_{j,a}`, and the `72 = 3 × 3 × 8` **independent coordinates
`∂_j A_{k,a}`** representing the spatial derivatives of the gauge field.  Each particle of the
nested Fock space `⊕ₙ L²(ℝ^{99n})` carries its own copy (`ycoord`).

* `magPolyN` — the magnetic field `B_{i a} = ε_{ijk}(∂_j A_{k,a} + f_{abc} A_{j,b} A_{k,c})`
  of each particle at **arbitrary real structure constants**: the quartic, genuinely
  non-abelian case is included, with no restriction on the coupling.
* `gaussPolyN` — the **3D gauge-fixing form** `Σ_j ∂_j A_{j,a}`, the transverse condition on
  the spatial slice, written in the independent derivative coordinates; `gaussPolyN_eval`
  shows it is not vacuous.
* `ymSectorHam` — the `n`-particle Hamiltonian `½ Σ π² + ½ Σ B² + ½ Σ (gauge fixing)²`;
  `ymSectorHam_symmetricOn` and **`ymSectorHam_quadForm_nonneg`**: symmetric and **bounded
  below**.  Hence `ymSector_friedrichs_extension`, a positive self-adjoint extension in every
  sector.
* **`ymFockHam_quadForm_nonneg`, `ymFock_friedrichs_extension`** — the headline: the outer
  Hamiltonian on the nested Fock space is bounded below and has a positive self-adjoint
  (Friedrichs) extension, obtained from the project's own unconditional Friedrichs theorem
  `FriedrichsExtension.friedrichs_extension_exists` (no boundedness hypothesis) applied to
  the dense finite-particle core.  Positivity and symmetry are checked fibrewise, which is
  exactly why the construction lifts.
* `ymFock_stone_flow` — the unitary time evolution it generates (Stone).
* `ymFockHam_number_conserving`, `ymFockHam_sector` — the outer Hamiltonian conserves the
  particle number: no lattice.

The earlier Faris–Lavine Yang–Mills results are kept and remain valid where they apply
(`BookProof/ChapterYangMillsOuterFockFL.lean`): for the **abelian** magnetic field the
Hamiltonian is kinetic-plus-squares and is *essentially* self-adjoint — the self-adjoint
extension is unique — on the one-particle core and on the outer Fock space.

**What is proved for the non-abelian case, and what is not.**  Proved: bounded below, a
distinguished positive self-adjoint realization (the Friedrichs extension) and its unitary
flow, on every sector and on the whole nested Fock space.  Not proved, and not claimed:
*essential* self-adjointness, i.e. uniqueness of the self-adjoint extension, for `f_{abc} ≠ 0`
— the Faris–Lavine relative bound `‖Hu‖ ≤ K‖(N+1)u‖` fails for every comparison operator built
from the harmonic oscillator when the potential is quartic.  The matrix data of the full
non-abelian Hamiltonian in the Hermite basis (band radius, sparsity, entry bounds) is
available in `BookProof/ChapterYangMillsBandBounds.lean`.

## 4. What is *not* claimed

No spectral information, no mass gap, no continuum limit, and no statement about classical
Navier–Stokes regularity.  The Fock spaces are `ℓ²`-direct sums of the sectors
(distinguishable excitations, no symmetrization).  The geometric input of the mode models
(the mode set and the symbols) is data, not derived Riemannian geometry.  For the full
nonlinear Navier–Stokes models and for non-abelian Yang–Mills, uniqueness of the self-adjoint
extension from the finite-particle core is not claimed (§2.4, §3).

## 5. Verification

The modules of this line build (`lake build BookProof.ChapterEsaFarisLavineIndex`, which
pulls in every chapter cited above, including the two new Navier–Stokes chapters, and
`lake build BookProof.ChapterYangMillsFockFriedrichs`); none of the new modules contains
`sorry`; and the audit scripts
`Work/NsFullEulerianLagrangianAudit.lean` (this wave),
`Work/YmFockFriedrichsScalaronAudit.lean`,
`Work/QgVielbeinScalaronGaugeAudit.lean` and `Work/FarisLavineOnlyAudit.lean` report only
`propext`, `Classical.choice`, `Quot.sound` for every result listed above.  The 2026‑09‑15
revision is documentation only: no module of this line changed, so the verification above
still applies verbatim to the operator of §0.1 after the derivative variables are eliminated —
with the one deliberate exception recorded in §0.1: the Lagrangian **deformation gradient** is not
eliminated (the mode-wise substitution for it is degenerate), so the material Piola term and the
volume constraint keep `F` as an independent scalar mode (`CONSOLIDATED_PLAN.md` item 6).
