# Hamiltonian audit — what the proofs actually use, and the Faris–Lavine `N` of each theory

*2026‑09‑18.  Companion to `DESIGN_COMPARISON_N_20260915.md` (the design note that *chose* the
comparisons) and to `CONSOLIDATED_PLAN.md`.  This is an **evidence file**: for every one of the
QYM / QG / NS Hamiltonians it records (i) the declaration the proofs actually consume, (ii) the
already-proved theorem that pins that declaration to the intended physical expression, and
(iii) the explicit comparison operator `N` and commutator constant `c` of Theorem 1 of
Faris–Lavine.  Nothing here is a new obligation; two stale citations and one broken symbolic
module are reported at the end.*

## 0. Verdict

| theory | FL statement (proved) | comparison `N` | `c` | `N` is pinned to the physical `H` by |
| :-- | :-- | :-- | :-- | :-- |
| **NS**, one body (6 momenta) | `BookProof.NsOneBody.spHam_esa_farisLavine` | `spFried` = Friedrichs realization of `H_sp` itself | `0` | `spHam_eq_visc_add_advect`, `spHam_quadForm_nonneg`, `spFried_isPositiveSelfAdjointExtension` |
| **NS**, nested Fock lift | `BookProof.NsOneBody.nsSpDGamma_esa_farisLavine` | `nsSpDGammaFried` = Friedrichs realization of `dΓ(H_sp)` | `0` | `nsSpDGamma_one_particle`, `nsSpDGamma_number_conserving` |
| **NS**, outer Fock (gauge-fixed parcels) | `BookProof.NsOuterFock.nsOuterFock_esa_farisLavine` | lifted `harmFried (18n)` = `⊕ₙ Friedrichs(−Δ + ‖x‖²/4)` on `L²(ℝ^{18n})` | `flc = 1/2 + 84·B²` | `nsFamily_kap`, `nsFamily_dim`, `nsVec_coupling` |
| **NS**, full Lagrangian outer Fock | `BookProof.NsFullLagrangian.lagFullOuterN_esa` | lifted Friedrichs extension of the **auxiliary sum-of-squares operator** `lagSectorHam = weylOp … = ½Σ_m π_m² + ½Σ_r (form_r)²` (self-comparison — **not** of the NS Hamiltonian, see §2.3) | `0` | `lagSectorHam_quadForm_nonneg`, `lagFullFock_friedrichs_extension`, `detPoly_eval_testPt`, `volumePoly_not_quadratic` |
| **QYM**, one body (abelian, `D = 99`) | `BookProof.YmOuterFockFL.ymAbelian_esa_farisLavine` | `Friedrichs(−Δ + ‖x‖²/4)` on `L²(ℝ⁹⁹)` | `flc = Σ_j‖κ_j‖/2 + 2·(mass v)²` | `ymAbelian_eq_sqSumOp`, `gramQ_ymMagVec` |
| **QYM**, outer Fock (gauge-fixed parcels) | `BookProof.YmOuterFockFL.ymOuterFock_esa_farisLavine` | lifted `harmFried (99n)` | `flc = 12 + 2 059 200·B²` | `ymFamily_vv`, `ym_interaction_nontrivial` |
| **QG**, fibre / scalaron band | `BookProof.ScalaronOuterFockFL.secHam_essentiallySelfAdjointOn` | `secN` = `⊕ₐ Friedrichs(−∂²_φ + φ²/4 + V(φ) + σ_a)` (**wall inside**) | `6·Q.K` | `secHam_apply`, `secData_ext_core` |
| **QG**, full vielbein+scalaron, 3D gauge-fixed | `BookProof.QgVielbeinScalaronGaugeFL.qgFull_esa_farisLavine` | same `secN`, `Q = qgFullModes g` | `6·Q.K` | `qgFullModes` (κ = 855 + \|g\|, band 36), `gCoef_*_ne_zero`, `gCoupling_ne_zero` |
| **QG**, full model after the Fourier elimination | `BookProof.QgFullEliminated.qgElimFull_esa_farisLavine` | same `secN`, `Q = qgElimFullModes g` | `6·Q.K` | `qgElimFullModes` (κ = 513 + \|g\|, band 9), `eGram_eq_torsion_add_gauge3d` |
| **QG**, `dΓ` form on the outer Fock space | `BookProof.QgOuterFockFL.qgOuterFock_esa_farisLavine` | `dΓ(N₁)`, `N₁ = harmFried (84n)` | hypothesis `c` (uniform in `n`) | `qgOuterFriedN_isPositiveSelfAdjointExtension`, `qgOuterFriedN_apply` |
| **QG**, physical wall | `starobinsky_qgFull_esa`, `starobinsky_qgElimFull_esa` | as above with `W = starobinskyWall M α hα` | as above | `starobinskyV` (exact exponential), `starobinskyV_nonneg` |

Two families of comparison are in play, and the table shows the split cleanly:

* the **self-comparison** (`H = N`, `c = 0`), available exactly when the operator being
  compared is a positive sum of squares — `weylOp` is literally `½ Σ_i π_i² + ½ Σ_a B_a²`, so the
  NS one-body operator of record and its `dΓ` lift, and the full Eulerian/Lagrangian parcel
  models, all qualify.  **It does not qualify the Navier–Stokes Hamiltonian itself**, which is
  *not* bounded below (`nsKoopmanOp_not_bounded_below`, `nsKoopmanOp_not_positive`) — see §2.3;
* the **oscillator / wall comparison** with a uniform constant `c`: the harmonic
  `N₁ = −Δ + ‖x‖²/4` (possibly with the exponential wall moved *inside* `N`, as in QG's `secN`),
  used by the gauge-fixed *parcel* families (NS, YM) and by all four QG statements — the pure
  `dΓ(N₁)` spelling appears in the `qgOuterFock` route.

## 1. The nested-Hilbert-space convention

`CONSOLIDATED_PLAN.md` and `Book/` state the convention; here is where the Lean realizes it, so
the rest of the audit can refer to one notation.

* **One-particle level.**  `h` on `𝔥 = L²(ℝ^d)` (or the `d`-dimensional core representation).
* **Second quantization.**  `BookProof.FockSecondQuantization.dGamma col` is literally
  `dΓ(A) = Σ_{j,k} ⟪e_j, A e_k⟫ a_j† a_k` on the finite-occupation core (`Part2.lean:70`), and
  `dGammaOp col` is its realization on `lpFiniteModes Conf → Fock` (`Part2.lean:311`).  This is
  the "**one-particle Hamiltonian enclosed in creation (left) and annihilation (right)
  operators**" of the plan.
* **Outer Fock space over the gauge-fixed parcels.**
  `BookProof.SqSumOuterFamily.outerFock dim = lp (fun n => L2d (dim n)) 2` — the `ℓ²`-direct sum
  `⊕ₙ L²(ℝ^{dim n})` — with `outerCore dim` the finite-particle core, and
  `dsComparison`/`dsOp`/`dsFibOp` (`ChapterQgOuterFockFarisLavine/Part1`) the lifts.  Number is
  conserved by construction (`secHam_number_conserving`).

Two different lift spellings appear because the two chapters were written at different times:
`dGammaOp` (explicit `Σ a† a`) in the NS one-body chapter, and the `lp ℕ`-sector spelling
`dsOp`/`dsFibOp` in the parcel and QG chapters.  They are the same object; §7 records that the
plan should say so once.

## 2. Navier–Stokes

### 2.1 The auxiliary one-body operator (comparison/energy), and the NS Hamiltonian (`ChapterNsOneBodyDGamma`, namespace `BookProof.NsOneBody`)

**Correction (2026‑09‑19).**  The operator below is the *auxiliary positive operator* of the
Navier–Stokes sector — a positive sum of squares, and the one run as the Faris–Lavine comparison —
**not** the Navier–Stokes Hamiltonian.  (It is *not* to be confused with the literal object
book.tex floats in the sentence after eq. 4186, “using `H²(x)` as a positive auxiliary operator”:
that `H²` is the **square of the generator**, and it is **not** a valid Faris–Lavine comparison `N`
— the criterion needs `N + 1` *onto*, whereas `H² + 1 = (H−i)(H+i)` gives
`range(H²+1) ⊆ range(H−i)` so it fails exactly when `H` has a non-trivial deficiency; the
formalized general case is `BookProof.FarisLavine.not_farisLavine_criterion_of_relative_bound`,
and `D(H²) ⊊ D(H)` rules it out on the common domain.)  The
Navier–Stokes Hamiltonian is the Hermitized momentum×drift Koopman–von Neumann (Liouville)
generator of the **full** residual, which carries the pressure gradient `q_i = ∂_i p` (and the
external force `f_i`) as well as the advection and viscosity — the tree's
`BookProof.NsFullEuler.nsResPoly` (`u_j u_{i,j} + q_i − ν w_i`) with the incompressibility
`divPoly` (`Σ_j u_{j,j} = 0`); in the mainstream Leray–Galerkin form the pressure is eliminated by
the Leray projection, leaving `BookProof.NsKoopman.kvnPoly` / `nsKoopmanOp` with the pressure-free
drift.  The two are
*not* interchangeable: only the Koopman generator satisfies the defining commutator property of
the equation, `i[H, u_k] = 2F_k` with the full drift `F_k = u_j u_{k,j} + q_k − ν u_{k,jj} + f_k`
(i.e. the
Heisenberg equation of the velocity density **is** the Navier–Stokes equation), while the
auxiliary sum-of-squares gives the momentum density `i[½Σπ²,u_k] = π_k`.  The commutator
statement is verified symbolically at the one-body and outer-Fock levels (with the momentum-space
split `F_k → ν|k|²u_k + i(k·u)u_k`, the advection being the momentum convolution proved by
`fourier_advection_convolution`) in `../unfer/docs/ns_kvn_equation.cdb`; see
`../unfer/docs/VERIFY_FARIS_LAVINE_N.md`.  The choice of comparison operator is free
(Faris–Lavine), and it is this module `ChapterNsOneBodyDGamma` that supplies it.

The auxiliary operator is the *eliminated Eulerian* one-parcel one on `L²(ℝ⁶)`:

```
spHam Φ ν k = weylOp (spPi Φ) (spField Φ ν k)    -- ½ Σ_m π_m² + ½ Σ_{r<7} (mulOp Φ_r)²
```

with `spPi Φ m = Φ.op (momOp m)` (the six `π_m = −i∂_m`) and the **seven** multiplication forms
`spField Φ ν k r` = the three real residual parts `q_i + ν|k|²u_i` (`fourierVisc`), the three
advection parts `(k·u)u_i` (`fourierAdvect`), and the eliminated incompressibility `k·u`
(`fourierMomentum`).  That the seven forms are the intended ones is *proved*, not asserted:
`spFieldVisc_re`, `spFieldAdv_im`, `spFieldVisc_div` identify each form with its
`fourier*` polynomial.

The positive completion of the wave is visible in the splitting:

* `spField_sq_split` — each square splits into its viscous and advective part;
* `spHam_eq_visc_add_advect` — `H_sp = H_visc + H_advect`, `H_visc` carrying the six momenta
  and the four non-advective squares, `H_advect` carrying **only** the three squares
  `½((k·u)u_i)²` (no momentum term at all: `spAdvect = weylOp (fun _ : Fin 0 => 0) …`);
* `spHam_quadForm_split`, and `spHam_symmetricOn` / `spHam_quadForm_nonneg` plus the two halves.

So the advection is kept **squared**, never demoted to a perturbation and never dropped — the
route the plan adopted instead of a BRST gauge fixing of the derivative variables.  The module
doc-comment states the honest boundary as well: the shortcut `H = N` is available *because*
`H_sp` is a positive sum of squares, and it is **not** available for the mainstream
Koopman–von Neumann generator, which is not bounded below
(`BookProof.NsKoopman.nsKoopmanOp_not_bounded_below`); that sector uses the Leray energy
`N_E = 1 + ‖u‖²` (`BookProof.ChapterNsKoopman`).

**The comparison `N`.**  `spPosSym ν k` is the pair `(polyGaussCore 6, spHam)` with its symmetry
and positivity, and

```
spFried ν k = friedrichsComparison (spPosSym ν k) polyGaussCore_dense
```

is the **Friedrichs realization of `H_sp` itself**.  Then `polyGaussCore_le_spFriedDom` (domain
obligation), `spFried_op_core` (`N` extends the generator on the core),
`spHam_commForm_zero` (**`c = 0`**), `spHam_esa_farisLavine` (`EssentiallySelfAdjointOn` by
`Comparison.esa_self`), `spFried_isPositiveSelfAdjointExtension`, `spFried_dom_dense`,
`spHam_stone_flow`.

**The nested-Fock lift.**  `nsOnePart e ν k` is the same generator on the finite-mode domain of
the product-Hermite basis (`e : ℕ ≃ (Fin 6 →₀ ℕ)`), `nsSpCol e ν k` its column of coefficient
vectors (Hermitian and positive: `nsSpCol_isHermCol`, `nsSpCol_isPosCol`), and
`dGammaOp (nsSpCol e ν k)` is `dΓ(H_sp) = Σ a†_j (H_sp)_{jk} a_k`.  The certificate is
`nsSpDGamma_symmetricOn`, `nsSpDGamma_quadForm_nonneg`, `nsSpDGamma_friedrichs_extension`,
`nsSpDGammaFried`, `lpFiniteModes_le_nsSpDGammaFriedDom`, `nsSpDGammaFried_op_core`,
`nsSpDGamma_esa_farisLavine` (`H = N`, `c = 0`), `nsSpDGamma_number_conserving`,
`nsSpDGamma_one_particle` (non-vacuity: on the one-particle sector the lift **is** `H_sp`),
`nsSpDGamma_stone_flow`.

### 2.2 The gauge-fixed parcels on the outer Fock space (`ChapterNsOuterFockFarisLavine`)

`nsFamily : SqFamily` with `dim n = n * 18`, the eighteen coordinates of a parcel being the
three velocities, the nine derivative coordinates, the three constraint variables and the three
auxiliaries (`NsLoc`), and `kap ≡ 1` — the sector kinetic term is the **plain Laplacian**, with
no hyperbolic signature (`nsFamily_kap`).  The vertex data are `nsVec` with the coupling witness
`nsVec_coupling` and the interaction witness `ns_interaction_nontrivial`.  The Schur bounds are
`km = 1`, `a = 7B`, `b = 6B` (`nsVec_row_le`, `nsVec_col_le`).

**`N` = the lifted Friedrichs extension of `N₁ = −Δ + ‖x‖²/4` on each `L²(ℝ^{18n})`**, with

```
K = flK = 3km/2 + 4ab = 3/2 + 168 B²       c = flc = km/2 + 2ab = 1/2 + 84 B²
```

both uniform in the particle number (`ChapterSqSumOuterFamily.SqFamily.flK`, `.flc`,
`secHam_norm_le`, `secHam_commForm_le`, `secExt_rel`, `secExt_commForm_le`).  Conclusion:
`nsOuterHam_symmetricOn`, `nsOuterHam_esa_core` (the Carleman route, kept as a cross-check) and
`nsOuterFock_esa_farisLavine` — essential self-adjointness on `outerFriedDom`, plus the
extension property on the finite-particle core.

### 2.3 The full Lagrangian model

**Correction (2026-09-18).**  Earlier versions of this section, of the §0 table row and of the
plan's `N`/`c` table attached the self-comparison to *the NS Hamiltonian*.  That is wrong — the
NS Hamiltonian is not bounded below.  The
self-comparison `N = Friedrichs(·)`, `c = 0` is available exactly when the operator is a positive
sum of squares — and the object that is a positive sum of squares here is the **auxiliary
Weyl-ordered sum-of-squares operator**, *not* the Navier–Stokes Hamiltonian.

`lagSectorHam lam lam' mu gg n = weylOp (lagPiN n) (lagFieldN lam lam' mu gg n)` is, by
definition of `weylOp` (`ChapterYangMillsFriedrichs/Part2`), `½ Σ_m π_m² + ½ Σ_r (form_r)²`: the
squared momenta plus the squared constraint forms of the material model (kinetic, viscous, exact
Piola, the derivative-variable gauge fixings coupling neighbouring parcels, the viscous fixings
and the `y`-fixings).  Its quadratic form is manifestly a sum of squares, which is what
`weylOpDom_quadForm_nonneg` ⇒ `lagSectorHam_quadForm_nonneg` / `lagFullFockHam_quadForm_nonneg`
prove, and what makes the Friedrichs realization (hence the self-comparison) exist.
`BookProof.NsFullLagrangian.lagFullOuterN_esa` is then the Faris–Lavine statement on the outer
Fock space **with `c = 0`** and that lifted Friedrichs extension as comparison — the `Comparison.esa_self`
case.  It is the certificate the design note's `N_L` row intends.

**Why the distinction matters.**  The **Navier–Stokes Hamiltonian** is a different operator and is
**not bounded below**.  `BookProof.ChapterNsKoopman/Part1` defines it as `kvnPoly` / `nsKoopmanOp` —
the Weyl-ordered mainstream (Koopman–von Neumann / Liouville) generator with the *exact*
nonlinearity, explicitly “no square of a residual, no linearization, no perturbative splitting” —
and proves, on the Gauss–polynomial core of `L²(ℝᵈ)`:

* `kvnPoly_polySym` — it is symmetric on the core;
* `quadP_starP` — the antiunitary conjugation `Cψ = ψ̄` satisfies `C H_NS C = −H_NS`, so the
  numerical range is symmetric about `0` and it is bounded below **iff** bounded above;
* `kvn_quadP_not_bounded_below` / `nsKoopmanOp_not_bounded_below` — for `ν > 0` and one positive
  Stokes eigenvalue `λ_i > 0`, `inf ⟪x, H_NS x⟫ / ‖x‖² = −∞`; hence `nsKoopmanOp_not_positive`:
  it is not positive and **cannot** be a Faris–Lavine comparison operator for itself.

So for the NS Hamiltonian no Friedrichs realization and no self-comparison exist; its leg carries
the **Leray-energy** comparison `N_E = 1 + ‖u‖²` instead (`ChapterNsKoopman/Part2`:
`nsEnergyOp_quadForm_ge`, `commForm_kvn_energy_bound`, `nsKoopman_esa_of_energy_comparison`).  The
same distinction governs the full **Eulerian** model (`ChapterNavierStokesFullEulerianFock`,
`nsFullEuler_outer_esa_fl`): what is bounded below there is likewise the auxiliary sum-of-squares
operator `nsSectorHam = weylOp …`, not `H_NS`.  The `c = 0` in these rows is therefore a
statement about the auxiliary operator, and must never be quoted as “the NS Hamiltonian is
bounded below”.  Recorded here because it is the one place in the tree where the naming invites
it: `nsFullEuler_bddBelow` / `nsFullLagrangian_bddBelow` are *aliases* for
`nsFullFockHam_quadForm_nonneg` / `lagFullFockHam_quadForm_nonneg`, whose subjects are the
`weylOp` sum-of-squares operators — the Lean statements are correct; only the readings that
attached them to the NS Hamiltonian were not.

## 3. Yang–Mills (QYM)

### 3.1 The one-body, abelian Hamiltonian

`BookProof.YmOuterFockFL.ymAbelian_eq_sqSumOp` **is** the identification:

```
ymHamiltonian (coreRepPoly 99) 0 = sqSumOp ymKap ymMagVec
```

i.e. the abelian Yang–Mills Hamiltonian is `½ Σ_j κ_j π_j² + ½ Σ_m B_m²` with the signature
`ymKap` (`|ymKap l| ≤ 24`, `abs_ymKap_le`) and the 24 magnetic forms `ymMagVec`, whose Gram
matrix is `ymFqQ` (`gramQ_ymMagVec`, by `rfl`).  The Cadabra module reproduces the same shape
from the Lagrangian — see §6.2.

`ymAbelian_esa_farisLavine` then proves essential self-adjointness on the Gauss–polynomial core
by `BookProof.FarisLavineOnly.sqSumOp_esa_farisLavine ymKap ymMagVec`, whose comparison is the
**Friedrichs extension of `N₁ = −Δ + ‖x‖²/4`** with the trivial Schur data
(`constFamily`: `km = Σ_j |κ_j|`, `a = b = totalMass v`), i.e.
`K = 3·Σ|κ|/2 + 4·(totalMass v)²`, `c = Σ|κ|/2 + 2·(totalMass v)²`, and **no Carleman flux
estimate** anywhere (`ChapterFarisLavineOnly`).

### 3.2 The gauge-fixed parcels on the outer Fock space

`ymFamily : SqFamily`, `dim n = n * 99` with the 104 linear forms `YmForm` per parcel
(`card_ymForm`), and `km = 24`,
`a = 990B`, `b = 1040B`, hence

```
K = flK = 36 + 4 118 400 B²        c = flc = 12 + 2 059 200 B²
```

uniform in the particle number.  The Hamiltonian contains the magnetic energy of every parcel,
the 3D Gauss gauge-fixing terms, and the ties of the derivative coordinates to the finite
differences between neighbouring parcels (`ym_interaction_nontrivial` is the witness that the
last are genuine interactions).  `ymOuterHam_symmetricOn`, `ymOuterHam_esa_fl`, and finally
`ymOuterFock_esa_farisLavine` with the lifted `harmFried (99n)` as `N`.

## 4. Quantum gravity (QG)

Four proved FL statements, all with the **wall inside the comparison** (rule R3 of the design
note), which is the substantive difference from the parcel families above.

### 4.1 The fibre comparison

```
W.ham s        = wallHam (W.pot s) = kinCcR + opCc (pot s)        -- −d²/dφ² + φ²/4 + V(φ) + s
W.posSym s     = PosSymOp with op = W.ham s
fibCompar W Q a = W.comparison (Q.sig a)                          -- Friedrichs of the fibre operator
secN W Q       = dsComparison (fibCompar W Q)                     -- the ℓ²-lift over the modes
secCore        = dsCore (fun _ => ccDomain ℝ)
secHam W Q     = secDiag W Q + secA Q + secB Q                    -- fibre + vielbein A + coupling B
```

`secHam_commForm_le` is the commutator bound, `|commForm (secHam) (secDiag) x| ≤ (6·Q.K)·quadForm
(secDiag) x`, and `secHam_rel` the uniform relative bound with `K = 1 + 3·Q.K`; together they
give `secHam_essentiallySelfAdjointOn` via `secData`.  **`N` is therefore the `ℓ²`-lift of the
Friedrichs extension of `−∂²_φ + φ²/4 + V(φ) + σ_a`, the whole smooth non-negative wall `V`
included, and `c = 6·Q.K`.**  This is exactly the `N_QG` candidate of the design note §2.

### 4.2 The full model

* `qgFullModes g : QgModeData GMode` — the complete gauge-fixed model: `κ = 855 + |g|`, band 36,
  the scalaron–vielbein coupling at arbitrary `g`; `qgFull_esa_farisLavine` and
  `qgFull_esa_core_fl` are the two statements (whole domain / finite-particle core), and
  `secHam_number_conserving`, `secCore_dense`, `qgFull_stone_flow` complete the package.
* The **physical wall**: `starobinsky_qgFull_esa` instantiates `W = starobinskyWall M α hα`, and
  `starobinskyV M α φ = M⁴/(16α)·(1 − e^{−√(2/3)·φ/M})²` is the exact exponential — no Taylor
  truncation — with `starobinskyV_nonneg` (strongest sign form), `starobinskyV_zero`,
  `starobinskyV_tendsto_plateau`.
* **The wall's closed form is now derived, not asserted** (2026-09-21).  The Jordan-frame
  modules stop at `U(ψ) = (M⁴/16α)(ψ−1)²`; `../unfer/docs/qg_starobinsky_einstein_frame.cdb`
  certifies the conformal rescaling link `U(ψ)/ψ²  at  ψ = e^{√(2/3)φ/M}  =
  (M⁴/16α)(1 − e^{−√(2/3)φ/M})²` (weight `√(−g) = ψ²√(−g̃)`; kinetic `(3M²/4)(∂lnψ)² =
  ½(∂φ)²`), so `starobinskyV` is the genuine Einstein-frame potential of `f(R) = (M²/2)R + αR²`.
  The same note records the source-level comparison showing that the one-particle kernel used
  here — `oneParticleOp`/`secHam`/`qgFullModes`,
  `h_{ab} = δ_{ab}(−d²/dφ² + φ²/4 + V(φ) + σ_b) + A_{ab}·1 + B_{ab}·φ` — is the plan's stated QG
  inner operator **term for term**.  Evidence: `../unfer/docs/VERIFY_QG_STAROBINSKY_EINSTEIN_FRAME.md`.
* `ChapterQgFullEliminated` rebuilds the same model on the nine vielbein components **after the
  Fourier elimination** (`eSig = 1 + |k|²`, `eGram`, `eCoupling g`), with
  `eFormValue_torsion` (the eliminated torsion is the exact Fourier torsion),
  `eFormValue_dGauge` (the derivative-gauge forms vanish **identically** — solved by
  construction rather than imposed), `eFormValue_gauge3d`, `eGram_eq_torsion_add_gauge3d`, and
  `qgElimFull_esa_farisLavine` / `qgElimFull_esa_core_fl` / `starobinsky_qgElimFull_esa` with
  `κ = 513 + |g|`, band 9, and **no restriction-to-a-subset argument**.  This is the formal
  counterpart of the symbolic elimination in `../unfer/docs/ns_qg_fourier_elimination.cdb`.
* `ChapterQgOuterFockFarisLavine/Part2` is the `dΓ` spelling of the same certificate:
  `qgOuterComparison = dsComparison (fun n => harmFried (n * 84))` = `dΓ(N₁)`,
  `qgOuterFriedN_isPositiveSelfAdjointExtension` (the Friedrichs extension lifts),
  `qgOuterFriedN_surj` (`N + 1` onto), `qgOuterFriedN_esa` (`H = N`, `c = 0`) and
  `qgOuterFock_esa_farisLavine`, which takes the sector data `(H n, hsym, hext, K, c)` as
  hypotheses and is uniform in the particle number.

## 5. The comparison operators, explicitly

Only two comparison operators are used by the *parcel* families; three by QG.

```
N_NS,one-body   = N_E = Friedrichs(H_sp)                            c = 0
N_NS,dΓ         = Friedrichs(dΓ(H_sp))                              c = 0
N_NS,outer      = ⊕ₙ  Friedrichs(−Δ + ¼‖x‖²) on L²(ℝ^{18n})         c = ½ + 84 B²
N_YM,one-body   =      Friedrichs(−Δ + ¼‖x‖²) on L²(ℝ^{99})         c = Σ‖κ‖/2 + 2(mass v)²
N_YM,outer      = ⊕ₙ  Friedrichs(−Δ + ¼‖x‖²) on L²(ℝ^{99n})         c = 12 + 2 059 200 B²
N_QG,fibre      = ⊕ₐ  Friedrichs(−∂²_φ + φ²/4 + V(φ) + σ_a)         c = 6 K_Q
N_QG,outer(dΓ)  = ⊕ₙ  Friedrichs(−Δ + ¼‖x‖²) on L²(ℝ^{84n})         c uniform (hypothesis)
```

Three points worth stating plainly, because they are easy to get wrong:

1. **The NS one-body comparison is not the oscillator.**  `N_E` is the Friedrichs realization of
   the Hamiltonian itself; the oscillator comparison is what the *gauge-fixed parcel* family
   uses.  The two live in the same route and must not be conflated.
2. **`c = 0` for NS one-body/`dΓ` and for the full Eulerian/Lagrangian models** is a
   *consequence of positivity* of the **auxiliary sum-of-squares operator** (`commForm H H = 0`),
   not a smallness statement: Faris–Lavine consumes no relative-bound smallness
   (`DESIGN_COMPARISON_N_20260915.md` §0).  It is **not** a statement about the NS Hamiltonian,
   which is not bounded below (§2.3).
3. **The wall is inside `N` in every QG statement**, so the exponential does not have to be
   `N`-bounded as a perturbation — the relative bound `K = 1 + 3·K_Q` is a statement about the
   vielbein matrices, not about `V`.
4. **The mainstream NS Hamiltonian has no comparison in this table**, because it is the only
   operator here that is not a positive sum of squares: its leg carries the **Leray energy**
   `N_E = 1 + ‖u‖²` (`BookProof.NsKoopman.nsEnergyOp`), a multiplication operator (positive,
   self-adjoint, `N_E + 1` onto) whose commutator is the sign-definite viscous dissipation
   (`commForm_kvn_energy_bound`, `nsKoopman_esa_of_energy_comparison`).  Its `N` is **not**
   book.tex's literal `H²`: the criterion needs `N + 1` onto, and `H² + 1 = (H−i)(H+i)` gives
   `range(H²+1) ⊆ range(H−i)`, so `H² + 1` fails to be onto exactly when `H` has a non-trivial
   deficiency (the formalized general case is
   `BookProof.FarisLavine.not_farisLavine_criterion_of_relative_bound`), and `D(H²) ⊊ D(H)`
   independently excludes it.  Symbolic evidence: `../unfer/docs/ns_kvn_equation.cdb` CHECK 4–6.

## 6. Independent evidence (symbolic and arithmetic)

### 6.1 NS / QG Fourier elimination, re-run 2026‑09‑18

```
cadabra2-cli -q -n ../unfer/docs/ns_qg_fourier_elimination.cdb
```

Exit code 0; all A1–E3 checks print `0` as recorded in `../unfer/docs/VERIFY_NS_QG_FOURIER.md`:
the determinant identities (A), the Lagrangian substitution and — crucially — **the B4/B5
rank-one degeneracy** it exposes, the Eulerian substitution with the residual
`i(k·u)u_i + q_i + ν|k|²u_i` (C1/C2, matching `spFieldVisc`+`spFieldAdv` term by term), the
degree `q+1` no-go for the bare cubic (D), and the convolution bookkeeping (E).  The C-line is
the symbolic statement of the NS one-body generator of §2.1; the B-line is the reason the
Lagrangian determinant is carried as an independent scalar mode rather than eliminated.

```
cadabra2-cli -q -n ../unfer/docs/ns_kvn_equation.cdb
```

Exit code 0; CHECK 1a–1c identify the Navier–Stokes Hamiltonian through `[H,u_k] = −2iF_k` with
the full drift `F_k = u_j u_{k,j} + q_k − ν u_{k,jj} + f_k` (pressure gradient `q_k` and force
`f_k` included), CHECK 5 shows the Hermitized `π^iF_i + F_iπ^i` carries **both** the flow term and
the `+h.c.`/ordering term `−i(div F)` (so the operator is complete — book.tex 4186 to the letter),
CHECK 4–6 give the commutation condition and the sign-definite energy flux for the **valid**
comparison `N_E = 1 + ‖u‖²` (Leray), CHECK 7 records that the advection is the bilinear
(convolution) term while the viscosity is diagonal, and CHECK 8 verifies the pressure/constraint
structure (incompressibility `Σu_{j,j} → i(k·u)`, pressure does no work `Σu_k q_k → i(k·u)p = 0`).
The companion module `../unfer/docs/ns_pressure_poisson.cdb` derives the resulting pressure Poisson
equation `Δp = −∂_i(u_j∂_ju_i) + ∂_i f_i` by contracting the divergence with the momentum
equation (Clairaut for the viscous term, the Leibniz split `div[(u·∇)u] = tr((∇u)²)` for the
advection, and the constraint cancellations).  That equation is a **second-class** constraint: it
*determines* the multiplier `p` (inverting `Δ`, invertible on the non-zero modes), so there is no
gauge freedom to fix — the only free mode is the additive constant of `p`, invisible to
`q_i = ∂_i p` — and the correct treatment is the elimination strategy, not a new BRST generator.
This is book.tex's own taxonomy (the divergence constraint is solvable; the BRST charge is "only
the elegant packaging") and the tree's `ChapterNavierStokesEulerian` (`div u = 0` =
explicit-solution constraint; the derivative relations are the gauge-generator ones, with the
nilpotent `Ω = Σ_j G_jχ_j`, `[Ω,H] = 0`, in `ChapterNsBrstDerivativeGauge`).  Verified in
`../unfer/docs/ns_pressure_constraint.cdb` (CHECK 2/3 second-class; CHECK 4 cosmetic nilpotency;
CHECK 5 elimination).
See `../unfer/docs/VERIFY_FARIS_LAVINE_N.md`.

### 6.2 Yang–Mills, re-run 2026‑09‑18

```
cadabra2-cli -q -n ../unfer/docs/yang_mills_hamiltonian.cdb  <epilogue printing the named objects>
```

```
CHECK YM Lagrangian L_y     = 1/2 π^i_a π^i_a − 1/2 B_{i a} B_{i a}
CHECK YM H_final (Legendre) = 1/2 π^{i1}_a π^{i1}_a + 1/2 B_{i1 a} B_{i1 a}
```

The Legendre transform of the module's own Lagrangian is `½Σπ² + ½ΣB²` — the shape of
`sqSumOp ymKap ymMagVec` (§3.1).  The same module also carries the BRST generator (`ss`), and
the printed expression is manifestly `A_0`-dependent: the BRST route is *not* what fixes the
derivative variables, in accordance with the wave's plan of record.

### 6.3 QG densitized Hamiltonian, re-run 2026‑09‑18

```
cadabra2-cli -q -n ../unfer/docs/qg_gauge_fixed_hamiltonian.cdb  <epilogue>
```

```
RESULT qg t0_tegr (teleparallel torsion scalar) = e X_ab^b X^{ac}_c − … − ½ e X_abc X^{abc} + …
RESULT qg pi_derived (polymomentum)             = e e^μ_a e^ν_b η^{ab} … ∂_α(e^{j1}_σ) + …
RESULT qg8190 H_final (3D gauge-fixed)          = (1/16)𝒮_ab𝒮^{ab} e^{-1} − (1/24)𝒫𝒫 e^{-1}
                                                  + ½ T_abc T^{acb} e + ¼ T_abc T^{abc} e
                                                  − T^{ab}_b T_{ac}^c e − ¼ T_ab T^{ab} e
                                                  − E^{ab} T_ab e + ½ E^{ab}𝒮_ab
                                                  + ⅓ E^a_a 𝒫 + 2E_a T^{ab}_b e
```

i.e. book.tex‑8190, the 3D gauge-fixed Hamiltonian with the coefficients `1/16, −1/24, ½, ⅓`
and the torsion block — the object `BookProof.ChapterQuantumGravityDensitized` (`qg3DDensity`,
`qgSymbol`, `qgKappa`) formalizes.  Confirms `../unfer/docs/VERIFY_QG_DENSITIZED.md` check 1.

**Module repaired (2026‑09‑18).**
`../unfer/docs/qg_starobinsky_vielbein_hamiltonian.cdb` used to **abort** on Cadabra 2.5.14 at
line 141 (`RuntimeError: Python object '\prod' does not exist`).  Repairing the abort exposed
three further defects, and all four are now fixed:

1. the `@(name)` insertion macro resolves its argument through the LaTeX parser — an underscore is
   read as a subscript separator unless its stem is at least four characters — so `@(U_psi)`,
   `@(ex1_st)`, `@(H_8182_st)` and `@(H_final_st)` all mis-resolve (while `@(action_st)`, stem
   `action`, is fine); the aborts are the first three, and the last had the module's own Rust test
   `symbolic::tests::qg_starobinsky_vielbein_hamiltonian_derivation_runs` unable to extract it;
2. `fR_check` and `R2_check` never reached zero — the missing `expand`/`expand_power` steps (the
   sibling metric-route module has them) left `M⁴ α⁻¹ (R α M⁻²)²` unexpanded;
3. the scalaron polymomentum was defined under the name `pi_psi`, but the header, `AGENTS.md` and
   the Rust test all name it `pi_psi_check` (and the test's extraction is name-based), so the test
   could not have been green;
4. the chain copied the base module's `unwrap(ex1_st)` *before* `integrate_by_parts`; `unwrap`
   strips the top node of every term, so on the post-`product_rule` sum it kept only the first
   term — `ex1_st` collapsed to `U(ψ)e` and `pi_st` to `0`.  Removed; `ex1_st` is now the
   121-node expanded action density and `pi_st` the full `(M²/2)ψ·π₀`.

The module now runs clean (exit 0) and the identities it advertises vanish: `fR_check = 0`,
`R2_check = 0`, `pi_psi_check = 0`.  `H_final_st` and `base_limit_check` are
`(M²/2)ψ·(book.tex 8190) + U(ψ)e` and `(M²/2)·(book.tex 8190)` coefficient by coefficient (all
ten terms, exact rational arithmetic), unchanged by the repairs.  The module's Rust test passes on
a replay of `symbolic_derive`'s own extraction — its trailer, its CLI invocation and its eight
assertions (the crate itself is not buildable offline here: the `nanoda_lib` git dependency needs
network, so `cargo test -p prob_kernel` was not run).  Details in
`../unfer/docs/VERIFY_QG_STAROBINSKY_VIELBEIN.md`.  The **same** `unwrap` defect was found in the
**base** module `qg_gauge_fixed_hamiltonian.cdb` — silently, since that module does not abort and
its Rust test only asserts `ex1` is non-empty and tetrad-shaped — and was repaired on the same date:
its `ex1` (documented as the Einstein-Hilbert action density `eR`) went from **one summand**
(`len` 18, a single product of 18 factors; 199 chars) to the full **120-summand** integrand
(18 181 chars), and `pi_derived` from 2 to **132** summands.  A **module-level audit of all seven
`../unfer/docs/*.cdb` modules** for this class (epilogue dumping the size of every named expression,
counterfactual runs, replay of the Rust extraction trailer) confirms it was the **only** truncated
module, and that no module has an active `unwrap` in `post_process` — the variant that would
corrupt every sum in the file.  The audit also records two adjacent non-truncation findings (a
`diff` handle that is a hand-typed tautology, and a benign `unwrap` on a plain sum) in
`../unfer/docs/VERIFY_CDB_TRUNCATION_AUDIT.md`.  `G`, `t0_tegr` and `H_final` are byte-identical
before and after the base repair, so nothing in the Lean tree depends on the change either way,
and §6.4's exact-arithmetic reproduction of the same identities is unaffected.

### 6.4 Independent exact-arithmetic checks (19/19 pass)

`scripts/check_hamiltonian_identities.py` (exact `Fraction` arithmetic, no Cadabra, re-runnable
in a second) re-derives, in the same normalisations:

* **YM**: `¼F_ij F^ij = ½B·B` with `B_i = ½ε_ijk F_jk`, and the Legendre step
  `H = π² − (½π² − ½B²) = ½π² + ½B²`;
* **NS**: `|i(k·u)u_i + q_i + ν|k|²u_i|² = ((k·u)u_i)² + (q_i + ν|k|²u_i)²` for `i = 0,1,2`
  (the positive completion: both real parts squared = the modulus square of the complex
  residual), the C1 expression and the C4 divergence;
* **QG**: the `f(R)` identity at `ψ = 1 + 4αR/M²`, the `αR²e` content, the `α → 0` limit,
  linearity of `H_final_st` in the auxiliary `ψ`, the densitization
  `(1/16e)(yS)² − (1/24e)(yP)² = (1/16)S² − (1/24)P²` at `e = y²`, and the wall's
  `V(0) = 0`, `V'(0) = 0`, `V''(0) = M²/(12α)`, plateau `M⁴/(16α)` and `V ≥ 0`.

### 6.5 The independent Rust realization (present; not re-run here)

`../unfer/nested_fock_algebra/src/unit_tests.rs` contains the matching numerical tests —
`test_navier_stokes_hermitian`, `test_ns_hermite_derivative_fixing_nilpotent_and_closed`,
`test_qcd_ym_hamiltonian_outer_fock_vacuum_zero_and_hermitian`,
`test_qg_tegr_hamiltonian_outer_fock_vacuum_zero_and_hermitian`,
`test_qg3d_full_hamiltonian_cross_terms_and_indefinite`,
`test_qg_starobinsky_hamiltonian_vacuum_zero_and_hermitian`,
`test_qg_starobinsky_vielbein_full_exponential_hermitian_and_structure`.  They were **not
re-executed in this audit**: the workspace pins `nanoda_lib` through a `git` dependency (needs
network) and the flake's default dev shell pulls a CUDA closure.  Run them in a networked
shell before citing them.

### 6.6 The Faris–Lavine comparison `N` and its commutation conditions, certified 2026‑09‑19

Two new Cadabra modules in the sibling repo re-derive the one-particle content of the
comparison-operator certificate that §5/§8 record; both run clean (`exit 0`) with every numbered
check reducing to `0` (evidence: `../unfer/docs/VERIFY_FARIS_LAVINE_N.md`).

```
cadabra2-cli -q -n ../unfer/docs/faris_lavine_n_ns.cdb
cadabra2-cli -q -n ../unfer/docs/faris_lavine_n_qg.cdb
```

**NS** (`faris_lavine_n_ns.cdb`): `H = ½Σ_j κ_j π_j² + ½Σ_r L_r²`, `π_j = −i∂_j`, `L_r = Σ_i v_{ri}x_i`,
against the oscillator `N = −Δ + ‖x‖²/4`.  CHECK 1 (Leibniz expansion of `H(Nφ) − N(Hφ)`) reproduces
the shape of `commPoly_eq` — the commutator is **first order**,
`[H,N] = (−¼Σ_j κ_j + Σ_rΣ_k v_{rk}²) + Σ_j(−κ_j/2) x_j ∂_j + 2 Σ_j (∂_j V) ∂_j`; CHECK 2 verifies the
potential data `∂_j V = grad_j`, `∂_j² V = Σ_r v_{rj}²` (hence `commConst = −¼Σκ + Σ v²`); CHECK 4 the
AM‑GM `a² + b²/4 − ab = (a − b/2)²` and Young `2M(g²/2M + 2Ma² − 2ga) = (g − 2Ma)²` identities behind
`c = km/2 + 2M` and `K = 3km/2 + 8B`.

**QG** (`faris_lavine_n_qg.cdb`): `H_fib = N = −∂²_φ + φ²/4 + V(φ) + σ` with the **full exponential
wall inside `N`**, `H = secDiag + secA + secB`.  CHECK 1 the fibre self-commutator `[H_fib,N] = 0`
(the `c = 0` fibre part), CHECK 2 `[A,H_fib] = 0` for the constant vielbein self-interaction (`imA_le`),
CHECK 3 the coupling identity `[φ, H_fib] = 2 ∂_φ` (`ham_x_comm_cc`) whose derivative term `imB_le`
controls uniformly in the wall, CHECK 4–6 the wall-inside-`N` fibre estimates (`‖∂ψ‖² ≤ q`,
`‖ψ‖² ≤ q`, `‖φψ‖² ≤ 4q`), CHECK 7–9 the AM‑GM of `double_sum_amgm` and `2(½K + 9/4K) = 11/2 K ≤ 6K`
(`secHam_commForm_le`, `c = 6·K_Q`).

What the modules **cannot** certify is unchanged from §9: the one-particle symbol only.  In
particular the *core* obligations — `N` itself essentially self-adjoint on the Hermite /
Gauss-polynomial core, and `dΓ(H₁)` essentially self-adjoint on the **lifted** nested core — are
Hilbert-space statements proved in Lean and are **not** implied by the symbolic checks nor by the
one-particle `esa_on_core`.  `CONSOLIDATED_PLAN.md` §D6b records the two-level obligation for the
specialist.

## 7. Residuals, stale citations and doc repairs

1. `DESIGN_COMPARISON_N_20260915.md` §7 rows **NS, Lagrangian** (`lagRedOuterN_esa`) and
   **NS, Eulerian (squared)** (`nsRedOuterN_esa`) name declarations that **do not exist**
   anywhere in the tree (the names occur only in that note).  The realized statements for those
   rows are `BookProof.NsFullLagrangian.lagFullOuterN_esa` (Lagrangian, `c = 0`) and
   `BookProof.NsOneBody.spHam_esa_farisLavine` + `nsSpDGamma_esa_farisLavine` +
   `BookProof.NsOuterFock.nsOuterFock_esa_farisLavine` (Eulerian: one body, `dΓ` lift, outer
   Fock).  The note's *design* content stands — only the names need updating.
2. `BookProof/ChapterFarisLavineOnly.lean` §"What is proved" cites `SqFamily.fl_certificate`; no
   such declaration exists.  The certificate is `SqFamily.esa_farisLavine`.  (Fixed in this
   commit.)
3. `../unfer/docs/qg_starobinsky_vielbein_hamiltonian.cdb` — **repaired 2026‑09‑18** (§6.3): four
   defects fixed (the `@()` name mis-resolution that aborted it, the missing `expand`/`expand_power`
   steps, the `pi_psi`/`pi_psi_check` mismatch the Rust test extracts by name, and a `unwrap` that
   collapsed the expanded action to its first term).  The module runs clean, its checks reduce to
   zero and its Rust test passes on a replay of the extraction.  Recorded in
   `../unfer/docs/VERIFY_QG_STAROBINSKY_VIELBEIN.md` — not a gap in `timepiece`.
4. The `dΓ` and `ℓ²`-sector spellings of the lift (§1) should be stated once in
   `CONSOLIDATED_PLAN.md` as the same object, so that a future chapter does not "discover" a
   second second-quantization convention.
5. The B4/B5 rank-one degeneracy of the Lagrangian substitution is the reason the Lagrangian
   determinant is carried as an independent scalar mode; the `lagFullOuterN_esa` certificate is
   consistent with this (it does not eliminate `F`), but any *future* "reduced" Lagrangian
   comparison must respect it.

---

## 8. The comparison operator `N`, verbatim (what each proof consumes)

Taken from the **definitions**, not from the doc-comments.  All three theories use the same
building block on a parcel family, so it is stated once:

```lean
-- BookProof/ChapterQgHermiteOscillatorEsa.lean
def harmW (x : Vd d) : ℝ := ‖x‖ ^ 2 / 4
def harmCore : (polyGaussCore (d := d)) →ₗ[ℂ] L2d d :=
  hamCore harmW continuous_harmW expBounded_harmW
-- BookProof/ChapterQgOuterFockFarisLavine/Part2.lean
def harmFried (d : ℕ) : Comparison (L2d d) :=
  friedrichsComparison (harmPosSym d) polyGaussCore_dense
-- BookProof/ChapterSqSumOuterFamily.lean
def SqFamily.secData (n : ℕ) : CoreData (L2d (F.dim n)) where
  C := harmFried (F.dim n)        -- <-- THE COMPARISON CONSUMED
def SqFamily.flK : ℝ := 3 / 2 * F.km + 4 * (F.a * F.b)   -- relative-bound constant
def SqFamily.flc : ℝ := F.km / 2 + 2 * (F.a * F.b)       -- commutator constant c
```

so a parcel-family FL statement is essential self-adjointness in the domain of

    N = dsFibOp (fun n => harmFried (F.dim n))   =   ⊕ₙ Friedrichs(−Δ_{ℝ^{dim n}} + ‖x‖²/4).

| family | `dim n` | `km` | `a` | `b` | `c = km/2 + 2ab` | where |
| :-- | :-- | :-- | :-- | :-- | :-- | :-- |
| NS, gauge-fixed parcels | `18n` | `1` | `7B` | `6B` | **`½ + 84B²`** | `ChapterNsOuterFockFarisLavine/Part2` (`nsFamily`, `nsOuterFock_esa_farisLavine`) |
| QYM, gauge-fixed parcels | `99n` | `24` | `990B` | `1040B` | **`12 + 2 059 200B²`** | `ChapterYangMillsOuterFockFL/Part2` (`ymFamily`, `ymOuterFock_esa_farisLavine`) |
| QYM, one body (abelian) | `99` | `Σ_j‖κ_j‖` | `mass v` | `mass v` | **`Σ_j‖κ_j‖/2 + 2(mass v)²`** | `ChapterFarisLavineOnly` (`constFamily`), consumed by `ymAbelian_esa_farisLavine` via `sqSumOp_esa_farisLavine ymKap ymMagVec` |
| QG, `dΓ` route | `84n` | — | — | — | **hypothesis `c`**, uniform in `n` | `ChapterQgOuterFockFarisLavine/Part2` (`qgOuterFock_esa_farisLavine`), instantiated by `qgOuterFock_esa_farisLavine_full` |

**QG's physical comparison** — the wall sits *inside* `N`, with the mode shift `σ_a`:

```lean
-- BookProof/ChapterScalaronFiberFL/Part2.lean
def WallPot.pot : ℝ → ℝ := fun x => x ^ 2 / 4 + (W.V x + s)
def WallPot.ham : ccDomain ℝ →ₗ[ℂ] L2R := wallHam (W.pot s) (W.pot_smooth s)
def WallPot.comparison : Comparison L2R := friedrichsComparison (W.posSym s hs) ccDomain_dense
-- BookProof/ChapterScalaronOuterFockFL/Part1.lean
def fibCompar (a : ι) : Comparison L2R := W.comparison (Q.sig a) (Q.sig_nonneg a)
def secN : Comparison (Sec ι) := dsComparison (fibCompar W Q)
-- Part4.lean
theorem secHam_essentiallySelfAdjointOn :
    EssentiallySelfAdjointOn (secN W Q).dom (secData W Q).ext := … (c := 6 * Q.K)
```

    N = ⊕_{a : ι} Friedrichs(−d²/dφ² + φ²/4 + V(φ) + σ_a),        c = 6·K_Q

The one `N` serves the fibre/scalaron-band model and the three full models: the vielbein+scalaron
(`qgFullModes g`, κ = 855 + \|g\|, band 36), the Fourier-eliminated one (`qgElimFullModes g`,
κ = 513 + \|g\|, band 9) and the finite lattice instance.  The physical instance is
`V = starobinskyV M α` — the full exponential, no Taylor expansion (`starobinskyWall M α hα`,
`starobinskyWall_esa`); the relative-bound constant is `K = 1 + 3·K_Q` and is a statement about the
vielbein matrices, not about `V` (§5, rule R3).

**NS's own comparison operators** (§2.1/§2.3):

| NS leg | `N` | `c` |
| :-- | :-- | :-- |
| one body, operator of record `H_sp = ½Σπ² + ½Σ(form)²` | `spFried ν k = Friedrichs(spHam)` (self) | `0` |
| its `dΓ` lift | `nsSpDGammaFried` = `Friedrichs(dΓ(H_sp))` (self) | `0` |
| full Eulerian / Lagrangian parcels (auxiliary `weylOp`) | lifted Friedrichs extension of `weylOp` (self) | `0` |
| **the mainstream NS Hamiltonian `H_NS = ½Σ(πF + Fπ)`** | *no self-comparison exists* (not bounded below) — Leray energy `N_E = 1 + ‖u‖²` | by `commForm_kvn_energy_bound` |

## 9. Why these are the intended Hamiltonians, and how they sit on the nested space

| theory | the operator the FL proof runs on (shape) | proved identification with the intended physics | nested-space realization | symbolic / arithmetic evidence |
| :-- | :-- | :-- | :-- | :-- |
| **NS** one body (**auxiliary** comparison, not the NS Hamiltonian — see §2.1 correction; the Hamiltonian is the Koopman form `kvnPoly`/`nsKoopmanOp`, `i[H,u_k]=2F_k`) | `spHam = weylOp (spPi Φ) (spField Φ ν k)` = `½ Σ_{m<6} π_m² + ½ Σ_{r<7} (mulOp Φ_r)²` | `spHam_eq_visc_add_advect` (advection kept **squared**, three squares `½((k·u)u_i)²`, no momentum term), `spHam_quadForm_split` | `dΓ(H_sp)` = `dGammaOp (nsSpCol …)`; `redHam_eq_sum_parcel`, `nsRedFullFockHam_sector_sum_parcel`, `weylOpDom_block_sum`, `nsSpDGamma_number_conserving` | `ns_qg_fourier_elimination.cdb` C1–C5 (the Eulerian residual and divergence are the substituted ones); `scripts/check_hamiltonian_identities.py` NS block |
| **NS** full Eulerian / Lagrangian | `nsSectorHam` / `lagSectorHam` = `weylOp … = ½Σπ² + ½Σ(constraint form)²` | `nsResPoly_not_affine` (Piola term is genuinely quadratic), `volumePoly_not_quadratic` + `detPoly_eval_testPt` (`det F = 1` is cubic, `t³ − 1` on the isotropic line) | `dsOp`/`dsFibOp` on `lp (fun n => L²(ℝ^{21n})) 2` (`nsFockSpace = lp (fun n => L2d (n*21)) 2`, `ChapterNavierStokesFullEulerianFock:277`; the `18n` belongs to the **reduced / gauge-fixed** family `nsFamily`, `dim := n*18`), `lagFockSpace = lp (fun n => L²(ℝ^{36n})) 2`; number conserving (`nsFullFockHam_number_conserving`, `lagFullFockHam_number_conserving`) | `ns_qg_fourier_elimination.cdb` A1–E3 (incl. B4/B5: the rank-one degeneracy that forbids eliminating `F`) |
| **QYM** one body | `ymHamiltonian (coreRepPoly 99) 0 = sqSumOp ymKap ymMagVec` = `½ Σ_j κ_j π_j² + ½ Σ_m B_m²` | `ymAbelian_eq_sqSumOp` (`= ` by construction), `gramQ_ymMagVec` (the Gram of the 24 magnetic forms) | `dΓ(H₁)` (`ChapterFockSecondQuantization`, `ChapterQymTimeIndependentFlow`); `ym_fock_friedrichs_extension` for the non-abelian direct-Friedrichs route | `yang_mills_hamiltonian.cdb`: `L_y = ½π² − ½B²` → Legendre → `H_final = ½π² + ½B²`, plus the 3D ε identity numerically |
| **QYM** parcels | `ymFamily.secHam` (99 coordinates per parcel) | `ymFamily_vv` (the forms are the magnetic, Gauss and derivative-tie forms), `ym_interaction_nontrivial` | `outerHam`/`outerCore` on `⊕ₙ L²(ℝ^{99n})`, `ymOuterHam_symmetricOn`; number conserving | same module (the same magnetic forms appear as `B_{i a}`) |
| **QG** | `secHam (n) = Σ_{a,b} a†_a h_{ab} a_b` with `h_{ab} = δ_{ab}(−d²/dφ² + φ²/4 + V(φ) + σ_b) + A_{ab}·1 + B_{ab}·φ` | `secHam_eq_sum_oneParticle`, `secHam_single`, `secHam_matrix_element` — one-particle matrix elements, *no outer vertex*; `starobinskyV_not_quadratic` (the wall is not a degree-≤2 polynomial) | `Sec ι = ℓ²(ι ; L²(ℝ))`; `secHam_number_conserving`, `qgFull_number_conserving` (so no lattice/occupation cut-off is needed) | `qg_gauge_fixed_hamiltonian.cdb` (book.tex 8190, coefficients `1/16, −1/24, ½, ⅓`), `qg_starobinsky_vielbein_hamiltonian.cdb` (`H_final_st = (M²/2)ψ·(8190) + U(ψ)e`, `base_limit_check`), `qg_densitized_hamiltonian.cdb` (`1/16ε S² − 1/24ε P²` is flat after densitization), `qg_starobinsky_einstein_frame.cdb` (`U(ψ)/ψ²` at `ψ = e^{√(2/3)φ/M}` is `starobinskyV`; the kernel above equals the plan's stated inner operator) |

**The one thing the Cadabra modules cannot certify, stated plainly.**  A `.cdb` module is a
symbolic/algebraic engine on *classical* expressions: it can certify the one-particle symbol — that
the expression which enters `h` really is the intended physical Hamiltonian (metric-splitting,
Legendre, substitution chain and coefficients) — and nothing else.  The **nested** structure (that
the outer operator is `Σ_{i,j} h_{ij} C†(e_i) A(e_j) = dΓ(h)`, that no outer vertex is added, that
the particle number is conserved) is a Hilbert-space statement and is certified **in Lean**, by the
identification theorems named in the last-but-one column: `dGammaOp`/`dsOp`/`dsFibOp` for the lift,
`secHam_eq_sum_oneParticle` for the QG kernel, `redHam_eq_sum_parcel` for the NS parcel identity,
and `*_number_conserving` for the sector preservation.  The two halves are exactly the convention
the plan states once (§“The final-Hamiltonian convention”): the **inner** matrix elements carry all
the nonlinearity (quartic, wall, interaction), and the **outer** operator is quadratic in the
ladders for any `h`.

**Inner-operator audits, sector by sector (2026‑09‑21).**  The one-particle operators of §9's table
have been checked against the plan *definition by definition* (not from the doc-comments):

* **QG** — `h_{ab} = δ_{ab}(−d²/dφ² + φ²/4 + V(φ) + σ_b) + A_{ab}·1 + B_{ab}·φ` with
  `V = starobinskyV`, `A = gGram`, `B = gCoupling g`: `oneParticleOp` / `secHam` /
  `qgFullModes` match the plan term for term, and the Einstein-frame closed form of `V` is now
  derived (not asserted) in `../unfer/docs/qg_starobinsky_einstein_frame.cdb`;
  `../unfer/docs/VERIFY_QG_STAROBINSKY_EINSTEIN_FRAME.md`.
* **NS** — reduced `spHam` (6 coordinates, 7 forms), full `nsSectorHam` (21 coordinates, 12 momenta,
  19 forms) with `nsFullFockHam = dΓ(H₁)` on `L²(ℝ^{21n})`, the mainstream `kvnPoly` with
  `F_i = −νλ_iu_i + B_i(u,u)`, and the full residue `nsResPoly`/`divPoly`: all match the plan;
  the plan should just say *which* one-particle model it means at each occurrence
  (`H_sp` = reduced, `H₁` = `nsSectorHam … 1`).
* **QYM** — `ymHamiltonian = ½Σπ² + ½ΣB²` (24 momenta, 24 magnetic forms), the abelian
  `ymAbelian_eq_sqSumOp` identification, and the `99n` parcel family: all match the plan,
  including the `+½Σ` sign convention.

The NS/QYM tables are in `../unfer/docs/VERIFY_FARIS_LAVINE_N.md` §“Audit of the NS and QYM inner
one-particle operators”.

**Re-certified on the current tree (2026‑09‑18).**  All seven `../unfer/docs/*.cdb` modules re-run
with the term-count epilogue: `exit 0`, no tracebacks, for every one; the two values that repair
work touched are in place (`qg_gauge_fixed_hamiltonian.cdb`: `pi_derived` = 132 summands;
`qg_starobinsky_vielbein_hamiltonian.cdb`: `ex1_st` = 121 summands).  The full module-level
truncation audit is `../unfer/docs/VERIFY_CDB_TRUNCATION_AUDIT.md` and §7.3 below.

---

### Reproduction

```
# symbolic (Cadabra2 2.5.14, via the ../unfer nix flake)
export LD_LIBRARY_PATH="$(ls -d /nix/store/*gcc-15*/lib | head -1):$LD_LIBRARY_PATH"
C2=/nix/store/rpdv12r5grn47rixhdiydxq675f8h5i0-cadabra2-2.5.14-p1/bin/cadabra2-cli
$C2 -q -n ../unfer/docs/ns_qg_fourier_elimination.cdb
$C2 -q -n ../unfer/docs/yang_mills_hamiltonian.cdb
$C2 -q -n ../unfer/docs/qg_gauge_fixed_hamiltonian.cdb

# arithmetic (no dependencies)
python3 scripts/check_hamiltonian_identities.py
```
