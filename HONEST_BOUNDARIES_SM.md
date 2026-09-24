# The Standard-Model honest boundaries: what is now a Lean theorem, and what is not

**Current state of record** (updated 2026-09-23 after the closure wave, the book-BRST wave,
and the accounting identity of §2026-09-23d in `CONSOLIDATED_PLAN.md`).  Every theorem
cited here is intended to compile inside `lake build BookProof` with no `sorry` and no
`axiom` beyond the usual `propext`, `Classical.choice`, `Quot.sound`; the axiom audits are
`Work/SmStandardModelAudit.lean`, `Work/SmHonestBoundariesAudit.lean`, and
`Work/BookBrstAudit.lean`, and (for L2, closed 2026-09-23g) `Work/SmComparisonEsaAudit.lean`.  Historical boundary quotes that the tree has since *closed*
are kept only as section titles of the form *“…was open”* — the live list is **§L** below.

> **Supersession.**  Earlier drafts of this file left §1’s “Still open” line
> (*continuum CAR*, *gauge connection inside `D`*, *ghost/BRST sector*) standing after
> §5 had already closed all three.  Those three items are **not open**.  §5.5’s
> “everything of §§1–4” was likewise wrong for them.  This rewrite reconciles the ledger
> with the modules.

---

## §L. Still open, and explicitly not claimed

This is the only live “not claimed” list for the SM wave.  Everything else in the file is
either a closed boundary (theorem now in tree) or a historical quote.

| # | Boundary | Why it stays open |
| :-- | :-- | :-- |
| L1 | **Majorana masses and the see-saw** | `book.tex` works *“in the absence of Majorana masses”*; only the Dirac-type Yukawa `M_ν φ ν_R` and its biunitary/PMNS algebra are in `h`. |
| L2 | **Unconditional bosonic ESA** `sm_h_esa` — **closed (2026-09-23g)** | Fermionic half: `sm_fermi_fl_i/ii/iii`, `sm_fermi_esa`.  Bosonic half: `BookProof/ChapterSmFarisLavine.lean` proves both Faris–Lavine inequalities against `N = 2h + Σ_m q_m² + c₀` (`sm_commForm_le`, `c = 1`; `sm_norm_le_shift`, `K = 1`; `smComparison` provably cannot serve, §2bis) and reduces `sm_h_esa` to essential self-adjointness of `N` on `polyGaussCore 163` (`sm_h_esa_of_comparison_esa`).  That former hypothesis — a Kato-type statement for a coupled quartic Schrödinger operator in 163 variables, which Faris–Lavine structurally cannot supply — is now a **theorem**: `SmComparisonEsa.smFlN_esa` (every `c₀ : ℝ`), via `smFlN_eq_hamCoreS` (`N = −Δ_S + W`, `W = Σ_r Φ_r² + Σ_m q_m² + c₀`), `HermiteGraphApprox.hamCoreS_esa` (polynomial-core transfer), and `DegKatoEsa.ccHamS_esa` (Kato's theorem for `−Δ_S + W`, `W ≥ 1` smooth, on `C_c^∞`).  Hence **`SmComparisonEsa.sm_h_esa`** is proved with no hypothesis beyond `P : SmParams`.  Axioms: `propext`, `Classical.choice`, `Quot.sound` only (`Work/SmComparisonEsaAudit.lean`). |
| L3 | **Continuum spectrum / mass gap** of the bosonic `dΓ(h)`; QCD confinement | Spectral claims are only the finite-mode fermionic spectrum/gap and the one-particle relativistic energies. |
| L4 | **EWSB as dynamics**; measured CKM/PMNS parameters | Statics only (vacuum manifold, Goldstone flatness, radial curvature, mass form of broken generators). No expansion of `H` around the vacuum, no `W/Z` mass value, no Wolfenstein/PMNS angles, phases, ordering or absolute masses — only unitarity identities and `yukawa_entry_bound`. |
| L5 | **Size of the BRST cohomology** `ker Ω / im Ω` | The quotient is defined and well defined (`exactStates_le_physicalStates`); its dimension is not claimed. |
| L6 | **Continuum local Gauss law** | The local gauge algebra is a finite-dimensional Lie algebra with derivations `∂_μ` (book’s totally antisymmetric `SU(N)` structure constants); Gauss law closes in that algebra, not at every point of continuum space. |
| L7 | **Faddeev–Popov determinant (SM/book formalism)** | The book’s BRST formalism uses none and none is constructed. (The separate QYM abelian FP sector is `ChapterYangMillsGhostSector.lean`, not part of the SM `h`/`N` record.) |
| L8 | **Continuum CAR beyond the Fock representation** | `ChapterSmCarContinuum` builds the Fock rep on the vacuum over `ℓ²(ℕ)` / arbitrary separable one-particle space; nothing about inequivalent representations, the C\*-completion, or a Hamiltonian on that space. |
| L9 | **Gauge-field dynamics / continuum limit of `D`** | Connection in `ChapterSmGaugeConnection` is a constant collective-coordinate background: `D_j = i(k_j + A_j)` carries `ik_j`, not an unbounded derivative, so that module’s `[D_j, D_l]` sees only the non-abelian part of `F` (`∂A = 0` by construction). The **full** `F_{μν} = ∂_μ A_ν − ∂_ν A_μ + [A_μ, A_ν]` (curl **and** `f^{abc}AA`) is in the tree as `smMagG`/`smMagW`/`smMagB` — but no gauge-field dynamics (time evolution of `A`) and no continuum limit of `D` on `L²(ℝ³)` is claimed. **Route note:** the curl/continuum half is reachable by the **momentum-space convolution already used for NS and QG** (`fourier_mul_eq_convolution`, `fourier_advection_convolution` in `ChapterNsAdvectionConvolution` — products with spatial derivatives become convolutions with weight `2π i ⟨q,m⟩`); this device is **not** part of QYM (QYM proofs do not need it) and is only invoked here for proofs of this type. |
| L10 | **Finite mode set for the SM BRST multiplet** | One plane-wave matter multiplet + twelve ghosts (and the book’s `N`-colour realization); not a full continuum field BRST. |
| L11 | **QG accounting identity in the SM form** | QG 3D reduction is **non-ADM** (`book.tex` ~8226–8244): `v^μ = δ^μ_0`, ghosts constant in the timepiece, charge with 4D functional form; frame fermion `{G, i b_j A_0^j}` is **not** covered by `bookGfTerm_eq_zero_of_Afield0`. |

---

# 0. Faris–Lavine Corollary 1.1: where it already lived

The criterion itself is **proved**, not assumed, in

* `BookProof/ChapterFarisLavineCore.lean` — `BookProof.FarisLavine`:
  `essentiallySelfAdjointOn_of_farisLavine` (Theorem 1 of Faris–Lavine 1974) and
  **`essentiallySelfAdjointOn_core_of_farisLavine`** (Corollary 1.1), with
  `essentiallySelfAdjointOn_restrict_of_graph_core`;
* split copies `ChapterFarisLavineCore/Part1.lean`, `Part2.lean`;
* users elsewhere: `ChapterNavierStokesFlow.lean`, `ChapterNavierStokesAffineFiberEsa*.lean`,
  `ChapterNavierStokesDiffFarisLavine*.lean`, `ChapterNavierStokesHermiteFarisLavine*.lean`,
  `ChapterNavierStokesFockFarisLavine.lean`, `ChapterNavierStokesIkebeKato.lean`,
  `ChapterNavierStokesMomentumEsa.lean`, `ChapterNavierStokesFockManyMode.lean`.

What was missing for the SM was never the criterion; it was the **hypotheses** for the SM
operators and the algebra the fermionic operators live on — both now supplied for the
fermionic sector and (Cadabra-certified) for the bosonic algebraic content.

---

# 1. Closed: finite CAR, Dirac/Yukawa, spinor structure

**Was:** *“The Dirac and Yukawa operators are not formalized (they need the CAR/Grassmann
algebra) — only the mixing algebra they rest on is.”*  
**Now:** formalized for a finite mode set.

* `BookProof/ChapterSmCarAlgebra.lean` — `FermiFock n = ℓ²(Finset (Fin n))`, Jordan–Wigner
  ladders, the four CAR relations, adjointness, contractivity, occupation number,
  `fermiBilin`, `fermiEnergy_occ`, **`fermi_mass_gap`**.
* `BookProof/ChapterSmDiracYukawa.lean` — `smDirac`, `smYukawa`, `smFermiHam`;
  `isMixing_mul`, **`yukawa_entry_bound`**; Fermionic FL **`sm_fermi_fl_i/ii/iii`**,
  **`sm_fermi_esa`**.
* `BookProof/ChapterSmDiracSpinor.lean` — `diracOneParticle` Hermitian, mass-shell
  `H² = (k² + m₁² + m₂²)`, energies `±√(k² + m₁² + m₂²)`, `diracFieldHam`,
  **`dirac_field_esa`**.

*Module-header note in `ChapterSmCarAlgebra` still says continuum CAR / spinor / ghost are
“not built here” — true **of that file**; the boundary is closed by the modules of §5.*

---

# 2. Closed for the fermionic sector and (since 2026-09-23g) for the bosonic sector (L2)

**Was:** *“The three Faris–Lavine hypotheses of §D6b-SM.3 remain symbolic.”*

**Now Lean theorems for the fermionic sector** with
`N = Σ_i ω_i a†_i a_i + c₀` (`ω_i ≥ 0`, `c₀ ≥ 1`):

| hypothesis | theorem | constant |
| :-- | :-- | :-- |
| (i) `±h ≤ c₁N` | `sm_fermi_fl_i` | `c₁ = Σ_{i,j} ‖h_{ij}‖` |
| (ii) `|⟨ψ,[h,N]ψ⟩| ≤ c₂⟨ψ,Nψ⟩` | `sm_fermi_fl_ii` | `c₂ = 2c₁Ω` |
| (iii) `|⟨ψ,[N,[N,h]]ψ⟩| ≤ c₃⟨ψ,N²ψ⟩` | `sm_fermi_fl_iii` | `c₃ = 4c₁Ω²` |

side conditions: `smFermiN_symmetricOn`, `sm_fermi_N_ge_one`, `sm_fermi_N_add_one_surjective`;
conclusion **`sm_fermi_esa`**; spinor instance `dirac_field_esa`.

**Bosonic half (L2), current state.**  `BookProof/ChapterSmFarisLavine.lean` is in the tree
and `sorry`-free.  It proves the two inequalities the Lean Faris–Lavine theorems actually
consume — the form commutator bound `sm_commForm_le` (`c = 1`) and the relative bound
`sm_norm_le_shift` (`K = 1`) — and instantiates Theorem 1 / Corollary 1.1 through the new
abstract last mile `CoreData.esa_core`.  Two honest qualifications:

* the comparison operator is **not** the `smComparison` of §D6b-SM.2 but
  `N = 2h + Σ_m q_m² + c₀` (see §2bis for why the quartic uncoupled `N₀` cannot work);
* the conclusion is **conditional**: `sm_h_esa_of_graph_core` assumes
  `IsGraphCore (smFlComparison P hc₀) (polyGaussCore 163)`, and `isGraphCore_of_esa` turns
  that into the plainer `sm_h_esa_of_comparison_esa`, which assumes only
  `EssentiallySelfAdjointOn (polyGaussCore 163) (smFlN P c₀)`.  Both are named hypotheses,
  never axioms.  The unconditional `sm_h_esa` was therefore
  not claimed by that module alone.

**Update 2026-09-23g — the hypothesis is discharged.**  `BookProof/ChapterSmComparisonEsa.lean`
proves `smFlN_esa : EssentiallySelfAdjointOn (polyGaussCore 163) (smFlN P c₀)` for every
`c₀ : ℝ` and hence the unconditional **`sm_h_esa P`**.  The Kato-type input is supplied by

* `BookProof/ChapterDegKatoEsa.lean` — `ccHamS_esa`: `−Δ_S + W` (kinetic part on any
  coordinate subset `S`, `W` smooth, `W ≥ 1`) is essentially self-adjoint on `C_c^∞(ℝᵈ)`
  (mollifier + cut-off energy argument; no elliptic regularity);
* `BookProof/ChapterHermiteGraphApprox.lean` with `BookProof/ChapterHermiteLadderOrder.lean`
  — `hamCoreS_esa`: for a real polynomial `W ≥ 1`, every `C_c^∞` vector is a graph-norm limit
  of Gauss–polynomial vectors, so essential self-adjointness transfers to `polyGaussCore`;
* `smFlN_eq_hamCoreS` — on the core `N = −Δ_S + W` with `S` the 40 momentum coordinates and
  `W = Σ_r Φ_r² + Σ_m q_m² + c₀ ≥ 1` for `c₀ ≥ 1`; other `c₀` by a bounded shift.

No named hypothesis and no axiom remains on this route; `#print axioms` reports only
`propext`, `Classical.choice`, `Quot.sound`.

Not needed for the Friedrichs route (`sm_friedrichs_extension`,
`sm_dGamma_friedrichs_extension`).  The Cadabra module
`../unfer/docs/faris_lavine_n_sm.cdb` certifies *algebraic shape* (CHECK 1–28 + PART F) at
exit 0; a shape check is not the inequality, and the Lean FL theorems consume symmetry +
positivity + surjectivity of `N+1` + the form commutator, not the double commutator (iii).

---

# 2bis. Why `smComparison` cannot be the Faris–Lavine comparison operator

Write `h = ½T + V_h` and `N = T + V_N + c₀` with `T = Σ_m π_m²`.  The commutator is first
order,

```
i[h, N] = Σ_m (π_m G_m + G_m π_m),   G = ∇(½V_N − V_h),
```

so `± i[h,N] ≤ c N` forces the pointwise bound `|G|² ≤ c²(V_N + c₀)`: test the form on a
wave packet `e^{iξ·x}φ` concentrated at a point and optimize in `ξ` (the optimum is at
`ξ = G/c`, not at `ξ = G`).  For `smComparison`, `V_N = Σ_m q_m⁴ + …` is quartic and `G` is
cubic.  Along a single gluon direction `G^1_1 = R` the totally antisymmetric structure
constants kill the non-abelian magnetic energy and `φ = 0` kills the covariant Higgs
derivative, so `∇V_h = 0` there and the requirement reads `4R⁶ ≤ c²R⁴` — false for large
`R`.  The obstruction is caused by the quartic confinement of `N` itself and is already
present for the free Hamiltonian; it is not an artefact of the interaction.

The cure — the one Faris and Lavine use in their own application — is to let the comparison
operator contain the Hamiltonian, so that `∇V_h` cancels: with `V_N = 2V_h + Σ_m q_m²` one
gets `G = ½∇(Σ_m q_m²)`, which is linear, and both inequalities hold with absolute
constants.  That is `smFlN`.  The price is that graph-core-ness of `N` is no longer free.

That price has now been paid (2026-09-23g): Faris–Lavine indeed cannot produce
essential self-adjointness of `N` — any admissible `N` contains `2V_h` and is a coupled
quartic Schrödinger operator in 163 variables — so it is supplied by an independent
Kato-type theorem, `DegKatoEsa.ccHamS_esa`, transferred to the Gauss–polynomial core by
`HermiteGraphApprox.hamCoreS_esa`.  The result is `SmComparisonEsa.smFlN_esa` and the
unconditional `SmComparisonEsa.sm_h_esa`.

---

# 3. Closed: derivative-coordinate summands of `N₀`

**Was:** *“The derivative-coordinate summands of `N₀` lie outside the ESA chain.”*

**Now closed** in `BookProof/ChapterSmComparisonFull.lean`:
`smoothPotential_essentiallySelfAdjoint` / **`deriv_coordinate_esa`** ⇒ each derivative
coordinate is an `EsaOp`; **`sm_N_full_esa`** (all 160 summands),
`sm_N_full_stone_flow`, **`smFullChain_length = 1+36+3+120 = 160`**.
Framework: `ChapterTensorSumChain.lean`.

---

# 4. Still open in part: spectrum, gap, dynamics, measured parameters (L3, L4)

**Addressed where the content is a theorem:**

* Fermionic spectrum/gap: `fermiEnergy_occ`, **`fermi_mass_gap`**;
  one-particle relativistic energies: `diracOneParticle_eigenvalue_sq`.
* EWSB **statics**: `ChapterSmHiggsVacuum.lean` — `higgsV_eq_min_iff`,
  `higgs_goldstone`, `higgs_radial`, `gaugeMassForm_eq_zero_iff`.

**Still open (L3, L4):** continuum spectrum/mass gap of bosonic `dΓ(h)`; QCD confinement;
EWSB as dynamics; any measured CKM/PMNS parameter beyond unitarity + entry bound.

---

# 5. The closure wave: the three §1 boundaries that are now theorems

The old §1 boundary line was: *“Still open: the continuum CAR algebra over an
infinite-dimensional one-particle space, the gauge connection inside `D`, the ghost/BRST
sector, and Majorana masses / the see-saw.”*  
The **first three are closed**; only **Majorana / see-saw (L1)** remains from that sentence.

## 5.1 Closed: continuum CAR — `BookProof/ChapterSmCarContinuum.lean`

Mode set `ℕ`, one-particle space `ℓ²(ℕ)` (any separable one-particle space via a Hilbert
basis), Fock space `CFock = ℓ²(Finset ℕ)`.

* `cAnn`/`cCre`, four CAR relations, adjointness;
* smeared `cCreS f`/`cAnnS f` for arbitrary `f ∈ ℓ²(ℕ)`;
  **`car_smeared`**: `{a(f), a†(g)} = ⟪f, g⟫`; `norm_cCreS_le`: `‖a†(f)‖ ≤ ‖f‖`;
* `oneParticleIsometry`, `norm_cCreS_eq`;
* **`car_hilbert`** over an arbitrary separable one-particle Hilbert space.

*Still open here (L8):* Fock representation on the vacuum only; no inequivalent
representations, no C\*-completion claim, no Hamiltonian on this space.

## 5.2 Closed: gauge connection inside `D` — `BookProof/ChapterSmGaugeConnection.lean`

Minimal coupling in the constant collective-coordinate background:
`D_j = i(k_j + A_j)`, `A_j = g Σ_a A^a_j T_a`.

* `conn_conjTranspose`, `covD_conjTranspose`, `covD_zero_coupling`;
* **`covD_commutator`** — non-abelian field strength (operator form of
  `W^j_{μν} = −(i/g) tr([D_μ,D_ν]τ^j)` / the `g_s f^{abc} G^b_j G^c_k` term);
* `covD_conj`, `conn_gauge_transform` — gauge covariance;
* `diracGaugeMat`, `diracGaugeField`, **`dirac_gauge_field_esa`** — second quantization
  and ESA through the Fermionic FL hypotheses.

*Still open here (L9):* constant background (`ik_j`, not ∂), so this module’s
`[D_j, D_l]` sees only the non-abelian part of `F` (`∂A = 0`); the full
`F = ∂A − ∂A + [A,A]` lives in `smMagG`/`smMagW`/`smMagB`; no gauge-field
dynamics, no continuum limit of `D`. **Route note:** the curl/continuum half is
reachable by the momentum-space convolution already used for NS and QG
(`ChapterNsAdvectionConvolution.fourier_mul_eq_convolution` /
`fourier_advection_convolution`) — not a QYM device, only invoked for proofs
of this type.

## 5.3 Closed: ghost / BRST sector — `ChapterSmBrstGhost.lean` + `ChapterSmGaugeRepresentation.lean`

* `smStruct f₃` with **`smStruct_antisymm`**, **`smStruct_jacobi`**;
* twelve ghosts on the CAR algebra, `smGhostCAR`, `ghostNumber`;
* **`fermiBilin_lie`** ⇒ Gauss generators close; **`brstCharge_nilpotent`**,
  **`smBrstCharge_nilpotent`**;
* `ChapterSmGaugeRepresentation`: `su2gen_closes`, `smGen_closes`,
  **`sm_brst_nilpotent_rep`** on the 18-mode Fock space (6 matter + 12 ghosts), with `su(3)`
  antisymmetry/Jacobi **derived** from the two defining relations
  (`BookProof.YangMillsSU3`).

*Still open here (L5, L7, L10):* cohomology size; no Faddeev–Popov determinant; finite
mode set.

## 5.3bis Closed: BRST **as `book.tex` defines it** — `ChapterBookBrstYangMills`,
`ChapterBookBrstGaugeFixing`, `ChapterBookBrstInstances`

Book density
`Ω = π^μ_a ∂_μψ†_a − π^μ_a f_{abc} A_{μb} ψ†_c − (i/2) f_{abc} ψ†_aψ†_bψ_c`
with `[A,π] = i δ`, `{ψ,ψ†} = δ`:

* **`bookCCR`**, **`bookGhostCar`**, **`bookOmega`**, **`gaussGen_bracket`** (Gauss law
  derived), **`bookOmega_nilpotent`**, `bookOmega_eq_brstCharge`;
* gauge-fixing fermion `Ψ = i ψ_a A_{0a}`: **`bookGfTerm_eq`**, **`bookGfTerm_brst_closed`**;
* **Accounting identity (h, N unchanged):** **`gfFermion_eq_zero`**,
  **`bookGfFermion_eq_zero_of_Afield0`**, **`bookGfTerm_eq_zero_of_Afield0`**, instances
  **`su2_bookGfTerm_eq_zero_of_Afield0`**, **`sm_bookGfTerm_eq_zero_of_Afield0`**
  (Cadabra CHECK 29, 30a–c, exit 0); QG form **not** asserted (L11);
* cohomology `brstCohomology` well defined; observables via `brstCharge_comm_of_comm`,
  `su2_casimir_bookOmega_comm`;
* `innerDeriv_leibniz`, `su2BookAlgebra`, `smBookAlgebra`,
  **`sm_bookOmega_nilpotent`**, `su2_gaussGenPoly_ne_zero`.

*Still open here (L5–L7):* continuum local Gauss law; no FP determinant; cohomology size.

## 5.4 From the original §1 sentence, only this remains open

**Majorana masses and the see-saw (L1)** — plus everything in **§L** (L3–L11; L2 was closed on 2026-09-23g and is kept in the table
with its closing theorems).

## 5.5 Accounting identity (2026-09-23d): no extra gauge-fixing/ghost summand in `h` or `N`

**Answered.**  On `A₀ = 0` the whole BRST-exact term `{Ω, Ψ}` vanishes; `h` and `N` are
structurally complete without an extra summand.

* Lean: `gfFermion_eq_zero`, `bookGfFermion_eq_zero_of_Afield0`,
  **`bookGfTerm_eq_zero_of_Afield0`** (`ChapterBookBrstGaugeFixing.lean` §2b);
  **`su2_bookGfTerm_eq_zero_of_Afield0`**, **`sm_bookGfTerm_eq_zero_of_Afield0`**
  (`ChapterBookBrstInstances.lean` §5); audit `Work/BookBrstAudit.lean` §4b.
* Cadabra: PART F CHECK 29, 30a–c of `../unfer/docs/faris_lavine_n_sm.cdb`, exit 0,
  trailing `ALL SM ACCOUNTING IDENTITY CHECKS DONE (QYM spatial-only; QG non-ADM)`
  (`VERIFY_SM_FARIS_LAVINE.md`).
* **QYM:** Weyl gauge may use only spatial components
  (`ChapterQymTimeIndependentFlow.lean`).
* **QG non-ADM (L11):** `book.tex` ~8226–8244 — `v^μ = δ^μ_0`, ghosts constant in the
  timepiece, charge with 4D functional form; frame fermion `{G, i b_j A_0^j}` is **not**
  covered by the `A₀ = 0` vanishing
  (`ChapterQuantumGravityBrstCharge.lean`, `ChapterQuantumGravity3DGauge.lean`,
  `Book/Starobinsky.lean`).

*Still open here:* does **not** close L1–L4, L5–L10.

---

## Module map (closed boundaries → files)

| Boundary | Modules |
| :-- | :-- |
| Finite CAR / Dirac / Yukawa / spinor | `ChapterSmCarAlgebra`, `ChapterSmDiracYukawa`, `ChapterSmDiracSpinor` |
| Continuum CAR | `ChapterSmCarContinuum` |
| Gauge connection in `D` | `ChapterSmGaugeConnection` |
| Ghost / BRST (abstract + rep) | `ChapterSmBrstGhost`, `ChapterSmGaugeRepresentation` |
| Book BRST + accounting identity | `ChapterBookBrstYangMills`, `ChapterBookBrstGaugeFixing`, `ChapterBookBrstInstances` |
| `N` all summands ESA | `ChapterSmComparison` (`sm_N_positive`, `sm_N_dyn_esa`), `ChapterSmComparisonFull` (`sm_N_full_esa`) |
| Fermionic FL | `ChapterSmDiracYukawa` (`sm_fermi_fl_*`, `sm_fermi_esa`) |
| Friedrichs (bosonic, independent) | `ChapterSmHamiltonian`, `ChapterSmOuterFock` |
| Cadabra certificate (h, N, FL algebra, PART F) | `../unfer/docs/faris_lavine_n_sm.cdb`, `VERIFY_SM_FARIS_LAVINE.md` |
| Bosonic FL / L2 **closed (2026-09-23g)** | **`ChapterSmFarisLavine`** (`sm_commForm_le`, `sm_norm_le_shift`, `sm_h_esa_of_comparison_esa`) + **`ChapterSmComparisonEsa`** (`smFlN_eq_hamCoreS`, `smFlN_esa`, `sm_h_esa`), on the instrument chapters `ChapterDegSchrodingerCore`, `ChapterMollifierL2`, `ChapterConvolutionCalc`, `ChapterDegEnergyEstimate`, `ChapterDegKatoEsa`, `ChapterHermiteLadderOrder`, `ChapterHermiteGraphApprox`; audits `Work/SmFarisLavineAudit.lean`, `Work/SmComparisonEsaAudit.lean` |
