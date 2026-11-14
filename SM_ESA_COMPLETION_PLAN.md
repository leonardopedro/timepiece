# Full Standard-Model ESA: completion plan and implementation audit

Date: 2026-11-09; numerical implementation updated 2026-11-09c (§9).
Executor: LLM-Lean4-specialist for proof packets P0–P8;
`unfer` implementer for numerical/symbolic packets N0–N5. This is a source-audited
work order, not a claim that the remaining theorems are proved. No Lean compilation
is part of this planning wave. Read the 2026-11-09c SM entry in
[CONSOLIDATED_PLAN.md](CONSOLIDATED_PLAN.md) and the
[boundary ledger](HONEST_BOUNDARIES_SM.md) with this document.

This supersedes “SM refinements” as the work order and any interpretation of
`smFull_h_esa` or `smYukawa_h_esa` as already covering the complete manuscript
matter interaction. Keep their actual theorems and prior successful-build records.
The existing bosonic ESA proof is an input to reuse, not an open proof to repeat.

## External-source audit within the nested formalism (2026-11-11)

This section replaces the earlier external-source commentary. E1/E2 and P0–P8 below
remain statements about the manuscript's nested-Fock/Mehler Hamiltonian and its
Hashimoto/SIRK approximations. **E2 here denotes the intended infinite-mode SM endpoint**;
it is unrelated to the Euclidean construction packet E2 in `cftproof.md`.
Neither SM endpoint requires Wightman axioms, OS positivity or a 4D Euclidean measure.
Any comparison between these formalisms is additional work in
[cftproof.md](cftproof.md), B0–B3, and does not gate SM ESA completion.

### Source contributions and boundaries

The inspected [October submission](../OpenAI-YM-20261028/README.md),
[results/review](../YM/README.md) and
[Balaban manuscripts](../Yang--Mills-LLM-experiment/README.md) are documented with snapshot
revisions in cftproof's source audit. The first concerns pure gauge theory under a simple
Lie-algebra hypothesis; the last supplies tentative manuscript arguments. Neither
constructs this plan's full SM inner operator or proves its analytic estimates.

Correct two earlier source interpretations. `GaugeGroup` itself describes closed compact
matrix subgroups; **`IsSimple` in the theorem hypothesis**, not the base type, excludes
`SU(3) × SU(2) × U(1)` from that theorem. Likewise, complex-linear field labels and an
antilinear adjoint can describe fermionic fields. The external **ordinary locality axiom**
and pure-gauge content, rather than linearity, are what fail to supply graded locality/CAR
for SM matter. A real scalar coefficient does not make a matrix-valued operator Hermitian;
retain the P1 coefficient-adjoint and domain proofs.

The useful transferable ideas are structural:

* **Shared witnesses:** the review's `CombinedAcceptance` fixes one family, table and
  final theory across its clauses. P8 should bind one physical dictionary, inner operator,
  comparison, closure, parity/physical reduction and outer lift across all SM clauses.
* **Normalization identities:** the review separately checks common scale, action-law
  conversion and insertion normalization. Here check generator conventions, couplings,
  Higgs placement, CAR basis, constant term and normal-order contractions against the
  manuscript and implementation. Test the identities actually used by `h_SM`; no
  external free-Maxwell or Bianchi comparison substitutes for this representation proof.
* **Dependency isolation:** the Balaban diagram separates geometry, inverse estimates,
  integration and conditional laws; several analytic inputs remain not closed. Apply
  that organization to our operator/core identification, scalar graph estimate, matrix
  transfer and outer lift. A conditional transfer theorem does not discharge its estimate.
* **Verification scope:** retain axiom audits and add endpoint-type/definition provenance
  and a dated evidence manifest when proof packets land. Distinguish a successful target
  build from a dependency cache, source reading and an independent checker run.

### P4 resumption: prove the needed graph estimate, with a free finite constant

The current stopping point is §§22, 32, 38–43. Keep the QYM-first priority in
[CURRENT_WORK_ORDER.md](CURRENT_WORK_ORDER.md); do not repeat the completed P1/P2
coefficient assembly. Resume when a candidate analytic method addresses the actual
`smPotPoly P c₀` and the partial kinetic set `smS`.

Write `K = −Δ_S`, `W = smPotPoly P c₀`, `N = K + W`, and `u = pgFun p`.
The sufficient scalar packet is a finite `c ≥ 0` such that, for all polynomial-core `u`,

```text
‖K u‖ ≤ c ‖(N + I)u‖.
```

Equivalently, existence of a finite `β ≥ 0` with
`‖(W + I)u‖ ≤ β ‖(N + I)u‖` supplies `PotSelfBound` and the existing transfer engine.
Neither a sharp constant `β = 1` nor a mass gap is required for this norm-bound packet.
Check the remaining Faris–Lavine commutator bound separately at its **quadratic-form**
level; a bound by the square of a graph norm does not replace it.

**Correct domain reading (§32).** `FormDomainComparison` names an operator graph estimate
on a core. After the appropriate core/closure proof it controls `K` on `D(N)`. It does
not put the quadratic-form domain `D(N^{1/2})` in `H²`. For the partial kinetic set the
natural form domain has derivatives only in `S`, with `W^{1/2}u ∈ L²`; it is not full
`H¹(R¹⁶³)`. Form coercivity gives `‖u‖ ≤ ‖(N+I)u‖` on the operator core; it does not
prove the reverse domain inclusion `D(N^{1/2}) ⊆ D(N)` asserted in older prose.
Use the displayed Lean predicates as the target until the extension theorem is proved.

**A candidate sufficient estimate, not a theorem already obtained.** Reuse §38's identity
on the same core:

```text
‖(N+I)u‖² = ‖Ku‖² + ‖(W+1)u‖²
             + 2 ∫ (W+1)|∇_S u|² − ∫ (Δ_S W)|u|².
```

A new proof of `∫ (Δ_S W)|u|² ≤ a‖Ku‖² + b‖(W+1)u‖² + C‖u‖²`,
with `0 ≤ a,b < 1` and `C ≥ 0`, would yield both graph controls, using positivity and
coercivity. This permits slack and a larger finite constant. Verify it uniformly in the
120 derivative-free jet parameters; no ellipticity in those variables may be assumed.
Pointwise quartic growth in all 163 coordinates is not available along every flat channel.
If the candidate fails, record the channel and failed uniformity estimate. The radial
proxy of §43 tests neither all channels nor this general finite-constant assertion.

**Landed on the QYM side (2026-11-11), and what does not transfer.**
`ChapterYangMillsMehlerBridge` now carries `graphNorm H u = ‖u‖ + ‖Hu‖`,
`quadForm_le_norm_mul_graphNorm` (the form bounded by `‖u‖ · graphNorm`, from `re z ≤ ‖z‖` and
Cauchy–Schwarz), `potentialPart_le_graphNorm` (any non-negative summand of the form), and
`potentialEnergy_le_graphNorm` for the `w + ‖·‖²` split, with the instance
`ym_quadForm_le_norm_mul_graphNorm`. That is the **quadratic-form** domination the Faris–Lavine
commutator input needs on the QYM side, and it is deliberately not the operator estimate this
section asks for. `‖K u‖ ≤ c‖(N+I)u‖` stays open, and the reason is the one stated above: a weight
with a large kernel and a large value on a thin set keeps the form small while making `‖W u‖` large,
so no form-level bound reaches the norm level. The QYM row's remaining item is unchanged.

### Packet acceptance after that input

P4 must instantiate the existing family bounds with the proved constants, complete the
form-level commutator estimate and audit the resulting ESA theorem's binders. P5 then
constructs the physical reducing sector and the required graded outer lift; P6 binds its
Hashimoto/SIRK resolvents to that same self-adjoint realization. P7 still needs its own
cutoff-uniform estimates for the intended infinite-mode operator. P8 records all of these
against one fixed operator, including numerical tails and remaining conditional clauses.

Ordinary polynomial degree of `smMagG/W/B` and engineering weight of a covariant local
field are different invariants. The QYM quartic degree theorem suggests an analogous
**polynomial** lemma for the SM comparison. Gauge-invariant label quotients, a stress
trace, OPE exponents and Ward identities would require the additional cftproof dictionary;
none is a P5 ESA prerequisite, and no pure-gauge short-distance coefficient is borrowed.

The exclusion *template* is now code, and it borrows no coefficient:
`BookProof/Sm/ChapterSmFreeModeExclusion.lean` states the finite-kernel non-freeness test —
`shortNorm`, `modeKernel`, `wickSum`, and `not_eventuallyEq_wickSum` — with the trace coefficient as
a hypothesis and the finite-list scope explicit. An SM candidate observable can be tested against
`not_eventuallyEq_modeKernels` without any pure-gauge number entering the statement.

## 1. Fix the mathematical endpoint before proving it

The reference is [book.tex](book.tex), especially “Majorana spinors in the Standard
Model”: the weak/Higgs Lagrangian, quark covariant derivatives and Yukawa equations,
and the analogous lepton sector with three right-handed neutrinos **without Majorana
mass terms**. “Majorana” as a real spinor representation does not introduce a
Majorana mass. The manuscript's recursive second-quantization convention determines
which operator is the final Hamiltonian.

Read this alongside [the pedagogical SM chapter](Book/StandardModel.lean),
[softmodes.md](softmodes.md) for the nested-sector and spectral boundaries, and
[Hashimoto–Nodera](../papers/Hashimoto.md), Definition 2.4 and Theorem 4.1,
for the operator-function approximation conditions used in P6/N4.

The endpoint in this formalism is

```text
h_SM = h_B + h_Dirac + h_gauge–matter + h_Yukawa,
H_SM = dΓ_out(h_SM) = Σᵢⱼ (h_SM)ᵢⱼ C†(eᵢ) A(eⱼ).
```

**Numerical priority:** Hashimoto approximations of these complete nested-Fock
objects are the physical acceptance tests. Do not substitute a mainstream lattice
Hamiltonian, radial Higgs model, decoupled sector or free-field surrogate. A finite
compression is acceptable as a controlled approximation of the same operator,
with every retained interaction and omitted-support error identified. Small matrix
and CCR/CAR tests are supporting construction oracles only.

All inner terms are retained **before** enclosing them, with creation on the left
and annihilation on the right. “Quadratic in outer ladders” does not mean free or
quadratic in the inner fields. Hashimoto approximation starts from an identified
self-adjoint closure; it neither defines a substitute Hamiltonian nor proves ESA
from finite Ritz values.

Two endpoints must be reported separately:

* **E1: the complete manuscript collective-coordinate operator.** All SM gauge,
  Higgs and matter multiplets, all four real Higgs components, the operator-valued
  gauge connection, and the spatial Dirac derivative on the stated inner space;
  then its physical-sector realization and outer enclosure. A finite *internal*
  species/Grassmann space is not automatically a spatial or energy cutoff.
* **E2: an infinite matter-mode/Fock realization**, if the inner fermionic factor
  is `SmCarContinuum.CFock` rather than the finite internal space of E1. Define
  that Hamiltonian and its common core, infinite sums and local products first.
  The continuum CAR representation alone does not construct it. E2 cannot be
  claimed from a sequence of finite-dimensional ESA statements without estimates.

P0 pins the E1 representation and its relation to E2. Complete E1 without hiding
its domain in “finite modes”; include P7 until the interpretation of the intended
infinite-mode realization has been settled by an explicit representation theorem.
No claim of an ordinary continuum SM ultraviolet construction follows merely
from naming the collective-coordinate operator “full”.

### 1.1 Bosonic, matter and outer spaces

The source bosonic space is `L2d 163`, with the nine coordinate blocks of
`SmOneParticle.SmCoord`: `3+24+72+9+27+3+9+4+12=163`. There are **40** active
field/Higgs momentum coordinates and **49** squared forms. The other 120 jet
coordinates and three spatial coordinates are not forty additional field momenta.
The jets remain independent coordinates in this SM realization. The spatial-
derivative elimination by momentum convolution is an **NS/QG-only** work order;
do not import that elimination to change this SM operator.

The inner space initially has the form
`K_SM = L²(R¹⁶³) ⊗ F_internal`, with a proved finite CAR/Clifford representation
for *all* manuscript matter components. Its outer Fock space counts copies of
these inner states. `QuantumState::vacuum()` in Rust is the empty **outer** space;
creating an empty inner bosonic or fermionic universe is not that vacuum.
The physical prior has one outer particle at each informed point of 3D space, hence
can have many outer particles when field information concerns several spatial points.
This is a local occupation statement, not a global one-universe or `N_out = 1` constraint.
“Outer-free” retains every inner gauge, Higgs and matter interaction in `h_SM`.
The current Rust state model has separate bosonic and fermionic outer-universe
collections; identify a **joint** inner boson–fermion state before claiming it
implements this tensor-product one-particle object.

Reference: [book.tex](book.tex), “Free field parametrization in Statistical Field Theory”,
the recursive lift and the proposition at distinct spatial points, including its
number-density normalization. P0 must identify the spatial prior supports, their local
inner states and joint correlations, and their embedding in the existing SM coordinates.
P6/N4 must test Hashimoto/SIRK evolution and joint observables for populated multi-point
priors. Empty-outer-vacuum annihilation remains a structural check, not the physical
reference state or a reason to add number-changing observables. No stationary/ground
state assumption follows just from specifying prior information.

Recount independent matter variables after the manuscript's reality/chirality
constraints and choice of complex structure. The book explicitly lists 72, 36,
36 real quark components and an analogous lepton construction. Record the
lepton count, particle/antiparticle convention and constraint ranks as theorems.
Do not identify a real-component count with a number of CAR annihilation modes
without proving that identification. Include all three generations, color,
weak doublets/singlets and right-handed neutrinos; ghosts are a separate sector.

### 1.2 The exact interactions to assemble

Use the bosonic `smHamiltonian P` with full `smMagG`, `smMagW`, `smMagB`,
`smCovD` and Higgs wall. Pin physical structure constants and real electroweak
matrices, rather than leaving `SmParams.tgen/ygen` arbitrary and calling that
physical identification complete. The manuscript's weak field-strength sign
must be matched to the chosen generator/structure-constant convention explicitly.

Pin the meaning of the spatial matter derivative as well: does it act at fixed
collective field/jet coordinates, or as a total derivative on configurations
containing fields that depend on position? Prove the representation map and its
chain rule from the manuscript. Do not assume a constant background or set the
spatial field derivatives to zero to obtain the simpler analytic normal form.
If the map produces extra jet–momentum terms, include them in the operator and
the comparison work before claiming P2/P4 complete.

For a finite internal representation the full matter expression should reduce to

```text
h_SM = h_B ⊗ I
     + Σⱼ p_xⱼ ⊗ Aⱼ
     + Σ_(field coordinates r) qᵣ ⊗ Jᵣ
     + Σ_(a : Fin 4) φₐ ⊗ Yₐ
     + I ⊗ M₀,
```

where the constant internal operators are bounded and Hermitian, and the
coefficient dictionary is **derived** from the manuscript, including chirality,
charges, color, spin and generation. This is a target normal form, not a new
unproved definition declared equal to the physical Hamiltonian. If realification
requires another term, extend the formula and its estimates instead of dropping it.

The Yukawa dictionary must include `M_d`, `M_u`, `M_e`, `M_ν`, the doublet and its
`iσ₂` partner, conjugate/chiral conventions and h.c. pairing. Generic complex
three-generation matrices cover phases; a real two-generation rotation is only
a test case. Derive the factors from the manuscript's `-L_Y/2` convention before
building Hermitian coupling matrices. All four real Higgs components need their
coefficient matrices even when some entries vanish by representation structure.

Fix the Higgs energy convention once. With `φ†φ=|φ_real|²/2`,
`V=−μ²|φ_real|²/2+λ|φ_real|⁴/4`, and the implemented positive square adds
`c_H=μ⁴/(4λ)` when `λ>0` and `v²=μ²/λ`. This specified inner constant changes
`H_SM` by `c_H N_out`. It is not an arbitrary outer vacuum-energy subtraction.
ESA does not need the full matter Hamiltonian to be nonnegative or gapped.

## 2. Reuse inventory: exact source scope

The entries below are source-present declarations, not newly rerun axiom/build audits.

| Source | Reusable result | Boundary |
|---|---|---|
| `BookProof/Sm/ChapterSmOneParticle.lean` | `card_smCoord`, indexing and `IsMixing` identities | A coordinate count and matrix identities do not assemble the full matter operator. |
| `ChapterSmHamiltonian.lean`, `ChapterSmFieldStrengthSplit.lean` | Symmetric nonnegative bosonic form; full derivative/commutator magnetic polynomials | Dirac and Yukawa operators are outside `smHamiltonian`. Physical generator matrices still need instantiation. |
| `ChapterSmFarisLavine.lean` | `smFlN`, `sm_commForm_le`, `sm_norm_le_shift` | The useful comparison is `2h_B+Σ_active q²+c`, not the old quartic `smComparison`. |
| `ChapterSmComparisonEsa.lean` | `smFlN_esa`, `sm_h_esa` | Bosonic ESA is closed; it does not include spatial Dirac or gauge–matter interactions. |
| `ChapterSmFockEsa.lean` | `smSectorHam_esa`, `smFockHam_esa`, `sm_dGamma_esa` | Encloses that bosonic inner operator. |
| `ChapterSmCarAlgebra.lean`, `ChapterSmDiracYukawa.lean` | Finite CAR and bounded Hermitian bilinears; `sm_fermi_esa` | Finite fermionic operator; fixed-background Higgs and Dirac matrix. |
| `ChapterSmFullEnclosure.lean` | `smFull_h_esa`, `smFull_dGamma_esa` | Tensor sum with a fixed Higgs background, not a boson–fermion interaction. |
| `ChapterSmYukawaCoupling.lean` | `higgsMul_relBound`, `smYukawa_h_esa`, `smYukawa_dGamma_esa` | Operator-valued Yukawa, but only `smPhi 0/1`, finite CAR factor and fixed `hD`; no gauge-coordinate coupling or unbounded spatial Dirac derivative. |
| `ChapterSmGaugeConnection.lean` | `diracGaugeMat_split`, `dirac_gauge_field_esa` | Gauge components are scalar background values and momentum is `ik`, not an assembled coordinate operator and spatial derivative. |
| `ChapterSmCarContinuum.lean` | Smeared CAR and `norm_cCreS_le` | No complete SM Hamiltonian on `CFock` or cutoff-removal theorem. |
| `ChapterSmGaugeRepresentation.lean`, `ChapterSmBrstGhost.lean`, book BRST modules | Finite representation algebra, nilpotency and temporal-slice accounting | Not yet a strongly reducing physical Hilbert realization of the full interacting closure. |

The remaining work is mainly **operator identification and assembly**, followed by
a genuine new comparison estimate for the full normal form. Searching only for
`sorry` misses this: proved theorems can cover a smaller operator than the target.

## 3. Preferred analytic route: a comparison controlling the whole operator

A generic gauge coordinate is not relatively bounded by `h_B` just because the
magnetic polynomial is quartic. Along commuting gauge directions the magnetic
potential can vanish. Do not extend the Higgs-wall Kato–Rellich argument to all
gauge coordinates without a proof.

Instead investigate the full comparison

```text
N_SM = [2 h_B + Σ_active qᵣ² + Σ_(j : Fin 3)(p_xⱼ²+xⱼ²) + c] ⊗ I_internal,
c ≥ 1.
```

The active set is the source's 40 momentum-carrying coordinates, disjoint from
`smX`. This is a **comparison**, never the final Hamiltonian. In particular it
does not add an oscillator confinement term to `h_SM`.

The same degenerate Kato/Hermite-core machinery that proves `smFlN_esa` should
apply to `N_SM`: kinetic subset = the 40 active coordinates plus the three
spatial coordinates; polynomial potential = all original squared forms plus
active/spatial coordinate squares and the fixed constant. Its pointwise lower
bound follows from sums of squares. This proposed application must be proved
for the exact source operators and normalization, not inferred from its shape.

This simple comparison route applies only after P0/P2 prove the displayed
normal form and its spatial-independence identities. If the correct matter
derivative includes additional jet-coordinate times field-momentum products,
the specialist must derive their commutators, design a weighted comparison
controlling those products and prove that comparison ESA independently. The
43-coordinate candidate is not a justification for omitting such terms.

The useful core commutators are:

* `[h_B,N_SM]` reduces to the already controlled `[h_B,Σ_active q²]`,
  because `h_B` has no explicit dependence on the three `x` coordinates;
* `[qᵣ,N_SM]` is proportional to its active conjugate momentum;
* `[p_xⱼ,N_SM]` is proportional to `xⱼ`;
* bounded constant internal matrices commute with the scalar comparison.

Thus the new linear gauge/Higgs and spatial Dirac terms have comparison-form
bounds controlled by momenta/positions already present in `N_SM`. The growth
constants depend on the actual internal operators, not on a sampling residual.
Prove both the relative **operator norm** estimate and the commutator **form**
estimate. A form inequality alone is not the norm hypothesis of Faris–Lavine.
Do not replace this step by `N=h_SM²+I`: its ESA/range assumptions would be
circular. The obsolete uncoupled quartic comparison cannot be revived by an
AM–GM identity involving an uncontrolled `q⁶` term.

## 4. Proof packets for the LLM-Lean4-specialist

All names introduced in this section are **proposed deliverables**, not existing
Lean declarations. Keep each packet small enough to compile and audit separately.
Record the operator, Hilbert space, core and remaining assumptions for every theorem.

### P0 — freeze the operator and verify the baseline

Create `BookProof/Sm/ChapterSmPhysicalData.lean` and a term ledger relating
manuscript equations, existing definitions, Cadabra handles and Rust contracts.
Specify E1/E2, all coordinate/fermion indices, the chosen inner constant and
outer statistics. Prove active/spatial index disjointness and all field-count
identities; check gauge and Higgs normalization/sign conventions against the book.
Re-run the existing SM audit files before building on their recorded results.
Repair import-component metadata deliberately before registering new targets;
its stale roots and unnamed component are already recorded in the prior work order.

Acceptance: no occurrence of “full” is doing the work of an unproved operator
identity; no empty mode set, zero coupling or fixed background discharges the target.

### P1 — complete the internal representation and four-component Yukawa dictionary

Create `ChapterSmMatterRepresentation.lean` and `ChapterSmFullYukawaData.lean`.
Construct all quark/lepton chiral representations in the manuscript's real
spinor convention, including charge conjugation, color, generation and right-
handed neutrinos. Prove the chosen independent-component/CAR identification.
Instantiate the Higgs generators and their realification rather than assuming
arbitrary `tgen/ygen` are the physical matrices.

Construct Hermitian bounded `A_j`, `J_r`, `Y_a`, `M₀`, with all four mass/Yukawa
matrices and complex phases. Reuse finite CAR bilinear norm/adjoint lemmas.
Prove the full h.c. expression equals the sum over four real Higgs components;
recover the existing two-component and fixed-background models as labeled
specializations. Derive gauge covariance and the appropriate charge conservation
relations; a single-mode `y φ n_f` test is not this dictionary.

Acceptance: a nonzero charged-doublet component and nontrivial complex mixing
example, with gauge covariance and Hermiticity checked independently. No Majorana
mass term is silently added because the spinor representation is real.

### P2 — construct the exact coupled inner operator on a common Mehler core

Create `ChapterSmFullMatterHamiltonian.lean`. Use the source's
`polyGaussCore 163` tensor the internal finite space. Define the spatial momenta
on `smX` with the actual Gaussian-polynomial momentum convention, and the
operator-valued gauge/Higgs coordinates on their own conjugate modes.

Prove density, invariance under each polynomial/differential term, symmetry,
fermion-parity preservation, and the elementary-tensor action of the full
normal form. Prove a term-by-term identity to the physical expression from P0/P1.
Do not use a plane-wave parameter in place of the spatial derivative and still
call the resulting theorem the full-space result.

The Mehler dictionary must specify the Gaussian normalization, Hermite variance,
coordinate scale and canonical commutators. `pgFun p = p exp(-|x|²/4)` describes
vectors in Lebesgue `L²`; multiplication/differentiation transport must agree
with `coreRepPoly` and `momOp`. A Gaussian reference weight is not a new Higgs
or gauge potential, and its vacuum is not the physical outer vacuum.

Acceptance: the operator contains every ledger term, and no “proof” of equality
is merely a new definition chosen to make the theorem `rfl`.

### P3 — prove comparison ESA and its graph-core transfer

Create `ChapterSmFullComparisonEsa.lean`. Define exactly the `N_SM` of §3.
Express it as the appropriate `hamCoreS` on the 43-coordinate kinetic subset
of `R¹⁶³`, with the untouched 120 jet coordinates in the potential/parameter
part. Prove positivity, the polynomial lower bound, symmetry and dense core.
Reuse `DegKatoEsa.ccHamS_esa`, `HermiteGraphApprox.hamCoreS_esa` and real-shift
transport to obtain `N_SM` ESA on that same core. Tensor with the finite
internal factor and construct the comparison/graph-core data actually consumed
by the Faris–Lavine API.

Acceptance: no frozen gauge/Higgs background and no added kinetic derivatives
in the jet coordinates; no assumption that the desired comparison is ESA.

### P4 — full Faris–Lavine bounds and inner ESA

Create `ChapterSmFullFarisLavine.lean`. First prove comparison controls on
`q_active`, `p_active`, `x`, `p_x`, and the bosonic Hamiltonian. The operator
norm bound for `h_B` with the enlarged comparison needs proof: exploit the
spatial independence and commuting positive spatial oscillator, or generalize
`sm_norm_le_shift` without assuming positive cross terms by fiat.

Lift the controls to finite internal components using the proved matrix/operator
norm constants. Establish explicit `K,C≥0` such that on the common core

```text
‖h_SM u‖ ≤ K ‖(N_SM+I)u‖,
|commForm h_SM N_SM u| ≤ C quadForm N_SM u.
```

Then apply `CoreData.esa_core` or the appropriate Faris–Lavine core theorem.
The conclusion target is `smComplete_inner_esa` with physical data and stated
coupling assumptions only. Try the comparison-based proof before demanding
`λ>0` from the restricted Higgs-wall perturbation proof; distinguish minimal
analytic assumptions from the physical positive-quartic parameter instance.

Fallback: prove an explicit matrix-valued differential-operator ESA theorem
for this normal form, with full domains, if the existing norm-bound machinery
cannot accommodate it. Do not leave `FullSmComparisonESA` as a final hypothesis
or invoke the scalar Kato theorem directly for an indefinite matrix potential.

Acceptance: `#print axioms` and theorem binders show no assumed symmetry,
comparison ESA or relative bounds equivalent to the requested conclusion.

### P5 — physical gauge sector and the complete outer enclosure

Create `ChapterSmPhysicalReductionEsa.lean` and `ChapterSmCompleteEnclosure.lean`.
First identify the unreduced closure. To restrict it, construct the actual
physical Hilbert subspace/quotient, a positive inner product and a reducing
projection or gauge-group unitary action. Show strong commutation with the
self-adjoint closure and supply a dense graph core for the restriction.
A formal core commutator, BRST nilpotency or well-defined algebraic cohomology
alone does not prove ESA on the physical sector.

Use temporal-slice BRST accounting with its exact hypotheses. Do not append a
free ghost Hamiltonian to a physical record from which gauge fixing has already
been eliminated. Any ghost-extended comparison needs its own operator contract.

Lift the identified physical `h_SM` using
`EsaOneParticle.dGamma_essentiallySelfAdjointOn_of_esa`, and instantiate the
required symmetric/antisymmetric/graded sectors. Existing ordinary statistics
lifts are reusable; if the manuscript requires a graded permutation action,
prove its compatibility with the even inner Hamiltonian and its core explicitly.

The numerical graded representation now supplies a concrete route: split the
inner space by finite-CAR parity into `K_even ⊕ K_odd`. Prove parity is a bounded
unitary preserving the common core and commuting with every assembled term;
use ESA to obtain strong reduction of the closure. Identify the graded outer
space with `Gamma_s(K_even) tensor Gamma_a(K_odd)` and prove the two lifted
operators' tensor-core sum is ESA. This needs the actual unitary/core transfer,
not just an algebraic parity commutator. Reuse the ordinary statistics lifts
on the two reducing factors rather than assuming a general graded theorem.

**Landed 2026-11-12: the strong reduction of the closure (see §44).** `ChapterSmPhysicalReductionEsa`
turns the core-level identity into a statement about the closure: the deficiency space of
`smNormalForm D` at a deflation point is trivial **iff** both parity-sector deficiency problems are
trivial (`deficiencyTrivialAt_iff_sectors` generic, `smNormalForm_esd_iff_parity_sectors` at `h_SM`),
and each sector core is dense in its sector (`topologicalClosure_evenCore`, `topologicalClosure_oddCore`).
Deficiency spaces are the corpus's representation of the closure, so this is the "strong commutation
with the self-adjoint closure" this paragraph asks for, obtained from the unitary/core transfer and
not from an algebraic parity commutator. What P5 still lacks is the *physical* side: the BRST
quotient with its positive inner product, and the graded outer lift
`Γ_s(K_even) ⊗ Γ_a(K_odd)` — the latter consumes essential self-adjointness of each sector
operator, i.e. P4's elliptic input, which stays a hypothesis.

**Landed 2026-11-11: the unitary/core half of that route.** In
`ChapterSmFullMatterHamiltonian`, `coupledParity` is now a norm-preserving involution
(`coupledParity_norm` from the coupled `ℓ²` identity `coupledSpace_norm_sq`,
`coupledParity_involutive`, hence `coupledParity_surjective`), and it preserves the common core
(`coupledParity_mem_core`, `coupledParityCore`). What is still missing is precisely the part this
paragraph requires next: `smNormalForm_parity` is a **core-level** identity, and the closure's graph
has no commutation statement, so the strong reduction is not obtained.

Acceptance: `smComplete_dGamma_esa` and the intended statistics/physical-sector
versions all refer to **the same** `h_SM`, with `C†` left and `A` right.
`HΩ=0` is structural; do not add a positivity or mass-gap conclusion to ESA.

### P6 — closure, Stone evolution and the Hashimoto seam

Create `ChapterSmCompleteHashimoto.lean`. Identify the unique self-adjoint
closure and its Stone group. Reuse the existing non-real resolvent theory:
for `Im z≠0`, `‖(h̄_SM-z)⁻¹‖≤1/|Im z|`. Prove the corresponding lifted
operator statement on its correct domain.

For Hashimoto–Nodera, map the evolution generator explicitly (`A=-i h̄_SM`
for unitary evolution). Its imaginary-axis spectrum is not a proof that an
arbitrary positive real shift works for `h̄_SM` itself. Check Definition 2.4
and Theorem 4.1's numerical-range, function and shift-budget hypotheses for
the chosen generator/approximation. Keep time step distinct from Hamiltonian
notation. Charge projection, cutoff, solve, roundoff and rational-approximation
errors separately. Finite forward Krylov polynomials require their initial
vectors in the relevant powers' domains; extend to general states by an
explicit density/unitarity argument if that is claimed.

Acceptance: numerical SIRK tests apply the declared operator/closure and shift
convention. ESA and resolvent existence do not supply a spectral gap or an
unseen-eigenvalue exclusion.

### P7 — infinite inner fermion modes, where intended

Create `ChapterSmInfiniteMatterHamiltonian.lean` only after P0 states its
representation and kernels. Start with the existing smeared CAR model. Define
the unbounded free matter second quantization, its energy/number comparison,
finite-mode embeddings, a dense finite-energy/core domain, and every interaction
as an operator or closable form. A bounded smeared creation operator does not
make an infinite bilinear sum bounded or a point-field product well defined.

Prove cutoff-uniform graph/commutator estimates and convergence on a common
core, then identify an ESA limit using a theorem with its actual hypotheses.
Strong-resolvent convergence of selected self-adjoint extensions alone does not
prove ESA of the proposed limit's initial core. If ultraviolet/local products
diverge, deliver the exact obstruction and a fully labeled regulated theorem;
state the necessary kernel or counterterm problem rather than assuming uniformity.
A momentum or mode cutoff is numerical/analytic data, not NS/QG jet elimination.

Acceptance: E2 has a constructed operator and audited ESA proof, or is explicitly
open with the failed estimate identified. E1 may be closed without pretending
this proves E2.

### P8 — publication and regression gate

Update the boundary ledger, `Book/StandardModel.lean`, the routing table and the
consolidated state **after** proof checks. Run the existing SM audit files,
new target theorem/axiom audits, import/target checks, the patched book wrapper
and KaTeX checks. Print all final theorem binders and the actual identified
operator; count a wrapper with a missing physical-equivalence assumption as C,
not U. Keep historical proofs and rename ambiguous model descriptions rather
than rewriting them into a stronger theorem.

## 5. `unfer` findings and required corrections

The detailed implementation work order is
`../unfer/docs/SM_HAMILTONIAN_AUDIT.md`. Its findings are part of this plan:

1. `sm_higgs_expression` uses `φ=c₀+a₀` and a kinetic expression on **mode 1**.
   Thus field and putative momentum commute. This is a two-coordinate comparison,
   not a canonical quantization of the same Higgs component.
2. `cas::normal_order_inner` sorts creators/annihilators, discards contractions
   and does not implement general fermionic reordering signs. For a quartic,
   omitted contractions include lower-degree **operator** terms, not just a scalar.
   Consequently restoring one constant is not a general repair. Do not globally
   change the legacy compiler without an API/consumer migration and regression plan.
3. `sm_comparison_n` implements a historical `:π²:+:φ⁴:` model. It is not the
   proved `smFlN`. The Cadabra text claiming first differential order implies
   its domination is false; an AM–GM `q⁶+p²` bound does not control `p²+q⁴`.
4. `sm_gauge_fixed_hamiltonian.cdb` CHECK 9's prior assembly repeats one gauge
   scalar three times and omits explicit Higgs kinetic/covariant and Dirac pieces.
   Its CHECK 11's scalar identity does not verify U(1) normalization. These checks
   require bounded corrections and honest scope labels, not a “full SM derived” claim.
5. A scalar single-field coherent state over the whole line is not certified
   gauge-invariant merely by calling the coordinate radial. A true doublet
   radial reduction needs its measure, domain and gauge constraint. The reduced
   dynamics cannot establish EWSB of the complete Hamiltonian.
6. A finite SIRK Ritz minimum above `-10^6` is not a semiboundedness proof; it
   is variational upper information within the observed subspace. Nor does
   projected Hermiticity alone verify all omitted operator sectors.
7. The numerical budget/ghost/mass-anchor tests exercise separate models.
   A commuting-Gauss ghost charge is not the complete nonabelian SM BRST charge,
   and a measured W/Z mass inserted as a parameter is not a prediction from `h_SM`.

Implement **N0** labeling and local algebra/test repairs now. Defer the expensive
full canonical builder, exact CCR/CAR compiler and joint-state enclosure migration
to N1–N5; no regenerated physical spectrum or renewed certificate is claimed by
this source audit.

## 6. Order, deliverables and completion gate

```text
P0 → P1 → P2 → P3 → P4 → P5 → P6 → P8
                    P7 → E2 audit → P8 (where E2 is intended)
N0 → N1 → N2 → N3 → N4 → N5, cross-checking P0/P1/P2/P6
```

P1 and the scalar comparison lemmas of P3 can be developed independently after
P0 fixes the operator. P4 is the main analytic assembly risk; P5's physical
reduction and P7's infinite sums are separate risks, not bookkeeping. Execute
small modules with compilation/axiom audits, not one giant proof attempt.

| Endpoint | Evidence required |
|---|---|
| Bosonic baseline retained | Actual `sm_h_esa` and bosonic enclosure audits, no duplicate replacement proof |
| Complete inner E1 ESA | All manuscript terms identified on a common dense core; full comparison bounds discharged |
| Physical/statistics enclosure | Reducing physical realization, graph core and outer lift of that exact inner operator |
| Hashimoto implementation seam | Identified generator, admissible shifts and independent error/representation budgets |
| Infinite-mode E2 | Constructed operator, uniform estimates and proved limit/core identification, or explicit open obstruction |
| Numerical consistency | Canonical same-mode CCR/CAR, retained inner constants/contractions, full term ledger and labeled cutoff convergence |

Completion is not “all files contain no `sorry`”. It is the audited theorem chain
for the declared endpoints and operator, with no equivalence/ESA hypothesis hiding
the unfinished part. New numerical or symbolic checks cannot substitute for it.

## 7. Validation record for this planning wave

No Lean compilation was performed. A focused Cargo attempt used
`cargo test --offline --release -p fock_sirk --test sm_gauge_fixed_validation`;
it stopped before compilation because `ahash v0.8.12` is absent from the local
Cargo cache. This is an environment limitation, not a passing test or a test failure.
Further source/static and isolated Rust-algebra results are recorded in the sibling
audit and the consolidated state after they have actually run. Cadabra runtime
checks remain pending in an engine-equipped environment.

### Full-operator Hashimoto numerical acceptance (user priority)

N4 is the principal numerical deliverable. Required tests must instantiate the
complete nonzero-coupling nested operator from N1–N3, not mainstream Hamiltonians,
radial scalar dynamics or decoupled simplifications. Finite matrices and the
construction checks added in N0 are necessary identity/error oracles only.

* `sm_full_hashimoto_inner_outer_action`: the full inner and one-outer-particle
  actions agree, with the same joint boson–fermion basis and every ledger term.
* `sm_full_hashimoto_sector_structure`: vacuum rank collapse, nontrivial
  one-particle Krylov action, and two-particle sector sums/statistics for that
  full operator; inner constants give the correct number-dependent shift.
* `sm_full_hashimoto_ritz_residual_enclosure`: Ritz values and complete residuals
  agree with independently assembled small compressions of the full operator;
  include the outside-cutoff component and an independent separation assumption
  wherever a spectral enclosure uses one.
* `sm_full_hashimoto_budget_refinement`: vary rational shift budget, Krylov
  length, occupation cutoff and pruning independently, retaining all physical
  terms; report each approximation error instead of changing the model.
* `sm_full_hashimoto_restarted_evolution`: fixed full-generator evolution
  stabilizes under Krylov/time/cutoff refinements with norm/energy diagnostics
  and the actual admissible-shift/function hypotheses.
* `sm_full_hashimoto_interaction_mutations`: omitted gauge/Higgs/Yukawa/Dirac
  terms and chiral/contraction/sign errors fail targeted action or residual
  comparisons. Zero-coupling models are controls, not the physical acceptance run.

These are proposed test names and acceptance contracts, not implemented passing
tests. If the full sparse action is too costly, implement factorized application
and bounded discarded support. Report that computational boundary explicitly;
do not obtain a green physical test by removing fields or interactions.

The staged Rust algebra-only source was compiled separately with its cached
`num_complex` dependency and all 11 construction checks passed. This is supporting
N0 evidence only: it is not a Cargo/SIRK integration run or full-SM validation.

After installation, the GitBook checker passed with 87 pages, 609 internal links,
and no warnings. The source-citation gate found no unreviewed misses; its existing
forward-reference and `realize_injective` ledger warning remains a separate
maintenance issue. Root relative-link checks and whitespace checks in all three
repositories passed. The documentation index was regenerated; these checks do
not elaborate Lean or execute Cadabra.

## 8. Executed continuation — ordered joint action (2026-11-09b)

The N1/N3 algebra/action foundation is now implemented in
`../unfer/nested_fock_algebra/src/exact_inner.rs`. It supplies a joint inner
boson/fermion basis, factorized ordered products, same-mode canonical coordinates,
adjoints and a single outer enclosure on ordinary symmetric/antisymmetric joint
sectors. It retains constants, CCR contractions and CAR signs. Resource limits
return errors without silently pruning or changing the operator. Coefficients
still use floating point; this is not an interval-rounding certificate.

An additional source/runtime finding is material: each legacy `Inner*` letter
already acts as an outer one-body lift. Multiplying them can give
`dGamma(B)dGamma(C)` rather than `dGamma(BC)`. An empty legacy word acts as outer
identity rather than outer particle number. The new API completes the inner
action before lifting, and a regression reproduces the distinction using the
actual legacy API. Existing executable semantics remain unchanged.

The complete staged algebra library, including its LaTeX feature, compiled
directly against compatible cached Rust dependencies. The new integration suite
linked against that rebuilt library and **10 tests passed**, using independent
ladder/Jordan–Wigner matrices and symmetric/exterior tensor sums. Ordinary
offline Cargo remains blocked before compilation on missing `ahash v0.8.12`.
No Lean compilation or Cadabra execution was performed.

This is construction evidence, not a full-SM numerical result. N1 still needs
the complete physical bosonic builder, N2 the physical matter dictionary, and
N3 the correct physical comparison/statistics identification. N4 must migrate
the SIRK vector/registry/matvec interface to joint states, propagate action errors
and account for support deletion, including the old `scale_and_add` amplitude
threshold. Residual identities must include any pruning defect. Then execute
the six full-operator Hashimoto contracts with all interactions retained.
See `../unfer/docs/ORDERED_JOINT_FOCK.md` for the API and migration boundary.

Post-installation checks passed: 87 GitBook pages / 610 links, no warnings;
no unreviewed source-citation misses; all three repositories' whitespace checks.
The existing reviewed forward references/ledger warning remain separate.

## 9. Full numerical E1 assembly and joint rational integration (2026-11-09c)

The full executable E1 operator and its joint Hashimoto path are implemented.
The current dictionary and commands are in
[SM_FULL_IMPLEMENTATION.md](../unfer/docs/SM_FULL_IMPLEMENTATION.md).
This supersedes earlier N1–N4 implementation deferrals in this document;
the Lean proof packets P0–P8 are still the specialist's work order.

The implementation retains all 163 bosonic coordinates, 40 field momenta,
49 squared forms, 96 complex CAR coordinates (192 real Majorana components),
spatial Dirac momenta, every gauge–matter coupling, and all four Higgs/Yukawa
components with fully complex three-generation matrices and h.c. No additional
Majorana mass or duplicate antiparticle coordinate is introduced. The source
Majorana spin frame is checked against the fixed integer matrices in
`ChapterA3` and `ChapterCPTHamiltonian`; it is not replaced by an assumed
conventional Pauli-frame formula. The spatial derivative is the declared E1
fixed-collective-coordinate derivative; a total-jet interpretation still needs
its own proved representation map before it can be identified with this operator.

Cadabra2 independently derives and exports 1,241 actual LaTeX expressions:
40 momenta, 49 forms and all 1,152 symbolic matter entries. The existing
mathhook calculus imports only commuting coefficient polynomials, checks them
against the native dictionary, and constructs the exact ordered inner action
before its single outer enclosure. Missing/extra terms, coefficient changes,
unknown AST nodes and noncommuting same-mode scalar imports fail. The complete
export fixture and the older SM templates have actual engine-run evidence.

The joint solver now constructs genuine resolvent vectors. For `A=-i h`,
`z_j=i gamma_j` with `gamma_j=(N-j delta)/t>0`, it uses the paper's bounded
resolvent compression `B=V†(gamma_m I+i h)^-1 V` and function generator
`gamma_m I-B^-1`. The separately computed Hamiltonian compression supplies
Ritz diagnostics. Forward products remain explicitly named polynomial
diagnostics; they do not inherit the rational approximation theorem.

Declared finite basis/occupation windows compress this same full operator.
Complete-image caching accelerates the projected shifted solves while retaining
all tails. Full shifted/Ritz residuals, restarted norms/energies, function-solve
errors and physical-basis orthogonality defects are reported. Pruning is
disabled; cache/action limits return errors. Gram whitening is followed by
reorthogonalization of the actual vectors to avoid coordinate cancellation.
The outer action supports parity-graded configurations mixing even bosonic
occupations and odd fermionic occupations, as well as the ordinary statistics
specializations. The primary full-SM runs use the graded representation.

**Executed validation:** normal Cargo runs pass 13 exact-action contracts,
7 full dictionary/Majorana/Cadabra contracts, 6 primary full-SM rational tests
and 11 supporting SM algebra checks: **37 unique tests**. The fresh Cadabra
fixture test ran without a skip. The `ahash` blocker is resolved through locked
dependency provisioning. No Lean compilation was performed.

For the illustrative nonzero-coupling instance, the finite-reference state error
at `t=0.01` is about `4.18e-7` with four rational vectors. This is accuracy for
the declared finite compression. The first full-action tail norms remain about
`9.78` (occupation 1) and `4.04` (occupation 2); the code exposes this unresolved
full-operator accuracy boundary rather than interpreting a small projected error
as a continuum certificate. No mass gap or full-operator cutoff removal follows.

Next for the Lean specialist: turn the executable coordinate/spinor/realification
and component identities into P0/P1 theorems, assemble the common-core operator
in P2, prove P3/P4 comparison bounds and ESA, then physical/graded reduction,
outer lift and the P6 resolvent/function error seam. E2 infinite matter modes,
roundoff enclosures and cutoff-uniform estimates remain separate proof tasks.

Post-installation verification: the complete example executed with a 70-state
window, norm `0.9999999999999639` and orthogonality defect `7.77e-16`; its
JSON includes the substantial full-action tails and conditional resolvent
error bounds. The symbolic regeneration gate passed (19/49 legacy CHECK rows
and exact full LaTeX fixture). The GitBook checker passed 87 pages / 611 links /
452 source–target pairs with no warnings. Cargo.lock was unchanged.

## 10. P0 executed (2026-11-09d)

`BookProof/Sm/ChapterSmPhysicalData.lean` now carries the P0 ledger and its proved identities;
it builds (`lake build BookProof.Sm.ChapterSmPhysicalData`, and through `BookProof.lean`).

* **Ledger data.** `SmLedgerEntry` and `smLedger` (six rows: `h_B` gauge, `h_B` Higgs, `h_Dirac`,
  `h_gauge–matter`, `h_Yukawa`, `dΓ_out`), each row naming the manuscript place, the Lean
  declaration, the Cadabra check/export, the Rust contract and an honest status. Only the
  bosonic row is `PROVED`; the Dirac, gauge–matter and Yukawa rows are `NOT AN OPERATOR` here, so
  no occurrence of "full" in the module does the work of an unproved operator identity.
* **Endpoints.** `SmEndpointSpec`, `smE1` (finite internal factor: 96 complex CAR coordinates,
  192 real Majorana components, fixed-collective-coordinate spatial derivative) and `smE2`
  (`SmCarContinuum.CFock`, no declared mode counts), with `smE1_ne_smE2`, `smE1_complexModes`,
  `smE1_realComponents`, `smE1_real_eq_two_mul_complex`, `smE2_noModeCount`.
* **Coordinate partition and disjointness.** `card_smJet` (72+27+9+12 = 120), `card_partition`
  (3+40+120 = 163), `kinetic_card` (40+3 = 43), `kinetic_partition` (43+120 = 163),
  `smCoord_partition`; the jet family `smJetCoord` is new; `smMomCoord_injective`,
  `smJetCoord_injective`, and the three disjointness theorems `smMom_disjoint_spatial`,
  `smMom_disjoint_jet`, `spatial_disjoint_jet` are proved, so the active, spatial and jet index
  families are pairwise disjoint subsets of `Fin 163`.
* **No empty mode set.** `smMom_nonempty`, `smForm_nonempty`, `smForm_blocks`
  (36+13 = 49, splitting the forms into the 24+9+3 magnetic block and the 12+1 Higgs block); the
  bosonic operator theorems already hold for **arbitrary** `SmParams`, so no zero coupling or
  fixed background discharges them.
* **Conventions.** `higgsVacuumEnergy` (`c_H = μ⁴/(4λ)`) with `higgsVacuumEnergy_eq`
  (`= μ²v²/4` under `v² = μ²/λ`, `λ ≠ 0`), `higgsVacuumEnergy_pos`, `higgsVacuumEnergy_zero`.
* **Matter recount is arithmetic, not modes.** `quark_leftReal`/`quark_rightReal`
  (36+36 = 72), `lepton_leftReal`/`lepton_rightReal` (12+12 = 24),
  `quark_real_eq`, `lepton_real_eq`, `matterReal_eq` (72+24 = 96). The identification of these
  real components with CAR annihilation modes is explicitly left to P1.

Not done by this packet: no `h_Dirac`, `h_gauge–matter` or `h_Yukawa` operator, no common core,
no comparison operator, no ESA statement, and no import-component metadata repair (the
`import_components` gate still reports its known split-wave drift, unchanged by this module).

## 11. P1 executed (2026-11-09e)

`BookProof/Sm/ChapterSmMatterRepresentation.lean` and `BookProof/Sm/ChapterSmFullYukawaData.lean`
now carry P1; both build (`lake build BookProof.Sm.ChapterSmFullYukawaData`) and are imported by
`BookProof.lean` after `ChapterSmPhysicalData`.

### The internal representation (`BookProof.SmMatter`)

* **Chiral content.** `SmWeylField` is the explicit 16-field content of one generation
  (`Q c s`, `uR c`, `dR c`, `L s`, `eR`, `nuR`), with `SmWeylField.card_field` (`6+3+3+2+1+1 = 16`);
  `SmMatterIndex = SmGen × SmWeylField × Fin 2` is the 96-complex-coordinate index
  (`card_matterIndex`, `matterIndex_complexModes` naming `smE1.innerComplexModes`) and
  `SmMajoranaIndex = SmMatterIndex × Fin 2` the 192 real Majorana components
  (`card_majoranaIndex`, `card_majoranaIndex_eq_two_mul`, `majoranaIndex_realComponents` naming
  `smE1.innerRealComponents`). Both counts are the E1 endpoint's, in the endpoint's own vocabulary.
* **Independent-component identification.** `smMatterMode : SmMatterIndex ≃ Fin 96` and
  `smMajoranaMode : SmMajoranaIndex ≃ Fin 192` (`Fintype.equivFinOfCardEq`), with
  `smMatterMode_injective`/`smMatterMode_ne`: the 96 coordinates are 96 distinct CAR modes, not a
  coarse-grained recount.
* **CAR representation.** `MatterFock = FermiFock 96`, `matterVac`, `matterAnnih`, `matterCreat`,
  and the transported relations `matter_car_annih_creat_self`, `matter_car_annih_creat_of_ne`,
  `matter_inner_creat_left`, `matter_norm_annih_le`, `matter_norm_creat_le`; the second quantized
  internal matrix `matterBilin` with `matterBilin_apply`, `matterBilin_symmetric` (Hermitian `M`
  gives a symmetric operator) and `matterBilin_norm_le` (the `ℓ¹` bound).
* **Charge conjugation.** `eps = iσ₂ = !![0, 1; -1, 0]` with `eps_transpose`, `eps_conjTranspose`,
  `eps_mul_self` (`ε² = -1`), `eps_unitary`, `eps_mul_unitary`; `chargeConj` (`ψ ↦ ε ψ̅`) with
  `chargeConj_zero`/`chargeConj_one`, `chargeConj_chargeConj` (**`C² = -1`**),
  `chargeConj_smul` (conjugate-linear), `chargeConj_add`, `chargeConj_injective`. Boundary: the
  doubling `SmMajoranaIndex` is a counting statement, not an identification with Majorana fields,
  and no Majorana mass term is implicit.

### The four-component Yukawa dictionary (`BookProof.SmFullYukawa`)

* **Higgs realification.** `higgsGen = ![1, σ₁, σ₂, σ₃]` built from
  `BookProof.SmGaugeRep.pauli`, with `pauli_conjTranspose`, `su2gen_hermitian`,
  `higgsGen_hermitian`, `higgsField φ = Σ_a φ_a • higgsGen a` and `higgsField_hermitian`;
  `higgsField_apply` gives the entries, `higgsCharged`/`higgsNeutral` the charged and neutral
  doublet components (`higgsCharged_nonzero`), `higgsField_injective` and
  `higgsField_surjective` (`higgsCoeff`, `eq_ofReal_re_of_conjTranspose_eq`) give
  **`higgsField_existsUnique`**: the four real components coordinatize exactly the Hermitian
  `2 × 2` matrices — the realification is onto, and no generator is redundant.
* **The h.c. dictionary.** `yukawaPair A Y = A Y + (A Y)ᴴ`, `yukawaPair_hermitian`;
  `yukawaPair_ofReal_smul_higgs` and **`yukawaPair_sum_higgs`**:
  `yukawaPair (higgsField φ) Y = Σ_a φ_a • yukawaPair (higgsGen a) Y` — **the full h.c.
  expression is the sum over the four real Higgs components**, each summand Hermitian
  (`yukawaPair_higgs_gen_hermitian`).
* **Specializations.** `yukawaPair_one` (`1` background), `yukawaPair_fixed_background`
  (`φ = e₀` and Hermitian `Y` give the mass term `2 • Y`), `yukawaPair_one_pauli` (a single `σ₁`
  component), `yukawaPair_zero`.
* **Gauge covariance and charge conservation.** `yukawaPair_gauge`: for `Uᴴ U = 1`,
  `yukawaPair (U A Uᴴ) (U Y Uᴴ) = U · yukawaPair A Y · Uᴴ`; `yukawaPair_charge`: a Hermitian `T`
  commuting with `A` and `Y` commutes with the insertion.
* **Four mass/Yukawa matrices with phases.** `SmYukawaData` carries `Yu, Yd, Ye, Yν` and four
  unit phases (`c c̄ = 1`; `SmYukawaData.upBlock`, `upBlock_phase_unit`), with the nontrivial
  complex-mixing example `exampleYukawa` (`exampleYukawa_mixing`: the `(0,1)` entry is `I`),
  **`exampleYukawa_not_hermitian`** (independent Hermiticity check: `Y` itself need not be
  Hermitian, the hermitianization does the work) and `exampleYukawa_pair_hermitian`.
* **Bounded currents.** `gaugeCurrent_bounded` and `yukawaCurrent_bounded` reuse
  `BookProof.SmCar.norm_fermiBilin_le` to give the `ℓ¹` operator bound P2's comparison consumes.

Not done by this packet: the 96-mode assembly `Σ_{x,y} M_{xy} a†_x a_y` of the full matter
Hamiltonian, the spinor action of `γ·∂` (so `h_Dirac` is still not an operator), the connection
between the free internal `U` and the gauge generators `smGen`, the gauge-field sector, any common
core, and the ESA/Faris–Lavine comparison. P2 is the next packet.

## 12. P2 executed (2026-11-09f)

`BookProof/Sm/ChapterSmFullMatterHamiltonian.lean` (641 lines, namespace `BookProof.SmFullMatter`)
now carries P2; it builds (`lake build BookProof`, 8913 jobs, no warnings from the module) and is
imported by `BookProof.lean` after `ChapterSmFullYukawaData`.  Acceptance of §4 is met as follows.

* **Every ledger term is present, as an elementary tensor.**
  `h_SM = Σⱼ πⱼ ⊗ Aⱼ + Σⱼ πⱼ² ⊗ Bⱼ + Σⱼ uⱼ ⊗ Jⱼ + 1 ⊗ M₀` is `smNormalForm D`: one finite sum
  per ledger family, each summand the elementary tensor `smTensorCore T M` with a bosonic factor
  `T` on `polyGaussCore 163` and an internal matrix `M` on the occupation basis.  The derivative
  families are the **genuine Gaussian-polynomial operators** `smMom j = CoreRep.op (momOp j)`
  (`πⱼ = −i∂ⱼ`) and `smKinetic j = smMom j ∘ smMom j` (`πⱼ² = −∂ⱼ²`), with
  `smPos j = CoreRep.op (mulOp (X j))` for the coordinates (the four real Higgs components are
  four of the `uⱼ`); no plane-wave parameter replaces the derivative.
* **No definition is rigged to make a theorem `rfl`.**  The bosonic factors are fixed first,
  independently of any symmetry claim, and are carried through `CoreRep.op`: the symmetries are
  those of `momOp`/`mulOp` on `polyGaussCore 163` (`momOp_polySym`, `mulOp_polySym`,
  `realCoeff_X`), not of a chosen representative.  `smNormalForm` is a plain finite sum of
  `smTensorCore`s, and the theorems about it are proved *about* that sum (below).
* **The common core.**  `SmBosSpace = L2d 163`, `SmCoupledSpace = PiLp 2 (fun _ : Finset (Fin 96)
  => SmBosSpace)` (the tensor product with the finite internal factor; `coupledSpace_norm_sq`
  gives `‖f‖² = Σ_S ‖f_S‖²`), and `SmCoupledCore = {f | ∀ S, f.ofLp S ∈ polyGaussCore 163}` with
  `coupledCore_ext` and **`coupledCore_dense`**: density is the finite-`ℓ²` reassembly of
  `polyGaussCore_dense`, not a new analytic input.
* **Invariance under each term.**  `smTensorCore T M : SmCoupledCore →ₗ SmCoupledCore`: the
  bosonic factor is core-to-core by definition (`coreComp`, `tensorComp`), so the codomain of
  every term *is* the common core and no separate invariance lemma is needed — the operator's
  type is the invariance statement.  `tensorComp_apply`, `tensorComp_add`, `tensorComp_smul`,
  `coreComp_add`, `coreComp_smul`, `coe_coreComp` are the exposed component lemmas.
* **Symmetry.**  `smTensorCore_symmetricOn'` takes a `SymmetricOn` bosonic factor
  (`CoreRep.symmetricOn_op` of `momOp_polySym`/`mulOp_polySym`) and a Hermitian internal matrix,
  via `star_transpose_sum`; `symmetricOn_add`/`symmetricOn_sum` close finite combinations and
  `symmetricOn_comp_self` gives `smKinetic_symmetricOn` from `smMom_symmetricOn` by
  `⟪T²x, y⟫ = ⟪Tx, Ty⟫ = ⟪x, T²y⟫`.  Hence **`smNormalForm_symmetricOn`**: the full normal form
  is symmetric on `SmCoupledCore` under `HermitianCoeffs D`.
* **Fermion parity.**  §1 proves `fockParity = (−1)^N` is an involution, symmetric and
  norm-preserving, with the anticommutation `P a_i = −a_i P`, `P a†_i = −a†_i P`, hence
  `matterBilin_parity`; §4 lifts it to the coupled core
  (`coupledParityCore := (coupledParity.comp SmCoupledCore.subtype).codRestrict SmCoupledCore …`)
  and proves `coupledParity_smTensorCore` from the parity grading of the coefficient matrix.
  Hence **`smNormalForm_parity`**: the normal form preserves fermion parity under
  `ParityGradedCoeffs D`, through `coupledParity_sum`.
* **Elementary-tensor action of the full normal form.**  **`smNormalForm_apply`** expands
  `(smNormalForm D f).ofLp A` into the four family sums, term by term, with the internal matrix
  acting on the occupation index and `tensorComp` on the bosonic argument — the ledger's
  component-by-component statement, obtained from `LinearMap.sum_apply`/`PiLp.add_apply`, not a
  new definition.

Not done by this packet: no 96-mode embedding of the P1 doublet dictionary `yukawaPair`/its
`SmYukawaData` (the coefficient matrices are the data `SmNormalFormData` carries), no spinor
action of `γ·∂`, no gauge-field generator action (`q_r ⊗ J_r` is the coordinate family, P5 builds
the gauge action), no essential self-adjointness/graph statement and no Faris–Lavine comparison —
those are P3/P4, and nothing here assumes them.

## 13. P3 executed, scalar half (2026-11-09g)

`BookProof/Sm/ChapterSmFullComparisonEsa.lean` (427 lines, namespace `BookProof.SmFullComparisonEsa`)
now carries the scalar comparison `N_SM` of §3; it builds (`lake build BookProof`, 8914 jobs, no
warnings from the module) and is imported by `BookProof.lean` after `ChapterSmFullMatterHamiltonian`.

* **The 43-coordinate kinetic subset, proved.**  `smXSet` is the three spatial coordinates,
  `smS = image smCoord univ` the 40 momentum-carrying ones; `smS_disjoint_smXSet` is
  `smMom_disjoint_spatial` transported through the `SmMom ≃ Fin 40` labelling and
  **`card_smFullS : smFullS.card = 43`** is the plan's recount as a theorem (`card_smS = 40`,
  `card_smXSet = 3`).  **`smFullS_disjoint_jet`**: no jet coordinate is kinetic, so no spatial
  derivative is added in a jet direction.
* **The potential.**  `smFullPotPoly P c = smPotPoly P c + Σ_(j : Fin 3) xⱼ²`, with
  `realCoeff_smFullPotPoly`, the pointwise form `polyW_smFullPotPoly` (sums of squares plus `c`)
  and **`one_le_polyW_smFullPotPoly`** (`1 ≤ W` for `1 ≤ c`): the polynomial lower bound the Kato
  input needs, from sums of squares.
* **The operator.**  `smFullComparison P c := hamCoreS (polyW …) smFullS` is `−Δ_S + W` on the
  Gauss–polynomial core, i.e. exactly the `N_SM` of §3 with the untouched 120 jets inside the
  degree-four `Σ_r Φ_r²` (potential) part.
* **The identification with the source operators.**  `smFullComparisonPhys P c` is
  `2 h_B + Σ_m q_m² + Σⱼ (πⱼ² + xⱼ²) + c` built from `smHamiltonian`, `smQL` and the P2 core
  factors `smMom`/`smPos` at the spatial coordinates, and **`smFullComparisonPhys_eq`** proves the
  two agree on the whole core.  The proof evaluates both sides on `pgLp p` and matches polynomials:
  `kinPolyS_union` (disjoint union), `kinPolyS_smXSet` (`momOp_momOp` on the spatial set),
  `sum_momOp_eq_kinPolyS` (`smS`), the potential distribution, and `smFullPoly_identity`.  Nothing
  is defined to make a theorem `rfl`: the right-hand side is a new combination of pre-existing
  operators, and the equality is the content.
* **Symmetry, positivity, dense core, ESA.**  `smFullComparison_symmetricOn`
  (`hamCoreS_symmetricOn`); **`smFullComparison_quadForm_nonneg`** — the quadratic form is
  `2·q(h_B) + q(Σq²) + Σ_i ‖π_i x‖² + Σ_i ‖x_i x‖² + c‖x‖²`, each term non-negative, using
  `quadForm_comp_self` for the squares; `polyGaussCore_dense'`; and **`smFullComparison_esa`** for
  every shift `c`, with `smFullComparison_esa_one_le` from `hamCoreS_esa` and the bounded symmetric
  shift (`KatoRellich.essentiallySelfAdjointOn_add_bounded`).

Not done by this packet (the remainder of P3): the tensor `N_SM ⊗ I_internal` on `SmCoupledCore`
(the P2 carrier, whose density is `coupledCore_dense`) and the `Comparison`/`IsGraphCore` data of
`BookProof.QgOuterFockCoreFL`.  Those consume no new analysis — the scalar comparison is complete —
but they are the interface P4's relative-bound estimate is stated on, so P4 starts by building
them.  Deliberately not assumed anywhere here: the relative bound `‖h_SM u‖ ≤ K‖(N_SM+I)u‖`, the
commutator form bound, or any ESA statement about `h_SM`.

## 14. P3 remainder, P4 transfer engine and the P1 coefficient matrices (2026-11-09h)

Three modules, all `sorry`-free and `axiom`-free, each building through `lake build BookProof`
(8916 jobs) with no warnings from itself.

### `BookProof/Sm/ChapterSmFullCoupledCore.lean` — the coupled comparison and the Faris–Lavine data

* `coupledOp T M` — the elementary tensor for a bosonic factor with codomain `L²` (the comparison
  operators `smFullComparison`, `smFlN`, `smHamiltonian` all have codomain `L²`, so P2's
  core-to-core `smTensorCore` cannot take them).  `coupledOp_one_apply`: for `M = 1` it is `T ⊗ I`
  componentwise.
* `coupledOp_symmetricOn`, `coupledOp_one_quadForm` (the coupled quadratic form is the sum of the
  componentwise ones) and `coupledOp_one_quadForm_nonneg`.
* **`smCoupledFullComparisonComparison`** — the coupled comparison `N_SM ⊗ I` as a Friedrichs
  `Comparison` on `SmCoupledCore`, with `smCoupledFullComparisonComparison_extends`; and
  **`smCoupledFlComparison`** — the same for the Faris–Lavine pair `N = 2h + Σ q² + c₀`.
* **`coupledOp_norm_le`** — the relative bound transfers: `‖T ⊗ M f‖ ≤ c√(pairSum M)‖(N ⊗ I + 1)f‖`,
  the coefficient matrix entering only through the Frobenius square sum `pairSum`.  The proof is
  Cauchy–Schwarz per internal row (`norm_sum_smul_sq_le`) plus the `ℓ²` reassembly
  (`coupledOp_one_add_norm_sq`).
* **`coupledOp_one_commForm_le`** — the commutator-form bound transfers with the same constant,
  from `coupledOp_one_commForm` (the coupled commutator form is the sum of the componentwise ones).
* **`smCoupledCoreData`** and **`smCoupledHamiltonian_esa`** — the `CoreData` package and essential
  self-adjointness of `h ⊗ I` on the common core from the graph-core property, with the relative
  bound `K = √(pairSum 1)` and the commutator constant `c = 1` of the scalar theory.

### P4 — the relative bound of the full normal form

`smTensorCore_eq_coupledOp` identifies P2's tensor with the `L²`-valued one, so
`smTensorCore_norm_le` is the engine applied to a core-to-core factor.  **`smNormalForm_norm_le`**:
if each bosonic family obeys `‖Tⱼ x‖ ≤ c‖(N + 1)x‖` on the core, then

```text
‖h_SM f‖ ≤ c · normalFormConst D · ‖(N ⊗ I + 1) f‖,
```

with `normalFormConst D = Σⱼ √(pairSum (D.mom j)) + Σⱼ √(pairSum (D.kinetic j))
+ Σⱼ √(pairSum (D.coord j)) + √(pairSum D.mass)`.  The proof is the term-by-term transfer plus the
triangle inequality; nothing about the normal form beyond its shape is used.

**What P4 still needs** (recorded, not assumed): the scalar relative bounds of the three families
`πⱼ`, `πⱼ²`, `uⱼ` against `N`.  The corpus proves the bound of the *combination* `h`
(`sm_norm_le_shift`, constant 1) and the transfer engine is now in place; what is missing is the
one-particle estimate for each family separately.  The commutator-form bound of the full normal
form is likewise transferred only for a diagonal internal factor (`coupledOp_one_commForm_le`);
for a general coefficient matrix it needs the bilinear pairing estimate
`|⟪T x, N y⟫| ≤ c(‖x‖² + ‖y‖²)`-type input, which is the same scalar analysis.

### `BookProof/Sm/ChapterSmFullYukawaCoeffs.lean` — the P1 dictionary in the coefficient matrices

* `fockBasis`, `fockMatrix` — the occupation basis and the matrix of an internal operator in it,
  with `fockMatrix_eq_inner`;
* **`fockMatrix_star`** — a symmetric internal operator has a Hermitian coefficient matrix (from
  `inner_conj_symm` and the symmetry);
* **`fockMatrix_parity`** — an internal operator commuting with `fockParity` has a parity-graded
  coefficient matrix, `fockSign S * M S T = M S T * fockSign T` (with the stronger statement
  `M S T = 0` unless the parities agree);
* `SmInternalData` — the internal data of the P1 dictionary: the coordinate `pos a` of each real
  Higgs component, the four second-quantized Higgs generators `matterBilin (higgs a)` (with
  `a ↦ yukawaPair (higgsGen a) Y`), the mass/Yukawa insertion `matterBilin mass`, and the
  Hermiticity of each (`higgsGen_hermitian`, `higgsField_hermitian`, `yukawaPair_hermitian`);
* **`SmInternalData.toNormalForm`** — the resulting `SmNormalFormData`: the Higgs generators in the
  coordinate family, the Yukawa insertion in the mass slot, and the zero matrix in both derivative
  families (`toNormalForm_mom_null`, `toNormalForm_kinetic_null` — no derivative is added in an
  internal direction);
* **`toNormalForm_hermitian`** and **`toNormalForm_parity`** — P2's `HermitianCoeffs` and
  `ParityGradedCoeffs` for the P1 data, from `matterBilin_symmetric`/`matterBilin_parity` and the
  entrywise sum lemmas `matrix_sum_hermitian`/`matrix_sum_parity`, so P2's
  `smNormalForm_symmetricOn` (**`toNormalForm_symmetricOn`**) and `smNormalForm_parity` apply.

Boundary: `pos : Fin 4 → Fin 163` is data, not derived, and no mass value is computed from the P1
couplings.  The statement is structural — the P1 dictionary satisfies the P2 hypotheses in the
occupation basis.

## 15. The per-family relative bounds, and the P1 normal-form bound (2026-11-10a)

`BookProof/Sm/ChapterSmFullFamilyBounds.lean`, `sorry`-free and `axiom`-free, building through
`lake build BookProof` (8917 jobs) with no warnings from itself.

§14 recorded what `smNormalForm_norm_le` still needs: a scalar relative bound
`‖Tⱼ x‖ ≤ c‖(N + 1)x‖` for each bosonic family, where the corpus had only the bound of the
combination `h`.  This module supplies it for every first-order family, with the absolute
constant `1`, and then applies it.

### The mechanism

* **`quadForm_le_half_norm_add_sq`** — for symmetric `A` with `quadForm A ≥ 0`,
  `quadForm A x ≤ ½‖A x + x‖²`.  The cross term of the shift *is* the quadratic form (so it is
  non-negative), and Cauchy–Schwarz plus `‖u‖² + ‖v‖² ≥ 2‖u‖‖v‖` closes it.  This is the only
  place where the argument uses anything about `N`, and it uses no spectral information.
* **`norm_le_shift_of_sq_le_quadForm`** — the transfer: `‖T x‖² ≤ 2 quadForm A x` implies
  `‖T x‖ ≤ 1 · ‖A x + x‖`, via `sq_le_sq`.

### The families

* **`smPi_norm_le_shift`** — the momentum family `πⱼ = −i∂ⱼ`, `j = smCoord m` (`m : Fin 40`), from
  `smPi_sq_le_quadForm_smFlN`: the momentum squares are half of `quadForm h`
  (`smHamiltonian_quadForm`), and `2 quadForm h` is a summand of `quadForm N` (`smFlN_quadForm`).
* **`smMomField_norm_le_shift`** and **`smPos_smCoord_norm_le_shift`** — the coordinate family
  `uⱼ` in the same `40` harmonic coordinates, from `smMomField_sq_le_quadForm_smFlN`: the
  harmonic part `Σ_m q_m²` of `N` is a sum of squares of exactly those multiplications
  (`smQL_quadForm`).
* **`smField_norm_le_shift`** — each of the `49` field polynomials `Ψ_r` of `smHamiltonian`, from
  `smField_sq_le_quadForm_smFlN`.

All three hold for every set of couplings, structure constants and electroweak generators, and
for every `c₀ ≥ 0`.

### Application

* **`smTensorCore_zero`** — the elementary tensor with a zero coefficient matrix vanishes.
* **`smNormalForm_norm_le_support`** — `smNormalForm_norm_le` with the per-family hypothesis
  required only where the coefficient matrix is non-zero (the index sets
  `Smom`, `Skin`, `Scoord` are part of the statement, with `hSmom : j ∉ Smom → D.mom j = 0`).
  The constant is unchanged: `c · normalFormConst D`.
* **`SmInternalData.toNormalForm_norm_le`** — the payoff for the P1 data: since
  `SmInternalData.toNormalForm` has zero derivative families, the bound

  ```text
  ‖h_P1 f‖ ≤ 1 · normalFormConst D · ‖(N ⊗ I + 1) f‖
  ```

  is **unconditional in `πⱼ`, `πⱼ²`, `uⱼ`** (it needs neither), with `N = 2h + Σ q² + c₀`,
  `c₀ ≥ 0`, and `c = 1` supplied by `smPos_smCoord_norm_le_shift` for the four Higgs coordinates
  and by `norm_le_norm_shift` for the mass slot.  Its one hypothesis is `hpos`: the four
  coordinates `D.pos a` are harmonic ones (`∃ m, D.pos a = smCoord m`).

### What is still open

* **`πⱼ²` (`smKinetic`) has no per-family bound here.**  `quadForm N` carries exactly one power
  of `πⱼ²`, so dominating `‖πⱼ² x‖` needs the quadratic form of `N` at `πⱼ x` — a second-order
  estimate, not the first-order one this module turns into a norm bound.  This is the remaining
  input of `smNormalForm_norm_le` for a general P2 normal form.
* **The coordinate family outside the `40` harmonic coordinates** is not bounded, and cannot be
  from `quadForm N` alone: `N` carries no `uⱼ²` term there.  `SmInternalData.toNormalForm_norm_le`
  therefore carries `hpos`; deriving that placement from the physical data is the separate
  obligation of §14's boundary note (`pos` is data, not derived).
* The commutator-form bound of the full normal form with non-scalar coefficient matrices is
  unchanged from §14 — still the bilinear-pairing estimate.

## 16. The commutator form with general matrices, the canonical placement, and the second-order
family (2026-11-10b)

`BookProof/Sm/ChapterSmFullNormalFormBounds.lean`, `sorry`-free and `axiom`-free, building through
`lake build BookProof` (8918 jobs) with no warnings from itself.

§15 named three remaining inputs.  This module closes the first two and reduces the third to a
single elliptic estimate.

### The commutator form with general coefficient matrices

`coupledOp_one_commForm_le` (§14) bounds the commutator form of `h ⊗ I` against `N ⊗ I`, i.e. of a
**scalar** factor coupled with the identity.  `smNormalForm_commForm_le` does the same for the full
normal form `Σⱼ Tⱼ ⊗ Mⱼ` with arbitrary coefficient matrices `Mⱼ`:

```text
|commForm (smNormalForm D) (N ⊗ 1) f| ≤ 4 c (normalFormConst D) ‖((N ⊗ 1) f + f)‖².
```

* **`coupledOp_self_norm_le`** — `‖(N ⊗ 1) f‖ ≤ 2‖((N ⊗ 1) f + f)‖`, from `‖x‖ ≤ ‖Nx + x‖`
  componentwise (`norm_le_norm_shift`) inside `coupledSpace_norm_sq == 1`'s sum.
* The proof is `commForm_eq` (`= −2 Im ⟪Hf, Nf⟫`) plus `|Im z| ≤ ‖z‖` and two factors:
  `smNormalForm_norm_le` for `‖Hf‖` and `coupledOp_self_norm_le` for `‖Nf‖`, both at the level of
  the **shifted graph norm squared**.
* That level is not an artefact of the proof.  For a scalar factor the imaginary part of one inner
  product `⟪T x, N x⟫` is bounded by the quadratic form of `N`; for general matrices the
  components of `Mⱼ` pair `T f_B` with `N f_A`, so only the product of the two norms is available.
  A `quadForm`-level bound would need the coefficient matrices diagonal.

### The canonical placement of the Higgs components

`pos` is *data*: which of the `163` oscillator coordinates carries the `a`-th real Higgs component.
§15's `hpos` (`∃ m, D.pos a = smCoord m`) was therefore a hypothesis of `toNormalForm_norm_le`.

* **`smCanonicalPos`** — the `a`-th component on the `a`-th harmonic coordinate `smCoord ⟨a⟩`.
* **`smCanonicalPos_harmonic`** — `∃ m, smCanonicalPos a = smCoord m`, by `rfl`.  This is `hpos`.
* **`SmInternalData.canonical`** — the P1 internal data at that placement.
* **`SmInternalData.canonical_toNormalForm_norm_le`** — §15's relative bound for the canonical P1
  data, with **no** hypothesis about the placement.

The remaining content of the statement is a modelling choice, not a proof obligation: the physics
fixes *that* the four Higgs modes are oscillator coordinate modes; among the harmonic coordinates
the choice of four is canonical up to relabelling.

### The second-order family `πⱼ²`

`N` carries exactly one power of `πⱼ²`, so a bound on `‖πⱼ² x‖` cannot come from `quadForm N` at
`x` (§15).  The module separates the part that needs no elliptic input from the part that does.

* **`pderiv_X_eq`**, **`pderiv_pderiv_comm`** — partial derivatives commute (not in Mathlib).
* **`derOp_comp_comm`** — `[∂ⱼ − ½xⱼ, ∂ₖ − ½xₖ] = 0`, since `∂ⱼ(xₖ · ) = xₖ · ∂ⱼ` for `j ≠ k`.
* **`momOp_comp_comm`**, **`CoreRep.op_comp`** (the transport is multiplicative),
  **`smPi_comp_comm`** — the `40` momentum operators `πₘ` commute pairwise.
* **`sq_norm_comp_le_sum`** — generic: for pairwise commuting symmetric `Tⱼ` on an inner-product
  space, `‖Tᵢ²x‖ ≤ ‖(Σⱼ Tⱼ²)x‖`.  `‖Σⱼ Tⱼ²x‖²` expands into the double sum
  `Σⱼₖ ‖TⱼTₖx‖²` — the cross terms are `⟪Tⱼ²x, Tₖ²x⟫ = ‖TⱼTₖx‖²` by symmetry and commutation —
  and `‖Tᵢ²x‖²` is its diagonal term.
* **`smPi_sq_norm_le_kineticSum`** — the instantiation: `‖πₘ²x‖ ≤ ‖(Σₘ πₘ²)x‖`.
* **`smKinetic_norm_le_shift`** — the reduction: if the kinetic sum satisfies
  `‖(Σₘ πₘ²)x‖ ≤ c‖Nx + x‖`, then every `smKinetic j` at a momentum coordinate does, with the
  same `c`.  This is exactly `hkin` of `smNormalForm_norm_le` in the `40` momentum directions.

**What remains** is the single estimate

```text
‖(Σₘ πₘ²) x‖ ≤ c ‖N x + x‖,        N = 2h + Σ q² + c₀,
```

i.e. the elliptic (Gårding) step: `Σₘ πₘ²` is the kinetic part of `N`, and the gap between bare
kinetic energy and `N` is the quartic potential, which does not commute with `∂ⱼ`.  Neither this
module nor `smNormalForm_norm_le` assumes it; both state it as a hypothesis, so the second-order
family is now a *single* unproved elliptic input rather than `163` independent ones.

## 17. The support-restricted commutator bound, the canonical P1 data at the commutator level,
## and diagonal coefficients (2026-11-10c)

Module: `BookProof/Sm/ChapterSmFullCommFormDiagonal.lean`.  Registered in `BookProof.lean`.

The two follow-ups requested after §16 — the commutator bound without family hypotheses, and the
diagonal-coefficient specialization at the quadratic-form level — close here unconditionally.  The
third item, the elliptic estimate for the kinetic sum, does not close: it is recorded below as the
named gap it is, not restated as a hypothesis under a different name.

### The commutator bound with support-restricted hypotheses

§16's `smNormalForm_commForm_le` asks for the scalar relative bound at **every** index of the three
bosonic families, which the P1 dictionary — whose two derivative families are zero — cannot
supply.  §15 already fixed the shape of the hypothesis for the norm bound
(`smNormalForm_norm_le_support`); §17 does the same for the commutator bound.

* **`abs_commForm_le_of_norm_le`** — the engine separated out of §16: from
  `‖H f‖ ≤ C ‖(N ⊗ 1 + 1) f‖` and `‖(N ⊗ 1) f‖ ≤ 2 ‖(N ⊗ 1 + 1) f‖` (the second is
  `coupledOp_self_norm_le`, from componentwise `norm_le_norm_shift`) it concludes
  `|commForm H (N ⊗ 1) f| ≤ 4 C ‖(N ⊗ 1 + 1) f‖²`.  The mechanism is
  `commForm_eq : commForm H N x = −2 Im ⟪H x, N x⟫`, so the imaginary part of one inner product
  is controlled by the product of two norms.
* **`smNormalForm_commForm_le_support`** — the support-restricted version, obtained by feeding
  `smNormalForm_norm_le_support` into the engine; the constant is again
  `4 c normalFormConst D`.

### The canonical P1 data at the commutator level

* **`SmInternalData.toNormalForm_commForm_le`** — the P1 dictionary: derivative families on the
  empty support, the four Higgs coordinates on `univ.image D.pos`, the mass slot from
  `norm_le_norm_shift`, and `c = 1` from `smPos_smCoord_norm_le_shift`.  This is the commutator
  analogue of §15's `toNormalForm_norm_le`.
* **`SmInternalData.canonical_toNormalForm_commForm_le`** — the same at §16's canonical placement,
  so **no** family hypothesis and **no** placement hypothesis remains:
  `|commForm h_P1 (N ⊗ 1) f| ≤ 4 normalFormConst · ‖(N ⊗ 1 + 1) f‖²`.

### Diagonal coefficient matrices: the quadratic-form level

§16 recorded the obstruction in its own text: with a general `Mⱼ`, the components `T f_B` are
paired with `N f_A`, and "a `quadForm`-level bound would need the coefficient matrices diagonal".
For a diagonal matrix that level is reached.

* **`coupledOp_diagonal_apply`** — `(T ⊗ diag d) f` has `A`-th component `d_A • T f_A`: a diagonal
  matrix pairs each component with itself.
* **`coupledOp_diagonal_commForm_eq`** —
  `commForm (T ⊗ diag d) (N ⊗ 1) f = Σ_A d_A · commForm T N f_A`, from `PiLp.inner_apply`,
  `inner_smul_left` and the scalarity of `d_A ∈ ℝ`.  This is the identity that makes the
  componentwise quadratic-form bound possible.
* **`coupledOp_diagonal_commForm_le`** — from the scalar input
  `|commForm T N y| ≤ c quadForm N y`, positivity of `quadForm N` and `d_A ≥ 0`:
  `|commForm (T ⊗ diag d) (N ⊗ 1) f| ≤ c (Σ_A d_A) quadForm (N ⊗ 1) f`, using
  `coupledOp_one_quadForm` for the right-hand side.  No shifted-graph-norm-squared factor remains.
* **`smHamiltonian_diagonal_commForm_le`** — the specialization to the canonical operator `h`,
  with `sm_commForm_le` (`c = 1`) as the scalar input:
  `|commForm (h ⊗ diag d) (N ⊗ 1) f| ≤ (Σ_A d_A) quadForm (N ⊗ 1) f`.

### The elliptic step: status

The single estimate §16 left open,

```text
‖(Σₘ πₘ²) x‖ ≤ c ‖N x + x‖,        N = 2h + Σ q² + c₀,
```

is **not** proved here, and the module says so.  It is not a formal consequence of the
quadratic-form bounds the corpus owns (`smPi_sq_le_quadForm_smFlN`, `smField_sq_le_quadForm_smFlN`):
those bound `‖πₘ x‖²` by `quadForm N x`, while the estimate is at the level of `‖πₘ² x‖`, i.e.
Kato relative boundedness of the second-order part with respect to `N`.  The corpus's *second-order
norm* bounds are all for the twisted derivative `coreD = ∂ − x/2` of the oscillator picture —
`norm_kinPoly_le_shiftNorm`, `‖pgLp (kinPoly p)‖ ≤ 3 ‖pgLp (harmP p) + pgLp p‖`, together with
`norm_harmPoly_mul_le_shiftNorm` and `norm_weighted_kin_le` in
`BookProof/ChapterGaussCoreQuadBounds.lean` — because there `kinPoly` *is* the Gaussian Laplacian.
The SM momenta are plain derivatives `∂`, and the substitution `∂ = coreD + x / 2` multiplies by a
coordinate: each such factor costs one power of the graph norm, so the twisted bound does not
transport.  The remaining options are (a) an interpolation (Gårding) inequality for the quartic
`W`, or (b) a norm-level bound for the twisted model written for *plain* `∂` in the Gaussian
picture, which the corpus does not have.  Until one of them lands, `hkin` stays a hypothesis of
`smNormalForm_norm_le` in the `40` momentum directions and nothing downstream assumes it.

## 18. Block-diagonal coefficient matrices over the four Higgs components (2026-11-10d)

Module: `BookProof/Sm/ChapterSmFullCommFormBlock.lean`.  Registered in `BookProof.lean`.

§17 reached the quadratic-form level for a **diagonal** coefficient matrix, where every component
sees the *same* bosonic operator `T` and only the scalar weight `d_A` varies.  The physically
faithful finite-dimensional shape is different: the four Higgs components each multiply their own
block, so the operator acting on a component is selected by the component's block.  This section
closes that generalization.

* **`blockMat blk d a`** — the `a`-th block of a diagonal matrix, cut out by the block index
  `blk : Finset (Fin 96) → Fin 4`.  `sum_blockMat` shows the four blocks reassemble into `diag d`,
  so the block structure is a partition of the diagonal entries and not a new hypothesis.
* **`blockOp T blk d = Σ_a T_a ⊗ blockMat blk d a`**, with `blockOp_apply`: component `A` is
  `d_A • T_{blk A} f_A`.  The four blocks carry four *different* operators; the diagonal case of
  §17 is the degenerate one where the family is constant.
* **`blockOp_commForm_eq`** — the identity survives in full:
  `commForm (blockOp T blk d) (N ⊗ 1) f = Σ_A d_A · commForm (T_{blk A}) N f_A`.  Block diagonality
  inside each block is all that §17's argument used, so the same rearrangement applies.
* **`blockOp_commForm_le`** — the quadratic-form-level bound, with the same constant as §17:
  from a scalar form bound `|commForm T_a N y| ≤ c quadForm N y` on each block's operator and
  `d_A ≥ 0`, `|commForm (blockOp T blk d) (N ⊗ 1) f| ≤ c (Σ_A d_A) quadForm (N ⊗ 1) f`.
* **`blockOp_norm_le`** — the norm-level sibling.  Multiplication families carry no scalar
  `commForm` bound in the corpus (they enter through relative *norm* bounds), so the second half
  of the module works at the norm level: from `‖T_a x‖ ≤ c ‖N x + x‖` and `|d_A| ≤ K`,
  `‖blockOp T blk d f‖ ≤ c K ‖(N ⊗ 1 + 1) f‖`, assembled through `coupledSpace_norm_sq` and
  `coupledOp_one_add_norm_sq`.
* **The four Higgs components.**  `smPos_block_norm_le` instantiates `T_a = u_{D.pos a}` against the
  SM comparison `smFlN` (constant `1` per block, from `smPos_smCoord_norm_le_shift`), and
  `smPos_block_commForm_le` feeds it to §17's engine `abs_commForm_le_of_norm_le`, giving
  `|commForm (blockOp u blk d) (N ⊗ 1) f| ≤ 4 K ‖(N ⊗ 1 + 1) f‖²`.  At the canonical placement
  `smCanonicalPos` the statement is `smCanonical_smPos_block_commForm_le`, with **no** hypothesis
  on the placement left.

Not claimed: a bound with a *non-diagonal* block interior.  The identity above uses only that the
matrix is diagonal inside each block, so a general Hermitian `M` still leaves the cross-component
pairing of §16.

## 19. The kinetic sum as a plain Laplacian, and the interpolation half of the elliptic estimate
## (2026-11-10e)

Module: `BookProof/Sm/ChapterSmKineticElliptic.lean`.  Registered in `BookProof.lean`.

### Correction of §17's reading of the derivative mismatch

§17 (and §16 before it) described the elliptic step as blocked by a derivative mismatch: the SM
momenta were said to be *plain* derivatives while the corpus's second-order bounds were for the
*twisted* `coreD = ∂ − x/2`, with the substitution `∂ = coreD + x/2` costing a power of the graph
norm per factor.  **That reading is wrong.**  `coreD` is the twisted derivative on *polynomials*,
but `kinPoly p = −Σ_j coreD_j (coreD_j p)` is the plain Laplacian of the *function*
`pgFun p = p · e^{−‖x‖²/4}`: `lapCS_pgFun` is exactly `Δ_S (pgFun p) = pgFun (kinPolyS S p)`.  Since
`momOp j = (−i) • coreD j` and `(−i)² = −1`, the transported momentum squared is the plain second
derivative in the function picture, so the corpus's `norm_kinPoly_le_shiftNorm` *is* the
plain-derivative analogue of the requested bound, and the SM kinetic sum is a plain partial
Laplacian.  This is now proved rather than argued:

* **`smPi_apply_pgLp_core` / `smPi_apply_pgLp`** — `π_m ⟨pgLp p⟩ = ⟨pgLp (momOp (smCoord m) p)⟩`.
* **`kineticSum_apply_pgLp` / `kineticSum_norm_pgLp`** — `Σ_m π_m (π_m x) = ⟨pgLp (kinPolyS smS p)⟩`
  for `x = ⟨pgLp p⟩`, and hence `‖Σ_m π_m² x‖ = ‖pgLp (kinPolyS smS p)‖`.  This is
  `sum_momOp_eq_kinPolyS` at the level of the core.

The remaining obstruction is therefore *only* the SM's quartic potential `W = Σ_r Φ_r² + Σ_m q_m² +
c₀`, because `norm_sq_harmPoly_mul_le` — the uncertainty-bound step behind
`norm_kinPoly_le_shiftNorm` — controls the *quadratic* `harmPoly` against the oscillator's own graph
norm, and there is no quartic analogue.

### The elliptic estimate reduced to one polynomial inequality

* **`smFlN_apply_pgLp`** — the comparison in polynomial coordinates,
  `N ⟨pgLp p⟩ = pgLp (kinPolyS smS p + smPotPoly P c₀ * p)` (from `smFlN_eq_hamCoreS`,
  `hamCoreS_pgLp`, `potLp_polyW`).
* **`kineticSum_norm_le_of_poly`** — the whole analytic content of §16's `hkin` isolated in **one**
  inequality, of exactly the shape `norm_kinPoly_le_shiftNorm` but with the SM comparison on the
  right:

```text
hpoly :  ∀ p, ‖pgLp (kinPolyS smS p)‖ ≤ c ‖pgLp (kinPolyS smS p + smPotPoly P c₀ * p) + pgLp p‖
        ⇒  ∀ x, ‖(Σ_m π_m²) x‖ ≤ c ‖N x + x‖.
```

  `hpoly` is the named gap of §19.  It is not assumed downstream and not restated under another
  name: it is the precise statement a Gårding/ellipticity argument has to supply.

### The interpolation half (closing the *first-order* side)

The corpus had no interpolation mechanism at all.  This section supplies the classical one, which
turns a bound on a square into a bound on the operator itself:

* **`sq_norm_le_norm_comp_mul_norm`** — for core-symmetric `T`, `‖T x‖² = ⟪T²x, x⟫ ≤ ‖T²x‖ ‖x‖`.
* **`sq_norm_le_of_comp_self_eps`** — its ε-form, i.e. Young's inequality:
  `‖T x‖² ≤ ε ‖T²x‖² + (4ε)⁻¹ ‖x‖²` for every `ε > 0`.  This is the Gårding interpolation in the
  form that trades a second-order term against a zeroth-order one with an arbitrarily small
  coefficient.
* **`smMom_norm_le_shift_of_kineticSum`** — fed with the kinetic-sum estimate and `‖x‖ ≤ ‖N x + x‖`,
  the interpolation gives `‖π_m x‖ ≤ √c ‖N x + x‖`: the first-order momentum family needs **no**
  relative bound of its own.
* **`smNormalForm_norm_le_of_kineticSum`** — hence §15's second-order family bound holds with the
  hypothesis `hmom` **removed**: the momentum slot now only records where `D.mom` is supported
  (`∀ j ∉ image smMomCoordFin univ, D.mom j = 0`), and the constant passes from `√c` to `c` because
  `c ≥ 1`.  The whole P2 relative bound rests on the single elliptic input.

### What is still open

For a quartic `W`, applying the ε-form requires `‖W²x‖` dominated by `‖N x + x‖`, which is the
elliptic estimate itself; there is no circular shortcut and none is taken.  §19's gap is `hpoly`;
everything else in the SM chain above is proved, `sorry`-free and `axiom`-free.

## 20. Block-diagonal operators with Hermitian block interiors (2026-11-10f)

Module: `BookProof/Sm/ChapterSmFullCommFormBlockHermitian.lean`.  Registered in `BookProof.lean`.

§18 let the four blocks carry four different *operators* while the interior of each block stayed a
scalar `d A`, and said so in its closing note.  This section reaches a full matrix interior at the
norm level — the level the commutator bound is assembled from — so a block may now be any complex
matrix, in particular a Hermitian one.

* **`blockOpMat T M = Σ_a T_a ⊗ M_a`** — no block index is needed, because the support of `M a` *is*
  the block.  The condition that makes it block-diagonal is
  `hsupp : M a A B ≠ 0 → blk A = a`; with `M a = blockMat blk d a` it holds by construction, and
  `blockOp_eq_blockOpMat` records `blockOp` as the special case.
* **`blockOpMat_apply_of_supp`** — component `A` is met only by its own block's matrix, so
  `(blockOpMat T M f).ofLp A = Σ_B M_{blk A} A B • T_{blk A} f_B`.
* **`sq_sum_mul_le_sum_mul_sq`** — the weighted Cauchy–Schwarz step `(Σ w g)² ≤ (Σ w)(Σ w g²)`.
* **`blockOpMat_norm_sq_le`, `blockOpMat_norm_le`** — **Schur's test**:
  `‖blockOpMat T M f‖ ≤ c √(ρ κ) ‖N⊗1 f + f‖`, where `ρ` and `κ` bound the row sums
  `rowSum M blk A = Σ_B |M_{blk A} A B|` and the column sums `colSum M blk B = Σ_A |M_{blk A} A B|`.
  For a diagonal interior both equal `sup_A |d A|` (`rowSum_blockMat`, `colSum_blockMat`), so the
  constant is exactly §18's `c K`: the generalization degrades nothing.  A plain Cauchy–Schwarz over
  the pair `(A, B)` would instead have cost `√96` — the number of internal components — which is why
  the bound is stated with the two Schur sums rather than a Hilbert–Schmidt norm.  That choice is the
  technical content of the section.
* **The Higgs family with Hermitian interiors** — `smPos_blockMat_norm_le`,
  `smPos_blockMat_commForm_le` (through §17's engine `abs_commForm_le_of_norm_le`) and
  `smCanonical_smPos_blockMat_commForm_le` at the canonical placement.

**Still not claimed:** the *form-level* identity `commForm = Σ_A d_A commForm` of §18 does not survive
a non-diagonal interior.  Component `A` then pairs `T f_B` with `N f_A` for `B ≠ A`, and the imaginary
part of that cross pairing is not a scalar form bound of `T` — it would need a bound on
`Im ⟪T f_B, N f_A⟧` for `B ≠ A`, which no module of the corpus states.  The commutator bound is
therefore obtained from the norm bound, exactly as §18 did for the multiplication families.

## 21. The P1 Yukawa dictionary's four Higgs coefficient matrices (2026-11-10g)

Module: `BookProof/Sm/ChapterSmFullCommFormBlockP1.lean`.  Registered in `BookProof.lean`.

§20 is abstract in its matrix family; this section instantiates it at the dictionary that the SM
actually uses.

* **`p1HiggsMat D a = fockMatrix (matterBilin (D.higgs a))`** — the `a`-th Higgs generator of the P1
  dictionary in the occupation basis.  These are the matrices §18 had to leave as scalar weights.
* **`SmInternalData.toNormalForm_coord_eq`** — the normal form's coordinate family is built from
  exactly these four matrices: `D.toNormalForm.coord j = Σ_a [D.pos a = j] · p1HiggsMat D a`.
* **`toNormalForm_coord_eq_p1HiggsMat`** — for an injective placement the coordinate matrix at
  `D.pos a` *is* `p1HiggsMat D a`, so the four blocks carry one Higgs component each and no mixing.
* **`p1HiggsMat_hermitian`** — the four matrices are Hermitian, from `D.higgsHermitian` through
  `matterBilin_symmetric` and `fockMatrix_star`.  This is what makes the interiors admissible for §20:
  they are genuinely non-diagonal, since `matterBilin` sums over the `96²` mode pairs.
* **`fockMatrix_entry_norm_le`** — the only uniform entry bound available, the `ℓ¹` bound of
  `matterBilin` read in the occupation basis, which makes the Schur sums finite.
* **`smPos_p1Higgs_commForm_le`, `smCanonical_smPos_p1Higgs_commForm_le`** — the §20 commutator bound
  for `Σ_a u_{pos a} ⊗ p1HiggsMat D a`, with no hypothesis on the placement left at `smCanonicalPos`.

**The constant is data, and this section says so rather than inventing a number.**  The Schur data
`ρ`, `κ` are the row and column sums of the four P1 matrices; they are finite but their values belong
to the dictionary, and unlike the four Higgs *coordinates* — whose relative bound is §15's constant
`1` — the non-diagonal interiors admit no uniform constant.  They therefore stay as hypotheses of the
concrete bound.

## 22. The quartic Gårding step: what the attempt produced (2026-11-10h)

Module: `BookProof/Sm/ChapterSmKineticGarding.lean`.  Registered in `BookProof.lean`.

§19 reduced §16's `hkin` to the one polynomial inequality `hpoly`.  This section reports the outcome
of attempting `hpoly` itself: **it is still not proved**, and the section pins down exactly what is
missing instead of renaming the gap.

* **`kinetic_le_shift_add_pot`** — the Gårding factorization
  `‖Δ p‖ ≤ ‖Δp + Wp + p‖ + ‖Wp + p‖`.  Nothing but the potential stands between `hpoly` and the
  elliptic estimate.
* **`PotSelfBound P c₀ β`** — the self-bound of the potential:
  `∀ p, ‖W p + p‖ ≤ β ‖Δ_S p + W p + p‖`.  This is the Kato-type self-boundedness of `W` with respect
  to `−Δ_S + W`, the standard first step of every ellipticity proof for a polynomial potential.
* **`kineticSum_norm_le_of_pot_self_bound`** — hence the elliptic estimate, with `c = 1 + β`.
* **`smNormalForm_norm_le_of_pot_self_bound`** — the composition with §19's interpolation half: §15's
  second-order family bound now rests on `PotSelfBound` **alone**.  The whole P2 relative bound for the
  SM is one inequality about the quartic potential.

**Why the corpus cannot supply `PotSelfBound`.**  The standard proof reads the sign of the cross term

```text
Re ⟪W u, −Δ u⟫ = ‖√W ∇u‖² + Re ⟪u ∇W, ∇u⟫,
```

whose first term is non-negative, and then interpolates `∇` between `L²` and the graph norm.  Neither
ingredient exists here: there is no integration-by-parts identity for a polynomial weight on the
Gaussian core (the core lemmas are algebraic — `pgLp_add'`, `lapCS_pgFun` — or inner-product
identities for core *endomorphisms*, while `W` is a multiplication operator), and the corpus's only
uncertainty-type bound, `norm_sq_harmPoly_mul_le`, controls the **quadratic** weight `harmPoly`
against the oscillator's own graph norm.  That is exactly what makes `norm_kinPoly_le_shiftNorm` work,
and it has no quartic analogue.

The trap the attempt hit first is worth recording: `one_le_polyW_smPotPoly` gives `W ≥ 1` pointwise,
and one is tempted to conclude `PotSelfBound` from positivity.  It does not follow.  A polynomial
concentrating at high frequency where `W` is of order one has a huge `‖Δp‖` and a moderate `‖Wp‖`, so
the self-bound needs the elliptic bootstrap itself.  `hpoly` (§19) and `PotSelfBound` (§22) are two
equivalent spellings of one open problem, and neither is assumed downstream.

## 23. The weighted integration-by-parts identity on the Gauss–polynomial core (2026-11-10k)

Module: `BookProof/Sm/ChapterSmGaussWeightedIbp.lean`.  Registered in `BookProof.lean`.

§22 named the missing tool for the quartic step: the sign of the cross term,
`Re ⟪W u, −Δ u⟫ = ‖√W ∇u‖² + Re ⟪u ∇W, ∇u⟫`, whose first term is non-negative.  This section
supplies that identity on the core where the corpus computes — the Gauss–polynomial core, where every
inner product is a Gaussian integral `gaussInt` of polynomials.

The statement is the discrete form of the identity, in the corpus's own conventions: `−Δ_S` realized
by `kinPolyS S`, `∇` by the twisted derivative `coreD j = ∂_j − x_j/2`, and the weight `Q` a
real-coefficient polynomial.

* **`gaussInt_weighted_kinPolyS`** — the identity in integral form:
  `⟪Q u, −Δ_S u⟫ = ∑_{j∈S} (⟪∂_j Q · u, ∇_j u⟫ + ⟪Q ∇_j u, ∇_j u⟫)`.  Proof: `gaussInt_kinPolyS`
  (the corpus's integration by parts) plus `coreD_mul` (its Leibniz rule) — the weight moves inside
  the derivative and leaves exactly the two terms.  There is nothing else in the proof, which is why
  the identity was missing rather than hard.
* **`inner_weighted_kinPolyS`** — the same identity with the left-hand side written
  `Re ⟪Q u, −Δ_S u⟫` for `u = pgLp p`.
* **`eval_cpoly_self_eq`, `eval_weighted_self_re`** — pointwise, the weighted self-pairing is the
  weight times the squared modulus, `(Q q, q) ↦ Q(x)‖q(x)‖²`.
* **`gaussInt_weighted_self_nonneg`, `inner_weighted_kinPolyS_dirichlet_nonneg`** — hence
  `‖√Q ∇u‖² ≥ 0` whenever `Q ≥ 0` pointwise.  This is the sign the elliptic argument needs, and it is
  now a theorem instead of an appeal to positivity.
* **`inner_weighted_kinPolyS_ge`** — the resulting semi-boundedness direction:
  `Re ⟪Q u, −Δ_S u⟫ ≥ ∑_{j∈S} Re ⟪u ∇_j Q, ∇_j u⟫`.
* **`smPotPoly_nonneg`, `sm_weighted_kinetic_ibp`, `sm_weighted_kinetic_ibp_ge`** — the instance at
  the SM comparison, where the weight is the quartic potential `smPotPoly P c₀` and `S = smS`.  The
  non-negativity of the weight comes from `polyW_smPotPoly` and `c₀ ≥ 0`, so the instance carries only
  `0 ≤ c₀`.

**What this does not do.**  It is the first ingredient of §22's `PotSelfBound` and not a proof of it.
The identity gives the sign; the estimate `‖W p + p‖ ≤ β ‖Δ_S p + W p + p‖` additionally needs the
commutator term controlled by the graph norm of `−Δ_S + W + 1`, which requires interpolating `∇`
between `L²` and the graph norm.  The corpus has no bound of that shape for a quartic weight, so
`PotSelfBound` remains a hypothesis downstream — but it now has one fewer unproved ingredient than
§22 left it with.

## 24. The Schur constants of the four P1 Higgs matrices, made explicit (2026-11-10i)

Module: `BookProof/Sm/ChapterSmFullCommFormBlockP1Schur.lean`.  Registered in `BookProof.lean`.

§21 proved the P1 commutator bound with the two Schur sums `ρ`, `κ` as hypotheses and recorded that
they are finite because the matrices live on a finite type.  "Finite" is not a number, so the bound
could not be applied without supplying them by hand.  This section supplies them.

* **`p1HiggsMass D a = ∑_{ij} ‖D.higgs a i j‖`**, **`p1HiggsMassTotal D = ∑_a p1HiggsMass D a`**,
  **`fockMass = ∑_T ‖fockBasis T‖`** — the three numbers everything is built from.
* **`p1Higgs_entry_le`** — `‖p1HiggsMat D a S T‖ ≤ p1HiggsMassTotal D * ‖fockBasis T‖`, uniform in the
  component `a`; this is `fockMatrix_entry_norm_le` of §21 with the component's mass replaced by the
  total.
* **`p1HiggsRowRadius D = p1HiggsMassTotal D * fockMass`** and
  **`p1HiggsColRadius D = card (Finset (Fin 96)) * p1HiggsRowRadius D`** — the two radii, with
  `rowSum_p1Higgs_le` and `colSum_p1Higgs_le` proving the Schur bounds.
* **`smCanonical_smPos_p1Higgs_commForm_le_radius`**, **`smPos_p1Higgs_commForm_le_radius`** — §21's
  commutator bounds at those radii: no Schur hypothesis left.

**Honesty about the size.**  These constants are crude on purpose: `ℓ¹` mass is not the operator norm,
`fockMass` is not `1` because the corpus records no normalisation of `fockBasis`, and the column count
is the full cardinality of `Finset (Fin 96)` rather than the number of occupied sectors.  Their role is
to be explicit and finite — what a Schur hypothesis needs in order to be discharged.  A sharp constant
is a computation on the dictionary, not a theorem about it.

## 25. The operator-valued Schur test: no block-diagonal support condition (2026-11-10j)

Module: `BookProof/Sm/ChapterSmFullCommFormBlockGeneral.lean`.  Registered in `BookProof.lean`.

§20's bound assumed `hsupp : M a A B ≠ 0 → blk A = a`: the `a`-th matrix may only reach the block `a`.
That covers block-diagonal families, in particular the P1 dictionary, but not one that mixes blocks —
and the SM's Yukawa couplings do mix them.

* **`weightSum M A B = ∑_a ‖M_a A B‖`**, **`rowSumGen`**, **`colSumGen`** — the Schur weight and the two
  general Schur sums.
* **`weightSum_eq_of_supp`** — under §20's `hsupp` the weight collapses to a single term, so
  `rowSumGen`/`colSumGen` are §20's `rowSum`/`colSum`.  The general bound is therefore a strict
  extension, not a weaker parallel theory, and the diagonal constant is recovered exactly.
* **`blockOpMat_apply_general`** — component `A` is `∑_a ∑_B (M_a)_{A B} • T_a f_B`, with no support
  hypothesis.
* **`blockOpMat_component_le_general`, `blockOpMat_norm_sq_le_general`, `blockOpMat_norm_le_general`** —
  Schur's test with the constant `c √(ρ κ)` from the two general sums.
* **`smPos_blockMat_norm_le_general`, `smPos_blockMat_commForm_le_general`** — the SM Higgs family for an
  arbitrary coefficient family that may mix blocks.
* **`p1HiggsGeneralRowRadius`, `p1HiggsGeneralColRadius`, `rowSumGen_p1Higgs_le`,
  `colSumGen_p1Higgs_le`** — §24's radii with the one factor the mixing costs, `card (Fin 4) = 4`.
* **`smCanonical_p1Higgs_commForm_le_unconditional`** — the payoff: the commutator bound for the P1
  Yukawa dictionary with **no hypothesis at all** beyond `0 ≤ c₀`.  The support condition is gone, the
  Schur data is explicit, and the placement is canonical.

## 26. The gradient interpolation from the weighted IBP identity (2026-11-10l)

Module: `BookProof/Sm/ChapterSmGradInterpolation.lean`.  Registered in `BookProof.lean`.

§23 proved the sign identity of the commutator term and said that closing §22's `PotSelfBound` still
needs an interpolation of `∇` between `L²` and the graph norm.  This section proves the interpolation
the identity actually affords, and states precisely why it does **not** close the self-bound.

* **`norm_coreD_sq_le_weighted`** — one coordinate of the domination `‖∇_j p‖² ≤ ‖√W ∇_j p‖²`, from
  `W ≥ 1` pointwise and §23's `eval_weighted_self_re`.
* **`abs_cross_le_op`** — the commutator term is a Hilbert–Schmidt pairing:
  `|Re ⟪(∂_j W)p, ∇_j p⟫| ≤ ‖(∂_j W) p‖ ‖∇_j p‖`, via `inner_pgLp_pgLp` and Cauchy–Schwarz.
* **`mul_le_half_add_sq`** — `2ab ≤ a² + b²`.
* **`dirichlet_le_weighted_form`** — the interpolation proper:

  ```text
  ∑_{j∈S} ‖∇_j p‖²  ≤  2 Re ⟪W p, −Δ_S p⟫  +  ∑_{j∈S} ‖(∂_j W) p‖²,
  ```

  and **`sm_dirichlet_le_weighted_form`** at the quartic potential, where `W ≥ 1` is
  `one_le_polyW_smPotPoly` for `c₀ ≥ 1`.
* **`potSelfBound_of_kinetic_bound`** — the **converse** of §22's reduction: §19's `hpoly`
  (`‖Δ_S p‖ ≤ c ‖(−Δ_S + W + 1)p‖`) implies `PotSelfBound P c₀ (1 + c)`.  §22 asserted that the two
  are "two equivalent spellings of one open problem"; this makes the missing direction a theorem.

**Why the interpolation is not the self-bound.**  Two obstructions, both recorded in the module.

1. The term `∑_j ‖(∂_j W)p‖²` is not absorbable: `W` has degree four, so `∂_j W` has degree three and
   `|∇W|²` has degree six, and there is **no constant** `C` with `|∇W(x)|² ≤ C W(x)` as `x → ∞`.  That
   inequality is the hypothesis every absorption of the commutator term requires, so the interpolation
   cannot be reduced to a statement about `W` alone.
2. The direction is wrong for the self-bound in any case: the interpolation bounds `∇` **by** the form,
   while `PotSelfBound` asks for the *degree-four* term to be dominated by the form.  By
   `potSelfBound_of_kinetic_bound` that is exactly `hpoly`, i.e. the open problem itself.

The net effect is that §23+§26 give the sign and every size estimate the sign affords, and the one
thing they cannot give — a **reverse** elliptic estimate `‖W p‖ ≲ ‖(−Δ_S + W + 1)p‖` — is what
`PotSelfBound` is.  `PotSelfBound` stays a hypothesis downstream, and §26 assumes nothing away.

## 27. The P1 Schur radii as operator norms (2026-11-10l)

Module: `BookProof/Sm/ChapterSmFullCommFormBlockP1OpNorm.lean`.  Registered in `BookProof.lean`.

§24's radii were built from the `ℓ¹` mass of the internal matrices times the basis mass — a sum over
**every entry**, while a Schur row bound only needs a bound on **each row**.  This section uses the
norm the row bound calls for: Mathlib's `L^∞` operator norm on a finite matrix, which is the supremum
of the row sums (`Matrix.linfty_opNorm_def`, `open scoped Matrix.Norms.Operator`).

* **`row_le_opNorm`**, **`row_norm_le_opNorm`**, **`entry_le_opNorm`** — every row sum, the sup norm
  of every row, and every entry are bounded by the operator norm.
* **`norm_le_of_row_le`** — conversely, a uniform row bound bounds the operator norm.
* **`p1HiggsOpMass D a = ‖p1HiggsMat D a‖`**, **`p1HiggsOpRowRadius D = ∑_a p1HiggsOpMass D a`**,
  **`p1HiggsOpColRadius D = card (Finset (Fin 96)) * p1HiggsOpRowRadius D`** — the radii.
* **`rowSum_p1Higgs_le_opRadius`**, **`colSum_p1Higgs_le_opRadius`** — the two Schur bounds, so
  `smPos_p1Higgs_commForm_le_opRadius` / `smCanonical_p1Higgs_commForm_le_opRadius` are §21's bounds
  with no Schur data left.
* **`p1Higgs_entry_le_own`** — each P1 matrix obeys the entrywise bound of **its own** internal matrix
  (not the total), which is what makes the comparison sharp.
* **`p1HiggsOpMass_le_mass`**, **`p1HiggsOpRowRadius_le_rowRadius`**,
  **`p1HiggsOpColRadius_le_colRadius`** — the new radii are at most §24's, and hence at most §25's.
* **`rowSumGen_p1Higgs_le_opRowRadius`**, **`colSumGen_p1Higgs_le_opColRadius`**, and the payoff
  **`smCanonical_p1Higgs_commForm_le_opRadius_unconditional`** — the mixing-block bound of §25 at the
  operator-norm radii, still with no hypothesis beyond `0 ≤ c₀`.

The `fockMass` factor is gone entirely: the `L^∞` norm is defined on the entries, so the unrecorded
normalisation of `fockBasis` no longer enters the constant.  What remains crude is the column count,
which is still the full cardinality of `Finset (Fin 96)`.

## 28. A Yukawa family that provably mixes blocks (2026-11-10l)

Module: `BookProof/Sm/ChapterSmFullCommFormBlockYukawaMixing.lean`.  Registered in `BookProof.lean`.

§25 removed §20's support condition but its example was the P1 dictionary itself, where the mixing is
a property of the second-quantized Higgs generators that the corpus never computes entrywise.  This
section supplies a family whose mixing is **provable**, so §25's test is applied to a family §20
provably cannot accept, and the price of mixing is visible as a constant.

* **`occDiag`**, **`mixYuk`** — the degenerate number-conserving Yukawa: components `0` and `1` both
  couple the occupation diagonal with unit strength, components `2`, `3` vanish.  This is the
  situation of a Higgs doublet whose two members share a coupling pattern.
* **`mixYuk_unsupported`** — **no** `blk` satisfies §20's condition: row `∅` has a nonzero entry for
  component `0` and for component `1`, forcing `blk ∅ = 0` and `blk ∅ = 1`.  §20's theorem cannot be
  instantiated here; §25's is required, not merely convenient.
* **`weightSum_mixYuk`**, **`rowSumGen_mixYuk`**, **`colSumGen_mixYuk`** — both general Schur sums are
  `2`, so §25's constant is `4 √(2 · 2) = 8`; **`mixYuk_commForm_le`** is the resulting commutator
  bound.
* **`p1HiggsMix D a = p1HiggsMat D a + mixYuk a`** — the dictionary with the degenerate pair added,
  which mixes blocks for the same reason.
* **`weightSum_p1HiggsMix_le`**, **`rowSumGen_p1HiggsMix_le`** (`≤ p1HiggsGeneralOpRowRadius D + 2`),
  **`colSumGen_p1HiggsMix_le`** (`≤ card * (p1HiggsGeneralOpRowRadius D + 2)`), and
  **`p1HiggsMix_commForm_le`** — mixing costs one *additive* term per degenerate component, not the
  bound.

These models demonstrate the method; they are not a claim about the SM's Yukawa matrices, whose block
structure is not computed in the corpus.  What is proved is that when mixing is present the general
Schur test still yields a finite explicit constant, and what that constant costs.

## 29. The occupation basis is orthonormal (2026-11-10m)

Module: `BookProof/Sm/ChapterSmFockBasisNormalised.lean`.  Registered in `BookProof.lean`.

§24 recorded that `fockMass = ∑_T ‖fockBasis T‖` is not known to be `1`, because the corpus never
states the normalisation of the occupation basis, and carried it as a factor in both radii.  That was
the last unknown quantity in §24's constant, and it is a two-line computation.

* **`fockBasis_norm`** — `‖fockBasis S‖ = 1`.  The basis vector is the delta function at `S`, so its
  squared norm is a single entry of modulus one; the proof sums `‖·‖²` over the occupied sets.
* **`fockMass_eq_card`**, **`fockMass_eq_two_pow`** — `fockMass = card (Finset (Fin 96)) = 2 ^ 96`,
  `fockMass_pos`.
* **`p1HiggsRowRadius_eq`**, **`p1HiggsColRadius_eq`** and the `2 ^ 96` forms — §24's radii with the
  basis mass evaluated: `p1HiggsMassTotal D * 2 ^ 96` and `p1HiggsMassTotal D * (2 ^ 96) ^ 2`.
* **`rowSum_p1Higgs_le_mass_card`**, **`colSum_p1Higgs_le_mass_card_sq`** — §24's Schur bounds at the
  evaluated radii.

What is left crude is not the basis but the route: the `ℓ¹` mass is not an operator norm and the
column count is the full cardinality.  §27 already removed both by switching to `L^∞` operator norms,
which is why this section does not re-derive §24's bound as the recommended one.

## 30. The block structure of `p1HiggsMat`, and a dictionary with none (2026-11-10m)

Module: `BookProof/Sm/ChapterSmP1BlockStructure.lean`.  Registered in `BookProof.lean`.

§20's commutator bound needs `blk : Finset (Fin 96) → Fin 4` with `p1HiggsMat D a A B ≠ 0 → blk A = a`.
§21 assumed it, §25/§28 removed it, and none of them asked whether the P1 dictionary itself has one.
This section answers both directions.

* **`p1HiggsMat_of_card_ne`**, **`p1HiggsMat_card_eq`** — every term of `matterBilin` is `a†_i a_j`,
  which removes one mode and inserts one, so `p1HiggsMat D a S T ≠ 0` forces `S.card = T.card`.  The
  blocks the dictionary does have are the `97` occupation numbers, and they are **the same blocks for
  all four components**: occupation number does not refer to `a`.  They are therefore too coarse to
  be §20's `blk`; declining to say so would have hidden that §20's hypothesis was never available.
* **`degHiggsData`**, **`matterBilin_one_eq_fermiEnergy`**, **`p1HiggsMat_degHiggs_eq`**,
  **`p1HiggsMat_degHiggs_apply`** — the fully degenerate dictionary (four equal identity components,
  the extreme degenerate doublet) is the number operator, `(S.card : ℂ)` on the occupation diagonal.
* **`degHiggs_no_support`** — **no** `blk` satisfies §20's condition: row `{0}` is nonzero for every
  component, so `blk {0}` would have to be `0`, `1`, `2` and `3` simultaneously.
  **`no_support_of_shared_entry`** states the general criterion, so the example is structural: any
  two components that agree as internal matrices and have a nonzero entry rule out a per-component
  block function.

The consequence is that §25's support-free Schur test — with §27's operator-norm radii — is
**necessary** for data of this kind, not merely convenient.  Nothing here bounds the Schur sums of
`degHiggsData`; §28's general test is what applies, and the constant it gives there (`8`) is the
price of the mixing.

## 31. The reverse elliptic estimate: its exact residual (2026-11-10m)

Module: `BookProof/Sm/ChapterSmReverseEllipticResidual.lean`.  Registered in `BookProof.lean`.

§26 reduced `PotSelfBound` to §19's `hpoly` and said in prose that the gradient term is not
absorbable.  This section turns the reducee into an equation and says exactly what the sign route
reaches.

Writing `K = −Δ_S p`, `T = W p + p`:

* **`re_inner_kinPolyS_self`** — `ℜ⟪−Δ_S p, p⟫ = ∑_{j∈S} ‖∇_j p‖²`: §23's weighted identity at weight
  `1`, where the commutator term vanishes.  It was used implicitly in §26 and is recorded because the
  residual needs it.
* **`norm_shift_sq_decomp`** — `‖K + T‖² = ‖K‖² + 2 ℜ⟪K, T⟫ + ‖T‖²`, and **`inner_KT_eq`** —
  `ℜ⟪K, T⟫ = ℜ⟪W p, −Δ_S p⟫ + ∑_j ‖∇_j p‖²`, i.e. the cross term is §23's quantity plus the
  Dirichlet energy.
* **`potSelfBound_one_iff_remainder`** — `PotSelfBound P c₀ 1` **is** the non-negativity of
  `‖K‖² + 2 ℜ⟪K, T⟫`.  With `β = 1` there is no slack anywhere: the reverse estimate and the
  residual are the same statement.
* **`potSelfBound_one_of_grad_residual`** — substituting §26's interpolation gives the sufficient
  condition `∑_j ‖(∂_j W)p‖² ≤ ‖Δ_S p‖² + 3 ∑_j ‖∇_j p‖²`, which yields `PotSelfBound P c₀ 1`.

**Do not read the last item as progress towards the self-bound.**  The condition compares a
**degree-six** density with second-order norms, the constant `3` is exactly the `2ab ≤ a² + b²` slack
of `mul_le_half_add_sq`, and the condition is **not proved** here for the SM's quartic `W`.  What the
section establishes is negative and definite: every route through the sign identity and the
interpolation lands on that condition, so a proof of `PotSelfBound` cannot come from this calculus at
all.  It must compare **form domains** — the domain of the closed form of `−Δ_S + W` with the `H²`
domain — which is elliptic regularity, absent from this corpus.  `PotSelfBound` remains a hypothesis
downstream, and this section assumes nothing away.

## 32. The form-domain comparison, named (2026-11-10n)

Module: `BookProof/Sm/ChapterSmFormDomainComparison.lean`.  Registered in `BookProof.lean`.

§31 localised the reverse estimate as an exact residual and left the missing input in prose.  This
section gives it a name, because the missing input is a **domain** statement and the corpus should be
able to cite it:

```text
FormDomainComparison P c₀ c  :=  ∀ p, ‖−Δ_S p‖ ≤ c ‖(−Δ_S + W + 1) p‖,
```

i.e. the comparison's graph norm controls its partial kinetic term on the polynomial core.
**Domain correction (2026-11-11):** extension requires an operator-core/closure argument;
it concerns `D(−Δ_S + W + 1)`, not inclusion of its quadratic-form domain into `H²`.
Only derivatives in `S` occur. The source module's stronger domain prose is not a theorem
of its displayed definition; the missing uniform graph estimate remains open.

* **`FormDomainComparison`**, `formDomainComparison_iff` — the definition, in the domain reading.
* **`formDomainComparison_of_potSelfBound`** — `PotSelfBound` with constant `β` gives the comparison
  with `1 + β`, through §22's triangle inequality `‖Δ p‖ ≤ ‖N p‖ + ‖W p + p‖`.  The hypothesis
  `0 ≤ β` is *not* needed for this direction.
* **`potSelfBound_of_formDomainComparison`** — the converse, at `1 + c`: §26's
  `potSelfBound_of_kinetic_bound`, stated for the named object.
* **`exists_potSelfBound_iff_exists_formDomainComparison`** — therefore a non-negative self-bound
  exists iff the comparison does.  **The name is not a weaker hypothesis**, and that is proved rather
  than claimed: whoever discharges one discharges both.  Nothing here narrows the gap; it makes the
  gap quotable and pins what a proof must produce.
* **`form_coercive`** — the half the quadratic form does give: `‖p‖² ≤ ℜ⟪p, N p⟫`, from §31's
  `ℜ⟪−Δ_S p, p⟫ = ∑_j ‖∇_j p‖² ≥ 0` and the pointwise non-negativity of `W` (§23).
* **`norm_le_shiftNorm_of_coercive`** — hence `‖p‖ ≤ ‖N p‖`, by Cauchy–Schwarz.

The norm bound is available on the operator core. It does not imply that the form domain
lies in `D(N)`; for a positive self-adjoint realization the automatic inclusion runs
`D(N) ⊆ D(N^{1/2})`. `FormDomainComparison` is **not** proved for the SM's quartic `W`.

## 33. The quadratic weight: the case the corpus does prove (2026-11-10n)

Module: `BookProof/Sm/ChapterSmHarmonicReverseEstimate.lean`.  Registered in `BookProof.lean`.

The follow-up question was whether the corpus's harmonic-potential ellipticity already gives the
reverse estimate for a *quadratic* weight.  It does, and the answer is in
`ChapterGaussCoreQuadBounds`:

| ingredient | corpus lemma |
| :--- | :--- |
| graph norm of the comparison | `shiftNorm p = ‖pgLp (harmP p) + pgLp p‖` |
| potential by graph norm | `norm_harmPoly_mul_le_shiftNorm` (constant `2`) |
| identity by graph norm | `norm_pgLp_le_shiftNorm` (constant `1`) |
| **reverse (`H²`) estimate** | `norm_kinPoly_le_shiftNorm` (constant `3`) |
| coercivity | `dim_mul_norm_le_shiftNorm` (`D/2 + 1`) |

This section records them under the SM chapter's naming, so that the two cases can be compared
statement for statement:

* **`reverseEstimate_harm`** — the `FormDomainComparison` of §32 at the harmonic weight, `c = 3`;
* **`potentialBound_harm`**, **`identityBound_harm`** — the two addition terms;
* **`selfBound_harm`** — the `PotSelfBound` of §22 at the harmonic weight, `β = 3`.  For a quadratic
  weight the self-bound is a **theorem**, not an input;
* **`coercive_harm`** — the coercivity with its explicit constant.

**Why nothing transfers.**  The harmonic instance is a statement about `−Δ + harmPoly + 1`, not about
`−Δ_S + W + 1`; transferring it needs `‖N_harm p‖ ≤ κ ‖N_W p‖`, a comparison of two graph norms and
therefore the same kind of form-domain statement as §32.  The corpus proves the quadratic case
because `norm_sq_harmPoly_mul_le` — the uncertainty bound — controls a quadratic weight against the
oscillator's graph norm; that bound has **no quartic analogue**, and `W` is not pointwise dominated by
`harmPoly` (degree four against degree two).  So §33 is the shape of a complete argument in the only
case the corpus's uncertainty bound covers, and it is not a step towards `PotSelfBound`.

## 34. The degenerate doublet's Schur sums, evaluated (2026-11-10n)

Module: `BookProof/Sm/ChapterSmDegenerateDoubletConstant.lean`.  Registered in `BookProof.lean`.

§30 showed that `degHiggsData` admits no per-component block function, so §25's general Schur test is
the one that applies; §28's constant `8` was for a hand-written family, not for this dictionary.
This section evaluates the test for `degHiggsData` itself.

* **`degHiggsCanonical`** — the same dictionary at the canonical placement, so §25's general test
  needs no hypothesis on `pos`; `p1HiggsMat_degHiggsCanonical` records that the coefficient matrices
  are those of §30, and `p1HiggsMat_degHiggsCanonical_apply` their values.
* **`weightSum_degHiggs`** — the Schur weight is `4 * A.card` on the diagonal and `0` off it: the
  four components coincide with the number operator.
* **`rowSumGen_degHiggs`**, **`colSumGen_degHiggs`** — both equal `4 * card`; **`rowSumGen_degHiggs_le`**,
  **`colSumGen_degHiggs_le`** — both at most `4 * 96 = 384`.
* **`degHiggs_constant`** — `4 √(384 · 384) = 1536`, and **`degHiggs_commForm_le`** — §25's
  commutator bound for the degenerate doublet at that constant.

The number is the expected one (occupation number `≤` mode count, times the number of degenerate
components) and it is a *bound*, not the sharp Schur constant: `A.card ≤ 96` is used sector by
sector, while the number operator's rows are concentrated.  Sharpening it is a computation on the
sector sizes, not a theorem about the method.  What is now settled is that the support-free test is
not merely applicable to a dictionary §20 provably cannot accept, but **quantified** on it.

## 35. The quartic analogue of the uncertainty bound (2026-11-10o)

Module: `BookProof/Sm/ChapterSmQuarticUncertainty.lean`.  Registered in `BookProof.lean`.

§33 said the harmonic instance does not transfer because `norm_sq_harmPoly_mul_le` has no quartic
analogue.  This section states the analogue precisely and proves exactly one direction of it.

The harmonic bound is `‖harmPoly · p‖² ≤ ‖(−Δ + harmPoly) p‖² + (d/2)‖p‖²`: the potential is bounded by
the graph norm **plus a lower-order remainder**.  The quartic analogue, with the `L²` remainder
replaced by the only remainder available at degree four, is

```text
QuarticUncertainty P c₀ C :  ‖W · p‖² ≤ ‖(−Δ_S + W) p‖² + C ∑_j ‖∇_j p‖².
```

* **`QuarticUncertainty`** — the definition.
* **`quarticUncertainty_of_gradResidual`** — §31's gradient-residual condition implies it with
  `C = 2`: expand `‖(−Δ_S + W)p‖²`, and the cross term is bounded below by §26's interpolation.

The quartic analogue is therefore **weaker** than §31's condition — proving it is a strictly smaller
ask, not the same one.  The converse is **not available and not claimed**: `QuarticUncertainty`
supplies a *lower* bound on `2 ℜ⟪W p, −Δ_S p⟫`, while deriving §31's condition needs an *upper* bound
with the same constant, `2 ℜ⟪W p, −Δ_S p⟫ ≤ −∑_j ‖∇_j p‖² + ∑_j ‖(∂_j W)p‖²`, which the sign identity
does not give anywhere in the corpus.  That one-sidedness of §23 is the obstruction to closing
`PotSelfBound` by the sign route, and it is now on record as such rather than as a proverb.

**No transfer.**  Even with `QuarticUncertainty`, the remainder `2 ∑_j ‖∇_j p‖²` still has to be
absorbed by the graph norm of `−Δ_S + W + 1`, which is §32's `FormDomainComparison`.  The quartic
analogue of the *uncertainty bound* is weaker than §31's condition; the quartic analogue of the
*transfer* is `PotSelfBound` itself.  They are different targets and neither is proved.

## 36. The degenerate doublet's Schur radius is sharp (2026-11-10o)

Module: `BookProof/Sm/ChapterSmDegenerateDoubletSharp.lean`.  Registered in `BookProof.lean`.

§34 bounded the general Schur sums of the degenerate doublet by `384` and used that for the constant
`1536`.  That bound is not improvable, and the sector-size distribution shows why: the rows are
`4 · card`, so the radius is `4 · max_A |A|`, and the maximum is attained.

* **`rowSumGen_degHiggs_univ`**, **`colSumGen_degHiggs_univ`** — the full sector `univ` has both sums
  exactly `384`;
* **`degHiggs_rowRadius_sharp`**, **`degHiggs_colRadius_sharp`** — every uniform Schur radius
  satisfies `384 ≤ ρ`;
* **`degHiggs_rowRadius_eq_card_max`** — the row value is `4 · 96`, read off the distribution.

So `384` is the **exact** uniform Schur radius, and `1536` is what the Schur test gives at it.  A
smaller commutator constant for this family must come from cancellation, not from a sharper radius —
"sharpen the constant" and "sharpen the method" are different tasks, and only the second is available
here.  (For the physical, non-diagonal matrices §27's operator-norm radii are the sharper tool; this
section is about the dictionary §20 provably cannot handle.)

## 37. Which quadratic-weight lemmas survive domination by `harmPoly` (2026-11-10o)

Module: `BookProof/Sm/ChapterSmQuadraticWeightLemmas.lean`.  Registered in `BookProof.lean`.

The largest class in which the corpus's quadratic tool (`norm_potLp_le_of_le_harm`) applies is
`|W(x)| ≤ λ · harmW(x) + μ`.  This section maps which of §33's lemmas survive there.

| lemma | status |
| :--- | :--- |
| potential bound `‖W p‖ ≤ λ' shiftNorm p` | **holds** — `norm_potLp_le_of_le_harm` plus `potentialBound_harm` |
| identity bound `‖p‖ ≤ shiftNorm p` | **holds** unconditionally — `identityBound_harm` |
| self-bound `‖W p + p‖ ≤ β shiftNorm p` | **holds by composition** — new `selfBound_of_potBound` |
| coercivity `‖p‖ ≤ ‖N_W p‖` | **holds** for `W ≥ 0`, by §32's argument with `W` for `smPotPoly` |
| **reverse (`H²`) estimate** | **does not follow** |

* **`selfBound_of_potBound`** — the composition step, valid for *any* weight: a potential bound with
  constant `λ` plus §33's identity bound gives the self-bound with `λ + 1`.

Why the reverse estimate is absent: it is a statement about the graph norm of `−Δ + W + 1`, while the
domination is a bound on the *coefficient* `W`.  Passing from the harmonic instance to `N_W` needs
`‖N_harm p‖ ≤ κ ‖N_W p‖`, i.e. §32's named input again.  Every lower-order statement survives
domination; the comparison of the two forms does not.  And the SM's quartic `W` is not even in this
class, so the table's provable half does not apply to it either.

## 38. The cross term is a Hessian weight: the upper bound §35 asked for (2026-11-10p)

Module: `BookProof/Sm/ChapterSmCrossTermHessian.lean`.  Registered in `BookProof.lean`.

§35 recorded the obstruction precisely: §23's identity bounds the cross term of `‖(−Δ_S + W)p‖²`
*below* (the weighted Dirichlet energy is non-negative), whereas `PotSelfBound` needs the
commutator term `ℜ⟪p ∇W, ∇p⟫` to be *bounded above*, and the only route the corpus had — §26's
interpolation plus `2ab ≤ a² + b²` — landed on `GradResidual`, a comparison between a degree-six
density `∑_j ‖(∂_j W)p‖²` and a second-order norm.  This section proves the missing bound, and it
is sharper than an inequality: the commutator term is a **Hessian weight**.

**The identity.**  Two integration by parts, on the Gauss–polynomial core where everything is a
Gaussian integral:

```text
2 Re ⟪Q p, −Δ_S p⟫  =  2 ∑_{j ∈ S} ∫ Q |∇_j p|²  −  ∑_{j ∈ S} ∫ (∂_j² Q) |p|².
```

No derivative is left on `Q`.  The mechanism is the twisted Leibniz rule: `coreD j a * b + a *
coreD j b = ∂_j(ab) − x_j ab` (`coreD_mul_add`), so the two halves of
`⟪Qp, −Δ_S p⟫ = ∑_j (⟪(∂_jQ)p, ∇_j p⟫ + ⟪Q∇_j p, ∇_j p⟫)` combine into a single ordinary
derivative, which the antisymmetry of `coreD` (`gaussInt_coreD`) integrates by parts once more;
the twist `−x_j/2` cancels exactly between the two halves.

* **`coreD_mul_add`** — the twisted Leibniz rule in the shape the identity consumes.
* **`gaussInt_cpoly`**, **`two_re_gaussInt`** — conjugation commutes with the Gaussian integral
  (the weight is real), so `2 Re ∫ f = ∫ (f + conj f)`; these are bookkeeping, `cpoly` being the
  conjugate polynomial.
* **`commutator_cross_eq`** — the identity coordinate by coordinate.
* **`crossTerm_eq`** — the identity summed over `S`, in the two weights
  `weightedDirichlet S Q p = ∑_{j∈S} ∫ Q |∇_j p|²` and `hessForm S Q p = ∑_{j∈S} ∫ (∂_j²Q)|p|²`:
  `2 ℜ⟪Q p, −Δ_S p⟫ = 2 · weightedDirichlet − hessForm`.
* **`crossTerm_upper`** — the missing direction: when `hessForm ≥ 0` the cross term is dominated by
  the weighted Dirichlet energy.  **`hessForm_eq_trace`** / **`hessForm_nonneg`** reduce the sign to
  the pointwise non-negativity of the Hessian trace `∑_j ∂_j²Q`, and **`sm_crossTerm_upper`** is the
  statement at the SM's quartic weight under that one sign hypothesis.
* **`weightedDirichlet_add`**, **`weightedDirichlet_one`** — the weighted energy is additive in the
  weight and the weight `1` gives back §26's Dirichlet energy, so the residual can be written with
  the weight `W + 1` alone.

**What this does to `PotSelfBound`.**  Substituting the identity into §31's residual gives, with no
inequality anywhere,

```text
R = ‖Δ_S p‖² + 2 ∑_{j∈S} ∫ (W+1)|∇_j p|² − ∑_{j∈S} ∫ (∂_j²W)|p|²,
```

hence **`residual_eq_hessForm`** and the equivalence

```text
PotSelfBound P c₀ 1   ⟺   hessForm(W) ≤ ‖Δ_S p‖² + 2 · weightedDirichlet(W+1)   for all p
```

(**`potSelfBound_one_iff_hessForm`**).  This is the honest state of the target after the packet:

* the degree-six density is **gone**.  §31's `GradResidual` compared a cubic object with a
  second-order norm; the Hessian gap compares two **quadratic** forms — the Hessian-weighted `L²`
  mass of `p` against the graph form.  Nothing in the new condition is a statement about `∇W`;
* the gap is **exact**, not sufficient: §31's `potSelfBound_one_of_grad_residual` carried the
  `2ab ≤ a² + b²` slack, this does not;
* the gap is **still not proved**, and `PotSelfBound` therefore remains a hypothesis.  What is left
  is a numerical comparison of the SM's constants — the Hessian trace of the quartic potential
  against the kinetic term and the weighted Dirichlet energy — at the level of quadratic forms.
  For `p = 1` both sides are finite sums of Gaussian moments, so the gap is *checkable*; it is not
  *decided* here, and no claim is made that it holds.

The sign hypothesis of `sm_crossTerm_upper` deserves a note of its own, because it is the reason no
unconditional upper bound follows from the identity: `∑_j ∂_j²(φ_r²) = 2∑_j (∂_jφ_r)² + 2φ_r Δφ_r`
is a degree-two polynomial whose second term is indefinite.  For the SM's fields (quadratic
magnetic components, quadratic covariant derivatives) the sign is data-dependent, and the corpus
does not compute it.  Where the trace *is* non-negative, the cross term is dominated by the weighted
energy — that is §35's missing bound, now a theorem.

## 39. Can the `ExpBounded` machinery supply the form-domain inclusion? No. (2026-11-10p)

No module: this section records a **check** whose result is negative, so that the search is not
repeated.  The question was whether the corpus's exponential-growth class — the hypothesis under
which the graph norm of `−Δ_S + W` is even defined — can be pushed to §32's
`FormDomainComparison`, and hence to `PotSelfBound`.

**Where the class enters.**  `ExpBounded f` is `|f x| ≤ C e^{c‖x‖}`.  It is the hypothesis of
`potLp` (`BookProof/Qg/ChapterQgHermiteFriedrichs.lean`) and hence of `hamPolyS`, `hamCoreS`,
`hamCore`; its only job is to make `W · p · e^{−‖x‖²/4}` an `L²` function
(`memLp_mul_pgFun_of_expBounded`).  Every polynomial is in the class (`expBounded_polyW`,
`expBounded_poly`), so the SM weight qualifies.

**What the class proves.**  `ccHamS_esa` / `hamCoreS_esa`
(`BookProof/ChapterDegKatoEsa.lean`, `BookProof/Toolbox/ChapterHermiteGraphApprox.lean`) prove
essential self-adjointness of `−Δ_S + W` for every smooth `W ≥ 1`, by mollification and a cut-off
energy estimate: the deficiency vector `w` at a purely imaginary `z` satisfies
`∫_{‖x‖≤R} |w|² ≤ (2C²/R²)‖w‖²`, and `R → ∞` gives `w = 0`.  That is a **qualitative** theorem:
it says the deficiency indices vanish.  It contains no inequality between `‖W u‖` and `‖Au‖`, and
it uses no elliptic regularity.

**What the inclusion needs.**  §22's `PotSelfBound P c₀ β` is
`‖(W+1)p‖ ≤ β‖(−Δ_S + W + 1)p‖` — a *relative bound*, i.e. a quantitative norm inequality, and by
§38 it is equivalent to the Hessian gap.  Three reasons the class cannot produce it:

1. **Growth is not size.**  `ExpBounded` is closed under `const_mul` and under adding bounded
   functions, so it is *scale-blind*: `t·W` is in the class for every `t > 0`.  The Hessian gap is
   not scale-blind — its Hessian side is linear in `t`, its Dirichlet side is `t·weightedDirichlet(W)
   + weightedDirichlet(1)`, its kinetic side is independent of `t`.  A hypothesis that holds
   uniformly in `t` cannot decide an inequality whose two sides have different degrees in `t`.
2. **Deficiency is not domination.**  The energy estimate bounds a vector *in the kernel of
   `A* − z`*.  A relative bound needs a statement about every core vector, and the corpus's own
   quantitative theorems on the class — `norm_potLp_le_of_le_harm`
   (`|W| ≤ λ harmW + μ`), `norm_potLp_le_shift` — each carry exactly the extra domination the class
   lacks.  For a quartic `W` neither domination holds.
3. **The quadratic case proves the pattern.**  §33's reverse estimate for `harmPoly` *is* obtained
   from these tools — because a quadratic weight admits the domination `W ≤ λ harmPoly + μ` and the
   uncertainty bound `norm_sq_harmPoly_mul_le`.  Both are degree-two facts.  Nothing in the class
   substitutes for them at degree four.

**Verdict.**  The machinery supplies the *bookkeeping* (the graph norm exists) and the
*qualitative* half (the form is closed and the operator essentially self-adjoint); it does not
supply the inclusion.  §32's `FormDomainComparison` — the graph norm of `−Δ_S + W + 1` dominating the
`H²` (or, by §38, the Hessian-weighted `L²`) norm — remains the open input, and `PotSelfBound`
remains a hypothesis.  Note that the SM's *essential self-adjointness* is unaffected: `sm_h_esa` is
proved unconditionally (§13), and `PotSelfBound` is the hypothesis of the P1/P2 **relative-bound**
transfer (`smNormalForm_norm_le_of_pot_self_bound`), a different estimate from ESA.

---

## §40. The Hessian gap at `p = 1`: a Gaussian-moment test

### 40.1. What `p = 1` reduces to — and a correction to the first reading of it

By §38, `PotSelfBound P c₀ 1` is equivalent to

```
hessForm(W)  ≤  ‖Δ_S p‖²  +  2 · weightedDirichlet(W + 1)        (all p)
```

with `W = smPotPoly P c₀` and `S = smS`.

> **Correction (2026-11-11).**  The first version of this section claimed that at `p = 1`
> both right-hand terms vanish — `‖Δ_S 1‖² = 0` and `∑_{j∈S} ∫ (W+1)|∇_j 1|² = 0` — so
> that the criterion would collapse to `∫ Δ_S W · e^{-‖x‖²/2} ≤ 0`.  **That is wrong.**  The
> sentence uses the *untwisted* gradient, but the module's derivative is the twisted one
> `coreD_j p = ∂_j p − x_j p / 2`, and on the twisted core the polynomial `1` is the Gaussian
> `e^{-‖x‖²/4}`, not the constant function.  The corresponding untwisted constant test is
> vacuous anyway — at a constant `p` the residual inequality reads `‖(W+1)p‖ ≤ ‖(W+1)p‖` — so
> the only nontrivial `p = 1` test the module has is the Gaussian test, and it keeps the
> weighted Dirichlet term.

The module's `p = 1` values are exact (`ChapterSmCrossTermHessian` §9):

```
coreD_j 1                    =  −x_j / 2
kinPolyS smS 1               =  20 − ¼ ‖x_S‖²
hessForm smS W 1             =  ∫ Δ_S W · e^{-‖x‖²/2}
weightedDirichlet smS W 1    =  ¼ ∫ W · ‖x_S‖² · e^{-‖x‖²/2}
```

(`coreD_one`, `kinPolyS_one`, `hessForm_one`, `weightedDirichlet_one_one`,
`hessForm_smPotPoly_one`, `weightedDirichlet_smPotPoly_one`).  Hence the `p = 1` instance of
the criterion is

```
E[Δ_S W]  ≤  (n² + 2n)/16  +  ½ E[(W + 1) ‖x_S‖²] ,        n = |S| = 40 ,
```

with `(n² + 2n)/16 = 1680/16 = 105`.  The second term is the large one: for the quadratic part
`‖x_S‖²` of `W` alone it is `½ E[‖x_S‖⁴] = ½ (n² + 2n) = 840`.  So the `p = 1` test is **not**
the sign test `E[Δ_S W] ≤ 0`; it is the inequality above, and §42 evaluates it.

### 40.2. Decomposition of `Δ_S W`

`W = ∑_{r=0}^{48} Φ_r² + ∑_{m=0}^{39} q_m² + c₀`, with `Φ_r = smFormPoly P id r`.  Therefore

```
Δ_S W  =  Δ_S(∑ q_m²)  +  ∑_r Δ_S(Φ_r²)
        =  80  +  ∑_r [ 2 |∇_S Φ_r|² + 2 Φ_r Δ_S Φ_r ] .
```

The family-by-family sign:

* **`smQPoly` part (`∑ q_m²`).**  Contributes the constant `80` (each of the 40
  momentum coordinates contributes `2`).

* **`smMagB` (3 forms, hypercharge).**  Each `Φ` is linear in the *derivative*
  coordinates `smDB` (the field strengths `B_{k,j}`), not in the momentum
  coordinates.  Hence `∇_S Φ = 0` and `Δ_S(Φ²) = 0`: the contribution is **zero**
  (`smMagB` never sees the fields `B_i` themselves, only their derivatives).

* **`smMagG` (24 forms) and `smMagW` (9 forms).**  Each `Φ = L (derivative) + Q`
  where `Q` is quadratic in the gauge momentum coordinates with a harmonic
  (zero-Laplacian) quadratic part; the structure constants sit in `Q` but
  `levi(i,j,k)` forces `j ≠ k`, so no momentum coordinate is squared and
  `Δ_S Q = 0`.  Contribution `2 |∇_S Q|²`, a **non-negative** polynomial (zero at
  the origin).  (`smMagB` is the exception: its `Φ` is linear in `smDB` alone,
  so its `∇_S Φ` vanishes identically.)

* **`smCovD` (12 forms).**  `Φ = (derivative linear) + (bilinear in two distinct
  momentum coordinates)`, so again `Δ_S Φ = 0`; contribution `2 |∇_S Φ|²`,
  **non-negative** (zero at the origin).

* **`smWall` (1 form).**  `Φ = c (S − v₀²)` with `c = √(λ/2)` and
  `S = ∑_{a=0}^{3} φ_a²` (the four Higgs components are momentum coordinates).
  Here the Laplacian is non-zero and the contribution is

```
  Δ_S(Φ²)  =  24 c² S  −  16 c² v₀² .
```

  (Verified by direct differentiation: `∂²/∂φ_a²` of `c²(S−v₀²)²` sums to
  `4 c² (S − v₀² + 2 φ_a²)` over `a`, i.e. `24 c² S − 16 c² v₀²`.)

### 40.3. The Gaussian moment of `Δ_S W`

Under the (unnormalised) Gaussian `e^{-‖x‖²/2}`, the momentum coordinates are
independent standard normals, so `E[X²] = 1` and `E[S] = 4`.  Only the wall has a non-zero
twisted Laplacian, so the expectation is an **identity**, not an inequality:

```
E[Δ_S W]  =  80  +  E[G]  +  48 λ − 8 λ v₀² ,
```

with `G = 2 ∑_{r ∈ {magG, magW, covD}} |∇_S Φ_r|² ≥ 0` (the `smMagB` contribution is exactly
zero) and `E[wall] = 24 c²·E[S] − 16 c² v₀² = 96 c² − 16 c² v₀² = 48 λ − 8 λ v₀²`.  The
gradient tail `E[G]` is computed in §42.

### 40.4. Verdict of the test — corrected

> **Retraction (2026-11-11).**  The first version of this section dropped the weighted
> Dirichlet term at `p = 1` and concluded `E[Δ_S W] ≤ 0`, hence the threshold
> `λ v₀² ≥ 10 + 6 λ + E[G]/(8 λ)`.  That threshold is **withdrawn**: it is not a necessary
> condition for `PotSelfBound`, because at `p = 1` the weighted Dirichlet energy is
> `½ E[(W+1)‖x_S‖²]`, which is large and positive, not zero.

The `p = 1` test is the inequality of §40.1.  Writing `Φ = ∑_r Φ_r² ≥ 0` for the sum of the
squared forms, `W = ‖x_S‖² + Φ + c₀`, and using `E[‖x_S‖²] = n`, `E[‖x_S‖⁴] = n² + 2n` with
`n = 40`:

```
½ E[(W+1)‖x_S‖²]  =  840 + 20 (c₀ + 1) + ½ E[Φ ‖x_S‖²] ,
(n² + 2n)/16      =  105 ,
```

so the test reads

```
80 + E[G] + 48 λ − 8 λ v₀²   ≤   965 + 20 c₀ + ½ E[Φ ‖x_S‖²] .                     (∗)
```

Three consequences, in decreasing order of how much they settle:

* **(∗) is not a lower bound on `λ v₀²`.**  It fails only when

```
  λ v₀²  <  (80 + 48 λ + E[G] − 965 − 20 c₀ − ½ E[Φ ‖x_S‖²]) / 8 ,
```

  and both `E[G] ≥ 0` and `½ E[Φ ‖x_S‖²] ≥ 0`, while `E[Φ ‖x_S‖²]` carries the quartic and
  sextic field powers (`Φ_wall` alone contributes `c² E[(S − v₀²)² ‖x_S‖²]`, which is
  `c² v₀⁴ · 40 + O(c² v₀²)`).  For any positive `λ v₀²` in the range where
  `½ E[Φ ‖x_S‖²]` is of the size of `8 λ v₀²`, the test is passed — including the physical
  regime.  Nothing like a threshold at `10 + 6 λ` is implied.

* **(∗) is not scale-covariant.**  The Gaussian has unit variance, while the fields carry
  whatever normalization the coordinates are written in; the terms of (∗) have different
  homogeneity (`E[G]` is quartic, `E[Φ‖x_S‖²]` is sextic, `8 λ v₀²` is quartic with the
  couplings explicit).  Rescaling the fields changes the inequality.  The corpus fixes no
  field normalization, so (∗) has no numerical verdict until one is fixed — the same
  scale-blindness that closed the `ExpBounded` route in §39.

* **What survives.**  The pointwise sign analysis of §41 is unaffected (it is a statement
  about the polynomial `Δ_S W`, not about the Gaussian weight), and the `p = 1` test is now
  an exact, machine-checked inequality rather than a sign condition.  The honest reading of
  the test is therefore: *at `p = 1` the Hessian gap is governed by the competition between
  the negative wall lobe of `Δ_S W` and the positive moment `½ E[(W+1)‖x_S‖²]`.*  That
  competition is decided at `p = 1`, and it is not the same question as
  `E[Δ_S W] ≤ 0`.

`PotSelfBound` remains a hypothesis.  The `p = 1` case does not discharge it, and — after the
correction — the `p = 1` case does not exclude any physically sensible data either.

### 40.5. What this does not settle

The test only rules out regimes; it does not prove `PotSelfBound` in any regime,
because `PotSelfBound` must hold for *all* `p`, not just `p = 1`, and the
`H²`/form-domain comparison (§32) is untouched.  It does, however, convert the
abstract gap into an explicit data inequality, which is the honest content of
the hypothesis.

---

## §41. Sign of the Hessian trace (momentum Laplacian) of `smPotPoly`

### 41.1. The Laplacian polynomial

From §40.2,

```
Δ_S W(x)  =  80
            + 2 ∑_{magG,magW,covD} |∇_S Φ_r|²   (non-negative polynomials, zero at 0)
            + 24 c² S  −  16 c² v₀² .
```

(`smMagB` contributes nothing: its field strength is built from the derivative
coordinates `smDB`, not from the momentum coordinates `B_i`.)

The only term that can be negative is the wall piece, and only where the Higgs
field is small: `24 c² S − 16 c² v₀² < 0  ⟺  S < (2/3) v₀²`.

### 41.2. Where it changes sign

* **At the origin** (`x = 0`, all fields zero): `S = 0` and the non-negative
  `|∇|²` terms vanish for `magG`/`magW`/`covD` (their gradients are linear in
  the fields), leaving

``  `Δ_S W|₀  =  80 − 8 λ v₀² .
```

  This is negative iff `λ v₀² > 10`.  So for strong coupling/large vev the
  Laplacian is negative at the origin; for weak data it is positive everywhere
  near the origin.

* **For large fields**: the `24 c² S` term and the `|∇|²` quadratics grow, so
  `Δ_S W → +∞` along any ray.  Hence the negative region (if any) is a bounded
  neighbourhood of the origin in field space.

* **The `q²` sum is the only constant contributor**: its `80` is independent of
  the fields and survives at the origin.  The `smMagB` sector contributes `0`.

### 41.3. Consequences

1. **`hessForm` is not sign-definite.**  `hessForm(W)` integrates
   `Δ_S W · |p|²` against the Gaussian; for `p` supported in the negative
   region the integral can be negative.  Thus `crossTerm_upper` (§38) is not
   automatic: its hypothesis `hessForm ≥ 0` is a condition on `p` and the data,
   not a consequence of `W ≥ 0`.

2. **The `p = 1` test (§40) is the integrated version of this pointwise fact, with the
   corrected right-hand side.**  The Gaussian expectation `E[Δ_S W] = 80 + E[G] + 48 λ − 8 λ v₀²`
   is compared not with `0` but with `105 + ½ E[(W+1)‖x_S‖²]` (§40.1); the negative lobe near
   the origin must outweigh that positive moment.  The earlier threshold
   `λ v₀² ≥ 10 + 6 λ` came from comparing with `0` and is withdrawn in §40.4.

3. **No proof of `PotSelfBound` is available from this calculus.**  The gap
   requires either (a) a regime restriction on `(λ, v₀)` plus a proof that the
   integral stays non-positive for all `p`, or (b) elliptic regularity supplying
   the form-domain comparison of §32 directly.  Neither is in this corpus.

### 41.4. Recorded status

* `hessForm_eq_trace` / `hessForm_nonneg` (§38) reduce the question to the sign
  of `∫ Δ_S W |p|²`; this section records that the sign is **data- and
  point-dependent**, and gives the explicit origin value `80 − 8 λ v₀²`.
* `PotSelfBound` and `FormDomainComparison` remain hypotheses.  `sm_h_esa` (ESA)
  is unaffected.

---

## §42. The gradient tail `E[G]`, explicitly

### 42.1. The rule for a bilinear form

Every field strength and covariant derivative in `smFormPoly` is, in the momentum coordinates,
either zero, linear in coordinates outside `S` (the derivative coordinates `smDG`, `smDW`,
`smDB`, `smDPhi`), or **bilinear in two distinct momentum coordinates**.  The `smMagB` family
is the first case (its `Φ` is linear in `smDB`, so `∇_S Φ = 0`), and the wall is the only
family whose twisted Laplacian does not vanish; §40.2 proved that.

For a bilinear form `Φ = ∑_{u,v} M_{uv} x_u x_v`,

```
∂Φ/∂x_u  =  ∑_v (M_{uv} + M_{vu}) x_v ,
E[|∇Φ|²] =  ∑_{u,v} (M_{uv} + M_{vu})² ,
```

because the momentum coordinates are independent standard normals (`E[x_u x_v] = δ_{uv}`).
This is the general quadratic-form formula §40.4 quoted; the point of this section is to
evaluate it.

### 42.2. The gluon and weak families

For `smMagG` the coefficient of `G^b_j G^d_k` in `Φ_{a,i}` is
`½ gs · ε_{ijk} · f^{abd}`, so

```
(M + Mᵀ)_{(b,j),(d,k)}  =  ½ gs · ε_{ijk} · (f^{abd} − f^{adb}) ,
E[|∇_S Φ_{a,i}|²]       =  (gs²/4) (∑_{j,k} ε_{ijk}²) · D_f(a)
                        =  (gs²/2) · D_f(a) ,        D_f(a) = ∑_{b,d} (f^{abd} − f^{adb})² ,
```

using `∑_{j,k} ε_{ijk}² = 2` for each `i`.  Summing over the `8` colours and `3` directions:

```
E[∑_{magG} |∇_S Φ_r|²]  =  (3 gs² / 2) · D_f ,      D_f = ∑_{a,b,d} (f^{abd} − f^{adb})² .
```

The weak family is identical with `gw`, `e^{mbd}` and `Fin 3` colour indices:
`(3 gw² / 2) · D_e`, `D_e = ∑_{m,b,d} (e^{mbd} − e^{mdb})²`.

Both formulas are stated for a **general** `fabc`/`eabc`: the antisymmetrisation is what the
levi-Civita contraction produces, so a non-antisymmetric structure-constant table is handled
without extra hypotheses.  For totally antisymmetric constants `D_f = 4 ∑ f²`, `D_e = 4 ∑ e²`.

### 42.3. The covariant Higgs derivative

`Φ_{a,i} = (D_i φ)_a` is linear in `W^j_i`, `B_i` and `φ_b` through the two bilinears
`gw · tgen(j,a,b) W^j_i φ_b` and `gy · ygen(a,b) B_i φ_b`.  Differentiating in the momentum
coordinates:

```
∂/∂W^j_i  :  coefficient gw · tgen(j,a,b) in φ_b                 (sum over b)
∂/∂φ_b    :  gw · tgen(j,a,b) in W^j_i   and   gy · ygen(a,b) in B_i
∂/∂B_i    :  coefficient gy · ygen(a,b) in φ_b
```

so

```
E[|∇_S Φ_{a,i}|²]  =  2 gw² ∑_{j,b} tgen(j,a,b)²  +  2 gy² ∑_b ygen(a,b)² ,
```

and summing over the `4` doublet components and `3` spatial directions:

```
E[∑_{covD} |∇_S Φ_r|²]  =  6 gw² · T  +  6 gy² · Y ,
T = ∑_{a,j,b} tgen(j,a,b)² ,       Y = ∑_{a,b} ygen(a,b)² .
```

### 42.4. The tail

With `G = 2 ∑_{magG, magW, covD} |∇_S Φ_r|²`:

```
E[G]  =  3 gs² D_f  +  3 gw² D_e  +  12 gw² T  +  12 gy² Y  ≥  0 .
```

For the standard normalizations (`∑_{abd} f^{abd}² = 24` for `SU(3)`, `e^{mbd} = ε^{mbd}`,
`tgen = τ_j/2`, `ygen = σ₃/2`, so `D_f = 96`, `D_e = 24`, `T = 3/2`, `Y = 1/2`):

```
E[G]  =  288 gs²  +  90 gw²  +  6 gy² .
```

At the physical couplings (`gs² ≈ 1.48`, `gw² ≈ 0.43`, `gy² ≈ 0.13`) this is `≈ 466` — an
illustration only, because it is evaluated at the unit field normalization that the Gaussian
weight fixes, and the corpus fixes none (§40.4).

### 42.5. Where it enters — on the left, not the right

`E[Δ_S W] = 80 + E[G] + 48 λ − 8 λ v₀²` (§40.3).  So `E[G]` is a **positive** contribution to
the Hessian trace's expectation: the non-abelian and covariant-derivative gradients make
`E[Δ_S W]` larger and the corrected `p = 1` inequality (∗) *easier* to satisfy.  The retracted
§40.4 put it on the right-hand side as an addition to the required `λ v₀²`; that was a
consequence of the same dropped term, and it is withdrawn with it.

### 42.6. What is proved and what is not

* `coreD_one`, `kinPolyS_one`, `hessForm_one`, `weightedDirichlet_one_one` and the two SM
  instances `hessForm_smPotPoly_one`, `weightedDirichlet_smPotPoly_one` are proved, `sorry`-
  and `axiom`-free, in `BookProof/Sm/ChapterSmCrossTermHessian.lean` §9.  They fix the shape
  of the `p = 1` test exactly.
* The two facts the arithmetic rests on **are** proved, in the same module §10:
  `gaussMoment_one` (`∫ t e^{-t²/2} = 0`), `gaussInt_X_mul_X_of_ne` (distinct momentum
  coordinates do not correlate, `∫ xⱼxₖ e^{-‖x‖²/2} = 0` for `j ≠ k` — the reason `E[|∇Φ|²]`
  has no cross terms) and `hessForm_eq_zero_of_trace_zero` (a form with vanishing twisted
  Laplacian carries no Hessian weight, for every test polynomial — the abstract form of §40.2's
  `Δ_S Φ_r = 0` for `smMagG`/`smMagW`/`smCovD`).
* The evaluations of §42.2–§42.4 are arithmetic on the coefficient data, checked symbolically
  (including a non-antisymmetric `fabc`); the coefficient sums `∑_{u,v}(M_{uv}+M_{vu})²` are not
  formalized.  The SM instantiation would still need `smMagG`, `smMagW`, `smCovD` expanded into
  monomials — the coefficient bookkeeping, not the Gaussian analysis.
* `PotSelfBound` and `FormDomainComparison` remain hypotheses.  Nothing in §40–§42 proves
  either, and the `p = 1` test excludes no physically sensible data.

---

## §43. Are there test functions sharper than the Gaussian in the polynomial core?

### 43.1. The question, made quantitative

By §38, `PotSelfBound P c₀ 1` is equivalent to `R(p) ≥ 0` for every polynomial `p`, where

```
R(p)  =  ‖A p‖²  +  2 Re ⟨A p, (W + 1) p⟩ ,        A = kinPolyS smS ,  W = smPotPoly P c₀ ,
```

and `R(p) ≥ 0` is the same statement as

```
ρ(p)  :=  ‖(W + 1) p‖ / ‖(A + W + 1) p‖  ≤  1 .
```

So "sharper test function" has an exact meaning: larger `ρ`.  `ρ` is homogeneous of degree `0`,
and `PotSelfBound` says that its supremum over the core is `≤ 1`.  The question of this section
is whether the supremum over the core is attained, and whether polynomials with larger `ρ` than
the Gaussian `p = 1` are available in closed form.

### 43.2. The core loses nothing, but it also attains nothing

Two facts pull in opposite directions.

* **Density.**  The polynomial core is dense in the graph-norm domain of `A + W + 1`, so the
  supremum of `ρ` over the core equals the supremum over the closure.  Hence if any vector of
  the domain has `ρ > 1`, then so do polynomials: sharper tests, when they exist, are always
  available *somewhere* in the core.
* **No source of an extremal polynomial.**  The extremal vectors of `ρ` satisfy a fourth-order
  Euler–Lagrange equation, `(W+1)² p = λ (A + W + 1)² p`; for the quartic `W` of the SM nothing
  in the corpus identifies a polynomial solution, and the computed family below shows the sharp
  direction is a *rescaling* of the test function rather than an increase of its degree.

### 43.3. A computed proxy

The radial proxy is `W(s) = s + κ (s − v₀²)²` with `s = ‖x_S‖²`, `n = |S| = 40`, `κ = λ/2`.
Every expectation below is exact (Gaussian moments).  Three families of test functions:

* `p = 1` (the Gaussian `e^{-‖x‖²/4}`) — the §40 test;
* `p = x₀` — the first member of the degree ladder, `A p = x₀ ((n+1)/2 − s/4)`;
* the scaled Gaussians `ψ_a = e^{-a s/2}`, i.e. `p = e^{(1/2-a)s/2}`, which are polynomials only
  at `a = 1/2`.

```
κ = 0        (mass term only):     ρ(p=1) = 0.815802    ρ(p=x₀) = 0.822655
κ = λ/2, v₀² = 6:                  ρ(p=1) = 0.939581    ρ(p=x₀) = 0.944227

scaled Gaussians, κ = λ/2, v₀² = 6:
  a = 0.5    ρ = 0.93958        a = 0.2    ρ = 0.99575        a = 0.1    ρ = 0.999460
  a = 0.05   ρ = 0.999932       a = 0.02   ρ = 0.999996       a → 0      ρ → 1
```

For the mass-only proxy the ratio is explicit:

```
ρ²(a)  =  (420 a⁻² + 40 a⁻¹ + 1) / (420 a⁻² + 40 a⁻¹ + 1 + 420 a² + 40 a + 760) ,
```

so `1 − ρ²(a) ~ (760/420) a²` as `a → 0`: the sharpness approaches `1` quadratically as the test
function spreads out, and it never crosses `1`.  The same mechanism holds for the SM weight,
because `W` grows like a fourth power in the coordinates of `S` while the kinetic term of a
spread test vector is only of order `a`, so the potential dominates both norms in the limit.

### 43.4. Answer

* **Yes, sharper tests than `p = 1` are available in the core, in closed form.**  The degree-one
  test `p = x₀` already has larger `ρ` than the Gaussian, in both proxy regimes
  (`0.8227 > 0.8158` and `0.9442 > 0.9396`).  So `p = 1` is **not** the extremal available test,
  and the §40 test is strictly weaker than the first rung of the degree ladder.
* **No polynomial test is the sharpest.**  The supremum of `ρ` is `1`, approached by spread-out
  test functions; the corresponding vectors are `p = e^{(1/2-a)s/2}` with `a ≠ 1/2`, which are
  not polynomials.  The core supplies them only as limits, so no closed-form polynomial attains
  the boundary.
* **No test in the proxy crosses `1`.**  The proxy satisfies `ρ < 1` everywhere computed, with
  the margin `1 − ρ²` shrinking like `a²` in the spread direction.  The `p = 1` margin is not
  small — `1 − ρ² ≈ 0.12` at `v₀² = 6` — which is exactly why the §40 test passed comfortably
  and could not have excluded any regime.

### 43.5. Consequence for the route

**Scope correction (2026-11-11):** these proxy tests concern the sharp choice `β = 1`.
P4 only needs some finite constant, and the full 49-form potential has additional
channels and parameter dependence. The conclusions below do not rule out a graph-bound
proof with slack; use the resumption packet in this file's external-source audit.

The "test the Hessian gap at a sequence of polynomials" route is therefore **exhausted as a
decision procedure**: the ladder is monotone but its increments are small near the Gaussian, and
the sharp direction leaves the core.  A proof of `PotSelfBound` cannot be replaced by choosing a
better polynomial; it still needs the form-domain/elliptic-regularity input of §32.  What the
ladder does supply is a cheap family of necessary conditions — the degree-one rung
`ρ(x₀) ≤ 1` is now the sharpest *closed-form* check available, and it should replace `p = 1` as
the first test in any future attempt.

### 43.6. Status of the numbers

All values in §43.3–§43.4 are exact Gaussian moments for the radial proxy `W = s + κ(s−v₀²)²`,
computed with exact rational arithmetic / high-precision `Γ`-moments; they are not Lean theorems
and not statements about the full `smPotPoly` (which has 49 forms rather than one radial
polynomial).  The density argument of §43.2 is a general fact about the core.  `PotSelfBound`
and `FormDomainComparison` remain hypotheses.

## §44. P5's parity reduction of the closure — landed 2026-11-12

### 44.1. What was missing, in the plan's own words

P5 records the gap exactly: "`smNormalForm_parity` is a **core-level** identity, and the closure's
graph has no commutation statement, so the strong reduction is not obtained".  Parity was known to be
a norm-preserving involution of the coupled space, to preserve the common core, and to commute with
the normal form on that core.  None of that restricts the *closure*: the deficiency criterion is a
statement about the adjoint's deficiency space, and a core identity does not by itself see it.

### 44.2. The generic statement, and why it is about the closure

`BookProof/Sm/ChapterSmPhysicalReductionEsa.lean` (namespace
`BookProof.SmPhysicalReduction`) first builds the two sectors of an involution `U` on a complex
inner-product space together with the algebra that the SM instance needs:

| lemma | content |
| :-- | :-- |
| `evenSpace`, `oddSpace` | `ker (U − 1)` and `ker (U + 1)` |
| `evenPart`, `oddPart`, `evenPart_add_oddPart` | `x = ½(x + Ux) + ½(x − Ux)` |
| `evenPart_mem`, `oddPart_mem` | the two parts lie in their sectors |
| `inner_map_map_of_norm_map` | norm preservation ⇒ `⟪Ux, Uy⟫ = ⟪x, y⟫` |
| `inner_map_left_eq` | a unitary involution is self-adjoint |
| `inner_eq_zero_of_mem_even_of_mem_odd` (+ odd-first form) | **the sectors are orthogonal** |
| `evenPart_mem_of_mem`, `oddPart_mem_of_mem`, `evenPart_mem_core`, `oddPart_mem_core` | an invariant core splits |
| `evenOp`, `oddOp`, `evenOp_mem`, `oddOp_mem` | the two restrictions, and that `T` graded by parity stays graded |

The reduction itself needs only one analytic-shaped lemma, which is pure algebra:

* `deficiency_at_of_even_deficiency` — a vector `w` *of the even sector* satisfying the deficiency
  equation `⟪T v, w⟫ = z⟪v, w⟫` against the even core satisfies it against the **whole** core.

Proof: write `v = e + o` with `e, o` the two sector parts of `v`.  Both lie in `D` (`D` is
`U`-invariant) and in their sectors.  `T o` is odd because `U(T o) = T(U o) = T(−o) = −T o` uses
the core commutation, so `⟪T o, w⟫ = 0` by orthogonality; likewise `e ⊥ w` in the scalar product
against `v`.  Hence the core equation for `v` follows from the sector equation for `e`.

Consequently

```
deficiencyTrivialAt_iff_sectors :
  DeficiencyTrivialAt D T z  ↔
    SectorDeficiencyTrivial (D ⊓ evenSpace U) (evenOp) (evenSpace U) z  ∧
    SectorDeficiencyTrivial (D ⊓ oddSpace U) (oddOp) (oddSpace U) z .
```

This is a statement about the closure because `DeficiencyTrivialAt` is exactly "the deficiency space
of the adjoint at `z` is trivial", i.e. the range of `T − z̄` is dense; triviality at both `±i` is
`EssentiallySelfAdjointOn`.  The proof never uses density of `D` and never quantifies over the
closure explicitly — it shows that the *deficiency* test vectors cannot distinguish the core from
its closure.  That is the strong commutation the plan asks for, expressed in the corpus's own idiom.

### 44.3. The SM instance

* `coupledParity_inner` — parity preserves the inner product of `PiLp 2 (fun _ => L2d 163)`
  (from `coupledParity_norm` through `LinearIsometry.inner_map_map`), which is the "bounded
  unitary" half of P5's sentence.
* `smNormalForm_parity_core` — `smNormalForm_parity` in the orientation the reduction consumes,
  with the subtype proof handled through `coe_coupledParityCore`.
* **`smNormalForm_esd_iff_parity_sectors`** — for every `SmNormalFormData D` and every
  `ParityGradedCoeffs D`,

```
EssentiallySelfAdjointOn SmCoupledCore (smNormalForm D)
  ↔  (sector-deficient on the even core at I) ∧ (on the odd core at I)
   ∧ (on the even core at −I) ∧ (on the odd core at −I).
```

  No hypothesis beyond the parity grading is used, and none is added: the equivalence is not a
  weakening of the demand, it is an equality of the two conditions.
* `topologicalClosure_evenCore`, `topologicalClosure_oddCore` — the closure of the even (odd) part of
  a dense invariant core **is** the even (odd) sector, which is P5's "supply a dense graph core for
  the restriction".  The odd case is the even case at `−U` (`evenSpace_neg`, `evenCore_neg`).

### 44.4. What this does not prove

* **Not** essential self-adjointness of either sector operator.  The reduction *localises* the
  obstruction: two decoupled sector problems replace one coupled one, and each sector still needs
  the elliptic/`PotSelfBound`/`FormDomainComparison` input of P4.  That input is unchanged, still a
  hypothesis, and was not attempted here.  §43's conclusion — that no polynomial test function
  supplies it — still stands.
* **Not** the physical (gauge) sector: no BRST quotient, no positive inner product on it, no
  reducing projection from a gauge-group unitary action.  The parity split is a *kinematic*
  decomposition of the unreduced Hilbert space, and the plan's "identify the unreduced closure /
  construct the actual physical Hilbert subspace" is not done.
* **Not** the outer lift.  `EsaOneParticle.dGamma_essentiallySelfAdjointOn_of_esa` needs ESA of the
  one-particle operator, so `Γ_s(K_even) ⊗ Γ_a(K_odd)` and `smComplete_dGamma_esa` remain
  conditional on §44.4's first bullet.  The graded permutation action's compatibility with the even
  inner Hamiltonian is likewise untouched.
* `SectorDeficiencyTrivial` is a *definition introduced here*; it is stated in the same shape as
  `DeficiencyTrivialAt` with the test vector confined to a sector, and §44.2 is the proof that this
  is the correct restriction.  It is not a re-labelling of the open problem: the equivalence is
  proved, and the two sides are then both open or both closed.

### 44.5. Verification performed (2026-11-12)

* `lake build BookProof.Sm.ChapterSmPhysicalReductionEsa` — clean, no `sorry`, no new axioms.
* `lake build Work.SmPhysicalReductionEsaAudit` — each of the 17 named declarations reports exactly
  `propext, Classical.choice, Quot.sound`; `sorryAx` does not appear.
* `import BookProof.Sm.ChapterSmPhysicalReductionEsa` registered in `BookProof.lean` with its
  scope comment (line 4101); the aggregate file re-elaborates against the built oleans
  (`lake env lean BookProof.lean`, exit 0, 4.6 s), and the full **`lake build BookProof` completed
  successfully (8969 jobs, 0 errors)** after the registration, so no downstream module, roadmap
  audit or aggregate target is disturbed by the new module.
* No numerical claim is made in this section.  The §40–§43 numbers are unaffected and were not
  recomputed.

## §45. P4 in one parity sector: the sector does not exist as a weakening (2026-11-12)

### 45.1. The question

§44 reduced the matter closure to its two parity sectors, under `ParityGradedCoeffs` alone.  The
obvious next hope is that the same split helps P4: that the analytic input
(`PotSelfBound` / `FormDomainComparison`) restricted to **one** parity sector is weaker than the
input on the whole coupled space, so that one sector could be closed first and only the other left
open.

### 45.2. The answer, and why it is structural

It is not weaker, and the reason is a feature of the model's parity that is visible in its
definition.  `coupledParity` is diagonal on the **outer** occupation index,

    (coupledParity f).ofLp A = fockSign A • f.ofLp A,      fockSign A = (-1)^{|A|},

and it does not touch the inner 163-coordinate factor.  Consequently:

* **every elementary tensor is a parity eigenvector** (`coupledParity_deltaFun`): for a single outer
  occupation `A` and any inner vector `v`, `coupledParity (deltaFun A v) = fockSign A • deltaFun A v`,
  so `deltaFun A v` is in the even sector iff `|A|` is even (`deltaFun_mem_evenSpace_iff`);
* the **entire inner test class** — every Gauss-polynomial in 163 variables — sits inside each
  sector whole, with its norm unchanged (`deltaFun_norm` is an isometry);
* the coupled tensor acts **componentwise** on it (`coupledOp_one_deltaFun`,
  `coupledOp_one_add_deltaFun`), so the sector inequality at `deltaFun A v` *is* the scalar
  inequality at `v`.

### 45.3. The two theorems that settle it

* `scalarBound_of_evenSectorBound` — a relative bound `‖T ⊗ I f‖ ≤ c ‖(N ⊗ I + 1) f‖` valid only on
  the **even** sector already yields the scalar bound `‖T x‖ ≤ c ‖N x + x‖` for every inner core
  vector, by evaluating at the empty outer occupation (which is even, `fockSign ∅ = 1`).
* `scalarBound_of_oddSectorBound` — the same from the odd sector, at the single occupation `{0}`
  (`fockSign {0} = -1`).
* `sectorComparison_iff_formDomainComparison` — §32's `FormDomainComparison` read on the elementary
  tensors of *any* sector is literally the whole scalar statement,
  and `sectorComparison_const_in_sector` records that the sector statement does not depend on which
  sector is chosen.

So P4 does not decompose over the parity split.  The split localises the **closure** (§44), not the
elliptic estimate: both sectors inherit the identical open problem, and the sharp constant is the
same in both.  This is not a limitation of the formalisation but the content of the model's parity.

### 45.4. What this does not prove

`PotSelfBound` / `FormDomainComparison` for the quartic `W` remains a hypothesis, unchanged and with
its constant free.  Nothing here bounds the potential, produces the reverse elliptic estimate, or
supplies the missing form-domain comparison: the module shows that the sector route cannot supply it
either, and removes that route from the search space.

### 45.5. Verification performed (2026-11-12)

* `lake build BookProof.Sm.ChapterSmSectorFormDomain` — clean, no warning, no line over 100 columns.
* `lake build Work.SmSectorFormDomainAudit` — 17 declarations, each `#print axioms` reporting exactly
  `propext, Classical.choice, Quot.sound`, no `sorryAx`.
* `lake env lean BookProof.lean` after registering the import — exit 0.

## §46. The BRST quotient on top of the parity split (2026-11-12)

Module: `BookProof/Sm/ChapterSmBrstQuotient.lean`, namespace `BookProof.SmBrstQuotient`.

### 46.1. What is built

The algebra P5's physical half needs, in the indefinite-metric form a BRST charge actually requires
(in a positive-definite space a nilpotent self-adjoint charge vanishes, so "quotient by the exact
space and inherit the ambient inner product" is not the physical construction):

* **Nilpotency and the two spaces.**  `IsBrst Q` is `Q² = 0`; the gauge orbit is `gauge Q = im Q`
  and the closed space is `closed Q = ker Q`; nilpotency puts the former inside the latter
  (`gauge_le_ker`).
* **The charge form** `kform η x y = ⟪x, ηy⟫`, with its additivity in both slots.
* **Ghost nullity.**  If the charge is symmetric for the charge form,
  `kform η (Qx) y = kform η x (Qy)`, then every exact vector is null against every closed vector
  (`kform_ghost_null`, and `kform_ghost_null_right` from the Hermitian symmetry).
* **The form is well defined on the cohomology.**  Two representatives in the closed space that
  differ by a gauge orbit give the same charge form (`kform_well_defined`) — this is what lets the
  physical form live on `ker Q / im Q` rather than on `ker Q`.
* **Parity descent.**  A unitary involution commuting with the charge preserves the closed space and
  the gauge orbit (`U_mem_closed`, `U_mem_gauge`); the metric operator maps each sector into itself,
  so the sectors stay **orthogonal for the charge form** (`kform_eq_zero_of_mem_even_of_mem_odd`,
  `kform_eq_zero_of_mem_odd_of_mem_even`); the quadratic form therefore splits,
  `kform_quadForm_split`, and non-negativity is a **sector-by-sector** statement
  (`kform_quadForm_nonneg`, `physicalPositivity_nonneg_of_sectors`).

### 46.2. What is not built — the named input

`PhysicalPositivity Q η` (non-negative on the closed space, radical there exactly the gauge orbit) is
a **definition, not a theorem**, and it is not proved anywhere in the corpus for the matter model.
It is the Kugo–Ojima no-ghost condition, and proving it requires the quartet structure of the
model's actual BRST charge, which has not been constructed.  Consequently:

* no positive physical inner product is produced for the SM;
* the BRST charge of the matter model itself is not constructed here (the module is generic in `Q`
  and `η`);
* what the module supplies is the reduction — well-definedness, the graded splitting and the
  sector-local positivity criterion — so that a future quartet construction has only the two sector
  conditions left to verify.

### 46.3. Verification performed (2026-11-12)

* `lake build BookProof.Sm.ChapterSmBrstQuotient` — clean.
* `lake build Work.SmBrstQuotientAudit` — 22 declarations, axioms exactly
  `propext, Classical.choice, Quot.sound`, no `sorryAx` (note `PhysicalPositivity` is audited as a
  definition and its axiom list is inherited from the definitions it mentions).
* `lake env lean BookProof.lean` — exit 0.

## §47. The quartet structure behind the BRST charge (2026-11-12)

Module: `BookProof/Sm/ChapterSmQuartet.lean`, namespace `BookProof.SmQuartet`.

### 47.1. What §46 left open, and what closes it

§46 reduced the physical-positivity question to the Kugo–Ojima condition `PhysicalPositivity`, as a
**named input**.  That input is not idle: nilpotency alone cannot give it (in a definite space a
nilpotent self-adjoint charge vanishes).  The mechanism that does give it is the quartet, and it is
one identity:

  `Q P + P Q = 1 − V`,  with `Q² = 0`, `V` a projector, `V`'s range inside `ker Q`.

On a quartet block the right-hand side is the identity — `Q` pairs the two members and the b-ghost
`P` pairs them back — and on the physical subspace it vanishes.  `BrstQuartet Q` is that data.

### 47.2. What is proved

* **The hypothesis set is not over-specified.**  `V Q = 0` is *derived* from the quartet identity and
  `Q² = 0` (`quartet_physProj_comp_Q`): applying `Q` to the identity at `x` gives
  `Q (P (Q x)) = Q x`, the identity at `Q x` gives `Q (P (Q x)) = Q x − V (Q x)`, hence `V (Q x) = 0`.
* **Every closed vector splits as exact plus physical**: `x = Q (P x) + V x` (`quartet_decompose`).
* **The charge form sees only the physical part** (`kform_quartet_reduce`): the exact–exact term
  vanishes by nilpotency (`kform_exact_self`), and both cross terms vanish by §46's ghost nullity and
  the symmetry of the form.
* **The no-ghost theorem** (`physicalPositivity_of_quartet`): if the metric operator fixes the range of
  `V` — the physical subspace sits in the ghost-parity-even sector, which is what the no-ghost theorem
  asserts — then on the closed space `⟨x,x⟩_η = ‖V x‖²`, so the form is non-negative and its radical
  is exactly the gauge orbit (`‖V x‖ = 0` ⟹ `x = Q (P x)`).  **`PhysicalPositivity` is a theorem
  here, not an input.**
* **Sector by sector** (`kform_quartet_reduce_sectors`, `physicalPositivity_of_quartet_sectors`):
  composing with §46's parity split, positivity known one parity sector at a time — non-negativity
  plus definiteness on the physical subspace inside each sector — assembles into the whole statement.
  This is the shape a physical smoke test takes.
* **The 2⊕1-dimensional instance** (`exQuartet`, `exPhysicalPositivity`): `Q : e₀ ↦ e₁`, `P : e₁ ↦ e₀`,
  `V : e₂ ↦ e₂`, indefinite metric `σ₁` on the block and the identity on the physical line.  All four
  quartet fields and both metric hypotheses are verified (`exQ_nil`, `exQuartet_anticomm`,
  `exEta_physProj`, `exKrein`, `exSymm`), and the instance is **not vacuous**: the physical line is
  closed (`exE2_closed`) but not exact (`exE2_not_exact`), so the cohomology is one-dimensional.
* **The link to the SM charge**: `isBrst_smBrstCharge` — `IsBrst` for `smBrstCharge` follows from
  `smBrstCharge_nilpotent` (§36), via `Module.End.mul_eq_comp`.

### 47.3. What is not built

The quartet *data* `(P, V)` for the gauge-fixed matter model.  §47 proves that quartet data yields
the no-ghost theorem and that the SM charge is a BRST charge; it does **not** construct the b-ghost
that pairs each longitudinal/ghost mode of the matter model with its partner.  So:

* `PhysicalPositivity` for the SM remains unproved — what changed is that it no longer has to be
  assumed *in addition* to a quartet decomposition, it is derived from one;
* the module is generic in the Hilbert space and the charge, which is what allows §47.2's instance to
  be checked independently of the SM's 163-coordinate normal form.

### 47.4. Verification performed (2026-11-12)

* `lake env lean BookProof/Sm/ChapterSmQuartet.lean` — exit 0, no warnings.
* `lake build BookProof.Sm.ChapterSmQuartet` — clean (6.1 s).
* `lake env lean Work/SmQuartetAudit.lean` — 23 declarations, axioms exactly
  `propext, Classical.choice, Quot.sound`, no `sorryAx`.
* `lake env lean BookProof.lean` — exit 0.
* `scripts/check-sm-section-guards` — see §48.4.
* **Merge note (2026-11-13):** a parallel local draft of §47 (a 294-line module with a degenerate
  `ℂ³` instance, `exQuartet'`) was dropped on merging with this branch.  This section and §50 are
  the survivor: the instance here is the non-vacuous `2 ⊕ 1` Krein one (`exQuartet`), and §50
  removes `V` from the inputs altogether.  The merged tree was re-verified on 2026-11-13 (§47.4
  bullets above, re-run: clean build, axioms unchanged).

## §48. The reverse elliptic estimate for the quartic potential (2026-11-12)

Module: `BookProof/Sm/ChapterSmReverseEllipticQuartic.lean`, namespace
`BookProof.SmReverseEllipticQuartic`.

### 48.1. The estimate, and the one hypothesis it needs

§31 reduced `PotSelfBound P c₀ β` — `‖W p + p‖ ≤ β ‖(−Δ_S + W + 1) p‖` — to an exact residual and
showed that the sign route lands on a gradient-residual condition comparing a *degree-six* density
with a *second-order* norm; §35 showed the quartic uncertainty bound is weaker than that condition,
and one-sided in the wrong direction for closing it.  This section takes the other route.

With `u = pgLp p`, `w = pgLp (W p)`, `k = pgLp (Δ_S p)`, `B = w + u`, `N = k + B`, one has
`B = N − k` **identically**, hence

  `‖B‖² = Re ⟪B, N⟫ − Re ⟪B, k⟫`,

and §23's weighted integration-by-parts identity (`sm_weighted_kinetic_ibp`) evaluates the second
term as `∑_j [Re ⟪(∂_j W) p, D_j p⟫ + Re ⟪W D_j p, D_j p⟫]`.  The second sum is non-negative because
`W ≥ 0` (`gaussInt_weighted_self_nonneg` against `smPotPoly_nonneg`), so what survives is the **single
commutator term** `∑_j Re ⟪(∂_j W) p, D_j p⟫`.  Cauchy–Schwarz over `j` (`Finset.sum_mul_sq_le_sq_mul_sq`)
and Young (`sqrt_mul_le_div`) turn it into

  `(1 − a'/(4η)) ‖B‖² ≤ ‖B‖ ‖N‖ + C_η ‖N‖²`,

with the only inputs besides the algebra

* `‖p‖ ≤ ‖N‖` (§32's `norm_le_shiftNorm_of_coercive`) and
* `∑_j ‖D_j p‖² ≤ ‖N‖²` (`sum_coreD_sq_le_shiftNorm_sq`), and
* the **gradient domination**

  `∑_{j∈S} ‖(∂_j W) p‖² ≤ a ‖W p‖² + b ‖p‖²`   (`GradDom`, `b ≥ 0`).

`norm_le_of_quad_le` completes the square and yields an explicit constant, so
**`exists_potSelfBound_of_gradDom`**: `GradDom` ⟹ `∃ β, PotSelfBound P c₀ β`.  No elliptic regularity
and no form-domain comparison is used anywhere in that argument.

### 48.2. `GradDom` is the residual input, and it is not automatic

`GradDom` is a condition on the polynomial alone, so §48.3 settles its status rather than leaving it
as a slogan:

* **It holds for a coercive quartic.**  `gradDom_coercive_quartic`: for `W = X₀⁴ + X₁⁴` one has
  `|∂₀W|² + |∂₁W|² = 16(x₀⁶ + x₁⁶) ≤ 16 W² + 32` at every point, from `t⁶ ≤ t⁸ + 1`.
* **It fails for a flat quartic.**  `not_gradDom_flat_quartic`: for `W = X₀²X₁²` — non-negative, degree
  four, flat on both coordinate hyperplanes — there are **no** `a, b` with
  `|∂₀W|² + |∂₁W|² ≤ a W² + b`: on the curve `(t, 1/t)` the left side is `4(t² + t⁻²)` while the right
  side is the constant `a + b`.

So `GradDom` is a genuine restriction, not a consequence of `W ≥ 0` and `deg W = 4`.  This is exactly
why `PotSelfBound` stays a hypothesis for the SM: `smPotPoly` is a sum of squares of quadratics
(`polyW_smPotPoly`), and a quadratic factor that couples `X_i` to another coordinate produces the
`X₀²X₁²` pattern — non-coercive — so the domination must be established for the actual 49 field
polynomials, and it is not established here.

### 48.3. What this does and does not settle

* **Settled**: the reverse estimate is *not* a matter of elliptic regularity.  Given the gradient
  domination, it is a two-line consequence of §23's sign identity plus Cauchy–Schwarz–Young, and the
  argument is complete and axiom-clean (`exists_potSelfBound_of_gradDom`).
* **Settled**: the domination hypothesis is a genuine algebraic condition — true for coercive
  quartics, false for flat ones.
* **Not settled**: `GradDom` for `smPotPoly P c₀`.  `PotSelfBound` therefore remains a named input
  downstream, and P4 is unchanged in status: it is now *one algebraic question about `smPotPoly`*
  rather than *an analytic statement about `−Δ_S + W`*.

### 48.4. Verification performed (2026-11-12)

* `lake env lean BookProof/Sm/ChapterSmReverseEllipticQuartic.lean` — exit 0, no warnings.
* `lake build BookProof.Sm.ChapterSmReverseEllipticQuartic` — clean.
* `lake env lean Work/SmReverseEllipticQuarticAudit.lean` — 16 declarations, axioms exactly
  `propext, Classical.choice, Quot.sound`, no `sorryAx`.
* `lake env lean BookProof.lean` — exit 0.
* `scripts/check-sm-section-guards` — green on the tree; and it was driven adversarially against a
  synthetic tree to confirm the aggressor property: deleting any one side of a guarded pair makes it
  exit 1 with a `[FAIL]` line naming the missing statement (verified for the §45 "no weakening"
  verdict, `dense_colouredCore`, and the plan's meson/glueball entry).

## §49. Which of the 49 directions are flat, and why `GradDom` nevertheless holds (2026-11-12)

Modules: `BookProof/Sm/ChapterSmGradDomStructural.lean` (namespace
`BookProof.SmGradDomStructural`), audit `Work/SmGradDomStructuralAudit.lean`.

### 49.1. The question, and the answer

§48 reduced P4 to `GradDom` — `∑_{j∈S} ‖(∂_jW)p‖² ≤ a‖Wp‖² + b‖p‖²` — and left it open, with the
flat `X₀²X₁²` pattern named as the worry.  The answer is **affirmative**: `GradDom` holds for
`W = smPotPoly P c₀` (`c₀ ≥ 0`), and *not* because `W` is coercive as a quartic (it is not), but
because `W` contains the **coercive quadratic** `∑_{m∈M} q_m²` and every `∂_j Φ_r` (`j ∈ M`, the 40
momentum coordinates) is at most **linear**.  Then `|∇W|² ≲ (1 + W)·W ≤ aW² + b`.

The two facts are proved in the module as the structural theorem, and the flat pattern is
*exhibited* as rescued, not argued away:

* `wsSum`/`polyW_wsSum`/`polyW_pderiv_wsSum` — the shape `W = ∑_r Φ_r² + ∑_m x_m² + c₀`, its value
  `∑_r Φ_r(x)² + ∑_m x_m² + c₀`, and its derivative `2∑_r Φ_r ∂_jΦ_r + 2x_j` on `M`;
* `GradBound` — the per-form hypothesis `(∂_jΦ_r)² ≤ C(1 + ∑_m x_m²)`;
* `sq_pderiv_le` — one coordinate: Cauchy–Schwarz `(∑_r A_rB_{jr})² ≤ (∑_r A_r²)(∑_r B_{jr}²)` with
  `∑_r A_r² ≤ W` and `∑_r B_{jr}² ≤ |ι|C(1+S²)`, then `2ab ≤ a² + b²`;
* **`pointwise_dom_of_sq_sum`** — `∑_{j∈M} (∂_jW)² ≤ (16|M||ι|C + 8)W² + (8|M||ι|C + 8)`;
* **`gradDom_flat_plus_quadratic`** — the model instance `X₀²X₁² + X₀² + X₁²`: `|∂₀W|² + |∂₁W|² ≤
  40W² + 24`, whereas §48's `not_gradDom_flat_quartic` shows the bare `X₀²X₁²` obeys no such bound.
  This is the theorem that says the flat directions are not an obstruction.

### 49.2. The classification of the 49 forms

`smPhi P r = smFormPoly P id (smFormFin.symm r)`, with `SmForm` the five families of
`ChapterSmHamiltonian` (24 + 9 + 3 + 12 + 1 = 49).  For `j` in the 40 momentum coordinates
(`smS`), `∂_jΦ_r` never involves the derivative coordinates `smDG`/`smDW`/`smDB`/`smDPhi` (those
carry no momentum and are not controlled by `W`), and it is at most linear.  What the family is,
and where it is flat:

| family | count | shape | `∂_jΦ_r ≠ 0` in | flat in |
|---|---|---|---|---|
| gluon magnetic `smMagG` | 24 | `½ε_{ijk}(∂_kG − ∂_jG + g_s f^{abd}G^b_jG^d_k)` | `G` (linear) | `φ`, `W`, `B`; and at `G = 0` |
| weak magnetic `smMagW` | 9 | `½ε_{ijk}(∂_kW − ∂_jW + g_w e^{mbd}W^b_jW^d_k)` | `W` (linear) | `G`, `φ`, `B`; and at `W = 0` |
| hypercharge `smMagB` | 3 | `½ε_{ijk}(∂_kB − ∂_jB)`, **purely derivative** | none | all 40 |
| covariant Higgs `smCovD` | 12 | `φ_{a,i} + g_w(τ_j/2φ)_a W^j_i + g_y(σ₃/2φ)_a B_i` | `W`, `B`, `φ` (linear) | `G`; and at `φ = 0` or `W = B = 0` |
| wall `smWall` | 1 | `√(λ/2)(‖φ‖² − v²)` | `φ` (linear) | `G`, `W`, `B` |

So **none** of the 49 is a coercive quartic except the wall, and the 33 magnetic ones have exactly
the `X₀²X₁²` shape — their squares vanish on a coordinate hyperplane and their gradients grow
without bound along `(t, 1/t)` in the `G`-variables.  The flat pattern is therefore *present*; §49.1
is why it does not matter.

### 49.3. What this settles, and the two steps that remain

* **Settled**: `GradDom` is not refuted by the SM's flat directions — the answer to the question is
  affirmative, with a proved mechanism and a proved model instance.
* **Not formalized** (both named in the module and in `BookProof.lean`):
  1. the **per-form support table** of §49.2 as Lean facts about `pderiv j (smPhi P r)`: at most
     linear, and no coordinate outside `smS` (this needs the `pderiv`/support analysis of the five
     families, and the index-distinctness lemmas `smG_ne_smDG` and friends);
  2. the **`L²` transfer** from the pointwise bound to `GradDom`: Gaussian-integral monotonicity
     (`gaussInt_re_mono`) against `norm_pgLp_sq`, multiplied pointwise by the non-negative weight
     `cpoly p * p` (as in `eval_weighted_self_re`).  §48's docstring previously cited a
     `l2_gradDom_of_pointwise` for this; **that lemma does not exist** and the citation has been
     corrected — the passage is routine but unformalized.
* Therefore `PotSelfBound` for `smPotPoly` remains a hypothesis, now with an affirmative answer to
  the algebraic question standing between it and a proof.

### 49.4. Verification performed (2026-11-12)

* `lake env lean BookProof/Sm/ChapterSmGradDomStructural.lean` — exit 0, no warnings.
* `lake build BookProof.Sm.ChapterSmGradDomStructural` — clean (8170 jobs).
* `lake env lean Work/SmGradDomStructuralAudit.lean` — 19 declarations, axioms exactly
  `propext, Classical.choice, Quot.sound`, no `sorryAx`.
* `lake env lean BookProof.lean` — exit 0.
* `scripts/check-sm-section-guards` — extended with the §48/§49 pair (coercive, flat, model); driven
  adversarially: deleting `not_gradDom_flat_quartic` makes it exit 1 with two `[FAIL]` lines.

## §50. The physical projector is constructed from the b-ghost (2026-11-12)

Module: §5 of `BookProof/Sm/ChapterSmQuartet.lean` (namespace `BookProof.SmQuartet.BrstQuartet`),
audit `Work/SmQuartetConstructedAudit.lean`.  This is §47.5 of the plan's ordering; it is recorded
here so that the two follow-ups of 2026-11-12 stay together.

### 50.1. The construction

§47 assumed quartet data `(P, V)`.  The projector is in fact determined by the b-ghost:

* **`physProjOf Q P = 1 − (QP + PQ) + Q P²Q`**, **`bGhostOf Q P = P − Q P²`**.
* From `Q P Q = Q` and `P Q P = P` (the two contraction identities a b-ghost satisfies):
  `QP` and `PQ` are idempotent, `(PQ)(QP) = P Q² P = 0`, and `(QP)(PQ) = Q P²Q` — so with
  `Π = QP + PQ − Q P²Q` one has `Π² = Π`; `V = 1 − Π` is a projector (`physProjOf_idem`), `QV = 0`
  (`physProjOf_Q`) and `VQ = 0` (`physProjOf_comp_Q`), and `Q P' + P' Q = Π = 1 − V`
  (`bGhostOf_anticomm`).  The correction term is not cosmetic: the naive `1 − (QP + PQ)` fails
  idempotency, and the naive `P` misses the anticommutator, by the *same* product `Q P²Q`.
* **`quartetOfHomotopy`** assembles a `BrstQuartet Q` from `(Q, P)` alone;
  **`physicalPositivity_of_homotopy`** is then the no-ghost theorem from a single object.

### 50.2. The ghost-parity-even sector

`V` is a polynomial in `Q` and `P`, so a parity `U` commuting with both (`physProjOf_commute_parity`)
makes `V` parity-even, hence `V` maps `evenSpace U` into itself (`physProjOf_mem_even`) — the
physical subspace *restricted to the even sector* is `V`'s range there.  With the sector hypotheses
of §45/§47 (`U² = 1`, isometric, `ηU = Uη`), **`physicalPositivity_of_homotopy_sectors`** concludes
`PhysicalPositivity`: non-negativity and definiteness are needed only on the physical subspace
inside each sector.

### 50.3. What is and is not constructed

* **Constructed**: `V` (and the quartet's `P`) from one input, the contracting homotopy — checked
  against the worked example: `exQ_exP_exQ`, `exP_exQ_exP`, and `exP_exQ_exP_gives_V`
  (`physProjOf exQ exP = exV`), so the construction reproduces §47's model projector.
* **Not constructed**: the Standard Model's own b-ghost, i.e. the pairing of each
  longitudinal/ghost mode of the matter model with its partner.  `PhysicalPositivity` for
  `smBrstCharge` therefore stays a hypothesis; what changed is that it now has **one** named
  input instead of two, and that the parity refinement is automatic once that input is parity-even.

### 50.4. Verification performed (2026-11-12)

* `lake env lean BookProof/Sm/ChapterSmQuartet.lean` — exit 0, no warnings.
* `lake env lean Work/SmQuartetConstructedAudit.lean` — 18 declarations, axioms exactly
  `propext, Classical.choice, Quot.sound`, no `sorryAx`.
* `lake env lean BookProof.lean` — exit 0; `scripts/check-sm-section-guards` — green, with the new
  §47.5 needles (`physProjOf`, `physicalPositivity_of_homotopy`, `exP_exQ_exP_gives_V`).

## 51. The linear-form bridge: `GradBound` reduced to a support table (P4)

§49 left `GradDom` conditional on two steps, the first of which was the *per-form support table*:
for `j ∈ smS`, `pderiv j (smPhi P r)` must be at most linear and must not involve the derivative
coordinates `smDG`/`smDW`/`smDB`/`smDPhi`.  §51 carries out the algebra of that step, so the table
becomes the only remaining input.

### 51.1. The reduction

`BookProof/Sm/ChapterSmGradDomStructural.lean` §3b adds:

* `linForm b L = ∑_{i∈L} C (b i) * X i` — a linear form with real coefficients, and
  `realCoeff_linForm`, `polyW_linForm` (`polyW (linForm b L) x = ∑_{i∈L} b i * x i`);
* **`sq_polyW_linForm_le`** — for `L ⊆ M`,
  `(polyW (linForm b L) x)² ≤ (∑_{i∈L} (b i)²) (1 + ∑_{m∈M} x_m²)`.
  This is `Finset.sum_mul_sq_le_sq_mul_sq` (Cauchy–Schwarz) followed by monotonicity of the sum
  under `L ⊆ M`, so the coercive quadratic of `W` on `M` alone controls the form;
* **`gradBound_of_linear`** — if for every `j ∈ M` and every form `r` there are a support `L j r ⊆ M`
  and coefficients `b j r` with `pderiv j (Φ r) = linForm (b j r) (L j r)`, then
  `GradBound Φ M (∑_{j∈M} ∑_r ∑_{i∈L j r} (b j r i)²)`.

`gradBound_of_linear` is the composition with `pointwise_dom_of_sq_sum` that §49.3 anticipated: a
support table plus Cauchy–Schwarz gives the per-form bound, and the per-form bound gives the
pointwise domination `∑_{j∈M} (∂_j W)² ≤ a W² + b`.  The model check
`sq_polyW_linForm_le_model` (with `linForm_unit_eq : linForm (fun _ => 1) {1} = X₁`) shows the
inequality is the sharp one on the flat-quartic model's differentiated coordinate.

### 51.2. What this does and does not close

* **Closed**: no further analysis is needed once the `pderiv` computation for the five families is
  available.  In particular the *coefficients* are no longer part of the open problem — they enter
  only through the sum of squares, which `gradBound_of_linear` produces mechanically.
* **Open**: the `pderiv` computation itself.  It is a finite, per-family statement about
  `smFormPoly`: `∂(smMagG)` in a gauge coordinate is `½ ε · (structure constant) · X(W)`, `∂(smMagB)`
  is `0` (the hypercharge form is purely derivative), `∂(smCovD)` in `W`/`B`/`φ` is a constant times
  `X(φ)` or `X(W)`/`X(B)`, `∂(smWall)` is `√(λ/2) · 2 X(φ)`.  None of these meets a derivative
  coordinate, which is the substantive content of the table.  Still not formalized, so `GradDom`
  for `smPotPoly` remains a hypothesis.
* **Unchanged**: the pointwise→`L²` transfer (`exists_potSelfBound_of_gradDom` consumes the `L²`
  form), and the SM's own b-ghost.

### 51.3. Verification performed (2026-11-12)

* `lake build BookProof.Sm.ChapterSmGradDomStructural` — 8170 jobs, clean, no warnings.
* `lake env lean Work/SmGradDomStructuralAudit.lean` — 28 declarations, axioms exactly
  `propext, Classical.choice, Quot.sound`, no `sorryAx`.
* `scripts/check-sm-section-guards` — green, with new §49.3b needles (`sq_polyW_linForm_le`,
  `gradBound_of_linear`).

## 52. The pointwise-to-`L²` transfer, and `PotSelfBound` from the table alone (P4)

§49 left two steps under `GradDom`: the per-form support table and the passage from the pointwise
domination to the `L²` inequality.  §51 reduced the first; §52 closes the second, so what is left of
P4 is a finite algebraic computation.

### 52.1. The transfer

`BookProof/Sm/ChapterSmGradDomTransfer.lean` (concurrent session, commit `f240c22`) carries
`∑_{j∈M} (∂_j W)(x)² ≤ a W(x)² + b` to

  `∑_{j∈M} ‖(∂_j W) p‖² ≤ a ‖W p‖² + b ‖p‖²`

by Gaussian-integral monotonicity: the pointwise bound is multiplied by the non-negative `‖p(x)‖²`
and integrated.  The evaluation identities `eval_real_of_realCoeff`, `norm_eval_sq_eq_polyW_sq`,
`eval_cpoly_mul_re`, `eval_sum_cpoly_re` supply the pointwise shapes, `l2_gradDom_of_pointwise` is
the transfer, and `exists_potSelfBound_of_pointwise` composes it with §48's
`exists_potSelfBound_of_gradDom`.

### 52.2. The chain from the table

`exists_potSelfBound_of_gradBound` closes the loop: a `GradBound` for the 49 forms at a constant `C`
gives `∃ β, PotSelfBound P c₀ β`, with the explicit constants `a = 16 |smS| 49 C + 8`,
`b = 8 |smS| 49 C + 8`.  The step that makes this an instance of the SM rather than of a generic
potential is `smPotPoly_eq_wsSum` (§49.3c): `smPotPoly P c₀` *is* `wsSum` at the 49 forms and the 40
momentum coordinates, `Finset.sum_image` along `smCoord_injective` being the reindexing.

So P4 now depends on one input, the per-form `pderiv` table: `∂_j (smPhi P r)` is a linear form
supported in `smS` for every `j ∈ smS`.  §51's `gradBound_of_linear` turns that table into
`GradBound`; §52 turns `GradBound` into `PotSelfBound`.  No analysis and no further algebra lies
between them, and until the table is written down `PotSelfBound` remains a hypothesis.

### 52.3. Verification performed (2026-11-13)

* `lake build BookProof.Sm.ChapterSmGradDomStructural BookProof.Sm.ChapterSmGradDomTransfer
  BookProof.Sm.ChapterSmReverseEllipticQuartic` — clean.
* `lake env lean Work/SmGradDomStructuralAudit.lean` — 28 declarations, axioms exactly
  `propext, Classical.choice, Quot.sound`, no `sorryAx`.
* `lake env lean Work/SmGradDomTransferAudit.lean` — 8 declarations, same three axioms, no `sorryAx`.
* `lake env lean BookProof.lean` — exit 0.
* `scripts/check-sm-section-guards` — green, with the §49.3b/§49.3c and §52 needles.

These changes landed inside commit `09aabdd` (the concurrent session's symbol-gate commit took the
staged files with it), so §52.1–§52.3 and `Work/SmGradDomTransferAudit.lean` are recorded here for
the provenance the commit message does not carry.  The old
  "unformalized `L²` transfer" caveat needle is replaced in the same commit by the §49 block's
  `per-form \`pderiv\` table` caveat, since the caveat itself is now obsolete; the pderiv table is
  still not written down, so the caveat is preserved in its narrowed form rather than deleted.

## 53. The per-form `pderiv` table, and `PotSelfBound` discharged (P4 closed)

§52 left P4 depending on one input: for `j ∈ smS`, each `∂_j Φ_r` of the 49 forms is a linear form
supported in `smS`.  §53 supplies it, and with it `PotSelfBound` stops being a hypothesis.

### 53.1. Normal forms instead of 49 computations

Writing the table out form by form would mean 49 computations through `levi`, `fabc`, `eabc`,
`tgen`, `ygen` and the `Fin 3`/`Fin 8` index sums, and every one of them would be a place to be
wrong.  `BookProof/Sm/ChapterSmGradTable.lean` avoids all of it with a *normal form*: `Biform A T`
carries the polynomial together with its coefficients —

  `poly = C cst + ∑_a C (linf a) · X a + ∑_a ∑_c C (sqf a c) · (X a * X c)`,

with `linf` supported in `T` and `sqf` supported in `A × A`.  The constructors (`const`, `atom`,
`atomSq`, `lin`, `sq`, `add`, `sub`, `smul`, `sum`) are closed under the shapes the Hamiltonian
uses, so a form is recognised **by shape alone**, and the coefficients are whatever they are.

Two lemmas then finish the job:

* `pderiv_eq` — for `j ∈ A`, `∂_j poly = ∑_v C (sqf j v + sqf v j) · X v`.  The linear part
  contributes `linf j`, which is `0` because `A` and `T` are disjoint; the bilinear part
  contributes the row and the column of `sqf` at `j`.  `pderiv_lin_sum` and `pderiv_sq_sum` are the
  two computations, both `Finset.sum_eq_single` plus the product rule.
* `sq_le` — Cauchy–Schwarz against the coercive quadratic on `A`: the derivative's coefficients are
  square-summed, so **no numerical constant is quoted anywhere**.  The support argument is the whole
  point: the derivative coordinates `smDG`/`smDW`/`smDB`/`smDPhi` never appear.

### 53.2. The five families and the 49

`smT := univ \ smS`, `Disjoint smS smT` is `Finset.disjoint_sdiff`, and the four derivative families
are proved outside `smS` by `notMem_of_coord` — membership in `smS` being membership in the image of
`smMomCoord`, a four-case `SmMom` split resolved by `smIdx.injective`.  Then

`biform_smMagG`/`biform_smMagW`/`biform_smMagB`/`biform_smCovD`/`biform_smWall`

are `Biform smS smT` by `refine` chains of constructors, with the `_poly` lemmas closing by `rfl` —
the built polynomial *is* the definitional formula, which is worth checking rather than asserting.
`biform_form` assembles the `SmForm`-indexed family and `biform_smPhi P r := biform_form P
(smFormFin.symm r)` is all 49.

### 53.3. The discharge

`gradBound_smPhi` is `GradBound` at the constant `∑_{j∈smS} ∑_r ∑_{v∈smS} (sqf j v + sqf v j)²`, by
two `Finset.single_le_sum` steps, and

  **`exists_potSelfBound_sm (P) (hc0 : 0 ≤ c0) : ∃ β, PotSelfBound P c0 β`**

follows from §52's `exists_potSelfBound_of_gradBound`.  The elliptic input of P4 is therefore
proved, not assumed — for the potential's own self-bound.

### 53.4. What this does not say

`PotSelfBound` is the *potential's* self-boundedness.  What still stands:

* P5's physical input is untouched: `PhysicalPositivity` still needs the matter model's own quartet
  data (§46/§47), and no physical inner product is claimed.
* The joint model's dynamics — the identification of the gauge-fixed joint rational solver with this
  comparison operator — is not addressed here; `PotSelfBound` is an estimate about `W`, not a
  spectral statement about the joint operator.
* `0 ≤ c₀` is needed (the `+1` shift of the comparison), and the constant `β` is produced, not
  computed sharply.

Six prose blocks claimed the self-bound was still open — §22, §23, §26, §27, §35 in `BookProof.lean`
and `ChapterSmKineticGarding`'s docstring — and all of them, plus the two `PotSelfBound`-caveat
needles in `scripts/check-sm-section-guards`, are corrected in this commit rather than left to
contradict the theorem.

### 53.5. Verification performed (2026-11-13)

* `lake build BookProof.Sm.ChapterSmGradTable` — clean, no warnings.
* `lake env lean Work/SmGradTableAudit.lean` — 20 declarations, axioms exactly
  `propext, Classical.choice, Quot.sound`, no `sorryAx`.
* `lake build BookProof.Sm.ChapterSmKineticGarding` — clean.
* `scripts/check-sm-section-guards` — green, with the §53 needles (`exists_potSelfBound_sm`, and the
  surviving `quartet data` caveat).

## §54. What `PotSelfBound` now yields, and where the normal form stops (2026-11-13)

### 54.1. The downstream statements are instantiated, not conditional

§53 produced `∃ β, PotSelfBound P c₀ β` for `0 ≤ c₀`, while §15 and §19 state their consequences with
`β` as a *parameter* — so on their own they were conditionals waiting for a value.  Four theorems in
`ChapterSmGradTable` now discharge the wait:

* `PotSelfBound_mono` — monotone in `β`.  Its use is the next line: the produced `β` can be replaced
  by `|β|`.
* `exists_potSelfBound_sm_nonneg` — `∃ β, 0 ≤ β ∧ PotSelfBound P c₀ β`.  Needed because `hpoly` and
  the P2 bound both carry `1 + β`, where a sign of `β` is a sign inside a bound.
* `exists_kineticSum_bound_sm` — **§19's `hpoly`**, by §26's `kineticSum_norm_le_of_pot_self_bound`:
  `∃ β ≥ 0, ∀ x, ‖∑_m smPi m (smPi m x)‖ ≤ (1 + β) ‖smFlN P c₀ x + x‖`.  §22 and §26 recorded
  `hpoly` and `PotSelfBound` as equivalent spellings of one statement; the equivalence is now an
  instantiation rather than a promise.
* `exists_smNormalForm_norm_le` — **§15's P2 second-order family bound**, by
  `smNormalForm_norm_le_of_pot_self_bound`, at the same `∃ β`.

§15's lemma carries four hypotheses (`_hpos`, `_hkin`, `_hcoord`, `_hmass`) that its proof does not
consume.  They are kept — `_`-prefixed and documented in the docstring — so this theorem is a drop-in
replacement; they are not silently deleted, and the statement is not quietly strengthened.

### 54.2. The machinery transfers; the conclusion does not

The second question — does the normal form prove QYM's and NS's gradient domination the same way? — has
a split answer, and the split is the content.

*The machinery transfers.*  `Biform A T`, `pderiv_eq` and `sq_le` quantify over the dimension, the atom
set and the polynomial: nothing in them refers to the SM's 163 coordinates, to `smS`, or to the gauge
content.  Any form that is "linear in a derivative, bilinear in a field" — the QYM field strengths, the
NS convection terms, the SM's five families — *is* a normal form, with its derivative read off the
coefficients and its square bounded by Cauchy–Schwarz.

*The conclusion does not transfer*, and not because a proof is missing: `GradDom` is **false** for the
QYM potential.  `sq_le` bounds `(∂_j Φ)²` by the coercive quadratic `1 + ∑_{m∈A} x_m²`, so the
domination needs a `W` that contains that quadratic.  The SM's `smPotPoly` has `∑_m q_m²` (§49); the
QYM comparison's Weyl potential is `weylPotPoly Φ = ∑_j Φ_j² + 1`, and at a single bilinear form it is
literally `weylFlat`, which `weylFlat_eq_weylPotPoly` identifies with
`BookProof/YangMillsNonAbelianEsa`'s `weylPotPoly (fun _ : Fin 1 => X₀X₁)`.  Then `not_gradDom_weylFlat`: there are no `a b` with
`‖∂₀W‖² + ‖∂₁W‖² ≤ a‖W‖² + b` everywhere, because on the curve `(t, 1/t)` the left side is
`4/t² + 4t²` while `W` stays `2`.  This is §48's flat mechanism, not a new phenomenon.

### 54.3. What that means for P4 in those models

The normal form is reusable — it is the right way to build a per-form `pderiv` table anywhere.  Gradient
domination is an *analytic* input specific to potentials carrying a coercive quadratic; for QYM/NS it
must be supplied from that model's own structure (a confining term, a mass term, or an anisotropic
weight), not imported from the SM.  Nothing here claims QYM's or NS's elliptic estimate beyond this
obstruction — and only the QYM instance is formalised: the corpus's NS modules are operator-level
(`BookProof/Ns/*`), so there is no NS polynomial potential to run the `(t, 1/t)` computation against,
and the NS statement is the proof template, not a proved counterexample.

### 54.4. Verification performed (2026-11-13)

* `lake env lean BookProof/Sm/ChapterSmGradTable.lean` — clean, no warnings.
* `lake build BookProof.Sm.ChapterSmGradTable` — `Build completed successfully`.
* `lake env lean Work/SmGradTableAudit.lean` — 30 declarations, every one on exactly
  `propext, Classical.choice, Quot.sound`; no `sorryAx`.
* `lake build BookProof` was not run to completion *in that round* (it exceeded a 600 s budget), and the
  root module `BookProof.lean` compiled directly was the substitute check.  **It has since completed:**
  see §55.4 — the substitute check was sound but is no longer the strongest available statement.

## §55. What restores the domination, and where the quartet construction stops (2026-11-13)

### 55.1. The converse of §54.2, and what it says about the obstruction

§54 proved the domination *fails* for the QYM potential and identified the reason: `sq_le` bounds the
derivative against the coercive quadratic, and `weylPotPoly Φ = ∑_j Φ_j² + 1` does not contain it.
An obstruction is only worth the size of its converse, so §7 of `ChapterSmGradTable` puts the
quadratic back and proves the bound.

`weylCoercive Φ M := weylPotPoly Φ + ∑_{m∈M} X_m²` **is** `wsSum Φ M 1`
(`weylCoercive_eq_wsSum`), so nothing is recomputed: §49's `pointwise_dom_of_sq_sum` applies verbatim
and gives, for any family of forms admitting a `GradBound C` (`gradDom_weylCoercive`),

  `∑_{j∈M} |∂_j W|² ≤ (16|M||ι|C + 8) W² + (8|M||ι|C + 8)`.

At the single bilinear form `X₀X₁` the potential is `(X₀X₁)² + 1 + X₀² + X₁²`, the `GradBound` is
`gradBound_weylFlat` (`C = 1`), and the constants come out as `a = 40`, `b = 24`
(`gradDom_weylCoercive_flat`) — the same pair §49's `gradDom_flat_plus_quadratic` computes for the
same potential.

So §54's obstruction is sharp in the right sense: what the QYM/NS forms lack is not a proof technique
but a term.  Adding it is a modelling decision (mass, confinement, anisotropic weight); this section
does not choose it and does not compute a sharp constant — the constants above are whatever the
generic estimate produces from the coefficient sum.

### 55.2. The SM quartet: what was attempted, and why it is not delivered

The request was to build the SM's own quartet data so that `PhysicalPositivity` stops being a named
input.  It is **not** delivered, and the attempt is recorded because the reason is structural.

`physicalPositivity_of_homotopy` needs a b-ghost `P` with `Q P Q = Q`, `P Q P = P` for
`smBrstCharge = brstCharge (smStruct f3) ghostCre ghostAnn matterGen`.  The natural first step is the
abelian (`f3 = 0`) sector, where the charge is `c† ⊗ T` on two ghost slots over the matter space and a
generalized inverse `S` of `T` gives the candidate b-ghost `b ⊗ S`.  That construction was written
and then **withdrawn**, for two reasons found while doing it:

* this Mathlib has **no product inner-product space** (`InnerProductSpace ℂ (K × K)` does not
  synthesize), so the two-slot model cannot be fed to the corpus's `IsBrst`/`BrstQuartet` machinery
  without an index-restricted `EuclideanSpace` reformulation; and
* more importantly, the ghost-pairing metric `(u, v) ↦ (v, u)` does **not** satisfy the hypothesis
  `η (V y) = V y` that the no-ghost theorem needs.  The identity it does satisfy is
  `η (V x) = V (η x)`, i.e. the metric commutes with the projector rather than fixing its range —
  exactly the difference between "the physical subspace is invariant" and "the physical subspace is
  definite".  Supplying the right Krein metric is a separate construction, not a line of bookkeeping.

So `PhysicalPositivity` for the SM charge remains a named input.  What the attempt clarifies is the
*size* of what is missing: a contracting homotopy for the non-abelian complex, plus a Krein metric
that fixes the physical subspace — two objects, both named, neither of them algebraic routine.  No
module was added for this, and no claim was upgraded on the strength of the attempt.

### 55.3. Verification performed (2026-11-13)

* `lake env lean BookProof/Sm/ChapterSmGradTable.lean` — clean, no warnings (the §7 block fixed the
  line-length lints introduced by the §6 and §54 prose in the same session).
* `lake build BookProof.Sm.ChapterSmGradTable` — `Build completed successfully`.
* `lake env lean Work/SmGradTableAudit.lean` — 35 declarations, every one on exactly
  `propext, Classical.choice, Quot.sound`; no `sorryAx`.
* `lake env lean BookProof.lean` — clean (root-module check).
* `scripts/check-sm-section-guards` — green with the §55 needles.
* `lake build BookProof` to completion: **succeeded** (`8982 jobs`, 28m56s, exit 0) — see §55.4.

### 55.4. The full build, completed (2026-11-13)

The earlier rounds reported `lake build BookProof` as not run to completion, with the root-module
`lake env lean BookProof.lean` check as the substitute.  With a real budget it **completes**, on the
tree this section describes:

```
$ time lake build BookProof
Build completed successfully (8982 jobs).

real    28m55.505s
user    28m55.586s
sys     0m7.105s
EXIT=0
```

An earlier run finished `8981 jobs` in 30m16s on the tree *before* the §7 block existed; that run is
why the count differs by one, and it is not the run being relied on.  The reported one is the second,
started after every edit in this section and §7 was in place.  Warnings in the log are pre-existing
linter advisories on modules this session did not touch (`setOption`, `longLine`, flexible-`simp`
notes); there are no errors and no `sorry` warnings.

So the substitute check was sound, but "the root module elaborates" and "the whole book builds" are
different statements, and the weaker one was labelled as the weaker one until it could be replaced.

---

## §56. Gradient domination for the NS potential itself (2026-11-13)

### 56.1. The question, and a correction

> **Correction (§58, 2026-11-13):** the input this section reduces to, `VolDom`, is *false* for the
> model's own `volPot` — the unimodular shears refute it with the ratio `4/ε² → ∞`.  `lagGradDom_of_volDom`
> is therefore a reduction to an unsatisfiable hypothesis, and the §49 chain does not reach the NS
> energy.  The two coercive blocks proved below are not affected.

§54 (ix) answered the cross-model question for Navier–Stokes with "the NS modules are
operator-level (`BookProof/Ns/*`), so the NS half is the proof template rather than a proved
counterexample".  That sentence was wrong, and this section corrects it: the Lagrangian NS model
already carries a potential of exactly the contested shape, and the question can be *answered* for
it rather than templated.  The request was to "prove the coercive domination for the NS model's own
potential shape"; what follows separates the part that is free in the model from the one input that
is not, and proves that the input cannot be dropped.

### 56.2. What the model already carries

`BookProof/Ns/ChapterNsLagrangianDetFarisLavine` defines

```
lagEnergy S = 1 + ½ ∑_j v_j² + V_κ(ξ),      lagLyap S = lagEnergy S + ½ ∑_j ξ_j²,
```

with `V_κ = volPot S.kappa S.kvec` the degree-six incompressibility penalty
(`volPot_eval_nonneg`; its zero set is incompressible by `det_eq_one_of_volPot_eq_zero`).  New
module `BookProof/Ns/ChapterNsGradDomCoercive.lean` (namespace `BookProof.NsGradDomCoercive`):

* `pderiv_vel_lagEnergy` — `∂_{v_j} E = v_j`; `pderiv_disp_lagLyap` — `∂_{ξ_j} W = ∂_{ξ_j} V_κ + ξ_j`.
* `vel_grad_sum`, `lagEnergy_vel_gradDom` — the velocity block is *exactly* the kinetic energy,
  `∑_j (∂_{v_j}E)² = ∑_j v_j² ≤ 2E`, i.e. a domination with `a = 2` and **no constant term**.
* `disp_grad_sum` — the Lyapunov displacement quadratic contributes `2 · ½∑ ξ²` exactly.
* `lagGradDom_of_volDom` — if the penalty obeys `VolDom A B`
  (`∑_j (∂_{ξ_j}V_κ)² ≤ A V_κ² + B`) then the whole of `lagLyap` obeys the pointwise domination
  with `a = 2A + 3`, `b = 2B + 3`; `volDom_phase` is the same statement in phase-space coordinates.

The difference from QYM is the point: §55 had to *add* `∑_m X_m²` to `weylPotPoly` before §49's
mechanism applied, while here the quadratic is part of the model.  So for NS the coercive input is
already there and the open question is only the penalty's own estimate, named `VolDom`.

### 56.3. The input cannot be dropped

`not_gradDom_flatSextic` shows `VolDom` is not a consequence of `V_κ ≥ 0` and `deg V_κ = 6`: the
flat sextic `(xyz)²` is non-negative of degree six (`ev3_flatSextic_nonneg`) and along
`(t, 1/t, 1)` its potential is the constant `1` while `∑_j (∂_j)² = 4t² + 4/t² + 4`
(`ev3_pderiv_zero`/`_one`/`_two`), so no `a, b` dominate it — the same curve as §48's flat quartic.
Sixth-order flatness is no better than fourth-order flatness, and `lagGradDom_of_volDom` is a
reduction, not a discharge.

What this does **not** say: nothing about `V_κ`'s actual `A`, `B` (the penalty is not flat, and its
conic structure `conjP_volPot` is where those constants would come from), and nothing about ESA of
the Lagrangian generator `N_L`, which remains the explicit hypothesis of
`lagKoopman_esa_of_comparison_esa` (`lagCan_esa` is unconditional, `N_L`'s ESA is not).

### 56.4. Verification (2026-11-13)

* `lake build BookProof.Ns.ChapterNsGradDomCoercive` — `Build completed successfully`, and no
  warnings attributed to the module (the >100-character lints of the first draft were fixed).
* `lake env lean Work/AuditNs.lean` — 10 declarations (`evP_X_re`, `pderiv_vel_lagEnergy`,
  `pderiv_disp_lagLyap`, `vel_grad_sum`, `lagEnergy_vel_gradDom`, `disp_grad_sum`, `volDom_phase`,
  `lagGradDom_of_volDom`, `not_gradDom_flatSextic`, `ev3_flatSextic_nonneg`), every one on exactly
  `propext, Classical.choice, Quot.sound`; no `sorryAx`.
* `scripts/check-sm-section-guards` — green with the §56 needles; the §56 co-occurrence pair
  (`lagGradDom_of_volDom` → `not_gradDom_flatSextic`) is exercised negatively by `SM_PAIR_WINDOW=5`.
* `lake build BookProof` to completion on the post-edit tree: **succeeded** (`8984 jobs`, 29m57s,
  exit 0; §55.4's run of the same target reported `8982` jobs, the difference being the module added
  here).  The log carries no errors and no `sorry`; its remaining messages are the pre-existing
  linter advisories on modules this change did not touch.

---

## §57. The b-ghost on an index-restricted Euclidean space (2026-11-13)

### 57.1. The withdrawal this answers

§47 (x) withdrew the attempt to build the SM's b-ghost for two reasons: this Mathlib has no product
inner-product space, so a two-slot `K × K` ghost model cannot be handed to `IsBrst`/`BrstQuartet`;
and the ghost-pairing metric satisfied `η (V x) = V (η x)` but not `η (V y) = V y`.  The first is a
bookkeeping obstacle and it is now removed; the second is a real obstruction only for the *pairing*
metric, not for the index-swap metric.  §6 of `ChapterSmQuartet` had already exhibited the whole
mechanism on a hand-written three-dimensional block; what was missing was a construction that does
not depend on the size of the sector.  That is what this section adds.

### 57.2. The construction

New module `BookProof/Sm/ChapterSmIndexGhostQuartet.lean` (namespace
`BookProof.SmIndexGhostQuartet`).  The index set is

```
Idx n m = (Fin n × Bool) ⊕ Fin m,
```

with `(a, false)` the ghost of pair `a`, `(a, true)` its antighost, and `inr j` a physical mode, and
the space is `Space n m = EuclideanSpace ℂ (Idx n m)`.  Three maps, *by index*, for every `n, m`:

* `Q` sends `(a, false) ↦ (a, true)` and kills everything else;
* `P` sends `(a, true) ↦ (a, false)` and kills everything else;
* `Eta` swaps `(a, false) ↔ (a, true)` and fixes the physical modes.

The six inputs of `physicalPositivity_of_homotopy` are all discharged:

* `Q_nil : IsBrst (Q n m)`; `QPQ`, `PQP` — the two contraction identities, one `ext_coords`
  argument each;
* `krein` — `⟨η (Q x), y⟩ = ⟨η x, Q y⟩`, by expanding the inner product over the index set;
* `symm` — the charge form is symmetric.  This one is *derived*, not computed: `Eta_inner` says the
  metric is an isometry (it permutes coordinates) and `Eta_involutive` says `η² = 1`, which turn
  `⟨x, η y⟩` into `⟨η x, y⟩ = conj ⟨y, η x⟩`;
* `eta_physProj` — `η (V y) = V y` for the *computed* projector `V = physProjOf Q P`.  This is the
  point the §47 withdrawal failed on, and the index restriction is why it works: `physProj_ghost`
  and `physProj_anti` show `V` lands on the physical coordinates, where `η` is the identity.

Hence `physicalPositivity (n m) : PhysicalPositivity (Q n m) (Eta n m)` with **no hypotheses**, and
`physVec_not_exact` shows the model's cohomology is non-trivial: a physical mode is closed and not a
gauge orbit, so this is not positivity on a space where everything is exact.  Nothing is chosen per
pair; `n = 12` — the SM ghost count — is an instance, not a case.

### 57.3. What this does not do

It is **not** `smBrstCharge`.  That charge lives on the fermionic Fock space `FermiFock (m + 12)` and
is known here only as a `Module.End`; to instantiate this model on it one still needs an
inner-product structure on the Fock space, the charge as a linear map, and the identification of its
twelve ghost modes with the index pattern above.  So `PhysicalPositivity` for `smBrstCharge` remains
a named input — but the input has moved: it is no longer *quartet data* (a b-ghost and a metric,
which is what §47 and §50 recorded as missing) but an *identification*, since the quartet data now
exists at every size and the metric is proved to fix the projector's range.  Nothing in the SM claim
is upgraded until that identification is written down.

### 57.4. Verification (2026-11-13)

* `lake build BookProof.Sm.ChapterSmIndexGhostQuartet` — `Build completed successfully`, no warnings
  on the module.
* `lake env lean Work/SmIndexGhostAudit.lean` — 11 declarations (`Q_nil`, `QPQ`, `PQP`,
  `physProj_phys`, `eta_physProj`, `Eta_involutive`, `Eta_inner`, `krein`, `symm`,
  `physicalPositivity`, `physVec_not_exact`), every one on exactly
  `propext, Classical.choice, Quot.sound`; no `sorryAx`.
* `scripts/check-sm-section-guards` — green with the §57 needles, and the §57 pair
  (`eta_physProj` → `physVec_not_exact`, construction then non-vacuity) is exercised negatively by
  `SM_PAIR_WINDOW=4`.
* `lake env lean BookProof.lean` then `lake build BookProof` — `Build completed successfully`,
  `8988 jobs`, exit 0, in 8.9s because every dependency was already built on this tree; §56.4's
  29m57s run of the same target was the full recompile, so this is a reachability check of the new
  import rather than a second full build.

---

## §58. `VolDom` is false for the actual volume penalty (2026-11-13)

### 58.1. What §56 left open, and what the answer turned out to be

§56 reduced gradient domination for the NS Lagrangian energy to a single pointwise estimate on the
incompressibility penalty `V_κ` and proved that non-negativity plus degree six cannot give it
(`not_gradDom_flatSextic`).  The request was to evaluate `VolDom A B` for the model's own `volPot`
and report numeric constants.  The measurement below reports a different answer: **no finite `A` and
`B` exist**.  `VolDom A B` is not merely unproved for `volPot` — it is false, so
`lagGradDom_of_volDom` can never be applied and the §49-style route does not reach the NS energy at
all.  §56.3's phrase "the one input" should be read as "the one input, and it is unprovable".

### 58.2. The family that refutes it

Let `F = I + ∇ξ`, and take `N = e_x ⊗ e_y`, the shear generator: `N² = 0`, so `det(I + tN) = 1` for
every amplitude `t`.  Perturb transversally by `ε B` with `B = e_y ⊗ e_x` (so `tr B = 0` while
`tr(NB) = 1`).  Then `(I + tN)⁻¹ = I − tN` and

```
det F − 1 = ε · tr((I − tN) B) + O(ε²) = −ε t + O(ε²),
```

so `V_κ = (κ/2) ε² t² + O(ε³)`.  The two partial derivatives are `∂_t V_κ ≈ κ ε² t` and
`∂_ε V_κ ≈ κ ε t²`, hence

```
|∇V_κ|² / V_κ²  →  (κ² ε² t⁴)/((κ/2)² ε⁴ t⁴)  =  4/ε².
```

The ratio does not grow with the amplitude `t` — it *saturates* at `4/ε²` — and `ε → 0` makes it
unbounded.  No `A`, `B` can dominate a quantity whose supremum is infinite, so `VolDom A B` fails for
every pair.

The obstruction is the shear family, not the degree: `V_κ` is flat along the unimodular directions
(`det F = 1` exactly there) while its gradient still grows like `t` in the transverse direction.  It
is the same failure mode as the QYM `weylPotPoly` of §54 and the flat sextic of §56.3, with the
flatness coming from incompressibility rather than from monomial structure.

### 58.3. The measurement (`scripts/eval-vol-dom.py`)

The script evaluates `volPot` exactly on the truncation `|K| = 2`, `k(k₀) = e_x`, `k(k₁) = e_y`,
`κ = 1` — 12 real coordinates, 25 momenta — reconstructing `detCoef` as the triple convolution of
`ChapterNsLagrangianDetConvolution` and differentiating with forward-mode dual numbers, so both `V_κ`
and `∇V_κ` are exact for that truncation (no finite differences).  Reported quantity:
`|∇V_κ|²/(V_κ² + 1)`, whose supremum is the quantity any `A = B` must dominate.

| `t` | `ε` | `V_κ` | `|∇V_κ|²` | ratio | `4/ε²` |
|---|---|---|---|---|---|
| 1e2 | 1e-2 | 2 | 1.6e5 | 32000 | 4e4 |
| 1e4 | 1e-2 | 2e4 | 1.6e13 | 40000 | 4e4 |
| 1e5 | 1e-2 | 2e6 | 1.6e17 | 40000 | 4e4 |
| 1e2 | 1e-3 | 0.02 | 1600 | 1599.36 | 4e6 |
| 1e4 | 1e-3 | 200 | 1.6e11 | 3.9999e6 | 4e6 |
| 1e5 | 1e-3 | 2e4 | 1.6e15 | 4e6 | 4e6 |
| 1e2 | 1e-4 | 2e-4 | 16 | 16 | 4e8 |
| 1e4 | 1e-4 | 2 | 1.6e9 | 3.2e8 | 4e8 |
| 1e5 | 1e-4 | 200 | 1.6e13 | 4e8 | 4e8 |

Three rows of `t` per `ε` show the saturation at `4/ε²` predicted in §58.2, and the last column is
that prediction; the saturated ratios agree to every printed digit.  The prefactor of `V_κ` itself is
larger than the two-term expansion of §58.2 by `4` — the shear and its tilt each split over a mode
and its conjugate — which cancels in the ratio and leaves the `4/ε²` law intact.  Unrestricted random sampling (`400` points,
scales `1e-1.5`–`1e1`), large-amplitude sampling (`400` points, scales `1e1`–`1e2.5`) and noisy
shear samples give `7.05`, `0.79` and `334` respectively — the sampled supremum over a *bounded* box
is finite and small, which is exactly why the failure needs the two-parameter family rather than
random sampling to be visible.

This is a measurement, not a proof: it is the exact value for a truncation of the model, and it
matches the analytic expansion §58.2 term by term.  A Lean refutation of `VolDom` at the model's own
constants would require evaluating `detCoef` on an explicit two-mode model; the analytic expansion
above is the statement a proof would formalize.

### 58.4. What this changes

* `lagGradDom_of_volDom` stands as a reduction, but its hypothesis is *unsatisfiable*: the NS
  Lyapunov energy is **not** gradient-dominated, and the §49 chain (`GradBound` →
  `pointwise_dom_of_sq_sum` → `PotSelfBound`) cannot be run on `lagEnergy`/`lagLyap`.
* The two blocks that *are* dominated remain true and independent (`lagEnergy_vel_gradDom`,
  `disp_grad_sum`): the velocity and displacement quadratics are coercive in the model.
* A repairable route, recorded and not attempted: dominate with a weight that vanishes on the
  shear family — i.e. replace `V_κ²` by `V_κ² + (deviation from unimodularity)⁴` or restrict the
  estimate to configurations with a positive lower bound on `|det F − 1| + |∇ det F|`.  Either
  changes the potential, so it is a different model, not a proof of this one.

---

## §59. The parity sectors of the index-restricted ghost complex (2026-11-13)

### 59.1. The question

§57 proves `PhysicalPositivity` for the index-restricted complex with `eta_physProj` as its last
input.  The sector refinement of the no-ghost theorem replaces that single hypothesis by two
estimates, one per parity sector, and the request was to add the parity-even version so that
`physicalPositivity_of_homotopy_sectors` applies.  It turns out there are two sector statements, and
exactly one of them can hold.

### 59.2. The global hypotheses are inconsistent — in any space

`physicalPositivity_of_homotopy_sectors` and `physicalPositivity_of_quartet_sectors` ask for
non-negativity **and definiteness** of the charge form on the whole of each parity sector.  For a
unitary involution `U` preserving `η`, a vector splits into orthogonal even and odd parts
(`kform_quadForm_split`), so those four hypotheses make the charge form positive definite on the whole
space; a nilpotent charge that is self-adjoint for a definite form is zero.  This is
`global_sectors_force_zero`, proved in the general inner-product setting, and it makes the request as
literally stated impossible: any nonzero nilpotent BRST charge refutes its own sector hypotheses.  The
index model is the witness (`parity_globals_fail`, `Q_ne_zero`), and so is every non-abelian gauge
theory.

### 59.3. The closed-space hypotheses hold, for the ghost parity

With `Par` = `−1` on every ghost and antighost coordinate and `+1` on the physical ones
(`ChapterSmIndexGhostSectors`), the parity is an involutive isometry commuting with `η`, `Q` and `P`
(`Par_involutive`, `Par_norm`, `Eta_comm_Par`, `Q_comm_Par`, `P_comm_Par`).  Coordinatewise:

* an even vector has neither ghost nor antighost coordinates (`ghost_eq_zero_of_mem_even`,
  `anti_eq_zero_of_mem_even`), so `η` fixes it (`Eta_eq_of_mem_even`) and the charge form is `‖v‖²`
  (`kform_even_nonneg`);
* an odd *closed* vector is a pure antighost (`phys_eq_zero_of_mem_odd` plus closure), whose `η`-image
  is a pure ghost, so the form vanishes (`kform_odd_closed`).

Hence the sector hypotheses hold on `ker Q`, which is the shape `kform_quadForm_nonneg` consumes, and
`kform_nonneg_closed` assembles them into non-negativity on the whole closed space —
`sector_hypotheses_closed` states them in that form.  The lesson matches §47: the sector hypotheses
have to be read on the closed space, not on the ambient space.

### 59.4. What is *not* claimed

The radical half of `PhysicalPositivity` still uses `eta_physProj` (as in
`ChapterSmIndexGhostQuartet.physicalPositivity`): an odd antighost has vanishing charge form, so
definiteness cannot remove it — only the quartet decomposition can, and that is what the sibling
module does.  So the sector route supplies the non-negativity, and the radical remains where §57 left
it.

### 59.5. Verification

* `lake build BookProof.Sm.ChapterSmIndexGhostSectors` — succeeded (10s), no warning attributed to the
  module.
* `lake env lean Work/SmIndexGhostSectorAudit.lean` — 11 declarations, every one on exactly
  `propext, Classical.choice, Quot.sound`; no `sorryAx`.
* `scripts/check-sm-section-guards` — green with the §59 needles; the pair
  (`global_sectors_force_zero` → `parity_globals_fail`) is exercised negatively by
  `SM_PAIR_WINDOW` set below its span.

---

## §60. The Fock side of the ghost sector (2026-11-13)

### 60.1. A correction to item (xii)

`HONEST_BOUNDARIES_SM` (xii) said that to instantiate the index-restricted quartet on
`smBrstCharge` one still needs "an inner product on that Fock space".  Read literally that is wrong.
The fermionic Fock space of this corpus is `FermiFock n = ℓ²(Finset (Fin n)) = EuclideanSpace ℂ
(Finset (Fin n))`, which *is* an inner-product space: its occupation basis is orthonormal
(`occ_inner`, restated here from `ChapterSmCarAlgebra`) and the CAR creation operators are adjoints
for it (`inner_creat_left`).  No product structure was ever missing.

### 60.2. The identification that is true

`ChapterSmIndexGhostFock` proves the part of the identification that holds:

* the twelve ghost modes are `ghostMode m a`, the last twelve coordinates of `Fin (m + 12)`, and
  `ghostMode_injective` makes that an injection of mode labels;
* their occupation vectors `ghostVec m a = occ {ghostMode m a}` are orthonormal
  (`ghostVec_orthonormal`), so the one-particle ghost sector is an isometric copy of
  `EuclideanSpace ℂ (Fin 12)` — one coordinate per ghost pair, which is the index pattern;
* that copy is exactly the orbit of the vacuum under `ghostCre` (`ghostCre_vac`);
* the pairing that the index model's metric `η` implements is realized on the Fock side by the
  adjunction `b_a = (c^a)†` (`ghost_pairing`, from `inner_creat_left`).

### 60.3. The identification that is false

`smBrstCharge` is **not** the index complex at `n = 12`.  It is `∑ a, χ_a G^a − ½ ∑ f χ β`, a
degree-one derivation whose linear part pairs a ghost with a *matter* bilinear and whose quadratic
part creates a second ghost, so it does not preserve the one-particle ghost sector: a single ghost is
not mapped to a single antighost.  The index-restricted quartet is therefore the free (one-particle)
part of the ghost complex — an isometric slice of the Fock space, not a subcomplex of
`smBrstCharge`.  What remains open is the b-ghost of the derivation, and that is what (xii) should
have named.

### 60.4. Verification

* `lake build BookProof.Sm.ChapterSmIndexGhostFock` — succeeded (4.5s), no warning attributed to the
  module.
* `lake env lean Work/SmIndexGhostFockAudit.lean` — 5 declarations, all on exactly
  `propext, Classical.choice, Quot.sound`.

---

## §61. `VolDom` in normal form, and whether a deformation norm repairs it (2026-11-13)

### 61.1. The law of §58 is an identity, not an asymptotics

§58 measured `|∇V_κ|²/V_κ² → 4/ε²` along the shear family `F = I + t N + ε B` and used the second-order
expansion `det F − 1 = −ε t + O(ε²)` to explain it. The leading term of the penalty across that family
is the two-parameter polynomial `(ε t)²/2`, and for *that* polynomial the ratio is exact:

    ∑_j (∂_j V)²  =  V² · (4/t² + 4/ε²).

New module `BookProof/Ns/ChapterNsVolDomShear.lean` (namespace `BookProof.NsVolDomShear`) proves it:
`shearPot = ½ (X₀X₁)²` with `x 0 = t`, `x 1 = ε`; `ev2_shearPot_flat` is the flatness at *every*
amplitude (zero tilt gives zero potential, not just zero derivative); `ev2_pderiv_zero`/
`ev2_pderiv_one` compute `∂_t V = ε²t`, `∂_ε V = εt²`; `shear_grad_sq` is the identity above. Both
terms are visible: `4/ε²` is what the sweep saturates at, and `4/t²` is the correction that shows up at
moderate `t` — at `t = 1e2, ε = 1e-3` the law gives `4e6 + 4e-4`, and the measurement printed `1599.36`
because at that `t` the truncated penalty has not yet reached the asymptotic regime.

Then `not_volDom_shear`:

    ¬ ∃ A B, ∀ x : Fin 2 → ℝ, ∑(∂V)² ≤ A V² + B.

The proof is one family: at `x = (1/d, d)` the product `εt` is the constant `1`, so `V ≡ 1/2` while
`∑(∂V)² = d² + d⁻²` blows up as `d → 0`. Choosing `d = 1/(|A| + |B| + 4)` makes the right-hand side
`A/4 + B ≤ 1/d` and the left-hand side at least `(1/d)² > 1/d`.

**Scope.** This refutes the estimate for the *normal form* of the penalty across the shear family. It
does not refute it for the model's literal `volPot`, whose passage to the normal form is the
second-order expansion of §58.1 plus the measurement; that bridge is not formalized, and the module
says so in this many words. What the module does establish is that the mechanism of §58 is not an
artifact of the truncation: a potential that is quadratic in `ε t` fails this estimate at *any* degree
and *any* truncation, so no change of truncation can rescue `VolDom`.

### 61.2. A deformation norm does repair it — measured

The failure is that `V_κ` is flat on the unimodular set while its gradient is not, so any fix has to
add a term that does *not* vanish there. Weighting the penalty by a function of `det F` cannot work
(any weight vanishing at `det F = 1` leaves the shear flat); what can work is a term in the
deformation itself. The evaluator now measures

    V_μ = V_κ + (μ/2) · ∑_{k,j} (1 + |k|²) |ξ̂_{k,j}|²,

the `H¹`-type deformation norm written in Fourier space, with exact dual-number gradients as before.

Sampled supremum of `|∇V_μ|²/(V_μ² + 1)` over four boxes (the refuting shear family incl. `ε` down to
`1e-4`, 200 random points, the noisy shear family, 200 large-`|ξ|` points):

| `μ` | shear family | random | shear + noise | large `|ξ|` |
|---|---|---|---|---|
| 0 | `4e6` | 7.04 | 334 | 0.154 |
| 1e-3 | 1111 | 7.04 | 302 | 0.154 |
| 1e-2 | 15.4 | 6.95 | 142 | 0.154 |
| 0.1 | 0.160 | 6.16 | 19.8 | 0.153 |
| 1 | 0.00200 | 3.92 | 2.23 | 0.141 |
| 10 | 0.000416 | 20.6 | 16.6 | 0.090 |

The discriminating column is the shear family, and the diagnostic sharpens it — shrink the tilt at
fixed shear amplitude `t = 1e4`:

| `ε` | `μ = 0` | `μ = 0.01` | `μ = 0.1` | `μ = 1` |
|---|---|---|---|---|
| 1e-2 | `4.00e4` | 15.4 | 0.159 | 0.00160 |
| 1e-3 | `4.00e6` | 0.160 | 0.00160 | `1.60e-5` |
| 1e-4 | `3.20e8` | 0.00160 | `1.60e-5` | `2.00e-7` |
| 1e-5 | (cancellation) | `1.60e-5` | `2.00e-7` | `4.16e-8` |
| 1e-6 | (cancellation) | `2.00e-7` | `4.16e-8` | `4.00e-8` |

Read column by column: at `μ = 0` the ratio grows like `4/ε²`; at every `μ > 0` it *decreases* as the
tilt shrinks, which is the opposite of a divergence. So a finite `A` exists for each `μ > 0`, and on
these boxes `A ≈ 21` suffices at `μ = 0.01`, `A ≈ 8` at `μ = 0.1`. This is a measurement on a
truncation, not a proof, and the repair is a *different model* — the penalty is no longer the pure
volume penalty, so `lagGradDom_of_volDom`'s chain would have to be re-run for the modified Lagrangian.

**A caveat the table itself forced.** From `ε ≤ 1e-4` on, the `μ = 0` column is *not* data: `V` is so
small that the dual-number gradient loses its digits to cancellation and the printed numbers fall back
down. The script now prints that warning next to the table, and the exact law for `μ = 0` is
`shear_grad_sq`, not the float.

### 61.3. Verification (2026-11-13)

* `lake build BookProof.Ns.ChapterNsVolDomShear` — `Build completed successfully`; no warning attributed
  to the module.
* `lake env lean Work/NsVolDomShearAudit.lean` — 7 declarations (`ev2_shearPot`,
  `ev2_shearPot_flat`, `ev2_shearPot_nonneg`, `ev2_pderiv_zero`, `ev2_pderiv_one`, `shear_grad_sq`,
  `not_volDom_shear`), each on exactly `propext, Classical.choice, Quot.sound`; no `sorryAx`.
* `python3 scripts/eval-vol-dom.py` — the two new tables above, ~1m20s.
* `scripts/check-sm-section-guards` — §61 pair (`shear_grad_sq` → `not_volDom_shear`) guarded.

## §62. The b-ghost of the derivation, and where it contracts to (2026-11-13)

### 62.1. What was open

§60 ended with: "`smBrstCharge` is a degree-one derivation, so it does not preserve the one-particle
ghost sector … the open object is the b-ghost of the derivation." This section names that object and
proves its defining identity.

### 62.2. The construction

New module `BookProof/Sm/ChapterSmIndexGhostDerivation.lean` (namespace
`BookProof.SmIndexGhostDerivation`). Three maps on `FermiFock (m + 12)`:

* `matterHalf = ∑_a χ_a G^a`, the matter half of the charge (`χ_a = ghostCre m a`,
  `G^a = matterGen m T a`);
* `bGhost = ∑_b β_b`, the **antighost sum** — the b-ghost of the derivation;
* `gaussSum = ∑_a G^a`, the Gauss-law generator.

Then `bGhost_anticomm`:

    { ∑_a χ_a G^a , ∑_b β_b }  =  ∑_a G^a ,

proved per pair (`pair_anticomm`: `χ_a G^a β_b + β_b χ_a G^a = δ_{ab} G^a`, using
`matterGen_comm_ghostAnn` and the CAR `{β_b, χ_a} = δ_{ba}`) and summed with
`Finset.sum_ite_eq`. Two corollaries follow, and they are the answer to §60:

* `bGhost_no_contraction` — if `{matterHalf, bGhost} = 1` then `gaussSum = 1`. Since the sum of the
  Gauss generators is not the identity, the antighost is *not* a contracting homotopy for the
  derivation. It contracts onto **matter**. That is the precise sense in which the ghost sector of
  `smBrstCharge` is not the index complex: the contraction has nowhere else to land.
* `bGhost_anticomm_abelian` — when `gaussSum = 0` the anticommutator vanishes, so §57's index quartet
  is exactly the `∑ G^a = 0` fibre of the derivation. The quartet is therefore a *comparison model*
  for the SM charge, which is what §57.3 said and this now proves.

### 62.3. What is not covered

The structure-constant half `−½ ∑_{a,b,c} f_{abc} χ_a χ_b β_c` was left open when this section was
first written. **§65 computes it** (2026-11-13b): its anticommutator with `bGhost` is a
ghost–antighost bilinear carrying `f`, and the coefficient is the *first-slot trace* `Σ_y f_{yxe}`,
which antisymmetry does **not** kill — so the remainder is real, it now has an exact form,
`{Ω, b} = Σ_a G^a − Σ_{x,e} (Σ_y f_{yxe}) χ_x β_e`, and the free ghost complex is not a subcomplex of
the interacting one. The cohomological meaning of that remainder is still open, and
`PhysicalPositivity` for `smBrstCharge` remains a named input. What has changed is its shape: it is no
longer "find a b-ghost" (§57 supplied quartet data at every size, §62 supplies the derivation's own
antighost) but "show the Gauss sector is what the contraction lands in", which is a statement about
the matter representation, not about ghost bookkeeping.

### 62.4. Verification (2026-11-13)

* `lake build BookProof.Sm.ChapterSmIndexGhostDerivation` — `Build completed successfully`; no warning
  attributed to the module.
* `lake env lean Work/SmIndexGhostDerivationAudit.lean` — 4 declarations (`pair_anticomm`,
  `bGhost_anticomm`, `bGhost_no_contraction`, `bGhost_anticomm_abelian`), all on exactly
  `propext, Classical.choice, Quot.sound`; no `sorryAx`.
* `lake build BookProof` — `Build completed successfully`, **8998 jobs**, 1m54s, exit 0, with all four
  new modules imported (the run also re-elaborated the modules the concurrent work order added, which
  is why the job count moved from 8988).
* `scripts/check-sm-section-guards` — §62 pair (`bGhost_anticomm` → `gaussSum = 1` consequence)
  guarded.

## §63. The expansion behind the shear normal form (2026-11-13b)

### 63.1. What §61 left open

§61 proved the law `∑(∂V)² = V²(4/t² + 4/ε²)` for the *normal form* `V = (εt)²/2` and refuted domination
for it, and said in as many words that the bridge from the model's literal `volPot` to that normal form
was not formalized. This section formalizes the algebraic half of the bridge and isolates exactly what is
left. New module `BookProof/Ns/ChapterNsVolDomExpansion.lean` (namespace
`BookProof.NsVolDomExpansion`).

### 63.2. The determinant identity

Write the shear and tilt of §58 as indicator matrices, `shM i j = δ_{i0}δ_{j1}` and
`tlM i j = δ_{i1}δ_{j0}`, so that neither is a matrix literal:

* `shM_mul_self : shM * shM = 0`, hence `det_one_add_shM : det(I + t·shM) = 1` **at every amplitude**
  (not merely to first order). This is the algebraic content of §58's "the shears are flat".
* `tlM_mul_self : tlM * tlM = 0`, so the tilt contributes no pure `ε²` term.
* `det_one_add_smul : det(I + t·shM + ε·tlM) = 1 − ε t`, exactly — the expansion §58.1 expanded to has
  **no** `t²`, `ε²` or `O(ε²)` term, only the mixed one.

The residual `volResid t ε = det(I + t·shM + ε·tlM) − 1` therefore satisfies
`volResid t 0 = 0` (`volResid_zero_tilt`), `volResid 0 ε = 0` (`volResid_zero_shear`) and
`volResid t ε = −(εt)` identically (`volResid_eq`).

### 63.3. Transfer to every amplitude constant

The penalty across the family is a *positive multiple* of `(εt)²`: the multiplier is the profile's
amplitude together with `κ/2`. The module therefore works with `normForm c = c·((X₀X₁)²)` and proves the
law for every `c` (`normForm_grad_sq`, with `ev2_normForm`, `pderiv_normForm_zero/one` giving
`∂₀ = 2c(εt)t`, `∂₁ = 2c(εt)ε`), so nothing in §61 depended on the profile constant. Then
`shearPot_eq_normForm : shearPot = normForm (1/2)` identifies §61's potential as the `c = 1/2` member, and
`not_volDom_normForm c (hc : c ≠ 0)` refutes domination for **every** nonzero multiple: on the family
`x = (K, 1/K)` the value is `c` while the gradient grows like `K`, with `K` absorbing `|A|`, `|B|` and
`1/(4c²)`. `volDom_fails_of_normal_form` restates it as a hypothesis on an arbitrary potential whose value
is `c(εt)²`.

### 63.4. Scope

What is *not* formalized is the passage from the model's `volPot` to a value of the form `c(εt)²` on the
family, i.e. the Fourier reconstruction of `det F − 1` (Parseval with the convolution `detCoef`); that is
where the profile constant is produced, and §58's measurement is its numerical evidence. So the chain now
reads: model penalty → (measured, not formalized) normal form → (proved here) law and non-domination at
every amplitude. The non-domination therefore holds for any truncation of the penalty that reproduces the
`(εt)²` normal form, which is §61's claim made precise.

### 63.5. Verification (2026-11-13b)

* `lake build BookProof.Ns.ChapterNsVolDomExpansion` — `Build completed successfully`; no warning
  attributed to the module.
* `lake env lean Work/NsVolDomExpansionAudit.lean` — 12 declarations (`shM_mul_self`, `tlM_mul_self`,
  `det_one_add_shM`, `det_one_add_smul`, `volResid_eq`, `ev2_normForm`, `pderiv_normForm_zero`,
  `pderiv_normForm_one`, `normForm_grad_sq`, `shearPot_eq_normForm`, `not_volDom_normForm`,
  `volDom_fails_of_normal_form`), all on exactly `propext, Classical.choice, Quot.sound`; no `sorryAx`.

## §64. Gradient domination for the deformation-norm repair (2026-11-13b)

### 64.1. The repair §61.2 measured

§61.2 measured that adding `(μ/2)∑(1 + |k|²)|ξ̂|²` makes the ratio `|∇V_μ|²/(V_μ² + 1)` bounded for
`μ > 0` and *decreasing* as the tilt shrinks. This section proves that closure for the two-parameter
model of the family, with explicit constants, and states what it changes. New module
`BookProof/Ns/ChapterNsVolDomMuRepair.lean` (namespace `BookProof.NsVolDomMuRepair`), with

    V_μ(t, ε) = ½(εt)² + (μ/2)(t² + ε²),   μ > 0   (`muPot`).

`muPot_zero : muPot 0 = normForm (1/2)` records that the `μ = 0` member is exactly §61's potential, so
the repair is a genuine deformation of the same object, not a different ansatz. On `a = t²`, `b = ε²`:

    ∑(∂V_μ)² = ab(a+b) + 4μab + μ²(a+b),     V_μ = ½(ab + μ(a+b))

(`pderiv_muPot_zero/one`, `ev2_muPot`), and the algebraic core `muPot_quad_bound` proves

    4μ·∑(∂V_μ)² ≤ (5 + μ)(ab + μ(a+b))² + 4μ³

by three polynomial estimates: `4μ·ab(a+b) ≤ (ab+μ(a+b))²` (AM–GM), `16μ²ab ≤ 4(ab+μ(a+b))²`, and
`4μ³(a+b) ≤ μ(ab+μ(a+b))² + 4μ³` from `μ(a+b) ≤ ab+μ(a+b)` and `(s−2μ)² ≥ 0`. Dividing gives
`muPot_dom`:

    ∃ A B, ∀ x, ∑(∂V_μ)² ≤ A·V_μ² + B,   with A = 5/μ + 1, B = μ².

**`B > 0` is necessary, not slack.** `muPot_no_hom_dom` shows that for *every* `A` there is a state with
`∑(∂V_μ)² > A·V_μ²`: on the diagonal `t = ε = δ → 0` the gradient sum decays like `δ²` while `V_μ²`
decays like `δ⁴`, so no homogeneous bound exists. The affine shape of `muPot_dom` is therefore forced by
the model.

Measured support for the constants (30000 sampled points per μ, μ from `1e-6` to `1e6`, log-uniform
`t, ε` over `1e-12..1e12`): the maximum of `∑(∂V_μ)² − (A·V_μ² + B)` over the grid is `0` (never
violated), and the `μ = 0` point `(t, ε) = (1e6, 1e-6)` has `V² = 0.25` against a gradient sum of `1e12`,
i.e. ratio `4e12`. So `5/μ + 1` is a valid `A` where §61.2's sampled `A ≈ 21` was only an estimate on
four boxes.

### 64.2. Scope

This is a **family-level** closure of a **changed** Lagrangian. The model's own `volPot` is the `μ = 0`
member and stays un-dominated (`muPot_zero` plus §61's `not_volDom_shear`); what is proved is that the
deformation-norm augmentation removes the obstruction with constants uniform in the state and explicit in
`μ`. `lagGradDom_of_volDom`'s chain has therefore been re-run for the modified potential, not for the
original one, which is the caveat §61.2 asked for.

### 64.3. Verification (2026-11-13b)

* `lake build BookProof.Ns.ChapterNsVolDomMuRepair` — `Build completed successfully`; no warning
  attributed to the module.
* `lake env lean Work/NsVolDomMuRepairAudit.lean` — 7 declarations (`muPot_zero`, `ev2_muPot`,
  `pderiv_muPot_zero`, `pderiv_muPot_one`, `muPot_quad_bound`, `muPot_dom`, `muPot_no_hom_dom`), all on
  exactly `propext, Classical.choice, Quot.sound`; no `sorryAx`.
* the grid check above, run as a standalone script over 11 values of `μ`.

## §65. The structure-constant remainder of `{Ω, b}` (2026-11-13b)

### 65.1. The remainder, exactly

§62.3 could only say that the cubic ghost half of `smBrstCharge` "picks up a term proportional to the
structure constants". New module `BookProof/Sm/ChapterSmIndexGhostRemainder.lean` (namespace
`BookProof.SmGhostRemainder`) computes it. Each cubic ghost term carries one antighost, but pushing a
single `β_d` through the pair `χ_a χ_b` produces **two** contraction channels:

    { χ_a χ_b β_e , β_d }  =  δ_{da} χ_b β_e − δ_{db} χ_a β_e      (`cubic_anticomm`),

and summing over `d` gives `χ_b β_e − χ_a β_e` (`sum_d_cubic_anticomm`). Over the charge, antisymmetry in
the first two slots makes the two channels equal, so

    { Q f χ β , b }  =  2 · ∑_{x,e} (∑_y f_{yxe}) · χ_x β_e          (`Q_anticomm_bGhost`),

and hence, with the matter half of §62,

    { Ω , b }  =  ∑_a G^a  −  ∑_{x,e} (∑_y f_{yxe}) χ_x β_e          (`brstCharge_anticomm_bGhost`).

The sign is a minus: the charge is `∑χG − ½Q`, so `{Ω,b} = {∑χG,b} − ½{Q,b}`. The coefficient is the
**first-slot trace** of `f`, `structTrace f x e = Σ_y f_{yxe}`, and antisymmetry in the first two slots
does *not* make it vanish — this is the precise sense in which "the free ghost complex is not a
subcomplex of the interacting one".

Two consequences. `brstCharge_anticomm_bGhost_of_trace_zero`: if the trace vanishes (in particular for
an abelian algebra, `brstCharge_anticomm_bGhost_abelian`) then `b` anticommutes with the *full* charge,
not only its matter half — §62's corollary upgraded from the derivation to the charge. And
`su2Trace_nonzero`: for `su(2)` structure constants `f_{abc} = ε_{abc}` the trace is `su2Trace 1 0 = −1`
(`epsZ_trace_ten`, `by decide`), so the full charge does **not** admit `b` as a contracting homotopy —
the same structural reason as §62's matter half: the contraction lands in the Gauss sector.

### 65.2. The SM instance: definitional, and the limitation is Lean's

`smBrstCharge_def : smBrstCharge m T f3 = brstCharge (smStruct f3) (ghostCre m) (ghostAnn m) (matterGen
m T)` is `rfl`, so the general theorem *is* the SM statement once that identification is used.

Instantiating the general theorem at `R := Module.End ℂ (FermiFock (m + 12))` with `n = 12` as a
separate declaration **does not terminate**: `whnf` runs out past 8M heartbeats, and even
`Algebra ℝ (Module.End ℂ (FermiFock (m + 12)))` exceeds the default 20000 typeclass heartbeats. The cause
is an **instance diamond**, not the mathematics: the goal's `+`/`∑` elaborate through `LinearMap.instAdd`
while the theorem's argue through `Ring.toAdd` of the `End`-ring, so deciding the definitional equality
unfolds `PiLp`/`ESeminormedAddCommMonoid`/`ENNReal`. At `n = 3` or `R = ℂ` the instantiation is
immediate.

**Corrected 2026-11-13c: the corollary is asserted anyway.** §6 of
`BookProof/Sm/ChapterSmIndexGhostRemainder.lean` proves

    smBrstCharge m T f3 * bGhost m + bGhost m * smBrstCharge m T f3
      = gaussSum m T − ∑ x, ∑ e, (algebraMap ℝ _ (structTrace (smStruct f3) x e))
          * (ghostCre m x * ghostAnn m e),

with **no** hypothesis on `b` (the ghost CAR supplies the `1/2` cancellation). The workaround is to
re-run the computation in the concrete ring instead of transporting the abstract theorem: the two
inputs `Q_anticomm_bGhost` and `bGhost_anticomm` are combined locally
(`hQ := Q_anticomm_bGhost`, `hM := bGhost_anticomm m T`, then `unfold smBrstCharge brstCharge bGhost
SmIndexGhostDerivation.gaussSum` and `rw [sub_mul, mul_sub, smul_mul_assoc, mul_smul_comm, hsplit, hM,
hQ']`). Same statement, no `sorry`, no `rfl`-through-unification; the module carries
`set_option maxHeartbeats 800000 in` with the reason in a comment. What remains unproved by *this*
route is only that the abstract theorem transports definitionally at `n = 12` — which is why the
statement is re-derived rather than `exact`ed.

### 65.3. Verification (2026-11-13b)

* `lake build BookProof.Sm.ChapterSmIndexGhostRemainder` — `Build completed successfully`, **8030 jobs**;
  no warning attributed to the module.
* `lake env lean Work/SmIndexGhostRemainderAudit.lean` — 7 declarations (`cubic_anticomm`,
  `sum_d_cubic_anticomm`, `Q_anticomm_bGhost`, `brstCharge_anticomm_bGhost`,
  `brstCharge_anticomm_bGhost_of_trace_zero`, `brstCharge_anticomm_bGhost_abelian`, `su2Trace_nonzero`),
  all on exactly `propext, Classical.choice, Quot.sound`; no `sorryAx`.
* independent `#eval`-free check that `su2Trace 1 0 = -1` is `by decide` on `Fin 3` (`epsZ_trace_ten`).
* `lake build BookProof` — `Build completed successfully`, **9001 jobs**, exit 0, with all three new
  modules imported and registered in the root (§63's and §64's too).
* `scripts/check-sm-section-guards` — green, including the new §63/§64/§65 sections.

## §66. The Fourier reconstruction, as far as it is algebraic (2026-11-13c)

### 66.1. What is proved

§63 stopped at a boundary it named: `not_volDom_normForm` is a theorem about the normal form
`c(εt)²`, and the passage from the model's own penalty `volPot kappa kv = (κ/2) Σ_q |(det F − 1)^(q)|²`
to that normal form was measurement. New module `BookProof/Ns/ChapterNsVolDomReconstruction.lean`
(namespace `BookProof.NsVolDomReconstruction`) moves part of the line.

**The dual grid is orthogonal.** With `ω = exp(2πi/N)` on an `N`-point grid,

    ∑_{j < N} ω^{m·j} = 0   unless `N ∣ m`        (`dft_orthogonal`),
    ∑_{j < N} ω^{0·j} = N                          (`dft_zero`),

which is the algebraic content of "a mode the grid cannot resolve averages to nothing". No measure
theory: the grid is finite, the proof is the geometric series (`geom_sum_eq`) plus `ω^N = 1` from
`Complex.isPrimitiveRoot_exp`.

**A single-mode residual is exactly its coefficient.** If the residual's spectrum is supported at the
zero mode — which is what *spatially constant* means on a finite grid — then

    volPot kappa kv = (κ/2) Λ²        (`volPot_of_single_mode`),

and with `Λ = c·ε·t` on §63's shear family,

    volPot kappa kv = (κ/2)(c·ε·t)²   (`volPot_of_shear_constant`),
    volPot kappa kv = (κ/2) · value of `normForm c` at `(t, ε)`   (`volPot_of_shear_constant_normForm`).

So the constant `c` that §63 refutes domination for, for every `c ≠ 0`, is the *measured* constant:
the penalty's value is `(κ/2)` times the normal form's, with no re-scaling smuggled in.

### 66.2. What was still not proved, and is now (see §68)

The assembly from position space to that spectrum. `volPot`'s sum over `waveSet` was asserted at the
coefficient level, and the identity `(1/N) Σ_j |R(a_j)|² = Σ_q |R̂_q|²` (unitarity of the discrete
transform) was not formalized — so `hspec` was a hypothesis. **§68 does that assembly**: the transform
is inverted on a grid (`coeff_eq_zero_of_grid_vanishing`) and the spectrum of a *spatially constant*
residual is derived (`volCoef_eq_zero_of_constant`, `volPot_of_single_mode_of_constant`), so `hspec`
no longer appears as a hypothesis. What stays open there is the instantiation of the grid
orthogonality at a concrete commensurate grid.

### 66.3. Verification (2026-11-13c)

* `lake build BookProof.Ns.ChapterNsVolDomReconstruction` — `Build completed successfully`, **8143
  jobs**; no warning attributed to the module.
* `lake env lean Work/NsVolDomReconstructionAudit.lean` — 5 declarations (`dft_orthogonal`,
  `dft_zero`, `volPot_of_single_mode`, `volPot_of_shear_constant`,
  `volPot_of_shear_constant_normForm`), all on exactly `propext, Classical.choice, Quot.sound`; no
  `sorryAx`.

## §67. The augmented Lagrangian: `VolDom` discharged rather than assumed (2026-11-13c)

### 67.1. The chain

§61 refuted `VolDom` for the model's own penalty, which left `lagGradDom_of_volDom` (§56) with an
unsatisfiable hypothesis and the NS chain stopping there. §64 proved the estimate for the repair
`V_μ = ½(εt)² + (μ/2)(t² + ε²)` but never fed it back. New module
`BookProof/Ns/ChapterNsVolDomMuLagrangian.lean` (namespace `BookProof.NsVolDomMuLagrangian`) feeds it
back: in the two shear coordinates `x₀ = t`, `x₁ = ε` the augmented Lagrangian is

    W = 1 + ½(t² + ε²) + V_μ        (`lagMu`),

and

    ∑_i (∂_i W)² ≤ (2A + 2)·W² + (2B + 2),   A = 5/μ + 1,  B = μ²     (`lagGradDom_mu`)

holds at **every** real point with **no** hypothesis: `VolDom` is proved for this model, not assumed.

### 67.2. Why the constants add rather than multiply

The three steps are the ones `lagGradDom_of_volDom` spells out, and each is now a lemma:

* `(x_i + ∂_i V_μ)² ≤ 2x_i² + 2(∂_i V_μ)²`, so the shear quadratic enters with coefficient `2`
  (`ev2_pderiv_lagMu_zero`/`_one` carry the derivative, `one_le_ev2_lagMu` the coercivity);
* `Σ_i (∂_i V_μ)² ≤ A V_μ² + B` is §64's `muPot_dom`, consumed through `muPot_dom_nonneg` — the
  comparison `A V_μ² ≤ A W²` needs `A ≥ 0`, and taking `max A 0`, `max B 0` supplies it without
  changing the estimate;
* `V_μ ≥ 0` gives `V_μ ≤ W`, and `t² + ε² = 2(W − 1) ≤ W² + 1` because `W ≥ 1`.

### 67.3. Scope

The model has exactly the two coordinates of the shear family: it is §64's augmented Lagrangian, **not**
`LagNsData`'s `volPot` (whose `VolDom` is false, §61). What it removes is the hypothesis — on this model
the §49 chain (`GradBound → pointwise_dom_of_sq_sum → PotSelfBound`) runs end to end with nothing
assumed. It is not a claim about the three-dimensional model, and it does not certify ESA of `N_L`.

### 67.4. Verification (2026-11-13c)

* `lake build BookProof.Ns.ChapterNsVolDomMuLagrangian` — `Build completed successfully`, **8143
  jobs**; no warning attributed to the module.
* `lake env lean Work/NsVolDomMuLagrangianAudit.lean` — 5 declarations (`ev2_lagMu`,
  `one_le_ev2_lagMu`, `ev2_pderiv_lagMu_zero`, `ev2_pderiv_lagMu_one`, `lagGradDom_mu`), all on
  exactly `propext, Classical.choice, Quot.sound`; no `sorryAx`.
* `muPot_dom_nonneg` added to `ChapterNsVolDomMuRepair` (rebuild clean) rather than duplicating the
  estimate's proof.

## §68. The Plancherel assembly: `hspec` derived, not assumed (2026-11-14)

### 68.1. The inversion

§63/§66 assumed that the residual `det F − 1` has no nonzero Fourier coefficient (`hspec`). The reason
it could not be derived was that the *position-space* statement had never been formalized: constancy of
`det(I + ∇ξ)` in `a`. §68 supplies the missing step, in the form the argument actually needs — the
inversion of the discrete transform.

`coeff_eq_zero_of_grid_vanishing` (with `phase q a = e^{i q·a}` and `phase_mul_conj`, `phase_conj`):
if the grid pairs the modes unitarily,

    horth :  Σ_{a ∈ G} e^{i (q − q')·a}  =  if q = q' then |G| else 0,

then a residual with `Σ_q c_q e^{iq·a} = 0` at every `a ∈ G` has `c_q = 0` for all `q`. The proof is
one line of algebra — multiply by `e^{−i q'·a}`, sum, use `horth`:

    0 = Σ_a (Σ_q c_q e^{iq·a}) e^{−i q'·a} = Σ_q c_q · (Σ_a e^{i(q−q')·a}) = c_{q'} · |G|.

`coeff_eq_zero_of_grid_const` handles the constant right-hand side by subtracting the zero mode — which
is what a *spatially constant* residual is.

### 68.2. From constancy to the spectrum

`detCoef_eval_eq_zero_of_constant`: if `det(I + ∇ξ(a)) = 1 + Λ` at every grid point (the modelling
fact — this is exactly what the shear family has, `det F = 1 − εt` everywhere), then
`ev y (detCoef kv q) = 0` for every `q ≠ 0`. The bridge is `det_deformation_eq`, which already expresses
`det(I + ∇ξ(a))` as the Fourier series `Σ_q ev y (detCoef q) e^{iq·a}` — so the inversion applies
verbatim.

Then `volCoef_eq_zero_of_constant` lifts that from evaluations to the *polynomial*: `ev`-vanishing at
every real point forces `volCoef kv q = 0`, via `mvpoly_eq_zero_of_eval_real_fintype` (a general form of
the `Fin n` lemma in `ChapterHermiteProductCore`, proved here with `MvPolynomial.funext_set` on the
real line). `volCoef_zero_eq_of_constant` gives the zero coefficient as the constant `Λ`.

The payoff is that the two §66 theorems now have hypothesis-free-spectrum versions:

    volPot_of_single_mode_of_constant :  volPot kappa kv = C((κ/2) Λ²),
    volPot_of_shear_constant_of_const :  volPot kappa kv = C((κ/2)(c ε t)²),

with **no** `hspec`: the inputs are `h0 : 0 ∈ waveSet kv` (as before), `hconst` (constancy on the grid)
and `horth` (grid unitarity). `hspec` is a *consequence* of the first two, not an assumption.

### 68.3. What is still open

The instantiation of `horth` at a concrete grid. `dft_orthogonal` (§1 of the module) is the level-1
statement — `Σ_{j<N} ω^{mj} = 0` unless `N ∣ m` — and it is exactly what the commensurate case (modes
`2πm/N`, grid `j ↦ j•e₀`) needs, but the reduction of the general `horth` to it (a labelling of the
modes by their grid frequencies, plus injectivity modulo `N`) is **not** carried out here. So the honest
statement of the gain: `hspec` is no longer assumed *given* the grid unitarity; the grid unitarity
itself is assumed, and it is a statement about the numerical grid rather than about the physics.

### 68.4. Verification (2026-11-14)

* `lake build BookProof.Ns.ChapterNsVolDomReconstruction` — `Build completed successfully`, **8141
  jobs**; no warning attributed to the module.
* `lake env lean Work/NsVolDomReconstructionAudit.lean` — **15** declarations, all on exactly
  `propext, Classical.choice, Quot.sound`; no `sorryAx`. New: `mvpoly_eq_zero_of_eval_real_fintype`,
  `phase_conj`, `phase_mul_conj`, `coeff_eq_zero_of_grid_vanishing`, `coeff_eq_zero_of_grid_const`,
  `detCoef_eval_eq_zero_of_constant`, `volCoef_eq_zero_of_constant`, `volCoef_zero_eq_of_constant`,
  `volPot_of_single_mode_of_constant`, `volPot_of_shear_constant_of_const`.

## §69. The constants do not depend on the dimension (2026-11-14)

### 69.1. The estimate in `n` coordinates

§67 closed the NS chain in the *two* shear coordinates, which invited the reading that the estimate is a
two-dimensional accident. It is not. `lagGradDom_family` proves, for every `n` and every non-negative
potential `V` whose own gradient is dominated (`Σ_i (∂_i V)² ≤ A V² + B`),

    Σ_i (x_i + ∂_i V)²  ≤  (2A + 2)·W² + (2B + 2),      W = 1 + ½ Σ_i x_i² + V,

with the **same** constants as `n = 2`: no step multiplies by `n`. The absorption happens once, through
`Σ_i x_i² = 2(W − 1 − V) ≤ W² + 1`, and `(x + d)² ≤ 2x² + 2d²` contributes a fixed `2`.

### 69.2. The nine-component instance

`LagNsData`'s `volPot` does not live in two coordinates: it is a function of the nine components of the
3D deformation gradient `∇ξ`. `lagGradDom_mu_nine` therefore assembles the augmented Lagrangian in
**those nine coordinates** — the two shear entries carrying `V_μ`, the other seven flat
(`V9`, `d9`, `d9_sum`) — and closes the chain there, with `a = 2A + 2`, `b = 2B + 2` for the `A, B` of
`muPot_dom_nonneg`. The dimension is not what the estimate was ever restricted by.

### 69.3. What this does not say

It is a statement about the **augmented** model in three dimensions. The model's own `volPot` still has
no gradient domination at all (§61: `not_volDom_shear`), and `lagGradDom_mu_nine` does not change that —
what it removes is the suggestion that the repair worked only because the shear family is
two-dimensional. Nothing here claims ESA of the 3D Lagrangian generator.

### 69.4. Verification (2026-11-14)

* `lake build BookProof.Ns.ChapterNsVolDomMuLagrangian` — `Build completed successfully`, **8142
  jobs**; no warning attributed to the module.
* `lake env lean Work/NsVolDomMuLagrangianAudit.lean` — **8** declarations, all on exactly
  `propext, Classical.choice, Quot.sound`. New: `lagGradDom_family`, `lagGradDom_mu_nine`, `d9_sum`.

## §70. The quartet condition and the explicit antighost (2026-11-14)

### 70.1. The observation

`PhysicalPositivity` for `smBrstCharge` has been carried as a named input. Part of that story is stale:
the quartet **data** for the SM charge already exists — `ChapterSmQuartet` §8 builds `smQuartet`,
`smBghost`, `smPhysProj` by `exists_contractingHomotopy` (a choice of complement of the exact states in
the closed space), so `physicalPositivity_of_quartet` *does* apply, and §9 reduces the remaining input to
positivity of the charge form on `range smPhysProj`. What was never explained is *why* the b-ghost has
to be chosen rather than exhibited, given that the model has an explicit antighost sum `bGhost`.

§70 answers that. `bGhost_quartet_iff`: with `Q = smBrstCharge m T f3` and `P = bGhost m`, the quartet
condition `Q P Q = Q` is **equivalent** to

    (Σ_a G^a − traceEnd) · Q  =  Q,        traceEnd = Σ_{x,e} (Σ_y f_{yxe}) · c^x b_e,

i.e. the trace-corrected Gauss generators must act as the identity on the charge's range. The proof is
`{Q, b} = S` (that is `smBrstCharge_anticomm_bGhost`), `Q² = 0` (that is `smBrstCharge_nilpotent`), and
`Q b Q = (S − bQ) Q = S Q`.

So the explicit antighost is a contracting homotopy exactly when the Gauss sector supplies the identity
— the condition `bGhost_no_contraction` named — and the first-slot trace of `smStruct` is what stands in
the way. This is why `smQuartet` is choice-based: the choice is of a complement, not of a formula.

### 70.2. What is still open

`PhysicalPositivity (smBrstCharge m T f3) η` itself. It remains a consequence of a no-ghost estimate on
`range smPhysProj` (`smPhysicalPositivity_of_physForm`), and the choice-based construction does not
identify that range with the transverse, ghost-parity-even subspace — that needs a concrete mode
pairing, which no formula in the corpus supplies. Nothing in §70 proves positivity; it shows that the
obvious candidate for `P` fails for the reason the trace gives.

### 70.3. Verification (2026-11-14)

* `lake build BookProof.Sm.ChapterSmIndexGhostRemainder` — `Build completed successfully`, **8031
  jobs**; the only message attributed to the module is a pre-existing "Try this" at line 266.
  Measured build time ≈ 3 min, dominated by the kernel checking `smBrstCharge_anticomm_bGhost`'s
  elaboration at `Module.End ℂ (FermiFock (m + 12))`.
* `lake env lean Work/SmIndexGhostRemainderAudit.lean` — **10** declarations, all on exactly
  `propext, Classical.choice, Quot.sound`; new: `traceEnd`, `bGhost_quartet_iff`.

## 71. The commensurate reduction: `horth` is discharged at the grid it is meant for

§68 removed `hspec` at the price of a hypothesis: unitarity of the discrete transform on the grid
(`horth`). That hypothesis is now derived, in `BookProof/Ns/ChapterNsVolDomReconstruction.lean` §4, at
the grid it describes — `N` equally spaced points `j • e` along a direction `e ≠ 0`:

* `phase_smul_eq_gridRoot`: the plane-wave pairing of two modes at the `j`-th grid point is
  `ζ^{m·j}` (`ζ = e^{2πi/N}`) as soon as `⟨q − q', e⟩ = 2πm/N`;
* `geom_sum_gridRoot`: the geometric sum is `N` exactly when `N ∣ m` and `0` otherwise, for `m : ℤ`
  (the integer mode number a *difference* of real wave numbers produces, via `exp_int_mul`);
* `horth_of_commensurate`: combining the two gives `horth` from a labelling
  `m : (q, q') ↦ ℤ` with `⟨q − q', e⟩ = 2πm/N` and `N ∣ m ↔ q = q'`;
* `grid_card`, `grid_nonempty` supply the cardinality `N` and non-emptiness the statements need, and
  `volPot_of_single_mode_of_commensurate` / `volPot_of_shear_constant_of_commensurate` are §68's two
  theorems with `horth` replaced by that labelling.

So the Plancherel step has no *abstract* unitarity input left. What replaces it is a modelling
hypothesis, and it is not derivable from `kv`: the pairwise differences of wave numbers are lattice
fractions `2πm/N` along `e`, and the residue mod `N` separates the modes (`N ∤ m` iff `q ≠ q'`). That
is a statement about which modes the truncation keeps and it is false for a generic choice. The grid is
one line of `N` points; §74 replaces it by a three-dimensional box and analyses the aliasing that
appears across directions.

## 72. Positivity is not a consequence of the quartet schema: a decided counterexample

§70 reduced the SM quartet condition to a Gauss-sector identity. This section settles the *other*
standing question — whether `PhysicalPositivity` follows from the quartet construction — and the answer
is **no**, decided by an explicit three-dimensional model
(`BookProof/Sm/ChapterSmQuartet.lean` §10):

* `exQh`, `exBh`, `exVh`: `Q e₀ = e₁`, `Q e₁ = Q e₂ = 0`; `b e₁ = e₀`; `V` the projection onto `e₂`;
* `exQuartet3`: `Q b + b Q = 1 − V` (`quartet_pt` at every vector), `V` idempotent, `Q V = 0`, so the
  quartet data exist with no `Classical.choice` and no hypothesis;
* `kform_exEtah_Q`, `kform_exEtah_symm`: the metric `η x = x₁ e₀ + x₀ e₁ − x₂ e₂` satisfies §3's
  `hKrein` and `hSymm` — the charge is symmetric for it and it is self-adjoint;
* `exNotPhysicalPositivity`: yet `(kform η e₂ e₂).re = −1` at the physical state, which is closed, so
  `PhysicalPositivity` fails.

Hence positivity cannot be obtained by strengthening the *projection* side of §9: the metric decides,
and a no-ghost estimate on it — not an identity on `η` — is what the SM still needs. The counterexample
is about the schema, not about the Standard Model's own physical sector.

## 73. The quartet condition is a ring identity

§70's computation is not specific to `FermiFock`. `quartet_iff_of_anticomm`
(`BookProof/Sm/ChapterSmIndexGhostRemainder.lean` §8) proves, in an arbitrary ring, that from
`Q * Q = 0` and `Q * b + b * Q = S` one gets `Q * b * Q = Q ↔ S * Q = Q`. §70 is that lemma at
`R = Module.End ℂ (FermiFock (m + 12))`, `S = gaussSum − traceEnd`. What this says about deciding
`(Σ G^a − traceEnd) Q = Q`: the equation is *not* an identity of the ghost algebra — it says the
remainder acts as the identity on `range Q`, and that is a matter-sector statement, which is why §5's
`su2Trace 1 0 = −1` refutes it for `bGhost` but cannot settle it for a different candidate.

## 74. The three-dimensional box: aliasing is a residue condition in every direction

`BookProof/Ns/ChapterNsVolDomReconstruction.lean` §5 replaces §71's line by the box
`j ↦ Σ_x j x • e x` with `j x < N` in each coordinate, the three coordinate vectors of `e` assumed
independent:

* `latPoint`, `gridBox`, `latPoint_injective`, `gridBox_card`: the box is a set of `N³` distinct
  points, the injectivity coming from independence and the entries being distinct natural numbers;
* `phase_latPoint`: with a per-direction pairing `Σ_y w y e x y = 2π m x/N`, the phase at the `j`-th
  box point is `ζ^{Σ_x m x · j x}` — so the exponent is a *sum* of three pairings;
* `geom_sum_latBox`: the sum over the box is `N³` exactly when `(N : ℤ) ∣ m x` for **every** `x`, and
  `0` otherwise. One non-commensurate direction kills the whole sum: a mode cannot be repaired
  direction by direction;
* `horth_of_lattice_commensurate`: the unitarity hypothesis of §68 on the box, from a per-direction
  labelling with `N ∣ m q q' x ↔ q ≠ q'` holding for all `x` at once;
* `latBox_character_one_iff`: the alias classes. The character is trivial on the box exactly when each
  dual component differs by a multiple of `2π`, i.e. `q − q' ∈ N·Λ*`. The *total* wave number is
  irrelevant: two modes collide whenever their residue vector does, and only then;
* `volPot_of_single_mode_of_lattice_commensurate`: the assembly, as in §71.

Boundary: the box is one truncation and its coordinates are assumed independent; the residue statement
describes which modes collide *on that truncation*, not which modes the model keeps. Nothing is claimed
about the penalty off the constant family.

## 75. Which metrics are no-ghost: `PhysicalPositivity` is an equivalence

§72 showed the quartet schema does not decide positivity. The natural question is then which metrics do,
and `BookProof/Sm/ChapterSmQuartet.lean` §11 answers it with equivalences rather than implications:

* `physicalPositivity_iff_physForm`: `PhysicalPositivity Q η` holds **iff** `η` is positive definite on
  `range V` — non-negative there, and vanishing only at `0`. The forward direction uses the idempotence
  of `V`, the radical condition and `V Q = 0` (a fixed point of `V` in the gauge orbit is `0`); the
  reverse is §9's `physicalPositivity_of_quartet_on_range`. So the reduction of §9 is exact;
* `physicalPositivity_congr`: two metrics agreeing on `range V` are no-ghost together. The ghost
  directions are irrelevant, so no change of the metric away from the physical subspace can create or
  remove the sign;
* `range_physProj_eq_inf`: given that the b-ghost kills the physical subspace, the physical range is
  `ker Q ⊓ ker b` — the harmonic representatives, matching §5's `range_physProjOf`;
* `smPhysicalPositivity_iff_physForm`: the same equivalence at `smBrstCharge`, so the check on a
  concrete SM metric is a sign computation on `range smPhysProj = ker Ω ⊓ (range Ω)ᗮ`
  (`smPhysProjFormula_range`).

Boundary: the equivalence does not *produce* the sign — §72's model has the same hypotheses with the
opposite sign on `range V` — and no metric for `smBrstCharge` is constructed in this corpus. The SM
statement is therefore an equivalence in `η`, not a verification for a particular `η`; a ghost-parity
operator for the SM charge remains unbuilt.

## 76. A candidate whose remainder vanishes on the charge's range

§73 left the trace-corrected Gauss equation undecided for a candidate. `BookProof/Sm/ChapterSmIndexGhostRemainder.lean`
§9 decides what the equation asks of one:

* `QbQ_eq_SQ`: from `Q² = 0` and `{Q, b} = S` one has `Q b Q = S Q` identically, so the quartet
  condition and "`Σ − trace` acts as the identity on `range Q`" are the *same* equation, not two;
* `smBrstCharge_mul_traceCorrected`: the same identity at the SM charge,
  `(Σ − trace) Ω = Ω b Ω`. The equation constrains the charge algebra, which is why changing the
  b-ghost alone cannot make it true or false;
* `trace_correction_iff`: if `T Q = 0` the correction is invisible — `(S − T) Q = Q` and `S Q = Q` are
  the same equation. The explicit antighost's failure at `su₂` is exactly a correction that does *not*
  kill the range (`su2Trace 1 0 = −1`, §7);
* `quartet_condition_of_contracting`: a `b` that contracts `Q` on its range (`Q b Q = Q`, which
  `exists_contractingHomotopy` supplies in finite dimension) makes the equation hold for its own
  anticommutator;
* `CandModel.cand_equation`: a two-dimensional model — `q`: `e₀ ↦ e₁`, `b`: `e₁ ↦ e₀`, `tr`: `x ↦ x₀ e₀`
  with `tr` nonzero but `tr q = 0` — where `q b q = q` and `((q b + b q) − tr) q = q`. The positive case
  exists, with a nonzero correction.

Boundary: this does not construct a b-ghost for `smBrstCharge`. It shows what the equation requires of
one and that the choice-based homotopy meets the requirement, not that the SM's Gauss sector is
trace-free.

