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
The current Rust state model has separate bosonic and fermionic outer-universe
collections; identify a **joint** inner boson–fermion state before claiming it
implements this tensor-product one-particle object.

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
