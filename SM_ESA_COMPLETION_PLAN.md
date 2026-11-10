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
