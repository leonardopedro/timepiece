# PLAN_LEAN_SPECIALIST_QYM_FLOW.md — Quantum Yang–Mills: the Friedrichs route

This is the plan item requested by `CONSOLIDATED_PLAN.md` §11.3 ("Suggested next
step"), in the style of `PLAN_LEAN_SPECIALIST_NS_FLOW.md`: Part A the Weyl-gauge
fiber, Part B the quadratic form and its closure, Part C the Friedrichs extension
as a **named theorem, never an axiom**, Part D the Hashimoto/SIRK limit.

**Status (2026-08-20f): the *abstract* Stone theorem is proved (2026-08-20e,
`ChapterStoneResolvent`–`ChapterStoneSeparable`), but the continuous flow is
**not yet instantiated for QYM**.**  `stoneGroup`/`stoneEquiv` apply to a bundled
`UnboundedSelfAdjoint` structure; the QYM thread only produces
`IsPositiveSelfAdjointExtension` operators (`A : Dom →ₗ[ℂ] Fock`).  The bridge —
repackaging the selected Friedrichs extension as `UnboundedSelfAdjoint`
(`IsSelfAdjointExtension` already holds, so a wrapper lemma suffices) and then
applying `stoneGroup` to obtain `e^{-itA}` — is not built, and no module imports
`ChapterStone*` except `Book/FreeField.lean` (prose).  This is the recorded
instantiation step for the next specialist.

**Status (2026-08-18, third pass): Part C is now discharged *without any
boundedness hypothesis*, and the two plan items of `CONSOLIDATED_PLAN.md` §11.4
are closed.**  `BookProof/ChapterFriedrichsExtension.lean` (namespace
`BookProof.FriedrichsExtension`, `sorry`-free / `axiom`-free) proves the
Friedrichs extension theorem itself — see the new rows C.8–C.12 and D.9–D.11 —
and settles the realization question in favour of the occupation-number (Hermite)
picture.

**Status (2026-08-17, second pass): Parts A–C executed; Part C is now also
*discharged by construction* in the bounded regime, and Part D.4 is proved there
rather than left as prose.  See the new rows C.5–C.7 and D.5–D.8 below, in
`BookProof/ChapterYangMillsFriedrichsLimit.lean`.**

**Status (2026-08-17): executed, with one item deliberately left unstated.**
Parts A–C and the proved half of Part D are in
`BookProof/ChapterYangMillsFriedrichs.lean`, `sorry`-free and `axiom`-free,
registered in `BookProof.lean`, certified in `BookProof/ChapterRoadmapAudit.lean`
and cited from `Book/YangMillsQuantization.lean`.  The Part D *identification of
the SIRK limit with the Friedrichs extension* remains a research conjecture and is
recorded in prose only (see the note at the end of Part D).

## The setting

The 3D gauge-fixed Yang–Mills Hamiltonian (`book.tex` ~7037–7120) is, in the Weyl
gauge and the Hermite basis, a **sum of squares** of the self-adjoint electric- and
magnetic-field operators,

```
H = ½ Σ (πⁱ_a)² + ½ Σ (B_{i a})²,
```

hence symmetric and bounded below by `0`.  `BookProof/ChapterWeylHamiltonian.lean`
already proves this for *bounded* fields (`weylHamiltonian_isPositive`); the
Friedrichs route needs the densely defined version.

## Part A — the Weyl-gauge Hamiltonian on a domain

| Item | Lean name | Status |
| :-- | :-- | :--: |
| A.1 `H = ½Σπᵢ² + ½ΣBₐ²` as an operator on an invariant domain | `weylOpDom`, `weylOp`, `weylOp_apply` | PROVED |
| A.2 symmetry on the domain | `weylOpDom_symmetricOn` | PROVED |
| A.3 the quadratic form is the sum of squares `½Σ‖πᵢx‖² + ½Σ‖Bₐx‖²` | `weylOpDom_quadForm` | PROVED |
| A.4 semi-boundedness (`H ≥ 0`), the hypothesis of Friedrichs | `weylOpDom_quadForm_nonneg` | PROVED |
| A.5 (already in the repository) the bounded case | `BookProof.WeylHamiltonian.weylHamiltonian_isPositive` | PROVED |

## Part B — the quadratic form and its closure

For an arbitrary symmetric positive `H` on a domain `D`:

| Item | Lean name | Status |
| :-- | :-- | :--: |
| B.1 the form `⟪x,y⟫_H = ⟪x,y⟫ + ⟪x,Hy⟫` and the form norm | `formInner`, `formNormSq`, `formNormSq_eq` | PROVED |
| B.2 the form is Hermitian | `formInner_conj_symm`, `re_formInner_swap` | PROVED |
| B.3 it dominates the ambient norm (`‖x‖² ≤ ‖x‖_H²`), hence is an inner product | `formNormSq_ge_normSq`, `formNormSq_nonneg` | PROVED |
| B.4 the expansions `‖x+y‖_H²`, `‖x−y‖_H²`, `‖x+ty‖_H²` | `formNormSq_add`, `formNormSq_sub`, `formNormSq_add_smul` | PROVED |
| B.5 **Cauchy–Schwarz** for the form | `re_formInner_sq_le` | PROVED |
| B.6 **closability of the form** — the analytic heart of the Friedrichs construction | `form_closable` | PROVED |
| B.7 the Weyl-gauge form is closable | `weylForm_closable` | PROVED |

B.6 says: if `xₙ` is Cauchy in the form norm and `xₙ → 0` in the ambient space,
then `‖xₙ‖_H → 0`.  Symmetry and positivity of `H` are exactly what the proof
uses; without closability the "closed form" of the Friedrichs construction would
not be well defined.

## Part C — the Friedrichs extension as a named theorem

| Item | Lean name | Status |
| :-- | :-- | :--: |
| C.1 what a positive self-adjoint extension *is* (domain, agreement, symmetry, positivity, adjoint condition) | `IsPositiveSelfAdjointExtension` | DEFINED |
| C.2 the Friedrichs theorem as an explicit hypothesis, applied | `friedrichs_extension_of_semibounded` | PROVED (hypothesis named) |
| C.3 the hypothesis is satisfiable (everywhere-defined case) | `friedrichs_hypothesis_satisfiable` | PROVED |
| C.4 the conclusion for the Weyl-gauge Hamiltonian, conditional on C.2 | `weyl_friedrichs_extension` | PROVED |
| C.5 the Friedrichs hypothesis **discharged by construction** for bounded operators on a dense domain | `friedrichs_of_bounded` | PROVED |
| C.6 symmetry and positivity pass from a dense domain to the whole space | `symmetricOn_top_of_dense`, `quadForm_top_nonneg_of_dense` | PROVED |
| C.7 the construction applies to a genuinely **proper** dense domain (in `ℓ²(ℕ,ℂ)`) | `friedrichs_bounded_proper_domain_example`, `not_mem_span_of_repr_ne_zero` | PROVED |
| C.8 the domain with the form inner product is an inner product space, and the form norm dominates the ambient norm | `PosSymOp`, `FormDom`, `FormDom.instCore`, `FormDom.norm_toAmbient_le` | PROVED |
| C.9 the form completion embeds into the ambient space (closability, no ghost vectors) | `FormDom.formExt`, `FormDom.inner_coe_eq`, `FormDom.formExt_injective` | PROVED |
| C.10 the resolvent `(H+1)⁻¹` by Riesz representation: bounded, injective, positive, self-adjoint, and inverse to `x ↦ x + Hx` | `FormDom.friedrichsResolvent`, `_isSelfAdjoint`, `_pos`, `_injective`, `_shift` | PROVED |
| C.11 **the Friedrichs theorem, no boundedness hypothesis**; C.2's named hypothesis discharged | `friedrichs_extension_exists`, `friedrichs_hypothesis_holds` | PROVED |
| C.12 the Weyl-gauge conclusion, unconditional | `weyl_friedrichs_extension_unconditional` | PROVED |

C.5–C.7 live in `BookProof/ChapterYangMillsFriedrichsLimit.lean`: on the bounded
class the extension is built, not assumed, and the domain may be a proper dense
subspace.  C.8–C.12 (`BookProof/ChapterFriedrichsExtension.lean`) go further and
**remove the named hypothesis of C.2 outright**: the classical form-completion
construction is carried out in Lean (form inner product → completion → Riesz
representation → `A = S⁻¹ − 1`), so every densely defined symmetric positive
operator — bounded or not — has a positive self-adjoint extension.  C.2–C.4 are
kept as the historical conditional statements they were.

References for C.2: K. Friedrichs, *Spektraltheorie halbbeschränkter Operatoren*,
Math. Ann. **109** (1934) 465–487; M. Reed & B. Simon, *Methods of Modern
Mathematical Physics*, Thm X.23.  It is a hypothesis, never an `axiom`.

## Part D — the Hashimoto/SIRK limit

| Item | Lean name | Status |
| :-- | :-- | :--: |
| D.1 the order-`n` Krylov best-approximation error is antitone in the order | `weylKrylov_bestApprox_antitone` | PROVED |
| D.2 for a cyclic seed the error tends to `0` | `weylKrylov_bestApprox_tendsto_zero` | PROVED |
| D.3 the numerical ranges of the SIRK orders nest (already in the repository) | `BookProof.ChapterH9.sirk_numRange_nested_orders` | PROVED |
| D.4 *the infinite Hashimoto limit selects the Friedrichs extension* | — | **CONJECTURE in general; PROVED in the bounded regime, D.8** |
| D.5 the Krylov projections converge strongly to the identity for a cyclic seed | `krylov_starProjection_tendsto` | PROVED |
| D.6 the SIRK compressions `Pₙ A Pₙ` of a bounded operator converge strongly to `A` | `sirkCompression`, `sirk_compression_tendsto` | PROVED |
| D.7 the limit is unique: no other bounded operator agrees with it on the Krylov flag | `sirk_limit_unique` | PROVED |
| D.8 **D.4 in the bounded regime**: the Hashimoto limit *is* the positive self-adjoint extension | `sirk_limit_eq_positive_selfadjoint_extension`, `weyl_friedrichs_bounded` | PROVED |
| D.9 the shift-invert selection theorem with the extension **constructed**, not assumed (unbounded) | `friedrichs_hashimoto_selects` | PROVED |
| D.10 the same for the Weyl-gauge Hamiltonian in the occupation-number realization | `weyl_hashimoto_selects_friedrichs` | PROVED |
| D.11 non-vacuity: a genuinely unbounded operator (`A eₙ = n eₙ` on `ℓ²(ℕ,ℂ)`) | `unbounded_friedrichs_example` | PROVED |
| D.12 **the continuous flow `e^{-itA}` for the QYM Hamiltonian** — the abstract Stone theorem (2026-08-20e) applied to the extension of C.11 | `stoneGroup` + `UnboundedSelfAdjoint` bridge | **PENDING** — bridge not built |

D.5–D.8 (also in `BookProof/ChapterYangMillsFriedrichsLimit.lean`) construct the
missing limit operator under a boundedness hypothesis and identify it with the
extension of C.5, so D.4 is a theorem there.  D.9–D.11
(`BookProof/ChapterFriedrichsExtension.lean`) remove the last hypothesis on the
*unbounded* side: the shift-invert route of
`BookProof/ChapterHashimotoShiftInvert.lean` already converged to whichever
positive self-adjoint extension it was handed, and C.11 now hands it one.  What
is still not formalized in the unbounded case is the *strong-limit* rendering of
D.4 along a Krylov flag (as opposed to the shift-invert/resolvent rendering).

On D.4: the identification of the limit operator requires the limit of the Krylov
flag as an operator, which is not constructed here (it *is* constructed in the
bounded regime, D.5–D.8).  Every naive Lean rendering of
the sentence is either trivially true (any two extensions agree on the original
domain by definition) or presupposes that missing construction, so the item is
recorded in prose in the module docstring rather than written as a theorem.

## Honest boundary (unchanged from `CONSOLIDATED_PLAN.md` §11.3)

* **Not claimed:** self-adjointness of the continuum Yang–Mills operator on
  `L²(ℝ⁹⁹ × ℤ₂³¹)`, the mass gap, or global existence.  The Yang–Mills existence
  and mass-gap Millennium problem is out of scope; the book's own statement is a
  conditional ("if the Hamiltonian is positive-definite then … with or without a
  mass gap").
* The Friedrichs theorem for the continuum operator is a *named* theorem, in the
  same honesty class as Strichartz (§10) and the continuum Faris–Lavine
  inequalities of the Navier–Stokes thread.
* D.4 is a research item, not a plan deliverable.
* D.12 is a *mechanical* bridge (wrap `IsSelfAdjointExtension` as
  `UnboundedSelfAdjoint`, apply `stoneGroup`) and is now the only step separating
  the proved abstract Stone theorem from the QYM flow `e^{-itA}`; it is a plan
  item, not a research target.

## Part E — the continuum realization (the definitional choice of §11.4.2)

`CONSOLIDATED_PLAN.md` §11.4 item 2 asked for a decision between

* **(a)** accepting the occupation-number/Hermite realization as *the* definition
  of the quantum theory — the fields act on the finite-mode domain of a complete
  orthonormal basis of the Fock space, i.e. `ℓ²(ℕ, ℂ)` *is* the continuum in the
  Fock sense; and
* **(b)** realizing `B_{i a} = ε_{ijk}(∂_j A_{k,a} + f_{abc}A_{j,b}A_{k,c})` as a
  field-space differential operator on `L²(ℝ⁹⁹ × ℤ₂³¹)`.

**Decision (2026-08-18): (a).**  Every theorem of Parts A–D is stated for an
abstract complex Hilbert space with a `HilbertBasis ℕ ℂ F` and the finite-mode
domain of that basis, which is exactly the occupation-number realization; the
concrete model `ℓ²(ℕ, ℂ)` instantiates it (`unbounded_friedrichs_example`).  With
(a) the theory is complete as stated: existence of the extension (C.11) and its
selection by the Hashimoto/SIRK limit (D.9, D.10), with no boundedness anywhere.

Option (b) is **not** taken, and remains the recorded boundary shared with the
Navier–Stokes and quantum-gravity threads: it needs Mathlib's Sobolev /
differential-operator machinery, and nothing in the book's claims depends on it.
The mass gap stays out of scope by the author's decision.

**Refinement (2026-08-18): (b) is a construction task, not a research boundary.**
The book's base `ℝ⁹⁹` is finite-dimensional (3 coordinates + 24 fields `A_{k,a}`
+ 72 derivatives `∂_j A_{k,a}`, book.tex:7045-7048), so `L²(ℝ⁹⁹)` carries the
product Hermite basis built from the 1D `hermiteBasis`
(`BookProof/ChapterHermiteFunctions.lean`, dense by `hermiteCore_dense`).  The
one-particle Hamiltonian `H₁ = ½Σπⁱ_aπⁱ_a + ½ΣB_{i a}B_{i a}` is a finite-degree
polynomial-coefficient differential operator: coordinate multiplication by
`A_{k,a}` and the derivative `∂_j` act on Hermite functions as ladder operators,
so `H₁` is well-defined and symmetric on the Hermite core, and the
second-quantized `H` on the finite-occupation states over it — the same pattern
already proved in 1D by `harmonicOscOp_apply_eq_differential`.  So (b) is a
well-scoped **construction task**: build the product Hermite core of `L²(ℝ⁹⁹)`,
define `A`, `π = −iδ/δA`, `B` on it, prove core-invariance/symmetry/positivity
of `H₁`, then feed the proved `friedrichs_extension_exists` +
`friedrichs_hashimoto_selects`.  Two caveats to settle first:
  - **ordering:** the `πA` cross-terms inside `B²` do not commute
    (`[A_{j,a}, π^k_b] = iδ^k_j δ_{ab}`, book.tex:7060-7061) — the product needs
    Weyl ordering (`½(πA + Aπ)`), the *same* subtlety as the NS Hamiltonian
    `H_N = Σ(π_i A_i + A_i π_i)` and the E.5 BRST charge of
    `PLAN_LEAN_SPECIALIST_NS_FLOW.md`;
  - **sign:** book.tex:7077 writes `H(x) = −½ππ − ½BB`, while the plan uses the
    positive sum-of-squares `H = ½Σπ² + ½ΣB²` (bounded below by 0, the
    Friedrichs hypothesis) — reconcile the sign before feeding the operator to
    the machinery (same style of sign correction already recorded for `□` in
    `CONSOLIDATED_PLAN.md` §9.5).

## Part F — the field-space realization on the Hermite core (option (b))

**Status (2026-08-18): EXECUTED.**  The two modules
`BookProof/ChapterHermiteProductCore.lean` (namespace
`BookProof.HermiteProductCore`) and `BookProof/ChapterYangMillsHermite.lean`
(namespace `BookProof.YangMillsHermite`) are `sorry`-free and `axiom`-free, are
imported by `BookProof.lean`, certified by `#print axioms` in
`BookProof/ChapterRoadmapAudit.lean`, and cited from
`Book/YangMillsQuantization.lean`.  Both caveats are settled *in the modules*:
the Weyl ordering is `weylProd` with `weylProd_polySym` (and the commutation
relation it answers to is `commutator_coord_mom`), and the sign is fixed to the
positive sum of squares in `ymHamiltonian`.  Original plan text follows.  Executes
option (b) as a construction task (the Part E refinement above): build the book's
one-particle operator `H₁` as a concretely defined operator on the product Hermite
already-proved Friedrichs + Hashimoto theorems with it.  The resulting module
(general position) is a new file `BookProof/ChapterYangMillsHermite.lean` with
namespace `BookProof.YangMillsHermite`, reusing the existing 1D Hermite
machinery (`BookProof/ChapterHermiteFunctions.lean`, `ChapterStrichartzHermiteQG.lean`)
and the abstract theorems (`ChapterYangMillsFriedrichs.lean`,
`ChapterYangMillsFriedrichsLimit.lean`, `ChapterFriedrichsExtension.lean`,
`ChapterHashimotoShiftInvert.lean`).  After the module builds, register it in
`BookProof.lean`, certify it with `#print axioms` in
`BookProof/ChapterRoadmapAudit.lean`, and cite it from
`Book/YangMillsQuantization.lean`; then update this status row and
`CONSOLIDATED_PLAN.md` §11.3/§11.4.

### Part F scope (suggested item rows; adjust names to what actually builds)

| Item | Suggested Lean name | Status |
| :-- | :-- | :--: |
| F.1 the product Hermite basis of `L²(ℝ⁹⁹)` from the 1D `hermiteBasis` (tensor of the 1D ladder machinery) | `polyGaussCore`, `polyGaussCore_dense`, `hermiteMv`, `polyGaussCore_eq_hermiteSpan`, `coreBasis`, `span_range_coreBasis` | DONE |
| F.2 coordinate multiplication by `A_{k,a}` as an operator on the core, with the ladder action (maps each basis vector to a finite combination) | `mulOp`, `mulOp_polySym`, `CoreRep.op` | DONE |
| F.3 the functional derivative `π = −i δ/δA` as an operator on the core, symmetric | `derOp`, `momOp`, `momOp_polySym` | DONE |
| F.4 the magnetic field `B_{i a} = ε_{ijk}(∂_j A_{k,a} + f_{abc}A_{j,b}A_{k,c})` as an operator on the core, with the `ε`/`f_{abc}` tensor contraction | `levi`, `magPoly`, `realCoeff_magPoly`, `magOps` | DONE |
| F.5 the Weyl ordering of the `πA` cross-terms inside `B²` (`[A_{j,a}, π^k_b] = iδ^k_j δ_{ab}`, book.tex:7060-7061; the `½(πA + Aπ)` convention of `H_N`) | `weylProd`, `weylProd_polySym`, `commutator_coord_mom` | DONE |
| F.6 `H₁ = ½Σππ + ½ΣBB` (sign reconciled with book.tex:7077 to the positive sum-of-squares) well-defined on the core | `ymHamiltonian`, `ymHamiltonian_apply` | DONE |
| F.7 `H₁` symmetric on the core | `ymHamiltonian_symmetricOn` | DONE |
| F.8 `H₁` positive (bounded below by 0), the Friedrichs hypothesis | `ymHamiltonian_quadForm`, `ymHamiltonian_quadForm_nonneg` | DONE |
| F.9 **instantiation**: `H₁` satisfies the hypothesis of `friedrichs_extension_exists` → the Weyl-gauge field-space Hamiltonian has a positive self-adjoint extension | `ym_hermite_friedrichs_extension` | DONE |
| F.10 **instantiation**: the shift-invert Hashimoto/SIRK limit selects it → `friedrichs_hashimoto_selects` / `weyl_hashimoto_selects_friedrichs` applied | `ym_hermite_hashimoto_selects` | DONE |
| F.11 the second-quantized `H` on finite-occupation states over the core | `Conf`, `annA`, `creA`, `ccr_annA_creA`, `inner_creA_left`, `dGamma`, `dGamma_one_particle`, `dGammaOp_symmetricOn`, `dGammaOp_quadForm_nonneg`, `dGamma_friedrichs_extension`, `secondQuantization_friedrichs`, `ym_fock_friedrichs_extension`, `finiteModeDomain_fockBasisN`, `dGamma_hashimoto_selects`, `secondQuantization_hashimoto_selects`, `ym_fock_hashimoto_selects` | DONE |

**Status (2026-08-19): F.11 EXECUTED.**  `BookProof/ChapterFockSecondQuantization.lean`
(namespace `BookProof.FockSecondQuantization`) is `sorry`-free and `axiom`-free,
imported by `BookProof.lean`, certified by `#print axioms` in
`BookProof/ChapterRoadmapAudit.lean` and cited from
`Book/YangMillsQuantization.lean`.  It builds the occupation-number Fock space
`ℓ²(Conf)` over the one-particle core, `Conf = ℕ →₀ ℕ`, with its dense
finite-occupation domain `lpFiniteModes Conf`; the ladder operators `annA j`,
`creA j` with the canonical commutation relation `[a_j, a_j†] = 1`
(`ccr_annA_creA`) and the adjoint pairing `⟪a_j† u, v⟫ = ⟪u, a_j v⟫`
(`inner_creA_left`); the second quantization
`dΓ(A) = Σ_{j,k} ⟪e_j, A e_k⟫ a_j† a_k` of a one-particle operator given by its
column-finite matrix (`dGamma`, `dGamma_eq_sum`), which on the one-particle
sector *is* the one-particle operator (`dGamma_one_particle`); symmetry and
positivity of `dΓ(A)` from Hermiticity and positive semidefiniteness of that
matrix (`dGammaOp_symmetricOn`, `dGammaOp_quadForm_nonneg`), hence its
Friedrichs extension (`dGamma_friedrichs_extension`); the matrix of an arbitrary
symmetric positive one-particle operator on the finite-mode domain of a Hilbert
basis (`opCol`, `isHermCol_opCol`, `isPosCol_opCol`) and the resulting general
statement `secondQuantization_friedrichs`; and finally the instantiation by the
field-space Yang–Mills `H₁ = ½Σπ² + ½ΣB²` of Part F,
`ym_fock_friedrichs_extension`.  A closing section identifies the finite-mode
domain of the configuration Hilbert basis with the finite-occupation domain
(`fockConfBasis`, `fockBasisN`, `finiteModeDomain_fockBasisN`), so the F.10
Hashimoto/SIRK machinery applies verbatim to the second-quantized operator:
`dGamma_hashimoto_selects`, `secondQuantization_hashimoto_selects` and
`ym_fock_hashimoto_selects` state that for every shift `γ > 0` the shift-inverted
operator `R = (A + γ)⁻¹` is bounded by `γ⁻¹` and self-adjoint, its Galerkin
truncations converge strongly and in the resolvent sense, and `R` determines the
Friedrichs extension `A` uniquely.  As everywhere in this plan, no mass gap and
no global existence statement is claimed.

### Part F verification expectations

- The module is `sorry`-free and `axiom`-free; `#print axioms` on F.9–F.10 shows
  only `propext`, `Classical.choice`, `Quot.sound`.
- The `ε`/`f_{abc}` contraction is `Fin 3`-indexed finite sums (no Sobolev /
  distribution machinery needed — the base `ℝ⁹⁹` is finite-dimensional).
- The two caveats from Part E are **settled in the module, not assumed**:
  the Weyl ordering of the `πA` terms (F.5) and the sign reconciliation of
  book.tex:7077 (F.6).  If either blocks the build, stop and record it here
  rather than weakening the theorem.
- Do **not** claim the mass gap or global existence — out of scope by the
  author's decision.