# CONSOLIDATED_PLAN.md — The Single Plan

One plan that supersedes the per-thread plans for **future work**. It (1) collects
everything that is still **open** from `BOOK_PROOF_PLAN.md`,
`PLAN_LEAN_SPECIALIST_UNPROVED.md`, `SPECIALIST_PLAN_REMAINING.md`,
`PLAN_LEAN_SPECIALIST_COHERENT.md`, `PLAN_A_BOOK_FORMALIZATION.md`,
`PLAN_B_PROSE_VERIFICATION.md`, `SINGULARITY_DETECTION_PLAN.md` and
`PLAN_A_EXECUTION_REPORT.md`, and (2) gives a **disposition for every item** in
`Issues.md` and `Contention.md`. Work already landed is listed in §2 so it is not
re-done or re-listed.

**Status (2026-08-17, verification-gate pass + plan item A.7 closed):** the §8
verification gate was re-run in this repository and is green (`lake build` over the
default targets, `lake build RandomMap`, the sorry/axiom audit and the isolation
audit); this discharges the "verification gate not yet run in this repo" note of
§9. The one open plan item recorded in §9 — **A.7** of
`PLAN_LEAN_SPECIALIST_NS_FLOW.md`, the second-derivative extension `genY2` of the
Eulerian gauge generator — is now **closed** by the new `sorry`-free /
`axiom`-free module `BookProof/ChapterNavierStokesGaugeY2.lean`: the second-order
field `u_i(y) = u_i + u_{i,j} y_j + ½ u_{i,jj} y_j²` (`uField2`), the derivative
field `u_{i,j}(y)` (`uDField`), the generator
`G²_j = ∂/∂y_j − u_{i,j} ∂/∂u_i − u_{i,jj} ∂/∂u_{i,j}` (`genY2`), the annihilation
theorems (`genY2_uField2`, `genY2_uDField`), the gauge invariance of the symbol
built from the fields (`genY2_nsSymbol2`, `genX_nsSymbol2`) and its `y = 0`
collapse (`setYZero_nsSymbol2`), the sharpness statements
(`genY_uField2_ne_zero`, `genY2_uField_ne_zero`,
`genY2_uField2_perturbed_ne_zero`) and the first-class (abelian) property
(`genY2_genY2_commute`, `genX_genY2_commute`), together with the honest
non-commutation of the *mixed* bracket (`genY_genY2_not_commute`). The module is
registered in `BookProof.lean`, certified in `ChapterRoadmapAudit.lean` and cited
from `Book/FreeField.lean`. The cosmetic A.1 name was also closed:
`ChapterF1.positionOp` is now an alias of `fieldPhi = creat + annih`.

**Status (2026-08-13, maintenance + analytic layer pass):** the §8 verification gate
was re-run and is green (`lake build` over the default targets, `lake build
RandomMap`, `./patches/build-book.sh`, `./patches/check-katex.sh`, the sorry/axiom
audit and the isolation audit). No plan item was open; the pass therefore advanced
the *standing open layer* recorded in §9.3 (the infinite-dimensional analytic
realization behind §4.8) with three new `sorry`-free / `axiom`-free modules —
`BookProof/ChapterContinuityUnitaryInfinite.lean` (the dynamics-based unitary as
bounded operators on `ℓ²(ℤ)`, with countably additive Born recovery),
`BookProof/ChapterBornMeasure.lean` (`P(B) = ∫_B |Ψ|² dμ` as a genuine probability
*measure* on an arbitrary measure space, for the evolved state of any bounded
self-adjoint generator) and `BookProof/ChapterUnboundedPosition.lean` (the lattice
position operator: densely defined, symmetric, and provably unbounded) — all
registered in `BookProof.lean`, certified in `ChapterRoadmapAudit.lean` and cited
from `Book/ConditionalUnitary.lean` and the `Book/ProofPlans.lean` §E boundary. A
second wave the same day took `ChapterUnboundedPosition` past symmetry: the maximal
multiplication operator on `ℓ²(ℤ)` is proved **self-adjoint**
(`adjointDomain_eq_mulDomain`, `adjoint_eq_mulOp` — the adjoint domain is exactly
the natural domain, and the adjoint acts by the same multiplication), and it
**generates its unitary group** (`phaseUnitary`, a `LinearIsometryEquiv`, with
`phaseUnitary_zero`/`phaseUnitary_add` the one-parameter group law,
`tendsto_phaseUnitary` strong continuity at `0` for every state with no domain
hypothesis, and `tendsto_slope_phaseUnitary` Stone's relation `dU/dt|₀ = iA` in
`ℓ²(ℤ)` on the natural domain).  What is still open is that package for unbounded
operators that are *not* multiplication operators in the ambient basis (the
continuum Laplacian), i.e. Stone's theorem in full generality.
The executable bits on
`patches/*.sh` were restored in git (they had reverted to mode 644, which broke
`./patches/build-book.sh`).

**Status (2026-08-12, final pass):** the last two formalization targets are now
closed — `weakValue` (§4.7, `BookProof/ChapterWeakValue.lean`) and
`continuityUnitary` (§4.8, `BookProof/ChapterContinuityUnitary.lean`) are proved,
`sorry`-free and `axiom`-free, registered in `BookProof.lean`, certified in
`BookProof/ChapterRoadmapAudit.lean`, and cited from `Book/DoubleSlit.lean` and
`Book/ConditionalUnitary.lean`; the `Book/ProofPlans.lean` appendix §D/§E now record
them as PROVED. The keep-or-delete decision on `Book/Trivial.lean` (§7) is settled:
**keep** (see §7). No plan item remains open.

**Status (2026-08-12):** the default build (`lake build`: `BookProof`, `Book`,
`Singularity`), `lake build RandomMap`, `lake build book` + `lake exe book` +
`./patches/postprocess-html.sh`, and the `#print axioms` audit are all green with
no in-scope warnings. `BookProof/` is `sorry`-free / `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`); every `Book/*.lean` chapter is included in
`Book.lean` (35 `{include}`s, 36 chapter files; `Book/Trivial.lean` is unused
scaffolding and is not `{include}`d). Of the two historical
mathematical gaps, **both GAP-1 (2026-08-10) and GAP-2 (2026-08-12) are now
CLOSED** (§3); no `BookProof/` module is left unproved and none remains to be
`#check`-ed from `Book/`. The remaining work is the two medium-value
formalization targets `weakValue` (§4.7) and `continuityUnitary` (§4.8), and the
keep-or-delete decision on `Book/Trivial.lean` (§7). The Issues.md doc refresh is
done (chapter count 35/36 and §1 default-targets wording).

---

## 1. Mandatory commands (do not skip)

```bash
export PATH="/home/leo/.elan/bin:$PATH"
cd /home/leo/Projects/timepiece   # repository root (BOOK_PROOF_PLAN.md's /media/… path is stale)

lake build               # default targets: BookProof + Book + Singularity
lake build RandomMap
lake build book
./patches/build-book.sh  # ALWAYS use this wrapper: patches → build → render → postprocess + asserts
                         # NEVER bare `lake exe book` — it skips the <base>-removal step.
```

Reserve `lake build` and `lake build book` for the end of a pass; `lake serve` is
the day-to-day tool. Verify candidate Mathlib names with
`lake env lean --stdin <<< '#check <name>'` before relying on them.

**Invariants that must hold after any change:**
- `grep -rn "sorry" BookProof/ PnpProof/ Singularity/ RandomMap/ UsedRoute/` shows
  only the intentional `UnusedRoute/SchoenfeldPRA.lean:163,178` (and the
  historical `UnusedRoute/Legacy.lean`, `UnusedRoute/RcpEuler.lean` sorries, which
  are quarantined, not default-reachable).
- `grep -rn "^axiom" BookProof/ PnpProof/` is empty.
- No `BookProof/` file imports `PnpProof`, `UnusedRoute`, or `UsedRoute`;
  `grep -rn "import UnusedRoute" RandomMap/` is empty.
- After a fresh clone / `lake update`, run `./patches/apply-verso-patches.sh`
  (`.lake/` is gitignored; the two Verso patches must be re-applied).

---

## 2. Already done (do not redo)

- **Book build pipeline hardened (2026-08-10, this session).** Root cause of the
  non-portable PDF bookmarks: Verso emits `<base href="./">`, so the browser
  resolves `#fragment` ToC links against an absolute `file://` location and a
  printed PDF gets browser-opening bookmarks. `./patches/build-book.sh` now runs
  the patches, the build, the render, `postprocess-html.sh` (removes the base,
  the redirect, the `find/?domain` permalinks, injects screen-only ToC CSS/JS) and
  **asserts** `no <base>` + fragment links. `AGENTS.md` documents it as the only
  supported build path. Current `_out/html-single/index.html` verified clean
  (base count 0, redirect 0, permalinks 0, 316 fragment links with 0 missing
  targets).
- **`BookProof` coherence (2026-07→08).** Every wave of
  `PLAN_LEAN_SPECIALIST_COHERENT.md` landed — Parts A–G plus all attention-layer,
  information-theoretic, control-layer, soft-maximum/circuit and
  decoding/locality packages (≈40 new `Chapter*` files, all registered in
  `BookProof.lean`, certified in `BookProof/ChapterRoadmapAudit.lean`,
  `#check`-ed in `Book/CoherentState.lean`, all `sorry`-free/`axiom`-free).
- **`tailSplitEquiv_map`** and **`mehler_unique_by_finite_marginals`** proved
  (`ChapterSolovayCoordinates.lean`, `ChapterMehlerUniqueness.lean`); the Solovay
  `sorry` is closed.
- **`ChapterSelectingEvents` hardened:** the `True`-placeholders were replaced
  with real conclusions — `exists_regular_conditional_probability` (via
  `condDistrib`/`compProd_map_condDistrib`), `vonNeumann_abelian_classification_typeI`
  (the genuine `Iₙ` case), `exists_continuous_atomic_decomposition`,
  `selecting_events_not_rewriting_history`; the two `axiom : True` lines were
  removed (kept commented-out for the record).
- **Part G isolation closed:** the RH spine moved to `UnusedRoute/`;
  `RandomMap/RandomMap2.lean` imports `BookProof.PhysMehler`, not
  `UnusedRoute.SchoenfeldPRA`; `RcpRandomMap2Bridge.lean` and
  `RandomMap2Phase7.lean` moved; `grep -rn "import UnusedRoute" RandomMap/` empty;
  the promoted `Phys*` modules (`PhysMeasureBasis`, `PhysFunctionalAnalysis`,
  `PhysHSGaussian`, `PhysMehler`) are line-length-clean.
- **Priority 1/2 of `BOOK_PROOF_PLAN.md`** (ODE honesty + PA-free completion):
  all DONE; Priority 4 (26-`{include}` Verso limit) DONE via
  `patches/verso-0001-annotate-subparts.patch`; Priority 5 (honesty-flag refresh)
  DONE; Priority 7 (`book.tex` claims) DONE; Priority 8 (Issues-derived) DONE.
- **GAP-2 closed (2026-08-12).** The abelian von Neumann exhaustiveness wave
  landed: `ChapterLinftyMaximalAbelian`, `ChapterAbelianAtomicCondensation`,
  `ChapterTensorCompleteness`, `ChapterAbelianGelfandModel`,
  `ChapterSpectralMultiplication`, `ChapterSpectralCommutant`,
  `ChapterCyclicDecomposition`, `ChapterCyclicDirectSum`, `ChapterSpectralDirectSum`,
  `ChapterAbelianCyclicModel`, `ChapterAbelianCyclicCommutant`, `ChapterAbelianDirectSum`,
  `ChapterMeasureAtomicDiffuse`, `ChapterDiffuseCdfModel`, `ChapterDiffuseUnitaryModel`,
  `ChapterAtomicDiagonalModel`, `ChapterLpRestrictSplit`, `ChapterLpScaleMeasure`,
  `ChapterAbelianClassificationList`, `ChapterStandardBorelClassification`,
  `ChapterSeparableSpectrum`, `ChapterSeparableL2Model` — all `sorry`-free/`axiom`-free,
  registered in `BookProof.lean`, certified in `ChapterRoadmapAudit.lean`,
  `#check`-ed in `Book/NullMeasure.lean`. The metrizability residue is removed; only a
  nonseparably *acting* algebra is outside the statement.
- **`BookProof` §4 and GAP-1 (2026-08-08→12).** `ChapterCoherentThermalFidelity`
  (displaced-thermal fidelity → `thermalTemperature_eq_fidelity_width_sub_coherent_half`,
  closing **GAP-1**), `ChapterSolovayTailDimension`, `ChapterSolovaySeparableExistence`,
  `ChapterSolovayHilbertTensor`, `ChapterSolovayCrossDim` — closing §4.1–4.6. The
  finite algebraic core (`ChapterThermalTemperatureCore`) is also proved.
- **Verso integrated** on v4.28.0; single-page output decided and locked
  (`emitHtmlSingle := .immediately`, `emitHtmlMulti := .no`).
- **Book prose coverage of §4.7/§4.8 landed (2026-08-12).** The *prose* halves of
  the two BookProof targets are written up and `#check`-ed from the book: the "Weak
  Measurements / weak values" section of `Book/DoubleSlit.lean` (weak-value ratio,
  ABL core in `ChapterTrajectory`, see Proof-Plans appendix §D) and the "Less
  Arbitrary Construction / dynamics-based unitary" sections of
  `Book/ConditionalUnitary.lean` (continuity Hamiltonian `H = ½(p̂·v + v·p̂)`,
  tensor-product identification, Born-rule recovery; Proof-Plans appendix §E).
  The BookProof modules are now **DONE** as well (see §4.7/§4.8 and §9): only the
  unbounded *continuum* generator (Stone's theorem in full generality) is outside
  the formalized statement.
- **Weak measurements / weak values proved (2026-08-12).** `ChapterWeakValue`
  formalizes `⟨A⟩_w = ⟨f|A|i⟩/⟨f|i⟩` on `Fin n → ℂ` (`weakValue_wellDefined`,
  `weakValue_diag`, `weakValue_linear`, `weakValue_proj_sum`,
  `jointProb_eq_normSq_weakNumerator`, `condProb_eq_weakNumerator_ratio`,
  `dslit_weakValue`), closing §4.7. See §4.7 and Proof-Plans appendix §D.
- **Dynamics-based unitary proved (2026-08-12).** `ChapterContinuityUnitary`
  builds `H = ½(p·v + v·p)` on the cyclic lattice, the unitary `e^{iHt}`, the
  Born-rule recovery `bornRecover` and the capstone `condProb_of_continuity`,
  closing §4.8. See §4.8 and Proof-Plans appendix §E.
- **Analytic layer wave (2026-08-13).** `ChapterContinuityUnitaryInfinite` runs
  the dynamics-based construction on `ℓ²(ℤ)` with bounded operators
  (`momentum_isSelfAdjoint`, `velocityOp_isSelfAdjoint`,
  `continuityHamiltonian_isSelfAdjoint`, `continuityUnitary_unitary`,
  `bornRecover_tsum_univ`, `condProb_of_continuity_infinite`);
  `ChapterBornMeasure` proves `P(B) = ∫_B |Ψ|² dμ` is a probability measure on any
  measure space (`bornMeasure`, `isProbabilityMeasure_bornMeasure`,
  `bornMeasure_absolutelyContinuous`, `condProb_of_bounded_dynamics`);
  `ChapterUnboundedPosition` proves the lattice position operator is densely
  defined, symmetric and genuinely unbounded, then self-adjoint
  (`adjointDomain_eq_mulDomain`, `adjoint_eq_mulOp`) and generates its unitary
  group with Stone's relation (`phaseUnitary`, `tendsto_phaseUnitary`,
  `tendsto_slope_phaseUnitary`); `ChapterUnitaryTransport` carries the whole
  package through any unitary change of Hilbert space
  (`transport_isSelfAdjointOn`, `tendsto_transportUnitary`,
  `tendsto_slope_transportUnitary`, `transported_position_isSelfAdjointOn`).
  What remains is the *existence* of a diagonalizing unitary for a general
  unbounded self-adjoint operator (the spectral theorem behind a continuum
  Laplacian) — a research target, not a plan item (see §9).
- **Display-math fix (2026-08-12).** Five display equations in
  `Book/FreeField.lean` and `Book/SolovayTensor.lean` wrote `$$` on its own line,
  which Verso emits as literal text + a plain `<code>` block that KaTeX never
  touches. Rewritten in the working form (`$$` immediately before the backtick);
  rebuilt book + `check-katex.sh` (1818 snippets, 0 failures). A remaining
  `Issues.md` §0b/§4 count (38/39) was refreshed to the actual 35 `{include}`s /
  36 chapter files.
- **The Navier–Stokes thread is now proved (2026-08-14→15, the
  `PLAN_LEAN_SPECIALIST_NS_FLOW.md` wave).** The whole plan landed in 27 new
  `BookProof/ChapterNavierStokes*.lean` + `ChapterFarisLavine.lean` +
  `ChapterH8*.lean` + `ChapterH9.lean` modules (registered in `BookProof.lean`),
  all `sorry`-free / `axiom`-free, `#check`-ed from the book. In dependency
  order: the **truncation** — `ChapterNavierStokesFlow` (Hermitian
  `nsHamiltonian`, polynomial of degree ≤ 3, complete unitary flow
  `nsFlow_unitary`/`nsFlow_noBlowup`, zero deficiency `nsHamiltonian_hasZeroDeficiency`),
  `ChapterNavierStokesCauchy` (unique global solution `nsCauchy_existsUnique`),
  the BRST/divergence constraint `nsBrst_nilpotent`/`nsDivergenceConstraint_resolution`,
  the Lagrangian change of variables (`volume_preservation_constraint`,
  `transformed_hamiltonian_decomposition` with positive kinetic/viscous terms);
  then the **analytic layer** — `ChapterNavierStokesEsa` (Nelson's complete-flow
  criterion `hasZeroDeficiencyOn_of_completeUnitaryFlow`, bounded-symmetric ESA on
  a proper dense domain), `ChapterNavierStokesDeficiency` (the limit-circle Jacobi
  counterexample: symmetry alone is not ESA), `ChapterNavierStokesFarisLavineLift`
  + `ChapterNavierStokesFock*` (second quantization, the comparison operator
  `n = Σπᵢ² + ΣVᵢ² + I` with `N̂ ≥ I`, the Fock-of-Fock lift where the
  form-commutator bound lifts but the operator bound does not,
  `not_forall_norm_sum_le_of_pointwise`), `ChapterNavierStokesIkebeKato`
  (maximal-domain multiplication operators: `N+1` onto, finite-mode graph cores),
  `ChapterNavierStokesMomentumEsa` (ESA of the one-particle and Fock-space
  Navier–Stokes Hamiltonian on the finite-mode core), and
  `ChapterNavierStokesHermiteFarisLavine`/`ChapterNavierStokesFockFarisLavine`/
  `ChapterNavierStokesShiftHamiltonian`/`ChapterNavierStokesFockManyMode` (the two
  Faris–Lavine inequalities **proved** for the Hamiltonian itself — relative bound
  `‖Hx‖² ≤ ½‖Nx‖² + …` and commutator bound `|⟨x,i[H,N]x⟩| ≤ c⟨x,Nx⟩` — with a
  genuinely non-vanishing commutator `fock_commForm_ne_zero`).
- **Faris–Lavine commutator criterion proved (2026-08-15h).**
  `BookProof/ChapterFarisLavine.lean` proves Theorem 1 and Corollary 1.1 of Faris
  & Lavine, *Commutators and self-adjointness of Hamiltonian operators*, CMP 35
  (1974) 39–48 — `essentiallySelfAdjointOn_of_farisLavine`,
  `essentiallySelfAdjointOn_core_of_farisLavine`, the resolvent-estimate core
  `deficiencyTrivialAt_of_farisLavine` and the sharpness refutation
  `not_farisLavine_criterion_of_relative_bound` (relative-bound-only is false,
  via the limit-circle Jacobi operator). The criterion that
  `ns_esa_of_farisLavine_dense` carried as a named hypothesis is now a proved
  theorem, and `hasZeroDeficiencyOn_of_farisLavine` delivers it in the chapter's
  own predicate.
- **SIRK nesting completed (2026-08-14→15, `PLAN_LEAN_SPECIALIST_SIRK_NESTED.md`
  + its spectral side).** `ChapterH8` proves the approximant nesting — the
  subspace tower `sirk_krylov_tower`, block compatibility `sirk_compression_block`,
  the projection identities `sirk_band_refinement(_poly/_rational)` and
  `sirk_approx_projection(_poly/_rational)`, with hypothesis-free realizations via
  orthonormal Krylov bases (`krylovOrthonormal_span`, `sirk_band_refinement_krylov`);
  `ChapterH8Bases` provides the Gram–Schmidt orthonormal Krylov bases; `ChapterH9`
  adds the spectral face — the numerical ranges nest
  `W(Bₘ) ⊆ W(Bₙ) ⊆ W(X)` (`sirk_numRange_nested_orders`, `sirk_numRange_krylov`),
  the norms nest, Ritz values and Ritz spectra nest
  (`ritz_mem_numRange(_compress)`), and the *unconditional* best-approximation
  antitone/tend-to-zero (`krylov_bestApprox_antitone`,
  `krylov_bestApprox_tendsto_zero`, no Crouzeix constant). Honest boundaries kept:
Crouzeix's inequality stays a named hypothesis; no rate; no Toeplitz–Hausdorff
   convexity; `W(Bₙ)` grows with the order so band decay comes from approximation
   quality.
- **Eulerian constraints + gauge generators landed (2026-08-16,
  `PLAN_LEAN_SPECIALIST_NS_FLOW.md` Part A.5 + Part E.3).** Two new modules,
  `ChapterNavierStokesEulerian.lean` and `ChapterNavierStokesGaugeY.lean`
  (registered in `BookProof.lean`, cited from `Book/FreeField.lean`), both
  `sorry`-free / `axiom`-free, completing the Eulerian side of the
  derivatives-as-fields construction:
  - `ChapterNavierStokesEulerian` — the Eulerian counterpart of the Lagrangian
    constraints: the Eulerian field collapse `u_evaluates_to_value`
    (`u_i(X) = u_i + u_{i,j}(X_j − x_j)` → `u_i` on position eigenstates), the
    full momentum CCR family `eulerian_momentum_constraint` (`[u_j, π^k] =
    iδ^k_j` plus the derivative-mode CCRs) and `eulerian_momentum_dual`, the
    gauge-generator derivative relations `derivativeField_relates_to_field`
    (`u_{i,j} = ∂_j u_i`), `derivativeField_second`, `derivativeField_consistency`
    (Clairaut), the initial-condition-imposed `eulerian_divergence_constraint`
    (`u_{3,3}` substitution) with non-empty witness
    `cyclicShear_divergence_free` — and the correction to optional E.3:
    `nsBrst_not_hermitian` (the BRST charge is **not** Hermitian when the
    divergence is non-zero; the honest Hermitian statement is the symmetrized
    packaging `nsBrst_symmetrization_hermitian`).
  - `ChapterNavierStokesGaugeY` — the second-coordinate refinement: the field in
    the Hamiltonian is `u_i(y) = u_i + u_{i,j}y_j` (`uField`), with two gauge
    generators — `genX = ∂/∂x_j` (the standard momentum) and
    `genY = ∂/∂y_j − u_{i,j}∂/∂u_i` (the generator built from the derivatives of
    `u_i`). Both annihilate the field and the NS symbol, commute (abelian, hence
    first class), the coefficient `u_{i,j}` is the *only* admissible one
    (`genY_uField_perturbed_ne_zero`), and at the initial state `y = 0` the field
    collapses to `u_i` and the Hamiltonian acts as the ordinary NS one
    (`setYZero_uField`, `hamiltonianOp_apply_of_y_zero`).

---

## 3. The two documented mathematical gaps (BookProof, high value)

**Update (2026-08-12): both historical gaps are now CLOSED.**

- **GAP-1 closed** (2026-08-10) by `ChapterCoherentThermalFidelity` — the zero-point
  half of `τ = n̄ + ½` is derived from the coherent-state overlap, not postulated.
- **GAP-2 closed** (2026-08-12) by the abelian-classification wave — the five-type
  exhaustiveness is established; only a nonseparably *acting* algebra is outside
  the statement.

Both were **documented gaps, not `sorry`s** — and remain so. The sections below
record the history and the explicit closure; do not reopen them.

### GAP-1 — Physical derivation of `τ = n̄ + ½` (Part A.4 / F.4)

Status: **CLOSED (2026-08-10).** The finite algebraic core was proved first
(`ChapterThermalTemperatureCore.lean`: `geometricOccupancy_mean`,
`geometricOccupancy_variance`, `half_integer_floor`, `thermal_temperature_eq_mean_half`).
The physical derivation is `ChapterCoherentThermalFidelity.lean`:

- `coherentThermalFidelity nbar lam = ∑ₙ |⟨β|n⟩|²·Pr_th(n)` — thermal state vs
  coherent state in Fock coordinates;
- `coherentThermalFidelity_eq` — collapses to `exp(−λ/(n̄+1))/(n̄+1)`, a Gaussian of
  width `n̄ + 1`;
- `coherentThermalFidelity_vacuum_eq_fidelityC` — at `n̄ = 0` this is the coherent
  fidelity `exp(−‖q−k‖²)`, fixing the coherent-state width `coherentWidth = ½`
  (via `fidelityC_width` `½ + ½ = 1`);
- `coherentThermalFidelity_width_eq` — widths add: `n̄ + 1 = τ + ½`;
- **headline** `thermalTemperature_eq_fidelity_width_sub_coherent_half` — the width
  of the fidelity determines the temperature (`τ = w − ½`), so `τ = n̄ + ½` is *read
  off* the fidelity. The extra half is exactly the coherent-state overlap.

`sorry`-free / `axiom`-free, registered in `BookProof.lean`, `#check`-ed in
`Book/CoherentState.lean`. Recorded as CLOSED in `BookProof/STATUS.md` (wave
2026-08-10).

### GAP-2 — Exhaustiveness of the abelian von Neumann classification (Part B.4 / F.5)

Status: **CLOSED (2026-08-12).** The four concrete classes were proved first —
finite `Iₙ` (`ChapterAbelianDiagonal`), countable `ℓ∞(ℕ)`
(`ChapterAbelianDiagonalCountable`), diffuse `L∞(μ)` (`ChapterLinftyMultiplication`),
mixed atomic-plus-diffuse (`ChapterAbelianMixture`). The exhaustiveness claim —
every abelian `*`-algebra on separable `L²` is `*`-iso to one of the five standard
types — is now established (the full von Neumann theorem, out of Mathlib).

**Update (2026-08-12): essentially closed.** The condensation was carried out in
full: `ChapterLpRestrictSplit` (the `L²` splitting along a measurable set),
`ChapterLpScaleMeasure` (rescaling the measure is a unitary),
`ChapterAbelianClassificationList` (the five-type list for a Borel probability
measure on the line) and `ChapterStandardBorelClassification` (Borel-isomorphism
transport; every summand of the general abelian model realises one of the five
standard types, for a compact metrizable spectrum). All `sorry`-free / `axiom`-free.

**Update (2026-08-12, later the same day): the metrizability residue is closed.**
`ChapterSeparableSpectrum` proves that, for a compact Hausdorff spectrum,
metrizability of the spectrum is *equivalent* to separability of the algebra of
continuous functions, and discharges it for every separable commutative unital
C*-algebra via Gelfand duality.  `ChapterSeparableL2Model` then removes it outright
in the separably acting case: a separable `L²` is carried, by a countable dense
family of continuous functions, unitarily onto an `L²` over a standard Borel space,
so every abelian algebra of operators on a separable complex Hilbert space is a
countable direct sum of multiplication algebras each realising one of the five
standard types.  Both modules are `sorry`-free / `axiom`-free.  The only case now
left outside the statement is a nonseparably *acting* algebra.

Definition of done: attempt the provable condensation — e.g."every abelian,
star-closed, unital algebra on `L²` whose projections are purely atomic is
`*`-isomorphic to `ℓ∞(ℕ)` (or `Iₙ`)"; finite convex combinations reduce to the
mixture class. If out of reach, record the exact obstruction in
`BookProof/STATUS.md` — do **not** `sorry`.

---

## 4. BookProof tasks from the older plans (medium value, isolated)

**Update (2026-08-12): these are now all LANDED** — the copied wave closed every
item originally listed here. They are kept as a record only; do not redo them.

- **4.1 `tail_infinite_dimensional` (Task B2b).** DONE — `ChapterSolovayTailDimension`
  proves `¬ FiniteDimensional ℝ InnerTail` (infinite orthonormal family).
- **4.2 Hilbert-space tensor identification (Task B2, "heavier" half).** DONE —
  `ChapterSolovayHilbertTensor` gives `solovayTensorEquiv` (the Hilbert-space form
  of the tensor isomorphism, with `solovayTensorEquiv_map` / `solovayTensorUnitary`).
- **4.3 Cross-dimensional inner product (Task B5 / `BOOK_PROOF_PLAN.md` 6.6).**
  DONE — `ChapterSolovayCrossDim`: `cross_dim_embedding` (enlarging `N ↦ N + k` is
  measure-preserving) and the expectation/norm-pairing identities via
  `inner_reduces_to_head`.
- **4.4 `joint_prob_has_wavefunction` (Task D1).** DONE —
  `ChapterSolovaySeparableExistence` proves `joint_prob_has_wavefunction` and the
  product form `joint_prob_has_wavefunction_prod`.
- **4.5 `exists_separable_prob_with_arbitrary_finite_law` (Task D3).** DONE —
  `ChapterSolovaySeparableExistence` proves
  `exists_separable_prob_with_arbitrary_finite_law` (and the substrate form).
- **4.6 Disintegration via `prod_disintegrate` (Task D2).** DONE —
  `ChapterSolovaySeparableExistence` carries the explicit `prod_disintegration`
  companion (`μ = μ.fst ⊗ₘ κ`) alongside the `condDistrib` route in
  `ChapterSelectingEvents`.

All of the above are `sorry`-free / `axiom`-free, registered in `BookProof.lean`,
certified in `BookProof/ChapterRoadmapAudit.lean`, and `#check`-ed from
`Book/CoherentState.lean`, `Book/NullMeasure.lean` and `Book/SolovayTensor.lean`.

No remaining work item of this section is open.

**Addition (2026-08): weak measurements / weak values (book.tex "Reconstruction of
the trajectory"; the double-slit chapter's "Weak Measurements" section).** The
post-selection / ABL core is proved (`ChapterTrajectory`); the weak-value ratio
itself is not. Medium value, small and self-contained — a natural next target:

- **4.7 `weakValue` (ChapterWeakValue).** **DONE (2026-08-12).**
  `BookProof/ChapterWeakValue.lean` defines `ip` (the standard inner product on
  `Fin n → ℂ`) and `weakValue i f A = ip f (A *ᵥ i) / ip f i`, and proves
  `weakValue_wellDefined` + `weakValue_unique` (the ratio is the unique solution of
  `w·⟨f|i⟩ = ⟨f|A|i⟩` when `⟨f|i⟩ ≠ 0`), `weakValue_diag` and
  `weakValue_diag_isReal`, `weakValue_add`/`weakValue_smul`/`weakValue_linear`,
  `weakValue_proj`/`weakValue_proj_sum`, the ABL ties
  `jointProb_eq_normSq_weakNumerator` and `condProb_eq_weakNumerator_ratio`, and the
  double-slit capstone `dslit_weakValue`. `sorry`-free / `axiom`-free, registered in
  `BookProof.lean`, certified in `ChapterRoadmapAudit.lean`, cited from
  `Book/DoubleSlit.lean`.

- **4.8 `continuityUnitary` (ChapterContinuityUnitary).** **DONE (2026-08-12).**
  `BookProof/ChapterContinuityUnitary.lean` works on the cyclic lattice `ZMod N`
  with the symmetric-difference momentum: `continuityHamiltonian v = ½(p·v + v·p)`
  with `continuityHamiltonian_hermitian` (and
  `momentum_mul_velocityOp_not_hermitian`, showing the symmetrization is needed),
  `continuityUnitary v t = exp (i t H)` with `continuityUnitary_unitary`,
  `continuityUnitary_zero`, `continuityUnitary_add`, the Born recovery
  `bornRecover` (`_nonneg`, `_empty`, `_union`, `_mono`, `_univ`) and `bornPMF`,
  the finite tensor identification `tensorIsom`/`tensorIsom_tmul` with
  `bornRecover_product_state`, and the capstone `condProb_of_continuity`.
  `sorry`-free / `axiom`-free, registered in `BookProof.lean`, certified in
  `ChapterRoadmapAudit.lean`, cited from `Book/ConditionalUnitary.lean`. The
  infinite-dimensional analytic layer is now also proved for the bounded case and
  for the lattice position operator (§4.9); only the continuum Laplacian's
  diagonalizing unitary (Stone's theorem in full generality) remains outside.

- **4.9 The analytic layer of §4.8 (2026-08-13, DONE as bounded + lattice).**
  `ChapterContinuityUnitaryInfinite` (the construction on `ℓ²(ℤ)` with bounded
  operators), `ChapterBornMeasure` (the Born law as a probability measure on any
  measure space), `ChapterUnboundedPosition` (the lattice position operator is
  densely defined, symmetric, unbounded, then self-adjoint and generating its
  unitary group with Stone's relation) and `ChapterUnitaryTransport` (unitary
  invariance of the whole package). The open research boundary is the spectral
  theorem for a general unbounded self-adjoint operator (a continuum Laplacian):
  the *existence* of the diagonalizing unitary. See §2 and §9.

---

## 5. Issues.md — full disposition

| § | Item | Status now | Action required |
| :-- | :-- | :-- | :-- |
| 0 | verso-blueprint needs Lean ≥ v4.29.0 (project pinned v4.28.0) | **[BLOCKER]** | **Keep Verso v4.28.0 manual as the deliverable.** Adopt blueprint **only** when a toolchain exists that is *both* blueprint-compatible *and* supported by `aristotle.harmonic.fun` (see `BOOK_PROOF_PLAN.md` §3.2). Do not bump toolchain/Mathlib in this repo meanwhile. |
| 0b | Current state of this deliverable | **RESOLVED (2026-08-12)** | Issues.md §0b refreshed to the actual tree: 35 `{include}`s / 36 chapter files (`Book/Trivial.lean` unused scaffolding, not `{include}`d). Re-verify only when the chapter set next changes. |
| 1 | Transitive dependency pins (subverso/MD4Lean/plausible chosen by date) | **LOW RISK, untracked** | Leave pinned; re-derive **only** if a Verso/Mathlib upgrade is ever attempted. Do not upgrade in this repo. |
| 1 | Full `lake build BookProof` recompile integrity | **RESOLVED** | Re-run once per release cycle; the latest `lake build` is green. |
| 1 | `book` is intentionally not a default target | **RESOLVED** | `defaultTargets` is now `["BookProof", "Book", "Singularity"]`; `Issues.md` §1 records the `["PnpProof", "BookProof"]` wording as **UPDATED**. Re-verify only if `lakefile.toml` changes. |
| 2 | Curated-edition coverage table | **STALE** | The "deferred" physics chapters have since been **written up**: `GaugeSymmetry`, `PhysicalParity`, `YangMillsQuantization`, `RealRepresentations`, `DiffeomorphismsGravity`, `AlignedDeepLearning`, `GribovAmbiguity`, `ConsciousnessBayesianPrior` all exist under `Book/` and are **included** in `Book.lean`. The §6 "deferred" list should be re-marked `DONE (framing settled)` or moved to Contention dispositions. |
| 2 | Sketch proofs re-derived, not transcribed | **OPEN, editorial** | No build action; cross-check any less-standard claim against `book.tex` before publication (see Contention §7). |
| 3 | `newproof.md` layers (verified core vs philosophical claim) | **RESOLVED** | `Book/PaFreeHilbert.lean` keeps the compartments separate; no action. |
| 4 | KaTeX coverage | **OPEN, spot-check** | Spot-check matrix/`pmatrix` rendering in `_out/html-single/index.html` once; matrices were never confirmed. |
| 4 | Long `#check` types | **MOSTLY RESOLVED** | Readable prose paraphrases exist for the worst offenders; restate any remaining unwieldy `#check` as a clean `example` when a chapter is next edited. |
| 4 | Single-page, menu-free HTML decision | **DONE** | Locked in `BookMain.lean`. |
| 4 | 26-`{include}` limit | **DONE** | Verso patch `verso-0001`; re-apply after fresh clones. |
| 4 | Multi-line `**bold**` wrapping inline math | **GOTCHA (live rule)** | Keep bold-with-math on one line; re-check on any edit to a `Book/*.lean` chapter. |
| 5 | Output formats (single-page HTML; TeX/PDF disabled) | **DECIDED** | Single-page HTML is the deliverable. The PDF-bookmark fix in §2 was the PDF concern; do **not** enable `emitTeX` unless author explicitly asks. |
| 7 | Abstract measure-theoretic layer of `book.tex` §3 | **RESOLVED (2026-08-12)** | The finite core + `condDistrib` kernel was done; the abstract layer (five-type classification, `≅ L∞` commutative-von-Neumann passage, disintegration on standard Borel) is now **CLOSED** by the GAP-2 wave (§3) + §4.6. Only a nonseparably *acting* algebra is outside the statement. |
| 7 | Remaining non-deferred gaps (two) | **GAP-1 CLOSED (08-10); GAP-2 CLOSED (08-12)** | No mathematical target remains; see §3. |

---

## 6. Contention.md — full disposition

Governing rule (from `Book/Introduction.lean` and Contention's conventions): the
book is a **deliberate re-selection** ("selects the threads whose mathematics is
both self-contained and already formalized"), and nothing in `Book/` contradicts
`book.tex`. Dispositions:

| Item | Claim vs `book.tex` | Status | Action required |
| :-- | :-- | :-- | :-- |
| D1 | Intro slogan "QM is what probability theory looks like…" (drops the "(not of probability theory)" caveat) vs the caveat *preserved* in `DeterministicTransformations` | **INTERNAL TENSION** | **Resolve the internal disagreement.** Either add the caveat to `Introduction` (align with `DeterministicTransformations`) or explicitly frame the slogan as rhetoric with the caveat in a footnote that cross-references `DeterministicTransformations`. Should be a one-line edit; flag to author. |
| D2 | ODE chapter claims both blow-up problems resolved; manuscript says the second is "not completely satisfactory" | **OVERCLAIM** | Add one honesty sentence to `Book/OdeSingularity.lean` (near lines 45–48) reporting the manuscript's own caveat, mirroring the honesty-flag style used for the ODE theorems. |
| D3 | Essential self-adjointness reduced to algebraic certificate layer | **DISCLOSED** | Keep as is; ProofPlans A.1–A.2 already defer the analytic realization. |
| D4 | "most general formalism" softened to "generalizes statistical mechanics" | **DELIBERATE** | Keep. |
| D5 | Navier–Stokes existence/uniqueness thesis not carried by any chapter | **PARTIALLY ADDRESSED (2026-08-15)** | Keep the scope discipline — no theorem claims continuum NS existence/uniqueness. But `Book/FreeField.lean` now carries a full "Navier–Stokes Hamiltonian: a Complete Flow on the Truncation" section (complete unitary flow, unique global Cauchy solution, BRST constraint, Lagrangian change of variables, Faris–Lavine route), and `Book/YangMillsQuantization.lean` now has the one-line pointer to that formalized subset. |
| D6 | Weak holomorphicity weakened to strong pointwise | **DISCLOSED** | Keep; documented in the module; not imported by any chapter. |
| D7 | Arrow of time reframed from unitarity to dissipation/set theory | **DELIBERATE REFRAME** | Keep; it is the thesis of Chapters III. If the author wants the manuscript's "due to unitarity" framing, that is a prose decision, not a Lean one. |
| D8 | Consciousness thesis reduced | **NOW LARGELY RESOLVED** | A full `Book/ConsciousnessBayesianPrior.lean` chapter now exists (no-best-prior, prior dependence, null-measure). Verify it expresses "no prior / no point is special" faithfully and re-mark Contention D8 as addressed; the AI-hallucination/misalignment half stays out of scope. |
| D9 | Handwritten RH claim dropped; only the metamathematical motivation kept | **DELIBERATE** | Keep; `PaFreeHilbert` + `SolovayTensor` are the intended replacement. |
| S1–S10 | Scope selections (narrowing, not contradiction) | **DELIBERATE** | Keep. No action. |
| A1–A8 | Additions (content in `Book/` not in manuscript) | **DELIBERATE, fine** | Keep. Optionally mark them "additions per author" in the Contention doc. |

**Concrete now-actionable items: D1 and D2** (prose honesty/consistency, one-line
edits each). Everything else is already deliberate or already addressed by the
now-written chapters.

---

## 7. Hygiene residue (small, cosmetic)

- `BookProof/B1_randomMap2_axioms.lean` and `BookProof/randomMap2_axioms.lean`
  still `import` RH modules (`UnusedRoute.SchoenfeldPRA`). They are in **no build
  target**, so the default build is clean. **DONE (2026-08-12):** both now carry an
  explicit "Audit-only module (not in any build target)" docstring and are kept as
  the audit trail.
- Root `RiemannProof.lean` now `import UnusedRoute.RcpRandomMap2Bridge` (repointed
  in this wave); the §7 "repoint the import" item is **RESOLVED**.
- `patches/build-book.sh` is tracked; `patches/check-katex.sh` is tracked with the
  executable bit set (mode `100755`) — the §7 "untracked" item is **RESOLVED**.
- `SpecialFiles`: **DECIDED (2026-08-12) — keep `Book/Trivial.lean`.** It is a
  two-section scaffold used to reproduce the Verso section-count threshold; it is
  not `{include}`d, costs nothing to build, and is worth retaining as a minimal
  reproducer should the Verso patches ever need to be re-derived. The file now says
  so in its own text.
- **`UsedRoute` build repaired (2026-08-17).** `UsedRoute/TwoLimits.lean` carried no
  imports at all and `UsedRoute/SimplifiedStrategy.lean` was missing
  `UsedRoute.Basic` / `UnusedRoute.Legacy`, so `lake build UsedRoute` failed. The
  missing imports were added and `lake build UsedRoute` is now green (0 errors).
  `UsedRoute` is **not** a default target, and `RandomMap` only imports the
  sorry-free `UsedRoute.Basic` / `UsedRoute.SolovayHilbert`, so this does not affect
  the §8 gate. Residue: **26** legacy RH-route declarations still use `sorry`
  (was 33). In this wave `UsedRoute/SimplifiedStrategy.lean` went from 10 to 4:
  `σ_P_lt_one` (restated with the necessary hypothesis `2 ≤ P`; the original claim
  is false for `P ≤ 1`), `σ_P_tendsto`, `corrected_partial_sums_bounded`,
  `S_smooth_analyticAt`, `f_P_analyticOnNhd`, `eulerProd_analyticOnNhd`,
  `eulerProd_ne_zero` and `eulerProd_tendsto` are now proved. The four remaining
  ones there (`corrected_bohr_cahen_tail`, `f_P_converges_to_recip_zeta_above_one`,
  `f_P_uniform_convergence`, `simplified_euler_approx_on_ball`) are the deep
  RH-equivalent content and stay open.

---

## 8. Definition of done (whole consolidated plan)

```bash
# 1. Builds green, no in-scope warnings
lake build && lake build RandomMap
# 2. Book builds through the wrapper, invariants hold
./patches/build-book.sh     # asserts: no <base>, fragment links present
# 3. Sorry/axiom audit
grep -rn "sorry" BookProof/ PnpProof/ Singularity/ RandomMap/ UsedRoute/ | grep -v UnusedRoute
grep -rn "^axiom" BookProof/ PnpProof/    # empty
# 4. Isolation audit
grep -rn "import PnpProof" BookProof/ Book/ Singularity/ RandomMap/
grep -rn "import UnusedRoute" RandomMap/
# 5. GAP-1 / GAP-2 closures recorded in BookProof/STATUS.md (proved, no sorry)
```

No mathematical gap (§3) remains; both GAP-1 and GAP-2 are closed and their
closures are already recorded in `BookProof/STATUS.md` (waves 2026-08-10 and
2026-08-11/12).

---

## 9. Suggested attack order for the next agent

**Update (2026-08-16): every plan item is closed, and the Navier–Stokes thread has
landed including its Eulerian side.** D1/D2 prose cleanups are done, **GAP-1 is
closed** (2026-08-10, `ChapterCoherentThermalFidelity`), **GAP-2 is closed**
(2026-08-12), §4 is fully landed including §4.7/§4.8/§4.9, and the
`Book/Trivial.lean` decision (§7) is settled as *keep*. On top of that, the
2026-08-14→16 waves proved the whole Navier–Stokes thread
(`PLAN_LEAN_SPECIALIST_NS_FLOW.md`, 29 modules): the truncation has a complete
flow and unique global Cauchy solution, the Faris–Lavine commutator criterion is
**proved** (Theorem 1 + Corollary 1.1, `ChapterFarisLavine`), the two
Faris–Lavine inequalities are **proved** for the Navier–Stokes Hamiltonian itself
(Hermite/Fock/shift realizations) with a genuinely non-vanishing commutator, the
SIRK nesting plan (`PLAN_LEAN_SPECIALIST_SIRK_NESTED.md`) plus its spectral side
(`ChapterH9`) are proved, and the **Eulerian side** is now complete:
`ChapterNavierStokesEulerian` (Part A.5: the Eulerian field collapse, the
momentum CCR family, the gauge-generator derivative relations, the
initial-condition divergence constraint, and the E.3 correction — the BRST charge
is not Hermitian, `nsBrst_not_hermitian`) and `ChapterNavierStokesGaugeY` (the
second-coordinate refinement with the two gauge generators `genX`, `genY`).
No `BookProof/` module is left unproved and no module remains to be `#check`-ed
from `Book/`.

For a future pass, the remaining work is maintenance rather than mathematics:

1. Re-run the **§8 verification gate** (`lake build`, `lake build RandomMap`,
   `./patches/build-book.sh`, the sorry/axiom audit and the isolation audit) after
   any change. **Done (2026-08-17):** the gate was run in this repository on the
   copied-in waves and on the new `ChapterNavierStokesGaugeY2` module; `lake build`
   (default targets) and `lake build RandomMap` are green, the sorry/axiom and
   isolation audits are clean.
2. Keep `Issues.md` §0b in sync when the chapter set changes.
3. The infinite-dimensional analytic layer (§4.8's boundary) is largely closed: as of 2026-08-13 the bounded case is formalized on `ℓ²(ℤ)`
   (`ChapterContinuityUnitaryInfinite`), the Born law is a probability measure on an
   arbitrary measure space (`ChapterBornMeasure`), and the unbounded boundary is
   stated, exhibited, and then carried through: the maximal multiplication operator
   is proved self-adjoint and shown to generate its unitary group
   (`ChapterUnboundedPosition`: `adjointDomain_eq_mulDomain`, `adjoint_eq_mulOp`,
   `phaseUnitary`, `phaseUnitary_add`, `tendsto_phaseUnitary`,
   `tendsto_slope_phaseUnitary`). The research target that remains is the same
   package for unbounded operators that are *not* multiplication operators in the
   ambient basis — the continuum Laplacian — i.e. Stone's theorem in full
   generality; it is a research target, not a plan item.
4. The Navier–Stokes research target (also not a plan item): essential
   self-adjointness of the *continuum* Navier–Stokes generator. The named-hypothesis
   form (`ns_esa_of_farisLavine_dense`) is now backed by a **proved** Faris–Lavine
   criterion and **proved** inequalities for the Hamiltonian on the finite-mode
   core; what remains hypothetical is exactly the two inequalities for a continuum
   generator. Global existence/uniqueness for Navier–Stokes is not claimed anywhere.

### What is missing from `PLAN_LEAN_SPECIALIST_NS_FLOW.md` (record, 2026-08-16)

The plan is **executed** — every headline of Parts A–G is proved and `#check`-ed
(see the plan's Status table). What is *missing* is exactly the boundary the plan
itself drew, plus one small item and one correction:

- **The continuum ESA conclusion (the §7 research target, not a plan item).** The
  two Faris–Lavine inequalities are proved for the fiber Hamiltonian with
  `V = κu` **linear** in the field (on `L²(du)`, `π = −i∂/∂u` — a genuine
  differential operator; `ℓ²(ℕ)` is just its Hermite basis), and for the Fock /
  momentum realizations. What is *not* proved is the two inequalities for the
  **quadratic** NS symbol `A_i = u_j u_{i,j} − ν u_{i,jj}`. Both candidate routes
  are named (§7): the Lagrangian change of variables (Part B, advection →
  positive 2nd-order Laplacian) and the Eulerian derivatives-as-fields picture
  (Part A, momentum representation with the multiplication-operator comparison).
  The residual is a concrete FL *estimate* for that quadratic `A_i` (a relative
  bound + form-commutator bound) in the already-proved framework — not a
  "Sobolev/differential realization" gap, and not a research project needing new
  analytic machinery.
- **Global existence of the flow is a corollary of ESA, not a separate gap.** Once
  ESA is proved (in the Hermite basis, where `N = π² + V² + I` is diagonal and
  `H = ½(πV + Vπ)` is a concrete shift), Stone's theorem gives the complete
  unitary group `e^{-itH}` for every real `t` — global existence of the operator
  evolution, no finite-time blow-up. This is what `book.tex` §4210-4216's "the
  solution ... exists and it is unique" means; the truncation already proves it as
  `nsCauchy_existsUnique`. It is **not** an additional theorem to chase beyond
  ESA.
- **The genuinely open scope cut is the *classical* NS PDE (Contention D5).**
  Completeness of the Hilbert-space unitary flow does not by itself settle the
  Clay regularity problem (global smooth solutions of the classical NS equation),
  which is a statement about the PDE, not about the operator flow, and is not
  claimed anywhere. Recorded in `CONSOLIDATED_PLAN.md` §6 and the book's
  honest-boundary prose.
- **`PLAN_LEAN_SPECIALIST_NS_FLOW.md` A.1 `positionOp`.** CLOSED (2026-08-17): the
  alias `BookProof.ChapterF1.positionOp` now carries the plan's name (the position
  operator is realized as `ChapterF1.fieldPhi = creat + annih`, ChapterF1.lean:98).
  Nothing mathematical was missing; the name now matches.
- **The optional E.3 was corrected, not closed.** The plan's optional
  `nsBrst_hermitian : Ωᴴ = Ω` is **false** when the divergence field is non-zero;
  the Aristotle wave proved `nsBrst_not_hermitian` and the honest Hermitian
  packaging `nsBrst_symmetrization_hermitian` (`Ω + Ω†`). The plan's E.3 text
  should be read as superseded by that correction.
- **The second-coordinate `y` (GaugeY, plan A.6) and its second-derivative
  extension (plan A.7) are both CLOSED (2026-08-17).** The `genX`/`genY`
  construction and the `y = 0` collapse are in `ChapterNavierStokesGaugeY.lean`
  (A.6); the extension `genY2 j = ∂/∂y_j − u_{i,j}∂/∂u_i − u_{i,jj}∂/∂u_{i,j}`
  annihilating the second-order field `u_i(y) = u_i + u_{i,j} y_j + ½ u_{i,jj}
  y_j²` is in `ChapterNavierStokesGaugeY2.lean` (A.7) — Eulerian-only (the
  Lagrangian parcel side has no such field expansion). The executed A.7 carries
  the Taylor coefficient `½` on the quadratic term (with coefficient `1` no
  generator of that shape annihilates the field), adds the derivative field
  `uDField`, the gauge-invariant symbol `nsSymbol2` and the honest mixed-bracket
  statement `genY_genY2_not_commute`.
- **Verification gate: run (2026-08-17).** `lake build` (default targets) and
  `lake build RandomMap` are green in this repository, and the sorry/axiom and
  isolation audits are clean.

None of these is a mathematical gap in the provable core: they are the recorded
boundary (continuum ESA + classical NS regularity), a closed cosmetic name (A.1),
a superseded optional item (E.3), and the closed A.6/A.7 gauge-generator items.
With the gate green and A.7 landed, `PLAN_LEAN_SPECIALIST_NS_FLOW.md` is fully
executed.
5. Pedagogical polish (small, editorial): the Eulerian/GaugeY prose in
   `Book/FreeField.lean` is in place; the plan's A.6/A.7 now carry the
   second-coordinate `y` and the second-order generator `genY2` as named plan
   items, so the plan and the proof modules are in one-to-one correspondence.

---

## 10. Quantum Gravity: the ESA of the 3D gauge-fixed Hamiltonian (candidate
route, record — not a proved Lean theorem)

The manuscript's *final, 3D gauge-fixed* gravity Hamiltonian
(`book.tex` §"Classical Hamiltonian" / §"Quantum Hamiltonian", ~8138–8310, on
`Γ^s(L²(ℝ⁸⁴×ℤ₂¹⁹)) ⊗ Γ^a(L²(ℝ⁸⁴×ℤ₂¹⁹))`, the `ℝ⁸⁴` = 4 coordinates + 16 tetrads
`e_μ^a` + their derivatives, `ℤ₂¹⁹` the diffeomorphism ghosts) contains the
**singular** kinetic terms

```
H = (1/16e) S^{ab} S_ab − (1/24e) P² + …
```

whose `1/e` denominator (with `e = det(e_i^a)`) diverges as the tetrad
determinant vanishes. This record states the *candidate route* the manuscript's
own analytic-layer pattern (the NS-FLOW wave) suggests, following the same
honesty discipline: **named theorems, never claimed Lean results.**

### 10.1 The change of variables: densitized tetrads

Perform the canonical change of variables to **densitized tetrad variables**

```
y   = √e            (= (det e_i^a)^{1/2})
ẽ_i^a = √e · e_i^a
```

Under this change the `1/e` factors of the singular kinetic terms are absorbed
into the field derivatives, and the transformed kinetic operator becomes a
**flat d'Alembertian (wave operator)** in field space:

```
H_transformed = ( 1/16 Δ_{S̃} − 1/24 ∂²/∂y² )  +  H_1  −  Ṽ(ẽ, ∂ẽ)
                └─────── flat hyperbolic H₀ ───────┘
```

The principal part `H₀` is a flat second-order hyperbolic operator; `H_1` is
first-order, and `Ṽ` a (polynomial) potential built from the densitized tetrads
and their first derivatives.

### 10.2 The ESA theorem: Strichartz

The ESA claim for `H_transformed` rests on **Strichartz's theorem** (R. S.
Strichartz, *Essential self-adjointness of powers of generators of hyperbolic
equations*, J. Funct. Anal. **13** (1973) 82–93): a second-order differential
operator whose principal part is a **flat d'Alembertian on `L²(ℝ^N)`** with a
(smooth, polynomial) potential is essentially self-adjoint, because waves
propagate at finite speed in field space. This is the hyperbolic analogue of
Sears' theorem (Reed & Simon Vol. II, Thm X.28) that Part G of the NS plan uses
for the elliptic case.

### 10.3 Honest boundary (same as the NS-FLOW wave)

- **What is provable now** is the *algebraic* content, mirroring the NS plan:
  the change of variables itself, `y = √e`, `ẽ_i^a = √e·e_i^a`; the identity
  that `1/e = (∂y/∂e)²` absorbs the singular denominator into a field
  derivative; the operator-order decomposition of `H_transformed` (2nd + 1st +
  0th); and the positive/flat character of `H₀`. None of this requires the
  continuum analytic theorem.
- **ESA in the transformed variables does NOT transfer to the original
  variables.** This is the crucial scope point. The densitized-tetrad map
  `y = √e`, `ẽ_i^a = √e·e_i^a` is a **nonlinear point transformation of the
  field configuration space**, not a Hilbert-space unitary; it changes the
  measure, the domain, and the operator itself. ESA is not invariant under such
  a map, so `H_transformed` being essentially self-adjoint says **nothing** about
  the raw `(1/16e)S² − (1/24e)P²` operator in the original tetrad variables.
  (Contrast: the NS-flow *Lagrangian* change of variables was carried by
  `hasZeroDeficiencyOn_of_linearIsometryEquiv` — a *unitary* map — so there ESA
  genuinely transferred Eulerian ⟷ Lagrangian. No such transfer exists here.)
  The honest statement is exactly what this record says: **ESA is claimed only
  for the transformed-operator route**, as the manuscript's own
  singular-to-flat change of variables is understood to be load-bearing.
- **What is recorded, not claimed**: the **Strichartz ESA conclusion** for the
  continuum `L²(ℝ⁸⁴)` operator is a named analytic theorem (like Crouzeix in
  `ChapterH4`, or the Faris–Lavine inequalities for the NS continuum). The
  project's ODE chapter's `ẋ = x²` warning applies here too: the *singular*
  `1/e` form shows that the *raw* tetrad operator is not even well-defined as an
  operator on a fixed domain, so the change of variables is load-bearing, not
  cosmetic.
- **Do NOT claim**: ESA of the continuum gravity operator, global existence, or
  any unitary-evolution result as a *proved Lean theorem*. The book's own
  existence/uniqueness claims for gravity are in the same scope-cut class as
  Contention D5 for NS.
- **Suggested next step (a plan item, like the NS waves)**: a
  `PLAN_LEAN_SPECIALIST_QG_FLOW.md` in the NS-FLOW style — Part A (the
  densitized change of variables `√e`, `√e·e_i^a` and the `1/e = (∂y/∂e)²`
  identity), Part B (the flat d'Alembertian principal part and the operator
  decomposition), Part C (the finite truncation on `Fin N` modes with its
  complete unitary flow), Part D (Strichartz/Sears as a named hypothesis, never
  an axiom, exactly as `ns_esa_of_farisLavine` is named in the NS plan). Reuse
  the `Singularity/ChangeOfVars.lean` reciprocal/logarithmic-map pattern and the
  `DiffeomorphismsGravity` book chapter.

### 10.4 The three-theorem toolbox (record)

The manuscript's analytic-layer conclusions draw on three named theorems, all
recorded in this project's honesty style:

| Theorem | Reference | Use in this manuscript |
| :-- | :-- | :-- |
| Strichartz | Strichartz, J. Funct. Anal. 13 (1973) 82–93 | flat d'Alembertian principal part ⟹ ESA (hyperbolic kinetic term, incl. the gravity `H₀`) |
| Sears / Reed–Simon X.28 | Sears, Canad. J. Math. 3 (1951); Reed & Simon Vol. II Thm X.28 | `−Δ + V` with `V ≥ −c|x|² − d` ⟹ ESA (elliptic/quadratic-growth case, NS Part G) |
| Faris–Lavine | Faris & Lavine, CMP 35 (1974) 39–48, Cor. 1.1 | comparison-operator commutator criterion (proved in `ChapterFarisLavine`, NS Part G) |

None of these is an `axiom` in `BookProof/`; each enters as a named theorem with
a citation docstring when a plan requires it.
