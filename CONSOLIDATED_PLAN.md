# CONSOLIDATED_PLAN.md — The Single Plan

One plan that supersedes the per-thread plans for **future work**. It (1) collects
everything that is still **open** from `BOOK_PROOF_PLAN.md`,
`PLAN_LEAN_SPECIALIST_UNPROVED.md`, `SPECIALIST_PLAN_REMAINING.md`,
`PLAN_LEAN_SPECIALIST_COHERENT.md`, `PLAN_A_BOOK_FORMALIZATION.md`,
`PLAN_B_PROSE_VERIFICATION.md`, `SINGULARITY_DETECTION_PLAN.md` and
`PLAN_A_EXECUTION_REPORT.md`, and (2) gives a **disposition for every item** in
`Issues.md` and `Contention.md`. Work already landed is listed in §2 so it is not
re-done or re-listed.

**Status (2026-08-18c, the non-commuting mixed case):**
`BookProof/ChapterHarmonicOscillatorEsa.lean` (`sorry`-free / `axiom`-free,
registered in `BookProof.lean`, certified in `BookProof/ChapterRoadmapAudit.lean`)
closes the gap left by the wave below — a differential kinetic term plus a
non-commuting unbounded polynomial potential — in the elliptic normalization:
the harmonic oscillator `-d²/dx² + x²/4` is essentially self-adjoint on the
Hermite core of `L²(ℝ)` (`harmonicOsc_essentiallySelfAdjoint`), is symmetric there
(`harmonicOsc_symmetric`) and is genuinely unbounded (`harmonicOsc_not_bounded`).
The substance is `harmonicOscOp_apply_eq_differential`, identifying the diagonal
operator with eigenvalues `n + ½` with the differential expression
`x ↦ -ψ''(x) + (x²/4) ψ(x)` on the Hermite basis (Mathlib's `deriv`), on top of
`hermiteC_oscillator`.  The hyperbolic mixture, with the sign correction recorded
below, remains the open boundary.  Details: `STRICHARTZ_WAVE_ESA.md`.

**Status (2026-08-18b, §9.5 unbounded-potential item executed as far as it is
true):** `BookProof/ChapterWaveUnboundedPotential.lean` (`sorry`-free /
`axiom`-free, registered in `BookProof.lean`, certified in
`BookProof/ChapterRoadmapAudit.lean`) carries out steps (a) and (b) of the
localization plan of §9.5 and closes both *commuting* halves of the problem with
unbounded coefficients: an arbitrary real potential of temperate growth — every
polynomial, unbounded and with no semiboundedness assumption — is essentially
self-adjoint on the Schwartz core (`potentialOp_essentiallySelfAdjoint`,
`polynomialPotential_essentiallySelfAdjoint`), and dually every real *symbol* of
temperate growth gives an essentially self-adjoint Fourier multiplier
(`multiplierOp_essentiallySelfAdjoint`, with `constCoeffOp_eq_multiplierOp`
showing this generalizes the quadratic-symbol theorem of
`ChapterStrichartzWave`).  For the mixture, `□ + W` is proved to be a well-defined
symmetric operator on the Schwartz core for every real `W` of temperate growth
(`wave_add_potentialOp_symmetric`), and essentially self-adjoint for every
truncation `W_R` of it (`wave_add_truncatedPotential_essentiallySelfAdjoint`).
Step (c) is **not** taken, and the plan item's hypothesis needs a **sign
correction**: with this project's convention `□ = -∂_t² + Δ_x`, a potential
bounded *below* makes the time-Fourier fibre `-Δ_x - W` unbounded below (for
`W = x⁴` the limit-circle operator `-d²/dx² - x⁴`, deficiency indices `(2,2)` — a
classical fact quoted from the literature, not formalized here), so essential
self-adjointness genuinely fails; the closable hypothesis is `W` bounded
*above* by a quadratic here, equivalently `W` bounded below in the
opposite-signature convention `□ = ∂_t² - Δ_x` of the physics literature.  Details:
`STRICHARTZ_WAVE_ESA.md`; the wave is cited from `Book/DiffeomorphismsGravity.lean`.

**Status (2026-08-19, §11.4 + Part F closed):** the two plan items of §11.4 (the
unbounded Friedrichs existence theorem and the continuum-realization decision)
are executed by `BookProof/ChapterFriedrichsExtension.lean`; see §9 item 6 and
the update at the end of §11.4.  The field-space realization is now **executed,
not just well-defined**: `BookProof/ChapterHermiteProductCore.lean` and
`BookProof/ChapterYangMillsHermite.lean` build the product Hermite (Gauss–
polynomial) core of `L²(ℝ⁹⁹)` and define the coordinate/momentum/magnetic-field
operators, the Weyl ordering (`[A_j, π_j] = i`) and the positive sum-of-squares
Hamiltonian on it, instantiating the Friedrichs + Hashimoto theorems; the
second quantization on the finite-occupation states is executed in
`BookProof/ChapterFockSecondQuantization.lean`.  See the closing updates of
§11.3/§11.4 and `PLAN_LEAN_SPECIALIST_QYM_FLOW.md` Part F.

**Status (2026-08-17, QG + QYM plan items executed):** the two "suggested next
step" plan items of §10.3 and §11.3 are now **closed**.  Both are written up as
plans in the NS-FLOW style — `PLAN_LEAN_SPECIALIST_QG_FLOW.md` and
`PLAN_LEAN_SPECIALIST_QYM_FLOW.md` — and executed by two new `sorry`-free /
`axiom`-free modules, registered in `BookProof.lean`, certified in
`BookProof/ChapterRoadmapAudit.lean` and cited from the book:

* `BookProof/ChapterQuantumGravityDensitized.lean` (§10, cited from
  `Book/DiffeomorphismsGravity.lean`) — Part A the densitized change of variables
  (`densY`, `densTetrad`, the absorption identity `1/e = 4(∂y/∂e)²`
  — note the factor `4`, which §10.1's prose omits — the densitized form of the two
  singular kinetic terms, and `tendsto_inv_det_atTop` vs `tendsto_densY_zero`);
  Part B the flat principal part (`qgSymbol`, `qgSymbol_eq_metric_form`,
  `qgMetric_det_ne_zero`, `qgSymbol_indefinite` — hyperbolic, not elliptic — and
  `christoffel_eq_zero_of_const`, the vanishing of the connection corrections for a
  constant field-space metric, plus the operator-order decomposition
  `qgFullSymbol_scaling`); Part C the Hermite-basis realization, where the
  operator is unbounded, essentially self-adjoint on its maximal domain and has
  trivial deficiency at *every* non-real `z`
  (`qgModeHamiltonian_essentiallySelfAdjoint`,
  `qgModeHamiltonian_deficiencyTrivialAt`, `qgModeHamiltonian_not_bounded`); and
  Part D Strichartz as a **named hypothesis, never an axiom**
  (`strichartz_esa_of_finiteSpeed`, shown satisfiable by
  `strichartz_finiteSpeed_satisfiable`), the Faris–Lavine alternative
   (`qg_esa_of_farisLavine`) and the half-density transfer step
   (`densitized_hasZeroDeficiencyOn_transfer`).  **2026-08-19:** the book's full
   quantum Hilbert space and its 3D gauge-fixed operator are the next targets,
   written up as Part E (second quantization on the graded Fock space
   `Γˢ⊗Γᵃ`, fermionic CAR half) and Part F (concrete densitized/Weyl-ordered
   field-space Hamiltonian + BRST charge `G`) of
   `PLAN_LEAN_SPECIALIST_QG_FLOW.md`.
* `BookProof/ChapterYangMillsFriedrichs.lean` (§11, cited from
  `Book/YangMillsQuantization.lean`) — Part A the densely-defined Weyl-gauge
  Hamiltonian (`weylOpDom`, `weylOpDom_symmetricOn`, `weylOpDom_quadForm` the sum
  of squares, `weylOpDom_quadForm_nonneg` semi-boundedness); Part B the quadratic
  form and its closure (`formInner`, `formNormSq_ge_normSq`, Cauchy–Schwarz
  `re_formInner_sq_le` and the headline `form_closable`, applied as
  `weylForm_closable`); Part C the Friedrichs extension as a **named theorem**
  (`IsPositiveSelfAdjointExtension`, `friedrichs_extension_of_semibounded`,
  satisfiability `friedrichs_hypothesis_satisfiable`, and the conditional
  conclusion `weyl_friedrichs_extension`); Part D the proved SIRK supporting facts
  (`weylKrylov_bestApprox_antitone`, `weylKrylov_bestApprox_tendsto_zero`).  The
  §11.2 uniqueness sentence ("the infinite Hashimoto limit selects the Friedrichs
  extension") stays a **conjecture recorded in prose**: it is not written as a Lean
  statement, because it needs the limit operator of the Krylov flag, which is not
  constructed.

The honest boundaries of §10.3 and §11.3 are unchanged: nothing is claimed about
essential self-adjointness of the continuum gravity operator, about
self-adjointness of the continuum Yang–Mills operator (which is, however,
*well-defined on the Hermite core* — see the 2026-08-18 refinement in
§11.3/§11.4), about the mass gap, or about global existence in either theory.

After this wave the full §8 gate was re-run and is green: `lake build` over the
default targets (no warnings), `lake build RandomMap`, `./patches/build-book.sh`
(the `<base>`-removal and fragment-link assertions pass, and the new QG/QYM
citations render), the sorry/axiom audit (`BookProof/`, `PnpProof/`,
`Singularity/`, `RandomMap/` are `sorry`-free and `axiom`-free) and the isolation
audit (no `import PnpProof` / `import UnusedRoute` in the in-scope libraries).

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
- **Quantum Gravity + Quantum Yang–Mills plan items executed, plus the
  Hashimoto/Galerkin–Friedrichs extension (2026-08-17).** The §10.3 / §11.3
  "suggested next step" items are written up as `PLAN_LEAN_SPECIALIST_QG_FLOW.md`
  and `PLAN_LEAN_SPECIALIST_QYM_FLOW.md` and executed by new `sorry`-free /
  `axiom`-free modules (see the leading Status block for the full name-by-name
  accounting). Three further modules extend the Hashimoto/Galerkin machinery that
  backs the QYM Friedrichs route:
  - `ChapterHermiteGalerkinFriedrichs.lean` — a Galerkin/Rayleigh–Ritz truncation
    in a complete (Hermite) basis converges to the Friedrichs (energy-form)
    extension; `galerkinCompression`, `ritzInf_antitone`,
    `ritzInf_tendsto_domainInf`, `galerkinCompression_tendsto`, strong resolvent
    convergence `galerkinResolvent_tendsto`, `positive_selfadjoint_extension_unique`
    (Hellinger–Toeplitz + density), headline `hermiteGalerkin_selects_friedrichs`.
    The bounded case is discharged (`finiteModeRestrict_selects_operator`); the
    unbounded non-ESA case is not claimed. Doc-map: `HERMITE_GALERKIN_FRIEDRICHS.md`.
  - `ChapterHashimotoShiftInvert.lean` — the shift-invert trick frees the
    Galerkin–Friedrichs theory of its boundedness hypothesis: for a positive
    Hamiltonian `H`, `‖(H+γ)x‖ ≥ γ‖x‖` makes `R = (H+γ)⁻¹` bounded (`‖R‖ ≤ 1/γ`)
    however unbounded `H` is; `R` determines `H` (`shiftInvert_determines`), and
    `hashimoto_shiftInvert_selects_friedrichs` reaches unbounded Hamiltonians, with
    the number operator on `ℓ²(ℕ,ℂ)` as the genuinely unbounded example.
  - `ChapterHashimotoComplexShifts.lean` — the same theory for the complex, non-real
    shifts of the Hashimoto–Nodera Shift-invert Rational Krylov method: `|Im γ|`
    alone bounds `‖(γ−A)x‖` (no positivity), the resolvent `X = (γI−A)⁻¹` has
    `‖X‖ ≤ 1/|Im γ|`, the resolvent identity and rational-Krylov structure
    (`shiftInvertC_resolvent_identity`, `shiftInvertC_commute`), and
    `hashimoto_multishift_selects_friedrichs`. Doc-map: `HASHIMOTO_COMPLEX_SHIFTS.md`.
  All are registered in `BookProof.lean`, certified in
  `ChapterRoadmapAudit.lean` (`#print axioms`, only `propext`,
  `Classical.choice`, `Quot.sound`), and cited from
  `Book/DiffeomorphismsGravity.lean` and `Book/YangMillsQuantization.lean`.
- **Strichartz wave-operator ESA + Hermite core + unbounded Friedrichs (2026-08-18,
  the "wave" of §11.4 items 1–2 and the QG Strichartz step).** Seven new modules,
  all `sorry`-free / `axiom`-free, registered in `BookProof.lean` and certified in
  `ChapterRoadmapAudit.lean`:
  - `ChapterStrichartzWave` — `□ = −∂_t² + Δ_x` plus a real constant is essentially
    self-adjoint on the Schwartz core of `L²(ℝ^{1+n})`; all constant-coefficient
    real-symbol operators too (`constCoeffOp_essentiallySelfAdjoint`), by the
    Fourier/multiplier argument (Plancherel + real symbol), with the smooth cut-off
    lemma `exists_smooth_cutoff` as the first ingredient of the general energy
    argument.
  - `ChapterKatoRellichDeficiency` — bounded symmetric perturbations preserve ESA,
    from scratch in the deficiency formulation (explicit Neumann series, no
    closure/spectral theory): `essentiallySelfAdjointOn_add_bounded`.
  - `ChapterWaveBoundedPotential` — `□ + V` is ESA on the Schwartz core for every
    essentially bounded real `V`.
  - `ChapterHermiteFunctions` — the genuine Hermite orthonormal basis of `L²(ℝ)`
    (`hermiteBasis`, completeness via Fourier uniqueness, `hermiteFun_oscillator`).
  - `ChapterStrichartzHermiteQG` — the Hermite core (finite combinations of Hermite
    functions, dense), diagonal operators on it with real symbol (ESA on the core,
    trivial deficiency at every non-real `z`, unbounded), the harmonic oscillator,
    and the 3D gauge-fixed QG mode Hamiltonian
    `qg3D_essentiallySelfAdjoint_on_hermiteCore` (now realized on `L²(ℝ)`, not
    abstractly on `ℓ²(ℕ)`).
  - `ChapterFriedrichsExtension` — the **Friedrichs extension theorem with no
    boundedness hypothesis** (`friedrichs_extension_exists`): the form inner
    product, its completion `FormSpace`, injectivity of the extension
    (`formExt_injective`, the closability step), Riesz representation of
    `(H+1)⁻¹`, and `A = S⁻¹ − 1`. `friedrichs_hypothesis_holds` retires the named
    hypothesis of `friedrichs_extension_of_semibounded`;
    `weyl_friedrichs_extension_unconditional` gives the Weyl-gauge conclusion;
    `friedrichs_hashimoto_selects` / `weyl_hashimoto_selects_friedrichs` combine it
    with shift-invert (the Hashimoto/SIRK limit selects the constructed extension,
    unbounded), and `unbounded_friedrichs_example` (A eₙ = n·eₙ) shows it is not
    vacuous. **This closes §11.4 items 1 and 2** (item 2 settled in favour of the
    occupation-number/Hermite realization, Part E of
    `PLAN_LEAN_SPECIALIST_QYM_FLOW.md`). Doc-maps: `STRICHARTZ_WAVE_ESA.md`,
    `HERMITE_CORE_STRICHARTZ.md`.
  - `UsedRoute` wave: `RectangleWinding` (the Cauchy-integral/rect winding-number
    core), `GaussianEuler` (+147, re-powering the rectangle strategy with Gaussian
    Euler products) and `RectangleStrategy` (+49); registered in `UsedRoute.lean`.

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
| 4 | KaTeX coverage | **RESOLVED (2026-08-18b)** | `./patches/build-book.sh` followed by `./patches/check-katex.sh` re-renders every math snippet of the built page with `throwOnError: true`: **2129 snippets, 0 failures**, matrices included. Re-run the two scripts after any chapter edit. |
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

**Update (2026-08-17): the NS thread, the QG route and the QYM route are all
executed; the remaining work is the recorded research boundaries.** D1/D2 prose
cleanups are done, **GAP-1** and **GAP-2** are closed, §4 is fully landed, the
Navier–Stokes thread (`PLAN_LEAN_SPECIALIST_NS_FLOW.md`, 29+ modules) is proved
including its Eulerian/GaugeY side, the §8 gate is green, and the two further
plan items are closed:
* **Quantum Gravity** (`PLAN_LEAN_SPECIALIST_QG_FLOW.md`, executed by
  `ChapterQuantumGravityDensitized.lean` + `ChapterQuantumGravityHalfDensity.lean`,
  cited from `Book/DiffeomorphismsGravity.lean`) — the densitized change of
  variables, the flat hyperbolic principal part, the Hermite-basis ESA (unbounded,
  trivial deficiency at every non-real `z`), Strichartz as a named hypothesis, and
  the *constructed* half-density unitary transfer.
* **Quantum Yang–Mills** (`PLAN_LEAN_SPECIALIST_QYM_FLOW.md`, executed by
  `ChapterYangMillsFriedrichs.lean` + `ChapterYangMillsFriedrichsLimit.lean`, cited
  from `Book/YangMillsQuantization.lean`) — the Weyl-gauge sum-of-squares form, its
  closability, the Friedrichs extension as a named theorem, and the Hashimoto-limit
  identification proved in the bounded regime. Plus the supporting Hashimoto
  extension (`ChapterHermiteGalerkinFriedrichs`, `ChapterHashimotoShiftInvert`,
  `ChapterHashimotoComplexShifts`).

For a future pass, the remaining work is the **recorded research boundaries** —
none of which is a plan item:

1. Re-run the **§8 verification gate** after any change. **Done (2026-08-17):**
   the gate is green in this repository on all the copied-in waves (see the
   leading Status block).  **Re-run 2026-08-18c and green:** `lake build`
   (8630 jobs), `lake build RandomMap` (8039 jobs) and `lake build UsedRoute` all
   complete with no errors; no `sorry` and no `axiom` declaration in `BookProof/`,
   `PnpProof/`, `Singularity/`, `RandomMap/` (only prose mentions); the isolation
   greps are empty; `./patches/build-book.sh` re-renders the book with its asserts
   holding and `./patches/check-katex.sh` reports 2135 snippets, 0 failures.  The
   quarantined legacy RH route still carries 28 `sorry`ed declarations in
   `UsedRoute/` / `UnusedRoute/` (neither is a default target).
   **Re-run 2026-08-18b and green:** `lake build`
   (BookProof + Book + Singularity) and `lake build RandomMap` complete with no
   errors; no `sorry` and no `axiom` declaration in `BookProof/`, `PnpProof/`,
   `Singularity/`, `RandomMap/` (the only `sorry`s left in the tree are the
   quarantined legacy RH-route ones in `UsedRoute/`/`UnusedRoute/`, which are in
   no default target); the isolation greps are empty; `./patches/build-book.sh`
   renders `_out/html-single/index.html` and its assertions (no `<base>`,
   fragment links present) hold; `./patches/check-katex.sh` reports 2129 math
   snippets, 0 failures.  Note: the `patches/*.sh` scripts had lost their
   executable bit in this snapshot and it has been restored.
2. Keep `Issues.md` §0b in sync when the chapter set changes.
3. The infinite-dimensional analytic layer (§4.8's boundary): Stone's theorem in
   full generality for operators that are not multiplication operators — the
   continuum Laplacian. Research target, not a plan item.
4. **The NS continuum ESA**: the two Faris–Lavine inequalities for the quadratic
   symbol `A_i = u_j u_{i,j} − ν u_{i,jj}` in a genuinely differential realization;
   ESA then gives the complete flow via Stone. Global existence of the *classical*
   NS equation is a separate, deliberate D5 scope cut.
5. **QG continuum ESA — materially advanced (2026-08-18).** The wave-operator
   ESA that was "entered as a named hypothesis" is now **proved**:
   `BookProof/ChapterStrichartzWave.lean` proves `□ + κ` (real constant) and all
   constant-coefficient real-symbol operators are essentially self-adjoint on the
   Schwartz core of `L²(ℝ^{1+n})` (via the Fourier/multiplier argument),
   `ChapterKatoRellichDeficiency.lean` proves the bounded-perturbation
   Kato–Rellich theorem, and `ChapterWaveBoundedPotential.lean` gives `□ + V` for
   essentially bounded real `V`. On the gravity side, `ChapterStrichartzHermiteQG`
   builds the genuine Hermite core of `L²(ℝ)` (`ChapterHermiteFunctions`:
   `hermiteBasis`, completeness) and proves the 3D gauge-fixed mode Hamiltonian
   `qg3D_essentiallySelfAdjoint_on_hermiteCore` (unbounded, trivial deficiency at
   every non-real `z`). Plan-to-Lean map: `STRICHARTZ_WAVE_ESA.md`.
   **Next target (the author's claim, 2026-08-18): the potential is polynomial
   and bounded below ⟹ `□ + V` is ESA.** The bounded-below-polynomial case is the
   genuine Strichartz step: a polynomial is unbounded, so the *bounded* `V`
   results do not apply, but it is bounded on every compact set, which is exactly
   what the finite-speed/localized energy argument needs (boundedness below is
   the global growth control that keeps the local estimates uniform). The plan:
   (a) localize with the proved `exists_smooth_cutoff` — on each ball of radius
   `R` the truncated `V_R` is essentially bounded; (b) apply the proved
   `wave_add_potential_essentiallySelfAdjoint` to `□ + V_R` — ESA per truncation;
   (c) pass ESA to `□ + V` in the limit `R → ∞` by the finite-speed/energy (or
   form-locality) argument, with the boundedness-below of `V` making the gluing
   uniform. This is a plan item (the cut-off lemma is already proved); the
   remaining boundary is the gauge/BRST-sector transfer check.
   **Update (2026-08-18b): executed as far as it is true.**
   `BookProof/ChapterWaveUnboundedPotential.lean` proves (a)+(b) — for every
   radius `R` a truncation `W_R` of temperate growth agreeing with `W` on the ball
   of radius `R` with `□ + W_R` essentially self-adjoint
   (`wave_add_truncatedPotential_essentiallySelfAdjoint`) — plus the two commuting
   halves with unbounded coefficients: an arbitrary real potential of temperate
   growth is essentially self-adjoint on the Schwartz core
   (`potentialOp_essentiallySelfAdjoint`) and so is every real-symbol Fourier
   multiplier of temperate growth (`multiplierOp_essentiallySelfAdjoint`, which
   contains `constCoeffOp_essentiallySelfAdjoint` via
   `constCoeffOp_eq_multiplierOp`).  Step (c) is **not** taken: with the convention
   `□ = -∂_t² + Δ_x` used in this project, a potential bounded *below* makes the
   time-Fourier fibre `-Δ_x - W` unbounded below — for `W = x⁴` this is the
   limit-circle operator `-d²/dx² - x⁴` with deficiency indices `(2,2)`, a
   classical fact quoted from the literature and not formalized here — so the
   claim as worded is false for this signature.  The correct hypothesis is `W`
   bounded *above* by a quadratic here (equivalently bounded below for
   `□ = ∂_t² - Δ_x`), which is the Sears / Faris–Lavine class; proving that case
    needs the fibrewise (direct-integral) argument and remains the open boundary.
    **Clarification (2026-08-19, the sign question):** the sign is *not* an
    artifact removable by convention, initial conditions, or the overall sign of
    `□` — essential self-adjointness is invariant under negation (`S` ESA ⟺ `−S`
    ESA), and the relevant sign is the *inner* one of `W` relative to the spatial
    `Δ_x` in the time-Fourier fibre, which is fixed by the operator.  The
    `(2,2)` claim for `-d²/dx² - x⁴` is a classical fact quoted from the
    literature, *not* formalized here (only a discrete limit-circle Jacobi
    counterexample is proved, `ChapterNavierStokesDeficiency.lean`).  The
    genuine open question is the sign of `Ṽ` in `H₀ + H₁ - Ṽ` after the
    densitizing/half-density unitary from the book's 3D gauge-fixed `ℋ`; the
    densitized mode symbol is `+V` and the book's `-e(𝒯-terms)` is `≤ 0` (good
    sign for `□ = -∂_t² + Δ_x`), but neither indicator is proved — see
    `PLAN_LEAN_SPECIALIST_QG_FLOW.md` Part D.6.
    **Update (2026-08-18c): the non-commuting mixed case is closed in the elliptic
   normalization.**  `BookProof/ChapterHarmonicOscillatorEsa.lean` proves that the
   harmonic oscillator `-d²/dx² + x²/4` — a differential kinetic term plus an
   unbounded polynomial potential that does not commute with it — is essentially
   self-adjoint on the Hermite core of `L²(ℝ)`
   (`harmonicOsc_essentiallySelfAdjoint`), with the differential identification
   `harmonicOscOp_apply_eq_differential` and unboundedness
   `harmonicOsc_not_bounded`.  This is the sign-correct (potential bounded below)
   case; the hyperbolic direct-integral argument is still open.
6. **QYM unbounded continuum — CLOSED (2026-08-18).** Both plan items of §11.4
   are executed by `BookProof/ChapterFriedrichsExtension.lean` (`sorry`-free /
   `axiom`-free, registered in `BookProof.lean`, certified in
   `ChapterRoadmapAudit.lean`, cited from `Book/YangMillsQuantization.lean`):
   item (1) is `friedrichs_extension_exists` — the Friedrichs extension theorem
   proved with **no boundedness hypothesis**, via the form inner product, its
   completion, Riesz representation of `(H+1)⁻¹` and `A = S⁻¹ − 1` — with
   `friedrichs_hypothesis_holds` discharging the named hypothesis of
   `friedrichs_extension_of_semibounded` and
   `weyl_friedrichs_extension_unconditional` giving the Weyl-gauge conclusion;
   item (2) is settled in favour of the occupation-number/Hermite realization
   (Part E of `PLAN_LEAN_SPECIALIST_QYM_FLOW.md`), and the combined statement —
   the extension exists *and* the Hashimoto/SIRK limit selects it, unbounded —
   is `friedrichs_hashimoto_selects` / `weyl_hashimoto_selects_friedrichs`, with
    `unbounded_friedrichs_example` showing it is not vacuous. What remains is
    only the recorded boundary: the mass gap, deliberately out of scope.
    **Refinement (2026-08-18):** option (b) is *not* a research boundary — the
    book's base `ℝ⁹⁹` is finite-dimensional and `H₁ = ½Σππ + ½ΣBB` is a
    finite-degree polynomial-coefficient differential operator, so the operator
    is **well-defined and symmetric on the product Hermite core** of `L²(ℝ⁹⁹)`
    (the `A`/`∂` ladder structure; same pattern as
    `harmonicOscOp_apply_eq_differential`).  It is a construction task: build
    `A`, `π = −iδ/δA`, `B` on that core and prove core-invariance/symmetry/
    positivity, with the Weyl ordering of the non-commuting `πA` cross-terms and
    the sign of book.tex:7077 as the two caveats.  See the §11.3/§11.4 closing
    updates.  **Executed (2026-08-18/19):** the construction task is done —
    `BookProof/ChapterHermiteProductCore.lean` (Gauss–polynomial core of
    `L²(ℝ⁹⁹)`, dense orthonormal basis whose finite-mode domain is the core)
    and `BookProof/ChapterYangMillsHermite.lean` (coordinate/momentum/
    magnetic-field operators, `[A_j, π_j] = i`, Weyl ordering `weylProd`, positive
    sum-of-squares `ymHamiltonian`, symmetry/positivity, instantiating the
    Friedrichs + Hashimoto theorems), plus the second quantization on
    finite-occupation states in `BookProof/ChapterFockSecondQuantization.lean`.
    Both caveats (Weyl ordering, sign) are settled *inside* the modules; only the
    mass gap remains out of scope.
7. Pedagogical polish (small, editorial): the new plan/doc files
   (`PLAN_LEAN_SPECIALIST_QG_FLOW.md`, `PLAN_LEAN_SPECIALIST_QYM_FLOW.md`,
   `HASHIMOTO_COMPLEX_SHIFTS.md`, `HERMITE_GALERKIN_FRIEDRICHS.md`) and the Book
   prose are in place; keep them in one-to-one correspondence with the proof
   modules on any future edit.

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
and their first derivatives. The densitized coordinates are special in that the
field-space metric is *flat* there: the kinetic term has constant coefficients
`(1/16, −1/24)`, so the Christoffel symbols and curvature vanish and the
connection ("quantum potential") corrections that a generic point transformation
would produce drop out — the unitary image is exactly `H₀ + H₁ − Ṽ` (see §10.3
for the Jacobian half-density that makes the map unitary).

### 10.2 The ESA theorem: Strichartz

The ESA claim for `H_transformed` rests on **Strichartz's theorem** (R. S.
Strichartz, *Essential self-adjointness of powers of generators of hyperbolic
equations*, J. Funct. Anal. **13** (1973) 82–93): a second-order differential
operator whose principal part is a **flat d'Alembertian on `L²(ℝ^N)`** with a
(smooth, polynomial) potential is essentially self-adjoint, because waves
propagate at finite speed in field space. This is the hyperbolic analogue of
Sears' theorem (Reed & Simon Vol. II, Thm X.28) that Part G of the NS plan uses
for the elliptic case.

### 10.2a A proof outline for the Strichartz ESA (plan item)

This subsection records a *concrete proof outline* a Lean–specialist could
execute, in the project's honesty style. The target is the continuum operator
`H = H₀ + V` on `D = C_c^∞(ℝ^N)`, with `H₀` the flat d'Alembertian (principal
part `diag(1/16, −1/24)`) and `V` a smooth polynomial potential. The theorem to
prove (as a named theorem with citation, **never an axiom**, exactly like
Crouzeix in `ChapterH4`):

```
strichartz_esa
  (H₀ : (C_c^∞(ℝ^N)) →ₗ[ℂ] L²(ℝ^N))   -- the flat d'Alembertian, symmetric on D
  (V : ℝ^N → ℂ) (hV : smooth polynomial)
  : EssentiallySelfAdjointOn C_c^∞(ℝ^N) (H₀ + V)
```

**The proof route — via the deficiency/range machinery already in
`BookProof/ChapterFarisLavine` and `BookProof/ChapterNavierStokesEsa`.** The
project already proves the *abstract* spine of the argument; the Strichartz input
is exactly the one analytic hypothesis that feeds it:

1. **Symmetry on `D`.** `H₀` is formally self-adjoint on `C_c^∞` (integration by
   parts on the flat d'Alembertian), `V` is real-valued, so
   `H = H₀ + V` is symmetric on `D`. This is `SymmetricOn` in
   `ChapterFarisLavine`/`ChapterNavierStokesFullEsa`.
2. **The resolvent/range argument (the part the project already has).** ESA of a
   symmetric operator is equivalent to the two ranges
   `(H − i·1)(D)` and `(H + i·1)(D)` being *dense* — the
   `deficiencyTrivialAt_of_dense_range` / `essentiallySelfAdjointOn_of_farisLavine`
   machinery of `ChapterFarisLavine` (Thm 1: with `N` a positive comparison
   operator, `N+1` onto, and the commutator bound, ESA follows). The remaining
   work is to *verify the two Faris–Lavine hypotheses* for the specific
   `H₀ + V` with comparison operator `N = H₀² + 1` (the book.tex auxiliary-operator
   choice) — or to bypass them via finite-speed propagation.
3. **The Strichartz input: finite-speed propagation.** The genuinely new analytic
   content, and the one thing Mathlib does not yet contain: solutions of the
   hyperbolic equation `(∂_t² − Δ_x)φ = 0` propagate at finite speed, so a
   deficiency vector `w` of `H*` (satisfying `H*w = ±i w`) has *empty* domain of
   dependence: by finite speed it would have to propagate out of any compact set,
   contradicting square-integrability. Formally: for a flat d'Alembertian with a
   smooth polynomial potential, `ker(H* − z) = 0` for `Im z ≠ 0` — a **unique
   continuation / finite-speed** statement. This is the named input, recorded with
   its citation (Strichartz 1973; the hyperbolic analogue of the elliptic
   Kato–Rellich/Sears argument).
4. **Conclusion.** With `ker(H* ± i) = 0` (both deficiency indices `(0,0)`),
   `H` is essentially self-adjoint on `D` — matching the project's
   `EssentiallySelfAdjointOn` predicate and, through
   `hasZeroDeficiencyOn_of_farisLavine` / the deficiency-predicate bridge, the
   `HasZeroDeficiencyOn` form the QG/NS chapters use.

**Honest flag.** Steps 1, 2 and 4 are provable in the existing framework. Step 3
 is the analytic core — *finite-speed propagation / unique continuation for the
 flat d'Alembertian with a polynomial potential* — and it is the part recorded as
 a named hypothesis (with citation), exactly as `ns_esa_of_farisLavine` and
 Crouzeix are named rather than assumed. A specialist who formalizes step 3 (e.g.
 the standard energy-estimate + finite-speed argument for the wave equation, or
 Mathlib's `Laplacian`/`MemElap` machinery extended to the wave operator) would
 turn the whole outline into a proof; until then it is a plan item, not a claimed
 theorem.

**Update (2026-08-18): step 3 is now *half-proved* and its precise residual is
the bounded-below-polynomial case.** `BookProof/ChapterStrichartzWave.lean`
proved the *free* wave operator `□ + κ` is ESA on the Schwartz core (Fourier
multiplier), `ChapterKatoRellichDeficiency.lean` proved bounded perturbations
preserve ESA, and `ChapterWaveBoundedPotential.lean` reached `□ + V` for
*essentially bounded* `V`. The author's claim — **`V` polynomial and bounded
below ⟹ `□ + V` ESA** — is the exact remaining content of step 3: a polynomial
is unbounded (so the bounded-`V` results do not apply) but bounded on every
compact set (so the finite-speed/localized energy argument applies, with
boundedness below the uniform growth control). Plan: (a) truncate `V` to
essentially bounded `V_R` on balls using the proved `exists_smooth_cutoff`;
(b) apply the proved `wave_add_potential_essentiallySelfAdjoint` to `□ + V_R`;
(c) pass ESA to `□ + V` by `R → ∞` via the finite-speed/energy (or form-locality)
argument. See §9 item 5.

### 10.3 Honest boundary (same as the NS-FLOW wave)

- **What is provable now** is the *algebraic* content, mirroring the NS plan:
  the change of variables itself, `y = √e`, `ẽ_i^a = √e·e_i^a`; the identity
  that `1/e = (∂y/∂e)²` absorbs the singular denominator into a field
  derivative; the operator-order decomposition of `H_transformed` (2nd + 1st +
  0th); and the positive/flat character of `H₀`. None of this requires the
  continuum analytic theorem.
- **ESA in the transformed variables transfers to the original variables ONLY
  when the transformation is made unitary — and it can be.** The crucial scope
  point is that the raw point map `e ↦ (y, ẽ)` (a nonlinear diffeomorphism of
  field space) is **not** by itself a Hilbert-space unitary: the pushforward
  `(Uψ)(ẽ,y) = ψ(e(ẽ,y))` changes the norm because `Dẽ = J·De`. The standard
  repair is the **Jacobian half-density (metaplectic / van Vleck) factor**:
  `(Uψ)(ẽ,y) = |J|^{−1/2}·ψ(e(ẽ,y))`, `J = det ∂ẽ/∂e`, which makes `U` a genuine
  unitary on `L²(Dẽ Dy)`. With that factor and the ordering chosen to respect it
  (the naive `(1/16e)S² → (1/16)S̃²` holds only for the consistent ordering; a
  generic point transformation conjugates a flat Laplacian into a Sturm–Liouville
  operator with a "quantum potential" `Q[y] ~ (∇y/y)²`), the transformed
  operator is exactly `H₀ + H₁ − Ṽ` with flat principal part. **Then ESA
  transfers by unitary equivalence**, via the project's own
  `hasZeroDeficiencyOn_of_linearIsometryEquiv` (`ChapterNavierStokesLagrangianEsa`):
  vanishing adjoint deficiency is invariant under a unitary `W`, so ESA of the
  flat `H₀`-dominated operator implies ESA of the physical Hamiltonian. (This is
  the same mechanism as the NS Eulerian ⟷ Lagrangian transfer — that change was
  *already* unitary; the densitized one becomes unitary exactly by including the
  half-density.) Honest caveat: the *gauge/BRST sector* is not covered by this
  argument alone — a full BRST-reduced transfer needs `U` to map the physical
  (gauge-invariant) subspace to itself, which the `1/e`-absorption guarantees
  for the kinetic/conformal part but must be checked for `H₁ − Ṽ` once the full
  constraint structure is imposed.
- **What is recorded, not claimed**: the **Strichartz ESA of the flat
  d'Alembertian** is now *proved* in `BookProof/ChapterStrichartzWave.lean`
  (`wave_essentiallySelfAdjoint`, plus `□ + W` for bounded/truncated `W`), and
  the **bounded-below polynomial potential** `W x = ‖x‖^(2k)` is proved as a
  pure potential (`polynomialPotential_essentiallySelfAdjoint`).  What is *not*
  claimed is the **full-potential** continuum conclusion — ESA of `H₀ + H₁ − Ṽ`
  for the untruncated polynomial `Ṽ` on `L²(ℝ⁸⁴)`.  This is **not** a mere
  `R → ∞` limit: under this project's sign convention (`□ = −∂_t² + Δ_x`) a
  bounded-*below* `W` puts the fibre `−Δ_x − W` in the limit-circle regime where
  ESA **fails** (`−d²/dx² − x⁴` has deficiency `(2,2)`); the localization closes
  only under the opposite sign (module docstring of
  `ChapterWaveUnboundedPotential.lean`).  Whether the QG `Ṽ` lies in the proved
  or the failing regime is the analytic core that decides the boundary (cf.
  step (c) of §9.5; see also `PLAN_LEAN_SPECIALIST_QG_FLOW.md` Part D, updated
  2026-08-19).  The project's ODE chapter's `ẋ = x²` warning applies here too:
  the *singular* `1/e` form shows that the *raw* tetrad operator is not even
  well-defined as an operator on a fixed domain, so the change of variables is
  load-bearing, not cosmetic.
- **Do NOT claim**: ESA of the continuum gravity operator, global existence, or
  any unitary-evolution result as a *proved Lean theorem*. The book's own
  existence/uniqueness claims for gravity are in the same scope-cut class as
  Contention D5 for NS.
- **Suggested next step (a plan item, like the NS waves) — CLOSED (2026-08-17):**
  `PLAN_LEAN_SPECIALIST_QG_FLOW.md` now exists and is executed by
  `BookProof/ChapterQuantumGravityDensitized.lean`.  The original wording of the
  item follows.  A
  `PLAN_LEAN_SPECIALIST_QG_FLOW.md` in the NS-FLOW style — Part A (the
  densitized change of variables `√e`, `√e·e_i^a` and the `1/e = (∂y/∂e)²`
  identity), Part B (the flat d'Alembertian principal part and the operator
  decomposition), Part C (the finite truncation on `Fin N` modes with its
  complete unitary flow), Part D (Strichartz/Sears as a named hypothesis, never
  an axiom, exactly as `ns_esa_of_farisLavine` is named in the NS plan). Reuse
   the `Singularity/ChangeOfVars.lean` reciprocal/logarithmic-map pattern and the
   `DiffeomorphismsGravity` book chapter.
- **Next targets (2026-08-19): the book's full quantum Hilbert space and its
  gauge-fixed 3D operator.**  Parts A–D formalize the *one-particle densitized
  operator's* ESA.  To match the book's own definition (book.tex:8247–8320)
  there remain (a) the second quantization on the graded Fock space
  `Γˢ(L²(ℝ⁸⁴×ℤ₂¹⁹)) ⊗ Γᵃ(L²(ℝ⁸⁴×ℤ₂¹⁹))` with the `ℤ₂`-graded superalgebra and
  the fermionic CAR half — the gravity analogue of
  `BookProof/ChapterFockSecondQuantization.lean`; and (b) the concrete 3D
  gauge-fixed field-space Hamiltonian (densitized, Weyl-ordered, positive
  sum-of-squares) plus the BRST charge `G` with the ghosts on `ℤ₂¹⁹`.  These are
  written up as **Part E and Part F of `PLAN_LEAN_SPECIALIST_QG_FLOW.md`** for
  the Lean-specialist.  The mass gap and global existence remain out of scope by
  the author's decision.

### 10.4 The three-theorem toolbox (record)

The manuscript's analytic-layer conclusions draw on three named theorems, all
recorded in this project's honesty style:

| Theorem | Reference | Use in this manuscript |
| :-- | :-- | :-- |
| Strichartz | Strichartz, J. Funct. Anal. 13 (1973) 82–93 | flat d'Alembertian principal part ⟹ ESA (hyperbolic kinetic term, incl. the gravity `H₀`). **Proved** in `ChapterStrichartzWave.lean` (`wave_essentiallySelfAdjoint`); the full-potential `H₀ + H₁ − Ṽ` step remains a boundary (2026-08-19) |
| Sears / Reed–Simon X.28 | Sears, Canad. J. Math. 3 (1951); Reed & Simon Vol. II Thm X.28 | `−Δ + V` with `V ≥ −c|x|² − d` ⟹ ESA (elliptic/quadratic-growth case, NS Part G) |
| Faris–Lavine | Faris & Lavine, CMP 35 (1974) 39–48, Cor. 1.1 | comparison-operator commutator criterion (proved in `ChapterFarisLavine`, NS Part G) |

None of these is an `axiom` in `BookProof/`; each enters as a named theorem with
a citation docstring when a plan requires it.  Of the three, the Strichartz (flat
d'Alembertian) and Faris–Lavine ESA theorems are now **proved** in-repo; the
Sears/Reed–Simon one is used only as a named route for the NS elliptic case.

---

## 11. Quantum Yang–Mills: Friedrichs extension of the 3D gauge-fixed Hamiltonian
(candidate route, record — not a proved Lean theorem)

The manuscript's 3D gauge-fixed Quantum Yang–Mills Hamiltonian
(`book.tex` §"Quantization due to time-evolution: Yang-Mills and Classical
Statistical Field Theory", ~7037–7120, on
`Γ^s(L²(ℝ⁹⁹×ℤ₂³¹)) ⊗ Γ^a(L²(ℝ⁹⁹×ℤ₂³¹))`, the `ℝ⁹⁹` = 3 coordinates + 24 SU(3)
gauge fields `A_{k,a}` + their derivatives, `ℤ₂³¹` the 8 ghosts + derivatives
minus one) is, in the Weyl gauge and **in the Hermite (oscillator) basis**,

```
H(x) = −½ πⁱ_a πⁱ_a − ½ B_{i a} B_{i a}
```

with the BRST charge `Ω = ∫ π^k_a ∂_k ψ†_a − π^k_a f_abc A_{k b} ψ†_c
− (i/2) f_abc ψ†_a ψ†_b ψ_c`. The sign is the convention of the classical
action; up to that sign the Weyl-gauge Hamiltonian is a **sum of squares of the
self-adjoint electric- and magnetic-field operators** (`½Σ(πⁱ_a)² + ½Σ(B_{i a})²`),
i.e. **positive (bounded below by 0)** — already formalized as
`weylHamiltonian_isPositive` in `BookProof/ChapterWeylHamiltonian.lean`.

### 11.1 The theorem: Friedrichs extension

Because `H` is **symmetric and bounded below** (semi-bounded), the classical
**Friedrichs extension theorem** applies: a densely defined, symmetric,
semi-bounded operator on a Hilbert space admits a canonical self-adjoint
extension — the *Friedrichs extension* — obtained by closing its quadratic form
and taking the operator of the closure. Key properties:

- it is the self-adjoint extension whose domain is contained in the form domain
  of the closure, and it is the *largest* (in the sense of the partial order on
  extensions) self-adjoint extension;
- it is **canonical**: it depends only on the operator (and its lower bound), not
  on any choice of auxiliary data — which is exactly the uniqueness the
  Hashimoto-limit claim below needs;
- for a *positive* operator (`H ≥ 0`, the Weyl-gauge case) the Friedrichs
  extension is `√(H*)√(H)`-based and its quadratic form is the closure of the
  original form.

Reference: M. Reed & B. Simon, *Methods of Modern Mathematical Physics, Vol. I*,
Thm X.23 (the Friedrichs extension); K. Friedrichs, *Spektraltheorie
halb-beschränkter Operatoren*, Math. Ann. **109** (1934) 465–487.

### 11.2 The uniqueness claim: the infinite Hashimoto limit selects it

The project's Hashimoto–SIRK machinery (`PLAN_LEAN_SPECIALIST_SIRK_NESTED.md`,
`BookProof/ChapterH8`/`ChapterH9`) builds the order-`n` Krylov approximations
`Bₙ = Vₙ* X Vₙ` whose *spectral side nests*:
`W(Bₘ) ⊆ W(Bₙ) ⊆ W(X)` for `m ≤ n` (`sirk_numRange_nested_orders`), the Ritz
spectra nest, and the best-approximation error is antitone in the order
(`krylov_bestApprox_antitone`), tending to `0` for a cyclic seed
(`krylov_bestApprox_tendsto_zero`). The uniqueness claim to record is:

> **The infinite limit of the Hashimoto algorithm selects the Friedrichs
> extension** — the self-adjoint extension recovered as the order-`n` Krylov
> approximations refine is the canonical one, i.e. the Friedrichs extension of
> §11.1, because the Friedrichs extension is the only self-adjoint extension
> that is *determined by the quadratic form alone* (no boundary condition at
> infinity is imposed beyond the form domain), and the nested-orders
> convergence of the approximants is form-domain-preserving.

### 11.3 Honest boundary

- **What is provable now** (mirroring the NS-FLOW and QG waves): the
  *algebraic* content — the Weyl-gauge Hamiltonian is a sum of squares
  (`weylHamiltonian_isPositive`, already proved); the Hermite-basis (oscillator)
  realization of the fiber, where the comparison/number operator is diagonal and
  the electric/magnetic fields are concrete shifts; the form
  `q(x) = ½Σ‖πⁱ_a x‖² + ½Σ‖B_{i a} x‖²` and its positivity; the BRST charge
  `Ω` and its nilpotency (`nsBrst_nilpotent`-style, via `ChapterGhostField`).
  None of this requires the continuum analytic theorem.
- **What is recorded, not claimed**: the **Friedrichs extension** for the
  continuum `L²(ℝ⁹⁹)` operator, and the **uniqueness by the infinite Hashimoto
  limit**, are named theorems / named claims (Friedrichs 1934, Reed–Simon
  X.23), in the same honesty class as Strichartz (§10) and the NS continuum FL
  inequalities. The Hasimoto-limit-uniqueness sentence in §11.2 is a *conjecture
  to be proved* (a research item), not a proved statement: the current SIRK
  results give nesting, monotone approximation error and (for cyclic seeds)
  tend-to-zero, but the identification of the *limit operator* with the
  Friedrichs extension is not yet formalized.
- **Refinement (2026-08-18): the continuum operator is well-defined on the
  Hermite core, so the remaining boundary is a construction task, not a gap.**
  The base `ℝ⁹⁹` is finite-dimensional (3 + 24 + 72 coordinates, book.tex:
  7045-7048), `H₁ = ½Σππ + ½ΣBB` is a finite-degree polynomial-coefficient
  differential operator, and `A`, `∂` act on the product Hermite basis as ladder
  operators — so `H₁` is well-defined and symmetric on the Hermite core (same
  pattern as `harmonicOscOp_apply_eq_differential` in 1D).  What is not yet
  built is the *Lean construction* of that operator on the product Hermite core
  of `L²(ℝ⁹⁹)`, plus the proofs of core-invariance/symmetry/positivity; the two
  delicate points are the Weyl ordering of the non-commuting `πA` cross-terms in
  `B²` and the sign reconciliation of book.tex:7077 with the positive
  sum-of-squares form.  See the closing update of §11.4.  **(2026-08-18: this
  construction task is now executed — `BookProof/ChapterHermiteProductCore.lean`
  and `BookProof/ChapterYangMillsHermite.lean`; both caveats are settled inside
  the modules.)**  **(2026-08-19: the remaining Part F.11 row — the *second
  quantization* of that one-particle Hamiltonian on the finite-occupation states
  over the core — is executed too, in
  `BookProof/ChapterFockSecondQuantization.lean`: the occupation-number Fock
  space `ℓ²(ℕ →₀ ℕ)`, the ladder operators with `[a_j, a_j†] = 1`,
  `dΓ(A) = Σ ⟪e_j, A e_k⟫ a_j† a_k`, its symmetry, positivity and Friedrichs
  extension, ending in `ym_fock_friedrichs_extension`, together with the
  Hashimoto/SIRK selection of that extension (`ym_fock_hashimoto_selects`).
  Still **not** claimed:
  the mass gap or global existence.)**
- **Do NOT claim**: self-adjointness of the continuum QYM operator, the mass
  gap, or global existence as *proved Lean theorems*. The Yang–Mills existence
  and mass-gap Millennium problem is deliberately out of scope (the book's own
  "if the Hamiltonian is positive-definite then ... with or without a mass gap"
  is a conditional, not a claim).
- **Suggested next step (a plan item) — CLOSED (2026-08-17):**
  `PLAN_LEAN_SPECIALIST_QYM_FLOW.md` now exists and is executed by
  `BookProof/ChapterYangMillsFriedrichs.lean` (Part D.4, the identification of the
  Hashimoto limit with the Friedrichs extension, is deliberately left as a recorded
  conjecture).  The original wording of the item follows.  A
  `PLAN_LEAN_SPECIALIST_QYM_FLOW.md`
  in the NS-FLOW style — Part A (the Hermite-basis fiber: `πⁱ_a`, `B_{i a}` as
  concrete oscillator shifts, `H` a sum of squares, `Ω` nilpotent), Part B (the
  quadratic form and its closure), Part C (the Friedrichs extension as a named
  theorem — never an axiom), Part D (the Hashimoto-limit identification: state
  `sirk_limit_eq_friedrichs` as the research conjecture, with the proved
  `sirk_numRange_nested_orders`/`krylov_bestApprox_tendsto_zero` as the
  supporting nesting facts). Reuse `ChapterWeylHamiltonian`,
  `ChapterGhostField`, `ChapterSuperBracket` and `ChapterH8`/`ChapterH9`.

### 11.4 The unbounded continuum case: precise status and the two plan items
(record, 2026-08-17)

The executed wave proves **more** than §11.3's "What is recorded, not claimed"
records, and it is worth being precise about what is and is not in hand, so a
future specialist knows exactly what to attack.

**What the unbounded case already has (proved, no boundedness):**
`hashimoto_shiftInvert_selects_friedrichs`
(`BookProof/ChapterHashimotoShiftInvert.lean`) reaches *unbounded* Hamiltonians:
for any positive self-adjoint extension `A` of an unbounded symmetric positive
`H`, the shift-inverted operator `R = (A + γ)⁻¹` exists, is **bounded**
(`‖R‖ ≤ 1/γ`), and the whole bounded Galerkin theory applies to `R` — strong
convergence of the truncations, strong resolvent convergence at every non-real
`z`, and `R` uniquely determines `A`. So the *convergence/selection* half is
done for unbounded operators, with no boundedness hypothesis anywhere.

**The two things that prevent a full claim (both plan-sized, not research):**

1. **The extension `A` is input, not constructed.** The headline takes
   `A : Dom →ₗ[ℂ] F` with `hA : IsPositiveSelfAdjointExtension H A` as a
   *hypothesis*: it proves the algorithm converges to whichever extension it is
   given (and that the limit is unique). It does **not** prove that the unbounded
   `H` *has* such an extension — that existence is the Friedrichs theorem, which
   for unbounded operators is still the named hypothesis
   `friedrichs_extension_of_semibounded`, discharged by construction only in the
   bounded regime (`friedrichs_of_bounded`). **Plan item:** prove the existence
   of the positive self-adjoint extension for the specific Weyl-gauge operator —
   an analytic form-closure theorem (the domain of the closed form of
   `½Σ‖πⁱx‖² + ½Σ‖Bₐx‖²` on the actual domain, i.e. the unbounded analogue of
   `weylForm_closable` feeding `friedrichs_of_bounded` without the boundedness
   hypothesis). This is the same kind of content as the QG finite-speed step:
   a genuine but bounded task, recorded in the honesty framework as a plan item.
2. **The continuum realization is a definitional choice, not a gap.** The
    theorems live on an abstract Hilbert space `F` with a `HilbertBasis ℕ ℂ F`,
    and the concrete models are `ℓ²(ℕ,ℂ)` (occupation/Hermite-basis
    representations); the field-space differential realization on
    `L²(ℝ⁹⁹×ℤ₂³¹)` with the magnetic-field operator
    `B_{i a} = ε_{ijk}(∂_j A_{k,a} + f_{abc}A_{j,b}A_{k,c})` is not built. **Two
    defensible choices:** either (a) accept the occupation-number/Hermite
    realization as *the* definition of the quantum theory (then `ℓ²(ℕ,ℂ)` *is*
    the continuum in the Fock sense, and only item 1 remains), or (b) realize
    `B_{i a}` concretely as a field-space differential operator (needing
    Mathlib's Sobolev/differential-operator machinery, the same boundary as the
    NS and QG continuum). **Plan item:** state the choice in
    `PLAN_LEAN_SPECIALIST_QYM_FLOW.md`; if (b), add the concrete realization as a
    Part-E-style item.

With items 1 and 2 settled, the full claim — *the unbounded continuum Weyl-gauge
Hamiltonian has a Friedrichs extension, and the infinite Hashimoto/SIRK limit
selects exactly it* — becomes a theorem of the proved machinery. The mass gap is
out of scope by the author's decision.

**Update (2026-08-18): both items are CLOSED; the claim above is now a proved
theorem.** `BookProof/ChapterFriedrichsExtension.lean` proves the Friedrichs
extension theorem itself with no boundedness hypothesis —
`friedrichs_extension_exists` (form inner product → `FormDom`/`FormSpace`
completion → `formExt_injective`, the closability step → Riesz representation
`friedrichsResolvent` = `(H+1)⁻¹` → `A = S⁻¹ − 1` through the module's own
`invShiftOperator`) — so item 1 is discharged in full generality, not just for
the Weyl operator (`weyl_friedrichs_extension_unconditional`), and
`friedrichs_hypothesis_holds` retires the named hypothesis. Item 2 is decided in
favour of **(a)**, the occupation-number/Hermite realization, recorded as Part E
of `PLAN_LEAN_SPECIALIST_QYM_FLOW.md`; the field-space differential realization
(b) is not built and stays the recorded boundary shared with the NS and QG
threads. The combined unbounded statement is `friedrichs_hashimoto_selects` and
`weyl_hashimoto_selects_friedrichs`, and `unbounded_friedrichs_example` exhibits
it on the genuinely unbounded `A eₙ = n eₙ` on `ℓ²(ℕ, ℂ)`.

**Update (2026-08-18, the Hermite-core well-definedness refinement):** the
conclusion of the previous update is *not* that the field-space realization (b)
is out of reach — it is well-defined on the Hermite core, which turns the
remaining boundary into a concrete construction task rather than a research gap.
The book's base is **finite-dimensional**: `ℝ⁹⁹` = 3 coordinates + 24 gauge
fields `A_{k,a}` + 72 derivatives `∂_j A_{k,a}` (book.tex:7045-7048), so
`L²(ℝ⁹⁹)` carries the explicit product Hermite basis built from the 1D
`hermiteBasis` of `BookProof/ChapterHermiteFunctions.lean` (dense, via
`hermiteCore_dense`).  The one-particle Hamiltonian
`H₁ = ½Σπⁱ_aπⁱ_a + ½ΣB_{i a}B_{i a}` with
`B_{i a} = ε_{ijk}(∂_j A_{k,a} + f_{abc}A_{j,b}A_{k,c})` is a **finite-degree
polynomial-coefficient differential operator**: coordinate multiplication by
`A_{k,a}` and the derivative `∂_j` act on Hermite functions as ladder operators,
so `H₁` maps each Hermite basis vector to a *finite* Hermite combination — hence
it is well-defined and symmetric on the Hermite core, and the second-quantized
`H` is well-defined on the finite-occupation states over it.  This is the same
pattern the repo already proves in 1D:
`harmonicOscOp_apply_eq_differential` identifies the diagonal operator `n + ½`
with the differential expression `x ↦ -ψₙ''(x) + (x²/4)ψₙ(x)` on the Hermite
basis (`BookProof/ChapterHarmonicOscillatorEsa.lean`).  So option (b) is a
well-scoped **construction task**: build the product Hermite core of `L²(ℝ⁹⁹)`,
define `A`, `π = −iδ/δA`, `B` on it, prove core-invariance, symmetry and
positivity of `H₁`, then feed the proved `friedrichs_extension_exists` +
`friedrichs_hashimoto_selects`.  Two genuine caveats to settle before executing:
  - **ordering:** the `πA` cross-terms inside `B²` do not commute
    (`[A_{j,a}, π^k_b] = iδ^k_j δ_{ab}`, book.tex:7060-7061) — the product needs
    Weyl ordering (`½(πA + Aπ)`), the *same* subtlety as the NS Hamiltonian
    `H_N = Σ(π_i A_i + A_i π_i)` and the E.5 BRST charge of
    `PLAN_LEAN_SPECIALIST_NS_FLOW.md`;
  - **sign:** book.tex:7077 writes `H(x) = −½ππ − ½BB`, while the plan and the
    formalized theorems use the positive sum-of-squares `H = ½Σπ² + ½ΣB²`
    (bounded below by 0, the Friedrichs hypothesis) — the book's literal sign
    must be reconciled before the operator is fed to the machinery (same style
    of sign correction already recorded for `□` in §9.5).

**Update (2026-08-18, the field-space realization (b) is EXECUTED).**  The
construction task above is done, `sorry`-free and `axiom`-free, in two new
modules.  `BookProof/ChapterHermiteProductCore.lean` builds the Gauss–polynomial
(product Hermite) core of `L²(ℝᵈ)`: `pgMap : ℂ[X₀,…,X_{d−1}] →ₗ[ℂ] L²(ℝᵈ)`,
`p ↦ p·e^{-‖x‖²/4}`, is injective (`pgMap_injective`), its range
`polyGaussCore` is dense (`polyGaussCore_dense`, by the `d`-dimensional
Fourier/moment argument), Gaussian integration by parts holds
(`gaussInt_pderiv`), and Gram–Schmidt on the enumerated monomials gives an
orthonormal basis `coreBasis` whose finite-mode domain *is* the core
(`span_range_coreBasis`).  `BookProof/ChapterYangMillsHermite.lean` defines the
operators at the polynomial level and transports them through the injection
(`CoreRep`): multiplication by a coordinate (`mulOp`, symmetric for real
coefficients), the momentum `π_j = −i ∂_j` (`momOp`, symmetric by
`gaussInt_pderiv`), the magnetic field
`B_{ia} = ε_{ijk}(∂_j A_{k,a} + f_{abc}A_{j,b}A_{k,c})` as multiplication by the
real polynomial `magPoly` over the `99 = 3 + 24 + 72` coordinates, the Weyl
ordering `weylProd` with `weylProd_polySym`, and the commutation relation
`commutator_coord_mom` (`[A_j, π_j] = i`) that forces it.  The Hamiltonian
`ymHamiltonian = ½Σπ² + ½ΣB²` — the positive sign, the caveat above settled — is
symmetric (`ymHamiltonian_symmetricOn`) with sum-of-squares quadratic form
(`ymHamiltonian_quadForm`, `ymHamiltonian_quadForm_nonneg`), so
`ym_hermite_friedrichs_extension` instantiates `friedrichs_extension_exists` and
`ym_hermite_hashimoto_selects` instantiates
`weyl_hashimoto_selects_friedrichs`.  Nothing about the mass gap or global
existence is claimed.
  With ordering and sign fixed, this Hermite-core construction is the remaining
  link between the abstract theorem and the book's operator.  The mass gap stays
  out of scope by the author's decision.
