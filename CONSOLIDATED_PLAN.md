# CONSOLIDATED_PLAN.md — The Single Plan

One plan that supersedes the per-thread plans for **future work**. It (1) collects
everything that is still **open** from `BOOK_PROOF_PLAN.md`,
`PLAN_LEAN_SPECIALIST_UNPROVED.md`, `SPECIALIST_PLAN_REMAINING.md`,
`PLAN_LEAN_SPECIALIST_COHERENT.md`, `PLAN_A_BOOK_FORMALIZATION.md`,
`PLAN_B_PROSE_VERIFICATION.md`, `SINGULARITY_DETECTION_PLAN.md` and
`PLAN_A_EXECUTION_REPORT.md`, and (2) gives a **disposition for every item** in
`Issues.md` and `Contention.md`. Work already landed is listed in §2 so it is not
re-done or re-listed.

**Status (2026-08-12):** the default build (`lake build`: `BookProof`, `Book`,
`Singularity`), `lake build RandomMap`, `lake build book` + `lake exe book` +
`./patches/postprocess-html.sh`, and the `#print axioms` audit are all green with
no in-scope warnings. `BookProof/` is `sorry`-free / `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`); every `Book/*.lean` chapter is included in
`Book.lean` (38 `{include}`s, 39 chapter files). Of the two historical
mathematical gaps, **both GAP-1 (2026-08-10) and GAP-2 (2026-08-12) are now
CLOSED** (§3); the remaining work is the §7 hygiene residue and the doc refresh.

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

- **4.7 `weakValue` (ChapterWeakValue).** On `Fin n → ℂ` with the standard inner
  product, prove `weakValue i f A = (inner f (A • i)) / inner f i`, its
  well-definedness when `⟨f|i⟩ ≠ 0` (`weakValue_wellDefined`), the diagonal
  collapse to the ordinary expectation when `i = f` (`weakValue_diag`), linearity
  in the observable (`weakValue_linear`), and a double-slit capstone
  (`dslit_weakValue`) tying it to `ChapterTrajectory`. Priority: after §9 items 1–3.

---

## 5. Issues.md — full disposition

| § | Item | Status now | Action required |
| :-- | :-- | :-- | :-- |
| 0 | verso-blueprint needs Lean ≥ v4.29.0 (project pinned v4.28.0) | **[BLOCKER]** | **Keep Verso v4.28.0 manual as the deliverable.** Adopt blueprint **only** when a toolchain exists that is *both* blueprint-compatible *and* supported by `aristotle.harmonic.fun` (see `BOOK_PROOF_PLAN.md` §3.2). Do not bump toolchain/Mathlib in this repo meanwhile. |
| 0b | Current state of this deliverable | **STALE on chapter count** | It says "31 chapters"; the root `#doc` now has **38** `{include}`s, 39 chapter files. Refresh the count and the honesty-flag wording when Issues.md is next touched. |
| 1 | Transitive dependency pins (subverso/MD4Lean/plausible chosen by date) | **LOW RISK, untracked** | Leave pinned; re-derive **only** if a Verso/Mathlib upgrade is ever attempted. Do not upgrade in this repo. |
| 1 | Full `lake build BookProof` recompile integrity | **RESOLVED** | Re-run once per release cycle; the latest `lake build` is green. |
| 1 | `book` is intentionally not a default target | **STALE** | `defaultTargets` is now `["BookProof", "Book", "Singularity"]` — update the wording that still says `["PnpProof", "BookProof"]`. |
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
| D5 | Navier–Stokes existence/uniqueness thesis not carried by any chapter | **DELIBERATE SCOPE** | Keep; `FreeField` does not and should not claim it. Optionally a one-line pointer in `Book/YangMillsQuantization.lean` noting the formalized subset. |
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
  target**, so the default build is clean. Either delete them or add a docstring
  saying they are audit-only. Prefer the docstring (they are the audit trail).
- Root `RiemannProof.lean` now `import UnusedRoute.RcpRandomMap2Bridge` (repointed
  in this wave); the §7 "repoint the import" item is **RESOLVED**.
- `patches/build-book.sh` is tracked; `patches/check-katex.sh` was copied in with
  this wave and is **untracked** — `git add` it (and re-verify its executable bit,
  which has been lost before).
- `SpecialFiles`: keep `Book/Trivial.lean` (unused scaffolding) or delete it;
  it is not `{include}`d.

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

**Update (2026-08-12): the plan is now complete.** D1/D2 prose cleanups are done
(the caveats landed in `Book/Introduction.lean` and `Book/OdeSingularity.lean`),
**GAP-1 is closed** (2026-08-10, `ChapterCoherentThermalFidelity`), **GAP-2 is
closed** (2026-08-12, metrizability residue removed by `ChapterSeparableSpectrum` +
`ChapterSeparableL2Model`), and §4 is fully landed. No mathematical item remains
open. The only remaining work is the medium-value **weak-value task (§4.7)**,
hygiene, and doc-refresh:

1. **§4.7 `weakValue`** (`ChapterWeakValue`) — the weak-value ratio and its
   well-definedness, diagonal collapse, and linearity (see §4 and the Proof-Plans
   appendix §D). Small, self-contained, and the natural next mathematical target.
2. **Hygiene §7** — note the two `randomMap2_axioms` audit-only modules; confirm
   `patches/check-katex.sh` is tracked.
3. **Issues.md refresh** — the §0b chapter count and §1 default-targets wording
   were already updated in-flight; re-verify they match the current tree (38
   `{include}`s, `defaultTargets = ["BookProof", "Book", "Singularity"]`).
4. Run the **§8 verification gate** (builds, book wrapper, sorry/axiom audit,
   isolation audit), then re-verify the GAP-1/GAP-2 closures are recorded in
   `BookProof/STATUS.md` (both already are).