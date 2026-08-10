# CONSOLIDATED_PLAN.md — The Single Plan

One plan that supersedes the per-thread plans for **future work**. It (1) collects
everything that is still **open** from `BOOK_PROOF_PLAN.md`,
`PLAN_LEAN_SPECIALIST_UNPROVED.md`, `SPECIALIST_PLAN_REMAINING.md`,
`PLAN_LEAN_SPECIALIST_COHERENT.md`, `PLAN_A_BOOK_FORMALIZATION.md`,
`PLAN_B_PROSE_VERIFICATION.md`, `SINGULARITY_DETECTION_PLAN.md` and
`PLAN_A_EXECUTION_REPORT.md`, and (2) gives a **disposition for every item** in
`Issues.md` and `Contention.md`. Work already landed is listed in §2 so it is not
re-done or re-listed.

**Status (2026-08-10):** the default build (`lake build`: `BookProof`, `Book`,
`Singularity`), `lake build RandomMap`, `lake build book` + `lake exe book` +
`./patches/postprocess-html.sh`, and the `#print axioms` audit are all green with
no in-scope warnings. `BookProof/` is `sorry`-free / `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`); every `Book/*.lean` chapter is included in
`Book.lean` (38 `{include}`s, 39 chapter files).

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
- **Verso integrated** on v4.28.0; single-page output decided and locked
  (`emitHtmlSingle := .immediately`, `emitHtmlMulti := .no`).

---

## 3. The two documented mathematical gaps (BookProof, high value)

These are the only two *mathematical* open items in the whole thread. Both are
**documented gaps, not `sorry`s** — keep it that way.

### GAP-1 — Physical derivation of `τ = n̄ + ½` (Part A.4 / F.4)

Status: the **finite algebraic core is proved** (`ChapterThermalTemperatureCore.lean`:
`geometricOccupancy_mean`, `geometricOccupancy_variance`, `half_integer_floor`,
`thermal_temperature_eq_mean_half`, all `#check`-ed). What remains is the
*physical derivation from the fidelity of displaced thermal states* — the
"extra 1/2" must be shown to come from the coherent-state overlap, not just
postulated. Reuse `ChapterBoseEinstein` (`τ(x) = ½·coth(x/2)`),
`ChapterCoherentOccupation`, `ChapterCoherentFidelity`.

Definition of done: a new `BookProof/ChapterCoherentTemperature.lean` (or an
extension of the core) proving where `n̄ + ½` comes from, `sorry`-free, registered
in `BookProof.lean`, `#check`-ed in `Book/CoherentState.lean`. If the physics
cannot be made algebraic, record the exact obstruction in `BookProof/STATUS.md` —
do **not** `sorry`.

### GAP-2 — Exhaustiveness of the abelian von Neumann classification (Part B.4 / F.5)

Status: the four concrete classes are **proved** — finite `Iₙ`
(`ChapterAbelianDiagonal`), countable `ℓ∞(ℕ)` (`ChapterAbelianDiagonalCountable`),
diffuse `L∞(μ)` (`ChapterLinftyMultiplication`), mixed atomic-plus-diffuse
(`ChapterAbelianMixture`). What remains is the **exhaustiveness** claim: every
abelian `*`-algebra on separable `L²` is `*`-iso to one of the five standard
types (the full von Neumann theorem, out of Mathlib).

Definition of done: attempt the provable condensation — e.g."every abelian,
star-closed, unital algebra on `L²` whose projections are purely atomic is
`*`-isomorphic to `ℓ∞(ℕ)` (or `Iₙ`)"; finite convex combinations reduce to the
mixture class. If out of reach, record the exact obstruction in
`BookProof/STATUS.md` — do **not** `sorry`.

---

## 4. Open BookProof tasks from the older plans (medium value, isolated)

These are the pieces of `SPECIALIST_PLAN_REMAINING.md` Parts B/D that never
landed (verified absent from the current tree):

- **4.1 `tail_infinite_dimensional` (Task B2b).** `¬ FiniteDimensional ℝ InnerTail`
  for `InnerTail = Substrate = L²[0,1]`: build an infinite orthonormal family
  (dyadic indicator rectangles, generalizing `substrate_orthonormal_pair`).
  Unblocks the Hilbert-space tensor identification.
- **4.2 Hilbert-space tensor identification (Task B2, "heavier" half).**
  `SolovayHilbertSpace (N₁+N₂) … ≃ₗᵢ[ℂ] (InnerHead N₁ ⊗[ℂ] … ⊗[ℂ] …)` with
  `innerSpaceTensorEquiv`/`headSumEquiv`/`tailTensorEquiv_map`. The **measure
  form** exists; the Hilbert form is a corollary/`abbrev`.
- **4.3 Cross-dimensional inner product (Task B5 / `BOOK_PROOF_PLAN.md` 6.6).**
  `enlarge_is_measure_preserving` and `cross_dimensional_inner_well_defined`
  (Mehler tail split ⇒ padding with Gaussian coordinates is an isometry). Depends
  on A1/A2 (both proved) and `inner_reduces_to_head`.
- **4.4 `joint_prob_has_wavefunction` (Task D1).** The `|Ψ|² = p` finite anchored
  theorem (nonneg `p`, `∑ p = 1` ⇒ `∃ Ψ, ‖Ψ z‖² = p z ∧ ∑ ‖Ψ z‖² = 1`). Small,
  self-contained. The unitary/Gram–Schmidt/SVD follow-up `p(x,y) = |U(y,x,0)|²`
  (D1b) is strictly optional.
- **4.5 `exists_separable_prob_with_arbitrary_finite_law` (Task D3).** The
  Intro-answering headline: arbitrary law on the finite head × Mehler on the tail,
  separable, with the correct finite marginal. Depends on B2a/B2b.
- **4.6 Disintegration via `prod_disintegrate` (Task D2).** `joint = marginal ×`
  conditional kernel on standard Borel spaces. The `condDistrib` route now lives
  in `ChapterSelectingEvents`; add the explicit `prod_disintegrate` form if a
  chapter wants it. Low priority; implement once and reference from both.

Priority order within this section: 4.1 → 4.2 → 4.3 → 4.5 → 4.4 → 4.6.

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
| 7 | Abstract measure-theoretic layer of `book.tex` §3 | **PARTIALLY RESOLVED** | The finite core + `condDistrib` kernel is done. The genuinely abstract layer (full standard-measure-space classification, commutative-von-Neumann `≅ L∞` as a theorem, disintegration on standard Borel) is **GAP-2** + §4.6. |
| 7 | Remaining non-deferred gaps (two) | **= GAP-1, GAP-2** | See §3. |

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
- Root `RiemannProof.lean` still `import RandomMap.RcpRandomMap2Bridge` (that
  module now lives at `UnusedRoute.RcpRandomMap2Bridge`). Root modules are not a
  default build target, so nothing breaks; repoint the import the next time the
  root file is touched.
- `patches/build-book.sh` is new and **untracked** — `git add` it with the
  current session's hardening.
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
# 5. GAP-1 / GAP-2 statuses recorded in BookProof/STATUS.md (proved or exact obstruction, no sorry)
```

The two mathematical gaps (§3) each need a `BookProof/STATUS.md` "Unchanged
gaps" update in line with the existing convention: *proved*, or *exact
obstruction recorded, not `sorry`-ed*.

---

## 9. Suggested attack order for the next agent

1. **D1 + D2 prose cleanups** (one-liners, no build needed) — closes the only
   flagged Contention contradictions.
2. **GAP-1** (`ChapterCoherentTemperature` fidelity derivation) — high value,
   mostly algebraic.
3. **§4.1 → 4.2 → 4.3** (`tail_infinite_dimensional` → Hilbert tensor form →
   cross-dim inner) — one dependency chain, closer the Solovay programme.
4. **GAP-2** (vonNeumann exhaustiveness; attempt the atomic→`ℓ∞` condensation).
5. **§4.4 → 4.5 → 4.6** (`joint_prob_has_wavefunction` → separable existence →
   `prod_disintegrate`) — small, self-contained closers.
6. **Hygiene §7** and **Issues.md refresh** (§0b count, §1 default-targets, §2
   deferred-marking) at the end of the pass, then the §8 verification gate.