# Issues, Uncertainties, and Constructive Criticism

This file records open questions, places where more information would help, and
constructive criticism of the current approach. It is maintained by the agent
building the Verso edition of the book. Items are grouped by theme and tagged
`[UNCERTAIN]`, `[NEEDS-INFO]`, `[CRITIQUE]`, or `[BLOCKER]`.

---

## 0. verso-blueprint requires a toolchain migration (BLOCKER for that path)

- **[BLOCKER]** The author requested using
  [`verso-blueprint`](https://github.com/leanprover/verso-blueprint) to sync the
  Lean content with the exposition. **verso-blueprint requires Lean ≥ v4.29.0**
  (it was extracted from Verso in March 2026 and was *never* on v4.28.0; its
  earliest commit is `v4.29.0-rc3`, and `main` is `v4.32.0`). This project,
  Mathlib, Verso, and the 198-module `BookProof` library are all pinned to
  **v4.28.0**.

- verso-blueprint works by tagging Lean declarations with
  `@[blueprint "label"]` and **elaborating** them (it detects `sorry`, builds
  dependency graphs, and renders progress). It therefore must run on the *same*
  toolchain as the code it documents. A v4.29.0+ blueprint cannot load v4.28.0
  `BookProof` oleans.

- **Consequences of adopting verso-blueprint:**
  1. Bump `lean-toolchain` to ≥ v4.29.0 (or v4.32.0 to track blueprint `main`).
  2. Bump Mathlib to the matching version and **re-fetch/rebuild it** (conflicts
     with the "do not rebuild Mathlib" instruction).
  3. **Re-verify `BookProof`** against the new Mathlib (API-drift risk across 198
     modules; the STATUS.md notes the library already drifted once against
     v4.28.0).
  4. Add `@[blueprint "label"]` attributes to the featured `BookProof` theorems
     (and choose a stable label scheme mirroring the chapter structure).
  5. Set up the verso-blueprint package (chapter modules + Blueprint top-level +
     `lake exe vbp build` generator) and port the exposition written so far into
     `:::theorem`/`:::proof` blueprint blocks with `{uses ...}`/`{bpref ...}`
     dependency edges.

- **Decision (confirmed by author):** keep the working **Verso v4.28.0 manual** as
  the deliverable (it builds and renders to HTML), and treat verso-blueprint
  adoption as a planned migration for the Lean specialist — to be executed only when
  a toolchain exists that is *both* verso-blueprint-compatible *and* supported by
  `aristotle.harmonic.fun`. See `BOOK_PROOF_PLAN.md` §3.2. The Verso markup already
  written ports to blueprint blocks with modest edits, so the prose is reusable.

---

## 0b. Current state of this deliverable (DONE)

- **Verso integrated** on v4.28.0: `lakefile.toml` now requires `verso @ v4.28.0`,
  `subverso @ verso-v4.28.0`, `MD4Lean @ 7e097e9a…`, `plausible @ 55c8532e…`.
  Originals backed up at `lakefile.toml.bak`, `lake-manifest.json.bak`.
- **The book builds and renders.** `lake build book && lake exe book` produces the
  single-page `_out/html-single/index.html` (see §4 for the single-page decision and
  the 35-`{include}` root `#doc`). Prose, KaTeX math, and the Lean statement code
  blocks (`<pre>`) all render.
- **35 chapters** written (36 chapter files under `Book/`, of which 35 are
  `{include}`d in the root `Book.lean`; `Book/Trivial.lean` is unused scaffolding,
  kept deliberately): Introduction; Part I (Dutch book, sequential Bayes,
  max-entropy, total variance); Part II (probability clock/Euler, Born reproduces,
  gauge fiber, **conditional probability parametrized by a unitary**, Stern–Gerlach,
  free field, **spin–statistics**); Part III
  (irreversibility, bijection probability, null measure, baryon asymmetry, law of
  large numbers); Part IV (ODE singularity, from `ODE.tex`); Part V (PA-free Hilbert
  space from `newproof.md`, and the **Solovay–Kopperman tensor product**); Part VI
  (**symmetries as unitary representations**, deterministic transformations, collapse
  keeps Kolmogorov, Euler generic, time-translation stochastic, **trajectory
  reconstruction**, double-slit, Bell/CHSH, EPR-complete, classical limit); and the
  proof-plans appendix. The five bolded chapters were added to close the remaining
  non-deferred `book.tex` gaps (see §2 and §7). **Update (August 2026):** the
  physics chapters formerly listed as *deferred* in §6 have since been written up
  as well — `GaugeSymmetry`, `RealRepresentations`, `YangMillsQuantization`,
  `GribovAmbiguity`, `PhysicalParity`, `DiffeomorphismsGravity`,
  `ConsciousnessBayesianPrior` and `AlignedDeepLearning` — all `{include}`d in the
  root `Book.lean`, along with the later `CoherentState` chapter.
- **Lean statements are shown as plain (non-elaborated) code blocks.** Verification
  is anchored on `lake build BookProof`. Upgrading to elaborated blocks
  (`public import` + `experimental.module`) and to verso-blueprint are planned
  (`BOOK_PROOF_PLAN.md` §3).
- **Honesty flags refreshed (July 2026):** all three ODE-related items are now
  `sorry`-free theorems: `nelson_essential_self_adjoint` (deficiency-index
  certificate in `Singularity/Esa.lean`), `weyl_symmetrization_self_adjoint`
  (Wick self-adjointness in `Singularity/Hamiltonian.lean`), and
  `ae_no_real_singular_time` (complexification resolution in
  `BookProof/ChapterOdeComplexification.lean`). The PA-free chapter
  separates the **verified** Riesz–Fischer core
  (`completeSpace_iff_summable_norm`) from the **metamathematical** "no PA leak"
  interpretation.  **Update (August 2026):** two further honesty edits
  landed — `Book/Introduction.lean` now carries the "(not of probability theory)"
  caveat alongside the slogan, matching `Book/DeterministicTransformations.lean`
  (Contention D1), and `Book/OdeSingularity.lean` reports the manuscript's own
  "not completely satisfactory" caveat for the second (degeneracy) blow-up problem
  (Contention D2).

---

## 1. Build and dependency setup

- **[UNCERTAIN] Transitive dependency pins.** Verso `v4.28.0` was added with these
  pins (in `lakefile.toml`): `subverso @ verso-v4.28.0`
  (`4539e605…`), `MD4Lean @ 7e097e9a…` (latest commit before the Verso release
  date 2026-02-16), and `plausible @ 55c8532e…` (the rev Mathlib `v4.28.0` already
  uses). The empty scaffolding and a `#check` test build succeeded, so these are
  *probably* correct, but they were chosen by date rather than from an authoritative
  "known-good" lockfile. If a future Verso/Mathlib upgrade is attempted, these pins
  should be re-derived. Originals are backed up at `lakefile.toml.bak` and
  `lake-manifest.json.bak`.

- **[NEEDS-INFO] Existing build integrity after adding Verso.** `lake build book`
  works, and the book build **resolves the whole workspace** (Mathlib stays at
  `v4.28.0`, `plausible` pin unchanged), so the manifest is consistent and
  `BookProof`'s dependencies are unchanged. A full `lake build BookProof` compile has
  **not** been re-run here (it is a long build); it should be confirmed once before
  merging — handed to the specialist per the "no long builds" instruction.

- **[RESOLVED] Book build speed.** Earlier the chapters `import`ed `BookProof`
  modules (pulling Mathlib elaboration into the book build, ~60–120 s/chapter). The
  Lean statements are now **plain code blocks** and the chapters `import` only
  `VersoManual`, so the whole book builds in ~2 minutes (≈173 jobs). Re-introducing
  elaboration (§3.1 of `BOOK_PROOF_PLAN.md`) would make it slower again.

- **[UPDATED] Default targets.** `defaultTargets` is now
  `["BookProof", "Book", "Singularity"]`: a bare `lake build` compiles the proof
  library, the book's chapter modules and the ODE development, but **not** the
  `book` executable and **not** `PnpProof` / `RandomMap` (build those explicitly,
  e.g. `lake build RandomMap`). Render the book with `./patches/build-book.sh`
  rather than a bare `lake exe book`: the wrapper asserts that the emitted HTML has
  no `<base>` element and that the fragment links are present.

## 2. Content and curation

- **[CRITIQUE→RESOLVED (August 2026)] This is a curated edition, not a full
  conversion.** `book.tex` has 17 chapters. Coverage after adding **Part VI
  (Determinism, Complementarity, and Collapse)** — 8 new chapters anchored to
  existing `BookProof` modules — is mapped in the table below. **Update (August 2026):** the field-theory /
  gravity / representation-theory / applied chapters that this section previously
  listed as *deferred pending a framing decision* have now been written up, so the
  table below is re-marked and §6 is closed. Two chapter names used elsewhere in
  this file were never separate files: the *classical limit* material lives in
  `Book/EPRComplete.lean` and the *trajectory reconstruction* material in
  `Book/DoubleSlit.lean` (both anchored on `ChapterTrajectory`).  The
  "Part N" labels used in this file predate the current eight-part structure of
  `Book.lean` (Probability as Coherent Belief; Wave-functions, Euler's Formula and
  the Born Rule; Relativity, Gauge Theory and Gravity; Consciousness, Deep Learning
  and the Bayesian Prior; Entropy, Irreversibility and the Arrow of Time; the ODE
  singularity; Completeness without Peano Arithmetic; Determinism, Complementarity
  and Collapse) — read them as chapter pointers, not as part numbers.

  | `book.tex` chapter | Book coverage |
  | :--- | :--- |
  | Introduction | **Covered** (revised per author; beach example, why-Timepiece, aim, quantization-is-not) |
  | Resolution of the ODE $x'=x^2$ singularity | **Covered** (Part IV, from `ODE.tex`) |
  | Wave-function parametrization of a probability measure | **Covered**: §3 Born/fiber (Part II `BornReproduces`, `BornFiber`); §3 unitary parametrization of conditional probability — joint density = `|U|²`, Gram–Schmidt unitary, Hilbert–Schmidt boundedness, singular-value expansion, and the marginal/regular-conditional converse (Part II `ConditionalUnitary`, **now a chapter**, using `ChapterJointUnitary`, `ChapterKernelBound`, `ChapterB3`/`ChapterB3b`, `ChapterConditional`); §4 collapse-vs-Gleason (Part VI `CollapseKeepsKolmogorov`); §5 free field (Part II `FreeField`); §6 spin-statistics (Part II `SpinStatistics`); §7 symmetries as unitary representations (Part VI `SymmetryRep`); §8–9 conservative/deterministic (Part VI `DeterministicTransformations`); §10–11 ensemble forecasting + classical limit (Part VI `ClassicalLimit`). Only the abstract measure-theoretic layer of §3 (classification of standard measure spaces, commutative-von-Neumann `≅ L∞`, disintegration on a standard Borel space) remains as placeholders in `ChapterSelectingEvents` — see §7. |
  | Gauge symmetry & dissipative dynamics | **Covered** (`Book/GaugeSymmetry.lean`; `ChapterBRSTNilpotent`, `ChapterGhostField`, `ChapterFreeFieldConstraint`, `ChapterConservative`) |
  | Reconstructing the classical trajectory | **Covered** in Part VI: symmetries as unitary representations (`SymmetryRep`), time-translation-stochastic-iff-deterministic (`TimeTranslationStochastic`, using `ChapterReconstruct`), deterministic theory (`DeterministicTransformations`), causality + inverse transform (`EPRComplete`), double-slit (`DoubleSlit`), Bell/CHSH (`BellInequalities`), and trajectory reconstruction by post-selection (`TrajectoryReconstruction`, **now a chapter**, using `ChapterTrajectory`) |
  | Wave-function collapse vs Euler's formula | **Covered**: probability clock (Part II), Stern–Gerlach (Part II), Euler $N$-state/countable/complex/quaternionic (Part VI `EulerGeneric`); black-hole-information section not yet a chapter |
  | Free field parametrization in Classical SFT & Navier–Stokes | **Covered in the formalized subset** (`Book/FreeField.lean`, `Book/YangMillsQuantization.lean`; `ChapterNavierStokes`, `ChapterMassGap`, `ChapterQuadraticOrdering`, `ChapterHolomorphic`, `ChapterLocalOperators`). The manuscript's existence/uniqueness thesis is deliberately **not** claimed (Contention D5) |
  | Real representations, CPT, relativistic position operator | **Covered** (`Book/RealRepresentations.lean`; `ChapterLorentz*`, `ChapterMajorana*`, `ChapterCPT*`, `ChapterLocalization`, `ChapterLittleGroup`) |
  | Quantization due to time-evolution: Yang–Mills & CSFT | **Covered** (`Book/YangMillsQuantization.lean`; `ChapterYangMills*`, `ChapterFreeEMField`, `ChapterGellMann`) |
  | Timepiece and the Gribov ambiguity | **Covered** (`Book/GribovAmbiguity.lean`) |
  | Physical parity transformation & antiparticles | **Covered** (`Book/PhysicalParity.lean`; `ChapterParity*`) |
  | Diffeomorphisms and gravity | **Covered** (`Book/DiffeomorphismsGravity.lean`; `ChapterGravity*`) |
  | Selecting events is not rewriting history (P vs NP) | **Covered** (Part V, from `newproof.md`; `ChapterSelectingEvents`, `ChapterSolovay` exist) |
  | Consciousness as a Bayesian prior | **Covered** (`Book/ConsciousnessBayesianPrior.lean`; `ChapterConsciousnessNullMeasure`, also used in Part III). The AI-misalignment/Fermi-paradox material stays out of scope |
  | Entropy & irreversible deterministic time-evolution | **Covered** (Part III: `Irreversibility`, `BaryonAsymmetry`) |
  | Aligned deep learning as random sampling | **Covered** (`Book/AlignedDeepLearning.lean`; `ChapterDeepLearning*`, `ChapterMAPNull`, `ChapterHierarchicalBayes*`) |
  | Statistical Model Theory & Bayesian priors where RH is true | **Out of scope by decision** — recorded here only; the handwritten RH claim is dropped (Contention D9) and `PaFreeHilbert` + `SolovayTensor` are the intended replacement |

- **[UNCERTAIN] Sketch proofs were re-derived, not transcribed.** The sketch proofs
  in the chapters were written from the `BookProof` docstrings (`STATUS.md`), the
  theorem statements, and standard mathematics — and in places *improved* for
  pedagogy, as permitted. They were **not** line-by-line checked against the
  corresponding `book.tex` passages. The Dutch-book, Bayes, max-entropy, and
  total-variance sketches are standard and low-risk; any chapter making a less
  standard claim should be cross-checked against `book.tex` before publication.

- **[RESOLVED] Author intent for the "central thesis".** The author confirmed the
  slogan "quantum mechanics is what probability theory looks like when you
  parametrize the simplex by the sphere" is fine, and clarified the intended framing
  of the Introduction: the core message of `book.tex` is that **probabilities let us
  relate arbitrary, complex random events to standard intuitive random events** (the
  manuscript's example: a probability of $0.32$ means "as likely as finding a lost
  object buried in a 1 km beach by searching a 320 m interval"). We do **not** need
  to say what probability _means_ — only to relate complex events to intuitive ones.
  The Dutch-book argument should be kept as _one example_ of what probability can
  be, not the foundation. The Introduction was revised accordingly (new opening
  section "What Probability Does: Relating the Complex to the Intuitive", plus the
  manuscript's "Why a simple solution exists", "Why Timepiece", "Aim / what
  quantization is not" sections).

## 3. The two replacement chapters

- **[CRITIQUE] `newproof.md` mixes a verified fact with a philosophical claim.**
  The *verified* core is the Banach-space characterization
  `completeSpace_iff_summable_norm`, which already exists in Mathlib. The
  *philosophical* claim — that the completed Hilbert space "does not leak Peano
  Arithmetic because infinite elements are unselectable" — is a metamathematical
  argument that is **not** (and likely cannot be) a single Lean theorem. The PA-free
  chapter must keep these two layers clearly separated and must not present the
  philosophical layer as machine-verified. `newproof.md` itself contains `sorry`d
  proof sketches; these are plans, not proofs.

- **[NEEDS-INFO] ODE chapter formal status.** `ODE.tex` §"Formal Verification in
  Lean 4" references `Poly.lean`, `Hamiltonian.lean`, `Esa.lean`, `Singularity.lean`
  and a "current status". I should confirm which of these exist and are `sorry`-free
  (there is a `Singularity/` directory and `Singularity.lean` in the repo) before
  claiming any ODE result is verified. See the proof-plan appendix for the gaps.

## 4. Rendering

- **[RESOLVED, 2026-08-11] KaTeX coverage.** Display/inline math is written as
  `` $`…` `` / `` $$`…` `` and rendered client-side by KaTeX with
  `throwOnError: false`, so an unsupported construct would be shown in red rather
  than break the build. It is now checked mechanically:
  `./patches/check-katex.sh` extracts every `.math.inline` / `.math.display`
  snippet from `_out/html-single/index.html` and re-renders each one with
  `throwOnError: true` against the KaTeX build the book ships. Current result:
  **2120 snippets, 0 failures** (re-run 18 August 2026 after the unbounded
  Friedrichs section landed; previously 1838 on 12 August 2026), including all
  `pmatrix`/`bmatrix` displays (the case that had never been confirmed). Re-run it
  after `./patches/build-book.sh`.  Note (18 August 2026): the `patches/*.sh`
  scripts had lost their executable bit in this snapshot and it has been restored
  (`git update-index --chmod=+x`), since `./patches/build-book.sh` is the only
  supported book build path.

- **[CRITIQUE] Some `#check` types are very long.** A few headline theorems
  (e.g. the free-field and measure-theoretic ones) have large elaborated types that
  may render unwieldily. For the worst offenders it may be worth adding a short
  prose paraphrase immediately above the block (already done for most), or restating
  a clean `example` instead of `#check`.

- **[DECISION] Single-page, menu-free HTML.** The author reported the multi-page
  navigation buttons "are not working well" and asked for **HTML without menus, just
  the text non-stop, with links/bookmarks to the appropriate place**. `BookMain.lean`
  now sets `emitHtmlSingle := .immediately` and `emitHtmlMulti := .no`. Verso's
  `emitHtmlSingle` produces one `_out/html-single/index.html` containing the whole
  book continuously, a linked Table of Contents, in-page anchor cross-references
  (`traverseHtmlSingle` uses `htmlDepth := 0`), and `showNavButtons := false` (no
  nav buttons/menu). Output moves from `_out/html-multi/` to `_out/html-single/`.

- **[RESOLVED] The 26-`{include}` build limit.** The full 26-chapter root `#doc`
  originally failed to elaborate (`invalid {...} notation … PartMetadata ?m`, a stuck
  genre metavariable), so the single-page HTML could not be built. **Root cause:** a
  Verso bug — `FinishedPart.toSyntax` (`Verso/Doc/Elab/Basic.lean`) annotated each
  *block* as `(b : Block genre)` to survive Lean's array-elaboration chunking, but
  left the *sub-parts* array unannotated; with ~26 included chapters the chunked
  sub-parts let-bindings left nested parts' implicit genre unresolved. **Fix:**
  annotate sub-parts as `(s : Part genre)`, shipped as
  `patches/verso-0001-annotate-subparts.patch` (apply with
  `./patches/apply-verso-patches.sh`; re-run after any fresh clone / `lake update`,
  since `.lake/` is gitignored). With the patch, `lake build book && lake exe book`
  produces `_out/html-single/index.html` (single page, all 26 chapters, ~190 anchored
  headings, 0 broken ToC links). It was *not* a count limit and *not* fixed by
  `maxHeartbeats`/`maxRecDepth`/`experimental.module`. See `BOOK_PROOF_PLAN.md`
  Priority 4.   **Update (August 2026):** the root `#doc` now has **35**
  `{include}`s — the chapters of §7 plus the formerly deferred physics
  chapters. Since the fix annotates every sub-part binding (it was never a hard
  count limit), 35 includes elaborate the same way, and `./patches/build-book.sh`
  renders them into the single page.

- **[GOTCHA] Multi-line `**bold**` wrapping inline math breaks the root splice.**
  A `**bold**` that spans a line break *and* contains inline math (`` $`…` ``)
  compiles fine in a chapter module but makes the root `Book.lean` `#doc` splice
  fail with `invalid {...} notation, expected type is not of the form (C ...)`.
  Keep any bold that contains math on a single line (or move the math out of the
  bold). Hit in `ClassicalLimit.lean` ("dense in the $`L^2` measure").

## 6. Formerly deferred chapters — **DONE (framing settled, August 2026)**

Every item in this section has since been written up as a chapter under `Book/`
and `{include}`d in the root `Book.lean`; the list below is kept as the record of
the framing questions that were resolved and of the formal anchors each chapter
uses.  The only item still deliberately *not* a chapter is `book.tex` ch. 17
(Statistical Model Theory / priors where RH is true), which stays recorded in this
file only.

- **[NEEDS-INFO] Gauge symmetry & dissipative dynamics (`book.tex` ch. 4).** Anchors:
  `ChapterBRSTNilpotent`, `ChapterGhostField`, `ChapterFreeFieldConstraint`,
  `ChapterConservative`. Open question: how much of the gauge-fixing / Gribov /
  BRST discussion to include versus stating the "quantum constraints implement exact
  constraints without null measure" thesis and pointing at the modules.

- **[NEEDS-INFO] Classical Statistical Field Theory & Navier–Stokes (`book.tex`
  ch. 7).** Anchors: `ChapterNavierStokes`, `ChapterMassGap`,
  `ChapterQuadraticOrdering`, `ChapterHolomorphic`, `ChapterLocalOperators`,
  `ChapterNoLebesgue`. The Navier–Stokes "existence and uniqueness" claim and the
  mass-gap discussion are strong; needs care to state exactly what the finite-
  dimensional formalization does and does not prove.

- **[NEEDS-INFO] Real representations, CPT, relativistic position operator
  (`book.tex` ch. 8).** Anchors: `ChapterLorentz*`, `ChapterMajorana*`,
  `ChapterPauli*`, `ChapterPin*`, `ChapterIPin`, `ChapterLittleGroup`,
  `ChapterLocalization`, `ChapterCPT*`. This is the largest technical chapter; a
  decision is needed on how much representation theory to reproduce versus summarize.

- **[NEEDS-INFO] Yang–Mills quantization & Gribov ambiguity (`book.tex` ch. 9–10).**
  Anchors: `ChapterYangMillsBianchi`, `ChapterYangMillsFieldStrength`,
  `ChapterYangMillsSU3`, `ChapterFreeEMField`, `ChapterGellMann`.

- **[NEEDS-INFO] Physical parity & antiparticles (`book.tex` ch. 11).** Anchors:
  `ChapterParity*` (13 modules), `ChapterParityMajoranaQuant`.

- **[NEEDS-INFO] Diffeomorphisms & gravity (`book.tex` ch. 12).** Anchors:
  `ChapterGravity*` (8 modules).

- **[NEEDS-INFO] Consciousness as a Bayesian prior (`book.tex` ch. 14).** Anchor:
  `ChapterConsciousnessNullMeasure` (already used in Part III). The Fermi-paradox /
  AGI / misalignment material is speculative; recommend a short chapter or omission.

- **[NEEDS-INFO] Aligned deep learning as random sampling (`book.tex` ch. 16).**
  Anchors: `ChapterDeepLearningEnsemble`, `ChapterDeepLearningMAP`,
  `ChapterDeepLearningSampling`, `ChapterMAPNull`, `ChapterHierarchicalBayes*`.

- **[NEEDS-INFO] Statistical Model Theory & priors where RH is true (`book.tex`
  ch. 17).** This is the most speculative; recommend recording it in `Issues.md`
  only, not as a chapter, unless the author wants it.

## 5. Process

- **[NOTE] Backups.** `lakefile.toml.bak`, `lake-manifest.json.bak` hold the
  pre-Verso state. `FORMALIZATION_ROADMAP.md.bak`, `RandomMap.lean_bk`, etc. are
  pre-existing and untouched.

- **[NEEDS-INFO] Desired output formats.** The book is configured for **single-page**
  HTML output (`emitHtmlSingle := .immediately`, `emitHtmlMulti := .no`; see §4); the
  rendered file is `_out/html-single/index.html`. TeX/PDF output (`emitTeX`) is
  disabled. If a PDF is wanted, enable it and resolve any KaTeX→TeX gaps.

## 7. New chapters added and remaining non-deferred gaps

- **[DONE] Five chapters added (July 2026)** to close the remaining non-deferred
  `book.tex` gaps. Each is anchored to `sorry`-free `BookProof` modules and follows
  the existing chapter conventions (`:::paragraph` prose, plain `#check` code blocks,
  `{ref}` cross-references):
  - `Book/ConditionalUnitary.lean` (tag `conditional-unitary`, Part II) — `book.tex`
    §3 "any conditional probability measure … is parametrized by a unitary operator":
    a joint density is `|U|²` on a column of a unitary (Gram–Schmidt), the converse
    `tr(BB†)=1 ⇒ p=|B|²`, the Hilbert–Schmidt boundedness of the kernel operator, the
    singular-value expansion `Ψ = W D U†`, and the marginal/regular-conditional
    reading `p(x)={B†B}(x,x)`, `p(x,y)=p(y|x)p(x)`. Anchors: `ChapterJointUnitary`
    (`exists_unitary_joint`, `sqAbs_isProb_of_frobenius_one`), `ChapterKernelBound`
    (`kernel_l2_bound`, `kernel_contraction`), `ChapterB3b` (`denseCore_svd`),
    `ChapterB3` (`IsPartialIsometry`, `conditional_operator_identity`),
    `ChapterConditional` (`pMarg_eq_diagBHB`, `pJoint_eq_cond_mul_marg`). The
    finite-dimensional core is proved; the abstract standard-measure-space layer is
    flagged (below).
  - `Book/SpinStatistics.lean` (tag `spin-statistics`, Part II) — `book.tex` §6: the
    two-mode fermionic CAR algebra on `ℂ⁴ ≅ ℂ² ⊗ ℂ²` (Jordan–Wigner), the
    anticommutation that distinguishes fermionic from bosonic statistics, and Pauli
    exclusion. Anchors: `BookProof.SpinStatistics` (`fermi_CAR₁/₂`, `fermiAnticomm_*`,
    `fermiAnnih₁_sq`, `fermiNumber_*`).
  - `Book/SymmetryRep.lean` (tag `symmetry-rep`, Part VI) — `book.tex` §7: a symmetry
    group of canonical transformations is a unitary representation; the one-parameter
    time-translation group `U(t)=e^{iHt}` as a `MonoidHom` into the unitary group.
    Anchors: `ChapterSymmetryRep` (`timeEvoRep`, `timeEvoU_mul`) + `ChapterConservative`
    (`timeEvo_unitary`).
  - `Book/TrajectoryReconstruction.lean` (tag `trajectory-reconstruction`, Part VI) —
    `book.tex` ch. 5 "Reconstruction of the trajectory": the three-instant collapsed
    Born process and the ABL post-selection formula. Anchors: `ChapterTrajectory`
    (`jointProb`, `finalProb`, `condProb`, `finalProb_total`,
    `jointProb_sum_final_eq_midProb`). The "symmetry-iff-deterministic" half
    (`ChapterReconstruct`) is left to `TimeTranslationStochastic` to avoid duplication.
  - `Book/SolovayTensor.lean` (tag `solovay-tensor`, Part V) — the author's central new
    goal: the tensor product of a finite-dimensional Hilbert space
    (`InnerHead N ≃ ℝ^N`) with a separable infinite-dimensional one
    (`InnerTail = L²[0,1]`); an arbitrary law on the finite part; and the Mehler measure
    forced on the infinite part because the cylindrical Kopperman language cannot
    distinguish tail points. Anchors: `ChapterSolovay` (`inner_reduces_to_head`,
    `headSumEquiv`, `only_mehler_on_tail`, `head_vs_tail_admissibility`),
    `ChapterSolovayCoordinates` (`tailTensorEquiv_map`, `finiteCoordinateMarginal`),
    `PnpProof.Kopperman` (`kopperman_substrate_separable`). Grounded in `book.tex`
    Intro (133–141), §3 (1467–1527), §5–6 (1802–1844).

- **[RESOLVED] The two items formerly flagged inside `SolovayTensor`.** Both are now
  `sorry`-free theorems: the **uniqueness** of the Mehler tail law from its finite
  marginals (`BookProof.ChapterMehlerUniqueness.mehler_unique_by_finite_marginals`,
  the forcing half of "only the Mehler measure") and the **measure-preservation** of
  the coordinate tail-split (`BookProof.ChapterSolovayCoordinates.tailSplitEquiv_map`).
  *Additions (August 2026):* `ChapterSolovayTailDimension` proves the Kopperman tail is
  infinite dimensional (`tail_infinite_dimensional`); `ChapterSolovayHilbertTensor`
  gives the Hilbert form of the identification (`solovayTensorUnitary`,
  `measurePreserving_solovayTensorEquiv`, and the pure-tensor inner product
  `inner_tensorLp`), with the completeness half — density of the span of pure tensors —
  explicitly *not* claimed, Mathlib having no Hilbert-space tensor product to state it
  against; and `ChapterSolovaySeparableExistence` supplies
  `joint_prob_has_wavefunction`, `exists_separable_prob_with_arbitrary_finite_law` and
  `prod_disintegration`.

- **[NEEDS-INFO] `book.tex` §3 abstract measure-theoretic layer.** The
  finite-dimensional algebraic core of §3 is now the `ConditionalUnitary` chapter
  (above). What remains open is the **abstract** layer for arbitrary standard measure
  spaces (possibly continuous): the classification of standard measure spaces
  (Lebesgue / discrete / mixture), the identification of commutative von Neumann
  algebras on a separable Hilbert space with `L∞(X,μ)` (`book.tex` 1426–1442), and
  regular conditional probabilities via disintegration on a standard Borel space
  (1479–1481). These were formalized only as `True` placeholders in
  `ChapterSelectingEvents` (`exists_regular_conditional_probability`,
  `vonNeumann_abelian_classification`, `selecting_events_not_rewriting_history`).
  **Update (August 2026):** the disintegration half is now a real theorem
  (`ChapterSolovaySeparableExistence.prod_disintegration` /
  `coordinateState_disintegration`, on a standard Borel second factor), and the
  *purely atomic* half of the abelian classification is proved in
  `ChapterAbelianAtomicCondensation` — `atomic_abelian_maximal_eq_diagonal` (a purely
  atomic maximal abelian algebra is exactly the diagonal algebra, i.e. `ℓ∞` of its
  index set) together with `atomic_measure_index_dichotomy` (a purely atomic index set
  is `Fin n` or `ℕ`). What remains genuinely open is the **diffuse** half: the
  spectral/Gelfand passage from an abstract abelian von Neumann algebra to an `L∞(μ)`
  model, for which Mathlib has no spectral theorem to build on. That is recorded as an
  exact obstruction in `BookProof/STATUS.md` and is *not* `sorry`-ed; the
  measure-theoretic splitting it would be applied to is available
  (`ChapterAtomicDecomposition.eq_continuousPart_add_atomicPart`).
  **Update (12 August 2026) — this item is now closed.**  The diffuse half was
  carried out: `ChapterLinftyMultiplication` (the `L∞(μ)` multiplication model),
  `ChapterAbelianGelfandModel` and `ChapterAbelianDirectSum` (every abelian algebra,
  presented as a unital `*`-representation of `C(X, ℂ)` or of a commutative unital
  C*-algebra, is a direct sum of multiplication algebras — no cyclic vector, no
  generator, no separability), `ChapterLpRestrictSplit` / `ChapterLpScaleMeasure` /
  `ChapterAbelianClassificationList` (the five-type list for a Borel probability
  measure on the line), `ChapterStandardBorelClassification` (transport to any
  standard Borel space, and each summand classified), and finally
  `ChapterSeparableSpectrum` and `ChapterSeparableL2Model`, which remove the
  metrizability hypothesis: it is *equivalent* to separability of the algebra, it is
  automatic for a separable commutative unital C*-algebra, and it is unnecessary
  altogether when the algebra acts on a separable Hilbert space
  (`abelian_multiplication_model_classified_separable_hilbert`).  All of this is
  `sorry`-free and `axiom`-free; only a nonseparably *acting* algebra is still
  outside the statement.

- **[NEEDS-INFO] `book.tex` ch. 6 black-hole information paradox (`book.tex`
  3445–3478).** The Stern–Gerlach half of this section is covered
  (`Book/SternGerlach.lean`); the black-hole-information-paradox half is physics-heavy
  and speculative. Recommend recording it here (or as a short note) rather than a full
  chapter unless the author wants it — the same disposition as the deferred physics
  sections in §6.

- **[NOTE] Remaining `book.tex` content (August 2026).** Every `book.tex` chapter
  except ch. 17 (Statistical Model Theory / priors where RH is true) now has a book
  chapter — the physics chapters formerly listed in §6 have been written up, so §6 is
  closed. The remaining open items are content-level, not chapter-level: (i) the
  *diffuse* half of the abstract measure-theoretic layer of §3 — **closed in August
  2026**, see the update two items above — and (ii) the black-hole-information
  sub-section of ch. 6, still a framing decision.

- **[RESOLVED] The `τ = n̄ + ½` zero-point postulate.** The half of the coherent-state
  temperature relation that used to be postulated is now derived in
  `BookProof/ChapterCoherentThermalFidelity.lean`: the coherent/thermal fidelity has the
  closed form `exp(−λ/(n̄+1))/(n̄+1)`, its width in `λ` is `n̄+1`, that width is unique,
  and the headline `thermalTemperature_eq_fidelity_width_sub_coherent_half` reads the
  temperature off as (fidelity width) − (coherent width), the coherent width being the
  `½`. Prose and `#check`s are in `Book/CoherentState.lean`.

- **[RESOLVED, 2026-08-12] The last two proof-plan formalization targets.** The
  appendix items §D (weak measurements / weak values) and §E (the dynamics-based
  "less arbitrary" unitary) are now proved, not planned:
  - `BookProof/ChapterWeakValue.lean` — the weak value
    `⟨A⟩_w = ⟨f|A|i⟩/⟨f|i⟩` on `Fin n → ℂ`: well-definedness and uniqueness off
    orthogonality, the diagonal collapse to the ordinary expectation (real for a
    Hermitian observable), linearity in the observable, the projector weak values
    summing to `1`, the ties to the ABL joint/conditional laws of
    `ChapterTrajectory`, and the double-slit capstone `dslit_weakValue`. Cited from
    `Book/DoubleSlit.lean`.
  - `BookProof/ChapterContinuityUnitary.lean` — the Weyl-symmetrized continuity
    generator `H = ½(p·v + v·p)` on a finite cyclic lattice (Hermitian, and *not*
    Hermitian without the symmetrization), the unitary `exp (i t H)` and its
    one-parameter group law, the Born recovery of a conditional probability
    (nonnegative, finitely additive, total mass `1`, packaged as a distribution and
    as the capstone `condProb_of_continuity`), and the finite tensor-product
    identification `L²(X) ⊗ L²(Z) ≅ L²(X × Z)`. Cited from
    `Book/ConditionalUnitary.lean`. The infinite-dimensional analytic realization
    remains the standing open layer, as elsewhere in the book.
  Both are `sorry`-free / `axiom`-free, registered in `BookProof.lean` and certified
  in `BookProof/ChapterRoadmapAudit.lean`; `Book/ProofPlans.lean` §D/§E now record
  them as PROVED.

- **[RESOLVED, 2026-08-12] Executable bits on the `patches/` shell scripts.** The
  four scripts (`apply-verso-patches.sh`, `build-book.sh`, `check-katex.sh`,
  `postprocess-html.sh`) are tracked with mode `100755` again, so
  `./patches/build-book.sh` runs from a fresh clone.

- **[RESOLVED, 2026-08-12] Verso emphasis warnings.** Three `**not**` spans in
  `Book/OdeSingularity.lean` triggered the Verso markup linter (in Verso, `*` is
  bold and `**` is bold-inside-bold); they are now single-starred, and the `Book`
  target builds warning-free.
