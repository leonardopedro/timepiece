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
- **The book builds and renders.** `lake build book && lake exe book` produces
  ~118 HTML pages under `_out/html-multi/`. Prose, KaTeX math, and the Lean
  statement code blocks (`<pre>`) all render. Note: with `htmlDepth := 2` each
  chapter has a landing page and its **sections are sub-pages** — the body content
  (prose/math/code) lives in the section sub-pages, not the chapter landing page.
- **18 chapters** written: Introduction; Part I (Dutch book, sequential Bayes,
  max-entropy, total variance); Part II (probability clock/Euler, Born reproduces,
  gauge fiber, Stern–Gerlach, free field); Part III (irreversibility, bijection
  probability, null measure, baryon asymmetry, law of large numbers); Part IV (ODE
  singularity, from `ODE.tex`); Part V (PA-free Hilbert space, from `newproof.md`);
  and the proof-plans appendix.
- **Lean statements are shown as plain (non-elaborated) code blocks.** Verification
  is anchored on `lake build BookProof`. Upgrading to elaborated blocks
  (`public import` + `experimental.module`) and to verso-blueprint are planned
  (`BOOK_PROOF_PLAN.md` §3).
- **Honesty flags carried into the text:** the ODE chapter states explicitly that
  `weyl_symmetrization_self_adjoint` (proves only `True`) and
  `nelson_essential_self_adjoint` (discards its hypothesis) are **placeholders**,
  and that the complexification resolution is **not formalized**; the PA-free
  chapter separates the **verified** Riesz–Fischer core
  (`completeSpace_iff_summable_norm`) from the **metamathematical** "no PA leak"
  interpretation.

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

- **[NOTE] `book` is intentionally NOT a default target.** `defaultTargets` is still
  `["PnpProof", "BookProof"]`, so a bare `lake build` does not build the book and
  the existing CI behaviour is unchanged. Build the book with `lake build book`.

## 2. Content and curation

- **[CRITIQUE] This is a curated edition, not a full conversion.** `book.tex` has
  ~30 chapters; this edition presents ~17. Omitted threads include: reconstructing
  the classical trajectory, gauge symmetry & dissipative dynamics, real
  representations / CPT / relativistic position operator, Yang–Mills quantization,
  the Gribov ambiguity, physical parity & antiparticles, diffeomorphisms & gravity,
  and the consciousness-as-prior chapter (only its null-measure lemma is used).
  These omissions should be confirmed as acceptable, or the selection widened.

- **[UNCERTAIN] Sketch proofs were re-derived, not transcribed.** The sketch proofs
  in the chapters were written from the `BookProof` docstrings (`STATUS.md`), the
  theorem statements, and standard mathematics — and in places *improved* for
  pedagogy, as permitted. They were **not** line-by-line checked against the
  corresponding `book.tex` passages. The Dutch-book, Bayes, max-entropy, and
  total-variance sketches are standard and low-risk; any chapter making a less
  standard claim should be cross-checked against `book.tex` before publication.

- **[NEEDS-INFO] Author intent for the "central thesis".** The Introduction states
  the slogan "quantum mechanics is what probability theory looks like when you
  parametrize the simplex by the sphere." This is my synthesis of the manuscript's
  themes; the author should confirm it faithfully represents the intended message
  and tone.

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

- **[UNCERTAIN] KaTeX coverage.** Display/inline math is written as `` $`…` `` /
  `` $$`…` `` and rendered by KaTeX. Most constructs used (sums, fractions,
  `pmatrix`, `\mathbb`, `\mathrm`) are standard KaTeX, but this has not yet been
  confirmed against the rendered HTML. Matrices in particular should be spot-checked.

- **[CRITIQUE] Some `#check` types are very long.** A few headline theorems
  (e.g. the free-field and measure-theoretic ones) have large elaborated types that
  may render unwieldily. For the worst offenders it may be worth adding a short
  prose paraphrase immediately above the block (already done for most), or restating
  a clean `example` instead of `#check`.

## 5. Process

- **[NOTE] Backups.** `lakefile.toml.bak`, `lake-manifest.json.bak` hold the
  pre-Verso state. `FORMALIZATION_ROADMAP.md.bak`, `RandomMap.lean_bk`, etc. are
  pre-existing and untouched.

- **[NEEDS-INFO] Desired output formats.** Currently only HTML multi-page output is
  configured (`emitHtmlMulti := .immediately`). TeX/PDF output (`emitTeX`) is
  disabled. If a PDF is wanted, enable it and resolve any KaTeX→TeX gaps.
