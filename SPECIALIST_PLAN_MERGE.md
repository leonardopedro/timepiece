# Specialist Plan — Aristotle Merge Verification + Pauli–Grover (§11)

## Context

Two changes were made to the live tree and need build verification by the
specialist (the orchestrator must not run long compiles).

### 1. Aristotle merge (build-cleanups only — no new proofs)

The Aristotle output at
`/home/leo/Downloads/5797690b-cbbf-4c1a-935c-257fe1dc80c9-aristotle/output-final_aristotle`
is a divergent snapshot whose latest run was a **build-repair / warning-cleaning /
Verso-markup pass** (see its `ARISTOTLE_SUMMARY.md`). It added **no proofs**
(actual `sorry`-tactic count is `1` in both trees).

**Crucially, Aristotle's snapshot EXCLUDED `UsedRoute/`, `UnusedRoute/`,
`PnpProof/`** (its `lakefile.toml` says "PnpProof is not included in this
repository snapshot"). Therefore Aristotle *removed* the five `PnpProof`-importing
modules from the `BookProof.lean` aggregate. The live tree HAS `PnpProof`, so those
modules must stay imported.

What was overlaid onto the live tree (via `rsync -ac`, no `--delete`):
- `BookProof/` — 71 files (mostly removed unused simp arguments, e.g.
  `simp +decide` → `simp +decide [ Module.finrank_pi ]` direction is LIVE-has-more;
  Aristotle's versions have FEWER explicit args).
- `Singularity/` — 6 files (`EnergyBounded`, `Esa`, `Hamiltonian`, `Poly`, `Report`,
  `Tests`) — warning cleanups.

Also overlaid (after the author confirmed indifference to bold vs italic):
- `Book/` (31 chapters) and `Book.lean` — Aristotle's `**bold**` → `*italic*`
  conversion. Verified **purely cosmetic**: normalizing live's `**`→`*` makes every
  file byte-identical to Aristotle's, and the §4.7 `SequentialBayes` content is intact.

What was **deliberately NOT overlaid** (live versions kept):
- `lakefile.toml` — live keeps `defaultTargets = ["PnpProof", "BookProof"]`
  (Aristotle's dropped `PnpProof`).
- `BookProof.lean` — live keeps the imports of `Substrate`, `ChapterSolovay`,
  `ChapterSolovayCoordinates`, `ChapterG3`, `ChapterKopperman` (Aristotle removed
  them) **and** the new `import BookProof.ChapterPauliGrover`.

The five `PnpProof`-importing modules (`Substrate`, `ChapterKopperman`, `ChapterG3`,
`ChapterSolovay`, `ChapterSolovayCoordinates`) were verified **byte-identical**
between Aristotle and live, so the overlay did not alter them.

A safety backup of the pre-merge `BookProof.lean`, `lakefile.toml`, `Book.lean` is at
`/media/leo/e7ed9d6f-5f0a-4e19-a74e-83424bc154ba/containers/tmp/opencode/merge_backup/`.

### 2. New module `BookProof/ChapterPauliGrover.lean`

A new sorry-free module formalizing the ideal (`a = 1`) Pauli–Grover rotation as a
concrete unitary parametrization of a deterministic regular conditional probability
(the running example for book §11). It reuses `BookProof.ChapterConditional`
(`pJoint`/`pMarg`/`pCond`). It is imported in `BookProof.lean`.

Declarations: `pauliX`, `pauliX_conjTranspose`, `pauliX_sq`, `pauliX_unitary`,
`pauliX_rotates`, `pauliX_parametrizes_delta`, `pauliGrover_joint_one`,
`pauliGrover_marg_one`, `pauliGrover_cond_one`.

The orchestrator wrote build-fix edits but **never confirmed it compiles**. Known
fixes already applied: `Matrix.mem_unitaryGroup` (does not exist) →
`Matrix.mem_unitaryGroup_iff` + `star_eq_conjTranspose`; removed redundant
`norm_num` / `Matrix.one_apply` simp args that `simp` already discharged.

## Definition of done

```bash
export PATH="/home/leo/.elan/bin:$PATH"
lake build BookProof      # exits 0  (validates Aristotle cleanups + ChapterPauliGrover)
lake build Singularity    # exits 0  (validates Aristotle Singularity cleanups)
lake build book           # exits 0  (after Priority 3 prose is added)
```
- `grep -rn "sorry" BookProof/ChapterPauliGrover.lean` is empty.
- `BookProof.lean` still imports `Substrate`, `ChapterSolovay`,
  `ChapterSolovayCoordinates`, `ChapterG3`, `ChapterKopperman`, `ChapterPauliGrover`.
- `lakefile.toml` still has `defaultTargets = ["PnpProof", "BookProof"]`.
- After Priority 3: `python3 /media/leo/e7ed9d6f-5f0a-4e19-a74e-83424bc154ba/containers/tmp/opencode/verify_refs.py`
  reports `NOT FOUND : 0`, and `Book/ConditionalUnitary.lean` lints clean.

## Priority 1 — Verify the merge builds

Run `lake build BookProof` and `lake build Singularity`. Aristotle's cleanups were
produced in a tree WITHOUT `PnpProof`; re-confirm they compile in the live tree
(WITH `PnpProof`). If a removed simp argument turns out to be needed here, restore
just that argument. **Do not** remove the `PnpProof`-module imports from
`BookProof.lean`, and **do not** edit `lakefile.toml` `defaultTargets`.

## Priority 2 — Finish `ChapterPauliGrover.lean`

Ensure all nine declarations elaborate sorry-free. If a tactic fails, prefer the
minimal fix consistent with the existing style (`ext`/`fin_cases`/`simp`/`norm_num`
over `Fin 2`). The headline theorem is `pauliGrover_cond_one : pCond pauliX 0 1 = 1`.
Keep lines ≤ 100 chars; no trailing whitespace.

## Priority 3 — Add the Pauli–Grover section to §11 (`Book/ConditionalUnitary.lean`)

§11 is the rendered chapter "Conditional Probability Is Parametrized by a Unitary"
(`Book/ConditionalUnitary.lean`, `tag := "conditional-unitary"`). Add a new section
after "# Marginal and Conditional Probability" (or before "# What Is Verified…"):

```
# A Concrete Parametrization: the Pauli–Grover Rotation
```

Content (source: `QFM.tex`, `\section{Alternate Hamiltonian: the Pauli--Grover
construction}`, `\label{sec:pauli-grover}`): present the Pauli–Grover Hamiltonian
`H_PG` acting as a Pauli-X rotation in the two-dimensional subspace
`{ |i,0⟩, |i,f_i⟩ }`; at `a = 1` it is the swap, so evolving `|0⟩` for `τ = π/2`
yields `|f⟩` up to an unobservable global phase; the readout
`p(f|i) = |⟨i,f| e^{-iH_PG π/2} |i,0⟩|² = 1` is a **deterministic** regular
conditional probability (perfect training accuracy). Frame it as a concrete
finite-dimensional instance of the abstract theorem of this chapter. Describe the
imperfect-rotation case `a < 1`, the many-input sum, and the Krylov start vector as
prose (not formalized).

`#check` anchors to use (each on its own line inside a ``` ```lean block):
- `@BookProof.ChapterPauliGrover.pauliX_unitary`
- `@BookProof.ChapterPauliGrover.pauliX_rotates`
- `@BookProof.ChapterPauliGrover.pauliX_parametrizes_delta`
- `@BookProof.ChapterPauliGrover.pauliGrover_cond_one`
- existing: `@exists_unitary_joint`, `@pCond`, `@pJoint_eq_cond_mul_marg`

(Note: the `#check` blocks are plain code verified by `verify_refs.py` via grep, not
elaborated by the book build — the names must simply exist in `BookProof`.)

### Book markup conventions (must follow — the book lints these)
- No `>` blockquotes.
- Inline math is `` $`…` `` — the closing delimiter is a BACKTICK.
- `:::paragraph` … `:::` must be balanced.
- Lines ≤ 100 chars (pre-existing display-math lines may exceed).
- Multi-line `**bold**` is OK **unless math is inside the bold** (then keep the
  bold span on one line).
- Cross-refs: `{ref "tag"}[text]`. Useful tags: `conditional-unitary`,
  `born-reproduces`, `symmetry-rep`, `collapse-kolmogorov`, `born-fiber`.

After editing: run `verify_refs.py` (expect `NOT FOUND : 0`) and lint the file
(paragraphs balanced, no math-in-multiline-bold, no missing refs).

## Priority 4 — Book/ bold→italic: APPLIED (verify only)

Aristotle's `**bold**` → `*italic*` conversion across all 31 `Book/` chapters and
`Book.lean` is **already applied** (the author is indifferent to bold vs italic). No
action needed beyond confirming `lake build book` exits 0 and the rendered HTML still
shows the emphasis. If the build emits the `linter.verso.markup.emph` note, that is
expected and non-fatal.

## Build / render commands (for reference)

```bash
export PATH="/home/leo/.elan/bin:$PATH"
lake build BookProof
lake build Singularity
./patches/apply-verso-patches.sh        # idempotent; needed after fresh .lake
lake build book && lake exe book
./patches/postprocess-html.sh           # -> _out/html-single/index.html
```
