# PLAN B — Prose Verification & Book Build (Track B)

**Owner:** LLM-Lean-Specialist-B  
**Machine:** Machine B  
**Target files:** `Book/*.lean` (all prose chapters), `Issues.md`, `Book.lean`, `BookMain.lean`  
**Hard constraints:** Never writes `BookProof/*.lean`, `Singularity/*.lean`, `Singularity/`, `RiemannProof/`

---

## Task B1: Book Honesty-Flag Refresh (Priority 5 + 8.5)

**Goal:** Update prose to reflect that ODE theorems are now proved, not placeholders.

### B1.1 Update `Book/OdeSingularity.lean`

**File:** `Book/OdeSingularity.lean`

Current state (lines 116–120, 151–153, 175–180):
- Lines 116–120: "Nelson's theorem is a deep result... its formal proof... is one of the main open items"
- Lines 151–153: "This complexification argument is the mathematical heart... but it is **not yet formalized**"
- Lines 175–180: Lists `nelson_essential_self_adjoint`, `weyl_symmetrization_self_adjoint` as placeholders, complexification resolution as "not formalized"

Changes needed:
1. Lines 116–120: Replace placeholder note with verified statement. Nelson's theorem
   is formalized in `Singularity/Esa.lean` (`nelson_essential_self_adjoint`).
   Add `#check` block showing the theorem statement.
2. Lines 151–153: Replace "not yet formalized" with verified statement. Complexification
   resolution is in `BookProof/ChapterOdeComplexification.lean` (`ae_no_real_singular_time`).
   Add `#check` block showing the theorem statement.
3. Lines 175–180: Move `nelson_essential_self_adjoint` and `weyl_symmetrization_self_adjoint`
   to the "Genuinely proved" list. Remove complexification from "Placeholders or open".
4. Update the `# What Is Verified, and What Is Open` section to reflect current state.

### B1.2 Update `Book/Introduction.lean`

**File:** `Book/Introduction.lean`

Current state (lines 350–354):
```
: Part IV — Resolution of the Singularity of an ODE

  An operator-theoretic resolution of the blow-up of $`x' = x^2`, via
  Koopman–von Neumann theory, Weyl quantization, and Nelson's essential
  self-adjointness theorem.
```

Changes needed:
1. Update to mention that the resolution is now fully formalized (ODE.tex + complexification).
2. Add `#check` blocks for the three key theorems: `weyl_symmetrization_self_adjoint`,
   `nelson_essential_self_adjoint`, `ChapterOdeComplexification.ae_no_real_singular_time`.

### B1.3 Update `Issues.md` §3 (ODE formal status)

**File:** `Issues.md`

Current state (lines 69–75):
```
- **Honesty flags carried into the text:** the ODE chapter states explicitly that
  `weyl_symmetrization_self_adjoint` (proves only `True`) and
  `nelson_essential_self_adjoint` (discards its hypothesis) are **placeholders**,
  and that the complexification resolution is **not formalized**...
```

Changes needed:
1. Update §3 to reflect that all three are now proved and `sorry`-free.
2. Remove the "not formalized" references.
3. Update the "Current state of this deliverable" section (§0b) if needed.

---

## Task B2: Verify Formal Anchors (Priority 8.2)

**Goal:** For each `Book/*.lean` chapter, confirm every cited `BookProof` theorem
is `sorry`-free and its statement matches the prose claim.

### B2.1 Systematic verification

**Files:** All `Book/*.lean` files

For each chapter in `Book/`:
1. Extract every `BookProof.*` theorem citation (via `#check` or prose references).
2. Check that the theorem exists in the corresponding `BookProof/*.lean` file.
3. Verify with `lean_verify` that it is `sorry`-free and axiom-clean.
4. Flag any mismatches between the prose claim and the formal statement.

### B2.2 Cross-check `Book/ProofPlans.lean`

**File:** `Book/ProofPlans.lean`

The sketch proofs in `Book/*.lean` were re-derived, not transcribed. Verify that
the sketch proofs in `Book/ProofPlans.lean` match the formal proofs in
`BookProof/*.lean`. Flag any discrepancies.

---

## Task B3: Confirm Build Integrity (Priority 8.1)

**Goal:** Run end-to-end builds and confirm clean, `sorry`-free, `axiom`-free results.

### B3.1 Full build

```bash
export PATH="/home/leo/.elan/bin:$PATH"
cd /media/leo/e7ed9d6f-5f0a-4e19-a74e-83424bc154ba/timepiece
lake build BookProof
lake build Singularity
lake build book && lake exe book
```

### B3.2 Check for `sorry` and `admit`

```bash
rg -c sorry BookProof/
rg -c sorry Book/
rg -c admit BookProof/
rg -c admit Book/
```

### B3.3 Check for non-standard axioms

For each `BookProof/*.lean` module, verify:
```lean
#check axioms <module_name>
```
Should only show `propext`, `Classical.choice`, `Quot.sound`.

### B3.4 Check for API drift

Compare the current build output against the last known-good build (documented
in `ARISTOTLE_SUMMARY.md` or `Issues.md`). Report any new warnings or errors.

---

## Task B4: The 26-Include Verso Elaboration Limit (Priority 8.3 + Priority 4)

**Goal:** Investigate and resolve the 26-`{include}` elaboration limit in the
Verso book build.

### B4.1 Understand the failure

**Symptoms:**
- Root `#doc` fails with 26 `{include}`d chapters.
- 25 chapters work fine.
- The error is: `invalid {...} notation, expected type is not of the form (C ...) /
  Verso.Doc.Genre.PartMetadata ?m.…` — a stuck `PartMetadata ?m` genre metavariable.
- `experimental.module` and `autoImplicit = false` were tried and commented out.
- Raising `maxSynthPendingDepth` did NOT remove the limit.

### B4.2 Investigate Verso source

Inspect `Verso/Doc/Elab.lean` (in the lake dependencies or Mathlib cache) for:
- `includeSection`, `closePartsUntil`, `addPart` — the part elaboration functions.
- Look for a fixed bound, a fold that nests unifications, or a metavariable-batching
  limit.
- Check if the limit is on total includes (not top-level parts).

### B4.3 Try scoped `set_option` fixes

The most promising approach (per BOOK_PROOF_PLAN.md §4):
- Try `set_option maxRecDepth N` or `set_option maxHeartbeats N` scoped to `Book.lean`
  via `set_option … in #doc …`.
- Focus on the part-term construction at the end of `#doc` elaboration.

### B4.4 If `set_option` fails: reduce include count

If no `set_option` fix works, reduce to ≤ 25 includes by:
- Merging two short chapters into one `#doc` module with two top-level `#` sections.
- Candidate merge: `Book/ClassicalLimit.lean` into a neighbouring foundations chapter.
- This is reliable but changes book granularity.

### B4.5 If all else fails: split into two volumes

Split the manual into two `#doc` volumes (Parts I–III and Parts IV–VI) rendered
separately. This is the fallback if a single volume cannot be made to elaborate.

**Note:** Do NOT re-introduce `experimental.module` or `autoImplicit = false`;
keep `maxSynthPendingDepth` at its working value.

---

## Task B5: Restate Long #check Types (Priority 8.4) — Prose Side

**Goal:** For the worst-offending `#check` blocks in `Book/*.lean`, add clean
restated `example`/`theorem` with short types in the prose.

**Files:** `Book/*.lean` (selected chapters)

Target: `#check` blocks that render as unreadable long types in the HTML book.
Add a clean `example` with a short type and a prose paraphrase.

---

## Execution Order

```
B1 (Priority 5/8.5 — Honesty-flag refresh)
  → B2 (Priority 8.2 — Verify formal anchors)
  → B3 (Priority 8.1 — Build integrity)
  → B4 (Priority 8.3/4 — Verso elaboration limit)
  → B5 (Priority 8.4 — Restate #check types, prose side)
```

B1–B3 are independent and can be worked on in parallel.
B4 is independent.
B5 depends on B1–B4 (knows which #check blocks need restating).

---

## Summary

| Task | File(s) | Content | Status |
|------|---------|---------|--------|
| B1 | Book/OdeSingularity.lean, Book/Introduction.lean, Issues.md | Honesty-flag refresh (5 + 8.5) | TODO |
| B2 | All Book/*.lean, Book/ProofPlans.lean | Verify formal anchors (8.2) | TODO |
| B3 | BookProof/, Book/, lakefile.toml | Build integrity + axiom check (8.1) | TODO |
| B4 | Verso/Doc/Elab.lean (investigate), Book.lean | 26-include Verso limit (8.3 + 4) | TODO |
| B5 | Book/*.lean (selected) | Restate long #check types, prose side (8.4) | TODO |

---

## Coordination with Plan A

| Plan A (Track A) | Plan B (Track B) |
|------------------|-------------------|
| MODIFIES: `BookProof/*.lean` | MODIFIES: `Book/*.lean`, `Issues.md` |
| READ-ONLY: `Singularity/*.lean` | NEVER touches `Singularity/` |
| NEVER touches `Book/` | NEVER touches `BookProof/` |
| **Target:** Tensor product, book.tex claims, #check cleanup | **Target:** Prose updates, honesty flags, build verification, Verso limit |

**Zero file overlap. Both plans compile the same project.**
