# BOOK_PROOF_PLAN.md — Tasks for the LLM Lean 4 Specialist (Aristotle)

This file is the machine-oriented companion to the book appendix
(`Book/ProofPlans.lean`). It lists the precise Lean 4 tasks that remain to make the
book's claims fully verified, plus the tooling migrations.

**Target environment (do not change without coordination):**
- Lean toolchain: `leanprover/lean4:v4.28.0` (see `lean-toolchain`)
- Mathlib: `v4.28.0`
- The `BookProof` library must remain `sorry`-free and `axiom`-free (only
  `propext`, `Classical.choice`, `Quot.sound`). Verify with
  `lake build BookProof` and `#print axioms <name>`.
- Stay compatible with `aristotle.harmonic.fun`.

**Verification commands:**
```bash
export PATH="/home/leo/.elan/bin:$PATH"
cd RiemannProof   # this repository root
lake build BookProof          # the verified mathematics
lake build book && lake exe book   # the Verso book -> _out/html-multi/
```

---

## Priority 1 — ODE chapter (`Singularity/`)

The `Singularity` library is `sorry`-free, but two headlines are **placeholders**
and the analytic resolution is absent.

### 1.1 Self-adjointness of the Weyl Hamiltonian
- **File:** `Singularity/Hamiltonian.lean`
- **Current (stub):** `weyl_symmetrization_self_adjoint {M} (sys) : True := by trivial`
- **Replace with:** a real symmetry statement for `odeToHamiltonian sys`.
- **Math:** with `p̂ = -i ∂ₓ`, `(f·p̂)† = p̂·f` and `(∂f)† = -∂f`, so the
  Weyl-symmetrized `½(f·p̂ + p̂·f)` is symmetric.
- **Steps:**
  1. Define an adjoint involution `adj : NormalOrderedOp M → NormalOrderedOp M`
     on the Wick algebra in `Singularity/Poly.lean`.
  2. Prove `adj_mulXMode`, `adj_mulPMode` (the two identities above) by induction
     on normal-ordered terms (use the existing `wickCoeff`/`wickTerm`).
  3. Prove `adj_odeToHamiltonian : adj (odeToHamiltonian sys) = odeToHamiltonian sys`.
  4. Restate the theorem as this equality (or a `IsSymmetric`-style predicate).

### 1.2 Nelson's essential-self-adjointness theorem
- **File:** `Singularity/Esa.lean`
- **Current (stub):** `nelson_essential_self_adjoint` is marked "Placeholder"; its
  body is `intro h_esa; exact (analyzeClassicalFlow sys 0).isComplete` (discards the
  hypothesis).
- **Goal:** prove the Nelson analytic-vector theorem and apply it:
  `isEssentiallySelfAdjoint (odeToHamiltonian sys) ↔ (analyzeClassicalFlow sys 0).isComplete`.
- **Steps:**
  1. Formalize analytic vectors and the Nelson–Gårding theorem (a symmetric operator
     with a dense set of analytic vectors is essentially self-adjoint).
  2. Use the existing `deficiencyIndices` to state essential self-adjointness as
     `deficiencyIndices H = (0,0)`.
  3. Connect flow completeness (`Singularity/Flow.analyzeClassicalFlow`) to the
     existence of enough analytic vectors (the hard analytic step).
- **Note:** This is the largest item. It is acceptable to first prove the
  finite-dimensional / bounded truncation and mark the unbounded analytic-vector step
  clearly.

### 1.3 Complexification resolution (no finite-time singularity in L²(ℝ²))
- **Suggested file:** new `BookProof/ChapterOdeComplexification.lean` (keep it
  `sorry`-free, axiom-clean, register in `BookProof.lean`).
- **Goal:** for `ż = z²` on `ℂ ≃ ℝ²`, the set of initial data with a **real**
  singular time has measure zero.
- **Statements to prove:**
  - `complex_solution (z0 : ℂ) (hz0 : z0 ≠ 0) : ∃ z : ℝ → ℂ, ... z t = z0 / (1 - t*z0)`
  - `singular_time_real_iff_im_zero : (1 / z0).im = 0 ↔ z0.im = 0`
  - `real_axis_volume_zero : volume {z : ℂ | z.im = 0} = 0`  (the line `{y=0}` is
    null in `ℝ²`; style after `ChapterConsciousnessNullMeasure.countable_volume_zero`)
  - **HEADLINE** `ae_no_real_singular_time : ∀ᵐ z0 ∂volume, (1 / z0).im ≠ 0`
- **Dependencies:** `MeasureTheory`, `Complex`, `Measure.pi`.

### 1.4 Energy-bounded initial conditions
- **Depends on 1.2** (spectral theorem for the essentially self-adjoint `H`).
- **Goal:** `‖H ψ‖ ≤ E_max ‖ψ‖` for `ψ` in the spectral subspace `[-∞, E_max]`,
  hence `‖∂ₜ ψ(t)‖` is uniformly bounded (no finite-time blow-up).

---

## Priority 2 — PA-free chapter

### 2.1 Instantiate the verified analytic core (short)
- **Suggested file:** new `BookProof/ChapterPaFreeCompletion.lean`.
- **Goal:** instantiate Mathlib's Riesz–Fischer characterization for the
  finitely-supported core and its completion.
- **Statements:**
  - Define `DenseCore P := P →₀ ℝ` (or `→₀ ℝ_alg` if a real-algebraic type is wanted).
  - `instance : CompleteSpace (UniformSpace.Completion (DenseCore P))`
    := `UniformSpace.Completion.completeSpace _`
  - `#check @completeSpace_iff_summable_norm` applied to `DenseCore P`.
  - `definable_vectors_have_finite_support (v : DenseCore P) :
       (Function.support v).Finite` := `Finsupp.finite_support v`
  - `infinite_vectors_are_null_events` under a diffuse measure
    (use `MeasureTheory.Measure.noAtoms` / `measure_singleton`).

### 2.2 Definability / conservativity fragment (research-scale; scope carefully)
- The full claim "the completion does not leak PA / is a conservative decidable
  extension" is **metamathematical** and is NOT to be presented as a Lean theorem.
- Formalize only the precise, provable fragment: *in the language whose vector
  constants are finitely supported, every term-denotable vector is finitely
  supported* (this is essentially `Finsupp.finite_support`).
- Document explicitly (in the book and here) that the conservativity/non-definability
  step is interpretation, not a proved theorem. Do **not** claim it as verified.

---

## Priority 3 — Book tooling

### 3.1 Inline-elaborated Lean blocks (optional polish)
- Currently the book shows Lean statements as **plain code blocks**; verification is
  via `lake build BookProof`.
- To elaborate them in-book: enable `experimental.module` for the `Book` lib and
  `book` exe in `lakefile.toml`, change each chapter's `BookProof` import to
  `public import BookProof.<Module>`, re-add the imports, and verify one chapter at a
  time. (This re-introduces Mathlib *elaboration* into the book build — slower — but
  does **not** rebuild Mathlib.)
- Risk: `experimental.module` interaction with non-module Mathlib oleans; test
  incrementally.

### 3.2 Migration to verso-blueprint (deferred — toolchain blocker)
- **Blocker:** `verso-blueprint` requires Lean **≥ v4.29.0**; this project is on
  **v4.28.0** (Mathlib v4.28.0, `BookProof`). verso-blueprint elaborates the
  declarations it documents, so it needs the same toolchain as the code.
- **Execute only when a toolchain is available that is BOTH verso-blueprint-compatible
  AND supported by `aristotle.harmonic.fun`.** Then:
  1. Bump `lean-toolchain` + Mathlib to that version; `lake exe cache get`; re-verify
     `BookProof` (watch for API drift).
  2. Pick a stable label scheme mirroring the chapters (e.g.
     `dutch_book_coherent_iff`, `euler_sum_one`, `total_variance`,
     `born_fiber_complex`, `bijProb_tendsto_zero`).
  3. Tag featured `BookProof` theorems with `@[blueprint "label"]`
     (`autoDeps := true` where useful).
  4. Port the existing prose/sketch proofs into blueprint blocks
     (`:::theorem "label" (uses := ...)`, `:::proof`, `{uses ...}`/`{bpref ...}`).
  5. `lake exe vbp build`; inspect progress + dependency views.
- The Verso markup already written ports with modest edits; the prose is reusable.

---

## Notes for the specialist
- The book's chapters are in `Book/*.lean`; the root is `Book.lean`; the generator is
  `BookMain.lean`. Build with `lake build book && lake exe book`.
- Verso markup gotchas already hit (avoid): no `>` blockquotes; keep `**bold**` on a
  single line; close `:::paragraph` with `:::` before opening another (or just use
  plain blank-line-separated paragraphs); inline `{lean}`...`` elaborates its content
  (so it fails on free variables / `#check`) — use plain backticks for schematic code.
- See `Issues.md` for open uncertainties and constructive criticism.
