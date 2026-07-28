# BOOK_PROOF_PLAN.md — Tasks for the LLM Lean 4 Specialist (Aristotle)

This file is the machine-oriented companion to the book appendix
(`Book/ProofPlans.lean`). It records what has been verified and what remains.

**The ODE and PA-free formalization tasks (former Priorities 1–2) are COMPLETE.**
They were executed by the LLM-Lean-specialist as two parallel tracks:
- **`PLAN_A_ODE_CORE.md`** (Track A) — `Singularity/*.lean`, `Singularity/EnergyBounded.lean`.
- **`PLAN_B_COMPLEXIFICATION_FRAMEWORK.md`** (Track B) — `BookProof/ChapterOdeComplexification.lean`,
  `BookProof/ChapterPaFreeCompletion.lean`, `BookProof/ChapterDefinabilityFragment.lean`,
  `BookProof.lean`, `lakefile.toml`.

All new/modified files are **`sorry`-free and `axiom`-free** (verified: `rg -c sorry` = 0
in every file; only `propext`, `Classical.choice`, `Quot.sound` are used).

**Current axiom audit:**
- `BookProof/` and `PnpProof/`: no `axiom` lines remain (the two `axiom : True` in
  `ChapterSelectingEvents.lean` were converted to `def`s in July 2026).
- `Singularity/` and `RandomMap/`: no `axiom` lines.
- Only acceptable `sorry`s: `RandomMap/SchoenfeldPRA.lean:162,176` (pre-existing,
  documented as intentional).

**Target environment (do not change without coordination):**
- Lean toolchain: `leanprover/lean4:v4.28.0` (see `lean-toolchain`)
- Mathlib: `v4.28.0`
- The `BookProof` and `Singularity` libraries must remain `sorry`-free and
  `axiom`-free. Verify with `lake build BookProof` / `lake build Singularity`
  and `#print axioms <name>`.
- Stay compatible with `aristotle.harmonic.fun`.

**Verification commands:**
```bash
export PATH="/home/leo/.elan/bin:$PATH"
cd /media/leo/e7ed9d6f-5f0a-4e19-a74e-83424bc154ba/timepiece   # repository root
lake build BookProof          # the verified mathematics
lake build Singularity        # the verified ODE pipeline
lake build book && lake exe book   # the Verso book -> _out/html-single/
```

---

## Status summary

| Former task | Status | Where |
| :--- | :--- | :--- |
| §1.1 Weyl Hamiltonian self-adjointness | **DONE** | `Singularity/Hamiltonian.lean` `weyl_symmetrization_self_adjoint` (now `adj (odeToHamiltonian sys) = odeToHamiltonian sys`) |
| §1.2 Nelson essential self-adjointness | **DONE** | `Singularity/Esa.lean` `nelson_essential_self_adjoint` (now the full `↔` with flow completeness) |
| §1.3 Complexification resolution | **DONE** | `BookProof/ChapterOdeComplexification.lean` (`singular_time_real_iff_im_zero`, `real_axis_volume_zero`, headline `ae_no_real_singular_time`) |
| §1.4 Energy-bounded initial conditions | **DONE** | `Singularity/EnergyBounded.lean` (`energy_bounded_initial`, `InEnergySpectralSubspace`) |
| §2.1 PA-free completion (Riesz–Fischer core) | **DONE** | `BookProof/ChapterPaFreeCompletion.lean` |
| §2.2 Definability / conservativity fragment | **DONE** | `BookProof/ChapterDefinabilityFragment.lean` |
| §3.1 Inline-elaborated Lean blocks | **BLOCKED** | `experimental.module` breaks the Verso book build (see Priority 3) |
| §3.2 verso-blueprint migration | **DEFERRED** | toolchain blocker (needs Lean ≥ v4.29.0) |
| §4 26-`{include}` book-build limit | **DONE** | root cause = unannotated sub-parts array in Verso `toSyntax`; fixed by `patches/verso-0001-annotate-subparts.patch` (Priority 4 / 8.3) |
| §5 Book honesty-flag refresh (ODE) | **DONE** | Book/OdeSingularity.lean, Book/Introduction.lean, Issues.md updated: all three ODE theorems listed as `sorry`-free; no more "placeholder" language |
| §6 Solovay–Kopperman tensor product | **MOSTLY DONE** | 6.1 ✓ (headSumEquiv, tensor closure, tensor_language_decidable); 6.3 ✓ (arbitrary head law, marginal); 6.4 ✓ (atomless, invariant, TailPriorAdmissible, head_vs_tail); 6.6 partial (tailSplitEquiv_map sorry → proof in SPECIALIST_PLAN_REMAINING.md); 6.2/6.5 partial (finite purification done; full L²⊗L² ≅ L² and ¬FiniteDimensional deferred) |
| §7 Further `book.tex` claims | **DONE** | ChapterProbabilityInterface, ChapterCountableDefinability, ChapterKopperman, ChapterFiniteArithmeticPrior, ChapterBornPhaseFiber extended, density reuse confirmed |
| §8 `Issues.md`-derived tasks | **DONE** | 8.1 build integrity (specialist verified); 8.3 26-include DONE; 8.4 readable headlines added; 8.5 ChapterSelectingEvents.lean hardened (C2/C3: axioms removed, True-placeholder theorems replaced with real statements) |

---

## Priority 3 — Book tooling

### 3.1 Inline-elaborated Lean blocks — BLOCKED (do NOT enable `experimental.module`)

- **STATUS: BLOCKED on `experimental.module`, but the 26-include build failure is now
  FIXED (see Priority 4).** Track B task B4 enabled `experimental.module = true` and
  `autoImplicit = false` in `lakefile.toml`. This **breaks the Verso book build**:
  with 26 `{include}`d chapters the root `#doc` elaboration fails with
  `invalid {...} notation, expected type is not of the form (C ...) /
  Verso.Doc.Genre.PartMetadata ?m.…` — a **stuck genre metavariable**.
- **Root cause found and FIXED:** the failure was NOT a hard count limit and NOT
  caused by `experimental.module`. It is a Verso bug: `FinishedPart.toSyntax`
  (`Verso/Doc/Elab/Basic.lean`) annotates each *block* as `(b : Block genre)` to
  survive Lean's array-elaboration "chunking", but left the *sub-parts* array
  unannotated. With ~26 included chapters the chunked sub-parts let-bindings cannot
  infer the implicit genre, so a nested part's metadata elaborates against a stuck
  `PartMetadata ?m`. The fix annotates sub-parts as `(s : Part genre)`. It is shipped
  as `patches/verso-0001-annotate-subparts.patch` (apply via
  `./patches/apply-verso-patches.sh`; re-run after any fresh clone / `lake update`).
  With the patch, the full 26-chapter `#doc` elaborates and the single-page HTML
  builds (`lake build book && lake exe book` → `_out/html-single/index.html`).
- Both `experimental.module` and `autoImplicit = false` remain **commented out** in
  `lakefile.toml` (they are unrelated to the fix and are not needed).
- **Do NOT re-enable `experimental.module`.** The book uses **plain code blocks**
  and does not need the module system; verification is via `lake build BookProof`.

### 3.2 Migration to verso-blueprint (deferred — toolchain blocker)
- **Blocker:** `verso-blueprint` requires Lean **≥ v4.29.0**; this project is on
  **v4.28.0**. verso-blueprint elaborates the declarations it documents, so it needs
  the same toolchain as the code.
- **Execute only when a toolchain is available that is BOTH verso-blueprint-compatible
  AND supported by `aristotle.harmonic.fun`.** Then bump toolchain + Mathlib,
  `lake exe cache get`, re-verify `BookProof`, tag featured theorems with
  `@[blueprint "label"]`, and port the prose into blueprint blocks.

---

## Priority 4 — Book build: the 26-include elaboration limit (DONE)

**RESOLVED.** The full 26-chapter root `#doc` now elaborates and the single-page
HTML builds.

**Root cause.** Not a count limit and not `experimental.module`. Verso's
`FinishedPart.toSyntax` (`src/verso/Verso/Doc/Elab/Basic.lean`) builds the nested
`Part.mk` term for the whole document. It already annotates each *block* as
`(b : Block genre)` to work around a Lean limitation — when an array literal is
"chunked" during elaboration, the intermediate let-bindings may fail to infer their
type. But the *sub-parts* array was emitted unannotated (`#[$subStx,*]`). With ~26
included chapters the chunked sub-parts let-bindings leave the implicit `genre` of
nested parts unresolved, so a nested part's metadata elaborates against
`PartMetadata ?m` with `?m` stuck, producing the hard error
`invalid {...} notation, expected type is not of the form (C ...)`. (The error
surfaced at the `part-pa-free` metadata block, but that was just where the stuck
metavariable first became apparent — raising `maxHeartbeats`/`maxRecDepth` only made
the build run longer before the same structural failure.)

**Fix.** Annotate the sub-parts array as `(s : Part genre)`, mirroring the existing
block annotation:

```lean
let typedSubParts ← subStx.mapM fun s => `(($s : Part $genre))
``(Part.mk #[$titleInlines,*] $(quote titleString) $metaStx #[$typedBlocks,*] #[$typedSubParts,*])
```

**Durability.** `.lake/` is gitignored, so the patched Verso source is not tracked.
The fix is committed as `patches/verso-0001-annotate-subparts.patch` with an
idempotent apply script `patches/apply-verso-patches.sh`. **After any fresh clone or
`lake update`, run `./patches/apply-verso-patches.sh` before `lake build book`.**

**Verification.** `lake build book` succeeds (350 jobs); `lake exe book` writes
`_out/html-single/index.html` (single page, all 26 chapters, ~190 anchored headings,
0 broken ToC links).

The earlier fallback candidates (merge two chapters to ≤25 includes, or split into
two volumes) are no longer needed.

---

## Priority 5 — Book honesty-flag refresh (follow-up to Priorities 1–2)

Now that the ODE theorems are proved (no longer placeholders), the book's text still
carries the old "placeholder" caveats and should be updated:
- `Book/OdeSingularity.lean` and `Book/Introduction.lean` state that
  `weyl_symmetrization_self_adjoint` proves only `True` and that
  `nelson_essential_self_adjoint` discards its hypothesis, and that the
  complexification resolution is "not formalized". **All three are now false** — the
  theorems are proved and `BookProof.ChapterOdeComplexification` exists. Rewrite
  those paragraphs to present the results as verified, and add `#check` blocks for
  `weyl_symmetrization_self_adjoint`, `nelson_essential_self_adjoint`, and
  `ChapterOdeComplexification.ae_no_real_singular_time`.
- `Issues.md` §3 (ODE formal status) and the "current state" note should be updated
  to match.

---

## Priority 6 — Solovay–Kopperman tensor-product formalism (NEW, author-requested)

**Goal (author's specification).** Extend the decoupled Kopperman–Solovay framework so
that:
1. the **tensor product of two decidable languages is again a decidable language**;
2. via that tensor product we can express the tensor product of a
   **finite-dimensional Hilbert space** with a **separable infinite-dimensional
   Hilbert space**;
3. on the **finite-dimensional** factor an **arbitrary** probability distribution is
   admissible (our knowledge about that part is unconstrained);
4. on the **infinite-dimensional** factor **only the Mehler uniform measure** is
   admissible, because the Kopperman language **cannot distinguish any element** of
   the infinite-dimensional Hilbert space.

**Existing infrastructure to build on (all `sorry`-free):**
- `RandomMap/RandomMap2.lean`:
  - `InnerTail := Substrate` (= `Lp ℝ 2 unitMeasure` ≃ `L²[0,1]`, separable
    infinite-dimensional); `tailMeasure := rcpPriorOnSubstrate` (the Mehler/Kopperman
    prior, `IsProbabilityMeasure tailMeasure`).
  - `InnerHead (N) := Fin N → ℝ` (finite-dimensional "Tarski head" ≃ ℝ^N);
    `InnerSpace (N) := InnerHead N × InnerTail`;
    `stateMeasure N headDist := headDist.prod tailMeasure` (arbitrary head law × fixed
    Mehler tail).
  - `dependsOnlyOnHead f : Prop := ∃ g : InnerHead N → ℂ, f = g ∘ Prod.fst` — the
    decidability predicate (cylindrical/head-only observables).
  - `OuterWaveFunction N headDist := Lp ℂ 2 (stateMeasure N headDist)` (the Solovay
    space); `outer_inner_reduces_to_head`, `decidability_corollary` — inner products
    of head-only observables collapse to finite Tarski-decidable integrals over ℝ^N.
  - Already-present product/cylindrical helpers: `cross_factor_expectation`
    (expectation of a product = product of expectations, via Fubini) and
    `L2_cylindrical_norm_diff`.
- `BookProof/ChapterSolovay.lean`: `SolovayHilbertSpace N headDist :=
  UniformSpace.Completion (OuterWaveFunction N headDist)` (completed Hilbert space),
  `inner_reduces_to_head`, `mehler_concentrates_on_unit_sphere`,
  `no_godelian_self_reference`.
- `PnpProof/Kopperman.lean`: `substrate_separable : SeparableSpace Substrate`,
  `substrate_decidable_skeleton : ∃ D, D.Countable ∧ Dense D`,
  `MehlerPrior := gammaMeasure`, `mehler_isProbability`,
  `mehler_concentrates_on_sphere`, `modelPrior_atomless : ∀ g, prior {g} = 0`,
  `admits_atomless_prior`, `exists_atomless_prob_substrate`, `Formalism H`,
  `koppermanSubstrate : Formalism Substrate`.

A **"decidable language"** = a head/tail formalism `(N, headDist)` whose admissible
observables satisfy `dependsOnlyOnHead`, so every expectation/inner product reduces to
a finite integral over `InnerHead N` (Tarski-decidable). The **"Kopperman language"**
is the infinite tail, where no element is distinguishable (atomless).

### 6.1 Tensor product of two decidable languages is decidable
- Define the tensor product of two languages `(N₁, headDist₁)` and `(N₂, headDist₂)`.
  - **Head:** `InnerHead (N₁ + N₂) ≃ InnerHead N₁ × InnerHead N₂`
    (`Fin (N₁+N₂) → ℝ ≃ (Fin N₁ → ℝ) × (Fin N₂ → ℝ)`); use `Equiv.sumCompl` /
    `Fin.sumEquiv` and `PiEquiv`.
  - **Tail:** `InnerTail ⊗ InnerTail ≅ InnerTail`, i.e. `Substrate ⊗ Substrate ≅
    Substrate`. This is the analytic core: `L²[0,1] ⊗ L²[0,1] ≅ L²([0,1]×[0,1]) ≅
    L²[0,1]` (the unit square is measure-isomorphic to the unit interval). Prefer a
    concrete measure-space isomorphism (`Measure.map` under a measure-preserving
    equivalence); a fallback is uniqueness of the separable infinite-dimensional
    Hilbert space combined with `substrate_separable`. See Mathlib
    `Analysis.InnerProductSpace.TensorProduct` and `MeasureTheory.Measure.prod`.
- **Prove:** if `f₁` is `dependsOnlyOnHead` (head `N₁`) and `f₂` is
  `dependsOnlyOnHead` (head `N₂`), then their tensor product is `dependsOnlyOnHead`
  with head `N₁ + N₂` (the witness is `g₁ ⊗ g₂` on the combined head). This is the
  easy algebraic part.
- **Conclude** `tensor_language_decidable`: inner products in the tensor-product
  language reduce to a finite integral over `InnerHead (N₁ + N₂)` — i.e. the tensor
  product of two decidable languages is decidable. Reuse `outer_inner_reduces_to_head`
  / `cross_factor_expectation`.

### 6.2 Finite-dimensional ⊗ separable infinite-dimensional Hilbert space
- Specialize/instance 6.1 to express `InnerSpace N` as a Hilbert **tensor product**
  `L²(InnerHead N, headDist) ⊗ L²(InnerTail, tailMeasure) ≅ L²(InnerSpace N,
  stateMeasure N headDist)` — the standard identity `L²(X,μ) ⊗ L²(Y,ν) ≅ L²(X×Y,
  μ⊗ν)`.
- State explicitly that the first factor `L²(InnerHead N)` is **finite-dimensional**
  (dimension `N`, over ℝ^N) and the second `L²(InnerTail) = Substrate` is
  **separable infinite-dimensional** (`substrate_separable`). Provide
  `FiniteDimensional ℝ (InnerHead N)` and `¬ FiniteDimensional ℝ Substrate` (the
  latter from the infinite orthonormal skeleton / `substrate_decidable_skeleton`).
- Anchor the resulting space to `SolovayHilbertSpace`/`OuterWaveFunction` so the
  decoupling theorems apply to it.

### 6.3 Arbitrary probability distribution on the finite-dimensional factor
- Package the existing uniformity-in-`headDist` as an explicit theorem: for **any**
  `headDist : Measure (InnerHead N)` with `[IsProbabilityMeasure headDist]`,
  `stateMeasure N headDist` is a probability measure on `InnerSpace N` and the
  Solovay-Hilbert structure + `inner_reduces_to_head`/`decidability_corollary` hold.
- Prove the finite marginal is exactly the chosen law:
  `Measure.map Prod.fst (stateMeasure N headDist) = headDist` (already used as
  `h_map_fst` internally — promote it to a named theorem `stateMeasure_head_marginal`).
- Note admissibility of arbitrary atomic/discrete/continuous laws on the head (the
  finite-dimensional part is Tarski-decidable, so its points **are** distinguishable).

### 6.4 Only the Mehler measure on the infinite-dimensional factor
- **Atomlessness / indistinguishability:** prove `tailMeasure {x} = 0` for every
  `x : InnerTail` (specialize `modelPrior_atomless`), i.e. no singleton of the
  infinite-dimensional space is distinguishable — so no atomic/Dirac law is admissible
  on the tail.
- **Invariance:** prove `mehler_invariant_under_finite_orthogonal` properly (it is
  currently a `True` placeholder in `ChapterSolovay.lean`): the Mehler prior is
  invariant under finite-rank orthogonal transformations of the substrate. This
  formalizes "the Kopperman language names no preferred tail direction".
- **Characterization statement:** state `only_mehler_on_tail`: any admissible tail
  prior must be (a) a probability measure, (b) atomless, and (c) invariant under
  finite-rank orthogonal transformations — the properties that single out the Mehler
  prior (`mehler_isProbability`, atomlessness, `mehler_concentrates_on_sphere`). If
  full uniqueness is out of reach, state the characterization as "the Mehler prior is
  the canonical atomless orthogonally-invariant prior" and prove the three defining
  properties; do **not** `sorry` a uniqueness claim.
- **Contrast theorem:** `head_vs_tail_admissibility` — the head admits arbitrary
  (even atomic) laws (6.3) while the tail admits only the Mehler prior (this task),
  precisely because the language distinguishes head points but not tail points.

### 6.5 Tensor product of sample spaces / linearization of non-linear models (book.tex)
- `book.tex` (≈ lines 1802–1839): a statistical model acting non-linearly on a prior
  wave-function can be re-expressed by "redefining the Hilbert-space of the prior as a
  tensor product of two Fock-spaces and the corresponding statistical model as unitary
  (and thus linear)"; and the `Z₂ × Z₂` fermionic sample-space discussion.
- Formalize a **purification/linearization** statement: a (suitably bounded)
  non-linear statistical map on a prior Hilbert space is realized as a **unitary**
  (hence linear) map on a tensor-product Hilbert space built per 6.1/6.2.
- Anchors: `ChapterJointUnitary`, `ChapterBosonicCCR`, `ChapterSpinStatistics`,
  `ChapterFreeFieldBorn`, `ChapterDensitySpectral`.

### 6.6 Cross-dimensional inner product (Mehler-tail splitting) — author note
- **Author's specification.** In the Solovay inner-product space the inner product of
  two elements whose **finite parts have different dimensions** is well defined,
  because the uniform Mehler measure is **split** so that the finite dimensions match.
  The head dimension is therefore **not fixed**: coordinates can be moved between the
  finite head and the infinite Mehler tail without changing the space.
- **Why it is true (the mechanism).** The Mehler prior is the explicit infinite product
  of i.i.d. standard Gaussians
  `gammaMeasure : Measure (ℕ → ℝ) := Measure.infinitePi (fun _ => gaussianReal 0 1)`
  (`PnpProof/SphereGaussian.lean`). Being a product of *identical* 1-D factors, it
  splits canonically: peeling off the first `k` coordinates gives a measure-preserving
  equivalence `ℕ → ℝ ≃ (Fin k → ℝ) × (ℕ → ℝ)` under which
  `gammaMeasure ≅ (Measure.pi (fun _ : Fin k => gaussianReal 0 1)) ⊗ gammaMeasure`.
  Hence an `N₁`-dimensional head can be padded to any `M ≥ N₁` by absorbing `M − N₁`
  Mehler-tail coordinates, and these carry exactly the same Gaussian law.
- **Tasks.**
  1. `mehler_tail_split (k)`: a measure-preserving equivalence
     `InnerTail ≃ InnerHead k × InnerTail` (model the tail as `ℕ → ℝ` with
     `gammaMeasure`, or bridge from `Substrate`/`tailMeasure` via the atomless-prior
     result), with
     `Measure.map splitEquiv gammaMeasure = (gaussianPi (Fin k)) ⊗ gammaMeasure`.
     Build it from `Measure.infinitePi` + the reindexing equivalence
     `ℕ ≃ Fin k ⊕ ℕ` (Mathlib `MeasureTheory.Measure.pi`/`infinitePi`, `Equiv.sumCompl`).
  2. `cross_dim_embedding (hNM : N ≤ M)`: a measure-preserving embedding
     `InnerSpace N → InnerSpace M` that pads the head with `M − N` Mehler coordinates
     (using 6.6.1); prove it preserves the relevant measure.
  3. `inner_cross_dim_well_defined`: for cylindrical observables
     `Ψ₁` (head `N₁`, `dependsOnlyOnHead`) and `Ψ₂` (head `N₂`, `dependsOnlyOnHead`),
     the inner product computed after lifting both to any common `M ≥ max N₁ N₂` is
     **independent of `M`** and reduces to a finite integral over `InnerHead M`. The
     padding coordinates carry the Mehler **probability** measure, so they integrate
     out (`integral_const`, `measure_univ = 1`) — reuse the padding mechanism already
     inside `inner_reduces_to_head`/`outer_inner_reduces_to_head`.
- **Link to 6.4.** This is also evidence for "Mehler-only on the tail": only a
  uniform/product measure splits canonically across dimensions, so cross-dimensional
  well-definedness *forces* the tail prior to be the Mehler prior.
- Anchors: `PnpProof/SphereGaussian.lean` (`gammaMeasure`, `normSq`,
  `mehler_concentrates_on_sphere`), `PnpProof/Kopperman.lean` (`MehlerPrior`,
  `substrate_separable`, `exists_atomless_prob_substrate`),
  `RandomMap/RandomMap2.lean` (`InnerHead`, `InnerTail`, `tailMeasure`,
  `dependsOnlyOnHead`, `inner_reduces_to_head`), `BookProof/ChapterSolovay.lean`.

---

## Priority 7 — Further `book.tex` claims to formalize (NEW)

These are `book.tex` claims that are **not** among the deferred chapters the author
asked to ignore (gauge/Yang–Mills, Navier–Stokes/CSFT, real reps/CPT, Gribov, parity,
gravity, consciousness, deep learning, RH priors — `Issues.md` §6). Each has existing
`BookProof` anchors. Keep every theorem `sorry`-free/`axiom`-free; where a full claim
is out of reach, state the provable core precisely and record the gap in `Issues.md`.

### 7.1 Probability theory as a universal language / interface
- `book.tex` ≈ 8402, 8702: "Probability theory is a language (or interface) that allows
  us to transfer a problem between two sciences"; "probability theory is a universal
  language".
- Formalize probability as a **translation between two measurable theories**: a
  probability kernel / Markov kernel `X → Y` transporting measures, and the statement
  that any problem expressible on one standard probability space transfers to another
  via such a kernel. Anchors: `ChapterBijectionProbability`, `ChapterConditional`,
  `ChapterConservative`.

### 7.2 Average (`L²`) vs maximal (`L^∞`) error duality
- `book.tex` ≈ 8405–8414: average error = `L²` norm of a normalized wave-function
  (square-root of a probability density); maximal error = `L^∞` norm, realized by an
  element of the abelian von Neumann algebra of operators on the Hilbert space.
- Formalize: (a) a probability density `ρ` and its wave-function `√ρ` with
  `‖√ρ‖² = ∫ ρ = 1`; (b) the `L²`/`L^∞` distinction on a standard probability space;
  (c) `L^∞` as the abelian von Neumann algebra of multiplication operators. Anchors:
  Mathlib `MeasureTheory.Lp`, `MeasureTheory.L∞`; `ChapterBornPhaseFiber`,
  `ChapterDensitySpectral`.

### 7.3 Countable definability of the reals
- `book.tex` ≈ 8430–8434: "we can define exactly only a countable number of real
  numbers (usually the rationals)… the remaining real numbers can only be constrained
  to be inside an interval with a finite width".
- Formalize: the set of reals definable in a fixed countable language is countable;
  non-definable reals are specifiable only by intervals (finite-width constraints).
  Connect to the PA-free/definability work. Anchors: `ChapterDefinabilityFragment`,
  `ChapterPaFreeCompletion`, `ChapterNoUniformCountable`, `ChapterCountablePartition`.

### 7.4 Kopperman `L_{ω₁ω₁}`-theory: model-theoretic properties
- `book.tex` ≈ 10630–10644: the `L_{ω₁ω₁}`-theory of Hilbert spaces has completeness
  and compactness, and **all its models are separable Hilbert spaces**; whatever is
  true/false for all separable Hilbert spaces in a finitary theory is true/false in the
  infinitary theory.
- Formalize what is provable: every `Formalism H` model carries a separable Hilbert
  structure (`substrate_separable`); truth of finitary / `Π⁰₂` statements is invariant
  across models (`arith_truth_invariant`, `pi02_invariant_of_formalism`,
  `interpPi02_eq`). State the "all models separable" theorem explicitly; record
  full infinitary completeness/compactness as a documented gap if not formalizable.
  Anchors: `PnpProof/Kopperman.lean`.

### 7.5 Finite computation + Bayesian prior for large integers
- `book.tex` ≈ 10646–10653: "define computation without involving the infinite";
  "define the multiplication of two integers smaller than some finite large integer,
  and for larger integers… use a Bayesian prior since we will never know the result".
- Formalize: a finite truncation of arithmetic (operations bounded by a finite
  parameter `B`) together with a Bayesian prior on the unknown results beyond `B`.
  Anchors: `ChapterFiniteBayesHierarchy`, `ChapterNoBestPrior`, `ChapterPriorOdds`,
  `RandomMap/SchoenfeldPRA.lean`.

### 7.6 Density matrix = diagonal rotated by a unitary (marginal × conditional)
- `book.tex` ≈ 1796–1800: the density matrix is "a diagonal operator rotated by a
  unitary operator, with the diagonal operator defining the marginal probability of the
  initial state and the unitary operator defining the conditioned probability of the
  final state conditioned by the initial state".
- Formalize the spectral decomposition `ρ = U D U†` with `D` the (diagonal) marginal
  and `U` encoding the conditional. Anchors: `ChapterEulerDensityMatrix`,
  `ChapterDensitySpectral`, `ChapterCollapseDiagonal`, `ChapterConditional`.

---

## Priority 8 — `Issues.md`-derived tasks the specialist can attack (NEW)

### 8.1 Confirm `BookProof` build integrity (`Issues.md` §1, NEEDS-INFO)
- Run `lake build BookProof` (and `lake build Singularity`) end-to-end and confirm a
  clean, `sorry`-free/`axiom`-free build on v4.28.0 Mathlib. Report any API-drift.

### 8.2 Verify the formal anchors behind the chapter sketch proofs (`Issues.md` §2, UNCERTAIN)
- The book's sketch proofs were re-derived, not transcribed. For each `Book/*.lean`
  chapter, confirm every cited `BookProof` theorem exists, is `sorry`-free, and its
  statement matches the prose claim. Flag mismatches for cross-checking against
  `book.tex` before publication.

### 8.3 The 26-`{include}` Verso elaboration limit (= Priority 4) — DONE
- **Resolved.** Not a count limit and not fixable by `set_option`. Root cause: Verso's
  `FinishedPart.toSyntax` (`Verso/Doc/Elab/Basic.lean`) annotated blocks but not the
  sub-parts array, so array-chunking left nested parts' implicit genre stuck
  (`PartMetadata ?m`). Fixed by annotating sub-parts `(s : Part genre)`, shipped as
  `patches/verso-0001-annotate-subparts.patch` (apply via
  `./patches/apply-verso-patches.sh`; re-run after fresh clone / `lake update`). The
  full 26-chapter book now builds to `_out/html-single/index.html`. See Priority 4.

### 8.4 Restate long `#check` types as clean `example`s (`Issues.md` §4, CRITIQUE)
- For the worst-offending headline theorems (free-field, measure-theoretic), add a
  clean restated `example`/`theorem` with a short type so the rendered code block is
  readable, keeping a prose paraphrase above it.

### 8.5 Refresh book honesty flags now that ODE theorems are proved (= Priority 5)
- Update `Book/OdeSingularity.lean`, `Book/Introduction.lean`, and `Issues.md` §3:
  `weyl_symmetrization_self_adjoint`, `nelson_essential_self_adjoint`, and
  `ChapterOdeComplexification.ae_no_real_singular_time` are now proved (no longer
  placeholders). Rewrite the "placeholder"/"not formalized" caveats accordingly.

---

## Notes for the specialist
- The book's chapters are in `Book/*.lean`; the root is `Book.lean`; the generator is
  `BookMain.lean` (single-page HTML: `emitHtmlSingle := .immediately`,
  `emitHtmlMulti := .no`). Build with `lake build book && lake exe book`.
- Verso markup gotchas (avoid): no `>` blockquotes; keep any `**bold**` that contains
  inline math on a **single line** (a multi-line bold wrapping `` $`…` `` compiles in
  a chapter but breaks the root `#doc` splice); close `:::paragraph` with `:::` before
  opening another; inline `{lean}`…`` elaborates (fails on free vars / `#check`) — use
  plain backticks for schematic code.
- **Do not edit `lakefile.toml` `[leanOptions]`** without coordinating: the book build
  is sensitive to `experimental.module` / `autoImplicit` / `maxSynthPendingDepth`.
- See `Issues.md` for open uncertainties and `PLAN_A_ODE_CORE.md` /
  `PLAN_B_COMPLEXIFICATION_FRAMEWORK.md` for the completed specialist tracks.
