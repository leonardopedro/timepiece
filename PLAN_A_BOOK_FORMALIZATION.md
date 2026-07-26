# PLAN A — Book Proof Formalization (Track A)

**Owner:** LLM-Lean-Specialist-A  
**Machine:** Machine A  
**Target files:** `BookProof/*.lean` (all new modules), `Singularity/*.lean` (read-only cross-check)  
**Hard constraints:** Never writes `Book/*.lean`, `Issues.md`, `Singularity/EnergyBounded.lean` (except cross-check)

---

## Task A1: Solovay–Kopperman Tensor Product (Priority 6)

**Goal:** Extend the decoupled Kopperman–Solovay framework with tensor-product formalism.

### 6.1 Tensor product of two decidable languages is decidable

**File:** `BookProof/ChapterSolovay.lean` (EXTEND)

Define the tensor product of two languages `(N₁, headDist₁)` and `(N₂, headDist₂)`:

- **Head:** `InnerHead (N₁ + N₂) ≃ InnerHead N₁ × InnerHead N₂`
  (`Fin (N₁+N₂) → ℝ ≃ (Fin N₁ → ℝ) × (Fin N₂ → ℝ)`); use `Equiv.sumCompl` /
  `Fin.sumEquiv` and `PiEquiv`.

- **Tail:** `InnerTail ⊗ InnerTail ≅ InnerTail`, i.e. `Substrate ⊗ Substrate ≅
  Substrate`. Use `L²[0,1] ⊗ L²[0,1] ≅ L²([0,1]×[0,1]) ≅ L²[0,1]`
  (unit square measure-isomorphic to unit interval). Prefer a concrete
  measure-space isomorphism (`Measure.map` under a measure-preserving equivalence).

- **Prove:** if `f₁` is `dependsOnlyOnHead` (head `N₁`) and `f₂` is
  `dependsOnlyOnHead` (head `N₂`), then their tensor product is `dependsOnlyOnHead`
  with head `N₁ + N₂`. This is the easy algebraic part.

- **Conclude** `tensor_language_decidable`: inner products in the tensor-product
  language reduce to a finite integral over `InnerHead (N₁ + N₂)`.

**Dependencies:** `Finsupp`, `Equiv`, `MeasureTheory.Measure.prod`,
`Analysis.InnerProductSpace.TensorProduct`

### 6.2 Finite-dimensional ⊗ separable infinite-dimensional Hilbert space

**File:** `BookProof/ChapterSolovay.lean` (EXTEND)

- Specialize 6.1 to express `InnerSpace N` as a Hilbert **tensor product**
  `L²(InnerHead N, headDist) ⊗ L²(InnerTail, tailMeasure) ≅ L²(InnerSpace N,
  stateMeasure N headDist)`.
- State: first factor is **finite-dimensional** (dimension `N`), second is
  **separable infinite-dimensional** (`substrate_separable`).
- Anchor to `SolovayHilbertSpace`/`OuterWaveFunction` so the decoupling
  theorems apply.

### 6.3 Arbitrary probability distribution on the finite-dimensional factor

**File:** `BookProof/ChapterSolovay.lean` (EXTEND)

- For **any** `headDist : Measure (InnerHead N)` with `[IsProbabilityMeasure headDist]`,
  prove `stateMeasure N headDist` is a probability measure on `InnerSpace N`.
- Prove the finite marginal: `Measure.map Prod.fst (stateMeasure N headDist) = headDist`.
- Note admissibility of arbitrary atomic/discrete/continuous laws on the head.

### 6.4 Only the Mehler measure on the infinite-dimensional factor

**File:** `BookProof/ChapterSolovay.lean` (EXTEND)

- **Atomlessness:** prove `tailMeasure {x} = 0` for every `x : InnerTail`.
- **Invariance:** prove `mehler_invariant_under_finite_orthogonal` (currently `True` placeholder).
- **Characterization:** state `only_mehler_on_tail` — any admissible tail prior must be
  (a) probability, (b) atomless, (c) invariant under finite-rank orthogonal
  transformations. Prove the three defining properties; do NOT `sorry` a uniqueness claim.
- **Contrast theorem:** `head_vs_tail_admissibility` — head admits arbitrary laws
  while tail admits only Mehler.

### 6.5 Tensor product of sample spaces / linearization of non-linear models

**File:** `BookProof/ChapterJointUnitary.lean` (EXTEND)  
**Cross-check:** `BookProof/ChapterBosonicCCR.lean`, `BookProof/ChapterSpinStatistics.lean`

- Formalize a **purification/linearization** statement: a (suitably bounded)
  non-linear statistical map on a prior Hilbert space is realized as a
  **unitary** (hence linear) map on a tensor-product Hilbert space built per 6.1/6.2.

### 6.6 Cross-dimensional inner product (Mehler-tail splitting)

**File:** `BookProof/ChapterSolovay.lean` (EXTEND)

- **`mehler_tail_split (k)`:** a measure-preserving equivalence
  `InnerTail ≃ InnerHead k × InnerTail` with
  `Measure.map splitEquiv gammaMeasure = (gaussianPi (Fin k)) ⊗ gammaMeasure`.
- **`cross_dim_embedding (hNM : N ≤ M)`:** a measure-preserving embedding
  `InnerSpace N → InnerSpace M` padding the head with `M - N` Mehler coordinates.
- **`inner_cross_dim_well_defined`:** for cylindrical observables with different
  head dimensions, the inner product computed after lifting to a common `M` is
  independent of `M` and reduces to a finite integral.

---

## Task A2: Further book.tex Claims (Priority 7)

**Goal:** Formalize the remaining `book.tex` claims that are not deferred chapters.

### 7.1 Probability as a universal language / interface

**File:** `BookProof/ChapterBijectionProbability.lean` (EXTEND)

Already formalized: bijection probability `n!/nⁿ`, Stirling asymptotics, tendsto to 0.

Add:
- Formalize probability as a **translation between two measurable theories**:
  a probability kernel / Markov kernel `X → Y` transporting measures, and the
  statement that any problem expressible on one standard probability space transfers
  to another via such a kernel.

**Anchors:** `ChapterBijectionProbability`, `ChapterConditional`, `ChapterConservative`.

### 7.2 Average (`L²`) vs maximal (`L^∞`) error duality

**File:** `BookProof/ChapterBornPhaseFiber.lean` (EXTEND)  
**Cross-check:** `ChapterDensitySpectral`, `ChapterCollapseDiagonal`

- Formalize: (a) a probability density `ρ` and its wave-function `√ρ` with
  `‖√ρ‖² = ∫ ρ = 1`; (b) the `L²`/`L^∞` distinction on a standard probability space;
  (c) `L^∞` as the abelian von Neumann algebra of multiplication operators.

### 7.3 Countable definability of the reals

**File:** `BookProof/ChapterNoUniformCountable.lean` (READ-ONLY cross-check)
**File:** `BookProof/ChapterCountablePartition.lean` (READ-ONLY cross-check)

Already formalized: countable partition results.

Add:
- Formalize: the set of reals definable in a fixed countable language is countable;
  non-definable reals are specifiable only by intervals (finite-width constraints).
  Connect to the PA-free/definability work.

**Anchors:** `ChapterDefinabilityFragment`, `ChapterPaFreeCompletion`, `ChapterNoUniformCountable`, `ChapterCountablePartition`.

### 7.4 Kopperman `L_{ω₁ω₁}`-theory: model-theoretic properties

**File:** `BookProof/ChapterKopperman.lean` (EXTEND)  
**Cross-check:** `PnpProof/Kopperman.lean`

Already formalized: `Formalism H`, `koppermanSubstrate`, `substrate_separable`.

Add:
- Prove: every `Formalism H` model carries a separable Hilbert structure
  (`substrate_separable`); truth of finitary / `Π⁰₂` statements is invariant
  across models (`arith_truth_invariant`, `pi02_invariant_of_formalism`).
- State the "all models separable" theorem explicitly; record full infinitary
  completeness/compactness as a documented gap if not formalizable.

### 7.5 Finite computation + Bayesian prior for large integers

**File:** `BookProof/ChapterFiniteBayesHierarchy.lean` (READ-ONLY cross-check)  
**File:** `BookProof/ChapterNoBestPrior.lean` (READ-ONLY cross-check)

Already formalized: finite Bayes hierarchy, prior odds, no best prior.

Add:
- Formalize: a finite truncation of arithmetic (operations bounded by a finite
  parameter `B`) together with a Bayesian prior on the unknown results beyond `B`.

**Anchors:** `ChapterFiniteBayesHierarchy`, `ChapterNoBestPrior`, `ChapterPriorOdds`, `RandomMap/SchoenfeldPRA.lean`.

### 7.6 Density matrix = diagonal rotated by a unitary

**File:** `BookProof/ChapterEulerDensityMatrix.lean` (READ-ONLY cross-check)  
**File:** `BookProof/ChapterDensitySpectral.lean` (READ-ONLY cross-check)

Already formalized: Euler density matrix, spectral form.

Add:
- Formalize the spectral decomposition `ρ = U D U†` with `D` the (diagonal) marginal
  and `U` encoding the conditional.

**Anchors:** `ChapterEulerDensityMatrix`, `ChapterDensitySpectral`, `ChapterCollapseDiagonal`, `ChapterConditional`.

---

## Task A3: Restate Long #check Types (Priority 8.4)

**Goal:** For the worst-offending headline theorems, add clean restated
`example`/`theorem` with short types so the rendered code block is readable.

**Files:** All `BookProof/*.lean` files (SELECTED)

Target theorems (from `Issues.md`): free-field, measure-theoretic headlines.
Add a clean `example` or short-named theorem with a readable type above or
beside the original `#check` block.

Keep a prose paraphrase above the code block.

---

## Task A4: Cross-check Singularity/ (read-only)

**Goal:** Verify that `Singularity/` theorems cited in `Book/OdeSingularity.lean`
are still `sorry`-free and their statements match the prose claims.

**Files:** `Singularity/Hamiltonian.lean`, `Singularity/Esa.lean`, `Singularity/Singularity.lean`

This is a read-only cross-check; do NOT modify any `Singularity/` file.
Report any discrepancies.

---

## Execution Order

```
A1 (Priority 6 — Solovay-Kopperman tensor product)
  → A2 (Priority 7 — Further book.tex claims)
  → A3 (Priority 8.4 — Restate #check types)
  → A4 (read-only cross-check Singularity/)
```

A1 and A2 are independent and can be worked on in parallel.
A3 depends on A1/A2 (knows which theorems need restating).
A4 is independent.

---

## Summary

| Task | File(s) | Content | Status |
|------|---------|---------|--------|
| A1 | ChapterSolovay.lean, ChapterJointUnitary.lean | Solovay-Kopperman tensor product (6.1–6.6) | TODO |
| A2 | ChapterBijectionProbability.lean, ChapterBornPhaseFiber.lean, ChapterKopperman.lean, etc. | Further book.tex claims (7.1–7.6) | TODO |
| A3 | All BookProof/*.lean (selected) | Restate long #check types (8.4) | TODO |
| A4 | Singularity/*.lean (read-only) | Cross-check cited theorems | TODO |

---

## Coordination with Plan B

| Plan A (Track A) | Plan B (Track B) |
|------------------|-------------------|
| MODIFIES: `BookProof/*.lean` | MODIFIES: `Book/*.lean`, `Issues.md` |
| READ-ONLY: `Singularity/*.lean` | NEVER touches `Singularity/` |
| NEVER touches `Book/` | NEVER touches `BookProof/` |
| **Target:** Tensor product, book.tex claims, #check cleanup | **Target:** Prose updates, honesty flags, build verification, Verso limit |

**Zero file overlap. Both plans compile the same project.**
