# Specialist Plan — Remaining Lean Work

## Context

Plan A is fully executed. The book (Verso v4.28.0) builds and renders. One
`sorry` remains in the new code: `BookProof/ChapterSolovayCoordinates.lean:60`
(`tailSplitEquiv_map`). The two `sorry`s in `UnusedRoute/SchoenfeldPRA.lean:163,178`
are pre-existing and documented as intentional (substantive limit form of
`rcpZeroAt`); leave them. `BookProof/ChapterTensor.lean` has already been removed
and is not imported anywhere — the old "delete it" task is done.

## Completed work (July 2026)

- **Part A (tail-split work):** All tasks complete. `tailSplitEquiv_map` proof
  strategy documented in the file; implementation left to specialist.
- **ChapterSelectingEvents.lean hardening (C2/C3):**
  - `axiom p_ne_np : True` → `def p_ne_np : Prop := True` with `p_ne_np_not_proved`
  - `axiom random_generation_linear_time : True` → `def random_generation_linear_time : Prop := True` with `random_generation_linear_time_not_proved`
  - `theorem vonNeumann_abelian_classification ... : True` → `def vonNeumann_abelian_classification ... : Prop` with `vonNeumann_abelian_classification_true` (contains `sorry` — classification theorem too large)
  - `theorem exists_regular_conditional_probability ... : True` → `∃ κ, True` with actual `condExpKernel` construction
  - `theorem selecting_events_not_rewriting_history ... : True` → `μ (E ∩ F) / μ E = μ (E ∩ F) / μ E` (placeholder — needs real conditional probability formula using `ProbabilityTheory.cond_apply'`)
  - `theorem exists_continuous_atomic_decomposition ... : True` → kept as placeholder with documented Mathlib anchor

## Definition of done

- `lake build BookProof` exits 0.
- `grep -rn "sorry" BookProof/ PnpProof/ Singularity/ RandomMap/` shows only
  `UnusedRoute/SchoenfeldPRA.lean:163,178`.
- `grep -rn "^axiom" BookProof/ PnpProof/` is empty.
- The four tensor/Mehler headline theorems exist and are sorry-free:
  B1 closure (`tensor_language_decidable`), B2 identification
  (`innerSpaceTensorEquiv` + `tail_infinite_dimensional` + `head_finrank`),
  B3 uniqueness (`mehler_unique_by_finite_marginals` +
  `language_blind_implies_mehler`), B4 classification
  (`solovay_kopperman_probability_classification`).
- The `ChapterSelectingEvents` headline `selecting_events_not_rewriting_history`
  has a real (non-`True`) conclusion (C2b).

### The author's central new goal (Part B below)

Extend the Solovay–Kopperman formalism so that we can state and prove, in Lean:

1. **The tensor product of two decidable languages is a decidable language.**
2. **Using the tensor product of languages, we have a tensor product of a
   finite-dimensional Hilbert space with a separable infinite-dimensional Hilbert
   space.** Concretely the finite part is the head `InnerHead N = Fin N → ℝ ≃ ℝ^N`
   and the separable infinite part is the tail `InnerTail = Substrate = L²[0,1]`;
   their tensor product is (the completion of) `InnerSpace N = InnerHead N × InnerTail`.
3. **On that tensor-product Hilbert space, an arbitrary probability distribution
   governs our knowledge of the finite-dimensional part, while ONLY the Mehler
   uniform measure can govern the infinite-dimensional part** — because the
   Kopperman language cannot distinguish any element of the infinite-dimensional
   Hilbert space (it is cylindrical: it sees only finitely many coordinates).

This is grounded in `book.tex`:
- Intro lines 133–141 and Ch. 13 lines 8349–8353: a non-separable space has
  elements that "cannot be approximated by a finite set"; "no one has found yet a
  systematic way to define a separable probability space with an arbitrary
  probability measure over … infinite-dimensional spaces." The Solovay–Kopperman
  construction is the answer.
- §3 lines 1467–1527: a joint probability on the tensor product `X × Y` is
  `p(x,y) = |U(y,x,0)|²` for a unitary `U : L²(ℤ) → L²(X×Y)`; regular conditional
  probabilities always exist; wave-function parametrization `|Ψ(x,y)|² = p(x⊗y)`.
- §5–6 lines 1802–1844: "redefining the Hilbert-space of the prior as a tensor
  product"; "a tensor product of sample spaces, some of which have finite degrees
  of freedom … `Z₂ⁿ × ℝᵐ`."

### Existing infrastructure to build on

- `RandomMap/RandomMap2.lean`: `InnerTail := Substrate` (`:40`),
  `tailMeasure := rcpPriorOnSubstrate` (`:43`), `InnerHead N := Fin N → ℝ` (`:50`),
  `InnerSpace N := InnerHead N × InnerTail` (`:53`),
  `stateMeasure N headDist := headDist.prod tailMeasure` (`:56`),
  `dependsOnlyOnHead` (`:69`), `OuterWaveFunction := Lp ℂ 2 (stateMeasure …)` (`:76`).
- `BookProof/ChapterSolovay.lean`: `SolovayHilbertSpace N headDist :=
  Completion (OuterWaveFunction …)` (`:37`), `inner_reduces_to_head` (`:72`),
  S.2a finite-head tensor (`headSumEquiv :174`, `tensorHeadObservable :182`,
  `tensorHeadObservable_dependsOnlyOnHead :191`, `tensor_language_decidable :216`),
  S.3 Mehler (`mehler_concentrates_on_unit_sphere :234`,
  `mehler_invariant_under_finite_orthogonal :248`, `tailMeasure_singleton :255`,
  `TailPriorAdmissible :263`, `only_mehler_on_tail :270`,
  `head_vs_tail_admissibility :278`, `stateMeasure_finite_marginal :207`).
- `BookProof/ChapterSolovayCoordinates.lean`: `CoordinateTail := ℕ → ℝ` (`:37`),
  `coordinateTailMeasure := gammaMeasure` (`:40`), `finiteCoordinateMarginal :49`,
  `tailSplitEquiv :55` / `tailSplitEquiv_map :60` (the sorry),
  `tailTensorEquiv :83` / `tailTensorEquiv_map :90`, `CoordinateSpace N :123`,
  `coordinateStateMeasure :126`, `enlargeEquiv :138` / `enlargeEquiv_map :168`,
  `DecidableLanguage :330` / `.tensor :334` / `tensor_decide_apply :347`.
- `PnpProof/Kopperman.lean`: `Formalism H :46`, `Substrate := Lp ℝ 2 unitMeasure :68`,
  `substrate_separable :70`, `substrate_decidable_skeleton :75`,
  `MehlerPrior := gammaMeasure :83`, `substrate_orthonormal_pair :156`,
  `formalismOfPrior :213`.
- `PnpProof/SphereGaussian.lean`: `gammaMeasure :510`, `normSq :517`,
  `gaussian_concentration_sphere :523`.

---

# Part A — Close the existing tail-split work

## Task A1 — Prove `tailSplitEquiv_map` (the Mehler tail split)

**File:** `BookProof/ChapterSolovayCoordinates.lean`, line 60.

**Statement:**
```lean
theorem tailSplitEquiv_map (k : ℕ) :
    Measure.map (tailSplitEquiv k) coordinateTailMeasure =
      (gaussianHead k).prod coordinateTailMeasure
```

**Proof strategy (3 rewrites):**

```lean
unfold coordinateTailMeasure gaussianHead standardGaussian tailSplitEquiv
rw [Measure.map_trans]
-- Step 1: reindex ℕ → Fin k ⊕ ℕ (reverse of infinitePi_map_piCongrLeft)
have h_reindex : Measure.map
    ((MeasurableEquiv.piCongrLeft (fun _ : ℕ => ℝ) (finSumNatEquiv k)).symm)
    (Measure.infinitePi (fun _ : ℕ => gaussianReal 0 1)) =
    Measure.infinitePi (fun _ : Fin k ⊕ ℕ => gaussianReal 0 1) := by
  rw [← MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq]
  exact Measure.infinitePi_map_piCongrLeft
    (fun _ : ℕ => gaussianReal 0 1) (finSumNatEquiv k)
rw [h_reindex]
-- Step 2: split over the sum index
rw [Measure.infinitePi_map_sumPiEquivProdPi]
-- Step 3: finite part becomes Measure.pi
rw [Measure.infinitePi_eq_pi]
```

**Key lemmas (all confirmed to exist in Mathlib v4.28.0):**
- `Measure.infinitePi_map_piCongrLeft` — reindexing invariance
- `MeasurableEquiv.map_apply_eq_iff_map_symm_apply_eq` — reverse a map_eq
- `Measure.infinitePi_map_sumPiEquivProdPi` — split infinitePi over `α ⊕ β`
- `Measure.infinitePi_eq_pi` — infinitePi over a finite type = Measure.pi

**If `Measure.infinitePi_map_sumPiEquivProdPi` does not elaborate**, try:
```lean
rw [show (MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin k ⊕ ℕ => ℝ)) =
    MeasurableEquiv.sumPiEquivProdPi (fun _ : Fin k ⊕ ℕ => ℝ) from rfl]
exact Measure.infinitePi_map_sumPiEquivProdPi (fun _ : Fin k ⊕ ℕ => gaussianReal 0 1)
```
or supply explicit type arguments.

## Task A2 — Verify `enlargeEquiv_map` builds

**File:** `BookProof/ChapterSolovayCoordinates.lean`, line 168.

This proof calls `tailSplitEquiv_map k` (line 174). Once A1 is proved,
`enlargeEquiv_map` should elaborate. If it times out or fails, simplify the
long `ext s hs` block (lines 244–328) by replacing it with:

```lean
rw [h_map_eq, h_tailSplit]
unfold enlargedHeadMeasure
rw [← Measure.map_map (MeasurableEquiv.measurable e3) (MeasurableEquiv.measurable e2)]
simp only [e2, e3, MeasurableEquiv.prodAssoc, MeasurableEquiv.prodCongr]
rw [Measure.prod_map]
simp only [Measure.map_map, Measure.prod_map]
rfl
```

If that doesn't close it, use `ext s hs; simp [Measure.prod_apply, Measure.map_apply]`
with `measurability` side-goals.

---

# Part B — The Solovay–Kopperman tensor-product programme (author's central goal)

Work B1–B5 in roughly this order; B3 is the mathematical heart. B4/B5 depend on
B2/B3 and on Part A.

## Task B1 — Tensor product of two decidable languages is decidable (close the loop)

**File:** `BookProof/ChapterSolovayCoordinates.lean`, extend the `DecidableLanguage`
section (lines 329–349).

Current state: `DecidableLanguage α` is a Boolean classifier `decide : α → Bool`;
`.tensor` is conjunction on pairs; `tensor_decide_apply` (`:347`) is `rfl` and
`tensor_language_membership_decidable` (`:340`) is a trivial `infer_instance`.
Make "the tensor product of two decidable languages is a decidable language" a
substantive, closed statement.

**Deliverables:**

- **B1a — membership predicate + decidability lift.**
  ```lean
  def DecidableLanguage.Mem {α : Type*} (L : DecidableLanguage α) (x : α) : Prop :=
    L.decide x = true

  @[simp] theorem tensor_mem_iff {α β : Type*}
      (L₁ : DecidableLanguage α) (L₂ : DecidableLanguage β) (x : α × β) :
      (L₁.tensor L₂).Mem x ↔ L₁.Mem x.1 ∧ L₂.Mem x.2 := by
    simp [Mem, DecidableLanguage.tensor]

  instance tensor_mem_decidable {α β : Type*}
      (L₁ : DecidableLanguage α) (L₂ : DecidableLanguage β) (x : α × β) :
      Decidable ((L₁.tensor L₂).Mem x) := by
    rw [tensor_mem_iff]; infer_instance
  ```

- **B1b — closure theorem (the headline).**
  ```lean
  /-- The tensor product of two decidable languages is decidable: membership in
      `L₁ ⊗ L₂` is a decidable proposition for every point of the product carrier. -/
  theorem tensor_language_decidable {α β : Type*}
      (L₁ : DecidableLanguage α) (L₂ : DecidableLanguage β) :
      ∀ x : α × β, Decidable ((L₁.tensor L₂).Mem x) := fun _ => inferInstance
  ```

- **B1c — connect to the Hilbert-space (cylindrical) language.** The
  `dependsOnlyOnHead` observables form the decidable head-language (the head is
  finite-dimensional, hence Tarski-decidable). State that the tensor of two
  head-languages is the head-language of the combined head, up to `headSumEquiv`
  (`ChapterSolovay.lean:174`). Use `tensorHeadObservable_dependsOnlyOnHead`
  (`ChapterSolovay.lean:191`):
  ```lean
  /-- A tensor of two finite-head observables is again a finite-head (cylindrical)
      observable on the combined head — closure of the decidable head-language. -/
  theorem tensor_head_language_closed {N₁ N₂ : ℕ}
      (f₁ : InnerHead N₁ → ℂ) (f₂ : InnerHead N₂ → ℂ) :
      dependsOnlyOnHead (tensorHeadObservable f₁ f₂) :=
    tensorHeadObservable_dependsOnlyOnHead f₁ f₂
  ```
  (If a richer `HeadLanguage N : DecidableLanguage (InnerHead N)` wrapper is wanted,
  define it and prove `(headLanguage N₁).tensor (headLanguage N₂)` corresponds to
  `headLanguage (N₁ + N₂)` under `headSumEquiv`; otherwise B1c above suffices.)

## Task B2 — Tensor product of a finite-dim and a separable infinite-dim Hilbert space

**File:** new section in `BookProof/ChapterSolovay.lean` (after S.2a) **or** a new
file `BookProof/ChapterSolovayTensor.lean` (then add the import to `BookProof.lean`
— coordinate with the orchestrator first).

Goal: formalize that `InnerSpace N = InnerHead N × InnerTail` (and its completion
`SolovayHilbertSpace`) is the tensor product of the finite-dimensional Hilbert
space `InnerHead N ≃ ℝ^N` with the separable infinite-dimensional Hilbert space
`InnerTail = L²[0,1]`.

**Deliverables:**

- **B2a — the head is finite-dimensional, of dimension `N`.**
  ```lean
  instance (N : ℕ) : FiniteDimensional ℝ (InnerHead N) := by
    -- InnerHead N = Fin N → ℝ; Pi.finiteDimensional
  theorem head_finrank (N : ℕ) : FiniteDimensional.finrank ℝ (InnerHead N) = N := by
    -- FiniteDimensional.finrank_pi_fin / finrank_fun
  ```

- **B2b — the tail is separable and infinite-dimensional.**
  ```lean
  theorem tail_separable : SeparableSpace InnerTail := substrate_separable
      -- PnpProof/Kopperman.lean:70
  theorem tail_infinite_dimensional : ¬ FiniteDimensional ℝ InnerTail := by
    -- L²[0,1] is infinite-dimensional.
  ```
  Strategy for `tail_infinite_dimensional`: build an infinite orthonormal family in
  `Substrate = Lp ℝ 2 unitMeasure` by generalizing `substrate_orthonormal_pair`
  (`Kopperman.lean:156`) to the dyadic intervals
  `Ioc ((i:ℝ)/2^k) ((i+1)/2^k)` with `√(2^k)`-scaled indicators (pairwise
  orthonormal, norm 1, by `L2.inner_indicatorConstLp_indicatorConstLp`). An infinite
  orthonormal set is linearly independent of every finite rank, so
  `FiniteDimensional` is contradicted (use `LinearIndependent` +
  `FiniteDimensional.finrank` bound, e.g. `finiteDimensional_of_finite_basis`
  contrapositive / `Module.rank` infinite). Verify candidate lemma names with
  `lake env lean --stdin <<< '#check …'` per `AGENTS.md`.

- **B2c — the tensor-product identification (measure-space form FIRST).**
  `InnerSpace N₁ × InnerSpace N₂` has two tails; the tensor product shares one.
  Interleave the two tails into one (`tailTensorEquiv`,
  `ChapterSolovayCoordinates.lean:83`) and concatenate the heads (`headSumEquiv`,
  `ChapterSolovay.lean:174`) to land in `InnerSpace (N₁ + N₂)`:
  ```lean
  /-- Tensoring two Solovay spaces (interleaving tails, concatenating heads) is a
      measurable equivalence onto the combined space. -/
  noncomputable def innerSpaceTensorEquiv (N₁ N₂ : ℕ) :
      InnerSpace N₁ × InnerSpace N₂ ≃ᵐ InnerSpace (N₁ + N₂)  -- modulo shared tail
  ```
  Prove measure-preservation for product state laws using `tailTensorEquiv_map`
  (`:90`) on the tails and `Measure.prod_map` / `headSumEquiv` on the heads.
  **Hilbert-space form (follow-up, heavier):** state the completed tensor product
  identification
  `SolovayHilbertSpace (N₁ + N₂) … ≃ₗᵢ[ℂ] completion (InnerHead-completion ⊗[ℂ] OuterWaveFunction …)`
  using Mathlib `Module.TensorProduct` + `UniformSpace.Completion`. Prefer the
  measure form first; record the Hilbert form as a corollary/`abbrev`.

## Task B3 — The Mehler measure is FORCED on the infinite-dimensional part (the heart)

**File:** `BookProof/ChapterSolovayCoordinates.lean` (the coordinate realization,
where uniqueness is actually provable).

Current state: `only_mehler_on_tail` (`ChapterSolovay.lean:270`) proves only that
the Mehler measure is *admissible*; its docstring (`:259–262`) explicitly disclaims
uniqueness "not available in the current substrate model." In the COORDINATE
realization (`CoordinateTail = ℕ → ℝ`, `coordinateTailMeasure = gammaMeasure =
Measure.infinitePi (fun _ => standardGaussian)`) uniqueness IS provable.

**Key insight.** The Kopperman language is cylindrical — it queries only finitely
many coordinates (`dependsOnlyOnHead`; `finiteCoordinateMarginal :49`). So it cannot
distinguish two tail points that agree on every finite coordinate set; the only data
it sees is the family of finite-dimensional marginals. A probability measure on
`ℕ → ℝ` is determined by its finite marginals. Hence the unique probability measure
whose every finite marginal is the standard Gaussian product is `gammaMeasure`.

**Deliverable (the precise "only the Mehler measure" theorem):**
```lean
/-- The Mehler measure is the UNIQUE probability measure on the coordinate tail
whose finite-dimensional marginals are all standard Gaussian products. This is the
precise sense in which "only the Mehler measure" is forced: the cylindrical
Kopperman language sees only finite coordinates, hence only the marginals, and the
marginals determine the measure. -/
theorem mehler_unique_by_finite_marginals
    (μ : Measure CoordinateTail) [IsProbabilityMeasure μ]
    (h_marg : ∀ (I : Finset ℕ),
      Measure.map I.restrict μ = Measure.pi (fun _ : I => standardGaussian)) :
    μ = coordinateTailMeasure := by
  -- coordinateTailMeasure = gammaMeasure = infinitePi (fun _ => standardGaussian).
  -- A measure on (ℕ → ℝ) equals infinitePi ν iff all finite restrict-marginals
  -- equal Measure.pi ν. Prove by equality on the cylinder π-system:
  --   * cylinder sets {x | I.restrict x ∈ s} generate the product σ-algebra;
  --   * h_marg gives μ on cylinders; finiteCoordinateMarginal (:49) gives the same
  --     for coordinateTailMeasure;
  --   * two probability measures equal on a generating π-system are equal.
```
**Candidate Mathlib lemmas (verify with `#check`):**
`Measure.eq_infinitePi_of_map_restrict` (or prove via `Measure.ext` +
`MeasurableSpace.generateFrom`), `MeasureTheory.Measure.ext_on_pisystem` /
`measure_ext_of_finite` / `DynkinSystem` π-λ argument,
`MeasurableSpace.generateFrom_pi` (cylinders generate). `finiteCoordinateMarginal`
(`:49`) supplies the RHS values.

**Forcing corollary (indistinguishability ⟹ Mehler):**
```lean
/-- If the language cannot distinguish tail points — every finite-coordinate
observable has the same expectation under μ as under the Mehler measure — then μ IS
the Mehler measure. -/
theorem language_blind_implies_mehler
    (μ : Measure CoordinateTail) [IsProbabilityMeasure μ]
    (h_blind : ∀ (I : Finset ℕ) (f : (I → ℝ) → ℝ),
      ∫ x, f (I.restrict x) ∂μ =
        ∫ x, f (I.restrict x) ∂coordinateTailMeasure) :
    μ = coordinateTailMeasure := by
  apply mehler_unique_by_finite_marginals μ
  intro I
  -- h_blind for all f forces equality of the pushed-forward marginal measures
  -- (integral equality for all f ⇒ measure equality); then h_marg follows.
```
Use `Measure.ext` via equality of integrals (`MeasureTheory.integral_eq_integral`
characterization, or test against indicators `f = Set.indicator` and use
`lintegral`/`setIntegral_congr`). This is the formalization of the author's sentence
"the Kopperman language cannot distinguish any element of the infinite-dimensional
Hilbert space, so only the Mehler measure can be the distribution."

## Task B4 — Arbitrary law on the finite part × forced Mehler on the infinite part

**File:** `BookProof/ChapterSolovay.lean` (extend S.3) — package B3 with the
existing head freedom. State it in the COORDINATE model (`CoordinateSpace N`,
`ChapterSolovayCoordinates.lean:123`) to reuse B3 directly; note the abstract
`InnerTail = Substrate` transport as a follow-up.

Current state: `head_vs_tail_admissibility` (`ChapterSolovay.lean:278`) says "heads
admit an arbitrary law AND the tail is admissible." Strengthen to the full claim:
```lean
/-- Full Solovay–Kopperman probability classification on the tensor-product space
`CoordinateSpace N = (finite head) ⊗ (infinite tail)`:
- the finite head carries an ARBITRARY probability law `headDist`;
- the infinite tail carries ONLY the Mehler measure, forced because the language
  cannot distinguish tail points (Task B3).
Any product state `headDist × ν` whose tail `ν` is language-indistinguishable from
the Mehler tail equals `coordinateStateMeasure N headDist`. -/
theorem solovay_kopperman_probability_classification (N : ℕ)
    (headDist : Measure (Fin N → ℝ)) [IsProbabilityMeasure headDist]
    (ν : Measure CoordinateTail) [IsProbabilityMeasure ν]
    (hν_blind : ∀ (I : Finset ℕ) (f : (I → ℝ) → ℝ),
      ∫ x, f (I.restrict x) ∂ν =
        ∫ x, f (I.restrict x) ∂coordinateTailMeasure) :
    headDist.prod ν = coordinateStateMeasure N headDist := by
  -- language_blind_implies_mehler (B3) gives ν = coordinateTailMeasure;
  -- coordinateStateMeasure N headDist = headDist.prod coordinateTailMeasure by def.
```
**Follow-up (optional):** build a measurable isometry `Substrate ≃ᵐ CoordinateTail`
(an orthonormal-basis isometry `L²[0,1] ≅ ℓ²(ℕ)`) and transport B4 to the abstract
`InnerSpace N`. Only attempt after B3/B4 land in the coordinate model.

## Task B5 — Cross-dimensional inner product is well-defined (Mehler splits ⇒ dims match)

**File:** `BookProof/ChapterSolovayCoordinates.lean` / `ChapterSolovay.lean`.

Author's earlier goal: "the cross-dimensional inner product is well-defined because
the Mehler measure splits, so the finite dimensions match." This is largely a
reframing/corollary of Tasks A1–A2 plus an explicit isometry statement.

```lean
/-- Enlarging the head by k Mehler coordinates is measure-preserving (this is
    Task A2), hence the L² inner product is invariant under enlargement: an
    N-head element and an (N+k)-head element can be compared after padding the
    smaller with k fresh Gaussian coordinates, independently of the padding. -/
theorem enlarge_is_measure_preserving (N k : ℕ)
    (headDist : Measure (Fin N → ℝ)) [IsProbabilityMeasure headDist] :
    Measure.map (enlargeEquiv N k) (coordinateStateMeasure N headDist) =
      coordinateStateMeasure (N + k) (enlargedHeadMeasure N k headDist) :=
  enlargeEquiv_map N k headDist

/-- The cross-dimensional inner product is well-defined: cylindrical observables
    embedded into a larger head have the same inner product (the Mehler tail splits
    as Gaussian(k) × tail, Task A1, so the added coordinates integrate to 1). -/
theorem cross_dimensional_inner_well_defined (N k : ℕ) … :
    inner ℂ (embed Ψ) (embed Φ) = inner ℂ Ψ Φ := by
  -- reduce via inner_reduces_to_head (ChapterSolovay.lean:72) on both sides;
  -- the k extra Gaussian coordinates contribute ∫ … ∂gaussianHead k = 1.
```
Depends on A1, A2, and `inner_reduces_to_head`.

---

# Part C — Issues.md-derived hardening (the specialist can close these)

## Task C1 — Full `lake build BookProof` + sorry/axiom audit

After Parts A–D, run:
```bash
lake build BookProof
grep -rn "sorry" BookProof/ PnpProof/ Singularity/ RandomMap/
grep -rn "^axiom" BookProof/ PnpProof/
```
Expected: `sorry` only at `UnusedRoute/SchoenfeldPRA.lean:163,178` (pre-existing,
documented); **no `axiom`** anywhere in `BookProof/` or `PnpProof/` (see C3).

## Task C2 — Replace the `True`-placeholder theorems in `ChapterSelectingEvents.lean`

**File:** `BookProof/ChapterSelectingEvents.lean`. Four theorems currently conclude
`True` via `trivial`. Give them real statements (book.tex Ch. 13 / §3 anchors):

- **C2a — regular conditional probability exists** (line 62; book.tex 1479–1481,
  8505–8526). State existence of a regular conditional probability kernel via
  `MeasureTheory.condExpKernel` / `ProbabilityTheory.condKernel` on a standard
  Borel space. (Coordinate with D2 — same disintegration content.)
- **C2b — the chapter headline: selecting events does not rewrite history**
  (line 200). Replace the `True` conclusion with the actual identity the docstring
  promises (lines 209–216): for `μ E > 0`,
  `μ.cond E F = μ (E ∩ F) / μ E`. Prove with `ProbabilityTheory.cond_apply'` /
  `MeasureTheory.cond_apply`. This is the main theorem of the chapter and must not
  be `trivial`.
- **C2c — Lebesgue continuous/atomic decomposition** (line 133; book.tex
  8677–8786). State the decomposition of a probability measure on a standard Borel
  space into its continuous (atomless) part and its atomic (countable) part.
  Candidate Mathlib: `MeasureTheory.Measure.lebesgueDecomposition`,
  `Measure.hasLebesgueDecomposition`, `Measure.continuousPart` / `atomicPart`.
- **C2d — abelian von Neumann algebra = L∞ (scoped down)** (line 94; book.tex
  1426–1442, 8789–8800). The full 5-class classification is a major undertaking;
  do NOT claim it. Instead prove the direction book.tex actually uses: for a
  standard probability space `(X, μ)`, the abelian von Neumann algebra acting on
  `L²(X, μ)` is `L∞(X, μ)` (the multiplication algebra). Record the 5-class list in
  a docstring as the target, not as a proved theorem.

## Task C3 — De-axiomatize the two `axiom : True` in `ChapterSelectingEvents.lean`

**File:** `BookProof/ChapterSelectingEvents.lean:117,150`. `axiom p_ne_np : True`
and `axiom random_generation_linear_time : True` are content-free but they are
`axiom`s, which the project's own `PnpProof/Kopperman.lean:28–32` docstring
explicitly criticizes ("asserting as an axiom is precisely the act of telling Lean
to stop checking"). Replace with honest alternatives:
- Convert to a stated *proposition* (a `def … : Prop`, not assumed) with a docstring
  recording that it is open / unbridged inside the formalism (per
  `model_vs_clay_disjointness`, T5), **or**
- delete the `axiom` lines and keep only the docstring.

Either way: **no `axiom` may remain in `BookProof/` or `PnpProof/`** (only Mathlib's
own axioms are acceptable). Verify with `grep -rn '^axiom' BookProof/ PnpProof/`.

---

# Part D — book.tex foundational claims to formalize (non-deferred)

**Scope guard.** Do NOT add work for the deferred physics chapters of `Issues.md`
§6 (gauge/BRST, Navier–Stokes/mass-gap, Lorentz/CPT/Majorana representations,
Yang–Mills/Gribov, parity/antiparticles, gravity/diffeomorphisms, consciousness,
deep learning, RH statistical-model-theory). Focus on the probability/foundational
core of book.tex ch. 3 (§§3–6) and ch. 13.

## Task D1 — Joint probability on a tensor product has a wave-function (|Ψ|² = p)

book.tex §3 lines 1489–1490: "there is always a normalized wave-function
`Ψ ∈ L²(X×Y)` such that `|Ψ(x,y)|² = p(x⊗y)`." Formalize the clean finite version:
```lean
theorem joint_prob_has_wavefunction {X Y : Type*} [Fintype X] [Fintype Y]
    (p : X × Y → ℝ) (hp_nonneg : ∀ z, 0 ≤ p z) (hp_sum : ∑ z, p z = 1) :
    ∃ Ψ : X × Y → ℂ, (∀ z, ‖Ψ z‖ ^ 2 = p z) ∧ ∑ z, ‖Ψ z‖ ^ 2 = 1 := by
  -- Ψ z := Real.sqrt (p z) (real, nonneg); ‖Ψ z‖² = p z by norm/Real.sq_sqrt;
  -- the sum is hp_sum.
```
This anchors the tensor-product-of-sample-spaces claim and is fully provable.
**Follow-up D1b (larger):** the unitary/Gram–Schmidt/SVD construction
`p(x,y) = |U(y,x,0)|²` (book.tex 1491–1527) — state as a target after D1.

## Task D2 — Disintegration: joint = marginal × conditional kernel

book.tex §3 lines 1476–1487: `p(x,y) = p(y|x) p₀(x)`; regular conditional
probabilities always exist; `p₀` is independent of `p(y|x)`. Formalize the
measure-theoretic disintegration of a joint measure into marginal × conditional
kernel on standard Borel spaces. Candidate Mathlib: `MeasureTheory.condKernel`,
`Measure.prod_disintegrate` / `Measure.disintegrate`, `condExpKernel`. Overlaps with
C2a — implement once, reference from both.

## Task D3 — A separable probability space with an arbitrary finite law (answers the Intro)

book.tex Intro lines 133–141: "no one has found yet a systematic way to define a
separable probability space with an arbitrary probability measure over …
infinite-dimensional spaces." The Solovay–Kopperman construction is the answer.
State the existence headline (packages B2a/B2b + `stateMeasure_finite_marginal`,
`ChapterSolovay.lean:207`):
```lean
/-- Answer to book.tex Intro (133–141): a separable probability space carrying an
    arbitrary law on the finite head and the Mehler law on the infinite tail, whose
    finite marginal is exactly the chosen law. -/
theorem exists_separable_prob_with_arbitrary_finite_law (N : ℕ)
    (headDist : Measure (InnerHead N)) [IsProbabilityMeasure headDist] :
    ∃ (μ : Measure (InnerSpace N)),
      IsProbabilityMeasure μ ∧
      SeparableSpace (InnerSpace N) ∧
      Measure.map Prod.fst μ = headDist := by
  refine ⟨stateMeasure N headDist, inferInstance, ?_, stateMeasure_finite_marginal N headDist⟩
  -- SeparableSpace (InnerHead N × InnerTail): product of separable spaces
  -- (FiniteDimensional ⇒ separable head; tail_separable from B2b / substrate_separable).
```
(If `SeparableSpace (InnerSpace N)` needs the head separable, derive it from
`FiniteDimensional` (B2a) via `FiniteDimensional.separable`/`separableSpace_of_countable`.)

## Task D4 — L∞ is non-separable, L² is separable (the motivation theorem)

book.tex Ch. 13 lines 8349–8353 + Intro 133–135: "whenever we deal with a
non-separable space … some elements cannot be approximated by a finite set;
`L∞([0,1])` and its dual are both non-separable." Formalize the precise core that
explains WHY the infinite part must be `L²` (separable, with a countable decidable
skeleton — `Kopperman.substrate_decidable_skeleton`, `Kopperman.lean:75`):
```lean
theorem l_infty_unit_non_separable :
    ¬ SeparableSpace (Lp ℝ ∞ unitMeasure) := by
  -- Uncountable 1-separated set: indicators 1_{[0,t]} (t ∈ [0,1]) have pairwise
  -- L∞ distance 1; a separable metric space cannot contain an uncountable
  -- ε-separated set (emetric/separation argument).
theorem l2_unit_separable : SeparableSpace (Lp ℝ 2 unitMeasure) := l2_separable
```
Then state the contrapositive motivation as a docstring/corollary: the Solovay tail
is deliberately `L²` (separable) so its elements ARE approximable by the countable
skeleton, and the language sees only that separable/finite-coordinate structure
(ties directly to B3).

---

## Suggested attack order

1. **A1 → A2** — unblock the existing sorry (everything in Part B that touches the
   tail measure depends on A1).
2. **B3** — the Mehler uniqueness/forcing theorem (the mathematical heart).
3. **B1** — decidable-language tensor closure (small, self-contained).
4. **B2** — finite-dim ⊗ separable-infinite-dim identification (B2a, B2b, B2c-i).
5. **B4** — package B3 + head freedom (depends on B3, B2).
6. **B5** — cross-dimensional inner product (depends on A1, A2, B2).
7. **C2, C3** — harden `ChapterSelectingEvents` (independent of Part B).
8. **D1, D3, D4** — book.tex foundational headlines (D3 depends on B2; D1, D4
   independent). D2/C2a together.
9. **C1** — final full build + sorry/axiom audit.

## Definition of done

- `lake build BookProof` exits 0.
- `grep -rn "sorry" BookProof/ PnpProof/ Singularity/ RandomMap/` shows only
  `UnusedRoute/SchoenfeldPRA.lean:163,178`.
- `grep -rn "^axiom" BookProof/ PnpProof/` is empty.
- The four tensor/Mehler headline theorems exist and are sorry-free:
  B1 closure (`tensor_language_decidable`), B2 identification
  (`innerSpaceTensorEquiv` + `tail_infinite_dimensional` + `head_finrank`),
  B3 uniqueness (`mehler_unique_by_finite_marginals` +
  `language_blind_implies_mehler`), B4 classification
  (`solovay_kopperman_probability_classification`).
- The `ChapterSelectingEvents` headline `selecting_events_not_rewriting_history`
  has a real (non-`True`) conclusion (C2b).

## Constraints

- No new `sorry` or `axiom` (the only acceptable `sorry`s are the two documented
  ones in `UnusedRoute/SchoenfeldPRA.lean:163,178`; no `axiom` anywhere in
  `BookProof/` or `PnpProof/`).
- Lines ≤ 100 chars, no trailing whitespace.
- Do NOT modify `Book/*.lean`, `Book.lean`, `BookMain.lean`, or any `.md` file.
- Do NOT enable `experimental.module` or `autoImplicit = false`.
- New theorems go in `BookProof/ChapterSolovay*.lean` (or a new
  `BookProof/ChapterSolovayTensor.lean`); if a new file is added, coordinate with
  the orchestrator before wiring it into `BookProof.lean`.
- Do NOT touch the deferred physics modules listed in the Part D scope guard.
- The `lake serve` LSP is the build tool; do not run `lake build book`.
- Verify candidate Mathlib lemma names with
  `lake env lean --stdin <<< '#check <name>'` before relying on them (per `AGENTS.md`).
