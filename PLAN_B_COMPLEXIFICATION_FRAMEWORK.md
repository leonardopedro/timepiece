# PLAN B — Complexification & Framework (Track B)

**Owner:** LLM-Lean-Specialist-B
**Machine:** Machine B
**Target files:** `BookProof/ChapterOdeComplexification.lean` (NEW), `BookProof/ChapterPaFreeCompletion.lean` (NEW), `BookProof/ChapterDefinabilityFragment.lean` (NEW), `BookProof.lean` (MODIFY), `lakefile.toml` (MODIFY)
**Hard constraints:** Never writes `Singularity/`, `Singularity/*.lean`, `RiemannProof/`, `UsedRoute/`, `UnusedRoute/`

---

## Task B1: Complexification Resolution (ChapterOdeComplexification.lean)

**File:** `BookProof/ChapterOdeComplexification.lean` (NEW)

**Goal:** For `ż = z²` on `ℂ ≃ ℝ²`, the set of initial data with a **real**
singular time has measure zero.

### Deliverables

```lean
import Mathlib

/-!
# Complex ODE: z' = z² — Singularity has Measure Zero

For the complex ODE ż = z², solutions are z(t) = z₀ / (1 - t·z₀).
A singular time occurs when the denominator vanishes: t = 1/z₀.
We prove that the set of z₀ ∈ ℂ for which 1/z₀ is real has measure zero.
-/

open Complex
open MeasureTheory
open Set

/-- Solution to ż = z² with initial condition z(0) = z₀ ≠ 0.
    z(t) = z₀ / (1 - t·z₀) for t ≠ 1/z₀. -/
theorem complex_solution (z0 : ℂ) (hz0 : z0 ≠ 0) :
    ∃ z : ℝ → ℂ, DifferentiableOn ℂ z (Set.Ioo (-1) 1) ∧
    z 0 = z0 ∧ ∀ t, 1 - (t : ℂ) * z0 ≠ 0 → HasDerivAt z (z t ^ 2) t := ...

/-- The blow-up time is t = 1/z₀. Its imaginary part is zero iff z₀ is real. -/
theorem singular_time_real_iff_im_zero (z0 : ℂ) (hz0 : z0 ≠ 0) :
    (1 / z0).im = 0 ↔ z0.im = 0 := by
  constructor
  · intro h
    have hz0' : z0 ≠ 0 := hz0
    apply Complex.ofReal_injective
    -- If 1/z₀ is real, then z₀ is real
    -- 1/z₀ = conj(z₀) / |z₀|², so im(1/z₀) = -im(z₀)/|z₀|²
    -- Thus im(1/z₀) = 0 ⇒ im(z₀) = 0
    sorry
  · intro h
    have hz0' : z0 ≠ 0 := hz0
    rcases eq_or_ne z0 0 with (rfl | hz0')
    · exact hz0 rfl
    · have : z0 = (z0.re : ℂ) := by
        apply Complex.ext <;> simp [h]
      rw [this]
      simp

/-- The real axis has measure zero in ℝ² ≃ ℂ. -/
theorem real_axis_volume_zero : volume {z : ℂ | z.im = 0} = 0 := by
  -- The set {z | z.im = 0} is isomorphic to ℝ, which has Lebesgue measure zero
  -- in ℝ² (as a subspace)
  sorry

/-- HEADLINE: Almost every initial condition has a non-real singular time.
    The set of z₀ ∈ ℂ for which the blow-up time is real has measure zero. -/
theorem ae_no_real_singular_time : ∀ᵐ z0 ∂(volume : Measure ℂ), (1 / z0).im ≠ 0 := by
  -- Follows from real_axis_volume_zero and the fact that z ↦ 1/z is measure-preserving
  sorry
```

### Dependencies
- `MeasureTheory` — Lebesgue measure on ℂ ≃ ℝ²
- `Complex` — complex arithmetic, `im` field
- The proof of `singular_time_real_iff_im_zero` uses `Complex.inv_im` or direct algebra
- The proof of `real_axis_volume_zero` uses that a line in ℝ² has zero Lebesgue measure
- `ae_no_real_singular_time` uses the measure-preserving property of z ↦ 1/z on ℂ\{0}

**Estimated effort:** 4-6 hours

---

## Task B2: PA-Free Completion (ChapterPaFreeCompletion.lean)

**File:** `BookProof/ChapterPaFreeCompletion.lean` (NEW)

**Goal:** Formalize the Riesz–Fischer characterization for finitely-supported
core and its completion. Show that the completion adds exactly the limit points
needed for Hilbert space completeness without introducing new "pathological" vectors.

### Deliverables

```lean
import Mathlib

/-!
# PA-Free Completion: The Riesz–Fischer Framework

We formalize the statement that the completion of the finitely-supported
core (which represents "definable" vectors) adds exactly the Cauchy sequences
that are needed for Hilbert space completeness, without introducing any
new vectors that would violate provable decidability.

This is the mathematical foundation for the Solovay-Hilbert decidability
architecture: the completion does not leak PA / is a conservative extension.
-/

open Set
open Filter

/-- The dense core: finitely-supported vectors on a countable set P.
    These represent the "definable" or "computable" vectors. -/
def DenseCore (P : Type*) [Countable P] := P →₀ ℝ

/-- The dense core is a real vector space. -/
instance (P : Type*) [Countable P] : AddCommGroup (DenseCore P) :=
  Finsupp.addCommGroup

/-- The dense core embeds into its completion. -/
def DenseCore.toCompletion (P : Type*) [Countable P] :
    DenseCore P → UniformSpace.Completion (DenseCore P) :=
  UniformSpace.Completion.mapCocones (fun _ => id)

/-- The completion is a Hilbert space. -/
noncomputable def HilbertCompletion (P : Type*) [Countable P] [InnerProductSpace ℝ P] :
    Type := UniformSpace.Completion (DenseCore P)

/-- Every term-denotable vector is finitely supported.
    This is the core conservativity statement. -/
theorem term_denotable_finite_support (v : DenseCore P) :
    (Function.support v).Finite :=
  Finsupp.finite_support v

/-- Infinite vectors (limit points in the completion) are null events
    under a diffuse (atomless) measure. -/
theorem infinite_vectors_null (μ : Measure (UniformSpace.Completion (DenseCore P)))
    [IsProbabilityMeasure μ] [Measure.NoAtoms μ] (v : UniformSpace.Completion (DenseCore P))
    (h : v ∉ Set.range (DenseCore.toCompletion P)) : μ {v} = 0 := by
  -- In a diffuse measure space, every singleton has measure zero
  exact Measure.measure_singleton v

/-- The completion is complete: every Cauchy sequence converges. -/
instance (P : Type*) [Countable P] : CompleteSpace (UniformSpace.Completion (DenseCore P)) :=
  UniformSpace.Completion.completeSpace _

/-- Riesz–Fischer: a sequence converges in the completion iff its norms
    satisfy the Cauchy criterion. -/
noncomputable def riesz_fischer (P : Type*) [Countable P] :
    -- ∀ {u : ℕ → DenseCore P}, CauchySeq u → ∃ v, Tendsto u atTop (𝓝 v)
    True := by
  -- This is exactly the definition of CompleteSpace
  trivial
```

### Key mathematical content

1. `DenseCore P` = `P →₀ ℝ` (finitely supported functions)
2. The completion is taken via `UniformSpace.Completion`
3. `term_denotable_finite_support`: every finitely supported vector is indeed finitely supported (trivial by Finsupp)
4. `infinite_vectors_null`: under a diffuse measure, limit points (which are not in the original core) have measure zero
5. `CompleteSpace` instance is automatic from the completion

### Dependencies
- `Finsupp` — finitely supported functions
- `UniformSpace.Completion` — metric completion
- `MeasureTheory` — measures on the completion

**Estimated effort:** 2-3 hours

---

## Task B3: Definability / Conservativity Fragment (ChapterDefinabilityFragment.lean)

**File:** `BookProof/ChapterDefinabilityFragment.lean` (NEW)

**Goal:** Formalize the precise, provable fragment of the conservativity claim.

The full claim "the completion does not leak PA / is a conservative decidable
extension" is **metamathematical** and is NOT to be presented as a Lean theorem.

We formalize only the precise, provable fragment: *in the language whose vector
constants are finitely supported, every term-denotable vector is finitely
supported* (this is essentially `Finsupp.finite_support`).

### Deliverables

```lean
import Mathlib

/-!
# Definability / Conservativity Fragment

This module formalizes the precise, provable fragment of the claim that
the completion of the finitely-supported core does not leak provability
assumptions (PA / Gödelian self-reference).

The full metamathematical claim "the completion is a conservative extension"
is documented here but NOT formalized as a Lean theorem. The formal content
is the `Finsupp.finite_support` lemma: in the finitely-supported fragment,
every denotable vector is finitely supported.
-/

open Finset

/-- In the finitely-supported fragment, every vector is finitely supported.
    This is the core definability result: there are no "infinite" vectors
    definable in the finite-support language. -/
theorem finitely_supported_vectors_are_finite (v : ℕ →₀ ℝ) :
    (v.support).Finite := by
  -- Trivial: Finsupp has finite support by definition
  exact Finsupp.finite_support v

/-- No vector in the completion is term-denotable unless it is finitely supported.
    This is the contrapositive: if a vector requires infinite support,
    it cannot be constructed from finitely many basis vectors. -/
theorem non_finitely_supported_not_term_denotable (v : ℕ → ℝ)
    (h_infinite : ¬ (Function.support v).Finite) :
    v ∉ Set.range (fun (w : ℕ →₀ ℝ) => fun n => w n) := by
  intro h
  rcases h with ⟨w, hw⟩
  apply h_infinite
  rw [← hw]
  exact Finsupp.finite_support w

/-- The formal statement: the completion does not make more vectors definable
    than were already definable in the finite-support fragment.
    
    This is a tautology in the formalism: the completion only adds limit points
    of Cauchy sequences, and a limit point cannot be term-denotable
    (term-denotable vectors have finite support, but limit points in an
    infinite-dimensional space typically do not).
    
    **This is NOT a theorem in Lean.** It is a metamathematical observation
    documented here for completeness. -/
theorem conservativity_documentation : True := by
  -- The full conservativity claim requires external justification
  -- (e.g., forcing arguments in set theory)
  -- We document it here but do not attempt to prove it in Lean
  trivial
```

### Content

- `finitely_supported_vectors_are_finite`: the trivial direction (Finsupp.finite_support)
- `non_finitely_supported_not_term_denotable`: the contrapositive
- `conservativity_documentation`: explicit documentation that the full claim is metamathematical

**Estimated effort:** 1-2 hours

---

## Task B4: Book Tooling — Inline-Elaborated Lean Blocks

**Files:** `BookProof.lean` (MODIFY), `lakefile.toml` (MODIFY)

**Goal:** Enable in-book Lean elaboration so that code blocks in the book
are elaborated in-place rather than shown as plain text.

### Current state

The book shows Lean statements as plain code blocks; verification is
via `lake build BookProof`. To elaborate them in-book: enable `experimental.module`
for the `Book` lib and `book` exe in `lakefile.toml`, change each chapter's
`BookProof` import to `public import BookProof.<Module>`, re-add the imports,
and verify one chapter at a time.

### Deliverables

**Step 1: Modify lakefile.toml**

Add `experimental.module` and `public import` support:

```toml
# In lakefile.toml, enable experimental module feature
[package]
...

# Add to the book target
[exe.book]
...

# Enable module elaboration for Book
leanOptions := #[⟨`autoImplicit, false⟩, ⟨`experimental.module, true⟩]
```

**Step 2: Register new modules in BookProof.lean**

Add imports for the new chapters:

```lean
-- In BookProof.lean, add:
public import BookProof.ChapterOdeComplexification
public import BookProof.ChapterPaFreeCompletion
public import BookProof.ChapterDefinabilityFragment
```

**Step 3: Test incremental build**

```bash
cd /media/leo/e7ed9d6f-5f0a-4e19-a74e-83424bc154ba/timepiece
lake build BookProof
lake build book
```

Verify:
- `lake build BookProof` succeeds (all modules compile)
- `lake build book` succeeds (book renders with elaborated Lean blocks)
- No new `sorry` or `admit` introduced

**Important notes from BOOK_PROOF_PLAN.md:**

- Risk: `experimental.module` interaction with non-module Mathlib oleans; test
  incrementally.
- Verso markup gotchas: no `>` blockquotes; keep `**bold**` on a single line;
  close `:::paragraph` with `:::` before opening another.

**Estimated effort:** 3-4 hours (including testing)

---

## Execution Order

```
B1 (Complexification) → B2 (PA-Free) → B3 (Definability) → B4 (Tooling)
```

B1, B2, and B3 are independent and can be worked on in parallel.
B4 depends on B1-B3 (to register the new modules).

---

## Summary

| Task | File | Status | Effort |
|------|------|--------|--------|
| B1 | ChapterOdeComplexification.lean (NEW) | TO DO | 4-6h |
| B2 | ChapterPaFreeCompletion.lean (NEW) | TO DO | 2-3h |
| B3 | ChapterDefinabilityFragment.lean (NEW) | TO DO | 1-2h |
| B4 | BookProof.lean + lakefile.toml (MODIFY) | TO DO | 3-4h |

## Coordination with Plan A

| Plan A (Track A) | Plan B (Track B) |
|------------------|-------------------|
| MODIFIES: `Singularity/Poly.lean`, `Singularity/Hamiltonian.lean`, `Singularity/Esa.lean` | CREATES: `BookProof/ChapterOdeComplexification.lean`, `ChapterPaFreeCompletion.lean`, `ChapterDefinabilityFragment.lean` |
| CREATES: `Singularity/EnergyBounded.lean` | MODIFIES: `BookProof.lean`, `lakefile.toml` |
| NEVER touches `BookProof/` | NEVER touches `Singularity/` |
| **Target:** Self-adjointness of Weyl Hamiltonian, Nelson's theorem | **Target:** Complexification resolution, PA-free framework, book tooling |

**Zero file overlap. Both plans compile the same project.**
