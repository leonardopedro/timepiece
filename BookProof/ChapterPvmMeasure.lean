import Mathlib
import BookProof.ChapterOrthogonalSums

/-!
# Projection-valued measures on a measurable base, and the measure of a vector

This file is the first step in removing the honest boundary recorded with
`BookProof.ChapterMackeyQuasiInvariant`: over a *continuous* (measure-theoretic) base only
the **induced direction** of Mackey's imprimitivity theorem was formalized, the converse
being available only for a discrete base (`BookProof.ChapterMackeyGeneralBase`).

Here we set up the objects the converse needs.

* `Pvm X H` — a projection-valued measure on the measurable space `X` acting on the complex
  inner-product space `H`: a family `p E` of operators, self-adjoint, multiplicative on
  intersections, normalized (`p univ = 1`) and countably additive in the unconditional
  (`HasSum`) sense.
* `pvmMeasure P ψ` — the scalar measure `E ↦ ‖p E ψ‖²` attached to a vector, a *finite*
  measure on `X`.
* `pvm_eq_zero_of_measure_zero` — for a **cyclic** vector, a set of measure zero carries the
  zero projection: the measure class of `pvmMeasure P ψ` determines the measure algebra of
  the projection-valued measure.

Everything is `sorry`-free and uses only the standard axioms.
-/

open MeasureTheory
open scoped InnerProductSpace

namespace BookProof.ChapterPvmMeasure

variable {X : Type*} [MeasurableSpace X]
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- A **projection-valued measure** on the measurable space `X`, acting on `H`: the
operators `p E` are self-adjoint, multiplicative on intersections of measurable sets,
`p univ = 1`, and countably additive in the unconditional sense. -/
structure Pvm (X H : Type*) [MeasurableSpace X] [NormedAddCommGroup H]
    [InnerProductSpace ℂ H] where
  /-- The projection attached to a set. -/
  p : Set X → (H →L[ℂ] H)
  /-- Self-adjointness. -/
  symm : ∀ {E : Set X}, MeasurableSet E → ∀ u v : H, ⟪p E u, v⟫_ℂ = ⟪u, p E v⟫_ℂ
  /-- Multiplicativity on intersections. -/
  inter : ∀ {E F : Set X}, MeasurableSet E → MeasurableSet F → ∀ u : H,
    p E (p F u) = p (E ∩ F) u
  /-- Normalization. -/
  univ : ∀ u : H, p Set.univ u = u
  /-- Countable additivity, unconditionally. -/
  hasSum : ∀ f : ℕ → Set X, (∀ i, MeasurableSet (f i)) → Pairwise (Function.onFun Disjoint f) →
    ∀ u : H, HasSum (fun i => p (f i) u) (p (⋃ i, f i) u)

namespace Pvm

variable (P : Pvm X H)

/-- The empty set carries the zero projection. -/
theorem p_empty (u : H) : P.p ∅ u = 0 := by
  have hdisj : Pairwise (Function.onFun Disjoint (fun _ : ℕ => (∅ : Set X))) := by
    intro i j _
    simp [Function.onFun]
  have h := P.hasSum (fun _ : ℕ => (∅ : Set X)) (fun _ => MeasurableSet.empty) hdisj u
  have h0 : Filter.Tendsto (fun _ : ℕ => P.p ∅ u) Filter.atTop (nhds 0) :=
    h.summable.tendsto_atTop_zero
  exact tendsto_const_nhds_iff.mp h0

/-- Idempotence. -/
theorem idem {E : Set X} (hE : MeasurableSet E) (u : H) : P.p E (P.p E u) = P.p E u := by
  rw [P.inter hE hE u, Set.inter_self]

/-- Disjoint sets carry orthogonal projections. -/
theorem orthogonal {E F : Set X} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hd : Disjoint E F) (u : H) : P.p E (P.p F u) = 0 := by
  rw [P.inter hE hF u, Set.disjoint_iff_inter_eq_empty.mp hd, P.p_empty]

/-- Vectors in the ranges of the projections of disjoint sets are orthogonal. -/
theorem inner_eq_zero {E F : Set X} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hd : Disjoint E F) (u v : H) : ⟪P.p E u, P.p F v⟫_ℂ = 0 := by
  rw [P.symm hE, P.orthogonal hE hF hd, inner_zero_right]

/-- Finite additivity of the squared norms on a disjoint pair. -/
theorem norm_sq_nonneg (E : Set X) (u : H) : 0 ≤ ‖P.p E u‖ ^ 2 := by positivity

/-- **Finite additivity** on a disjoint pair of measurable sets. -/
theorem add_of_disjoint {E F : Set X} (hE : MeasurableSet E) (hF : MeasurableSet F)
    (hd : Disjoint E F) (u : H) : P.p (E ∪ F) u = P.p E u + P.p F u := by
  classical
  have hmeas : ∀ i : ℕ, MeasurableSet (if i = 0 then E else if i = 1 then F else (∅ : Set X)) := by
    intro i
    by_cases h0 : i = 0
    · simp [h0, hE]
    · by_cases h1 : i = 1 <;> simp [h0, h1, hF]
  have hdisj : Pairwise (Function.onFun Disjoint
      (fun i : ℕ => if i = 0 then E else if i = 1 then F else (∅ : Set X))) := by
    intro i j hij
    simp only [Function.onFun]
    by_cases hi0 : i = 0 <;> by_cases hi1 : i = 1 <;> by_cases hj0 : j = 0 <;>
      by_cases hj1 : j = 1 <;>
      simp_all [hd]
  have hunion : (⋃ i : ℕ, if i = 0 then E else if i = 1 then F else (∅ : Set X)) = E ∪ F := by
    apply Set.Subset.antisymm
    · refine Set.iUnion_subset fun i => ?_
      by_cases h0 : i = 0
      · simp [h0]
      · by_cases h1 : i = 1 <;> simp [h0, h1]
    · refine Set.union_subset ?_ ?_
      · intro x hx; exact Set.mem_iUnion.mpr ⟨0, by simpa using hx⟩
      · intro x hx; exact Set.mem_iUnion.mpr ⟨1, by simpa using hx⟩
  have hsum := P.hasSum _ hmeas hdisj u
  rw [hunion] at hsum
  have hsum2 : HasSum
      (fun i : ℕ => P.p (if i = 0 then E else if i = 1 then F else (∅ : Set X)) u)
      (∑ i ∈ ({0, 1} : Finset ℕ),
        P.p (if i = 0 then E else if i = 1 then F else (∅ : Set X)) u) := by
    refine hasSum_sum_of_ne_finset_zero ?_
    intro i hi
    have h0 : i ≠ 0 := fun h => hi (by simp [h])
    have h1 : i ≠ 1 := fun h => hi (by simp [h])
    simp [h0, h1, P.p_empty]
  have hval := hsum.unique hsum2
  rw [hval]
  simp

end Pvm

/-! ## The scalar measure attached to a vector -/

/-- The measure `E ↦ ‖p E ψ‖²` of a vector: a finite measure on the base. -/
noncomputable def pvmMeasure (P : Pvm X H) (ψ : H) : Measure X :=
  Measure.ofMeasurable (fun E _ => ENNReal.ofReal (‖P.p E ψ‖ ^ 2))
    (by simp [P.p_empty])
    (by
      intro f hf hdisj
      have hsum : HasSum (fun i => ‖P.p (f i) ψ‖ ^ 2) (‖P.p (⋃ i, f i) ψ‖ ^ 2) :=
        BookProof.ChapterOrthogonalSums.hasSum_norm_sq_of_hasSum
          (P.hasSum f hf hdisj ψ)
          (fun i j hij => P.inner_eq_zero (hf i) (hf j) (hdisj hij) ψ ψ)
      rw [← hsum.tsum_eq,
        ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hsum.summable])

variable (P : Pvm X H) (ψ : H)

@[simp] theorem pvmMeasure_apply {E : Set X} (hE : MeasurableSet E) :
    pvmMeasure P ψ E = ENNReal.ofReal (‖P.p E ψ‖ ^ 2) :=
  Measure.ofMeasurable_apply E hE

theorem pvmMeasure_univ : pvmMeasure P ψ Set.univ = ENNReal.ofReal (‖ψ‖ ^ 2) := by
  rw [pvmMeasure_apply P ψ MeasurableSet.univ, P.univ]

instance : IsFiniteMeasure (pvmMeasure P ψ) :=
  ⟨by rw [pvmMeasure_univ]; exact ENNReal.ofReal_lt_top⟩

theorem pvmMeasure_eq_zero_iff {E : Set X} (hE : MeasurableSet E) :
    pvmMeasure P ψ E = 0 ↔ P.p E ψ = 0 := by
  rw [pvmMeasure_apply P ψ hE, ENNReal.ofReal_eq_zero]
  constructor
  · intro h
    have : ‖P.p E ψ‖ ^ 2 = 0 := le_antisymm h (by positivity)
    simpa using pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
  · intro h
    simp [h]

attribute [irreducible] pvmMeasure

/-! ## Cyclic vectors -/

/-- The set of vectors `p E ψ`: its closed span is the cyclic subspace generated by `ψ`. -/
def pvmOrbit (P : Pvm X H) (ψ : H) : Set H := {v | ∃ E : Set X, MeasurableSet E ∧ v = P.p E ψ}

/-- `ψ` is a **cyclic vector** for `P` when the vectors `p E ψ` span a dense subspace. -/
def IsCyclic (P : Pvm X H) (ψ : H) : Prop :=
  Dense ((Submodule.span ℂ (pvmOrbit P ψ) : Submodule ℂ H) : Set H)

/-- For a cyclic vector, a set of measure zero carries the **zero projection**. -/
theorem pvm_eq_zero_of_measure_zero (hcyc : IsCyclic P ψ) {E : Set X} (hE : MeasurableSet E)
    (h0 : pvmMeasure P ψ E = 0) : P.p E = 0 := by
  have hEψ : P.p E ψ = 0 := (pvmMeasure_eq_zero_iff P ψ hE).mp h0
  -- the projection kills the generating vectors
  have hgen : ∀ v ∈ pvmOrbit P ψ, P.p E v = 0 := by
    rintro _ ⟨F, hF, rfl⟩
    have hEF : pvmMeasure P ψ (E ∩ F) = 0 :=
      measure_mono_null Set.inter_subset_left h0
    have := (pvmMeasure_eq_zero_iff P ψ (hE.inter hF)).mp hEF
    rw [P.inter hE hF ψ]
    exact this
  -- hence the whole closed span
  have hspan : ∀ v ∈ (Submodule.span ℂ (pvmOrbit P ψ) : Submodule ℂ H), P.p E v = 0 := by
    intro v hv
    induction hv using Submodule.span_induction with
    | mem x hx => exact hgen x hx
    | zero => simp
    | add x y _ _ hx hy => simp [map_add, hx, hy]
    | smul c x _ hx => simp [map_smul, hx]
  have hclosed : IsClosed {v : H | P.p E v = 0} := isClosed_eq (P.p E).continuous continuous_const
  have hsub : ((Submodule.span ℂ (pvmOrbit P ψ) : Submodule ℂ H) : Set H)
      ⊆ {v : H | P.p E v = 0} := hspan
  ext v
  have hv : v ∈ closure ((Submodule.span ℂ (pvmOrbit P ψ) : Submodule ℂ H) : Set H) := by
    rw [hcyc.closure_eq]; trivial
  have := (closure_minimal hsub hclosed) hv
  simpa using this

end BookProof.ChapterPvmMeasure
