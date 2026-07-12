import Mathlib
import Mathlib.Analysis.InnerProductSpace.Basic
import Mathlib.Analysis.NormedSpace.LpSpace
import Mathlib.MeasureTheory.Measure.ProbabilityMeasure
import RiemannProof.SchoenfeldPRA

/-!
# RandomMap2.lean — The Decoupled Kopperman-Solovay Framework

This file implements the formalization plan described in `RandomMap2.md`.
It constructs a probability space whose *points* are infinite-dimensional
wave-functions (inner), while its *evaluations* remain decidable via
Tarski's Real Closed Fields (outer).

The decoupling is achieved by:
1. **Inner language (Ontology):** defines the points of the sample space
   (the inner wave-functions), split into a finite Tarski head and an
   infinite Kopperman tail.
2. **Outer language (Epistemology):** defines probability amplitudes over
   the inner wave-functions, depending *only* on the finite head.
3. **Decoupling theorem:** the L² inner product over the infinite space
   collapses to a finite-dimensional Tarski-decidable integral.
-/

open MeasureTheory ProbabilityTheory
open RiemannProof.SchoenfeldPRA

noncomputable section

/-! ## Phase 1: The Inner Wave-Function (The Sample Space) -/

/-! ### 1.1 The Kopperman Tail -/

/-- The infinite, unknown tail of the inner wave-function.
    Modeled precisely by the Kopperman Substrate (L²[0,1]). -/
abbrev InnerTail := Substrate

/-- The uniform probability measure over the infinite tail (the Mehler/Kopperman prior) -/
def tailMeasure : Measure InnerTail := rcpPriorOnSubstrate

instance : IsProbabilityMeasure tailMeasure := rcpPriorOnSubstrate_isProb

/-! ### 1.2 The Tarski Head and the Total Space -/

/-- The finite known components of the inner wave-function -/
def InnerHead (N : ℕ) := Fin N → ℝ

/-- The total sample space of inner wave-functions -/
def InnerSpace (N : ℕ) := InnerHead N × InnerTail

/-- The total probability measure, given an arbitrary law on the head -/
noncomputable def stateMeasure (N : ℕ) (headDist : Measure (InnerHead N))
    [IsProbabilityMeasure headDist] : Measure (InnerSpace N) :=
  headDist.prod tailMeasure

instance (N : ℕ) (headDist : Measure (InnerHead N)) [IsProbabilityMeasure headDist] :
    IsProbabilityMeasure (stateMeasure N headDist) :=
  Measure.isProbabilityMeasure_prod

/-! ## Phase 2: The Outer Wave-Function (The Solovay Space) -/

/-! ### 2.1 Defining the Outer Wave-Function -/

/-- A macroscopic observable function depends only on the finite head -/
def dependsOnlyOnHead {N : ℕ} (f : InnerSpace N → ℂ) : Prop :=
  ∃ g : InnerHead N → ℂ, f = g ∘ Prod.fst

/-- The Solovay space of Outer Wave-functions.
    These are L² functions on `InnerSpace` that (a.e.) depend only on the
    finite head. We deliberately do NOT assert `CompleteSpace` here,
    keeping the space within Solovay's decidable pre-Hilbert boundaries. -/
structure OuterWaveFunction (N : ℕ) (headDist : Measure (InnerHead N))
    [IsProbabilityMeasure headDist] where
  val : Lp ℂ 2 (stateMeasure N headDist)
  is_cylindrical : dependsOnlyOnHead val

/-! ### 2.2 The Solovay-Hilbert Structure -/

/-- Equip `OuterWaveFunction` with a `NormedAddCommGroup` instance. -/
noncomputable instance (N : ℕ) (headDist : Measure (InnerHead N))
    [IsProbabilityMeasure headDist] : NormedAddCommGroup (OuterWaveFunction N headDist) :=
  inferInstanceAs (NormedAddCommGroup (Lp ℂ 2 (stateMeasure N headDist)))

/-- Equip `OuterWaveFunction` with a `InnerProductSpace ℂ` instance.
    This is the pre-Hilbert structure; we do NOT provide `CompleteSpace`,
    keeping the space within Solovay's decidable boundaries. -/
noncomputable instance (N : ℕ) (headDist : Measure (InnerHead N))
    [IsProbabilityMeasure headDist] : InnerProductSpace ℂ (OuterWaveFunction N headDist) :=
  inferInstanceAs (InnerProductSpace ℂ (Lp ℂ 2 (stateMeasure N headDist)))

/-! ## Phase 3: The Decoupling Theorem (Dimensional Reduction) -/

/-! ### 3.1 The Fubini-Tonelli Reduction -/

/-- The inner product of outer wave-functions reduces to a finite Tarski-decidable
    integral over the head. Because the outer wave-functions depend only on the head
    and the tail measure is an independent probability measure, the L² inner product
    over the infinite-dimensional `InnerSpace` collapses exactly to a finite-dimensional
    integral over `ℝ^N`. -/
theorem outer_inner_reduces_to_head {N : ℕ} {headDist : Measure (InnerHead N)}
    [IsProbabilityMeasure headDist] (Ψ₁ Ψ₂ : OuterWaveFunction N headDist) :
    ∃ (g₁ g₂ : Lp ℂ 2 headDist),
      ⟪Ψ₁, Ψ₂⟫ = ∫ x, g₁ x * conj (g₂ x) ∂headDist := by
  -- Extract the underlying functions on the InnerHead from the cylindrical condition
  rcases Ψ₁.is_cylindrical with ⟨g₁', hg₁⟩
  rcases Ψ₂.is_cylindrical with ⟨g₂', hg₂⟩
  -- hg₁ : (Ψ₁.val : InnerSpace N → ℂ) = g₁' ∘ Prod.fst  (pointwise equality)
  -- hg₂ : (Ψ₂.val : InnerSpace N → ℂ) = g₂' ∘ Prod.fst
  have h_tail_ne_zero : tailMeasure ≠ 0 := by
    have h_univ_one : tailMeasure Set.univ = 1 := measure_univ
    intro h_eq
    have h_univ_zero : tailMeasure Set.univ = 0 := by simpa [h_eq] using measure_univ
    linarith
  -- The map_fst_prod lemma: Measure.map Prod.fst (headDist.prod tailMeasure) = (tailMeasure univ) • headDist
  -- Since tailMeasure is a probability measure, this equals headDist
  have h_map_fst : Measure.map Prod.fst (headDist.prod tailMeasure) = headDist := by
    rw [Measure.map_fst_prod, measure_univ, one_smul]
  -- From the Lp membership, we have AEStronglyMeasurable and HasFiniteIntegral for Ψ₁.val
  have h_ae₁ : AEStronglyMeasurable (Ψ₁.val : InnerSpace N → ℂ) (headDist.prod tailMeasure) :=
    Lp.aestronglyMeasurable _
  have h_ae₂ : AEStronglyMeasurable (Ψ₂.val : InnerSpace N → ℂ) (headDist.prod tailMeasure) :=
    Lp.aestronglyMeasurable _
  -- Since Ψ₁.val = g₁' ∘ Prod.fst, we get AEStronglyMeasurable for g₁' ∘ Prod.fst
  have h_ae_comp₁ : AEStronglyMeasurable (g₁' ∘ Prod.fst) (headDist.prod tailMeasure) := by
    rw [← hg₁]; exact h_ae₁
  have h_ae_comp₂ : AEStronglyMeasurable (g₂' ∘ Prod.fst) (headDist.prod tailMeasure) := by
    rw [← hg₂]; exact h_ae₂
  -- By AEStronglyMeasurable.of_comp_fst, g₁' and g₂' are AEStronglyMeasurable on the head
  have h_ae_g₁ : AEStronglyMeasurable g₁' headDist :=
    h_ae_comp₁.of_comp_fst h_tail_ne_zero
  have h_ae_g₂ : AEStronglyMeasurable g₂' headDist :=
    h_ae_comp₂.of_comp_fst h_tail_ne_zero
  -- Memℒp membership for g₁' ∘ Prod.fst and g₂' ∘ Prod.fst
  have h_mem_comp₁ : Memℒp (g₁' ∘ Prod.fst) 2 (headDist.prod tailMeasure) := by
    rw [← hg₁]; exact Lp.memLp _
  have h_mem_comp₂ : Memℒp (g₂' ∘ Prod.fst) 2 (headDist.prod tailMeasure) := by
    rw [← hg₂]; exact Lp.memLp _
  -- Use memLp_map_measure_iff to convert from product measure to head measure
  -- Measure.map Prod.fst (headDist.prod tailMeasure) = headDist (since tailMeasure is a probability measure)
  have h_mem_g₁ : Memℒp g₁' 2 headDist := by
    have h_ae_map : AEStronglyMeasurable g₁' (Measure.map Prod.fst (headDist.prod tailMeasure)) := by
      rw [h_map_fst]; exact h_ae_g₁
    have h_meas_fst : AEMeasurable Prod.fst (headDist.prod tailMeasure) :=
      measurable_fst.aemeasurable
    have h_equiv := memLp_map_measure_iff h_ae_map h_meas_fst
    rw [h_map_fst] at h_equiv
    exact h_equiv.mpr h_mem_comp₁
  have h_mem_g₂ : Memℒp g₂' 2 headDist := by
    have h_ae_map : AEStronglyMeasurable g₂' (Measure.map Prod.fst (headDist.prod tailMeasure)) := by
      rw [h_map_fst]; exact h_ae_g₂
    have h_meas_fst : AEMeasurable Prod.fst (headDist.prod tailMeasure) :=
      measurable_fst.aemeasurable
    have h_equiv := memLp_map_measure_iff h_ae_map h_meas_fst
    rw [h_map_fst] at h_equiv
    exact h_equiv.mpr h_mem_comp₂
  -- Construct the Lp elements
  let g₁ : Lp ℂ 2 headDist := Lp.mk g₁' h_mem_g₁
  let g₂ : Lp ℂ 2 headDist := Lp.mk g₂' h_mem_g₂
  refine ⟨g₁, g₂, ?_⟩
  -- Now compute the inner product
  -- ⟪Ψ₁, Ψ₂⟫ = ∫ z, ⟪Ψ₁.val z, Ψ₂.val z⟫ ∂(stateMeasure N headDist)
  -- = ∫ z, (g₁' z.1) * conj (g₂' z.1) ∂(headDist.prod tailMeasure)  (by hg₁, hg₂)
  calc
    ⟪Ψ₁, Ψ₂⟫ = ∫ z : InnerSpace N, ⟪(Ψ₁.val : InnerSpace N → ℂ) z, (Ψ₂.val : InnerSpace N → ℂ) z⟫
        ∂(stateMeasure N headDist) := rfl
    _ = ∫ z : InnerSpace N, ⟪(Ψ₁.val : InnerSpace N → ℂ) z, (Ψ₂.val : InnerSpace N → ℂ) z⟫
        ∂(headDist.prod tailMeasure) := by rw [stateMeasure]
    _ = ∫ z : InnerSpace N, ((g₁' ∘ Prod.fst) z) * conj ((g₂' ∘ Prod.fst) z)
        ∂(headDist.prod tailMeasure) := by
      refine integral_congr_ae ?_
      filter_upwards with z
      simp [hg₁, hg₂]
    _ = ∫ z : InnerSpace N, (g₁' z.1) * conj (g₂' z.1) ∂(headDist.prod tailMeasure) := rfl
    _ = ∫ x, (g₁' x) * conj (g₂' x) ∂headDist := by
      -- Use Fubini's theorem
      -- Let f (x, y) := (g₁' x) * conj (g₂' x)
      -- Then f ∘ Prod.fst = the integrand
      -- We know f ∘ Prod.fst is integrable (from integrable_inner)
      -- So f is integrable w.r.t. headDist (by Integrable.of_comp_fst)
      -- Then integral_prod f gives the result
      have h_int_comp : Integrable (fun z : InnerSpace N => (g₁' z.1) * conj (g₂' z.1))
          (headDist.prod tailMeasure) := by
        -- From integrable_inner for Ψ₁.val and Ψ₂.val
        -- integrable_inner f g : Integrable (fun x => ⟪f x, g x⟫) μ for f, g : Lp 𝕜 2 μ
        have h_int_inner : Integrable (fun z : InnerSpace N =>
            ⟪(Ψ₁.val : InnerSpace N → ℂ) z, (Ψ₂.val : InnerSpace N → ℂ) z⟫)
            (headDist.prod tailMeasure) := by
          rw [← stateMeasure]
          exact integrable_inner (𝕜 := ℂ) Ψ₁.val Ψ₂.val
        -- Now rewrite using hg₁, hg₂
        have h_eq : (fun z : InnerSpace N => (g₁' z.1) * conj (g₂' z.1)) =ᵐ[headDist.prod tailMeasure]
            (fun z => ⟪(Ψ₁.val : InnerSpace N → ℂ) z, (Ψ₂.val : InnerSpace N → ℂ) z⟫) := by
          filter_upwards with z
          simp [hg₁, hg₂]
        exact (integrable_congr h_eq).mp h_int_inner
      -- Now use integral_prod_symm for the correct order
      have h_fubini : ∫ z : InnerSpace N, (g₁' z.1) * conj (g₂' z.1) ∂(headDist.prod tailMeasure) =
          ∫ y, ∫ x, (g₁' x) * conj (g₂' x) ∂headDist ∂tailMeasure := by
        rw [integral_prod_symm (fun z : InnerHead N × InnerTail => (g₁' z.1) * conj (g₂' z.1)) h_int_comp]
      rw [h_fubini]
      -- Now: ∫ y, (∫ x, (g₁' x) * conj (g₂' x) ∂headDist) ∂tailMeasure
      -- The inner integral doesn't depend on y, so we can factor it out
      -- ∫ y, c ∂tailMeasure = c * (tailMeasure univ).toReal = c * 1 = c
      simp [integral_const, measure_univ]
    _ = ∫ x, g₁ x * conj (g₂ x) ∂headDist := by
      -- g₁ and g₂ equal g₁' and g₂' in Lp sense
      -- So the integrals are equal
      refine integral_congr_ae ?_
      -- Lp.mk g₁' h₁ equals g₁' in the Lp sense
      -- Actually, (Lp.mk g₁' h₁ : InnerHead N → ℂ) = g₁'  (pointwise)
      -- Similarly for g₂
      -- So the integrals are equal
      simp [g₁, g₂]
