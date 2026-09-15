import Mathlib
import BookProof.ChapterMackeyQuasiInvariant
import BookProof.ChapterOrthogonalSums

/-!
# Countable additivity of the projection-valued measure over a continuous base

`BookProof.ChapterMackeyQuasiInvariant` builds Mackey's induced system of imprimitivity over
a continuous base: the induced representation on `L²(X, μ; K)` for a quasi-invariant measure
`μ`, and multiplication by indicators as the projection-valued measure, with idempotence,
multiplicativity, self-adjointness, the unit at the whole base and *finite* additivity.

This file adds the remaining defining property of a projection-valued measure, **countable
additivity in the strong operator sense**:

* `norm_sq_proj` — the squared norm of `P(A) f` is the integral of `‖f‖²` over `A`;
* `proj_orthogonal` — disjoint sets give orthogonal images;
* **`proj_hasSum_iUnion`** — for a countable family of pairwise disjoint measurable sets the
  family `n ↦ P(Eₙ) f` is unconditionally summable, with sum `P(⋃ₙ Eₙ) f`.

The proof is the Hilbert-space one: the terms are pairwise orthogonal, and the series of
their squared norms converges — by countable additivity of the Lebesgue integral — to the
squared norm of `P(⋃ₙ Eₙ) f`, so the sum exists (`BookProof.ChapterOrthogonalSums`);
Parseval and the inner products `⟪P(Eₙ) f, P(⋃ₙ Eₙ) f⟫ = ‖P(Eₙ) f‖²` then identify it with
`P(⋃ₙ Eₙ) f`.

Everything is `sorry`-free and uses only the standard axioms.
-/

open MeasureTheory Measure
open scoped InnerProductSpace

namespace BookProof.ChapterMackeyQuasiInvariant

variable {X K : Type*} [MeasurableSpace X]
variable [NormedAddCommGroup K] [InnerProductSpace ℂ K]

/-! ## Norms of the projections -/

omit [InnerProductSpace ℂ K] in
/-- The squared `L²`-norm as a Lebesgue integral. -/
theorem norm_sq_eq_lintegral (μ : Measure X) (g : Lp K 2 μ) :
    ‖g‖ ^ 2 = (∫⁻ x, ‖(g : X → K) x‖ₑ ^ (2:ℕ) ∂μ).toReal := by
  have hJ : ∫⁻ x, ‖(g : X → K) x‖ₑ ^ (2:ℕ) ∂μ
      = ∫⁻ x, ‖(g : X → K) x‖ₑ ^ ((2:ENNReal).toReal) ∂μ := by
    refine lintegral_congr fun x => ?_
    rw [show ((2:ENNReal).toReal) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]
  have hfin : eLpNorm (g : X → K) 2 μ ≠ ⊤ := (Lp.memLp g).2.ne
  rw [Lp.norm_def, eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)] at *
  set J := ∫⁻ x, ‖(g : X → K) x‖ₑ ^ ((2:ENNReal).toReal) ∂μ with hJdef
  have hJtop : J ≠ ⊤ := by
    intro h
    apply hfin
    rw [h]
    simp [ENNReal.top_rpow_of_pos]
  rw [hJ, ← ENNReal.toReal_rpow,
    ← Real.rpow_natCast (J.toReal ^ (1 / (2:ENNReal).toReal)) 2,
    ← Real.rpow_mul ENNReal.toReal_nonneg]
  norm_num

omit [InnerProductSpace ℂ K] in
/-- The `ℒ²`-integral of a square-integrable function is finite. -/
theorem lintegral_enorm_sq_ne_top (μ : Measure X) (g : Lp K 2 μ) :
    ∫⁻ x, ‖(g : X → K) x‖ₑ ^ (2:ℕ) ∂μ ≠ ⊤ := by
  have hJ : ∫⁻ x, ‖(g : X → K) x‖ₑ ^ (2:ℕ) ∂μ
      = ∫⁻ x, ‖(g : X → K) x‖ₑ ^ ((2:ENNReal).toReal) ∂μ := by
    refine lintegral_congr fun x => ?_
    rw [show ((2:ENNReal).toReal) = ((2:ℕ):ℝ) by norm_num, ENNReal.rpow_natCast]
  have hfin : eLpNorm (g : X → K) 2 μ ≠ ⊤ := (Lp.memLp g).2.ne
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)] at hfin
  rw [hJ]
  intro h
  apply hfin
  rw [h]
  simp [ENNReal.top_rpow_of_pos]

omit [InnerProductSpace ℂ K] in
/-- The `ℒ²`-integral of `P(A) f` is the integral of `f` over `A`. -/
theorem lintegral_enorm_proj (μ : Measure X) {A : Set X} (hA : MeasurableSet A)
    (f : Lp K 2 μ) :
    ∫⁻ x, ‖(proj μ hA f : X → K) x‖ₑ ^ (2:ℕ) ∂μ
      = ∫⁻ x in A, ‖(f : X → K) x‖ₑ ^ (2:ℕ) ∂μ := by
  rw [← lintegral_indicator hA]
  refine lintegral_congr_ae ?_
  filter_upwards [proj_coeFn μ hA f] with x hx
  rw [hx]
  by_cases h : x ∈ A <;> simp [h]

omit [InnerProductSpace ℂ K] in
/-- `‖P(A) f‖² = ∫_A ‖f‖²`. -/
theorem norm_sq_proj (μ : Measure X) {A : Set X} (hA : MeasurableSet A) (f : Lp K 2 μ) :
    ‖proj μ hA f‖ ^ 2 = (∫⁻ x in A, ‖(f : X → K) x‖ₑ ^ (2:ℕ) ∂μ).toReal := by
  rw [norm_sq_eq_lintegral, lintegral_enorm_proj]

omit [InnerProductSpace ℂ K] in
/-- The projections attached to equal sets agree. -/
theorem proj_congr (μ : Measure X) {A B : Set X} (hA : MeasurableSet A) (hB : MeasurableSet B)
    (hAB : A = B) (f : Lp K 2 μ) : proj μ hA f = proj μ hB f := by
  refine Lp.ext ?_
  filter_upwards [proj_coeFn μ hA f, proj_coeFn μ hB f] with x e1 e2
  rw [e1, e2, hAB]

/-! ## Orthogonality -/

/-- Disjoint sets give orthogonal projections. -/
theorem proj_orthogonal (μ : Measure X) {A B : Set X} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hd : Disjoint A B) (f : Lp K 2 μ) :
    ⟪proj μ hA f, proj μ hB f⟫_ℂ = 0 := by
  rw [proj_symm μ hA f (proj μ hB f), proj_inter μ hA hB f,
    proj_congr μ (hA.inter hB) (MeasurableSet.empty (α := X))
      (Set.disjoint_iff_inter_eq_empty.mp hd) f,
    proj_empty μ f, inner_zero_right]

/-- The inner product of `P(A) f` with `P(B) f` for `A ⊆ B` is `‖P(A) f‖²`. -/
theorem inner_proj_proj_of_subset (μ : Measure X) {A B : Set X} (hA : MeasurableSet A)
    (hB : MeasurableSet B) (hAB : A ⊆ B) (f : Lp K 2 μ) :
    ⟪proj μ hA f, proj μ hB f⟫_ℂ = ((‖proj μ hA f‖ ^ 2 : ℝ) : ℂ) := by
  have h1 : ⟪proj μ hB (proj μ hA f), f⟫_ℂ = ⟪proj μ hA f, proj μ hB f⟫_ℂ :=
    proj_symm μ hB (proj μ hA f) f
  have h2 : proj μ hB (proj μ hA f) = proj μ hA f := by
    rw [proj_inter μ hB hA f]
    exact proj_congr μ (hB.inter hA) hA (Set.inter_eq_self_of_subset_right hAB) f
  rw [h2] at h1
  have h3 : ⟪proj μ hA f, f⟫_ℂ = ⟪proj μ hA f, proj μ hA f⟫_ℂ := by
    have := proj_symm μ hA (proj μ hA f) f
    rw [proj_idem μ hA f] at this
    exact this.symm ▸ rfl
  rw [← h1, h3, inner_self_eq_norm_sq_to_K]
  norm_num

/-! ## Countable additivity -/

/-- **Countable additivity of the projection-valued measure of the induced system.**  For a
countable family of pairwise disjoint measurable subsets of the base, the projections of a
vector onto them are unconditionally summable, with sum the projection onto the union. -/
theorem proj_hasSum_iUnion [CompleteSpace K] (μ : Measure X) {E : ℕ → Set X}
    (hE : ∀ n, MeasurableSet (E n)) (hd : Pairwise (Function.onFun Disjoint E))
    (f : Lp K 2 μ) :
    HasSum (fun n => proj μ (hE n) f) (proj μ (MeasurableSet.iUnion hE) f) := by
  classical
  have hU : MeasurableSet (⋃ n, E n) := MeasurableSet.iUnion hE
  set φ : X → ENNReal := fun x => ‖(f : X → K) x‖ₑ ^ (2:ℕ) with hφdef
  have hsum_I : ∫⁻ x in (⋃ n, E n), φ x ∂μ = ∑' n, ∫⁻ x in E n, φ x ∂μ :=
    lintegral_iUnion hE hd φ
  have hIU_top : ∫⁻ x in (⋃ n, E n), φ x ∂μ ≠ ⊤ :=
    ne_top_of_le_ne_top (lintegral_enorm_sq_ne_top μ f) (setLIntegral_le_lintegral _ _)
  have htsum_top : (∑' n, ∫⁻ x in E n, φ x ∂μ) ≠ ⊤ := by rw [← hsum_I]; exact hIU_top
  have hI_top : ∀ n, (∫⁻ x in E n, φ x ∂μ) ≠ ⊤ := fun n =>
    ne_top_of_le_ne_top htsum_top (ENNReal.le_tsum n)
  -- the series of squared norms
  have hsumreal : HasSum (fun n => ‖proj μ (hE n) f‖ ^ 2) (‖proj μ hU f‖ ^ 2) := by
    have hnorms : ∀ n, ‖proj μ (hE n) f‖ ^ 2 = (∫⁻ x in E n, φ x ∂μ).toReal := fun n =>
      norm_sq_proj μ (hE n) f
    have hUnorm : ‖proj μ hU f‖ ^ 2 = (∫⁻ x in (⋃ n, E n), φ x ∂μ).toReal :=
      norm_sq_proj μ hU f
    have hsummable : Summable fun n => (∫⁻ x in E n, φ x ∂μ).toReal :=
      ENNReal.summable_toReal htsum_top
    have hval : (∫⁻ x in (⋃ n, E n), φ x ∂μ).toReal
        = ∑' n, (∫⁻ x in E n, φ x ∂μ).toReal := by
      rw [hsum_I, ENNReal.tsum_toReal_eq hI_top]
    simp only [hnorms, hUnorm, hval]
    exact hsummable.hasSum
  -- orthogonality
  have horth : ∀ i j, i ≠ j → ⟪proj μ (hE i) f, proj μ (hE j) f⟫_ℂ = 0 := fun i j hij =>
    proj_orthogonal μ (hE i) (hE j) (hd hij) f
  -- the sum exists
  have hsummable_v : Summable fun n => proj μ (hE n) f :=
    BookProof.ChapterOrthogonalSums.summable_of_orthogonal_of_summable_norm_sq horth
      hsumreal.summable
  have hS : HasSum (fun n => proj μ (hE n) f) (∑' n, proj μ (hE n) f) := hsummable_v.hasSum
  set S := ∑' n, proj μ (hE n) f with hSdef
  -- Parseval identifies the norm
  have hnormS : ‖S‖ ^ 2 = ‖proj μ hU f‖ ^ 2 :=
    (BookProof.ChapterOrthogonalSums.hasSum_norm_sq_of_hasSum hS horth).unique hsumreal
  -- and the inner product with `P(⋃ Eₙ) f`
  have hinner1 : HasSum (fun n => ⟪proj μ (hE n) f, proj μ hU f⟫_ℂ) (⟪S, proj μ hU f⟫_ℂ) :=
    hS.mapL ((innerSL ℂ (E := Lp K 2 μ)).flip (proj μ hU f))
  have hinner2 : HasSum (fun n => ((‖proj μ (hE n) f‖ ^ 2 : ℝ) : ℂ))
      (((‖proj μ hU f‖ ^ 2 : ℝ) : ℂ)) := hsumreal.mapL Complex.ofRealCLM
  have hterms : ∀ n, ⟪proj μ (hE n) f, proj μ hU f⟫_ℂ = ((‖proj μ (hE n) f‖ ^ 2 : ℝ) : ℂ) :=
    fun n => inner_proj_proj_of_subset μ (hE n) hU (Set.subset_iUnion E n) f
  have hinnerS : ⟪S, proj μ hU f⟫_ℂ = ((‖proj μ hU f‖ ^ 2 : ℝ) : ℂ) := by
    refine HasSum.unique ?_ hinner2
    simpa only [hterms] using hinner1
  -- conclude
  have hzero : ‖S - proj μ hU f‖ ^ 2 = 0 := by
    rw [norm_sub_sq (𝕜 := ℂ), hnormS, hinnerS]
    simp only [Complex.ofReal_pow, RCLike.re_to_complex]
    rw [← Complex.ofReal_pow, Complex.ofReal_re]
    ring
  have : S = proj μ hU f := by
    have := pow_eq_zero_iff (n := 2) (by norm_num) |>.mp hzero
    exact sub_eq_zero.mp (norm_eq_zero.mp this)
  rw [← this]
  exact hS

end BookProof.ChapterMackeyQuasiInvariant
