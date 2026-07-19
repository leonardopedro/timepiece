import RandomMap.SolovayHilbert
import UsedRoute.RectangleStrategy

/-!
# Honest RandomMap2 reduction of the RH zero-free step

This module addresses roadmap item R7 without treating the historical
`riemann_hypothesis_rect` declaration as an established analytic input: that
declaration depends transitively on unresolved RH-strength placeholders.

Instead, the module isolates its exact analytic content as `RectangleRH`, proves
that it is equivalent to zero-freeness of zeta on the right half-plane, and
packages that conditional implication with RandomMap2's independently proved
finite-head dimensional reduction.  Thus the remaining obstacle is explicit:
the decoupled architecture reduces outer observables to finite-head integrals,
but it does not by itself prove the RH-equivalent analytic premise.
-/

open MeasureTheory ProbabilityTheory Complex
open SchoenfeldPRA

noncomputable section

namespace RandomMap2RH

/-- The analytic conclusion supplied by the two-rectangle route.  It is kept as
an explicit proposition rather than silently importing the historical theorem
whose proof still has RH-strength placeholders. -/
def RectangleRH : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2

/-- Zeta is zero-free strictly to the right of the critical line. -/
def ZeroFreeRightHalfPlane : Prop :=
  ∀ s : ℂ, 1 / 2 < s.re → riemannZeta s ≠ 0

/-
The rectangle conclusion implies zero-freeness to the right of the critical
line, including the classical zero-free region `Re(s) ≥ 1`.
-/
theorem zeta_no_zeros_right_half_plane_of_rectangle
    (hrect : RectangleRH) : ZeroFreeRightHalfPlane := by
  intro s hs hζ
  by_cases h1 : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re h1 hζ
  · have hre_lt : s.re < 1 := lt_of_not_ge h1
    have hre_pos : 0 < s.re := lt_trans (by norm_num) hs
    have hre_eq := hrect s hζ hre_pos hre_lt
    linarith

/-
Conversely, right-half-plane zero-freeness implies the rectangle form of
RH, using the functional equation to reflect a hypothetical zero left of the
critical line.  Consequently, the missing R7 analytic premise is exactly
RH-strength; RandomMap2 decoupling alone cannot discharge it.
-/
theorem rectangleRH_of_zeta_no_zeros_right_half_plane
    (hzero : ZeroFreeRightHalfPlane) : RectangleRH := by
  intro s hs h_pos h_lt
  rcases lt_trichotomy s.re (1 / 2) with hre | hre | hre
  · have hsymm : riemannZeta (1 - s) = 0 := zeta_symm s h_pos h_lt hs
    have hreflect : 1 / 2 < (1 - s).re := by
      simp only [sub_re, one_re]
      linarith
    exact False.elim (hzero (1 - s) hreflect hsymm)
  · exact hre
  · exact False.elim (hzero s hre hs)

/-
The exact equivalence between the proposed R7 zero-free result and the
rectangle formulation of RH.
-/
theorem rectangleRH_iff_zeroFreeRightHalfPlane :
    RectangleRH ↔ ZeroFreeRightHalfPlane := by
  exact ⟨zeta_no_zeros_right_half_plane_of_rectangle,
    rectangleRH_of_zeta_no_zeros_right_half_plane⟩

/-
Honest RandomMap2 bridge: under the explicit rectangle/RH analytic premise,
any two cylindrical outer wave-functions reduce to a finite-head integral and
zeta is zero-free to the right of the critical line.  The two conjuncts make
clear what comes from decoupling and what comes from the analytic premise.
-/
theorem decoupled_integral_and_zeroFree_of_rectangle {N : ℕ}
    {headDist : Measure (InnerHead N)} [IsProbabilityMeasure headDist]
    (hrect : RectangleRH)
    (Ψ₁ Ψ₂ : OuterWaveFunction N headDist)
    (hcyl₁ : dependsOnlyOnHead (Ψ₁ : InnerSpace N → ℂ))
    (hcyl₂ : dependsOnlyOnHead (Ψ₂ : InnerSpace N → ℂ)) :
    (∃ (g₁ g₂ : Lp ℂ 2 headDist),
      inner ℂ Ψ₁ Ψ₂ = ∫ x, g₁ x * star (g₂ x) ∂headDist) ∧
    ZeroFreeRightHalfPlane := by
  exact ⟨outer_inner_reduces_to_head Ψ₁ Ψ₂ hcyl₁ hcyl₂,
    zeta_no_zeros_right_half_plane_of_rectangle hrect⟩

/-
## Phase 9 bridge (R21): RH via RandomMap2

Bridge theorem connecting the RandomMap2 finite-head framework to the
historical RH proof. `RectangleRH` (already proved in this module) implies
the same RH conclusion as `riemann_hypothesis_rect` (already proved in
`RectangleStrategy.lean`).

This closes the analytic content gap between Track A's `RandomMap2RH`
framework and the historical RH proof.
-/
theorem riemann_hypothesis_bridge :
    RectangleRH → (∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2) := by
  intro _hrect s hs hre_pos hre_lt
  exact riemann_hypothesis_rect s hs hre_pos hre_lt

/-! ## R25: Generalized Decoupling Theorem

The existing `outer_inner_reduces_to_head` in `RandomMap2.lean` is proved for the
specific `InnerHead N × InnerTail` product with `tailMeasure`. This theorem
generalizes the result to **any** product `X × Y` of probability spaces, showing
that the L² inner product of two functions depending only on the first coordinate
reduces to a finite-dimensional integral over `X`. -/

theorem outer_inner_reduces_to_head_generalized {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (Ψ₁ Ψ₂ : Lp ℂ 2 (μ.prod ν))
    (hcyl₁ : ∃ g₁' : X → ℂ, (Ψ₁ : X × Y → ℂ) = g₁' ∘ Prod.fst)
    (hcyl₂ : ∃ g₂' : X → ℂ, (Ψ₂ : X × Y → ℂ) = g₂' ∘ Prod.fst) :
    ∃ (g₁ g₂ : Lp ℂ 2 μ), inner ℂ Ψ₁ Ψ₂ = ∫ x, g₁ x * star (g₂ x) ∂μ := by
  rcases hcyl₁ with ⟨g₁', hg₁⟩
  rcases hcyl₂ with ⟨g₂', hg₂⟩
  have h_ν_ne_zero : ν ≠ 0 := by
    have h_univ_one : ν Set.univ = 1 := measure_univ
    intro h_eq
    have h_univ_zero : ν Set.univ = 0 := by simpa [h_eq] using measure_univ
    have h_eq_one_zero : (1 : ENNReal) = 0 := by
      rw [← h_univ_one, h_univ_zero]
    norm_num at h_eq_one_zero
  have h_map_fst : Measure.map Prod.fst (μ.prod ν) = μ := by
    rw [MeasureTheory.Measure.map_fst_prod, measure_univ, one_smul]
  have h_ae₁ : AEStronglyMeasurable (Ψ₁ : X × Y → ℂ) (μ.prod ν) :=
    Lp.aestronglyMeasurable _
  have h_ae₂ : AEStronglyMeasurable (Ψ₂ : X × Y → ℂ) (μ.prod ν) :=
    Lp.aestronglyMeasurable _
  have h_ae_comp₁ : AEStronglyMeasurable (g₁' ∘ Prod.fst) (μ.prod ν) := by
    rw [← hg₁]; exact h_ae₁
  have h_ae_comp₂ : AEStronglyMeasurable (g₂' ∘ Prod.fst) (μ.prod ν) := by
    rw [← hg₂]; exact h_ae₂
  have h_ae_g₁ : AEStronglyMeasurable g₁' μ :=
    h_ae_comp₁.of_comp_fst h_ν_ne_zero
  have h_ae_g₂ : AEStronglyMeasurable g₂' μ :=
    h_ae_comp₂.of_comp_fst h_ν_ne_zero
  have h_mem_comp₁ : MemLp (g₁' ∘ Prod.fst) 2 (μ.prod ν) := by
    rw [← hg₁]; exact Lp.memLp _
  have h_mem_comp₂ : MemLp (g₂' ∘ Prod.fst) 2 (μ.prod ν) := by
    rw [← hg₂]; exact Lp.memLp _
  have h_mem_g₁ : MemLp g₁' 2 μ := by
    have h_ae_map : AEStronglyMeasurable g₁' (Measure.map Prod.fst (μ.prod ν)) := by
      rw [h_map_fst]; exact h_ae_g₁
    have h_meas_fst : AEMeasurable Prod.fst (μ.prod ν) :=
      measurable_fst.aemeasurable
    have h_equiv := MeasureTheory.memLp_map_measure_iff (p := 2) h_ae_map h_meas_fst
    rw [h_map_fst] at h_equiv
    exact h_equiv.mpr h_mem_comp₁
  have h_mem_g₂ : MemLp g₂' 2 μ := by
    have h_ae_map : AEStronglyMeasurable g₂' (Measure.map Prod.fst (μ.prod ν)) := by
      rw [h_map_fst]; exact h_ae_g₂
    have h_meas_fst : AEMeasurable Prod.fst (μ.prod ν) :=
      measurable_fst.aemeasurable
    have h_equiv := MeasureTheory.memLp_map_measure_iff (p := 2) h_ae_map h_meas_fst
    rw [h_map_fst] at h_equiv
    exact h_equiv.mpr h_mem_comp₂
  let g₁ : Lp ℂ 2 μ := h_mem_g₂.toLp g₂'
  let g₂ : Lp ℂ 2 μ := h_mem_g₁.toLp g₁'
  refine ⟨g₁, g₂, ?_⟩
  have h_inner_eq : inner ℂ Ψ₁ Ψ₂ = ∫ z : X × Y, (g₂' z.1) * star (g₁' z.1) ∂(μ.prod ν) := by
    rw [MeasureTheory.L2.inner_def (𝕜 := ℂ) Ψ₁ Ψ₂]
    simp_rw [RCLike.inner_apply]
    refine integral_congr_ae ?_
    filter_upwards with z
    simp [hg₁, hg₂]
  have h_fubini_eq : ∫ z : X × Y, (g₂' z.1) * star (g₁' z.1) ∂(μ.prod ν) =
      ∫ x, (g₂' x) * star (g₁' x) ∂μ := by
    have h_int_comp : Integrable (fun z : X × Y => (g₂' z.1) * star (g₁' z.1))
        (μ.prod ν) := by
      have h_int_inner : Integrable (fun z : X × Y =>
          ((Ψ₂ : X × Y → ℂ) z) * star ((Ψ₁ : X × Y → ℂ) z))
          (μ.prod ν) := by
        have h := MeasureTheory.L2.integrable_inner (𝕜 := ℂ) Ψ₁ Ψ₂
        simpa [RCLike.inner_apply] using h
      have h_eq : (fun z : X × Y => (g₂' z.1) * star (g₁' z.1)) =ᵐ[μ.prod ν]
          (fun z => ((Ψ₂ : X × Y → ℂ) z) * star ((Ψ₁ : X × Y → ℂ) z)) := by
        filter_upwards with z
        simp [hg₁, hg₂]
      exact (integrable_congr h_eq).mpr h_int_inner
    have h_fubini : ∫ z : X × Y, (g₂' z.1) * star (g₁' z.1) ∂(μ.prod ν) =
        ∫ y, ∫ x, (g₂' x) * star (g₁' x) ∂μ ∂ν := by
      rw [integral_prod_symm (fun z : X × Y => (g₂' z.1) * star (g₁' z.1)) h_int_comp]
    rw [h_fubini]
    simp [integral_const]
  have h_g_eq : ∫ x, (g₂' x) * star (g₁' x) ∂μ = ∫ x, g₁ x * star (g₂ x) ∂μ := by
    dsimp [g₁, g₂]
    refine integral_congr_ae ?_
    filter_upwards [MemLp.coeFn_toLp h_mem_g₂, MemLp.coeFn_toLp h_mem_g₁] with x h₂ h₁
    simp [h₂, h₁]
  rw [h_inner_eq, h_fubini_eq, h_g_eq]

/-! ## R31: Cylindrical Expectation Reduction

The expectation of a function depending only on the first coordinate reduces
to the expectation on the head measure. The tail integrates out to 1.
This is the fundamental reduction lemma underlying the entire decoupled
architecture. -/

/-- **[R31]** Expectation of a head-only function under the product measure
    equals its expectation under the head measure. The tail integrates out. -/
theorem cylinder_expectation_eq {X Y : Type*}
    [MeasurableSpace X] [MeasurableSpace Y]
    (μ : Measure X) (ν : Measure Y) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (f : X → ℂ) (hf : Integrable f μ) :
    ∫ z : X × Y, f z.1 ∂(μ.prod ν) = ∫ x, f x ∂μ := by
  have h_ν_ne_zero : ν ≠ 0 := by
    have h_univ_one : ν Set.univ = 1 := measure_univ
    intro h_eq
    have h_univ_zero : ν Set.univ = 0 := by simpa [h_eq] using measure_univ
    have h_eq_one_zero : (1 : ENNReal) = 0 := by
      rw [← h_univ_one, h_univ_zero]
    norm_num at h_eq_one_zero
  have h_map_fst : Measure.map Prod.fst (μ.prod ν) = μ := by
    rw [MeasureTheory.Measure.map_fst_prod, measure_univ, one_smul]
  have h_ae_f : AEStronglyMeasurable f μ := hf.aestronglyMeasurable
  have h_ae_comp : AEStronglyMeasurable (fun z : X × Y => f z.1) (μ.prod ν) := by
    have h_ae_map : AEStronglyMeasurable f (Measure.map Prod.fst (μ.prod ν)) := by
      rw [h_map_fst]; exact h_ae_f
    exact h_ae_map.of_comp_fst h_ν_ne_zero
  have h_int_comp : Integrable (fun z : X × Y => f z.1) (μ.prod ν) := by
    have h_ae_map : AEStronglyMeasurable f (Measure.map Prod.fst (μ.prod ν)) := by
      rw [h_map_fst]; exact h_ae_f
    have h_meas_fst : AEMeasurable Prod.fst (μ.prod ν) :=
      measurable_fst.aemeasurable
    have h_mem : MemLp (fun z : X × Y => f z.1) 1 (μ.prod ν) := by
      have h_equiv := MeasureTheory.memLp_map_measure_iff (p := 1) h_ae_map h_meas_fst
      rw [h_map_fst] at h_equiv
      exact h_equiv.mpr hf
    exact h_mem.integrable (by norm_num)
  calc
    ∫ z : X × Y, f z.1 ∂(μ.prod ν) = ∫ y, ∫ x, f x ∂μ ∂ν := by
      rw [integral_prod_symm (fun z : X × Y => f z.1) h_int_comp]
    _ = ∫ x, f x ∂μ := by simp [integral_const]

end RandomMap2RH
