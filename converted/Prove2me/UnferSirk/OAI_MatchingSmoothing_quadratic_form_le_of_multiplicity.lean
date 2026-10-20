/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : e3c175a4-21ff-4603-acbe-f0d6150219d0
* original name       : `OAI.MatchingSmoothing.quadratic_form_le_of_multiplicity`
* title               : Large eigenvalue multiplicities and a small trace of the square bound a symmetric operator from above
* statement author    : Shuze Chen
* solution author     : Shuze Chen (submission 49741ed7-d2a3-4527-a4e2-2af6effe5230,
                        accepted 2026-10-18T06:09:39.732983+00:00)
* source              : https://github.com/openai/math/blob/1581d4cbdd69a0faf34b2089614fe2a814316a6a/lean/OAI/Combinatorics/MatchingPSD/SpectralMultiplicity.lean#L55-L72
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/unfer-sirk/OAI.MatchingSmoothing.quadratic_form_le_of_multiplicity.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/OAI_MatchingSmoothing_quadratic_form_le_of_multiplicity.diff`.
-/
-- Generated from openai/math@1581d4c lean/OAI/Combinatorics/MatchingPSD/SpectralMultiplicity.lean:L55-L72
-- (upload_full_project.md Phase 4): solution for node OAI.MatchingSmoothing.quadratic_form_le_of_multiplicity. The node keeps its source
-- declaration (inside its namespace, so name resolution is unchanged) next to the proof-only
-- helpers it needs; the top-level `theorem solution` has its type (`type_of%`) and is proved by it.
import Mathlib
import Definitions.Def_MatchingPSD
import Definitions.Def_OAI_Combinatorics_MatchingPSD_EdgeProducts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_Pairings
import Definitions.Def_OAI_Combinatorics_MatchingPSD_RepresentationDimension
import Definitions.Def_OAI_Combinatorics_MatchingPSD_ColoringCounts
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TransitionMatrices
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TensorBounds
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TypeProbabilities
import Definitions.Def_OAI_Combinatorics_MatchingPSD_TableMoments
import Definitions.Def_OAI_Combinatorics_MatchingPSD_IncidenceKernels

-- ---- from OAI.Combinatorics.MatchingPSD.SpectralMultiplicity ----
namespace OAI

universe u_1

namespace MatchingSmoothing

open scoped RealInnerProductSpace

variable {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

lemma trace_square_eq_sum_eigenvalue_sq (B : Module.End ℝ E) (hB : B.IsSymmetric) :
    LinearMap.trace ℝ E (B * B) =
      ∑ i, (hB.eigenvalues (n := Module.finrank ℝ E) rfl i) ^ 2 := by
  rw [LinearMap.trace_eq_sum_inner _ (hB.eigenvectorBasis rfl)]
  apply Finset.sum_congr rfl
  intro i _
  simp only [Module.End.mul_apply, hB.apply_eigenvectorBasis rfl, map_smul,
    real_inner_smul_right, OrthonormalBasis.inner_eq_one, mul_one]
  simp [pow_two]

lemma eigenspace_dim_mul_sq_le_trace_square (B : Module.End ℝ E) (hB : B.IsSymmetric)
    (c : ℝ) :
    (Module.finrank ℝ (Module.End.eigenspace B c) : ℝ) * c ^ 2 ≤
      LinearMap.trace ℝ E (B * B) := by
  classical
  let ev :=  hB.eigenvalues (n := Module.finrank ℝ E) rfl
  let s := Finset.univ.filter fun i => ev i = c
  have hcard : s.card = Module.finrank ℝ (Module.End.eigenspace B c) := by
    -- conversion: the pinned `card_filter_eigenvalues_eq` assumes `HasEigenvalue B c`
    by_cases hc : Module.End.HasEigenvalue B c
    · simpa using hB.card_filter_eigenvalues_eq rfl hc
    · have h1 : Module.End.eigenspace B c = ⊥ := by
        simpa [Module.End.HasEigenvalue, Module.End.HasUnifEigenvalue] using hc
      rw [h1, finrank_bot, Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro i _ hi
      exact hc (hi ▸ by simpa using hB.hasEigenvalue_eigenvalues rfl i)
  have he : ∑ i ∈ s, ev i ^ 2 = (s.card : ℝ) * c ^ 2 := by
    calc
      ∑ i ∈ s, ev i ^ 2 = ∑ _i ∈ s, c ^ 2 := by
        apply Finset.sum_congr rfl
        intro i hi
        rw [(Finset.mem_filter.mp hi).2]
      _ = _ := by simp
  rw [trace_square_eq_sum_eigenvalue_sq B hB, ← hcard, ← he]
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_univ s)
    (fun _ _ _ => sq_nonneg _)

lemma quadratic_form_le_of_eigenvalues_le (B : Module.End ℝ E) (hB : B.IsSymmetric)
    (a : ℝ) (ha : ∀ i, hB.eigenvalues (n := Module.finrank ℝ E) rfl i ≤ a)
    (x : E) : ⟪x, B x⟫ ≤ a * ‖x‖ ^ 2 := by
  let b := hB.eigenvectorBasis (n := Module.finrank ℝ E) rfl
  rw [← b.sum_inner_mul_inner x (B x), ← b.sum_sq_inner_right x, Finset.mul_sum]
  apply Finset.sum_le_sum
  intro i _
  have he : B (b i) = (hB.eigenvalues rfl i) • b i := hB.apply_eigenvectorBasis rfl i
  rw [← hB (b i) x, he, real_inner_smul_left, real_inner_comm x (b i)]
  nlinarith [sq_nonneg (inner ℝ (b i) x), ha i]

lemma quadratic_form_le_of_multiplicity (B : Module.End ℝ E) (hB : B.IsSymmetric)
    (m H a : ℝ) (hm : 0 < m) (ha : 0 ≤ a)
    (hdim : ∀ c : ℝ, c ≠ 0 → Module.End.HasEigenvalue B c →
      m ≤ Module.finrank ℝ (Module.End.eigenspace B c))
    (htrace : LinearMap.trace ℝ E (B * B) ≤ H)
    (hHa : H ≤ m * a ^ 2) (x : E) : ⟪x, B x⟫ ≤ a * ‖x‖ ^ 2 := by
  apply quadratic_form_le_of_eigenvalues_le B hB a _ x
  intro i
  let c := hB.eigenvalues (n := Module.finrank ℝ E) rfl i
  by_cases hc : c = 0
  · simpa only [← show c = hB.eigenvalues rfl i from rfl, hc] using ha
  · have hd := hdim c hc (hB.hasEigenvalue_eigenvalues rfl i)
    have he := eigenspace_dim_mul_sq_le_trace_square B hB c
    have hsq : m * c ^ 2 ≤ m * a ^ 2 :=
      (mul_le_mul_of_nonneg_right hd (sq_nonneg c)).trans (he.trans (htrace.trans hHa))
    have hle : c ^ 2 ≤ a ^ 2 := (mul_le_mul_iff_right₀ hm).mp hsq
    change c ≤ a
    nlinarith

end MatchingSmoothing

end OAI

-- ---- platform node ----
open OAI OAI.MatchingSmoothing
open scoped RealInnerProductSpace


theorem _root_.Prove2me.Solution.OAI_MatchingSmoothing_quadratic_form_le_of_multiplicity : type_of% @_root_.OAI.MatchingSmoothing.quadratic_form_le_of_multiplicity := @_root_.OAI.MatchingSmoothing.quadratic_form_le_of_multiplicity

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), checked against the solution above.  The solution declares the platform theorem `OAI.MatchingSmoothing.quadratic_form_le_of_multiplicity` itself, so the statement is restated as an `example`. -/

section Prove2meStatement

open OAI OAI.MatchingSmoothing
open scoped RealInnerProductSpace
variable {E : Type u_1} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [FiniteDimensional ℝ E]

example (B : Module.End ℝ E) (hB : B.IsSymmetric)
    (m H a : ℝ) (hm : 0 < m) (ha : 0 ≤ a)
    (hdim : ∀ c : ℝ, c ≠ 0 → Module.End.HasEigenvalue B c →
      m ≤ Module.finrank ℝ (Module.End.eigenspace B c))
    (htrace : LinearMap.trace ℝ E (B * B) ≤ H)
    (hHa : H ≤ m * a ^ 2) (x : E) : ⟪x, B x⟫ ≤ a * ‖x‖ ^ 2 := by
  first
  | exact _root_.Prove2me.Solution.OAI_MatchingSmoothing_quadratic_form_le_of_multiplicity B hB m H a hm ha hdim htrace hHa x
  | (apply _root_.Prove2me.Solution.OAI_MatchingSmoothing_quadratic_form_le_of_multiplicity <;> assumption)


end Prove2meStatement
