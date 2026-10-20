/-
prove2.me platform library module `Definitions.Def_OAIE3v2B160`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_OAIE3v2B160.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_ErdosReciprocal
import Definitions.Def_OAIE3v2B100
import Definitions.Def_OAIE3v2B142
import Definitions.Def_OAIE3v2B147
import Definitions.Def_OAIE3v2B148

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Dynamics.PreparedFiniteStageNativeBudget
namespace OAI

section

namespace Erdos3.VectorPolynomial
open scoped BigOperators

theorem exists_preparedFiniteForwardSchedule_budget (depth A : ℕ)
    (stageCountConstant : ℕ → ℕ) :
    ∃ C : ℕ, 2 ≤ C ∧ ∀ x : ℝ, 0 ≤ x → ∀ n : ℕ, n ≤ depth →
      preparedFiniteForwardParameter A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardWork A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardCap A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardCount A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) ∧
      preparedFiniteForwardBranch A stageCountConstant n x ∈ Set.Icc 0 ((x + C) ^ C) := by
  let Q : ℕ → Polynomial ℕ := fun n =>
    preparedFiniteForwardParameterPolynomial A stageCountConstant n +
      preparedFiniteForwardWorkPolynomial A stageCountConstant n +
      preparedFiniteForwardCapPolynomial A stageCountConstant n +
      preparedFiniteForwardCountPolynomial A stageCountConstant n +
      preparedFiniteForwardBranchPolynomial A stageCountConstant n
  obtain ⟨C, hC, hbudget⟩ :=
    exists_natPolynomial_eval_budget (∑ n ∈ Finset.range (depth + 1), Q n)
  refine ⟨C, hC, ?_⟩
  intro x hx n hn
  have hentry : (Q n).eval₂ (Nat.castRingHom ℝ) x ≤ (x + C) ^ C := by
    apply le_trans _ (hbudget x hx)
    rw [Polynomial.eval₂_finsetSum]
    exact Finset.single_le_sum (fun i _ => natPolynomial_eval_nonneg (Q i) hx)
      (Finset.mem_range.mpr (by omega))
  have hp := preparedFiniteForwardParameter_nonneg A stageCountConstant n hx
  have hw := preparedFiniteForwardWork_nonneg A stageCountConstant n hx
  have hcap := preparedFiniteForwardCap_nonneg A stageCountConstant n hx
  have hcount := preparedFiniteForwardCount_nonneg A stageCountConstant n hx
  have hbranch := preparedFiniteForwardBranch_nonneg A stageCountConstant n hx
  simp only [Q, Polynomial.eval₂_add] at hentry
  change preparedFiniteForwardParameter A stageCountConstant n x +
      preparedFiniteForwardWork A stageCountConstant n x +
      preparedFiniteForwardCap A stageCountConstant n x +
      preparedFiniteForwardCount A stageCountConstant n x +
      preparedFiniteForwardBranch A stageCountConstant n x ≤ (x + C) ^ C at hentry
  exact ⟨⟨hp, by linarith⟩, ⟨hw, by linarith⟩, ⟨hcap, by linarith⟩,
    ⟨hcount, by linarith⟩, ⟨hbranch, by linarith⟩⟩

end Erdos3.VectorPolynomial

end

end OAI
end

section
-- module Solutions.OAIErdos3.Combinatorics.Progressions.Sampling.PhysicalGridCorrelation
namespace OAI

section

namespace Erdos3

open scoped BigOperators

noncomputable def normalizedBoxPartitions {I : Type*} (N : I → ℕ) (H : I → ℝ) (ρ : ℝ)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ)) :
    ∀ i, FiniteProgressionPartition (N i) :=
  comparableBoxPartitions N (fun i => ⌊ρ * H i / 2⌋₊)
    (fun i => (normalizedGridLength_bounds (N i) (H i) ρ (hlarge i) (hwhole i)).1)
    (fun i => (normalizedGridLength_bounds (N i) (H i) ρ (hlarge i) (hwhole i)).2.1)

theorem normalizedBoxPartitions_positive {I : Type*} (N : I → ℕ) (H : I → ℝ) (ρ : ℝ)
    (hlarge : ∀ i, 4 ≤ ρ * H i) (hwhole : ∀ i, ρ * H i ≤ 2 * (N i : ℝ))
    (i : I) (c : (normalizedBoxPartitions N H ρ hlarge hwhole i).Label) :
    0 < (normalizedBoxPartitions N H ρ hlarge hwhole i).length c := by
  exact (normalizedGridLength_bounds (N i) (H i) ρ (hlarge i) (hwhole i)).1.trans_le
    (comparableBoxPartitions_length N _ _ _ i c).1

end Erdos3

end

end OAI
end
