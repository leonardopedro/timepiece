import Mathlib

/-!
# Chapter "Wave-function collapse versus Euler's formula", §"Euler's formula for
the probability clock" — the most general probability-preserving linear map on a
2-state phase space

This file formalizes the self-contained mathematical claim of `book.tex`
(§"Euler's formula for the probability clock", line ~3310):

> *"the most general linear transformation of a probability distribution that
> preserves the space of probability distributions is
> `M(a,b) = [[cos²a, cos²b],[sin²a, sin²b]]` … because if we apply `M` to a
> deterministic distribution `(1,0)` or `(0,1)` we must obtain probability
> distributions … the matrix `M` such that `M·½(1,1) = (1,0)` is necessarily
> singular and so it is not suitable to represent a symmetry group."*

The book contrasts this with the rotations `exp(Ja)` that act invertibly on the
wave-function: on the *probability* simplex the only linear symmetries are the
(column-)stochastic matrices, and the specific one collapsing the uniform
distribution to a vertex is singular — motivating the wave-function
parametrization, where the corresponding transformation is an invertible
rotation.

We work over `Matrix (Fin 2) (Fin 2) ℝ`.

* `IsProbVec v` — `v` is a 2-state probability vector (`v i ≥ 0`, `v 0 + v 1 = 1`).
* `PreservesProb M` — `M` maps every probability vector to a probability vector.
* `Mmat a b` — the book's `M(a,b)`.

Results:
* `Mmat_preservesProb` — every `M(a,b)` preserves probability distributions.
* `preservesProb_iff_exists_angles` — **headline**: a linear map preserves the
  space of probability distributions *iff* it is `M(a,b)` for some angles `a,b`
  (the book's "most general" claim).
* `preservesProb_iff_columnStochastic` — the same characterization in terms of
  column-stochasticity (each column is a probability vector).
* `uniform_to_vertex_singular` — **headline**: any probability-preserving `M`
  with `M·½(1,1) = (1,0)` is singular (`M.det = 0`), so it cannot represent a
  symmetry group.
-/

open scoped Matrix BigOperators

namespace BookProof.ChapterEulerStochastic

/-- A 2-state probability vector: non-negative entries summing to `1`. -/
def IsProbVec (v : Fin 2 → ℝ) : Prop := (∀ i, 0 ≤ v i) ∧ v 0 + v 1 = 1

/-- A linear map (matrix) *preserves the space of probability distributions* if
it sends every probability vector to a probability vector. -/
def PreservesProb (M : Matrix (Fin 2) (Fin 2) ℝ) : Prop :=
    ∀ v : Fin 2 → ℝ, IsProbVec v → IsProbVec (M *ᵥ v)

/-- The book's most general probability-preserving matrix
`M(a,b) = [[cos²a, cos²b],[sin²a, sin²b]]`. -/
noncomputable def Mmat (a b : ℝ) : Matrix (Fin 2) (Fin 2) ℝ :=
    !![Real.cos a ^ 2, Real.cos b ^ 2; Real.sin a ^ 2, Real.sin b ^ 2]

/-
Every probability `p ∈ [0,1]` is realized as `cos² a` for some angle `a`
(with the complementary entry `sin² a = 1 - p`).
-/
theorem exists_cos_sq {p : ℝ} (hp0 : 0 ≤ p) (hp1 : p ≤ 1) :
    ∃ a : ℝ, Real.cos a ^ 2 = p := by
      exact ⟨ Real.arccos ( Real.sqrt p ), by rw [ Real.cos_arccos ] <;> nlinarith [ Real.mul_self_sqrt hp0 ] ⟩

/-
The two standard basis / deterministic distributions are probability
vectors.
-/
theorem isProbVec_e0 : IsProbVec ![1, 0] := by
  exact ⟨ fun i => by fin_cases i <;> norm_num, by norm_num ⟩

theorem isProbVec_e1 : IsProbVec ![0, 1] := by
  exact ⟨ fun i => by fin_cases i <;> norm_num, by norm_num ⟩

/-
**Converse direction (constructive):** every `M(a,b)` preserves the space of
probability distributions.
-/
theorem Mmat_preservesProb (a b : ℝ) : PreservesProb (Mmat a b) := by
  intro v hv; constructor <;> norm_num [ Mmat ] at *;
  · exact ⟨ add_nonneg ( mul_nonneg ( sq_nonneg _ ) ( hv.1 0 ) ) ( mul_nonneg ( sq_nonneg _ ) ( hv.1 1 ) ), add_nonneg ( mul_nonneg ( sq_nonneg _ ) ( hv.1 0 ) ) ( mul_nonneg ( sq_nonneg _ ) ( hv.1 1 ) ) ⟩;
  · rw [ Real.sin_sq, Real.sin_sq ] ; ring!; nlinarith! [ hv.1 0, hv.1 1, hv.2 ] ;

/-
A matrix preserves probability distributions iff it is column-stochastic
(each column is itself a probability vector).
-/
theorem preservesProb_iff_columnStochastic (M : Matrix (Fin 2) (Fin 2) ℝ) :
    PreservesProb M ↔
      (IsProbVec (fun i => M i 0) ∧ IsProbVec (fun i => M i 1)) := by
        refine ⟨ ?_, fun h => ?_ ⟩;
        · intro hM
          constructor;
          · have := hM ( fun i => if i = 0 then 1 else 0 ) ; simp_all +decide [ IsProbVec, Matrix.mulVec ] ;
          · have := hM ( fun i => if i = 0 then 0 else 1 ) ?_ <;> simp_all +decide [ IsProbVec, Matrix.mulVec ];
        · intro v hv; rw [ IsProbVec ] at *; simp_all +decide [ Matrix.mulVec, Fin.sum_univ_two ] ;
          exact ⟨ ⟨ by nlinarith [ h.2.1 0, h.2.1 1 ], by nlinarith [ h.2.1 0, h.2.1 1 ] ⟩, by nlinarith [ h.2.2 ] ⟩

/-
**Headline.** A linear transformation preserves the space of probability
distributions **iff** it equals `M(a,b)` for some real angles `a, b`. This is the
book's claim that `M(a,b)` is the most general probability-preserving linear map
on a 2-state phase space.
-/
theorem preservesProb_iff_exists_angles (M : Matrix (Fin 2) (Fin 2) ℝ) :
    PreservesProb M ↔ ∃ a b : ℝ, M = Mmat a b := by
      constructor <;> intro h;
      · -- By `preservesProb_iff_columnStochastic`, both columns are probability vectors: `0 ≤ M 0 0`, `0 ≤ M 1 0`, `M 0 0 + M 1 0 = 1`, and likewise `0 ≤ M 0 1`, `0 ≤ M 1 1`, `M 0 1 + M 1 1 = 1`.
        obtain ⟨h00, h01, h10, h11, hsum⟩ : 0 ≤ M 0 0 ∧ 0 ≤ M 0 1 ∧ 0 ≤ M 1 0 ∧ 0 ≤ M 1 1 ∧ M 0 0 + M 1 0 = 1 ∧ M 0 1 + M 1 1 = 1 := by
          have := preservesProb_iff_columnStochastic M |>.1 h; simp_all +decide [ Fin.forall_fin_two, IsProbVec ] ;
        -- From these, `M 0 0 ∈ [0,1]` and `M 0 1 ∈ [0,1]`. By `exists_cos_sq` get `a` with `Real.cos a ^ 2 = M 0 0` and `b` with `Real.cos b ^ 2 = M 0 1`.
        obtain ⟨a, ha⟩ : ∃ a : ℝ, Real.cos a ^ 2 = M 0 0 := exists_cos_sq h00 (by linarith)
        obtain ⟨b, hb⟩ : ∃ b : ℝ, Real.cos b ^ 2 = M 0 1 := exists_cos_sq h01 (by linarith);
        use a, b; ext i j; fin_cases i <;> fin_cases j <;> simp +decide [ *, Mmat ] ; linarith [ Real.sin_sq_add_cos_sq a, Real.sin_sq_add_cos_sq b ] ;
        linarith [ Real.sin_sq_add_cos_sq b ];
      · exact h.elim fun a ha => ha.elim fun b hb => hb ▸ Mmat_preservesProb a b

/-
**Headline.** The specific probability-preserving matrix that collapses the
uniform distribution `½(1,1)` to the vertex `(1,0)` is singular (`det = 0`), so
it is not suitable to represent a symmetry group.
-/
theorem uniform_to_vertex_singular (M : Matrix (Fin 2) (Fin 2) ℝ)
    (hM : PreservesProb M) (hcollapse : M *ᵥ ![1/2, 1/2] = ![1, 0]) :
    M.det = 0 := by
      rw [ Matrix.det_fin_two ];
      simp_all +decide [ funext_iff, Fin.forall_fin_two, Matrix.mulVec ];
      have := hM ![1, 0] ; have := hM ![0, 1] ; norm_num [ IsProbVec ] at *;
      norm_num [ Matrix.vecHead, Matrix.vecTail, Matrix.mulVec ] at * ; nlinarith!

end BookProof.ChapterEulerStochastic