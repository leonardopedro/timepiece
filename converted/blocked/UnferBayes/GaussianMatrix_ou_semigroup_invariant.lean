/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 504ceb37-906c-42ce-b475-d350aa6b3102
* original name       : `GaussianMatrix.ou_semigroup_invariant`
* title               : Invariance of $N(0,1)$ under the Ornstein–Uhlenbeck semigroup: $\int P_th\,d\gamma=\int h\,d\gamma$
* statement author    : tc
* solution author     : tc (submission 02938562-e07c-4b07-8bc2-690ca8b5dc34,
                        accepted 2026-10-09T08:22:48.235978+00:00)
* source              : Standard fact: if $X,Y$ are independent $N(0,1)$ random variables and $a^2+b^2=1$ then $aX+bY\sim N(0,1)$; hence $\gamma$ is invariant for the Ornstein–Uhlenbeck semigroup. See D. Bakry, I. Gentil, M. Ledoux, Analysis and Geometry of Markov Diffusion Operators (Springer, 2014), §2.7.1 (cited from memory).
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/unfer-bayes/GaussianMatrix.ou_semigroup_invariant.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/GaussianMatrix_ou_semigroup_invariant.diff`.
-/
import Definitions.Def_GaussianMatrix_basic

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

/-- The image of `γ ⊗ γ` under `(x, y) ↦ a x + b y` is `γ` when `a² + b² = 1`. -/
lemma map_lin_comb_gaussian (a b : ℝ) (hab : a ^ 2 + b ^ 2 = 1) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map (fun p : ℝ × ℝ => a * p.1 + b * p.2)
      = gaussianReal 0 1 := by
  have h1 : (fun p : ℝ × ℝ => a * p.1 + b * p.2)
      = (fun p : ℝ × ℝ => p.1 + p.2) ∘ Prod.map (fun x => a * x) (fun y => b * y) := by
    ext p; simp
  rw [h1, ← Measure.map_map (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop),
    gaussianReal_map_const_mul, gaussianReal_map_const_mul]
  rw [← Measure.conv, gaussianReal_conv_gaussianReal]
  congr 1
  · simp
  · apply NNReal.eq; simp [hab]

lemma integral_lin_comb_gaussian (h : ℝ → ℝ) (hh : Integrable h (gaussianReal 0 1)) (a b : ℝ)
    (hab : a ^ 2 + b ^ 2 = 1) :
    ∫ x, (∫ y, h (a * x + b * y) ∂(gaussianReal 0 1)) ∂(gaussianReal 0 1)
      = ∫ x, h x ∂(gaussianReal 0 1) := by
  have hmap : ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
      (fun p : ℝ × ℝ => a * p.1 + b * p.2) = gaussianReal 0 1 := by
    exact map_lin_comb_gaussian a b hab
  have hF : AEMeasurable (fun p : ℝ × ℝ => a * p.1 + b * p.2)
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) := by fun_prop
  have hh' : Integrable h (((gaussianReal 0 1).prod (gaussianReal 0 1)).map
      (fun p : ℝ × ℝ => a * p.1 + b * p.2)) := by rw [hmap]; exact hh
  have hcomp : Integrable (fun p : ℝ × ℝ => h (a * p.1 + b * p.2))
      ((gaussianReal 0 1).prod (gaussianReal 0 1)) :=
    (integrable_map_measure hh'.aestronglyMeasurable hF).1 hh'
  rw [← integral_prod (fun p : ℝ × ℝ => h (a * p.1 + b * p.2)) hcomp]
  rw [← integral_map hF (by rw [hmap]; exact hh.aestronglyMeasurable), hmap]

end GaussianMatrix

open GaussianMatrix

theorem _root_.Prove2me.Solution.GaussianMatrix_ou_semigroup_invariant (h : ℝ → ℝ) (hh : Integrable h (gaussianReal 0 1)) (t : ℝ)
    (ht : 0 ≤ t) :
    ∫ x, (∫ y, h (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-(2 * t))) * y)
        ∂(gaussianReal 0 1)) ∂(gaussianReal 0 1)
      = ∫ x, h x ∂(gaussianReal 0 1) := by
  apply integral_lin_comb_gaussian h hh
  have h1 : Real.exp (-(2 * t)) ≤ 1 := Real.exp_le_one_iff.2 (by linarith)
  rw [Real.sq_sqrt (by linarith), sq, ← Real.exp_add]
  ring_nf

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem ou_semigroup_invariant (h : ℝ → ℝ) (hh : Integrable h (gaussianReal 0 1)) (t : ℝ)
    (ht : 0 ≤ t) :
    ∫ x, (∫ y, h (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-(2 * t))) * y)
        ∂(gaussianReal 0 1)) ∂(gaussianReal 0 1)
      = ∫ x, h x ∂(gaussianReal 0 1) :=
  _root_.Prove2me.Solution.GaussianMatrix_ou_semigroup_invariant h hh t ht

end GaussianMatrix

end Prove2meStatement
