/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : cbcb40a9-f91e-4f68-be16-596f87acd709
* original name       : `GaussianMatrix.ou_semigroup_commutation`
* title               : Commutation of the Ornstein–Uhlenbeck semigroup with differentiation: $(P_tf)'=e^{-t}P_t(f')$
* statement author    : tc
* solution author     : tc (submission 938279dc-3a55-488c-97b8-76fe669f383a,
                        accepted 2026-10-09T08:21:34.238728+00:00)
* source              : Standard fact (differentiation under the integral sign in Mehler's formula); D. Bakry, I. Gentil, M. Ledoux, Analysis and Geometry of Markov Diffusion Operators (Springer, 2014), §2.7.1, commutation $\nabla P_t=e^{-t}P_t\nabla$ for the Ornstein–Uhlenbeck semigroup (cited from memory).
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/unfer-bayes/GaussianMatrix.ou_semigroup_commutation.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/GaussianMatrix_ou_semigroup_commutation.diff`.
-/
import Definitions.Def_GaussianMatrix_basic
import Prove2me.Shim.Misc  -- conversion shim (platform Mathlib API)

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

lemma integrable_abs_id_gaussian : Integrable (fun y : ℝ => |y|) (gaussianReal 0 1) := by
  have : Integrable (fun y : ℝ => y) (gaussianReal 0 1) :=
    memLp_one_iff_integrable.1 (memLp_id_gaussianReal 1)
  exact this.abs

/-- A function with bounded derivative has linear growth. -/
lemma abs_le_of_deriv_bound (f : ℝ → ℝ) (hf : Differentiable ℝ f) (C : ℝ)
    (hdf : ∀ x, |deriv f x| ≤ C) (z : ℝ) : |f z| ≤ |f 0| + C * |z| := by
  have := Convex.norm_image_sub_le_of_norm_deriv_le (f := f) (s := Set.univ) (C := C)
    (fun x _ => hf x) (fun x _ => by simpa using hdf x) convex_univ (Set.mem_univ 0)
    (Set.mem_univ z)
  simp only [Real.norm_eq_abs, sub_zero] at this
  have h2 := abs_sub_abs_le_abs_sub (f z) (f 0)
  linarith

lemma integrable_comp_affine_of_deriv_bound (f : ℝ → ℝ) (hf : Differentiable ℝ f) (C : ℝ)
    (hdf : ∀ x, |deriv f x| ≤ C) (c d : ℝ) :
    Integrable (fun y => f (c + d * y)) (gaussianReal 0 1) := by
  have hC : 0 ≤ C := le_trans (abs_nonneg _) (hdf 0)
  refine Integrable.mono' ((integrable_const (|f 0| + C * |c|)).add
    (integrable_abs_id_gaussian.const_mul (C * |d|))) ?_ ?_
  · exact (hf.continuous.comp (by fun_prop)).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun y => ?_)
    rw [Real.norm_eq_abs]
    refine (abs_le_of_deriv_bound f hf C hdf _).trans ?_
    have : |c + d * y| ≤ |c| + |d| * |y| := by
      rw [← abs_mul]; exact abs_add_le _ _
    simp only [Pi.add_apply]
    nlinarith

end GaussianMatrix

open GaussianMatrix

theorem _root_.Prove2me.Solution.GaussianMatrix_ou_semigroup_commutation (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (C : ℝ)
    (hdf : ∀ x, |deriv f x| ≤ C) (t x : ℝ) :
    HasDerivAt
      (fun z => ∫ y, f (Real.exp (-t) * z + Real.sqrt (1 - Real.exp (-(2 * t))) * y)
        ∂(gaussianReal 0 1))
      (Real.exp (-t) * ∫ y, deriv f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-(2 * t))) * y)
        ∂(gaussianReal 0 1)) x := by
  set a := Real.exp (-t)
  set b := Real.sqrt (1 - Real.exp (-(2 * t)))
  have hfd : Differentiable ℝ f := hf.differentiable one_ne_zero
  have hfc : Continuous (deriv f) := hf.continuous_deriv le_rfl
  rw [← integral_const_mul]
  refine (hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := gaussianReal 0 1)
    (F := fun z y => f (a * z + b * y)) (F' := fun z y => a * deriv f (a * z + b * y))
    (x₀ := x) (bound := fun _ => |a| * C) Filter.univ_mem ?_ ?_ ?_ ?_ ?_ ?_).2
  · exact Filter.Eventually.of_forall (fun z =>
      (hfd.continuous.comp (by fun_prop)).aestronglyMeasurable)
  · exact integrable_comp_affine_of_deriv_bound f hfd C hdf (a * x) b
  · exact ((hfc.comp (by fun_prop)).const_mul a).aestronglyMeasurable
  · refine Filter.Eventually.of_forall (fun y z _ => ?_)
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul_of_nonneg_left (hdf _) (abs_nonneg _)
  · exact integrable_const _
  · refine Filter.Eventually.of_forall (fun y z _ => ?_)
    have h1 : HasDerivAt (fun z => a * z + b * y) a z := by
      simpa using ((hasDerivAt_id z).const_mul a).add_const (b * y)
    have := (hfd (a * z + b * y)).hasDerivAt.comp z h1
    rw [mul_comm (deriv f _) a] at this
    exact this

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open MeasureTheory ProbabilityTheory
open scoped Matrix

namespace GaussianMatrix

theorem ou_semigroup_commutation (f : ℝ → ℝ) (hf : ContDiff ℝ 1 f) (C : ℝ)
    (hdf : ∀ x, |deriv f x| ≤ C) (t x : ℝ) :
    HasDerivAt
      (fun z => ∫ y, f (Real.exp (-t) * z + Real.sqrt (1 - Real.exp (-(2 * t))) * y)
        ∂(gaussianReal 0 1))
      (Real.exp (-t) * ∫ y, deriv f (Real.exp (-t) * x + Real.sqrt (1 - Real.exp (-(2 * t))) * y)
        ∂(gaussianReal 0 1)) x := by
  first
  | exact _root_.Prove2me.Solution.GaussianMatrix_ou_semigroup_commutation f hf C hdf t x
  | (apply _root_.Prove2me.Solution.GaussianMatrix_ou_semigroup_commutation <;> assumption)

end GaussianMatrix


end Prove2meStatement
