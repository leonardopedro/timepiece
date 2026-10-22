module

public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv
public import Mathlib.Analysis.Calculus.MeanValue
public import Mathlib.Analysis.Calculus.FDeriv.Pi
public import Mathlib.Analysis.Calculus.Deriv.Inv
public import Mathlib.Analysis.Calculus.Deriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Mul
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# Milestone 3: Bounded cosine attention and softmax

We formalize nGPT attention logits over normalized query/key vectors: the cosine similarity of
two unit vectors lies in `[-1, 1]`, so the scaled logits lie in `[-τ, τ]`. We then define the
softmax over a finite index type, prove a strictly positive lower bound for its probabilities
under bounded logits, and prove that softmax is globally Lipschitz (with constant `2` for the
sup norm on `d → ℝ`), via an explicit bound `‖∂ softmax_i‖ ≤ 2` on the derivative of each
coordinate.

Note: the plan's `softmax_lipschitz` took an unused argument `tau`; global Lipschitz continuity
on all of `d → ℝ` (which in particular covers the cube `[-τ, τ]^d`) is proved, so the argument is
omitted.
-/

@[expose] public section

open scoped NNReal

namespace BayesianTransformer

section Cosine

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Cosine similarity between two (unit) vectors. -/
def cosineSimilarity (q k : E) : ℝ := inner ℝ q k

/-- Cauchy–Schwarz: the cosine similarity of unit vectors lies in `[-1, 1]`. -/
theorem cosineSimilarity_bounds {q k : E} (hq : ‖q‖ = 1) (hk : ‖k‖ = 1) :
    -1 ≤ cosineSimilarity q k ∧ cosineSimilarity q k ≤ 1 := by
  have h := abs_real_inner_le_norm q k
  rw [hq, hk, one_mul] at h
  exact abs_le.mp h

/-- The scaled attention logit is bounded within `[-tau, tau]`. -/
theorem scaled_logit_bounds {q k : E} (hq : ‖q‖ = 1) (hk : ‖k‖ = 1) {tau : ℝ} (htau : 0 ≤ tau) :
    -tau ≤ tau * cosineSimilarity q k ∧ tau * cosineSimilarity q k ≤ tau := by
  obtain ⟨h1, h2⟩ := cosineSimilarity_bounds hq hk
  constructor <;> nlinarith

end Cosine

section Softmax

variable {d : Type*} [Fintype d]

/-- Softmax vector over a finite index type. -/
noncomputable def softmax (z : d → ℝ) : d → ℝ :=
  let exps := fun i => Real.exp (z i)
  let sum_exp := Finset.univ.sum exps
  fun i => exps i / sum_exp

/-- The softmax normalizer `∑ⱼ exp zⱼ`. -/
noncomputable def expSum (z : d → ℝ) : ℝ := ∑ j, Real.exp (z j)

theorem softmax_apply (z : d → ℝ) (i : d) : softmax z i = Real.exp (z i) * (expSum z)⁻¹ := by
  simp [softmax, expSum, div_eq_mul_inv]

theorem expSum_pos [Nonempty d] (z : d → ℝ) : 0 < expSum z :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) Finset.univ_nonempty

theorem exp_le_expSum (z : d → ℝ) (i : d) : Real.exp (z i) ≤ expSum z :=
  Finset.single_le_sum (f := fun j => Real.exp (z j)) (fun _ _ => (Real.exp_pos _).le)
    (Finset.mem_univ i)

/-- Strictly positive lower bound for softmax probabilities under bounded logits. -/
theorem softmax_min_prob_bound {z : d → ℝ} {tau : ℝ} (hz : ∀ i, |z i| ≤ tau) (i : d) :
    (Real.exp (-tau) / ((Fintype.card d : ℝ) * Real.exp tau)) ≤ softmax z i := by
  haveI : Nonempty d := ⟨i⟩
  rw [softmax_apply, ← div_eq_mul_inv]
  have hnum : Real.exp (-tau) ≤ Real.exp (z i) :=
    Real.exp_le_exp.mpr (by linarith [(abs_le.mp (hz i)).1])
  have hden : expSum z ≤ (Fintype.card d : ℝ) * Real.exp tau := by
    have := Finset.sum_le_card_nsmul Finset.univ (fun j => Real.exp (z j)) (Real.exp tau)
      (fun j _ => Real.exp_le_exp.mpr (abs_le.mp (hz j)).2)
    simpa [expSum, nsmul_eq_mul] using this
  exact div_le_div₀ (Real.exp_pos _).le hnum (expSum_pos z) hden

/-- The softmax probabilities are strictly positive. -/
theorem softmax_pos (z : d → ℝ) (i : d) : 0 < softmax z i := by
  haveI : Nonempty d := ⟨i⟩
  rw [softmax_apply]
  exact mul_pos (Real.exp_pos _) (inv_pos.mpr (expSum_pos z))

/-- The softmax probabilities sum to one. -/
theorem softmax_sum_eq_one [Nonempty d] (z : d → ℝ) : ∑ i, softmax z i = 1 := by
  simp_rw [softmax_apply, ← Finset.sum_mul]
  exact mul_inv_cancel₀ (expSum_pos z).ne'

theorem expSum_hasFDerivAt (z : d → ℝ) :
    HasFDerivAt expSum
      (∑ j, Real.exp (z j) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : d => ℝ) j) z := by
  have := HasFDerivAt.sum (u := Finset.univ) (x := z)
    (A := fun j (z : d → ℝ) => Real.exp (z j))
    (fun j _ => (hasFDerivAt_apply j z).exp)
  convert this using 1
  ext y; simp [expSum]

/-- Explicit derivative of a softmax coordinate `z ↦ exp(zᵢ) / ∑ⱼ exp(zⱼ)`. -/
theorem softmax_coord_hasFDerivAt [Nonempty d] (z : d → ℝ) (i : d) :
    HasFDerivAt (fun z => softmax z i)
      (Real.exp (z i) • ((-((expSum z) ^ 2)⁻¹) •
          (∑ j, Real.exp (z j) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : d => ℝ) j))
        + (expSum z)⁻¹ •
          (Real.exp (z i) • ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : d => ℝ) i)) z := by
  have h1 := (hasFDerivAt_apply (𝕜 := ℝ) i z).exp
  have h2 := (hasDerivAt_inv (expSum_pos z).ne').comp_hasFDerivAt z (expSum_hasFDerivAt z)
  convert h1.mul h2 using 1

/-- Jacobian bound: each softmax coordinate has derivative of operator norm at most `2`
(with respect to the sup norm on `d → ℝ`). -/
theorem softmax_coord_fderiv_norm_le [Nonempty d] (z : d → ℝ) (i : d) :
    ‖fderiv ℝ (fun z => softmax z i) z‖ ≤ 2 := by
  rw [(softmax_coord_hasFDerivAt z i).fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun h => ?_
  have hS := expSum_pos z
  have hei := exp_le_expSum z i
  have hepos := Real.exp_pos (z i)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.proj_apply, smul_eq_mul]
  have hsum : |∑ j, Real.exp (z j) * h j| ≤ expSum z * ‖h‖ := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [expSum, Finset.sum_mul]
    refine Finset.sum_le_sum fun j _ => ?_
    rw [abs_mul, abs_of_pos (Real.exp_pos _)]
    exact mul_le_mul_of_nonneg_left (norm_le_pi_norm h j) (Real.exp_pos _).le
  have hhi : |h i| ≤ ‖h‖ := norm_le_pi_norm h i
  have hratio : Real.exp (z i) * (expSum z)⁻¹ ≤ 1 := by
    rw [mul_inv_le_iff₀ hS]; linarith
  rw [Real.norm_eq_abs]
  calc _ ≤ |Real.exp (z i) * (-(expSum z ^ 2)⁻¹ * ∑ j, Real.exp (z j) * h j)|
          + |(expSum z)⁻¹ * (Real.exp (z i) * h i)| := abs_add_le _ _
    _ = Real.exp (z i) * (expSum z ^ 2)⁻¹ * |∑ j, Real.exp (z j) * h j|
          + Real.exp (z i) * (expSum z)⁻¹ * |h i| := by
        rw [abs_mul, abs_mul, abs_neg, abs_mul, abs_mul, abs_of_pos hepos,
          abs_of_pos (by positivity : (0:ℝ) < (expSum z ^ 2)⁻¹), abs_of_pos (inv_pos.mpr hS)]
        ring
    _ ≤ Real.exp (z i) * (expSum z ^ 2)⁻¹ * (expSum z * ‖h‖)
          + Real.exp (z i) * (expSum z)⁻¹ * ‖h‖ := by gcongr
    _ = 2 * (Real.exp (z i) * (expSum z)⁻¹) * ‖h‖ := by field_simp; ring
    _ ≤ 2 * 1 * ‖h‖ := by gcongr
    _ = 2 * ‖h‖ := by ring

/-- Explicit global Lipschitz bound: softmax is `2`-Lipschitz for the sup norm on `d → ℝ`. -/
theorem softmax_lipschitzWith_two : LipschitzWith 2 (fun z : d → ℝ => softmax z) := by
  cases isEmpty_or_nonempty d with
  | inl _ =>
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [Subsingleton.elim (softmax x) (softmax y), dist_self]
    positivity
  | inr _ =>
    refine LipschitzWith.of_dist_le_mul fun x y => ?_
    refine (dist_pi_le_iff (by positivity)).mpr fun i => ?_
    have hL : LipschitzWith 2 (fun z : d → ℝ => softmax z i) :=
      lipschitzWith_of_nnnorm_fderiv_le
        (fun z => (softmax_coord_hasFDerivAt z i).differentiableAt)
        (fun z => by
          rw [← NNReal.coe_le_coe, coe_nnnorm]
          exact softmax_coord_fderiv_norm_le z i)
    exact hL.dist_le_mul x y

/-- Lipschitz continuity of the softmax operator (globally, hence on every cube `[-τ, τ]^d`). -/
theorem softmax_lipschitz :
    ∃ L : ℝ≥0, LipschitzWith L (fun z : d → ℝ => softmax z) :=
  ⟨2, softmax_lipschitzWith_two⟩

end Softmax

end BayesianTransformer
