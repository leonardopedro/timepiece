import BookProof.Qym.ChapterYangMillsGaussRotationFlow
import BookProof.Toolbox.ChapterStoneBridge

/-!
# The Gauss generator: the derivative of the rotation flow

`BookProof/Qym/ChapterYangMillsGaussRotationFlow.lean` builds the residual colour rotation
`E(t) = e^{-tM}` as a flow of `L²(ℝ⁹⁹)` and leaves one analytic input as a hypothesis: that
`t ↦ E(t) f` is differentiable with derivative the Gauss constraint `𝒢_d`.  This module
proves that identity.

The proof has three layers.

* **Pointwise.**  For a fixed `x`, the scalar function `s ↦ p(E(s)ᵀx)` is differentiable with
  derivative `(∇p)(E(t)ᵀx) · (E(t)ᵀ M x)`, by the chain rule for `MvPolynomial.eval` along a
  curve (`hasDerivAt_eval_along`).  Since `M` is the matrix of the Gauss vector field
  (`ymGaussVec_eq_sum_gaussMat`), that scalar equals `𝒢_d (p ∘ E(t)ᵀ)` evaluated at `x`
  (`eval_sum_pderiv_gaussFlow`).
* **Domination.**  The difference quotient is the average of the derivative, and the
  derivative is bounded by `K ‖x‖ (1 + ‖x‖)^N` uniformly in the parameter: `E(s)` is
  orthogonal, so it preserves `‖x‖`, and a polynomial of total degree `N` grows at most like
  `(1 + ‖x‖)^N` (`exists_norm_eval_le`).
* **`L²`.**  The squared `L²` norm of a Gauss polynomial is bounded by the Gaussian integral
  of `‖q‖²` (`norm_pgLp_sq_le`); dominated convergence then turns the pointwise limit into
  convergence of the integrals, hence differentiability in `L²`.
-/

namespace BookProof.Qym.GaussGenerator

open Matrix MvPolynomial MeasureTheory Filter
open scoped Norms.Operator Topology
open BookProof.Qym.GaussCasimir BookProof.BrstYmCommute BookProof.BookBrstYangMills
open BookProof.YangMillsHermite BookProof.HermiteProductCore BookProof.Qym.GaussSkew
open BookProof.Qym.GaussClosure BookProof.Qym.GaussSkewAdjoint
open BookProof.Qym.GaussSkewAdjointDomain BookProof.Qym.GaussRotationFlow
open BookProof.ChapterStoneResolvent BookProof.StoneBridge
open BookProof.QuadraticRotation

noncomputable section

variable {d : ℕ}

/-! ## The chain rule for the evaluation of a polynomial along a curve -/

/-- **Evaluating a polynomial along a differentiable curve.**  If `y : ℝ → ℝⁿ` is
differentiable at `t` with derivative `y'`, then `s ↦ p(y s)` is differentiable there with
derivative `Σ_m y'_m (∂_m p)(y t)`.  Proved by induction on `p`: the constants are constant,
sums add, and a product with `X i` uses the product rule together with
`∂_m(p * X_i) = (∂_m p) * X_i + δ_{m i} p`. -/
theorem hasDerivAt_eval_along {y : ℝ → (Fin d → ℝ)} {y' : Fin d → ℝ} {t : ℝ}
    (hy : HasDerivAt y y' t) (p : MvPolynomial (Fin d) ℂ) :
    HasDerivAt (fun s : ℝ => MvPolynomial.eval (fun i => ((y s i : ℝ) : ℂ)) p)
      (MvPolynomial.eval (fun i => ((y t i : ℝ) : ℂ))
        (∑ m, MvPolynomial.C (((y' m : ℝ) : ℂ)) * pderiv m p)) t := by
  induction p using MvPolynomial.induction_on with
  | C a =>
      have hzero : (∑ m : Fin d, MvPolynomial.C (((y' m : ℝ) : ℂ)) * pderiv m
          (MvPolynomial.C a : MvPolynomial (Fin d) ℂ)) = 0 := by
        simp
      rw [hzero, map_zero]
      simpa using hasDerivAt_const (x := t) (c := a)
  | add p q hp hq =>
      have hsum : (∑ m : Fin d, MvPolynomial.C (((y' m : ℝ) : ℂ)) * pderiv m (p + q))
          = (∑ m : Fin d, MvPolynomial.C (((y' m : ℝ) : ℂ)) * pderiv m p)
            + ∑ m : Fin d, MvPolynomial.C (((y' m : ℝ) : ℂ)) * pderiv m q := by
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [map_add, mul_add]
      rw [hsum, map_add]
      simpa only [map_add] using hp.add hq
  | mul_X p i hp =>
      have hleib : ∀ m : Fin d, pderiv m (p * MvPolynomial.X i)
          = pderiv m p * MvPolynomial.X i + if m = i then p else 0 := by
        intro m
        rw [Derivation.leibniz, pderiv_X]
        by_cases h : m = i <;> simp [h, Pi.single_apply, smul_eq_mul, mul_comm, add_comm]
      have hsum : (∑ m : Fin d, MvPolynomial.C (((y' m : ℝ) : ℂ)) * pderiv m (p * X i))
          = (∑ m : Fin d, MvPolynomial.C (((y' m : ℝ) : ℂ)) * pderiv m p) * X i
            + MvPolynomial.C (((y' i : ℝ) : ℂ)) * p := by
        have hS1 : (∑ m : Fin d, MvPolynomial.C (((y' m : ℝ) : ℂ))
              * (pderiv m p * MvPolynomial.X i))
            = (∑ m : Fin d, MvPolynomial.C (((y' m : ℝ) : ℂ)) * pderiv m p)
              * MvPolynomial.X i := by
          rw [Finset.sum_mul]
          exact Finset.sum_congr rfl fun m _ => by rw [mul_assoc]
        have hS2 : (∑ m : Fin d, MvPolynomial.C (((y' m : ℝ) : ℂ))
              * (if m = i then p else 0)) = MvPolynomial.C (((y' i : ℝ) : ℂ)) * p := by
          rw [Finset.sum_eq_single i]
          · rw [if_pos rfl]
          · intro m _ hm
            rw [if_neg hm, mul_zero]
          · intro h
            exact absurd (Finset.mem_univ _) h
        rw [Finset.sum_congr rfl fun m (_ : m ∈ Finset.univ) => by rw [hleib m]]
        simp only [mul_add]
        rw [Finset.sum_add_distrib, hS1, hS2]
      have hfun : (fun s : ℝ => MvPolynomial.eval (fun i => ((y s i : ℝ) : ℂ))
          (p * MvPolynomial.X i))
          = fun s : ℝ => MvPolynomial.eval (fun i => ((y s i : ℝ) : ℂ)) p
              * (((y s i : ℝ) : ℂ)) := by
        funext s
        simp
      have hyi : HasDerivAt (fun s : ℝ => ((y s i : ℝ) : ℂ)) ((y' i : ℝ) : ℂ) t :=
        (hasDerivAt_pi.1 hy i).ofReal_comp
      rw [hfun, hsum]
      simp only [map_add, map_mul, eval_C, eval_X]
      have hmul := hp.mul hyi
      convert hmul using 1
      ring

/-! ## The transposed flow -/

/-- **The transpose of the flow** is the opposite exponential: `(E t)ᵀ = e^{tM} = E(-t)`. -/
theorem gaussFlow_transpose_eq (G : GaugeAlgebra 8) (dd : Fin 8) (t : ℝ) :
    Matrix.transpose (gaussFlow G dd t) = NormedSpace.exp (t • gaussMat G dd) := by
  rw [gaussFlow, ← Matrix.exp_transpose, Matrix.transpose_smul, gaussMat_transpose]
  simp only [smul_neg, neg_smul, neg_neg]

/-- The generator commutes with the transposed flow. -/
theorem gaussMat_mul_transpose_comm (G : GaugeAlgebra 8) (dd : Fin 8) (t : ℝ) :
    gaussMat G dd * Matrix.transpose (gaussFlow G dd t)
      = Matrix.transpose (gaussFlow G dd t) * gaussMat G dd := by
  rw [gaussFlow_transpose_eq]
  exact (Commute.exp_left ((Commute.refl (gaussMat G dd)).smul_left t)).eq.symm

/-- **The transposed flow is differentiable**, with derivative left multiplication by the
generator. -/
theorem gaussFlow_transpose_hasDerivAt (G : GaugeAlgebra 8) (dd : Fin 8) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Matrix.transpose (gaussFlow G dd s))
      (gaussMat G dd * Matrix.transpose (gaussFlow G dd t)) t := by
  have hfun : (fun s : ℝ => Matrix.transpose (gaussFlow G dd s))
      = fun s : ℝ => NormedSpace.exp (s • gaussMat G dd) := by
    funext s
    exact gaussFlow_transpose_eq G dd s
  rw [hfun, gaussFlow_transpose_eq G dd t]
  exact hasDerivAt_exp_smul_const' (gaussMat G dd) t

/-- The transposed flow applied to a fixed vector is differentiable. -/
theorem gaussFlow_transpose_mulVec_hasDerivAt (G : GaugeAlgebra 8) (dd : Fin 8)
    (x : Fin 99 → ℝ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => Matrix.transpose (gaussFlow G dd s) *ᵥ x)
      (((Matrix.transpose (gaussFlow G dd t) * gaussMat G dd) *ᵥ x)) t := by
  have hfun : (fun s : ℝ => Matrix.transpose (gaussFlow G dd s) *ᵥ x)
      = fun s : ℝ => (fun i => ∑ j : Fin 99,
          Matrix.transpose (gaussFlow G dd s) i j * x j) := by
    funext s
    funext i
    simp [Matrix.mulVec, dotProduct]
  rw [hfun, hasDerivAt_pi]
  intro i
  have hentry : ∀ j : Fin 99, HasDerivAt
      (fun s : ℝ => Matrix.transpose (gaussFlow G dd s) i j * x j)
      ((gaussMat G dd * Matrix.transpose (gaussFlow G dd t)) i j * x j) t := fun j => by
    have h := (hasDerivAt_pi.1 (hasDerivAt_pi.1 (gaussFlow_transpose_hasDerivAt G dd t) i)) j
    exact h.mul_const (x j)
  have hsum := HasDerivAt.fun_sum (u := Finset.univ) fun j _ => hentry j
  convert hsum using 1
  · -- the matrix entry of `Eᵀ M` from `M Eᵀ`
    rw [Matrix.mulVec, dotProduct]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [gaussMat_mul_transpose_comm]

/-- The rotated point `E(t)ᵀ x`. -/
def rotPt (G : GaugeAlgebra 8) (dd : Fin 8) (t : ℝ) (x : Vd 99) : Fin 99 → ℝ :=
  fun i => ((rotIso (gaussFlow_transpose_mul G dd t) x).ofLp) i

/-- The velocity of the rotated point: `E(t)ᵀ M x`. -/
def rotVel (G : GaugeAlgebra 8) (dd : Fin 8) (t : ℝ) (x : Vd 99) : Fin 99 → ℝ :=
  fun m => ((Matrix.transpose (gaussFlow G dd t) * gaussMat G dd) *ᵥ (fun j => x j)) m

theorem rotPt_apply (G : GaugeAlgebra 8) (dd : Fin 8) (t : ℝ) (x : Vd 99) (i : Fin 99) :
    rotPt G dd t x i = (Matrix.transpose (gaussFlow G dd t) *ᵥ fun j => x j) i := by
  simp [rotPt, rotIso_apply, rotLin, Matrix.mulVec, dotProduct]

theorem rotPt_hasDerivAt (G : GaugeAlgebra 8) (dd : Fin 8) (x : Vd 99) (t : ℝ) :
    HasDerivAt (fun s : ℝ => rotPt G dd s x) (rotVel G dd t x) t := by
  have hfun : (fun s : ℝ => rotPt G dd s x)
      = fun s : ℝ => Matrix.transpose (gaussFlow G dd s) *ᵥ (fun j => x j) := by
    funext s
    funext i
    exact rotPt_apply G dd s x i
  rw [hfun]
  exact gaussFlow_transpose_mulVec_hasDerivAt G dd (fun j => x j) t

/-- The Gauss vector field, evaluated at `x`, is the matrix acting on `x`. -/
theorem eval_ymGaussVec (G : GaugeAlgebra 8) (dd : Fin 8) (x : Vd 99) (k : Fin 99) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (ymGaussVec G dd k)
      = ∑ j : Fin 99, ((gaussMat G dd k j : ℝ) : ℂ) * ((x j : ℝ) : ℂ) := by
  rw [ymGaussVec_eq_sum_gaussMat, map_sum]
  exact Finset.sum_congr rfl fun j _ => by simp [smul_eq_C_mul]

/-- The derivative of the rotated polynomial, evaluated at `x`. -/
theorem eval_pderiv_rotPoly (G : GaugeAlgebra 8) (dd : Fin 8)
    (pp : MvPolynomial (Fin 99) ℂ) (x : Vd 99) (t : ℝ) (k : Fin 99) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ))
        (pderiv k (rotPoly (gaussFlow G dd t) pp))
      = ∑ m : Fin 99, ((gaussFlow G dd t k m : ℝ) : ℂ)
          * MvPolynomial.eval (fun i => ((rotPt G dd t x i : ℝ) : ℂ)) (pderiv m pp) := by
  rw [pderiv_rotPoly (O := gaussFlow G dd t) k pp, map_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul]
  congr 1
  · simp
  · rw [eval_rotPoly (gaussFlow_transpose_mul G dd t) (pderiv m pp) x]
    rfl

set_option maxHeartbeats 2000000 in
-- the induction over `MvPolynomial.induction_on` with a product rule exceeds the budget
set_option maxRecDepth 8000 in
/-- **The derivative of the rotation is the Gauss constraint.**  The chain-rule derivative of
`s ↦ p(E(s)ᵀx)` is `(∇p)(E(t)ᵀx) · E(t)ᵀ M x`; commuting `M` past `E(t)ᵀ` and using `v = Mx`
identifies it with `𝒢_d p` evaluated at `x`. -/
theorem eval_sum_pderiv_gaussFlow (G : GaugeAlgebra 8) (dd : Fin 8)
    (p : MvPolynomial (Fin 99) ℂ) (x : Vd 99) (t : ℝ) :
    MvPolynomial.eval (fun i => ((rotPt G dd t x i : ℝ) : ℂ))
        (∑ m : Fin 99, MvPolynomial.C (((rotVel G dd t x m : ℝ) : ℂ)) * pderiv m p)
      = MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ))
          (firstOrder (ymGaussVec G dd) (rotPoly (gaussFlow G dd t) p)) := by
  have hy' : ∀ m : Fin 99, ((rotVel G dd t x m : ℝ) : ℂ)
      = ∑ k : Fin 99, ((gaussFlow G dd t k m : ℝ) : ℂ)
          * (∑ j : Fin 99, ((gaussMat G dd k j : ℝ) : ℂ) * ((x j : ℝ) : ℂ)) := by
    intro m
    rw [rotVel, ← Matrix.mulVec_mulVec]
    simp [Matrix.mulVec, dotProduct, Matrix.transpose_apply, Finset.mul_sum]
  have hL : MvPolynomial.eval (fun i => ((rotPt G dd t x i : ℝ) : ℂ))
        (∑ m : Fin 99, MvPolynomial.C (((rotVel G dd t x m : ℝ) : ℂ)) * pderiv m p)
      = ∑ m : Fin 99, (∑ k : Fin 99, ((gaussFlow G dd t k m : ℝ) : ℂ)
            * (∑ j : Fin 99, ((gaussMat G dd k j : ℝ) : ℂ) * ((x j : ℝ) : ℂ)))
          * MvPolynomial.eval (fun i => ((rotPt G dd t x i : ℝ) : ℂ)) (pderiv m p) := by
    rw [map_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [map_mul, eval_C, hy' m]
  have hR : MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ))
        (firstOrder (ymGaussVec G dd) (rotPoly (gaussFlow G dd t) p))
      = ∑ k : Fin 99, (∑ j : Fin 99, ((gaussMat G dd k j : ℝ) : ℂ) * ((x j : ℝ) : ℂ))
          * (∑ m : Fin 99, ((gaussFlow G dd t k m : ℝ) : ℂ)
            * MvPolynomial.eval (fun i => ((rotPt G dd t x i : ℝ) : ℂ)) (pderiv m p)) := by
    rw [firstOrder_apply, map_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, eval_ymGaussVec, eval_pderiv_rotPoly]
  have hstep : ∀ k : Fin 99,
      (∑ j : Fin 99, ((gaussMat G dd k j : ℝ) : ℂ) * ((x j : ℝ) : ℂ))
        * (∑ m : Fin 99, ((gaussFlow G dd t k m : ℝ) : ℂ)
          * MvPolynomial.eval (fun i => ((rotPt G dd t x i : ℝ) : ℂ)) (pderiv m p))
      = ∑ m : Fin 99, (∑ j : Fin 99, ((gaussMat G dd k j : ℝ) : ℂ) * ((x j : ℝ) : ℂ))
          * (((gaussFlow G dd t k m : ℝ) : ℂ)
            * MvPolynomial.eval (fun i => ((rotPt G dd t x i : ℝ) : ℂ)) (pderiv m p)) := by
    intro k
    rw [Finset.mul_sum]
  rw [hL, hR]
  simp only [hstep]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by ring

set_option maxHeartbeats 2000000 in
-- the sum of `MvPolynomial.eval` terms is a large expression; rewriting needs the budget
set_option maxRecDepth 8000 in
/-- **The pointwise generator identity.**  For each `x`, the scalar function
`s ↦ p(E(s)ᵀx)` has derivative `𝒢_d p` evaluated at `x` at every time `t`. -/
theorem hasDerivAt_eval_gaussFlow (G : GaugeAlgebra 8) (dd : Fin 8)
    (p : MvPolynomial (Fin 99) ℂ) (x : Vd 99) (t : ℝ) :
    HasDerivAt (fun s : ℝ => MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ))
        (rotPoly (gaussFlow G dd s) p))
      (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ))
        (firstOrder (ymGaussVec G dd) (rotPoly (gaussFlow G dd t) p))) t := by
  have hfun : (fun s : ℝ => MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ))
        (rotPoly (gaussFlow G dd s) p))
      = fun s : ℝ => MvPolynomial.eval (fun i => ((rotPt G dd s x i : ℝ) : ℂ)) p := by
    funext s
    rw [eval_rotPoly (gaussFlow_transpose_mul G dd s) p x]
    simp only [rotPt]
  rw [hfun]
  have h := hasDerivAt_eval_along (rotPt_hasDerivAt G dd x t) p
  rw [eval_sum_pderiv_gaussFlow] at h
  exact h

/-! ## Growth and integrability estimates -/

/-- **A polynomial grows at most like `(1 + ‖x‖) ^ totalDegree`.** -/
theorem exists_norm_eval_le (q : MvPolynomial (Fin d) ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y : Vd d,
      ‖MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) q‖
        ≤ C * (1 + ‖y‖) ^ q.totalDegree := by
  classical
  refine ⟨∑ v ∈ q.support, ‖MvPolynomial.coeff v q‖, Finset.sum_nonneg fun v _ =>
    norm_nonneg _, ?_⟩
  intro y
  have hsum : MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) q
      = ∑ v ∈ q.support, MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ))
          (MvPolynomial.monomial v (MvPolynomial.coeff v q)) := by
    conv_lhs => rw [(MvPolynomial.support_sum_monomial_coeff q).symm]
    exact map_sum _ _ _
  have hterm : ∀ v ∈ q.support,
      ‖MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ))
        (MvPolynomial.monomial v (MvPolynomial.coeff v q))‖
      ≤ ‖MvPolynomial.coeff v q‖ * (1 + ‖y‖) ^ q.totalDegree := by
    intro v hv
    rw [MvPolynomial.eval_monomial, norm_mul, Finsupp.prod, norm_prod]
    refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
    have hprod : (∏ b ∈ v.support, ‖((y b : ℝ) : ℂ) ^ v b‖)
        ≤ ‖y‖ ^ (v.sum fun _ e => e) := by
      calc ∏ b ∈ v.support, ‖((y b : ℝ) : ℂ) ^ v b‖
          = ∏ b ∈ v.support, ‖((y b : ℝ) : ℂ)‖ ^ v b := by
            exact Finset.prod_congr rfl fun b _ => norm_pow _ _
        _ ≤ ∏ b ∈ v.support, ‖y‖ ^ v b := by
            refine Finset.prod_le_prod (fun i _ => by positivity) fun b _ => ?_
            refine pow_le_pow_left₀ (norm_nonneg _) ?_ _
            simpa using coord_abs_le_norm y b
        _ = ‖y‖ ^ (v.sum fun _ e => e) := by
            rw [Finset.prod_pow_eq_pow_sum, Finsupp.sum]
    have hN : (v.sum fun _ e => e) ≤ q.totalDegree := MvPolynomial.le_totalDegree hv
    have hn1 : (0 : ℝ) ≤ ‖y‖ := norm_nonneg y
    refine hprod.trans ?_
    refine (pow_le_pow_left₀ hn1 (by linarith) _).trans (pow_le_pow_right₀ (by linarith) hN)
  rw [hsum]
  exact (norm_sum_le _ _).trans ((Finset.sum_le_sum hterm).trans_eq (Finset.sum_mul _ _ _).symm)

/-- **Polynomial growth times the Gaussian weight is integrable.**  The weight is
`e^{-‖x‖²/2} = (e^{-‖x‖²/4})²`, so a polynomial factor of any degree is absorbed by half of the
Gaussian: `(1 + ‖x‖)^k ≤ e^{k‖x‖} = (e^{k‖x‖/2})²`, and the square of the exponential–Gaussian
is integrable. -/
theorem integrable_oneAddNorm_pow_mul_gaussWD (k : ℕ) :
    Integrable (fun x : Vd d => (1 + ‖x‖) ^ k * gaussWD x) := by
  have hL2 : MemLp (fun x : Vd d =>
      (((Real.exp ((k / 2 : ℝ) * ‖x‖) * gaussD x : ℝ)) : ℂ)) 2 (volume : Measure (Vd d)) :=
    memLp_two_exp_norm_mul_gaussD (d := d) (k / 2 : ℝ)
  have hsq : Integrable (fun x : Vd d =>
      ‖(((Real.exp ((k / 2 : ℝ) * ‖x‖) * gaussD x : ℝ)) : ℂ)‖ ^ 2) :=
    (memLp_two_iff_integrable_sq_norm hL2.aestronglyMeasurable).1 hL2
  have hcont : Continuous fun x : Vd d => (1 + ‖x‖) ^ k * gaussWD x := by
    have h1 : Continuous fun x : Vd d => (1 + ‖x‖) ^ k := by fun_prop
    have h2 : Continuous (fun x : Vd d => gaussWD x) := by
      rw [show gaussWD = fun x : Vd d => Real.exp (-‖x‖ ^ 2 / 2) from rfl]
      fun_prop
    exact h1.mul h2
  refine Integrable.mono' hsq hcont.aestronglyMeasurable ?_
  filter_upwards with x
  have hgw : (0 : ℝ) < gaussWD x := by
    rw [show gaussWD x = Real.exp (-‖x‖ ^ 2 / 2) from rfl]
    exact Real.exp_pos _
  have hpos : 0 < Real.exp ((k / 2 : ℝ) * ‖x‖) * gaussD x :=
    mul_pos (Real.exp_pos _) (gaussD_pos x)
  have hnorm : ‖(((Real.exp ((k / 2 : ℝ) * ‖x‖) * gaussD x : ℝ)) : ℂ)‖
      = Real.exp ((k / 2 : ℝ) * ‖x‖) * gaussD x := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
  rw [hnorm, mul_pow, Real.norm_eq_abs,
    abs_of_nonneg (mul_nonneg (by positivity) (le_of_lt hgw))]
  have hbase : 1 + ‖x‖ ≤ Real.exp ‖x‖ := by
    linarith [Real.add_one_le_exp ‖x‖]
  have hpow := pow_le_pow_left₀ (by positivity) hbase k
  have hexp : (Real.exp ‖x‖) ^ k = Real.exp ((k : ℝ) * ‖x‖) := by
    rw [← Real.exp_nat_mul]
  rw [hexp] at hpow
  have hdist : Real.exp ((k : ℝ) * ‖x‖) * gaussWD x
      = Real.exp ((k / 2 : ℝ) * ‖x‖) * gaussD x
        * (Real.exp ((k / 2 : ℝ) * ‖x‖) * gaussD x) := by
    rw [gaussWD_eq_sq]
    have hexp : Real.exp ((k : ℝ) * ‖x‖)
        = Real.exp ((k / 2 : ℝ) * ‖x‖) * Real.exp ((k / 2 : ℝ) * ‖x‖) := by
      rw [← Real.exp_add]
      congr 1
      ring
    rw [hexp]
    ring
  calc (1 + ‖x‖) ^ k * gaussWD x
      ≤ Real.exp ((k : ℝ) * ‖x‖) * gaussWD x :=
        mul_le_mul_of_nonneg_right hpow (le_of_lt hgw)
    _ = Real.exp ((k / 2 : ℝ) * ‖x‖) * gaussD x
          * (Real.exp ((k / 2 : ℝ) * ‖x‖) * gaussD x) := hdist
    _ = Real.exp ((k / 2 : ℝ) * ‖x‖) ^ 2 * gaussD x ^ 2 := by ring

/-- **The `L²` norm of a Gauss polynomial is bounded by its Gaussian integral.** -/
theorem norm_pgLp_sq_le (q : MvPolynomial (Fin d) ℂ) :
    ‖pgLp q‖ ^ 2
      ≤ ∫ x : Vd d, ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) q‖ ^ 2 * gaussWD x := by
  have hnorm : (inner ℂ (pgLp q) (pgLp q) : ℂ) = ((‖pgLp q‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  have hsq : ((‖pgLp q‖ ^ 2 : ℝ) : ℂ) = gaussInt (starP q * q) := by
    rw [← hnorm, inner_pgLp_pgLp]
  have hre : ‖pgLp q‖ ^ 2 = (gaussInt (starP q * q)).re := by
    rw [← hsq, Complex.ofReal_re]
  have hpt : ∀ x : Vd d,
      ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (starP q * q)‖
        = ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) q‖ ^ 2 := by
    intro x
    rw [map_mul, eval_starP, norm_mul, Complex.norm_conj, pow_two]
  rw [hre, gaussInt]
  refine (Complex.re_le_norm _).trans ?_
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  have hgw : (0 : ℝ) < gaussWD x := by
    rw [show gaussWD x = Real.exp (-‖x‖ ^ 2 / 2) from rfl]
    exact Real.exp_pos _
  beta_reduce
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hgw, hpt x]

/-- **The generator's polynomial.** -/
def gaussGenPoly (G : GaugeAlgebra 8) (dd : Fin 8) (t : ℝ)
    (p : MvPolynomial (Fin 99) ℂ) : MvPolynomial (Fin 99) ℂ :=
  firstOrder (ymGaussVec G dd) (rotPoly (gaussFlow G dd t) p)

/-- The generator's polynomial, evaluated at a point. -/
def genEval (G : GaugeAlgebra 8) (dd : Fin 8) (t : ℝ) (p : MvPolynomial (Fin 99) ℂ)
    (x : Vd 99) : ℂ :=
  MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (gaussGenPoly G dd t p)

/-- Entries of the rotation are bounded by one. -/
theorem gaussFlow_abs_entry_le_one (G : GaugeAlgebra 8) (dd : Fin 8) (s : ℝ) (k m : Fin 99) :
    |gaussFlow G dd s k m| ≤ 1 := by
  have h := congrFun (congrFun (gaussFlow_transpose_mul G dd s) m) m
  have hsum : ∑ j : Fin 99, gaussFlow G dd s j m * gaussFlow G dd s j m = 1 := by
    simpa [Matrix.mul_apply, Matrix.transpose_apply, Matrix.one_apply_eq] using h
  have hle : gaussFlow G dd s k m * gaussFlow G dd s k m ≤ 1 := by
    have hs := Finset.single_le_sum
      (f := fun j : Fin 99 => gaussFlow G dd s j m * gaussFlow G dd s j m)
      (fun j _ => mul_self_nonneg _) (Finset.mem_univ k)
    rwa [hsum] at hs
  have hsq : |gaussFlow G dd s k m| ^ 2 = gaussFlow G dd s k m * gaussFlow G dd s k m := by
    rw [sq_abs, sq]
  nlinarith [abs_nonneg (gaussFlow G dd s k m)]


/-- **The matrix acting on a point**: each coordinate of `M x` is bounded by the sum of the
entries of `M` times `‖x‖`. -/
theorem norm_mulVec_gaussMat_le (G : GaugeAlgebra 8) (dd : Fin 8) (x : Vd 99) (k : Fin 99) :
    ‖(((gaussMat G dd) *ᵥ (fun j => x j)) k : ℝ)‖
      ≤ (∑ k : Fin 99, ∑ j : Fin 99, |gaussMat G dd k j|) * ‖x‖ := by
  rw [Matrix.mulVec, dotProduct, Real.norm_eq_abs]
  calc |∑ j : Fin 99, gaussMat G dd k j * x j|
      ≤ ∑ j : Fin 99, |gaussMat G dd k j * x j| := Finset.abs_sum_le_sum_abs _ _
    _ = ∑ j : Fin 99, |gaussMat G dd k j| * |x j| := by
        exact Finset.sum_congr rfl fun j _ => abs_mul _ _
    _ ≤ ∑ j : Fin 99, |gaussMat G dd k j| * ‖x‖ := by
        refine Finset.sum_le_sum fun j _ => mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        simpa using coord_abs_le_norm x j
    _ = (∑ j : Fin 99, |gaussMat G dd k j|) * ‖x‖ := (Finset.sum_mul _ _ _).symm
    _ ≤ (∑ k : Fin 99, ∑ j : Fin 99, |gaussMat G dd k j|) * ‖x‖ := by
        refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg x)
        exact Finset.single_le_sum (f := fun k : Fin 99 => ∑ j : Fin 99,
          |gaussMat G dd k j|) (fun i _ => Finset.sum_nonneg fun j _ => abs_nonneg _)
          (Finset.mem_univ k)

/-- **The velocity of the rotated point** is bounded uniformly in the time. -/
theorem norm_rotVel_le (G : GaugeAlgebra 8) (dd : Fin 8) (x : Vd 99) (s : ℝ) (m : Fin 99) :
    ‖(rotVel G dd s x m : ℝ)‖
      ≤ 99 * ((∑ k : Fin 99, ∑ j : Fin 99, |gaussMat G dd k j|) * ‖x‖) := by
  have hfac : ((Matrix.transpose (gaussFlow G dd s) * gaussMat G dd) *ᵥ (fun j => x j))
      = Matrix.transpose (gaussFlow G dd s)
        *ᵥ ((gaussMat G dd) *ᵥ (fun j => x j)) := by
    rw [Matrix.mulVec_mulVec]
  rw [rotVel, hfac, Matrix.mulVec, dotProduct, Real.norm_eq_abs]
  calc |∑ k : Fin 99, Matrix.transpose (gaussFlow G dd s) m k
        * (gaussMat G dd *ᵥ (fun j => x j)) k|
      ≤ ∑ k : Fin 99, |Matrix.transpose (gaussFlow G dd s) m k
          * (gaussMat G dd *ᵥ (fun j => x j)) k| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _k : Fin 99, 1 * ((∑ k : Fin 99, ∑ j : Fin 99, |gaussMat G dd k j|) * ‖x‖) := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [abs_mul, Matrix.transpose_apply]
        refine mul_le_mul (gaussFlow_abs_entry_le_one G dd s k m) ?_
          (abs_nonneg _) zero_le_one
        exact norm_mulVec_gaussMat_le G dd x k
    _ = 99 * ((∑ k : Fin 99, ∑ j : Fin 99, |gaussMat G dd k j|) * ‖x‖) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        norm_num


/-- The pairing of the velocity with the gradient of `p` — the generator's value, written as
a finite sum.  Bundled in a definition so that statements stay small. -/
def genSum (G : GaugeAlgebra 8) (dd : Fin 8) (s : ℝ) (p : MvPolynomial (Fin 99) ℂ)
    (x : Vd 99) : ℂ :=
  ∑ m : Fin 99, ((rotVel G dd s x m : ℝ) : ℂ)
    * MvPolynomial.eval (fun i => ((rotPt G dd s x i : ℝ) : ℂ)) (pderiv m p)

/-- The generator's value is the pairing of the velocity with the gradient. -/
theorem genEval_eq_sum (G : GaugeAlgebra 8) (dd : Fin 8) (p : MvPolynomial (Fin 99) ℂ)
    (x : Vd 99) (s : ℝ) :
    genEval G dd s p x = genSum G dd s p x := by
  rw [genEval, gaussGenPoly, genSum, ← eval_sum_pderiv_gaussFlow G dd p x s, map_sum]
  exact Finset.sum_congr rfl fun m _ => by rw [map_mul, eval_C]

/-- A purely arithmetic regrouping bound: the termwise velocity/gradient estimate, summed. -/
theorem total_le_const_mul (N : ℕ) (Cm : Fin 99 → ℝ) (KM d : ℝ)
    (hKM : 0 ≤ KM) (hd : 0 ≤ d) (hCm : ∀ m : Fin 99, 0 ≤ Cm m) :
    ∑ m : Fin 99, (99 * (KM * d)) * (Cm m * (1 + d) ^ N)
      ≤ (99 * (99 * KM) * (∑ m : Fin 99, Cm m)) * (1 + d) ^ (N + 1) := by
  have h1 : (0 : ℝ) ≤ 1 + d := by linarith
  have hpow : (0 : ℝ) ≤ (1 + d) ^ N := pow_nonneg h1 N
  have hS : (0 : ℝ) ≤ ∑ m : Fin 99, Cm m := Finset.sum_nonneg fun m _ => hCm m
  have hkey : ∑ m : Fin 99, (99 * (KM * d)) * (Cm m * (1 + d) ^ N)
      = (99 * (KM * d)) * ((∑ m : Fin 99, Cm m) * (1 + d) ^ N) := by
    rw [← Finset.mul_sum, Finset.sum_mul]
  rw [hkey]
  have hstep : 99 * (KM * d) ≤ 99 * (99 * KM) * (1 + d) := by
    nlinarith
  calc (99 * (KM * d)) * ((∑ m : Fin 99, Cm m) * (1 + d) ^ N)
      ≤ (99 * (99 * KM) * (1 + d)) * ((∑ m : Fin 99, Cm m) * (1 + d) ^ N) :=
        mul_le_mul_of_nonneg_right hstep (mul_nonneg hS hpow)
    _ = (99 * (99 * KM) * (∑ m : Fin 99, Cm m)) * (1 + d) ^ (N + 1) := by
        rw [pow_succ]
        ring

set_option maxHeartbeats 2000000 in
-- rewriting the `Fin 99` sums of the generator exceeds the default budget
set_option maxRecDepth 4000 in
/-- **The generator's value is bounded by a fixed polynomial growth.**  The derivative of
`p(E(s)ᵀx)` is `Σ_m (E(s)ᵀMx)_m (∂_m p)(E(s)ᵀx)`; the velocity is bounded by `‖M‖`-data and
`‖x‖`, and each `∂_m p` grows like `(1 + ‖x‖)^{deg}` with `E(s)ᵀ` preserving `‖x‖`. -/
theorem exists_bound_genSum (G : GaugeAlgebra 8) (dd : Fin 8)
    (p : MvPolynomial (Fin 99) ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Vd 99) (s : ℝ),
      ‖genSum G dd s p x‖
        ≤ C * (1 + ‖x‖) ^ ((∑ m : Fin 99, (pderiv m p).totalDegree) + 1) := by
  classical
  set N : ℕ := ∑ m : Fin 99, (pderiv m p).totalDegree with hN
  choose Cm hCm0 hCm using fun m : Fin 99 => exists_norm_eval_le (pderiv m p)
  set KM : ℝ := ∑ k : Fin 99, ∑ j : Fin 99, |gaussMat G dd k j| with hKM
  have hKM0 : 0 ≤ KM := by
    rw [hKM]
    exact Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun j _ => abs_nonneg _
  have hD : ∀ (x : Vd 99) (s : ℝ) (m : Fin 99),
      ‖MvPolynomial.eval (fun i => ((rotPt G dd s x i : ℝ) : ℂ)) (pderiv m p)‖
        ≤ Cm m * (1 + ‖x‖) ^ N := by
    intro x s m
    have hO := gaussFlow_transpose_mul G dd s
    have hy : ‖rotIso hO x‖ = ‖x‖ := (rotIso hO).norm_map x
    have h := hCm m (rotIso hO x)
    rw [hy] at h
    have hexp : (pderiv m p).totalDegree ≤ N := by
      rw [hN]
      exact Finset.single_le_sum (f := fun m : Fin 99 => (pderiv m p).totalDegree)
        (fun i _ => Nat.zero_le _) (Finset.mem_univ m)
    refine h.trans ?_
    refine mul_le_mul_of_nonneg_left ?_ (hCm0 m)
    exact pow_le_pow_right₀ (by linarith [norm_nonneg x]) hexp
  have hS : (0 : ℝ) ≤ ∑ m : Fin 99, Cm m := Finset.sum_nonneg fun m _ => hCm0 m
  refine ⟨99 * (99 * KM) * (∑ m : Fin 99, Cm m), by nlinarith, ?_⟩
  intro x s
  have hx : 0 ≤ ‖x‖ := norm_nonneg x
  have hkey : ‖genSum G dd s p x‖
      ≤ ∑ m : Fin 99, (99 * (KM * ‖x‖)) * (Cm m * (1 + ‖x‖) ^ N) := by
    rw [genSum]
    refine (norm_sum_le _ _).trans ?_
    refine Finset.sum_le_sum fun m _ => ?_
    rw [norm_mul, Complex.norm_real]
    exact mul_le_mul (norm_rotVel_le G dd x s m) (hD x s m) (norm_nonneg _) (by positivity)
  exact hkey.trans (total_le_const_mul N Cm KM ‖x‖ hKM0 hx hCm0)


/-! ## The polynomial difference quotient -/

/-- Evaluation of a rotated polynomial is evaluation at the rotated point. -/
theorem eval_rotPoly_gaussFlow (G : GaugeAlgebra 8) (dd : Fin 8) (s : ℝ)
    (p : MvPolynomial (Fin 99) ℂ) (x : Vd 99) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (rotPoly (gaussFlow G dd s) p)
      = MvPolynomial.eval (fun i => ((rotPt G dd s x i : ℝ) : ℂ)) p := by
  rw [eval_rotPoly (gaussFlow_transpose_mul G dd s) p x]
  simp only [rotPt]

set_option maxHeartbeats 2000000 in
-- the mean value theorem step and the `ℂ`-valued rewrite chain exceed the budget
set_option maxRecDepth 8000 in
/-- The scalar function `s ↦ p(E(s)ᵀx)` has derivative the generator at every time. -/
theorem hasDerivAt_eval_rotPoly_gaussFlow (G : GaugeAlgebra 8) (dd : Fin 8)
    (p : MvPolynomial (Fin 99) ℂ) (x : Vd 99) (t : ℝ) :
    HasDerivAt (fun s : ℝ => MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ))
        (rotPoly (gaussFlow G dd s) p)) (genEval G dd t p x) t := by
  have h := hasDerivAt_eval_gaussFlow G dd p x t
  simpa only [genEval, gaussGenPoly] using h

/-- The generator, evaluated at a point, obeys the same polynomial growth bound. -/
theorem exists_bound_genEval (G : GaugeAlgebra 8) (dd : Fin 8)
    (p : MvPolynomial (Fin 99) ℂ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Vd 99) (s : ℝ),
      ‖genEval G dd s p x‖
        ≤ C * (1 + ‖x‖) ^ ((∑ m : Fin 99, (pderiv m p).totalDegree) + 1) := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_genSum G dd p
  exact ⟨C, hC0, fun x s => (genEval_eq_sum G dd p x s) ▸ hC x s⟩

set_option maxHeartbeats 2000000 in
-- the arithmetic regrouping of the sum needs more than the default budget
set_option maxRecDepth 4000 in
/-- **The difference quotient is bounded**, uniformly in the parameter, by the derivative
bound: the mean value theorem applied to `p(E(u)ᵀx) - (u - t) 𝒢_d p (x)`. -/
theorem norm_slope_eval_le (G : GaugeAlgebra 8) (dd : Fin 8)
    (p : MvPolynomial (Fin 99) ℂ) {C : ℝ}
    (hC : ∀ (x : Vd 99) (s : ℝ), ‖genEval G dd s p x‖
      ≤ C * (1 + ‖x‖) ^ ((∑ m : Fin 99, (pderiv m p).totalDegree) + 1))
    (x : Vd 99) {s t : ℝ} (hst : s ≠ t) :
    ‖(((s - t : ℝ))⁻¹ : ℂ) * (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ))
          (rotPoly (gaussFlow G dd s) p)
        - MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (rotPoly (gaussFlow G dd t) p))
      - genEval G dd t p x‖
      ≤ 2 * C * (1 + ‖x‖) ^ ((∑ m : Fin 99, (pderiv m p).totalDegree) + 1) := by
  set N : ℕ := (∑ m : Fin 99, (pderiv m p).totalDegree) + 1 with hN
  have hCN : ∀ (y : Vd 99) (u : ℝ), ‖genEval G dd u p y‖ ≤ C * (1 + ‖y‖) ^ N := hC
  set B : ℝ := C * (1 + ‖x‖) ^ N with hB
  have hCx : ∀ u : ℝ, ‖genEval G dd u p x‖ ≤ B := fun u => hCN x u
  set F : ℝ → ℂ := fun u => MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ))
    (rotPoly (gaussFlow G dd u) p) with hF
  set e : ℂ := genEval G dd t p x with he
  set ψ : ℝ → ℂ := fun u => F u - ((u - t : ℝ) : ℂ) * e with hψdef
  have hF' : ∀ u : ℝ, HasDerivAt F (genEval G dd u p x) u := by
    intro u
    have h := hasDerivAt_eval_rotPoly_gaussFlow G dd p x u
    simpa only [← hF] using h
  have hψ' : ∀ u : ℝ, HasDerivAt ψ (genEval G dd u p x - e) u := by
    intro u
    have hin : HasDerivAt (fun v : ℝ => ((v - t : ℝ) : ℂ)) 1 u :=
      ((hasDerivAt_id u).sub_const t).ofReal_comp
    have hmul : HasDerivAt (fun v : ℝ => ((v - t : ℝ) : ℂ) * e) (1 * e) u :=
      hin.mul_const e
    have h := (hF' u).sub hmul
    simpa only [← hψdef, one_mul] using h
  have hMVT : ‖ψ s - ψ t‖ ≤ 2 * B * ‖s - t‖ := by
    refine Convex.norm_image_sub_le_of_norm_deriv_le
      (f := ψ) (s := Set.uIcc s t) (x := t) (y := s) (C := 2 * B)
      (fun u _ => (hψ' u).differentiableAt) (fun u _ => ?_)
      (convex_uIcc s t) (Set.right_mem_uIcc) (Set.left_mem_uIcc)
    rw [(hψ' u).deriv]
    calc ‖genEval G dd u p x - e‖ ≤ ‖genEval G dd u p x‖ + ‖e‖ := norm_sub_le _ _
      _ ≤ B + B := add_le_add (hCx u) (hCx t)
      _ = 2 * B := by ring
  have hstc : (((s - t : ℝ)) : ℂ) ≠ 0 := by
    exact_mod_cast sub_ne_zero.2 hst
  have hψval : ψ s - ψ t = (F s - F t) - (((s - t : ℝ)) : ℂ) * e := by
    change (F s - (((s - t : ℝ)) : ℂ) * e) - (F t - (((t - t : ℝ)) : ℂ) * e) = _
    push_cast
    ring
  have hkey : (((s - t : ℝ))⁻¹ : ℂ) * (F s - F t) - e
      = (((s - t : ℝ))⁻¹ : ℂ) * (ψ s - ψ t) := by
    rw [hψval]
    conv_rhs => rw [mul_sub]
    have hci : ((↑(s - t) : ℂ))⁻¹ * ((↑(s - t) : ℂ)) = 1 := inv_mul_cancel₀ hstc
    have hce' : ((↑(s - t) : ℂ))⁻¹ * (((↑(s - t) : ℂ)) * e) = e := by
      rw [← mul_assoc, hci, one_mul]
    rw [hce']
  have hnormc : ‖(((s - t : ℝ))⁻¹ : ℂ)‖ = |s - t|⁻¹ := by
    rw [← Complex.ofReal_inv, Complex.norm_real, Real.norm_eq_abs, abs_inv]
  rw [hkey, norm_mul, hnormc]
  have hst0 : (0 : ℝ) < |s - t| := abs_pos.2 (sub_ne_zero.2 hst)
  have hnorm : ‖s - t‖ = |s - t| := by rw [Real.norm_eq_abs]
  calc |s - t|⁻¹ * ‖ψ s - ψ t‖
      ≤ |s - t|⁻¹ * (2 * B * ‖s - t‖) :=
        mul_le_mul_of_nonneg_left hMVT (le_of_lt (inv_pos.2 hst0))
    _ = 2 * B := by
        rw [hnorm, mul_comm (2 * B) |s - t|, ← mul_assoc,
          inv_mul_cancel₀ (ne_of_gt hst0), one_mul]
    _ = 2 * C * (1 + ‖x‖) ^ ((∑ m : Fin 99, (pderiv m p).totalDegree) + 1) := by
        rw [hB, hN]
        ring

/-- The polynomial whose `L²` class is the difference quotient minus the generator. -/
def slopePoly (G : GaugeAlgebra 8) (dd : Fin 8) (t s : ℝ)
    (p : MvPolynomial (Fin 99) ℂ) : MvPolynomial (Fin 99) ℂ :=
  MvPolynomial.C (((s - t : ℝ))⁻¹ : ℂ)
      * (rotPoly (gaussFlow G dd s) p - rotPoly (gaussFlow G dd t) p)
    - gaussGenPoly G dd t p

/-- The same polynomial written with the scalar action. -/
theorem slopePoly_eq (G : GaugeAlgebra 8) (dd : Fin 8) (t s : ℝ)
    (p : MvPolynomial (Fin 99) ℂ) :
    slopePoly G dd t s p
      = (((s - t : ℝ))⁻¹ : ℂ) • (rotPoly (gaussFlow G dd s) p
          - rotPoly (gaussFlow G dd t) p) - gaussGenPoly G dd t p := by
  rw [slopePoly, MvPolynomial.smul_eq_C_mul]

/-- Pointwise value of the difference quotient polynomial. -/
theorem eval_slopePoly (G : GaugeAlgebra 8) (dd : Fin 8) (t s : ℝ)
    (p : MvPolynomial (Fin 99) ℂ) (x : Vd 99) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (slopePoly G dd t s p)
      = (((s - t : ℝ))⁻¹ : ℂ) * (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ))
            (rotPoly (gaussFlow G dd s) p)
          - MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (rotPoly (gaussFlow G dd t) p))
        - genEval G dd t p x := by
  rw [slopePoly, map_sub, map_mul, eval_C, map_sub]
  rfl

/-- The squared norm of a polynomial, weighted by the Gaussian, is continuous. -/
theorem continuous_normEvalSq_mul_gaussWD (q : MvPolynomial (Fin 99) ℂ) :
    Continuous fun x : Vd 99 =>
      ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) q‖ ^ 2 * gaussWD x := by
  have h1 : Continuous fun x : Vd 99 =>
      ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) q‖ ^ 2 :=
    (continuous_polyEval q).norm.pow 2
  have h2 : Continuous fun x : Vd 99 => gaussWD x := by
    have hfun : gaussWD = fun x : Vd 99 => gaussD x ^ 2 := by
      funext x
      rw [gaussWD_eq_sq, pow_two]
    rw [hfun]
    exact continuous_gaussD.pow 2
  exact h1.mul h2

/-- `pgLp` of a difference and of a scalar multiple. -/
theorem pgLp_sub_pgLp (a b : MvPolynomial (Fin 99) ℂ) : pgLp (a - b) = pgLp a - pgLp b := by
  simpa only [pgMap_apply] using map_sub pgMap a b

theorem pgLp_smul_pgLp (c : ℂ) (a : MvPolynomial (Fin 99) ℂ) :
    pgLp (c • a) = c • pgLp a := by
  simpa only [pgMap_apply] using map_smul pgMap c a


/-- The difference quotient of the flow, as an `L²` element. -/
theorem slope_eq_pgLp (G : GaugeAlgebra 8) (dd : Fin 8) (p : MvPolynomial (Fin 99) ℂ)
    (t s : ℝ) :
    (s - t)⁻¹ • (gaussFlowOp G dd s (pgLp p) - gaussFlowOp G dd t (pgLp p))
      = pgLp (slopePoly G dd t s p) + pgLp (gaussGenPoly G dd t p) := by
  rw [gaussFlowOp_pgLp, gaussFlowOp_pgLp, ← pgLp_sub_pgLp, ← Complex.coe_smul,
    ← pgLp_smul_pgLp, slopePoly_eq, pgLp_sub_pgLp]
  simp only [Complex.ofReal_inv]
  exact (sub_add_cancel _ _).symm

set_option maxHeartbeats 4000000 in
-- dominated convergence over the difference quotients exceeds the default budget
set_option maxRecDepth 4000 in
/-- **The flow is differentiable in `L²`**, with derivative the Gauss constraint: the
difference quotients converge by dominated convergence, dominated by the fixed polynomial
growth of the generator. -/
theorem hasDerivAt_gaussFlowOp_pgLp (G : GaugeAlgebra 8) (dd : Fin 8)
    (p : MvPolynomial (Fin 99) ℂ) (t : ℝ) :
    HasDerivAt (fun s : ℝ => gaussFlowOp G dd s (pgLp p)) (pgLp (gaussGenPoly G dd t p)) t := by
  obtain ⟨C, hC0, hC⟩ := exists_bound_genEval G dd p
  set N : ℕ := (∑ m : Fin 99, (pderiv m p).totalDegree) + 1 with hN
  have hCN : ∀ (x : Vd 99) (s : ℝ), ‖genEval G dd s p x‖ ≤ C * (1 + ‖x‖) ^ N := hC
  have hslope : ∀ (x : Vd 99) {s : ℝ}, s ≠ t →
      ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (slopePoly G dd t s p)‖
        ≤ 2 * C * (1 + ‖x‖) ^ N := by
    intro x s hs
    rw [eval_slopePoly]
    exact norm_slope_eval_le G dd p hC x hs
  have hbound_int : Integrable (fun x : Vd 99 =>
      (2 * C) ^ 2 * (1 + ‖x‖) ^ (2 * N) * gaussWD x) := by
    have h := (integrable_oneAddNorm_pow_mul_gaussWD (d := 99) (2 * N)).const_mul ((2 * C) ^ 2)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    ring
  have hsq : Tendsto (fun s : ℝ => ∫ x : Vd 99,
      ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (slopePoly G dd t s p)‖ ^ 2 * gaussWD x)
      (𝓝[≠] t) (𝓝 0) := by
    have hmain := tendsto_integral_filter_of_dominated_convergence
      (l := 𝓝[≠] t)
      (F := fun s : ℝ => fun x : Vd 99 =>
        ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (slopePoly G dd t s p)‖ ^ 2 * gaussWD x)
      (f := fun _ : Vd 99 => (0 : ℝ))
      (bound := fun x : Vd 99 => (2 * C) ^ 2 * (1 + ‖x‖) ^ (2 * N) * gaussWD x)
      (Filter.Eventually.of_forall fun s =>
        (continuous_normEvalSq_mul_gaussWD (slopePoly G dd t s p)).aestronglyMeasurable)
      ?_ hbound_int ?_
    · simpa using hmain
    · filter_upwards [self_mem_nhdsWithin] with s hs
      filter_upwards with x
      have h := hslope x hs
      have hgw : (0 : ℝ) ≤ gaussWD x := by
        rw [show gaussWD x = Real.exp (-‖x‖ ^ 2 / 2) from rfl]
        exact le_of_lt (Real.exp_pos _)
      have h2 : ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (slopePoly G dd t s p)‖ ^ 2
          ≤ (2 * C * (1 + ‖x‖) ^ N) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (by positivity) hgw)]
      calc ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (slopePoly G dd t s p)‖ ^ 2 * gaussWD x
          ≤ (2 * C * (1 + ‖x‖) ^ N) ^ 2 * gaussWD x := mul_le_mul_of_nonneg_right h2 hgw
        _ = (2 * C) ^ 2 * (1 + ‖x‖) ^ (2 * N) * gaussWD x := by
            rw [mul_pow, mul_pow, ← pow_mul, mul_comm N 2]
    · refine Filter.Eventually.of_forall fun x => ?_
      have hsl := (hasDerivAt_iff_tendsto_slope).1
        (hasDerivAt_eval_rotPoly_gaussFlow G dd p x t)
      have hzero : Tendsto (fun s : ℝ => MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ))
          (slopePoly G dd t s p)) (𝓝[≠] t) (𝓝 0) := by
        have h1 : Tendsto (fun s : ℝ => slope (fun u : ℝ =>
            MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (rotPoly (gaussFlow G dd u) p)) t s
            - genEval G dd t p x) (𝓝[≠] t) (𝓝 (genEval G dd t p x - genEval G dd t p x)) :=
          hsl.sub_const _
        rw [sub_self] at h1
        refine h1.congr' (Filter.Eventually.of_forall fun s => ?_)
        beta_reduce
        rw [eval_slopePoly, slope, Complex.real_smul, Complex.ofReal_inv]
        rfl
      have h2 := (hzero.norm.pow 2).mul_const (gaussWD x)
      simpa using h2
  have hnorm : Tendsto (fun s : ℝ => ‖pgLp (slopePoly G dd t s p)‖) (𝓝[≠] t) (𝓝 0) := by
    have hsq' : Tendsto (fun s : ℝ => ‖pgLp (slopePoly G dd t s p)‖ ^ 2) (𝓝[≠] t) (𝓝 0) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsq
        (fun s => by positivity) (fun s => norm_pgLp_sq_le _)
    have hcomp : Tendsto (fun s : ℝ => Real.sqrt (‖pgLp (slopePoly G dd t s p)‖ ^ 2))
        (𝓝[≠] t) (𝓝 (Real.sqrt (0 : ℝ))) :=
      Real.continuous_sqrt.continuousAt.tendsto.comp hsq'
    have h3 : Tendsto (fun s : ℝ => Real.sqrt (‖pgLp (slopePoly G dd t s p)‖ ^ 2))
        (𝓝[≠] t) (𝓝 0) := by
      simpa using hcomp
    refine h3.congr' (Filter.Eventually.of_forall fun s => ?_)
    exact Real.sqrt_sq (norm_nonneg _)
  have hpg : Tendsto (fun s : ℝ => pgLp (slopePoly G dd t s p)) (𝓝[≠] t) (𝓝 0) :=
    (tendsto_iff_norm_sub_tendsto_zero).2 (by simpa using hnorm)
  have hadd : Tendsto (fun s : ℝ => pgLp (slopePoly G dd t s p) + pgLp (gaussGenPoly G dd t p))
      (𝓝[≠] t) (𝓝 (pgLp (gaussGenPoly G dd t p))) := by
    have h := hpg.add_const (pgLp (gaussGenPoly G dd t p))
    simpa using h
  refine (hasDerivAt_iff_tendsto_slope).2 ?_
  refine hadd.congr' (Filter.Eventually.of_forall fun s => ?_)
  simpa only [slope] using (slope_eq_pgLp G dd p t s).symm


/-! ## The generator on the core, and unconditional skew-adjointness -/

/-- The `CoreRep` of the polynomial core, in coordinates. -/
theorem coreRepPoly_equiv_pgLp (p : MvPolynomial (Fin 99) ℂ) :
    (coreRepPoly 99).equiv p = (⟨pgLp p, pgLp_mem_core p⟩ : polyGaussCore (d := 99)) :=
  Subtype.ext ((coreRepPoly 99).coe_equiv p)

theorem coreRepPoly_equiv_symm_pgLp (p : MvPolynomial (Fin 99) ℂ) :
    (coreRepPoly 99).equiv.symm (⟨pgLp p, pgLp_mem_core p⟩ : polyGaussCore (d := 99)) = p := by
  rw [← coreRepPoly_equiv_pgLp p, LinearEquiv.symm_apply_apply]

theorem coreRepPoly_op_pgLp (T : Module.End ℂ (MvPolynomial (Fin 99) ℂ))
    (p : MvPolynomial (Fin 99) ℂ) :
    (coreRepPoly 99).op T (⟨pgLp p, pgLp_mem_core p⟩ : polyGaussCore (d := 99))
      = ⟨pgLp (T p), pgLp_mem_core _⟩ := by
  refine Subtype.ext ?_
  rw [CoreRep.coe_op, coreRepPoly_equiv_symm_pgLp]

/-- The Gauss constraint acts on a core element by the transported polynomial operator. -/
theorem gaussPMap_core_apply (G : GaugeAlgebra 8) (dd : Fin 8)
    (q : MvPolynomial (Fin 99) ℂ) :
    (gaussPMap G dd (coreRepPoly 99) ⟨pgLp q, pgLp_mem_core q⟩ : L2d 99)
      = pgLp (ymGaussPoly G dd q) := by
  rw [gaussPMap_apply, LinearMap.comp_apply, coreRepPoly_op_pgLp]
  rfl

set_option maxHeartbeats 2000000 in
-- the subtype and `pgLp` rewrites of the core element exceed the default budget
/-- **The flow is differentiable on the core**, with derivative the Gauss charge: this is the
generator identity the flow chapter assumes, now proved for every core element. -/
theorem hasDerivAt_gaussFlowOp (G : GaugeAlgebra 8) (dd : Fin 8)
    (v : (gaussPMap G dd (coreRepPoly 99)).domain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => gaussFlowOp G dd s (v : L2d 99))
      ((gaussPMap G dd (coreRepPoly 99))
        ⟨gaussFlowOp G dd t (v : L2d 99),
          gaussFlowOp_mem_core G dd t v.2⟩) t := by
  obtain ⟨p, hp⟩ := v.2
  have hv : (v : L2d 99) = pgLp p := hp.symm
  have hfun : (fun s : ℝ => gaussFlowOp G dd s (v : L2d 99))
      = fun s : ℝ => gaussFlowOp G dd s (pgLp p) := by
    funext s
    rw [hv]
  have harg : (⟨gaussFlowOp G dd t (v : L2d 99), gaussFlowOp_mem_core G dd t v.2⟩
      : polyGaussCore (d := 99))
      = ⟨pgLp (rotPoly (gaussFlow G dd t) p), pgLp_mem_core _⟩ := by
    refine Subtype.ext ?_
    change gaussFlowOp G dd t (v : L2d 99) = pgLp (rotPoly (gaussFlow G dd t) p)
    rw [hv]
    exact gaussFlowOp_pgLp G dd t p
  have hderiv_eq : pgLp (gaussGenPoly G dd t p)
      = (gaussPMap G dd (coreRepPoly 99))
        ⟨gaussFlowOp G dd t (v : L2d 99),
          gaussFlowOp_mem_core G dd t v.2⟩ := by
    rw [harg, gaussPMap_core_apply]
    congr 1
    rw [ymGaussPoly_eq_firstOrder]
    rfl
  have h := hasDerivAt_gaussFlowOp_pgLp G dd p t
  rw [hderiv_eq, ← hfun] at h
  exact h

/-- **The closed Gauss charge is skew-adjoint — unconditionally.**  The flow bundle, its
invariance of the core and the generator identity are all proved in this chapter, so the
hypothesis of `gaussPMap_closure_skewAdjoint_of_rotation` is discharged. -/
theorem gaussPMap_closure_skewAdjoint (G : GaugeAlgebra 8) (dd : Fin 8) :
    SkewAdjoint (gaussPMap G dd (coreRepPoly 99)).closure :=
  gaussPMap_closure_skewAdjoint_of_rotation G dd fun v t => hasDerivAt_gaussFlowOp G dd v t


/-! ## Stone's theorem for the Gauss charge -/

set_option maxHeartbeats 1000000 in
-- the `ℂ`-inner-product rewrites on an abstract domain exceed the default budget
/-- Multiplying a skew operator by `I` makes it symmetric. -/
theorem isSymmetricOn_smul_I {A : L2d 99 →ₗ.[ℂ] L2d 99}
    (hsk : ∀ x y : A.domain, inner ℂ (A.toFun x) (y : L2d 99)
      = -inner ℂ (x : L2d 99) (A.toFun y)) :
    BookProof.ChapterUnitaryTransport.IsSymmetricOn A.domain (Complex.I • A.toFun) := by
  intro ψ φ
  rw [LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_left, inner_smul_right, hsk,
    Complex.conj_I]
  ring

set_option maxHeartbeats 1000000 in
-- the repeated unfolding of the Gauss closure's domain and operator exceeds the default budget
/-- **The Gauss charge as a self-adjoint operator**: `i 𝒢_d` is self-adjoint because `𝒢_d` is
skew-adjoint.  The domain is the closure's domain, which is dense. -/
noncomputable def gaussChargeSelfAdjoint (G : GaugeAlgebra 8) (dd : Fin 8) :
    UnboundedSelfAdjoint (L2d 99) where
  domain := (gaussPMap G dd (coreRepPoly 99)).closure.domain
  op := Complex.I • (gaussPMap G dd (coreRepPoly 99)).closure.toFun
  denseDomain := gaussPMap_closure_domain_dense G dd (coreRepPoly 99) polyGaussCore_dense
  symmetric := isSymmetricOn_smul_I fun x y =>
    gaussPMap_closure_skew G dd (coreRepPoly 99) polyGaussCore_dense x y
  selfAdjoint := by
    have hsk : ∀ x y : (gaussPMap G dd (coreRepPoly 99)).closure.domain,
        inner ℂ ((gaussPMap G dd (coreRepPoly 99)).closure.toFun x) (y : L2d 99)
          = -inner ℂ (x : L2d 99) ((gaussPMap G dd (coreRepPoly 99)).closure.toFun y) :=
      fun x y => gaussPMap_closure_skew G dd (coreRepPoly 99) polyGaussCore_dense x y
    have hskadj := gaussPMap_closure_skewAdjoint G dd
    rw [BookProof.ChapterUnitaryTransport.IsSelfAdjointOn]
    ext φ
    constructor
    · rintro ⟨η, hη⟩
      have hmem : φ ∈ (gaussPMap G dd (coreRepPoly 99)).closure.adjoint.domain := by
        refine LinearPMap.mem_adjoint_domain_of_exists φ ⟨Complex.I • η, ?_⟩
        intro x
        change inner ℂ (Complex.I • η) (x : L2d 99)
          = inner ℂ φ ((gaussPMap G dd (coreRepPoly 99)).closure.toFun x)
        have hx := hη x
        rw [LinearMap.smul_apply, inner_smul_left, Complex.conj_I] at hx
        have hc : Complex.I * inner ℂ φ ((gaussPMap G dd (coreRepPoly 99)).closure.toFun x)
            = inner ℂ η (x : L2d 99) := by
          have h := congrArg (starRingEnd ℂ) hx
          simpa [map_mul, Complex.conj_I, inner_conj_symm] using h
        have hI : -Complex.I * Complex.I = 1 := by
          rw [neg_mul, Complex.I_mul_I]
          norm_num
        rw [inner_smul_left, Complex.conj_I]
        calc -Complex.I * inner ℂ η (x : L2d 99)
            = -Complex.I * (Complex.I
                * inner ℂ φ ((gaussPMap G dd (coreRepPoly 99)).closure.toFun x)) := by rw [hc]
          _ = inner ℂ φ ((gaussPMap G dd (coreRepPoly 99)).closure.toFun x) := by
              rw [← mul_assoc, hI, one_mul]
      rwa [hskadj, LinearPMap.neg_domain] at hmem
    · intro hφ
      refine ⟨Complex.I • (gaussPMap G dd (coreRepPoly 99)).closure ⟨φ, hφ⟩, ?_⟩
      intro ψ
      rw [LinearMap.smul_apply, inner_smul_left, Complex.conj_I, inner_smul_right,
        hsk ψ ⟨φ, hφ⟩, neg_mul, mul_neg, neg_neg]
      rfl

@[simp] theorem gaussChargeSelfAdjoint_domain (G : GaugeAlgebra 8) (dd : Fin 8) :
    (gaussChargeSelfAdjoint G dd).domain = (gaussPMap G dd (coreRepPoly 99)).closure.domain :=
  rfl

@[simp] theorem gaussChargeSelfAdjoint_op (G : GaugeAlgebra 8) (dd : Fin 8) :
    (gaussChargeSelfAdjoint G dd).op
      = Complex.I • (gaussPMap G dd (coreRepPoly 99)).closure.toFun :=
  rfl

/-- **The unitary group of the Gauss charge.**  Stone's theorem, applied to the self-adjoint
operator `i 𝒢_d`, produces a strongly continuous one-parameter unitary group solving
`d/dt U(t) v = 𝒢_d (U(t) v)` on the domain. -/
theorem gaussCharge_stoneFlow (G : GaugeAlgebra 8) (dd : Fin 8) :
    ∃ U : ℝ → (L2d 99 →L[ℂ] L2d 99), IsStoneFlow (gaussChargeSelfAdjoint G dd) U :=
  ⟨_, isStoneFlow_stoneU _⟩

end

end BookProof.Qym.GaussGenerator
