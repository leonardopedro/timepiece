import BookProof.Qym.ChapterYangMillsGaussRotationFlow

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

open Matrix MvPolynomial MeasureTheory
open scoped Norms.Operator
open BookProof.Qym.GaussCasimir BookProof.BrstYmCommute BookProof.BookBrstYangMills
open BookProof.YangMillsHermite BookProof.HermiteProductCore BookProof.Qym.GaussSkew
open BookProof.Qym.GaussClosure BookProof.Qym.GaussSkewAdjoint
open BookProof.Qym.GaussSkewAdjointDomain BookProof.Qym.GaussRotationFlow
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

/-! ## The pointwise derivative -/

/-- The rotated point `E(t)ᵀ x`. -/
def rotPt (G : GaugeAlgebra 8) (dd : Fin 8) (t : ℝ) (x : Vd 99) : Fin 99 → ℝ :=
  fun i => ((rotIso (gaussFlow_transpose_mul G dd t) x).ofLp) i

end
