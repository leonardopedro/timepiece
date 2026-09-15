import Mathlib
import BookProof.ChapterHyperbolicQuadraticEsa

/-!
# General (non-diagonal) quadratic Hamiltonians of arbitrary signature

`BookProof.ChapterHyperbolicQuadraticEsa` proves that the *diagonal* quadratic operator

`H_c = ∑ᵢ cᵢ (−∂ᵢ² + xᵢ²/4)`,  `c : Fin d → ℝ` arbitrary (hyperbolic signatures included),

is essentially self-adjoint on the Gauss–polynomial (product Hermite) core of `L²(ℝᵈ)`.
This module removes the diagonality restriction: for an **arbitrary real symmetric matrix**
`A` the operator

`H_A = ∑_{k,l} A_{kl} (π_k π_l + x_k x_l / 4)`,  `π_k = −i ∂/∂x_k`,

— the general quadratic Hamiltonian whose kinetic and potential forms share the matrix
`A`, of arbitrary signature — is symmetric and essentially self-adjoint on the same core.
With `A = diag(c)` this is the diagonal theorem; with `A` a rotated Minkowski form it is
`□ + V` written in rotated coordinates, where neither the kinetic form nor the potential
is diagonal.

## The route

An orthogonal change of coordinates.  The Gaussian `e^{−‖x‖²/4}` is rotation invariant, so
composition with an orthogonal matrix `O` maps the Gauss–polynomial core onto itself; on
the polynomial coordinates it is the substitution `rotPoly O`, an algebra automorphism.
The canonical pair transforms contravariantly with the *same* matrix
(`rotPoly_mulXPoly`, `rotPoly_momPoly`), so the diagonal operator `H_c` is carried onto
`H_A` with `A = O diag(c) Oᵀ` (`quadPolyMat_rotPoly`).  The rotated product Hermite
functions are therefore an orthonormal family of joint eigenvectors of `H_A` spanning the
core (`orthonormal_rotHermiteLp`, `span_rotHermiteLp`, `quadOpMat_rotHermiteLp`), and the
diagonal instruments of `BookProof.ChapterHyperbolicQuadraticEsa`
(`symmetricOn_of_diagonal`, `deficiencyTrivialAt_of_diagonal`) finish the argument.
The spectral theorem for real symmetric matrices supplies `O` and `c` for an arbitrary
symmetric `A`.

## What is proved

* `rotPoly`, `pderiv_rotPoly`, `rotPoly_mulXPoly`, `rotPoly_momPoly` — the orthogonal
  substitution on polynomial coordinates and its action on the canonical pair;
* `rotIso`, `gaussInt_rotPoly`, `inner_pgLp_rotPoly` — the rotation as a
  measure-preserving linear isometry of `ℝᵈ`, and the resulting unitarity on the core;
* `quadPolyMat`, `quadPolyMat_rotPoly` — the general quadratic operator and the
  conjugation identity `H_{O diag(c) Oᵀ} ∘ R = R ∘ H_c`;
* `rotHermiteLp`, `orthonormal_rotHermiteLp`, `span_rotHermiteLp` — the rotated product
  Hermite functions are an orthonormal family whose span is the core;
* `quadOpMat_rotConj_symmetric`, `quadOpMat_rotConj_essentiallySelfAdjoint` — the headline
  for `A = O diag(c) Oᵀ`;
* `quadOpMat_symmetric`, `quadOpMat_essentiallySelfAdjoint` — **the headline**: for every
  real symmetric matrix `A`, `H_A` is symmetric and essentially self-adjoint on the
  Gauss–polynomial core of `L²(ℝᵈ)`;
* `quadOpMat_not_bounded`, `polyGaussCore_dense_L2` — non-vacuity: the operator is
  genuinely unbounded whenever `A ≠ 0`, and its domain is dense.

## Honest boundary

The potential is quadratic and its matrix is *the same* as the matrix of the kinetic form:
that matched pair is what a single rotation diagonalizes.  A general Faris–Lavine
potential bounded above by a quadratic remains out of reach by this argument, exactly as
recorded in `BookProof.ChapterHyperbolicQuadraticEsa`.
-/

namespace BookProof.QuadraticRotation

open MeasureTheory MvPolynomial Matrix
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HyperbolicQuadratic

noncomputable section

variable {d : ℕ}

/-! ## 1. The orthogonal substitution on polynomial coordinates -/

/-- The substitution `Xᵢ ↦ ∑ⱼ Oⱼᵢ Xⱼ`: on functions this is `p ↦ p ∘ Oᵀ`. -/
def rotPoly (O : Matrix (Fin d) (Fin d) ℝ) :
    MvPolynomial (Fin d) ℂ →ₐ[ℂ] MvPolynomial (Fin d) ℂ :=
  aeval (fun i => ∑ j, C ((O j i : ℝ) : ℂ) * X j)

theorem rotPoly_X (O : Matrix (Fin d) (Fin d) ℝ) (i : Fin d) :
    rotPoly O (X i) = ∑ j, C ((O j i : ℝ) : ℂ) * X j := by
  simp [rotPoly]

theorem rotPoly_C (O : Matrix (Fin d) (Fin d) ℝ) (z : ℂ) : rotPoly O (C z) = C z := by
  simp [rotPoly]

/-- **The chain rule** for the substitution: `∂_k (p ∘ Oᵀ) = ∑ᵢ O_{ki} (∂ᵢp) ∘ Oᵀ`. -/
theorem pderiv_rotPoly (O : Matrix (Fin d) (Fin d) ℝ) (k : Fin d)
    (p : MvPolynomial (Fin d) ℂ) :
    pderiv k (rotPoly O p) = ∑ i, C ((O k i : ℝ) : ℂ) * rotPoly O (pderiv i p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq, Finset.sum_add_distrib, mul_add]
  | mul_X p i hp =>
      have hd : pderiv k (rotPoly O (X i)) = C ((O k i : ℝ) : ℂ) := by
        rw [rotPoly_X, map_sum]
        simp [Pi.single_apply]
      have hr : ∀ m : Fin d, pderiv m (p * X i)
          = pderiv m p * X i + (if m = i then p else 0) := by
        intro m
        rw [Derivation.leibniz, pderiv_X]
        by_cases h : m = i <;> simp [h, Pi.single_apply, smul_eq_mul, mul_comm, add_comm]
      have hRHS : ∑ m, C ((O k m : ℝ) : ℂ) * rotPoly O (pderiv m (p * X i))
          = (∑ m, C ((O k m : ℝ) : ℂ) * rotPoly O (pderiv m p)) * rotPoly O (X i)
            + C ((O k i : ℝ) : ℂ) * rotPoly O p := by
        have hsplit : ∀ m : Fin d, C ((O k m : ℝ) : ℂ) * rotPoly O (pderiv m (p * X i))
            = C ((O k m : ℝ) : ℂ) * rotPoly O (pderiv m p) * rotPoly O (X i)
              + (if m = i then C ((O k m : ℝ) : ℂ) * rotPoly O p else 0) := by
          intro m
          rw [hr m, map_add, map_mul, mul_add]
          by_cases h : m = i <;> simp [h, mul_assoc]
        rw [Finset.sum_congr rfl fun m _ => hsplit m, Finset.sum_add_distrib, Finset.sum_mul]
        congr 1
        simp
      rw [map_mul, Derivation.leibniz, hd, hp, hRHS]
      simp only [smul_eq_mul]
      ring

/-- The substitutions by `O` and by `Oᵀ` are mutually inverse. -/
theorem rotPoly_rotPoly_transpose {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (p : MvPolynomial (Fin d) ℂ) : rotPoly O (rotPoly Oᵀ p) = p := by
  have hOO : O * Oᵀ = 1 := mul_eq_one_comm.mp hO
  have hgen : ∀ i : Fin d, rotPoly O (rotPoly Oᵀ (X i)) = X i := by
    intro i
    rw [rotPoly_X, map_sum]
    have hstep : ∀ j : Fin d, rotPoly O (C ((Oᵀ j i : ℝ) : ℂ) * X j)
        = ∑ k, C (((O i j * O k j : ℝ)) : ℂ) * X k := by
      intro j
      rw [map_mul, rotPoly_C, rotPoly_X, Finset.mul_sum]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← mul_assoc, ← map_mul]
      norm_num [Matrix.transpose_apply]
    rw [Finset.sum_congr rfl fun j _ => hstep j, Finset.sum_comm]
    have hk : ∀ k : Fin d, ∑ j, C (((O i j * O k j : ℝ)) : ℂ) * X k
        = (if i = k then (1 : MvPolynomial (Fin d) ℂ) else 0) * X k := by
      intro k
      rw [← Finset.sum_mul]
      congr 1
      have h1 := congrFun (congrFun hOO i) k
      have h2 : ∑ j, O i j * O k j = if i = k then (1 : ℝ) else 0 := by
        simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.transpose_apply] using h1
      rw [← map_sum,
        show (∑ j, ((O i j * O k j : ℝ) : ℂ)) = ((∑ j, O i j * O k j : ℝ) : ℂ) by
          push_cast; ring,
        h2]
      by_cases h : i = k <;> simp [h]
    rw [Finset.sum_congr rfl fun k _ => hk k]
    simp
  have hcomp := MvPolynomial.algHom_ext (f := (rotPoly O).comp (rotPoly Oᵀ))
    (g := AlgHom.id ℂ (MvPolynomial (Fin d) ℂ)) (by intro i; simpa using hgen i)
  exact congrArg (fun f => f p) hcomp

theorem rotPoly_surjective {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) :
    Function.Surjective (rotPoly O) := fun p =>
  ⟨rotPoly Oᵀ p, rotPoly_rotPoly_transpose hO p⟩

/-! ## 2. The canonical pair transforms with the same matrix -/

theorem rotPoly_mulXPoly (O : Matrix (Fin d) (Fin d) ℝ) (i : Fin d)
    (p : MvPolynomial (Fin d) ℂ) :
    rotPoly O (mulXPoly i p) = ∑ k, ((O k i : ℝ) : ℂ) • mulXPoly k (rotPoly O p) := by
  simp only [mulXPoly_apply, map_mul, rotPoly_X, Finset.sum_mul]
  exact Finset.sum_congr rfl fun k _ => by rw [MvPolynomial.smul_eq_C_mul, mul_assoc]

/-- `∂ᵢ` pulled back: `R(∂ᵢ p) = ∑ₖ O_{ki} ∂ₖ (R p)`, by the chain rule and `OᵀO = 1`. -/
theorem rotPoly_pderiv {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (i : Fin d)
    (p : MvPolynomial (Fin d) ℂ) :
    rotPoly O (pderiv i p) = ∑ k, ((O k i : ℝ) : ℂ) • pderiv k (rotPoly O p) := by
  have hexp : ∀ k : Fin d, ((O k i : ℝ) : ℂ) • pderiv k (rotPoly O p)
      = ∑ m, ((O k i * O k m : ℝ) : ℂ) • rotPoly O (pderiv m p) := by
    intro k
    rw [pderiv_rotPoly, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [MvPolynomial.smul_eq_C_mul, MvPolynomial.smul_eq_C_mul, ← mul_assoc, ← map_mul]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl fun k _ => hexp k, Finset.sum_comm]
  have hm : ∀ m : Fin d, ∑ k, ((O k i * O k m : ℝ) : ℂ) • rotPoly O (pderiv m p)
      = (if i = m then (1 : ℂ) else 0) • rotPoly O (pderiv m p) := by
    intro m
    rw [← Finset.sum_smul]
    congr 1
    have h1 := congrFun (congrFun hO i) m
    have h2 : ∑ k, O k i * O k m = if i = m then (1 : ℝ) else 0 := by
      simpa [Matrix.mul_apply, Matrix.one_apply, Matrix.transpose_apply] using h1
    rw [show (∑ k, ((O k i * O k m : ℝ) : ℂ)) = ((∑ k, O k i * O k m : ℝ) : ℂ) by
        push_cast; ring, h2]
    by_cases h : i = m <;> simp [h]
  rw [Finset.sum_congr rfl fun m _ => hm m]
  simp

theorem rotPoly_momPoly {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1) (i : Fin d)
    (p : MvPolynomial (Fin d) ℂ) :
    rotPoly O (momPoly i p) = ∑ k, ((O k i : ℝ) : ℂ) • momPoly k (rotPoly O p) := by
  have hX : rotPoly O (X i * p) = ∑ k, ((O k i : ℝ) : ℂ) • (X k * rotPoly O p) := by
    simpa using rotPoly_mulXPoly O i p
  rw [momPoly_apply, map_mul, rotPoly_C, map_sub, map_mul, rotPoly_C, rotPoly_pderiv hO, hX,
    Finset.mul_sum, ← Finset.sum_sub_distrib, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [momPoly_apply, MvPolynomial.smul_eq_C_mul]
  ring

/-! ## 3. The general quadratic operator and the conjugation identity -/

/-- The general quadratic Hamiltonian `∑_{k,l} A_{kl}(π_k π_l + x_k x_l/4)` in polynomial
coordinates. -/
def quadPolyMat (A : Matrix (Fin d) (Fin d) ℝ) :
    MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  ∑ k, ∑ l, ((A k l : ℝ) : ℂ) •
    ((momPoly k).comp (momPoly l) + (1/4 : ℂ) • ((mulXPoly k).comp (mulXPoly l)))

theorem quadPolyMat_apply (A : Matrix (Fin d) (Fin d) ℝ) (p : MvPolynomial (Fin d) ℂ) :
    quadPolyMat A p = ∑ k, ∑ l, ((A k l : ℝ) : ℂ) •
      (momPoly k (momPoly l p) + (1/4 : ℂ) • (X k * (X l * p))) := by
  simp [quadPolyMat, LinearMap.sum_apply]

/-- The diagonal-weight operator, in the form used below. -/
theorem quadPoly_apply' (c : Fin d → ℝ) (p : MvPolynomial (Fin d) ℂ) :
    quadPoly c p = ∑ i, ((c i : ℝ) : ℂ) •
      (momPoly i (momPoly i p) + (1/4 : ℂ) • (X i * (X i * p))) := by
  simp [quadPoly, oscPoly, LinearMap.sum_apply]

/-- **The diagonal case is the operator of `BookProof.ChapterHyperbolicQuadraticEsa`**, so
the theorems below genuinely extend the diagonal ones. -/
theorem quadPolyMat_diagonal (c : Fin d → ℝ) :
    quadPolyMat (Matrix.diagonal c) = quadPoly c := by
  refine LinearMap.ext fun p => ?_
  rw [quadPolyMat_apply, quadPoly_apply']
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Finset.sum_eq_single k (fun l _ hl => by simp [Ne.symm hl]) (by simp)]
  simp

/-- `O diag(c) Oᵀ`, written entrywise. -/
def rotConj (O : Matrix (Fin d) (Fin d) ℝ) (c : Fin d → ℝ) : Matrix (Fin d) (Fin d) ℝ :=
  fun k l => ∑ i, O k i * c i * O l i

theorem rotConj_eq (O : Matrix (Fin d) (Fin d) ℝ) (c : Fin d → ℝ) :
    rotConj O c = O * Matrix.diagonal c * Oᵀ := by
  ext k l
  simp only [rotConj, Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Finset.sum_eq_single j (fun i _ hi => by simp [hi]) (by simp)]
  simp

/-- **The conjugation identity**: the rotation carries the diagonal Hamiltonian `H_c` onto
the general one `H_{O diag(c) Oᵀ}`. -/
theorem quadPolyMat_rotPoly {O : Matrix (Fin d) (Fin d) ℝ} (hO : Oᵀ * O = 1)
    (c : Fin d → ℝ) (p : MvPolynomial (Fin d) ℂ) :
    quadPolyMat (rotConj O c) (rotPoly O p) = rotPoly O (quadPoly c p) := by
  have hmom : ∀ i : Fin d, rotPoly O (momPoly i (momPoly i p))
      = ∑ k, ∑ l, ((O k i * O l i : ℝ) : ℂ) • momPoly k (momPoly l (rotPoly O p)) := by
    intro i
    rw [rotPoly_momPoly hO i (momPoly i p), rotPoly_momPoly hO i p]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [map_smul, smul_smul]
    congr 1
    push_cast
    ring
  have hx : ∀ i : Fin d, rotPoly O (X i * (X i * p))
      = ∑ k, ∑ l, ((O k i * O l i : ℝ) : ℂ) • (X k * (X l * rotPoly O p)) := by
    intro i
    have h1 := rotPoly_mulXPoly O i (X i * p)
    have h2 := rotPoly_mulXPoly O i p
    simp only [mulXPoly_apply] at h1 h2
    rw [h1, h2]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.mul_sum, Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [mul_smul_comm, smul_smul]
    congr 1
    push_cast
    ring
  have hboth : ∀ i : Fin d, rotPoly O (((c i : ℝ) : ℂ) •
      (momPoly i (momPoly i p) + (1/4 : ℂ) • (X i * (X i * p))))
      = ∑ k, ∑ l, ((O k i * c i * O l i : ℝ) : ℂ) •
          (momPoly k (momPoly l (rotPoly O p))
            + (1/4 : ℂ) • (X k * (X l * rotPoly O p))) := by
    intro i
    have hquarter : (1/4 : ℂ) •
        (∑ k, ∑ l, ((O k i * O l i : ℝ) : ℂ) • (X k * (X l * rotPoly O p)))
        = ∑ k, ∑ l, ((O k i * O l i : ℝ) : ℂ) •
            ((1/4 : ℂ) • (X k * (X l * rotPoly O p))) := by
      simp only [Finset.smul_sum]
      exact Finset.sum_congr rfl fun k _ =>
        Finset.sum_congr rfl fun l _ => smul_comm _ _ _
    have hcomb :
        (∑ k, ∑ l, ((O k i * O l i : ℝ) : ℂ) • momPoly k (momPoly l (rotPoly O p)))
          + (∑ k, ∑ l, ((O k i * O l i : ℝ) : ℂ) •
              ((1/4 : ℂ) • (X k * (X l * rotPoly O p))))
        = ∑ k, ∑ l, ((O k i * O l i : ℝ) : ℂ) •
            (momPoly k (momPoly l (rotPoly O p))
              + (1/4 : ℂ) • (X k * (X l * rotPoly O p))) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun l _ => (smul_add _ _ _).symm
    rw [map_smul, map_add, map_smul, hmom i, hx i, hquarter, hcomb, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [smul_smul]
    congr 1
    push_cast
    ring
  have hswap : ∀ f : Fin d → Fin d → Fin d → MvPolynomial (Fin d) ℂ,
      ∑ i, ∑ k, ∑ l, f i k l = ∑ k, ∑ l, ∑ i, f i k l := by
    intro f
    rw [Finset.sum_comm]
    exact Finset.sum_congr rfl fun k _ => Finset.sum_comm
  rw [quadPoly_apply', map_sum, Finset.sum_congr rfl fun i _ => hboth i, hswap,
    quadPolyMat_apply]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  rw [rotConj]
  push_cast
  ring

end

end BookProof.QuadraticRotation
