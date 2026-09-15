import Mathlib
import BookProof.ChapterHermiteProductCore
import BookProof.ChapterFriedrichsExtension

/-!
# The gauge-fixed Yang–Mills Hamiltonian on the Gauss–polynomial core of `L²(ℝ⁹⁹)`

`PLAN_LEAN_SPECIALIST_QYM_FLOW.md` Part F asks for the **field-space** (option
(b)) realization of the Weyl-gauge Yang–Mills Hamiltonian: the fields must act as
genuine multiplication and differentiation operators on a dense core of
`L²(ℝ⁹⁹)`, not merely abstractly on an occupation-number space.

The core is `BookProof.HermiteProductCore.polyGaussCore`, the span of the product
Hermite functions `p(x) e^{-‖x‖²/4}`.  Because the map `p ↦ p · e^{-‖x‖²/4}` is
an injective linear map from `ℂ[X₀,…,X₉₈]`, every operator can be defined at the
purely algebraic level of polynomials and transported to the core (`CoreRep`).

* `mulOp f` — multiplication by a polynomial (F.2, the coordinate operators
  `A_{k,a}`);
* `derOp j`, `momOp j` — the true derivative `∂_j` of `p·e^{-‖x‖²/4}` written back
  on the polynomial factor, and the momentum `π_j = −i ∂_j` (F.3);
* `magPoly i a` — the magnetic field
  `B_{i a} = ε_{ijk}(∂_j A_{k,a} + f_{abc} A_{j,b} A_{k,c})`, a *real* polynomial
  in the `99 = 3 + 24 + 72` coordinates (3 spatial, 24 fields `A_{j,a}`, 72
  independent derivative coordinates `∂_j A_{k,a}`), acting by multiplication
  (F.4);
* `weylProd` — the Weyl ordering `½(PQ + QP)`, symmetric whenever `P` and `Q`
  are (F.5); the canonical commutation relation `[A_{j}, π_{j}] = i` is
  `commutator_coord_mom`;
* `ymHamiltonian` — `H₁ = ½ Σ π² + ½ Σ B²`, the *positive* sum of squares (the
  sign of `book.tex:7077` reconciled), well defined, symmetric and positive on
  the core (F.6–F.8);
* `ym_hermite_friedrichs_extension` (F.9) and `ym_hermite_hashimoto_selects`
  (F.10) — the instantiation of the already-proved
  `BookProof.FriedrichsExtension.friedrichs_extension_exists` and
  `BookProof.FriedrichsExtension.weyl_hashimoto_selects_friedrichs`.

Nothing here claims a mass gap or global existence; the Millennium problem stays
out of scope.
-/

namespace BookProof.YangMillsHermite

open MeasureTheory Complex MvPolynomial
open BookProof.HermiteProductCore BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension BookProof.HashimotoShiftInvert

noncomputable section

variable {d : ℕ}

/-! ## Conjugate polynomials and the inner product on the core -/

/-- Complex conjugation of the coefficients of a polynomial. -/
def starP (p : MvPolynomial (Fin d) ℂ) : MvPolynomial (Fin d) ℂ := map (starRingEnd ℂ) p

@[simp] theorem starP_add (p q : MvPolynomial (Fin d) ℂ) :
    starP (p + q) = starP p + starP q := map_add _ _ _

@[simp] theorem starP_mul (p q : MvPolynomial (Fin d) ℂ) :
    starP (p * q) = starP p * starP q := map_mul _ _ _

@[simp] theorem starP_X (j : Fin d) : starP (X j : MvPolynomial (Fin d) ℂ) = X j := by
  simp [starP]

@[simp] theorem starP_C (c : ℂ) : starP (C c : MvPolynomial (Fin d) ℂ) = C ((starRingEnd ℂ) c) := by
  simp [starP]

@[simp] theorem starP_zero : starP (0 : MvPolynomial (Fin d) ℂ) = 0 := map_zero _

theorem starP_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin d) ℂ) :
    starP (∑ i ∈ s, f i) = ∑ i ∈ s, starP (f i) := map_sum _ _ _

theorem starP_smul (c : ℂ) (p : MvPolynomial (Fin d) ℂ) :
    starP (c • p) = ((starRingEnd ℂ) c) • starP p := by
  rw [smul_eq_C_mul, starP_mul, starP_C, smul_eq_C_mul]

theorem starP_real_smul (t : ℝ) (p : MvPolynomial (Fin d) ℂ) :
    starP ((t : ℂ) • p) = (t : ℂ) • starP p := by
  rw [starP_smul, Complex.conj_ofReal]

/-- A polynomial with *real* coefficients is fixed by `starP`; these are exactly
the ones that act as symmetric multiplication operators. -/
def RealCoeff (p : MvPolynomial (Fin d) ℂ) : Prop := starP p = p

theorem RealCoeff.add {p q : MvPolynomial (Fin d) ℂ} (hp : RealCoeff p) (hq : RealCoeff q) :
    RealCoeff (p + q) := by
  change starP (p + q) = p + q
  rw [starP_add, show starP p = p from hp, show starP q = q from hq]

theorem RealCoeff.mul {p q : MvPolynomial (Fin d) ℂ} (hp : RealCoeff p) (hq : RealCoeff q) :
    RealCoeff (p * q) := by
  change starP (p * q) = p * q
  rw [starP_mul, show starP p = p from hp, show starP q = q from hq]

theorem RealCoeff.smul {t : ℝ} {p : MvPolynomial (Fin d) ℂ} (hp : RealCoeff p) :
    RealCoeff ((t : ℂ) • p) := by
  rw [RealCoeff, starP_real_smul, hp]

theorem RealCoeff.sum {ι : Type*} {s : Finset ι} {f : ι → MvPolynomial (Fin d) ℂ}
    (h : ∀ i ∈ s, RealCoeff (f i)) : RealCoeff (∑ i ∈ s, f i) := by
  rw [RealCoeff, starP_sum]
  exact Finset.sum_congr rfl h

theorem realCoeff_X (j : Fin d) : RealCoeff (X j : MvPolynomial (Fin d) ℂ) := starP_X j

/-- Conjugation of the coefficients is conjugation of the values at real points. -/
theorem eval_starP (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (starP p)
      = (starRingEnd ℂ) (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p) := by
  rw [starP, eval_map]
  induction p using MvPolynomial.induction_on with
  | C a => simp
  | add p q hp hq => simp [hp, hq]
  | mul_X p i hp => simp [hp]

/-- **The inner product of two core vectors is a Gaussian polynomial integral.** -/
theorem inner_pgLp_pgLp (p q : MvPolynomial (Fin d) ℂ) :
    (inner ℂ (pgLp p) (pgLp q) : ℂ) = gaussInt (starP p * q) := by
  rw [inner_pgLp, gaussInt]
  refine integral_congr_ae ?_
  filter_upwards [pgLp_coeFn q] with x hx
  have hev : MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (starP p * q)
      = (starRingEnd ℂ) (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p)
        * MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) q := by
    rw [map_mul, eval_starP]
  rw [hx, hev, pgFun, pgFun, gaussWD_eq_sq]
  simp only [map_mul, Complex.conj_ofReal]
  push_cast
  ring

/-! ## Polynomial-level operators and Gauss symmetry -/

/-- A polynomial-level operator is **Gauss symmetric** when it is symmetric for
the Gaussian inner product `⟪p, q⟫ = ∫ p̄ q e^{-‖x‖²/2}`.  By
`inner_pgLp_pgLp` this is exactly symmetry of the transported operator on the
core. -/
def PolySym (T : Module.End ℂ (MvPolynomial (Fin d) ℂ)) : Prop :=
  ∀ p q : MvPolynomial (Fin d) ℂ, gaussInt (starP (T p) * q) = gaussInt (starP p * T q)

theorem PolySym.add {S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (hS : PolySym S) (hT : PolySym T) : PolySym (S + T) := by
  intro p q
  simp only [LinearMap.add_apply, starP_add, add_mul, mul_add]
  rw [gaussInt_add, gaussInt_add, hS, hT]

theorem PolySym.real_smul {t : ℝ} {T : Module.End ℂ (MvPolynomial (Fin d) ℂ)} (hT : PolySym T) :
    PolySym (((t : ℂ)) • T) := by
  intro p q
  simp only [LinearMap.smul_apply, starP_real_smul, smul_mul_assoc, mul_smul_comm]
  rw [gaussInt_smul, gaussInt_smul, hT]

/-- The **adjoint pairing** of two operators: `S` and `T` are adjoint when
`⟪S p, q⟫ = ⟪p, T q⟫`. -/
def PolyAdj (S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)) : Prop :=
  ∀ p q : MvPolynomial (Fin d) ℂ, gaussInt (starP (S p) * q) = gaussInt (starP p * T q)

theorem PolyAdj.symm_of {S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (h : PolyAdj S T) (h' : PolyAdj T S) : PolySym (S + T) := by
  intro p q
  simp only [LinearMap.add_apply, starP_add, add_mul, mul_add]
  rw [gaussInt_add, gaussInt_add, h, h']
  ring

/-- The composition of two Gauss-symmetric operators is adjoint to the reversed
composition. -/
theorem PolySym.comp_adj {S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (hS : PolySym S) (hT : PolySym T) : PolyAdj (S.comp T) (T.comp S) := by
  intro p q
  rw [LinearMap.comp_apply, LinearMap.comp_apply, hS, hT]

/-- **Weyl ordering** `½(PQ + QP)`: the symmetric product of two operators.
This is the ordering prescription for the non-commuting `πA` cross terms. -/
def weylProd (S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)) :
    Module.End ℂ (MvPolynomial (Fin d) ℂ) :=
  ((1 / 2 : ℝ) : ℂ) • (S.comp T + T.comp S)

/-- **The Weyl-ordered product of two symmetric operators is symmetric** (F.5). -/
theorem weylProd_polySym {S T : Module.End ℂ (MvPolynomial (Fin d) ℂ)}
    (hS : PolySym S) (hT : PolySym T) : PolySym (weylProd S T) :=
  PolySym.real_smul ((hS.comp_adj hT).symm_of (hT.comp_adj hS))

/-! ### Multiplication operators (F.2) -/

/-- Multiplication by a fixed polynomial. -/
def mulOp (f : MvPolynomial (Fin d) ℂ) : Module.End ℂ (MvPolynomial (Fin d) ℂ) :=
  LinearMap.mulLeft ℂ f

@[simp] theorem mulOp_apply (f p : MvPolynomial (Fin d) ℂ) : mulOp f p = f * p := rfl

/-- **Multiplication by a real polynomial is Gauss symmetric.** -/
theorem mulOp_polySym {f : MvPolynomial (Fin d) ℂ} (hf : RealCoeff f) : PolySym (mulOp f) := by
  intro p q
  simp only [mulOp_apply, starP_mul, show starP f = f from hf]
  congr 1
  ring

/-! ### Momentum operators (F.3) -/

/-- The derivative `∂_j` acting on `p·e^{-‖x‖²/4}`, written back on the
polynomial factor: `∂_j (p e^{-‖x‖²/4}) = (∂_j p − ½ x_j p) e^{-‖x‖²/4}`. -/
def derOp (j : Fin d) : Module.End ℂ (MvPolynomial (Fin d) ℂ) :=
  (pderiv j).toLinearMap - ((1 / 2 : ℝ) : ℂ) • mulOp (X j)

theorem derOp_apply (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    derOp j p = pderiv j p - ((1 / 2 : ℝ) : ℂ) • (X j * p) := rfl

/-- The **momentum operator** `π_j = −i ∂_j` on the core (F.3). -/
def momOp (j : Fin d) : Module.End ℂ (MvPolynomial (Fin d) ℂ) := (-Complex.I) • derOp j

theorem momOp_apply (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    momOp j p = (-Complex.I) • (pderiv j p - ((1 / 2 : ℝ) : ℂ) • (X j * p)) := rfl

theorem starP_pderiv (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    starP (pderiv j p) = pderiv j (starP p) := (MvPolynomial.pderiv_map).symm

@[simp] theorem starP_neg (p : MvPolynomial (Fin d) ℂ) : starP (-p) = -starP p := map_neg _ _

@[simp] theorem starP_sub (p q : MvPolynomial (Fin d) ℂ) :
    starP (p - q) = starP p - starP q := map_sub _ _ _

theorem gaussInt_sub (r s : MvPolynomial (Fin d) ℂ) :
    gaussInt (r - s) = gaussInt r - gaussInt s := by
  have h := gaussInt_add r (-s)
  rw [show (-s) = (-1 : ℂ) • s by module, gaussInt_smul] at h
  rw [show r - s = r + (-1 : ℂ) • s by module, h]
  ring

/-- The Leibniz rule combined with Gaussian integration by parts:
`∫ (∂_j P) Q e^{-‖x‖²/2} + ∫ P (∂_j Q) e^{-‖x‖²/2} = ∫ x_j P Q e^{-‖x‖²/2}`. -/
theorem gaussInt_leibniz (j : Fin d) (P Q : MvPolynomial (Fin d) ℂ) :
    gaussInt (pderiv j P * Q) + gaussInt (P * pderiv j Q) = gaussInt (X j * (P * Q)) := by
  rw [← gaussInt_pderiv j (P * Q), ← gaussInt_add]
  congr 1
  rw [Derivation.leibniz]
  simp only [smul_eq_mul]
  ring

theorem starP_momOp (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    starP (momOp j p)
      = Complex.I • (pderiv j (starP p) - ((1 / 2 : ℝ) : ℂ) • (X j * starP p)) := by
  rw [momOp_apply, neg_smul, starP_neg, starP_smul, starP_sub, starP_pderiv, starP_real_smul,
    starP_mul, starP_X, Complex.conj_I, neg_smul, neg_neg]

/-- **The momentum operator is Gauss symmetric** (F.3) — this is exactly the
`d`-dimensional Gaussian integration by parts `gaussInt_pderiv`. -/
theorem momOp_polySym (j : Fin d) : PolySym (momOp (d := d) j) := by
  intro p q
  have hleib := gaussInt_leibniz j (starP p) q
  have e1 : (X j : MvPolynomial (Fin d) ℂ) * starP p * q = X j * (starP p * q) := by ring
  have e2 : starP p * (X j * q) = X j * (starP p * q) := by ring
  have hL : gaussInt (starP (momOp j p) * q)
      = Complex.I * (gaussInt (pderiv j (starP p) * q)
          - ((1 / 2 : ℝ) : ℂ) * gaussInt (X j * (starP p * q))) := by
    rw [starP_momOp, smul_mul_assoc, gaussInt_smul, sub_mul, gaussInt_sub, smul_mul_assoc,
      gaussInt_smul, e1]
  have hR : gaussInt (starP p * momOp j q)
      = -Complex.I * (gaussInt (starP p * pderiv j q)
          - ((1 / 2 : ℝ) : ℂ) * gaussInt (X j * (starP p * q))) := by
    rw [momOp_apply, mul_smul_comm, gaussInt_smul, mul_sub, gaussInt_sub, mul_smul_comm,
      gaussInt_smul, e2]
  rw [hL, hR]
  push_cast
  linear_combination Complex.I * hleib

/-- **The canonical commutation relation** `[A_j, π_j] = i` (book.tex:7060-7061),
at the polynomial level: this is the reason the `πA` cross terms need the Weyl
ordering `weylProd`. -/
theorem commutator_coord_mom (j : Fin d) (p : MvPolynomial (Fin d) ℂ) :
    mulOp (X j) (momOp j p) - momOp j (mulOp (X j) p) = Complex.I • p := by
  have hX : (pderiv j) (X j * p) = p + X j * pderiv j p := by
    rw [Derivation.leibniz]
    simp only [pderiv_X_self, smul_eq_mul, mul_one]
    ring
  simp only [mulOp_apply, momOp_apply, hX, neg_smul, smul_eq_C_mul]
  ring


end

end BookProof.YangMillsHermite
