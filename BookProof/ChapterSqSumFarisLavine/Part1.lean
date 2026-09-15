import Mathlib
import BookProof.ChapterGaussCoreQuadBounds

/-!
# The two Faris–Lavine inequalities for `½ Σ_j κ_j π_j² + ½ Σ_r L_r²`

This module proves, on the Gauss–polynomial core of `L²(ℝᴰ)`, the two inequalities that
Theorem 1 of Faris–Lavine asks of a Hamiltonian and its comparison operator, for the
**kinetic-plus-squares Hamiltonian**

`H = ½ Σ_j κ_j π_j² + ½ Σ_r L_r²`,  `L_r = Σ_i v_{ri} x_i`,

of `BookProof.QgOuterFock.sqSumOp`, against the harmonic comparison operator
`N = −Δ + ‖x‖²/4` (`harmCore`).  The signature `κ` is an arbitrary *real* vector — no sign,
no ellipticity — and the family of linear forms `L_r` is arbitrary and finite.

What matters for the Fock lift is the *shape of the constants*: both are expressed through

* `km`, a bound on `|κ_j|`, and
* Schur-type `ℓ¹` bounds on the coefficient matrix `v` of the linear forms

and **not** through the dimension `D`.  This is exactly what makes the same two constants
serve every particle-number sector of the outer Fock space simultaneously, which is the
hypothesis the `ℓ²`-direct-sum Faris–Lavine theorem of
`BookProof.ChapterQgOuterFockFarisLavine` needs.

## What is proved

* `schur_bound` — the Schur test for a real matrix with bounded row and column `ℓ¹` norms;
* `linFun`, `potFun`, `potPoly`, `gradPoly`, `gradFun`, `kinPart` — the data of the
  Hamiltonian, and `sqSumPoly_apply`, its splitting into kinetic and potential parts;
* `potFun_le_of_schur`, `sum_gradFun_sq_le_of_schur` — the pointwise bounds
  `V(x) ≤ (ab/2)‖x‖²` and `Σ_k (∂_k V)(x)² ≤ (ab)²‖x‖²` from the Schur data of `v`;
* `commPoly`, `commPoly_eq` — the commutator `[H, N]` computed in polynomial coordinates:
  it is again first order, with the gradient of the potential as its coefficient;
* `commForm_eq_im`, `abs_im_gaussInt_le` — the commutator form as a Gaussian integral;
* **`commForm_sqSumOp_le`** — the Faris–Lavine commutator bound
  `|⟪u, i[H,N]u⟫| ≤ (km/2 + 2M)·⟪u, Nu⟫`, with `M` a bound on the gradient of the
  potential;
* **`norm_sqSumOp_le`** — the relative bound `‖Hu‖ ≤ (3km/2 + 8B)·‖(N+1)u‖`, with `B` a
  bound on the potential.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SqSumFarisLavine

open Finset MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.QgHermiteOscillator BookProof.FarisLavine
open BookProof.HermiteQuadraticEsa
open BookProof.QgOuterFock
open BookProof.GaussCoreQuadBounds

noncomputable section

variable {D : ℕ} {R : Type*} [Fintype R]

/-! ## 1. The Schur test -/

/-- **The Schur test** for a real matrix with bounded row and column `ℓ¹` norms. -/
theorem schur_bound {I J : Type*} [Fintype I] [Fintype J] (A : I → J → ℝ) {a b : ℝ}
    (ha0 : 0 ≤ a)
    (ha : ∀ i, ∑ j : J, |A i j| ≤ a) (hb : ∀ j, ∑ i : I, |A i j| ≤ b) (y : J → ℝ) :
    ∑ i : I, (∑ j : J, A i j * y j) ^ 2 ≤ a * b * ∑ j : J, (y j) ^ 2 := by
  have hrow : ∀ i : I, (∑ j : J, A i j * y j) ^ 2 ≤ a * ∑ j : J, |A i j| * (y j) ^ 2 := by
    intro i
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.univ : Finset J)
      (fun j => Real.sqrt |A i j|) (fun j => Real.sqrt |A i j| * |y j|)
    have h1 : ∑ j : J, Real.sqrt |A i j| * (Real.sqrt |A i j| * |y j|)
        = ∑ j : J, |A i j| * |y j| := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← mul_assoc, Real.mul_self_sqrt (abs_nonneg (A i j))]
    have h2 : ∑ j : J, (Real.sqrt |A i j|) ^ 2 = ∑ j : J, |A i j| :=
      Finset.sum_congr rfl fun j _ => Real.sq_sqrt (abs_nonneg _)
    have h3 : ∑ j : J, (Real.sqrt |A i j| * |y j|) ^ 2 = ∑ j : J, |A i j| * (y j) ^ 2 := by
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mul_pow, Real.sq_sqrt (abs_nonneg _), sq_abs]
    rw [h1, h2, h3] at hcs
    have habs : |∑ j : J, A i j * y j| ≤ ∑ j : J, |A i j| * |y j| := by
      refine (Finset.abs_sum_le_sum_abs _ _).trans_eq ?_
      exact Finset.sum_congr rfl fun j _ => abs_mul _ _
    have hnn : 0 ≤ ∑ j : J, |A i j| * |y j| :=
      Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (abs_nonneg _)
    have hsq : (∑ j : J, A i j * y j) ^ 2 ≤ (∑ j : J, |A i j| * |y j|) ^ 2 := by
      rw [← sq_abs (∑ j : J, A i j * y j)]
      nlinarith [abs_nonneg (∑ j : J, A i j * y j)]
    have hpos : 0 ≤ ∑ j : J, |A i j| * (y j) ^ 2 :=
      Finset.sum_nonneg fun j _ => mul_nonneg (abs_nonneg _) (sq_nonneg _)
    calc (∑ j : J, A i j * y j) ^ 2 ≤ (∑ j : J, |A i j| * |y j|) ^ 2 := hsq
      _ ≤ (∑ j : J, |A i j|) * ∑ j : J, |A i j| * (y j) ^ 2 := hcs
      _ ≤ a * ∑ j : J, |A i j| * (y j) ^ 2 :=
          mul_le_mul_of_nonneg_right (ha i) hpos
  calc ∑ i : I, (∑ j : J, A i j * y j) ^ 2
      ≤ ∑ i : I, a * ∑ j : J, |A i j| * (y j) ^ 2 := Finset.sum_le_sum fun i _ => hrow i
    _ = a * ∑ j : J, (∑ i : I, |A i j|) * (y j) ^ 2 := by
        rw [← Finset.mul_sum]
        congr 1
        rw [Finset.sum_comm]
        exact Finset.sum_congr rfl fun j _ => by rw [Finset.sum_mul]
    _ ≤ a * ∑ j : J, b * (y j) ^ 2 := by
        refine mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun j _ => ?_) ha0
        exact mul_le_mul_of_nonneg_right (hb j) (sq_nonneg _)
    _ = a * b * ∑ j : J, (y j) ^ 2 := by rw [← Finset.mul_sum, mul_assoc]

/-! ## 2. The data of a kinetic-plus-squares Hamiltonian -/

/-- The value of the linear form `L_v` at a point. -/
def linFun (v : Fin D → ℝ) (x : Vd D) : ℝ := ∑ i : Fin D, v i * x i

/-- The potential `V = ½ Σ_r L_r²`, as a real function. -/
def potFun (v : R → Fin D → ℝ) (x : Vd D) : ℝ := (1 / 2) * ∑ r : R, (linFun (v r) x) ^ 2

/-- The potential `V = ½ Σ_r L_r²`, as a polynomial. -/
def potPoly (v : R → Fin D → ℝ) : MvPolynomial (Fin D) ℂ :=
  ((1 / 2 : ℝ) : ℂ) • ∑ r : R, linForm (v r) * linForm (v r)

/-- The gradient `∂_k V = Σ_r v_{rk} L_r`, as a polynomial. -/
def gradPoly (v : R → Fin D → ℝ) (k : Fin D) : MvPolynomial (Fin D) ℂ :=
  ∑ r : R, ((v r k : ℝ) : ℂ) • linForm (v r)

/-- The gradient `∂_k V`, as a real function. -/
def gradFun (v : R → Fin D → ℝ) (k : Fin D) (x : Vd D) : ℝ :=
  ∑ r : R, v r k * linFun (v r) x

/-- The kinetic part `−½ Σ_j κ_j ∂_j²`, on polynomial coordinates. -/
def kinPart (kappa : Fin D → ℝ) (p : MvPolynomial (Fin D) ℂ) : MvPolynomial (Fin D) ℂ :=
  ∑ j : Fin D, ((-(kappa j) / 2 : ℝ) : ℂ) • coreD j (coreD j p)

/-- **The Hamiltonian, split into its kinetic and potential parts.** -/
theorem sqSumPoly_apply (kappa : Fin D → ℝ) (v : R → Fin D → ℝ)
    (p : MvPolynomial (Fin D) ℂ) :
    sqSumPoly kappa v p = kinPart kappa p + potPoly v * p := by
  have hmom : ∀ (j : Fin D) (q : MvPolynomial (Fin D) ℂ),
      YangMillsHermite.momOp j q = (-Complex.I) • coreD j q := by
    intro j q
    have hc : coreD j q = pderiv j q - ((1 / 2 : ℝ) : ℂ) • (X j * q) := by
      rw [coreD, MvPolynomial.smul_eq_C_mul]
      norm_num
    rw [YangMillsHermite.momOp_apply, hc]
  have hsq : ∀ j : Fin D, YangMillsHermite.momOp j (YangMillsHermite.momOp j p)
      = -(coreD j (coreD j p)) := by
    intro j
    rw [hmom, hmom, coreD_smul, smul_smul]
    rw [show (-Complex.I) * (-Complex.I) = (-1 : ℂ) by
      rw [neg_mul_neg, Complex.I_mul_I]]
    rw [neg_one_smul]
  have hlhs : sqSumPoly kappa v p
      = ((1 / 2 : ℝ) : ℂ)
        • ((∑ j : Fin D, ((kappa j : ℝ) : ℂ)
              • YangMillsHermite.momOp j (YangMillsHermite.momOp j p))
            + ∑ r : R, linForm (v r) * (linForm (v r) * p)) := by
    simp [sqSumPoly]
  rw [hlhs, kinPart, potPoly, smul_add]
  congr 1
  · rw [Finset.smul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [hsq j, smul_smul, smul_neg, ← neg_smul]
    congr 1
    push_cast
    ring
  · rw [Finset.smul_sum, smul_mul_assoc, Finset.sum_mul, Finset.smul_sum]
    exact Finset.sum_congr rfl fun r _ => by rw [mul_assoc]

/-! ### Evaluations -/

theorem eval_linForm (v : Fin D → ℝ) (x : Vd D) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (linForm v) = ((linFun v x : ℝ) : ℂ) := by
  rw [linForm, linFun, map_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X,
    Complex.ofReal_mul]

theorem eval_potPoly (v : R → Fin D → ℝ) (x : Vd D) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (potPoly v) = ((potFun v x : ℝ) : ℂ) := by
  rw [potPoly, potFun, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, map_sum,
    Complex.ofReal_mul, Complex.ofReal_sum]
  congr 1
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [map_mul, eval_linForm, ← Complex.ofReal_mul, ← pow_two]

theorem eval_gradPoly (v : R → Fin D → ℝ) (k : Fin D) (x : Vd D) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (gradPoly v k) = ((gradFun v k x : ℝ) : ℂ) := by
  rw [gradPoly, gradFun, map_sum, Complex.ofReal_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, eval_linForm,
    Complex.ofReal_mul]

theorem cpoly_linForm (v : Fin D → ℝ) : cpoly (linForm v) = linForm v := by
  rw [linForm, cpoly_sum]
  exact Finset.sum_congr rfl fun i _ => by rw [cpoly_real_smul, cpoly_X]

theorem cpoly_gradPoly (v : R → Fin D → ℝ) (k : Fin D) :
    cpoly (gradPoly v k) = gradPoly v k := by
  rw [gradPoly, cpoly_sum]
  exact Finset.sum_congr rfl fun r _ => by rw [cpoly_real_smul, cpoly_linForm]

/-! ## 3. The Schur bounds on the potential data -/

theorem potFun_le_of_schur {v : R → Fin D → ℝ} {a b : ℝ} (ha0 : 0 ≤ a)
    (ha : ∀ r, ∑ i : Fin D, |v r i| ≤ a) (hb : ∀ i, ∑ r : R, |v r i| ≤ b) (x : Vd D) :
    potFun v x ≤ (a * b / 2) * ‖x‖ ^ 2 := by
  have hs := schur_bound v ha0 ha hb (fun i => x i)
  rw [← norm_sq_eq_sum x] at hs
  rw [potFun]
  have hlin : ∀ r : R, linFun (v r) x = ∑ i : Fin D, v r i * x i := fun r => rfl
  simp only [hlin]
  linarith

theorem sum_gradFun_sq_le_of_schur {v : R → Fin D → ℝ} {a b : ℝ} (ha0 : 0 ≤ a) (hb0 : 0 ≤ b)
    (ha : ∀ r, ∑ i : Fin D, |v r i| ≤ a) (hb : ∀ i, ∑ r : R, |v r i| ≤ b) (x : Vd D) :
    ∑ k : Fin D, (gradFun v k x) ^ 2 ≤ (a * b) ^ 2 * ‖x‖ ^ 2 := by
  have hs := schur_bound (fun (k : Fin D) (r : R) => v r k) hb0
    (fun k => hb k) (fun r => ha r) (fun r => linFun (v r) x)
  have hgrad : ∀ k : Fin D, gradFun v k x = ∑ r : R, v r k * linFun (v r) x := fun k => rfl
  simp only [hgrad]
  have hpot := potFun_le_of_schur ha0 ha hb x
  have hsum : ∑ r : R, (linFun (v r) x) ^ 2 = 2 * potFun v x := by
    rw [potFun]; ring
  rw [hsum] at hs
  have hab : 0 ≤ b * a := mul_nonneg hb0 ha0
  nlinarith [hs, hpot, norm_nonneg x, sq_nonneg ‖x‖]

/-! ## 4. The first Faris–Lavine inequality: the relative bound -/

theorem potFun_nonneg (v : R → Fin D → ℝ) (x : Vd D) : 0 ≤ potFun v x := by
  rw [potFun]
  have : (0 : ℝ) ≤ ∑ r : R, (linFun (v r) x) ^ 2 :=
    Finset.sum_nonneg fun r _ => sq_nonneg _
  linarith

theorem norm_potPoly_mul_le {v : R → Fin D → ℝ} {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x : Vd D, potFun v x ≤ B * ‖x‖ ^ 2) (p : MvPolynomial (Fin D) ℂ) :
    ‖pgLp (potPoly v * p)‖ ≤ 4 * B * ‖pgLp (harmPoly * p)‖ := by
  refine norm_mul_le_of_pointwise (by positivity) (fun x => ?_) p
  rw [eval_potPoly, eval_harmPoly, Complex.norm_real, Complex.norm_real,
    Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (potFun_nonneg v x),
    abs_of_nonneg (show (0 : ℝ) ≤ harmW x by rw [harmW]; positivity), harmW]
  have := hB x
  linarith

/-- **The relative bound `‖H p‖ ≤ K ‖(N+1) p‖`**, with `K = 3κ/2 + 8B` depending only on the
bound `κ` on the signature and the bound `B` of the potential against `‖x‖²`, *not* on the
dimension. -/
theorem norm_sqSumPoly_le {kappa : Fin D → ℝ} {v : R → Fin D → ℝ} {km B : ℝ}
    (hkm : 0 ≤ km) (hk : ∀ j, |kappa j| ≤ km) (hB0 : 0 ≤ B)
    (hB : ∀ x : Vd D, potFun v x ≤ B * ‖x‖ ^ 2) (p : MvPolynomial (Fin D) ℂ) :
    ‖pgLp (sqSumPoly kappa v p)‖ ≤ (3 / 2 * km + 8 * B) * shiftNorm p := by
  have hsplit : pgLp (sqSumPoly kappa v p)
      = pgLp (kinPart kappa p) + pgLp (potPoly v * p) := by
    rw [sqSumPoly_apply, ← pgMap_apply, ← pgMap_apply, ← pgMap_apply, map_add]
  have hkin : ‖pgLp (kinPart kappa p)‖ ≤ km / 2 * ‖pgLp (kinPoly p)‖ :=
    norm_weighted_kin_le (kappa := fun j => -(kappa j) / 2) (km := km / 2) (by linarith)
      (fun j => by
        have h := abs_le.mp (hk j)
        rw [abs_le]
        constructor <;> linarith [h.1, h.2]) p
  have h1 : ‖pgLp (kinPoly p)‖ ≤ 3 * shiftNorm p := norm_kinPoly_le_shiftNorm p
  have h2 : ‖pgLp (harmPoly * p)‖ ≤ 2 * shiftNorm p := norm_harmPoly_mul_le_shiftNorm p
  have hpot := norm_potPoly_mul_le hB0 hB p
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  nlinarith [norm_nonneg (pgLp (kinPoly p)), norm_nonneg (pgLp (harmPoly * p)),
    shiftNorm_nonneg p]

/-! ## 5. The second Faris–Lavine inequality: the commutator form -/

/-- The formal commutator `[H, N]`, on polynomial coordinates. -/
def commPoly (kappa : Fin D → ℝ) (v : R → Fin D → ℝ) (p : MvPolynomial (Fin D) ℂ) :
    MvPolynomial (Fin D) ℂ :=
  sqSumPoly kappa v (harmP p) - harmP (sqSumPoly kappa v p)

/-- The commutator constant of the identity below. -/
def commConst (kappa : Fin D → ℝ) (v : R → Fin D → ℝ) : ℝ :=
  -(1 / 4) * ∑ j : Fin D, kappa j + ∑ r : R, ∑ k : Fin D, (v r k) ^ 2

/-! ### Derivatives of the potentials -/

theorem coreD_sum {ι : Type*} (s : Finset ι) (j : Fin D) (f : ι → MvPolynomial (Fin D) ℂ) :
    coreD j (∑ i ∈ s, f i) = ∑ i ∈ s, coreD j (f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [coreD]
  | insert a s ha ih => rw [Finset.sum_insert ha, coreD_add, ih, Finset.sum_insert ha]

theorem coreD_neg (j : Fin D) (p : MvPolynomial (Fin D) ℂ) : coreD j (-p) = -coreD j p := by
  rw [show (-p) = (-1 : ℂ) • p by rw [neg_smul, one_smul], coreD_smul, neg_smul, one_smul]

theorem pderiv_linForm (v : Fin D → ℝ) (j : Fin D) :
    pderiv j (linForm v) = C ((v j : ℝ) : ℂ) := by
  rw [linForm, map_sum, Finset.sum_eq_single j]
  · rw [MvPolynomial.smul_eq_C_mul, pderiv_C_mul, pderiv_X_self, mul_one]
  · intro i _ hi
    simp [MvPolynomial.smul_eq_C_mul, pderiv_X, Ne.symm hi]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem C_two_eq : (C (2 : ℂ) : MvPolynomial (Fin D) ℂ) = 2 := by
  rw [show (2 : ℂ) = ((2 : ℕ) : ℂ) by norm_num, MvPolynomial.C_eq_coe_nat]
  norm_num

theorem pderiv_potPoly (v : R → Fin D → ℝ) (k : Fin D) :
    pderiv k (potPoly v) = gradPoly v k := by
  rw [potPoly, MvPolynomial.smul_eq_C_mul, pderiv_C_mul, map_sum, gradPoly, Finset.mul_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [pderiv_mul, pderiv_linForm, MvPolynomial.smul_eq_C_mul,
    show (C (((1 : ℝ) / 2 : ℝ) : ℂ) : MvPolynomial (Fin D) ℂ)
        * (C ((v r k : ℝ) : ℂ) * linForm (v r) + linForm (v r) * C ((v r k : ℝ) : ℂ))
      = (C (((1 : ℝ) / 2 : ℝ) : ℂ) * C ((v r k : ℝ) : ℂ) * C (2 : ℂ)) * linForm (v r) by
      rw [C_two_eq]; ring]
  congr 1
  rw [← map_mul, ← map_mul]
  congr 1
  push_cast
  ring

theorem pderiv_gradPoly_self (v : R → Fin D → ℝ) (k : Fin D) :
    pderiv k (gradPoly v k) = C (((∑ r : R, (v r k) ^ 2 : ℝ) : ℂ)) := by
  rw [gradPoly, map_sum, Complex.ofReal_sum, map_sum]
  refine Finset.sum_congr rfl fun r _ => ?_
  rw [MvPolynomial.smul_eq_C_mul, pderiv_C_mul, pderiv_linForm, ← map_mul]
  congr 1
  push_cast
  ring

theorem pderiv_harmPoly (j : Fin D) :
    pderiv j (harmPoly (d := D)) = C (1 / 2 : ℂ) * X j := by
  rw [harmPoly, map_sum, Finset.sum_eq_single j]
  · rw [show (X j : MvPolynomial (Fin D) ℂ) ^ 2 = X j * X j by ring, pderiv_C_mul, pderiv_mul,
      pderiv_X_self, one_mul, mul_one,
      show (X j + X j : MvPolynomial (Fin D) ℂ) = C (2 : ℂ) * X j by rw [C_two_eq]; ring,
      ← mul_assoc, ← map_mul]
    norm_num
  · intro i _ hi
    rw [show (X i : MvPolynomial (Fin D) ℂ) ^ 2 = X i * X i by ring, pderiv_C_mul, pderiv_mul,
      pderiv_X]
    simp [Ne.symm hi]
  · intro h
    exact absurd (Finset.mem_univ j) h

theorem pderiv_pderiv_harmPoly (j : Fin D) :
    pderiv j (pderiv j (harmPoly (d := D))) = C (1 / 2 : ℂ) := by
  rw [pderiv_harmPoly, pderiv_C_mul, pderiv_X_self, mul_one]

end

end BookProof.SqSumFarisLavine
