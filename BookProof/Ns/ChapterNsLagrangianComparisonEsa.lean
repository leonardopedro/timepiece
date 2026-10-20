import BookProof.Toolbox.ChapterKvnKatoPoly
import BookProof.Ns.ChapterNsLagrangianDetFarisLavine

/-!
# Essential self-adjointness of the Lagrangian Koopman comparison operator `N_L = H_L² + E`

This chapter discharges the standing hypothesis of
`NsLagrangianDetFL.lagKoopman_esa_of_comparison_esa`: the Faris–Lavine comparison operator
`N_L = H_L² + E` (`NsLagrangianDetFL.lagComparison`) of the Koopman generator `H_L` of the
degree-five Galerkin Lagrangian Navier–Stokes flow with the determinant penalty is **essentially
self-adjoint on the Gauss–polynomial core** of `L²(ℝ^{PIdx K})`.

The proof applies `KvnKato.lyapunovComparison_esa_poly`, which needs a *proper* polynomial
Lyapunov function `P` (`‖y‖ ≤ P(y)`, `|F·∇P| ≤ c₀ P`).  The energy `E = 1 + ½|v|² + V_κ(ξ)` is not
proper (the penalty `V_κ` vanishes on the unbounded incompressible set), so we take

```
P = E + ½ |ξ|² = 1 + ½|v|² + ½|ξ|² + V_κ(ξ),
```

for which `F·∇P = −ν Σ |k|² v² + ξ·v` (`lagLyapFlux_eq`), hence `|F·∇P| ≤ (2νΛ + 1) P`, and
`P ≥ 1 + ½‖y‖² ≥ ‖y‖`.

## Main results

* `lagComparison_esa` — **`N_L = H_L² + E` is essentially self-adjoint on the core**,
  unconditionally, for every finite set of wave vectors, `ν ≥ 0`, `κ ≥ 0`;
* `lagKoopman_esa` — consequently (Faris–Lavine) the Lagrangian Koopman generator `H_L` itself
  is essentially self-adjoint on the core.
-/

namespace BookProof.NsLagrangianComparisonEsa

open MvPolynomial
open BookProof.HermiteProductCore BookProof.YangMillsHermite BookProof.FarisLavine
open BookProof.NsKoopman BookProof.KoopmanLyapunov BookProof.NsLagrangianDet
open BookProof.NsLagrangianDetFL

noncomputable section

variable {K : Type*} [Fintype K] (S : LagNsData K)

/-- The squared displacement `Σ ξ²`. -/
def dispSq : MvPolynomial (PIdx K) ℂ :=
  ∑ j : DIdx K, (X (false, j) : MvPolynomial (PIdx K) ℂ) * X (false, j)

/-- The proper Lyapunov polynomial `P = E + ½ |ξ|²`. -/
def lagLyap : MvPolynomial (PIdx K) ℂ := lagEnergy S + ((1 / 2 : ℝ) : ℂ) • dispSq

theorem pderiv_disp_dispSq (j : DIdx K) :
    pderiv ((false, j) : PIdx K) (dispSq (K := K)) = (2 : ℂ) • X (false, j) := by
  classical
  rw [dispSq, map_sum, Finset.sum_eq_single j (fun l _ hl => by
    rw [pderiv_mul, pderiv_X_of_ne (by simpa using hl)]
    simp) (fun h => absurd (Finset.mem_univ j) h)]
  rw [pderiv_mul, pderiv_X_self, one_mul, mul_one]
  module

theorem pderiv_vel_dispSq (j : DIdx K) :
    pderiv ((true, j) : PIdx K) (dispSq (K := K)) = 0 := by
  classical
  simp [dispSq, pderiv_X]

/-- The derivative of `½|ξ|²` along the flow is `ξ·v`. -/
theorem dispSq_flux :
    ∑ i, lagDrift S i * pderiv i (((1 / 2 : ℝ) : ℂ) • dispSq (K := K))
      = ∑ j : DIdx K, (X (true, j) : MvPolynomial (PIdx K) ℂ) * X (false, j) := by
  rw [Fintype.sum_prod_type, Fintype.sum_bool]
  simp only [Derivation.map_smul, pderiv_disp_dispSq, pderiv_vel_dispSq, smul_zero, mul_zero,
    Finset.sum_const_zero, lagDrift, smul_smul]
  simp

/-- **The flux of the Lyapunov polynomial**: `F·∇P = −ν Σ |k|² v² + ξ·v`. -/
theorem lagLyapFlux_eq :
    ∑ i, lagDrift S i * pderiv i (lagLyap S)
      = lagFlux S + ∑ j : DIdx K, (X (true, j) : MvPolynomial (PIdx K) ℂ) * X (false, j) := by
  rw [← lagFlux_eq, ← dispSq_flux, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [lagLyap, map_add, mul_add]

theorem eval_lagLyap_re (z : PIdx K → ℝ) :
    (MvPolynomial.eval (fun i => ((z i : ℝ) : ℂ)) (lagLyap S)).re
      = (MvPolynomial.eval (fun i => ((z i : ℝ) : ℂ)) (lagEnergy S)).re
        + (1 / 2) * ∑ j : DIdx K, z (false, j) ^ 2 := by
  rw [lagLyap, map_add, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C, dispSq,
    map_sum, Complex.add_re, Complex.re_ofReal_mul, Complex.re_sum]
  congr 2
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_mul, MvPolynomial.eval_X, ← Complex.ofReal_mul, Complex.ofReal_re]
  ring

theorem eval_lagLyap_ge (z : PIdx K → ℝ) :
    1 + (1 / 2) * (∑ j : DIdx K, z (true, j) ^ 2 + ∑ j : DIdx K, z (false, j) ^ 2)
      ≤ (MvPolynomial.eval (fun i => ((z i : ℝ) : ℂ)) (lagLyap S)).re := by
  rw [eval_lagLyap_re]
  have := eval_lagEnergy_ge S z
  linarith

theorem eval_lagEnergy_le_lagLyap (z : PIdx K → ℝ) :
    (MvPolynomial.eval (fun i => ((z i : ℝ) : ℂ)) (lagEnergy S)).re
      ≤ (MvPolynomial.eval (fun i => ((z i : ℝ) : ℂ)) (lagLyap S)).re := by
  rw [eval_lagLyap_re]
  have : 0 ≤ ∑ j : DIdx K, z (false, j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
  linarith

/-- The pointwise Lyapunov bound `|F·∇P| ≤ (2νΛ + 1) P`. -/
theorem abs_eval_lagLyapFlux_le (z : PIdx K → ℝ) :
    |(MvPolynomial.eval (fun i => ((z i : ℝ) : ℂ))
        (∑ i, lagDrift S i * pderiv i (lagLyap S))).re|
      ≤ (2 * S.nu * ∑ j, lam S j + 1)
        * (MvPolynomial.eval (fun i => ((z i : ℝ) : ℂ)) (lagLyap S)).re := by
  rw [lagLyapFlux_eq, map_add, Complex.add_re]
  have h1 := abs_eval_lagFlux_le S z
  have h2 := eval_lagEnergy_le_lagLyap S z
  have h3 := eval_lagLyap_ge S z
  have hc : 0 ≤ 2 * S.nu * ∑ j, lam S j :=
    mul_nonneg (by linarith [S.nu_nonneg]) (Finset.sum_nonneg fun j _ => lam_nonneg S j)
  have hcross : (MvPolynomial.eval (fun i => ((z i : ℝ) : ℂ))
      (∑ j : DIdx K, (X (true, j) : MvPolynomial (PIdx K) ℂ) * X (false, j))).re
      = ∑ j : DIdx K, z (true, j) * z (false, j) := by
    rw [map_sum, Complex.re_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_mul, MvPolynomial.eval_X, MvPolynomial.eval_X, ← Complex.ofReal_mul,
      Complex.ofReal_re]
  rw [hcross]
  have hxy : |∑ j : DIdx K, z (true, j) * z (false, j)|
      ≤ (1 / 2) * (∑ j : DIdx K, z (true, j) ^ 2 + ∑ j : DIdx K, z (false, j) ^ 2) := by
    rw [abs_le]
    constructor
    · have : ∀ j : DIdx K, -((1 / 2) * (z (true, j) ^ 2 + z (false, j) ^ 2))
          ≤ z (true, j) * z (false, j) := fun j => by nlinarith [sq_nonneg (z (true, j) + z (false, j))]
      have := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => this j
      rw [Finset.sum_neg_distrib, ← Finset.mul_sum, Finset.sum_add_distrib] at this
      linarith
    · have : ∀ j : DIdx K, z (true, j) * z (false, j)
          ≤ (1 / 2) * (z (true, j) ^ 2 + z (false, j) ^ 2) := fun j => by
        nlinarith [sq_nonneg (z (true, j) - z (false, j))]
      have := Finset.sum_le_sum fun j (_ : j ∈ Finset.univ) => this j
      rw [← Finset.mul_sum, Finset.sum_add_distrib] at this
      linarith
  have hE0 : 0 ≤ (MvPolynomial.eval (fun i => ((z i : ℝ) : ℂ)) (lagEnergy S)).re := by
    have := eval_lagEnergy_ge S z
    have : 0 ≤ ∑ j : DIdx K, z (true, j) ^ 2 := Finset.sum_nonneg fun j _ => sq_nonneg _
    linarith
  calc _ ≤ |(MvPolynomial.eval (fun i => ((z i : ℝ) : ℂ)) (lagFlux S)).re|
        + |∑ j : DIdx K, z (true, j) * z (false, j)| := abs_add_le _ _
    _ ≤ _ := by nlinarith [mul_le_mul_of_nonneg_left h2 hc]

/-! ## Transport to the coordinates `Fin (lagDim K)` -/

/-- The Lyapunov polynomial in the coordinates `Fin (lagDim K)`. -/
def lagP : MvPolynomial (Fin (lagDim K)) ℂ := rename lagEquiv (lagLyap S)

theorem lagG_lyapFlux :
    ∑ i, lagG S i * pderiv i (lagP S)
      = rename lagEquiv (∑ i, lagDrift S i * pderiv i (lagLyap S)) := by
  rw [map_sum]
  rw [← (lagEquiv (K := K)).symm.sum_comp]
  refine Finset.sum_congr rfl fun i _ => ?_
  have h := pderiv_rename (lagEquiv (K := K)).injective (lagEquiv.symm i) (lagLyap S)
  rw [Equiv.apply_symm_apply] at h
  rw [lagG, lagP, h, map_mul]

theorem norm_le_lagP (y : Vd (lagDim K)) :
    ‖y‖ ≤ (MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) (lagP S)).re := by
  rw [lagP, eval_rename_lagEquiv]
  have hge := eval_lagLyap_ge S (fun j => y (lagEquiv j))
  have hsum : ∑ i, y i ^ 2
      = ∑ j : DIdx K, y (lagEquiv (true, j)) ^ 2 + ∑ j : DIdx K, y (lagEquiv (false, j)) ^ 2 := by
    rw [← (lagEquiv (K := K)).sum_comp, Fintype.sum_prod_type, Fintype.sum_bool, add_comm]
  have hn : ‖y‖ ^ 2 = ∑ i, y i ^ 2 := by
    rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]
    simp [Real.norm_eq_abs, sq_abs]
  have : ‖y‖ ≤ 1 + (1 / 2) * ‖y‖ ^ 2 := by nlinarith [sq_nonneg (‖y‖ - 1)]
  simp only at hge
  linarith

theorem lagP_flux_bound (y : Vd (lagDim K)) :
    |(MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) (∑ i, lagG S i * pderiv i (lagP S))).re|
      ≤ (2 * S.nu * ∑ j, lam S j + 1)
        * (MvPolynomial.eval (fun i => ((y i : ℝ) : ℂ)) (lagP S)).re := by
  rw [lagG_lyapFlux, lagP, eval_rename_lagEquiv, eval_rename_lagEquiv]
  exact abs_eval_lagLyapFlux_le S _

/-! ## The main results -/

/-- **Essential self-adjointness of the Lagrangian Koopman comparison operator.**  For every
finite set of wave vectors, viscosity `ν ≥ 0` and bulk modulus `κ ≥ 0`, the Faris–Lavine
comparison operator `N_L = H_L² + 1 + ½|v|² + V_κ(ξ)` of the Lagrangian Navier–Stokes Koopman
generator is essentially self-adjoint on the Gauss–polynomial core of `L²(ℝ^{PIdx K})`. -/
theorem lagComparison_esa :
    EssentiallySelfAdjointOn (polyGaussCore (d := lagDim K)) (lagComparison S) :=
  KvnKato.lyapunovComparison_esa_poly (lagG S) (lagG_realCoeff S) (lagE_realCoeff S)
    (lagE_eval_ge S) (norm_le_lagP S) (lagP_flux_bound S)

/-- **The Lagrangian Navier–Stokes Koopman generator `H_L` is essentially self-adjoint on the
Gauss–polynomial core** — the hypothesis of `lagKoopman_esa_of_comparison_esa` discharged by
`lagComparison_esa`. -/
theorem lagKoopman_esa :
    EssentiallySelfAdjointOn (polyGaussCore (d := lagDim K)) (lagKoopmanOp S) :=
  lagKoopman_esa_of_comparison_esa S (lagComparison_esa S)

end

end BookProof.NsLagrangianComparisonEsa
