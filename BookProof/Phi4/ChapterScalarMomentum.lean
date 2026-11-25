import BookProof.Phi4.ChapterScalarSirk

/-!
# The continuous-momentum real scalar λφ⁴ model

Coordinates `0, 1, 2, 3` of `L²(ℝ⁴)` are `(φ, k₁, k₂, k₃)`, all continuous.
Only `φ` carries a conjugate momentum; `k₁, k₂, k₃` are momentum multipliers.
The inner Hamiltonian is

`h_cont = ½ p_φ² + ½ (k₁² + k₂² + k₃²) φ² + (λ/4)(φ² − v²)²`.

The gradient term is the diagonal continuous multiplier `½ |k|² φ²`: there is
no discrete momentum sum, no spatial lattice, and no spatial-derivative jet
constraint. The periodic lattice (`siteModel`, `twoSite`) and static-jet
(`jetModel`) models are frozen comparisons only.
-/

namespace BookProof.Phi4

open MvPolynomial HermiteProductCore HermiteProductBasis HermiteCore
open BookProof.YangMillsNonAbelianEsa BookProof.YangMillsHermite EsaClosure ChapterStoneResolvent
open ChapterSirkTrotterKato FarisLavine YangMillsFriedrichs
open scoped InnerProductSpace

noncomputable section

/-- The continuous-momentum scalar model on `L²(ℝ³_k × ℝ_φ)`. -/
def momContModel (p : Parameters) : Model 4 1 4 where
  momentum := fun _ => 0
  distinct := fun _ _ _ => Subsingleton.elim _ _
  form := Fin.cases (wall 0 (Real.sqrt (p.coupling / 2)) (p.vev ^ 2))
    (fun i => X i.succ * X 0)
  real_form := Fin.cases (real_wall ..)
    (fun i => (realCoeff_X i.succ).mul (realCoeff_X 0))

/-- Unit parameters and unit Mehler width. -/
def unitMomCont : Model 4 1 4 :=
  momContModel ⟨1, by norm_num, 1, by norm_num⟩

/-- The form sum splits into the double-well wall in `φ` and the three
continuous momentum–field products `kᵣ φ`. -/
theorem unitMomCont_forms (p : MvPolynomial (Fin 4) ℂ) :
    ∑ j, unitMomCont.form j * (unitMomCont.form j * p) =
      C (1 / 2 : ℂ) * (X 0 ^ 2 - 1) * ((X 0 ^ 2 - 1) * p) +
        (X 1 * X 0) * ((X 1 * X 0) * p) +
        (X 2 * X 0) * ((X 2 * X 0) * p) +
        (X 3 * X 0) * ((X 3 * X 0) * p) := by
  have hw : unitMomCont.form 0 =
      C (Real.sqrt (1 / 2) : ℂ) * (X 0 * X 0 - 1) := by
    change wall 0 _ _ = _
    simp [wall, smul_eq_C_mul]
  have h1 : unitMomCont.form 1 = (X 1 * X 0 : MvPolynomial (Fin 4) ℂ) := by
    change (momContModel ⟨1, by norm_num, 1, by norm_num⟩).form (1 : Fin 4) = _
    rfl
  have h2 : unitMomCont.form 2 = (X 2 * X 0 : MvPolynomial (Fin 4) ℂ) := by
    change (momContModel ⟨1, by norm_num, 1, by norm_num⟩).form (2 : Fin 4) = _
    rfl
  have h3 : unitMomCont.form 3 = (X 3 * X 0 : MvPolynomial (Fin 4) ℂ) := by
    change (momContModel ⟨1, by norm_num, 1, by norm_num⟩).form (3 : Fin 4) = _
    rfl
  rw [Fin.sum_univ_four, hw, h1, h2, h3]
  ring_nf
  simp only [← map_pow, ← Complex.ofReal_pow]
  rw [Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 1 / 2)]
  push_cast
  apply MvPolynomial.funext
  intro x
  simp
  ring

/-- The full action on the unnormalized Gaussian. The `He₂(φ)K₂` term is the
continuous momentum–field entanglement absent from the frozen static-jet
comparison. -/
theorem unitMomCont_vacuum_column :
    unitMomCont.innerHam ⟨pgLp 1, pgLp_mem_core 1⟩ =
      pgLp (C (17 / 8 : ℂ) + C (19 / 8 : ℂ) * (X 0 ^ 2 - 1) +
        C (1 / 4 : ℂ) * (X 0 ^ 4 - 6 * X 0 ^ 2 + 3) +
        C (1 / 2 : ℂ) * ((X 1 ^ 2 - 1) + (X 2 ^ 2 - 1) + (X 3 ^ 2 - 1)) +
        C (1 / 2 : ℂ) * (X 0 ^ 2 - 1) *
          ((X 1 ^ 2 - 1) + (X 2 ^ 2 - 1) + (X 3 ^ 2 - 1))) := by
  rw [Model.innerHam_pgLp, unitMomCont_forms, Fin.sum_univ_one]
  congr 1
  have hmom : unitMomCont.momentum 0 = (0 : Fin 4) := rfl
  rw [hmom, momOp_momOp_d]
  simp [QgHermiteFriedrichs.coreD, smul_eq_C_mul, Derivation.leibniz]
  apply MvPolynomial.funext
  intro x
  simp
  ring

/-! ## The product-Hermite basis of the unit action -/

/-- The one-coordinate multi-index `n eᵢ`. -/
private def hIdx (i : Fin 4) (n : ℕ) : Fin 4 →₀ ℕ := Finsupp.single i n

private theorem hermiteFactor_two (i : Fin 4) : hermiteFactor i 2 = X i ^ 2 - 1 := by
  simp [hermiteFactor, hermiteCx, Polynomial.hermite_succ, Polynomial.hermite_zero]
  ring

private theorem hermiteFactor_four (i : Fin 4) :
    hermiteFactor i 4 = X i ^ 4 - 6 * X i ^ 2 + 3 := by
  simp [hermiteFactor, hermiteCx, Polynomial.hermite_succ, Polynomial.hermite_zero]
  ring

private theorem hermiteMv_single (i : Fin 4) (n : ℕ) :
    hermiteMv (hIdx i n) = hermiteFactor i n := by
  rw [hermiteMv_erase i]
  have hval : (hIdx i n) i = n := by simp [hIdx]
  rw [hval]
  have h1 : ∏ j ∈ Finset.univ.erase i, hermiteFactor j ((hIdx i n) j) = 1 := by
    refine Finset.prod_eq_one fun j hj => ?_
    rw [show (hIdx i n) j = 0 by simp [hIdx, Finset.ne_of_mem_erase hj],
      hermiteFactor_zero]
  rw [h1, mul_one]

private theorem hermiteMv_two_two (i j : Fin 4) (hij : i ≠ j) :
    hermiteMv (hIdx i 2 + hIdx j 2) = (X i ^ 2 - 1) * (X j ^ 2 - 1) := by
  rw [hermiteMv_erase i]
  have hi : (hIdx i 2 + hIdx j 2) i = 2 := by simp [hIdx, hij.symm]
  rw [hi]
  rw [Finset.prod_eq_mul_prod_diff_singleton
    (Finset.mem_erase.mpr ⟨hij.symm, Finset.mem_univ j⟩)]
  have hj : (hIdx i 2 + hIdx j 2) j = 2 := by simp [hIdx, hij]
  rw [hj]
  have h1 : ∏ k ∈ Finset.univ.erase i \ {j}, hermiteFactor k
      ((hIdx i 2 + hIdx j 2) k) = 1 := by
    refine Finset.prod_eq_one fun k hk => ?_
    rw [Finset.mem_sdiff, Finset.mem_erase] at hk
    have hki : k ≠ i := hk.1.1
    have hkj : k ≠ j := fun h => hk.2 (by simp [h])
    rw [show (hIdx i 2 + hIdx j 2) k = 0 by simp [hIdx, hki, hkj], hermiteFactor_zero]
  rw [h1, mul_one, hermiteFactor_two i, hermiteFactor_two j]

private def momResidual : MvPolynomial (Fin 4) ℂ :=
  C (19 / 8 : ℂ) * (X 0 ^ 2 - 1) + C (1 / 4 : ℂ) * (X 0 ^ 4 - 6 * X 0 ^ 2 + 3) +
    C (1 / 2 : ℂ) * ((X 1 ^ 2 - 1) + (X 2 ^ 2 - 1) + (X 3 ^ 2 - 1)) +
    C (1 / 2 : ℂ) * (X 0 ^ 2 - 1) *
      ((X 1 ^ 2 - 1) + (X 2 ^ 2 - 1) + (X 3 ^ 2 - 1))

private theorem residual_vector :
    unitMomCont.innerHam ⟨pgLp 1, pgLp_mem_core 1⟩ - (17 / 8 : ℂ) • pgLp 1 =
      pgLp momResidual := by
  rw [unitMomCont_vacuum_column]
  change pgMap _ - _ • pgMap _ = pgMap _
  rw [← map_smul, ← map_sub]
  congr 1
  simp [momResidual, smul_eq_C_mul]
  ring

private theorem momResidual_decomp :
    momResidual =
      (19 / 8 : ℂ) • hermiteMv (hIdx 0 2) +
      (1 / 4 : ℂ) • hermiteMv (hIdx 0 4) +
      (1 / 2 : ℂ) • (hermiteMv (hIdx 1 2) + hermiteMv (hIdx 2 2) +
        hermiteMv (hIdx 3 2)) +
      (1 / 2 : ℂ) • (hermiteMv (hIdx 0 2 + hIdx 1 2) +
        hermiteMv (hIdx 0 2 + hIdx 2 2) + hermiteMv (hIdx 0 2 + hIdx 3 2)) := by
  rw [momResidual]
  simp only [mul_add]
  apply MvPolynomial.funext
  intro x
  have e1 : MvPolynomial.eval x (hermiteMv (hIdx 0 2)) = x 0 ^ 2 - 1 := by
    rw [hermiteMv_single, hermiteFactor_two]
    simp
  have e2 : MvPolynomial.eval x (hermiteMv (hIdx 0 4)) = x 0 ^ 4 - 6 * x 0 ^ 2 + 3 := by
    rw [hermiteMv_single, hermiteFactor_four]
    simp
  have e3 : MvPolynomial.eval x (hermiteMv (hIdx 1 2)) = x 1 ^ 2 - 1 := by
    rw [hermiteMv_single, hermiteFactor_two]
    simp
  have e4 : MvPolynomial.eval x (hermiteMv (hIdx 2 2)) = x 2 ^ 2 - 1 := by
    rw [hermiteMv_single, hermiteFactor_two]
    simp
  have e5 : MvPolynomial.eval x (hermiteMv (hIdx 3 2)) = x 3 ^ 2 - 1 := by
    rw [hermiteMv_single, hermiteFactor_two]
    simp
  have e6 : MvPolynomial.eval x (hermiteMv (hIdx 0 2 + hIdx 1 2)) =
      (x 0 ^ 2 - 1) * (x 1 ^ 2 - 1) := by
    rw [hermiteMv_two_two 0 1 (by decide)]
    simp
  have e7 : MvPolynomial.eval x (hermiteMv (hIdx 0 2 + hIdx 2 2)) =
      (x 0 ^ 2 - 1) * (x 2 ^ 2 - 1) := by
    rw [hermiteMv_two_two 0 2 (by decide)]
    simp
  have e8 : MvPolynomial.eval x (hermiteMv (hIdx 0 2 + hIdx 3 2)) =
      (x 0 ^ 2 - 1) * (x 3 ^ 2 - 1) := by
    rw [hermiteMv_two_two 0 3 (by decide)]
    simp
  simp only [smul_eq_C_mul, MvPolynomial.eval_add, MvPolynomial.eval_mul,
    MvPolynomial.eval_C, MvPolynomial.eval_X, MvPolynomial.eval_pow,
    MvPolynomial.eval_sub, map_one, map_ofNat, e1, e2, e3, e4, e5, e6, e7, e8]
  ring

private def momIdx : Fin 8 → Fin 4 →₀ ℕ :=
  ![hIdx 0 2, hIdx 0 4, hIdx 1 2, hIdx 2 2, hIdx 3 2,
    hIdx 0 2 + hIdx 1 2, hIdx 0 2 + hIdx 2 2, hIdx 0 2 + hIdx 3 2]

private def momCoeff : Fin 8 → ℂ :=
  ![19 / 8, 1 / 4, 1 / 2, 1 / 2, 1 / 2, 1 / 2, 1 / 2, 1 / 2]

private theorem momIdx_injective : Function.Injective momIdx := by
  intro i j heq
  fin_cases i <;> fin_cases j <;>
    first
    | rfl
    | (exfalso
       have h0 := congrArg (fun f : Fin 4 →₀ ℕ => f 0) heq
       have h1 := congrArg (fun f : Fin 4 →₀ ℕ => f 1) heq
       have h2 := congrArg (fun f : Fin 4 →₀ ℕ => f 2) heq
       have h3 := congrArg (fun f : Fin 4 →₀ ℕ => f 3) heq
       simp [momIdx, hIdx] at h0 h1 h2 h3)

private def momVec : Fin 8 → L2d 4 := fun i => pgLp (hermiteMv (momIdx i))

private theorem pgLp_momResidual : pgLp momResidual = ∑ i, momCoeff i • momVec i := by
  rw [momResidual_decomp]
  change pgMap _ = ∑ i, momCoeff i • pgMap (hermiteMv (momIdx i))
  simp only [map_add, map_smul, smul_add]
  rw [Fin.sum_univ_eight]
  simp only [momCoeff, momIdx]
  abel

private theorem inner_psi_off (a b : Fin 4 →₀ ℕ) (h : a ≠ b) :
    inner ℂ (pgLp (hermiteMv a)) (pgLp (hermiteMv b)) = 0 := by
  obtain ⟨i, hi⟩ : ∃ i, a i ≠ b i := by
    by_contra hcon
    push_neg at hcon
    exact h (Finsupp.ext hcon)
  rw [inner_pgLp_hermiteMv, Complex.ofReal_eq_zero]
  exact Finset.prod_eq_zero (Finset.mem_univ i) (by rw [hermiteInner_eq, if_neg hi])

private theorem norm_psi_diag (a : Fin 4 →₀ ℕ) :
    ‖pgLp (hermiteMv a)‖ ^ 2 =
      (∏ i, (a i).factorial : ℝ) * ‖pgLp (d := 4) 1‖ ^ 2 := by
  have h := inner_pgLp_hermiteMv (d := 4) a a
  have h0 : (inner ℂ (pgLp (d := 4) 1) (pgLp (d := 4) 1)) =
      ((∏ i, hermiteInner ((0 : Fin 4 →₀ ℕ) i) ((0 : Fin 4 →₀ ℕ) i) : ℝ) : ℂ) := by
    rw [show (1 : MvPolynomial (Fin 4) ℂ) = hermiteMv 0 from (hermiteMv_zero).symm]
    exact inner_pgLp_hermiteMv _ _
  rw [inner_self_eq_norm_sq_to_K] at h h0
  have hh : (∏ i, hermiteInner (a i) (a i)) =
      (∏ i, (a i).factorial : ℝ) *
        (∏ i, hermiteInner ((0 : Fin 4 →₀ ℕ) i) ((0 : Fin 4 →₀ ℕ) i)) := by
    simp only [hermiteInner_eq, if_true]
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
    simp
  have hnormA : ‖pgLp (hermiteMv a)‖ ^ 2 = ∏ i, hermiteInner (a i) (a i) := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_pow]
    exact h
  have hnorm0 : ‖pgLp (d := 4) 1‖ ^ 2 =
      ∏ i, hermiteInner ((0 : Fin 4 →₀ ℕ) i) ((0 : Fin 4 →₀ ℕ) i) := by
    apply Complex.ofReal_injective
    rw [Complex.ofReal_pow]
    exact h0
  rw [hnormA, hnorm0, hh]

private theorem norm_sq_orthogonal_sum {ι : Type*} [Fintype ι] (c : ι → ℂ) (v : ι → L2d 4)
    (h : ∀ i j, i ≠ j → inner ℂ (v i) (v j) = 0) :
    ‖∑ i, c i • v i‖ ^ 2 = ∑ i, ‖c i‖ ^ 2 * ‖v i‖ ^ 2 := by
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ)]
  simp only [inner_sum, sum_inner, inner_smul_left, inner_smul_right, Finset.mul_sum, map_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_eq_single i]
  · have hnn : inner ℂ (v i) (v i) = ((‖v i‖ ^ 2 : ℝ) : ℂ) := by
      rw [inner_self_eq_norm_sq_to_K]
      push_cast
      rfl
    rw [hnn, ← mul_assoc, Complex.mul_conj, ← Complex.ofReal_mul]
    change Complex.re (↑(Complex.normSq (c i) * ‖v i‖ ^ 2) : ℂ) = _
    rw [Complex.ofReal_re, Complex.normSq_eq_norm_sq]
  · intro j _ hji
    rw [← inner_conj_symm, h j i hji]
    simp
  · intro hi
    simp at hi

theorem unitMomCont_defect_norm_sq :
    ‖unitMomCont.innerHam ⟨pgLp 1, pgLp_mem_core 1⟩ - (17 / 8 : ℂ) • pgLp 1‖ ^ 2 =
      (553 / 32 : ℝ) * ‖pgLp (d := 4) 1‖ ^ 2 := by
  rw [residual_vector, pgLp_momResidual]
  rw [norm_sq_orthogonal_sum momCoeff momVec (by
    intro i j hij
    exact inner_psi_off _ _ fun heq => hij (momIdx_injective heq))]
  rw [Fin.sum_univ_eight]
  simp [momCoeff, momVec, momIdx, hIdx, norm_psi_diag, Nat.factorial,
    Finsupp.single_apply, Finsupp.add_apply, Fin.prod_univ_four,
    Matrix.cons_val_zero]
  norm_num
  ring

/-- The exact continuous-momentum Hashimoto phase on the vacuum, compared with the
full unbounded evolution. Squaring avoids a square-root normalization on the Gaussian. -/
theorem unitMomCont_rankOne_error {T : UnboundedSelfAdjoint (L2d 4)}
    (hext : IsSelfAdjointExtension unitMomCont.innerHam T.op) (t : ℝ) :
    ‖T.stoneU t (pgLp 1) - Complex.exp (-(Complex.I * (17 / 8) * t)) • pgLp 1‖ ^ 2 ≤
      (553 / 32 : ℝ) * t ^ 2 * ‖pgLp (d := 4) 1‖ ^ 2 := by
  let seed : polyGaussCore (d := 4) := ⟨pgLp 1, pgLp_mem_core 1⟩
  obtain ⟨hmem, hval⟩ := hext.1 seed
  have h := rankOne_flow_error T ⟨seed, hmem⟩ (17 / 8) t
  rw [hval] at h
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  change (‖T.stoneU t (pgLp 1) - _ • pgLp 1‖) ^ 2 ≤
    (‖unitMomCont.innerHam seed - _ • pgLp 1‖ * |t|) ^ 2 at hs
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at hs
  rw [mul_pow, sq_abs, unitMomCont_defect_norm_sq] at hs
  linarith

/-- For the continuous-momentum Gaussian seed the normalized return probability
loses at most (553/32)t². Both sides are multiplied by the fourth power of the
Gaussian norm. -/
theorem unitMomCont_return_probability {T : UnboundedSelfAdjoint (L2d 4)}
    (hext : IsSelfAdjointExtension unitMomCont.innerHam T.op) (t : ℝ) :
    (1 - (553 / 32 : ℝ) * t ^ 2) * ‖pgLp (d := 4) 1‖ ^ 4 ≤
      ‖inner ℂ (pgLp (d := 4) 1) (T.stoneU t (pgLp 1))‖ ^ 2 := by
  let x := pgLp (d := 4) 1
  let c := Complex.exp (-(Complex.I * (17 / 8) * t))
  have hc : ‖c‖ = 1 := by simp [c, Complex.norm_exp]
  have hn : ‖c • x‖ = ‖x‖ := by rw [norm_smul, hc, one_mul]
  have hy := T.norm_stoneU_apply t x
  have loss := overlap_loss (c • x) (T.stoneU t x) (hy.trans hn.symm)
  rw [hn, inner_smul_left, norm_mul, Complex.norm_conj, hc, one_mul, norm_sub_rev] at loss
  have err := unitMomCont_rankOne_error hext t
  change ‖T.stoneU t x - c • x‖ ^ 2 ≤ (553 / 32 : ℝ) * t ^ 2 * ‖x‖ ^ 2 at err
  change (1 - (553 / 32 : ℝ) * t ^ 2) * ‖x‖ ^ 4 ≤ ‖inner ℂ x (T.stoneU t x)‖ ^ 2
  nlinarith [mul_le_mul_of_nonneg_left err (sq_nonneg ‖x‖)]


end
end BookProof.Phi4
