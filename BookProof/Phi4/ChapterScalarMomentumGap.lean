import BookProof.Phi4.ChapterScalarMomentum
import BookProof.Phi4.ChapterScalarEnergy
import BookProof.ChapterQuadraticRotationEsa

/-!
# Gap and parity of the continuous-momentum scalar model

This chapter proves a unit-parameter lower bound for the inner fibre and its graph
closure, and records the field and spatial reflection identities on the core.

The analytic input is the harmonic lower bound for the Gaussian core: the
uncertainty identity for `P_j = momOp j` and `X_j = mulOp (X j)` gives
`α/2 ‖ψ‖² ≤ ½ (‖P_j ψ‖² + α² ‖X_j ψ‖²)`.
-/

namespace BookProof.Phi4

open MvPolynomial HermiteProductCore HermiteProductBasis HermiteCore
open BookProof.YangMillsNonAbelianEsa BookProof.YangMillsHermite
open ChapterStoneResolvent EsaClosure ChapterSirkTrotterKato FarisLavine YangMillsFriedrichs
open scoped InnerProductSpace Matrix
open BookProof.QuadraticRotation

noncomputable section

variable {d : ℕ}

/-- The Gaussian-core representative of the physical momentum `−i ∂_j`. -/
def coreP (j : Fin d) : polyGaussCore (d := d) →ₗ[ℂ] L2d d :=
  (polyGaussCore (d := d)).subtype.comp ((coreRepPoly d).op (momOp j))

/-- The Gaussian-core representative of multiplication by `x_j`. -/
def coreX (j : Fin d) : polyGaussCore (d := d) →ₗ[ℂ] L2d d :=
  (polyGaussCore (d := d)).subtype.comp ((coreRepPoly d).op (mulOp (X j)))

theorem coreP_symmetric (j : Fin d) :
    SymmetricOn (polyGaussCore (d := d)) (coreP j) :=
  (coreRepPoly d).symmetricOn_op (momOp_polySym j)

theorem coreX_symmetric (j : Fin d) :
    SymmetricOn (polyGaussCore (d := d)) (coreX j) :=
  (coreRepPoly d).symmetricOn_op (mulOp_polySym (realCoeff_X j))

/-- The canonical commutator on the Gaussian core: `[momOp j, mulOp (X j)] = −i`. -/
theorem momOp_mulOp_comm (j : Fin d) :
    (momOp (d := d) j).comp (mulOp (X j)) - (mulOp (X j)).comp (momOp (d := d) j) =
      (-Complex.I) • LinearMap.id := by
  refine LinearMap.ext fun p => ?_
  simp only [LinearMap.sub_apply, LinearMap.comp_apply, LinearMap.smul_apply, LinearMap.id_apply,
    momOp_apply, mulOp_apply]
  rw [Derivation.leibniz, pderiv_X_self]
  simp only [smul_eq_C_mul, smul_eq_mul]
  ring

/-- The commutator transported to the core. -/
theorem coreP_coreX_comm (j : Fin d) (x : polyGaussCore (d := d)) :
    (coreRepPoly d).op (momOp (d := d) j) ((coreRepPoly d).op (mulOp (X j)) x) -
        (coreRepPoly d).op (mulOp (X j)) ((coreRepPoly d).op (momOp (d := d) j) x) =
      (-Complex.I) • x := by
  let p := (coreRepPoly d).equiv.symm x
  have h := congrArg (coreRepPoly d).equiv (LinearMap.congr_fun (momOp_mulOp_comm j) p)
  simp only [] at h
  simpa [CoreRep.op_apply, p] using h

/-- **The uncertainty identity** on the Gaussian core. -/
theorem inner_coreP_coreX (j : Fin d) (x : polyGaussCore (d := d)) :
    inner ℂ (coreP j x) (coreX j x) - inner ℂ (coreX j x) (coreP j x) =
      -Complex.I * ((‖(x : L2d d)‖ ^ 2 : ℝ) : ℂ) := by
  have hPX := coreP_symmetric j x ((coreRepPoly d).op (mulOp (X j)) x)
  have hXP := coreX_symmetric j x ((coreRepPoly d).op (momOp j) x)
  have hsub : coreP j x - coreX j x = coreP j x - coreX j x := rfl
  -- rewrite both inner products as pairings of core elements
  have h1 : inner ℂ (coreP j x) (coreX j x) =
      inner ℂ (x : L2d d) (coreP j ((coreRepPoly d).op (mulOp (X j)) x)) := hPX
  have h2 : inner ℂ (coreX j x) (coreP j x) =
      inner ℂ (x : L2d d) (coreX j ((coreRepPoly d).op (momOp j) x)) := hXP
  rw [h1, h2]
  have hcomb : inner ℂ (x : L2d d) (coreP j ((coreRepPoly d).op (mulOp (X j)) x)) -
      inner ℂ (x : L2d d) (coreX j ((coreRepPoly d).op (momOp j) x)) =
      inner ℂ (x : L2d d) (coreP j ((coreRepPoly d).op (mulOp (X j)) x) -
        coreX j ((coreRepPoly d).op (momOp j) x)) := (inner_sub_right ..).symm
  rw [hcomb]
  simp only [coreP, coreX, LinearMap.comp_apply, Submodule.subtype_apply]
  have hsub := sub_eq_iff_eq_add.mp (coreP_coreX_comm j x)
  rw [hsub]
  simp only [Submodule.coe_add]
  rw [add_sub_cancel_right]
  simp only [Submodule.coe_smul]
  rw [inner_smul_right]
  simp

set_option maxHeartbeats 1000000 in
/-- **Harmonic lower bound.** For every Gaussian-core vector and every positive `α`,
`(α/2)‖x‖² ≤ ½(‖P_j x‖² + α²‖X_j x‖²)`. -/
theorem harmonic_lower_bound (j : Fin d) {α : ℝ} (hα : 0 < α)
    (x : polyGaussCore (d := d)) :
    (α / 2) * ‖(x : L2d d)‖ ^ 2 ≤
      (1 / 2) * (‖coreP j x‖ ^ 2 + α ^ 2 * ‖coreX j x‖ ^ 2) := by
  let c : ℂ := Complex.I * (α : ℂ)
  have hnonneg : 0 ≤ ‖coreP j x - c • coreX j x‖ ^ 2 := sq_nonneg _
  have hinner := inner_coreP_coreX j x
  have hz : inner ℂ (coreP j x) (coreX j x) -
      (starRingEnd ℂ) (inner ℂ (coreP j x) (coreX j x)) =
      -Complex.I * ((‖(x : L2d d)‖ ^ 2 : ℝ) : ℂ) := by
    simpa only [inner_conj_symm] using hinner
  have him : (inner ℂ (coreP j x) (coreX j x)).im = -(‖(x : L2d d)‖ ^ 2) / 2 := by
    have h := congrArg Complex.im hz
    simp only [Complex.sub_im, Complex.conj_im, Complex.neg_im, Complex.mul_im,
      Complex.ofReal_re, Complex.ofReal_im, Complex.I_im] at h
    linarith
  have hnormc : ‖c‖ = α := by
    simp [c, Complex.norm_I, abs_of_pos hα]
  have hexp : ‖coreP j x - c • coreX j x‖ ^ 2 =
      ‖coreP j x‖ ^ 2 + α ^ 2 * ‖coreX j x‖ ^ 2 - α * ‖(x : L2d d)‖ ^ 2 := by
    rw [norm_sub_sq (𝕜 := ℂ)]
    have hcX : ‖c • coreX j x‖ = α * ‖coreX j x‖ := by
      rw [norm_smul, hnormc]
    rw [hcX, mul_pow]
    have hre : RCLike.re (inner ℂ (coreP j x) (c • coreX j x)) =
        α * ‖(x : L2d d)‖ ^ 2 / 2 := by
      rw [inner_smul_right]
      change Complex.re (c * inner ℂ (coreP j x) (coreX j x)) =
        α * ‖(x : L2d d)‖ ^ 2 / 2
      rw [Complex.mul_re]
      simp [c, him]
      ring
    rw [hre]
    ring
  have hnonneg : 0 ≤ ‖coreP j x - c • coreX j x‖ ^ 2 := sq_nonneg _
  rw [hexp] at hnonneg
  linarith

/-- The absolute inner gap scale of the continuous-momentum scalar model. -/
def contAlpha (p : Parameters) : ℝ :=
  min (1 / (2 * p.vev ^ 2)) (min (1 / 2) (p.coupling / 2))

/-- Candidate lower bound for a general parameter pair. -/
def contGap (p : Parameters) : ℝ := (7 / 32) * contAlpha p

/-- The absolute inner gap scale is strictly positive for every admissible parameter. -/
theorem contGap_pos (p : Parameters) : 0 < contGap p := by
  have hv : 0 < p.vev ^ 2 := pow_pos p.vev_pos 2
  have hvev : 0 < 1 / (2 * p.vev ^ 2) := one_div_pos.mpr (by positivity)
  have hcoupling : 0 < p.coupling / 2 := half_pos p.coupling_pos
  have hmin : 0 < min (1 / 2 : ℝ) (p.coupling / 2) :=
    lt_min (by norm_num) hcoupling
  exact mul_pos (by norm_num) (lt_min hvev hmin)


/-! ## `ℤ₂` field reflection and spatial parity -/

/-- The diagonal matrix `diag(-1, 1, 1, 1)` of field reflection `φ ↦ -φ`. -/
def fieldReflMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal (fun i => if i = 0 then (-1 : ℝ) else 1)

/-- The diagonal matrix `diag(1, -1, -1, -1)` of spatial parity `k ↦ -k`. -/
def spatialReflMatrix : Matrix (Fin 4) (Fin 4) ℝ :=
  Matrix.diagonal (fun i => if i = 0 then (1 : ℝ) else -1)

theorem fieldReflMatrix_orth : fieldReflMatrixᵀ * fieldReflMatrix = 1 := by
  rw [fieldReflMatrix, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  rw [show (fun i : Fin 4 =>
      (if i = 0 then (-1 : ℝ) else 1) * (if i = 0 then (-1 : ℝ) else 1)) = 1 by
    funext i
    fin_cases i <;> norm_num]
  exact Matrix.diagonal_one

theorem spatialReflMatrix_orth : spatialReflMatrixᵀ * spatialReflMatrix = 1 := by
  rw [spatialReflMatrix, Matrix.diagonal_transpose, Matrix.diagonal_mul_diagonal]
  rw [show (fun i : Fin 4 =>
      (if i = 0 then (1 : ℝ) else -1) * (if i = 0 then (1 : ℝ) else -1)) = 1 by
    funext i
    fin_cases i <;> norm_num]
  exact Matrix.diagonal_one

/-- The orthogonal substitution as an endomorphism of the Gaussian core. -/
def coreRot {d : ℕ} (O : Matrix (Fin d) (Fin d) ℝ) :
    polyGaussCore (d := d) →ₗ[ℂ] polyGaussCore (d := d) :=
  (coreRepPoly d).op (rotPoly O).toLinearMap

set_option maxHeartbeats 1000000 in
theorem coreRot_pgLp {d : ℕ} (O : Matrix (Fin d) (Fin d) ℝ)
    (p : MvPolynomial (Fin d) ℂ) :
    coreRot O ⟨pgLp p, pgLp_mem_core p⟩ =
      ⟨pgLp (rotPoly O p), pgLp_mem_core _⟩ :=
  op_pgLp_d (rotPoly O).toLinearMap p

set_option maxHeartbeats 1000000 in
theorem coreRot_inner {d : ℕ} {O : Matrix (Fin d) (Fin d) ℝ}
    (hO : Oᵀ * O = 1) (x y : polyGaussCore (d := d)) :
    inner ℂ (coreRot O x) (coreRot O y) = inner ℂ x y := by
  let p := (coreRepPoly d).equiv.symm x
  let q := (coreRepPoly d).equiv.symm y
  have hx : x = ⟨pgLp p, pgLp_mem_core p⟩ := by
    rw [← equiv_pgLp_d p, LinearEquiv.apply_symm_apply]
  have hy : y = ⟨pgLp q, pgLp_mem_core q⟩ := by
    rw [← equiv_pgLp_d q, LinearEquiv.apply_symm_apply]
  rw [hx, hy, coreRot_pgLp, coreRot_pgLp]
  exact mod_cast inner_pgLp_rotPoly hO p q

/-- The field-reflection `ℤ₂` parity on the Gaussian core. -/
def fieldParity : polyGaussCore (d := 4) →ₗ[ℂ] polyGaussCore (d := 4) :=
  coreRot fieldReflMatrix

/-- The spatial-parity `k ↦ -k` on the Gaussian core. -/
def spatialParity : polyGaussCore (d := 4) →ₗ[ℂ] polyGaussCore (d := 4) :=
  coreRot spatialReflMatrix

/-- The `ℤ₂`-even sector of field reflection. -/
def fieldEven (x : polyGaussCore (d := 4)) : Prop := fieldParity x = x


/-- Field reflection is orthogonal on the Gaussian core. -/
theorem fieldParity_inner (x y : polyGaussCore (d := 4)) :
    inner ℂ (fieldParity x) (fieldParity y) = inner ℂ x y :=
  coreRot_inner fieldReflMatrix_orth x y

/-- Spatial parity is orthogonal on the Gaussian core. -/
theorem spatialParity_inner (x y : polyGaussCore (d := 4)) :
    inner ℂ (spatialParity x) (spatialParity y) = inner ℂ x y :=
  coreRot_inner spatialReflMatrix_orth x y


end
end BookProof.Phi4

namespace BookProof.Phi4

open MvPolynomial HermiteProductCore HermiteProductBasis HermiteCore
open BookProof.YangMillsHermite BookProof.YangMillsNonAbelianEsa BookProof.FarisLavine
open ChapterStoneResolvent EsaClosure ChapterSirkTrotterKato YangMillsFriedrichs
open BookProof.QuadraticRotation

/-! ## Square completion for the unit double well -/

/-- The unit wall form is the completed square
`½ V² = ⅛ φ² − 9/64 + ¼ (φ² − 3/2)²` in operator form. -/
theorem unit_wall_completion (p : MvPolynomial (Fin 4) ℂ) :
    (1 / 2 : ℂ) • (unitMomCont.form 0 * (unitMomCont.form 0 * p)) =
      C (1 / 8 : ℂ) * (X 0 * (X 0 * p)) - C (9 / 64 : ℂ) * p +
        C (1 / 4 : ℂ) * ((X 0 ^ 2 - C (5 / 4 : ℂ)) *
          ((X 0 ^ 2 - C (5 / 4 : ℂ)) * p)) := by
  have hw : unitMomCont.form 0 =
      C (Real.sqrt (1 / 2) : ℂ) * (X 0 * X 0 - 1) := by
    change wall 0 _ _ = _
    simp [wall, smul_eq_C_mul]
  rw [hw]
  apply MvPolynomial.funext
  intro x
  have h3 : ((Real.sqrt (1 / 2) : ℝ) : ℂ) * ((Real.sqrt (1 / 2) : ℝ) : ℂ) =
      (1 / 2 : ℂ) := by
    rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num)]
    norm_num
  simp only [MvPolynomial.eval_add, MvPolynomial.eval_mul, MvPolynomial.eval_C,
    MvPolynomial.eval_X, MvPolynomial.eval_pow, MvPolynomial.eval_sub,
    map_one, map_ofNat, Algebra.smul_def, smul_eq_mul]
  have hc : (MvPolynomial.eval x)
      ((algebraMap ℂ (MvPolynomial (Fin 4) ℂ)) (1 / 2)) = (1 / 2 : ℂ) := by simp
  have hs : (((Real.sqrt (1 / 2) : ℝ) : ℂ)) ^ 2 = (1 / 2 : ℂ) := by
    rw [sq, h3]
  rw [hc]
  ring_nf
  rw [hs]
  ring_nf


/-! ## The unconditional unit gap -/

private noncomputable def uFactor : Fin 1 ⊕ Fin 4 → polyGaussCore (d := 4) →ₗ[ℂ] L2d 4 :=
  Sum.elim (fun i => polyGaussCore.subtype.comp
      ((coreRepPoly 4).op (momOp (unitMomCont.momentum i))))
    (fun j => polyGaussCore.subtype.comp ((coreRepPoly 4).op (mulOp (unitMomCont.form j))))

set_option maxHeartbeats 1000000 in
private theorem unit_inner_pair (x y : polyGaussCore (d := 4)) :
    inner ℂ (x : L2d 4) (Model.innerHam unitMomCont y) = (1 / 2 : ℂ) *
      ∑ i, inner ℂ (uFactor i x) (uFactor i y) := by
  rw [Model.innerHam, weylPoly, weylOp_apply, inner_smul_right, inner_add_right, inner_sum,
    inner_sum]
  conv_rhs => arg 2; rw [Fintype.sum_sum_type]
  have hpi (i : Fin 1) := (coreRepPoly 4).symmetricOn_op
    (momOp_polySym (unitMomCont.momentum i)) x
    ((coreRepPoly 4).op (momOp (unitMomCont.momentum i)) y)
  have hf (j : Fin 4) := (coreRepPoly 4).symmetricOn_op
    (mulOp_polySym (unitMomCont.real_form j)) x
    ((coreRepPoly 4).op (mulOp (unitMomCont.form j)) y)
  simp only [LinearMap.comp_apply, Submodule.subtype_apply] at hpi hf
  simp only [uFactor, Sum.elim_inl, Sum.elim_inr, LinearMap.comp_apply,
    Submodule.subtype_apply, hpi, hf, Complex.ofReal_div, Complex.ofReal_one,
    Complex.ofReal_ofNat]

private noncomputable def uField0c :
    polyGaussCore (d := 4) →ₗ[ℂ] polyGaussCore (d := 4) :=
  (coreRepPoly 4).op (mulOp (unitMomCont.form 0))

private noncomputable def uField0 : polyGaussCore (d := 4) →ₗ[ℂ] L2d 4 :=
  polyGaussCore.subtype.comp uField0c

private noncomputable def uFieldQc :
    polyGaussCore (d := 4) →ₗ[ℂ] polyGaussCore (d := 4) :=
  (coreRepPoly 4).op (mulOp (X 0 * X 0 - C (5 / 4 : ℂ)))

private noncomputable def uFieldQ : polyGaussCore (d := 4) →ₗ[ℂ] L2d 4 :=
  polyGaussCore.subtype.comp uFieldQc

private noncomputable def coreXc (j : Fin 4) :
    polyGaussCore (d := 4) →ₗ[ℂ] polyGaussCore (d := 4) :=
  (coreRepPoly 4).op (mulOp (X j))

private theorem uField0_symmetric : SymmetricOn (polyGaussCore (d := 4)) uField0 :=
  (coreRepPoly 4).symmetricOn_op (mulOp_polySym (unitMomCont.real_form 0))

set_option maxHeartbeats 1000000 in
private theorem uFieldQ_symmetric : SymmetricOn (polyGaussCore (d := 4)) uFieldQ := by
  refine (coreRepPoly 4).symmetricOn_op (mulOp_polySym ?_)
  change starP (X 0 * X 0 - C (5 / 4 : ℂ)) = X 0 * X 0 - C (5 / 4 : ℂ)
  simp [starP_mul, map_div₀, map_ofNat]

set_option maxHeartbeats 1000000 in
/-- The completed-square identity transported to the Gaussian core. -/
private theorem unit_wall_completion_core (ψ : polyGaussCore (d := 4)) :
    (1 / 2 : ℂ) • uField0c (uField0c ψ) =
      (1 / 8 : ℂ) • coreXc 0 (coreXc 0 ψ) - (9 / 64 : ℂ) • ψ +
        (1 / 4 : ℂ) • uFieldQc (uFieldQc ψ) := by
  let p := (coreRepPoly 4).equiv.symm ψ
  have hψ : (coreRepPoly 4).equiv p = ψ := LinearEquiv.apply_symm_apply _ _
  have hC (c : ℂ) (q : MvPolynomial (Fin 4) ℂ) :
      (coreRepPoly 4).equiv (C c * q) = c • (coreRepPoly 4).equiv q := by
    apply Subtype.ext
    rw [CoreRep.coe_equiv, Submodule.coe_smul, CoreRep.coe_equiv]
    rw [← smul_eq_C_mul]
    rw [← HermiteProductCore.pgMap_apply, map_smul, HermiteProductCore.pgMap_apply]
  have h := congrArg (fun q => (coreRepPoly 4).equiv q) (unit_wall_completion p)
  simp only [map_smul, map_add, map_sub, hC, hψ] at h
  simpa [p, uField0c, uFieldQc, coreXc, CoreRep.op_apply, mulOp, hψ, mul_assoc, pow_two] using h

set_option maxHeartbeats 1000000 in
/-- The field part of the unit energy is the completed square `½ V²`. -/
private theorem unit_field_norm (ψ : polyGaussCore (d := 4)) :
    ‖uField0 ψ‖ ^ 2 =
      (1 / 4) * ‖coreX 0 ψ‖ ^ 2 - (9 / 32) * ‖(ψ : L2d 4)‖ ^ 2 +
        (1 / 2) * ‖uFieldQ ψ‖ ^ 2 := by
  have hcore := unit_wall_completion_core ψ
  have h0 : inner ℂ (ψ : L2d 4) ((uField0c (uField0c ψ) : L2d 4)) = ‖uField0 ψ‖ ^ 2 := by
    have hs := uField0_symmetric ψ (uField0c ψ)
    change inner ℂ (uField0 ψ) ((uField0c ψ : L2d 4)) =
      inner ℂ (ψ : L2d 4) ((uField0c (uField0c ψ) : L2d 4)) at hs
    rw [← hs]
    exact_mod_cast inner_self_eq_norm_sq_to_K (uField0 ψ)
  have hX : inner ℂ (ψ : L2d 4) ((coreXc 0 (coreXc 0 ψ) : L2d 4)) =
      ‖coreX 0 ψ‖ ^ 2 := by
    have hs := coreX_symmetric 0 ψ (coreXc 0 ψ)
    change inner ℂ (coreX 0 ψ) ((coreXc 0 ψ : L2d 4)) =
      inner ℂ (ψ : L2d 4) ((coreXc 0 (coreXc 0 ψ) : L2d 4)) at hs
    rw [← hs]
    exact_mod_cast inner_self_eq_norm_sq_to_K (coreX 0 ψ)
  have hQ : inner ℂ (ψ : L2d 4) ((uFieldQc (uFieldQc ψ) : L2d 4)) = ‖uFieldQ ψ‖ ^ 2 := by
    have hs := uFieldQ_symmetric ψ (uFieldQc ψ)
    change inner ℂ (uFieldQ ψ) ((uFieldQc ψ : L2d 4)) =
      inner ℂ (ψ : L2d 4) ((uFieldQc (uFieldQc ψ) : L2d 4)) at hs
    rw [← hs]
    exact_mod_cast inner_self_eq_norm_sq_to_K (uFieldQ ψ)
  have hψ : inner ℂ (ψ : L2d 4) (ψ : L2d 4) = ‖(ψ : L2d 4)‖ ^ 2 := by
    exact_mod_cast inner_self_eq_norm_sq_to_K (ψ : L2d 4)
  have h2 := congrArg (fun z : polyGaussCore (d := 4) => inner ℂ (ψ : L2d 4) (z : L2d 4)) hcore
  simp only [Submodule.coe_smul, Submodule.coe_add, Submodule.coe_sub] at h2
  simp only [inner_add_right, inner_sub_right, inner_smul_right] at h2
  rw [h0, hX, hQ, hψ] at h2
  norm_num at h2
  have h2' := congrArg Complex.re h2
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.add_re, Complex.sub_re, Complex.ofReal_pow, Complex.ofReal_div,
    Complex.ofReal_one, Complex.ofReal_ofNat] at h2'
  norm_num at h2'
  rw [← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_pow,
    ← Complex.ofReal_pow] at h2'
  simp only [Complex.ofReal_re] at h2'
  ring_nf at h2' ⊢
  linarith

set_option maxHeartbeats 4000000 in
/-- The unit lower bound `7/64` on the Gaussian core. -/
theorem unitMomCont_inner_gap (ψ : polyGaussCore (d := 4)) :
    (7 / 64 : ℝ) * ‖(ψ : L2d 4)‖ ^ 2 ≤
      (inner ℂ (ψ : L2d 4) (Model.innerHam unitMomCont ψ)).re := by
  have hpair := congrArg Complex.re (unit_inner_pair ψ ψ)
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, mul_zero, sub_zero,
    Complex.ofReal_div, Complex.ofReal_one, Complex.ofReal_ofNat, Complex.ofReal_sum,
    Complex.re_sum] at hpair
  norm_num at hpair
  simp only [← Complex.ofReal_pow, Complex.ofReal_re] at hpair
  have hnonneg : ∀ i, 0 ≤ (inner ℂ (uFactor i ψ) (uFactor i ψ)).re := fun i => by
    have h := inner_self_nonneg (𝕜 := ℂ) (x := uFactor i ψ)
    exact h
  have hsum : (∑ i, (inner ℂ (uFactor i ψ) (uFactor i ψ)).re) =
      (inner ℂ (uFactor (Sum.inl 0) ψ) (uFactor (Sum.inl 0) ψ)).re +
        (inner ℂ (uFactor (Sum.inr 0) ψ) (uFactor (Sum.inr 0) ψ)).re +
        ∑ i : Fin 3, (inner ℂ (uFactor (Sum.inr i.succ) ψ) (uFactor (Sum.inr i.succ) ψ)).re := by
    rw [Fintype.sum_sum_type, Fin.sum_univ_one, Fin.sum_univ_succ]
    abel
  have hdrop : (∑ i, (inner ℂ (uFactor i ψ) (uFactor i ψ)).re) ≥
      (inner ℂ (uFactor (Sum.inl 0) ψ) (uFactor (Sum.inl 0) ψ)).re +
        (inner ℂ (uFactor (Sum.inr 0) ψ) (uFactor (Sum.inr 0) ψ)).re := by
    rw [hsum]
    exact le_add_of_nonneg_right (Finset.sum_nonneg fun i _ => hnonneg _)
  have hP : uFactor (Sum.inl 0) ψ = coreP 0 ψ := rfl
  have hF : uFactor (Sum.inr 0) ψ = uField0 ψ := rfl
  have hnorm_i : ∀ i, (inner ℂ (uFactor i ψ) (uFactor i ψ)).re = ‖uFactor i ψ‖ ^ 2 := fun i =>
    (by simpa only [RCLike.re_to_complex] using
      (inner_self_eq_norm_sq (𝕜 := ℂ) (x := uFactor i ψ)))
  have hPnorm : (inner ℂ (coreP 0 ψ) (coreP 0 ψ)).re = ‖coreP 0 ψ‖ ^ 2 := by
    simpa [hP] using hnorm_i (Sum.inl 0)
  have hFnorm : (inner ℂ (uField0 ψ) (uField0 ψ)).re = ‖uField0 ψ‖ ^ 2 := by
    simpa [hF] using hnorm_i (Sum.inr 0)
  have hdrop_norm : (∑ i, ‖uFactor i ψ‖ ^ 2) ≥
      ‖coreP 0 ψ‖ ^ 2 + ‖uField0 ψ‖ ^ 2 := by
    calc
      (∑ i, ‖uFactor i ψ‖ ^ 2) = ∑ i, (inner ℂ (uFactor i ψ) (uFactor i ψ)).re :=
        Finset.sum_congr rfl fun i _ => (hnorm_i i).symm
      _ ≥ (inner ℂ (uFactor (Sum.inl 0) ψ) (uFactor (Sum.inl 0) ψ)).re +
            (inner ℂ (uFactor (Sum.inr 0) ψ) (uFactor (Sum.inr 0) ψ)).re := hdrop
      _ = ‖coreP 0 ψ‖ ^ 2 + ‖uField0 ψ‖ ^ 2 := by rw [hP, hF, hPnorm, hFnorm]
  have hsum_norm : (∑ i, ‖uFactor i ψ‖ ^ 2) =
      ‖coreP 0 ψ‖ ^ 2 + ∑ x, ‖uFactor (Sum.inr x) ψ‖ ^ 2 := by
    calc
      (∑ i, ‖uFactor i ψ‖ ^ 2) = ∑ i, (inner ℂ (uFactor i ψ) (uFactor i ψ)).re :=
        Finset.sum_congr rfl fun i _ => (hnorm_i i).symm
      _ = (inner ℂ (uFactor (Sum.inl 0) ψ) (uFactor (Sum.inl 0) ψ)).re +
            (inner ℂ (uFactor (Sum.inr 0) ψ) (uFactor (Sum.inr 0) ψ)).re +
            ∑ i : Fin 3, (inner ℂ (uFactor (Sum.inr i.succ) ψ)
              (uFactor (Sum.inr i.succ) ψ)).re := hsum
      _ = ‖coreP 0 ψ‖ ^ 2 + ∑ x, ‖uFactor (Sum.inr x) ψ‖ ^ 2 := by
        conv_rhs => rw [Fin.sum_univ_succ]
        rw [hP, hF, hPnorm, hFnorm]
        rw [show (∑ i : Fin 3, (inner ℂ (uFactor (Sum.inr i.succ) ψ)
              (uFactor (Sum.inr i.succ) ψ)).re) =
            ∑ i : Fin 3, ‖uFactor (Sum.inr i.succ) ψ‖ ^ 2 from
          Finset.sum_congr rfl fun i _ => hnorm_i _]
        abel
  rw [hP] at hpair
  have henergy : (1 / 2) * (‖coreP 0 ψ‖ ^ 2 + ‖uField0 ψ‖ ^ 2) ≤
      (inner ℂ (ψ : L2d 4) (Model.innerHam unitMomCont ψ)).re := by
    rw [hpair]
    nlinarith [hdrop_norm, hsum_norm]
  have hfield := unit_field_norm ψ
  have hharm := harmonic_lower_bound (d := 4) 0 (α := (1 / 2 : ℝ)) (by norm_num) ψ
  have hnnQ : 0 ≤ ‖uFieldQ ψ‖ ^ 2 := sq_nonneg _
  nlinarith [henergy, hfield, hharm, hnnQ]


private theorem floor_on_closure {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    {D : Submodule ℂ F} (T : D →ₗ[ℂ] F) (hd : Dense (D : Set F)) (hs : SymmetricOn D T)
    (m : ℝ) (hm : ∀ ψ : D, m * ‖(ψ : F)‖ ^ 2 ≤ (inner ℂ (ψ : F) (T ψ)).re)
    (x : clDom T) : m * ‖(x : F)‖ ^ 2 ≤ (inner ℂ (x : F) (clExt T hd hs x)).re := by
  let S : Set (F × F) := {p | m * ‖p.1‖ ^ 2 ≤ (inner ℂ p.1 p.2).re}
  have hl : Continuous (fun p : F × F => m * ‖p.1‖ ^ 2) :=
    continuous_const.mul (continuous_fst.norm.pow 2)
  have hr : Continuous (fun p : F × F => (inner ℂ p.1 p.2).re) :=
    Complex.continuous_re.comp (continuous_fst.inner continuous_snd)
  have hclosed : IsClosed S := isClosed_le hl hr
  have hsub : (opGraph T : Set _) ⊆ S := by
    rintro _ ⟨ψ, rfl⟩
    exact hm ψ
  have hgraph : ((x : F), clFun T x) ∈ closure (opGraph T : Set _) := clFun_spec T x
  exact (closure_minimal hsub hclosed) hgraph

/-- The unit core estimate passes to every vector in the closed operator domain. -/
theorem unitMomCont_closure_floor (x : clDom unitMomCont.innerHam) :
    (7 / 64 : ℝ) * ‖(x : L2d 4)‖ ^ 2 ≤ FarisLavine.quadForm
      (clExt unitMomCont.innerHam (polyGaussCore_dense (d := 4)) unitMomCont.symmetric) x :=
  floor_on_closure unitMomCont.innerHam polyGaussCore_dense unitMomCont.symmetric
    (7 / 64) unitMomCont_inner_gap x

/-! ## The shifted-well comparison fails pointwise

The tempting even-sector estimate `V(φ) ≥ (λv²/4)(φ−v)²` cannot hold: at `φ = −v`
the double-well potential vanishes, while the shifted quadratic is `λv⁴ > 0`.
The correct even-sector analysis therefore needs a merged-well (quartic) estimate,
not a one-well quadratic comparison. -/

/-- The scalar double-well potential `(λ/4)(φ² − v²)²`. -/
noncomputable def contPotential (p : Parameters) (φ : ℝ) : ℝ :=
  (p.coupling / 4) * (φ ^ 2 - p.vev ^ 2) ^ 2

/-- The one-well quadratic lower bound around `φ = v` is false on the full line. -/
theorem shifted_well_comparison_false (p : Parameters) :
    ¬ ∀ φ : ℝ, contPotential p φ ≥ (p.coupling * p.vev ^ 2 / 4) * (φ - p.vev) ^ 2 := by
  intro h
  have hneg := h (-p.vev)
  have hpot : contPotential p (-p.vev) = 0 := by
    simp [contPotential]
  have hquad : (p.coupling * p.vev ^ 2 / 4) * (-p.vev - p.vev) ^ 2 =
      p.coupling * p.vev ^ 4 := by ring
  rw [hpot, hquad] at hneg
  have hpos : 0 < p.coupling * p.vev ^ 4 := mul_pos p.coupling_pos (pow_pos p.vev_pos 4)
  linarith

end BookProof.Phi4
