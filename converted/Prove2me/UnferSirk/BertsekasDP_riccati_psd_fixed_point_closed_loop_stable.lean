/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : f8cf4c1c-7ed4-445a-a59f-1103dd6d6c4f
* original name       : `BertsekasDP.riccati_psd_fixed_point_closed_loop_stable`
* title               : Closed-loop stability of a positive definite Riccati fixed point (Prop. 4.4.1, part 4, conditional form)
* statement author    : jackjburleson
* solution author     : salim (submission 56ced7bd-e18b-4268-8392-7504f55ca517,
                        accepted 2026-09-08T10:50:49.261747+00:00)
* source              : D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, Athena Scientific, 3rd ed., 2005, Section 4.4, Proposition 4.4.1 (part 4); J. C. Willems, Least squares stationary optimal control and the algebraic Riccati equation, IEEE Trans. Automat. Control 16 (1971), no. 6, 621–634.
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/unfer-sirk/BertsekasDP.riccati_psd_fixed_point_closed_loop_stable.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/BertsekasDP_riccati_psd_fixed_point_closed_loop_stable.diff`.
-/
import Mathlib
import Definitions.Def_BertsekasRiccatiMap

set_option autoImplicit false
open Matrix


open Matrix
namespace TrustRootW9Riccati
lemma lyapunov_identity {n m q : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (C : Matrix (Fin q) (Fin n) ℝ) (P : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q = Cᵀ * C) (hP : P.PosDef) (hR : R.PosDef)
    (hfix : BertsekasRiccatiMap A B Q R P = P) :
    let L := -((Bᵀ * P * B + R)⁻¹ * Bᵀ * P * A)
    let T := A + B * L
    P = Tᵀ * P * T + Cᵀ * C + Lᵀ * R * L := by
  let D := Bᵀ * P * B + R
  let L := -(D⁻¹ * Bᵀ * P * A)
  let T := A + B * L
  change P = Tᵀ * P * T + Cᵀ * C + Lᵀ * R * L
  have hD : D.PosDef := by
    simpa only [conjTranspose_eq_transpose_of_trivial] using
      hR.posSemidef_add (hP.posSemidef.conjTranspose_mul_mul_same B)
  have hinv : D * D⁻¹ = 1 := D.mul_nonsing_inv (D.isUnit_iff_isUnit_det.mp hD.isUnit)
  have hDL : D * L = -(Bᵀ * P * A) := by
    dsimp [L]
    simp only [Matrix.mul_neg, ← Matrix.mul_assoc, hinv, Matrix.one_mul]
  have hcancel : Lᵀ * (Bᵀ * P * A) + Lᵀ * (D * L) = 0 := by
    rw [hDL, Matrix.mul_neg, add_neg_cancel]
  have hric : BertsekasRiccatiMap A B Q R P = Aᵀ * P * A + Aᵀ * P * B * L + Q := by
    simp only [BertsekasRiccatiMap, L, D, Matrix.mul_sub, Matrix.sub_mul,
      Matrix.mul_neg, Matrix.neg_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc, sub_eq_add_neg]
  calc
    P = Aᵀ * P * A + Aᵀ * P * B * L + Q := hfix.symm.trans hric
    _ = Aᵀ * P * A + Aᵀ * P * B * L + Q +
        (Lᵀ * (Bᵀ * P * A) + Lᵀ * (D * L)) := by rw [hcancel, add_zero]
    _ = Tᵀ * P * T + Cᵀ * C + Lᵀ * R * L := by
      rw [hQ]
      simp only [T, D, Matrix.transpose_add, Matrix.transpose_mul,
        Matrix.add_mul, Matrix.mul_add, Matrix.mul_assoc]
      abel
end TrustRootW9Riccati


open Matrix
namespace TrustAlgebraW9Riccati

lemma re_mulVec {n m : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (v : Fin n → ℂ) :
    (fun i => ((M.map (algebraMap ℝ ℂ)) *ᵥ v) i |>.re) =
      M *ᵥ (fun i => (v i).re) := by
  ext i
  simp [Matrix.mulVec, dotProduct, Complex.mul_re]

lemma im_mulVec {n m : ℕ} (M : Matrix (Fin m) (Fin n) ℝ) (v : Fin n → ℂ) :
    (fun i => ((M.map (algebraMap ℝ ℂ)) *ᵥ v) i |>.im) =
      M *ᵥ (fun i => (v i).im) := by
  ext i
  simp [Matrix.mulVec, dotProduct, Complex.mul_im]

lemma quadratic_rotation {n : ℕ} (P : Matrix (Fin n) (Fin n) ℝ)
    (x y : Fin n → ℝ) (a b : ℝ) :
    (a • x - b • y) ⬝ᵥ (P *ᵥ (a • x - b • y)) +
      (b • x + a • y) ⬝ᵥ (P *ᵥ (b • x + a • y)) =
        (a ^ 2 + b ^ 2) * (x ⬝ᵥ (P *ᵥ x) + y ⬝ᵥ (P *ᵥ y)) := by
  simp only [Matrix.mulVec_sub, Matrix.mulVec_add, Matrix.mulVec_smul,
    dotProduct_sub, sub_dotProduct, dotProduct_add, add_dotProduct,
    smul_dotProduct, dotProduct_smul, smul_eq_mul]
  ring

lemma quadratic_identity {n m q : ℕ}
    (P T : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (C : Matrix (Fin q) (Fin n) ℝ) (L : Matrix (Fin m) (Fin n) ℝ)
    (hid : P = Tᵀ * P * T + Cᵀ * C + Lᵀ * R * L) (x : Fin n → ℝ) :
    x ⬝ᵥ (P *ᵥ x) = (T *ᵥ x) ⬝ᵥ (P *ᵥ (T *ᵥ x)) +
      (C *ᵥ x) ⬝ᵥ (C *ᵥ x) + (L *ᵥ x) ⬝ᵥ (R *ᵥ (L *ᵥ x)) := by
  conv_lhs => rw [hid]
  simp only [Matrix.add_mulVec, dotProduct_add, Matrix.mulVec_mulVec,
    dotProduct_mulVec, ← Matrix.vecMul_vecMul, vecMul_transpose]

theorem eigenvector_vanish {n m q : ℕ}
    (P T : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (C : Matrix (Fin q) (Fin n) ℝ) (L : Matrix (Fin m) (Fin n) ℝ)
    (hP : P.PosDef) (hR : R.PosDef)
    (hid : P = Tᵀ * P * T + Cᵀ * C + Lᵀ * R * L)
    (z : ℂ) (v : Fin n → ℂ)
    (hev : T.map (algebraMap ℝ ℂ) *ᵥ v = z • v) (hz : 1 ≤ ‖z‖) :
    C.map (algebraMap ℝ ℂ) *ᵥ v = 0 ∧ L.map (algebraMap ℝ ℂ) *ᵥ v = 0 := by
  let x : Fin n → ℝ := fun i => (v i).re
  let y : Fin n → ℝ := fun i => (v i).im
  have hevr : T *ᵥ x = z.re • x - z.im • y := by
    have h := congrArg (fun w : Fin n → ℂ => fun i => (w i).re) hev
    beta_reduce at h  -- conversion
    rw [re_mulVec] at h
    ext i
    simpa [x, y, Complex.mul_re, Pi.smul_apply, smul_eq_mul] using congrFun h i
  have hevi : T *ᵥ y = z.im • x + z.re • y := by
    have h := congrArg (fun w : Fin n → ℂ => fun i => (w i).im) hev
    beta_reduce at h  -- conversion
    rw [im_mulVec] at h
    ext i
    simpa [x, y, Complex.mul_im, Pi.smul_apply, smul_eq_mul, add_comm] using congrFun h i
  have hPx : 0 ≤ x ⬝ᵥ (P *ᵥ x) := by simpa using hP.posSemidef.dotProduct_mulVec_nonneg x
  have hPy : 0 ≤ y ⬝ᵥ (P *ᵥ y) := by simpa using hP.posSemidef.dotProduct_mulVec_nonneg y
  have hCx : 0 ≤ (C *ᵥ x) ⬝ᵥ (C *ᵥ x) := by simpa using dotProduct_star_self_nonneg (C *ᵥ x)
  have hCy : 0 ≤ (C *ᵥ y) ⬝ᵥ (C *ᵥ y) := by simpa using dotProduct_star_self_nonneg (C *ᵥ y)
  have hLx : 0 ≤ (L *ᵥ x) ⬝ᵥ (R *ᵥ (L *ᵥ x)) := by simpa using hR.posSemidef.dotProduct_mulVec_nonneg (L *ᵥ x)
  have hLy : 0 ≤ (L *ᵥ y) ⬝ᵥ (R *ᵥ (L *ᵥ y)) := by simpa using hR.posSemidef.dotProduct_mulVec_nonneg (L *ᵥ y)
  have hix := quadratic_identity P T R C L hid x
  have hiy := quadratic_identity P T R C L hid y
  have hrot := quadratic_rotation P x y z.re z.im
  rw [← hevr, ← hevi] at hrot
  have hnorm : 1 ≤ z.re ^ 2 + z.im ^ 2 := by
    have hsq := Complex.sq_norm z
    rw [Complex.normSq_apply] at hsq
    nlinarith
  have hprod := mul_nonneg (sub_nonneg.mpr hnorm) (add_nonneg hPx hPy)
  have hzero : (C *ᵥ x) ⬝ᵥ (C *ᵥ x) + (C *ᵥ y) ⬝ᵥ (C *ᵥ y) +
      (L *ᵥ x) ⬝ᵥ (R *ᵥ (L *ᵥ x)) + (L *ᵥ y) ⬝ᵥ (R *ᵥ (L *ᵥ y)) = 0 := by
    nlinarith
  have hcx : C *ᵥ x = 0 := dotProduct_self_eq_zero.mp (by linarith)
  have hcy : C *ᵥ y = 0 := dotProduct_self_eq_zero.mp (by linarith)
  have hlx : L *ᵥ x = 0 := by
    by_contra h
    have hp : 0 < (L *ᵥ x) ⬝ᵥ (R *ᵥ (L *ᵥ x)) := by simpa using hR.dotProduct_mulVec_pos h
    linarith
  have hly : L *ᵥ y = 0 := by
    by_contra h
    have hp : 0 < (L *ᵥ y) ⬝ᵥ (R *ᵥ (L *ᵥ y)) := by simpa using hR.dotProduct_mulVec_pos h
    linarith
  constructor
  · ext i
    apply Complex.ext
    · simpa [x, hcx] using congrFun (re_mulVec C v) i
    · simpa [y, hcy] using congrFun (im_mulVec C v) i
  · ext i
    apply Complex.ext
    · simpa [x, hlx] using congrFun (re_mulVec L v) i
    · simpa [y, hly] using congrFun (im_mulVec L v) i

end TrustAlgebraW9Riccati


open Matrix

namespace TrustGraphW9Riccati

lemma complex_left_kernel_eq_zero {n : ℕ} {ι : Type*} [Fintype ι]
    (M : Matrix (Fin n) ι ℝ) (hrank : M.rank = n)
    (v : Fin n → ℂ) (hv : v ᵥ* M.map (algebraMap ℝ ℂ) = 0) : v = 0 := by
  have hlin : LinearIndependent ℝ M.row := by
    apply linearIndependent_iff_card_eq_finrank_span.mpr
    simpa only [Set.finrank, ← M.rank_eq_finrank_span_row, Fintype.card_fin] using hrank.symm
  have hinj : Function.Injective M.vecMul := Matrix.vecMul_injective_iff.mpr hlin
  have hre : (fun i => (v i).re) ᵥ* M = 0 := by
    funext j
    have h := congrArg Complex.re (congrFun hv j)
    simpa [Matrix.vecMul, dotProduct, Complex.mul_re] using h
  have him : (fun i => (v i).im) ᵥ* M = 0 := by
    funext j
    have h := congrArg Complex.im (congrFun hv j)
    simpa [Matrix.vecMul, dotProduct, Complex.mul_im] using h
  have hre0 : (fun i => (v i).re) = 0 := hinj (by simpa using hre)
  have him0 : (fun i => (v i).im) = 0 := hinj (by simpa using him)
  funext i
  apply Complex.ext
  · exact congrFun hre0 i
  · exact congrFun him0 i

lemma eigenvector_pow {n : ℕ} (A : Matrix (Fin n) (Fin n) ℂ)
    (z : ℂ) (v : Fin n → ℂ) (h : A *ᵥ v = z • v) (j : ℕ) :
    A ^ j *ᵥ v = z ^ j • v := by
  induction j with
  | zero => simp
  | succ j ih =>
    rw [pow_succ', ← Matrix.mulVec_mulVec, ih, Matrix.mulVec_smul, h, smul_smul, pow_succ]

lemma observable_eigenvector_eq_zero {n q : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin q) (Fin n) ℝ)
    (hobs : BertsekasObservablePair A C) (z : ℂ) (v : Fin n → ℂ)
    (hev : A.map (algebraMap ℝ ℂ) *ᵥ v = z • v)
    (hCv : C.map (algebraMap ℝ ℂ) *ᵥ v = 0) : v = 0 := by
  let M : Matrix (Fin n) (Fin n × Fin q) ℝ :=
    Matrix.of fun i p => (Aᵀ ^ (p.1 : ℕ) * Cᵀ) i p.2
  have hrank : M.rank = n := hobs
  have hz (j : ℕ) : (C * A ^ j).map (algebraMap ℝ ℂ) *ᵥ v = 0 := by
    rw [Matrix.map_mul, Matrix.map_pow, ← Matrix.mulVec_mulVec,
      eigenvector_pow _ z v hev, Matrix.mulVec_smul, hCv, smul_zero]
  have hk : v ᵥ* M.map (algebraMap ℝ ℂ) = 0 := by
    funext p
    have h := congrFun (hz p.1.val) p.2
    simpa [M, Matrix.vecMul, Matrix.mulVec, dotProduct,
      ← Matrix.transpose_mul, ← Matrix.transpose_pow, mul_comm] using h
  exact complex_left_kernel_eq_zero M hrank v hk

lemma observable_eigenvector_ne_zero {n q : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin q) (Fin n) ℝ)
    (hobs : BertsekasObservablePair A C) (z : ℂ) (v : Fin n → ℂ)
    (hv : v ≠ 0) (hev : A.map (algebraMap ℝ ℂ) *ᵥ v = z • v) :
    C.map (algebraMap ℝ ℂ) *ᵥ v ≠ 0 := by
  intro hCv
  exact hv (observable_eigenvector_eq_zero A C hobs z v hev hCv)

end TrustGraphW9Riccati



open Matrix

namespace TrustScoutW9RiccatiSpectrum

lemma exists_complex_eigenvector {n : ℕ}
    (T : Matrix (Fin n) (Fin n) ℝ) (z : ℂ)
    (hz : z ∈ spectrum ℂ (T.map (algebraMap ℝ ℂ))) :
    ∃ v : Fin n → ℂ, v ≠ 0 ∧
      (T.map (algebraMap ℝ ℂ)) *ᵥ v = z • v := by
  have hz' : z ∈ spectrum ℂ (T.map (algebraMap ℝ ℂ)).toLin' := by
    simpa only [Matrix.spectrum_toLin'] using hz
  obtain ⟨v, hv⟩ :=
    (Module.End.HasEigenvalue.of_mem_spectrum hz').exists_hasEigenvector
  exact ⟨v, hv.2, hv.apply_eq_smul⟩

end TrustScoutW9RiccatiSpectrum


theorem _root_.Prove2me.Solution.BertsekasDP_riccati_psd_fixed_point_closed_loop_stable {n m q : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (C : Matrix (Fin q) (Fin n) ℝ)
    (hQ : Q = Cᵀ * C) (hQpsd : Q.PosSemidef) (hR : R.PosDef)
    (hctrb : BertsekasControllablePair A B)
    (hobs : BertsekasObservablePair A C)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef)
    (hfix : BertsekasRiccatiMap A B Q R P = P) :
    ∀ z ∈ spectrum ℂ
          ((A + B * (-((Bᵀ * P * B + R)⁻¹ * Bᵀ * P * A))).map
            (algebraMap ℝ ℂ)),
        ‖z‖ < 1 := by
  let L := -((Bᵀ * P * B + R)⁻¹ * Bᵀ * P * A)
  let T := A + B * L
  have hid : P = Tᵀ * P * T + Cᵀ * C + Lᵀ * R * L :=
    TrustRootW9Riccati.lyapunov_identity A B Q R C P hQ hP hR hfix
  intro z hz
  by_contra hn
  have hnorm : 1 ≤ ‖z‖ := le_of_not_gt hn
  obtain ⟨v, hv, hev⟩ := TrustScoutW9RiccatiSpectrum.exists_complex_eigenvector T z hz
  obtain ⟨hCv, hLv⟩ := TrustAlgebraW9Riccati.eigenvector_vanish P T R C L hP hR hid z v hev hnorm
  have hAv : A.map (algebraMap ℝ ℂ) *ᵥ v = z • v := by
    simpa only [T, Matrix.map_add _ (map_add (algebraMap ℝ ℂ)), Matrix.map_mul, Matrix.add_mulVec,
      ← Matrix.mulVec_mulVec, hLv, Matrix.mulVec_zero, add_zero] using hev
  exact hv (TrustGraphW9Riccati.observable_eigenvector_eq_zero A C hobs z v hAv hCv)



#print axioms _root_.Prove2me.Solution.BertsekasDP_riccati_psd_fixed_point_closed_loop_stable

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open Matrix

namespace BertsekasDP

theorem riccati_psd_fixed_point_closed_loop_stable {n m q : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (C : Matrix (Fin q) (Fin n) ℝ)
    (hQ : Q = Cᵀ * C) (hQpsd : Q.PosSemidef) (hR : R.PosDef)
    (hctrb : BertsekasControllablePair A B)
    (hobs : BertsekasObservablePair A C)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosDef)
    (hfix : BertsekasRiccatiMap A B Q R P = P) :
    ∀ z ∈ spectrum ℂ
          ((A + B * (-((Bᵀ * P * B + R)⁻¹ * Bᵀ * P * A))).map
            (algebraMap ℝ ℂ)),
        ‖z‖ < 1 := by
  first
  | exact _root_.Prove2me.Solution.BertsekasDP_riccati_psd_fixed_point_closed_loop_stable A B Q R C hQ hQpsd hR hctrb hobs P hP hfix
  | (apply _root_.Prove2me.Solution.BertsekasDP_riccati_psd_fixed_point_closed_loop_stable <;> assumption)

end BertsekasDP


end Prove2meStatement
