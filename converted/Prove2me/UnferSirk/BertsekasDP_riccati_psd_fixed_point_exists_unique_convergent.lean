/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : c34225cc-57e1-4056-b261-9d914d26f498
* original name       : `BertsekasDP.riccati_psd_fixed_point_exists_unique_convergent`
* title               : Riccati iteration: existence, uniqueness, and global attraction of the positive definite fixed point (Prop. 4.4.1, parts 1–3)
* statement author    : jackjburleson
* solution author     : olivier (submission 668e0d3c-ad07-43d0-9516-2db5f56001ac,
                        accepted 2026-09-08T23:32:36.799261+00:00)
* source              : D. P. Bertsekas, Dynamic Programming and Optimal Control, Vol. I, Athena Scientific, 3rd ed., 2005, Section 4.4, Proposition 4.4.1 (parts 1–3); cf. J. C. Willems, Least squares stationary optimal control and the algebraic Riccati equation, IEEE Trans. Automat. Control 16 (1971), no. 6, 621–634.
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/unfer-sirk/BertsekasDP.riccati_psd_fixed_point_exists_unique_convergent.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/BertsekasDP_riccati_psd_fixed_point_exists_unique_convergent.diff`.
-/
import Mathlib
import Definitions.Def_BertsekasRiccatiMap

set_option autoImplicit false

open Matrix

namespace RiccatiWork

variable {n m : ℕ}

/-- Le gain associe a `P` : `L*(P) = -(BᵀPB + R)⁻¹ BᵀP A`. -/
noncomputable def optGain (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (R : Matrix (Fin m) (Fin m) ℝ) (P : Matrix (Fin n) (Fin n) ℝ) :
    Matrix (Fin m) (Fin n) ℝ :=
  -((Bᵀ * P * B + R)⁻¹ * (Bᵀ * P * A))

/-- Cout d'un pas sous le gain constant `L` :
`G(P,L) = (A+BL)ᵀ P (A+BL) + Q + Lᵀ R L`. -/
noncomputable def stepCost (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (L : Matrix (Fin m) (Fin n) ℝ) :
    Matrix (Fin n) (Fin n) ℝ :=
  (A + B * L)ᵀ * P * (A + B * L) + Q + Lᵀ * R * L

/-- Completion du carre, forme abstraite. -/
lemma completion_square (D : Matrix (Fin m) (Fin m) ℝ) (S : Matrix (Fin m) (Fin n) ℝ)
    (L : Matrix (Fin m) (Fin n) ℝ) (hDsymm : Dᵀ = D) (hD : IsUnit D.det) :
    (L + D⁻¹ * S)ᵀ * D * (L + D⁻¹ * S)
      = Lᵀ * D * L + Lᵀ * S + Sᵀ * L + Sᵀ * D⁻¹ * S := by
  have hinvsymm : (D⁻¹)ᵀ = D⁻¹ := by rw [Matrix.transpose_nonsing_inv, hDsymm]
  simp only [transpose_add, transpose_mul, hinvsymm, Matrix.add_mul, Matrix.mul_add,
    Matrix.mul_assoc, Matrix.mul_nonsing_inv_cancel_left _ _ hD,
    Matrix.nonsing_inv_mul_cancel_left _ _ hD]
  abel

/-- Identite fondamentale (Bertsekas, Vol. I, §4.1) :
`G(P,L) = F(P) + (L - L*(P))ᵀ D (L - L*(P))`, avec `D = BᵀPB + R`.
Elle fait de `F(P)` le minimum de `G(P,·)`, atteint en `L*(P)`. -/
lemma stepCost_eq_riccati_add
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (L : Matrix (Fin m) (Fin n) ℝ)
    (hPsymm : Pᵀ = P) (hRsymm : Rᵀ = R)
    (hD : IsUnit (Bᵀ * P * B + R).det) :
    stepCost A B Q R P L
      = BertsekasRiccatiMap A B Q R P
        + (L - optGain A B R P)ᵀ * (Bᵀ * P * B + R) * (L - optGain A B R P) := by
  have hDsymm : (Bᵀ * P * B + R)ᵀ = Bᵀ * P * B + R := by
    simp [transpose_add, transpose_mul, Matrix.mul_assoc, hPsymm, hRsymm]
  have key := completion_square (Bᵀ * P * B + R) (Bᵀ * P * A) L hDsymm hD
  simp only [optGain, sub_neg_eq_add]
  rw [key]
  simp only [stepCost, BertsekasRiccatiMap, transpose_add, transpose_mul, transpose_transpose,
    Matrix.add_mul, Matrix.mul_add, Matrix.sub_mul, Matrix.mul_sub, Matrix.mul_assoc, hPsymm]
  abel

/-- `D = BᵀPB + R` est definie positive des que `P ⪰ 0` et `R ≻ 0`. -/
lemma riccatiD_posDef (B : Matrix (Fin n) (Fin m) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (hP : P.PosSemidef) (hR : R.PosDef) :
    (Bᵀ * P * B + R).PosDef := by
  have h1 : (Bᵀ * P * B).PosSemidef := by
    have := hP.conjTranspose_mul_mul_same B
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using this
  simpa [add_comm] using hR.add_posSemidef h1

/-- Le minimum de `G(P,·)` est atteint en `L*(P)`, ou il vaut `F(P)`. -/
lemma stepCost_optGain
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ)
    (hPsymm : Pᵀ = P) (hRsymm : Rᵀ = R)
    (hD : IsUnit (Bᵀ * P * B + R).det) :
    stepCost A B Q R P (optGain A B R P) = BertsekasRiccatiMap A B Q R P := by
  rw [stepCost_eq_riccati_add A B Q R P _ hPsymm hRsymm hD]
  simp

/-- `G(P,L)` domine `F(P)` : le terme d'ecart est un carre. -/
lemma riccati_le_stepCost
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (L : Matrix (Fin m) (Fin n) ℝ)
    (hP : P.PosSemidef) (hR : R.PosDef) :
    (stepCost A B Q R P L - BertsekasRiccatiMap A B Q R P).PosSemidef := by
  have hDpd := riccatiD_posDef B R P hP hR
  have hD : IsUnit (Bᵀ * P * B + R).det := (Matrix.isUnit_iff_isUnit_det _).mp hDpd.isUnit
  have hPsymm : Pᵀ = P := hP.isHermitian
  have hRsymm : Rᵀ = R := hR.isHermitian
  rw [stepCost_eq_riccati_add A B Q R P L hPsymm hRsymm hD]
  have : BertsekasRiccatiMap A B Q R P
      + (L - optGain A B R P)ᵀ * (Bᵀ * P * B + R) * (L - optGain A B R P)
      - BertsekasRiccatiMap A B Q R P
      = (L - optGain A B R P)ᵀ * (Bᵀ * P * B + R) * (L - optGain A B R P) := by abel
  rw [this]
  have := hDpd.posSemidef.conjTranspose_mul_mul_same (L - optGain A B R P)
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using this

/-- `G(·,L)` est croissante en `P` : l'ecart est une congruence. -/
lemma stepCost_mono_in_P
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (P P' : Matrix (Fin n) (Fin n) ℝ) (L : Matrix (Fin m) (Fin n) ℝ)
    (hle : (P' - P).PosSemidef) :
    (stepCost A B Q R P' L - stepCost A B Q R P L).PosSemidef := by
  have e : stepCost A B Q R P' L - stepCost A B Q R P L
      = (A + B * L)ᵀ * (P' - P) * (A + B * L) := by
    simp only [stepCost, Matrix.mul_sub, Matrix.sub_mul]
    abel
  rw [e]
  have := hle.conjTranspose_mul_mul_same (A + B * L)
  simpa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using this

/-- **Monotonie de l'operateur de Riccati** sur le cone semi-defini positif
(Bertsekas, Vol. I, §4.1) : `0 ⪯ P ⪯ P'` entraine `F(P) ⪯ F(P')`. -/
lemma riccati_mono
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (P P' : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosSemidef) (hP' : P'.PosSemidef) (hR : R.PosDef)
    (hle : (P' - P).PosSemidef) :
    (BertsekasRiccatiMap A B Q R P' - BertsekasRiccatiMap A B Q R P).PosSemidef := by
  have hD' : IsUnit (Bᵀ * P' * B + R).det := (Matrix.isUnit_iff_isUnit_det _).mp (riccatiD_posDef B R P' hP' hR).isUnit
  have e1 : BertsekasRiccatiMap A B Q R P' = stepCost A B Q R P' (optGain A B R P') :=
    (stepCost_optGain A B Q R P' hP'.isHermitian hR.isHermitian hD').symm
  have e2 := stepCost_mono_in_P A B Q R P P' (optGain A B R P') hle
  have e3 := riccati_le_stepCost A B Q R P (optGain A B R P') hP hR
  have e : BertsekasRiccatiMap A B Q R P' - BertsekasRiccatiMap A B Q R P
      = (stepCost A B Q R P' (optGain A B R P') - stepCost A B Q R P (optGain A B R P'))
        + (stepCost A B Q R P (optGain A B R P') - BertsekasRiccatiMap A B Q R P) := by
    rw [e1]; abel
  rw [e]
  exact e2.add e3

/-- `F` preserve le cone semi-defini positif. -/
lemma riccati_posSemidef
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hR : R.PosDef) :
    (BertsekasRiccatiMap A B Q R P).PosSemidef := by
  have hD : IsUnit (Bᵀ * P * B + R).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (riccatiD_posDef B R P hP hR).isUnit
  rw [← stepCost_optGain A B Q R P hP.isHermitian hR.isHermitian hD]
  set L := optGain A B R P
  have h1 : ((A + B * L)ᵀ * P * (A + B * L)).PosSemidef := by
    have := hP.conjTranspose_mul_mul_same (A + B * L)
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using this
  have h2 : (Lᵀ * R * L).PosSemidef := by
    have := hR.posSemidef.conjTranspose_mul_mul_same L
    simpa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using this
  exact (h1.add hQ).add h2

/-- Les iterees `F^k(0)` sont semi-definies positives. -/
lemma iterate_posSemidef
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (hQ : Q.PosSemidef) (hR : R.PosDef) (k : ℕ) :
    ((BertsekasRiccatiMap A B Q R)^[k] 0).PosSemidef := by
  induction k with
  | zero => simpa using (Matrix.PosSemidef.zero (n := Fin n) (R := ℝ))
  | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact riccati_posSemidef A B Q R _ ih hQ hR

/-- **La suite `F^k(0)` est croissante** : demarree en `0`, elle monte
puisque `F(0) = Q ⪰ 0` et que `F` est monotone. -/
lemma iterate_mono_succ
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (hQ : Q.PosSemidef) (hR : R.PosDef) (k : ℕ) :
    ((BertsekasRiccatiMap A B Q R)^[k + 1] 0 - (BertsekasRiccatiMap A B Q R)^[k] 0).PosSemidef := by
  induction k with
  | zero =>
      have h0 : BertsekasRiccatiMap A B Q R 0 = Q := by
        simp [BertsekasRiccatiMap]
      simp only [zero_add, Function.iterate_one, Function.iterate_zero, id_eq, h0, sub_zero]
      exact hQ
  | succ k ih =>
      have hk1 : (BertsekasRiccatiMap A B Q R ((BertsekasRiccatiMap A B Q R)^[k] 0)).PosSemidef := by
        have := iterate_posSemidef A B Q R hQ hR (k + 1)
        rwa [Function.iterate_succ_apply' (f := BertsekasRiccatiMap A B Q R) (n := k)] at this
      rw [Function.iterate_succ_apply' (f := BertsekasRiccatiMap A B Q R) (n := k)] at ih
      rw [Function.iterate_succ_apply' (n := k + 1), Function.iterate_succ_apply' (n := k)]
      exact riccati_mono A B Q R _ _
        (iterate_posSemidef A B Q R hQ hR k) hk1 hR ih

/-- Congruence sur les formes quadratiques. -/
lemma quad_congr {k : ℕ} (N : Matrix (Fin n) (Fin n) ℝ) (M : Matrix (Fin n) (Fin k) ℝ)
    (x : Fin k → ℝ) :
    x ⬝ᵥ ((Mᵀ * N * M) *ᵥ x) = (M *ᵥ x) ⬝ᵥ (N *ᵥ (M *ᵥ x)) := by
  simp only [← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose]

/-- Forme quadratique d'une matrice semi-definie positive. -/
lemma quad_nonneg {M : Matrix (Fin n) (Fin n) ℝ} (hM : M.PosSemidef) (x : Fin n → ℝ) :
    0 ≤ x ⬝ᵥ (M *ᵥ x) := by
  simpa using hM.dotProduct_mulVec_nonneg x

/-- Comparaison de formes quadratiques induite par une difference PSD. -/
lemma quad_le_of_sub_posSemidef {M N : Matrix (Fin n) (Fin n) ℝ}
    (h : (N - M).PosSemidef) (x : Fin n → ℝ) :
    x ⬝ᵥ (M *ᵥ x) ≤ x ⬝ᵥ (N *ᵥ x) := by
  have := quad_nonneg h x
  simp only [Matrix.sub_mulVec, dotProduct_sub, sub_nonneg] at this
  exact this

/-- **Inegalite de programmation dynamique.** Pour tout etat `x` et toute commande `u`,
`xᵀ F(P) x ≤ (Ax+Bu)ᵀ P (Ax+Bu) + xᵀQx + uᵀRu`. C'est la forme faible du principe
d'optimalite : `F(P)` est le minimum sur `u`, donc majore par n'importe quel choix. -/
lemma dp_inequality
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ)
    (hP : P.PosSemidef) (hQ : Q.PosSemidef) (hR : R.PosDef)
    (x : Fin n → ℝ) (u : Fin m → ℝ) :
    x ⬝ᵥ (BertsekasRiccatiMap A B Q R P *ᵥ x)
      ≤ (A *ᵥ x + B *ᵥ u) ⬝ᵥ (P *ᵥ (A *ᵥ x + B *ᵥ u))
        + x ⬝ᵥ (Q *ᵥ x) + u ⬝ᵥ (R *ᵥ u) := by
  by_cases hx : x = 0
  · subst hx
    have h1 : (0 : Fin n → ℝ) ⬝ᵥ (BertsekasRiccatiMap A B Q R P *ᵥ 0) = 0 := by simp
    rw [h1]
    have hb : 0 ≤ (A *ᵥ (0 : Fin n → ℝ) + B *ᵥ u) ⬝ᵥ (P *ᵥ (A *ᵥ (0 : Fin n → ℝ) + B *ᵥ u)) :=
      quad_nonneg hP _
    have hq : (0 : Fin n → ℝ) ⬝ᵥ (Q *ᵥ (0 : Fin n → ℝ)) = 0 := by simp
    have hr : 0 ≤ u ⬝ᵥ (R *ᵥ u) := quad_nonneg hR.posSemidef u
    rw [hq]
    linarith
  · -- `L` realise `L x = u`
    have hxx : x ⬝ᵥ x ≠ 0 := by
      simpa [dotProduct_self_eq_zero] using hx
    set L : Matrix (Fin m) (Fin n) ℝ := (x ⬝ᵥ x)⁻¹ • Matrix.vecMulVec u x with hL
    have hLx : L *ᵥ x = u := by
      rw [hL, Matrix.smul_mulVec]
      have : Matrix.vecMulVec u x *ᵥ x = (x ⬝ᵥ x) • u := by
        simpa using Matrix.vecMulVec_mulVec u x x
      rw [this, smul_smul, inv_mul_cancel₀ hxx, one_smul]
    have hstep := quad_le_of_sub_posSemidef (riccati_le_stepCost A B Q R P L hP hR) x
    refine hstep.trans_eq ?_
    have hABL : (A + B * L) *ᵥ x = A *ᵥ x + B *ᵥ u := by
      rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hLx]
    simp only [stepCost, Matrix.add_mulVec, dotProduct_add, quad_congr, hABL, hLx]

/-- **Deroulement sur `k` etapes.** Pour toute trajectoire admissible partant de
`traj 0`, la forme quadratique de `F^k(0)` est majoree par le cout accumule sur
`k` etapes. C'est l'inegalite de programmation dynamique iteree : `F^k(0)` est le
cout optimal a horizon `k` avec cout terminal nul, donc majore par le cout de
n'importe quelle suite de commandes. -/
lemma iterate_quad_le
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (hQ : Q.PosSemidef) (hR : R.PosDef) (k : ℕ) :
    ∀ (traj : ℕ → Fin n → ℝ) (ctrl : ℕ → Fin m → ℝ),
      (∀ j, traj (j + 1) = A *ᵥ traj j + B *ᵥ ctrl j) →
      traj 0 ⬝ᵥ ((BertsekasRiccatiMap A B Q R)^[k] 0 *ᵥ traj 0)
        ≤ ∑ j ∈ Finset.range k, (traj j ⬝ᵥ (Q *ᵥ traj j) + ctrl j ⬝ᵥ (R *ᵥ ctrl j)) := by
  induction k with
  | zero => intro traj ctrl _; simp
  | succ k ih =>
      intro traj ctrl hdyn
      have hPk : ((BertsekasRiccatiMap A B Q R)^[k] 0).PosSemidef :=
        iterate_posSemidef A B Q R hQ hR k
      have hstep : traj 0 ⬝ᵥ ((BertsekasRiccatiMap A B Q R)^[k + 1] 0 *ᵥ traj 0)
          ≤ traj 1 ⬝ᵥ ((BertsekasRiccatiMap A B Q R)^[k] 0 *ᵥ traj 1)
            + traj 0 ⬝ᵥ (Q *ᵥ traj 0) + ctrl 0 ⬝ᵥ (R *ᵥ ctrl 0) := by
        rw [Function.iterate_succ_apply' (f := BertsekasRiccatiMap A B Q R) (n := k)]
        have := dp_inequality A B Q R _ hPk hQ hR (traj 0) (ctrl 0)
        rwa [← hdyn 0] at this
      have htail := ih (fun j => traj (j + 1)) (fun j => ctrl (j + 1)) (fun j => hdyn (j + 1))
      -- `htail` porte deja sur la trajectoire decalee
      rw [Finset.sum_range_succ']
      linarith

/-- Trajectoire engendree par une suite de commandes depuis l'etat `x₀`. -/
noncomputable def stateFrom (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (x₀ : Fin n → ℝ) (u : ℕ → Fin m → ℝ) : ℕ → Fin n → ℝ
  | 0 => x₀
  | j + 1 => A *ᵥ stateFrom A B x₀ u j + B *ᵥ u j

lemma stateFrom_zero (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (x₀ : Fin n → ℝ) (u : ℕ → Fin m → ℝ) : stateFrom A B x₀ u 0 = x₀ := rfl

lemma stateFrom_succ (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (x₀ : Fin n → ℝ) (u : ℕ → Fin m → ℝ) (j : ℕ) :
    stateFrom A B x₀ u (j + 1) = A *ᵥ stateFrom A B x₀ u j + B *ᵥ u j := rfl

/-- La trajectoire au temps `k` ne depend des commandes que sur `[0, k)`. -/
lemma stateFrom_congr (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (x₀ : Fin n → ℝ) (u u' : ℕ → Fin m → ℝ) (k : ℕ)
    (h : ∀ j < k, u j = u' j) :
    stateFrom A B x₀ u k = stateFrom A B x₀ u' k := by
  induction k with
  | zero => rfl
  | succ k ih =>
      rw [stateFrom_succ, stateFrom_succ, ih (fun j hj => h j (by omega)), h k (by omega)]

/-- Decomposition affine : la trajectoire est la reponse libre plus la reponse forcee. -/
lemma stateFrom_split (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (x₀ : Fin n → ℝ) (u : ℕ → Fin m → ℝ) (k : ℕ) :
    stateFrom A B x₀ u k = (A ^ k) *ᵥ x₀ + stateFrom A B 0 u k := by
  induction k with
  | zero => simp [stateFrom_zero]
  | succ k ih =>
      rw [stateFrom_succ, stateFrom_succ, ih, Matrix.mulVec_add, Matrix.mulVec_mulVec,
        ← pow_succ']
      abel

/-- **La reponse forcee atteint toute combinaison `Σ_{i<k} Aⁱ B wᵢ`.** -/
lemma stateFrom_reach (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (k : ℕ) (w : ℕ → Fin m → ℝ) :
    ∃ u : ℕ → Fin m → ℝ,
      stateFrom A B 0 u k = ∑ i ∈ Finset.range k, (A ^ i * B) *ᵥ w i := by
  induction k generalizing w with
  | zero => exact ⟨fun _ => 0, by simp [stateFrom_zero]⟩
  | succ k ih =>
      obtain ⟨u', hu'⟩ := ih (fun i => w (i + 1))
      refine ⟨fun j => if j = k then w 0 else u' j, ?_⟩
      rw [stateFrom_succ]
      have hcong : stateFrom A B 0 (fun j => if j = k then w 0 else u' j) k
          = stateFrom A B 0 u' k :=
        stateFrom_congr A B 0 _ _ k (fun j hj => by simp [Nat.ne_of_lt hj])
      rw [hcong, hu', if_pos rfl]
      rw [Matrix.mulVec_sum]
      rw [Finset.sum_range_succ']
      simp only [pow_zero, Matrix.one_mul]
      congr 1
      refine Finset.sum_congr rfl (fun i _ => ?_)
      rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, ← pow_succ']

/-- La matrice de controlabilite agit comme la somme des `Aⁱ B`. -/
lemma ctrb_mulVec (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (w : Fin n × Fin m → ℝ) :
    (Matrix.of fun (i : Fin n) (p : Fin n × Fin m) => (A ^ (p.1 : ℕ) * B) i p.2) *ᵥ w
      = ∑ a : Fin n, (A ^ (a : ℕ) * B) *ᵥ (fun b => w (a, b)) := by
  funext i
  simp only [Matrix.mulVec, Matrix.of_apply, dotProduct, Finset.sum_apply]
  rw [Fintype.sum_prod_type]

/-- **La controlabilite annule l'etat en `n` pas.** Pour tout etat initial il existe
une suite de commandes, nulle au-dela de `n`, dont la trajectoire est nulle a partir
de l'instant `n`. -/
lemma exists_deadbeat (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (hctrb : BertsekasControllablePair A B) (x₀ : Fin n → ℝ) :
    ∃ u : ℕ → Fin m → ℝ, (∀ j, n ≤ j → u j = 0) ∧ ∀ j, n ≤ j → stateFrom A B x₀ u j = 0 := by
  -- rang plein : l'application `w ↦ Ctrb w` est surjective
  set Ctrb : Matrix (Fin n) (Fin n × Fin m) ℝ :=
    Matrix.of fun (i : Fin n) (p : Fin n × Fin m) => (A ^ (p.1 : ℕ) * B) i p.2 with hCtrb
  have hsurj : Function.Surjective (fun w => Ctrb *ᵥ w) := by
    have hr : LinearMap.range Ctrb.mulVecLin = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [← Matrix.rank, hctrb]
      simp
    intro y
    obtain ⟨w, hw⟩ := LinearMap.range_eq_top.mp hr y
    exact ⟨w, hw⟩
  obtain ⟨w, hw⟩ := hsurj (-((A ^ n) *ᵥ x₀))
  -- la reponse forcee atteint la valeur voulue
  obtain ⟨u, hu⟩ := stateFrom_reach A B n (fun i => if h : i < n then (fun b => w (⟨i, h⟩, b)) else 0)
  have hsum : stateFrom A B 0 u n = -((A ^ n) *ᵥ x₀) := by
    rw [hu, ← hw]
    show _ = Ctrb *ᵥ w
    rw [hCtrb, ctrb_mulVec]
    rw [← Fin.sum_univ_eq_sum_range (fun i => (A ^ i * B) *ᵥ
      (if h : i < n then (fun b => w (⟨i, h⟩, b)) else 0))]
    exact Finset.sum_congr rfl (fun a _ => by simp [a.isLt])
  -- on tronque les commandes au-dela de `n`
  refine ⟨fun j => if j < n then u j else 0, fun j hj => by simp [Nat.not_lt.mpr hj], ?_⟩
  have hn : stateFrom A B x₀ (fun j => if j < n then u j else 0) n = 0 := by
    rw [stateFrom_congr A B x₀ _ u n (fun j hj => by simp [hj]), stateFrom_split, hsum]
    abel
  intro j hj
  obtain ⟨d, rfl⟩ := Nat.exists_eq_add_of_le hj
  induction d with
  | zero => simpa using hn
  | succ d ihd =>
      rw [show n + (d + 1) = (n + d) + 1 by omega, stateFrom_succ,
        ihd (by omega), if_neg (by omega)]
      simp

/-- Une somme partielle d'une suite positive nulle au-dela de `N` est majoree par
la somme sur `range N`. -/
lemma sum_range_le_of_vanishing {f : ℕ → ℝ} (N : ℕ) (hnn : ∀ j, 0 ≤ f j)
    (hvan : ∀ j, N ≤ j → f j = 0) (k : ℕ) :
    ∑ j ∈ Finset.range k, f j ≤ ∑ j ∈ Finset.range N, f j := by
  rcases le_total k N with h | h
  · exact Finset.sum_le_sum_of_subset_of_nonneg ((fun a ha => Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 ha) h)))
      (fun i _ _ => hnn i)
  · refine le_of_eq ?_
    exact (Finset.sum_subset ((fun a ha => Finset.mem_range.2 (lt_of_lt_of_le (Finset.mem_range.1 ha) h)))
      (fun x _ hnx => hvan x (by simpa using hnx))).symm

/-- **Bornitude des iterees.** Sous controlabilite, la suite croissante
`k ↦ xᵀ Fᵏ(0) x` est majoree : le cout de la commande qui annule l'etat en `n` pas
ne depend pas de l'horizon. -/
lemma iterate_quad_bddAbove
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (hQ : Q.PosSemidef) (hR : R.PosDef) (hctrb : BertsekasControllablePair A B)
    (x : Fin n → ℝ) :
    ∃ c : ℝ, ∀ k, x ⬝ᵥ ((BertsekasRiccatiMap A B Q R)^[k] 0 *ᵥ x) ≤ c := by
  obtain ⟨u, hu0, hun⟩ := exists_deadbeat A B hctrb x
  set traj := stateFrom A B x u with htraj
  set f : ℕ → ℝ := fun j => traj j ⬝ᵥ (Q *ᵥ traj j) + u j ⬝ᵥ (R *ᵥ u j) with hf
  have hnn : ∀ j, 0 ≤ f j := fun j =>
    add_nonneg (quad_nonneg hQ _) (quad_nonneg hR.posSemidef _)
  have hvan : ∀ j, n ≤ j → f j = 0 := by
    intro j hj
    simp only [hf, hun j hj, hu0 j hj]
    simp
  refine ⟨∑ j ∈ Finset.range n, f j, fun k => ?_⟩
  have hstart : traj 0 = x := stateFrom_zero A B x u
  have hdyn : ∀ j, traj (j + 1) = A *ᵥ traj j + B *ᵥ u j := fun j => stateFrom_succ A B x u j
  have := iterate_quad_le A B Q R hQ hR k traj u hdyn
  rw [hstart] at this
  exact this.trans (sum_range_le_of_vanishing n hnn hvan k)

/-- Pour chaque `x`, la suite `k ↦ xᵀ Fᵏ(0) x` est croissante. -/
lemma quad_monotone
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (hQ : Q.PosSemidef) (hR : R.PosDef) (x : Fin n → ℝ) :
    Monotone (fun k => x ⬝ᵥ ((BertsekasRiccatiMap A B Q R)^[k] 0 *ᵥ x)) := by
  refine monotone_nat_of_le_succ (fun k => ?_)
  exact quad_le_of_sub_posSemidef (iterate_mono_succ A B Q R hQ hR k) x

/-- **Convergence des formes quadratiques** : croissante et majoree. -/
lemma quad_tendsto
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (hQ : Q.PosSemidef) (hR : R.PosDef) (hctrb : BertsekasControllablePair A B)
    (x : Fin n → ℝ) :
    ∃ L : ℝ, Filter.Tendsto (fun k => x ⬝ᵥ ((BertsekasRiccatiMap A B Q R)^[k] 0 *ᵥ x))
      Filter.atTop (nhds L) := by
  obtain ⟨c, hc⟩ := iterate_quad_bddAbove A B Q R hQ hR hctrb x
  refine ⟨⨆ k, x ⬝ᵥ ((BertsekasRiccatiMap A B Q R)^[k] 0 *ᵥ x), ?_⟩
  exact tendsto_atTop_ciSup (quad_monotone A B Q R hQ hR x) ⟨c, by rintro _ ⟨k, rfl⟩; exact hc k⟩

/-- L'entree `(i,j)` est la forme bilineaire sur les vecteurs de base. -/
lemma entry_eq_quad (P : Matrix (Fin n) (Fin n) ℝ) (i j : Fin n) :
    P i j = Pi.single i (1 : ℝ) ⬝ᵥ (P *ᵥ Pi.single j (1 : ℝ)) := by
  simp [Matrix.mulVec, single_dotProduct, dotProduct_single]

/-- **Identite de polarisation** pour une matrice symetrique. -/
lemma polarization (P : Matrix (Fin n) (Fin n) ℝ) (hP : Pᵀ = P) (i j : Fin n) :
    P i j = ((Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ))
              ⬝ᵥ (P *ᵥ (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ)))
            - Pi.single i (1 : ℝ) ⬝ᵥ (P *ᵥ Pi.single i (1 : ℝ))
            - Pi.single j (1 : ℝ) ⬝ᵥ (P *ᵥ Pi.single j (1 : ℝ))) / 2 := by
  have hji : P j i = P i j := by
    conv_lhs => rw [← hP]
    simp [Matrix.transpose_apply]
  simp only [Matrix.mulVec_add, dotProduct_add, add_dotProduct, ← entry_eq_quad, hji]
  ring

/-- **Convergence de l'iteration de Riccati depuis `0`.** Chaque forme quadratique
converge ; la polarisation transporte la convergence aux entrees, donc a la matrice. -/
lemma iterate_tendsto
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (hQ : Q.PosSemidef) (hR : R.PosDef) (hctrb : BertsekasControllablePair A B) :
    ∃ P : Matrix (Fin n) (Fin n) ℝ,
      Filter.Tendsto (fun k => (BertsekasRiccatiMap A B Q R)^[k] 0) Filter.atTop (nhds P) := by
  choose L hL using fun x => quad_tendsto A B Q R hQ hR hctrb x
  refine ⟨Matrix.of fun i j =>
    (L (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ))
      - L (Pi.single i (1 : ℝ)) - L (Pi.single j (1 : ℝ))) / 2, ?_⟩
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have hconv := (((hL (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ))).sub
    (hL (Pi.single i (1 : ℝ)))).sub (hL (Pi.single j (1 : ℝ)))).div_const 2
  refine hconv.congr (fun k => ?_)
  exact (polarization _ (iterate_posSemidef A B Q R hQ hR k).isHermitian i j).symm

/-- **Continuite de l'operateur de Riccati** la ou `BᵀPB + R` est inversible.
L'inverse total de Mathlib est continu en une matrice inversible, via
`det` et `adjugate` qui sont polynomiaux. -/
lemma riccati_continuousAt
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (P₀ : Matrix (Fin n) (Fin n) ℝ) (h : IsUnit (Bᵀ * P₀ * B + R).det) :
    ContinuousAt (BertsekasRiccatiMap A B Q R) P₀ := by
  unfold BertsekasRiccatiMap
  have hDc : Continuous fun P : Matrix (Fin n) (Fin n) ℝ => Bᵀ * P * B + R :=
    (continuous_const.matrix_mul continuous_id).matrix_mul continuous_const |>.add continuous_const
  have hinv : ContinuousAt (fun P : Matrix (Fin n) (Fin n) ℝ => (Bᵀ * P * B + R)⁻¹) P₀ := by
    refine ContinuousAt.comp ?_ hDc.continuousAt
    refine continuousAt_matrix_inv _ ?_
    rw [Ring.inverse_eq_inv']
    exact continuousAt_inv₀ (isUnit_iff_ne_zero.mp h)
  fun_prop (disch := assumption)

/-- Le cone semi-defini positif est stable par passage a la limite. -/
lemma posSemidef_of_tendsto
    {f : ℕ → Matrix (Fin n) (Fin n) ℝ} {P : Matrix (Fin n) (Fin n) ℝ}
    (hf : ∀ k, (f k).PosSemidef)
    (hlim : Filter.Tendsto f Filter.atTop (nhds P)) :
    P.PosSemidef := by
  have hentry : ∀ i j, Filter.Tendsto (fun k => f k i j) Filter.atTop (nhds (P i j)) :=
    fun i j => tendsto_pi_nhds.1 (tendsto_pi_nhds.1 hlim i) j
  have hsymm : ∀ i j, P j i = P i j := by
    intro i j
    refine tendsto_nhds_unique (hentry j i) ?_
    have heq : ∀ k, f k j i = f k i j := fun k => by
      have := congrFun₂ (hf k).isHermitian i j
      simpa using this
    simp only [heq]
    exact hentry i j
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ ?_
  · ext i j
    show star (P j i) = P i j
    simpa using hsymm i j
  · intro x
    have hq : Filter.Tendsto (fun k => star x ⬝ᵥ (f k *ᵥ x)) Filter.atTop
        (nhds (star x ⬝ᵥ (P *ᵥ x))) := by
      have hc : Continuous fun M : Matrix (Fin n) (Fin n) ℝ => star x ⬝ᵥ (M *ᵥ x) := by
        fun_prop
      exact hc.continuousAt.tendsto.comp hlim
    exact ge_of_tendsto hq (Filter.Eventually.of_forall fun k => (hf k).dotProduct_mulVec_nonneg x)

/-- **La limite de `Fᵏ(0)` est un point fixe semi-defini positif.** -/
lemma exists_psd_fixed_point_limit
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (hQ : Q.PosSemidef) (hR : R.PosDef) (hctrb : BertsekasControllablePair A B) :
    ∃ P : Matrix (Fin n) (Fin n) ℝ, P.PosSemidef ∧
      BertsekasRiccatiMap A B Q R P = P ∧
      Filter.Tendsto (fun k => (BertsekasRiccatiMap A B Q R)^[k] 0) Filter.atTop (nhds P) := by
  obtain ⟨P, hlim⟩ := iterate_tendsto A B Q R hQ hR hctrb
  have hPsd : P.PosSemidef :=
    posSemidef_of_tendsto (fun k => iterate_posSemidef A B Q R hQ hR k) hlim
  refine ⟨P, hPsd, ?_, hlim⟩
  have hD : IsUnit (Bᵀ * P * B + R).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (riccatiD_posDef B R P hPsd hR).isUnit
  -- `F` est continue en `P`, donc `F(Fᵏ(0)) → F(P)`
  have h1 : Filter.Tendsto (fun k => BertsekasRiccatiMap A B Q R ((BertsekasRiccatiMap A B Q R)^[k] 0))
      Filter.atTop (nhds (BertsekasRiccatiMap A B Q R P)) :=
    (riccati_continuousAt A B Q R P hD).tendsto.comp hlim
  -- mais cette suite est `F^{k+1}(0)`, qui tend aussi vers `P`
  have h2 : Filter.Tendsto (fun k => (BertsekasRiccatiMap A B Q R)^[k + 1] 0)
      Filter.atTop (nhds P) := hlim.comp (Filter.tendsto_add_atTop_nat 1)
  have heq : (fun k => BertsekasRiccatiMap A B Q R ((BertsekasRiccatiMap A B Q R)^[k] 0))
      = fun k => (BertsekasRiccatiMap A B Q R)^[k + 1] 0 := by
    funext k
    exact (Function.iterate_succ_apply' (BertsekasRiccatiMap A B Q R) k 0).symm
  rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

/-- Forme quadratique nulle sous une matrice definie positive : le vecteur est nul. -/
lemma eq_zero_of_quad_eq_zero {k : ℕ} {M : Matrix (Fin k) (Fin k) ℝ} (hM : M.PosDef)
    {x : Fin k → ℝ} (hx : x ⬝ᵥ (M *ᵥ x) = 0) : x = 0 := by
  by_contra hne
  have := hM.dotProduct_mulVec_pos hne
  simp only [star_trivial] at this
  exact absurd hx (ne_of_gt this)

/-- **Un pas de la recurrence d'observabilite.** Si la forme quadratique de `F(P)`
s'annule en `x`, alors `Cx = 0` et celle de `P` s'annule en `Ax`. Les trois termes
`(A+BL)ᵀP(A+BL)`, `Q` et `LᵀRL` sont positifs et de somme nulle, donc tous nuls ;
`R ≻ 0` force `Lx = 0`, donc `(A+BL)x = Ax`. -/
lemma quad_zero_step
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    {q : ℕ} (C : Matrix (Fin q) (Fin n) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ)
    (hQ : Q = Cᵀ * C) (hP : P.PosSemidef) (hR : R.PosDef)
    (x : Fin n → ℝ) (hx : x ⬝ᵥ (BertsekasRiccatiMap A B Q R P *ᵥ x) = 0) :
    C *ᵥ x = 0 ∧ (A *ᵥ x) ⬝ᵥ (P *ᵥ (A *ᵥ x)) = 0 := by
  have hD : IsUnit (Bᵀ * P * B + R).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (riccatiD_posDef B R P hP hR).isUnit
  set L := optGain A B R P with hLdef
  rw [← stepCost_optGain A B Q R P hP.isHermitian hR.isHermitian hD] at hx
  -- decomposition de la forme quadratique en trois termes positifs
  have hsplit : x ⬝ᵥ (stepCost A B Q R P L *ᵥ x)
      = ((A + B * L) *ᵥ x) ⬝ᵥ (P *ᵥ ((A + B * L) *ᵥ x))
        + x ⬝ᵥ (Q *ᵥ x) + (L *ᵥ x) ⬝ᵥ (R *ᵥ (L *ᵥ x)) := by
    simp only [stepCost, Matrix.add_mulVec, dotProduct_add, quad_congr]
  rw [hsplit] at hx
  have h1 : 0 ≤ ((A + B * L) *ᵥ x) ⬝ᵥ (P *ᵥ ((A + B * L) *ᵥ x)) := quad_nonneg hP _
  have h2 : 0 ≤ x ⬝ᵥ (Q *ᵥ x) := by
    rw [hQ]; exact quad_nonneg (hQ ▸ (Matrix.posSemidef_conjTranspose_mul_self C)) x
  have h3 : 0 ≤ (L *ᵥ x) ⬝ᵥ (R *ᵥ (L *ᵥ x)) := quad_nonneg hR.posSemidef _
  have e1 : ((A + B * L) *ᵥ x) ⬝ᵥ (P *ᵥ ((A + B * L) *ᵥ x)) = 0 := by linarith
  have e2 : x ⬝ᵥ (Q *ᵥ x) = 0 := by linarith
  have e3 : (L *ᵥ x) ⬝ᵥ (R *ᵥ (L *ᵥ x)) = 0 := by linarith
  -- `R ≻ 0` force `Lx = 0`
  have hLx : L *ᵥ x = 0 := eq_zero_of_quad_eq_zero hR e3
  have hABLx : (A + B * L) *ᵥ x = A *ᵥ x := by
    rw [Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hLx]
    simp
  refine ⟨?_, by rwa [hABLx] at e1⟩
  -- `xᵀCᵀCx = ‖Cx‖² = 0`
  have hCC : x ⬝ᵥ ((Cᵀ * C) *ᵥ x) = (C *ᵥ x) ⬝ᵥ (C *ᵥ x) := by
    have h := quad_congr (n := q) (k := n) 1 C x
    simpa using h
  have hz : (C *ᵥ x) ⬝ᵥ (C *ᵥ x) = 0 := by rw [← hCC, ← hQ]; exact e2
  exact dotProduct_self_eq_zero.mp hz

/-- **L'observabilite tue le noyau a gauche.** Si `C Aʲ x = 0` pour tout `j`, alors
`x = 0` : la matrice d'observabilite etant surjective, `x` est orthogonal a tout. -/
lemma obs_left_kernel {q : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (C : Matrix (Fin q) (Fin n) ℝ)
    (hobs : BertsekasObservablePair A C) (x : Fin n → ℝ)
    (hx : ∀ j : ℕ, C *ᵥ ((A ^ j) *ᵥ x) = 0) : x = 0 := by
  set Obs : Matrix (Fin n) (Fin n × Fin q) ℝ :=
    Matrix.of fun (i : Fin n) (p : Fin n × Fin q) => ((Aᵀ) ^ (p.1 : ℕ) * Cᵀ) i p.2 with hObs
  have hsurj : Function.Surjective (fun w => Obs *ᵥ w) := by
    have hr : LinearMap.range Obs.mulVecLin = ⊤ := by
      apply Submodule.eq_top_of_finrank_eq
      rw [← Matrix.rank]
      · rw [show Obs.rank = n from hobs]
        simp
    intro y
    obtain ⟨w, hw⟩ := LinearMap.range_eq_top.mp hr y
    exact ⟨w, hw⟩
  obtain ⟨w, hw⟩ := hsurj x
  simp only at hw
  have hvecMul : Matrix.vecMul x Obs = 0 := by
    funext p
    obtain ⟨a, b⟩ := p
    have h1 : ((Aᵀ) ^ (a : ℕ) * Cᵀ) = (C * A ^ (a : ℕ))ᵀ := by
      rw [Matrix.transpose_mul, Matrix.transpose_pow]
    have h2 := congrFun (hx (a : ℕ)) b
    rw [Matrix.mulVec_mulVec] at h2
    simp only [hObs, Matrix.vecMul, Matrix.of_apply, dotProduct, h1, Matrix.transpose_apply,
      Pi.zero_apply]
    simpa [Matrix.mulVec, dotProduct, mul_comm] using h2
  have hzero : x ⬝ᵥ x = 0 := by
    have hd : x ⬝ᵥ (Obs *ᵥ w) = 0 := by
      rw [Matrix.dotProduct_mulVec, hvecMul, zero_dotProduct]
    rwa [hw] at hd
  exact dotProduct_self_eq_zero.mp hzero

/-- Chaque terme d'une suite croissante est majore par sa limite : la forme
quadratique de `Fᵏ(0)` est dominee par celle de la limite. -/
lemma quad_iterate_le_limit
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (hQ : Q.PosSemidef) (hR : R.PosDef) {P : Matrix (Fin n) (Fin n) ℝ}
    (hlim : Filter.Tendsto (fun k => (BertsekasRiccatiMap A B Q R)^[k] 0) Filter.atTop (nhds P))
    (y : Fin n → ℝ) (k : ℕ) :
    y ⬝ᵥ ((BertsekasRiccatiMap A B Q R)^[k] 0 *ᵥ y) ≤ y ⬝ᵥ (P *ᵥ y) := by
  have hc : Continuous fun M : Matrix (Fin n) (Fin n) ℝ => y ⬝ᵥ (M *ᵥ y) := by fun_prop
  exact (quad_monotone A B Q R hQ hR y).ge_of_tendsto (hc.continuousAt.tendsto.comp hlim) k

/-- **La limite est definie positive.** Si sa forme quadratique s'annule en `x`,
celle de chaque iteree s'annule aussi ; la recurrence force `C Aʲ x = 0` pour tout
`j`, ce que l'observabilite interdit sauf si `x = 0`. -/
lemma limit_posDef
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    {q : ℕ} (C : Matrix (Fin q) (Fin n) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (hQdef : Q = Cᵀ * C) (hQ : Q.PosSemidef) (hR : R.PosDef)
    (hobs : BertsekasObservablePair A C) {P : Matrix (Fin n) (Fin n) ℝ}
    (hPsd : P.PosSemidef)
    (hlim : Filter.Tendsto (fun k => (BertsekasRiccatiMap A B Q R)^[k] 0) Filter.atTop (nhds P)) :
    P.PosDef := by
  refine Matrix.PosDef.of_dotProduct_mulVec_pos hPsd.isHermitian (fun x hx => ?_)
  simp only [star_trivial]
  rcases lt_or_eq_of_le (quad_nonneg hPsd x) with hlt | heq
  · exact hlt
  · exfalso
    apply hx
    -- toutes les iterees s'annulent en `x`
    have hall : ∀ (y : Fin n → ℝ), y ⬝ᵥ (P *ᵥ y) = 0 →
        ∀ k, y ⬝ᵥ ((BertsekasRiccatiMap A B Q R)^[k] 0 *ᵥ y) = 0 := by
      intro y hy k
      exact le_antisymm (by rw [← hy]; exact quad_iterate_le_limit A B Q R hQ hR hlim y k)
        (quad_nonneg (iterate_posSemidef A B Q R hQ hR k) y)
    -- propagation le long des puissances de `A`
    have hprop : ∀ j : ℕ, ∀ k, ((A ^ j) *ᵥ x) ⬝ᵥ
        ((BertsekasRiccatiMap A B Q R)^[k] 0 *ᵥ ((A ^ j) *ᵥ x)) = 0 := by
      intro j
      induction j with
      | zero => simpa using hall x heq.symm
      | succ j ih =>
          intro k
          have hk1 := ih (k + 1)
          rw [Function.iterate_succ_apply' (f := BertsekasRiccatiMap A B Q R) (n := k)] at hk1
          have := (quad_zero_step A B C Q R _ hQdef
            (iterate_posSemidef A B Q R hQ hR k) hR ((A ^ j) *ᵥ x) hk1).2
          rwa [Matrix.mulVec_mulVec, ← pow_succ'] at this
    -- d'ou `C Aʲ x = 0` pour tout `j`
    refine obs_left_kernel A C hobs x (fun j => ?_)
    have hj := hprop j 1
    rw [Function.iterate_succ_apply' (f := BertsekasRiccatiMap A B Q R) (n := 0)] at hj
    simpa using (quad_zero_step A B C Q R _ hQdef
      (iterate_posSemidef A B Q R hQ hR 0) hR ((A ^ j) *ᵥ x) hj).1

/-- **Minimalite.** Tout point fixe semi-defini positif domine chaque iteree
`Fᵏ(0)` : la monotonie propage `0 ⪯ P'` le long de l'iteration. -/
lemma iterate_le_fixed_point
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (hQ : Q.PosSemidef) (hR : R.PosDef) {P' : Matrix (Fin n) (Fin n) ℝ}
    (hP' : P'.PosSemidef) (hfix : BertsekasRiccatiMap A B Q R P' = P') (k : ℕ) :
    (P' - (BertsekasRiccatiMap A B Q R)^[k] 0).PosSemidef := by
  induction k with
  | zero => simpa using hP'
  | succ k ih =>
      rw [Function.iterate_succ_apply' (f := BertsekasRiccatiMap A B Q R) (n := k)]
      have := riccati_mono A B Q R _ _ (iterate_posSemidef A B Q R hQ hR k) hP' hR ih
      rwa [hfix] at this

/-- La limite est le plus petit point fixe semi-defini positif. -/
lemma limit_le_fixed_point
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (hQ : Q.PosSemidef) (hR : R.PosDef) {P P' : Matrix (Fin n) (Fin n) ℝ}
    (hP' : P'.PosSemidef) (hfix : BertsekasRiccatiMap A B Q R P' = P')
    (hlim : Filter.Tendsto (fun k => (BertsekasRiccatiMap A B Q R)^[k] 0) Filter.atTop (nhds P)) :
    (P' - P).PosSemidef := by
  refine posSemidef_of_tendsto (f := fun k => P' - (BertsekasRiccatiMap A B Q R)^[k] 0)
    (fun k => iterate_le_fixed_point A B Q R hQ hR hP' hfix k) ?_
  exact tendsto_const_nhds.sub hlim

/-- **Minoration uniforme d'une forme definie positive.** Le minimum de `xᵀMx` sur
la sphere `x ⬝ᵥ x = 1`, compacte, est strictement positif ; l'homogeneite conclut. -/
lemma posDef_quad_lower_bound {k : ℕ} {M : Matrix (Fin k) (Fin k) ℝ} (hM : M.PosDef) :
    ∃ c > 0, ∀ x : Fin k → ℝ, c * (x ⬝ᵥ x) ≤ x ⬝ᵥ (M *ᵥ x) := by
  rcases Nat.eq_zero_or_pos k with rfl | hk
  · refine ⟨1, one_pos, fun x => ?_⟩
    have : x = 0 := by funext i; exact absurd i.isLt (by omega)
    simp [this]
  have hcont : Continuous fun x : Fin k → ℝ => x ⬝ᵥ (M *ᵥ x) := by fun_prop
  have hcontN : Continuous fun x : Fin k → ℝ => x ⬝ᵥ x := by fun_prop
  set S : Set (Fin k → ℝ) := {x | x ⬝ᵥ x = 1} with hS
  have hbdd : Bornology.IsBounded S := by
    refine (Metric.isBounded_closedBall (x := (0 : Fin k → ℝ)) (r := 1)).subset (fun x hx => ?_)
    simp only [Metric.mem_closedBall, dist_zero_right]
    rw [pi_norm_le_iff_of_nonneg zero_le_one]
    intro i
    have hle : x i * x i ≤ x ⬝ᵥ x :=
      Finset.single_le_sum (f := fun j => x j * x j)
        (fun j _ => mul_self_nonneg _) (Finset.mem_univ i)
    rw [show x ⬝ᵥ x = 1 from hx] at hle
    simp only [Real.norm_eq_abs]
    nlinarith [abs_nonneg (x i), sq_abs (x i)]
  have hcompact : IsCompact S :=
    Metric.isCompact_of_isClosed_isBounded (isClosed_eq hcontN continuous_const) hbdd
  have hne : S.Nonempty := by
    refine ⟨Pi.single ⟨0, hk⟩ 1, ?_⟩
    simp [hS, dotProduct_single, single_dotProduct]
  obtain ⟨x₀, hx₀S, hmin⟩ := hcompact.exists_isMinOn hne hcont.continuousOn
  have hx₀ne : x₀ ≠ 0 := by
    intro h
    rw [h] at hx₀S
    simp [hS] at hx₀S
  have hc : 0 < x₀ ⬝ᵥ (M *ᵥ x₀) := by
    have := hM.dotProduct_mulVec_pos hx₀ne
    simpa using this
  refine ⟨x₀ ⬝ᵥ (M *ᵥ x₀), hc, fun x => ?_⟩
  rcases eq_or_ne x 0 with rfl | hx
  · simp
  have hxxnn : 0 ≤ x ⬝ᵥ x := by
    rw [dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have hxx : 0 < x ⬝ᵥ x :=
    lt_of_le_of_ne hxxnn (fun h => hx (dotProduct_self_eq_zero.mp h.symm))
  set t := Real.sqrt (x ⬝ᵥ x) with ht
  have htpos : 0 < t := Real.sqrt_pos.mpr hxx
  have ht2 : t * t = x ⬝ᵥ x := Real.mul_self_sqrt hxx.le
  have humem : (t⁻¹ • x) ∈ S := by
    simp only [hS, Set.mem_setOf_eq, smul_dotProduct, dotProduct_smul, smul_eq_mul]
    field_simp
    rw [← ht2]
    ring
  have hstep : x₀ ⬝ᵥ (M *ᵥ x₀) ≤ (t⁻¹ • x) ⬝ᵥ (M *ᵥ (t⁻¹ • x)) := hmin humem
  simp only [smul_dotProduct, Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul] at hstep
  have hq : t⁻¹ * (t⁻¹ * (x ⬝ᵥ (M *ᵥ x))) = (x ⬝ᵥ (M *ᵥ x)) / (x ⬝ᵥ x) := by
    rw [← ht2]
    field_simp
  rw [hq, le_div_iff₀ hxx] at hstep
  exact hstep

/-- Une suite dont la norme euclidienne au carre tend vers `0` tend vers `0`. -/
lemma tendsto_zero_of_quad_tendsto_zero {k : ℕ} {z : ℕ → Fin k → ℝ}
    (h : Filter.Tendsto (fun j => z j ⬝ᵥ z j) Filter.atTop (nhds 0)) :
    Filter.Tendsto z Filter.atTop (nhds 0) := by
  refine tendsto_pi_nhds.2 (fun i => ?_)
  have hsq : Filter.Tendsto (fun j => (z j i) ^ 2) Filter.atTop (nhds 0) := by
    refine squeeze_zero (fun j => sq_nonneg _) (fun j => ?_) h
    rw [sq, dotProduct]
    exact Finset.single_le_sum (f := fun l => z j l * z j l)
      (fun l _ => mul_self_nonneg _) (Finset.mem_univ i)
  have habs : Filter.Tendsto (fun j => |z j i|) Filter.atTop (nhds 0) := by
    have := hsq.sqrt
    simpa [Real.sqrt_sq_eq_abs] using this
  exact squeeze_zero_norm (fun j => le_of_eq (Real.norm_eq_abs _)) habs

/-- Le cas d'egalite dans la decroissance de Lyapunov : le decrement
`zᵀ(Q + LᵀRL)z` est nul si et seulement si `Cz = 0` et `Lz = 0`. -/
lemma decrement_zero_iff
    {q : ℕ} (C : Matrix (Fin q) (Fin n) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (hQdef : Q = Cᵀ * C) (hR : R.PosDef) (L : Matrix (Fin m) (Fin n) ℝ)
    (z : Fin n → ℝ) (h : z ⬝ᵥ ((Q + Lᵀ * R * L) *ᵥ z) = 0) :
    C *ᵥ z = 0 ∧ L *ᵥ z = 0 := by
  have hCC : z ⬝ᵥ (Q *ᵥ z) = (C *ᵥ z) ⬝ᵥ (C *ᵥ z) := by
    rw [hQdef]
    have hq := quad_congr (n := q) (k := n) 1 C z
    simpa using hq
  have hLL : z ⬝ᵥ ((Lᵀ * R * L) *ᵥ z) = (L *ᵥ z) ⬝ᵥ (R *ᵥ (L *ᵥ z)) := quad_congr R L z
  have hsplit : z ⬝ᵥ ((Q + Lᵀ * R * L) *ᵥ z)
      = (C *ᵥ z) ⬝ᵥ (C *ᵥ z) + (L *ᵥ z) ⬝ᵥ (R *ᵥ (L *ᵥ z)) := by
    rw [Matrix.add_mulVec, dotProduct_add, hCC, hLL]
  rw [hsplit] at h
  have h1 : 0 ≤ (C *ᵥ z) ⬝ᵥ (C *ᵥ z) := by
    rw [dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  have h2 : 0 ≤ (L *ᵥ z) ⬝ᵥ (R *ᵥ (L *ᵥ z)) := quad_nonneg hR.posSemidef _
  refine ⟨dotProduct_self_eq_zero.mp (by linarith), ?_⟩
  exact eq_zero_of_quad_eq_zero hR (by linarith)

/-- **Identite de Lyapunov.** Au point fixe, `P = TᵀPT + Q + LᵀRL` avec `T = A + BL`,
donc la forme quadratique de `P` decroit le long de la boucle fermee, d'un decrement
exactement egal a `zᵀ(Q + LᵀRL)z`. -/
lemma lyapunov_step
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (P : Matrix (Fin n) (Fin n) ℝ) (L : Matrix (Fin m) (Fin n) ℝ)
    (hfix : stepCost A B Q R P L = P) (z : Fin n → ℝ) :
    z ⬝ᵥ (P *ᵥ z) - ((A + B * L) *ᵥ z) ⬝ᵥ (P *ᵥ ((A + B * L) *ᵥ z))
      = z ⬝ᵥ ((Q + Lᵀ * R * L) *ᵥ z) := by
  have hstep : stepCost A B Q R P L
      = (A + B * L)ᵀ * P * (A + B * L) + Q + Lᵀ * R * L := rfl
  have h1 : z ⬝ᵥ (P *ᵥ z)
      = ((A + B * L) *ᵥ z) ⬝ᵥ (P *ᵥ ((A + B * L) *ᵥ z))
        + z ⬝ᵥ (Q *ᵥ z) + z ⬝ᵥ ((Lᵀ * R * L) *ᵥ z) := by
    conv_lhs => rw [← hfix, hstep]
    rw [Matrix.add_mulVec, Matrix.add_mulVec, dotProduct_add, dotProduct_add, quad_congr]
  rw [h1]
  conv_rhs => rw [Matrix.add_mulVec, dotProduct_add]
  ring

/-- **La boucle fermee est contractante.** Argument de Lyapunov : `zᵀPz` decroit le
long de `T = A + BL`, donc converge ; toute valeur d'adherence `y*` de la trajectoire
realise l'egalite a chaque pas, ce qui force `C Tʲy* = 0` et `L Tʲy* = 0`, donc
`Tʲy* = Aʲy*` ; l'observabilite donne `y* = 0`, donc la limite est nulle. -/
lemma closedLoop_pow_tendsto_zero
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    {q : ℕ} (C : Matrix (Fin q) (Fin n) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (hQdef : Q = Cᵀ * C) (hR : R.PosDef) (hobs : BertsekasObservablePair A C)
    {P : Matrix (Fin n) (Fin n) ℝ} (hPd : P.PosDef)
    (hfix : BertsekasRiccatiMap A B Q R P = P) (x : Fin n → ℝ) :
    Filter.Tendsto (fun k => ((A + B * optGain A B R P) ^ k) *ᵥ x) Filter.atTop (nhds 0) := by
  set L := optGain A B R P with hL
  set T := A + B * L with hT
  set y : ℕ → Fin n → ℝ := fun k => (T ^ k) *ᵥ x with hy
  set v : ℕ → ℝ := fun k => y k ⬝ᵥ (P *ᵥ y k) with hv
  -- identite de Lyapunov au point fixe
  have hD : IsUnit (Bᵀ * P * B + R).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (riccatiD_posDef B R P hPd.posSemidef hR).isUnit
  have hLyap : stepCost A B Q R P L = P := by
    rw [hL, stepCost_optGain A B Q R P hPd.isHermitian hR.isHermitian hD]; exact hfix
  -- decalage temporel
  have hshift : ∀ k j, y (k + j) = (T ^ j) *ᵥ y k := by
    intro k j
    simp only [hy]
    rw [Matrix.mulVec_mulVec, ← pow_add, Nat.add_comm j k]
  have hsucc : ∀ k, y (k + 1) = T *ᵥ y k := by
    intro k
    have := hshift k 1
    simpa using this
  -- decrement de Lyapunov
  have hdec : ∀ z : Fin n → ℝ,
      z ⬝ᵥ (P *ᵥ z) - (T *ᵥ z) ⬝ᵥ (P *ᵥ (T *ᵥ z)) = z ⬝ᵥ ((Q + Lᵀ * R * L) *ᵥ z) :=
    fun z => lyapunov_step A B Q R P L hLyap z
  have hQpsd : Q.PosSemidef := by rw [hQdef]; exact Matrix.posSemidef_conjTranspose_mul_self C
  have hdecnn : ∀ z : Fin n → ℝ, 0 ≤ z ⬝ᵥ ((Q + Lᵀ * R * L) *ᵥ z) := by
    intro z
    have h2 : (Lᵀ * R * L).PosSemidef := by
      have := hR.posSemidef.conjTranspose_mul_mul_same L
      simpa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using this
    exact quad_nonneg (hQpsd.add h2) z
  -- `v` est decroissante, positive, donc convergente
  have hvanti : Antitone v := by
    refine antitone_nat_of_succ_le (fun k => ?_)
    have := hdecnn (y k)
    rw [← hdec (y k)] at this
    simp only [hv]
    rw [hsucc k]
    linarith
  have hvnn : ∀ k, 0 ≤ v k := fun k => quad_nonneg hPd.posSemidef _
  have hvlim : Filter.Tendsto v Filter.atTop (nhds (⨅ k, v k)) :=
    tendsto_atTop_ciInf hvanti ⟨0, by rintro _ ⟨k, rfl⟩; exact hvnn k⟩
  set vstar := ⨅ k, v k with hvstar
  -- bornitude de la trajectoire
  obtain ⟨c, hcpos, hcb⟩ := posDef_quad_lower_bound hPd
  have hybound : ∀ k, y k ⬝ᵥ y k ≤ v 0 / c := by
    intro k
    rw [le_div_iff₀ hcpos]
    calc y k ⬝ᵥ y k * c = c * (y k ⬝ᵥ y k) := by ring
      _ ≤ v k := hcb (y k)
      _ ≤ v 0 := hvanti (Nat.zero_le k)
  set M := Real.sqrt (v 0 / c) with hM
  have hyball : ∀ k, y k ∈ Metric.closedBall (0 : Fin n → ℝ) M := by
    intro k
    simp only [Metric.mem_closedBall, dist_zero_right]
    rw [pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)]
    intro i
    have hle : y k i * y k i ≤ y k ⬝ᵥ y k :=
      Finset.single_le_sum (f := fun l => y k l * y k l)
        (fun l _ => mul_self_nonneg _) (Finset.mem_univ i)
    have h2 : y k i * y k i ≤ v 0 / c := le_trans hle (hybound k)
    rw [Real.norm_eq_abs, ← Real.sqrt_sq_eq_abs]
    exact Real.sqrt_le_sqrt (by nlinarith [sq_abs (y k i), abs_nonneg (y k i)])
  -- valeur d'adherence de la trajectoire
  obtain ⟨ystar, -, φ, hφ, hφlim⟩ :=
    (isCompact_closedBall (0 : Fin n → ℝ) M).tendsto_subseq hyball
  have hqcont : Continuous fun z : Fin n → ℝ => z ⬝ᵥ (P *ᵥ z) := by fun_prop
  -- chaque iteree de `ystar` realise la valeur limite
  have hvj : ∀ j, ((T ^ j) *ᵥ ystar) ⬝ᵥ (P *ᵥ ((T ^ j) *ᵥ ystar)) = vstar := by
    intro j
    have hmono : StrictMono (fun i => φ i + j) := fun a b hab => by
      simpa using Nat.add_lt_add_right (hφ hab) j
    have hsub : Filter.Tendsto (fun i => v (φ i + j)) Filter.atTop (nhds vstar) :=
      hvlim.comp hmono.tendsto_atTop
    have hycont : Filter.Tendsto (fun i => y (φ i + j)) Filter.atTop
        (nhds ((T ^ j) *ᵥ ystar)) := by
      have hc : Continuous fun z : Fin n → ℝ => (T ^ j) *ᵥ z := by fun_prop
      have heq : (fun i => y (φ i + j)) = fun i => (T ^ j) *ᵥ (y (φ i)) := by
        funext i; exact hshift (φ i) j
      rw [heq]
      exact hc.continuousAt.tendsto.comp hφlim
    have hqlim := hqcont.continuousAt.tendsto.comp hycont
    exact tendsto_nhds_unique hqlim hsub
  -- le decrement de Lyapunov est nul en chaque iteree
  have hzero : ∀ j, C *ᵥ ((T ^ j) *ᵥ ystar) = 0 ∧ L *ᵥ ((T ^ j) *ᵥ ystar) = 0 := by
    intro j
    refine decrement_zero_iff C Q R hQdef hR L _ ?_
    have h1 := hdec ((T ^ j) *ᵥ ystar)
    have h2 : T *ᵥ ((T ^ j) *ᵥ ystar) = (T ^ (j + 1)) *ᵥ ystar := by
      rw [Matrix.mulVec_mulVec, ← pow_succ']
    rw [h2, hvj j, hvj (j + 1)] at h1
    linarith
  -- les iterees de la boucle fermee coincident avec celles de `A`
  have hTA : ∀ j, (T ^ j) *ᵥ ystar = (A ^ j) *ᵥ ystar := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
        have h2 : (T ^ (j + 1)) *ᵥ ystar = T *ᵥ ((T ^ j) *ᵥ ystar) := by
          rw [Matrix.mulVec_mulVec, ← pow_succ']
        have hLz : L *ᵥ ((A ^ j) *ᵥ ystar) = 0 := by
          have := (hzero j).2; rwa [ih] at this
        rw [h2, ih, hT, Matrix.add_mulVec, ← Matrix.mulVec_mulVec, hLz,
          Matrix.mulVec_mulVec, ← pow_succ']
        simp
  -- l'observabilite annule la valeur d'adherence
  have hystar0 : ystar = 0 := by
    refine obs_left_kernel A C hobs ystar (fun j => ?_)
    have := (hzero j).1
    rwa [hTA j] at this
  have hvstar0 : vstar = 0 := by
    have h0 := hvj 0
    rw [hystar0] at h0
    simpa using h0.symm
  -- la forme quadratique tend vers zero, donc la trajectoire aussi
  refine tendsto_zero_of_quad_tendsto_zero ?_
  refine squeeze_zero (g := fun k => v k / c) (fun k => ?_) (fun k => ?_) ?_
  · rw [dotProduct]; exact Finset.sum_nonneg (fun i _ => mul_self_nonneg _)
  · exact (le_div_iff₀ hcpos).mpr (by linarith [hcb (y k)])
  · have : Filter.Tendsto (fun k => v k / c) Filter.atTop (nhds (vstar / c)) :=
      hvlim.div_const c
    rw [hvstar0, zero_div] at this
    exact this

/-- L'ecart entre deux couts sous le meme gain est une congruence. -/
lemma stepCost_sub
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (X Y : Matrix (Fin n) (Fin n) ℝ) (L : Matrix (Fin m) (Fin n) ℝ) :
    stepCost A B Q R X L - stepCost A B Q R Y L
      = (A + B * L)ᵀ * (X - Y) * (A + B * L) := by
  simp only [stepCost, Matrix.mul_sub, Matrix.sub_mul]
  abel

/-- L'iteration sous gain constant est explicite : `Hᵏ(P₀) - P = (Tᵀ)ᵏ (P₀ - P) Tᵏ`. -/
lemma stepCostIterate_sub
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (P P₀ : Matrix (Fin n) (Fin n) ℝ) (L : Matrix (Fin m) (Fin n) ℝ)
    (hLyap : stepCost A B Q R P L = P) (k : ℕ) :
    (fun X => stepCost A B Q R X L)^[k] P₀ - P
      = (((A + B * L) ^ k)ᵀ) * (P₀ - P) * ((A + B * L) ^ k) := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply' (f := fun X => stepCost A B Q R X L) (n := k)]
      have hstep : stepCost A B Q R ((fun X => stepCost A B Q R X L)^[k] P₀) L - P
          = (A + B * L)ᵀ * ((fun X => stepCost A B Q R X L)^[k] P₀ - P) * (A + B * L) := by
        conv_lhs => rw [← hLyap]
        exact stepCost_sub A B Q R _ P L
      rw [hstep, ih]
      simp only [Matrix.transpose_pow]
      rw [pow_succ' ((A + B * L)ᵀ) k, pow_succ (A + B * L) k]
      simp only [Matrix.mul_assoc]

/-- Les iterees de Riccati depuis `P₀` restent semi-definies positives. -/
lemma iterate_posSemidef_of
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (hQ : Q.PosSemidef) (hR : R.PosDef) {P₀ : Matrix (Fin n) (Fin n) ℝ}
    (hP₀ : P₀.PosSemidef) (k : ℕ) :
    ((BertsekasRiccatiMap A B Q R)^[k] P₀).PosSemidef := by
  induction k with
  | zero => simpa using hP₀
  | succ k ih =>
      rw [Function.iterate_succ_apply' (f := BertsekasRiccatiMap A B Q R) (n := k)]
      exact riccati_posSemidef A B Q R _ ih hQ hR

/-- **Encadrement superieur** : l'iteration de Riccati est dominee par l'iteration
sous le gain constant optimal. -/
lemma riccatiIterate_le_stepCostIterate
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (hQ : Q.PosSemidef) (hR : R.PosDef) (L : Matrix (Fin m) (Fin n) ℝ)
    {P₀ : Matrix (Fin n) (Fin n) ℝ} (hP₀ : P₀.PosSemidef) (k : ℕ) :
    ((fun X => stepCost A B Q R X L)^[k] P₀
      - (BertsekasRiccatiMap A B Q R)^[k] P₀).PosSemidef := by
  induction k with
  | zero => simpa using Matrix.PosSemidef.zero (n := Fin n) (R := ℝ)
  | succ k ih =>
      rw [Function.iterate_succ_apply' (f := fun X => stepCost A B Q R X L) (n := k),
        Function.iterate_succ_apply' (f := BertsekasRiccatiMap A B Q R) (n := k)]
      have hFk := iterate_posSemidef_of A B Q R hQ hR hP₀ k
      have e1 : (stepCost A B Q R ((fun X => stepCost A B Q R X L)^[k] P₀) L
          - stepCost A B Q R ((BertsekasRiccatiMap A B Q R)^[k] P₀) L).PosSemidef := by
        rw [stepCost_sub]
        have := ih.conjTranspose_mul_mul_same (A + B * L)
        simpa [Matrix.conjTranspose_eq_transpose_of_trivial, Matrix.mul_assoc] using this
      have e2 := riccati_le_stepCost A B Q R _ L hFk hR
      have e : stepCost A B Q R ((fun X => stepCost A B Q R X L)^[k] P₀) L
          - BertsekasRiccatiMap A B Q R ((BertsekasRiccatiMap A B Q R)^[k] P₀)
          = (stepCost A B Q R ((fun X => stepCost A B Q R X L)^[k] P₀) L
              - stepCost A B Q R ((BertsekasRiccatiMap A B Q R)^[k] P₀) L)
            + (stepCost A B Q R ((BertsekasRiccatiMap A B Q R)^[k] P₀) L
              - BertsekasRiccatiMap A B Q R ((BertsekasRiccatiMap A B Q R)^[k] P₀)) := by
        abel
      rw [e]
      exact e1.add e2

/-- **Encadrement inferieur** : l'iteration depuis `0` minore celle depuis `P₀ ⪰ 0`. -/
lemma riccatiIterate_ge_from_zero
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (hQ : Q.PosSemidef) (hR : R.PosDef) {P₀ : Matrix (Fin n) (Fin n) ℝ}
    (hP₀ : P₀.PosSemidef) (k : ℕ) :
    ((BertsekasRiccatiMap A B Q R)^[k] P₀ - (BertsekasRiccatiMap A B Q R)^[k] 0).PosSemidef := by
  induction k with
  | zero => simpa using hP₀
  | succ k ih =>
      rw [Function.iterate_succ_apply' (f := BertsekasRiccatiMap A B Q R) (n := k),
        Function.iterate_succ_apply' (f := BertsekasRiccatiMap A B Q R) (n := k)]
      exact riccati_mono A B Q R _ _ (iterate_posSemidef A B Q R hQ hR k)
        (iterate_posSemidef_of A B Q R hQ hR hP₀ k) hR ih

/-- La convergence de toutes les formes quadratiques entraine la convergence
matricielle, par polarisation. -/
lemma tendsto_of_quad_tendsto {f : ℕ → Matrix (Fin n) (Fin n) ℝ}
    {P : Matrix (Fin n) (Fin n) ℝ}
    (hsymm : ∀ k, (f k)ᵀ = f k) (hPsymm : Pᵀ = P)
    (h : ∀ x : Fin n → ℝ,
      Filter.Tendsto (fun k => x ⬝ᵥ (f k *ᵥ x)) Filter.atTop (nhds (x ⬝ᵥ (P *ᵥ x)))) :
    Filter.Tendsto f Filter.atTop (nhds P) := by
  refine tendsto_pi_nhds.2 fun i => tendsto_pi_nhds.2 fun j => ?_
  have hconv := (((h (Pi.single i (1 : ℝ) + Pi.single j (1 : ℝ))).sub
    (h (Pi.single i (1 : ℝ)))).sub (h (Pi.single j (1 : ℝ)))).div_const 2
  rw [← polarization P hPsymm i j] at hconv
  refine hconv.congr (fun k => ?_)
  exact (polarization (f k) (hsymm k) i j).symm

/-- **Attraction globale.** Encadrement : l'iteration depuis `P₀` est comprise entre
celle depuis `0`, qui converge vers `P`, et celle sous le gain constant optimal, dont
l'ecart a `P` est `(Tᵀ)ᵏ (P₀ - P) Tᵏ`, qui tend vers `0` par contraction. -/
lemma riccati_global_attraction
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    {q : ℕ} (C : Matrix (Fin q) (Fin n) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (hQdef : Q = Cᵀ * C) (hQ : Q.PosSemidef) (hR : R.PosDef)
    (hobs : BertsekasObservablePair A C)
    {P : Matrix (Fin n) (Fin n) ℝ} (hPd : P.PosDef)
    (hfix : BertsekasRiccatiMap A B Q R P = P)
    (hlim0 : Filter.Tendsto (fun k => (BertsekasRiccatiMap A B Q R)^[k] 0) Filter.atTop (nhds P))
    {P₀ : Matrix (Fin n) (Fin n) ℝ} (hP₀ : P₀.PosSemidef) :
    Filter.Tendsto (fun k => (BertsekasRiccatiMap A B Q R)^[k] P₀) Filter.atTop (nhds P) := by
  set L := optGain A B R P with hL
  have hD : IsUnit (Bᵀ * P * B + R).det :=
    (Matrix.isUnit_iff_isUnit_det _).mp (riccatiD_posDef B R P hPd.posSemidef hR).isUnit
  have hLyap : stepCost A B Q R P L = P := by
    rw [hL, stepCost_optGain A B Q R P hPd.isHermitian hR.isHermitian hD]; exact hfix
  refine tendsto_of_quad_tendsto
    (fun k => (iterate_posSemidef_of A B Q R hQ hR hP₀ k).isHermitian) hPd.isHermitian
    (fun x => ?_)
  -- borne inferieure : l'iteration depuis `0`
  have hlow : ∀ k, x ⬝ᵥ ((BertsekasRiccatiMap A B Q R)^[k] 0 *ᵥ x)
      ≤ x ⬝ᵥ ((BertsekasRiccatiMap A B Q R)^[k] P₀ *ᵥ x) := fun k =>
    quad_le_of_sub_posSemidef (riccatiIterate_ge_from_zero A B Q R hQ hR hP₀ k) x
  -- borne superieure : l'iteration sous gain constant
  have hupp : ∀ k, x ⬝ᵥ ((BertsekasRiccatiMap A B Q R)^[k] P₀ *ᵥ x)
      ≤ x ⬝ᵥ ((fun X => stepCost A B Q R X L)^[k] P₀ *ᵥ x) := fun k =>
    quad_le_of_sub_posSemidef (riccatiIterate_le_stepCostIterate A B Q R hQ hR L hP₀ k) x
  -- la borne inferieure converge
  have hcx : Continuous fun M : Matrix (Fin n) (Fin n) ℝ => x ⬝ᵥ (M *ᵥ x) := by fun_prop
  have hlowlim : Filter.Tendsto
      (fun k => x ⬝ᵥ ((BertsekasRiccatiMap A B Q R)^[k] 0 *ᵥ x)) Filter.atTop
      (nhds (x ⬝ᵥ (P *ᵥ x))) := hcx.continuousAt.tendsto.comp hlim0
  -- la borne superieure aussi, par contraction de la boucle fermee
  have hupplim : Filter.Tendsto
      (fun k => x ⬝ᵥ ((fun X => stepCost A B Q R X L)^[k] P₀ *ᵥ x)) Filter.atTop
      (nhds (x ⬝ᵥ (P *ᵥ x))) := by
    have hdecomp : ∀ k, x ⬝ᵥ ((fun X => stepCost A B Q R X L)^[k] P₀ *ᵥ x)
        = x ⬝ᵥ (P *ᵥ x)
          + (((A + B * L) ^ k) *ᵥ x) ⬝ᵥ ((P₀ - P) *ᵥ (((A + B * L) ^ k) *ᵥ x)) := by
      intro k
      have hsub := stepCostIterate_sub A B Q R P P₀ L hLyap k
      have : (fun X => stepCost A B Q R X L)^[k] P₀
          = P + ((((A + B * L) ^ k)ᵀ) * (P₀ - P) * ((A + B * L) ^ k)) := by
        rw [← hsub]; abel
      rw [this, Matrix.add_mulVec, dotProduct_add, quad_congr]
    simp only [hdecomp]
    have htail : Filter.Tendsto
        (fun k => (((A + B * L) ^ k) *ᵥ x) ⬝ᵥ ((P₀ - P) *ᵥ (((A + B * L) ^ k) *ᵥ x)))
        Filter.atTop (nhds 0) := by
      have hT := closedLoop_pow_tendsto_zero A B C Q R hQdef hR hobs hPd hfix x
      rw [← hL] at hT
      have hc : Continuous fun z : Fin n → ℝ => z ⬝ᵥ ((P₀ - P) *ᵥ z) := by fun_prop
      have hcomp := hc.continuousAt.tendsto.comp hT
      have hz : (0 : Fin n → ℝ) ⬝ᵥ ((P₀ - P) *ᵥ (0 : Fin n → ℝ)) = 0 := by simp
      rw [hz] at hcomp
      exact hcomp
    simpa using tendsto_const_nhds.add htail
  -- gendarmes
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlowlim hupplim hlow hupp

end RiccatiWork

open RiccatiWork

/-- **Proposition 4.4.1 (parties 1-3), Bertsekas, *Dynamic Programming and Optimal
Control*, Vol. I, 3e ed., §4.4.**

Sous controlabilite de `(A,B)` et observabilite de `(A,C)` avec `Q = CᵀC` et `R ≻ 0`,
l'operateur de Riccati admet un point fixe defini positif, unique dans le cone
semi-defini positif, et globalement attractif sur ce cone. -/
theorem _root_.Prove2me.Solution.BertsekasDP_riccati_psd_fixed_point_exists_unique_convergent {n m q : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (C : Matrix (Fin q) (Fin n) ℝ)
    (hQ : Q = Cᵀ * C) (hQpsd : Q.PosSemidef) (hR : R.PosDef)
    (hctrb : BertsekasControllablePair A B)
    (hobs : BertsekasObservablePair A C) :
    ∃ P : Matrix (Fin n) (Fin n) ℝ, P.PosDef ∧
      BertsekasRiccatiMap A B Q R P = P ∧
      (∀ P' : Matrix (Fin n) (Fin n) ℝ, P'.PosSemidef →
        BertsekasRiccatiMap A B Q R P' = P' → P' = P) ∧
      (∀ P₀ : Matrix (Fin n) (Fin n) ℝ, P₀.PosSemidef →
        Filter.Tendsto (fun k => (BertsekasRiccatiMap A B Q R)^[k] P₀)
          Filter.atTop (nhds P)) := by
  -- l'iteration depuis `0` converge vers un point fixe semi-defini positif
  obtain ⟨P, hPsd, hfix, hlim⟩ := exists_psd_fixed_point_limit A B Q R hQpsd hR hctrb
  -- l'observabilite le rend defini positif
  have hPd : P.PosDef := limit_posDef A B C Q R hQ hQpsd hR hobs hPsd hlim
  -- attraction globale sur le cone
  have hattr : ∀ P₀ : Matrix (Fin n) (Fin n) ℝ, P₀.PosSemidef →
      Filter.Tendsto (fun k => (BertsekasRiccatiMap A B Q R)^[k] P₀)
        Filter.atTop (nhds P) :=
    fun P₀ hP₀ => riccati_global_attraction A B C Q R hQ hQpsd hR hobs hPd hfix hlim hP₀
  refine ⟨P, hPd, hfix, fun P' hP' hfix' => ?_, hattr⟩
  -- unicite : un point fixe est sa propre orbite, qui converge vers `P`
  have hconst : ∀ k, (BertsekasRiccatiMap A B Q R)^[k] P' = P' := by
    intro k
    induction k with
    | zero => rfl
    | succ k ih =>
        rw [Function.iterate_succ_apply' (f := BertsekasRiccatiMap A B Q R) (n := k), ih, hfix']
  have := hattr P' hP'
  simp only [hconst] at this
  exact tendsto_nhds_unique tendsto_const_nhds this

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open Matrix

namespace BertsekasDP

theorem riccati_psd_fixed_point_exists_unique_convergent {n m q : ℕ}
    (A : Matrix (Fin n) (Fin n) ℝ) (B : Matrix (Fin n) (Fin m) ℝ)
    (Q : Matrix (Fin n) (Fin n) ℝ) (R : Matrix (Fin m) (Fin m) ℝ)
    (C : Matrix (Fin q) (Fin n) ℝ)
    (hQ : Q = Cᵀ * C) (hQpsd : Q.PosSemidef) (hR : R.PosDef)
    (hctrb : BertsekasControllablePair A B)
    (hobs : BertsekasObservablePair A C) :
    ∃ P : Matrix (Fin n) (Fin n) ℝ, P.PosDef ∧
      BertsekasRiccatiMap A B Q R P = P ∧
      (∀ P' : Matrix (Fin n) (Fin n) ℝ, P'.PosSemidef →
        BertsekasRiccatiMap A B Q R P' = P' → P' = P) ∧
      (∀ P₀ : Matrix (Fin n) (Fin n) ℝ, P₀.PosSemidef →
        Filter.Tendsto (fun k => (BertsekasRiccatiMap A B Q R)^[k] P₀)
          Filter.atTop (nhds P)) := by
  first
  | exact _root_.Prove2me.Solution.BertsekasDP_riccati_psd_fixed_point_exists_unique_convergent A B Q R C hQ hQpsd hR hctrb hobs
  | (apply _root_.Prove2me.Solution.BertsekasDP_riccati_psd_fixed_point_exists_unique_convergent <;> assumption)

end BertsekasDP


end Prove2meStatement
