/-
Copyright (c) 2026.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BookProof

# The second-order expansion behind the shear normal form

§61 of `SM_ESA_COMPLETION_PLAN` proved that the penalty's *normal form* across the shear family,
`V = (εt)²/2`, has the exact ratio law `∑(∂V)² = V²(4/t² + 4/ε²)` and is not dominated.  The bridge
from that normal form to the model's literal `volPot` was left as §58.1's expansion.  This file
formalizes the expansion's engine, and the one place where it could have hidden a constant.

**1. The determinant.**  For the two explicit `3 × 3` matrices `N = e_x ⊗ e_y` and `B = e_y ⊗ e_x`
of §58, the volume residual across `F = I + tN + εB` is *exactly*

  `det(I + tN + εB) = 1 − ε t`   (`det_one_add_smul`),

with no `O(ε²)` term at all: `det(I + tN) = 1` for every amplitude (`det_one_add_shM`) because
`N² = 0`, and the tilt's pure second-order contribution vanishes (`tlM_mul_self`).  So the
second-order structure that produces the quartic normal form is an identity for this family, not an
asymptotic.  `volResid_*` state the three consequences separately (flatness in `t`, flatness in `ε`,
and the mixed coefficient `−1`).

**2. The transfer.**  Since `V` is a *positive multiple* of `(εt)²` — the multiplier is the profile's
amplitude and the penalty weight `κ/2` — and the ratio law is invariant under that multiplier
(`normForm_grad_sq`: it holds for every `c`, including `c = 0`), nothing in §61 depended on the
profile's constant.  So `not_volDom_normForm` refutes domination for **every** positive multiple of
the normal form, and `volDom_fails_of_normal_form` transfers that to any potential whose value is
`c(εt)²` with `c ≠ 0`.

**Scope.**  What is *not* formalized is the passage from the model's `volPot` to a value of the form
`c(εt)²` on the family — that is the Fourier reconstruction of `det F − 1` (Parseval plus the
convolution `detCoef`), and it is where the profile constant is produced.  §58's measurement and
§61's tables are the numerical evidence for it; this file supplies the algebraic half, exactly.
-/

import BookProof.Ns.ChapterNsVolDomShear

namespace BookProof.NsVolDomExpansion

open MvPolynomial

/-! ## 1. The two shear matrices and their determinant -/

/-- The shear direction `N = e_x ⊗ e_y`: `N² = 0`, so `I + tN` is unimodular at every amplitude.
Written as an indicator so that its entries compute without unfolding a matrix literal. -/
def shM : Matrix (Fin 3) (Fin 3) ℝ := fun i j => if i = 0 ∧ j = 1 then 1 else 0

/-- The transversal tilt `B = e_y ⊗ e_x` of §58. -/
def tlM : Matrix (Fin 3) (Fin 3) ℝ := fun i j => if i = 1 ∧ j = 0 then 1 else 0

theorem shM_apply (i j : Fin 3) :
    shM i j = if i = 0 ∧ j = 1 then 1 else 0 := rfl

theorem tlM_apply (i j : Fin 3) :
    tlM i j = if i = 1 ∧ j = 0 then 1 else 0 := rfl

theorem shM_mul_self : shM * shM = 0 := by
  ext i j
  simp only [shM, Matrix.mul_apply, Fin.sum_univ_three, Matrix.zero_apply]
  fin_cases j <;> simp

theorem tlM_mul_self : tlM * tlM = 0 := by
  ext i j
  simp only [tlM, Matrix.mul_apply, Fin.sum_univ_three, Matrix.zero_apply]
  fin_cases i <;> simp

/-- The shear matrix `I + tN` in entries. -/
theorem one_add_shM_eq (t : ℝ) :
    (1 + t • shM) = !![1, t, 0; 0, 1, 0; 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [shM, Matrix.add_apply, Matrix.smul_apply]

/-- **The shear is volume preserving at every amplitude.**  `det(I + tN) = 1` identically — not
just to first order — which is what makes the penalty flat along the family. -/
theorem det_one_add_shM (t : ℝ) : (1 + t • shM).det = 1 := by
  rw [one_add_shM_eq]
  simp [Matrix.det_fin_three]

/-- **The second-order expansion, exactly.**  Along `F = I + tN + εB` the volume residual is
`−εt`: the linear terms in `t` and in `ε` are absent and there is no `ε²` or `t²` term, so the
residual is purely the mixed second-order term.  This is the identity that §58.1 expanded to. -/
theorem det_one_add_smul (t ε : ℝ) :
    (1 + t • shM + ε • tlM).det = 1 - ε * t := by
  have h : (1 + t • shM + ε • tlM) = !![1, t, 0; ε, 1, 0; 0, 0, 1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [shM, tlM, Matrix.add_apply, Matrix.smul_apply]
  rw [h]
  simp [Matrix.det_fin_three]
  ring

/-- The volume residual of the family. -/
noncomputable def volResid (t ε : ℝ) : ℝ := (1 + t • shM + ε • tlM).det - 1

/-- Flat in the shear: the residual vanishes at zero tilt. -/
theorem volResid_zero_tilt (t : ℝ) : volResid t 0 = 0 := by
  have h := det_one_add_smul t 0
  simp only [zero_smul, add_zero] at h
  simp [volResid, h]

/-- Flat in the tilt: the residual vanishes at zero shear.  Together with `volResid_zero_tilt` this
says the two *pure* second-order coefficients vanish, so the expansion has no `t²` or `ε²` term. -/
theorem volResid_zero_shear (ε : ℝ) : volResid 0 ε = 0 := by
  have h := det_one_add_smul 0 ε
  simp only [zero_smul, add_zero] at h
  simp [volResid, h]

/-- **The mixed coefficient is `−1`**, and it is the whole residual. -/
theorem volResid_eq (t ε : ℝ) : volResid t ε = -(ε * t) := by
  rw [volResid, det_one_add_smul]
  ring

/-! ## 2. The transfer through the amplitude constant -/

/-- The normal form `c·(εt)²` for an arbitrary amplitude constant `c`. -/
noncomputable def normForm (c : ℝ) : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.C ((c : ℂ)) * ((X 0 * X 1) * (X 0 * X 1))

abbrev ev2 (x : Fin 2 → ℝ) (p : MvPolynomial (Fin 2) ℂ) : ℂ :=
  MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p

theorem ev2_normForm (c : ℝ) (x : Fin 2 → ℝ) :
    ev2 x (normForm c) = ((c * (x 0 * x 1) ^ 2 : ℝ) : ℂ) := by
  simp only [ev2, normForm, map_mul, MvPolynomial.eval_C, MvPolynomial.eval_X]
  push_cast
  ring

theorem pderiv_normForm_zero (c : ℝ) (x : Fin 2 → ℝ) :
    (ev2 x (pderiv 0 (normForm c))).re = 2 * c * (x 0 * x 1) * x 1 := by
  simp [ev2, normForm, pderiv_X]
  ring

theorem pderiv_normForm_one (c : ℝ) (x : Fin 2 → ℝ) :
    (ev2 x (pderiv 1 (normForm c))).re = 2 * c * (x 0 * x 1) * x 0 := by
  simp [ev2, normForm, pderiv_X]
  ring

/-- **The ratio law is independent of the amplitude constant.**  For every `c`, `∑(∂V)²` is
`V²(4/t² + 4/ε²)` — so §61's law does not depend on which positive multiple of `(εt)²` the model's
profile produces. -/
theorem normForm_grad_sq (c : ℝ) {x : Fin 2 → ℝ} (h0 : x 0 ≠ 0) (h1 : x 1 ≠ 0) :
    (ev2 x (pderiv 0 (normForm c))).re ^ 2 + (ev2 x (pderiv 1 (normForm c))).re ^ 2
      = (ev2 x (normForm c)).re ^ 2 * (4 / x 0 ^ 2 + 4 / x 1 ^ 2) := by
  rw [pderiv_normForm_zero, pderiv_normForm_one]
  have hV := ev2_normForm c x
  rw [hV]
  simp only [Complex.ofReal_re]
  field_simp
  ring

/-- `shearPot` of §61 is the amplitude `c = 1/2` of the normal form. -/
theorem shearPot_eq_normForm : NsVolDomShear.shearPot = normForm (1 / 2) := by
  simp [normForm, NsVolDomShear.shearPot, MvPolynomial.smul_eq_C_mul]

/-- **No constants dominate any nonzero multiple of the normal form.**  The refuting family is the
same `(t, ε) = (1/d, d)` of §61; the constant `c` only rescales the two sides. -/
theorem not_volDom_normForm (c : ℝ) (hc : c ≠ 0) :
    ¬ ∃ A B : ℝ, ∀ x : Fin 2 → ℝ,
      (ev2 x (pderiv 0 (normForm c))).re ^ 2 + (ev2 x (pderiv 1 (normForm c))).re ^ 2
        ≤ A * (ev2 x (normForm c)).re ^ 2 + B := by
  rintro ⟨A, B, h⟩
  -- The family is `(t, ε) = (K, 1/K)`: the product `εt` is `1`, so `V ≡ c` while the gradient
  -- still grows like `K`.  `K` absorbs the constants, the amplitude `c`, and `1/(4c²)`.
  set K : ℝ := (|A| + |B|) * (1 + c ^ 2) + 1 / (4 * c ^ 2) + 4 with hK
  have hc2 : 0 < c ^ 2 := by positivity
  have hKpos : 0 < K := by
    rw [hK]
    have : 0 < 1 / (4 * c ^ 2) := by positivity
    nlinarith [abs_nonneg A, abs_nonneg B, sq_nonneg c]
  have hKin : 1 ≤ 4 * c ^ 2 * K := by
    have h1 : 1 / (4 * c ^ 2) ≤ K := by
      rw [hK]; nlinarith [abs_nonneg A, abs_nonneg B, sq_nonneg c]
    have h2 : (4 * c ^ 2) * (1 / (4 * c ^ 2)) = 1 := by field_simp
    have h4 : (0 : ℝ) < 4 * c ^ 2 := by positivity
    have h3 := mul_le_mul_of_nonneg_left h1 (le_of_lt h4)
    nlinarith [h1, hc2, h2, h3]
  have hKbound : A * c ^ 2 + B ≤ K := by
    have hA : A * c ^ 2 ≤ |A| * (1 + c ^ 2) := by
      have hcsq : (0 : ℝ) ≤ c ^ 2 := by positivity
      have hc1 : c ^ 2 ≤ 1 + c ^ 2 := by nlinarith [sq_nonneg c]
      -- the multiplier `c²` is nonnegative, so scaling preserves the order
      have hmul : A * c ^ 2 ≤ |A| * c ^ 2 :=
        mul_le_mul_of_nonneg_right (le_abs_self A) hcsq
      nlinarith [abs_nonneg A, hc1, hmul]
    have hB : B ≤ |B| * (1 + c ^ 2) := by
      have h1 : (0:ℝ) ≤ |B| := abs_nonneg B
      have h2 : (0:ℝ) ≤ c ^ 2 := by positivity
      nlinarith [le_abs_self B]
    rw [hK]
    have hpos : 0 < 1 / (4 * c ^ 2) := by positivity
    nlinarith [hA, hB, hpos]
  -- evaluate at `x = (K, 1/K)`
  set x : Fin 2 → ℝ := fun i => if i = 0 then K else 1 / K with hx
  have hx0 : x 0 = K := by simp [hx]
  have hx1 : x 1 = 1 / K := by simp [hx]
  have hprod : x 0 * x 1 = 1 := by
    rw [hx0, hx1]; field_simp
  have hpt := h x
  rw [pderiv_normForm_zero, pderiv_normForm_one] at hpt
  have hV := ev2_normForm c x
  rw [hV, hprod] at hpt
  simp only [Complex.ofReal_re, one_pow, mul_one] at hpt
  rw [hx0, hx1] at hpt
  -- the two gradient pieces are `2cK` and `2c/K` (up to the factors of `1` from `εt`)
  have e1 : 2 * c * (1 / K) = 2 * c / K := by ring
  rw [e1] at hpt
  -- `(2c/K)² + (2cK)² ≥ K ≥ A c² + B`: contradiction
  have hsq : (2 * c / K) ^ 2 + (2 * c * K) ^ 2 = 4 * c ^ 2 * (1 / K ^ 2 + K ^ 2) := by
    field_simp
    ring
  rw [hsq] at hpt
  have hbig : 4 * c ^ 2 * K ^ 2 ≥ K := by
    have h1 : 4 * c ^ 2 * K ^ 2 = (4 * c ^ 2 * K) * K := by ring
    rw [h1]
    exact le_mul_of_one_le_left (le_of_lt hKpos) hKin
  have hK2 : (0 : ℝ) < 1 / K ^ 2 := div_pos one_pos (pow_pos hKpos 2)
  have hpos2 : (0 : ℝ) < 4 * c ^ 2 * (1 / K ^ 2) := by positivity
  have hmix : 4 * c ^ 2 * (1 / K ^ 2 + K ^ 2)
      = 4 * c ^ 2 * (1 / K ^ 2) + 4 * c ^ 2 * K ^ 2 := by ring
  nlinarith [hpt, hmix, hbig, hpos2, hKbound]

/-- **The transfer, stated as a hypothesis on the potential.**  Any potential of the two parameters
whose value is `c(εt)²` with `c ≠ 0` fails `VolDom`; this is what the model's `volPot` needs to
supply on the family, and the only thing the expansion has to produce. -/
theorem volDom_fails_of_normal_form (V : MvPolynomial (Fin 2) ℂ) (c : ℝ) (hc : c ≠ 0)
    (hV : V = normForm c) :
    ¬ ∃ A B : ℝ, ∀ x : Fin 2 → ℝ,
      (ev2 x (pderiv 0 V)).re ^ 2 + (ev2 x (pderiv 1 V)).re ^ 2
        ≤ A * (ev2 x V).re ^ 2 + B := by
  subst hV
  exact not_volDom_normForm c hc

end BookProof.NsVolDomExpansion
