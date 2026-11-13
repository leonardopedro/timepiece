/-
Copyright (c) 2026.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BookProof

# `VolDom` is false: the normal form across a unimodular shear (§58, sharpened)

Section §58 of `SM_ESA_COMPLETION_PLAN.md` records two facts about the incompressibility penalty
`V_κ`: the shear family `F = I + t N + ε B` (`N = e_x ⊗ e_y`, `B = e_y ⊗ e_x`) leaves `det F = 1`,
so `V_κ` is flat along it, while a transversal tilt makes `det F − 1 = −ε t + O(ε²)`.  The
measurement
`scripts/eval-vol-dom.py` then reports

  `|∇V_κ|² / V_κ²  =  4/ε² + 4/t²`     (saturating in `t` at fixed `ε`).

This file proves that law as an identity, for the **normal form** of the penalty across the family:
the leading behaviour `V_κ ≈ (κ/2)(ε t)²` is a genuine polynomial in the two parameters, and the
squashed gradient of *any* potential of that shape is exactly `4/t² + 4/ε²` times its square.

The consequence is `not_volDom_shear`: no constants `A`, `B` dominate the gradient by the potential,
because the ratio is unbounded as the tilt shrinks. The bridge from `volPot` to this normal form is
the second-order expansion of §58.1 (plus the measurement); it is *not* formalized here, and the
`VolDom` refutation for the model's literal `volPot` remains unproved in Lean.
-/

import BookProof.Ns.ChapterNsGradDomCoercive

namespace BookProof.NsVolDomShear

open MvPolynomial

/-! ## 1. The normal form along the shear -/

/-- The two parameters are `x 0 = t` (shear amplitude) and `x 1 = ε` (tilt).  The penalty's leading
term across the family is `(ε t)² / 2`: quadratic in the tilt and quadratic in the shear amplitude,
with no linear or constant part — that is exactly what `det F − 1 = −ε t + O(ε²)` produces. -/
noncomputable def shearPot : MvPolynomial (Fin 2) ℂ :=
  ((1 / 2 : ℝ) : ℂ) • ((X 0 * X 1) * (X 0 * X 1))

/-- Evaluation at a real point of `ℝ²`. -/
abbrev ev2 (x : Fin 2 → ℝ) (p : MvPolynomial (Fin 2) ℂ) : ℂ :=
  MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p

theorem ev2_shearPot (x : Fin 2 → ℝ) :
    (ev2 x shearPot).re = (x 0 * x 1) ^ 2 / 2 := by
  simp [ev2, shearPot]
  ring

/-- **The penalty is flat along the shear, at every amplitude**: at zero tilt the potential vanishes
identically, not merely at first order. -/
theorem ev2_shearPot_flat (t : ℝ) : (ev2 (fun i => if i = 0 then t else 0) shearPot).re = 0 := by
  rw [ev2_shearPot]
  simp

theorem ev2_shearPot_nonneg (x : Fin 2 → ℝ) : 0 ≤ (ev2 x shearPot).re := by
  rw [ev2_shearPot]; positivity

/-- `∂_t V = ε² t`: the gradient along the shear grows like `t`, though the potential is flat. -/
theorem ev2_pderiv_zero (x : Fin 2 → ℝ) :
    (ev2 x (pderiv 0 shearPot)).re = x 0 * x 1 ^ 2 := by
  simp [ev2, shearPot, pderiv_X]
  ring

/-- `∂_ε V = ε t²`. -/
theorem ev2_pderiv_one (x : Fin 2 → ℝ) :
    (ev2 x (pderiv 1 shearPot)).re = x 0 ^ 2 * x 1 := by
  simp [ev2, shearPot, pderiv_X]
  ring

/-! ## 2. The exact ratio law -/

/-- **The measured law, as an identity.**  The squashed gradient is the potential's square times
`4/t² + 4/ε²`.  Note both terms: the `4/ε²` is the one the sweep saturates at, and `4/t²` is the
correction visible at moderate `t`. -/
theorem shear_grad_sq {x : Fin 2 → ℝ} (h0 : x 0 ≠ 0) (h1 : x 1 ≠ 0) :
    (ev2 x (pderiv 0 shearPot)).re ^ 2 + (ev2 x (pderiv 1 shearPot)).re ^ 2
      = (ev2 x shearPot).re ^ 2 * (4 / x 0 ^ 2 + 4 / x 1 ^ 2) := by
  rw [ev2_pderiv_zero, ev2_pderiv_one, ev2_shearPot]
  field_simp
  ring

/-! ## 3. No constants dominate the gradient by the potential -/

/-- **`VolDom` fails for the normal form.**  Suppose `∑ (∂V)² ≤ A V² + B`.  Fix the tilt at a
small `ε > 0` and let the shear amplitude run: the potential grows like `ε⁴t⁴`, the gradient term
`∂_t V` grows like `ε²t⁴` — one power of `ε` slower — so the bound fails for every `A`, `B`.

The tilt is chosen from `A` itself: `ε² A < 4` is what makes the gradient outrun the potential.
This is the mechanism behind §58's measurement, in the exact two-parameter geometry of the shear
family; it does not by itself refute `VolDom` for the model's literal `volPot`, whose expansion onto
this normal form is the analytic step of §58.1. -/
theorem not_volDom_shear :
    ¬ ∃ A B : ℝ, ∀ x : Fin 2 → ℝ,
      (ev2 x (pderiv 0 shearPot)).re ^ 2 + (ev2 x (pderiv 1 shearPot)).re ^ 2
        ≤ A * (ev2 x shearPot).re ^ 2 + B := by
  rintro ⟨A, B, h⟩
  -- the family `(t, ε) = (1/d, d)`: the *product* `ε t` is the constant `1`,
  -- so the potential is the constant `1/2` while the gradient grows like `1/d`.
  set d : ℝ := 1 / (|A| + |B| + 4) with hd
  have hden : 0 < |A| + |B| + 4 := by positivity
  have hdpos : 0 < d := by rw [hd]; positivity
  have hK : 1 / d = |A| + |B| + 4 := by
    rw [hd]
    field_simp
  set x : Fin 2 → ℝ := fun i => if i = 0 then 1 / d else d with hx
  have hx0 : x 0 = 1 / d := by simp [hx]
  have hx1 : x 1 = d := by simp [hx]
  have hpt := h x
  rw [ev2_pderiv_zero, ev2_pderiv_one, ev2_shearPot, hx0, hx1] at hpt
  -- the potential is `1/2`, fixed along the whole family
  have hdt : (1 / d) * d = 1 := by field_simp
  have hV : ((1 / d) * d) ^ 2 / 2 = 1 / 2 := by rw [hdt]; norm_num
  rw [hV] at hpt
  have e1 : (1 / d) * d ^ 2 = d := by field_simp
  have e2 : (1 / d) ^ 2 * d = 1 / d := by field_simp
  rw [e1, e2] at hpt
  -- `d ^ 2 + (1/d) ^ 2 ≤ A/4 + B` with `1/d = |A| + |B| + 4`
  have hK4 : (4 : ℝ) ≤ 1 / d := by
    rw [hK]
    linarith [abs_nonneg A, abs_nonneg B]
  have hAB : A / 4 + B ≤ 1 / d := by
    have hA4 : A / 4 ≤ |A| / 4 := by linarith [le_abs_self A]
    have hB : B ≤ |B| := le_abs_self B
    have hAB' : |A| / 4 + |B| ≤ 1 / d := by
      rw [hK]
      linarith [abs_nonneg A, abs_nonneg B]
    linarith
  have hsq : (1 / d) ^ 2 > 1 / d := by nlinarith
  nlinarith [hpt, hsq, hAB, sq_nonneg d]

end BookProof.NsVolDomShear
