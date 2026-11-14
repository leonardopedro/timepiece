/-
Copyright (c) 2026.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BookProof

# The gradient-domination chain on the augmented Lagrangian, with no hypothesis left

§61/§63 refuted `VolDom` for the model's own penalty: along the shear family the volume residual is
flat while its gradient is not, so `lagGradDom_of_volDom` (`ChapterNsGradDomCoercive`) has an
unsatisfiable hypothesis and the NS chain stops there.  §64 then proved the penalty estimate *for the
repair* `V_μ = ½(εt)² + (μ/2)(t² + ε²)`, but never fed it back into the Lagrangian.

This file feeds it back.  In the shear/tilt coordinates `x₀ = t`, `x₁ = ε` — the two coordinates
§63 and §64 live in — the augmented Lagrangian is

  `W = 1 + ½(t² + ε²) + V_μ`

(`lagMu`), and the chain closes **unconditionally**:

  `lagGradDom_mu : ∃ a b, ∀ x, Σ_i (∂_i W)² ≤ a · W² + b`,
  `a = 2(5/μ + 1) + 2`,  `b = 2μ² + 2`.

No `VolDom` hypothesis appears: it is *proved* for this model.  The steps are the ones
`lagGradDom_of_volDom` spells out, and they are the reason the constants add rather than multiply:

* `(x_i + ∂_i V_μ)² ≤ 2x_i² + 2(∂_i V_μ)²`, so the shear quadratic enters with coefficient `2`;
* `Σ_i (∂_i V_μ)² ≤ A V_μ² + B` by `muPot_dom`;
* `V_μ ≥ 0` gives `V_μ ≤ W`, and `t² + ε² = 2(W − 1) ≤ W² + 1` since `W ≥ 1`.

**Scope.**  The model here has exactly the two coordinates of the shear family; it is the augmented
Lagrangian of §64, not `LagNsData`'s `volPot` (whose `VolDom` is false, §61).  What it removes is the
hypothesis: on this model the §49 chain (`GradBound → pointwise_dom_of_sq_sum → PotSelfBound`) runs
end to end with nothing assumed.

**The constants do not depend on the dimension (§3, §4).**  `lagGradDom_family` proves the same
estimate in `n` coordinates with the *same* `a = 2A + 2`, `b = 2B + 2`: the shear quadratic is
absorbed once, by `Σ_i x_i² = 2(W − 1 − V) ≤ W² + 1`, and no step multiplies by `n`.  §4 therefore
assembles the Lagrangian in the nine components of the 3D deformation gradient `∇ξ` — the coordinates
`volPot` actually lives in — with the two shear entries carrying the penalty and the other seven flat:
`lagGradDom_mu_nine`.  That is a statement about the *augmented* model in three dimensions, not about
the model's own `volPot`, whose `VolDom` stays false (§61).
-/

import BookProof.Ns.ChapterNsVolDomMuRepair

namespace BookProof.NsVolDomMuLagrangian

open MvPolynomial
open BookProof.NsVolDomExpansion BookProof.NsVolDomMuRepair

noncomputable section

/-! ## 1. The augmented Lagrangian in the shear coordinates -/

/-- **The augmented Lagrangian** `W = 1 + ½(t² + ε²) + V_μ`: the repair's penalty plus a coercive
quadratic in the same two coordinates.  This is `lagLyap`'s shape, not `lagEnergy`'s. -/
def quad : MvPolynomial (Fin 2) ℂ :=
  (X 0 : MvPolynomial (Fin 2) ℂ) * X 0 + (X 1 : MvPolynomial (Fin 2) ℂ) * X 1

def lagMu (mu : ℝ) : MvPolynomial (Fin 2) ℂ :=
  1 + ((1 / 2 : ℝ) : ℂ) • quad + muPot mu

theorem ev2_lagMu (mu : ℝ) (x : Fin 2 → ℝ) :
    (ev2 x (lagMu mu)).re
      = 1 + (1 / 2) * (x 0 ^ 2 + x 1 ^ 2) + (ev2 x (muPot mu)).re := by
  have hq : (ev2 x quad).re = x 0 ^ 2 + x 1 ^ 2 := by
    simp only [quad, ev2, map_add, map_mul, MvPolynomial.eval_X, Complex.add_re, Complex.mul_re,
      Complex.ofReal_re, Complex.ofReal_im]
    ring
  simp only [lagMu, ev2, map_add, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.eval_C,
    map_one, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.one_re]
  rw [hq]
  ring

/-- `W ≥ 1`: the penalty is non-negative and the quadratic is too. -/
theorem one_le_ev2_lagMu {mu : ℝ} (hmu : 0 < mu) (x : Fin 2 → ℝ) :
    1 ≤ (ev2 x (lagMu mu)).re := by
  rw [ev2_lagMu]
  have hV := ev2_muPot mu x
  rw [hV, Complex.ofReal_re]
  have hq : 0 ≤ (1 / 2 : ℝ) * (x 0 ^ 2 + x 1 ^ 2) := by positivity
  have hp : 0 ≤ (1 / 2) * (x 0 * x 1) ^ 2 + (mu / 2) * (x 0 ^ 2 + x 1 ^ 2) := by
    have h1 : 0 ≤ (1 / 2 : ℝ) * (x 0 * x 1) ^ 2 := by positivity
    have h2 : 0 ≤ (mu / 2) * (x 0 ^ 2 + x 1 ^ 2) := by
      have : 0 ≤ x 0 ^ 2 + x 1 ^ 2 := by positivity
      exact mul_nonneg (by linarith) this
    linarith
  linarith

section deriv

/-- The `t`-derivative of the augmented Lagrangian: the quadratic contributes `t`. -/
theorem ev2_pderiv_quad_zero (x : Fin 2 → ℝ) : (ev2 x (pderiv (0 : Fin 2) quad)).re = 2 * x 0 := by
  simp [quad, ev2]
  ring

theorem ev2_pderiv_quad_one (x : Fin 2 → ℝ) : (ev2 x (pderiv (1 : Fin 2) quad)).re = 2 * x 1 := by
  simp [quad, ev2]
  ring

theorem ev2_pderiv_lagMu_zero (mu : ℝ) (x : Fin 2 → ℝ) :
    (ev2 x (pderiv (0 : Fin 2) (lagMu mu))).re = x 0 + (ev2 x (pderiv 0 (muPot mu))).re := by
  have hq : (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (pderiv (0 : Fin 2) quad)).re
      = 2 * x 0 := ev2_pderiv_quad_zero x
  simp only [ev2, Fin.isValue, lagMu, one_div, Complex.ofReal_inv, Complex.ofReal_ofNat,
    smul_eq_C_mul, map_add, Derivation.map_one_eq_zero, Derivation.leibniz, smul_eq_mul,
    derivation_C, mul_zero, add_zero, zero_add, map_mul, eval_C, Complex.add_re, Complex.mul_re,
    Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat, div_self_mul_self', Complex.inv_im,
    Complex.im_ofNat, neg_zero, zero_div, zero_mul, sub_zero, add_left_inj]
  rw [hq]
  ring

theorem ev2_pderiv_lagMu_one (mu : ℝ) (x : Fin 2 → ℝ) :
    (ev2 x (pderiv (1 : Fin 2) (lagMu mu))).re = x 1 + (ev2 x (pderiv 1 (muPot mu))).re := by
  have hq : (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (pderiv (1 : Fin 2) quad)).re
      = 2 * x 1 := ev2_pderiv_quad_one x
  simp only [ev2, Fin.isValue, lagMu, one_div, Complex.ofReal_inv, Complex.ofReal_ofNat,
    smul_eq_C_mul, map_add, Derivation.map_one_eq_zero, Derivation.leibniz, smul_eq_mul,
    derivation_C, mul_zero, add_zero, zero_add, map_mul, eval_C, Complex.add_re, Complex.mul_re,
    Complex.inv_re, Complex.re_ofNat, Complex.normSq_ofNat, div_self_mul_self', Complex.inv_im,
    Complex.im_ofNat, neg_zero, zero_div, zero_mul, sub_zero, add_left_inj]
  rw [hq]
  ring

end deriv

/-! ## 2. The chain, unconditionally -/

/-- **Gradient domination for the augmented Lagrangian.**  With the `A = 5/μ + 1`, `B = μ²` of
`muPot_dom`, the squashed gradient of `W` is dominated by `(2A + 2)W² + (2B + 2)` at every real
point, with no hypothesis: `VolDom` for `V_μ` is discharged, not assumed. -/
theorem lagGradDom_mu {mu : ℝ} (hmu : 0 < mu) :
    ∃ a b : ℝ, ∀ x : Fin 2 → ℝ,
      (ev2 x (pderiv 0 (lagMu mu))).re ^ 2 + (ev2 x (pderiv 1 (lagMu mu))).re ^ 2
        ≤ a * (ev2 x (lagMu mu)).re ^ 2 + b := by
  obtain ⟨A, B, hA0, hB0, hAB⟩ := muPot_dom_nonneg hmu
  refine ⟨2 * A + 2, 2 * B + 2, fun x => ?_⟩
  -- the penalty's own estimate, which is the only input of the chain
  have hV := hAB x
  -- the potential is at most the Lagrangian
  have hVle : (ev2 x (muPot mu)).re ≤ (ev2 x (lagMu mu)).re := by
    rw [ev2_lagMu, ev2_muPot mu x, Complex.ofReal_re]
    have hq : 0 ≤ (1 / 2 : ℝ) * (x 0 ^ 2 + x 1 ^ 2) := by positivity
    have hp2 : 0 ≤ (mu / 2) * (x 0 ^ 2 + x 1 ^ 2) := by
      have h2 : 0 ≤ x 0 ^ 2 + x 1 ^ 2 := by positivity
      exact mul_nonneg (by linarith) h2
    linarith
  set V := (ev2 x (muPot mu)).re with hVdef
  set W := (ev2 x (lagMu mu)).re with hWdef
  have hV0 : 0 ≤ V := by
    rw [hVdef, ev2_muPot, Complex.ofReal_re]
    have h1 : 0 ≤ (1 / 2 : ℝ) * (x 0 * x 1) ^ 2 := by positivity
    have h2 : 0 ≤ (mu / 2) * (x 0 ^ 2 + x 1 ^ 2) := by
      have h2' : 0 ≤ x 0 ^ 2 + x 1 ^ 2 := by positivity
      exact mul_nonneg (by linarith) h2'
    linarith
  have hW1 : 1 ≤ W := one_le_ev2_lagMu hmu x
  -- the quadratic in terms of `W`
  have hquad : x 0 ^ 2 + x 1 ^ 2 = 2 * (W - 1 - V) := by
    rw [hWdef, ev2_lagMu, hVdef]
    ring
  have hquadle : x 0 ^ 2 + x 1 ^ 2 ≤ W ^ 2 + 1 := by
    rw [hquad]
    nlinarith
  -- each shear component gains at most `2x_i² + 2(∂_i V_μ)²`
  rw [ev2_pderiv_lagMu_zero, ev2_pderiv_lagMu_one]
  have hgrad : (x 0 + (ev2 x (pderiv 0 (muPot mu))).re) ^ 2
        + (x 1 + (ev2 x (pderiv 1 (muPot mu))).re) ^ 2
      ≤ 2 * (x 0 ^ 2 + x 1 ^ 2)
        + 2 * ((ev2 x (pderiv 0 (muPot mu))).re ^ 2
          + (ev2 x (pderiv 1 (muPot mu))).re ^ 2) := by
    nlinarith [sq_nonneg (x 0 - (ev2 x (pderiv 0 (muPot mu))).re),
      sq_nonneg (x 1 - (ev2 x (pderiv 1 (muPot mu))).re)]
  have hVW : V ^ 2 ≤ W ^ 2 := by nlinarith
  nlinarith [hV, hgrad, hVW, hVle, hquadle]

/-! ## 3. The chain in `n` coordinates, with dimension-free constants -/

variable {n : ℕ}

/-- **Gradient domination is dimension-independent.**  In `n` coordinates, with a non-negative
potential `V` whose own gradient is dominated (`hdom`, the `VolDom` of the potential) the augmented
Lagrangian `W = 1 + ½ Σ_i x_i² + V` obeys `Σ_i (∂_i W)² ≤ (2A + 2) W² + (2B + 2)` for **every** `n`:
the constants do not grow with the dimension, because the shear quadratic is absorbed by
`Σ_i x_i² = 2(W − 1 − V) ≤ W² + 1` exactly once. -/
theorem lagGradDom_family (A B : ℝ) (hA : 0 ≤ A)
    (V : (Fin n → ℝ) → ℝ) (d : (Fin n → ℝ) → Fin n → ℝ)
    (hV0 : ∀ x, 0 ≤ V x)
    (hdom : ∀ x, ∑ i, d x i ^ 2 ≤ A * V x ^ 2 + B) :
    ∀ x, ∑ i, (x i + d x i) ^ 2
      ≤ (2 * A + 2) * (1 + (1 / 2) * ∑ i, x i ^ 2 + V x) ^ 2 + (2 * B + 2) := by
  intro x
  set S := ∑ i, x i ^ 2 with hS
  set Vx := V x with hVx
  set G := ∑ i, d x i ^ 2 with hG
  set W := 1 + (1 / 2) * S + Vx with hW
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => sq_nonneg (x i)
  have hhalf : (0 : ℝ) ≤ 1 / 2 * S := mul_nonneg (by norm_num) hS0
  have hW1 : 1 ≤ W := by rw [hW]; linarith [hV0 x]
  have hVle : Vx ≤ W := by rw [hW]; linarith [hV0 x]
  have hVW : Vx ^ 2 ≤ W ^ 2 := by nlinarith [hVle, hV0 x]
  have hkey : S ≤ W ^ 2 + 1 := by
    rw [hW]
    nlinarith [sq_nonneg (1 + 1 / 2 * S + Vx - 1), hS0, hV0 x]
  have hstep : ∑ i, (x i + d x i) ^ 2 ≤ 2 * S + 2 * G := by
    rw [hS, hG, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_le_sum fun i _ => ?_
    nlinarith [sq_nonneg (x i - d x i)]
  have hdomx := hdom x
  nlinarith [hstep, hdomx, hVW, hkey, hA, hW1]

/-! ## The nine-component instance: the shape of the 3D volume penalty -/

/-- The two shear coordinates inside the nine components of `∇ξ` (three rows, three columns). -/
def emb9 : Fin 2 → Fin 9 := fun i => if i = 0 then 0 else 1

/-- The augmented penalty, read in the nine-component coordinates of the 3D deformation gradient. -/
def V9 (mu : ℝ) (x : Fin 9 → ℝ) : ℝ := (ev2 (fun j => x (emb9 j)) (muPot mu)).re

/-- Its gradient, in the same nine coordinates: only the two shear components carry a derivative. -/
def d9 (mu : ℝ) (x : Fin 9 → ℝ) (i : Fin 9) : ℝ :=
  if i = 0 then (ev2 (fun j => x (emb9 j)) (pderiv 0 (muPot mu))).re
  else if i = 1 then (ev2 (fun j => x (emb9 j)) (pderiv 1 (muPot mu))).re
  else 0

theorem d9_eq_zero (mu : ℝ) (x : Fin 9 → ℝ) {i : Fin 9} (h0 : i ≠ 0) (h1 : i ≠ 1) :
    d9 mu x i = 0 := by
  simp [d9, h0, h1]

/-- The nine-component gradient sum is the two-component one: the other seven directions are
flat. -/
theorem d9_sum (mu : ℝ) (x : Fin 9 → ℝ) :
    ∑ i, d9 mu x i ^ 2
      = (ev2 (fun j => x (emb9 j)) (pderiv 0 (muPot mu))).re ^ 2
        + (ev2 (fun j => x (emb9 j)) (pderiv 1 (muPot mu))).re ^ 2 := by
  rw [Fin.sum_univ_succ, Fin.sum_univ_succ]
  have hz : ∑ i : Fin 7, d9 mu x i.succ.succ ^ 2 = 0 := by
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [d9_eq_zero mu x ?_ ?_]
    · simp
    · intro h
      have hv := congrArg Fin.val h
      rw [Fin.val_succ, Fin.val_succ] at hv
      simp at hv
    · intro h
      have hv := congrArg Fin.val h
      rw [Fin.val_succ, Fin.val_succ] at hv
      have h1 : ((1 : Fin 9) : ℕ) = 1 := rfl
      rw [h1] at hv
      omega
  rw [hz, add_zero]
  simp [d9, emb9]

/-- **The estimate in nine coordinates.**  The 3D volume penalty lives in the nine components of
`∇ξ`; here the augmented Lagrangian is assembled in exactly those nine coordinates and the chain
closes with the *same* `a = 2A + 2`, `b = 2B + 2` as in two: the dimension is not what the constants
depend on. -/
theorem lagGradDom_mu_nine {mu : ℝ} (hmu : 0 < mu) :
    ∃ a b : ℝ, ∀ x : Fin 9 → ℝ,
      ∑ i, (x i + d9 mu x i) ^ 2
        ≤ a * (1 + (1 / 2) * ∑ i, x i ^ 2 + V9 mu x) ^ 2 + b := by
  obtain ⟨A, B, hA0, _hB0, hAB⟩ := muPot_dom_nonneg hmu
  refine ⟨2 * A + 2, 2 * B + 2, fun x => ?_⟩
  refine lagGradDom_family A B hA0 (V9 mu) (d9 mu) ?_ ?_ x
  · intro y
    rw [V9, ev2_muPot mu (fun j => y (emb9 j)), Complex.ofReal_re]
    have h1 : 0 ≤ (1 / 2 : ℝ) * (y (emb9 0) * y (emb9 1)) ^ 2 := by positivity
    have h2 : 0 ≤ (mu / 2) * (y (emb9 0) ^ 2 + y (emb9 1) ^ 2) := by
      have h2' : 0 ≤ y (emb9 0) ^ 2 + y (emb9 1) ^ 2 := by positivity
      exact mul_nonneg (by linarith) h2'
    linarith
  · intro y
    rw [d9_sum]
    exact hAB (fun j => y (emb9 j))


end

end BookProof.NsVolDomMuLagrangian
