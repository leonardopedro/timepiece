/-
Copyright (c) 2026.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BookProof

# Gradient domination for the deformation-norm repair

§61 shows the shear normal form `V = (εt)²/2` cannot be dominated: `∑(∂V)²` grows like `V^{3/2}` along
`tε = const`.  `ChapterNsVolDomExpansion` transfers that to every nonzero multiple of the normal form,
so no *constant* rescaling of the volume penalty repairs it.

This file closes the chain for the one repair that does work, and states exactly what it changes.  The
repair adds a deformation-norm mass term,

  `V_μ(t, ε) = ½(εt)² + (μ/2)(t² + ε²)`,   `μ > 0`,

i.e. the original volume penalty plus `(μ/2)|F − I|²` in the two shear amplitudes.  Then

  `∑(∂V_μ)² = ab(a+b) + 4μab + μ²(a+b)`,  `V_μ = ½(ab + μ(a+b))`,  `a = t²`, `b = ε²`,

and the gradient-domination inequality holds with **explicit constants**

  `∑(∂V_μ)² ≤ (5/μ + 1)·V_μ² + μ²`   (`muPot_dom`).

The four steps are `ab(a+b) ≤ V²/μ` (AM–GM), `4μab ≤ μ(a+b)² ≤ 4V²/μ`, `μ²(a+b) ≤ V² + μ²`
(these are the two cheap directions), and, in the absence of the last one, the bound fails at
`(t, ε) → 0`: the `μ²` constant is *necessary*, not slack, which is why the statement is affine in
`V²` rather than homogeneous.  `muPot_zero` records that `μ = 0` is exactly §61's potential, so the
mass term — not any rescaling — is what makes the chain close.  `muPot_no_hom_dom` proves the
`B > 0` half too: for *every* `A` there is a state with `∑(∂V_μ)² > A·V_μ²`, on the diagonal
`t = ε → 0`, so the affine shape is not an artefact of the estimates.

**Scope.**  This is a *family-level* closure of a **changed** Lagrangian: the model's own `volPot` is
the `μ = 0` member, which stays un-dominated.  What is proven here is that the deformation-norm
augmentation removes the obstruction with constants that are uniform in the state and explicit in `μ`,
and that the obstruction at `μ = 0` is recovered exactly (`muPot_zero` + `not_volDom_normForm`).
-/

import BookProof.Ns.ChapterNsVolDomExpansion

namespace BookProof.NsVolDomMuRepair

open MvPolynomial

/-- The deformation-norm repair family: half the squared volume residual plus `(μ/2)(t² + ε²)`. -/
noncomputable def muPot (mu : ℝ) : MvPolynomial (Fin 2) ℂ :=
  MvPolynomial.C ((1 / 2 : ℂ)) * ((X 0 * X 1) * (X 0 * X 1))
    + MvPolynomial.C ((mu / 2 : ℂ)) * (X 0 ^ 2 + X 1 ^ 2)

/-- At `μ = 0` the repair is exactly §61's shear normal form: the change is the mass term alone. -/
theorem muPot_zero : muPot 0 = NsVolDomExpansion.normForm (1 / 2) := by
  simp [muPot, NsVolDomExpansion.normForm]

/-- The repaired potential is `½(ab) + (μ/2)(a + b)` on `a = t²`, `b = ε²`. -/
theorem ev2_muPot (mu : ℝ) (x : Fin 2 → ℝ) :
    NsVolDomExpansion.ev2 x (muPot mu)
      = (((1 / 2) * (x 0 * x 1) ^ 2 + (mu / 2) * (x 0 ^ 2 + x 1 ^ 2) : ℝ) : ℂ) := by
  simp only [NsVolDomExpansion.ev2, muPot, map_mul, map_add, map_pow,
    MvPolynomial.eval_C, MvPolynomial.eval_X]
  push_cast
  ring

/-- The `t`-derivative of the repair is `t(ε² + μ)`. -/
theorem pderiv_muPot_zero (mu : ℝ) (x : Fin 2 → ℝ) :
    (NsVolDomExpansion.ev2 x (pderiv 0 (muPot mu))).re = x 0 * (x 1 ^ 2 + mu) := by
  simp [NsVolDomExpansion.ev2, muPot, pderiv_X]
  ring

/-- The `ε`-derivative of the repair is `ε(t² + μ)`. -/
theorem pderiv_muPot_one (mu : ℝ) (x : Fin 2 → ℝ) :
    (NsVolDomExpansion.ev2 x (pderiv 1 (muPot mu))).re = x 1 * (x 0 ^ 2 + mu) := by
  simp [NsVolDomExpansion.ev2, muPot, pderiv_X]
  ring

/-- **The algebraic core.**  For `a, b ≥ 0` and `μ > 0`,

  `4μ·(Σ) ≤ (5 + μ)·(ab + μ(a+b))² + 4μ³`,  `Σ = ab(a+b) + 4μab + μ²(a+b)`.

Multiplying by `4μ` clears the division so that every step is polynomial: the three estimates are
`4μ·ab(a+b) ≤ (ab+μ(a+b))²`, `16μ²ab ≤ 4(ab+μ(a+b))²`, and `4μ³(a+b) ≤ μ(ab+μ(a+b))² + 4μ³`. -/
theorem muPot_quad_bound (mu a b : ℝ) (hmu : 0 < mu) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    4 * mu * (a * b * (a + b) + 4 * mu * (a * b) + mu ^ 2 * (a + b))
      ≤ (5 + mu) * (a * b + mu * (a + b)) ^ 2 + 4 * mu ^ 3 := by
  have hp : 0 ≤ a * b := mul_nonneg ha hb
  have hq : 0 ≤ a + b := by linarith
  set s : ℝ := a * b + mu * (a + b) with hs
  -- `μ(a+b) ≤ s`, since `ab ≥ 0`
  have hsp : mu * (a + b) ≤ s := by rw [hs]; linarith
  -- step 1: `4μ·ab(a+b) ≤ s²` from `(ab − μ(a+b))² ≥ 0`
  have h1 : 4 * mu * (a * b * (a + b)) ≤ s ^ 2 := by
    have := sq_nonneg (a * b - mu * (a + b))
    rw [hs]; nlinarith
  -- step 2: `4ab ≤ (a+b)²`, hence `16μ²ab ≤ 4s²` via `μ²(a+b)² ≤ s²`
  have h2 : 4 * (a * b) ≤ (a + b) ^ 2 := by
    have := sq_nonneg (a - b); nlinarith
  have hsq : mu ^ 2 * (a + b) ^ 2 ≤ s ^ 2 := by
    have hd : 0 ≤ s - mu * (a + b) := by linarith
    have hsm : 0 ≤ s + mu * (a + b) := by nlinarith [hsp, hq, hmu.le]
    nlinarith [mul_nonneg hd hsm]
  have h2b : 16 * mu ^ 2 * (a * b) ≤ 4 * s ^ 2 := by
    have hm2 : (0 : ℝ) < 4 * mu ^ 2 := by positivity
    have hprod := mul_le_mul_of_nonneg_left h2 (le_of_lt hm2)
    have hsq2 : 4 * mu ^ 2 * (a + b) ^ 2 ≤ 4 * s ^ 2 := by linarith [hsq]
    nlinarith [hprod, hsq2]
  -- step 3: `4μ³(a+b) ≤ μs² + 4μ³` from `μ(a+b) ≤ s` and `(s − 2μ)² ≥ 0`
  have h3 : 4 * mu ^ 3 * (a + b) ≤ mu * s ^ 2 + 4 * mu ^ 3 := by
    have h4 := sq_nonneg (s - 2 * mu)
    nlinarith [hsp, hmu.le]
  nlinarith [h1, h2b, h3]

/-- **Gradient domination for the repair, with explicit constants.**  `A = 5/μ + 1` and `B = μ²`
work uniformly in the state; `B > 0` is needed because the ratio `∑(∂V)²/V²` diverges as
`(t, ε) → 0`. -/
theorem muPot_dom (mu : ℝ) (hmu : 0 < mu) :
    ∃ A B : ℝ, ∀ x : Fin 2 → ℝ,
      (NsVolDomExpansion.ev2 x (pderiv 0 (muPot mu))).re ^ 2
          + (NsVolDomExpansion.ev2 x (pderiv 1 (muPot mu))).re ^ 2
        ≤ A * (NsVolDomExpansion.ev2 x (muPot mu)).re ^ 2 + B := by
  refine ⟨5 / mu + 1, mu ^ 2, fun x => ?_⟩
  rw [pderiv_muPot_zero, pderiv_muPot_one]
  have hV := ev2_muPot mu x
  rw [hV]
  simp only [Complex.ofReal_re]
  set a : ℝ := x 0 ^ 2 with ha'
  set b : ℝ := x 1 ^ 2 with hb'
  have ha : 0 ≤ a := sq_nonneg _
  have hb : 0 ≤ b := sq_nonneg _
  set s : ℝ := a * b + mu * (a + b) with hs'
  -- the two gradient pieces reconstruct the algebraic `Σ`
  have hsum : (x 0 * (x 1 ^ 2 + mu)) ^ 2 + (x 1 * (x 0 ^ 2 + mu)) ^ 2
      = a * b * (a + b) + 4 * mu * (a * b) + mu ^ 2 * (a + b) := by
    rw [ha', hb']; ring
  -- and the value is `s/2`
  have hval : (1 / 2) * (x 0 * x 1) ^ 2 + (mu / 2) * (x 0 ^ 2 + x 1 ^ 2) = s / 2 := by
    rw [← ha', ← hb', hs']
    ring
  rw [hsum, hval]
  have hkey := muPot_quad_bound mu a b hmu ha hb
  have h4 : (0 : ℝ) < 4 * mu := by linarith
  have hstep : a * b * (a + b) + 4 * mu * (a * b) + mu ^ 2 * (a + b)
      ≤ ((5 + mu) * s ^ 2 + 4 * mu ^ 3) / (4 * mu) := by
    rw [le_div_iff₀ h4]; linarith
  have hsplit : ((5 + mu) * s ^ 2 + 4 * mu ^ 3) / (4 * mu)
      = (5 / mu + 1) * (s / 2) ^ 2 + mu ^ 2 := by
    field_simp
    ring
  linarith [hstep, hsplit]

set_option maxHeartbeats 1600000 in
-- the final refutation multiplies high-degree monomials in `δ` and `μ`, which is slow to certify
/-- **The constant is necessary: no homogeneous domination.**  For every `A` there is a state with
`∑(∂V_μ)² > A·V_μ²`, because on the diagonal `t = ε → 0` the gradient sum decays like `t²` while
`V_μ²` decays like `t⁴`.  So `muPot_dom`'s affine form `A·V² + B` is not an artefact of the proof:
with `B = 0` the chain fails for every `A`. -/
theorem muPot_no_hom_dom (mu : ℝ) (hmu : 0 < mu) :
    ¬ ∃ A : ℝ, ∀ x : Fin 2 → ℝ,
      (NsVolDomExpansion.ev2 x (pderiv 0 (muPot mu))).re ^ 2
          + (NsVolDomExpansion.ev2 x (pderiv 1 (muPot mu))).re ^ 2
        ≤ A * (NsVolDomExpansion.ev2 x (muPot mu)).re ^ 2 := by
  rintro ⟨A, hA⟩
  -- the diagonal amplitude: `δ ≤ 1` makes `δ² ≤ δ`, so both smallness conditions hold at once
  set δ : ℝ := min (min (mu / 2) 1) (1 / (|A| + 1)) with hδ
  have hδpos : 0 < δ := lt_min (lt_min (by linarith) one_pos) (by positivity)
  have hδle1 : δ ≤ 1 := le_trans (min_le_left _ _) (min_le_right _ _)
  have hδleμ : δ ≤ mu / 2 := le_trans (min_le_left _ _) (min_le_left _ _)
  have hδleA : δ ≤ 1 / (|A| + 1) := min_le_right _ _
  have hd2le1 : δ ^ 2 ≤ δ := by nlinarith [hδpos.le, hδle1]
  have hd2μ : δ ^ 2 ≤ mu / 2 := le_trans hd2le1 hδleμ
  have hd2A : A * δ ^ 2 ≤ 1 := by
    have h1 : δ * (|A| + 1) ≤ 1 := by
      calc δ * (|A| + 1) ≤ (1 / (|A| + 1)) * (|A| + 1) :=
            mul_le_mul_of_nonneg_right hδleA (by positivity)
        _ = 1 := by field_simp
    have hmul : A * δ ^ 2 ≤ |A| * δ ^ 2 :=
      mul_le_mul_of_nonneg_right (le_abs_self A) (sq_nonneg δ)
    have hstep : |A| * δ ^ 2 ≤ |A| * δ :=
      mul_le_mul_of_nonneg_left hd2le1 (abs_nonneg A)
    nlinarith [h1, hmul, hstep, hδpos.le]
  -- evaluate on the diagonal `x = (δ, δ)`
  set x : Fin 2 → ℝ := fun _ => δ with hx
  have hx0 : x 0 = δ := rfl
  have hx1 : x 1 = δ := rfl
  have hpt := hA x
  rw [pderiv_muPot_zero, pderiv_muPot_one] at hpt
  have hV := ev2_muPot mu x
  rw [hV] at hpt
  simp only [Complex.ofReal_re] at hpt
  have hgrad : (x 0 * (x 1 ^ 2 + mu)) ^ 2 + (x 1 * (x 0 ^ 2 + mu)) ^ 2
      = 2 * δ ^ 2 * (δ ^ 2 + mu) ^ 2 := by
    simp only [hx0, hx1]
    ring
  have hval : (1 / 2) * (x 0 * x 1) ^ 2 + (mu / 2) * (x 0 ^ 2 + x 1 ^ 2)
      = (1 / 2) * (δ ^ 4 + 2 * mu * δ ^ 2) := by
    simp only [hx0, hx1]
    ring
  rw [hgrad, hval] at hpt
  -- the two-sided estimate: LHS decays like `δ²`, RHS like `δ⁴`
  have hd2pos : 0 < δ ^ 2 := by positivity
  have hL : mu ^ 2 ≤ (δ ^ 2 + mu) ^ 2 := by nlinarith [hd2pos.le]
  have hRp : (δ ^ 2 + 2 * mu) ^ 2 ≤ (5 * mu / 2) ^ 2 := by nlinarith [hd2μ, hmu.le]
  have h4 : (0 : ℝ) ≤ 4 := by norm_num
  have h4p := mul_le_mul_of_nonneg_left hpt h4
  have hstep1 : 8 * δ ^ 2 * (δ ^ 2 + mu) ^ 2 ≤ A * δ ^ 4 * (δ ^ 2 + 2 * mu) ^ 2 := by
    have hid : A * (δ ^ 4 + 2 * mu * δ ^ 2) ^ 2 = A * δ ^ 4 * (δ ^ 2 + 2 * mu) ^ 2 := by
      ring
    nlinarith [h4p, hid]
  have hm1 : A * δ ^ 4 * (δ ^ 2 + 2 * mu) ^ 2 ≤ δ ^ 2 * (δ ^ 2 + 2 * mu) ^ 2 := by
    have hnn : (0 : ℝ) ≤ δ ^ 2 * (δ ^ 2 + 2 * mu) ^ 2 := by positivity
    nlinarith [mul_le_mul_of_nonneg_right hd2A hnn]
  have hm2 : δ ^ 2 * (δ ^ 2 + 2 * mu) ^ 2 ≤ δ ^ 2 * (5 * mu / 2) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hRp hd2pos.le]
  have h8 : 8 * δ ^ 2 * mu ^ 2 ≤ 8 * δ ^ 2 * (δ ^ 2 + mu) ^ 2 := by
    nlinarith [mul_le_mul_of_nonneg_left hL (by positivity : (0 : ℝ) ≤ 8 * δ ^ 2)]
  have hpos : 0 < δ ^ 2 * mu ^ 2 := by positivity
  nlinarith [h8, hstep1, hm1, hm2, hpos]

end BookProof.NsVolDomMuRepair
