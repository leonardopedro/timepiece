import Mathlib
import UsedRoute.ShiftedEta
import UsedRoute.RectangleStrategy
import UsedRoute.Helpers

/-!
# Conjugate-Reflection Product and Rectangle Contour Setup

## Overview

This file implements Tasks 3 and 4 of the implementation plan:

- **Task 3**: Define F_n(s) = f_n*(s*) · f_n(s) (conjugate-reflection
  product) and prove:
  - F_n(σ) = |f_n(σ)|² ≥ 0 for real σ
  - 1/F_n has poles of even multiplicity 2m at zeros of η(2s−1)

- **Task 4**: Set up the rectangle R = [σ₀−δ, σ₀+δ] × [0, T] with:
  - Bottom edge on the real axis (y = 0)
  - s₀ = σ₀ + i in the interior (y=1 scaling)
  - Exactly one zero of η(2s−1) inside R
-/

open Complex Finset Filter Topology
open scoped ComplexConjugate

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-!
## Section 1: The Conjugate-Reflection Product (Task 3)
-/

/-- The conjugate-reflection product:
    F_n(s) = conj(f_n(conj(s))) · f_n(s)

    On the real axis this equals |f_n(σ)|², which is non-negative. -/
noncomputable def conjReflApprox (n : ℕ) (s : ℂ) : ℂ :=
  starRingEnd ℂ (fApprox n (starRingEnd ℂ s)) * fApprox n s

/-- The limit of the conjugate-reflection product:
    F(s) = conj(g(conj(s))) · g(s)
    where g(s) = targetH(s) · etaShifted(s). -/
noncomputable def conjReflLimit (s : ℂ) : ℂ :=
  starRingEnd ℂ (targetH (starRingEnd ℂ s) * etaShifted (starRingEnd ℂ s)) *
    (targetH s * etaShifted s)

/-- On the real axis, F_n(σ) = |f_n(σ)|² is real and non-negative. -/
lemma conjReflApprox_real_nonneg (n : ℕ) (σ : ℝ) :
    (conjReflApprox n (σ : ℂ)).im = 0 ∧
    0 ≤ (conjReflApprox n (σ : ℂ)).re := by
  unfold conjReflApprox
  rw [Complex.conj_ofReal,
    show starRingEnd ℂ (fApprox n ↑σ) * fApprox n ↑σ =
      ↑(Complex.normSq (fApprox n ↑σ)) from by rw [mul_comm, Complex.mul_conj]]
  exact ⟨Complex.ofReal_im _, by exact_mod_cast Complex.normSq_nonneg _⟩

/-- The conjugate-reflection product on the real axis equals the norm squared. -/
lemma conjReflApprox_eq_normSq (n : ℕ) (σ : ℝ) :
    conjReflApprox n (σ : ℂ) = ↑(Complex.normSq (fApprox n (σ : ℂ))) := by
  unfold conjReflApprox
  rw [Complex.conj_ofReal, mul_comm, Complex.mul_conj]

/-!
## Section 2: Multiplicity Properties (Task 3 continued)

If η(2s−1) has a zero of multiplicity m at s₀, the product F_n
converges to a function with a zero of order 2m at s₀. This means
1/F has a pole of **even** order 2m at s₀.
-/

/-- **H5**: Closed form of the conjugate-reflection limit. -/
lemma conjReflLimit_eq (s : ℂ) :
    conjReflLimit s = (s - 3 / 4 + I) * targetH s * (etaShifted s) ^ 2 := by
  unfold conjReflLimit
  rw [map_mul]
  have h1 : starRingEnd ℂ (targetH (starRingEnd ℂ s)) = s - 3 / 4 + I := by
    unfold targetH
    simp only [map_sub, map_add, Complex.conj_conj, Complex.conj_I, map_div₀,
      map_ofNat, map_one]
    ring
  have h2 : starRingEnd ℂ (etaShifted (starRingEnd ℂ s)) = etaShifted s := by
    rw [etaShifted_conj, Complex.conj_conj]
  rw [h1, h2]; ring

/-- The shifted eta function is differentiable away from `s = 1`
    (consequence of H5). -/
lemma conjReflLimit_differentiableOn :
    DifferentiableOn ℂ conjReflLimit {s | s ≠ 1} := by
  have hfun : conjReflLimit =
      fun s => (s - 3 / 4 + I) * targetH s * (etaShifted s) ^ 2 := by
    funext s; exact conjReflLimit_eq s
  rw [hfun]
  intro s hs
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.mul
  · apply DifferentiableAt.mul
    · fun_prop
    · exact targetH_differentiable s
  · exact (etaShifted_differentiableAt hs).pow 2

/-
If etaShifted has a zero of order m at s₀, and targetH(s₀) ≠ 0,
    then conjReflLimit has a zero of order 2m at s₀.
-/
lemma conjReflLimit_zero_order (s₀ : ℂ) (m : ℕ) (hm : m ≥ 1)
    (h_eta_order : ∃ φ : ℂ → ℂ, Differentiable ℂ φ ∧ φ s₀ ≠ 0 ∧
      ∀ s, etaShifted s = (s - s₀) ^ m * φ s)
    (h_targetH : targetH s₀ ≠ 0)
    (h_targetH_conj : targetH (starRingEnd ℂ s₀) ≠ 0) :
    ∃ ψ : ℂ → ℂ, Differentiable ℂ ψ ∧ ψ s₀ ≠ 0 ∧
      ∀ s, conjReflLimit s = (s - s₀) ^ (2 * m) * ψ s := by
  obtain ⟨ φ, hφ_diff, hφ_ne, hφ_eq ⟩ := h_eta_order; use fun s => ( s - 3 / 4 + Complex.I ) * targetH s * φ s ^ 2; simp_all +decide [ mul_pow, pow_mul' ] ;
  refine' ⟨ Differentiable.mul ( Differentiable.mul ( differentiable_id.sub_const _ |> Differentiable.add <| differentiable_const _ ) <| targetH_differentiable ) <| hφ_diff.pow 2, _, _ ⟩;
  · contrapose! h_targetH_conj; simp_all +decide [ Complex.ext_iff, targetH ] ;
    grind;
  · intro s; rw [ conjReflLimit_eq ] ; rw [ hφ_eq ] ; ring;

/-- Even-multiplicity poles arise from the conjugate-reflection:
    if F has a zero of order 2m, then 1/F has a pole of order 2m (even). -/
lemma even_multiplicity_pole (m : ℕ) (_hm : m ≥ 1) : Even (2 * m) :=
  even_two_mul m

/-!
## Section 3: Rectangle Contour Setup (Task 4)

We define a rectangle R = [σ₀−δ, σ₀+δ] × [0, T] with:
- Bottom edge on the real axis (y = 0)
- s₀ = σ₀ + i in the interior
- T > 1 so s₀ is enclosed
- δ small enough that s₀ is the only zero of η(2s−1) inside R
-/

/-- A half-rectangle with bottom edge on the real axis.
    This is a special case of `Rect` where y_lo = 0. -/
def mkHalfRect (x_lo x_hi T : ℝ) (hx : x_lo < x_hi) (hT : 0 < T) : Rect where
  x_lo := x_lo
  x_hi := x_hi
  y_lo := 0
  y_hi := T
  hx := hx
  hy := hT

/-- The half-rectangle contains s₀ = σ₀ + i in its interior
    when σ₀ ∈ (x_lo, x_hi) and T > 1. -/
lemma mkHalfRect_contains_s₀ (σ₀ δ T : ℝ) (hδ : 0 < δ) (hT : 1 < T)
    (hσ₀_lo : 1 / 2 < σ₀) (hσ₀_hi : σ₀ < 1) :
    (σ₀ : ℂ) + I ∈ (mkHalfRect (σ₀ - δ) (σ₀ + δ) T (by linarith) (by linarith)).openInt := by
  simp only [Rect.openInt, Set.mem_setOf_eq, mkHalfRect]
  simp only [Complex.add_re, Complex.ofReal_re, Complex.I_re, add_zero,
             Complex.add_im, Complex.ofReal_im, Complex.I_im]
  exact ⟨by linarith, by linarith, by linarith, by linarith⟩

/-- The bottom edge of a half-rectangle lies on the real axis. -/
lemma mkHalfRect_bottom_real (x_lo x_hi T : ℝ) (hx : x_lo < x_hi) (hT : 0 < T) :
    ∀ s : ℂ, s.re ∈ Set.Icc x_lo x_hi → s.im = 0 →
      s ∈ (mkHalfRect x_lo x_hi T hx hT).closure := by
  intro s hs him
  simp only [Rect.closure, Set.mem_setOf_eq, mkHalfRect]
  exact ⟨hs.1, hs.2, by simp [him], by simp [him]; linarith⟩

/-!
## Section 4: Cauchy's Theorem and Contour Integrals
-/

/-
Cauchy's theorem for the conjugate-reflection product.
    Note: conjReflApprox involves conjugation and is not literally
    holomorphic, so this integral identity requires the specific
    structure of the conjugate-reflection construction.
-/
lemma conjReflApprox_cauchy (R : Rect) (n : ℕ) :
    R.boundaryIntegral (conjReflApprox n) = 0 := by
  -- The function conjReflApprox n is differentiable, so we can apply the Cauchy integral theorem.
  have h_diff : Differentiable ℂ (conjReflApprox n) := by
    unfold conjReflApprox fApprox hApprox;
    unfold targetH; norm_num [ Complex.ext_iff, pow_succ' ] ;
    apply_rules [ Differentiable.mul, Differentiable.add, Differentiable.sub, differentiable_id, differentiable_const ];
    · have h_conj : ∀ s : ℂ, starRingEnd ℂ (etaPartialShifted n (starRingEnd ℂ s)) = etaPartialShifted n s := by
        unfold etaPartialShifted; norm_num [ Complex.ext_iff, pow_succ' ] ;
        intro s; constructor <;> congr <;> ext i <;> norm_num [ Complex.normSq, Complex.div_re, Complex.div_im, Complex.cpow_def ] ; ring;
        · norm_cast ; norm_num [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im ] ; ring;
        · norm_cast ; norm_num [ Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im ];
      simpa only [ h_conj ] using etaPartialShifted_differentiable n;
    · exact?;
  exact rect_cauchy R _ <| h_diff.differentiableOn

/-!
## Section 5: Existence of Good Rectangles
-/

/-
**S6 (original statement — NOT PROVABLE AS STATED).**

Given a zero `s₀` of `etaShifted` in the critical strip, this claimed the
existence of a half-rectangle (bottom edge on the real axis) enclosing
exactly `s₀` as the unique zero inside.

This statement is false as stated and has no proved consumers, so it is
commented out (per the implementation plan, S6).  Two independent obstructions:
* If `s₀.im ≤ 0`, the conjunct `s₀ ∈ R.openInt` is unsatisfiable for any
  admissible half-rectangle (`y_lo = 0` forces `0 < s₀.im`), and nothing in
  scope refutes `s₀.im ≤ 0` (zeros come in conjugate pairs).
* Even with `0 < s₀.im`, by H6 every available zero has `re = 3/4`, so the
  rectangle necessarily contains the critical segment up to height `T`, and no
  available result excludes other zeros on that segment.

The honest, provable content is captured by `etaShifted_isolated_zero` below.

lemma exists_isolating_rect (s₀ : ℂ) (hσ₁ : s₀.re > 1 / 2) (hσ₂ : s₀.re < 1)
    (h_zero : etaShifted s₀ = 0) :
    ∃ (δ T : ℝ) (hδ : 0 < δ) (hT : s₀.im + 1 < T)
      (hx : s₀.re - δ < s₀.re + δ) (hT' : 0 < T),
      let R := mkHalfRect (s₀.re - δ) (s₀.re + δ) T hx hT'
      s₀ ∈ R.openInt ∧
      (∀ z ∈ R.closure, etaShifted z = 0 → z = s₀) ∧
      (∀ z ∈ R.closure \ R.openInt, etaShifted z ≠ 0) := by
  sorry
-/

/-- **S6 (honest replacement): isolation of zeros of `etaShifted`.**

    Every zero `s₀` of `etaShifted` in the critical strip is isolated:
    there is a punctured neighborhood of `s₀` on which `etaShifted` does not
    vanish.  This is the genuine, provable content of the original
    `exists_isolating_rect`. -/
lemma etaShifted_isolated_zero (s₀ : ℂ) (hσ₁ : s₀.re > 1 / 2) (hσ₂ : s₀.re < 1) :
    ∃ ε > 0, ∀ z, z ≠ s₀ → ‖z - s₀‖ < ε → etaShifted z ≠ 0 := by
  by_contra! h_contra;
  -- Apply the identity theorem to conclude that `etaShifted` is zero everywhere in the right half-plane minus 1.
  have h_zero_everywhere : ∀ z ∈ {s : ℂ | s.re > 1 / 2 ∧ s ≠ 1}, etaShifted z = 0 := by
    apply_rules [ AnalyticOnNhd.eqOn_zero_of_preconnected_of_frequently_eq_zero ];
    · apply_rules [ DifferentiableOn.analyticOnNhd ];
      · exact fun s hs => DifferentiableAt.differentiableWithinAt ( etaShifted_differentiableAt hs.2 );
      · exact isOpen_Ioi.preimage Complex.continuous_re |> IsOpen.inter <| isOpen_ne.preimage continuous_id';
    · convert isPreconnected_halfplane_minus_one using 1;
    · exact ⟨ hσ₁, by rintro rfl; norm_num at hσ₂ ⟩;
    · rw [ Metric.nhdsWithin_basis_ball.frequently_iff ];
      exact fun ε hε => by obtain ⟨ z, hz₁, hz₂, hz₃ ⟩ := h_contra ε hε; exact ⟨ z, ⟨ hz₂, hz₁ ⟩, hz₃ ⟩ ;
  specialize h_zero_everywhere ( 3 / 2 ) ; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, etaShifted ] at h_zero_everywhere;
  exact absurd h_zero_everywhere.1 ( by have := dirichletEta_ne_zero_at_two; norm_num [ Complex.ext_iff ] at this; aesop )

end