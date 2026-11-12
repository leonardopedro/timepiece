/-
Copyright (c) 2026 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib
import BookProof.Sm.ChapterSmGaussWeightedIbp
import BookProof.Sm.ChapterSmReverseEllipticQuartic

/-!
# Why the Standard Model's potential satisfies the gradient domination

Work order: `SM_ESA_COMPLETION_PLAN` §49 (P4).

## 1. The question

`SM_ESA_COMPLETION_PLAN` §48 reduced P4's `PotSelfBound` to one algebraic hypothesis, `GradDom`:

  `∑_{j∈S} ‖(∂_j W) p‖²  ≤  a ‖W p‖² + b ‖p‖²`,

for `W = smPotPoly P c₀ = ∑_{r<49} Φ_r² + ∑_{m∈M} q_m² + c₀`, the 49 forms being the 24 gluon
magnetic components, the 9 weak ones, the 3 hypercharge ones, the 12 covariant Higgs derivatives
and the wall (`BookProof.SmHamiltonian.smFormPoly`).  §48 showed the hypothesis is not automatic —
it holds for `X₀⁴ + X₁⁴` and fails for `X₀²X₁²` — and left it open.

The reason the flat pattern is *not* what happens here is that `W` is not a bare quartic: it
carries the **coercive quadratic** `∑_{m∈M} q_m²`, and every `∂_j Φ_r` (`j ∈ M`) is at most
**linear**.  Those two facts give `|∂_j W|² ≲ (1 + W)·W`, hence `GradDom` with explicit constants.
So the answer to the question is **affirmative**, and §49.3 records it in the two halves that a
formal statement needs:

* `wsSum` is the shape `∑_r Φ_r² + ∑_m x_m² + c₀`, `polyW_wsSum` its pointwise value;
* `pointwise_dom_of_sq_sum` — **the structural theorem**: a gradient bound
  `(∂_j Φ_r)² ≤ C (1 + ∑_m x_m²)` for the family members yields the pointwise domination
  `∑_{j∈M} (∂_j W)² ≤ a W² + b` with `a = 16 M N C + 8`, `b = 8 M N C + 8`;
* `gradDom_flat_plus_quadratic` — the model case `X₀²X₁² + X₀² + X₁²`, i.e. exactly the flat
  quartic of §48 `not_gradDom_flat_quartic` **plus** the quadratic term.  The flat quartic alone
  fails for every `a, b`; with the quadratic term it satisfies the domination with `a = b = 32`.
  This is the theorem that says the SM's flat directions are not an obstruction;
* `smPotPoly_eq_wsSum` — `smPotPoly` is `wsSum` at the 49 forms and the 40 momentum coordinates,
  which is what lets `pointwise_dom_of_sq_sum` be applied to the Standard Model's potential;

## 2. What is and is not instantiated

Turning the structural theorem into `GradDom` for `smPotPoly` needs two steps.  The second (§3c) is
carried out here; the first (§3b) is reduced to the per-form `pderiv` computation alone:

* **The per-form support table.**  `(∂_j Φ_r)² ≤ C (1 + ∑_m x_m²)` is a statement about
  `smFormPoly`: it needs to know that `pderiv j (smPhi P r)` for `j ∈ smS` is at most linear *and*
  involves no coordinate outside `smS` (the derivative coordinates `smDG`/`smDW`/`smDB`/`smDPhi`
  carry no momentum and are not controlled by `W`).  §49.4 of the plan lists that table for the five
  families.  §3b below reduces it to a single target: `gradBound_of_linear` produces `GradBound`
  from any support table `L` and coefficient vectors `b` with `∂_j Φ_r = ∑_{i∈L} b_i x_i`, all
  `L ⊆ smS`, so what remains is the `pderiv` computation for each of the five families, not any
  further analysis.
* **The `L²` transfer.**  `GradDom` is an `L²` inequality, and `exists_potSelfBound_of_gradDom`
  consumes that form.  The passage is *not* in this module: it is
  `BookProof.SmGradDomTransfer.l2_gradDom_of_pointwise`, where the pointwise bound is multiplied by
  `‖p(x)‖² ≥ 0` and integrated (`gaussInt_re_mono` against `norm_pgLp_sq`), and
  `exists_potSelfBound_of_gradBound` composes it with §3's `pointwise_dom_of_sq_sum` and §3c's
  identification into `∃ β, PotSelfBound P c₀ β`.

So the integration step and the algebra are both closed; `PotSelfBound` for the SM now depends on
one input, the per-form `pderiv`/support table, which §3b reduces to its stated form.  Until that
table is written down, `PotSelfBound` stays a hypothesis.

Everything here is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmGradDomStructural

open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.DegSchrodinger BookProof.GaussCoreQuadBounds
open BookProof.SmComparisonEsa BookProof.SmOneParticle BookProof.SmHamiltonian
open BookProof.SmFarisLavine BookProof.SmGaussWeightedIbp BookProof.YangMillsHermite
open BookProof.SmReverseEllipticQuartic

noncomputable section

variable {d : ℕ}

/-! ## 1. The pointwise algebra of `polyW` -/

theorem polyW_add (p q : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    polyW (p + q) x = polyW p x + polyW q x := by
  simp [polyW, MvPolynomial.eval_add]

theorem polyW_sum {ι : Type} (s : Finset ι) (f : ι → MvPolynomial (Fin d) ℂ) (x : Vd d) :
    polyW (∑ i ∈ s, f i) x = ∑ i ∈ s, polyW (f i) x := by
  simp [polyW, Complex.re_sum]

theorem polyW_C_eq (c : ℝ) (x : Vd d) :
    polyW (C ((c : ℝ) : ℂ) : MvPolynomial (Fin d) ℂ) x = c := by
  simp [polyW]

theorem polyW_X_eq (i : Fin d) (x : Vd d) :
    polyW (X i : MvPolynomial (Fin d) ℂ) x = x i := by
  simp [polyW]

theorem polyW_mul {p q : MvPolynomial (Fin d) ℂ} (hp : RealCoeff p) (hq : RealCoeff q)
    (x : Vd d) : polyW (p * q) x = polyW p x * polyW q x := by
  have h1 := polyW_ofReal (d := d) hp x
  have h2 := polyW_ofReal (d := d) hq x
  have hval : MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (p * q)
      = ((polyW p x : ℝ) : ℂ) * ((polyW q x : ℝ) : ℂ) := by
    rw [MvPolynomial.eval_mul, ← h1, ← h2]
  rw [polyW, hval, ← Complex.ofReal_mul, Complex.ofReal_re]

theorem realCoeff_pderiv' {q : MvPolynomial (Fin d) ℂ} (hq : RealCoeff q) (j : Fin d) :
    RealCoeff (pderiv j q) := by
  rw [RealCoeff, starP_pderiv, show starP q = q from hq]

/-- The `R`-th derivative of a square of a real form: `∂_j (Φ²) = 2 Φ ∂_j Φ`. -/
theorem polyW_pderiv_sq {q : MvPolynomial (Fin d) ℂ} (hq : RealCoeff q) (j : Fin d) (x : Vd d) :
    polyW (pderiv j (q * q)) x = 2 * (polyW q x * polyW (pderiv j q) x) := by
  have hd : RealCoeff (pderiv j q) := realCoeff_pderiv' hq j
  rw [pderiv_mul]
  rw [polyW_add (d := d), polyW_mul hd hq, polyW_mul hq hd]
  ring

/-- `∂_j (∑_{m∈M} x_m²) = 2 x_j` on `M`, and `0` off it. -/
theorem pderiv_sum_sq_X (M : Finset (Fin d)) (j : Fin d) :
    pderiv j (∑ m ∈ M, (X m * X m : MvPolynomial (Fin d) ℂ))
      = if j ∈ M then 2 * X j else 0 := by
  rw [map_sum]
  by_cases hj : j ∈ M
  · rw [if_pos hj, Finset.sum_eq_single j]
    · rw [pderiv_mul, pderiv_X_self]
      ring
    · intro b _ hb
      rw [pderiv_mul, pderiv_X_of_ne hb]
      simp
    · intro hcon
      exact absurd hj hcon
  · rw [if_neg hj]
    refine Finset.sum_eq_zero fun m hm => ?_
    have hmj : m ≠ j := fun h => hj (h ▸ hm)
    rw [pderiv_mul, pderiv_X_of_ne hmj]
    simp

/-! ## 2. The potential assembled from a family of forms -/

/-- **The shape of the Standard-Model potential**: a sum of squares of forms, plus a coercive
quadratic term on a coordinate set `M`, plus a constant. -/
def wsSum {ι : Type} [Fintype ι] (Φ : ι → MvPolynomial (Fin d) ℂ) (M : Finset (Fin d)) (c0 : ℝ) :
    MvPolynomial (Fin d) ℂ :=
  (∑ r, Φ r * Φ r) + (∑ m ∈ M, X m * X m) + C ((c0 : ℝ) : ℂ)

theorem realCoeff_wsSum {ι : Type} [Fintype ι] (Φ : ι → MvPolynomial (Fin d) ℂ)
    (hΦ : ∀ r, RealCoeff (Φ r)) (M : Finset (Fin d)) (c0 : ℝ) :
    RealCoeff (wsSum Φ M c0) :=
  ((RealCoeff.sum fun r _ => (hΦ r).mul (hΦ r)).add
    (RealCoeff.sum fun m _ => (realCoeff_X m).mul (realCoeff_X m))).add
    (realCoeff_C_real c0)

/-- **The pointwise value of the assembled potential**:
`W(x) = ∑_r Φ_r(x)² + ∑_{m∈M} x_m² + c₀`. -/
theorem polyW_wsSum {ι : Type} [Fintype ι] (Φ : ι → MvPolynomial (Fin d) ℂ)
    (hΦ : ∀ r, RealCoeff (Φ r)) (M : Finset (Fin d)) (c0 : ℝ) (x : Vd d) :
    polyW (wsSum Φ M c0) x
      = (∑ r, (polyW (Φ r) x) ^ 2) + (∑ m ∈ M, (x m) ^ 2) + c0 := by
  rw [wsSum, polyW_add, polyW_add, polyW_sum, polyW_C_eq, polyW_sum]
  congr 2
  · refine Finset.sum_congr rfl fun r _ => ?_
    rw [polyW_mul (hΦ r) (hΦ r), sq]
  · refine Finset.sum_congr rfl fun m _ => ?_
    rw [polyW_mul (realCoeff_X m) (realCoeff_X m), polyW_X_eq, sq]

/-- **The derivative of the assembled potential**:
`∂_j W = 2 ∑_r Φ_r ∂_j Φ_r + 2 x_j` on `M`. -/
theorem polyW_pderiv_wsSum {ι : Type} [Fintype ι] (Φ : ι → MvPolynomial (Fin d) ℂ)
    (hΦ : ∀ r, RealCoeff (Φ r)) (M : Finset (Fin d)) (c0 : ℝ) {j : Fin d} (hj : j ∈ M)
    (x : Vd d) :
    polyW (pderiv j (wsSum Φ M c0)) x
      = 2 * (∑ r, polyW (Φ r) x * polyW (pderiv j (Φ r)) x) + 2 * x j := by
  have hX : polyW (pderiv j (∑ m ∈ M, (X m * X m : MvPolynomial (Fin d) ℂ))) x = 2 * x j := by
    rw [pderiv_sum_sq_X, if_pos hj]
    simp [polyW, MvPolynomial.eval_mul]
  rw [wsSum, map_add, map_add, pderiv_C, polyW_add (d := d), polyW_add (d := d)]
  have hz : polyW (0 : MvPolynomial (Fin d) ℂ) x = 0 := by simp [polyW]
  rw [hz, add_zero, hX, map_sum, polyW_sum]
  rw [Finset.sum_congr rfl fun r _ => polyW_pderiv_sq (hΦ r) j x, ← Finset.mul_sum]

/-! ## 3. The structural domination -/

/-- **The gradient hypothesis on a family of forms**: every `∂_j Φ_r` (`j ∈ M`) is dominated by
the coercive quadratic.  For the Standard Model this is where the *support* of `pderiv j Φ_r`
enters: it must not involve the coordinates outside `M` (the derivative coordinates), and it is at
most linear. -/
def GradBound {ι : Type} (Φ : ι → MvPolynomial (Fin d) ℂ) (M : Finset (Fin d)) (C : ℝ) : Prop :=
  ∀ (j : Fin d), j ∈ M → ∀ r, ∀ x : Vd d,
    (polyW (pderiv j (Φ r)) x) ^ 2 ≤ C * (1 + ∑ m ∈ M, (x m) ^ 2)

set_option maxHeartbeats 1000000 in
-- the `163`-coordinate sums exceed the default elaboration budget
/-- **One coordinate of the structural domination.**  With `A_r = Φ_r(x)`, `B_{jr} = ∂_j Φ_r(x)`,
Cauchy–Schwarz gives `(∑_r A_r B_{jr})² ≤ (∑_r A_r²)(∑_r B_{jr}²)`, and both factors are
controlled: `∑_r A_r² ≤ W(x)` and `∑_r B_{jr}² ≤ N C (1 + ∑_m x_m²)`. -/
theorem sq_pderiv_le {ι : Type} [Fintype ι] (Φ : ι → MvPolynomial (Fin d) ℂ)
    (hΦ : ∀ r, RealCoeff (Φ r)) (M : Finset (Fin d)) {c0 C : ℝ} (hc0 : 0 ≤ c0)
    (hC : 0 ≤ C) (hdom : GradBound Φ M C) {j : Fin d} (hj : j ∈ M) (x : Vd d) :
    (polyW (pderiv j (wsSum Φ M c0)) x) ^ 2
      ≤ 8 * polyW (wsSum Φ M c0) x
          * ((Fintype.card ι : ℝ) * C * (1 + ∑ m ∈ M, (x m) ^ 2)) + 8 * (x j) ^ 2 := by
  set A : ι → ℝ := fun r => polyW (Φ r) x with hA
  set B : ι → ℝ := fun r => polyW (pderiv j (Φ r)) x with hB
  set S2 : ℝ := ∑ m ∈ M, (x m) ^ 2 with hS2
  set Wv : ℝ := polyW (wsSum Φ M c0) x with hW
  set NC : ℝ := (Fintype.card ι : ℝ) * C with hNC
  set P : ℝ := ∑ r, A r * B r with hP
  set Qs : ℝ := ∑ r, A r ^ 2 with hQ
  set Rs : ℝ := ∑ r, B r ^ 2 with hR
  have hS2nonneg : 0 ≤ S2 := by
    rw [hS2]
    exact Finset.sum_nonneg fun m _ => sq_nonneg _
  have hQs0 : 0 ≤ Qs := by
    rw [hQ]
    exact Finset.sum_nonneg fun r _ => sq_nonneg _
  have hRs0 : 0 ≤ Rs := by
    rw [hR]
    exact Finset.sum_nonneg fun r _ => sq_nonneg _
  have hWval : Wv = Qs + S2 + c0 := by
    rw [hW, hQ, hS2]
    exact polyW_wsSum Φ hΦ M c0 x
  have hAsq : Qs ≤ Wv := by rw [hWval]; linarith
  have hWnonneg : 0 ≤ Wv := by rw [hWval]; linarith
  have hCnonneg : 0 ≤ C := hC
  have hNCnonneg : 0 ≤ NC := by
    rw [hNC]
    exact mul_nonneg (Nat.cast_nonneg _) hCnonneg
  have hKnonneg : 0 ≤ NC * (1 + S2) := by
    refine mul_nonneg hNCnonneg ?_
    linarith
  have hBsq : Rs ≤ NC * (1 + S2) := by
    have hb : ∑ r, B r ^ 2 ≤ ∑ _r : ι, C * (1 + S2) :=
      Finset.sum_le_sum fun r _ => hdom j hj r x
    have hcard : (∑ _r : ι, C * (1 + S2)) = (Fintype.card ι : ℝ) * (C * (1 + S2)) := by
      simp [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [hcard] at hb
    have hNCalc : (Fintype.card ι : ℝ) * (C * (1 + S2)) = NC * (1 + S2) := by
      rw [hNC]
      ring
    rw [hNCalc] at hb
    exact hb
  have hCS : P ^ 2 ≤ Qs * Rs := by
    rw [hP, hQ, hR]
    exact Finset.sum_mul_sq_le_sq_mul_sq Finset.univ A B
  have hPQ : P ^ 2 ≤ Wv * (NC * (1 + S2)) := by
    nlinarith [hCS, hAsq, hBsq, hKnonneg, hWnonneg]
  have hkey : (2 * P + 2 * (x j)) ^ 2 ≤ 8 * Wv * (NC * (1 + S2)) + 8 * (x j) ^ 2 := by
    have h1 : (2 * P + 2 * (x j)) ^ 2 = 4 * P ^ 2 + 8 * P * (x j) + 4 * (x j) ^ 2 := by ring
    have hcross : 2 * P * (x j) ≤ Wv * (NC * (1 + S2)) + (x j) ^ 2 := by
      nlinarith [hPQ, sq_nonneg (P - (x j))]
    rw [h1]
    nlinarith [hPQ, hcross]
  rw [polyW_pderiv_wsSum Φ hΦ M c0 hj x, hW]
  exact hkey

set_option maxHeartbeats 2000000 in
-- the `163`-coordinate sums exceed the default elaboration budget
/-- **The structural gradient domination.**  For a potential of the shape
`W = ∑_r Φ_r² + ∑_{m∈M} x_m² + c₀` whose forms satisfy the linear-gradient bound `GradBound`,
the pointwise domination holds with `a = 16 |M| |ι| C + 8` and `b = 8 |M| |ι| C + 8`:

  `∑_{j∈M} (∂_j W)² ≤ a W² + b`.

This is the algebraic content of "the flat quartic is rescued by the coercive quadratic": the
gradient is at most linear in the differentiated coordinates, so `|∇W|² ≲ W (1 + W)`. -/
theorem pointwise_dom_of_sq_sum {ι : Type} [Fintype ι] (Φ : ι → MvPolynomial (Fin d) ℂ)
    (hΦ : ∀ r, RealCoeff (Φ r)) (M : Finset (Fin d)) {c0 C : ℝ} (hc0 : 0 ≤ c0) (hC : 0 ≤ C)
    (hdom : GradBound Φ M C) (x : Vd d) :
    ∑ j ∈ M, (polyW (pderiv j (wsSum Φ M c0)) x) ^ 2
      ≤ (16 * (M.card : ℝ) * (Fintype.card ι : ℝ) * C + 8)
          * (polyW (wsSum Φ M c0) x) ^ 2
        + (8 * (M.card : ℝ) * (Fintype.card ι : ℝ) * C + 8) := by
  set Wv : ℝ := polyW (wsSum Φ M c0) x with hW
  set S2 : ℝ := ∑ m ∈ M, (x m) ^ 2 with hS2
  set NC : ℝ := (Fintype.card ι : ℝ) * C with hNC
  set Mc : ℝ := (M.card : ℝ) with hMc
  have hS2nonneg : 0 ≤ S2 := by
    rw [hS2]
    exact Finset.sum_nonneg fun m _ => sq_nonneg _
  have hWval : Wv = (∑ r, (polyW (Φ r) x) ^ 2) + S2 + c0 := by
    rw [hW, hS2]
    exact polyW_wsSum Φ hΦ M c0 x
  have hsumSq : 0 ≤ ∑ r, (polyW (Φ r) x) ^ 2 :=
    Finset.sum_nonneg fun r _ => sq_nonneg _
  have hS2le : S2 ≤ Wv := by rw [hWval]; linarith [hsumSq]
  have hWnonneg : 0 ≤ Wv := by rw [hWval]; linarith [hsumSq, hS2nonneg]
  have hMcnonneg : 0 ≤ Mc := by
    rw [hMc]
    exact Nat.cast_nonneg _
  have hNCnonneg : 0 ≤ NC := by
    rw [hNC]
    exact mul_nonneg (Nat.cast_nonneg _) hC
  have hstep : ∑ j ∈ M, (polyW (pderiv j (wsSum Φ M c0)) x) ^ 2
      ≤ ∑ j ∈ M, (8 * Wv * (NC * (1 + S2)) + 8 * (x j) ^ 2) := by
    refine Finset.sum_le_sum fun j hj => ?_
    exact sq_pderiv_le Φ hΦ M hc0 hC hdom hj x
  have hcollapse : ∑ j ∈ M, (8 * Wv * (NC * (1 + S2)) + 8 * (x j) ^ 2)
      = Mc * (8 * Wv * (NC * (1 + S2))) + 8 * S2 := by
    rw [Finset.sum_add_distrib]
    have h1 : ∑ _j ∈ M, (8 * Wv * (NC * (1 + S2))) = Mc * (8 * Wv * (NC * (1 + S2))) := by
      rw [Finset.sum_const, hMc]
      simp [nsmul_eq_mul]
    have h2 : ∑ j ∈ M, (8 * (x j) ^ 2) = 8 * S2 := by
      rw [← Finset.mul_sum, ← hS2]
    rw [h1, h2]
  have hmain : ∑ j ∈ M, (8 * Wv * (NC * (1 + S2)) + 8 * (x j) ^ 2)
      ≤ (16 * Mc * NC + 8) * Wv ^ 2 + (8 * Mc * NC + 8) := by
    rw [hcollapse]
    have hWsq : Wv ≤ Wv ^ 2 + 1 := by nlinarith [sq_nonneg (Wv - 1 / 2)]
    have hWS : 8 * Mc * NC * Wv * S2 ≤ 8 * Mc * NC * Wv ^ 2 := by
      have hcoef : 0 ≤ 8 * Mc * NC * Wv := by
        have : 0 ≤ 8 * Mc * NC := by nlinarith [hMcnonneg, hNCnonneg]
        exact mul_nonneg this hWnonneg
      nlinarith [hS2le, hcoef]
    have hWlin : 8 * Mc * NC * Wv ≤ 8 * Mc * NC * (Wv ^ 2 + 1) := by
      have hcoef : 0 ≤ 8 * Mc * NC := by nlinarith [hMcnonneg]
      nlinarith [hWsq, hcoef]
    have hS2lin : 8 * S2 ≤ 8 * Wv := by linarith
    nlinarith [hWS, hWlin, hS2lin, hWsq]
  have hfin : ∑ j ∈ M, (8 * Wv * (NC * (1 + S2)) + 8 * (x j) ^ 2)
      ≤ (16 * (M.card : ℝ) * (Fintype.card ι : ℝ) * C + 8) * Wv ^ 2
        + (8 * (M.card : ℝ) * (Fintype.card ι : ℝ) * C + 8) := by
    have hcons : (16 * (M.card : ℝ) * (Fintype.card ι : ℝ) * C + 8)
        = 16 * Mc * NC + 8 := by
      rw [hMc, hNC]
      ring
    have hcons' : (8 * (M.card : ℝ) * (Fintype.card ι : ℝ) * C + 8)
        = 8 * Mc * NC + 8 := by
      rw [hMc, hNC]
      ring
    rw [hcons, hcons']
    exact hmain
  exact hstep.trans hfin

/-! ## 3b. The linear-form bridge

`GradBound` is a statement about the individual forms: `(∂_j Φ_r)² ≤ C (1 + ∑_m x_m²)`.  For the
Standard Model every `∂_j Φ_r` with `j ∈ smS` is a **linear form** in the momentum coordinates —
each form is bilinear, so one derivative leaves at most one field factor — and no derivative
coordinate survives that differentiation.  This section reduces `GradBound` to exactly those two
facts, so the per-form support table of §49.4 has a single algebraic target:

* `linForm` and `polyW_linForm` — the pointwise value of a linear form is `∑ b_i x_i`;
* `sq_polyW_linForm_le` — Cauchy–Schwarz, `(∑ b_i x_i)² ≤ (∑ b_i²)(1 + ∑_m x_m²)` for `L ⊆ M`;
* `gradBound_of_linear` — hence `GradBound` holds with the sum of squared coefficients, given a
  support table `L` and coefficient vectors `b` for the derivatives.

The model check `sq_polyW_linForm_le_model` instantiates the inequality on `X₁`, whose square is
`gradBound_flatPlusQuad`'s bound without the `x₀` cross term. -/

theorem realCoeff_C_const (c : ℝ) : RealCoeff (C ((c : ℝ) : ℂ) : MvPolynomial (Fin d) ℂ) := by
  change starP (C ((c : ℝ) : ℂ)) = C ((c : ℝ) : ℂ)
  rw [starP_C, Complex.conj_ofReal]

/-- The linear form `∑_{i ∈ L} b_i x_i`. -/
def linForm (b : Fin d → ℝ) (L : Finset (Fin d)) : MvPolynomial (Fin d) ℂ :=
  ∑ i ∈ L, C ((b i : ℝ) : ℂ) * X i

theorem realCoeff_linForm (b : Fin d → ℝ) (L : Finset (Fin d)) : RealCoeff (linForm b L) :=
  RealCoeff.sum fun i _ => (realCoeff_C_const (b i)).mul (realCoeff_X i)

theorem polyW_linForm (b : Fin d → ℝ) (L : Finset (Fin d)) (x : Vd d) :
    polyW (linForm b L) x = ∑ i ∈ L, b i * x i := by
  rw [linForm, polyW_sum]
  exact Finset.sum_congr rfl fun i _ => by
    rw [polyW_mul (realCoeff_C_const (b i)) (realCoeff_X i), polyW_C_eq]
    simp [polyW_X_eq]

/-- **Cauchy–Schwarz for a linear form.**  A form supported in `M` is controlled by the coercive
quadratic restricted to `M`, which is the whole content of `GradBound`. -/
theorem sq_polyW_linForm_le (b : Fin d → ℝ) (L M : Finset (Fin d)) (hLM : L ⊆ M) (x : Vd d) :
    (polyW (linForm b L) x) ^ 2 ≤ (∑ i ∈ L, (b i) ^ 2) * (1 + ∑ m ∈ M, (x m) ^ 2) := by
  have hcs : (∑ i ∈ L, b i * x i) ^ 2 ≤ (∑ i ∈ L, (b i) ^ 2) * ∑ i ∈ L, (x i) ^ 2 :=
    Finset.sum_mul_sq_le_sq_mul_sq _ _ _
  have hsub : (∑ i ∈ L, (x i) ^ 2) ≤ ∑ m ∈ M, (x m) ^ 2 :=
    Finset.sum_le_sum_of_subset_of_nonneg hLM fun i _ _ => sq_nonneg _
  have hnn : (0 : ℝ) ≤ ∑ i ∈ L, (b i) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hM : (0 : ℝ) ≤ ∑ m ∈ M, (x m) ^ 2 := Finset.sum_nonneg fun i _ => sq_nonneg _
  have hmono : (∑ i ∈ L, (b i) ^ 2) * ∑ i ∈ L, (x i) ^ 2
      ≤ (∑ i ∈ L, (b i) ^ 2) * (1 + ∑ m ∈ M, (x m) ^ 2) := by
    nlinarith [hsub, hnn, hM]
  rw [polyW_linForm]
  linarith

/-- **`GradBound` from a linear-form support table.**  Each derivative `∂_j Φ_r`, `j ∈ M`, is a
linear form supported in `M`; then the gradient bound holds with the total squared coefficient. -/
theorem gradBound_of_linear {ι : Type} [Fintype ι] (Φ : ι → MvPolynomial (Fin d) ℂ)
    (M : Finset (Fin d)) (b : Fin d → ι → Fin d → ℝ) (L : Fin d → ι → Finset (Fin d))
    (hLM : ∀ j ∈ M, ∀ r, L j r ⊆ M)
    (hrepr : ∀ j ∈ M, ∀ r, pderiv j (Φ r) = linForm (b j r) (L j r)) :
    GradBound Φ M (∑ j ∈ M, ∑ r, ∑ i ∈ L j r, (b j r i) ^ 2) := by
  intro j hj r x
  have hbound := sq_polyW_linForm_le (b j r) (L j r) M (hLM j hj r) x
  rw [← hrepr j hj r] at hbound
  have hone : (0 : ℝ) ≤ 1 + ∑ m ∈ M, (x m) ^ 2 := by
    have := Finset.sum_nonneg (f := fun m : Fin d => (x m) ^ 2) (s := M) fun i _ => sq_nonneg _
    linarith
  have hstep1 : (∑ i ∈ L j r, (b j r i) ^ 2) ≤ ∑ r', ∑ i ∈ L j r', (b j r' i) ^ 2 :=
    Finset.single_le_sum (f := fun r' => ∑ i ∈ L j r', (b j r' i) ^ 2)
      (fun r' _ => Finset.sum_nonneg fun i _ => sq_nonneg _) (Finset.mem_univ r)
  have hstep2 : ∑ r', ∑ i ∈ L j r', (b j r' i) ^ 2
      ≤ ∑ j' ∈ M, ∑ r', ∑ i ∈ L j' r', (b j' r' i) ^ 2 :=
    Finset.single_le_sum (f := fun j' => ∑ r', ∑ i ∈ L j' r', (b j' r' i) ^ 2)
      (fun j' _ => Finset.sum_nonneg fun r' _ => Finset.sum_nonneg fun i _ => sq_nonneg _) hj
  have hterm : (∑ i ∈ L j r, (b j r i) ^ 2)
      ≤ ∑ j' ∈ M, ∑ r', ∑ i ∈ L j' r', (b j' r' i) ^ 2 := hstep1.trans hstep2
  exact hbound.trans (mul_le_mul_of_nonneg_right hterm hone)

/-- The model check: `linForm (fun _ => 1) {1}` is `X₁`, and its square obeys the bound. -/
theorem linForm_unit_eq :
    (linForm (fun _ : Fin 2 => (1 : ℝ)) {1} : MvPolynomial (Fin 2) ℂ) = X 1 := by
  rw [linForm, Finset.sum_singleton]
  simp

theorem sq_polyW_linForm_le_model (x : Vd 2) :
    (polyW (linForm (fun _ : Fin 2 => (1 : ℝ)) {1}) x) ^ 2
      ≤ (1 : ℝ) * (1 + ∑ m ∈ ({0, 1} : Finset (Fin 2)), (x m) ^ 2) := by
  have h := sq_polyW_linForm_le (fun _ : Fin 2 => (1 : ℝ)) {1} ({0, 1} : Finset (Fin 2))
    (by decide) x
  simpa using h

/-! ## 3c. The identification of `smPotPoly` with `wsSum`

With the table in hand, `pointwise_dom_of_sq_sum` produces the pointwise domination of
`smPotPoly`.  That needs `smPotPoly` to *be* `wsSum` at the 49 forms and the 40 momentum
coordinates, which is the reindexing below; the `L²` transfer is
`BookProof.SmGradDomTransfer.l2_gradDom_of_pointwise` and the composition is
`BookProof.SmGradDomTransfer.exists_potSelfBound_of_gradBound`. -/

/-- The assembled potential is `wsSum` at the 49 forms and the 40 momentum coordinates. -/
theorem smPotPoly_eq_wsSum (P : SmParams) (c0 : ℝ) :
    smPotPoly P c0 = wsSum (fun r : Fin 49 => smPhi P r) smS c0 := by
  rw [wsSum, smPotPoly, smQPoly, smS,
    Finset.sum_image (fun a _ b _ hab => smCoord_injective hab)]

/-! ## 4. The model case: the flat quartic rescued by the coercive quadratic -/

/-- **The flat quartic plus the coercive quadratic**: `X₀²X₁² + X₀² + X₁²`.  §48's
`not_gradDom_flat_quartic` shows the first term alone violates the domination for every `a, b`;
this is the same quartic with the quadratic term of `smPotPoly` added. -/
def flatPlusQuad : MvPolynomial (Fin 2) ℂ := X 0 ^ 2 * X 1 ^ 2 + X 0 ^ 2 + X 1 ^ 2

/-- `flatPlusQuad` is the assembled potential of the single form `X₀X₁`. -/
theorem wsSum_unit_eq :
    wsSum (fun _ : Unit => (X 0 * X 1 : MvPolynomial (Fin 2) ℂ)) {0, 1} 0
      = flatPlusQuad := by
  rw [wsSum, flatPlusQuad, Finset.sum_pair (show (0 : Fin 2) ≠ 1 by decide)]
  simp
  ring

/-- **The gradient bound for the single flat form**: `∂_j (X₀X₁)` is a single coordinate, so its
square is at most `1 + x₀² + x₁²`. -/
theorem gradBound_flatPlusQuad :
    GradBound (fun _ : Unit => (X 0 * X 1 : MvPolynomial (Fin 2) ℂ)) {0, 1} 1 := by
  intro j hj r x
  have hmem : j = 0 ∨ j = 1 := by
    simpa using hj
  rw [Finset.sum_pair (show (0 : Fin 2) ≠ 1 by decide)]
  rcases hmem with h | h
  · subst h
    have hd : pderiv (0 : Fin 2) (X 0 * X 1 : MvPolynomial (Fin 2) ℂ) = X 1 := by
      rw [pderiv_mul, pderiv_X_self, pderiv_X_of_ne (show (1 : Fin 2) ≠ 0 by decide)]
      simp
    rw [hd]
    simp only [polyW_X_eq, one_mul]
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]
  · subst h
    have hd : pderiv (1 : Fin 2) (X 0 * X 1 : MvPolynomial (Fin 2) ℂ) = X 0 := by
      rw [pderiv_mul, pderiv_X_self, pderiv_X_of_ne (show (0 : Fin 2) ≠ 1 by decide)]
      simp
    rw [hd]
    simp only [polyW_X_eq, one_mul]
    nlinarith [sq_nonneg (x 0), sq_nonneg (x 1)]

/-- **The flat quartic plus the quadratic term satisfies the gradient domination**, with explicit
`a = 40`, `b = 24`:

  `|∂₀W|² + |∂₁W|² ≤ 40 W² + 24`,   `W = X₀²X₁² + X₀² + X₁²`.

Compare §48's `not_gradDom_flat_quartic`: the pure quartic `X₀²X₁²` admits no such constant.  The
difference is the `X₀² + X₁²`, and it is exactly the `∑_m q_m²` of `smPotPoly`. -/
theorem gradDom_flat_plus_quadratic (x : Vd 2) :
    (polyW (pderiv 0 flatPlusQuad) x) ^ 2 + (polyW (pderiv 1 flatPlusQuad) x) ^ 2
      ≤ 40 * (polyW flatPlusQuad x) ^ 2 + 24 := by
  have hgen := pointwise_dom_of_sq_sum (fun _ : Unit => (X 0 * X 1 : MvPolynomial (Fin 2) ℂ))
    (fun _ => (realCoeff_X 0).mul (realCoeff_X 1)) {0, 1} (c0 := 0) le_rfl zero_le_one
    gradBound_flatPlusQuad x
  rw [Finset.sum_pair (show (0 : Fin 2) ≠ 1 by decide)] at hgen
  rw [wsSum_unit_eq] at hgen
  norm_num at hgen
  linarith [hgen]

end

end BookProof.SmGradDomStructural
