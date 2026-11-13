import Mathlib
import BookProof.Sm.ChapterSmGradDomStructural
import BookProof.Sm.ChapterSmReverseEllipticQuartic

/-!
# The `L²` transfer of the gradient domination: from `|∇W|² ≤ a W² + b` to `GradDom`

§48/§49 of the plan reduce the reverse elliptic estimate for the Standard Model potential to two
inputs: the per-form support table (`GradBound`, in `ChapterSmGradDomStructural`) and the passage of
the resulting *pointwise* domination

  `∑_{j∈M} (∂_j W)(x)² ≤ a W(x)² + b`

to the `L²` inequality `GradDom` that `exists_potSelfBound_of_gradDom` consumes.  That step was
recorded in both modules as "routine but not formalized".  This module formalizes it, which is what
turns `PotSelfBound` into a statement about a finite pointwise computation alone.

* `eval_real_of_realCoeff`, `norm_eval_sq_eq_polyW_sq`, `eval_cpoly_mul_re` — the evaluation
  identities: on real points a real-coefficient polynomial has a real value, its squared modulus is
  the square of `polyW`, and the Gaussian weight `cpoly (q p) * (q p)` evaluates to
  `(polyW q)² ‖p‖²`.
* **`l2_gradDom_of_pointwise`** — the transfer: Gaussian-integral monotonicity `gaussInt_re_mono`
  against `norm_pgLp_sq`, with the pointwise bound multiplied by the non-negative `‖p‖²`.
* **`exists_potSelfBound_of_pointwise`** — composition with
  `BookProof.SmReverseEllipticQuartic.exists_potSelfBound_of_gradDom`: a pointwise domination for
  `smPotPoly` yields `PotSelfBound`.

So after this module the residual input for `PotSelfBound` on the Standard Model's own potential is
exactly the per-form `GradBound` table — a finite algebraic check on the 49 forms, with no analysis
left in between.

Everything here is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmGradDomTransfer

open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.QgHermiteCore BookProof.QgHermiteFriedrichs
open BookProof.DegSchrodinger BookProof.GaussCoreQuadBounds
open BookProof.SmComparisonEsa BookProof.SmOneParticle BookProof.SmHamiltonian
open BookProof.SmFarisLavine BookProof.SmReverseEllipticQuartic BookProof.SmKineticGarding
open BookProof.SmGaussWeightedIbp BookProof.SmGradDomStructural BookProof.YangMillsHermite

noncomputable section

variable {d : ℕ}

/-! ## 1. Evaluation identities at real points -/

/-- On a real point, a real-coefficient polynomial has a real value. -/
theorem eval_real_of_realCoeff {q : MvPolynomial (Fin d) ℂ} (hq : RealCoeff q) (x : Vd d) :
    MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) q = ((polyW q x : ℝ) : ℂ) := by
  have hconj : (starRingEnd ℂ) (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) q)
      = MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (cpoly q) := conj_polyEval q x
  have hfix : MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (cpoly q)
      = MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) q := by
    rw [show cpoly q = q from hq]
  have hreal : (starRingEnd ℂ) (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) q)
      = MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) q := by rw [hconj, hfix]
  simpa [polyW] using (Complex.conj_eq_iff_re.mp hreal).symm

/-- The squared modulus of a real-coefficient polynomial's value is the square of `polyW`. -/
theorem norm_eval_sq_eq_polyW_sq {q : MvPolynomial (Fin d) ℂ} (hq : RealCoeff q) (x : Vd d) :
    ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) q‖ ^ 2 = (polyW q x) ^ 2 := by
  rw [eval_real_of_realCoeff hq x, Complex.norm_real, Real.norm_eq_abs, sq_abs]

/-- The Gaussian weight of a self-product evaluates to the squared `L²` (pointwise) norm. -/
theorem eval_cpoly_self_re (p : MvPolynomial (Fin d) ℂ) (x : Vd d) :
    (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (cpoly p * p)).re
      = ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p‖ ^ 2 := by
  rw [eval_cpoly_self_eq p x, Complex.ofReal_re]

/-- The Gaussian weight of `q p` evaluates to `(polyW q)² ‖p‖²` when `q` has real coefficients. -/
theorem eval_cpoly_mul_re {q p : MvPolynomial (Fin d) ℂ} (hq : RealCoeff q) (x : Vd d) :
    (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (cpoly (q * p) * (q * p))).re
      = (polyW q x) ^ 2 * ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p‖ ^ 2 := by
  rw [eval_cpoly_self_eq (q * p) x, Complex.ofReal_re, MvPolynomial.eval_mul, norm_mul, mul_pow,
    norm_eval_sq_eq_polyW_sq hq x]

/-- A pointwise domination controls the Gaussian weight of a sum of gradient terms. -/
theorem eval_sum_cpoly_re {W p : MvPolynomial (Fin d) ℂ} (hW : RealCoeff W) (M : Finset (Fin d))
    {a b : ℝ}
    (h : ∀ x : Vd d, ∑ j ∈ M, (polyW (pderiv j W) x) ^ 2 ≤ a * (polyW W x) ^ 2 + b) (x : Vd d) :
    (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ))
        (∑ j ∈ M, cpoly (pderiv j W * p) * (pderiv j W * p))).re
      ≤ (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ))
          (C (((a : ℝ) : ℂ)) * (cpoly (W * p) * (W * p))
            + C (((b : ℝ) : ℂ)) * (cpoly p * p))).re := by
  have hL : (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ))
        (∑ j ∈ M, cpoly (pderiv j W * p) * (pderiv j W * p))).re
      = (∑ j ∈ M, (polyW (pderiv j W) x) ^ 2)
          * ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p‖ ^ 2 := by
    rw [map_sum]
    have hre : (∑ j ∈ M, (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ))
          (cpoly (pderiv j W * p) * (pderiv j W * p)))).re
        = ∑ j ∈ M, (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ))
          (cpoly (pderiv j W * p) * (pderiv j W * p))).re := by simp
    rw [hre, Finset.sum_congr rfl fun j _ => eval_cpoly_mul_re (realCoeff_pderiv' hW j) x,
      Finset.sum_mul]
  have hR : (MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ))
        (C (((a : ℝ) : ℂ)) * (cpoly (W * p) * (W * p))
          + C (((b : ℝ) : ℂ)) * (cpoly p * p))).re
      = a * ((polyW W x) ^ 2 * ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p‖ ^ 2)
        + b * ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p‖ ^ 2 := by
    have e1 : MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ))
          (C (((a : ℝ) : ℂ)) * (cpoly (W * p) * (W * p)))
        = ((a : ℝ) : ℂ) * MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ))
            (cpoly (W * p) * (W * p)) := by
      rw [map_mul, MvPolynomial.eval_C]
    have e2 : MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ))
          (C (((b : ℝ) : ℂ)) * (cpoly p * p))
        = ((b : ℝ) : ℂ) * MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) (cpoly p * p) := by
      rw [map_mul, MvPolynomial.eval_C]
    rw [map_add, e1, e2, eval_cpoly_self_eq (W * p) x, eval_cpoly_self_eq p x,
      Complex.add_re, Complex.mul_re, Complex.mul_re]
    simp only [Complex.ofReal_re, Complex.ofReal_im, zero_mul, sub_zero]
    rw [MvPolynomial.eval_mul, norm_mul, mul_pow, norm_eval_sq_eq_polyW_sq hW x]
  rw [hL, hR]
  have hnonneg : (0 : ℝ) ≤ ‖MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p‖ ^ 2 := sq_nonneg _
  nlinarith [h x, hnonneg]

/-! ## 2. The `L²` transfer -/

/-- **The pointwise-to-`L²` transfer.**  The pointwise gradient domination implies the `L²`
inequality `GradDom`, by monotonicity of the Gaussian integral: multiply the pointwise bound by
the non-negative `‖p‖²` and integrate against the Gaussian weight. -/
theorem l2_gradDom_of_pointwise {W p : MvPolynomial (Fin d) ℂ} (hW : RealCoeff W)
    (M : Finset (Fin d)) {a b : ℝ}
    (h : ∀ x : Vd d, ∑ j ∈ M, (polyW (pderiv j W) x) ^ 2 ≤ a * (polyW W x) ^ 2 + b) :
    ∑ j ∈ M, ‖pgLp (pderiv j W * p)‖ ^ 2
      ≤ a * ‖pgLp (W * p)‖ ^ 2 + b * ‖pgLp p‖ ^ 2 := by
  have hmono := gaussInt_re_mono (s := C (((a : ℝ) : ℂ)) * (cpoly (W * p) * (W * p))
      + C (((b : ℝ) : ℂ)) * (cpoly p * p))
    (eval_sum_cpoly_re hW M h)
  have hL : ∑ j ∈ M, ‖pgLp (pderiv j W * p)‖ ^ 2
      = (gaussInt (∑ j ∈ M, cpoly (pderiv j W * p) * (pderiv j W * p))).re := by
    rw [gaussInt_sum]
    have hre : (∑ j ∈ M, gaussInt (cpoly (pderiv j W * p) * (pderiv j W * p))).re
        = ∑ j ∈ M, (gaussInt (cpoly (pderiv j W * p) * (pderiv j W * p))).re := by simp
    rw [hre]
    exact Finset.sum_congr rfl fun j _ => norm_pgLp_sq (pderiv j W * p)
  have hR : (gaussInt (C (((a : ℝ) : ℂ)) * (cpoly (W * p) * (W * p))
        + C (((b : ℝ) : ℂ)) * (cpoly p * p))).re
      = a * ‖pgLp (W * p)‖ ^ 2 + b * ‖pgLp p‖ ^ 2 := by
    rw [gaussInt_add, ← smul_eq_C_mul, ← smul_eq_C_mul, gaussInt_smul, gaussInt_smul,
      Complex.add_re, Complex.mul_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_re,
      Complex.ofReal_im, Complex.ofReal_im, zero_mul, sub_zero, zero_mul, sub_zero,
      ← norm_pgLp_sq, ← norm_pgLp_sq]
  rw [← hL, hR] at hmono
  exact hmono

/-! ## 3. `PotSelfBound` from the pointwise domination -/

/-- **`PotSelfBound` follows from the pointwise domination of the Standard Model potential.**  The
only hypothesis on `W = smPotPoly P c0` is the pointwise bound, which is what `GradBound` supplies
via `pointwise_dom_of_sq_sum`. -/
theorem exists_potSelfBound_of_pointwise (P : SmParams) {c0 a b : ℝ} (hc0 : 0 ≤ c0) (hb : 0 ≤ b)
    (h : ∀ x : Vd 163, ∑ j ∈ smS, (polyW (pderiv j (smPotPoly P c0)) x) ^ 2
      ≤ a * (polyW (smPotPoly P c0) x) ^ 2 + b) :
    ∃ β, PotSelfBound P c0 β :=
  exists_potSelfBound_of_gradDom P (c0 := c0) (a := a) (b := b) hc0 hb fun p =>
    l2_gradDom_of_pointwise (W := smPotPoly P c0) (p := p) (realCoeff_smPotPoly P c0) smS h

/-! ## 4. `PotSelfBound` from the per-form `GradBound` table alone -/

/-- **`PotSelfBound` follows from `GradBound`.**  The pointwise domination of `smPotPoly` is
`pointwise_dom_of_sq_sum` (with `smPotPoly_eq_wsSum` supplying the identification with `wsSum`), and
the pointwise-to-`L²` transfer above closes the rest — so the per-form support table for the 49
forms is the *only* remaining input for `PotSelfBound`, with no analysis left in between. -/
theorem exists_potSelfBound_of_gradBound (P : SmParams) {c0 C : ℝ} (hc0 : 0 ≤ c0) (hC : 0 ≤ C)
    (hdom : GradBound (fun r : Fin 49 => smPhi P r) smS C) :
    ∃ β, PotSelfBound P c0 β :=
  exists_potSelfBound_of_pointwise P (c0 := c0)
    (a := 16 * (smS.card : ℝ) * (Fintype.card (Fin 49) : ℝ) * C + 8)
    (b := 8 * (smS.card : ℝ) * (Fintype.card (Fin 49) : ℝ) * C + 8) hc0 (by positivity)
    (fun x => by
      have h := pointwise_dom_of_sq_sum (fun r : Fin 49 => smPhi P r)
        (fun r => realCoeff_smPhi P r) smS hc0 hC hdom x
      rwa [← smPotPoly_eq_wsSum P c0] at h)

end

end BookProof.SmGradDomTransfer
