import Mathlib
import BookProof.Toolbox.PhysHSGaussian

/-!
# Chapter MehlerEigenfunction — the pCN step is diagonalised by the Hermite functions

Plan: `pcnl.md`, Module 1.  §1.A of the plan says that the unadjusted pCN step

`v = ρ u + √(1 − ρ²) ξ`

commutes with the orthogonal group at finite dimension, so Schur's lemma makes the
hyperspherical harmonics (Gegenbauer polynomials) its eigenfunctions with eigenvalue `ρⁿ`, and
§1.B says that in the `d → ∞` limit the same statement becomes the statement that the
**Fock number states** (Hermite functions) are eigenfunctions with eigenvalue `ρⁿ`.  The
status note of `pcnl.md` records that the eigenfunction identity itself was missing from the
corpus, in either form: it needs the Gegenbauer addition theorem, or its `α → ∞` Gaussian
form,

`∫ Hₙ(ρ x + √(1 − ρ²) y) γ(dy) = ρⁿ Hₙ(x)`.

This module proves the Gaussian form — the limit the plan actually uses, since it is the one
whose eigenfunctions are `PhysHSGaussian.physHermite`, the basis of the Fock/number-state
model `BookProof.MCMC.UnadjustedPCNGap`.  So Module 1 of `pcnl.md` is closed in the infinite
dimensional form: the Mehler operator `T_ρ`, which is exactly one pCN step of §1, has the
Hermite functions as eigenfunctions with the eigenvalue `ρⁿ` of §1.A.

## Contents

* `mehlerCoupling ρ = √(1 − ρ²)`, `mehlerArg ρ x y = ρ x + √(1 − ρ²) y` — the pCN argument,
  with `mehlerCoupling_sq`: `ρ² + (√(1 − ρ²))² = 1`, the norm-preservation of the step;
* `integral_exp_neg_sq` — the normalising Gaussian integral `∫ e^{−y²} = √π` (from
  `Real.integral_gaussian`), so the density below is the standard one in the physicists'
  Hermite normalisation;
* `exists_physHermite_abs_bound` — the growth bound `|Hₙ z| ≤ C (1 + |z|)ⁿ`, by induction on
  the three-term recurrence;
* `integrable_pow_mehler` — `y ↦ yᵏ Hₙ(ρx + √(1 − ρ²)y) e^{−y²}` is integrable: the
  hypothesis the integration by parts needs;
* `hasDerivAt_mehlerHermite`, `hasDerivAt_gauss` — the two derivatives;
* **`stein_mehler`** — the Stein/Mehler recursion
  `∫ y Hₙ(ρx + √(1 − ρ²)y) e^{−y²} = √(1 − ρ²) · n · ∫ Hₙ₋₁(ρx + √(1 − ρ²)y) e^{−y²}`,
  i.e. the transverse Gaussian moment of `Hₙ ∘ mehlerArg` is the lower Hermite polynomial —
  the conjugation that makes the recurrence close;
* **`mehler_hermite`** — **the eigenfunction identity**:
  `∫ Hₙ(ρx + √(1 − ρ²)y) e^{−y²} dy = √π · ρⁿ · Hₙ(x)` for `ρ² ≤ 1`, by two-step induction
  on `n` using `physHermite_succ_succ` and `stein_mehler`;
* `mehlerOp`, **`mehlerOp_physHermite`** — the same statement as the operator identity
  `T_ρ Hₙ = ρⁿ • Hₙ` for the normalised Mehler operator
  `T_ρ f x = π^{−1/2} ∫ f(ρx + √(1 − ρ²)y) e^{−y²} dy`, which is one pCN step in the `d → ∞` limit;
* `mehler_gap` — consequently `1 − ρ` separates the vacuum eigenvalue `1` from every excited
  number state's `ρⁿ`, the `d → ∞` counterpart of §1.A's `gap(P₀^{(d)}) = 1 − √(1 − β²)`.

## Relation to the finite-`d` side and to `UnadjustedPCNGap`

`gegenbauerScaled_tendsto_hermite` (`PhysHSGaussian`) is §1.B's polynomial convergence, and
`pcn_gap_uniform` (`BookProof.MCMC.UnadjustedPCN`) is the `d`-independence of the eigenvalue
`λₙ = ρⁿ`.  With this module the two halves meet: the eigenvalue is `ρⁿ` at every `d` and the
eigenfunction converges to `Hₙ`, so the diagonal matrix element `⟨n|P₀^{(d)}|n⟩` of Module 2 is
`ρⁿ` for every `d` and in the limit.  What is not formalised anywhere is the finite-`d`
identity `P₀^{(d)} Cₙ^{(α/2)} = ρⁿ Cₙ^{(α/2)}` itself (the Gegenbauer addition theorem): that
needs the spherical measure and the addition formula, neither of which is in the corpus.
-/

noncomputable section

namespace BookProof.MCMC

open PhysHSGaussian MeasureTheory
open scoped BigOperators Real

/-! ## 1. The pCN argument -/

/-- The Mehler coupling `√(1 − ρ²)` — the transverse weight of one pCN step. -/
def mehlerCoupling (ρ : ℝ) : ℝ := Real.sqrt (1 - ρ ^ 2)

/-- The pCN/Mehler argument `ρ x + √(1 − ρ²) y`. -/
def mehlerArg (ρ x y : ℝ) : ℝ := ρ * x + mehlerCoupling ρ * y

theorem mehlerCoupling_nonneg (ρ : ℝ) : 0 ≤ mehlerCoupling ρ := Real.sqrt_nonneg _

/-- **The step preserves the norm**: `ρ² + (√(1 − ρ²))² = 1` for `|ρ| ≤ 1`. -/
theorem mehlerCoupling_sq {ρ : ℝ} (hρ : ρ ^ 2 ≤ 1) : mehlerCoupling ρ ^ 2 = 1 - ρ ^ 2 :=
  Real.sq_sqrt (by linarith)

theorem mehlerArg_eq (ρ x y : ℝ) : mehlerArg ρ x y = ρ * x + mehlerCoupling ρ * y := rfl

/-! ## 2. The normalising integral -/

theorem integral_exp_neg_sq : ∫ y : ℝ, Real.exp (-(y ^ 2)) = Real.sqrt Real.pi := by
  have h := integral_gaussian (1 : ℝ)
  rw [div_one] at h
  simpa using h

/-! ## 3. Growth of the physicists' Hermite polynomials -/

/-- **A polynomial growth bound for `physHermite`**: `|Hₙ z| ≤ C (1 + |z|)ⁿ`.  This is what
makes every Gaussian moment of a Hermite polynomial finite. -/
theorem exists_physHermite_abs_bound (n : ℕ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : ℝ, |physHermite n z| ≤ C * (1 + |z|) ^ n := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    match n, ih with
    | 0, _ => exact ⟨1, zero_le_one, fun z => by simp⟩
    | 1, _ =>
        refine ⟨2, by norm_num, fun z => ?_⟩
        have hz : (0 : ℝ) ≤ |z| := abs_nonneg z
        calc |physHermite 1 z| = 2 * |z| := by
              rw [physHermite_one, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2)]
            _ ≤ 2 * (1 + |z|) ^ 1 := by rw [pow_one]; nlinarith
    | (m + 2), ih =>
        obtain ⟨C₁, hC₁, h₁⟩ := ih (m + 1) (by omega)
        obtain ⟨C₀, hC₀, h₀⟩ := ih m (by omega)
        refine ⟨2 * C₁ + 2 * ((m : ℝ) + 1) * C₀ + 1, by positivity, fun z => ?_⟩
        have hz : (0 : ℝ) ≤ |z| := abs_nonneg z
        have hbase : (1 : ℝ) ≤ 1 + |z| := by linarith
        set t : ℝ := 1 + |z| with ht
        have ht1 : (1 : ℝ) ≤ t := hbase
        have hzt : |z| ≤ t := by rw [ht]; linarith
        have htpos : (0 : ℝ) ≤ t := by linarith
        have hp1 : (0 : ℝ) ≤ t ^ (m + 1) := pow_nonneg htpos _
        have hpm : (0 : ℝ) ≤ t ^ m := pow_nonneg htpos _
        have h02 : t ^ (m + 2) = t * t ^ (m + 1) := pow_succ' t (m + 1)
        have h01 : t ^ (m + 2) = t ^ m * t ^ 2 := by rw [← pow_add]
        -- the two terms of the recurrence
        have hterm₁ : |2 * z * physHermite (m + 1) z| ≤ 2 * C₁ * t ^ (m + 2) := by
          have h1' := h₁ z
          have habs : |2 * z * physHermite (m + 1) z| = 2 * (|z| * |physHermite (m + 1) z|) := by
            rw [show (2 : ℝ) * z * physHermite (m + 1) z
                = 2 * (z * physHermite (m + 1) z) from by ring,
              abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 2), abs_mul]
          rw [habs]
          have h2 : |z| * |physHermite (m + 1) z| ≤ t * (C₁ * t ^ (m + 1)) := by
            refine mul_le_mul hzt ?_ (abs_nonneg _) htpos
            exact h1'
          have h3 : t * (C₁ * t ^ (m + 1)) = C₁ * t ^ (m + 2) := by
            rw [h02]; ring
          calc 2 * (|z| * |physHermite (m + 1) z|)
              ≤ 2 * (t * (C₁ * t ^ (m + 1))) := by linarith
            _ = 2 * C₁ * t ^ (m + 2) := by rw [h3]; ring
        have hterm₀ : |2 * ((m : ℝ) + 1) * physHermite m z|
            ≤ 2 * ((m : ℝ) + 1) * C₀ * t ^ (m + 2) := by
          have h0' := h₀ z
          have hcoef : (0 : ℝ) ≤ 2 * ((m : ℝ) + 1) := by positivity
          have habs : |2 * ((m : ℝ) + 1) * physHermite m z|
              = 2 * ((m : ℝ) + 1) * |physHermite m z| := by
            rw [abs_mul, abs_of_nonneg hcoef]
          rw [habs]
          have h2 : |physHermite m z| ≤ C₀ * t ^ (m + 2) := by
            refine h0'.trans ?_
            exact mul_le_mul_of_nonneg_left (pow_le_pow_right₀ ht1 (by omega)) hC₀
          nlinarith [hcoef, h2, hpm, pow_nonneg htpos (m + 2)]
        have hrec := physHermite_succ_succ m z
        calc |physHermite (m + 2) z|
            = |2 * z * physHermite (m + 1) z - 2 * ((m : ℝ) + 1) * physHermite m z| := by
              rw [hrec]
            _ ≤ |2 * z * physHermite (m + 1) z| + |2 * ((m : ℝ) + 1) * physHermite m z| := by
              simpa using abs_add_le (2 * z * physHermite (m + 1) z)
                (-(2 * ((m : ℝ) + 1) * physHermite m z))
            _ ≤ 2 * C₁ * t ^ (m + 2) + 2 * ((m : ℝ) + 1) * C₀ * t ^ (m + 2) := by
              linarith
            _ ≤ (2 * C₁ + 2 * ((m : ℝ) + 1) * C₀ + 1) * (1 + |z|) ^ (m + 2) := by
              rw [← ht]
              nlinarith [pow_nonneg htpos (m + 2)]

/-! ## 4. Integrability of the Mehler moments -/

theorem integrable_one_add_abs_pow_exp_neg_sq (k : ℕ) :
    Integrable (fun y : ℝ => (1 + |y|) ^ k * Real.exp (-(y ^ 2))) := by
  have h : ∀ y : ℝ, (1 + |y|) ^ k * Real.exp (-(y ^ 2)) =
      ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * (|y| ^ j * Real.exp (-(y ^ 2))) := by
    intro y
    rw [add_comm (1 : ℝ), add_pow, Finset.sum_mul]
    exact Finset.sum_congr rfl fun j _ => by rw [one_pow, mul_one]; ring
  simp_rw [h]
  refine integrable_finset_sum _ fun j _ => ?_
  refine Integrable.const_mul ?_ _
  have hj : (-1 : ℝ) < (j : ℝ) := by
    have : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    linarith
  have hb : (0 : ℝ) < 1 := one_pos
  have := (integrable_rpow_mul_exp_neg_mul_sq (b := 1) hb (s := (j : ℝ)) hj).norm
  refine this.congr (Filter.Eventually.of_forall fun y => ?_)
  simp [Real.norm_eq_abs, Real.rpow_natCast, abs_of_pos (Real.exp_pos _)]

/-- **Every shifted Hermite moment against the Gaussian is integrable.**  The factor `y ^ k`
is what the integration by parts below produces. -/
theorem integrable_pow_mehler (n k : ℕ) (ρ x : ℝ) :
    Integrable (fun y : ℝ => y ^ k * physHermite n (mehlerArg ρ x y) * Real.exp (-(y ^ 2))) := by
  obtain ⟨C, hC, hb⟩ := exists_physHermite_abs_bound n
  set A : ℝ := |ρ| * |x|
  set B : ℝ := |mehlerCoupling ρ|
  have hAn : (0 : ℝ) ≤ A := mul_nonneg (abs_nonneg _) (abs_nonneg _)
  have hBn : (0 : ℝ) ≤ B := abs_nonneg _
  set D : ℝ := C * (1 + A + B) ^ n with hD
  have hDn : (0 : ℝ) ≤ D := by
    rw [hD]
    have : (0 : ℝ) ≤ (1 + A + B) ^ n := pow_nonneg (by linarith) n
    positivity
  refine (integrable_one_add_abs_pow_exp_neg_sq (n + k)).const_mul D |>.mono'
    ?_ ?_
  · have h1 : Continuous fun y : ℝ => mehlerArg ρ x y := by
      simp only [mehlerArg_eq]
      exact continuous_const.add (continuous_const.mul continuous_id)
    have hexpc : Continuous fun y : ℝ => Real.exp (-(y ^ 2)) := by fun_prop
    have hmehl : Continuous fun y : ℝ => physHermite n (mehlerArg ρ x y) :=
      (physHermite_continuous n).comp h1
    have hprod : Continuous fun y : ℝ =>
        y ^ k * physHermite n (mehlerArg ρ x y) * Real.exp (-(y ^ 2)) := by
      simpa [mul_assoc] using (continuous_id.pow k).mul (hmehl.mul hexpc)
    exact hprod.aestronglyMeasurable
  · refine Filter.Eventually.of_forall fun y => ?_
    have hy : (0 : ℝ) ≤ |y| := abs_nonneg y
    have hbase : (1 : ℝ) ≤ 1 + |y| := by linarith
    -- the argument bound `1 + |z| ≤ (1 + A + B) (1 + |y|)`
    have hz : 1 + |mehlerArg ρ x y| ≤ (1 + A + B) * (1 + |y|) := by
      have h1 : |mehlerArg ρ x y| ≤ A + B * |y| := by
        rw [mehlerArg_eq]
        calc |ρ * x + mehlerCoupling ρ * y| ≤ |ρ * x| + |mehlerCoupling ρ * y| := abs_add_le _ _
          _ = |ρ| * |x| + |mehlerCoupling ρ| * |y| := by rw [abs_mul, abs_mul]
      have h4 : 1 + A + B * |y| ≤ (1 + A + B) * (1 + |y|) := by
        nlinarith [hBn, hAn, hy, mul_nonneg hAn hy, mul_nonneg hBn hy,
          mul_pos (by norm_num : (0 : ℝ) < 1) (by linarith : (0 : ℝ) < 1 + |y|)]
      linarith
    have hHerm : |physHermite n (mehlerArg ρ x y)| ≤ C * ((1 + A + B) ^ n * (1 + |y|) ^ n) := by
      have h := hb (mehlerArg ρ x y)
      have hpow : (1 + |mehlerArg ρ x y|) ^ n ≤ ((1 + A + B) * (1 + |y|)) ^ n := by
        exact pow_le_pow_left₀ (by positivity) hz n
      rw [mul_pow] at hpow
      exact h.trans (by nlinarith [hC, hpow])
    -- assemble
    rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_pow, abs_of_pos (Real.exp_pos _)]
    have hexp : (0 : ℝ) ≤ Real.exp (-(y ^ 2)) := (Real.exp_pos _).le
    have hyk : |y| ^ k ≤ (1 + |y|) ^ k := pow_le_pow_left₀ hy (by linarith) k
    have hgoal : |y| ^ k * |physHermite n (mehlerArg ρ x y)|
        ≤ D * ((1 + |y|) ^ k * (1 + |y|) ^ n) := by
      have h1 : |y| ^ k * |physHermite n (mehlerArg ρ x y)| ≤
          |y| ^ k * (C * ((1 + A + B) ^ n * (1 + |y|) ^ n)) :=
        mul_le_mul_of_nonneg_left hHerm (pow_nonneg hy k)
      have h2 : |y| ^ k * (C * ((1 + A + B) ^ n * (1 + |y|) ^ n)) ≤
          (1 + |y|) ^ k * (C * ((1 + A + B) ^ n * (1 + |y|) ^ n)) := by
        refine mul_le_mul_of_nonneg_right hyk ?_
        have hAA : (0 : ℝ) ≤ (1 + A + B) ^ n := pow_nonneg (by linarith) n
        have hy2 : (0 : ℝ) ≤ (1 + |y|) ^ n := pow_nonneg (by linarith) n
        positivity
      refine (h1.trans h2).trans (le_of_eq ?_)
      rw [hD]
      ring
    have hfin : |y| ^ k * |physHermite n (mehlerArg ρ x y)| * Real.exp (-(y ^ 2)) ≤
        D * ((1 + |y|) ^ k * (1 + |y|) ^ n * Real.exp (-(y ^ 2))) := by
      nlinarith [hgoal, hexp]
    simpa [pow_add, mul_comm, mul_left_comm, mul_assoc] using hfin

/-! ## 5. The Stein recursion for the shifted Hermite polynomial -/

theorem integrable_mehler (n : ℕ) (ρ x : ℝ) :
    Integrable (fun y : ℝ => physHermite n (mehlerArg ρ x y) * Real.exp (-(y ^ 2))) := by
  have := integrable_pow_mehler n 0 ρ x
  simpa using this

theorem integrable_mehler_y (n : ℕ) (ρ x : ℝ) :
    Integrable (fun y : ℝ => y * physHermite n (mehlerArg ρ x y) * Real.exp (-(y ^ 2))) := by
  have := integrable_pow_mehler n 1 ρ x
  simpa using this

theorem integrable_exp_neg_sq : Integrable (fun y : ℝ => Real.exp (-(y ^ 2))) := by
  have := integrable_one_add_abs_pow_exp_neg_sq 0
  simpa using this

theorem integrable_y_exp_neg_sq : Integrable (fun y : ℝ => y * Real.exp (-(y ^ 2))) := by
  have h : Integrable (fun y : ℝ => ‖y ^ (1 : ℝ) * Real.exp (-1 * y ^ 2)‖) :=
    (integrable_rpow_mul_exp_neg_mul_sq (b := 1) (by norm_num) (s := (1 : ℝ))
      (by norm_num)).norm
  refine Integrable.mono' h ?_ (Filter.Eventually.of_forall fun y => ?_)
  · have : Continuous fun y : ℝ => y * Real.exp (-(y ^ 2)) := by fun_prop
    exact this.aestronglyMeasurable
  · simp [Real.rpow_one]

/-- The derivative of the pCN argument in its transverse variable,
`d/dt (ρx + √(1−ρ²)t) = √(1−ρ²)`. -/
theorem hasDerivAt_mehlerArg (ρ x y : ℝ) :
    HasDerivAt (fun t : ℝ => mehlerArg ρ x t) (mehlerCoupling ρ) y := by
  have h : HasDerivAt (fun t : ℝ => mehlerCoupling ρ * t) (mehlerCoupling ρ) y := by
    simpa [mul_comm] using (hasDerivAt_id y).const_mul (mehlerCoupling ρ)
  have h2 := h.const_add (ρ * x)
  simpa [mehlerArg_eq, add_comm] using h2

/-- The derivative of `y ↦ Hₙ(ρx + √(1−ρ²)y)`. -/
theorem hasDerivAt_mehlerHermite (n : ℕ) (ρ x y : ℝ) :
    HasDerivAt (fun t : ℝ => physHermite n (mehlerArg ρ x t))
      (mehlerCoupling ρ * (2 * n * physHermite (n - 1) (mehlerArg ρ x y))) y := by
  have h := (physHermite_hasDerivAt_aux n (mehlerArg ρ x y)).comp y (hasDerivAt_mehlerArg ρ x y)
  simpa [mul_comm, mul_left_comm, mul_assoc] using h

/-- The derivative of the Gaussian weight. -/
theorem hasDerivAt_exp_neg_sq (y : ℝ) :
    HasDerivAt (fun t : ℝ => Real.exp (-(t ^ 2))) (-2 * y * Real.exp (-(y ^ 2))) y := by
  have h : HasDerivAt (fun t : ℝ => -(t ^ 2)) (-(2 * y)) y := by
    have h2 := (hasDerivAt_pow 2 y).neg
    simpa using h2
  have h2 := h.exp
  simpa [mul_comm, mul_left_comm, mul_assoc] using h2

/-- **The Stein/Mehler recursion.**  The transverse Gaussian moment of `Hₙ ∘ mehlerArg` is the
lower Hermite polynomial, with the coupling `√(1 − ρ²)` and the index `n`: this is the identity
that makes the three-term recurrence of `physHermite` close under the Mehler average. -/
theorem stein_mehler (n : ℕ) (ρ x : ℝ) :
    ∫ y : ℝ, y * physHermite n (mehlerArg ρ x y) * Real.exp (-(y ^ 2))
      = mehlerCoupling ρ * n *
          ∫ y : ℝ, physHermite (n - 1) (mehlerArg ρ x y) * Real.exp (-(y ^ 2)) := by
  have hf : ∀ y : ℝ, HasLineDerivAt ℝ (fun t : ℝ => physHermite n (mehlerArg ρ x t))
      (mehlerCoupling ρ * (2 * n * physHermite (n - 1) (mehlerArg ρ x y))) y 1 := by
    intro y
    have hd := hasDerivAt_mehlerHermite n ρ x y
    have hF : HasFDerivAt (fun t : ℝ => physHermite n (mehlerArg ρ x t))
        ((1 : ℝ →L[ℝ] ℝ).smulRight
          (mehlerCoupling ρ * (2 * n * physHermite (n - 1) (mehlerArg ρ x y)))) y :=
      hasFDerivAt_iff_hasDerivAt.mpr (by simpa using hd)
    simpa using hF.hasLineDerivAt 1
  have hg : ∀ y : ℝ, HasLineDerivAt ℝ (fun t : ℝ => Real.exp (-(t ^ 2)))
      (-2 * y * Real.exp (-(y ^ 2))) y 1 := by
    intro y
    have hd := hasDerivAt_exp_neg_sq y
    have hF : HasFDerivAt (fun t : ℝ => Real.exp (-(t ^ 2)))
        ((1 : ℝ →L[ℝ] ℝ).smulRight (-2 * y * Real.exp (-(y ^ 2)))) y :=
      hasFDerivAt_iff_hasDerivAt.mpr (by simpa using hd)
    simpa using hF.hasLineDerivAt 1
  have hibp := integral_bilinear_hasLineDerivAt_right_eq_neg_left_of_integrable
    (μ := (volume : Measure ℝ)) (B := ContinuousLinearMap.mul ℝ ℝ)
    (f := fun t : ℝ => physHermite n (mehlerArg ρ x t))
    (f' := fun y : ℝ => mehlerCoupling ρ * (2 * n * physHermite (n - 1) (mehlerArg ρ x y)))
    (g := fun t : ℝ => Real.exp (-(t ^ 2)))
    (g' := fun y : ℝ => -2 * y * Real.exp (-(y ^ 2)))
    (v := (1 : ℝ)) ?_ ?_ ?_ hf hg
  · simp only [ContinuousLinearMap.mul_apply'] at hibp
    have hL : ∫ y : ℝ, physHermite n (mehlerArg ρ x y) * (-2 * y * Real.exp (-(y ^ 2)))
        = -2 * ∫ y : ℝ, y * physHermite n (mehlerArg ρ x y) * Real.exp (-(y ^ 2)) := by
      have hfun : (fun y : ℝ => physHermite n (mehlerArg ρ x y) * (-2 * y * Real.exp (-(y ^ 2))))
          = fun y : ℝ => -2 * (y * physHermite n (mehlerArg ρ x y) * Real.exp (-(y ^ 2))) := by
        funext y; ring
      rw [hfun, integral_const_mul]
    have hR : ∫ y : ℝ,
        (mehlerCoupling ρ * (2 * n * physHermite (n - 1) (mehlerArg ρ x y))) *
          Real.exp (-(y ^ 2))
        = mehlerCoupling ρ * (2 * n) *
            ∫ y : ℝ, physHermite (n - 1) (mehlerArg ρ x y) * Real.exp (-(y ^ 2)) := by
      have hfun : (fun y : ℝ =>
            (mehlerCoupling ρ * (2 * n * physHermite (n - 1) (mehlerArg ρ x y))) *
              Real.exp (-(y ^ 2)))
          = fun y : ℝ => (mehlerCoupling ρ * (2 * n)) *
              (physHermite (n - 1) (mehlerArg ρ x y) * Real.exp (-(y ^ 2))) := by
        funext y; ring
      rw [hfun, integral_const_mul]
    rw [hL, hR] at hibp
    linarith [hibp]
  · -- integrability of `f' * g`
    have := (integrable_mehler (n - 1) ρ x).const_mul (mehlerCoupling ρ * (2 * (n : ℝ)))
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [ContinuousLinearMap.mul_apply']
    ring
  · -- integrability of `f * g'`
    have := (integrable_mehler_y n ρ x).const_mul (-2 : ℝ)
    refine this.congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [ContinuousLinearMap.mul_apply']
    ring
  · -- integrability of `f * g`
    simpa only [ContinuousLinearMap.mul_apply'] using integrable_mehler n ρ x

/-! ## 6. The eigenfunction identity -/

/-- **The Mehler eigenfunction identity**: the Hermite polynomials are eigenfunctions of one pCN
step, with eigenvalue `ρⁿ`.

`∫ Hₙ(ρ x + √(1 − ρ²) y) e^{−y²} dy = √π · ρⁿ · Hₙ(x)` for `ρ² ≤ 1`.  This is the `α → ∞`
(Gaussian/Fock) form of `P₀^{(d)} Cₙ^{(α/2)} = ρⁿ Cₙ^{(α/2)}` that `pcnl.md` Module 1 asks for,
proved by two-step induction on the Hermite recurrence with `stein_mehler` supplying the
transverse moment. -/
theorem mehler_hermite (n : ℕ) {ρ : ℝ} (hρ : ρ ^ 2 ≤ 1) (x : ℝ) :
    ∫ y : ℝ, physHermite n (mehlerArg ρ x y) * Real.exp (-(y ^ 2))
      = Real.sqrt Real.pi * ρ ^ n * physHermite n x := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
    rcases n with _ | _ | m
    · simp [integral_exp_neg_sq]
    · -- `n = 1`: the linear case; the odd Gaussian moment vanishes
      have hodd : ∫ y : ℝ, y * Real.exp (-(y ^ 2)) = 0 := by
        have h := stein_mehler 0 ρ x
        simpa using h
      have hI0 : Integrable fun y : ℝ => Real.exp (-(y ^ 2)) := integrable_exp_neg_sq
      have hI1 : Integrable fun y : ℝ => y * Real.exp (-(y ^ 2)) := integrable_y_exp_neg_sq
      have hsplit : (fun y : ℝ => physHermite 1 (mehlerArg ρ x y) * Real.exp (-(y ^ 2)))
          = fun y : ℝ => 2 * ρ * x * Real.exp (-(y ^ 2)) +
              2 * mehlerCoupling ρ * (y * Real.exp (-(y ^ 2))) := by
        funext y
        rw [physHermite_one, mehlerArg_eq]
        ring
      calc ∫ y : ℝ, physHermite 1 (mehlerArg ρ x y) * Real.exp (-(y ^ 2))
          = ∫ y : ℝ, (2 * ρ * x * Real.exp (-(y ^ 2)) +
              2 * mehlerCoupling ρ * (y * Real.exp (-(y ^ 2)))) := by rw [hsplit]
        _ = (∫ y : ℝ, 2 * ρ * x * Real.exp (-(y ^ 2))) +
              ∫ y : ℝ, 2 * mehlerCoupling ρ * (y * Real.exp (-(y ^ 2))) :=
            integral_add (hI0.const_mul _) (hI1.const_mul _)
        _ = 2 * ρ * x * Real.sqrt Real.pi + 2 * mehlerCoupling ρ * 0 := by
            rw [integral_const_mul, integral_const_mul, integral_exp_neg_sq, hodd]
        _ = Real.sqrt Real.pi * ρ ^ 1 * physHermite 1 x := by
            rw [physHermite_one]; ring
    · -- `n = m + 2`: the three-term recurrence
      have hIH1 := ih (m + 1) (by omega)
      have hIH0 := ih m (by omega)
      have hStein : ∫ y : ℝ, y * physHermite (m + 1) (mehlerArg ρ x y) * Real.exp (-(y ^ 2))
          = mehlerCoupling ρ * (m + 1) *
              ∫ y : ℝ, physHermite m (mehlerArg ρ x y) * Real.exp (-(y ^ 2)) := by
        simpa using stein_mehler (m + 1) ρ x
      have hI1 : Integrable fun y : ℝ =>
          physHermite (m + 1) (mehlerArg ρ x y) * Real.exp (-(y ^ 2)) := integrable_mehler _ _ _
      have hI0 : Integrable fun y : ℝ =>
          physHermite m (mehlerArg ρ x y) * Real.exp (-(y ^ 2)) := integrable_mehler _ _ _
      have hIy1 : Integrable fun y : ℝ =>
          y * physHermite (m + 1) (mehlerArg ρ x y) * Real.exp (-(y ^ 2)) :=
        integrable_mehler_y _ _ _
      have hsplit : (fun y : ℝ => physHermite (m + 2) (mehlerArg ρ x y) * Real.exp (-(y ^ 2)))
          = fun y : ℝ =>
              2 * ρ * x * (physHermite (m + 1) (mehlerArg ρ x y) * Real.exp (-(y ^ 2))) +
              2 * mehlerCoupling ρ *
                (y * physHermite (m + 1) (mehlerArg ρ x y) * Real.exp (-(y ^ 2))) -
              2 * ((m : ℝ) + 1) * (physHermite m (mehlerArg ρ x y) * Real.exp (-(y ^ 2))) := by
        funext y
        rw [physHermite_succ_succ, mehlerArg_eq]
        ring
      calc ∫ y : ℝ, physHermite (m + 2) (mehlerArg ρ x y) * Real.exp (-(y ^ 2))
          = ∫ y : ℝ,
              2 * ρ * x * (physHermite (m + 1) (mehlerArg ρ x y) * Real.exp (-(y ^ 2))) +
              2 * mehlerCoupling ρ *
                (y * physHermite (m + 1) (mehlerArg ρ x y) * Real.exp (-(y ^ 2))) -
              2 * ((m : ℝ) + 1) * (physHermite m (mehlerArg ρ x y) * Real.exp (-(y ^ 2))) := by
            rw [hsplit]
        _ = (∫ y : ℝ,
                2 * ρ * x * (physHermite (m + 1) (mehlerArg ρ x y) * Real.exp (-(y ^ 2))) +
                2 * mehlerCoupling ρ *
                  (y * physHermite (m + 1) (mehlerArg ρ x y) * Real.exp (-(y ^ 2)))) -
              ∫ y : ℝ, 2 * ((m : ℝ) + 1) *
                (physHermite m (mehlerArg ρ x y) * Real.exp (-(y ^ 2))) :=
            integral_sub ((hI1.const_mul _).add (hIy1.const_mul _)) (hI0.const_mul _)
        _ = ((∫ y : ℝ,
                2 * ρ * x * (physHermite (m + 1) (mehlerArg ρ x y) * Real.exp (-(y ^ 2)))) +
              ∫ y : ℝ, 2 * mehlerCoupling ρ *
                (y * physHermite (m + 1) (mehlerArg ρ x y) * Real.exp (-(y ^ 2)))) -
              ∫ y : ℝ, 2 * ((m : ℝ) + 1) *
                (physHermite m (mehlerArg ρ x y) * Real.exp (-(y ^ 2))) :=
            congrArg (fun t => t - ∫ y : ℝ, 2 * ((m : ℝ) + 1) *
              (physHermite m (mehlerArg ρ x y) * Real.exp (-(y ^ 2))))
              (integral_add (hI1.const_mul _) (hIy1.const_mul _))
        _ = (2 * ρ * x * (Real.sqrt Real.pi * ρ ^ (m + 1) * physHermite (m + 1) x) +
              2 * mehlerCoupling ρ *
                (mehlerCoupling ρ * (m + 1) *
                  (Real.sqrt Real.pi * ρ ^ m * physHermite m x))) -
              2 * ((m : ℝ) + 1) * (Real.sqrt Real.pi * ρ ^ m * physHermite m x) := by
            rw [integral_const_mul, hIH1, integral_const_mul, hStein, integral_const_mul, hIH0]
        _ = Real.sqrt Real.pi * ρ ^ (m + 2) * physHermite (m + 2) x := by
            have hs2 := mehlerCoupling_sq hρ
            have hrec := physHermite_succ_succ m x
            have hpow : ρ ^ (m + 2) = ρ ^ m * ρ ^ 2 := by rw [← pow_add]
            have hpow1 : ρ ^ (m + 1) = ρ ^ m * ρ := pow_succ ρ m
            rw [hrec, hpow, hpow1]
            ring_nf
            rw [hs2]
            ring

/-! ## 7. The Mehler operator and the gap of the limit proposal -/

/-- **One pCN step at infinite dimension**: the normalised Mehler average of `f` at `x`. -/
def mehlerOp (ρ : ℝ) (f : ℝ → ℝ) : ℝ → ℝ :=
  fun x => (Real.sqrt Real.pi)⁻¹ * ∫ y : ℝ, f (mehlerArg ρ x y) * Real.exp (-(y ^ 2))

/-- **The Hermite functions are the eigenfunctions of one pCN step** with eigenvalue `ρⁿ`: the
operator form of `mehler_hermite`, i.e. of `pcnl.md` Module 1 at `d = ∞`. -/
theorem mehlerOp_physHermite {ρ : ℝ} (hρ : ρ ^ 2 ≤ 1) (n : ℕ) :
    mehlerOp ρ (physHermite n) = fun x => ρ ^ n * physHermite n x := by
  have hpi : (Real.sqrt Real.pi) ≠ 0 := by positivity
  funext x
  simp only [mehlerOp, mehler_hermite n hρ x]
  field_simp

theorem mehlerOp_vacuum {ρ : ℝ} (hρ : ρ ^ 2 ≤ 1) : mehlerOp ρ (physHermite 0) = fun _ => 1 := by
  rw [mehlerOp_physHermite hρ 0]
  funext x
  simp

/-- **The gap of the limit proposal.**  With `0 ≤ ρ < 1` the vacuum has eigenvalue `1` and every
excited number state has eigenvalue at most `ρ`: the gap `1 − ρ` separates the vacuum from the
rest, the `d → ∞` counterpart of `pcnl.md` §1.A's `1 − √(1 − β²)`. -/
theorem mehler_gap {ρ : ℝ} (hρ0 : 0 ≤ ρ) (hρ1 : ρ ≤ 1) {n : ℕ} (hn : n ≠ 0) :
    1 - ρ ≤ 1 - ρ ^ n := by
  have hpow1 : ρ ^ (n - 1) ≤ 1 := pow_le_one₀ hρ0 hρ1
  have heq : ρ ^ n = ρ * ρ ^ (n - 1) := by
    cases n with
    | zero => exact absurd rfl hn
    | succ k => rw [Nat.succ_sub_one, pow_succ']
  have hle : ρ ^ n ≤ ρ := by
    rw [heq]
    calc ρ * ρ ^ (n - 1) ≤ ρ * 1 := mul_le_mul_of_nonneg_left hpow1 hρ0
      _ = ρ := mul_one ρ
  linarith

end BookProof.MCMC
