import Mathlib
import BookProof.ReflectionPositivity.ChapterMehlerTransitionDensity

/-!
# Chapter MehlerKernelSemigroup — H3's Gaussian convolution identity

The `N`-slice path measure is built by composing one-slice kernels.  This module proves the
exact convolution law for the closed-form density of H1:

    ∫ z, mehlerKernel ρ x z * mehlerKernel σ z y = mehlerKernel (ρ*σ) x y

for `ρ² < 1`, `σ² < 1`.  The proof completes the square in the quadratic exponent and uses
`integral_gaussian` plus translation invariance of Lebesgue measure.  It is the algebraic
identity the finite-slice Markov composition and the `N → ∞` Feynman–Kac limit consume.

No interacting potential, `N`-slice measure, continuum limit or reflection positivity is
proved here.  Axioms are `propext`, `Classical.choice`, `Quot.sound` only.
-/

set_option maxHeartbeats 800000

noncomputable section

namespace BookProof.MehlerKernelSemigroup

open BookProof.MehlerTransitionDensity
open Filter Topology

/-- The convolution of two Mehler steps is the Mehler step at the product parameter. -/
theorem mehlerKernel_integral_mul {ρ σ x y : ℝ} (hρ : ρ ^ 2 < 1) (hσ : σ ^ 2 < 1) :
    (∫ z : ℝ, mehlerKernel ρ x z * mehlerKernel σ z y) =
      mehlerKernel (ρ * σ) x y := by
  have ha : 0 < 1 - ρ ^ 2 := by linarith
  have hb : 0 < 1 - σ ^ 2 := by linarith
  have hprod : (ρ * σ) ^ 2 < 1 := by nlinarith [sq_nonneg (ρ ^ 2 - σ ^ 2)]
  have hd : 0 < 1 - (ρ * σ) ^ 2 := by linarith
  let a : ℝ := 1 - ρ ^ 2
  let b : ℝ := 1 - σ ^ 2
  let d : ℝ := 1 - (ρ * σ) ^ 2
  let A : ℝ := 1 / a + σ ^ 2 / b
  let B : ℝ := ρ * x / a + σ * y / b
  let C : ℝ := ρ ^ 2 * x ^ 2 / a + y ^ 2 / b
  have ha0 : a ≠ 0 := by dsimp [a]; linarith
  have hb0 : b ≠ 0 := by dsimp [b]; linarith
  have hA : 0 < A := by
    dsimp [A]
    positivity
  have hbap : 0 < b + a * σ ^ 2 := by
    have hpos : 0 < A * (a * b) := mul_pos hA (mul_pos ha hb)
    have heq : A * (a * b) = b + a * σ ^ 2 := by
      dsimp [A]
      field_simp [ha0, hb0]
    rwa [heq] at hpos
  have hbap0 : b + a * σ ^ 2 ≠ 0 := ne_of_gt hbap
  have hd0 : d ≠ 0 := ne_of_gt hd
  have hAeq : A * (a * b) = d := by
    dsimp [A, a, b, d]
    field_simp [ha0, hb0, hbap0, hd0]
    ring
  have hdecomp : ∀ z : ℝ,
      -(z - ρ * x) ^ 2 / a - (y - σ * z) ^ 2 / b =
        -A * (z - B / A) ^ 2 + (B ^ 2 / A - C) := by
    intro z
    dsimp [A, B, C]
    field_simp [ha0, hb0, hbap0, hd0]
    ring_nf
  have hexp : ∀ z : ℝ, Real.exp (-(z - ρ * x) ^ 2 / a) *
      Real.exp (-(y - σ * z) ^ 2 / b) =
        Real.exp (B ^ 2 / A - C) * Real.exp (-A * (z - B / A) ^ 2) := by
    intro z
    have hz := hdecomp z
    calc
      Real.exp (-(z - ρ * x) ^ 2 / a) * Real.exp (-(y - σ * z) ^ 2 / b)
          = Real.exp (-(z - ρ * x) ^ 2 / a + -(y - σ * z) ^ 2 / b) := by
              rw [Real.exp_add]
      _ = Real.exp (-(z - ρ * x) ^ 2 / a - (y - σ * z) ^ 2 / b) := by ring_nf
      _ = Real.exp (-A * (z - B / A) ^ 2 + (B ^ 2 / A - C)) := by rw [hz]
      _ = Real.exp (B ^ 2 / A - C) * Real.exp (-A * (z - B / A) ^ 2) := by
              rw [Real.exp_add]; ring_nf
  have htrans :
      (∫ z : ℝ, Real.exp (-A * (z - B / A) ^ 2)) =
        ∫ w : ℝ, Real.exp (-A * w ^ 2) := by
    let g : ℝ → ℝ := fun w => Real.exp (-A * w ^ 2)
    have ht := MeasureTheory.integral_add_right_eq_self (μ := MeasureTheory.volume) g (-(B / A))
    change (∫ w : ℝ, g (w + (-(B / A)))) = ∫ z : ℝ, g z at ht
    change (∫ w : ℝ, g (w + (-(B / A)))) = ∫ z : ℝ, g z
    exact ht
  have hgauss : (∫ w : ℝ, Real.exp (-A * w ^ 2)) = Real.sqrt (Real.pi / A) := by
    exact integral_gaussian A
  have hsqrta : Real.sqrt (Real.pi * a) = Real.sqrt Real.pi * Real.sqrt a := by
    rw [Real.sqrt_mul (le_of_lt Real.pi_pos)]
  have hsqrtb : Real.sqrt (Real.pi * b) = Real.sqrt Real.pi * Real.sqrt b := by
    rw [Real.sqrt_mul (le_of_lt Real.pi_pos)]
  have hsqrtd : Real.sqrt (Real.pi * d) = Real.sqrt Real.pi * Real.sqrt d := by
    rw [Real.sqrt_mul (le_of_lt Real.pi_pos)]
  have hAd : Real.sqrt (Real.pi / A) =
      Real.sqrt Real.pi * Real.sqrt (a * b) / Real.sqrt d := by
    have hAform : A = d / (a * b) := by
      rw [← hAeq]
      field_simp [mul_ne_zero ha0 hb0]
    rw [hAform]
    have habpos : 0 < a * b := mul_pos ha hb
    have hdiv : Real.pi / (d / (a * b)) = (Real.pi * (a * b)) / d := by
      field_simp [ne_of_gt habpos, ne_of_gt hd]
    rw [hdiv]
    rw [Real.sqrt_div (le_of_lt (mul_pos Real.pi_pos habpos))]
    rw [Real.sqrt_mul (le_of_lt Real.pi_pos)]
  have hd0' : 1 - ρ ^ 2 * σ ^ 2 ≠ 0 := by
    nlinarith [hd]
  have hnum : B ^ 2 / A - C = -(y - ρ * σ * x) ^ 2 / d := by
    dsimp [A, B, C, a, b, d]
    field_simp [ha0, hb0, hbap0, hd0']
    ring_nf
  have hpref : (Real.sqrt (Real.pi * a))⁻¹ * (Real.sqrt (Real.pi * b))⁻¹ *
      Real.sqrt Real.pi * Real.sqrt (a * b) / Real.sqrt d =
        (Real.sqrt (Real.pi * d))⁻¹ := by
    rw [hsqrta, hsqrtb, hsqrtd]
    have hapos : 0 < a := by dsimp [a]; exact ha
    have hbpos : 0 < b := by dsimp [b]; exact hb
    have hdpos : 0 < d := by dsimp [d]; exact hd
    have hsab : Real.sqrt (a * b) = Real.sqrt a * Real.sqrt b := by
      rw [Real.sqrt_mul (le_of_lt hapos)]
    rw [hsab]
    field_simp [ne_of_gt (Real.sqrt_pos.2 Real.pi_pos), ne_of_gt (Real.sqrt_pos.2 hapos),
      ne_of_gt (Real.sqrt_pos.2 hbpos), ne_of_gt (Real.sqrt_pos.2 hdpos)]
  dsimp [mehlerKernel]
  change (∫ z : ℝ, (Real.sqrt (Real.pi * a))⁻¹ * Real.exp (-(z - ρ * x) ^ 2 / a) *
      ((Real.sqrt (Real.pi * b))⁻¹ * Real.exp (-(y - σ * z) ^ 2 / b))) =
    (Real.sqrt (Real.pi * d))⁻¹ * Real.exp (-(y - ρ * σ * x) ^ 2 / d)
  have hmul (z : ℝ) :
      (Real.sqrt (Real.pi * a))⁻¹ * Real.exp (-(z - ρ * x) ^ 2 / a) *
          ((Real.sqrt (Real.pi * b))⁻¹ * Real.exp (-(y - σ * z) ^ 2 / b)) =
        ((Real.sqrt (Real.pi * a))⁻¹ * (Real.sqrt (Real.pi * b))⁻¹) *
          (Real.exp (-(z - ρ * x) ^ 2 / a) * Real.exp (-(y - σ * z) ^ 2 / b)) := by
    ring
  simp_rw [hmul, hexp]
  rw [MeasureTheory.integral_const_mul, MeasureTheory.integral_const_mul]
  rw [htrans, hgauss, hAd, hnum]
  calc
    ((Real.sqrt (Real.pi * a))⁻¹ * (Real.sqrt (Real.pi * b))⁻¹) *
        (Real.exp (-(y - ρ * σ * x) ^ 2 / d) *
          (Real.sqrt Real.pi * Real.sqrt (a * b) / Real.sqrt d)) =
      ((Real.sqrt (Real.pi * a))⁻¹ * (Real.sqrt (Real.pi * b))⁻¹ *
        Real.sqrt Real.pi * Real.sqrt (a * b) / Real.sqrt d) *
          Real.exp (-(y - ρ * σ * x) ^ 2 / d) := by ring
    _ = (Real.sqrt (Real.pi * d))⁻¹ * Real.exp (-(y - ρ * σ * x) ^ 2 / d) := by
      rw [hpref]

/-- The three-slice composition, with the integrals taken in path order (innermost first).
    This is the `N = 3` instance of the finite-slice Markov composition and needs no Fubini
    swap: the convolution law applies to the two inner slices, then to the outer one. -/
theorem mehlerKernel_integral_mul_three {ρ σ τ x y : ℝ}
    (hρ : ρ ^ 2 < 1) (hσ : σ ^ 2 < 1) (hτ : τ ^ 2 < 1) :
    (∫ z₁ : ℝ, ∫ z₂ : ℝ, mehlerKernel ρ x z₁ * mehlerKernel σ z₁ z₂ *
      mehlerKernel τ z₂ y) = mehlerKernel (ρ * σ * τ) x y := by
  have hστ : (σ * τ) ^ 2 < 1 := by nlinarith [sq_nonneg (σ ^ 2 - τ ^ 2)]
  calc
    (∫ z₁ : ℝ, ∫ z₂ : ℝ, mehlerKernel ρ x z₁ * mehlerKernel σ z₁ z₂ *
        mehlerKernel τ z₂ y) =
        ∫ z₁ : ℝ, mehlerKernel ρ x z₁ *
          (∫ z₂ : ℝ, mehlerKernel σ z₁ z₂ * mehlerKernel τ z₂ y) := by
      congr 1
      funext z₁
      rw [← MeasureTheory.integral_const_mul]
      congr 1
      funext z₂
      ring
    _ = ∫ z₁ : ℝ, mehlerKernel ρ x z₁ * mehlerKernel (σ * τ) z₁ y := by
      simp_rw [mehlerKernel_integral_mul hσ hτ]
    _ = mehlerKernel (ρ * (σ * τ)) x y := mehlerKernel_integral_mul hρ hστ
    _ = mehlerKernel (ρ * σ * τ) x y := by ring_nf

/-! ## Arbitrary finite slice count -/

/-- Product of the parameters of a slice schedule. -/
def paramProd : List ℝ → ℝ
  | [] => 1
  | ρ :: ρs => ρ * paramProd ρs

/-- The nested path integral over `n` intermediate slices, in path order. -/
def pathIntegral : List ℝ → ℝ → ℝ → ℝ
  | [], _, _ => 1
  | [ρ], x, y => mehlerKernel ρ x y
  | ρ :: ρs, x, y => ∫ z : ℝ, mehlerKernel ρ x z * pathIntegral ρs z y

/-- The product parameter stays inside the unit disc when every slice parameter does
    and the schedule is nonempty. -/
theorem paramProd_sq_lt_one : ∀ {ρs : List ℝ}, ρs ≠ [] →
    (∀ ρ ∈ ρs, ρ ^ 2 < 1) → (paramProd ρs) ^ 2 < 1 := by
  intro ρs hne h
  cases ρs with
  | nil => exact (hne rfl).elim
  | cons ρ ρs =>
      cases ρs with
      | nil => simpa [paramProd] using h ρ (by simp)
      | cons σ ρs =>
          have hρ : ρ ^ 2 < 1 := h ρ (by simp)
          have htail : ∀ τ ∈ σ :: ρs, τ ^ 2 < 1 := by intro τ hτ; exact h τ (by simp [hτ])
          have ht : (paramProd (σ :: ρs)) ^ 2 < 1 :=
            paramProd_sq_lt_one (ρs := σ :: ρs) (by simp) htail
          change (ρ * paramProd (σ :: ρs)) ^ 2 < 1
          have hp : (ρ * paramProd (σ :: ρs)) ^ 2 = ρ ^ 2 * (paramProd (σ :: ρs)) ^ 2 := by ring
          rw [hp]
          nlinarith [sq_nonneg ρ, sq_nonneg (paramProd (σ :: ρs))]

/-- **The finite-slice composition law.**  For a nonempty finite schedule the nested path
    integral is the closed kernel at the product of its parameters.  No Fubini swap is needed:
    each inner integral is taken in path order, so the two-kernel convolution applies at each
    step. -/
theorem pathIntegral_eq : ∀ (ρs : List ℝ), ρs ≠ [] → (∀ ρ ∈ ρs, ρ ^ 2 < 1) →
    ∀ x y : ℝ, pathIntegral ρs x y = mehlerKernel (paramProd ρs) x y := by
  intro ρs hne h
  induction ρs with
  | nil => intro x y; exact (hne rfl).elim
  | cons ρ ρs ih =>
      intro x y
      have hρ : ρ ^ 2 < 1 := h ρ (by simp)
      have htail0 : ∀ σ ∈ ρs, σ ^ 2 < 1 := by intro σ hσ; exact h σ (by simp [hσ])
      cases ρs with
      | nil =>
          simp [pathIntegral, paramProd]
      | cons σ ρs =>
          have htail : ∀ τ ∈ σ :: ρs, τ ^ 2 < 1 := by intro τ hτ; exact h τ (by simp [hτ])
          have ht : (paramProd (σ :: ρs)) ^ 2 < 1 :=
            paramProd_sq_lt_one (ρs := σ :: ρs) (by simp) htail
          dsimp [pathIntegral, paramProd]
          calc
            (∫ z : ℝ, mehlerKernel ρ x z * pathIntegral (σ :: ρs) z y) =
                ∫ z : ℝ, mehlerKernel ρ x z * mehlerKernel (paramProd (σ :: ρs)) z y := by
              congr 1
              funext z
              have ihz := ih (by simp) htail0 z y
              rw [ihz]
            _ = mehlerKernel (ρ * paramProd (σ :: ρs)) x y :=
              mehlerKernel_integral_mul hρ ht

/-- Repeated product of a constant schedule. -/
theorem paramProd_replicate (r : ℝ) : ∀ N : ℕ, paramProd (List.replicate N r) = r ^ N
  | 0 => rfl
  | N + 1 => by
      simp [List.replicate_succ, paramProd, paramProd_replicate r N]
      ring

/-- The exponential time schedule `ρ_N = exp(−T/N)` reproduces the continuous-time parameter
    exactly after `N` slices: `ρ_N^N = exp(−T)`.  Combined with `pathIntegral_eq` this gives the
    `N`-slice representation of the continuous-time Mehler kernel at fixed cutoffs. -/
theorem pathIntegral_exp_schedule {T : ℝ} (hT : 0 < T) {N : ℕ} (hN : 0 < N)
    (x y : ℝ) :
    pathIntegral (List.replicate N (Real.exp (-T / N))) x y =
      mehlerKernel (Real.exp (-T)) x y := by
  have hNr : 0 < (N : ℝ) := by exact_mod_cast hN
  have hρ : (Real.exp (-T / N)) ^ 2 < 1 := by
    have hnegT : -T < 0 := by linarith
    have hneg : -T / (N : ℝ) < 0 := div_neg_of_neg_of_pos hnegT hNr
    have hlt : Real.exp (-T / N) < 1 := Real.exp_lt_one_iff.mpr hneg
    have hpos : 0 < Real.exp (-T / N) := Real.exp_pos _
    nlinarith
  have hmem : ∀ ρ ∈ List.replicate N (Real.exp (-T / N)), ρ ^ 2 < 1 := by
    intro ρ hρmem
    have hmem' : ¬N = 0 ∧ ρ = Real.exp (-T / N) := by simpa using hρmem
    rw [hmem'.2]
    exact hρ
  have hpath := pathIntegral_eq (List.replicate N (Real.exp (-T / N)))
    (by simp [ne_of_gt hN]) hmem x y
  rw [hpath]
  rw [paramProd_replicate]
  rw [← Real.exp_nat_mul]
  congr 1
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast (ne_of_gt hN)
  field_simp [hN0]

/-! ## The continuum parameter limit -/

/-- The Euler schedule `ρ_N = 1 − T/N` has product parameter tending to `exp(−T)`. -/
theorem tendsto_paramProd_linear (T : ℝ) :
    Tendsto (fun N : ℕ => paramProd (List.replicate N (1 - T / N))) atTop
      (𝓝 (Real.exp (-T))) := by
  have heq : (fun N : ℕ => paramProd (List.replicate N (1 - T / N))) =
      fun N : ℕ => (1 + (-T) / (N : ℝ)) ^ N := by
    funext N
    rw [paramProd_replicate]
    congr 1
    ring
  rw [heq]
  exact Real.tendsto_one_add_div_pow_exp (-T)

/-- The finite-slice path integrals of the Euler schedule converge to the continuous-time
    Mehler kernel.  This is the parameter-level continuum limit: the interacting potential
    weight and the measure-valued `N → ∞` transfer are still open (H3). -/
theorem tendsto_pathIntegral_linear {T : ℝ} (hT : 0 < T) (x y : ℝ) :
    Tendsto (fun N : ℕ => pathIntegral (List.replicate N (1 - T / N)) x y) atTop
      (𝓝 (mehlerKernel (Real.exp (-T)) x y)) := by
  have hparam := tendsto_paramProd_linear T
  have hexplt : (Real.exp (-T)) ^ 2 < 1 := by
    have hneg : -T < 0 := by linarith
    have hlt : Real.exp (-T) < 1 := Real.exp_lt_one_iff.mpr hneg
    have hpos : 0 < Real.exp (-T) := Real.exp_pos _
    nlinarith
  have hcont : ContinuousAt (fun ρ : ℝ => mehlerKernel ρ x y) (Real.exp (-T)) := by
    dsimp [mehlerKernel]
    have hden : 1 - (Real.exp (-T)) ^ 2 ≠ 0 := by linarith
    have hsqrt_pos : 0 < Real.sqrt (Real.pi * (1 - (Real.exp (-T)) ^ 2)) := by
      apply Real.sqrt_pos.2
      exact mul_pos Real.pi_pos (by linarith)
    have hpref : ContinuousAt (fun ρ : ℝ => (Real.sqrt (Real.pi * (1 - ρ ^ 2)))⁻¹)
        (Real.exp (-T)) := by
      apply ContinuousAt.inv₀
      · fun_prop
      · exact ne_of_gt hsqrt_pos
    have hexparg : ContinuousAt (fun ρ : ℝ => (-(y - ρ * x) ^ 2) / (1 - ρ ^ 2))
        (Real.exp (-T)) := by
      apply ContinuousAt.div₀
      · fun_prop
      · fun_prop
      · exact hden
    exact hpref.mul (Real.continuous_exp.continuousAt.comp hexparg)
  apply (hcont.tendsto.comp hparam).congr'
  filter_upwards [eventually_gt_atTop (Nat.ceil T)] with N hN
  have hNr : 0 < (N : ℝ) := by
    have : 0 < N := by omega
    exact_mod_cast this
  have hmem : ∀ ρ ∈ List.replicate N (1 - T / N), ρ ^ 2 < 1 := by
    intro ρ hρmem
    have hρmem' : ¬N = 0 ∧ ρ = 1 - T / N := by simpa using hρmem
    rw [hρmem'.2]
    have hle : T / (N : ℝ) < 1 := by
      have hTle : T ≤ (Nat.ceil T : ℝ) := Nat.le_ceil T
      have hNc : (Nat.ceil T : ℝ) < (N : ℝ) := by exact_mod_cast hN
      rw [div_lt_one hNr]
      linarith
    have hpos : 0 < 1 - T / (N : ℝ) := by linarith
    have hdivpos : 0 < T / (N : ℝ) := div_pos hT hNr
    have hlt : 1 - T / (N : ℝ) < 1 := by linarith
    nlinarith
  have hne : List.replicate N (1 - T / N) ≠ [] := by
    simp [ne_of_gt (show 0 < N by omega)]
  rw [pathIntegral_eq (List.replicate N (1 - T / N)) hne hmem x y]
  rfl

end BookProof.MehlerKernelSemigroup
