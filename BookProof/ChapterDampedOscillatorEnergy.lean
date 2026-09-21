import Mathlib

/-!
# The damped coupled oscillators: no conserved energy, but conserved probability

This module formalizes the concrete example of the section *"Wave-function
parametrization of dissipative dynamics"* of `book.tex` (lines 2184–2222), the
two classical coupled oscillators with different frequencies and different
damping constants,

```
ẍ₁ + λ₁ ẋ₁ + ω₁² x₁ − c x₂ = 0,
ẍ₂ + λ₂ ẋ₂ + ω₂² x₂ − c x₁ = 0,
```

about which the manuscript says: *"Since this system is dissipative, it cannot
have a conserved Energy but the pendulums do not disappear and thus the
probability is conserved."*

## Results

* `hasDerivAt_dampedEnergy`, `dampedEnergy_antitone`,
  `dampedEnergy_not_constant_of_damped` — for a single damped oscillator the
  mechanical energy `½ẋ² + ½ω²x²` has derivative `−λ ẋ²`; it is therefore
  non-increasing when the damping is non-negative, and it is *not* conserved as
  soon as the damping is positive and the oscillator is moving at some instant.
* `hasDerivAt_coupledEnergy`, `coupledEnergy_antitone`,
  `coupledEnergy_not_constant_of_damped` — the same three statements for the
  book's coupled pair, whose energy `½(ẋ₁² + ẋ₂²) + ½(ω₁²x₁² + ω₂²x₂²) − c x₁x₂`
  decays at the rate `−λ₁ẋ₁² − λ₂ẋ₂²`.
* `criticallyDamped_isSolution`, `criticallyDamped_energy`,
  `criticallyDamped_energy_strictAnti` — a completely explicit non-trivial
  solution (`x t = e^{−t}` with `λ = 2`, `ω = 1`) whose energy `e^{−2t}` is
  strictly decreasing: the dissipation statement is not vacuous.
* `total_probability_conserved` — meanwhile the total probability *is* conserved
  by any (measurable) deterministic evolution of the state: the pushforward of a
  probability measure along the evolution is again a probability measure.  This
  is the manuscript's reason to parametrize the state by a wave-function rather
  than by a conserved energy.

Everything in this module is `sorry`-free and `axiom`-free.
-/

namespace BookProof.DampedOscillatorEnergy

open MeasureTheory

/-! ## 1. One damped oscillator -/

/-- The mechanical energy `½ẋ² + ½ω²x²` of an oscillator with position `x` and
velocity `v`. -/
noncomputable def dampedEnergy (omega : ℝ) (x v : ℝ → ℝ) (t : ℝ) : ℝ :=
  v t ^ 2 / 2 + omega ^ 2 * x t ^ 2 / 2

/-- **Energy balance.** Along a solution of `ẍ + λẋ + ω²x = 0` the energy has
derivative `−λ ẋ²`. -/
theorem hasDerivAt_dampedEnergy {lam omega : ℝ} {x v a : ℝ → ℝ}
    (hx : ∀ t, HasDerivAt x (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (heq : ∀ t, a t + lam * v t + omega ^ 2 * x t = 0) (t : ℝ) :
    HasDerivAt (dampedEnergy omega x v) (-(lam * v t ^ 2)) t := by
  have hderiv : HasDerivAt (dampedEnergy omega x v)
      (v t * a t + omega ^ 2 * (x t * v t)) t := by
    have h1 : HasDerivAt (fun s => v s ^ 2 / 2) (v t * a t) t := by
      have h := ((hv t).pow 2).div_const 2
      convert h using 1
      ring
    have h2 : HasDerivAt (fun s => omega ^ 2 * x s ^ 2 / 2) (omega ^ 2 * (x t * v t)) t := by
      have h := (((hx t).pow 2).const_mul (omega ^ 2)).div_const 2
      convert h using 1
      ring
    simpa [dampedEnergy] using h1.add h2
  have hrate : v t * a t + omega ^ 2 * (x t * v t) = -(lam * v t ^ 2) := by
    have ha : a t = -(lam * v t) - omega ^ 2 * x t := by linarith [heq t]
    rw [ha]; ring
  rwa [hrate] at hderiv

/-- With non-negative damping the energy is non-increasing. -/
theorem dampedEnergy_antitone {lam omega : ℝ} {x v a : ℝ → ℝ} (hlam : 0 ≤ lam)
    (hx : ∀ t, HasDerivAt x (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (heq : ∀ t, a t + lam * v t + omega ^ 2 * x t = 0) :
    Antitone (dampedEnergy omega x v) := by
  refine antitone_of_deriv_nonpos
    (fun t => (hasDerivAt_dampedEnergy hx hv heq t).differentiableAt) (fun t => ?_)
  rw [(hasDerivAt_dampedEnergy hx hv heq t).deriv]
  have : 0 ≤ lam * v t ^ 2 := mul_nonneg hlam (sq_nonneg _)
  linarith

/-- **The energy is not conserved.** If the damping is positive and the
oscillator is moving at some instant, the mechanical energy is not a constant of
the motion. -/
theorem dampedEnergy_not_constant_of_damped {lam omega : ℝ} {x v a : ℝ → ℝ}
    (hlam : 0 < lam) (hx : ∀ t, HasDerivAt x (v t) t) (hv : ∀ t, HasDerivAt v (a t) t)
    (heq : ∀ t, a t + lam * v t + omega ^ 2 * x t = 0) {t₀ : ℝ} (hmove : v t₀ ≠ 0) :
    ¬ ∃ E : ℝ, ∀ t, dampedEnergy omega x v t = E := by
  rintro ⟨E, hE⟩
  have hconst : HasDerivAt (dampedEnergy omega x v) 0 t₀ := by
    have : dampedEnergy omega x v = fun _ => E := funext hE
    rw [this]
    exact hasDerivAt_const t₀ E
  have hval := (hasDerivAt_dampedEnergy hx hv heq t₀).unique hconst
  have hsq : 0 < v t₀ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hmove))
  have hpos : 0 < lam * v t₀ ^ 2 := mul_pos hlam hsq
  linarith

/-! ## 2. The book's coupled pair -/

/-- The energy of the coupled pair, including the coupling term. -/
noncomputable def coupledEnergy (omega1 omega2 c : ℝ) (x1 x2 v1 v2 : ℝ → ℝ) (t : ℝ) : ℝ :=
  v1 t ^ 2 / 2 + v2 t ^ 2 / 2 + omega1 ^ 2 * x1 t ^ 2 / 2 + omega2 ^ 2 * x2 t ^ 2 / 2
    - c * (x1 t * x2 t)

/-- **Energy balance for the coupled pair.** -/
theorem hasDerivAt_coupledEnergy {lam1 lam2 omega1 omega2 c : ℝ}
    {x1 x2 v1 v2 a1 a2 : ℝ → ℝ}
    (hx1 : ∀ t, HasDerivAt x1 (v1 t) t) (hx2 : ∀ t, HasDerivAt x2 (v2 t) t)
    (hv1 : ∀ t, HasDerivAt v1 (a1 t) t) (hv2 : ∀ t, HasDerivAt v2 (a2 t) t)
    (heq1 : ∀ t, a1 t + lam1 * v1 t + omega1 ^ 2 * x1 t - c * x2 t = 0)
    (heq2 : ∀ t, a2 t + lam2 * v2 t + omega2 ^ 2 * x2 t - c * x1 t = 0) (t : ℝ) :
    HasDerivAt (coupledEnergy omega1 omega2 c x1 x2 v1 v2)
      (-(lam1 * v1 t ^ 2) - lam2 * v2 t ^ 2) t := by
  have h1 : HasDerivAt (fun s => v1 s ^ 2 / 2) (v1 t * a1 t) t := by
    have h := ((hv1 t).pow 2).div_const 2
    convert h using 1
    ring
  have h2 : HasDerivAt (fun s => v2 s ^ 2 / 2) (v2 t * a2 t) t := by
    have h := ((hv2 t).pow 2).div_const 2
    convert h using 1
    ring
  have h3 : HasDerivAt (fun s => omega1 ^ 2 * x1 s ^ 2 / 2) (omega1 ^ 2 * (x1 t * v1 t)) t := by
    have h := (((hx1 t).pow 2).const_mul (omega1 ^ 2)).div_const 2
    convert h using 1
    ring
  have h4 : HasDerivAt (fun s => omega2 ^ 2 * x2 s ^ 2 / 2) (omega2 ^ 2 * (x2 t * v2 t)) t := by
    have h := (((hx2 t).pow 2).const_mul (omega2 ^ 2)).div_const 2
    convert h using 1
    ring
  have h5 : HasDerivAt (fun s => c * (x1 s * x2 s))
      (c * (v1 t * x2 t + x1 t * v2 t)) t := ((hx1 t).mul (hx2 t)).const_mul c
  have hsum := ((((h1.add h2).add h3).add h4).sub h5)
  have hrate : v1 t * a1 t + v2 t * a2 t + omega1 ^ 2 * (x1 t * v1 t)
      + omega2 ^ 2 * (x2 t * v2 t) - c * (v1 t * x2 t + x1 t * v2 t)
      = -(lam1 * v1 t ^ 2) - lam2 * v2 t ^ 2 := by
    have ha1 : a1 t = -(lam1 * v1 t) - omega1 ^ 2 * x1 t + c * x2 t := by linarith [heq1 t]
    have ha2 : a2 t = -(lam2 * v2 t) - omega2 ^ 2 * x2 t + c * x1 t := by linarith [heq2 t]
    rw [ha1, ha2]; ring
  have : HasDerivAt (coupledEnergy omega1 omega2 c x1 x2 v1 v2)
      (v1 t * a1 t + v2 t * a2 t + omega1 ^ 2 * (x1 t * v1 t)
        + omega2 ^ 2 * (x2 t * v2 t) - c * (v1 t * x2 t + x1 t * v2 t)) t := by
    simpa [coupledEnergy] using hsum
  rwa [hrate] at this

/-- With non-negative damping constants the energy of the coupled pair is
non-increasing. -/
theorem coupledEnergy_antitone {lam1 lam2 omega1 omega2 c : ℝ} {x1 x2 v1 v2 a1 a2 : ℝ → ℝ}
    (hlam1 : 0 ≤ lam1) (hlam2 : 0 ≤ lam2)
    (hx1 : ∀ t, HasDerivAt x1 (v1 t) t) (hx2 : ∀ t, HasDerivAt x2 (v2 t) t)
    (hv1 : ∀ t, HasDerivAt v1 (a1 t) t) (hv2 : ∀ t, HasDerivAt v2 (a2 t) t)
    (heq1 : ∀ t, a1 t + lam1 * v1 t + omega1 ^ 2 * x1 t - c * x2 t = 0)
    (heq2 : ∀ t, a2 t + lam2 * v2 t + omega2 ^ 2 * x2 t - c * x1 t = 0) :
    Antitone (coupledEnergy omega1 omega2 c x1 x2 v1 v2) := by
  refine antitone_of_deriv_nonpos
    (fun t => (hasDerivAt_coupledEnergy hx1 hx2 hv1 hv2 heq1 heq2 t).differentiableAt)
    (fun t => ?_)
  rw [(hasDerivAt_coupledEnergy hx1 hx2 hv1 hv2 heq1 heq2 t).deriv]
  have p1 : 0 ≤ lam1 * v1 t ^ 2 := mul_nonneg hlam1 (sq_nonneg _)
  have p2 : 0 ≤ lam2 * v2 t ^ 2 := mul_nonneg hlam2 (sq_nonneg _)
  linarith

/-- **The coupled pair has no conserved energy.** -/
theorem coupledEnergy_not_constant_of_damped {lam1 lam2 omega1 omega2 c : ℝ}
    {x1 x2 v1 v2 a1 a2 : ℝ → ℝ} (hlam1 : 0 < lam1) (hlam2 : 0 ≤ lam2)
    (hx1 : ∀ t, HasDerivAt x1 (v1 t) t) (hx2 : ∀ t, HasDerivAt x2 (v2 t) t)
    (hv1 : ∀ t, HasDerivAt v1 (a1 t) t) (hv2 : ∀ t, HasDerivAt v2 (a2 t) t)
    (heq1 : ∀ t, a1 t + lam1 * v1 t + omega1 ^ 2 * x1 t - c * x2 t = 0)
    (heq2 : ∀ t, a2 t + lam2 * v2 t + omega2 ^ 2 * x2 t - c * x1 t = 0)
    {t₀ : ℝ} (hmove : v1 t₀ ≠ 0) :
    ¬ ∃ E : ℝ, ∀ t, coupledEnergy omega1 omega2 c x1 x2 v1 v2 t = E := by
  rintro ⟨E, hE⟩
  have hconst : HasDerivAt (coupledEnergy omega1 omega2 c x1 x2 v1 v2) 0 t₀ := by
    have hfun : coupledEnergy omega1 omega2 c x1 x2 v1 v2 = fun _ => E := funext hE
    rw [hfun]
    exact hasDerivAt_const t₀ E
  have hval := (hasDerivAt_coupledEnergy hx1 hx2 hv1 hv2 heq1 heq2 t₀).unique hconst
  have hsq : 0 < v1 t₀ ^ 2 := lt_of_le_of_ne (sq_nonneg _) (Ne.symm (pow_ne_zero 2 hmove))
  have hpos : 0 < lam1 * v1 t₀ ^ 2 := mul_pos hlam1 hsq
  have hnn : 0 ≤ lam2 * v2 t₀ ^ 2 := mul_nonneg hlam2 (sq_nonneg _)
  linarith

/-! ## 3. An explicit dissipating solution -/

/-- The position of the critically damped motion, `x t = e^{−t}`, differentiates
to its velocity `−e^{−t}`. -/
theorem criticallyDamped_hasDerivAt_pos (t : ℝ) :
    HasDerivAt (fun s => Real.exp (-s)) (-Real.exp (-t)) t := by
  have h := (Real.hasDerivAt_exp (-t)).comp t ((hasDerivAt_id t).neg)
  simpa using h

/-- Its velocity differentiates to its acceleration `e^{−t}`. -/
theorem criticallyDamped_hasDerivAt_vel (t : ℝ) :
    HasDerivAt (fun s => -Real.exp (-s)) (Real.exp (-t)) t := by
  simpa using (criticallyDamped_hasDerivAt_pos t).neg

/-- The critically damped motion `x t = e^{−t}` solves `ẍ + 2ẋ + x = 0`. -/
theorem criticallyDamped_isSolution (t : ℝ) :
    (Real.exp (-t)) + 2 * (-Real.exp (-t)) + 1 ^ 2 * Real.exp (-t) = 0 := by
  ring

/-- The general energy balance, applied to this explicit motion. -/
theorem criticallyDamped_hasDerivAt_energy (t : ℝ) :
    HasDerivAt (dampedEnergy 1 (fun s => Real.exp (-s)) (fun s => -Real.exp (-s)))
      (-(2 * (-Real.exp (-t)) ^ 2)) t :=
  hasDerivAt_dampedEnergy criticallyDamped_hasDerivAt_pos criticallyDamped_hasDerivAt_vel
    criticallyDamped_isSolution t

/-- Its energy is not conserved, by the general theorem. -/
theorem criticallyDamped_energy_not_constant :
    ¬ ∃ E : ℝ, ∀ t, dampedEnergy 1 (fun s => Real.exp (-s)) (fun s => -Real.exp (-s)) t = E :=
  dampedEnergy_not_constant_of_damped (by norm_num) criticallyDamped_hasDerivAt_pos
    criticallyDamped_hasDerivAt_vel criticallyDamped_isSolution (t₀ := 0)
    (by simp)

/-- Its energy is `e^{−2t}`. -/
theorem criticallyDamped_energy (t : ℝ) :
    dampedEnergy 1 (fun s => Real.exp (-s)) (fun s => -Real.exp (-s)) t
      = Real.exp (-t) ^ 2 := by
  simp [dampedEnergy]

/-- And it is strictly decreasing: the dissipation statement is not vacuous. -/
theorem criticallyDamped_energy_strictAnti :
    StrictAnti (dampedEnergy 1 (fun s => Real.exp (-s)) (fun s => -Real.exp (-s))) := by
  intro s t hst
  rw [criticallyDamped_energy, criticallyDamped_energy]
  have h : Real.exp (-t) < Real.exp (-s) := Real.exp_lt_exp.mpr (by linarith)
  have hpos : 0 < Real.exp (-t) := Real.exp_pos _
  nlinarith [Real.exp_pos (-s)]

/-! ## 4. Probability is conserved -/

/-- **The total probability is conserved** by any measurable deterministic
evolution of the state, whether or not the energy is: the pushforward of a
probability measure along the evolution is again a probability measure.  This is
the manuscript's reason for parametrizing the state of a dissipative system by a
wave-function (a square root of a probability density) instead of by a conserved
energy. -/
theorem total_probability_conserved {Ω : Type*} [MeasurableSpace Ω] (μ : Measure Ω)
    [IsProbabilityMeasure μ] {T : Ω → Ω} (hT : Measurable T) :
    (μ.map T) Set.univ = 1 := by
  rw [Measure.map_apply hT MeasurableSet.univ, Set.preimage_univ, measure_univ]

end BookProof.DampedOscillatorEnergy
