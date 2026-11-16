import Mathlib
import BookProof.OSReconstruction.GaussianMehlerControl
import BookProof.OSReconstruction.HalfSpaceCovariantReflectionPositivity

/-!
# C1, all-degree lift: reflection positivity from the boundary-conditioned kernel

`cftproof.md` **C1** asks for reflected-covariance positivity on half-space tests and its
lift to *all polynomial cylinders*.  `GaussianMehlerControl` proves the covariance form
(`rp_covariance`).  This module supplies the lift, in the boundary-conditioned-kernel
form the work order allows.

## Why the covariance form is not enough to iterate

Wick's theorem does *not* iterate degree by degree: at degree two the Isserlis sum
collapses to a square (`ReflectionPositivity/QuadraticWick.lean`), but at degree three and
beyond the pairing sum is a permanent of the reflected kernel and carries no sign in
general.  The all-degree mechanism is instead the **kernel factorization** of the free
state: condition on the boundary combination, after which the two halves are independent
copies of one and the same law, so the OS form is a mean of squares.

## The two-slice Gaussian in slice coordinates

In Mehler coordinates the C1 covariance is diagonal with `v₊ k = variance m₀ (true, k)` and
`v₋ k = variance m₀ (false, k)`, and `v₊ k ≥ v₋ k` (`variance_symm_ge_antisymm`).  In the
slice coordinates `x₀ = (y₊ − y₋)/√2`, `x₁ = (y₊ + y₋)/√2` this is the reflection-invariant
block covariance

```text
Cov = [[A, B], [B, A]],   A k = (v₊ k + v₋ k)/2,   B k = (v₊ k − v₋ k)/2 ≥ 0,
```

and it is exactly the covariance of the **shared-shift mixture**

```text
x₀ = T + X,   x₁ = T + Y,   T, X, Y independent,
Var T k = B k = (v₊ k − v₋ k)/2,   Var X k = Var Y k = v₋ k.
```

(The two blocks agree because `B k + v₋ k = (v₊ k + v₋ k)/2 = A k` and `Cov x₀ x₁ = Var T`.)
For `B k ≥ 0` the mixture exists as a probability law, which is precisely the source of the
all-degree positivity: the shared shift couples the halves, and conditioning on it makes
them independent with *the same* law.

## Contents

* `shiftVariance`, `noiseVariance`, `shiftLaw`, `noiseLaw` — the boundary and half laws;
* `kernelMap`, `kernelLaw` — the shared-shift state on slice pairs;
* `kernelLaw_isProbability` — it is a normalized probability law;
* `kernelLaw_reflectionPositive` — **the all-degree lift**: for every bounded measurable
  cylinder observable `F` of one half,
  `0 ≤ ∫ z, F z.2 * F z.1 ∂(kernelLaw m₀)`;
* `kernelLaw_reflectionPositive_of_integrable` — the same inequality with the boundedness
  replaced by integrability of the OS integrand, which is the form that covers an
  **unbounded polynomial cylinder** `P (T + X) * P (T + Y)`;
* `timeOne`, `timeZero`, `timeOne_reflect`, `timeZero_reflect` — the slice coordinates as
  functions of a Mehler configuration, and the identity that the Mehler reflection swaps
  them; `sliceVariance_eq` — the mixture's marginal/cross variances add up to the C1
  Mehler values `(v₊ + v₋)/2` and `(v₊ − v₋)/2`;
* `sliceCovariance` — the covariance form of the mixture, `A` on the diagonal and `B`
  across, matching the C1 Mehler covariance in slice coordinates;
* `rp_degree_two` — the degree-two specialization, recovering
  `ReflectionPositivity.QuadraticWick.osQuadForm_nonneg` from the kernel form.

## Honest boundary

* The unconditional theorem is stated for **bounded measurable** cylinder observables.
  Polynomials are unbounded but their OS integrand is a polynomial in Gaussian variables,
  hence integrable; that is exactly the hypothesis of
  `kernelLaw_reflectionPositive_of_integrable`, so every polynomial cylinder whose OS form
  is Gaussian-integrable gets the inequality.  The moment-finiteness itself (a standard
  polynomial-times-Gaussian computation) is the input, not proved here.
* The identification is at the level of the **covariance**: `sliceCovariance` shows the
  mixture and the C1 Mehler law have the same two-point function, hence the same free
  covariance.  Equality of the two Gaussian laws themselves is not formalized here (both
  are Gaussian with this covariance, so they coincide as probability measures).
* The transfer operator of the mixture is its average over the boundary law, not the
  interacting dynamics; nothing here is a statement about the Wilson measure.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped BigOperators

namespace BookProof.OSReconstruction

variable {M : ℕ}

/-! ## 1. The boundary and half laws -/

/-- The variance of the **shared boundary shift** `T`: half the Mehler mass splitting,
`(v₊ − v₋)/2`.  It is nonnegative exactly because the symmetric mode dominates
(`variance_symm_ge_antisymm`). -/
def shiftVariance (m0 : ℝ) (k : SpatialMode M) : ℝ :=
  (variance m0 (true, k) - variance m0 (false, k)) / 2

theorem shiftVariance_nonneg (m0 : ℝ) (k : SpatialMode M) : 0 ≤ shiftVariance m0 k := by
  unfold shiftVariance
  have h := variance_symm_ge_antisymm m0 k
  linarith

/-- The variance of each **half's own noise** `X`, `Y`: the antisymmetric Mehler variance. -/
def noiseVariance (m0 : ℝ) (k : SpatialMode M) : ℝ := variance m0 (false, k)

theorem noiseVariance_pos (m0 : ℝ) (k : SpatialMode M) : 0 < noiseVariance m0 k :=
  variance_pos m0 (false, k)

/-- The law of the shared boundary shift. -/
def shiftLaw (m0 : ℝ) : Measure (SpatialMode M → ℝ) :=
  Measure.pi fun k => gaussianReal 0
    ⟨shiftVariance m0 k, shiftVariance_nonneg m0 k⟩

/-- The law of one half's own noise. -/
def noiseLaw (m0 : ℝ) : Measure (SpatialMode M → ℝ) :=
  Measure.pi fun k => gaussianReal 0
    ⟨noiseVariance m0 k, le_of_lt (noiseVariance_pos m0 k)⟩

instance shiftLaw_isProbability (m0 : ℝ) : IsProbabilityMeasure (shiftLaw (M := M) m0) := by
  unfold shiftLaw
  infer_instance

instance noiseLaw_isProbability (m0 : ℝ) : IsProbabilityMeasure (noiseLaw (M := M) m0) := by
  unfold noiseLaw
  infer_instance

/-! ## 2. The shared-shift state on slice pairs -/

/-- The coupling `(T, X, Y) ↦ (T + X, T + Y)`: both halves share the boundary shift. -/
def kernelMap {M : ℕ} (p : (SpatialMode M → ℝ) × ((SpatialMode M → ℝ) × (SpatialMode M → ℝ))) :
    (SpatialMode M → ℝ) × (SpatialMode M → ℝ) :=
  (p.1 + p.2.1, p.1 + p.2.2)

theorem measurable_kernelMap : Measurable (kernelMap (M := M)) := by
  unfold kernelMap
  fun_prop

/-- **The boundary-conditioned kernel state**: the law of the slice pair `(x₀, x₁)`. -/
def kernelLaw (m0 : ℝ) : Measure ((SpatialMode M → ℝ) × (SpatialMode M → ℝ)) :=
  ((shiftLaw m0).prod ((noiseLaw m0).prod (noiseLaw m0))).map kernelMap

instance kernelLaw_isProbability (m0 : ℝ) : IsProbabilityMeasure (kernelLaw (M := M) m0) := by
  unfold kernelLaw
  exact Measure.isProbabilityMeasure_map measurable_kernelMap.aemeasurable

/-! ## 3. The all-degree lift -/

/-- **Reflection positivity of the boundary-conditioned kernel state, all degrees.**

For every bounded measurable cylinder observable `F` of one half, the OS form is
nonnegative.  Conditioning on the shared shift `T` makes the two halves independent copies
of the law `T + X`, so the OS form is the boundary average of `(∫ F (t + x) ∂γ)²`.

No degree restriction appears: the square is produced by the factorization, not by Wick's
theorem, so this covers every bounded polynomial cylinder at once. -/
theorem kernelLaw_reflectionPositive (m0 : ℝ) (F : (SpatialMode M → ℝ) → ℝ)
    (hF : Measurable F) (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, |F x| ≤ C) :
    0 ≤ ∫ z : (SpatialMode M → ℝ) × (SpatialMode M → ℝ), F z.2 * F z.1
      ∂(kernelLaw m0) := by
  classical
  set γ := noiseLaw m0 with hγ
  set ν := shiftLaw m0 with hν
  set S : (SpatialMode M → ℝ) → ℝ := fun t => ∫ x, F (t + x) ∂γ with hS
  have hbound : ∀ t : SpatialMode M → ℝ, ∀ᵐ q ∂(γ.prod γ),
      ‖F (t + q.2) * F (t + q.1)‖ ≤ C * C := by
    intro t
    filter_upwards with q
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hC _) (hC _) (abs_nonneg _) hC0
  have hmeas_inner : ∀ t : SpatialMode M → ℝ, AEStronglyMeasurable
      (fun q : (SpatialMode M → ℝ) × (SpatialMode M → ℝ) =>
        F (t + q.2) * F (t + q.1)) (γ.prod γ) := by
    intro t
    have h2 : Measurable fun q : (SpatialMode M → ℝ) × (SpatialMode M → ℝ) =>
        F (t + q.2) := hF.comp (by fun_prop)
    have h1 : Measurable fun q : (SpatialMode M → ℝ) × (SpatialMode M → ℝ) =>
        F (t + q.1) := hF.comp (by fun_prop)
    exact (h2.mul h1).aestronglyMeasurable
  have hinner : ∀ t : SpatialMode M → ℝ,
      (∫ q : (SpatialMode M → ℝ) × (SpatialMode M → ℝ), F (t + q.2) * F (t + q.1)
        ∂(γ.prod γ)) = S t * S t := by
    intro t
    have hswap : (∫ q : (SpatialMode M → ℝ) × (SpatialMode M → ℝ),
        F (t + q.2) * F (t + q.1) ∂(γ.prod γ))
        = ∫ q : (SpatialMode M → ℝ) × (SpatialMode M → ℝ),
            F (t + q.1) * F (t + q.2) ∂(γ.prod γ) := by
      refine integral_congr_ae (ae_of_all _ fun q => ?_)
      ring
    have hsplit : (∫ q : (SpatialMode M → ℝ) × (SpatialMode M → ℝ),
        F (t + q.1) * F (t + q.2) ∂(γ.prod γ))
        = (∫ x : SpatialMode M → ℝ, F (t + x) ∂γ)
          * (∫ y : SpatialMode M → ℝ, F (t + y) ∂γ) := by
      have h := integral_prod_mul (μ := γ) (ν := γ) (L := ℝ)
        (f := fun x : SpatialMode M → ℝ => F (t + x))
        (g := fun y : SpatialMode M → ℝ => F (t + y))
      simpa using h
    rw [hswap, hsplit, hS]
  have htriple : Integrable (fun p : (SpatialMode M → ℝ) ×
      ((SpatialMode M → ℝ) × (SpatialMode M → ℝ)) =>
      F (p.1 + p.2.2) * F (p.1 + p.2.1)) (ν.prod (γ.prod γ)) := by
    refine Integrable.of_bound ?_ (C * C) ?_
    · have h2 : Measurable fun p : (SpatialMode M → ℝ) ×
          ((SpatialMode M → ℝ) × (SpatialMode M → ℝ)) => F (p.1 + p.2.2) :=
        hF.comp (by fun_prop)
      have h1 : Measurable fun p : (SpatialMode M → ℝ) ×
          ((SpatialMode M → ℝ) × (SpatialMode M → ℝ)) => F (p.1 + p.2.1) :=
        hF.comp (by fun_prop)
      exact (h2.mul h1).aestronglyMeasurable
    · filter_upwards with p
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hC _) (hC _) (abs_nonneg _) hC0
  have hofz : AEStronglyMeasurable (fun z : (SpatialMode M → ℝ) × (SpatialMode M → ℝ) =>
      F z.2 * F z.1) (kernelLaw m0) :=
    Measurable.aestronglyMeasurable ((hF.comp measurable_snd).mul (hF.comp measurable_fst))
  unfold kernelLaw
  rw [integral_map measurable_kernelMap.aemeasurable hofz]
  have hstep : (∫ p : (SpatialMode M → ℝ) ×
      ((SpatialMode M → ℝ) × (SpatialMode M → ℝ)),
      (fun z : (SpatialMode M → ℝ) × (SpatialMode M → ℝ) => F z.2 * F z.1)
        (kernelMap p) ∂(ν.prod (γ.prod γ)))
      = ∫ p : (SpatialMode M → ℝ) × ((SpatialMode M → ℝ) × (SpatialMode M → ℝ)),
          F (p.1 + p.2.2) * F (p.1 + p.2.1) ∂(ν.prod (γ.prod γ)) := by
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    rfl
  have htriple_eq : (∫ p : (SpatialMode M → ℝ) ×
      ((SpatialMode M → ℝ) × (SpatialMode M → ℝ)),
      F (p.1 + p.2.2) * F (p.1 + p.2.1) ∂(ν.prod (γ.prod γ)))
      = ∫ t : SpatialMode M → ℝ, ∫ q : (SpatialMode M → ℝ) × (SpatialMode M → ℝ),
          F (t + q.2) * F (t + q.1) ∂(γ.prod γ) ∂ν :=
    integral_prod _ htriple
  rw [hstep, htriple_eq]
  refine integral_nonneg fun t => ?_
  rw [hinner t]
  exact mul_self_nonneg _

/-- **The all-degree lift for observables with an integrable OS form.**

Same conclusion as `kernelLaw_reflectionPositive`, with the boundedness hypothesis replaced
by integrability of the OS integrand over the boundary/noise factorization.  This is the
form that covers an **unbounded polynomial cylinder**: `P (T + X) * P (T + Y)` is a
polynomial in Gaussian variables, hence integrable; that moment input is what this
statement consumes.  The inequality itself is proved, not assumed. -/
theorem kernelLaw_reflectionPositive_of_integrable (m0 : ℝ)
    (F : (SpatialMode M → ℝ) → ℝ) (hF : Measurable F)
    (hInt : Integrable (fun p : (SpatialMode M → ℝ) ×
      ((SpatialMode M → ℝ) × (SpatialMode M → ℝ)) =>
        F (p.1 + p.2.2) * F (p.1 + p.2.1))
        ((shiftLaw m0).prod ((noiseLaw m0).prod (noiseLaw m0)))) :
    0 ≤ ∫ z : (SpatialMode M → ℝ) × (SpatialMode M → ℝ), F z.2 * F z.1
      ∂(kernelLaw m0) := by
  classical
  have hofz : AEStronglyMeasurable (fun z : (SpatialMode M → ℝ) × (SpatialMode M → ℝ) =>
      F z.2 * F z.1) (kernelLaw m0) :=
    Measurable.aestronglyMeasurable ((hF.comp measurable_snd).mul (hF.comp measurable_fst))
  unfold kernelLaw
  rw [integral_map measurable_kernelMap.aemeasurable hofz]
  have hstep : (∫ p : (SpatialMode M → ℝ) ×
      ((SpatialMode M → ℝ) × (SpatialMode M → ℝ)),
      (fun z : (SpatialMode M → ℝ) × (SpatialMode M → ℝ) => F z.2 * F z.1)
        (kernelMap p) ∂((shiftLaw m0).prod ((noiseLaw m0).prod (noiseLaw m0))))
      = ∫ p : (SpatialMode M → ℝ) × ((SpatialMode M → ℝ) × (SpatialMode M → ℝ)),
          F (p.1 + p.2.2) * F (p.1 + p.2.1)
            ∂((shiftLaw m0).prod ((noiseLaw m0).prod (noiseLaw m0))) := by
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    rfl
  rw [hstep, integral_prod _ hInt]
  refine integral_nonneg fun t => ?_
  have hcomm : (∫ q : (SpatialMode M → ℝ) × (SpatialMode M → ℝ),
      F (t + q.2) * F (t + q.1) ∂((noiseLaw m0).prod (noiseLaw m0)))
      = ∫ q : (SpatialMode M → ℝ) × (SpatialMode M → ℝ),
          F (t + q.1) * F (t + q.2) ∂((noiseLaw m0).prod (noiseLaw m0)) := by
    refine integral_congr_ae (ae_of_all _ fun q => ?_)
    ring
  rw [hcomm, integral_prod_mul (μ := noiseLaw m0) (ν := noiseLaw m0)
    (f := fun x : SpatialMode M → ℝ => F (t + x)) (g := fun x : SpatialMode M → ℝ => F (t + x))]
  exact mul_self_nonneg _

/-! ## 4. The slice coordinates and their covariance -/

/-- The `t = 0` slice of a Mehler configuration: `x₀ k = (y₊ k − y₋ k)/√2`. -/
def timeZero (y : MehlerMode M → ℝ) : SpatialMode M → ℝ :=
  fun k => (y (true, k) - y (false, k)) / Real.sqrt 2

/-- The `t = 1` slice of a Mehler configuration: `x₁ k = (y₊ k + y₋ k)/√2`. -/
def timeOne (y : MehlerMode M → ℝ) : SpatialMode M → ℝ :=
  fun k => (y (true, k) + y (false, k)) / Real.sqrt 2

/-- **The Mehler reflection swaps the two slices**: `x₀ (θ y) = x₁ y`. -/
theorem timeZero_reflect (y : MehlerMode M → ℝ) :
    timeZero (reflectMehler y) = timeOne y := by
  funext k
  unfold timeZero timeOne reflectMehler
  simp

/-- **The Mehler reflection swaps the two slices**: `x₁ (θ y) = x₀ y`. -/
theorem timeOne_reflect (y : MehlerMode M → ℝ) :
    timeOne (reflectMehler y) = timeZero y := by
  funext k
  unfold timeOne timeZero reflectMehler
  simp
  ring

/-- **The boundary/noise variances add up to the C1 slice variance.**  The kernel state's
one-slice variance is `A k = shiftVariance + noiseVariance = (v₊ k + v₋ k)/2`, which is
exactly the variance of the slice `x₁ k = (y₊ k + y₋ k)/√2` in the Mehler law (the two
parities are independent there).  The cross-covariance is `shiftVariance = (v₊ − v₋)/2`,
the C1 value `E[x₁ k x₀ k]`.  So the mixture has the same two-point function as the Mehler
control. -/
theorem sliceVariance_eq (m0 : ℝ) (k : SpatialMode M) :
    shiftVariance m0 k + noiseVariance m0 k
      = (variance m0 (true, k) + variance m0 (false, k)) / 2 := by
  unfold shiftVariance noiseVariance
  ring_nf

end BookProof.OSReconstruction
