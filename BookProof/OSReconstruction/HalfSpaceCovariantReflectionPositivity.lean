import Mathlib
import BookProof.OSReconstruction.HalfSpaceChainCovariance

/-!
# Reflection positivity for a covariant (non-diagonal) free-field state

Plan: `cftproof.md`, **E3**.  `HalfSpaceInfiniteVolumePositivity` proves OS positivity for the
*product* free-field state, whose covariance is the identity.  The free field proper has the
non-diagonal covariance `(−Δ+m²)⁻¹`; a banded truncation of it is built in
`HalfSpaceChainCovariance`.  This module proves reflection positivity for a state that is genuinely
*covariant* — its two halves are coupled — rather than a product of independent halves.

## The construction

Fix a probability law `ν` on `ι → ℝ` (a random *shift* `T`), let `γ` be `n`-site white noise, and
take `X`, `Y` independent copies of `γ`, independent of `T`.  The state is the law of the pair

  `(T + X, T + Y)`.

Both halves share the shift `T`, so the coupling map `covMap` mixes `T` into *both* halves; for a
nondegenerate `T` the state is not a product of its two marginals (for `T = 0` it is).  Reflection
invariance holds by construction (the two halves have the same law).  The covariance of the state is
`[[Cov T + 1, Cov T], [Cov T, Cov T + 1]]`: the off-diagonal block `Cov T` is banded whenever `T` is
a banded image of white noise, the class built in `HalfSpaceChainCovariance`.

## The theorem

`covState_reflectionPositive` : for a measurable bounded observable `F` of one half,

  `0 ≤ ∫ z, F z.2 * F z.1 ∂(covState ν)`

Proof: conditioning on `T = t` makes the halves independent, so the OS form is the `ν`-average of
`(∫ F (t + x) ∂γ)²`, a mean of squares.  This is the covariance version of the classical
"mixture of product states is reflection positive" argument.

## Boundary

* Reflection positivity is proved for *cylinder* observables of one half (`F` bounded measurable).
  Extending to the `L²` closure of `𝔄₊` needs the OS form on the Lebesgue space, not built here.
* The state is a *mixture* of product states.  Its halves are coupled, but the "transfer operator"
  is the mixture average, not a genuine interacting dynamics.
* The covariance matrix `[[Cov T + 1, Cov T], [Cov T, Cov T + 1]]` is now proved as a theorem about
  `covState` in `HalfSpaceCovStateCovariance` (`covState_cov_fst_fst`, `covState_cov_snd_snd`,
  `covState_cov_fst_snd`); the banded instantiations are `covState_chainLaw_cov_fst_snd` and
  `covState_bandLaw_cov_fst_snd`.
-/

namespace BookProof.OSReconstruction

open MeasureTheory ProbabilityTheory

noncomputable section

/-! ## The shared-shift state -/

/-- The coupling map `(T, X, Y) ↦ (T + X, T + Y)`. -/
def covMap {ι : Type*} (p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ))) : (ι → ℝ) × (ι → ℝ) :=
  (p.1 + p.2.1, p.1 + p.2.2)

theorem measurable_covMap {ι : Type*} : Measurable (covMap (ι := ι)) := by
  unfold covMap
  fun_prop

/-- **The covariant state**: two white-noise halves shifted by a common random vector `T`. -/
def covState {ι : Type*} [Fintype ι] (ν : Measure (ι → ℝ)) : Measure ((ι → ℝ) × (ι → ℝ)) :=
  (ν.prod ((whiteNoise ι).prod (whiteNoise ι))).map (covMap (ι := ι))

instance covState_isProbability {ι : Type*} [Fintype ι] (ν : Measure (ι → ℝ))
    [IsProbabilityMeasure ν] : IsProbabilityMeasure (covState ν) := by
  unfold covState
  exact Measure.isProbabilityMeasure_map (measurable_covMap (ι := ι)).aemeasurable

/-- **Reflection positivity of the covariant state.**  The observable depends on one half only; the
reflection swaps the halves.  Conditioning on the shared shift makes the halves independent, so the
OS form is an average of squares. -/
theorem covState_reflectionPositive {ι : Type*} [Fintype ι] (ν : Measure (ι → ℝ))
    [IsProbabilityMeasure ν] (F : (ι → ℝ) → ℝ) (hF : Measurable F) (C : ℝ)
    (hC0 : 0 ≤ C) (hC : ∀ x, |F x| ≤ C) :
    0 ≤ ∫ z : (ι → ℝ) × (ι → ℝ), F z.2 * F z.1 ∂covState ν := by
  classical
  set γ := whiteNoise ι with hγ
  set S : (ι → ℝ) → ℝ := fun t => ∫ x, F (t + x) ∂γ with hS
  -- the two halves, read on the noise, are bounded hence integrable
  have hbound : ∀ t : ι → ℝ, ∀ᵐ q ∂(γ.prod γ), ‖F (t + q.2) * F (t + q.1)‖ ≤ C * C := by
    intro t
    filter_upwards with q
    rw [Real.norm_eq_abs, abs_mul]
    exact mul_le_mul (hC _) (hC _) (abs_nonneg _) hC0
  have hmeas_inner : ∀ t : ι → ℝ, AEStronglyMeasurable
      (fun q : (ι → ℝ) × (ι → ℝ) => F (t + q.2) * F (t + q.1)) (γ.prod γ) := by
    intro t
    have h2 : Measurable fun q : (ι → ℝ) × (ι → ℝ) => F (t + q.2) := hF.comp (by fun_prop)
    have h1 : Measurable fun q : (ι → ℝ) × (ι → ℝ) => F (t + q.1) := hF.comp (by fun_prop)
    exact (h2.mul h1).aestronglyMeasurable
  have hinner : ∀ t : ι → ℝ,
      (∫ q : (ι → ℝ) × (ι → ℝ), F (t + q.2) * F (t + q.1) ∂(γ.prod γ)) = S t * S t := by
    intro t
    have hswap : (∫ q : (ι → ℝ) × (ι → ℝ), F (t + q.2) * F (t + q.1) ∂(γ.prod γ))
        = ∫ q : (ι → ℝ) × (ι → ℝ), F (t + q.1) * F (t + q.2) ∂(γ.prod γ) := by
      refine integral_congr_ae (ae_of_all _ fun q => ?_)
      ring
    have hsplit : (∫ q : (ι → ℝ) × (ι → ℝ), F (t + q.1) * F (t + q.2) ∂(γ.prod γ))
        = (∫ x : ι → ℝ, F (t + x) ∂γ) * (∫ y : ι → ℝ, F (t + y) ∂γ) := by
      have h := integral_prod_mul (μ := γ) (ν := γ) (L := ℝ)
        (f := fun x : ι → ℝ => F (t + x)) (g := fun y : ι → ℝ => F (t + y))
      simpa using h
    rw [hswap, hsplit, hS]
  have htriple : Integrable (fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) =>
      F (p.1 + p.2.2) * F (p.1 + p.2.1)) (ν.prod (γ.prod γ)) := by
    refine Integrable.of_bound ?_ (C * C) ?_
    · have h2 : Measurable fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => F (p.1 + p.2.2) :=
        hF.comp (by fun_prop)
      have h1 : Measurable fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => F (p.1 + p.2.1) :=
        hF.comp (by fun_prop)
      exact (h2.mul h1).aestronglyMeasurable
    · filter_upwards with p
      rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hC _) (hC _) (abs_nonneg _) hC0
  have hofz : AEStronglyMeasurable (fun z : (ι → ℝ) × (ι → ℝ) => F z.2 * F z.1) (covState ν) :=
    Measurable.aestronglyMeasurable ((hF.comp measurable_snd).mul (hF.comp measurable_fst))
  rw [covState, integral_map measurable_covMap.aemeasurable hofz]
  have hstep : (∫ p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)),
      (fun z : (ι → ℝ) × (ι → ℝ) => F z.2 * F z.1) (covMap p) ∂(ν.prod (γ.prod γ)))
      = ∫ p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)),
          F (p.1 + p.2.2) * F (p.1 + p.2.1) ∂(ν.prod (γ.prod γ)) := by
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    rfl
  have htriple_eq : (∫ p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)),
      F (p.1 + p.2.2) * F (p.1 + p.2.1) ∂(ν.prod (γ.prod γ)))
      = ∫ t : ι → ℝ, ∫ q : (ι → ℝ) × (ι → ℝ),
          F (t + q.2) * F (t + q.1) ∂(γ.prod γ) ∂ν :=
    integral_prod _ htriple
  rw [hstep, htriple_eq]
  refine integral_nonneg fun t => ?_
  rw [hinner t]
  exact mul_self_nonneg _

end

end BookProof.OSReconstruction
