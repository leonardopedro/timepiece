import Mathlib
import BookProof.OSReconstruction.HalfSpaceCovariantReflectionPositivity

/-!
# The interacting half-space inequality for a factorized interaction

Plan: `cftproof.md`, **C2 / E3**.  `HalfSpaceCovariantReflectionPositivity` proves the OS
inequality for the (possibly coupled) free state `covState ν`: for a bounded measurable
observable `F` of one half,

  `0 ≤ ∫ z, F z.2 * F z.1 ∂covState ν`.

The *interacting* half-space inequality asks the same of a state that is no longer Gaussian.  The
one class of interactions where this is a theorem with no approximation at all is the one where the
Boltzmann weight **factorizes across the reflection plane**:

  `ρ(z) = g z₁ * g z₂`,   `g ≥ 0` a positive-time weight,

which is the lattice form of `e^{-V}` with `V = V₊ + θV₊` — an interaction built from positive-time
fields plus its reflection, the Dyson–Lieb–Simon class.  Then the interacting OS form *is* a free OS
form with `F` replaced by `F · g`:

  `⟨θF F⟩_int = ∫ θF F · g₁ g₂ ∂μ₀ = ∫ θ(F g) (F g) ∂μ₀ ≥ 0`.

No expansion, no cluster expansion and no cutoff removal is involved: the positivity is inherited
from the free state, and the interaction only has to *factorize*, not to be small.

## Boundary

* The interaction is a **positive-time weight** `g` on the free state, not a Gibbs measure of
  independent interest: `g = e^{-V₊}` is the intended reading, but nothing here constructs the
  pressure, the thermodynamic limit or a transfer operator.
* `g` is bounded and measurable, and `F` is a bounded cylinder observable of one half.  The `L²`
  closure of the positive-time algebra and an unbounded `V₊` are not covered.
* A general reflection-invariant positive density does **not** preserve reflection positivity;
  the factorization is what the proof uses, and no converse is claimed.
-/

namespace BookProof.OSReconstruction

open MeasureTheory ProbabilityTheory

open scoped NNReal ENNReal

noncomputable section

/-! ## The factorized interaction -/

/-- The interaction weight `ρ(z) = g z₁ * g z₂`: one positive-time factor on each half. -/
def intWeight {ι : Type*} (g : (ι → ℝ) → ℝ≥0) : ((ι → ℝ) × (ι → ℝ)) → ℝ≥0 :=
  fun z => g z.1 * g z.2

theorem measurable_intWeight {ι : Type*} {g : (ι → ℝ) → ℝ≥0} (hg : Measurable g) :
    Measurable (intWeight g) := by
  unfold intWeight
  exact (hg.comp measurable_fst).mul (hg.comp measurable_snd)

/-- **The interacting state**: the covariant state reweighted by the factorized interaction. -/
def intState {ι : Type*} [Fintype ι] (ν : Measure (ι → ℝ)) (g : (ι → ℝ) → ℝ≥0) :
    Measure ((ι → ℝ) × (ι → ℝ)) :=
  (covState ν).withDensity (fun z => (intWeight g z : ℝ≥0∞))

/-- The interacting state is not a probability measure in general: its mass is is `∫ ρ`. -/
theorem intState_univ {ι : Type*} [Fintype ι] (ν : Measure (ι → ℝ)) [IsProbabilityMeasure ν]
    (g : (ι → ℝ) → ℝ≥0) :
    intState ν g Set.univ = ∫⁻ z, (intWeight g z : ℝ≥0∞) ∂covState ν := by
  unfold intState
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]

/-! ## The inequality -/

/-- **Interacting half-space reflection positivity.**  If the interaction factorizes as
`g z₁ * g z₂` with a bounded measurable nonnegative `g`, then the reflected OS form of the
interacting state is nonnegative for every bounded cylinder observable of one half.

This is the Dyson–Lieb–Simon mechanism: the weight splits into a factor on each half, each factor
joins the observable on its own side, and the free reflection positivity of
`covState_reflectionPositive` finishes the proof. -/
theorem intState_reflectionPositive {ι : Type*} [Fintype ι] (ν : Measure (ι → ℝ))
    [IsProbabilityMeasure ν] (g : (ι → ℝ) → ℝ≥0) (hg : Measurable g)
    (F : (ι → ℝ) → ℝ) (hF : Measurable F)
    (C D : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, |F x| ≤ C) (hD0 : 0 ≤ D) (hD : ∀ x, (g x : ℝ) ≤ D) :
    0 ≤ ∫ z : (ι → ℝ) × (ι → ℝ), F z.2 * F z.1 ∂intState ν g := by
  classical
  have hgR : Measurable fun x : ι → ℝ => (g x : ℝ) := hg.coe_nnreal_real
  unfold intState
  rw [integral_withDensity_eq_integral_smul (measurable_intWeight hg)]
  have hfree := covState_reflectionPositive (ν := ν) (fun x => F x * (g x : ℝ))
    (hF.mul hgR) (C * D) (mul_nonneg hC0 hD0) (by
      intro x
      rw [abs_mul, abs_of_nonneg (NNReal.coe_nonneg (g x))]
      exact mul_le_mul (hC x) (hD x) (NNReal.coe_nonneg (g x)) hC0)
  have hEq : (∫ z : (ι → ℝ) × (ι → ℝ),
        intWeight g z • (F z.2 * F z.1) ∂covState ν)
      = ∫ z : (ι → ℝ) × (ι → ℝ),
        (F z.2 * (g z.2 : ℝ)) * (F z.1 * (g z.1 : ℝ)) ∂covState ν := by
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [intWeight, NNReal.smul_def, smul_eq_mul, NNReal.coe_mul]
    ring
  rw [hEq]
  exact hfree

/-- The interacting OS expectation: the normalized form, which is what "the interacting state" means
when the weight is not normalized.  Division by the mass preserves sign, so this is a corollary. -/
theorem intState_expectation_re_nonneg {ι : Type*} [Fintype ι] (ν : Measure (ι → ℝ))
    [IsProbabilityMeasure ν] (g : (ι → ℝ) → ℝ≥0) (hg : Measurable g)
    (F : (ι → ℝ) → ℝ) (hF : Measurable F)
    (C D : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, |F x| ≤ C) (hD0 : 0 ≤ D) (hD : ∀ x, (g x : ℝ) ≤ D)
    (hmass : (0 : ℝ) < ∫ _ : (ι → ℝ) × (ι → ℝ), (1 : ℝ) ∂intState ν g) :
    0 ≤ (∫ z : (ι → ℝ) × (ι → ℝ), F z.2 * F z.1 ∂intState ν g) /
      (∫ _ : (ι → ℝ) × (ι → ℝ), (1 : ℝ) ∂intState ν g) :=
  div_nonneg
    (intState_reflectionPositive ν g hg F hF C D hC0 hC hD0 hD) (le_of_lt hmass)

/-! ## The interaction as a convergent expansion

The factorized weight is a single term, and nothing in the proof above uses that there is only
one: a nonnegative *series* of factorized weights is reflection positive term by term, so the OS
form of the whole series is a sum of nonnegative terms.  That matters because the series can have
a density

  `ρ(z) = ∑' i, g i z.1 * g i z.2`

that is **unbounded** while every term `g i` is bounded — an unbounded `V₊` written as a sum of
bounded pieces.  The mechanism is the same mean of squares, taken over the mixture index and the
shared shift together; only integrability of the total form has to be assumed, and the summability
hypothesis below is exactly what makes it hold.
-/

/-- **The expansion state**: the sum of the term states, i.e. the state of the density
`ρ(z) = ∑' i, g i z.1 * g i z.2`.  It is a mixture, not a probability: its mass is `∑' i, ∫ ρᵢ`. -/
def intStateSum {ι : Type*} [Fintype ι] (ν : Measure (ι → ℝ)) (g : ℕ → (ι → ℝ) → ℝ≥0) :
    Measure ((ι → ℝ) × (ι → ℝ)) :=
  Measure.sum fun i => intState ν (g i)

/-- The total mass of the expansion state: the series of the term masses. -/
theorem intStateSum_univ {ι : Type*} [Fintype ι] (ν : Measure (ι → ℝ))
    (g : ℕ → (ι → ℝ) → ℝ≥0) :
    intStateSum ν g Set.univ = ∑' i, intState ν (g i) Set.univ := by
  unfold intStateSum
  exact Measure.sum_apply _ MeasurableSet.univ

/-- **Reflection positivity of a convergent expansion of the interaction.**

Every term is a bounded factorized weight, hence reflection positive by
`intState_reflectionPositive`; the OS form of the series is the series of the forms, and a series
of nonnegative terms is nonnegative.  The density of `intStateSum` need not be bounded (`D` may be
unbounded), so this is a strictly wider class of interactions than a single `ρ = g₁ g₂`. -/
theorem intStateSum_reflectionPositive {ι : Type*} [Fintype ι] (ν : Measure (ι → ℝ))
    [IsProbabilityMeasure ν] (g : ℕ → (ι → ℝ) → ℝ≥0) (hg : ∀ i, Measurable (g i))
    (F : (ι → ℝ) → ℝ) (hF : Measurable F) (C : ℝ) (hC0 : 0 ≤ C) (hC : ∀ x, |F x| ≤ C)
    (D : ℕ → ℝ) (hD0 : ∀ i, 0 ≤ D i) (hD : ∀ i x, (g i x : ℝ) ≤ D i)
    (hsum : Summable fun i => C ^ 2 * (D i) ^ 2) :
    0 ≤ ∫ z : (ι → ℝ) × (ι → ℝ), F z.2 * F z.1 ∂intStateSum ν g := by
  classical
  set μ : ℕ → Measure ((ι → ℝ) × (ι → ℝ)) := fun i => intState ν (g i) with hμ
  set f : (ι → ℝ) × (ι → ℝ) → ℝ := fun z => F z.2 * F z.1 with hf
  have hfmeas : Measurable f := (hF.comp measurable_snd).mul (hF.comp measurable_fst)
  -- each term is a finite measure whose mass is bounded by `Dᵢ²`
  have hmass : ∀ i, μ i Set.univ ≤ ENNReal.ofReal ((D i) ^ 2) := by
    intro i
    rw [hμ, intState_univ]
    calc ∫⁻ z, (intWeight (g i) z : ℝ≥0∞) ∂covState ν
        ≤ ∫⁻ _, ENNReal.ofReal ((D i) ^ 2) ∂covState ν := by
          refine lintegral_mono fun z => ?_
          rw [← ENNReal.ofReal_coe_nnreal, intWeight]
          refine ENNReal.ofReal_le_ofReal ?_
          have h1 : (g i z.1 : ℝ) ≤ D i := hD i z.1
          have h2 : (g i z.2 : ℝ) ≤ D i := hD i z.2
          have h1' : (0 : ℝ) ≤ (g i z.1 : ℝ) := NNReal.coe_nonneg _
          have h2' : (0 : ℝ) ≤ (g i z.2 : ℝ) := NNReal.coe_nonneg _
          calc (g i z.1 : ℝ) * (g i z.2 : ℝ) ≤ (D i) * (D i) :=
                mul_le_mul h1 h2 h2' (hD0 i)
            _ = (D i) ^ 2 := by ring
      _ = ENNReal.ofReal ((D i) ^ 2) * (covState ν) Set.univ := lintegral_const _
      _ = ENNReal.ofReal ((D i) ^ 2) := by rw [measure_univ, mul_one]
  -- the integrand is bounded by `C²`, so each term contributes at most `C² Dᵢ²`
  have hterm : ∀ i, ∫⁻ z, ENNReal.ofReal ‖f z‖ ∂μ i ≤ ENNReal.ofReal (C ^ 2 * (D i) ^ 2) := by
    intro i
    calc ∫⁻ z, ENNReal.ofReal ‖f z‖ ∂μ i
        ≤ ∫⁻ _, ENNReal.ofReal (C * C) ∂μ i := by
          refine lintegral_mono fun z => ?_
          refine ENNReal.ofReal_le_ofReal ?_
          rw [hf]
          simp only
          rw [Real.norm_eq_abs, abs_mul]
          exact mul_le_mul (hC _) (hC _) (abs_nonneg _) hC0
      _ = ENNReal.ofReal (C * C) * μ i Set.univ := lintegral_const _
      _ ≤ ENNReal.ofReal (C * C) * ENNReal.ofReal ((D i) ^ 2) := by
          exact mul_le_mul_of_nonneg_left (hmass i) (zero_le _)
      _ = ENNReal.ofReal (C ^ 2 * (D i) ^ 2) := by
          rw [← ENNReal.ofReal_mul (by positivity)]
          ring_nf
  have hlt : ∫⁻ z, ENNReal.ofReal ‖f z‖ ∂intStateSum ν g < ⊤ := by
    have hsum' : ∑' i, (∫⁻ z, ENNReal.ofReal ‖f z‖ ∂μ i) < ⊤ := by
      calc ∑' i, (∫⁻ z, ENNReal.ofReal ‖f z‖ ∂μ i)
          ≤ ∑' i, ENNReal.ofReal (C ^ 2 * (D i) ^ 2) := ENNReal.tsum_le_tsum hterm
        _ = ENNReal.ofReal (∑' i, C ^ 2 * (D i) ^ 2) :=
            (ENNReal.ofReal_tsum_of_nonneg (fun i => by positivity) hsum).symm
        _ < ⊤ := ENNReal.ofReal_lt_top
    rw [show intStateSum ν g = Measure.sum μ from rfl, lintegral_sum_measure]
    exact hsum'
  have hint : Integrable f (intStateSum ν g) := by
    refine ⟨hfmeas.aestronglyMeasurable, ?_⟩
    rw [HasFiniteIntegral]
    simp_rw [← ofReal_norm_eq_enorm]
    exact hlt
  rw [show intStateSum ν g = Measure.sum μ from rfl, integral_sum_measure hint]
  refine tsum_nonneg fun i => ?_
  exact intState_reflectionPositive ν (g i) (hg i) F hF C (D i) hC0 hC (hD0 i) (hD i)

end

end BookProof.OSReconstruction
