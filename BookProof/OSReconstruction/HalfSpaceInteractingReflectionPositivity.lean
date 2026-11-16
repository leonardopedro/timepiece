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
fields plus its reflection, the Dyson–Lieb–Simon class.  Then the interacting OS form *is* a
free OS form with `F` replaced by `F · g`:

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

/-- The interacting OS expectation: the normalized form, the meaning of "the interacting state"
when the weight is not normalized.  Division by the mass preserves sign, so this is a
corollary. -/
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

/-! ## The `L²`-free statement: only finiteness of the form is needed

In the free theorem the observable is bounded, and that bound is used for exactly one thing:
integrability of the triple product whose iterated integral is the OS form.  Nothing else.  So the
hypothesis can be stated as what it really is — *the OS form is finite* — and the statement then
covers unbounded observables: the mean-of-squares representation `⟨θH H⟩ = ∫ (S_t H)² dν` is
unchanged, and only `Integrable` has to be supplied.  This is the form the `L²` closure of the
positive-time algebra needs; the remaining gap to a closure statement is the bounded-truncation
argument that would discharge the hypothesis from `MemLp`, not a change of mechanism.
-/

/-- **Reflection positivity of the covariant state for a form-finite observable.**  `H` need not
be bounded: it is enough that the OS form's triple integral exists. -/
theorem covState_reflectionPositive_of_integrable {ι : Type*} [Fintype ι]
    (ν : Measure (ι → ℝ)) [IsProbabilityMeasure ν] (H : (ι → ℝ) → ℝ) (hH : Measurable H)
    (hint : Integrable (fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) =>
      H (p.1 + p.2.2) * H (p.1 + p.2.1))
      (ν.prod ((whiteNoise ι).prod (whiteNoise ι)))) :
    0 ≤ ∫ z : (ι → ℝ) × (ι → ℝ), H z.2 * H z.1 ∂covState ν := by
  classical
  set γ := whiteNoise ι with hγ
  set S : (ι → ℝ) → ℝ := fun t => ∫ x, H (t + x) ∂γ with hS
  have hinner : ∀ t : ι → ℝ,
      (∫ q : (ι → ℝ) × (ι → ℝ), H (t + q.2) * H (t + q.1) ∂(γ.prod γ)) = S t * S t := by
    intro t
    have hswap : (∫ q : (ι → ℝ) × (ι → ℝ), H (t + q.2) * H (t + q.1) ∂(γ.prod γ))
        = ∫ q : (ι → ℝ) × (ι → ℝ), H (t + q.1) * H (t + q.2) ∂(γ.prod γ) := by
      refine integral_congr_ae (ae_of_all _ fun q => ?_)
      ring
    have hsplit : (∫ q : (ι → ℝ) × (ι → ℝ), H (t + q.1) * H (t + q.2) ∂(γ.prod γ))
        = (∫ x : ι → ℝ, H (t + x) ∂γ) * (∫ y : ι → ℝ, H (t + y) ∂γ) := by
      have h := integral_prod_mul (μ := γ) (ν := γ) (L := ℝ)
        (f := fun x : ι → ℝ => H (t + x)) (g := fun y : ι → ℝ => H (t + y))
      simpa using h
    rw [hswap, hsplit, hS]
  have hofz : AEStronglyMeasurable (fun z : (ι → ℝ) × (ι → ℝ) => H z.2 * H z.1) (covState ν) :=
    Measurable.aestronglyMeasurable ((hH.comp measurable_snd).mul (hH.comp measurable_fst))
  rw [covState, integral_map measurable_covMap.aemeasurable hofz]
  have hstep : (∫ p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)),
      (fun z : (ι → ℝ) × (ι → ℝ) => H z.2 * H z.1) (covMap p) ∂(ν.prod (γ.prod γ)))
      = ∫ p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)),
          H (p.1 + p.2.2) * H (p.1 + p.2.1) ∂(ν.prod (γ.prod γ)) := by
    refine integral_congr_ae (ae_of_all _ fun p => ?_)
    rfl
  rw [hstep, integral_prod _ hint]
  refine integral_nonneg fun t => ?_
  rw [hinner t]
  exact mul_self_nonneg _

/-! ## The marginal lift: `MemLp` on `ν ⊗ γ` transfers to `ν ⊗ γ ⊗ γ`

The two halves of the OS form are integrals against *shifted* copies of the same Gaussian, so the
`L²` hypothesis naturally lives on `ν ⊗ γ`, while the form's integrand lives on `ν ⊗ (γ ⊗ γ)`.
The bridge is that each projection `(t, x, y) ↦ (t, x)` and `(t, x, y) ↦ (t, y)` pushes the triple
product *down* to `ν ⊗ γ`: both are `Prod.map id Prod.fst` and `Prod.map id Prod.snd`, so
`Measure.map_prod_map` reduces each to the marginal law of a single Gaussian, and that marginal is
`γ` itself because `γ` is a probability.  With the lift in hand, Hölder
(`MemLp.integrable_mul`) produces exactly the integrability the form-finiteness theorem asks for.
-/

/-- **The projection `(t, x, y) ↦ (t, x)` is measure preserving** from `ν ⊗ (γ ⊗ γ)` to `ν ⊗ γ`. -/
theorem measurePreserving_covMarginal_left {ι : Type*} [Fintype ι]
    (ν : Measure (ι → ℝ)) [SFinite ν] :
    MeasurePreserving (fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => (p.1, p.2.1))
      (ν.prod ((whiteNoise ι).prod (whiteNoise ι))) (ν.prod (whiteNoise ι)) := by
  refine ⟨by fun_prop, ?_⟩
  have h := Measure.map_prod_map (μa := ν) (μc := (whiteNoise ι).prod (whiteNoise ι))
    (f := id) (g := Prod.fst) measurable_id measurable_fst
  simp only [Measure.map_id, Measure.map_fst_prod, measure_univ, one_smul] at h
  simpa [Prod.map] using h.symm

/-- **The projection `(t, x, y) ↦ (t, y)` is measure preserving** from `ν ⊗ (γ ⊗ γ)` to `ν ⊗ γ`. -/
theorem measurePreserving_covMarginal_right {ι : Type*} [Fintype ι]
    (ν : Measure (ι → ℝ)) [SFinite ν] :
    MeasurePreserving (fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => (p.1, p.2.2))
      (ν.prod ((whiteNoise ι).prod (whiteNoise ι))) (ν.prod (whiteNoise ι)) := by
  refine ⟨by fun_prop, ?_⟩
  have h := Measure.map_prod_map (μa := ν) (μc := (whiteNoise ι).prod (whiteNoise ι))
    (f := id) (g := Prod.snd) measurable_id measurable_snd
  simp only [Measure.map_id, Measure.map_snd_prod, measure_univ, one_smul] at h
  simpa [Prod.map] using h.symm

/-- **Reflection positivity of the covariant state from an `L²` hypothesis.**

The only hypothesis on the observable is that the shift-averaged field is square integrable on
`ν ⊗ γ`; there is no bound and no separate integrability assumption.  The proof lifts the `L²`
statement to the triple product by `measurePreserving_covMarginal_left`/`_right`, multiplies the
two halves by Hölder, and hands the resulting integrability to
`covState_reflectionPositive_of_integrable`.  This closes the gap the form-finiteness statement
left open: the finiteness is *derived*, not assumed. -/
theorem covState_reflectionPositive_of_memLp {ι : Type*} [Fintype ι]
    (ν : Measure (ι → ℝ)) [IsProbabilityMeasure ν] (H : (ι → ℝ) → ℝ) (hH : Measurable H)
    (hLp : MemLp (fun q : (ι → ℝ) × (ι → ℝ) => H (q.1 + q.2)) 2
      (ν.prod (whiteNoise ι))) :
    0 ≤ ∫ z : (ι → ℝ) × (ι → ℝ), H z.2 * H z.1 ∂covState ν := by
  have hleft : MemLp (fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => H (p.1 + p.2.1)) 2
      (ν.prod ((whiteNoise ι).prod (whiteNoise ι))) := by
    have := hLp.comp_measurePreserving (measurePreserving_covMarginal_left ν)
    simpa [Function.comp_def] using this
  have hright : MemLp (fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) => H (p.1 + p.2.2)) 2
      (ν.prod ((whiteNoise ι).prod (whiteNoise ι))) := by
    have := hLp.comp_measurePreserving (measurePreserving_covMarginal_right ν)
    simpa [Function.comp_def] using this
  exact covState_reflectionPositive_of_integrable (ν := ν) H hH (hright.integrable_mul hleft)

/-- **The interacting inequality with no boundedness at all.**  A measurable nonnegative weight `g`
and a measurable observable `F`, with only the finiteness of the interacting OS form assumed (as
integrability in the state).  `g` may be unbounded and `F` unbounded. -/
theorem intState_reflectionPositive_of_integrable {ι : Type*} [Fintype ι]
    (ν : Measure (ι → ℝ)) [IsProbabilityMeasure ν] (g : (ι → ℝ) → ℝ≥0) (hg : Measurable g)
    (F : (ι → ℝ) → ℝ) (hF : Measurable F)
    (hint : Integrable (fun z : (ι → ℝ) × (ι → ℝ) =>
      F z.2 * F z.1 * (intWeight g z : ℝ)) (covState ν)) :
    0 ≤ ∫ z : (ι → ℝ) × (ι → ℝ), F z.2 * F z.1 ∂intState ν g := by
  classical
  have hgR : Measurable fun x : ι → ℝ => (g x : ℝ) := hg.coe_nnreal_real
  have hH : Measurable fun x : ι → ℝ => F x * (g x : ℝ) := hF.mul hgR
  have hform : Measurable fun z : (ι → ℝ) × (ι → ℝ) => F z.2 * F z.1 * (intWeight g z : ℝ) :=
    ((hF.comp measurable_snd).mul (hF.comp measurable_fst)).mul
      (measurable_intWeight hg).coe_nnreal_real
  -- transfer the finiteness hypothesis to the shift-averaged product
  have hprod : Integrable (fun p : (ι → ℝ) × ((ι → ℝ) × (ι → ℝ)) =>
      (F (p.1 + p.2.2) * (g (p.1 + p.2.2) : ℝ)) *
        (F (p.1 + p.2.1) * (g (p.1 + p.2.1) : ℝ)))
      (ν.prod ((whiteNoise ι).prod (whiteNoise ι))) := by
    have hiff := (integrable_map_measure
      (μ := ν.prod ((whiteNoise ι).prod (whiteNoise ι)))
      (g := fun z : (ι → ℝ) × (ι → ℝ) => F z.2 * F z.1 * (intWeight g z : ℝ))
      hform.aestronglyMeasurable measurable_covMap.aemeasurable).1
    have h := hiff hint
    refine h.congr ?_
    filter_upwards with p
    simp only [Function.comp_apply, covMap, intWeight, NNReal.coe_mul]
    ring
  have hfree := covState_reflectionPositive_of_integrable (ν := ν)
    (fun x : ι → ℝ => F x * (g x : ℝ)) hH hprod
  unfold intState
  rw [integral_withDensity_eq_integral_smul (measurable_intWeight hg)]
  have hEq : (∫ z : (ι → ℝ) × (ι → ℝ),
        intWeight g z • (F z.2 * F z.1) ∂covState ν)
      = ∫ z : (ι → ℝ) × (ι → ℝ),
        (F z.2 * (g z.2 : ℝ)) * (F z.1 * (g z.1 : ℝ)) ∂covState ν := by
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [intWeight, NNReal.smul_def, smul_eq_mul, NNReal.coe_mul]
    ring
  rw [hEq]
  exact hfree

/-- **The interacting inequality from an `L²` hypothesis on the weighted observable.**  The same
statement as `intState_reflectionPositive_of_integrable`, except that the finiteness of the
interacting OS form is not assumed: it follows from `MemLp` of `F * g` against the shift-averaged
Gaussian.  This hypothesis is strictly stronger than the integrability used in
`intState_reflectionPositive_of_integrable` -- the lift derives that integrability from it -- and
it is the form in which the interacting state inherits the marginal lift: the weight `g` rides
along with the observable because `intState` is `covState` reweighted by `g z.1 * g z.2`. -/
theorem intState_reflectionPositive_of_memLp {ι : Type*} [Fintype ι]
    (ν : Measure (ι → ℝ)) [IsProbabilityMeasure ν] (g : (ι → ℝ) → ℝ≥0) (hg : Measurable g)
    (F : (ι → ℝ) → ℝ) (hF : Measurable F)
    (hLp : MemLp (fun q : (ι → ℝ) × (ι → ℝ) => F (q.1 + q.2) * (g (q.1 + q.2) : ℝ)) 2
      (ν.prod (whiteNoise ι))) :
    0 ≤ ∫ z : (ι → ℝ) × (ι → ℝ), F z.2 * F z.1 ∂intState ν g := by
  classical
  have hgR : Measurable fun x : ι → ℝ => (g x : ℝ) := hg.coe_nnreal_real
  have hH : Measurable fun x : ι → ℝ => F x * (g x : ℝ) := hF.mul hgR
  have hfree := covState_reflectionPositive_of_memLp (ν := ν)
    (fun x : ι → ℝ => F x * (g x : ℝ)) hH hLp
  unfold intState
  rw [integral_withDensity_eq_integral_smul (measurable_intWeight hg)]
  have hEq : (∫ z : (ι → ℝ) × (ι → ℝ),
        intWeight g z • (F z.2 * F z.1) ∂covState ν)
      = ∫ z : (ι → ℝ) × (ι → ℝ),
        (F z.2 * (g z.2 : ℝ)) * (F z.1 * (g z.1 : ℝ)) ∂covState ν := by
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    simp only [intWeight, NNReal.smul_def, smul_eq_mul, NNReal.coe_mul]
    ring
  rw [hEq]
  exact hfree

/-! ## Why the hypothesis cannot be weakened to reflection invariance

The theorems above need the weight to be a nonnegative sum of matched products.  Reflection
invariance alone is not enough, and this section proves the failure instead of asserting it: for
any bounded `h` with `|h| ≤ 1` and any `0 < ε < 1`, the weight

  `W(z) = 1 - ε * h z₁ * h z₂`

is strictly positive and reflection invariant, and whenever `∫ h = 0` and `∫ h * h = 1` its OS
form on `h` is `-ε`.  The sign is the whole story — `1 + ε h₁ h₂` has OS form `+ε` — so it is the
coefficient of the rank-one term, not the invariance, that carries positivity.  This is the
precise sense in which a general reflection-invariant density is *false* rather than open.

The statement needs no Gaussian computation: it holds for any probability `μ₀` and any such `h`,
the product state of the corpus being the case `μ₀ = whiteNoise ι`.  A two-point space with the
`±1` sign and the uniform measure satisfies the hypotheses (`∫h = 0`, `∫h * h = 1`, `|h| = 1`).
-/

section GeneralWeight

variable {α : Type*} [MeasurableSpace α] (μ₀ : Measure α) [IsProbabilityMeasure μ₀]

omit [MeasurableSpace α] in
/-- The weight `1 - ε h z₁ h z₂` is strictly positive for `|h| ≤ 1` and `0 ≤ ε < 1`. -/
theorem generalWeight_pos (h : α → ℝ) (hbound : ∀ x, |h x| ≤ 1) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε1 : ε < 1) (z : α × α) : 0 < 1 - ε * h z.1 * h z.2 := by
  have habs : |h z.1 * h z.2| ≤ 1 := by
    rw [abs_mul]
    nlinarith [abs_nonneg (h z.1), abs_nonneg (h z.2), hbound z.1, hbound z.2]
  have hle : ε * (h z.1 * h z.2) ≤ ε := by
    nlinarith [mul_le_mul_of_nonneg_left habs hε0, (abs_le.1 habs).2]
  nlinarith [hle]

omit [MeasurableSpace α] in
/-- The weight is reflection invariant: it is a function of the unordered pair `{z₁, z₂}`. -/
theorem generalWeight_swap (h : α → ℝ) (ε : ℝ) (z : α × α) :
    (1 - ε * h z.2 * h z.1) = 1 - ε * h z.1 * h z.2 := by
  ring

/-- **The OS form of `1 - ε h₁ h₂` on the observable `h` is `-ε`.**  Each term is a product of one
function of each half, so the double integral factorizes. -/
theorem generalWeight_osForm (h : α → ℝ) (hh : Measurable h) (hbound : ∀ x, |h x| ≤ 1)
    (hmean : ∫ x, h x ∂μ₀ = 0) (hvar : ∫ x, h x * h x ∂μ₀ = 1) (ε : ℝ) :
    (∫ z : α × α, h z.2 * h z.1 * (1 - ε * h z.1 * h z.2) ∂(μ₀.prod μ₀)) = -ε := by
  have hint1 : Integrable (fun z : α × α => h z.2 * h z.1) (μ₀.prod μ₀) :=
    Integrable.of_bound (μ := μ₀.prod μ₀) (f := fun z : α × α => h z.2 * h z.1)
      ((hh.comp measurable_snd).mul (hh.comp measurable_fst)).aestronglyMeasurable (1 : ℝ) (by
        filter_upwards with z
        rw [Real.norm_eq_abs, abs_mul]
        nlinarith [abs_nonneg (h z.1), abs_nonneg (h z.2), hbound z.1, hbound z.2])
  have hint2 : Integrable (fun z : α × α => (h z.1 * h z.1) * (h z.2 * h z.2))
      (μ₀.prod μ₀) :=
    Integrable.of_bound (μ := μ₀.prod μ₀)
      (f := fun z : α × α => (h z.1 * h z.1) * (h z.2 * h z.2))
      (((hh.mul hh).comp measurable_fst).mul
        ((hh.mul hh).comp measurable_snd)).aestronglyMeasurable
      (1 : ℝ) (by
        filter_upwards with z
        rw [Real.norm_eq_abs, abs_mul]
        have h1 : |h z.1 * h z.1| ≤ 1 := by
          rw [abs_mul]
          nlinarith [abs_nonneg (h z.1), hbound z.1]
        have h2 : |h z.2 * h z.2| ≤ 1 := by
          rw [abs_mul]
          nlinarith [abs_nonneg (h z.2), hbound z.2]
        nlinarith [abs_nonneg (h z.1 * h z.1), abs_nonneg (h z.2 * h z.2)])
  have hsplit : (∫ z : α × α, h z.2 * h z.1 * (1 - ε * h z.1 * h z.2) ∂(μ₀.prod μ₀))
      = (∫ z : α × α, h z.2 * h z.1 ∂(μ₀.prod μ₀))
        - ε * (∫ z : α × α, (h z.1 * h z.1) * (h z.2 * h z.2) ∂(μ₀.prod μ₀)) := by
    rw [← integral_const_mul, ← integral_sub hint1 (hint2.const_mul ε)]
    refine integral_congr_ae (ae_of_all _ fun z => ?_)
    ring
  have hsq : (∫ z : α × α, (h z.1 * h z.1) * (h z.2 * h z.2) ∂(μ₀.prod μ₀)) = 1 := by
    have hprod := integral_prod_mul (μ := μ₀) (ν := μ₀) (L := ℝ)
      (f := fun x : α => h x * h x) (g := fun y : α => h y * h y)
    rw [hprod, hvar, mul_one]
  have hcross : (∫ z : α × α, h z.2 * h z.1 ∂(μ₀.prod μ₀)) = 0 := by
    have hprod := integral_prod_mul (μ := μ₀) (ν := μ₀) (L := ℝ)
      (f := fun x : α => h x) (g := fun y : α => h y)
    have hswap : (∫ z : α × α, h z.2 * h z.1 ∂(μ₀.prod μ₀))
        = ∫ z : α × α, h z.1 * h z.2 ∂(μ₀.prod μ₀) :=
      integral_congr_ae (ae_of_all _ fun z => mul_comm _ _)
    rw [hswap, hprod, hmean, mul_zero]
  rw [hsplit, hcross, hsq]
  ring

/-- **Reflection positivity fails for a reflection-invariant positive weight.**  There is a
strictly positive, reflection-invariant weight on `α × α` whose OS form is negative, so no
argument from invariance alone can give reflection positivity for a general density. -/
theorem not_reflectionPositive_of_generalWeight (h : α → ℝ) (hh : Measurable h)
    (hbound : ∀ x, |h x| ≤ 1) (hmean : ∫ x, h x ∂μ₀ = 0) (hvar : ∫ x, h x * h x ∂μ₀ = 1)
    {ε : ℝ} (hε0 : 0 < ε) (hε1 : ε < 1) :
    ∃ W : α × α → ℝ, (∀ z, 0 < W z) ∧ (∀ z, W (z.2, z.1) = W z) ∧
      (∫ z : α × α, h z.2 * h z.1 * W z ∂(μ₀.prod μ₀)) < 0 := by
  refine ⟨fun z => 1 - ε * h z.1 * h z.2, ?_, ?_, ?_⟩
  · exact fun z => generalWeight_pos (ε := ε) h hbound (le_of_lt hε0) hε1 z
  · exact fun z => generalWeight_swap h ε z
  · rw [show (∫ z : α × α, h z.2 * h z.1 * (1 - ε * h z.1 * h z.2) ∂(μ₀.prod μ₀)) = -ε from
      generalWeight_osForm μ₀ h hh hbound hmean hvar ε]
    linarith

end GeneralWeight


/-! ## What the `L²` question has as a complete answer

For the *product* state the two halves are independent, so the OS form collapses to a square and
the statement holds for **every** function of one half — no measurability, no bound and no
integrability hypothesis.  This is the `ν = δ₀` end of `covState`, and it shows that the
obstruction to the general `L²` statement is the shared shift (which is what makes the form a mean
of squares of *integrals* rather than a square of an integral), not the unboundedness of the
observable.
-/

/-- **A product state is reflection positive for every observable.** -/
theorem productState_reflectionPositive {α : Type*} [MeasurableSpace α] (μ₀ : Measure α)
    [SFinite μ₀] (H : α → ℝ) : 0 ≤ ∫ z : α × α, H z.2 * H z.1 ∂(μ₀.prod μ₀) := by
  have hprod := integral_prod_mul (μ := μ₀) (ν := μ₀) (L := ℝ)
    (f := fun x : α => H x) (g := fun y : α => H y)
  have hswap : (∫ z : α × α, H z.2 * H z.1 ∂(μ₀.prod μ₀))
      = ∫ z : α × α, H z.1 * H z.2 ∂(μ₀.prod μ₀) :=
    integral_congr_ae (ae_of_all _ fun z => mul_comm _ _)
  rw [hswap, hprod]
  exact mul_self_nonneg _

end

end BookProof.OSReconstruction
