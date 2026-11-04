import Mathlib
import BookProof.ReflectionPositivity.WilsonLattice

/-!
# The plaquette partition function and the normalised Wilson measure

`BookProof.ReflectionPositivity.WilsonLattice` shows that the Wilson plaquette interaction does not
spoil the slice split: the interacting measure is `ρ ⊗ ν_z ⊗ ν_z` with the interacting kernel
`ν_z = exp(−A(z,·))`, hence reflection positive.  What it does not do is normalise: it records "the
normalising constant of the interacting measure is not evaluated (it cancels), so no statement about
finiteness is made".

This chapter supplies that constant, and it turns out that the *plaquette bound is exactly the
whole story*:

* **`plaqDensity_le_two`** — together with the existing `plaqDensity_nonneg`, every plaquette
  density lies in `[0, 2]` for a unitary holonomy, because `|Re tr U| ≤ |tr U| ≤ N`;
* **`wilsonHalfAction_le`** — hence the half-space action is *bounded*,
  `0 ≤ A(y,z) ≤ 2β·#P`, and **`wilsonAction_le`** gives `0 ≤ S ≤ 4β·#P + sup b`
  (`wilsonAction_nonneg`, `wilsonAction_le`);
* **`exp_neg_wilsonAction_pos`**, **`exp_neg_wilsonAction_le_one`** and
  **`exp_neg_wilsonAction_ge`** — the Boltzmann density is squeezed,
  `exp(−(4β·#P + M)) ≤ exp(−S) ≤ 1`, *uniformly in the configuration*;
* **`wilsonMass`** — the plaquette partition function `Z = ∫ exp(−S)`, with
  **`wilsonMass_le`** `Z ≤ μ(univ)` and **`wilsonMass_ge`** `exp(−(4β·#P + M))·μ(univ) ≤ Z`: the two
  bounds together say the partition function is *a multiple of the reference volume*, nothing else;
* **`wilsonMass_eq_top`** — the consequence for the model as it stands: against the Lebesgue
  reference measure the Wilson measure has **infinite total mass**, `Z = ⊤`.  This is not a defect
  of the bound but a fact about the model: a bounded interaction cannot damp an infinite reference
  measure, and in a lattice gauge theory the reference measure is the (finite) *Haar* measure on
  the compact group, not Lebesgue;
* **`isProbabilityMeasure_wilsonProbability`** — whenever the reference measure is normalised,
  `μ(univ) = 1` (which is exactly what Haar on a compact group gives), the plaquette partition
  function satisfies `0 < Z ≤ 1` and `Z⁻¹ • wilsonMeasure` **is a probability measure**, by the
  same construction as `latticeGFFProbability`;
* **`wilsonProbability_reflectionPositive`** — and the normalised interacting measure is still
  reflection positive: a positive rescaling does not change the sign of the OS form.

## Honest boundary

* The theorem that makes the normalisation work is stated with the reference volume normalised,
  `μ(univ) = 1`.  That hypothesis *is* the Haar measure of the compact gauge group, which this
  model does not construct: the configurations are still points of `Gz × (Gy × Gy)` against a
  fixed reference measure, and the plaquette holonomies are an input function `U`.  What is proved
  is that *if* the reference measure is the group measure (a probability measure), the interacting
  partition function is finite, non-zero, bounded by `1`, and normalises the measure.
* No thermodynamic limit, no gauge invariance of observables, no continuum limit: `β`, `N`, the
  plaquette set `P` and the holonomies are fixed throughout.
-/

namespace BookProof.ReflectionPositivity

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {Gz Gy : Type*} [MeasureSpace Gz] [MeasureSpace Gy]
variable [SFinite (volume : Measure Gz)] [SFinite (volume : Measure Gy)]
variable {P : Type*} [Fintype P]

/-! ## 1. The plaquette density is bounded, so the action is bounded -/

/-- **The plaquette density is at most two**: `1 − Re tr U / N ≤ 2` because
`Re tr U ≥ −|tr U| ≥ −N` for a unitary `U`.  Together with `plaqDensity_nonneg` this puts every
plaquette density in `[0, 2]`. -/
theorem plaqDensity_le_two {N : ℕ} {U : Matrix (Fin N) (Fin N) ℂ}
    (hU : U ∈ Matrix.unitaryGroup (Fin N) ℂ) : plaqDensity N U ≤ 2 := by
  have hnorm : ‖U.trace‖ ≤ (N : ℝ) := by
    have := norm_trace_le_card hU
    simpa using this
  have habs : |U.trace.re| ≤ ‖U.trace‖ := Complex.abs_re_le_norm _
  have hge : -(N : ℝ) ≤ U.trace.re := by
    have : -‖U.trace‖ ≤ U.trace.re := by
      have := neg_abs_le (U.trace.re)
      linarith
    linarith
  have hN : (0 : ℝ) ≤ N := by positivity
  simp only [plaqDensity]
  rcases eq_or_lt_of_le hN with h | h
  · simp [← h]
  · have h1 : -(1 : ℝ) * N ≤ U.trace.re := by nlinarith
    have h2 : -(1 : ℝ) * N ≤ U.trace.re / N * N := by
      rwa [div_mul_cancel₀ _ h.ne']
    have h3 : -(1 : ℝ) ≤ U.trace.re / N := le_of_mul_le_mul_right h2 h
    linarith

/-- **The half-space plaquette action is bounded**: a sum over `#P` plaquettes of densities in
`[0,2]`, so `A(y,z) ≤ 2β·#P`. -/
theorem wilsonHalfAction_le {β : ℝ} (hβ : 0 ≤ β) {N : ℕ}
    {U : P → Gy → Gz → Matrix (Fin N) (Fin N) ℂ}
    (hU : ∀ (p : P) (y : Gy) (z : Gz), U p y z ∈ Matrix.unitaryGroup (Fin N) ℂ)
    (y : Gy) (z : Gz) :
    wilsonHalfAction β N U y z ≤ 2 * β * (Fintype.card P : ℝ) := by
  have hterm : ∀ p : P, β * plaqDensity N (U p y z) ≤ β * 2 := fun p =>
    mul_le_mul_of_nonneg_left (plaqDensity_le_two (hU p y z)) hβ
  simp only [wilsonHalfAction]
  calc ∑ p, β * plaqDensity N (U p y z) ≤ ∑ _p : P, β * 2 := Finset.sum_le_sum fun p _ => hterm p
    _ = 2 * β * (Fintype.card P : ℝ) := by
      rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
      ring

/-- **The Wilson action is nonnegative** for `β ≥ 0`, unitary holonomies and a nonnegative
boundary action: a sum of nonnegative plaquette densities. -/
theorem wilsonAction_nonneg {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (hN : 0 < N)
    {U : P → Gy → Gz → Matrix (Fin N) (Fin N) ℂ}
    (hU : ∀ (p : P) (y : Gy) (z : Gz), U p y z ∈ Matrix.unitaryGroup (Fin N) ℂ)
    {b : Gz → ℝ} (hb : ∀ z, 0 ≤ b z) (γ : Gz × (Gy × Gy)) :
    0 ≤ wilsonAction β N U b γ := by
  have h1 := wilsonHalfAction_nonneg hβ hN hU γ.2.1 γ.1
  have h2 := wilsonHalfAction_nonneg hβ hN hU γ.2.2 γ.1
  simp only [wilsonAction]
  linarith [hb γ.1]

/-- **The Wilson action is bounded**: `S ≤ 4β·#P + M` whenever the boundary action is bounded
by `M`.  This is the bound that makes the partition function a multiple of the reference volume. -/
theorem wilsonAction_le {β : ℝ} (hβ : 0 ≤ β) {N : ℕ}
    {U : P → Gy → Gz → Matrix (Fin N) (Fin N) ℂ}
    (hU : ∀ (p : P) (y : Gy) (z : Gz), U p y z ∈ Matrix.unitaryGroup (Fin N) ℂ)
    {b : Gz → ℝ} {M : ℝ} (hb : ∀ z, b z ≤ M) (γ : Gz × (Gy × Gy)) :
    wilsonAction β N U b γ ≤ 4 * β * (Fintype.card P : ℝ) + M := by
  have h1 := wilsonHalfAction_le hβ hU γ.2.1 γ.1
  have h2 := wilsonHalfAction_le hβ hU γ.2.2 γ.1
  have h3 := hb γ.1
  simp only [wilsonAction]
  linarith

/-! ## 2. The Boltzmann density is squeezed -/

theorem exp_neg_wilsonAction_pos {β : ℝ} {N : ℕ}
    {U : P → Gy → Gz → Matrix (Fin N) (Fin N) ℂ} {b : Gz → ℝ} (γ : Gz × (Gy × Gy)) :
    0 < Real.exp (-(wilsonAction β N U b γ)) := Real.exp_pos _

theorem exp_neg_wilsonAction_le_one {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (hN : 0 < N)
    {U : P → Gy → Gz → Matrix (Fin N) (Fin N) ℂ}
    (hU : ∀ (p : P) (y : Gy) (z : Gz), U p y z ∈ Matrix.unitaryGroup (Fin N) ℂ)
    {b : Gz → ℝ} (hb : ∀ z, 0 ≤ b z) (γ : Gz × (Gy × Gy)) :
    Real.exp (-(wilsonAction β N U b γ)) ≤ 1 := by
  rw [Real.exp_le_one_iff]
  have := wilsonAction_nonneg hβ hN hU hb γ
  linarith

theorem exp_neg_wilsonAction_ge {β : ℝ} (hβ : 0 ≤ β) {N : ℕ}
    {U : P → Gy → Gz → Matrix (Fin N) (Fin N) ℂ}
    (hU : ∀ (p : P) (y : Gy) (z : Gz), U p y z ∈ Matrix.unitaryGroup (Fin N) ℂ)
    {b : Gz → ℝ} {M : ℝ} (hb : ∀ z, b z ≤ M) (γ : Gz × (Gy × Gy)) :
    Real.exp (-(4 * β * (Fintype.card P : ℝ) + M)) ≤ Real.exp (-(wilsonAction β N U b γ)) := by
  refine Real.exp_le_exp.mpr ?_
  have := wilsonAction_le hβ hU hb γ
  linarith

/-! ## 3. The plaquette partition function -/

/-- **The plaquette partition function** `Z = ∫ exp(−S) dγ`: the total mass of the interacting
lattice gauge measure. -/
def wilsonMass (β : ℝ) (N : ℕ) (U : P → Gy → Gz → Matrix (Fin N) (Fin N) ℂ)
    (b : Gz → ℝ) : ℝ≥0∞ :=
  wilsonMeasure β N U b (Set.univ : Set (Gz × (Gy × Gy)))

/-- The reference measure of the configuration space, written out. -/
def wilsonBaseMeasure : Measure (Gz × (Gy × Gy)) :=
  (volume : Measure Gz).prod ((volume : Measure Gy).prod (volume : Measure Gy))

theorem wilsonMass_eq_lintegral (β : ℝ) (N : ℕ)
    (U : P → Gy → Gz → Matrix (Fin N) (Fin N) ℂ) (b : Gz → ℝ) :
    wilsonMass β N U b
      = ∫⁻ γ, ENNReal.ofReal (Real.exp (-(wilsonAction β N U b γ)))
          ∂(wilsonBaseMeasure (Gz := Gz) (Gy := Gy)) := by
  rw [wilsonMass, wilsonMeasure, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  rfl

/-- The total mass of the reference measure, written out. -/
theorem wilsonBaseMeasure_univ :
    wilsonBaseMeasure (Gz := Gz) (Gy := Gy)
        (Set.univ : Set (Gz × (Gy × Gy)))
      = (volume : Measure Gz) Set.univ
          * ((volume : Measure Gy) Set.univ * (volume : Measure Gy) Set.univ) := by
  have h1 : wilsonBaseMeasure (Gz := Gz) (Gy := Gy) (Set.univ : Set (Gz × (Gy × Gy)))
      = (volume : Measure Gz) Set.univ
          * (((volume : Measure Gy).prod (volume : Measure Gy))
              (Set.univ : Set (Gy × Gy))) := by
    rw [wilsonBaseMeasure, ← Set.univ_prod_univ,
      MeasureTheory.Measure.prod_prod]
  have h2 : ((volume : Measure Gy).prod (volume : Measure Gy))
      (Set.univ : Set (Gy × Gy))
      = (volume : Measure Gy) Set.univ * (volume : Measure Gy) Set.univ := by
    rw [← Set.univ_prod_univ, MeasureTheory.Measure.prod_prod]
  rw [h1, h2]

/-- **The partition function is at most the reference volume**: `Z ≤ μ(univ)`, because the
plaquette weights are at most one. -/
theorem wilsonMass_le {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (hN : 0 < N)
    {U : P → Gy → Gz → Matrix (Fin N) (Fin N) ℂ}
    (hU : ∀ (p : P) (y : Gy) (z : Gz), U p y z ∈ Matrix.unitaryGroup (Fin N) ℂ)
    {b : Gz → ℝ} (hb : ∀ z, 0 ≤ b z) :
    wilsonMass β N U b ≤ wilsonBaseMeasure (Gz := Gz) (Gy := Gy) Set.univ := by
  rw [wilsonMass_eq_lintegral]
  calc ∫⁻ γ, ENNReal.ofReal (Real.exp (-(wilsonAction β N U b γ)))
        ∂(wilsonBaseMeasure (Gz := Gz) (Gy := Gy))
      ≤ ∫⁻ _γ, (1 : ℝ≥0∞) ∂(wilsonBaseMeasure (Gz := Gz) (Gy := Gy)) :=
        lintegral_mono fun γ => by
          rw [ENNReal.ofReal_le_one]
          exact exp_neg_wilsonAction_le_one hβ hN hU hb γ
    _ = wilsonBaseMeasure (Gz := Gz) (Gy := Gy) Set.univ := lintegral_one

/-- **The partition function is at least a positive multiple of the reference volume**:
`exp(−(4β·#P + M))·μ(univ) ≤ Z`, because the action is bounded. -/
theorem wilsonMass_ge {β : ℝ} (hβ : 0 ≤ β) {N : ℕ}
    {U : P → Gy → Gz → Matrix (Fin N) (Fin N) ℂ}
    (hU : ∀ (p : P) (y : Gy) (z : Gz), U p y z ∈ Matrix.unitaryGroup (Fin N) ℂ)
    {b : Gz → ℝ} {M : ℝ} (hb : ∀ z, b z ≤ M) :
    ENNReal.ofReal (Real.exp (-(4 * β * (Fintype.card P : ℝ) + M)))
        * wilsonBaseMeasure (Gz := Gz) (Gy := Gy) Set.univ
      ≤ wilsonMass β N U b := by
  rw [wilsonMass_eq_lintegral]
  have hmono : (∫⁻ _γ, ENNReal.ofReal (Real.exp (-(4 * β * (Fintype.card P : ℝ) + M)))
        ∂(wilsonBaseMeasure (Gz := Gz) (Gy := Gy)))
      ≤ ∫⁻ γ, ENNReal.ofReal (Real.exp (-(wilsonAction β N U b γ)))
        ∂(wilsonBaseMeasure (Gz := Gz) (Gy := Gy)) :=
    lintegral_mono fun γ => ENNReal.ofReal_le_ofReal (exp_neg_wilsonAction_ge hβ hU hb γ)
  rwa [lintegral_const] at hmono

/-- **Against the Lebesgue reference measure the plaquette partition function diverges**: the
interaction is bounded, so it cannot damp an infinite reference measure,

`Z ≥ exp(−(4β·#P + M)) · μ(univ) = ⊤`.

This is why a lattice gauge theory uses the *finite* Haar measure of the compact group as its
reference measure: with it the same bound gives `0 < Z ≤ 1` (`wilsonMass_le`, `wilsonMass_ge`). -/
theorem wilsonMass_eq_top {β : ℝ} (hβ : 0 ≤ β) {N : ℕ}
    {U : P → Gy → Gz → Matrix (Fin N) (Fin N) ℂ}
    (hU : ∀ (p : P) (y : Gy) (z : Gz), U p y z ∈ Matrix.unitaryGroup (Fin N) ℂ)
    {b : Gz → ℝ} {M : ℝ} (hb : ∀ z, b z ≤ M)
    (hinf : (volume : Measure Gy) Set.univ = ⊤)
    (hpos : (volume : Measure Gz) Set.univ ≠ 0) :
    wilsonMass β N U b = ⊤ := by
  have hc : ENNReal.ofReal (Real.exp (-(4 * β * (Fintype.card P : ℝ) + M))) ≠ 0 :=
    ENNReal.ofReal_ne_zero_iff.mpr (Real.exp_pos _)
  have huniv : wilsonBaseMeasure (Gz := Gz) (Gy := Gy) Set.univ = ⊤ := by
    rw [wilsonBaseMeasure_univ, hinf]
    simp only [ENNReal.top_mul_top, ENNReal.mul_top hpos]
  have hge := wilsonMass_ge (Gz := Gz) (Gy := Gy) hβ hU hb
  rw [huniv, ENNReal.mul_top hc] at hge
  exact top_le_iff.mp hge

/-! ## 4. The normalised interacting measure is a probability measure -/

/-- **The normalised Wilson measure**: the interacting lattice gauge measure rescaled by its
plaquette partition function.  For a normalised reference measure (`μ(univ) = 1`, as for the Haar
measure of a compact gauge group) this is the physical probability law of the lattice gauge
theory. -/
def wilsonProbability (β : ℝ) (N : ℕ) (U : P → Gy → Gz → Matrix (Fin N) (Fin N) ℂ)
    (b : Gz → ℝ) : Measure (Gz × (Gy × Gy)) :=
  (wilsonMass (Gz := Gz) (Gy := Gy) β N U b)⁻¹ • wilsonMeasure β N U b

/-- **The partition function is positive and at most one for a normalised reference measure** —
this is the plaquette bound `0 ≤ S` together with `μ(univ) = 1`. -/
theorem wilsonMass_pos_of_univ_eq_one {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (hN : 0 < N)
    {U : P → Gy → Gz → Matrix (Fin N) (Fin N) ℂ}
    (hU : ∀ (p : P) (y : Gy) (z : Gz), U p y z ∈ Matrix.unitaryGroup (Fin N) ℂ)
    {b : Gz → ℝ} (hb : ∀ z, 0 ≤ b z) {M : ℝ} (hbM : ∀ z, b z ≤ M)
    (hμ : wilsonBaseMeasure (Gz := Gz) (Gy := Gy) Set.univ = 1) :
    0 < wilsonMass β N U b ∧ wilsonMass β N U b ≤ 1 := by
  have hcpos : 0 < Real.exp (-(4 * β * (Fintype.card P : ℝ) + M)) := Real.exp_pos _
  have hge := wilsonMass_ge (Gz := Gz) (Gy := Gy) hβ hU hbM
  rw [hμ, mul_one] at hge
  refine ⟨lt_of_lt_of_le (ENNReal.ofReal_pos.mpr hcpos) hge, ?_⟩
  have hle := wilsonMass_le (Gz := Gz) (Gy := Gy) hβ hN hU hb
  rwa [hμ] at hle

/-- **`wilsonMeasure` normalised is a probability measure** whenever the reference measure is
normalised (`μ(univ) = 1`) — the case of the Haar measure on the compact gauge group. -/
theorem isProbabilityMeasure_wilsonProbability {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (hN : 0 < N)
    {U : P → Gy → Gz → Matrix (Fin N) (Fin N) ℂ}
    (hU : ∀ (p : P) (y : Gy) (z : Gz), U p y z ∈ Matrix.unitaryGroup (Fin N) ℂ)
    {b : Gz → ℝ} (hb : ∀ z, 0 ≤ b z) {M : ℝ} (hbM : ∀ z, b z ≤ M)
    (hμ : wilsonBaseMeasure (Gz := Gz) (Gy := Gy) Set.univ = 1) :
    IsProbabilityMeasure (wilsonProbability (Gz := Gz) (Gy := Gy) β N U b) := by
  obtain ⟨h0, htop⟩ := wilsonMass_pos_of_univ_eq_one hβ hN hU hb hbM hμ
  refine ⟨?measure_univ⟩
  rw [wilsonProbability, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel h0.ne'
    (ne_of_lt (lt_of_le_of_lt htop (by simp : (1 : ℝ≥0∞) < ⊤)))

/-- **Normalising does not destroy reflection positivity**: the OS form under the probability
measure is `Z⁻¹` times the OS form under the unnormalised interacting measure, hence still
nonnegative. -/
theorem wilsonProbability_reflectionPositive {β : ℝ} (hβ : 0 ≤ β) {N : ℕ} (hN : 0 < N)
    {U : P → Gy → Gz → Matrix (Fin N) (Fin N) ℂ} {b : Gz → ℝ}
    (hmeas : Measurable fun q : Gy × Gz => wilsonHalfAction β N U q.1 q.2)
    (hb : Measurable b) (f : Gz → Gy → ℝ)
    (hint : Integrable (fun γ : Gz × (Gy × Gy) =>
        Real.exp (-(wilsonAction β N U b γ)) * fkOSForm f γ)
      ((volume : Measure Gz).prod ((volume : Measure Gy).prod (volume : Measure Gy)))) :
    0 ≤ ∫ γ, liftHalf f (reflectConf γ) * liftHalf f γ
        ∂(wilsonProbability (Gz := Gz) (Gy := Gy) β N U b) := by
  have hunit : (volume : Measure Gz).prod ((volume : Measure Gy).prod (volume : Measure Gy))
      = wilsonBaseMeasure (Gz := Gz) (Gy := Gy) := rfl
  rw [wilsonProbability, integral_smul_measure, smul_eq_mul]
  refine mul_nonneg ENNReal.toReal_nonneg ?_
  exact wilson_reflectionPositive hβ hN hmeas hb f (by rw [hunit]; exact hint)

end

end BookProof.ReflectionPositivity
