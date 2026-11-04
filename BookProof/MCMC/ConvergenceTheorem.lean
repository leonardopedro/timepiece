import Mathlib
import BookProof.MCMC.GeometricErgodicity

/-!
# Chapter ConvergenceTheorem — total variation convergence from the L² gap

Plan: `pcnl.md`, Milestone 5 (target file `BookProof/MCMC/ConvergenceTheorem.lean`).

`BookProof.MCMC.GeometricErgodicity` proves the `L²` half of the plan's Modules 4–5,

`‖P ^ m ψ − ⟪φ,ψ⟫ φ‖ ≤ (1 − γ) ^ m ‖ψ − ⟪φ,ψ⟫ φ‖`,

and records as its **boundary** — the step deliberately left unproved there — the
*Born-to-variation* inequality that converts an `L²` estimate on a **density ratio** into a
total-variation estimate:

`‖ν − π‖_TV ≤ ½ ‖dν/dπ − 1‖_{L²(π)}`.

This chapter supplies exactly that step, and then discharges Milestone 5's statement
(`pcnl_mcmc_geometric_convergence`): geometric decay of `‖d_m − 1‖_{L²}` implies geometric
convergence in total variation.

## What is proved here

* `tvDist` — the total variation distance, defined as the sup over measurable sets of
  `ofReal |ν s − π s|`.  (Mathlib has `SignedMeasure.totalVariation`, but no measure-to-measure
  distance; this is the standard definition `sup_A |ν A − π A|`.)  It lands in `ENNReal`, since
  `ℝ` is only *conditionally* complete in this Mathlib version and the supremum need not be
  bounded a priori.
* `toReal_eq_integral_one` — `(π s).toReal = ∫ x in s, 1 ∂π`: the reference measure *is* the
  integral of its constant density, so the two discrepancies in `tvDist` live in one integral.
* `integrable_add_one` / `integrable_sub_one` — `g − 1 ∈ L¹` implies `g ∈ L¹`, since
  `g = (g − 1) + 1`.  This turns the `MemLp` hypothesis on the density *ratio* into the
  integrability the `withDensity` relation needs.
* `withDensity_toReal_eq_integral` — the density relation for `π.withDensity (ofReal ∘ g)`: on
  a measurable set its value is `∫ x in s, g x ∂π`, given `g ≥ 0` and integrable.
* **`tvDist_le_half_l2`** — **the Born-to-variation bound**.  If `ν` has density `g` with
  `∫ g = 1` and `g − 1 ∈ L²(π)`, then
  `‖ν − π‖_TV ≤ ofReal (½ √(∫ (g − 1)²))`.
* `pcnl_mcmc_geometric_convergence` — Milestone 5: `‖ν_m − π‖_TV ≤ ofReal ((C/2)(1 − γ)^m)`
  whenever `√(∫ (d_m − 1)²) ≤ C (1 − γ)^m`.

## Proof of `tvDist_le_half_l2`, in words

Fix a measurable `s` and write `a = ∫ x in s, (g x − 1) ∂π`.  Since `∫ (g − 1) = ∫ g − ∫ 1 = 0`
(the reference measure is a probability measure, so `∫ 1 = 1`), complementarity gives
`∫ x in sᶜ, (g x − 1) ∂π = −a`, hence `|a| = |∫ x in sᶜ, (g x − 1)|`.  Each of these two numbers
is bounded by the integral of `|g − 1|` over the corresponding piece, so
`2|a| ≤ ∫_s |g − 1| + ∫_{sᶜ} |g − 1| = ∫ |g − 1|`, i.e. `|a| ≤ ½ ∫ |g − 1|`.
Finally Cauchy–Schwarz (Hölder with the constant density `1`, whose `L²` norm is `1` because
`π` is a probability measure) yields `∫ |g − 1| ≤ √(∫ (g − 1)²)`.
Since `ν s − π s = a`, taking the sup over `s` finishes.

The factor `½` is therefore *sharp* and not an artefact: the sup is attained at the set
`{g ≥ 1}` (not proved here — the inequality is all Milestone 5 needs).

## Boundary

* `tvDist` is defined here rather than taken from Mathlib, because Mathlib's
  `SignedMeasure.totalVariation` lives on signed measures, not on pairs of measures.
* The hypothesis `hdens` in `tvDist_le_half_l2` is the *set-wise* form of "ν has density `g`
  w.r.t. `π`"; `withDensity_toReal_eq_integral` discharges it for the concrete
  `π.withDensity (ofReal ∘ g)` used by MCMC.
* Nothing here assumes a mixing rate: `C` and `γ` are carried as hypotheses, exactly as in
  `GeometricErgodicity`.
-/

noncomputable section

namespace BookProof.MCMC

open MeasureTheory

variable {α : Type*} [MeasurableSpace α]

/-! ## The total variation distance -/

/-- The total variation distance between two measures: the supremum over measurable sets `s` of
`ofReal |ν s − π s|`.  For probability measures this equals the usual `sup_A |ν A − π A|`.

The codomain is `ENNReal` rather than `ℝ` because `ℝ` is only *conditionally* complete in this
Mathlib version, so an unguarded `⨆` into `ℝ` is not available. -/
noncomputable def tvDist (ν π : Measure α) : ENNReal :=
  ⨆ t : {t : Set α // MeasurableSet t}, ENNReal.ofReal (|(ν t.1).toReal - (π t.1).toReal|)

/-- `tvDist` is bounded by `c` as soon as every measurable set's discrepancy is. -/
theorem tvDist_le {ν π : Measure α} {c : ENNReal}
    (h : ∀ s : Set α, MeasurableSet s →
      ENNReal.ofReal (|(ν s).toReal - (π s).toReal|) ≤ c) :
    tvDist ν π ≤ c := by
  simp only [tvDist]
  exact @iSup_le ENNReal {t : Set α // MeasurableSet t} _
    (fun t : {t : Set α // MeasurableSet t} =>
      ENNReal.ofReal (|(ν t.1).toReal - (π t.1).toReal|)) c
    (fun t : {t : Set α // MeasurableSet t} => h t.1 t.2)

/-! ## The reference measure is the integral of its constant density -/

/-- For a measurable set `s`, `(π s).toReal = ∫ x in s, 1 ∂π`.  This is what lets us compare
`(ν s).toReal` with `(π s).toReal` inside a single integral. -/
theorem toReal_eq_integral_one {π : Measure α} {s : Set α} (_hs : MeasurableSet s) :
    (π s).toReal = ∫ _ in s, (1:ℝ) ∂π := by
  rw [setIntegral_const, measureReal_def]
  simp [smul_eq_mul]

/-! ## Integrability of a density from that of its deviation -/

/-- `g − 1` integrable implies `g` integrable, since `g = (g − 1) + 1`. -/
theorem integrable_add_one {π : Measure α} [IsFiniteMeasure π] {g : α → ℝ}
    (h : Integrable (fun x => g x - 1) π) : Integrable g π := by
  have h2 : Integrable (fun x => (g x - 1) + (1:ℝ)) π := h.add (integrable_const _)
  have h3 : (fun x => (g x - 1) + (1:ℝ)) = g := by funext x; simp [sub_add_cancel]
  rwa [h3] at h2

/-- `MemLp (fun x => g x - 1) (ENNReal.ofReal 2) π` implies `Integrable (fun x => g x - 1) π`. -/
theorem integrable_sub_one {π : Measure α} [IsFiniteMeasure π] {g : α → ℝ}
    (h : MemLp (fun x => g x - 1) (ENNReal.ofReal 2) π) :
    Integrable (fun x => g x - 1) π :=
  h.integrable (by simp only [ENNReal.ofReal_ofNat]; norm_num)

/-! ## The density relation for `withDensity` -/

/-- `π.withDensity (ofReal ∘ g)` really does have density `g`: on a measurable set its value is
`∫ x in s, g x ∂π`.  This is `withDensity_apply` plus the fact that `ofReal` commutes with the
integral of a nonnegative integrable function. -/
theorem withDensity_toReal_eq_integral {π : Measure α} (g : α → ℝ)
    (hgI : Integrable g π) (hg0 : 0 ≤ g) {s : Set α} (hs : MeasurableSet s) :
    ((π.withDensity fun x => ENNReal.ofReal (g x)) s).toReal = ∫ x in s, g x ∂π := by
  rw [withDensity_apply _ hs]
  simp only [← ofReal_integral_eq_lintegral_ofReal hgI.restrict (ae_of_all _ hg0)]
  exact ENNReal.toReal_ofReal (integral_nonneg hg0)

/-! ## The Born-to-variation bound -/

/-- **The Born-to-variation bound.**  If `ν` has density `g` with `∫ g = 1` and `g − 1 ∈ L²(π)`,
then `‖ν − π‖_TV ≤ ofReal (½ √(∫ (g − 1)²))`, i.e. `½ ‖g − 1‖_{L²(π)}`.

The hypothesis `hdens` is the set-wise form of "ν has density `g` w.r.t. `π`";
`withDensity_toReal_eq_integral` discharges it for MCMC's `π.withDensity (ofReal ∘ g)`. -/
theorem tvDist_le_half_l2 {π : Measure α} [IsProbabilityMeasure π] (g : α → ℝ)
    (ν : Measure α)
    (hdens : ∀ s : Set α, MeasurableSet s → (ν s).toReal = ∫ x in s, g x ∂π)
    (hg1 : ∫ x, g x ∂π = 1)
    (hg2 : MemLp (fun x => g x - 1) (ENNReal.ofReal 2) π) :
    tvDist ν π ≤ ENNReal.ofReal ((1 / 2) * Real.sqrt (∫ x, (g x - 1) ^ 2 ∂π)) := by
  have hsub : Integrable (fun x => g x - 1) π := integrable_sub_one hg2
  have hgI : Integrable g π := integrable_add_one hsub
  -- the reference measure integrates its constant density to `1`
  have h1c : ∫ x, (1:ℝ) ∂π = 1 := by
    rw [integral_const, probReal_univ]
    simp
  -- hence `∫ (g − 1) = 0`
  have hzero : ∫ x, (g x - 1) ∂π = 0 := by
    rw [integral_sub hgI (integrable_const _), hg1, h1c]
    simp
  refine tvDist_le fun s hs => ?_
  refine ENNReal.ofReal_le_ofReal ?_
  rw [hdens s hs, toReal_eq_integral_one hs]
  -- `∫_s g − ∫_s 1 = ∫_s (g − 1)`
  have hsplit : ∫ x in s, g x ∂π - ∫ x in s, (1:ℝ) ∂π = ∫ x in s, (g x - 1) ∂π :=
    (integral_sub (hgI.restrict (s := s)) (integrable_const (1:ℝ))).symm
  rw [hsplit]
  -- the complement carries the opposite mass, hence the same absolute value
  have hneg : ∫ x in sᶜ, (g x - 1) ∂π = -∫ x in s, (g x - 1) ∂π := by
    have hsum : ∫ x in s, (g x - 1) ∂π + ∫ x in sᶜ, (g x - 1) ∂π
        = ∫ x, (g x - 1) ∂π := integral_add_compl hs hsub
    rw [hzero] at hsum
    linarith
  have habsI : Integrable (fun x => |g x - 1|) π := hsub.abs
  have habs' : ∫ x in s, |g x - 1| ∂π + ∫ x in sᶜ, |g x - 1| ∂π
      = ∫ x, |g x - 1| ∂π := integral_add_compl hs habsI
  have ha1 : |∫ x in s, (g x - 1) ∂π| ≤ ∫ x in s, |g x - 1| ∂π :=
    abs_integral_le_integral_abs
  have ha2 : |∫ x in sᶜ, (g x - 1) ∂π| ≤ ∫ x in sᶜ, |g x - 1| ∂π :=
    abs_integral_le_integral_abs
  have ha : |∫ x in s, (g x - 1) ∂π| = |∫ x in sᶜ, (g x - 1) ∂π| := by
    rw [hneg, abs_neg]
  have h2m : 2 * |∫ x in s, (g x - 1) ∂π| ≤ ∫ x, |g x - 1| ∂π := by
    rw [two_mul]
    have ha1' : |∫ x in s, (g x - 1) ∂π| ≤ ∫ x in sᶜ, |g x - 1| ∂π := by
      rw [ha]
      exact ha2
    exact le_trans (add_le_add ha1 ha1') (le_of_eq habs')
  have hhalf : |∫ x in s, (g x - 1) ∂π| ≤ (1 / 2) * ∫ x, |g x - 1| ∂π := by
    have hkey : (1 / 2:ℝ) * (2 * |∫ x in s, (g x - 1) ∂π|)
        = |∫ x in s, (g x - 1) ∂π| := by ring
    rw [← hkey]
    exact mul_le_mul_of_nonneg_left h2m (by norm_num)
  -- Cauchy–Schwarz against the constant density, whose `L²` norm is `1`
  have hcs : ∫ x, |g x - 1| ∂π ≤ (∫ x, (g x - 1) ^ 2 ∂π) ^ ((1:ℝ) / 2) := by
    have h := integral_mul_norm_le_Lp_mul_Lq Real.HolderConjugate.two_two hg2
      (memLp_const (1:ℝ))
    simp only [Real.norm_eq_abs, abs_one, mul_one, Real.rpow_two, sq_abs, one_pow] at h
    rw [h1c, Real.one_rpow, mul_one] at h
    exact h
  rw [Real.sqrt_eq_rpow]
  exact le_trans hhalf (mul_le_mul_of_nonneg_left hcs (by norm_num))

/-! ## Milestone 5 -/

/-- **`pcnl.md`, Milestone 5** — geometric convergence in total variation.

If the density ratios `d m` of a family of MCMC iterates `ν m` satisfy
`√(∫ (d m − 1)²) ≤ C (1 − γ)^m`, then `‖ν m − π‖_TV ≤ ofReal ((C/2) (1 − γ)^m)`.

The decay estimate `hdecay` is exactly what
`GeometricErgodicity.norm_iterate_sub_invariant_le` supplies for the `L²(π)` distance of the
symmetrised densities to `1`; this theorem is the Born-to-variation half of Milestone 5 and
needs nothing further. -/
theorem pcnl_mcmc_geometric_convergence {π : Measure α} [IsProbabilityMeasure π]
    (ν : ℕ → Measure α) (d : ℕ → α → ℝ) (C γ : ℝ) (hγ1 : γ < 1)
    (hdens : ∀ m, ∀ s : Set α, MeasurableSet s → (ν m s).toReal = ∫ x in s, d m x ∂π)
    (hd1 : ∀ m, ∫ x, d m x ∂π = 1)
    (hd2 : ∀ m, MemLp (fun x => d m x - 1) (ENNReal.ofReal 2) π)
    (hdecay : ∀ m, Real.sqrt (∫ x, (d m x - 1) ^ 2 ∂π) ≤ C * (1 - γ) ^ m) :
    ∀ m, tvDist (ν m) π ≤ ENNReal.ofReal ((C / 2) * (1 - γ) ^ m) := by
  intro m
  refine le_trans (tvDist_le_half_l2 (d m) (ν m) (hdens m) (hd1 m) (hd2 m)) ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hsq : 0 ≤ Real.sqrt (∫ x, (d m x - 1) ^ 2 ∂π) := Real.sqrt_nonneg _
  have hpp : 0 ≤ (1 - γ) ^ m := pow_nonneg (by linarith) _
  nlinarith [hdecay m, hsq, hpp]

end BookProof.MCMC
