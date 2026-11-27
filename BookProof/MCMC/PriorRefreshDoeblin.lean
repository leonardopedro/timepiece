import Mathlib
import BookProof.MCMC.SatisficingTarget

/-!
# Chapter PriorRefreshDoeblin — the prior-refresh independence sampler's Doeblin minorisation

This is packet **S1** (first module) of `pcnl.md`'s active S0–S6 work order, executing Q1 of
the programme.  The sharp-Gibbs wall measured in R13 (`e^{−O(10^4)}` minorisation constants in
57k dimensions) is a statement about a *likelihood-dominated* target.  This chapter proves the
one global certificate that needs no spectral analysis at all: an **independence MH** move that
proposes from the prior has a Doeblin coefficient `Z/M` for every target whose density is
bounded away from `∞` by `M`.

## Setting

`μ0` is a probability prior, `L : Ω → ℝ` a nonnegative measurable likelihood with `0 ≤ L ≤ M`,
and the target is `π = Z⁻¹ L μ0` with `Z = ∫ L dμ0`.  The independence step proposes `y ∼ μ0`
and accepts with `min 1 (L y / L x)`; its accepted part is `indKernel μ0 L x`, and adding the
rejection atom at `x` gives `indStep`.

## Contents

* **§1, the kernel** — `indAccept`, `indKernel`, `indStep`, and `indKernel_univ_le_one`;
* **§2, the minorisation** — **`indKernel_ge_density`** (`(1/M) • (L μ0) ≤ K(x,·)`), and its
  normalised form **`indKernel_minorant`**: `(Z/M) • π ≤ K(x,·)` for every `x` with
  `0 < L x ≤ M`.  The plan's hypothesis set `{L > 0}` is exactly `hxpos`; no other condition on
  the start point enters.  **`indStep_minorant`** carries the same constant through the
  rejection atom, and **`mixture_minorant`** gives `c_ω = ω Z/M` for
  `K_ω = (1−ω) K_local + ω K_ind`;
* **§3, the Doeblin consequence** — `priorTarget_univ`, `indStep_univ`, and the set-level
  contraction **`indStep_tv_bound`**: for every measurable `A`,
  `|K(x,A) − π(A)| ≤ 1 − Z/M`;
* **§4, the S0 bridge** — `minorant_coefficient_pos`, recording that with S0's lower bound
  `Z ≥ P₀(A) e^{−b}` the coefficient `Z/M` is the same number that S0 certifies positive;
  `coefficient_le_one` (`Z/M ≤ 1`) and **`coefficient_le_of_ceiling_le`**: if the likelihood
  ceiling is at most `C`, the coefficient is at least `Z/C`.  With an `O(1)` plateau
  `C = O(1)` this is `Z/O(1)`, rather than the sharp-Gibbs `e^{−O(10^4)}` collapse.

## Scope

`B` (boundary): this is the *independence-sampler* certificate.  It says nothing about the
local pCN proposal's own gap; it is the reference/fallback kernel, as the plan states.  The
accepted-part kernel is a subprobability; `indStep` is the probability kernel.  The target
needs `0 < Z < ∞` (proved from the hypotheses here), and the minorisation is stated for starts
with `L x > 0` exactly as Q1 requires.

`C` (conditional): the **centred `L²(π)` form** of the contraction is not proved here.  It
proceeds by the decomposition `K = cΠ + (1−c)Q` with `Q` a Markov kernel built from the
residual `K − cπ`; that construction and the resulting `‖Kf − πf‖₂ ≤ (1−c)‖f − πf‖₂` are
left for a later wave.  What is proved unconditionally is the set-level total-variation
contraction `indStep_tv_bound`.
-/

namespace BookProof.MCMC.PriorRefreshDoeblin

open MeasureTheory

variable {Ω : Type*} [MeasurableSpace Ω]

/-! ## §1. The independence MH kernel -/

/-- The independence-MH acceptance probability `min 1 (L y / L x)`. -/
noncomputable def indAccept (L : Ω → ℝ) (x y : Ω) : ℝ := min 1 (L y / L x)

/-- The **accepted** part of the independence step: the prior `μ0` weighted by the acceptance
probability.  This is a subprobability whose missing mass is the rejection atom. -/
noncomputable def indKernel (μ0 : Measure Ω) (L : Ω → ℝ) (x : Ω) : Measure Ω :=
  μ0.withDensity fun y => ENNReal.ofReal (indAccept L x y)

/-- The independence step with its rejection atom: accepted moves plus `(1 − K(x,·)(Ω)) δ_x`. -/
noncomputable def indStep (μ0 : Measure Ω) (L : Ω → ℝ) (x : Ω) : Measure Ω :=
  indKernel μ0 L x
    + (1 - indKernel μ0 L x Set.univ) • Measure.dirac x

/-- The unnormalised target mass `Z = ∫ L dμ0`. -/
noncomputable def priorZ (μ0 : Measure Ω) (L : Ω → ℝ) : ENNReal :=
  ∫⁻ y, ENNReal.ofReal (L y) ∂μ0

/-- The normalised prior-refresh target `π = Z⁻¹ L μ0`. -/
noncomputable def priorTarget (μ0 : Measure Ω) (L : Ω → ℝ) : Measure Ω :=
  (priorZ μ0 L)⁻¹ • μ0.withDensity (fun y => ENNReal.ofReal (L y))

/-- The accepted part has mass at most one (the acceptance is at most one). -/
theorem indKernel_univ_le_one (μ0 : Measure Ω) [IsProbabilityMeasure μ0] (L : Ω → ℝ)
    (x : Ω) : indKernel μ0 L x Set.univ ≤ 1 := by
  unfold indKernel
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  calc ∫⁻ y, ENNReal.ofReal (indAccept L x y) ∂μ0
      ≤ ∫⁻ _y, (1 : ENNReal) ∂μ0 := by
        refine lintegral_mono fun y => ?_
        unfold indAccept
        exact ENNReal.ofReal_le_one.mpr (min_le_left _ _)
    _ = 1 := by rw [lintegral_one, measure_univ]

/-! ## §2. The minorisation -/

/-- **The density-level minorisation.**  If `0 < L x ≤ M` and `0 ≤ L ≤ M`, the accepted part
of the independence step dominates `(1/M) · (L μ0)`. -/
theorem indKernel_ge_density {μ0 : Measure Ω} {L : Ω → ℝ} {M : ℝ} (hM : 0 < M)
    (hLmeas : Measurable L) (hLnn : ∀ y, 0 ≤ L y) (hLbdd : ∀ y, L y ≤ M) {x : Ω}
    (hxpos : 0 < L x) (hxM : L x ≤ M) :
    ENNReal.ofReal M⁻¹ • μ0.withDensity (fun y => ENNReal.ofReal (L y))
      ≤ indKernel μ0 L x := by
  have hpt : ∀ y, ENNReal.ofReal (M⁻¹ * L y) ≤ ENNReal.ofReal (indAccept L x y) := by
    intro y
    refine ENNReal.ofReal_le_ofReal ?_
    have hy : 0 ≤ L y := hLnn y
    have h1 : M⁻¹ * L y ≤ 1 := by
      have : L y / M ≤ 1 := (div_le_one hM).mpr (hLbdd y)
      simpa [div_eq_inv_mul] using this
    have h2 : M⁻¹ * L y ≤ L y / L x := by
      have hMx : M⁻¹ ≤ (L x)⁻¹ := (inv_le_inv₀ hM hxpos).mpr hxM
      calc M⁻¹ * L y ≤ (L x)⁻¹ * L y := by gcongr
        _ = L y / L x := by rw [div_eq_inv_mul]
    exact le_min h1 h2
  have hwith : μ0.withDensity (fun y => ENNReal.ofReal (M⁻¹ * L y))
      ≤ indKernel μ0 L x := by
    unfold indKernel
    exact withDensity_mono (Filter.Eventually.of_forall hpt)
  have hfun : (fun y => ENNReal.ofReal (M⁻¹ * L y))
      = (fun y => ENNReal.ofReal M⁻¹ * ENNReal.ofReal (L y)) := by
    funext y
    rw [ENNReal.ofReal_mul (inv_nonneg.mpr hM.le)]
  have hsmul : μ0.withDensity (fun y => ENNReal.ofReal M⁻¹ * ENNReal.ofReal (L y))
      = ENNReal.ofReal M⁻¹ • μ0.withDensity (fun y => ENNReal.ofReal (L y)) := by
    simpa [Pi.smul_apply, smul_eq_mul] using
      (withDensity_smul (μ := μ0) (ENNReal.ofReal M⁻¹)
        (f := fun y => ENNReal.ofReal (L y)) (ENNReal.measurable_ofReal.comp hLmeas))
  rwa [hfun, hsmul] at hwith

/-- **The normalised minorisation `K_ind(x,·) ≥ (Z/M) π(·)`.**  The coefficient is `Z/M`, and
the only condition on the start is `0 < L x ≤ M` (the plan's `{L > 0}`). -/
theorem indKernel_minorant {μ0 : Measure Ω} {L : Ω → ℝ} {M : ℝ} (hM : 0 < M)
    (hLmeas : Measurable L) (hLnn : ∀ y, 0 ≤ L y) (hLbdd : ∀ y, L y ≤ M)
    (hZ0 : priorZ μ0 L ≠ 0) (hZtop : priorZ μ0 L ≠ ⊤) {x : Ω} (hxpos : 0 < L x)
    (hxM : L x ≤ M) :
    (priorZ μ0 L * ENNReal.ofReal M⁻¹) • priorTarget μ0 L ≤ indKernel μ0 L x := by
  have hbase := indKernel_ge_density (μ0 := μ0) hM hLmeas hLnn hLbdd hxpos hxM
  have hun : μ0.withDensity (fun y => ENNReal.ofReal (L y))
      = priorZ μ0 L • priorTarget μ0 L := by
    unfold priorTarget
    rw [smul_smul, ENNReal.mul_inv_cancel hZ0 hZtop, one_smul]
  rw [hun, smul_smul] at hbase
  simpa [mul_comm] using hbase

/-- **The same constant through the rejection atom**: the probability step dominates
`(Z/M) π`. -/
theorem indStep_minorant {μ0 : Measure Ω} {L : Ω → ℝ} {M : ℝ} (hM : 0 < M)
    (hLmeas : Measurable L) (hLnn : ∀ y, 0 ≤ L y) (hLbdd : ∀ y, L y ≤ M)
    (hZ0 : priorZ μ0 L ≠ 0) (hZtop : priorZ μ0 L ≠ ⊤) {x : Ω} (hxpos : 0 < L x)
    (hxM : L x ≤ M) :
    (priorZ μ0 L * ENNReal.ofReal M⁻¹) • priorTarget μ0 L ≤ indStep μ0 L x := by
  refine le_trans
    (indKernel_minorant (μ0 := μ0) hM hLmeas hLnn hLbdd hZ0 hZtop hxpos hxM) ?_
  unfold indStep
  exact Measure.le_add_right le_rfl

/-! ### The mixture with a local kernel -/

/-- `K_ω = (1−ω) K_local + ω K_ind`, the proposed mixture of Q1. -/
noncomputable def mixtureKernel (ω : ENNReal) (Klocal Kind : Measure Ω) : Measure Ω :=
  (1 - ω) • Klocal + ω • Kind

/-- **Mixture coefficient `c_ω = ω Z/M`**: the local kernel contributes no minorisation, so the
mixture inherits `ω` times the independence coefficient. -/
theorem mixture_minorant {μ0 : Measure Ω} {L : Ω → ℝ} {M : ℝ} {ω : ENNReal} (hM : 0 < M)
    (hLmeas : Measurable L) (hLnn : ∀ y, 0 ≤ L y) (hLbdd : ∀ y, L y ≤ M)
    (hZ0 : priorZ μ0 L ≠ 0) (hZtop : priorZ μ0 L ≠ ⊤) {x : Ω} (hxpos : 0 < L x)
    (hxM : L x ≤ M) (Klocal : Measure Ω) :
    (ω * (priorZ μ0 L * ENNReal.ofReal M⁻¹)) • priorTarget μ0 L
      ≤ mixtureKernel ω Klocal (indKernel μ0 L x) := by
  have hind := indKernel_minorant (μ0 := μ0) hM hLmeas hLnn hLbdd hZ0 hZtop hxpos hxM
  have h1 : (ω * (priorZ μ0 L * ENNReal.ofReal M⁻¹)) • priorTarget μ0 L
      ≤ ω • indKernel μ0 L x := by
    rw [← smul_smul]
    refine Measure.le_iff'.mpr fun s => ?_
    rw [Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul]
    exact mul_le_mul_right ((Measure.le_iff'.mp hind) s) ω
  refine le_trans h1 ?_
  unfold mixtureKernel
  exact Measure.le_add_left le_rfl

/-! ## §3. The probability normalisation and the set-level contraction -/

/-- The normalised target is a probability measure when `0 < Z < ∞`. -/
theorem priorTarget_univ {μ0 : Measure Ω} {L : Ω → ℝ} (hZ0 : priorZ μ0 L ≠ 0)
    (hZtop : priorZ μ0 L ≠ ⊤) : priorTarget μ0 L Set.univ = 1 := by
  unfold priorTarget
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ]
  simp only [Measure.restrict_univ]
  change (priorZ μ0 L)⁻¹ * priorZ μ0 L = 1
  rw [ENNReal.inv_mul_cancel hZ0 hZtop]

/-- The full independence step has mass one. -/
theorem indStep_univ (μ0 : Measure Ω) [IsProbabilityMeasure μ0] [MeasurableSingletonClass Ω]
    (L : Ω → ℝ) (x : Ω) : indStep μ0 L x Set.univ = 1 := by
  unfold indStep
  rw [Measure.add_apply, Measure.smul_apply, smul_eq_mul]
  have hle := indKernel_univ_le_one μ0 L x
  rw [Measure.dirac_apply, Set.indicator_of_mem (Set.mem_univ x), Pi.one_apply, mul_one]
  exact add_tsub_cancel_of_le hle

/-- **The Doeblin contraction, set by set.**  A step that is a probability, preserves `π`, and
dominates `c • π` at every start is within `1 − c` of `π` in total variation:
`|K(x,A) − π(A)| ≤ 1 − c` for every measurable `A`. -/
theorem doeblin_tv_bound {π Kx : Measure Ω} {c : ENNReal}
    (hπ : π Set.univ = 1) (hK : Kx Set.univ = 1) (hc : c ≤ 1)
    (hminor : c • π ≤ Kx) {A : Set Ω} (hA : MeasurableSet A) :
    |(Kx A).toReal - (π A).toReal| ≤ 1 - c.toReal := by
  have hAc : MeasurableSet Aᶜ := hA.compl
  have hminorAc : c * π Aᶜ ≤ Kx Aᶜ := by
    have := (Measure.le_iff.mp hminor) Aᶜ hAc
    rwa [Measure.smul_apply] at this
  have hminorA : c * π A ≤ Kx A := by
    have := (Measure.le_iff.mp hminor) A hA
    rwa [Measure.smul_apply] at this
  have hπA : π A + π Aᶜ = 1 := by
    rw [measure_add_measure_compl hA, hπ]
  have hKA : Kx A + Kx Aᶜ = 1 := by
    rw [measure_add_measure_compl hA, hK]
  have hπA_le : π A ≤ 1 := by
    rw [← hπ]; exact measure_mono (Set.subset_univ A)
  have hKA_le : Kx A ≤ 1 := by
    rw [← hK]; exact measure_mono (Set.subset_univ A)
  have hπAc_le : π Aᶜ ≤ 1 := by
    rw [← hπ]; exact measure_mono (Set.subset_univ Aᶜ)
  have hKAc_le : Kx Aᶜ ≤ 1 := by
    rw [← hK]; exact measure_mono (Set.subset_univ Aᶜ)
  have hπ_ne : π A ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hπA_le
  have hK_ne : Kx A ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hKA_le
  have hπAc_ne : π Aᶜ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hπAc_le
  have hKAc_ne : Kx Aᶜ ≠ ⊤ := ne_top_of_le_ne_top ENNReal.one_ne_top hKAc_le
  set p : ℝ := (π A).toReal with hp
  set a : ℝ := (Kx A).toReal with ha
  set k : ℝ := c.toReal with hk
  have hk0 : 0 ≤ k := ENNReal.toReal_nonneg
  have hk1 : k ≤ 1 := by
    simpa [hk] using ENNReal.toReal_mono ENNReal.one_ne_top hc
  have hp0 : 0 ≤ p := ENNReal.toReal_nonneg
  have hp1 : p ≤ 1 := by
    simpa [hp] using ENNReal.toReal_mono ENNReal.one_ne_top hπA_le
  have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
  have ha1 : a ≤ 1 := by
    simpa [ha] using ENNReal.toReal_mono ENNReal.one_ne_top hKA_le
  have hlower : k * p ≤ a := by
    have := ENNReal.toReal_mono hK_ne hminorA
    rw [ENNReal.toReal_mul, ← hp, ← ha] at this
    exact this
  have hcAc : k * (1 - p) ≤ 1 - a := by
    have hcomp : (Kx Aᶜ).toReal = 1 - a := by
      have hsum : (Kx A).toReal + (Kx Aᶜ).toReal = 1 := by
        rw [← ENNReal.toReal_add hK_ne hKAc_ne, hKA, ENNReal.toReal_one]
      rw [← ha] at hsum
      linarith
    have hpAc : (π Aᶜ).toReal = 1 - p := by
      have hsum : (π A).toReal + (π Aᶜ).toReal = 1 := by
        rw [← ENNReal.toReal_add hπ_ne hπAc_ne, hπA, ENNReal.toReal_one]
      rw [← hp] at hsum
      linarith
    have hmono := ENNReal.toReal_mono hKAc_ne hminorAc
    rw [ENNReal.toReal_mul, hpAc, hcomp, ← hk] at hmono
    exact hmono
  have hupper : a - p ≤ 1 - k := by nlinarith
  have hlower' : -(1 - k) ≤ a - p := by nlinarith
  rw [abs_le]
  exact ⟨hlower', hupper⟩

/-- The unnormalised mass is at most `M` for a bounded likelihood. -/
theorem priorZ_le_of_bdd {μ0 : Measure Ω} [IsProbabilityMeasure μ0] {L : Ω → ℝ} {M : ℝ}
    (hLbdd : ∀ y, L y ≤ M) :
    priorZ μ0 L ≤ ENNReal.ofReal M := by
  unfold priorZ
  calc ∫⁻ y, ENNReal.ofReal (L y) ∂μ0 ≤ ∫⁻ _y, ENNReal.ofReal M ∂μ0 :=
        lintegral_mono fun y => ENNReal.ofReal_le_ofReal (hLbdd y)
    _ = ENNReal.ofReal M := by rw [lintegral_const, measure_univ, mul_one]

/-- **`Z/M ≤ 1`**, so the Doeblin coefficient is a legitimate probability defect. -/
theorem coefficient_le_one {Z : ENNReal} {M : ℝ} (hM : 0 < M) (hZ : Z ≤ ENNReal.ofReal M) :
    Z * ENNReal.ofReal M⁻¹ ≤ 1 := by
  calc Z * ENNReal.ofReal M⁻¹ ≤ ENNReal.ofReal M * ENNReal.ofReal M⁻¹ := by
        exact mul_le_mul_left hZ _
    _ = 1 := by
        rw [mul_comm (ENNReal.ofReal M) (ENNReal.ofReal M⁻¹),
          ← ENNReal.ofReal_mul (inv_nonneg.mpr hM.le),
          mul_comm M⁻¹ M, mul_inv_cancel₀ hM.ne', ENNReal.ofReal_one]

/-- **The step's TV contraction `1 − Z/M`.**  This is §3's `doeblin_tv_bound` instantiated at
`indStep`, its target and the coefficient `Z/M`. -/
theorem indStep_tv_bound {μ0 : Measure Ω} [IsProbabilityMeasure μ0]
    [MeasurableSingletonClass Ω] {L : Ω → ℝ} {M : ℝ} (hM : 0 < M) (hLmeas : Measurable L)
    (hLnn : ∀ y, 0 ≤ L y) (hLbdd : ∀ y, L y ≤ M) (hZ0 : priorZ μ0 L ≠ 0)
    (hZtop : priorZ μ0 L ≠ ⊤) {x : Ω} (hxpos : 0 < L x) (hxM : L x ≤ M)
    {A : Set Ω} (hA : MeasurableSet A) :
    |(indStep μ0 L x A).toReal - (priorTarget μ0 L A).toReal|
      ≤ 1 - (priorZ μ0 L * ENNReal.ofReal M⁻¹).toReal := by
  have hZM : priorZ μ0 L * ENNReal.ofReal M⁻¹ ≤ 1 :=
    coefficient_le_one hM (priorZ_le_of_bdd hLbdd)
  exact doeblin_tv_bound (priorTarget_univ hZ0 hZtop) (indStep_univ μ0 L x) hZM
    (indStep_minorant (μ0 := μ0) hM hLmeas hLnn hLbdd hZ0 hZtop hxpos hxM) hA

/-- The Doeblin coefficient is positive whenever `Z > 0`. -/
theorem minorant_coefficient_pos {Z : ENNReal} {M : ℝ} (hM : 0 < M) (hZ0 : Z ≠ 0) :
    0 < Z * ENNReal.ofReal M⁻¹ :=
  ENNReal.mul_pos hZ0 (ne_of_gt (ENNReal.ofReal_pos.mpr (inv_pos.mpr hM)))

/-- **The `O(1)` plateau keeps the coefficient `O(1)`.**  If the likelihood ceiling is at most
`C`, the coefficient is at least `Z/C`; with S0's plateau `C = O(1)` this is `Z/O(1)`, in
contrast with the sharp-Gibbs regime where the analogue collapses like `e^{−O(10^4)}`. -/
theorem coefficient_le_of_ceiling_le {Z : ENNReal} {M C : ℝ} (hM : 0 < M) (hMC : M ≤ C) :
    Z * ENNReal.ofReal C⁻¹ ≤ Z * ENNReal.ofReal M⁻¹ := by
  refine mul_le_mul_right ?_ Z
  exact ENNReal.ofReal_le_ofReal (inv_anti₀ hM hMC)

end BookProof.MCMC.PriorRefreshDoeblin
