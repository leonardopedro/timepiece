import Mathlib
import BookProof.OSReconstruction.SemigroupContinuity

/-!
# The generator of the transfer *semigroup*

`OSReconstruction.Generator` defines the generator through difference quotients converging along the
*punctured* filter `𝓝[≠] 0`, and `OSReconstruction.GeneratorClosed` proves it closed through the
fundamental theorem of calculus applied to the orbit `s ↦ P(s)z`, whose derivative `P(s)(A z)` is a
two-sided derivative at every real `s`.

Both choices are wrong for a Euclidean transfer matrix, which exists only for `τ ≥ 0`.  On that side
the orbit has a right derivative at interior points but no left derivative (`P(t + h) = P(t)P(h)`
needs `h ≥ 0`), and a limit along `𝓝[>] 0` does **not** upgrade to `𝓝[≠] 0`: there is no left-hand
information to supply.  So the forward-time generator needs its own domain, and this module builds
it, together with the closedness argument that goes with it:

* `HasGenRight`, `genDomainRight`, `generatorRight` — the same construction as `HasGen`,
  `genDomain` and `generator`, with `𝓝[>] 0` in place of `𝓝[≠] 0`.  Linearity of the difference
  quotient is filter-independent (`diffQuot_add`, `diffQuot_smul`), and the limits are unique, so
  the proofs are the same;
* `hasDerivWithinAt_physEvolRight` — the orbit has the *right* derivative `P(t)(A z)` within
  `Ioi t`: for `h > 0` the quotient of the translated vector is the translate of the quotient,
  `h⁻¹ • (P(t+h)z − P(t)z) = P(t)(h⁻¹ • (P(h)z − z))`;
* `physEvol_sub_eq_integral_right` — `P(τ)z − z = ∫₀^τ P(s)(A z) ds` for `τ ≥ 0`, from the
  right-derivative form of the fundamental theorem of calculus
  (`intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le`);
* `tendsto_average_physEvol_right` — `τ⁻¹ • ∫₀^τ P(s)y ds → y` as `τ → 0⁺`, from strong continuity
  at `0⁺` and contractivity;
* `generatorRight_isClosed` — the graph of `generatorRight` is closed;
* `generatorRight_inner_le_zero` — the generator is *dissipative*: `⟪A z, z⟫ ≤ 0` on its domain,
  the one-sided substitute for symmetry, forced by contractivity alone.

So closedness needs neither a resolvent nor a Laplace representation, contrary to the conjecture
recorded in `SemigroupContinuity`: the right-derivative fundamental theorem of calculus is enough.

## Boundary

The residual dependence on the two-sided hypothesis is in the *type* of the earlier definitions:
`hinv` ranges over all `τ : ℝ` because `physEvolCompletion` is built by `LinearMap.extendOfNorm`,
whose norm bound fails for `τ < 0`, and orbit continuity on `[0, τ]` is taken here from
`continuous_physEvolCompletion_apply`, which shifts by a negative time and so uses strong continuity
at `0` in the full filter `𝓝 0`.  A fully forward-only rebuild would restrict both, replacing that
continuity lemma by a one-sided version (right continuity at `0`, and for `h ∈ (0, t)`
`P(t)z − P(t−h)z = P(t−h)(P(h)z − z)`); nothing below would change.  Self-adjointness is a separate
question, and under the two-sided hypothesis it is vacuous (`TransferSelfAdjoint`).
-/

namespace BookProof.OSReconstruction

open BookProof.ReflectionPositivity
open Filter MeasureTheory Set
open scoped Topology RealInnerProductSpace Interval

noncomputable section

/-! ## The forward-time domain -/

/-- `z` is in the forward-time domain when the difference quotient converges as `τ → 0⁺`. -/
def HasGenRight (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (z : Hphys Λ) : Prop :=
  ∃ y : Hphys Λ, Tendsto (fun τ : ℝ => diffQuot Λ T hinv τ z) (𝓝[>] 0) (𝓝 y)

/-- The origin is in the forward-time domain, with generator value `0`. -/
theorem hasGenRight_zero (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F) :
    HasGenRight Λ T hinv (0 : Hphys Λ) := by
  refine ⟨0, ?_⟩
  simpa only [diffQuot_zero] using
    (tendsto_const_nhds : Tendsto (fun _ : ℝ => (0 : Hphys Λ)) (𝓝[>] 0) (𝓝 0))

/-- The forward-time domain is closed under addition. -/
theorem hasGenRight_add (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    {z w : Hphys Λ} (hz : HasGenRight Λ T hinv z) (hw : HasGenRight Λ T hinv w) :
    HasGenRight Λ T hinv (z + w) := by
  obtain ⟨y, hy⟩ := hz
  obtain ⟨y', hy'⟩ := hw
  refine ⟨y + y', ?_⟩
  refine (hy.add hy').congr' ?_
  exact Eventually.of_forall fun τ => (diffQuot_add Λ T hinv τ z w).symm

/-- The forward-time domain is closed under scalar multiplication. -/
theorem hasGenRight_smul (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (c : ℝ) {z : Hphys Λ} (hz : HasGenRight Λ T hinv z) :
    HasGenRight Λ T hinv (c • z) := by
  obtain ⟨y, hy⟩ := hz
  refine ⟨c • y, ?_⟩
  refine (hy.const_smul c).congr' ?_
  exact Eventually.of_forall fun τ => (diffQuot_smul Λ T hinv τ c z).symm

/-- **The forward-time domain of the generator** as a real submodule of `ℋ`. -/
def genDomainRight (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F) :
    Submodule ℝ (Hphys Λ) where
  carrier := {z | HasGenRight Λ T hinv z}
  add_mem' := fun hz hw => hasGenRight_add Λ T hinv hz hw
  zero_mem' := hasGenRight_zero Λ T hinv
  smul_mem' := fun c _ hz => hasGenRight_smul Λ T hinv c hz

/-- Membership in the forward-time domain is convergence of the quotient at `0⁺`. -/
@[simp]
theorem mem_genDomainRight (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (z : Hphys Λ) : z ∈ genDomainRight Λ T hinv ↔ HasGenRight Λ T hinv z :=
  Iff.rfl

/-- The forward-time generator's value at a domain point, as a chosen limit. -/
def genValueRight (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (z : genDomainRight Λ T hinv) : Hphys Λ :=
  Classical.choose z.2

/-- The defining limit property of `genValueRight`. -/
theorem genValueRight_tendsto (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (z : genDomainRight Λ T hinv) :
    Tendsto (fun τ : ℝ => diffQuot Λ T hinv τ (z : Hphys Λ)) (𝓝[>] 0)
      (𝓝 (genValueRight Λ T hinv z)) :=
  Classical.choose_spec z.2

/-- `genValueRight` is additive, by uniqueness of limits. -/
theorem genValueRight_add (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (z w : genDomainRight Λ T hinv) :
    genValueRight Λ T hinv (z + w) = genValueRight Λ T hinv z + genValueRight Λ T hinv w := by
  refine tendsto_nhds_unique (genValueRight_tendsto Λ T hinv (z + w)) ?_
  have h : Tendsto (fun τ : ℝ => diffQuot Λ T hinv τ (z : Hphys Λ)
      + diffQuot Λ T hinv τ (w : Hphys Λ)) (𝓝[>] 0)
      (𝓝 (genValueRight Λ T hinv z + genValueRight Λ T hinv w)) :=
    (genValueRight_tendsto Λ T hinv z).add (genValueRight_tendsto Λ T hinv w)
  refine h.congr' ?_
  exact Eventually.of_forall fun τ =>
    (diffQuot_add Λ T hinv τ (z : Hphys Λ) (w : Hphys Λ)).symm

/-- `genValueRight` is homogeneous, by uniqueness of limits. -/
theorem genValueRight_smul (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (c : ℝ) (z : genDomainRight Λ T hinv) :
    genValueRight Λ T hinv (c • z) = c • genValueRight Λ T hinv z := by
  refine tendsto_nhds_unique (genValueRight_tendsto Λ T hinv (c • z)) ?_
  have h : Tendsto (fun τ : ℝ => c • diffQuot Λ T hinv τ (z : Hphys Λ)) (𝓝[>] 0)
      (𝓝 (c • genValueRight Λ T hinv z)) := (genValueRight_tendsto Λ T hinv z).const_smul c
  refine h.congr' ?_
  exact Eventually.of_forall fun τ => (diffQuot_smul Λ T hinv τ c (z : Hphys Λ)).symm

/-- The forward-time generator's action as a linear map on its domain. -/
def genFunRight (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F) :
    genDomainRight Λ T hinv →ₗ[ℝ] Hphys Λ where
  toFun := genValueRight Λ T hinv
  map_add' := genValueRight_add Λ T hinv
  map_smul' := genValueRight_smul Λ T hinv

/-- **The generator of the forward-time transfer semigroup.** -/
def generatorRight (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F) :
    Hphys Λ →ₗ.[ℝ] Hphys Λ where
  domain := genDomainRight Λ T hinv
  toFun := genFunRight Λ T hinv

/-- The defining property of the forward-time generator. -/
theorem generatorRight_apply_tendsto (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (z : (generatorRight Λ T hinv).domain) :
    Tendsto (fun τ : ℝ => diffQuot Λ T hinv τ (z : Hphys Λ)) (𝓝[>] 0)
      (𝓝 (generatorRight Λ T hinv z)) :=
  genValueRight_tendsto Λ T hinv z

/-! ## The right derivative of the orbit -/

/-- **The orbit of a forward-time domain vector has a right derivative at every time**, namely
`P(t)(A z)`.

For `h > 0` the semigroup law gives `P(t + h)z − P(t)z = P(t)(P(h)z − z)`, so the difference
quotient of the orbit is the image under the continuous map `P(t)` of the difference quotient at
`0`, which converges to `A z` along `𝓝[>] 0`.  No left derivative is involved. -/
theorem hasDerivWithinAt_physEvolRight (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (z : (generatorRight Λ T hinv).domain) (t : ℝ) :
    HasDerivWithinAt (fun s : ℝ => physEvolCompletion Λ T hinv s (z : Hphys Λ))
      (physEvolCompletion Λ T hinv t (generatorRight Λ T hinv z)) (Ioi t) t := by
  have hq : Tendsto
      (fun h : ℝ => h⁻¹ • (physEvolCompletion Λ T hinv h (z : Hphys Λ) - (z : Hphys Λ)))
      (𝓝[>] 0) (𝓝 (generatorRight Λ T hinv z)) :=
    generatorRight_apply_tendsto Λ T hinv z
  have hpc : Tendsto (physEvolCompletion Λ T hinv t) (𝓝 (generatorRight Λ T hinv z))
      (𝓝 (physEvolCompletion Λ T hinv t (generatorRight Λ T hinv z))) :=
    (physEvolCompletion Λ T hinv t).continuous.tendsto _
  have hmain : Tendsto
      (fun h : ℝ => physEvolCompletion Λ T hinv t
        (h⁻¹ • (physEvolCompletion Λ T hinv h (z : Hphys Λ) - (z : Hphys Λ))))
      (𝓝[>] 0) (𝓝 (physEvolCompletion Λ T hinv t (generatorRight Λ T hinv z))) :=
    hpc.comp hq
  -- reindex along `h ↦ h - t`, which sends `𝓝[Ioi t] t` to `𝓝[>] 0`
  have hsub : Tendsto (fun y : ℝ => y - t) (𝓝[Ioi t] t) (𝓝[>] (0 : ℝ)) := by
    have h1 : Tendsto (fun y : ℝ => y - t) (𝓝[Ioi t] t) (𝓝 (0 : ℝ)) := by
      have hcont : Continuous fun y : ℝ => y - t := continuous_id.sub continuous_const
      have h : Tendsto (fun y : ℝ => y - t) (𝓝[Ioi t] t) (𝓝 (t - t)) := hcont.continuousWithinAt
      rwa [sub_self] at h
    change Tendsto (fun y : ℝ => y - t) (𝓝[Ioi t] t) (𝓝 (0 : ℝ) ⊓ 𝓟 (Ioi 0))
    rw [tendsto_inf, tendsto_principal]
    exact ⟨h1, by
      filter_upwards [self_mem_nhdsWithin] with y hy
      exact sub_pos.2 (mem_Ioi.mp hy)⟩
  rw [hasDerivWithinAt_iff_tendsto_slope,
    show Ioi t \ {t} = Ioi t from diff_singleton_eq_self (by simp)]
  refine (hmain.comp hsub).congr' ?_
  filter_upwards [self_mem_nhdsWithin] with y hy
  have hcomp : physEvolCompletion Λ T hinv y (z : Hphys Λ)
      = physEvolCompletion Λ T hinv t (physEvolCompletion Λ T hinv (y - t) (z : Hphys Λ)) := by
    conv_lhs => rw [show y = t + (y - t) from by ring]
    rw [physEvolCompletion_comp_apply]
  have hslope : slope (fun s : ℝ => physEvolCompletion Λ T hinv s (z : Hphys Λ)) t y
      = (y - t)⁻¹ • (physEvolCompletion Λ T hinv y (z : Hphys Λ)
        - physEvolCompletion Λ T hinv t (z : Hphys Λ)) := by
    rw [slope_def_module]
  rw [hslope, hcomp, ← map_sub, ← map_smul]
  rfl

/-! ## The integral representation, for nonnegative times -/

/-- **The integral representation for a one-sided semigroup**: for `τ ≥ 0` and a domain vector,
`∫₀^τ P(s)(A z) ds = P(τ)z − z`.

This is the fundamental theorem of calculus in its right-derivative form, fed by
`hasDerivWithinAt_physEvolRight`.  Only interior right derivatives and continuity on `[0, τ]` are
required, so no left derivative of the orbit is ever taken. -/
theorem physEvol_sub_eq_integral_right (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (hcont : ∀ F : Observable, Continuous fun τ : ℝ => osBilin Λ.ω (T τ F) F)
    (z : (generatorRight Λ T hinv).domain) (τ : ℝ) (hτ : 0 ≤ τ) :
    ∫ s in (0 : ℝ)..τ, physEvolCompletion Λ T hinv s (generatorRight Λ T hinv z)
      = physEvolCompletion Λ T hinv τ (z : Hphys Λ) - (z : Hphys Λ) := by
  have hcurve : Continuous fun s : ℝ => physEvolCompletion Λ T hinv s (z : Hphys Λ) :=
    continuous_physEvolCompletion_apply Λ T hinv hcont _
  have hint : IntervalIntegrable
      (fun s : ℝ => physEvolCompletion Λ T hinv s (generatorRight Λ T hinv z)) volume 0 τ :=
    (continuous_physEvolCompletion_apply Λ T hinv hcont _).intervalIntegrable 0 τ
  have h := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hτ hcurve.continuousOn
    (fun x _ => hasDerivWithinAt_physEvolRight Λ T hinv z x) hint
  simpa [physEvolCompletion_zero] using h

/-! ## Averaging a curve that is right-continuous at `0` -/

/-- **The average converges to the value at `0` from the right.**  Strong continuity at `0⁺` gives
`‖P(s)y − y‖ < ε/2` on `(0, δ)`, and the average of `P(·)y − y` over `(0, τ]` is then bounded by
`ε/2` for `τ < δ`, by the norm bound for the vector-valued integral. -/
theorem tendsto_average_physEvol_right (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (hcont : ∀ F : Observable, Continuous fun τ : ℝ => osBilin Λ.ω (T τ F) F)
    (y : Hphys Λ) :
    Tendsto (fun τ : ℝ => τ⁻¹ • ∫ s in (0 : ℝ)..τ, physEvolCompletion Λ T hinv s y)
      (𝓝[>] 0) (𝓝 y) := by
  have hcurve : Continuous fun s : ℝ => physEvolCompletion Λ T hinv s y :=
    continuous_physEvolCompletion_apply Λ T hinv hcont y
  have hint : ∀ a b : ℝ, IntervalIntegrable
      (fun s : ℝ => physEvolCompletion Λ T hinv s y) volume a b :=
    fun a b => hcurve.intervalIntegrable a b
  have hsplit : ∀ τ : ℝ,
      (∫ s in (0 : ℝ)..τ, physEvolCompletion Λ T hinv s y)
        = (∫ s in (0 : ℝ)..τ, (physEvolCompletion Λ T hinv s y - y)) + τ • y := by
    intro τ
    have h2 : (∫ s in (0 : ℝ)..τ, physEvolCompletion Λ T hinv s y)
        = ∫ s in (0 : ℝ)..τ, ((physEvolCompletion Λ T hinv s y - y) + y) :=
      intervalIntegral.integral_congr fun s _ => by abel
    rw [h2, intervalIntegral.integral_add ((hint 0 τ).sub intervalIntegrable_const)
      intervalIntegrable_const, intervalIntegral.integral_const]
    simp
  rw [Metric.tendsto_nhds]
  intro ε hε
  -- strong continuity at `0⁺` gives `‖P(s)y − y‖ < ε/2` on a right neighbourhood of `0`
  have hsmall : ∀ᶠ s in 𝓝[>] (0 : ℝ), ‖physEvolCompletion Λ T hinv s y - y‖ < ε / 2 := by
    have h := Metric.tendsto_nhds.mp (tendsto_physEvolCompletion_right Λ T hinv hcont y)
      (ε / 2) (by linarith)
    filter_upwards [h] with s hs
    simpa [dist_eq_norm] using hs
  obtain ⟨δ, hδpos, hδsub⟩ := Metric.mem_nhdsWithin_iff.mp
    (show {s : ℝ | ‖physEvolCompletion Λ T hinv s y - y‖ < ε / 2} ∈ 𝓝[>] (0 : ℝ) from hsmall)
  have hevδ : ∀ᶠ τ in 𝓝[>] (0 : ℝ), τ < δ := by
    have hball : ∀ᶠ τ in 𝓝 (0 : ℝ), τ < δ := by
      filter_upwards [Metric.ball_mem_nhds (0 : ℝ) hδpos] with τ hτ
      exact (abs_lt.1 (by simpa [Real.dist_eq] using hτ)).2
    exact hball.filter_mono nhdsWithin_le_nhds
  filter_upwards [self_mem_nhdsWithin, hevδ] with τ hτ hτδ
  have hτpos : 0 < τ := hτ
  have hdiff : τ⁻¹ • (∫ s in (0 : ℝ)..τ, physEvolCompletion Λ T hinv s y) - y
      = τ⁻¹ • ∫ s in (0 : ℝ)..τ, (physEvolCompletion Λ T hinv s y - y) := by
    rw [hsplit τ, smul_add, smul_smul, inv_mul_cancel₀ (ne_of_gt hτpos), one_smul,
      add_sub_cancel_right]
  have hbound : ‖∫ s in (0 : ℝ)..τ, (physEvolCompletion Λ T hinv s y - y)‖
      ≤ (ε / 2) * |τ| := by
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := ε / 2) ?_).trans_eq ?_
    · intro s hs
      have hsIoo : s ∈ Ioo (0 : ℝ) δ := by
        rcases Set.mem_uIoc.1 hs with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · exact ⟨h1, lt_of_le_of_lt h2 hτδ⟩
        · exact absurd (lt_trans hτpos h1) (not_lt.2 h2)
      refine le_of_lt (hδsub ⟨?_, hsIoo.1⟩)
      rw [Metric.mem_ball, Real.dist_eq, sub_zero, abs_of_pos hsIoo.1]
      exact hsIoo.2
    · rw [sub_zero]
  have hdist : dist (τ⁻¹ • (∫ s in (0 : ℝ)..τ, physEvolCompletion Λ T hinv s y)) y
      = ‖τ⁻¹ • ∫ s in (0 : ℝ)..τ, (physEvolCompletion Λ T hinv s y - y)‖ := by
    rw [dist_eq_norm, hdiff]
  rw [hdist, norm_smul, Real.norm_eq_abs, abs_inv]
  refine lt_of_le_of_lt ?_ (by linarith : ε / 2 < ε)
  calc |τ|⁻¹ * ‖∫ s in (0 : ℝ)..τ, (physEvolCompletion Λ T hinv s y - y)‖
      ≤ |τ|⁻¹ * ((ε / 2) * |τ|) :=
        mul_le_mul_of_nonneg_left hbound (by positivity)
    _ = ε / 2 := by
        rw [mul_comm (ε / 2) |τ|, ← mul_assoc,
          inv_mul_cancel₀ (abs_ne_zero.2 (ne_of_gt hτpos)), one_mul]

/-! ## Closedness, from the one-sided representation -/

/-- **The forward-time generator has closed graph**, proved with right derivatives only.

If `uₙ → z₀` in the graph norm, the integral representation passes to the limit at every `τ ≥ 0`
by contractivity; dividing by `τ` exhibits the difference quotient of `z₀` as the average of the
strongly right-continuous curve `P(·)y`, which converges to `y` as `τ → 0⁺`. -/
theorem generatorRight_isClosed (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (hcont : ∀ F : Observable, Continuous fun τ : ℝ => osBilin Λ.ω (T τ F) F) :
    ∀ (u : ℕ → (generatorRight Λ T hinv).domain) {z₀ y : Hphys Λ},
      Tendsto (fun n => (u n : Hphys Λ)) atTop (𝓝 z₀) →
      Tendsto (fun n => generatorRight Λ T hinv (u n)) atTop (𝓝 y) →
      ∃ h : HasGenRight Λ T hinv z₀, generatorRight Λ T hinv ⟨z₀, h⟩ = y := by
  intro u z₀ y hu hy
  have hmain : ∀ τ : ℝ, 0 ≤ τ →
      physEvolCompletion Λ T hinv τ z₀ - z₀
        = ∫ s in (0 : ℝ)..τ, physEvolCompletion Λ T hinv s y := by
    intro τ hτ
    have hleft : Tendsto (fun n => physEvolCompletion Λ T hinv τ (u n) - (u n : Hphys Λ))
        atTop (𝓝 (physEvolCompletion Λ T hinv τ z₀ - z₀)) :=
      (((physEvolCompletion Λ T hinv τ).continuous.tendsto z₀).comp hu).sub hu
    have hlim : Tendsto (fun n => |τ| * ‖generatorRight Λ T hinv (u n) - y‖) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => ‖generatorRight Λ T hinv (u n) - y‖) atTop (𝓝 0) := by
        have hsub : Tendsto (fun n => generatorRight Λ T hinv (u n) - y) atTop (𝓝 (y - y)) :=
          hy.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop (𝓝 y))
        simpa using hsub.norm
      simpa using h1.const_mul |τ|
    have hright : Tendsto
        (fun n => ∫ s in (0 : ℝ)..τ,
          physEvolCompletion Λ T hinv s (generatorRight Λ T hinv (u n)))
        atTop (𝓝 (∫ s in (0 : ℝ)..τ, physEvolCompletion Λ T hinv s y)) := by
      refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
      have hb : ∀ n,
          ‖(∫ s in (0 : ℝ)..τ, physEvolCompletion Λ T hinv s (generatorRight Λ T hinv (u n)))
            - (∫ s in (0 : ℝ)..τ, physEvolCompletion Λ T hinv s y)‖
            ≤ |τ| * ‖generatorRight Λ T hinv (u n) - y‖ := by
        intro n
        rw [← intervalIntegral.integral_sub
          ((continuous_physEvolCompletion_apply Λ T hinv hcont _).intervalIntegrable 0 τ)
          ((continuous_physEvolCompletion_apply Λ T hinv hcont _).intervalIntegrable 0 τ)]
        refine (intervalIntegral.norm_integral_le_of_norm_le_const
          (C := ‖generatorRight Λ T hinv (u n) - y‖) ?_).trans_eq ?_
        · intro s _
          rw [← map_sub]
          exact physEvolCompletion_contractive Λ T hinv s _
        · rw [sub_zero, mul_comm]
      rw [Metric.tendsto_atTop] at hlim ⊢
      intro ε hε
      obtain ⟨N, hN⟩ := hlim ε hε
      refine ⟨N, fun n hn => ?_⟩
      have hlt := hN n hn
      rw [Real.dist_eq, sub_zero,
        abs_of_nonneg (mul_nonneg (abs_nonneg _) (norm_nonneg _))] at hlt
      simpa [Real.dist_eq] using lt_of_le_of_lt (hb n) hlt
    exact tendsto_nhds_unique hleft
      (hright.congr' (Eventually.of_forall fun n =>
        physEvol_sub_eq_integral_right Λ T hinv hcont (u n) τ hτ))
  have hquot : (fun τ : ℝ => diffQuot Λ T hinv τ z₀)
      =ᶠ[𝓝[>] 0]
        (fun τ : ℝ => τ⁻¹ • ∫ s in (0 : ℝ)..τ, physEvolCompletion Λ T hinv s y) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    change τ⁻¹ • (physEvolCompletion Λ T hinv τ z₀ - z₀)
      = τ⁻¹ • ∫ s in (0 : ℝ)..τ, physEvolCompletion Λ T hinv s y
    rw [hmain τ hτ.le]
  have hlim : Tendsto (fun τ : ℝ => diffQuot Λ T hinv τ z₀) (𝓝[>] 0) (𝓝 y) :=
    (tendsto_average_physEvol_right Λ T hinv hcont y).congr' hquot.symm
  have hgen : HasGenRight Λ T hinv z₀ := ⟨y, hlim⟩
  exact ⟨hgen, tendsto_nhds_unique (genValueRight_tendsto Λ T hinv ⟨z₀, hgen⟩) hlim⟩

/-! ## Dissipativity: the one-sided substitute for symmetry -/

/-- **The forward-time generator is dissipative**: `⟪A z, z⟫ ≤ 0` throughout its domain.

`P(τ)` is a contraction for every `τ`, so `⟪P(τ)z, z⟫ ≤ ‖P(τ)z‖ ‖z‖ ≤ ⟪z, z⟫` by
Cauchy–Schwarz, and the difference quotient of this inequality converges to `⟪A z, z⟫` along
`𝓝[>] 0`.  Only `τ ≥ 0` is used, which is why this replaces `generator_isSymmetric` in the
forward-time theory: a self-adjoint `P(τ)` would force `P ≡ 1` (`physEvolCompletion_eq_one`). -/
theorem generatorRight_inner_le_zero (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (z : (generatorRight Λ T hinv).domain) :
    ⟪generatorRight Λ T hinv z, (z : Hphys Λ)⟫ ≤ 0 := by
  have hq : Tendsto (fun τ : ℝ => diffQuot Λ T hinv τ (z : Hphys Λ)) (𝓝[>] 0)
      (𝓝 (generatorRight Λ T hinv z)) :=
    generatorRight_apply_tendsto Λ T hinv z
  have hinner : Tendsto (fun τ : ℝ => ⟪diffQuot Λ T hinv τ (z : Hphys Λ), (z : Hphys Λ)⟫)
      (𝓝[>] 0) (𝓝 ⟪generatorRight Λ T hinv z, (z : Hphys Λ)⟫) :=
    hq.inner tendsto_const_nhds
  refine le_of_tendsto_of_tendsto hinner tendsto_const_nhds ?_
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  have hquot : ⟪diffQuot Λ T hinv τ (z : Hphys Λ), (z : Hphys Λ)⟫
      = τ⁻¹ * (⟪physEvolCompletion Λ T hinv τ (z : Hphys Λ), (z : Hphys Λ)⟫
        - ⟪(z : Hphys Λ), (z : Hphys Λ)⟫) := by
    rw [diffQuot, real_inner_smul_left, inner_sub_left]
  rw [hquot]
  refine mul_nonpos_of_nonneg_of_nonpos (inv_nonneg.2 (le_of_lt hτ)) (sub_nonpos.2 ?_)
  calc ⟪physEvolCompletion Λ T hinv τ (z : Hphys Λ), (z : Hphys Λ)⟫
      ≤ ‖physEvolCompletion Λ T hinv τ (z : Hphys Λ)‖ * ‖(z : Hphys Λ)‖ := real_inner_le_norm _ _
    _ ≤ ‖(z : Hphys Λ)‖ * ‖(z : Hphys Λ)‖ :=
        mul_le_mul_of_nonneg_right (physEvolCompletion_contractive Λ T hinv τ _) (norm_nonneg _)
    _ = ⟪(z : Hphys Λ), (z : Hphys Λ)⟫ := (real_inner_self_eq_norm_mul_norm _).symm

end

end BookProof.OSReconstruction
