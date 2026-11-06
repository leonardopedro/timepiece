import Mathlib
import BookProof.OSReconstruction.Generator

/-!
# Closedness of the generator, from the integral representation

`OSReconstruction.Generator` builds the generator `A` of the transfer semigroup `P` as the limit of
the difference quotients and proves it symmetric (given self-adjoint `P(τ)`), leaving closedness
open.  This module closes it, by the standard route: the difference quotients have an *integral
representation*,

`P(τ) z − z = ∫₀^τ P(s) (A z) ds`   for `z ∈ D(A)`,

(`physEvol_sub_eq_integral`), obtained from the fundamental theorem of calculus applied to the
orbit `s ↦ P(s) z`, whose derivative is `P(s)(A z)` (`hasDerivAt_physEvol`).  The orbit is
differentiable because the quotient of the translated vector is the translate of the quotient.

With the representation, closedness is immediate:

* if `zₙ → z₀` in `ℋ` and `A zₙ → y`, then `P(τ) zₙ − zₙ → P(τ) z₀ − z₀` and, by
  `∫₀^τ P(s)(A zₙ) ds → ∫₀^τ P(s) y ds`, the identity passes to the limit (`hmain`);
* the passage of the integral is *contractivity*, not dominated convergence: the difference of the
  two integrals is at most `|τ| ‖A zₙ − y‖`, because `P(s)` is a contraction
  (`hbound`);
* dividing the limit identity by `τ` and letting `τ → 0` gives `z₀ ∈ D(A)` with `A z₀ = y`: the
  average of a strongly continuous curve converges to its value at `0`
  (`tendsto_average_physEvol`), again by contractivity alone.

So the graph is closed (`generator_isClosed`).  What this does *not* give is self-adjointness: a
closed symmetric operator is symmetric, and self-adjointness needs the deficiency indices or the
integral representation of the resolvent.  The step supplied here is exactly the one `softmodes.md`
records as missing.

The hypotheses are the ones the previous two modules already carry: contractivity in both time
directions (`hinv`) and continuity of the two-point function (`hcont`), from which strong
continuity on `ℋ` is derived.

The orbit derivative used here is two-sided, because the punctured filter `𝓝[≠] 0` that defines
the domain sees both signs.  For a Euclidean transfer matrix only `τ ≥ 0` exists, and
`OSReconstruction.SemigroupGenerator` re-proves closedness in that setting: the same argument runs
with the *right* derivative at interior times, and the one-sided integral representation gives a
closed generator on the one-sided domain.  No resolvent or Laplace representation is required.
-/

namespace BookProof.OSReconstruction

open BookProof.ReflectionPositivity
open Filter MeasureTheory Set
open scoped Topology RealInnerProductSpace Interval

noncomputable section

/-! ## The orbit of a domain vector -/

/-- The group law in application form: `P(s)(P(t)z) = P(s+t)z`. -/
theorem physEvolCompletion_comp_apply (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (s t : ℝ) (z : Hphys Λ) :
    physEvolCompletion Λ T hinv s (physEvolCompletion Λ T hinv t z)
      = physEvolCompletion Λ T hinv (s + t) z := by
  rw [← ContinuousLinearMap.comp_apply, ← physEvolCompletion_add]

/-- Strong continuity in the time variable, for a fixed vector: `s ↦ P(s)w` is continuous.  The
proof writes `P(s)w = P(t)(P(s−t)w)` and uses continuity of `P(t)` and strong continuity at `0`. -/
theorem continuous_physEvolCompletion_apply (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (hcont : ∀ F : Observable, Continuous fun τ : ℝ => osBilin Λ.ω (T τ F) F)
    (w : Hphys Λ) :
    Continuous fun s : ℝ => physEvolCompletion Λ T hinv s w := by
  refine continuous_iff_continuousAt.2 fun t => ?_
  have hshift : Tendsto (fun s : ℝ => s - t) (𝓝 t) (𝓝 0) := by
    simpa using (tendsto_id.sub tendsto_const_nhds :
      Tendsto (fun s : ℝ => s - t) (𝓝 t) (𝓝 (t - t)))
  have hq : Tendsto (fun s : ℝ => physEvolCompletion Λ T hinv (s - t) w) (𝓝 t) (𝓝 w) :=
    (tendsto_physEvolCompletion Λ T hinv hcont w).comp hshift
  have hpc : Tendsto (physEvolCompletion Λ T hinv t) (𝓝 w)
      (𝓝 (physEvolCompletion Λ T hinv t w)) :=
    (physEvolCompletion Λ T hinv t).continuous.tendsto w
  refine (hpc.comp hq).congr' (Eventually.of_forall fun s => ?_)
  change physEvolCompletion Λ T hinv t (physEvolCompletion Λ T hinv (s - t) w)
    = physEvolCompletion Λ T hinv s w
  rw [physEvolCompletion_comp_apply, show t + (s - t) = s from by ring]

/-- **The orbit of a domain vector is differentiable**, with derivative `P(t)(A z)`: the quotient
of the translated vector is the translate of the quotient. -/
theorem hasDerivAt_physEvol (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (z : (generator Λ T hinv).domain) (t : ℝ) :
    HasDerivAt (fun s : ℝ => physEvolCompletion Λ T hinv s (z : Hphys Λ))
      (physEvolCompletion Λ T hinv t (generator Λ T hinv z)) t := by
  rw [hasDerivAt_iff_tendsto_slope_zero]
  have hpc : Tendsto (physEvolCompletion Λ T hinv t) (𝓝 (generator Λ T hinv z))
      (𝓝 (physEvolCompletion Λ T hinv t (generator Λ T hinv z))) :=
    (physEvolCompletion Λ T hinv t).continuous.tendsto _
  refine (hpc.comp (generator_apply_tendsto Λ T hinv z)).congr'
    (Eventually.of_forall fun h => ?_)
  change physEvolCompletion Λ T hinv t
      (h⁻¹ • (physEvolCompletion Λ T hinv h (z : Hphys Λ) - (z : Hphys Λ)))
    = h⁻¹ • (physEvolCompletion Λ T hinv (t + h) (z : Hphys Λ)
      - physEvolCompletion Λ T hinv t (z : Hphys Λ))
  rw [map_smul, map_sub, physEvolCompletion_comp_apply]

/-! ## The integral representation -/

/-- **The integral representation of the difference quotients**: for a domain vector,
`∫₀^τ P(s)(A z) ds = P(τ)z − z`.  This is the fundamental theorem of calculus applied to the
orbit, whose derivative is `hasDerivAt_physEvol`. -/
theorem physEvol_sub_eq_integral (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (hcont : ∀ F : Observable, Continuous fun τ : ℝ => osBilin Λ.ω (T τ F) F)
    (z : (generator Λ T hinv).domain) (τ : ℝ) :
    ∫ s in (0 : ℝ)..τ, physEvolCompletion Λ T hinv s (generator Λ T hinv z)
      = physEvolCompletion Λ T hinv τ (z : Hphys Λ) - (z : Hphys Λ) := by
  have hderiv : ∀ x ∈ uIcc (0 : ℝ) τ,
      HasDerivAt (fun s : ℝ => physEvolCompletion Λ T hinv s (z : Hphys Λ))
        (physEvolCompletion Λ T hinv x (generator Λ T hinv z)) x :=
    fun x _ => hasDerivAt_physEvol Λ T hinv z x
  have hint : IntervalIntegrable
      (fun s : ℝ => physEvolCompletion Λ T hinv s (generator Λ T hinv z)) volume 0 τ :=
    (continuous_physEvolCompletion_apply Λ T hinv hcont _).intervalIntegrable 0 τ
  have h := intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv hint
  simpa [physEvolCompletion_zero] using h

/-! ## Averaging a strongly continuous curve

This is the only analytic input of the closedness argument: `τ⁻¹ • ∫₀^τ f(s) ds → f(0)` for a
strongly continuous curve with `f(0) = y`.  Contractivity replaces dominated convergence: the
difference of the average and `y` is bounded by the supremum of `‖f(s) − y‖` over the interval,
which is small by strong continuity. -/

/-- **The average of a strongly continuous curve converges to its value at `0`.** -/
theorem tendsto_average_physEvol (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (hcont : ∀ F : Observable, Continuous fun τ : ℝ => osBilin Λ.ω (T τ F) F)
    (y : Hphys Λ) :
    Tendsto (fun τ : ℝ => τ⁻¹ • ∫ s in (0 : ℝ)..τ, physEvolCompletion Λ T hinv s y)
      (𝓝[≠] 0) (𝓝 y) := by
  have hcurve : Continuous fun s : ℝ => physEvolCompletion Λ T hinv s y :=
    continuous_physEvolCompletion_apply Λ T hinv hcont y
  have hint : ∀ a b : ℝ, IntervalIntegrable
      (fun s : ℝ => physEvolCompletion Λ T hinv s y) volume a b :=
    fun a b => hcurve.intervalIntegrable a b
  -- split the integral as `∫(f − y) + ∫ y = ∫(f − y) + τ • y`
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
  -- strong continuity at `0`: eventually `‖P(s)y − y‖ < ε/2`
  have hnorm : Tendsto (fun s : ℝ => ‖physEvolCompletion Λ T hinv s y - y‖) (𝓝 0) (𝓝 0) := by
    have hsub : Tendsto (fun s : ℝ => physEvolCompletion Λ T hinv s y - y) (𝓝 0) (𝓝 (y - y)) :=
      (tendsto_physEvolCompletion Λ T hinv hcont y).sub
        (tendsto_const_nhds : Tendsto (fun _ : ℝ => y) (𝓝 0) (𝓝 y))
    simpa using hsub.norm
  have hev : ∀ᶠ s in 𝓝 (0 : ℝ), ‖physEvolCompletion Λ T hinv s y - y‖ < ε / 2 := by
    have h := Metric.tendsto_nhds.mp hnorm (ε / 2) (by linarith)
    simpa using h
  obtain ⟨δ, hδpos, hδ⟩ := Metric.eventually_nhds_iff.mp hev
  have hball : ∀ᶠ s in 𝓝[≠] (0 : ℝ), s ∈ Metric.ball (0 : ℝ) δ :=
    Filter.Eventually.filter_mono nhdsWithin_le_nhds (Metric.ball_mem_nhds (0 : ℝ) hδpos)
  filter_upwards [hball, self_mem_nhdsWithin] with τ hτ hτne
  -- the average minus `y` is the average of the centred curve
  have hdiff : τ⁻¹ • (∫ s in (0 : ℝ)..τ, physEvolCompletion Λ T hinv s y) - y
      = τ⁻¹ • ∫ s in (0 : ℝ)..τ, (physEvolCompletion Λ T hinv s y - y) := by
    rw [hsplit τ, smul_add, smul_smul, inv_mul_cancel₀ hτne, one_smul, add_sub_cancel_right]
  have hbound : ‖∫ s in (0 : ℝ)..τ, (physEvolCompletion Λ T hinv s y - y)‖
      ≤ (ε / 2) * |τ| := by
    refine (intervalIntegral.norm_integral_le_of_norm_le_const (C := ε / 2) ?_).trans_eq ?_
    · intro s hs
      have hmem := Set.mem_uIoc.1 hs
      have hτabs : |τ| < δ := by
        simpa [Real.dist_eq] using hτ
      have hsabs : |s| ≤ |τ| := by
        rcases hmem with ⟨h1, h2⟩ | ⟨h1, h2⟩
        · rw [abs_of_pos h1, abs_of_pos (lt_of_lt_of_le h1 h2)]
          exact h2
        · rw [abs_of_nonpos h2, abs_of_nonpos (le_of_lt (lt_of_lt_of_le h1 h2))]
          linarith
      have hsbound : ‖physEvolCompletion Λ T hinv s y - y‖ < ε / 2 :=
        hδ (by rw [Real.dist_eq, sub_zero]; exact lt_of_le_of_lt hsabs hτabs)
      exact le_of_lt hsbound
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
          inv_mul_cancel₀ (abs_ne_zero.2 (by simpa using hτne)), one_mul]

/-! ## Closedness -/

/-- **The generator has closed graph.**  If domain vectors converge in `ℋ` and their images under
the generator converge, then the limit vector is again in the domain and its image is the limit. -/
theorem generator_isClosed (Λ : OSState) (T : TimeTranslation)
    (hinv : ∀ (τ : ℝ) (F : Observable), osBilin Λ.ω (T τ F) (T τ F) ≤ osBilin Λ.ω F F)
    (hcont : ∀ F : Observable, Continuous fun τ : ℝ => osBilin Λ.ω (T τ F) F) :
    ∀ (u : ℕ → (generator Λ T hinv).domain) {z₀ y : Hphys Λ},
      Tendsto (fun n => (u n : Hphys Λ)) atTop (𝓝 z₀) →
      Tendsto (fun n => generator Λ T hinv (u n)) atTop (𝓝 y) →
      ∃ h : HasGen Λ T hinv z₀, generator Λ T hinv ⟨z₀, h⟩ = y := by
  intro u z₀ y hu hy
  -- the integral identity passes to the limit, for every `τ`
  have hmain : ∀ τ : ℝ,
      physEvolCompletion Λ T hinv τ z₀ - z₀
        = ∫ s in (0 : ℝ)..τ, physEvolCompletion Λ T hinv s y := by
    intro τ
    have hleft : Tendsto (fun n => physEvolCompletion Λ T hinv τ (u n) - (u n : Hphys Λ))
        atTop (𝓝 (physEvolCompletion Λ T hinv τ z₀ - z₀)) :=
      (((physEvolCompletion Λ T hinv τ).continuous.tendsto z₀).comp hu).sub hu
    have hlim : Tendsto (fun n => |τ| * ‖generator Λ T hinv (u n) - y‖) atTop (𝓝 0) := by
      have h1 : Tendsto (fun n => ‖generator Λ T hinv (u n) - y‖) atTop (𝓝 0) := by
        have hsub : Tendsto (fun n => generator Λ T hinv (u n) - y) atTop (𝓝 (y - y)) :=
          hy.sub (tendsto_const_nhds : Tendsto (fun _ : ℕ => y) atTop (𝓝 y))
        simpa using hsub.norm
      simpa using h1.const_mul |τ|
    have hright : Tendsto
        (fun n => ∫ s in (0 : ℝ)..τ, physEvolCompletion Λ T hinv s (generator Λ T hinv (u n)))
        atTop (𝓝 (∫ s in (0 : ℝ)..τ, physEvolCompletion Λ T hinv s y)) := by
      refine tendsto_iff_norm_sub_tendsto_zero.2 ?_
      have hb : ∀ n,
          ‖(∫ s in (0 : ℝ)..τ, physEvolCompletion Λ T hinv s (generator Λ T hinv (u n)))
            - (∫ s in (0 : ℝ)..τ, physEvolCompletion Λ T hinv s y)‖
            ≤ |τ| * ‖generator Λ T hinv (u n) - y‖ := by
        intro n
        rw [← intervalIntegral.integral_sub
          ((continuous_physEvolCompletion_apply Λ T hinv hcont _).intervalIntegrable 0 τ)
          ((continuous_physEvolCompletion_apply Λ T hinv hcont _).intervalIntegrable 0 τ)]
        refine (intervalIntegral.norm_integral_le_of_norm_le_const
          (C := ‖generator Λ T hinv (u n) - y‖) ?_).trans_eq ?_
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
        physEvol_sub_eq_integral Λ T hinv hcont (u n) τ))
  -- the quotient limit, hence domain membership
  have hquot : (fun τ : ℝ => diffQuot Λ T hinv τ z₀)
      =ᶠ[𝓝[≠] 0]
        (fun τ : ℝ => τ⁻¹ • ∫ s in (0 : ℝ)..τ, physEvolCompletion Λ T hinv s y) :=
    Eventually.of_forall fun τ => by
      change τ⁻¹ • (physEvolCompletion Λ T hinv τ z₀ - z₀)
        = τ⁻¹ • ∫ s in (0 : ℝ)..τ, physEvolCompletion Λ T hinv s y
      rw [hmain τ]
  have haverage := tendsto_average_physEvol Λ T hinv hcont y
  have hgen : HasGen Λ T hinv z₀ := ⟨y, haverage.congr' hquot.symm⟩
  refine ⟨hgen, ?_⟩
  exact tendsto_nhds_unique (genValue_tendsto Λ T hinv ⟨z₀, hgen⟩) (haverage.congr' hquot.symm)

end

end BookProof.OSReconstruction
