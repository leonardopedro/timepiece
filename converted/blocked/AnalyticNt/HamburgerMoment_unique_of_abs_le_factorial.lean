/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 8aa3486d-502d-4cfe-a31d-fe2045be08fa
* original name       : `HamburgerMoment.unique_of_abs_le_factorial`
* title               : Uniqueness under the growth bound $|m_n|\le CD^nn!$
* statement author    : Lucas
* solution author     : fizzyinc3 (submission 97c65ba2-a392-4d5d-859e-a334fcc19635,
                        accepted 2026-10-17T13:12:56.425162+00:00)
* source              : Wikipedia, "Hamburger moment problem", revision oldid=1356180072, https://en.wikipedia.org/w/index.php?title=Hamburger_moment_problem&oldid=1356180072, section "Uniqueness of solutions", sentence "More generally, the solution is unique if there are constants C and D such that, for all n, |mn| ≤ CD^n n! (Reed & Simon 1975, p. 205)"
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/analytic-nt/HamburgerMoment.unique_of_abs_le_factorial.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/HamburgerMoment_unique_of_abs_le_factorial.diff`.
-/
import Definitions.Def_HamburgerMoment_Defs

open MeasureTheory ProbabilityTheory Filter Set
open scoped Topology

private lemma exp_integrable (m : ℕ → ℝ) (C D : ℝ)
    (hb : ∀ n, |m n| ≤ |C| * |D| ^ n * (n.factorial : ℝ))
    (μ : Measure ℝ) (hμ : HamburgerMoment.IsMomentMeasure m μ)
    (t : ℝ) (ht : |t * D| < 1) : Integrable (fun x : ℝ => Real.exp (t * x)) μ := by
  let F : ℕ → ℝ → ℝ := fun n x => (t * x) ^ (2*n) / ((2*n).factorial : ℝ)
  have hi (n : ℕ) : Integrable (F n) μ := by
    simpa only [F, mul_pow, div_eq_mul_inv] using
      ((hμ (2*n)).1.const_mul (t^(2*n))).mul_const (((2*n).factorial : ℝ)⁻¹)
  have hn (n : ℕ) (x : ℝ) : 0 ≤ F n x := by
    dsimp [F]
    rw [pow_mul]
    positivity
  have he (n : ℕ) : (∫ x, ‖F n x‖ ∂μ) ≤ |C| * ((t * D)^2)^n := by
    simp_rw [Real.norm_of_nonneg (hn n _)]
    have hid : (∫ x, F n x ∂μ) = t^(2*n) * m (2*n) / ((2*n).factorial : ℝ) := by
      simp_rw [F, mul_pow, div_eq_mul_inv, mul_assoc]
      rw [integral_const_mul, integral_mul_const, (hμ (2*n)).2]
    rw [hid]
    have hp : 0 < ((2*n).factorial : ℝ) := by positivity
    apply (div_le_iff₀ hp).2
    calc
      t^(2*n) * m (2*n) ≤ t^(2*n) * |m (2*n)| :=
        mul_le_mul_of_nonneg_left (le_abs_self _) (by rw [pow_mul]; positivity)
      _ ≤ t^(2*n) * (|C| * |D|^(2*n) * ((2*n).factorial : ℝ)) :=
        mul_le_mul_of_nonneg_left (hb _) (by rw [pow_mul]; positivity)
      _ = |C| * ((t*D)^2)^n * ((2*n).factorial : ℝ) := by
        simp only [mul_pow, pow_mul, sq_abs]
        ring
  have hs : Summable (fun n => ∫ x, ‖F n x‖ ∂μ) := by
    refine Summable.of_nonneg_of_le (fun _ => integral_nonneg (fun _ => norm_nonneg _)) he ?_
    apply Summable.mul_left
    apply summable_geometric_of_norm_lt_one
    rw [Real.norm_of_nonneg (sq_nonneg _)]
    nlinarith [abs_nonneg (t*D), sq_abs (t*D)]
  have hc : Integrable (fun x : ℝ => Real.cosh (t*x)) μ := by
    refine ⟨by fun_prop, ?_⟩
    apply lt_of_le_of_lt (b := ∑' n, ∫⁻ x, ‖F n x‖ₑ ∂μ)
    · calc
        (∫⁻ x, ‖Real.cosh (t*x)‖ₑ ∂μ) ≤ ∫⁻ x, ∑' n, ‖F n x‖ₑ ∂μ := by
          apply lintegral_mono
          intro x
          dsimp only
          rw [Real.cosh_eq_tsum]
          exact enorm_tsum_le_tsum_enorm
        _ = _ := lintegral_tsum (fun n => (hi n).aestronglyMeasurable.enorm)
    · simp_rw [← ofReal_integral_norm_eq_lintegral_enorm (hi _)]
      rw [← ENNReal.ofReal_tsum_of_nonneg
        (fun _ => integral_nonneg (fun _ => norm_nonneg _)) hs]
      exact ENNReal.ofReal_lt_top
  refine (hc.const_mul 2).mono' (by fun_prop) (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_of_pos (Real.exp_pos _), Real.cosh_eq]
  linarith [Real.exp_pos (-(t*x))]

private lemma local_exp (m : ℕ → ℝ) (C D : ℝ)
    (hb : ∀ n, |m n| ≤ |C| * |D| ^ n * (n.factorial : ℝ))
    (μ : Measure ℝ) (hμ : HamburgerMoment.IsMomentMeasure m μ) :
    Ioo (-(1 / (|D| + 1))) (1 / (|D| + 1)) ⊆ interior (integrableExpSet id μ) := by
  apply interior_maximal _ isOpen_Ioo
  intro t ht
  apply exp_integrable m C D hb μ hμ t
  rw [abs_mul]
  have hd : 0 < |D| + 1 := by positivity
  have ht' : |t| < 1 / (|D| + 1) := abs_lt.mpr ht
  have ht'' := (lt_div_iff₀ hd).mp ht'
  nlinarith [abs_nonneg t, abs_nonneg D]

theorem _root_.Prove2me.Solution.HamburgerMoment_unique_of_abs_le_factorial (m : ℕ → ℝ) (C D : ℝ)
    (hCD : ∀ n : ℕ, |m n| ≤ C * D ^ n * (n.factorial : ℝ))
    (μ ν : Measure ℝ) (hμ : HamburgerMoment.IsMomentMeasure m μ)
    (hν : HamburgerMoment.IsMomentMeasure m ν) : μ = ν := by
  have hb (n : ℕ) : |m n| ≤ |C| * |D| ^ n * (n.factorial : ℝ) := by
    calc
      _ ≤ C * D ^ n * (n.factorial : ℝ) := hCD n
      _ ≤ |C * D ^ n * (n.factorial : ℝ)| := le_abs_self _
      _ = _ := by simp [abs_mul]
  let r : ℝ := 1 / (|D| + 1)
  have hr : 0 < r := by dsimp [r]; positivity
  have hμi := local_exp m C D hb μ hμ
  have hνi := local_exp m C D hb ν hν
  have hμ0 : (0 : ℝ) ∈ interior (integrableExpSet id μ) := hμi ⟨by linarith, hr⟩
  have hν0 : (0 : ℝ) ∈ interior (integrableExpSet id ν) := hνi ⟨by linarith, hr⟩
  let : IsFiniteMeasure μ := (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℝ) ≠ 0)).mp
    (by simpa using (hμ 0).1)
  let : IsFiniteMeasure ν := (integrable_const_iff_isFiniteMeasure (one_ne_zero : (1 : ℝ) ≠ 0)).mp
    (by simpa using (hν 0).1)
  have he (n : ℕ) : iteratedDeriv n (complexMGF id μ) 0 =
      iteratedDeriv n (complexMGF id ν) 0 := by
    rw [iteratedDeriv_complexMGF (by simpa using hμ0),
      iteratedDeriv_complexMGF (by simpa using hν0)]
    simp only [Function.id_def, zero_mul, Complex.exp_zero, mul_one]
    norm_cast
    rw [(hμ n).2, (hν n).2]
  have hps := (analyticAt_complexMGF (X := id) (μ := μ) (by simpa using hμ0 :
    (0 : ℂ).re ∈ interior (integrableExpSet id μ))).hasFPowerSeriesAt
  have hqs := (analyticAt_complexMGF (X := id) (μ := ν) (by simpa using hν0 :
    (0 : ℂ).re ∈ interior (integrableExpSet id ν))).hasFPowerSeriesAt
  have hseries : (fun n => iteratedDeriv n (complexMGF id μ) 0 / (n.factorial : ℂ)) =
      (fun n => iteratedDeriv n (complexMGF id ν) 0 / (n.factorial : ℂ)) := by
    funext n
    rw [he n]
  rw [hseries] at hps
  have hlocal : complexMGF id μ =ᶠ[𝓝 (0 : ℂ)] complexMGF id ν := by
    filter_upwards [hps.eventually_hasSum, hqs.eventually_hasSum] with z hz hz'
    simpa using hz.unique hz'
  let U : Set ℂ := {z | z.re ∈ Ioo (-r) r}
  have hU : IsPreconnected U := ((convex_Ioo (-r) r).linear_preimage Complex.reLm).isPreconnected
  have hμa : AnalyticOnNhd ℂ (complexMGF id μ) U := fun z hz =>
    analyticAt_complexMGF (hμi hz)
  have hνa : AnalyticOnNhd ℂ (complexMGF id ν) U := fun z hz =>
    analyticAt_complexMGF (hνi hz)
  have heq := hμa.eqOn_of_preconnected_of_eventuallyEq hνa hU
    (show (0 : ℂ) ∈ U from ⟨by simp; linarith, by simpa using hr⟩) hlocal
  apply Measure.ext_of_charFun
  funext t
  rw [← complexMGF_id_mul_I, ← complexMGF_id_mul_I]
  apply heq
  change -r < ((t : ℂ) * Complex.I).re ∧ ((t : ℂ) * Complex.I).re < r
  simpa using (show -r < (0 : ℝ) ∧ (0 : ℝ) < r from ⟨by linarith, hr⟩)

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

open MeasureTheory

namespace HamburgerMoment

theorem unique_of_abs_le_factorial (m : ℕ → ℝ) (C D : ℝ)
    (hCD : ∀ n : ℕ, |m n| ≤ C * D ^ n * (n.factorial : ℝ))
    (μ ν : Measure ℝ) (hμ : IsMomentMeasure m μ) (hν : IsMomentMeasure m ν) :
    μ = ν :=
  _root_.Prove2me.Solution.HamburgerMoment_unique_of_abs_le_factorial m C D hCD μ ν hμ hν

end HamburgerMoment

end Prove2meStatement
