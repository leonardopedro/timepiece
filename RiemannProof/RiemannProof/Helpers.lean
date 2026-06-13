import Mathlib
import RiemannProof.ShiftedEta
import RiemannProof.RectangleStrategy

/-!
# Helper Lemmas (H1–H6) for the Conjugate-Reflection / Zero-Location Arguments

This file collects the analytic helper lemmas described in the implementation
plan:

* `dirichletEta_one` / `etaShifted_one` (H1): the junk value at `s = 1`.
* `dirichletEta_tendsto_log_two` / `etaShifted_tendsto_log_two` (H2):
  the genuine limit `log 2` at `s = 1`.
* `riemannZeta_conj'` (H3): Schwarz reflection for `ζ`.
* `etaShifted_conj` (H4): Schwarz reflection for the shifted eta.
* `etaShifted_differentiableAt` (H5 consequence): differentiability away from 1.
* `etaShifted_zero_re_eq` (H6): every strip zero lies on `Re = 3/4`.
-/

open Complex Finset Filter Topology
open scoped ComplexConjugate

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-! ## H1: The junk value at 1 -/

lemma dirichletEta_one : dirichletEta 1 = 0 := by
  simp [dirichletEta, Complex.cpow_zero]

lemma etaShifted_one : etaShifted 1 = 0 := by
  unfold etaShifted
  norm_num
  exact dirichletEta_one

/-! ## H2: The true limit at 1 -/

lemma log_two_ne_zero : Complex.log 2 ≠ 0 := by
  norm_num [ Complex.ext_iff, Complex.log_re, Complex.log_im ]

lemma dirichletEta_tendsto_log_two :
    Tendsto dirichletEta (𝓝[≠] (1 : ℂ)) (𝓝 (Complex.log 2)) := by
  -- Apply L'Hôpital's Rule to evaluate the limit.
  have h_lhopital : HasDerivAt (fun s : ℂ => 1 - 2 ^ (1 - s)) (Complex.log 2) 1 := by
    convert HasDerivAt.const_sub _ ( HasDerivAt.cpow ( hasDerivAt_const _ _ ) ( hasDerivAt_id 1 |> HasDerivAt.const_sub _ ) _ ) using 1 <;> norm_num;
  -- Apply the fact that the limit of a product is the product of the limits, given that both limits exist.
  have h_prod : Filter.Tendsto (fun s : ℂ => (1 - 2 ^ (1 - s)) / (s - 1)) (nhdsWithin 1 {1}ᶜ) (nhds (Complex.log 2)) ∧ Filter.Tendsto (fun s : ℂ => (s - 1) * riemannZeta s) (nhdsWithin 1 {1}ᶜ) (nhds 1) := by
    constructor;
    · rw [ hasDerivAt_iff_tendsto_slope ] at h_lhopital;
      convert h_lhopital using 2 ; norm_num [ slope_def_field ];
    · convert riemannZeta_residue_one using 1;
  have := h_prod.1.mul h_prod.2;
  simpa using this.congr' ( by filter_upwards [ self_mem_nhdsWithin ] with x hx using by rw [ ← mul_assoc, div_mul_cancel₀ _ ( sub_ne_zero_of_ne hx ) ] ; rfl )

lemma etaShifted_tendsto_log_two :
    Tendsto etaShifted (𝓝[≠] (1 : ℂ)) (𝓝 (Complex.log 2)) := by
  have h_cont : Filter.Tendsto (fun s : ℂ => 2 * s - 1) (nhdsWithin 1 {1}ᶜ) (nhdsWithin 1 {1}ᶜ) := by
    refine' Filter.Tendsto.inf _ _ <;> norm_num [ Filter.Tendsto ];
    · exact Continuous.tendsto' ( by continuity ) _ _ ( by norm_num );
    · exact fun x hx => fun h => hx <| by linear_combination' h / 2;
  exact Filter.Tendsto.comp ( dirichletEta_tendsto_log_two ) h_cont

/-! ## H3: Schwarz reflection for ζ -/

lemma riemannZeta_conj' (s : ℂ) (hs : s ≠ 1) :
    riemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (riemannZeta s) := by
  by_contra h_contra;
  -- Apply the identity theorem for analytic functions.
  have h_identity : AnalyticOnNhd ℂ riemannZeta {z : ℂ | z ≠ 1} ∧ AnalyticOnNhd ℂ (fun z => starRingEnd ℂ (riemannZeta (starRingEnd ℂ z))) {z : ℂ | z ≠ 1} := by
    constructor;
    · apply_rules [ DifferentiableOn.analyticOnNhd ];
      · intro z hz; exact differentiableAt_riemannZeta hz |> DifferentiableAt.differentiableWithinAt;
      · exact isOpen_ne;
    · apply_rules [ DifferentiableOn.analyticOnNhd ];
      · intro z hz
        have h_diff : DifferentiableAt ℂ riemannZeta (starRingEnd ℂ z) := by
          apply_rules [ differentiableAt_riemannZeta ];
          exact fun h => hz <| by simpa using congr_arg Star.star h;
        have h_diff_conj : HasDerivAt (fun z => starRingEnd ℂ (riemannZeta (starRingEnd ℂ z))) (starRingEnd ℂ (deriv riemannZeta (starRingEnd ℂ z))) z := by
          rw [ hasDerivAt_iff_tendsto_slope_zero ];
          have := h_diff.hasDerivAt.tendsto_slope_zero;
          convert Complex.continuous_conj.continuousAt.tendsto.comp ( this.comp ( show Filter.Tendsto ( fun t : ℂ => starRingEnd ℂ t ) ( 𝓝[≠] 0 ) ( 𝓝[≠] 0 ) from ?_ ) ) using 2 <;> norm_num;
          rw [ Metric.tendsto_nhdsWithin_nhdsWithin ] ; aesop;
        exact h_diff_conj.differentiableAt.differentiableWithinAt;
      · exact isOpen_ne;
  have h_eq : ∀ z : ℂ, z.re > 1 → riemannZeta z = starRingEnd ℂ (riemannZeta (starRingEnd ℂ z)) := by
    intro z hz
    have h_eq : riemannZeta z = ∑' n : ℕ, (1 : ℂ) / (n + 1) ^ z := by
      convert zeta_eq_tsum_one_div_nat_add_one_cpow hz using 1
    have h_eq_conj : riemannZeta (starRingEnd ℂ z) = ∑' n : ℕ, (1 : ℂ) / (n + 1) ^ (starRingEnd ℂ z) := by
      convert zeta_eq_tsum_one_div_nat_add_one_cpow _ using 1;
      simpa using hz
    simp_all +decide [ Complex.conj_ofReal, Complex.conj_I ];
    rw [ Complex.conj_tsum ] ; congr ; ext n ; norm_num [ Complex.cpow_def ] ; ring;
    norm_cast ; norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im ];
  have h_eq : ∀ z : ℂ, z ≠ 1 → riemannZeta z = starRingEnd ℂ (riemannZeta (starRingEnd ℂ z)) := by
    apply h_identity.left.eqOn_of_preconnected_of_eventuallyEq h_identity.right;
    any_goals exact ( 2 : ℂ );
    · have h_preconnected : IsPreconnected (Set.univ \ {0} : Set ℂ) := by
        have h_preconnected : IsConnected (Set.univ \ {0} : Set ℂ) := by
          have h_connected : IsConnected (Set.range (fun z : ℂ => Complex.exp z)) := by
            exact isConnected_range ( Complex.continuous_exp )
          convert h_connected using 1;
          ext; simp [Complex.exp_ne_zero];
        exact h_preconnected.isPreconnected;
      convert h_preconnected.image ( fun z => z + 1 ) ( Continuous.continuousOn ( by continuity ) ) using 1 ; ext ; simp +decide [ Set.diff_eq ];
    · norm_num;
    · filter_upwards [ IsOpen.mem_nhds ( isOpen_lt continuous_const Complex.continuous_re ) ( show ( 2 : ℂ ).re > 1 by norm_num ) ] with z hz using h_eq z hz;
  exact h_contra <| by simpa using h_eq s hs ▸ by simp +decide [ Complex.ext_iff ] ;

/-! ## H4: Schwarz reflection for the shifted eta -/

lemma etaShifted_conj (s : ℂ) :
    etaShifted (starRingEnd ℂ s) = starRingEnd ℂ (etaShifted s) := by
  by_cases hs : 2 * s - 1 = 1;
  · norm_num [ show s = 1 by linear_combination hs / 2, etaShifted_one ];
  · convert congr_arg₂ ( · * · ) ( show ( 1 - ( 2 : ℂ ) ^ ( 1 - ( 2 * ( starRingEnd ℂ s ) - 1 ) ) ) = ( starRingEnd ℂ ( 1 - ( 2 : ℂ ) ^ ( 1 - ( 2 * s - 1 ) ) ) ) from ?_ ) ( show riemannZeta ( 2 * ( starRingEnd ℂ s ) - 1 ) = starRingEnd ℂ ( riemannZeta ( 2 * s - 1 ) ) from ?_ ) using 1;
    · rw [ ← map_mul, etaShifted_eq ];
    · norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Complex.cpow_def ];
    · convert riemannZeta_conj' _ _ using 2 ; norm_num [ Complex.ext_iff ];
      exact hs

/-! ## H5 consequence: differentiability of etaShifted away from 1 -/

lemma etaShifted_differentiableAt {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ etaShifted s := by
  refine' DifferentiableAt.mul _ _;
  · norm_num [ Complex.cpow_def, mul_comm ];
  · refine' DifferentiableAt.comp s ( differentiableAt_riemannZeta _ ) _;
    · exact fun h => hs <| by linear_combination' h / 2;
    · exact DifferentiableAt.sub ( differentiableAt_id.const_mul _ ) ( differentiableAt_const _ )

/-! ## H6: All strip zeros lie on Re = 3/4 -/

lemma etaShifted_zero_re_eq (s₀ : ℂ) (hσ₁ : s₀.re > 1 / 2) (hσ₂ : s₀.re < 1)
    (h_zero : etaShifted s₀ = 0) : s₀.re = 3 / 4 := by
  by_cases h : s₀.re < 3 / 4 <;> simp_all +decide [ etaShifted ];
  · -- From the hypothesis `h_zero`, since `etaRect w = 0` and `etaFactor w ≠ 0` (because `w.re < 1`), we get `ζ w = 0`.
    have h_zeta_w : riemannZeta (2 * s₀ - 1) = 0 := by
      exact eq_zero_of_ne_zero_of_mul_left_eq_zero ( etaFactRect_ne_zero _ <| by norm_num; linarith ) h_zero;
    have h_zeta_1_minus_w : riemannZeta (1 - (2 * s₀ - 1)) = 0 := by
      apply zeta_symm;
      · norm_num at * ; linarith;
      · norm_num at * ; linarith;
      · exact h_zeta_w;
    contrapose! h_zeta_1_minus_w;
    convert zetaRect_ne_zero_critical_strip ( 1 - ( 2 * s₀ - 1 ) ) _ _ using 1 <;> norm_num at * <;> linarith;
  · by_contra h_contra;
    exact etaRect_ne_zero_critical_strip ( 2 * s₀ - 1 ) ( by norm_num; contrapose! h_contra; linarith ) ( by norm_num; contrapose! h_contra; linarith ) h_zero

end