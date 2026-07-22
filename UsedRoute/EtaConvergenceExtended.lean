import Mathlib
import UsedRoute.EtaConvergence

/-!
# Extended uniform convergence of eta partial sums

We extend the result from `EtaConvergence.lean` to compact subsets of
{Re > 1/2} \ {1}, removing the restriction Re < 1. This is needed for
rectangles crossing the line Re = 1.

## Main results

- `etaPartial'_tendstoUniformlyOn_extended`: Uniform convergence on compact
  K ⊂ {Re > 1/2} with (1 : ℂ) ∉ K.

- `reciprocal_tendstoUniformlyOn_of_nonvanishing`: If f_n → f uniformly on
  compact K, f ≠ 0 on K, then 1/f_n → 1/f uniformly on K.
-/

open Complex Finset Filter Topology MeasureTheory
open scoped ArithmeticFunction

noncomputable section

/-
The eta partial sums converge uniformly to dirichletEta on compact
    K ⊂ {Re > 1/2} with (1 : ℂ) ∉ K. This extends `etaPartial'_tendstoUniformlyOn`
    by removing the restriction Re < 1.
-/
theorem etaPartial'_tendstoUniformlyOn_extended (K : Set ℂ) (hK : IsCompact K)
    (hK_lower : ∀ z ∈ K, z.re > 1 / 2)
    (hK_ne_one : ∀ z ∈ K, z ≠ 1) :
    TendstoUniformlyOn (fun n => etaPartial' n) dirichletEta atTop K := by
  have h_even : TendstoUniformlyOn (fun m s => etaPartial' (2 * m) s) dirichletEta atTop K := by
    have h_even : TendstoUniformlyOn (fun m s => ∑ j ∈ Finset.range m, etaPairedTerm j s) (fun s => ∑' j, etaPairedTerm j s) atTop K := by
      exact?;
    intro ε hε; filter_upwards [ h_even ε hε ] with n hn x hx; specialize hn x hx; rw [ etaPartial'_even_eq_paired_sum ] ; convert hn using 1; rw [ paired_tsum_eq_dirichletEta x ( hK_lower x hx ) ( hK_ne_one x hx ) ] ;
  -- For the odd case, use `odd_correction_tendstoUniformlyOn K hK hK_lower` and `etaPartial'_odd_minus_even`.
  have h_odd : TendstoUniformlyOn (fun m s => etaPartial' (2 * m + 1) s - etaPartial' (2 * m) s) (fun _ => 0) atTop K := by
    convert odd_correction_tendstoUniformlyOn K hK hK_lower using 1;
    exact funext fun m => funext fun s => etaPartial'_odd_minus_even m s;
  rw [ Metric.tendstoUniformlyOn_iff ] at *;
  intro ε hε; rcases Filter.eventually_atTop.mp ( h_even ( ε / 2 ) ( half_pos hε ) ) with ⟨ N₁, hN₁ ⟩ ; rcases Filter.eventually_atTop.mp ( h_odd ( ε / 2 ) ( half_pos hε ) ) with ⟨ N₂, hN₂ ⟩ ; refine' Filter.eventually_atTop.mpr ⟨ 2 * N₁ + 2 * N₂, fun n hn => _ ⟩ ; rcases Nat.even_or_odd' n with ⟨ k, rfl | rfl ⟩ <;> simp_all +decide [ Nat.mul_succ ] ;
  · exact fun x hx => lt_of_lt_of_le ( hN₁ k ( by linarith ) x hx ) ( by linarith );
  · intro x hx; specialize hN₁ k ( by linarith ) x hx; specialize hN₂ k ( by linarith ) x hx; exact lt_of_le_of_lt ( dist_triangle _ _ _ ) ( by linarith ) ;

/-
If f_n → f uniformly on compact K, and f ≠ 0 on K, and f is continuous on K,
    then 1/f_n → 1/f uniformly on K.
-/
theorem reciprocal_tendstoUniformlyOn_of_nonvanishing
    (K : Set ℂ) (hK : IsCompact K)
    (F : ℕ → ℂ → ℂ) (f : ℂ → ℂ)
    (h_unif : TendstoUniformlyOn F f atTop K)
    (hf_cont : ContinuousOn f K)
    (hf_nz : ∀ z ∈ K, f z ≠ 0) :
    TendstoUniformlyOn (fun n z => 1 / F n z) (fun z => 1 / f z) atTop K := by
  rw [ Metric.tendstoUniformlyOn_iff ] at *;
  -- Since $f$ is continuous and nonzero on compact $K$, $\|f\|$ achieves a positive minimum $\delta > 0$ on $K$.
  obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ z ∈ K, δ ≤ ‖f z‖ := by
    by_cases hK_empty : K = ∅;
    · exact ⟨ 1, zero_lt_one, by simp +decide [ hK_empty ] ⟩;
    · obtain ⟨ z, hz ⟩ := Set.nonempty_iff_ne_empty.mpr hK_empty; have := hK.exists_isMinOn ⟨ z, hz ⟩ hf_cont.norm; aesop;
  intro ε ε_pos; filter_upwards [ h_unif ( Min.min ( δ/2 ) ( ε * δ^2/2 ) ) ( lt_min ( half_pos hδ_pos ) ( by positivity ) ) ] with n hn; intro x hx; by_cases h' : F n x = 0 <;> simp_all +decide [ dist_eq_norm ] ;
  · grind +qlia;
  · rw [ inv_sub_inv ] <;> try tauto;
    rw [ norm_div, norm_mul ];
    rw [ norm_sub_rev, div_lt_iff₀ ] <;> nlinarith [ hn x hx, hδ x hx, norm_nonneg ( f x - F n x ), norm_nonneg ( f x ), norm_nonneg ( F n x ), mul_pos ε_pos hδ_pos, mul_pos ε_pos ( norm_pos_iff.mpr ( hf_nz x hx ) ), mul_pos ε_pos ( norm_pos_iff.mpr h' ), norm_sub_norm_le ( f x ) ( F n x ) ]

end