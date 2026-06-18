import Mathlib
import PnpProof.Foundations

/-!
# Part 3: Function space (H1–H7)

Separability of `L²`, non-separability of `L^∞`, existence of the
wave-function `√p`, the Hilbert-space classification surrogate for the
Fock–Guichardet isomorphism, and an atomless probability measure on the unit
sphere.
-/

open MeasureTheory Set
open scoped ENNReal

noncomputable section

namespace PnpProof

/-! ### H1. `L²([0,1])` is separable -/

instance : Fact ((2 : ℝ≥0∞) ≠ ⊤) := ⟨by norm_num⟩

theorem l2_separable :
    TopologicalSpace.SeparableSpace (Lp ℝ 2 unitMeasure) := by
  convert inferInstanceAs (TopologicalSpace.SeparableSpace (MeasureTheory.Lp ℝ 2 (MeasureTheory.Measure.restrict (MeasureTheory.volume : MeasureTheory.Measure ℝ) (Set.Icc 0 1)))) using 1

/-! ### H2. `L^∞([0,1])` is NOT separable -/

theorem linf_not_separable :
    ¬ TopologicalSpace.SeparableSpace (Lp ℝ ⊤ unitMeasure) := by
  intro h
  obtain ⟨D, hD_countable, hD_dense⟩ : ∃ D : Set (Lp ℝ ⊤ unitMeasure), D.Countable ∧ Dense D := by
    grind +splitIndPred;
  -- For $t \in (0,1]$, let $u_t := \text{indicatorConstLp} \top (\text{measurableSet_Ioc}) (\text{finiteness}) (1:ℝ)$ for the set $Ioc 0 t$.
  set u : ℝ → Lp ℝ ⊤ unitMeasure := fun t => MeasureTheory.MemLp.toLp (Set.indicator (Set.Ioc 0 t) fun _ => 1) (MeasureTheory.memLp_const (1 : ℝ) |>.indicator (measurableSet_Ioc));
  -- For $0 < s < t \leq 1$, $\|u_t - u_s\| = 1$: the difference is a.e. the indicator of $Ioc s t$, and the $L^\infty$ norm of the indicator of a positive-measure set with value 1 equals 1.
  have h_dist : ∀ s t : ℝ, 0 < s → s < t → t ≤ 1 → dist (u t) (u s) = 1 := by
    intros s t hs ht ht1
    have h_diff : ∀ᵐ x ∂unitMeasure, (u t - u s) x = if x ∈ Set.Ioc s t then 1 else 0 := by
      have h_diff : ∀ᵐ x ∂unitMeasure, (u t - u s) x = (Set.indicator (Set.Ioc 0 t) (fun _ => 1 : ℝ → ℝ) - Set.indicator (Set.Ioc 0 s) (fun _ => 1 : ℝ → ℝ)) x := by
        have h_diff : ∀ᵐ x ∂unitMeasure, (u t - u s) x = (u t) x - (u s) x := by
          exact MeasureTheory.Lp.coeFn_sub _ _;
        filter_upwards [ h_diff, MeasureTheory.MemLp.coeFn_toLp ( MeasureTheory.memLp_const ( 1 : ℝ ) |>.indicator ( measurableSet_Ioc ) : MeasureTheory.MemLp ( Set.indicator ( Set.Ioc 0 t ) fun _ => 1 : ℝ → ℝ ) ⊤ unitMeasure ), MeasureTheory.MemLp.coeFn_toLp ( MeasureTheory.memLp_const ( 1 : ℝ ) |>.indicator ( measurableSet_Ioc ) : MeasureTheory.MemLp ( Set.indicator ( Set.Ioc 0 s ) fun _ => 1 : ℝ → ℝ ) ⊤ unitMeasure ) ] with x hx₁ hx₂ hx₃ ; aesop;
      filter_upwards [ h_diff ] with x hx ; split_ifs <;> simp_all +decide [ Set.indicator ] ;
      · grind;
      · grind;
    -- The L^∞ norm of the indicator of a positive-measure set with value 1 equals 1.
    have h_norm : eLpNorm (fun x => if x ∈ Set.Ioc s t then 1 else 0 : ℝ → ℝ) ⊤ unitMeasure = 1 := by
      refine' le_antisymm _ _ <;> norm_num [ eLpNormEssSup ];
      · refine' csInf_le _ _ <;> norm_num;
        exact Filter.eventually_inf_principal.mpr ( Filter.Eventually.of_forall fun x hx => by split_ifs <;> norm_num );
      · refine' le_csInf _ _ <;> norm_num;
        · refine' ⟨ 1, _ ⟩ ; norm_num [ Filter.eventually_inf_principal ];
          exact Filter.Eventually.of_forall fun x hx₁ hx₂ => by split_ifs <;> norm_num;
        · intro b hb; contrapose! hb; simp_all +decide [ Filter.eventually_inf_principal ] ;
          rw [ Filter.Frequently, Filter.eventually_inf_principal ];
          rw [ MeasureTheory.ae_iff ] ; norm_num;
          refine' ne_of_gt ( lt_of_lt_of_le _ ( MeasureTheory.measure_mono _ ) );
          rotate_left;
          exact Set.Ioc s t;
          · exact fun x hx => ⟨ by linarith [ hx.1 ], by linarith [ hx.2 ], by rw [ if_pos ⟨ hx.1, hx.2 ⟩ ] ; simpa using hb ⟩;
          · simp +decide [ ht ];
    rw [ dist_eq_norm, Lp.norm_def ];
    rw [ eLpNorm_congr_ae h_diff ] ; aesop;
  -- From a countable dense set $D$, for each $t$ pick $d_t \in D$ with $\dist (u t) (d t) < 1/2$; the assignment $t \mapsto d t$ is injective on $(0,1]$.
  obtain ⟨d, hd⟩ : ∃ d : ℝ → Lp ℝ ⊤ unitMeasure, (∀ t : ℝ, 0 < t → t ≤ 1 → d t ∈ D ∧ dist (u t) (d t) < 1 / 2) ∧ (∀ s t : ℝ, 0 < s → s < t → t ≤ 1 → d s ≠ d t) := by
    have h_inj : ∀ t : ℝ, 0 < t → t ≤ 1 → ∃ d_t ∈ D, dist (u t) d_t < 1 / 2 := by
      exact fun t ht₁ ht₂ => by rcases Metric.mem_closure_iff.mp ( hD_dense ( u t ) ) ( 1 / 2 ) ( by norm_num ) with ⟨ d, hd₁, hd₂ ⟩ ; exact ⟨ d, hd₁, hd₂ ⟩ ;
    choose! d hd using h_inj;
    refine' ⟨ d, hd, fun s t hs ht ht' hst => _ ⟩;
    have := h_dist s t hs ht ht'; have := hd s hs ( by linarith ) ; have := hd t ( by linarith ) ht'; simp_all +decide [ dist_comm ] ;
    have := dist_triangle_left ( u s ) ( u t ) ( d t ) ; norm_num at * ; linarith [ h_dist s t hs ht ht' ] ;
  -- Hence $(0,1]$ injects into countable $D$, so $(Ioc (0:ℝ) 1)$ is countable.
  have h_countable : Set.Countable (Set.Ioc (0 : ℝ) 1) := by
    have h_inj : Set.InjOn d (Set.Ioc (0 : ℝ) 1) := by
      exact fun x hx y hy hxy => le_antisymm ( le_of_not_gt fun h => hd.2 _ _ hy.1 h hx.2 hxy.symm ) ( le_of_not_gt fun h => hd.2 _ _ hx.1 h hy.2 hxy );
    exact Set.MapsTo.countable_of_injOn ( fun x hx => hd.1 x hx.1 hx.2 |>.1 ) h_inj hD_countable;
  exact absurd h_countable ( by exact fun h => absurd ( h.measure_zero <| MeasureTheory.MeasureSpace.volume ) ( by norm_num ) )

/-! ### H3. Wave-functions exist: `Ψ = √p` -/

theorem sqrt_density_memLp {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (p : α → ℝ) (hp : Integrable p μ) (hp0 : 0 ≤ᵐ[μ] p) :
    MemLp (fun x => Real.sqrt (p x)) 2 μ := by
  constructor;
  · exact Real.continuous_sqrt.comp_aestronglyMeasurable hp.1;
  · rw [ MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal ] <;> norm_num [ hp0 ];
    refine' ENNReal.rpow_lt_top_of_nonneg _ _ <;> norm_num;
    refine' ne_of_lt ( lt_of_le_of_lt ( MeasureTheory.lintegral_mono_ae _ ) _ );
    use fun x => ENNReal.ofReal ( p x );
    · filter_upwards [ hp0 ] with x hx using by rw [ Real.enorm_eq_ofReal ( Real.sqrt_nonneg _ ) ] ; rw [ ← ENNReal.ofReal_pow ( Real.sqrt_nonneg _ ) ] ; rw [ Real.sq_sqrt hx ] ;
    · exact hp.lintegral_lt_top

theorem sqrt_density_norm {α : Type*} [MeasurableSpace α] (μ : Measure α)
    (p : α → ℝ) (hp : Integrable p μ) (hp0 : 0 ≤ᵐ[μ] p)
    (hp1 : ∫ x, p x ∂μ = 1) :
    ‖(sqrt_density_memLp μ p hp hp0).toLp _‖ = 1 := by
  rw [ Lp.norm_toLp ];
  rw [ MeasureTheory.eLpNorm_eq_lintegral_rpow_enorm_toReal ];
  · convert congr_arg ENNReal.toReal ( congr_arg ( · ^ ( 1 / 2 : ℝ ) ) ( show ( ∫⁻ x : α, ENNReal.ofReal ( p x ) ∂μ ) = 1 from ?_ ) ) using 1 <;> norm_num;
    · rw [ MeasureTheory.lintegral_congr_ae ];
      filter_upwards [ hp0 ] with x hx using by rw [ Real.enorm_eq_ofReal ( Real.sqrt_nonneg _ ) ] ; rw [ ← ENNReal.ofReal_pow ( Real.sqrt_nonneg _ ) ] ; rw [ Real.sq_sqrt hx ] ;
    · convert MeasureTheory.ofReal_integral_eq_lintegral_ofReal hp using 1;
      aesop;
  · norm_num;
  · norm_num

/-! ### H5. Polynomials are dense in `L²([0,1])` -/

theorem polynomial_dense_L2 :
    Dense {f : Lp ℝ 2 unitMeasure | ∃ P : Polynomial ℝ,
           f =ᵐ[unitMeasure] fun x => P.eval x} := by
  intro f
  have h_dense : ∀ ε > 0, ∃ g : Lp ℝ 2 unitMeasure, ‖f - g‖ < ε ∧ ∃ P : Polynomial ℝ, g =ᵐ[unitMeasure] fun x => P.eval x := by
    intro ε ε_pos;
    -- By the density of continuous functions in L², there exists a continuous function g such that ‖f - g‖ < ε/2.
    obtain ⟨g, hg⟩ : ∃ g : Lp ℝ 2 unitMeasure, ‖f - g‖ < ε / 2 ∧ ∃ g_cont : C(ℝ, ℝ), g =ᵐ[unitMeasure] fun x => g_cont x := by
      have h_dense : ∀ f : Lp ℝ 2 unitMeasure, ∀ ε > 0, ∃ g : Lp ℝ 2 unitMeasure, ‖f - g‖ < ε ∧ ∃ g_cont : C(ℝ, ℝ), g =ᵐ[unitMeasure] fun x => g_cont x := by
        intro f ε ε_pos;
        have := @BoundedContinuousFunction.toLp_denseRange;
        specialize this ℝ unitMeasure ( p := 2 ) ℝ;
        have := this ( by norm_num );
        have := this.exists_dist_lt f ε_pos;
        obtain ⟨ g, hg ⟩ := this;
        refine' ⟨ _, hg, g.toContinuousMap, _ ⟩;
        exact MeasureTheory.AEEqFun.coeFn_mk _ _;
      exact h_dense f ( ε / 2 ) ( half_pos ε_pos );
    obtain ⟨ g_cont, hg_cont ⟩ := hg.2
    obtain ⟨ P, hP ⟩ : ∃ P : Polynomial ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 1, |g_cont x - P.eval x| < ε / 4 := by
      have h_weierstrass : ∃ P : Polynomial ℝ, ∀ x ∈ Set.Icc (0 : ℝ) 1, |P.eval x - g_cont x| < ε / 4 := by
        apply_rules [ exists_polynomial_near_of_continuousOn, g_cont.continuous.continuousOn ] ; linarith;
      simpa only [ abs_sub_comm ] using h_weierstrass
    use (MemLp.toLp (fun x => P.eval x) (by
    have h_poly_integrable : MeasureTheory.Integrable (fun x => P.eval x ^ 2) unitMeasure := by
      exact Continuous.integrableOn_Icc ( by exact P.continuous.pow 2 ) |> fun h => h.mono_set <| Set.Icc_subset_Icc le_rfl le_rfl;
    rw [ memLp_two_iff_integrable_sq ] ; aesop;
    exact P.continuous.aestronglyMeasurable));
    have h_norm : ‖g - (MemLp.toLp (fun x => P.eval x) (by
    have h_poly_integrable : MeasureTheory.Integrable (fun x => P.eval x ^ 2) unitMeasure := by
      exact Continuous.integrableOn_Icc ( by exact P.continuous.pow 2 ) |> fun h => h.mono_set <| Set.Icc_subset_Icc le_rfl le_rfl;
    rw [ memLp_two_iff_integrable_sq ] ; aesop;
    exact P.continuous.aestronglyMeasurable))‖ ≤ ENNReal.toReal (ENNReal.ofReal (ε / 4)) := by
      refine' ENNReal.toReal_mono _ _;
      · norm_num;
      · rw [ eLpNorm_congr_ae ];
        rotate_left;
        exact MeasureTheory.Lp.coeFn_sub _ _ |> fun h => h.trans ( Filter.EventuallyEq.sub hg_cont ( MeasureTheory.MemLp.coeFn_toLp _ ) );
        rw [ eLpNorm_eq_lintegral_rpow_enorm_toReal ] <;> norm_num;
        refine' le_trans ( ENNReal.rpow_le_rpow ( MeasureTheory.lintegral_mono_ae _ ) ( by norm_num ) ) _;
        use fun x => ENNReal.ofReal ( ε / 4 ) ^ 2;
        · filter_upwards [ MeasureTheory.ae_restrict_mem measurableSet_Icc ] with x hx using pow_le_pow_left₀ ( by positivity ) ( by simpa [ Real.enorm_eq_ofReal_abs ] using ENNReal.ofReal_le_ofReal ( le_of_lt ( hP x hx ) ) ) _;
        · norm_num [ ← ENNReal.ofReal_pow, ε_pos.le ];
          rw [ ← ENNReal.rpow_natCast, ← ENNReal.rpow_mul ] ; norm_num;
    exact ⟨ by rw [ show f - MemLp.toLp ( fun x => Polynomial.eval x P ) _ = ( f - g ) + ( g - MemLp.toLp ( fun x => Polynomial.eval x P ) _ ) by abel1 ] ; exact lt_of_le_of_lt ( norm_add_le _ _ ) ( by rw [ ENNReal.toReal_ofReal ( by positivity ) ] at h_norm; linarith ), P, by exact MeasureTheory.MemLp.coeFn_toLp _ ⟩;
  rw [ Metric.mem_closure_iff ];
  exact fun ε hε => by rcases h_dense ε hε with ⟨ g, hg₁, P, hg₂ ⟩ ; exact ⟨ g, ⟨ P, hg₂ ⟩, by simpa [ dist_eq_norm ] using hg₁ ⟩ ;

/-! ### H6. All infinite-dimensional separable real Hilbert spaces are
isometrically isomorphic -/

/-
A uniformly separated family in a separable (pseudo)metric space is indexed
    by a countable type.
-/
theorem countable_of_separated {X : Type*} [PseudoMetricSpace X]
    [TopologicalSpace.SeparableSpace X] {ι : Type*} (u : ι → X) {r : ℝ} (hr : 0 < r)
    (hsep : ∀ i j, i ≠ j → r ≤ dist (u i) (u j)) : Countable ι := by
  obtain ⟨ D, hD_countable, hD_dense ⟩ := TopologicalSpace.exists_countable_dense X;
  -- For each $i \in \iota$, choose $d_i \in D$ such that $dist (u i) (d_i) < r / 2$.
  obtain ⟨d, hd⟩ : ∃ d : ι → X, (∀ i, d i ∈ D) ∧ (∀ i, dist (u i) (d i) < r / 2) := by
    exact ⟨ fun i => Classical.choose ( hD_dense.exists_dist_lt ( u i ) ( half_pos hr ) ), fun i => Classical.choose_spec ( hD_dense.exists_dist_lt ( u i ) ( half_pos hr ) ) |>.1, fun i => Classical.choose_spec ( hD_dense.exists_dist_lt ( u i ) ( half_pos hr ) ) |>.2 ⟩;
  have h_inj : Function.Injective d := by
    intro i j hij;
    exact Classical.not_not.1 fun h => by have := hsep i j h; linarith [ hd.2 i, hd.2 j, dist_triangle_right ( u i ) ( u j ) ( d i ), dist_triangle_right ( u j ) ( u i ) ( d j ), hij ▸ hd.2 i, hij ▸ hd.2 j ] ;
  exact Set.countable_univ_iff.mp ( Set.Countable.mono ( fun x _ => by aesop ) ( hD_countable.preimage h_inj ) )

/-
A separable infinite-dimensional real Hilbert space is isometric to
    `ℓ²(ℕ, ℝ)`.
-/
theorem exists_l2_iso (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E] (hE : ¬ FiniteDimensional ℝ E) :
    Nonempty (E ≃ₗᵢ[ℝ] ℓ²(ℕ, ℝ)) := by
  have := exists_hilbertBasis ℝ E;
  obtain ⟨ w, b, hb ⟩ := this;
  -- Since $w$ is countable and infinite, there exists an equivalence $e : ℕ ≃ w$.
  obtain ⟨e, he⟩ : ∃ e : ℕ ≃ w, True := by
    have h_countable : Countable w := by
      convert PnpProof.countable_of_separated ( fun i => b i ) ( show 0 < ( 1 : ℝ ) / 2 by norm_num ) _ using 1;
      intro i j hij
      have h_dist : ‖b i - b j‖ ^ 2 = 2 := by
        rw [ @norm_sub_sq ℝ ] ; simp +decide [ b.orthonormal.1, b.orthonormal.2 hij ] ; ring;
      rw [ dist_eq_norm ] ; nlinarith [ norm_nonneg ( b i - b j ) ];
    have h_infinite : Infinite w := by
      contrapose! hE;
      convert Module.Basis.finiteDimensional_of_finite ( b.toOrthonormalBasis.toBasis );
      exact Fintype.ofFinite _;
    exact ⟨ ( Classical.arbitrary _ ), trivial ⟩;
  refine' ⟨ _ ⟩;
  exact ( HilbertBasis.mk ( b.orthonormal.comp _ e.injective ) ( by
    have := b.dense_span;
    simp_all +decide [ Set.range_comp ] ) ).repr

theorem hilbert_classification (E F : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace.SeparableSpace E]
    [NormedAddCommGroup F] [InnerProductSpace ℝ F] [CompleteSpace F]
    [TopologicalSpace.SeparableSpace F]
    (hE : ¬ FiniteDimensional ℝ E) (hF : ¬ FiniteDimensional ℝ F) :
    Nonempty (E ≃ₗᵢ[ℝ] F) :=
  ⟨(exists_l2_iso E hE).some.trans (exists_l2_iso F hF).some.symm⟩

/-! ### H7. An atomless Borel probability measure on the unit sphere -/

theorem exists_atomless_sphere_measure (E : Type*)
    [NormedAddCommGroup E] [InnerProductSpace ℝ E] [CompleteSpace E]
    [MeasurableSpace E] [BorelSpace E]
    (e₀ e₁ : E) (h : Orthonormal ℝ ![e₀, e₁]) :
    ∃ μ : Measure E, IsProbabilityMeasure μ ∧
      (∀ x, μ {x} = 0) ∧
      ∀ᵐ v ∂μ, ‖v‖ = 1 := by
  -- Define the function φ : ℝ → E by φ(t) = cos(πt/2) • e₀ + sin(πt/2) • e₁.
  let φ : ℝ → E := fun t => Real.cos (Real.pi * t / 2) • e₀ + Real.sin (Real.pi * t / 2) • e₁;
  refine' ⟨ MeasureTheory.Measure.map φ unitMeasure, _, _, _ ⟩;
  · constructor;
    rw [ Measure.map_apply ] <;> norm_num;
    fun_prop;
  · intro x
    have h_preimage : MeasureTheory.volume (φ ⁻¹' {x} ∩ Set.Icc 0 1) = 0 := by
      have h_preimage : ∀ t₁ t₂ : ℝ, t₁ ∈ Set.Icc 0 1 → t₂ ∈ Set.Icc 0 1 → φ t₁ = φ t₂ → t₁ = t₂ := by
        intro t₁ t₂ ht₁ ht₂ h_eq
        have h_cos : Real.cos (Real.pi * t₁ / 2) = Real.cos (Real.pi * t₂ / 2) := by
          apply_fun ( fun x => inner ℝ x e₀ ) at h_eq;
          simp +zetaDelta at *;
          simp_all +decide [ inner_add_left, inner_smul_left ];
          simp_all +decide [ real_inner_comm ]
        have h_sin : Real.sin (Real.pi * t₁ / 2) = Real.sin (Real.pi * t₂ / 2) := by
          simp +zetaDelta at *;
          replace h_eq := congr_arg ( fun x => inner ℝ x e₁ ) h_eq ; simp_all +decide [ inner_add_left, inner_smul_left ];
        exact Eq.symm ( by apply_fun Real.arccos at h_cos; rw [ Real.arccos_cos, Real.arccos_cos ] at h_cos <;> nlinarith [ Real.pi_pos, ht₁.1, ht₁.2, ht₂.1, ht₂.2 ] );
      exact Set.Subsingleton.measure_zero ( fun t₁ ht₁ t₂ ht₂ => h_preimage t₁ t₂ ht₁.2 ht₂.2 <| by aesop ) MeasureTheory.MeasureSpace.volume;
    rw [ MeasureTheory.Measure.map_apply_of_aemeasurable ];
    · unfold unitMeasure; aesop;
    · fun_prop;
    · exact MeasurableSingletonClass.measurableSet_singleton x;
  · rw [ MeasureTheory.ae_map_iff ];
    · refine' Filter.Eventually.of_forall fun t => _;
      have := norm_add_sq_real ( Real.cos ( Real.pi * t / 2 ) • e₀ ) ( Real.sin ( Real.pi * t / 2 ) • e₁ ) ; simp_all +decide [ norm_smul, inner_smul_left, inner_smul_right ];
      exact this.resolve_right ( by linarith [ norm_nonneg ( Real.cos ( Real.pi * t / 2 ) • e₀ + Real.sin ( Real.pi * t / 2 ) • e₁ ) ] );
    · fun_prop;
    · exact measurableSet_eq_fun ( measurable_norm ) measurable_const

end PnpProof
