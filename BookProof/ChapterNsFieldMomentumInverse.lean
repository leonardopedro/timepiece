import Mathlib
import BookProof.ChapterNsSpatialMomentumMultiplier

/-!
# The inverse field momentum `π^{-1}`

Item 2 of the Navier–Stokes plan items of `CONSOLIDATED_PLAN.md`: *the constraint solved,
`D_j ψ = 0`*.  The field momentum is `π_m = −i ∂_m` in the fibre variable `u`, and the derivative
gauge, solved for the derivative mode, reads `u^{(1)}_j = p_j π^{-1}`.  The item asks for the
inverse `π^{-1}` and flags the domain question as the one genuine analytic residual: `π` is not
boundedly invertible.

Everything here is done in the momentum representation of the fibre variable, where — by
`BookProof.NsSpatialMultiplier.fourier_opL2_momentumOp`, re-exported below as
`isMomInverse_momentumOp` — the field momentum **is** multiplication by the real symbol
`momSymbol m ξ = 2π ⟪ξ, m⟫`.  `IsMomInverse m f g` is the relation `π_m g = f` there, i.e.
`g = π_m^{-1} f`.

What is proved, for a non-zero fibre direction `m`:

* `volume_momSymbol_zero`, `momSymbol_ne_zero_ae` — the symbol vanishes only on a hyperplane, a
  Lebesgue null set;
* `momentum_kernel_trivial` — hence **the kernel of the field momentum is trivial**: the
  `u`-constant mode that the plan flags is not an `L²` state, so no finite-dimensional kernel has
  to be split off, and `π^{-1}` is single valued (`isMomInverse_unique`);
* `isMomInverse_of_memLp` — the inverse exists exactly when the divided symbol is square
  integrable, which is the honest domain of `π^{-1}`;
* `momDomain` is a submodule and `momDomain_dense` — **`π^{-1}` is densely defined**, proved by
  cutting off a neighbourhood of the hyperplane `{σ = 0}`;
* `isMomInverse_smul` — `u^{(1)}_j = p_j π^{-1}`: the solution for the right-hand side `p_j ψ` is
  `p_j` times the inverse, which is the plan's identity on the physical sector;
* `eq_div_of_mul_eq_ae` — its symbol form: a symbol `t` with `σ · t = p` is `t = p / σ` almost
  everywhere, so the derivative mode is determined by the constraint;
* `isMomInverse_momentumOp` — the faithfulness statement: on the Schwartz core the relation
  `IsMomInverse` is satisfied by the `L²` realization of the honest operator `−i ∂_m` and its
  argument.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.NsFieldMomentumInverse

open MeasureTheory SchwartzMap FourierTransform
open BookProof.NsSpatialMultiplier BookProof.FourierMultiplierEsa BookProof.StrichartzWave

noncomputable section

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℝ W] [FiniteDimensional ℝ W]
  [MeasurableSpace W] [BorelSpace W]

/-! ## 1. The symbol of the field momentum, and where it vanishes -/

/-- The real symbol of the field momentum `π_m = −i ∂_m`: `ξ ↦ 2π ⟪ξ, m⟫`. -/
def momSymbol (m : W) (ξ : W) : ℝ := 2 * Real.pi * (inner ℝ ξ m)

omit [FiniteDimensional ℝ W] [MeasurableSpace W] [BorelSpace W] in
theorem continuous_momSymbol (m : W) : Continuous (momSymbol m) :=
  continuous_const.mul ((innerSL ℝ).flip m).continuous

omit [FiniteDimensional ℝ W] in
theorem measurable_momSymbol (m : W) : Measurable (momSymbol m) :=
  (continuous_momSymbol m).measurable

/-- **The symbol vanishes only on a hyperplane**, which is a Lebesgue null set. -/
theorem volume_momSymbol_zero {m : W} (hm : m ≠ 0) :
    (volume : Measure W) {ξ : W | momSymbol m ξ = 0} = 0 := by
  have h : {ξ : W | momSymbol m ξ = 0}
      = (LinearMap.ker ((innerSL ℝ m : W →L[ℝ] ℝ).toLinearMap) : Submodule ℝ W) := by
    ext x
    simp only [Set.mem_setOf_eq, SetLike.mem_coe, LinearMap.mem_ker,
      ContinuousLinearMap.coe_coe, innerSL_apply_apply, momSymbol]
    rw [real_inner_comm]
    constructor
    · intro hx
      have : (2 * Real.pi) ≠ 0 := by positivity
      exact (mul_eq_zero.mp hx).resolve_left this
    · intro hx
      rw [hx, mul_zero]
  rw [h]
  refine Measure.addHaar_submodule _ _ ?_
  intro htop
  have hmem : m ∈ LinearMap.ker ((innerSL ℝ m : W →L[ℝ] ℝ).toLinearMap) := by
    rw [htop]; trivial
  have hm' : (inner ℝ m m : ℝ) = 0 := by simpa [LinearMap.mem_ker] using hmem
  exact hm (inner_self_eq_zero.mp hm')

/-- Almost every frequency has non-zero symbol. -/
theorem momSymbol_ne_zero_ae {m : W} (hm : m ≠ 0) :
    ∀ᵐ ξ ∂(volume : Measure W), momSymbol m ξ ≠ 0 := by
  have h := volume_momSymbol_zero hm
  rw [MeasureTheory.ae_iff]
  simpa using h

/-! ## 2. The inverse field momentum -/

/-- **`g = π_m^{-1} f`**, in the momentum representation of the fibre variable: multiplying `g` by
the symbol of the field momentum returns `f`. -/
def IsMomInverse (m : W) (f g : Lp ℂ 2 (volume : Measure W)) : Prop :=
  (fun ξ => ((momSymbol m ξ : ℝ) : ℂ) * (g : W → ℂ) ξ) =ᵐ[(volume : Measure W)] (f : W → ℂ)

/-- **The field momentum has trivial kernel.**  The `u`-constant mode is not an `L²` state, so
nothing has to be split off before inverting. -/
theorem momentum_kernel_trivial {m : W} (hm : m ≠ 0) (g : Lp ℂ 2 (volume : Measure W))
    (h : IsMomInverse m 0 g) : g = 0 := by
  refine (MeasureTheory.Lp.eq_zero_iff_ae_eq_zero).2 ?_
  filter_upwards [h, momSymbol_ne_zero_ae hm,
    MeasureTheory.Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure W))] with ξ hξ hσ hz
  rw [hz] at hξ
  have : ((momSymbol m ξ : ℝ) : ℂ) ≠ 0 := by
    simpa using hσ
  exact (mul_eq_zero.mp hξ).resolve_left this

/-- `π^{-1}` is single valued. -/
theorem isMomInverse_unique {m : W} (hm : m ≠ 0) {f g₁ g₂ : Lp ℂ 2 (volume : Measure W)}
    (h₁ : IsMomInverse m f g₁) (h₂ : IsMomInverse m f g₂) : g₁ = g₂ := by
  have h : IsMomInverse m 0 (g₁ - g₂) := by
    filter_upwards [h₁, h₂, MeasureTheory.Lp.coeFn_sub g₁ g₂,
      MeasureTheory.Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure W))] with
      ξ hx₁ hx₂ hsub hz
    simp only [hsub, hz, Pi.sub_apply, Pi.zero_apply, mul_sub, hx₁, hx₂, sub_self]
  have := momentum_kernel_trivial hm _ h
  exact sub_eq_zero.mp this

/-- **The domain of `π^{-1}`**: the states whose divided symbol is again square integrable. -/
theorem isMomInverse_of_memLp {m : W} (hm : m ≠ 0) (f : Lp ℂ 2 (volume : Measure W))
    (hf : MemLp (fun ξ => (f : W → ℂ) ξ / ((momSymbol m ξ : ℝ) : ℂ)) 2 (volume : Measure W)) :
    IsMomInverse m f hf.toLp := by
  filter_upwards [hf.coeFn_toLp, momSymbol_ne_zero_ae hm] with ξ hξ hσ
  rw [hξ]
  have : ((momSymbol m ξ : ℝ) : ℂ) ≠ 0 := by simpa using hσ
  field_simp

/-- The set of states on which `π^{-1}` is defined, as a submodule. -/
def momDomain (m : W) : Submodule ℂ (Lp ℂ 2 (volume : Measure W)) where
  carrier := {f | ∃ g, IsMomInverse m f g}
  zero_mem' := by
    refine ⟨0, ?_⟩
    filter_upwards [MeasureTheory.Lp.coeFn_zero (E := ℂ) (p := 2) (μ := (volume : Measure W))]
      with ξ hz
    rw [hz]
    simp
  add_mem' := by
    rintro f₁ f₂ ⟨g₁, h₁⟩ ⟨g₂, h₂⟩
    refine ⟨g₁ + g₂, ?_⟩
    filter_upwards [h₁, h₂, MeasureTheory.Lp.coeFn_add g₁ g₂,
      MeasureTheory.Lp.coeFn_add f₁ f₂] with ξ hx₁ hx₂ hg hf
    rw [hg, hf]
    simp only [Pi.add_apply, mul_add]
    rw [hx₁, hx₂]
  smul_mem' := by
    rintro c f ⟨g, h⟩
    refine ⟨c • g, ?_⟩
    filter_upwards [h, MeasureTheory.Lp.coeFn_smul c g, MeasureTheory.Lp.coeFn_smul c f]
      with ξ hx hg hf
    rw [hg, hf]
    simp only [Pi.smul_apply, smul_eq_mul]
    rw [← mul_assoc, mul_comm _ c, mul_assoc, hx]

theorem mem_momDomain_iff {m : W} (f : Lp ℂ 2 (volume : Measure W)) :
    f ∈ momDomain m ↔ ∃ g, IsMomInverse m f g := Iff.rfl

/-! ## 3. `π^{-1}` is densely defined -/

/-- The frequencies where the symbol is bounded away from zero by `1 / (n + 1)`. -/
def cutSet (m : W) (n : ℕ) : Set W := {ξ : W | 1 / ((n : ℝ) + 1) ≤ |momSymbol m ξ|}

omit [FiniteDimensional ℝ W] in
theorem measurableSet_cutSet (m : W) (n : ℕ) : MeasurableSet (cutSet m n) :=
  measurableSet_le measurable_const (measurable_momSymbol m).abs

/-- The cut-off of a state to the frequencies where the symbol is bounded away from zero. -/
def cut (m : W) (n : ℕ) (f : Lp ℂ 2 (volume : Measure W)) : Lp ℂ 2 (volume : Measure W) :=
  ((MeasureTheory.Lp.memLp f).indicator (measurableSet_cutSet m n)).toLp

theorem coeFn_cut (m : W) (n : ℕ) (f : Lp ℂ 2 (volume : Measure W)) :
    (cut m n f : W → ℂ) =ᵐ[(volume : Measure W)] (cutSet m n).indicator (f : W → ℂ) :=
  ((MeasureTheory.Lp.memLp f).indicator (measurableSet_cutSet m n)).coeFn_toLp

/-- Every cut-off state lies in the domain of `π^{-1}`. -/
theorem cut_mem_momDomain {m : W} (hm : m ≠ 0) (n : ℕ) (f : Lp ℂ 2 (volume : Measure W)) :
    cut m n f ∈ momDomain m := by
  have hmeas : AEStronglyMeasurable
      (fun ξ => (cut m n f : W → ℂ) ξ / ((momSymbol m ξ : ℝ) : ℂ)) (volume : Measure W) :=
    ((MeasureTheory.Lp.aestronglyMeasurable (cut m n f)).aemeasurable.div
      ((Complex.continuous_ofReal.comp
        (continuous_momSymbol m)).measurable.aemeasurable)).aestronglyMeasurable
  have hdom : MemLp (fun ξ => (((n : ℝ) + 1) : ℂ) * (f : W → ℂ) ξ) 2 (volume : Measure W) :=
    (MeasureTheory.Lp.memLp f).const_mul _
  have hbound : ∀ᵐ ξ ∂(volume : Measure W),
      ‖(cut m n f : W → ℂ) ξ / ((momSymbol m ξ : ℝ) : ℂ)‖
        ≤ ‖(((n : ℝ) + 1) : ℂ) * (f : W → ℂ) ξ‖ := by
    filter_upwards [coeFn_cut m n f] with ξ hξ
    rw [hξ]
    by_cases hmem : ξ ∈ cutSet m n
    · have hlow : 1 / ((n : ℝ) + 1) ≤ |momSymbol m ξ| := hmem
      have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hσ : |momSymbol m ξ| ≠ 0 := by
        have : (0 : ℝ) < 1 / ((n : ℝ) + 1) := by positivity
        exact ne_of_gt (lt_of_lt_of_le this hlow)
      rw [Set.indicator_of_mem hmem, norm_div, Complex.norm_real, Real.norm_eq_abs, norm_mul]
      rw [div_le_iff₀ (lt_of_le_of_ne (abs_nonneg _) (Ne.symm hσ))]
      have hn : ‖(((n : ℝ) + 1) : ℂ)‖ = (n : ℝ) + 1 := by
        have : (((n : ℝ) + 1) : ℂ) = ((((n : ℝ) + 1) : ℝ) : ℂ) := by push_cast; ring
        rw [this, Complex.norm_real, Real.norm_eq_abs, abs_of_pos hpos]
      rw [hn]
      calc ‖(f : W → ℂ) ξ‖ = ‖(f : W → ℂ) ξ‖ * (((n : ℝ) + 1) * (1 / ((n : ℝ) + 1))) := by
            rw [mul_one_div_cancel (ne_of_gt hpos), mul_one]
        _ ≤ ‖(f : W → ℂ) ξ‖ * (((n : ℝ) + 1) * |momSymbol m ξ|) := by
            gcongr
        _ = ((n : ℝ) + 1) * ‖(f : W → ℂ) ξ‖ * |momSymbol m ξ| := by ring
    · rw [Set.indicator_of_notMem hmem]
      simp only [zero_div, norm_zero]
      positivity
  exact ⟨_, isMomInverse_of_memLp hm _ (hdom.of_le hmeas hbound)⟩

/-- **`π^{-1}` is densely defined**: the states whose divided symbol is square integrable are dense
in `L²`.  Cutting off a neighbourhood of the hyperplane `{σ = 0}` changes a state by as little as
one likes, because that hyperplane is null. -/
theorem momDomain_dense {m : W} (hm : m ≠ 0) :
    Dense ((momDomain m : Set (Lp ℂ 2 (volume : Measure W)))) := by
  rw [Submodule.dense_iff_topologicalClosure_eq_top, Submodule.topologicalClosure_eq_top_iff]
  refine Submodule.eq_bot_iff _ |>.2 fun h hh => ?_
  -- `h` is orthogonal to every cut-off state, hence vanishes on every cut set
  have hzero : ∀ n : ℕ, ∀ᵐ ξ ∂(volume : Measure W), ξ ∈ cutSet m n → (h : W → ℂ) ξ = 0 := by
    intro n
    have hmem : cut m n h ∈ momDomain m := cut_mem_momDomain hm n h
    have hinner : (inner ℂ (cut m n h) h : ℂ) = 0 := hh _ hmem
    have hint : (∫ ξ, (cutSet m n).indicator (fun ξ => (‖(h : W → ℂ) ξ‖ ^ 2 : ℝ)) ξ) = 0 := by
      have hcalc : (inner ℂ (cut m n h) h : ℂ)
          = ((∫ ξ, (cutSet m n).indicator (fun ξ => (‖(h : W → ℂ) ξ‖ ^ 2 : ℝ)) ξ : ℝ) : ℂ) := by
        rw [MeasureTheory.L2.inner_def]
        rw [← integral_complex_ofReal]
        refine integral_congr_ae ?_
        filter_upwards [coeFn_cut m n h] with ξ hξ
        rw [hξ]
        by_cases hmemξ : ξ ∈ cutSet m n
        · rw [Set.indicator_of_mem hmemξ, Set.indicator_of_mem hmemξ,
            inner_self_eq_norm_sq_to_K]
          norm_cast
        · rw [Set.indicator_of_notMem hmemξ, Set.indicator_of_notMem hmemξ]
          simp
      rw [hcalc] at hinner
      exact_mod_cast hinner
    have hnonneg : 0 ≤ᵐ[(volume : Measure W)]
        fun ξ => (cutSet m n).indicator (fun ξ => (‖(h : W → ℂ) ξ‖ ^ 2 : ℝ)) ξ :=
      Filter.Eventually.of_forall fun ξ => Set.indicator_nonneg (fun _ _ => by positivity) ξ
    have hintg : Integrable
        (fun ξ => (cutSet m n).indicator (fun ξ => (‖(h : W → ℂ) ξ‖ ^ 2 : ℝ)) ξ)
        (volume : Measure W) := by
      have : Integrable (fun ξ => (‖(h : W → ℂ) ξ‖ ^ 2 : ℝ)) (volume : Measure W) := by
        simpa [Real.rpow_natCast] using
          (MeasureTheory.Lp.memLp h).integrable_norm_rpow (by norm_num) (by norm_num)
      exact this.indicator (measurableSet_cutSet m n)
    have hae := (integral_eq_zero_iff_of_nonneg_ae hnonneg hintg).1 hint
    filter_upwards [hae] with ξ hξ hmemξ
    rw [Set.indicator_of_mem hmemξ] at hξ
    have : ‖(h : W → ℂ) ξ‖ = 0 := by
      have := hξ
      simpa [pow_eq_zero_iff] using this
    simpa using this
  have hall : ∀ᵐ ξ ∂(volume : Measure W), ∀ n : ℕ, ξ ∈ cutSet m n → (h : W → ℂ) ξ = 0 :=
    (MeasureTheory.ae_all_iff).2 hzero
  refine (Submodule.mem_bot ℂ).2 ?_
  refine (MeasureTheory.Lp.eq_zero_iff_ae_eq_zero).2 ?_
  filter_upwards [hall, momSymbol_ne_zero_ae hm] with ξ hξ hσ
  obtain ⟨n, hn⟩ := exists_nat_one_div_lt (show (0:ℝ) < |momSymbol m ξ| from abs_pos.2 hσ)
  exact hξ n (le_of_lt hn)

/-! ## 4. The identity of the physical sector, `u^{(1)}_j = p_j π^{-1}` -/

/-- **`u^{(1)}_j = p_j π^{-1}`**: the solution of the constraint with the right-hand side scaled by
the spatial frequency is the same multiple of the inverse field momentum. -/
theorem isMomInverse_smul {m : W} (c : ℂ) {f g : Lp ℂ 2 (volume : Measure W)}
    (h : IsMomInverse m f g) : IsMomInverse m (c • f) (c • g) := by
  filter_upwards [h, MeasureTheory.Lp.coeFn_smul c g, MeasureTheory.Lp.coeFn_smul c f]
    with ξ hx hg hf
  rw [hg, hf]
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← mul_assoc, mul_comm _ c, mul_assoc, hx]

/-- The symbol form of the same statement: a derivative symbol `t` constrained by `σ · t = p` is
`p / σ` almost everywhere — the derivative mode is `p_j π^{-1}`. -/
theorem eq_div_of_mul_eq_ae {m : W} (hm : m ≠ 0) (t : W → ℂ) (p : ℂ)
    (h : ∀ᵐ ξ ∂(volume : Measure W), ((momSymbol m ξ : ℝ) : ℂ) * t ξ = p) :
    ∀ᵐ ξ ∂(volume : Measure W), t ξ = p / ((momSymbol m ξ : ℝ) : ℂ) := by
  filter_upwards [h, momSymbol_ne_zero_ae hm] with ξ hξ hσ
  have hσ' : ((momSymbol m ξ : ℝ) : ℂ) ≠ 0 := by simpa using hσ
  rw [eq_div_iff hσ', mul_comm]
  exact hξ

/-! ## 5. Faithfulness: the relation is the honest operator `−i ∂_m` -/

/-- **The relation `IsMomInverse` is the field momentum.**  On the Schwartz core, the `L²`
realization of `−i ∂_m` and its argument, both read in the momentum representation, satisfy it. -/
theorem isMomInverse_momentumOp (m : W) (f : 𝓢(W, ℂ)) :
    IsMomInverse m (l2Fourier W (opL2 (momentumOp m) (schwartzEquiv W f)))
      (l2Fourier W (f.toLp 2 (volume : Measure W))) := by
  have hrep := fourier_opL2_momentumOp m f
  have hl : (l2Fourier W (f.toLp 2 (volume : Measure W)) : W → ℂ)
      =ᵐ[(volume : Measure W)] fun ξ => (𝓕 f : 𝓢(W, ℂ)) ξ := by
    rw [l2Fourier_apply, SchwartzMap.toLp_fourier_eq]
    exact (𝓕 f : 𝓢(W, ℂ)).coeFn_toLp 2 (volume : Measure W)
  have hr : (l2Fourier W (opL2 (momentumOp m) (schwartzEquiv W f)) : W → ℂ)
      =ᵐ[(volume : Measure W)]
        fun ξ => ((momSymbol m ξ : ℝ) : ℂ) * (𝓕 f : 𝓢(W, ℂ)) ξ := by
    rw [hrep]
    filter_upwards [(mulSymbolOp (fun x => 2 * Real.pi * (inner ℝ x m : ℝ))
      (𝓕 f : 𝓢(W, ℂ))).coeFn_toLp 2 (volume : Measure W)] with ξ hξ
    rw [hξ]
    have hσ : Function.HasTemperateGrowth
        (fun x : W => ((2 * Real.pi * (inner ℝ x m : ℝ) : ℝ) : ℂ)) := by
      have h := hasTemperateGrowth_foSymbol (fun _ : Fin 1 => (1 : ℝ)) (fun _ => m)
      simpa [foSymbolFn] using h
    rw [mulSymbolOp_apply _ hσ]
    rfl
  filter_upwards [hl, hr] with ξ hxl hxr
  rw [hxl, hxr]

end

end BookProof.NsFieldMomentumInverse
