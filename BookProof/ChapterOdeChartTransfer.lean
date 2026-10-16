import Mathlib
import BookProof.ChapterMomentumChartEsa
import BookProof.ChapterOdeUnitaryFlow
import BookProof.ChapterStoneBridge

/-!
# ODE-C.2 / ODE-C.3 — the quantized vector field of `ẋ = x²` is essentially self-adjoint
**in the chart realization**

`CONSOLIDATED_PLAN.md` §"2026-10-15b", rows ODE-C.2 and ODE-C.3.

`BookProof.OdeUnitaryFlow` shows that the evolution of the quantized vector field
`H = x² p − i x` of `ẋ = x²` is, after the change of variables `w = −1/x` implemented by
`(Wψ)(x) = ψ(−1/x)/x` (`chartW`), the translation group of the `w`-line
(`odeKoop_chartW`), and that `W` preserves the `L²` norm (`chartW_lintegral_normSq`).  This
module

1. turns `chartW` into a genuine **unitary** `chartUnitary : L²(ℝ) ≃ₗᵢ[ℂ] L²(ℝ)`
   (`chartUnitary_apply`: it acts by `chartW` almost everywhere; `W² = −1`);
2. proves the generic fact that a unitary conjugation carries essential self-adjointness
   (`conj_essentiallySelfAdjointOn`) — the `EssentiallySelfAdjointOn` analogue of
   `densitized_hasZeroDeficiencyOn_transfer`;
3. transports ODE-C.1 (`momentum_essentiallySelfAdjointOn`) through the chart:
   **`chartHam_essentiallySelfAdjointOn`** — the operator `chartHam = W P W⁻¹` is essentially
   self-adjoint on the chart domain `chartDomain = W(𝓢(ℝ))`, and
   `chartHam_apply_ae` identifies it there with the quantized vector field:
   `(chartHam (W ψ))(x) = x² (−i (Wψ)'(x)) − i x (Wψ)(x)` for a.e. `x`;
4. (ODE-C.3) feeds the result into the Stone bridge: `chartHam_stone_flow`.

## The domain is part of the statement

The verdict is for the **chart realization**: the operator `H = x² p − i x` on the domain
`W(𝓢(ℝ))`.  It is *not* a statement about `H` on a domain such as `C_c^∞(ℝ)` of `L²(ℝ)`;
`Book/OdeSingularity.lean` keeps the correction that `H` there is not essentially
self-adjoint (its classical flow is incomplete).  Functions in `W(𝓢(ℝ))` behave like
`x⁻¹ ψ(−1/x)` near `x = 0` and decay like `x⁻¹` at infinity; these are exactly the states
for which the flow through the blow-up is complete.
-/

namespace BookProof.OdeChartTransfer

open MeasureTheory Filter Set
open scoped ENNReal
open BookProof.FarisLavine BookProof.OdeUnitaryFlow BookProof.StrichartzWave
  BookProof.MomentumChart

noncomputable section

/-! ## 1. Unitary conjugation carries essential self-adjointness -/

section Conj

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- The image `W(D)` of a domain under a unitary. -/
def conjDomain (W : F ≃ₗᵢ[ℂ] G) (D : Submodule ℂ F) : Submodule ℂ G :=
  D.map (W.toLinearEquiv : F →ₗ[ℂ] G)

/-- The identification `D ≃ W(D)`. -/
def conjEquiv (W : F ≃ₗᵢ[ℂ] G) (D : Submodule ℂ F) : D ≃ₗ[ℂ] conjDomain W D :=
  Submodule.equivMapOfInjective (W.toLinearEquiv : F →ₗ[ℂ] G) W.injective D

@[simp] theorem conjEquiv_coe (W : F ≃ₗᵢ[ℂ] G) (D : Submodule ℂ F) (x : D) :
    ((conjEquiv W D x : conjDomain W D) : G) = W (x : F) := rfl

/-- The conjugated operator `W T W⁻¹` on `W(D)`. -/
def conjOp (W : F ≃ₗᵢ[ℂ] G) (D : Submodule ℂ F) (T : D →ₗ[ℂ] F) :
    conjDomain W D →ₗ[ℂ] G :=
  (W.toLinearEquiv : F →ₗ[ℂ] G) ∘ₗ T ∘ₗ (conjEquiv W D).symm.toLinearMap

@[simp] theorem conjOp_conjEquiv (W : F ≃ₗᵢ[ℂ] G) (D : Submodule ℂ F) (T : D →ₗ[ℂ] F)
    (x : D) : conjOp W D T (conjEquiv W D x) = W (T x) := by
  simp [conjOp]

theorem conj_symmetricOn (W : F ≃ₗᵢ[ℂ] G) {D : Submodule ℂ F} {T : D →ₗ[ℂ] F}
    (hT : SymmetricOn D T) : SymmetricOn (conjDomain W D) (conjOp W D T) := by
  intro y₁ y₂
  obtain ⟨x₁, rfl⟩ := (conjEquiv W D).surjective y₁
  obtain ⟨x₂, rfl⟩ := (conjEquiv W D).surjective y₂
  rw [conjOp_conjEquiv, conjOp_conjEquiv, conjEquiv_coe, conjEquiv_coe,
    LinearIsometryEquiv.inner_map_map, LinearIsometryEquiv.inner_map_map]
  exact hT x₁ x₂

theorem conj_deficiencyTrivialAt (W : F ≃ₗᵢ[ℂ] G) {D : Submodule ℂ F} {T : D →ₗ[ℂ] F}
    {z : ℂ} (h : DeficiencyTrivialAt D T z) :
    DeficiencyTrivialAt (conjDomain W D) (conjOp W D T) z := by
  intro w hw
  have hu : W.symm w = 0 := by
    refine h (W.symm w) fun x => ?_
    have hx := hw (conjEquiv W D x)
    rw [conjOp_conjEquiv, conjEquiv_coe] at hx
    rw [← LinearIsometryEquiv.inner_map_map W, ← LinearIsometryEquiv.inner_map_map W (x : F),
      LinearIsometryEquiv.apply_symm_apply]
    exact hx
  simpa using congrArg W hu

/-- **Unitary conjugation carries essential self-adjointness.** -/
theorem conj_essentiallySelfAdjointOn (W : F ≃ₗᵢ[ℂ] G) {D : Submodule ℂ F} {T : D →ₗ[ℂ] F}
    (h : EssentiallySelfAdjointOn D T) :
    EssentiallySelfAdjointOn (conjDomain W D) (conjOp W D T) :=
  ⟨conj_deficiencyTrivialAt W h.1, conj_deficiencyTrivialAt W h.2⟩

theorem conjDomain_dense (W : F ≃ₗᵢ[ℂ] G) {D : Submodule ℂ F} (hD : Dense (D : Set F)) :
    Dense (conjDomain W D : Set G) := by
  have h : (conjDomain W D : Set G) = W '' (D : Set F) := by
    rw [conjDomain, Submodule.map_coe]
    rfl
  rw [h]
  exact W.surjective.denseRange.dense_image W.continuous hD

end Conj

/-! ## 2. The chart `W` is a unitary of `L²(ℝ)` -/

section ChartUnitary

theorem measurable_invMap : Measurable invMap := by
  unfold invMap
  fun_prop

/-- `x ↦ −1/x` does not create mass out of null sets. -/
theorem quasiMeasurePreserving_invMap :
    Measure.QuasiMeasurePreserving invMap (volume : Measure ℝ) volume := by
  refine ⟨measurable_invMap, ?_⟩
  refine Measure.AbsolutelyContinuous.mk fun s hs hs0 => ?_
  rw [Measure.map_apply measurable_invMap hs]
  have key := lintegral_comp_invMap (s.indicator fun _ => (1 : ℝ≥0∞))
  rw [lintegral_indicator hs, setLIntegral_const, one_mul, hs0] at key
  have hmeas : Measurable fun x : ℝ =>
      ENNReal.ofReal ((x ^ 2)⁻¹) * s.indicator (fun _ => (1 : ℝ≥0∞)) (invMap x) := by
    refine Measurable.mul ?_ ?_
    · exact ENNReal.measurable_ofReal.comp (by fun_prop)
    · exact (measurable_const.indicator hs).comp measurable_invMap
  rw [lintegral_eq_zero_iff hmeas] at key
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
    simp [ae_iff, measure_singleton]
  rw [← compl_mem_ae_iff]
  filter_upwards [key, hne] with x hx hx0
  intro hxs
  have h1 : s.indicator (fun _ => (1 : ℝ≥0∞)) (invMap x) = 1 := by
    simp [Set.indicator_of_mem (show invMap x ∈ s from hxs)]
  have h2 : ENNReal.ofReal ((x ^ 2)⁻¹) ≠ 0 := by
    rw [ne_eq, ENNReal.ofReal_eq_zero, not_le]
    positivity
  have h3 := hx
  simp only [Pi.zero_apply, h1, mul_one] at h3
  exact h2 h3

theorem chartW_aestronglyMeasurable {ψ : ℝ → ℂ}
    (hψ : AEStronglyMeasurable ψ (volume : Measure ℝ)) :
    AEStronglyMeasurable (chartW ψ) (volume : Measure ℝ) := by
  have h1 : AEStronglyMeasurable (fun x : ℝ => ψ (invMap x)) (volume : Measure ℝ) :=
    hψ.comp_quasiMeasurePreserving quasiMeasurePreserving_invMap
  have h2 : AEStronglyMeasurable (fun x : ℝ => ((x : ℝ) : ℂ)⁻¹) (volume : Measure ℝ) :=
    (by fun_prop : Measurable fun x : ℝ => ((x : ℝ) : ℂ)⁻¹).aestronglyMeasurable
  exact h2.mul h1

theorem chartW_lintegral_enorm (ψ : ℝ → ℂ) :
    ∫⁻ x, ‖chartW ψ x‖ₑ ^ (2 : ℝ) = ∫⁻ y, ‖ψ y‖ₑ ^ (2 : ℝ) := by
  have h := chartW_lintegral_normSq ψ
  have hc : ∀ a : ℂ, ENNReal.ofReal (‖a‖ ^ 2) = ‖a‖ₑ ^ (2 : ℝ) := by
    intro a
    rw [ENNReal.rpow_two, ENNReal.ofReal_pow (norm_nonneg a), ofReal_norm_eq_enorm]
  simp only [hc] at h
  exact h

theorem chartW_eLpNorm (ψ : ℝ → ℂ) :
    eLpNorm (chartW ψ) 2 (volume : Measure ℝ) = eLpNorm ψ 2 (volume : Measure ℝ) := by
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num),
    eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  simp only [ENNReal.toReal_ofNat]
  rw [chartW_lintegral_enorm]

theorem chartW_memLp {ψ : ℝ → ℂ} (hψ : MemLp ψ 2 (volume : Measure ℝ)) :
    MemLp (chartW ψ) 2 (volume : Measure ℝ) :=
  ⟨chartW_aestronglyMeasurable hψ.1, by rw [chartW_eLpNorm]; exact hψ.2⟩

theorem chartW_congr_ae {ψ φ : ℝ → ℂ} (h : ψ =ᵐ[volume] φ) :
    chartW ψ =ᵐ[volume] chartW φ := by
  have h' := h.comp_tendsto quasiMeasurePreserving_invMap.tendsto_ae
  filter_upwards [h'] with x hx
  simp only [chartW, Function.comp_apply] at hx ⊢
  rw [hx]

theorem chartW_add (ψ φ : ℝ → ℂ) : chartW (ψ + φ) = chartW ψ + chartW φ := by
  funext x; simp [chartW, mul_add]

theorem chartW_smul (c : ℂ) (ψ : ℝ → ℂ) : chartW (c • ψ) = c • chartW ψ := by
  funext x; simp [chartW]; ring

/-- `W` applied twice is `−1` (away from `x = 0`). -/
theorem chartW_chartW (ψ : ℝ → ℂ) {x : ℝ} (hx : x ≠ 0) : chartW (chartW ψ) x = -ψ x := by
  have hxc : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx
  simp only [chartW, invMap_invMap hx]
  simp only [invMap]
  push_cast
  field_simp

/-- `W` as a linear map of `L²(ℝ)`. -/
def chartLin : Lp ℂ 2 (volume : Measure ℝ) →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) where
  toFun f := (chartW_memLp (Lp.memLp f)).toLp _
  map_add' f g := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp (chartW_memLp (Lp.memLp (f + g))),
      Lp.coeFn_add ((chartW_memLp (Lp.memLp f)).toLp _) ((chartW_memLp (Lp.memLp g)).toLp _),
      MemLp.coeFn_toLp (chartW_memLp (Lp.memLp f)), MemLp.coeFn_toLp (chartW_memLp (Lp.memLp g)),
      chartW_congr_ae (Lp.coeFn_add f g)] with x h1 h2 h3 h4 h5
    rw [h1, h2, Pi.add_apply, h3, h4, h5, chartW_add, Pi.add_apply]
  map_smul' c f := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp (chartW_memLp (Lp.memLp (c • f))),
      Lp.coeFn_smul c ((chartW_memLp (Lp.memLp f)).toLp _),
      MemLp.coeFn_toLp (chartW_memLp (Lp.memLp f)),
      chartW_congr_ae (Lp.coeFn_smul c f)] with x h1 h2 h3 h4
    rw [h1, RingHom.id_apply, h2, Pi.smul_apply, h3, h4, chartW_smul, Pi.smul_apply]

theorem chartLin_apply (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (chartLin f : ℝ → ℂ) =ᵐ[volume] chartW f :=
  MemLp.coeFn_toLp (chartW_memLp (Lp.memLp f))

theorem norm_chartLin (f : Lp ℂ 2 (volume : Measure ℝ)) : ‖chartLin f‖ = ‖f‖ := by
  rw [Lp.norm_def, Lp.norm_def, eLpNorm_congr_ae (chartLin_apply f), chartW_eLpNorm]

/-- `W` as a linear isometry. -/
def chartIsom : Lp ℂ 2 (volume : Measure ℝ) →ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  ⟨chartLin, norm_chartLin⟩

theorem chartIsom_chartIsom (f : Lp ℂ 2 (volume : Measure ℝ)) :
    chartIsom (chartIsom f) = -f := by
  refine Lp.ext ?_
  have h1 : (chartIsom (chartIsom f) : ℝ → ℂ) =ᵐ[volume] chartW (chartIsom f) :=
    chartLin_apply _
  have h2 : chartW (chartIsom f : ℝ → ℂ) =ᵐ[volume] chartW (chartW f) :=
    chartW_congr_ae (chartLin_apply f)
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
    simp [ae_iff, measure_singleton]
  filter_upwards [h1, h2, Lp.coeFn_neg f, hne] with x hx1 hx2 hx3 hx0
  rw [hx1, hx2, hx3, Pi.neg_apply, chartW_chartW _ hx0]

theorem chartIsom_surjective : Function.Surjective chartIsom := fun g =>
  ⟨-chartIsom g, by rw [map_neg, chartIsom_chartIsom, neg_neg]⟩

/-- **The chart unitary** `(W ψ)(x) = ψ(−1/x)/x` of `L²(ℝ)`. -/
def chartUnitary : Lp ℂ 2 (volume : Measure ℝ) ≃ₗᵢ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  LinearIsometryEquiv.ofSurjective chartIsom chartIsom_surjective

/-- The chart unitary acts by `chartW` almost everywhere. -/
theorem chartUnitary_apply (f : Lp ℂ 2 (volume : Measure ℝ)) :
    (chartUnitary f : ℝ → ℂ) =ᵐ[volume] chartW f :=
  chartLin_apply f

/-- `W² = −1`. -/
theorem chartUnitary_chartUnitary (f : Lp ℂ 2 (volume : Measure ℝ)) :
    chartUnitary (chartUnitary f) = -f :=
  chartIsom_chartIsom f

end ChartUnitary

/-! ## 3. The quantized vector field on the chart domain -/

section Transfer

/-- The Schwartz core is dense in `L²(ℝ)`. -/
theorem schwartzDomain_real_dense :
    Dense ((schwartzDomain ℝ : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ))) :
      Set (Lp ℂ 2 (volume : Measure ℝ))) := by
  have hd : Dense {f : Lp ℂ 2 (volume : Measure ℝ) | ∃ g, (f : ℝ → ℂ) =ᵐ[volume] g ∧
      HasCompactSupport g ∧ ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) g} :=
    MeasureTheory.Lp.dense_hasCompactSupport_contDiff (by norm_num)
  refine Dense.mono ?_ hd
  rintro f ⟨g, hfg, hgc, hgs⟩
  refine ⟨hgc.toSchwartzMap hgs, ?_⟩
  refine MeasureTheory.Lp.ext ?_
  filter_upwards [(hgc.toSchwartzMap hgs).coeFn_toLp 2 (volume : Measure ℝ), hfg]
    with x hx hy
  change ((hgc.toSchwartzMap hgs).toLp 2 (volume : Measure ℝ) : ℝ → ℂ) x = _
  rw [hx, hy]
  rfl

/-- **The chart domain** `W(𝓢(ℝ))` of `L²(ℝ, dx)`. -/
def chartDomain : Submodule ℂ (Lp ℂ 2 (volume : Measure ℝ)) :=
  conjDomain chartUnitary (schwartzDomain ℝ)

/-- **The chart realization of the quantized vector field**: `W P W⁻¹` on `W(𝓢(ℝ))`, with
`P = −i d/dw`. -/
def chartHam : chartDomain →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  conjOp chartUnitary (schwartzDomain ℝ) (opL2 chartMomentum)

theorem chartDomain_dense : Dense (chartDomain : Set (Lp ℂ 2 (volume : Measure ℝ))) :=
  conjDomain_dense chartUnitary schwartzDomain_real_dense

theorem chartHam_symmetricOn : SymmetricOn chartDomain chartHam :=
  conj_symmetricOn chartUnitary chartMomentum_symmetricOn

/-- **ODE-C.2.**  The quantized vector field of `ẋ = x²`, in its chart realization
`W P W⁻¹` on the chart domain `W(𝓢(ℝ))`, is essentially self-adjoint. -/
theorem chartHam_essentiallySelfAdjointOn : EssentiallySelfAdjointOn chartDomain chartHam :=
  conj_essentiallySelfAdjointOn chartUnitary momentum_essentiallySelfAdjointOn

/-- The pointwise identity behind the chart: `W (−i ψ') = H (W ψ)` with
`H = x² p − i x`, at every `x ≠ 0` where `ψ` is differentiable at `−1/x`. -/
theorem hamValue_chartW (ψ : ℝ → ℂ) {x : ℝ} (hx : x ≠ 0)
    (hψ : DifferentiableAt ℝ ψ (invMap x)) :
    hamValue x (deriv (chartW ψ) x) (chartW ψ x)
      = chartW (fun w => -Complex.I * deriv ψ w) x := by
  have hxc : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx
  have hinv : HasDerivAt (fun y : ℝ => ((y : ℝ) : ℂ)⁻¹) (((-(x ^ 2)⁻¹ : ℝ) : ℂ)) x := by
    have h := (hasDerivAt_inv hx).ofReal_comp
    have hf : (fun y : ℝ => ((y⁻¹ : ℝ) : ℂ)) = fun y : ℝ => ((y : ℝ) : ℂ)⁻¹ := by
      funext y; push_cast; rfl
    rw [hf] at h
    exact h
  have hcomp : HasDerivAt (fun y : ℝ => ψ (invMap y)) (((x ^ 2)⁻¹ : ℝ) • deriv ψ (invMap x)) x :=
    hψ.hasDerivAt.scomp x (hasDerivAt_invMap hx)
  have hd : HasDerivAt (chartW ψ)
      (((-(x ^ 2)⁻¹ : ℝ) : ℂ) * ψ (invMap x)
        + ((x : ℝ) : ℂ)⁻¹ * (((x ^ 2)⁻¹ : ℝ) • deriv ψ (invMap x))) x :=
    hinv.mul hcomp
  rw [hd.deriv]
  simp only [hamValue, chartW, Complex.real_smul]
  push_cast
  field_simp
  ring

/-- **The chart operator is the quantized vector field.**  For a Schwartz function `ψ`,
`chartHam` sends the chart state `W ψ` to `x ↦ x² (−i (Wψ)'(x)) − i x (Wψ)(x)`
(almost everywhere): on the chart domain, `chartHam` is `H = x² p − i x`. -/
theorem chartHam_apply_ae (ψ : SchwartzMap ℝ ℂ) :
    (chartHam (conjEquiv chartUnitary (schwartzDomain ℝ) (schwartzEquiv ℝ ψ)) : ℝ → ℂ)
      =ᵐ[volume] fun x => hamValue x (deriv (chartW ψ) x) (chartW ψ x) := by
  have h1 : (chartHam (conjEquiv chartUnitary (schwartzDomain ℝ) (schwartzEquiv ℝ ψ))
      : Lp ℂ 2 (volume : Measure ℝ))
      = chartUnitary ((chartMomentum ψ).toLp 2 (volume : Measure ℝ)) := by
    rw [chartHam]
    erw [conjOp_conjEquiv]
    rw [opL2_apply]
  have h2 := chartUnitary_apply ((chartMomentum ψ).toLp 2 (volume : Measure ℝ))
  have h3 : chartW ((chartMomentum ψ).toLp 2 (volume : Measure ℝ) : ℝ → ℂ)
      =ᵐ[volume] chartW (chartMomentum ψ) :=
    chartW_congr_ae (SchwartzMap.coeFn_toLp _ _ _)
  have hne : ∀ᵐ x ∂(volume : Measure ℝ), x ≠ 0 := by
    simp [ae_iff, measure_singleton]
  rw [h1]
  filter_upwards [h2, h3, hne] with x hx2 hx3 hx0
  rw [hx2, hx3, hamValue_chartW (ψ : ℝ → ℂ) hx0 (ψ.differentiableAt)]
  simp only [chartW, chartMomentum_apply]

open BookProof.ChapterStoneResolvent BookProof.StoneBridge BookProof.EsaClosure in
/-- **ODE-C.3.**  The chart realization of the quantized vector field generates a complete
unitary flow: its unique self-adjoint extension and Stone's group. -/
theorem chartHam_stone_flow :
    ∃ (T : UnboundedSelfAdjoint (Lp ℂ 2 (volume : Measure ℝ)))
      (U : ℝ → (Lp ℂ 2 (volume : Measure ℝ) →L[ℂ] Lp ℂ 2 (volume : Measure ℝ))),
      IsSelfAdjointExtension chartHam T.op ∧ IsStoneFlow T U :=
  exists_stone_flow_of_esa chartHam chartDomain_dense chartHam_symmetricOn
    chartHam_essentiallySelfAdjointOn

end Transfer

end

end BookProof.OdeChartTransfer
