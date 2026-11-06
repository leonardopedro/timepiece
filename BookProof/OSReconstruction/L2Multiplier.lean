import Mathlib
import BookProof.OSReconstruction.FockIntertwining
import BookProof.OSReconstruction.KallenLehmannModel

/-!
# Bounded multiplication on `L²(ν)` and the `e^{−τ f}` flow

`OSReconstruction.KallenLehmannModel` states the Källén–Lehmann representation in a multiplication
model, but takes the action of the transfer semigroup on `L²(ν)` as a hypothesis in representative
form: for each `τ` it asks for a representative `uh` of `U (P(τ) z)` and for the a.e. identity
`uh =ᵐ e^{−τ f} zh`.  That is a separate choice at every `τ`, so it cannot feed a statement about
*one* spectral measure, and it certainly cannot fill the `Q` slot of an `OsFockBridge`.

This module builds the operator instead:

* `mulL2` — multiplication by an essentially bounded real function is a **bounded** operator on
  `L²(ν)`.  This is Hölder's inequality with the exponent triple `(⊤, 2, 2)`
  (`ContinuousLinearMap.holderL`), and `mulL2_coeFn` records that it acts pointwise;
* `memLp_exp_neg_mul_top` — for `f ≥ 0` a.e. and `τ ≥ 0` the multiplier `e^{−τ f}` is bounded by
  one, hence an element of `L^∞`, hence an admissible multiplier;
* `expFlow` — the family `Q(τ)`, multiplication by `e^{−τ f}`, defined for *all* real `τ` (as the
  identity off `τ ≥ 0`, so that it can be the `Q` of a bridge).  `expFlow_of_nonneg` identifies it
  on `τ ≥ 0`, `expFlow_zero` and `expFlow_comp` prove the semigroup law on nonnegative times from
  `Real.exp_add`;
* `expFlow_contractive` / `norm_expFlow_le_one` — the flow is a contraction, `‖expFlow τ‖ ≤ 1`: the
  multiplier's essential supremum is at most one, so `mulL2_contractive` applies;
* `tendsto_expFlow_zero` — norm strong continuity of the flow at `0⁺`, from the difference quotient;
* `kl_physEvol_uniform` — **one** representative `zh` of `U z` and **one** spectral measure
  `z² dν ∘ f⁻¹` give the KL representation at every `τ ≥ 0` simultaneously, which is exactly the
  hypothesis `hkl` of `continuousOn_physEvol_twoPoint`;
* `osFockBridgeOfMulModel` — with a dense-range isometry `U` and the multiplier law for `P`, the
  bundle `OsFockBridge` is *instantiated*: its `Q` is the constructed `expFlow`, not a parameter;
* `inner_physEvol_eq_inner_expFlow` and `klMeasure_same_for_physEvol_and_expFlow` — the matrix
  elements of `P` *are* the matrix elements of the flow, and both are the Laplace transform of the
  single measure `klMeasure ν f zh`, so the KL measure is one measure for both sides;
* `expFlow_twoPoint_nonneg` — positivity of the flow's two-point function, read off that measure.

## Boundary

The multiplier law `U (P(τ) x) = expFlow τ (U x)` remains a hypothesis: it is the spectral theorem
for the generator, which this reconstruction does not have.  What changes is that the right-hand
side is now a concrete bounded operator on `L²(ν)` with the semigroup law proved, so the bundle's
axioms are discharged by construction and only the identification of `P` with that flow is open.

Agreement of the Laplace transforms for every `τ ≥ 0` is *not* used to conclude equality of the
measures: that would be injectivity of the Laplace transform on finite measures on `[0, ∞)`, which
this corpus does not have.  What is proved is the converse-facing statement that actually matters
here — the two sides are transforms of one and the same explicitly given measure.
-/

namespace BookProof.OSReconstruction

open Filter MeasureTheory
open scoped ENNReal RealInnerProductSpace Topology

noncomputable section

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-! ## Bounded multiplication on `L²(ν)` -/

/-- **Multiplication by an essentially bounded real function, as a bounded operator on `L²(ν)`.**

This is Hölder's inequality in the exponent form `(⊤, 2, 2)`: the `L^∞` factor is paired with the
`L²` factor and the product stays in `L²`. -/
def mulL2 (W : Lp ℝ (⊤ : ℝ≥0∞) ν) : Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  (ContinuousLinearMap.mul ℝ ℝ).holderL ν (⊤ : ℝ≥0∞) 2 2 W

/-- `mulL2` acts pointwise: the product class is the pointwise product of the representatives. -/
theorem mulL2_coeFn (W : Lp ℝ (⊤ : ℝ≥0∞) ν) (u : Lp ℝ 2 ν) :
    (mulL2 W u : X → ℝ) =ᵐ[ν] fun x => W x * u x :=
  ContinuousLinearMap.coeFn_holder _ _ _

/-! ## The multiplier `e^{−τ f}` -/

/-- For `f ≥ 0` a.e. and `τ ≥ 0` the multiplier `e^{−τ f}` is bounded by one, so it is an element
of `L^∞(ν)` and can be used in `mulL2`. -/
theorem memLp_exp_neg_mul_top {f : X → ℝ} (hf : Measurable f)
    (hpos : ∀ᵐ x ∂ν, 0 ≤ f x) {τ : ℝ} (hτ : 0 ≤ τ) :
    MemLp (fun x => Real.exp (-(τ * f x))) (⊤ : ℝ≥0∞) ν := by
  refine memLp_top_of_bound ?_ 1 ?_
  · exact (Real.measurable_exp.comp ((measurable_const.mul hf).neg)).aestronglyMeasurable
  · filter_upwards [hpos] with x hx
    rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), ← Real.exp_zero]
    exact Real.exp_le_exp.2 (by nlinarith)

/-- **The flow `Q(τ)`: multiplication by `e^{−τ f}`.**  It is defined for every real `τ` (as the
identity off `τ ≥ 0`) so that it can be the `Q` of an `OsFockBridge`; on `τ ≥ 0` it is the
contractive multiplier of `e^{−τ f}`. -/
def expFlow (f : X → ℝ) (hf : Measurable f) (hpos : ∀ᵐ x ∂ν, 0 ≤ f x) (τ : ℝ) :
    Lp ℝ 2 ν →L[ℝ] Lp ℝ 2 ν :=
  if h : 0 ≤ τ then mulL2 ((memLp_exp_neg_mul_top hf hpos h).toLp _) else 1

/-- On nonnegative times the flow is the multiplier by `e^{−τ f}`. -/
theorem expFlow_of_nonneg {f : X → ℝ} (hf : Measurable f)
    (hpos : ∀ᵐ x ∂ν, 0 ≤ f x) {τ : ℝ} (hτ : 0 ≤ τ) :
    expFlow f hf hpos τ = mulL2 ((memLp_exp_neg_mul_top hf hpos hτ).toLp _) := by
  rw [expFlow, dif_pos hτ]

/-- The flow acts pointwise by the multiplier `e^{−τ f}`. -/
theorem expFlow_coeFn {f : X → ℝ} (hf : Measurable f) (hpos : ∀ᵐ x ∂ν, 0 ≤ f x)
    {τ : ℝ} (hτ : 0 ≤ τ) (u : Lp ℝ 2 ν) :
    (expFlow f hf hpos τ u : X → ℝ) =ᵐ[ν] fun x => Real.exp (-(τ * f x)) * u x := by
  rw [expFlow_of_nonneg hf hpos hτ]
  refine (mulL2_coeFn _ u).trans ?_
  filter_upwards [MemLp.coeFn_toLp (memLp_exp_neg_mul_top hf hpos hτ)] with x hx
  rw [hx]

/-- At time zero the flow is the identity. -/
theorem expFlow_zero {f : X → ℝ} (hf : Measurable f) (hpos : ∀ᵐ x ∂ν, 0 ≤ f x) :
    expFlow f hf hpos 0 = 1 := by
  refine ContinuousLinearMap.ext fun u => Lp.ext ?_
  filter_upwards [expFlow_coeFn hf hpos le_rfl u] with x hx
  rw [hx]
  simp

/-- **The flow is a semigroup on nonnegative times**, read off `Real.exp_add` pointwise. -/
theorem expFlow_comp {f : X → ℝ} (hf : Measurable f) (hpos : ∀ᵐ x ∂ν, 0 ≤ f x)
    {τ σ : ℝ} (hτ : 0 ≤ τ) (hσ : 0 ≤ σ) (u : Lp ℝ 2 ν) :
    expFlow f hf hpos τ (expFlow f hf hpos σ u) = expFlow f hf hpos (τ + σ) u := by
  refine Lp.ext ?_
  filter_upwards [expFlow_coeFn hf hpos hτ (expFlow f hf hpos σ u),
    expFlow_coeFn hf hpos hσ u, expFlow_coeFn hf hpos (add_nonneg hτ hσ) u] with x h2 h3 h4
  rw [h2, h3, h4]
  have harg : -(τ * f x) + -(σ * f x) = -((τ + σ) * f x) := by ring
  rw [← mul_assoc, ← Real.exp_add, harg]

/-! ## The flow is a contraction -/

/-- A multiplier bounded by one in the essential supremum is a contraction on `L²(ν)`. -/
theorem mulL2_contractive (W : Lp ℝ (⊤ : ℝ≥0∞) ν) (hW : ∀ᵐ x ∂ν, ‖W x‖ ≤ 1)
    (u : Lp ℝ 2 ν) : ‖mulL2 W u‖ ≤ ‖u‖ := by
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [mulL2_coeFn W u, hW] with x hx h
  rw [hx, norm_mul]
  calc ‖W x‖ * ‖u x‖ ≤ 1 * ‖u x‖ := mul_le_mul_of_nonneg_right h (norm_nonneg _)
    _ = ‖u x‖ := one_mul _

/-- **The flow is contractive.**  For `f ≥ 0` a.e. and `τ ≥ 0` the multiplier `e^{−τ f}` is bounded
by one in the essential supremum, so `‖expFlow τ u‖ ≤ ‖u‖`. -/
theorem expFlow_contractive {f : X → ℝ} (hf : Measurable f) (hpos : ∀ᵐ x ∂ν, 0 ≤ f x)
    {τ : ℝ} (hτ : 0 ≤ τ) (u : Lp ℝ 2 ν) : ‖expFlow f hf hpos τ u‖ ≤ ‖u‖ := by
  rw [expFlow_of_nonneg hf hpos hτ]
  refine mulL2_contractive _ ?_ u
  filter_upwards [MemLp.coeFn_toLp (memLp_exp_neg_mul_top hf hpos hτ), hpos] with x hx hfx
  rw [hx, Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), ← Real.exp_zero]
  exact Real.exp_le_exp.2 (by nlinarith)

/-- The operator norm of the flow is at most one. -/
theorem norm_expFlow_le_one {f : X → ℝ} (hf : Measurable f) (hpos : ∀ᵐ x ∂ν, 0 ≤ f x)
    {τ : ℝ} (hτ : 0 ≤ τ) : ‖expFlow f hf hpos τ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun u => by
    calc ‖expFlow f hf hpos τ u‖ ≤ ‖u‖ := expFlow_contractive hf hpos hτ u
      _ = 1 * ‖u‖ := (one_mul _).symm

/-! ## The KL representation with one representative and one measure -/

/-- **Källén–Lehmann with a `τ`-independent representative.**  A single measurable representative
`zh` of `U z` and a single spectral measure `z² dν ∘ f⁻¹` give the KL representation of the
physical two-point function at *every* `τ ≥ 0`.  The hypothesis is the multiplier law for `P` in
representative form; everything else is constructed, in contrast to `kl_physEvol`, where a
representative `uh` had to be supplied separately for each `τ`. -/
theorem kl_physEvol_uniform (Λ : OSState) (T : TimeTranslation) (hinv : HinvRight Λ T)
    {f : X → ℝ} (hf : Measurable f) (hpos : ∀ᵐ x ∂ν, 0 ≤ f x)
    (U : Hphys Λ →ₗᵢ[ℝ] Lp ℝ 2 ν) (z : Hphys Λ)
    {zh : X → ℝ} (hzh : MemLp zh 2 ν) (hzhm : Measurable zh) (hUz : U z = hzh.toLp zh)
    (hUev : ∀ (τ : ℝ), 0 ≤ τ →
      U (physEvolCompletionRightFun hinv τ z) = expFlow f hf hpos τ (U z)) :
    ∀ (τ : ℝ), 0 ≤ τ →
      ⟪z, physEvolCompletionRightFun hinv τ z⟫
        = laplace ((ν.withDensity (fun x => ENNReal.ofReal ((zh x) * (zh x)))).map f) τ := by
  intro τ hτ
  rw [physEvolCompletionRightFun_of_nonneg hinv hτ]
  have hUev' : U (physEvolCompletionRight hinv τ hτ z) = expFlow f hf hpos τ (U z) := by
    rw [← physEvolCompletionRightFun_of_nonneg hinv hτ]
    exact hUev τ hτ
  have hinner : ⟪z, physEvolCompletionRight hinv τ hτ z⟫
      = ⟪hzh.toLp zh, expFlow f hf hpos τ (hzh.toLp zh)⟫ := by
    rw [← U.inner_map_map z (physEvolCompletionRight hinv τ hτ z), hUz, hUev', hUz]
  rw [hinner, L2.inner_def]
  have hone : (∫ x, inner ℝ ((hzh.toLp zh : X → ℝ) x)
        ((expFlow f hf hpos τ (hzh.toLp zh) : X → ℝ) x) ∂ν)
      = ∫ x, zh x * (Real.exp (-(τ * f x)) * zh x) ∂ν := by
    refine integral_congr_ae ?_
    filter_upwards [hzh.coeFn_toLp, expFlow_coeFn hf hpos hτ (hzh.toLp zh)] with x hx hy
    rw [hx, hy, hx, RCLike.inner_apply', RCLike.conj_to_real]
  rw [hone, integral_mul_exp_eq_laplace hzhm hf τ]

/-! ## Instantiating the OS-to-Fock bridge -/

/-- **The multiplier model instantiates `OsFockBridge`.**  With a dense-range isometry
`U : ℋ →ₗᵢ L²(ν)` intertwining the transfer semigroup with the *constructed* multiplier flow, the
bundle's three fields are all available: `U`, its density, and the intertwining.  The `Q` of the
resulting bridge is `expFlow`, whose semigroup law on nonnegative times is proved
(`expFlow_comp`), so `OsFockBridge.semigroup_transfer` applies without further hypotheses. -/
def osFockBridgeOfMulModel (Λ : OSState) {f : X → ℝ} (hf : Measurable f)
    (hpos : ∀ᵐ x ∂ν, 0 ≤ f x) (P : ℝ → Hphys Λ →L[ℝ] Hphys Λ)
    (U : Hphys Λ →ₗᵢ[ℝ] Lp ℝ 2 ν) (hdense : DenseRange U)
    (hU : ∀ (τ : ℝ), 0 ≤ τ → ∀ x : Hphys Λ, U (P τ x) = expFlow f hf hpos τ (U x)) :
    OsFockBridge (Lp ℝ 2 ν) P (expFlow f hf hpos) where
  U := U
  dense_range := hdense
  intertwines := hU

/-! ## The difference quotient at `0⁺`

At `τ = 0⁺` the slope of the flow is multiplication by `−f`: the generator of `Q` is `−M_f`, at
least as a limit in `L²(ν)`.  Everything here is elementary — the pointwise slope of
`t ↦ e^{−t c}` is bounded by `c`, so the whole family is dominated by `2 f |z|`, and dominated
convergence applies to the square. -/

/-- **First-order bound on the kernel's slope**: for `c ≥ 0` and `τ > 0` the slope at `0` of
`t ↦ e^{−t c}` is bounded by `c`. -/
theorem abs_exp_neg_mul_sub_one_div_le {c τ : ℝ} (hc : 0 ≤ c) (hτ : 0 < τ) :
    |(Real.exp (-(τ * c)) - 1) / τ| ≤ c := by
  have hle1 : Real.exp (-(τ * c)) ≤ 1 := by
    rw [← Real.exp_zero]
    exact Real.exp_le_exp.2 (by nlinarith)
  have habs : |Real.exp (-(τ * c)) - 1| = 1 - Real.exp (-(τ * c)) := by
    rw [abs_of_nonpos (by linarith), neg_sub]
  have hbound : 1 - Real.exp (-(τ * c)) ≤ τ * c := by
    have h := Real.add_one_le_exp (-(τ * c))
    linarith
  rw [abs_div, abs_of_pos hτ, habs, div_le_iff₀ hτ]
  linarith

/-- **The slope of `t ↦ e^{−t c}` at `0⁺` tends to `−c`**, from differentiability of `Real.exp`. -/
theorem tendsto_exp_neg_mul_sub_one_div {c : ℝ} :
    Tendsto (fun τ : ℝ => (Real.exp (-(τ * c)) - 1) / τ) (𝓝[>] 0) (𝓝 (-c)) := by
  have hd : HasDerivAt (fun u : ℝ => Real.exp (-(u * c))) (-c) 0 := by
    have h1 : HasDerivAt (fun u : ℝ => u * c) c 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).mul_const c
    simpa using (h1.neg).exp
  refine (hasDerivAt_iff_tendsto_slope_left_right.mp hd).2.congr' ?_
  filter_upwards with y
  have h0 : Real.exp (-(0 * c)) = 1 := by simp
  simp only [slope_fun_def_field, sub_zero, div_eq_inv_mul, h0]

/-- **The `L²` difference quotient of the multiplier flow at `0⁺`.**  For `z ∈ L²(ν)` and
`f z ∈ L²(ν)`, the slope of `Q(τ) z` at `τ = 0⁺` converges in `L²(ν)` to `−f z`. -/
theorem tendsto_expFlow_slope {z : X → ℝ} (hz : MemLp z 2 ν) {f : X → ℝ} (hf : Measurable f)
    (hpos : ∀ᵐ x ∂ν, 0 ≤ f x) (hfz : MemLp (fun x => f x * z x) 2 ν) :
    Tendsto (fun τ : ℝ => τ⁻¹ • (expFlow f hf hpos τ (hz.toLp z) - hz.toLp z))
      (𝓝[>] 0) (𝓝 (-(hfz.toLp (fun x => f x * z x)))) := by
  set κ : ℝ → X → ℝ := fun τ x => τ⁻¹ * ((Real.exp (-(τ * f x)) - 1) * z x) + f x * z x
  have hκeq : ∀ (τ : ℝ) (x : X),
      κ τ x = ((Real.exp (-(τ * f x)) - 1) / τ) * z x + f x * z x := by
    intro τ x
    simp only [κ]
    rw [div_eq_inv_mul]
    ring
  have hae : ∀ τ : ℝ, 0 < τ →
      ((τ⁻¹ • (expFlow f hf hpos τ (hz.toLp z) - hz.toLp z)
          + hfz.toLp (fun x => f x * z x) : Lp ℝ 2 ν) : X → ℝ) =ᵐ[ν] κ τ := by
    intro τ hτ
    filter_upwards [Lp.coeFn_add (τ⁻¹ • (expFlow f hf hpos τ (hz.toLp z) - hz.toLp z))
        (hfz.toLp (fun x => f x * z x)),
      Lp.coeFn_smul τ⁻¹ (expFlow f hf hpos τ (hz.toLp z) - hz.toLp z),
      Lp.coeFn_sub (expFlow f hf hpos τ (hz.toLp z)) (hz.toLp z),
      expFlow_coeFn hf hpos hτ.le (hz.toLp z), hz.coeFn_toLp, hfz.coeFn_toLp]
      with x h1 h2 h3 h4 h5 h6
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul, h3, Pi.sub_apply, h4, h5, h6]
    simp only [κ]
    ring
  have hnorm : ∀ τ : ℝ, 0 < τ →
      ‖τ⁻¹ • (expFlow f hf hpos τ (hz.toLp z) - hz.toLp z)
          + hfz.toLp (fun x => f x * z x)‖ ^ 2 = ∫ x, κ τ x * κ τ x ∂ν := by
    intro τ hτ
    rw [← real_inner_self_eq_norm_sq, L2.inner_def]
    refine integral_congr_ae ?_
    filter_upwards [hae τ hτ] with x hx
    rw [hx, RCLike.inner_apply', RCLike.conj_to_real]
  have hDCT : Tendsto (fun τ : ℝ => ∫ x, κ τ x * κ τ x ∂ν) (𝓝[>] 0) (𝓝 0) := by
    have hmeas : ∀ᶠ τ in 𝓝[>] (0 : ℝ), AEStronglyMeasurable (fun x => κ τ x * κ τ x) ν :=
      Eventually.of_forall fun τ => by
        have hexp : AEStronglyMeasurable (fun x => Real.exp (-(τ * f x))) ν :=
          (Real.measurable_exp.comp ((measurable_const.mul hf).neg)).aestronglyMeasurable
        have hκ : AEStronglyMeasurable (fun x => κ τ x) ν := by
          simp only [κ]
          exact (aestronglyMeasurable_const.mul
            ((hexp.sub aestronglyMeasurable_const).mul hz.aestronglyMeasurable)).add
              (hf.aestronglyMeasurable.mul hz.aestronglyMeasurable)
        exact hκ.mul hκ
    have hbound : ∀ᶠ τ in 𝓝[>] (0 : ℝ),
        ∀ᵐ x ∂ν, ‖κ τ x * κ τ x‖ ≤ 4 * (f x * z x) ^ 2 := by
      filter_upwards [self_mem_nhdsWithin] with τ hτ
      filter_upwards [hpos] with x hx
      have hslope : |(Real.exp (-(τ * f x)) - 1) / τ| ≤ f x :=
        abs_exp_neg_mul_sub_one_div_le hx hτ
      have hle : |κ τ x| ≤ 2 * |f x * z x| := by
        rw [hκeq]
        calc |((Real.exp (-(τ * f x)) - 1) / τ) * z x + f x * z x|
            ≤ |((Real.exp (-(τ * f x)) - 1) / τ) * z x| + |f x * z x| := abs_add_le _ _
          _ = |(Real.exp (-(τ * f x)) - 1) / τ| * |z x| + |f x * z x| := by rw [abs_mul]
          _ ≤ f x * |z x| + |f x * z x| :=
              add_le_add (mul_le_mul_of_nonneg_right hslope (abs_nonneg _)) le_rfl
          _ = 2 * |f x * z x| := by rw [abs_mul, abs_of_nonneg hx]; ring
      rw [norm_mul]
      calc ‖κ τ x‖ * ‖κ τ x‖ = |κ τ x| * |κ τ x| := by rw [Real.norm_eq_abs]
        _ ≤ (2 * |f x * z x|) * (2 * |f x * z x|) :=
            mul_le_mul hle hle (abs_nonneg _) (by positivity)
        _ = 4 * (f x * z x) ^ 2 := by rw [← sq_abs]; ring
    have hint : Integrable (fun x => 4 * (f x * z x) ^ 2) ν :=
      (MemLp.integrable_sq hfz).const_mul 4
    have hlim : ∀ᵐ x ∂ν, Tendsto (fun τ : ℝ => κ τ x * κ τ x) (𝓝[>] 0) (𝓝 0) := by
      filter_upwards with x
      have hκlim : Tendsto (fun τ : ℝ => κ τ x) (𝓝[>] 0) (𝓝 0) := by
        have h1 := (tendsto_exp_neg_mul_sub_one_div (c := f x)).mul_const (z x)
        have h2 : Tendsto (fun τ : ℝ => ((Real.exp (-(τ * f x)) - 1) / τ) * z x + f x * z x)
            (𝓝[>] 0) (𝓝 (-(f x) * z x + f x * z x)) := h1.add_const (f x * z x)
        have h0 : -(f x) * z x + f x * z x = 0 := by ring
        rw [h0] at h2
        refine h2.congr' ?_
        filter_upwards with τ
        exact (hκeq τ x).symm
      simpa using hκlim.mul hκlim
    have := tendsto_integral_filter_of_dominated_convergence (μ := ν)
      (fun x => 4 * (f x * z x) ^ 2) hmeas hbound hint hlim
    simpa using this
  have hnorm_tendsto : Tendsto (fun τ : ℝ =>
      ‖τ⁻¹ • (expFlow f hf hpos τ (hz.toLp z) - hz.toLp z)
        + hfz.toLp (fun x => f x * z x)‖) (𝓝[>] 0) (𝓝 0) := by
    have hsq : Tendsto (fun τ : ℝ =>
        ‖τ⁻¹ • (expFlow f hf hpos τ (hz.toLp z) - hz.toLp z)
          + hfz.toLp (fun x => f x * z x)‖ ^ 2) (𝓝[>] 0) (𝓝 0) := by
      refine hDCT.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with τ hτ
      exact (hnorm τ hτ).symm
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    have h := (Metric.tendsto_nhds.1 hsq) (ε ^ 2) (by positivity)
    filter_upwards [h] with τ hτ
    have hτ' : ‖τ⁻¹ • (expFlow f hf hpos τ (hz.toLp z) - hz.toLp z)
        + hfz.toLp (fun x => f x * z x)‖ ^ 2 < ε ^ 2 := by
      simpa [Real.dist_eq, sub_zero] using hτ
    rw [Real.dist_eq, sub_zero]
    have ha : (0 : ℝ) ≤ ‖τ⁻¹ • (expFlow f hf hpos τ (hz.toLp z) - hz.toLp z)
        + hfz.toLp (fun x => f x * z x)‖ := norm_nonneg _
    rw [abs_of_nonneg ha]
    nlinarith
  have hw : Tendsto (fun τ : ℝ => τ⁻¹ • (expFlow f hf hpos τ (hz.toLp z) - hz.toLp z)
      + hfz.toLp (fun x => f x * z x)) (𝓝[>] 0) (𝓝 0) := by
    refine Metric.tendsto_nhds.2 fun ε hε => ?_
    have h := (Metric.tendsto_nhds.1 hnorm_tendsto) ε hε
    filter_upwards [h] with τ hτ
    simpa [Real.dist_eq, sub_zero] using hτ
  have hfinal := hw.sub_const (hfz.toLp (fun x => f x * z x))
  simpa [add_sub_cancel_right] using hfinal

/-- **Norm strong continuity of the flow at `0⁺`**, from the difference quotient: there
`expFlow τ u = u + τ • (τ⁻¹ • (expFlow τ u − u))`, and the second summand is `τ` times a
convergent quantity. -/
theorem tendsto_expFlow_zero {z : X → ℝ} (hz : MemLp z 2 ν) {f : X → ℝ} (hf : Measurable f)
    (hpos : ∀ᵐ x ∂ν, 0 ≤ f x) (hfz : MemLp (fun x => f x * z x) 2 ν) :
    Tendsto (fun τ : ℝ => expFlow f hf hpos τ (hz.toLp z)) (𝓝[>] 0) (𝓝 (hz.toLp z)) := by
  have hslope := tendsto_expFlow_slope hz hf hpos hfz
  have hEq : (fun τ : ℝ => expFlow f hf hpos τ (hz.toLp z)) =ᶠ[𝓝[>] (0 : ℝ)]
      fun τ => hz.toLp z + τ • (τ⁻¹ • (expFlow f hf hpos τ (hz.toLp z) - hz.toLp z)) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    rw [smul_smul, mul_inv_cancel₀ (ne_of_gt hτ), one_smul]
    abel
  have hid : Tendsto (fun τ : ℝ => τ) (𝓝[>] 0) (𝓝 0) :=
    tendsto_id.mono_left nhdsWithin_le_nhds
  have hsmul : Tendsto (fun τ : ℝ =>
      τ • (τ⁻¹ • (expFlow f hf hpos τ (hz.toLp z) - hz.toLp z))) (𝓝[>] 0) (𝓝 0) := by
    have h := hid.smul hslope
    simpa using h
  have hsum : Tendsto (fun τ : ℝ => hz.toLp z
      + τ • (τ⁻¹ • (expFlow f hf hpos τ (hz.toLp z) - hz.toLp z))) (𝓝[>] 0)
      (𝓝 (hz.toLp z)) := by
    have hc : Tendsto (fun _ : ℝ => hz.toLp z) (𝓝[>] 0) (𝓝 (hz.toLp z)) := tendsto_const_nhds
    simpa using hc.add hsmul
  exact hsum.congr' hEq.symm

/-! ## The matrix elements of `P` are the matrix elements of the flow

Everything so far is a statement about the constructed flow.  This section connects it back to the
transfer semigroup: under the multiplier law, the matrix elements of `P` *are* the `L²(ν)` matrix
elements of `expFlow`, and both are the Laplace transform of one and the same measure
`klMeasure ν f zh`, fixed by the representative of `U z` alone. -/

/-- **The KL spectral measure of the multiplier model**: the push-forward of `zh² dν` along `f`.
It depends only on the multiplier `f` and on the representative `zh` of `U z`. -/
def klMeasure (ν : Measure X) (f : X → ℝ) (zh : X → ℝ) : Measure ℝ :=
  (ν.withDensity (fun x => ENNReal.ofReal ((zh x) * (zh x)))).map f

/-- **Matrix elements of the transfer semigroup are matrix elements of the flow.**  For `τ ≥ 0`,
`⟪x, P(τ)y⟫` equals the `L²(ν)` matrix element of `expFlow` between `U x` and `U y`.  Only the
isometry `U` and the multiplier law are used — no KL input. -/
theorem inner_physEvol_eq_inner_expFlow (Λ : OSState) (T : TimeTranslation)
    (hinv : HinvRight Λ T) {f : X → ℝ} (hf : Measurable f) (hpos : ∀ᵐ x ∂ν, 0 ≤ f x)
    (U : Hphys Λ →ₗᵢ[ℝ] Lp ℝ 2 ν)
    (hU : ∀ (τ : ℝ), 0 ≤ τ → ∀ x : Hphys Λ,
      U (physEvolCompletionRightFun hinv τ x) = expFlow f hf hpos τ (U x))
    {τ : ℝ} (hτ : 0 ≤ τ) (x y : Hphys Λ) :
    ⟪x, physEvolCompletionRightFun hinv τ y⟫ = ⟪U x, expFlow f hf hpos τ (U y)⟫ := by
  rw [← U.inner_map_map x (physEvolCompletionRightFun hinv τ y), hU τ hτ y]

/-- **The two-point function of `P` is the two-point function of the flow.** -/
theorem twoPoint_physEvol_eq_expFlow (Λ : OSState) (T : TimeTranslation) (hinv : HinvRight Λ T)
    {f : X → ℝ} (hf : Measurable f) (hpos : ∀ᵐ x ∂ν, 0 ≤ f x)
    (U : Hphys Λ →ₗᵢ[ℝ] Lp ℝ 2 ν)
    (hU : ∀ (τ : ℝ), 0 ≤ τ → ∀ x : Hphys Λ,
      U (physEvolCompletionRightFun hinv τ x) = expFlow f hf hpos τ (U x))
    {τ : ℝ} (hτ : 0 ≤ τ) (z : Hphys Λ) :
    ⟪z, physEvolCompletionRightFun hinv τ z⟫ = ⟪U z, expFlow f hf hpos τ (U z)⟫ :=
  inner_physEvol_eq_inner_expFlow Λ T hinv hf hpos U hU hτ z z

/-- **The `L²` matrix element of the flow**, as an integral of representatives. -/
theorem inner_expFlow_eq_integral {z u : X → ℝ} (hz : MemLp z 2 ν) (hu : MemLp u 2 ν)
    {f : X → ℝ} (hf : Measurable f) (hpos : ∀ᵐ x ∂ν, 0 ≤ f x) {τ : ℝ} (hτ : 0 ≤ τ) :
    ⟪hz.toLp z, expFlow f hf hpos τ (hu.toLp u)⟫
      = ∫ x, z x * (Real.exp (-(τ * f x)) * u x) ∂ν := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hz.coeFn_toLp, hu.coeFn_toLp,
    expFlow_coeFn hf hpos hτ (hu.toLp u)] with x h1 h2 h3
  rw [h1, h3, h2, RCLike.inner_apply', RCLike.conj_to_real]

/-- **The KL measure is the same one for `P` and for the flow.**  Both matrix elements of a vector
`z` are the Laplace transform of the single measure `klMeasure ν f zh`, fixed by a representative
`zh` of `U z`.  So a mass gap, a support condition or nonnegativity read off the KL measure is a
statement about the transfer semigroup and about the multiplier flow at once. -/
theorem klMeasure_same_for_physEvol_and_expFlow (Λ : OSState) (T : TimeTranslation)
    (hinv : HinvRight Λ T) {f : X → ℝ} (hf : Measurable f) (hpos : ∀ᵐ x ∂ν, 0 ≤ f x)
    (U : Hphys Λ →ₗᵢ[ℝ] Lp ℝ 2 ν) (z : Hphys Λ)
    {zh : X → ℝ} (hzh : MemLp zh 2 ν) (hzhm : Measurable zh) (hUz : U z = hzh.toLp zh)
    (hU : ∀ (τ : ℝ), 0 ≤ τ → ∀ x : Hphys Λ,
      U (physEvolCompletionRightFun hinv τ x) = expFlow f hf hpos τ (U x)) :
    (∀ (τ : ℝ), 0 ≤ τ →
        ⟪z, physEvolCompletionRightFun hinv τ z⟫ = laplace (klMeasure ν f zh) τ) ∧
      (∀ (τ : ℝ), 0 ≤ τ →
        ⟪U z, expFlow f hf hpos τ (U z)⟫ = laplace (klMeasure ν f zh) τ) := by
  constructor
  · intro τ hτ
    have h := kl_physEvol_uniform Λ T hinv hf hpos U z hzh hzhm hUz
      (fun σ hσ => by rw [hU σ hσ z, hUz]) τ hτ
    simpa only [klMeasure] using h
  · intro τ hτ
    have h1 : ⟪U z, expFlow f hf hpos τ (U z)⟫
        = ⟪hzh.toLp zh, expFlow f hf hpos τ (hzh.toLp zh)⟫ := by rw [hUz]
    rw [h1, inner_expFlow_eq_integral hzh hzh hf hpos hτ]
    have h2 := integral_mul_exp_eq_laplace (ν := ν) hzhm hf τ
    simpa only [klMeasure] using h2

/-- **Positivity of the flow's two-point function**, from the KL measure shared with `P`. -/
theorem expFlow_twoPoint_nonneg (Λ : OSState) (T : TimeTranslation) (hinv : HinvRight Λ T)
    {f : X → ℝ} (hf : Measurable f) (hpos : ∀ᵐ x ∂ν, 0 ≤ f x)
    (U : Hphys Λ →ₗᵢ[ℝ] Lp ℝ 2 ν) (z : Hphys Λ)
    {zh : X → ℝ} (hzh : MemLp zh 2 ν) (hzhm : Measurable zh) (hUz : U z = hzh.toLp zh)
    (hU : ∀ (τ : ℝ), 0 ≤ τ → ∀ x : Hphys Λ,
      U (physEvolCompletionRightFun hinv τ x) = expFlow f hf hpos τ (U x))
    {τ : ℝ} (hτ : 0 ≤ τ) :
    0 ≤ ⟪U z, expFlow f hf hpos τ (U z)⟫ := by
  rw [(klMeasure_same_for_physEvol_and_expFlow Λ T hinv hf hpos U z hzh hzhm hUz hU).2 τ hτ]
  exact laplace_nonneg _ τ

end

end BookProof.OSReconstruction
