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
* `klMeasure_univ_lt_top`, `isFiniteMeasure_klMeasure`, `klMeasure_support` — the KL measure is
  finite and supported on `[0, ∞)` under `f ≥ 0`, so the decay lemmas of `Clustering` apply to it;
* `laplace_le_mass`, `twoPoint_le_klMass`, `klMeasure_mass_eq_norm_sq` — the transform and the
  transfer two-point function are bounded by the mass of the KL measure, which is `‖z‖²`;
* `abs_twoPoint_le_norm_sq` — the norm bound `|⟪z, P(τ)z⟫| ≤ ‖z‖²`, from the contraction bound;
* `tendsto_physEvol_of_representative`, `tendsto_physEvol` — **strong continuity of `P` itself** at
  every `σ ≥ 0`: the multiplier law carries it to the flow, and the isometry `U` brings the `L²`
  convergence back to `ℋ`; the version for all vectors assumes `f` essentially bounded;
* `klMeasure_apply`, `weight_univ_lt_top`, `klMeasure_finite` — the push-forward description, the
  finiteness of the weight `z² dν`, and the bundle of finiteness and support of the KL measure;
* `support_klMeasure`, `support_klMeasure_subset_closure_range`,
  `support_klMeasure_eq_closure_range` — the support of the KL measure is the essential range of
  `f` for the weight `z² dν`;
* `support_klMeasure_subset_Ici_zero`, `klMeasure_Iio_of_support_subset` — the support lies in
  `[0, ∞)`, and the exponential tail bound holds for every `m` at or below it, so the sharpest
  case `m = sInf (support)` is available;
* `klMeasure_pos_of_pos`, `klMeasure_pos_of_isOpen_meets_range`,
  `support_klMeasure_eq_closure_range_of_measure`, `sInf_support_klMeasure_eq` — the essential-range
  hypothesis is derived from properties of `ν` (`z ≠ 0` a.e. and positive `ν`-mass on the relevant
  preimages), and the sharp exponent is `sInf (closure (range f))`;
* `laplace_antitoneOn`, `twoPoint_antitoneOn` — the transform, hence the physical two-point
  function, is antitone on `[0, ∞)`;
* `tendsto_physEvol_slope`, `tendsto_inner_slope_twoPoint` — the right difference quotient of `P` at
  `0⁺` is `−M_f`: `τ⁻¹ • (P(τ)y − y) → −M` whenever `U M = M_f(U y)`, in norm and in matrix
  elements (so `τ ↦ ⟪x, P(τ)y⟫` has right derivative `−⟪x, M⟫` at `0`);
* `twoPoint_le_norm_sq_mul_exp` — the exponential tail bound `⟪z, P(τ)z⟫ ≤ ‖z‖² e^{−mτ}` when the
  KL measure has no mass below `m`;
* `klMeasure_absolutelyContinuous` — `klMeasure ν f z ≪ ν.map f`;
* `convexOn_laplace`, `twoPoint_convexOn` — the transform, hence the physical two-point function,
  is convex on `[0, ∞)`;
* `hasDerivWithinAt_twoPoint` — the derivative form of the generator statement:
  `τ ↦ ⟪x, P(τ)y⟫` has right derivative `−⟪x, M⟫` at `0`;
* `tendsto_expFlow_at` — norm strong continuity at every `τ ≥ 0`, from the semigroup law;
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

/-! ## The KL measure: finiteness and support

The KL measure is `zh² dν` pushed forward by `f`, so it is finite because `zh ∈ L²(ν)`, and it is
supported on `[0, ∞)` because `f ≥ 0` `ν`-almost everywhere (and `zh² dν` is absolutely continuous
with respect to `ν`).  Both facts are what the decay lemmas of `Clustering` need. -/

/-- The total mass of the KL measure, as a single integral. -/
theorem klMeasure_univ {z : X → ℝ} (hz : MemLp z 2 ν) {f : X → ℝ} (hf : Measurable f) :
    klMeasure ν f z Set.univ = ENNReal.ofReal (∫ x, (z x) ^ 2 ∂ν) := by
  rw [klMeasure, Measure.map_apply hf MeasurableSet.univ, Set.preimage_univ,
    withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hcongr : (∫⁻ x, ENNReal.ofReal (z x * z x) ∂ν)
      = ∫⁻ x, ENNReal.ofReal ((z x) ^ 2) ∂ν :=
    lintegral_congr fun x => by rw [pow_two]
  rw [hcongr]
  exact (ofReal_integral_eq_lintegral_ofReal (MemLp.integrable_sq hz)
    (Eventually.of_forall fun x => sq_nonneg (z x))).symm

/-- **The KL measure is finite**, since `zh ∈ L²(ν)`. -/
theorem klMeasure_univ_lt_top {z : X → ℝ} (hz : MemLp z 2 ν) {f : X → ℝ}
    (hf : Measurable f) : klMeasure ν f z Set.univ < ⊤ := by
  rw [klMeasure_univ hz hf]
  exact ENNReal.ofReal_lt_top

/-- The KL measure is a finite measure. -/
theorem isFiniteMeasure_klMeasure {z : X → ℝ} (hz : MemLp z 2 ν) {f : X → ℝ}
    (hf : Measurable f) : IsFiniteMeasure (klMeasure ν f z) :=
  ⟨klMeasure_univ_lt_top hz hf⟩

/-- **The KL measure is supported on `[0, ∞)`** when `f ≥ 0` a.e.: the preimage of `(-∞, 0)` is
`ν`-null, and the density is absolutely continuous. -/
theorem klMeasure_support {z : X → ℝ} {f : X → ℝ} (hf : Measurable f)
    (hpos : ∀ᵐ x ∂ν, 0 ≤ f x) : klMeasure ν f z (Set.Iio 0) = 0 := by
  rw [klMeasure, Measure.map_apply hf measurableSet_Iio,
    withDensity_apply _ (hf measurableSet_Iio)]
  have hnull : ν (f ⁻¹' Set.Iio 0) = 0 := by
    have hset : f ⁻¹' Set.Iio 0 = {x : X | ¬ 0 ≤ f x} := by
      ext x
      simp only [Set.mem_preimage, Set.mem_Iio, Set.mem_setOf_eq, not_le]
    rw [hset]
    exact ae_iff.mp hpos
  rw [show (∫⁻ x in f ⁻¹' Set.Iio 0, ENNReal.ofReal (z x * z x) ∂ν)
      = ∫⁻ x, ENNReal.ofReal (z x * z x) ∂(ν.restrict (f ⁻¹' Set.Iio 0)) from rfl,
    Measure.restrict_eq_zero.2 hnull]
  simp

/-- The exponential kernel is integrable against a finite measure supported on `[0, ∞)`. -/
theorem laplace_integrable_of_support {ρ : Measure ℝ} [IsFiniteMeasure ρ] {τ : ℝ} (hτ : 0 ≤ τ)
    (hsupp : ρ (Set.Iio 0) = 0) : Integrable (fun l : ℝ => Real.exp (-(τ * l))) ρ := by
  refine Integrable.of_bound
    (Real.measurable_exp.comp ((measurable_const.mul measurable_id).neg)).aestronglyMeasurable 1 ?_
  have hset : {l : ℝ | ¬ 0 ≤ l} = Set.Iio 0 := by
    ext l
    simp only [Set.mem_setOf_eq, Set.mem_Iio, not_le]
  have hae : ∀ᵐ l ∂ρ, 0 ≤ l := by
    refine ae_iff.2 ?_
    rw [hset]
    exact hsupp
  filter_upwards [hae] with l hl
  rw [Real.norm_eq_abs, abs_of_nonneg (Real.exp_nonneg _), ← Real.exp_zero]
  exact Real.exp_le_exp.2 (by nlinarith)

/-- **The transform is bounded by the total mass**, for a finite measure supported on `[0, ∞)`:
the specialization of `laplace_le_of_massGap` to zero gap. -/
theorem laplace_le_mass {ρ : Measure ℝ} [IsFiniteMeasure ρ] {τ : ℝ} (hτ : 0 ≤ τ)
    (hsupp : ρ (Set.Iio 0) = 0) : laplace ρ τ ≤ (ρ Set.univ).toReal := by
  have h := laplace_le_of_massGap (ρ := ρ) (m := 0) hτ
    (laplace_integrable_of_support hτ hsupp) hsupp
  simpa using h

/-- **The KL mass is the square of the norm**: `(z² dν ∘ f⁻¹)(ℝ) = ‖z‖²`, by the isometry `U`.
So the mass of the shared KL measure is exactly `‖z‖²`, and the bounds below are sharp at
`τ = 0`. -/
theorem klMeasure_mass_eq_norm_sq (Λ : OSState) {f : X → ℝ} (hf : Measurable f)
    (U : Hphys Λ →ₗᵢ[ℝ] Lp ℝ 2 ν) (z : Hphys Λ) {zh : X → ℝ} (hzh : MemLp zh 2 ν)
    (hUz : U z = hzh.toLp zh) : (klMeasure ν f zh Set.univ).toReal = ‖z‖ ^ 2 := by
  have hnn : 0 ≤ ∫ x, (zh x) ^ 2 ∂ν := integral_nonneg fun x => sq_nonneg (zh x)
  rw [klMeasure_univ hzh hf, ENNReal.toReal_ofReal hnn]
  simp only [pow_two]
  have h1 : ⟪hzh.toLp zh, hzh.toLp zh⟫ = ∫ x, zh x * zh x ∂ν := inner_toLp_eq_integral hzh hzh
  rw [← h1, real_inner_self_eq_norm_sq, ← hUz, U.norm_map, sq]

/-- **Norm bound on the two-point function of the transfer semigroup.**  Through the matrix-element
identity and the contraction bound on the flow, `|⟪z, P(τ)z⟫| ≤ ‖z‖²` for `τ ≥ 0`. -/
theorem abs_twoPoint_le_norm_sq (Λ : OSState) (T : TimeTranslation) (hinv : HinvRight Λ T)
    {f : X → ℝ} (hf : Measurable f) (hpos : ∀ᵐ x ∂ν, 0 ≤ f x)
    (U : Hphys Λ →ₗᵢ[ℝ] Lp ℝ 2 ν)
    (hU : ∀ (τ : ℝ), 0 ≤ τ → ∀ x : Hphys Λ,
      U (physEvolCompletionRightFun hinv τ x) = expFlow f hf hpos τ (U x))
    {τ : ℝ} (hτ : 0 ≤ τ) (z : Hphys Λ) :
    |⟪z, physEvolCompletionRightFun hinv τ z⟫| ≤ ‖z‖ ^ 2 := by
  rw [twoPoint_physEvol_eq_expFlow Λ T hinv hf hpos U hU hτ z]
  calc |⟪U z, expFlow f hf hpos τ (U z)⟫|
      ≤ ‖U z‖ * ‖expFlow f hf hpos τ (U z)‖ := abs_real_inner_le_norm _ _
    _ ≤ ‖U z‖ * ‖U z‖ :=
        mul_le_mul_of_nonneg_left (expFlow_contractive hf hpos hτ (U z)) (norm_nonneg _)
    _ = ‖z‖ ^ 2 := by rw [← sq, U.norm_map]

/-- **The two-point function is bounded by the mass of the shared KL measure.** -/
theorem twoPoint_le_klMass (Λ : OSState) (T : TimeTranslation) (hinv : HinvRight Λ T)
    {f : X → ℝ} (hf : Measurable f) (hpos : ∀ᵐ x ∂ν, 0 ≤ f x)
    (U : Hphys Λ →ₗᵢ[ℝ] Lp ℝ 2 ν) (z : Hphys Λ)
    {zh : X → ℝ} (hzh : MemLp zh 2 ν) (hzhm : Measurable zh) (hUz : U z = hzh.toLp zh)
    (hU : ∀ (τ : ℝ), 0 ≤ τ → ∀ x : Hphys Λ,
      U (physEvolCompletionRightFun hinv τ x) = expFlow f hf hpos τ (U x))
    {τ : ℝ} (hτ : 0 ≤ τ) :
    ⟪z, physEvolCompletionRightFun hinv τ z⟫ ≤ (klMeasure ν f zh Set.univ).toReal := by
  haveI : IsFiniteMeasure (klMeasure ν f zh) := isFiniteMeasure_klMeasure hzh hf
  rw [(klMeasure_same_for_physEvol_and_expFlow Λ T hinv hf hpos U z hzh hzhm hUz hU).1 τ hτ]
  exact laplace_le_mass hτ (klMeasure_support hf hpos)

/-! ## Strong continuity at every nonnegative time -/

/-- `e^{−τ f} z` stays in `L²(ν)` for `τ ≥ 0`; unlike `memLp_exp_mul`, no measurability assumption
on `z` is needed. -/
theorem memLp_exp_mul_ae {z : X → ℝ} (hz : MemLp z 2 ν) {f : X → ℝ} (hf : Measurable f)
    (hpos : ∀ᵐ x ∂ν, 0 ≤ f x) {τ : ℝ} (hτ : 0 ≤ τ) :
    MemLp (fun x => Real.exp (-(τ * f x)) * z x) 2 ν := by
  refine MemLp.of_le hz ?_ ?_
  · exact ((Real.measurable_exp.comp ((measurable_const.mul hf).neg)).aestronglyMeasurable).mul
      hz.aestronglyMeasurable
  · filter_upwards [hpos] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_of_nonneg (Real.exp_nonneg _)]
    have hle : Real.exp (-(τ * f x)) ≤ 1 := by
      rw [← Real.exp_zero]
      exact Real.exp_le_exp.2 (by nlinarith)
    calc Real.exp (-(τ * f x)) * |z x| ≤ 1 * |z x| :=
          mul_le_mul_of_nonneg_right hle (abs_nonneg _)
      _ = |z x| := one_mul _

/-- **Norm strong continuity at every nonnegative time.**  Writing `τ = σ + (τ − σ)` and using the
semigroup law, continuity at `σ` reduces to continuity of the flow at `0⁺` applied to the vector
`expFlow σ u`, whose representative is `e^{−σ f} z`. -/
theorem tendsto_expFlow_at {z : X → ℝ} (hz : MemLp z 2 ν) {f : X → ℝ} (hf : Measurable f)
    (hpos : ∀ᵐ x ∂ν, 0 ≤ f x) (hfz : MemLp (fun x => f x * z x) 2 ν)
    {σ : ℝ} (hσ : 0 ≤ σ) :
    Tendsto (fun τ : ℝ => expFlow f hf hpos τ (hz.toLp z)) (𝓝[>] σ)
      (𝓝 (expFlow f hf hpos σ (hz.toLp z))) := by
  set z' : X → ℝ := fun x => Real.exp (-(σ * f x)) * z x with hz'def
  have hz'x : ∀ x : X, z' x = Real.exp (-(σ * f x)) * z x := fun x => by rw [hz'def]
  have hz'm : MemLp z' 2 ν := memLp_exp_mul_ae hz hf hpos hσ
  have hfz' : MemLp (fun x => f x * z' x) 2 ν := by
    refine MemLp.of_le hfz ?_ ?_
    · exact hf.aestronglyMeasurable.mul hz'm.aestronglyMeasurable
    · have hle : ∀ᵐ x ∂ν, Real.exp (-(σ * f x)) ≤ 1 := by
        filter_upwards [hpos] with x hx
        rw [← Real.exp_zero]
        exact Real.exp_le_exp.2 (by nlinarith)
      filter_upwards [hle] with x hx
      have hmain : |f x| * (Real.exp (-(σ * f x)) * |z x|) ≤ |f x| * |z x| := by
        calc |f x| * (Real.exp (-(σ * f x)) * |z x|) ≤ |f x| * (1 * |z x|) :=
              mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right hx (abs_nonneg _))
                (abs_nonneg _)
          _ = |f x| * |z x| := by ring
      calc ‖f x * z' x‖ = |f x| * (Real.exp (-(σ * f x)) * |z x|) := by
            rw [Real.norm_eq_abs, hz'x x, abs_mul, abs_mul,
              abs_of_nonneg (Real.exp_nonneg _)]
        _ ≤ |f x| * |z x| := hmain
        _ = ‖f x * z x‖ := by rw [Real.norm_eq_abs, abs_mul]
  have hExpσ : expFlow f hf hpos σ (hz.toLp z) = hz'm.toLp z' := by
    refine Lp.ext ?_
    filter_upwards [expFlow_coeFn hf hpos hσ (hz.toLp z), hz'm.coeFn_toLp,
      hz.coeFn_toLp] with x h1 h2 h3
    rw [h1, h2, h3, hz'x x]
  have hsub : Tendsto (fun τ : ℝ => τ - σ) (𝓝[>] σ) (𝓝[>] 0) := by
    rw [tendsto_nhdsWithin_iff]
    refine ⟨?_, ?_⟩
    · have hcont : Continuous fun τ : ℝ => τ - σ := continuous_id.sub continuous_const
      simpa using (hcont.tendsto σ).mono_left nhdsWithin_le_nhds
    · filter_upwards [self_mem_nhdsWithin] with τ hτ
      exact sub_pos.2 (Set.mem_Ioi.mp hτ)
  have h0 := (tendsto_expFlow_zero (z := z') hz'm hf hpos hfz').comp hsub
  have h0' : Tendsto
      (fun τ : ℝ => expFlow f hf hpos (τ - σ) (expFlow f hf hpos σ (hz.toLp z)))
      (𝓝[>] σ) (𝓝 (expFlow f hf hpos σ (hz.toLp z))) := by
    rw [hExpσ]
    exact h0
  have hEq : (fun τ : ℝ => expFlow f hf hpos τ (hz.toLp z)) =ᶠ[𝓝[>] σ]
      fun τ => expFlow f hf hpos (τ - σ) (expFlow f hf hpos σ (hz.toLp z)) := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    have hτσ : 0 ≤ τ - σ := le_of_lt (sub_pos.2 hτ)
    rw [expFlow_comp hf hpos hτσ hσ (hz.toLp z)]
    congr 1
    ring_nf
  exact h0'.congr' hEq.symm

/-! ## Strong continuity of the transfer semigroup

The flow acts on `L²(ν)`, but `U` is an isometry, so convergence in `L²(ν)` reflects to `ℋ`: the
multiplier law turns `P τ y` into `expFlow τ (U y)`, and the flow's norm continuity at `σ` then
gives norm continuity of `P` itself. -/

/-- **Strong continuity of the transfer semigroup** at `σ ≥ 0`, in representative form. -/
theorem tendsto_physEvol_of_representative (Λ : OSState) (T : TimeTranslation)
    (hinv : HinvRight Λ T) {f : X → ℝ} (hf : Measurable f) (hpos : ∀ᵐ x ∂ν, 0 ≤ f x)
    (U : Hphys Λ →ₗᵢ[ℝ] Lp ℝ 2 ν)
    (hU : ∀ (τ : ℝ), 0 ≤ τ → ∀ x : Hphys Λ,
      U (physEvolCompletionRightFun hinv τ x) = expFlow f hf hpos τ (U x))
    (y : Hphys Λ) {zy : X → ℝ} (hzy : MemLp zy 2 ν) (hUy : U y = hzy.toLp zy)
    (hfzy : MemLp (fun x => f x * zy x) 2 ν) {σ : ℝ} (hσ : 0 ≤ σ) :
    Tendsto (fun τ : ℝ => physEvolCompletionRightFun hinv τ y) (𝓝[>] σ)
      (𝓝 (physEvolCompletionRightFun hinv σ y)) := by
  have hflow := tendsto_expFlow_at hzy hf hpos hfzy hσ
  have hnonneg : ∀ᶠ τ : ℝ in 𝓝[>] σ, 0 ≤ τ := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact le_trans hσ (le_of_lt (Set.mem_Ioi.mp hτ))
  have hconst : expFlow f hf hpos σ (hzy.toLp zy)
      = U (physEvolCompletionRightFun hinv σ y) := by
    have h := hU σ hσ y
    rw [hUy] at h
    exact h.symm
  rw [hconst] at hflow
  have hflow' : Tendsto (fun τ : ℝ => U (physEvolCompletionRightFun hinv τ y)) (𝓝[>] σ)
      (𝓝 (U (physEvolCompletionRightFun hinv σ y))) := by
    refine hflow.congr' ?_
    filter_upwards [hnonneg] with τ hτ
    have h := hU τ hτ y
    rw [hUy] at h
    exact h.symm
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have h := (Metric.tendsto_nhds.1 hflow') ε hε
  filter_upwards [h] with τ hτ
  rwa [LinearIsometry.dist_map] at hτ

/-- **Strong continuity of the transfer semigroup at `0⁺`**, with limit `y` since `P(0) = 1`. -/
theorem tendsto_physEvol_zero (Λ : OSState) (T : TimeTranslation) (hinv : HinvRight Λ T)
    {f : X → ℝ} (hf : Measurable f) (hpos : ∀ᵐ x ∂ν, 0 ≤ f x)
    (U : Hphys Λ →ₗᵢ[ℝ] Lp ℝ 2 ν)
    (hU : ∀ (τ : ℝ), 0 ≤ τ → ∀ x : Hphys Λ,
      U (physEvolCompletionRightFun hinv τ x) = expFlow f hf hpos τ (U x))
    (y : Hphys Λ) {zy : X → ℝ} (hzy : MemLp zy 2 ν) (hUy : U y = hzy.toLp zy)
    (hfzy : MemLp (fun x => f x * zy x) 2 ν) :
    Tendsto (fun τ : ℝ => physEvolCompletionRightFun hinv τ y) (𝓝[>] 0) (𝓝 y) := by
  have h0 : physEvolCompletionRightFun hinv 0 = ContinuousLinearMap.id ℝ (Hphys Λ) := by
    rw [physEvolCompletionRightFun_of_nonneg hinv le_rfl]
    exact physEvolCompletionRight_zero hinv
  simpa [h0] using tendsto_physEvol_of_representative Λ T hinv hf hpos U hU y hzy hUy hfzy
    (σ := 0) le_rfl

/-- A multiplier bounded by `C` keeps every `L²` class in `L²`. -/
theorem memLp_mul_of_abs_bound {u : X → ℝ} (hu : MemLp u 2 ν) {f : X → ℝ} (hf : Measurable f)
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ᵐ x ∂ν, |f x| ≤ C) :
    MemLp (fun x => f x * u x) 2 ν := by
  refine MemLp.of_le (hu.const_mul C) ?_ ?_
  · exact hf.aestronglyMeasurable.mul hu.aestronglyMeasurable
  · filter_upwards [hC] with x hx
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hC0]
    exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)

/-- **Strong continuity of the transfer semigroup for every vector**, assuming the multiplier `f` is
essentially bounded: then `f` preserves `L²(ν)`, so every `U y` has the required representative. -/
theorem tendsto_physEvol (Λ : OSState) (T : TimeTranslation) (hinv : HinvRight Λ T)
    {f : X → ℝ} (hf : Measurable f) (hpos : ∀ᵐ x ∂ν, 0 ≤ f x)
    (U : Hphys Λ →ₗᵢ[ℝ] Lp ℝ 2 ν)
    (hU : ∀ (τ : ℝ), 0 ≤ τ → ∀ x : Hphys Λ,
      U (physEvolCompletionRightFun hinv τ x) = expFlow f hf hpos τ (U x))
    {C : ℝ} (hC0 : 0 ≤ C) (hC : ∀ᵐ x ∂ν, |f x| ≤ C) (y : Hphys Λ) {σ : ℝ} (hσ : 0 ≤ σ) :
    Tendsto (fun τ : ℝ => physEvolCompletionRightFun hinv τ y) (𝓝[>] σ)
      (𝓝 (physEvolCompletionRightFun hinv σ y)) := by
  have hy : MemLp (U y : X → ℝ) 2 ν := Lp.memLp (U y)
  have hUy : U y = hy.toLp (U y) := by
    refine Lp.ext ?_
    filter_upwards [MemLp.coeFn_toLp hy] with x hx
    exact hx.symm
  exact tendsto_physEvol_of_representative Λ T hinv hf hpos U hU y hy hUy
    (memLp_mul_of_abs_bound hy hf hC0 hC) hσ

/-! ## The KL weight, and monotonicity in time -/

/-- The weighted measure `z² dν` is a push-forward along any measurable `f`: its value on a
measurable set is the weight of the preimage. -/
theorem klMeasure_apply {z : X → ℝ} {f : X → ℝ} (hf : Measurable f) {s : Set ℝ}
    (hs : MeasurableSet s) :
    klMeasure ν f z s = (ν.withDensity (fun x => ENNReal.ofReal (z x * z x))) (f ⁻¹' s) :=
  Measure.map_apply hf hs

/-- **The KL weight `z² dν` is a finite measure** on `X`, since `z ∈ L²(ν)`. -/
theorem weight_univ_lt_top {z : X → ℝ} (hz : MemLp z 2 ν) :
    (ν.withDensity (fun x => ENNReal.ofReal (z x * z x))) Set.univ < ⊤ := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  have hcongr : (∫⁻ x, ENNReal.ofReal (z x * z x) ∂ν)
      = ∫⁻ x, ENNReal.ofReal ((z x) ^ 2) ∂ν := lintegral_congr fun x => by rw [pow_two]
  rw [hcongr, ← ofReal_integral_eq_lintegral_ofReal (MemLp.integrable_sq hz)
    (Eventually.of_forall fun x => sq_nonneg (z x))]
  exact ENNReal.ofReal_lt_top

/-- **The KL measure is a finite measure on `ℝ`, supported on `[0, ∞)`** when `f ≥ 0`: a genuine
finite Borel measure for the decay lemmas of `Clustering`. -/
theorem klMeasure_finite {z : X → ℝ} (hz : MemLp z 2 ν) {f : X → ℝ} (hf : Measurable f)
    (hpos : ∀ᵐ x ∂ν, 0 ≤ f x) :
    IsFiniteMeasure (klMeasure ν f z) ∧ klMeasure ν f z (Set.Iio 0) = 0 :=
  ⟨isFiniteMeasure_klMeasure hz hf, klMeasure_support hf hpos⟩

/-- **The Laplace transform is antitone on `[0, ∞)`** for a measure supported there: increasing `τ`
shrinks `e^{−τλ}` for `λ ≥ 0`. -/
theorem laplace_antitoneOn {ρ : Measure ℝ} [IsFiniteMeasure ρ] (hsupp : ρ (Set.Iio 0) = 0) :
    AntitoneOn (fun τ => laplace ρ τ) (Set.Ici 0) := by
  intro τ₁ hτ₁ τ₂ hτ₂ hle
  refine integral_mono_ae (laplace_integrable_of_support hτ₂ hsupp)
    (laplace_integrable_of_support hτ₁ hsupp) ?_
  have hset : {l : ℝ | ¬ 0 ≤ l} = Set.Iio 0 := by
    ext l
    simp only [Set.mem_setOf_eq, Set.mem_Iio, not_le]
  have hae : ∀ᵐ l ∂ρ, 0 ≤ l := by
    refine ae_iff.2 ?_
    rw [hset]
    exact hsupp
  filter_upwards [hae] with l hl
  refine Real.exp_le_exp.2 ?_
  nlinarith

/-- **The physical two-point function is antitone on `[0, ∞)`**: it is the Laplace transform of the
shared KL measure, so `σ ≤ τ` implies `⟪z, P(τ)z⟫ ≤ ⟪z, P(σ)z⟫`. -/
theorem twoPoint_antitoneOn (Λ : OSState) (T : TimeTranslation) (hinv : HinvRight Λ T)
    {f : X → ℝ} (hf : Measurable f) (hpos : ∀ᵐ x ∂ν, 0 ≤ f x)
    (U : Hphys Λ →ₗᵢ[ℝ] Lp ℝ 2 ν) (z : Hphys Λ)
    {zh : X → ℝ} (hzh : MemLp zh 2 ν) (hzhm : Measurable zh) (hUz : U z = hzh.toLp zh)
    (hU : ∀ (τ : ℝ), 0 ≤ τ → ∀ x : Hphys Λ,
      U (physEvolCompletionRightFun hinv τ x) = expFlow f hf hpos τ (U x)) :
    AntitoneOn (fun τ => ⟪z, physEvolCompletionRightFun hinv τ z⟫) (Set.Ici 0) := by
  haveI : IsFiniteMeasure (klMeasure ν f zh) := isFiniteMeasure_klMeasure hzh hf
  have hsupp : klMeasure ν f zh (Set.Iio 0) = 0 := klMeasure_support hf hpos
  have hkl := (klMeasure_same_for_physEvol_and_expFlow Λ T hinv hf hpos U z hzh hzhm hUz hU).1
  intro τ₁ hτ₁ τ₂ hτ₂ hle
  change ⟪z, physEvolCompletionRightFun hinv τ₂ z⟫
    ≤ ⟪z, physEvolCompletionRightFun hinv τ₁ z⟫
  rw [hkl τ₂ hτ₂, hkl τ₁ hτ₁]
  exact laplace_antitoneOn hsupp hτ₁ hτ₂ hle

/-! ## The right difference quotient: the generator is `−M_f`

For `τ → 0⁺` the slope of `P` is multiplication by `−f`: if `M` is the vector whose image under `U`
is multiplication by `f` on the representative of `y`, then `τ⁻¹ • (P(τ)y − y) → −M` in `ℋ`.  This
is the multiplier model's form of `generatorRight = −M_f`, at the level of vectors and of matrix
elements. -/

/-- **The right difference quotient of `P` at `0⁺`.** -/
theorem tendsto_physEvol_slope (Λ : OSState) (T : TimeTranslation) (hinv : HinvRight Λ T)
    {f : X → ℝ} (hf : Measurable f) (hpos : ∀ᵐ x ∂ν, 0 ≤ f x)
    (U : Hphys Λ →ₗᵢ[ℝ] Lp ℝ 2 ν)
    (hU : ∀ (τ : ℝ), 0 ≤ τ → ∀ x : Hphys Λ,
      U (physEvolCompletionRightFun hinv τ x) = expFlow f hf hpos τ (U x))
    (y : Hphys Λ) {zy : X → ℝ} (hzy : MemLp zy 2 ν) (hUy : U y = hzy.toLp zy)
    (hfzy : MemLp (fun x => f x * zy x) 2 ν) {M : Hphys Λ}
    (hM : U M = hfzy.toLp (fun x => f x * zy x)) :
    Tendsto (fun τ : ℝ => τ⁻¹ • (physEvolCompletionRightFun hinv τ y - y)) (𝓝[>] 0)
      (𝓝 (-M)) := by
  have hslope := tendsto_expFlow_slope hzy hf hpos hfzy
  have hnonneg : ∀ᶠ τ : ℝ in 𝓝[>] 0, 0 ≤ τ := by
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact le_of_lt (Set.mem_Ioi.mp hτ)
  have hM' : U (-M) = -(hfzy.toLp (fun x => f x * zy x)) := by
    rw [map_neg, hM]
  have hslope' : Tendsto (fun τ : ℝ => τ⁻¹ • (U (physEvolCompletionRightFun hinv τ y) - U y))
      (𝓝[>] 0) (𝓝 (U (-M))) := by
    rw [hM']
    refine hslope.congr' ?_
    filter_upwards [hnonneg] with τ hτ
    have h := hU τ hτ y
    rw [hUy] at h
    rw [h.symm, ← hUy]
  have hmap : ∀ τ : ℝ, U (τ⁻¹ • (physEvolCompletionRightFun hinv τ y - y))
      = τ⁻¹ • (U (physEvolCompletionRightFun hinv τ y) - U y) := fun τ => by
    rw [map_smul, map_sub]
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  have h := (Metric.tendsto_nhds.1 hslope') ε hε
  filter_upwards [h] with τ hτ
  rw [← hmap τ, LinearIsometry.dist_map] at hτ
  exact hτ

/-- **Matrix-element form of the generator statement**: the slope `τ⁻¹ • (P(τ)y − y)` has matrix
elements tending to `−⟪x, M⟫`, i.e. `τ ↦ ⟪x, P(τ)y⟫` has right derivative `−⟪x, M⟫` at `0`. -/
theorem tendsto_inner_slope_twoPoint (Λ : OSState) (T : TimeTranslation) (hinv : HinvRight Λ T)
    {f : X → ℝ} (hf : Measurable f) (hpos : ∀ᵐ x ∂ν, 0 ≤ f x)
    (U : Hphys Λ →ₗᵢ[ℝ] Lp ℝ 2 ν)
    (hU : ∀ (τ : ℝ), 0 ≤ τ → ∀ x : Hphys Λ,
      U (physEvolCompletionRightFun hinv τ x) = expFlow f hf hpos τ (U x))
    (y : Hphys Λ) {zy : X → ℝ} (hzy : MemLp zy 2 ν) (hUy : U y = hzy.toLp zy)
    (hfzy : MemLp (fun x => f x * zy x) 2 ν) {M : Hphys Λ}
    (hM : U M = hfzy.toLp (fun x => f x * zy x)) (x : Hphys Λ) :
    Tendsto (fun τ : ℝ => ⟪x, τ⁻¹ • (physEvolCompletionRightFun hinv τ y - y)⟫)
      (𝓝[>] 0) (𝓝 (-⟪x, M⟫)) := by
  have hslope := tendsto_physEvol_slope Λ T hinv hf hpos U hU y hzy hUy hfzy hM
  have hconst : Tendsto (fun _ : ℝ => x) (𝓝[>] (0 : ℝ)) (𝓝 x) := tendsto_const_nhds
  have hinner : Tendsto
      (fun τ : ℝ => inner ℝ x (τ⁻¹ • (physEvolCompletionRightFun hinv τ y - y)))
      (𝓝[>] (0 : ℝ)) (𝓝 (inner ℝ x (-M))) := hconst.inner hslope
  simpa [inner_neg_right] using hinner

/-- **The two-point function has right derivative `−⟪x, M⟫` at `0`**, in the `HasDerivWithinAt`
form on `(0, ∞)`.  This is the derivative reading of `tendsto_inner_slope_twoPoint`, with `P(0) = 1`
identifying `⟪x, P(0)y⟫` with `⟪x, y⟫`. -/
theorem hasDerivWithinAt_twoPoint (Λ : OSState) (T : TimeTranslation) (hinv : HinvRight Λ T)
    {f : X → ℝ} (hf : Measurable f) (hpos : ∀ᵐ x ∂ν, 0 ≤ f x)
    (U : Hphys Λ →ₗᵢ[ℝ] Lp ℝ 2 ν)
    (hU : ∀ (τ : ℝ), 0 ≤ τ → ∀ x : Hphys Λ,
      U (physEvolCompletionRightFun hinv τ x) = expFlow f hf hpos τ (U x))
    (y : Hphys Λ) {zy : X → ℝ} (hzy : MemLp zy 2 ν) (hUy : U y = hzy.toLp zy)
    (hfzy : MemLp (fun x => f x * zy x) 2 ν) {M : Hphys Λ}
    (hM : U M = hfzy.toLp (fun x => f x * zy x)) (x : Hphys Λ) :
    HasDerivWithinAt (fun τ => ⟪x, physEvolCompletionRightFun hinv τ y⟫) (-⟪x, M⟫)
      (Set.Ioi 0) 0 := by
  have h0 : physEvolCompletionRightFun hinv 0 = ContinuousLinearMap.id ℝ (Hphys Λ) := by
    rw [physEvolCompletionRightFun_of_nonneg hinv le_rfl]
    exact physEvolCompletionRight_zero hinv
  have hfun : ∀ τ : ℝ, slope (fun τ => ⟪x, physEvolCompletionRightFun hinv τ y⟫) 0 τ
      = ⟪x, τ⁻¹ • (physEvolCompletionRightFun hinv τ y - y)⟫ := by
    intro τ
    simp only [slope_fun_def_field, h0, ContinuousLinearMap.id_apply, sub_zero, div_eq_inv_mul,
      inner_sub_right, inner_smul_right]
  rw [hasDerivWithinAt_iff_tendsto_slope' (by simp)]
  refine (tendsto_inner_slope_twoPoint Λ T hinv hf hpos U hU y hzy hUy hfzy hM x).congr' ?_
  filter_upwards with τ
  exact (hfun τ).symm

/-! ## Tail bound, and absolute continuity of the KL measure -/

/-- **Exponential tail bound for the transfer two-point function.**  If the KL measure has no mass
below `m`, then `⟪z, P(τ)z⟫ ≤ ‖z‖² e^{−mτ}` for `τ ≥ 0`: the mass bound times the gap decay. -/
theorem twoPoint_le_norm_sq_mul_exp (Λ : OSState) (T : TimeTranslation) (hinv : HinvRight Λ T)
    {f : X → ℝ} (hf : Measurable f) (hpos : ∀ᵐ x ∂ν, 0 ≤ f x)
    (U : Hphys Λ →ₗᵢ[ℝ] Lp ℝ 2 ν) (z : Hphys Λ)
    {zh : X → ℝ} (hzh : MemLp zh 2 ν) (hzhm : Measurable zh) (hUz : U z = hzh.toLp zh)
    (hU : ∀ (τ : ℝ), 0 ≤ τ → ∀ x : Hphys Λ,
      U (physEvolCompletionRightFun hinv τ x) = expFlow f hf hpos τ (U x))
    {m : ℝ} (hgap : klMeasure ν f zh (Set.Iio m) = 0) {τ : ℝ} (hτ : 0 ≤ τ) :
    ⟪z, physEvolCompletionRightFun hinv τ z⟫ ≤ ‖z‖ ^ 2 * Real.exp (-(m * τ)) := by
  haveI : IsFiniteMeasure (klMeasure ν f zh) := isFiniteMeasure_klMeasure hzh hf
  have hsupp : klMeasure ν f zh (Set.Iio 0) = 0 := klMeasure_support hf hpos
  rw [(klMeasure_same_for_physEvol_and_expFlow Λ T hinv hf hpos U z hzh hzhm hUz hU).1 τ hτ,
    ← klMeasure_mass_eq_norm_sq Λ hf U z hzh hUz]
  exact laplace_le_of_massGap hτ (laplace_integrable_of_support hτ hsupp) hgap

/-- **The KL measure is absolutely continuous with respect to the push-forward of `ν` under `f`**:
it is the push-forward of the weighted measure `z² dν ≪ ν`. -/
theorem klMeasure_absolutelyContinuous {z : X → ℝ} {f : X → ℝ} (hf : Measurable f) :
    klMeasure ν f z ≪ ν.map f := by
  have hw : ν.withDensity (fun x => ENNReal.ofReal (z x * z x)) ≪ ν :=
    withDensity_absolutelyContinuous ν _
  simpa [klMeasure] using hw.map hf

/-! ## Support of the KL measure

`klMeasure ν f z` is by construction the push-forward of the weight `z² dν` along `f`, so its
support *is* the essential range of `f` for that weight.  Mathlib has no separate `essRange`, so the
identification is recorded through `Measure.support`: immediate from the definition, then the two
halves that make it concrete — the support always lies in `closure (range f)`, and it contains that
closure as soon as the weight is positive on every open set meeting the range. -/

/-- **The support of the KL measure is the support of the weighted push-forward**, i.e. the
essential range of `f` for the weight `z² dν`. -/
theorem support_klMeasure (z : X → ℝ) (f : X → ℝ) :
    Measure.support (klMeasure ν f z)
      = Measure.support ((ν.withDensity (fun x => ENNReal.ofReal (z x * z x))).map f) :=
  rfl

/-- **The support of the KL measure lies in `closure (range f)`**: off that closure an entire open
neighbourhood of the point has empty preimage, hence zero measure. -/
theorem support_klMeasure_subset_closure_range {z : X → ℝ} {f : X → ℝ} (hf : Measurable f) :
    Measure.support (klMeasure ν f z) ⊆ closure (Set.range f) := by
  intro y hy
  by_contra hnot
  have hU : IsOpen (closure (Set.range f))ᶜ := isClosed_closure.isOpen_compl
  have hempty : f ⁻¹' (closure (Set.range f))ᶜ = (∅ : Set X) := by
    ext x
    constructor
    · intro hx
      exact hx (subset_closure ⟨x, rfl⟩)
    · intro hx
      exact absurd hx (by simp)
  have hzero : klMeasure ν f z (closure (Set.range f))ᶜ = 0 := by
    rw [klMeasure, Measure.map_apply hf hU.measurableSet, hempty, measure_empty]
  exact (Measure.notMem_support_iff_exists.2 ⟨_, hU.mem_nhds hnot, hzero⟩) hy

/-- **`closure (range f)` lies in the support of the KL measure** when the weight is positive on
every open set meeting the range — the defining property of the essential range. -/
theorem closure_range_subset_support_klMeasure {z : X → ℝ} {f : X → ℝ}
    (hpos : ∀ U : Set ℝ, IsOpen U → (U ∩ Set.range f).Nonempty → 0 < klMeasure ν f z U) :
    closure (Set.range f) ⊆ Measure.support (klMeasure ν f z) := by
  intro y hy
  rw [Measure.mem_support_iff_forall]
  intro V hV
  obtain ⟨U, hUV, hUo, hyU⟩ := mem_nhds_iff.1 hV
  have hUpos : 0 < klMeasure ν f z U :=
    hpos U hUo (mem_closure_iff.1 hy U hUo hyU)
  exact lt_of_lt_of_le hUpos ((klMeasure ν f z).mono hUV)

/-- **The support of the KL measure is exactly the essential range of `f`**, identified with
`closure (range f)` once the weight is positive on open sets meeting the range. -/
theorem support_klMeasure_eq_closure_range {z : X → ℝ} {f : X → ℝ} (hf : Measurable f)
    (hpos : ∀ U : Set ℝ, IsOpen U → (U ∩ Set.range f).Nonempty → 0 < klMeasure ν f z U) :
    Measure.support (klMeasure ν f z) = closure (Set.range f) :=
  Set.Subset.antisymm (support_klMeasure_subset_closure_range hf)
    (closure_range_subset_support_klMeasure hpos)

/-- **The KL mass of a set is positive when `ν` gives its preimage positive mass.**  The weight `z²`
is a.e. nonzero, so on a `ν`-positive set it is a.e. positive, and the `lintegral` is positive. -/
theorem klMeasure_pos_of_pos {z : X → ℝ} (hz : Measurable z) (hzne : ∀ᵐ x ∂ν, z x ≠ 0)
    {f : X → ℝ} (hf : Measurable f) {U : Set ℝ} (hU : MeasurableSet U)
    (hUν : 0 < ν (f ⁻¹' U)) : 0 < klMeasure ν f z U := by
  have hs : MeasurableSet (f ⁻¹' U) := hf hU
  have hz0 : MeasurableSet {x : X | z x = 0} := hz (measurableSet_singleton 0)
  have hmem : MeasurableSet {x : X | z x ≠ 0} := hz0.compl
  have hnull : ν {x : X | z x = 0} = 0 := by
    have h := ae_iff.1 hzne
    simpa using h
  have hset : {x : X | ENNReal.ofReal (z x * z x) ≠ 0} = {x : X | z x ≠ 0} := by
    ext x
    simp only [Set.mem_setOf_eq, ne_eq, ENNReal.ofReal_eq_zero, not_le]
    exact ⟨fun h => mul_self_pos.1 h, fun h => mul_self_pos.2 h⟩
  have hzero : ν (f ⁻¹' U \ {x : X | z x ≠ 0}) = 0 := by
    have hsub : f ⁻¹' U \ {x : X | z x ≠ 0} ⊆ {x : X | z x = 0} := by
      intro x hx
      simp only [Set.mem_diff, Set.mem_setOf_eq, not_ne_iff] at hx
      exact hx.2
    exact le_antisymm (((ν).mono hsub).trans (le_of_eq hnull)) (zero_le _)
  have hadd := measure_inter_add_diff (μ := ν) (f ⁻¹' U) hmem
  have hpos : ν (f ⁻¹' U ∩ {x : X | z x ≠ 0}) = ν (f ⁻¹' U) := by
    rw [← hadd, hzero, add_zero]
  have hgmeas : Measurable fun x => ENNReal.ofReal (z x * z x) :=
    ENNReal.measurable_ofReal.comp (hz.mul hz)
  rw [klMeasure, Measure.map_apply hf hU, withDensity_apply _ hs]
  by_contra hcon
  have hI0 : ∫⁻ x in f ⁻¹' U, ENNReal.ofReal (z x * z x) ∂ν = 0 :=
    le_antisymm (not_lt.1 hcon) (zero_le _)
  have hae : (fun x => ENNReal.ofReal (z x * z x)) =ᵐ[ν.restrict (f ⁻¹' U)] 0 :=
    (lintegral_eq_zero_iff hgmeas).1 hI0
  have hsupp0 : (ν.restrict (f ⁻¹' U)) {x : X | ENNReal.ofReal (z x * z x) ≠ 0} = 0 := by
    have h := ae_iff.1 hae
    simpa using h
  rw [hset, Measure.restrict_apply hmem, Set.inter_comm, hpos] at hsupp0
  exact absurd hsupp0 (ne_of_gt hUν)

/-- **The KL weight is positive on open sets meeting the range**, given that `ν` gives positive mass
to the corresponding preimages: the essential-range hypothesis is a property of `ν`. -/
theorem klMeasure_pos_of_isOpen_meets_range {z : X → ℝ} (hz : Measurable z)
    (hzne : ∀ᵐ x ∂ν, z x ≠ 0) {f : X → ℝ} (hf : Measurable f)
    (hνpos : ∀ U : Set ℝ, IsOpen U → (U ∩ Set.range f).Nonempty → 0 < ν (f ⁻¹' U))
    {U : Set ℝ} (hUo : IsOpen U) (hne : (U ∩ Set.range f).Nonempty) :
    0 < klMeasure ν f z U :=
  klMeasure_pos_of_pos hz hzne hf hUo.measurableSet (hνpos U hUo hne)

/-- **The support of the KL measure is `closure (range f)`** under positivity of `ν` on preimages
of open sets meeting the range. -/
theorem support_klMeasure_eq_closure_range_of_measure {z : X → ℝ} (hz : Measurable z)
    (hzne : ∀ᵐ x ∂ν, z x ≠ 0) {f : X → ℝ} (hf : Measurable f)
    (hνpos : ∀ U : Set ℝ, IsOpen U → (U ∩ Set.range f).Nonempty → 0 < ν (f ⁻¹' U)) :
    Measure.support (klMeasure ν f z) = closure (Set.range f) :=
  support_klMeasure_eq_closure_range hf fun U hUo hne =>
    klMeasure_pos_of_pos hz hzne hf hUo.measurableSet (hνpos U hUo hne)

/-- **The infimum of the support of the KL measure is the infimum of the essential range of `f`**:
under the essential-range hypothesis the support *is* that essential range, so the exponent of the
sharp tail bound is `sInf (closure (range f))`. -/
theorem sInf_support_klMeasure_eq {z : X → ℝ} (hz : Measurable z)
    (hzne : ∀ᵐ x ∂ν, z x ≠ 0) {f : X → ℝ} (hf : Measurable f)
    (hνpos : ∀ U : Set ℝ, IsOpen U → (U ∩ Set.range f).Nonempty → 0 < ν (f ⁻¹' U)) :
    sInf (Measure.support (klMeasure ν f z)) = sInf (closure (Set.range f)) := by
  rw [support_klMeasure_eq_closure_range_of_measure hz hzne hf hνpos]

/-- **The KL measure is supported on `[0, ∞)`** when `f ≥ 0`, in the sense of `Measure.support`. -/
theorem support_klMeasure_subset_Ici_zero {z : X → ℝ} {f : X → ℝ} (hf : Measurable f)
    (hpos : ∀ᵐ x ∂ν, 0 ≤ f x) :
    Measure.support (klMeasure ν f z) ⊆ Set.Ici 0 := by
  intro y hy
  by_contra h
  have hy0 : y ∈ Set.Iio (0 : ℝ) := Set.mem_Iio.2 (lt_of_not_ge h)
  exact (Measure.subset_compl_support_of_isOpen isOpen_Iio (klMeasure_support hf hpos)) hy0 hy

/-- **Any half-line below the support has zero KL mass**: `Iio m` is contained in the complement
of the support, which is null in a hereditarily Lindelöf space such as `ℝ`. -/
theorem klMeasure_Iio_of_support_subset {z : X → ℝ} {f : X → ℝ} {m : ℝ}
    (hsupp : Measure.support (klMeasure ν f z) ⊆ Set.Ici m) :
    klMeasure ν f z (Set.Iio m) = 0 := by
  have hsub : Set.Iio m ⊆ (Measure.support (klMeasure ν f z))ᶜ := by
    intro y hy
    exact fun hys => (not_le.2 hy) (Set.mem_Ici.1 (hsupp hys))
  have hzero : klMeasure ν f z (Measure.support (klMeasure ν f z))ᶜ = 0 :=
    Measure.measure_compl_support
  exact le_antisymm (((klMeasure ν f z).mono hsub).trans (le_of_eq hzero)) (zero_le _)

/-- **The exponential tail bound holds for every `m` at or below the support of the KL measure.**
This generalizes `twoPoint_le_norm_sq_mul_exp` from an explicit mass gap `klMeasure (Iio m) = 0` to
the support condition, which is what the essential-range description provides. -/
theorem twoPoint_le_norm_sq_mul_exp_of_support (Λ : OSState) (T : TimeTranslation)
    (hinv : HinvRight Λ T) {f : X → ℝ} (hf : Measurable f) (hpos : ∀ᵐ x ∂ν, 0 ≤ f x)
    (U : Hphys Λ →ₗᵢ[ℝ] Lp ℝ 2 ν) (z : Hphys Λ)
    {zh : X → ℝ} (hzh : MemLp zh 2 ν) (hzhm : Measurable zh) (hUz : U z = hzh.toLp zh)
    (hU : ∀ (τ : ℝ), 0 ≤ τ → ∀ x : Hphys Λ,
      U (physEvolCompletionRightFun hinv τ x) = expFlow f hf hpos τ (U x))
    {m : ℝ} (hsupp : Measure.support (klMeasure ν f zh) ⊆ Set.Ici m) {τ : ℝ} (hτ : 0 ≤ τ) :
    ⟪z, physEvolCompletionRightFun hinv τ z⟫ ≤ ‖z‖ ^ 2 * Real.exp (-(m * τ)) :=
  twoPoint_le_norm_sq_mul_exp Λ T hinv hf hpos U z hzh hzhm hUz hU
    (klMeasure_Iio_of_support_subset hsupp) hτ

/-- **The sharpest case of the tail bound**, with `m` the infimum of the support of the KL measure:
no larger `m` can be used in general, and the support lies in `[0, ∞)` so the infimum exists. -/
theorem twoPoint_le_norm_sq_mul_exp_sInf (Λ : OSState) (T : TimeTranslation)
    (hinv : HinvRight Λ T) {f : X → ℝ} (hf : Measurable f) (hpos : ∀ᵐ x ∂ν, 0 ≤ f x)
    (U : Hphys Λ →ₗᵢ[ℝ] Lp ℝ 2 ν) (z : Hphys Λ)
    {zh : X → ℝ} (hzh : MemLp zh 2 ν) (hzhm : Measurable zh) (hUz : U z = hzh.toLp zh)
    (hU : ∀ (τ : ℝ), 0 ≤ τ → ∀ x : Hphys Λ,
      U (physEvolCompletionRightFun hinv τ x) = expFlow f hf hpos τ (U x))
    {τ : ℝ} (hτ : 0 ≤ τ) :
    ⟪z, physEvolCompletionRightFun hinv τ z⟫ ≤
      ‖z‖ ^ 2 * Real.exp (-(sInf (Measure.support (klMeasure ν f zh)) * τ)) := by
  have hbdd : BddBelow (Measure.support (klMeasure ν f zh)) := by
    refine ⟨0, fun y hy => ?_⟩
    exact Set.mem_Ici.1 (support_klMeasure_subset_Ici_zero hf hpos hy)
  exact twoPoint_le_norm_sq_mul_exp_of_support Λ T hinv hf hpos U z hzh hzhm hUz hU
    (fun y hy => csInf_le hbdd hy) hτ

/-- **The tail bound with the infimum of the essential range of `f` as exponent**, obtained from
the support form by rewriting `sInf (support) = sInf (closure (range f))`. -/
theorem twoPoint_le_norm_sq_mul_exp_range (Λ : OSState) (T : TimeTranslation)
    (hinv : HinvRight Λ T) {f : X → ℝ} (hf : Measurable f) (hpos : ∀ᵐ x ∂ν, 0 ≤ f x)
    (U : Hphys Λ →ₗᵢ[ℝ] Lp ℝ 2 ν) (z : Hphys Λ)
    {zh : X → ℝ} (hzh : MemLp zh 2 ν) (hzhm : Measurable zh) (hUz : U z = hzh.toLp zh)
    (hU : ∀ (τ : ℝ), 0 ≤ τ → ∀ x : Hphys Λ,
      U (physEvolCompletionRightFun hinv τ x) = expFlow f hf hpos τ (U x))
    (hzne : ∀ᵐ x ∂ν, zh x ≠ 0)
    (hνpos : ∀ V : Set ℝ, IsOpen V → (V ∩ Set.range f).Nonempty → 0 < ν (f ⁻¹' V))
    {τ : ℝ} (hτ : 0 ≤ τ) :
    ⟪z, physEvolCompletionRightFun hinv τ z⟫ ≤
      ‖z‖ ^ 2 * Real.exp (-(sInf (closure (Set.range f)) * τ)) := by
  have h := twoPoint_le_norm_sq_mul_exp_sInf Λ T hinv hf hpos U z hzh hzhm hUz hU hτ
  rwa [sInf_support_klMeasure_eq hzhm hzne hf hνpos] at h

/-! ## Convexity in time -/

/-- **The Laplace transform is convex on `[0, ∞)`** for a measure supported there: `τ ↦ e^{−τλ}` is
convex for `λ ≥ 0`, and an integral of functions convex in the parameter is convex in it. -/
theorem convexOn_laplace {ρ : Measure ℝ} [IsFiniteMeasure ρ] (hsupp : ρ (Set.Iio 0) = 0) :
    ConvexOn ℝ (Set.Ici 0) (fun τ => laplace ρ τ) := by
  refine integral_convexOn_of_integrand_ae (convex_Ici (0 : ℝ)) ?_ ?_
  · have hset : {l : ℝ | ¬ 0 ≤ l} = Set.Iio 0 := by
      ext l
      simp only [Set.mem_setOf_eq, Set.mem_Iio, not_le]
    have hae : ∀ᵐ l ∂ρ, 0 ≤ l := by
      refine ae_iff.2 ?_
      rw [hset]
      exact hsupp
    filter_upwards [hae] with l hl
    have h := ConvexOn.comp_linearMap (𝕜 := ℝ) (f := Real.exp) (s := Set.univ) convexOn_exp
      ((-l) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ))
    have hsub := h.subset (by simp) (convex_Ici (0 : ℝ))
    have hfun : (Real.exp ∘ ⇑((-l) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)))
        = fun τ : ℝ => Real.exp (-(τ * l)) := by
      funext τ
      rw [Function.comp_apply,
        show ((-l) • (LinearMap.id : ℝ →ₗ[ℝ] ℝ)) τ = -(l * τ) from by
          simp [LinearMap.smul_apply, smul_eq_mul],
        mul_comm]
    rw [hfun] at hsub
    exact hsub
  · intro a ha
    exact laplace_integrable_of_support ha hsupp

/-- **The physical two-point function is convex on `[0, ∞)`**, being the Laplace transform of the
shared KL measure. -/
theorem twoPoint_convexOn (Λ : OSState) (T : TimeTranslation) (hinv : HinvRight Λ T)
    {f : X → ℝ} (hf : Measurable f) (hpos : ∀ᵐ x ∂ν, 0 ≤ f x)
    (U : Hphys Λ →ₗᵢ[ℝ] Lp ℝ 2 ν) (z : Hphys Λ)
    {zh : X → ℝ} (hzh : MemLp zh 2 ν) (hzhm : Measurable zh) (hUz : U z = hzh.toLp zh)
    (hU : ∀ (τ : ℝ), 0 ≤ τ → ∀ x : Hphys Λ,
      U (physEvolCompletionRightFun hinv τ x) = expFlow f hf hpos τ (U x)) :
    ConvexOn ℝ (Set.Ici 0) (fun τ => ⟪z, physEvolCompletionRightFun hinv τ z⟫) := by
  haveI : IsFiniteMeasure (klMeasure ν f zh) := isFiniteMeasure_klMeasure hzh hf
  have hsupp : klMeasure ν f zh (Set.Iio 0) = 0 := klMeasure_support hf hpos
  have hkl := (klMeasure_same_for_physEvol_and_expFlow Λ T hinv hf hpos U z hzh hzhm hUz hU).1
  exact (convexOn_laplace hsupp).congr fun τ hτ => (hkl τ hτ).symm

end

end BookProof.OSReconstruction
