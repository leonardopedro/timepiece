import Mathlib
import BookProof.OSReconstruction.L2Multiplier
import BookProof.OSReconstruction.SemigroupGenerator

/-!
# The generator of `P` is the transported generator of the flow

`OSReconstruction.L2Multiplier` proved the difference-quotient statement *for the flow*:
`τ⁻¹ • (expFlow τ u − u) → −f·u` in `L²(ν)` (`tendsto_expFlow_slope`), and carried it to the
transfer semigroup as the vector limit `τ⁻¹ • (P(τ)y − y) → −M` whenever `U M = M_f(U y)`
(`tendsto_physEvol_slope`).  Both are statements about *limits*, and neither says that the limit
is the generator: `HasGenRight`, `genDomainRight` and `generatorRight` of
`OSReconstruction.SemigroupGenerator` ask for exactly that, in `ℋ`, and `L2Multiplier`'s boundary
records the gap — `generatorRight = −M_f` was asserted for the flow only.

This module closes the gap, and it does so without a spectral theorem.  The observation is that a
bridge is an *isometry*, so the difference quotient commutes with it exactly:

`U (τ⁻¹ • (P(τ)z − z)) = τ⁻¹ • (Q(τ)(U z) − U z)`   (`map_diffQuot`),

for `τ ≥ 0` and every `z`.  That identity is the whole content of the transfer, because

* `hasGenRight_of_bridge` — a limit of the `Q`-side quotient produces a limit on the `ℋ` side, by
  applying the inverse unitary to the convergent sequence.  So the *domain* of the forward generator
  is the preimage of the domain of the flow's generator;
* `generatorRight_bridge` — and the *value* is the transported one,
  `U (generatorRight z) = w`, by uniqueness of limits in `F`.  This is what the corpus called the
  missing identification of generators: it needs no self-adjointness of `H`, no Friedrichs
  extension, and no functional calculus, only that the flows correspond;
* `exists_generatorRight_mulModel` — the multiplier instance: with the multiplier law
  `U (P(τ)x) = expFlow τ (U x)` and `f·zy ∈ L²`, the vector `y` is in the forward-time domain and
  `U (generatorRight y) = −M_f(U y)`.  Since the bridge is onto (`OsFockBridge.surjective`), the
  `M` of `tendsto_physEvol_slope` always exists, so that theorem's `hM` hypothesis disappears;
* `inner_generatorRight_mulModel` — the quadratic form of the generator on that domain is
  `⟪A y, y⟫ = −∫ f |zy|²`, so `A = −M_f` and dissipativity (`generatorRight_inner_le_zero`) is
  exactly `f ≥ 0` a.e.  The Wick-rotated Hamiltonian is `M_f ≥ 0`, and the generator is its
  negative — which is why the one-sided contractivity hypothesis is the correct one.
* `exists_resolvent_mulModel`, `range_sub_generatorRight_mulModel` — the Lumer–Phillips **range
  condition** `ran(λ − A) = ℋ` for `λ > 0`, with the inverse written down: multiplication by
  `(λ + f)⁻¹` is bounded by `1/λ` exactly because `f ≥ 0`, so the preimage of `(λ + f)⁻¹(U x)` is a
  domain vector solving `λ y − A y = x`;
* `norm_resolvent_mulModel` — the matching estimate `λ‖y‖ ≤ ‖x‖`, the a priori bound of
  `SemigroupGenerator` read on the explicit solution.

## Boundary

The multiplier law `U (P(τ)x) = expFlow τ (U x)` remains a hypothesis, and it is the spectral
theorem for `P`: the module identifies the generator *given* the flow, it does not produce the
flow from the OS axioms.  What is no longer open is the passage from a flow to the generator —
that is an isometry calculation, and it is now a theorem for every bridge, not only for the
multiplier model.

The other half of Lumer–Phillips — the **range condition** `ran(λ − A) = ℋ` for `λ > 0` — is
proved too, in the last section: the candidate is written down rather than postulated, as the
preimage under the bridge of `(λ + f)⁻¹(U x)`.  So `λ − A` is onto with an explicit inverse
(`exists_resolvent_mulModel`, `range_sub_generatorRight_mulModel`), and the inverse is bounded by
`1/λ` (`norm_resolvent_mulModel`), which is the estimate `SemigroupGenerator` already had.  What is
*not* claimed is that the self-adjoint `H` with `A = −H` exists as an operator: `(λ + f)⁻¹` is a
bounded multiplier and `λ − A` is onto, but no unbounded self-adjoint operator is constructed here,
and the multiplier law itself is still the hypothesis that supplies the flow.
-/

namespace BookProof.OSReconstruction

open Filter MeasureTheory
open scoped Topology RealInnerProductSpace ENNReal

noncomputable section

variable {Λ : OSState} {T : TimeTranslation}

/-! ## A bridge commutes with the difference quotient -/

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℝ F]
variable {Q : ℝ → F →L[ℝ] F}

/-- **The difference quotient passes through the bridge.**  For `τ ≥ 0` the isometry `U` carries
the quotient of `P` to the quotient of `Q`, because it is linear and intertwines the two flows.  No
limit is taken here: this is the identity that makes the generator statements equivalent. -/
theorem map_diffQuot (hinv : HinvRight Λ T)
    (B : OsFockBridge F (physEvolCompletionRightFun hinv) Q) {τ : ℝ} (hτ : 0 ≤ τ)
    (z : Hphys Λ) :
    B.U (diffQuot hinv τ z) = τ⁻¹ • (Q τ (B.U z) - B.U z) := by
  simp only [diffQuot]
  rw [map_smul, map_sub, B.intertwines τ hτ z]

/-! ## The domain and the value of the generator transport -/

/-- **The forward-time domain is the preimage of the flow's domain.**  If the `Q`-side quotient
converges to `w`, then `z` lies in the domain of the transfer generator: the inverse unitary,
applied to the convergent sequence, is a convergent sequence of difference quotients. -/
theorem hasGenRight_of_bridge (hinv : HinvRight Λ T)
    (B : OsFockBridge F (physEvolCompletionRightFun hinv) Q) {z : Hphys Λ} {w : F}
    (hw : Tendsto (fun τ : ℝ => τ⁻¹ • (Q τ (B.U z) - B.U z)) (𝓝[>] 0) (𝓝 w)) :
    HasGenRight hinv z := by
  refine ⟨B.toIsometryEquiv.symm w, ?_⟩
  have hcomp : Tendsto
      (fun τ : ℝ => B.toIsometryEquiv.symm (τ⁻¹ • (Q τ (B.U z) - B.U z)))
      (𝓝[>] 0) (𝓝 (B.toIsometryEquiv.symm w)) :=
    (B.toIsometryEquiv.symm.continuous.tendsto w).comp hw
  refine hcomp.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  rw [← map_diffQuot hinv B (le_of_lt hτ) z]
  simp

/-- **The generator's value is the transported value.**  On the domain, `U` identifies the
forward-time generator of `P` with the generator of the flow `Q`: the image of the limit is the
limit of the images. -/
theorem generatorRight_bridge (hinv : HinvRight Λ T)
    (B : OsFockBridge F (physEvolCompletionRightFun hinv) Q) {z : Hphys Λ}
    (hz : HasGenRight hinv z) {w : F}
    (hw : Tendsto (fun τ : ℝ => τ⁻¹ • (Q τ (B.U z) - B.U z)) (𝓝[>] 0) (𝓝 w)) :
    B.U (generatorRight hinv ⟨z, hz⟩) = w := by
  have himg : Tendsto (fun τ : ℝ => B.U (diffQuot hinv τ z)) (𝓝[>] 0)
      (𝓝 (B.U (generatorRight hinv ⟨z, hz⟩))) :=
    (B.U.continuous.tendsto _).comp (generatorRight_apply_tendsto hinv ⟨z, hz⟩)
  have hslope : Tendsto (fun τ : ℝ => B.U (diffQuot hinv τ z)) (𝓝[>] 0) (𝓝 w) := by
    refine hw.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with τ hτ
    exact (map_diffQuot hinv B (le_of_lt hτ) z).symm
  exact tendsto_nhds_unique himg hslope

/-! ## The multiplier instance: `generatorRight = −M_f` -/

variable {X : Type*} [MeasurableSpace X] {ν : Measure X}

/-- **The transfer semigroup's forward generator is `−M_f`, at the level of vectors.**  In the
multiplier model, for `y ∈ ℋ` whose image has a representative `zy` with `f·zy ∈ L²(ν)`, the vector
`y` is in the forward-time domain and its generator value maps to `−f·zy`:

`U (generatorRight y) = −(f zy)`  in `L²(ν)`.

This is `tendsto_physEvol_slope` read as a statement about `generatorRight` rather than about a
limit: the bridge is onto, so the auxiliary vector `M` of that theorem is available, and the
uniqueness of limits identifies it with the generator's value.  The multiplier law remains the only
hypothesis. -/
theorem exists_generatorRight_mulModel (hinv : HinvRight Λ T)
    {f : X → ℝ} (hf : Measurable f) (hpos : ∀ᵐ x ∂ν, 0 ≤ f x)
    (U : Hphys Λ →ₗᵢ[ℝ] Lp ℝ 2 ν) (hdense : DenseRange U)
    (hU : ∀ (τ : ℝ), 0 ≤ τ → ∀ x : Hphys Λ,
      U (physEvolCompletionRightFun hinv τ x) = expFlow f hf hpos τ (U x))
    (y : Hphys Λ) {zy : X → ℝ} (hzy : MemLp zy 2 ν) (hUy : U y = hzy.toLp zy)
    (hfzy : MemLp (fun x => f x * zy x) 2 ν) :
    ∃ hz : HasGenRight hinv y,
      U (generatorRight hinv ⟨y, hz⟩) = -(hfzy.toLp (fun x => f x * zy x)) := by
  let B := osFockBridgeOfMulModel Λ hf hpos (physEvolCompletionRightFun hinv) U hdense hU
  set M : Hphys Λ := B.toIsometryEquiv.symm (hfzy.toLp (fun x => f x * zy x)) with hM
  have hMimg : U M = hfzy.toLp (fun x => f x * zy x) := B.apply_toIsometryEquiv_symm_apply _
  have hslope : Tendsto (fun τ : ℝ => τ⁻¹ • (physEvolCompletionRightFun hinv τ y - y))
      (𝓝[>] 0) (𝓝 (-M)) :=
    tendsto_physEvol_slope Λ T hinv hf hpos U hU y hzy hUy hfzy hMimg
  have hquot : Tendsto (fun τ : ℝ => diffQuot hinv τ y) (𝓝[>] 0) (𝓝 (-M)) := by
    simpa only [diffQuot] using hslope
  refine ⟨⟨-M, hquot⟩, ?_⟩
  have hval : generatorRight hinv ⟨y, ⟨-M, hquot⟩⟩ = -M :=
    generatorRight_apply_eq_of_tendsto hinv ⟨y, ⟨-M, hquot⟩⟩ hquot
  rw [hval, map_neg, hMimg]

/-- **The generator's quadratic form is `−∫ f zy²`.**  On the multiplier domain the generator is
multiplication by `−f`, so its quadratic form is the negative of the `f`-weighted mass.  With
`f ≥ 0` a.e. this *is* the dissipativity `⟪A y, y⟫ ≤ 0` of `generatorRight_inner_le_zero`, now with
the quantitative value: the Wick-rotated Hamiltonian is `M_f ≥ 0`, and its spectrum is the
essential range of `f`. -/
theorem inner_generatorRight_mulModel (hinv : HinvRight Λ T) {f : X → ℝ}
    (U : Hphys Λ →ₗᵢ[ℝ] Lp ℝ 2 ν)
    (y : Hphys Λ) {zy : X → ℝ} (hzy : MemLp zy 2 ν) (hUy : U y = hzy.toLp zy)
    (hfzy : MemLp (fun x => f x * zy x) 2 ν) {hz : HasGenRight hinv y}
    (hgen : U (generatorRight hinv ⟨y, hz⟩) = -(hfzy.toLp (fun x => f x * zy x))) :
    ⟪generatorRight hinv ⟨y, hz⟩, y⟫ = -∫ x, f x * zy x * zy x ∂ν := by
  have hinner : ⟪generatorRight hinv ⟨y, hz⟩, y⟫
      = ⟪-(hfzy.toLp (fun x => f x * zy x)), hzy.toLp zy⟫ := by
    rw [← U.inner_map_map (generatorRight hinv ⟨y, hz⟩) y, hgen, hUy]
  rw [hinner, inner_neg_left, L2.inner_def]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [hfzy.coeFn_toLp, hzy.coeFn_toLp] with x h1 h2
  rw [h1, h2, RCLike.inner_apply', RCLike.conj_to_real]

/-- Dissipativity, read off the multiplier: the generator's quadratic form is nonpositive because
`f ≥ 0` a.e.  This recovers `generatorRight_inner_le_zero` on the multiplier domain from the
identification `A = −M_f`, and identifies the sign convention: `H = M_f ≥ 0` is the Hamiltonian,
`A = −H` is the Euclidean generator. -/
theorem inner_generatorRight_mulModel_nonpos (hinv : HinvRight Λ T)
    {f : X → ℝ} (hpos : ∀ᵐ x ∂ν, 0 ≤ f x)
    (U : Hphys Λ →ₗᵢ[ℝ] Lp ℝ 2 ν)
    (y : Hphys Λ) {zy : X → ℝ} (hzy : MemLp zy 2 ν) (hUy : U y = hzy.toLp zy)
    (hfzy : MemLp (fun x => f x * zy x) 2 ν) {hz : HasGenRight hinv y}
    (hgen : U (generatorRight hinv ⟨y, hz⟩) = -(hfzy.toLp (fun x => f x * zy x))) :
    ⟪generatorRight hinv ⟨y, hz⟩, y⟫ ≤ 0 := by
  rw [inner_generatorRight_mulModel hinv U y hzy hUy hfzy hgen]
  refine neg_nonpos.2 (integral_nonneg_of_ae ?_)
  filter_upwards [hpos] with x hx
  have hsq : f x * zy x * zy x = f x * (zy x * zy x) := by ring
  rw [hsq]
  exact mul_nonneg hx (mul_self_nonneg (zy x))

/-! ## The range condition: `λ − A` is onto, with the resolvent `(λ + f)⁻¹`

Lumer–Phillips needs two halves: the a priori estimate, which is
`generatorRight_resolvent_bound` in `OSReconstruction.SemigroupGenerator`, and the **range
condition** `ran(λ − A) = ℋ` for `λ > 0`, which that module records as not proved.  In the
multiplier model the second half is explicit rather than abstract: the inverse is multiplication by
`(λ + f)⁻¹`, bounded by `1/λ` exactly because `f ≥ 0`.  The candidate is written down and shown to
lie in the domain using the identification `A = −M_f` of the previous section, so no self-adjoint
operator is needed — only the multiplier law. -/

/-- **The resolvent exists, explicitly.**  For `λ > 0` every `x : ℋ` is `λ y − A y` for some
domain vector `y`: take `y` to be the preimage under the bridge of `(λ + f)⁻¹ · (U x)`.  The three
things that have to be checked are that `(λ + f)⁻¹(U x)` is in the multiplier domain — i.e. that
`f (λ + f)⁻¹ (U x)` is in `L²`, which holds because `f/(λ + f) ≤ 1` — that its preimage is in the
forward-time domain (the previous section), and that `(λ + f)(λ + f)⁻¹ = 1` a.e. -/
theorem exists_resolvent_mulModel (hinv : HinvRight Λ T)
    {f : X → ℝ} (hf : Measurable f) (hpos : ∀ᵐ x ∂ν, 0 ≤ f x)
    (U : Hphys Λ →ₗᵢ[ℝ] Lp ℝ 2 ν) (hdense : DenseRange U)
    (hU : ∀ (τ : ℝ), 0 ≤ τ → ∀ x : Hphys Λ,
      U (physEvolCompletionRightFun hinv τ x) = expFlow f hf hpos τ (U x))
    {lam : ℝ} (hlam : 0 < lam) (x : Hphys Λ) :
    ∃ y : (generatorRight hinv).domain,
      lam • (y : Hphys Λ) - generatorRight hinv y = x := by
  let g : X → ℝ := fun t => (lam + f t)⁻¹
  have hgmeas : Measurable g := (hf.const_add lam).inv
  have hgbound : ∀ᵐ t ∂ν, ‖g t‖ ≤ lam⁻¹ := by
    filter_upwards [hpos] with t ht
    have hpos' : 0 < lam + f t := by linarith
    rw [Real.norm_eq_abs, abs_of_pos (inv_pos.2 hpos')]
    exact inv_anti₀ hlam (by linarith)
  have hg : MemLp g ⊤ ν := memLp_top_of_bound hgmeas.aestronglyMeasurable lam⁻¹ hgbound
  have hfg : MemLp (fun t => f t * g t) ⊤ ν := by
    refine memLp_top_of_bound (hf.mul hgmeas).aestronglyMeasurable 1 ?_
    filter_upwards [hpos] with t ht
    have hq : 0 < lam + f t := by linarith
    have hnn : 0 ≤ g t := inv_nonneg.2 hq.le
    have hle : f t * g t ≤ 1 := by
      calc f t * g t ≤ (lam + f t) * g t := mul_le_mul_of_nonneg_right (by linarith) hnn
        _ = 1 := mul_inv_cancel₀ hq.ne'
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg ht hnn)]
    exact hle
  let W : Lp ℝ ⊤ ν := hg.toLp g
  have hW : (W : X → ℝ) =ᵐ[ν] g := MemLp.coeFn_toLp hg
  let v : Lp ℝ 2 ν := mulL2 W (U x)
  let zx : X → ℝ := (U x : X → ℝ)
  let zy : X → ℝ := fun t => g t * zx t
  have hv_eq : (v : X → ℝ) =ᵐ[ν] zy := by
    filter_upwards [mulL2_coeFn W (U x), hW] with t h1 h2
    rw [h1, h2]
  have hzy : MemLp zy 2 ν := by
    refine MemLp.congr_norm (Lp.memLp v) ?_ ?_
    · simp only [zy]
      exact hgmeas.aestronglyMeasurable.mul (Lp.memLp (U x)).aestronglyMeasurable
    · filter_upwards [hv_eq] with t ht
      rw [ht]
  have hfx : MemLp (fun t => (f t * g t) * zx t) 2 ν :=
    (ContinuousLinearMap.mul ℝ ℝ).memLp_of_bilin 2 hfg (Lp.memLp (U x))
  have hfzy : MemLp (fun t => f t * zy t) 2 ν := by
    refine hfx.congr_norm (hf.aestronglyMeasurable.mul hzy.aestronglyMeasurable) ?_
    filter_upwards with t
    simp only [zy, Real.norm_eq_abs]
    congr 1
    ring
  let B := osFockBridgeOfMulModel Λ hf hpos (physEvolCompletionRightFun hinv) U hdense hU
  let y : Hphys Λ := B.toIsometryEquiv.symm (hzy.toLp zy)
  have hUy : U y = hzy.toLp zy := B.apply_toIsometryEquiv_symm_apply (hzy.toLp zy)
  obtain ⟨hz, hgen⟩ :=
    exists_generatorRight_mulModel hinv hf hpos U hdense hU y hzy hUy hfzy
  refine ⟨⟨y, hz⟩, ?_⟩
  have hsum : lam • (hzy.toLp zy) + hfzy.toLp (fun t => f t * zy t) = U x := by
    refine Lp.ext ?_
    filter_upwards [Lp.coeFn_add (lam • (hzy.toLp zy)) (hfzy.toLp (fun t => f t * zy t)),
      Lp.coeFn_smul lam (hzy.toLp zy), MemLp.coeFn_toLp hfzy, MemLp.coeFn_toLp hzy, hpos]
      with t h1 h2 h3 h4 ht
    rw [h1, Pi.add_apply, h2, Pi.smul_apply, smul_eq_mul, h3, h4]
    have hq : lam + f t ≠ 0 := by linarith
    change lam * (g t * zx t) + f t * (g t * zx t) = zx t
    calc lam * (g t * zx t) + f t * (g t * zx t)
        = ((lam + f t) * g t) * zx t := by ring
      _ = zx t := by rw [mul_inv_cancel₀ hq, one_mul]
  refine U.injective ?_
  change U (lam • y - generatorRight hinv ⟨y, hz⟩) = U x
  rw [map_sub, map_smul, hgen, hUy, sub_neg_eq_add]
  exact hsum

/-- **The Lumer–Phillips range condition**, in the multiplier model: `λ − A` is onto `ℋ` for
`λ > 0`.  Together with the a priori estimate of `SemigroupGenerator` this is the pair of
hypotheses Lumer–Phillips needs; what is still a hypothesis here is the multiplier law, which is
what supplies the candidate `(λ + f)⁻¹`. -/
theorem range_sub_generatorRight_mulModel (hinv : HinvRight Λ T)
    {f : X → ℝ} (hf : Measurable f) (hpos : ∀ᵐ x ∂ν, 0 ≤ f x)
    (U : Hphys Λ →ₗᵢ[ℝ] Lp ℝ 2 ν) (hdense : DenseRange U)
    (hU : ∀ (τ : ℝ), 0 ≤ τ → ∀ x : Hphys Λ,
      U (physEvolCompletionRightFun hinv τ x) = expFlow f hf hpos τ (U x))
    {lam : ℝ} (hlam : 0 < lam) :
    Function.Surjective (fun y : (generatorRight hinv).domain =>
      lam • (y : Hphys Λ) - generatorRight hinv y) :=
  fun x => exists_resolvent_mulModel hinv hf hpos U hdense hU hlam x

/-- **The resolvent is bounded by `1/λ`**, the quantitative half: the solution `y` of
`λ y − A y = x` satisfies `λ‖y‖ ≤ ‖x‖`.  This is `generatorRight_resolvent_bound` applied to the
explicit solution, so the range condition and the estimate meet in the same statement. -/
theorem norm_resolvent_mulModel (hinv : HinvRight Λ T)
    {lam : ℝ} (hlam : 0 < lam) {y : (generatorRight hinv).domain} {x : Hphys Λ}
    (h : lam • (y : Hphys Λ) - generatorRight hinv y = x) :
    lam * ‖(y : Hphys Λ)‖ ≤ ‖x‖ := by
  rw [← h]
  exact generatorRight_resolvent_bound hinv y hlam

end

end BookProof.OSReconstruction
