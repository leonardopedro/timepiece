module

public import BayesianTransformer.Analysis.SphereProj
public import BayesianTransformer.Analysis.ScaleInvariance
public import BayesianTransformer.Transformer.CosineAttention
public import Mathlib.Analysis.Calculus.FDeriv.Comp
public import Mathlib.Analysis.Calculus.FDeriv.Add
public import Mathlib.Analysis.Calculus.FDeriv.Mul

/-!
# Milestone 4: Global gradient bound of the full nGPT network (Theorem 1)

* `NGPTLayer`, `NGPTModel`: the abstract formulation of the plan.
* `nGPT_uniform_gradient_bound`: if every per-example loss has a uniformly bounded derivative
  (`NGPTModel.uniform_grad_bound`), then so does the empirical risk (data average), with the same
  ceiling `M`, uniformly over all parameters `w`.
* `normalized_fderiv_le`, `normalized_fderiv_le_uniform`: the mechanism behind the uniform bound.
  If a block `g` only sees the *normalized* weight `Ŵ = W / ‖W‖` and has derivative bounded by
  `K` on the unit sphere, then `‖d(g ∘ Π)(W)‖ ≤ K / ‖W‖`, so parameter growth can only *shrink*
  the chain-rule operator norm (Milestone 1 feeds in here).
* `epsProj`, `epsProj_fderiv_opNorm_le`, `epsProj_fderiv_le`: the *additive* `ε`-regularization
  `Ŵ = W/(‖W‖ + ε)` that the SG-pCNL work order (`pcnl.md` §2.2) actually writes.  It is not
  scale invariant, so its differential costs `2/ε` rather than `1/ε`, and a block's gradient is
  bounded by `K_ε/ε` with `K_ε = 2K` on the domain `‖W‖ ≥ ε`.  This is the `M_ε = K/ε` that
  `BookProof.MCMC.FockLangevin`'s `driftScale_eps_arch` turns into the drift's constant.
* `isScaleInvariant_comp_sphereProj`, `normalized_gradient_orthogonal`: any scalar potential of
  the normalized weight is scale invariant, hence (Milestone 2) its derivative annihilates `W`.

The per-example bound assumed in `NGPTModel.uniform_grad_bound` is *derived* for a concrete
normalized-transformer architecture in `Transformer/NGPTArchitecture.lean`
(`ngpt_exampleLoss_fderiv_bound`, `ngpt_empiricalRisk_fderiv_bound`), on the parameter domain
where every weight has norm at least `ε > 0`.

Note: the plan's hypothesis `data.Nonempty` turned out to be unnecessary (for empty data the
averaged loss is identically `0`), so it is omitted.
-/

@[expose] public section

namespace BayesianTransformer

/-- Abstract formulation of an nGPT layer as a composition of bounded-derivative blocks. -/
structure NGPTLayer (E : Type*) [NormedAddCommGroup E] [InnerProductSpace ℝ E] where
  forward : E → E → E  -- (parameters, input) -> output
  eps : ℝ
  eps_pos : 0 < eps
  fderiv_weight_bound : ∀ (w x : E), ‖x‖ = 1 → ‖fderiv ℝ (fun w => forward w x) w‖ ≤ eps⁻¹

/-- The total multi-layer nGPT network composed with the loss. -/
structure NGPTModel (Param : Type*) (Input : Type*) [NormedAddCommGroup Param]
    [InnerProductSpace ℝ Param] where
  loss : Param → Input → ℝ
  differentiable : ∀ x, Differentiable ℝ (fun w => loss w x)
  uniform_grad_bound :
    ∃ M : ℝ, 0 < M ∧ ∀ (w : Param) (x : Input), ‖fderiv ℝ (fun w => loss w x) w‖ ≤ M

variable {Param Input : Type*} [NormedAddCommGroup Param] [InnerProductSpace ℝ Param]

/-- **Theorem 1** (main formal theorem): existence of a universal gradient ceiling `M` for the
empirical risk `w ↦ (1/|D|) ∑_{x ∈ D} ℓ(w, x)`, uniformly over all parameters `w`. -/
theorem nGPT_uniform_gradient_bound
    (model : NGPTModel Param Input) (data : Finset Input) :
    ∃ M : ℝ, 0 < M ∧ ∀ (w : Param),
      ‖fderiv ℝ (fun w => (data.sum (fun x => model.loss w x)) / (data.card : ℝ)) w‖ ≤ M := by
  obtain ⟨M, hM, hbound⟩ := model.uniform_grad_bound
  refine ⟨M, hM, fun w => ?_⟩
  have hsum : HasFDerivAt (fun w => data.sum (fun x => model.loss w x))
      (∑ x ∈ data, fderiv ℝ (fun w => model.loss w x) w) w :=
    HasFDerivAt.fun_sum fun x _ => ((model.differentiable x) w).hasFDerivAt
  have hdiv : HasFDerivAt (fun w => (data.sum (fun x => model.loss w x)) / (data.card : ℝ))
      ((data.card : ℝ)⁻¹ • ∑ x ∈ data, fderiv ℝ (fun w => model.loss w x) w) w := by
    simpa only [div_eq_mul_inv] using hsum.mul_const (data.card : ℝ)⁻¹
  rw [hdiv.fderiv, norm_smul, Real.norm_eq_abs, abs_inv, Nat.abs_cast]
  rcases Nat.eq_zero_or_pos data.card with h0 | hpos
  · rw [h0]; simp [hM.le]
  · have hc : (0 : ℝ) < data.card := by exact_mod_cast hpos
    rw [inv_mul_le_iff₀ hc]
    calc ‖∑ x ∈ data, fderiv ℝ (fun w => model.loss w x) w‖
        ≤ ∑ x ∈ data, ‖fderiv ℝ (fun w => model.loss w x) w‖ := norm_sum_le _ _
      _ ≤ ∑ _x ∈ data, M := Finset.sum_le_sum fun x _ => hbound w x
      _ = data.card * M := by simp

section Normalization

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The hyperspherical projection is invariant under positive rescaling. -/
theorem sphereProj_smul_pos (w : E) {c : ℝ} (hc : 0 < c) : sphereProj (c • w) = sphereProj w := by
  rw [sphereProj, sphereProj, norm_smul, Real.norm_eq_abs, abs_of_pos hc, smul_smul]
  rcases eq_or_ne w 0 with rfl | hw
  · simp
  · congr 1
    have : ‖w‖ ≠ 0 := norm_ne_zero_iff.mpr hw
    field_simp

/-- Internal normalization: if a block `g` sees only the normalized weight `Π(W) = W / ‖W‖` and
`‖dg‖ ≤ K` on the unit sphere, then `‖d(g ∘ Π)(W)‖ ≤ K / ‖W‖`. -/
theorem normalized_fderiv_le {g : E → F} {K : ℝ} (hK : 0 ≤ K)
    (hg_diff : ∀ u : E, ‖u‖ = 1 → DifferentiableAt ℝ g u)
    (hg_bound : ∀ u : E, ‖u‖ = 1 → ‖fderiv ℝ g u‖ ≤ K)
    {w : E} (hw : w ≠ 0) :
    ‖fderiv ℝ (g ∘ sphereProj) w‖ ≤ K * ‖w‖⁻¹ := by
  have hu := norm_sphereProj hw
  rw [fderiv_comp w (hg_diff _ hu) (sphereProj_differentiableAt hw)]
  calc ‖(fderiv ℝ g (sphereProj w)).comp (fderiv ℝ sphereProj w)‖
      ≤ ‖fderiv ℝ g (sphereProj w)‖ * ‖fderiv ℝ sphereProj w‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ K * ‖w‖⁻¹ :=
        mul_le_mul (hg_bound _ hu) (sphereProj_fderiv_opNorm_le hw) (norm_nonneg _) hK

/-- Uniform version on an `ε`-separated parameter domain: `‖d(g ∘ Π)(W)‖ ≤ K / ε`
whenever `‖W‖ ≥ ε`, independently of how large `W` is. -/
theorem normalized_fderiv_le_uniform {g : E → F} {K : ℝ} (hK : 0 ≤ K)
    (hg_diff : ∀ u : E, ‖u‖ = 1 → DifferentiableAt ℝ g u)
    (hg_bound : ∀ u : E, ‖u‖ = 1 → ‖fderiv ℝ g u‖ ≤ K)
    {ε : ℝ} (hε : 0 < ε) {w : E} (hw : ε ≤ ‖w‖) :
    ‖fderiv ℝ (g ∘ sphereProj) w‖ ≤ K * ε⁻¹ := by
  have hw0 : w ≠ 0 := norm_pos_iff.mp (hε.trans_le hw)
  exact (normalized_fderiv_le hK hg_diff hg_bound hw0).trans
    (mul_le_mul_of_nonneg_left (inv_anti₀ hε hw) hK)

/-- Any scalar potential of the normalized weight is scale invariant. -/
theorem isScaleInvariant_comp_sphereProj (g : E → ℝ) : IsScaleInvariant (g ∘ sphereProj) :=
  fun w _c hc => by simp only [Function.comp_apply, sphereProj_smul_pos w hc]

/-- Orthogonal drift for normalized potentials: the derivative of `g ∘ Π` annihilates `W`
(Milestone 2 applied to the normalized architecture). -/
theorem normalized_gradient_orthogonal {g : E → ℝ} {w : E}
    (h_diff : DifferentiableAt ℝ (g ∘ sphereProj) w) :
    (fderiv ℝ (g ∘ sphereProj) w) w = 0 :=
  scaleInvariant_gradient_orthogonal (isScaleInvariant_comp_sphereProj g) h_diff

end Normalization

section EpsNormalization

variable {E F : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
  [NormedAddCommGroup F] [NormedSpace ℝ F]

/-- The `ε`-regularized normalization `Ŵ = W / (‖W‖ + ε)` of the SG-pCNL architecture.  The
parameter enters the potential only through this map, so the `1/ε` of the gradient bound is the
differential of this one function.  Unlike `sphereProj` it is defined at the origin (there it is
`W/ε`), so it needs no `ε`-separated domain to *exist* — only to be bounded — and it is not
scale invariant, which is the factor `2` in `epsProj_fderiv_opNorm_le` below. -/
noncomputable def epsProj (ε : ℝ) (v : E) : E := (‖v‖ + ε)⁻¹ • v

/-- The normalized weight stays in the closed unit ball: `‖W/(‖W‖ + ε)‖ ≤ 1`. -/
theorem norm_epsProj_le {ε : ℝ} (hε : 0 < ε) (v : E) : ‖epsProj ε v‖ ≤ 1 := by
  have hr : (0 : ℝ) < ‖v‖ + ε := by positivity
  rw [epsProj, norm_smul, Real.norm_eq_abs, abs_of_pos (inv_pos.mpr hr), mul_comm]
  have h : ‖v‖ * (‖v‖ + ε)⁻¹ ≤ (‖v‖ + ε) * (‖v‖ + ε)⁻¹ :=
    mul_le_mul_of_nonneg_right (le_add_of_nonneg_right hε.le) (inv_nonneg.mpr hr.le)
  simpa [mul_inv_cancel₀ hr.ne'] using h

/-- Derivative of the scalar factor `x ↦ (‖x‖ + ε)⁻¹` away from the origin. -/
theorem norm_add_inv_hasFDerivAt {ε : ℝ} (hε : 0 < ε) {v : E} (hv : v ≠ 0) :
    HasFDerivAt (fun x : E => (‖x‖ + ε)⁻¹)
      (-(((‖v‖ + ε) ^ 2)⁻¹ * ‖v‖⁻¹) • innerSL ℝ v) v := by
  have hn : 0 < ‖v‖ := norm_pos_iff.mpr hv
  have h1 : HasFDerivAt (fun x : E => Real.sqrt (‖x‖ ^ 2))
      ((1 / (2 * Real.sqrt (‖v‖ ^ 2))) •
        (2 • (innerSL ℝ v).comp (ContinuousLinearMap.id ℝ E))) v :=
    ((hasFDerivAt_id v).norm_sq).sqrt (by positivity)
  have h1' : HasFDerivAt (fun x : E => ‖x‖) (‖v‖⁻¹ • innerSL ℝ v) v := by
    convert h1 using 1
    · ext x
      rw [Real.sqrt_sq (norm_nonneg x)]
    · ext x
      simp only [ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
        ContinuousLinearMap.id_apply, Real.sqrt_sq hn.le, smul_eq_mul]
      ring_nf
  have hbase : HasDerivAt (fun y : ℝ => y⁻¹) (-(((‖v‖ + ε) ^ 2)⁻¹)) (‖v‖ + ε) :=
    hasDerivAt_inv (x := ‖v‖ + ε) (by positivity)
  have hadd : HasDerivAt (fun t : ℝ => t + ε) 1 ‖v‖ := (hasDerivAt_id ‖v‖).add_const ε
  have h3 : HasDerivAt (fun t : ℝ => (t + ε)⁻¹) (-(((‖v‖ + ε) ^ 2)⁻¹)) ‖v‖ := by
    simpa using HasDerivAt.comp (x := ‖v‖) hbase hadd
  have h4 : HasFDerivAt (fun x : E => (‖x‖ + ε)⁻¹)
      ((-(((‖v‖ + ε) ^ 2)⁻¹)) • (‖v‖⁻¹ • innerSL ℝ v)) v :=
    HasDerivAt.comp_hasFDerivAt (f := fun x : E => ‖x‖) (x := v) h3 h1'
  convert h4 using 1
  ext x
  simp only [ContinuousLinearMap.smul_apply, smul_eq_mul]
  ring

/-- Differential of the `ε`-regularized normalization. -/
theorem epsProj_hasFDerivAt {ε : ℝ} (hε : 0 < ε) {v : E} (hv : v ≠ 0) :
    HasFDerivAt (epsProj ε)
      ((‖v‖ + ε)⁻¹ • ContinuousLinearMap.id ℝ E +
        ContinuousLinearMap.smulRight
          (-(((‖v‖ + ε) ^ 2)⁻¹ * ‖v‖⁻¹) • innerSL ℝ v) v) v :=
  (norm_add_inv_hasFDerivAt hε hv).smul (hasFDerivAt_id v)

/-- `epsProj` is differentiable away from the origin. -/
theorem epsProj_differentiableAt {ε : ℝ} (hε : 0 < ε) {v : E} (hv : v ≠ 0) :
    DifferentiableAt ℝ (epsProj ε) v := (epsProj_hasFDerivAt hε hv).differentiableAt

/-- **`‖dŴ‖ ≤ 2/ε` on `{‖W‖ ≥ ε}`.**  The two terms of the differential are each at most
`ε⁻¹`: the first is the identity scaled by `(‖W‖ + ε)⁻¹ ≤ ε⁻¹`, and the second is the radial
correction, whose norm is `‖W‖/(‖W‖ + ε)² ≤ ε⁻¹` (the `‖W‖ ≤ ‖W‖ + ε` cancellation).  The sum
is therefore `2/ε` — where the sphere projection `W/‖W‖` costs `1/ε`, because it is scale
invariant and this map is not. -/
theorem epsProj_fderiv_opNorm_le {ε : ℝ} (hε : 0 < ε) {v : E} (hv : ε ≤ ‖v‖) :
    ‖fderiv ℝ (epsProj ε) v‖ ≤ 2 / ε := by
  have hr : (0 : ℝ) < ‖v‖ + ε := by positivity
  have hv0 : v ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hv
    linarith
  rw [(epsProj_hasFDerivAt hε hv0).fderiv]
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun x => ?_
  have hinv : (‖v‖ + ε)⁻¹ ≤ ε⁻¹ := inv_anti₀ hε (le_add_of_nonneg_left (norm_nonneg v))
  have hsq : ((‖v‖ + ε) ^ 2)⁻¹ ≤ (‖v‖ + ε)⁻¹ * ε⁻¹ := by
    rw [sq, mul_inv]
    exact mul_le_mul_of_nonneg_left hinv (inv_nonneg.mpr hr.le)
  have hinner : ∀ x : E, |inner ℝ v x| ≤ ‖v‖ * ‖x‖ := fun x => abs_real_inner_le_norm v x
  calc ‖((‖v‖ + ε)⁻¹ • ContinuousLinearMap.id ℝ E +
        ContinuousLinearMap.smulRight (-(((‖v‖ + ε) ^ 2)⁻¹ * ‖v‖⁻¹) • innerSL ℝ v) v) x‖
      = ‖(‖v‖ + ε)⁻¹ • x
          + (-(((‖v‖ + ε) ^ 2)⁻¹ * ‖v‖⁻¹) * inner ℝ v x) • v‖ := by
        simp [ContinuousLinearMap.smulRight_apply]
    _ ≤ ‖(‖v‖ + ε)⁻¹ • x‖
          + ‖(-(((‖v‖ + ε) ^ 2)⁻¹ * ‖v‖⁻¹) * inner ℝ v x) • v‖ := norm_add_le _ _
    _ = (‖v‖ + ε)⁻¹ * ‖x‖
          + |(((‖v‖ + ε) ^ 2)⁻¹ * ‖v‖⁻¹) * inner ℝ v x| * ‖v‖ := by
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs,
          abs_of_nonneg (inv_nonneg.mpr hr.le), neg_mul, abs_neg]
    _ ≤ (‖v‖ + ε)⁻¹ * ‖x‖
          + ((((‖v‖ + ε) ^ 2)⁻¹ * ‖v‖⁻¹) * (‖v‖ * ‖x‖)) * ‖v‖ := by
        have hle : |(((‖v‖ + ε) ^ 2)⁻¹ * ‖v‖⁻¹) * inner ℝ v x|
            ≤ (((‖v‖ + ε) ^ 2)⁻¹ * ‖v‖⁻¹) * (‖v‖ * ‖x‖) := by
          rw [abs_mul, abs_of_nonneg (mul_nonneg (inv_nonneg.mpr (sq_nonneg _))
            (inv_nonneg.mpr (norm_nonneg v)))]
          exact mul_le_mul_of_nonneg_left (hinner x)
            (mul_nonneg (inv_nonneg.mpr (sq_nonneg _)) (inv_nonneg.mpr (norm_nonneg v)))
        exact add_le_add (le_refl _) (mul_le_mul_of_nonneg_right hle (norm_nonneg v))
    _ = ((‖v‖ + ε)⁻¹ + ((‖v‖ + ε) ^ 2)⁻¹ * ‖v‖) * ‖x‖ := by
        field_simp
    _ ≤ (2 / ε) * ‖x‖ := by
        have h1 : (‖v‖ + ε)⁻¹ ≤ ε⁻¹ := hinv
        have h2 : ((‖v‖ + ε) ^ 2)⁻¹ * ‖v‖ ≤ ε⁻¹ := by
          calc ((‖v‖ + ε) ^ 2)⁻¹ * ‖v‖ ≤ ((‖v‖ + ε) ^ 2)⁻¹ * (‖v‖ + ε) :=
                mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hε.le) (by positivity)
            _ = (‖v‖ + ε)⁻¹ := by field_simp
            _ ≤ ε⁻¹ := hinv
        have hsum : (‖v‖ + ε)⁻¹ + ((‖v‖ + ε) ^ 2)⁻¹ * ‖v‖ ≤ ε⁻¹ + ε⁻¹ :=
          add_le_add h1 h2
        rw [show (2 : ℝ) / ε = 2 * ε⁻¹ by ring]
        exact mul_le_mul_of_nonneg_right (by linarith) (norm_nonneg x)

/-- **The gradient bound `M_ε = K_ε/ε` of the `ε`-regularized potential.**  If the block `g`
that sees only the normalized weight `Ŵ = W/(‖W‖ + ε)` has derivative bounded by `K` on the
closed unit ball, then the potential `g ∘ Ŵ` has derivative bounded by `K_ε/ε` on the
`ε`-separated domain `‖W‖ ≥ ε`, with `K_ε = 2K`: the chain rule times `epsProj_fderiv_opNorm_le`.
This is `pcnl.md` §2.2's `M_ε = K/ε`, with the factor `2` absorbed into `K_ε`. -/
theorem epsProj_fderiv_le {g : E → F} {K : ℝ} (hK : 0 ≤ K)
    (hg_diff : ∀ u : E, ‖u‖ ≤ 1 → DifferentiableAt ℝ g u)
    (hg_bound : ∀ u : E, ‖u‖ ≤ 1 → ‖fderiv ℝ g u‖ ≤ K)
    {ε : ℝ} (hε : 0 < ε) {w : E} (hw : ε ≤ ‖w‖) :
    ‖fderiv ℝ (g ∘ epsProj ε) w‖ ≤ 2 * K / ε := by
  have hball : ‖epsProj ε w‖ ≤ 1 := norm_epsProj_le hε w
  have hw0 : w ≠ 0 := norm_pos_iff.mp (hε.trans_le hw)
  rw [fderiv_comp w (hg_diff _ hball) (epsProj_differentiableAt hε hw0)]
  calc ‖(fderiv ℝ g (epsProj ε w)).comp (fderiv ℝ (epsProj ε) w)‖
      ≤ ‖fderiv ℝ g (epsProj ε w)‖ * ‖fderiv ℝ (epsProj ε) w‖ :=
        ContinuousLinearMap.opNorm_comp_le _ _
    _ ≤ K * (2 / ε) :=
        mul_le_mul (hg_bound _ hball) (epsProj_fderiv_opNorm_le hε hw) (by positivity) hK
    _ = 2 * K / ε := by ring

end EpsNormalization

end BayesianTransformer
