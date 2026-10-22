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

end BayesianTransformer
