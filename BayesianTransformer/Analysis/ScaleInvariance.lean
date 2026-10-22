module

public import Mathlib.Analysis.Calculus.Gradient.Basic
public import Mathlib.Analysis.Calculus.Deriv.Mul
public import Mathlib.Analysis.Calculus.Deriv.Comp

/-!
# Milestone 2: Scale invariance and orthogonal gradient drift

Euler's homogeneous function theorem in degree zero: a differentiable potential that is invariant
under positive homotheties, `Φ (c • w) = Φ w` for `c > 0`, has a derivative that annihilates `w`,
i.e. its gradient is orthogonal to `w`.

Note: the plan states both theorems with an extra hypothesis `w ≠ 0`. It is not needed (at
`w = 0` the conclusion `dΦ(0) 0 = 0` holds by linearity), so it is omitted, which makes the
statements more general.
-/

@[expose] public section

namespace BayesianTransformer

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Scale invariance of a functional `Phi` under positive scalar homotheties. -/
def IsScaleInvariant (Phi : E → ℝ) : Prop :=
  ∀ (w : E) (c : ℝ), 0 < c → Phi (c • w) = Phi w

/-- Euler's theorem for homogeneous functions of degree zero:
if `Phi` is scale invariant and differentiable at `w`, then `dPhi(w) w = 0`. -/
theorem scaleInvariant_gradient_orthogonal
    {Phi : E → ℝ} (h_scale : IsScaleInvariant Phi)
    {w : E} (h_diff : DifferentiableAt ℝ Phi w) :
    (fderiv ℝ Phi w) w = 0 := by
  -- the auxiliary path `γ c = Phi (c • w)`
  have hpath : HasDerivAt (fun c : ℝ => c • w) w 1 := by
    simpa using (hasDerivAt_id (1 : ℝ)).smul_const w
  have hγ : HasDerivAt (fun c : ℝ => Phi (c • w)) ((fderiv ℝ Phi w) w) 1 := by
    have h : HasFDerivAt Phi (fderiv ℝ Phi w) ((1 : ℝ) • w) := by
      rw [one_smul]; exact h_diff.hasFDerivAt
    exact HasFDerivAt.comp_hasDerivAt (1 : ℝ) h hpath
  -- `γ` is locally constant near `1`, hence has derivative `0` there
  have hconst : HasDerivAt (fun c : ℝ => Phi (c • w)) 0 1 := by
    refine (hasDerivAt_const (1 : ℝ) (Phi w)).congr_of_eventuallyEq ?_
    filter_upwards [lt_mem_nhds (show (0 : ℝ) < 1 by norm_num)] with c hc
    exact h_scale w c hc
  exact hγ.unique hconst

/-- Gradient formulation via the Riesz representation: `⟪w, ∇Phi(w)⟫ = 0`. -/
theorem scaleInvariant_inner_grad_zero [CompleteSpace E]
    {Phi : E → ℝ} (h_scale : IsScaleInvariant Phi)
    {w : E} (h_diff : DifferentiableAt ℝ Phi w) :
    inner ℝ w (gradient Phi w) = 0 := by
  rw [real_inner_comm, gradient, InnerProductSpace.toDual_symm_apply]
  exact scaleInvariant_gradient_orthogonal h_scale h_diff

end BayesianTransformer
