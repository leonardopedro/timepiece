import Mathlib
import BookProof.MCMC.KernelContract

/-!
# Chapter LpDescent — the kernel action on almost-everywhere classes

Plan: `pcnl.md`, packet **T0**: "*Then descend to almost-everywhere equivalence classes and
extend to `Lp complex 2 pi`. This must prove that changing a representative does not change
the resulting `L2` class; writing the Bochner integral for an arbitrary representative is not
sufficient.*"

`KernelContract.lintegral_kernelIntegral_sq_le` proves the `L²(π)` contraction for a
*function* `f`, with integrability assumed at every state measure `κ x`.  This chapter
supplies the part of the descent that does not need that assumption: the action
`(Pf)(x) = ∫ y, f y ∂(κ x)` is well defined on almost-everywhere classes, and is additive and
homogeneous.

## What is proved here

* `markovOpFun` — the function-level action `(Pf)(x) = ∫ y, f y ∂(κ x)`.
* `markovOpFun_congr` — **representative independence**: if every state measure is absolutely
  continuous with respect to `π`, then `f =ᵐ[π] g` implies `Pf = Pg` pointwise.  This is the
  step the plan insists on; it is what makes the action a function of the `L²` class rather
  than of a chosen representative.
* `markovOpFun_add`, `markovOpFun_smul` — additivity and `ℂ`-homogeneity, which are what an
  eventual `LinearMap` structure consumes.

## Honest boundary

**Status update.**  Both bullets below are now supplied at the function level.
`LpMarkovOperator.ae_integrable_kernel` proves, from the joint measure `π ⊗ₘ κ`, that
`f ∈ L¹(π)` is `κ x`-integrable for `π`-almost every `x`; `lintegral_kernelIntegral_sq_le_ae`
is the `L²` contraction with those a.e. hypotheses; `aestronglyMeasurable_kernelIntegral`
proves a.e. strong measurability of the action; `memLp_two_kernelIntegral` proves
`MemLp (Pf) 2 π`; and `eLpNorm_kernelIntegral_le` is the norm estimate `‖P f‖₂ ≤ ‖f‖₂`.
What remains is the quotient/packaging step only.

**Second status update.**  That step is now *proved*, in `LpKernelOperator`: `markovOpLp` is the
`ContinuousLinearMap` on `Lp ℂ 2 π` with `norm_markovOpLp_le_one : ‖markovOpLp κ π hπ hac‖ ≤ 1`,
and `markovOpLp_coeFn` identifies its action with `kernelIntegral` on representatives.  The
pCN instance is `gaussianPCNOp` (`norm_gaussianPCNOp_le_one`), for `s ≠ 0`.

Why the quotient was not a formality:

* *Integrability at each state measure.*  `markovOpFun` is defined through the Bochner
  integral, which is junk (`0`) where `f` is not `κ x`-integrable.  For the Gaussian proposal
  the density `d(κ x)/dπ` is unbounded (it grows like `exp(y²(1-s²)/(2s²))` for `s < 1`), so
  `L¹(π)` does not embed in `L¹(κ x)` for every `x`; the contraction estimate therefore carries
  its integrability hypotheses only almost everywhere, and the quotient step needs `κ x ≪ π`
  for every `x` to make `Pf` dependent on the class rather than the representative.
* *The `Lp` assembly.*  `MemLp (Pf) 2 π` and the norm bound are exactly what `MemLp.toLp`
  consumes; additivity and `ℂ`-homogeneity of `toLp` need an a.e. linearity statement, which is
  `markovOpLpFun_add`/`markovOpLpFun_smul` in `LpKernelOperator`, and `LinearMap.mkContinuous`
  then produces the operator with its norm bound.
-/

noncomputable section

namespace BookProof.MCMC

open MeasureTheory ProbabilityTheory
open scoped ENNReal

variable {α : Type*} [MeasurableSpace α]

/-- The action of a Markov kernel on functions: `(Pf)(x) = ∫ y, f y ∂(κ x)`. -/
def markovOpFun (κ : Kernel α α) (f : α → ℂ) (x : α) : ℂ :=
  ∫ y, f y ∂(κ x)

/-- **Representative independence.**  If every state measure is absolutely continuous with
respect to `π`, then functions equal `π`-almost everywhere have equal actions.  This is what
makes `markovOpFun` act on `L²(π)` classes rather than on representatives. -/
theorem markovOpFun_congr (κ : Kernel α α) (π : Measure α) (hac : ∀ x, κ x ≪ π)
    {f g : α → ℂ} (hfg : f =ᵐ[π] g) (x : α) :
    markovOpFun κ f x = markovOpFun κ g x := by
  unfold markovOpFun
  exact integral_congr_ae ((hac x).ae_le hfg)

/-- The action is additive wherever both terms are integrable at the state measure. -/
theorem markovOpFun_add (κ : Kernel α α) (f g : α → ℂ) (x : α)
    (hf : Integrable f (κ x)) (hg : Integrable g (κ x)) :
    markovOpFun κ (f + g) x = markovOpFun κ f x + markovOpFun κ g x := by
  unfold markovOpFun
  exact integral_add hf hg

/-- The action is `ℂ`-homogeneous. -/
theorem markovOpFun_smul (κ : Kernel α α) (c : ℂ) (f : α → ℂ) (x : α) :
    markovOpFun κ (c • f) x = c • markovOpFun κ f x := by
  unfold markovOpFun
  exact integral_smul c f

/-- For a Markov kernel the action fixes constants: `P 1 = 1`. -/
theorem markovOpFun_one (κ : Kernel α α) [IsMarkovKernel κ] (x : α) :
    markovOpFun κ (fun _ => (1 : ℂ)) x = 1 := by
  unfold markovOpFun
  rw [integral_const, probReal_univ, one_smul]

end BookProof.MCMC
