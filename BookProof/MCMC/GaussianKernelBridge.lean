import Mathlib
import BookProof.MCMC.KernelContract

/-!
# Chapter GaussianKernelBridge — the concrete Gaussian pCN proposal kernel

Plan: `pcnl.md`, packet **T0** ("reuse the actual kernel API, then build its `L²` action"),
deliverable `GaussianKernelBridge.lean`, and packet **P1** (the Gaussian Mehler benchmark).

`KernelContract.lean` states the contract abstractly.  This chapter supplies the concrete
kernel it was written for: the **pCN / Mehler proposal** on `ℝ` with standard Gaussian prior
`π = N(0,1)`,

`x' = ρ x + s ξ,   ξ ~ N(0,1)`,

i.e. the state measure at `x` is the law of `ρ x + s ξ`.  The pair `(ρ, s)` is the
`(cos, sin)` of the proposal angle; the measure-preserving case is `ρ² + s² = 1`, and
`0 ≤ ρ < 1` together with `s = √(1-ρ²)` is the contraction regime of P1.

## What is proved here

* `gaussianPCNKernel ρ s` — the proposal as an honest `ProbabilityTheory.Kernel ℝ ℝ`,
  built from `Kernel.compProd` and `Kernel.map` of Mathlib's kernel API.
* `instIsMarkovKernel_gaussianPCNKernel` — it is a Markov kernel.
* `gaussianPCNKernel_apply` — its state measure: `κ x = π.map (ξ ↦ ρ x + s ξ)`.
* `gaussianPCNKernel_bind` — the **joint representation**
  `π.bind κ = (π.prod π).map (p ↦ ρ p.1 + s p.2)`, i.e. one Mehler step applied to two
  independent draws has the law of the pushforward of the product measure.
* `gaussianPCNKernel_invariant` — **prior invariance**: for `ρ² + s² = 1`,
  `κ.Invariant π`, so `π` is stationary for the proposal.  This is the analytic content
  P1 needs: one Mehler step with `ρ² + s² = 1` leaves `N(0,1)` fixed.
* `isReversible_of_swap_invariant_joint` — a general bridge lemma: a Markov kernel whose
  joint law `π ⊗ₘ κ` is invariant under `Prod.swap` satisfies `Kernel.IsReversible κ π`.
  Reversibility is thus reduced to the symmetry of the joint law.

## Honest boundary

* Reversibility of `gaussianPCNKernel` itself is **not** claimed here; the reduction above
  isolates exactly what it needs.  The symmetry of the two-dimensional Mehler joint
  `(x, ξ) ↦ (x, ρ x + s ξ)` is proved in `GaussianReversibility.lean`, as
  `gaussianPCNKernel_swap_invariant_joint`, using the density of `gaussianReal` together with
  the identity `y² s² + (x - ρ y)² = x² s² + (y - ρ x)²`; `gaussianPCNKernel_isReversible`
  there is the resulting detailed-balance statement.  Nothing is left open for
  `gaussianPCNKernel` in the `ρ² + s² = 1`, `s > 0` regime.
* The `L²` action on `Lp ℂ 2 π` is the separate `Lp` descent; here only the kernel-level
  statements are made.  `GaussianPCNL2` supplies the function-level part for this kernel
  (`κ x ≪ π` for `s ≠ 0`, hence `MemLp (P f) 2 π` and `‖P f‖₂ ≤ ‖f‖₂`); the packaged
  `Lp` operator is still open there.
-/

noncomputable section

namespace BookProof.MCMC

open MeasureTheory ProbabilityTheory
open scoped ENNReal MeasureTheory

/-- **The pCN / Mehler proposal kernel on `ℝ`.**  The state measure at `x` is the law of
`ρ x + s ξ` with `ξ` a standard normal, obtained by composing the deterministic kernel
`x ↦ (x, x)`-style product `Kernel.id ⊗ₖ const N(0,1)` with the affine map
`(x, ξ) ↦ ρ x + s ξ`.

The parameters are kept free: the measure-preserving (reversible-regime) case is
`ρ² + s² = 1`, and Gaussian moment identities are stated under the hypotheses that make them
true rather than baked into the definition. -/
noncomputable def gaussianPCNKernel (ρ s : ℝ) : Kernel ℝ ℝ :=
  Kernel.map (Kernel.compProd Kernel.id (Kernel.const (ℝ × ℝ) (gaussianReal 0 1)))
    (fun p : ℝ × ℝ => ρ * p.1 + s * p.2)

/-- The Gaussian proposal is a Markov kernel. -/
instance instIsMarkovKernel_gaussianPCNKernel (ρ s : ℝ) : IsMarkovKernel (gaussianPCNKernel ρ s) :=
  Kernel.IsMarkovKernel.map _ (by fun_prop)

/-- **State measure of the Gaussian proposal**: `κ x = N(0,1).map (ξ ↦ ρ x + s ξ)`. -/
theorem gaussianPCNKernel_apply (ρ s x : ℝ) :
    gaussianPCNKernel ρ s x = (gaussianReal 0 1).map (fun ξ : ℝ => ρ * x + s * ξ) := by
  unfold gaussianPCNKernel
  rw [Kernel.map_apply _ (by fun_prop) x, Kernel.compProd_apply_eq_compProd_sectR,
    Kernel.id_apply]
  have hsect : Kernel.sectR (Kernel.const (ℝ × ℝ) (gaussianReal 0 1)) x
      = Kernel.const ℝ (gaussianReal 0 1) := by
    ext b s hs
    rfl
  rw [hsect, Measure.compProd_const, Measure.dirac_prod,
    Measure.map_map (by fun_prop) (by fun_prop)]
  rfl

/-- **The joint representation of one Mehler step.**  Applying the proposal to a draw from
`π = N(0,1)` gives the pushforward of the product measure `π ⊗ π` under
`(x, ξ) ↦ ρ x + s ξ`; the first coordinate is the current state, the second the proposal. -/
theorem gaussianPCNKernel_bind (ρ s : ℝ) :
    (gaussianReal 0 1).bind (gaussianPCNKernel ρ s)
      = ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
          (fun p : ℝ × ℝ => ρ * p.1 + s * p.2) := by
  ext t ht
  rw [Measure.bind_apply ht (Kernel.aemeasurable _), Measure.map_apply (by fun_prop) ht,
    Measure.prod_apply (measurableSet_preimage (by fun_prop) ht)]
  refine lintegral_congr fun x => ?_
  rw [gaussianPCNKernel_apply, Measure.map_apply (by fun_prop) ht]
  rfl

/-- The Mehler pushforward of two independent standard normals is again a standard normal
when `ρ² + s² = 1`.  This is the computation behind prior invariance. -/
theorem gaussianReal_mehler_map (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) :
    ((gaussianReal 0 1).prod (gaussianReal 0 1)).map
        (fun p : ℝ × ℝ => ρ * p.1 + s * p.2) = gaussianReal 0 1 := by
  have hcomp : (fun p : ℝ × ℝ => ρ * p.1 + s * p.2)
      = (fun q : ℝ × ℝ => q.1 + q.2) ∘ (Prod.map (fun x : ℝ => ρ * x) (fun ξ : ℝ => s * ξ)) :=
    rfl
  conv_lhs => rw [hcomp]
  rw [← Measure.map_map (g := fun q : ℝ × ℝ => q.1 + q.2) (by fun_prop) (by fun_prop),
    ← Measure.map_prod_map _ _ (by fun_prop) (by fun_prop)]
  change Measure.conv ((gaussianReal 0 1).map (fun x : ℝ => ρ * x))
      ((gaussianReal 0 1).map (fun ξ : ℝ => s * ξ)) = gaussianReal 0 1
  rw [gaussianReal_map_const_mul, gaussianReal_map_const_mul, gaussianReal_conv_gaussianReal]
  congr 2
  · ring
  · rw [← NNReal.coe_inj]
    push_cast
    linarith [hρs]

/-- **Prior invariance of the Gaussian proposal**: if `ρ² + s² = 1`, the standard normal
is stationary for the Mehler kernel. -/
theorem gaussianPCNKernel_invariant (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) :
    (gaussianPCNKernel ρ s).Invariant (gaussianReal 0 1) := by
  rw [ProbabilityTheory.Kernel.Invariant]
  rw [gaussianPCNKernel_bind, gaussianReal_mehler_map ρ s hρs]

/-! ## 2. Reversibility: the joint-symmetry bridge -/

/-- **Joint symmetry implies detailed balance.**  If the joint law `π ⊗ₘ κ` of
`(x, κ x)` is invariant under exchanging its two coordinates, then `κ` is reversible with
respect to `π`.

This isolates the single two-dimensional fact that reversibility of a Gaussian proposal
needs: exchangeability of the joint law.  The proof reads the two setwise flows as the
`A × B` and `B × A` masses of the joint. -/
theorem isReversible_of_swap_invariant_joint {α : Type*} [MeasurableSpace α]
    (κ : Kernel α α) [IsSFiniteKernel κ] (π : Measure α) [SFinite π]
    (h : (π ⊗ₘ κ).map Prod.swap = π ⊗ₘ κ) : Kernel.IsReversible κ π := by
  intro A B hA hB
  have hAB : (π ⊗ₘ κ) (A ×ˢ B) = (π ⊗ₘ κ) (B ×ˢ A) := by
    rw [← h, Measure.map_apply measurable_swap (hB.prod hA)]
    congr 1
    ext p
    simp
  rw [← Measure.compProd_apply_prod hA hB, ← Measure.compProd_apply_prod hB hA]
  exact hAB

end BookProof.MCMC
