import Mathlib

/-!
# The kernel contract (pcnl.md P0)

`pcnl.md` P0 asks for one file that fixes, before any posterior or outer-Fock lift:

* a **measurable kernel** `κ` on a state space `α`;
* its **integral action** on observables, `P f x = ∫ f d(κ x)`;
* the **stationary law**, i.e. `Kernel.Invariant κ π`, and the detailed-balance
  (reversibility) notion `Kernel.IsReversible κ π`;
* the **associated `L²` operator** and its contraction;
* the **adjoint/density action**, so that the density chain and the observable
  chain are not conflated.

## What is proved

* `kernelOp` is the integral action; `kernelOp_one` proves `P 1 = 1` for a Markov
  kernel, so a kernel contract cannot silently lose mass;
* `convexOn_norm_sq` and `norm_integral_sq_le_integral_norm_sq` prove the
  pointwise **Jensen estimate** `‖P f x‖² ≤ P (‖f‖²) x` for a probability fiber,
  and `kernelOp_jensen` is the kernel form of it;
* `const_kernelOp`, `const_invariant`, `const_reversible` instantiate the contract
  on the **prior-refresh benchmark** `Kernel.const α π`: the kernel that forgets
  the current state and redraws from `π` is `π`-invariant and reversible;
* `const_l2_contraction`, `const_mean_preserved` and `const_selfAdjoint_pairing`
  give the `L²(π)` contraction, the preservation of the mean and the
  adjoint/density action for that benchmark.

## Boundary

The general `L²` contraction `∫ ‖P f‖² dπ ≤ ∫ ‖f‖² dπ` under an arbitrary
`Kernel.Invariant κ π` needs the Fubini identity for a kernel against an invariant
measure together with the integrability of the parameterized integral; those are
stated and proved here only for the concrete benchmark, where the integral action
is constant in `x`.  No posterior, no `pCN` proposal and no outer-Fock lift is
claimed: a `Kernel` is a transition law, not yet a self-adjoint operator on a
specified dense domain.
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace BookProof.MCMC

variable {α : Type*} [MeasurableSpace α]

/-! ## 1. The integral action and `P 1 = 1` -/

/-- **The integral action** of a kernel on observables:
`P f x = ∫ y, f y ∂(κ x)`.  This is the observable orientation used throughout
`pcnl.md`; the density chain evolves by the adjoint. -/
def kernelOp (κ : Kernel α α) {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    (f : α → E) (x : α) : E :=
  ∫ y, f y ∂(κ x)

@[simp]
theorem kernelOp_apply (κ : Kernel α α) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : α → E) (x : α) :
    kernelOp κ f x = ∫ y, f y ∂(κ x) := rfl

/-- **`P 1 = 1`** for a Markov kernel: the integral action preserves the unit
observable, hence the total mass of every fiber. -/
theorem kernelOp_one {κ : Kernel α α} [IsMarkovKernel κ] :
    kernelOp (E := ℂ) κ (fun _ => 1) = fun _ => 1 := by
  funext x
  simp [kernelOp]

/-! ## 2. The pointwise Jensen estimate -/

/-- **`z ↦ ‖z‖²` is convex on `ℂ`.**  This is the convexity that the pointwise
Jensen estimate for the norm of an integral needs; it is not the composition of
two scalar convex functions, because `‖·‖` is real-valued on a complex space. -/
theorem convexOn_norm_sq : ConvexOn ℝ (Set.univ : Set ℂ) (fun z => ‖z‖ ^ 2) := by
  refine ⟨convex_univ, ?_⟩
  intro x _ y _ a b ha hb hab
  have hxy : inner ℝ x y ≤ ‖x‖ * ‖y‖ := real_inner_le_norm x y
  have h1 : ‖a • x + b • y‖ ^ 2
      = a ^ 2 * ‖x‖ ^ 2 + 2 * (a * b) * inner ℝ x y + b ^ 2 * ‖y‖ ^ 2 := by
    rw [norm_add_sq_real, real_inner_smul_left, real_inner_smul_right]
    simp only [norm_smul, Real.norm_eq_abs, abs_of_nonneg ha, abs_of_nonneg hb]
    ring
  change ‖a • x + b • y‖ ^ 2 ≤ a * ‖x‖ ^ 2 + b * ‖y‖ ^ 2
  rw [h1]
  have h3 : 2 * (a * b) * inner ℝ x y ≤ a * b * (‖x‖ ^ 2 + ‖y‖ ^ 2) := by
    nlinarith [hxy, mul_nonneg ha hb, sq_nonneg (‖x‖ - ‖y‖),
      mul_nonneg (mul_nonneg ha hb) (sq_nonneg (‖x‖ - ‖y‖))]
  nlinarith [h3, hab, mul_nonneg ha hb]

/-- **Jensen for the norm squared of a Bochner integral** on a probability space:
`‖∫ f‖² ≤ ∫ ‖f‖²`.  This is the pointwise estimate behind the `L²` contraction of
a Markov kernel; it is stronger than `‖∫ f‖ ≤ ∫ ‖f‖` and is what the quadratic
observable needs. -/
theorem norm_integral_sq_le_integral_norm_sq {μ : Measure α} [IsProbabilityMeasure μ]
    (f : α → ℂ) (hf : Integrable f μ) (hf2 : Integrable (fun y => ‖f y‖ ^ 2) μ) :
    ‖∫ y, f y ∂μ‖ ^ 2 ≤ ∫ y, ‖f y‖ ^ 2 ∂μ := by
  have hcont : ContinuousOn (fun z : ℂ => ‖z‖ ^ 2) Set.univ :=
    (continuous_norm.pow 2).continuousOn
  have h := convexOn_norm_sq.map_integral_le hcont isClosed_univ
    (ae_of_all _ fun _ => Set.mem_univ _) hf hf2
  simpa [Function.comp] using h

/-- **The pointwise Jensen estimate for a Markov kernel**:
`‖P f x‖² ≤ P (‖f‖²) x`.  The fiber `κ x` is a probability measure, so no
normalization hypothesis is needed beyond `IsMarkovKernel`. -/
theorem kernelOp_jensen {κ : Kernel α α} [IsMarkovKernel κ] {f : α → ℂ} {x : α}
    (hf : Integrable f (κ x)) (hf2 : Integrable (fun y => ‖f y‖ ^ 2) (κ x)) :
    ‖kernelOp κ f x‖ ^ 2 ≤ kernelOp κ (fun y => ‖f y‖ ^ 2) x :=
  norm_integral_sq_le_integral_norm_sq f hf hf2

/-! ## 3. The prior-refresh benchmark `Kernel.const α π` -/

/-- The integral action of the **prior-refresh benchmark** is independent of the
current state: it integrates against `π` and redraws. -/
theorem const_kernelOp (π : Measure α) {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] (f : α → E) (x : α) :
    kernelOp (Kernel.const α π) f x = ∫ y, f y ∂π := by
  simp [kernelOp]

/-- **The prior-refresh kernel is `π`-invariant.**  This is the stationary-law
clause of P0: redrawing from a probability `π` leaves `π` unchanged. -/
theorem const_invariant (π : Measure α) [IsProbabilityMeasure π] :
    Kernel.Invariant (Kernel.const α π) π := by
  rw [Kernel.Invariant]
  change (fun _ : α => π) ∘ₘ π = π
  rw [Measure.bind_const, measure_univ, one_smul]

/-- **The prior-refresh kernel is reversible** (detailed balance) with respect to
`π`: mass flowing from `A` to `B` equals mass flowing from `B` to `A`.  For the
constant kernel both flows are `π A * π B`. -/
theorem const_reversible (π : Measure α) [IsProbabilityMeasure π] :
    Kernel.IsReversible (Kernel.const α π) π := by
  intro A B hA hB
  simp [Kernel.const_apply, lintegral_const, mul_comm]

/-- The **`L²(π)` contraction** of the prior-refresh benchmark:
`∫ ‖P f‖² dπ ≤ ∫ ‖f‖² dπ`.  The left side is constant in `x`, so this is exactly
the Jensen estimate of §2 integrated against the probability `π`. -/
theorem const_l2_contraction (π : Measure α) [IsProbabilityMeasure π] {f : α → ℂ}
    (hf : Integrable f π) (hf2 : Integrable (fun y => ‖f y‖ ^ 2) π) :
    ∫ x, ‖kernelOp (Kernel.const α π) f x‖ ^ 2 ∂π ≤ ∫ x, ‖f x‖ ^ 2 ∂π := by
  have hJ := norm_integral_sq_le_integral_norm_sq f hf hf2
  calc
    ∫ x, ‖kernelOp (Kernel.const α π) f x‖ ^ 2 ∂π
        = ‖∫ y, f y ∂π‖ ^ 2 := by
          simp [const_kernelOp, integral_const, measure_univ]
    _ ≤ ∫ y, ‖f y‖ ^ 2 ∂π := hJ

/-- The prior-refresh kernel **preserves the mean**: `∫ P f dπ = ∫ f dπ`.  This is
the observable-side form of `π`-invariance. -/
theorem const_mean_preserved (π : Measure α) [IsProbabilityMeasure π] {f : α → ℂ}
    (hf : Integrable f π) :
    ∫ x, kernelOp (Kernel.const α π) f x ∂π = ∫ x, f x ∂π := by
  simp [const_kernelOp, integral_const, measure_univ]

/-- **The adjoint/density action of the benchmark is the operator itself.**  With
`P` the integral action, the `L²(π)` pairing `∫ f · P g dπ` is symmetric: the
operator is self-adjoint for the bilinear (unconjugated) pairing, which is the form
reversibility gives on a commutative observable algebra.  Equivalently the density
action fixes the constant density `1`, which is `kernelOp_one`.  This is the P0
clause that the observable and density orientations must not be conflated: for a
reversible kernel they agree. -/
theorem const_selfAdjoint_pairing (π : Measure α) [IsProbabilityMeasure π]
    {f g : α → ℂ} (hf : Integrable f π) (hg : Integrable g π) :
    ∫ x, f x * kernelOp (Kernel.const α π) g x ∂π
      = ∫ x, g x * kernelOp (Kernel.const α π) f x ∂π := by
  simp only [const_kernelOp]
  rw [integral_mul_const, integral_mul_const, mul_comm]

end BookProof.MCMC
