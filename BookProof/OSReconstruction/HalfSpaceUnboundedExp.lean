import Mathlib
import BookProof.OSReconstruction.HalfSpaceHilbert
import BookProof.OSReconstruction.L2Multiplier

/-!
# The unbounded exponential `e^{−τM_f}` on the half-space carrier

Plan: `cftproof.md`, **E3**.  `HalfSpaceExponential` constructs `e^{−τH}` for a **bounded**
`H : Hhalf Λ →L[ℝ] Hhalf Λ`, and `HalfSpaceExpIdentification` identifies it with the abstract
semigroup.  The physical Hamiltonian is unbounded, so this module handles that case in the
representation the corpus already uses for it — the **spectral/multiplier model** of
`L2Multiplier`, `MultiplierGenerator` and `MultiplierSelfAdjoint`.

The exponential of an unbounded operator is not `NormedSpace.exp`; it is the multiplier
`e^{−τ f}`, and `L2Multiplier.expFlow` already provides it on `L²(ν)` with the semigroup law
(`expFlow_comp`), contractivity (`expFlow_contractive`) and the generator limit
(`tendsto_expFlow_slope`).  What this module adds is the *half-space* side: an isometric
identification `e : Hhalf Λ ≃ₗᵢ[ℝ] L²(ν)` turns the multiplier flow into a flow on `Hhalf`, and the
generator is read off there.

## Contents

* `HsMulModel` — the datum: a measure `ν`, a measurable nonnegative density `f`, and an isometric
  **equivalence** `e : Hhalf Λ ≃ₗᵢ[ℝ] L²(ν)` (so the half-space carrier *is* the multiplier
  representation, not merely a subspace of it).
* `HsMulModel.flow` — the family `P(τ) = e⁻¹ ∘ (multiplication by e^{−τ f}) ∘ e` on `Hhalf`.  It is
  constructed, not assumed; the bounded exponential of `HalfSpaceExponential` is the special case of
  a bounded `f`.
* `HsMulModel.flow_zero`, `flow_comp`, `flow_contractive` — `P(0) = I`, `P(s+t) = P(s)P(t)`,
  `‖P(τ)z‖ ≤ ‖z‖` for `τ ≥ 0`, transported from `expFlow` along the isometry.
* `HsMulModel.flow_tendsto` — **strong continuity at `0⁺`** on the natural domain.
* `HsMulModel.opValue` — the unbounded Hamiltonian applied to a vector of its natural domain: the
  unique `w` with `e w = −f · e z`.  Its domain is `{z | f · e z ∈ L²(ν)}`.
* `HsMulModel.hasDerivWithinAt_flow` — **the generator statement**: for every `z` in that domain,
  `d/dτ P(τ)z = −M_f z` at `0⁺`.  This is the unbounded analogue of
  `HalfSpaceExponential.hsExpOp_hasDerivWithinAt_zero`.
* `HsMulModel.mem_domain_of_bounded` — when `f` is essentially bounded, the domain is all of
  `Hhalf`, recovering the bounded case.

## Boundary

The operator is genuinely unbounded: its domain is the set of `z` with `f · e z ∈ L²(ν)`, and the
operator is *maximally* defined by that condition (one cannot evaluate it elsewhere).  What is
**not** proved here, and is the spectral-theorem content of the multiplier model, is (a) that this
domain is
dense in `Hhalf` for unbounded `f` — proved below only for essentially bounded `f` — and (b) that
the operator is self-adjoint.  Those are exactly the two facts `MultiplierSelfAdjoint.MulModel`
consumes from its own datum (`hdense : DenseRange U`, plus the positivity of `f`); they are not
derived from `ν` here.  Symmetry of the operator, on the other hand, is *not* assumed: it is the
pointwise reality of `f`, and needs no hypothesis.
-/

noncomputable section

open MeasureTheory Filter Set
open scoped Topology ENNReal

namespace BookProof.OSReconstruction

variable {Λ : HalfSpaceState}

/-- **A multiplier model for the half-space carrier.**  The measure, the density `f ≥ 0` whose
multiplication is the (unbounded) Hamiltonian, and the isometric identification of `Hhalf Λ` with
`L²(ν)`.  Being an equivalence, `e` carries both directions continuously, so every flow transported
along it is again a bounded operator on `Hhalf Λ`. -/
structure HsMulModel (Λ : HalfSpaceState) (X : Type*) [MeasurableSpace X] where
  /-- The reference measure. -/
  ν : Measure X
  /-- The Hamiltonian density. -/
  f : X → ℝ
  /-- It is measurable. -/
  hf : Measurable f
  /-- It is nonnegative a.e., so `e^{−τ f}` is a contraction for `τ ≥ 0`. -/
  hpos : ∀ᵐ x ∂ν, 0 ≤ f x
  /-- The isometric identification of the half-space carrier with `L²(ν)`. -/
  e : Hhalf Λ ≃ₗᵢ[ℝ] Lp ℝ 2 ν

namespace HsMulModel

variable {X : Type*} [MeasurableSpace X] (M : HsMulModel Λ X)

/-! ## The unbounded Hamiltonian's natural domain -/

/-- **The natural domain of the unbounded Hamiltonian**: the vectors whose `f`-multiple is square
integrable in the multiplier representation.  This is a submodule because membership is
`MemLp` of a pointwise-linear expression. -/
def domain : Submodule ℝ (Hhalf Λ) where
  carrier := {z | MemLp (fun x => M.f x * (M.e z : X → ℝ) x) 2 M.ν}
  zero_mem' := by
    have hzero : (fun _ : X => (0 : ℝ)) =ᵐ[M.ν] fun x => M.f x * (M.e 0 : X → ℝ) x := by
      filter_upwards [Lp.coeFn_zero ℝ 2 M.ν] with x hx
      rw [map_zero, hx]
      simp
    exact MemLp.zero.ae_eq hzero
  add_mem' := by
    intro z w hz hw
    have hcoe : ((M.e (z + w) : Lp ℝ 2 M.ν) : X → ℝ) =ᵐ[M.ν]
        ((M.e z : Lp ℝ 2 M.ν) : X → ℝ) + ((M.e w : Lp ℝ 2 M.ν) : X → ℝ) := by
      rw [map_add]
      exact Lp.coeFn_add _ _
    refine (hz.add hw).ae_eq ?_
    filter_upwards [hcoe] with x hx
    simp only [Pi.add_apply, hx]
    ring
  smul_mem' := by
    intro c z hz
    have hcoe : ((M.e (c • z) : Lp ℝ 2 M.ν) : X → ℝ) =ᵐ[M.ν]
        c • ((M.e z : Lp ℝ 2 M.ν) : X → ℝ) := by
      rw [map_smul]
      exact Lp.coeFn_smul c _
    refine (hz.const_mul c).ae_eq ?_
    filter_upwards [hcoe] with x hx
    rw [hx]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring

/-- **The unbounded Hamiltonian applied to a domain vector**: the unique `w` with
`e w = −f · e z`.  Existence is what the domain says (`f · e z ∈ L²`) and uniqueness is injectivity
of the isometry. -/
def opValue (z : Hhalf Λ)
    (hz : MemLp (fun x => M.f x * (M.e z : X → ℝ) x) 2 M.ν) : Hhalf Λ :=
  M.e.symm (-(hz.toLp (fun x => M.f x * (M.e z : X → ℝ) x)))

/-- **`opValue` is the multiplication by `−f`** in the multiplier representation. -/
theorem e_opValue (z : Hhalf Λ)
    (hz : MemLp (fun x => M.f x * (M.e z : X → ℝ) x) 2 M.ν) :
    M.e (M.opValue z hz) = -(hz.toLp (fun x => M.f x * (M.e z : X → ℝ) x)) := by
  simp [opValue]

/-- `opValue` depends only on the vector, not on the membership proof. -/
theorem opValue_congr {z : Hhalf Λ}
    {h₁ h₂ : MemLp (fun x => M.f x * (M.e z : X → ℝ) x) 2 M.ν} :
    M.opValue z h₁ = M.opValue z h₂ := by
  have h : h₁.toLp (fun x => M.f x * (M.e z : X → ℝ) x)
      = h₂.toLp (fun x => M.f x * (M.e z : X → ℝ) x) := rfl
  simp only [opValue, h]

/-! ## The flow `P(τ) = e⁻¹ ∘ e^{−τ f} ∘ e` -/

/-- **The exponential of the unbounded Hamiltonian on `Hhalf Λ`**: the multiplier flow `e^{−τ f}`,
conjugated by the isometric identification. -/
def flow (τ : ℝ) : Hhalf Λ →L[ℝ] Hhalf Λ :=
  (M.e.symm.toContinuousLinearEquiv : Lp ℝ 2 M.ν →L[ℝ] Hhalf Λ).comp
    ((expFlow M.f M.hf M.hpos τ).comp
      (M.e.toContinuousLinearEquiv : Hhalf Λ →L[ℝ] Lp ℝ 2 M.ν))

/-- The flow acts through the multiplier representation. -/
theorem flow_apply (τ : ℝ) (z : Hhalf Λ) :
    M.flow τ z = M.e.symm (expFlow M.f M.hf M.hpos τ (M.e z)) :=
  rfl

/-- **`P(0) = I`.** -/
theorem flow_zero : M.flow 0 = 1 := by
  refine ContinuousLinearMap.ext fun z => ?_
  rw [flow_apply, expFlow_zero]
  simp

/-- **`P(s + t) = P(s)P(t)`** for `s, t ≥ 0`, from `expFlow_comp`. -/
theorem flow_comp {s t : ℝ} (hs : 0 ≤ s) (ht : 0 ≤ t) (z : Hhalf Λ) :
    M.flow s (M.flow t z) = M.flow (s + t) z := by
  simp only [flow_apply]
  rw [LinearIsometryEquiv.apply_symm_apply, expFlow_comp M.hf M.hpos hs ht]

/-- **The flow is a contraction**: the isometry transfers `expFlow_contractive` unchanged. -/
theorem flow_contractive {τ : ℝ} (hτ : 0 ≤ τ) (z : Hhalf Λ) :
    ‖M.flow τ z‖ ≤ ‖z‖ := by
  rw [flow_apply, LinearIsometryEquiv.norm_map]
  calc ‖expFlow M.f M.hf M.hpos τ (M.e z)‖ ≤ ‖M.e z‖ :=
        expFlow_contractive M.hf M.hpos hτ _
    _ = ‖z‖ := LinearIsometryEquiv.norm_map M.e z

/-- **Strong continuity at `0⁺`**, on the natural domain — the hypothesis of
`tendsto_expFlow_zero`, which is the only place the corpus needs `f · e z ∈ L²(ν)`. -/
theorem flow_tendsto {z : Hhalf Λ}
    (hz : MemLp (fun x => M.f x * (M.e z : X → ℝ) x) 2 M.ν) :
    Tendsto (fun τ : ℝ => M.flow τ z) (𝓝[>] 0) (𝓝 z) := by
  have h := tendsto_expFlow_zero (ν := M.ν) (Lp.memLp (M.e z)) M.hf M.hpos hz
  have h' : Tendsto
      (fun τ : ℝ => M.e.symm (expFlow M.f M.hf M.hpos τ
        (MemLp.toLp (M.e z : X → ℝ) (Lp.memLp (M.e z)))))
      (𝓝[>] 0) (𝓝 (M.e.symm (MemLp.toLp (M.e z : X → ℝ) (Lp.memLp (M.e z))))) :=
    M.e.symm.toContinuousLinearEquiv.continuous.continuousAt.tendsto.comp h
  simpa [flow_apply] using h'

/-! ## The generator -/

/-- **The unbounded generator statement**: for every vector of the natural domain, the orbit has
right derivative `−M_f z` at `0⁺`.  This is the unbounded analogue of
`hsExpOp_hasDerivWithinAt_zero`: `NormedSpace.exp` is replaced by the multiplier flow, and `H` by
the maximally defined multiplication operator. -/
theorem hasDerivWithinAt_flow {z : Hhalf Λ}
    (hz : MemLp (fun x => M.f x * (M.e z : X → ℝ) x) 2 M.ν) :
    HasDerivWithinAt (fun τ : ℝ => M.flow τ z) (M.opValue z hz) (Ioi 0) 0 := by
  set L : Lp ℝ 2 M.ν := -(hz.toLp (fun x => M.f x * (M.e z : X → ℝ) x)) with hL
  have hslope : Tendsto
      (fun τ : ℝ => τ⁻¹ • (expFlow M.f M.hf M.hpos τ
        (MemLp.toLp (M.e z : X → ℝ) (Lp.memLp (M.e z)))
          - MemLp.toLp (M.e z : X → ℝ) (Lp.memLp (M.e z)))) (𝓝[>] 0) (𝓝 L) := by
    rw [hL]
    exact tendsto_expFlow_slope (Lp.memLp (M.e z)) M.hf M.hpos hz
  have hmap := (M.e.symm.toContinuousLinearEquiv.continuous.continuousAt.tendsto.comp hslope)
  have hP : ∀ τ : ℝ, M.flow τ z - z
      = M.e.symm (expFlow M.f M.hf M.hpos τ (M.e z) - M.e z) := by
    intro τ
    rw [flow_apply, map_sub, LinearIsometryEquiv.symm_apply_apply]
  refine (hasDerivWithinAt_iff_tendsto_slope).2 ?_
  rw [show Ioi (0 : ℝ) \ {0} = Ioi 0 from diff_singleton_eq_self (by simp)]
  refine hmap.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with τ hτ
  rw [Function.comp_apply, slope_def_module, sub_zero, flow_zero,
    ContinuousLinearMap.one_apply, map_smul]
  congr 1
  rw [flow_apply]
  simp

/-! ## The essentially bounded case -/

/-- **When `f` is essentially bounded the domain is everything**, so the unbounded operator is
bounded and this module reduces to the situation of `HalfSpaceExponential`. -/
theorem mem_domain_of_bounded {C : ℝ} (hC0 : 0 ≤ C)
    (hC : ∀ᵐ x ∂M.ν, |M.f x| ≤ C) (z : Hhalf Λ) : z ∈ M.domain :=
  memLp_mul_of_abs_bound (Lp.memLp (M.e z)) M.hf hC0 hC

end HsMulModel

end BookProof.OSReconstruction
