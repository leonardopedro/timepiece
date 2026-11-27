import Mathlib
import BookProof.Toolbox.ChapterStoneTheorem
import BookProof.Toolbox.ChapterEsaClosure

/-!
# The Stone bridge: from a selected self-adjoint extension to the unitary flow

`BookProof.ChapterStoneResolvent`–`BookProof.ChapterStoneTheorem` prove Stone's
theorem in full generality, but they consume the *bundled* structure
`UnboundedSelfAdjoint` (a dense domain, the operator, symmetry, and equality of
the adjoint domain with the domain).  The essential-self-adjointness /
Hashimoto-selection threads (Navier–Stokes, Yang–Mills) instead produce the
predicates `BookProof.EsaClosure.IsSelfAdjointExtension` and
`BookProof.YangMillsFriedrichs.IsPositiveSelfAdjointExtension` for an operator
`A : Dom →ₗ[ℂ] F`.

This module is the missing packaging step, plus the resulting flow statement:

* `dense_domain_of_isSelfAdjointExtension` — a self-adjoint extension of a
  densely defined operator has a dense domain;
* `isSelfAdjointOn_of_isSelfAdjointExtension` — the adjoint domain of such an
  extension is *equal* to its domain (both inclusions are conjuncts of the
  predicate, one via symmetry and one via the representation clause);
* `unboundedSelfAdjointOf` — the bundled `UnboundedSelfAdjoint` structure built
  from `IsSelfAdjointExtension`, with `unboundedSelfAdjointOf_domain` /
  `unboundedSelfAdjointOf_op`;
* `IsStoneFlow` — the flow package: `U 0 = 1`, the group law, isometry of each
  `U t`, and the Schrödinger equation `d/dt U t x = -i A (U t x)` on the domain;
* `isStoneFlow_stoneU` — Stone's group `e^{-itA}` is such a flow;
* `exists_stone_flow_of_selfAdjointExtension`, `exists_stone_flow_of_positive`
  and `exists_stone_flow_of_esa` — the three entry points: from a selected
  self-adjoint extension, from a positive (Friedrichs) one, and directly from
  essential self-adjointness of a symmetric core operator.

Everything is `sorry`-free and `axiom`-free.
-/

open Filter Topology
open scoped InnerProductSpace

namespace BookProof.StoneBridge

open BookProof.FarisLavine BookProof.EsaClosure BookProof.YangMillsFriedrichs
open BookProof.ChapterUnitaryTransport BookProof.ChapterStoneResolvent

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-! ## Packaging a selected extension -/

/-- The domain of a self-adjoint extension contains the original domain. -/
theorem le_of_isSelfAdjointExtension {D Dom : Submodule ℂ F} {Hc : D →ₗ[ℂ] F}
    {A : Dom →ₗ[ℂ] F} (h : IsSelfAdjointExtension Hc A) : (D : Set F) ⊆ (Dom : Set F) :=
  fun x hx => (h.1 ⟨x, hx⟩).choose

/-- **A self-adjoint extension of a densely defined operator is densely
defined.** -/
theorem dense_domain_of_isSelfAdjointExtension {D Dom : Submodule ℂ F} {Hc : D →ₗ[ℂ] F}
    {A : Dom →ₗ[ℂ] F} (hdense : Dense ((D : Submodule ℂ F) : Set F))
    (h : IsSelfAdjointExtension Hc A) : Dense ((Dom : Submodule ℂ F) : Set F) :=
  hdense.mono (le_of_isSelfAdjointExtension h)

/-- **The adjoint domain of a self-adjoint extension is exactly its domain.**
The inclusion `Dom ⊆ adjointDomain` is symmetry; the reverse inclusion is the
representation clause of `IsSelfAdjointExtension`. -/
theorem isSelfAdjointOn_of_isSelfAdjointExtension {D Dom : Submodule ℂ F} {Hc : D →ₗ[ℂ] F}
    {A : Dom →ₗ[ℂ] F} (h : IsSelfAdjointExtension Hc A) : IsSelfAdjointOn Dom A := by
  apply Set.Subset.antisymm
  · rintro phi ⟨eta, heta⟩
    exact (h.2.2 phi eta fun v => heta v).choose
  · intro phi hphi
    exact ⟨A ⟨phi, hphi⟩, fun psi => h.2.1 psi ⟨phi, hphi⟩⟩

/-- **The bundled unbounded self-adjoint operator** determined by a selected
self-adjoint extension of a densely defined operator. -/
noncomputable def unboundedSelfAdjointOf {D Dom : Submodule ℂ F} {Hc : D →ₗ[ℂ] F}
    {A : Dom →ₗ[ℂ] F} (hdense : Dense ((D : Submodule ℂ F) : Set F))
    (h : IsSelfAdjointExtension Hc A) : UnboundedSelfAdjoint F where
  domain := Dom
  op := A
  denseDomain := dense_domain_of_isSelfAdjointExtension hdense h
  symmetric := h.2.1
  selfAdjoint := isSelfAdjointOn_of_isSelfAdjointExtension h

@[simp] theorem unboundedSelfAdjointOf_domain {D Dom : Submodule ℂ F} {Hc : D →ₗ[ℂ] F}
    {A : Dom →ₗ[ℂ] F} (hdense : Dense ((D : Submodule ℂ F) : Set F))
    (h : IsSelfAdjointExtension Hc A) :
    (unboundedSelfAdjointOf hdense h).domain = Dom := rfl

@[simp] theorem unboundedSelfAdjointOf_op {D Dom : Submodule ℂ F} {Hc : D →ₗ[ℂ] F}
    {A : Dom →ₗ[ℂ] F} (hdense : Dense ((D : Submodule ℂ F) : Set F))
    (h : IsSelfAdjointExtension Hc A) :
    (unboundedSelfAdjointOf hdense h).op = A := rfl

/-! ## The flow package -/

/-- **A Stone flow for `T`**: a one-parameter family `U` of operators with
`U 0 = 1`, the group law, every `U t` isometric, and solving the Schrödinger
equation `d/dt (U t x) = -i T (U t x)` on the domain of `T` (in particular the
orbit of a domain vector stays in the domain). -/
def IsStoneFlow (T : UnboundedSelfAdjoint F) (U : ℝ → (F →L[ℂ] F)) : Prop :=
  U 0 = 1 ∧ (∀ s t, U (s + t) = U s * U t) ∧ (∀ t x, ‖U t x‖ = ‖x‖) ∧
    ∀ (x : F) (_hx : x ∈ T.domain) (t : ℝ), ∃ h : U t x ∈ T.domain,
      HasDerivAt (fun s : ℝ => U s x) ((-Complex.I) • T.op ⟨U t x, h⟩) t

variable [CompleteSpace F]

/-! ## Strong continuity of a Stone flow -/

/-- **A Stone flow is strongly continuous at the origin.**  On the domain this is continuity
of a differentiable curve; elsewhere it follows from the isometry and density. -/
theorem IsStoneFlow.tendsto_zero {T : UnboundedSelfAdjoint F} {U : ℝ → (F →L[ℂ] F)}
    (h : IsStoneFlow T U) (x : F) : Tendsto (fun t : ℝ => U t x) (𝓝 0) (𝓝 x) := by
  rw [Metric.tendsto_nhds_nhds]
  intro ε hε
  obtain ⟨z, hz, hxz⟩ := T.denseDomain.exists_dist_lt x (ε := ε / 3) (by linarith)
  obtain ⟨hzm, hzder⟩ := h.2.2.2 z hz 0
  have hcont : Tendsto (fun t : ℝ => U t z) (𝓝 0) (𝓝 z) := by
    have h0 : U 0 z = z := by rw [h.1]; rfl
    have hc := hzder.continuousAt
    change Tendsto (fun t : ℝ => U t z) (𝓝 0) (𝓝 (U 0 z)) at hc
    rwa [h0] at hc
  obtain ⟨δ, hδ, hδz⟩ := Metric.tendsto_nhds_nhds.1 hcont (ε / 3) (by linarith)
  refine ⟨δ, hδ, fun t ht => ?_⟩
  have hsplit : U t x - x = U t (x - z) + (U t z - z) + (z - x) := by
    rw [map_sub]
    abel
  have hzx : ‖z - x‖ = ‖x - z‖ := norm_sub_rev z x
  have hxz' : ‖x - z‖ < ε / 3 := by
    rw [dist_eq_norm] at hxz
    exact hxz
  have htz : ‖U t z - z‖ < ε / 3 := by
    have hd := hδz ht
    rwa [dist_eq_norm] at hd
  rw [dist_eq_norm]
  calc ‖U t x - x‖
      ≤ ‖U t (x - z)‖ + ‖U t z - z‖ + ‖z - x‖ := by
        rw [hsplit]
        exact (norm_add_le _ _).trans (by gcongr; exact norm_add_le _ _)
    _ = ‖x - z‖ + ‖U t z - z‖ + ‖z - x‖ := by rw [h.2.2.1 t (x - z)]
    _ < ε := by rw [hzx]; linarith

/-- **A Stone flow is strongly continuous in time on every vector.** -/
theorem IsStoneFlow.continuous {T : UnboundedSelfAdjoint F} {U : ℝ → (F →L[ℂ] F)}
    (h : IsStoneFlow T U) (x : F) : Continuous (fun t : ℝ => U t x) := by
  refine continuous_iff_continuousAt.2 fun t₀ => ?_
  have h1 : Tendsto (fun t : ℝ => t - t₀) (𝓝 t₀) (𝓝 0) := by
    simpa using (continuous_sub_right t₀).tendsto t₀
  have h2 : Tendsto (fun t : ℝ => U (t - t₀) x) (𝓝 t₀) (𝓝 x) :=
    (h.tendsto_zero x).comp h1
  have h3 : Tendsto (fun t : ℝ => U t₀ (U (t - t₀) x)) (𝓝 t₀) (𝓝 (U t₀ x)) :=
    ((U t₀).continuous.tendsto x).comp h2
  have heq : (fun t : ℝ => U t₀ (U (t - t₀) x)) = fun t : ℝ => U t x := by
    funext t
    rw [← ContinuousLinearMap.mul_apply, ← h.2.1 t₀ (t - t₀)]
    congr 1
    ring
  rwa [heq] at h3

/-! ## Uniqueness from a dense core -/

/-- **A Stone flow is determined by its generator on a dense submodule of the domain.**
If an isometric one-parameter group solves the Schrödinger equation with generator `T` on a
dense `D ≤ T.domain`, it is `e^{-itT}`. -/
theorem eq_stoneU_of_dense_core {T : UnboundedSelfAdjoint F} {D : Submodule ℂ F}
    (hDense : Dense (D : Set F)) (hD : D ≤ T.domain) {U : ℝ → (F →L[ℂ] F)}
    (hU0 : U 0 = 1) (hUadd : ∀ s t, U (s + t) = U s * U t)
    (hUnorm : ∀ t x, ‖U t x‖ = ‖x‖)
    (hUderiv : ∀ (x : D) (t : ℝ), ∃ h : U t (x : F) ∈ T.domain,
      HasDerivAt (fun s : ℝ => U s (x : F)) ((-Complex.I) • T.op ⟨U t (x : F), h⟩) t) :
    ∀ t, U t = T.stoneU t := by
  intro t
  have key : ∀ x ∈ (D : Set F), U t x = T.stoneU t x := by
    intro x hx
    obtain ⟨hUmem, -⟩ := hUderiv ⟨x, hx⟩ t
    -- the pairing against every domain vector is conserved
    have hpair : ∀ y ∈ (T.domain : Set F), inner ℂ (T.stoneU t y) (U t x)
        = inner ℂ y x := by
      intro y hy
      set y' : T.domain := ⟨y, hy⟩ with hy'
      have hder : ∀ s : ℝ,
          HasDerivAt (fun r : ℝ => inner ℂ (T.stoneU r y) (U r x)) 0 s := by
        intro s
        obtain ⟨husm, huder⟩ := hUderiv ⟨x, hx⟩ s
        have h1 : HasDerivAt (fun r : ℝ => T.stoneU r y)
            (T.stoneU s ((-Complex.I) • T.op y')) s := T.hasDerivAt_stoneU y' s
        have h2 : HasDerivAt (fun r : ℝ => U r x)
            ((-Complex.I) • T.op ⟨U s x, husm⟩) s := huder
        have h := HasDerivAt.inner ℂ h1 h2
        have hsym := T.symmetric ⟨T.stoneU s y, T.stoneU_mem_domain s y'⟩
          ⟨U s x, husm⟩
        have hop : T.stoneU s (T.op y')
            = T.op ⟨T.stoneU s y, T.stoneU_mem_domain s y'⟩ :=
          (T.stoneU_op s y').symm
        have hzero : (⟪T.stoneU s y, (-Complex.I) • T.op ⟨U s x, husm⟩⟫_ℂ
            + ⟪T.stoneU s ((-Complex.I) • T.op y'), U s x⟫_ℂ) = 0 := by
          rw [inner_smul_right, map_smul, hop, inner_smul_left, Complex.conj_neg_I, hsym]
          ring
        rw [hzero] at h
        simpa using h
      have hconst := is_const_of_deriv_eq_zero
        (f := fun r : ℝ => inner ℂ (T.stoneU r y) (U r x))
        (fun s => (hder s).differentiableAt) (fun s => (hder s).deriv) t 0
      have h0 : inner ℂ (T.stoneU 0 y) (U 0 x) = inner ℂ y x := by
        rw [T.stoneU_zero, hU0]
        simp
      rwa [h0] at hconst
    -- rewrite the conserved pairing through the inverse flow
    have hz : ∀ z ∈ (T.domain : Set F),
        inner ℂ z (U t x) = inner ℂ z (T.stoneU t x) := by
      intro z hzdom
      set z' : T.domain := ⟨z, hzdom⟩ with hz'
      have h1 := hpair (T.stoneU (-t) z) (T.stoneU_mem_domain (-t) z')
      rw [T.stoneU_apply_stoneU, show t + -t = 0 by ring, T.stoneU_zero] at h1
      simp only [ContinuousLinearMap.one_apply] at h1
      have hx0 : T.stoneU (-t) (T.stoneU t x) = x := by
        rw [T.stoneU_apply_stoneU]
        show T.stoneU (-t + t) x = x
        rw [show -t + t = 0 by ring, T.stoneU_zero]
        rfl
      have hunit : inner ℂ (T.stoneU (-t) z) x = inner ℂ z (T.stoneU t x) := by
        conv_lhs => rw [← hx0]
        rw [T.inner_stoneU_map_map]
      rw [hunit] at h1
      exact h1
    refine sub_eq_zero.mp (T.denseDomain.eq_zero_of_inner_right fun v => ?_)
    have := hz (v : F) v.2
    rw [inner_sub_right, this, sub_self]
  exact Continuous.ext_on hDense (U t).continuous (T.stoneU t).continuous key

/-- **Stone's group is a Stone flow.** -/
theorem isStoneFlow_stoneU (T : UnboundedSelfAdjoint F) : IsStoneFlow T T.stoneU := by
  refine ⟨T.stoneU_zero, ?_, ?_, ?_⟩
  · intro s t
    exact T.stoneU_add s t
  · intro t x
    exact T.norm_stoneU_apply t x
  · intro x hx t
    exact ⟨T.stoneU_mem_domain t ⟨x, hx⟩, T.hasDerivAt_stoneU_op ⟨x, hx⟩ t⟩

/-- **The bridge, first entry point.**  A selected self-adjoint extension of a
densely defined operator generates a complete unitary flow solving the
Schrödinger equation, and the flow's generator extends the original operator. -/
theorem exists_stone_flow_of_selfAdjointExtension {D Dom : Submodule ℂ F} {Hc : D →ₗ[ℂ] F}
    {A : Dom →ₗ[ℂ] F} (hdense : Dense ((D : Submodule ℂ F) : Set F))
    (h : IsSelfAdjointExtension Hc A) :
    ∃ (T : UnboundedSelfAdjoint F) (U : ℝ → (F →L[ℂ] F)),
      T.domain = Dom ∧ HEq T.op A ∧ IsStoneFlow T U :=
  ⟨unboundedSelfAdjointOf hdense h, _, rfl, HEq.rfl,
    isStoneFlow_stoneU (unboundedSelfAdjointOf hdense h)⟩

/-- **The bridge, positive (Friedrichs) entry point.** -/
theorem exists_stone_flow_of_positive {D Dom : Submodule ℂ F} {Hc : D →ₗ[ℂ] F}
    {A : Dom →ₗ[ℂ] F} (hdense : Dense ((D : Submodule ℂ F) : Set F))
    (h : IsPositiveSelfAdjointExtension Hc A) :
    ∃ (T : UnboundedSelfAdjoint F) (U : ℝ → (F →L[ℂ] F)),
      T.domain = Dom ∧ HEq T.op A ∧ IsStoneFlow T U :=
  exists_stone_flow_of_selfAdjointExtension hdense (isSelfAdjointExtension_of_positive h)

/-- **The bridge, essential-self-adjointness entry point.**  An essentially
self-adjoint symmetric operator on a dense core generates a complete unitary
flow: the flow of its (unique) self-adjoint extension. -/
theorem exists_stone_flow_of_esa {D : Submodule ℂ F} (Hc : D →ₗ[ℂ] F)
    (hdense : Dense ((D : Submodule ℂ F) : Set F)) (hsym : SymmetricOn D Hc)
    (hesa : EssentiallySelfAdjointOn D Hc) :
    ∃ (T : UnboundedSelfAdjoint F) (U : ℝ → (F →L[ℂ] F)),
      IsSelfAdjointExtension Hc T.op ∧ IsStoneFlow T U := by
  obtain ⟨Dom, A, hA⟩ := exists_isSelfAdjointExtension_of_esa Hc hdense hsym hesa
  exact ⟨unboundedSelfAdjointOf hdense hA, _, hA,
    isStoneFlow_stoneU (unboundedSelfAdjointOf hdense hA)⟩

end BookProof.StoneBridge
