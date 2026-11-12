import Mathlib
import BookProof.OSReconstruction.FockIntertwining
import BookProof.OSReconstruction.HilbertSpace

/-!
# A concrete `OsFockBridge`: the one-particle sector of the point-evaluation state

Plan: `cftproof.md`, **E4/B2** — "construct an isometry onto its physical cyclic space
`U : ℋ_OS → ℋ_ref` … align the OS cyclic vector with the reference prior and intertwine the heat
semigroups".  `OSReconstruction.FockIntertwining` *states* that condition as the bundle
`OsFockBridge` and proves its consequences, but every inhabitant of the bundle so far takes `U` as
an input (`OsFockBridge.id` is the identity, `osFockBridgeOfMulModel` assumes `U`, its density and
the intertwining).  B2 therefore remained conditional, exactly as the module notes say.

This module builds one **whose `U` is constructed**, and the reason it can is the state: the
point-evaluation state.

## 1. The state

`evalZeroState` is the functional `ω F = F 0` at the zero configuration.  It is a
`LinearFunctional` (additive and homogeneous for every observable, no integrability needed) and
θ-invariant because `fieldReflection` fixes `0`; it is reflection positive because

`⟨F,F⟩ = ω(θF · F) = θF(0) · F(0) = F(0)² ≥ 0`   (`evalZero_osBilin`).

So the OS form of this state is **rank one**: `⟨F,G⟩ = F(0) · G(0)`.

## 2. Its OS Hilbert space is the one-particle line

Because the form factorizes, the radical is the kernel of evaluation at `0`
(`evalZero_mem_radical_iff`), and evaluation descends to the quotient `𝔄/𝔑` as a linear map
`evalQuot` that is an **isometry onto `ℝ`** (`evalQuot_norm`): `‖[F]‖ = √(F(0)²) = |F(0)|`.  It is
onto (`evalQuot_surjective`), so `𝔄/𝔑 ≃ₗᵢ ℝ`.  Extending along the dense embedding by
`LinearMap.extendOfNorm` gives an isometry `evalHphysU : ℋ →ₗᵢ[ℝ] ℝ`
(`evalHphysMap_norm`) whose range is all of
`ℝ` (`evalHphysU_denseRange`): **the whole OS Hilbert space of this state is the one-particle
sector**, the line on which `F` below lives.

## 3. The bridge

`oneParticleBridge P : OsFockBridge ℝ P (oneParticleFlow P)` for any transfer semigroup
`P : ℝ → ℋ →L[ℝ] ℋ`.  All three fields are proved:

* `U := evalHphysU`, constructed above (no hypothesis);
* `dense_range := evalHphysU_denseRange`, from surjectivity;
* `intertwines`: on `ℋ ≃ ℝ` every vector is `x = U x • Ω`, so linearity gives
  `U (P τ x) = U x • U (P τ Ω) = c τ · U x`, i.e. the Fock-side flow is the **scalar flow**
  `Q τ = c τ • id` with `c τ = U (P τ Ω)` (`oneParticleScalar`).

The consequences of the bundle become numerical identities for this model: the two-point function is
`c τ · ‖x‖²` (`oneParticleBridge_twoPoint`) and the semigroup acts by the scalar
`|c τ|` (`oneParticleBridge_norm`).

## Boundary

The instance is non-conditional in `U`, but the **model is degenerate**: the point-evaluation state
is a character of the observable algebra, so its OS form is rank one and its Hilbert space is the
one-particle line.  That is why an isometry can be written down at all: there is nothing
multi-particle to identify.  `F = ℝ` is the one-particle sector of the Fock space over a
one-dimensional one-particle space, and `oneParticleFlow` is `dΓ` of the one-particle operator
`c τ • id` on it; it is *not* the manuscript's inner `h_F`, and no complex structure, no spatial
translation and no identification with `ℱ_out` is built.  The transfer semigroup `P` is an input,
as it is for every bridge.  B2 in general — a unitary `ℋ_OS → ℋ_ref ⊆ ℱ_out` for the interacting
theory, intertwining the smeared fields and the actual heat semigroup — remains open, and this
module does not narrow it beyond recording that the bundle is satisfiable by a constructed map.
-/

namespace BookProof.OSReconstruction

open BookProof.ReflectionPositivity
open scoped RealInnerProductSpace

noncomputable section

/-! ## 1. The point-evaluation state and its rank-one OS form -/

/-- **The point-evaluation functional** `ω F = F 0` at the zero configuration, as a
`LinearFunctional`: additive and homogeneous for *every* observable, and θ-invariant because the
field reflection fixes `0`. -/
def evalZeroLF : LinearFunctional where
  toFun F := F 0
  map_add _ _ := rfl
  map_smul _ _ := rfl
  map_theta F := by
    change F (fieldReflection 0) = F 0
    rw [map_zero]

/-- **The OS form of the point-evaluation state factorizes**: `⟨F,G⟩ = F(0)·G(0)`. -/
theorem evalZero_osBilin (F G : Observable) : osBilin evalZeroLF F G = F 0 * G 0 := by
  simp [osBilin, osForm, evalZeroLF, thetaObs_apply, Pi.mul_apply, map_zero]

/-- **The point-evaluation state is reflection positive**, because its OS form is a square. -/
theorem evalZero_reflectionPositive : IsReflectionPositive fun F : Observable => F 0 := by
  intro F
  change 0 ≤ osBilin evalZeroLF F F
  rw [evalZero_osBilin]
  nlinarith [sq_nonneg (F 0)]

/-- **The point-evaluation state**: a concrete `OSState` of the full observable algebra. -/
def evalZeroState : OSState where
  ω := evalZeroLF
  pos := evalZero_reflectionPositive

/-! ## 2. Its radical is the kernel of evaluation, and the quotient is the line -/

/-- The radical of the point-evaluation form is exactly the observables vanishing at `0`. -/
theorem evalZero_mem_radical_iff {F : Observable} :
    F ∈ Radical evalZeroLF ↔ F 0 = 0 := by
  constructor
  · intro h
    have h1 := h 1
    simpa [evalZero_osBilin] using h1
  · intro h G
    rw [evalZero_osBilin, h, zero_mul]

/-- Evaluation at `0`, as a linear map on the observables. -/
def evalZeroLM : Observable →ₗ[ℝ] ℝ where
  toFun := evalZeroLF
  map_add' := evalZeroLF.map_add
  map_smul' := evalZeroLF.map_smul

/-- Evaluation at `0` descends to the OS quotient. -/
def evalQuot : PhysSpace evalZeroState →ₗ[ℝ] ℝ :=
  (Radical evalZeroLF).liftQ evalZeroLM (fun F hF => by
    rw [LinearMap.mem_ker]
    exact evalZero_mem_radical_iff.1 hF)

theorem evalQuot_apply_mk (F : Observable) :
    evalQuot (Submodule.Quotient.mk F) = F 0 :=
  Submodule.liftQ_apply _ _ _

/-- **`evalQuot` is an isometry**: on the quotient the OS norm is `|F(0)|`. -/
theorem evalQuot_norm (x : PhysSpace evalZeroState) : ‖evalQuot x‖ = ‖x‖ := by
  refine Submodule.Quotient.induction_on _ x fun F => ?_
  rw [evalQuot_apply_mk, physNorm_mk]
  change ‖F 0‖ = Real.sqrt (osBilin evalZeroLF F F)
  rw [evalZero_osBilin, Real.norm_eq_abs, ← pow_two, Real.sqrt_sq_eq_abs]

/-- **Evaluation is an isometry of the OS space into the one-particle line.** -/
def evalQuotIsometry : PhysSpace evalZeroState →ₗᵢ[ℝ] ℝ where
  toLinearMap := evalQuot
  norm_map' := evalQuot_norm

/-- It is onto: `[1]` evaluates to `1`, so every real number is `λ • [1]`. -/
theorem evalQuot_surjective : Function.Surjective evalQuot := by
  intro y
  refine ⟨y • Submodule.Quotient.mk (1 : Observable), ?_⟩
  rw [map_smul, evalQuot_apply_mk, Pi.one_apply, smul_eq_mul, mul_one]

/-! ## 3. The completion: `ℋ ≃ₗᵢ ℝ`, constructed -/

theorem norm_physCoe (x : PhysSpace evalZeroState) : ‖physCoe evalZeroState x‖ = ‖x‖ :=
  UniformSpace.Completion.norm_coe x

/-- The isometry extended to the completion `ℋ`, by `LinearMap.extendOfNorm`. -/
def evalHphysMap : Hphys evalZeroState →L[ℝ] ℝ :=
  LinearMap.extendOfNorm evalQuot (physCoe evalZeroState)

theorem evalHphysMap_coe (x : PhysSpace evalZeroState) :
    evalHphysMap (physCoe evalZeroState x) = evalQuot x :=
  LinearMap.extendOfNorm_eq (f := evalQuot) (e := physCoe evalZeroState)
    (by simpa [physCoe] using denseRange_physCoe evalZeroState)
    ⟨1, fun y => by rw [evalQuot_norm, norm_physCoe, one_mul]⟩ x

/-- **The extended map is still an isometry**: it agrees with `evalQuot` on the dense subspace, and
both sides of `‖evalHphysMap z‖ = ‖z‖` are continuous. -/
theorem evalHphysMap_norm (z : Hphys evalZeroState) : ‖evalHphysMap z‖ = ‖z‖ := by
  have hclosed : IsClosed {z : Hphys evalZeroState | ‖evalHphysMap z‖ = ‖z‖} :=
    isClosed_eq (continuous_norm.comp evalHphysMap.continuous) continuous_norm
  have hsub : Set.range (physCoe evalZeroState) ⊆ {z | ‖evalHphysMap z‖ = ‖z‖} := by
    rintro _ ⟨x, rfl⟩
    change ‖evalHphysMap (physCoe evalZeroState x)‖ = ‖physCoe evalZeroState x‖
    rw [evalHphysMap_coe, evalQuot_norm, norm_physCoe]
  have hd : closure (Set.range (physCoe evalZeroState)) = Set.univ :=
    DenseRange.closure_range (denseRange_physCoe evalZeroState)
  have hcl := hclosed.closure_subset_iff.2 hsub
  rw [hd] at hcl
  exact hcl trivial

/-- **The OS Hilbert space of the point-evaluation state, as an isometry into the one-particle
line.**  This is the `U` of the bridge, and it is constructed, not assumed. -/
def evalHphysU : Hphys evalZeroState →ₗᵢ[ℝ] ℝ where
  toLinearMap := evalHphysMap.toLinearMap
  norm_map' := evalHphysMap_norm

theorem evalHphysU_apply_coe (x : PhysSpace evalZeroState) :
    evalHphysU (physCoe evalZeroState x) = evalQuot x :=
  evalHphysMap_coe x

/-- The vacuum class `Ω = [1]` of this state, in the completion. -/
def evalVacuum : Hphys evalZeroState :=
  physCoe evalZeroState (Submodule.Quotient.mk (1 : Observable))

theorem evalHphysU_vacuum : evalHphysU evalVacuum = 1 := by
  rw [evalVacuum, evalHphysU_apply_coe, evalQuot_apply_mk, Pi.one_apply]

/-- **The identification is onto**: `λ • Ω` maps to `λ`. -/
theorem evalHphysU_surjective : Function.Surjective evalHphysU := by
  intro y
  refine ⟨y • evalVacuum, ?_⟩
  rw [map_smul, evalHphysU_vacuum, smul_eq_mul, mul_one]

theorem evalHphysU_denseRange : DenseRange evalHphysU := by
  rw [DenseRange, evalHphysU_surjective.range_eq]
  exact dense_univ

/-! ## 4. The one-particle bridge -/

/-- **The scalar of the transfer semigroup** on the one-particle sector: `U (P τ Ω)`.  On a
one-dimensional sector every vector is `U x • Ω`, so this number determines `P τ` completely. -/
def oneParticleScalar (P : ℝ → Hphys evalZeroState →L[ℝ] Hphys evalZeroState) (τ : ℝ) : ℝ :=
  evalHphysU (P τ evalVacuum)

/-- **The Fock-side flow** on the one-particle sector: multiplication by `oneParticleScalar`.  It is
`dΓ` of the one-particle operator `c τ • id`. -/
def oneParticleFlow (P : ℝ → Hphys evalZeroState →L[ℝ] Hphys evalZeroState) :
    ℝ → ℝ →L[ℝ] ℝ :=
  fun τ => oneParticleScalar P τ • ContinuousLinearMap.id ℝ ℝ

/-- **A concrete `OsFockBridge` whose `U` is constructed.**  `F` is `ℝ`, the one-particle sector of
the Fock space over a one-dimensional one-particle space; the OS side is the point-evaluation
state, whose whole Hilbert space is that sector.  No field of the bundle is assumed. -/
def oneParticleBridge (P : ℝ → Hphys evalZeroState →L[ℝ] Hphys evalZeroState) :
    OsFockBridge ℝ P (oneParticleFlow P) where
  U := evalHphysU
  dense_range := evalHphysU_denseRange
  intertwines := by
    intro τ _ x
    have hx : x = evalHphysU x • evalVacuum := by
      have h0 : evalHphysU (x - evalHphysU x • evalVacuum) = 0 := by
        rw [map_sub, map_smul, evalHphysU_vacuum, smul_eq_mul, mul_one]
        ring
      have hzero : x - evalHphysU x • evalVacuum = 0 :=
        evalHphysU.injective (by simpa using h0)
      exact sub_eq_zero.mp hzero
    rw [hx, oneParticleFlow, oneParticleScalar]
    simp only [map_smul, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
      evalHphysU_vacuum, smul_eq_mul]
    ring

/-- **The two-point function of the one-particle bridge is the scalar times the norm squared.** -/
theorem oneParticleBridge_twoPoint
    (P : ℝ → Hphys evalZeroState →L[ℝ] Hphys evalZeroState) {τ : ℝ} (hτ : 0 ≤ τ)
    (x : Hphys evalZeroState) :
    ⟪x, P τ x⟫ = oneParticleScalar P τ * ‖x‖ ^ 2 := by
  rw [OsFockBridge.twoPoint (oneParticleBridge P) hτ x]
  simp only [oneParticleFlow, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    inner_smul_right, real_inner_self_eq_norm_sq]
  change oneParticleScalar P τ * ‖evalHphysU x‖ ^ 2 = oneParticleScalar P τ * ‖x‖ ^ 2
  rw [evalHphysU.norm_map]

/-- **The semigroup acts by its scalar** on the one-particle sector: `‖P τ x‖ = |c τ| ‖x‖`. -/
theorem oneParticleBridge_norm
    (P : ℝ → Hphys evalZeroState →L[ℝ] Hphys evalZeroState) {τ : ℝ} (hτ : 0 ≤ τ)
    (x : Hphys evalZeroState) :
    ‖P τ x‖ = |oneParticleScalar P τ| * ‖x‖ := by
  rw [OsFockBridge.norm_intertwines (oneParticleBridge P) hτ x]
  have hU : |evalHphysU x| = ‖x‖ := by
    rw [← Real.norm_eq_abs]
    exact evalHphysU.norm_map x
  simp only [oneParticleFlow, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    norm_smul, Real.norm_eq_abs]
  change |oneParticleScalar P τ| * |evalHphysU x| = |oneParticleScalar P τ| * ‖x‖
  rw [hU]

/-- The bridge is unitary (`toIsometryEquiv`), since the sector is one-dimensional. -/
theorem oneParticleBridge_unitary
    (P : ℝ → Hphys evalZeroState →L[ℝ] Hphys evalZeroState) :
    Function.Surjective (oneParticleBridge P).toIsometryEquiv :=
  (oneParticleBridge P).toIsometryEquiv.surjective

end

end BookProof.OSReconstruction
