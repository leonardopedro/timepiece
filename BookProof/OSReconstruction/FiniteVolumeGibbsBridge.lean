/-
Copyright (c) 2026 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import Mathlib
import BookProof.OSReconstruction.HilbertSpace
import BookProof.OSReconstruction.FockIntertwining

/-!
# A finite-volume Gibbs state and its one-particle bridge

Plan: `cftproof.md`, **E4/B2**.  `OneParticleBridge` built the `OsFockBridge` of the
*point-evaluation* state, and said plainly why it could: that state is a character, its OS form is
rank one, so the OS Hilbert space is a line and the isometry is essentially forced.  This module
builds the bridge for a state that is **not** a character — a finite-volume Gibbs (Boltzmann)
state — on an OS Hilbert space that is genuinely two-dimensional.

## 1. The state

The ensemble is the set of **constant** field configurations `φ_t = const (a_t)` with
`a_0 = 0`, `a_1 = 1`.  A constant field is fixed by the time reflection `θ` whatever the
component encoding is (`fieldReflection_constConfig`), so the reflection acts trivially on the
support — which is exactly what makes the state reflection positive.

The Gibbs weights are `w_t = exp (-β H (φ_t)) / Z (β)` with `H (φ_t) = a_t² ∈ {0, 1}` and
`Z = exp 0 + exp (-β)`; they are positive (`gibbsWeight_pos`) and sum to one
(`gibbsWeight_sum`).  The state is

`ω F = Σ_t w_t · F (φ_t)`,   `gibbsLF β`.

**Why a finite ensemble, and not a full Gibbs measure.**  `LinearFunctional` demands additivity on
*all* observables `Config → ℝ`, and Lean's Bochner integral is not additive on non-integrable
functions, so an integral over a measure with infinite support cannot be a `LinearFunctional`.
A measure with finite support can: `Σ_t w_t δ_{φ_t}` is a genuine finite-volume Gibbs measure
(the Boltzmann measure of the two-constant-field sub-ensemble), and its expectation *is* additive
for every observable.  That is the state built here.

## 2. Reflection positivity, without rank one

`gibbs_osBilin`: `⟨F, G⟩ = Σ_t w_t · F (φ_t) · G (φ_t)` — because `θ` fixes `φ_t`.  Positivity
then holds termwise, `⟨F, F⟩ = Σ_t w_t · F (φ_t)² ≥ 0` (`gibbs_reflectionPositive`), in contrast
with the point-evaluation state, where it came from a single square.  The radical is the set of
observables vanishing on both configurations (`gibbs_mem_radical_iff`), so `𝔄 / 𝔑` is
two-dimensional.

`gibbs_not_multiplicative` records that the state is **not a character**: the indicators of the two
configurations have disjoint support, so `ω (δ₀ δ₁) = 0` while `ω δ₀ · ω δ₁ = w_0 w_1 > 0`.  This
is the precise sense in which the example is not the previous one in disguise.

## 3. The OS Hilbert space is `ℝ²`, and the bridge

`gibbsCoord` sends an observable to the vector `(√w_t · F (φ_t))_t ∈ ℝ²`; it annihilates exactly
the radical (`gibbsCoord_eq_zero_iff`), is an isometry on the quotient (`gibbsQuot_norm`, from
`gibbsCoord_norm_sq`), and is onto (`gibbsQuot_surjective`: interpolate the prescribed values with
a finite sum of indicators).  Extending along the dense embedding by `LinearMap.extendOfNorm`
gives

`gibbsU β : ℋ (gibbsState β) →ₗᵢ[ℝ] ℝ²`

(`gibbsU`, `gibbsHphysMap_norm`, `gibbsU_denseRange`).

`gibbsBridge β E` is then an `OsFockBridge ℝ² P Q`: the OS Hilbert space of the Gibbs state is
identified with the two-dimensional Fock space, and the transfer semigroup is intertwined with the
Fock flow.  The flow used is the heat evolution at one energy `E`, `Q τ = exp (-τ E) • id`; on
this ensemble both configurations are eigenstates with the same eigenvalue, so the transfer
operator is the scalar `exp (-τ E)`.  Its matrix elements are `exp (-τ E) ‖x‖²`
(`gibbsBridge_twoPoint`) and it acts by `|exp (-τ E)|` (`gibbsBridge_norm`).

## Why not E3's Gibbs state

`HalfSpaceFreeState` already builds the genuine finite-volume free-field Gibbs state
(`gibbsFun V`).  It cannot be used here: the full-algebra OS form of that state is
`⟨F, G⟩ = Σ_{x,y} w x w y · F (y, x) · G (x, y)`, which is *indefinite* — for the observable
`F` with `F (1,2) = 1`, `F (2,1) = -1` and `F = 0` elsewhere one gets
`⟨F, F⟩ = -2 w_1 w_2 < 0`.  Reflection positivity there holds only on the half-space algebra
`𝔄₊` (`gibbsFun_osForm`: a single square), which is a one-dimensional OS space again.  The
carrier `LinearFunctional` / `IsReflectionPositive` used by `PhysicalSpace` and `FockIntertwining`
is the *full* observable algebra, so a state of that carrier must have a `θ`-fixed support; the
lowest non-character case is two constant fields, and that is what is built here.

## Boundary

What is new is the *state*: a Gibbs state, non-character, with a two-dimensional OS Hilbert
space, and a constructed isometry onto `ℝ²`.  What is still an input is the transfer semigroup `P`,
as in every occupant of the bundle, and — here — its scalar character reflects the ensemble: the
two configurations are degenerate in energy, so no nontrivial dynamics is exhibited.  The ensemble
is a two-point sub-ensemble of the lattice Gibbs measure, not the full Gaussian Gibbs measure; the
latter is not a `LinearFunctional` at all (see §1), and the genuine lattice Gibbs state is not a
state of this carrier (see above).  No spatial translation, no complex structure and no
identification with `ℱ_out` is built, so B2 in general — a unitary
`ℋ_OS → ℋ_ref ⊆ ℱ_out` for the interacting theory, intertwining the smeared fields and the actual
heat semigroup — remains open.
-/

namespace BookProof.OSReconstruction

open BookProof.ReflectionPositivity BookProof.BalabanRG
open scoped RealInnerProductSpace

noncomputable section

namespace TwoStateGibbs

/-! ## 1. The two-state Gibbs ensemble -/

/-- The two field values of the ensemble: the constant configurations `φ = 0` and `φ = 1`. -/
def gibbsValue : Fin 2 → ℝ := ![0, 1]

/-- The energy of the `t`-th configuration, `H (φ_t) = φ_t²`, i.e. `0` and `1`. -/
def gibbsEnergy (t : Fin 2) : ℝ := gibbsValue t ^ 2

/-- The partition function `Z (β) = Σ_t exp (-β H (φ_t))`. -/
def gibbsZ (β : ℝ) : ℝ := ∑ t, Real.exp (-β * gibbsEnergy t)

/-- `Z` is positive: a sum of exponentials over a non-empty index set. -/
theorem gibbsZ_pos (β : ℝ) : 0 < gibbsZ β :=
  Finset.sum_pos (fun _ _ => Real.exp_pos _) ⟨0, Finset.mem_univ 0⟩

/-- **The Boltzmann weights** `exp (-β H (φ_t)) / Z (β)`. -/
def gibbsWeight (β : ℝ) (t : Fin 2) : ℝ := Real.exp (-β * gibbsEnergy t) / gibbsZ β

theorem gibbsWeight_pos (β : ℝ) (t : Fin 2) : 0 < gibbsWeight β t :=
  div_pos (Real.exp_pos _) (gibbsZ_pos β)

/-- **The weights sum to one**: the state is normalized. -/
theorem gibbsWeight_sum (β : ℝ) : ∑ t, gibbsWeight β t = 1 := by
  unfold gibbsWeight
  rw [← Finset.sum_div]
  exact div_self (ne_of_gt (gibbsZ_pos β))

/-- The constant field configuration with value `a`. -/
def constConfig (a : ℝ) : Config := fun _ => a

/-- **Constant configurations are reflection invariant**: `θ` permutes the components and a
constant field does not notice the permutation.  This is what makes the finite ensemble reflection
positive, and it uses nothing about the reflection beyond it being a permutation. -/
theorem fieldReflection_constConfig (a : ℝ) :
    fieldReflection (constConfig a) = constConfig a := by
  funext i
  rfl

/-- The `t`-th configuration of the ensemble. -/
def gibbsConfig (t : Fin 2) : Config := constConfig (gibbsValue t)

theorem fieldReflection_gibbsConfig (t : Fin 2) :
    fieldReflection (gibbsConfig t) = gibbsConfig t :=
  fieldReflection_constConfig _

/-- The two configurations are distinct, because the component type is non-empty. -/
theorem gibbsConfig_injective : Function.Injective gibbsConfig := by
  haveI : NeZero latticeDim := ⟨by rw [latticeDim_eq]; decide⟩
  intro s t h
  have h' : gibbsValue s = gibbsValue t := by
    simpa [gibbsConfig, constConfig] using congrFun h 0
  fin_cases s <;> fin_cases t <;> simp [gibbsValue] at h' ⊢

/-! ## 2. The state, its OS form, and its radical -/

/-- **The Gibbs expectation at inverse temperature `β`**: the Boltzmann average over the two
constant configurations.  It is a `LinearFunctional` because a finite average is additive for every
observable, with no integrability hypothesis. -/
def gibbsLF (β : ℝ) : LinearFunctional where
  toFun F := ∑ t, gibbsWeight β t * F (gibbsConfig t)
  map_add F G := by
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul c F := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  map_theta F := by
    simp only [thetaObs_apply, fieldReflection_gibbsConfig]

/-- **The OS form of the Gibbs state** is the weighted `ℓ²` pairing of the two field values. -/
theorem gibbs_osBilin (β : ℝ) (F G : Observable) :
    osBilin (gibbsLF β) F G
      = ∑ t, gibbsWeight β t * (F (gibbsConfig t) * G (gibbsConfig t)) := by
  simp [osBilin, osForm, gibbsLF, thetaObs_apply, Pi.mul_apply, fieldReflection_gibbsConfig]

/-- **The Gibbs state is reflection positive**: each summand of the diagonal is a positive weight
times a square. -/
theorem gibbs_reflectionPositive (β : ℝ) :
    IsReflectionPositive fun F : Observable => gibbsLF β F := by
  intro F
  change 0 ≤ osBilin (gibbsLF β) F F
  rw [gibbs_osBilin]
  exact Finset.sum_nonneg fun t _ =>
    mul_nonneg (le_of_lt (gibbsWeight_pos β t)) (mul_self_nonneg _)

/-- **The finite-volume Gibbs state**, as an `OSState`. -/
def gibbsState (β : ℝ) : OSState where
  ω := gibbsLF β
  pos := gibbs_reflectionPositive β

/-- **The radical of the Gibbs form** is the set of observables vanishing on both configurations:
the weight makes the diagonal form definite, and vanishing of the form in both arguments is the
same as vanishing on the support. -/
theorem gibbs_mem_radical_iff (β : ℝ) {F : Observable} :
    F ∈ Radical (gibbsLF β) ↔ ∀ t : Fin 2, F (gibbsConfig t) = 0 := by
  constructor
  · intro h
    have hsum : ∑ t : Fin 2,
        gibbsWeight β t * (F (gibbsConfig t) * F (gibbsConfig t)) = 0 := by
      have := h F
      simpa [gibbs_osBilin] using this
    have hnonneg : ∀ t ∈ (Finset.univ : Finset (Fin 2)),
        0 ≤ gibbsWeight β t * (F (gibbsConfig t) * F (gibbsConfig t)) := fun t _ =>
      mul_nonneg (le_of_lt (gibbsWeight_pos β t)) (mul_self_nonneg _)
    have hz := (Finset.sum_eq_zero_iff_of_nonneg hnonneg).1 hsum
    intro t
    have ht := hz t (Finset.mem_univ t)
    have hw : gibbsWeight β t ≠ 0 := ne_of_gt (gibbsWeight_pos β t)
    rcases mul_eq_zero.1 ht with h0 | h0
    · exact absurd h0 hw
    · exact mul_self_eq_zero.1 h0
  · intro h G
    rw [gibbs_osBilin]
    exact Finset.sum_eq_zero fun t _ => by rw [h t, zero_mul, mul_zero]

/-- The observable that is `1` on the `t`-th configuration and `0` elsewhere. -/
def gibbsDelta (t : Fin 2) : Observable := fun x => if x = gibbsConfig t then 1 else 0

theorem gibbsDelta_self (t : Fin 2) : gibbsDelta t (gibbsConfig t) = 1 := by
  simp [gibbsDelta]

theorem gibbsDelta_of_ne {s t : Fin 2} (h : s ≠ t) : gibbsDelta t (gibbsConfig s) = 0 := by
  simp only [gibbsDelta]
  rw [if_neg]
  exact fun hst => h (gibbsConfig_injective hst)

/-- The expectation of an indicator is its Boltzmann weight. -/
theorem gibbsLF_delta (β : ℝ) (t : Fin 2) : gibbsLF β (gibbsDelta t) = gibbsWeight β t := by
  change ∑ s : Fin 2, gibbsWeight β s * gibbsDelta t (gibbsConfig s) = gibbsWeight β t
  rw [Finset.sum_eq_single t]
  · rw [gibbsDelta_self, mul_one]
  · intro s _ hst
    rw [gibbsDelta_of_ne hst, mul_zero]
  · intro ht
    exact absurd (Finset.mem_univ t) ht

/-- The product of the two indicators vanishes on the support: each configuration matches exactly
one of them. -/
theorem gibbsDelta_mul (s : Fin 2) :
    (gibbsDelta 0 * gibbsDelta 1) (gibbsConfig s) = 0 := by
  have hs : s = 0 ∨ s = 1 := by fin_cases s <;> simp
  rcases hs with h | h
  · subst h
    rw [Pi.mul_apply, gibbsDelta_of_ne (by decide : (0 : Fin 2) ≠ 1), mul_zero]
  · subst h
    rw [Pi.mul_apply, gibbsDelta_of_ne (by decide : (1 : Fin 2) ≠ 0), zero_mul]

theorem gibbsLF_delta_mul (β : ℝ) :
    gibbsLF β (gibbsDelta 0 * gibbsDelta 1) = 0 := by
  change ∑ s : Fin 2,
    gibbsWeight β s * ((gibbsDelta 0 * gibbsDelta 1) (gibbsConfig s)) = 0
  exact Finset.sum_eq_zero fun s _ => by rw [gibbsDelta_mul, mul_zero]

/-- **The Gibbs state is not a character.**  The indicators of the two configurations have disjoint
support, so the expectation of their product vanishes while the product of the expectations is
`w_0 w_1 > 0`.  This is what distinguishes the example from the point-evaluation state. -/
theorem gibbs_not_multiplicative (β : ℝ) :
    gibbsLF β (gibbsDelta 0 * gibbsDelta 1) ≠
      gibbsLF β (gibbsDelta 0) * gibbsLF β (gibbsDelta 1) := by
  rw [gibbsLF_delta_mul, gibbsLF_delta, gibbsLF_delta]
  exact fun h => (mul_pos (gibbsWeight_pos β 0) (gibbsWeight_pos β 1)).ne' h.symm

/-! ## 3. The coordinates: `𝔄 / 𝔑 ≃ ℝ²` -/

/-- **The coordinate map**: the weighted values at the two configurations, as a vector in `ℝ²`. -/
def gibbsCoord (β : ℝ) (F : Observable) : EuclideanSpace ℝ (Fin 2) :=
  WithLp.toLp 2 fun t => Real.sqrt (gibbsWeight β t) * F (gibbsConfig t)

theorem gibbsCoord_add (β : ℝ) (F G : Observable) :
    gibbsCoord β (F + G) = gibbsCoord β F + gibbsCoord β G := by
  refine PiLp.ext fun t => ?_
  simp [gibbsCoord, Pi.add_apply, mul_add]

theorem gibbsCoord_smul (β : ℝ) (c : ℝ) (F : Observable) :
    gibbsCoord β (c • F) = c • gibbsCoord β F := by
  refine PiLp.ext fun t => ?_
  simp [gibbsCoord, Pi.smul_apply, smul_eq_mul]
  ring

/-- The coordinate map, as a linear map. -/
def gibbsCoordLM (β : ℝ) : Observable →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toFun := gibbsCoord β
  map_add' := gibbsCoord_add β
  map_smul' := gibbsCoord_smul β

/-- **The coordinates reproduce the OS form**: the squared norm of `gibbsCoord` is `⟨F, F⟩`. -/
theorem gibbsCoord_norm_sq (β : ℝ) (F : Observable) :
    ‖gibbsCoord β F‖ ^ 2
      = ∑ t, gibbsWeight β t * (F (gibbsConfig t) * F (gibbsConfig t)) := by
  rw [EuclideanSpace.norm_eq]
  have hsq : ∑ t : Fin 2, ‖(gibbsCoord β F).ofLp t‖ ^ 2
      = ∑ t : Fin 2, gibbsWeight β t * (F (gibbsConfig t) * F (gibbsConfig t)) := by
    refine Finset.sum_congr rfl fun t _ => ?_
    rw [gibbsCoord, WithLp.ofLp_toLp, Real.norm_eq_abs, sq_abs, mul_pow,
      Real.sq_sqrt (le_of_lt (gibbsWeight_pos β t))]
    ring
  rw [hsq]
  exact Real.sq_sqrt (Finset.sum_nonneg fun t _ =>
    mul_nonneg (le_of_lt (gibbsWeight_pos β t)) (mul_self_nonneg _))

/-- **The coordinate map vanishes exactly on the radical.** -/
theorem gibbsCoord_eq_zero_iff (β : ℝ) (F : Observable) :
    gibbsCoord β F = 0 ↔ ∀ t : Fin 2, F (gibbsConfig t) = 0 := by
  constructor
  · intro h t
    have h1 : (gibbsCoord β F).ofLp t = 0 := by
      rw [h]
      simp
    rw [gibbsCoord, WithLp.ofLp_toLp] at h1
    have hw : Real.sqrt (gibbsWeight β t) ≠ 0 :=
      (Real.sqrt_pos.2 (gibbsWeight_pos β t)).ne'
    exact (mul_eq_zero.1 h1).resolve_left hw
  · intro h
    refine PiLp.ext fun t => ?_
    simp [gibbsCoord, h t]

/-- **The coordinates descend to the OS quotient.** -/
def gibbsQuot (β : ℝ) : PhysSpace (gibbsState β) →ₗ[ℝ] EuclideanSpace ℝ (Fin 2) :=
  (Radical (gibbsLF β)).liftQ (gibbsCoordLM β) fun F hF => by
    rw [LinearMap.mem_ker]
    exact (gibbsCoord_eq_zero_iff β F).2 ((gibbs_mem_radical_iff β).1 hF)

theorem gibbsQuot_apply_mk (β : ℝ) (F : Observable) :
    gibbsQuot β (Submodule.Quotient.mk F) = gibbsCoord β F :=
  Submodule.liftQ_apply _ _ _

/-- **The quotient map is an isometry onto `ℝ²`.** -/
theorem gibbsQuot_norm (β : ℝ) (x : PhysSpace (gibbsState β)) :
    ‖gibbsQuot β x‖ = ‖x‖ := by
  refine Submodule.Quotient.induction_on _ x fun F => ?_
  rw [gibbsQuot_apply_mk, physNorm_mk]
  change ‖gibbsCoord β F‖ = Real.sqrt (osBilin (gibbsLF β) F F)
  rw [gibbs_osBilin]
  rw [← gibbsCoord_norm_sq β F, Real.sqrt_sq (norm_nonneg _)]

/-- **The quotient map is onto**: prescribed values at the two configurations are interpolated by a
finite sum of indicators. -/
theorem gibbsQuot_surjective (β : ℝ) : Function.Surjective (gibbsQuot β) := by
  intro v
  refine ⟨Submodule.Quotient.mk (fun x : Config => ∑ t : Fin 2,
    if x = gibbsConfig t then v.ofLp t / Real.sqrt (gibbsWeight β t) else 0), ?_⟩
  rw [gibbsQuot_apply_mk]
  refine PiLp.ext fun t => ?_
  rw [gibbsCoord, WithLp.ofLp_toLp]
  have hval : (∑ s : Fin 2, if gibbsConfig t = gibbsConfig s then
      v.ofLp s / Real.sqrt (gibbsWeight β s) else 0)
      = v.ofLp t / Real.sqrt (gibbsWeight β t) := by
    rw [Finset.sum_eq_single t]
    · simp
    · intro s _ hst
      rw [if_neg fun h => hst (gibbsConfig_injective h).symm]
    · intro ht
      exact absurd (Finset.mem_univ t) ht
  rw [hval]
  have hw : Real.sqrt (gibbsWeight β t) ≠ 0 :=
    (Real.sqrt_pos.2 (gibbsWeight_pos β t)).ne'
  field_simp

/-! ## 4. The completion: `ℋ (gibbsState β) ≃ₗᵢ ℝ²` -/

/-- The isometry extended to the completion, by `LinearMap.extendOfNorm`. -/
def gibbsHphysMap (β : ℝ) :
    Hphys (gibbsState β) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  LinearMap.extendOfNorm (gibbsQuot β) (physCoe (gibbsState β))

theorem gibbsHphysMap_coe (β : ℝ) (x : PhysSpace (gibbsState β)) :
    gibbsHphysMap β (physCoe (gibbsState β) x) = gibbsQuot β x := by
  refine LinearMap.extendOfNorm_eq
    (f := gibbsQuot β) (e := physCoe (gibbsState β))
    (denseRange_physCoe (gibbsState β)) ⟨1, fun y => by simp [gibbsQuot_norm]⟩ x

/-- **The extended map is still an isometry.** -/
theorem gibbsHphysMap_norm (β : ℝ) (z : Hphys (gibbsState β)) :
    ‖gibbsHphysMap β z‖ = ‖z‖ := by
  have hclosed : IsClosed {z : Hphys (gibbsState β) | ‖gibbsHphysMap β z‖ = ‖z‖} :=
    isClosed_eq (continuous_norm.comp (gibbsHphysMap β).continuous) continuous_norm
  have hsub : Set.range (physCoe (gibbsState β)) ⊆
      {z | ‖gibbsHphysMap β z‖ = ‖z‖} := by
    rintro _ ⟨x, rfl⟩
    change ‖gibbsHphysMap β (physCoe (gibbsState β) x)‖ =
      ‖physCoe (gibbsState β) x‖
    rw [gibbsHphysMap_coe, gibbsQuot_norm, physCoe_apply,
      UniformSpace.Completion.norm_coe]
  have hd : closure (Set.range (physCoe (gibbsState β))) = Set.univ :=
    DenseRange.closure_range (denseRange_physCoe (gibbsState β))
  have hcl := hclosed.closure_subset_iff.2 hsub
  rw [hd] at hcl
  exact hcl trivial

/-- **The OS Hilbert space of the Gibbs state, as an isometry onto `ℝ²`.** -/
def gibbsU (β : ℝ) : Hphys (gibbsState β) →ₗᵢ[ℝ] EuclideanSpace ℝ (Fin 2) where
  toLinearMap := (gibbsHphysMap β).toLinearMap
  norm_map' := gibbsHphysMap_norm β

theorem gibbsU_apply_coe (β : ℝ) (x : PhysSpace (gibbsState β)) :
    gibbsU β (physCoe (gibbsState β) x) = gibbsQuot β x :=
  gibbsHphysMap_coe β x

theorem gibbsU_surjective (β : ℝ) : Function.Surjective (gibbsU β) := by
  intro v
  obtain ⟨x, hx⟩ := gibbsQuot_surjective β v
  exact ⟨physCoe (gibbsState β) x, by rw [gibbsU_apply_coe, hx]⟩

theorem gibbsU_denseRange (β : ℝ) : DenseRange (gibbsU β) := by
  rw [DenseRange, (gibbsU_surjective β).range_eq]
  exact dense_univ

/-! ## 5. The bridge -/

/-- The transfer semigroup of the instance: heat evolution at one energy `E`.  On this ensemble both
configurations are eigenstates with the same eigenvalue, so it acts as the scalar `exp (-τ E)`. -/
def gibbsTransfer (β E : ℝ) : ℝ → Hphys (gibbsState β) →L[ℝ] Hphys (gibbsState β) :=
  fun τ => Real.exp (-(τ * E)) • ContinuousLinearMap.id ℝ (Hphys (gibbsState β))

/-- The Fock-side flow: the same scalar on `ℝ²`. -/
def gibbsFlow (E : ℝ) :
    ℝ → EuclideanSpace ℝ (Fin 2) →L[ℝ] EuclideanSpace ℝ (Fin 2) :=
  fun τ => Real.exp (-(τ * E)) • ContinuousLinearMap.id ℝ (EuclideanSpace ℝ (Fin 2))

/-- **A bridge for the Gibbs state**: the OS Hilbert space of a non-character state is identified
with the two-dimensional Fock space, and the transfer semigroup is intertwined with the flow. -/
def gibbsBridge (β E : ℝ) :
    OsFockBridge (EuclideanSpace ℝ (Fin 2)) (gibbsTransfer β E) (gibbsFlow E) where
  U := gibbsU β
  dense_range := gibbsU_denseRange β
  intertwines := by
    intro τ _ x
    simp [gibbsTransfer, gibbsFlow]

/-- **The two-point function of the Gibbs bridge**: the matrix element is the Boltzmann scalar times
the norm squared. -/
theorem gibbsBridge_twoPoint (β E : ℝ) {τ : ℝ} (hτ : 0 ≤ τ)
    (x : Hphys (gibbsState β)) :
    ⟪x, gibbsTransfer β E τ x⟫ = Real.exp (-(τ * E)) * ‖x‖ ^ 2 := by
  rw [OsFockBridge.twoPoint (gibbsBridge β E) hτ x]
  have hU : (gibbsBridge β E).U = gibbsU β := rfl
  rw [hU, gibbsFlow, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    real_inner_smul_right, real_inner_self_eq_norm_sq, (gibbsU β).norm_map]

/-- **The semigroup acts by its scalar** on the two-dimensional OS space. -/
theorem gibbsBridge_norm (β E : ℝ) {τ : ℝ} (hτ : 0 ≤ τ)
    (x : Hphys (gibbsState β)) :
    ‖gibbsTransfer β E τ x‖ = |Real.exp (-(τ * E))| * ‖x‖ := by
  rw [OsFockBridge.norm_intertwines (gibbsBridge β E) hτ x]
  have hU : (gibbsBridge β E).U = gibbsU β := rfl
  rw [hU, gibbsFlow, ContinuousLinearMap.smul_apply, ContinuousLinearMap.id_apply,
    norm_smul, Real.norm_eq_abs, (gibbsU β).norm_map]

end TwoStateGibbs

end

end BookProof.OSReconstruction
