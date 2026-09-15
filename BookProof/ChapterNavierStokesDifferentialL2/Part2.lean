import Mathlib
import BookProof.ChapterHermiteProductBasis
import BookProof.ChapterNavierStokesCanonicalVector
import BookProof.ChapterNavierStokesLagrangianEsa
import BookProof.ChapterNavierStokesDifferentialL2.Part1

/-!
# The differential realization of the Navier–Stokes quadratic symbol on `L²(du₁du₂du₃)`

`BookProof.ChapterNavierStokesThreeComponent` proves that the coupled three-component
fiber Hamiltonian `H = ∑ᵢ ½(πᵢVᵢ + Vᵢπᵢ)`, `Vᵢ(u) = ∑ₖ A_{ik}u_k + c_i`, is essentially
self-adjoint on the finite-mode core of `ℓ²(Vel)`, `Vel = Fin 3 → ℕ`, and
`BookProof.ChapterNavierStokesCanonicalVector` shows that this sequence-space matrix *is*
the Weyl-ordered expression in the abstract ladder operators of that space.  What both
modules record as the honest open step is the **differential realization**: the operator
written with `πᵢ = −i ∂/∂uᵢ` and `uᵢ` a genuine multiplication operator, on the Hermite
core of `L²(du₁du₂du₃)`.  This module takes that step.

## The setting

The Hilbert space is `L²(ℝ³)` and the dense domain is the Gauss–polynomial (product
Hermite) core `polyGaussCore` of `BookProof.ChapterHermiteProductCore`: the functions
`p(u)·e^{-‖u‖²/4}` with `p` a polynomial.  Since `pgMap` is injective, the core carries the
polynomial coordinates `coreEquiv`, and an operator on the core is given by a polynomial
operator (`coreOp`).  Two such operators are the physical ones:

* `posOp i` — multiplication by the coordinate `uᵢ` (`pgFun_mulXPoly`);
* `momOp i` — the differential operator `πᵢ = −i ∂/∂uᵢ`.  That it *is* the derivative is
  `momOp_apply_eq_differential`: the value of `momOp i` at `p·e^{-‖u‖²/4}` is, pointwise,
  `−i` times the honest derivative `deriv (fun t => f (u with uᵢ := t)) uᵢ` of the function
  along the `i`-th coordinate (Mathlib's `deriv`, `hasDerivAt_pgFun_sec`).

`comm_momOp_posOp` is the canonical commutation relation `[πᵢ, u_k] = −i δ_{ik}` for these
genuinely differential operators.

## The Hamiltonian and the transport

`nsDiffH A c = ∑ᵢ ½(πᵢ Vᵢ + Vᵢ πᵢ)` with `Vᵢ` the multiplication operator by the affine
field `∑ₖ A_{ik}u_k + c_i` is the Weyl quantization of the Navier–Stokes quadratic symbol
`A_i(u) = u_j u_{i,j} − ν u_{i,jj}` at one Eulerian fiber (linear part the velocity
gradient, constant part `−ν` times the velocity Laplacian).

The **unitary transport** is `velUnitary : ℓ²(Vel) ≃ₗᵢ L²(ℝ³)`, the Hilbert-basis
isomorphism given by the product Hermite functions
(`BookProof.ChapterHermiteProductBasis`).  It carries the finite-mode core onto the
Gauss–polynomial core (`map_finiteModes`) and the abstract ladder operators onto the
differential ones (`intertwine_ann`, `intertwine_cre`), hence the abstract canonical
Hamiltonian onto the differential one (`conj_canH`).  The conclusions:

* `nsDiffH_essentiallySelfAdjointOn_core` — the **differentially written** Navier–Stokes
  quadratic symbol is essentially self-adjoint on the Hermite core of `L²(ℝ³)`, for every
  real velocity gradient and every constant part;
* `nsQuadraticDiffH_essentiallySelfAdjointOn_core` — the same with the coefficients spelled
  out as `(ν, u_{i,j}, u_{i,jj})`;
* `nsDiffH_not_bounded`, `polyGaussCore_dense_L2` — the operator is genuinely unbounded and
  the domain is dense, so the statement is not a bounded-operator artefact.

## Honest boundary

Nothing here claims global regularity of the *classical* Navier–Stokes PDE (Contention D5,
the deliberate scope cut): the theorem is about the Hilbert-space operator at one Eulerian
fiber, where the derivative fields `u_{i,j}`, `u_{i,jj}` are independent canonical
coordinates.
-/

namespace BookProof.NavierStokesFlow.DifferentialL2

open MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.NavierStokesFlow
open BookProof.NavierStokesFlow.LpNat BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine
open BookProof.NavierStokesFlow.ThreeComponent BookProof.NavierStokesFlow.CanonicalVector
open BookProof.NavierStokesFlow.LagrangianEsa

noncomputable section

variable {d : ℕ}
/-! ### The ladder action on the basis states -/

theorem crd_coreState (b g : Vel) : crd (coreState b) g = if g = b then 1 else 0 := by
  simp [crd, coreState, lp.single_apply, Pi.single_apply]

/-- `a_i e_β = √βᵢ e_{β−eᵢ}`. -/
theorem ann_coreState (i : Fin 3) (b : Vel) :
    ann i (coreState b) = ((Real.sqrt ((b i : ℝ)) : ℝ) : ℂ) • coreState (lower i b) := by
  refine crd_injective (funext fun g => ?_)
  rw [crd_ann, crd_smul]
  simp only [aFun, crd_coreState, Pi.smul_apply, smul_eq_mul]
  by_cases hg : raise i g = b
  · have hbi : b i = g i + 1 := by rw [← hg, raise_self]
    have hlow : lower i b = g := by rw [← hg, lower_raise]
    rw [if_pos hg, hlow, if_pos rfl, hbi]
    push_cast
    ring
  · rw [if_neg hg, mul_zero]
    by_cases hg2 : g = lower i b
    · have hb0 : b i = 0 := by
        by_contra hne
        exact hg (by rw [hg2, raise_lower i (Nat.one_le_iff_ne_zero.mpr hne)])
      rw [hb0]
      simp
    · rw [if_neg hg2, mul_zero]

/-- `a_i† e_β = √(βᵢ+1) e_{β+eᵢ}`. -/
theorem cre_coreState (i : Fin 3) (b : Vel) :
    cre i (coreState b) = ((Real.sqrt ((b i : ℝ) + 1) : ℝ) : ℂ) • coreState (raise i b) := by
  refine crd_injective (funext fun g => ?_)
  rw [crd_cre, crd_smul]
  simp only [cFun, crd_coreState, Pi.smul_apply, smul_eq_mul]
  by_cases hg : g = raise i b
  · have hlow : lower i g = b := by rw [hg, lower_raise]
    have hgi : (g i : ℝ) = (b i : ℝ) + 1 := by rw [hg, raise_self]; push_cast; ring
    rw [hlow, if_pos rfl, if_pos hg, hgi]
  · rw [if_neg hg, mul_zero]
    by_cases hg2 : lower i g = b
    · have hgi : g i = 0 := by
        by_contra hne
        exact hg (by rw [← hg2, raise_lower i (Nat.one_le_iff_ne_zero.mpr hne)])
      rw [hgi]
      simp
    · rw [if_neg hg2, mul_zero]

/-! ### The transport of the core, and of the ladder operators -/

theorem hermiteVel_mem_core (b : Vel) : hermiteVel b ∈ polyGaussCore (d := 3) :=
  hermiteMvLp_mem_core (velIdx b)

theorem pgLp_smul (c : ℂ) (p : MvPolynomial (Fin d) ℂ) : pgLp (c • p) = c • pgLp p :=
  map_smul (pgMap (d := d)) c p

theorem velUnitary_mem_core (x : lpFiniteModes Vel) :
    velUnitary ((x : L2I Vel)) ∈ polyGaussCore (d := 3) := by
  have hspan : (⊤ : Submodule ℂ (lpFiniteModes Vel))
      ≤ (polyGaussCore (d := 3)).comap
        (velUnitary.toLinearEquiv.toLinearMap ∘ₗ (lpFiniteModes Vel).subtype) := by
    rw [← span_coreState, Submodule.span_le]
    rintro _ ⟨b, rfl⟩
    change velUnitary ((coreState b : L2I Vel)) ∈ polyGaussCore (d := 3)
    rw [coreState_coe, velUnitary_single]
    exact hermiteVel_mem_core b
  exact hspan Submodule.mem_top

/-- **The transport of the finite-mode core into the Gauss–polynomial core.** -/
def embedCore : lpFiniteModes Vel →ₗ[ℂ] (polyGaussCore (d := 3)) :=
  LinearMap.codRestrict _ (velUnitary.toLinearEquiv.toLinearMap ∘ₗ (lpFiniteModes Vel).subtype)
    velUnitary_mem_core

@[simp] theorem embedCore_coe (x : lpFiniteModes Vel) :
    ((embedCore x : polyGaussCore (d := 3)) : L2d 3) = velUnitary ((x : L2I Vel)) := rfl

theorem embedCore_coreState (b : Vel) :
    embedCore (coreState b)
      = coreEquiv (((hermiteMvNorm (velIdx b) : ℝ) : ℂ)⁻¹ • hermiteMv (velIdx b)) := by
  refine Subtype.ext ?_
  rw [coreEquiv_coe, embedCore_coe, coreState_coe, velUnitary_single, hermiteVel, hermiteMvLp,
    pgLp_smul]

/-- **The annihilation operator on the Hermite core of `L²(ℝ³)`**: `∂ᵢ + uᵢ/2`. -/
def annOp (i : Fin 3) : (polyGaussCore (d := 3)) →ₗ[ℂ] (polyGaussCore (d := 3)) :=
  coreOp (annPoly i)

/-- **The creation operator on the Hermite core of `L²(ℝ³)`**: `uᵢ/2 − ∂ᵢ`. -/
def creOp (i : Fin 3) : (polyGaussCore (d := 3)) →ₗ[ℂ] (polyGaussCore (d := 3)) :=
  coreOp (crePoly i)

/-- The transport carries the abstract annihilation operator to the differential one. -/
theorem intertwine_ann (i : Fin 3) : (annOp i).comp embedCore = embedCore.comp (ann i) := by
  refine core_ext fun b => ?_
  refine Subtype.ext ?_
  simp only [LinearMap.comp_apply, annOp]
  have hR : ((embedCore (ann i (coreState b)) : polyGaussCore (d := 3)) : L2d 3)
      = ((Real.sqrt ((b i : ℝ)) : ℝ) : ℂ) • hermiteMvLp (velIdx b - Finsupp.single i 1) := by
    rw [ann_coreState, map_smul, Submodule.coe_smul, embedCore_coe, coreState_coe,
      velUnitary_single, hermiteVel, velIdx_lower]
  rw [hR, embedCore_coreState, coreOp_coe, map_smul, pgLp_smul, annPoly_hermiteMvLp,
    velIdx_apply]

/-- The transport carries the abstract creation operator to the differential one. -/
theorem intertwine_cre (i : Fin 3) : (creOp i).comp embedCore = embedCore.comp (cre i) := by
  refine core_ext fun b => ?_
  refine Subtype.ext ?_
  simp only [LinearMap.comp_apply, creOp]
  have hR : ((embedCore (cre i (coreState b)) : polyGaussCore (d := 3)) : L2d 3)
      = ((Real.sqrt ((b i : ℝ) + 1) : ℝ) : ℂ) • hermiteMvLp (velIdx b + Finsupp.single i 1) := by
    rw [cre_coreState, map_smul, Submodule.coe_smul, embedCore_coe, coreState_coe,
      velUnitary_single, hermiteVel, velIdx_raise]
  rw [hR, embedCore_coreState, coreOp_coe, map_smul, pgLp_smul, crePoly_hermiteMvLp,
    velIdx_apply]

/-! ### The algebra of intertwined operators -/

/-- `T'` is the transport of `T`: the two agree through `embedCore`. -/
def Intertwined (T : lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel)
    (T' : (polyGaussCore (d := 3)) →ₗ[ℂ] (polyGaussCore (d := 3))) : Prop :=
  ∀ x, T' (embedCore x) = embedCore (T x)

theorem Intertwined.add {T S T' S'} (hT : Intertwined T T') (hS : Intertwined S S') :
    Intertwined (T + S) (T' + S') := fun x => by
  simp only [LinearMap.add_apply, hT x, hS x, map_add]

theorem Intertwined.sub {T S T' S'} (hT : Intertwined T T') (hS : Intertwined S S') :
    Intertwined (T - S) (T' - S') := fun x => by
  simp only [LinearMap.sub_apply, hT x, hS x, map_sub]

theorem Intertwined.smul {T T'} (c : ℂ) (hT : Intertwined T T') :
    Intertwined (c • T) (c • T') := fun x => by
  simp only [LinearMap.smul_apply, hT x, map_smul]

theorem Intertwined.comp {T S T' S'} (hT : Intertwined T T') (hS : Intertwined S S') :
    Intertwined (T.comp S) (T'.comp S') := fun x => by
  simp only [LinearMap.comp_apply, hS x, hT (S x)]

theorem Intertwined.id : Intertwined LinearMap.id LinearMap.id := fun _ => rfl

theorem Intertwined.sum {ι : Type*} (s : Finset ι)
    {T : ι → lpFiniteModes Vel →ₗ[ℂ] lpFiniteModes Vel}
    {T' : ι → (polyGaussCore (d := 3)) →ₗ[ℂ] (polyGaussCore (d := 3))}
    (h : ∀ i ∈ s, Intertwined (T i) (T' i)) :
    Intertwined (∑ i ∈ s, T i) (∑ i ∈ s, T' i) := fun x => by
  simp only [LinearMap.sum_apply]
  rw [map_sum]
  exact Finset.sum_congr rfl fun i hi => h i hi x

theorem intertwined_ann (i : Fin 3) : Intertwined (ann i) (annOp i) := fun x =>
  congrFun (congrArg (fun F : lpFiniteModes Vel →ₗ[ℂ] (polyGaussCore (d := 3)) => ⇑F)
    (intertwine_ann i)) x

theorem intertwined_cre (i : Fin 3) : Intertwined (cre i) (creOp i) := fun x =>
  congrFun (congrArg (fun F : lpFiniteModes Vel →ₗ[ℂ] (polyGaussCore (d := 3)) => ⇑F)
    (intertwine_cre i)) x

/-! ### Position and momentum as ladder combinations -/

theorem posOp_eq_ladder (i : Fin 3) : posOp i = annOp i + creOp i := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨p, rfl⟩ := (coreEquiv (d := 3)).surjective y
  simp only [posOp, annOp, creOp, coreOp_coreEquiv, LinearMap.add_apply, ← map_add]
  congr 1
  simp only [mulXPoly_apply, annPoly_apply, crePoly_apply]
  ring

set_option maxHeartbeats 1000000 in
-- Unfolding the core coordinates through three linear equivalences is elaboration-heavy.
theorem momOp_eq_ladder (i : Fin 3) :
    momOp i = (Complex.I / 2) • (creOp i - annOp i) := by
  refine LinearMap.ext fun y => ?_
  obtain ⟨p, rfl⟩ := (coreEquiv (d := 3)).surjective y
  simp only [momOp, annOp, creOp, coreOp_coreEquiv, LinearMap.smul_apply, LinearMap.sub_apply,
    ← map_sub, ← map_smul]
  congr 1
  have hI : (C (Complex.I / 2) : MvPolynomial (Fin 3) ℂ) = C Complex.I * C (1 / 2 : ℂ) := by
    rw [← map_mul]
    congr 1
    ring
  have h2 : (C (1 / 2 : ℂ) : MvPolynomial (Fin 3) ℂ) * 2 = 1 := by
    rw [← map_ofNat C 2, ← map_mul]
    norm_num
  simp only [momPoly_apply, annPoly_apply, crePoly_apply, MvPolynomial.smul_eq_C_mul, map_neg,
    hI]
  linear_combination (C Complex.I * (pderiv i) p) * h2

/-! ### The transported canonical pair -/

theorem sqrtTwo_ne_zero : ((Real.sqrt 2 : ℝ) : ℂ) ≠ 0 := by
  simp

theorem sqrtTwo_mul_self : ((Real.sqrt 2 : ℝ) : ℂ) * ((Real.sqrt 2 : ℝ) : ℂ) = 2 := by
  rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 2)]
  norm_num

set_option maxHeartbeats 4000000 in
-- The transport arguments unfold operators on a submodule of `L²(ℝ³)` through several
-- linear equivalences, so the default heartbeat budget is not enough.
/-- The transport carries the mode coordinate `uᵢ = (aᵢ + aᵢ†)/√2` to `(1/√2)` times
multiplication by the coordinate. -/
theorem intertwined_pos (i : Fin 3) :
    Intertwined (pos i) (((1 / Real.sqrt 2 : ℝ) : ℂ) • posOp i) := by
  rw [posOp_eq_ladder, add_comm (annOp i) (creOp i)]
  exact ((intertwined_cre i).add (intertwined_ann i)).smul _

set_option maxHeartbeats 4000000 in
-- The transport arguments unfold operators on a submodule of `L²(ℝ³)` through several
-- linear equivalences, so the default heartbeat budget is not enough.
/-- The transport carries the mode momentum `πᵢ = i(aᵢ† − aᵢ)/√2` to `√2` times the
differential operator `−i ∂/∂uᵢ`. -/
theorem intertwined_mom (i : Fin 3) :
    Intertwined (mom i) (((Real.sqrt 2 : ℝ) : ℂ) • momOp i) := by
  have hs : ((Real.sqrt 2 : ℝ) : ℂ) • momOp i
      = (Complex.I * ((1 / Real.sqrt 2 : ℝ) : ℂ)) • (creOp i - annOp i) := by
    rw [momOp_eq_ladder, smul_smul]
    congr 1
    have hne := sqrtTwo_ne_zero
    have hsq : ((Real.sqrt 2 : ℝ) : ℂ) ^ 2 = 2 := by rw [sq]; exact sqrtTwo_mul_self
    push_cast
    field_simp
    linear_combination hsq
  rw [hs]
  exact ((intertwined_cre i).sub (intertwined_ann i)).smul _

/-! ### The differentially written Navier–Stokes quadratic symbol -/

variable (A : Matrix (Fin 3) (Fin 3) ℝ) (c : Fin 3 → ℝ)

/-- **The affine fiber field as a multiplication operator** on the Hermite core of
`L²(ℝ³)`: `Vᵢ(u) = ∑ₖ A_{ik} uₖ + cᵢ`. -/
def fieldOp (i : Fin 3) : (polyGaussCore (d := 3)) →ₗ[ℂ] (polyGaussCore (d := 3)) :=
  (∑ k, ((A i k : ℝ) : ℂ) • posOp k) + (((c i : ℝ) : ℂ) • LinearMap.id)

/-- **The differentially written Weyl-ordered Hamiltonian**
`∑ᵢ ½(πᵢ Vᵢ + Vᵢ πᵢ)` on the Hermite core of `L²(du₁du₂du₃)`, with `πᵢ = −i ∂/∂uᵢ`
and `Vᵢ` multiplication by the affine field. -/
def nsDiffH : (polyGaussCore (d := 3)) →ₗ[ℂ] (polyGaussCore (d := 3)) :=
  ∑ i, ((1 : ℂ) / 2) • ((momOp i).comp (fieldOp A c i) + (fieldOp A c i).comp (momOp i))

set_option maxHeartbeats 4000000 in
-- The transport arguments unfold operators on a submodule of `L²(ℝ³)` through several
-- linear equivalences, so the default heartbeat budget is not enough.
theorem intertwined_fieldV (i : Fin 3) :
    Intertwined (fieldV A c i)
      (((1 / Real.sqrt 2 : ℝ) : ℂ) • fieldOp A (fun j => Real.sqrt 2 * c j) i) := by
  have hsum : Intertwined (∑ k, ((A i k : ℝ) : ℂ) • pos k)
      (∑ k, ((A i k : ℝ) : ℂ) • (((1 / Real.sqrt 2 : ℝ) : ℂ) • posOp k)) :=
    Intertwined.sum _ fun k _ => (intertwined_pos k).smul _
  have hid : Intertwined (((c i : ℝ) : ℂ) • LinearMap.id)
      (((c i : ℝ) : ℂ) • LinearMap.id) := Intertwined.id.smul _
  have heq : ((1 / Real.sqrt 2 : ℝ) : ℂ) • fieldOp A (fun j => Real.sqrt 2 * c j) i
      = (∑ k, ((A i k : ℝ) : ℂ) • (((1 / Real.sqrt 2 : ℝ) : ℂ) • posOp k))
        + ((c i : ℝ) : ℂ) • LinearMap.id := by
    rw [fieldOp, smul_add, Finset.smul_sum]
    congr 1
    · exact Finset.sum_congr rfl fun k _ => smul_comm _ _ _
    · rw [smul_smul]
      congr 1
      have hne := sqrtTwo_ne_zero
      push_cast
      field_simp
  rw [heq]
  exact hsum.add hid

set_option maxHeartbeats 4000000 in
-- The transport arguments unfold operators on a submodule of `L²(ℝ³)` through several
-- linear equivalences, so the default heartbeat budget is not enough.
/-- **The transport carries the canonical Hamiltonian to the differential one.** -/
theorem intertwined_canH :
    Intertwined (canH A c) (nsDiffH A (fun j => Real.sqrt 2 * c j)) := by
  have hscal : ((Real.sqrt 2 : ℝ) : ℂ) * ((1 / Real.sqrt 2 : ℝ) : ℂ) = 1 := by
    have hne := sqrtTwo_ne_zero
    push_cast
    field_simp
  have hterm : ∀ i : Fin 3,
      Intertwined (((1 : ℂ) / 2) • ((mom i).comp (fieldV A c i) + (fieldV A c i).comp (mom i)))
        (((1 : ℂ) / 2) • ((momOp i).comp (fieldOp A (fun j => Real.sqrt 2 * c j) i)
          + (fieldOp A (fun j => Real.sqrt 2 * c j) i).comp (momOp i))) := by
    intro i
    have hm := intertwined_mom i
    have hf := intertwined_fieldV A c i
    have h := ((hm.comp hf).add (hf.comp hm)).smul ((1 : ℂ) / 2)
    have heq : (((Real.sqrt 2 : ℝ) : ℂ) • momOp i).comp
          (((1 / Real.sqrt 2 : ℝ) : ℂ) • fieldOp A (fun j => Real.sqrt 2 * c j) i)
        + (((1 / Real.sqrt 2 : ℝ) : ℂ) • fieldOp A (fun j => Real.sqrt 2 * c j) i).comp
          (((Real.sqrt 2 : ℝ) : ℂ) • momOp i)
        = (momOp i).comp (fieldOp A (fun j => Real.sqrt 2 * c j) i)
          + (fieldOp A (fun j => Real.sqrt 2 * c j) i).comp (momOp i) := by
      rw [LinearMap.smul_comp, LinearMap.comp_smul, LinearMap.smul_comp, LinearMap.comp_smul,
        smul_smul, smul_smul, hscal, mul_comm (((1 / Real.sqrt 2 : ℝ) : ℂ))
          (((Real.sqrt 2 : ℝ) : ℂ)), hscal, one_smul, one_smul]
    rw [← heq]
    exact h
  exact Intertwined.sum Finset.univ fun i _ => hterm i

/-! ## Essential self-adjointness of the differentially written operator -/

theorem sqrtTwo_real_ne_zero : Real.sqrt 2 ≠ 0 :=
  ne_of_gt (Real.sqrt_pos.mpr (by norm_num))

/-- **The Navier–Stokes quadratic symbol, written with genuine derivatives and genuine
multiplication operators on `L²(du₁du₂du₃)`, is essentially self-adjoint on the Hermite
core** — for every real velocity gradient `A` and every real constant part `c`. -/
theorem nsDiffH_essentiallySelfAdjointOn_core :
    EssentiallySelfAdjointOn (polyGaussCore (d := 3))
      ((polyGaussCore (d := 3)).subtype.comp (nsDiffH A c)) := by
  rw [essentiallySelfAdjointOn_iff_hasZeroDeficiencyOn]
  have hc : (fun j => Real.sqrt 2 * (c j / Real.sqrt 2)) = c := by
    funext j
    field_simp
  have hint : ∀ x : lpFiniteModes Vel,
      ((nsDiffH A c ⟨velUnitary ((x : L2I Vel)), velUnitary_mem_core x⟩ :
            polyGaussCore (d := 3)) : L2d 3)
        = velUnitary (((canH A (fun j => c j / Real.sqrt 2) x : lpFiniteModes Vel) : L2I Vel)) := by
    intro x
    have h := intertwined_canH A (fun j => c j / Real.sqrt 2) x
    rw [hc] at h
    have hx : (⟨velUnitary ((x : L2I Vel)), velUnitary_mem_core x⟩ : polyGaussCore (d := 3))
        = embedCore x := rfl
    rw [hx, h, embedCore_coe]
  refine hasZeroDeficiencyOn_map_of_linearIsometryEquiv velUnitary velUnitary_mem_core hint ?_
  exact (essentiallySelfAdjointOn_iff_hasZeroDeficiencyOn _ _).1
    (canH_essentiallySelfAdjointOn_core A (fun j => c j / Real.sqrt 2))

/-- **The differentially written operator is unbounded**: essential self-adjointness above
is not a boundedness phenomenon. -/
theorem nsDiffH_not_bounded (hA : A 0 0 ≠ 0) (K : ℝ) :
    ∃ f : polyGaussCore (d := 3), ‖(f : L2d 3)‖ = 1
      ∧ K < ‖((nsDiffH A c f : polyGaussCore (d := 3)) : L2d 3)‖ := by
  have hc : (fun j => Real.sqrt 2 * (c j / Real.sqrt 2)) = c := by
    funext j
    field_simp
  obtain ⟨x, hx1, hx2⟩ := canH_not_bounded A (fun j => c j / Real.sqrt 2) hA K
  refine ⟨embedCore x, ?_, ?_⟩
  · rw [embedCore_coe, velUnitary.norm_map, hx1]
  · have h := intertwined_canH A (fun j => c j / Real.sqrt 2) x
    rw [hc] at h
    rw [h, embedCore_coe, velUnitary.norm_map]
    exact hx2

/-- The Hermite core is dense in `L²(ℝ³)`, so the operator above is densely defined. -/
theorem nsDiffH_domain_dense :
    Dense ((polyGaussCore (d := 3) : Submodule ℂ (L2d 3)) : Set (L2d 3)) :=
  polyGaussCore_dense

/-! ## The Navier–Stokes reading of the coefficients -/

/-- **The quantized Navier–Stokes quadratic symbol on `L²(du₁du₂du₃)`**,
`∑ᵢ ½(πᵢ Aᵢ + Aᵢ πᵢ)` with `Aᵢ(u) = ∑ⱼ (grad i j) uⱼ − ν (lap i)`, `πᵢ = −i ∂/∂uᵢ`. -/
def nsQuadraticDiffH (nu : ℝ) (grad : Matrix (Fin 3) (Fin 3) ℝ) (lap : Fin 3 → ℝ) :
    (polyGaussCore (d := 3)) →ₗ[ℂ] (polyGaussCore (d := 3)) :=
  nsDiffH grad (fun i => -(nu * lap i))

/-- **The differentially written quantized Navier–Stokes quadratic symbol is essentially
self-adjoint on the Hermite core of `L²(du₁du₂du₃)`**, for every viscosity, every velocity
gradient and every velocity Laplacian at the fiber. -/
theorem nsQuadraticDiffH_essentiallySelfAdjointOn_core
    (nu : ℝ) (grad : Matrix (Fin 3) (Fin 3) ℝ) (lap : Fin 3 → ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := 3))
      ((polyGaussCore (d := 3)).subtype.comp (nsQuadraticDiffH nu grad lap)) :=
  nsDiffH_essentiallySelfAdjointOn_core grad _

end

end BookProof.NavierStokesFlow.DifferentialL2
