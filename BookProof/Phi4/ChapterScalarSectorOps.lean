import BookProof.Phi4.ChapterScalarOuter

/-!
# Operations on the scalar outer sector

Two structural facts about the second quantization `dΓ(A)` on the completed symmetric
outer Fock space of the scalar model are recorded here.

* `outerHam_add_const` — the **shift law**: second quantization is affine along a
  one-particle shift `A ↦ A + c·1`, the increment being `c` times the outer number
  operator `N_out`, which multiplies the `n`-particle sector by `n`.
* `outerHam_oneParticle_eq` — the **one-particle sector**: on the `n = 1` sector the
  outer Hamiltonian acts exactly as the one-particle Hamiltonian `M.innerHam`.

Both statements are proved for an arbitrary one-particle operator `A` on the Gauss
polynomial core and then specialized to `M.innerHam`.  Nothing is assumed: the module
contains no `axiom` and no `sorry`.
-/
namespace BookProof.Phi4.Model

open TensorCore SecondQuantizationCore FockStatistics ReducedEsa
open DirectSumEsa GraphCore YangMillsNonAbelianEsa
open HermiteProductCore YangMillsHermite

noncomputable section

/-! ## Linearity of the sector derivation in the one-particle operator -/

section Derivation

variable {Hs : IPSpace} {D₂ : Submodule ℂ Hs.carrier}

/-- The Leibniz recursion step of the sector derivation, as an equation on linear maps. -/
theorem derPow_succ (A : D₂ →ₗ[ℂ] Hs.carrier) (n : ℕ) :
    derPow Hs D₂ A (n + 1) =
      TensorProduct.map A (inclPow Hs D₂ n).toLinearMap
        + TensorProduct.map D₂.subtype (derPow Hs D₂ A n) := rfl

/-- The sector derivation is additive in the one-particle operator. -/
theorem derPow_add (A B : D₂ →ₗ[ℂ] Hs.carrier) (n : ℕ) :
    derPow Hs D₂ (A + B) n = derPow Hs D₂ A n + derPow Hs D₂ B n := by
  induction n with
  | zero => ext; simp [derPow]
  | succ n ih =>
      rw [derPow_succ, derPow_succ, derPow_succ, ih, TensorProduct.map_add_left,
        TensorProduct.map_add_right]
      abel

/-- The sector derivation is homogeneous in the one-particle operator. -/
theorem derPow_smul (A : D₂ →ₗ[ℂ] Hs.carrier) (c : ℂ) (n : ℕ) :
    derPow Hs D₂ (c • A) n = c • derPow Hs D₂ A n := by
  induction n with
  | zero => ext; simp [derPow]
  | succ n ih =>
      rw [derPow_succ, derPow_succ, ih, TensorProduct.map_smul_left,
        TensorProduct.map_smul_right, smul_add]

/-- The sector derivation of the inclusion `D₂ ↪ H` is the particle number: on `D₂^{⊗n}`
it multiplies by `n`. -/
theorem derPow_subtype (n : ℕ) :
    derPow Hs D₂ D₂.subtype n = (n : ℂ) • (inclPow Hs D₂ n).toLinearMap := by
  induction n with
  | zero => ext; simp [derPow]
  | succ n ih =>
      refine TensorProduct.ext' fun a b => ?_
      rw [derPow_succ, ih]
      change (TensorProduct.map D₂.subtype (inclPow Hs D₂ n).toLinearMap) (a ⊗ₜ[ℂ] b)
          + (TensorProduct.map D₂.subtype ((n : ℂ) • (inclPow Hs D₂ n).toLinearMap))
              (a ⊗ₜ[ℂ] b)
        = (((n + 1 : ℕ) : ℂ) • (inclPow Hs D₂ (n + 1)).toLinearMap) (a ⊗ₜ[ℂ] b)
      rw [TensorProduct.map_tmul, TensorProduct.map_tmul, LinearMap.smul_apply,
        LinearMap.smul_apply]
      simp only [LinearIsometry.coe_toLinearMap, inclPow_tmul, TensorProduct.tmul_smul]
      have hx : D₂.subtype a ⊗ₜ[ℂ] inclPow Hs D₂ n b
            + (n : ℂ) • (D₂.subtype a ⊗ₜ[ℂ] inclPow Hs D₂ n b)
          = ((n : ℂ) + 1) • (D₂.subtype a ⊗ₜ[ℂ] inclPow Hs D₂ n b) := by
        rw [add_comm, add_smul, one_smul]
      rw [hx]
      congr 1
      push_cast
      ring

end Derivation

/-! ## Additivity of the sector operators -/

section Transport

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- Transport along a linear isometry is additive in the transported operator. -/
theorem pushOp_add (U : F →ₗᵢ[ℂ] G) {D : Submodule ℂ F} (T T' : D →ₗ[ℂ] F) :
    pushOp U (T + T') = pushOp U T + pushOp U T' := by
  simp only [pushOp, LinearMap.comp_add, LinearMap.add_comp]

/-- Transport along a linear isometry is homogeneous in the transported operator. -/
theorem pushOp_smul (U : F →ₗᵢ[ℂ] G) {D : Submodule ℂ F} (T : D →ₗ[ℂ] F) (c : ℂ) :
    pushOp U (c • T) = c • pushOp U T := by
  simp only [pushOp, LinearMap.comp_smul, LinearMap.smul_comp]

end Transport

section Sector

variable {Hs : IPSpace} {D : Submodule ℂ Hs.carrier}

/-- The sector derivation is additive in the one-particle operator. -/
theorem sectorOp_add (A B : D →ₗ[ℂ] Hs.carrier) (n : ℕ) :
    sectorOp Hs D (A + B) n = sectorOp Hs D A n + sectorOp Hs D B n := by
  simp only [sectorOp, derPow_add, LinearMap.add_comp]

/-- The sector derivation is homogeneous in the one-particle operator. -/
theorem sectorOp_smul (A : D →ₗ[ℂ] Hs.carrier) (c : ℂ) (n : ℕ) :
    sectorOp Hs D (c • A) n = c • sectorOp Hs D A n := by
  simp only [sectorOp, derPow_smul, LinearMap.smul_comp]

/-- The completed sector derivation is additive in the one-particle operator. -/
theorem fockSectorOp_add (A B : D →ₗ[ℂ] Hs.carrier) (n : ℕ) :
    fockSectorOp Hs D (A + B) n = fockSectorOp Hs D A n + fockSectorOp Hs D B n := by
  simp only [fockSectorOp, sectorOp_add, pushOp_add]

/-- The completed sector derivation is homogeneous in the one-particle operator. -/
theorem fockSectorOp_smul (A : D →ₗ[ℂ] Hs.carrier) (c : ℂ) (n : ℕ) :
    fockSectorOp Hs D (c • A) n = c • fockSectorOp Hs D A n := by
  simp only [fockSectorOp, sectorOp_smul, pushOp_smul]

/-- The symmetrized sector derivation is additive in the one-particle operator. -/
theorem cbosonicSectorOp_add (A B : D →ₗ[ℂ] Hs.carrier) (n : ℕ) :
    cbosonicSectorOp Hs D (A + B) n = cbosonicSectorOp Hs D A n + cbosonicSectorOp Hs D B n := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [cbosonicSectorOp, redOp_coe, LinearMap.add_apply, Submodule.coe_add,
    fockSectorOp_add]

/-- The symmetrized sector derivation is homogeneous in the one-particle operator. -/
theorem cbosonicSectorOp_smul (A : D →ₗ[ℂ] Hs.carrier) (c : ℂ) (n : ℕ) :
    cbosonicSectorOp Hs D (c • A) n = c • cbosonicSectorOp Hs D A n := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp only [cbosonicSectorOp, redOp_coe, LinearMap.smul_apply, Submodule.coe_smul,
    fockSectorOp_smul]

/-- **The particle number on a symmetric sector**: the symmetrized sector derivation of the
inclusion `D ↪ H` multiplies the `n`-particle sector by `n`. -/
theorem cbosonicSectorOp_subtype (n : ℕ)
    (x : redDom (cbosonicProj Hs n) (fockSectorDom Hs D n)) :
    cbosonicSectorOp Hs D D.subtype n x = (n : ℂ) • x := by
  apply Subtype.ext
  rw [Submodule.coe_smul]
  obtain ⟨x₀, hx₀, hxe⟩ := x.2
  have hx₀' : ∃ y : ((domSpace Hs D).pow n), inclPow Hs D n y = x₀ := hx₀
  obtain ⟨y₀, hy₀⟩ := hx₀'
  have hy : x₀ = inclPow Hs D n y₀ := hy₀.symm
  have hxe' : sectorEmb Hs n x₀ = (x : fockSector Hs n) := by simpa using hxe
  have hpush : fockSectorOp Hs D D.subtype n
      (redIncl (cbosonicProj Hs n) (fockSectorDom Hs D n) x)
      = sectorEmb Hs n (sectorOp Hs D D.subtype n ⟨x₀, hx₀⟩) := by
    refine pushOp_apply (sectorEmb Hs n) (sectorOp Hs D D.subtype n) _ ⟨x₀, hx₀⟩ ?_
    rw [redIncl_coe]
    exact hxe'.symm
  calc (cbosonicSectorOp Hs D D.subtype n x : fockSector Hs n)
      = fockSectorOp Hs D D.subtype n
          (redIncl (cbosonicProj Hs n) (fockSectorDom Hs D n) x) := by
        rw [cbosonicSectorOp, redOp_coe]
    _ = sectorEmb Hs n (sectorOp Hs D D.subtype n ⟨x₀, hx₀⟩) := hpush
    _ = sectorEmb Hs n (derPow Hs D D.subtype n y₀) := by
        rw [sectorOp_apply Hs D D.subtype n ⟨x₀, hx₀⟩ y₀ hy]
    _ = sectorEmb Hs n ((n : ℂ) • inclPow Hs D n y₀) := by
        rw [derPow_subtype, LinearMap.smul_apply, LinearIsometry.coe_toLinearMap]
    _ = (n : ℂ) • sectorEmb Hs n (inclPow Hs D n y₀) := map_smul _ _ _
    _ = (n : ℂ) • (x : fockSector Hs n) := by rw [← hy, ← hxe']

end Sector

/-! ## The outer number operator and the shift law -/

section Shift

variable {Hs : IPSpace} {D : Submodule ℂ Hs.carrier}

/-- The **outer number operator**: on the `n`-particle sector it multiplies by `n`. -/
def outerNumber (Hs : IPSpace) (D : Submodule ℂ Hs.carrier) :
    hbosonicFockDom Hs D →ₗ[ℂ] hbosonicFock Hs :=
  dsOp fun n => (n : ℂ) • (redDom (cbosonicProj Hs n) (fockSectorDom Hs D n)).subtype

set_option maxHeartbeats 1000000 in
-- the componentwise comparison unfolds `dsOp` and the completed sector coercions
/-- **The shift law**: second quantization is affine along a one-particle shift; the
increment of `A ↦ A + c·1` is `c` times the outer number operator. -/
theorem hbosonicFockOp_add_scalar (A : D →ₗ[ℂ] Hs.carrier) (c : ℝ)
    (x : hbosonicFockDom Hs D) :
    hbosonicFockOp Hs D (A + (c : ℂ) • D.subtype) x
      = hbosonicFockOp Hs D A x + (c : ℂ) • outerNumber Hs D x := by
  apply lp.ext
  funext n
  apply Subtype.ext
  simp only [hbosonicFockOp, outerNumber, dsOp, LinearMap.coe_mk, AddHom.coe_mk,
    lp.coeFn_add, lp.coeFn_smul, Pi.add_apply, Pi.smul_apply]
  rw [show cbosonicSectorOp Hs D (A + (c : ℂ) • D.subtype) n
      = cbosonicSectorOp Hs D A n + (c : ℂ) • cbosonicSectorOp Hs D D.subtype n from by
    rw [cbosonicSectorOp_add, cbosonicSectorOp_smul]]
  simp only [LinearMap.add_apply, LinearMap.smul_apply, Submodule.coe_add, Submodule.coe_smul,
    Submodule.coe_subtype, cbosonicSectorOp_subtype, smul_smul]

end Shift

/-! ## The one-particle sector -/

section OneParticle

variable {Hs : IPSpace} {D : Submodule ℂ Hs.carrier}

/-- The derivation of a one-particle operator in degree one, on the state `a ⊗ 1`. -/
theorem derPow_one (A : D →ₗ[ℂ] Hs.carrier) (a : D) :
    derPow Hs D A 1 (a ⊗ₜ[ℂ] (1 : ℂ)) = (A a) ⊗ₜ[ℂ] (1 : ℂ) := by
  rw [derPow_tmul]
  simp only [derPow_zero, TensorProduct.tmul_zero, add_zero]
  rfl

/-- The isometric inclusion in degree one, on the state `a ⊗ 1`. -/
theorem inclPow_one (a : D) :
    inclPow Hs D 1 (a ⊗ₜ[ℂ] (1 : ℂ)) = (a : Hs.carrier) ⊗ₜ[ℂ] (1 : ℂ) := by
  rw [inclPow_tmul]
  rfl

/-- The sector derivation of a one-particle operator in degree one is that operator. -/
theorem sectorOp_one (A : D →ₗ[ℂ] Hs.carrier) (a : D) :
    sectorOp Hs D A 1 (⟨(a : Hs.carrier) ⊗ₜ[ℂ] (1 : ℂ), ⟨a ⊗ₜ[ℂ] (1 : ℂ), rfl⟩⟩ :
      sectorDom Hs D 1) = (A a) ⊗ₜ[ℂ] (1 : ℂ) := by
  rw [sectorOp_apply Hs D A 1 _ (a ⊗ₜ[ℂ] (1 : ℂ)) rfl, derPow_one]

/-- **The one-particle sector action**: on a degree-one state built from a core vector `a`,
the symmetrized sector derivation acts as the one-particle operator `A` itself. -/
theorem cbosonicSectorOp_oneParticle (A : D →ₗ[ℂ] Hs.carrier) (a : D)
    (x : redDom (cbosonicProj Hs 1) (fockSectorDom Hs D 1))
    (hx : (x : fockSector Hs 1) = sectorEmb Hs 1 (inclPow Hs D 1 (a ⊗ₜ[ℂ] (1 : ℂ)))) :
    (cbosonicSectorOp Hs D A 1 x : fockSector Hs 1)
      = sectorEmb Hs 1 ((A a) ⊗ₜ[ℂ] (1 : ℂ)) := by
  have hx' : (x : fockSector Hs 1) = sectorEmb Hs 1 ((a : Hs.carrier) ⊗ₜ[ℂ] (1 : ℂ)) := by
    rw [hx, inclPow_one]
  calc (cbosonicSectorOp Hs D A 1 x : fockSector Hs 1)
      = fockSectorOp Hs D A 1
          (redIncl (cbosonicProj Hs 1) (fockSectorDom Hs D 1) x) := by
        rw [cbosonicSectorOp, redOp_coe]
    _ = sectorEmb Hs 1 (sectorOp Hs D A 1
          ⟨(a : Hs.carrier) ⊗ₜ[ℂ] (1 : ℂ), ⟨a ⊗ₜ[ℂ] (1 : ℂ), rfl⟩⟩) := by
        refine pushOp_apply (sectorEmb Hs 1) (sectorOp Hs D A 1) _ _ ?_
        rw [redIncl_coe]
        exact hx'
    _ = sectorEmb Hs 1 ((A a) ⊗ₜ[ℂ] (1 : ℂ)) := by
        rw [sectorOp_one]

end OneParticle

section Model

variable {d k r : ℕ} (M : Model d k r)

/-- **The shift law for the scalar outer Hamiltonian**: `dΓ(h + c·1) = dΓ(h) + c·N_out`
on the completed symmetric outer Fock core, where `N_out` is `outerNumber`. -/
theorem outerHam_add_const (c : ℝ)
    (x : hbosonicFockDom (L2dSpace d) (polyGaussCore (d := d))) :
    hbosonicFockOp (L2dSpace d) (polyGaussCore (d := d))
        (M.innerHam + (c : ℂ) • (polyGaussCore (d := d)).subtype) x
      = M.outerHam x
        + (c : ℂ) • outerNumber (L2dSpace d) (polyGaussCore (d := d)) x :=
  hbosonicFockOp_add_scalar (Hs := L2dSpace d) (D := polyGaussCore (d := d)) M.innerHam c x

/-- The degree-one component of the outer core, for a one-particle core vector. -/
private def oneParticleComponent (u : polyGaussCore (d := d)) :
    redDom (cbosonicProj (L2dSpace d) 1)
      (fockSectorDom (L2dSpace d) (polyGaussCore (d := d)) 1) := by
  let Hs := L2dSpace d
  let D := polyGaussCore (d := d)
  let z := inclPow Hs D 1 (u ⊗ₜ[ℂ] (1 : ℂ))
  have hz : z ∈ sectorDom Hs D 1 := ⟨u ⊗ₜ[ℂ] (1 : ℂ), rfl⟩
  refine ⟨⟨sectorEmb Hs 1 z, (mem_cbosonicSector_iff Hs 1).mpr ?_⟩,
    mem_pushDom (sectorEmb Hs 1) (⟨z, hz⟩ : sectorDom Hs D 1)⟩
  intro σ
  rw [Subsingleton.elim σ 1, (cpermRep Hs 1).act_one]

/-- The one-particle outer state determined by a one-particle core vector. -/
def oneParticle (u : polyGaussCore (d := d)) :
    hbosonicFockDom (L2dSpace d) (polyGaussCore (d := d)) :=
  ⟨lp.single (E := fun n => ↥(sector (cbosonicProj (L2dSpace d) n))) 2 1
      (oneParticleComponent u).val,
    single_mem_dsCore (D := fun n =>
      redDom (cbosonicProj (L2dSpace d) n)
        (fockSectorDom (L2dSpace d) (polyGaussCore (d := d)) n)) 1 (oneParticleComponent u)⟩

set_option maxHeartbeats 1000000 in
-- the component comparison unfolds the outer `dsOp` at degree one
/-- **The one-particle sector**: in degree one the outer Hamiltonian acts as the
one-particle Hamiltonian `M.innerHam`. -/
theorem outerHam_oneParticle_eq (u : polyGaussCore (d := d)) :
    ((M.outerHam (oneParticle u) : hbosonicFock (L2dSpace d)) 1 :
        fockSector (L2dSpace d) 1)
      = sectorEmb (L2dSpace d) 1 ((M.innerHam u) ⊗ₜ[ℂ] (1 : ℂ)) := by
  have h₁ : ((oneParticle u : hbosonicFock (L2dSpace d)) 1)
      = (oneParticleComponent u).val := by
    simp [oneParticle]
  have hx : ((⟨(oneParticle u : hbosonicFock (L2dSpace d)) 1,
        (oneParticle u).2.2 1⟩ :
      redDom (cbosonicProj (L2dSpace d) 1)
        (fockSectorDom (L2dSpace d) (polyGaussCore (d := d)) 1)) :
          fockSector (L2dSpace d) 1)
      = sectorEmb (L2dSpace d) 1
          (inclPow (L2dSpace d) (polyGaussCore (d := d)) 1 (u ⊗ₜ[ℂ] (1 : ℂ))) := by
    change ((oneParticle u : hbosonicFock (L2dSpace d)) 1 : fockSector (L2dSpace d) 1)
      = sectorEmb (L2dSpace d) 1
          (inclPow (L2dSpace d) (polyGaussCore (d := d)) 1 (u ⊗ₜ[ℂ] (1 : ℂ)))
    rw [h₁]
    rfl
  exact cbosonicSectorOp_oneParticle (Hs := L2dSpace d) (D := polyGaussCore (d := d))
    M.innerHam u ⟨(oneParticle u : hbosonicFock (L2dSpace d)) 1, (oneParticle u).2.2 1⟩ hx

end Model

end

end BookProof.Phi4.Model
