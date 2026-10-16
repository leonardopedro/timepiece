import Mathlib
import BookProof.ChapterScalaronDensitizedTransfer

/-!
# QG-D-C.2 / QG-D-C.3 — the assembled (kinetic + potential + ghost + gauge-fixing) gravity
Hamiltonian through the half-density unitary

`CONSOLIDATED_PLAN.md` §"2026-10-15b", rows QG-D-C.2 and QG-D-C.3 (and the honest status of
QG-D-C.1).

The 2026-08-24 scope clarification fixes the target as the **full** gauge-fixed
Hamiltonian, not the potential alone.  This module packages the four constituents and runs
the transfer for their sum:

* `QgPieces D` — kinetic, potential, ghost and gauge-fixing terms, four symmetric operators
  on a common domain `D`, and `QgPieces.total` their sum (`total_isSymmetricDom`);
* `assembled_transfer` — for **any** unitary `W` carrying the physical domain onto the
  densitized one and intertwining the four pieces *termwise*, vanishing adjoint deficiency
  of the densitized total gives it for the physical total;
* **`qg_assembled_halfDensity_transfer`** — the same at the constructed half-density unitary
  `halfDensityUnitary : L²((0,∞), de) ≃ₗᵢ[ℂ] L²((0,∞), 2y dy)`;
* `confPieces_phys`, `confPieces_dens`, **`qg_assembled_conformal_hasZeroDeficiencyOn`** — the
  assembly is not vacuous: the conformal-mode instance (potential `V₃`, the other three
  terms switched off) satisfies every hypothesis, including the flat one, and its physical
  total has vanishing deficiency unconditionally;
* **`qg_assembled_stone_flow_of_flat`** (QG-D-C.3) — the transferred statement feeds the
  Stone bridge: the physical assembled Hamiltonian then generates a complete unitary flow.

## QG-D-C.1 — the one open row

The flat-side hypothesis `hflat` of `qg_assembled_halfDensity_transfer` — vanishing
deficiency of the densitized assembled operator, whose kinetic term is the flat
d'Alembertian `(1/16)Σ∂² − (1/24)∂_y²` on the continuum `L²(ℝ⁸⁴)` — is exactly the continuum
finite-speed / unique-continuation input of `strichartz_esa_of_finiteSpeed` (route R1) or the
fiberwise Faris–Lavine input of `qg_esa_of_farisLavine` (route R2).  It is **not**
discharged here; it enters only as the explicit hypothesis `hflat`.  This is the one row the
plan allows to remain open.
-/

namespace BookProof.QgAssembledTransfer

open MeasureTheory
open BookProof.FarisLavine BookProof.NavierStokesFlow BookProof.NavierStokesFlow.FullEsa
open BookProof.QuantumGravityHalfDensity BookProof.ScalaronDensitized

noncomputable section

/-! ## 1. The four constituents and their sum -/

section Pieces

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- **The constituents of the gauge-fixed gravity Hamiltonian** on a common domain `D`:
kinetic, potential, Faddeev–Popov ghost and gauge-fixing terms, each symmetric. -/
structure QgPieces (D : Submodule ℂ E) where
  /-- The kinetic term. -/
  kinetic : D →ₗ[ℂ] D
  /-- The potential term. -/
  potential : D →ₗ[ℂ] D
  /-- The ghost term. -/
  ghost : D →ₗ[ℂ] D
  /-- The gauge-fixing term. -/
  gaugeFix : D →ₗ[ℂ] D
  kinetic_symm : IsSymmetricDom kinetic
  potential_symm : IsSymmetricDom potential
  ghost_symm : IsSymmetricDom ghost
  gaugeFix_symm : IsSymmetricDom gaugeFix

namespace QgPieces

variable {D : Submodule ℂ E} (P : QgPieces D)

/-- **The assembled Hamiltonian** `kinetic + potential + ghost + gauge-fixing`. -/
def total : D →ₗ[ℂ] D := P.kinetic + P.potential + P.ghost + P.gaugeFix

theorem total_isSymmetricDom : IsSymmetricDom P.total :=
  ((P.kinetic_symm.add P.potential_symm).add P.ghost_symm).add P.gaugeFix_symm

end QgPieces

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- **The assembled transfer.**  If the unitary `W` carries the physical domain `D` onto the
densitized domain `D'` and intertwines the four constituents termwise, then vanishing adjoint
deficiency of the densitized assembled Hamiltonian gives it for the physical one. -/
theorem assembled_transfer (W : F ≃ₗᵢ[ℂ] G) {D : Submodule ℂ F} {D' : Submodule ℂ G}
    (P : QgPieces D) (P' : QgPieces D')
    (hmap : ∀ x : D, W (x : F) ∈ D') (hsurj : ∀ y : D', ∃ x : D, W (x : F) = (y : G))
    (hK : ∀ x : D, (P'.kinetic ⟨W (x : F), hmap x⟩ : G) = W (P.kinetic x : F))
    (hV : ∀ x : D, (P'.potential ⟨W (x : F), hmap x⟩ : G) = W (P.potential x : F))
    (hGh : ∀ x : D, (P'.ghost ⟨W (x : F), hmap x⟩ : G) = W (P.ghost x : F))
    (hGF : ∀ x : D, (P'.gaugeFix ⟨W (x : F), hmap x⟩ : G) = W (P.gaugeFix x : F))
    (hflat : HasZeroDeficiencyOn D' P'.total) : HasZeroDeficiencyOn D P.total := by
  refine BookProof.QuantumGravityDensitized.densitized_hasZeroDeficiencyOn_transfer W hmap
    hsurj (fun x => ?_) hflat
  simp only [QgPieces.total, LinearMap.add_apply, Submodule.coe_add, map_add, hK, hV, hGh, hGF]

end Pieces

/-! ## 2. At the constructed half-density unitary -/

/-- **QG-D-C.2.**  The assembled transfer at the constructed half-density unitary
`halfDensityUnitary`: termwise intertwining plus vanishing deficiency of the densitized
(flat) assembled Hamiltonian give vanishing deficiency of the physical assembled one. -/
theorem qg_assembled_halfDensity_transfer
    {D : Submodule ℂ (Lp ℂ 2 physMeasure)} {D' : Submodule ℂ (Lp ℂ 2 qgSrcMeasure)}
    (P : QgPieces D) (P' : QgPieces D')
    (hmap : ∀ x : D, halfDensityUnitary (x : Lp ℂ 2 physMeasure) ∈ D')
    (hsurj : ∀ y : D', ∃ x : D,
      halfDensityUnitary (x : Lp ℂ 2 physMeasure) = (y : Lp ℂ 2 qgSrcMeasure))
    (hK : ∀ x : D, (P'.kinetic ⟨halfDensityUnitary (x : Lp ℂ 2 physMeasure), hmap x⟩ :
      Lp ℂ 2 qgSrcMeasure) = halfDensityUnitary (P.kinetic x : Lp ℂ 2 physMeasure))
    (hV : ∀ x : D, (P'.potential ⟨halfDensityUnitary (x : Lp ℂ 2 physMeasure), hmap x⟩ :
      Lp ℂ 2 qgSrcMeasure) = halfDensityUnitary (P.potential x : Lp ℂ 2 physMeasure))
    (hGh : ∀ x : D, (P'.ghost ⟨halfDensityUnitary (x : Lp ℂ 2 physMeasure), hmap x⟩ :
      Lp ℂ 2 qgSrcMeasure) = halfDensityUnitary (P.ghost x : Lp ℂ 2 physMeasure))
    (hGF : ∀ x : D, (P'.gaugeFix ⟨halfDensityUnitary (x : Lp ℂ 2 physMeasure), hmap x⟩ :
      Lp ℂ 2 qgSrcMeasure) = halfDensityUnitary (P.gaugeFix x : Lp ℂ 2 physMeasure))
    (hflat : HasZeroDeficiencyOn D' P'.total) : HasZeroDeficiencyOn D P.total :=
  assembled_transfer halfDensityUnitary P P' hmap hsurj hK hV hGh hGF hflat

/-! ## 3. The conformal-mode instance: the assembly is not vacuous -/

section Conformal

variable (M alpha : ℝ)

/-- The physical conformal-mode constituents: potential `V₃(e)`, other terms off. -/
def confPieces_phys : QgPieces (physConfCore M alpha) where
  kinetic := 0
  potential := physConfOp M alpha
  ghost := 0
  gaugeFix := 0
  kinetic_symm := IsSymmetricDom.zero
  potential_symm := physConfOp_symmetricOn M alpha
  ghost_symm := IsSymmetricDom.zero
  gaugeFix_symm := IsSymmetricDom.zero

/-- The densitized conformal-mode constituents: potential `V₃(y²)`, other terms off. -/
def confPieces_dens : QgPieces (densConfCore M alpha) where
  kinetic := 0
  potential := densConfOp M alpha
  ghost := 0
  gaugeFix := 0
  kinetic_symm := IsSymmetricDom.zero
  potential_symm := densConfOp_symmetricOn M alpha
  ghost_symm := IsSymmetricDom.zero
  gaugeFix_symm := IsSymmetricDom.zero

theorem confPieces_dens_total : (confPieces_dens M alpha).total = densConfOp M alpha := by
  simp [QgPieces.total, confPieces_dens]

/-- **The assembled transfer, instantiated with every hypothesis discharged** for the
conformal-mode constituents. -/
theorem qg_assembled_conformal_hasZeroDeficiencyOn :
    HasZeroDeficiencyOn (physConfCore M alpha) (confPieces_phys M alpha).total := by
  refine qg_assembled_halfDensity_transfer (confPieces_phys M alpha) (confPieces_dens M alpha)
    (halfDensityUnitary_mem_densConfCore M alpha)
    (halfDensityUnitary_densConfCore_surjective M alpha)
    (fun x => by simp [confPieces_phys, confPieces_dens])
    (halfDensityUnitary_intertwines M alpha)
    (fun x => by simp [confPieces_phys, confPieces_dens])
    (fun x => by simp [confPieces_phys, confPieces_dens]) ?_
  rw [confPieces_dens_total]
  exact densConf_hasZeroDeficiencyOn M alpha

end Conformal

/-! ## 4. QG-D-C.3: into the Stone bridge -/

open BookProof.ChapterStoneResolvent BookProof.StoneBridge BookProof.EsaClosure in
/-- **QG-D-C.3.**  Under the transfer hypotheses (in particular the flat input `hflat` of
QG-D-C.1), the physical assembled Hamiltonian is essentially self-adjoint and generates a
complete unitary (Stone) flow. -/
theorem qg_assembled_stone_flow_of_flat
    {D : Submodule ℂ (Lp ℂ 2 physMeasure)} {D' : Submodule ℂ (Lp ℂ 2 qgSrcMeasure)}
    (hD : Dense (D : Set (Lp ℂ 2 physMeasure)))
    (P : QgPieces D) (P' : QgPieces D')
    (hmap : ∀ x : D, halfDensityUnitary (x : Lp ℂ 2 physMeasure) ∈ D')
    (hsurj : ∀ y : D', ∃ x : D,
      halfDensityUnitary (x : Lp ℂ 2 physMeasure) = (y : Lp ℂ 2 qgSrcMeasure))
    (hK : ∀ x : D, (P'.kinetic ⟨halfDensityUnitary (x : Lp ℂ 2 physMeasure), hmap x⟩ :
      Lp ℂ 2 qgSrcMeasure) = halfDensityUnitary (P.kinetic x : Lp ℂ 2 physMeasure))
    (hV : ∀ x : D, (P'.potential ⟨halfDensityUnitary (x : Lp ℂ 2 physMeasure), hmap x⟩ :
      Lp ℂ 2 qgSrcMeasure) = halfDensityUnitary (P.potential x : Lp ℂ 2 physMeasure))
    (hGh : ∀ x : D, (P'.ghost ⟨halfDensityUnitary (x : Lp ℂ 2 physMeasure), hmap x⟩ :
      Lp ℂ 2 qgSrcMeasure) = halfDensityUnitary (P.ghost x : Lp ℂ 2 physMeasure))
    (hGF : ∀ x : D, (P'.gaugeFix ⟨halfDensityUnitary (x : Lp ℂ 2 physMeasure), hmap x⟩ :
      Lp ℂ 2 qgSrcMeasure) = halfDensityUnitary (P.gaugeFix x : Lp ℂ 2 physMeasure))
    (hflat : HasZeroDeficiencyOn D' P'.total) :
    ∃ (T : UnboundedSelfAdjoint (Lp ℂ 2 physMeasure))
      (U : ℝ → (Lp ℂ 2 physMeasure →L[ℂ] Lp ℂ 2 physMeasure)),
      IsSelfAdjointExtension (D.subtype.comp P.total) T.op ∧ IsStoneFlow T U :=
  exists_stone_flow_of_esa _ hD (fun x y => P.total_isSymmetricDom x y)
    ((essentiallySelfAdjointOn_iff_hasZeroDeficiencyOn _ _).2
      (qg_assembled_halfDensity_transfer P P' hmap hsurj hK hV hGh hGF hflat))

end

end BookProof.QgAssembledTransfer
