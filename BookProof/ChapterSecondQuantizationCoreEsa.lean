import Mathlib
import BookProof.ChapterTensorGraphCore
import BookProof.ChapterDirectSumEsa

/-!
# Second quantization over an essentially self-adjoint one-particle operator

This module assembles the two instruments of the *core transfer* route into the second
quantization theorem for a one-particle operator `A` that is only **essentially** self-adjoint
on the one-particle core `D`:

1. the **core transfer principle** of `BookProof/ChapterGraphCoreTransfer.lean`: essential
   self-adjointness passes from a domain to any graph-norm dense subspace of it;
2. the **multilinear core estimate** of `BookProof/ChapterTensorGraphCore.lean`: if `D` is a
   core for `A`, then `D^{⊗n}` is a core for the sector derivation `dΓ(A)⁽ⁿ⁾` on `D₂^{⊗n}`;
3. the ℓ²-**direct sum** instrument `BookProof.DirectSumEsa.dsOp_essentiallySelfAdjointOn`,
   already in the tree: fibrewise essential self-adjointness glues along the particle-number
   decomposition.

The Fock space is the ℓ²-direct sum of the completed sectors
`𝓕ₙ = completion of H^{⊗n}`, and the finite-particle domain over the core is the algebraic
direct sum of the images of `D^{⊗n}` — `dsCore` applied to the sector cores.  This is the
domain `𝓕_fin(D)` of the statement.

The one hypothesis carried, sector by sector, is essential self-adjointness of `dΓ(A)⁽ⁿ⁾` on
the *full* tensor power `D₂^{⊗n}` of the domain of the closure — the statement for a
self-adjoint one-particle operator, whose proof (Nelson's analytic-vector or invariant-domain
argument) is a separate matter and is **not** proved here.  What is proved here is exactly the
step the essentially-self-adjoint hypothesis obstructs: the passage from the domain `D₂` of
the closure to the small core `D`, on every sector and then on the whole Fock space.

## Contents

* `fockSector` — the `n`-particle sector, the completion of `H^{⊗n}`;
* `fockSectorDom`, `fockSectorCore`, `fockSectorOp` — the sector domain `D₂^{⊗n}`, the sector
  core `D^{⊗n}` and the sector derivation inside it;
* `essentiallySelfAdjointOn_fockSectorCore` — sectorwise core transfer;
* `dGamma_essentiallySelfAdjointOn_fockCore` — **the main theorem**: `dΓ(A)` is essentially
  self-adjoint on the finite-particle domain over the core `D`.

Nothing is assumed beyond the stated sector hypothesis: the module contains no `axiom` and no
`sorry`.
-/

namespace BookProof.SecondQuantizationCore

open scoped TensorProduct
open BookProof.FarisLavine BookProof.GraphCore BookProof.TensorCore BookProof.DirectSumEsa

noncomputable section

variable (Hs : IPSpace) (D₂ : Submodule ℂ Hs.carrier) (A : D₂ →ₗ[ℂ] Hs.carrier)
  (D : Submodule ℂ Hs.carrier)

/-- The `n`-particle sector of the Fock space: the Hilbert space completion of the algebraic
tensor power `H^{⊗n}`. -/
abbrev fockSector (n : ℕ) : Type := UniformSpace.Completion ((Hs.pow n).carrier)

/-- The isometric embedding of the algebraic tensor power into its completion. -/
def sectorEmb (n : ℕ) : (Hs.pow n).carrier →ₗᵢ[ℂ] fockSector Hs n :=
  UniformSpace.Completion.toComplₗᵢ

/-- The domain of the sector derivation inside the `n`-particle sector: the image of
`D₂^{⊗n}`. -/
def fockSectorDom (n : ℕ) : Submodule ℂ (fockSector Hs n) :=
  pushDom (sectorEmb Hs n) (sectorDom Hs D₂ n)

/-- The finite-particle core inside the `n`-particle sector: the image of `D^{⊗n}`. -/
def fockSectorCore (n : ℕ) : Submodule ℂ (fockSector Hs n) :=
  pushDom (sectorEmb Hs n) (sectorCore Hs D₂ D n)

/-- The sector derivation `dΓ(A)⁽ⁿ⁾` inside the `n`-particle sector. -/
def fockSectorOp (n : ℕ) : fockSectorDom Hs D₂ n →ₗ[ℂ] fockSector Hs n :=
  pushOp (sectorEmb Hs n) (sectorOp Hs D₂ A n)

theorem fockSectorCore_le_fockSectorDom (n : ℕ) :
    fockSectorCore Hs D₂ D n ≤ fockSectorDom Hs D₂ n :=
  pushDom_mono _ (sectorCore_le_sectorDom Hs D₂ D n)

/-- The sector core is a core for the sector derivation, inside the completed sector. -/
theorem isGraphCore_fockSectorCore (hcore : IsGraphCore D A) (n : ℕ) :
    IsGraphCore (fockSectorCore Hs D₂ D n) (fockSectorOp Hs D₂ A n) :=
  isGraphCore_pushOp _ _ (isGraphCore_sectorCore Hs D₂ A D hcore n)

/-- **Sectorwise core transfer.**  If the sector derivation is essentially self-adjoint on the
tensor power of the domain of the closure, it is essentially self-adjoint on the tensor power
of the core. -/
theorem essentiallySelfAdjointOn_fockSectorCore (hcore : IsGraphCore D A) (n : ℕ)
    (hesa : EssentiallySelfAdjointOn (fockSectorDom Hs D₂ n) (fockSectorOp Hs D₂ A n)) :
    EssentiallySelfAdjointOn (fockSectorCore Hs D₂ D n)
      (restrictOp (fockSectorOp Hs D₂ A n) (fockSectorCore_le_fockSectorDom Hs D₂ D n)) :=
  essentiallySelfAdjointOn_of_graphCore _ _ (isGraphCore_fockSectorCore Hs D₂ A D hcore n) hesa

/-- The sector derivation is symmetric inside the completed sector, whenever the
one-particle operator is symmetric. -/
theorem symmetricOn_fockSectorOp (hA : SymmetricOn D₂ A) (n : ℕ) :
    SymmetricOn (fockSectorDom Hs D₂ n) (fockSectorOp Hs D₂ A n) :=
  symmetricOn_pushOp _ _ (symmetricOn_sectorOp Hs D₂ A hA n)

/-- **The second quantization `dΓ(A)` on the finite-particle domain over the core `D`.** -/
def dGammaCoreOp :
    dsCore (fun n : ℕ => fockSectorCore Hs D₂ D n) →ₗ[ℂ] lp (fun n : ℕ => fockSector Hs n) 2 :=
  dsOp (fun n : ℕ =>
    restrictOp (fockSectorOp Hs D₂ A n) (fockSectorCore_le_fockSectorDom Hs D₂ D n))

/-- **Main theorem (essential self-adjointness of `dΓ(A)` over a core).**  Let `A` be a
one-particle operator with domain `D₂` and let `D ≤ D₂` be a core for `A` in the graph norm —
the situation of an operator that is only *essentially* self-adjoint on `D`, with `D₂` the
domain of its closure.  If, sector by sector, the derivation `dΓ(A)⁽ⁿ⁾` is essentially
self-adjoint on the tensor power `D₂^{⊗n}`, then `dΓ(A)` is essentially self-adjoint on the
finite-particle domain `𝓕_fin(D)` built from the core alone. -/
theorem dGamma_essentiallySelfAdjointOn_fockCore (hcore : IsGraphCore D A)
    (hsector : ∀ n : ℕ,
      EssentiallySelfAdjointOn (fockSectorDom Hs D₂ n) (fockSectorOp Hs D₂ A n)) :
    EssentiallySelfAdjointOn (dsCore (fun n : ℕ => fockSectorCore Hs D₂ D n))
      (dGammaCoreOp Hs D₂ A D) :=
  dsOp_essentiallySelfAdjointOn _
    (fun n => essentiallySelfAdjointOn_fockSectorCore Hs D₂ A D hcore n (hsector n))

/-- `dΓ(A)` is symmetric on the finite-particle domain over the core. -/
theorem symmetricOn_dGammaCoreOp (hA : SymmetricOn D₂ A) :
    SymmetricOn (dsCore (fun n : ℕ => fockSectorCore Hs D₂ D n)) (dGammaCoreOp Hs D₂ A D) :=
  dsOp_symmetricOn _
    (fun n => symmetricOn_restrictOp _ _ (symmetricOn_fockSectorOp Hs D₂ A hA n))

/-! ## Non-vacuity -/

/-- The finite-particle domain over the core is not the zero space: a nonzero vector of the
one-particle core `D` produces a nonzero one-particle state in `dsCore`. -/
theorem exists_ne_zero_mem_dGammaCoreDomain (hD : D ≤ D₂) {a : Hs.carrier} (haD : a ∈ D)
    (ha0 : a ≠ 0) :
    ∃ f ∈ dsCore (fun n : ℕ => fockSectorCore Hs D₂ D n), f ≠ 0 := by
  classical
  obtain ⟨x, hx, hx0⟩ := exists_ne_zero_mem_sectorCore_one Hs D₂ D hD haD ha0
  refine ⟨lp.single 2 1 (sectorEmb Hs 1 x), ⟨?_, ?_⟩, ?_⟩
  · refine Set.Finite.subset (Set.finite_singleton 1) (fun i hi => ?_)
    simp only [Set.mem_setOf_eq, lp.single_apply] at hi
    by_contra hne
    exact hi (Pi.single_eq_of_ne (by simpa using hne) _)
  · intro i
    rw [lp.single_apply]
    by_cases hi : i = 1
    · subst hi
      rw [Pi.single_eq_same]
      exact mem_pushDom (sectorEmb Hs 1) (⟨x, hx⟩ : sectorCore Hs D₂ D 1)
    · rw [Pi.single_eq_of_ne hi]
      exact Submodule.zero_mem _
  · intro hzero
    have hnorm : ‖lp.single 2 1 (sectorEmb Hs 1 x)‖ = ‖x‖ := by
      rw [lp.norm_single (by norm_num) 1 (sectorEmb Hs 1 x), (sectorEmb Hs 1).norm_map]
    rw [hzero, norm_zero] at hnorm
    exact hx0 (norm_eq_zero.mp hnorm.symm)

end

end BookProof.SecondQuantizationCore
