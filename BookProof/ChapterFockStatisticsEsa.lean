import Mathlib
import BookProof.ChapterPermutationSectorEsa
import BookProof.ChapterEsaOneParticleDGamma
import BookProof.ChapterDirectSumEsa

/-!
# The bosonic and the fermionic Fock space

`BookProof.PermSector` proves that the sector derivation `dΓ(A)⁽ⁿ⁾` is essentially
self-adjoint on the symmetric and on the antisymmetric part of `H^{⊗n}` **as soon as it is
essentially self-adjoint on the whole of `D₂^{⊗n}`**, and it proves nothing about the direct
sum over `n`.  This module removes both restrictions.

## What is proved

* `deficiencyTrivialAt_of_pushOp`, `essentiallySelfAdjointOn_of_pushOp` — essential
  self-adjointness descends along an isometry: what holds in the completion holds in the
  incomplete space it completes.
* `essentiallySelfAdjointOn_sectorDom_of_esa` — **the sector hypothesis, discharged**.  For a
  symmetric, essentially self-adjoint one-particle operator `A` on a dense domain `D` of a
  Hilbert space, `dΓ(A)⁽ⁿ⁾` *is* essentially self-adjoint on `D^{⊗n}`, for every `n`.  It is
  obtained by pulling `BookProof.EsaOneParticle.essentiallySelfAdjointOn_fockSectorDom_esa`
  back from the completed sector along `sectorEmb`.
* `essentiallySelfAdjointOn_bosonic_of_esa`, `essentiallySelfAdjointOn_fermionic_of_esa`,
  and the two core versions — the four statements of `BookProof.PermSector` with the
  sectorwise hypothesis removed: only the one-particle hypotheses remain.
* `bosonicFock`, `fermionicFock` — the two **Fock spaces**: the `ℓ²` direct sum over `n` of
  the symmetric, respectively the antisymmetric, part of `H^{⊗n}`; `bosonicFockDom`,
  `bosonicFockOp` (and the fermionic twins) — the algebraic direct sum of the sector domains
  and the second quantization `dΓ(A)` on it.
* **`bosonicFock_esa`**, **`fermionicFock_esa`** — the headline: `dΓ(A)` is essentially
  self-adjoint on the symmetric Fock space and on the antisymmetric Fock space, with
  `bosonicFock_symmetricOn` / `fermionicFock_symmetricOn` the matching symmetry statements,
  and `bosonicFockOp_single` / `fermionicFockOp_single` the identification of the operator on
  a single-particle-number state with the sector operator of `BookProof.PermSector`.

Nothing is assumed: the module contains no `axiom` and no `sorry`.
-/

namespace BookProof.FockStatistics

open scoped TensorProduct ENNReal
open BookProof.FarisLavine BookProof.GraphCore BookProof.ReducedEsa BookProof.TensorCore
open BookProof.GroupAverage BookProof.TensorPerm BookProof.PermSector
open BookProof.SecondQuantizationCore BookProof.EsaOneParticle BookProof.DirectSumEsa

noncomputable section

/-! ## 1. Essential self-adjointness descends along an isometry -/

section Pullback

variable {F G : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
  [NormedAddCommGroup G] [InnerProductSpace ℂ G]

/-- Triviality of a deficiency space of the transported operator `U T U⁻¹` forces triviality
of the same deficiency space of `T`: a deficiency vector of `T` is carried by `U` to one of
the transport. -/
theorem deficiencyTrivialAt_of_pushOp (U : F →ₗᵢ[ℂ] G) {D : Submodule ℂ F} (T : D →ₗ[ℂ] F)
    {z : ℂ} (h : DeficiencyTrivialAt (pushDom U D) (pushOp U T) z) :
    DeficiencyTrivialAt D T z := by
  intro w hw
  have hUw : U w = 0 := by
    refine h (U w) (fun V => ?_)
    obtain ⟨v₀, hv₀, hV⟩ := V.2
    have hx : (V : G) = U ((⟨v₀, hv₀⟩ : D) : F) := hV.symm
    rw [pushOp_apply U T V ⟨v₀, hv₀⟩ hx, hx, U.inner_map_map, U.inner_map_map]
    exact hw ⟨v₀, hv₀⟩
  exact U.injective (by rw [hUw, map_zero])

/-- **Essential self-adjointness descends along an isometry.** -/
theorem essentiallySelfAdjointOn_of_pushOp (U : F →ₗᵢ[ℂ] G) {D : Submodule ℂ F}
    (T : D →ₗ[ℂ] F) (h : EssentiallySelfAdjointOn (pushDom U D) (pushOp U T)) :
    EssentiallySelfAdjointOn D T :=
  ⟨deficiencyTrivialAt_of_pushOp U T h.1, deficiencyTrivialAt_of_pushOp U T h.2⟩

end Pullback

/-! ## 2. The sector hypothesis, discharged -/

section Sector

variable {Hs : IPSpace} [CompleteSpace Hs.carrier] {D : Submodule ℂ Hs.carrier}
  (A : D →ₗ[ℂ] Hs.carrier) (hdense : Dense (D : Set Hs.carrier)) (hsym : SymmetricOn D A)
  (hesa : EssentiallySelfAdjointOn D A)

include hdense hsym hesa in
/-- **The sector derivation is essentially self-adjoint on the tensor power of the
one-particle domain.**  This is the hypothesis that `BookProof.PermSector` carried through
its reduction; for an essentially self-adjoint one-particle operator on a dense domain of a
Hilbert space it is a theorem. -/
theorem essentiallySelfAdjointOn_sectorDom_of_esa (n : ℕ) :
    EssentiallySelfAdjointOn (sectorDom Hs D n) (sectorOp Hs D A n) :=
  essentiallySelfAdjointOn_of_pushOp (sectorEmb Hs n) _
    (essentiallySelfAdjointOn_fockSectorDom_esa A hdense hsym hesa n)

end Sector

/-! ## 3. The two sectors of `H^{⊗n}`, unconditionally -/

section Statistics

variable (Hs : IPSpace) (D : Submodule ℂ Hs.carrier) (A : D →ₗ[ℂ] Hs.carrier)

/-- The sector derivation reduced to the **symmetric** part of `H^{⊗n}`. -/
def bosonicSectorOp (n : ℕ) :
    redDom (bosonicProj Hs n) (sectorDom Hs D n) →ₗ[ℂ] sector (bosonicProj Hs n) :=
  redOp (sectorOp Hs D A n) (isReducingProjection_bosonicProj Hs n)
    ((permRep Hs n).commutes_avgProj
      (hD := permRep_mem_sectorDom Hs D n)
      (permRep_commutes_sectorDom Hs D A n))

/-- The sector derivation reduced to the **antisymmetric** part of `H^{⊗n}`. -/
def fermionicSectorOp (n : ℕ) :
    redDom (fermionicProj Hs n) (sectorDom Hs D n) →ₗ[ℂ] sector (fermionicProj Hs n) :=
  redOp (sectorOp Hs D A n) (isReducingProjection_fermionicProj Hs n)
    ((signRep Hs n).commutes_avgProj
      (hD := signRep_mem_sectorDom Hs D n)
      (signRep_commutes_sectorDom Hs D A n))

variable (D₀ : Submodule ℂ Hs.carrier)

/-- The sector derivation reduced to the symmetrized tensor power of a one-particle core. -/
def bosonicCoreOp (n : ℕ) :
    redDom (bosonicProj Hs n) (sectorCore Hs D D₀ n) →ₗ[ℂ] sector (bosonicProj Hs n) :=
  redOp (restrictOp (sectorOp Hs D A n) (sectorCore_le_sectorDom Hs D D₀ n))
    (isReducingProjection_bosonicProj Hs n)
    ((permRep Hs n).commutes_avgProj
      (hD := permRep_mem_sectorCore Hs D D₀ n)
      (permRep_commutes_sectorCore Hs D A D₀ n))

/-- The sector derivation reduced to the antisymmetrized tensor power of a one-particle
core. -/
def fermionicCoreOp (n : ℕ) :
    redDom (fermionicProj Hs n) (sectorCore Hs D D₀ n) →ₗ[ℂ] sector (fermionicProj Hs n) :=
  redOp (restrictOp (sectorOp Hs D A n) (sectorCore_le_sectorDom Hs D D₀ n))
    (isReducingProjection_fermionicProj Hs n)
    ((signRep Hs n).commutes_avgProj
      (hD := signRep_mem_sectorCore Hs D D₀ n)
      (signRep_commutes_sectorCore Hs D A D₀ n))

end Statistics

section StatisticsEsa

variable {Hs : IPSpace} [CompleteSpace Hs.carrier] {D : Submodule ℂ Hs.carrier}
  (A : D →ₗ[ℂ] Hs.carrier) (hdense : Dense (D : Set Hs.carrier)) (hsym : SymmetricOn D A)
  (hesa : EssentiallySelfAdjointOn D A)

include hdense hsym hesa in
/-- **The bosonic `n`-particle derivation is essentially self-adjoint**, with no sectorwise
hypothesis left: the one-particle operator is only assumed symmetric and essentially
self-adjoint on its dense domain. -/
theorem essentiallySelfAdjointOn_bosonic_of_esa (n : ℕ) :
    EssentiallySelfAdjointOn (redDom (bosonicProj Hs n) (sectorDom Hs D n))
      (bosonicSectorOp Hs D A n) :=
  essentiallySelfAdjointOn_bosonic Hs D A n
    (essentiallySelfAdjointOn_sectorDom_of_esa A hdense hsym hesa n)

include hdense hsym hesa in
/-- **The fermionic `n`-particle derivation is essentially self-adjoint**, with no sectorwise
hypothesis left. -/
theorem essentiallySelfAdjointOn_fermionic_of_esa (n : ℕ) :
    EssentiallySelfAdjointOn (redDom (fermionicProj Hs n) (sectorDom Hs D n))
      (fermionicSectorOp Hs D A n) :=
  essentiallySelfAdjointOn_fermionic Hs D A n
    (essentiallySelfAdjointOn_sectorDom_of_esa A hdense hsym hesa n)

variable {D₀ : Submodule ℂ Hs.carrier}

include hdense hsym hesa in
/-- The bosonic statement on the symmetrized tensor power of any one-particle core. -/
theorem essentiallySelfAdjointOn_bosonic_core_of_esa (hcore : IsGraphCore D₀ A) (n : ℕ) :
    EssentiallySelfAdjointOn (redDom (bosonicProj Hs n) (sectorCore Hs D D₀ n))
      (bosonicCoreOp Hs D A D₀ n) :=
  essentiallySelfAdjointOn_bosonic_core Hs D A D₀ n hcore
    (essentiallySelfAdjointOn_sectorDom_of_esa A hdense hsym hesa n)

include hdense hsym hesa in
/-- The fermionic statement on the antisymmetrized tensor power of any one-particle core. -/
theorem essentiallySelfAdjointOn_fermionic_core_of_esa (hcore : IsGraphCore D₀ A) (n : ℕ) :
    EssentiallySelfAdjointOn (redDom (fermionicProj Hs n) (sectorCore Hs D D₀ n))
      (fermionicCoreOp Hs D A D₀ n) :=
  essentiallySelfAdjointOn_fermionic_core Hs D A D₀ n hcore
    (essentiallySelfAdjointOn_sectorDom_of_esa A hdense hsym hesa n)

end StatisticsEsa

/-! ## 4. The Fock spaces -/

section Fock

variable (Hs : IPSpace) (D : Submodule ℂ Hs.carrier) (A : D →ₗ[ℂ] Hs.carrier)
  (D₀ : Submodule ℂ Hs.carrier)

/-- **The bosonic Fock space** over `H`: the `ℓ²` direct sum, over the particle number `n`,
of the symmetric part of `H^{⊗n}`. -/
abbrev bosonicFock : Type := lp (fun n : ℕ => ↥(sector (bosonicProj Hs n))) 2

/-- **The fermionic Fock space** over `H`: the `ℓ²` direct sum, over the particle number `n`,
of the antisymmetric part of `H^{⊗n}`. -/
abbrev fermionicFock : Type := lp (fun n : ℕ => ↥(sector (fermionicProj Hs n))) 2

/-- The domain of `dΓ(A)` on the bosonic Fock space: the algebraic direct sum of the
symmetric sector domains. -/
def bosonicFockDom : Submodule ℂ (bosonicFock Hs) :=
  dsCore (fun n : ℕ => redDom (bosonicProj Hs n) (sectorDom Hs D n))

/-- The domain of `dΓ(A)` on the fermionic Fock space. -/
def fermionicFockDom : Submodule ℂ (fermionicFock Hs) :=
  dsCore (fun n : ℕ => redDom (fermionicProj Hs n) (sectorDom Hs D n))

/-- **The second quantization `dΓ(A)` on the bosonic Fock space.** -/
def bosonicFockOp : bosonicFockDom Hs D →ₗ[ℂ] bosonicFock Hs :=
  dsOp (fun n : ℕ => bosonicSectorOp Hs D A n)

/-- **The second quantization `dΓ(A)` on the fermionic Fock space.** -/
def fermionicFockOp : fermionicFockDom Hs D →ₗ[ℂ] fermionicFock Hs :=
  dsOp (fun n : ℕ => fermionicSectorOp Hs D A n)

/-- The domain of `dΓ(A)` over a one-particle core, on the bosonic Fock space. -/
def bosonicFockCoreDom : Submodule ℂ (bosonicFock Hs) :=
  dsCore (fun n : ℕ => redDom (bosonicProj Hs n) (sectorCore Hs D D₀ n))

/-- The domain of `dΓ(A)` over a one-particle core, on the fermionic Fock space. -/
def fermionicFockCoreDom : Submodule ℂ (fermionicFock Hs) :=
  dsCore (fun n : ℕ => redDom (fermionicProj Hs n) (sectorCore Hs D D₀ n))

/-- `dΓ(A)` on the symmetric Fock space over a one-particle core. -/
def bosonicFockCoreOp : bosonicFockCoreDom Hs D D₀ →ₗ[ℂ] bosonicFock Hs :=
  dsOp (fun n : ℕ => bosonicCoreOp Hs D A D₀ n)

/-- `dΓ(A)` on the antisymmetric Fock space over a one-particle core. -/
def fermionicFockCoreOp : fermionicFockCoreDom Hs D D₀ →ₗ[ℂ] fermionicFock Hs :=
  dsOp (fun n : ℕ => fermionicCoreOp Hs D A D₀ n)

end Fock

section FockEsa

variable {Hs : IPSpace} [CompleteSpace Hs.carrier] {D : Submodule ℂ Hs.carrier}
  (A : D →ₗ[ℂ] Hs.carrier) (hdense : Dense (D : Set Hs.carrier)) (hsym : SymmetricOn D A)
  (hesa : EssentiallySelfAdjointOn D A)

omit [CompleteSpace Hs.carrier] in
include hsym in
/-- `dΓ(A)` is symmetric on the bosonic Fock space. -/
theorem bosonicFock_symmetricOn :
    SymmetricOn (bosonicFockDom Hs D) (bosonicFockOp Hs D A) :=
  dsOp_symmetricOn _ (fun n => symmetricOn_bosonic Hs D A n hsym)

omit [CompleteSpace Hs.carrier] in
include hsym in
/-- `dΓ(A)` is symmetric on the fermionic Fock space. -/
theorem fermionicFock_symmetricOn :
    SymmetricOn (fermionicFockDom Hs D) (fermionicFockOp Hs D A) :=
  dsOp_symmetricOn _ (fun n => symmetricOn_fermionic Hs D A n hsym)

include hdense hsym hesa in
/-- **`dΓ(A)` is essentially self-adjoint on the bosonic Fock space** — on the direct sum
over *all* particle numbers, not one sector at a time — as soon as the one-particle operator
is symmetric and essentially self-adjoint on its dense domain. -/
theorem bosonicFock_esa :
    EssentiallySelfAdjointOn (bosonicFockDom Hs D) (bosonicFockOp Hs D A) :=
  dsOp_essentiallySelfAdjointOn _
    (fun n => essentiallySelfAdjointOn_bosonic_of_esa A hdense hsym hesa n)

include hdense hsym hesa in
/-- **`dΓ(A)` is essentially self-adjoint on the fermionic Fock space.** -/
theorem fermionicFock_esa :
    EssentiallySelfAdjointOn (fermionicFockDom Hs D) (fermionicFockOp Hs D A) :=
  dsOp_essentiallySelfAdjointOn _
    (fun n => essentiallySelfAdjointOn_fermionic_of_esa A hdense hsym hesa n)

variable {D₀ : Submodule ℂ Hs.carrier}

include hdense hsym hesa in
/-- **`dΓ(A)` is essentially self-adjoint on the bosonic Fock space built from a one-particle
core.** -/
theorem bosonicFockCore_esa (hcore : IsGraphCore D₀ A) :
    EssentiallySelfAdjointOn (bosonicFockCoreDom Hs D D₀) (bosonicFockCoreOp Hs D A D₀) :=
  dsOp_essentiallySelfAdjointOn _
    (fun n => essentiallySelfAdjointOn_bosonic_core_of_esa A hdense hsym hesa hcore n)

include hdense hsym hesa in
/-- **`dΓ(A)` is essentially self-adjoint on the fermionic Fock space built from a
one-particle core.** -/
theorem fermionicFockCore_esa (hcore : IsGraphCore D₀ A) :
    EssentiallySelfAdjointOn (fermionicFockCoreDom Hs D D₀) (fermionicFockCoreOp Hs D A D₀) :=
  dsOp_essentiallySelfAdjointOn _
    (fun n => essentiallySelfAdjointOn_fermionic_core_of_esa A hdense hsym hesa hcore n)

end FockEsa

/-! ## 5. The Fock operator on a state of definite particle number -/

section Single

variable (Hs : IPSpace) (D : Submodule ℂ Hs.carrier) (A : D →ₗ[ℂ] Hs.carrier)

/-- On a state living in the `n`-particle sector the Fock operator is the bosonic sector
operator of `BookProof.PermSector`: the direct sum is particle-number conserving. -/
theorem bosonicFockOp_single (n : ℕ)
    (u : redDom (bosonicProj Hs n) (sectorDom Hs D n)) :
    (bosonicFockOp Hs D A ⟨lp.single 2 n ((u : sector (bosonicProj Hs n))),
        single_mem_dsCore (D := fun n : ℕ => redDom (bosonicProj Hs n) (sectorDom Hs D n))
          n u⟩ : bosonicFock Hs)
      = lp.single 2 n (bosonicSectorOp Hs D A n u) :=
  dsOp_single (fun n : ℕ => bosonicSectorOp Hs D A n) n u

/-- The fermionic twin. -/
theorem fermionicFockOp_single (n : ℕ)
    (u : redDom (fermionicProj Hs n) (sectorDom Hs D n)) :
    (fermionicFockOp Hs D A ⟨lp.single 2 n ((u : sector (fermionicProj Hs n))),
        single_mem_dsCore (D := fun n : ℕ => redDom (fermionicProj Hs n) (sectorDom Hs D n))
          n u⟩ : fermionicFock Hs)
      = lp.single 2 n (fermionicSectorOp Hs D A n u) :=
  dsOp_single (fun n : ℕ => fermionicSectorOp Hs D A n) n u

end Single

end

end BookProof.FockStatistics
