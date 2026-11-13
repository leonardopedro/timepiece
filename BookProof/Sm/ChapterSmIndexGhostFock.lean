/-
Copyright (c) 2026 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import BookProof.Sm.ChapterSmIndexGhostQuartet
import BookProof.Sm.ChapterSmBrstGhost

/-!
# The Fock side of the ghost sector

`HONEST_BOUNDARIES_SM` item (xii) said that to instantiate the index-restricted quartet on
`smBrstCharge` one still needs "an inner product on that Fock space".  Read literally that is
**wrong**: the fermionic Fock space of this corpus is

```
FermiFock n = ℓ²(Finset (Fin n)) = EuclideanSpace ℂ (Finset (Fin n)),
```

an `EuclideanSpace`, so it *is* an inner-product space, its occupation basis is orthonormal
(`occ_inner`), and the CAR creation and annihilation operators are adjoints for that product
(`inner_creat_left`, `inner_annih_left`, quoted from `ChapterSmCarAlgebra`).  No product
structure is missing; what is missing is an *identification* of the index complex with the
ghost sector of `smBrstCharge`.  This module proves the part of that identification that is
true, and records the part that is false.

**What is proved here.**

* `ghostMode_injective` — the twelve ghost modes are the last twelve coordinates of
  `Fin (m + 12)`, so `Fin 12 ↪ Fin (m + 12)` is a genuine injection of mode labels.
* `ghostVec_orthonormal` — the occupation vectors `|a⟩ = occ {ghostMode m a}` of those modes are
  an orthonormal system: the one-particle ghost sector is an *isometric* copy of
  `EuclideanSpace ℂ (Fin 12)`, which is the index pattern with one coordinate per ghost pair.
* `ghostCre_vac` — that copy is exactly the orbit of the Fock vacuum under the ghost creation
  operators, so the twelve modes the SM charge creates from the vacuum are the index pattern's
  ghost coordinates.
* `ghost_pairing` — the ghost/antighost pairing that the index model's metric `η` implements is
  the Fock adjunction `b_a = (c^a)†` restricted to this copy.

**What is not true.**  `smBrstCharge` is *not* the index complex at `n = 12`.  It is
`∑ a, χ_a G^a − ½ ∑ f χ β`, i.e. a degree-one derivation whose linear part mixes a ghost with a
*matter* bilinear and whose quadratic part creates the second ghost, so it does not preserve the
one-particle ghost sector: a single ghost is not mapped to a single antighost.  The
index-restricted quartet is therefore the *free* (one-particle) part of the ghost complex, an
isometric slice of the Fock space rather than a subcomplex of `smBrstCharge`; matching the two
still needs the b-ghost of the derivation, which is open and is what item (xii) should have
named.

Everything here is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmIndexGhostFock

open BookProof.SmCar
open BookProof.SmBrstGhost
open BookProof.SmIndexGhostQuartet

noncomputable section

/-! ## 1. The ℓ² product on the Fock space is already there -/

variable {n : ℕ}

/-- **The occupation basis is orthonormal for the Fock inner product** — the same statement
`ChapterSmCarAlgebra` uses, restated in the form the identification needs. -/
theorem occ_ofLp (S T : Finset (Fin n)) : (occ S).ofLp T = if T = S then 1 else 0 := by
  rw [occ, EuclideanSpace.single_apply]

/-- **The occupation basis is orthonormal for the Fock inner product** — the same statement
`ChapterSmCarAlgebra` uses, restated in the form the identification needs. -/
theorem occ_inner (S T : Finset (Fin n)) :
    inner ℂ (occ S) (occ T) = if S = T then 1 else 0 := by
  rw [inner_eq_sum, Finset.sum_eq_single S]
  · rw [occ_ofLp, if_pos rfl, occ_ofLp, map_one, one_mul]
  · intro U _ hU
    rw [occ_ofLp, if_neg hU]
    simp
  · intro h
    exact absurd (Finset.mem_univ S) h

/-! ## 2. The twelve ghost modes and their orthonormal occupation vectors -/

/-- The occupation vector of the ghost mode `a`: the Fock-space representative of the index
model's ghost coordinate. -/
noncomputable def ghostVec (m : ℕ) (a : Fin 12) : FermiFock (m + 12) :=
  occ {ghostMode m a}

/-- **The ghost occupation vectors are orthonormal**: the twelve ghost modes give an isometric
copy of the index pattern's ghost coordinates. -/
theorem ghostVec_orthonormal (m : ℕ) (a b : Fin 12) :
    inner ℂ (ghostVec m a) (ghostVec m b) = if a = b then 1 else 0 := by
  rw [ghostVec, ghostVec, occ_inner]
  by_cases h : a = b
  · subst h; simp
  · have hs : ({ghostMode m a} : Finset (Fin (m + 12))) ≠ {ghostMode m b} := by
      intro hh
      exact h (ghostMode_injective m (Finset.singleton_injective hh))
    simp [h, hs]

/-- **The copy is the orbit of the vacuum**: creating a ghost mode from the Fock vacuum gives
exactly the corresponding occupation vector. -/
theorem ghostCre_vac (m : ℕ) (a : Fin 12) : ghostCre m a (vac) = ghostVec m a := by
  rw [ghostCre]
  apply WithLp.ofLp_injective
  funext S
  rw [creat_apply, ghostVec, occ_ofLp, vac, occ_ofLp]
  by_cases hS : S = {ghostMode m a}
  · subst hS
    rw [if_pos rfl, Finset.erase_singleton]
    simp [jwSign]
  · by_cases hi : ghostMode m a ∈ S
    · have herase : S.erase (ghostMode m a) ≠ ∅ := by
        intro hnil
        have hsub : S ⊆ {ghostMode m a} := by
          intro x hx
          by_cases hxi : x = ghostMode m a
          · simp [hxi]
          · exfalso
            have hx' : x ∈ S.erase (ghostMode m a) := Finset.mem_erase.mpr ⟨hxi, hx⟩
            rw [hnil] at hx'
            exact absurd hx' (Finset.notMem_empty x)
        exact hS (Finset.Subset.antisymm hsub (Finset.singleton_subset_iff.mpr hi))
      rw [if_pos hi, if_neg hS, if_neg herase]
      ring
    · rw [if_neg hi, if_neg hS]

/-! ## 3. The ghost/antighost pairing is the Fock adjunction -/

/-- **The pairing the index model calls `η` is the Fock adjunction**: the antighost of a mode is
the adjoint of its ghost creation operator, so `⟨c_a ψ, φ⟩ = ⟨ψ, b_a φ⟩`. -/
theorem ghost_pairing (m : ℕ) (a : Fin 12) (ψ φ : FermiFock (m + 12)) :
    inner ℂ (ghostCre m a ψ) φ = inner ℂ ψ (ghostAnn m a φ) := by
  rw [ghostCre, ghostAnn]
  exact inner_creat_left (ghostMode m a) ψ φ

end

end BookProof.SmIndexGhostFock
