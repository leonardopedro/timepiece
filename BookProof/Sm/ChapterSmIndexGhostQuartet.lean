/-
Copyright (c) 2026 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import BookProof.Sm.ChapterSmQuartet

/-!
# The b-ghost on an index-restricted Euclidean space

`ChapterSmQuartet` §5 removed one of the two objects in `BrstQuartet`: given a contracting
homotopy `P` (`Q P Q = Q`, `P Q P = P`) the physical projector is *computed*
(`physProjOf`), and §6 exhibited the whole mechanism on a three-dimensional block by hand —
`exQ`, `exP`, `exV`, `exEta` written out coordinate by coordinate.

Writing the ghost complex out by hand does not scale to a real gauge sector, and §47's
withdrawal recorded why the two-slot `K × K` formulation was abandoned: this Mathlib has no
product inner-product space, so the ghost and antighost slots cannot be fed to `IsBrst` /
`BrstQuartet` without an `EuclideanSpace` reformulation.  This module is that reformulation, and
it is *index-restricted*: the index set is

```
Idx n m = (Fin n × Bool) ⊕ Fin m,
```

where `(a, false)` is ghost `a`, `(a, true)` its antighost, and `inr j` a physical mode.  The
charge, the b-ghost and the metric are then defined *by index* for every `n` and `m` at once:

* `Q` sends `(a, false) ↦ (a, true)` and kills everything else;
* `P` sends `(a, true) ↦ (a, false)` and kills everything else;
* `η` swaps `(a, false) ↔ (a, true)` and fixes the physical modes.

Nothing is chosen per pair: `n` ghost pairs are one definition, so the construction is
independent of the size of the gauge sector (the SM's ghost sector is `n = 12` with the twelve
modes indexed by `Fin 12`).

All six hypotheses of `physicalPositivity_of_homotopy` are then *discharged*, not assumed:
nilpotency (`Q_nil`), the two contraction identities (`QPQ`, `PQP`), Krein self-adjointness
(`krein`), symmetry of the charge form (`symm`), and the metric fixing the constructed
projector's range (`eta_physProj`).  Hence `physicalPositivity` is a theorem for this model, and
`physVec_not_exact` shows the model is not one where every closed vector is a gauge orbit.

What this does **not** do: it is not `smBrstCharge`.  That charge lives on the fermionic Fock
space `FermiFock (m + 12)` and is only known here as a `Module.End`; to instantiate this model
on it one still needs an inner-product structure on that Fock space, the charge as a linear map,
and the identification of its twelve ghost modes with the index pattern above.  So
`PhysicalPositivity` is no longer a *generic* named input — it is proved for the index-restricted
ghost complex at every size — but it is not yet proved for `smBrstCharge`, and nothing here
upgrades the SM claim.

Everything here is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmIndexGhostQuartet

open BookProof.SmQuartet
open BookProof.SmQuartet.BrstQuartet
open BookProof.SmBrstQuotient

noncomputable section

/-! ## 1. The index set and the metric space -/

/-- The index set of the restricted ghost complex: ghost `(a, false)` and antighost `(a, true)`
of pair `a`, plus the physical modes. -/
abbrev Idx (n m : ℕ) := Fin n × Bool ⊕ Fin m

/-- The underlying Hilbert space. -/
abbrev Space (n m : ℕ) := EuclideanSpace ℂ (Idx n m)

/-- A ghost slot. -/
abbrev ghostIdx {n m : ℕ} (a : Fin n) : Idx n m := Sum.inl (a, false)

/-- The antighost slot of the same pair. -/
abbrev antiIdx {n m : ℕ} (a : Fin n) : Idx n m := Sum.inl (a, true)

/-- A physical slot. -/
abbrev physIdx {n m : ℕ} (j : Fin m) : Idx n m := Sum.inr j

/-- Extensionality through the coordinate representation. -/
theorem lp_ext {n m : ℕ} {x y : Space n m} (h : x.ofLp = y.ofLp) : x = y := by
  rw [← WithLp.toLp_ofLp 2 x, ← WithLp.toLp_ofLp 2 y, h]

/-! ## 2. The charge, the b-ghost and the metric, by index -/

/-- The charge: ghost `a` maps to its antighost, everything else is killed. -/
def Q (n m : ℕ) : Space n m →ₗ[ℂ] Space n m where
  toFun v := WithLp.toLp 2 (fun i => match i with
    | Sum.inl (a, true) => v.ofLp (Sum.inl (a, false))
    | _ => 0)
  map_add' x y := by
    apply lp_ext
    funext i
    rcases i with ⟨a, b⟩ | j
    · cases b <;> simp
    · simp
  map_smul' c x := by
    apply lp_ext
    funext i
    rcases i with ⟨a, b⟩ | j
    · cases b <;> simp
    · simp

/-- The b-ghost: the antighost of pair `a` maps back to its ghost, everything else is killed. -/
def P (n m : ℕ) : Space n m →ₗ[ℂ] Space n m where
  toFun v := WithLp.toLp 2 (fun i => match i with
    | Sum.inl (a, false) => v.ofLp (Sum.inl (a, true))
    | _ => 0)
  map_add' x y := by
    apply lp_ext
    funext i
    rcases i with ⟨a, b⟩ | j
    · cases b <;> simp
    · simp
  map_smul' c x := by
    apply lp_ext
    funext i
    rcases i with ⟨a, b⟩ | j
    · cases b <;> simp
    · simp

/-- The metric: the indefinite pairing that swaps each ghost with its antighost and fixes the
physical modes.  It is indefinite of necessity — a nilpotent self-adjoint charge cannot exist in
a definite space. -/
def Eta (n m : ℕ) : Space n m →ₗ[ℂ] Space n m where
  toFun v := WithLp.toLp 2 (fun i => match i with
    | Sum.inl (a, false) => v.ofLp (Sum.inl (a, true))
    | Sum.inl (a, true) => v.ofLp (Sum.inl (a, false))
    | Sum.inr j => v.ofLp (Sum.inr j))
  map_add' x y := by
    apply lp_ext
    funext i
    rcases i with ⟨a, b⟩ | j
    · cases b <;> simp
    · simp
  map_smul' c x := by
    apply lp_ext
    funext i
    rcases i with ⟨a, b⟩ | j
    · cases b <;> simp
    · simp

/-! ## 3. Coordinates of the three maps -/

theorem Q_anti (n m : ℕ) (v : Space n m) (a : Fin n) :
    (Q n m v).ofLp (antiIdx a) = v.ofLp (ghostIdx a) := rfl

theorem Q_ghost (n m : ℕ) (v : Space n m) (a : Fin n) :
    (Q n m v).ofLp (ghostIdx a) = 0 := rfl

theorem Q_phys (n m : ℕ) (v : Space n m) (j : Fin m) :
    (Q n m v).ofLp (physIdx j) = 0 := rfl

theorem P_ghost (n m : ℕ) (v : Space n m) (a : Fin n) :
    (P n m v).ofLp (ghostIdx a) = v.ofLp (antiIdx a) := rfl

theorem P_anti (n m : ℕ) (v : Space n m) (a : Fin n) :
    (P n m v).ofLp (antiIdx a) = 0 := rfl

theorem P_phys (n m : ℕ) (v : Space n m) (j : Fin m) :
    (P n m v).ofLp (physIdx j) = 0 := rfl

theorem Eta_ghost (n m : ℕ) (v : Space n m) (a : Fin n) :
    (Eta n m v).ofLp (ghostIdx a) = v.ofLp (antiIdx a) := rfl

theorem Eta_anti (n m : ℕ) (v : Space n m) (a : Fin n) :
    (Eta n m v).ofLp (antiIdx a) = v.ofLp (ghostIdx a) := rfl

theorem Eta_phys (n m : ℕ) (v : Space n m) (j : Fin m) :
    (Eta n m v).ofLp (physIdx j) = v.ofLp (physIdx j) := rfl

/-- A vector is determined by its ghost, antighost and physical coordinates. -/
theorem ext_coords {n m : ℕ} {x y : Space n m}
    (hg : ∀ a, x.ofLp (ghostIdx a) = y.ofLp (ghostIdx a))
    (ha : ∀ a, x.ofLp (antiIdx a) = y.ofLp (antiIdx a))
    (hp : ∀ j, x.ofLp (physIdx j) = y.ofLp (physIdx j)) : x = y := by
  apply lp_ext
  funext i
  rcases i with ⟨a, b⟩ | j
  · cases b
    · exact hg a
    · exact ha a
  · exact hp j

/-! ## 4. Nilpotency and the two contraction identities -/

/-- **The charge is nilpotent**: `Q² = 0`. -/
theorem Q_nil (n m : ℕ) : IsBrst (Q n m) := by
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, LinearMap.zero_apply]
  refine ext_coords (fun a => ?_) (fun a => ?_) (fun j => ?_)
  · rw [Q_ghost]; simp
  · rw [Q_anti, Q_ghost]; simp
  · rw [Q_phys]; simp

/-- **`Q P Q = Q`**: the b-ghost is a right inverse for the charge on its range. -/
theorem QPQ (n m : ℕ) (v : Space n m) : Q n m (P n m (Q n m v)) = Q n m v := by
  refine ext_coords (fun a => ?_) (fun a => ?_) (fun j => ?_)
  · rw [Q_ghost, Q_ghost]
  · rw [Q_anti, P_ghost, Q_anti]
  · rw [Q_phys, Q_phys]

/-- **`P Q P = P`**: the b-ghost is a left inverse for the charge on its range. -/
theorem PQP (n m : ℕ) (v : Space n m) : P n m (Q n m (P n m v)) = P n m v := by
  refine ext_coords (fun a => ?_) (fun a => ?_) (fun j => ?_)
  · rw [P_ghost, Q_anti, P_ghost]
  · rw [P_anti, P_anti]
  · rw [P_phys, P_phys]

/-! ## 5. The constructed projector is the physical projection -/

/-- **The projector computed from the b-ghost keeps exactly the physical coordinates**. -/
theorem physProj_ghost (n m : ℕ) (v : Space n m) (a : Fin n) :
    (physProjOf (Q n m) (P n m) v).ofLp (ghostIdx a) = 0 := by
  rw [BrstQuartet.physProjOf_apply]
  simp only [WithLp.ofLp_add, WithLp.ofLp_sub, Pi.add_apply, Pi.sub_apply]
  simp only [Q_ghost, P_ghost, Q_anti]
  ring

theorem physProj_anti (n m : ℕ) (v : Space n m) (a : Fin n) :
    (physProjOf (Q n m) (P n m) v).ofLp (antiIdx a) = 0 := by
  rw [BrstQuartet.physProjOf_apply]
  simp only [WithLp.ofLp_add, WithLp.ofLp_sub, Pi.add_apply, Pi.sub_apply]
  simp only [Q_anti, P_anti, P_ghost]
  ring

theorem physProj_phys (n m : ℕ) (v : Space n m) (j : Fin m) :
    (physProjOf (Q n m) (P n m) v).ofLp (physIdx j) = v.ofLp (physIdx j) := by
  rw [BrstQuartet.physProjOf_apply]
  simp only [WithLp.ofLp_add, WithLp.ofLp_sub, Pi.add_apply, Pi.sub_apply]
  simp only [Q_phys, P_phys]
  ring

/-- **The metric fixes the projector's range**: `η (V y) = V y`, the hypothesis the no-ghost
theorem needs.  This is where the index restriction pays: the constructed projector lands on the
physical coordinates, where `η` is the identity. -/
theorem eta_physProj (n m : ℕ) (v : Space n m) :
    Eta n m (physProjOf (Q n m) (P n m) v) = physProjOf (Q n m) (P n m) v := by
  refine ext_coords (fun a => ?_) (fun a => ?_) (fun j => ?_)
  · rw [Eta_ghost, physProj_anti, physProj_ghost]
  · rw [Eta_anti, physProj_ghost, physProj_anti]
  · rw [Eta_phys]

/-! ## 6. The charge form -/

/-- **The metric is an involution**: `η² = 1`. -/
theorem Eta_involutive (n m : ℕ) (v : Space n m) : Eta n m (Eta n m v) = v := by
  refine ext_coords (fun a => ?_) (fun a => ?_) (fun j => ?_)
  · rw [Eta_ghost, Eta_anti]
  · rw [Eta_anti, Eta_ghost]
  · rw [Eta_phys, Eta_phys]

/-- **The metric is an isometry** for the Hilbert inner product: swapping each ghost with its
antighost permutes the coordinates. -/
theorem Eta_inner (n m : ℕ) (x y : Space n m) :
    inner ℂ (Eta n m x) (Eta n m y) = inner ℂ x y := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [RCLike.inner_apply, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fintype.sum_bool, Eta_ghost, Eta_anti, Eta_phys]
  rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
  ring

/-- **The charge is self-adjoint for the charge form**: `⟨η (Q x), y⟩ = ⟨η x, Q y⟩`. -/
theorem krein (n m : ℕ) (x y : Space n m) :
    kform (Eta n m) (Q n m x) y = kform (Eta n m) x (Q n m y) := by
  rw [kform, kform, PiLp.inner_apply, PiLp.inner_apply]
  simp [Fintype.sum_sum_type, Fintype.sum_prod_type, Eta_ghost, Eta_anti, Eta_phys, Q_ghost,
    Q_anti, Q_phys, ghostIdx, antiIdx, physIdx, mul_comm]

/-- **The charge form is symmetric**: `⟨x, η y⟩ = conj ⟨y, η x⟩`.  This follows from the metric
being an involutive isometry rather than from a coordinate computation. -/
theorem symm (n m : ℕ) (x y : Space n m) :
    kform (Eta n m) x y = star (kform (Eta n m) y x) := by
  have h : star (inner ℂ y (Eta n m x)) = inner ℂ (Eta n m x) y :=
    inner_conj_symm (𝕜 := ℂ) (Eta n m x) y
  rw [kform, kform, h]
  rw [← Eta_inner (n := n) (m := m) (Eta n m x) y, Eta_involutive]

/-! ## 7. `PhysicalPositivity` for the restricted ghost complex -/

/-- **Kugo–Ojima positivity holds for the index-restricted ghost complex, with nothing
assumed**: every hypothesis of `physicalPositivity_of_homotopy` is discharged above, at every
size `n, m`.  The charge form on a closed vector is `‖V x‖²`, and its radical is the gauge
orbit. -/
theorem physicalPositivity (n m : ℕ) : PhysicalPositivity (Q n m) (Eta n m) :=
  BrstQuartet.physicalPositivity_of_homotopy (Q_nil n m) (QPQ n m) (PQP n m) (krein n m) (symm n m)
    (eta_physProj n m)

/-- A physical basis vector: the `j`-th physical mode. -/
def physVec {n m : ℕ} (j : Fin m) : Space n m :=
  WithLp.toLp 2 (Pi.single (physIdx j) 1)

theorem physVec_ofLp {n m : ℕ} (j : Fin m) :
    (physVec (n := n) j).ofLp = Pi.single (physIdx j) 1 := rfl

/-- The physical mode is closed. -/
theorem physVec_closed {n m : ℕ} (j : Fin m) : physVec (n := n) j ∈ closed (Q n m) := by
  rw [closed, LinearMap.mem_ker]
  refine ext_coords (fun a => ?_) (fun a => ?_) (fun j' => ?_)
  · rw [Q_ghost]; simp
  · rw [Q_anti, physVec_ofLp, Pi.single_eq_of_ne (by simp [physIdx])]
    simp
  · rw [Q_phys]; simp

/-- **The cohomology is non-trivial**: a physical mode is not a gauge orbit, so
`physicalPositivity` is not being applied to a space on which every closed vector is exact. -/
theorem physVec_not_exact {n m : ℕ} (j : Fin m) :
    ¬ physVec (n := n) j ∈ SmBrstQuotient.gauge (Q n m) := by
  rw [SmBrstQuotient.gauge, LinearMap.mem_range]
  rintro ⟨w, hw⟩
  have h := congrArg (fun z : Space n m => z.ofLp (physIdx j)) hw
  simp only [Q_phys, physVec_ofLp, Pi.single_eq_same] at h
  exact one_ne_zero h.symm

end

end BookProof.SmIndexGhostQuartet
