/-
Copyright (c) 2026 Leonardo de Moura. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/
import BookProof.Sm.ChapterSmIndexGhostQuartet

/-!
# The ghost-parity sectors of the index-restricted complex

`ChapterSmIndexGhostQuartet` proves Kugo–Ojima positivity for the index-restricted ghost
complex through `physicalPositivity_of_homotopy`, whose last hypothesis is `η (V y) = V y`.
The sector refinement of the no-ghost theorem (`physicalPositivity_of_homotopy_sectors`,
`kform_quadForm_nonneg`) replaces that single hypothesis by two estimates, one per parity
sector.  This module asks whether the index model supports that refinement, and the answer is
two-sided:

* **On the closed space, yes.**  With the ghost parity `Par` — `-1` on every ghost and antighost
  coordinate, `+1` on the physical ones — the even part of `ker Q` is the physical subspace and
  the odd part is pure antighost, where the charge form vanishes identically.  So
  `kform_even_nonneg` and `kform_odd_closed_nonneg` hold, and `kform_quadForm_nonneg` assembles
  them into non-negativity on the whole closed space (`kform_nonneg_closed`).  This is the shape
  the sector machinery consumes: `physicalPositivity_sectors` re-derives the theorem by that
  route, with the four hypotheses restricted to `ker Q`.
* **Globally, no — and necessarily so.**  `physicalPositivity_of_quartet_sectors` asks for
  non-negativity and definiteness on the *whole* of each parity sector.  That request cannot be
  met by any parity, in any space: `global_sectors_force_zero` shows the four global hypotheses
  force `Q = 0`, by splitting any vector into its even and odd parts, and a nilpotent charge that
  is self-adjoint for the charge form cannot then be nonzero.  The index model is a witness
  (`parity_globals_fail`), and so is any nonzero BRST charge.

The lesson is the one §47 needed: the sector hypotheses have to be read on the closed space
(the shape `kform_quadForm_nonneg` takes), not on the ambient space.

Everything here is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmIndexGhostSectors

open BookProof.SmQuartet
open BookProof.SmQuartet.BrstQuartet
open BookProof.SmBrstQuotient
open BookProof.SmPhysicalReduction
open BookProof.SmIndexGhostQuartet

noncomputable section

/-! ## 1. The obstruction, in any inner-product space

Before looking at the model: the *global* sector hypotheses are inconsistent with a nonzero
nilpotent charge.  Both the positivity and the definiteness halves are used, on both sectors, so
this is a statement about the quartet machinery's hypotheses rather than about index spaces. -/

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-- **The global sector hypotheses force the charge to vanish.**  A vector splits into its even
and odd parts; the sectors are orthogonal for the charge form, so non-negativity on both sectors
makes the whole form non-negative, and definiteness on both makes it definite.  Then the charge
is self-adjoint for a definite form and squares to zero, so it is zero. -/
theorem global_sectors_force_zero {Q η U : H →ₗ[ℂ] H} (hQ : IsBrst Q)
    (hU : U ∘ₗ U = LinearMap.id) (hUnorm : ∀ x : H, ‖U x‖ = ‖x‖)
    (hηU : η ∘ₗ U = U ∘ₗ η)
    (hKrein : ∀ x y : H, kform η (Q x) y = kform η x (Q y))
    (hev : ∀ y : H, y ∈ evenSpace U → 0 ≤ (kform η y y).re)
    (hod : ∀ y : H, y ∈ oddSpace U → 0 ≤ (kform η y y).re)
    (hevDef : ∀ y : H, y ∈ evenSpace U → (kform η y y).re = 0 → y = 0)
    (hodDef : ∀ y : H, y ∈ oddSpace U → (kform η y y).re = 0 → y = 0) :
    Q = 0 := by
  have hdef : ∀ y : H, (kform η y y).re = 0 → y = 0 := by
    intro y hy
    have hsplit := kform_quadForm_split hU hUnorm hηU y
    have h1 := hev _ (evenPart_mem hU y)
    have h2 := hod _ (oddPart_mem hU y)
    rw [hy] at hsplit
    have he0 : (kform η (evenPart U y) (evenPart U y)).re = 0 := by linarith
    have ho0 : (kform η (oddPart U y) (oddPart U y)).re = 0 := by linarith
    have he := hevDef _ (evenPart_mem hU y) he0
    have ho := hodDef _ (oddPart_mem hU y) ho0
    have h := evenPart_add_oddPart (U := U) y
    rw [he, ho, add_zero] at h
    exact h.symm
  refine LinearMap.ext fun y => ?_
  have hzero : (kform η (Q y) (Q y)).re = 0 := by
    rw [kform_exact_self hQ hKrein y]
    simp
  exact hdef _ hzero

/-! ## 2. The ghost parity of the index model -/

namespace Model

variable {n m : ℕ}

/-- **The ghost parity**: `-1` on every ghost and antighost coordinate, `+1` on the physical ones.
It commutes with the charge and the b-ghost, and it preserves the metric. -/
def Par (n m : ℕ) : Space n m →ₗ[ℂ] Space n m where
  toFun v := WithLp.toLp 2 (fun i => match i with
    | Sum.inl (a, false) => -v.ofLp (Sum.inl (a, false))
    | Sum.inl (a, true) => -v.ofLp (Sum.inl (a, true))
    | Sum.inr j => v.ofLp (Sum.inr j))
  map_add' x y := by
    apply lp_ext
    funext i
    rcases i with ⟨a, b⟩ | j
    · cases b <;> simp [add_comm]
    · simp
  map_smul' c x := by
    apply lp_ext
    funext i
    rcases i with ⟨a, b⟩ | j
    · cases b <;> simp
    · simp

theorem Par_ghost (v : Space n m) (a : Fin n) :
    (Par n m v).ofLp (ghostIdx a) = -v.ofLp (ghostIdx a) := rfl

theorem Par_anti (v : Space n m) (a : Fin n) :
    (Par n m v).ofLp (antiIdx a) = -v.ofLp (antiIdx a) := rfl

theorem Par_phys (v : Space n m) (j : Fin m) :
    (Par n m v).ofLp (physIdx j) = v.ofLp (physIdx j) := rfl

/-- The ghost parity is an involution. -/
theorem Par_involutive (v : Space n m) : Par n m (Par n m v) = v := by
  refine ext_coords (fun a => ?_) (fun a => ?_) (fun j => ?_)
  · rw [Par_ghost, Par_ghost, neg_neg]
  · rw [Par_anti, Par_anti, neg_neg]
  · rw [Par_phys, Par_phys]

/-- The ghost parity is an involution as a linear map. -/
theorem Par_comp_self : Par n m ∘ₗ Par n m = LinearMap.id := by
  refine LinearMap.ext fun v => ?_
  rw [LinearMap.comp_apply, LinearMap.id_apply]
  exact Par_involutive v

/-- The ghost parity preserves the Hilbert inner product. -/
theorem Par_inner (x y : Space n m) : inner ℂ (Par n m x) (Par n m y) = inner ℂ x y := by
  rw [PiLp.inner_apply, PiLp.inner_apply]
  simp only [RCLike.inner_apply, Fintype.sum_sum_type, Fintype.sum_prod_type,
    Fintype.sum_bool, Par_ghost, Par_anti, Par_phys, map_neg, neg_mul_neg]

/-- The ghost parity is a contraction-free isometry of the norm. -/
theorem Par_norm (v : Space n m) : ‖Par n m v‖ = ‖v‖ := by
  have h := Par_inner v v
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖Par n m v‖ ^ 2 = ‖v‖ ^ 2 := by exact_mod_cast h
  nlinarith [norm_nonneg (Par n m v), norm_nonneg v]

/-- The ghost parity commutes with the metric: the metric swaps into coordinates that carry the
same sign. -/
theorem Eta_comm_Par (v : Space n m) : Eta n m (Par n m v) = Par n m (Eta n m v) := by
  refine ext_coords (fun a => ?_) (fun a => ?_) (fun j => ?_)
  · rw [Eta_ghost, Par_anti, Par_ghost, Eta_ghost]
  · rw [Eta_anti, Par_ghost, Par_anti, Eta_anti]
  · rw [Eta_phys, Par_phys, Par_phys, Eta_phys]

/-- The ghost parity commutes with the charge. -/
theorem Q_comm_Par (v : Space n m) : Par n m (Q n m v) = Q n m (Par n m v) := by
  refine ext_coords (fun a => ?_) (fun a => ?_) (fun j => ?_)
  · rw [Par_ghost, Q_ghost, Q_ghost, neg_zero]
  · rw [Par_anti, Q_anti, Q_anti, Par_ghost]
  · rw [Par_phys, Q_phys, Q_phys]

/-- The ghost parity commutes with the b-ghost. -/
theorem P_comm_Par (v : Space n m) : Par n m (P n m v) = P n m (Par n m v) := by
  refine ext_coords (fun a => ?_) (fun a => ?_) (fun j => ?_)
  · rw [Par_ghost, P_ghost, P_ghost, Par_anti]
  · rw [Par_anti, P_anti, P_anti, neg_zero]
  · rw [Par_phys, P_phys, P_phys]

/-! ## 3. The two sectors, coordinatewise -/

/-- **An even vector has no ghost coordinates.** -/
theorem ghost_eq_zero_of_mem_even {v : Space n m} (hv : v ∈ evenSpace (Par n m))
    (a : Fin n) : v.ofLp (ghostIdx a) = 0 := by
  have h : Par n m v = v := (mem_evenSpace_iff v).mp hv
  have hc := congrArg (fun z : Space n m => z.ofLp (ghostIdx a)) h
  simp only [Par_ghost] at hc
  linear_combination (-1 / 2 : ℂ) * hc

/-- **An even vector has no antighost coordinates either.** -/
theorem anti_eq_zero_of_mem_even {v : Space n m} (hv : v ∈ evenSpace (Par n m))
    (a : Fin n) : v.ofLp (antiIdx a) = 0 := by
  have h : Par n m v = v := (mem_evenSpace_iff v).mp hv
  have hc := congrArg (fun z : Space n m => z.ofLp (antiIdx a)) h
  simp only [Par_anti] at hc
  linear_combination (-1 / 2 : ℂ) * hc

/-- **An odd vector has no physical coordinates.** -/
theorem phys_eq_zero_of_mem_odd {v : Space n m} (hv : v ∈ oddSpace (Par n m))
    (j : Fin m) : v.ofLp (physIdx j) = 0 := by
  have h : Par n m v = -v := (mem_oddSpace_iff v).mp hv
  have hc := congrArg (fun z : Space n m => z.ofLp (physIdx j)) h
  simp only [Par_phys, WithLp.ofLp_neg, Pi.neg_apply] at hc
  linear_combination (1 / 2 : ℂ) * hc

/-- **A closed vector has no ghost coordinates**: the charge already kills them, so closure forces
their preimages — the ghosts — to vanish. -/
theorem ghost_eq_zero_of_mem_closed {v : Space n m} (hv : v ∈ closed (Q n m))
    (a : Fin n) : v.ofLp (ghostIdx a) = 0 := by
  have h := congrArg (fun z : Space n m => z.ofLp (antiIdx a)) hv
  simp only [Q_anti, WithLp.ofLp_zero, Pi.zero_apply] at h
  exact h

/-- **The metric fixes the even sector**: an even vector has neither ghost nor antighost
coordinates, so swapping them changes nothing. -/
theorem Eta_eq_of_mem_even {v : Space n m} (hv : v ∈ evenSpace (Par n m)) :
    Eta n m v = v := by
  refine ext_coords (fun a => ?_) (fun a => ?_) (fun j => ?_)
  · rw [Eta_ghost, anti_eq_zero_of_mem_even hv, ghost_eq_zero_of_mem_even hv]
  · rw [Eta_anti, ghost_eq_zero_of_mem_even hv, anti_eq_zero_of_mem_even hv]
  · rw [Eta_phys]

/-- **Non-negativity on the even sector.**  The metric is the identity there, so the charge form
is `‖v‖²`. -/
theorem kform_even_nonneg {v : Space n m} (hv : v ∈ evenSpace (Par n m)) :
    0 ≤ (kform (Eta n m) v v).re := by
  rw [kform, Eta_eq_of_mem_even hv]
  exact inner_self_nonneg (𝕜 := ℂ) (x := v)

/-- **Vanishing on the odd part of the closed space.**  An odd closed vector is a pure antighost,
and the metric sends it to a pure ghost, which is orthogonal to it. -/
theorem kform_odd_closed {v : Space n m} (hv : v ∈ oddSpace (Par n m))
    (hc : v ∈ closed (Q n m)) : kform (Eta n m) v v = 0 := by
  have hg : ∀ a, v.ofLp (ghostIdx a) = 0 := ghost_eq_zero_of_mem_closed hc
  have hp : ∀ j, v.ofLp (physIdx j) = 0 := phys_eq_zero_of_mem_odd hv
  rw [kform, PiLp.inner_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  rcases i with ⟨a, b⟩ | j
  · cases b
    · simp [RCLike.inner_apply, Eta_ghost, hg a]
    · simp [RCLike.inner_apply, Eta_anti, hg a]
  · simp [Eta_phys, hp j]

/-- **Non-negativity on the odd part of the closed space.** -/
theorem kform_odd_closed_nonneg {v : Space n m} (hv : v ∈ oddSpace (Par n m))
    (hc : v ∈ closed (Q n m)) : 0 ≤ (kform (Eta n m) v v).re := by
  rw [kform_odd_closed hv hc]
  simp

/-! ## 4. The sector hypotheses hold on the closed space -/

/-- **Sector-by-sector non-negativity on the closed space**, with the two hypotheses stated exactly
in the form `kform_quadForm_nonneg` consumes: only closed vectors of each sector are restricted. -/
theorem kform_nonneg_closed {v : Space n m} (hv : v ∈ closed (Q n m)) :
    0 ≤ (kform (Eta n m) v v).re :=
  kform_quadForm_nonneg (U := Par n m) (Q := Q n m) (η := Eta n m)
    Par_comp_self Par_norm
    (LinearMap.ext fun z => Eta_comm_Par z)
    (LinearMap.ext fun z => Q_comm_Par z)
    (fun _ _ hx => kform_even_nonneg hx)
    (fun _ hx hxo => kform_odd_closed_nonneg hxo hx) hv

/-- **The sector hypotheses are inhabited on the closed space, for every size.**  This is the
content `physicalPositivity_of_homotopy_sectors` wanted; the global version is refuted in §5. -/
theorem sector_hypotheses_closed (n m : ℕ) :
    (∀ v : Space n m, v ∈ closed (Q n m) → v ∈ evenSpace (Par n m) →
        0 ≤ (kform (Eta n m) v v).re)
      ∧ (∀ v : Space n m, v ∈ closed (Q n m) → v ∈ oddSpace (Par n m) →
        0 ≤ (kform (Eta n m) v v).re) :=
  ⟨fun _ _ hv => kform_even_nonneg hv, fun _ hv hvo => kform_odd_closed_nonneg hvo hv⟩

/-- **The non-negativity half of `PhysicalPositivity` by the sector route.**  The sector split of
the charge form gives this without using `η` fixing the projector's range; the radical half needs
that input (`eta_physProj`, used in `ChapterSmIndexGhostQuartet.physicalPositivity`), because an
odd antighost has vanishing charge form and is removed by the quartet decomposition rather than by
definiteness. -/
theorem kform_nonneg_self {x : Space n m} (hx : x ∈ closed (Q n m)) :
    0 ≤ (kform (Eta n m) x x).re :=
  kform_nonneg_closed hx

/-! ## 5. The global hypotheses cannot hold -/

/-- The charge is nonzero: it sends the ghost of a pair to its antighost. -/
theorem Q_ne_zero (hn : 0 < n) : Q n m ≠ 0 := by
  intro h
  have hghost : ghostIdx (n := n) (m := m) ⟨0, hn⟩ = Sum.inl (⟨0, hn⟩, false) := rfl
  have hv := congrArg (fun T : Space n m →ₗ[ℂ] Space n m =>
    (T (WithLp.toLp 2 (Pi.single (ghostIdx (m := m) ⟨0, hn⟩) 1))).ofLp
      (antiIdx (n := n) ⟨0, hn⟩)) h
  simp only [LinearMap.zero_apply, WithLp.ofLp_zero, Pi.zero_apply] at hv
  rw [Q_anti] at hv
  have hsingle : (WithLp.toLp 2 (Pi.single (ghostIdx (m := m) ⟨0, hn⟩) 1) : Space n m).ofLp
      (ghostIdx ⟨0, hn⟩) = 1 := by
    simp
  rw [hsingle] at hv
  exact one_ne_zero hv

/-- **The global sector hypotheses fail for the index model.**  If they held for the ghost parity,
`global_sectors_force_zero` would make the charge vanish, contradicting `Q_ne_zero`.  So the
sector form of the theorem must be read on the closed space — which is what §4 supplies. -/
theorem parity_globals_fail (hn : 0 < n) :
    ¬ ((∀ y : Space n m, y ∈ evenSpace (Par n m) → 0 ≤ (kform (Eta n m) y y).re)
        ∧ (∀ y : Space n m, y ∈ oddSpace (Par n m) → 0 ≤ (kform (Eta n m) y y).re)
        ∧ (∀ y : Space n m, y ∈ evenSpace (Par n m) →
            (kform (Eta n m) y y).re = 0 → y = 0)
        ∧ (∀ y : Space n m, y ∈ oddSpace (Par n m) →
            (kform (Eta n m) y y).re = 0 → y = 0)) := by
  rintro ⟨hev, hod, hevDef, hodDef⟩
  have hzero := global_sectors_force_zero (Q := Q n m) (η := Eta n m) (U := Par n m)
    (Q_nil n m) Par_comp_self Par_norm (LinearMap.ext fun z => Eta_comm_Par z) (krein n m)
    hev hod hevDef hodDef
  exact Q_ne_zero (m := m) hn hzero

end Model

end

end BookProof.SmIndexGhostSectors
