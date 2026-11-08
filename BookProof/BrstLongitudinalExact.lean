import Mathlib
import BookProof.ChapterBrstReducedTransfer

/-!
# "Longitudinal = exact" in the periodic derivative-gauge model

`softmodes.md` Phase 1, open item 3 asks for the identification

`closure (range Ω) = span{∂ᵢφ}`

(the pure-gauge directions are precisely the BRST-exact states), together with the observation
that a longitudinal plane wave is not harmonic.  `ChapterBrstLongitudinal` proves one inclusion
in the algebraic realization of `book.tex` — the longitudinal direction *is* BRST-produced —
and records why the equality of subspaces is not available there: `BookState N` carries no inner
product and no completion, so there is no topological closure to compare with a span.

This file closes the equality in the smallest model that has both a derivative and a Hilbert
space: fields on a **periodic lattice**, `Fin (n+1) → ℂ`, with the cyclic difference

`∂f (j) = f (j+1) − f (j)`   (`derivLin`),

and the charge acting on `stateSpace n = (fields) × (ghosts)`, where the ghost factor is a single
two-dimensional occupation space and the charge is the derivative raising the ghost number:

`Ω (x, y) = (0, ∂x)`   (`brstCharge`).

That is the abelian derivative-gauge charge of `ChapterBrstLongitudinal` with the ghost dressing
kept and the gauge algebra trivialized (`comm_bookOmega_Afield`: `[Ω, A] = −i·dChi`); the factor
`c†` is what makes `Ω² = 0`, and the gauge-field part is the derivative.

## What is proved

* **`sum_deriv`: the derivative has no zero mode**, `∑ⱼ ∂f(j) = 0`.  This is the finite-lattice
  content of "a gradient is orthogonal to the constants";
* **`range_derivLin`**: `range ∂ = {f | ∑ⱼ f(j) = 0}` — the gradient's image is *exactly* the
  mean-zero fields.  The inclusion is `sum_deriv`; the converse is explicit: the cumulative sum
  `cumFun f` of a mean-zero field satisfies `∂(cumFun f) = f` (`derivLin_cumFun`), which also
  identifies the right-hand side as `span{∂φ}` rather than merely `⊆ span{∂φ}`;
* **`brstCharge_nilpotent`**: `Ω² = 0` — the ghost factor kills the second derivative;
* **`exactStates_eq_longitudinal`** — the identification itself: the BRST-exact states are
  exactly the ghost-raised longitudinal fields,
  `exactStates Ω = ⊥ × {f | ∑ⱼ f(j) = 0}`, and the closure is the closure of the range by
  definition, so this is `closure (range Ω) = span{∂ᵢφ}` in the model;
* **`longitudinal_le_exactStates`** and **`physicalStates_eq`**: every longitudinal state is
  exact, hence zero in the cohomology, while the BRST-closed states are those whose gauge-field
  part is *constant* (`∂x = 0`) — the surviving gauge-field mode is the zero mode, which is what
  "no longitudinal soft zero-mode" says.

## Honest boundary

The equality is proved **in the periodic one-dimensional model**, with a bounded charge and a
single ghost.  The physical statement is about the ghost-dressed cubic charge of the
three-dimensional continuum theory acting on a field Hilbert space: there `Ω` is unbounded, the
gauge algebra is non-abelian (so `[Ω, A]` has the extra `commGaugeVec` term, as
`ChapterBrstLongitudinal` proves), and the charge couples infinitely many modes.  What this file
supplies is the *identification theorem* in the setting where both sides are defined objects;
the closure statement for the continuum charge still needs the field Hilbert space and the
closed unbounded `Ω` — the same missing inputs as `ChapterBrstHarmonicDecomposition`'s boundary.
No claim is made here about a continuum `H_phys`.
-/

namespace BookProof.BrstLongitudinalExact

noncomputable section

open Finset BookProof.BrstReducedTransfer

variable {n : ℕ}

/-! ## 1. The cyclic difference -/

/-- The cyclic shift on the lattice `Fin (n+1)`. -/
def shiftFun (f : Fin (n + 1) → ℂ) : Fin (n + 1) → ℂ := fun j => f (finRotate (n + 1) j)

/-- The cyclic shift as a linear map. -/
def shiftLin (n : ℕ) : (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) :=
  LinearMap.pi fun j => LinearMap.proj (φ := fun _ => ℂ) (finRotate (n + 1) j)

@[simp] theorem shiftLin_apply (f : Fin (n + 1) → ℂ) :
    shiftLin n f = shiftFun f := by
  funext j
  simp [shiftLin, shiftFun, LinearMap.pi_apply]

/-- The forward difference `∂f(j) = f(j+1) − f(j)` on the cycle. -/
def derivFun (f : Fin (n + 1) → ℂ) : Fin (n + 1) → ℂ := fun j => shiftFun f j - f j

/-- The forward difference as a linear map.  This is the gauge-field part of the charge: the
longitudinal direction `∂ᵢφ`. -/
def derivLin (n : ℕ) : (Fin (n + 1) → ℂ) →ₗ[ℂ] (Fin (n + 1) → ℂ) where
  toFun := derivFun
  map_add' f g := by
    funext j
    simp only [derivFun, shiftFun, Pi.add_apply]
    ring
  map_smul' c f := by
    funext j
    simp only [derivFun, shiftFun, Pi.smul_apply, RingHom.id_apply, smul_eq_mul]
    ring

@[simp] theorem derivLin_apply (f : Fin (n + 1) → ℂ) :
    derivLin n f = derivFun f := rfl

/-- The component sum, whose kernel is the space of mean-zero fields. -/
def sumLin (n : ℕ) : (Fin (n + 1) → ℂ) →ₗ[ℂ] ℂ :=
  ∑ j : Fin (n + 1), LinearMap.proj (φ := fun _ => ℂ) j

@[simp] theorem sumLin_apply (f : Fin (n + 1) → ℂ) : sumLin n f = ∑ j, f j := by
  simp [sumLin]

/-- **Mean-zero fields**: the orthogonal complement, in the finite lattice model, of the constant
(zero-mode) fields.  This is the space the gradient is shown to fill exactly. -/
def meanZeroSub (n : ℕ) : Submodule ℂ (Fin (n + 1) → ℂ) := LinearMap.ker (sumLin n)

theorem mem_meanZeroSub {f : Fin (n + 1) → ℂ} :
    f ∈ meanZeroSub n ↔ ∑ j, f j = 0 := by
  simp [meanZeroSub]

/-- The cyclic shift does not change the component sum. -/
theorem sum_shiftFun (f : Fin (n + 1) → ℂ) : ∑ j, shiftFun f j = ∑ j, f j :=
  Fintype.sum_equiv (finRotate (n + 1)) (fun j => shiftFun f j) f fun _ => rfl

/-- **The derivative has no zero mode**: the component sum of a gradient vanishes, so the image of
`∂` is orthogonal to the constants. -/
theorem sum_deriv (f : Fin (n + 1) → ℂ) : ∑ j, derivFun f j = 0 := by
  simp only [derivFun, Finset.sum_sub_distrib, sum_shiftFun, sub_self]

/-! ## 2. Every mean-zero field is a gradient -/

/-- The cumulative sum of a field: `cumFun f (m) = ∑_{k < m} f(k)`. -/
def cumFun (f : Fin (n + 1) → ℂ) : Fin (n + 1) → ℂ :=
  fun m => ∑ k : Fin (n + 1), if k.val < m.val then f k else 0

theorem cumFun_apply (f : Fin (n + 1) → ℂ) (m : Fin (n + 1)) :
    cumFun f m = ∑ k ∈ (Finset.univ.filter fun k : Fin (n + 1) => k.val < m.val), f k := by
  rw [cumFun, Finset.sum_filter]

theorem cumFun_zero (f : Fin (n + 1) → ℂ) : cumFun f 0 = 0 := by
  simp [cumFun]

/-- Telescoping: adding the term `f(j)` to the prefix sum. -/
theorem cumFun_succ (f : Fin (n + 1) → ℂ) (j : Fin n) :
    cumFun f (Fin.succ j) = cumFun f (Fin.castSucc j) + f (Fin.castSucc j) := by
  have hset : (Finset.univ.filter fun k : Fin (n + 1) => k.val < (Fin.succ j).val)
      = insert (Fin.castSucc j)
          (Finset.univ.filter fun k : Fin (n + 1) => k.val < (Fin.castSucc j).val) := by
    ext k
    simp only [Fin.val_succ, Fin.val_castSucc, Finset.mem_filter, Finset.mem_univ, true_and,
      Finset.mem_insert]
    constructor
    · intro hk
      rcases lt_or_eq_of_le (Nat.lt_succ_iff.mp hk) with h | h
      · exact Or.inr h
      · exact Or.inl (Fin.ext h)
    · rintro (rfl | hk)
      · exact Nat.lt_succ_self _
      · exact Nat.lt_succ_of_lt hk
  rw [cumFun_apply, cumFun_apply, hset]
  have hnot : (Fin.castSucc j) ∉
      (Finset.univ.filter fun k : Fin (n + 1) => k.val < (Fin.castSucc j).val) := by
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.val_castSucc]
    exact Nat.lt_irrefl _
  rw [Finset.sum_insert hnot]
  ring

/-- The prefix sum omits exactly the last component. -/
theorem cumFun_last (f : Fin (n + 1) → ℂ) :
    cumFun f (Fin.last n) = (∑ k, f k) - f (Fin.last n) := by
  have hset : (Finset.univ.filter fun k : Fin (n + 1) => k.val < (Fin.last n).val)
      = (Finset.univ : Finset (Fin (n + 1))).erase (Fin.last n) := by
    ext k
    rw [Finset.mem_filter, Finset.mem_erase]
    constructor
    · rintro ⟨-, hk⟩
      refine ⟨fun hc => ?_, Finset.mem_univ _⟩
      rw [hc] at hk
      exact lt_irrefl _ hk
    · rintro ⟨hne, -⟩
      refine ⟨Finset.mem_univ _, ?_⟩
      have h1 : k.val ≠ n := fun hc => hne (Fin.ext (by simpa using hc))
      have h2 := k.isLt
      have h3 : (Fin.last n).val = n := rfl
      omega
  rw [cumFun_apply, hset, Finset.sum_erase_eq_sub (Finset.mem_univ _)]

/-- **The cumulative sum inverts the derivative on mean-zero fields.**  This is the constructive
half of `range ∂ = mean-zero`: at every site except the last one the prefix telescopes, and at the
last site the wrap-around uses `∑ f = 0`. -/
theorem derivLin_cumFun (f : Fin (n + 1) → ℂ) (hsum : ∑ k, f k = 0) :
    derivLin n (cumFun f) = f := by
  funext m
  have hrot : finRotate (n + 1) m = m + 1 := finRotate_succ_apply m
  rw [derivLin_apply, derivFun, shiftFun, hrot]
  by_cases hm : m.val < n
  · set j : Fin n := ⟨m.val, hm⟩ with hj
    have hmc : m = Fin.castSucc j := Fin.ext rfl
    have hms : m + 1 = Fin.succ j := by
      apply Fin.ext
      rw [Fin.val_add_one]
      have : m ≠ Fin.last n := by
        intro hc
        rw [hc] at hm
        exact absurd hm (by simp)
      rw [if_neg this]
      simp [hj]
    rw [hms, hmc, cumFun_succ]
    ring
  · have hlast : m = Fin.last n := by
      apply Fin.ext
      have := m.isLt
      simp only [Fin.val_last]
      omega
    have hlast' : m + 1 = 0 := by
      apply Fin.ext
      rw [Fin.val_add_one, Fin.val_zero, if_pos hlast]
    rw [hlast', hlast, cumFun_zero, cumFun_last, hsum]
    ring

/-- **`range ∂` is exactly the mean-zero fields.**  One inclusion is `sum_deriv`; the other is
`derivLin_cumFun`.  Read on the image: the gradients `∂ᵢφ` fill the orthogonal complement of the
constant (zero-mode) fields, which is the finite-lattice Hodge statement behind "longitudinal =
exact". -/
theorem range_derivLin (n : ℕ) : LinearMap.range (derivLin n) = meanZeroSub n := by
  refine le_antisymm ?_ ?_
  · rintro y ⟨x, rfl⟩
    exact mem_meanZeroSub.mpr (sum_deriv x)
  · intro y hy
    refine ⟨cumFun y, derivLin_cumFun y ?_⟩
    exact mem_meanZeroSub.mp hy

/-! ## 3. The charge, its nilpotency, and the exact states -/

/-- The graded state space of the model: gauge fields paired with a two-dimensional ghost
occupation space (the ghost number is the second coordinate's role, and its triviality is what
makes the charge bounded). -/
abbrev stateSpace (n : ℕ) : Type := (Fin (n + 1) → ℂ) × (Fin (n + 1) → ℂ)

/-- **The BRST charge of the derivative gauge**: the derivative of the field, raising the ghost
number.  In the notation of `ChapterBrstLongitudinal` this is `Σᵢ ∂ᵢ c†`, i.e. the abelian charge
with the ghost dressing kept and the gauge algebra trivialized. -/
def brstCharge (n : ℕ) : stateSpace n →ₗ[ℂ] stateSpace n where
  toFun z := (0, derivLin n z.1)
  map_add' a b := by
    refine Prod.ext ?_ ?_
    · simp
    · simp [map_add]
  map_smul' c a := by
    refine Prod.ext ?_ ?_
    · simp
    · simp [map_smul]

/-- **Nilpotency `Ω² = 0`**: the ghost factor raises once, and the second application has no
field left to differentiate. -/
theorem brstCharge_nilpotent (n : ℕ) (z : stateSpace n) :
    brstCharge n (brstCharge n z) = 0 := by
  have h0 : derivFun (0 : Fin (n + 1) → ℂ) = 0 := by
    funext j
    simp [derivFun, shiftFun]
  simp [brstCharge, h0]

/-- The same charge as a continuous linear map, which is what the chapter's `exactStates` and
`physicalStates` consume.  Continuity is automatic in finite dimension. -/
noncomputable def brstChargeCLM (n : ℕ) : stateSpace n →L[ℂ] stateSpace n :=
  (brstCharge n).toContinuousLinearMap

/-- The longitudinal span: **no gauge field** (the ghost is raised) and a **mean-zero** field.
This is `span{∂ᵢφ}` in the model, characterized by `range_derivLin` rather than by definition. -/
def longitudinalSub (n : ℕ) : Submodule ℂ (stateSpace n) :=
  (⊥ : Submodule ℂ (Fin (n + 1) → ℂ)).prod (meanZeroSub n)

theorem mem_range_brstCharge {z : stateSpace n} :
    z ∈ LinearMap.range (brstCharge n) ↔ z.1 = 0 ∧ z.2 ∈ meanZeroSub n := by
  constructor
  · rintro ⟨w, rfl⟩
    refine ⟨rfl, ?_⟩
    have : derivLin n w.1 ∈ LinearMap.range (derivLin n) := ⟨w.1, rfl⟩
    rwa [range_derivLin] at this
  · rintro ⟨h1, h2⟩
    rw [← range_derivLin] at h2
    obtain ⟨x, hx⟩ := h2
    refine ⟨(x, 0), ?_⟩
    have hz : z = (0, z.2) := Prod.ext h1 rfl
    rw [hz]
    change ((0 : Fin (n + 1) → ℂ), derivLin n x) = (0, z.2)
    rw [hx]

/-- **The identification `closure (range Ω) = span{∂ᵢφ}`**, in the model: the BRST-exact states
are exactly the ghost-raised longitudinal fields.  The left-hand side is the closure of the range
(that is `exactStates`), the right-hand side is the longitudinal span of `longitudinalSub`,
characterized by the gradient's range. -/
theorem exactStates_eq_longitudinal (n : ℕ) :
    exactStates (brstChargeCLM n) = longitudinalSub n := by
  have hclosed : IsClosed
      ((LinearMap.range (brstChargeCLM n : stateSpace n →ₗ[ℂ] stateSpace n) :
        Submodule ℂ (stateSpace n)) : Set (stateSpace n)) :=
    Submodule.closed_of_finiteDimensional _
  rw [exactStates, hclosed.submodule_topologicalClosure_eq]
  refine SetLike.ext fun z => ?_
  change z ∈ LinearMap.range (brstCharge n) ↔ z ∈ longitudinalSub n
  rw [longitudinalSub, Submodule.mem_prod, Submodule.mem_bot]
  exact mem_range_brstCharge

/-- **Every longitudinal state is exact**, hence represents the zero class in the BRST
cohomology: no longitudinal gauge mode survives the reduction. -/
theorem longitudinal_le_exactStates (n : ℕ) :
    longitudinalSub n ≤ exactStates (brstChargeCLM n) :=
  (exactStates_eq_longitudinal n).ge

/-- **The BRST-closed states.**  A state is closed iff its gauge-field part is *constant*
(`∂x = 0`): the only gauge-field configuration in the kernel is the zero mode. -/
theorem physicalStates_eq (n : ℕ) :
    physicalStates (brstChargeCLM n)
      = (LinearMap.ker (derivLin n)).prod (⊤ : Submodule ℂ (Fin (n + 1) → ℂ)) := by
  refine SetLike.ext fun z => ?_
  rw [Submodule.mem_prod, mem_physicalStates]
  constructor
  · intro hz
    refine ⟨?_, trivial⟩
    have h2 : derivLin n z.1 = 0 := by
      have := congrArg Prod.snd hz
      simpa [brstCharge, brstChargeCLM] using this
    exact h2
  · rintro ⟨h1, -⟩
    simpa [brstCharge, brstChargeCLM] using h1

/-- The surviving gauge-field content of the cohomology: the constants.  Exact states have
`z.1 = 0`, so the first component of `physicalStates ⧸ exactStates` is a quotient of a space of
constant fields — the longitudinal modes are gone, the zero mode remains. -/
theorem disjoint_exact_constants (n : ℕ) :
    exactStates (brstChargeCLM n) ⊓
        ((LinearMap.ker (derivLin n)).prod (⊥ : Submodule ℂ (Fin (n + 1) → ℂ))) = ⊥ := by
  rw [eq_bot_iff]
  intro z hz
  rw [Submodule.mem_inf, exactStates_eq_longitudinal, longitudinalSub, Submodule.mem_prod]
    at hz
  obtain ⟨⟨hx, -⟩, -, hy⟩ := hz
  have hx0 : z.1 = 0 := by simpa using hx
  have hy0 : z.2 = 0 := by simpa using hy
  rw [Submodule.mem_bot]
  exact Prod.ext hx0 hy0

end

end BookProof.BrstLongitudinalExact
