import Mathlib
import BookProof.YangMillsLadderTransport

/-!
# The magnetic ladder as an operator, and its vanishing diagonal part

`YangMillsLadderTransport` identifies the cut-off magnetic kernel with the matrix elements of the
Hermite creation ladder: `magCutoffKernel A m n = ∑ i, Aᵢ · creCoeff i (boxEmbed m) (boxEmbed n)`.
That is a statement about *entries*.  This module reads the same identity at the level of
**operators** on the truncated Fock space `Box d Λ → ℂ`, `Box d Λ = Fin d → Fin Λ`.

* `creOp Λ i` — the creation operator `a†ᵢ` with matrix `creCoeff i` in the occupation-number
  basis: `(creOp Λ i x) β = ∑ α, creCoeff i β α · x α`;
* `magCutoffOp Λ A` — the operator whose matrix *is* the cut-off magnetic kernel,
  `(magCutoffOp Λ A x) m = ∑ n, magCutoffKernel A m n · x n`;
* **`magCutoffOp_eq_sum_cre`** — `magCutoffOp Λ A = ∑ i, Aᵢ • creOp Λ i`.  So the magnetic
  kernel-sum operator *is* the sum of the creation ladders, as operators rather than entrywise;
* `occDeg` — the total occupation number `∑ i, mᵢ`, and `occProj Λ N` — the projection onto the
  degree-`N` subspace;
* **`occProj_comp_magCutoffOp_comp_occProj`** — the degree-preserving part of `magCutoffOp`
  vanishes at every degree: `proj_N ∘ magCutoffOp ∘ proj_N = 0`.  This is the operator-level
  form of "the magnetic term is purely off-diagonal in the occupation grading": the diagonal part
  of the reduced form is `diagUnb` and carries no ladder (`diagUnb_mem_reducedSector`).

## Boundary

The identification is made on the **cut-off** space, where all sums are finite: `Box d Λ` is a
finite type, so the kernel sum and the ladder sums are `Finset` sums and no summability or
boundedness of the operator is needed.  It is *not* a statement about the continuum: `ℓ²(Idx d)`
needs the Hilbert–Schmidt/relative-bound hypotheses of `YangMillsFormClosureNonDiagonal` §10–11,
and the operator there is unbounded (`ladder_form_norm_le` bounds its form, not its norm).  It is
also not a statement that `magCutoffOp` is the off-diagonal part of the *reduced* magnetic
operator of §24: what is proved is that the ladder component, read as an operator on the
truncated Fock space, is `∑ᵢ Aᵢ a†ᵢ` and has no degree-preserving part.  The step from here to
"the second-quantized Hamiltonian of the reduced theory equals `diagUnb + magCutoffOp`" still
needs the box-to-continuum limit and the BRST quotient, neither of which is formalized.
-/

namespace BookProof.YangMillsFormClosureND

open BookProof.HermiteBand BookProof.HermiteProductBasis

noncomputable section

variable {d : ℕ}

/-- The cut-off occupation-number space: `Fin d → Fin Λ`, on which the truncated magnetic kernel
lives.  As a finite type it carries a `Fintype` instance, so every sum below is a `Finset` sum. -/
abbrev Box (d : ℕ) (Λ : ℕ) : Type := Fin d → Fin Λ

/-! ## The creation operator on the truncated Fock space -/

/-- **The creation ladder `a†ᵢ` on the truncated Fock space**, with the transported matrix
elements `creCoeff`: `(creOp Λ i x) β = ∑ α, creCoeff i β α · x α`.  Because `creCoeff` uses
`boxEmbed` into `Idx d`, a raise that would leave the box has no target in `Box d Λ`, so the
truncation is built in. -/
def creOp (Λ : ℕ) (i : Fin d) : (Box d Λ → ℂ) →ₗ[ℂ] (Box d Λ → ℂ) where
  toFun x := fun β => ∑ α : Box d Λ, creCoeff i (boxEmbed β) (boxEmbed α) * x α
  map_add' x y := by
    ext β
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext β
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun α _ => ?_
    rw [RingHom.id_apply]
    ring

/-- The defining formula for `creOp`. -/
@[simp]
theorem creOp_apply (Λ : ℕ) (i : Fin d) (x : Box d Λ → ℂ) (β : Box d Λ) :
    creOp Λ i x β = ∑ α : Box d Λ, creCoeff i (boxEmbed β) (boxEmbed α) * x α := rfl

/-! ## The magnetic kernel, read as an operator -/

/-- **The magnetic kernel as an operator**: `(magCutoffOp Λ A x) m = ∑ n, K m n · x n`.  This is
the operator of the cut-off magnetic term, not just its matrix. -/
def magCutoffOp (Λ : ℕ) (A : Fin d → ℝ) : (Box d Λ → ℂ) →ₗ[ℂ] (Box d Λ → ℂ) where
  toFun x := fun m => ∑ n : Box d Λ, magCutoffKernel A m n * x n
  map_add' x y := by
    ext m
    simp only [Pi.add_apply, mul_add, Finset.sum_add_distrib]
  map_smul' c x := by
    ext m
    simp only [Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [RingHom.id_apply]
    ring

/-- The defining formula for `magCutoffOp`. -/
@[simp]
theorem magCutoffOp_apply (Λ : ℕ) (A : Fin d → ℝ) (x : Box d Λ → ℂ) (m : Box d Λ) :
    magCutoffOp Λ A x m = ∑ n : Box d Λ, magCutoffKernel A m n * x n := rfl

/-- **Operator-level identification of the ladder.**  The magnetic kernel-sum operator is the
sum of the creation ladders with the field-strength coefficients `Aᵢ`:

`magCutoffOp Λ A = ∑ i, Aᵢ • a†ᵢ`.

Both sides are functions of the mode, and they are sums over the same matrix elements; only the
order of summation differs (`Finset.sum_comm`). -/
theorem magCutoffOp_eq_sum_cre (Λ : ℕ) (A : Fin d → ℝ) :
    magCutoffOp Λ A = ∑ i : Fin d, (A i : ℂ) • creOp (d := d) Λ i := by
  refine LinearMap.ext fun x => ?_
  funext m
  rw [magCutoffOp_apply]
  simp only [LinearMap.coe_sum, Finset.sum_apply, LinearMap.smul_apply, creOp_apply,
    Pi.smul_apply, smul_eq_mul]
  have hterm : ∀ n : Box d Λ,
      magCutoffKernel A m n * x n
        = ∑ i : Fin d, (A i : ℂ) * (creCoeff i (boxEmbed m) (boxEmbed n) * x n) := by
    intro n
    rw [magCutoffKernel_eq_ladder, Finset.sum_mul]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp only [hterm]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.mul_sum]

/-! ## The occupation grading and the vanishing diagonal part -/

/-- The total occupation number `∑ i, vᵢ` of a mode, on `Idx d` so that the `boxEmbed`
bookkeeping drops out. -/
def occDeg (v : Fin d → ℕ) : ℕ := ∑ i, v i

theorem le_occDeg (v : Fin d → ℕ) (i : Fin d) : v i ≤ occDeg v := by
  classical
  have h : occDeg v = v i + ∑ j ∈ Finset.univ.erase i, v j := by
    rw [occDeg, ← Finset.add_sum_erase (Finset.univ : Finset (Fin d)) (fun j => v j)
      (Finset.mem_univ i)]
  rw [h]
  exact Nat.le_add_right _ _

/-- The occupation number after raising one coordinate. -/
theorem occDeg_update (v : Fin d → ℕ) (i : Fin d) (k : ℕ) :
    occDeg (Function.update v i k) = occDeg v - v i + k := by
  classical
  have h1 : occDeg (Function.update v i k) = k + ∑ j ∈ Finset.univ.erase i, v j := by
    rw [occDeg, ← Finset.add_sum_erase (Finset.univ : Finset (Fin d))
      (fun j => Function.update v i k j) (Finset.mem_univ i)]
    congr 1
    · simp
    · refine Finset.sum_congr rfl fun j hj => ?_
      rw [Function.update_apply, if_neg (Finset.ne_of_mem_erase hj)]
  have h2 : occDeg v = v i + ∑ j ∈ Finset.univ.erase i, v j := by
    rw [occDeg, ← Finset.add_sum_erase (Finset.univ : Finset (Fin d)) (fun j => v j)
      (Finset.mem_univ i)]
  have h3 := le_occDeg v i
  omega

theorem occDeg_update_self (v : Fin d → ℕ) (i : Fin d) :
    occDeg (Function.update v i (v i + 1)) = occDeg v + 1 := by
  rw [occDeg_update]
  have h3 := le_occDeg v i
  omega

/-- A transported matrix element is nonzero only at the raised index: the `creCoeff` form of
"the ladder moves one quantum". -/
theorem creCoeff_ne_zero_iff {i : Fin d} {β α : Fin d → ℕ} :
    creCoeff i β α ≠ 0 ↔ β = Function.update α i (α i + 1) := by
  have hne : ((Real.sqrt ((α i : ℝ) + 1) : ℝ) : ℂ) ≠ 0 := by
    have hpos : (0 : ℝ) < Real.sqrt ((α i : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    exact_mod_cast ne_of_gt hpos
  unfold creCoeff
  by_cases h : β = Function.update α i (α i + 1)
  · rw [if_pos h]
    exact ⟨fun _ => h, fun _ => hne⟩
  · rw [if_neg h]
    exact ⟨fun hc => absurd rfl hc, fun hc => absurd hc h⟩

/-- **A nonzero entry of the magnetic kernel raises the occupation number by one.** -/
theorem occDeg_boxEmbed_raise {Λ : ℕ} (A : Fin d → ℝ) {m n : Box d Λ}
    (h : magCutoffKernel A m n ≠ 0) :
    occDeg (boxEmbed m) = occDeg (boxEmbed n) + 1 := by
  rw [magCutoffKernel_eq_ladder] at h
  obtain ⟨i, -, hi⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  have hc : creCoeff i (boxEmbed m) (boxEmbed n) ≠ 0 := right_ne_zero_of_mul hi
  rw [creCoeff_ne_zero_iff] at hc
  rw [hc, occDeg_update_self]

/-- The degree-preserving entries of the magnetic kernel vanish. -/
theorem magCutoffKernel_eq_zero_of_occDeg_eq {Λ : ℕ} (A : Fin d → ℝ) {m n : Box d Λ}
    (h : occDeg (boxEmbed m) = occDeg (boxEmbed n)) : magCutoffKernel A m n = 0 := by
  by_contra hne
  have := occDeg_boxEmbed_raise A hne
  omega

/-- The projection onto the degree-`N` subspace of the truncated Fock space. -/
def occProj (Λ : ℕ) (N : ℕ) : (Box d Λ → ℂ) →ₗ[ℂ] (Box d Λ → ℂ) where
  toFun x := fun m => if occDeg (boxEmbed m) = N then x m else 0
  map_add' x y := by
    ext m
    by_cases h : occDeg (boxEmbed m) = N <;> simp [h]
  map_smul' c x := by
    ext m
    by_cases h : occDeg (boxEmbed m) = N <;> simp [h]

@[simp]
theorem occProj_apply (Λ : ℕ) (N : ℕ) (x : Box d Λ → ℂ) (m : Box d Λ) :
    occProj Λ N x m = if occDeg (boxEmbed m) = N then x m else 0 := rfl

/-- **The magnetic operator has no diagonal part.**  For every degree `N`, the part of
`magCutoffOp` that preserves the occupation grading vanishes:

`proj_N ∘ magCutoffOp Λ A ∘ proj_N = 0`.

This is an identity of operators, not of entries: it says the magnetic term is purely
off-diagonal in the grading by total occupation number, which is the shape a coupling must have,
and the reason the diagonal non-ladder part of the reduced form has to come from a separate term
(`diagUnb`). -/
theorem occProj_comp_magCutoffOp_comp_occProj (Λ : ℕ) (A : Fin d → ℝ) (N : ℕ) :
    (occProj (d := d) Λ N).comp ((magCutoffOp Λ A).comp (occProj (d := d) Λ N)) = 0 := by
  ext x m
  simp only [LinearMap.comp_apply, LinearMap.zero_apply]
  by_cases hm : occDeg (boxEmbed m) = N
  · rw [occProj_apply, if_pos hm, magCutoffOp_apply]
    refine Finset.sum_eq_zero fun n _ => ?_
    by_cases hn : occDeg (boxEmbed n) = N
    · rw [occProj_apply, if_pos hn, magCutoffKernel_eq_zero_of_occDeg_eq A (by rw [hm, hn])]
      ring
    · rw [occProj_apply, if_neg hn, mul_zero]
  · simp [occProj, hm]

end

end BookProof.YangMillsFormClosureND
