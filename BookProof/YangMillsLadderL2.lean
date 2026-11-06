import Mathlib
import BookProof.YangMillsLadderOperator

/-!
# The magnetic ladder on `ℓ²(Idx d)`: the operator identity without a cut-off

`YangMillsLadderOperator.magCutoffOp_eq_sum_cre` proves `magCutoffOp Λ A = ∑ᵢ Aᵢ • creOp Λ i` on the
truncated space `Box d Λ → ℂ`, where every sum is finite because `Box d Λ` is a finite type.
`YangMillsLadderTransport.magCutoffKernel_eq_ladder` is the entrywise version on the unbounded
index `Idx d`, but still for the *cut-off* kernel and the *cut-off* box.

This module removes the cut-off from the operator statement.  On the algebraic core
`CoreCoeff d = (Idx d →₀ ℂ)` of `ℓ²(Idx d)` — the dense subspace `coreEmbed` of
`YangMillsFormClosure` — the creation ladder is an honest endomorphism

`creCore i c = ∑_{α ∈ supp c} c α • single (update α i (αᵢ + 1)) (√(αᵢ + 1))`,

and `magCore A := ∑ᵢ Aᵢ • creCore i` satisfies, for every occupation function `β : Idx d`,

`(magCore A (single α x)) β = ∑ᵢ Aᵢ · creCoeff i β α · x`   (`magCore_single_apply`),

which is `magCutoffOp_eq_sum_cre` with `Box d Λ` replaced by `Idx d` and no `Λ` at all: the matrix
of `magCore A` in the occupation basis *is* the transported ladder of
`YangMillsLadderTransport.creCoeff`.  Its support sits in degree `occDeg α + 1`, so the operator is
unbounded on `ℓ²(Idx d)` — it raises the degree, and each raised vector has norm
`‖x‖ · |Aᵢ| · √(αᵢ + 1)`, which grows with the occupation numbers rather than decaying.

## Boundary

The identity is proved on the core, not on the whole of `ℓ²(Idx d)`: `magCore A` does not preserve
`ℓ²`, because raising a coordinate multiplies the norm by `√(αᵢ + 1)` without bound.  What the
Hilbert–Schmidt and relative-bound results of `YangMillsFormClosureNonDiagonal` §10–11 supply is
the *form* estimate, and that is where this identity has to be consumed: the quadratic form of
`magCore` on a core vector is the kernel form of the zero-extended `boxKernel`
(`closedKernelForm_coreEmbed`), and `closed_farisLavine_boxKernel` /
`ladder_closed_domination_sharp` bound it by the degree form with a relative constant below `1`.
  Turning that form bound into a
closed (or self-adjoint) operator on `ℓ²(Idx d)`, and identifying it with the magnetic part of the
reduced Hamiltonian of §24, is not formalized here.
-/

namespace BookProof.YangMillsFormClosureND

open BookProof.HermiteBand BookProof.HermiteProductBasis
open BookProof.YangMillsFormClosure BookProof.ReferenceGap

noncomputable section

variable {d : ℕ}

/-! ## The ladder on the core -/

/-- **The creation ladder `a†ᵢ` on the core of `ℓ²(Idx d)`.**  It raises the occupation number in
direction `i` by one and multiplies the coefficient by `√(αᵢ + 1)`; since the coefficient family is
finitely supported, so is the image. -/
def creCore (i : Fin d) (c : CoreCoeff d) : CoreCoeff d :=
  c.sum fun α x =>
    Finsupp.single (Function.update α i (α i + 1)) (x * ((Real.sqrt ((α i : ℝ) + 1) : ℝ) : ℂ))

/-- The ladder on a basis vector: one term, raised once. -/
theorem creCore_single (i : Fin d) (α : Idx d) (x : ℂ) :
    creCore i (Finsupp.single α x)
      = Finsupp.single (Function.update α i (α i + 1))
          (x * ((Real.sqrt ((α i : ℝ) + 1) : ℝ) : ℂ)) := by
  classical
  rw [creCore, Finsupp.sum_single_index (by simp)]

/-- **The magnetic ladder operator on the core**, `∑ᵢ Aᵢ a†ᵢ` — the cut-off-free analogue of
`magCutoffOp`, with no finite box anywhere in its definition. -/
def magCore (A : Fin d → ℝ) (c : CoreCoeff d) : CoreCoeff d :=
  ∑ i, (A i : ℂ) • creCore i c

/-- **The operator identity, in the form of a restatement**: `magCore` is the sum of the ladders,
exactly as `magCutoffOp_eq_sum_cre` says on the box. -/
theorem magCore_eq_sum_cre (A : Fin d → ℝ) (c : CoreCoeff d) :
    magCore A c = ∑ i, (A i : ℂ) • creCore i c :=
  rfl

/-- The ladder computed on a basis vector, as an explicit finite sum over the directions. -/
theorem magCore_single (A : Fin d → ℝ) (α : Idx d) (x : ℂ) :
    magCore A (Finsupp.single α x)
      = ∑ i, Finsupp.single (Function.update α i (α i + 1))
          (x * (A i : ℂ) * ((Real.sqrt ((α i : ℝ) + 1) : ℝ) : ℂ)) := by
  classical
  rw [magCore]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [creCore_single, Finsupp.smul_single]
  congr 1
  simp only [smul_eq_mul]
  ring

/-- **The matrix elements of the magnetic ladder on `Idx d`.**  For every occupation function `β`,
the coefficient of `β` in `magCore A (single α x)` is `∑ᵢ Aᵢ · creCoeff i β α · x`: the sum of the
transported ladder's matrix elements, with the cut-off box and the parameter `Λ` gone. -/
theorem magCore_single_apply (A : Fin d → ℝ) (α : Idx d) (x : ℂ) (β : Idx d) :
    (magCore A (Finsupp.single α x)) β
      = ∑ i, (A i : ℂ) * creCoeff i β α * x := by
  classical
  rw [magCore_single]
  simp only [Finsupp.finset_sum_apply, Finsupp.single_apply, creCoeff]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : β = Function.update α i (α i + 1)
  · subst h
    simp [mul_assoc, mul_comm]
  · have h' : Function.update α i (α i + 1) ≠ β := fun hc => h hc.symm
    simp [h, h']

/-! ## The degree grading: the ladder is unbounded -/

/-- Raising one coordinate raises the total occupation number by one. -/
theorem occDeg_update_raise (α : Idx d) (i : Fin d) :
    occDeg (Function.update α i (α i + 1)) = occDeg α + 1 := by
  simpa using occDeg_update_self α i

/-- **The ladder raises the degree**: every coefficient of `magCore A (single α x)` sits in total
occupation number `occDeg α + 1`, so the operator is not bounded on `ℓ²(Idx d)` and its degree is
exactly one above the input's. -/
theorem magCore_support_occDeg {A : Fin d → ℝ} {α : Idx d} {x : ℂ} {β : Idx d}
    (hβ : β ∈ (magCore A (Finsupp.single α x)).support) : occDeg β = occDeg α + 1 := by
  classical
  rw [Finsupp.mem_support_iff] at hβ
  by_contra h
  apply hβ
  rw [magCore_single_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hne : β ≠ Function.update α i (α i + 1) := fun hc => h (by rw [hc, occDeg_update_raise])
  rw [creCoeff_eq_zero_of_ne hne]
  ring

end

end BookProof.YangMillsFormClosureND
