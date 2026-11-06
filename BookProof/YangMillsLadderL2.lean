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
reduced Hamiltonian of §24, is not formalized here.  It also cannot be done for `magCore` itself:
the bare ladder is not symmetric (`magKernel_asymm`), so there is no self-adjoint operator agreeing
with it on the core.  The symmetric object is `magSymKernel`, the ladder plus its transpose; that
is the kernel whose form `closedKernelForm` sees, and pushing the domination through it is what a
self-adjoint realization would have to consume.
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

/-! ## The matrix of the ladder, without a box -/

/-- The matrix of the ladder on `Idx d × Idx d`: `magKernel A m n` is the coefficient of `m` in the
image of the occupation state `n`.  No box, no `Λ`. -/
def magKernel (A : Fin d → ℝ) (m n : Idx d) : ℂ :=
  ∑ i, (A i : ℂ) * creCoeff i m n

/-- The core identity and the matrix are the same object: `magKernel` is the matrix of `magCore`. -/
theorem magCore_single_eq_kernel (A : Fin d → ℝ) (n : Idx d) (x : ℂ) (m : Idx d) :
    (magCore A (Finsupp.single n x)) m = magKernel A m n * x := by
  rw [magCore_single_apply, magKernel, Finset.sum_mul]

/-- **The entry at a raise**, exactly: raising direction `i` gives `Aᵢ √(nᵢ + 1)`. -/
theorem magKernel_raise (A : Fin d → ℝ) (n : Idx d) (i : Fin d) :
    magKernel A (Function.update n i (n i + 1)) n
      = (A i : ℂ) * ((Real.sqrt ((n i : ℝ) + 1) : ℝ) : ℂ) := by
  classical
  rw [magKernel]
  have hzero : ∀ j : Fin d, j ≠ i →
      (A j : ℂ) * creCoeff j (Function.update n i (n i + 1)) n = 0 := by
    intro j hj
    have hne : Function.update n i (n i + 1) ≠ Function.update n j (n j + 1) := by
      intro hc
      have h := congrFun hc j
      simp only [Function.update_apply] at h
      split_ifs at h <;> omega
    rw [creCoeff_eq_zero_of_ne hne, mul_zero]
  rw [Finset.sum_eq_single i (fun j _ hj => hzero j hj)
    (fun h => absurd (Finset.mem_univ i) h)]
  rw [creCoeff_self]

/-- **The entry at a lowering is zero**: the bare ladder only creates. -/
theorem magKernel_lower (A : Fin d → ℝ) (n : Idx d) (i : Fin d) :
    magKernel A n (Function.update n i (n i + 1)) = 0 := by
  classical
  rw [magKernel]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hne : n ≠ Function.update (Function.update n i (n i + 1)) j
      (Function.update n i (n i + 1) j + 1) := by
    intro hc
    have h := congrFun hc j
    rw [Function.update_apply, if_pos rfl] at h
    by_cases hji : j = i
    · subst hji
      rw [Function.update_apply, if_pos rfl] at h
      omega
    · rw [Function.update_apply, if_neg hji] at h
      omega
  rw [creCoeff_eq_zero_of_ne hne, mul_zero]

/-- **The bare ladder is not symmetric**: at a raise its entry is `Aᵢ√(nᵢ + 1)` and at the
corresponding lowering it vanishes, so `magKernel A m n ≠ magKernel A n m` as soon as some `Aᵢ` is
nonzero.  Hence no symmetric — in particular no self-adjoint — operator agrees with `magCore` on
the core; the symmetric object is `magSymKernel`. -/
theorem magKernel_asymm {A : Fin d → ℝ} (hA : ∃ i, A i ≠ 0) :
    ∃ m n : Idx d, magKernel A m n ≠ magKernel A n m := by
  classical
  obtain ⟨i, hi⟩ := hA
  refine ⟨Function.update (fun _ : Fin d => (0 : ℕ)) i 1, fun _ => 0, ?_⟩
  have h1 : magKernel A (Function.update (fun _ : Fin d => (0 : ℕ)) i 1) (fun _ => 0)
      = (A i : ℂ) * ((Real.sqrt ((0 : ℝ) + 1) : ℝ) : ℂ) := by
    simpa using magKernel_raise A (fun _ : Fin d => (0 : ℕ)) i
  have h2 : magKernel A (fun _ : Fin d => (0 : ℕ))
      (Function.update (fun _ : Fin d => (0 : ℕ)) i 1) = 0 := by
    simpa using magKernel_lower A (fun _ : Fin d => (0 : ℕ)) i
  rw [h1, h2]
  have hval : ((Real.sqrt ((0 : ℝ) + 1) : ℝ) : ℂ) = 1 := by norm_num
  rw [hval, mul_one]
  intro hzero
  exact hi (by
    have := congrArg Complex.re hzero
    simpa using this)

/-- **The symmetric kernel**: the ladder plus its transpose.  This is the matrix a self-adjoint
magnetic operator on `ℓ²(Idx d)` is built from, and the one whose form the Hilbert–Schmidt and
relative-bound results bound. -/
def magSymKernel (A : Fin d → ℝ) (m n : Idx d) : ℂ :=
  magKernel A m n + magKernel A n m

theorem magSymKernel_comm (A : Fin d → ℝ) (m n : Idx d) :
    magSymKernel A m n = magSymKernel A n m := by
  rw [magSymKernel, magSymKernel, add_comm]

end

end BookProof.YangMillsFormClosureND
