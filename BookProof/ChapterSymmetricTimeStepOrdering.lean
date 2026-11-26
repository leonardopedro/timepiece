import Mathlib
import BookProof.ChapterQuantizationWeyl

/-!
# Chapter SymmetricTimeStepOrdering — H2's midpoint ordering and its negative control

`cftproof.md` H2 asks for a Euclidean Lie–Trotter/Strang product formula together with a
midpoint/Weyl ordering theorem for position–momentum cross-terms.  The general operator-norm
Lie–Trotter limit is **not** available in this Mathlib (and `ChapterSirkTrotterKato` proves a
different statement — strong resolvent convergence of a family, not a splitting formula), so
this module proves the exact algebraic half in the Heisenberg model where all BCH terms
terminate:

* `symmetric_time_step` — the Strang/midpoint step
  `exp(aX/2)·exp(bY)·exp(aX/2)` equals `exp(aX + bY)`: the first BCH commutator cancels;
* `endpoint_time_step_not_weyl` — the unsymmetric Lie step `exp(aX)·exp(bY)` differs from
  `exp(aX + bY)` by the central term `ab/2 · Z`, so endpoint time-slicing does **not**
  reproduce the Weyl-ordered Hamiltonian (the negative control H2 records).

Both are exact equalities of `3×3` matrices, proved from `exp_Ngen` and `Heis_mul`.  No
continuous-time limit, unbounded form sum, Euclidean measure or physical Hamiltonian is
used.  Axioms are `propext`, `Classical.choice`, `Quot.sound` only.
-/

set_option linter.unnecessarySeqFocus false
set_option linter.unusedTactic false
set_option linter.unreachableTactic false

noncomputable section

namespace BookProof.SymmetricTimeStepOrdering

open NormedSpace
open scoped Matrix
open BookProof.QuantizationWeyl

/-- The matrix of `aX + bY` is `Ngen a b 0`; the central correction is added by `Zgen`. -/
theorem Ngen_X_add_Y (a b : ℝ) : Ngen a 0 0 + Ngen 0 b 0 = Ngen a b 0 := by
  unfold Ngen
  ext i j
  fin_cases i <;> fin_cases j <;> simp

theorem smul_Zgen (c : ℝ) : c • Zgen = Ngen 0 0 c := by
  unfold Zgen Ngen
  ext i j
  fin_cases i <;> fin_cases j <;> simp

/-- The midpoint (Strang) time step has no BCH correction: it is exactly the Weyl-ordered
    exponential of the full generator. -/
theorem symmetric_time_step (a b : ℝ) :
    NormedSpace.exp ((a / 2) • Xgen) * NormedSpace.exp (b • Ygen) *
        NormedSpace.exp ((a / 2) • Xgen) =
      NormedSpace.exp (a • Xgen + b • Ygen) := by
  rw [smul_Xgen, smul_Ygen, smul_Xgen, Ngen_X_add_Y]
  simp only [exp_Ngen]
  rw [Heis_mul, Heis_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Heis] <;> ring_nf

/-- The endpoint (plain Lie) time step carries a central BCH term: it is not the Weyl
    exponential of `aX + bY` unless the commutator vanishes. -/
theorem endpoint_time_step_not_weyl (a b : ℝ) (hab : a * b ≠ 0) :
    NormedSpace.exp (a • Xgen) * NormedSpace.exp (b • Ygen) ≠
      NormedSpace.exp (a • Xgen + b • Ygen) := by
  intro h
  rw [smul_Xgen, smul_Ygen, Ngen_X_add_Y] at h
  simp only [exp_Ngen] at h
  rw [Heis_mul] at h
  have hentry := congrFun (congrFun h 0) 2
  simp [Heis] at hentry
  exact hab (by linarith)

/-- The exact defect of the endpoint step: the two products differ by the central element
    `(ab/2) Z`, i.e. by half the commutator `[aX, bY]`. -/
theorem endpoint_defect (a b : ℝ) :
    NormedSpace.exp (a • Xgen) * NormedSpace.exp (b • Ygen) =
      NormedSpace.exp (a • Xgen + b • Ygen) *
        NormedSpace.exp ((a * b / 2) • Zgen) := by
  rw [smul_Xgen, smul_Ygen, smul_Zgen, Ngen_X_add_Y]
  simp only [exp_Ngen]
  rw [Heis_mul, Heis_mul]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Heis] <;> ring_nf

end BookProof.SymmetricTimeStepOrdering
