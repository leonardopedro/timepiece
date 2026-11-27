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
set_option linter.flexible false

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

/-- The exponential of a Heisenberg generator is a one-parameter subgroup: its `n`th power is
    the exponential at `n` times the parameters.  This is the algebraic core of `cft_path.md`'s
    time-slicing identity `exp(−iHT) = (exp(−iHε))^N` in the model where BCH terminates. -/
theorem exp_Ngen_pow (a b : ℝ) (n : ℕ) :
    (NormedSpace.exp (Ngen a b 0)) ^ n =
      NormedSpace.exp (Ngen ((n : ℝ) * a) ((n : ℝ) * b) 0) := by
  induction n with
  | zero =>
      simp only [pow_zero, Nat.cast_zero, zero_mul, zero_div]
      rw [exp_Ngen]
      ext i j <;> fin_cases i <;> fin_cases j <;> simp [Heis]
  | succ n ih =>
      rw [pow_succ, ih]
      rw [exp_Ngen, exp_Ngen, exp_Ngen]
      rw [Heis_mul]
      ext i j <;> fin_cases i <;> fin_cases j <;> simp [Heis] <;> ring

/-- Midpoint time-slicing is exact for every number of steps: `N` Strang steps at width `ε`
    give the exponential of the full generator at time `Nε`.  This is the finite analogue of the
    continuum sum in `cft_path.md` §1–§3, with no accumulated ordering error. -/
theorem symmetric_time_step_pow (a b : ℝ) (n : ℕ) :
    (NormedSpace.exp ((a / 2) • Xgen) * NormedSpace.exp (b • Ygen) *
        NormedSpace.exp ((a / 2) • Xgen)) ^ n =
      NormedSpace.exp (Ngen ((n : ℝ) * a) ((n : ℝ) * b) 0) := by
  rw [symmetric_time_step, smul_Xgen, smul_Ygen, Ngen_X_add_Y]
  exact exp_Ngen_pow a b n

/-- The plain Lie step is the exponential of one generator whose central parameter is half the
    commutator coefficient `ab/2` — the Weyl cocycle of the unordered product. -/
theorem endpoint_time_step_eq_exp (a b : ℝ) :
    NormedSpace.exp (a • Xgen) * NormedSpace.exp (b • Ygen) =
      NormedSpace.exp (Ngen a b (a * b / 2)) := by
  rw [smul_Xgen, smul_Ygen, exp_Ngen, exp_Ngen, exp_Ngen, Heis_mul]
  ext i j <;> fin_cases i <;> fin_cases j <;> simp [Heis] <;> ring

/-- Endpoint time-slicing accumulates its central defect linearly in the step count: `n` Lie
    steps carry `n·ab/2` in the central parameter.  The defect does not cancel across steps. -/
theorem endpoint_time_step_pow (a b : ℝ) (n : ℕ) :
    (NormedSpace.exp (a • Xgen) * NormedSpace.exp (b • Ygen)) ^ n =
      NormedSpace.exp (Ngen ((n : ℝ) * a) ((n : ℝ) * b) ((n : ℝ) * a * b / 2)) := by
  rw [endpoint_time_step_eq_exp]
  induction n with
  | zero =>
      simp only [pow_zero, Nat.cast_zero, zero_mul, zero_div]
      rw [exp_Ngen]
      ext i j <;> fin_cases i <;> fin_cases j <;> simp [Heis]
  | succ n ih =>
      rw [pow_succ, ih]
      rw [exp_Ngen, exp_Ngen, exp_Ngen]
      rw [Heis_mul]
      ext i j <;> fin_cases i <;> fin_cases j <;> simp [Heis] <;> ring

/-- Endpoint slicing never reproduces the Weyl exponential of the full generator once the
    commutator is nonzero, at any positive step count.  The `n = 1` negative control
    `endpoint_time_step_not_weyl` is the special case; no continuum limit repairs it here. -/
theorem endpoint_pow_ne_symmetric_pow {a b : ℝ} (hab : a * b ≠ 0) {n : ℕ} (hn : 0 < n) :
    (NormedSpace.exp (a • Xgen) * NormedSpace.exp (b • Ygen)) ^ n ≠
      NormedSpace.exp (Ngen ((n : ℝ) * a) ((n : ℝ) * b) 0) := by
  rw [endpoint_time_step_pow]
  intro h
  have hentry := congrFun (congrFun h 0) 2
  simp [exp_Ngen, Heis] at hentry
  rcases hentry with (hn0' | ha) | hb
  · exact (ne_of_gt hn) hn0'
  · exact hab (by simp [ha])
  · exact hab (by simp [hb])

end BookProof.SymmetricTimeStepOrdering
