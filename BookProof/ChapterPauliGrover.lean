import Mathlib
import BookProof.ChapterConditional

/-!
# Chapter B §3 — a concrete unitary parametrization: the Pauli–Grover rotation

Source: the Pauli–Grover construction of `QFM.tex`
(`\section{Alternate Hamiltonian: the Pauli--Grover construction}`,
`\label{sec:pauli-grover}`), read as a concrete finite-dimensional instance of the
unitary parametrization of a regular conditional probability (`book.tex` §3 *"Any
conditional probability measure in a standard measure space is parametrized by a
unitary operator"*, formalized abstractly in `ChapterJointUnitary` and
`ChapterConditional`).  The section is `sec:pauli-grover` of `QFM.tex`, and §11 of
the book quotes it (`Book/ConditionalUnitary.lean`).

The Pauli–Grover Hamiltonian acts, for each training pair `(i, fᵢ)`, as a Pauli-X
rotation in the two-dimensional subspace `{ |i,0⟩, |i,fᵢ⟩ }`. In the ideal case
`a = 1` this rotation is exactly the swap `|0⟩ ↔ |f⟩`, so that evolving `|0⟩` for
time `τ = π/2` yields `|f⟩` up to an unobservable global phase. The readout
probability of output `f` given input `0` is therefore `1`: the unitary parametrizes
a *deterministic* regular conditional probability (a perfect classifier on the
training pair).

Here we formalize the single-input, two-output core (`X = Y = Fin 2`):

* `pauliX` — the swap (Pauli-X) matrix in the `{ |0⟩, |f⟩ }` basis;
* `pauliX_unitary` — it is a unitary, hence a valid instance of the parametrization
  of `ChapterJointUnitary`;
* `pauliX_rotates` — its action `|0⟩ ↦ |f⟩` (entry `(1,0) = 1`, entry `(0,0) = 0`);
* `pauliX_parametrizes_delta` — the Born readout of column `0` is the delta
  distribution on output `1`;
* `pauliGrover_joint_one`, `pauliGrover_marg_one`, `pauliGrover_cond_one` — through
  the `ChapterConditional` layer, the joint and marginal concentrate on the training
  pair and the regular conditional probability `p(f|0) = 1`.

Everything is `sorry`-free. The imperfect-rotation case `a < 1` (a tunable
approximation) and the many-input sum / Krylov start of `QFM.tex` are described in
the book prose; the ideal `a = 1` swap proved here is the case `QFM.tex` reports as
achieving 100% training accuracy.
-/

open scoped BigOperators Matrix ComplexConjugate
open Matrix
open BookProof.ChapterConditional

namespace BookProof.ChapterPauliGrover

/-- The Pauli-X (swap) matrix on the two-dimensional subspace `{ |0⟩, |f⟩ }`:
zero on the diagonal, one off the diagonal. This is the ideal (`a = 1`)
Pauli–Grover Hamiltonian in the `{ |0⟩, |f⟩ }` basis, which swaps `|0⟩` and
`|f⟩`. -/
noncomputable def pauliX : Matrix (Fin 2) (Fin 2) ℂ :=
  fun i j => if i = j then 0 else 1

/-- The swap is real and symmetric, hence self-adjoint. -/
theorem pauliX_conjTranspose : pauliX.conjTranspose = pauliX := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [pauliX, Matrix.conjTranspose_apply]

/-- The swap is an involution: `pauliX² = 1`. -/
theorem pauliX_sq : pauliX * pauliX = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pauliX, Matrix.mul_apply, Fin.sum_univ_two]

/-- **The Pauli–Grover rotation is a unitary.** It is therefore a valid concrete
instance of the unitary parametrization of `ChapterJointUnitary`. -/
theorem pauliX_unitary : pauliX ∈ Matrix.unitaryGroup (Fin 2) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, star_eq_conjTranspose, pauliX_conjTranspose]
  exact pauliX_sq

/-- **The rotation action** `|0⟩ ↦ |f⟩`: the `(f, 0)` entry is `1` and the
`(0, 0)` entry is `0`. -/
theorem pauliX_rotates : pauliX 1 0 = 1 ∧ pauliX 0 0 = 0 := by
  constructor <;> simp [pauliX]

/-- **Born readout.** The squared modulus of column `0` is the delta distribution
concentrated on output `1`: the swap parametrizes a deterministic output. -/
theorem pauliX_parametrizes_delta (y : Fin 2) :
    ‖pauliX y 0‖ ^ 2 = (if y = 1 then 1 else 0 : ℝ) := by
  fin_cases y <;> simp [pauliX]

/-- The joint probability `p(0, f) = |pauliX(f, 0)|²` concentrates on the training
pair `(0, 1)`. -/
theorem pauliGrover_joint_one : pJoint pauliX (0 : Fin 2) 1 = 1 := by
  simp [pJoint, pauliX]

/-- The marginal `p(0) = ∑_f |pauliX(f, 0)|² = 1`, so the regular conditional
probability at input `0` is well-defined. -/
theorem pauliGrover_marg_one : pMarg pauliX (0 : Fin 2) = 1 := by
  simp [pMarg, pauliX, Fin.sum_univ_two]

/-- **Headline: the Pauli–Grover rotation parametrizes a deterministic regular
conditional probability.** The conditional probability of the target output `f = 1`
given the training input `0` is `p(f|0) = 1` — perfect training accuracy. -/
theorem pauliGrover_cond_one : pCond pauliX (0 : Fin 2) 1 = 1 := by
  rw [pCond, pauliGrover_joint_one, pauliGrover_marg_one]
  norm_num

end BookProof.ChapterPauliGrover
