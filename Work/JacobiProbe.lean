import Work.SmSu3Ring

open BookProof.SmSu3

namespace BookProof.SmSu3

@[simp] theorem CQ.pow_two' (x : CQ) : x ^ 2 = x * x := by
  change CQ.npowOp 2 x = x * x
  rw [show (2 : ℕ) = 1 + 1 from rfl, CQ.npowOp_succ', CQ.npowOp_succ', CQ.npowOp_zero', one_mul]

@[simp] theorem CQ.I_mul_self : CQ.I * CQ.I = -1 := by
  ext <;> simp [CQ.I] <;> ring

@[simp] theorem CQ.I_sq : CQ.I ^ 2 = -1 := by
  rw [CQ.pow_two', CQ.I_mul_self]

/-- The generators with `λ_8 * sqrt 3 = diag(1,1,-2)`, so that every entry is an integer. -/
def gmZ : Fin 8 → M3
  | 7 => !![1, 0, 0; 0, 1, 0; 0, 0, -2]
  | e => gm e

/-- The seven-term sum over the `λ` index. -/
def sum7 (u : Fin 8 → CQ) : CQ := u 0 + u 1 + u 2 + u 3 + u 4 + u 5 + u 6

@[simp] theorem gmZ_seven : gmZ 7 = !![1, 0, 0; 0, 1, 0; 0, 0, -2] := rfl

end BookProof.SmSu3

set_option maxHeartbeats 4000000 in
open BookProof.SmSu3 in
example (M N : M3) :
    3 * sum7 (fun e => mtrace (mmul M (gm e)) * mtrace (mmul N (gm e))) +
        mtrace (mmul M (gmZ 7)) * mtrace (mmul N (gmZ 7)) + 2 * (mtrace M * mtrace N) =
      6 * mtrace (mmul M N) := by
  simp [sum7, gm, gmZ, mtrace, mmul]
  ring_nf
  simp [CQ.I_sq]
  ring
