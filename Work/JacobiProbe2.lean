import Work.SmSu3Ring
open BookProof.SmSu3

@[simp] theorem CQ.pow_two' (x : CQ) : x ^ 2 = x * x := by
  change CQ.npowOp 2 x = x * x
  rw [show (2 : ℕ) = 1 + 1 from rfl, CQ.npowOp_succ', CQ.npowOp_succ', CQ.npowOp_zero', one_mul]

@[simp] theorem mul_1_m2_sqrt3 :
    (⟨CQ.invSqrt3, 0⟩ : CQ) * ⟨-(CQ.invSqrt3 * 2), 0⟩ = CQ.ofRat (-2 / 3) := by
  ext <;> simp [CQ.invSqrt3] <;> ring

example (x y : CQ) : x * (⟨CQ.invSqrt3, 0⟩ : CQ) * ⟨-(CQ.invSqrt3 * 2), 0⟩ * y = 0 ∨ True := by
  simp
  left
  trace_state
  sorry
