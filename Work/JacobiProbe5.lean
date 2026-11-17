import Work.SmSu3Ring
open BookProof.SmSu3

example : ((3 : CQ)).re = Qsqrt3.ofRat 3 := by
  have h : (3 : CQ) = ⟨Qsqrt3.ofRat 3, 0⟩ := rfl
  rw [h]
  rfl

example (x : CQ) : x * (2 : CQ) * (3 : CQ) = 0 → True := by
  intro h
  trivial
