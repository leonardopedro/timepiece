import Work.SmSu3Ring
open BookProof.SmSu3
#check @CQ.natCast_re
example : ((3 : CQ)).re = Qsqrt3.ofRat 3 := by
  simp only [CQ.natCast_re]
