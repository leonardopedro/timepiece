import Work.SmSu3Ring
open BookProof.SmSu3
set_option pp.all true in
example : ((3 : CQ)).re = ((3 : Qsqrt3)) := by rfl
example : ((3 : Qsqrt3)) = Qsqrt3.ofRat 3 := by rfl
