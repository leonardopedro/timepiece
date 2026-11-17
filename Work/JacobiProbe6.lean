import Work.SmSu3Ring
open BookProof.SmSu3

example (x y : Qsqrt3) (h : (3 : Qsqrt3) * x = 3 * y) : x = y := by
  ext
  · have hre := congrArg Qsqrt3.re h
    simp only [Qsqrt3.mul_re] at hre
    norm_num at hre
    nlinarith
  · have him := congrArg Qsqrt3.im h
    simp only [Qsqrt3.mul_re, Qsqrt3.mul_im] at him
    norm_num at him
    nlinarith
