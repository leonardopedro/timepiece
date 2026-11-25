import BookProof.Phi4.ChapterScalarMomRankTwo

/-!
# The rank-two continuous orbit

This module starts `P9`: the rational quadratic-algebra certificate is mapped
into `ℂ` before the exponential orbit is formed.  The remaining analytic
contractivity and two-sided return interval are recorded in the plan.
-/

namespace BookProof.Phi4.MomRankTwo

open Matrix

noncomputable section

/-- The ring map `ℚ[i] → ℂ` sending the rational basis element to `Complex.I`. -/
noncomputable def toComplex : QI →+* ℂ where
  toFun z := (z.re : ℂ) + (z.im : ℂ) * Complex.I
  map_one' := by
    show ((1 : QI).re : ℂ) + ((1 : QI).im : ℂ) * Complex.I = 1
    simp [QuadraticAlgebra.im_one]
  map_zero' := by
    show ((0 : QI).re : ℂ) + ((0 : QI).im : ℂ) * Complex.I = 0
    simp
  map_add' := by
    intro x y
    show (((x + y).re : ℂ) + ((x + y).im : ℂ) * Complex.I) =
      ((x.re : ℂ) + (x.im : ℂ) * Complex.I) +
        ((y.re : ℂ) + (y.im : ℂ) * Complex.I)
    simp
    ring
  map_mul' := by
    intro x y
    show (((x * y).re : ℂ) + ((x * y).im : ℂ) * Complex.I) =
      ((x.re : ℂ) + (x.im : ℂ) * Complex.I) *
        ((y.re : ℂ) + (y.im : ℂ) * Complex.I)
    simp only [QuadraticAlgebra.re_mul, QuadraticAlgebra.im_mul]
    ring_nf
    rw [pow_two, Complex.I_mul_I]
    push_cast
    ring

theorem toComplex_star (z : QI) : toComplex (star z) = star (toComplex z) := by
  show ((star z).re : ℂ) + ((star z).im : ℂ) * Complex.I =
    star ((z.re : ℂ) + (z.im : ℂ) * Complex.I)
  simp [QuadraticAlgebra.re_star, QuadraticAlgebra.im_star]

/-- Entrywise complexification of a rational matrix. -/
noncomputable def toCMat {m n : ℕ} (A : Mat m n) : Matrix (Fin m) (Fin n) ℂ :=
  A.map toComplex

theorem toCMat_mul {m n o : ℕ} (A : Mat m n) (B : Mat n o) :
    toCMat (A * B) = toCMat A * toCMat B := by
  simp [toCMat, Matrix.map_mul]

theorem toCMat_one (n : ℕ) : toCMat (1 : Mat n n) = 1 := by
  ext i j
  simp [toCMat, Matrix.one_apply]

theorem toCMat_conjTranspose {m n : ℕ} (A : Mat m n) :
    toCMat A.conjTranspose = (toCMat A).conjTranspose := by
  ext i j
  simp [toCMat, Matrix.conjTranspose_apply, toComplex_star]

theorem toCMat_trace {n : ℕ} (A : Mat n n) :
    (toCMat A).trace = toComplex A.trace := by
  simp [toCMat, Matrix.trace, map_sum]

theorem toCMat_hermitian {n : ℕ} (A : Mat n n) (h : A.conjTranspose = A) :
    (toCMat A).conjTranspose = toCMat A := by
  rw [← toCMat_conjTranspose, h]

end

end BookProof.Phi4.MomRankTwo
