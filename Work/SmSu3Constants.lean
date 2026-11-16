import Work.Qsqrt3

/-!
# The `su(3)` structure constants, derived from the Gell-Mann generators

`smStruct` in `BookProof` takes `f3 : Fin 8 → Fin 8 → Fin 8 → ℝ` as a parameter, so the ghost
sector's
matrix cannot be instantiated without a concrete `f3`.  This file derives one, in exact arithmetic:

* `gm : Fin 8 → Matrix (Fin 3) (Fin 3) CQ` — the Gell-Mann matrices, where `CQ` is
  `Q(sqrt 3) + Q(sqrt 3) * i`, so `1/√3` is `(0, 1/3)` and `i` is `(0, 1)` with no floating point;
* `f3Q a b c := Im(tr([λ_a, λ_b] λ_c)) / 4`, the trace formula (with `T_a = λ_a / 2` absorbed: the
  `-i/4` prefactor of `f = -(i/4) tr([λ_a,λ_b]λ_c)` becomes this quarter because the trace is purely
  imaginary);
* the standard table as a *computed* consequence — `f3Q 0 1 2 = 1`, the six `1/2` constants, and the
  two `√3/2` weak constants — each proved by evaluating the trace formula, never by citing a list.

The proofs evaluate the concrete `3 x 3` computation: `simp` unfolds the generators and the matrix
product, `ext` splits the exact pair, and `norm_num` closes in `ℚ`.  `decide` cannot be used here
because kernel reduction gets stuck on `ℚ` equality, and `native_decide` is excluded by the axiom
rule.

Nothing in this file is used by the build.
-/

namespace BookProof.SmSu3

open Qsqrt3

/-- `Q(sqrt 3) + Q(sqrt 3) i`: the complex numbers over the exact field, for the Gell-Mann entries.
-/
structure CQ where
  re : Qsqrt3
  im : Qsqrt3
  deriving DecidableEq, Repr

namespace CQ

def add (x y : CQ) : CQ := ⟨x.re + y.re, x.im + y.im⟩
def neg (x : CQ) : CQ := ⟨-x.re, -x.im⟩
def mul (x y : CQ) : CQ := ⟨x.re * y.re - x.im * y.im, x.re * y.im + x.im * y.re⟩
def zero : CQ := ⟨0, 0⟩
def one : CQ := ⟨1, 0⟩

instance : Add CQ := ⟨add⟩
instance : Neg CQ := ⟨neg⟩
instance : Mul CQ := ⟨mul⟩
instance : Zero CQ := ⟨zero⟩
instance : One CQ := ⟨one⟩
instance : NatCast CQ := ⟨fun n => ⟨Qsqrt3.ofRat n, 0⟩⟩

@[simp] theorem add_re (x y : CQ) : (x + y).re = x.re + y.re := rfl
@[simp] theorem add_im (x y : CQ) : (x + y).im = x.im + y.im := rfl
@[simp] theorem neg_re (x : CQ) : (-x).re = -x.re := rfl
@[simp] theorem neg_im (x : CQ) : (-x).im = -x.im := rfl
@[simp] theorem mul_re (x y : CQ) : (x * y).re = x.re * y.re - x.im * y.im := rfl
@[simp] theorem mul_im (x y : CQ) : (x * y).im = x.re * y.im + x.im * y.re := rfl
@[simp] theorem zero_re : (0 : CQ).re = 0 := rfl
@[simp] theorem zero_im : (0 : CQ).im = 0 := rfl
@[simp] theorem one_re : (1 : CQ).re = 1 := rfl
@[simp] theorem one_im : (1 : CQ).im = 0 := rfl
@[simp] theorem natCast_re (n : ℕ) : ((n : CQ)).re = Qsqrt3.ofRat n := rfl
@[simp] theorem natCast_im (n : ℕ) : ((n : CQ)).im = 0 := rfl

/-- The imaginary unit `i`. -/
def I : CQ := ⟨0, 1⟩

/-- A rational, as an exact complex number. -/
def ofRat (q : ℚ) : CQ := ⟨Qsqrt3.ofRat q, 0⟩

/-- `1/√3 = √3/3`. -/
def invSqrt3 : Qsqrt3 := ⟨0, 1 / 3⟩

end CQ

/-- A `3 x 3` matrix over the exact complex numbers. -/
abbrev M3 := Matrix (Fin 3) (Fin 3) CQ

/-- The matrix product, written out so that it needs no further instances. -/
def mmul (A B : M3) : M3 := fun i j => A i 0 * B 0 j + A i 1 * B 1 j + A i 2 * B 2 j

/-- The trace. -/
def mtrace (A : M3) : CQ := A 0 0 + A 1 1 + A 2 2

/-- The commutator `[A, B] = AB - BA`. -/
def mcomm (A B : M3) : M3 := fun i j => mmul A B i j + (-(mmul B A i j))

/-- `λ_1 … λ_8`, with `λ_8` carrying `1/√3 = (0, 1/3)` and `λ_2, λ_5, λ_7` carrying `i`. -/
def gm : Fin 8 → M3
  | 0 => !![0, 1, 0; 1, 0, 0; 0, 0, 0]
  | 1 => !![0, -CQ.I, 0; CQ.I, 0, 0; 0, 0, 0]
  | 2 => !![1, 0, 0; 0, -1, 0; 0, 0, 0]
  | 3 => !![0, 0, 1; 0, 0, 0; 1, 0, 0]
  | 4 => !![0, 0, -CQ.I; 0, 0, 0; CQ.I, 0, 0]
  | 5 => !![0, 0, 0; 0, 0, 1; 0, 1, 0]
  | 6 => !![0, 0, 0; 0, 0, -CQ.I; 0, CQ.I, 0]
  | 7 => !![⟨CQ.invSqrt3, 0⟩, 0, 0; 0, ⟨CQ.invSqrt3, 0⟩, 0; 0, 0, ⟨-2 * CQ.invSqrt3, 0⟩]

/-- **The structure constants, from the trace formula**: `f_{abc} = Im(tr([λ_a, λ_b] λ_c)) / 4`. -/
def f3Q (a b c : Fin 8) : Qsqrt3 :=
  (mtrace (mmul (mcomm (gm a) (gm b)) (gm c))).im * ofRat (1 / 4)


/-! ## The table, computed -/

/-- `f_{123} = 1`. -/
theorem f3Q_123 : f3Q 0 1 2 = ofRat 1 + sqrt3 * ofRat 0 := by
  simp [f3Q, gm, mcomm, mmul, mtrace, CQ.I, Qsqrt3.ofRat,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
  ext <;> simp
  all_goals norm_num

/-- `f_{147} = 1/2`. -/
theorem f3Q_147 : f3Q 0 3 6 = ofRat (1 / 2) + sqrt3 * ofRat 0 := by
  simp [f3Q, gm, mcomm, mmul, mtrace, CQ.I, Qsqrt3.ofRat,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
  ext <;> simp
  all_goals norm_num

/-- `f_{246} = 1/2`. -/
theorem f3Q_246 : f3Q 1 3 5 = ofRat (1 / 2) + sqrt3 * ofRat 0 := by
  simp [f3Q, gm, mcomm, mmul, mtrace, CQ.I, Qsqrt3.ofRat,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
  ext <;> simp
  all_goals norm_num

/-- `f_{257} = 1/2`. -/
theorem f3Q_257 : f3Q 1 4 6 = ofRat (1 / 2) + sqrt3 * ofRat 0 := by
  simp [f3Q, gm, mcomm, mmul, mtrace, CQ.I, Qsqrt3.ofRat,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
  ext <;> simp
  all_goals norm_num

/-- `f_{345} = 1/2`. -/
theorem f3Q_345 : f3Q 2 3 4 = ofRat (1 / 2) + sqrt3 * ofRat 0 := by
  simp [f3Q, gm, mcomm, mmul, mtrace, CQ.I, Qsqrt3.ofRat,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
  ext <;> simp
  all_goals norm_num

/-- `f_{516} = 1/2`. -/
theorem f3Q_516 : f3Q 4 0 5 = ofRat (1 / 2) + sqrt3 * ofRat 0 := by
  simp [f3Q, gm, mcomm, mmul, mtrace, CQ.I, Qsqrt3.ofRat,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
  ext <;> simp
  all_goals norm_num

/-- `f_{637} = 1/2`. -/
theorem f3Q_637 : f3Q 5 2 6 = ofRat (1 / 2) + sqrt3 * ofRat 0 := by
  simp [f3Q, gm, mcomm, mmul, mtrace, CQ.I, Qsqrt3.ofRat,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
  ext <;> simp
  all_goals norm_num

/-- `f_{458} = √3/2`, the first weak constant. -/
theorem f3Q_458 : f3Q 3 4 7 = ofRat 0 + sqrt3 * ofRat (1 / 2) := by
  simp [f3Q, gm, mcomm, mmul, mtrace, CQ.I, CQ.invSqrt3, Qsqrt3.ofRat,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
  ext <;> simp
  all_goals norm_num

/-- `f_{678} = √3/2`, the second weak constant. -/
theorem f3Q_678 : f3Q 5 6 7 = ofRat 0 + sqrt3 * ofRat (1 / 2) := by
  simp [f3Q, gm, mcomm, mmul, mtrace, CQ.I, CQ.invSqrt3, Qsqrt3.ofRat,
    Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one]
  ext <;> simp
  all_goals norm_num

/-! ## The real constants consumed by `smStruct` -/

/-- The structure constants as real numbers, the exact element read back as `p + q * sqrt 3`. -/
noncomputable def smF3 (a b c : Fin 8) : ℝ := (f3Q a b c).toReal

/-- `smF3 1 2 3 = 1` in `Fin`-zero-based indices `0 1 2`. -/
theorem smF3_123 : smF3 0 1 2 = 1 := by
  rw [smF3, f3Q_123, Qsqrt3.toReal_form]
  norm_num

/-- `smF3 1 4 7 = 1/2`. -/
theorem smF3_147 : smF3 0 3 6 = 1 / 2 := by
  rw [smF3, f3Q_147, Qsqrt3.toReal_form]
  norm_num

/-- `smF3 4 5 8 = √3/2`, derived. -/
theorem smF3_458 : smF3 3 4 7 = Real.sqrt 3 / 2 := by
  rw [smF3, f3Q_458, Qsqrt3.toReal_form]
  ring

/-- `smF3 6 7 8 = √3/2`, derived. -/
theorem smF3_678 : smF3 5 6 7 = Real.sqrt 3 / 2 := by
  rw [smF3, f3Q_678, Qsqrt3.toReal_form]
  ring

end BookProof.SmSu3
