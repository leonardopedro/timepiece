import Mathlib

/-!
# An exact `Q(sqrt 3)` arithmetic layer

`scripts/sm-cubic-kernel-basis.py` computes the ghost-number-two matrix and its `55 x 55` rank
certificate in `Q(sqrt 3)`, carrying `a + b * sqrt 3` as a pair of `fractions.Fraction`s.  This file
is
the Lean counterpart: the same pair representation, as a `CommRing` so that Mathlib's `Matrix.det`
applies, with `toReal` for reading a value back as a real number, the conjugation `sqrt 3 -> -sqrt
3`,
and the norm-formula inverse.

The multiplication rule `(a + b√3)(c + d√3) = (ac + 3bd) + (ad + bc)√3` is the only place `√3² = 3`
enters, and every ring axiom is "unfold both coordinates and `ring`".  The `_re`/`_im` lemmas exist
in
two forms: about the named operation (used while the `CommRing` instance is being built) and about
the
notation (used afterwards).

There is no `Field` instance: `inv'` is the norm formula, but `x * x⁻¹ = 1` is an obligation, stated
as
`mul_inv'_cancel` rather than assumed.  Nothing here is used by the build.
-/

structure Qsqrt3 where
  re : ℚ
  im : ℚ
  deriving DecidableEq, Repr

namespace Qsqrt3
@[ext] theorem ext' {x y : Qsqrt3} (h1 : x.re = y.re) (h2 : x.im = y.im) : x = y := by
  cases x; cases y; simp_all
def addOp (x y : Qsqrt3) : Qsqrt3 := ⟨x.re + y.re, x.im + y.im⟩
def mulOp (x y : Qsqrt3) : Qsqrt3 := ⟨x.re * y.re + 3 * (x.im * y.im), x.re * y.im + x.im * y.re⟩
def zeroOp : Qsqrt3 := ⟨0, 0⟩
def oneOp : Qsqrt3 := ⟨1, 0⟩
def negOp (x : Qsqrt3) : Qsqrt3 := ⟨-x.re, -x.im⟩
def subOp (x y : Qsqrt3) : Qsqrt3 := ⟨x.re - y.re, x.im - y.im⟩
def nsmulOp (n : ℕ) (x : Qsqrt3) : Qsqrt3 := ⟨n • x.re, n • x.im⟩
def zsmulOp (n : ℤ) (x : Qsqrt3) : Qsqrt3 := ⟨n • x.re, n • x.im⟩
def npowOp (n : ℕ) (x : Qsqrt3) : Qsqrt3 := Nat.rec oneOp (fun _ ih => mulOp ih x) n
instance : Add Qsqrt3 := ⟨addOp⟩
instance : Mul Qsqrt3 := ⟨mulOp⟩
instance : Zero Qsqrt3 := ⟨zeroOp⟩
instance : One Qsqrt3 := ⟨oneOp⟩
instance : Neg Qsqrt3 := ⟨negOp⟩
instance : Sub Qsqrt3 := ⟨subOp⟩
instance : SMul ℕ Qsqrt3 := ⟨nsmulOp⟩
instance : SMul ℤ Qsqrt3 := ⟨zsmulOp⟩
instance : Pow Qsqrt3 ℕ := ⟨fun x n => npowOp n x⟩
instance : NatCast Qsqrt3 := ⟨fun n => ⟨n, 0⟩⟩
instance : IntCast Qsqrt3 := ⟨fun n => ⟨n, 0⟩⟩
@[simp] theorem add_re (x y : Qsqrt3) : (x + y).re = x.re + y.re := rfl
@[simp] theorem add_im (x y : Qsqrt3) : (x + y).im = x.im + y.im := rfl
@[simp] theorem mul_re (x y : Qsqrt3) : (x * y).re = x.re * y.re + 3 * (x.im * y.im) := rfl
@[simp] theorem mul_im (x y : Qsqrt3) : (x * y).im = x.re * y.im + x.im * y.re := rfl
@[simp] theorem zero_re : (0 : Qsqrt3).re = 0 := rfl
@[simp] theorem zero_im : (0 : Qsqrt3).im = 0 := rfl
@[simp] theorem one_re : (1 : Qsqrt3).re = 1 := rfl
@[simp] theorem one_im : (1 : Qsqrt3).im = 0 := rfl
@[simp] theorem neg_re (x : Qsqrt3) : (-x).re = -x.re := rfl
@[simp] theorem neg_im (x : Qsqrt3) : (-x).im = -x.im := rfl
@[simp] theorem sub_re (x y : Qsqrt3) : (x - y).re = x.re - y.re := rfl
@[simp] theorem sub_im (x y : Qsqrt3) : (x - y).im = x.im - y.im := rfl
@[simp] theorem nsmul_re (n : ℕ) (x : Qsqrt3) : (nsmulOp n x).re = n • x.re := rfl
@[simp] theorem nsmul_im (n : ℕ) (x : Qsqrt3) : (nsmulOp n x).im = n • x.im := rfl
@[simp] theorem zsmul_re (n : ℤ) (x : Qsqrt3) : (zsmulOp n x).re = n • x.re := rfl
@[simp] theorem zsmul_im (n : ℤ) (x : Qsqrt3) : (zsmulOp n x).im = n • x.im := rfl
@[simp] theorem natCast_re (n : ℕ) : ((n : Qsqrt3)).re = n := rfl
@[simp] theorem natCast_im (n : ℕ) : ((n : Qsqrt3)).im = 0 := rfl
@[simp] theorem negOp_re' (x : Qsqrt3) : (negOp x).re = -x.re := rfl
@[simp] theorem negOp_im' (x : Qsqrt3) : (negOp x).im = -x.im := rfl
@[simp] theorem subOp_re' (x y : Qsqrt3) : (subOp x y).re = x.re - y.re := rfl
@[simp] theorem subOp_im' (x y : Qsqrt3) : (subOp x y).im = x.im - y.im := rfl
@[simp] theorem zsmulOp_re' (n : ℤ) (x : Qsqrt3) : (zsmulOp n x).re = n • x.re := rfl
@[simp] theorem zsmulOp_im' (n : ℤ) (x : Qsqrt3) : (zsmulOp n x).im = n • x.im := rfl
@[simp] theorem nsmulOp_re' (n : ℕ) (x : Qsqrt3) : (nsmulOp n x).re = n • x.re := rfl
@[simp] theorem nsmulOp_im' (n : ℕ) (x : Qsqrt3) : (nsmulOp n x).im = n • x.im := rfl
@[simp] theorem npowOp_zero' (x : Qsqrt3) : (npowOp 0 x) = 1 := rfl
@[simp] theorem npowOp_succ' (n : ℕ) (x : Qsqrt3) : (npowOp (n + 1) x) = npowOp n x * x := rfl
instance : CommRing Qsqrt3 where
  add := addOp
  add_assoc := by intro x y z; ext <;> simp <;> ring
  zero := zeroOp
  zero_add := by intro x; ext <;> simp
  add_zero := by intro x; ext <;> simp
  nsmul := nsmulOp
  nsmul_zero := by intro x; ext <;> simp
  nsmul_succ := by intro n x; ext <;> simp <;> ring
  neg := negOp
  sub := subOp
  sub_eq_add_neg := by intro x y; ext <;> simp <;> ring
  neg_add_cancel := by intro x; ext <;> simp
  zsmul := zsmulOp
  zsmul_zero' := by intro x; ext <;> simp
  zsmul_succ' := by intro n x; ext <;> simp <;> ring
  zsmul_neg' := by intro n x; ext <;> simp <;> ring
  one := oneOp
  natCast := fun n => ⟨n, 0⟩
  natCast_zero := by ext <;> simp
  natCast_succ := by intro n; ext <;> simp
  mul := mulOp
  left_distrib := by intro x y z; ext <;> simp <;> ring
  right_distrib := by intro x y z; ext <;> simp <;> ring
  zero_mul := by intro x; ext <;> simp
  mul_zero := by intro x; ext <;> simp
  mul_assoc := by intro x y z; ext <;> simp <;> ring
  one_mul := by intro x; ext <;> simp
  mul_one := by intro x; ext <;> simp
  npow := npowOp
  npow_zero := by intro x; rfl
  npow_succ := by intro n x; rfl
  intCast := fun n => ⟨n, 0⟩
  intCast_ofNat := by intro n; ext <;> simp
  intCast_negSucc := by intro n; ext <;> simp
  add_comm := by intro x y; ext <;> exact add_comm _ _
  mul_comm := by intro x y; ext <;> simp <;> ring

/-- Cast lemmas in the post-`CommRing` notation, which the pre-instance ones cannot match. -/
@[simp] theorem natCast_re' (n : ℕ) : ((n : Qsqrt3)).re = n := rfl
@[simp] theorem natCast_im' (n : ℕ) : ((n : Qsqrt3)).im = 0 := rfl
@[simp] theorem intCast_re' (n : ℤ) : ((n : Qsqrt3)).re = n := rfl
@[simp] theorem intCast_im' (n : ℤ) : ((n : Qsqrt3)).im = 0 := rfl

/-! ## `sqrt 3`, the real value, conjugation and the inverse -/

/-- A rational embedded as `q + 0 * sqrt 3`. -/
def ofRat (q : ℚ) : Qsqrt3 := ⟨q, 0⟩

@[simp] theorem ofRat_re (q : ℚ) : (ofRat q).re = q := rfl
@[simp] theorem ofRat_im (q : ℚ) : (ofRat q).im = 0 := rfl

theorem ofRat_add (p q : ℚ) : ofRat p + ofRat q = ofRat (p + q) := by
  ext <;> simp [ofRat]

theorem ofRat_mul (p q : ℚ) : ofRat p * ofRat q = ofRat (p * q) := by
  ext <;> simp [ofRat]

theorem ofRat_neg (p : ℚ) : -ofRat p = ofRat (-p) := by
  ext <;> simp [ofRat]

/-- The canonical element `sqrt 3 = 0 + 1 * sqrt 3`. -/
def sqrt3 : Qsqrt3 := ⟨0, 1⟩

@[simp] theorem sqrt3_re : sqrt3.re = 0 := rfl
@[simp] theorem sqrt3_im : sqrt3.im = 1 := rfl

/-- `sqrt 3` really squares to `3`: this is the entire content of the multiplication rule. -/
theorem sqrt3_sq : sqrt3 * sqrt3 = ofRat 3 := by
  ext <;> simp only [mul_re, mul_im, sqrt3_re, sqrt3_im, ofRat_re, ofRat_im] <;> norm_num

/-- The real value of an exact element: `a + b * sqrt 3`, computed in `ℝ`. -/
noncomputable def toReal (x : Qsqrt3) : ℝ := x.re + x.im * Real.sqrt 3

theorem toReal_ofRat (q : ℚ) : (ofRat q).toReal = q := by
  simp [toReal, ofRat]

theorem toReal_add (x y : Qsqrt3) : (x + y).toReal = x.toReal + y.toReal := by
  simp only [toReal, add_re, add_im]
  push_cast
  ring

theorem toReal_mul (x y : Qsqrt3) : (x * y).toReal = x.toReal * y.toReal := by
  have h : Real.sqrt 3 ^ 2 = (3 : ℝ) := by
    rw [sq, Real.mul_self_sqrt (by norm_num)]
  simp only [toReal, mul_re, mul_im]
  push_cast
  ring_nf
  rw [h]

theorem toReal_sqrt3 : (sqrt3 : Qsqrt3).toReal = Real.sqrt 3 := by
  simp [toReal, sqrt3]

/-- `sqrt 3 / 2`, the weak constant `f_458 = f_678` of `su(3)`, as an exact element. -/
def sqrt3DivTwo : Qsqrt3 := sqrt3 * ofRat (1 / 2)

theorem toReal_sqrt3DivTwo : (sqrt3DivTwo : Qsqrt3).toReal = Real.sqrt 3 / 2 := by
  rw [sqrt3DivTwo, toReal_mul, toReal_sqrt3, toReal_ofRat]
  ring

/-- The real value of `p + q * sqrt 3`, in the shape the derived constants are stated in. -/
theorem toReal_form (p q : ℚ) : (ofRat p + sqrt3 * ofRat q).toReal = p + q * Real.sqrt 3 := by
  rw [toReal_add, toReal_mul, toReal_ofRat, toReal_ofRat, toReal_sqrt3]
  ring

/-- Conjugation `sqrt 3 ↦ -sqrt 3`, which the norm formula uses. -/
def conj (x : Qsqrt3) : Qsqrt3 := ⟨x.re, -x.im⟩

@[simp] theorem conj_re (x : Qsqrt3) : (conj x).re = x.re := rfl
@[simp] theorem conj_im (x : Qsqrt3) : (conj x).im = -x.im := rfl

theorem mul_conj_re (x : Qsqrt3) : (x * conj x).re = x.re ^ 2 - 3 * x.im ^ 2 := by
  simp only [mul_re, conj_re, conj_im]
  ring

theorem mul_conj_im (x : Qsqrt3) : (x * conj x).im = 0 := by
  simp only [mul_im, conj_re, conj_im]
  ring

/-- The inverse, by the norm formula. -/
def inv' (x : Qsqrt3) : Qsqrt3 :=
  ⟨x.re / (x.re ^ 2 - 3 * x.im ^ 2), -x.im / (x.re ^ 2 - 3 * x.im ^ 2)⟩

/-- The inverse is a right inverse away from the zero norm: an obligation, not an assumption. -/
theorem mul_inv'_cancel (x : Qsqrt3) (h : x.re ^ 2 - 3 * x.im ^ 2 ≠ 0) :
    x * inv' x = 1 := by
  ext <;> simp only [mul_re, mul_im, inv', one_re, one_im] <;> field_simp <;> ring

/-! ## A determinant over the field -/

/-- `Matrix.det` over `Q(sqrt 3)`: the exact determinant the rank certificate needs. -/
noncomputable def detQ {n : Type} [Fintype n] [DecidableEq n]
    (M : Matrix n n Qsqrt3) : Qsqrt3 := Matrix.det M

/-- The layer is computable and the determinant computes: `det [[0, √3], [√3, 0]] = -3`. -/
theorem det_sqrt3_block :
    detQ (Matrix.of ![![(0 : Qsqrt3), sqrt3], ![sqrt3, (0 : Qsqrt3)]]) = ofRat (-3) := by
  simp only [detQ, Matrix.det_fin_two_of, sqrt3_sq]
  ext <;> simp [ofRat]

/-- The `2 x 2` multiplication matrix of `a + b√3` has determinant the norm `a^2 - 3b^2`. -/
theorem det_mulMat (x : Qsqrt3) :
    detQ (Matrix.of ![![ofRat x.re, ofRat (3 * x.im)], ![ofRat x.im, ofRat x.re]])
      = ofRat (x.re ^ 2 - 3 * x.im ^ 2) := by
  simp only [detQ, Matrix.det_fin_two_of, ofRat_mul]
  ext <;> simp [ofRat]
  ring

/-- The rank certificate, stated in exact arithmetic: a `55 x 55` minor is nonsingular.  The
script's
minor has determinant `-3^12 / 2^35`; supplying its literal matrix is the open obligation. -/
noncomputable def certificateStatement (M : Matrix (Fin 55) (Fin 55) Qsqrt3) : Prop :=
  detQ M ≠ 0

/-! ## Numeral projections

`simp` cannot see through the `OfNat` instance on `Q(sqrt 3)`, so the numerals that appear in the
Gell-Mann computation get their own `rfl` lemmas.  Each is definitional.
-/

@[simp] theorem re_ofNat_0 : ((0 : Qsqrt3)).re = 0 := rfl
@[simp] theorem im_ofNat_0 : ((0 : Qsqrt3)).im = 0 := rfl
@[simp] theorem re_ofNat_1 : ((1 : Qsqrt3)).re = 1 := rfl
@[simp] theorem im_ofNat_1 : ((1 : Qsqrt3)).im = 0 := rfl
@[simp] theorem re_ofNat_2 : ((2 : Qsqrt3)).re = 2 := rfl
@[simp] theorem im_ofNat_2 : ((2 : Qsqrt3)).im = 0 := rfl
@[simp] theorem re_ofNat_3 : ((3 : Qsqrt3)).re = 3 := rfl
@[simp] theorem im_ofNat_3 : ((3 : Qsqrt3)).im = 0 := rfl
@[simp] theorem re_ofNat_4 : ((4 : Qsqrt3)).re = 4 := rfl
@[simp] theorem im_ofNat_4 : ((4 : Qsqrt3)).im = 0 := rfl
@[simp] theorem re_ofNat_5 : ((5 : Qsqrt3)).re = 5 := rfl
@[simp] theorem im_ofNat_5 : ((5 : Qsqrt3)).im = 0 := rfl
@[simp] theorem re_ofNat_6 : ((6 : Qsqrt3)).re = 6 := rfl
@[simp] theorem im_ofNat_6 : ((6 : Qsqrt3)).im = 0 := rfl
@[simp] theorem re_ofNat_7 : ((7 : Qsqrt3)).re = 7 := rfl
@[simp] theorem im_ofNat_7 : ((7 : Qsqrt3)).im = 0 := rfl
@[simp] theorem re_ofNat_8 : ((8 : Qsqrt3)).re = 8 := rfl
@[simp] theorem im_ofNat_8 : ((8 : Qsqrt3)).im = 0 := rfl
@[simp] theorem re_ofNat_9 : ((9 : Qsqrt3)).re = 9 := rfl
@[simp] theorem im_ofNat_9 : ((9 : Qsqrt3)).im = 0 := rfl

end Qsqrt3
