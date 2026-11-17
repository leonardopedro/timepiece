import Work.SmSu3Lie

/-!
# A ring structure on the exact complex numbers (local instance)

`Work/SmSu3Constants.lean` deliberately defines `CQ` with only the typeclasses its proofs need, so
that every goal has to be pushed down to `ℚ` by `ext` before `ring` can see it.  That is fine for the
table, but it makes the *linear algebra* of the Jacobi identity awkward: sums over the `λ` index need
an `AddCommMonoid`, and cyclicity arguments need to move factors inside a `∑`.

`CQ = Q(sqrt 3) + Q(sqrt 3) i` is a commutative ring, so this file provides the instance — copied from
the pattern `Work/Qsqrt3.lean` uses for `Qsqrt3` itself — as an **exported** instance of this
module: nothing that imports `SmSu3Constants` alone changes behaviour, because the instance only
exists from `SmSu3Ring` downwards.
-/

namespace BookProof.SmSu3

namespace CQ

/-- A subtraction, so that `CommRing` can be stated in the usual form. -/
def subOp (x y : CQ) : CQ := ⟨x.re - y.re, x.im - y.im⟩

def nsmulOp (n : ℕ) (x : CQ) : CQ := ⟨n • x.re, n • x.im⟩

def zsmulOp (n : ℤ) (x : CQ) : CQ := ⟨n • x.re, n • x.im⟩

/-- Powers by repeated multiplication: `(a + bi)^n` is not entrywise, so this cannot be `re ^ n`. -/
def npowOp (n : ℕ) (x : CQ) : CQ := Nat.rec one (fun _ ih => ih * x) n

instance : Sub CQ := ⟨subOp⟩
instance : SMul ℕ CQ := ⟨nsmulOp⟩
instance : SMul ℤ CQ := ⟨zsmulOp⟩
instance : Pow CQ ℕ := ⟨fun x n => npowOp n x⟩
instance : IntCast CQ := ⟨fun n => ⟨Qsqrt3.ofRat n, 0⟩⟩

@[simp] theorem sub_re (x y : CQ) : (x - y).re = x.re - y.re := rfl

@[simp] theorem sub_im (x y : CQ) : (x - y).im = x.im - y.im := rfl

@[simp] theorem nsmulOp_zero' (x : CQ) : nsmulOp 0 x = 0 := by
  ext <;> simp [nsmulOp]

@[simp] theorem nsmulOp_succ' (n : ℕ) (x : CQ) : nsmulOp (n + 1) x = nsmulOp n x + x := by
  ext <;> simp [nsmulOp] <;> ring

@[simp] theorem zsmulOp_zero' (x : CQ) : zsmulOp 0 x = 0 := by
  ext <;> simp [zsmulOp]

@[simp] theorem zsmulOp_succ' (n : ℕ) (x : CQ) : zsmulOp (n + 1) x = zsmulOp n x + x := by
  ext <;> simp [zsmulOp] <;> ring

@[simp] theorem zsmulOp_neg' (n : ℕ) (x : CQ) : zsmulOp (Int.negSucc n) x = -zsmulOp (n + 1) x := by
  ext <;> simp [zsmulOp] <;> ring

@[simp] theorem npowOp_zero' (x : CQ) : npowOp 0 x = 1 := rfl

@[simp] theorem npowOp_succ' (n : ℕ) (x : CQ) : npowOp (n + 1) x = npowOp n x * x := rfl

set_option maxHeartbeats 4000000 in
/-- `CQ` is a commutative ring: complex numbers over the exact field `Q(sqrt 3)`. -/
def commRing : CommRing CQ where
  add := (· + ·)
  add_assoc := by intro x y z; ext <;> simp <;> ring
  zero := 0
  zero_add := by intro x; ext <;> simp
  add_zero := by intro x; ext <;> simp
  nsmul := nsmulOp
  nsmul_zero := by intro x; ext <;> simp [nsmulOp]
  nsmul_succ := by intro n x; ext <;> simp [nsmulOp] <;> ring
  neg := (-·)
  sub := subOp
  sub_eq_add_neg := by intro x y; ext <;> simp <;> ring
  neg_add_cancel := by intro x; ext <;> simp
  zsmul := zsmulOp
  zsmul_zero' := by intro x; ext <;> simp [zsmulOp]
  zsmul_succ' := by intro n x; ext <;> simp [zsmulOp] <;> ring
  zsmul_neg' := by intro n x; ext <;> simp [zsmulOp] <;> ring
  one := 1
  natCast := fun n => ⟨Qsqrt3.ofRat n, 0⟩
  natCast_zero := by ext <;> simp
  natCast_succ := by intro n; ext <;> simp
  mul := (· * ·)
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
  intCast := fun n => ⟨Qsqrt3.ofRat n, 0⟩
  intCast_ofNat := by intro n; ext <;> simp
  intCast_negSucc := by intro n; ext <;> simp
  add_comm := by intro x y; ext <;> simp <;> ring
  mul_comm := by intro x y; ext <;> simp <;> ring

attribute [instance] commRing

end CQ

end BookProof.SmSu3
