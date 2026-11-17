import Work.SmSu3Constants

/-!
# `su(3)` trace algebra: cyclicity, total antisymmetry, and the open Jacobi statement

`Work/SmSu3Constants.lean` derives `f3Q a b c := Im(tr([λ_a, λ_b] λ_c)) / 4` and proves the table
and antisymmetry in the first pair.  This file adds the general trace algebra that the rest of the
Lie identities rest on — that the trace ignores the order of two factors, that the matrix product
is associative, and therefore that it is cyclic in three factors — and with it:

* `mtrace_comm_mul` — `tr([A,B] C) = tr(A [B,C])`, the identity that makes the trace formula
  visibly cyclic;
* `f3Q_cyclic` — `f_{abc} = f_{bca}`;
* `f3Q_swap23`, `f3Q_swap13` — the two remaining odd permutations, each a sign;
* so the derived constants are **totally antisymmetric**, from algebra rather than from `8^3` cases.

The Jacobi identity is *not* proved here; `jacobiStatement` records it as a `Prop`.  It is a
different kind of statement from antisymmetry: it needs the expansion of a matrix in the `λ` basis
(equivalently the completeness relation
`Σ_e (λ_e)_{ij} (λ_e)_{kl} = 2 δ_{il} δ_{jk} - (2/3) δ_{ij} δ_{kl}`), which antisymmetry never
touches.  See `HONEST_BOUNDARIES_SM.md` for the measured cost of the alternative (case evaluation)
and why the algebraic route needs that expansion first.
-/

namespace BookProof.SmSu3

open Qsqrt3

/-! ## Products, traces and the pointwise lemmas -/

/-- Multiplication on the right by a negation is a negation of the product. -/
theorem CQ.mul_neg' (x y : CQ) : x * (-y) = -(x * y) := by
  ext <;> simp <;> ring

/-- The trace of a product does not see the order of its two factors. -/
theorem mtrace_mul_comm (A B : M3) : mtrace (mmul A B) = mtrace (mmul B A) := by
  ext <;> simp [mtrace, mmul] <;> ring

/-- The matrix product is associative. -/
theorem mmul_assoc (A B C : M3) : mmul (mmul A B) C = mmul A (mmul B C) := by
  funext i j
  ext <;> simp [mmul] <;> ring

/-- The trace is cyclic in three factors: `tr(ABC) = tr(BCA)`. -/
theorem mtrace_cycle (A B C : M3) :
    mtrace (mmul (mmul A B) C) = mtrace (mmul (mmul B C) A) := by
  rw [mtrace_mul_comm, ← mmul_assoc, mtrace_mul_comm, ← mmul_assoc]

/-- The trace is additive over a pointwise sum. -/
theorem mtrace_pointwise_add (A B : M3) :
    mtrace (fun i j => A i j + B i j) = mtrace A + mtrace B := by
  ext <;> simp [mtrace] <;> ring

/-- The product distributes over a pointwise sum on the left. -/
theorem mmul_add_left (A B C : M3) :
    mmul (fun i j => A i j + B i j) C = fun i j => mmul A C i j + mmul B C i j := by
  funext i j
  ext <;> simp [mmul] <;> ring

/-- The product distributes over a pointwise sum on the right. -/
theorem mmul_add_right (A B C : M3) :
    mmul A (fun i j => B i j + C i j) = fun i j => mmul A B i j + mmul A C i j := by
  funext i j
  ext <;> simp [mmul] <;> ring

/-- A pointwise negation on the right is a negation of the product. -/
theorem mmul_neg_right (A B : M3) :
    mmul A (fun i j => -(B i j)) = fun i j => -(mmul A B i j) := by
  funext i j
  simp only [mmul, CQ.mul_neg']
  rw [← CQ.neg_add', ← CQ.neg_add']

/-- The trace of a pointwise difference. -/
theorem mtrace_add_neg (A B : M3) :
    mtrace (fun i j => A i j + -(B i j)) = mtrace A + -(mtrace B) := by
  rw [mtrace_pointwise_add, mtrace_neg]

/-! ## The commutator in the trace -/

/-- **`tr([A, B] C) = tr(A [B, C])`.**  Unfold the commutator into `AB - BA`, push the difference
through the product and the trace, and use cyclicity to move `BA` onto `AC`. -/
theorem mtrace_comm_mul (A B C : M3) :
    mtrace (mmul (mcomm A B) C) = mtrace (mmul A (mcomm B C)) := by
  rw [show mcomm A B = fun i j => mmul A B i j + -(mmul B A i j) from rfl,
    show mcomm B C = fun i j => mmul B C i j + -(mmul C B i j) from rfl]
  rw [mmul_add_left, mmul_neg_left, mtrace_add_neg]
  rw [mmul_add_right, mmul_neg_right, mtrace_add_neg]
  rw [mmul_assoc A B C, mtrace_cycle B A C,
    show mtrace (mmul (mmul A C) B) = mtrace (mmul A (mmul C B)) from by rw [mmul_assoc]]

/-! ## Total antisymmetry of the derived constants -/

/-- **The constants are cyclic**: `f_{abc} = f_{bca}`.  Both sides are
`Im(tr(λ_a [λ_b, λ_c])) / 4` after `mtrace_comm_mul` and one exchange of factors. -/
theorem f3Q_cyclic (a b c : Fin 8) : f3Q a b c = f3Q b c a := by
  simp only [f3Q]
  rw [mtrace_comm_mul, mtrace_mul_comm]

/-- The second pair is antisymmetric as well: from cyclicity and `f3Q_antisym`,
`f_{abc} = f_{bca} = -f_{cba} = -f_{acb}`. -/
theorem f3Q_swap23 (a b c : Fin 8) : f3Q a b c = - f3Q a c b := by
  rw [f3Q_cyclic, f3Q_antisym, (f3Q_cyclic a c b).symm]

/-- The outer pair is antisymmetric too. -/
theorem f3Q_swap13 (a b c : Fin 8) : f3Q a b c = - f3Q c b a := by
  rw [f3Q_swap23, (f3Q_cyclic a c b).symm]

/-- Total antisymmetry: every transposition of the three indices flips the sign. -/
theorem f3Q_transposition (a b c : Fin 8) :
    f3Q a b c = - f3Q b a c ∧ f3Q a b c = - f3Q a c b ∧ f3Q a b c = - f3Q c b a :=
  ⟨f3Q_antisym a b c, f3Q_swap23 a b c, f3Q_swap13 a b c⟩

/-! ## Jacobi: stated, not proved -/

/-- The Jacobi identity in structure-constant form: the cyclic sum of `Σ_e f_{abe} f_{cde}`
vanishes.  This is a `Prop` and not a theorem — see the module docstring. -/
def jacobiStatement : Prop :=
  ∀ a b c d : Fin 8,
    (∑ e : Fin 8, f3Q a b e * f3Q c d e) + (∑ e : Fin 8, f3Q b c e * f3Q a d e) +
        (∑ e : Fin 8, f3Q c a e * f3Q b d e) =
      0

end BookProof.SmSu3
