import Work.SmSu3Ring

/-!
# The Jacobi identity for the derived `su(3)` constants

This file proves `jacobiStatement` from `Work/SmSu3Lie.lean`.  The route is the algebraic one, and the
one thing that makes it work is a `CommRing` structure on `CQ` (`Work/SmSu3Ring.lean`): with it, sums
over the `λ` index and `ring`-normal `3 x 3` matrix algebra become available, and the whole identity is
a *symbolic* statement rather than 4096 numerical cases.

The steps:

1. `parsevalInteger` — the completeness (Parseval) relation for the Gell-Mann basis, in the
   integer-coefficient form `3 Σ_{e<8} tr(M λ_e) tr(N λ_e) + 2 tr M tr N = 6 tr(MN)`, where `λ_8` has
   been rescaled by `sqrt 3` so that no `1/sqrt 3` ever appears.  This is a single polynomial identity
   in the 18 entries of `M` and `N`.
2. `tracePair_three` — the same with the original `λ_8`, which costs one factor of `3`.
3. `purity` — for `M` a commutator of two generators, `tr(M λ_e)` is purely imaginary, so
   `tr(M λ_e) tr(N λ_e)` is the negative of the product of the imaginary parts.
4. `tracePair_traceless` — for traceless `M`, `N` the `2/3` term is gone, and the pairing is
   `2 tr(MN)`.
5. `jacobi_mcomm` — the matrix Jacobi identity, and cyclicity of the trace, give
   `Σ_cyc tr([λ_a,λ_b][λ_c,λ_d]) = 0`.
6. `jacobiStatement` — assembling, since `16 f_{abe} f_{cde}` is the negative of the trace pairing.
-/

namespace BookProof.SmSu3

open Qsqrt3

/-! ## Powers and the imaginary unit -/

@[simp] theorem CQ.pow_two' (x : CQ) : x ^ 2 = x * x := by
  change CQ.npowOp 2 x = x * x
  rw [show (2 : ℕ) = 1 + 1 from rfl, CQ.npowOp_succ', CQ.npowOp_succ', CQ.npowOp_zero', one_mul]

@[simp] theorem CQ.I_mul_self : CQ.I * CQ.I = -1 := by
  ext <;> simp [CQ.I] <;> ring

@[simp] theorem CQ.I_sq : CQ.I ^ 2 = -1 := by
  rw [CQ.pow_two', CQ.I_mul_self]

@[simp] theorem CQ.ofRat_re (q : ℚ) : (CQ.ofRat q).re = Qsqrt3.ofRat q := rfl

@[simp] theorem CQ.ofRat_im (q : ℚ) : (CQ.ofRat q).im = 0 := rfl

/-- The cast lemmas in the post-`CommRing` notation: numerals now resolve through the instance's own
`NatCast`, so the pre-instance `natCast_re` no longer matches.  (Same phenomenon, and same fix, as in
`Work/Qsqrt3.lean`.) -/
@[simp] theorem CQ.num_re (n : ℕ) : ((n : CQ)).re = Qsqrt3.ofRat n := by
  have h : (n : CQ) = CQ.ofRat n := rfl
  rw [h]
  rfl

@[simp] theorem CQ.num_im (n : ℕ) : ((n : CQ)).im = 0 := by
  have h : (n : CQ) = CQ.ofRat n := rfl
  rw [h]
  rfl

/-! ## The rescaled eighth generator

`λ_8 = diag(1,1,-2)/sqrt 3`, so `sqrt 3 * λ_8 = diag(1,1,-2)` has integer entries.  Working in that
basis removes every `1/sqrt 3` from the completeness relation; the cost is a factor of `3`, recovered
in `tracePair_three`. -/

/-- The generators with `λ_8` multiplied by `sqrt 3`, so that every entry is an integer. -/
def gmZ : Fin 8 → M3
  | 7 => !![1, 0, 0; 0, 1, 0; 0, 0, -2]
  | e => gm e

/-- `sqrt 3` as an exact complex number. -/
def sqrt3C : CQ := ⟨⟨0, 1⟩, 0⟩

/-- The seven-term sum over the `λ` index. -/
def sum7 (u : Fin 8 → CQ) : CQ := u 0 + u 1 + u 2 + u 3 + u 4 + u 5 + u 6

theorem sqrt3C_sq : sqrt3C * sqrt3C = 3 := by
  have h : (3 : CQ) = ⟨Qsqrt3.ofRat 3, 0⟩ := rfl
  rw [h]
  ext <;> simp [sqrt3C] <;> norm_num

theorem sqrt3C_pow : sqrt3C ^ 2 = 3 := by
  rw [CQ.pow_two', sqrt3C_sq]

/-- `sqrt 3 * (1/sqrt 3) = 1`, the entry of the rescaled generator. -/
theorem sqrt3C_mul_inv : sqrt3C * (⟨CQ.invSqrt3, 0⟩ : CQ) = 1 := by
  ext <;> simp [sqrt3C, CQ.invSqrt3] <;> ring

/-- The rescaled generator is `sqrt 3` times the original one, entry by entry. -/
theorem gmZ_seven (i j : Fin 3) : gmZ 7 i j = sqrt3C * gm 7 i j := by
  have h2 : (2 : CQ) = ⟨Qsqrt3.ofRat 2, 0⟩ := rfl
  fin_cases i <;> fin_cases j <;>
    (ext <;> simp [gmZ, gm, sqrt3C, CQ.invSqrt3, h2] <;> norm_num <;> ring)

/-- The product is linear in the second factor. -/
theorem mmul_smul_right (M A : M3) (c : CQ) :
    mmul M (fun i j => c * A i j) = fun i j => c * mmul M A i j := by
  funext i j
  simp only [mmul]
  ring

/-- The eighth generator in the rescaled basis is `sqrt 3` times the original one. -/
theorem trace_seven (M : M3) :
    mtrace (mmul M (gmZ 7)) = sqrt3C * mtrace (mmul M (gm 7)) := by
  have h : gmZ 7 = fun i j => sqrt3C * gm 7 i j := by
    funext i j
    exact gmZ_seven i j
  rw [h, mmul_smul_right]
  simp only [mtrace]
  rw [← mul_add, ← mul_add]

/-! ## The completeness relation -/

set_option maxHeartbeats 4000000 in
/-- **Completeness, with integer coefficients.**  The `λ_8` in `gm Z` is `sqrt 3 λ_8`, so the usual
`2 δ_il δ_jk - (2/3) δ_ij δ_kl` becomes this integer identity after multiplying by three. -/
theorem parsevalInteger (M N : M3) :
    3 * sum7 (fun e => mtrace (mmul M (gm e)) * mtrace (mmul N (gm e))) +
        mtrace (mmul M (gmZ 7)) * mtrace (mmul N (gmZ 7)) + 2 * (mtrace M * mtrace N) =
      6 * mtrace (mmul M N) := by
  simp [sum7, gm, gmZ, mtrace, mmul]
  ring_nf
  simp [CQ.I_sq]
  ring

/-! ## The pairing in the original basis -/

/-- `Σ_e tr(M λ_e) tr(N λ_e)` in the original Gell-Mann basis. -/
def tracePair (M N : M3) : CQ :=
  sum7 (fun e => mtrace (mmul M (gm e)) * mtrace (mmul N (gm e))) +
    mtrace (mmul M (gm 7)) * mtrace (mmul N (gm 7))

/-- The `λ_8` term is three times the rescaled one. -/
theorem three_mul_seven (M N : M3) :
    3 * (mtrace (mmul M (gm 7)) * mtrace (mmul N (gm 7))) =
      mtrace (mmul M (gmZ 7)) * mtrace (mmul N (gmZ 7)) := by
  rw [trace_seven M, trace_seven N]
  ring_nf
  rw [sqrt3C_pow]

/-- **The pairing, with the original `λ_8`:** `3 Σ_e tr(M λ_e) tr(N λ_e) + 2 tr M tr N = 6 tr(MN)`. -/
theorem tracePair_three (M N : M3) :
    3 * tracePair M N + 2 * (mtrace M * mtrace N) = 6 * mtrace (mmul M N) := by
  have h := parsevalInteger M N
  rw [← three_mul_seven M N] at h
  simp only [tracePair]
  linear_combination h

/-! ## Purity: the trace of a commutator against a generator is purely imaginary -/

/-- The eight-term sum over the `λ` index, valued in `Q(sqrt 3)`. -/
def oct (u : Fin 8 → Qsqrt3) : Qsqrt3 :=
  u 0 + u 1 + u 2 + u 3 + u 4 + u 5 + u 6 + u 7

set_option maxHeartbeats 4000000 in
/-- **Purity.**  `Tr([λ_a, λ_b] λ_e)` is `i` times a real number: its `re` component vanishes.  This is
the anti-Hermiticity of the commutator against Hermiticity of the generators, and it is the only place
where the generators are evaluated (`8^3 = 512` closed computations). -/
theorem purity (a b e : Fin 8) :
    (mtrace (mmul (mcomm (gm a) (gm b)) (gm e))).re = 0 := by
  fin_cases a <;> fin_cases b <;> fin_cases e <;>
    (simp [mtrace, mmul, mcomm, gm, CQ.I] <;> norm_num <;> ring)

/-- A purely imaginary complex number is determined by its imaginary part. -/
theorem eq_hat_of_re_zero {T : CQ} (h : T.re = 0) : T = ⟨0, T.im⟩ := by
  cases T with
  | mk re im => simp_all

/-- Cancellation of `3` in `Q(sqrt 3)`: it is a field of characteristic zero, checked in coordinates. -/
theorem Qsqrt3.three_cancel {x y : Qsqrt3} (h : (3 : Qsqrt3) * x = 3 * y) : x = y := by
  ext
  · have hre := congrArg Qsqrt3.re h
    simp only [Qsqrt3.mul_re] at hre
    norm_num at hre
    nlinarith
  · have him := congrArg Qsqrt3.im h
    simp only [Qsqrt3.mul_im] at him
    norm_num at him
    nlinarith

/-- The same cancellation in `CQ`. -/
theorem CQ.three_cancel {x y : CQ} (h : 3 * x = 3 * y) : x = y := by
  have hre := congrArg CQ.re h
  have him := congrArg CQ.im h
  simp only [CQ.mul_re, CQ.mul_im] at hre him
  rw [show (3 : CQ) = (⟨Qsqrt3.ofRat 3, 0⟩ : CQ) from rfl] at hre him
  simp only [CQ.re, CQ.im] at hre him
  exact CQ.ext' (Qsqrt3.three_cancel (by simpa using hre))
    (Qsqrt3.three_cancel (by simpa using him))

/-! ## The termwise conversion to the structure constants -/

/-- `16 f_{abe} f_{cde}` is `-Tr([λ_a,λ_b] λ_e) Tr([λ_c,λ_d] λ_e)` in its real part, when both traces
are purely imaginary. -/
theorem term_eq (T U : CQ) (hT : T = ⟨0, T.im⟩) (hU : U = ⟨0, U.im⟩) :
    16 * ((T.im * Qsqrt3.ofRat (1 / 4)) * (U.im * Qsqrt3.ofRat (1 / 4))) = -(T * U).re := by
  rw [hT, hU]
  simp only [CQ.mul_re, CQ.mul_im, CQ.zero_re, CQ.zero_im]
  rw [show (16 : Qsqrt3) = Qsqrt3.ofRat 16 from rfl]
  ext <;> simp [Qsqrt3.ofRat] <;> ring

/-- **The sum form.**  `16 Σ_e f_{abe} f_{cde}` is minus the real part of the trace pairing of the two
commutators. -/
theorem fsum_sixteen (a b c d : Fin 8) :
    16 * oct (fun e => f3Q a b e * f3Q c d e) =
      -(tracePair (mcomm (gm a) (gm b)) (mcomm (gm c) (gm d))).re := by
  have h : ∀ e : Fin 8, 16 * (f3Q a b e * f3Q c d e) =
      -(mtrace (mmul (mcomm (gm a) (gm b)) (gm e)) *
        mtrace (mmul (mcomm (gm c) (gm d)) (gm e))).re := by
    intro e
    exact term_eq _ _ (eq_hat_of_re_zero (purity a b e)) (eq_hat_of_re_zero (purity c d e))
  simp only [oct, tracePair, sum7, CQ.add_re]
  rw [mul_add, mul_add, mul_add, mul_add, mul_add, mul_add, mul_add]
  rw [h 0, h 1, h 2, h 3, h 4, h 5, h 6, h 7]
  ring

/-! ## The traceless form of the pairing -/

/-- A commutator is traceless. -/
theorem mtrace_mcomm (A B : M3) : mtrace (mcomm A B) = 0 := by
  rw [show mcomm A B = fun i j => mmul A B i j + -(mmul B A i j) from rfl]
  rw [mtrace_add_neg, mtrace_mul_comm]
  exact add_neg_cancel _

/-- **The pairing of two traceless matrices is twice their product trace.**  The `2/3` term of the
completeness relation is `2 tr M tr N / 3`, so it is gone; what remains is the cancellation of `3`. -/
theorem tracePair_traceless (M N : M3) (hM : mtrace M = 0) (hN : mtrace N = 0) :
    tracePair M N = 2 * mtrace (mmul M N) := by
  have h := tracePair_three M N
  rw [hM, hN, mul_zero, mul_zero, add_zero] at h
  -- `3 * tracePair = 6 * tr(MN)`, so `tracePair = 2 * tr(MN)`
  have h' : 3 * tracePair M N = 3 * (2 * mtrace (mmul M N)) := by
    rw [h]
    ring
  exact CQ.three_cancel h'

/-! ## The matrix Jacobi identity and cyclicity of the trace -/

set_option maxHeartbeats 4000000 in
/-- `[[A,B],C] + [[B,C],A] + [[C,A],B] = 0`, entry by entry.  This is associativity and distributivity
of `CQ` alone: the four terms `ABC, BCA, CAB` and their negatives cancel pairwise. -/
theorem jacobi_mcomm (A B C : M3) (i j : Fin 3) :
    mcomm (mcomm A B) C i j + mcomm (mcomm B C) A i j + mcomm (mcomm C A) B i j = 0 := by
  simp only [mcomm, mmul]
  ring

/-- Traces of products with a common right factor add. -/
theorem mtrace_mmul_add (X Y W : M3) :
    mtrace (mmul (fun i j => X i j + Y i j) W) = mtrace (mmul X W) + mtrace (mmul Y W) := by
  rw [mmul_add_left, mtrace_pointwise_add]

/-- **The cyclic sum of the pairings vanishes**: `Σ_cyc tr([λ_a,λ_b][λ_c,λ_d]) = 0`.  Each term is
`tr([[λ_a,λ_b],λ_c] λ_d)` by `mtrace_comm_mul`, so the sum is `tr(0 * λ_d)`. -/
theorem trace_bracket_sum (A B C W : M3) :
    mtrace (mmul (mcomm (mcomm A B) C) W) + mtrace (mmul (mcomm (mcomm B C) A) W) +
        mtrace (mmul (mcomm (mcomm C A) B) W) =
      0 := by
  rw [← mtrace_mmul_add, ← mtrace_mmul_add]
  have hzero : (fun i j => mcomm (mcomm A B) C i j + mcomm (mcomm B C) A i j +
      mcomm (mcomm C A) B i j) = fun _ _ => (0 : CQ) := by
    funext i j
    exact jacobi_mcomm A B C i j
  rw [hzero]
  simp [mmul, mtrace]

/-! ## The Jacobi identity for the derived constants -/

/-- The unfolded eight-term sum is the `Finset` sum over `Fin 8`. -/
theorem oct_eq_sum (u : Fin 8 → Qsqrt3) : oct u = ∑ e : Fin 8, u e := by
  simp [oct, Fin.sum_univ_eight]

/-- Cancellation of `16` in `Q(sqrt 3)`. -/
theorem Qsqrt3.sixteen_cancel {x y : Qsqrt3} (h : (16 : Qsqrt3) * x = 16 * y) : x = y := by
  have h16 : (16 : Qsqrt3) = Qsqrt3.ofRat 16 := rfl
  rw [h16] at h
  ext
  · have hre := congrArg Qsqrt3.re h
    simp only [Qsqrt3.mul_re] at hre
    norm_num at hre
    nlinarith
  · have him := congrArg Qsqrt3.im h
    simp only [Qsqrt3.mul_im] at him
    norm_num at him
    nlinarith

/-- **The Jacobi identity**, in structure-constant form.  Assembling:

* `fsum_sixteen` writes `16 Σ_e f_{abe} f_{cde}` as minus the real part of
  `tr([λ_a,λ_b] [λ_c,λ_d])`;
* `tracePair_traceless` evaluates the pairing as `2 tr(MN)` for the traceless commutators;
* `trace_bracket_sum` kills the cyclic sum of those pairings.

So `16 ×` the Jacobi sum is zero, and `16` cancels. -/
set_option maxHeartbeats 8000000 in
theorem jacobi_holds : jacobiStatement := by
  intro a b c d
  show (∑ e : Fin 8, f3Q a b e * f3Q c d e) + (∑ e : Fin 8, f3Q b c e * f3Q a d e) +
      (∑ e : Fin 8, f3Q c a e * f3Q b d e) = 0
  rw [← oct_eq_sum, ← oct_eq_sum, ← oct_eq_sum]
  -- the three trace pairings
  have hcyc := trace_bracket_sum (gm a) (gm b) (gm c) (gm d)
  have hcycR :
      (mtrace (mmul (mcomm (gm a) (gm b)) (mcomm (gm c) (gm d)))).re +
          (mtrace (mmul (mcomm (gm b) (gm c)) (mcomm (gm a) (gm d)))).re +
        (mtrace (mmul (mcomm (gm c) (gm a)) (mcomm (gm b) (gm d)))).re =
      0 := by
    have := congrArg CQ.re hcyc
    simpa [CQ.add_re, CQ.zero_re] using this
  have h16 :
      16 * (oct (fun e => f3Q a b e * f3Q c d e) + oct (fun e => f3Q b c e * f3Q a d e) +
          oct (fun e => f3Q c a e * f3Q b d e)) =
        0 := by
    rw [mul_add, mul_add, fsum_sixteen a b c d, fsum_sixteen b c a d, fsum_sixteen c a b d]
    linear_combination -hcycR
  exact Qsqrt3.sixteen_cancel (by rw [h16])

end BookProof.SmSu3
