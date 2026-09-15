import Mathlib

/-!
# The canonical commutation relations need unbounded operators

Source: `book.tex`, chapter *"Timepiece and the Gribov ambiguity"*, §*"Quantization due to
time-evolution"*, subsection *"Gauge symmetry: definition within Quantum Field Theory"*
(`book.tex` line ~7155):

> *"When the Lagrangian is singular, in the classical Hamiltonian formalism there are
> conjugate momenta constrained to be null while the corresponding field has a definite
> value.  This is incompatible with the canonical commutation relations of the
> corresponding quantum fields."*

and the remark repeated elsewhere in the project that a CCR pair *"has no
finite-dimensional representation (the trace of a commutator vanishes while the trace of a
nonzero scalar does not)"*.

This file proves the three no-go statements behind those sentences.

* `ccr_fails_of_momentum_zero` — the book's literal claim: a **null momentum** cannot
  satisfy the canonical commutation relation, so the constraint `p = 0` of a singular
  Lagrangian is incompatible with the CCR.
* `matrix_no_ccr` — the **finite-dimensional** no-go, by the trace argument: no square
  matrices of positive size satisfy `q p − p q = c · 1` with `c ≠ 0`.
* `no_ccr_one`, `no_ccr_smul` — the **Wielandt–Wintner** theorem: in *any* nontrivial
  normed real algebra — in particular for bounded operators on a Banach space — there are
  no elements with `x y − y x = c · 1`, `c ≠ 0`.  The commutation relation therefore forces
  *unbounded* operators, which is the analytic reason why the essential-self-adjointness
  machinery of the rest of this project is needed at all.

The proof of the last statement is the classical one: `xⁿ⁺¹ y − y xⁿ⁺¹ = (n+1)·xⁿ`
(`ccr_pow`), so no power of `x` can vanish (`ccr_pow_ne_zero`), and then
`(n+1)‖xⁿ‖ ≤ 2‖x‖‖y‖‖xⁿ‖` bounds every natural number by the fixed real `2‖x‖‖y‖`.
-/

namespace BookProof.CcrNoBounded

/-! ## The book's literal claim: a null momentum contradicts the CCR -/

/-- A vanishing momentum makes the commutator vanish. -/
theorem commutator_eq_zero_of_momentum_zero {A : Type*} [Ring A] (q p : A) (hp : p = 0) :
    q * p - p * q = 0 := by
  subst hp
  simp

/-- **A constrained (null) conjugate momentum is incompatible with the canonical
commutation relation.**  If `p = 0`, the commutator `q p − p q` vanishes and therefore
cannot equal a nonzero multiple of the identity. -/
theorem ccr_fails_of_momentum_zero {A : Type*} [Ring A] [Module ℝ A]
    [NoZeroSMulDivisors ℝ A] [Nontrivial A] (q p : A) (hp : p = 0) {c : ℝ} (hc : c ≠ 0) :
    q * p - p * q ≠ c • (1 : A) := by
  rw [commutator_eq_zero_of_momentum_zero q p hp]
  exact fun h => (smul_ne_zero hc (one_ne_zero : (1 : A) ≠ 0)) h.symm

/-! ## The finite-dimensional no-go, by the trace -/

/-- **No finite-dimensional representation of the CCR.**  The trace of a commutator
vanishes, while the trace of a nonzero multiple of the identity is `c · n ≠ 0`. -/
theorem matrix_no_ccr {n : ℕ} (hn : 0 < n) (q p : Matrix (Fin n) (Fin n) ℂ) {c : ℂ}
    (hc : c ≠ 0) :
    q * p - p * q ≠ c • (1 : Matrix (Fin n) (Fin n) ℂ) := by
  intro h
  have htr : Matrix.trace (q * p - p * q) = 0 := by
    rw [Matrix.trace_sub, Matrix.trace_mul_comm, sub_self]
  rw [h, Matrix.trace_smul, Matrix.trace_one, Fintype.card_fin, smul_eq_mul] at htr
  have hn' : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hn.ne'
  rcases mul_eq_zero.mp htr with h' | h'
  · exact hc h'
  · exact hn' h'

/-! ## The Wielandt–Wintner theorem -/

variable {A : Type*} [NormedRing A] [NormedAlgebra ℝ A]

/-- The iterated commutator identity `xⁿ⁺¹ y − y xⁿ⁺¹ = (n+1) · xⁿ` implied by the CCR
`x y − y x = 1`. -/
theorem ccr_pow {x y : A} (h : x * y - y * x = 1) (n : ℕ) :
    x ^ (n + 1) * y - y * x ^ (n + 1) = ((n : ℝ) + 1) • x ^ n := by
  induction n with
  | zero => simpa using h
  | succ n ih =>
    have hxy : x * y = 1 + y * x := sub_eq_iff_eq_add.mp h
    have e1 : x ^ (n + 1 + 1) * y - y * x ^ (n + 1 + 1)
        = (x ^ (n + 1) * y - y * x ^ (n + 1)) * x + x ^ (n + 1) := by
      rw [pow_succ x (n + 1), mul_assoc (x ^ (n + 1)) x y, hxy]
      noncomm_ring
    rw [e1, ih, smul_mul_assoc, ← pow_succ]
    push_cast
    module

/-- Under the CCR no power of `x` can vanish. -/
theorem ccr_pow_ne_zero [Nontrivial A] {x y : A} (h : x * y - y * x = 1) (n : ℕ) :
    x ^ n ≠ 0 := by
  have key : ∀ m : ℕ, x ^ m = 0 → (1 : A) = 0 := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      intro hm
      have hcomm := ccr_pow h m
      rw [hm] at hcomm
      simp only [mul_zero, zero_mul, sub_zero] at hcomm
      have hc : ((m : ℝ) + 1) ≠ 0 := by positivity
      refine ih ?_
      rcases smul_eq_zero.mp hcomm.symm with h' | h'
      · exact absurd h' hc
      · exact h'
  intro hx
  exact absurd (key n hx) one_ne_zero

/-- **Wielandt–Wintner.**  In a nontrivial normed real algebra — in particular in the
algebra of bounded operators on a Banach space, or in any C*-algebra — the canonical
commutation relation `x y − y x = 1` has no solution.  The position and momentum operators
of quantum mechanics are therefore necessarily unbounded. -/
theorem no_ccr_one [Nontrivial A] (x y : A) : x * y - y * x ≠ 1 := by
  intro h
  obtain ⟨N, hN⟩ := exists_nat_gt (2 * ‖x‖ * ‖y‖)
  have hpow : x ^ N ≠ 0 := ccr_pow_ne_zero h N
  have hnorm_pos : 0 < ‖x ^ N‖ := norm_pos_iff.mpr hpow
  have hcomm := ccr_pow h N
  have hnx : ‖x ^ (N + 1)‖ ≤ ‖x ^ N‖ * ‖x‖ := by
    rw [pow_succ]
    exact norm_mul_le _ _
  have h2 : ‖x ^ (N + 1) * y - y * x ^ (N + 1)‖ ≤ 2 * ‖x‖ * ‖y‖ * ‖x ^ N‖ := by
    calc ‖x ^ (N + 1) * y - y * x ^ (N + 1)‖
        ≤ ‖x ^ (N + 1) * y‖ + ‖y * x ^ (N + 1)‖ := norm_sub_le _ _
      _ ≤ ‖x ^ (N + 1)‖ * ‖y‖ + ‖y‖ * ‖x ^ (N + 1)‖ :=
          add_le_add (norm_mul_le _ _) (norm_mul_le _ _)
      _ ≤ (‖x ^ N‖ * ‖x‖) * ‖y‖ + ‖y‖ * (‖x ^ N‖ * ‖x‖) :=
          add_le_add (mul_le_mul_of_nonneg_right hnx (norm_nonneg y))
            (mul_le_mul_of_nonneg_left hnx (norm_nonneg y))
      _ = 2 * ‖x‖ * ‖y‖ * ‖x ^ N‖ := by ring
  have h1 : ‖((N : ℝ) + 1) • x ^ N‖ = ((N : ℝ) + 1) * ‖x ^ N‖ := by
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (by positivity)]
  have hle : ((N : ℝ) + 1) * ‖x ^ N‖ ≤ 2 * ‖x‖ * ‖y‖ * ‖x ^ N‖ := by
    rw [← h1, ← hcomm]
    exact h2
  have hfin : ((N : ℝ) + 1) ≤ 2 * ‖x‖ * ‖y‖ :=
    le_of_mul_le_mul_right (by linarith [hle]) hnorm_pos
  linarith

/-- The same statement with an arbitrary nonzero scalar on the right-hand side — the
physics convention is `c = ħ` after absorbing the factor `i`. -/
theorem no_ccr_smul [Nontrivial A] (x y : A) {c : ℝ} (hc : c ≠ 0) :
    x * y - y * x ≠ c • (1 : A) := by
  intro h
  have hx : (c⁻¹ • x) * y - y * (c⁻¹ • x) = 1 := by
    have hrw : (c⁻¹ • x) * y - y * (c⁻¹ • x) = c⁻¹ • (x * y - y * x) := by
      rw [smul_mul_assoc, mul_smul_comm, smul_sub]
    rw [hrw, h, smul_smul, inv_mul_cancel₀ hc, one_smul]
  exact no_ccr_one (c⁻¹ • x) y hx

end BookProof.CcrNoBounded
