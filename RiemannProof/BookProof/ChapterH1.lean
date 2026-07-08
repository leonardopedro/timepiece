import Mathlib

/-!
# Chapter H1 — Hashimoto SIRK: φ-functions and resolvent algebra (roadmap N13, §0 S7)

This file formalizes the algebraic backbone of the Hashimoto–Nodera *Shift-invert
Rational Krylov (SIRK)* method (source `RiemannProof/Hashimoto.md`; `book.tex`
cites at lines 1147 / 2055).  It follows §0 S7 of the roadmap (the numerical
backbone of the Mehler/Hashimoto Fock formalism), and the `IsSchurFull`/`EXTERNAL`
design pattern: the genuinely deep analytic inputs (Crouzeix's inequality, the
Göckler–Grimm / Hashimoto RK error theorems) are named hypotheses with citation
docstrings in `ChapterH2.lean`, never axioms; everything here is proved outright.

## Deliverables (this file)

* **H1.1 — the φ-functions.** `phi : ℕ → ℂ → ℂ`, `phi 0 = exp`,
  `phi (k+1) z = ∫ s in 0..1, exp (s·z)·(1−s)^k / k!` (eq. 3); `phi_zero`,
  `phi_at_zero : phi k 0 = 1/k!`.
* **H1.2 — the φ-recurrence.** `phi_succ_mul : z · phi (k+1) z = phi k z − 1/k!`
  (integration by parts); corollary `phi_one : z ≠ 0 → phi 1 z = (exp z − 1)/z`.
* **H1.4 — numerical range & eigenvalue inclusion.** `numericalRange A` (the set
  of Rayleigh quotients) with `eigenvalue_mem_numericalRange` (every eigenvalue
  lies in `W(A)` — the easy half of Toeplitz–Hausdorff).
* **H1.6 — the resolvent shift identity (the clean SIRK algebra core).** The
  resolvent identity `resolvent_identity` and the SIRK shift form
  `resolvent_shift_mul : X_j · (1 + h(m−j)·X_m) = X_m` for `γ_j = N − h·j`
  (§4, between eqs. (10)–(11)) — purely algebraic, no analysis.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`); **no `EXTERNAL` hypothesis**.
-/

open scoped BigOperators
open intervalIntegral

namespace BookProof.ChapterH1

noncomputable section

/-! ## H1.1 — the φ-functions and their values -/

/-- The φ-functions (Hashimoto eq. 3): `φ₀ = exp`, and for `k ≥ 0`
`φ_{k+1}(z) = ∫₀¹ e^{s z} (1−s)^k / k! ds`.  Each `φ_k` is entire (a convergent
power series). -/
noncomputable def phi : ℕ → ℂ → ℂ
  | 0, z => Complex.exp z
  | (k + 1), z => ∫ s in (0 : ℝ)..1, Complex.exp (s * z) * (1 - s) ^ k / k.factorial

/-- **H1.1**: `φ₀ = exp`. -/
theorem phi_zero : phi 0 = Complex.exp := rfl

@[simp] theorem phi_zero_apply (z : ℂ) : phi 0 z = Complex.exp z := rfl

theorem phi_succ_apply (k : ℕ) (z : ℂ) :
    phi (k + 1) z = ∫ s in (0 : ℝ)..1, Complex.exp (s * z) * (1 - s) ^ k / k.factorial := rfl

/-
**H1.1** (values at `0`): `φ_k(0) = 1/k!`.
For `k = 0` this is `exp 0 = 1`.  For `k+1`, the integrand at `z = 0` is
`(1−s)^k / k!`, whose integral over `[0,1]` is `1/((k+1)·k!) = 1/(k+1)!`.
-/
theorem phi_at_zero (k : ℕ) : phi k 0 = 1 / k.factorial := by
  induction' k with k ih;
  · norm_num [ phi_zero_apply ];
  · simp +decide [ *, phi_succ_apply ];
    norm_cast;
    erw [ intervalIntegral.integral_ofReal, intervalIntegral.integral_comp_sub_left fun x => x ^ k ] ; norm_num [ Nat.factorial_succ ];
    ring

/-! ## H1.2 — the φ-recurrence -/

/-
**H1.2** (recurrence): `z · φ_{k+1}(z) = φ_k(z) − 1/k!`.
Integration by parts on the defining integral: with `u = e^{s z}` and
`dv = (1−s)^k/k! ds`, the boundary terms give `φ_k(z) − 1/k!` and the remaining
integral is `z·φ_{k+1}(z)`.
-/
theorem phi_succ_mul (k : ℕ) (z : ℂ) :
    z * phi (k + 1) z = phi k z - 1 / k.factorial := by
  by_cases h : z = 0 <;> simp_all +decide [ div_eq_inv_mul, mul_assoc, mul_comm, mul_left_comm, intervalIntegral.integral_comp_mul_right ];
  · rw [ phi_at_zero ] ; ring;
  · have h_int_parts : ∫ s in (0 : ℝ)..1, deriv (fun s => Complex.exp (s * z) * (1 - s) ^ k) s = (Complex.exp (1 * z) * (1 - 1) ^ k) - (Complex.exp (0 * z) * (1 - 0) ^ k) := by
      rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
      rotate_right;
      use fun x => Complex.exp ( x * z ) * ( 1 - x ) ^ k;
      · norm_num;
      · intro x hx; convert HasDerivAt.comp x ( hasDerivAt_deriv_iff.mpr <| show DifferentiableAt ℂ ( fun s => Complex.exp ( s * z ) * ( 1 - s ) ^ k ) _ from DifferentiableAt.mul ( Complex.differentiableAt_exp.comp _ <| differentiableAt_id.mul_const _ ) <| DifferentiableAt.pow ( differentiableAt_id.const_sub _ ) _ ) ( hasDerivAt_id _ |> HasDerivAt.ofReal_comp ) using 1; aesop;
      · apply_rules [ Continuous.intervalIntegrable ];
        fun_prop;
    have h_int_parts : ∫ s in (0 : ℝ)..1, deriv (fun s => Complex.exp (s * z) * (1 - s) ^ k) s = ∫ s in (0 : ℝ)..1, (z * Complex.exp (s * z) * (1 - s) ^ k - k * Complex.exp (s * z) * (1 - s) ^ (k - 1)) := by
      refine' intervalIntegral.integral_congr fun x hx => _;
      convert HasDerivAt.deriv ( HasDerivAt.mul ( HasDerivAt.comp _ ( Complex.hasDerivAt_exp _ ) ( hasDerivAt_mul_const _ ) ) ( HasDerivAt.comp _ ( hasDerivAt_pow k _ ) ( hasDerivAt_id' _ |> HasDerivAt.const_sub _ ) ) ) using 1 ; norm_num ; ring;
    rcases k with ( _ | k ) <;> simp_all +decide [ mul_assoc, mul_div_assoc ];
    · exact intervalIntegral.integral_congr fun x _ => by norm_num [ phi ] ;
    · rw [ intervalIntegral.integral_sub ] at * <;> norm_num at *;
      · simp_all +decide [ Nat.factorial_succ, phi ];
        field_simp;
        grind;
      · exact Continuous.intervalIntegrable ( by continuity ) _ _;
      · exact Continuous.intervalIntegrable ( by continuity ) _ _

/-- **H1.2** (corollary): `φ₁(z) = (e^{z} − 1)/z` for `z ≠ 0`. -/
theorem phi_one {z : ℂ} (hz : z ≠ 0) : phi 1 z = (Complex.exp z - 1) / z := by
  have h := phi_succ_mul 0 z
  simp only [phi_zero_apply, Nat.factorial_zero, Nat.cast_one, div_one] at h
  field_simp
  linear_combination h

/-! ## H1.4 — numerical range and eigenvalue inclusion -/

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-- The **numerical range** `W(A)` of an operator: the set of Rayleigh quotients
`⟪v, A v⟫` over unit vectors `v`. -/
def numericalRange (A : E →ₗ[ℂ] E) : Set ℂ :=
  { c | ∃ v : E, ‖v‖ = 1 ∧ (inner (𝕜 := ℂ) v (A v)) = c }

/-
**H1.4** (eigenvalue inclusion — the easy half of Toeplitz–Hausdorff): every
eigenvalue of `A` lies in its numerical range.  If `A v = λ v` with `‖v‖ = 1`,
then `⟪v, A v⟫ = λ·⟪v, v⟫ = λ·‖v‖² = λ`.
-/
theorem eigenvalue_mem_numericalRange (A : E →ₗ[ℂ] E) (l : ℂ) (v : E)
    (hv : ‖v‖ = 1) (hAv : A v = l • v) : l ∈ numericalRange A := by
  use v;
  simp_all +decide [ inner_self_eq_norm_sq_to_K ]

/-! ## H1.6 — the resolvent shift identity (the clean SIRK algebra core) -/

variable {A : Type*} [Ring A] [Algebra ℂ A]

/-
**H1.6** (resolvent identity): if `X_j` and `X_m` are two-sided inverses of
the shifted operators `γ_j·1 − a` and `γ_m·1 − a`, then
`X_j − X_m = (γ_m − γ_j)·(X_j · X_m)`.  Purely algebraic: insert the two
inverses and cancel `a`.
-/
theorem resolvent_identity (a : A) (gj gm : ℂ) (Xj Xm : A)
    (hjl : (algebraMap ℂ A gj - a) * Xj = 1) (hjr : Xj * (algebraMap ℂ A gj - a) = 1)
    (hml : (algebraMap ℂ A gm - a) * Xm = 1) (hmr : Xm * (algebraMap ℂ A gm - a) = 1) :
    Xj - Xm = (gm - gj) • (Xj * Xm) := by
  -- Using the fact that $Xj * (γ_m - a) = 1$ and $Xm * (γ_m - a) = 1$, we can simplify the expression.
  have h_simp : Xj * (gm - gj) • 1 * Xm = Xj * (algebraMap ℂ A gm - a) * Xm - Xj * (algebraMap ℂ A gj - a) * Xm := by
    simp +decide [ sub_mul, mul_sub, Algebra.smul_def ];
  convert h_simp.symm using 1 <;> simp +decide [ mul_assoc, hjl, hjr, hml, hmr ]

/-
**H1.6** (SIRK shift form): with the SIRK shifts `γ_j = N − h·j` the resolvent
identity rearranges to `X_j · (1 + h·(m−j)·X_m) = X_m`.  This is the algebraic
core that turns the rational-Krylov recurrence into a shift-invert recurrence
(§4, between eqs. (10)–(11)); no analysis is needed.
-/
theorem resolvent_shift_mul (a : A) (N h : ℂ) (j m : ℂ)
    (Xj Xm : A)
    (hjl : (algebraMap ℂ A (N - h * j) - a) * Xj = 1)
    (hjr : Xj * (algebraMap ℂ A (N - h * j) - a) = 1)
    (hml : (algebraMap ℂ A (N - h * m) - a) * Xm = 1)
    (hmr : Xm * (algebraMap ℂ A (N - h * m) - a) = 1) :
    Xj * (1 + (h * (m - j)) • Xm) = Xm := by
  simp_all +decide [ mul_add, mul_sub, sub_mul, mul_comm, mul_left_comm, Algebra.smul_def ];
  apply_fun ( · * Xm ) at hjr ; simp_all +decide [ mul_assoc, sub_mul ];
  simp_all +decide [ mul_assoc, sub_eq_iff_eq_add ];
  simp_all +decide [ mul_add, add_mul, mul_assoc ];
  grind

end

end BookProof.ChapterH1