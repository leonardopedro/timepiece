import Mathlib

/-!
# Legendre polynomials, their differential equation, and the coefficients of
their derivatives

This module provides the one-variable algebraic input needed to identify the
associated Legendre functions / spherical harmonics `Y_{lμ}` of `book.tex` §A.5
with harmonic functions homogeneous of degree `l` (the missing ingredient of
Note 68, recorded until now as an open boundary).  Mathlib has no Legendre
polynomials, so they are built here from Rodrigues' formula.

## Contents

* `iterD_add`, `iterD_X_mul`, `iterD_Xsq_mul` — Leibniz rules for the iterated
  derivative of `X · f` and `X² · f` (the two cases needed below);
* `legendreAux l = (d/dX)ˡ (X²−1)ˡ` and the normalized
  `legendre l = (2ˡ l!)⁻¹ (d/dX)ˡ (X²−1)ˡ` (Rodrigues' formula);
* `legendreAux_ode`, `legendre_ode` — **Legendre's differential equation**
  `(1−X²)P'' − 2X P' + l(l+1) P = 0`;
* `legendre_deriv_ode` — the equation satisfied by the `μ`-th derivative
  `Y = P^{(μ)}` (the Gegenbauer form)
  `(1−X²)Y'' − 2(μ+1) X Y' + (l−μ)(l+μ+1) Y = 0`;
* `legendre_deriv_coeff_rec` — the resulting **two-step coefficient recursion**
  `(j+2)(j+1) Y_{j+2} = −((l−μ)−j)((l−μ)+j+2μ+1) Y_j`, which is exactly the
  condition for the associated solid harmonic to be harmonic;
* `legendre_natDegree_le`, `legendre_deriv_coeff_eq_zero_of_lt`,
  `legendre_deriv_parity` — degree and parity of `Y`, needed to sum the
  associated solid harmonic over the right index set;
* `legendre_coeff_top`, `legendre_ne_zero` — the leading coefficient of `P_l`
  is `(2l)!/(2ˡ (l!)²) ≠ 0`, so the construction is not vacuous.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.ChapterLegendrePolynomial

open Polynomial

/-! ## Leibniz rules for the iterated derivative -/

theorem iterD_add (k : ℕ) (p q : ℝ[X]) :
    derivative^[k] (p + q) = derivative^[k] p + derivative^[k] q := by
  induction k generalizing p q with
  | zero => simp
  | succ k ih =>
      rw [Function.iterate_succ_apply, Function.iterate_succ_apply, Function.iterate_succ_apply,
        derivative_add, ih]

theorem iterD_X_mul_succ (k : ℕ) (f : ℝ[X]) :
    derivative^[k+1] (X * f) = X * derivative^[k+1] f + C ((k : ℝ) + 1) * derivative^[k] f := by
  induction k with
  | zero => simp [derivative_mul]; ring
  | succ k ih =>
      rw [Function.iterate_succ_apply' derivative (k+1) (X * f), ih, derivative_add,
        derivative_mul, derivative_mul, derivative_X, derivative_C, one_mul, zero_mul, zero_add,
        ← Function.iterate_succ_apply' derivative (k+1) f,
        ← Function.iterate_succ_apply' derivative k f]
      generalize derivative^[k+1] f = a
      generalize derivative^[k+1+1] f = b
      push_cast
      simp only [C_add, C_1]
      ring

/-- Leibniz for `X · f`: `(X f)^{(k)} = X f^{(k)} + k f^{(k−1)}`. -/
theorem iterD_X_mul (k : ℕ) (f : ℝ[X]) :
    derivative^[k] (X * f) = X * derivative^[k] f + C (k : ℝ) * derivative^[k-1] f := by
  cases k with
  | zero => simp
  | succ k => simpa using iterD_X_mul_succ k f

/-- Leibniz for `X² · f`:
`(X² f)^{(k)} = X² f^{(k)} + 2k X f^{(k−1)} + k(k−1) f^{(k−2)}`. -/
theorem iterD_Xsq_mul (k : ℕ) (f : ℝ[X]) :
    derivative^[k] (X ^ 2 * f)
      = X ^ 2 * derivative^[k] f + C (2 * (k : ℝ)) * X * derivative^[k-1] f
        + C ((k : ℝ) * ((k : ℝ) - 1)) * derivative^[k-2] f := by
  have h1 : X ^ 2 * f = X * (X * f) := by ring
  rw [h1, iterD_X_mul k (X * f), iterD_X_mul k f, iterD_X_mul (k-1) f]
  match k with
  | 0 => simp; ring
  | 1 => simp; push_cast; simp only [C_add, C_1, C_mul, map_ofNat]; ring
  | (n+2) =>
      have e1 : n + 2 - 1 = n + 1 := rfl
      have e2 : n + 2 - 2 = n := rfl
      have e3 : n + 1 - 1 = n := rfl
      rw [e1, e2, e3]
      push_cast
      simp only [C_sub, C_add, C_mul, C_1, map_ofNat]
      ring

/-! ## Rodrigues' formula and Legendre's equation -/

/-- The unnormalized Rodrigues polynomial `(d/dX)ˡ (X²−1)ˡ`. -/
noncomputable def legendreAux (l : ℕ) : ℝ[X] := derivative^[l] ((X ^ 2 - 1) ^ l)

/-- **The Legendre polynomial** `P_l = (2ˡ l!)⁻¹ (d/dX)ˡ (X²−1)ˡ`. -/
noncomputable def legendre (l : ℕ) : ℝ[X] :=
  C ((2 ^ l * (Nat.factorial l : ℝ))⁻¹) * legendreAux l

theorem rodrigues_step (l : ℕ) :
    (X ^ 2 - 1) * derivative ((X ^ 2 - 1) ^ l) = C (2 * (l : ℝ)) * X * (X ^ 2 - 1) ^ l := by
  rcases l with _ | l
  · simp
  · rw [derivative_pow]
    simp only [derivative_sub, derivative_X_pow, derivative_one, Nat.add_sub_cancel]
    push_cast
    simp only [C_add, C_1, C_mul, map_ofNat]
    ring_nf

/-- **Legendre's differential equation** for the unnormalized polynomial. -/
theorem legendreAux_ode (l : ℕ) :
    (X ^ 2 - 1) * derivative^[2] (legendreAux l) + C 2 * X * derivative (legendreAux l)
      - C ((l : ℝ) * ((l : ℝ) + 1)) * legendreAux l = 0 := by
  rcases l with _ | l
  · simp [legendreAux]
  · set n := l + 1 with hn
    set v : ℝ[X] := (X ^ 2 - 1) ^ n with hv
    have hLHS := congrArg (fun p => derivative^[n+1] p) (rodrigues_step n)
    have e1 : (X ^ 2 - 1 : ℝ[X]) * derivative v = X ^ 2 * derivative v - derivative v := by ring
    rw [e1, iterate_derivative_sub, iterD_Xsq_mul (n+1) (derivative v),
      show C (2 * (n : ℝ)) * X * v = C (2 * (n : ℝ)) * (X * v) from by ring,
      iterate_derivative_C_mul, iterD_X_mul (n+1) v] at hLHS
    have d1 : derivative^[n+1] (derivative v) = derivative^[n+2] v := by
      rw [← Function.iterate_succ_apply derivative (n+1) v]
    have d2 : derivative^[n+1-1] (derivative v) = derivative^[n+1] v := by
      simp only [Nat.add_sub_cancel]
      rw [← Function.iterate_succ_apply derivative n v]
    have d3 : derivative^[n+1-2] (derivative v) = derivative^[n] v := by
      have h : n + 1 - 2 = n - 1 := by omega
      rw [h, ← Function.iterate_succ_apply derivative (n-1) v]
      congr 1
    rw [d1, d2, d3] at hLHS
    have hu : legendreAux n = derivative^[n] v := rfl
    have hu1 : derivative (legendreAux n) = derivative^[n+1] v := by
      rw [hu, ← Function.iterate_succ_apply' derivative n v]
    have hu2 : derivative^[2] (legendreAux n) = derivative^[n+2] v := by
      rw [hu, ← Function.iterate_add_apply derivative 2 n v, Nat.add_comm]
    rw [hu2, hu1, hu, show n + 1 - 1 = n from rfl] at *
    push_cast at hLHS ⊢
    simp only [C_add, C_1, C_mul, map_ofNat, C_sub] at hLHS ⊢
    linear_combination hLHS

/-- **The equation satisfied by the `μ`-th derivative of the Legendre
polynomial** (Gegenbauer form). -/
theorem legendreAux_deriv_ode (l μ : ℕ) :
    (X ^ 2 - 1) * derivative^[2] (derivative^[μ] (legendreAux l))
      + C (2 * (μ : ℝ) + 2) * X * derivative (derivative^[μ] (legendreAux l))
      + C ((μ : ℝ) * ((μ : ℝ) + 1) - (l : ℝ) * ((l : ℝ) + 1)) * derivative^[μ] (legendreAux l)
      = 0 := by
  set u : ℝ[X] := legendreAux l with hu
  have sh : ∀ (a b : ℕ), derivative^[a] (derivative^[b] u) = derivative^[a+b] u := by
    intro a b; rw [← Function.iterate_add_apply]
  have key := congrArg (fun p => derivative^[μ] p) (legendreAux_ode l)
  simp only [← hu] at key
  have e1 : (X ^ 2 - 1 : ℝ[X]) * derivative^[2] u
      = X ^ 2 * derivative^[2] u - derivative^[2] u := by ring
  rw [e1, iterate_derivative_sub, iterD_add, iterate_derivative_sub,
    iterD_Xsq_mul μ (derivative^[2] u),
    show C 2 * X * derivative u = C (2 : ℝ) * (X * derivative u) from by ring,
    iterate_derivative_C_mul, iterD_X_mul μ (derivative u),
    iterate_derivative_C_mul, iterate_derivative_zero] at key
  have n1 : derivative^[μ] (derivative^[2] u) = derivative^[μ+2] u := sh μ 2
  have n2 : derivative^[μ] (derivative u) = derivative^[μ+1] u := by
    rw [show derivative u = derivative^[1] u from rfl, sh μ 1]
  have n3 : C ((μ : ℝ) * ((μ : ℝ) - 1)) * derivative^[μ-2] (derivative^[2] u)
      = C ((μ : ℝ) * ((μ : ℝ) - 1)) * derivative^[μ] u := by
    match μ with
    | 0 => norm_num
    | 1 => norm_num
    | (n+2) => rw [show n + 2 - 2 = n from rfl, sh n 2]
  have n4 : C (2 * (μ : ℝ)) * X * derivative^[μ-1] (derivative^[2] u)
      = C (2 * (μ : ℝ)) * X * derivative^[μ+1] u := by
    match μ with
    | 0 => norm_num
    | (n+1) => rw [show n + 1 - 1 = n from rfl, sh n 2]
  have n5 : C ((μ : ℝ)) * derivative^[μ-1] (derivative u)
      = C ((μ : ℝ)) * derivative^[μ] u := by
    match μ with
    | 0 => norm_num
    | (n+1) => rw [show n + 1 - 1 = n from rfl, show derivative u = derivative^[1] u from rfl,
        sh n 1]
  rw [n1, n4, n3, n2, n5] at key
  rw [sh 2 μ, Nat.add_comm 2 μ, show derivative (derivative^[μ] u) = derivative^[μ+1] u from by
    rw [← Function.iterate_succ_apply' derivative μ u]]
  simp only [C_add, C_1, C_mul, map_ofNat, C_sub] at key ⊢
  linear_combination key

/-- The same equation for the normalized Legendre polynomial. -/
theorem legendre_deriv_ode (l μ : ℕ) :
    (X ^ 2 - 1) * derivative^[2] (derivative^[μ] (legendre l))
      + C (2 * (μ : ℝ) + 2) * X * derivative (derivative^[μ] (legendre l))
      + C ((μ : ℝ) * ((μ : ℝ) + 1) - (l : ℝ) * ((l : ℝ) + 1)) * derivative^[μ] (legendre l)
      = 0 := by
  have hc : derivative^[μ] (legendre l)
      = C ((2 ^ l * (Nat.factorial l : ℝ))⁻¹) * derivative^[μ] (legendreAux l) := by
    rw [legendre, iterate_derivative_C_mul]
  rw [hc, iterate_derivative_C_mul, derivative_C_mul]
  linear_combination (C ((2 ^ l * (Nat.factorial l : ℝ))⁻¹)) * legendreAux_deriv_ode l μ

/-! ## The coefficient recursion -/

theorem coeff_iterD_two (Y : ℝ[X]) (j : ℕ) :
    (derivative^[2] Y).coeff j = (((j : ℝ) + 2) * ((j : ℝ) + 1)) * Y.coeff (j + 2) := by
  rw [coeff_iterate_derivative]
  have h : (j + 2).descFactorial 2 = (j + 2) * (j + 1) := by
    simp [Nat.descFactorial]; ring
  rw [h]
  push_cast
  ring

/-- **The two-step recursion for the coefficients of the `μ`-th derivative of
the Legendre polynomial.** -/
theorem legendre_deriv_coeff_rec (l μ j : ℕ) :
    (((j : ℝ) + 2) * ((j : ℝ) + 1)) * (derivative^[μ] (legendre l)).coeff (j + 2)
      = ((j : ℝ) * ((j : ℝ) - 1) + (2 * (μ : ℝ) + 2) * j
          + ((μ : ℝ) * ((μ : ℝ) + 1) - (l : ℝ) * ((l : ℝ) + 1)))
        * (derivative^[μ] (legendre l)).coeff j := by
  set Y : ℝ[X] := derivative^[μ] (legendre l) with hY
  have hode := legendre_deriv_ode l μ
  rw [← hY] at hode
  have hco := congrArg (fun p : ℝ[X] => p.coeff j) hode
  simp only [coeff_add, coeff_sub, coeff_zero, coeff_C_mul] at hco
  have e1 : ((X ^ 2 - 1 : ℝ[X]) * derivative^[2] Y).coeff j
      = (X ^ 2 * derivative^[2] Y).coeff j - (derivative^[2] Y).coeff j := by
    rw [show (X ^ 2 - 1 : ℝ[X]) * derivative^[2] Y
      = X ^ 2 * derivative^[2] Y - derivative^[2] Y from by ring, coeff_sub]
  have e2 : (X ^ 2 * derivative^[2] Y).coeff j
      = if 2 ≤ j then (derivative^[2] Y).coeff (j - 2) else 0 := by
    rw [mul_comm, coeff_mul_X_pow']
  have e3 : (C (2 * (μ : ℝ) + 2) * X * derivative Y).coeff j
      = (2 * (μ : ℝ) + 2) * (if 1 ≤ j then (derivative Y).coeff (j - 1) else 0) := by
    rw [mul_assoc, coeff_C_mul, mul_comm X (derivative Y), ← pow_one X, coeff_mul_X_pow']
  rw [e1, e2, e3] at hco
  have hd : ∀ k : ℕ, (derivative Y).coeff k = ((k : ℝ) + 1) * Y.coeff (k + 1) := by
    intro k
    rw [coeff_derivative]
    push_cast
    ring
  match j with
  | 0 =>
      simp only [coeff_iterD_two, hd] at hco ⊢
      norm_num at hco ⊢
      linarith [hco]
  | 1 =>
      simp only [coeff_iterD_two, hd] at hco ⊢
      norm_num at hco ⊢
      linarith [hco]
  | (i + 2) =>
      have hj2 : i + 2 - 2 = i := rfl
      have hj1 : i + 2 - 1 = i + 1 := rfl
      simp only [hj2, hj1, coeff_iterD_two, hd, if_pos (by omega : 2 ≤ i + 2),
        if_pos (by omega : 1 ≤ i + 2)] at hco ⊢
      push_cast at hco ⊢
      linarith [hco]

/-! ## Degree, parity and the leading coefficient -/

theorem natDegree_Xsq_sub_one : (X ^ 2 - 1 : ℝ[X]).natDegree = 2 := by
  have h : (X ^ 2 - 1 : ℝ[X]) = X ^ 2 - C 1 := by simp
  rw [h, natDegree_X_pow_sub_C]

theorem legendreAux_natDegree_le (l : ℕ) : (legendreAux l).natDegree ≤ l := by
  have h := natDegree_iterate_derivative ((X ^ 2 - 1 : ℝ[X]) ^ l) l
  have h2 : ((X ^ 2 - 1 : ℝ[X]) ^ l).natDegree = 2 * l := by
    rw [natDegree_pow, natDegree_Xsq_sub_one]; ring
  rw [legendreAux]
  omega

theorem legendre_natDegree_le (l : ℕ) : (legendre l).natDegree ≤ l :=
  le_trans (natDegree_C_mul_le _ _) (legendreAux_natDegree_le l)

theorem legendre_coeff_eq_zero_of_lt (l k : ℕ) (h : l < k) : (legendre l).coeff k = 0 :=
  coeff_eq_zero_of_natDegree_lt (lt_of_le_of_lt (legendre_natDegree_le l) h)

/-- The `μ`-th derivative of `P_l` has degree at most `l − μ`. -/
theorem legendre_deriv_coeff_eq_zero (l μ k : ℕ) (h : l < k + μ) :
    (derivative^[μ] (legendre l)).coeff k = 0 := by
  rw [coeff_iterate_derivative, legendre_coeff_eq_zero_of_lt l (k + μ) h, smul_zero]

theorem monic_Xsq_sub_one : (X ^ 2 - 1 : ℝ[X]).Monic := by
  have h : (X ^ 2 - 1 : ℝ[X]) = X ^ 2 - C 1 := by simp
  rw [h]
  exact monic_X_pow_sub_C 1 (by norm_num)

theorem legendreAux_coeff_self (l : ℕ) :
    (legendreAux l).coeff l = ((2 * l).descFactorial l : ℝ) := by
  rw [legendreAux, coeff_iterate_derivative]
  have hm : ((X ^ 2 - 1 : ℝ[X]) ^ l).Monic := monic_Xsq_sub_one.pow l
  have hdeg : ((X ^ 2 - 1 : ℝ[X]) ^ l).natDegree = 2 * l := by
    rw [natDegree_pow, natDegree_Xsq_sub_one]; ring
  have hc : ((X ^ 2 - 1 : ℝ[X]) ^ l).coeff (l + l) = 1 := by
    have h := hm.coeff_natDegree
    rw [hdeg] at h
    rw [show l + l = 2 * l from by ring]
    exact h
  rw [hc, show l + l = 2 * l from by ring]
  simp

/-- The leading coefficient of `P_l` is `(2l)!/(2ˡ (l!)²) ≠ 0`. -/
theorem legendre_coeff_self_ne_zero (l : ℕ) : (legendre l).coeff l ≠ 0 := by
  rw [legendre, coeff_C_mul, legendreAux_coeff_self]
  have h1 : ((2 * l).descFactorial l : ℝ) ≠ 0 := by
    have h : (2 * l).descFactorial l ≠ 0 := by
      have := Nat.descFactorial_eq_zero_iff_lt (n := 2 * l) (k := l)
      omega
    exact_mod_cast h
  have h2 : ((2 : ℝ) ^ l * (Nat.factorial l : ℝ))⁻¹ ≠ 0 := by
    apply inv_ne_zero
    positivity
  exact mul_ne_zero h2 h1

/-- The `μ`-th derivative of `P_l` has degree exactly `l − μ` (for `μ ≤ l`), so
the associated solid harmonic below is not the zero function. -/
theorem legendre_deriv_coeff_top_ne_zero (l μ : ℕ) (h : μ ≤ l) :
    (derivative^[μ] (legendre l)).coeff (l - μ) ≠ 0 := by
  rw [coeff_iterate_derivative, show l - μ + μ = l from by omega]
  have h1 : l.descFactorial μ ≠ 0 := by
    have := Nat.descFactorial_eq_zero_iff_lt (n := l) (k := μ)
    omega
  have h2 := legendre_coeff_self_ne_zero l
  simp only [nsmul_eq_mul, ne_eq, mul_eq_zero, not_or]
  exact ⟨by exact_mod_cast h1, h2⟩

/-- The multiplier of the coefficient recursion, in factored form, is nonzero
away from the top degree `l − μ`. -/
theorem rec_coeff_ne_zero (l μ j : ℕ) (h : μ ≤ l) (hne : j ≠ l - μ) :
    ((j : ℝ) * ((j : ℝ) - 1) + (2 * (μ : ℝ) + 2) * j
      + ((μ : ℝ) * ((μ : ℝ) + 1) - (l : ℝ) * ((l : ℝ) + 1))) ≠ 0 := by
  have hn : ((l - μ : ℕ) : ℝ) = (l : ℝ) - (μ : ℝ) := by
    push_cast [h]; ring
  have hfac : ((j : ℝ) * ((j : ℝ) - 1) + (2 * (μ : ℝ) + 2) * j
      + ((μ : ℝ) * ((μ : ℝ) + 1) - (l : ℝ) * ((l : ℝ) + 1)))
      = ((j : ℝ) - ((l - μ : ℕ) : ℝ)) * ((j : ℝ) + ((l - μ : ℕ) : ℝ) + 2 * μ + 1) := by
    rw [hn]; ring
  rw [hfac]
  refine mul_ne_zero ?_ ?_
  · have hcast : ((j : ℝ)) ≠ ((l - μ : ℕ) : ℝ) := by exact_mod_cast hne
    intro hzero
    exact hcast (by linarith)
  · have h1 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
    have h2 : (0 : ℝ) ≤ ((l - μ : ℕ) : ℝ) := Nat.cast_nonneg _
    have h3 : (0 : ℝ) ≤ (μ : ℝ) := Nat.cast_nonneg μ
    linarith

/-- **Parity**: the `μ`-th derivative of `P_l` contains only powers congruent to
`l − μ` modulo `2`. -/
theorem legendre_deriv_coeff_parity (l μ : ℕ) (h : μ ≤ l) (j : ℕ)
    (hpar : j % 2 ≠ (l - μ) % 2) : (derivative^[μ] (legendre l)).coeff j = 0 := by
  by_contra hne
  have step : ∀ k : ℕ, (derivative^[μ] (legendre l)).coeff (j + 2 * k) ≠ 0 := by
    intro k
    induction k with
    | zero => simpa using hne
    | succ k ih =>
        intro hzero
        apply ih
        have hrec := legendre_deriv_coeff_rec l μ (j + 2 * k)
        rw [show j + 2 * (k + 1) = j + 2 * k + 2 from by ring] at hzero
        rw [hzero, mul_zero] at hrec
        have hc := rec_coeff_ne_zero l μ (j + 2 * k) h (by omega)
        exact (mul_eq_zero.mp hrec.symm).resolve_left hc
  exact step (l + 1) (legendre_deriv_coeff_eq_zero l μ (j + 2 * (l + 1)) (by omega))

end BookProof.ChapterLegendrePolynomial
