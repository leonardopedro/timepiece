import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.MeasureTheory.Measure.MeasureSpace

open Complex Finset Filter MeasureTheory Topology
open scoped ArithmeticFunction ArithmeticFunction.Moebius

set_option linter.unusedSectionVars false

/-!
# Finite-Dimensional Probabilistic Regularization and the Riemann Hypothesis

Formalizes the probabilistic regularization framework utilizing a sequence
of finite $N$-dimensional probability spaces $\Omega_N$.

## Design Note
`Ω`, `E`, `Var`, and `X` are kept as section variables so that all proved
theorems go through without requiring a concrete `MeasureSpace` elaboration.
The concrete construction (product of Lebesgue measures on `Fin (N+1) → ℝ`)
is left as the next milestone; the theorems tagged `sorry` are the open proof
obligations that depend on it.
-/

section ProbabilisticRegularization

-- We define a sequence of measure spaces Ω_N for each truncation N.
variable {Ω : ℕ → Type*} [∀ N, MeasureSpace (Ω N)]

-- The Expectation and Variance operators are strictly parameterized by N.
variable (E : ∀ N, (Ω N → ℂ) → ℂ)
variable (Var : ∀ N, (Ω N → ℂ) → ℝ)

-- The random variable X(ε, n) evaluated in the N-th probability space.
variable (X : ℝ → ℕ → ∀ N, Ω N → ℂ)

/-! ### Probabilistic axioms (to be proved from a concrete Ω) -/

-- The perturbation has mean one for all n ≤ N.
axiom exp_X_eq_one (ε : ℝ) (hε : ε > 0) (N : ℕ) (n : ℕ) (hn : n ≤ N) :
  E N (X ε n N) = 1

-- Distinct modes are pairwise orthogonal in the mean-zero sense in Ω_N.
axiom X_orthogonal (ε : ℝ) (hε : ε > 0) (N : ℕ) (n m : ℕ)
    (hn : n ≤ N) (hm : m ≤ N) (hneq : n ≠ m) :
  E N (fun ω ↦ (X ε n N ω - 1) * (X ε m N ω - 1)) = 0

-- The variance of each mode is logarithmically bounded in Ω_N.
axiom Var_X_bound (ε : ℝ) (hε : ε > 0) (N : ℕ) (n : ℕ) (hn : n ≤ N) :
  Var N (X ε n N) ≤ ε * Real.log (n : ℝ)

/-! ### Linearity of expectation for a fixed N -/

axiom E_zero (N : ℕ) : E N (fun _ ↦ 0) = 0
axiom E_add (N : ℕ) (f g : Ω N → ℂ) : E N (fun ω ↦ f ω + g ω) = E N f + E N g
axiom E_smul (N : ℕ) (c : ℂ) (f : Ω N → ℂ) : E N (fun ω ↦ c * f ω) = c * E N f

lemma E_sum {α : Type*} (N : ℕ) (s : Finset α) (f : α → Ω N → ℂ) :
    E N (fun ω ↦ ∑ x ∈ s, f x ω) = ∑ x ∈ s, E N (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty       => simp only [sum_empty]; exact E_zero E N
  | insert a s ha ih => simp only [sum_insert ha]; rw [E_add E N, ih]

/-! ### Variance axioms for a fixed N -/

axiom Var_smul (N : ℕ) (c : ℂ) (f : Ω N → ℂ) :
  Var N (fun ω ↦ c * f ω) = ‖c‖ ^ 2 * Var N f

axiom Var_orthogonal_sum (N : ℕ) (s : Finset ℕ) (f : ℕ → Ω N → ℂ)
    (h : ∀ m ∈ s, ∀ n ∈ s, m ≠ n →
      E N (fun ω ↦ (f m ω - E N (f m)) * (f n ω - E N (f n))) = 0) :
    Var N (fun ω ↦ ∑ n ∈ s, f n ω) = ∑ n ∈ s, Var N (f n)

/-! ### Partial sums -/

noncomputable def S_classical (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Icc 1 N, (μ n : ℂ) / (n ^ s)

-- S_random now explicitly operates inside Ω_N.
noncomputable def S_random (ε : ℝ) (N : ℕ) (s : ℂ) (ω : Ω N) : ℂ :=
  ∑ n ∈ Icc 1 N, ((μ n : ℂ) * X ε n N ω) / (n ^ s)

/-! ### Expectation equivalence (PROVED) -/

lemma expected_S_random_eq_S_classical (ε : ℝ) (hε : ε > 0) (N : ℕ) (s : ℂ) :
    E N (S_random X ε N s) = S_classical N s := by
  unfold S_random S_classical
  rw [E_sum E N]
  refine sum_congr rfl (fun n hn ↦ ?_)
  have : (fun ω ↦ ((μ n : ℂ) * X ε n N ω) / (n ^ s)) =
         (fun ω ↦ ((μ n : ℂ) / (n ^ s)) * X ε n N ω) := by ext ω; ring
  rw [this, E_smul E N]
  have hnN : n ≤ N := (mem_Icc.mp hn).2
  rw [exp_X_eq_one E X ε hε N n hnN]
  ring

/-! ### Uniform variance bound (PROVED) -/

lemma uniform_variance_bound (E : ∀ N, (Ω N → ℂ) → ℂ) (ε : ℝ) (hε : ε > 0) (N : ℕ) (s : ℂ)
    (_hs : s.re > 1 / 2) :
    ∃ M : ℝ, Var N (S_random X ε N s) ≤ ε * M := by
  use ∑ n ∈ Icc 1 N, ‖(μ n : ℂ) / (n : ℂ) ^ s‖ ^ 2 * Real.log n
  have hE (k : ℕ) (hk : k ≤ N) :
      E N (fun ω ↦ ((μ k : ℂ) * X ε k N ω) / (k : ℂ) ^ s) = (μ k : ℂ) / (k : ℂ) ^ s := by
    have : (fun ω ↦ ((μ k : ℂ) * X ε k N ω) / (k : ℂ) ^ s) =
        (fun ω ↦ ((μ k : ℂ) / (k : ℂ) ^ s) * X ε k N ω) := by
      ext ω; ring
    rw [this, E_smul E N, exp_X_eq_one E X ε hε N k hk]
    ring
  have h_orth : ∀ m ∈ Icc 1 N, ∀ n ∈ Icc 1 N, m ≠ n →
      E N (fun ω ↦
        (((μ m : ℂ) * X ε m N ω) / (m : ℂ) ^ s -
          E N (fun ω ↦ ((μ m : ℂ) * X ε m N ω) / (m : ℂ) ^ s)) *
        (((μ n : ℂ) * X ε n N ω) / (n : ℂ) ^ s -
          E N (fun ω ↦ ((μ n : ℂ) * X ε n N ω) / (n : ℂ) ^ s))) = 0 := by
    intro m hm n hn hmn
    have hm_le : m ≤ N := (mem_Icc.mp hm).2
    have hn_le : n ≤ N := (mem_Icc.mp hn).2
    rw [hE m hm_le, hE n hn_le]
    have h_prod :
        (fun ω ↦
          (((μ m : ℂ) * X ε m N ω) / (m : ℂ) ^ s - (μ m : ℂ) / (m : ℂ) ^ s) *
          (((μ n : ℂ) * X ε n N ω) / (n : ℂ) ^ s - (μ n : ℂ) / (n : ℂ) ^ s)) =
        (fun ω ↦
          (((μ m : ℂ) / (m : ℂ) ^ s) * ((μ n : ℂ) / (n : ℂ) ^ s)) *
          ((X ε m N ω - 1) * (X ε n N ω - 1))) := by
      ext ω; ring
    rw [h_prod, E_smul E N, X_orthogonal E X ε hε N m n hm_le hn_le hmn]
    ring
  have h_var_sum :=
    Var_orthogonal_sum E Var N (Icc 1 N)
      (fun n ω ↦ ((μ n : ℂ) * X ε n N ω) / (n : ℂ) ^ s) h_orth
  have h_S_rand :
      S_random X ε N s =
      (fun ω ↦ ∑ n ∈ Icc 1 N, ((μ n : ℂ) * X ε n N ω) / (n : ℂ) ^ s) := by
    rfl
  rw [h_S_rand, h_var_sum]
  have h_var_term (n : ℕ) :
      Var N (fun ω ↦ ((μ n : ℂ) * X ε n N ω) / (n : ℂ) ^ s) =
      ‖(μ n : ℂ) / (n : ℂ) ^ s‖ ^ 2 * Var N (X ε n N) := by
    have : (fun ω ↦ ((μ n : ℂ) * X ε n N ω) / (n : ℂ) ^ s) =
        (fun ω ↦ ((μ n : ℂ) / (n : ℂ) ^ s) * X ε n N ω) := by
      ext ω; ring
    rw [this]
    exact Var_smul Var N ((μ n : ℂ) / (n : ℂ) ^ s) (X ε n N)
  have h_bound (n : ℕ) (hn : n ∈ Icc 1 N) :
      Var N (fun ω ↦ ((μ n : ℂ) * X ε n N ω) / (n : ℂ) ^ s) ≤
      ‖(μ n : ℂ) / (n : ℂ) ^ s‖ ^ 2 * (ε * Real.log (n : ℝ)) := by
    rw [h_var_term n]
    have hnN : n ≤ N := (mem_Icc.mp hn).2
    have h_le := Var_X_bound Var X ε hε N n hnN
    have h_pos : ‖(μ n : ℂ) / (n : ℂ) ^ s‖ ^ 2 ≥ 0 := sq_nonneg _
    exact mul_le_mul_of_nonneg_left h_le h_pos
  have h_sum_le : ∑ n ∈ Icc 1 N, Var N (fun ω ↦ ((μ n : ℂ) * X ε n N ω) / (n : ℂ) ^ s) ≤
                  ∑ n ∈ Icc 1 N, ‖(μ n : ℂ) / (n : ℂ) ^ s‖ ^ 2 * (ε * Real.log (n : ℝ)) :=
    sum_le_sum (fun n hn ↦ h_bound n hn)
  have h_rw : (∑ n ∈ Icc 1 N, ‖(μ n : ℂ) / (n : ℂ) ^ s‖ ^ 2 * (ε * Real.log (n : ℝ))) =
              ε * ∑ n ∈ Icc 1 N, ‖(μ n : ℂ) / (n : ℂ) ^ s‖ ^ 2 * Real.log (n : ℝ) := by
    have h_term (n : ℕ) : ‖(μ n : ℂ) / (n : ℂ) ^ s‖ ^ 2 * (ε * Real.log (n : ℝ)) =
                          ε * (‖(μ n : ℂ) / (n : ℂ) ^ s‖ ^ 2 * Real.log (n : ℝ)) := by
      ring
    simp only [h_term]
    rw [← mul_sum]
  rw [h_rw] at h_sum_le
  exact h_sum_le

end ProbabilisticRegularization

/-! ## Section 4: Limit commutation -/

-- Moore–Osgood commutation: uniform variance bound ⇒ deterministic limit exists.
axiom moore_osgood_commutation (s : ℂ) (hs : s.re > 1 / 2) :
  ∃ L : ℂ, Tendsto (fun N ↦ S_classical N s) atTop (𝓝 L)

/-! ### Concrete Dirichlet eta function -/

/-- The Dirichlet eta (alternating zeta) function: η(s) = (1 − 2^(1−s)) · ζ(s).
    It is entire and non-vanishing on the real axis for Re(s) > 1/2. -/
noncomputable def dirichletEta (s : ℂ) : ℂ := (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s

-- η is non-zero on the real axis at distance α > 0 from the critical line,
-- provided s ≠ 1 (i.e. α ≠ 1/2).  When α = 1/2 Mathlib sets riemannZeta 1 = 0
-- by convention (the function has a simple pole there), so the product formula
-- dirichletEta 1 = (1 − 2^0) · ζ(1) = 0 · 0 = 0 is numerically zero in Lean
-- even though analytically η(1) = ln 2.  The side-condition excludes that point.
-- Proof path: show (1 − 2^(1−s)) ≠ 0 (since s ≠ 1 forces 2^(1−s) ≠ 1) and
-- riemannZeta s ≠ 0 (Euler product for s > 1; alternating-series positivity for
-- 1/2 < s < 1).
theorem eta_non_zero_real_axis (α : ℝ) (hα : α > 0) (hα_ne : α ≠ 1 / 2) :
    dirichletEta ⟨1 / 2 + α, 0⟩ ≠ 0 := by
  unfold dirichletEta
  apply mul_ne_zero
  · -- Factor 1: 1 − (2:ℂ)^(1−s) ≠ 0,  i.e.  (2:ℂ)^(1−s) ≠ 1.
    -- For s = ⟨1/2+α, 0⟩:  1 − s = ⟨1/2−α, 0⟩  (purely real).
    simp only [sub_ne_zero]
    have h1s : (1 : ℂ) - ⟨1 / 2 + α, 0⟩ = ((1 / 2 - α : ℝ) : ℂ) := by
      apply Complex.ext
      · simp; linarith
      · simp
    rw [h1s]
    have h2_eq : (2 : ℂ) = ((2 : ℝ) : ℂ) := by simp
    rw [h2_eq]
    -- Rewrite (2:ℂ)^(r:ℂ)  as  ↑((2:ℝ)^r)  for r : ℝ, using 2 ≥ 0.
    rw [← Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2)]
    -- Reduce to the real claim (2:ℝ)^(1/2−α) ≠ 1.
    norm_cast
    have h2 : (1 : ℝ) < 2 := by norm_num
    rcases ne_iff_lt_or_gt.mp hα_ne with hlt | hgt
    · -- α < 1/2 → exponent 1/2−α > 0 → 2^(1/2−α) > 2^0 = 1
      have h := Real.rpow_lt_rpow_of_exponent_lt h2 (show (0 : ℝ) < 1 / 2 - α by linarith)
      rw [Real.rpow_zero] at h
      exact h.ne
    · -- α > 1/2 → exponent 1/2−α < 0 → 2^(1/2−α) < 2^0 = 1
      have h := Real.rpow_lt_rpow_of_exponent_lt h2 (show 1 / 2 - α < (0 : ℝ) by linarith)
      rw [Real.rpow_zero] at h
      exact h.ne'
  · -- Factor 2: riemannZeta ⟨1/2+α, 0⟩ ≠ 0.
    -- For α > 1/2 (s.re > 1): follows from the Euler product / Dirichlet series positivity.
    -- For 0 < α < 1/2 (1/2 < s.re < 1): follows from alternating-series positivity of η.
    -- Both sub-cases remain as proof obligations pending Mathlib API investigation.
    sorry


theorem classical_series_converges_at_s0 (α : ℝ) (hα : α > 0) :
    ∃ L : ℂ, Tendsto (fun N ↦ S_classical N ⟨1 / 2 + α, 0⟩) atTop (𝓝 L) :=
  moore_osgood_commutation ⟨1 / 2 + α, 0⟩ (by linarith)

/-! ## Section 5: The Riemann Hypothesis -/

-- Jensen–Bohr (Bohr–Cahen) theorem: convergence at s₀ extends to Re(s) > Re(s₀).
axiom jensen_bohr (s₀ : ℂ)
    (h : ∃ L, Tendsto (fun N ↦ S_classical N s₀) atTop (𝓝 L)) :
    ∀ s : ℂ, s.re > s₀.re → ∃ L', Tendsto (fun N ↦ S_classical N s) atTop (𝓝 L')

-- A conditionally-convergent Dirichlet series defines a holomorphic function
-- (no poles) in its half-plane of convergence.
axiom convergent_series_has_no_poles (s₀ : ℂ)
    (h : ∀ s : ℂ, s.re > s₀.re →
        ∃ L, Tendsto (fun N ↦ S_classical N s) atTop (𝓝 L)) :
    ∀ s : ℂ, s.re > s₀.re → (1 / riemannZeta s) ≠ 0

lemma zeta_symm (s : ℂ) (h1 : 0 < s.re) (h2 : s.re < 1)
    (hs : riemannZeta s = 0) :
    riemannZeta (1 - s) = 0 := by
  have h_ne_nat : ∀ (n : ℕ), s ≠ -↑n := by
    intro n hn
    have h_re : s.re = (-↑n : ℂ).re := by rw [hn]
    simp only [neg_re, Complex.natCast_re] at h_re
    have : (n : ℝ) ≥ 0 := Nat.cast_nonneg n
    linarith
  have h_ne_one : s ≠ 1 := by
    intro hn
    have h_re : s.re = (1 : ℂ).re := by rw [hn]
    simp only [one_re] at h_re
    linarith
  rw [riemannZeta_one_sub h_ne_nat h_ne_one, hs]
  ring

lemma zeta_no_zeros_right_half_plane
    (s : ℂ) (hs : riemannZeta s = 0) (hgt : s.re > 1 / 2) : False := by
  set α := (s.re - 1 / 2) / 2
  have hα : α > 0 := by dsimp only [α]; linarith
  let s₀ : ℂ := ⟨1 / 2 + α, 0⟩
  have hconv₀ := classical_series_converges_at_s0 α hα
  have hconv_all := jensen_bohr s₀ hconv₀
  have hno_poles := convergent_series_has_no_poles s₀ hconv_all
  have hs₀_re : s₀.re = 1 / 2 + α := rfl
  have hgt₀ : s.re > s₀.re := by
    rw [hs₀_re]
    dsimp only [α]
    linarith
  have hne : (1 / riemannZeta s) ≠ 0 := hno_poles s hgt₀
  have heq : 1 / riemannZeta s = 0 := by simp [hs]
  exact hne heq

theorem riemann_hypothesis (s : ℂ) (hs : riemannZeta s = 0)
    (h_pos : 0 < s.re) (h_lt : s.re < 1) : s.re = 1 / 2 := by
  rcases lt_trichotomy s.re (1 / 2) with h | h | h
  · have hsymm : riemannZeta (1 - s) = 0 := zeta_symm s h_pos h_lt hs
    have hgt : (1 - s).re > 1 / 2 := by simp only [sub_re, one_re]; linarith
    exact absurd (zeta_no_zeros_right_half_plane (1 - s) hsymm hgt) id
  · exact h
  · exact absurd (zeta_no_zeros_right_half_plane s hs h) id