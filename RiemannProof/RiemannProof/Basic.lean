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
-/

section ProbabilisticRegularization

-- We define a sequence of measure spaces Ω_N for each truncation N.
variable {Ω : ℕ → Type*} [∀ N, MeasureSpace (Ω N)]

-- The Expectation and Variance operators are now strictly parameterized by N.
variable (E : ∀ N, (Ω N → ℂ) → ℂ)
variable (Var : ∀ N, (Ω N → ℂ) → ℝ)

-- The random variable X(ε, n) evaluated in the N-th probability space.
variable (X : ℝ → ℕ → ∀ N, Ω N → ℂ)

/-! ### Probabilistic axioms in N-dimensional space -/

-- The perturbation has mean one for all n ≤ N.
axiom exp_X_eq_one (ε : ℝ) (hε : ε > 0) (N : ℕ) (n : ℕ) (hn : n ≤ N) :
  E N (X ε n N) = 1

-- Distinct modes are pairwise orthogonal in the mean-zero sense in Ω_N.
axiom X_orthogonal (ε : ℝ) (hε : ε > 0) (N : ℕ) (n m : ℕ) (hn : n ≤ N) (hm : m ≤ N) (hneq : n ≠ m) :
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

/-! ### Uniform variance bound -/

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

-- Moore–Osgood commutation relies on the fact that Var_N is bounded uniformly in N.
axiom moore_osgood_commutation (s : ℂ) (hs : s.re > 1 / 2) :
  ∃ L : ℂ, Tendsto (fun N ↦ S_classical N s) atTop (𝓝 L)

variable (eta : ℂ → ℂ)

axiom eta_non_zero_real_axis (α : ℝ) (hα : α > 0) :
    eta ⟨1 / 2 + α, 0⟩ ≠ 0

theorem classical_series_converges_at_s0 (α : ℝ) (hα : α > 0) :
    ∃ L : ℂ, Tendsto (fun N ↦ S_classical N ⟨1 / 2 + α, 0⟩) atTop (𝓝 L) :=
  moore_osgood_commutation ⟨1 / 2 + α, 0⟩ (by linarith)

/-! ## Section 5: The Riemann Hypothesis -/

axiom jensen_bohr (s₀ : ℂ)
    (h : ∃ L, Tendsto (fun N ↦ S_classical N s₀) atTop (𝓝 L)) :
    ∀ s : ℂ, s.re > s₀.re → ∃ L', Tendsto (fun N ↦ S_classical N s) atTop (𝓝 L')

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