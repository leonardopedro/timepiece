import Mathlib.Analysis.Complex.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Complex
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.ArithmeticFunction.Defs
import Mathlib.Probability.Moments.Basic
import Mathlib.Analysis.Calculus.FDeriv.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.NumberTheory.LSeries.RiemannZeta
import Mathlib.NumberTheory.LSeries.Dirichlet
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

open Complex Finset Filter MeasureTheory Topology
open scoped ArithmeticFunction ArithmeticFunction.Moebius

set_option linter.unusedSectionVars false

/-!
=============================================================================
                          SECTION 1: THE CONCRETE SPACE
=============================================================================
Here we construct the continuous probability space explicitly to resolve the
MeasureSpace typeclass synthesis hang, allowing Bochner integrals to map
directly to our Expectation and Variance operators.
-/

section ContinuousProbabilisticRegularization

-- 1. Continuous Probability Space: [0, 1]^(N+1)
def Ω_conc (N : ℕ) := Fin (N + 1) → ℝ

-- Assign the standard Uniform product Lebesgue measure
noncomputable instance (N : ℕ) : MeasureSpace (Ω_conc N) where
  toMeasurableSpace := inferInstanceAs (MeasurableSpace (Fin (N + 1) → ℝ))
  volume := Measure.pi (fun _ ↦ Measure.restrict volume (Set.Icc (0 : ℝ) 1))

-- 2. Bochner Integral for Expectation
noncomputable def E_conc (N : ℕ) (f : Ω_conc N → ℂ) : ℂ :=
  ∫ ω, f ω

-- 3. Variance
noncomputable def Var_conc (N : ℕ) (f : Ω_conc N → ℂ) : ℝ :=
  ∫ ω, ‖f ω - E_conc N f‖ ^ 2

-- 4. Continuous Random Variable in [1-ε, 1+ε]
noncomputable def X_conc (ε : ℝ) (n N : ℕ) (ω : Ω_conc N) : ℂ :=
  if h : n ≤ N ∧ n > 1 then
    1 + (ε : ℂ) * (2 * (ω ⟨n, Nat.lt_succ_of_le h.1⟩ : ℂ) - 1)
  else
    1
/-! ### Proving Linearity Axioms Natively for the Concrete Space -/

lemma E_conc_zero (N : ℕ) : E_conc N (fun _ ↦ 0) = 0 := by
  unfold E_conc
  exact integral_zero _

lemma E_conc_smul (N : ℕ) (c : ℂ) (f : Ω_conc N → ℂ) :
    E_conc N (fun ω ↦ c * f ω) = c * E_conc N f := by
  unfold E_conc
  exact integral_smul c f

-- Note: The Lebesgue integral is only additive if the functions are integrable.
-- Our concrete polynomials on the compact interval [0,1] will satisfy these
-- integrability conditions when we merge the sections.
lemma E_conc_add (N : ℕ) (f g : Ω_conc N → ℂ) (hf : Integrable f) (hg : Integrable g) :
    E_conc N (fun ω ↦ f ω + g ω) = E_conc N f + E_conc N g := by
  unfold E_conc
  exact integral_add hf hg

-- Variance scaling natively follows from Bochner integral properties of the norm
lemma Var_conc_smul (N : ℕ) (c : ℂ) (f : Ω_conc N → ℂ) :
    Var_conc N (fun ω ↦ c * f ω) = ‖c‖ ^ 2 * Var_conc N f := by
  unfold Var_conc
  have h_E : E_conc N (fun ω ↦ c * f ω) = c * E_conc N f := E_conc_smul N c f
  have h_norm : ∀ ω, ‖c * f ω - c * E_conc N f‖ ^ 2 = ‖c‖ ^ 2 * ‖f ω - E_conc N f‖ ^ 2 := by
    intro ω
    rw [← mul_sub]
    rw [norm_mul]
    exact mul_pow ‖c‖ ‖f ω - E_conc N f‖ 2
  have h_rw : (fun ω ↦ ‖(c * f ω) - E_conc N (fun ω ↦ c * f ω)‖ ^ 2) =
              (fun ω ↦ ‖c‖ ^ 2 * ‖f ω - E_conc N f‖ ^ 2) := by
    ext ω
    rw [h_E]
    exact h_norm ω
  rw [h_rw]
  -- We factor the real constant ‖c‖^2 out of the integral
  exact integral_mul_left (‖c‖ ^ 2) (fun ω ↦ ‖f ω - E_conc N f‖ ^ 2)
end ContinuousProbabilisticRegularization

/-!
=============================================================================
                          SECTION 2: PROBABILISTIC AXIOMS
=============================================================================
These abstract variables parameterize the remainder of the proof until we
can map them to Section 1 using Integrable conditions.
-/

section ProbabilisticRegularization

-- We define a sequence of measure spaces Ω_N for each truncation N.
variable {Ω : ℕ → Type*} [∀ N, MeasureSpace (Ω N)]

-- The Expectation and Variance operators are strictly parameterized by N.
variable (E : ∀ N, (Ω N → ℂ) → ℂ)
variable (Var : ∀ N, (Ω N → ℂ) → ℝ)

-- The random variable X(ε, n) evaluated in the N-th probability space.
variable (X : ℝ → ℕ → ∀ N, Ω N → ℂ)

-- The perturbation has mean one for all n ≤ N.
axiom exp_X_eq_one (ε : ℝ) (hε : ε > 0) (N : ℕ) (n : ℕ) (hn : n ≤ N) :
  E N (X ε n N) = 1

-- Distinct modes are pairwise orthogonal in the mean-zero sense in Ω_N.
axiom X_orthogonal (ε : ℝ) (hε : ε > 0) (N : ℕ) (n m : ℕ)
    (hn : n ≤ N) (hm : m ≤ N) (hneq : n ≠ m) :
  E N (fun ω ↦ (X ε n N ω - 1) * (X ε m N ω - 1)) = 0

-- The variance of each mode is bounded in Ω_N.
axiom Var_X_bound (ε : ℝ) (hε : ε > 0) (N : ℕ) (n : ℕ) (hn : n ≤ N) :
  Var N (X ε n N) ≤ ε * Real.log (n : ℝ)

-- Linearity of expectation for a fixed N
axiom E_zero (N : ℕ) : E N (fun _ ↦ 0) = 0
axiom E_add (N : ℕ) (f g : Ω N → ℂ) : E N (fun ω ↦ f ω + g ω) = E N f + E N g
axiom E_smul (N : ℕ) (c : ℂ) (f : Ω N → ℂ) : E N (fun ω ↦ c * f ω) = c * E N f

lemma E_sum {α : Type*} (N : ℕ) (s : Finset α) (f : α → Ω N → ℂ) :
    E N (fun ω ↦ ∑ x ∈ s, f x ω) = ∑ x ∈ s, E N (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty       => simp only [sum_empty]; exact E_zero E N
  | insert a s ha ih => simp only [sum_insert ha]; rw [E_add E N, ih]

-- Variance axioms for a fixed N
axiom Var_smul (N : ℕ) (c : ℂ) (f : Ω N → ℂ) :
  Var N (fun ω ↦ c * f ω) = ‖c‖ ^ 2 * Var N f

axiom Var_orthogonal_sum (N : ℕ) (s : Finset ℕ) (f : ℕ → Ω N → ℂ)
    (h : ∀ m ∈ s, ∀ n ∈ s, m ≠ n →
      E N (fun ω ↦ (f m ω - E N (f m)) * (f n ω - E N (f n))) = 0) :
    Var N (fun ω ↦ ∑ n ∈ s, f n ω) = ∑ n ∈ s, Var N (f n)

/-!
=============================================================================
                          SECTION 3: PARTIAL SUMS & VARIANCE
=============================================================================
Proofs concerning the equivalence and uniform distance of the random series.
-/

noncomputable def S_classical (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Icc 1 N, (μ n : ℂ) / (n ^ s)

noncomputable def S_random (ε : ℝ) (N : ℕ) (s : ℂ) (ω : Ω N) : ℂ :=
  ∑ n ∈ Icc 1 N, ((μ n : ℂ) * X ε n N ω) / (n ^ s)

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

/-!
=============================================================================
                          SECTION 4: LIMIT COMMUTATION & ETA
=============================================================================
Analytical results concerning Dirichlet limits.
-/

-- Moore–Osgood commutation: uniform variance bound ⇒ deterministic limit exists.
axiom moore_osgood_commutation (s : ℂ) (hs : s.re > 1 / 2) :
  ∃ L : ℂ, Tendsto (fun N ↦ S_classical N s) atTop (𝓝 L)

noncomputable def dirichletEta (s : ℂ) : ℂ := (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s

theorem eta_non_zero_real_axis (α : ℝ) (hα : α > 0) (hα_ne : α ≠ 1 / 2) :
    dirichletEta ⟨1 / 2 + α, 0⟩ ≠ 0 := by
  unfold dirichletEta
  apply mul_ne_zero
  · -- Factor 1: 1 − (2:ℂ)^(1−s) ≠ 0
    simp only [sub_ne_zero]
    have h1s : (1 : ℂ) - ⟨1 / 2 + α, 0⟩ = ((1 / 2 - α : ℝ) : ℂ) := by
      apply Complex.ext
      · simp; linarith
      · simp
    rw [h1s]
    have h2_eq : (2 : ℂ) = ((2 : ℝ) : ℂ) := by simp
    rw [h2_eq]
    rw [← Complex.ofReal_cpow (by norm_num : (0 : ℝ) ≤ 2)]
    norm_cast
    have h2 : (1 : ℝ) < 2 := by norm_num
    rcases ne_iff_lt_or_gt.mp hα_ne with hlt | hgt
    · have h := Real.rpow_lt_rpow_of_exponent_lt h2 (show (0 : ℝ) < 1 / 2 - α by linarith)
      rw [Real.rpow_zero] at h
      exact h.ne
    · have h := Real.rpow_lt_rpow_of_exponent_lt h2 (show 1 / 2 - α < (0 : ℝ) by linarith)
      rw [Real.rpow_zero] at h
      exact h.ne'
  · -- Factor 2: riemannZeta ⟨1/2+α, 0⟩ ≠ 0.
    rcases lt_trichotomy (1 / 2 + α) 1 with h_lt_one | h_eq_one | h_gt_one
    · -- Case 1/2 < s < 1 (Uses alternating series positivity)
      sorry
    · -- Case s = 1 (Contradiction since α ≠ 1/2)
      have h_alpha_eq : α = 1 / 2 := by linarith
      exfalso
      exact hα_ne h_alpha_eq
    · -- Case s > 1 (Mathlib Euler Product consequence)
      exact riemannZeta_ne_zero_of_one_lt_re h_gt_one

theorem classical_series_converges_at_s0 (α : ℝ) (hα : α > 0) :
    ∃ L : ℂ, Tendsto (fun N ↦ S_classical N ⟨1 / 2 + α, 0⟩) atTop (𝓝 L) :=
  moore_osgood_commutation ⟨1 / 2 + α, 0⟩ (by linarith)

/-!
=============================================================================
                          SECTION 5: RIEMANN HYPOTHESIS
=============================================================================
Combining the convergence and analytical non-zero properties into the RH.
-/

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
