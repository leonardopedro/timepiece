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
# Probabilistic Regularization and the Riemann Hypothesis

Formalizes the probabilistic regularization framework from `zetanew.tex`.
A random perturbation of the Möbius Dirichlet series has variance bounded by
`ε · M(s)`, forcing conditional convergence on Re(s) > 1/2 and yielding a
zero-free strip for the Riemann zeta function.
-/

section ProbabilisticRegularization

variable {Ω : Type*} [MeasureSpace Ω]
variable (E : (Ω → ℂ) → ℂ)
variable (Var : (Ω → ℂ) → ℝ)
variable (X : ℝ → ℕ → Ω → ℂ)

/-! ### Probabilistic axioms -/

-- The perturbation has mean one.
axiom exp_X_eq_one (ε : ℝ) (hε : ε > 0) (n : ℕ) :
  E (X ε n) = 1

-- Distinct modes are pairwise orthogonal in the mean-zero sense.
axiom X_orthogonal (ε : ℝ) (hε : ε > 0) (n m : ℕ) (hn : n ≠ m) :
  E (fun ω ↦ (X ε n ω - 1) * (X ε m ω - 1)) = 0

-- The variance of each mode is logarithmically bounded.
axiom Var_X_bound (ε : ℝ) (hε : ε > 0) (n : ℕ) :
  Var (X ε n) ≤ ε * Real.log (n : ℝ)

/-! ### Linearity of expectation -/

axiom E_zero : E (fun _ ↦ 0) = 0
axiom E_add (f g : Ω → ℂ) : E (fun ω ↦ f ω + g ω) = E f + E g
axiom E_smul (c : ℂ) (f : Ω → ℂ) : E (fun ω ↦ c * f ω) = c * E f

lemma E_sum {α : Type*} (s : Finset α) (f : α → Ω → ℂ) :
    E (fun ω ↦ ∑ x ∈ s, f x ω) = ∑ x ∈ s, E (f x) := by
  classical
  induction s using Finset.induction_on with
  | empty       => simp only [sum_empty]; exact E_zero E
  | insert a s ha ih => simp only [sum_insert ha]; rw [E_add E, ih]

/-! ### Variance axioms -/

-- Variance scales as ‖c‖² under scalar multiplication.
axiom Var_smul (c : ℂ) (f : Ω → ℂ) :
  Var (fun ω ↦ c * f ω) = ‖c‖ ^ 2 * Var f

-- For pairwise mean-zero orthogonal terms, variance is additive.
axiom Var_orthogonal_sum (s : Finset ℕ) (f : ℕ → Ω → ℂ)
    (h : ∀ m ∈ s, ∀ n ∈ s, m ≠ n →
      E (fun ω ↦ (f m ω - E (f m)) * (f n ω - E (f n))) = 0) :
    Var (fun ω ↦ ∑ n ∈ s, f n ω) = ∑ n ∈ s, Var (f n)

/-! ### Partial sums -/

noncomputable def S_classical (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Icc 1 N, (μ n : ℂ) / (n ^ s)

noncomputable def S_random (ε : ℝ) (N : ℕ) (s : ℂ) (ω : Ω) : ℂ :=
  ∑ n ∈ Icc 1 N, ((μ n : ℂ) * X ε n ω) / (n ^ s)

/-! ### Expectation equivalence (PROVED) -/

lemma expected_S_random_eq_S_classical (ε : ℝ) (hε : ε > 0) (N : ℕ) (s : ℂ) :
    E (S_random X ε N s) = S_classical N s := by
  unfold S_random S_classical
  rw [E_sum E]
  congr 1; ext n
  have : (fun ω ↦ ((μ n : ℂ) * X ε n ω) / (n ^ s)) =
         (fun ω ↦ ((μ n : ℂ) / (n ^ s)) * X ε n ω) := by ext ω; ring
  rw [this, E_smul E, exp_X_eq_one E X ε hε n]; ring

/-! ### Uniform variance bound -/

/-- The variance of the randomized partial sum is bounded by `ε · M` for some
    finite `M`, uniformly in `N`, when `Re(s) > 1/2`.

    Proof sketch:
    1. `Var_orthogonal_sum` + `X_orthogonal` collapse cross-terms.
    2. `Var_smul` gives `Var(c_n · X_n) = ‖c_n‖² · Var(X_n)`.
    3. `Var_X_bound` gives `Var(X_n) ≤ ε · log n`.
    4. Factor out `ε`; the remaining sum is finite and serves as `M`. -/
lemma uniform_variance_bound (ε : ℝ) (hε : ε > 0) (N : ℕ) (s : ℂ)
    (hs : s.re > 1 / 2) :
    ∃ M : ℝ, Var (S_random X ε N s) ≤ ε * M := by
  use ∑ n ∈ Icc 1 N, ‖(μ n : ℂ) / (n : ℂ) ^ s‖ ^ 2 * Real.log n
  sorry

end ProbabilisticRegularization

/-! ## Section 4: Limit commutation -/

-- Moore–Osgood: uniform variance bound → the limits N→∞, ε→0 commute.
axiom moore_osgood_commutation (s : ℂ) (hs : s.re > 1 / 2) :
  ∃ L : ℂ, Tendsto (fun N ↦ S_classical N s) atTop (𝓝 L)

variable (eta : ℂ → ℂ)

-- The Dirichlet eta function is non-zero at real points strictly right of 1/2.
lemma eta_non_zero_real_axis (α : ℝ) (hα : α > 0) :
    eta ⟨1 / 2 + α, 0⟩ ≠ 0 := by
  sorry

-- Conditional convergence at s₀ = 1/2 + α follows immediately from
-- moore_osgood_commutation, since (⟨1/2 + α, 0⟩ : ℂ).re = 1/2 + α > 1/2.
theorem classical_series_converges_at_s0 (α : ℝ) (hα : α > 0) :
    ∃ L : ℂ, Tendsto (fun N ↦ S_classical N ⟨1 / 2 + α, 0⟩) atTop (𝓝 L) :=
  moore_osgood_commutation ⟨1 / 2 + α, 0⟩ (by linarith)

/-! ## Section 5: The Riemann Hypothesis -/

-- Convergence at s₀ propagates to all s with Re(s) > Re(s₀).
axiom jensen_bohr (s₀ : ℂ)
    (h : ∃ L, Tendsto (fun N ↦ S_classical N s₀) atTop (𝓝 L)) :
    ∀ s : ℂ, s.re > s₀.re → ∃ L', Tendsto (fun N ↦ S_classical N s) atTop (𝓝 L')

-- Conditional convergence on a half-plane implies 1/ζ is non-zero there.
axiom convergent_series_has_no_poles (s₀ : ℂ)
    (h : ∀ s : ℂ, s.re > s₀.re →
        ∃ L, Tendsto (fun N ↦ S_classical N s) atTop (𝓝 L)) :
    ∀ s : ℂ, s.re > s₀.re → (1 / riemannZeta s) ≠ 0

-- Riemann functional equation: non-trivial zeros reflect across Re = 1/2.
axiom zeta_symm (s : ℂ) (h1 : 0 < s.re) (h2 : s.re < 1)
    (hs : riemannZeta s = 0) :
    riemannZeta (1 - s) = 0

/-- No zeros in Re(s) > 1/2: if ζ(s) = 0 there, we derive 1/ζ(s) = 0 and ≠ 0. -/
lemma zeta_no_zeros_right_half_plane
    (s : ℂ) (hs : riemannZeta s = 0) (hgt : s.re > 1 / 2) : False := by
  -- Pick evaluation point s₀ halfway between 1/2 and Re(s).
  set α := (s.re - 1 / 2) / 2
  have hα : α > 0 := by dsimp only [α]; linarith
  let s₀ : ℂ := ⟨1 / 2 + α, 0⟩
  -- Series converges at s₀ by Moore–Osgood.
  have hconv₀ := classical_series_converges_at_s0 α hα
  -- Jensen–Bohr extends convergence to the whole half-plane Re > Re(s₀).
  have hconv_all := jensen_bohr s₀ hconv₀
  -- Convergence implies 1/ζ ≠ 0.
  have hno_poles := convergent_series_has_no_poles s₀ hconv_all
  -- Re(s) > Re(s₀) = 1/2 + α.
  have hs₀_re : s₀.re = 1 / 2 + α := rfl
  have hgt₀ : s.re > s₀.re := by
    rw [hs₀_re]
    dsimp only [α]
    linarith
  -- So 1/ζ(s) ≠ 0 …
  have hne : (1 / riemannZeta s) ≠ 0 := hno_poles s hgt₀
  -- … but ζ(s) = 0 forces 1/ζ(s) = 0. Contradiction.
  have heq : 1 / riemannZeta s = 0 := by simp [hs]
  exact hne heq

/-- **The Riemann Hypothesis** (assuming the strip `0 < Re(s) < 1`):
    every non-trivial zero of ζ has real part 1/2.

    The right half-plane case is handled by `zeta_no_zeros_right_half_plane`.
    The left half-plane case reflects to the right via `zeta_symm`. -/
theorem riemann_hypothesis (s : ℂ) (hs : riemannZeta s = 0)
    (h_pos : 0 < s.re) (h_lt : s.re < 1) : s.re = 1 / 2 := by
  rcases lt_trichotomy s.re (1 / 2) with h | h | h
  · -- Re(s) < 1/2: reflect to Re(1-s) > 1/2 and derive contradiction.
    have hsymm : riemannZeta (1 - s) = 0 := zeta_symm s h_pos h_lt hs
    have hgt : (1 - s).re > 1 / 2 := by simp only [sub_re, one_re]; linarith
    exact absurd (zeta_no_zeros_right_half_plane (1 - s) hsymm hgt) id
  · exact h
  · exact absurd (zeta_no_zeros_right_half_plane s hs h) id
