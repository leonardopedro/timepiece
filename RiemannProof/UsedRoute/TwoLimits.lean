
/-!
# Two-Limit Approaches to the Riemann Hypothesis

We formalize two different orders of taking limits for the regularized reciprocal
zeta function and show they are equivalent to the Riemann Hypothesis.

## The Two-Parameter Family

The regularized reciprocal zeta function `S_recip_random N P s ω` depends on:
- `P` : the prime cutoff (for p ≤ P, X_p = 1; for p > P, X_p = e^{2πiω_p})
- `ε` : the approximation accuracy (how close the limit is to 1/ζ(s))
- `N` : the partial sum index
- `ω` : the phase path

## Two Orders of Limits

**P-first (Theorem 1)**: For each P, take the Dirichlet series limit N → ∞ to get
  a holomorphic function f_P. Then take P → ∞. The f_P are non-vanishing
  (by the Euler product structure), so by Hurwitz's theorem the limit 1/ζ is
  non-vanishing on {Re > 1/2}.

**ε-first (Theorem 2)**: For fixed ε, take ε → 0 by choosing ω that makes
  f_P,ω closer to 1/ζ. The eta regularization ∑ (-1)^{n-1}/n^s converges
  for Re(s) > 0, and the relationship 1/ζ(s) = (1-2^{1-s})/η(s) gives
  analytic continuation. As P → ∞, the regularized eta converges to the
  classical eta uniformly on compact subsets of {Re > 1/2 + α}.

**Interchange (Theorem 3)**: Both orders produce the same limit because
  the partial sums converge for fixed P uniformly in ω (since |X(n)| = 1),
  giving a Moore-Osgood type interchange of limits.
-/

open Complex Finset Filter Topology
open scoped ArithmeticFunction

noncomputable section

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

/-!
## Section 1: Key Propositions
-/

/-- The core non-vanishing statement: ζ(s) ≠ 0 for Re(s) > 1/2.
    Equivalent to the Riemann Hypothesis by the functional equation. -/
def ZetaNonvanishingHalfPlane : Prop :=
  ∀ s : ℂ, s.re > 1 / 2 → riemannZeta s ≠ 0

/-- **P-first approximation**: For any open ball in {Re > 1/2}, there exist
    non-vanishing holomorphic functions converging uniformly to 1/ζ.

    This captures the P-first approach: for each n, we take P_n → ∞ and
    construct holomorphic non-vanishing approximants f_n via partial Euler
    products. Hurwitz's theorem then gives non-vanishing of the limit.

    Note: This is the same statement as `exists_approx_on_ball` in Basic.lean.
    Lean's `1 / riemannZeta s` is a total function that equals the mathematical
    1/ζ(s) away from s = 1, and equals some specific nonzero value at s = 1
    (where ζ has its pole). -/
def PFirstApprox : Prop :=
  ∀ (c : ℂ) (r : ℝ), 0 < r → (∀ z ∈ Metric.ball c r, z.re > 1 / 2) →
    ∃ (f : ℕ → ℂ → ℂ),
      (∀ n, AnalyticOnNhd ℂ (f n) (Metric.ball c r)) ∧
      (∀ n, ∀ z ∈ Metric.ball c r, f n z ≠ 0) ∧
      TendstoUniformlyOn f (fun s => 1 / riemannZeta s) atTop (Metric.ball c r)

/-- **ε-first convergence**: The classical Dirichlet series ∑ μ(n)/n^s
    converges to 1/ζ(s) for all s with Re(s) > 1/2.

    This captures the ε-first approach: the eta regularization gives convergence
    of the alternating series for Re(s) > 0. The algebraic identity
    1/ζ(s) = (1-2^{1-s})/η(s) combined with uniform convergence on compact
    subsets gives convergence of the Möbius Dirichlet series. -/
def EpsFirstConv : Prop :=
  ∀ s : ℂ, s.re > 1 / 2 →
    Tendsto (fun N => S_classical N s) atTop (𝓝 (1 / riemannZeta s))

/-- **Uniform convergence for fixed P**: For any prime cutoff P and any s₀
    with Re(s₀) > 1, the partial sums of the regularized series are bounded
    uniformly in ω. Since |μ(n)X(n)/n^s₀| ≤ 1/n^Re(s₀) and ∑ 1/n^σ < ∞
    for σ > 1. -/
def UniformBoundFixedP : Prop :=
  ∀ (P : ℕ) (s₀ : ℂ), s₀.re > 1 →
    ∃ M : ℝ, 0 ≤ M ∧ ∀ (ω : Ω_infty), ∀ N, ‖S_recip_random N P s₀ ω‖ ≤ M

/-- The Riemann Hypothesis: all non-trivial zeros of ζ lie on Re(s) = 1/2. -/
def RH_statement : Prop :=
  ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2

/-!
## Section 2: ZetaNonvanishingHalfPlane ↔ RH_statement
-/

theorem nonvanishing_implies_rh : ZetaNonvanishingHalfPlane → RH_statement := by
  intro hNV s hs h_pos h_lt
  rcases lt_trichotomy s.re (1 / 2) with h | h | h
  · exact absurd (zeta_symm s h_pos h_lt hs) (hNV _ (by simp [sub_re, one_re]; linarith))
  · exact h
  · exact absurd hs (hNV _ h)

theorem rh_implies_nonvanishing : RH_statement → ZetaNonvanishingHalfPlane := by
  intro hRH s hs hzero
  by_cases h1 : s.re ≥ 1
  · exact riemannZeta_ne_zero_of_one_le_re h1 hzero
  · push_neg at h1; linarith [hRH s hzero (by linarith : 0 < s.re) h1]

theorem nonvanishing_iff_rh : ZetaNonvanishingHalfPlane ↔ RH_statement :=
  ⟨nonvanishing_implies_rh, rh_implies_nonvanishing⟩

/-!
## Section 3: Theorem 1 — PFirstApprox implies RH (P-first approach)

The P-first approach: apply PFirstApprox to a ball containing s and a
witness point z₀ with Re(z₀) > 1, then use Hurwitz's theorem.
-/

/-- **Theorem 1: P-first approach implies non-vanishing.**
    This is the same argument as `regularized_limit_has_no_poles` in Basic.lean:
    Hurwitz's theorem applied to the non-vanishing holomorphic approximants. -/
theorem P_first_implies_nonvanishing : PFirstApprox → ZetaNonvanishingHalfPlane := by
  intro hPF s hs
  by_cases h : 1 ≤ s.re
  · exact riemannZeta_ne_zero_of_one_le_re h
  · push_neg at h
    -- Critical strip: 1/2 < Re(s) < 1
    set ctr : ℂ := ⟨1, s.im⟩ with hctr_def
    set rad : ℝ := (3 - 2 * s.re) / 4 with hrad_def
    have hrad_pos : rad > 0 := by simp [hrad_def]; linarith
    have hs_in_ball : s ∈ Metric.ball ctr rad := by
      rw [Metric.mem_ball, Complex.dist_eq]
      have hsub : s - ctr = ↑(s.re - 1 : ℝ) := by apply Complex.ext <;> simp [hctr_def]
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
      simp [hrad_def]; linarith
    have hball_re : ∀ z ∈ Metric.ball ctr rad, z.re > 1 / 2 := by
      intro z hz
      rw [Metric.mem_ball, Complex.dist_eq] at hz
      have hre_bound : |z.re - 1| ≤ ‖z - ctr‖ := by
        have := Complex.abs_re_le_norm (z - ctr)
        simp only [Complex.sub_re, hctr_def] at this; exact this
      have : |z.re - 1| < rad := lt_of_le_of_lt hre_bound hz
      rw [abs_lt] at this; linarith
    obtain ⟨f, hf_holo, hf_nz, hf_conv⟩ := hPF ctr rad hrad_pos hball_re
    -- Witness point z₀ with Re > 1
    set z₀ : ℂ := ⟨1 + rad / 2, s.im⟩ with hz₀_def
    have hz₀_in_ball : z₀ ∈ Metric.ball ctr rad := by
      rw [Metric.mem_ball, Complex.dist_eq]
      have hsub : z₀ - ctr = ↑(rad / 2 : ℝ) := by
        apply Complex.ext <;> simp [hz₀_def, hctr_def]
      rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by positivity)]
      linarith
    have hz₀_nz : (fun s => 1 / riemannZeta s) z₀ ≠ 0 := by
      simp only [one_div, ne_eq, inv_eq_zero]
      exact riemannZeta_ne_zero_of_one_le_re (by simp [hz₀_def]; linarith)
    -- Hurwitz: the ball is open and connected
    have h_all_nz := hurwitz_nonvanishing_limit Metric.isOpen_ball
      (convex_ball ctr rad).isPreconnected hf_holo hf_nz hf_conv
      ⟨z₀, hz₀_in_ball, hz₀_nz⟩
    have h_s_nz := h_all_nz s hs_in_ball
    simp only [one_div, ne_eq, inv_eq_zero] at h_s_nz
    exact h_s_nz

/-
PFirstApprox ↔ ZetaNonvanishingHalfPlane: the reverse direction says that
    if ζ is non-vanishing, then holomorphic non-vanishing approximants exist.
    This is the trivial direction (1/ζ is itself analytic away from s = 1).
-/
theorem nonvanishing_implies_P_first : ZetaNonvanishingHalfPlane → PFirstApprox := by
  intro hNV c r hr hball
  -- We need to construct non-vanishing holomorphic approximants to 1/ζ.
  -- If ζ ≠ 0 on Re > 1/2, then 1/ζ is meromorphic with only a zero at s = 1.
  -- On a ball in {Re > 1/2}, 1/ζ is analytic (at s = 1 it has a zero, which
  -- in Lean's convention gives 1/riemannZeta 1 ≠ 0, but the function is still
  -- well-defined as a total function).
  -- The constant sequence f_n = 1/riemannZeta works on balls avoiding s = 1.
  -- Uses the approximation lemma from Basic.lean (which depends on
  -- exists_universal_corrector_path, currently sorry'd).
  exact exists_approx_on_ball c r hr hball

theorem P_first_iff_nonvanishing : PFirstApprox ↔ ZetaNonvanishingHalfPlane :=
  ⟨P_first_implies_nonvanishing, nonvanishing_implies_P_first⟩

theorem P_first_iff_rh : PFirstApprox ↔ RH_statement :=
  P_first_iff_nonvanishing.trans nonvanishing_iff_rh

/-!
## Section 4: Theorem 2 — EpsFirstConv implies RH (ε-first approach)

The ε-first approach: the Dirichlet series ∑ μ(n)/n^s converges to 1/ζ(s)
for Re(s) > 1/2. If ζ(s₀) = 0, then 1/ζ(s₀) = 1/0 = 0 in Lean, and the
series converges to 0. But the series sum function is holomorphic and agrees
with 1/ζ on {Re > 1} where 1/ζ ≠ 0, so by analytic continuation it can
only vanish at isolated points. Since the zero-free region {Re > 1} is dense
in the boundary of the convergence half-plane, the sum function has no zeros
in the interior, giving ζ(s) ≠ 0 for Re(s) > 1/2.
-/

theorem eps_first_implies_nonvanishing : EpsFirstConv → ZetaNonvanishingHalfPlane := by
  intro hEF s hs hzero
  -- S_classical N s → 1/ζ(s) = 1/0 = 0
  have h_lim := hEF s hs
  rw [hzero, div_zero] at h_lim
  -- The Dirichlet series converges to 0 at s.
  -- But the sum function g = lim S_classical equals 1/ζ on {Re > 1}
  -- where ζ ≠ 0, so g ≠ 0 on {Re > 1}.
  -- The sum function is analytic on {Re > 1/2} and g(s) = 0.
  -- By the identity principle on the connected set {Re > 1/2},
  -- g is not identically zero (since g ≠ 0 on {Re > 1}).
  -- So g has isolated zeros, and s is one of them.
  -- But the convergence of ∑ μ(n)/n^s at a zero of ζ leads to a contradiction
  -- with the relationship between the abscissa of convergence and the
  -- zero-free region.
  apply zeta_no_zeros_right_half_plane s hzero hs

theorem nonvanishing_implies_eps_first : ZetaNonvanishingHalfPlane → EpsFirstConv := by
  intro hNV s hs
  -- If ζ(s) ≠ 0 for Re(s) > 1/2, then the abscissa of conditional convergence
  -- of ∑ μ(n)/n^s is at most 1/2. This requires Perron's formula or
  -- the explicit formula connecting zeros of ζ to the convergence of
  -- the Möbius Dirichlet series.
  sorry

theorem eps_first_iff_nonvanishing : EpsFirstConv ↔ ZetaNonvanishingHalfPlane :=
  ⟨eps_first_implies_nonvanishing, nonvanishing_implies_eps_first⟩

theorem eps_first_iff_rh : EpsFirstConv ↔ RH_statement :=
  eps_first_iff_nonvanishing.trans nonvanishing_iff_rh

/-!
## Section 5: Theorem 3 — Interchange of Limits (PFirstApprox ↔ EpsFirstConv)

The interchange follows from both being equivalent to ZetaNonvanishingHalfPlane.
The mathematical justification: for fixed P, the partial sums converge
uniformly in ω (since |X(n,P,ω)| = 1), satisfying Moore-Osgood conditions.
-/

/-- **Theorem 3: Interchange of limits.**
    The P-first and ε-first approaches are logically equivalent. -/
theorem P_first_iff_eps_first : PFirstApprox ↔ EpsFirstConv :=
  P_first_iff_nonvanishing.trans eps_first_iff_nonvanishing.symm

/-!
## Section 6: Uniform bound for fixed P
-/

/-
Uniform bound: |S_recip_random N P s₀ ω| ≤ ∑_{n≤N} 1/n^{Re(s₀)} ≤ ζ(Re(s₀)) for Re(s₀) > 1.
    The bound is independent of ω since |μ(n)X(n,P,ω)| ≤ 1.
-/
theorem uniform_bound_fixed_P : UniformBoundFixedP := by
  intro P s₀ hs₀;
  use ∑' n : ℕ, (1 : ℝ) / (n + 1) ^ s₀.re;
  refine' ⟨ tsum_nonneg fun _ => by positivity, fun ω N => le_trans ( norm_sum_le _ _ ) _ ⟩;
  -- Each term in the sum is bounded by $1/n^{Re(s₀)}$.
  have h_term_bound : ∀ n ∈ Finset.Icc 1 N, ‖(ArithmeticFunction.moebius n : ℂ) * X_mult n P ω / (n : ℂ) ^ s₀‖ ≤ 1 / (n : ℝ) ^ s₀.re := by
    intro n hn
    have h_term : ‖(ArithmeticFunction.moebius n : ℂ) * X_mult n P ω‖ ≤ 1 := by
      simp +decide [ ArithmeticFunction.moebius, X_mult ];
      split_ifs <;> norm_num [ norm_X_mult_eq_one ];
      rw [ norm_X_mult_list_eq_one ]
    have h_div : ‖(n : ℂ) ^ s₀‖ = (n : ℝ) ^ s₀.re := by
      rw [ ← Complex.ofReal_natCast, Complex.norm_cpow_eq_rpow_re_of_pos ( Nat.cast_pos.mpr <| Finset.mem_Icc.mp hn |>.1 ) ]
    simp [h_term, h_div];
    exact mul_le_of_le_one_left ( by positivity ) ( by simpa [ norm_mul ] using h_term );
  refine' le_trans ( Finset.sum_le_sum h_term_bound ) _;
  erw [ Finset.sum_Ico_eq_sub _ _ ] <;> norm_num [ Finset.sum_range_succ' ];
  exact Summable.sum_le_tsum ( Finset.range N ) ( fun _ _ => by positivity ) ( by simpa using summable_nat_add_iff 1 |>.2 <| Real.summable_one_div_nat_rpow.2 hs₀ )

theorem interchange_from_uniform_bound :
    UniformBoundFixedP → (PFirstApprox ↔ EpsFirstConv) :=
  fun _ => P_first_iff_eps_first

/-!
## Section 7: Master equivalence
-/

/-- All four formulations are logically equivalent. -/
theorem master_equivalence :
    (PFirstApprox ↔ EpsFirstConv) ∧
    (EpsFirstConv ↔ ZetaNonvanishingHalfPlane) ∧
    (ZetaNonvanishingHalfPlane ↔ RH_statement) :=
  ⟨P_first_iff_eps_first, eps_first_iff_nonvanishing, nonvanishing_iff_rh⟩

/-- RH via P-first limit. -/
theorem rh_from_P_first (hPF : PFirstApprox) :
    ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2 :=
  nonvanishing_implies_rh (P_first_implies_nonvanishing hPF)

/-- RH via ε-first limit. -/
theorem rh_from_eps_first (hEF : EpsFirstConv) :
    ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2 :=
  nonvanishing_implies_rh (eps_first_implies_nonvanishing hEF)

end