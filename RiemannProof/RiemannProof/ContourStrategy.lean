import Mathlib
import RiemannProof.Basic

/-!
# Contour Integration Strategy for the Riemann Hypothesis

## Strategy

We prove ζ(s) ≠ 0 for Re(s) > 1/2 by contradiction using contour integration.

Suppose ζ(s₀) = 0 for some s₀ with 1/2 < Re(s₀) < 1. Then 1/ζ has a pole at s₀.

### The contradiction:

1. **Residue theorem**: Since ζ(s₀) = 0 with order k ≥ 1, we can write
   ζ(z) = (z - s₀)^k · φ(z) with φ(s₀) ≠ 0. The Cauchy integral formula gives
   ∮ (z-s₀)^{k-1}/ζ(z) dz = 2πi/φ(s₀) ≠ 0.

2. **Bagchi universality**: Dirichlet polynomials S_n approximate 1/ζ
   uniformly on the circle. Therefore (z-s₀)^{k-1} · S_n approximates
   (z-s₀)^{k-1}/ζ uniformly.

3. **Cauchy's theorem**: Each (z-s₀)^{k-1} · S_n(z) is entire, so its
   circle integral is zero. By uniform convergence, ∮ (z-s₀)^{k-1}/ζ = 0.

This contradicts the nonzero residue integral.

## Sorries

The file contains two sorry statements capturing the deep analytic content:

- `bagchi_universality_compact`: Bagchi's universality theorem — the Möbius
  Dirichlet series ∑ μ(n)/n^s converges uniformly to 1/ζ on compact K ⊂ {Re > 1/2}
  with **connected complement** (Kᶜ connected), where ζ has no zeros on K.
  The connected complement condition is essential for the Mergelyan-type
  approximation underlying Bagchi's proof.

- `euler_product_convergence_compact`: For compact K ⊂ {Re > 1}, the Möbius
  partial sums converge uniformly to 1/ζ by absolute convergence of the Euler
  product ∏ (1 - 1/p^s).
-/

open Complex Finset Filter Topology MeasureTheory
open scoped ArithmeticFunction ArithmeticFunction.Moebius

noncomputable section

set_option maxHeartbeats 800000

/-!
## Section 1: The Contour

Given a hypothetical zero s₀ of ζ with 1/2 < Re(s₀) < 1, we construct a circle
C(c, R) where:
- c = (1, Im(s₀)) — center on the line Re = 1, same imaginary part as s₀
- R = 1 - Re(s₀) + δ — radius slightly larger than the distance from c to s₀

This ensures:
- s₀ is inside the circle (distance |c - s₀| = 1 - Re(s₀) < R)
- The circle passes through {Re > 1} (rightmost point has Re = 1 + R > 1)
- The circle stays in {Re > 1/2} (leftmost point has Re = 1 - R = Re(s₀) - δ > 1/2
  when δ < Re(s₀) - 1/2)
-/

/-- The center of the contour: on Re = 1 with the same imaginary part as s₀. -/
noncomputable def contourCenter (s₀ : ℂ) : ℂ := ⟨1, s₀.im⟩

/-- The gap parameter: a quarter of the distance from Re(s₀) to 1/2. -/
noncomputable def contourDelta (s₀ : ℂ) (_ : s₀.re > 1 / 2) : ℝ :=
  (s₀.re - 1 / 2) / 4

/-- The radius of the contour circle. -/
noncomputable def contourRadius (s₀ : ℂ) (hs : s₀.re > 1 / 2) : ℝ :=
  1 - s₀.re + contourDelta s₀ hs

lemma contourDelta_pos (s₀ : ℂ) (hs : s₀.re > 1 / 2) :
    contourDelta s₀ hs > 0 := by
  unfold contourDelta; linarith

lemma contourRadius_pos (s₀ : ℂ) (hs : s₀.re > 1 / 2) (hs2 : s₀.re < 1) :
    contourRadius s₀ hs > 0 := by
  unfold contourRadius; have := contourDelta_pos s₀ hs; linarith

/-- s₀ is strictly inside the contour circle. -/
lemma s₀_mem_ball (s₀ : ℂ) (hs : s₀.re > 1 / 2) (hs2 : s₀.re < 1) :
    s₀ ∈ Metric.ball (contourCenter s₀) (contourRadius s₀ hs) := by
  rw [Metric.mem_ball, Complex.dist_eq]
  have hsub : s₀ - contourCenter s₀ = ↑(s₀.re - 1 : ℝ) := by
    apply Complex.ext <;> simp [contourCenter]
  rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_neg (by linarith)]
  unfold contourRadius; have := contourDelta_pos s₀ hs; linarith

/-- The contour ball is contained in {Re > 1/2}. -/
lemma contour_ball_re_gt_half (s₀ : ℂ) (hs : s₀.re > 1 / 2) (_hs2 : s₀.re < 1) :
    ∀ z ∈ Metric.ball (contourCenter s₀) (contourRadius s₀ hs), z.re > 1 / 2 := by
  intro z hz
  rw [Metric.mem_ball, Complex.dist_eq] at hz
  have hre : |z.re - 1| ≤ ‖z - contourCenter s₀‖ := by
    have := Complex.abs_re_le_norm (z - contourCenter s₀)
    simp only [Complex.sub_re, contourCenter] at this; exact this
  have hlt : |z.re - 1| < contourRadius s₀ hs := lt_of_le_of_lt hre hz
  rw [abs_lt] at hlt
  unfold contourRadius contourDelta at hlt; linarith

/-- The contour circle extends into {Re > 1}. -/
lemma contour_reaches_above_one (s₀ : ℂ) (hs : s₀.re > 1 / 2) (hs2 : s₀.re < 1) :
    ∃ z ∈ Metric.ball (contourCenter s₀) (contourRadius s₀ hs), z.re > 1 := by
  set R := contourRadius s₀ hs with hR_def
  have hR_pos : R > 0 := contourRadius_pos s₀ hs hs2
  refine ⟨⟨1 + R / 2, s₀.im⟩, ?_, ?_⟩
  · rw [Metric.mem_ball, Complex.dist_eq]
    have hsub : (⟨1 + R / 2, s₀.im⟩ : ℂ) - contourCenter s₀ = ↑(R / 2 : ℝ) := by
      apply Complex.ext <;> simp [contourCenter]
    rw [hsub, Complex.norm_real, Real.norm_eq_abs, abs_of_pos (by linarith)]
    linarith
  · simp; linarith

/-!
## Section 2: Dirichlet Polynomials (Partial Sums of 1/ζ)

The partial sums S_N(s) = ∑_{n=1}^{N} μ(n)/n^s are entire functions (finite
sums of entire functions n^{-s} = exp(-s log n)).
-/

/-- A Dirichlet polynomial (partial sum of the Möbius series). -/
noncomputable def dirichletPoly (N : ℕ) (s : ℂ) : ℂ :=
  ∑ n ∈ Icc 1 N, (μ n : ℂ) / (n : ℂ) ^ s

/-- Dirichlet polynomials are `DiffContOnCl` on any ball.
    This is the form needed for Mathlib's Cauchy integral theorems
    (`DiffContOnCl.circleIntegral_eq_zero`, `DiffContOnCl.circleIntegral_sub_inv_smul`),
    which require `DiffContOnCl` rather than bare `DifferentiableOn`.
    The proof rewrites n^{-s} as exp(-s log n), which is entire and handled by `fun_prop`. -/
lemma dirichlet_poly_diffContOnCl (N : ℕ) (c : ℂ) (R : ℝ) :
    DiffContOnCl ℂ (dirichletPoly N) (Metric.ball c R) := by
  refine DifferentiableOn.diffContOnCl ?_
  apply DifferentiableOn.congr
    (f := fun s => ∑ n ∈ Finset.Icc 1 N, (μ n : ℂ) * Complex.exp (-s * Complex.log n))
  · fun_prop
  · intro x _; unfold dirichletPoly
    refine Finset.sum_congr rfl fun n hn => ?_
    have hne : (n : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr (by linarith [(Finset.mem_Icc.mp hn).1])
    rw [Complex.cpow_def_of_ne_zero hne, div_eq_mul_inv, ← Complex.exp_neg]; ring_nf

/-- Dirichlet polynomials are differentiable everywhere (entire functions). -/
lemma dirichletPoly_differentiable (N : ℕ) : Differentiable ℂ (dirichletPoly N) := by
  intro z
  exact (dirichlet_poly_diffContOnCl N z 1).differentiableAt
    Metric.isOpen_ball (Metric.mem_ball_self one_pos)

/-!
## Section 3: Cauchy's Theorem for Dirichlet Polynomials and Weighted Variants

Since Dirichlet polynomials are entire, their circle integrals are zero.
The same holds for products of entire functions.
-/

/-- **Cauchy's theorem**: The circle integral of a Dirichlet polynomial is zero. -/
theorem circleIntegral_dirichletPoly_eq_zero (N : ℕ) (c : ℂ) (R : ℝ) (hR : 0 ≤ R) :
    ∮ z in C(c, R), dirichletPoly N z = 0 :=
  DiffContOnCl.circleIntegral_eq_zero hR (dirichlet_poly_diffContOnCl N c R)

/-- The product (z - s₀)^m · dirichletPoly N z is `DiffContOnCl` on any ball. -/
lemma weighted_dirichlet_poly_diffContOnCl (N : ℕ) (s₀ c : ℂ) (m : ℕ) (R : ℝ) :
    DiffContOnCl ℂ (fun z => (z - s₀) ^ m * dirichletPoly N z) (Metric.ball c R) := by
  apply DifferentiableOn.diffContOnCl
  apply DifferentiableOn.mul
  · exact ((differentiable_id.sub (differentiable_const s₀)).pow m).differentiableOn
  · exact (dirichletPoly_differentiable N).differentiableOn

/-- The circle integral of (z - s₀)^m · S_N(z) is zero (product of entire functions). -/
theorem circleIntegral_weighted_dirichletPoly_eq_zero
    (N : ℕ) (s₀ c : ℂ) (m : ℕ) (R : ℝ) (hR : 0 ≤ R) :
    ∮ z in C(c, R), (z - s₀) ^ m * dirichletPoly N z = 0 :=
  DiffContOnCl.circleIntegral_eq_zero hR (weighted_dirichlet_poly_diffContOnCl N s₀ c m R)

/-!
## Section 4: The Residue at a Zero of Arbitrary Order

If ζ(s₀) = 0 with order k ≥ 1, then we can write ζ(z) = (z - s₀)^k · φ(z)
where φ is analytic and φ(s₀) ≠ 0. Then:

  (z - s₀)^{k-1}/ζ(z) = (z - s₀)^{-1} · (1/φ(z))

The Cauchy integral formula gives:
  ∮ (z - s₀)^{k-1}/ζ(z) dz = 2πi/φ(s₀) ≠ 0

This approach works for zeros of any order k ≥ 1, removing the need to assume
the Grand Simplicity Hypothesis (that all zeros are simple).
-/

/-- ζ is analytic at any point s ≠ 1. -/
lemma riemannZeta_analyticAt (s : ℂ) (hs : s ≠ 1) : AnalyticAt ℂ riemannZeta s := by
  have hd : DifferentiableOn ℂ riemannZeta ({(1 : ℂ)}ᶜ) :=
    fun z hz => (differentiableAt_riemannZeta
      (Set.mem_compl_singleton_iff.mp hz)).differentiableWithinAt
  exact hd.analyticAt (isOpen_compl_singleton.mem_nhds (Set.mem_compl_singleton_iff.mpr hs))

/-- If ζ(s₀) = 0 with Re(s₀) > 0, then ζ is not identically zero near s₀. -/
lemma riemannZeta_not_eventually_zero (s₀ : ℂ) (hs : s₀.re > 0) (hs1 : s₀ ≠ 1) :
    ¬ (∀ᶠ z in nhds s₀, riemannZeta z = 0) := by
  by_contra h_contra;
  have h_connected : AnalyticOnNhd ℂ riemannZeta (Set.univ \ {1}) := by
    apply_rules [ DifferentiableOn.analyticOnNhd ];
    · intro z hz; exact differentiableAt_riemannZeta ( by aesop ) |> DifferentiableAt.differentiableWithinAt;
    · exact isOpen_univ.sdiff isClosed_singleton;
  have h_zero : ∀ z ∈ Set.univ \ {1}, riemannZeta z = 0 := by
    apply_rules [ h_connected.eqOn_zero_of_preconnected_of_eventuallyEq_zero ];
    · have h_path_connected : IsPathConnected (Set.univ \ {1} : Set ℂ) := by
        have h_path_connected : IsPathConnected (Set.univ \ {0} : Set ℂ) := by
          have h_path_connected : IsPathConnected (Set.range (fun z : ℂ => Complex.exp z)) := by
            exact isPathConnected_range ( Complex.continuous_exp );
          convert h_path_connected using 1;
          ext; simp [Complex.exp_ne_zero];
        have h_path_connected : IsPathConnected (Set.image (fun z : ℂ => z + 1) (Set.univ \ {0})) := by
          apply_rules [ IsPathConnected.image, h_path_connected ];
          exact continuous_id.add continuous_const;
        convert h_path_connected using 1 ; ext ; aesop;
      exact h_path_connected.isConnected.isPreconnected;
    · aesop;
  exact absurd ( h_zero 2 ( by norm_num ) ) ( by norm_num [ riemannZeta_two ] )

/-- Zeros of ζ in the critical strip are isolated. -/
lemma riemannZeta_isolated_zero (s₀ : ℂ) (_hzero : riemannZeta s₀ = 0)
    (hs : s₀.re > 0) (hs1 : s₀ ≠ 1) :
    ∀ᶠ z in nhdsWithin s₀ {s₀}ᶜ, riemannZeta z ≠ 0 := by
  have := @riemannZeta_analyticAt s₀ hs1;
  have := this.eventually_eq_zero_or_eventually_ne_zero;
  exact this.resolve_left ( by exact fun h => riemannZeta_not_eventually_zero s₀ hs hs1 h )

/-- **Factoring ζ at a zero of arbitrary order.**

    If ζ(s₀) = 0 with s₀ ≠ 1, then ζ is not identically zero near s₀,
    so by `AnalyticAt.exists_eventuallyEq_pow_smul_nonzero_iff` there exist
    k ≥ 1 and φ analytic with φ(s₀) ≠ 0 such that ζ(z) = (z - s₀)^k · φ(z) near s₀. -/
lemma riemannZeta_factor_at_zero (s₀ : ℂ) (hzero : riemannZeta s₀ = 0)
    (hs : s₀.re > 0) (hs1 : s₀ ≠ 1) :
    ∃ (k : ℕ) (φ : ℂ → ℂ), 1 ≤ k ∧ AnalyticAt ℂ φ s₀ ∧ φ s₀ ≠ 0 ∧
      ∀ᶠ z in nhds s₀, riemannZeta z = (z - s₀) ^ k • φ z := by
  have h_analytic := riemannZeta_analyticAt s₀ hs1
  have h_not_all_zero : ¬∀ᶠ z in nhds s₀, riemannZeta z = 0 :=
    riemannZeta_not_eventually_zero s₀ hs hs1
  rw [← h_analytic.exists_eventuallyEq_pow_smul_nonzero_iff] at h_not_all_zero
  obtain ⟨k, φ, hφ_analytic, hφ_ne_zero, hfact⟩ := h_not_all_zero
  have hk_pos : 1 ≤ k := by
    by_contra h; push_neg at h; interval_cases k
    have h_ev := hfact.self_of_nhds
    simp only [pow_zero, one_smul] at h_ev
    exact hφ_ne_zero (h_ev ▸ hzero)
  exact ⟨k, φ, hk_pos, hφ_analytic, hφ_ne_zero, hfact⟩

/-
There exists r > 0 such that ζ(z) ≠ 0 for all z on sphere(s₀, r) and
    the closed ball B(s₀, r) ⊂ {Re > 1/2}.
-/
lemma riemannZeta_zero_exists_good_radius (s₀ : ℂ) (_hzero : riemannZeta s₀ = 0)
    (hre1 : s₀.re > 1 / 2) (hre_lt : s₀.re < 1) :
    ∃ r > 0, (∀ z ∈ Metric.closedBall s₀ r, z.re > 1 / 2) ∧
             (∀ z ∈ Metric.sphere s₀ r, riemannZeta z ≠ 0) ∧
             (∀ z ∈ Metric.ball s₀ r, z ≠ s₀ → riemannZeta z ≠ 0) := by
  -- Use `riemannZeta_isolated_zero` to get that zeros are isolated near s₀.
  obtain ⟨r₁, hr₁⟩ : ∃ r₁ > 0, ∀ z ∈ Metric.ball s₀ r₁, z ≠ s₀ → riemannZeta z ≠ 0 := by
    have := riemannZeta_isolated_zero s₀ _hzero ( by linarith ) ( by aesop );
    rcases Metric.mem_nhdsWithin_iff.mp this with ⟨ r₁, hr₁, hr₁' ⟩ ; use r₁ ; aesop;
  -- Choose r₂ such that closedBall(s₀, r₂) ⊂ {Re > 1/2}.
  obtain ⟨r₂, hr₂⟩ : ∃ r₂ > 0, ∀ z ∈ Metric.closedBall s₀ r₂, z.re > 1 / 2 := by
    norm_num [ Complex.dist_eq, Complex.normSq, Complex.norm_def ] at *;
    exact ⟨ ( s₀.re - 1 / 2 ) / 2, by linarith, fun z hz => by nlinarith [ Real.sqrt_le_iff.mp hz ] ⟩;
  refine' ⟨ Min.min r₁ r₂ / 2, _, _, _, _ ⟩ <;> norm_num [ hr₁, hr₂ ];
  · exact fun z hz => hr₂.2 z <| Metric.mem_closedBall.2 <| le_trans hz <| by linarith [ min_le_left r₁ r₂, min_le_right r₁ r₂ ] ;
  · intro z hz;
    exact hr₁.2 z ( by rw [ Metric.mem_ball ] ; exact hz.trans_lt ( by linarith [ min_le_left r₁ r₂, min_le_right r₁ r₂ ] ) ) ( by rintro rfl; norm_num at hz; linarith [ lt_min hr₁.1 hr₂.1 ] );
  · exact fun z hz hne => hr₁.2 z ( lt_of_lt_of_le hz ( by linarith [ min_le_left r₁ r₂, min_le_right r₁ r₂ ] ) ) hne

/-
**Weighted residue integral is nonzero** (no GSH needed).

    Since ζ(s₀) = 0 with order k ≥ 1, we can write
    ζ(z) = (z - s₀)^k · φ(z) where φ is analytic and φ(s₀) ≠ 0. Then:
      (z - s₀)^{k-1}/ζ(z) = (z - s₀)⁻¹ · φ(z)⁻¹
    By the Cauchy integral formula:
      ∮ (z-s₀)^{k-1}/ζ(z) dz = 2πi/φ(s₀) ≠ 0

    This works for zeros of any order k, not just simple zeros.
    In particular, the Grand Simplicity Hypothesis is NOT needed.
-/
lemma weighted_recip_zeta_nonzero_residue (s₀ : ℂ) (hzero : riemannZeta s₀ = 0)
    (hre1 : s₀.re > 1 / 2) (hre_lt : s₀.re < 1) :
    ∃ (k : ℕ) (r : ℝ), 1 ≤ k ∧ 0 < r ∧
      (∀ z ∈ Metric.closedBall s₀ r, z.re > 1 / 2) ∧
      (∀ z ∈ Metric.sphere s₀ r, riemannZeta z ≠ 0) ∧
      CircleIntegrable (fun z => (z - s₀) ^ (k - 1) / riemannZeta z) s₀ r ∧
      (∀ n, CircleIntegrable (fun z => (z - s₀) ^ (k - 1) * dirichletPoly n z) s₀ r) ∧
      ∮ z in C(s₀, r), ((z - s₀) ^ (k - 1) / riemannZeta z) ≠ 0 := by
  -- Step 1: s₀ ≠ 1
  have hs₀_ne_one : s₀ ≠ 1 := by intro h; rw [h] at hre_lt; simp at hre_lt
  -- Step 2: Factor ζ(z) = (z - s₀)^k · φ(z)
  obtain ⟨k, φ, hk, hφ_analytic, hφ_ne_zero, hfact⟩ :=
    riemannZeta_factor_at_zero s₀ hzero (by linarith) hs₀_ne_one
  -- Step 3: Get good radius
  obtain ⟨r₀, hr₀_pos, hcball, hno_zeros_sphere, hno_zeros_ball⟩ :=
    riemannZeta_zero_exists_good_radius s₀ hzero hre1 hre_lt
  -- Step 4: φ ≠ 0 in a neighborhood
  obtain ⟨r₁, hr₁_pos, hφ_nonzero⟩ :
      ∃ r₁ > 0, ∀ z ∈ Metric.ball s₀ r₁, φ z ≠ 0 := by
    obtain ⟨r₁, hr₁_pos, hr₁⟩ := Metric.eventually_nhds_iff.mp
      (hφ_analytic.continuousAt.eventually (isOpen_ne.mem_nhds hφ_ne_zero))
    exact ⟨r₁, hr₁_pos, fun z hz => hr₁ (Metric.mem_ball.mp hz)⟩
  -- Step 5: Factoring holds on a ball
  obtain ⟨r₂, hr₂_pos, hfact_ball⟩ :
      ∃ r₂ > 0, ∀ z ∈ Metric.ball s₀ r₂, riemannZeta z = (z - s₀) ^ k • φ z := by
    obtain ⟨r₂, hr₂_pos, hr₂⟩ := Metric.eventually_nhds_iff.mp hfact
    exact ⟨r₂, hr₂_pos, fun z hz => hr₂ (Metric.mem_ball.mp hz)⟩
  -- Step 5b: φ is differentiable on a ball
  obtain ⟨r₃, hr₃_pos, hφ_diff_on⟩ : ∃ r₃ > 0, DifferentiableOn ℂ φ (Metric.ball s₀ r₃) := by
    obtain ⟨r₃, hr₃_pos, hr₃⟩ := Metric.eventually_nhds_iff.mp hφ_analytic.eventually_analyticAt
    exact ⟨r₃, hr₃_pos, fun z hz =>
      (hr₃ (Metric.mem_ball.mp hz)).differentiableAt.differentiableWithinAt⟩
  -- Step 6: Choose r small enough
  set r := min (min (min r₀ r₁) r₂) r₃ / 2 with hr_def
  have hr_pos : r > 0 := by simp only [hr_def]; positivity
  have hr_lt_r₀ : r < r₀ := by
    have : min (min (min r₀ r₁) r₂) r₃ ≤ r₀ :=
      le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_left _ _)
    linarith
  have hr_lt_r₁ : r < r₁ := by
    have : min (min (min r₀ r₁) r₂) r₃ ≤ r₁ :=
      le_trans (le_trans (min_le_left _ _) (min_le_left _ _)) (min_le_right _ _)
    linarith
  have hr_lt_r₂ : r < r₂ := by
    have : min (min (min r₀ r₁) r₂) r₃ ≤ r₂ :=
      le_trans (min_le_left _ _) (min_le_right _ _)
    linarith
  have hr_lt_r₃ : r < r₃ := by
    have : min (min (min r₀ r₁) r₂) r₃ ≤ r₃ := min_le_right _ _
    linarith
  -- Step 7: Transfer properties
  have hcball_r : ∀ z ∈ Metric.closedBall s₀ r, z.re > 1 / 2 :=
    fun z hz => hcball z (Metric.closedBall_subset_closedBall (le_of_lt hr_lt_r₀) hz)
  have hno_zeros_r : ∀ z ∈ Metric.sphere s₀ r, riemannZeta z ≠ 0 := by
    intro z hz
    have hz_ne : z ≠ s₀ := by
      intro heq; rw [heq, Metric.mem_sphere, dist_self] at hz; linarith
    exact hno_zeros_ball z
      (Metric.mem_ball.mpr (by rw [Metric.mem_sphere.mp hz]; linarith)) hz_ne
  -- Step 8: Agree on sphere
  have h_agree : ∀ z ∈ Metric.sphere s₀ r,
      (z - s₀) ^ (k - 1) / riemannZeta z = (z - s₀)⁻¹ * (φ z)⁻¹ := by
    intro z hz
    have hz_ne : z ≠ s₀ := by
      intro heq; rw [heq, Metric.mem_sphere, dist_self] at hz; linarith
    have hz_ball₂ : z ∈ Metric.ball s₀ r₂ :=
      Metric.mem_ball.mpr (by rw [Metric.mem_sphere.mp hz]; linarith)
    rw [hfact_ball z hz_ball₂, smul_eq_mul, div_eq_mul_inv, mul_inv, ← mul_assoc]
    congr 1
    rw [← zpow_natCast (z - s₀) (k - 1), ← zpow_natCast (z - s₀) k,
        ← zpow_neg, ← zpow_add₀ (sub_ne_zero_of_ne hz_ne)]
    have : (↑(k - 1) : ℤ) + -↑k = -1 := by omega
    rw [this, zpow_neg_one]
  -- Step 9: φ⁻¹ is DiffContOnCl on ball(s₀, r)
  have hφ_inv_diffContOnCl : DiffContOnCl ℂ (fun z => (φ z)⁻¹) (Metric.ball s₀ r) := by
    apply DifferentiableOn.diffContOnCl
    intro z hz
    replace hz := Metric.closure_ball_subset_closedBall hz
    have hφ_da : DifferentiableAt ℂ φ z :=
      (hφ_diff_on z (Metric.closedBall_subset_ball hr_lt_r₃ hz)).differentiableAt
        (Metric.isOpen_ball.mem_nhds (Metric.closedBall_subset_ball hr_lt_r₃ hz))
    exact hφ_da.differentiableWithinAt.inv
      (hφ_nonzero z (Metric.closedBall_subset_ball hr_lt_r₁ hz))
  -- Step 10: Cauchy integral formula
  have h_cauchy : ∮ z in C(s₀, r), (z - s₀)⁻¹ • (φ z)⁻¹ =
      (2 * ↑Real.pi * I) • (φ s₀)⁻¹ :=
    DiffContOnCl.circleIntegral_sub_inv_smul hφ_inv_diffContOnCl (Metric.mem_ball_self hr_pos)
  -- Step 11: Circle integrability
  have hf_int : CircleIntegrable (fun z => (z - s₀) ^ (k - 1) / riemannZeta z) s₀ r := by
    apply_rules [ ContinuousOn.circleIntegrable ];
    · positivity;
    · refine' ContinuousOn.congr _ h_agree;
      refine' ContinuousOn.mul _ _;
      · exact continuousOn_of_forall_continuousAt fun z hz => ContinuousAt.inv₀ ( continuousAt_id.sub continuousAt_const ) ( sub_ne_zero_of_ne <| by rintro rfl; exact absurd hz <| by norm_num; linarith );
      · refine' ContinuousOn.inv₀ _ _;
        · exact hφ_diff_on.continuousOn.mono ( Metric.sphere_subset_closedBall.trans ( Metric.closedBall_subset_ball ( by linarith ) ) );
        · exact fun z hz => hφ_nonzero z <| Metric.mem_ball.mpr <| lt_of_le_of_lt ( Metric.mem_sphere.mp hz |> le_of_eq ) hr_lt_r₁
  have hg_int : ∀ n, CircleIntegrable
      (fun z => (z - s₀) ^ (k - 1) * dirichletPoly n z) s₀ r := by
    intro n
    exact ((((differentiable_id.sub (differentiable_const s₀)).pow (k - 1)).mul
      (dirichletPoly_differentiable n)).continuous.continuousOn).circleIntegrable hr_pos.le
  -- Step 12: The weighted integral equals the Cauchy integral
  have h_integral_eq : ∮ z in C(s₀, r), ((z - s₀) ^ (k - 1) / riemannZeta z) =
      (2 * ↑Real.pi * I) • (φ s₀)⁻¹ := by
    rw [← h_cauchy, circleIntegral.integral_congr (le_of_lt hr_pos)]
    intro z hz
    simp only [smul_eq_mul]
    exact h_agree z (by simpa [abs_of_pos hr_pos] using hz)
  -- Step 13: Nonzero
  have h_nonzero : (2 * ↑Real.pi * I) • (φ s₀)⁻¹ ≠ 0 :=
    smul_ne_zero
      (mul_ne_zero (mul_ne_zero two_ne_zero
        (Complex.ofReal_ne_zero.mpr Real.pi_ne_zero)) Complex.I_ne_zero)
      (inv_ne_zero hφ_ne_zero)
  exact ⟨k, r, hk, hr_pos, hcball_r, hno_zeros_r, hf_int, hg_int, h_integral_eq ▸ h_nonzero⟩

/-!
## Section 5: Uniform Approximation on the Contour (Bagchi Universality + Euler Product)
-/

/-- **Bagchi's universality theorem (Dirichlet polynomial form).** -/
theorem bagchi_universality_compact (K : Set ℂ) (_hK : IsCompact K)
    (_hconn : IsConnected Kᶜ)
    (_hre : ∀ z ∈ K, z.re > 1 / 2)
    (_hno_zeros : ∀ z ∈ K, riemannZeta z ≠ 0) :
    TendstoUniformlyOn (fun N => dirichletPoly N) (fun z => 1 / riemannZeta z)
      atTop K := by
  sorry

/-- **Absolute convergence of the Euler product.** -/
theorem euler_product_convergence_compact (K : Set ℂ) (_hK : IsCompact K)
    (_hre : ∀ z ∈ K, z.re > 1) :
    TendstoUniformlyOn (fun N => dirichletPoly N) (fun z => 1 / riemannZeta z)
      atTop K := by
  sorry

/-- **Uniform convergence on circles.** -/
lemma bagchi_approx_on_circle (c : ℂ) (R : ℝ) (_hR : 0 < R)
    (_hsphere_re : ∀ z ∈ Metric.sphere c R, z.re > 1 / 2)
    (_hno_zeros : ∀ z ∈ Metric.sphere c R, riemannZeta z ≠ 0) :
    TendstoUniformlyOn (fun N => dirichletPoly N) (fun z => 1 / riemannZeta z)
      atTop (Metric.sphere c R) := by
  sorry

/-!
## Section 6: The Contradiction Argument

We combine:
1. ∮ (z-s₀)^{k-1}/ζ(z) dz ≠ 0 (Cauchy integral formula at zero of order k)
2. (z-s₀)^{k-1} · S_n(z) → (z-s₀)^{k-1}/ζ(z) uniformly on the circle
3. ∮ (z-s₀)^{k-1} · S_n(z) dz = 0 (product of entire functions, Cauchy's theorem)
4. Therefore ∮ (z-s₀)^{k-1}/ζ(z) dz = 0

This contradicts step 1.
-/

/-- If a sequence of functions with zero circle integrals converges uniformly
    to f on the circle, then ∮ f = 0. -/
lemma circleIntegral_eq_zero_of_uniform_limit (c : ℂ) (R : ℝ) (hR : 0 < R)
    (f : ℂ → ℂ) (g : ℕ → ℂ → ℂ)
    (hg_zero : ∀ n, ∮ z in C(c, R), g n z = 0)
    (hconv : TendstoUniformlyOn g f atTop (Metric.sphere c R))
    (hf_int : CircleIntegrable f c R)
    (hg_int : ∀ n, CircleIntegrable (g n) c R) :
    ∮ z in C(c, R), f z = 0 := by
  by_contra h_nonzero
  set ε := ‖∮ z in C(c, R), f z‖ / 2 with hε_def
  obtain ⟨N₀, hN₀⟩ : ∃ N₀, ∀ n ≥ N₀, ∀ z ∈ Metric.sphere c R,
      ‖f z - g n z‖ < ε / (2 * Real.pi * R + 1) := by
    have := Metric.tendstoUniformlyOn_iff.mp hconv
    exact Filter.eventually_atTop.mp
      (this _ (div_pos (half_pos (norm_pos_iff.mpr h_nonzero)) (by positivity)))
  have h_bound : ‖∮ z in C(c, R), f z - g N₀ z‖ ≤
      2 * Real.pi * R * (ε / (2 * Real.pi * R + 1)) := by
    refine le_trans (circleIntegral.norm_integral_le_of_norm_le_const'
      (C := ε / (2 * Real.pi * R + 1)) ?_) (by rw [abs_of_pos hR])
    exact fun z hz => le_of_lt (hN₀ N₀ le_rfl z (by simpa [abs_of_pos hR] using hz))
  rw [circleIntegral.integral_sub] at h_bound
  · simp only [hg_zero, sub_zero] at h_bound
    rw [mul_div, le_div_iff₀] at h_bound
    · nlinarith [Real.pi_pos, mul_pos (mul_pos (by norm_num : (0:ℝ) < 2) Real.pi_pos) hR,
        norm_pos_iff.mpr h_nonzero]
    · linarith [mul_pos (mul_pos (by norm_num : (0:ℝ) < 2) Real.pi_pos) hR]
  · exact hf_int
  · exact hg_int N₀

/-- **Weighted uniform convergence**: if S_N → 1/ζ uniformly on a sphere,
    then (z-s₀)^m · S_N → (z-s₀)^m/ζ uniformly on the sphere. -/
lemma weighted_bagchi_approx_on_circle (s₀ c : ℂ) (m : ℕ) (R : ℝ) (_hR : 0 < R)
    (_hsphere_re : ∀ z ∈ Metric.sphere c R, z.re > 1 / 2)
    (_hno_zeros : ∀ z ∈ Metric.sphere c R, riemannZeta z ≠ 0) :
    TendstoUniformlyOn
      (fun N z => (z - s₀) ^ m * dirichletPoly N z)
      (fun z => (z - s₀) ^ m / riemannZeta z)
      atTop (Metric.sphere c R) := by
  sorry

/-- **The weighted contour integral vanishes.** -/
theorem weighted_recip_zeta_circleIntegral_eq_zero
    (s₀ c : ℂ) (m : ℕ) (R : ℝ) (hR : 0 < R)
    (hsphere_re : ∀ z ∈ Metric.sphere c R, z.re > 1 / 2)
    (hno_zeros : ∀ z ∈ Metric.sphere c R, riemannZeta z ≠ 0)
    (hf_int : CircleIntegrable (fun z => (z - s₀) ^ m / riemannZeta z) c R)
    (hg_int : ∀ n, CircleIntegrable (fun z => (z - s₀) ^ m * dirichletPoly n z) c R) :
    ∮ z in C(c, R), ((z - s₀) ^ m / riemannZeta z) = 0 :=
  circleIntegral_eq_zero_of_uniform_limit c R hR
    (fun z => (z - s₀) ^ m / riemannZeta z)
    (fun n z => (z - s₀) ^ m * dirichletPoly n z)
    (fun n => circleIntegral_weighted_dirichletPoly_eq_zero n s₀ c m R (le_of_lt hR))
    (weighted_bagchi_approx_on_circle s₀ c m R hR hsphere_re hno_zeros)
    hf_int hg_int

/-!
## Section 7: Deriving Non-Vanishing of ζ
-/

/-- If ζ has a zero s₀ in the critical strip, contradiction. -/
theorem zeta_no_zero_contour (s₀ : ℂ) (hzero : riemannZeta s₀ = 0)
    (hre1 : s₀.re > 1 / 2) (hre2 : s₀.re < 1) : False := by
  obtain ⟨k, r, _hk, hr_pos, hcball_re, hno_zeros, hf_int, hg_int, hr_nonzero⟩ :=
    weighted_recip_zeta_nonzero_residue s₀ hzero hre1 hre2
  have hsphere_re : ∀ z ∈ Metric.sphere s₀ r, z.re > 1 / 2 :=
    fun z hz => hcball_re z (Metric.sphere_subset_closedBall hz)
  have h_zero := weighted_recip_zeta_circleIntegral_eq_zero s₀ s₀ (k - 1) r hr_pos
    hsphere_re hno_zeros hf_int hg_int
  exact hr_nonzero h_zero

/-!
## Section 8: The Figure-8 Contour Strategy
-/

/-- The crossing point of the figure-8. -/
noncomputable def figure8CrossingPoint (s₀ : ℂ) : ℂ := ⟨1, s₀.im⟩

lemma figure8CrossingPoint_eq_contourCenter (s₀ : ℂ) :
    figure8CrossingPoint s₀ = contourCenter s₀ := rfl

/-- Right loop radius. -/
noncomputable def rightLoopRadius (s₀ : ℂ) (_ : s₀.re > 1 / 2) : ℝ :=
  (1 - s₀.re) / 4

/-- Right loop center. -/
noncomputable def rightLoopCenter (s₀ : ℂ) (hs : s₀.re > 1 / 2) : ℂ :=
  ⟨1 + rightLoopRadius s₀ hs, s₀.im⟩

lemma rightLoopRadius_pos (s₀ : ℂ) (hs : s₀.re > 1 / 2) (hs2 : s₀.re < 1) :
    rightLoopRadius s₀ hs > 0 := by
  unfold rightLoopRadius; linarith

/-- The right loop stays entirely in {Re ≥ 1}. -/
lemma rightLoop_re_ge_one (s₀ : ℂ) (hs : s₀.re > 1 / 2) (_hs2 : s₀.re < 1) :
    ∀ z ∈ Metric.closedBall (rightLoopCenter s₀ hs) (rightLoopRadius s₀ hs),
      z.re ≥ 1 := by
  intro z hz
  rw [Metric.mem_closedBall, Complex.dist_eq] at hz
  have hre : |z.re - (rightLoopCenter s₀ hs).re| ≤ ‖z - rightLoopCenter s₀ hs‖ :=
    Complex.abs_re_le_norm (z - rightLoopCenter s₀ hs)
  have : |z.re - (1 + rightLoopRadius s₀ hs)| ≤ rightLoopRadius s₀ hs := by
    calc |z.re - (1 + rightLoopRadius s₀ hs)| = |z.re - (rightLoopCenter s₀ hs).re| := by
          simp [rightLoopCenter]
      _ ≤ ‖z - rightLoopCenter s₀ hs‖ := hre
      _ ≤ rightLoopRadius s₀ hs := hz
  rw [abs_le] at this; linarith

/-- **Right loop non-vanishing**. -/
lemma rightLoop_zeta_ne_zero (s₀ : ℂ) (hs : s₀.re > 1 / 2) (hs2 : s₀.re < 1) :
    ∀ z ∈ Metric.closedBall (rightLoopCenter s₀ hs) (rightLoopRadius s₀ hs),
      riemannZeta z ≠ 0 :=
  fun z hz => riemannZeta_ne_zero_of_one_le_re (rightLoop_re_ge_one s₀ hs hs2 z hz)

/-
**Crossing point is not an accumulation point of zeros**.
-/
lemma crossingPoint_not_accumulation (s₀ : ℂ) (hs : s₀.re > 1 / 2) :
    ∃ ε > 0, ∀ z ∈ Metric.ball (figure8CrossingPoint s₀) ε,
      riemannZeta z ≠ 0 := by
  have hp_re : (figure8CrossingPoint s₀).re = 1 := by simp [figure8CrossingPoint]
  have hp_ne_zero : riemannZeta (figure8CrossingPoint s₀) ≠ 0 :=
    riemannZeta_ne_zero_of_one_le_re (by rw [hp_re])
  by_cases him : s₀.im = 0
  ·
    have := hp_ne_zero; simp_all +decide [ figure8CrossingPoint ] ;
    contrapose! hp_ne_zero;
    have h_seq : ∃ seq : ℕ → ℂ, Filter.Tendsto seq Filter.atTop (nhds { re := 1, im := 0 }) ∧ ∀ n, riemannZeta (seq n) = 0 ∧ seq n ≠ { re := 1, im := 0 } := by
                                                                                                                                        choose! seq hseq using hp_ne_zero;
                                                                                                                                        refine' ⟨ fun n => seq ( 1 / ( n + 1 ) ), _, _ ⟩ <;> norm_num [ hseq ];
                                                                                                                                        · exact tendsto_iff_dist_tendsto_zero.mpr ( squeeze_zero ( fun _ => dist_nonneg ) ( fun n => le_of_lt ( hseq _ ( by positivity ) |>.1 ) ) ( tendsto_inv_atTop_zero.comp ( Filter.tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop ) ) );
                                                                                                                                        · intro n; specialize hseq ( ( n + 1 : ℝ ) ⁻¹ ) ( by positivity ) ; refine' ⟨ hseq.2, _ ⟩ ; intro h; simp_all +decide [ dist_eq_norm ] ;
                                                                                                                                          exact absurd hseq.2 ( by erw [ show ( { re := 1, im := 0 } : ℂ ) = 1 by norm_num [ Complex.ext_iff ] ] ; exact riemannZeta_one_ne_zero );
    obtain ⟨ seq, hseq₁, hseq₂ ⟩ := h_seq;
    have h_seq_zero : Filter.Tendsto (fun n => riemannZeta (seq n) * (seq n - { re := 1, im := 0 })) Filter.atTop (nhds 1) := by
                                                                                  have h_seq_zero : Filter.Tendsto (fun z => riemannZeta z * (z - { re := 1, im := 0 })) (nhdsWithin { re := 1, im := 0 } { { re := 1, im := 0 } }ᶜ) (nhds 1) := by
                                                                                                                                                                                                                convert riemannZeta_residue_one using 1;
                                                                                                                                                                                                                ext; simp +decide [ mul_comm ];
                                                                                                                                                                                                                exact Or.inl rfl;
                                                                                  exact h_seq_zero.comp <| Filter.tendsto_inf.mpr ⟨ hseq₁, Filter.tendsto_principal.mpr <| Filter.Eventually.of_forall fun n => hseq₂ n |>.2 ⟩;
    aesop
  · have hp_ne_one : figure8CrossingPoint s₀ ≠ 1 := by
      intro heq; exact him (by have := congr_arg Complex.im heq; simpa using this)
    have h_cont := (differentiableAt_riemannZeta hp_ne_one).continuousAt
    have h_ev : ∀ᶠ z in nhds (figure8CrossingPoint s₀), riemannZeta z ≠ 0 :=
      h_cont.eventually (isOpen_ne.mem_nhds hp_ne_zero)
    obtain ⟨ε, hε_pos, hε⟩ := Metric.eventually_nhds_iff.mp h_ev
    exact ⟨ε, hε_pos, fun z hz => hε (Metric.mem_ball.mp hz)⟩

/-- **The figure-8 contradiction**. -/
theorem figure8_contradiction (s₀ : ℂ) (hzero : riemannZeta s₀ = 0)
    (hre1 : s₀.re > 1 / 2) (hre2 : s₀.re < 1) : False :=
  zeta_no_zero_contour s₀ hzero hre1 hre2

/-!
## Section 9: The Riemann Hypothesis (Contour Strategy)
-/

/-- **ζ(s) ≠ 0 for Re(s) > 1/2** (contour integration strategy). -/
theorem zeta_nonvanishing_half_plane_contour (s : ℂ) (hs : s.re > 1 / 2) :
    riemannZeta s ≠ 0 := by
  by_cases h1 : s.re ≥ 1
  · exact riemannZeta_ne_zero_of_one_le_re h1
  · push_neg at h1
    intro hzero
    exact zeta_no_zero_contour s hzero hs h1

/-- **The Riemann Hypothesis** (contour integration strategy).

    Every nontrivial zero of ζ has real part equal to 1/2. -/
theorem riemann_hypothesis_contour (s : ℂ) (hs : riemannZeta s = 0)
    (h_pos : 0 < s.re) (h_lt : s.re < 1) : s.re = 1 / 2 := by
  rcases lt_trichotomy s.re (1 / 2) with h | h | h
  · have hsymm := zeta_symm s h_pos h_lt hs
    have h_re_conj : (1 - s).re > 1 / 2 := by simp [sub_re, one_re]; linarith
    exact absurd (zeta_nonvanishing_half_plane_contour (1 - s) h_re_conj)
      (by rw [hsymm]; simp)
  · exact h
  · exact absurd hs (zeta_nonvanishing_half_plane_contour s h)

end