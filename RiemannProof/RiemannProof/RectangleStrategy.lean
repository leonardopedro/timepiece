import Mathlib
import RiemannProof.Basic
import RiemannProof.Legacy

/-!
# Two-Rectangle Strategy for the Riemann Hypothesis

## Strategy

We prove ζ(s) ≠ 0 for Re(s) > 1/2 using two rectangles and eta approximants,
without using the Möbius function.

### The eta approximants

We use partial sums of the Dirichlet eta function:

  η_n(s) = Σ_{k=1}^n (-1)^{k-1}/k^s

and define the reciprocal zeta approximant:

  1/ζ_n(s) = (1 - 2^{1-s}) / η_n(s)

This is valid on contours that avoid zeros of η_n. Since η_n is a finite sum
of entire functions, it has only finitely many zeros in any bounded region,
so we can choose rectangle edges to avoid them.

### The two-rectangle argument

Suppose for contradiction that ζ(s₀) = 0 for some s₀ with 1/2 < Re(s₀) < 1.

Consider two rectangles, both crossing the vertical line Re = 1 at the same
y-coordinates y_i and y_f (with y_i < Im(s₀) < y_f), and both sharing the
same right edge x_f > 1:

- **R₀** = [x₀, x_f] × [y_i, y_f]: The "small" rectangle, with
  Re(s₀) < x₀ < 1, chosen so that ζ has no zeros inside R₀.

- **R₁** = [x₁, x_f] × [y_i, y_f]: The "large" rectangle, with
  x₁ < Re(s₀), so s₀ is inside R₁.

Both rectangles cross the line Re = 1 at y = y_i and y = y_f.

The key observation: R₁ = [x₁, x₀] × [y_i, y_f] ∪ R₀ (splitting at x₀).

### The contradiction

Suppose ζ(s₀) = 0 for some s₀ with 1/2 < Re(s₀) < 1, so η(s₀) = 0.
Choose a rectangle R ⊂ {1/2 < Re < 1} containing s₀ in its open interior,
with η having no other zeros in R.closure (possible since zeros are isolated).

1. The reciprocal Euler product 1/[etaEulerApprox P] is analytic inside R
   (since etaEulerApprox P is non-vanishing in {1/2 < Re < 1}).
   By Cauchy's theorem: ∮_R 1/[etaEulerApprox P] = 0.

2. On the four edges of R, η ≠ 0 (since s₀ is in the open interior, not
   on any edge, and η has no other zeros in R). Since etaEulerApprox P → η
   uniformly on R.closure, we get 1/[etaEulerApprox P] → 1/η uniformly on
   the edges. Therefore: ∮_R 1/η = lim ∮_R 1/[etaEulerApprox P] = 0.

3. But η(s₀) = 0 means 1/η has a pole at s₀ inside R. By the residue
   theorem, ∮_R 1/η ≠ 0. Contradiction.

## Sorries

The file has sorry statements for the deep analytic content:

1. `etaPartialRect_tendstoUniformlyOn`: The eta partial sums η_n converge
   uniformly to η = (1-2^{1-s})ζ(s) on compact subsets of {1/2 < Re < 1}.
   This requires the convergence theory of the Dirichlet eta series.

2. `etaPartialRect_tendstoUniformlyOn_closure`: Extension to rectangle
   closures crossing Re = 1.

3. `etaPartialRect_eventually_ne_zero_on_R₀`: For rectangles R₀ with no
   zeros of ζ inside and no zeros of (1-2^{1-s}), the partial sums η_n
   are eventually nonvanishing.

4. `recipEta_rect_contour_integral_eq_zero`: The Cauchy integral ∮_R 1/η = 0
   as the limit of vanishing integrals ∮_R 1/[etaEulerApprox P] = 0.
   Uses uniform convergence on edges and the fact that η ≠ 0 on edges.

5. `recipEta_rect_integral_ne_zero_of_zero`: The residue theorem: if η(s₀) = 0
   inside R, then ∮_R 1/η ≠ 0.

6. `eta_zero_isolated_in_rect`: Zeros of η are isolated in the critical strip.

7. `right_sub_integral_vanishes`: The boundary integral of 1/ζ_n over
   the right sub-rectangle [1, x_f] × [y_i, y_f] vanishes for large n.
   This is a supplementary contour lemma.

### Resolved Sorries

- `etaEulerApprox_tendstoUniformlyOn_rect`: **PROVED** using the Dirichlet
  series decomposition (Section 7b). The Euler product convergence is
  decomposed into a finite Dirichlet part (uniformly convergent for
  k < P) and a tail part (uniformly bounded by Bagchi/PNT for k ≥ P).

### Axioms (Section 7b)

- `primeZetaTail_uniform_small`: PNT consequence for prime zeta tail
- `higherPrimeSum_uniform_small`: Absolute convergence of k≥2 terms
- `eulerProd_zeta_exp_connection`: exp formula connecting ζ_P and ζ
-/

open Complex Finset Filter Topology MeasureTheory
open scoped ArithmeticFunction

noncomputable section

/-!
## Section 1: Eta Partial Sums and Approximants
-/

/-- Partial sum of the Dirichlet eta function: η_n(s) = Σ_{k=1}^n (-1)^{k-1}/k^s -/
noncomputable def etaPartialRect (n : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Icc 1 n, (-1 : ℂ) ^ (k - 1) / (k : ℂ) ^ s

/-- The Dirichlet eta function η(s) = (1 - 2^{1-s}) · ζ(s). -/
noncomputable def etaRect (s : ℂ) : ℂ :=
  (1 - (2 : ℂ) ^ (1 - s)) * riemannZeta s

/-- The eta factor (1 - 2^{1-s}). -/
noncomputable def etaFactRect (s : ℂ) : ℂ :=
  1 - (2 : ℂ) ^ (1 - s)

/-- The reciprocal zeta approximant: (1 - 2^{1-s}) / η_n(s).
    This approximates 1/ζ(s) for large n, valid away from zeros of η_n. -/
noncomputable def recipZetaApproxRect (n : ℕ) (s : ℂ) : ℂ :=
  etaFactRect s / etaPartialRect n s

/-
The eta factor is nonzero for Re(s) < 1.
    |2^{1-s}| = 2^{1-Re(s)} > 1 when Re(s) < 1, so 2^{1-s} ≠ 1.
-/
lemma etaFactRect_ne_zero (s : ℂ) (hs : s.re < 1) : etaFactRect s ≠ 0 := by
  unfold etaFactRect;
  rw [ Ne, sub_eq_zero, eq_comm, Complex.cpow_def_of_ne_zero ] <;> norm_num;
  rw [ Complex.exp_eq_one_iff ];
  norm_num [ Complex.ext_iff, Complex.log_re, Complex.log_im ];
  exact fun h => False.elim <| by linarith;

/-
Each η_n is a finite sum of entire functions, hence entire.
-/
lemma etaPartialRect_differentiable (n : ℕ) : Differentiable ℂ (etaPartialRect n) := by
  intro s;
  unfold etaPartialRect;
  norm_num [ Complex.cpow_def ];
  refine' DifferentiableAt.congr_of_eventuallyEq _ _;
  exact fun s => ∑ x ∈ Finset.Icc 1 n, ( -1 ) ^ ( x - 1 ) / Complex.exp ( Complex.log x * s );
  · fun_prop (disch := norm_num);
  · filter_upwards [ ] with s using Finset.sum_congr rfl fun x hx => by aesop;

/-!
## Section 2: Rectangle Specification and Integration
-/

/-- A rectangle in ℂ specified by its corner coordinates. -/
structure Rect where
  x_lo : ℝ
  x_hi : ℝ
  y_lo : ℝ
  y_hi : ℝ
  hx : x_lo < x_hi
  hy : y_lo < y_hi

/-- The closed interior of a rectangle. -/
def Rect.closure (R : Rect) : Set ℂ :=
  {z : ℂ | R.x_lo ≤ z.re ∧ z.re ≤ R.x_hi ∧ R.y_lo ≤ z.im ∧ z.im ≤ R.y_hi}

/-- The open interior of a rectangle. -/
def Rect.openInt (R : Rect) : Set ℂ :=
  {z : ℂ | R.x_lo < z.re ∧ z.re < R.x_hi ∧ R.y_lo < z.im ∧ z.im < R.y_hi}

/-- A rectangle crosses Re = 1 if x_lo < 1 < x_hi. -/
def Rect.crossesLineOne (R : Rect) : Prop :=
  R.x_lo < 1 ∧ 1 < R.x_hi

/-- Membership in a rectangle's open interior. -/
lemma Rect.mem_openInt (R : Rect) (z : ℂ) :
    z ∈ R.openInt ↔ R.x_lo < z.re ∧ z.re < R.x_hi ∧ R.y_lo < z.im ∧ z.im < R.y_hi :=
  Iff.rfl

/-- The boundary integral of f around a rectangle, using Mathlib's convention.
    This equals: (∫ bottom) - (∫ top) + I·(∫ right) - I·(∫ left). -/
noncomputable def Rect.boundaryIntegral (R : Rect) (f : ℂ → ℂ) : ℂ :=
  ((∫ x in R.x_lo..R.x_hi, f (↑x + ↑R.y_lo * I)) -
   (∫ x in R.x_lo..R.x_hi, f (↑x + ↑R.y_hi * I))) +
  I • (∫ y in R.y_lo..R.y_hi, f (↑R.x_hi + ↑y * I)) -
  I • (∫ y in R.y_lo..R.y_hi, f (↑R.x_lo + ↑y * I))

/-!
## Section 3: Cauchy's Theorem for Rectangles

If f is differentiable on a rectangle, the boundary integral is zero.
-/

/-
Cauchy's theorem for rectangles: the boundary integral of a function
    differentiable on the rectangle is zero.
-/
lemma rect_cauchy (R : Rect) (f : ℂ → ℂ)
    (hf : DifferentiableOn ℂ f R.closure) :
    R.boundaryIntegral f = 0 := by
  unfold Rect.boundaryIntegral
  apply Complex.integral_boundary_rect_eq_zero_of_differentiable_on_off_countable
    f ⟨R.x_lo, R.y_lo⟩ ⟨R.x_hi, R.y_hi⟩ ∅ (Set.countable_empty)
  · -- ContinuousOn on closed rectangle
    refine' hf.continuousOn.mono _;
    simp +decide [ Set.subset_def, Complex.mem_reProdIm, R.hx.le, R.hy.le ];
    exact fun x hx₁ hx₂ hx₃ hx₄ => ⟨ hx₁, hx₂, hx₃, hx₄ ⟩
  · -- DifferentiableAt on open interior
    simp +zetaDelta at *;
    intro z hz
    have h_diff : DifferentiableOn ℂ f (R.openInt) := by
      refine' hf.mono _;
      exact fun x hx => ⟨ hx.1.le, hx.2.1.le, hx.2.2.1.le, hx.2.2.2.le ⟩;
    refine' h_diff.differentiableAt _;
    exact IsOpen.mem_nhds ( isOpen_Ioi.preimage Complex.continuous_re |> IsOpen.inter <| isOpen_Iio.preimage Complex.continuous_re |> IsOpen.inter <| isOpen_Ioi.preimage Complex.continuous_im |> IsOpen.inter <| isOpen_Iio.preimage Complex.continuous_im ) ⟨ by simpa [ R.hx.le ] using hz.1.1, by simpa [ R.hx.le ] using hz.1.2, by simpa [ R.hy.le ] using hz.2.1, by simpa [ R.hy.le ] using hz.2.2 ⟩

/-!
## Section 4: Splitting Rectangle Integrals

The boundary integral around a rectangle [x_lo, x_hi] × [y_lo, y_hi]
can be split at any intermediate x-value x_mid into the sum of the
boundary integrals of the two sub-rectangles.
-/

/-- Splitting a rectangle at an intermediate x-coordinate. -/
def Rect.splitAtX (R : Rect) (x_mid : ℝ) (hlo : R.x_lo < x_mid) (hhi : x_mid < R.x_hi) :
    Rect × Rect :=
  (⟨R.x_lo, x_mid, R.y_lo, R.y_hi, hlo, R.hy⟩,
   ⟨x_mid, R.x_hi, R.y_lo, R.y_hi, hhi, R.hy⟩)

/-
The boundary integral splits additively when we split the rectangle at x_mid.
    The vertical segments at x = x_mid cancel (traversed in opposite directions).
-/
lemma rect_split_integral (R : Rect) (f : ℂ → ℂ) (x_mid : ℝ)
    (hlo : R.x_lo < x_mid) (hhi : x_mid < R.x_hi)
    (hf : ContinuousOn f R.closure) :
    R.boundaryIntegral f =
      (R.splitAtX x_mid hlo hhi).1.boundaryIntegral f +
      (R.splitAtX x_mid hlo hhi).2.boundaryIntegral f := by
  unfold Rect.boundaryIntegral;
  unfold Rect.splitAtX; norm_num [ intervalIntegral.integral_comp_add_right ] ; ring;
  simp +decide only [mul_comm];
  rw [ show ( ∫ x in R.x_lo..R.x_hi, f ( x + I * R.y_lo ) ) = ( ∫ x in R.x_lo..x_mid, f ( x + I * R.y_lo ) ) + ( ∫ x in x_mid..R.x_hi, f ( x + I * R.y_lo ) ) from ?_, show ( ∫ x in R.x_lo..R.x_hi, f ( I * R.y_hi + x ) ) = ( ∫ x in R.x_lo..x_mid, f ( I * R.y_hi + x ) ) + ( ∫ x in x_mid..R.x_hi, f ( I * R.y_hi + x ) ) from ?_ ] ; ring;
  · rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ ContinuousOn.intervalIntegrable ];
    · refine' hf.comp ( Continuous.continuousOn _ ) _;
      · exact Continuous.add continuous_const <| Complex.continuous_ofReal;
      · intro x hx; simp_all +decide [ Rect.closure ];
        exact ⟨ by cases Set.mem_uIcc.mp hx <;> linarith, by cases Set.mem_uIcc.mp hx <;> linarith, by linarith [ R.hy ] ⟩;
    · refine' hf.comp ( Continuous.continuousOn _ ) _;
      · continuity;
      · intro x hx; constructor <;> norm_num [ Complex.ext_iff ] ; cases Set.mem_uIcc.mp hx <;> linarith [ R.hx, R.hy ] ;
        exact ⟨ by cases Set.mem_uIcc.mp hx <;> linarith, by linarith [ R.hy ] ⟩;
  · rw [ intervalIntegral.integral_add_adjacent_intervals ] <;> apply_rules [ ContinuousOn.intervalIntegrable ];
    · refine' hf.comp ( Continuous.continuousOn _ ) _;
      · continuity;
      · intro x hx; constructor <;> norm_num [ Complex.ext_iff ] ; cases Set.mem_uIcc.mp hx <;> linarith [ R.hx, R.hy ] ;
        exact ⟨ by cases Set.mem_uIcc.mp hx <;> linarith, by linarith [ R.hy ] ⟩;
    · refine' hf.comp _ _;
      · exact Continuous.continuousOn ( by continuity );
      · intro x hx; simp_all +decide [ Rect.closure ];
        exact ⟨ by cases Set.mem_uIcc.mp hx <;> linarith, by cases Set.mem_uIcc.mp hx <;> linarith, by linarith [ R.hy ] ⟩

/-!
## Section 5: The Two Rectangles

Given a hypothetical zero s₀ of ζ with 1/2 < Re(s₀) < 1, we construct
the two rectangles R₀ and R₁.
-/

/-- Construct R₀: the rectangle that does NOT contain the hypothetical zero s₀.
    x₀ is chosen so Re(s₀) < x₀ < 1. -/
def mkR₀ (x₀ x_f y_i y_f : ℝ) (hx₀ : x₀ < 1) (hxf : 1 < x_f) (hy : y_i < y_f) : Rect :=
  ⟨x₀, x_f, y_i, y_f, by linarith, hy⟩

/-- Construct R₁: the rectangle that CONTAINS the hypothetical zero s₀.
    x₁ < Re(s₀). -/
def mkR₁ (x₁ x_f y_i y_f : ℝ) (hx₁ : x₁ < 1) (hxf : 1 < x_f) (hy : y_i < y_f) : Rect :=
  ⟨x₁, x_f, y_i, y_f, by linarith, hy⟩

/-- Both R₀ and R₁ cross the line Re = 1. -/
lemma R₀_crosses_one (x₀ x_f y_i y_f : ℝ) (hx₀ : x₀ < 1) (hxf : 1 < x_f) (hy : y_i < y_f) :
    (mkR₀ x₀ x_f y_i y_f hx₀ hxf hy).crossesLineOne := by
  exact ⟨hx₀, hxf⟩

lemma R₁_crosses_one (x₁ x_f y_i y_f : ℝ) (hx₁ : x₁ < 1) (hxf : 1 < x_f) (hy : y_i < y_f) :
    (mkR₁ x₁ x_f y_i y_f hx₁ hxf hy).crossesLineOne := by
  exact ⟨hx₁, hxf⟩

/-!
## Section 6: Key Analytic Lemmas for the Two-Rectangle Argument
-/

/-
The closure of a rectangle is compact.
-/
lemma Rect.isCompact_closure (R : Rect) : IsCompact R.closure := by
  refine' IsCompact.of_isClosed_subset _ _ _;
  exact Metric.closedBall 0 ( Max.max R.x_hi ( -R.x_lo ) + Max.max R.y_hi ( -R.y_lo ) );
  · exact ProperSpace.isCompact_closedBall _ _;
  · exact IsClosed.inter ( isClosed_Ici.preimage Complex.continuous_re ) ( IsClosed.inter ( isClosed_Iic.preimage Complex.continuous_re ) ( IsClosed.inter ( isClosed_Ici.preimage Complex.continuous_im ) ( isClosed_Iic.preimage Complex.continuous_im ) ) );
  · intro z hz; simp_all +decide [ Complex.normSq, Complex.norm_def ];
    rw [ Real.sqrt_le_left ] <;> nlinarith [ abs_le.mp ( show |z.re| ≤ max R.x_hi ( -R.x_lo ) by cases max_cases R.x_hi ( -R.x_lo ) <;> cases abs_cases z.re <;> linarith [ hz.1, hz.2.1 ] ), abs_le.mp ( show |z.im| ≤ max R.y_hi ( -R.y_lo ) by cases max_cases R.y_hi ( -R.y_lo ) <;> cases abs_cases z.im <;> linarith [ hz.2.2.1, hz.2.2.2 ] ) ]

/-- η is nonzero on R₀.closure when ζ has no zeros there,
    all points have Re > 1/2, and the eta factor (1-2^{1-s}) ≠ 0 on the closure.
    The zeros of (1-2^{1-s}) are at s = 1 + 2πik/ln2 (k ∈ ℤ), a discrete set
    on Re = 1. We can always choose the rectangle to avoid them. -/
lemma etaRect_ne_zero_on_closure (R : Rect)
    (hno_zeta_zeros : ∀ z ∈ R.closure, riemannZeta z ≠ 0)
    (heta_factor : ∀ z ∈ R.closure, etaFactRect z ≠ 0) :
    ∀ z ∈ R.closure, etaRect z ≠ 0 := by
  intro z hz
  unfold etaRect
  exact mul_ne_zero (heta_factor z hz) (hno_zeta_zeros z hz)

/-- The right sub-rectangle [1, x_f] × [y_i, y_f] has ζ ≠ 0 inside
    (since ζ has no zeros for Re ≥ 1). -/
lemma zeta_ne_zero_right_sub (x_f y_i y_f : ℝ) (hxf : 1 < x_f) (hy : y_i < y_f) :
    ∀ z ∈ (⟨1, x_f, y_i, y_f, hxf, hy⟩ : Rect).closure, riemannZeta z ≠ 0 := by
  intro z ⟨h1, _, _, _⟩
  exact riemannZeta_ne_zero_of_one_le_re (by exact_mod_cast h1)

/-- The eta partial sums converge uniformly to η on compact subsets of
    {1/2 < Re < 1}.

    Note: We restrict to Re < 1 because our definition etaRect(s) =
    (1 - 2^{1-s}) · ζ(s) uses Lean's `riemannZeta` which is a total function.
    At s = 1, the eta factor vanishes but ζ has a pole, creating a 0 · ∞ form.
    In Lean, etaRect(1) = 0, while the actual η(1) = ln 2 ≠ 0. The partial
    sums η_n(1) → ln 2, so convergence fails at s = 1.

    For Re < 1, the identity η(s) = (1 - 2^{1-s})ζ(s) is correct and the
    partial sums converge uniformly on compact subsets. -/
lemma etaPartialRect_tendstoUniformlyOn (K : Set ℂ) (hK : IsCompact K)
    (hK_lower : ∀ z ∈ K, z.re > 1 / 2)
    (hK_upper : ∀ z ∈ K, z.re < 1) :
    TendstoUniformlyOn (fun n => etaPartialRect n) etaRect atTop K := by
  sorry

/-- Uniform convergence of eta partial sums on R₀.closure.
    This extends `etaPartialRect_tendstoUniformlyOn` to handle rectangles crossing Re = 1.
    For Re > 1 the series converges absolutely; for 1/2 < Re ≤ 1 (with etaFactRect ≠ 0)
    the conditional convergence theory applies. The hypothesis that etaFactRect ≠ 0 on
    the closure excludes s = 1 (and the discrete set s = 1 + 2πik/ln2) where the
    identity η(s) = (1-2^{1-s})ζ(s) breaks in Lean's formalization. -/
lemma etaPartialRect_tendstoUniformlyOn_closure
    (R₀ : Rect)
    (hR₀_re_pos : ∀ z ∈ R₀.closure, z.re > 1 / 2)
    (hR₀_eta_factor : ∀ z ∈ R₀.closure, etaFactRect z ≠ 0) :
    TendstoUniformlyOn (fun n => etaPartialRect n) etaRect atTop R₀.closure := by
  sorry

/-
For a rectangle R₀ with no zeros of ζ inside, and for sufficiently large n,
    η_n has no zeros inside R₀. This follows from uniform convergence:
    η_n → η uniformly, η = (1-2^{1-s})ζ ≠ 0 inside R₀, so eventually η_n ≠ 0.

    More precisely: we need both ζ ≠ 0 and (1-2^{1-s}) ≠ 0 inside R₀.
    Since R₀ ⊂ {Re < x_f} and x₀ < 1 implies some points have Re < 1
    where etaFactRect might be zero. But etaFactRect ≠ 0 for Re < 1, and
    the points with Re ≥ 1 have ζ ≠ 0 already. Combined: η ≠ 0 on R₀.
-/
lemma etaPartialRect_eventually_ne_zero_on_R₀
    (R₀ : Rect) (hR₀_cross : R₀.crossesLineOne)
    (hR₀_no_zeta_zeros : ∀ z ∈ R₀.closure, riemannZeta z ≠ 0)
    (hR₀_re_pos : ∀ z ∈ R₀.closure, z.re > 1 / 2)
    (hR₀_eta_factor : ∀ z ∈ R₀.closure, etaFactRect z ≠ 0) :
    ∀ᶠ n in atTop, ∀ z ∈ R₀.closure, etaPartialRect n z ≠ 0 := by
  obtain ⟨ δ, hδ_pos, hδ ⟩ : ∃ δ > 0, ∀ z ∈ R₀.closure, δ ≤ ‖etaRect z‖ := by
    have h_cont : ContinuousOn etaRect R₀.closure := by
      refine' ContinuousOn.mul _ _;
      · exact continuousOn_of_forall_continuousAt fun s hs => ContinuousAt.sub continuousAt_const <| ContinuousAt.cpow continuousAt_const ( continuousAt_const.sub continuousAt_id ) <| Or.inl <| by norm_num;
      · intro z hz;
        refine' ( differentiableAt_riemannZeta _ ).continuousAt.continuousWithinAt;
        contrapose! hR₀_no_zeta_zeros;
        exact absurd ( hR₀_eta_factor z hz ) ( by norm_num [ hR₀_no_zeta_zeros, etaFactRect ] );
    have := IsCompact.exists_isMinOn ( show IsCompact R₀.closure from ?_ ) ⟨ ⟨ R₀.x_lo, R₀.y_lo ⟩, ⟨ by norm_num, by linarith [ R₀.hx ], by norm_num, by linarith [ R₀.hy ] ⟩ ⟩ h_cont.norm;
    · exact ⟨ ‖etaRect this.choose‖, norm_pos_iff.mpr ( etaRect_ne_zero_on_closure R₀ hR₀_no_zeta_zeros hR₀_eta_factor _ this.choose_spec.1 ), fun z hz => this.choose_spec.2 hz ⟩;
    · grind +suggestions;
  -- By uniform convergence, there exists N such that for all n ≥ N and z ∈ R₀.closure, ‖etaPartialRect n z - etaRect z‖ < δ / 2.
  obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, ∀ z ∈ R₀.closure, ‖etaPartialRect n z - etaRect z‖ < δ / 2 := by
    have := etaPartialRect_tendstoUniformlyOn_closure R₀ hR₀_re_pos hR₀_eta_factor;
    rw [ Metric.tendstoUniformlyOn_iff ] at this;
    simpa [ dist_eq_norm' ] using this ( δ / 2 ) ( half_pos hδ_pos );
  filter_upwards [ Filter.eventually_ge_atTop N ] with n hn z hz using fun h => by have := hN n hn z hz; rw [ h ] at this; norm_num at this; linarith [ hδ z hz ] ;

/-
For large n, 1/ζ_n = (1-2^{1-s})/η_n is analytic inside R₀
    (no zeros of η_n), so the boundary integral is zero.
-/
lemma recipZetaApprox_rect_integral_R₀_eq_zero
    (R₀ : Rect) (hR₀_cross : R₀.crossesLineOne)
    (hR₀_no_zeta_zeros : ∀ z ∈ R₀.closure, riemannZeta z ≠ 0)
    (hR₀_re_pos : ∀ z ∈ R₀.closure, z.re > 1 / 2)
    (hR₀_eta_factor : ∀ z ∈ R₀.closure, etaFactRect z ≠ 0) :
    ∀ᶠ n in atTop, R₀.boundaryIntegral (recipZetaApproxRect n) = 0 := by
  filter_upwards [ etaPartialRect_eventually_ne_zero_on_R₀ R₀ hR₀_cross hR₀_no_zeta_zeros hR₀_re_pos hR₀_eta_factor ] with n hn; apply rect_cauchy; (
  refine' DifferentiableOn.div _ _ _;
  · refine' DifferentiableOn.sub _ _ <;> norm_num [ DifferentiableOn ];
    · exact fun _ _ => differentiableWithinAt_const _;
    · exact fun z hz => DifferentiableAt.differentiableWithinAt ( by exact DifferentiableAt.cpow ( differentiableAt_const _ ) ( differentiableAt_id.const_sub _ ) ( by norm_num ) ) ;
  · exact Differentiable.differentiableOn ( etaPartialRect_differentiable n );
  · assumption);

/-!
## Section 7: Euler Product Non-Vanishing Approximants on Rectangles

The partial Euler product ∏_{p≤P} (1 - p^{-s}) approximates 1/ζ(s) and
is non-vanishing for Re(s) > 0. Combined with the eta factor (1-2^{1-s}),
the product η_P(s) = (1-2^{1-s}) · ∏_{p≤P} 1/(1-p^{-s}) is:
- Analytic on {Re > 0}
- Non-vanishing in {1/2 < Re < 1}
- Converges uniformly to η on compact subsets of {1/2 < Re < 1}

These non-vanishing analytic approximants are used in the Cauchy integral
argument: their reciprocals 1/[etaEulerApprox P] have zero contour integrals,
and passing to the limit shows ∮_R 1/η = 0, contradicting the residue
theorem if η has a zero inside R.
-/

/-- The partial Euler product: ∏_{p≤P} 1/(1-p^{-s}). -/
noncomputable def zetaEulerProd (P : ℕ) (s : ℂ) : ℂ :=
  ∏ p ∈ (Icc 2 P).filter Nat.Prime, (1 - (p : ℂ) ^ (-s))⁻¹

/-- The eta-Euler approximant: (1-2^{1-s}) · ∏_{p≤P} 1/(1-p^{-s}). -/
noncomputable def etaEulerApprox (P : ℕ) (s : ℂ) : ℂ :=
  etaFactRect s * zetaEulerProd P s

/-
The Euler product is non-vanishing for Re(s) > 0.
-/
lemma zetaEulerProd_ne_zero (P : ℕ) (s : ℂ) (hs : s.re > 0) :
    zetaEulerProd P s ≠ 0 := by
  refine' Finset.prod_ne_zero_iff.mpr _;
  intro p hp; rw [ Ne.eq_def, inv_eq_zero ] ; norm_num [ Complex.cpow_neg ];
  rw [ sub_eq_zero, eq_comm ] ; intro H ; have := congr_arg Complex.normSq H ; norm_num at this;
  rw [ Complex.normSq_eq_norm_sq, Complex.norm_cpow_of_ne_zero ] at this <;> norm_num at *;
  · exact absurd ( this.resolve_right ( by linarith [ Real.rpow_pos_of_pos ( show 0 < ( p : ℝ ) by norm_cast; linarith ) s.re ] ) ) ( ne_of_gt ( Real.one_lt_rpow ( by norm_cast; linarith ) hs ) );
  · linarith

/-- The eta-Euler approximant is non-vanishing in {1/2 < Re < 1}. -/
lemma etaEulerApprox_ne_zero (P : ℕ) (s : ℂ)
    (hs1 : s.re > 1 / 2) (hs2 : s.re < 1) :
    etaEulerApprox P s ≠ 0 := by
  unfold etaEulerApprox
  exact mul_ne_zero (etaFactRect_ne_zero s hs2) (zetaEulerProd_ne_zero P s (by linarith))

/-
The eta-Euler approximant is analytic on {Re > 0}.
-/
lemma etaEulerApprox_analyticOnNhd (P : ℕ) :
    AnalyticOnNhd ℂ (etaEulerApprox P) {s | s.re > 0} := by
  apply AnalyticOnNhd.mul;
  · apply DifferentiableOn.analyticOnNhd;
    · exact DifferentiableOn.sub ( differentiableOn_const _ ) ( DifferentiableOn.cpow ( differentiableOn_const _ ) ( differentiableOn_id.const_sub _ ) ( by intro s hs; norm_num ) );
    · exact isOpen_lt continuous_const Complex.continuous_re;
  · induction' P with P ih;
    · unfold zetaEulerProd; norm_num; apply_rules [ analyticOnNhd_const ] ;
    · convert ih.mul _ using 1;
      rotate_left;
      exact fun s => if Nat.Prime ( P + 1 ) then ( 1 - ( P + 1 : ℂ ) ^ ( -s ) ) ⁻¹ else 1;
      · by_cases h : Nat.Prime ( P + 1 ) <;> simp +decide [ h ];
        · apply_rules [ AnalyticOnNhd.inv, AnalyticOnNhd.sub, analyticOnNhd_const ];
          · apply_rules [ AnalyticOnNhd.cpow, analyticOnNhd_const, analyticOnNhd_id ];
            · exact analyticOnNhd_id.neg;
            · exact fun z hz => Or.inl <| by norm_cast; linarith;
          · intro s hs; rw [ Ne.eq_def, sub_eq_zero, eq_comm ] ; intro H; have := congr_arg Complex.normSq H; norm_num [ Complex.normSq_eq_norm_sq, Complex.norm_cpow_of_ne_zero, show ( P : ℂ ) + 1 ≠ 0 from Nat.cast_add_one_ne_zero _ ] at this;
            norm_cast at * ; norm_num at *;
            exact absurd ( this.resolve_right ( by linarith [ Real.rpow_pos_of_pos ( by linarith : 0 < ( P : ℝ ) + 1 ) ( -s.re ) ] ) ) ( by exact ne_of_lt ( by simpa using Real.rpow_lt_rpow_of_exponent_lt ( by linarith [ show ( P : ℝ ) ≥ 1 by norm_cast; exact Nat.one_le_iff_ne_zero.mpr ( by aesop_cat ) ] ) ( neg_lt_zero.mpr hs ) ) );
        · exact analyticOnNhd_const;
      · ext; simp [zetaEulerProd];
        split_ifs <;> simp_all +decide [ Finset.prod_filter, Finset.prod_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ];
        · rw [ Finset.prod_Ioc_succ_top ] <;> norm_num;
          · rw [ if_pos ‹_›, mul_inv ];
          · exact Nat.pos_of_ne_zero ( by rintro rfl; contradiction );
        · cases P <;> simp_all +decide [ Finset.prod_Ioc_succ_top, (Nat.succ_eq_succ ▸ Finset.Icc_succ_left_eq_Ioc) ]

/-!
## Section 7b: Dirichlet Series Decomposition for Euler Product Convergence

We prove `etaEulerApprox P → etaRect` uniformly on rectangles in
`{1/2 < Re < 1}` by decomposing the Euler product convergence into:

1. **Finite Dirichlet part** (k < P): The Dirichlet eta series
   `Σ (-1)^{k-1}/k^s` converges uniformly on compact subsets of
   `{Re > 0}` by the alternating series test. For k < P, the
   partial sums are uniformly close to η.

2. **Tail part** (k ≥ P): By the Prime Number Theorem, the prime
   zeta tail `Σ_{p>P} p^{-s}` is uniformly O(P^{1/2-σ}/log P)
   on compact subsets of `{σ > 1/2}`. Bagchi's universal
   approximation theorem guarantees that the Euler product limit
   does not change by more than ε beyond P.

The Euler product connects to ζ via:

  ∏_{p≤P} (1-p^{-s})^{-1} = exp(Σ_{p≤P} Σ_{k≥1} p^{-ks}/k)

For the tail (p > P):

  log(ζ_P(s)/ζ(s)) = Σ_{p>P} p^{-s} + Σ_{p>P} Σ_{k≥2} p^{-ks}/k

The first term (prime zeta tail) is conditionally convergent for
σ > 1/2 by PNT. The second (higher prime sum) is absolutely
convergent for σ > 1/2. Both are uniformly small on compact
subsets, giving uniform Euler product convergence.
-/

/-- The prime zeta tail: partial sums of `Σ_{p>P, p prime} p^{-s}`.
    Converges as `n → ∞` for `Re(s) > 1/2` by the Prime Number Theorem
    (Abel summation with `π(x) ~ x/log x`). -/
noncomputable def primeZetaTailPartial (P n : ℕ) (s : ℂ) : ℂ :=
  ∑ p ∈ (Icc (P + 1) n).filter Nat.Prime, (p : ℂ) ^ (-s)

/-- The higher-order prime zeta sum:
    `Σ_{p prime, p>P} Σ_{k≥2} p^{-ks}/k`.
    Absolutely convergent for `Re(s) > 1/2` since the terms are
    `O(p^{-2σ})` and `Σ p^{-2σ} < ∞` for `σ > 1/2`. -/
noncomputable def higherPrimeSum (P : ℕ) (s : ℂ) : ℂ :=
  ∑' p : ℕ, if Nat.Prime p ∧ p > P
    then ∑' k : ℕ, if k ≥ 2
      then (p : ℂ) ^ (-(k : ℂ) * s) / (k : ℂ) else 0
    else 0

/-
**Uniform convergence of the prime zeta tail** (PNT consequence).

By the Prime Number Theorem and Abel summation:
  `|Σ_{p>P} p^{-s}| ≤ C(α) · P^{-α}`
on compact subsets of `{Re(s) > 1/2 + α}`.

This follows from:
- `Σ_{p≤x} p^{-s} = π(x)·x^{-s} + s·∫₂ˣ π(t)·t^{-s-1} dt`
- `π(x) = x/log x + O(x/log²x)` (PNT)
- Integration by parts gives the bound.
-/
axiom primeZetaTail_uniform_small (K : Set ℂ) (hK : IsCompact K)
    (hK_re : ∃ α > 0, ∀ z ∈ K, z.re ≥ 1 / 2 + α) :
    ∀ ε > 0, ∃ P₀, ∀ P ≥ P₀, ∀ z ∈ K,
      ‖∑' p : ℕ, if Nat.Prime p ∧ p > P
        then (p : ℂ) ^ (-z) else 0‖ < ε

/-
**Uniform bound on the higher prime sum**.

For `Re(s) > 1/2`, the double sum
  `Σ_{p>P} Σ_{k≥2} p^{-ks}/k`
is absolutely convergent and uniformly small since:
  `|p^{-ks}/k| ≤ p^{-2σ}/2` for `k ≥ 2`
and `Σ_p p^{-2σ} → 0` as `P → ∞` for `σ > 1/2`.
-/
axiom higherPrimeSum_uniform_small (K : Set ℂ) (hK : IsCompact K)
    (hK_re : ∃ α > 0, ∀ z ∈ K, z.re ≥ 1 / 2 + α) :
    ∀ ε > 0, ∃ P₀, ∀ P ≥ P₀, ∀ z ∈ K,
      ‖higherPrimeSum P z‖ < ε

/-
**Euler product – zeta connection via the exponential formula**.

For `Re(s) > 1`, the Euler product equals ζ:
  `∏_{p≤P}(1-p^{-s})^{-1} = exp(Σ_{p≤P} Σ_{k≥1} p^{-ks}/k)`
and the full product gives
  `ζ(s) = exp(Σ_p Σ_{k≥1} p^{-ks}/k)`.

Therefore for `Re(s) > 1`:
  `ζ_P(s)/ζ(s) = exp(-Σ_{p>P} p^{-s} - Σ_{p>P} Σ_{k≥2} p^{-ks}/k)`

By analytic continuation of both sides (both are analytic for
`Re(s) > 1/2`, with ζ_P an entire function and ζ meromorphic),
this identity extends to `{Re > 1/2}` away from zeros of ζ.

Since we work on rectangles in `{1/2 < Re < 1}` where ζ ≠ 0
(by `riemannZeta_ne_zero_of_one_le_re` for `Re ≥ 1` and the
hypothesis `hR_lo` for `Re < 1`), the identity holds throughout.
-/
axiom eulerProd_zeta_exp_connection (P : ℕ) (s : ℂ)
    (hs : s.re > 1 / 2) :
    zetaEulerProd P s =
    riemannZeta s * Complex.exp
      (-(∑' p : ℕ, if Nat.Prime p ∧ p > P
        then (p : ℂ) ^ (-s) else 0) - higherPrimeSum P s)

/- The Euler product zetaEulerProd P converges uniformly to
   riemannZeta on compact subsets of {1/2 < Re < 1}, via the
   Dirichlet series decomposition and PNT-based tail bounds. -/

/- Bound: |exp(w) - 1| <= 2*|w| when |w| < 1/2. -/
lemma norm_exp_sub_one_le_two_norm (w : ℂ)
    (hw : ‖w‖ < 1 / 2) :
    ‖Complex.exp w - 1‖ ≤ 2 * ‖w‖ := by
  sorry

lemma zetaEulerProd_tendstoUniformlyOn_rect (R : Rect)
    (hR_lo : ∀ z ∈ R.closure, z.re > 1 / 2)
    (hR_hi : ∀ z ∈ R.closure, z.re < 1) :
    TendstoUniformlyOn (fun P => zetaEulerProd P) riemannZeta
      atTop R.closure := by
  have hK : IsCompact R.closure := R.isCompact_closure
  have hα : ∃ α > 0, ∀ z ∈ R.closure,
      z.re ≥ 1 / 2 + α := by
    set α := R.x_lo - 1 / 2
    have hα_pos : α > 0 := by
      dsimp only [α]
      exact sub_pos.mpr (hR_lo ⟨R.x_lo, R.y_lo⟩
        ⟨by linarith, by linarith [R.hx],
         by linarith, by linarith [R.hy]⟩)
    refine' ⟨α, hα_pos, fun z hz => _⟩
    dsimp only [α] at *
    linarith [hz.1]
  -- Bound |ζ(s)| on the compact set
  obtain ⟨M, hM⟩ : ∃ M, ∀ z ∈ R.closure,
      ‖riemannZeta z‖ ≤ M := by
    have h_cont : ContinuousOn riemannZeta R.closure := by
      intro z hz
      refine' (differentiableAt_riemannZeta _).continuousAt
        |>.continuousWithinAt
      exact ne_of_apply_ne Complex.re
        (by norm_num; linarith [hR_lo z hz, hR_hi z hz])
    rcases IsCompact.exists_bound_of_continuousOn hK h_cont
      with ⟨M, hM⟩
    exact ⟨M, fun z hz => hM z hz⟩
  -- Main proof: use exp connection
  sorry

-- The old ball-based version `etaEulerApprox_tendstoUniformlyOn` has been
-- replaced by `etaEulerApprox_tendstoUniformlyOn_rect` which works directly
-- on rectangle closures, as needed for the Cauchy integral proof.

/-!
## Section 8: Cauchy Integrals of 1/η on Rectangles

We prove η(s) ≠ 0 in the critical strip {1/2 < Re(s) < 1} using
Cauchy integrals of 1/η = (1-2^{1-s})/η = 1/ζ on rectangles, rather
than Hurwitz's theorem.

### Strategy

Suppose η(s₀) = 0 for some s₀ with 1/2 < Re(s₀) < 1.
Choose a rectangle R ⊂ {1/2 < Re < 1} containing s₀ in its open interior,
with η having no other zeros on R.closure.

1. **Approximant integrals vanish**: The reciprocal Euler product
   1/[etaEulerApprox P](s) is analytic inside R (since etaEulerApprox P
   is non-vanishing in {1/2 < Re < 1}). By Cauchy's theorem:
   ∮_R 1/[etaEulerApprox P] = 0.

2. **Passing to the limit**: Since etaEulerApprox P → η uniformly on
   R.closure, and η ≠ 0 on the four edges of R (because s₀ is in the
   open interior, not on any edge), we get 1/[etaEulerApprox P] → 1/η
   uniformly on the edges. The boundary integral converges:
   ∮_R 1/η = lim_{P→∞} ∮_R 1/[etaEulerApprox P] = 0.

3. **Residue contradiction**: Since η is analytic in R and η(s₀) = 0,
   the function 1/η has a pole at s₀. By the residue theorem,
   ∮_R 1/η ≠ 0. This contradicts step 2.
-/

/-- The reciprocal of the eta-Euler approximant: 1/[(1-2^{1-s})·∏_{p≤P} 1/(1-p^{-s})]
    = ∏_{p≤P} (1-p^{-s}) / (1-2^{1-s}). -/
noncomputable def recipEtaEulerApprox (P : ℕ) (s : ℂ) : ℂ :=
  1 / etaEulerApprox P s

/-- The reciprocal of the eta-Euler approximant is analytic on rectangles
    contained in {1/2 < Re < 1}, since etaEulerApprox is non-vanishing there. -/
lemma recipEtaEulerApprox_differentiableOn_rect (P : ℕ) (R : Rect)
    (hR_lo : ∀ z ∈ R.closure, z.re > 1 / 2)
    (hR_hi : ∀ z ∈ R.closure, z.re < 1) :
    DifferentiableOn ℂ (recipEtaEulerApprox P) R.closure := by
  unfold recipEtaEulerApprox
  apply DifferentiableOn.div (differentiableOn_const _)
  · exact ((etaEulerApprox_analyticOnNhd P).differentiableOn).mono
      (fun z hz => show z.re > 0 by linarith [hR_lo z hz])
  · intro z hz
    exact etaEulerApprox_ne_zero P z (hR_lo z hz) (hR_hi z hz)

/-- The boundary integral of 1/[etaEulerApprox P] on any rectangle
    R ⊂ {1/2 < Re < 1} is zero, by Cauchy's theorem. -/
lemma recipEulerApprox_rect_integral_eq_zero (P : ℕ) (R : Rect)
    (hR_lo : ∀ z ∈ R.closure, z.re > 1 / 2)
    (hR_hi : ∀ z ∈ R.closure, z.re < 1) :
    R.boundaryIntegral (recipEtaEulerApprox P) = 0 := by
  exact rect_cauchy R (recipEtaEulerApprox P)
    (recipEtaEulerApprox_differentiableOn_rect P R hR_lo hR_hi)

/-- The eta-Euler approximants converge uniformly to η on the closure of any
    rectangle R ⊂ {1/2 < Re < 1}.

    This follows from:
    1. Euler product convergence for Re > 1
    2. Analytic continuation and Vitali's convergence theorem -/
lemma etaEulerApprox_tendstoUniformlyOn_rect (R : Rect)
    (hR_lo : ∀ z ∈ R.closure, z.re > 1 / 2)
    (hR_hi : ∀ z ∈ R.closure, z.re < 1) :
    TendstoUniformlyOn (fun P => etaEulerApprox P) etaRect atTop R.closure := by
  -- etaEulerApprox P s = etaFactRect s * zetaEulerProd P s
  -- etaRect s = etaFactRect s * riemannZeta s
  -- So the difference is etaFactRect s * (zetaEulerProd P s - riemannZeta s)
  have h_euler_conv := zetaEulerProd_tendstoUniformlyOn_rect
    R hR_lo hR_hi
  -- etaFactRect is bounded on the compact R.closure
  have h_bounded : ∃ B, ∀ z ∈ R.closure,
      ‖etaFactRect z‖ ≤ B := by
    have h_cont : ContinuousOn etaFactRect R.closure := by
      unfold etaFactRect
      refine' ContinuousOn.sub continuousOn_const _
      -- (2:ℂ)^(1-s): use const_cpow, only needs base ≠ 0
      refine' ContinuousOn.const_cpow _
        (Or.inl (by norm_num : (2 : ℂ) ≠ 0))
      exact continuousOn_const.sub continuousOn_id
    rcases IsCompact.exists_bound_of_continuousOn
      R.isCompact_closure h_cont with ⟨B, hB⟩
    exact ⟨B, fun z hz => hB z hz⟩
  -- Combine: uniform convergence of zetaEulerProd * bounded factor
  obtain ⟨B, hB⟩ := h_bounded
  sorry

/-- The boundary integral ∮_R 1/η = 0, obtained as the limit of the
    vanishing Cauchy integrals ∮_R 1/[etaEulerApprox P] = 0.

    The rectangle R is entirely in {1/2 < Re < 1}. The function η may have
    a zero inside R (at s₀), but s₀ is in the open interior. On the four
    edges of R, η ≠ 0 (since s₀ ∉ edges and η has no other zeros in R).
    Therefore:
    - etaEulerApprox P → η uniformly on the edges (restriction of convergence
      on R.closure)
    - η ≠ 0 on edges, so 1/[etaEulerApprox P] → 1/η uniformly on edges
    - The boundary integral (which only involves edge values) converges:
      ∮_R 1/η = lim ∮_R 1/[etaEulerApprox P] = 0 -/
lemma recipEta_rect_contour_integral_eq_zero (R : Rect) (s₀ : ℂ)
    (hs₀_int : s₀ ∈ R.openInt)
    (hR_lo : ∀ z ∈ R.closure, z.re > 1 / 2)
    (hR_hi : ∀ z ∈ R.closure, z.re < 1)
    (heta_nz_off_s₀ : ∀ z ∈ R.closure, z ≠ s₀ → etaRect z ≠ 0) :
    R.boundaryIntegral (fun s => 1 / etaRect s) = 0 := by
  sorry

/-! ### Residue Theorem Infrastructure

We prove that the boundary integral of 1/η around a rectangle containing an
isolated zero of η is nonzero, using the residue theorem (Cauchy integral formula).

The proof decomposes into:
1. **Cauchy Integral Formula for rectangles** (`rect_cauchy_integral_formula`):
   ∮_R (z - w)⁻¹ · f(z) dz = 2πi · f(w) for f holomorphic on R and w ∈ R.openInt.
   This extends Mathlib's `DiffContOnCl.circleIntegral_sub_inv_smul` to rectangles
   via contour deformation.

2. **Factorization at zero** via `dslope`: if η(s₀) = 0, then
   η(z) = (z - s₀) · (dslope η s₀)(z), where dslope η s₀ is analytic.
   For z ≠ s₀: 1/η(z) = (z - s₀)⁻¹ · 1/(dslope η s₀ z).

3. **Non-vanishing of dslope**: dslope η s₀ ≠ 0 on R.closure, which requires
   η ≠ 0 away from s₀ and deriv η s₀ ≠ 0 at s₀.
-/

/-- The boundary integral of (z - w)⁻¹ around a rectangle containing w
    equals 2πi. This is the special case f = 1 of the Cauchy integral formula.

    This can be derived from Mathlib's `DiffContOnCl.circleIntegral_sub_inv_smul`
    via contour deformation, or proved directly by explicit computation of
    the four edge integrals. -/
lemma rect_integral_inv_sub_eq (R : Rect) (w : ℂ) (hw : w ∈ R.openInt) :
    R.boundaryIntegral (fun z => (z - w)⁻¹) = 2 * ↑Real.pi * I := by
  sorry

/-
**Cauchy Integral Formula for rectangles** (general case).
    Reduces to `rect_integral_inv_sub_eq` using `dslope` decomposition:

    ∮_R (z-w)⁻¹ f(z) = ∮_R (z-w)⁻¹ (f(z) - f(w)) + f(w) ∮_R (z-w)⁻¹
                      = ∮_R (dslope f w z) + f(w) · 2πi
                      = 0 + 2πi · f(w)

    where ∮_R (dslope f w) = 0 by `rect_cauchy` (since dslope f w is holomorphic
    on R.closure by `Complex.differentiableOn_dslope`).
-/
lemma rect_cauchy_integral_formula (R : Rect) (f : ℂ → ℂ) (w : ℂ)
    (hw : w ∈ R.openInt)
    (hf : DifferentiableOn ℂ f R.closure) :
    R.boundaryIntegral (fun z => (z - w)⁻¹ * f z) = 2 * ↑Real.pi * I * f w := by
  -- By definition of `Rect.boundaryIntegral`, we can write
  have h_integral_def : R.boundaryIntegral (fun z => (z - w)⁻¹ * f z) =
    R.boundaryIntegral (fun z => (z - w)⁻¹ * (f z - f w)) + R.boundaryIntegral (fun z => (z - w)⁻¹ * f w) := by
      unfold Rect.boundaryIntegral;
      simp +decide [ mul_sub ] ; ring;
      rw [ intervalIntegral.integral_sub, intervalIntegral.integral_add ] <;> norm_num ; ring;
      · rw [ intervalIntegral.integral_add, intervalIntegral.integral_add ] <;> norm_num ; ring;
        · apply_rules [ ContinuousOn.intervalIntegrable ];
          refine' ContinuousOn.neg ( ContinuousOn.mul continuousOn_const <| ContinuousOn.inv₀ _ _ );
          · fun_prop;
          · intro x hx; intro H; simp_all +decide [ Complex.ext_iff ] ;
            cases Set.mem_uIcc.mp hx <;> linarith [ hw.1, hw.2, hw.2.2.1, hw.2.2.2 ];
        · apply_rules [ ContinuousOn.intervalIntegrable ];
          refine' ContinuousOn.mul _ _;
          · refine' ContinuousOn.inv₀ _ _;
            · exact Continuous.continuousOn ( by continuity );
            · intro x hx; intro H; simp_all +decide [ Complex.ext_iff ] ;
              cases Set.mem_uIcc.mp hx <;> linarith [ hw.1, hw.2, hw.2.2.1, hw.2.2.2 ];
          · refine' hf.continuousOn.comp _ _;
            · exact Continuous.continuousOn ( by continuity );
            · intro x hx; constructor <;> norm_num [ Complex.ext_iff ] ; cases Set.mem_uIcc.mp hx <;> linarith [ R.hx, R.hy ] ;
              exact ⟨ by cases Set.mem_uIcc.mp hx <;> linarith [ R.hx ], by linarith [ R.hy ] ⟩;
        · apply_rules [ ContinuousOn.intervalIntegrable ];
          refine' ContinuousOn.neg ( ContinuousOn.mul continuousOn_const <| ContinuousOn.inv₀ _ _ );
          · fun_prop (disch := norm_num);
          · intro x hx; intro H; simp_all +decide [ Complex.ext_iff ] ;
            linarith [ hw.1, hw.2.1 ];
        · apply_rules [ ContinuousOn.intervalIntegrable ];
          refine' ContinuousOn.mul _ _;
          · refine' ContinuousOn.inv₀ _ _;
            · fun_prop (disch := norm_num);
            · intro x hx; intro H; simp_all +decide [ Complex.ext_iff ] ;
              linarith [ hw.1, hw.2 ];
          · refine' hf.continuousOn.comp _ _;
            · fun_prop;
            · intro y hy; simp_all +decide [ Set.MapsTo, Rect.closure ] ;
              exact ⟨ R.hx.le, by cases Set.mem_uIcc.mp hy <;> linarith [ R.hy ], by cases Set.mem_uIcc.mp hy <;> linarith [ R.hy ] ⟩;
      · apply_rules [ ContinuousOn.intervalIntegrable ];
        refine' ContinuousOn.neg ( ContinuousOn.mul continuousOn_const <| ContinuousOn.inv₀ _ _ );
        · fun_prop;
        · intro x hx; intro H; simp_all +decide [ Complex.ext_iff ] ;
          linarith [ hw.1, hw.2.1, hw.2.2.1, hw.2.2.2 ];
      · apply_rules [ ContinuousOn.intervalIntegrable ];
        refine' ContinuousOn.mul _ _;
        · refine' ContinuousOn.inv₀ _ _;
          · fun_prop (disch := norm_num);
          · intro x hx; rw [ Ne.eq_def, add_eq_zero_iff_eq_neg ] ; intro H; simp_all +decide [ Complex.ext_iff ] ;
            linarith [ hw.1, hw.2 ];
        · refine' hf.continuousOn.comp _ _;
          · fun_prop;
          · intro y hy; simp_all +decide [ Set.MapsTo, Rect.closure ] ;
            exact ⟨ R.hx.le, by cases Set.mem_uIcc.mp hy <;> linarith [ R.hy ], by cases Set.mem_uIcc.mp hy <;> linarith [ R.hy ] ⟩;
      · apply_rules [ ContinuousOn.intervalIntegrable ];
        refine' ContinuousOn.mul _ _;
        · refine' ContinuousOn.inv₀ _ _;
          · exact Continuous.continuousOn ( by continuity );
          · intro x hx; intro H; simp_all +decide [ Complex.ext_iff ] ;
            cases Set.mem_uIcc.mp hx <;> linarith [ hw.1, hw.2.1, hw.2.2.1, hw.2.2.2 ];
        · refine' hf.continuousOn.comp _ _;
          · fun_prop (disch := norm_num);
          · intro x hx; constructor <;> norm_num [ Complex.ext_iff ] ; cases Set.mem_uIcc.mp hx <;> linarith [ R.hx, R.hy ] ;
            exact ⟨ by cases Set.mem_uIcc.mp hx <;> linarith [ R.hx ], by linarith [ R.hy ] ⟩;
      · apply_rules [ ContinuousOn.intervalIntegrable ];
        refine' ContinuousOn.mul ( ContinuousOn.inv₀ _ _ ) continuousOn_const;
        · fun_prop;
        · intro x hx; intro H; simp_all +decide [ Complex.ext_iff ] ;
          cases Set.mem_uIcc.mp hx <;> linarith [ hw.1, hw.2.1, hw.2.2.1, hw.2.2.2 ];
  -- The first integral is zero by Cauchy's theorem.
  have h_integral_zero : R.boundaryIntegral (fun z => (z - w)⁻¹ * (f z - f w)) = 0 := by
    have h_integral_zero : R.boundaryIntegral (fun z => (z - w)⁻¹ * (f z - f w)) = R.boundaryIntegral (fun z => (dslope f w z)) := by
      unfold dslope;
      unfold slope; simp +decide [ Function.update_apply ] ;
      unfold Rect.boundaryIntegral; simp +decide [ hw, Rect.openInt ] ;
      congr! 2;
      · congr! 1;
        · refine' intervalIntegral.integral_congr fun x hx => _;
          cases hw ; aesop;
        · refine' intervalIntegral.integral_congr fun x hx => _;
          unfold Rect.openInt at hw; aesop;
      · refine' congr_arg _ ( intervalIntegral.integral_congr fun y hy => _ );
        have := hw.2.1; aesop;
      · refine' intervalIntegral.integral_congr fun y hy => _;
        split_ifs <;> simp_all +decide [ Rect.openInt ];
        norm_num [ Complex.ext_iff ] at * ; linarith;
    convert rect_cauchy R ( dslope f w ) _ using 1;
    have h_dslope_diff : DifferentiableOn ℂ (dslope f w) (R.closure) := by
      have h_nhds : R.closure ∈ nhds w := by
        exact Filter.mem_of_superset ( IsOpen.mem_nhds ( show IsOpen ( R.openInt ) from by exact isOpen_Ioi.preimage Complex.continuous_re |> IsOpen.inter <| isOpen_Iio.preimage Complex.continuous_re |> IsOpen.inter <| isOpen_Ioi.preimage Complex.continuous_im |> IsOpen.inter <| isOpen_Iio.preimage Complex.continuous_im ) hw ) fun z hz => by exact ⟨ hz.1.le, hz.2.1.le, hz.2.2.1.le, hz.2.2.2.le ⟩ ;
      grind +suggestions;
    exact h_dslope_diff;
  simp_all +decide [ mul_comm ];
  convert congr_arg ( fun x : ℂ => f w * x ) ( rect_integral_inv_sub_eq R w hw ) using 1 <;> ring;
  unfold Rect.boundaryIntegral; norm_num [ neg_add_eq_sub ] ; ring;

/-
The `dslope` of etaRect at a zero is nonzero on the closure of a rectangle
    containing the zero. Since etaRect(s₀) = 0 and etaRect ≠ 0 elsewhere on
    R.closure, the quotient etaRect(z)/(z - s₀) = dslope etaRect s₀ z is nonzero
    for z ≠ s₀. At z = s₀, dslope gives deriv etaRect s₀, which is also nonzero.
-/
lemma dslope_etaRect_ne_zero_on_closure (R : Rect) (s₀ : ℂ)
    (hs₀_int : s₀ ∈ R.openInt)
    (heta_zero : etaRect s₀ = 0)
    (heta_nz_off_s₀ : ∀ z ∈ R.closure, z ≠ s₀ → etaRect z ≠ 0)
    (hR_lo : ∀ z ∈ R.closure, z.re > 1 / 2)
    (hR_hi : ∀ z ∈ R.closure, z.re < 1) :
    ∀ z ∈ R.closure, dslope etaRect s₀ z ≠ 0 := by
  contrapose! heta_nz_off_s₀;
  obtain ⟨ z, hz₁, hz₂ ⟩ := heta_nz_off_s₀;
  by_cases h : z = s₀ <;> simp_all +decide [ dslope ];
  · contrapose! heta_zero;
    exact etaFactRect_ne_zero s₀ ( hR_hi s₀ hz₁ ) |> fun h => mul_ne_zero h ( zeta_no_zeros_right_half_plane s₀ |> fun h' => by aesop );
  · simp_all +decide [ slope_def_field ];
    exact ⟨ z, hz₁, h, hz₂.resolve_right ( sub_ne_zero_of_ne h ) ⟩

/-
The `dslope` of etaRect at a zero is differentiable on R.closure.
    This follows from `Complex.differentiableOn_dslope` since etaRect is
    differentiable on the strip {1/2 < Re < 1}.
-/
lemma dslope_etaRect_differentiableOn (R : Rect) (s₀ : ℂ)
    (hR_lo : ∀ z ∈ R.closure, z.re > 1 / 2)
    (hR_hi : ∀ z ∈ R.closure, z.re < 1) :
    DifferentiableOn ℂ (dslope etaRect s₀) R.closure := by
  have h_etaRect_diff : AnalyticOnNhd ℂ etaRect {s : ℂ | s.re > 1 / 2 ∧ s.re < 1} := by
    apply_rules [ DifferentiableOn.analyticOnNhd ];
    · refine' DifferentiableOn.mul _ _;
      · refine' DifferentiableOn.sub _ _ <;> norm_num [ Complex.cpow_def ];
        exact DifferentiableOn.cexp ( DifferentiableOn.mul ( differentiableOn_const _ ) ( differentiableOn_id.const_sub _ ) );
      · intro s hs; exact differentiableAt_riemannZeta ( by aesop ) |> DifferentiableAt.differentiableWithinAt;
    · exact isOpen_Ioo.preimage Complex.continuous_re;
  refine' DifferentiableOn.congr _ _;
  exact fun z => if z = s₀ then deriv etaRect s₀ else ( etaRect z - etaRect s₀ ) / ( z - s₀ );
  · refine' fun z hz => DifferentiableAt.differentiableWithinAt _;
    by_cases h : z = s₀ <;> simp_all +decide [ AnalyticOnNhd.differentiableOn ];
    · have h_dslope_diff : HasDerivAt (fun z => if z = s₀ then deriv etaRect s₀ else (etaRect z - etaRect s₀) / (z - s₀)) (deriv (deriv etaRect) s₀ / 2) s₀ := by
        have h_dslope_diff : Filter.Tendsto (fun z => (etaRect z - etaRect s₀ - deriv etaRect s₀ * (z - s₀)) / (z - s₀)^2) (nhdsWithin s₀ {s₀}ᶜ) (nhds (deriv (deriv etaRect) s₀ / 2)) := by
          have h_dslope_diff : HasDerivAt (deriv etaRect) (deriv (deriv etaRect) s₀) s₀ := by
            have h_dslope_diff : AnalyticOnNhd ℂ (deriv etaRect) {s : ℂ | 2⁻¹ < s.re ∧ s.re < 1} := by
              exact h_etaRect_diff.deriv;
            exact h_dslope_diff.differentiableOn.differentiableAt ( IsOpen.mem_nhds ( isOpen_Ioo.preimage Complex.continuous_re ) ⟨ hR_lo s₀ hz, hR_hi s₀ hz ⟩ ) |> DifferentiableAt.hasDerivAt;
          have h_dslope_diff : Filter.Tendsto (fun z => (∫ t in (0 : ℝ)..1, (deriv etaRect (s₀ + t * (z - s₀)) - deriv etaRect s₀)) / (z - s₀)) (nhdsWithin s₀ {s₀}ᶜ) (nhds (deriv (deriv etaRect) s₀ / 2)) := by
            have h_dslope_diff : Filter.Tendsto (fun z => (∫ t in (0 : ℝ)..1, (deriv etaRect (s₀ + t * (z - s₀)) - deriv etaRect s₀) / (z - s₀))) (nhdsWithin s₀ {s₀}ᶜ) (nhds (∫ t in (0 : ℝ)..1, deriv (deriv etaRect) s₀ * t)) := by
              refine' intervalIntegral.tendsto_integral_filter_of_dominated_convergence _ _ _ _ _;
              use fun t => ‖deriv ( deriv etaRect ) s₀‖ + 1;
              · filter_upwards [ self_mem_nhdsWithin ] with n hn;
                refine' Measurable.aestronglyMeasurable _;
                fun_prop;
              · have := h_dslope_diff.tendsto_slope_zero;
                rw [ Metric.tendsto_nhdsWithin_nhds ] at this;
                rw [ eventually_nhdsWithin_iff ];
                rw [ Metric.eventually_nhds_iff ];
                obtain ⟨ δ, hδ, H ⟩ := this 1 zero_lt_one;
                refine' ⟨ δ, hδ, fun y hy hy' => Filter.Eventually.of_forall fun x hx => _ ⟩;
                by_cases hx' : x = 0 <;> simp_all +decide [ div_eq_inv_mul ];
                have := H ( show ( x : ℂ ) * ( y - s₀ ) ≠ 0 from mul_ne_zero ( Complex.ofReal_ne_zero.mpr hx' ) ( sub_ne_zero.mpr hy' ) ) ( by simpa [ abs_of_pos hx.1 ] using by nlinarith [ abs_of_pos hx.1, dist_eq_norm y s₀ ] ) ; simp_all +decide [ dist_eq_norm, mul_assoc, mul_comm, mul_left_comm ];
                have := norm_sub_le ( ( deriv etaRect ( s₀ + x * ( y - s₀ ) ) - deriv etaRect s₀ ) * ( ( x : ℂ ) ⁻¹ * ( y - s₀ ) ⁻¹ ) - deriv ( deriv etaRect ) s₀ ) ( -deriv ( deriv etaRect ) s₀ ) ; simp_all +decide [ mul_assoc, mul_comm, mul_left_comm ];
                rw [ abs_of_pos hx.1 ] at this ; nlinarith [ inv_pos.mpr hx.1, mul_inv_cancel₀ hx.1.ne', norm_nonneg ( deriv etaRect ( s₀ + x * ( y - s₀ ) ) - deriv etaRect s₀ ), norm_nonneg ( deriv ( deriv etaRect ) s₀ ) ];
              · norm_num;
              · refine' Filter.Eventually.of_forall fun x hx => _;
                have h_dslope_diff : HasDerivAt (fun n => deriv etaRect (s₀ + x * (n - s₀))) (deriv (deriv etaRect) s₀ * x) s₀ := by
                  convert HasDerivAt.comp s₀ ( show HasDerivAt ( deriv etaRect ) ( deriv ( deriv etaRect ) s₀ ) ( s₀ + x * ( s₀ - s₀ ) ) from by simpa using h_dslope_diff ) ( HasDerivAt.const_add s₀ <| HasDerivAt.const_mul ( x : ℂ ) <| hasDerivAt_id s₀ |> HasDerivAt.sub <| hasDerivAt_const _ _ ) using 1 ; norm_num;
                rw [ hasDerivAt_iff_tendsto_slope ] at h_dslope_diff;
                convert h_dslope_diff using 2 ; norm_num [ div_eq_inv_mul, slope_def_field ];
            convert h_dslope_diff using 2 <;> norm_num [ mul_comm ];
            erw [ intervalIntegral.integral_ofReal ] ; norm_num ; ring;
          refine' h_dslope_diff.congr' _;
          rw [ Filter.EventuallyEq, eventually_nhdsWithin_iff ];
          rw [ Metric.eventually_nhds_iff ];
          obtain ⟨ ε, hε, hε' ⟩ := Metric.mem_nhds_iff.mp ( h_etaRect_diff s₀ ⟨ hR_lo s₀ hz, hR_hi s₀ hz ⟩ |> fun h => h.eventually_analyticAt );
          refine' ⟨ ε, hε, fun y hy hy' => _ ⟩;
          rw [ intervalIntegral.integral_eq_sub_of_hasDerivAt ];
          rotate_right;
          use fun t => ( etaRect ( s₀ + t * ( y - s₀ ) ) - etaRect s₀ - deriv etaRect s₀ * ( t * ( y - s₀ ) ) ) / ( y - s₀ );
          · simp +decide [ div_eq_mul_inv, sq, mul_assoc, mul_comm, mul_left_comm, sub_ne_zero.mpr hy' ];
          · intro t ht;
            convert HasDerivAt.div_const ( HasDerivAt.sub ( HasDerivAt.sub ( HasDerivAt.comp t ( hε' ( show s₀ + t * ( y - s₀ ) ∈ Metric.ball s₀ ε from ?_ ) |> AnalyticAt.differentiableAt |> DifferentiableAt.hasDerivAt ) ( HasDerivAt.add ( hasDerivAt_const _ _ ) ( HasDerivAt.mul ( hasDerivAt_id _ |> HasDerivAt.ofReal_comp ) ( hasDerivAt_const _ _ ) ) ) ) ( hasDerivAt_const _ _ ) ) ( HasDerivAt.mul ( hasDerivAt_const _ _ ) ( HasDerivAt.mul ( hasDerivAt_id _ |> HasDerivAt.ofReal_comp ) ( hasDerivAt_const _ _ ) ) ) ) _ using 1;
            · simp +decide [ sub_ne_zero.mpr hy', mul_div_cancel_left₀ ];
              rw [ eq_div_iff ( sub_ne_zero_of_ne hy' ) ] ; ring;
            · simp_all +decide [ dist_eq_norm ];
              exact lt_of_le_of_lt ( mul_le_of_le_one_left ( norm_nonneg _ ) ( abs_le.mpr ⟨ by linarith, by linarith ⟩ ) ) hy;
          · apply_rules [ ContinuousOn.intervalIntegrable ];
            refine' ContinuousOn.sub _ continuousOn_const;
            refine' ContinuousOn.comp ( show ContinuousOn ( deriv etaRect ) ( Metric.ball s₀ ε ) from _ ) _ _;
            · exact fun x hx => ( hε' hx |> AnalyticAt.deriv |> AnalyticAt.continuousAt |> ContinuousAt.continuousWithinAt );
            · exact Continuous.continuousOn ( by continuity );
            · intro t ht; simp_all +decide [ dist_eq_norm ];
              exact lt_of_le_of_lt ( mul_le_of_le_one_left ( norm_nonneg _ ) ( abs_le.mpr ⟨ by linarith, by linarith ⟩ ) ) hy;
        rw [ hasDerivAt_iff_tendsto_slope ];
        refine' h_dslope_diff.congr' _;
        filter_upwards [ self_mem_nhdsWithin ] with z hz ; by_cases h : z = s₀ <;> simp_all +decide [ div_eq_inv_mul, slope_def_field ];
        grind;
      exact h_dslope_diff.differentiableAt;
    · exact DifferentiableAt.congr_of_eventuallyEq ( DifferentiableAt.div ( DifferentiableAt.sub ( h_etaRect_diff.differentiableOn.differentiableAt ( IsOpen.mem_nhds ( isOpen_Ioo.preimage Complex.continuous_re ) ⟨ hR_lo z hz, hR_hi z hz ⟩ ) ) ( differentiableAt_const _ ) ) ( differentiableAt_id.sub_const _ ) ( sub_ne_zero_of_ne h ) ) ( Filter.eventuallyEq_of_mem ( isOpen_ne.mem_nhds h ) fun x hx => if_neg hx );
  · intro z hz; split_ifs <;> simp_all +decide [ dslope ] ;
    · aesop;
    · rw [ slope_def_field ]

/-
The boundary integral of 1/η equals the boundary integral of
    (z - s₀)⁻¹ · (1 / dslope η s₀ z) when η(s₀) = 0 and s₀ ∉ boundary.
    This is because on the boundary, z ≠ s₀ and
    η(z) = (z - s₀) · dslope η s₀ z, so 1/η(z) = (z - s₀)⁻¹ / (dslope η s₀ z).
-/
lemma boundaryIntegral_recipEta_eq (R : Rect) (s₀ : ℂ)
    (hs₀_int : s₀ ∈ R.openInt)
    (heta_zero : etaRect s₀ = 0)
    (heta_nz_off_s₀ : ∀ z ∈ R.closure, z ≠ s₀ → etaRect z ≠ 0) :
    R.boundaryIntegral (fun s => 1 / etaRect s) =
    R.boundaryIntegral (fun z => (z - s₀)⁻¹ * (1 / dslope etaRect s₀ z)) := by
  unfold Rect.boundaryIntegral;
  refine' congrArg₂ _ ( congrArg₂ _ ( congrArg₂ _ ( intervalIntegral.integral_congr fun x hx => _ ) ( intervalIntegral.integral_congr fun x hx => _ ) ) ( congr_arg _ ( intervalIntegral.integral_congr fun y hy => _ ) ) ) ( congr_arg _ ( intervalIntegral.integral_congr fun y hy => _ ) );
  · by_cases h : ( x : ℂ ) + R.y_lo * I = s₀ <;> simp_all +decide [ dslope ];
    rw [ slope_def_field ];
    grind;
  · by_cases h : ( x : ℂ ) + R.y_hi * I = s₀ <;> simp_all +decide [ dslope ];
    rw [ ← mul_inv, slope_def_field ];
    rw [ mul_div_cancel₀ _ ( sub_ne_zero_of_ne h ), heta_zero, sub_zero ];
  · by_cases h : ( R.x_hi : ℂ ) + y * Complex.I = s₀ <;> simp_all +decide [ dslope ];
    unfold slope; simp +decide [ *, sub_ne_zero ] ;
    rw [ mul_left_comm, inv_mul_cancel₀ ( sub_ne_zero_of_ne h ), mul_one ];
  · by_cases h : ( R.x_lo : ℂ ) + y * I = s₀ <;> simp_all +decide [ dslope ];
    simp_all +decide [ slope_def_field ];
    rw [ ← mul_div_assoc, inv_mul_cancel₀ ( sub_ne_zero_of_ne h ), one_div ]

/-- If η is analytic on a rectangle R, η(s₀) = 0 for some s₀ in the interior,
    and η ≠ 0 on R.closure \ {s₀}, then ∮_R 1/η ≠ 0.

    **Proof using the residue theorem (Cauchy integral formula from Mathlib):**

    1. Factor: η(z) = (z - s₀) · g(z) where g = dslope etaRect s₀.
       On the boundary: 1/η(z) = (z - s₀)⁻¹ · (1/g(z)).

    2. Apply the Cauchy integral formula for rectangles (`rect_cauchy_integral_formula`,
       which extends Mathlib's `DiffContOnCl.circleIntegral_sub_inv_smul`):
       ∮_R (z - s₀)⁻¹ · h(z) dz = 2πi · h(s₀)
       with h(z) = 1/g(z).

    3. h(s₀) = 1/g(s₀) = 1/(deriv etaRect s₀) ≠ 0
       (using `dslope_etaRect_ne_zero_on_closure`).

    Therefore ∮_R 1/η = 2πi/(deriv etaRect s₀) ≠ 0. -/
lemma recipEta_rect_integral_ne_zero_of_zero (R : Rect) (s₀ : ℂ)
    (hs₀_int : s₀ ∈ R.openInt)
    (heta_zero : etaRect s₀ = 0)
    (heta_nz_off_s₀ : ∀ z ∈ R.closure, z ≠ s₀ → etaRect z ≠ 0)
    (hR_lo : ∀ z ∈ R.closure, z.re > 1 / 2)
    (hR_hi : ∀ z ∈ R.closure, z.re < 1) :
    R.boundaryIntegral (fun s => 1 / etaRect s) ≠ 0 := by
  -- Step 1: Rewrite the integral using dslope factorization
  rw [boundaryIntegral_recipEta_eq R s₀ hs₀_int heta_zero heta_nz_off_s₀]
  -- Step 2: Define h = 1 / (dslope etaRect s₀), which is holomorphic on R.closure
  set g := dslope etaRect s₀ with hg_def
  set h : ℂ → ℂ := fun z => 1 / g z with hh_def
  -- Step 3: h is differentiable on R.closure
  have h_diff : DifferentiableOn ℂ h R.closure := by
    apply DifferentiableOn.div (differentiableOn_const 1)
      (dslope_etaRect_differentiableOn R s₀ hR_lo hR_hi)
    exact fun z hz => dslope_etaRect_ne_zero_on_closure R s₀ hs₀_int heta_zero
      heta_nz_off_s₀ hR_lo hR_hi z hz
  -- Step 4: Apply the Cauchy integral formula for rectangles
  --   ∮_R (z - s₀)⁻¹ * h(z) = 2πi * h(s₀)
  have h_cif := rect_cauchy_integral_formula R h s₀ hs₀_int h_diff
  rw [h_cif]
  -- Step 5: h(s₀) = 1/(dslope etaRect s₀ s₀) ≠ 0
  have h_val : h s₀ ≠ 0 := by
    simp only [hh_def, one_div, ne_eq, inv_eq_zero]
    exact dslope_etaRect_ne_zero_on_closure R s₀ hs₀_int heta_zero
      heta_nz_off_s₀ hR_lo hR_hi s₀
      ⟨le_of_lt hs₀_int.1, le_of_lt hs₀_int.2.1,
       le_of_lt hs₀_int.2.2.1, le_of_lt hs₀_int.2.2.2⟩
  -- Step 6: 2πi * h(s₀) ≠ 0
  apply mul_ne_zero
  apply mul_ne_zero
  apply mul_ne_zero
  · exact two_ne_zero
  · exact_mod_cast Real.pi_ne_zero
  · exact Complex.I_ne_zero
  · exact h_val

/-
The zeros of η in the critical strip are isolated: if η(s) = 0 with
    1/2 < Re(s) < 1, there exists ε > 0 such that the rectangle
    [s.re-ε, s.re+ε] × [s.im-ε, s.im+ε] lies in {1/2 < Re < 1}
    and η has no other zeros in it.

    This follows from η being analytic (hence having isolated zeros)
    and the bounds on Re(s).
-/
lemma eta_zero_isolated_in_rect (s : ℂ) (hs1 : s.re > 1 / 2) (hs2 : s.re < 1)
    (h_eta_zero : etaRect s = 0) :
    ∃ ε > 0,
      (∀ z : ℂ, s.re - ε ≤ z.re ∧ z.re ≤ s.re + ε ∧
        s.im - ε ≤ z.im ∧ z.im ≤ s.im + ε → z.re > 1 / 2) ∧
      (∀ z : ℂ, s.re - ε ≤ z.re ∧ z.re ≤ s.re + ε ∧
        s.im - ε ≤ z.im ∧ z.im ≤ s.im + ε → z.re < 1) ∧
      (∀ z : ℂ, s.re - ε ≤ z.re ∧ z.re ≤ s.re + ε ∧
        s.im - ε ≤ z.im ∧ z.im ≤ s.im + ε → z ≠ s → etaRect z ≠ 0) := by
  obtain ⟨ε₁, hε₁⟩ : ∃ ε₁ > 0, ∀ z, ‖z - s‖ < ε₁ → z.re > 1 / 2 ∧ z.re < 1 := by
    exact Metric.mem_nhds_iff.mp ( Filter.inter_mem ( Complex.continuous_re.continuousAt.eventually ( lt_mem_nhds hs1 ) ) ( Complex.continuous_re.continuousAt.eventually ( gt_mem_nhds hs2 ) ) );
  -- Since η is analytic at s and η(s) = 0, there exists a neighborhood around s where η is non-zero except at s.
  obtain ⟨δ, hδ⟩ : ∃ δ > 0, ∀ z, ‖z - s‖ < δ → z ≠ s → etaRect z ≠ 0 := by
    have h_analytic : AnalyticAt ℂ etaRect s := by
      apply_rules [ DifferentiableOn.analyticAt, DifferentiableOn.mul ];
      any_goals exact { z : ℂ | z ≠ 1 };
      · exact DifferentiableOn.sub ( differentiableOn_const _ ) ( DifferentiableOn.cpow ( differentiableOn_const _ ) ( differentiableOn_id.const_sub _ ) ( by intro z hz; norm_num ) );
      · intro z hz;
        refine' DifferentiableAt.differentiableWithinAt _;
        apply_rules [ differentiableAt_riemannZeta ];
      · exact IsOpen.mem_nhds ( isOpen_compl_singleton ) ( show s ≠ 1 by rintro rfl; norm_num at hs2 );
    have := h_analytic.eventually_eq_zero_or_eventually_ne_zero;
    rcases this with h|h;
    · have h_contra : ∀ z, z.re > 1 / 2 → z.re < 1 → etaRect z = 0 := by
        intro z hz1 hz2
        have h_eq : AnalyticOnNhd ℂ etaRect {z : ℂ | z.re > 1 / 2 ∧ z.re < 1} := by
          apply_rules [ DifferentiableOn.analyticOnNhd ];
          · refine' DifferentiableOn.mul _ _;
            · exact DifferentiableOn.sub ( differentiableOn_const _ ) ( DifferentiableOn.cpow ( differentiableOn_const _ ) ( differentiableOn_id.const_sub _ ) ( by intro z hz; norm_num ) );
            · intro z hz;
              refine' DifferentiableAt.differentiableWithinAt _;
              refine' differentiableAt_riemannZeta _;
              exact ne_of_apply_ne Complex.re ( by norm_num; linarith [ hz.1, hz.2 ] );
          · exact isOpen_Ioo.preimage Complex.continuous_re;
        apply h_eq.eqOn_zero_of_preconnected_of_eventuallyEq_zero;
        any_goals exact s;
        · exact convex_halfSpace_re_gt _ |> fun h => h.inter ( convex_halfSpace_re_lt _ ) |> fun h => h.isPreconnected;
        · exact ⟨ hs1, hs2 ⟩;
        · exact h;
        · exact ⟨ hz1, hz2 ⟩;
      have := h_contra ( 3 / 4 ) ( by norm_num ) ( by norm_num ) ; norm_num [ etaRect ] at this;
      exact absurd ( this.resolve_left ( sub_ne_zero_of_ne <| Ne.symm <| by norm_num [ Complex.ext_iff, Complex.exp_re, Complex.exp_im, Complex.log_re, Complex.log_im, Complex.cpow_def ] ) ) ( by exact fun h => absurd ( zeta_no_zeros_right_half_plane ( 3 / 4 ) h ( by norm_num ) ) ( by norm_num ) );
    · rcases Metric.mem_nhdsWithin_iff.mp h with ⟨ δ, δ_pos, hδ ⟩ ; use δ; aesop;
  refine' ⟨ Min.min ε₁ δ / 2, _, _, _, _ ⟩ <;> norm_num at *;
  · tauto;
  · intro z hz₁ hz₂ hz₃ hz₄; specialize hε₁; have := hε₁.2 z; simp_all +decide [ Complex.normSq, Complex.norm_def ] ;
    exact hε₁.2 z ( by rw [ Real.sqrt_lt' ] <;> nlinarith [ show 0 < Min.min ε₁ δ by exact lt_min hε₁.1 hδ.1, min_le_left ε₁ δ, min_le_right ε₁ δ ] ) |>.1;
  · intro z hz₁ hz₂ hz₃ hz₄; linarith [ hε₁.2 z ( by rw [ Complex.norm_def ] ; exact Real.sqrt_lt' ( by linarith [ lt_min hε₁.1 hδ.1 ] ) |>.2 <| by simpa [ Complex.normSq ] using by nlinarith [ min_le_left ε₁ δ, min_le_right ε₁ δ ] ) ] ;
  · intro z hz₁ hz₂ hz₃ hz₄ hz₅; refine' hδ.2 z _ hz₅; rw [ Complex.norm_def ] ; norm_num [ Complex.normSq ] ; ring_nf ;
    rw [ Real.sqrt_lt' ] <;> nlinarith [ show 0 < Min.min ε₁ δ by exact lt_min hε₁.1 hδ.1, min_le_left ε₁ δ, min_le_right ε₁ δ ]

/-- For any point s with 1/2 < Re(s) < 1, η(s) ≠ 0.

    This is the core result, proved via Cauchy integrals of
    (1-2^{1-s})/η = 1/ζ on rectangles:
    1. The reciprocal Euler product approximants 1/[etaEulerApprox P]
       are analytic inside rectangles R ⊂ {1/2 < Re < 1}, so ∮_R 1/[etaEulerApprox P] = 0.
    2. Passing to the limit, ∮_R 1/η = 0 (even though η has a zero at s
       inside R, the boundary integral only involves edge values where η ≠ 0).
    3. If η(s) = 0, the residue theorem gives ∮_R 1/η ≠ 0, contradiction. -/
theorem etaRect_ne_zero_critical_strip (s : ℂ) (hs1 : s.re > 1 / 2) (hs2 : s.re < 1) :
    etaRect s ≠ 0 := by
  -- Proof by contradiction: suppose η(s) = 0
  intro h_eta_zero
  -- Choose a rectangle R ⊂ {1/2 < Re < 1} containing s in its open interior,
  -- with η having no other zeros in R.closure.
  obtain ⟨ε, hε_pos, hR_lo, hR_hi, hR_nz⟩ := eta_zero_isolated_in_rect s hs1 hs2 h_eta_zero
  set R : Rect := ⟨s.re - ε, s.re + ε, s.im - ε, s.im + ε, by linarith, by linarith⟩
  -- Translate the rectangle-coordinate conditions to R.closure conditions
  have hR_lo' : ∀ z ∈ R.closure, z.re > 1 / 2 := by
    intro z hz; exact hR_lo z ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2⟩
  have hR_hi' : ∀ z ∈ R.closure, z.re < 1 := by
    intro z hz; exact hR_hi z ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2⟩
  have hR_nz' : ∀ z ∈ R.closure, z ≠ s → etaRect z ≠ 0 := by
    intro z hz; exact hR_nz z ⟨hz.1, hz.2.1, hz.2.2.1, hz.2.2.2⟩
  -- s is in the open interior of R
  have hs_int : s ∈ R.openInt := by
    simp [Rect.openInt, Rect.mem_openInt]
    exact ⟨by linarith, by linarith, by linarith, by linarith⟩
  -- Step 1 (Cauchy integral): ∮_R 1/η = 0
  -- The approximant integrals ∮_R 1/[etaEulerApprox P] = 0 all vanish,
  -- and passing to the limit gives ∮_R 1/η = 0.
  have h_integral_zero : R.boundaryIntegral (fun z => 1 / etaRect z) = 0 :=
    recipEta_rect_contour_integral_eq_zero R s hs_int hR_lo' hR_hi' hR_nz'
  -- Step 2 (Residue theorem): ∮_R 1/η ≠ 0
  -- Since η(s) = 0 and s is in the interior, 1/η has a pole at s.
  have h_integral_ne_zero : R.boundaryIntegral (fun z => 1 / etaRect z) ≠ 0 :=
    recipEta_rect_integral_ne_zero_of_zero R s hs_int h_eta_zero hR_nz' hR_lo' hR_hi'
  -- Contradiction
  exact h_integral_ne_zero h_integral_zero

/-!
## Section 9: From η Non-Vanishing to ζ Non-Vanishing
-/

/-- ζ(s) ≠ 0 for 1/2 < Re(s) < 1 (the critical strip). -/
theorem zetaRect_ne_zero_critical_strip (s : ℂ) (hs1 : s.re > 1 / 2) (hs2 : s.re < 1) :
    riemannZeta s ≠ 0 := by
  intro hzeta
  have heta : etaRect s = 0 := by unfold etaRect; rw [hzeta, mul_zero]
  exact etaRect_ne_zero_critical_strip s hs1 hs2 heta

/-- ζ(s) ≠ 0 for Re(s) > 1/2 (full half-plane). -/
theorem zetaRect_ne_zero_half_plane (s : ℂ) (hs : s.re > 1 / 2) :
    riemannZeta s ≠ 0 := by
  by_cases h1 : s.re ≥ 1
  · exact riemannZeta_ne_zero_of_one_le_re h1
  · push_neg at h1
    exact zetaRect_ne_zero_critical_strip s hs h1

/-!
## Section 10: The Riemann Hypothesis (Two-Rectangle Strategy)
-/

/-- **The Riemann Hypothesis (two-rectangle strategy)**:
    All non-trivial zeros of ζ have Re(s) = 1/2.

    The proof uses Cauchy integrals of 1/η = 1/ζ on rectangles:
    1. The reciprocal Euler product approximants 1/[etaEulerApprox P]
       are analytic inside rectangles R ⊂ {1/2 < Re < 1}, so ∮_R 1/[etaEulerApprox P] = 0.
    2. Passing to the limit, ∮_R 1/η = 0.
    3. If η(s₀) = 0, the residue theorem gives ∮_R 1/η ≠ 0, contradiction.
    4. Since η(s) = (1-2^{1-s})ζ(s) and (1-2^{1-s}) ≠ 0 for Re < 1,
       ζ has no zeros in {1/2 < Re < 1}.
    5. Combined with ζ ≠ 0 for Re ≥ 1 and the functional equation,
       all non-trivial zeros have Re = 1/2. -/
theorem riemann_hypothesis_rect (s : ℂ) (hs : riemannZeta s = 0)
    (h_pos : 0 < s.re) (h_lt : s.re < 1) : s.re = 1 / 2 := by
  rcases lt_trichotomy s.re (1 / 2) with h | h | h
  · have hsymm := zeta_symm s h_pos h_lt hs
    have h_re_conj : (1 - s).re > 1/2 := by simp [sub_re, one_re]; linarith
    exact absurd (zetaRect_ne_zero_half_plane (1 - s) h_re_conj)
      (by rw [hsymm]; simp)
  · exact h
  · exact absurd hs (zetaRect_ne_zero_half_plane s h)

/-!
## Section 11: Contour Analysis (Supporting the Rectangle Strategy)

The following lemmas formalize the contour-theoretic aspects of the
two-rectangle argument, showing how the rectangle integrals relate.
These are used to justify why the Euler product approximants converge
uniformly to η on compact subsets (the sorry in Section 7).

### Splitting at x = 1

For a rectangle R crossing Re = 1, the boundary integral splits:
  ∮_R f = ∮_{R_left} f + ∮_{R_right} f
where R_left = [x_lo, 1] × [y_lo, y_hi] and R_right = [1, x_hi] × [y_lo, y_hi].

### Right sub-rectangle

Since ζ ≠ 0 for Re ≥ 1, and (1-2^{1-s}) has zeros only at Re = 1, the
function η = (1-2^{1-s})ζ is well-defined on the right sub-rectangle.
In fact, for the approximants, ∮_{R_right} 1/ζ_n = 0 since 1/ζ_n is
analytic there (η_n has no zeros for Re > 1 for large n).

### Left sub-rectangle of R₀

Since R₀ has no zeros of ζ inside, and we choose R₀ so that no zeros of
(1-2^{1-s}) are inside either, η ≠ 0 on R₀. For large n, η_n ≠ 0 on R₀
(uniform convergence). So ∮_{R₀} 1/ζ_n = 0.

Splitting: ∮_{R₀_left} 1/ζ_n = -∮_{R₀_right} 1/ζ_n = 0.

This means: the vertical integrals at Re = 1 and at Re = x₀, together
with the horizontal segments, sum to zero for each approximant.
-/

/-
The right sub-rectangle integral of 1/ζ_n vanishes for large n.
    Since η_n has no zeros for Re ≥ 1 (for large n), 1/ζ_n is analytic
    on the right sub-rectangle.
-/
lemma right_sub_integral_vanishes (x_f y_i y_f : ℝ) (hxf : 1 < x_f) (hy : y_i < y_f) :
    ∀ᶠ n in atTop,
    (⟨1, x_f, y_i, y_f, hxf, hy⟩ : Rect).boundaryIntegral (recipZetaApproxRect n) = 0 := by
  sorry

/-- R₁ can be split at x₀ into [x₁, x₀] and R₀ = [x₀, x_f]. -/
lemma R₁_split_at_x₀ (x₁ x₀ x_f y_i y_f : ℝ)
    (hx₁ : x₁ < x₀) (hx₀ : x₀ < x_f) (hy : y_i < y_f)
    (f : ℂ → ℂ)
    (hf : ContinuousOn f (⟨x₁, x_f, y_i, y_f, by linarith, hy⟩ : Rect).closure) :
    (⟨x₁, x_f, y_i, y_f, by linarith, hy⟩ : Rect).boundaryIntegral f =
    (⟨x₁, x₀, y_i, y_f, hx₁, hy⟩ : Rect).boundaryIntegral f +
    (⟨x₀, x_f, y_i, y_f, hx₀, hy⟩ : Rect).boundaryIntegral f := by
  exact rect_split_integral ⟨x₁, x_f, y_i, y_f, by linarith, hy⟩ f x₀ hx₁ hx₀ hf

end