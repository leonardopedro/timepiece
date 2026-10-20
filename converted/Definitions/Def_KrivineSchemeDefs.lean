/-
prove2.me platform library module `Definitions.Def_KrivineSchemeDefs`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_KrivineSchemeDefs.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace GrothendieckConstant

open MeasureTheory Real

/-- Joint density on `ℝ^k × ℝ^k` of two standard Gaussian vectors whose
coordinates are pairwise correlated with correlation `t`. -/
noncomputable def gaussianPairDensity (k : ℕ) (t : ℝ) (x y : Fin k → ℝ) : ℝ :=
  ∏ i : Fin k, (1 / (2 * π * Real.sqrt (1 - t ^ 2))) *
    Real.exp (-(x i ^ 2 - 2 * t * x i * y i + y i ^ 2) / (2 * (1 - t ^ 2)))

/-- A Krivine scheme in dimension `k`: a pair of measurable, odd, ±1-valued
functions on `ℝ^k`, i.e. a pair of partitions of `ℝ^k` into a `+1` and a `-1` region.
Oddness is required almost everywhere: a `±1`-valued function cannot be odd at the
origin, and only the null-set-invariant Gaussian expectation of the pair matters. -/
structure KrivineScheme (k : ℕ) where
  f : (Fin k → ℝ) → ℝ
  g : (Fin k → ℝ) → ℝ
  measurable_f : Measurable f
  measurable_g : Measurable g
  f_sign : ∀ z, f z = 1 ∨ f z = -1
  g_sign : ∀ z, g z = 1 ∨ g z = -1
  f_odd : ∀ᵐ z ∂(volume : Measure (Fin k → ℝ)), f (-z) = -f z
  g_odd : ∀ᵐ z ∂(volume : Measure (Fin k → ℝ)), g (-z) = -g z

/-- The half-space scheme underlying random hyperplane rounding, which exists in
every dimension `k ≥ 1`; in particular `KrivineScheme k` is inhabited for `k ≥ 1`. -/
noncomputable def halfspaceScheme (k : ℕ) (hk : 0 < k) : KrivineScheme k where
  f := fun z => if 0 < z ⟨0, hk⟩ then 1 else -1
  g := fun z => if 0 < z ⟨0, hk⟩ then 1 else -1
  measurable_f := by
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_lt measurable_const (measurable_pi_apply _)
  measurable_g := by
    refine Measurable.ite ?_ measurable_const measurable_const
    exact measurableSet_lt measurable_const (measurable_pi_apply _)
  f_sign := by intro z; by_cases h : 0 < z ⟨0, hk⟩ <;> simp [h]
  g_sign := by intro z; by_cases h : 0 < z ⟨0, hk⟩ <;> simp [h]
  f_odd := by
    have h0 : (volume : Measure (Fin k → ℝ)) {z : Fin k → ℝ | z ⟨0, hk⟩ = 0} = 0 :=
      Measure.pi_hyperplane _ _ _
    have hae : ∀ᵐ z ∂(volume : Measure (Fin k → ℝ)), z ⟨0, hk⟩ ≠ 0 := by
      rw [ae_iff]; simpa using h0
    filter_upwards [hae] with z hz
    rcases lt_or_gt_of_ne hz with h | h
    · rw [if_neg (not_lt.mpr h.le), if_pos (by simpa using neg_pos.mpr h)]; norm_num
    · rw [if_pos h, if_neg (by simpa using not_lt.mpr (neg_nonpos.mpr h.le))]
  g_odd := by
    have h0 : (volume : Measure (Fin k → ℝ)) {z : Fin k → ℝ | z ⟨0, hk⟩ = 0} = 0 :=
      Measure.pi_hyperplane _ _ _
    have hae : ∀ᵐ z ∂(volume : Measure (Fin k → ℝ)), z ⟨0, hk⟩ ≠ 0 := by
      rw [ae_iff]; simpa using h0
    filter_upwards [hae] with z hz
    rcases lt_or_gt_of_ne hz with h | h
    · rw [if_neg (not_lt.mpr h.le), if_pos (by simpa using neg_pos.mpr h)]; norm_num
    · rw [if_pos h, if_neg (by simpa using not_lt.mpr (neg_nonpos.mpr h.le))]

/-- The normalized correlation function `H(t) = (π/2) * E[f(X) g(Y)]`, where `X, Y`
are standard Gaussian vectors in `ℝ^k` with `E[X i * Y i] = t` coordinatewise. -/
noncomputable def correlationFunction {k : ℕ} (S : KrivineScheme k) (t : ℝ) : ℝ :=
  (π / 2) * ∫ x : Fin k → ℝ, ∫ y : Fin k → ℝ,
    S.f x * S.g y * gaussianPairDensity k t x y

/-- The linear coefficient `b₁` of `H(t) = b₁ t + b₃ t³ + ⋯`, as `H'(0)`. -/
noncomputable def coeffLinear {k : ℕ} (S : KrivineScheme k) : ℝ :=
  deriv (correlationFunction S) 0

/-- The cubic coefficient `b₃` of `H(t) = b₁ t + b₃ t³ + ⋯`, as `H'''(0)/6`. -/
noncomputable def coeffCubic {k : ℕ} (S : KrivineScheme k) : ℝ :=
  iteratedDeriv 3 (correlationFunction S) 0 / 6

end GrothendieckConstant
