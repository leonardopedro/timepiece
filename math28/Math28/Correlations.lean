import Mathlib

/-!
# Two-point correlations of multiplicative functions (openai/math family 007)

**Sources** (read-only snapshot, Lean v4.34.1, not imported):

* `OAI.OrdinaryTwoPointCorrelations.liouville_log_saving`,
  `….binary_corrected_elliott`, `….affine_corrected_elliott` —
  `math/OAI/NumberTheory/TwoPointCorrelations/FinalMain.lean`; definitions in
  `math/OAI/NumberTheory/TwoPoint/Basic.lean` and
  `math/OAI/NumberTheory/TwoPoint/PretentiousDistance.lean`.
  The import closure (1,539 modules) has no `sorry`, `axiom` or `native_decide`, but imports
  modules of packages that are not in the snapshot (`PrimeNumberTheoremAnd.Erdos970.*`,
  `StrongPNT.Erdos970.*`).
* `OAI.OrdinaryCorrelations.binary_corrected_elliott` —
  `math/OAI/NumberTheory/OrdinaryCorrelations/Elliott/BinaryCorrectedElliott.lean`; definitions
  in `math/OAI/NumberTheory/OrdinaryCorrelations/AbsoluteDefect/OneBounded.lean`.  Import closure
  (628 modules): no `sorry`, `axiom`, `native_decide`, nothing outside `Mathlib` and `OAI`.

None of this was re-elaborated here (the snapshot pins Lean v4.34.1).  The statements are kept
with the *ordinary* (fixed affine forms, natural-density) qualifier of the source, as
`CONSOLIDATED_PLAN.md` asks ("keep 007's ordinary qualifier").

**One transcription choice.**  The source's `liouville n` is `ArithmeticFunction.liouville n`
of the newer Mathlib, which the pinned Mathlib does not have.  It is defined here directly as
`λ(n) = (-1)^Ω(n)` for `n ≠ 0` and `λ(0) = 0` — the source's docstring records that its value at
zero is zero, and only positive arguments occur in the statements.

## Proved consequence

* `liouville_two_point_cesaro` — from `LiouvilleLogSaving`: for `h₁ ≠ h₂`,
  `(1/N) ∑_{n ≤ N} λ(n + h₁) λ(n + h₂) → 0`, the two-point (Chowla-type) Cesàro decay that
  `RandomMap.md` / `RandomMap2.md` use as a correlation-decay input.
-/

namespace Math28

open Filter Topology

/-! ## `OAI.TwoPointCorrelations` / `OAI.OrdinaryTwoPointCorrelations` -/

namespace TwoPointCorrelations

open scoped ComplexConjugate

/-- The Liouville function, complex valued, with `λ(0) = 0`. -/
noncomputable def liouville (n : ℕ) : ℂ :=
  if n = 0 then 0 else (-1) ^ ArithmeticFunction.cardFactors n

/-- An ordinary sum, with weight one on each positive integer at most `N`. -/
noncomputable def correlationSum (f g : ℕ → ℂ) (h₁ h₂ N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, f (n + h₁) * g (n + h₂)

/-- The ordinary affine correlation, allowing nonunit coefficients. -/
noncomputable def affineSum (f g : ℕ → ℂ) (a₁ a₂ b₁ b₂ N : ℕ) : ℂ :=
  ∑ n ∈ Finset.Icc 1 N, f (a₁ * n + b₁) * g (a₂ * n + b₂)

/-- Multiplicativity on coprime positive arguments. -/
def Multiplicative (f : ℕ → ℂ) : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → f (m * n) = f m * f n

/-- `|f| ≤ 1` on the positive integers. -/
def OneBounded (f : ℕ → ℂ) : Prop := ∀ n : ℕ, 0 < n → ‖f n‖ ≤ 1

/-- The primes not exceeding an integer cutoff. -/
def primesUpTo (N : ℕ) : Finset ℕ := (Finset.range (N + 1)).filter Nat.Prime

/-- The square of the pretentious distance. -/
noncomputable def squaredDistance (f g : ℕ → ℂ) (N : ℕ) : ℝ :=
  ∑ p ∈ primesUpTo N, (1 - (f p * conj (g p)).re) / (p : ℝ)

/-- The sequence `χ(n) n^(it)`. -/
noncomputable def characterTwist {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t : ℝ) (n : ℕ) : ℂ :=
  χ (n : ZMod q) * Complex.exp (((t * Real.log (n : ℝ) : ℝ) : ℂ) * Complex.I)

/-- Uniform nonpretentiousness against every fixed Dirichlet character. -/
def UniformlyNonpretentious (f : ℕ → ℂ) : Prop :=
  ∀ (q : ℕ), 0 < q → ∀ (χ : DirichletCharacter ℂ q) (K : ℝ),
    ∀ᶠ N : ℕ in atTop, ∀ t : ℝ, |t| ≤ (N : ℝ) →
      K ≤ squaredDistance f (characterTwist χ t) N

/-- **Named hypothesis — `OAI.OrdinaryTwoPointCorrelations.liouville_log_saving`.** -/
def LiouvilleLogSaving : Prop :=
  ∃ c : ℝ, 0 < c ∧ ∀ a₁ a₂ b₁ b₂ : ℕ,
    0 < a₁ → 0 < a₂ → a₁ * b₂ ≠ a₂ * b₁ →
    ∃ C : ℝ, 0 < C ∧ ∀ X : ℝ, 3 ≤ X →
      ‖affineSum liouville liouville a₁ a₂ b₁ b₂ ⌊X⌋₊‖ ≤
        C * X / Real.rpow (Real.log X) c

/-- **Named hypothesis — `OAI.OrdinaryTwoPointCorrelations.binary_corrected_elliott`.** -/
def BinaryCorrectedElliott : Prop :=
  ∀ f₁ f₂ : ℕ → ℂ, Multiplicative f₁ → Multiplicative f₂ →
    OneBounded f₁ → OneBounded f₂ →
    (UniformlyNonpretentious f₁ ∨ UniformlyNonpretentious f₂) →
    ∀ h₁ h₂ : ℕ, h₁ ≠ h₂ →
      Tendsto (fun N : ℕ => correlationSum f₁ f₂ h₁ h₂ N / (N : ℂ)) atTop (𝓝 0)

/-- **Named hypothesis — `OAI.OrdinaryTwoPointCorrelations.affine_corrected_elliott`.** -/
def AffineCorrectedElliott : Prop :=
  ∀ f₁ f₂ : ℕ → ℂ, Multiplicative f₁ → Multiplicative f₂ →
    OneBounded f₁ → OneBounded f₂ →
    (UniformlyNonpretentious f₁ ∨ UniformlyNonpretentious f₂) →
    ∀ a₁ a₂ b₁ b₂ : ℕ, 0 < a₁ → 0 < a₂ → a₁ * b₂ ≠ a₂ * b₁ →
      Tendsto (fun N : ℕ => affineSum f₁ f₂ a₁ a₂ b₁ b₂ N / (N : ℂ)) atTop (𝓝 0)

theorem correlationSum_eq_affineSum (f g : ℕ → ℂ) (h₁ h₂ N : ℕ) :
    correlationSum f g h₁ h₂ N = affineSum f g 1 1 h₁ h₂ N := by
  simp [correlationSum, affineSum]

/-- **Two-point Cesàro decay of the Liouville function, from the log saving.**  For distinct
shifts, `(1/N) ∑_{1 ≤ n ≤ N} λ(n + h₁) λ(n + h₂) → 0`. -/
theorem liouville_two_point_cesaro (h : LiouvilleLogSaving) {h₁ h₂ : ℕ} (hne : h₁ ≠ h₂) :
    Tendsto (fun N : ℕ => correlationSum liouville liouville h₁ h₂ N / (N : ℂ)) atTop (𝓝 0) := by
  obtain ⟨c, hc, hall⟩ := h
  obtain ⟨C, hC, hbound⟩ := hall 1 1 h₁ h₂ one_pos one_pos (by simpa using hne.symm)
  rw [tendsto_zero_iff_norm_tendsto_zero]
  -- the comparison function `C / (log N)^c → 0`
  have hlog : Tendsto (fun N : ℕ => C / Real.rpow (Real.log N) c) atTop (𝓝 0) := by
    have h1 : Tendsto (fun N : ℕ => Real.log (N : ℝ)) atTop atTop :=
      Real.tendsto_log_atTop.comp tendsto_natCast_atTop_atTop
    have h2 : Tendsto (fun N : ℕ => Real.rpow (Real.log N) c) atTop atTop :=
      (tendsto_rpow_atTop hc).comp h1
    exact h2.const_div_atTop C
  refine squeeze_zero' (Eventually.of_forall fun N => norm_nonneg _) ?_ hlog
  filter_upwards [eventually_ge_atTop 3] with N hN
  have hN3 : (3 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hb := hbound N hN3
  rw [Nat.floor_natCast, ← correlationSum_eq_affineSum] at hb
  rw [norm_div, Complex.norm_natCast, div_le_iff₀ hNpos]
  calc ‖correlationSum liouville liouville h₁ h₂ N‖ ≤ C * N / Real.rpow (Real.log N) c := hb
    _ = C / Real.rpow (Real.log N) c * N := by ring

end TwoPointCorrelations

/-! ## `OAI.OrdinaryCorrelations` -/

namespace OrdinaryCorrelations

/-- `|f| ≤ 1` everywhere (the `OrdinaryCorrelations` convention). -/
def OneBounded (f : ℕ → ℂ) : Prop := ∀ n, ‖f n‖ ≤ 1

/-- Multiplicativity on coprime positive arguments. -/
def Multiplicative (f : ℕ → ℂ) : Prop :=
  ∀ m n : ℕ, 0 < m → 0 < n → m.Coprime n → f (m * n) = f m * f n

/-- Squared pretentious distance up to `X`, twisted by `χ(p) p^{it}`. -/
noncomputable def distanceSq (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t X : ℝ) : ℝ :=
  ∑ p ∈ (Finset.Icc 2 ⌊X⌋₊).filter Nat.Prime,
    (1 - (f p * star (χ (p : ZMod q) *
      Complex.exp ((t * Real.log (p : ℝ) : ℝ) * Complex.I))).re) / (p : ℝ)

/-- The pretentious distance. -/
noncomputable def distance (f : ℕ → ℂ) {q : ℕ} (χ : DirichletCharacter ℂ q)
    (t X : ℝ) : ℝ := Real.sqrt (distanceSq f χ t X)

/-- Uniform nonpretentiousness (the `OrdinaryCorrelations` form). -/
def UniformlyNonpretentious (f : ℕ → ℂ) : Prop :=
  ∀ (q : ℕ), 0 < q → ∀ χ : DirichletCharacter ℂ q,
    Tendsto (fun N : ℕ => sInf ((fun t : ℝ => distance f χ t (N : ℝ)) ''
      Set.Icc (-(N : ℝ)) (N : ℝ))) atTop atTop

/-- The normalized shifted correlation. -/
noncomputable def shiftAverage (f₁ f₂ : ℕ → ℂ) (h₁ h₂ N : ℕ) : ℂ :=
  (N : ℂ)⁻¹ * ∑ n ∈ Finset.Icc 1 N, f₁ (n + h₁) * f₂ (n + h₂)

/-- **Named hypothesis — `OAI.OrdinaryCorrelations.binary_corrected_elliott`.** -/
def BinaryCorrectedElliott : Prop :=
  ∀ (f₁ f₂ : ℕ → ℂ), OneBounded f₁ → OneBounded f₂ →
    Multiplicative f₁ → Multiplicative f₂ →
    (UniformlyNonpretentious f₁ ∨ UniformlyNonpretentious f₂) →
    ∀ (h₁ h₂ : ℕ), h₁ ≠ h₂ → Tendsto (shiftAverage f₁ f₂ h₁ h₂) atTop (𝓝 0)

end OrdinaryCorrelations

end Math28
