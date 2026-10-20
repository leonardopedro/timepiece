import Mathlib
import BookProof.Toolbox.ChapterFarisLavineCore

/-!
# Essential self-adjointness is stable under a real shift

`BookProof.FarisLavine.EssentiallySelfAdjointOn` is defined through the two deficiency
spaces at `± i` only.  Adding a real constant `c` to an operator moves the deficiency
question from `± i` to `± i − c`, so the statement "`H` ESA ⇒ `H + c` ESA" needs the
deficiency spaces of `H` at **every** non-real point.  This module supplies that fact
(on a complete space) and the shift lemma requested by `CONSOLIDATED_PLAN.md`
§"2026-10-15b", row NS-L-C.3, step 3.

## What is proved

* `norm_sub_conj_smul_ge` — for a symmetric `T`, `|Im z| ‖v‖ ≤ ‖T v − z̄ v‖`;
* `deficiencyTrivialAt_of_near` — the deficiency space stays trivial on the open disk
  of radius `|Im z₀|` about `z₀` (no closure of `T` is used: the range of `T − z̄₀` is
  dense, and the bound passes to its closure);
* `deficiencyTrivialAt_of_essentiallySelfAdjointOn` — a symmetric operator that is ESA has
  trivial deficiency spaces at every non-real `z`;
* `deficiencyTrivialAt_add_const` — a real shift translates the spectral parameter;
* **`essentiallySelfAdjointOn_add_const`** — `H` symmetric and ESA ⇒ `H + c` ESA for every
  real `c`, together with `symmetricOn_add_const`.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.EsaRealShift

open BookProof.FarisLavine

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] {D : Submodule ℂ F}

/-- **The non-real lower bound.**  For a symmetric operator `T` and any `z`,
`|Im z| ‖v‖ ≤ ‖T v − z̄ v‖`. -/
theorem norm_sub_conj_smul_ge {T : D →ₗ[ℂ] F} (hT : SymmetricOn D T) (z : ℂ) (v : D) :
    |z.im| * ‖(v : F)‖ ≤ ‖T v - (starRingEnd ℂ z) • (v : F)‖ := by
  have hreal : (inner ℂ (v : F) (T v) : ℂ).im = 0 := by
    have h1 : (inner ℂ (T v) (v : F) : ℂ) = inner ℂ (v : F) (T v) := hT v v
    have h2 : (inner ℂ (T v) (v : F) : ℂ) = (starRingEnd ℂ) (inner ℂ (v : F) (T v)) :=
      (inner_conj_symm _ _).symm
    have h3 := congrArg Complex.im (h2.symm.trans h1)
    simp only [Complex.conj_im] at h3
    linarith
  have hkey : (inner ℂ (v : F) (T v - (starRingEnd ℂ z) • (v : F)) : ℂ).im
      = z.im * ‖(v : F)‖ ^ 2 := by
    rw [inner_sub_right, inner_smul_right, inner_self_eq_norm_sq_to_K]
    simp only [Complex.sub_im, hreal, Complex.mul_im, Complex.conj_re, Complex.conj_im]
    simp [sq, Complex.mul_re, Complex.mul_im]
  have hle : |z.im * ‖(v : F)‖ ^ 2| ≤ ‖(v : F)‖ * ‖T v - (starRingEnd ℂ z) • (v : F)‖ := by
    rw [← hkey]
    exact (Complex.abs_im_le_norm _).trans (norm_inner_le_norm _ _)
  rw [abs_mul, abs_of_nonneg (sq_nonneg ‖(v : F)‖)] at hle
  rcases eq_or_lt_of_le (norm_nonneg (v : F)) with h0 | hpos
  · rw [← h0]; simp
  · have : |z.im| * ‖(v : F)‖ * ‖(v : F)‖ ≤ ‖T v - (starRingEnd ℂ z) • (v : F)‖ * ‖(v : F)‖ := by
      nlinarith
    exact le_of_mul_le_mul_right this hpos

/-- The deficiency equation at `z` says that `w` is orthogonal to the range of `T − z̄`. -/
theorem inner_sub_conj_smul_eq {T : D →ₗ[ℂ] F} (z : ℂ) (v : D) (w : F) :
    (inner ℂ (T v - (starRingEnd ℂ z) • (v : F)) w : ℂ)
      = inner ℂ (T v) w - z * inner ℂ (v : F) w := by
  rw [inner_sub_left, inner_smul_left, Complex.conj_conj]

/-- **Stability of trivial deficiency on a disk.**  If the deficiency space of the
symmetric operator `T` at `z₀` is trivial, so is the one at every `z` with
`|z − z₀| < |Im z₀|`. -/
theorem deficiencyTrivialAt_of_near [CompleteSpace F] {T : D →ₗ[ℂ] F} (hT : SymmetricOn D T)
    {z₀ z : ℂ} (h₀ : DeficiencyTrivialAt D T z₀) (hz : ‖z - z₀‖ < |z₀.im|) :
    DeficiencyTrivialAt D T z := by
  set S : D →ₗ[ℂ] F := T - (starRingEnd ℂ z₀) • D.subtype with hS
  have hSapp : ∀ v : D, S v = T v - (starRingEnd ℂ z₀) • (v : F) := fun v => rfl
  set R : Submodule ℂ F := LinearMap.range S with hR
  -- the range of `T − z̄₀` has trivial orthogonal complement, hence is dense
  have horth : Rᗮ = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro u hu
    refine h₀ u fun v => ?_
    have h := (Submodule.mem_orthogonal R u).1 hu (S v) (LinearMap.mem_range_self S v)
    rw [hSapp, inner_sub_conj_smul_eq] at h
    exact sub_eq_zero.1 h
  have hclos : R.topologicalClosure = ⊤ := by
    rw [← Submodule.orthogonal_orthogonal_eq_closure, horth, Submodule.bot_orthogonal_eq_top]
  have hpos : 0 < |z₀.im| := lt_of_le_of_lt (norm_nonneg _) hz
  set q : ℝ := ‖z - z₀‖ / |z₀.im| with hq
  have hq1 : q < 1 := (div_lt_one hpos).2 hz
  have hq0 : 0 ≤ q := div_nonneg (norm_nonneg _) hpos.le
  intro w hw
  -- the bound `‖⟪x, w⟫‖ ≤ q ‖w‖ ‖x‖` on the range ...
  have hbound : ∀ x ∈ R, ‖(inner ℂ x w : ℂ)‖ ≤ q * ‖w‖ * ‖x‖ := by
    rintro x ⟨v, rfl⟩
    have h1 : (inner ℂ (S v) w : ℂ) = (z - z₀) * inner ℂ (v : F) w := by
      rw [hSapp, inner_sub_conj_smul_eq, hw v]; ring
    have h2 : |z₀.im| * ‖(v : F)‖ ≤ ‖S v‖ := by
      rw [hSapp]; exact norm_sub_conj_smul_ge hT z₀ v
    have h3 : ‖(v : F)‖ ≤ ‖S v‖ / |z₀.im| := by
      rw [le_div_iff₀ hpos]; linarith
    rw [h1, norm_mul]
    calc ‖z - z₀‖ * ‖(inner ℂ (v : F) w : ℂ)‖ ≤ ‖z - z₀‖ * (‖(v : F)‖ * ‖w‖) :=
          mul_le_mul_of_nonneg_left (norm_inner_le_norm _ _) (norm_nonneg _)
      _ ≤ ‖z - z₀‖ * (‖S v‖ / |z₀.im| * ‖w‖) := by
          gcongr
      _ = q * ‖w‖ * ‖S v‖ := by rw [hq]; ring
  -- ... passes to the closure, i.e. to all of `F`
  have hclosed : IsClosed {x : F | ‖(inner ℂ x w : ℂ)‖ ≤ q * ‖w‖ * ‖x‖} :=
    isClosed_le (continuous_norm.comp (continuous_id.inner continuous_const))
      (continuous_const.mul continuous_norm)
  have hall : ∀ x : F, ‖(inner ℂ x w : ℂ)‖ ≤ q * ‖w‖ * ‖x‖ := by
    intro x
    have hsub : (R.topologicalClosure : Set F) ⊆ {x : F | ‖(inner ℂ x w : ℂ)‖ ≤ q * ‖w‖ * ‖x‖} :=
      closure_minimal (fun x hx => hbound x hx) hclosed
    exact hsub (by rw [hclos]; trivial)
  have hw2 := hall w
  rw [inner_self_eq_norm_sq_to_K] at hw2
  simp only [norm_pow, RCLike.norm_ofReal, abs_norm] at hw2
  have : ‖w‖ ^ 2 ≤ 0 := by nlinarith [sq_nonneg ‖w‖]
  have h0 : ‖w‖ = 0 := by nlinarith [norm_nonneg w]
  exact norm_eq_zero.1 h0

/-- Horizontal moves: trivial deficiency at `z₀` (non-real) gives it at `z₀ + x` for every
real `x`. -/
theorem deficiencyTrivialAt_add_ofReal [CompleteSpace F] {T : D →ₗ[ℂ] F}
    (hT : SymmetricOn D T) {z₀ : ℂ} (hz₀ : z₀.im ≠ 0) (h₀ : DeficiencyTrivialAt D T z₀)
    (x : ℝ) : DeficiencyTrivialAt D T (z₀ + x) := by
  have hη : 0 < |z₀.im| := abs_pos.2 hz₀
  have key : ∀ n : ℕ, ∀ x : ℝ, |x| ≤ n * (|z₀.im| / 2) → DeficiencyTrivialAt D T (z₀ + x) := by
    intro n
    induction n with
    | zero =>
      intro x hx
      have : x = 0 := by
        have : |x| ≤ 0 := by simpa using hx
        exact abs_nonpos_iff.1 this
      simpa [this] using h₀
    | succ n ih =>
      intro x hx
      set x' : ℝ := x * n / (n + 1) with hx'
      have hn1 : (0 : ℝ) < n + 1 := by positivity
      have hx'b : |x'| ≤ n * (|z₀.im| / 2) := by
        rw [hx', abs_div, abs_mul, Nat.abs_cast, abs_of_pos hn1, div_le_iff₀ hn1]
        push_cast at hx
        nlinarith [abs_nonneg x, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have hprev := ih x' hx'b
      refine deficiencyTrivialAt_of_near hT hprev ?_
      have hdiff : (z₀ + (x : ℂ)) - (z₀ + (x' : ℂ)) = ((x - x' : ℝ) : ℂ) := by push_cast; ring
      have him : (z₀ + (x' : ℂ)).im = z₀.im := by simp
      rw [hdiff, him, Complex.norm_real, Real.norm_eq_abs]
      have hxx : x - x' = x / (n + 1) := by rw [hx']; field_simp; ring
      rw [hxx, abs_div, abs_of_pos hn1, div_lt_iff₀ hn1]
      push_cast at hx
      nlinarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
  obtain ⟨n, hn⟩ := exists_nat_ge (|x| / (|z₀.im| / 2))
  refine key n x ?_
  rwa [div_le_iff₀ (by positivity)] at hn

/-- Vertical moves: trivial deficiency at `z₀` (non-real) gives it at `Re z₀ + i s Im z₀`
for every `s > 0`. -/
theorem deficiencyTrivialAt_scale_im [CompleteSpace F] {T : D →ₗ[ℂ] F}
    (hT : SymmetricOn D T) {z₀ : ℂ} (hz₀ : z₀.im ≠ 0) (h₀ : DeficiencyTrivialAt D T z₀)
    {s : ℝ} (hs : 0 < s) : DeficiencyTrivialAt D T ⟨z₀.re, z₀.im * s⟩ := by
  have hη : 0 < |z₀.im| := abs_pos.2 hz₀
  have hnorm : ∀ a b : ℝ, ‖(⟨z₀.re, z₀.im * a⟩ : ℂ) - ⟨z₀.re, z₀.im * b⟩‖ = |z₀.im| * |a - b| := by
    intro a b
    have : (⟨z₀.re, z₀.im * a⟩ : ℂ) - ⟨z₀.re, z₀.im * b⟩
        = ((z₀.im * (a - b) : ℝ) : ℂ) * Complex.I := by
      apply Complex.ext
      · simp
      · simp; ring
    rw [this, norm_mul, Complex.norm_I, mul_one, Complex.norm_real, Real.norm_eq_abs, abs_mul]
  have key : ∀ n : ℕ, ∀ s : ℝ, 0 < s → s < (3 / 2 : ℝ) ^ n →
      DeficiencyTrivialAt D T ⟨z₀.re, z₀.im * s⟩ := by
    intro n
    induction n with
    | zero =>
      intro s hs hs1
      have h1 : (⟨z₀.re, z₀.im * 1⟩ : ℂ) = z₀ := by apply Complex.ext <;> simp
      refine deficiencyTrivialAt_of_near hT h₀ ?_
      have hd := hnorm s 1
      rw [h1] at hd
      rw [hd]
      simp only [pow_zero] at hs1
      rw [abs_of_neg (show s - 1 < 0 by linarith)]
      have : 0 < 1 - s := by linarith
      nlinarith
    | succ n ih =>
      intro s hs hsn
      have hprev := ih (2 * s / 3) (by positivity) (by rw [pow_succ] at hsn; linarith)
      refine deficiencyTrivialAt_of_near hT hprev ?_
      rw [hnorm]
      simp only [abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * s / 3)]
      rw [abs_of_pos (by linarith : (0 : ℝ) < s - 2 * s / 3)]
      nlinarith
  obtain ⟨n, hn⟩ := pow_unbounded_of_one_lt s (by norm_num : (1 : ℝ) < 3 / 2)
  exact key n s hs hn

/-- **A symmetric ESA operator has trivial deficiency at every non-real point.** -/
theorem deficiencyTrivialAt_of_essentiallySelfAdjointOn [CompleteSpace F] {T : D →ₗ[ℂ] F}
    (hT : SymmetricOn D T) (h : EssentiallySelfAdjointOn D T) {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt D T z := by
  rcases lt_or_gt_of_ne hz with hneg | hpos
  · have h1 := deficiencyTrivialAt_scale_im hT (by simp) h.2 (neg_pos.2 hneg)
    have h2 := deficiencyTrivialAt_add_ofReal hT (by simp; linarith) h1 z.re
    have hz' : (⟨(-Complex.I).re, (-Complex.I).im * -z.im⟩ : ℂ) + (z.re : ℂ) = z := by
      apply Complex.ext <;> simp
    rwa [hz'] at h2
  · have h1 := deficiencyTrivialAt_scale_im hT (by simp) h.1 hpos
    have h2 := deficiencyTrivialAt_add_ofReal hT (by simp; linarith) h1 z.re
    have hz' : (⟨Complex.I.re, Complex.I.im * z.im⟩ : ℂ) + (z.re : ℂ) = z := by
      apply Complex.ext <;> simp
    rwa [hz'] at h2

/-- **A real shift translates the spectral parameter.** -/
theorem deficiencyTrivialAt_add_const (T : D →ₗ[ℂ] F) (c : ℝ) (z : ℂ) :
    DeficiencyTrivialAt D (T + (c : ℂ) • D.subtype) z
      ↔ DeficiencyTrivialAt D T (z - (c : ℂ)) := by
  have key : ∀ (w : F) (v : D),
      (inner ℂ ((T + (c : ℂ) • D.subtype) v) w : ℂ)
        = (inner ℂ (T v) w : ℂ) + (c : ℂ) * inner ℂ (v : F) w := by
    intro w v
    rw [LinearMap.add_apply, inner_add_left, LinearMap.smul_apply, inner_smul_left,
      Submodule.subtype_apply, Complex.conj_ofReal]
  constructor
  · intro h w hw
    refine h w fun v => ?_
    rw [key w v, hw v]
    ring
  · intro h w hw
    refine h w fun v => ?_
    have hv := hw v
    rw [key w v] at hv
    linear_combination hv

/-- Symmetry is preserved by a real shift. -/
theorem symmetricOn_add_const {T : D →ₗ[ℂ] F} (hT : SymmetricOn D T) (c : ℝ) :
    SymmetricOn D (T + (c : ℂ) • D.subtype) := by
  intro x y
  rw [LinearMap.add_apply, LinearMap.add_apply, inner_add_left, inner_add_right,
    LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_left, inner_smul_right,
    Submodule.subtype_apply, Submodule.subtype_apply, Complex.conj_ofReal, hT x y]

/-- **`essentiallySelfAdjointOn_add_const`.**  If `T` is symmetric and essentially
self-adjoint on `D` (a subspace of a Hilbert space), so is `T + c` for every real `c`. -/
theorem essentiallySelfAdjointOn_add_const [CompleteSpace F] {T : D →ₗ[ℂ] F}
    (hT : SymmetricOn D T) (h : EssentiallySelfAdjointOn D T) (c : ℝ) :
    EssentiallySelfAdjointOn D (T + (c : ℂ) • D.subtype) := by
  constructor
  · rw [deficiencyTrivialAt_add_const]
    exact deficiencyTrivialAt_of_essentiallySelfAdjointOn hT h (by simp)
  · rw [deficiencyTrivialAt_add_const]
    exact deficiencyTrivialAt_of_essentiallySelfAdjointOn hT h (by simp)

end BookProof.EsaRealShift
