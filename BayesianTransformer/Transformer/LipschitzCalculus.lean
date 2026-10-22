module

public import Mathlib.Analysis.Normed.Operator.Basic
public import Mathlib.Analysis.InnerProductSpace.Basic
public import Mathlib.Topology.MetricSpace.Lipschitz

/-!
# A small Lipschitz calculus on a parameter domain

To derive the per-example gradient bound of the nGPT network from its architecture we track,
for every intermediate quantity of the forward pass viewed as a function of the parameters, an
explicit Lipschitz constant on the parameter domain together with a norm bound.

* `LipOn f D K`: `dist (f a) (f b) ≤ K * dist a b` for `a b ∈ D` (real constant `K`).
* Closure under composition, sums, scalar multiples, coordinates, and the bilinear operations
  that occur in a transformer (`apply` of a linear map, inner product, scalar times vector).
* `normalizeVec v = ‖v‖⁻¹ • v` (the projection to the unit sphere in an arbitrary real normed
  space; for inner product spaces it is `sphereProj`) is `2/δ`-Lipschitz on `{‖v‖ ≥ δ}`.
-/

@[expose] public section

namespace BayesianTransformer

/-- `f` is `K`-Lipschitz on `D` (real-valued constant). -/
def LipOn {P Y : Type*} [PseudoMetricSpace P] [PseudoMetricSpace Y] (f : P → Y) (D : Set P)
    (K : ℝ) : Prop :=
  ∀ a ∈ D, ∀ b ∈ D, dist (f a) (f b) ≤ K * dist a b

section General

variable {P Y Z : Type*} [PseudoMetricSpace P] [PseudoMetricSpace Y] [PseudoMetricSpace Z]
  {D : Set P}

theorem LipOn.const (y : Y) : LipOn (fun _ : P => y) D 0 := fun a _ b _ => by simp

theorem LipOn.mono {f : P → Y} {K K' : ℝ} (h : LipOn f D K) (hKK : K ≤ K') : LipOn f D K' :=
  fun a ha b hb => (h a ha b hb).trans (mul_le_mul_of_nonneg_right hKK dist_nonneg)

theorem LipOn.comp_on {f : P → Y} {g : Y → Z} {S : Set Y} {K c : ℝ} (hc : 0 ≤ c)
    (hg : ∀ y ∈ S, ∀ y' ∈ S, dist (g y) (g y') ≤ c * dist y y') (hfS : ∀ a ∈ D, f a ∈ S)
    (hf : LipOn f D K) : LipOn (fun a => g (f a)) D (c * K) := fun a ha b hb =>
  calc dist (g (f a)) (g (f b)) ≤ c * dist (f a) (f b) := hg _ (hfS a ha) _ (hfS b hb)
    _ ≤ c * (K * dist a b) := mul_le_mul_of_nonneg_left (hf a ha b hb) hc
    _ = c * K * dist a b := by ring

theorem LipOn.comp {f : P → Y} {g : Y → Z} {K c : ℝ} (hc : 0 ≤ c)
    (hg : ∀ y y', dist (g y) (g y') ≤ c * dist y y') (hf : LipOn f D K) :
    LipOn (fun a => g (f a)) D (c * K) :=
  hf.comp_on (S := Set.univ) hc (fun y _ y' _ => hg y y') (fun _ _ => Set.mem_univ _)

theorem LipOn.to_lipschitzOnWith {f : P → Y} {K : ℝ} (h : LipOn f D K) :
    LipschitzOnWith (Real.toNNReal K) f D :=
  LipschitzOnWith.of_dist_le' h

/-- Lipschitz in each coordinate with a common constant implies Lipschitz into the product
(sup) metric. -/
theorem LipOn.pi {ι : Type*} [Fintype ι] {Yi : ι → Type*} [∀ i, PseudoMetricSpace (Yi i)]
    {f : P → ∀ i, Yi i} {K : ℝ} (hK : 0 ≤ K) (h : ∀ i, LipOn (fun a => f a i) D K) :
    LipOn f D K := fun a ha b hb =>
  (dist_pi_le_iff (mul_nonneg hK dist_nonneg)).mpr fun i => h i a ha b hb

theorem LipOn.apply {ι : Type*} [Fintype ι] {Yi : ι → Type*} [∀ i, PseudoMetricSpace (Yi i)]
    {f : P → ∀ i, Yi i} {K : ℝ} (h : LipOn f D K) (i : ι) : LipOn (fun a => f a i) D K :=
  fun a ha b hb => (dist_le_pi_dist (f a) (f b) i).trans (h a ha b hb)

end General

section Normed

variable {P : Type*} [PseudoMetricSpace P] {D : Set P}
variable {E F G : Type*} [SeminormedAddCommGroup E] [NormedSpace ℝ E]
  [SeminormedAddCommGroup F] [NormedSpace ℝ F]

omit [NormedSpace ℝ E] in
theorem LipOn.add {f g : P → E} {K₁ K₂ : ℝ} (hf : LipOn f D K₁) (hg : LipOn g D K₂) :
    LipOn (fun a => f a + g a) D (K₁ + K₂) := fun a ha b hb => by
  calc dist (f a + g a) (f b + g b) ≤ dist (f a) (f b) + dist (g a) (g b) := dist_add_add_le _ _ _ _
    _ ≤ K₁ * dist a b + K₂ * dist a b := add_le_add (hf a ha b hb) (hg a ha b hb)
    _ = (K₁ + K₂) * dist a b := by ring

omit [NormedSpace ℝ E] in
theorem LipOn.sub {f g : P → E} {K₁ K₂ : ℝ} (hf : LipOn f D K₁) (hg : LipOn g D K₂) :
    LipOn (fun a => f a - g a) D (K₁ + K₂) := fun a ha b hb => by
  calc dist (f a - g a) (f b - g b) ≤ dist (f a) (f b) + dist (g a) (g b) := dist_sub_sub_le _ _ _ _
    _ ≤ K₁ * dist a b + K₂ * dist a b := add_le_add (hf a ha b hb) (hg a ha b hb)
    _ = (K₁ + K₂) * dist a b := by ring

theorem LipOn.const_smul {f : P → E} {K : ℝ} (hf : LipOn f D K) (c : ℝ) :
    LipOn (fun a => c • f a) D (|c| * K) := fun a ha b hb => by
  rw [dist_smul₀, Real.norm_eq_abs, mul_assoc]
  exact mul_le_mul_of_nonneg_left (hf a ha b hb) (abs_nonneg c)

omit [NormedSpace ℝ E] in
theorem LipOn.sum {ι : Type*} (s : Finset ι) {f : ι → P → E} {K : ι → ℝ}
    (hf : ∀ i ∈ s, LipOn (f i) D (K i)) :
    LipOn (fun a => ∑ i ∈ s, f i a) D (∑ i ∈ s, K i) := fun a ha b hb => by
  rw [dist_eq_norm, ← Finset.sum_sub_distrib, Finset.sum_mul]
  refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  rw [← dist_eq_norm]
  exact hf i hi a ha b hb

/-- Applying a parameter-dependent continuous linear map to a parameter-dependent vector. -/
theorem LipOn.clm_apply {f : P → E →L[ℝ] F} {g : P → E} {Kf Kg Bf Bg : ℝ}
    (hf : LipOn f D Kf) (hg : LipOn g D Kg) (hBf : ∀ a ∈ D, ‖f a‖ ≤ Bf)
    (hBg : ∀ a ∈ D, ‖g a‖ ≤ Bg) (hKf : 0 ≤ Kf) :
    LipOn (fun a => f a (g a)) D (Kf * Bg + Bf * Kg) := fun a ha b hb => by
  have e : f a (g a) - f b (g b) = (f a - f b) (g a) + f b (g a - g b) := by
    simp [map_sub]
  rw [dist_eq_norm, e]
  have hBf0 : 0 ≤ Bf := (norm_nonneg _).trans (hBf a ha)
  calc ‖(f a - f b) (g a) + f b (g a - g b)‖
      ≤ ‖f a - f b‖ * ‖g a‖ + ‖f b‖ * ‖g a - g b‖ :=
        (norm_add_le _ _).trans (add_le_add (ContinuousLinearMap.le_opNorm _ _)
          (ContinuousLinearMap.le_opNorm _ _))
    _ ≤ (Kf * dist a b) * Bg + Bf * (Kg * dist a b) := by
        rw [← dist_eq_norm, ← dist_eq_norm]
        exact add_le_add (mul_le_mul (hf a ha b hb) (hBg a ha) (norm_nonneg _)
            (mul_nonneg hKf dist_nonneg))
          (mul_le_mul (hBf b hb) (hg a ha b hb) dist_nonneg hBf0)
    _ = (Kf * Bg + Bf * Kg) * dist a b := by ring

/-- Product of a parameter-dependent scalar with a parameter-dependent vector. -/
theorem LipOn.smul {p : P → ℝ} {g : P → E} {Kp Kg Bp Bg : ℝ}
    (hp : LipOn p D Kp) (hg : LipOn g D Kg) (hBp : ∀ a ∈ D, |p a| ≤ Bp)
    (hBg : ∀ a ∈ D, ‖g a‖ ≤ Bg) (hKp : 0 ≤ Kp) :
    LipOn (fun a => p a • g a) D (Kp * Bg + Bp * Kg) := fun a ha b hb => by
  have e : p a • g a - p b • g b = (p a - p b) • g a + p b • (g a - g b) := by
    simp [sub_smul, smul_sub]
  rw [dist_eq_norm, e]
  have hBp0 : 0 ≤ Bp := (abs_nonneg _).trans (hBp a ha)
  calc ‖(p a - p b) • g a + p b • (g a - g b)‖
      ≤ |p a - p b| * ‖g a‖ + |p b| * ‖g a - g b‖ := by
        refine (norm_add_le _ _).trans ?_
        rw [norm_smul, norm_smul, Real.norm_eq_abs, Real.norm_eq_abs]
    _ ≤ (Kp * dist a b) * Bg + Bp * (Kg * dist a b) := by
        rw [← dist_eq_norm, ← Real.dist_eq]
        exact add_le_add (mul_le_mul (hp a ha b hb) (hBg a ha) (norm_nonneg _)
            (mul_nonneg hKp dist_nonneg))
          (mul_le_mul (hBp b hb) (hg a ha b hb) dist_nonneg hBp0)
    _ = (Kp * Bg + Bp * Kg) * dist a b := by ring

end Normed

section Inner

variable {P : Type*} [PseudoMetricSpace P] {D : Set P}
variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]

/-- Inner product of two parameter-dependent vectors. -/
theorem LipOn.real_inner {f g : P → E} {Kf Kg Bf Bg : ℝ}
    (hf : LipOn f D Kf) (hg : LipOn g D Kg) (hBf : ∀ a ∈ D, ‖f a‖ ≤ Bf)
    (hBg : ∀ a ∈ D, ‖g a‖ ≤ Bg) (hKf : 0 ≤ Kf) :
    LipOn (fun a => inner ℝ (f a) (g a)) D (Kf * Bg + Bf * Kg) := fun a ha b hb => by
  have e : inner ℝ (f a) (g a) - inner ℝ (f b) (g b)
      = inner ℝ (f a - f b) (g a) + inner ℝ (f b) (g a - g b) := by
    simp [inner_sub_left, inner_sub_right]
  rw [Real.dist_eq, e]
  have hBf0 : 0 ≤ Bf := (norm_nonneg _).trans (hBf a ha)
  calc |inner ℝ (f a - f b) (g a) + inner ℝ (f b) (g a - g b)|
      ≤ ‖f a - f b‖ * ‖g a‖ + ‖f b‖ * ‖g a - g b‖ :=
        (abs_add_le _ _).trans (add_le_add (abs_real_inner_le_norm _ _)
          (abs_real_inner_le_norm _ _))
    _ ≤ (Kf * dist a b) * Bg + Bf * (Kg * dist a b) := by
        rw [← dist_eq_norm, ← dist_eq_norm]
        exact add_le_add (mul_le_mul (hf a ha b hb) (hBg a ha) (norm_nonneg _)
            (mul_nonneg hKf dist_nonneg))
          (mul_le_mul (hBf b hb) (hg a ha b hb) dist_nonneg hBf0)
    _ = (Kf * Bg + Bf * Kg) * dist a b := by ring

end Inner

section Normalize

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- Projection to the unit sphere `v ↦ v / ‖v‖` in a real normed space (with `0 ↦ 0`).
For inner product spaces this is `sphereProj`. -/
noncomputable def normalizeVec (v : E) : E := (‖v‖)⁻¹ • v

theorem norm_normalizeVec_le (v : E) : ‖normalizeVec v‖ ≤ 1 := by
  rw [normalizeVec, norm_smul, norm_inv, norm_norm]
  rcases eq_or_ne v 0 with rfl | hv
  · simp
  · rw [inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

theorem norm_normalizeVec {v : E} (hv : v ≠ 0) : ‖normalizeVec v‖ = 1 := by
  rw [normalizeVec, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ (norm_ne_zero_iff.mpr hv)]

/-- The normalization map is `2/δ`-Lipschitz on the region `{v | δ ≤ ‖v‖}`. -/
theorem dist_normalizeVec_le {δ : ℝ} (hδ : 0 < δ) {u v : E} (hu : δ ≤ ‖u‖) (hv : δ ≤ ‖v‖) :
    dist (normalizeVec u) (normalizeVec v) ≤ (2 / δ) * dist u v := by
  have hu0 : 0 < ‖u‖ := hδ.trans_le hu
  have hv0 : 0 < ‖v‖ := hδ.trans_le hv
  have e : normalizeVec u - normalizeVec v = ‖u‖⁻¹ • (u - v) + (‖u‖⁻¹ - ‖v‖⁻¹) • v := by
    simp only [normalizeVec, smul_sub, sub_smul]; abel
  rw [dist_eq_norm, dist_eq_norm, e]
  have h2 : ‖(‖u‖⁻¹ - ‖v‖⁻¹) • v‖ ≤ ‖u‖⁻¹ * ‖u - v‖ := by
    rw [norm_smul, Real.norm_eq_abs]
    have : (‖u‖⁻¹ - ‖v‖⁻¹) * ‖v‖ = (‖v‖ - ‖u‖) * ‖u‖⁻¹ := by field_simp
    rw [← abs_of_pos hv0, ← abs_mul, abs_of_pos hv0, this, abs_mul, abs_of_pos (inv_pos.mpr hu0),
      mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (inv_pos.mpr hu0).le
    rw [abs_sub_comm]
    exact abs_norm_sub_norm_le u v
  calc ‖‖u‖⁻¹ • (u - v) + (‖u‖⁻¹ - ‖v‖⁻¹) • v‖
      ≤ ‖u‖⁻¹ * ‖u - v‖ + ‖u‖⁻¹ * ‖u - v‖ := by
        refine (norm_add_le _ _).trans (add_le_add ?_ h2)
        rw [norm_smul, norm_inv, norm_norm]
    _ = 2 * ‖u‖⁻¹ * ‖u - v‖ := by ring
    _ ≤ 2 * δ⁻¹ * ‖u - v‖ := by gcongr
    _ = (2 / δ) * ‖u - v‖ := by ring

end Normalize

end BayesianTransformer
