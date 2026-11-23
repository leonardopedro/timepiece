import BookProof.Phi4.ChapterScalarMehler
import BookProof.Sirk.ChapterSirkTrotterKato

/-!
# A full-action error estimate for the rank-one scalar Mehler window

The scalar reduced generator advances the inner vacuum by a phase. The full
operator also produces the second and fourth Hermites. Their orthogonal norm
controls the difference from the exact Stone evolution.
-/
namespace BookProof.Phi4

open MvPolynomial HermiteProductCore HermiteProductBasis HermiteCore
open EsaClosure FarisLavine YangMillsFriedrichs ChapterStoneResolvent ChapterSirkTrotterKato
open scoped InnerProductSpace

noncomputable section

/-- Undo the rank-one phase along the exact flow. Unitarity makes the norm of the
derivative equal to the norm of the full residual, at every time. -/
theorem rankOne_flow_error {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    [CompleteSpace F] (T : UnboundedSelfAdjoint F) (x : T.domain) (E t : ℝ) :
    ‖T.stoneU t x - Complex.exp (-(Complex.I * E * t)) • (x : F)‖ ≤
      ‖T.op x - (E : ℂ) • (x : F)‖ * |t| := by
  let phase := fun s : ℝ => Complex.exp (-(Complex.I * E * s))
  let g := fun s : ℝ => phase s • T.stoneU (t-s) x
  let v := T.op x - (E : ℂ) • (x : F)
  have hd (s : ℝ) : HasDerivAt g ((phase s * Complex.I) • T.stoneU (t-s) v) s := by
    have hp : HasDerivAt (fun s : ℝ => -(Complex.I * E * (s : ℂ))) (-(Complex.I * E)) s := by
      simpa using (((Complex.ofRealCLM.hasDerivAt (x := s)).const_mul (Complex.I * E)).neg)
    have hu := (T.hasDerivAt_stoneU x (t-s)).comp_const_sub t s
    apply (hp.cexp.smul hu).congr_deriv
    simp only [phase, v, map_sub, map_smul, smul_sub, smul_smul, neg_smul, map_neg, neg_neg]
    module
  have hn (s : ℝ) : ‖(phase s * Complex.I) • T.stoneU (t-s) v‖ ≤ ‖v‖ := by
    rw [norm_smul, norm_mul, T.norm_stoneU_apply]
    simp [phase, Complex.norm_exp]
  have hm := (convex_uIcc (0 : ℝ) t).norm_image_sub_le_of_norm_hasDerivWithin_le
    (fun s _ => (hd s).hasDerivWithinAt) (fun s _ => hn s) Set.left_mem_uIcc Set.right_mem_uIcc
  have hgt : g t = phase t • (x : F) := by
    simp only [g, sub_self, T.stoneU_zero, ContinuousLinearMap.one_apply]
  have hg0 : g 0 = T.stoneU t x := by
    simp only [g, phase, Complex.ofReal_zero, mul_zero, neg_zero, Complex.exp_zero,
      sub_zero, one_smul]
  rw [hgt, hg0, norm_sub_rev] at hm
  simpa only [sub_zero, Real.norm_eq_abs] using hm

/-- Integrate an affine envelope on the full-action residual of a reconstructed
Mehler-core orbit. The envelope may grow along the orbit, even for an exact reduced solve. -/
theorem Model.orbit_error {d k r : ℕ} (M : Model d k r) {T : UnboundedSelfAdjoint (L2d d)}
    (hext : IsSelfAdjointExtension M.innerHam T.op) (y : ℝ → polyGaussCore (d := d))
    (v : ℝ → L2d d) (hder : ∀ s, HasDerivAt (fun u => (y u : L2d d)) (v s) s)
    (a b t : ℝ) (ht : 0 ≤ t)
    (hbound : ∀ s ∈ Set.Ico 0 t, ‖Complex.I • M.innerHam (y s) + v s‖ ≤ a + b*s) :
    ‖(y t : L2d d) - T.stoneU t (y 0)‖ ≤ a*t + b*t^2/2 := by
  let g := fun s : ℝ => T.stoneU (t-s) (y s) - T.stoneU t (y 0)
  let w := fun s : ℝ => T.stoneU (t-s) (Complex.I • M.innerHam (y s) + v s)
  have hg (s : ℝ) : HasDerivAt g (w s) s := by
    obtain ⟨hmem, hval⟩ := hext.1 (y s)
    have h := hasDerivAt_stoneU_const_sub_apply T (hder s) hmem (t := t)
    rw [T.stoneU_op (t-s) (⟨y s, hmem⟩ : T.domain), hval] at h
    simpa only [g, w, map_add, map_smul] using h.sub_const (T.stoneU t (y 0))
  have hb (s : ℝ) : HasDerivAt (fun u : ℝ => a*u + b*u^2/2) (a+b*s) s := by
    convert ((hasDerivAt_id s).const_mul a).add
      ((((hasDerivAt_id s).pow 2).const_mul b).div_const 2) using 1 <;> simp <;> ring
  have hg0 : ‖g 0‖ ≤ a*0 + b*0^2/2 := by simp [g]
  have h := image_norm_le_of_norm_deriv_right_le_deriv_boundary
    (fun s _ => (hg s).continuousAt.continuousWithinAt)
    (fun s _ => (hg s).hasDerivWithinAt) hg0 hb
    (fun s hs => (T.norm_stoneU_apply _ _).le.trans (hbound s hs)) (Set.right_mem_Icc.mpr ht)
  simpa only [g, sub_self, T.stoneU_zero, ContinuousLinearMap.one_apply] using h

private def level (n : ℕ) : Fin 1 →₀ ℕ := Finsupp.single 0 n

private theorem hermite_levels :
    hermiteMv (level 2) = (X 0)^2 - 1 ∧
    hermiteMv (level 4) = (X 0)^4 - 6*(X 0)^2 + 3 := by
  have step (n : ℕ) := hermiteFactor_X_mul (d := 1) 0 n
  have h1 := step 0
  have h2 := step 1
  have h3 := step 2
  have h4 := step 3
  norm_num [hermiteFactor_zero, smul_eq_C_mul] at h1 h2 h3 h4
  have hc (n : ℕ) : (C (n : ℂ) : MvPolynomial (Fin 1) ℂ) = n := map_natCast _ _
  rw [show (C (2 : ℂ) : MvPolynomial (Fin 1) ℂ) = 2 from hc 2] at h3
  rw [show (C (3 : ℂ) : MvPolynomial (Fin 1) ℂ) = 3 from hc 3] at h4
  simp [hermiteMv, level]
  constructor
  · linear_combination -h2 - X 0 * h1
  · linear_combination -h4 - X 0*h3 - (X 0^2-3)*h2 - (X 0^3-5*X 0)*h1

private theorem residual_vector :
    unitCell.innerHam ⟨pgLp 1, pgLp_mem_core 1⟩ - (5/8 : ℂ) • pgLp 1 =
      (7/8 : ℂ) • pgLp (hermiteMv (level 2)) + (1/4 : ℂ) • pgLp (hermiteMv (level 4)) := by
  rw [unitCell_vacuum_column, hermite_levels.1, hermite_levels.2]
  change pgMap _ - _ • pgMap _ = _ • pgMap _ + _ • pgMap _
  rw [← map_smul, ← map_smul, ← map_smul, ← map_sub, ← map_add]
  congr 1
  simp [smul_eq_C_mul]
  ring

/-- The residual norm in the actual one-site L² inner product, relative to the
norm of the unnormalized Gaussian. -/
theorem unitCell_defect_norm_sq :
    ‖unitCell.innerHam ⟨pgLp 1, pgLp_mem_core 1⟩ - (5/8 : ℂ) • pgLp 1‖^2 =
      (97/32 : ℝ) * ‖pgLp (d := 1) 1‖^2 := by
  let ψ (n : ℕ) : L2d 1 := pgLp (hermiteMv (level n))
  have hi (m n : ℕ) : inner ℂ (ψ m) (ψ n) = (hermiteInner m n : ℂ) := by
    rw [inner_pgLp_hermiteMv]
    simp [level]
  have hz : pgLp (d := 1) 1 = ψ 0 := by simp [ψ, level, hermiteMv_zero]
  rw [residual_vector, hz]
  change ‖(7/8 : ℂ) • ψ 2 + (1/4 : ℂ) • ψ 4‖^2 = (97/32 : ℝ) * ‖ψ 0‖^2
  let y := (7/8 : ℂ) • ψ 2 + (1/4 : ℂ) • ψ 4
  change ‖y‖^2 = _
  rw [← inner_self_eq_norm_sq (𝕜 := ℂ) y, ← inner_self_eq_norm_sq (𝕜 := ℂ) (ψ 0)]
  dsimp only [y]
  simp only [inner_add_left, inner_add_right, inner_smul_left, inner_smul_right, hi]
  simp only [map_div₀, map_ofNat]
  norm_num [hermiteInner_eq, Nat.factorial, Complex.mul_re]
  ring

/-- The exact one-column Hashimoto phase on the vacuum, compared with the full
unbounded evolution. Squaring avoids a square-root normalization on the Gaussian. -/
theorem unitCell_rankOne_error {T : UnboundedSelfAdjoint (L2d 1)}
    (hext : IsSelfAdjointExtension unitCell.innerHam T.op) (t : ℝ) :
    ‖T.stoneU t (pgLp 1) - Complex.exp (-(Complex.I * (5/8) * t)) • pgLp 1‖^2 ≤
      (97/32 : ℝ) * t^2 * ‖pgLp (d := 1) 1‖^2 := by
  let seed : polyGaussCore (d := 1) := ⟨pgLp 1, pgLp_mem_core 1⟩
  obtain ⟨hmem, hval⟩ := hext.1 seed
  have h := rankOne_flow_error T ⟨seed, hmem⟩ (5/8) t
  rw [hval] at h
  have hs := pow_le_pow_left₀ (norm_nonneg _) h 2
  change (‖T.stoneU t (pgLp 1) - _ • pgLp 1‖)^2 ≤
    (‖unitCell.innerHam seed - _ • pgLp 1‖ * |t|)^2 at hs
  norm_num only [Complex.ofReal_div, Complex.ofReal_ofNat] at hs
  rw [mul_pow, sq_abs, unitCell_defect_norm_sq] at hs
  linarith

/-- Loss of return probability is bounded by squared distance from any
equal-norm reference state on the same ray. The inequality is homogeneous. -/
private theorem overlap_loss {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (x y : F) (hy : ‖y‖ = ‖x‖) :
    ‖x‖^4 - ‖inner ℂ x y‖^2 ≤ ‖x‖^2 * ‖x-y‖^2 := by
  rw [norm_sub_sq (𝕜 := ℂ), hy]
  have hr := Complex.re_le_norm (inner ℂ x y)
  change _ ≤ ‖x‖^2 * (‖x‖^2 - 2*(inner ℂ x y).re + ‖x‖^2)
  nlinarith [sq_nonneg (‖x‖^2 - ‖inner ℂ x y‖),
    mul_nonneg (sq_nonneg ‖x‖) (sub_nonneg.mpr hr)]

/-- For the one-site Gaussian seed the normalized return probability loses at most
(97/32)t². Both sides are multiplied by the fourth power of the Gaussian norm. -/
theorem unitCell_return_probability {T : UnboundedSelfAdjoint (L2d 1)}
    (hext : IsSelfAdjointExtension unitCell.innerHam T.op) (t : ℝ) :
    (1 - (97/32 : ℝ) * t^2) * ‖pgLp (d := 1) 1‖^4 ≤
      ‖inner ℂ (pgLp (d := 1) 1) (T.stoneU t (pgLp 1))‖^2 := by
  let x := pgLp (d := 1) 1
  let c := Complex.exp (-(Complex.I * (5/8) * t))
  have hc : ‖c‖ = 1 := by simp [c, Complex.norm_exp]
  have hn : ‖c • x‖ = ‖x‖ := by rw [norm_smul, hc, one_mul]
  have hy := T.norm_stoneU_apply t x
  have loss := overlap_loss (c • x) (T.stoneU t x) (hy.trans hn.symm)
  rw [hn, inner_smul_left, norm_mul, Complex.norm_conj, hc, one_mul, norm_sub_rev] at loss
  have err := unitCell_rankOne_error hext t
  change ‖T.stoneU t x - c • x‖^2 ≤ (97/32 : ℝ) * t^2 * ‖x‖^2 at err
  change (1 - (97/32 : ℝ) * t^2) * ‖x‖^4 ≤ ‖inner ℂ x (T.stoneU t x)‖^2
  nlinarith [mul_le_mul_of_nonneg_left err (sq_nonneg ‖x‖)]


end
end BookProof.Phi4
