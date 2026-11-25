import Mathlib
import BookProof.Sirk.ChapterSirkRitzMinMax

/-!
# Chapter MinMaxCount — the U3 Courant–Fischer count interface

U3 needs an *ordered* spectral count: a level `b` above a certified edge must be shown to
be the second Courant–Fischer level, not merely a number larger than a residual.  This
module proves the count step in the form in which the SIRK chain actually supplies it:
a quadratic-form bound on the orthogonal complement of an identified vector forces the
`k = 1` min–max level to be at least `b`.

The argument is elementary dimension counting.  A two-dimensional subspace `S` intersects
the codimension-one subspace `yᗮ` nontrivially (the linear functional `x ↦ ⟪y,x⟫` on `S`
has a nontrivial kernel).  At a nonzero `u ∈ S ∩ yᗮ` the form bound applies; after
normalizing, its Rayleigh value lies in `rayleighSetOn A S`, so `b` is below the supremum
over `S`, and hence below the infimum over all two-dimensional subspaces.

This is the `k = 1` inequality the plan records as missing (`ChapterSirkRitzMinMax`
identifies only `k = 0` with the bottom of the spectrum).  It is **not** an equality and
does not by itself produce ordered resolvent values or prove `b` is an eigenvalue; U3's
min–max/counting input still has to identify the edge and its multiplicity.  No
compactness, spectral theorem or continuum claim is used.  Axioms are `propext`,
`Classical.choice`, `Quot.sound` only.
-/

set_option maxHeartbeats 400000

noncomputable section

namespace BookProof.MinMaxCount

open BookProof.RitzMinMax

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

omit [CompleteSpace F] in
/-- If `b‖z‖² ≤ rayleighVal A z` on `yᗮ`, then every two-dimensional subspace has a unit
    vector in `yᗮ`, so `b` lies below its Rayleigh supremum and below the second min–max
    level. -/
theorem minmaxLevel_one_ge_of_formBound_on_orthogonal {A : F →L[ℂ] F} {y : F} {b : ℝ}
    (hform : ∀ z ∈ (ℂ ∙ y)ᗮ, b * ‖z‖ ^ 2 ≤ rayleighVal A z)
    (hdim : ∃ S : Submodule ℂ F, Module.finrank ℂ S = 2) :
    b ≤ minmaxLevel A 1 := by
  classical
  refine le_csInf ?hne ?_
  · rcases hdim with ⟨S, hS⟩
    exact ⟨rayleighSup A S, ⟨S, hS, rfl⟩⟩
  · intro t ht
    rcases ht with ⟨S, hSfin, rfl⟩
    haveI : FiniteDimensional ℂ S :=
      FiniteDimensional.of_finrank_pos (by rw [hSfin]; norm_num)
    let f : S →ₗ[ℂ] ℂ :=
      { toFun := fun x => inner ℂ y (x : F)
        map_add' := by intro x z; simp
        map_smul' := by intro c x; simp }
    have hrange : Module.finrank ℂ f.range ≤ 1 := by
      calc
        Module.finrank ℂ f.range ≤ Module.finrank ℂ ℂ := Submodule.finrank_le _
        _ = 1 := Module.finrank_self _
    have hker : f.ker ≠ ⊥ := by
      intro hbot
      have hker0 : Module.finrank ℂ f.ker = 0 := by rw [hbot]; simp
      have hsum := LinearMap.finrank_range_add_finrank_ker f
      omega
    haveI : Nontrivial f.ker := (Submodule.nontrivial_iff_ne_bot).2 hker
    obtain ⟨u, hu⟩ := exists_ne (0 : f.ker)
    have hu_norm_pos : 0 < ‖(u : F)‖ := by
      rw [norm_pos_iff]
      intro hzero
      apply hu
      ext
      simpa using hzero
    have hu_inner : inner ℂ y (u : F) = 0 := by
      have hf : f (u : S) = 0 := (u : f.ker).property
      change inner ℂ y (u : F) = 0 at hf
      exact hf
    have hu_orth : (u : F) ∈ (ℂ ∙ y)ᗮ :=
      Submodule.mem_orthogonal_singleton_iff_inner_right.mpr hu_inner
    have hv_mem : (‖(u : F)‖⁻¹ : ℂ) • (u : F) ∈ S := by
      exact S.smul_mem _ (u : S).property
    have hc_norm : ‖(‖(u : F)‖⁻¹ : ℂ)‖ = ‖(u : F)‖⁻¹ := by
      simp [Complex.norm_real]
    have hv_norm : ‖(‖(u : F)‖⁻¹ : ℂ) • (u : F)‖ = 1 := by
      rw [norm_smul, hc_norm]
      exact inv_mul_cancel₀ hu_norm_pos.ne'
    have hv_orth : (‖(u : F)‖⁻¹ : ℂ) • (u : F) ∈ (ℂ ∙ y)ᗮ := by
      exact (ℂ ∙ y)ᗮ.smul_mem _ hu_orth
    have hu_val := hform (u : F) hu_orth
    have hv_eq : rayleighVal A ((‖(u : F)‖⁻¹ : ℂ) • (u : F)) =
        rayleighVal A (u : F) / ‖(u : F)‖ ^ 2 := by
      rw [rayleighVal_smul]
      rw [hc_norm]
      field_simp [hu_norm_pos.ne']
    have hb_v : b ≤ rayleighVal A ((‖(u : F)‖⁻¹ : ℂ) • (u : F)) := by
      rw [hv_eq]
      exact (le_div_iff₀ (sq_pos_of_pos hu_norm_pos)).2 (by simpa [mul_comm] using hu_val)
    exact hb_v.trans (rayleighVal_le_rayleighSup A hv_mem hv_norm)

end BookProof.MinMaxCount
