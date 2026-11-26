import Mathlib
import BookProof.OSReconstruction.ChapterPathMeasureInduction

/-!
# Chapter PathMeasureMarginal — H3's projective consistency at the last slice

The finite path measures `pathMeasure x ρ` of `ChapterFinitePathMeasure` form a projective
family: marginalizing away the final time slice recovers the path measure with the final
transition kernel removed.  This is the consistency input for an Ionescu–Tulcea / Kolmogorov
extension of the Mehler path measures to continuous time, and completes the structure half of
H3's `N → ∞` limit.  No continuum limit or interacting measure is claimed here.

The proof splits the path at its last coordinate via `MeasurableEquiv.piFinSuccAbove`, rewrites
the set integral as a pushforward integral (`lintegral_map`), applies Tonelli and the kernel
normalization `mehlerKernel_lintegral`, then identifies the remaining density integral with the
smaller path measure.
-/

set_option maxHeartbeats 1200000

noncomputable section

namespace BookProof.PathMeasureMarginal

open MeasureTheory Filter Topology
open BookProof.FinitePathMeasure
open BookProof.PathMeasureInduction
open BookProof.TwoSlicePathMeasure
open BookProof.MehlerTransitionDensity

/-- The projection dropping the last time slice. -/
def dropLast {N : ℕ} (z : Fin (N + 2) → ℝ) : Fin (N + 1) → ℝ := fun i => z i.castSucc

/-- Measurability of the last-slice projection. -/
theorem measurable_dropLast {N : ℕ} : Measurable (@dropLast N) := by
  exact measurable_pi_lambda _ (fun i => measurable_pi_apply i.castSucc)

/-- The projection is the second component of the last-coordinate splitting. -/
theorem dropLast_eq_snd {N : ℕ} :
    dropLast = fun z : Fin (N + 2) → ℝ =>
      (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 2) => ℝ) (Fin.last (N + 1)) z).2 := by
  funext z i
  simp [dropLast, MeasurableEquiv.piFinSuccAbove, Fin.init]

/-- Marginalizing away the last time slice of the path measure gives the smaller path measure. -/
theorem pathMeasure_marginal {N : ℕ} (ρ : Fin (N + 1) → ℝ)
    (hρ : ∀ i, (ρ i) ^ 2 < 1) (x : ℝ) :
    Measure.map (@dropLast N) (pathMeasure x ρ) =
      pathMeasure x (fun j : Fin N => ρ j.castSucc) := by
  ext s hs
  rw [Measure.map_apply measurable_dropLast hs]
  dsimp [pathMeasure]
  rw [withDensity_apply _ (measurable_dropLast hs)]
  let e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 2) => ℝ) (Fin.last (N + 1))
  let ρ' : Fin N → ℝ := fun j => ρ j.castSucc
  have hpre : dropLast ⁻¹' s = e ⁻¹' (Set.univ ×ˢ s) := by
    rw [dropLast_eq_snd]
    ext z
    simp [e, MeasurableEquiv.piFinSuccAbove]
  rw [hpre]
  have hpre_meas : MeasurableSet (e ⁻¹' (Set.univ ×ˢ s)) :=
    (MeasurableSet.univ.prod hs).preimage e.measurable
  have hmap :
      (∫⁻ z in e ⁻¹' (Set.univ ×ˢ s), pathDensity ρ z ∂pathBase x (N + 1)) =
        ∫⁻ p, (Set.univ ×ˢ s).indicator (fun p => pathDensity ρ (e.symm p)) p
          ∂(Measure.map e (pathBase x (N + 1))) := by
    rw [← lintegral_indicator hpre_meas (pathDensity ρ)]
    rw [lintegral_map]
    · apply lintegral_congr_ae
      exact Filter.Eventually.of_forall (fun z => by
        change (e ⁻¹' (Set.univ ×ˢ s)).indicator (pathDensity ρ) z =
          (Set.univ ×ˢ s).indicator (fun p => pathDensity ρ (e.symm p)) (e z)
        by_cases hz : z ∈ e ⁻¹' (Set.univ ×ˢ s)
        · rw [Set.indicator_of_mem hz]
          have hez : e z ∈ Set.univ ×ˢ s := hz
          rw [Set.indicator_of_mem hez]
          simp
        · rw [Set.indicator_of_notMem hz]
          have hez : e z ∉ Set.univ ×ˢ s := hz
          rw [Set.indicator_of_notMem hez])
    · exact ((pathDensity_measurable ρ hρ).comp e.symm.measurable).indicator
        (MeasurableSet.univ.prod hs)
    · exact e.measurable
  rw [hmap, pathBase_split]
  have hf_meas : Measurable (fun p : ℝ × (Fin (N + 1) → ℝ) =>
      (Set.univ ×ˢ s).indicator (fun p => pathDensity ρ (e.symm p)) p) :=
    ((pathDensity_measurable ρ hρ).comp e.symm.measurable).indicator
      (MeasurableSet.univ.prod hs)
  rw [lintegral_prod_symm (f := fun p : ℝ × (Fin (N + 1) → ℝ) =>
      (Set.univ ×ˢ s).indicator (fun p => pathDensity ρ (e.symm p)) p) hf_meas.aemeasurable]
  change (∫⁻ y : Fin (N + 1) → ℝ,
      (∫⁻ t : ℝ, (Set.univ ×ˢ s).indicator (fun p => pathDensity ρ (e.symm p)) (t, y) ∂volume)
      ∂pathBase x N) = _
  have hinner : ∀ y : Fin (N + 1) → ℝ,
      (∫⁻ t : ℝ, (Set.univ ×ˢ s).indicator (fun p => pathDensity ρ (e.symm p)) (t, y) ∂volume) =
        s.indicator (pathDensity ρ') y := by
    intro y
    by_cases hy : y ∈ s
    · rw [Set.indicator_of_mem hy]
      have hf_eq : (fun t : ℝ =>
          (Set.univ ×ˢ s).indicator (fun p => pathDensity ρ (e.symm p)) (t, y)) =
          fun t : ℝ => pathDensity ρ (e.symm (t, y)) := by
        funext t
        rw [Set.indicator_of_mem (show (t, y) ∈ Set.univ ×ˢ s by simp [hy])]
      rw [hf_eq]
      rw [show (fun t : ℝ => pathDensity ρ (e.symm (t, y))) =
          (fun t : ℝ => pathDensity ρ' y *
            ENNReal.ofReal (mehlerKernel (ρ (Fin.last N)) (y (Fin.last N)) t)) by
        funext t
        exact density_symm_last ρ (t, y)]
      have hpd_ne : pathDensity ρ' y ≠ ⊤ := by
        apply ENNReal.prod_ne_top
        intro j hj
        exact ENNReal.ofReal_ne_top
      simp_rw [mul_comm]
      rw [lintegral_mul_const' _ _ hpd_ne]
      rw [mehlerKernel_lintegral (hρ (Fin.last N)) (y (Fin.last N))]
      simp
    · rw [Set.indicator_of_notMem hy]
      have hf_eq : (fun t : ℝ =>
          (Set.univ ×ˢ s).indicator (fun p => pathDensity ρ (e.symm p)) (t, y)) =
          fun _ : ℝ => 0 := by
        funext t
        rw [Set.indicator_of_notMem (show (t, y) ∉ Set.univ ×ˢ s by simp [hy])]
      rw [hf_eq]
      simp
  simp_rw [hinner]
  rw [lintegral_indicator hs]
  dsimp [pathMeasure, ρ']
  rw [withDensity_apply _ hs]

end BookProof.PathMeasureMarginal
