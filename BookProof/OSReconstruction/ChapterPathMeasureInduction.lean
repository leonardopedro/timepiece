import Mathlib
import BookProof.OSReconstruction.ChapterFinitePathMeasure
import BookProof.ReflectionPositivity.ChapterMehlerTransitionDensity
import BookProof.OSReconstruction.ChapterTwoSlicePathMeasure

/-!
# Chapter PathMeasureInduction — the Tonelli induction for the finite path measure

Uses `pathBase_split` and `pathDensity_last` to prove by induction that the `N`-slice path
measure of `ChapterFinitePathMeasure` has total mass one: the integral over the path base is
mapped to `volume.prod (pathBase x N)`, Tonelli integrates the final kernel in the final
configuration (value one), and the induction hypothesis handles the retained path.

This completes the normalization half of H3's finite-slice path measure.  The interacting
Strang weight and the `N → ∞` transfer remain open.  Axioms are `propext`,
`Classical.choice`, `Quot.sound` only.
-/

set_option maxHeartbeats 800000

noncomputable section

namespace BookProof.PathMeasureInduction

open MeasureTheory Filter Topology
open BookProof.FinitePathMeasure
open BookProof.MehlerTransitionDensity
open BookProof.TwoSlicePathMeasure

/-- The density under the inverse last-coordinate splitting. -/
theorem density_symm_last {N : ℕ} (ρ : Fin (N + 1) → ℝ)
    (p : ℝ × (Fin (N + 1) → ℝ)) :
    pathDensity ρ ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 2) => ℝ)
      (Fin.last (N + 1))).symm p) =
      pathDensity (fun j : Fin N => ρ j.castSucc) p.2 *
        ENNReal.ofReal (mehlerKernel (ρ (Fin.last N)) (p.2 (Fin.last N)) p.1) := by
  rw [pathDensity_last]
  congr 2
  · funext j
    simp
  · simp

/-- Normalization of the path measure, by induction on the slice count. -/
theorem pathMeasure_univ : ∀ (N : ℕ) (ρ : Fin N → ℝ), (∀ i, (ρ i) ^ 2 < 1) → ∀ x : ℝ,
    pathMeasure x ρ Set.univ = 1 := by
  intro N
  induction N with
  | zero =>
      intro ρ hρ x
      exact pathMeasure_zero x
  | succ N ih =>
      intro ρ hρ x
      dsimp [pathMeasure]
      rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
      let e := (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (N + 2) => ℝ)
        (Fin.last (N + 1)))
      let f : ℝ × (Fin (N + 1) → ℝ) → ENNReal := fun p => pathDensity ρ (e.symm p)
      have hf : Measurable f := by
        dsimp [f]
        exact (pathDensity_measurable ρ hρ).comp e.symm.measurable
      have hsplit := pathBase_split x N
      calc
        (∫⁻ z : Fin (N + 2) → ℝ, pathDensity ρ z ∂pathBase x (N + 1)) =
            ∫⁻ p : ℝ × (Fin (N + 1) → ℝ), f p ∂(volume.prod (pathBase x N)) := by
          symm
          rw [← hsplit]
          rw [lintegral_map hf e.measurable]
          apply lintegral_congr_ae
          exact Filter.Eventually.of_forall (fun a => by simp [f])
        _ = 1 := by
          change (∫⁻ p : ℝ × (Fin (N + 1) → ℝ), pathDensity ρ (e.symm p)
            ∂(volume.prod (pathBase x N))) = 1
          conv_lhs =>
            enter [2, p]
            rw [density_symm_last]
          have htail_all : ∀ i : Fin N, (ρ i.castSucc) ^ 2 < 1 := by
            intro i
            exact hρ (i.castSucc)
          rw [lintegral_prod_symm]
          · simp_rw [mul_comm]
            have hinner : ∀ rest : Fin (N + 1) → ℝ,
                (∫⁻ y : ℝ, ENNReal.ofReal (mehlerKernel (ρ (Fin.last N))
                    (rest (Fin.last N)) y) *
                  pathDensity (fun j : Fin N => ρ j.castSucc) rest ∂volume) =
                pathDensity (fun j : Fin N => ρ j.castSucc) rest := by
              intro rest
              have hpd_ne : pathDensity (fun j : Fin N => ρ j.castSucc) rest ≠ ⊤ := by
                apply ENNReal.prod_ne_top
                intro j hj
                exact ENNReal.ofReal_ne_top
              rw [lintegral_mul_const' _ _ hpd_ne]
              rw [mehlerKernel_lintegral (hρ (Fin.last N)) (rest (Fin.last N))]
              simp
            simp_rw [hinner]
            have htail : ∀ i : Fin N, (ρ i.castSucc) ^ 2 < 1 := by
              intro i
              exact hρ (i.castSucc)
            have hi := ih (fun i : Fin N => ρ i.castSucc) htail x
            dsimp [pathMeasure] at hi
            rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] at hi
            exact hi
          · have htail_meas : Measurable (fun p : ℝ × (Fin (N + 1) → ℝ) =>
                pathDensity (fun j : Fin N => ρ j.castSucc) p.2) :=
              (pathDensity_measurable (fun j : Fin N => ρ j.castSucc) htail_all).comp
                measurable_snd
            have hk_meas : Measurable (fun p : ℝ × (Fin (N + 1) → ℝ) =>
                ENNReal.ofReal (mehlerKernel (ρ (Fin.last N)) (p.2 (Fin.last N)) p.1)) := by
              have hc : Continuous (fun p : ℝ × (Fin (N + 1) → ℝ) =>
                  mehlerKernel (ρ (Fin.last N)) (p.2 (Fin.last N)) p.1) := by
                unfold mehlerKernel
                fun_prop
              exact hc.measurable.ennreal_ofReal
            exact (htail_meas.mul hk_meas).aemeasurable

end BookProof.PathMeasureInduction
