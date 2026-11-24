import BookProof.Phi4.ChapterScalarRankTwo

/-!
# The full-action residual of the rank-two two-site seed

Frozen periodic-lattice comparison. The continuous-momentum orbit and return
interval are `ChapterScalarMomOrbit`.

The exact fixture column and the site operator identify the seed residual with the
ten-mode coefficient vector `fullColumns · 0 - (13/4) e₀`. This is the first
transport step from the rational compressed matrix to the full Stone orbit; the
matrix-exponential norm bound and the return interval are not yet included.
-/
namespace BookProof.Phi4.RankTwoOrbit

open BookProof.Phi4 BookProof.Phi4.RankTwo HermiteProductCore

noncomputable section

/-- The rank-two seed is the mode vacuum. -/
def seed : L2d 2 := pgLp (fromModes (modeTerm 0))

/-- The fixture's Gaussian diagonal energy. -/
def energy : ℂ := 13 / 4

/-- Residual coefficients in the ten-row exact column. -/
def residualCoeff (i : Fin 10) : ℂ :=
  ((fullColumns i 0).re : ℂ) - energy * (if i = 0 then 1 else 0)

/-- The synthesized ten-mode vector is the Gaussian image of the mode polynomial. -/
theorem synthesize_eq (c : Fin 10 → ℂ) :
    synthesize c = pgLp (fromModes (∑ i, c i • modeTerm i)) := by
  rw [show synthesize c = ∑ i, c i • pgLp (fromModes (modeTerm i)) from rfl]
  rw [show (∑ i, c i • pgLp (fromModes (modeTerm i))) =
      pgMap (d := 2) (∑ i, c i • fromModes (modeTerm i)) by
    rw [map_sum]
    simp only [map_smul, pgMap_apply]]
  simp only [pgMap_apply]
  congr 1
  rw [Finset.sum_congr rfl (fun i _ => (map_smul fromModes (c i) (modeTerm i)).symm)]
  rw [← map_sum]

/-- The full two-site Hamiltonian on the seed minus its Gaussian phase is the exact
ten-mode residual. -/
theorem twoSite_residual :
    (twoSite 1 1 1 (by norm_num) (by norm_num) (by norm_num)).innerHam
        ⟨pgLp (fromModes (modeHe 0 0 * modeHe 0 1)), pgLp_mem_core _⟩ -
      energy • pgLp (fromModes (modeHe 0 0 * modeHe 0 1)) =
    pgLp (fromModes (∑ i, residualCoeff i • modeTerm i)) := by
  have hfull := fullColumns_action 0
  have hsite := site_columns 0
  change modeHam 1 1 1 (modeHe 0 0 * modeHe 0 1) =
    ∑ i, ((fullColumns i 0).re : ℂ) • modeTerm i at hfull
  change (twoSite 1 1 1 (by norm_num) (by norm_num) (by norm_num)).innerHam
      ⟨pgLp (fromModes (modeHe 0 0 * modeHe 0 1)), pgLp_mem_core _⟩ =
    pgLp (fromModes (∑ i, ((fullColumns i 0).re : ℂ) • modeTerm i)) at hsite
  have hres : (∑ i, residualCoeff i • modeTerm i) =
      (∑ i, ((fullColumns i 0).re : ℂ) • modeTerm i) - energy • modeTerm 0 := by
    simp only [residualCoeff, sub_smul, Finset.sum_sub_distrib]
    congr 1
    simp [Finset.sum_ite_eq']
  rw [hsite]
  change pgMap (fromModes (∑ i, ((fullColumns i 0).re : ℂ) • modeTerm i)) -
      energy • pgMap (fromModes (modeHe 0 0 * modeHe 0 1)) =
    pgMap (fromModes (∑ i, residualCoeff i • modeTerm i))
  rw [← map_smul (pgMap (d := 2)) energy, ← map_sub]
  rw [← map_smul (fromModes) energy, ← map_sub]
  rw [hres]
  rfl

end
end BookProof.Phi4.RankTwoOrbit
