import BookProof.ChapterBrstHarmonicDecomposition

open BookProof.BrstHarmonicDecomposition BookProof.BrstReducedTransfer

/-- The zero charge: exact states are trivial, harmonic states are everything. -/
example : exactStates (0 : ℂ →L[ℂ] ℂ) = ⊥ := by
  simp [exactStates]

example : harmonicStates (0 : ℂ →L[ℂ] ℂ) = ⊤ := by
  simp [harmonicStates, physicalStates]

/-- The Hodge decomposition holds for the zero charge (deliberately the degenerate case). -/
example : harmonicStates (0 : ℂ →L[ℂ] ℂ) ⊔ exactStates (0 : ℂ →L[ℂ] ℂ)
    ⊔ coexactStates (0 : ℂ →L[ℂ] ℂ) = ⊤ :=
  hodge_decomposition (0 : ℂ →L[ℂ] ℂ) (by simp)

/-- The quotient norm is realised by the harmonic representative: on the zero charge the
quotient is by `⊥`, so the BRST norm must be the ordinary norm. -/
example (x : ℂ) : Metric.infDist x (exactStates (0 : ℂ →L[ℂ] ℂ)) = ‖x‖ := by
  rw [infDist_eq_norm_harmonicPart]
  have h : (exactStates (0 : ℂ →L[ℂ] ℂ)) = ⊥ := by simp [exactStates]
  simp [harmonicPart, h]

/-- The representative is a class function for the zero charge (every state is already
harmonic, so nothing is added). -/
example (x : ℂ) : harmonicPart (0 : ℂ →L[ℂ] ℂ) x = x := by
  have h : (exactStates (0 : ℂ →L[ℂ] ℂ)) = ⊥ := by simp [exactStates]
  simp [harmonicPart, h]
