import BookProof.ChapterBrstHarmonicDecomposition

open BookProof.BrstHarmonicDecomposition BookProof.BrstReducedTransfer

/-- A genuinely non-zero nilpotent charge on `ℂ × ℂ`: `(x₁, x₂) ↦ (0, x₁)`. -/
noncomputable def nilOp : ℂ × ℂ →L[ℂ] ℂ × ℂ :=
  (0 : ℂ × ℂ →L[ℂ] ℂ).prod (ContinuousLinearMap.fst ℂ ℂ ℂ)

example : ∀ x, nilOp (nilOp x) = 0 := by
  intro x
  simp [nilOp]

/-- The non-degenerate case: the two summands of the Hodge decomposition are both nontrivial and
together fill the space. -/
example : exactStates nilOp ⊔ harmonicStates nilOp = ⊤ := by
  rw [sup_exact_harmonic nilOp (by intro x; simp [nilOp])]
  simp [physicalStates, nilOp]

/-- The BRST norm on the non-degenerate charge is the norm of the first coordinate — the norm of
the harmonic representative. -/
example (x : ℂ × ℂ) : Metric.infDist x (exactStates nilOp) = ‖x.1‖ := by
  rw [infDist_eq_norm_harmonicPart]
  have : exactStates nilOp = (LinearMap.range (nilOp : ℂ × ℂ →ₗ[ℂ] ℂ × ℂ)).topologicalClosure := rfl
  sorry
