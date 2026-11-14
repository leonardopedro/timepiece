import BookProof.OSReconstruction.HalfSpaceExpIdentification

/-!
# The two-point form of `hflow`

`hflow` (`HalfSpaceExpIdentification`) is the *strong* statement that the abstract semigroup
`hsEvolCompletionFun` has right derivative `−H z` at `0` in the Hilbert norm.  This module records
the exact consequence that survives when the derivative is only tested against vectors, which is
the form the OS reconstruction actually uses (matrix elements of the transfer operator):

`hasDerivWithinAt_inner_hsEvol` — for all `y z`, the scalar orbit `τ ↦ ⟪y, P τ z⟫` has right
derivative `⟪y, −H z⟫` at `0⁺`.

This is a genuine theorem, not a restatement: the pair `(hflow, matrix element)` is one of the
places where the corpus could silently assume more than it has, and here the derivation is short
because `HasDerivWithinAt.inner` handles the bilinear product (the second factor's derivative is
`0`, since `y` is constant).

## What the converse would need

The reverse implication is **not** available from this module, and not from any boundedness
hypothesis either.  Weak convergence plus a uniform norm bound does not give strong convergence:
in `ℓ²(ℕ)` the basis vectors `e_n` are weakly null with `‖e_n‖ = 1` but not strongly null.  So the
two-point form alone cannot recover `hflow`; the difference quotients of the orbit would have to
converge in norm (or the semigroup's continuity in `τ` would have to be used, which is exactly the
generator/Stone content of `HalfSpaceExpIdentification`).  Recording the one direction honestly is
the point of this module: it is the direction that is provable from the abstract data.
-/

namespace BookProof.OSReconstruction

open BookProof.ReflectionPositivity
open Filter Set
open scoped Topology RealInnerProductSpace

noncomputable section

variable {Λ : HalfSpaceState} {T : TimeTranslation}

/-- **The two-point (matrix-element) form of `hflow`.**  If every orbit has right derivative
`−H z` at `0⁺` in norm, then for every pair `y, z` the scalar orbit `τ ↦ ⟪y, P τ z⟫` has right
derivative `⟪y, −H z⟫`. -/
theorem hasDerivWithinAt_inner_hsEvol (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT)
    (H : Hhalf Λ →L[ℝ] Hhalf Λ)
    (hflow : ∀ z : Hhalf Λ, HasDerivWithinAt
      (fun τ : ℝ => hsEvolCompletionFun Λ hT hinv τ z) (-(H z)) (Ioi 0) 0)
    (y z : Hhalf Λ) :
    HasDerivWithinAt (fun τ : ℝ => ⟪y, (hsEvolCompletionFun Λ hT hinv τ z)⟫)
      ⟪y, -(H z)⟫ (Ioi 0) 0 := by
  have hinner :=
    (hasDerivWithinAt_const (x := (0 : ℝ)) (s := Ioi 0) y).inner (𝕜 := ℝ) (hflow z)
  simpa [hsEvolCompletionFun_zero, ContinuousLinearMap.one_apply, inner_zero_left] using hinner

/-- **The same statement in slope form**: the difference quotients of the matrix element converge
to `⟪y, −H z⟫` from the right. -/
theorem tendsto_slope_inner_hsEvol (hT : PreservesPositiveTime T) (hinv : HsHinv Λ hT)
    (H : Hhalf Λ →L[ℝ] Hhalf Λ)
    (hflow : ∀ z : Hhalf Λ, HasDerivWithinAt
      (fun τ : ℝ => hsEvolCompletionFun Λ hT hinv τ z) (-(H z)) (Ioi 0) 0)
    (y z : Hhalf Λ) :
    Tendsto (fun τ : ℝ => τ⁻¹ * (⟪y, (hsEvolCompletionFun Λ hT hinv τ z)⟫ - ⟪y, z⟫))
      (𝓝[>] 0) (𝓝 ⟪y, -(H z)⟫) := by
  have h := hasDerivWithinAt_inner_hsEvol hT hinv H hflow y z
  have hslope := (hasDerivWithinAt_iff_tendsto_slope).1 h
  have hdiff : Ioi (0 : ℝ) \ {0} = Ioi 0 := diff_singleton_eq_self (by simp)
  rw [hdiff] at hslope
  refine hslope.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with τ _
  rw [slope_def_field, sub_zero, hsEvolCompletionFun_zero, div_eq_inv_mul]

end

end BookProof.OSReconstruction
