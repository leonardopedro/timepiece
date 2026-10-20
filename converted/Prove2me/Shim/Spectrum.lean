import Mathlib

/-!
# Shim: roots of the characteristic polynomial of a symmetric operator

The platform Mathlib provides `LinearMap.IsSymmetric.roots_charpoly_eq_eigenvalues`, the
operator counterpart of the pinned `Matrix.IsHermitian.roots_charpoly_eq_eigenvalues`: the roots
of the characteristic polynomial of a symmetric operator on a finite-dimensional inner product
space are its eigenvalues, with multiplicity.  It is proved here by diagonalising in the
eigenvector basis.
-/

open Module Polynomial

namespace LinearMap.IsSymmetric

variable {𝕜 E : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [FiniteDimensional 𝕜 E] {T : E →ₗ[𝕜] E}

theorem roots_charpoly_eq_eigenvalues (hT : T.IsSymmetric) {n : ℕ} (hn : finrank 𝕜 E = n) :
    T.charpoly.roots = Multiset.map (RCLike.ofReal ∘ hT.eigenvalues hn) Finset.univ.val := by
  have hdiag : LinearMap.toMatrix (hT.eigenvectorBasis hn).toBasis
      (hT.eigenvectorBasis hn).toBasis T = Matrix.diagonal fun i => (hT.eigenvalues hn i : 𝕜) := by
    ext i j
    rw [LinearMap.toMatrix_apply, OrthonormalBasis.coe_toBasis, hT.apply_eigenvectorBasis,
      map_smul, Finsupp.smul_apply, OrthonormalBasis.coe_toBasis_repr_apply, OrthonormalBasis.repr_self,
      Matrix.diagonal_apply]
    by_cases h : i = j
    · subst h; simp
    · rw [EuclideanSpace.single_apply, if_neg h, if_neg h, smul_zero]
  rw [← T.charpoly_toMatrix (hT.eigenvectorBasis hn).toBasis, hdiag, Matrix.charpoly_diagonal, Polynomial.roots_prod]
  · simp
  · simp [Finset.prod_ne_zero_iff, Polynomial.X_sub_C_ne_zero]

end LinearMap.IsSymmetric
