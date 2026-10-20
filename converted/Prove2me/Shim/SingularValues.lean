import Mathlib

/-!
# Shim: singular values of a linear map between finite-dimensional inner product spaces

Stands in for the platform Mathlib file `Mathlib.Analysis.InnerProductSpace.SingularValues`,
which is not part of the pinned Mathlib.  It provides the platform names used by the
converted modules:

* `LinearMap.singularValues T : ℕ →₀ ℝ` -- the singular values of `T`, in decreasing order,
  counted with multiplicity: for `k < finrank 𝕜 E` the value at `k` is the square root of the
  `k`-th eigenvalue (in decreasing order) of the positive operator `T† T`, and it is `0` for
  `k ≥ finrank 𝕜 E`;
* `LinearMap.singularValues_fin`, `LinearMap.sq_singularValues_fin`,
  `LinearMap.singularValues_nonneg`, `LinearMap.singularValues_of_finrank_le`.
-/

open Module

namespace LinearMap

variable {𝕜 E F : Type*} [RCLike 𝕜] [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F] [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

/-- `T† T` is symmetric. -/
theorem isSymmetric_adjoint_comp_self (T : E →ₗ[𝕜] F) : (adjoint T ∘ₗ T).IsSymmetric :=
  (isPositive_adjoint_comp_self T).isSymmetric

/-- The singular values of `T`, in decreasing order and counted with multiplicity, as a
finitely supported sequence: the `k`-th one is `√(λₖ(T† T))` for `k < finrank 𝕜 E`, and `0`
afterwards. -/
noncomputable def singularValues (T : E →ₗ[𝕜] F) : ℕ →₀ ℝ :=
  Finsupp.embDomain Fin.valEmbedding <| Finsupp.equivFunOnFinite.symm fun i =>
    √(T.isSymmetric_adjoint_comp_self.eigenvalues rfl i)

theorem singularValues_fin (T : E →ₗ[𝕜] F) {n : ℕ} (hn : finrank 𝕜 E = n) (i : Fin n) :
    T.singularValues i = √(T.isSymmetric_adjoint_comp_self.eigenvalues hn i) := by
  subst hn
  have := Finsupp.embDomain_apply_self Fin.valEmbedding
    (Finsupp.equivFunOnFinite.symm fun i =>
      √(T.isSymmetric_adjoint_comp_self.eigenvalues rfl i)) i
  simpa [singularValues] using this

theorem singularValues_nonneg (T : E →ₗ[𝕜] F) (k : ℕ) : 0 ≤ T.singularValues k := by
  by_cases hk : k < finrank 𝕜 E
  · have := T.singularValues_fin rfl ⟨k, hk⟩
    simp only at this
    rw [this]
    exact Real.sqrt_nonneg _
  · rw [singularValues, Finsupp.embDomain_notin_range]
    rintro ⟨i, rfl⟩
    exact hk i.2

theorem singularValues_of_finrank_le (T : E →ₗ[𝕜] F) {k : ℕ} (hk : finrank 𝕜 E ≤ k) :
    T.singularValues k = 0 := by
  rw [singularValues, Finsupp.embDomain_notin_range]
  rintro ⟨i, rfl⟩
  exact absurd i.2 (not_lt.mpr hk)

theorem sq_singularValues_fin (T : E →ₗ[𝕜] F) {n : ℕ} (hn : finrank 𝕜 E = n) (i : Fin n) :
    T.singularValues i ^ 2 = T.isSymmetric_adjoint_comp_self.eigenvalues hn i := by
  rw [T.singularValues_fin hn i, Real.sq_sqrt]
  subst hn
  have h := (isPositive_adjoint_comp_self T).inner_nonneg_left
    (T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl i)
  rw [T.isSymmetric_adjoint_comp_self.apply_eigenvectorBasis, inner_smul_left] at h
  simpa [(T.isSymmetric_adjoint_comp_self.eigenvectorBasis rfl).orthonormal.1 i] using h

end LinearMap
