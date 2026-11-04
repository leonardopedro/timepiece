import Mathlib
import BookProof.ReflectionPositivity.Involution

/-!
# `θ` commutes with block averaging: `θ Q_k = Q_k θ`

Plan: `cftproof.md`, Phase 3.1 — "Check `θ² = 1`, `θ` preserves the measure `θ * dγ = dγ`, and
`θ` commutes with `Q_k`".  The first two are in `ReflectionPositivity.Involution`; this module
proves the third, which `ReflectionPositivity.Involution` and `OSReconstruction.Hamiltonian`
carried as a hypothesis.

## Why it is true

`Q_k` (`BalabanRG.blockAveragingOp`) is the orthogonal projection of a sector onto the
block-constant subspace `blockConst`: the field is replaced by its average over each block.  The
time reflection `θ` moves a component from cell `c` to the reflected cell `flipCell c` and leaves
its `μ` index alone, so it maps blocks to blocks and hence permutes the coordinates of
`blockConst` among themselves.  An isometry preserving a subspace commutes with the orthogonal
projection onto it.

## Contents

* `reflectEquiv` — `reflectCoord` as an `Equiv` (it is an involution), and
  `fieldReflectionSector` — `θ` on a sector `ℱ_k` as a `LinearIsometryEquiv`, with the coordinate
  formula `fieldReflectionSector_apply : (θx)_i = x_{θi}`;
* `blockOf_reflectCoord` — **the block structure is `θ`-stable**:
  `blockOf (θ i) = flipCell (blockOf i)`;
* `mem_blockConst_fieldReflectionSector` — `θ` preserves the block-constant subspace (both
  directions, using `flipCell`'s injectivity);
* `blockConst_map_fieldReflectionSector` — the same statement at the level of submodules,
  `blockConst.map θ = blockConst`;
* **`fieldReflectionSector_blockAveragingOp`** — `θ (Q_k x) = Q_k (θ x)`, the commutation
  `θ Q_k = Q_k θ`, and its total-space form `theta_commutes_blockAveraging` on `FTotal = ⊕_k ℱ_k`.

## Note on the block structure

`blockOf` is defined in `BalabanRG.BlockOperator` as the *cell* of a component index, read
through the split `coordOf : Fin latticeDim → Fin nComponents × Fin cellsPerBlock` of
`BalabanRG.MultiscaleSpace`.  That split is what `reflectCoord` permutes, so "one block = the
`nComponents` components `A_μ` at one lattice cell" is precisely the choice that makes the block
structure `θ`-stable.  (Grouping consecutive indices instead would mix the `μ` slots into
different blocks and destroy the commutation.)
-/

namespace BookProof.ReflectionPositivity

open BookProof.BalabanRG

open scoped InnerProductSpace

noncomputable section

/-! ## `θ` as an equiv and as an isometry of a sector -/

/-- The component reflection `i ↦ θi` as an equivalence (it is an involution). -/
def reflectEquiv : Fin latticeDim ≃ Fin latticeDim where
  toFun := reflectCoord
  invFun := reflectCoord
  left_inv := reflectCoord_involutive
  right_inv := reflectCoord_involutive

@[simp]
theorem reflectEquiv_apply (i : Fin latticeDim) : reflectEquiv i = reflectCoord i := rfl

@[simp]
theorem reflectEquiv_symm_apply (i : Fin latticeDim) : reflectEquiv.symm i = reflectCoord i := rfl

/-- The reflection is its own inverse, as an equivalence. -/
theorem reflectEquiv_symm : reflectEquiv.symm = reflectEquiv := by
  ext i
  rfl

/-- **The time reflection on a sector** `ℱ_k`, as a linear isometry: it permutes the component
coordinates by `reflectCoord`. -/
def fieldReflectionSector (k : ℕ) : Sector k ≃ₗᵢ[ℝ] Sector k :=
  LinearIsometryEquiv.piLpCongrLeft 2 ℝ ℝ reflectEquiv

/-- The coordinate formula `(θx)_i = x_{θi}`. -/
theorem fieldReflectionSector_apply (k : ℕ) (x : Sector k) (i : Fin latticeDim) :
    fieldReflectionSector k x i = x (reflectCoord i) := by
  simp [fieldReflectionSector, Equiv.piCongrLeft'_apply]

/-- `θ` is an involution on a sector. -/
theorem fieldReflectionSector_symm_eq (k : ℕ) :
    (fieldReflectionSector k).symm = fieldReflectionSector k := by
  rw [fieldReflectionSector, LinearIsometryEquiv.piLpCongrLeft_symm, reflectEquiv_symm]

/-- The inverse of `θ` acts by the same coordinate formula (`θ` is an involution). -/
theorem fieldReflectionSector_symm_apply (k : ℕ) (x : Sector k) (i : Fin latticeDim) :
    (fieldReflectionSector k).symm x i = x (reflectCoord i) := by
  rw [fieldReflectionSector_symm_eq, fieldReflectionSector_apply]

/-! ## The block structure is `θ`-stable -/

/-- **`θ` moves a component to the reflected cell of the same block.** -/
theorem blockOf_reflectCoord (i : Fin latticeDim) :
    blockOf (reflectCoord i) = flipCell (blockOf i) := by
  have h : coordOf (reflectCoord i) = ((coordOf i).1, flipCell (coordOf i).2) := by
    have h' := coordOf_coordIdx ((coordOf i).1, flipCell (coordOf i).2)
    rwa [show coordIdx ((coordOf i).1, flipCell (coordOf i).2) = reflectCoord i from rfl] at h'
  unfold blockOf
  rw [h]

/-- The `θ`-stability of the block partition: two components lie in the same block iff their
reflections do. -/
theorem blockOf_reflectCoord_eq_iff (i j : Fin latticeDim) :
    blockOf (reflectCoord i) = blockOf (reflectCoord j) ↔ blockOf i = blockOf j := by
  have hinj : Function.Injective flipCell :=
    fun a b h => by
      have h' := congrArg flipCell h
      rwa [flipCell_involutive a, flipCell_involutive b] at h'
  rw [blockOf_reflectCoord, blockOf_reflectCoord]
  constructor
  · exact fun h => hinj h
  · intro h
    rw [h]

/-- **`θ` preserves the block-constant subspace** (both directions). -/
theorem mem_blockConst_fieldReflectionSector {k : ℕ} {x : Sector k} :
    fieldReflectionSector k x ∈ blockConst ↔ x ∈ blockConst := by
  constructor
  · intro h i j hij
    have h' := h (reflectCoord i) (reflectCoord j) ((blockOf_reflectCoord_eq_iff i j).2 hij)
    simpa [fieldReflectionSector_apply, reflectCoord_involutive] using h'
  · intro h i j hij
    have h' := h (reflectCoord i) (reflectCoord j) ((blockOf_reflectCoord_eq_iff i j).2 hij)
    simpa [fieldReflectionSector_apply] using h'

/-- The same preservation for the inverse of `θ` (which acts by the same formula). -/
theorem mem_blockConst_fieldReflectionSector_symm {k : ℕ} {x : Sector k} :
    (fieldReflectionSector k).symm x ∈ blockConst ↔ x ∈ blockConst := by
  rw [fieldReflectionSector_symm_eq]
  exact mem_blockConst_fieldReflectionSector

/-- **`blockConst` is `θ`-stable as a submodule**: `blockConst.map θ = blockConst`. -/
theorem blockConst_map_fieldReflectionSector (k : ℕ) :
    Submodule.map ((fieldReflectionSector k).toLinearEquiv : Sector k →ₗ[ℝ] Sector k) blockConst
      = blockConst := by
  ext x
  constructor
  · rintro ⟨y, hy, rfl⟩
    exact mem_blockConst_fieldReflectionSector.2 hy
  · intro hx
    refine ⟨(fieldReflectionSector k).symm x, ?_, (fieldReflectionSector k).apply_symm_apply x⟩
    exact mem_blockConst_fieldReflectionSector_symm.2 hx

/-! ## `θ Q_k = Q_k θ` -/

/-- **The time reflection commutes with block averaging** — the plan's `θ Q_k = Q_k θ`.

Both sides are the orthogonal projection of `θ x` onto `blockConst`, made explicit with the
characterisation `Submodule.eq_starProjection_of_mem_of_inner_eq_zero`: `θ (Q_k x)` lies in
`blockConst` because `Q_k x` does and `θ` preserves it, and `θ x − θ (Q_k x) = θ (x − Q_k x)` is
orthogonal to `blockConst` because `x − Q_k x` is and `θ` is an isometry preserving `blockConst`
(so `θ⁻¹` maps `blockConst` to itself). -/
theorem starProjection_fieldReflectionSector (k : ℕ) (x : Sector k) :
    blockConst.starProjection (fieldReflectionSector k x)
      = fieldReflectionSector k (blockConst.starProjection x) := by
  have hmem : fieldReflectionSector k (blockConst.starProjection x) ∈ blockConst :=
    mem_blockConst_fieldReflectionSector.mpr (Submodule.starProjection_apply_mem blockConst x)
  refine Submodule.eq_starProjection_of_mem_of_inner_eq_zero (K := blockConst) hmem ?_
  intro w hw
  have hw' : (fieldReflectionSector k).symm w ∈ blockConst :=
    mem_blockConst_fieldReflectionSector_symm.mpr hw
  have horth : ⟪x - blockConst.starProjection x, (fieldReflectionSector k).symm w⟫_ℝ = 0 := by
    rw [real_inner_comm]
    exact (Submodule.sub_starProjection_mem_orthogonal x) _ hw'
  have hdiff : fieldReflectionSector k x - fieldReflectionSector k (blockConst.starProjection x)
      = fieldReflectionSector k (x - blockConst.starProjection x) := by
    rw [map_sub]
  have hwand : w = fieldReflectionSector k ((fieldReflectionSector k).symm w) :=
    ((fieldReflectionSector k).apply_symm_apply w).symm
  rw [hdiff, hwand, LinearIsometryEquiv.inner_map_map]
  exact horth

theorem fieldReflectionSector_blockAveragingOp (k : ℕ) (x : Sector k) :
    fieldReflectionSector k (blockAveragingOp k x) =
      blockAveragingOp k (fieldReflectionSector k x) :=
  (starProjection_fieldReflectionSector k x).symm

/-! ## The total space -/

/-- `θ` on the total space `F_total = ⊕_k ℱ_k`, componentwise. -/
def fieldReflectionTotal (ψ : FTotal) : ∀ k, Sector k :=
  fun k => fieldReflectionSector k (ψ k)

theorem fieldReflectionTotal_memℓp (ψ : FTotal) : Memℓp (fieldReflectionTotal ψ) 2 := by
  refine memℓp_gen ?_
  have hψ : Summable fun k : ℕ => ‖ψ k‖ ^ 2 := by
    simpa using (lp.memℓp ψ).summable (p := 2) (by norm_num)
  simpa [fieldReflectionTotal, LinearIsometryEquiv.norm_map] using hψ

/-- The reflected vector, as an element of the total space. -/
def fieldReflectionFTotalFun (ψ : FTotal) : FTotal :=
  ⟨fieldReflectionTotal ψ, fieldReflectionTotal_memℓp ψ⟩

/-- The reflection is an isometry on the total space: it permutes the coordinates in every
sector, so the `ℓ²` norm of the components is unchanged. -/
theorem norm_fieldReflectionFTotalFun (ψ : FTotal) : ‖fieldReflectionFTotalFun ψ‖ = ‖ψ‖ := by
  rw [lp.norm_eq_tsum_rpow (p := 2) (by norm_num), lp.norm_eq_tsum_rpow (p := 2) (by norm_num)]
  congr 1
  refine tsum_congr fun k => ?_
  simp [fieldReflectionFTotalFun, fieldReflectionTotal]

/-- The time reflection on the multiscale space, as a linear isometry of `FTotal`. -/
def fieldReflectionFTotal : FTotal ≃ₗᵢ[ℝ] FTotal where
  toFun := fieldReflectionFTotalFun
  invFun := fieldReflectionFTotalFun
  map_add' := by
    intro ψ φ
    apply FTotal.ext
    intro k
    simp [fieldReflectionFTotalFun, fieldReflectionTotal, map_add]
  map_smul' := by
    intro c ψ
    apply FTotal.ext
    intro k
    simp [fieldReflectionFTotalFun, fieldReflectionTotal, map_smul]
  left_inv := by
    intro ψ
    apply FTotal.ext
    intro k
    have := (fieldReflectionSector k).symm_apply_apply (ψ k)
    rw [fieldReflectionSector_symm_eq] at this
    simpa [fieldReflectionFTotalFun, fieldReflectionTotal] using this
  right_inv := by
    intro ψ
    apply FTotal.ext
    intro k
    have := (fieldReflectionSector k).apply_symm_apply (ψ k)
    rw [fieldReflectionSector_symm_eq] at this
    simpa [fieldReflectionFTotalFun, fieldReflectionTotal] using this
  norm_map' := norm_fieldReflectionFTotalFun

/-- **`θ` commutes with the RG step on the total space**: `θ (rgOnTotal Q ψ) = rgOnTotal Q (θ ψ)`
whenever every `Q_k` commutes with `θ` — in particular for the block averaging
`Q_k = blockAveragingOp k`, by `fieldReflectionSector_blockAveragingOp`. -/
theorem theta_commutes_rgOnTotal (Q : ∀ k : ℕ, Sector k →L[ℝ] Sector (k + 1))
    (hQθ : ∀ (k : ℕ) (x : Sector k),
      fieldReflectionSector (k + 1) (Q k x) = Q k (fieldReflectionSector k x))
    (hQ : ∀ k, ‖Q k‖ ≤ 1) (ψ : FTotal) :
    fieldReflectionFTotal (rgOnTotal Q hQ ψ) = rgOnTotal Q hQ (fieldReflectionFTotal ψ) := by
  apply FTotal.ext
  intro k
  exact hQθ k (ψ k)

/-- **`θ` commutes with block averaging on the total space** (Phase 3.1 for the Balaban step). -/
theorem theta_commutes_blockAveraging (ψ : FTotal) :
    fieldReflectionFTotal (rgOnTotal blockAveraging blockAveraging_norm_le ψ) =
      rgOnTotal blockAveraging blockAveraging_norm_le (fieldReflectionFTotal ψ) :=
  theta_commutes_rgOnTotal blockAveraging (fun k => fieldReflectionSector_blockAveragingOp k)
    blockAveraging_norm_le ψ

end

end BookProof.ReflectionPositivity
