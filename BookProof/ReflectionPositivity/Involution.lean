import Mathlib
import BookProof.EuclideanFock4D.MehlerMeasure
import BookProof.BalabanRG.BlockOperator

/-!
# Time reflection `θ`

Plan: `cftproof.md`, Phase 3.1 — "Define the time reflection `θ(x₀, x⃗) = (−x₀, x⃗)`. Check
`θ² = 1`, `θ` preserves the measure: `θ * dγ = dγ`, `θ` commutes with `Q_k`".

## What is proved here

* `timeReflection` — `θ` on `ℝ⁴`, built as a `LinearIsometryEquiv` by negating the time
  coordinate (`LinearIsometryEquiv.piLpCongrRight`), hence automatically an isometry;
* `timeReflection_apply_zero`, `timeReflection_apply_succ` — the coordinate formula
  `θ(x₀,x⃗) = (−x₀, x⃗)`;
* `timeReflection_involutive` — `θ² = 1`;
* `timeReflection_measure_invariant` — **`θ` preserves the Mehler measure `dγ₀`**.  This is a
  real theorem, Phase 1.2's `O(4)` invariance applied to `θ ∈ O(4)`;
* the lattice side: `flipCell`, `reflectCoord` — the involution of the block lattice that
  exchanges the two time halves; `fieldReflection` — `θ` on a field configuration
  `Fin latticeDim → ℝ`, a coordinate permutation, with `fieldReflection_involutive`.

## `θ Q_k = Q_k θ`

`θ`'s commutation with `Q_k` is proved in `ReflectionPositivity.BlockCommute`:
`fieldReflectionSector_blockAveragingOp` (per sector) and `theta_commutes_blockAveraging` (on
`F_total`).  It needs the block structure to be `θ`-stable, which is why `blockOf` is the *cell*
of a component index (`BalabanRG.MultiscaleSpace.coordOf`) rather than a run of consecutive
indices: `reflectCoord` keeps `μ` and reflects the cell, so it maps blocks to blocks
(`BlockCommute.blockOf_reflectCoord`).  `ReflectionPositivity.Proof` no longer carries it as a
hypothesis.
-/

namespace BookProof.ReflectionPositivity

open BookProof.EuclideanFock4D BookProof.BalabanRG MeasureTheory

noncomputable section

/-! ## `θ` on spacetime `ℝ⁴` -/

/-- **Time reflection** `θ(x₀, x⃗) = (−x₀, x⃗)` on `ℝ⁴`, as a linear isometry. -/
def timeReflection : Spacetime4D ≃ₗᵢ[ℝ] Spacetime4D :=
  LinearIsometryEquiv.piLpCongrRight (p := 2) fun i : Fin 4 =>
    if i = 0 then LinearIsometryEquiv.neg ℝ else LinearIsometryEquiv.refl ℝ ℝ

/-- The time coordinate changes sign. -/
theorem timeReflection_apply_zero (x : Spacetime4D) : timeReflection x 0 = -x 0 := by
  rw [timeReflection, LinearIsometryEquiv.piLpCongrRight_apply]
  simp

/-- The spatial coordinates are fixed. -/
theorem timeReflection_apply_of_ne_zero (x : Spacetime4D) {i : Fin 4} (hi : i ≠ 0) :
    timeReflection x i = x i := by
  rw [timeReflection, LinearIsometryEquiv.piLpCongrRight_apply]
  simp [hi]

/-- `θ² = 1`. -/
theorem timeReflection_involutive (x : Spacetime4D) : timeReflection (timeReflection x) = x := by
  refine PiLp.ext fun i => ?_
  by_cases hi : i = 0
  · subst hi
    rw [timeReflection_apply_zero (timeReflection x), timeReflection_apply_zero x, neg_neg]
  · rw [timeReflection_apply_of_ne_zero (timeReflection x) hi,
      timeReflection_apply_of_ne_zero x hi]

/-- `θ` is measurable. -/
theorem timeReflection_measurable : Measurable timeReflection :=
  timeReflection.continuous.measurable

/-- **`θ` preserves the Mehler measure**: `θ * dγ₀ = dγ₀` (plan Phase 3.1). -/
theorem timeReflection_measure_invariant :
    Measure.map timeReflection mehlerMeasure4D = mehlerMeasure4D :=
  mehler4D_O4_invariant timeReflection

/-! ## `θ` on the block lattice -/

/-- The number of cells in one time half of the block. -/
def halfCells : ℕ := cellsPerBlock / 2

/-- Is the cell of this component in the positive-time half (`x₀ > 0`)? -/
def isPosTime (i : Fin latticeDim) : Prop := (coordOf i).2.val < halfCells

instance instDecidableIsPosTime (i : Fin latticeDim) : Decidable (isPosTime i) := by
  unfold isPosTime
  infer_instance

/-- **The cell reflection**: `c ↦ c + 8 (mod 16)`.  This exchanges the two time halves. -/
def flipCell (c : Fin cellsPerBlock) : Fin cellsPerBlock :=
  ⟨(c.val + halfCells) % cellsPerBlock, Nat.mod_lt _ (by
    have : 0 < cellsPerBlock := by decide
    exact this)⟩

theorem flipCell_val (c : Fin cellsPerBlock) :
    (flipCell c).val = (c.val + halfCells) % cellsPerBlock := rfl

/-- The cell reflection is an involution. -/
theorem flipCell_involutive (c : Fin cellsPerBlock) : flipCell (flipCell c) = c := by
  have h16 : cellsPerBlock = 16 := by decide
  have h8 : halfCells = 8 := by decide
  apply Fin.ext
  simp only [flipCell_val, h16, h8]
  omega

/-- The cell reflection exchanges the time halves. -/
theorem flipCell_pos_iff (c : Fin cellsPerBlock) :
    (flipCell c).val < halfCells ↔ halfCells ≤ c.val := by
  have h16 : cellsPerBlock = 16 := by decide
  have h8 : halfCells = 8 := by decide
  have hc : c.val < 16 := by omega
  simp only [flipCell_val, h16, h8]
  omega

/-- The reflected component index: same `μ`, reflected cell. -/
def reflectCoord (i : Fin latticeDim) : Fin latticeDim :=
  coordIdx ((coordOf i).1, flipCell (coordOf i).2)

/-- The reflection of component indices is an involution. -/
theorem reflectCoord_involutive (i : Fin latticeDim) : reflectCoord (reflectCoord i) = i := by
  unfold reflectCoord
  rw [coordOf_coordIdx, flipCell_involutive, coordIdx_coordOf]

/-- The field configurations of a sector, as plain functions on the component index. -/
abbrev Config : Type := Fin latticeDim → ℝ

/-- **`θ` on field configurations**: values are moved to the reflected component. -/
def fieldReflection : Config ≃ₗ[ℝ] Config where
  toFun x := fun i => x (reflectCoord i)
  invFun x := fun i => x (reflectCoord i)
  map_add' := by
    intro x y
    rfl
  map_smul' := by
    intro c x
    rfl
  left_inv := by
    intro x
    funext i
    simp only [reflectCoord_involutive]
  right_inv := by
    intro x
    funext i
    simp only [reflectCoord_involutive]

/-- `θ` on configurations is an involution. -/
theorem fieldReflection_involutive (x : Config) : fieldReflection (fieldReflection x) = x :=
  fieldReflection.right_inv x

end

end BookProof.ReflectionPositivity
