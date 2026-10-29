import Mathlib
import BookProof.BalabanRG.MultiscaleSpace

/-!
# Block averaging: the contractions `Q_k : ℱ_k → ℱ_{k+1}`

Plan: `cftproof.md`, Phase 2.2 — "Define `Q_k : ℱ_k → ℱ_{k+1}` … The operator `Q_k` is a
projection (averaging) … Show `blockAveragingOp_norm_le`".

## What is proved here

Block averaging is the orthogonal projection of a sector onto its block-constant subspace
`blockConst`: a field configuration is replaced by its block average, and the projection
property makes the average the *best* block-constant approximation (which is exactly why the
map is a contraction, and what makes it insensitive to the choice of internal basis).

* `blockOf` — the partition of the `4 · L⁴` components into the `L⁴` blocks (one block = the
  four components of one lattice cell);
* `blockConst` — the block-constant subspace;
* `blockAveragingOp` — the projection, as a continuous linear map `ℱ_k → ℱ_{k+1}`;
* `blockAveragingOp_norm_le` — **`‖Q_k‖ ≤ 1`** (the plan's estimate);
* `blockAveragingOp_eq_self` — `Q_k` is the identity on block-constant vectors (idempotence:
  averaging twice changes nothing) — the "gauge fixing … returns to the original subspace"
  remark of Phase 2.2, at the level at which it is a genuine statement;
* `blockAveragingOp_mem` — the image is block-constant.

## Boundary

The plan's `Q_k` acts on the Fock space `Γ^s(…)` and implements the *gauge-fixing* step that
restricts to a finite-dimensional block subspace.  Here it acts on the one-particle sector
carrier (see `MultiscaleSpace` for the Fock/colour boundary); the projection is the honest
finite-dimensional shadow of "average over a block and discard the modes the coarse lattice
cannot see".  The Gaussian measure pushing forward under `Q_k` (Phase 1.2's `dγ_k`) is *not*
claimed: it would require the Fock measure machinery, which is absent from Mathlib and from the
corpus.
-/

namespace BookProof.BalabanRG

noncomputable section

/-- The component index of a sector belongs to a block: one block per lattice cell, so the
`4` components `4c, 4c+1, 4c+2, 4c+3` form block `c`. -/
def blockOf (i : Fin latticeDim) : Fin cellsPerBlock :=
  ⟨i.val / nComponents, Nat.div_lt_of_lt_mul (by
    have h : i.val < nComponents * cellsPerBlock := by
      simpa [latticeDim] using i.isLt
    simpa [Nat.mul_comm] using h)⟩

theorem blockOf_apply (i : Fin latticeDim) : (blockOf i).val = i.val / nComponents := rfl

/-- **The block-constant subspace** of a sector: configurations constant across the `4`
components of each cell. -/
def blockConst : Submodule ℝ (Sector 0) where
  carrier := {x | ∀ i j : Fin latticeDim, blockOf i = blockOf j → x i = x j}
  zero_mem' := by
    intro i j _
    rfl
  add_mem' := by
    intro x y hx hy i j hij
    simp [hx i j hij, hy i j hij]
  smul_mem' := by
    intro c x hx i j hij
    simp [hx i j hij]

/-- **Block averaging** (plan Phase 2.2, `blockAveragingOp`): the orthogonal projection of the
scale-`k` sector onto its block-constant subspace, read as a map to the scale-`k+1` sector. -/
def blockAveragingOp (k : ℕ) : Sector k →L[ℝ] Sector (k + 1) :=
  blockConst.starProjection

/-- **`Q_k` is a contraction**: `‖blockAveragingOp k‖ ≤ 1` (plan Phase 2.2
`blockAveragingOp_norm_le`). -/
theorem blockAveragingOp_norm_le (k : ℕ) : ‖blockAveragingOp k‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun x => ?_
  simpa [blockAveragingOp] using blockConst.norm_starProjection_apply_le x

/-- Averaging is idempotent: it fixes the block-constant subspace. -/
theorem blockAveragingOp_eq_self (k : ℕ) {x : Sector k} (hx : x ∈ blockConst) :
    blockAveragingOp k x = x :=
  blockConst.starProjection_eq_self_iff.mpr hx

/-- The image of block averaging is block-constant: one application lands in the coarse
subspace. -/
theorem blockAveragingOp_mem (k : ℕ) (x : Sector k) :
    blockAveragingOp k x ∈ blockConst := by
  simpa [blockAveragingOp] using blockConst.starProjection_mem_subspace x

/-- The family of block-averaging maps, in the shape consumed by `rgOnTotal`. -/
def blockAveraging : ∀ k : ℕ, Sector k →L[ℝ] Sector (k + 1) := fun k => blockAveragingOp k

/-- **The block contractions satisfy the RG hypothesis**, so the total-space step
`rgOnTotal blockAveraging` is well defined and is a contraction. -/
theorem blockAveraging_norm_le : ∀ k : ℕ, ‖blockAveraging k‖ ≤ 1 :=
  blockAveragingOp_norm_le

/-- Averaging at every scale is a contraction on the total space. -/
theorem rgOnTotal_blockAveraging_norm_le : ‖rgOnTotal blockAveraging blockAveraging_norm_le‖ ≤ 1 :=
  norm_rgOnTotal_le blockAveraging blockAveraging_norm_le

end

end BookProof.BalabanRG
