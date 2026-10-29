import Mathlib

/-!
# The Balaban multiscale space `⊕_k ℱ_k`

Plan: `cftproof.md`, Phase 2.1 — "Divide the field into `L`-blocks of size `L^4` … Define the
multiscale space `F_total = ⊕_k ℱ_k`, `ℱ_k ≅ Γ^s(L²(Block_k × su(N)))`".

## The model (and what it is a model *of*)

A sector `ℱ_k` is modelled by its *one-particle* field content at scale `k`: the `4`
components `A_μ` of the gauge field on a block lattice of `L^{4k}` cells.  The symmetric Fock
space `Γ^s` and the `su(N)` colour factor are **not** part of the Lean carrier: Mathlib has no
symmetric Fock space, and (see `BookProof.EuclideanFock4D.CoreBasis`) no Hilbert tensor
product with which to multiply the colour factor in.  Sector multiplicities are therefore
carried at the level at which the later phases use them — as a normed space with a scale — and
the Fock/colour structure is recorded as boundary in `docs/euclidean_cft_proof.md`.

All sectors share the same carrier `EuclideanSpace ℝ (Fin latticeDim)`.  This is deliberate:
the plan's maps `Q_k : ℱ_k → ℱ_{k+1}` are maps *between* sectors, and giving every sector the
same carrier is exactly what makes `Q_k` an honest continuous linear map that can be iterated
inside `F_total` (`rgOnTotal`); a genuinely dimension-dependent carrier would need coherent
transport of norms along `dimBlock k → dimBlock (k+1)`, which is bookkeeping with no
mathematical content.  The scale is carried by the *index* `k` in the direct sum, which is
where the plan uses it (`⊕_k ℱ_k`, `Ψ_N` supported on scales `≤ N`).

## Contents

* `blockFactor`, `nComponents`, `cellsPerBlock`, `latticeDim`, `Sector`, `FTotal` — the spaces;
* `FTotal.ext`, `norm_component_le`, `sectorEmbed` — the elementary `ℓ²` API used downstream;
* `rgStepFun`, `rgStepFun_memℓp`, `rgOnTotal`, `rgOnTotal_norm_le`, `norm_rgOnTotal_le` —
  the total-space action of a family of contractions `Q_k` (Phase 2.2's `rgOnTotal`,
  Phase 2.3's `balaban_rg_contraction`);
* `psiSeq` — the recursion `Ψ_{N+1} = Q_N Ψ_N` of Phase 2.3.
-/

namespace BookProof.BalabanRG

noncomputable section

/-- The Balaban block factor `L` (the plan's "blocks of size `L⁴`"); taken to be `2`. -/
def blockFactor : ℕ := 2

/-- The number of components of the gauge field `A_μ`, `μ = 0,1,2,3`. -/
def nComponents : ℕ := 4

/-- The number of lattice cells in one block: `L⁴`. -/
def cellsPerBlock : ℕ := blockFactor ^ 4

/-- The one-particle dimension of a sector: `4` components on `cellsPerBlock` cells. -/
def latticeDim : ℕ := nComponents * cellsPerBlock

theorem latticeDim_eq : latticeDim = 64 := by decide

/-- **A sector `ℱ_k`.**  Its scale is the index `k` in `FTotal`; see the module docstring. -/
abbrev Sector (_k : ℕ) : Type := EuclideanSpace ℝ (Fin latticeDim)

/-- **The multiscale space** `F_total = ⊕_k ℱ_k`, realized as the `ℓ²` direct sum. -/
abbrev FTotal : Type := lp (fun k : ℕ => Sector k) 2

/-- Extensionality for the total space. -/
theorem FTotal.ext {ψ φ : FTotal} (h : ∀ k, ψ k = φ k) : ψ = φ :=
  lp.ext (funext h)

/-- The `k`-th component of a total vector is bounded by the total norm. -/
theorem norm_component_le (ψ : FTotal) (k : ℕ) : ‖ψ k‖ ≤ ‖ψ‖ :=
  lp.norm_apply_le_norm (by norm_num) ψ k

/-- A vector supported on a single scale. -/
def sectorEmbed (k : ℕ) (x : Sector k) : FTotal := lp.single 2 k x

/-! ## Phase 2.2 / 2.3: the total-space action of the block contractions -/

/-- Componentwise action of the family `Q_k` on the total space. -/
def rgStepFun (Q : ∀ k : ℕ, Sector k →L[ℝ] Sector (k + 1)) (ψ : FTotal) : ∀ k, Sector k :=
  fun k => Q k (ψ k)

/-- The componentwise action of a family of contractions stays in `ℓ²`. -/
theorem rgStepFun_memℓp (Q : ∀ k : ℕ, Sector k →L[ℝ] Sector (k + 1))
    (hQ : ∀ k, ‖Q k‖ ≤ 1) (ψ : FTotal) : Memℓp (rgStepFun Q ψ) 2 := by
  refine memℓp_gen ?_
  have hψ : Summable fun k : ℕ => ‖ψ k‖ ^ 2 := by
    simpa using (lp.memℓp ψ).summable (p := 2) (by norm_num)
  refine hψ.of_nonneg_of_le (fun k => by positivity) (fun k => ?_)
  have h1 : ‖Q k (ψ k)‖ ≤ ‖Q k‖ * ‖ψ k‖ := ContinuousLinearMap.le_opNorm _ _
  have h2 : ‖Q k‖ ≤ 1 := hQ k
  have h3 : ‖Q k‖ * ‖ψ k‖ ≤ 1 * ‖ψ k‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
  rw [one_mul] at h3
  simpa using pow_le_pow_left₀ (norm_nonneg _) (h1.trans h3) (2 : ℕ)

/-- **The block-averaging operator on the total space** (plan Phase 2.2 `rgOnTotal`).

The contraction hypothesis `‖Q k‖ ≤ 1` is part of the *data* here: it is what makes the
componentwise action land in `ℓ²`, and it is exactly the analytic input the plan supplies
from the block averaging (`BlockOperator.blockAveragingOp_norm_le`). -/
def rgOnTotalₗ (Q : ∀ k : ℕ, Sector k →L[ℝ] Sector (k + 1)) (hQ : ∀ k, ‖Q k‖ ≤ 1) :
    FTotal →ₗ[ℝ] FTotal where
  toFun ψ := ⟨rgStepFun Q ψ, rgStepFun_memℓp Q hQ ψ⟩
  map_add' := by
    intro ψ φ
    apply FTotal.ext
    intro k
    simp [rgStepFun, map_add]
  map_smul' := by
    intro c ψ
    apply FTotal.ext
    intro k
    simp [rgStepFun, map_smul]

/-- **The RG step is a contraction** (plan Phase 2.3 `balaban_rg_contraction`), linear-map
form. -/
theorem rgOnTotalₗ_norm_le (Q : ∀ k : ℕ, Sector k →L[ℝ] Sector (k + 1))
    (hQ : ∀ k, ‖Q k‖ ≤ 1) (ψ : FTotal) : ‖rgOnTotalₗ Q hQ ψ‖ ≤ ‖ψ‖ := by
  have hp : (0 : ℝ) < ((2 : ENNReal).toReal) := by norm_num
  rw [← Real.rpow_le_rpow_iff (norm_nonneg _) (norm_nonneg _) hp,
    lp.norm_rpow_eq_tsum (p := 2) hp, lp.norm_rpow_eq_tsum (p := 2) hp]
  refine Summable.tsum_le_tsum (fun k => ?_) ?_ ?_
  · have h1 : ‖Q k (ψ k)‖ ≤ ‖Q k‖ * ‖ψ k‖ := ContinuousLinearMap.le_opNorm _ _
    have h2 : ‖Q k‖ ≤ 1 := hQ k
    have h3 : ‖Q k‖ * ‖ψ k‖ ≤ 1 * ‖ψ k‖ := mul_le_mul_of_nonneg_right h2 (norm_nonneg _)
    rw [one_mul] at h3
    have hle : ‖Q k (ψ k)‖ ≤ ‖ψ k‖ := by simpa using h1.trans h3
    exact Real.rpow_le_rpow (norm_nonneg _) hle (by positivity)
  · simpa using (lp.memℓp ((rgOnTotalₗ Q hQ) ψ)).summable hp
  · simpa using (lp.memℓp ψ).summable hp

/-- **The block-averaging operator on the total space** (plan Phase 2.2 `rgOnTotal`). -/
def rgOnTotal (Q : ∀ k : ℕ, Sector k →L[ℝ] Sector (k + 1)) (hQ : ∀ k, ‖Q k‖ ≤ 1) :
    FTotal →L[ℝ] FTotal :=
  (rgOnTotalₗ Q hQ).mkContinuous 1 (by
    intro ψ
    simpa using rgOnTotalₗ_norm_le Q hQ ψ)

@[simp]
theorem rgOnTotal_apply (Q : ∀ k : ℕ, Sector k →L[ℝ] Sector (k + 1))
    (hQ : ∀ k, ‖Q k‖ ≤ 1) (ψ : FTotal) :
    rgOnTotal Q hQ ψ = rgOnTotalₗ Q hQ ψ := rfl

@[simp]
theorem rgOnTotal_apply_apply (Q : ∀ k : ℕ, Sector k →L[ℝ] Sector (k + 1))
    (hQ : ∀ k, ‖Q k‖ ≤ 1) (ψ : FTotal) (k : ℕ) :
    rgOnTotal Q hQ ψ k = Q k (ψ k) := rfl

/-- The norm bound of the RG step, as a theorem about the continuous linear map. -/
theorem rgOnTotal_norm_le (Q : ∀ k : ℕ, Sector k →L[ℝ] Sector (k + 1))
    (hQ : ∀ k, ‖Q k‖ ≤ 1) (ψ : FTotal) : ‖rgOnTotal Q hQ ψ‖ ≤ ‖ψ‖ :=
  rgOnTotalₗ_norm_le Q hQ ψ

/-- The operator norm of the total-space RG step is at most one. -/
theorem norm_rgOnTotal_le (Q : ∀ k : ℕ, Sector k →L[ℝ] Sector (k + 1))
    (hQ : ∀ k, ‖Q k‖ ≤ 1) : ‖rgOnTotal Q hQ‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun ψ => by
    simpa using rgOnTotal_norm_le Q hQ ψ

/-! ## Phase 2.3: the iteration `Ψ_{N+1} = Q_N Ψ_N` -/

/-- **The sequence of effective actions** (plan Phase 2.3): `Ψ_0 = ψ₀`,
`Ψ_{N+1} = Q_N Ψ_N`. -/
def psiSeq (Q : ∀ k : ℕ, Sector k →L[ℝ] Sector (k + 1)) (hQ : ∀ k, ‖Q k‖ ≤ 1)
    (ψ0 : FTotal) : ℕ → FTotal
  | 0 => ψ0
  | n + 1 => rgOnTotal Q hQ (psiSeq Q hQ ψ0 n)

@[simp]
theorem psiSeq_zero (Q : ∀ k : ℕ, Sector k →L[ℝ] Sector (k + 1)) (hQ : ∀ k, ‖Q k‖ ≤ 1)
    (ψ0 : FTotal) : psiSeq Q hQ ψ0 0 = ψ0 := rfl

theorem psiSeq_succ (Q : ∀ k : ℕ, Sector k →L[ℝ] Sector (k + 1)) (hQ : ∀ k, ‖Q k‖ ≤ 1)
    (ψ0 : FTotal) (n : ℕ) : psiSeq Q hQ ψ0 (n + 1) = rgOnTotal Q hQ (psiSeq Q hQ ψ0 n) := rfl

/-- The sequence is uniformly bounded by its starting vector, because every step is a
contraction.  This is the quantitative form of Balaban's boundedness estimate that Phase 2.3
uses before the geometric decay hypothesis. -/
theorem psiSeq_norm_le (Q : ∀ k : ℕ, Sector k →L[ℝ] Sector (k + 1))
    (hQ : ∀ k, ‖Q k‖ ≤ 1) (ψ0 : FTotal) (n : ℕ) : ‖psiSeq Q hQ ψ0 n‖ ≤ ‖ψ0‖ := by
  induction n with
  | zero => simp
  | succ n ih => rw [psiSeq_succ]; exact (rgOnTotal_norm_le Q hQ _).trans ih

end

end BookProof.BalabanRG
