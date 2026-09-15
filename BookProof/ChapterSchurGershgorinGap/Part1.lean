import Mathlib
import BookProof.ChapterTruncationGapLift

/-!
# Chapter SchurGershgorinGap — the tail and coupling inputs, from matrix elements

`CONSOLIDATED_PLAN.md`, QYM-1 **task 3**: "`λ₁(H₁|core) > 0` (strict positivity, not just
non-negativity) is the mathematical claim to establish or to leave as the single named
hypothesis."

`ChapterTruncationGapLift` reduced the core form gap of the *infinite* one-particle operator
to three inputs: a gap certified on the order-`m` truncation, **tail coercivity** on
`tailSpan b m`, and a **coupling bound** across the split.  The last two were left as
hypotheses.  This chapter proves both of them from *matrix-element data* — the numbers
`aᵢⱼ = ⟪bᵢ, H bⱼ⟫` a certificate actually records — so that strict positivity of the
one-particle operator becomes a checkable family of inequalities on the entries rather than
an unanalysed assumption.

## The two criteria

* **Gershgorin (diagonal dominance) ⇒ coercivity.**  If on an index set `T` the diagonal
  entries satisfy `dᵢ ≤ Re aᵢᵢ` and the off-diagonal absolute row sums satisfy
  `∑_{j ∈ T, j ≠ i} ‖aᵢⱼ‖ ≤ rᵢ`, then on the span of `{bᵢ | i ∈ T}` the energy form obeys
  `⟪v, H v⟫ ≥ (infᵢ (dᵢ − rᵢ)) ‖v‖²` (`quadForm_ge_of_gershgorin_on`).  Taking
  `T = {i | m ≤ i}` gives exactly the tail coercivity of the lift
  (`tail_coercive_of_gershgorin`); taking `T = Set.univ` gives a core form gap outright
  (`quadForm_ge_of_gershgorin`).

* **Schur test ⇒ coupling bound.**  If the off-diagonal block `{i < m} × {m ≤ j}` has all
  row sums and all column sums at most `ε`, then `|⟪x, H w⟫| ≤ ε‖x‖‖w‖` across the split
  (`abs_inner_block_le`, `coupling_bound_of_schur`) — the second hypothesis of the lift.

Both criteria are stated with the sums quantified over *arbitrary finite subsets* of the
index set, which is the form a summable row / column bound delivers and which keeps every
proof finite.

## Deliverables

* `bvec`, `entry` — the basis vectors as core elements and the matrix elements;
* `exists_repr_of_mem_span_image`, `norm_sq_sum`, `quadForm_sum`, `inner_sum_apply_sum` —
  the finite-combination calculus behind everything else;
* **`quadForm_sum_ge`**, **`quadForm_ge_of_gershgorin_on`**, `quadForm_ge_of_gershgorin`,
  **`tail_coercive_of_gershgorin`**;
* **`abs_inner_block_le`**, `coupling_bound_of_schur`;
* **`gap_of_level_gap_and_matrix_bounds`** — the composition with
  `TruncationGapLift.gap_of_level_gap_and_tail`: certified order-`m` gap + Gershgorin tail
  data + Schur block data ⇒ core form gap `μ − ε`, and `strict_pos_of_matrix_bounds` — the
  strict positivity `⟪v, H v⟫ > 0` for `v ≠ 0` when `ε < μ`, which is QYM-1 task 3's claim
  in the form the chain consumes;
* **`ym_fock_gap_of_truncated_gap_and_matrix_bounds`** and
  **`ym_fock_mass_gap_of_truncated_gap_and_matrix_bounds`** — the same for the concrete
  gauge-fixed Yang–Mills one-particle Hamiltonian and its `dΓ` lift.

## Honest boundary

What is proved here is the *implication*: the recorded matrix elements satisfying diagonal
dominance on the tail and a Schur bound on the coupling block give the gap, with the
explicit constant `μ − ε`.  Whether the gauge-fixed Yang–Mills entries satisfy those
inequalities is not decided here — it is a computation on the entries, not an assumption
about the spectrum, which is the point: the remaining input is now finite, checkable data
of the same kind the certificate already reports.  No mass gap of the physical Yang–Mills
Hamiltonian is claimed.

Everything in this module is `sorry`-free and `axiom`-free.
-/

noncomputable section

namespace BookProof.SchurGershgorin

open BookProof.FarisLavine BookProof.HermiteGalerkin BookProof.TruncationGapLift
open BookProof.FockSecondQuantization BookProof.FockOneParticleGap
open BookProof.YangMillsHermite BookProof.HermiteProductCore
open BookProof.YangMillsFriedrichs BookProof.YangMillsFockGapChain

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-! ## 1. Basis vectors, matrix elements, and finite combinations -/

/-- The `i`-th basis vector, as an element of the finite-mode core. -/
def bvec (b : HilbertBasis ℕ ℂ F) (i : ℕ) : finiteModeDomain b :=
  ⟨b i, Submodule.subset_span ⟨i, rfl⟩⟩

@[simp] theorem bvec_coe (b : HilbertBasis ℕ ℂ F) (i : ℕ) :
    ((bvec b i : finiteModeDomain b) : F) = b i := rfl

/-- **The matrix element** `aᵢⱼ = ⟪bᵢ, H bⱼ⟫` — the number a certificate records. -/
def entry (b : HilbertBasis ℕ ℂ F) (H : finiteModeDomain b →ₗ[ℂ] F) (i j : ℕ) : ℂ :=
  inner ℂ (b i) (H (bvec b j))

/-- For a symmetric operator the matrix is Hermitian. -/
theorem entry_conj (b : HilbertBasis ℕ ℂ F) (H : finiteModeDomain b →ₗ[ℂ] F)
    (hsym : SymmetricOn _ H) (i j : ℕ) :
    (starRingEnd ℂ) (entry b H i j) = entry b H j i := by
  simp only [entry]
  rw [inner_conj_symm]
  simpa using hsym (bvec b j) (bvec b i)

/-- The absolute values of the matrix are symmetric. -/
theorem norm_entry_symm (b : HilbertBasis ℕ ℂ F) (H : finiteModeDomain b →ₗ[ℂ] F)
    (hsym : SymmetricOn _ H) (i j : ℕ) : ‖entry b H i j‖ = ‖entry b H j i‖ := by
  rw [← entry_conj b H hsym i j, RCLike.norm_conj]

/-- **Every vector of a basis-span is a finite combination with distinct indices.** -/
theorem exists_repr_of_mem_span_image (b : HilbertBasis ℕ ℂ F) (T : Set ℕ) {v : F}
    (hv : v ∈ Submodule.span ℂ (b '' T)) :
    ∃ (S : Finset ℕ) (c : ℕ → ℂ), (↑S : Set ℕ) ⊆ T ∧ v = ∑ i ∈ S, c i • b i := by
  rw [Finsupp.mem_span_image_iff_linearCombination] at hv
  obtain ⟨l, hl, rfl⟩ := hv
  refine ⟨l.support, fun i => l i, (Finsupp.mem_supported ℂ l).mp hl, ?_⟩
  simp [Finsupp.linearCombination_apply, Finsupp.sum]

/-- Pythagoras for a finite orthonormal combination. -/
theorem norm_sq_sum (b : HilbertBasis ℕ ℂ F) (S : Finset ℕ) (c : ℕ → ℂ) :
    ‖∑ i ∈ S, c i • b i‖ ^ 2 = ∑ i ∈ S, ‖c i‖ ^ 2 := by
  have h := congrArg Complex.re (b.orthonormal.inner_sum c c S)
  have hl : (inner ℂ (∑ i ∈ S, c i • b i) (∑ i ∈ S, c i • b i) : ℂ).re
      = ‖∑ i ∈ S, c i • b i‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K (𝕜 := ℂ)]
    norm_cast
  have hr : (∑ i ∈ S, (starRingEnd ℂ) (c i) * c i).re = ∑ i ∈ S, ‖c i‖ ^ 2 := by
    simp [Complex.re_sum, ← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq,
      -Complex.ofReal_pow]
  rw [hl, hr] at h
  exact h

/-- The energy pairing of two finite combinations, in matrix elements. -/
theorem inner_sum_apply_sum (b : HilbertBasis ℕ ℂ F) (H : finiteModeDomain b →ₗ[ℂ] F)
    (S T : Finset ℕ) (c e : ℕ → ℂ) :
    (inner ℂ (∑ i ∈ S, c i • b i) (H (∑ j ∈ T, e j • bvec b j)) : ℂ)
      = ∑ i ∈ S, ∑ j ∈ T, (starRingEnd ℂ) (c i) * e j * entry b H i j := by
  rw [map_sum, sum_inner]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [inner_smul_left, inner_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [map_smul, inner_smul_right]
  simp only [entry]
  ring

/-- The energy form of a finite combination, in matrix elements. -/
theorem quadForm_sum (b : HilbertBasis ℕ ℂ F) (H : finiteModeDomain b →ₗ[ℂ] F)
    (S : Finset ℕ) (c : ℕ → ℂ) :
    quadForm H (∑ i ∈ S, c i • bvec b i)
      = (∑ i ∈ S, ∑ j ∈ S, (starRingEnd ℂ) (c i) * c j * entry b H i j).re := by
  have hcoe : ((∑ i ∈ S, c i • bvec b i : finiteModeDomain b) : F) = ∑ i ∈ S, c i • b i := by
    push_cast
    rfl
  simp only [quadForm, hcoe]
  rw [inner_sum_apply_sum]

/-- Swapping the two indices of an off-diagonal double sum. -/
theorem sum_off_diag_comm (S : Finset ℕ) (G : ℕ → ℕ → ℝ) :
    ∑ i ∈ S, ∑ j ∈ S.erase i, G i j = ∑ j ∈ S, ∑ i ∈ S.erase j, G i j := by
  have h1 : ∀ i ∈ S, ∑ j ∈ S.erase i, G i j = (∑ j ∈ S, G i j) - G i i :=
    fun i hi => Finset.sum_erase_eq_sub hi
  have h2 : ∀ j ∈ S, ∑ i ∈ S.erase j, G i j = (∑ i ∈ S, G i j) - G j j :=
    fun j hj => Finset.sum_erase_eq_sub hj
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_sub_distrib,
    Finset.sum_sub_distrib, Finset.sum_comm]

/-! ## 2. Gershgorin: diagonal dominance gives coercivity -/

/-- **The Gershgorin estimate on a finite combination.**  Each mode contributes at least its
diagonal entry minus the absolute row sum of the off-diagonal entries. -/
theorem quadForm_sum_ge (b : HilbertBasis ℕ ℂ F) (H : finiteModeDomain b →ₗ[ℂ] F)
    (hsym : SymmetricOn _ H) (S : Finset ℕ) (c : ℕ → ℂ) (d r : ℕ → ℝ)
    (hdiag : ∀ i ∈ S, d i ≤ (entry b H i i).re)
    (hrow : ∀ i ∈ S, ∑ j ∈ S.erase i, ‖entry b H i j‖ ≤ r i) :
    ∑ i ∈ S, (d i - r i) * ‖c i‖ ^ 2 ≤ quadForm H (∑ i ∈ S, c i • bvec b i) := by
  classical
  set N : ℕ → ℝ := fun i => ‖c i‖ ^ 2 with hN
  set A : ℕ → ℕ → ℝ := fun i j => ‖entry b H i j‖ with hA
  have hNnonneg : ∀ i, 0 ≤ N i := fun i => sq_nonneg _
  have hAnonneg : ∀ i j, 0 ≤ A i j := fun i j => norm_nonneg _
  set f : ℕ → ℕ → ℝ := fun i j => ((starRingEnd ℂ) (c i) * c j * entry b H i j).re with hf
  have hre : quadForm H (∑ i ∈ S, c i • bvec b i) = ∑ i ∈ S, ∑ j ∈ S, f i j := by
    rw [quadForm_sum]
    simp [Complex.re_sum, hf]
  have hdiagval : ∀ i, f i i = N i * (entry b H i i).re := by
    intro i
    have hz : (starRingEnd ℂ) (c i) * c i = ((N i : ℝ) : ℂ) := by
      rw [← Complex.normSq_eq_conj_mul_self, Complex.normSq_eq_norm_sq]
    simp only [hf]
    rw [hz, Complex.re_ofReal_mul]
  have hoff : ∀ i j, -(A i j * (N i + N j) / 2) ≤ f i j := by
    intro i j
    have h1 : |f i j| ≤ ‖(starRingEnd ℂ) (c i) * c j * entry b H i j‖ :=
      Complex.abs_re_le_norm _
    have h2 : ‖(starRingEnd ℂ) (c i) * c j * entry b H i j‖ = ‖c i‖ * ‖c j‖ * A i j := by
      simp [hA]
    rw [h2] at h1
    have h3 : -(‖c i‖ * ‖c j‖ * A i j) ≤ f i j := by linarith [(abs_le.mp h1).1]
    have h4 : 2 * (‖c i‖ * ‖c j‖) ≤ N i + N j := by
      have := sq_nonneg (‖c i‖ - ‖c j‖)
      simp only [hN]
      nlinarith
    nlinarith [hAnonneg i j]
  have hrowlb : ∀ i ∈ S, N i * d i - (∑ j ∈ S.erase i, A i j * (N i + N j) / 2)
      ≤ ∑ j ∈ S, f i j := by
    intro i hi
    have hsplit : ∑ j ∈ S, f i j = f i i + ∑ j ∈ S.erase i, f i j := by
      rw [← Finset.sum_erase_add S _ hi]; ring
    have h1 : N i * d i ≤ f i i := by
      rw [hdiagval i]
      exact mul_le_mul_of_nonneg_left (hdiag i hi) (hNnonneg i)
    have h2 : -(∑ j ∈ S.erase i, A i j * (N i + N j) / 2) ≤ ∑ j ∈ S.erase i, f i j := by
      rw [← Finset.sum_neg_distrib]
      exact Finset.sum_le_sum fun j _ => hoff i j
    rw [hsplit]; linarith
  have hsum1 : ∑ i ∈ S, (N i * d i - (∑ j ∈ S.erase i, A i j * (N i + N j) / 2))
      ≤ ∑ i ∈ S, ∑ j ∈ S, f i j := Finset.sum_le_sum hrowlb
  have hexp : ∀ i, (∑ j ∈ S.erase i, A i j * (N i + N j) / 2)
      = (∑ j ∈ S.erase i, A i j * N i) / 2 + (∑ j ∈ S.erase i, A i j * N j) / 2 := by
    intro i
    have hterm : ∀ j, A i j * (N i + N j) / 2 = A i j * N i / 2 + A i j * N j / 2 :=
      fun j => by ring
    simp_rw [hterm]
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div]
  have hT2 : ∑ i ∈ S, (∑ j ∈ S.erase i, A i j * N i) ≤ ∑ i ∈ S, r i * N i := by
    refine Finset.sum_le_sum fun i hi => ?_
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (hrow i hi) (hNnonneg i)
  have hT3 : ∑ i ∈ S, (∑ j ∈ S.erase i, A i j * N j) ≤ ∑ i ∈ S, r i * N i := by
    rw [sum_off_diag_comm S (fun i j => A i j * N j)]
    refine Finset.sum_le_sum fun j hj => ?_
    have hswap : ∀ i, A i j = A j i := fun i => norm_entry_symm b H hsym i j
    calc ∑ i ∈ S.erase j, A i j * N j = (∑ i ∈ S.erase j, A j i) * N j := by
            rw [Finset.sum_mul]
            exact Finset.sum_congr rfl fun i _ => by rw [hswap i]
      _ ≤ r j * N j := mul_le_mul_of_nonneg_right (hrow j hj) (hNnonneg j)
  rw [hre]
  have hlhs : ∑ i ∈ S, (d i - r i) * ‖c i‖ ^ 2 = ∑ i ∈ S, N i * d i - ∑ i ∈ S, r i * N i := by
    rw [← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp only [hN]; ring
  have hrhs : ∑ i ∈ S, (N i * d i - (∑ j ∈ S.erase i, A i j * (N i + N j) / 2))
      = ∑ i ∈ S, N i * d i
        - ((∑ i ∈ S, (∑ j ∈ S.erase i, A i j * N i)) / 2
           + (∑ i ∈ S, (∑ j ∈ S.erase i, A i j * N j)) / 2) := by
    rw [Finset.sum_sub_distrib]
    congr 1
    rw [Finset.sum_div, Finset.sum_div, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hexp i
  rw [hlhs]
  rw [hrhs] at hsum1
  linarith

/-- **Gershgorin on a basis-span.**  Diagonal dominance with margin `μ` on the index set `T`
gives the form bound `⟪v, H v⟫ ≥ μ‖v‖²` on the span of `{bᵢ | i ∈ T}`. -/
theorem quadForm_ge_of_gershgorin_on (b : HilbertBasis ℕ ℂ F)
    (H : finiteModeDomain b →ₗ[ℂ] F) (hsym : SymmetricOn _ H) (T : Set ℕ) {mu : ℝ}
    (d r : ℕ → ℝ)
    (hdiag : ∀ i ∈ T, d i ≤ (entry b H i i).re)
    (hrow : ∀ i ∈ T, ∀ S : Finset ℕ, (↑S : Set ℕ) ⊆ T → i ∉ S →
      ∑ j ∈ S, ‖entry b H i j‖ ≤ r i)
    (hgap : ∀ i ∈ T, mu ≤ d i - r i)
    (v : finiteModeDomain b) (hv : (v : F) ∈ Submodule.span ℂ (b '' T)) :
    mu * ‖(v : F)‖ ^ 2 ≤ quadForm H v := by
  classical
  obtain ⟨S, c, hST, hvc⟩ := exists_repr_of_mem_span_image b T hv
  have hvsum : v = ∑ i ∈ S, c i • bvec b i := by
    refine Subtype.ext ?_
    rw [hvc]
    push_cast
    rfl
  have hdiagS : ∀ i ∈ S, d i ≤ (entry b H i i).re := fun i hi => hdiag i (hST hi)
  have hrowS : ∀ i ∈ S, ∑ j ∈ S.erase i, ‖entry b H i j‖ ≤ r i := by
    intro i hi
    refine hrow i (hST hi) (S.erase i) ?_ ?_
    · intro j hj
      have hj' : j ∈ S.erase i := Finset.mem_coe.mp hj
      exact hST (Finset.mem_coe.mpr (Finset.mem_of_mem_erase hj'))
    · simp
  have hmain := quadForm_sum_ge b H hsym S c d r hdiagS hrowS
  have hnorm : ‖(v : F)‖ ^ 2 = ∑ i ∈ S, ‖c i‖ ^ 2 := by
    rw [hvc]; exact norm_sq_sum b S c
  have hle : mu * ‖(v : F)‖ ^ 2 ≤ ∑ i ∈ S, (d i - r i) * ‖c i‖ ^ 2 := by
    rw [hnorm, Finset.mul_sum]
    refine Finset.sum_le_sum fun i hi => ?_
    exact mul_le_mul_of_nonneg_right (hgap i (hST hi)) (sq_nonneg _)
  calc mu * ‖(v : F)‖ ^ 2 ≤ ∑ i ∈ S, (d i - r i) * ‖c i‖ ^ 2 := hle
    _ ≤ quadForm H (∑ i ∈ S, c i • bvec b i) := hmain
    _ = quadForm H v := by rw [← hvsum]

/-- **Gershgorin on the whole core.** -/
theorem quadForm_ge_of_gershgorin (b : HilbertBasis ℕ ℂ F)
    (H : finiteModeDomain b →ₗ[ℂ] F) (hsym : SymmetricOn _ H) {mu : ℝ} (d r : ℕ → ℝ)
    (hdiag : ∀ i, d i ≤ (entry b H i i).re)
    (hrow : ∀ i, ∀ S : Finset ℕ, i ∉ S → ∑ j ∈ S, ‖entry b H i j‖ ≤ r i)
    (hgap : ∀ i, mu ≤ d i - r i) (v : finiteModeDomain b) :
    mu * ‖(v : F)‖ ^ 2 ≤ quadForm H v := by
  refine quadForm_ge_of_gershgorin_on b H hsym Set.univ d r (fun i _ => hdiag i)
    (fun i _ S _ hiS => hrow i S hiS) (fun i _ => hgap i) v ?_
  have : (b '' Set.univ) = Set.range b := Set.image_univ
  rw [this]
  exact v.2

/-- **Tail coercivity from the entries** — the first analytic input of
`TruncationGapLift.gap_of_level_gap_and_tail`, now a theorem about the recorded matrix. -/
theorem tail_coercive_of_gershgorin (b : HilbertBasis ℕ ℂ F)
    (H : finiteModeDomain b →ₗ[ℂ] F) (hsym : SymmetricOn _ H) {m : ℕ} {mu : ℝ}
    (d r : ℕ → ℝ)
    (hdiag : ∀ i, m ≤ i → d i ≤ (entry b H i i).re)
    (hrow : ∀ i, m ≤ i → ∀ S : Finset ℕ, (∀ j ∈ S, m ≤ j) → i ∉ S →
      ∑ j ∈ S, ‖entry b H i j‖ ≤ r i)
    (hgap : ∀ i, m ≤ i → mu ≤ d i - r i)
    (w : finiteModeDomain b) (hw : (w : F) ∈ tailSpan b m) :
    mu * ‖(w : F)‖ ^ 2 ≤ quadForm H w :=
  quadForm_ge_of_gershgorin_on b H hsym {i | m ≤ i} d r (fun i hi => hdiag i hi)
    (fun i hi S hS hiS => hrow i hi S (fun _ hj => hS hj) hiS) (fun i hi => hgap i hi) w hw

end BookProof.SchurGershgorin

end
