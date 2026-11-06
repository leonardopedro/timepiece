import Mathlib
import BookProof.YangMillsLadderOperator

/-!
# The magnetic ladder on `ℓ²(Idx d)`: the operator identity without a cut-off

`YangMillsLadderOperator.magCutoffOp_eq_sum_cre` proves `magCutoffOp Λ A = ∑ᵢ Aᵢ • creOp Λ i` on the
truncated space `Box d Λ → ℂ`, where every sum is finite because `Box d Λ` is a finite type.
`YangMillsLadderTransport.magCutoffKernel_eq_ladder` is the entrywise version on the unbounded
index `Idx d`, but still for the *cut-off* kernel and the *cut-off* box.

This module removes the cut-off from the operator statement.  On the algebraic core
`CoreCoeff d = (Idx d →₀ ℂ)` of `ℓ²(Idx d)` — the dense subspace `coreEmbed` of
`YangMillsFormClosure` — the creation ladder is an honest endomorphism

`creCore i c = ∑_{α ∈ supp c} c α • single (update α i (αᵢ + 1)) (√(αᵢ + 1))`,

and `magCore A := ∑ᵢ Aᵢ • creCore i` satisfies, for every occupation function `β : Idx d`,

`(magCore A (single α x)) β = ∑ᵢ Aᵢ · creCoeff i β α · x`   (`magCore_single_apply`),

which is `magCutoffOp_eq_sum_cre` with `Box d Λ` replaced by `Idx d` and no `Λ` at all: the matrix
of `magCore A` in the occupation basis *is* the transported ladder of
`YangMillsLadderTransport.creCoeff`.  Its support sits in degree `occDeg α + 1`, so the operator is
unbounded on `ℓ²(Idx d)` — it raises the degree, and each raised vector has norm
`‖x‖ · |Aᵢ| · √(αᵢ + 1)`, which grows with the occupation numbers rather than decaying.

## Boundary

The identity is proved on the core, not on the whole of `ℓ²(Idx d)`: `magCore A` does not preserve
`ℓ²`, because raising a coordinate multiplies the norm by `√(αᵢ + 1)` without bound.  What the
Hilbert–Schmidt and relative-bound results of `YangMillsFormClosureNonDiagonal` §10–11 supply is
the *form* estimate, and that is where this identity has to be consumed: the quadratic form of
`magCore` on a core vector is the kernel form of the zero-extended `boxKernel`
(`closedKernelForm_coreEmbed`), and `closed_farisLavine_boxKernel` /
`ladder_closed_domination_sharp` bound it by the degree form with a relative constant below `1`.
  Turning that form bound into a
closed (or self-adjoint) operator on `ℓ²(Idx d)`, and identifying it with the magnetic part of the
reduced Hamiltonian of §24, is not formalized here.  It also cannot be done for `magCore` itself:
the bare ladder is not symmetric (`magKernel_asymm`), so there is no self-adjoint operator agreeing
with it on the core.  The symmetric object is `magSymKernel`, the ladder plus its transpose; that
is the kernel whose form `closedKernelForm` sees, and pushing the domination through it is what a
self-adjoint realization would have to consume.
-/

namespace BookProof.YangMillsFormClosureND

open BookProof.HermiteBand BookProof.HermiteProductBasis
open BookProof.YangMillsFormClosure BookProof.ReferenceGap

noncomputable section

variable {d : ℕ}

/-! ## The ladder on the core -/

/-- **The creation ladder `a†ᵢ` on the core of `ℓ²(Idx d)`.**  It raises the occupation number in
direction `i` by one and multiplies the coefficient by `√(αᵢ + 1)`; since the coefficient family is
finitely supported, so is the image. -/
def creCore (i : Fin d) (c : CoreCoeff d) : CoreCoeff d :=
  c.sum fun α x =>
    Finsupp.single (Function.update α i (α i + 1)) (x * ((Real.sqrt ((α i : ℝ) + 1) : ℝ) : ℂ))

/-- The ladder on a basis vector: one term, raised once. -/
theorem creCore_single (i : Fin d) (α : Idx d) (x : ℂ) :
    creCore i (Finsupp.single α x)
      = Finsupp.single (Function.update α i (α i + 1))
          (x * ((Real.sqrt ((α i : ℝ) + 1) : ℝ) : ℂ)) := by
  classical
  rw [creCore, Finsupp.sum_single_index (by simp)]

/-- **The magnetic ladder operator on the core**, `∑ᵢ Aᵢ a†ᵢ` — the cut-off-free analogue of
`magCutoffOp`, with no finite box anywhere in its definition. -/
def magCore (A : Fin d → ℝ) (c : CoreCoeff d) : CoreCoeff d :=
  ∑ i, (A i : ℂ) • creCore i c

/-- **The operator identity, in the form of a restatement**: `magCore` is the sum of the ladders,
exactly as `magCutoffOp_eq_sum_cre` says on the box. -/
theorem magCore_eq_sum_cre (A : Fin d → ℝ) (c : CoreCoeff d) :
    magCore A c = ∑ i, (A i : ℂ) • creCore i c :=
  rfl

/-- The ladder computed on a basis vector, as an explicit finite sum over the directions. -/
theorem magCore_single (A : Fin d → ℝ) (α : Idx d) (x : ℂ) :
    magCore A (Finsupp.single α x)
      = ∑ i, Finsupp.single (Function.update α i (α i + 1))
          (x * (A i : ℂ) * ((Real.sqrt ((α i : ℝ) + 1) : ℝ) : ℂ)) := by
  classical
  rw [magCore]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [creCore_single, Finsupp.smul_single]
  congr 1
  simp only [smul_eq_mul]
  ring

/-- **The matrix elements of the magnetic ladder on `Idx d`.**  For every occupation function `β`,
the coefficient of `β` in `magCore A (single α x)` is `∑ᵢ Aᵢ · creCoeff i β α · x`: the sum of the
transported ladder's matrix elements, with the cut-off box and the parameter `Λ` gone. -/
theorem magCore_single_apply (A : Fin d → ℝ) (α : Idx d) (x : ℂ) (β : Idx d) :
    (magCore A (Finsupp.single α x)) β
      = ∑ i, (A i : ℂ) * creCoeff i β α * x := by
  classical
  rw [magCore_single]
  simp only [Finsupp.finset_sum_apply, Finsupp.single_apply, creCoeff]
  refine Finset.sum_congr rfl fun i _ => ?_
  by_cases h : β = Function.update α i (α i + 1)
  · subst h
    simp [mul_assoc, mul_comm]
  · have h' : Function.update α i (α i + 1) ≠ β := fun hc => h hc.symm
    simp [h, h']

/-! ## The degree grading: the ladder is unbounded -/

/-- Raising one coordinate raises the total occupation number by one. -/
theorem occDeg_update_raise (α : Idx d) (i : Fin d) :
    occDeg (Function.update α i (α i + 1)) = occDeg α + 1 := by
  simpa using occDeg_update_self α i

/-- **The ladder raises the degree**: every coefficient of `magCore A (single α x)` sits in total
occupation number `occDeg α + 1`, so the operator is not bounded on `ℓ²(Idx d)` and its degree is
exactly one above the input's. -/
theorem magCore_support_occDeg {A : Fin d → ℝ} {α : Idx d} {x : ℂ} {β : Idx d}
    (hβ : β ∈ (magCore A (Finsupp.single α x)).support) : occDeg β = occDeg α + 1 := by
  classical
  rw [Finsupp.mem_support_iff] at hβ
  by_contra h
  apply hβ
  rw [magCore_single_apply]
  refine Finset.sum_eq_zero fun i _ => ?_
  have hne : β ≠ Function.update α i (α i + 1) := fun hc => h (by rw [hc, occDeg_update_raise])
  rw [creCoeff_eq_zero_of_ne hne]
  ring

/-! ## The matrix of the ladder, without a box -/

/-- The matrix of the ladder on `Idx d × Idx d`: `magKernel A m n` is the coefficient of `m` in the
image of the occupation state `n`.  No box, no `Λ`. -/
def magKernel (A : Fin d → ℝ) (m n : Idx d) : ℂ :=
  ∑ i, (A i : ℂ) * creCoeff i m n

/-- The core identity and the matrix are the same object: `magKernel` is the matrix of `magCore`. -/
theorem magCore_single_eq_kernel (A : Fin d → ℝ) (n : Idx d) (x : ℂ) (m : Idx d) :
    (magCore A (Finsupp.single n x)) m = magKernel A m n * x := by
  rw [magCore_single_apply, magKernel, Finset.sum_mul]

/-- **The entry at a raise**, exactly: raising direction `i` gives `Aᵢ √(nᵢ + 1)`. -/
theorem magKernel_raise (A : Fin d → ℝ) (n : Idx d) (i : Fin d) :
    magKernel A (Function.update n i (n i + 1)) n
      = (A i : ℂ) * ((Real.sqrt ((n i : ℝ) + 1) : ℝ) : ℂ) := by
  classical
  rw [magKernel]
  have hzero : ∀ j : Fin d, j ≠ i →
      (A j : ℂ) * creCoeff j (Function.update n i (n i + 1)) n = 0 := by
    intro j hj
    have hne : Function.update n i (n i + 1) ≠ Function.update n j (n j + 1) := by
      intro hc
      have h := congrFun hc j
      simp only [Function.update_apply] at h
      split_ifs at h <;> omega
    rw [creCoeff_eq_zero_of_ne hne, mul_zero]
  rw [Finset.sum_eq_single i (fun j _ hj => hzero j hj)
    (fun h => absurd (Finset.mem_univ i) h)]
  rw [creCoeff_self]

/-- **The entry at a lowering is zero**: the bare ladder only creates. -/
theorem magKernel_lower (A : Fin d → ℝ) (n : Idx d) (i : Fin d) :
    magKernel A n (Function.update n i (n i + 1)) = 0 := by
  classical
  rw [magKernel]
  refine Finset.sum_eq_zero fun j _ => ?_
  have hne : n ≠ Function.update (Function.update n i (n i + 1)) j
      (Function.update n i (n i + 1) j + 1) := by
    intro hc
    have h := congrFun hc j
    rw [Function.update_apply, if_pos rfl] at h
    by_cases hji : j = i
    · subst hji
      rw [Function.update_apply, if_pos rfl] at h
      omega
    · rw [Function.update_apply, if_neg hji] at h
      omega
  rw [creCoeff_eq_zero_of_ne hne, mul_zero]

/-- **The bare ladder is not symmetric**: at a raise its entry is `Aᵢ√(nᵢ + 1)` and at the
corresponding lowering it vanishes, so `magKernel A m n ≠ magKernel A n m` as soon as some `Aᵢ` is
nonzero.  Hence no symmetric — in particular no self-adjoint — operator agrees with `magCore` on
the core; the symmetric object is `magSymKernel`. -/
theorem magKernel_asymm {A : Fin d → ℝ} (hA : ∃ i, A i ≠ 0) :
    ∃ m n : Idx d, magKernel A m n ≠ magKernel A n m := by
  classical
  obtain ⟨i, hi⟩ := hA
  refine ⟨Function.update (fun _ : Fin d => (0 : ℕ)) i 1, fun _ => 0, ?_⟩
  have h1 : magKernel A (Function.update (fun _ : Fin d => (0 : ℕ)) i 1) (fun _ => 0)
      = (A i : ℂ) * ((Real.sqrt ((0 : ℝ) + 1) : ℝ) : ℂ) := by
    simpa using magKernel_raise A (fun _ : Fin d => (0 : ℕ)) i
  have h2 : magKernel A (fun _ : Fin d => (0 : ℕ))
      (Function.update (fun _ : Fin d => (0 : ℕ)) i 1) = 0 := by
    simpa using magKernel_lower A (fun _ : Fin d => (0 : ℕ)) i
  rw [h1, h2]
  have hval : ((Real.sqrt ((0 : ℝ) + 1) : ℝ) : ℂ) = 1 := by norm_num
  rw [hval, mul_one]
  intro hzero
  exact hi (by
    have := congrArg Complex.re hzero
    simpa using this)

/-- **The symmetric kernel**: the ladder plus its transpose.  This is the matrix a self-adjoint
magnetic operator on `ℓ²(Idx d)` is built from, and the one whose form the Hilbert–Schmidt and
relative-bound results bound. -/
def magSymKernel (A : Fin d → ℝ) (m n : Idx d) : ℂ :=
  magKernel A m n + magKernel A n m

theorem magSymKernel_comm (A : Fin d → ℝ) (m n : Idx d) :
    magSymKernel A m n = magSymKernel A n m := by
  rw [magSymKernel, magSymKernel, add_comm]

/-! ## Degree truncation: a uniform mass bound

The Hilbert–Schmidt mass of `boxKernel` is finite only because the box is finite.  On `Idx d` the
honest substitute is a **degree** cut: the ladder moves one unit of `occDeg` at a time, so the
symmetric kernel restricted to degrees `≤ N` has finitely many entries and a mass that grows like
`(N+1)^{d+1}` — the same growth as `magCutoffKernel_hs_mass`, with `N` replacing `Λ` and no box.
That is what makes the form dominated without a KLMN theorem: for each `N` the kernel is supported
on a finite set of pairs, so its form is bounded, hence closed; only the uniformity in `N` fails. -/

/-- The symmetric ladder kernel cut down to total occupation number `≤ N`.  No box, no `Λ`. -/
def magSymKernelTrunc (N : ℕ) (A : Fin d → ℝ) (m n : Idx d) : ℂ :=
  if occDeg m ≤ N ∧ occDeg n ≤ N then magSymKernel A m n else 0

theorem magSymKernelTrunc_eq_zero_left {N : ℕ} {A : Fin d → ℝ} {m n : Idx d}
    (h : ¬ occDeg m ≤ N) : magSymKernelTrunc N A m n = 0 := by
  rw [magSymKernelTrunc, if_neg]
  rintro ⟨h1, -⟩
  exact h h1

theorem magSymKernelTrunc_eq_zero_right {N : ℕ} {A : Fin d → ℝ} {m n : Idx d}
    (h : ¬ occDeg n ≤ N) : magSymKernelTrunc N A m n = 0 := by
  rw [magSymKernelTrunc, if_neg]
  rintro ⟨-, h2⟩
  exact h h2

/-- Each entry of the ladder matrix is at most `(∑ᵢ |Aᵢ|) √(occDeg n + 1)`: the weights are
`√(nᵢ + 1)`, and the triangle inequality is enough. -/
theorem norm_magKernel_le (A : Fin d → ℝ) (m n : Idx d) :
    ‖magKernel A m n‖ ≤ (∑ i, |A i|) * Real.sqrt ((occDeg n : ℝ) + 1) := by
  rw [magKernel]
  calc ‖∑ i, (A i : ℂ) * creCoeff i m n‖ ≤ ∑ i, ‖(A i : ℂ) * creCoeff i m n‖ :=
        norm_sum_le Finset.univ _
    _ ≤ ∑ i, |A i| * Real.sqrt ((occDeg n : ℝ) + 1) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        by_cases h : m = Function.update n i (n i + 1)
        · rw [h, creCoeff_self, Complex.norm_real, Real.norm_eq_abs,
            abs_of_nonneg (Real.sqrt_nonneg _)]
          refine Real.sqrt_le_sqrt ?_
          have hle : n i ≤ occDeg n := le_occDeg n i
          have hcast : (n i : ℝ) ≤ (occDeg n : ℝ) := by exact_mod_cast hle
          linarith
        · rw [creCoeff_eq_zero_of_ne h, norm_zero]
          exact Real.sqrt_nonneg _
    _ = (∑ i, |A i|) * Real.sqrt ((occDeg n : ℝ) + 1) := by rw [Finset.sum_mul]

/-- **Uniform entry bound after truncation**: each entry of the truncated symmetric kernel is at
most `4 (∑ᵢ|Aᵢ|)² (N+1)` — both directions are charged the same `√(N+1)`. -/
theorem norm_sq_magSymKernelTrunc_le {N : ℕ} {A : Fin d → ℝ} {m n : Idx d}
    (hm : occDeg m ≤ N) (hn : occDeg n ≤ N) :
    ‖magSymKernelTrunc N A m n‖ ^ 2 ≤ 4 * (∑ i, |A i|) ^ 2 * ((N : ℝ) + 1) := by
  classical
  set S : ℝ := ∑ i, |A i| with hS
  have hS0 : 0 ≤ S := Finset.sum_nonneg fun i _ => abs_nonneg (A i)
  set K : ℝ := S * Real.sqrt ((N : ℝ) + 1) with hK
  have hK0 : 0 ≤ K := mul_nonneg hS0 (Real.sqrt_nonneg _)
  have hsqrt : Real.sqrt ((occDeg n : ℝ) + 1) ≤ Real.sqrt ((N : ℝ) + 1) :=
    Real.sqrt_le_sqrt (by
      have : (occDeg n : ℝ) ≤ (N : ℝ) := by exact_mod_cast hn
      linarith)
  have hsqrt' : Real.sqrt ((occDeg m : ℝ) + 1) ≤ Real.sqrt ((N : ℝ) + 1) :=
    Real.sqrt_le_sqrt (by
      have : (occDeg m : ℝ) ≤ (N : ℝ) := by exact_mod_cast hm
      linarith)
  have h1 : ‖magKernel A m n‖ ≤ K := (norm_magKernel_le A m n).trans (by
    rw [hK, hS]
    exact mul_le_mul_of_nonneg_left hsqrt hS0)
  have h2 : ‖magKernel A n m‖ ≤ K := (norm_magKernel_le A n m).trans (by
    rw [hK, hS]
    exact mul_le_mul_of_nonneg_left hsqrt' hS0)
  have h3 : ‖magKernel A m n + magKernel A n m‖ ≤ 2 * K := by
    calc ‖magKernel A m n + magKernel A n m‖
        ≤ ‖magKernel A m n‖ + ‖magKernel A n m‖ := norm_add_le _ _
      _ ≤ K + K := add_le_add h1 h2
      _ = 2 * K := by ring
  rw [magSymKernelTrunc, if_pos ⟨hm, hn⟩, magSymKernel]
  calc ‖magKernel A m n + magKernel A n m‖ ^ 2
      = ‖magKernel A m n + magKernel A n m‖ * ‖magKernel A m n + magKernel A n m‖ :=
        pow_two _
    _ ≤ (2 * K) * (2 * K) := mul_self_le_mul_self (norm_nonneg _) h3
    _ = 4 * (∑ i, |A i|) ^ 2 * ((N : ℝ) + 1) := by
        rw [hK, hS]
        have hsq : Real.sqrt ((N : ℝ) + 1) ^ 2 = (N : ℝ) + 1 := Real.sq_sqrt (by positivity)
        nlinarith [hsq]

/-- **The uniform mass bound on degree-truncated kernels.**  For every finite set of indices the
Hilbert–Schmidt mass of `magSymKernelTrunc N A` is at most
`((N+1)^d)² · 4 (∑ᵢ|Aᵢ|)² (N+1)`: the count `(N+1)^d` of indices of degree `≤ N` times the entry
bound.  This is the exact analogue of `boxKernel_hs_finset`, with the degree cut replacing the
box. -/
theorem hs_mass_magSymKernelTrunc (N : ℕ) (A : Fin d → ℝ) (s : Finset (Idx d)) :
    ∑ m ∈ s, ∑ n ∈ s, ‖magSymKernelTrunc N A m n‖ ^ 2
      ≤ (((N + 1 : ℕ) : ℝ) ^ d) ^ 2 * (4 * (∑ i, |A i|) ^ 2 * ((N : ℝ) + 1)) := by
  classical
  set E : ℝ := 4 * (∑ i, |A i|) ^ 2 * ((N : ℝ) + 1) with hE
  have hE0 : 0 ≤ E := by rw [hE]; positivity
  set t : Finset (Idx d) := s.filter (fun m => occDeg m ≤ N) with ht
  have houter : ∑ m ∈ s, ∑ n ∈ s, ‖magSymKernelTrunc N A m n‖ ^ 2
      = ∑ m ∈ t, ∑ n ∈ t, ‖magSymKernelTrunc N A m n‖ ^ 2 := by
    rw [ht]
    rw [Finset.sum_subset (Finset.filter_subset _ _) (fun m hm hmn => by
      have h : ¬ occDeg m ≤ N := fun hc => hmn (Finset.mem_filter.mpr ⟨hm, hc⟩)
      simp [magSymKernelTrunc_eq_zero_left h])]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [Finset.sum_subset (Finset.filter_subset _ _) (fun n hn hnm => by
      have h : ¬ occDeg n ≤ N := fun hc => hnm (Finset.mem_filter.mpr ⟨hn, hc⟩)
      simp [magSymKernelTrunc_eq_zero_right h])]
  have hcard : (t.card : ℝ) ≤ ((N + 1 : ℕ) : ℝ) ^ d := by
    have hnat : t.card ≤ (N + 1) ^ d := by
      have himg : t ⊆ (Finset.univ : Finset (Fin d → Fin (N + 1))).image
          (boxEmbed (Λ := N + 1)) := by
        intro m hm
        have hN : occDeg m ≤ N := by
          rw [ht] at hm
          exact (Finset.mem_filter.mp hm).2
        have hin : InBox (Λ := N + 1) m := fun i =>
          Nat.lt_succ_of_le (le_trans (le_occDeg m i) hN)
        obtain ⟨v, hv⟩ := exists_boxEmbed (Λ := N + 1) hin
        exact Finset.mem_image.mpr ⟨v, Finset.mem_univ v, hv⟩
      calc t.card ≤ ((Finset.univ : Finset (Fin d → Fin (N + 1))).image
            (boxEmbed (Λ := N + 1))).card := Finset.card_le_card himg
        _ ≤ Fintype.card (Fin d → Fin (N + 1)) := Finset.card_image_le
        _ = (N + 1) ^ d := by simp
    exact_mod_cast hnat
  rw [houter]
  have hstep : ∑ m ∈ t, ∑ n ∈ t, ‖magSymKernelTrunc N A m n‖ ^ 2
      ≤ (t.card : ℝ) * ((t.card : ℝ) * E) := by
    have hcol : ∀ m ∈ t, ∑ n ∈ t, ‖magSymKernelTrunc N A m n‖ ^ 2 ≤ (t.card : ℝ) * E := by
      intro m hm
      have hmN : occDeg m ≤ N := by
        rw [ht] at hm
        exact (Finset.mem_filter.mp hm).2
      calc ∑ n ∈ t, ‖magSymKernelTrunc N A m n‖ ^ 2 ≤ ∑ _n ∈ t, E := by
            refine Finset.sum_le_sum fun n hn => ?_
            have hnN : occDeg n ≤ N := by
              rw [ht] at hn
              exact (Finset.mem_filter.mp hn).2
            exact norm_sq_magSymKernelTrunc_le hmN hnN
        _ = (t.card : ℝ) * E := by simp [Finset.sum_const, nsmul_eq_mul]
    calc ∑ m ∈ t, ∑ n ∈ t, ‖magSymKernelTrunc N A m n‖ ^ 2
        ≤ ∑ _m ∈ t, (t.card : ℝ) * E := Finset.sum_le_sum hcol
      _ = (t.card : ℝ) * ((t.card : ℝ) * E) := by
          simp [Finset.sum_const, nsmul_eq_mul, mul_assoc]
  refine hstep.trans ?_
  have hCC : (t.card : ℝ) * (t.card : ℝ)
      ≤ (((N + 1 : ℕ) : ℝ) ^ d) * (((N + 1 : ℕ) : ℝ) ^ d) :=
    mul_le_mul hcard hcard (by positivity) (by positivity)
  calc (t.card : ℝ) * ((t.card : ℝ) * E) = ((t.card : ℝ) * (t.card : ℝ)) * E := by ring
    _ ≤ ((((N + 1 : ℕ) : ℝ) ^ d) * (((N + 1 : ℕ) : ℝ) ^ d)) * E :=
        mul_le_mul_of_nonneg_right hCC hE0
    _ = (((N + 1 : ℕ) : ℝ) ^ d) ^ 2 * (4 * (∑ i, |A i|) ^ 2 * ((N : ℝ) + 1)) := by
        rw [hE]; ring

/-- **The KLMN-free domination.**  Since `magSymKernelTrunc N A` is supported in degrees `≤ N`, its
form is bounded by the mass bound above, so `ladder_closed_domination_sharp` applies with the
cut-off-free kernel and a shift `σ` that depends on `N` only.  Nothing is assumed about a box,
and no
KLMN theorem is needed at any fixed `N`; what fails is a `σ` uniform in `N`. -/
theorem closed_farisLavine_magSym_trunc (N : ℕ) (A : Fin d → ℝ) {μ g : Idx d → ℝ}
    {c₁ c₂ σ : ℝ} (hc₁ : 0 < c₁)
    (hσ : (((N + 1 : ℕ) : ℝ) ^ d) ^ 2 * (4 * (∑ i, |A i|) ^ 2 * ((N : ℝ) + 1)) ≤ σ ^ 2)
    (hσ0 : 0 ≤ σ)
    (hdom : ∀ x : L2 d, closedForm g x ≠ ⊤ →
      c₁ * (closedForm μ x).toReal - c₂ * ‖x‖ ^ 2 ≤ (closedForm g x).toReal) :
    0 < (1 / 2) * c₁ ∧
      ∀ x : L2 d, closedForm g x ≠ ⊤ →
        (1 / 2) * c₁ * (closedForm μ x).toReal - ((1 / 2) * c₂ + σ) * ‖x‖ ^ 2
          ≤ (closedForm g x).toReal + closedKernelForm (magSymKernelTrunc N A) x :=
  ladder_closed_domination_sharp (K := magSymKernelTrunc N A) hc₁ hdom hσ0
    (fun s => (hs_mass_magSymKernelTrunc N A s).trans hσ)

end

end BookProof.YangMillsFormClosureND
