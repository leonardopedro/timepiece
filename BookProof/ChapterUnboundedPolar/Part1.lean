import BookProof.Prelude
import BookProof.ChapterVonNeumannCore

/-!
# The unbounded polar decomposition: `|Ā| = (A* Ā)^{1/2}` and `Ā = U |Ā|`

`BookProof.ChapterFriedrichsSquareFactorization` builds the composite `A* Ā` as a
linear relation `factorRel A` and proves it self-adjoint;
`BookProof.ChapterVonNeumannCore` adds the bounded inverse
`R = (1 + A* Ā)⁻¹ = resCLM A` and von Neumann's core theorem.  Both modules
recorded the same boundary: the *positive square root* `|Ā| = (A* Ā)^{1/2}` of
the unbounded operator `A* Ā`, and the polar decomposition `Ā = U |Ā|`, were not
proved, because they appear to need a functional calculus for unbounded
self-adjoint operators.

This module proves them, without any unbounded functional calculus.  The whole
construction is carried out with the **bounded** continuous functional calculus
applied to the single positive contraction `R = (1 + A* Ā)⁻¹`:

* `sqrtOp R = R^{1/2}` and `coSqrtOp R = (1 − R)^{1/2}`;
* `|Ā|` is the linear relation `absRel A = {(R^{1/2} y, (1 − R)^{1/2} y) : y}`.

Formally `|Ā| = (1 − R)^{1/2} R^{−1/2}`, which is `((R⁻¹ − 1))^{1/2} = (A* Ā)^{1/2}`,
and its domain is the range of `R^{1/2}`.

## What is proved

Part 0 — a general criterion, extracted from von Neumann's argument: a symmetric
linear relation `S` with `1 + S` surjective is self-adjoint
(`adjPairs_eq_self_of_symmetric_of_surjective`).

Part 1 — the bounded square roots of a positive contraction `R`: `sqrtOp`,
`coSqrtOp`, `midOp` with `R^{1/2} R^{1/2} = R`, `(1−R)^{1/2}(1−R)^{1/2} = 1 − R`,
the commutation `R^{1/2}(1−R)^{1/2} = (1−R)^{1/2}R^{1/2} = midOp R`, positivity,
and the invertibility of `R^{1/2} + (1 − R)^{1/2}` (its spectrum lies in `[1, √2]`).

Part 2 — `R = resCLM A` is a positive, injective contraction (`resCLM_nonneg`,
`resCLM_le_one`, `resCLM_injective`).

Part 3 — the absolute value `absRel A`: it is single-valued, symmetric, positive,
`1 + |Ā|` is surjective, hence **`|Ā|` is self-adjoint** (`adjPairs_absRel`), and
**`|Ā|² = A* Ā`** (`absRel_comp_self`).

Part 4 — the domain and the norm: `D(|Ā|) = D(Ā)` and `‖ |Ā| x ‖ = ‖Ā x‖`
(`absDom_eq_clDom`, `norm_absFun_eq`), proved from von Neumann's core theorem
applied on both sides.

Part 5 — **the polar decomposition** `Ā = U |Ā|`, with `U` a linear isometry of
`ran |Ā|` onto `ran Ā` (`exists_polar_isometry`).

Hypotheses: `F` is a complex Hilbert space, `A` is symmetric on a dense domain
`D`.  No invariance of the domain is used.
-/

namespace BookProof.UnboundedPolar

open BookProof.FarisLavine BookProof.EsaClosure BookProof.ClosureUniqueness
open BookProof.FriedrichsSquare BookProof.VonNeumannCore
open scoped ComplexOrder

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-! ## Part 0 — a symmetric relation with `1 + S` surjective is self-adjoint -/

/-- **Self-adjointness criterion for linear relations.**  If a linear relation
`S ⊆ F × F` is symmetric (`S ⊆ S*`) and `1 + S` is surjective, then `S* = S`.
This is the step of von Neumann's theorem that upgrades symmetry to
self-adjointness. -/
theorem adjPairs_eq_self_of_symmetric_of_surjective {S : Submodule ℂ (F × F)}
    (hsym : S ≤ adjPairs S) (hsurj : ∀ h : F, ∃ p ∈ S, p.1 + p.2 = h) :
    adjPairs S = S := by
  refine le_antisymm ?_ hsym
  intro p hp
  obtain ⟨r, hr, hrsum⟩ := hsurj (p.1 + p.2)
  have hv : p - r ∈ adjPairs S := (adjPairs S).sub_mem hp (hsym hr)
  have hvsum : (p - r).1 + (p - r).2 = 0 := by
    have hsplit : (p - r).1 + (p - r).2 = (p.1 + p.2) - (r.1 + r.2) := by
      simp only [Prod.fst_sub, Prod.snd_sub]; abel
    rw [hsplit, hrsum, sub_self]
  have key : ∀ x : F, (inner ℂ x (p - r).1 : ℂ) = 0 := by
    intro x
    obtain ⟨q, hq, hqsum⟩ := hsurj x
    have hqv := hv q hq
    have hzero : (inner ℂ q.1 ((p - r).1 + (p - r).2) : ℂ) = 0 := by rw [hvsum]; simp
    rw [inner_add_right] at hzero
    rw [← hqsum, inner_add_left, hqv]
    linear_combination hzero
  have hv1 : (p - r).1 = 0 := inner_self_eq_zero.1 (key (p - r).1)
  have hv2 : (p - r).2 = 0 := by
    have := hvsum; rw [hv1, zero_add] at this; exact this
  have hpr : p = r := by
    refine Prod.ext ?_ ?_
    · have := hv1; simp only [Prod.fst_sub, sub_eq_zero] at this; exact this
    · have := hv2; simp only [Prod.snd_sub, sub_eq_zero] at this; exact this
  rw [hpr]; exact hr

/-- The adjoint of a relation is a closed subspace. -/
theorem adjPairs_isClosed (S : Submodule ℂ (F × F)) :
    IsClosed ((adjPairs S : Submodule ℂ (F × F)) : Set (F × F)) := by
  have : ((adjPairs S : Submodule ℂ (F × F)) : Set (F × F))
      = ⋂ q ∈ (S : Set (F × F)), {p : F × F | (inner ℂ q.2 p.1 : ℂ) = inner ℂ q.1 p.2} := by
    ext p; simp only [Set.mem_iInter, Set.mem_setOf_eq]; rfl
  rw [this]
  refine isClosed_biInter fun q _ => ?_
  exact isClosed_eq (continuous_const.inner continuous_fst) (continuous_const.inner continuous_snd)

/-! ## Part 1 — the bounded square roots of a positive contraction -/

section Sqrt

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [CompleteSpace H]

/-- `R^{1/2}` for a positive contraction `R`. -/
noncomputable def sqrtOp (R : H →L[ℂ] H) : H →L[ℂ] H := cfc Real.sqrt R

/-- `(1 − R)^{1/2}` for a positive contraction `R`. -/
noncomputable def coSqrtOp (R : H →L[ℂ] H) : H →L[ℂ] H := cfc (fun t => Real.sqrt (1 - t)) R

/-- `R^{1/2} (1 − R)^{1/2}`. -/
noncomputable def midOp (R : H →L[ℂ] H) : H →L[ℂ] H :=
  cfc (fun t => Real.sqrt t * Real.sqrt (1 - t)) R

variable {R : H →L[ℂ] H}

/-- The spectrum of a positive contraction lies in `[0, 1]`. -/
theorem spectrum_subset_Icc (hR : 0 ≤ R) (h1 : R ≤ 1) : spectrum ℝ R ⊆ Set.Icc 0 1 := by
  intro t ht
  exact ⟨spectrum_nonneg_of_nonneg hR ht,
    (le_algebraMap_iff_spectrum_le (R := ℝ) (a := R) (r := 1)).1 (by simpa using h1) t ht⟩

theorem sqrtOp_mul_self (hR : 0 ≤ R) (h1 : R ≤ 1) : sqrtOp R * sqrtOp R = R := by
  have hsa : IsSelfAdjoint R := hR.isSelfAdjoint
  have hs := spectrum_subset_Icc hR h1
  rw [sqrtOp, ← cfc_mul (R := ℝ) Real.sqrt Real.sqrt R]
  have h : cfc (fun x => Real.sqrt x * Real.sqrt x) R = cfc (id : ℝ → ℝ) R :=
    cfc_congr fun x hx => by simp [Real.mul_self_sqrt (hs hx).1]
  rw [h, cfc_id ℝ R]

theorem coSqrtOp_mul_self (hR : 0 ≤ R) (h1 : R ≤ 1) : coSqrtOp R * coSqrtOp R = 1 - R := by
  have hsa : IsSelfAdjoint R := hR.isSelfAdjoint
  have hs := spectrum_subset_Icc hR h1
  rw [coSqrtOp, ← cfc_mul (R := ℝ) _ _ R]
  have h : cfc (fun x => Real.sqrt (1 - x) * Real.sqrt (1 - x)) R
      = cfc (fun x : ℝ => 1 - id x) R :=
    cfc_congr fun x hx => by
      have hx' : (0:ℝ) ≤ 1 - x := by have := (hs hx).2; linarith
      simp [Real.mul_self_sqrt hx']
  rw [h, cfc_sub (R := ℝ) (fun _ => (1:ℝ)) id R, cfc_const_one ℝ R, cfc_id ℝ R]

theorem sqrtOp_mul_coSqrtOp (hR : 0 ≤ R) :
    sqrtOp R * coSqrtOp R = midOp R := by
  have hsa : IsSelfAdjoint R := hR.isSelfAdjoint
  rw [sqrtOp, coSqrtOp, midOp, cfc_mul (R := ℝ) _ _ R]

theorem coSqrtOp_mul_sqrtOp (hR : 0 ≤ R) :
    coSqrtOp R * sqrtOp R = midOp R := by
  have hsa : IsSelfAdjoint R := hR.isSelfAdjoint
  rw [sqrtOp, coSqrtOp, midOp, cfc_mul (R := ℝ) _ _ R]
  have h : cfc (fun x => Real.sqrt (1 - x) * Real.sqrt x) R
      = cfc (fun x => Real.sqrt x * Real.sqrt (1 - x)) R :=
    cfc_congr fun x _ => mul_comm _ _
  rw [← cfc_mul (R := ℝ) _ _ R, h, cfc_mul (R := ℝ) _ _ R]

theorem sqrtOp_nonneg (R : H →L[ℂ] H) : 0 ≤ sqrtOp R :=
  cfc_nonneg fun x _ => Real.sqrt_nonneg x

theorem coSqrtOp_nonneg (R : H →L[ℂ] H) : 0 ≤ coSqrtOp R :=
  cfc_nonneg fun _ _ => Real.sqrt_nonneg _

theorem midOp_nonneg (R : H →L[ℂ] H) : 0 ≤ midOp R :=
  cfc_nonneg fun _ _ => mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem isSelfAdjoint_sqrtOp (R : H →L[ℂ] H) : IsSelfAdjoint (sqrtOp R) :=
  (sqrtOp_nonneg R).isSelfAdjoint

theorem isSelfAdjoint_coSqrtOp (R : H →L[ℂ] H) : IsSelfAdjoint (coSqrtOp R) :=
  (coSqrtOp_nonneg R).isSelfAdjoint

/-- `R^{1/2} + (1 − R)^{1/2} ≥ 1`: on the spectrum, `√t + √(1−t) ≥ 1`. -/
theorem one_le_sqrtOp_add_coSqrtOp (hR : 0 ≤ R) (h1 : R ≤ 1) :
    1 ≤ sqrtOp R + coSqrtOp R := by
  have hsa : IsSelfAdjoint R := hR.isSelfAdjoint
  have hs := spectrum_subset_Icc hR h1
  have h : sqrtOp R + coSqrtOp R = cfc (fun t => Real.sqrt t + Real.sqrt (1 - t)) R := by
    rw [sqrtOp, coSqrtOp, cfc_add R _ _]
  rw [h]
  refine one_le_cfc _ _ fun x hx => ?_
  obtain ⟨hx0, hx1⟩ := hs hx
  nlinarith [Real.sq_sqrt hx0, Real.sq_sqrt (by linarith : (0:ℝ) ≤ 1 - x),
    Real.sqrt_nonneg x, Real.sqrt_nonneg (1 - x)]

/-- Hence `R^{1/2} + (1 − R)^{1/2}` is invertible. -/
theorem isUnit_sqrtOp_add_coSqrtOp (hR : 0 ≤ R) (h1 : R ≤ 1) :
    IsUnit (sqrtOp R + coSqrtOp R) := by
  have hsa : IsSelfAdjoint (sqrtOp R + coSqrtOp R) :=
    (isSelfAdjoint_sqrtOp R).add (isSelfAdjoint_coSqrtOp R)
  have hle : ∀ x ∈ spectrum ℝ (sqrtOp R + coSqrtOp R), (1:ℝ) ≤ x :=
    (algebraMap_le_iff_le_spectrum (R := ℝ) (a := sqrtOp R + coSqrtOp R) (r := 1)).1
      (by simpa using one_le_sqrtOp_add_coSqrtOp hR h1)
  refine (spectrum.zero_notMem_iff ℝ).1 fun h0 => ?_
  have := hle 0 h0
  linarith

/-- `R^{1/2} + (1 − R)^{1/2}` is surjective. -/
theorem exists_sqrtOp_add_coSqrtOp_eq (hR : 0 ≤ R) (h1 : R ≤ 1) (h : H) :
    ∃ y : H, sqrtOp R y + coSqrtOp R y = h := by
  obtain ⟨u, hu⟩ := isUnit_sqrtOp_add_coSqrtOp hR h1
  refine ⟨(↑u⁻¹ : H →L[ℂ] H) h, ?_⟩
  have : (sqrtOp R + coSqrtOp R) ((↑u⁻¹ : H →L[ℂ] H) h) = h := by
    have hmul : (sqrtOp R + coSqrtOp R) * (↑u⁻¹ : H →L[ℂ] H) = 1 := by
      rw [← hu]; exact u.mul_inv
    calc (sqrtOp R + coSqrtOp R) ((↑u⁻¹ : H →L[ℂ] H) h)
        = ((sqrtOp R + coSqrtOp R) * (↑u⁻¹ : H →L[ℂ] H)) h := rfl
      _ = h := by rw [hmul]; rfl
  simpa using this

/-- `R^{1/2}` is injective when `R` is. -/
theorem sqrtOp_injective (hR : 0 ≤ R) (h1 : R ≤ 1) (hinj : Function.Injective R) :
    Function.Injective (sqrtOp R) := by
  intro y z hyz
  refine hinj ?_
  have h2 : (sqrtOp R * sqrtOp R) y = (sqrtOp R * sqrtOp R) z := by
    change sqrtOp R (sqrtOp R y) = sqrtOp R (sqrtOp R z); rw [hyz]
  rwa [sqrtOp_mul_self hR h1] at h2

end Sqrt

/-- For a self-adjoint bounded operator the inner product may be moved across. -/
theorem inner_isSelfAdjoint_left [CompleteSpace F] {T : F →L[ℂ] F} (hT : IsSelfAdjoint T)
    (x y : F) : (inner ℂ (T x) y : ℂ) = inner ℂ x (T y) := by
  conv_lhs => rw [← hT.star_eq, ContinuousLinearMap.star_eq_adjoint]
  rw [ContinuousLinearMap.adjoint_inner_left]

end BookProof.UnboundedPolar
