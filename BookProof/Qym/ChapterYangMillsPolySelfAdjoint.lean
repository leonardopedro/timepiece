/-
Copyright (c) 2026.  All rights reserved.

# `polyOp.closure` is self-adjoint

The far end of the S0 programme: the closed polynomial core is a self-adjoint operator.  The input
is spectral and elementary — it is the orthonormal Hermite basis of `ChapterYangMillsPolyBasis` —
and no deficiency-space argument is used, which is what keeps this a *real* statement: over `ℝ`
there is no `±i` to test, so the operator is diagonalized instead.

Two halves.

* **Symmetry.**  `polyOp` is symmetric because it is diagonal in an orthonormal family with real
  eigenvalues: `⟪T b_m, b_n⟫ = m δ_{mn} = ⟪b_m, T b_n⟫` on the generators, and bilinearity
  propagates that to the span (`coreExt_inner_comm_span`, proved by `Submodule.span_induction₂`).
  `closure_isFormalAdjoint` then transfers symmetry to the closure by the sequence
  characterization of the closed graph: if `(xₖ, T xₖ) → (x, T x)` and `(yₗ, T yₗ) → (y, T y)`, the
  inner products `⟪T xₖ, yₗ⟫` converge to both `⟪T x, y⟫` and `⟪x, T y⟫`, and a limit is unique.

* **The adjoint is contained in the closure.**  This is the diagonal-operator argument.  For
  `y ∈ T.adjoint.domain` with `w = T.adjoint y`, the adjoint relation on the basis gives
  `⟪b_n, w⟫ = n ⟪b_n, y⟫`, so the basis expansion of `w` is the basis expansion of `y` with every
  coefficient multiplied by its eigenvalue.  The partial sums of the expansion of `y` therefore lie
  in `T.domain` and their images are the partial sums of the expansion of `w`; both converge,
  `yₙ → y` and `T yₙ → w`, and the closed graph of `T` gives `y ∈ T.domain` with `T y = w`.

With both halves `T.adjoint = T`, so `IsSelfAdjoint T`, and `closure_eq_of_le` then identifies the
closure of the polynomial core with the closure of `gaussOp`, given only that the latter is
symmetric — whence `IsSelfAdjoint gaussOp.closure` as well.

The two halves are not specific to this operator: `BookProof.DiagonalSelfAdjoint` proves them for
any closable operator acting diagonally on an orthonormal Hilbert basis, and the theorems below are
its specialization at `hermiteBasisR` with eigenvalues `n`.
-/
import BookProof.Qym.ChapterYangMillsPolyBasis
import BookProof.Toolbox.ChapterDiagonalSelfAdjoint

open Filter MeasureTheory Polynomial Topology
open scoped ENNReal InnerProductSpace

namespace BookProof.YangMillsPolySelfAdjoint

open BookProof.YangMillsPolyCore BookProof.YangMillsPolyGraphNorm BookProof.YangMillsPolyBasis
open BookProof.YangMillsPolyAnnulus BookProof.YangMillsHermiteSpectrum BookProof.YangMillsMehlerLp
open BookProof.YangMillsGaussForm BookProof.HermiteCore BookProof.SelfAdjointMaximal
open BookProof.DiagonalSelfAdjoint

noncomputable section

/-! ## `polyOp` is symmetric -/

/-- **`polyOp` on a normalized Hermite class.**  `polyOp` is read through `polyOpH`, which is
linear on the span, and `hermiteLpR n` is a nonzero multiple of `polyLp (hermiteR n)`. -/
theorem polyOpH_hermiteLpR (n : ℕ) :
    ((polyOpH ⟨hermiteLpR n, hermiteLpR_mem n⟩ : polyRange) : Lp ℝ 2 gaussMeasure)
      = (n : ℝ) • hermiteLpR n := by
  have hsub : (⟨hermiteLpR n, hermiteLpR_mem n⟩ : hermiteSpan)
      = (hermiteNorm n)⁻¹ •
        (⟨polyLp (hermiteR n), Submodule.subset_span ⟨n, rfl⟩⟩ : hermiteSpan) := by
    refine Subtype.ext ?_
    simp [hermiteLpR]
  rw [hsub, map_smul, Submodule.coe_smul, polyOpH_hermiteR, hermiteLpR]
  rw [smul_smul, smul_smul, mul_comm]

/-- **`polyOp` on a normalized Hermite class**, with the eigenvalue `n`. -/
theorem polyOp_hermiteLpR (n : ℕ) :
    polyOp ⟨hermiteLpR n, hermiteLpR_mem n⟩ = (n : ℝ) • hermiteLpR n :=
  polyOpH_hermiteLpR n

/-- **The global linear extension `coreExt` on a normalized Hermite class.** -/
theorem coreExt_hermiteLpR (n : ℕ) :
    coreExt (hermiteLpR n) = (n : ℝ) • hermiteLpR n := by
  rw [coreExt_apply_mem (hermiteLpR_mem n), polyOpH_hermiteLpR]

/-- **The Hermite classes are symmetric for the polynomial core.**  Both sides are linear in each
variable, so `Submodule.span_induction₂` reduces the claim to the generators; there it is
`m δ_{mn} = n δ_{mn}` for the orthonormal family `hermiteLpR`. -/
theorem coreExt_inner_comm_span {v w : Lp ℝ 2 gaussMeasure}
    (hv : v ∈ Submodule.span ℝ (Set.range hermiteLpR))
    (hw : w ∈ Submodule.span ℝ (Set.range hermiteLpR)) :
    ⟪coreExt v, w⟫_ℝ = ⟪v, coreExt w⟫_ℝ := by
  refine Submodule.span_induction₂ (p := fun v w _ _ =>
    ⟪coreExt v, w⟫_ℝ = ⟪v, coreExt w⟫_ℝ) ?_ ?_ ?_ ?_ ?_ ?_ ?_ hv hw
  · rintro x y ⟨m, rfl⟩ ⟨n, rfl⟩
    rw [coreExt_hermiteLpR, coreExt_hermiteLpR, inner_smul_left, inner_smul_right,
      inner_hermiteLpR]
    by_cases h : m = n <;> simp [h]
  · intro y _
    simp
  · intro x _
    simp
  · intro x y z _ _ _ ix iy
    simp only [map_add, inner_add_left]
    rw [ix, iy]
  · intro x y z _ _ _ iy iz
    simp only [map_add, inner_add_right]
    rw [iy, iz]
  · intro c x y _ _ ix
    simp only [map_smul, inner_smul_left]
    rw [ix]
  · intro c x y _ _ ix
    simp only [map_smul, inner_smul_right]
    rw [ix]

/-- **The polynomial operator is symmetric.**  `polyOp` is `coreExt` read on the span, so this is
`coreExt_inner_comm_span` with the membership proofs supplied by the bundling. -/
theorem polyOp_isFormalAdjoint : polyOp.IsFormalAdjoint polyOp := by
  intro x y
  have hxv : (x : Lp ℝ 2 gaussMeasure) ∈ Submodule.span ℝ (Set.range hermiteLpR) := by
    rw [span_hermiteLpR]
    exact x.2
  have hyv : (y : Lp ℝ 2 gaussMeasure) ∈ Submodule.span ℝ (Set.range hermiteLpR) := by
    rw [span_hermiteLpR]
    exact y.2
  have h := coreExt_inner_comm_span hxv hyv
  rw [coreExt_apply_mem x.2, coreExt_apply_mem y.2] at h
  exact h

/-! ## The closure is symmetric -/

/-- `polyOp` is closable: it sits inside the closed `gaussOp.closure`. -/
theorem polyOp_closure_isClosable : polyOp.IsClosable :=
  polyOp_isClosable polyGraphApprox_holds

/-- **The closure of `polyOp` is symmetric**, by the sequence argument of
`closure_isFormalAdjoint`. -/
theorem polyOp_closure_isFormalAdjoint :
    polyOp.closure.IsFormalAdjoint polyOp.closure :=
  closure_isFormalAdjoint polyOp_isFormalAdjoint polyOp_closure_isClosable

/-- **`polyOp.closure` is a symmetric operator** in the `SymmetricOp` sense. -/
theorem polyOp_closure_isSymmetric : SymmetricOp polyOp.closure :=
  polyOp_closure_isFormalAdjoint

/-- The Hermite span lies in the domain of the closure: `polyOp ≤ polyOp.closure`. -/
theorem hermiteSpan_le_closureDomain : hermiteSpan ≤ polyOp.closure.domain :=
  (LinearPMap.le_closure polyOp).1

/-- The Hermite span is dense in the domain of the closure. -/
theorem dense_closureDomain :
    Dense ((polyOp.closure.domain : Submodule ℝ (Lp ℝ 2 gaussMeasure)) :
      Set (Lp ℝ 2 gaussMeasure)) :=
  dense_hermiteSpanSet.mono fun _ hv => hermiteSpan_le_closureDomain hv

/-- **The closure acts on a Hermite class by its eigenvalue**, for any membership proof. -/
theorem closure_apply_hermiteLpR (n : ℕ) (h : hermiteLpR n ∈ polyOp.closure.domain) :
    polyOp.closure ⟨hermiteLpR n, h⟩ = (n : ℝ) • hermiteLpR n := by
  have hle := hermiteSpan_le_closureDomain (hermiteLpR_mem n)
  have heq : (⟨hermiteLpR n, h⟩ : polyOp.closure.domain) = ⟨hermiteLpR n, hle⟩ :=
    Subtype.ext rfl
  rw [heq]
  have hstep := (LinearPMap.le_closure polyOp).2
    (x := (⟨hermiteLpR n, hermiteLpR_mem n⟩ : polyOp.domain))
    (y := (⟨hermiteLpR n, hle⟩ : polyOp.closure.domain)) rfl
  rw [← hstep, polyOp_hermiteLpR]

/-! ## The adjoint is contained in the closure -/

/-- The Hermite basis lies in the domain of `polyOp`. -/
theorem hermiteBasisR_mem_domain (n : ℕ) : hermiteBasisR n ∈ polyOp.domain :=
  by simpa only [hermiteBasisR_apply] using hermiteLpR_mem n

/-- **`polyOp` acts on a basis vector by its eigenvalue**, for any membership proof. -/
theorem polyOp_hermiteBasisR (n : ℕ) (h : hermiteBasisR n ∈ polyOp.domain) :
    polyOp ⟨hermiteBasisR n, h⟩ = (n : ℝ) • hermiteBasisR n := by
  have h' : hermiteLpR n ∈ polyOp.domain := by
    simpa only [hermiteBasisR_apply] using hermiteLpR_mem n
  rw [show (⟨hermiteBasisR n, h⟩ : polyOp.domain) = ⟨hermiteLpR n, h'⟩ from
    Subtype.ext (hermiteBasisR_apply n)]
  rw [polyOp_hermiteLpR, hermiteBasisR_apply]

/-- The Hermite basis lies in the domain of the closure. -/
theorem hermiteBasisR_mem_closureDomain (n : ℕ) : hermiteBasisR n ∈ polyOp.closure.domain := by
  simpa only [hermiteBasisR_apply] using hermiteSpan_le_closureDomain (hermiteLpR_mem n)

/-- **The closure acts on a basis vector by its eigenvalue**, for any membership proof. -/
theorem closure_apply_hermiteBasisR (n : ℕ) (h : hermiteBasisR n ∈ polyOp.closure.domain) :
    polyOp.closure ⟨hermiteBasisR n, h⟩ = (n : ℝ) • hermiteBasisR n := by
  have h' : hermiteLpR n ∈ polyOp.closure.domain := by
    simpa only [hermiteBasisR_apply] using h
  rw [show (⟨hermiteBasisR n, h⟩ : polyOp.closure.domain) = ⟨hermiteLpR n, h'⟩ from
    Subtype.ext (hermiteBasisR_apply n)]
  rw [closure_apply_hermiteLpR, hermiteBasisR_apply]

/-- **The basis coefficients of the adjoint are the coefficients of the vector, scaled by the
eigenvalues.**  This is `BookProof.DiagonalSelfAdjoint.inner_adjoint_basis` at the Hermite basis:
the adjoint relation `⟪T† y, x⟫ = ⟪y, T x⟫` read at `x = b_n`, where `T b_n = n b_n`. -/
theorem inner_adjoint_hermiteLpR (z : polyOp.closure.adjoint.domain) (n : ℕ) :
    ⟪hermiteLpR n, polyOp.closure.adjoint z⟫_ℝ
      = (n : ℝ) * ⟪hermiteLpR n, (z : Lp ℝ 2 gaussMeasure)⟫_ℝ := by
  have h := inner_adjoint_basis hermiteBasisR (fun n : ℕ => (n : ℝ)) polyOp.closure
    (hermiteBasisR_mem_closureDomain n) (closure_apply_hermiteBasisR n _) dense_closureDomain z
  simpa only [hermiteBasisR_apply] using h

/-- **The adjoint of the closure is contained in the closure.**  This is
`BookProof.DiagonalSelfAdjoint.adjoint_le_closure_of_diag` at the Hermite basis: the expansion of an
adjoint-domain vector converges, its image converges, and closedness of the graph identifies the
limit pair as a graph point. -/
theorem closure_adjoint_le : polyOp.closure.adjoint ≤ polyOp.closure :=
  adjoint_le_closure_of_diag hermiteBasisR (fun n : ℕ => (n : ℝ)) polyOp
    hermiteBasisR_mem_domain (fun n => polyOp_hermiteBasisR n _) polyOp_closure_isClosable

/-- **`polyOp.closure` is self-adjoint.**  `polyOp` is symmetric (`polyOp_isFormalAdjoint`) and
diagonal on the Hermite basis, so
`BookProof.DiagonalSelfAdjoint.isSelfAdjoint_closure_of_diag_symm` applies with no further
hypotheses: symmetry plus a dense diagonal basis is the whole input, and closability is derived from
them. -/
theorem isSelfAdjoint_polyOp_closure : IsSelfAdjoint polyOp.closure :=
  isSelfAdjoint_closure_of_diag_symm hermiteBasisR (fun n : ℕ => (n : ℝ)) polyOp
    hermiteBasisR_mem_domain (fun n => polyOp_hermiteBasisR n _) polyOp_isFormalAdjoint

/-- **`gaussOp.closure` is symmetric**, from the symmetry of `gaussOp` on its core by the same
sequence argument. -/
theorem gaussOp_closure_isSymmetric : SymmetricOp gaussOp.closure :=
  closure_isFormalAdjoint gaussOp_isFormalAdjoint gaussOp_isClosable

/-- **The identification of the polynomial core with the closure of `gaussOp`**, with no
hypotheses at all: `polyOp.closure` is self-adjoint, `gaussOp.closure` is symmetric, and
maximality identifies them. -/
theorem polyOp_closure_eq_gaussOp_closure' : polyOp.closure = gaussOp.closure :=
  polyOp_closure_eq_gaussOp_closure polyGraphApprox_holds isSelfAdjoint_polyOp_closure
    gaussOp_closure_isSymmetric

/-- **`gaussOp.closure` is self-adjoint.**  It *is* the self-adjoint closure of the polynomial core
(`polyOp_closure_eq_gaussOp_closure'`), so self-adjointness transfers along the identification.
This is the last input the S0 identification was waiting on, and it is now a theorem rather than a
hypothesis: `gaussOp` is essentially self-adjoint on its `C²` core. -/
theorem isSelfAdjoint_gaussOp_closure : IsSelfAdjoint gaussOp.closure := by
  rw [← polyOp_closure_eq_gaussOp_closure']
  exact isSelfAdjoint_polyOp_closure

end

end BookProof.YangMillsPolySelfAdjoint
