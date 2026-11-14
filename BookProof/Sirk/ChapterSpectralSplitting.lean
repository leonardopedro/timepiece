import Mathlib
import BookProof.Sirk.ChapterRitzCertificate

/-!
# Chapter SpectralSplitting — deflating a certified eigenvector

`ChapterResolventTransfer` ends on a side condition: the reflected operator `A'` must be
*spectrally separated* at its certified edge,

  `SpectralSeparation A' lam b`  —  `lam ≤ b` and every spectral point is `lam` or `≥ b`,

and that hypothesis enters as an input.  `ChapterTempleSeparationNecessary` shows that no
Rayleigh/residual data can supply it, so the honest way to shrink the input is to state it
at the level of *forms on the complement of the eigenvector* instead of spectral points.
That reduction needs three pieces of linear algebra, which this chapter builds:

* the orthogonal projections `eigenProjection y` (onto the line `ℂ ∙ y`) and
  `complementProjection y` (onto `yᗮ`), with `P + Q = 1` and `A = lam • P + A ∘ Q`;
* **invariance**: a self-adjoint `A` with `A y = lam y` maps `yᗮ` into itself and commutes
  with `Q`, so the deflated operator `deflated A y = A ∘ Q` has range inside `yᗮ` and is
  again self-adjoint;
* **the cross term vanishes**: for `x = P x + Q x` the off-diagonal pairing
  `inner ℂ (P x) (A (Q x))` is zero, so a lower bound `b ‖z‖² ≤ re (inner ℂ z (A z))` on
  `yᗮ` transfers to the deflated operator as
  `b ‖Q x‖² ≤ re (inner ℂ x ((A ∘ Q) x))`.

What is *not* here is the spectrum union `spectrum A ⊆ spectrum (A ∘ Q) ∪ {lam}`: mathlib
has no block-spectrum lemma for a complemented invariant subspace of a bounded operator on
an abstract Hilbert space, and `ChapterSirkRitzMinMax` records that min–max at `k = 1` is
not available either.  So `spectralSeparation_of_complementBound` stays a target; this
chapter is the layer it needs.
-/

noncomputable section

namespace BookProof.SpectralSplitting

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-! ## 1. The line spanned by a vector and its two projections -/

/-- The complex line spanned by `y`. -/
noncomputable def eigenLine (y : F) : Submodule ℂ F := ℂ ∙ y

instance eigenLineFiniteDimensional (y : F) : FiniteDimensional ℂ (eigenLine y) := by
  unfold eigenLine
  infer_instance

instance eigenLineHasOrthogonalProjection (y : F) : (eigenLine y).HasOrthogonalProjection :=
  Submodule.HasOrthogonalProjection.ofCompleteSpace _

/-- Orthogonal projection onto the line `ℂ ∙ y`. -/
noncomputable def eigenProjection (y : F) : F →L[ℂ] F := (eigenLine y).starProjection

/-- Orthogonal projection onto the complement `yᗮ` of that line. -/
noncomputable def complementProjection (y : F) : F →L[ℂ] F := (eigenLine y)ᗮ.starProjection

omit [CompleteSpace F] in
theorem eigenProjection_apply_mem (y x : F) : eigenProjection y x ∈ eigenLine y :=
  Submodule.starProjection_apply_mem _ x

omit [CompleteSpace F] in
theorem complementProjection_apply_mem (y x : F) :
    complementProjection y x ∈ (eigenLine y)ᗮ :=
  Submodule.starProjection_apply_mem _ x

omit [CompleteSpace F] in
theorem complementProjection_apply_of_mem {y x : F} (hx : x ∈ (eigenLine y)ᗮ) :
    complementProjection y x = x :=
  Submodule.starProjection_eq_self_iff.mpr hx

omit [CompleteSpace F] in
theorem eigenProjection_apply_of_mem {y x : F} (hx : x ∈ eigenLine y) :
    eigenProjection y x = x :=
  Submodule.starProjection_eq_self_iff.mpr hx

omit [CompleteSpace F] in
/-- The two projections split the space: `P + Q = 1`. -/
theorem eigenProjection_add_complementProjection (y : F) :
    eigenProjection y + complementProjection y = (1 : F →L[ℂ] F) := by
  rw [eigenProjection, complementProjection, Submodule.starProjection_orthogonal]
  abel

omit [CompleteSpace F] in
/-- The complement projection annihilates the eigen-line. -/
theorem complementProjection_apply_of_mem_eigenLine {y x : F} (hx : x ∈ eigenLine y) :
    complementProjection y x = 0 := by
  have hP : eigenProjection y x = x := eigenProjection_apply_of_mem hx
  have h := congrArg (fun S : F →L[ℂ] F => S x)
    (eigenProjection_add_complementProjection y)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply, hP] at h
  exact add_left_cancel (a := x) (by simpa using h)

omit [CompleteSpace F] in
/-- The complement projection kills the eigenvector itself. -/
theorem complementProjection_apply_self (y : F) : complementProjection y y = 0 :=
  complementProjection_apply_of_mem_eigenLine (Submodule.mem_span_singleton_self y)

/-! ## 2. Invariance of the complement -/

/-- **A self-adjoint operator preserves the complement of any of its eigenvectors.**
For `x ⟂ y` and `A y = lam y` with `A` self-adjoint, `A x` is again orthogonal to `y`:
`inner ℂ (A x) y = inner ℂ x (A y) = lam * inner ℂ x y = 0`. -/
theorem mapsTo_orthogonal (A : F →L[ℂ] F) (hA : IsSelfAdjoint A) {y : F} {lam : ℂ}
    (hy : A y = lam • y) {x : F} (hx : x ∈ (eigenLine y)ᗮ) :
    A x ∈ (eigenLine y)ᗮ := by
  have hsym : ∀ u v : F, inner ℂ (A u) v = inner ℂ u (A v) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  have hx0 : inner ℂ x y = 0 :=
    (Submodule.mem_orthogonal' (K := eigenLine y) x).mp hx y
      (Submodule.mem_span_singleton_self y)
  rw [Submodule.mem_orthogonal']
  intro w hw
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hw
  rw [hsym]
  simp [hx0, hy]

/-- **The complement projection commutes with a self-adjoint operator at its eigenvector.**
The eigen-line is invariant under `A` (`A y = lam y`) and `yᗮ` is invariant too
(`mapsTo_orthogonal`), so the projection onto the one-dimensional summand commutes with
`A`. -/
theorem complementProjection_commutes (A : F →L[ℂ] F) (hA : IsSelfAdjoint A) {y : F}
    {lam : ℂ} (hy : A y = lam • y) :
    complementProjection y ∘L A = A ∘L complementProjection y := by
  refine ContinuousLinearMap.ext fun x => ?_
  have hsplit := congrArg (fun S : F →L[ℂ] F => S x)
    (eigenProjection_add_complementProjection y)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply] at hsplit
  have hPmem : eigenProjection y x ∈ eigenLine y := eigenProjection_apply_mem y x
  have hQmem : complementProjection y x ∈ (eigenLine y)ᗮ := complementProjection_apply_mem y x
  have hP : A (eigenProjection y x) = lam • eigenProjection y x := by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hPmem
    rw [← hc, map_smul, hy, smul_comm]
  have hAx : A x = lam • eigenProjection y x + A (complementProjection y x) := by
    conv_lhs => rw [← hsplit]
    rw [map_add, hP]
  simp only [ContinuousLinearMap.comp_apply]
  rw [hAx, map_add, map_smul,
    complementProjection_apply_of_mem_eigenLine hPmem,
    complementProjection_apply_of_mem (mapsTo_orthogonal A hA hy hQmem)]
  simp

/-! ## 3. The deflated operator -/

/-- The **deflation** of `A` at the line `ℂ ∙ y`: `A` followed by the projection onto the
complement.  For an eigenvector `y` of a self-adjoint `A` this kills the eigen-direction and
leaves the rest of the spectrum as the remaining problem. -/
noncomputable def deflated (A : F →L[ℂ] F) (y : F) : F →L[ℂ] F :=
  A ∘L complementProjection y

omit [CompleteSpace F] in
theorem deflated_apply (A : F →L[ℂ] F) (y x : F) :
    deflated A y x = A (complementProjection y x) := rfl

omit [CompleteSpace F] in
theorem deflated_apply_self (A : F →L[ℂ] F) (y : F) : deflated A y y = 0 := by
  rw [deflated_apply, complementProjection_apply_self, map_zero]

theorem deflated_apply_mem (A : F →L[ℂ] F) (hA : IsSelfAdjoint A) {y : F} {lam : ℂ}
    (hy : A y = lam • y) (x : F) : deflated A y x ∈ (eigenLine y)ᗮ :=
  mapsTo_orthogonal A hA hy (complementProjection_apply_mem y x)

/-- The deflation of a self-adjoint operator is self-adjoint: it is `A ∘ Q = Q ∘ A`, and
both factors are self-adjoint, so the product is self-adjoint by symmetry of the inner
product. -/
theorem isSelfAdjoint_deflated (A : F →L[ℂ] F) (hA : IsSelfAdjoint A) {y : F} {lam : ℂ}
    (hy : A y = lam • y) : IsSelfAdjoint (deflated A y) := by
  have hsymA : ∀ u v : F, inner ℂ (A u) v = inner ℂ u (A v) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA
  have hsymQ : ∀ u v : F, inner ℂ (complementProjection y u) v =
      inner ℂ u (complementProjection y v) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (isSelfAdjoint_starProjection _)
  have hcomm := complementProjection_commutes A hA hy
  refine ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun u v => ?_
  change inner ℂ ((deflated A y) u) v = inner ℂ u ((deflated A y) v)
  rw [deflated_apply, deflated_apply]
  calc inner ℂ (A (complementProjection y u)) v
      = inner ℂ (complementProjection y u) (A v) := hsymA _ _
    _ = inner ℂ u (complementProjection y (A v)) := hsymQ _ _
    _ = inner ℂ u (A (complementProjection y v)) := by
        have hv := congrArg (fun S : F →L[ℂ] F => S v) hcomm
        simpa only [ContinuousLinearMap.comp_apply] using congrArg (inner ℂ u) hv

/-! ## 4. The decomposition `A = lam • P + A ∘ Q` -/

omit [CompleteSpace F] in
/-- **Spectral splitting of an eigenvector.**  A bounded operator acting as `lam` on the
line `ℂ ∙ y` is the sum of `lam • P` and the deflation at `y` — the operator-level form of
"`y` spans a one-dimensional invariant summand". -/
theorem eq_smul_eigenProjection_add_deflated (A : F →L[ℂ] F) {y : F} {lam : ℂ}
    (hy : A y = lam • y) :
    A = lam • eigenProjection y + deflated A y := by
  refine ContinuousLinearMap.ext fun x => ?_
  have hsplit := congrArg (fun S : F →L[ℂ] F => S x)
    (eigenProjection_add_complementProjection y)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply] at hsplit
  have hPmem : eigenProjection y x ∈ eigenLine y := eigenProjection_apply_mem y x
  have hP : A (eigenProjection y x) = lam • eigenProjection y x := by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp hPmem
    rw [← hc, map_smul, hy, smul_comm]
  nth_rewrite 1 [show x = eigenProjection y x + complementProjection y x from hsplit.symm]
  rw [map_add, hP]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, deflated_apply]
/-! ## 5. The cross term vanishes -/

/-- **The off-diagonal pairing is zero.**  With `x = P x + Q x` and `A (Q x) ∈ yᗮ`, the
component of `x` along `y` contributes nothing to `inner ℂ x (A (Q x))`. -/
theorem inner_eigenProjection_deflated (A : F →L[ℂ] F) (hA : IsSelfAdjoint A) {y : F}
    {lam : ℂ} (hy : A y = lam • y) (x : F) :
    inner ℂ (eigenProjection y x) (deflated A y x) = 0 :=
  (Submodule.mem_orthogonal (K := eigenLine y) (deflated A y x)).mp
    (deflated_apply_mem A hA hy x) (eigenProjection y x) (eigenProjection_apply_mem y x)

/-- **A lower bound on the complement transfers to the deflation.**  If every `z ∈ yᗮ`
satisfies `b ‖z‖² ≤ re (inner ℂ z (A z))`, then `b ‖Q x‖² ≤ re (inner ℂ x ((A ∘ Q) x))`
for every `x`: the deflated operator is bounded below on the whole space by the complement
bound. -/
theorem deflated_re_inner_ge (A : F →L[ℂ] F) (hA : IsSelfAdjoint A) {y : F} {lam : ℂ}
    (hy : A y = lam • y) {b : ℝ}
    (hb : ∀ z ∈ (eigenLine y)ᗮ, b * ‖z‖ ^ 2 ≤ (inner ℂ z (A z) : ℂ).re) (x : F) :
    b * ‖complementProjection y x‖ ^ 2 ≤ (inner ℂ x (deflated A y x) : ℂ).re := by
  have hsplit := congrArg (fun S : F →L[ℂ] F => S x)
    (eigenProjection_add_complementProjection y)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply] at hsplit
  have horth : inner ℂ (eigenProjection y x) (deflated A y x) = 0 :=
    inner_eigenProjection_deflated A hA hy x
  have hmem : complementProjection y x ∈ (eigenLine y)ᗮ := complementProjection_apply_mem y x
  have hinner : inner ℂ x (deflated A y x)
      = inner ℂ (complementProjection y x) (A (complementProjection y x)) := by
    nth_rewrite 1 [show x = eigenProjection y x + complementProjection y x from hsplit.symm]
    rw [inner_add_left, horth, deflated_apply]
    simp
  rw [hinner]
  exact hb _ hmem

end BookProof.SpectralSplitting
