import Mathlib
import BookProof.Sirk.ChapterRitzCertificate
import BookProof.Sirk.ChapterSirkRitzSpectrum

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
* **the spectrum union** `spectrum A ⊆ spectrum (A ∘ Q) ∪ {l}`.  mathlib has no
  block-spectrum lemma, but none is needed: because `A = l • P + A ∘ Q` and
  `(A ∘ Q) ∘ P = 0`, the identity `t • 1 − A = (t • 1 − A ∘ Q)(1 − (l/t) • P)` writes
  `t • 1 − A` as a product of units for every `t` in the resolvent of the deflation with
  `t ≠ l`, and the second factor `1 − (l/t) • P` is inverted by `1 + (l/(t−l)) • P`.
  Accordingly `spectralSeparation_of_complementBound` derives
  `SpectralSeparation A l b` from a lower bound on the spectrum of `A ∘ Q`.  That input is
  degenerate (`13q`), so no certificate uses it: the deflated statement is kept only as the
  spectrum-level half of the reduction.

The step from a *form* bound on `yᗮ` (section 5) to a *spectrum* bound is Rayleigh–Ritz,
`ChapterSirkRitzSpectrum.le_rayleigh_iff_le_spectrum`, and it is already in the corpus — but
it does **not** compose with the deflation, for a structural reason: `A ∘ Q` kills `y`, so
`0 ∈ spectrum ℝ (A ∘ Q)` for every eigenvector (`zero_mem_spectrum_deflated`), and a bound on
the whole deflated spectrum therefore forces `b ≤ 0` (`le_zero_of_spectrum_ge_deflated`).
With `l ≤ b` that leaves only `l = b = 0`.  A positive gap has to be read off the
*compression* of `A` to `yᗮ`; the deflation is that compression extended by zero, and the
zero is the obstruction.  Section 8 therefore builds the compression `compressed A hA hy` on
the subspace and proves `spectrum A ⊆ spectrum (compressed) ∪ {l}`, and section 10 turns it
into the reduction this chapter was after: `spectralSeparation_of_compressionBound` derives
`SpectralSeparation A l b` from the *form* bound `b ‖z‖² ≤ re ⟪z, compressed z⟫` on `yᗮ`.
`ChapterResolventTransfer.sirk_reflected_gap_certificate_of_compression` is the certificate
with `hsep` replaced by that hypothesis, and it is non-degenerate: `b > 0` is admissible.

* **the form bound from a measurement** (section 11).  The remaining input is the form bound
  itself, and residual or Rayleigh data provably cannot supply it
  (`ChapterTempleSeparationNecessary.separation_necessary`: an exact eigenvector with
  complement spectrum at `-M`).  What can is an operator-norm measurement:
  `‖A - c • 1‖ ≤ c - b` gives the bound everywhere (`formBound_of_norm_sub_le`), hence on
  `yᗮ` (`formBound_compressed_of_norm_le`), hence the separation without any spectral
  hypothesis about the complement (`spectralSeparation_of_norm_le`).
* **the min–max reading** (`ChapterSirkRitzMinMax.le_minmaxLevel_of_formBound`, applied to the
  compression): the form bound places `b` below *every* Courant–Fischer level of the
  compression, so the certified separation is a statement about the whole Ritz ladder, not just
  its bottom.  The implication does not reverse: the Ritz levels are upper bounds
  (`minmaxLevel_le_minmaxLevelIn`), so a Galerkin computation can refute the bound but never
  establish it.
* **a worked instance** (section 12): `diag (5, 2)` on `EuclideanSpace ℂ (Fin 2)`, where the
  level `b = 3` is admissible on the complement of the eigenvector with eigenvalue `2` and
  inadmissible on the whole space.
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

/-! ## 6. The spectrum union: deflation removes the eigenvector and nothing else

The reduction of `hsep` to a bound on the deflated operator needs one spectral input that
mathlib does not package: for a self-adjoint `A` with `A y = l y` and `y ≠ 0`,

  `spectrum A ⊆ spectrum (A ∘ Q) ∪ {l}`.

The proof is a factorization, not a spectral theorem.  Since `A = l • P + A ∘ Q`
(`eq_smul_eigenProjection_add_deflated`) and `(A ∘ Q) ∘ P = 0`, the identity

  `t • 1 − A = (t • 1 − A ∘ Q) * (1 − (l/t) • P)`      (`t ≠ 0`)

exhibits `t • 1 − A` as a product of two units whenever `t` is in the resolvent of the
deflated operator and `t ≠ l`: the second factor is inverted explicitly by
`1 + (l/(t−l)) • P`.  The point `t = 0` is never in the resolvent of the deflation,
because the deflation kills the nonzero vector `y`. -/

omit [CompleteSpace F] in
/-- `P` is idempotent: `P (P x) = P x`, since `P x` already lies on the line. -/
theorem eigenProjection_mul_self (y : F) :
    eigenProjection y * eigenProjection y = eigenProjection y := by
  refine ContinuousLinearMap.ext fun x => ?_
  exact eigenProjection_apply_of_mem (eigenProjection_apply_mem y x)

omit [CompleteSpace F] in
/-- The deflation is zero on the eigen-line: `(A ∘ Q) ∘ P = 0`. -/
theorem deflated_mul_eigenProjection (A : F →L[ℂ] F) (y : F) :
    deflated A y * eigenProjection y = 0 := by
  refine ContinuousLinearMap.ext fun x => ?_
  rw [ContinuousLinearMap.mul_apply, ContinuousLinearMap.zero_apply, deflated_apply,
    complementProjection_apply_of_mem_eigenLine (eigenProjection_apply_mem y x), map_zero]

omit [CompleteSpace F] in
/-- **The rank-one factor is a unit.**  For an idempotent `P` and `a ≠ 1`, `1 − a • P` is
invertible, with inverse `1 + (a/(1−a)) • P`: the product is
`1 + (−a + (b − a b)) • P` in either order, and the coefficient vanishes at
`b = a/(1−a)`. -/
theorem isUnit_one_sub_smul_of_mul_self {P : F →L[ℂ] F} (hPP : P * P = P) {a : ℂ}
    (ha : a ≠ 1) : IsUnit ((1 : F →L[ℂ] F) - a • P) := by
  have hne : (1 : ℂ) - a ≠ 0 := sub_ne_zero.mpr ha.symm
  set b : ℂ := a / (1 - a) with hbdef
  have hb1 : -a + (b - a * b) = 0 := by
    rw [hbdef]
    field_simp
    ring
  have hb2 : -a + (b - b * a) = 0 := by
    rw [hbdef]
    field_simp
    ring
  have hexp1 : (1 - a • P) * (1 + b • P) = 1 - a • P + (b • P - (a * b) • P) := by
    rw [mul_add, mul_one, sub_mul, one_mul, smul_mul_assoc, mul_smul_comm, smul_smul, hPP]
  have hmain1 : (1 - a • P) * (1 + b • P) = 1 := by
    rw [hexp1, sub_eq_add_neg, ← neg_smul, add_assoc, ← sub_smul, ← add_smul, hb1,
      zero_smul, add_zero]
  have hexp2 : (1 + b • P) * (1 - a • P) = 1 - a • P + (b • P - (b * a) • P) := by
    rw [mul_sub, mul_one, add_mul, one_mul, smul_mul_assoc, mul_smul_comm, smul_smul, hPP]
    abel
  have hmain2 : (1 + b • P) * (1 - a • P) = 1 := by
    rw [hexp2, sub_eq_add_neg, ← neg_smul, add_assoc, ← sub_smul, ← add_smul, hb2,
      zero_smul, add_zero]
  exact ⟨⟨1 - a • P, 1 + b • P, hmain1, hmain2⟩, rfl⟩

omit [CompleteSpace F] in
/-- The eigen-projection instance of `isUnit_one_sub_smul_of_mul_self`. -/
theorem isUnit_one_sub_smul_eigenProjection (y : F) {a : ℂ} (ha : a ≠ 1) :
    IsUnit ((1 : F →L[ℂ] F) - a • eigenProjection y) :=
  isUnit_one_sub_smul_of_mul_self (eigenProjection_mul_self y) ha

omit [CompleteSpace F] in
/-- **The factorization of the resolvent difference.**  For `t ≠ 0`,
`t • 1 − A = (t • 1 − A ∘ Q) * (1 − (l/t) • P)`.  Only `(A ∘ Q) ∘ P = 0` and the
coefficient identity `t · (l/t) = l` are used. -/
theorem sub_smul_one_eq_mul (A : F →L[ℂ] F) {y : F} {l : ℝ}
    (hAy : A y = (l : ℂ) • y) {t : ℝ} (ht : t ≠ 0) :
    (t : ℂ) • (1 : F →L[ℂ] F) - A
      = ((t : ℂ) • (1 : F →L[ℂ] F) - deflated A y) *
          ((1 : F →L[ℂ] F) - ((l : ℂ) / (t : ℂ)) • eigenProjection y) := by
  have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht
  have hcoef : (t : ℂ) * ((l : ℂ) / (t : ℂ)) = (l : ℂ) := by
    field_simp
  have hDP := deflated_mul_eigenProjection A y
  have hDaP : deflated A y * (((l : ℂ) / (t : ℂ)) • eigenProjection y) = 0 := by
    rw [mul_smul_comm, hDP, smul_zero]
  have htP : ((t : ℂ) • (1 : F →L[ℂ] F)) * (((l : ℂ) / (t : ℂ)) • eigenProjection y)
      = (l : ℂ) • eigenProjection y := by
    rw [smul_mul_assoc, one_mul, smul_smul, hcoef]
  calc (t : ℂ) • (1 : F →L[ℂ] F) - A
      = (t : ℂ) • (1 : F →L[ℂ] F) - ((l : ℂ) • eigenProjection y + deflated A y) := by
        conv_lhs => rw [eq_smul_eigenProjection_add_deflated A hAy]
    _ = ((t : ℂ) • (1 : F →L[ℂ] F) - deflated A y) - (l : ℂ) • eigenProjection y := by
        abel
    _ = ((t : ℂ) • (1 : F →L[ℂ] F) - deflated A y)
          - ((t : ℂ) • (1 : F →L[ℂ] F)) * (((l : ℂ) / (t : ℂ)) • eigenProjection y) := by
        rw [htP]
    _ = ((t : ℂ) • (1 : F →L[ℂ] F) - deflated A y)
          - (((t : ℂ) • (1 : F →L[ℂ] F)) * (((l : ℂ) / (t : ℂ)) • eigenProjection y)
            - (deflated A y) * (((l : ℂ) / (t : ℂ)) • eigenProjection y)) := by
        rw [hDaP, sub_zero]
    _ = ((t : ℂ) • (1 : F →L[ℂ] F) - deflated A y)
          - (((t : ℂ) • (1 : F →L[ℂ] F) - deflated A y)
            * (((l : ℂ) / (t : ℂ)) • eigenProjection y)) := by
        rw [sub_mul]
    _ = ((t : ℂ) • (1 : F →L[ℂ] F) - deflated A y)
          * ((1 : F →L[ℂ] F) - ((l : ℂ) / (t : ℂ)) • eigenProjection y) := by
        rw [mul_sub, mul_one]

omit [CompleteSpace F] in
/-- **The spectrum union.**  For a self-adjoint `A` with eigenvector `y ≠ 0` at the real
eigenvalue `l`, every spectral point of `A` is either `l` or a spectral point of the
deflated operator `A ∘ Q`. -/
theorem spectrum_subset_union_deflated (A : F →L[ℂ] F)
    {y : F} (hy : y ≠ 0) {l : ℝ} (hAy : A y = (l : ℂ) • y) :
    spectrum ℝ A ⊆ spectrum ℝ (deflated A y) ∪ {(l : ℝ)} := by
  intro t ht
  rcases eq_or_ne t l with rfl | htl
  · exact Or.inr (Set.mem_singleton _)
  refine Or.inl ?_
  rw [spectrum.mem_iff]
  intro hunit
  have hunitC : IsUnit ((t : ℂ) • (1 : F →L[ℂ] F) - deflated A y) := by
    have h : IsUnit ((t : ℝ) • (1 : F →L[ℂ] F) - deflated A y) := by
      rwa [Algebra.algebraMap_eq_smul_one] at hunit
    rwa [RCLike.real_smul_eq_coe_smul (K := ℂ) t (1 : F →L[ℂ] F)] at h
  by_cases ht0 : t = 0
  · subst ht0
    have hDunit : IsUnit (deflated A y) := by
      have h : IsUnit (-(deflated A y)) := by simpa using hunitC
      simpa using h.neg
    obtain ⟨u, hu⟩ := hDunit
    have h0 : (u : F →L[ℂ] F) y = 0 := by
      rw [hu]
      exact deflated_apply_self A y
    have hy0 : y = 0 := by
      have h1 : u.inv ((u : F →L[ℂ] F) y) = u.inv 0 := by rw [h0]
      rw [← ContinuousLinearMap.mul_apply, u.inv_val, ContinuousLinearMap.one_apply,
        map_zero] at h1
      exact h1
    exact hy hy0
  · have ha1 : (l : ℂ) / (t : ℂ) ≠ 1 := by
      intro h
      have ht' : (t : ℂ) ≠ 0 := by exact_mod_cast ht0
      have hl : (l : ℂ) = (t : ℂ) := by
        have := (div_eq_iff ht').mp h
        simpa using this
      exact htl (by exact_mod_cast hl.symm)
    have hunitP : IsUnit ((1 : F →L[ℂ] F) - ((l : ℂ) / (t : ℂ)) • eigenProjection y) :=
      isUnit_one_sub_smul_eigenProjection y ha1
    have hunitTA : IsUnit ((t : ℂ) • (1 : F →L[ℂ] F) - A) := by
      rw [sub_smul_one_eq_mul A hAy ht0]
      exact hunitC.mul hunitP
    have hnot : ¬ IsUnit ((t : ℝ) • (1 : F →L[ℂ] F) - A) := by
      simpa [Algebra.algebraMap_eq_smul_one] using (spectrum.mem_iff.mp ht)
    refine hnot ?_
    rw [RCLike.real_smul_eq_coe_smul (K := ℂ) t (1 : F →L[ℂ] F)]
    exact hunitTA

omit [CompleteSpace F] in
/-- **The separation transfers to the deflated operator.**  If the deflated operator
`A ∘ Q` is bounded below by `b` on its whole spectrum and `l ≤ b`, then `A` is spectrally
separated at `l` with lower bound `b` — the `hsep` input, stated at the level of the
operator left after the certified eigenvector is removed.

Section 7 explains why this is *not* a weakening for a positive gap: the deflation contains
`0` in its spectrum (`zero_mem_spectrum_deflated`), so `hD` forces `b ≤ 0`, and `l ≤ b` leaves
`l = b = 0`.  The statement is the correct reduction for a *spectrum* bound; a *form* bound has
to be taken on the compression to `yᗮ`. -/
theorem spectralSeparation_of_complementBound (A : F →L[ℂ] F)
    {y : F} (hy : y ≠ 0) {l b : ℝ} (hAy : A y = (l : ℂ) • y) (hlb : l ≤ b)
    (hD : ∀ t ∈ spectrum ℝ (deflated A y), b ≤ t) :
    BookProof.RitzCertificate.SpectralSeparation A l b := by
  refine ⟨hlb, fun t ht => ?_⟩
  rcases spectrum_subset_union_deflated A hy hAy ht with h | h
  · exact Or.inr (hD t h)
  · exact Or.inl (Set.mem_singleton_iff.mp h)

/-! ## 7. Why the deflation cannot carry a positive gap

Section 5 gives `b ‖Q x‖² ≤ re (inner ℂ x ((A ∘ Q) x))` from a bound on `yᗮ`, and
`ChapterSirkRitzSpectrum.le_rayleigh_iff_le_spectrum` turns a *whole-space* form bound into a
whole-space spectrum bound.  The two do **not** compose, and the obstruction is structural:
the deflation `A ∘ Q` kills `y`, so `0` is always in its spectrum, and a bound `b ≤ t` on
*all* of `spectrum ℝ (A ∘ Q)` therefore forces `b ≤ 0`.  Together with `l ≤ b` that leaves
only the degenerate case `l = b = 0`.

The object whose spectrum really carries the complement bound is the **compression** of `A`
to `yᗮ`.  `A ∘ Q` is that compression extended by `0` on `ℂ ∙ y`, and the extra `0` is
exactly what rules out a positive `b`.  A gap statement therefore cannot be routed through
`A ∘ Q`; the block decomposition has to be taken on the subspace itself. -/

omit [CompleteSpace F] in
/-- **The deflation always has `0` in its spectrum.**  `A ∘ Q` annihilates the eigenvector,
so a unit of the algebra would carry the nonzero `y` to `0` and back. -/
theorem zero_mem_spectrum_deflated (A : F →L[ℂ] F) {y : F} (hy : y ≠ 0) :
    (0 : ℝ) ∈ spectrum ℝ (deflated A y) := by
  rw [spectrum.mem_iff]
  intro hunit
  have hDunit : IsUnit (deflated A y) := by
    have h : IsUnit (-(deflated A y)) := by simpa using hunit
    simpa using h.neg
  obtain ⟨u, hu⟩ := hDunit
  have h0 : (u : F →L[ℂ] F) y = 0 := by
    rw [hu]
    exact deflated_apply_self A y
  have hy0 : y = 0 := by
    have h1 : u.inv ((u : F →L[ℂ] F) y) = u.inv 0 := by rw [h0]
    rw [← ContinuousLinearMap.mul_apply, u.inv_val, ContinuousLinearMap.one_apply,
      map_zero] at h1
    exact h1
  exact hy hy0

omit [CompleteSpace F] in
/-- **A spectrum bound on the deflation forces `b ≤ 0`.**  This is the obstruction: the
hypothesis of `spectralSeparation_of_complementBound` is satisfiable only when the lower
bound is nonpositive, so it cannot certify a gap `l < b` with `0 < b`. -/
theorem le_zero_of_spectrum_ge_deflated (A : F →L[ℂ] F) {y : F} (hy : y ≠ 0) {b : ℝ}
    (hD : ∀ t ∈ spectrum ℝ (deflated A y), b ≤ t) : b ≤ 0 :=
  hD 0 (zero_mem_spectrum_deflated A hy)

/-! ## 8. The compression to the complement and the block spectrum

`deflated A y = A ∘ Q` is the compression of `A` to `yᗮ` **extended by zero** on the line, and
section 7 shows that added `0` ruins every spectral bound.  The compression itself is an
operator *on* the subspace, `compressed A y : yᗮ →L[ℂ] yᗮ`, `z ↦ A z`, and this section proves
the block statement

  `spectrum A ⊆ spectrum (compressed A y) ∪ {l}`,

the replacement for the deflation union that carries no spurious point.  With it, a form bound
on `yᗮ` and `le_rayleigh_iff_le_spectrum` on the compression give the gap of `A` directly. -/

/-- The **compression** of `A` to `yᗮ`: the operator `z ↦ A z` on the subspace, well defined
because a self-adjoint `A` preserves the complement of each of its eigenvectors
(`mapsTo_orthogonal`). -/
noncomputable def compressed (A : F →L[ℂ] F) (hA : IsSelfAdjoint A) {y : F} {lam : ℂ}
    (hy : A y = lam • y) : (eigenLine y)ᗮ →L[ℂ] (eigenLine y)ᗮ :=
  (A.comp (Submodule.subtypeL (eigenLine y)ᗮ)).codRestrict (eigenLine y)ᗮ
    fun z => mapsTo_orthogonal A hA hy z.2

/-- The compression acts as `A` on the underlying vectors. -/
theorem compressed_apply_coe (A : F →L[ℂ] F) (hA : IsSelfAdjoint A) {y : F} {lam : ℂ}
    (hy : A y = lam • y) (z : (eigenLine y)ᗮ) :
    (compressed A hA hy z : F) = A (z : F) := by
  simp [compressed, ContinuousLinearMap.coe_codRestrict_apply]

/-- The projection onto `yᗮ`, regarded as a map into the subtype. -/
noncomputable def complementProjectionCod (y : F) : F →L[ℂ] (eigenLine y)ᗮ :=
  (complementProjection y).codRestrict (eigenLine y)ᗮ
    fun x => complementProjection_apply_mem y x

omit [CompleteSpace F] in
/-- Restricting the projection to the subspace gives the identity there. -/
theorem complementProjectionCod_comp_subtype (y : F) :
    (complementProjectionCod y).comp (Submodule.subtypeL (eigenLine y)ᗮ)
      = (1 : (eigenLine y)ᗮ →L[ℂ] (eigenLine y)ᗮ) := by
  refine ContinuousLinearMap.ext fun z => ?_
  refine Subtype.ext ?_
  simp [complementProjectionCod, ContinuousLinearMap.coe_codRestrict_apply,
    complementProjection_apply_of_mem z.2]

omit [CompleteSpace F] in
/-- Extending the codomain-restricted projection back to `F` recovers the projection. -/
theorem subtype_comp_complementProjectionCod (y : F) :
    (Submodule.subtypeL (eigenLine y)ᗮ).comp (complementProjectionCod y)
      = complementProjection y := by
  refine ContinuousLinearMap.ext fun x => ?_
  simp [complementProjectionCod, ContinuousLinearMap.coe_codRestrict_apply]

/-- The eigen-projection kills the complement of the line. -/
theorem eigenProjection_apply_eq_zero_of_mem_orthogonal {y x : F}
    (hx : x ∈ (eigenLine y)ᗮ) (hy0 : y ≠ 0) : eigenProjection y x = 0 := by
  have hsym : ∀ u v : F, inner ℂ (eigenProjection y u) v = inner ℂ u (eigenProjection y v) :=
    ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp (isSelfAdjoint_starProjection _)
  have hxy : inner ℂ x y = 0 :=
    (Submodule.mem_orthogonal' (K := eigenLine y) x).mp hx y
      (Submodule.mem_span_singleton_self y)
  have hPy : eigenProjection y y = y :=
    eigenProjection_apply_of_mem (Submodule.mem_span_singleton_self y)
  have h1 : inner ℂ (eigenProjection y x) y = 0 := by
    rw [hsym, hPy, hxy]
  obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (eigenProjection_apply_mem y x)
  have hcy : (starRingEnd ℂ) c * (inner ℂ y y) = 0 := by
    calc (starRingEnd ℂ) c * (inner ℂ y y) = inner ℂ (c • y) y := (inner_smul_left _ _ _).symm
      _ = inner ℂ (eigenProjection y x) y := by rw [hc]
      _ = 0 := h1
  have hnorm : (inner ℂ y y : ℂ) ≠ 0 := by
    rw [inner_self_eq_norm_sq_to_K]
    have hyC : (‖y‖ : ℂ) ≠ 0 := Complex.ofReal_ne_zero.mpr (norm_ne_zero_iff.mpr hy0)
    exact pow_ne_zero 2 hyC
  have hc0 : c = 0 := by
    have hres := (mul_eq_zero.mp hcy).resolve_right hnorm
    simpa using hres
  calc eigenProjection y x = c • y := hc.symm
    _ = 0 := by rw [hc0, zero_smul]

/-- The eigen-projection annihilates the subspace `yᗮ`. -/
theorem eigenProjection_comp_subtype_orthogonal (y : F) (hy0 : y ≠ 0) :
    (eigenProjection y).comp (Submodule.subtypeL (eigenLine y)ᗮ) = 0 := by
  refine ContinuousLinearMap.ext fun z => ?_
  exact eigenProjection_apply_eq_zero_of_mem_orthogonal z.2 hy0

omit [CompleteSpace F] in
/-- The complement projection is idempotent. -/
theorem complementProjection_comp_self (y : F) :
    (complementProjection y).comp (complementProjection y) = complementProjection y := by
  refine ContinuousLinearMap.ext fun x => ?_
  exact complementProjection_apply_of_mem (complementProjection_apply_mem y x)

omit [CompleteSpace F] in
/-- The complement projection kills the line. -/
theorem complementProjection_comp_eigenProjection (y : F) :
    (complementProjection y).comp (eigenProjection y) = 0 := by
  refine ContinuousLinearMap.ext fun x => ?_
  exact complementProjection_apply_of_mem_eigenLine (eigenProjection_apply_mem y x)

omit [CompleteSpace F] in
/-- The codomain-restricted complement projection kills the line too. -/
theorem complementProjectionCod_comp_eigenProjection (y : F) :
    (complementProjectionCod y).comp (eigenProjection y) = 0 := by
  refine ContinuousLinearMap.ext fun x => ?_
  refine Subtype.ext ?_
  simp [complementProjectionCod, ContinuousLinearMap.coe_codRestrict_apply,
    complementProjection_apply_of_mem_eigenLine (eigenProjection_apply_mem y x)]

/-- The block decomposition of `A` with respect to `1 = P + Q`: the eigenvalue on the line and
the compression on `yᗮ`. -/
theorem eq_smul_eigenProjection_add_compressed (A : F →L[ℂ] F) (hA : IsSelfAdjoint A)
    {y : F} {lam : ℂ} (hy : A y = lam • y) :
    A = lam • eigenProjection y +
      (Submodule.subtypeL (eigenLine y)ᗮ).comp
        ((compressed A hA hy).comp (complementProjectionCod y)) := by
  refine ContinuousLinearMap.ext fun x => ?_
  have hsplit := congrArg (fun S : F →L[ℂ] F => S x)
    (eigenProjection_add_complementProjection y)
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.one_apply] at hsplit
  have hx : x = eigenProjection y x + complementProjection y x := hsplit.symm
  nth_rewrite 1 [hx]
  rw [map_add]
  have hP : A (eigenProjection y x) = lam • eigenProjection y x := by
    obtain ⟨c, hc⟩ := Submodule.mem_span_singleton.mp (eigenProjection_apply_mem y x)
    rw [← hc, map_smul, hy, smul_comm]
  rw [hP]
  have hR : ((lam • eigenProjection y + (Submodule.subtypeL (eigenLine y)ᗮ).comp
        ((compressed A hA hy).comp (complementProjectionCod y))) x)
      = lam • eigenProjection y x + (compressed A hA hy (complementProjectionCod y x) : F) :=
    rfl
  rw [hR, compressed_apply_coe]
  rfl

/-! ## 9. The spectrum of `A` is the eigenvalue plus the compression's spectrum

The block decomposition of section 8 is turned into a spectrum statement.  For `t ≠ l` the
operator `A − t` is block diagonal, with block `l − t` on the line and `C − t` on `yᗮ`, so it
is invertible exactly when `C − t` is; the inverse is `(l − t)⁻¹ • P + Q̃ (C − t)⁻¹ Q̃`, where
`Q̃` is the codomain-restricted complement projection.  Unlike the deflation of section 7, no
spurious `0` enters. -/

section BlockAlgebra

/-- Multiplication of two "blocks" `f ∘ A ∘ g` and `f ∘ B ∘ g`, using `g ∘ f = 1`: the outer
maps cancel and the inner operators multiply. -/
theorem comp_sub_comp_mul {U V : Type*} [NormedAddCommGroup U] [NormedSpace ℂ U]
    [NormedAddCommGroup V] [NormedSpace ℂ V]
    (f : U →L[ℂ] V) (g : V →L[ℂ] U) (A B : U →L[ℂ] U) (hgf : g.comp f = 1) :
    (f.comp (A.comp g)).comp (f.comp (B.comp g)) = f.comp ((A.comp B).comp g) := by
  rw [ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc,
    show g.comp (f.comp (B.comp g)) = (g.comp f).comp (B.comp g) from
      (ContinuousLinearMap.comp_assoc g f (B.comp g)).symm,
    hgf, ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp,
    ← ContinuousLinearMap.comp_assoc A B g]

end BlockAlgebra

/-- **The block spectrum.**  For a self-adjoint `A`, a nonzero eigenvector `y` and the real
eigenvalue `l`, the spectrum of `A` is contained in the spectrum of the compression to `yᗮ`
together with `{l}`. -/
theorem spectrum_subset_union_compressed (A : F →L[ℂ] F) (hA : IsSelfAdjoint A)
    {y : F} (hy0 : y ≠ 0) {lam : ℝ} (hAy : A y = (lam : ℂ) • y) :
    spectrum ℝ A ⊆ spectrum ℝ (compressed A hA hAy) ∪ {(lam : ℝ)} := by
  intro t ht
  rcases eq_or_ne t lam with rfl | htlam
  · exact Or.inr (by simp)
  refine Or.inl ?_
  rw [spectrum.mem_iff]
  intro hunit
  set K := (eigenLine y)ᗮ with hK
  set C : K →L[ℂ] K := compressed A hA hAy with hCdef
  set P : F →L[ℂ] F := eigenProjection y with hPdef
  set Q : F →L[ℂ] F := complementProjection y with hQdef
  set Qc : F →L[ℂ] K := complementProjectionCod y with hQcdef
  set sub : K →L[ℂ] F := Submodule.subtypeL K with hsubdef
  -- the unit for `algebraMap t - C` and the two blocks on `K`
  obtain ⟨v, hv⟩ := hunit
  have hvC : (v : K →L[ℂ] K) = algebraMap ℝ (K →L[ℂ] K) t - C := hv
  set W : K →L[ℂ] K := C - (t : ℂ) • (1 : K →L[ℂ] K) with hWdef
  have hWneg : W = -(v : K →L[ℂ] K) := by
    rw [hWdef, hvC, Algebra.algebraMap_eq_smul_one]
    abel
  set w : K →L[ℂ] K := -(↑v.inv) with hwdef
  have hWl : W.comp w = 1 := by
    rw [hWneg, hwdef]
    simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.neg_comp,
      ContinuousLinearMap.comp_neg, neg_neg] using Units.mul_inv v
  have hWr : w.comp W = 1 := by
    rw [hWneg, hwdef]
    simpa only [ContinuousLinearMap.mul_def, ContinuousLinearMap.neg_comp,
      ContinuousLinearMap.comp_neg, neg_neg] using Units.inv_mul v
  -- block algebra on `F`
  have hPP : P.comp P = P := eigenProjection_mul_self y
  have hPQ : P + Q = 1 := eigenProjection_add_complementProjection y
  have hPsub : P.comp sub = 0 := eigenProjection_comp_subtype_orthogonal y hy0
  have hQcsub : Qc.comp sub = 1 := complementProjectionCod_comp_subtype y
  have hsubQc : sub.comp Qc = Q := subtype_comp_complementProjectionCod y
  have hQcP : Qc.comp P = 0 := complementProjectionCod_comp_eigenProjection y
  set E : F →L[ℂ] F := sub.comp (W.comp Qc) with hEdef
  set E' : F →L[ℂ] F := sub.comp (w.comp Qc) with hE'def
  have hAblk : A = (lam : ℂ) • P + sub.comp (C.comp Qc) := by
    have h := eq_smul_eigenProjection_add_compressed A hA hAy
    rw [h, hPdef, hsubdef, hQcdef, hCdef]
  -- `A - t` is the block diagonal and the blocks invert each other
  have htQ : (t : ℂ) • Q = sub.comp (((t : ℂ) • (1 : K →L[ℂ] K)).comp Qc) := by
    rw [show sub.comp (((t : ℂ) • (1 : K →L[ℂ] K)).comp Qc) = (t : ℂ) • sub.comp Qc from by
      rw [ContinuousLinearMap.smul_comp, ContinuousLinearMap.one_def,
        ContinuousLinearMap.id_comp, ContinuousLinearMap.comp_smul], hsubQc]
  have hstep : sub.comp (C.comp Qc) - (t : ℂ) • Q = E := by
    rw [htQ, ← ContinuousLinearMap.comp_sub, ← ContinuousLinearMap.sub_comp, hEdef, hWdef]
  have hAt : A - (t : ℂ) • (1 : F →L[ℂ] F) = ((lam : ℂ) - t) • P + E := by
    rw [hAblk, ← hPQ, smul_add, sub_smul,
      show (lam : ℂ) • P + sub.comp (C.comp Qc) - ((t : ℂ) • P + (t : ℂ) • Q)
          = (lam : ℂ) • P - (t : ℂ) • P +
            (sub.comp (C.comp Qc) - (t : ℂ) • Q) from by abel,
      hstep]
  have hPE : P.comp E = 0 := by
    rw [hEdef, ← ContinuousLinearMap.comp_assoc, hPsub, ContinuousLinearMap.zero_comp]
  have hEP : E.comp P = 0 := by
    rw [hEdef, ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc, hQcP,
      ContinuousLinearMap.comp_zero, ContinuousLinearMap.comp_zero]
  have hPE' : P.comp E' = 0 := by
    rw [hE'def, ← ContinuousLinearMap.comp_assoc, hPsub, ContinuousLinearMap.zero_comp]
  have hE'P : E'.comp P = 0 := by
    rw [hE'def, ContinuousLinearMap.comp_assoc, ContinuousLinearMap.comp_assoc, hQcP,
      ContinuousLinearMap.comp_zero, ContinuousLinearMap.comp_zero]
  have hEE' : E.comp E' = Q := by
    rw [hEdef, hE'def, comp_sub_comp_mul sub Qc W w hQcsub, hWl,
      ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp, hsubQc]
  have hE'E : E'.comp E = Q := by
    rw [hEdef, hE'def, comp_sub_comp_mul sub Qc w W hQcsub, hWr,
      ContinuousLinearMap.one_def, ContinuousLinearMap.id_comp, hsubQc]
  -- the two-sided inverse
  have hcoe : ((lam : ℂ) - t) * (((lam : ℂ) - t)⁻¹) = 1 := by
    exact mul_inv_cancel₀ (sub_ne_zero.mpr (by exact_mod_cast Ne.symm htlam))
  have hcoe' : (((lam : ℂ) - t)⁻¹) * ((lam : ℂ) - t) = 1 := by
    exact inv_mul_cancel₀ (sub_ne_zero.mpr (by exact_mod_cast Ne.symm htlam))
  have hinv : (A - (t : ℂ) • (1 : F →L[ℂ] F)).comp
      ((((lam : ℂ) - t)⁻¹) • P + E') = 1 := by
    rw [hAt]
    simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    rw [hPP, hPE', hEP, hEE']
    simp [smul_smul, hcoe', hPQ]
  have hinv' : ((((lam : ℂ) - t)⁻¹) • P + E').comp
      (A - (t : ℂ) • (1 : F →L[ℂ] F)) = 1 := by
    rw [hAt]
    simp only [ContinuousLinearMap.add_comp, ContinuousLinearMap.comp_add,
      ContinuousLinearMap.smul_comp, ContinuousLinearMap.comp_smul]
    rw [hPP, hPE, hE'P, hE'E]
    simp [smul_smul, hcoe, hPQ]
  have hunitA : IsUnit (A - (t : ℂ) • (1 : F →L[ℂ] F)) :=
    isUnit_iff_exists.mpr ⟨_, hinv, hinv'⟩
  have hneg : IsUnit (algebraMap ℝ (F →L[ℂ] F) t - A) := by
    have h := hunitA.neg
    rw [show -(A - (t : ℂ) • (1 : F →L[ℂ] F)) =
        algebraMap ℝ (F →L[ℂ] F) t - A from by
      simp only [Algebra.algebraMap_eq_smul_one]
      abel] at h
    exact h
  exact (spectrum.mem_iff.mp ht) hneg


/-! ## 10. The separation input from a form bound on the compression

`spectralSeparation_of_complementBound` states the separation at the level of a *spectrum*
bound on the deflation, and section 7 showed that form is degenerate for a positive gap.  The
right input is a *form* bound on the compression: `b ‖z‖² ≤ re ⟪z, compressed z⟫` for every
`z ∈ yᗮ`.  `le_rayleigh_iff_le_spectrum` turns it into a spectrum bound on the compression —
that is where it is a bottom-level statement — and `spectrum_subset_union_compressed` carries
the bound back to `A`, with `l` covering the line. -/

/-- The compression is self-adjoint: it is `A` restricted to the invariant subspace `yᗮ`. -/
theorem isSelfAdjoint_compressed (A : F →L[ℂ] F) (hA : IsSelfAdjoint A) {y : F} {lam : ℂ}
    (hy : A y = lam • y) : IsSelfAdjoint (compressed A hA hy) := by
  haveI : CompleteSpace ↥(eigenLine y)ᗮ :=
    (Submodule.isClosed_orthogonal (eigenLine y)).completeSpace_coe
  refine ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mpr fun z w => ?_
  have hs : (inner ℂ ((compressed A hA hy z : ↥(eigenLine y)ᗮ) : F) (w : F))
      = inner ℂ (z : F) ((compressed A hA hy w : ↥(eigenLine y)ᗮ) : F) := by
    rw [compressed_apply_coe, compressed_apply_coe]
    exact (ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.mp hA) (z : F) (w : F)
  simpa only [Submodule.coe_inner] using hs

/-- **The separation from a form bound on the compression.**  If the compression to `yᗮ` is
bounded below by `b` in form and `l ≤ b`, then `A` is spectrally separated at `l` with lower
bound `b` — the `hsep` input of the reflected-gap certificate, with no spurious `0` and no
restriction to the degenerate case. -/
theorem spectralSeparation_of_compressionBound (A : F →L[ℂ] F) (hA : IsSelfAdjoint A)
    {y : F} (hy0 : y ≠ 0) {l b : ℝ} (hAy : A y = (l : ℂ) • y) (hlb : l ≤ b)
    (hC : ∀ z : ↥(eigenLine y)ᗮ,
      b * ‖z‖ ^ 2 ≤ (inner ℂ z (compressed A hA hAy z) : ℂ).re) :
    BookProof.RitzCertificate.SpectralSeparation A l b := by
  haveI : CompleteSpace ↥(eigenLine y)ᗮ :=
    (Submodule.isClosed_orthogonal (eigenLine y)).completeSpace_coe
  have hspec : ∀ t ∈ spectrum ℝ (compressed A hA hAy), b ≤ t :=
    (BookProof.ChapterSirkRitzSpectrum.le_rayleigh_iff_le_spectrum
      (compressed A hA hAy) (isSelfAdjoint_compressed A hA hAy) b).mp hC
  refine ⟨hlb, fun t ht => ?_⟩
  rcases spectrum_subset_union_compressed A hA hy0 hAy ht with h | h
  · exact Or.inr (hspec t h)
  · exact Or.inl (Set.mem_singleton_iff.mp h)


/-! ## 11. Deriving the form bound from a norm perturbation

Section 10 leaves one input: the form bound `b ‖z‖² ≤ re ⟪z, compressed z⟫` on `yᗮ`.  It
cannot be read off residual data — `ChapterTempleSeparationNecessary.separation_necessary`
exhibits an *exact* eigenvector (zero residual, Rayleigh quotient `0`) whose complement
spectrum sits at `-M` for every `M`.  What *can* be supplied by a finite measurement is the
operator-norm distance of `A` from a scalar: `T = c • 1 + N` with `‖N‖ ≤ c - b` gives the form
bound everywhere, hence on `yᗮ`.  This is the numerical-range route, and the quantity
`‖A - c • 1‖` is what the SIRK flow and numerical-range bounds estimate. -/

/-- The real part of a squared real, read in `ℂ`. -/
theorem re_sq_ofReal (r : ℝ) : (((r : ℂ)) ^ 2).re = r ^ 2 := by
  have h : ((r : ℂ) ^ 2) = ((r ^ 2 : ℝ) : ℂ) := by
    push_cast
    ring
  rw [h, Complex.ofReal_re]

omit [CompleteSpace F] in
/-- **The form bound from a norm perturbation.**  If `T` is within `c - b` in operator norm of
the scalar `c`, then `b ‖z‖² ≤ re ⟪z, T z⟫` for every `z`. -/
theorem formBound_of_norm_sub_le (T : F →L[ℂ] F) {c b : ℝ}
    (hN : ‖T - (c : ℂ) • 1‖ ≤ c - b) (z : F) :
    b * ‖z‖ ^ 2 ≤ (inner ℂ z (T z) : ℂ).re := by
  set N : F →L[ℂ] F := T - (c : ℂ) • 1 with hNdef
  have hsplit : T z = (c : ℂ) • z + N z := by
    simp [hNdef, ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
      ContinuousLinearMap.one_apply]
  have hinner : (inner ℂ z (T z) : ℂ)
      = (c : ℂ) * inner ℂ z z + inner ℂ z (N z) := by
    rw [hsplit, inner_add_right, inner_smul_right]
  have hzz : (inner ℂ z z : ℂ).re = ‖z‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    exact re_sq_ofReal ‖z‖
  have hre : (inner ℂ z (T z) : ℂ).re
      = c * ‖z‖ ^ 2 + (inner ℂ z (N z) : ℂ).re := by
    rw [hinner, Complex.add_re, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, hzz]
    ring
  have hlow : -(‖N‖ * ‖z‖ ^ 2) ≤ (inner ℂ z (N z) : ℂ).re := by
    have h1 : |(inner ℂ z (N z) : ℂ).re| ≤ ‖inner ℂ z (N z)‖ := Complex.abs_re_le_norm _
    have h2 : ‖inner ℂ z (N z)‖ ≤ ‖z‖ * ‖N z‖ := norm_inner_le_norm _ _
    have h3 : ‖N z‖ ≤ ‖N‖ * ‖z‖ := N.le_opNorm z
    have h4 : |(inner ℂ z (N z) : ℂ).re| ≤ ‖N‖ * ‖z‖ ^ 2 := by
      refine h1.trans (h2.trans ?_)
      calc ‖z‖ * ‖N z‖ ≤ ‖z‖ * (‖N‖ * ‖z‖) := by
            have := norm_nonneg z
            nlinarith
        _ = ‖N‖ * ‖z‖ ^ 2 := by ring
    have := neg_abs_le ((inner ℂ z (N z) : ℂ).re)
    linarith
  nlinarith [hN, hlow, sq_nonneg ‖z‖, hre]

/-- **The complement form bound from a norm perturbation.**  Restricting
`formBound_of_norm_sub_le` to `yᗮ` discharges the hypothesis of section 10. -/
theorem formBound_compressed_of_norm_le (A : F →L[ℂ] F) (hA : IsSelfAdjoint A) {y : F}
    {lam : ℂ} (hy : A y = lam • y) {c b : ℝ}
    (hN : ‖A - (c : ℂ) • 1‖ ≤ c - b) (z : ↥(eigenLine y)ᗮ) :
    b * ‖z‖ ^ 2 ≤ (inner ℂ z (compressed A hA hy z) : ℂ).re := by
  have h := formBound_of_norm_sub_le A hN (z : F)
  simpa only [Submodule.coe_inner, Submodule.coe_norm, compressed_apply_coe] using h

/-- **The separation from a norm perturbation.**  Section 10's `hC` replaced by the norm
measurement `‖A - c • 1‖ ≤ c - b`: no spectral assertion about the complement is left. -/
theorem spectralSeparation_of_norm_le (A : F →L[ℂ] F) (hA : IsSelfAdjoint A) {y : F}
    (hy0 : y ≠ 0) {l b c : ℝ} (hAy : A y = (l : ℂ) • y) (hlb : l ≤ b)
    (hN : ‖A - (c : ℂ) • 1‖ ≤ c - b) :
    BookProof.RitzCertificate.SpectralSeparation A l b :=
  spectralSeparation_of_compressionBound A hA hy0 hAy hlb
    (formBound_compressed_of_norm_le A hA hAy hN)

/-! ## 12. A worked numerical instance

The smallest instance that exhibits the chapter's content.  On `E2 = EuclideanSpace ℂ (Fin 2)`
take `A = 2 • 1 + 3 • P`, with `P` the rank-one projection onto `vTrial`: in the orthonormal
basis `(vTrial, vOther)` this is `diag (5, 2)`, so `vOther` is an eigenvector for `l = 2` and
the compression to its complement is the single eigenvalue `5`.  The separation level `b = 3`
is therefore admissible on `yᗮ` — and inadmissible on the whole space, which is exactly why the
hypothesis is stated on the complement.  The numbers are checked by `norm_num`; the spectral
content is the general theorem, not a computed spectrum. -/

section NumericInstance

/-- The two-dimensional space of the instance. -/
abbrev E2 := EuclideanSpace ℂ (Fin 2)

/-- The trial (certified) eigenvector. -/
noncomputable def vTrial : E2 := EuclideanSpace.single 0 1

/-- The complement direction: the eigenvector `y` whose line is deflated. -/
noncomputable def vOther : E2 := EuclideanSpace.single 1 1

/-- The rank-one projection onto `vTrial`. -/
noncomputable def projT : E2 →L[ℂ] E2 := (innerSL ℂ vTrial).smulRight vTrial

/-- The operator `2 • 1 + 3 • P`, i.e. `diag (5, 2)` in the `(vTrial, vOther)` basis. -/
noncomputable def A2 : E2 →L[ℂ] E2 := (2 : ℂ) • 1 + (3 : ℂ) • projT

@[simp] theorem projT_apply (x : E2) : projT x = (inner ℂ vTrial x : ℂ) • vTrial := rfl

theorem inner_trial_trial : (inner ℂ vTrial vTrial : ℂ) = 1 := by
  rw [inner_self_eq_norm_sq_to_K]
  have h : ‖vTrial‖ = 1 := by simp [vTrial]
  rw [h]
  norm_num

theorem inner_other_other : (inner ℂ vOther vOther : ℂ) = 1 := by
  rw [inner_self_eq_norm_sq_to_K]
  have h : ‖vOther‖ = 1 := by simp [vOther]
  rw [h]
  norm_num

theorem inner_trial_other : (inner ℂ vTrial vOther : ℂ) = 0 := by
  simp [vTrial, vOther, EuclideanSpace.inner_single_left, EuclideanSpace.single_apply]

theorem norm_trial_sq : ‖vTrial‖ ^ 2 = 1 := by simp [vTrial]

theorem norm_other_sq : ‖vOther‖ ^ 2 = 1 := by simp [vOther]

/-- `vOther` is an eigenvector with eigenvalue `2`. -/
theorem A2_other : A2 vOther = (2 : ℂ) • vOther := by
  simp [A2, inner_trial_other]

/-- The compression eigenvalue: `vTrial` is an eigenvector with eigenvalue `5`. -/
theorem A2_trial : A2 vTrial = (5 : ℂ) • vTrial := by
  rw [A2, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.one_apply, projT_apply,
    inner_trial_trial]
  module

/-- The form bound holds on `yᗮ` with `b = 3`: `3 ≤ 5`. -/
theorem bound_on_complement :
    (3 : ℝ) * ‖vTrial‖ ^ 2 ≤ (inner ℂ vTrial (A2 vTrial) : ℂ).re := by
  rw [A2_trial, inner_smul_right, inner_trial_trial, norm_trial_sq]
  norm_num

/-- The same level `b = 3` fails off `yᗮ`: `3 ≰ 2`.  The bound is a statement about the
complement, not about `A`. -/
theorem fails_off_complement :
    ¬ ((3 : ℝ) * ‖vOther‖ ^ 2 ≤ (inner ℂ vOther (A2 vOther) : ℂ).re) := by
  rw [A2_other, inner_smul_right, inner_other_other, norm_other_sq]
  norm_num

end NumericInstance
end BookProof.SpectralSplitting
