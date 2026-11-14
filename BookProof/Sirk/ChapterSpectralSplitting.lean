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
* **the spectrum union** `spectrum A ⊆ spectrum (A ∘ Q) ∪ {l}`.  mathlib has no
  block-spectrum lemma, but none is needed: because `A = l • P + A ∘ Q` and
  `(A ∘ Q) ∘ P = 0`, the identity `t • 1 − A = (t • 1 − A ∘ Q)(1 − (l/t) • P)` writes
  `t • 1 − A` as a product of units for every `t` in the resolvent of the deflation with
  `t ≠ l`, and the second factor `1 − (l/t) • P` is inverted by `1 + (l/(t−l)) • P`.
  Accordingly `spectralSeparation_of_complementBound` derives
  `SpectralSeparation A l b` from a lower bound on the spectrum of `A ∘ Q`, and
  `ChapterResolventTransfer.sirk_reflected_gap_certificate_of_deflated` is the certificate
  with `hsep` replaced by that hypothesis.

What is *not* here is the step from a bound on the *form* of `A ∘ Q` (section 5) to the
bound on its *spectrum* that the union consumes: that is min–max at `k = 1`, which
`ChapterSirkRitzMinMax` records as open (only `k = 0` is identified).  So the input is now
"the deflated operator is bounded below", not "`A` is separated at `l`", but the two are
not yet interchangeable.
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
operator left after the certified eigenvector is removed. -/
theorem spectralSeparation_of_complementBound (A : F →L[ℂ] F)
    {y : F} (hy : y ≠ 0) {l b : ℝ} (hAy : A y = (l : ℂ) • y) (hlb : l ≤ b)
    (hD : ∀ t ∈ spectrum ℝ (deflated A y), b ≤ t) :
    BookProof.RitzCertificate.SpectralSeparation A l b := by
  refine ⟨hlb, fun t ht => ?_⟩
  rcases spectrum_subset_union_deflated A hy hAy ht with h | h
  · exact Or.inr (hD t h)
  · exact Or.inl (Set.mem_singleton_iff.mp h)

end BookProof.SpectralSplitting
