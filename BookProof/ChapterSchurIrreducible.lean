import Mathlib
import BookProof.ChapterA
import BookProof.ChapterA2
import BookProof.ChapterA2b

/-!
# Schur's lemma for irreducible normal systems on an arbitrary complex Hilbert space

Source: `book.tex`, chapter *"Real representations, CPT theorem and the relativistic
position operator"*, §*Systems on real and complex Hilbert spaces* and §*Schur systems*
(Def 13, Lemma 28: "Schur's lemma for unitary representations").

`BookProof.ChapterA2b` introduces the **full Schur property**

```
IsSchurFull M : ∀ S : V →L[ℂ] V, M.Commutes S → ∃ c : ℂ, S = c • 1
```

and `BookProof.ChapterA2` the unitary variant `IsSchurUnitary`.  Both were introduced as
*named hypotheses*, because Schur's lemma for unitary representations on a possibly
infinite-dimensional Hilbert space is not available in Mathlib;
`BookProof.ChapterSchurFullFiniteDim` discharges them only in **finite** dimension, where
an eigenvalue exists.

This file discharges them in **full generality**: for a *normal* system (a set of bounded
operators closed under the adjoint — Def 24) which is *topologically irreducible*
(Def 7), every bounded operator commuting with the system is a complex scalar.  The proof
uses no eigenvalues; it uses only the **continuous functional calculus** of a bounded
self-adjoint operator:

* if a self-adjoint `T` in the commutant had two distinct spectral points `p < q`, then
  with `f x = max 0 (mid - x)`, `g x = max 0 (x - mid)` (`mid` the midpoint) the operators
  `F = f(T)`, `G = g(T)` are nonzero (their spectra are `f '' spectrum T ∋ f p ≠ 0`,
  resp. `g '' spectrum T ∋ g q ≠ 0`), satisfy `G * F = 0`, and lie in the commutant of
  everything commuting with `T`;
* hence the closure of the range of `F` is a **closed invariant subspace** which is
  nonzero (as `F ≠ 0`) and proper (it lies in `ker G ≠ ⊤`), contradicting irreducibility;
* so the spectrum of `T` is a single point `c` and the functional calculus gives
  `T = c • 1` directly (`cfc_congr` against the constant function);
* a general commuting operator splits as `S = A + i B` with `A = (S + S*)/2`,
  `B = (S - S*)/(2i)` self-adjoint; normality of the system makes `S*` commute with it
  too, so both parts are real scalars and `S` is a complex scalar.

## Main results

* `spectrum_subsingleton_of_irreducible` — the spectrum of a self-adjoint operator in the
  commutant of an irreducible system is a subsingleton.
* `selfAdjoint_commutant_scalar` — such an operator is a real scalar.
* `commutant_scalar_of_irreducible` — **Schur's lemma**: every bounded operator commuting
  with an irreducible normal system is a complex scalar.
* `isSchurFull_of_irreducible`, `isSchurUnitary_of_irreducible` — the two `EXTERNAL`
  hypotheses of `ChapterA2` / `ChapterA2b`, now *theorems*, with no dimension restriction.
* `commutant_eq_scalars_of_irreducible` — the commutant of an irreducible normal system is
  exactly `ℂ · 1`; `isNormal_and_irreducible_iff_schur` records the converse direction
  (the book's Lemma 27, `ChapterA.System.schur_normal_irreducible`).
-/

open scoped ComplexConjugate InnerProductSpace

namespace BookProof.ChapterSchurIrreducible

open BookProof.ChapterA BookProof.ChapterA.System

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-! ## The closure of a range as a closed invariant subspace -/

/-- The closure of the range of a bounded operator, as a closed subspace. -/
noncomputable def rangeClosure (F : V →L[ℂ] V) : Submodule ℂ V :=
  (LinearMap.range (F : V →ₗ[ℂ] V)).topologicalClosure

omit [CompleteSpace V] in
theorem isClosed_rangeClosure (F : V →L[ℂ] V) :
    IsClosed ((rangeClosure F : Submodule ℂ V) : Set V) :=
  Submodule.isClosed_topologicalClosure _

omit [CompleteSpace V] in
theorem mem_rangeClosure (F : V →L[ℂ] V) (x : V) : F x ∈ rangeClosure F :=
  Submodule.le_topologicalClosure _ ⟨x, rfl⟩

omit [CompleteSpace V] in
/-- If `m` commutes with `F`, the closure of the range of `F` is invariant under `m`. -/
theorem rangeClosure_invariant {F m : V →L[ℂ] V} (hc : Commute F m) {w : V}
    (hw : w ∈ rangeClosure F) : m w ∈ rangeClosure F := by
  have hle : (LinearMap.range (F : V →ₗ[ℂ] V)) ≤
      Submodule.comap (m : V →ₗ[ℂ] V) (rangeClosure F) := by
    rintro _ ⟨x, rfl⟩
    refine Submodule.le_topologicalClosure _ ?_
    exact ⟨m x, by
      have := congrArg (fun T : V →L[ℂ] V => T x) hc
      simpa [ContinuousLinearMap.mul_apply] using this⟩
  have hclosed : IsClosed
      ((Submodule.comap (m : V →ₗ[ℂ] V) (rangeClosure F) : Submodule ℂ V) : Set V) :=
    IsClosed.preimage m.continuous (isClosed_rangeClosure F)
  exact Submodule.topologicalClosure_minimal _ hle hclosed hw

omit [CompleteSpace V] in
theorem rangeClosure_ne_bot {F : V →L[ℂ] V} (hF : F ≠ 0) : rangeClosure F ≠ ⊥ := by
  intro h
  apply hF
  ext x
  have : F x ∈ rangeClosure F := mem_rangeClosure F x
  rw [h, Submodule.mem_bot] at this
  simp [this]

omit [CompleteSpace V] in
/-- If `G * F = 0` then the closure of the range of `F` lies in the kernel of `G`. -/
theorem rangeClosure_le_ker {F G : V →L[ℂ] V} (h : G * F = 0) :
    rangeClosure F ≤ LinearMap.ker (G : V →ₗ[ℂ] V) := by
  refine Submodule.topologicalClosure_minimal _ ?_ ?_
  · rintro _ ⟨x, rfl⟩
    have := congrArg (fun T : V →L[ℂ] V => T x) h
    simpa [ContinuousLinearMap.mul_apply] using this
  · exact (ContinuousLinearMap.isClosed_ker G).preimage continuous_id

omit [CompleteSpace V] in
theorem rangeClosure_ne_top {F G : V →L[ℂ] V} (hG : G ≠ 0) (h : G * F = 0) :
    rangeClosure F ≠ ⊤ := by
  intro htop
  apply hG
  ext x
  have hx : x ∈ rangeClosure F := by rw [htop]; trivial
  have := rangeClosure_le_ker h hx
  simpa using this

/-! ## The functional calculus of a commuting self-adjoint operator -/

/-- A continuous function of a self-adjoint operator is nonzero as soon as the function is
nonzero at some spectral point (its spectrum is the image of the spectrum). -/
theorem cfc_ne_zero_of_mem_spectrum [Nontrivial V] {T : V →L[ℂ] V} (hT : IsSelfAdjoint T)
    {f : ℝ → ℝ} (hf : Continuous f) {p : ℝ} (hp : p ∈ spectrum ℝ T) (hfp : f p ≠ 0) :
    cfc f T ≠ 0 := by
  intro h
  have hs : spectrum ℝ (cfc f T) = f '' spectrum ℝ T := cfc_map_spectrum f T
  rw [h, spectrum.zero_eq] at hs
  have : f p ∈ ({0} : Set ℝ) := by rw [hs]; exact ⟨p, hp, rfl⟩
  exact hfp this

/-- **Key step.**  The spectrum of a self-adjoint operator commuting with an irreducible
system is a subsingleton: two distinct spectral points would produce a nonzero proper
closed invariant subspace. -/
theorem spectrum_subsingleton_of_irreducible [Nontrivial V] (M : System ℂ V)
    (hirr : M.IsIrreducible) {T : V →L[ℂ] V} (hT : IsSelfAdjoint T) (hcomm : M.Commutes T)
    {a b : ℝ} (ha : a ∈ spectrum ℝ T) (hb : b ∈ spectrum ℝ T) : a = b := by
  by_contra hab
  -- Order the two spectral points.
  set p := min a b with hp_def
  set q := max a b with hq_def
  have hp : p ∈ spectrum ℝ T := by
    rcases min_cases a b with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [hp_def, h] <;> assumption
  have hq : q ∈ spectrum ℝ T := by
    rcases max_cases a b with ⟨h, _⟩ | ⟨h, _⟩ <;> rw [hq_def, h] <;> assumption
  have hpq : p < q := lt_of_le_of_ne (min_le_max) (by
    intro h
    rcases le_total a b with hle | hle
    · rw [hp_def, hq_def, min_eq_left hle, max_eq_right hle] at h; exact hab h
    · rw [hp_def, hq_def, min_eq_right hle, max_eq_left hle] at h; exact hab h.symm)
  set mid : ℝ := (p + q) / 2 with hmid
  have hpmid : p < mid := by rw [hmid]; linarith
  have hmidq : mid < q := by rw [hmid]; linarith
  set f : ℝ → ℝ := fun x => max 0 (mid - x) with hf_def
  set g : ℝ → ℝ := fun x => max 0 (x - mid) with hg_def
  have hfc : Continuous f := continuous_const.max (continuous_const.sub continuous_id)
  have hgc : Continuous g := continuous_const.max (continuous_id.sub continuous_const)
  have hfp : f p ≠ 0 := by
    rw [hf_def]
    simp only [ne_eq, max_eq_left_iff, not_le]
    linarith
  have hgq : g q ≠ 0 := by
    rw [hg_def]
    simp only [ne_eq, max_eq_left_iff, not_le]
    linarith
  set F : V →L[ℂ] V := cfc f T with hF_def
  set G : V →L[ℂ] V := cfc g T with hG_def
  have hF : F ≠ 0 := cfc_ne_zero_of_mem_spectrum hT hfc hp hfp
  have hG : G ≠ 0 := cfc_ne_zero_of_mem_spectrum hT hgc hq hgq
  -- The two functions have disjoint support, so the operators annihilate each other.
  have hGF : G * F = 0 := by
    have hzero : (fun x : ℝ => g x * f x) = fun _ : ℝ => (0 : ℝ) := by
      funext x
      rcases le_total x mid with hx | hx
      · have : g x = 0 := by rw [hg_def]; simp only [max_eq_left_iff]; linarith
        rw [this, zero_mul]
      · have : f x = 0 := by rw [hf_def]; simp only [max_eq_left_iff]; linarith
        rw [this, mul_zero]
    have := cfc_mul g f T (hgc.continuousOn) (hfc.continuousOn)
    rw [hzero] at this
    rw [hG_def, hF_def, ← this, cfc_const (0 : ℝ) T, map_zero]
  -- The closure of the range of `F` is a closed invariant subspace.
  have hsub : M.IsSubsystem (rangeClosure F) := by
    refine ⟨isClosed_rangeClosure F, ?_⟩
    intro m hm w hw
    have hcm : Commute T m := hcomm m hm
    have : Commute (cfc f T) m := hT.commute_cfc (𝕜 := ℝ) hcm f
    exact rangeClosure_invariant (F := F) this hw
  rcases hirr _ hsub with h | h
  · exact rangeClosure_ne_bot hF h
  · exact rangeClosure_ne_top hG hGF h

/-! ## Schur's lemma -/

/-- A self-adjoint operator commuting with an irreducible system is a **real** scalar. -/
theorem selfAdjoint_commutant_scalar (M : System ℂ V) (hirr : M.IsIrreducible)
    {T : V →L[ℂ] V} (hT : IsSelfAdjoint T) (hcomm : M.Commutes T) :
    ∃ c : ℝ, T = (c : ℂ) • (1 : V →L[ℂ] V) := by
  by_cases hV : Nontrivial V
  · -- Pick the (unique) spectral value, or `0` if the spectrum is empty.
    classical
    by_cases hne : (spectrum ℝ T).Nonempty
    · obtain ⟨c, hc⟩ := hne
      refine ⟨c, ?_⟩
      have hall : ∀ x ∈ spectrum ℝ T, x = c := fun x hx =>
        spectrum_subsingleton_of_irreducible M hirr hT hcomm hx hc
      have h1 : cfc (fun x : ℝ => x) T = T := cfc_id ℝ T
      rw [← h1, cfc_congr (g := fun _ => c) (fun x hx => hall x hx), cfc_const c T]
      simp [Algebra.algebraMap_eq_smul_one]
    · refine ⟨0, ?_⟩
      have hall : ∀ x ∈ spectrum ℝ T, x = (0 : ℝ) := by
        intro x hx; exact absurd ⟨x, hx⟩ hne
      have h1 : cfc (fun x : ℝ => x) T = T := cfc_id ℝ T
      rw [← h1, cfc_congr (g := fun _ => (0 : ℝ)) (fun x hx => hall x hx), cfc_const (0 : ℝ) T]
      simp
  · refine ⟨0, ?_⟩
    have : Subsingleton V := not_nontrivial_iff_subsingleton.mp hV
    ext x
    exact Subsingleton.elim _ _

/-- **Schur's lemma, general Hilbert-space form.**  Every bounded operator commuting with
a topologically irreducible *normal* system on a complex Hilbert space is a complex
scalar.  No finite-dimensionality is assumed. -/
theorem commutant_scalar_of_irreducible (M : System ℂ V) (hM : M.IsNormal)
    (hirr : M.IsIrreducible) {S : V →L[ℂ] V} (hcomm : M.Commutes S) :
    ∃ c : ℂ, S = c • (1 : V →L[ℂ] V) := by
  -- The adjoint of `S` also commutes with the system, by normality.
  have hstar : M.Commutes (star S) := by
    intro m hm
    have hm' : ContinuousLinearMap.adjoint m ∈ M.ops := hM m hm
    have h := hcomm _ hm'
    have := congrArg (fun T : V →L[ℂ] V => star T) h
    simpa [star_mul, ContinuousLinearMap.star_eq_adjoint, eq_comm] using this
  set A : V →L[ℂ] V := (2 : ℂ)⁻¹ • (S + star S) with hA
  set B : V →L[ℂ] V := ((2 : ℂ) * Complex.I)⁻¹ • (S - star S) with hB
  have hAsa : IsSelfAdjoint A := by
    have : star A = A := by
      rw [hA, star_smul, star_add, star_star]
      simp [add_comm]
    exact this
  have hBsa : IsSelfAdjoint B := by
    have : star B = B := by
      rw [hB, star_smul, star_sub, star_star]
      rw [show star ((2 : ℂ) * Complex.I)⁻¹ = -((2 : ℂ) * Complex.I)⁻¹ by
        simp]
      module
    exact this
  have hAcomm : M.Commutes A := by
    intro m hm
    have h1 := hcomm m hm
    have h2 := hstar m hm
    rw [hA]
    simp only [smul_mul_assoc, mul_smul_comm, add_mul, mul_add, h1, h2]
  have hBcomm : M.Commutes B := by
    intro m hm
    have h1 := hcomm m hm
    have h2 := hstar m hm
    rw [hB]
    simp only [smul_mul_assoc, mul_smul_comm, sub_mul, mul_sub, h1, h2]
  obtain ⟨a, ha⟩ := selfAdjoint_commutant_scalar M hirr hAsa hAcomm
  obtain ⟨b, hb⟩ := selfAdjoint_commutant_scalar M hirr hBsa hBcomm
  refine ⟨(a : ℂ) + Complex.I * (b : ℂ), ?_⟩
  have hS : S = A + Complex.I • B := by
    rw [hA, hB]
    have hI : Complex.I ≠ 0 := Complex.I_ne_zero
    have h2 : (2 : ℂ) ≠ 0 := two_ne_zero
    rw [smul_smul]
    rw [show Complex.I * ((2 : ℂ) * Complex.I)⁻¹ = (2 : ℂ)⁻¹ by
      field_simp]
    module
  rw [hS, ha, hb, smul_smul, add_smul, mul_smul]

/-- The `EXTERNAL` hypothesis `IsSchurFull` of `ChapterA2b`, proved for every irreducible
normal system on a complex Hilbert space (no dimension restriction). -/
theorem isSchurFull_of_irreducible (M : System ℂ V) (hM : M.IsNormal)
    (hirr : M.IsIrreducible) : IsSchurFull M :=
  fun _ hS => commutant_scalar_of_irreducible M hM hirr hS

/-- The commutant of an irreducible normal system is exactly the complex scalars. -/
theorem commutant_eq_scalars_of_irreducible (M : System ℂ V) (hM : M.IsNormal)
    (hirr : M.IsIrreducible) (S : V →L[ℂ] V) :
    M.Commutes S ↔ ∃ c : ℂ, S = c • (1 : V →L[ℂ] V) :=
  commutant_eq_complex_scalars M (isSchurFull_of_irreducible M hM hirr) S

/-- The `EXTERNAL` hypothesis `IsSchurUnitary` of `ChapterA2`, proved for every irreducible
normal system on a nonzero complex Hilbert space: a unitary commuting with the system is
multiplication by a scalar of modulus one. -/
theorem isSchurUnitary_of_irreducible [Nontrivial V] (M : System ℂ V) (hM : M.IsNormal)
    (hirr : M.IsIrreducible) : IsSchurUnitary M := by
  intro g hg
  set S : V →L[ℂ] V := g.toContinuousLinearEquiv.toContinuousLinearMap with hS
  have hSapp : ∀ x, S x = g x := fun _ => rfl
  have hcomm : M.Commutes S := by
    intro m hm
    ext x
    simp only [ContinuousLinearMap.coe_mul, Function.comp_apply, hSapp]
    exact hg m hm x
  obtain ⟨c, hc⟩ := commutant_scalar_of_irreducible M hM hirr hcomm
  have hcx : ∀ x, g x = c • x := by
    intro x
    have := congrArg (fun T : V →L[ℂ] V => T x) hc
    simpa [hSapp] using this
  refine ⟨c, ?_, hcx⟩
  obtain ⟨x, hx⟩ := exists_ne (0 : V)
  have hnorm : ‖g x‖ = ‖x‖ := g.norm_map x
  rw [hcx x, norm_smul] at hnorm
  have hxn : ‖x‖ ≠ 0 := by simpa using hx
  field_simp at hnorm
  exact hnorm

/-- **Irreducible = Schur, for a normal system.**  Combining the theorem above with the
book's Lemma 27 (`ChapterA.System.schur_normal_irreducible`): a normal system on a complex
Hilbert space is topologically irreducible **iff** every self-adjoint operator commuting
with it is a scalar — the Schur property of Def 13. -/
theorem isIrreducible_iff_schur (M : System ℂ V) (hM : M.IsNormal) :
    M.IsIrreducible ↔
      ∀ S : V →L[ℂ] V, M.Commutes S → IsSelfAdjoint S → ∃ c : ℂ, S = c • (1 : V →L[ℂ] V) := by
  constructor
  · intro hirr S hS hsa
    obtain ⟨r, hr⟩ := selfAdjoint_commutant_scalar M hirr hsa hS
    exact ⟨(r : ℂ), hr⟩
  · intro hSchur
    exact System.schur_normal_irreducible M hM hSchur

end BookProof.ChapterSchurIrreducible
