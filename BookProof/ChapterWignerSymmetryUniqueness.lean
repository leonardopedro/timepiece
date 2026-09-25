import Mathlib
import BookProof.ChapterWignerSymmetry

/-!
# Wigner's symmetry theorem: the uniqueness clause

`book.tex` quotes Wigner's theorem as: the transformations preserving the modulus of the
inner product are "unitary or anti-unitary operators, **defined up to a complex phase**".
`BookProof.ChapterWignerSymmetry` proves the existence half — a Wigner symmetry of a
complex Hilbert space with a finite orthonormal basis is implemented, up to a phase
depending on the vector, by one unitary or by one antiunitary operator.  This file proves
the two remaining clauses of the quoted statement.

## Results

* `eq_smul_of_forall_eigenvector` — a linear operator for which *every* vector is an
  eigenvector is a scalar;
* **`wigner_unique_unitary`** — two unitaries implementing the same Wigner symmetry differ
  by a single global phase, so the unitary of Wigner's theorem is unique up to a phase;
* `wigner_unique_antiunitary` — the same for two antiunitaries;
* **`not_linear_and_antiunitary`** — as soon as the space contains two orthonormal vectors
  the two alternatives are mutually exclusive: a Wigner symmetry cannot be implemented both
  by a unitary and by an antiunitary operator.  (In dimension one they coincide, so this
  hypothesis is necessary.)

Everything is `sorry`-free and uses only the standard axioms.
-/

open scoped InnerProductSpace ComplexConjugate

namespace BookProof.ChapterWignerSymmetryUniqueness

open BookProof.ChapterWignerSymmetry

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

/-! ## A linear operator all of whose vectors are eigenvectors is a scalar -/

/-- If every vector of `E` is an eigenvector of the linear map `V`, then `V` is a scalar. -/
theorem eq_smul_of_forall_eigenvector (V : E →ₗ[ℂ] E) (h : ∀ x : E, ∃ c : ℂ, V x = c • x) :
    ∃ c : ℂ, ∀ x : E, V x = c • x := by
  classical
  by_cases hE : ∀ x : E, x = 0
  · refine ⟨1, fun x => ?_⟩
    rw [hE x, _root_.map_zero, smul_zero]
  push_neg at hE
  obtain ⟨x₀, hx₀⟩ := hE
  obtain ⟨c₀, hc₀⟩ := h x₀
  refine ⟨c₀, fun x => ?_⟩
  by_cases hx : x = 0
  · rw [hx, _root_.map_zero, smul_zero]
  -- the scalar attached to a nonzero vector is the same for `x` and for `x₀`
  obtain ⟨c, hc⟩ := h x
  suffices hcc : c = c₀ by rw [hc, hcc]
  by_cases hmem : x ∈ Submodule.span ℂ ({x₀} : Set E)
  · -- `x = a • x₀` with `a ≠ 0`
    obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
    have ha0 : a ≠ 0 := by
      intro h0
      apply hx
      rw [← ha, h0, zero_smul]
    have h1 : c • x = c₀ • x := by
      rw [← hc, ← ha, map_smul, hc₀, smul_smul, smul_smul, mul_comm]
    have h2 : (c - c₀) • x = 0 := by
      rw [sub_smul, h1, sub_self]
    rcases smul_eq_zero.1 h2 with h3 | h3
    · exact sub_eq_zero.1 h3
    · exact absurd h3 hx
  · -- `x` and `x₀` are independent; compare the scalars on `x + x₀`
    obtain ⟨c₁, hc₁⟩ := h (x + x₀)
    have hsum : c₁ • x + c₁ • x₀ = c • x + c₀ • x₀ := by
      have := hc₁
      rw [map_add, hc, hc₀, smul_add] at this
      exact this.symm
    have hkey : (c₁ - c) • x = (c₀ - c₁) • x₀ := by
      rw [sub_smul, sub_smul]
      have := hsum
      abel_nf
      try abel_nf at this
      linear_combination (norm := module) this
    have hc1 : c₁ = c := by
      by_contra hne
      apply hmem
      have hinv : x = ((c₀ - c₁) / (c₁ - c)) • x₀ := by
        have hne' : c₁ - c ≠ 0 := sub_ne_zero.2 hne
        rw [div_eq_inv_mul, ← smul_smul, ← hkey, smul_smul, inv_mul_cancel₀ hne', one_smul]
      exact Submodule.mem_span_singleton.2 ⟨(c₀ - c₁) / (c₁ - c), hinv.symm⟩
    have hzero : (c₀ - c₁) • x₀ = 0 := by rw [← hkey, hc1, sub_self, zero_smul]
    rcases smul_eq_zero.1 hzero with h3 | h3
    · rw [← hc1]
      exact (sub_eq_zero.1 h3).symm
    · exact absurd h3 hx₀

/-! ## Uniqueness of the implementing operator -/

variable {T : E → E}

/-- **The unitary of Wigner's theorem is unique up to a global phase.** -/
theorem wigner_unique_unitary {U U' : E ≃ₗᵢ[ℂ] E}
    (hU : ∀ x, ∃ lam : ℂ, ‖lam‖ = 1 ∧ T x = lam • U x)
    (hU' : ∀ x, ∃ lam : ℂ, ‖lam‖ = 1 ∧ T x = lam • U' x) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ x, U' x = c • U x := by
  by_cases hE : ∀ x : E, x = 0
  · refine ⟨1, by simp, fun x => ?_⟩
    rw [hE x]
    simp
  push_neg at hE
  -- pointwise the two unitaries differ by a phase
  have hpt : ∀ x : E, ∃ mu : ℂ, ‖mu‖ = 1 ∧ U' x = mu • U x := by
    intro x
    obtain ⟨lam, hlam, hx⟩ := hU x
    obtain ⟨lam', hlam', hx'⟩ := hU' x
    have hlam'0 : lam' ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hlam'
      exact zero_ne_one hlam'
    refine ⟨lam / lam', ?_, ?_⟩
    · rw [norm_div, hlam, hlam', div_one]
    · have hxx : lam' • U' x = lam • U x := by rw [← hx', hx]
      rw [div_eq_inv_mul, ← smul_smul, ← hxx, smul_smul, inv_mul_cancel₀ hlam'0, one_smul]
  -- hence `U⁻¹ ∘ U'` is a linear map of which every vector is an eigenvector
  have hVeig : ∀ x : E, ∃ c : ℂ, (U'.trans U.symm).toLinearEquiv.toLinearMap x = c • x := by
    intro x
    obtain ⟨mu, _, hmu⟩ := hpt x
    refine ⟨mu, ?_⟩
    change U.symm (U' x) = mu • x
    rw [hmu, map_smul, U.symm_apply_apply]
  obtain ⟨c, hc⟩ :=
    eq_smul_of_forall_eigenvector (U'.trans U.symm).toLinearEquiv.toLinearMap hVeig
  have hUc : ∀ x : E, U' x = c • U x := by
    intro x
    have hcx : U.symm (U' x) = c • x := hc x
    have := congrArg U hcx
    rwa [U.apply_symm_apply, map_smul] at this
  obtain ⟨x, hx⟩ := hE
  refine ⟨c, ?_, hUc⟩
  have hnorm : ‖U' x‖ = ‖c‖ * ‖U x‖ := by rw [hUc x, norm_smul]
  rw [U'.norm_map, U.norm_map] at hnorm
  have hxne : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  field_simp at hnorm
  exact hnorm.symm

/-! ## Uniqueness in the antiunitary case -/

/-- An antiunitary operator preserves norms. -/
theorem antiunitary_norm_map {U : E → E} (hU : IsAntiunitary U) (x : E) : ‖U x‖ = ‖x‖ := by
  have h := hU.inner_conj x x
  rw [inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K] at h
  have h2 : ‖U x‖ ^ 2 = ‖x‖ ^ 2 := by
    simp only [map_pow, RCLike.conj_ofReal] at h
    exact_mod_cast h
  nlinarith [norm_nonneg (U x), norm_nonneg x]

/-- An antiunitary operator is injective. -/
theorem antiunitary_injective {U : E → E} (hU : IsAntiunitary U) : Function.Injective U := by
  intro x y hxy
  have hsub : U (x - y) = U x - U y := by
    have hadd := hU.map_add (x - y) y
    rw [sub_add_cancel] at hadd
    rw [hadd]
    abel
  have hz : ‖x - y‖ = 0 := by
    rw [← antiunitary_norm_map hU (x - y), hsub, hxy, sub_self, norm_zero]
  exact sub_eq_zero.mp (norm_eq_zero.mp hz)

/-- **The antiunitary of Wigner's theorem is unique up to a global phase.** -/
theorem wigner_unique_antiunitary {U U' : E → E} (hU0 : IsAntiunitary U)
    (hU0' : IsAntiunitary U')
    (hU : ∀ x, ∃ lam : ℂ, ‖lam‖ = 1 ∧ T x = lam • U x)
    (hU' : ∀ x, ∃ lam : ℂ, ‖lam‖ = 1 ∧ T x = lam • U' x) :
    ∃ c : ℂ, ‖c‖ = 1 ∧ ∀ x, U' x = c • U x := by
  by_cases hE : ∀ x : E, x = 0
  · refine ⟨1, by simp, fun x => ?_⟩
    have hU'0 : U' (0 : E) = 0 := by
      have hadd := hU0'.map_add 0 0
      simpa using hadd.symm
    have hU00 : U (0 : E) = 0 := by
      have hadd := hU0.map_add 0 0
      simpa using hadd.symm
    rw [hE x, hU'0, hU00, smul_zero]
  push_neg at hE
  -- pointwise phases
  have hpt : ∀ x : E, ∃ mu : ℂ, ‖mu‖ = 1 ∧ U' x = mu • U x := by
    intro x
    obtain ⟨lam, hlam, hx⟩ := hU x
    obtain ⟨lam', hlam', hx'⟩ := hU' x
    have hlam'0 : lam' ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hlam'
      exact zero_ne_one hlam'
    refine ⟨lam / lam', by rw [norm_div, hlam, hlam', div_one], ?_⟩
    have hxx : lam' • U' x = lam • U x := by rw [← hx', hx]
    rw [div_eq_inv_mul, ← smul_smul, ← hxx, smul_smul, inv_mul_cancel₀ hlam'0, one_smul]
  -- `U` is bijective, so `U' ∘ U⁻¹` is a linear map of which every vector is an eigenvector
  have hbij : Function.Bijective U := ⟨antiunitary_injective hU0, hU0.surjective⟩
  set g : E ≃ E := Equiv.ofBijective U hbij with hg
  have hgU : ∀ y : E, g.symm (U y) = y := fun y => g.symm_apply_apply y
  have hUg : ∀ x : E, U (g.symm x) = x := fun x => g.apply_symm_apply x
  have hgadd : ∀ x y : E, g.symm (x + y) = g.symm x + g.symm y := by
    intro x y
    refine antiunitary_injective hU0 ?_
    rw [hUg, hU0.map_add, hUg, hUg]
  have hgsmul : ∀ (a : ℂ) (x : E), g.symm (a • x) = conj a • g.symm x := by
    intro a x
    refine antiunitary_injective hU0 ?_
    rw [hUg, hU0.map_smul, hUg, Complex.conj_conj]
  set V : E →ₗ[ℂ] E :=
    { toFun := fun x => U' (g.symm x)
      map_add' := by
        intro x y
        rw [hgadd, hU0'.map_add]
      map_smul' := by
        intro a x
        rw [hgsmul, hU0'.map_smul, Complex.conj_conj]
        rfl } with hV
  have hVapp : ∀ x : E, V x = U' (g.symm x) := fun _ => rfl
  have hVeig : ∀ x : E, ∃ c : ℂ, V x = c • x := by
    intro x
    obtain ⟨mu, _, hmu⟩ := hpt (g.symm x)
    refine ⟨mu, ?_⟩
    rw [hVapp, hmu, hUg]
  obtain ⟨c, hc⟩ := eq_smul_of_forall_eigenvector V hVeig
  have hUc : ∀ y : E, U' y = c • U y := by
    intro y
    have hcy := hc (U y)
    rw [hVapp, hgU] at hcy
    exact hcy
  obtain ⟨x, hx⟩ := hE
  refine ⟨c, ?_, hUc⟩
  have hnorm : ‖U' x‖ = ‖c‖ * ‖U x‖ := by rw [hUc x, norm_smul]
  rw [antiunitary_norm_map hU0' x, antiunitary_norm_map hU0 x] at hnorm
  have hxne : ‖x‖ ≠ 0 := norm_ne_zero_iff.2 hx
  field_simp at hnorm
  exact hnorm.symm

/-! ## The two alternatives exclude each other -/

/-- **A Wigner symmetry cannot be implemented both by a unitary and by an antiunitary
operator**, as soon as the space contains two orthonormal vectors.  (In dimension one the
two notions coincide, so the hypothesis is necessary.) -/
theorem not_linear_and_antiunitary {U : E ≃ₗᵢ[ℂ] E} {U' : E → E} (hanti : IsAntiunitary U')
    (hU : ∀ x, ∃ lam : ℂ, ‖lam‖ = 1 ∧ T x = lam • U x)
    (hU' : ∀ x, ∃ lam : ℂ, ‖lam‖ = 1 ∧ T x = lam • U' x)
    {e f : E} (he : ‖e‖ = 1) (hf : ‖f‖ = 1) (hef : ⟪e, f⟫_ℂ = 0) : False := by
  -- the composite `W = U⁻¹ ∘ U'` is conjugate-linear and multiplies every vector by a phase
  set W : E → E := fun x => U.symm (U' x) with hW
  have hWadd : ∀ x y, W (x + y) = W x + W y := by
    intro x y
    rw [hW]
    simp [hanti.map_add, map_add]
  have hWsmul : ∀ (a : ℂ) (x : E), W (a • x) = conj a • W x := by
    intro a x
    rw [hW]
    simp [hanti.map_smul, map_smul]
  have hpt : ∀ x : E, ∃ mu : ℂ, ‖mu‖ = 1 ∧ W x = mu • x := by
    intro x
    obtain ⟨lam, hlam, hx⟩ := hU x
    obtain ⟨lam', hlam', hx'⟩ := hU' x
    have hlam'0 : lam' ≠ 0 := by
      intro h0
      rw [h0, norm_zero] at hlam'
      exact zero_ne_one hlam'
    refine ⟨lam / lam', by rw [norm_div, hlam, hlam', div_one], ?_⟩
    have hxx : lam' • U' x = lam • U x := by rw [← hx', hx]
    have hUx : U' x = (lam / lam') • U x := by
      rw [div_eq_inv_mul, ← smul_smul, ← hxx, smul_smul, inv_mul_cancel₀ hlam'0, one_smul]
    change U.symm (U' x) = (lam / lam') • x
    rw [hUx, map_smul, U.symm_apply_apply]
  -- the two orthonormal vectors and the coefficient extraction
  have hee : ⟪e, e⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, he]
    norm_num
  have hff : ⟪f, f⟫_ℂ = 1 := by
    rw [inner_self_eq_norm_sq_to_K, hf]
    norm_num
  have hfe : ⟪f, e⟫_ℂ = 0 := inner_eq_zero_symm.mp hef
  have hcoeff : ∀ p q : ℂ, p • e + q • f = 0 → p = 0 ∧ q = 0 := by
    intro p q hpq
    constructor
    · have h1 : ⟪e, p • e + q • f⟫_ℂ = 0 := by rw [hpq, inner_zero_right]
      rw [inner_add_right, inner_smul_right, inner_smul_right, hee, hef] at h1
      simpa using h1
    · have h2 : ⟪f, p • e + q • f⟫_ℂ = 0 := by rw [hpq, inner_zero_right]
      rw [inner_add_right, inner_smul_right, inner_smul_right, hfe, hff] at h2
      simpa using h2
  obtain ⟨a, ha1, hae⟩ := hpt e
  obtain ⟨b, _, hbf⟩ := hpt f
  obtain ⟨s, _, hsum⟩ := hpt (e + f)
  obtain ⟨r, _, hr⟩ := hpt (e + Complex.I • f)
  -- the real combination forces `a = b = s`
  have hadd : W (e + f) = a • e + b • f := by rw [hWadd, hae, hbf]
  have h3 : (s - a) • e + (s - b) • f = 0 := by
    have heq : s • e + s • f = a • e + b • f := by rw [← smul_add, ← hsum, hadd]
    linear_combination (norm := module) heq
  obtain ⟨h3a, h3b⟩ := hcoeff _ _ h3
  have hsa : s = a := sub_eq_zero.mp h3a
  have hsb : s = b := sub_eq_zero.mp h3b
  -- the imaginary combination forces `a = 0`
  have hadd2 : W (e + Complex.I • f) = a • e + (-Complex.I * b) • f := by
    rw [hWadd, hWsmul, hae, hbf, smul_smul, Complex.conj_I]
  have h4 : (r - a) • e + (r * Complex.I - (-Complex.I * b)) • f = 0 := by
    have heq : r • e + (r * Complex.I) • f = a • e + (-Complex.I * b) • f := by
      rw [← hadd2, hr, smul_add, smul_smul]
    linear_combination (norm := module) heq
  obtain ⟨h4a, h4b⟩ := hcoeff _ _ h4
  have hra : r = a := sub_eq_zero.mp h4a
  have hzero : a = 0 := by
    have hb : b = a := by rw [← hsb, hsa]
    rw [hra, hb] at h4b
    have h2a : (2 * Complex.I) * a = 0 := by linear_combination h4b
    have hI : (2 : ℂ) * Complex.I ≠ 0 := by
      simp [Complex.I_ne_zero]
    exact (mul_eq_zero.mp h2a).resolve_left hI
  rw [hzero, norm_zero] at ha1
  exact zero_ne_one ha1

end BookProof.ChapterWignerSymmetryUniqueness
