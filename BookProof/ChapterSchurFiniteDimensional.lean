import Mathlib
import BookProof.ChapterA2b

/-!
# Schur's lemma in finite dimension, and the real / pseudoreal dichotomy

Source: `book.tex`, chapter *"Real representations, CPT theorem and the relativistic
position operator"*, §"Finite-dimensional representations": **Lemma 20** (Schur's lemma for
finite-dimensional representations) and the core of **Lemma 21** (an anti-isomorphism of an
irreducible finite-dimensional complex system squares to a real scalar).

`BookProof.ChapterSchurIrreducible` proves Schur's lemma for a topologically irreducible
**normal** system on a complex Hilbert space (the hypothesis `Def 24` of the book), which is
what the infinite-dimensional chapters need.  In finite dimension the book states the lemma
with **no** normality hypothesis, and the proof is the eigenvalue argument rather than the
spectral one.  This file supplies that version, so that Props 17–19 of `ChapterA2b` and
`ChapterA2c` — whose hypotheses are `IsSchurFull` / `IsSchurUnitary` — apply to *every*
irreducible finite-dimensional complex system, normal or not.

## Results

* **`isSchurFull_of_irreducible_finiteDimensional` (Lemma 20)** — for an irreducible system
  on a nonzero finite-dimensional complex Hilbert space, every bounded operator commuting
  with the system is a complex scalar.  The proof: a commuting operator has an eigenvalue
  `c`, and `ker (S − c)` is a nonzero subsystem, hence everything.
* `isSchurUnitary_of_irreducible_finiteDimensional` — the unitary form of the same statement.
* **`antiUnitary_sq_of_irreducible_finiteDimensional` (Lemma 21, core)** — an anti-unitary
  commuting with such a system satisfies `θ² = 1` or `θ² = −1`: the real / pseudoreal
  dichotomy.  `θ²` is a commuting complex-linear isometry, hence a scalar `c` of modulus one
  by Lemma 20; conjugating `θ` past it forces `c` to be real.
* `isConjugation_or_sq_eq_neg_one` — the same statement in the book's vocabulary: either `θ`
  is a C-conjugation (`IsConjugation`, Def 8.1) of the system, or it is a pseudoreal
  structure `θ² = −1`.

Everything is `sorry`-free and uses only the standard axioms.
-/

open scoped ComplexConjugate InnerProductSpace

namespace BookProof.ChapterSchurFiniteDimensional

open BookProof.ChapterA BookProof.ChapterA.System

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℂ V] [CompleteSpace V]

/-! ## Lemma 20 — Schur's lemma in finite dimension -/

/-- **Lemma 20.**  On a nonzero finite-dimensional complex Hilbert space, every bounded
operator commuting with an irreducible system is a complex scalar.  No normality hypothesis
is needed. -/
theorem isSchurFull_of_irreducible_finiteDimensional [FiniteDimensional ℂ V] [Nontrivial V]
    (M : System ℂ V) (hirr : M.IsIrreducible) : IsSchurFull M := by
  intro S hS
  obtain ⟨c, hc⟩ := Module.End.exists_eigenvalue (S : V →ₗ[ℂ] V)
  set W : Submodule ℂ V := LinearMap.ker ((S : V →ₗ[ℂ] V) - c • LinearMap.id) with hW
  have hmemW : ∀ v : V, v ∈ W ↔ S v = c • v := by
    intro v
    simp only [hW, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply, sub_eq_zero]
    rfl
  have hWne : W ≠ ⊥ := by
    obtain ⟨v, hv, hv0⟩ := hc.exists_hasEigenvector
    intro hbot
    apply hv0
    have hvW : v ∈ W := (hmemW v).mpr (by simpa [Module.End.mem_eigenspace_iff] using hv)
    rw [hbot] at hvW
    simpa using hvW
  have hsub : M.IsSubsystem W := by
    refine ⟨W.closed_of_finiteDimensional, ?_⟩
    intro m hm w hw
    have hw' : S w = c • w := (hmemW w).mp hw
    refine (hmemW (m w)).mpr ?_
    have hcomm : S * m = m * S := hS m hm
    have h1 : S (m w) = m (S w) := by
      have := congrArg (fun T : V →L[ℂ] V => T w) hcomm
      simpa using this
    rw [h1, hw', map_smul]
  rcases hirr W hsub with h | h
  · exact absurd h hWne
  · refine ⟨c, ?_⟩
    ext x
    have hx : S x = c • x := (hmemW x).mp (by rw [h]; trivial)
    simpa using hx

/-- The unitary form of Lemma 20: every unitary commuting with an irreducible
finite-dimensional system is a phase. -/
theorem isSchurUnitary_of_irreducible_finiteDimensional [FiniteDimensional ℂ V] [Nontrivial V]
    (M : System ℂ V) (hirr : M.IsIrreducible) : IsSchurUnitary M := by
  intro g hg
  have hcomm : M.Commutes (g.toContinuousLinearEquiv.toContinuousLinearMap) := by
    intro m hm
    ext x
    have := hg m hm x
    simpa using this
  obtain ⟨c, hc⟩ :=
    isSchurFull_of_irreducible_finiteDimensional M hirr _ hcomm
  have hgx : ∀ x, g x = c • x := by
    intro x
    have := congrArg (fun T : V →L[ℂ] V => T x) hc
    simpa using this
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : V)
  have hnorm : ‖c‖ = 1 := by
    have hiso : ‖g x₀‖ = ‖x₀‖ := g.norm_map x₀
    rw [hgx x₀, norm_smul] at hiso
    have hx0 : ‖x₀‖ ≠ 0 := norm_ne_zero_iff.mpr hx₀
    field_simp at hiso
    exact hiso
  exact ⟨c, hnorm, hgx⟩

/-! ## Lemma 21 — the square of a commuting anti-unitary -/

/-- The square of an anti-unitary, as a complex-linear bounded operator. -/
noncomputable def antiSq (θ : AntiUnitary V) : V →L[ℂ] V where
  toFun x := θ (θ x)
  map_add' x y := by simp
  map_smul' c x := by rw [map_smulₛₗ, map_smulₛₗ]; simp
  cont := θ.continuous.comp θ.continuous

omit [CompleteSpace V] in
@[simp] theorem antiSq_apply (θ : AntiUnitary V) (x : V) : antiSq θ x = θ (θ x) := rfl

/-- **Lemma 21 (core).**  An anti-unitary commuting with an irreducible finite-dimensional
complex system is either an involution or a pseudoreal structure: `θ² = 1` or `θ² = −1`. -/
theorem antiUnitary_sq_of_irreducible_finiteDimensional [FiniteDimensional ℂ V] [Nontrivial V]
    (M : System ℂ V) (hirr : M.IsIrreducible) {θ : AntiUnitary V}
    (hθ : CommutesAntiUnitary M θ) :
    (∀ x, θ (θ x) = x) ∨ (∀ x, θ (θ x) = -x) := by
  have hcomm : M.Commutes (antiSq θ) := by
    intro m hm
    ext x
    have h1 : θ (m x) = m (θ x) := hθ m hm x
    have h2 : θ (m (θ x)) = m (θ (θ x)) := hθ m hm (θ x)
    simp only [ContinuousLinearMap.mul_apply, antiSq_apply]
    rw [h1, h2]
  obtain ⟨c, hc⟩ := isSchurFull_of_irreducible_finiteDimensional M hirr (antiSq θ) hcomm
  have hcx : ∀ x : V, θ (θ x) = c • x := by
    intro x
    have := congrArg (fun T : V →L[ℂ] V => T x) hc
    simpa using this
  obtain ⟨x₀, hx₀⟩ := exists_ne (0 : V)
  have hθx₀ : θ x₀ ≠ 0 := by
    intro h
    exact hx₀ (θ.injective (by simpa using h : θ x₀ = θ 0))
  have hconj : conj c = c := by
    have h1 : θ (θ (θ x₀)) = conj c • θ x₀ := by
      calc θ (θ (θ x₀)) = θ (c • x₀) := by rw [hcx x₀]
        _ = conj c • θ x₀ := by rw [map_smulₛₗ]
    have h2 : θ (θ (θ x₀)) = c • θ x₀ := hcx (θ x₀)
    have h3 : (conj c - c) • θ x₀ = 0 := by
      rw [sub_smul, ← h1, h2]; simp
    rcases smul_eq_zero.mp h3 with h | h
    · linear_combination (norm := ring_nf) h
    · exact absurd h hθx₀
  have hnorm : ‖c‖ = 1 := by
    have hiso : ‖θ (θ x₀)‖ = ‖x₀‖ := by rw [θ.norm_map, θ.norm_map]
    rw [hcx x₀, norm_smul] at hiso
    have hx0 : ‖x₀‖ ≠ 0 := norm_ne_zero_iff.mpr hx₀
    field_simp at hiso
    exact hiso
  have hreal : c = 1 ∨ c = -1 := by
    have himzero : c.im = 0 := by
      have h := congrArg Complex.im hconj
      simp [Complex.conj_im] at h
      linarith
    have hc' : c = (c.re : ℂ) := Complex.ext rfl (by simp [himzero])
    rw [hc', Complex.norm_real, Real.norm_eq_abs] at hnorm
    rcases (abs_eq (by norm_num : (0:ℝ) ≤ 1)).mp hnorm with h | h
    · left; rw [hc', h]; norm_num
    · right; rw [hc', h]; norm_num
  rcases hreal with rfl | rfl
  · left; intro x; simpa using hcx x
  · right; intro x; simpa using hcx x

/-- The dichotomy in the book's vocabulary: either `θ` is a **C-conjugation** of the system
(Def 8.1) or it is a pseudoreal structure, `θ² = −1`. -/
theorem isConjugation_or_sq_eq_neg_one [FiniteDimensional ℂ V] [Nontrivial V]
    (M : System ℂ V) (hirr : M.IsIrreducible) {θ : AntiUnitary V}
    (hθ : CommutesAntiUnitary M θ) :
    IsConjugation M θ ∨ ((∀ x, θ (θ x) = -x) ∧ ∀ m ∈ M.ops, ∀ x, θ (m x) = m (θ x)) := by
  rcases antiUnitary_sq_of_irreducible_finiteDimensional M hirr hθ with h | h
  · exact Or.inl ⟨h, fun m hm x => hθ m hm x⟩
  · exact Or.inr ⟨h, fun m hm x => hθ m hm x⟩

/-! ## Payoff: Prop 17 with no Schur hypothesis in finite dimension -/

/-- **Prop 17 in finite dimension, unconditionally.**  For an irreducible finite-dimensional
complex system with a C-conjugation `θ`, the operators commuting with the system *and* with
`θ` are exactly the **real** scalars. -/
theorem Rreal_commutant_eq_real_scalars_finiteDimensional [FiniteDimensional ℂ V] [Nontrivial V]
    (M : System ℂ V) (hirr : M.IsIrreducible) {θ : AntiUnitary V} (hθ : IsConjugation M θ)
    (S : V →L[ℂ] V) :
    (M.Commutes S ∧ CommutesConj θ S) ↔ ∃ r : ℝ, S = ((r : ℂ)) • (1 : V →L[ℂ] V) :=
  Rreal_commutant_eq_real_scalars M
    (isSchurFull_of_irreducible_finiteDimensional M hirr) hθ S

end BookProof.ChapterSchurFiniteDimensional
