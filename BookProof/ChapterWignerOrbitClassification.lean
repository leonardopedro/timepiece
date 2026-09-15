import Mathlib
import BookProof.ChapterWignerLittleGroupOrbits

/-!
# Wigner's orbit classification, completed: the spacelike shells and the full list

`BookProof.ChapterWignerLittleGroupOrbits` classified the orbits of `SL(2,ℂ)` on momentum
space *inside the closed future cone* (mass shells, future light cone, origin) and computed
the little group of the spacelike reference momentum `(0,0,0,1)`; transitivity on the
spacelike shells was left open.  This file removes that boundary.

## Results

* `exists_boost_spacelike` — **every** momentum `p` with `p·p = -m² < 0` is obtained from
  the spacelike reference momentum `(0,0,0,m)` by an explicit element of `SL(2,ℂ)`.  The
  element is written down in closed form in the three cases `p⁰+p³ > 0`, `p⁰+p³ < 0` and
  `p⁰+p³ = 0`: it is the Gauss (`LDLᴴ`) factorization of the Hermitian matrix `hermOfMom p`,
  whose determinant `-m²` is negative, followed by a real diagonal rescaling and, in the
  last case, by a square root of a phase;
* `sameOrbit_spacelike` — consequently each spacelike shell `{p | p·p = -m²}` is a **single**
  orbit, and `littleGroup_spacelike_conj_SU11` transports the little group `SU(1,1)` of
  `BookProof.ChapterWignerLittleGroupOrbits` to every one of its points;
* `orbit_classification` — the complete list of the orbits: two momenta lie in the same
  orbit iff their Minkowski squares agree and, when that square is nonnegative, they are
  either both zero, or both of positive energy, or both of negative energy.  So the orbits
  are exactly: the spacelike shells (one for each `m > 0`), the two mass shells for each
  `m > 0`, the two halves of the light cone, and the origin.

Everything is `sorry`-free and uses only the standard axioms.
-/

open Matrix Complex

namespace BookProof.ChapterWignerOrbitClassification

open BookProof.ChapterWignerLittleGroup BookProof.ChapterWignerLittleGroupOrbits

/-- The Minkowski square `p·p` of a 4-momentum. -/
def minkSq (p : Fin 4 → ℝ) : ℝ := p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2

/-- Two momenta lie in the same `SL(2,ℂ)` orbit. -/
def SameOrbit (p q : Fin 4 → ℝ) : Prop :=
  ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧ act A (hermOfMom p) = hermOfMom q

theorem SameOrbit.refl (p : Fin 4 → ℝ) : SameOrbit p p :=
  ⟨1, by simp, act_one _⟩

theorem SameOrbit.symm {p q : Fin 4 → ℝ} (h : SameOrbit p q) : SameOrbit q p := by
  obtain ⟨A, hA, hact⟩ := h
  exact ⟨A⁻¹, det_inv_eq_one hA, act_inv_of_act hA hact⟩

theorem SameOrbit.trans {p q r : Fin 4 → ℝ} (h₁ : SameOrbit p q) (h₂ : SameOrbit q r) :
    SameOrbit p r := by
  obtain ⟨A, hA, ha⟩ := h₁
  obtain ⟨B, hB, hb⟩ := h₂
  exact ⟨B * A, by rw [Matrix.det_mul, hA, hB]; ring, by rw [act_mul, ha, hb]⟩

theorem minkSq_eq_of_sameOrbit {p q : Fin 4 → ℝ} (h : SameOrbit p q) : minkSq p = minkSq q := by
  obtain ⟨A, hA, hact⟩ := h
  exact (mass_invariant hA hact).symm

/-! ## The spacelike reference momentum -/

/-- The spacelike reference momentum `(0,0,0,m)`. -/
def spaceRefMom (m : ℝ) : Fin 4 → ℝ := ![0, 0, 0, m]

theorem hermOfMom_spaceRefMom (m : ℝ) :
    hermOfMom (spaceRefMom m) = !![(m : ℂ), 0; 0, -(m : ℂ)] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermOfMom, spaceRefMom]

theorem minkSq_spaceRefMom (m : ℝ) : minkSq (spaceRefMom m) = -m ^ 2 := by
  simp [minkSq, spaceRefMom]

/-! ## Transitivity on the spacelike shells

The three cases of the Gauss factorization of `hermOfMom p`. -/

/-- Spacelike transitivity, generic case `p⁰ + p³ > 0`. -/
theorem exists_boost_spacelike_of_pos {m : ℝ} (hm : 0 < m) (p : Fin 4 → ℝ)
    (hshell : minkSq p = -m ^ 2) (hpos : 0 < p 0 + p 3) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧
      act A (hermOfMom (spaceRefMom m)) = hermOfMom p := by
  have hs : ((p 0 : ℂ)) ^ 2 - (p 1 : ℂ) ^ 2 - (p 2 : ℂ) ^ 2 - (p 3 : ℂ) ^ 2 = -(m : ℂ) ^ 2 := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) hshell
    simp only [minkSq] at h
    push_cast at h
    exact h
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hm
  rw [hermOfMom_spaceRefMom]
  have ha0 : (p 0 : ℂ) + (p 3 : ℂ) ≠ 0 := by
    have : ((p 0 + p 3 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hpos
    push_cast at this
    exact this
  set s : ℝ := Real.sqrt ((p 0 + p 3) / m) with hsdef
  have hspos : 0 < s := Real.sqrt_pos.2 (by positivity)
  have hs2 : s ^ 2 = (p 0 + p 3) / m := Real.sq_sqrt (by positivity)
  have hsa : (s : ℂ) ^ 2 * (m : ℂ) = (p 0 : ℂ) + (p 3 : ℂ) := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) hs2
    push_cast at h
    field_simp at h ⊢
    linear_combination h
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hspos
  refine ⟨!![(s : ℂ), 0;
      ((p 1 : ℂ) + I * (p 2 : ℂ)) * (s : ℂ) / ((p 0 : ℂ) + (p 3 : ℂ)),
      (m : ℂ) * (s : ℂ) / ((p 0 : ℂ) + (p 3 : ℂ))], ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    field_simp
    linear_combination hsa
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [act, hermOfMom, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
        Complex.conj_ofReal] <;>
      field_simp
    · exact hsa
    · linear_combination ((p 1 : ℂ) - I * (p 2 : ℂ)) * hsa
    · linear_combination ((p 1 : ℂ) + I * (p 2 : ℂ)) * hsa
    · linear_combination (((p 1 : ℂ) + I * (p 2 : ℂ)) * ((p 1 : ℂ) - I * (p 2 : ℂ)) - (m : ℂ) ^ 2)
        * hsa - ((p 0 : ℂ) + (p 3 : ℂ)) * hs
        - ((p 0 : ℂ) + (p 3 : ℂ)) * (p 2 : ℂ) ^ 2 * Complex.I_sq

/-- Spacelike transitivity, case `p⁰ + p³ < 0`. -/
theorem exists_boost_spacelike_of_neg {m : ℝ} (hm : 0 < m) (p : Fin 4 → ℝ)
    (hshell : minkSq p = -m ^ 2) (hneg : p 0 + p 3 < 0) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧
      act A (hermOfMom (spaceRefMom m)) = hermOfMom p := by
  have hs : ((p 0 : ℂ)) ^ 2 - (p 1 : ℂ) ^ 2 - (p 2 : ℂ) ^ 2 - (p 3 : ℂ) ^ 2 = -(m : ℂ) ^ 2 := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) hshell
    simp only [minkSq] at h
    push_cast at h
    exact h
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hm
  rw [hermOfMom_spaceRefMom]
  have ha0 : (p 0 : ℂ) + (p 3 : ℂ) ≠ 0 := by
    have : ((p 0 + p 3 : ℝ) : ℂ) ≠ 0 := by exact_mod_cast ne_of_lt hneg
    push_cast at this
    exact this
  set s : ℝ := Real.sqrt (-(p 0 + p 3) / m) with hsdef
  have hspos : 0 < s := Real.sqrt_pos.2 (by
    have h1 : 0 < -(p 0 + p 3) := by linarith
    positivity)
  have hs2 : s ^ 2 = -(p 0 + p 3) / m := Real.sq_sqrt (by
    have h1 : 0 < -(p 0 + p 3) := by linarith
    positivity)
  have hsa : (s : ℂ) ^ 2 * (m : ℂ) = -((p 0 : ℂ) + (p 3 : ℂ)) := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) hs2
    push_cast at h
    field_simp at h ⊢
    linear_combination h
  have hs0 : (s : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hspos
  refine ⟨!![0, (s : ℂ);
      (m : ℂ) * (s : ℂ) / ((p 0 : ℂ) + (p 3 : ℂ)),
      ((p 1 : ℂ) + I * (p 2 : ℂ)) * (s : ℂ) / ((p 0 : ℂ) + (p 3 : ℂ))], ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    field_simp
    linear_combination -hsa
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [act, hermOfMom, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
        Complex.conj_ofReal] <;>
      field_simp
    · linear_combination -hsa
    · linear_combination -((p 1 : ℂ) - I * (p 2 : ℂ)) * hsa
    · linear_combination -((p 1 : ℂ) + I * (p 2 : ℂ)) * hsa
    · linear_combination ((m : ℂ) ^ 2 - ((p 1 : ℂ) + I * (p 2 : ℂ)) * ((p 1 : ℂ) - I * (p 2 : ℂ)))
        * hsa - ((p 0 : ℂ) + (p 3 : ℂ)) * hs
        - ((p 0 : ℂ) + (p 3 : ℂ)) * (p 2 : ℂ) ^ 2 * Complex.I_sq

/-- Spacelike transitivity, degenerate case `p⁰ + p³ = 0` (the `(0,0)` entry of the
Hermitian matrix vanishes, so the Gauss factorization starts from a square root of the
phase of the off-diagonal entry). -/
theorem exists_boost_spacelike_of_zero {m : ℝ} (hm : 0 < m) (p : Fin 4 → ℝ)
    (hshell : minkSq p = -m ^ 2) (hzero : p 0 + p 3 = 0) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧
      act A (hermOfMom (spaceRefMom m)) = hermOfMom p := by
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hm
  have hp3 : p 3 = -p 0 := by linarith
  have hshell' : p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 = -m ^ 2 := hshell
  have hnorm : p 1 ^ 2 + p 2 ^ 2 = m ^ 2 := by
    rw [hp3] at hshell'; nlinarith [hshell']
  rw [hermOfMom_spaceRefMom]
  obtain ⟨beta, hbeta⟩ :=
    IsAlgClosed.exists_pow_nat_eq (-(((p 1 : ℂ) - I * (p 2 : ℂ)) / (m : ℂ))) (n := 2) two_pos
  have hnsb : Complex.normSq ((p 1 : ℂ) - I * (p 2 : ℂ)) = p 1 ^ 2 + p 2 ^ 2 := by
    simp [Complex.normSq_apply]
    ring
  have hns : Complex.normSq beta = 1 := by
    have h1 : Complex.normSq (beta ^ 2) = Complex.normSq beta * Complex.normSq beta := by
      rw [pow_two, Complex.normSq_mul]
    rw [hbeta] at h1
    have h2 : Complex.normSq (-(((p 1 : ℂ) - I * (p 2 : ℂ)) / (m : ℂ))) = 1 := by
      rw [Complex.normSq_neg, Complex.normSq_div, hnsb]
      have hmm : Complex.normSq ((m : ℝ) : ℂ) = m ^ 2 := by
        simp [Complex.normSq_apply]; ring
      rw [hmm, hnorm]
      field_simp
    rw [h2] at h1
    nlinarith [Complex.normSq_nonneg beta, h1]
  have hbb : beta * (starRingEnd ℂ) beta = 1 := by
    rw [Complex.mul_conj, hns]
    norm_num
  have hbeta' : beta ^ 2 * (m : ℂ) = -((p 1 : ℂ) - I * (p 2 : ℂ)) := by
    rw [hbeta]; field_simp
  have hbetac' : (starRingEnd ℂ) beta ^ 2 * (m : ℂ) = -((p 1 : ℂ) + I * (p 2 : ℂ)) := by
    have h := congrArg (starRingEnd ℂ) hbeta'
    simpa [map_mul, map_pow, Complex.conj_ofReal] using h
  set lam : ℝ := -(m + 2 * p 0) / (2 * m) with hlam
  have hlamC : (lam : ℂ) * (2 * (m : ℂ)) = -((m : ℂ) + 2 * (p 0 : ℂ)) := by
    have h := congrArg (fun x : ℝ => (x : ℂ)) hlam
    push_cast at h
    rw [h]
    field_simp
  refine ⟨!![beta, beta;
      (lam : ℂ) * (starRingEnd ℂ) beta, ((lam : ℂ) + 1) * (starRingEnd ℂ) beta], ?_, ?_⟩
  · rw [Matrix.det_fin_two_of]
    linear_combination hbb
  · ext i j
    fin_cases i <;> fin_cases j <;>
      simp [act, hermOfMom, Matrix.mul_apply, Fin.sum_univ_two, Matrix.conjTranspose_apply,
        Complex.conj_ofReal, hp3] <;>
      field_simp
    · linear_combination -hbeta'
    · linear_combination -hbetac'
    · linear_combination (-(m : ℂ) * (2 * (lam : ℂ) + 1)) * hbb - hlamC

/-- **Transitivity on the spacelike shells.**  Every momentum with `p·p = -m² < 0` is an
`SL(2,ℂ)` transform of the spacelike reference momentum `(0,0,0,m)`. -/
theorem exists_boost_spacelike {m : ℝ} (hm : 0 < m) (p : Fin 4 → ℝ)
    (hshell : minkSq p = -m ^ 2) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧
      act A (hermOfMom (spaceRefMom m)) = hermOfMom p := by
  rcases lt_trichotomy (p 0 + p 3) 0 with h | h | h
  · exact exists_boost_spacelike_of_neg hm p hshell h
  · exact exists_boost_spacelike_of_zero hm p hshell h
  · exact exists_boost_spacelike_of_pos hm p hshell h

/-- **Each spacelike shell is a single orbit.** -/
theorem sameOrbit_spacelike {p q : Fin 4 → ℝ} (hneg : minkSq p < 0) (hpq : minkSq p = minkSq q) :
    SameOrbit p q := by
  set m : ℝ := Real.sqrt (-minkSq p) with hm
  have hmpos : 0 < m := Real.sqrt_pos.2 (by linarith)
  have hm2 : m ^ 2 = -minkSq p := Real.sq_sqrt (by linarith)
  have hp : minkSq p = -m ^ 2 := by rw [hm2]; ring
  have hq : minkSq q = -m ^ 2 := by rw [← hpq]; exact hp
  have h1 : SameOrbit (spaceRefMom m) p := exists_boost_spacelike hmpos p hp
  have h2 : SameOrbit (spaceRefMom m) q := exists_boost_spacelike hmpos q hq
  exact h1.symm.trans h2

/-- The little group of any spacelike momentum is conjugate to `SU(1,1)`. -/
theorem littleGroup_spacelike_conj_SU11 {p : Fin 4 → ℝ} (hneg : minkSq p < 0) :
    ∃ A : Matrix (Fin 2) (Fin 2) ℂ, A.det = 1 ∧
      littleGroup p = (fun B => A * B * A⁻¹) '' SU11 := by
  set m : ℝ := Real.sqrt (-minkSq p) with hm
  have hmpos : 0 < m := Real.sqrt_pos.2 (by linarith)
  have hm2 : m ^ 2 = -minkSq p := Real.sq_sqrt (by linarith)
  have hp : minkSq p = -m ^ 2 := by rw [hm2]; ring
  obtain ⟨A, hA, hact⟩ := exists_boost_spacelike hmpos p hp
  refine ⟨A, hA, ?_⟩
  have hconj := littleGroup_conj hA hact
  rw [hconj]
  congr 1
  -- the little group of `(0,0,0,m)` is that of `(0,0,0,1)`, namely `SU(1,1)`
  have hm0 : (m : ℂ) ≠ 0 := by exact_mod_cast ne_of_gt hmpos
  have hE : !![(m : ℂ), 0; 0, -(m : ℂ)] = (m : ℂ) • !![(1 : ℂ), 0; 0, -1] := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have key : ∀ B : Matrix (Fin 2) (Fin 2) ℂ,
      B * !![(m : ℂ), 0; 0, -(m : ℂ)] * Bᴴ = (m : ℂ) • (B * !![(1 : ℂ), 0; 0, -1] * Bᴴ) := by
    intro B
    rw [hE, Matrix.mul_smul, Matrix.smul_mul]
  have hscale : littleGroup (spaceRefMom m) = SU11 := by
    ext B
    constructor
    · rintro ⟨hdet, hfix⟩
      refine ⟨hdet, ?_⟩
      simp only [hermOfMom_spaceRefMom, act] at hfix
      rw [key B, hE] at hfix
      exact smul_right_injective _ hm0 hfix
    · rintro ⟨hdet, hfix⟩
      refine ⟨hdet, ?_⟩
      simp only [hermOfMom_spaceRefMom, act]
      rw [key B, hfix, hE]
  exact hscale

/-! ## The complete list of the orbits -/

/-- The momentum with all components negated. -/
def negMom (p : Fin 4 → ℝ) : Fin 4 → ℝ := fun i => -p i

theorem minkSq_negMom (p : Fin 4 → ℝ) : minkSq (negMom p) = minkSq p := by
  simp [minkSq, negMom]

theorem hermOfMom_negMom (p : Fin 4 → ℝ) : hermOfMom (negMom p) = -hermOfMom p := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [hermOfMom, negMom] <;> ring

theorem sameOrbit_negMom {p q : Fin 4 → ℝ} (h : SameOrbit p q) :
    SameOrbit (negMom p) (negMom q) := by
  obtain ⟨A, hA, hact⟩ := h
  refine ⟨A, hA, ?_⟩
  simp only [act] at hact ⊢
  rw [hermOfMom_negMom, hermOfMom_negMom, Matrix.mul_neg, Matrix.neg_mul, hact]

theorem negMom_negMom (p : Fin 4 → ℝ) : negMom (negMom p) = p := by
  funext i; simp [negMom]

/-- A momentum with nonnegative Minkowski square and vanishing energy is zero. -/
theorem eq_zero_of_energy_zero {p : Fin 4 → ℝ} (hmass : 0 ≤ minkSq p) (h0 : p 0 = 0) :
    ∀ i, p i = 0 := by
  have hle : p 1 ^ 2 + p 2 ^ 2 + p 3 ^ 2 ≤ 0 := by
    simp only [minkSq, h0] at hmass
    nlinarith [hmass]
  have h1 : p 1 = 0 := by nlinarith [sq_nonneg (p 1), sq_nonneg (p 2), sq_nonneg (p 3)]
  have h2 : p 2 = 0 := by nlinarith [sq_nonneg (p 1), sq_nonneg (p 2), sq_nonneg (p 3)]
  have h3 : p 3 = 0 := by nlinarith [sq_nonneg (p 1), sq_nonneg (p 2), sq_nonneg (p 3)]
  intro i
  fin_cases i
  · simpa using h0
  · simpa using h1
  · simpa using h2
  · simpa using h3

theorem sameOrbit_of_zero {p q : Fin 4 → ℝ} (hp : ∀ i, p i = 0) (hq : ∀ i, q i = 0) :
    SameOrbit p q := by
  refine ⟨1, by simp, ?_⟩
  rw [hermOfMom_eq_zero_iff.2 hp, hermOfMom_eq_zero_iff.2 hq, act, Matrix.mul_zero,
    Matrix.zero_mul]

/-- **Wigner's orbit classification, complete.**  Two 4-momenta lie in the same `SL(2,ℂ)`
orbit exactly when their Minkowski squares agree and, in the case of a nonnegative square,
they are both zero, or both of positive energy, or both of negative energy.  The orbits are
therefore: for each `m > 0` the spacelike shell `p·p = -m²` (one orbit), the two mass shells
`p·p = m²` with `p⁰ > 0` and `p⁰ < 0`, the two halves of the light cone, and the origin. -/
theorem orbit_classification (p q : Fin 4 → ℝ) :
    SameOrbit p q ↔ minkSq p = minkSq q ∧
      (minkSq p < 0 ∨ ((∀ i, p i = 0) ∧ (∀ i, q i = 0)) ∨ (0 < p 0 ∧ 0 < q 0) ∨
        (p 0 < 0 ∧ q 0 < 0)) := by
  constructor
  · intro h
    refine ⟨minkSq_eq_of_sameOrbit h, ?_⟩
    rcases lt_or_ge (minkSq p) 0 with hneg | hmass
    · exact Or.inl hneg
    · rcases lt_trichotomy (p 0) 0 with hlt | heq | hgt
      · -- negative energy: pass to the negated momenta, which are future-pointing
        obtain ⟨A, hA, hact⟩ := sameOrbit_negMom h
        have hp0 : 0 < negMom p 0 := by simp [negMom]; linarith
        have hmass' : 0 ≤ negMom p 0 ^ 2 - negMom p 1 ^ 2 - negMom p 2 ^ 2 - negMom p 3 ^ 2 := by
          have := hmass
          simp only [minkSq] at this
          simpa [negMom] using this
        have := energy_pos_of_act hA hp0 hmass' hact
        simp only [negMom] at this
        exact Or.inr (Or.inr (Or.inr ⟨hlt, by linarith⟩))
      · -- zero energy and nonnegative square: both momenta vanish
        have hpz : ∀ i, p i = 0 := eq_zero_of_energy_zero hmass heq
        obtain ⟨A, hA, hact⟩ := h
        have hqz : hermOfMom q = 0 := by
          rw [← hact, hermOfMom_eq_zero_iff.2 hpz, act, Matrix.mul_zero, Matrix.zero_mul]
        exact Or.inr (Or.inl ⟨hpz, hermOfMom_eq_zero_iff.1 hqz⟩)
      · obtain ⟨A, hA, hact⟩ := h
        have hmass' : 0 ≤ p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 := hmass
        exact Or.inr (Or.inr (Or.inl ⟨hgt, energy_pos_of_act hA hgt hmass' hact⟩))
  · rintro ⟨hsq, hcase⟩
    rcases lt_or_ge (minkSq p) 0 with hneg | hmass
    · exact sameOrbit_spacelike hneg hsq
    rcases hcase with hneg | ⟨hpz, hqz⟩ | ⟨hp0, hq0⟩ | ⟨hp0, hq0⟩
    · exact absurd hneg (not_lt.2 hmass)
    · exact sameOrbit_of_zero hpz hqz
    · have hmass' : 0 ≤ p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 := hmass
      have hsq' : q 0 ^ 2 - q 1 ^ 2 - q 2 ^ 2 - q 3 ^ 2 = p 0 ^ 2 - p 1 ^ 2 - p 2 ^ 2 - p 3 ^ 2 :=
        hsq.symm
      exact (orbit_iff_massSq_eq hp0 hq0 hmass').2 hsq'
    · -- both of negative energy: negate, apply the future-cone case, negate back
      have hp0' : 0 < negMom p 0 := by simp [negMom]; linarith
      have hq0' : 0 < negMom q 0 := by simp [negMom]; linarith
      have hmass' : 0 ≤ negMom p 0 ^ 2 - negMom p 1 ^ 2 - negMom p 2 ^ 2 - negMom p 3 ^ 2 := by
        have := hmass
        simp only [minkSq] at this
        simpa [negMom] using this
      have hsq' : negMom q 0 ^ 2 - negMom q 1 ^ 2 - negMom q 2 ^ 2 - negMom q 3 ^ 2
          = negMom p 0 ^ 2 - negMom p 1 ^ 2 - negMom p 2 ^ 2 - negMom p 3 ^ 2 := by
        have h := hsq.symm
        simp only [minkSq] at h
        simpa [negMom] using h
      have hnn : SameOrbit (negMom p) (negMom q) := (orbit_iff_massSq_eq hp0' hq0' hmass').2 hsq'
      have := sameOrbit_negMom hnn
      rwa [negMom_negMom, negMom_negMom] at this

end BookProof.ChapterWignerOrbitClassification
