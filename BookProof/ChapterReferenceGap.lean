import Mathlib
import BookProof.ChapterHarmonicOscillatorEsa

/-!
# Chapter ReferenceGap — a solvable gapped reference operator in `d` dimensions

`softmodes.md` Phase 3 asks for a *reference* operator `H_ref` that (i) is explicitly
solvable on the product Hermite core, (ii) has closed-form energies with a known gap
`Δ_ref > 0`, and (iii) can later be compared with the Yang–Mills Hamiltonian at the level
of quadratic forms.  This chapter supplies (i) and (ii).

## The operator

On the `d`-dimensional anisotropic oscillator, the joint spectrum of
`H_ref = ∑_k (−∂²/∂x_k² + ω_k² x_k²)` (any fixed normalization) is labelled by the
multi-index `n : Fin d → ℕ` of occupation numbers, with energy

`refEnergy ω n = ∑ i, ωᵢ (nᵢ + ½)`.

This is a port of `Physlib.QuantumMechanics.HarmonicOscillator.eigenEnergy` and its
`eigenEnergy_strictMono` (with `ℏ = 1` and general frequencies `ω`); the ladder-operator
and eigenfunction machinery of that file is *not* ported, because nothing in the gap
argument needs it.  The port lands on this repository's `d = 1` oscillator: for unit
frequency `refEnergy` is `BookProof.HarmonicOscillator.harmonicSymbol`
(`refEnergy_one_eq_harmonicSymbol`), whose self-adjointness on the Hermite core and
differential realization are `harmonicOsc_essentiallySelfAdjoint` and
`harmonicOscOp_apply_eq_differential`.

## The gap

The vacuum is the multi-index `0`.  For any excited level `n ≠ 0` some occupation `n_j ≥ 1`,
so `refEnergy ω n − refEnergy ω 0 = ∑ i, ωᵢ nᵢ ≥ ω_j ≥ min_k ω_k = Δ_ref`
(`refEnergy_ge_vacuum_add_gap`).  Because the excitation energy is additive in `n`, this
gives the form inequality on the whole Gauss–polynomial core — finite coefficient families
`c : (Fin d → ℕ) →₀ ℂ`:

`href_spectral_gap` : `c 0 = 0` implies
`(refEnergy ω 0 + Δ_ref) * ∑ ‖c n‖² ≤ ∑ refEnergy ω n * ‖c n‖²`

which is the Phase-3 milestone in the shape the plan states it
(`ψ ⊥ Ω → ⟨ψ, H_ref ψ⟩ ≥ (μ₀ + Δ_ref)‖ψ‖²`).  The parity sector is the same statement with
hypothesis `n_j = 0 → c n = 0` (`href_spectral_gap_of_parity`), and the bound is attained
by the vacuum itself (`coreForm_vacuum`), so `Δ_ref` is the exact gap of `H_ref` on the
vacuum-orthogonal sector, not merely a lower bound.

## Honest boundary

The core here is the *coefficient* model of the product Hermite basis: `c n` is the
coefficient of the basis vector with multi-index `n`, and a state is a finite family.  This
is the core on which Phase 4 will compare quadratic forms, so it is the right generality
for the reference gap.  The extension of `href_spectral_gap` to the `L²` closure of the core
is `closed_refGap` in `BookProof.YangMillsFormClosure`: there `L²` is `ℓ²` over the
multi-indices, the core is dense in it, and the closed form `closedForm (refEnergy ω)` satisfies
`(μ₀ + Δ_ref)‖x‖² ≤ closedForm (refEnergy ω) x` for *every* `x` orthogonal to the vacuum.  The
comparison inequality of Phase 4 — that the Yang–Mills form dominates `coreForm` — is a separate
chapter (`BookProof.YangMillsFormDomination`) and is not claimed.
-/

noncomputable section

namespace BookProof.ReferenceGap

open Finset

variable {d : ℕ}

/-! ## The energy symbol -/

/-- The energy of the multi-index `n` for the anisotropic oscillator with frequencies `ω`,
`∑ i, ωᵢ (nᵢ + ½)`.  Port of `eigenEnergy` with `ℏ = 1`. -/
def refEnergy (ω : Fin d → ℝ) (n : Fin d → ℕ) : ℝ :=
  ∑ i, ω i * ((n i : ℝ) + 1 / 2)

/-- The vacuum energy `μ₀ = ∑ i, ωᵢ / 2`. -/
theorem refEnergy_zero (ω : Fin d → ℝ) : refEnergy ω 0 = ∑ i, ω i / 2 := by
  simp only [refEnergy, Pi.zero_apply, Nat.cast_zero, zero_add, div_eq_mul_inv, one_mul]

/-- The excitation energy above the vacuum is additive in the occupation numbers:
`μ(n) − μ(0) = ∑ i, ωᵢ nᵢ`. -/
theorem refEnergy_sub_zero (ω : Fin d → ℝ) (n : Fin d → ℕ) :
    refEnergy ω n - refEnergy ω 0 = ∑ i, ω i * (n i : ℝ) := by
  simp only [refEnergy, Pi.zero_apply, Nat.cast_zero, zero_add,
    ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun i _ => by ring

/-- Energies are nonnegative for positive frequencies. -/
theorem refEnergy_nonneg (ω : Fin d → ℝ) (hω : ∀ i, 0 < ω i) (n : Fin d → ℕ) :
    0 ≤ refEnergy ω n :=
  Finset.sum_nonneg fun i _ => mul_nonneg (hω i).le (by positivity)

/-- `refEnergy` is strictly monotone in the multi-index (port of `eigenEnergy_strictMono`):
raising any occupation raises the energy. -/
theorem refEnergy_strictMono {ω : Fin d → ℝ} (hω : ∀ i, 0 < ω i) :
    StrictMono (refEnergy ω) := by
  intro n n' h
  obtain ⟨hle, i, hi⟩ := Pi.lt_def.mp h
  refine Finset.sum_lt_sum (fun j _ => ?_) ⟨i, Finset.mem_univ i, ?_⟩
  · have hcast : (n j : ℝ) ≤ (n' j : ℝ) := by exact_mod_cast hle j
    have := hω j
    nlinarith
  · have hcast : (n i : ℝ) < (n' i : ℝ) := by exact_mod_cast hi
    have := hω i
    nlinarith

/-- On the single coordinate `d = 1` with unit frequency the ported symbol is this
repository's one-dimensional oscillator symbol. -/
theorem refEnergy_one_eq_harmonicSymbol (n : ℕ) :
    refEnergy (fun _ : Fin 1 => (1 : ℝ)) (fun _ => n)
      = BookProof.HarmonicOscillator.harmonicSymbol n := by
  rw [refEnergy, Fin.sum_univ_one]
  simp [BookProof.HarmonicOscillator.harmonicSymbol]

/-! ## The reference gap `Δ_ref = min_k ω_k` -/

/-- The reference gap: the smallest frequency, `Δ_ref = min_k ω_k`. -/
def refGap [Nonempty (Fin d)] (ω : Fin d → ℝ) : ℝ :=
  Finset.univ.inf' Finset.univ_nonempty ω

/-- `Δ_ref` is a lower bound for every frequency. -/
theorem refGap_le [Nonempty (Fin d)] (ω : Fin d → ℝ) (i : Fin d) : refGap ω ≤ ω i := by
  simpa only [refGap] using Finset.inf'_le (f := ω) (Finset.mem_univ i)

/-- For positive frequencies the reference gap is positive. -/
theorem refGap_pos [Nonempty (Fin d)] {ω : Fin d → ℝ} (hω : ∀ i, 0 < ω i) :
    0 < refGap ω := by
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_mem_eq_inf' (s := Finset.univ) (H := Finset.univ_nonempty) ω
  rw [refGap, hi]
  exact hω i

/-- The reference gap is attained. -/
theorem exists_refGap_eq [Nonempty (Fin d)] (ω : Fin d → ℝ) :
    ∃ i, refGap ω = ω i := by
  obtain ⟨i, -, hi⟩ :=
    Finset.exists_mem_eq_inf' (s := Finset.univ) (H := Finset.univ_nonempty) ω
  exact ⟨i, by rw [refGap, hi]⟩

/-- **Every excited level clears the vacuum by at least `Δ_ref`.** -/
theorem refEnergy_ge_vacuum_add_gap [Nonempty (Fin d)] {ω : Fin d → ℝ}
    (hω : ∀ i, 0 < ω i) {n : Fin d → ℕ} (hn : n ≠ 0) :
    refEnergy ω 0 + refGap ω ≤ refEnergy ω n := by
  have hsub := refEnergy_sub_zero ω n
  obtain ⟨j, hj⟩ : ∃ j, n j ≠ 0 := by
    by_contra h
    exact hn (funext fun j => by simpa using not_exists.mp h j)
  have hjpos : 0 < n j := Nat.pos_of_ne_zero hj
  have h1 : ω j ≤ ω j * (n j : ℝ) := by
    have hcast : (1 : ℝ) ≤ (n j : ℝ) := by exact_mod_cast hjpos
    have := hω j
    nlinarith
  have h2 : ω j * (n j : ℝ) ≤ ∑ i, ω i * (n i : ℝ) :=
    Finset.single_le_sum (s := Finset.univ) (f := fun i => ω i * (n i : ℝ))
      (fun i _ => mul_nonneg (hω i).le (by positivity)) (Finset.mem_univ j)
  have h3 : refGap ω ≤ ω j := refGap_le ω j
  linarith

/-! ## The Gauss–polynomial core

A state is a finite family of coefficients on the product Hermite basis: the algebraic
direct sum `(Fin d → ℕ) →₀ ℂ`, i.e. polynomials times the Gaussian.  `coreNormSq` and
`coreForm` are the norm-squared and the quadratic form of `H_ref` read in these
coefficients; the cross terms vanish because the basis is orthogonal. -/

/-- Coefficient vectors on the product Hermite core. -/
abbrev CoreCoeff (d : ℕ) := (Fin d → ℕ) →₀ ℂ

/-- The squared norm of a core state. -/
def coreNormSq (c : CoreCoeff d) : ℝ := ∑ n ∈ c.support, ‖c n‖ ^ 2

/-- The quadratic form of `H_ref` on a core state. -/
def coreForm (ω : Fin d → ℝ) (c : CoreCoeff d) : ℝ :=
  ∑ n ∈ c.support, refEnergy ω n * ‖c n‖ ^ 2

/-- The vacuum `Ω`: the basis vector with all occupation numbers zero. -/
def vacuum (d : ℕ) : CoreCoeff d := Finsupp.single 0 1

theorem coreNormSq_nonneg (c : CoreCoeff d) : 0 ≤ coreNormSq c :=
  Finset.sum_nonneg fun n _ => by positivity

theorem coreNormSq_vacuum (d : ℕ) : coreNormSq (vacuum d) = 1 := by
  rw [coreNormSq, vacuum, Finsupp.support_single_ne_zero _ one_ne_zero]
  simp

/-- The vacuum sits at the bottom of the spectrum. -/
theorem coreForm_vacuum (ω : Fin d → ℝ) : coreForm ω (vacuum d) = refEnergy ω 0 := by
  rw [coreForm, vacuum, Finsupp.support_single_ne_zero _ one_ne_zero]
  simp

/-- **Phase-3 milestone**: a state orthogonal to the vacuum has energy at least
`μ₀ + Δ_ref` in the sense of quadratic forms. -/
theorem href_spectral_gap [Nonempty (Fin d)] (ω : Fin d → ℝ) (hω : ∀ i, 0 < ω i)
    (c : CoreCoeff d) (hc : c 0 = 0) :
    (refEnergy ω 0 + refGap ω) * coreNormSq c ≤ coreForm ω c := by
  rw [coreForm, coreNormSq, Finset.mul_sum]
  refine Finset.sum_le_sum fun n hn => ?_
  have hne : n ≠ 0 := by
    rintro rfl
    exact (Finsupp.notMem_support_iff.mpr hc) hn
  exact mul_le_mul_of_nonneg_right (refEnergy_ge_vacuum_add_gap hω hne) (by positivity)

/-- The parity sector: a state with no even occupation in the `j`-th coordinate is
automatically orthogonal to the vacuum, so it carries the same gap. -/
theorem href_spectral_gap_of_parity [Nonempty (Fin d)] (ω : Fin d → ℝ) (hω : ∀ i, 0 < ω i)
    (j : Fin d) (c : CoreCoeff d) (hpar : ∀ n : Fin d → ℕ, n j = 0 → c n = 0) :
    (refEnergy ω 0 + refGap ω) * coreNormSq c ≤ coreForm ω c :=
  href_spectral_gap ω hω c (hpar 0 rfl)

end BookProof.ReferenceGap
