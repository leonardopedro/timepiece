import Mathlib
import BookProof.ChapterCPTHamiltonian
import BookProof.ChapterSmDiracYukawa

/-!
# The spinor Dirac operator, second quantized on the CAR algebra

`BookProof.ChapterSmDiracYukawa` puts a *general* Hermitian one-particle matrix on the CAR
algebra.  This module supplies the **concrete Dirac one-particle matrix** with its spinor
structure, taken from the `4 × 4` Majorana model already in the project
(`BookProof.ChapterCPTHamiltonian`, which formalizes `iH = ∂⃗·γ⃗γ⁰ + iγ⁰m₁ + γ⁰γ⁵m₂` and its
mass-shell identity), and second quantizes it.

## What is proved

* `diracOneParticle` — the plane-wave Dirac Hamiltonian matrix `H(k, m₁, m₂) = −i D(k,m₁,m₂)`
  on the four spinor components, with
  `diracOneParticle_hermitian` — it is Hermitian, so the Dirac sector is a legitimate input
  to the fermionic machinery;
* `diracOneParticle_sq` — the **dispersion relation** `H² = (k² + m₁² + m₂²)·1`;
* `diracOneParticle_eigenvalue_sq` — hence every eigenvalue satisfies `μ² = k² + m₁² + m₂²`:
  the relativistic energies `±√(k² + m₁² + m₂²)` (a *one-particle* spectral statement);
* `diracFieldHam` — its second quantization `Σ_{A,B} H_{AB} a†_A a_B` on the fermionic Fock
  space of the four spinor modes, `diracFieldHam_symmetric`;
* `dirac_field_esa` — essential self-adjointness of the second-quantized Dirac operator,
  through the three Faris–Lavine hypotheses of `BookProof.ChapterSmDiracYukawa`.

## Honest boundary

One plane-wave mode with its four spinor components: this is the spinor structure of the
Dirac operator, not the full field over all momenta, and not the covariant derivative `D`
with its gauge connection.  The colour/flavour and gauge structure enters only through the
one-particle matrix, which is an input here.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.SmDiracSpinor

open Matrix
open BookProof.ChapterCPTHamiltonian BookProof.SmCar BookProof.SmDiracYukawa
open BookProof.FarisLavine

noncomputable section

variable {k : Fin 3 → ℝ} {m1 m2 : ℝ}

/-- **The one-particle Dirac Hamiltonian matrix** of a plane-wave mode: `H = −i D`, where
`D = iH` is the anti-Hermitian operator of `BookProof.ChapterCPTHamiltonian`. -/
def diracOneParticle (k : Fin 3 → ℝ) (m1 m2 : ℝ) : Matrix (Fin 4) (Fin 4) ℂ :=
  (-Complex.I) • diracHamOp k m1 m2

/-- **The Dirac one-particle matrix is Hermitian.** -/
theorem diracOneParticle_hermitian :
    (diracOneParticle k m1 m2).conjTranspose = diracOneParticle k m1 m2 := by
  rw [diracOneParticle, Matrix.conjTranspose_smul, diracHamOp_conjTranspose]
  have hI : star (-Complex.I) = Complex.I := by simp
  rw [hI]
  simp [smul_neg, neg_smul]

/-- **The dispersion relation** `H² = (k² + m₁² + m₂²)·1`. -/
theorem diracOneParticle_sq :
    diracOneParticle k m1 m2 * diracOneParticle k m1 m2
      = (((∑ j : Fin 3, (k j : ℂ) ^ 2) + (m1 : ℂ) ^ 2 + (m2 : ℂ) ^ 2))
        • (1 : Matrix (Fin 4) (Fin 4) ℂ) := by
  rw [diracOneParticle, Matrix.smul_mul, Matrix.mul_smul, diracHamOp_sq, smul_smul, smul_smul]
  congr 1
  have hII : (-Complex.I) * (-Complex.I) = -1 := by
    rw [neg_mul_neg, Complex.I_mul_I]
  rw [hII]
  ring

/-- **The relativistic energies.**  Every eigenvalue `μ` of the Dirac one-particle matrix
satisfies `μ² = k² + m₁² + m₂²`, i.e. `μ = ±√(k² + m₁² + m₂²)`. -/
theorem diracOneParticle_eigenvalue_sq {v : Fin 4 → ℂ} {mu : ℂ} (hv : v ≠ 0)
    (heig : (diracOneParticle k m1 m2).mulVec v = mu • v) :
    mu ^ 2 = (∑ j : Fin 3, (k j : ℂ) ^ 2) + (m1 : ℂ) ^ 2 + (m2 : ℂ) ^ 2 := by
  set E : ℂ := (∑ j : Fin 3, (k j : ℂ) ^ 2) + (m1 : ℂ) ^ 2 + (m2 : ℂ) ^ 2 with hE
  have h1 : (diracOneParticle k m1 m2 * diracOneParticle k m1 m2).mulVec v = E • v := by
    rw [diracOneParticle_sq, Matrix.smul_mulVec, Matrix.one_mulVec]
  have h2 : (diracOneParticle k m1 m2 * diracOneParticle k m1 m2).mulVec v = (mu ^ 2) • v := by
    rw [← Matrix.mulVec_mulVec, heig, Matrix.mulVec_smul, heig, smul_smul, sq]
  have h3 : (mu ^ 2 - E) • v = 0 := by
    rw [sub_smul, ← h2, h1, sub_self]
  rcases smul_eq_zero.mp h3 with h | h
  · exact sub_eq_zero.mp h
  · exact absurd h hv

/-! ## The second quantization -/

theorem smFermiHam_zero_yukawa (hD : Matrix (Fin 4) (Fin 4) ℂ) :
    smFermiHam hD (0 : Matrix (Fin 4) (Fin 4) ℂ) 0 = fermiBilin hD := by
  simp [smFermiHam, smFermiMatrix]

/-- **The second-quantized Dirac operator** `Σ_{A,B} H_{AB} a†_A a_B` on the fermionic Fock
space of the four spinor modes. -/
def diracFieldHam (k : Fin 3 → ℝ) (m1 m2 : ℝ) : FermiFock 4 →ₗ[ℂ] FermiFock 4 :=
  fermiBilin (diracOneParticle k m1 m2)

theorem diracFieldHam_symmetric (psi phi : FermiFock 4) :
    (inner ℂ (diracFieldHam k m1 m2 psi) phi : ℂ)
      = inner ℂ psi (diracFieldHam k m1 m2 phi) :=
  fermiBilin_symmetric diracOneParticle_hermitian psi phi

/-- **The second-quantized Dirac operator is essentially self-adjoint**, by the Faris–Lavine
route of `BookProof.ChapterSmDiracYukawa` with the comparison operator
`N = Σ_A ω_A a†_A a_A + c₀`. -/
theorem dirac_field_esa {om : Fin 4 → ℝ} {c0 : ℝ} (hom : ∀ i, 0 ≤ om i) (hc0 : 1 ≤ c0) :
    EssentiallySelfAdjointOn (fullDom 4)
      ((onFull (smFermiHam (diracOneParticle k m1 m2) (0 : Matrix (Fin 4) (Fin 4) ℂ) 0)).comp
        (Submodule.inclusion (le_refl (fullDom 4)))) :=
  sm_fermi_esa (om := om) (c0 := c0) diracOneParticle_hermitian hom hc0

end

end BookProof.SmDiracSpinor
