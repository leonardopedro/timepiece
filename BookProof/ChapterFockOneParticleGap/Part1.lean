import Mathlib
import BookProof.ChapterFockSecondQuantization
import BookProof.ChapterSirkCertifiedGap
import BookProof.ChapterSirkRitzSpectrum
import BookProof.ChapterSpectralGapStability

/-!
# Chapter FockOneParticleGap — the one-particle edge and its free `dΓ` lift

/-!
Interpretation convention: this module proves facts about the inner one-particle
operator and their lift. The physical final Hamiltonian in QYM, QED, QG, and NS
is the outer creation-left/annihilation-right enclosure of that operator. Hence
inner squeezed states are not full-theory grounds; the outer vacuum is killed by
the rightmost outer annihilator.
-/!

`CONSOLIDATED_PLAN.md`, top work package ("Hashimoto observable to the real-Hamiltonian
gap"), asks for the composition that is genuinely missing between the finite Hashimoto/SIRK
certificate and a *Fock* mass gap:

* the **one-particle** observable, its strict positivity `h₊ ≥ μ I`, and the free
  number-operator shift `dΓ(h₊) = dΓ(h − E₀I) + μ N`;
* the **nested-band** conclusion: certified intervals with vanishing widths that all
  enclose the lowest positive one-particle energy of one *fixed* operator determine that
  energy, and a single interval whose lower end is `≥ μ` already forces `λ₁ ≥ μ`;
* the **free `dΓ` lift**: the vacuum has energy `0`, every non-vacuum finite-particle
  state has energy at least the lowest one-particle energy, and a one-particle creation
  attains it — so the Fock gap *is* the one-particle edge.

Everything is proved in the algebraic Fock space `FockAlg = Conf →₀ ℂ` of
`BookProof.FockSecondQuantization`, for the **free** (number-preserving, diagonal in the
one-particle eigenbasis) one-particle Hamiltonian: `diagCol e` is the one-particle matrix
with eigenvalues `e k`, i.e. the matrix of `h₊` in a basis that diagonalizes it.  That is
exactly the "free outer particles" hypothesis of the plan; it is stated explicitly
everywhere and nothing here applies to pair creation or other interacting terms.

## Deliverables

* `dGamma_diagCol_single`, `dGamma_diagCol_apply` — `dΓ(h₊)` is diagonal on
  configurations, with eigenvalue the configuration energy `Σ_k β_k e_k`;
* `dGamma_diagCol_vac`, `numberOp_vac` — `dΓ(h₊) Ω = 0` and `N Ω = 0`;
* `dGamma_diagCol_one_particle`, `fock_energy_one_particle` — `a†(e_k) Ω` is an
  eigenvector of energy `e k`, so the one-particle energies really are Fock energies;
* `dGamma_diagCol_shift` — the free number-operator shift
  `dΓ(h + μ) = dΓ(h) + μ N`;
* `fock_gap_quadForm`, `fock_gap_of_one_particle_gap` — the **free `dΓ` lift**: with
  `h₊ ≥ μ I ≥ 0`, the vacuum has energy `0` and every vacuum-orthogonal finite-particle
  state has energy at least `μ‖·‖²`;
* `band_endpoints_tendsto`, `le_of_band` — the nested-band conclusion for the
  one-particle edge;
* `fock_mass_gap_of_certified_bands` — the composition of the two, and
  `qcdG2M4_fock_gap_of_one_particle_enclosure` — its instance for the emitted
  `g = 2, m = 4` certificate value `1.932`.

## Honest boundary

No mass gap of the physical Yang–Mills Hamiltonian is claimed.  `1.932` remains a
*certified truncated* number.  What is proved here is the implication

  *(the certified bands enclose the lowest positive one-particle energy of the fixed
  selected operator, and one band has lower end `≥ μ > 0`)*
  ⟹ *(the free second quantization has vacuum energy `0` and every vacuum-orthogonal
  finite-particle state has energy `≥ μ`)*,

together with the exact identification of the Fock gap with the one-particle edge in the
free case.  The enclosure hypothesis itself — that the finite certificate brackets the
one-particle edge of the *infinite* selected operator — is an analytic obligation that
appears here as a hypothesis, never as a conclusion.
-/

noncomputable section

namespace BookProof.FockOneParticleGap

open BookProof.FockSecondQuantization BookProof.FarisLavine BookProof.NavierStokesFlow
open Filter Topology

/-! ## 1. The free (diagonal) one-particle Hamiltonian -/

/-- The one-particle matrix of an operator diagonal in the chosen basis, with eigenvalues
`e k`: `⟪e_j, h e_k⟫ = δ_{jk} e_k`.  This is `h₊` written in a basis diagonalizing it. -/
def diagCol (e : ℕ → ℝ) : ℕ → (ℕ →₀ ℂ) := fun k => Finsupp.single k ((e k : ℝ) : ℂ)

/-- The one-particle matrix of the identity, whose second quantization is the number
operator `N`. -/
def numberCol : ℕ → (ℕ →₀ ℂ) := diagCol (fun _ => 1)

/-- The total number of quanta of a configuration. -/
def confNumber (β : Conf) : ℕ := ∑ k ∈ β.support, β k

/-- The energy of a configuration for the diagonal one-particle Hamiltonian:
`E(β) = Σ_k β_k e_k`. -/
def confEnergy (e : ℕ → ℝ) (β : Conf) : ℝ := ∑ k ∈ β.support, (β k : ℝ) * e k

/-- The Fock vacuum, as an element of the algebraic Fock space. -/
def vac : FockAlg := Finsupp.single (0 : Conf) (1 : ℂ)

theorem confNumber_zero : confNumber (0 : Conf) = 0 := by
  simp [confNumber]

theorem confEnergy_zero (e : ℕ → ℝ) : confEnergy e (0 : Conf) = 0 := by
  simp [confEnergy]

theorem confEnergy_one (β : Conf) : confEnergy (fun _ => 1) β = (confNumber β : ℝ) := by
  simp [confEnergy, confNumber]

theorem confNumber_pos {β : Conf} (h : β ≠ 0) : 1 ≤ confNumber β := by
  classical
  obtain ⟨k, hk⟩ : ∃ k, β k ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h (Finsupp.ext fun k => by simpa using hc k)
  have hmem : k ∈ β.support := Finsupp.mem_support_iff.mpr hk
  have hle : β k ≤ confNumber β :=
    Finset.single_le_sum (f := fun k => β k) (fun _ _ => Nat.zero_le _) hmem
  omega

theorem confEnergy_single (e : ℕ → ℝ) (k : ℕ) :
    confEnergy e (Finsupp.single k 1) = e k := by
  classical
  have hsupp : (Finsupp.single k 1 : Conf).support = {k} :=
    Finsupp.support_single_ne_zero k one_ne_zero
  simp [confEnergy, hsupp]

theorem confEnergy_add_const (e : ℕ → ℝ) (mu : ℝ) (β : Conf) :
    confEnergy (fun k => e k + mu) β = confEnergy e β + mu * (confNumber β : ℝ) := by
  classical
  simp only [confEnergy, confNumber, Nat.cast_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun k _ => by ring

/-- **Every non-vacuum configuration has energy at least `μ`** when every one-particle
energy is at least `μ ≥ 0`. -/
theorem le_confEnergy {e : ℕ → ℝ} {mu : ℝ} (hmu : 0 ≤ mu) (he : ∀ k, mu ≤ e k)
    {β : Conf} (hβ : β ≠ 0) : mu ≤ confEnergy e β := by
  classical
  have hstep : mu * (confNumber β : ℝ) ≤ confEnergy e β := by
    rw [confEnergy, confNumber, Nat.cast_sum, Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    have hk : (0 : ℝ) ≤ (β k : ℝ) := by positivity
    nlinarith [he k]
  have h1 : (1 : ℝ) ≤ (confNumber β : ℝ) := by exact_mod_cast confNumber_pos hβ
  nlinarith

theorem confEnergy_nonneg {e : ℕ → ℝ} (he : ∀ k, 0 ≤ e k) (β : Conf) :
    0 ≤ confEnergy e β :=
  Finset.sum_nonneg fun k _ => mul_nonneg (by positivity) (he k)

/-! ## 2. The second quantization of a diagonal one-particle Hamiltonian -/

theorem creVec_diagCol (e : ℕ → ℝ) (k : ℕ) (x : FockAlg) :
    creVec (diagCol e k) x = ((e k : ℝ) : ℂ) • creA k x := by
  classical
  rw [creVec_apply]
  by_cases h : ((e k : ℝ) : ℂ) = 0
  · rw [show (diagCol e k) = 0 by simp [diagCol, h]]
    simp [h]
  · rw [show (diagCol e k).support = {k} from Finsupp.support_single_ne_zero k h]
    simp [diagCol]

theorem creA_annA_single (k : ℕ) (β : Conf) (c : ℂ) :
    creA k (annA k (Finsupp.single β c)) = ((β k : ℝ) : ℂ) • Finsupp.single β c := by
  rw [annA_single]
  by_cases hk : β k = 0
  · simp [hk]
  · have h1 : 1 ≤ β k := Nat.one_le_iff_ne_zero.mpr hk
    rw [map_smul, creA_single, up_dn k h1]
    have hcast : ((dn k β) k : ℝ) + 1 = (β k : ℝ) := by
      rw [dn_self, Nat.cast_sub (R := ℝ) h1]; ring
    rw [hcast, smul_smul, Finsupp.smul_single, Finsupp.smul_single]
    congr 1
    have h2 : (Real.sqrt (β k) : ℂ) * (Real.sqrt (β k) : ℂ) = ((β k : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul, Real.mul_self_sqrt (by positivity)]
    simp only [smul_eq_mul]
    calc c * (Real.sqrt (β k) : ℂ) * (Real.sqrt (β k) : ℂ)
        = c * ((Real.sqrt (β k) : ℂ) * (Real.sqrt (β k) : ℂ)) := by ring
      _ = ((β k : ℝ) : ℂ) * c := by rw [h2]; ring

/-- **The second quantization of a diagonal one-particle Hamiltonian is diagonal**, with
eigenvalue the configuration energy. -/
theorem dGamma_diagCol_single (e : ℕ → ℝ) (β : Conf) (c : ℂ) :
    dGamma (diagCol e) (Finsupp.single β c)
      = ((confEnergy e β : ℝ) : ℂ) • Finsupp.single β c := by
  classical
  rw [dGamma_single]
  have hterm : ∀ k ∈ β.support,
      creVec (diagCol e k) (annA k (Finsupp.single β (1 : ℂ)))
        = (((β k : ℝ) * e k : ℝ) : ℂ) • Finsupp.single β (1 : ℂ) := by
    intro k _
    rw [creVec_diagCol, creA_annA_single, smul_smul]
    push_cast
    ring_nf
  rw [Finset.sum_congr rfl hterm, ← Finset.sum_smul,
    show (∑ k ∈ β.support, (((β k : ℝ) * e k : ℝ) : ℂ)) = ((confEnergy e β : ℝ) : ℂ) by
      rw [confEnergy]; push_cast; ring,
    smul_smul, Finsupp.smul_single, Finsupp.smul_single]
  congr 1
  simp [mul_comm]

/-- The coordinatewise form of `dGamma_diagCol_single`. -/
theorem dGamma_diagCol_apply (e : ℕ → ℝ) (u : FockAlg) (β : Conf) :
    dGamma (diagCol e) u β = ((confEnergy e β : ℝ) : ℂ) * u β := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    rw [map_add, Finsupp.add_apply, hf, hg, Finsupp.add_apply]
    ring
  | single γ c =>
    rw [dGamma_diagCol_single]
    by_cases h : β = γ
    · subst h; simp
    · simp [h]

/-- **The vacuum is annihilated**: `dΓ(h₊) Ω = 0`. -/
theorem dGamma_diagCol_vac (e : ℕ → ℝ) : dGamma (diagCol e) vac = 0 := by
  rw [vac, dGamma_diagCol_single, confEnergy_zero]
  simp

/-- **The number operator annihilates the vacuum**: `N Ω = 0`. -/
theorem numberOp_vac : dGamma numberCol vac = 0 := dGamma_diagCol_vac _

/-- **A one-particle state is an eigenvector with the one-particle energy.** -/
theorem dGamma_diagCol_one_particle (e : ℕ → ℝ) (k : ℕ) :
    dGamma (diagCol e) (Finsupp.single (Finsupp.single k 1) (1 : ℂ))
      = ((e k : ℝ) : ℂ) • Finsupp.single (Finsupp.single k 1) (1 : ℂ) := by
  rw [dGamma_diagCol_single, confEnergy_single]

/-- **The free number-operator shift** `dΓ(h₊) = dΓ(h − E₀I) + μ N`: shifting every
one-particle energy by `μ` adds `μ` times the number operator.  The vacuum is unchanged
(`numberOp_vac`), while every non-vacuum state gains at least `μ`. -/
theorem dGamma_diagCol_shift (e : ℕ → ℝ) (mu : ℝ) (u : FockAlg) :
    dGamma (diagCol fun k => e k + mu) u
      = dGamma (diagCol e) u + ((mu : ℝ) : ℂ) • dGamma numberCol u := by
  refine Finsupp.ext fun β => ?_
  rw [Finsupp.add_apply, Finsupp.smul_apply, dGamma_diagCol_apply, dGamma_diagCol_apply,
    numberCol, dGamma_diagCol_apply, confEnergy_add_const, confEnergy_one]
  push_cast
  simp only [smul_eq_mul]
  ring

/-! ## 3. The Fock gap of a free second quantization -/

theorem conj_mul_re (z : ℂ) : ((starRingEnd ℂ) z * z).re = ‖z‖ ^ 2 := by
  have h : (starRingEnd ℂ) z * z = ((Complex.normSq z : ℝ) : ℂ) := by
    rw [mul_comm]; exact Complex.mul_conj z
  rw [h, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

theorem norm_toLp_sq (u : FockAlg) : ‖toLp u‖ ^ 2 = ∑ α ∈ u.support, ‖u α‖ ^ 2 := by
  have h1 : (inner ℂ (toLp u) (toLp u) : ℂ).re = ‖toLp u‖ ^ 2 := by
    rw [inner_self_eq_norm_sq_to_K]
    norm_cast
  rw [← h1, inner_toLp u u, Complex.re_sum]
  exact Finset.sum_congr rfl fun α _ => conj_mul_re (u α)

/-- The Fock energy of a finite-particle state is the weighted sum of the configuration
energies. -/
theorem re_inner_dGamma_diagCol (e : ℕ → ℝ) (u : FockAlg) :
    (inner ℂ (toLp u) (toLp (dGamma (diagCol e) u)) : ℂ).re
      = ∑ α ∈ u.support, confEnergy e α * ‖u α‖ ^ 2 := by
  rw [inner_toLp u (dGamma (diagCol e) u), Complex.re_sum]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [dGamma_diagCol_apply,
    show (starRingEnd ℂ) (u α) * (((confEnergy e α : ℝ) : ℂ) * u α)
        = ((confEnergy e α : ℝ) : ℂ) * ((starRingEnd ℂ) (u α) * u α) by ring,
    Complex.re_ofReal_mul, conj_mul_re]

/-- **The free `dΓ` lift, quadratic-form version.**  If every one-particle energy is at
least `μ ≥ 0`, then every finite-particle state orthogonal to the vacuum has Fock energy
at least `μ‖u‖²`. -/
theorem fock_gap_quadForm {e : ℕ → ℝ} {mu : ℝ} (hmu : 0 ≤ mu) (he : ∀ k, mu ≤ e k)
    {u : FockAlg} (h0 : u 0 = 0) :
    mu * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma (diagCol e) u)) : ℂ).re := by
  rw [re_inner_dGamma_diagCol, norm_toLp_sq, Finset.mul_sum]
  refine Finset.sum_le_sum fun α hα => ?_
  have hα0 : α ≠ 0 := by
    rintro rfl
    exact (Finsupp.mem_support_iff.mp hα) h0
  exact mul_le_mul_of_nonneg_right (le_confEnergy hmu he hα0) (sq_nonneg ‖u α‖)

/-- The vacuum component of a finite-particle state is its inner product with `Ω`. -/
theorem inner_vac (u : FockAlg) : (inner ℂ (toLp vac) (toLp u) : ℂ) = u 0 := by
  classical
  have hs : vac.support = {(0 : Conf)} := Finsupp.support_single_ne_zero _ one_ne_zero
  rw [inner_toLp vac u, hs]
  simp [vac]

/-- **The free `dΓ` lift on the Fock space.**  With `h₊ ≥ μ I ≥ 0` in the diagonalizing
basis: the vacuum has energy `0`, and every vacuum-orthogonal finite-occupation state has
energy at least `μ‖x‖²`. -/
theorem fock_gap_of_one_particle_gap {e : ℕ → ℝ} {mu : ℝ} (hmu : 0 ≤ mu)
    (he : ∀ k, mu ≤ e k) :
    dGammaOp (diagCol e) (fockEquiv vac) = 0 ∧
      ∀ x : lpFiniteModes Conf, (inner ℂ (toLp vac) ((x : Fock)) : ℂ) = 0 →
        mu * ‖(x : Fock)‖ ^ 2 ≤ quadForm (dGammaOp (diagCol e)) x := by
  constructor
  · rw [coe_dGammaOp, LinearEquiv.symm_apply_apply, dGamma_diagCol_vac]
    exact map_zero toLpL
  · intro x hx
    rw [quadForm, coe_dGammaOp, coe_fockEquiv_symm x]
    rw [coe_fockEquiv_symm x] at hx
    exact fock_gap_quadForm hmu he (by rwa [inner_vac] at hx)

/-- **Sharpness of the lift.**  The one-particle energies really are Fock energies: the
state `a†(e_k) Ω` has energy exactly `e k`.  With `fock_gap_of_one_particle_gap` this says
that the Fock gap of a free second quantization *is* the lowest one-particle energy. -/
theorem fock_energy_one_particle (e : ℕ → ℝ) (k : ℕ) :
    (inner ℂ (toLp (Finsupp.single (Finsupp.single k 1) (1 : ℂ)))
        (toLp (dGamma (diagCol e) (Finsupp.single (Finsupp.single k 1) (1 : ℂ)))) : ℂ).re
      = e k := by
  classical
  rw [re_inner_dGamma_diagCol,
    show (Finsupp.single (Finsupp.single k 1) (1 : ℂ)).support = {Finsupp.single k 1} from
      Finsupp.support_single_ne_zero _ one_ne_zero]
  simp [confEnergy_single]


end BookProof.FockOneParticleGap
end
