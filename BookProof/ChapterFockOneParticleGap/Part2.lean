import Mathlib
import BookProof.ChapterFockSecondQuantization
import BookProof.ChapterSirkCertifiedGap
import BookProof.ChapterSirkRitzSpectrum
import BookProof.ChapterSpectralGapStability
import BookProof.ChapterFockOneParticleGap.Part1

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
/-! ### The Fock gap *is* the one-particle edge -/

/-- The set of energies of the non-vacuum configurations. -/
def nonvacuumEnergies (e : ℕ → ℝ) : Set ℝ :=
  {x | ∃ β : Conf, β ≠ 0 ∧ x = confEnergy e β}

theorem iInf_le_confEnergy {e : ℕ → ℝ} (he : ∀ k, 0 ≤ e k) {β : Conf} (hβ : β ≠ 0) :
    (⨅ k, e k) ≤ confEnergy e β := by
  classical
  have hbdd : BddBelow (Set.range e) := ⟨0, by rintro x ⟨k, rfl⟩; exact he k⟩
  obtain ⟨k0, hk0⟩ : ∃ k, k ∈ β.support := by
    by_contra hc
    push_neg at hc
    exact hβ (Finsupp.ext fun k => by
      simpa using Finsupp.notMem_support_iff.mp (hc k))
  have hterm : e k0 ≤ (β k0 : ℝ) * e k0 := by
    have h1 : (1 : ℝ) ≤ (β k0 : ℝ) := by
      have h2 : 1 ≤ β k0 := Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp hk0)
      exact_mod_cast h2
    nlinarith [he k0]
  have hsum : (β k0 : ℝ) * e k0 ≤ confEnergy e β :=
    Finset.single_le_sum (f := fun k => (β k : ℝ) * e k)
      (fun k _ => mul_nonneg (by positivity) (he k)) hk0
  exact le_trans (le_trans (ciInf_le hbdd k0) hterm) hsum

/-- **The Fock gap of a free second quantization is exactly the one-particle edge.**  For a
nonnegative one-particle spectrum, the infimum of the non-vacuum Fock energies is the
infimum of the one-particle energies: the lower bound is `iInf_le_confEnergy`, and it is
attained in the limit by the one-particle states `a†(e_k) Ω`. -/
theorem sInf_nonvacuumEnergies {e : ℕ → ℝ} (he : ∀ k, 0 ≤ e k) :
    sInf (nonvacuumEnergies e) = ⨅ k, e k := by
  classical
  have hbdd : BddBelow (nonvacuumEnergies e) := by
    refine ⟨0, ?_⟩
    rintro x ⟨β, -, rfl⟩
    exact confEnergy_nonneg he _
  have hmem : ∀ k, e k ∈ nonvacuumEnergies e :=
    fun k => ⟨Finsupp.single k 1, by simp, (confEnergy_single e k).symm⟩
  refine le_antisymm (le_ciInf fun k => csInf_le hbdd (hmem k)) ?_
  refine le_csInf ⟨e 0, hmem 0⟩ ?_
  rintro x ⟨β, hβ, rfl⟩
  exact iInf_le_confEnergy he hβ

/-! ## 4. Nested certified bands determine the one-particle edge -/

/-- **The nested-band conclusion.**  If every certified interval `[lo m, hi m]` encloses
the same number `lam` — the lowest positive one-particle energy of the *fixed* selected
operator — and the widths vanish, then the certified endpoints converge to `lam`. -/
theorem band_endpoints_tendsto {lo hi : ℕ → ℝ} {lam : ℝ}
    (hmem : ∀ m, lam ∈ Set.Icc (lo m) (hi m))
    (hwidth : Tendsto (fun m => hi m - lo m) atTop (𝓝 0)) :
    Tendsto lo atTop (𝓝 lam) ∧ Tendsto hi atTop (𝓝 lam) := by
  have hlo : Tendsto lo atTop (𝓝 lam) := by
    have hsq : ∀ m, lam - (hi m - lo m) ≤ lo m := fun m => by
      have := (hmem m).2; linarith
    have hup : ∀ m, lo m ≤ lam := fun m => (hmem m).1
    have h1 : Tendsto (fun m => lam - (hi m - lo m)) atTop (𝓝 (lam - 0)) :=
      tendsto_const_nhds.sub hwidth
    rw [sub_zero] at h1
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le h1 tendsto_const_nhds hsq hup
  refine ⟨hlo, ?_⟩
  have h2 : Tendsto (fun m => (hi m - lo m) + lo m) atTop (𝓝 (0 + lam)) := hwidth.add hlo
  simpa using h2

/-- A single certified band with a positive lower end already forces the enclosed edge to
be at least that lower end. -/
theorem le_of_band {lo hi : ℕ → ℝ} {lam mu : ℝ} (hmem : ∀ m, lam ∈ Set.Icc (lo m) (hi m))
    {m : ℕ} (hlo : mu ≤ lo m) : mu ≤ lam :=
  le_trans hlo (hmem m).1

/-! ## 5. The composition: certified bands ⟹ Fock mass gap (free case) -/

/-- **The composition theorem.**  Hypotheses, all explicit:

* `hband` — every certified interval encloses `lam`, the lowest positive one-particle
  energy of the fixed selected operator `h₊` (the analytic enclosure obligation);
* `hwidth` — the certified widths vanish;
* `hlo` — one certified interval has lower end `≥ μ`;
* `hedge` — `lam` really is a lower bound for the one-particle spectrum in the
  diagonalizing basis, i.e. `h₊ ≥ lam I`;
* `hmu` — `0 ≤ μ`.

Conclusions: the certified lower endpoints converge to `lam`, `μ ≤ lam`, the vacuum has
Fock energy `0`, and every vacuum-orthogonal finite-particle state has Fock energy at
least `μ‖u‖²`. -/
theorem fock_mass_gap_of_certified_bands {e : ℕ → ℝ} {lo hi : ℕ → ℝ} {lam mu : ℝ}
    (hmu : 0 ≤ mu) (hband : ∀ m, lam ∈ Set.Icc (lo m) (hi m))
    (hwidth : Tendsto (fun m => hi m - lo m) atTop (𝓝 0))
    {m₀ : ℕ} (hlo : mu ≤ lo m₀) (hedge : ∀ k, lam ≤ e k) :
    Tendsto lo atTop (𝓝 lam) ∧ mu ≤ lam ∧ dGamma (diagCol e) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 →
        mu * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma (diagCol e) u)) : ℂ).re := by
  refine ⟨(band_endpoints_tendsto hband hwidth).1, le_of_band hband hlo,
    dGamma_diagCol_vac e, fun u h0 => ?_⟩
  exact fock_gap_quadForm hmu (fun k => le_trans (le_of_band hband hlo) (hedge k)) h0

/-- **The emitted `g = 2, m = 4` certificate, read as a one-particle enclosure.**  The
certificate number `1.932` is a *truncated* certified gap; if — and only if — its band is
known to enclose the lowest positive one-particle energy `lam` of the fixed selected
operator `h₊`, and `h₊ ≥ lam I` in the diagonalizing basis, then the free second
quantization has vacuum energy `0` and a Fock gap of at least `1.932`.  The enclosure is a
hypothesis, not a conclusion. -/
theorem qcdG2M4_fock_gap_of_one_particle_enclosure {e : ℕ → ℝ} {lo hi : ℕ → ℝ} {lam : ℝ}
    (hband : ∀ m, lam ∈ Set.Icc (lo m) (hi m)) {m₀ : ℕ}
    (hlo : (1.932 : ℝ) ≤ lo m₀) (hedge : ∀ k, lam ≤ e k) :
    (1.932 : ℝ) ≤ lam ∧ dGamma (diagCol e) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 →
        (1.932 : ℝ) * ‖toLp u‖ ^ 2
          ≤ (inner ℂ (toLp u) (toLp (dGamma (diagCol e) u)) : ℂ).re := by
  have hlam : (1.932 : ℝ) ≤ lam := le_of_band hband hlo
  refine ⟨hlam, dGamma_diagCol_vac e, fun u h0 => ?_⟩
  exact fock_gap_quadForm (by norm_num) (fun k => le_trans hlam (hedge k)) h0

/-- The number `1.932` above is exactly the lower end of the recorded `g = 2, m = 4`
certificate of `ChapterSirkCertifiedGap`. -/
theorem qcdG2M4_lower_eq : BookProof.SirkCertifiedGap.qcdG2M4.lower = 1.932 :=
  BookProof.SirkCertifiedGap.qcdG2M4_lower

/-! ## 6. Reading a parity-labelled certificate as a one-particle enclosure

The emitted certificate is labelled by parity sectors.  Using it for the `dGamma` theorems
above requires the **representation translation**: that the even sector ground value is the
outer-vacuum energy and the odd sector ground value is the lowest one-particle energy.  That
translation is a property of the concrete truncation, not a generic fact, so it appears
below as two explicit hypotheses; what the theorem adds is that *once they hold*, the
certified parity lower bound is a lower bound for the one-particle edge, and may then be
fed to `fock_mass_gap_of_certified_bands`. -/

section ParityTranslation

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]

open BookProof.SirkCertifiedGap

/-- **The parity-to-one-particle translation.**  Hypotheses: the certificate's two numbers
are the sector Ritz difference and the assembled width (`hgap`, `hwidth`), the two sector
enclosures hold (`hEven`, `hOdd`), and the *representation translation* holds — the even
sector ground value is the outer-vacuum energy `0` (`hvac`) and the odd sector ground value is
the one-particle edge `lam` (`hone`).  Conclusion: the certified lower bound is a lower
bound for the one-particle edge.  Nothing here asserts the translation itself. -/
theorem one_particle_edge_ge_of_parity_certificate {T P : E →ₗ[ℂ] E} (c : GapCertificate)
    {thetaE thetaO deltaE deltaO lam : ℝ}
    (hgap : c.gap = thetaO - thetaE) (hwidth : c.width = deltaO + deltaE)
    (hEven : sectorGround T P 1 ≤ thetaE + deltaE)
    (hOdd : thetaO - deltaO ≤ sectorGround T P (-1))
    (hvac : sectorGround T P 1 = 0) (hone : sectorGround T P (-1) = lam) :
    c.lower ≤ lam := by
  have h := gap_ge_of_certificate (T := T) (P := P) c hgap hwidth hEven hOdd
  rw [hvac, hone] at h
  linarith

end ParityTranslation

/-! ## 7. From the spectral edge of an actual one-particle operator to the Fock gap

The sections above take the one-particle data as the sequence of eigenvalues `e`.  This
section starts instead from a *bounded self-adjoint operator* `A` on a Hilbert space with a
Hilbert basis of eigenvectors — the situation the shift-inverted Hashimoto/SIRK route
produces — and reads its eigenvalues off the basis.  The certified bands are then required
to enclose `sInf (spectrum ℝ A)`, the actual spectral edge, and the conclusion is the Fock
gap of the free second quantization. -/

section OperatorEdge

open BookProof.ChapterSirkRitzSpectrum

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F] [CompleteSpace F]

/-- A lower bound for the spectrum of a bounded self-adjoint operator is a lower bound for
its eigenvalues along any Hilbert basis of eigenvectors. -/
theorem le_eigenvalue_of_le_spectrum {A : F →L[ℂ] F} (hA : IsSelfAdjoint A)
    {b : HilbertBasis ℕ ℂ F} {e : ℕ → ℝ}
    (heig : ∀ k, A (b k) = ((e k : ℝ) : ℂ) • b k) {mu : ℝ}
    (hspec : ∀ lam ∈ spectrum ℝ A, mu ≤ lam) : ∀ k, mu ≤ e k := by
  intro k
  have hray := (le_rayleigh_iff_le_spectrum A hA mu).mpr hspec (b k)
  have hnorm : ‖b k‖ = 1 := b.orthonormal.1 k
  have hinner : (inner ℂ (b k) (A (b k)) : ℂ) = ((e k : ℝ) : ℂ) := by
    rw [heig k, inner_smul_right, inner_self_eq_norm_sq_to_K, hnorm]
    norm_num
  rw [hinner, hnorm] at hray
  simpa using hray

/-- **The `dGamma` lift from the spectral edge of the one-particle operator.**  If the
spectrum of the bounded self-adjoint one-particle operator `A` is bounded below by `μ ≥ 0`
and `b` is a Hilbert basis of eigenvectors with eigenvalues `e`, then the free second
quantization built from `e` annihilates the vacuum and has Fock gap at least `μ`. -/
theorem fock_gap_of_operator_spectral_edge {A : F →L[ℂ] F} (hA : IsSelfAdjoint A)
    {b : HilbertBasis ℕ ℂ F} {e : ℕ → ℝ}
    (heig : ∀ k, A (b k) = ((e k : ℝ) : ℂ) • b k) {mu : ℝ} (hmu : 0 ≤ mu)
    (hspec : ∀ lam ∈ spectrum ℝ A, mu ≤ lam) :
    dGamma (diagCol e) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 →
        mu * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma (diagCol e) u)) : ℂ).re :=
  ⟨dGamma_diagCol_vac e,
    fun _ h0 => fock_gap_quadForm hmu (le_eigenvalue_of_le_spectrum hA heig hspec) h0⟩

/-- **The continuum-style transfer, for a bounded self-adjoint one-particle operator.**
Certified bands that enclose the actual spectral edge `sInf (spectrum ℝ A)` and shrink to a
point determine it; if one band has lower end `μ ≥ 0`, the edge is at least `μ` and the free
second quantization has vacuum energy `0` and Fock gap at least `μ`.  The enclosure of the
edge by the certified bands is a hypothesis. -/
theorem fock_mass_gap_of_certified_bands_operator {A : F →L[ℂ] F} (hA : IsSelfAdjoint A)
    {b : HilbertBasis ℕ ℂ F} {e : ℕ → ℝ}
    (heig : ∀ k, A (b k) = ((e k : ℝ) : ℂ) • b k) {lo hi : ℕ → ℝ} {mu : ℝ} (hmu : 0 ≤ mu)
    (hband : ∀ m, sInf (spectrum ℝ A) ∈ Set.Icc (lo m) (hi m))
    (hwidth : Tendsto (fun m => hi m - lo m) atTop (𝓝 0))
    {m₀ : ℕ} (hlo : mu ≤ lo m₀) :
    Tendsto lo atTop (𝓝 (sInf (spectrum ℝ A))) ∧ mu ≤ sInf (spectrum ℝ A) ∧
      dGamma (diagCol e) vac = 0 ∧
      ∀ u : FockAlg, u 0 = 0 →
        mu * ‖toLp u‖ ^ 2 ≤ (inner ℂ (toLp u) (toLp (dGamma (diagCol e) u)) : ℂ).re := by
  have hedge : mu ≤ sInf (spectrum ℝ A) := le_of_band hband hlo
  have hspec : ∀ lam ∈ spectrum ℝ A, mu ≤ lam := fun lam hlam =>
    le_trans hedge (csInf_le (spectrum_real_bddBelow A hA) hlam)
  obtain ⟨hvac, hgap⟩ := fock_gap_of_operator_spectral_edge hA heig hmu hspec
  exact ⟨(band_endpoints_tendsto hband hwidth).1, hedge, hvac, hgap⟩

end OperatorEdge

end BookProof.FockOneParticleGap

end
