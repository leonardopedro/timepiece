import BookProof.ChapterFockOneParticleGap.Part1
import BookProof.ChapterFockOneParticleGap.Part2

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
