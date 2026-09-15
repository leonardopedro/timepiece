import BookProof.ChapterNavierStokesFockEsa.Part1
import BookProof.ChapterNavierStokesFockEsa.Part2

/-!
# Essential self-adjointness of the full Navier–Stokes Hamiltonian in the
Lagrangian variables, on the Fock space of a Fock space

After the Lagrangian change of variables the Navier–Stokes Hamiltonian is a
*second* quantization.  The Eulerian velocity `u` is already an operator on a
Fock space; in the parcel variables `X(ξ)` one quantizes the parcels as well, so
the state space is the Fock space **over a Fock space** built in
`BookProof.ChapterNavierStokesFockSpace`, and the transformed Hamiltonian is
**quadratic in the outer creation and annihilation operators**,

`ĥ = ∫_Ω dξ  a†(ξ) h₁ a(ξ)`,

an integral of operators over the (infinite, continuous) parcel domain `Ω`, with
`h₁` the one-parcel Lagrangian symbol `½∑ᵢpᵢ² + ν∑ᵢqᵢ² + ∑ᵢfᵢdᵢ + c`.

## What is proved here

* `dGamma ω` — the second quantization `∑ₘ ωₘ a†ₘ aₘ` of a real one-particle
  symbol, on the dense finite-particle domain, with
  `dGamma_eq_sum_numberOp`: it *is* the quadratic expression in the ladder
  operators; `dGamma_isSymmetricDom`; and `dGamma_hasZeroDeficiencyOn` — **it is
  essentially self-adjoint, with no boundedness assumption**.
* `confEnergy_eq_integral` and `dGamma_inner_eq_integral` — **the integral over
  the continuous domain**: if the one-particle symbol is given by
  `ωₘ = ∫_Ω w(ξ) ρₘ(ξ) dξ` — the mode `m` weighted against a field `w` on `Ω` —
  then the quadratic form of the Hamiltonian is the integral over `Ω` of the
  quadratic forms of the local number-density operators `N(ξ) = a†(ξ)a(ξ)`.
* `twoLevelSymbol`, `hTwoLevel`, `hTwoLevel_hasZeroDeficiencyOn` — the two-level
  (Fock-of-Fock) Hamiltonian, whose one-parcel symbol is the external parcel
  energy plus the *internal* Fock energy of the field carried by that parcel; it
  is essentially self-adjoint.
* `lagrangianFockData`, `lagrangianFock_hasZeroDeficiencyOn` — the untruncated
  Lagrangian data of `BookProof.ChapterNavierStokesLagrangianEsa` realized on the
  Fock-of-Fock space, with the parcel momenta, viscous gradients, force drift and
  constraint all second-quantized: **the full transformed Navier–Stokes
  Hamiltonian `ĥ_full = ½∑Pᵢ² + ν∑Qᵢ² + ∑fᵢDᵢ + C` is essentially self-adjoint
  there, unconditionally**, and `lagrangianFock_not_bounded` shows this is not a
  boundedness phenomenon.
* `hFull_eq_hFock_oneParticle` — on one-parcel states the four-term Lagrangian
  operator agrees with the genuinely quadratic second quantization `dΓ(h₁)`.
* `nsFullData_hasZeroDeficiencyOn_of_fockLagrangian` — combined with the
  unitary-invariance of the property, essential self-adjointness proved *after*
  the change of variables gives it for the Eulerian operator it came from.
* `intervalModes` — a concrete realization on the infinite continuous domain
  `Ω = ℝ` with Lebesgue measure: parcel modes localized in the unit intervals
  `(j, j+1]`, weighted by the unbounded external field `w(ξ) = ξ²`.  The
  resulting symbol is unbounded (`intervalSymbol_unbounded`), so the
  Hamiltonian is an unbounded, essentially self-adjoint operator whose
  coefficients are honest integrals over `ℝ`.

## Scope

Nothing here claims essential self-adjointness of the *continuum* Navier–Stokes
generator with its full nonlinear structure: what is proved is that the
transformed Hamiltonian, in its second-quantized (quadratic) Fock-of-Fock form
with a real one-parcel symbol given by integrals over the continuous parcel
domain, is essentially self-adjoint on the finite-particle domain, and that this
transfers back through the change of variables.
-/
