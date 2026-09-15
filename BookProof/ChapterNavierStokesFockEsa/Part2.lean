import Mathlib
import BookProof.ChapterNavierStokesFockSpace
import BookProof.ChapterNavierStokesFockEsa.Part1

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

open MeasureTheory

namespace BookProof.NavierStokesFlow

namespace FockOfFock

open FullEsa LagrangianEsa
/-! ## The transformed Navier–Stokes Hamiltonian on the Fock-of-Fock space -/

section LagrangianFock

variable {M : Type*} [DecidableEq M]

/-- **The one-parcel Lagrangian symbol**
`h₁ = ½∑ᵢpᵢ² + ν∑ᵢqᵢ² + ∑ᵢfᵢdᵢ + c`: the advective (kinetic) energy of the
parcel, its viscous energy, the work of the external force and the
volume-preservation constraint. -/
noncomputable def lagSymbol (nu : ℝ) (p q dr : Fin 3 → M → ℝ) (force : Fin 3 → ℝ)
    (cst : M → ℝ) : M → ℝ := fun m =>
  (1 / 2) * (∑ i : Fin 3, p i m ^ 2) + nu * (∑ i : Fin 3, q i m ^ 2)
    + (∑ i : Fin 3, force i * dr i m) + cst m

/-- **The full transformed Navier–Stokes Hamiltonian in its second-quantized
form** `ĥ = ∑ₘ h₁(m) a†ₘ aₘ`: quadratic in the parcel creation and annihilation
operators. -/
noncomputable def hFockLag (nu : ℝ) (p q dr : Fin 3 → M → ℝ) (force : Fin 3 → ℝ) (cst : M → ℝ) :
    FockDom M →ₗ[ℂ] FockDom M :=
  dGamma (lagSymbol nu p q dr force cst)

omit [DecidableEq M] in
/-- **Essential self-adjointness of the second-quantized transformed
Hamiltonian**, unconditionally: no boundedness of the symbol is assumed. -/
theorem hFockLag_hasZeroDeficiencyOn (nu : ℝ) (p q dr : Fin 3 → M → ℝ) (force : Fin 3 → ℝ)
    (cst : M → ℝ) :
    HasZeroDeficiencyOn (FockDom M) (hFockLag nu p q dr force cst) :=
  dGamma_hasZeroDeficiencyOn _

/-- **The untruncated Lagrangian Navier–Stokes data realized on the Fock space of
a Fock space.**  The parcel momenta, the viscous gradients, the force drift
generators and the volume-preservation constraint are all second quantizations
of real one-parcel symbols on the dense finite-particle domain. -/
noncomputable def lagrangianFockData (nu : ℝ) (hnu : 0 ≤ nu) (p q dr : Fin 3 → M → ℝ)
    (force : Fin 3 → ℝ) (cst : M → ℝ) : LagrangianFullData (FockL2 M) where
  D := FockDom M
  P := fun i => dGamma (p i)
  Q := fun i => dGamma (q i)
  drive := fun i => dGamma (dr i)
  force := force
  constraintOp := dGamma cst
  nu := nu
  dense := fockDom_dense
  P_symm := fun _ => dGamma_isSymmetricDom _
  Q_symm := fun _ => dGamma_isSymmetricDom _
  drive_symm := fun _ => dGamma_isSymmetricDom _
  constraint_symm := dGamma_isSymmetricDom _
  nu_nonneg := hnu

omit [DecidableEq M] in
/-- **Essential self-adjointness of the full transformed Navier–Stokes
Hamiltonian `ĥ_full = ½∑Pᵢ² + ν∑Qᵢ² + ∑fᵢDᵢ + C` on the Fock space of a Fock
space**, unconditionally.  The occupation-number states are a total family of
common eigenvectors of all the constituents — this is the Lagrangian momentum
representation — so the four-term transformed operator has vanishing adjoint
deficiency on the dense finite-particle domain, with no boundedness assumption
anywhere. -/
theorem lagrangianFock_hasZeroDeficiencyOn (nu : ℝ) (hnu : 0 ≤ nu) (p q dr : Fin 3 → M → ℝ)
    (force : Fin 3 → ℝ) (cst : M → ℝ) :
    HasZeroDeficiencyOn (lagrangianFockData nu hnu p q dr force cst).D
      (lagrangianFockData nu hnu p q dr force cst).hFull := by
  classical
  exact (lagrangianFockData nu hnu p q dr force cst).hasZeroDeficiencyOn_of_commonEigenvectors
    (fun n : Conf M => (fockBasis n : FockDom M))
    (fun i n => confEnergy (p i) n) (fun i n => confEnergy (q i) n)
    (fun i n => confEnergy (dr i) n) (fun n => confEnergy cst n)
    (fun i n => dGamma_basis (p i) n) (fun i n => dGamma_basis (q i) n)
    (fun i n => dGamma_basis (dr i) n) (fun n => dGamma_basis cst n)
    lpBasis_total

omit [DecidableEq M] in
/-- The transformed Hamiltonian on the Fock-of-Fock space is genuinely
unbounded whenever one of its symbols is. -/
theorem lagrangianFock_not_bounded (nu : ℝ) (p q dr : Fin 3 → M → ℝ) (force : Fin 3 → ℝ)
    (cst : M → ℝ) (h : ∀ C : ℝ, ∃ m, C < |lagSymbol nu p q dr force cst m|) :
    ¬ ((∃ C : ℝ, ∀ f : FockDom M, ‖hFockLag nu p q dr force cst f‖ ≤ C * ‖f‖)) :=
  dGamma_not_bounded _ h

/-- **On a one-parcel state the four-term Lagrangian operator is exactly the
second quantization of the one-parcel symbol**: the two descriptions of the
transformed Hamiltonian agree where they must. -/
theorem hFull_eq_hFock_oneParticle (nu : ℝ) (hnu : 0 ≤ nu) (p q dr : Fin 3 → M → ℝ)
    (force : Fin 3 → ℝ) (cst : M → ℝ) (m : M) :
    (lagrangianFockData nu hnu p q dr force cst).hFull (fockBasis (Finsupp.single m 1))
      = hFockLag nu p q dr force cst (fockBasis (Finsupp.single m 1)) := by
  classical
  have hsingle : ∀ ω : M → ℝ, confEnergy ω (Finsupp.single m 1 : Conf M) = ω m := by
    intro ω
    simp [confEnergy, Finsupp.support_single_ne_zero _ (one_ne_zero)]
  have heig := (lagrangianFockData nu hnu p q dr force cst).hFull_eigenvector
    (v := (fockBasis (Finsupp.single m 1) : FockDom M))
    (p := fun i => p i m) (q := fun i => q i m) (dr := fun i => dr i m) (c := cst m)
    (fun i => by simpa [hsingle] using dGamma_basis (p i) (Finsupp.single m 1))
    (fun i => by simpa [hsingle] using dGamma_basis (q i) (Finsupp.single m 1))
    (fun i => by simpa [hsingle] using dGamma_basis (dr i) (Finsupp.single m 1))
    (by simpa [hsingle] using dGamma_basis cst (Finsupp.single m 1))
  rw [heig, hFockLag, dGamma_basis, hsingle]
  rfl

end LagrangianFock

/-! ## Back to the Eulerian operator -/

section Transfer

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
variable {M : Type*} [DecidableEq M]

omit [DecidableEq M] in
/-- **Essential self-adjointness of the full Navier–Stokes Hamiltonian, obtained
after the Lagrangian change of variables on the Fock space of a Fock space.**
If a unitary change of variables carries untruncated Eulerian Navier–Stokes data
onto the second-quantized Lagrangian data above, then the Eulerian Hamiltonian
is essentially self-adjoint — the Fock-of-Fock computation is done once and
transfers back. -/
theorem nsFullData_hasZeroDeficiencyOn_of_fockLagrangian (d : FullEsa.NSFullData F) (nu : ℝ)
    (hnu : 0 ≤ nu) (p q dr : Fin 3 → M → ℝ) (force : Fin 3 → ℝ) (cst : M → ℝ)
    (W : F ≃ₗᵢ[ℂ] FockL2 M)
    (hmap : ∀ x : d.D, W (x : F) ∈ (lagrangianFockData nu hnu p q dr force cst).D)
    (hsurj : ∀ y : (lagrangianFockData nu hnu p q dr force cst).D,
      ∃ x : d.D, W (x : F) = (y : FockL2 M))
    (hint : ∀ x : d.D, ((lagrangianFockData nu hnu p q dr force cst).hFull
        ⟨W (x : F), hmap x⟩ : FockL2 M) = W ((d.hamiltonian x : F))) :
    HasZeroDeficiencyOn d.D d.hamiltonian :=
  LagrangianEsa.NSFullData.hasZeroDeficiencyOn_of_lagrangian d
    (lagrangianFockData nu hnu p q dr force cst) W hmap hsurj hint
    (lagrangianFock_hasZeroDeficiencyOn nu hnu p q dr force cst)

end Transfer

/-! ## A concrete realization over the infinite continuous domain `ℝ` -/

section IntervalModes

variable {K : Type*} [DecidableEq K]

/-- The density of the parcel mode `j`: the parcel is localized in the unit
interval `(j, j+1]` of the parcel domain `ℝ`. -/
noncomputable def intervalDens (j : ℕ) : ℝ → ℝ :=
  Set.indicator (Set.Ioc (j : ℝ) ((j : ℝ) + 1)) (fun _ => 1)

/-- The external field on the parcel domain, `w(ξ) = ξ²` — unbounded, as an
external potential on an infinite domain generally is. -/
noncomputable def extField : ℝ → ℝ := fun ξ => ξ ^ 2

theorem intervalDens_mul_extField_eq (j : ℕ) :
    (fun ξ => extField ξ * intervalDens j ξ)
      = Set.indicator (Set.Ioc (j : ℝ) ((j : ℝ) + 1)) (fun ξ => ξ ^ 2) := by
  funext ξ
  by_cases hx : ξ ∈ Set.Ioc (j : ℝ) ((j : ℝ) + 1) <;>
    simp [extField, intervalDens, Set.indicator_of_mem, Set.indicator_of_notMem, hx]

theorem intervalDens_integrable (j : ℕ) :
    Integrable (fun ξ => extField ξ * intervalDens j ξ) volume := by
  rw [intervalDens_mul_extField_eq, integrable_indicator_iff measurableSet_Ioc]
  exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by linarith)).1
    ((continuous_pow 2).intervalIntegrable _ _)

/-- The one-parcel symbol produced by the external field: the honest integral
`∫_ℝ ξ² ρⱼ(ξ) dξ` over the infinite continuous parcel domain. -/
theorem intervalSymbol_eq (j : ℕ) :
    symbolOfIntegral volume extField intervalDens j = (((j : ℝ) + 1) ^ 3 - (j : ℝ) ^ 3) / 3 := by
  rw [symbolOfIntegral, intervalDens_mul_extField_eq, integral_indicator measurableSet_Ioc,
    ← intervalIntegral.integral_of_le (by linarith : (j : ℝ) ≤ (j : ℝ) + 1), integral_pow]
  ring

/-- The resulting symbol is **unbounded**. -/
theorem intervalSymbol_unbounded :
    ∀ C : ℝ, ∃ j : ℕ, C < |symbolOfIntegral volume extField intervalDens j| := by
  intro C
  obtain ⟨j, hj⟩ := exists_nat_gt (max C 0)
  refine ⟨j, ?_⟩
  have hC : C < (j : ℝ) := lt_of_le_of_lt (le_max_left _ _) hj
  have hj0 : (0 : ℝ) ≤ (j : ℝ) := Nat.cast_nonneg j
  have hval : symbolOfIntegral volume extField intervalDens j
      = (((j : ℝ) + 1) ^ 3 - (j : ℝ) ^ 3) / 3 := intervalSymbol_eq j
  have hge : (j : ℝ) ≤ (((j : ℝ) + 1) ^ 3 - (j : ℝ) ^ 3) / 3 := by nlinarith
  have hpos : 0 ≤ (((j : ℝ) + 1) ^ 3 - (j : ℝ) ^ 3) / 3 := le_trans hj0 hge
  rw [hval, abs_of_nonneg hpos]
  linarith

/-- The one-parcel symbol of the concrete two-level model: the external energy of
the parcel, given by an integral over the infinite continuous domain `ℝ`, plus
the internal Fock energy of the field the parcel carries. -/
noncomputable def intervalTwoLevelSymbol (eps : K → ℝ) : ℕ × Conf K → ℝ := fun m =>
  symbolOfIntegral volume extField intervalDens m.1 + confEnergy eps m.2

omit [DecidableEq K] in
/-- **The concrete Fock-of-Fock Navier–Stokes Hamiltonian is essentially
self-adjoint.**  The parcel modes live on the infinite continuous domain `ℝ`,
the external one-parcel energies are integrals of the unbounded field `ξ²`
against the mode densities, and each parcel carries its own quantum field with
internal mode energies `eps`. -/
theorem intervalTwoLevel_hasZeroDeficiencyOn (eps : K → ℝ) :
    HasZeroDeficiencyOn (FockOfFockDom ℕ K) (dGamma (intervalTwoLevelSymbol eps)) :=
  dGamma_hasZeroDeficiencyOn _

/-- The parcel-mode densities of the two-level model, as densities on the parcel
domain `ℝ`: a parcel of outer mode `(j, c)` is localized in `(j, j+1]` whatever
inner Fock state `c` it carries. -/
noncomputable def parcelDens : ℕ × Conf K → ℝ → ℝ := fun m ξ => intervalDens m.1 ξ

/-- The internal (inner-Fock) part of the one-parcel symbol. -/
noncomputable def innerEnergySymbol (eps : K → ℝ) : ℕ × Conf K → ℝ := fun m => confEnergy eps m.2

omit [DecidableEq K] in
theorem intervalTwoLevelSymbol_eq (eps : K → ℝ) :
    intervalTwoLevelSymbol eps
      = symbolOfIntegral volume extField parcelDens + innerEnergySymbol eps := rfl

omit [DecidableEq K] in
/-- **The concrete two-level Hamiltonian really is an integral of operators over
the infinite continuous domain `ℝ`, plus the internal field energy**:

`ĥ = ∫_ℝ ξ² a†(ξ) a(ξ) dξ + dΓ(internal energies)`,

as an identity of quadratic forms on the dense finite-particle domain of the
Fock space of a Fock space. -/
theorem intervalTwoLevel_inner_eq_integral (eps : K → ℝ) (v : FockOfFockDom ℕ K) :
    (inner ℂ ((v : FockOfFockL2 ℕ K))
        ((dGamma (intervalTwoLevelSymbol eps) v : FockOfFockDom ℕ K) : FockOfFockL2 ℕ K) : ℂ).re
      = (∫ ξ, extField ξ * (inner ℂ ((v : FockOfFockL2 ℕ K))
            ((numberDensityOp parcelDens ξ v : FockOfFockDom ℕ K) : FockOfFockL2 ℕ K) : ℂ).re)
        + (inner ℂ ((v : FockOfFockL2 ℕ K))
            ((dGamma (innerEnergySymbol eps) v : FockOfFockDom ℕ K) : FockOfFockL2 ℕ K)
              : ℂ).re := by
  have hint : ∀ m : ℕ × Conf K,
      Integrable (fun ξ => extField ξ * parcelDens m ξ) volume := fun m =>
    intervalDens_integrable m.1
  rw [intervalTwoLevelSymbol_eq, dGamma_add]
  simp only [LinearMap.add_apply, Submodule.coe_add, inner_add_right, Complex.add_re]
  rw [dGamma_inner_eq_integral volume extField parcelDens hint v]

omit [DecidableEq K] in
/-- … and it is genuinely unbounded. -/
theorem intervalTwoLevel_not_bounded (eps : K → ℝ) :
    ¬ ∃ C : ℝ, ∀ f : FockOfFockDom ℕ K,
      ‖dGamma (intervalTwoLevelSymbol eps) f‖ ≤ C * ‖f‖ := by
  refine dGamma_not_bounded _ fun C => ?_
  obtain ⟨j, hj⟩ := intervalSymbol_unbounded C
  refine ⟨(j, 0), ?_⟩
  simpa [intervalTwoLevelSymbol, confEnergy_zero] using hj

end IntervalModes

end FockOfFock

end BookProof.NavierStokesFlow
