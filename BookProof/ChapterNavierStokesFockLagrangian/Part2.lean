import Mathlib
import BookProof.ChapterNavierStokesFockContinuum
import BookProof.ChapterNavierStokesFockLagrangian.Part1

/-!
# The transformed Navier–Stokes Hamiltonian in the Lagrangian momentum
representation: essential self-adjointness with continuous spectrum

`BookProof.ChapterNavierStokesLagrangianEsa` sets up the untruncated Lagrangian
data `LagrangianFullData` — the parcel momenta `Pᵢ`, the viscous gradients `Qᵢ`,
the force drift generators `Dᵢ` and the volume-preservation constraint `C` — and
proves that the transformed Hamiltonian

`ĥ_full = ½∑ᵢPᵢ² + ν∑ᵢQᵢ² + ∑ᵢfᵢDᵢ + C`

is symmetric with positive second-order part, essentially self-adjoint whenever
the constituents admit a *total family of common eigenvectors*.

That criterion is a discrete-spectrum criterion: it needs eigenvectors.  The
Lagrangian momentum representation of a *continuum* fluid has none — the
constituents are multiplication operators by the momentum coordinates, whose
spectrum is purely continuous.  This module closes that gap.

## What is proved here

* `DominatedOn` and the multiplication operator `mulD` — multiplication by a
  real measurable symbol `h` on the bounded-energy core of a *scale* function
  `g`, available whenever `h` is bounded on the level sets of `g`, with its
  algebra (`mulD_comp`, `mulD_add`, `mulD_sum`, `mulD_real_smul`).
* `mulD_hasZeroDeficiencyOn` — **multiplication by any symbol dominated by the
  scale is essentially self-adjoint on the bounded-energy core of the scale.**
  This generalizes `FockContinuum.multOp_hasZeroDeficiencyOn`, where symbol and
  scale had to coincide, and it is what allows *all four* constituents of the
  transformed Hamiltonian to live on one common core.
* `LagSymbols` — the Lagrangian momentum representation itself: arbitrary
  measurable real symbols `Pᵢ, Qᵢ, Dᵢ, C` on a measure space of momentum
  configurations, with no boundedness assumption whatsoever, and the common
  core `boundedEnergyCore μ S.scale`.
* `LagSymbols.data` — the resulting `LagrangianFullData`, so everything proved
  about the abstract transformed operator (symmetry, positivity of the advective
  and viscous terms, transfer along the change of variables) applies verbatim.
* `LagSymbols.hFull_eq_mulD` — **the transformed Hamiltonian is multiplication
  by the total Lagrangian symbol** `½∑pᵢ² + ν∑qᵢ² + ∑fᵢdᵢ + c`.
* `LagSymbols.hFull_hasZeroDeficiencyOn` — **the headline: the untruncated
  transformed Navier–Stokes Hamiltonian is essentially self-adjoint in the
  Lagrangian momentum representation**, for arbitrary measurable symbols, with
  in general purely continuous spectrum and no eigenvectors at all.
* `norm_mulD_ge`, `mulD_not_bounded` — the lower bound that makes such an
  operator genuinely unbounded whenever its symbol is.

The second-quantized realization on the continuum Fock space of all
parcel-number sectors — where this criterion is applied to the transformed
Navier–Stokes Hamiltonian itself — is in
`BookProof.ChapterNavierStokesFockParcels`.

## Scope

Nothing here claims global existence for Navier–Stokes, and nothing here claims
essential self-adjointness of the *Eulerian* continuum generator: what is proved
is essential self-adjointness of the transformed operator in the Lagrangian
momentum representation, which by
`NavierStokesFlow.NSFullData.hasZeroDeficiencyOn_of_lagrangian` transports back
along a unitary change of variables only when such a change of variables is
supplied.
-/

open MeasureTheory

namespace BookProof.NavierStokesFlow

namespace FockLagrangian

open FullEsa FockContinuum

variable {X : Type*} [MeasurableSpace X]
/-! ### Lower bounds on the multiplication operator, and unboundedness -/

/-- Where the state lives, the symbol is at least `K`: then the operator
increases the norm by at least the factor `K`. -/
theorem norm_mulD_ge (μ : Measure X) {g h : X → ℝ} (hh : Measurable h)
    (hdom : DominatedOn μ g h) (v : boundedEnergyCore μ g) {K : ℝ} (hK : 0 ≤ K)
    (hge : ∀ᵐ x ∂μ, ((v : Lp ℂ 2 μ) : X → ℂ) x ≠ 0 → K ≤ |h x|) :
    K * ‖((v : Lp ℂ 2 μ))‖ ≤ ‖((mulD μ hh hdom v : boundedEnergyCore μ g) : Lp ℂ 2 μ)‖ := by
  have hsmul : ‖((K : ℂ) • (v : Lp ℂ 2 μ))‖ = K * ‖((v : Lp ℂ 2 μ))‖ := by
    rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hK]
  rw [← hsmul]
  refine Lp.norm_le_norm_of_ae_le ?_
  filter_upwards [hge, mulD_coeFn μ hh hdom v,
    Lp.coeFn_smul ((K : ℂ)) ((v : Lp ℂ 2 μ))] with x hx hmul hsm
  rw [hsm, hmul]
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, Real.norm_eq_abs]
  by_cases hv : ((v : Lp ℂ 2 μ) : X → ℂ) x = 0
  · rw [hv]; simp
  · exact mul_le_mul_of_nonneg_right (by rw [abs_of_nonneg hK]; exact hx hv) (norm_nonneg _)

/-- **A multiplication operator with arbitrarily large symbol on unit states is
unbounded.** -/
theorem mulD_not_bounded (μ : Measure X) {g h : X → ℝ} (hh : Measurable h)
    (hdom : DominatedOn μ g h)
    (H : ∀ K : ℝ, ∃ v : boundedEnergyCore μ g, ‖((v : Lp ℂ 2 μ))‖ = 1 ∧
      ∀ᵐ x ∂μ, ((v : Lp ℂ 2 μ) : X → ℂ) x ≠ 0 → K ≤ |h x|) :
    ¬ ∃ C : ℝ, ∀ v : boundedEnergyCore μ g,
      ‖((mulD μ hh hdom v : boundedEnergyCore μ g) : Lp ℂ 2 μ)‖ ≤ C * ‖((v : Lp ℂ 2 μ))‖ := by
  rintro ⟨C, hC⟩
  obtain ⟨v, hv1, hvge⟩ := H (|C| + 1)
  have hlow := norm_mulD_ge μ hh hdom v (by positivity) hvge
  have hup := hC v
  rw [hv1, mul_one] at hlow hup
  have : |C| + 1 ≤ C := le_trans hlow hup
  have hCle : C ≤ |C| := le_abs_self C
  linarith

/-! ### No eigenvectors: continuity of the spectrum -/

/-- **A multiplication operator whose symbol has null level sets has no
eigenvectors.**  If `{x | h x = λ}` is `μ`-null then the only solution of
`h · v = λ v` in the core is `v = 0`. -/
theorem mulD_eq_zero_of_eigen (μ : Measure X) {g h : X → ℝ} (hh : Measurable h)
    (hdom : DominatedOn μ g h) {lam : ℂ} (hlevel : μ {x | (h x : ℂ) = lam} = 0)
    (v : boundedEnergyCore μ g)
    (hv : ((mulD μ hh hdom v : boundedEnergyCore μ g) : Lp ℂ 2 μ)
        = lam • ((v : Lp ℂ 2 μ))) :
    ((v : Lp ℂ 2 μ)) = 0 := by
  have hae : ∀ᵐ x ∂μ, x ∉ {x | (h x : ℂ) = lam} := measure_eq_zero_iff_ae_notMem.1 hlevel
  have h1 : (((mulD μ hh hdom v : boundedEnergyCore μ g) : Lp ℂ 2 μ) : X → ℂ)
      =ᵐ[μ] ((lam • (v : Lp ℂ 2 μ) : Lp ℂ 2 μ) : X → ℂ) := by rw [hv]
  refine Lp.ext ?_
  filter_upwards [hae, mulD_coeFn μ hh hdom v, Lp.coeFn_smul lam ((v : Lp ℂ 2 μ)), h1,
    Lp.coeFn_zero (E := ℂ) (p := 2) (μ := μ)] with x hx hmul hsm heq hz
  rw [hz]
  rw [hmul, hsm] at heq
  simp only [Pi.smul_apply, smul_eq_mul] at heq
  by_contra hv0
  exact hx (mul_right_cancel₀ hv0 heq)

/-! ## The Lagrangian momentum representation -/

/-- **The Lagrangian momentum representation of the transformed Navier–Stokes
data.**  The parcel momenta `Pᵢ`, the viscous gradients `Qᵢ`, the force drift
generators `Dᵢ` and the volume-preservation constraint `C` are here *arbitrary
real measurable symbols* on a measure space `X` of momentum configurations —
nothing is assumed bounded, and the resulting operators have in general purely
continuous spectrum. -/
structure LagSymbols (X : Type*) [MeasurableSpace X] (μ : Measure X) where
  /-- The parcel-momentum symbols. -/
  P : Fin 3 → X → ℝ
  /-- The viscous-gradient symbols. -/
  Q : Fin 3 → X → ℝ
  /-- The drift-generator symbols. -/
  Dr : Fin 3 → X → ℝ
  /-- The volume-preservation constraint symbol. -/
  cfun : X → ℝ
  /-- The external force. -/
  force : Fin 3 → ℝ
  /-- The kinematic viscosity. -/
  nu : ℝ
  nu_nonneg : 0 ≤ nu
  P_meas : ∀ i, Measurable (P i)
  Q_meas : ∀ i, Measurable (Q i)
  Dr_meas : ∀ i, Measurable (Dr i)
  c_meas : Measurable cfun

namespace LagSymbols

variable {μ : Measure X} (S : LagSymbols X μ)

/-- The **scale**: the sum of the absolute values of all the symbols.  Its
bounded-energy core is the common domain on which all four constituents of the
transformed Hamiltonian act. -/
def scale : X → ℝ := fun x =>
  (∑ i : Fin 3, |S.P i x|) + (∑ i : Fin 3, |S.Q i x|) + (∑ i : Fin 3, |S.Dr i x|) + |S.cfun x|

theorem scale_nonneg (x : X) : 0 ≤ S.scale x := by
  have h1 : (0 : ℝ) ≤ ∑ i : Fin 3, |S.P i x| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have h2 : (0 : ℝ) ≤ ∑ i : Fin 3, |S.Q i x| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have h3 : (0 : ℝ) ≤ ∑ i : Fin 3, |S.Dr i x| := Finset.sum_nonneg fun i _ => abs_nonneg _
  have h4 : (0 : ℝ) ≤ |S.cfun x| := abs_nonneg _
  simp only [scale]
  linarith

theorem scale_meas : Measurable S.scale := by
  refine (((Finset.univ.measurable_sum fun i _ => (S.P_meas i).abs).add
    (Finset.univ.measurable_sum fun i _ => (S.Q_meas i).abs)).add
    (Finset.univ.measurable_sum fun i _ => (S.Dr_meas i).abs)).add S.c_meas.abs

/-- Every symbol of the family is dominated by the scale. -/
theorem dominated_of_abs_le {h : X → ℝ} (hle : ∀ x, |h x| ≤ S.scale x) :
    DominatedOn μ S.scale h :=
  (DominatedOn.rfl' μ S.scale).of_abs_le
    (Filter.Eventually.of_forall fun x =>
      le_trans (hle x) (le_abs_self (S.scale x)))

theorem P_dom (i : Fin 3) : DominatedOn μ S.scale (S.P i) := by
  refine S.dominated_of_abs_le fun x => ?_
  have h1 : |S.P i x| ≤ ∑ j : Fin 3, |S.P j x| :=
    Finset.single_le_sum (f := fun j => |S.P j x|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
  have h2 : (0 : ℝ) ≤ ∑ j : Fin 3, |S.Q j x| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have h3 : (0 : ℝ) ≤ ∑ j : Fin 3, |S.Dr j x| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have h4 : (0 : ℝ) ≤ |S.cfun x| := abs_nonneg _
  simp only [scale]
  linarith

theorem Q_dom (i : Fin 3) : DominatedOn μ S.scale (S.Q i) := by
  refine S.dominated_of_abs_le fun x => ?_
  have h1 : |S.Q i x| ≤ ∑ j : Fin 3, |S.Q j x| :=
    Finset.single_le_sum (f := fun j => |S.Q j x|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
  have h2 : (0 : ℝ) ≤ ∑ j : Fin 3, |S.P j x| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have h3 : (0 : ℝ) ≤ ∑ j : Fin 3, |S.Dr j x| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have h4 : (0 : ℝ) ≤ |S.cfun x| := abs_nonneg _
  simp only [scale]
  linarith

theorem Dr_dom (i : Fin 3) : DominatedOn μ S.scale (S.Dr i) := by
  refine S.dominated_of_abs_le fun x => ?_
  have h1 : |S.Dr i x| ≤ ∑ j : Fin 3, |S.Dr j x| :=
    Finset.single_le_sum (f := fun j => |S.Dr j x|) (fun j _ => abs_nonneg _)
      (Finset.mem_univ i)
  have h2 : (0 : ℝ) ≤ ∑ j : Fin 3, |S.P j x| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have h3 : (0 : ℝ) ≤ ∑ j : Fin 3, |S.Q j x| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have h4 : (0 : ℝ) ≤ |S.cfun x| := abs_nonneg _
  simp only [scale]
  linarith

theorem c_dom : DominatedOn μ S.scale S.cfun := by
  refine S.dominated_of_abs_le fun x => ?_
  have h1 : (0 : ℝ) ≤ ∑ j : Fin 3, |S.P j x| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have h2 : (0 : ℝ) ≤ ∑ j : Fin 3, |S.Q j x| := Finset.sum_nonneg fun j _ => abs_nonneg _
  have h3 : (0 : ℝ) ≤ ∑ j : Fin 3, |S.Dr j x| := Finset.sum_nonneg fun j _ => abs_nonneg _
  simp only [scale]
  linarith

/-- The common domain: the bounded-scale core. -/
def core : Submodule ℂ (Lp ℂ 2 μ) := boundedEnergyCore μ S.scale

theorem core_dense : Dense ((S.core : Submodule ℂ (Lp ℂ 2 μ)) : Set (Lp ℂ 2 μ)) :=
  boundedEnergyCore_dense μ S.scale_meas

/-- The parcel-momentum operators. -/
noncomputable def Pop (i : Fin 3) : S.core →ₗ[ℂ] S.core := mulD μ (S.P_meas i) (S.P_dom i)

/-- The viscous-gradient operators. -/
noncomputable def Qop (i : Fin 3) : S.core →ₗ[ℂ] S.core := mulD μ (S.Q_meas i) (S.Q_dom i)

/-- The drift generators. -/
noncomputable def Drop (i : Fin 3) : S.core →ₗ[ℂ] S.core := mulD μ (S.Dr_meas i) (S.Dr_dom i)

/-- The volume-preservation constraint operator. -/
noncomputable def Cop : S.core →ₗ[ℂ] S.core := mulD μ S.c_meas S.c_dom

/-- **The Lagrangian momentum representation as untruncated transformed
Navier–Stokes data.**  Everything proved about `LagrangianFullData` — symmetry,
positivity of the advective and viscous quadratic forms, transfer of essential
self-adjointness along the change of variables — applies to it. -/
noncomputable def data : LagrangianEsa.LagrangianFullData (Lp ℂ 2 μ) where
  D := S.core
  P := S.Pop
  Q := S.Qop
  drive := S.Drop
  force := S.force
  constraintOp := S.Cop
  nu := S.nu
  dense := S.core_dense
  P_symm i := mulD_isSymmetricDom μ (S.P_meas i) (S.P_dom i)
  Q_symm i := mulD_isSymmetricDom μ (S.Q_meas i) (S.Q_dom i)
  drive_symm i := mulD_isSymmetricDom μ (S.Dr_meas i) (S.Dr_dom i)
  constraint_symm := mulD_isSymmetricDom μ S.c_meas S.c_dom
  nu_nonneg := S.nu_nonneg

/-- **The total Lagrangian symbol** `½∑pᵢ² + ν∑qᵢ² + ∑fᵢdᵢ + c`: the classical
energy of the transformed Hamiltonian in the momentum representation. -/
noncomputable def total : X → ℝ := fun x =>
  (1 / 2) * (∑ i : Fin 3, (S.P i x) ^ 2) + S.nu * (∑ i : Fin 3, (S.Q i x) ^ 2)
    + (∑ i : Fin 3, S.force i * S.Dr i x) + S.cfun x

theorem total_meas : Measurable S.total := by
  refine ((((measurable_const).mul
    (Finset.univ.measurable_sum fun i _ => (S.P_meas i).pow_const 2)).add
    ((measurable_const).mul
      (Finset.univ.measurable_sum fun i _ => (S.Q_meas i).pow_const 2))).add
    (Finset.univ.measurable_sum fun i _ => (measurable_const).mul (S.Dr_meas i))).add S.c_meas

theorem total_dom : DominatedOn μ S.scale S.total := by
  have hP : DominatedOn μ S.scale (fun x => (1 / 2 : ℝ) * ∑ i : Fin 3, (S.P i x) ^ 2 ) := by
    refine DominatedOn.const_mul _ ?_
    refine DominatedOn.sum Finset.univ fun i _ => ?_
    have := (S.P_dom i).mul (S.P_dom i)
    exact this.of_abs_le (Filter.Eventually.of_forall fun x => by rw [pow_two])
  have hQ : DominatedOn μ S.scale (fun x => S.nu * ∑ i : Fin 3, (S.Q i x) ^ 2) := by
    refine DominatedOn.const_mul _ ?_
    refine DominatedOn.sum Finset.univ fun i _ => ?_
    have := (S.Q_dom i).mul (S.Q_dom i)
    exact this.of_abs_le (Filter.Eventually.of_forall fun x => by rw [pow_two])
  have hD : DominatedOn μ S.scale (fun x => ∑ i : Fin 3, S.force i * S.Dr i x) :=
    DominatedOn.sum Finset.univ fun i _ => DominatedOn.const_mul _ (S.Dr_dom i)
  exact ((hP.add hQ).add hD).add S.c_dom

/-! ### The transformed Hamiltonian is multiplication by the total symbol -/

/-- The symbol of the advective (kinetic) term, `½∑pᵢ²`. -/
noncomputable def kinSym : X → ℝ := fun x => (1 / 2) * (∑ i : Fin 3, (S.P i x) ^ 2)

/-- The symbol of the viscous term, `ν∑qᵢ²`. -/
def visSym : X → ℝ := fun x => S.nu * (∑ i : Fin 3, (S.Q i x) ^ 2)

/-- The symbol of the force drift, `∑fᵢdᵢ`. -/
def driSym : X → ℝ := fun x => ∑ i : Fin 3, S.force i * S.Dr i x

theorem sq_dom (i : Fin 3) : DominatedOn μ S.scale (fun x => (S.P i x) ^ 2) :=
  ((S.P_dom i).mul (S.P_dom i)).of_abs_le
    (Filter.Eventually.of_forall fun x => by rw [pow_two])

theorem sqQ_dom (i : Fin 3) : DominatedOn μ S.scale (fun x => (S.Q i x) ^ 2) :=
  ((S.Q_dom i).mul (S.Q_dom i)).of_abs_le
    (Filter.Eventually.of_forall fun x => by rw [pow_two])

theorem kinSym_meas : Measurable S.kinSym :=
  measurable_const.mul (Finset.univ.measurable_sum fun i _ => (S.P_meas i).pow_const 2)

theorem visSym_meas : Measurable S.visSym :=
  measurable_const.mul (Finset.univ.measurable_sum fun i _ => (S.Q_meas i).pow_const 2)

theorem driSym_meas : Measurable S.driSym :=
  Finset.univ.measurable_sum fun i _ => measurable_const.mul (S.Dr_meas i)

theorem kinSym_dom : DominatedOn μ S.scale S.kinSym :=
  DominatedOn.const_mul _ (DominatedOn.sum Finset.univ fun i _ => S.sq_dom i)

theorem visSym_dom : DominatedOn μ S.scale S.visSym :=
  DominatedOn.const_mul _ (DominatedOn.sum Finset.univ fun i _ => S.sqQ_dom i)

theorem driSym_dom : DominatedOn μ S.scale S.driSym :=
  DominatedOn.sum Finset.univ fun i _ => DominatedOn.const_mul _ (S.Dr_dom i)

/-- The advective term is multiplication by `½∑pᵢ²`. -/
theorem kinetic_eq : S.data.kinetic = mulD μ S.kinSym_meas S.kinSym_dom := by
  have hsq : ∀ i : Fin 3, (S.Pop i).comp (S.Pop i)
      = mulD μ ((S.P_meas i).pow_const 2) (S.sq_dom i) := fun i =>
    mulD_comp' μ (S.P_meas i) (S.P_meas i) ((S.P_meas i).pow_const 2) (S.P_dom i)
      (S.P_dom i) (S.sq_dom i) fun x => by rw [pow_two]
  have hsum : (∑ i : Fin 3, (S.Pop i).comp (S.Pop i))
      = mulD μ (Finset.univ.measurable_sum fun i (_ : i ∈ Finset.univ) =>
            (S.P_meas i).pow_const 2)
          (DominatedOn.sum Finset.univ fun i _ => S.sq_dom i) := by
    rw [Fin.sum_univ_three, hsq 0, hsq 1, hsq 2,
      mulD_add' μ ((S.P_meas 0).pow_const 2) ((S.P_meas 1).pow_const 2)
        (((S.P_meas 0).pow_const 2).add ((S.P_meas 1).pow_const 2)) (S.sq_dom 0) (S.sq_dom 1)
        ((S.sq_dom 0).add (S.sq_dom 1)) fun _ => rfl]
    exact mulD_add' μ _ _ _ _ _ _ fun x => by rw [Fin.sum_univ_three]
  have hkin : S.data.kinetic = ((1 / 2 : ℝ) : ℂ) • (∑ i : Fin 3, (S.Pop i).comp (S.Pop i)) := rfl
  rw [hkin, hsum]
  exact mulD_real_smul' μ (1 / 2 : ℝ) _ _ _ _ fun _ => rfl

/-- The viscous term is multiplication by `ν∑qᵢ²`. -/
theorem viscous_eq : S.data.viscous = mulD μ S.visSym_meas S.visSym_dom := by
  have hsq : ∀ i : Fin 3, (S.Qop i).comp (S.Qop i)
      = mulD μ ((S.Q_meas i).pow_const 2) (S.sqQ_dom i) := fun i =>
    mulD_comp' μ (S.Q_meas i) (S.Q_meas i) ((S.Q_meas i).pow_const 2) (S.Q_dom i)
      (S.Q_dom i) (S.sqQ_dom i) fun x => by rw [pow_two]
  have hsum : (∑ i : Fin 3, (S.Qop i).comp (S.Qop i))
      = mulD μ (Finset.univ.measurable_sum fun i (_ : i ∈ Finset.univ) =>
            (S.Q_meas i).pow_const 2)
          (DominatedOn.sum Finset.univ fun i _ => S.sqQ_dom i) := by
    rw [Fin.sum_univ_three, hsq 0, hsq 1, hsq 2,
      mulD_add' μ ((S.Q_meas 0).pow_const 2) ((S.Q_meas 1).pow_const 2)
        (((S.Q_meas 0).pow_const 2).add ((S.Q_meas 1).pow_const 2)) (S.sqQ_dom 0) (S.sqQ_dom 1)
        ((S.sqQ_dom 0).add (S.sqQ_dom 1)) fun _ => rfl]
    exact mulD_add' μ _ _ _ _ _ _ fun x => by rw [Fin.sum_univ_three]
  have hvis : S.data.viscous = ((S.nu : ℝ) : ℂ) • (∑ i : Fin 3, (S.Qop i).comp (S.Qop i)) := rfl
  rw [hvis, hsum]
  exact mulD_real_smul' μ S.nu _ _ _ _ fun _ => rfl

/-- The force drift is multiplication by `∑fᵢdᵢ`. -/
theorem drift_eq : S.data.drift = mulD μ S.driSym_meas S.driSym_dom := by
  have hterm : ∀ i : Fin 3, ((S.force i : ℝ) : ℂ) • S.Drop i
      = mulD μ (measurable_const.mul (S.Dr_meas i))
          (DominatedOn.const_mul (S.force i) (S.Dr_dom i)) := fun i =>
    mulD_real_smul' μ (S.force i) (S.Dr_meas i) _ (S.Dr_dom i) _ fun _ => rfl
  have hdri : S.data.drift = ∑ i : Fin 3, ((S.force i : ℝ) : ℂ) • S.Drop i := rfl
  rw [hdri, Fin.sum_univ_three, hterm 0, hterm 1, hterm 2,
    mulD_add' μ _ _ ((measurable_const.mul (S.Dr_meas 0)).add
        (measurable_const.mul (S.Dr_meas 1))) _ _
      ((DominatedOn.const_mul (S.force 0) (S.Dr_dom 0)).add
        (DominatedOn.const_mul (S.force 1) (S.Dr_dom 1))) fun _ => rfl]
  exact mulD_add' μ _ _ _ _ _ _ fun x => by simp only [driSym]; rw [Fin.sum_univ_three]

/-- **The transformed Navier–Stokes Hamiltonian in the Lagrangian momentum
representation is multiplication by the total Lagrangian symbol**
`½∑pᵢ² + ν∑qᵢ² + ∑fᵢdᵢ + c`.  The four terms of `ĥ_full` are the four terms of
the classical energy. -/
theorem hFull_eq_mulD : S.data.hFull = mulD μ S.total_meas S.total_dom := by
  have hdec : S.data.hFull
      = S.data.kinetic + S.data.viscous + S.data.drift + S.data.constraintOp := rfl
  have hcon : S.data.constraintOp = mulD μ S.c_meas S.c_dom := rfl
  rw [hdec, S.kinetic_eq, S.viscous_eq, S.drift_eq, hcon,
    mulD_add' μ S.kinSym_meas S.visSym_meas (S.kinSym_meas.add S.visSym_meas) S.kinSym_dom
      S.visSym_dom (S.kinSym_dom.add S.visSym_dom) fun _ => rfl,
    mulD_add' μ (S.kinSym_meas.add S.visSym_meas) S.driSym_meas
      ((S.kinSym_meas.add S.visSym_meas).add S.driSym_meas)
      (S.kinSym_dom.add S.visSym_dom) S.driSym_dom
      ((S.kinSym_dom.add S.visSym_dom).add S.driSym_dom) fun _ => rfl]
  exact mulD_add' μ _ _ _ _ _ _ fun _ => rfl

/-- **The headline.  The untruncated transformed Navier–Stokes Hamiltonian is
essentially self-adjoint in the Lagrangian momentum representation.**

The symbols are arbitrary measurable real functions: nothing is bounded, and the
operator has in general purely continuous spectrum and no eigenvector at all, so
none of the earlier criteria — bounded realization, complete unitary flow, or a
total family of common eigenvectors — applies. -/
theorem hFull_hasZeroDeficiencyOn :
    HasZeroDeficiencyOn S.data.D S.data.hFull := by
  rw [hFull_eq_mulD]
  exact mulD_hasZeroDeficiencyOn μ S.scale_meas S.total_meas S.total_dom

/-- **No eigenvectors.**  If the total symbol has a null level set at `λ`, then
`ĥ_full v = λ v` forces `v = 0`: the spectrum carries no point mass there. -/
theorem hFull_eq_zero_of_eigen {lam : ℂ} (hlevel : μ {x | (S.total x : ℂ) = lam} = 0)
    (v : S.core) (hv : ((S.data.hFull v : S.core) : Lp ℂ 2 μ) = lam • ((v : Lp ℂ 2 μ))) :
    ((v : Lp ℂ 2 μ)) = 0 := by
  rw [S.hFull_eq_mulD] at hv
  exact mulD_eq_zero_of_eigen μ S.total_meas S.total_dom hlevel v hv

/-- The transformed Hamiltonian is symmetric on its domain (inherited from the
abstract theory). -/
theorem hFull_isSymmetricDom : IsSymmetricDom S.data.hFull :=
  S.data.hFull_isSymmetricDom

end LagSymbols

end FockLagrangian

end BookProof.NavierStokesFlow
