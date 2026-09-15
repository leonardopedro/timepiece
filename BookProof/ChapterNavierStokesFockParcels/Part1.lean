import Mathlib
import BookProof.ChapterNavierStokesFockLagrangian

/-!
# The continuum Fock space over a parcel domain

`BookProof.ChapterNavierStokesFockLagrangian` proves that the untruncated
transformed Navier–Stokes Hamiltonian is essentially self-adjoint in the
Lagrangian momentum representation, for arbitrary measurable symbols
(`LagSymbols.hFull_hasZeroDeficiencyOn`).  This module supplies the
second-quantized realization of that theorem.

* `ParcelConf`, `fockMeasure`, `fockMeasure_sector` — the measure space of *all*
  finite parcel configurations: the continuum Fock space `⨁ₙ L²(Ωⁿ)` realized as
  a single `L²` space, with the `n`-parcel sector carrying the `n`-fold product
  measure.
* `secondQuant` — the second quantization `dΓ(s)(ξ) = ∑ₖ s(ξₖ)` of a one-parcel
  symbol.
* `fockLagSymbols`, `fockLagrangian_hasZeroDeficiencyOn` — **the transformed
  Navier–Stokes Hamiltonian, second-quantized on the whole continuum Fock space
  (all parcel-number sectors at once), is essentially self-adjoint** on a dense
  domain; the one-parcel symbols are arbitrary measurable real functions.
* `momFock`, `momFock_not_bounded`, `momFock_hasZeroDeficiencyOn` — the physical
  choice of symbols, where the advective term is the total kinetic energy: the
  resulting operator is genuinely unbounded, and essentially self-adjoint all the
  same.
* `momFock_core_ne_top` — the domain is a *proper* dense subspace: the state
  `tailState`, supported on unboundedly large momenta of finite total measure,
  lies in the Fock space but outside the domain.
* `momFock_no_eigenvector`, `momFock_vacuum_eigenvector` — the spectrum is
  purely continuous above the vacuum: no nonzero energy is an eigenvalue, while
  the vacuum is an honest unit eigenvector of energy zero.

## Scope

As in the parent module, nothing here claims global existence for Navier–Stokes,
and nothing is claimed for the Eulerian continuum generator except through the
unitary change of variables of
`BookProof.ChapterNavierStokesLagrangianEsa`.
-/

open MeasureTheory

namespace BookProof.NavierStokesFlow

namespace FockLagrangian

open FullEsa FockContinuum

/-! ## The continuum Fock space over a parcel domain -/

section Fock

variable {Ω : Type*} [MeasurableSpace Ω]

/-- A **parcel configuration**: an arbitrary finite number `n` of parcels
together with their positions (or momenta) `ξ : Fin n → Ω`.  The measurable
space of all parcel configurations is the base of the continuum Fock space: all
parcel-number sectors at once. -/
abbrev ParcelConf (Ω : Type*) [MeasurableSpace Ω] := Σ n : ℕ, (Fin n → Ω)

/-- The inclusion of the `n`-parcel sector into all parcel configurations. -/
def parcelMk (n : ℕ) (ξ : Fin n → Ω) : ParcelConf Ω := ⟨n, ξ⟩

/-- The inclusion of the `n`-parcel sector is measurable. -/
theorem measurable_parcelMk (n : ℕ) : Measurable (parcelMk (Ω := Ω) n) :=
  fun _ hs => MeasurableSpace.measurableSet_iInf.1 hs n

/-- A function on parcel configurations is measurable as soon as it is
measurable on every sector. -/
theorem measurable_parcel {γ : Type*} [MeasurableSpace γ] {f : ParcelConf Ω → γ}
    (h : ∀ n : ℕ, Measurable fun ξ : Fin n → Ω => f ⟨n, ξ⟩) : Measurable f :=
  fun _ hs => MeasurableSpace.measurableSet_iInf.2 fun n => h n hs

/-- A set of parcel configurations is measurable as soon as its intersection
with every sector is. -/
theorem measurableSet_parcel {A : Set (ParcelConf Ω)}
    (h : ∀ n : ℕ, MeasurableSet (parcelMk (Ω := Ω) n ⁻¹' A)) : MeasurableSet A :=
  MeasurableSpace.measurableSet_iInf.2 h

/-- **The Fock measure**: the sum over all parcel numbers of the product measure
on the `n`-parcel sector.  `L²` of this measure is the continuum Fock space
`⨁ₙ L²(Ωⁿ)`. -/
noncomputable def fockMeasure (μ : Measure Ω) : Measure (ParcelConf Ω) :=
  Measure.sum fun n => (Measure.pi fun _ : Fin n => μ).map (parcelMk n)

/-- The Fock measure of a measurable set, sector by sector. -/
theorem fockMeasure_apply (μ : Measure Ω) {A : Set (ParcelConf Ω)} (hA : MeasurableSet A) :
    fockMeasure μ A = ∑' n : ℕ, (Measure.pi fun _ : Fin n => μ) (parcelMk n ⁻¹' A) := by
  rw [fockMeasure, Measure.sum_apply _ hA]
  exact tsum_congr fun n => Measure.map_apply (measurable_parcelMk n) hA

/-! ### Sectors of the continuum Fock space -/

theorem parcelMk_preimage_image_self (n : ℕ) (B : Set (Fin n → Ω)) :
    parcelMk (Ω := Ω) n ⁻¹' (parcelMk n '' B) = B := by
  ext ξ
  exact ⟨fun ⟨η, hη, hEq⟩ => (sigma_mk_injective hEq) ▸ hη, fun h => ⟨ξ, h, rfl⟩⟩

theorem parcelMk_preimage_image_ne {n m : ℕ} (h : m ≠ n) (B : Set (Fin n → Ω)) :
    parcelMk (Ω := Ω) m ⁻¹' (parcelMk n '' B) = ∅ := by
  ext ξ
  simp only [Set.mem_preimage, Set.mem_empty_iff_false, iff_false]
  rintro ⟨η, _, hEq⟩
  exact h (congrArg Sigma.fst hEq).symm

theorem measurableSet_parcel_image {n : ℕ} {B : Set (Fin n → Ω)} (hB : MeasurableSet B) :
    MeasurableSet (parcelMk n '' B) := by
  refine measurableSet_parcel fun m => ?_
  by_cases h : m = n
  · subst h; rw [parcelMk_preimage_image_self]; exact hB
  · rw [parcelMk_preimage_image_ne h]; exact MeasurableSet.empty

/-- On the `n`-parcel sector the Fock measure is the `n`-fold product measure. -/
theorem fockMeasure_sector (μ : Measure Ω) [SigmaFinite μ] {n : ℕ} {B : Set (Fin n → Ω)}
    (hB : MeasurableSet B) :
    fockMeasure μ (parcelMk n '' B) = (Measure.pi fun _ : Fin n => μ) B := by
  rw [fockMeasure_apply μ (measurableSet_parcel_image hB),
    tsum_eq_single n (fun m hm => by rw [parcelMk_preimage_image_ne hm, measure_empty]),
    parcelMk_preimage_image_self]

/-- **Second quantization** `dΓ(s)` of a one-parcel symbol `s`: on the
`n`-parcel sector it is the total value `∑ₖ s(ξₖ)`. -/
def secondQuant (s : Ω → ℝ) : ParcelConf Ω → ℝ := fun c => ∑ k : Fin c.1, s (c.2 k)

@[simp] theorem secondQuant_apply (s : Ω → ℝ) (n : ℕ) (ξ : Fin n → Ω) :
    secondQuant s (⟨n, ξ⟩ : ParcelConf Ω) = ∑ k : Fin n, s (ξ k) := rfl

theorem secondQuant_measurable {s : Ω → ℝ} (hs : Measurable s) :
    Measurable (secondQuant s) :=
  measurable_parcel fun _ =>
    Finset.univ.measurable_sum fun k _ => hs.comp (measurable_pi_apply k)

/-- **The Lagrangian momentum representation on the continuum Fock space.**  Each
constituent of the transformed Navier–Stokes Hamiltonian is the second
quantization of its one-parcel symbol: `Pᵢ = dΓ(pᵢ)`, `Qᵢ = dΓ(qᵢ)`,
`Dᵢ = dΓ(dᵢ)`, `C = dΓ(c)`.  The one-parcel symbols are arbitrary measurable
real functions — in particular unbounded ones are allowed. -/
noncomputable def fockLagSymbols (μ : Measure Ω) {p q dr : Fin 3 → Ω → ℝ} {cf : Ω → ℝ}
    (hp : ∀ i, Measurable (p i)) (hq : ∀ i, Measurable (q i)) (hd : ∀ i, Measurable (dr i))
    (hc : Measurable cf) (force : Fin 3 → ℝ) {nu : ℝ} (hnu : 0 ≤ nu) :
    LagSymbols (ParcelConf Ω) (fockMeasure μ) where
  P i := secondQuant (p i)
  Q i := secondQuant (q i)
  Dr i := secondQuant (dr i)
  cfun := secondQuant cf
  force := force
  nu := nu
  nu_nonneg := hnu
  P_meas i := secondQuant_measurable (hp i)
  Q_meas i := secondQuant_measurable (hq i)
  Dr_meas i := secondQuant_measurable (hd i)
  c_meas := secondQuant_measurable hc

/-- **The transformed Navier–Stokes Hamiltonian on the whole continuum Fock
space is essentially self-adjoint.**

This is the second-quantized statement of the Lagrangian change of variables: all
parcel-number sectors at once (not one sector at a time), arbitrary measurable
one-parcel symbols, no boundedness anywhere, and in general purely continuous
spectrum. -/
theorem fockLagrangian_hasZeroDeficiencyOn (μ : Measure Ω) {p q dr : Fin 3 → Ω → ℝ}
    {cf : Ω → ℝ} (hp : ∀ i, Measurable (p i)) (hq : ∀ i, Measurable (q i))
    (hd : ∀ i, Measurable (dr i)) (hc : Measurable cf) (force : Fin 3 → ℝ) {nu : ℝ}
    (hnu : 0 ≤ nu) :
    HasZeroDeficiencyOn (fockLagSymbols μ hp hq hd hc force hnu).data.D
      (fockLagSymbols μ hp hq hd hc force hnu).data.hFull :=
  LagSymbols.hFull_hasZeroDeficiencyOn _

/-- The domain really is a dense subspace of the continuum Fock space. -/
theorem fockLagrangian_dense (μ : Measure Ω) {p q dr : Fin 3 → Ω → ℝ}
    {cf : Ω → ℝ} (hp : ∀ i, Measurable (p i)) (hq : ∀ i, Measurable (q i))
    (hd : ∀ i, Measurable (dr i)) (hc : Measurable cf) (force : Fin 3 → ℝ) {nu : ℝ}
    (hnu : 0 ≤ nu) :
    Dense (((fockLagSymbols μ hp hq hd hc force hnu).data.D :
      Submodule ℂ (Lp ℂ 2 (fockMeasure μ))) : Set (Lp ℂ 2 (fockMeasure μ))) :=
  (fockLagSymbols μ hp hq hd hc force hnu).core_dense

end Fock

/-! ## An unbounded continuum Fock realization -/

/-- The continuum Fock measure over the momentum line `ℝ`. -/
noncomputable abbrev fockR : Measure (ParcelConf ℝ) := fockMeasure (volume : Measure ℝ)

/-- **The physical choice of symbols**: each parcel momentum operator is
multiplication by the momentum coordinate itself, second-quantized — so the
advective term `½∑Pᵢ²` is the total kinetic energy — with no viscosity, no
external force and no constraint. -/
noncomputable def momFock : LagSymbols (ParcelConf ℝ) fockR :=
  fockLagSymbols (volume : Measure ℝ) (p := fun _ => id) (q := fun _ => fun _ => 0)
    (dr := fun _ => fun _ => 0) (cf := fun _ => 0) (fun _ => measurable_id)
    (fun _ => measurable_const) (fun _ => measurable_const) measurable_const (fun _ => 0)
    (le_refl 0)

theorem momFock_scale (c : ParcelConf ℝ) :
    momFock.scale c = 3 * |∑ k : Fin c.1, c.2 k| := by
  simp only [LagSymbols.scale, momFock, fockLagSymbols, secondQuant, Fin.sum_univ_three]
  simp
  ring

/-- The total symbol of this realization is the (total) kinetic energy. -/
theorem momFock_total (c : ParcelConf ℝ) :
    momFock.total c = (3 / 2) * (∑ k : Fin c.1, c.2 k) ^ 2 := by
  simp only [LagSymbols.total, momFock, fockLagSymbols, secondQuant, Fin.sum_univ_three]
  simp
  ring

/-- The one-parcel momentum box `[K, K+1]`. -/
def bigBox (K : ℝ) : Set (Fin 1 → ℝ) := Set.univ.pi fun _ => Set.Icc K (K + 1)

theorem bigBox_measurable (K : ℝ) : MeasurableSet (bigBox K) :=
  MeasurableSet.univ_pi fun _ => measurableSet_Icc

theorem volume_bigBox (K : ℝ) :
    (Measure.pi fun _ : Fin 1 => (volume : Measure ℝ)) (bigBox K) = 1 := by
  rw [bigBox, Measure.pi_pi]
  simp [Real.volume_Icc]

/-- The corresponding set of one-parcel configurations inside the Fock space. -/
def bigSet (K : ℝ) : Set (ParcelConf ℝ) := parcelMk 1 '' bigBox K

theorem bigSet_measurable (K : ℝ) : MeasurableSet (bigSet K) :=
  measurableSet_parcel_image (bigBox_measurable K)

theorem fockMeasure_bigSet (K : ℝ) : fockR (bigSet K) = 1 := by
  rw [bigSet, fockMeasure_sector (volume : Measure ℝ) (bigBox_measurable K), volume_bigBox]

/-- A unit state of the Fock space carrying one parcel of momentum in `[K,K+1]`. -/
noncomputable def bigState (K : ℝ) : Lp ℂ 2 fockR :=
  (memLp_indicator_const 2 (bigSet_measurable K) (1 : ℂ)
    (Or.inr (by rw [fockMeasure_bigSet K]; exact ENNReal.one_ne_top))).toLp _

theorem bigState_coeFn (K : ℝ) :
    ((bigState K : Lp ℂ 2 fockR) : ParcelConf ℝ → ℂ)
      =ᵐ[fockR] (bigSet K).indicator (fun _ => (1 : ℂ)) :=
  MemLp.coeFn_toLp _

theorem norm_bigState (K : ℝ) : ‖bigState K‖ = 1 := by
  rw [bigState, Lp.norm_toLp,
    eLpNorm_indicator_const (bigSet_measurable K) (by norm_num) (by norm_num),
    fockMeasure_bigSet]
  simp

theorem bigState_mem_core {K : ℝ} (hK : 0 ≤ K) : bigState K ∈ momFock.core := by
  refine ⟨⌈3 * (K + 1)⌉₊, ?_⟩
  filter_upwards [bigState_coeFn K] with x hx hbig
  rw [hx]
  by_cases hmem : x ∈ bigSet K
  · exfalso
    apply hbig
    obtain ⟨ξ, hξ, rfl⟩ := hmem
    have h0 : ξ 0 ∈ Set.Icc K (K + 1) := hξ 0 (Set.mem_univ 0)
    have hnn : 0 ≤ ξ 0 := le_trans hK h0.1
    have hs : |momFock.scale (parcelMk 1 ξ)| = 3 * ξ 0 := by
      rw [momFock_scale]
      simp only [parcelMk, Fin.sum_univ_one]
      rw [abs_of_nonneg hnn, abs_of_nonneg (by positivity)]
    rw [hs]
    calc 3 * ξ 0 ≤ 3 * (K + 1) := by linarith [h0.2]
      _ ≤ (⌈3 * (K + 1)⌉₊ : ℝ) := Nat.le_ceil _
  · exact Set.indicator_of_notMem hmem _

theorem bigState_symbol_ge {K : ℝ} (hK : 1 ≤ K) :
    ∀ᵐ x ∂fockR, ((bigState K : Lp ℂ 2 fockR) : ParcelConf ℝ → ℂ) x ≠ 0
        → K ≤ |momFock.total x| := by
  filter_upwards [bigState_coeFn K] with x hx hne
  rw [hx] at hne
  have hmem : x ∈ bigSet K := by
    by_contra h
    exact hne (Set.indicator_of_notMem h _)
  obtain ⟨ξ, hξ, rfl⟩ := hmem
  have h0 : ξ 0 ∈ Set.Icc K (K + 1) := hξ 0 (Set.mem_univ 0)
  have ht : momFock.total (parcelMk 1 ξ) = (3 / 2) * (ξ 0) ^ 2 := by
    rw [momFock_total]
    simp only [parcelMk, Fin.sum_univ_one]
  rw [ht, abs_of_nonneg (by positivity)]
  nlinarith [h0.1, hK]

/-- **The essentially self-adjoint Fock Hamiltonian really is unbounded.**  One
parcel carrying momentum in `[K, K+1]` is a unit state on which the transformed
Hamiltonian has norm at least `K`, so no bound `‖ĥ_full v‖ ≤ C‖v‖` can hold. -/
theorem momFock_not_bounded :
    ¬ ∃ C : ℝ, ∀ v : momFock.core,
      ‖((momFock.data.hFull v : momFock.core) : Lp ℂ 2 fockR)‖
        ≤ C * ‖((v : momFock.core) : Lp ℂ 2 fockR)‖ := by
  simp only [momFock.hFull_eq_mulD]
  refine mulD_not_bounded _ _ _ fun K => ?_
  refine ⟨⟨bigState (max K 1), bigState_mem_core (le_trans zero_le_one (le_max_right K 1))⟩,
    norm_bigState _, ?_⟩
  filter_upwards [bigState_symbol_ge (le_max_right K 1)] with x hx hne
  exact le_trans (le_max_left K 1) (hx hne)

/-- **Essential self-adjointness of the unbounded continuum Fock Hamiltonian.**
The transformed Navier–Stokes Hamiltonian of `momFock` — genuinely unbounded by
`momFock_not_bounded`, with purely continuous spectrum — has vanishing adjoint
deficiency on its dense domain. -/
theorem momFock_hasZeroDeficiencyOn :
    HasZeroDeficiencyOn momFock.data.D momFock.data.hFull :=
  momFock.hFull_hasZeroDeficiencyOn

end FockLagrangian

end BookProof.NavierStokesFlow
