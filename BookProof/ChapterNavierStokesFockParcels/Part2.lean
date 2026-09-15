import Mathlib
import BookProof.ChapterNavierStokesFockLagrangian
import BookProof.ChapterNavierStokesFockParcels.Part1

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
/-! ## The essentially self-adjoint domain is a proper subspace -/

/-- An unbounded set of momenta of finite total measure: the union of the
intervals `[k, k + 2⁻ᵏ]`. -/
def tailSet : Set ℝ := ⋃ k : ℕ, Set.Icc (k : ℝ) (k + (1 / 2) ^ k)

theorem tailSet_measurable : MeasurableSet tailSet :=
  MeasurableSet.iUnion fun _ => measurableSet_Icc

theorem volume_tail_Icc (k : ℕ) :
    volume (Set.Icc (k : ℝ) (k + (1 / 2) ^ k)) = (2⁻¹ : ENNReal) ^ k := by
  rw [Real.volume_Icc]
  have h : (k : ℝ) + (1 / 2) ^ k - k = (1 / 2) ^ k := by ring
  rw [h, ENNReal.ofReal_pow (by norm_num)]
  congr 1
  rw [show (1 / 2 : ℝ) = (2 : ℝ)⁻¹ by norm_num, ENNReal.ofReal_inv_of_pos (by norm_num)]
  norm_num

theorem volume_tailSet_ne_top : volume tailSet ≠ ⊤ := by
  have h1 : volume tailSet ≤ ∑' k : ℕ, volume (Set.Icc (k : ℝ) (k + (1 / 2) ^ k)) :=
    measure_iUnion_le _
  have h2 : (1 : ENNReal) - 2⁻¹ = 2⁻¹ :=
    ENNReal.sub_eq_of_eq_add (by norm_num) (by rw [← two_mul, ENNReal.mul_inv_cancel] <;> norm_num)
  simp only [volume_tail_Icc] at h1
  rw [ENNReal.tsum_geometric, h2, inv_inv] at h1
  exact ne_top_of_le_ne_top (by norm_num) h1

/-- The one-parcel configurations carrying a momentum in the tail. -/
def tailBox : Set (Fin 1 → ℝ) := Set.univ.pi fun _ => tailSet

theorem tailBox_measurable : MeasurableSet tailBox :=
  MeasurableSet.univ_pi fun _ => tailSet_measurable

theorem volume_tailBox_ne_top :
    (Measure.pi fun _ : Fin 1 => (volume : Measure ℝ)) tailBox ≠ ⊤ := by
  rw [tailBox, Measure.pi_pi]
  simpa using volume_tailSet_ne_top

/-- The corresponding finite-measure set of Fock configurations. -/
def tailFockSet : Set (ParcelConf ℝ) := parcelMk 1 '' tailBox

theorem tailFockSet_measurable : MeasurableSet tailFockSet :=
  measurableSet_parcel_image tailBox_measurable

theorem fockMeasure_tailFockSet_ne_top : fockR tailFockSet ≠ ⊤ := by
  rw [tailFockSet, fockMeasure_sector (volume : Measure ℝ) tailBox_measurable]
  exact volume_tailBox_ne_top

/-- A genuine `L²` state supported on unboundedly large momenta. -/
noncomputable def tailState : Lp ℂ 2 fockR :=
  (memLp_indicator_const 2 tailFockSet_measurable (1 : ℂ)
    (Or.inr fockMeasure_tailFockSet_ne_top)).toLp _

theorem tailState_coeFn :
    ((tailState : Lp ℂ 2 fockR) : ParcelConf ℝ → ℂ)
      =ᵐ[fockR] tailFockSet.indicator (fun _ => (1 : ℂ)) :=
  MemLp.coeFn_toLp _

/-- The `k`-th step of the tail, a positive-measure piece on which every parcel
carries momentum at least `k`. -/
def tailStep (k : ℕ) : Set (ParcelConf ℝ) :=
  parcelMk 1 '' (Set.univ.pi fun _ : Fin 1 => Set.Icc (k : ℝ) (k + (1 / 2) ^ k))

theorem tailStep_subset (k : ℕ) : tailStep k ⊆ tailFockSet :=
  Set.image_mono fun _ hξ i _ => Set.mem_iUnion.2 ⟨k, hξ i (Set.mem_univ i)⟩

theorem fockMeasure_tailStep_pos (k : ℕ) : 0 < fockR (tailStep k) := by
  rw [tailStep, fockMeasure_sector (volume : Measure ℝ)
    (MeasurableSet.univ_pi fun _ => measurableSet_Icc), Measure.pi_pi]
  simp only [Fin.prod_univ_one, volume_tail_Icc]
  exact ENNReal.pow_pos (by norm_num) k

/-- The tail state lies in the Fock space but not in the domain of the
Hamiltonian: on it the total kinetic energy is not essentially bounded. -/
theorem tailState_not_mem_core : tailState ∉ momFock.core := by
  rintro ⟨n, hn⟩
  have hzero : ∀ᵐ x ∂fockR, x ∉ tailStep (n + 1) := by
    filter_upwards [hn, tailState_coeFn] with x hx hcoe hmem
    obtain ⟨ξ, hξ, rfl⟩ := hmem
    have h0 : ξ 0 ∈ Set.Icc ((n : ℝ) + 1) ((n + 1 : ℕ) + (1 / 2) ^ (n + 1)) := by
      have := hξ 0 (Set.mem_univ 0)
      simpa using this
    have hnn : (0 : ℝ) ≤ ξ 0 := le_trans (by positivity) h0.1
    have hs : |momFock.scale (parcelMk 1 ξ)| = 3 * ξ 0 := by
      rw [momFock_scale]
      simp only [parcelMk, Fin.sum_univ_one]
      rw [abs_of_nonneg hnn, abs_of_nonneg (by positivity)]
    have hbig : ¬ (|momFock.scale (parcelMk 1 ξ)| ≤ (n : ℝ)) := by
      rw [hs]
      have hge : (n : ℝ) + 1 ≤ ξ 0 := h0.1
      push_neg
      linarith
    have h1 := hx hbig
    rw [hcoe, Set.indicator_of_mem (tailStep_subset (n + 1) ⟨ξ, hξ, rfl⟩)] at h1
    exact one_ne_zero h1
  rw [← measure_eq_zero_iff_ae_notMem] at hzero
  exact absurd hzero (ne_of_gt (fockMeasure_tailStep_pos (n + 1)))

/-- **The essentially self-adjoint domain is a proper dense subspace.**  The
Hamiltonian of `momFock` is not defined on all of the continuum Fock space: the
state `tailState` is a genuine `L²` vector outside its domain.  Together with
`fockLagrangian_dense` and `momFock_hasZeroDeficiencyOn` this says that the
domain is a proper *core*, exactly the situation essential self-adjointness is
meant for. -/
theorem momFock_core_ne_top : momFock.core ≠ ⊤ := fun h =>
  tailState_not_mem_core (h ▸ Submodule.mem_top)

/-! ## Continuity of the spectrum: no eigenvectors above the vacuum -/

set_option maxHeartbeats 400000 in
-- the affine-subspace and Haar-measure machinery below elaborates slowly
/-- A level set of the coordinate sum is a proper affine subspace of `ℝⁿ`, hence
Lebesgue-null as soon as there is at least one parcel. -/
theorem volume_sum_level (n : ℕ) (hn : 0 < n) (c : ℝ) :
    (volume : Measure (Fin n → ℝ)) {ξ : Fin n → ℝ | ∑ i, ξ i = c} = 0 := by
  classical
  have happ : ∀ ξ : Fin n → ℝ,
      ((∑ i : Fin n, LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ)) ξ = ∑ i, ξ i := by
    intro ξ
    rw [LinearMap.coe_sum, Finset.sum_apply]
    rfl
  obtain ⟨S, hcar⟩ : ∃ S : AffineSubspace ℝ (Fin n → ℝ),
      (S : Set (Fin n → ℝ)) = {ξ : Fin n → ℝ | ∑ i, ξ i = c} := by
    refine ⟨AffineSubspace.comap
      ((∑ i : Fin n, LinearMap.proj i : (Fin n → ℝ) →ₗ[ℝ] ℝ).toAffineMap)
      (AffineSubspace.mk' c (⊥ : Submodule ℝ ℝ)), ?_⟩
    ext ξ
    rw [SetLike.mem_coe, AffineSubspace.mem_comap, AffineSubspace.mem_mk', vsub_eq_sub,
      Submodule.mem_bot, sub_eq_zero, LinearMap.coe_toAffineMap, happ]
    exact Iff.rfl
  have hne : S ≠ ⊤ := by
    intro h
    have hmem : (fun _ => (c + 1) / n : Fin n → ℝ) ∈ S := by rw [h]; trivial
    rw [← SetLike.mem_coe, hcar] at hmem
    have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
    simp only [Set.mem_setOf_eq, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul] at hmem
    field_simp at hmem
    linarith
  have h0 := Measure.addHaar_affineSubspace (volume : Measure (Fin n → ℝ)) S hne
  rwa [hcar] at h0

/-- Consequently every level set of the *squared* coordinate sum — the classical
kinetic energy — is Lebesgue-null on each nonempty parcel sector. -/
theorem volume_sum_sq_level (n : ℕ) (hn : 0 < n) (a : ℝ) :
    (volume : Measure (Fin n → ℝ)) {ξ : Fin n → ℝ | (∑ i, ξ i) ^ 2 = a} = 0 := by
  rcases lt_or_ge a 0 with ha | ha
  · have hempty : {ξ : Fin n → ℝ | (∑ i, ξ i) ^ 2 = a} = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun ξ hξ => ?_
      have hsq : (0 : ℝ) ≤ (∑ i, ξ i) ^ 2 := sq_nonneg _
      rw [Set.mem_setOf_eq] at hξ
      linarith [hξ ▸ hsq]
    rw [hempty, measure_empty]
  · have hc : Real.sqrt a ^ 2 = a := Real.sq_sqrt ha
    have hsub : {ξ : Fin n → ℝ | (∑ i, ξ i) ^ 2 = a}
        ⊆ {ξ : Fin n → ℝ | ∑ i, ξ i = Real.sqrt a}
          ∪ {ξ : Fin n → ℝ | ∑ i, ξ i = -Real.sqrt a} := by
      intro ξ hξ
      rw [Set.mem_setOf_eq] at hξ
      have hprod : (∑ i, ξ i - Real.sqrt a) * (∑ i, ξ i + Real.sqrt a) = 0 := by nlinarith
      rcases mul_eq_zero.1 hprod with h1 | h1
      · exact Or.inl (by simp only [Set.mem_setOf_eq]; linarith)
      · exact Or.inr (by simp only [Set.mem_setOf_eq]; linarith)
    refine le_antisymm ?_ (zero_le _)
    calc (volume : Measure (Fin n → ℝ)) {ξ : Fin n → ℝ | (∑ i, ξ i) ^ 2 = a}
        ≤ volume ({ξ : Fin n → ℝ | ∑ i, ξ i = Real.sqrt a}
            ∪ {ξ : Fin n → ℝ | ∑ i, ξ i = -Real.sqrt a}) := measure_mono hsub
      _ ≤ volume {ξ : Fin n → ℝ | ∑ i, ξ i = Real.sqrt a}
            + volume {ξ : Fin n → ℝ | ∑ i, ξ i = -Real.sqrt a} := measure_union_le _ _
      _ = 0 := by rw [volume_sum_level n hn, volume_sum_level n hn, add_zero]

/-- **Every nonzero level set of the total energy is Fock-null.**  The
zero-parcel sector is excluded by `r ≠ 0`, and every other sector contributes a
null hyperplane pair. -/
theorem fockR_total_level {r : ℝ} (hr : r ≠ 0) :
    fockR {x | momFock.total x = r} = 0 := by
  have hmeas : MeasurableSet {x : ParcelConf ℝ | momFock.total x = r} :=
    momFock.total_meas (measurableSet_singleton r)
  rw [fockMeasure_apply (volume : Measure ℝ) hmeas]
  have hz : ∀ n : ℕ,
      (Measure.pi fun _ : Fin n => (volume : Measure ℝ))
        (parcelMk n ⁻¹' {x : ParcelConf ℝ | momFock.total x = r}) = 0 := by
    intro n
    have hpre : (parcelMk n ⁻¹' {x : ParcelConf ℝ | momFock.total x = r})
        = {ξ : Fin n → ℝ | (∑ i, ξ i) ^ 2 = 2 * r / 3} := by
      ext ξ
      simp only [Set.mem_preimage, Set.mem_setOf_eq, momFock_total, parcelMk]
      constructor
      · intro h; linarith
      · intro h; rw [h]; ring
    rw [hpre]
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · have hempty : {ξ : Fin 0 → ℝ | (∑ i, ξ i) ^ 2 = 2 * r / 3} = ∅ := by
        refine Set.eq_empty_iff_forall_notMem.2 fun ξ hξ => ?_
        simp only [Set.mem_setOf_eq, Finset.univ_eq_empty, Finset.sum_empty] at hξ
        exact hr (by linarith)
      rw [hempty, measure_empty]
    · rw [← volume_pi]
      exact volume_sum_sq_level n hn _
  rw [tsum_congr hz, tsum_zero]

/-- **No eigenvector of nonzero energy.**  The transformed Hamiltonian on the
continuum Fock space has purely continuous spectrum away from the vacuum energy:
`ĥ_full v = λ v` with `λ ≠ 0` forces `v = 0`. -/
theorem momFock_no_eigenvector {lam : ℂ} (hlam : lam ≠ 0) (v : momFock.core)
    (hv : ((momFock.data.hFull v : momFock.core) : Lp ℂ 2 fockR)
      = lam • ((v : Lp ℂ 2 fockR))) :
    ((v : Lp ℂ 2 fockR)) = 0 := by
  refine momFock.hFull_eq_zero_of_eigen ?_ v hv
  by_cases him : lam.im = 0
  · have hre : lam.re ≠ 0 := fun h =>
      hlam (Complex.ext (by simpa using h) (by simpa using him))
    have hset : {x : ParcelConf ℝ | (momFock.total x : ℂ) = lam}
        = {x : ParcelConf ℝ | momFock.total x = lam.re} := by
      ext x
      constructor
      · intro h; simpa using congrArg Complex.re h
      · intro h
        simp only [Set.mem_setOf_eq] at h
        exact Complex.ext (by simpa using h) (by simpa using him.symm)
    rw [hset]
    exact fockR_total_level hre
  · have hempty : {x : ParcelConf ℝ | (momFock.total x : ℂ) = lam} = ∅ := by
      refine Set.eq_empty_iff_forall_notMem.2 fun x hx => ?_
      have h2 := congrArg Complex.im hx
      simp only [Complex.ofReal_im] at h2
      exact him h2.symm
    rw [hempty, measure_empty]

/-! ### The vacuum, an honest eigenvector of energy zero -/

/-- The vacuum sector: the single configuration carrying no parcel at all. -/
def vacSet : Set (ParcelConf ℝ) := parcelMk 0 '' Set.univ

theorem vacSet_measurable : MeasurableSet vacSet :=
  measurableSet_parcel_image MeasurableSet.univ

theorem fockMeasure_vacSet : fockR vacSet = 1 := by
  rw [vacSet, fockMeasure_sector (volume : Measure ℝ) MeasurableSet.univ]
  simp

/-- The vacuum state. -/
noncomputable def vacState : Lp ℂ 2 fockR :=
  (memLp_indicator_const 2 vacSet_measurable (1 : ℂ)
    (Or.inr (by rw [fockMeasure_vacSet]; exact ENNReal.one_ne_top))).toLp _

theorem vacState_coeFn :
    ((vacState : Lp ℂ 2 fockR) : ParcelConf ℝ → ℂ)
      =ᵐ[fockR] vacSet.indicator (fun _ => (1 : ℂ)) :=
  MemLp.coeFn_toLp _

theorem norm_vacState : ‖vacState‖ = 1 := by
  rw [vacState, Lp.norm_toLp,
    eLpNorm_indicator_const vacSet_measurable (by norm_num) (by norm_num), fockMeasure_vacSet]
  simp

theorem vacState_mem_core : vacState ∈ momFock.core := by
  refine ⟨0, ?_⟩
  filter_upwards [vacState_coeFn] with x hx hbig
  rw [hx]
  by_cases hmem : x ∈ vacSet
  · exfalso
    apply hbig
    obtain ⟨ξ, -, rfl⟩ := hmem
    rw [momFock_scale]
    simp [parcelMk]
  · exact Set.indicator_of_notMem hmem _

/-- **The vacuum is an eigenvector of energy zero**, of norm one — so the bound
`lam ≠ 0` in `momFock_no_eigenvector` cannot be dropped.  Every *other* energy is
purely continuous. -/
theorem momFock_vacuum_eigenvector :
    ((momFock.data.hFull ⟨vacState, vacState_mem_core⟩ : momFock.core) : Lp ℂ 2 fockR) = 0 := by
  have key : ((mulD fockR momFock.total_meas momFock.total_dom
      ⟨vacState, vacState_mem_core⟩ : boundedEnergyCore fockR momFock.scale) :
      Lp ℂ 2 fockR) = 0 := by
    refine Lp.ext ?_
    filter_upwards [mulD_coeFn fockR momFock.total_meas momFock.total_dom
        (⟨vacState, vacState_mem_core⟩ : boundedEnergyCore fockR momFock.scale),
      vacState_coeFn, Lp.coeFn_zero (E := ℂ) (p := 2) (μ := fockR)] with x hmul hx hz
    rw [hmul, hz]
    by_cases hmem : x ∈ vacSet
    · obtain ⟨ξ, -, rfl⟩ := hmem
      have h0 : momFock.total (parcelMk 0 ξ) = 0 := by
        rw [momFock_total]; simp [parcelMk]
      rw [h0]
      simp
    · rw [hx, Set.indicator_of_notMem hmem]
      simp
  rw [momFock.hFull_eq_mulD]
  exact key

/-! ## Back to the Eulerian operator -/

section Transfer

variable {Ω : Type*} [MeasurableSpace Ω] {F : Type*} [NormedAddCommGroup F]
  [InnerProductSpace ℂ F]

/-- **Essential self-adjointness of the untruncated Eulerian Navier–Stokes
Hamiltonian, obtained after the Lagrangian change of variables on the continuum
Fock space.**  If a unitary change of variables carries the Eulerian data onto
the second-quantized Lagrangian data of `fockLagSymbols`, intertwining the two
Hamiltonians, then the Eulerian Hamiltonian inherits vanishing adjoint
deficiency: the continuum computation is done once, in the momentum
representation, and transfers back. -/
theorem nsFullData_hasZeroDeficiencyOn_of_continuumFock (d : FullEsa.NSFullData F)
    (μ : Measure Ω) {p q dr : Fin 3 → Ω → ℝ} {cf : Ω → ℝ} (hp : ∀ i, Measurable (p i))
    (hq : ∀ i, Measurable (q i)) (hd : ∀ i, Measurable (dr i)) (hc : Measurable cf)
    (force : Fin 3 → ℝ) {nu : ℝ} (hnu : 0 ≤ nu)
    (W : F ≃ₗᵢ[ℂ] Lp ℂ 2 (fockMeasure μ))
    (hmap : ∀ x : d.D, W (x : F) ∈ (fockLagSymbols μ hp hq hd hc force hnu).data.D)
    (hsurj : ∀ y : (fockLagSymbols μ hp hq hd hc force hnu).data.D,
      ∃ x : d.D, W (x : F) = (y : Lp ℂ 2 (fockMeasure μ)))
    (hint : ∀ x : d.D,
      (((fockLagSymbols μ hp hq hd hc force hnu).data.hFull ⟨W (x : F), hmap x⟩ :
        (fockLagSymbols μ hp hq hd hc force hnu).data.D) : Lp ℂ 2 (fockMeasure μ))
        = W ((d.hamiltonian x : F))) :
    HasZeroDeficiencyOn d.D d.hamiltonian :=
  LagrangianEsa.NSFullData.hasZeroDeficiencyOn_of_lagrangian d _ W hmap hsurj hint
    (fockLagrangian_hasZeroDeficiencyOn μ hp hq hd hc force hnu)

end Transfer

end FockLagrangian

end BookProof.NavierStokesFlow
