import Mathlib
import BookProof.ChapterNavierStokesEsa
import BookProof.ChapterNavierStokesIkebeKato
import BookProof.ChapterFriedrichsExtension
import BookProof.ChapterYangMillsHermite
import BookProof.ChapterFockSecondQuantization.Part2

/-!
# Second quantization over a one-particle core (Part F.11)

`PLAN_LEAN_SPECIALIST_QYM_FLOW.md` Part F.11 asks for the **second-quantized**
Hamiltonian on the finite-occupation states over the one-particle core, i.e. the
last row of the field-space realization of the gauge-fixed Yang–Mills
Hamiltonian.

The Fock space over a one-particle space with a countable orthonormal basis
`(e_k)` is `ℓ²` over the *configurations* `Conf = ℕ →₀ ℕ` (occupation numbers,
finitely many excited modes), and the finite-occupation domain is the dense
subspace `lpFiniteModes Conf` of finitely supported configuration vectors.  All
operators are defined at the *algebraic* level on `FockAlg = Conf →₀ ℂ` — where
linearity is free — and transported to the Hilbert space by the isomorphism
`fockEquiv`.

* `up`, `dn` — adding and removing one quantum in a mode;
* `annA j`, `creA j` — annihilation and creation, with the canonical commutation
  relation `[a_j, a_j†] = 1` (`ccr_annA_creA`) and the adjoint pairing
  `⟪a_j† u, v⟫ = ⟪u, a_j v⟫` (`inner_creA_left`);
* `dGamma col` — the second quantization `dΓ(A) = Σ_{j,k} ⟪e_j, A e_k⟫ a_j† a_k`
  of a one-particle operator given by its (column-finite) matrix `col`, and
  `dGamma_one_particle`, which checks that on the one-particle sector it *is*
  the one-particle operator;
* `dGammaOp_symmetricOn`, `dGammaOp_quadForm_nonneg` — symmetry and positivity of
  `dΓ(A)` on the finite-occupation domain, from Hermiticity and positivity of the
  one-particle matrix;
* `dGamma_friedrichs_extension` — hence `dΓ(A)` has a positive self-adjoint
  (Friedrichs) extension;
* `secondQuantization_friedrichs` — the same for the matrix of an arbitrary
  symmetric positive one-particle operator on the finite-mode domain of a Hilbert
  basis;
* `ym_fock_friedrichs_extension` — **F.11**: the second quantization of the
  field-space Yang–Mills Hamiltonian `H₁ = ½Σπ² + ½ΣB²` of
  `BookProof.YangMillsHermite` has a positive self-adjoint extension on the Fock
  space over the Gauss–polynomial core of `L²(ℝ⁹⁹)`;
* `dGamma_hashimoto_selects`, `secondQuantization_hashimoto_selects` and
  `ym_fock_hashimoto_selects` — the Hashimoto/SIRK shift-invert limit selects
  exactly that Friedrichs extension, with the Galerkin truncations of the
  shift-inverted operator converging strongly and in the resolvent sense.

No mass gap and no global existence is claimed; the Millennium problem stays out
of scope.
-/

namespace BookProof.FockSecondQuantization

open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.YangMillsFriedrichs
open BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.HashimotoShiftInvert

noncomputable section
/-! ## The matrix of a one-particle operator -/

section OneParticle

variable {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]

/-- The coordinates of a finite-mode vector, as a finitely supported function. -/
def coordFinsupp (b : HilbertBasis ℕ ℂ F) (x : F) : ℕ →₀ ℂ := by
  classical
  exact if h : x ∈ finiteModeDomain b then
    (Finsupp.mem_span_range_iff_exists_finsupp.mp h).choose else 0

theorem coordFinsupp_apply {b : HilbertBasis ℕ ℂ F} {x : F} (hx : x ∈ finiteModeDomain b)
    (j : ℕ) : coordFinsupp b x j = inner ℂ (b j) x := by
  classical
  have hx' : x ∈ Submodule.span ℂ (Set.range b) := hx
  have hspec : ((Finsupp.mem_span_range_iff_exists_finsupp.mp hx').choose.sum
      fun i a => a • b i) = x := (Finsupp.mem_span_range_iff_exists_finsupp.mp hx').choose_spec
  rw [coordFinsupp, dif_pos hx]
  conv_rhs => rw [← hspec]
  rw [← Finsupp.linearCombination_apply, b.orthonormal.inner_right_finsupp]

/-- The matrix of a one-particle operator in the basis `b`. -/
def opCol (b : HilbertBasis ℕ ℂ F) (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b)
    (k : ℕ) : ℕ →₀ ℂ :=
  coordFinsupp b (A ⟨b k, Submodule.subset_span ⟨k, rfl⟩⟩ : finiteModeDomain b)

theorem opCol_apply (b : HilbertBasis ℕ ℂ F) (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b)
    (k j : ℕ) :
    opCol b A k j
      = inner ℂ (b j) ((A ⟨b k, Submodule.subset_span ⟨k, rfl⟩⟩ : finiteModeDomain b) : F) :=
  coordFinsupp_apply (A ⟨b k, Submodule.subset_span ⟨k, rfl⟩⟩ : finiteModeDomain b).2 j

theorem isHermCol_opCol {b : HilbertBasis ℕ ℂ F}
    {A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b}
    (hA : SymmetricOn (finiteModeDomain b) ((finiteModeDomain b).subtype.comp A)) :
    IsHermCol (opCol b A) := by
  intro j k
  have h := hA ⟨b k, Submodule.subset_span ⟨k, rfl⟩⟩ ⟨b j, Submodule.subset_span ⟨j, rfl⟩⟩
  simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.subtype_apply] at h
  rw [opCol_apply, opCol_apply, ← h, inner_conj_symm]

theorem isPosCol_opCol {b : HilbertBasis ℕ ℂ F}
    {A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b}
    (hpos : ∀ x, 0 ≤ quadForm ((finiteModeDomain b).subtype.comp A) x) :
    IsPosCol (opCol b A) := by
  intro S c
  classical
  set x : finiteModeDomain b :=
    ∑ k ∈ S, c k • (⟨b k, Submodule.subset_span ⟨k, rfl⟩⟩ : finiteModeDomain b) with hxdef
  have hxc : ((x : finiteModeDomain b) : F) = ∑ k ∈ S, c k • b k := by
    rw [hxdef, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun k _ => rfl
  have hAx : ((A x : finiteModeDomain b) : F)
      = ∑ k ∈ S, c k • ((A ⟨b k, Submodule.subset_span ⟨k, rfl⟩⟩ : finiteModeDomain b) : F) := by
    rw [hxdef, map_sum, Submodule.coe_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_smul]; rfl
  have hval : (inner ℂ ((x : finiteModeDomain b) : F)
        (((finiteModeDomain b).subtype.comp A) x) : ℂ)
      = ∑ j ∈ S, ∑ k ∈ S, (starRingEnd ℂ) (c j) * opCol b A k j * c k := by
    change (inner ℂ ((x : finiteModeDomain b) : F)
      ((A x : finiteModeDomain b) : F) : ℂ) = _
    rw [hxc, hAx, sum_inner]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [inner_smul_left, inner_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [inner_smul_right, opCol_apply]
    ring
  have hq := hpos x
  rw [quadForm, hval] at hq
  exact hq

/-- **Second quantization of an arbitrary symmetric positive one-particle
operator**: `dΓ(A)` on the finite-occupation domain of the Fock space has a
positive self-adjoint (Friedrichs) extension. -/
theorem secondQuantization_friedrichs (b : HilbertBasis ℕ ℂ F)
    (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b)
    (hA : SymmetricOn (finiteModeDomain b) ((finiteModeDomain b).subtype.comp A))
    (hpos : ∀ x, 0 ≤ quadForm ((finiteModeDomain b).subtype.comp A) x) :
    ∃ (Dom : Submodule ℂ Fock) (A' : Dom →ₗ[ℂ] Fock),
      IsPositiveSelfAdjointExtension (dGammaOp (opCol b A)) A' :=
  dGamma_friedrichs_extension (isHermCol_opCol hA) (isPosCol_opCol hpos)

end OneParticle

/-! ## The Hashimoto/SIRK selection for the second-quantized operator -/

section Selection

open Filter Topology

/-- The canonical Hilbert basis of the Fock space, indexed by the
configurations. -/
def fockConfBasis : HilbertBasis Conf ℂ Fock :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

theorem fockConfBasis_apply (α : Conf) : fockConfBasis α = lp.single 2 α (1 : ℂ) := by
  rw [← HilbertBasis.repr_symm_single]
  rfl

/-- The Fock basis re-indexed by `ℕ`, the form in which the abstract Friedrichs
and Hashimoto theorems are stated. -/
def fockBasisN (ε : ℕ ≃ Conf) : HilbertBasis ℕ ℂ Fock :=
  HilbertBasis.mk (fockConfBasis.orthonormal.comp _ ε.injective)
    (by
      have h := fockConfBasis.dense_span
      rw [Set.range_comp, ε.range_eq_univ, Set.image_univ]
      exact h.ge)

theorem fockBasisN_apply (ε : ℕ ≃ Conf) (n : ℕ) :
    fockBasisN ε n = lp.single 2 (ε n) (1 : ℂ) := by
  rw [fockBasisN, HilbertBasis.coe_mk]
  exact fockConfBasis_apply _

theorem lp_sum_single_coord (S : Finset Conf) (f : Conf → ℂ) (β : Conf) :
    (((∑ α ∈ S, f α • lp.single 2 α (1 : ℂ)) : Fock) : Conf → ℂ) β
      = if β ∈ S then f β else 0 := by
  classical
  induction S using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    simp only [lp.coeFn_add, Pi.add_apply, lp.coeFn_smul, Pi.smul_apply, smul_eq_mul,
      lp.single_apply, ih]
    by_cases hb : β = a
    · subst hb
      simp [ha]
    · simp [hb, Finset.mem_insert]

/-- **The finite-mode domain of the Fock basis is exactly the finite-occupation
domain**, so the abstract theorems apply verbatim to `dΓ`. -/
theorem finiteModeDomain_fockBasisN (ε : ℕ ≃ Conf) :
    finiteModeDomain (fockBasisN ε) = lpFiniteModes Conf := by
  classical
  refine le_antisymm (Submodule.span_le.mpr ?_) fun x hx => ?_
  · rintro y ⟨n, rfl⟩
    rw [fockBasisN_apply]
    exact lpSingle_mem_lpFiniteModes _ _
  · set S : Finset Conf := hx.toFinset with hS
    have hxeq : x = ∑ α ∈ S, ((x : Conf → ℂ) α) • lp.single 2 α (1 : ℂ) := by
      refine lp.ext (funext fun β => ?_)
      rw [lp_sum_single_coord]
      by_cases hb : β ∈ S
      · simp [hb]
      · have hz : (x : Conf → ℂ) β = 0 := by
          by_contra hc
          exact hb (hx.mem_toFinset.mpr hc)
        simp [hb, hz]
    rw [hxeq]
    refine Submodule.sum_mem _ fun α _ => Submodule.smul_mem _ _ ?_
    refine Submodule.subset_span ⟨ε.symm α, ?_⟩
    rw [fockBasisN_apply, Equiv.apply_symm_apply]

/-- The second-quantized operator on the finite-mode domain of `fockBasisN ε`
(the same subspace as `lpFiniteModes Conf`). -/
def dGammaOpB (ε : ℕ ≃ Conf) (col : ℕ → (ℕ →₀ ℂ)) :
    finiteModeDomain (fockBasisN ε) →ₗ[ℂ] Fock :=
  (dGammaOp col).comp (LinearEquiv.ofEq _ _ (finiteModeDomain_fockBasisN ε)).toLinearMap

theorem dGammaOpB_symmetricOn {ε : ℕ ≃ Conf} {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col) :
    SymmetricOn (finiteModeDomain (fockBasisN ε)) (dGammaOpB ε col) := by
  intro x y
  exact dGammaOp_symmetricOn hherm
    (LinearEquiv.ofEq _ _ (finiteModeDomain_fockBasisN ε) x)
    (LinearEquiv.ofEq _ _ (finiteModeDomain_fockBasisN ε) y)

theorem dGammaOpB_quadForm_nonneg {ε : ℕ ≃ Conf} {col : ℕ → (ℕ →₀ ℂ)} (hpos : IsPosCol col)
    (x : finiteModeDomain (fockBasisN ε)) : 0 ≤ quadForm (dGammaOpB ε col) x :=
  dGammaOp_quadForm_nonneg hpos
    (LinearEquiv.ofEq _ _ (finiteModeDomain_fockBasisN ε) x)

/-- **The Hashimoto/SIRK shift-invert limit selects the Friedrichs extension of
the second-quantized Hamiltonian.**  For a Hermitian, positive semidefinite,
column-finite one-particle matrix the second quantization `dΓ(A)` has a positive
self-adjoint extension `A'`, and for every shift `γ > 0` the shift-inverted
operator `R = (A' + γ)⁻¹` is bounded and self-adjoint, its Galerkin truncations
converge strongly and in the resolvent sense, and `R` determines `A'`
uniquely. -/
theorem dGamma_hashimoto_selects (ε : ℕ ≃ Conf) {col : ℕ → (ℕ →₀ ℂ)}
    (hherm : IsHermCol col) (hpos : IsPosCol col) {γ : ℝ} (hγ : 0 < γ) :
    ∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock) (R : Fock →L[ℂ] Fock),
      IsPositiveSelfAdjointExtension (dGammaOpB ε col) A ∧ IsShiftInvert A γ R ∧
        ‖R‖ ≤ γ⁻¹ ∧ IsSelfAdjoint R ∧
        (∀ u : Fock, Tendsto (fun k : ℕ => galerkinCompression R (fockBasisN ε) k u)
          atTop (nhds (R u))) ∧
        (∀ z : ℂ, z.im ≠ 0 → ∀ u : Fock,
          Tendsto (fun k : ℕ => resolvent (galerkinCompression R (fockBasisN ε) k) z u) atTop
            (nhds (resolvent R z u))) ∧
        (∀ (Dom' : Submodule ℂ Fock) (A' : Dom' →ₗ[ℂ] Fock), IsShiftInvert A' γ R →
          Dom' = Dom ∧ ∀ (x : Fock) (hx : x ∈ Dom) (hx' : x ∈ Dom'), A' ⟨x, hx'⟩ = A ⟨x, hx⟩) :=
  friedrichs_hashimoto_selects (fockBasisN ε) (dGammaOpB ε col)
    (dGammaOpB_symmetricOn hherm) (dGammaOpB_quadForm_nonneg hpos) hγ

/-- A concrete enumeration of the configurations, so that the selection theorem
is not vacuous. -/
def fockEnum : ℕ ≃ Conf :=
  letI : Denumerable Conf := Denumerable.ofEncodableOfInfinite _
  (Denumerable.eqv Conf).symm

/-- **The Hashimoto/SIRK algorithm selects the Friedrichs extension of the second
quantization of an arbitrary symmetric positive one-particle operator.** -/
theorem secondQuantization_hashimoto_selects {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] (ε : ℕ ≃ Conf) (b : HilbertBasis ℕ ℂ F)
    (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b)
    (hA : SymmetricOn (finiteModeDomain b) ((finiteModeDomain b).subtype.comp A))
    (hpos : ∀ x, 0 ≤ quadForm ((finiteModeDomain b).subtype.comp A) x)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ (Dom : Submodule ℂ Fock) (A' : Dom →ₗ[ℂ] Fock) (R : Fock →L[ℂ] Fock),
      IsPositiveSelfAdjointExtension (dGammaOpB ε (opCol b A)) A' ∧ IsShiftInvert A' γ R ∧
        ‖R‖ ≤ γ⁻¹ ∧ IsSelfAdjoint R ∧
        (∀ u : Fock, Tendsto (fun k : ℕ => galerkinCompression R (fockBasisN ε) k u)
          atTop (nhds (R u))) ∧
        (∀ z : ℂ, z.im ≠ 0 → ∀ u : Fock,
          Tendsto (fun k : ℕ => resolvent (galerkinCompression R (fockBasisN ε) k) z u) atTop
            (nhds (resolvent R z u))) ∧
        (∀ (Dom' : Submodule ℂ Fock) (A'' : Dom' →ₗ[ℂ] Fock), IsShiftInvert A'' γ R →
          Dom' = Dom ∧ ∀ (x : Fock) (hx : x ∈ Dom) (hx' : x ∈ Dom'),
            A'' ⟨x, hx'⟩ = A' ⟨x, hx⟩) :=
  dGamma_hashimoto_selects ε (isHermCol_opCol hA) (isPosCol_opCol hpos) hγ

end Selection

/-! ## The second-quantized Yang–Mills Hamiltonian (F.11) -/

section YangMills

open BookProof.YangMillsHermite BookProof.HermiteProductCore
open Filter Topology

/-- The inner one-particle Yang–Mills Hamiltonian `H₁ = ½Σπ² + ½ΣB²` as an
endomorphism of the Gauss–polynomial core. The full final nested-Fock
Hamiltonian is its outer creation-left/annihilation-right enclosure; inner
pair terms are retained in `H₁`, and the outer annihilator kills the outer
vacuum.  The operator is realized as the finite-mode domain of
the orthonormal basis `coreBasis e` of `L²(ℝ⁹⁹)`. -/
def ymOnePart (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    finiteModeDomain (coreBasis e) →ₗ[ℂ] finiteModeDomain (coreBasis e) :=
  weylOpDom (piOps (coreRepBasis e)) (magOps (coreRepBasis e) fabc)

theorem coe_ymOnePart (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (x : finiteModeDomain (coreBasis e)) :
    ((ymOnePart e fabc x : finiteModeDomain (coreBasis e)) : L2d 99)
      = ymHamiltonian (coreRepBasis e) fabc x := rfl

/-- The matrix of the one-particle Yang–Mills Hamiltonian in the product Hermite
basis. -/
def ymFockCol (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) : ℕ → (ℕ →₀ ℂ) :=
  opCol (coreBasis e) (ymOnePart e fabc)

theorem ymFockCol_apply (e : ℕ ≃ (Fin 99 →₀ ℕ)) (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (k j : ℕ) :
    ymFockCol e fabc k j
      = inner ℂ (coreBasis e j)
          (ymHamiltonian (coreRepBasis e) fabc
            ⟨coreBasis e k, Submodule.subset_span ⟨k, rfl⟩⟩) :=
  opCol_apply _ _ k j

/-- **F.11 — the second-quantized field-space Yang–Mills Hamiltonian has a
positive self-adjoint extension.**  The one-particle operator is the concrete
`H₁ = ½Σπ² + ½ΣB²` of `BookProof.YangMillsHermite` on the Gauss–polynomial core
of `L²(ℝ⁹⁹)`; its second quantization
`dΓ(H₁) = Σ_{j,k} ⟪e_j, H₁ e_k⟫ a_j† a_k` on the finite-occupation states over
that core is symmetric and positive, hence has a positive self-adjoint
(Friedrichs) extension.  No mass gap is claimed. -/
theorem ym_fock_friedrichs_extension (e : ℕ ≃ (Fin 99 →₀ ℕ))
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    ∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock),
      IsPositiveSelfAdjointExtension (dGammaOp (ymFockCol e fabc)) A :=
  secondQuantization_friedrichs (coreBasis e) (ymOnePart e fabc)
    (ymHamiltonian_symmetricOn (coreRepBasis e) fabc)
    (ymHamiltonian_quadForm_nonneg (coreRepBasis e) fabc)

/-- **F.11 — the Hashimoto/SIRK algorithm selects the Friedrichs extension of the
second-quantized field-space Yang–Mills Hamiltonian.**  On the finite-occupation
states over the Gauss–polynomial core of `L²(ℝ⁹⁹)`, the second quantization
`dΓ(H₁)` of `H₁ = ½Σπ² + ½ΣB²` has a positive self-adjoint (Friedrichs)
extension `A`; for every shift `γ > 0` the shift-inverted operator
`R = (A + γ)⁻¹` is bounded by `γ⁻¹` and self-adjoint, its Galerkin truncations
converge strongly and in the resolvent sense, and `R` determines `A` uniquely.
No mass gap is claimed. -/
theorem ym_fock_hashimoto_selects (e : ℕ ≃ (Fin 99 →₀ ℕ))
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) (ε : ℕ ≃ Conf) {γ : ℝ} (hγ : 0 < γ) :
    ∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock) (R : Fock →L[ℂ] Fock),
      IsPositiveSelfAdjointExtension (dGammaOpB ε (ymFockCol e fabc)) A ∧
        IsShiftInvert A γ R ∧ ‖R‖ ≤ γ⁻¹ ∧ IsSelfAdjoint R ∧
        (∀ u : Fock, Tendsto (fun k : ℕ => galerkinCompression R (fockBasisN ε) k u)
          atTop (nhds (R u))) ∧
        (∀ z : ℂ, z.im ≠ 0 → ∀ u : Fock,
          Tendsto (fun k : ℕ => resolvent (galerkinCompression R (fockBasisN ε) k) z u) atTop
            (nhds (resolvent R z u))) ∧
        (∀ (Dom' : Submodule ℂ Fock) (A' : Dom' →ₗ[ℂ] Fock), IsShiftInvert A' γ R →
          Dom' = Dom ∧ ∀ (x : Fock) (hx : x ∈ Dom) (hx' : x ∈ Dom'), A' ⟨x, hx'⟩ = A ⟨x, hx⟩) :=
  secondQuantization_hashimoto_selects ε (coreBasis e) (ymOnePart e fabc)
    (ymHamiltonian_symmetricOn (coreRepBasis e) fabc)
    (ymHamiltonian_quadForm_nonneg (coreRepBasis e) fabc) hγ

end YangMills

end

end BookProof.FockSecondQuantization
