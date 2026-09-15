import Mathlib
import BookProof.ChapterFockSecondQuantization
import BookProof.ChapterBRSTNilpotent
import BookProof.ChapterFermionFock.Part2

/-!
# Chapter FermionFock — the fermionic (CAR) Fock space and its second quantization

`CONSOLIDATED_PLAN.md` §10.6.2 item 3 asks for the missing **fermionic half** of
the quantum-gravity second quantization: the project builds the bosonic Fock
space `Γˢ` over a one-particle core (`ChapterFockSecondQuantization`, occupation
numbers `Conf = ℕ →₀ ℕ`), but the antisymmetric factor `Γᵃ` — the ghost/fermion
sector, whose canonical **anticommutation** relations `ChapterBRSTNilpotent`
carries as the abstract hypothesis `GhostCAR` — is not constructed anywhere.

This chapter constructs it, in exactly the style of the bosonic one.

## Deliverables

* `FConf`, `FermiAlg`, `FermiFock` — a fermionic configuration is the **finite
  set of occupied modes**, the algebraic Fock space is `FConf →₀ ℂ`, and the
  Fock space is `ℓ²(FConf)`.
* `fsign` — the Jordan–Wigner sign `(−1)^{#\{i ∈ S : i < j\}}`, and the sign
  calculus it obeys (`fsign_mul_self`, `fsign_erase`, `fsign_insert_self`,
  `fsign_insert_of_ne`).
* `creF`, `annF` — creation and annihilation, with their coordinate formulas
  `creF_apply`, `annF_apply`.
* **The canonical anticommutation relations**, all four of them:
  `car_annF_creF_self` (`{c_j, c_j†} = 1`), `car_creF_creF` (`{c_j†, c_k†} = 0`,
  including `creF_creF_self`: `(c_j†)² = 0`, the Pauli principle),
  `car_annF_annF` (`{c_j, c_k} = 0`) and `car_annF_creF_of_ne`
  (`{c_j, c_k†} = 0` for `j ≠ k`).
* `inner_creF_left` — creation and annihilation are formal adjoints of each
  other on the finite-occupation domain.
* `dGammaF`, `dGammaOpF` — the fermionic second quantization
  `dΓᵃ(A) = Σ_{j,k} ⟪e_j, A e_k⟫ c_j† c_k`, its symmetry
  (`dGammaOpF_symmetricOn`) and positivity (`dGammaOpF_quadForm_nonneg`) for a
  Hermitian, positive semidefinite one-particle matrix.
* `dGammaF_friedrichs_extension`, `secondQuantizationF_friedrichs` — the
  fermionic second quantization of any symmetric positive one-particle operator
  has a positive self-adjoint (Friedrichs) extension …
* `dGammaF_hashimoto_selects`, `secondQuantizationF_hashimoto_selects` — … and
  the Hashimoto/SIRK shift-invert limit selects exactly that extension, with the
  Galerkin truncations converging strongly and in the resolvent sense.
* `parityF` — the fermion-number parity `(−1)^{N_f}`, the `ℤ₂` grading
  operator: an involution (`parityF_involutive`) that anticommutes with both
  creation and annihilation (`parityF_creF`, `parityF_annF`).
* `ghostCAR_creF_annF` — **the abstract ghost relations are realized**: the
  operators built here satisfy `BookProof.BRSTNilpotent.GhostCAR`, so the BRST
  chapter's hypotheses are not vacuous — and `brst_charge_nilpotent_fermiFock`
  is the resulting concrete nilpotency `Q² = 0`.

Everything is `sorry`-free and `axiom`-free (only `propext`, `Classical.choice`,
`Quot.sound`).
-/

namespace BookProof.FermionFock

open BookProof.NavierStokesFlow BookProof.NavierStokesFlow.IkebeKato
open BookProof.FarisLavine BookProof.HermiteGalerkin BookProof.FriedrichsExtension
open BookProof.YangMillsFriedrichs
open BookProof.HashimotoShiftInvert
open BookProof.FockSecondQuantization (IsHermCol IsPosCol opCol isHermCol_opCol isPosCol_opCol)

noncomputable section
/-! ## The Hashimoto/SIRK selection for the fermionic second quantization -/

section Selection

open Filter Topology

variable {ι : Type*} [DecidableEq ι]

/-- The canonical Hilbert basis of `ℓ²(ι)`, indexed by `ι` itself. -/
def l2Basis (ι : Type*) : HilbertBasis ι ℂ (L2I ι) :=
  HilbertBasis.ofRepr (LinearIsometryEquiv.refl ℂ _)

theorem l2Basis_apply (α : ι) : l2Basis ι α = lp.single 2 α (1 : ℂ) := by
  rw [← HilbertBasis.repr_symm_single]
  rfl

/-- The canonical basis of `ℓ²(ι)` re-indexed by `ℕ`, the form in which the
abstract Friedrichs and Hashimoto theorems are stated. -/
def l2BasisN (ε : ℕ ≃ ι) : HilbertBasis ℕ ℂ (L2I ι) :=
  HilbertBasis.mk ((l2Basis ι).orthonormal.comp _ ε.injective)
    (by
      have h := (l2Basis ι).dense_span
      rw [Set.range_comp, ε.range_eq_univ, Set.image_univ]
      exact h.ge)

theorem l2BasisN_apply (ε : ℕ ≃ ι) (n : ℕ) :
    l2BasisN ε n = lp.single 2 (ε n) (1 : ℂ) := by
  rw [l2BasisN, HilbertBasis.coe_mk]
  exact l2Basis_apply _

theorem lp_sum_single_coordI (S : Finset ι) (f : ι → ℂ) (β : ι) :
    (((∑ α ∈ S, f α • lp.single 2 α (1 : ℂ)) : L2I ι) : ι → ℂ) β
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

omit [DecidableEq ι] in
/-- **The finite-mode domain of the canonical basis of `ℓ²(ι)` is exactly the
finitely supported subspace**, so the abstract theorems apply verbatim. -/
theorem finiteModeDomain_l2BasisN (ε : ℕ ≃ ι) :
    finiteModeDomain (l2BasisN ε) = lpFiniteModes ι := by
  classical
  refine le_antisymm (Submodule.span_le.mpr ?_) fun x hx => ?_
  · rintro y ⟨n, rfl⟩
    rw [l2BasisN_apply]
    exact lpSingle_mem_lpFiniteModes _ _
  · set S : Finset ι := hx.toFinset with hS
    have hxeq : x = ∑ α ∈ S, ((x : ι → ℂ) α) • lp.single 2 α (1 : ℂ) := by
      refine lp.ext (funext fun β => ?_)
      rw [lp_sum_single_coordI]
      by_cases hb : β ∈ S
      · simp [hb]
      · have hz : (x : ι → ℂ) β = 0 := by
          by_contra hc
          exact hb (hx.mem_toFinset.mpr hc)
        simp [hb, hz]
    rw [hxeq]
    refine Submodule.sum_mem _ fun α _ => Submodule.smul_mem _ _ ?_
    refine Submodule.subset_span ⟨ε.symm α, ?_⟩
    rw [l2BasisN_apply, Equiv.apply_symm_apply]

/-- The fermionic second-quantized operator on the finite-mode domain of
`l2BasisN ε` (the same subspace as `lpFiniteModes FConf`). -/
def dGammaOpFB (ε : ℕ ≃ FConf) (col : ℕ → (ℕ →₀ ℂ)) :
    finiteModeDomain (l2BasisN ε) →ₗ[ℂ] FermiFock :=
  (dGammaOpF col).comp (LinearEquiv.ofEq _ _ (finiteModeDomain_l2BasisN ε)).toLinearMap

theorem dGammaOpFB_symmetricOn {ε : ℕ ≃ FConf} {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col) :
    SymmetricOn (finiteModeDomain (l2BasisN ε)) (dGammaOpFB ε col) := by
  intro x y
  exact dGammaOpF_symmetricOn hherm
    (LinearEquiv.ofEq _ _ (finiteModeDomain_l2BasisN ε) x)
    (LinearEquiv.ofEq _ _ (finiteModeDomain_l2BasisN ε) y)

theorem dGammaOpFB_quadForm_nonneg {ε : ℕ ≃ FConf} {col : ℕ → (ℕ →₀ ℂ)} (hpos : IsPosCol col)
    (x : finiteModeDomain (l2BasisN ε)) : 0 ≤ quadForm (dGammaOpFB ε col) x :=
  dGammaOpF_quadForm_nonneg hpos
    (LinearEquiv.ofEq _ _ (finiteModeDomain_l2BasisN ε) x)

/-- **The Hashimoto/SIRK shift-invert limit selects the Friedrichs extension of
the fermionic second-quantized Hamiltonian.** -/
theorem dGammaF_hashimoto_selects (ε : ℕ ≃ FConf) {col : ℕ → (ℕ →₀ ℂ)}
    (hherm : IsHermCol col) (hpos : IsPosCol col) {γ : ℝ} (hγ : 0 < γ) :
    ∃ (Dom : Submodule ℂ FermiFock) (A : Dom →ₗ[ℂ] FermiFock) (R : FermiFock →L[ℂ] FermiFock),
      IsPositiveSelfAdjointExtension (dGammaOpFB ε col) A ∧ IsShiftInvert A γ R ∧
        ‖R‖ ≤ γ⁻¹ ∧ IsSelfAdjoint R ∧
        (∀ u : FermiFock, Tendsto (fun k : ℕ => galerkinCompression R (l2BasisN ε) k u)
          atTop (nhds (R u))) ∧
        (∀ z : ℂ, z.im ≠ 0 → ∀ u : FermiFock,
          Tendsto (fun k : ℕ => resolvent (galerkinCompression R (l2BasisN ε) k) z u) atTop
            (nhds (resolvent R z u))) ∧
        (∀ (Dom' : Submodule ℂ FermiFock) (A' : Dom' →ₗ[ℂ] FermiFock), IsShiftInvert A' γ R →
          Dom' = Dom ∧ ∀ (x : FermiFock) (hx : x ∈ Dom) (hx' : x ∈ Dom'),
            A' ⟨x, hx'⟩ = A ⟨x, hx⟩) :=
  friedrichs_hashimoto_selects (l2BasisN ε) (dGammaOpFB ε col)
    (dGammaOpFB_symmetricOn hherm) (dGammaOpFB_quadForm_nonneg hpos) hγ

/-- A concrete enumeration of the fermionic configurations, so that the
selection theorem is not vacuous. -/
def fermiEnum : ℕ ≃ FConf :=
  letI : Denumerable FConf := Denumerable.ofEncodableOfInfinite _
  (Denumerable.eqv FConf).symm

/-- **The Hashimoto/SIRK algorithm selects the Friedrichs extension of the
fermionic second quantization of an arbitrary symmetric positive one-particle
operator.** -/
theorem secondQuantizationF_hashimoto_selects {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] (ε : ℕ ≃ FConf) (b : HilbertBasis ℕ ℂ F)
    (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b)
    (hA : SymmetricOn (finiteModeDomain b) ((finiteModeDomain b).subtype.comp A))
    (hpos : ∀ x, 0 ≤ quadForm ((finiteModeDomain b).subtype.comp A) x)
    {γ : ℝ} (hγ : 0 < γ) :
    ∃ (Dom : Submodule ℂ FermiFock) (A' : Dom →ₗ[ℂ] FermiFock) (R : FermiFock →L[ℂ] FermiFock),
      IsPositiveSelfAdjointExtension (dGammaOpFB ε (opCol b A)) A' ∧ IsShiftInvert A' γ R ∧
        ‖R‖ ≤ γ⁻¹ ∧ IsSelfAdjoint R ∧
        (∀ u : FermiFock, Tendsto (fun k : ℕ => galerkinCompression R (l2BasisN ε) k u)
          atTop (nhds (R u))) ∧
        (∀ z : ℂ, z.im ≠ 0 → ∀ u : FermiFock,
          Tendsto (fun k : ℕ => resolvent (galerkinCompression R (l2BasisN ε) k) z u) atTop
            (nhds (resolvent R z u))) ∧
        (∀ (Dom' : Submodule ℂ FermiFock) (A'' : Dom' →ₗ[ℂ] FermiFock), IsShiftInvert A'' γ R →
          Dom' = Dom ∧ ∀ (x : FermiFock) (hx : x ∈ Dom) (hx' : x ∈ Dom'),
            A'' ⟨x, hx'⟩ = A' ⟨x, hx⟩) :=
  dGammaF_hashimoto_selects ε (isHermCol_opCol hA) (isPosCol_opCol hpos) hγ

end Selection

/-! ## The BRST ghost relations are realized

`BookProof.BRSTNilpotent` proves the nilpotency `Q² = 0` of the cubic ghost BRST
charge from the *abstract* hypothesis `GhostCAR χ β`.  The operators built in
this chapter satisfy it, so those hypotheses are not vacuous. -/

/-- The ghost creation operators `χ_a = c_a†` on the fermionic Fock space. -/
def ghostChi (n : ℕ) : Fin n → Module.End ℂ FermiAlg := fun a => creF a.val

/-- The ghost annihilation operators `β_a = c_a` on the fermionic Fock space. -/
def ghostBeta (n : ℕ) : Fin n → Module.End ℂ FermiAlg := fun a => annF a.val

/-- **The abstract ghost anticommutation relations of `ChapterBRSTNilpotent` are
realized** by the creation and annihilation operators of the fermionic Fock
space. -/
theorem ghostCAR_creF_annF (n : ℕ) :
    BookProof.BRSTNilpotent.GhostCAR (ghostChi n) (ghostBeta n) where
  chichi a b := by
    refine LinearMap.ext fun u => ?_
    simpa [ghostChi, Module.End.mul_apply] using car_creF_creF a.val b.val u
  betabeta a b := by
    refine LinearMap.ext fun u => ?_
    simpa [ghostBeta, Module.End.mul_apply] using car_annF_annF a.val b.val u
  betachi a b := by
    refine LinearMap.ext fun u => ?_
    rcases eq_or_ne a b with rfl | hab
    · simpa [ghostChi, ghostBeta, Module.End.mul_apply] using car_annF_creF_self a.val u
    · have hval : a.val ≠ b.val := fun h => hab (Fin.ext h)
      simpa [ghostChi, ghostBeta, Module.End.mul_apply, hab] using
        car_annF_creF_of_ne hval u

/-- **The BRST charge is nilpotent on the concrete fermionic Fock space.**  This
is `BookProof.BRSTNilpotent.brst_charge_nilpotent` with the abstract ghost
algebra replaced by the operators constructed here. -/
theorem brst_charge_nilpotent_fermiFock {n : ℕ} (f : Fin n → Fin n → Fin n → ℝ)
    (hf12 : ∀ a b c, f a b c = -f b a c)
    (hjac : ∀ a b c h : Fin n,
      ∑ e, (f a b e * f e c h + f b c e * f e a h + f c a e * f e b h) = 0) :
    BookProof.BRSTNilpotent.Q f (ghostChi n) (ghostBeta n)
        * BookProof.BRSTNilpotent.Q f (ghostChi n) (ghostBeta n) = 0 :=
  BookProof.BRSTNilpotent.brst_charge_nilpotent f _ _ (ghostCAR_creF_annF n) hf12 hjac

end

end BookProof.FermionFock
