import Mathlib
import BookProof.ChapterFockSecondQuantization
import BookProof.ChapterBRSTNilpotent
import BookProof.ChapterFermionFock.Part1

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
/-! ## The finite-occupation domain of the fermionic Fock space -/

/-- The algebraic fermionic Fock space **is** the finite-occupation subspace of
`ℓ²(FConf)`. -/
def fermiEquiv : FermiAlg ≃ₗ[ℂ] lpFiniteModes FConf := by
  classical
  refine LinearEquiv.ofBijective (toLpFL.codRestrict (lpFiniteModes FConf) toLpF_mem) ⟨?_, ?_⟩
  · intro u v h
    exact toLpF_injective (congrArg Subtype.val h)
  · rintro ⟨x, hx⟩
    refine ⟨Finsupp.onFinset hx.toFinset (fun S => (x : FConf → ℂ) S) ?_, ?_⟩
    · intro S hS
      exact hx.mem_toFinset.mpr hS
    · exact Subtype.ext (lp.ext (funext fun _ => rfl))

@[simp] theorem coe_fermiEquiv (u : FermiAlg) :
    ((fermiEquiv u : lpFiniteModes FConf) : FermiFock) = toLpF u := rfl

theorem coe_fermiEquiv_symm (x : lpFiniteModes FConf) :
    ((x : lpFiniteModes FConf) : FermiFock) = toLpF (fermiEquiv.symm x) := by
  rw [← coe_fermiEquiv, LinearEquiv.apply_symm_apply]

/-! ## Fermionic second quantization -/

/-- The creation operator of a finitely supported one-particle vector
`v = Σ_j v_j e_j`: `c†(v) = Σ_j v_j c_j†`. -/
def creVecF (v : ℕ →₀ ℂ) : FermiAlg →ₗ[ℂ] FermiAlg := ∑ j ∈ v.support, (v j) • creF j

/-- **The fermionic second quantization** `dΓᵃ(A) = Σ_k c†(A e_k) c_k` of the
one-particle operator whose `k`-th column of matrix elements is `col k` (so
`(col k) j = ⟪e_j, A e_k⟫`).  Because a fermionic configuration *is* its set of
occupied modes, the sum on a basis state `|S⟩` runs over `k ∈ S`. -/
def dGammaF (col : ℕ → (ℕ →₀ ℂ)) : FermiAlg →ₗ[ℂ] FermiAlg :=
  Finsupp.lsum ℂ fun S => LinearMap.toSpanSingleton ℂ FermiAlg
    (∑ k ∈ S, creVecF (col k) (annF k (Finsupp.single S 1)))

theorem creVecF_apply (v : ℕ →₀ ℂ) (x : FermiAlg) :
    creVecF v x = ∑ j ∈ v.support, v j • creF j x := by
  simp [creVecF, LinearMap.sum_apply]

@[simp] theorem dGammaF_single (col : ℕ → (ℕ →₀ ℂ)) (S : FConf) (c : ℂ) :
    dGammaF col (Finsupp.single S c)
      = c • ∑ k ∈ S, creVecF (col k) (annF k (Finsupp.single S 1)) := by
  simp [dGammaF, LinearMap.toSpanSingleton]

/-- Enlarging the index set beyond the occupied modes does not change the sum. -/
theorem sum_creVecF_annF_subset (col : ℕ → (ℕ →₀ ℂ)) (u : FermiAlg) {K L : Finset ℕ}
    (hKL : K ⊆ L) (hK : modesF u ⊆ K) :
    ∑ k ∈ K, creVecF (col k) (annF k u) = ∑ k ∈ L, creVecF (col k) (annF k u) :=
  Finset.sum_subset hKL fun k _ hk => by
    rw [annF_eq_zero_of_not_mem_modesF (fun hc => hk (hK hc)), map_zero]

theorem dGammaF_eq_sum_aux (col : ℕ → (ℕ →₀ ℂ)) (u : FermiAlg) :
    ∀ K : Finset ℕ, modesF u ⊆ K → dGammaF col u = ∑ k ∈ K, creVecF (col k) (annF k u) := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => intro K _; simp
  | add f g hf hg =>
    intro K hK
    have hL1 : modesF f ⊆ K ∪ (modesF f ∪ modesF g) := fun x hx =>
      Finset.mem_union_right _ (Finset.mem_union_left _ hx)
    have hL2 : modesF g ⊆ K ∪ (modesF f ∪ modesF g) := fun x hx =>
      Finset.mem_union_right _ (Finset.mem_union_right _ hx)
    have hKL : K ⊆ K ∪ (modesF f ∪ modesF g) := Finset.subset_union_left
    rw [map_add, hf _ hL1, hg _ hL2, ← Finset.sum_add_distrib,
      sum_creVecF_annF_subset col (f + g) hKL hK]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_add, map_add]
  | single T c =>
    intro K hK
    have hsingle : (Finsupp.single T c : FermiAlg) = c • Finsupp.single T (1 : ℂ) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    by_cases hc : c = 0
    · subst hc; simp
    have hT : T ⊆ K := by
      refine fun i hi => hK ?_
      exact Finset.mem_biUnion.mpr ⟨T, Finsupp.mem_support_iff.mpr (by simpa using hc), hi⟩
    have hzero : ∀ k ∈ K, k ∉ T → creVecF (col k) (annF k (Finsupp.single T c)) = 0 := by
      intro k _ hk
      rw [annF_single, if_neg hk, smul_zero, map_zero]
    rw [← Finset.sum_subset hT hzero, dGammaF_single, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsingle, map_smul, map_smul]

/-- On a state occupying only modes in `K`, the second quantization is the finite
sum `∑_{k ∈ K} c†(A e_k) c_k`. -/
theorem dGammaF_eq_sum (col : ℕ → (ℕ →₀ ℂ)) {u : FermiAlg} {K : Finset ℕ} (hK : modesF u ⊆ K) :
    dGammaF col u = ∑ k ∈ K, creVecF (col k) (annF k u) :=
  dGammaF_eq_sum_aux col u K hK

/-- **On the one-particle sector the fermionic second quantization is the
one-particle operator**: `dΓᵃ(A)|e_k⟩ = Σ_j ⟪e_j, A e_k⟫ |e_j⟩`. -/
theorem dGammaF_one_particle (col : ℕ → (ℕ →₀ ℂ)) (k : ℕ) :
    dGammaF col (Finsupp.single ({k} : FConf) 1)
      = ∑ j ∈ (col k).support, (col k) j • Finsupp.single ({j} : FConf) (1 : ℂ) := by
  classical
  have hsign : ∀ j : ℕ, fsign j (∅ : FConf) = 1 := by
    intro j; simp [fsign]
  have hsk : fsign k ({k} : FConf) = 1 := by
    simp [fsign, Finset.filter_singleton]
  have hann : annF k (Finsupp.single ({k} : FConf) (1 : ℂ))
      = Finsupp.single (∅ : FConf) (1 : ℂ) := by
    rw [annF_single, if_pos (Finset.mem_singleton_self k), one_smul,
      Finset.erase_singleton, hsk]
  rw [dGammaF_single, Finset.sum_singleton, hann, one_smul, creVecF_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [creF_single, if_neg (Finset.notMem_empty j), one_smul, hsign]
  congr 1

/-! ### Symmetry and positivity of the fermionic second quantization -/

@[simp] theorem toLpF_zero : toLpF (0 : FermiAlg) = 0 := map_zero toLpFL

/-- One term of the double-sum expansion, on the left. -/
theorem inner_creVecF_annF (col : ℕ → (ℕ →₀ ℂ)) (u v : FermiAlg) (k : ℕ) {L : Finset ℕ}
    (h : (col k).support ⊆ L) :
    (inner ℂ (toLpF (creVecF (col k) (annF k u))) (toLpF v) : ℂ)
      = ∑ j ∈ L, (starRingEnd ℂ) ((col k) j)
          * inner ℂ (toLpF (annF k u)) (toLpF (annF j v)) := by
  have hexp : toLpF (creVecF (col k) (annF k u))
      = ∑ j ∈ (col k).support, (col k) j • toLpF (creF j (annF k u)) := by
    rw [creVecF_apply, ← toLpFL_apply, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, toLpFL_apply]
  rw [hexp, sum_inner, ← Finset.sum_subset h (fun j _ hj => by
    rw [Finsupp.notMem_support_iff.mp hj, map_zero, zero_mul])]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_creF_left]

/-- One term of the double-sum expansion, on the right. -/
theorem inner_annF_creVecF (col : ℕ → (ℕ →₀ ℂ)) (u v : FermiAlg) (j : ℕ) {L : Finset ℕ}
    (h : (col j).support ⊆ L) :
    (inner ℂ (toLpF u) (toLpF (creVecF (col j) (annF j v))) : ℂ)
      = ∑ k ∈ L, (col j) k * inner ℂ (toLpF (annF k u)) (toLpF (annF j v)) := by
  have hexp : toLpF (creVecF (col j) (annF j v))
      = ∑ k ∈ (col j).support, (col j) k • toLpF (creF k (annF j v)) := by
    rw [creVecF_apply, ← toLpFL_apply, map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_smul, toLpFL_apply]
  rw [hexp, inner_sum, ← Finset.sum_subset h (fun k _ hk => by
    rw [Finsupp.notMem_support_iff.mp hk, zero_mul])]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_smul_right, inner_creF_right]

/-- The double-sum expansion of the second-quantized sesquilinear form. -/
theorem inner_dGammaF_left (col : ℕ → (ℕ →₀ ℂ)) (u v : FermiAlg) {L : Finset ℕ}
    (hu : modesF u ⊆ L)
    (hL : ∀ k ∈ modesF u ∪ modesF v, (col k).support ⊆ L) :
    (inner ℂ (toLpF (dGammaF col u)) (toLpF v) : ℂ)
      = ∑ k ∈ L, ∑ j ∈ L,
        (starRingEnd ℂ) ((col k) j) * inner ℂ (toLpF (annF k u)) (toLpF (annF j v)) := by
  have hsum : toLpF (dGammaF col u) = ∑ k ∈ L, toLpF (creVecF (col k) (annF k u)) := by
    rw [dGammaF_eq_sum col hu, ← toLpFL_apply, map_sum]
    rfl
  rw [hsum, sum_inner]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hku : k ∈ modesF u
  · exact inner_creVecF_annF col u v k (hL k (Finset.mem_union_left _ hku))
  · have h0 : annF k u = 0 := annF_eq_zero_of_not_mem_modesF hku
    rw [h0, map_zero]
    simp

theorem inner_dGammaF_right (col : ℕ → (ℕ →₀ ℂ)) (u v : FermiAlg) {L : Finset ℕ}
    (hv : modesF v ⊆ L)
    (hL : ∀ k ∈ modesF u ∪ modesF v, (col k).support ⊆ L) :
    (inner ℂ (toLpF u) (toLpF (dGammaF col v)) : ℂ)
      = ∑ j ∈ L, ∑ k ∈ L,
        (col j) k * inner ℂ (toLpF (annF k u)) (toLpF (annF j v)) := by
  have hsum : toLpF (dGammaF col v) = ∑ j ∈ L, toLpF (creVecF (col j) (annF j v)) := by
    rw [dGammaF_eq_sum col hv, ← toLpFL_apply, map_sum]
    rfl
  rw [hsum, inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hjv : j ∈ modesF v
  · exact inner_annF_creVecF col u v j (hL j (Finset.mem_union_right _ hjv))
  · have h0 : annF j v = 0 := annF_eq_zero_of_not_mem_modesF hjv
    rw [h0, map_zero]
    simp

/-- A finite set of modes large enough for both states and for the columns of
the one-particle matrix over their modes. -/
def closureModesF (col : ℕ → (ℕ →₀ ℂ)) (u v : FermiAlg) : Finset ℕ :=
  (modesF u ∪ modesF v) ∪ (modesF u ∪ modesF v).biUnion fun k => (col k).support

theorem modesF_left_subset_closure (col : ℕ → (ℕ →₀ ℂ)) (u v : FermiAlg) :
    modesF u ⊆ closureModesF col u v := fun _ hx =>
  Finset.mem_union_left _ (Finset.mem_union_left _ hx)

theorem modesF_right_subset_closure (col : ℕ → (ℕ →₀ ℂ)) (u v : FermiAlg) :
    modesF v ⊆ closureModesF col u v := fun _ hx =>
  Finset.mem_union_left _ (Finset.mem_union_right _ hx)

theorem colF_support_subset_closure (col : ℕ → (ℕ →₀ ℂ)) (u v : FermiAlg) :
    ∀ k ∈ modesF u ∪ modesF v, (col k).support ⊆ closureModesF col u v := by
  intro k hk i hi
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, hk, hi⟩)

/-- **The fermionic second quantization of a Hermitian one-particle matrix is
symmetric.** -/
theorem inner_dGammaF_symm {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col) (u v : FermiAlg) :
    (inner ℂ (toLpF (dGammaF col u)) (toLpF v) : ℂ)
      = inner ℂ (toLpF u) (toLpF (dGammaF col v)) := by
  rw [inner_dGammaF_left col u v (modesF_left_subset_closure col u v)
      (colF_support_subset_closure col u v),
    inner_dGammaF_right col u v (modesF_right_subset_closure col u v)
      (colF_support_subset_closure col u v),
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hherm j k, Complex.conj_conj]

/-- **The fermionic second quantization of a positive one-particle matrix is
positive.** -/
theorem inner_dGammaF_nonneg {col : ℕ → (ℕ →₀ ℂ)} (hpos : IsPosCol col) (u : FermiAlg) :
    0 ≤ (inner ℂ (toLpF u) (toLpF (dGammaF col u)) : ℂ).re := by
  classical
  set L := closureModesF col u u with hLdef
  set S : Finset FConf := L.biUnion fun k => (annF k u).support with hSdef
  rw [inner_dGammaF_right col u u (modesF_right_subset_closure col u u)
    (colF_support_subset_closure col u u)]
  have hinner : ∀ k ∈ L, ∀ j : ℕ,
      (inner ℂ (toLpF (annF k u)) (toLpF (annF j u)) : ℂ)
        = ∑ T ∈ S, (starRingEnd ℂ) ((annF k u) T) * (annF j u) T := by
    intro k hk j
    exact inner_toLpF_of_subset (fun T hT => Finset.mem_biUnion.mpr ⟨k, hk, hT⟩) _
  have hstep : (∑ j ∈ L, ∑ k ∈ L, (col j) k * inner ℂ (toLpF (annF k u)) (toLpF (annF j u)))
      = ∑ T ∈ S, ∑ j ∈ L, ∑ k ∈ L,
          (starRingEnd ℂ) ((annF j u) T) * (col k) j * ((annF k u) T) := by
    have h1 : (∑ j ∈ L, ∑ k ∈ L, (col j) k * inner ℂ (toLpF (annF k u)) (toLpF (annF j u)))
        = ∑ j ∈ L, ∑ k ∈ L, ∑ T ∈ S,
            (col j) k * ((starRingEnd ℂ) ((annF k u) T) * (annF j u) T) := by
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k hk => ?_
      rw [hinner k hk j, Finset.mul_sum]
    rw [h1]
    rw [Finset.sum_comm (s := L) (t := L)]
    rw [show (∑ k ∈ L, ∑ j ∈ L, ∑ T ∈ S,
          (col j) k * ((starRingEnd ℂ) ((annF k u) T) * (annF j u) T))
        = ∑ k ∈ L, ∑ T ∈ S, ∑ j ∈ L,
          (col j) k * ((starRingEnd ℂ) ((annF k u) T) * (annF j u) T) from
      Finset.sum_congr rfl fun k _ => Finset.sum_comm]
    rw [Finset.sum_comm (s := L) (t := S)]
    refine Finset.sum_congr rfl fun T _ => ?_
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hstep, Complex.re_sum]
  refine Finset.sum_nonneg fun T _ => hpos L fun k => (annF k u) T

/-! ### The fermionic second-quantized operator on the finite-occupation domain -/

/-- **The fermionic second-quantized operator** on the finite-occupation domain
of the fermionic Fock space. -/
def dGammaOpF (col : ℕ → (ℕ →₀ ℂ)) : lpFiniteModes FConf →ₗ[ℂ] FermiFock :=
  (lpFiniteModes FConf).subtype.comp (fermiEquiv.conj (dGammaF col))

theorem coe_dGammaOpF (col : ℕ → (ℕ →₀ ℂ)) (x : lpFiniteModes FConf) :
    dGammaOpF col x = toLpF (dGammaF col (fermiEquiv.symm x)) := by
  simp [dGammaOpF, LinearEquiv.conj_apply, coe_fermiEquiv]

theorem dGammaOpF_symmetricOn {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col) :
    SymmetricOn (lpFiniteModes FConf) (dGammaOpF col) := by
  intro x y
  rw [coe_dGammaOpF, coe_dGammaOpF, coe_fermiEquiv_symm x, coe_fermiEquiv_symm y]
  exact inner_dGammaF_symm hherm _ _

theorem dGammaOpF_quadForm_nonneg {col : ℕ → (ℕ →₀ ℂ)} (hpos : IsPosCol col)
    (x : lpFiniteModes FConf) : 0 ≤ quadForm (dGammaOpF col) x := by
  rw [quadForm, coe_dGammaOpF, coe_fermiEquiv_symm x]
  exact inner_dGammaF_nonneg hpos _

/-- The finite-occupation domain is dense in the fermionic Fock space. -/
theorem finiteOccupationF_dense :
    Dense ((lpFiniteModes FConf : Submodule ℂ FermiFock) : Set FermiFock) :=
  lpFiniteModes_dense

/-- **The fermionic second-quantized Hamiltonian has a positive self-adjoint
(Friedrichs) extension.** -/
theorem dGammaF_friedrichs_extension {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col)
    (hpos : IsPosCol col) :
    ∃ (Dom : Submodule ℂ FermiFock) (A : Dom →ₗ[ℂ] FermiFock),
      IsPositiveSelfAdjointExtension (dGammaOpF col) A :=
  friedrichs_extension_exists
    ⟨lpFiniteModes FConf, dGammaOpF col, dGammaOpF_symmetricOn hherm,
      dGammaOpF_quadForm_nonneg hpos⟩
    finiteOccupationF_dense

/-- **Fermionic second quantization of an arbitrary symmetric positive
one-particle operator.** -/
theorem secondQuantizationF_friedrichs {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] (b : HilbertBasis ℕ ℂ F)
    (A : finiteModeDomain b →ₗ[ℂ] finiteModeDomain b)
    (hA : SymmetricOn (finiteModeDomain b) ((finiteModeDomain b).subtype.comp A))
    (hpos : ∀ x, 0 ≤ quadForm ((finiteModeDomain b).subtype.comp A) x) :
    ∃ (Dom : Submodule ℂ FermiFock) (A' : Dom →ₗ[ℂ] FermiFock),
      IsPositiveSelfAdjointExtension (dGammaOpF (opCol b A)) A' :=
  dGammaF_friedrichs_extension (isHermCol_opCol hA) (isPosCol_opCol hpos)

/-! ## The fermion-number parity (the `ℤ₂` grading operator) -/

/-- **The fermion-number parity operator** `(−1)^{N_f}`: it multiplies the
configuration `S` by `(−1)^{|S|}`.  It is the grading operator of the fermionic
Fock space. -/
def parityF : FermiAlg →ₗ[ℂ] FermiAlg :=
  Finsupp.lsum ℂ fun S => LinearMap.toSpanSingleton ℂ FermiAlg
    (Finsupp.single S ((-1 : ℂ) ^ S.card))

@[simp] theorem parityF_apply (u : FermiAlg) (S : FConf) :
    parityF u S = (-1 : ℂ) ^ S.card * u S := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, Finsupp.add_apply, hf, hg, mul_add]
  | single T c =>
    rw [parityF, Finsupp.lsum_single, LinearMap.toSpanSingleton_apply,
      Finsupp.smul_apply, Finsupp.single_apply, Finsupp.single_apply, smul_eq_mul]
    by_cases h : T = S
    · subst h; rw [if_pos rfl, if_pos rfl]; ring
    · rw [if_neg h, if_neg h, mul_zero, mul_zero]

/-- The parity operator is an involution. -/
theorem parityF_involutive (u : FermiAlg) : parityF (parityF u) = u := by
  refine Finsupp.ext fun S => ?_
  rw [parityF_apply, parityF_apply, ← mul_assoc, ← pow_add, ← two_mul, pow_mul]
  norm_num

/-- **Creation is odd**: it anticommutes with the parity operator. -/
theorem parityF_creF (j : ℕ) (u : FermiAlg) :
    parityF (creF j u) = - creF j (parityF u) := by
  classical
  refine Finsupp.ext fun S => ?_
  rw [parityF_apply, creF_apply, Finsupp.neg_apply, creF_apply]
  by_cases hj : j ∈ S
  · rw [if_pos hj, if_pos hj, parityF_apply]
    have hcard : S.card = (S.erase j).card + 1 := by
      rw [Finset.card_erase_of_mem hj]
      have := Finset.card_pos.mpr ⟨j, hj⟩
      omega
    rw [hcard, pow_succ]
    ring
  · rw [if_neg hj, if_neg hj, mul_zero, neg_zero]

/-- **Annihilation is odd**: it anticommutes with the parity operator. -/
theorem parityF_annF (j : ℕ) (u : FermiAlg) :
    parityF (annF j u) = - annF j (parityF u) := by
  classical
  refine Finsupp.ext fun S => ?_
  rw [parityF_apply, annF_apply, Finsupp.neg_apply, annF_apply]
  by_cases hj : j ∈ S
  · rw [if_pos hj, if_pos hj, mul_zero, neg_zero]
  · rw [if_neg hj, if_neg hj, parityF_apply,
      Finset.card_insert_of_notMem hj, pow_succ]
    ring

end

end BookProof.FermionFock
