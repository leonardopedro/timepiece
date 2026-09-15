import Mathlib
import BookProof.ChapterNavierStokesEsa
import BookProof.ChapterNavierStokesIkebeKato
import BookProof.ChapterFriedrichsExtension
import BookProof.ChapterYangMillsHermite
import BookProof.ChapterFockSecondQuantization.Part1

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
/-! ## Second quantization -/

/-- The creation operator of a finitely supported one-particle vector
`v = Σ_j v_j e_j`: `a†(v) = Σ_j v_j a_j†`. -/
def creVec (v : ℕ →₀ ℂ) : FockAlg →ₗ[ℂ] FockAlg := ∑ j ∈ v.support, (v j) • creA j

/-- **The second quantization** `dΓ(A) = Σ_k a†(A e_k) a_k` of the one-particle
operator whose `k`-th column of matrix elements is `col k` (so
`(col k) j = ⟪e_j, A e_k⟫`). -/
def dGamma (col : ℕ → (ℕ →₀ ℂ)) : FockAlg →ₗ[ℂ] FockAlg :=
  Finsupp.lsum ℂ fun β => LinearMap.toSpanSingleton ℂ FockAlg
    (∑ k ∈ β.support, creVec (col k) (annA k (Finsupp.single β 1)))

/-- On a state exciting only modes in `K`, the second quantization is the finite
sum `Σ_{k ∈ K} a†(A e_k) a_k`. -/
theorem creVec_apply (v : ℕ →₀ ℂ) (x : FockAlg) :
    creVec v x = ∑ j ∈ v.support, v j • creA j x := by
  simp [creVec, LinearMap.sum_apply]

@[simp] theorem dGamma_single (col : ℕ → (ℕ →₀ ℂ)) (β : Conf) (c : ℂ) :
    dGamma col (Finsupp.single β c)
      = c • ∑ k ∈ β.support, creVec (col k) (annA k (Finsupp.single β 1)) := by
  simp [dGamma, LinearMap.toSpanSingleton]

/-- Enlarging the index set beyond the excited modes does not change the sum. -/
theorem sum_creVec_annA_subset (col : ℕ → (ℕ →₀ ℂ)) (u : FockAlg) {K L : Finset ℕ}
    (hKL : K ⊆ L) (hK : modes u ⊆ K) :
    ∑ k ∈ K, creVec (col k) (annA k u) = ∑ k ∈ L, creVec (col k) (annA k u) :=
  Finset.sum_subset hKL fun k _ hk => by
    rw [annA_eq_zero_of_not_mem_modes (fun hc => hk (hK hc)), map_zero]

theorem dGamma_eq_sum_aux (col : ℕ → (ℕ →₀ ℂ)) (u : FockAlg) :
    ∀ K : Finset ℕ, modes u ⊆ K → dGamma col u = ∑ k ∈ K, creVec (col k) (annA k u) := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => intro K _; simp
  | add f g hf hg =>
    intro K hK
    have hL1 : modes f ⊆ K ∪ (modes f ∪ modes g) := fun x hx =>
      Finset.mem_union_right _ (Finset.mem_union_left _ hx)
    have hL2 : modes g ⊆ K ∪ (modes f ∪ modes g) := fun x hx =>
      Finset.mem_union_right _ (Finset.mem_union_right _ hx)
    have hKL : K ⊆ K ∪ (modes f ∪ modes g) := Finset.subset_union_left
    rw [map_add, hf _ hL1, hg _ hL2, ← Finset.sum_add_distrib,
      sum_creVec_annA_subset col (f + g) hKL hK]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_add, map_add]
  | single β c =>
    intro K hK
    have hsingle : (Finsupp.single β c : FockAlg) = c • Finsupp.single β (1 : ℂ) := by
      rw [Finsupp.smul_single, smul_eq_mul, mul_one]
    by_cases hc : c = 0
    · subst hc
      simp
    have hb : β.support ⊆ K := by
      refine fun i hi => hK ?_
      exact Finset.mem_biUnion.mpr ⟨β, Finsupp.mem_support_iff.mpr (by simpa using hc), hi⟩
    have hzero : ∀ k ∈ K, k ∉ β.support →
        creVec (col k) (annA k (Finsupp.single β c)) = 0 := by
      intro k _ hk
      have hβ : β k = 0 := by simpa using hk
      have hz : annA k (Finsupp.single β c) = 0 := by
        rw [annA_single, hβ]
        simp
      rw [hz, map_zero]
    rw [← Finset.sum_subset hb hzero, dGamma_single, Finset.smul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [hsingle, map_smul, map_smul]

/-- On a state exciting only modes in `K`, the second quantization is the finite
sum `∑_{k ∈ K} a†(A e_k) a_k`. -/
theorem dGamma_eq_sum (col : ℕ → (ℕ →₀ ℂ)) {u : FockAlg} {K : Finset ℕ} (hK : modes u ⊆ K) :
    dGamma col u = ∑ k ∈ K, creVec (col k) (annA k u) :=
  dGamma_eq_sum_aux col u K hK

/-- **On the one-particle sector the second quantization is the one-particle
operator**: `dΓ(A)|e_k⟩ = Σ_j ⟪e_j, A e_k⟫ |e_j⟩`. -/
theorem dGamma_one_particle (col : ℕ → (ℕ →₀ ℂ)) (k : ℕ) :
    dGamma col (Finsupp.single (Finsupp.single k 1) 1)
      = ∑ j ∈ (col k).support, (col k) j • Finsupp.single (Finsupp.single j 1) (1 : ℂ) := by
  classical
  have hup : ∀ j : ℕ, up j (0 : Conf) = Finsupp.single j 1 := by
    intro j
    refine Finsupp.ext fun i => ?_
    by_cases h : i = j
    · subst h; simp
    · rw [up_of_ne _ h]
      simp [h]
  have hsupp : (Finsupp.single k 1 : Conf).support = {k} :=
    Finsupp.support_single_ne_zero k one_ne_zero
  have hdn : dn k (Finsupp.single k 1 : Conf) = 0 := by
    refine Finsupp.ext fun i => ?_
    by_cases h : i = k
    · subst h; simp
    · rw [dn_of_ne _ h]
      simp [h]
  rw [dGamma_single, hsupp]
  have hann : annA k (Finsupp.single (Finsupp.single k 1 : Conf) (1 : ℂ))
      = Finsupp.single (0 : Conf) (1 : ℂ) := by
    rw [annA_single, hdn]
    simp
  rw [Finset.sum_singleton, hann, one_smul, creVec_apply]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [creA_single, hup j]
  simp

/-! ### Symmetry and positivity -/

/-- The matrix is **Hermitian**: `⟪e_j, A e_k⟫ = conj ⟪e_k, A e_j⟫`. -/
def IsHermCol (col : ℕ → (ℕ →₀ ℂ)) : Prop :=
  ∀ j k, (col j) k = (starRingEnd ℂ) ((col k) j)

/-- The matrix is **positive semidefinite** on every finite set of modes. -/
def IsPosCol (col : ℕ → (ℕ →₀ ℂ)) : Prop :=
  ∀ (S : Finset ℕ) (c : ℕ → ℂ),
    0 ≤ (∑ j ∈ S, ∑ k ∈ S, (starRingEnd ℂ) (c j) * (col k) j * c k).re

@[simp] theorem toLp_zero : toLp (0 : FockAlg) = 0 := map_zero toLpL

/-- One term of the double-sum expansion, on the left. -/
theorem inner_creVec_annA (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) (k : ℕ) {L : Finset ℕ}
    (h : (col k).support ⊆ L) :
    (inner ℂ (toLp (creVec (col k) (annA k u))) (toLp v) : ℂ)
      = ∑ j ∈ L, (starRingEnd ℂ) ((col k) j)
          * inner ℂ (toLp (annA k u)) (toLp (annA j v)) := by
  have hexp : toLp (creVec (col k) (annA k u))
      = ∑ j ∈ (col k).support, (col k) j • toLp (creA j (annA k u)) := by
    rw [creVec_apply, ← toLpL_apply, map_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [map_smul, toLpL_apply]
  rw [hexp, sum_inner, ← Finset.sum_subset h (fun j _ hj => by
    rw [Finsupp.notMem_support_iff.mp hj, map_zero, zero_mul])]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [inner_smul_left, inner_creA_left]

/-- One term of the double-sum expansion, on the right. -/
theorem inner_annA_creVec (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) (j : ℕ) {L : Finset ℕ}
    (h : (col j).support ⊆ L) :
    (inner ℂ (toLp u) (toLp (creVec (col j) (annA j v))) : ℂ)
      = ∑ k ∈ L, (col j) k * inner ℂ (toLp (annA k u)) (toLp (annA j v)) := by
  have hexp : toLp (creVec (col j) (annA j v))
      = ∑ k ∈ (col j).support, (col j) k • toLp (creA k (annA j v)) := by
    rw [creVec_apply, ← toLpL_apply, map_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [map_smul, toLpL_apply]
  rw [hexp, inner_sum, ← Finset.sum_subset h (fun k _ hk => by
    rw [Finsupp.notMem_support_iff.mp hk, zero_mul])]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [inner_smul_right, inner_creA_right]

/-- The double-sum expansion of the second-quantized sesquilinear form. -/
theorem inner_dGamma_left (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) {L : Finset ℕ}
    (hu : modes u ⊆ L)
    (hL : ∀ k ∈ modes u ∪ modes v, (col k).support ⊆ L) :
    (inner ℂ (toLp (dGamma col u)) (toLp v) : ℂ)
      = ∑ k ∈ L, ∑ j ∈ L,
        (starRingEnd ℂ) ((col k) j) * inner ℂ (toLp (annA k u)) (toLp (annA j v)) := by
  have hsum : toLp (dGamma col u) = ∑ k ∈ L, toLp (creVec (col k) (annA k u)) := by
    rw [dGamma_eq_sum col hu, ← toLpL_apply, map_sum]
    rfl
  rw [hsum, sum_inner]
  refine Finset.sum_congr rfl fun k _ => ?_
  by_cases hku : k ∈ modes u
  · exact inner_creVec_annA col u v k (hL k (Finset.mem_union_left _ hku))
  · have h0 : annA k u = 0 := annA_eq_zero_of_not_mem_modes hku
    rw [h0, map_zero]
    simp

theorem inner_dGamma_right (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) {L : Finset ℕ}
    (hv : modes v ⊆ L)
    (hL : ∀ k ∈ modes u ∪ modes v, (col k).support ⊆ L) :
    (inner ℂ (toLp u) (toLp (dGamma col v)) : ℂ)
      = ∑ j ∈ L, ∑ k ∈ L,
        (col j) k * inner ℂ (toLp (annA k u)) (toLp (annA j v)) := by
  have hsum : toLp (dGamma col v) = ∑ j ∈ L, toLp (creVec (col j) (annA j v)) := by
    rw [dGamma_eq_sum col hv, ← toLpL_apply, map_sum]
    rfl
  rw [hsum, inner_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hjv : j ∈ modes v
  · exact inner_annA_creVec col u v j (hL j (Finset.mem_union_right _ hjv))
  · have h0 : annA j v = 0 := annA_eq_zero_of_not_mem_modes hjv
    rw [h0, map_zero]
    simp

/-- A finite set of modes large enough for both states and for the columns of
the one-particle matrix over their modes. -/
def closureModes (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) : Finset ℕ :=
  (modes u ∪ modes v) ∪ (modes u ∪ modes v).biUnion fun k => (col k).support

theorem modes_left_subset_closure (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) :
    modes u ⊆ closureModes col u v := fun _ hx =>
  Finset.mem_union_left _ (Finset.mem_union_left _ hx)

theorem modes_right_subset_closure (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) :
    modes v ⊆ closureModes col u v := fun _ hx =>
  Finset.mem_union_left _ (Finset.mem_union_right _ hx)

theorem col_support_subset_closure (col : ℕ → (ℕ →₀ ℂ)) (u v : FockAlg) :
    ∀ k ∈ modes u ∪ modes v, (col k).support ⊆ closureModes col u v := by
  intro k hk i hi
  exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨k, hk, hi⟩)

/-- **The second quantization of a Hermitian one-particle matrix is symmetric.** -/
theorem inner_dGamma_symm {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col) (u v : FockAlg) :
    (inner ℂ (toLp (dGamma col u)) (toLp v) : ℂ) = inner ℂ (toLp u) (toLp (dGamma col v)) := by
  rw [inner_dGamma_left col u v (modes_left_subset_closure col u v)
      (col_support_subset_closure col u v),
    inner_dGamma_right col u v (modes_right_subset_closure col u v)
      (col_support_subset_closure col u v),
    Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => ?_
  rw [hherm j k, Complex.conj_conj]

/-- **The second quantization of a positive one-particle matrix is positive.** -/
theorem inner_dGamma_nonneg {col : ℕ → (ℕ →₀ ℂ)} (hpos : IsPosCol col) (u : FockAlg) :
    0 ≤ (inner ℂ (toLp u) (toLp (dGamma col u)) : ℂ).re := by
  classical
  set L := closureModes col u u with hLdef
  set S : Finset Conf := L.biUnion fun k => (annA k u).support with hSdef
  rw [inner_dGamma_right col u u (modes_right_subset_closure col u u)
    (col_support_subset_closure col u u)]
  have hinner : ∀ k ∈ L, ∀ j : ℕ,
      (inner ℂ (toLp (annA k u)) (toLp (annA j u)) : ℂ)
        = ∑ α ∈ S, (starRingEnd ℂ) ((annA k u) α) * (annA j u) α := by
    intro k hk j
    exact inner_toLp_of_subset (fun α hα => Finset.mem_biUnion.mpr ⟨k, hk, hα⟩) _
  have hstep : (∑ j ∈ L, ∑ k ∈ L, (col j) k * inner ℂ (toLp (annA k u)) (toLp (annA j u)))
      = ∑ α ∈ S, ∑ j ∈ L, ∑ k ∈ L,
          (starRingEnd ℂ) ((annA j u) α) * (col k) j * ((annA k u) α) := by
    have h1 : (∑ j ∈ L, ∑ k ∈ L, (col j) k * inner ℂ (toLp (annA k u)) (toLp (annA j u)))
        = ∑ j ∈ L, ∑ k ∈ L, ∑ α ∈ S,
            (col j) k * ((starRingEnd ℂ) ((annA k u) α) * (annA j u) α) := by
      refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k hk => ?_
      rw [hinner k hk j, Finset.mul_sum]
    rw [h1]
    rw [Finset.sum_comm (s := L) (t := L)]
    rw [show (∑ k ∈ L, ∑ j ∈ L, ∑ α ∈ S,
          (col j) k * ((starRingEnd ℂ) ((annA k u) α) * (annA j u) α))
        = ∑ k ∈ L, ∑ α ∈ S, ∑ j ∈ L,
          (col j) k * ((starRingEnd ℂ) ((annA k u) α) * (annA j u) α) from
      Finset.sum_congr rfl fun k _ => Finset.sum_comm]
    rw [Finset.sum_comm (s := L) (t := S)]
    refine Finset.sum_congr rfl fun α _ => ?_
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hstep, Complex.re_sum]
  refine Finset.sum_nonneg fun α _ => hpos L fun k => (annA k u) α

/-! ### The second-quantized operator on the finite-occupation domain -/

/-- **The second-quantized operator** on the finite-occupation domain of the Fock
space. -/
def dGammaOp (col : ℕ → (ℕ →₀ ℂ)) : lpFiniteModes Conf →ₗ[ℂ] Fock :=
  (lpFiniteModes Conf).subtype.comp (fockEquiv.conj (dGamma col))

theorem coe_dGammaOp (col : ℕ → (ℕ →₀ ℂ)) (x : lpFiniteModes Conf) :
    dGammaOp col x = toLp (dGamma col (fockEquiv.symm x)) := by
  simp [dGammaOp, LinearEquiv.conj_apply, coe_fockEquiv]

theorem dGammaOp_symmetricOn {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col) :
    SymmetricOn (lpFiniteModes Conf) (dGammaOp col) := by
  intro x y
  rw [coe_dGammaOp, coe_dGammaOp, coe_fockEquiv_symm x, coe_fockEquiv_symm y]
  exact inner_dGamma_symm hherm _ _

theorem dGammaOp_quadForm_nonneg {col : ℕ → (ℕ →₀ ℂ)} (hpos : IsPosCol col)
    (x : lpFiniteModes Conf) : 0 ≤ quadForm (dGammaOp col) x := by
  rw [quadForm, coe_dGammaOp, coe_fockEquiv_symm x]
  exact inner_dGamma_nonneg hpos _

/-- The finite-occupation domain is dense in the Fock space. -/
theorem finiteOccupation_dense : Dense ((lpFiniteModes Conf : Submodule ℂ Fock) : Set Fock) :=
  lpFiniteModes_dense

/-- **The second-quantized Hamiltonian has a positive self-adjoint (Friedrichs)
extension.** -/
theorem dGamma_friedrichs_extension {col : ℕ → (ℕ →₀ ℂ)} (hherm : IsHermCol col)
    (hpos : IsPosCol col) :
    ∃ (Dom : Submodule ℂ Fock) (A : Dom →ₗ[ℂ] Fock),
      IsPositiveSelfAdjointExtension (dGammaOp col) A :=
  friedrichs_extension_exists
    ⟨lpFiniteModes Conf, dGammaOp col, dGammaOp_symmetricOn hherm,
      dGammaOp_quadForm_nonneg hpos⟩
    finiteOccupation_dense

end

end BookProof.FockSecondQuantization
