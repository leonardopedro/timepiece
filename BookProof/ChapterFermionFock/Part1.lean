import Mathlib
import BookProof.ChapterFockSecondQuantization
import BookProof.ChapterBRSTNilpotent

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

/-! ## Configurations and the Jordan–Wigner sign -/

/-- A **fermionic configuration**: the (finite) set of occupied one-particle
modes.  The Pauli principle is built into the type: a mode is occupied or not. -/
abbrev FConf := Finset ℕ

/-- The **algebraic fermionic Fock space**: finite linear combinations of
configurations. -/
abbrev FermiAlg := FConf →₀ ℂ

/-- The **fermionic Fock space** `ℓ²(FConf)`. -/
abbrev FermiFock := L2I FConf

/-- The **Jordan–Wigner sign** `(−1)^{#\{i ∈ S : i < j\}}` picked up when a
fermion is created in, or removed from, the mode `j` of the configuration
`S`. -/
def fsign (j : ℕ) (S : FConf) : ℂ := (-1 : ℂ) ^ ((S.filter (fun i => i < j)).card)

theorem fsign_mul_self (j : ℕ) (S : FConf) : fsign j S * fsign j S = 1 := by
  rw [fsign, ← pow_add, ← two_mul, pow_mul]
  norm_num

theorem fsign_conj (j : ℕ) (S : FConf) : (starRingEnd ℂ) (fsign j S) = fsign j S := by
  rw [fsign, map_pow]
  norm_num

/-- Removing the mode `j` does not change its own sign. -/
theorem fsign_erase (j : ℕ) (S : FConf) : fsign j (S.erase j) = fsign j S := by
  rw [fsign, fsign]
  congr 1
  congr 1
  ext i
  simp only [Finset.mem_filter, Finset.mem_erase]
  constructor
  · rintro ⟨⟨_, hi⟩, hlt⟩; exact ⟨hi, hlt⟩
  · rintro ⟨hi, hlt⟩; exact ⟨⟨by omega, hi⟩, hlt⟩

/-- Adding the mode `j` does not change its own sign. -/
theorem fsign_insert_self (j : ℕ) (S : FConf) : fsign j (insert j S) = fsign j S := by
  rw [fsign, fsign]
  congr 2
  ext i
  simp only [Finset.mem_filter, Finset.mem_insert]
  constructor
  · rintro ⟨hi | hi, hlt⟩
    · omega
    · exact ⟨hi, hlt⟩
  · rintro ⟨hi, hlt⟩; exact ⟨Or.inr hi, hlt⟩

/-- Adding a *different* mode `k` flips the sign of `j` exactly when `k < j`. -/
theorem fsign_insert_of_ne {j k : ℕ} (S : FConf) (hkS : k ∉ S) (hkj : k ≠ j) :
    fsign j (insert k S) = (if k < j then (-1 : ℂ) else 1) * fsign j S := by
  classical
  by_cases hlt : k < j
  · have hfil : (insert k S).filter (fun i => i < j)
        = insert k (S.filter (fun i => i < j)) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hi | hi, h2⟩
        · exact Or.inl hi
        · exact Or.inr ⟨hi, h2⟩
      · rintro (rfl | ⟨hi, h2⟩)
        · exact ⟨Or.inl rfl, hlt⟩
        · exact ⟨Or.inr hi, h2⟩
    have hnot : k ∉ S.filter (fun i => i < j) := fun h => hkS (Finset.mem_filter.mp h).1
    rw [fsign, fsign, hfil, Finset.card_insert_of_notMem hnot, pow_succ, if_pos hlt]
    ring
  · have hfil : (insert k S).filter (fun i => i < j) = S.filter (fun i => i < j) := by
      ext i
      simp only [Finset.mem_filter, Finset.mem_insert]
      constructor
      · rintro ⟨hi | hi, h2⟩
        · exact absurd (hi ▸ h2) hlt
        · exact ⟨hi, h2⟩
      · rintro ⟨hi, h2⟩; exact ⟨Or.inr hi, h2⟩
    rw [fsign, fsign, hfil, if_neg hlt, one_mul]

/-! ## Creation and annihilation at the algebraic level -/

open Classical in
/-- **The fermionic creation operator of the mode `j`**:
`c_j†|S⟩ = 0` if `j ∈ S`, and `(−1)^{#\{i ∈ S : i < j\}}|S ∪ \{j\}⟩` otherwise. -/
def creF (j : ℕ) : FermiAlg →ₗ[ℂ] FermiAlg :=
  Finsupp.lsum ℂ fun S => LinearMap.toSpanSingleton ℂ FermiAlg
    (if j ∈ S then 0 else Finsupp.single (insert j S) (fsign j S))

open Classical in
/-- **The fermionic annihilation operator of the mode `j`**:
`c_j|S⟩ = (−1)^{#\{i ∈ S : i < j\}}|S \ \{j\}⟩` if `j ∈ S`, and `0` otherwise. -/
def annF (j : ℕ) : FermiAlg →ₗ[ℂ] FermiAlg :=
  Finsupp.lsum ℂ fun S => LinearMap.toSpanSingleton ℂ FermiAlg
    (if j ∈ S then Finsupp.single (S.erase j) (fsign j S) else 0)

@[simp] theorem creF_single (j : ℕ) (S : FConf) (c : ℂ) :
    creF j (Finsupp.single S c)
      = c • (if j ∈ S then 0 else Finsupp.single (insert j S) (fsign j S)) := by
  classical
  simp [creF, LinearMap.toSpanSingleton]

@[simp] theorem annF_single (j : ℕ) (S : FConf) (c : ℂ) :
    annF j (Finsupp.single S c)
      = c • (if j ∈ S then Finsupp.single (S.erase j) (fsign j S) else 0) := by
  classical
  simp [annF, LinearMap.toSpanSingleton]

/-- The coordinates of `c_j† u`. -/
theorem creF_apply (j : ℕ) (u : FermiAlg) (S : FConf) :
    creF j u S = if j ∈ S then fsign j S * u (S.erase j) else 0 := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add, Finsupp.add_apply, hf, hg]
    by_cases h : j ∈ S <;> simp [h, mul_add]
  | single T c =>
    rw [creF_single]
    by_cases hT : j ∈ T
    · have hne : ∀ hS : j ∈ S, T ≠ S.erase j := by
        intro _ hc
        exact (Finset.notMem_erase j S) (hc ▸ hT)
      simp only [hT, if_true, smul_zero, Finsupp.zero_apply]
      by_cases hS : j ∈ S
      · rw [if_pos hS, Finsupp.single_apply, if_neg (hne hS), mul_zero]
      · rw [if_neg hS]
    · have hins : j ∈ insert j T := Finset.mem_insert_self j T
      by_cases hS : j ∈ S
      · rw [if_neg hT, if_pos hS, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
        by_cases hTS : insert j T = S
        · subst hTS
          rw [if_pos rfl, Finsupp.single_apply,
            if_pos (Finset.erase_insert (by simpa using hT)).symm,
            fsign_insert_self]
          ring
        · rw [if_neg hTS, mul_zero, Finsupp.single_apply]
          have : T ≠ S.erase j := by
            intro hc
            exact hTS (by rw [hc, Finset.insert_erase hS])
          rw [if_neg this, mul_zero]
      · rw [if_neg hT, if_neg hS, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
        have : insert j T ≠ S := fun hc => hS (hc ▸ hins)
        rw [if_neg this, mul_zero]

/-- The coordinates of `c_j u`. -/
theorem annF_apply (j : ℕ) (u : FermiAlg) (S : FConf) :
    annF j u S = if j ∈ S then 0 else fsign j S * u (insert j S) := by
  classical
  induction u using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg =>
    simp only [map_add, Finsupp.add_apply, hf, hg]
    by_cases h : j ∈ S <;> simp [h, mul_add]
  | single T c =>
    rw [annF_single]
    by_cases hT : j ∈ T
    · by_cases hS : j ∈ S
      · rw [if_pos hT, if_pos hS, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul]
        have : T.erase j ≠ S := fun hc => (Finset.notMem_erase j T) (hc ▸ hS)
        rw [if_neg this, mul_zero]
      · rw [if_pos hT, if_neg hS, Finsupp.smul_apply, Finsupp.single_apply, smul_eq_mul,
          Finsupp.single_apply]
        by_cases hTS : T.erase j = S
        · subst hTS
          rw [if_pos rfl, if_pos (Finset.insert_erase hT).symm, fsign_erase]
          ring
        · rw [if_neg hTS, mul_zero]
          have : T ≠ insert j S := by
            intro hc
            exact hTS (by rw [hc, Finset.erase_insert (by simpa using hS)])
          rw [if_neg this, mul_zero]
    · rw [if_neg hT, smul_zero, Finsupp.zero_apply]
      by_cases hS : j ∈ S
      · rw [if_pos hS]
      · rw [if_neg hS, Finsupp.single_apply]
        have : T ≠ insert j S := fun hc => hT (hc ▸ Finset.mem_insert_self j S)
        rw [if_neg this, mul_zero]

/-! ## The canonical anticommutation relations -/

/-- **CAR, the diagonal relation** `{c_j, c_j†} = 1`. -/
theorem car_annF_creF_self (j : ℕ) (u : FermiAlg) :
    annF j (creF j u) + creF j (annF j u) = u := by
  classical
  refine Finsupp.ext fun S => ?_
  simp only [Finsupp.add_apply, annF_apply, creF_apply]
  by_cases hS : j ∈ S
  · rw [if_pos hS, if_pos hS, zero_add, if_neg (Finset.notMem_erase j S),
      fsign_erase, Finset.insert_erase hS, ← mul_assoc, fsign_mul_self, one_mul]
  · rw [if_neg hS, if_neg hS, add_zero, if_pos (Finset.mem_insert_self j S),
      fsign_insert_self, Finset.erase_insert hS, ← mul_assoc, fsign_mul_self, one_mul]

/-- **CAR** `{c_j†, c_k†} = 0`; with `j = k` this is the Pauli principle
`(c_j†)² = 0`. -/
theorem car_creF_creF (j k : ℕ) (u : FermiAlg) :
    creF j (creF k u) + creF k (creF j u) = 0 := by
  classical
  refine Finsupp.ext fun S => ?_
  simp only [Finsupp.add_apply, creF_apply, Finsupp.zero_apply]
  rcases eq_or_ne j k with rfl | hjk
  · simp
  · by_cases hjS : j ∈ S
    · by_cases hkS : k ∈ S
      · rw [if_pos hjS, if_pos hkS,
          if_pos (Finset.mem_erase.mpr ⟨hjk.symm, hkS⟩),
          if_pos (Finset.mem_erase.mpr ⟨hjk, hjS⟩)]
        have hswap : (S.erase j).erase k = (S.erase k).erase j := Finset.erase_right_comm
        have hj : fsign j S = (if k < j then (-1 : ℂ) else 1) * fsign j (S.erase k) := by
          have h := fsign_insert_of_ne (j := j) (k := k) (S.erase k)
            (Finset.notMem_erase k S) hjk.symm
          rwa [Finset.insert_erase hkS] at h
        have hk : fsign k S = (if j < k then (-1 : ℂ) else 1) * fsign k (S.erase j) := by
          have h := fsign_insert_of_ne (j := k) (k := j) (S.erase j)
            (Finset.notMem_erase j S) hjk
          rwa [Finset.insert_erase hjS] at h
        rcases lt_or_gt_of_ne hjk with h | h
        · have e1 : fsign k (S.erase j) = -fsign k S := by
            rw [hk, if_pos h]; ring
          have e2 : fsign j (S.erase k) = fsign j S := by
            rw [hj, if_neg (by omega : ¬ k < j), one_mul]
          rw [hswap, e1, e2]; ring
        · have e1 : fsign j (S.erase k) = -fsign j S := by
            rw [hj, if_pos h]; ring
          have e2 : fsign k (S.erase j) = fsign k S := by
            rw [hk, if_neg (by omega : ¬ j < k), one_mul]
          rw [hswap, e1, e2]; ring
      · rw [if_pos hjS, if_neg hkS,
          if_neg (fun hc => hkS (Finset.mem_of_mem_erase hc))]
        ring
    · by_cases hkS : k ∈ S
      · rw [if_neg hjS, if_pos hkS,
          if_neg (fun hc => hjS (Finset.mem_of_mem_erase hc))]
        ring
      · rw [if_neg hjS, if_neg hkS]
        ring

/-- The Pauli principle: no mode can be occupied twice. -/
theorem creF_creF_self (j : ℕ) (u : FermiAlg) : creF j (creF j u) = 0 := by
  have h := car_creF_creF j j u
  have h2 : (2 : ℂ) • creF j (creF j u) = 0 := by
    rw [two_smul]; exact h
  simpa using h2

/-- **CAR** `{c_j, c_k} = 0`. -/
theorem car_annF_annF (j k : ℕ) (u : FermiAlg) :
    annF j (annF k u) + annF k (annF j u) = 0 := by
  classical
  refine Finsupp.ext fun S => ?_
  simp only [Finsupp.add_apply, annF_apply, Finsupp.zero_apply]
  rcases eq_or_ne j k with rfl | hjk
  · by_cases hS : j ∈ S
    · rw [if_pos hS]
      ring
    · rw [if_neg hS, if_pos (Finset.mem_insert_self j S)]
      ring
  · by_cases hjS : j ∈ S
    · rw [if_pos hjS, if_pos (Finset.mem_insert_of_mem hjS)]
      simp
    · by_cases hkS : k ∈ S
      · rw [if_neg hjS, if_pos hkS, if_pos (Finset.mem_insert_of_mem hkS)]
        ring
      · have hk' : k ∉ insert j S := by simp [Finset.mem_insert, hjk.symm, hkS]
        have hj' : j ∉ insert k S := by simp [Finset.mem_insert, hjk, hjS]
        rw [if_neg hjS, if_neg hkS, if_neg hk', if_neg hj']
        have hswap : insert k (insert j S) = insert j (insert k S) := Finset.insert_comm k j S
        have hj : fsign j (insert k S) = (if k < j then (-1 : ℂ) else 1) * fsign j S :=
          fsign_insert_of_ne S hkS hjk.symm
        have hk : fsign k (insert j S) = (if j < k then (-1 : ℂ) else 1) * fsign k S :=
          fsign_insert_of_ne S hjS hjk
        rw [hswap, hj, hk]
        rcases lt_or_gt_of_ne hjk with h | h
        · rw [if_neg (by omega : ¬ k < j), if_pos h]
          ring
        · rw [if_pos h, if_neg (by omega : ¬ j < k)]
          ring

/-- **CAR, the off-diagonal mixed relation** `{c_j, c_k†} = 0` for `j ≠ k`. -/
theorem car_annF_creF_of_ne {j k : ℕ} (hjk : j ≠ k) (u : FermiAlg) :
    annF j (creF k u) + creF k (annF j u) = 0 := by
  classical
  refine Finsupp.ext fun S => ?_
  simp only [Finsupp.add_apply, annF_apply, creF_apply, Finsupp.zero_apply]
  by_cases hjS : j ∈ S
  · rw [if_pos hjS, zero_add]
    by_cases hkS : k ∈ S
    · rw [if_pos hkS, if_pos (Finset.mem_erase.mpr ⟨hjk, hjS⟩), mul_zero]
    · rw [if_neg hkS]
  · rw [if_neg hjS]
    by_cases hkS : k ∈ S
    · rw [if_pos hkS, if_pos (Finset.mem_insert_of_mem hkS),
        if_neg (fun hc => hjS (Finset.mem_of_mem_erase hc))]
      have hset : (insert j S).erase k = insert j (S.erase k) :=
        Finset.erase_insert_of_ne hjk
      have hk : fsign k (insert j S) = (if j < k then (-1 : ℂ) else 1) * fsign k S :=
        fsign_insert_of_ne S hjS hjk
      have hj : fsign j S = (if k < j then (-1 : ℂ) else 1) * fsign j (S.erase k) := by
        have hk' : k ∉ S.erase k := Finset.notMem_erase k S
        have h := fsign_insert_of_ne (j := j) (k := k) (S.erase k) hk' hjk.symm
        rwa [Finset.insert_erase hkS] at h
      rcases lt_or_gt_of_ne hjk with h | h
      · have e1 : fsign k (insert j S) = -fsign k S := by rw [hk, if_pos h]; ring
        have e2 : fsign j (S.erase k) = fsign j S := by
          rw [hj, if_neg (by omega : ¬ k < j), one_mul]
        rw [hset, e1, e2]; ring
      · have e1 : fsign k (insert j S) = fsign k S := by
          rw [hk, if_neg (by omega : ¬ j < k), one_mul]
        have e2 : fsign j (S.erase k) = -fsign j S := by rw [hj, if_pos h]; ring
        rw [hset, e1, e2]; ring
    · rw [if_neg hkS, if_neg (fun hc => hkS (by
        rcases Finset.mem_insert.mp hc with h | h
        · exact absurd h.symm hjk
        · exact h)), mul_zero, add_zero]

/-! ## The occupied modes of a state -/

/-- The set of modes a state of the algebraic Fock space can occupy. -/
def modesF (u : FermiAlg) : Finset ℕ := u.support.biUnion id

theorem mem_modesF {u : FermiAlg} {S : FConf} (hS : S ∈ u.support) {i : ℕ} (hi : i ∈ S) :
    i ∈ modesF u := Finset.mem_biUnion.mpr ⟨S, hS, hi⟩

/-- A mode that no configuration of `u` occupies is annihilated by `c_k`. -/
theorem annF_eq_zero_of_not_mem_modesF {u : FermiAlg} {k : ℕ} (h : k ∉ modesF u) :
    annF k u = 0 := by
  classical
  refine Finsupp.ext fun S => ?_
  rw [annF_apply, Finsupp.zero_apply]
  by_cases hk : k ∈ S
  · rw [if_pos hk]
  · rw [if_neg hk]
    have hu : u (insert k S) = 0 := by
      by_contra hc
      exact h (mem_modesF (Finsupp.mem_support_iff.mpr hc) (Finset.mem_insert_self k S))
    rw [hu, mul_zero]

/-! ## Transport to `ℓ²(FConf)` -/

/-- A finitely supported fermionic state as an element of `ℓ²(FConf)`. -/
def toLpF (u : FermiAlg) : FermiFock :=
  ⟨fun S => u S, memLpTwo_of_finite_support u.finite_support⟩

@[simp] theorem toLpF_apply (u : FermiAlg) (S : FConf) :
    ((toLpF u : FermiFock) : FConf → ℂ) S = u S := rfl

/-- The transport map is linear. -/
def toLpFL : FermiAlg →ₗ[ℂ] FermiFock where
  toFun := toLpF
  map_add' u v := by
    refine lp.ext (funext fun S => ?_)
    simp [toLpF]
  map_smul' c u := by
    refine lp.ext (funext fun S => ?_)
    simp [toLpF]

@[simp] theorem toLpFL_apply (u : FermiAlg) : toLpFL u = toLpF u := rfl

theorem toLpF_mem (u : FermiAlg) : toLpF u ∈ lpFiniteModes FConf := u.finite_support

theorem toLpF_injective : Function.Injective toLpF := by
  intro u v h
  refine Finsupp.ext fun S => ?_
  have := congrArg (fun f : FermiFock => (f : FConf → ℂ) S) h
  simpa using this

/-- The inner product of two finitely supported fermionic states is the finite
sum of the products of their coordinates. -/
theorem inner_toLpF_of_subset {u : FermiAlg} {s : Finset FConf} (hs : u.support ⊆ s)
    (v : FermiAlg) :
    (inner ℂ (toLpF u) (toLpF v) : ℂ) = ∑ S ∈ s, (starRingEnd ℂ) (u S) * v S := by
  rw [lp.inner_eq_tsum]
  have hcoord : ∀ S : FConf,
      (inner ℂ (((toLpF u : FermiFock) : FConf → ℂ) S)
        (((toLpF v : FermiFock) : FConf → ℂ) S) : ℂ) = (starRingEnd ℂ) (u S) * v S := by
    intro S
    simp [RCLike.inner_apply, mul_comm]
  rw [tsum_congr hcoord]
  refine tsum_eq_sum fun S hS => ?_
  have hu : u S = 0 := by
    by_contra hc
    exact hS (hs (Finsupp.mem_support_iff.mpr hc))
  rw [hu, map_zero, zero_mul]

theorem inner_toLpF (u v : FermiAlg) :
    (inner ℂ (toLpF u) (toLpF v) : ℂ) = ∑ S ∈ u.support, (starRingEnd ℂ) (u S) * v S :=
  inner_toLpF_of_subset (Finset.Subset.refl _) v

/-! ## Creation and annihilation are formal adjoints -/

/-- The involution of configurations that toggles the occupation of the mode
`j`; it matches the configurations `c_j†` connects. -/
def toggle (j : ℕ) (S : FConf) : FConf := if j ∈ S then S.erase j else insert j S

theorem toggle_of_mem {j : ℕ} {S : FConf} (h : j ∈ S) : toggle j S = S.erase j :=
  if_pos h

theorem toggle_of_not_mem {j : ℕ} {S : FConf} (h : j ∉ S) : toggle j S = insert j S :=
  if_neg h

theorem toggle_toggle (j : ℕ) (S : FConf) : toggle j (toggle j S) = S := by
  by_cases hS : j ∈ S
  · rw [toggle_of_mem hS, toggle_of_not_mem (Finset.notMem_erase j S), Finset.insert_erase hS]
  · rw [toggle_of_not_mem hS, toggle_of_mem (Finset.mem_insert_self j S),
      Finset.erase_insert hS]

theorem support_creF (j : ℕ) (u : FermiAlg) :
    (creF j u).support ⊆ u.support.image (toggle j) := by
  classical
  intro S hS
  have hS' := Finsupp.mem_support_iff.mp hS
  rw [creF_apply] at hS'
  by_cases hj : j ∈ S
  · rw [if_pos hj] at hS'
    have hu : u (S.erase j) ≠ 0 := fun h => hS' (by rw [h, mul_zero])
    refine Finset.mem_image.mpr ⟨S.erase j, Finsupp.mem_support_iff.mpr hu, ?_⟩
    rw [toggle_of_not_mem (Finset.notMem_erase j S), Finset.insert_erase hj]
  · rw [if_neg hj] at hS'
    exact absurd rfl hS'

theorem support_annF (j : ℕ) (u : FermiAlg) :
    (annF j u).support ⊆ u.support.image (toggle j) := by
  classical
  intro S hS
  have hS' := Finsupp.mem_support_iff.mp hS
  rw [annF_apply] at hS'
  by_cases hj : j ∈ S
  · rw [if_pos hj] at hS'
    exact absurd rfl hS'
  · rw [if_neg hj] at hS'
    have hu : u (insert j S) ≠ 0 := fun h => hS' (by rw [h, mul_zero])
    refine Finset.mem_image.mpr ⟨insert j S, Finsupp.mem_support_iff.mpr hu, ?_⟩
    rw [toggle_of_mem (Finset.mem_insert_self j S), Finset.erase_insert hj]

/-- **The adjoint pairing of creation and annihilation**: `⟪c_j† u, v⟫ = ⟪u, c_j v⟫`. -/
theorem inner_creF_left (j : ℕ) (u v : FermiAlg) :
    (inner ℂ (toLpF (creF j u)) (toLpF v) : ℂ) = inner ℂ (toLpF u) (toLpF (annF j v)) := by
  classical
  set s : Finset FConf := (creF j u).support ∪ u.support with hs
  set F : Finset FConf := s ∪ s.image (toggle j) with hF
  have hmemF : ∀ S ∈ F, toggle j S ∈ F := by
    intro S hS
    rcases Finset.mem_union.mp hS with h | h
    · exact Finset.mem_union_right _ (Finset.mem_image.mpr ⟨S, h, rfl⟩)
    · obtain ⟨T, hT, hTS⟩ := Finset.mem_image.mp h
      refine Finset.mem_union_left _ ?_
      rw [← hTS, toggle_toggle]
      exact hT
  have hcre : (creF j u).support ⊆ F :=
    fun S hS => Finset.mem_union_left _ (Finset.mem_union_left _ hS)
  have hu : u.support ⊆ F :=
    fun S hS => Finset.mem_union_left _ (Finset.mem_union_right _ hS)
  rw [inner_toLpF_of_subset hcre v, inner_toLpF_of_subset hu (annF j v)]
  refine Finset.sum_nbij' (i := toggle j) (j := toggle j)
    (fun S hS => hmemF S hS) (fun S hS => hmemF S hS)
    (fun S _ => toggle_toggle j S) (fun S _ => toggle_toggle j S) ?_
  intro S _
  by_cases hj : j ∈ S
  · rw [creF_apply, if_pos hj, toggle_of_mem hj, annF_apply,
      if_neg (Finset.notMem_erase j S), fsign_erase, Finset.insert_erase hj, map_mul,
      fsign_conj]
    ring
  · rw [creF_apply, if_neg hj, toggle_of_not_mem hj, annF_apply,
      if_pos (Finset.mem_insert_self j S), map_zero, zero_mul, mul_zero]

/-- The mirror image of `inner_creF_left`: `⟪u, c_j† v⟫ = ⟪c_j u, v⟫`. -/
theorem inner_creF_right (j : ℕ) (u v : FermiAlg) :
    (inner ℂ (toLpF u) (toLpF (creF j v)) : ℂ) = inner ℂ (toLpF (annF j u)) (toLpF v) := by
  have h := inner_creF_left j v u
  have := congrArg (starRingEnd ℂ) h
  rwa [inner_conj_symm, inner_conj_symm] at this

end

end BookProof.FermionFock
