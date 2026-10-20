/-
Prove2.me import, converted to Lean 4.28.0 (this repository's Mathlib pin).

* platform theorem id : 0b16e865-79df-4e0e-ab2a-9eb3b5fe184f
* original name       : `Clifford6Casimir.spectrum`
* title               : Odd-sector Casimir spectrum: eigenvalue 2 (×24) and 0 (×8)
* statement author    : lisamegawatts
* solution author     : Nickrobbins95 (submission 43a4ee55-8539-4857-801f-4dba63037847,
                        accepted 2026-09-24T12:28:19.322966+00:00)
* source              : MonumentalSystems/LeanProofs research memory #2561 (2026-09-12): exact full-sector SU(2) decomposition on Cl⁻(6,0); frozen internal targets Rosetta/Cl60OddSectorCasimirSpectrumV1Targets.lean and program research/cl60-casimir-spectrum-v1/program.json, https://github.com/MonumentalSystems/LeanProofs
* platform Mathlib rev: 0df444a360eaa60ab8c11dca51a86af692955474
* original file       : Downloads/qft-wick/Clifford6Casimir.spectrum.lean

Public prove2.me contributions are licensed under Apache 2.0
(https://prove2.me/terms); this file keeps that license. The conversion diff
against the original download is `converted/diffs/Clifford6Casimir_spectrum.diff`.
-/
import Mathlib
import Definitions.Def_clifford6_casimir_data

/-! 0b16e865 Clifford6Casimir.spectrum (odd-sector Casimir spectrum on Cl(6,0)).
Route (direct, blade-based; no tensor-product plumbing):
* `P L` = product of generators along a list; `e6 a * P L = (-1)^(#{l ∈ L, l ≠ a}) • (P L * e6 a)`.
* Hence each `E_k = e p e q` commutes or anticommutes with every blade, so
  `T_k (T_k (P L))` is `0` or `-(P L)` and `C (P L) = cnt L • P L`, with `cnt L` = number of `E_k`
  anticommuting with the blade (decided: 2 or 0 on odd blades; 24 blades with 2, 8 with 0).
* Linear independence of the 64 blades: they are eigenvectors of `F = Σ_j 2^j (x ↦ e_j x e_j)`
  with pairwise distinct (decided) integer eigenvalues, and are nonzero (`P L * P L.reverse = 1`).
* `finrank Cl(6,0) = 64` via `CliffordAlgebra.equivExterior` and the `ExteriorAlgebra` basis;
  `evenOdd_isCompl` plus 32 independent even blades gives `finrank oddSector ≤ 32`.
* The 32 odd blades then span the odd sector, forcing `A ⊔ B = odd`, and `A ⊓ B = ⊥` plus the
  lower bounds 24 and 8 pin the two finranks. -/

set_option autoImplicit false

namespace Cl6Build
open Clifford6

theorem Q60_single (i : Fin 6) : Q60 (Pi.single i 1) = 1 := by
  simp [Q60, QuadraticMap.weightedSumSquares_apply, Pi.single_apply]

theorem e_sq (i : Fin 6) : e6 i * e6 i = 1 := by
  rw [e6, CliffordAlgebra.ι_sq_scalar, Q60_single, map_one]

theorem isOrtho_single {i j : Fin 6} (h : i ≠ j) :
    Q60.IsOrtho (Pi.single i 1) (Pi.single j 1) := by
  rw [QuadraticMap.isOrtho_def]
  simp only [Q60, QuadraticMap.weightedSumSquares_apply, Pi.add_apply, Pi.single_apply, one_smul]
  rw [Fin.sum_univ_six, Fin.sum_univ_six, Fin.sum_univ_six]
  fin_cases i <;> fin_cases j <;> simp_all

theorem e_anti {i j : Fin 6} (h : i ≠ j) : e6 i * e6 j = -(e6 j * e6 i) :=
  CliffordAlgebra.ι_mul_ι_comm_of_isOrtho (isOrtho_single h)

/-- product of generators along a list -/
noncomputable def P (L : List (Fin 6)) : CliffordAlgebra Q60 := (L.map e6).prod

theorem P_nil : P [] = 1 := rfl
theorem P_cons (a : Fin 6) (L : List (Fin 6)) : P (a :: L) = e6 a * P L := by
  simp [P]

/-- number of entries of `L` different from `a` -/
def nc (a : Fin 6) (L : List (Fin 6)) : ℕ := L.countP (fun i => i ≠ a)

theorem e_mul_P (a : Fin 6) (L : List (Fin 6)) :
    e6 a * P L = (-1 : ℝ) ^ (nc a L) • (P L * e6 a) := by
  unfold nc
  induction L with
  | nil => simp [P_nil]
  | cons b L ih =>
    rw [P_cons, List.countP_cons]
    by_cases hb : b = a
    · subst hb
      rw [if_neg (by simp), add_zero]
      conv_lhs => rw [ih]
      rw [mul_smul_comm, mul_assoc (e6 b) (P L) (e6 b)]
    · have hb' : a ≠ b := fun h => hb h.symm
      rw [if_pos (by simpa using hb), pow_succ, mul_neg_one, neg_smul,
        ← mul_assoc (e6 a) (e6 b) (P L), e_anti hb', neg_mul, mul_assoc (e6 b) (e6 a) (P L)]
      conv_lhs => rw [ih]
      rw [mul_smul_comm, mul_assoc (e6 b) (P L) (e6 a)]


theorem P_append_single (L : List (Fin 6)) (a : Fin 6) : P (L ++ [a]) = P L * e6 a := by
  simp [P, List.prod_append]

theorem P_mul_P_reverse (L : List (Fin 6)) : P L * P L.reverse = 1 := by
  induction L with
  | nil => simp [P_nil]
  | cons a L ih =>
    rw [List.reverse_cons, P_append_single, P_cons, mul_assoc, ← mul_assoc (P L), ih, one_mul,
      e_sq]

noncomputable instance inv2 : Invertible (2 : ℝ) := invertibleOfNonzero two_ne_zero

theorem P_ne_zero (L : List (Fin 6)) : P L ≠ 0 := by
  intro h
  have h1 := P_mul_P_reverse L
  rw [h, zero_mul] at h1
  exact zero_ne_one h1

theorem P_mem_evenOdd (L : List (Fin 6)) :
    P L ∈ CliffordAlgebra.evenOdd Q60 (L.length : ZMod 2) := by
  induction L with
  | nil => simpa [P_nil] using SetLike.one_mem_graded (CliffordAlgebra.evenOdd Q60)
  | cons a L ih =>
    rw [P_cons, List.length_cons, Nat.cast_succ, add_comm]
    exact SetLike.mul_mem_graded (CliffordAlgebra.ι_mem_evenOdd_one Q60 _) ih

theorem EP (p q : Fin 6) (L : List (Fin 6)) :
    e6 p * e6 q * P L = (-1 : ℝ) ^ (nc p L + nc q L) • (P L * (e6 p * e6 q)) := by
  rw [mul_assoc, e_mul_P q, mul_smul_comm, ← mul_assoc (e6 p) (P L) (e6 q), e_mul_P p,
    smul_mul_assoc, smul_smul, ← pow_add, Nat.add_comm (nc q L), mul_assoc]

theorem EE (p q : Fin 6) (h : p ≠ q) : e6 p * e6 q * (e6 p * e6 q) = -1 := by
  rw [mul_assoc, ← mul_assoc (e6 q), e_anti (Ne.symm h), neg_mul, mul_assoc, e_sq, mul_one,
    mul_neg, e_sq]

theorem tt_comm (E y : CliffordAlgebra Q60)
    (T : CliffordAlgebra Q60 →ₗ[ℝ] CliffordAlgebra Q60)
    (hT : ∀ x, T x = (1/2:ℝ) • (E * x - x * E)) (hc : E * y = y * E) : T (T y) = 0 := by
  rw [hT y, hc, sub_self, smul_zero, map_zero]

theorem tt_anti (E y : CliffordAlgebra Q60) (hEE : E * E = -1)
    (T : CliffordAlgebra Q60 →ₗ[ℝ] CliffordAlgebra Q60)
    (hT : ∀ x, T x = (1/2:ℝ) • (E * x - x * E)) (ha : E * y = -(y * E)) : T (T y) = -y := by
  have h1 : T y = -(y * E) := by
    rw [hT, ha]
    module
  rw [h1, map_neg, hT, ← mul_assoc E y E, ha, neg_mul, mul_assoc y E E, hEE, mul_neg_one]
  module

/-- 1 if `e p e q` anticommutes with `P L`, else 0 -/
def ac (p q : Fin 6) (L : List (Fin 6)) : ℕ := if (nc p L + nc q L) % 2 = 0 then 0 else 1

theorem TT_P (p q : Fin 6) (hpq : p ≠ q) (E : CliffordAlgebra Q60) (hE : E = e6 p * e6 q)
    (T : CliffordAlgebra Q60 →ₗ[ℝ] CliffordAlgebra Q60)
    (hT : ∀ x, T x = (1/2:ℝ) • (E * x - x * E)) (L : List (Fin 6)) :
    T (T (P L)) = -((ac p q L : ℕ) : ℝ) • P L := by
  subst hE
  have key := EP p q L
  unfold ac
  split_ifs with h
  · rw [Nat.cast_zero, neg_zero, zero_smul]
    apply tt_comm _ _ T hT
    rw [key, (Nat.even_iff.mpr h).neg_one_pow, one_smul]
  · rw [Nat.cast_one, neg_smul, one_smul]
    apply tt_anti _ _ (EE p q hpq) T hT
    rw [key, (Nat.odd_iff.mpr (by omega)).neg_one_pow, neg_one_smul]

def cnt (L : List (Fin 6)) : ℕ := ac 0 2 L + ac 2 5 L + ac 0 5 L

theorem C_P (T1 T2 T3 C : CliffordAlgebra Q60 →ₗ[ℝ] CliffordAlgebra Q60)
    (h1 : ∀ x, T1 x = (1/2:ℝ) • (E1 * x - x * E1))
    (h2 : ∀ x, T2 x = (1/2:ℝ) • (E2 * x - x * E2))
    (h3 : ∀ x, T3 x = (1/2:ℝ) • (E3 * x - x * E3))
    (hC : ∀ x, C x = -(T1 (T1 x) + T2 (T2 x) + T3 (T3 x))) (L : List (Fin 6)) :
    C (P L) = ((cnt L : ℕ) : ℝ) • P L := by
  rw [hC, TT_P 0 2 (by decide) E1 rfl T1 h1, TT_P 2 5 (by decide) E2 rfl T2 h2,
    TT_P 0 5 (by decide) E3 rfl T3 h3]
  unfold cnt
  push_cast
  module

def sg (j : Fin 6) (L : List (Fin 6)) : ℤ := if nc j L % 2 = 0 then 1 else -1

noncomputable def sig (j : Fin 6) : CliffordAlgebra Q60 →ₗ[ℝ] CliffordAlgebra Q60 :=
  (LinearMap.mulLeft ℝ (e6 j)) ∘ₗ (LinearMap.mulRight ℝ (e6 j))

theorem sig_P (j : Fin 6) (L : List (Fin 6)) : sig j (P L) = ((sg j L : ℤ) : ℝ) • P L := by
  simp only [sig, LinearMap.comp_apply, LinearMap.mulLeft_apply, LinearMap.mulRight_apply]
  rw [← mul_assoc, e_mul_P, smul_mul_assoc, mul_assoc, e_sq, mul_one]
  congr 1
  unfold sg
  split_ifs with h
  · rw [(Nat.even_iff.mpr h).neg_one_pow]; simp
  · rw [(Nat.odd_iff.mpr (by omega)).neg_one_pow]; simp

noncomputable def F : CliffordAlgebra Q60 →ₗ[ℝ] CliffordAlgebra Q60 :=
  sig 0 + (2:ℝ) • sig 1 + (4:ℝ) • sig 2 + (8:ℝ) • sig 3 + (16:ℝ) • sig 4 + (32:ℝ) • sig 5

def muZ (L : List (Fin 6)) : ℤ :=
  sg 0 L + 2 * sg 1 L + 4 * sg 2 L + 8 * sg 3 L + 16 * sg 4 L + 32 * sg 5 L

theorem F_P (L : List (Fin 6)) : F (P L) = ((muZ L : ℤ) : ℝ) • P L := by
  simp only [F, LinearMap.add_apply, LinearMap.smul_apply, sig_P, muZ]
  push_cast
  module

def bits (n : Fin 64) : List (Fin 6) := (List.finRange 6).filter (fun i => n.val.testBit i.val)

noncomputable def blade (n : Fin 64) : CliffordAlgebra Q60 := P (bits n)

theorem muZ_inj : ∀ a b : Fin 64, muZ (bits a) = muZ (bits b) → a = b := by decide +kernel

theorem blade_li : LinearIndependent ℝ blade :=
  Module.End.eigenvectors_linearIndependent' F (fun n => ((muZ (bits n) : ℤ) : ℝ))
    (fun a b h => muZ_inj a b (Int.cast_injective h)) blade
    (fun _ => Module.End.hasEigenvector_iff.mpr
      ⟨Module.End.mem_eigenspace_iff.mpr (F_P _), P_ne_zero _⟩)

theorem card_O : Fintype.card {n : Fin 64 // (bits n).length % 2 = 1} = 32 := by decide +kernel
theorem card_E : Fintype.card {n : Fin 64 // (bits n).length % 2 = 0} = 32 := by decide +kernel
theorem card_A :
    Fintype.card {n : Fin 64 // (bits n).length % 2 = 1 ∧ cnt (bits n) = 2} = 24 := by
  decide +kernel
theorem card_B :
    Fintype.card {n : Fin 64 // (bits n).length % 2 = 1 ∧ cnt (bits n) = 0} = 8 := by
  decide +kernel
theorem odd_cases : ∀ n : Fin 64, (bits n).length % 2 = 1 →
    cnt (bits n) = 2 ∨ cnt (bits n) = 0 := by decide +kernel


noncomputable instance fdExt : FiniteDimensional ℝ (ExteriorAlgebra ℝ (Fin 6 → ℝ)) :=
  Module.Finite.of_basis (Pi.basisFun ℝ (Fin 6)).ExteriorAlgebra

noncomputable instance fdCl : FiniteDimensional ℝ (CliffordAlgebra Q60) :=
  LinearEquiv.finiteDimensional (CliffordAlgebra.equivExterior Q60).symm

theorem finrank_cl : Module.finrank ℝ (CliffordAlgebra Q60) = 64 := by
  rw [LinearEquiv.finrank_eq (CliffordAlgebra.equivExterior Q60),
    Module.finrank_eq_card_basis (Pi.basisFun ℝ (Fin 6)).ExteriorAlgebra, Fintype.card_finset,
    Fintype.card_fin]
  norm_num

theorem card_le_finrank_of_mem {ι : Type} [Fintype ι] (v : ι → CliffordAlgebra Q60)
    (hv : LinearIndependent ℝ v) (S : Submodule ℝ (CliffordAlgebra Q60)) (hS : ∀ i, v i ∈ S) :
    Fintype.card ι ≤ Module.finrank ℝ S := by
  rw [← finrank_span_eq_card hv]
  exact Submodule.finrank_mono (Submodule.span_le.mpr (by rintro _ ⟨i, rfl⟩; exact hS i))

theorem blade_mem (n : Fin 64) (k : ZMod 2) (hk : (((bits n).length % 2 : ℕ) : ZMod 2) = k) :
    blade n ∈ CliffordAlgebra.evenOdd Q60 k := by
  have h := P_mem_evenOdd (bits n)
  rw [← ZMod.natCast_mod, hk] at h
  exact h

theorem finrank_odd_le : Module.finrank ℝ (CliffordAlgebra.evenOdd Q60 1) ≤ 32 := by
  have hE : 32 ≤ Module.finrank ℝ (CliffordAlgebra.evenOdd Q60 0) := by
    rw [← card_E]
    exact card_le_finrank_of_mem (fun i : {n : Fin 64 // (bits n).length % 2 = 0} => blade i.1)
      (blade_li.comp _ Subtype.val_injective) _
      (fun i => blade_mem i.1 0 (by rw [i.2]; rfl))
  have h := Submodule.finrank_sup_add_finrank_inf_eq (CliffordAlgebra.evenOdd Q60 0)
    (CliffordAlgebra.evenOdd Q60 1)
  rw [(CliffordAlgebra.evenOdd_isCompl Q60).inf_eq_bot, finrank_bot, add_zero] at h
  have hle := Submodule.finrank_le (CliffordAlgebra.evenOdd Q60 0 ⊔ CliffordAlgebra.evenOdd Q60 1)
  rw [finrank_cl] at hle
  omega

end Cl6Build

set_option maxHeartbeats 4000000 in
open Clifford6 in
theorem _root_.Prove2me.Solution.Clifford6Casimir_spectrum
    (T1 T2 T3 C : CliffordAlgebra Clifford6.Q60 →ₗ[ℝ] CliffordAlgebra Clifford6.Q60)
    (h1 : ∀ x, T1 x = (1/2:ℝ) • (Clifford6.E1 * x - x * Clifford6.E1))
    (h2 : ∀ x, T2 x = (1/2:ℝ) • (Clifford6.E2 * x - x * Clifford6.E2))
    (h3 : ∀ x, T3 x = (1/2:ℝ) • (Clifford6.E3 * x - x * Clifford6.E3))
    (hC : ∀ x, C x = -(T1 (T1 x) + T2 (T2 x) + T3 (T3 x))) :
    (∀ x ∈ Clifford6.oddSector,
      T1 x ∈ Clifford6.oddSector ∧ T2 x ∈ Clifford6.oddSector ∧
        T3 x ∈ Clifford6.oddSector ∧ C x ∈ Clifford6.oddSector)
      ∧ (Clifford6.oddSector ⊓ LinearMap.ker (C - (2:ℝ) • LinearMap.id) ⊔
          Clifford6.oddSector ⊓ LinearMap.ker C = Clifford6.oddSector)
      ∧ (Module.finrank ℝ
          ↥(Clifford6.oddSector ⊓ LinearMap.ker (C - (2:ℝ) • LinearMap.id)) = 24)
      ∧ (Module.finrank ℝ ↥(Clifford6.oddSector ⊓ LinearMap.ker C) = 8) := by
  -- the odd sector is preserved
  have pres : ∀ (E : CliffordAlgebra Q60), E ∈ CliffordAlgebra.evenOdd Q60 0 →
      ∀ (T : CliffordAlgebra Q60 →ₗ[ℝ] CliffordAlgebra Q60),
      (∀ x, T x = (1/2:ℝ) • (E * x - x * E)) → ∀ x ∈ oddSector, T x ∈ oddSector := by
    intro E hE T hT x hx
    rw [hT]
    refine Submodule.smul_mem _ _ (Submodule.sub_mem _ ?_ ?_)
    · have h := SetLike.mul_mem_graded hE hx
      rwa [zero_add] at h
    · have h := SetLike.mul_mem_graded hx hE
      rwa [add_zero] at h
  have hE1 : E1 ∈ CliffordAlgebra.evenOdd Q60 0 := CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero _ _ _
  have hE2 : E2 ∈ CliffordAlgebra.evenOdd Q60 0 := CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero _ _ _
  have hE3 : E3 ∈ CliffordAlgebra.evenOdd Q60 0 := CliffordAlgebra.ι_mul_ι_mem_evenOdd_zero _ _ _
  have p1 := pres E1 hE1 T1 h1
  have p2 := pres E2 hE2 T2 h2
  have p3 := pres E3 hE3 T3 h3
  have pC : ∀ x ∈ oddSector, C x ∈ oddSector := by
    intro x hx
    rw [hC]
    exact Submodule.neg_mem _ (Submodule.add_mem _ (Submodule.add_mem _ (p1 _ (p1 x hx))
      (p2 _ (p2 x hx))) (p3 _ (p3 x hx)))
  -- blades are eigenvectors
  have hO : ∀ n : Fin 64, (Cl6Build.bits n).length % 2 = 1 → Cl6Build.blade n ∈ oddSector :=
    fun n hn => Cl6Build.blade_mem n 1 (by rw [hn]; rfl)
  have memA : ∀ n : Fin 64, (Cl6Build.bits n).length % 2 = 1 → Cl6Build.cnt (Cl6Build.bits n) = 2 →
      Cl6Build.blade n ∈ oddSector ⊓ LinearMap.ker (C - (2:ℝ) • LinearMap.id) := by
    intro n hn hc
    refine Submodule.mem_inf.mpr ⟨hO n hn, ?_⟩
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, Cl6Build.blade,
      Cl6Build.C_P T1 T2 T3 C h1 h2 h3 hC, hc]
    norm_num
  have memB : ∀ n : Fin 64, (Cl6Build.bits n).length % 2 = 1 → Cl6Build.cnt (Cl6Build.bits n) = 0 →
      Cl6Build.blade n ∈ oddSector ⊓ LinearMap.ker C := by
    intro n hn hc
    refine Submodule.mem_inf.mpr ⟨hO n hn, ?_⟩
    rw [LinearMap.mem_ker, Cl6Build.blade, Cl6Build.C_P T1 T2 T3 C h1 h2 h3 hC, hc]
    norm_num
  -- the two eigenspaces meet trivially
  have hinf : (oddSector ⊓ LinearMap.ker (C - (2:ℝ) • LinearMap.id)) ⊓
      (oddSector ⊓ LinearMap.ker C) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨⟨-, hx2⟩, ⟨-, hx0⟩⟩
    rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply,
      LinearMap.id_apply] at hx2
    rw [SetLike.mem_coe, LinearMap.mem_ker] at hx0
    rw [hx0, zero_sub, neg_eq_zero, smul_eq_zero] at hx2
    rcases hx2 with h | h
    · norm_num at h
    · exact (Submodule.mem_bot ℝ).mpr h
  -- the odd blades span the odd sector
  have liO : LinearIndependent ℝ
      (fun i : {n : Fin 64 // (Cl6Build.bits n).length % 2 = 1} => Cl6Build.blade i.1) :=
    Cl6Build.blade_li.comp _ Subtype.val_injective
  have hSO_le : Submodule.span ℝ (Set.range
      (fun i : {n : Fin 64 // (Cl6Build.bits n).length % 2 = 1} => Cl6Build.blade i.1)) ≤
      oddSector ⊓ LinearMap.ker (C - (2:ℝ) • LinearMap.id) ⊔ oddSector ⊓ LinearMap.ker C := by
    rw [Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rcases Cl6Build.odd_cases i.1 i.2 with h | h
    · exact Submodule.mem_sup_left (memA i.1 i.2 h)
    · exact Submodule.mem_sup_right (memB i.1 i.2 h)
  have hsupO : oddSector ⊓ LinearMap.ker (C - (2:ℝ) • LinearMap.id) ⊔
      oddSector ⊓ LinearMap.ker C ≤ oddSector := sup_le inf_le_left inf_le_left
  have finSO := finrank_span_eq_card liO
  rw [Cl6Build.card_O] at finSO
  have hSO_eq : Submodule.span ℝ (Set.range
      (fun i : {n : Fin 64 // (Cl6Build.bits n).length % 2 = 1} => Cl6Build.blade i.1)) = oddSector := by
    apply Submodule.eq_of_le_of_finrank_eq (hSO_le.trans hsupO)
    have := Cl6Build.finrank_odd_le
    have := Submodule.finrank_mono (hSO_le.trans hsupO)
    unfold oddSector at *
    omega
  have hsup : oddSector ⊓ LinearMap.ker (C - (2:ℝ) • LinearMap.id) ⊔
      oddSector ⊓ LinearMap.ker C = oddSector :=
    le_antisymm hsupO (hSO_eq ▸ hSO_le)
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq
    (oddSector ⊓ LinearMap.ker (C - (2:ℝ) • LinearMap.id)) (oddSector ⊓ LinearMap.ker C)
  rw [hsup, hinf, finrank_bot, add_zero] at hsum
  have finO : Module.finrank ℝ oddSector = 32 := by rw [← hSO_eq, finSO]
  rw [finO] at hsum
  have hA : 24 ≤ Module.finrank ℝ ↥(oddSector ⊓ LinearMap.ker (C - (2:ℝ) • LinearMap.id)) := by
    rw [← Cl6Build.card_A]
    exact Cl6Build.card_le_finrank_of_mem
      (fun i : {n : Fin 64 // (Cl6Build.bits n).length % 2 = 1 ∧ Cl6Build.cnt (Cl6Build.bits n) = 2} => Cl6Build.blade i.1)
      (Cl6Build.blade_li.comp _ Subtype.val_injective) _ (fun i => memA i.1 i.2.1 i.2.2)
  have hB : 8 ≤ Module.finrank ℝ ↥(oddSector ⊓ LinearMap.ker C) := by
    rw [← Cl6Build.card_B]
    exact Cl6Build.card_le_finrank_of_mem
      (fun i : {n : Fin 64 // (Cl6Build.bits n).length % 2 = 1 ∧ Cl6Build.cnt (Cl6Build.bits n) = 0} => Cl6Build.blade i.1)
      (Cl6Build.blade_li.comp _ Subtype.val_injective) _ (fun i => memB i.1 i.2.1 i.2.2)
  refine ⟨fun x hx => ⟨p1 x hx, p2 x hx, p3 x hx, pC x hx⟩, hsup, by omega, by omega⟩

/-! ## Platform statement

The formal statement registered on prove2.me (manifest `formal_statement`), proved by the solution above. -/

section Prove2meStatement

theorem Clifford6Casimir.spectrum
    (T1 T2 T3 C : CliffordAlgebra Clifford6.Q60 →ₗ[ℝ] CliffordAlgebra Clifford6.Q60)
    (h1 : ∀ x, T1 x = (1/2:ℝ) • (Clifford6.E1 * x - x * Clifford6.E1))
    (h2 : ∀ x, T2 x = (1/2:ℝ) • (Clifford6.E2 * x - x * Clifford6.E2))
    (h3 : ∀ x, T3 x = (1/2:ℝ) • (Clifford6.E3 * x - x * Clifford6.E3))
    (hC : ∀ x, C x = -(T1 (T1 x) + T2 (T2 x) + T3 (T3 x))) :
    (∀ x ∈ Clifford6.oddSector,
      T1 x ∈ Clifford6.oddSector ∧ T2 x ∈ Clifford6.oddSector ∧
        T3 x ∈ Clifford6.oddSector ∧ C x ∈ Clifford6.oddSector)
      ∧ (Clifford6.oddSector ⊓ LinearMap.ker (C - (2:ℝ) • LinearMap.id) ⊔
          Clifford6.oddSector ⊓ LinearMap.ker C = Clifford6.oddSector)
      ∧ (Module.finrank ℝ
          ↥(Clifford6.oddSector ⊓ LinearMap.ker (C - (2:ℝ) • LinearMap.id)) = 24)
      ∧ (Module.finrank ℝ ↥(Clifford6.oddSector ⊓ LinearMap.ker C) = 8) :=
  _root_.Prove2me.Solution.Clifford6Casimir_spectrum T1 T2 T3 C h1 h2 h3 hC



end Prove2meStatement
