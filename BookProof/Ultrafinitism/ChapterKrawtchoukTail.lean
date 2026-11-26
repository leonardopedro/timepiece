import Mathlib.Tactic
import Mathlib.Data.Finset.Powerset
import Mathlib.Data.Finset.SymmDiff
import Mathlib.Data.Nat.Choose.Basic
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Data.Fintype.BigOperators

/-!
# Chapter KrawtchoukTail — Strictly Finite Dyadic Gaussian Tail

This module replaces the infinite coordinate tail `(ℕ → ℝ, γ)` of the classical
Solovay–Mehler–Kopperman framework with a **strictly finite** dyadic hypercube
`BitCube M = Fin M → Bool` equipped with the uniform probability law `cubeExpect M`.

Everything here is computable over `ℚ` (zero `noncomputable`, zero `MeasureTheory`,
zero `sorry`, zero custom axioms).

## Main results

* `walsh_mul`, `walsh_expect`, `walsh_inner` — Walsh characters form an exact
  orthonormal basis of `BitCube M → ℚ`.
* `krawtchouk_inner` — unnormalized Krawtchouk modes are mutually orthogonal with
  exact integer squared norm `Nat.choose M n`.
* `krawtchouk_one_mul_succ` — exact finite-horizon ladder / linearization identity,
  closing at degree `M` (`krawtchouk_gt`).
* `discreteMehler_krawtchouk`, `discreteMehler_selfAdjoint`, `discreteMehler_comp` —
  the Bonami–Beckner bit-flip channel is a self-adjoint Markov semigroup with exact
  Mehler eigenvalues `ρ ^ n`.
* `dyadicGauss_mean`, `dyadicGauss_variance`, `dyadicGauss_fourth_moment` — for
  `M = 4 ^ q`, the scaled sum `dyadicGauss q` is an exact dyadic rational with
  mean `0`, variance `1`, and fourth moment `3 - 2 / 4 ^ q`.
* `walsh_expansion`, `card_walsh_basis`, `parity_low_degree_l2_error`,
  `discreteMehler_parity`, `pointInd_sq_expect`, `pointInd_walshCoeff` — exact
  degree-`2^M` representation and low-degree / `L²` approximation obstructions.
-/

namespace BookProof.Ultrafinitism.ChapterKrawtchoukTail

open scoped BigOperators

/-! ## 1. The Boolean hypercube and uniform expectation -/

/-- A single coordinate block of `M` microscopic signs `{-1, +1}`. -/
abbrev BitCube (M : ℕ) := Fin M → Bool

/-- Map `Bool` to `{-1, +1} ⊂ ℚ`. -/
def bitSign (b : Bool) : ℚ := if b then 1 else -1

@[simp] theorem bitSign_true : bitSign true = 1 := rfl
@[simp] theorem bitSign_false : bitSign false = -1 := rfl

theorem bitSign_mul_self (b : Bool) : bitSign b * bitSign b = 1 := by
  cases b <;> norm_num

theorem bitSign_sq (b : Bool) : bitSign b ^ 2 = 1 := by
  cases b <;> norm_num

theorem sum_bitSign : (∑ b : Bool, bitSign b) = 0 := by
  simp

/-- Uniform expectation over `BitCube M = (Fin M → Bool)`. -/
def cubeExpect (M : ℕ) (f : BitCube M → ℚ) : ℚ :=
  (∑ x : BitCube M, f x) / ((2 ^ M : ℕ) : ℚ)

theorem two_pow_pos_rat (M : ℕ) : (0 : ℚ) < ((2 ^ M : ℕ) : ℚ) := by
  positivity

theorem two_pow_ne_zero_rat (M : ℕ) : ((2 ^ M : ℕ) : ℚ) ≠ 0 :=
  (two_pow_pos_rat M).ne'

theorem cubeExpect_const (M : ℕ) (c : ℚ) :
    cubeExpect M (fun _ => c) = c := by
  simp [cubeExpect]

theorem cubeExpect_zero (M : ℕ) :
    cubeExpect M (fun _ => 0) = 0 := by
  simp [cubeExpect]

theorem cubeExpect_add (M : ℕ) (f g : BitCube M → ℚ) :
    cubeExpect M (fun x => f x + g x) = cubeExpect M f + cubeExpect M g := by
  simp [cubeExpect, Finset.sum_add_distrib, add_div]

theorem cubeExpect_sub (M : ℕ) (f g : BitCube M → ℚ) :
    cubeExpect M (fun x => f x - g x) = cubeExpect M f - cubeExpect M g := by
  simp [cubeExpect, Finset.sum_sub_distrib, sub_div]

theorem cubeExpect_smul (M : ℕ) (c : ℚ) (f : BitCube M → ℚ) :
    cubeExpect M (fun x => c * f x) = c * cubeExpect M f := by
  simp [cubeExpect, ← Finset.mul_sum, mul_div_assoc]

theorem cubeExpect_sum {ι : Type*} (s : Finset ι) (M : ℕ) (f : ι → BitCube M → ℚ) :
    cubeExpect M (fun x => ∑ i ∈ s, f i x) = ∑ i ∈ s, cubeExpect M (f i) := by
  simp only [cubeExpect, Finset.sum_div]
  rw [Finset.sum_comm]

theorem cubeExpect_nonneg (M : ℕ) (f : BitCube M → ℚ) (hf : ∀ x, 0 ≤ f x) :
    0 ≤ cubeExpect M f := by
  unfold cubeExpect
  exact div_nonneg (Finset.sum_nonneg fun x _ => hf x) (two_pow_pos_rat M).le

/-- Factorization of expectation over independent product functions on `Fin M → Bool`. -/
theorem cubeExpect_prod_factor (M : ℕ) (f : Fin M → Bool → ℚ) :
    cubeExpect M (fun x => ∏ i : Fin M, f i (x i)) =
      ∏ i : Fin M, ((f i false + f i true) / 2) := by
  unfold cubeExpect
  have hsum : (∑ x : BitCube M, ∏ i : Fin M, f i (x i)) =
      ∏ i : Fin M, (f i false + f i true) := by
    rw [← Fintype.prod_sum (fun i b => f i b)]
    congr 1
    ext i
    rw [Fintype.sum_bool, add_comm]
  have hden : ((2 ^ M : ℕ) : ℚ) = ∏ _i : Fin M, (2 : ℚ) := by
    push_cast
    simp [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hsum, hden, ← Finset.prod_div_distrib]

/-! ## 2. Walsh characters -/

/-- Walsh character indexed by a subset `S ⊆ Fin M`. -/
def walsh {M : ℕ} (S : Finset (Fin M)) (x : BitCube M) : ℚ :=
  ∏ i ∈ S, bitSign (x i)

theorem walsh_empty {M : ℕ} (x : BitCube M) : walsh (∅ : Finset (Fin M)) x = 1 := by
  simp [walsh]

theorem walsh_eq_prod_ite {M : ℕ} (S : Finset (Fin M)) (x : BitCube M) :
    walsh S x = ∏ i : Fin M, (if i ∈ S then bitSign (x i) else 1) := by
  unfold walsh
  rw [Finset.prod_ite_mem, Finset.univ_inter]

/-- Multiplication of Walsh characters corresponds to symmetric difference. -/
theorem walsh_mul {M : ℕ} (S T : Finset (Fin M)) (x : BitCube M) :
    walsh S x * walsh T x = walsh (symmDiff S T) x := by
  rw [walsh_eq_prod_ite, walsh_eq_prod_ite, walsh_eq_prod_ite, ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases hS : i ∈ S <;> by_cases hT : i ∈ T <;>
    simp [hS, hT, Finset.mem_symmDiff, bitSign_mul_self]

/-- Expectation of a Walsh character is `1` on `∅` and `0` otherwise. -/
theorem walsh_expect {M : ℕ} (S : Finset (Fin M)) :
    cubeExpect M (walsh S) = if S = ∅ then 1 else 0 := by
  have hfac : cubeExpect M (walsh S) =
      ∏ i : Fin M, (if i ∈ S then (0 : ℚ) else 1) := by
    have heq : (fun x => walsh S x) =
        fun x => ∏ i : Fin M, (if i ∈ S then bitSign (x i) else 1) :=
      funext (walsh_eq_prod_ite S)
    change cubeExpect M (fun x => walsh S x) = _
    rw [heq, cubeExpect_prod_factor M (fun i b => if i ∈ S then bitSign b else 1)]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : i ∈ S <;> simp [hi]
  rw [hfac]
  by_cases hS : S = ∅
  · subst hS
    simp
  · simp only [if_neg hS]
    obtain ⟨i₀, hi₀⟩ := Finset.nonempty_iff_ne_empty.mpr hS
    exact Finset.prod_eq_zero (Finset.mem_univ i₀) (by simp [hi₀])

/-- Orthogonality of Walsh characters under `cubeExpect M`. -/
theorem walsh_inner {M : ℕ} (S T : Finset (Fin M)) :
    cubeExpect M (fun x => walsh S x * walsh T x) = if S = T then 1 else 0 := by
  have h : (fun x => walsh S x * walsh T x) = walsh (symmDiff S T) :=
    funext (walsh_mul S T)
  rw [h, walsh_expect]
  have heq : symmDiff S T = ∅ ↔ S = T := by
    rw [Finset.eq_empty_iff_forall_notMem, Finset.ext_iff]
    constructor
    · intro h i
      have hi := h i
      rw [Finset.mem_symmDiff] at hi
      tauto
    · intro h i
      simp [Finset.mem_symmDiff, h i]
  simp [heq]

/-! ## 3. Unnormalized Krawtchouk basis and exact ladder identities -/

/-- Unnormalized Krawtchouk mode of degree `n` on `BitCube M`. -/
def krawtchouk (M n : ℕ) (x : BitCube M) : ℚ :=
  ∑ S ∈ (Finset.univ : Finset (Fin M)).powersetCard n, walsh S x

@[simp] theorem krawtchouk_zero (M : ℕ) (x : BitCube M) :
    krawtchouk M 0 x = 1 := by
  simp [krawtchouk, walsh_empty]

theorem krawtchouk_gt {M n : ℕ} (h : M < n) (x : BitCube M) :
    krawtchouk M n x = 0 := by
  have hempty : (Finset.univ : Finset (Fin M)).powersetCard n = ∅ := by
    rw [Finset.eq_empty_iff_forall_notMem]
    intro S hS
    have hcard : S.card = n := (Finset.mem_powersetCard.mp hS).2
    have hle : S.card ≤ M := by
      simpa [Fintype.card_fin] using Finset.card_le_univ S
    omega
  simp [krawtchouk, hempty]

/-- Exact orthogonality of unnormalized Krawtchouk modes. -/
theorem krawtchouk_inner (M n m : ℕ) :
    cubeExpect M (fun x => krawtchouk M n x * krawtchouk M m x) =
      if n = m then (Nat.choose M n : ℚ) else 0 := by
  have hexp : (fun x => krawtchouk M n x * krawtchouk M m x) =
      fun x => ∑ S ∈ (Finset.univ : Finset (Fin M)).powersetCard n,
        ∑ T ∈ (Finset.univ : Finset (Fin M)).powersetCard m,
          walsh S x * walsh T x := by
    ext x
    simp only [krawtchouk, Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
  rw [hexp, cubeExpect_sum]
  have h1 : ∀ S ∈ (Finset.univ : Finset (Fin M)).powersetCard n,
      cubeExpect M (fun x =>
        ∑ T ∈ (Finset.univ : Finset (Fin M)).powersetCard m, walsh S x * walsh T x) =
      if n = m then 1 else 0 := by
    intro S hS
    rw [cubeExpect_sum]
    simp_rw [walsh_inner]
    have hScard : S.card = n := (Finset.mem_powersetCard.mp hS).2
    by_cases hnm : n = m
    · subst hnm
      simp [hS]
    · simp only [if_neg hnm]
      refine Finset.sum_eq_zero fun T hT => ?_
      have hTcard : T.card = m := (Finset.mem_powersetCard.mp hT).2
      have hne : S ≠ T := fun h => hnm (hScard.symm.trans (h ▸ hTcard))
      simp [hne]
  rw [Finset.sum_congr rfl h1]
  by_cases hnm : n = m
  · simp [hnm, Finset.card_powersetCard, Fintype.card_fin]
  · simp [hnm]

theorem krawtchouk_one_eq (M : ℕ) (x : BitCube M) :
    krawtchouk M 1 x = ∑ i : Fin M, bitSign (x i) := by
  unfold krawtchouk
  rw [Finset.powersetCard_one, Finset.sum_map]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp [walsh]

theorem krawtchouk_one_mul_zero (M : ℕ) (x : BitCube M) :
    krawtchouk M 1 x * krawtchouk M 0 x = krawtchouk M 1 x := by
  simp

private theorem bitSign_mul_walsh_mem {M : ℕ} {i : Fin M} {S : Finset (Fin M)}
    (hi : i ∈ S) (x : BitCube M) :
    bitSign (x i) * walsh S x = walsh (S.erase i) x := by
  have hS : walsh S x = bitSign (x i) * walsh (S.erase i) x := by
    unfold walsh
    rw [← Finset.mul_prod_erase S (fun j => bitSign (x j)) hi]
  rw [hS, ← mul_assoc, bitSign_mul_self, one_mul]

private theorem bitSign_mul_walsh_notMem {M : ℕ} {i : Fin M} {S : Finset (Fin M)}
    (hi : i ∉ S) (x : BitCube M) :
    bitSign (x i) * walsh S x = walsh (insert i S) x := by
  unfold walsh
  rw [Finset.prod_insert hi]

/-- Exact finite-horizon ladder identity for unnormalized Krawtchouk polynomials. -/
theorem krawtchouk_one_mul_succ (M n : ℕ) (x : BitCube M) :
    krawtchouk M 1 x * krawtchouk M (n + 1) x =
      ((n + 2 : ℕ) : ℚ) * krawtchouk M (n + 2) x +
        ((M - n : ℕ) : ℚ) * krawtchouk M n x := by
  rw [krawtchouk_one_eq, krawtchouk, Finset.sum_mul]
  let P0 := (Finset.univ : Finset (Fin M)).powersetCard n
  let P1 := (Finset.univ : Finset (Fin M)).powersetCard (n + 1)
  let P2 := (Finset.univ : Finset (Fin M)).powersetCard (n + 2)
  let pairs := (Finset.univ : Finset (Fin M)) ×ˢ P1
  have hprod : (∑ i : Fin M, bitSign (x i) * ∑ S ∈ P1, walsh S x) =
      ∑ p ∈ pairs, bitSign (x p.1) * walsh p.2 x := by
    simp_rw [Finset.mul_sum]
    rw [← Finset.sum_product']
  rw [hprod]
  let A := pairs.filter (fun p => p.1 ∉ p.2)
  let B := pairs.filter (fun p => p.1 ∈ p.2)
  have hsplit : (∑ p ∈ pairs, bitSign (x p.1) * walsh p.2 x) =
      (∑ p ∈ A, walsh (insert p.1 p.2) x) +
        (∑ p ∈ B, walsh (p.2.erase p.1) x) := by
    rw [← Finset.sum_filter_add_sum_filter_not pairs (fun p => p.1 ∉ p.2)]
    congr 1
    · refine Finset.sum_congr rfl fun p hp => ?_
      exact bitSign_mul_walsh_notMem (Finset.mem_filter.mp hp).2 x
    · have hB : pairs.filter (fun p => ¬ p.1 ∉ p.2) = B := by
        ext p; simp [B]
      rw [hB]
      refine Finset.sum_congr rfl fun p hp => ?_
      exact bitSign_mul_walsh_mem (Finset.mem_filter.mp hp).2 x
  have hA : (∑ p ∈ A, walsh (insert p.1 p.2) x) =
      ((n + 2 : ℕ) : ℚ) * krawtchouk M (n + 2) x := by
    have hmap : ∀ p ∈ A, insert p.1 p.2 ∈ P2 := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hp_mem, hp_not⟩
      have hcard : p.2.card = n + 1 :=
        (Finset.mem_powersetCard.mp (Finset.mem_product.mp hp_mem).2).2
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.card_insert_of_notMem hp_not, hcard]
    rw [← Finset.sum_fiberwise_of_maps_to hmap (fun p => walsh (insert p.1 p.2) x)]
    have hfib : ∀ U ∈ P2,
        (∑ p ∈ A.filter (fun p => insert p.1 p.2 = U), walsh (insert p.1 p.2) x) =
          ((n + 2 : ℕ) : ℚ) * walsh U x := by
      intro U hU
      have hUcard : U.card = n + 2 := (Finset.mem_powersetCard.mp hU).2
      have hconst : (∑ p ∈ A.filter (fun p => insert p.1 p.2 = U),
          walsh (insert p.1 p.2) x) =
          ∑ _p ∈ A.filter (fun p => insert p.1 p.2 = U), walsh U x :=
        Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2]
      rw [hconst, Finset.sum_const, nsmul_eq_mul]
      have hbij : (A.filter (fun p => insert p.1 p.2 = U)).card = U.card := by
        refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
        · intro p hp
          rcases Finset.mem_filter.mp hp with ⟨_, hins⟩
          dsimp only
          rw [← hins]
          exact Finset.mem_insert_self _ _
        · intro p₁ hp₁ p₂ hp₂ heq
          rcases Finset.mem_filter.mp hp₁ with ⟨hp₁A, hins₁⟩
          rcases Finset.mem_filter.mp hp₂ with ⟨hp₂A, hins₂⟩
          have h1not : p₁.1 ∉ p₁.2 := (Finset.mem_filter.mp hp₁A).2
          have h2not : p₂.1 ∉ p₂.2 := (Finset.mem_filter.mp hp₂A).2
          have hp2eq : p₁.2 = p₂.2 := by
            have e1 := Finset.erase_insert h1not
            have e2 := Finset.erase_insert h2not
            dsimp only at heq
            rw [← e1, ← e2, hins₁, hins₂, heq]
          exact Prod.ext heq hp2eq
        · intro i hi
          refine ⟨(i, U.erase i), ?_, rfl⟩
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
            ⟨Finset.mem_univ i, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩⟩,
            Finset.notMem_erase i U⟩, Finset.insert_erase hi⟩
          rw [Finset.card_erase_of_mem hi, hUcard]
          omega
      rw [hbij, hUcard]
    rw [Finset.sum_congr rfl hfib, ← Finset.mul_sum]
    rfl
  have hB : (∑ p ∈ B, walsh (p.2.erase p.1) x) =
      ((M - n : ℕ) : ℚ) * krawtchouk M n x := by
    have hmap : ∀ p ∈ B, p.2.erase p.1 ∈ P0 := by
      intro p hp
      rcases Finset.mem_filter.mp hp with ⟨hp_mem, hp_in⟩
      have hcard : p.2.card = n + 1 :=
        (Finset.mem_powersetCard.mp (Finset.mem_product.mp hp_mem).2).2
      rw [Finset.mem_powersetCard]
      refine ⟨Finset.subset_univ _, ?_⟩
      rw [Finset.card_erase_of_mem hp_in, hcard]
      omega
    rw [← Finset.sum_fiberwise_of_maps_to hmap (fun p => walsh (p.2.erase p.1) x)]
    have hfib : ∀ T ∈ P0,
        (∑ p ∈ B.filter (fun p => p.2.erase p.1 = T), walsh (p.2.erase p.1) x) =
          ((M - n : ℕ) : ℚ) * walsh T x := by
      intro T hT
      have hTcard : T.card = n := (Finset.mem_powersetCard.mp hT).2
      have hconst : (∑ p ∈ B.filter (fun p => p.2.erase p.1 = T),
          walsh (p.2.erase p.1) x) =
          ∑ _p ∈ B.filter (fun p => p.2.erase p.1 = T), walsh T x :=
        Finset.sum_congr rfl fun p hp => by rw [(Finset.mem_filter.mp hp).2]
      rw [hconst, Finset.sum_const, nsmul_eq_mul]
      have hbij : (B.filter (fun p => p.2.erase p.1 = T)).card =
          ((Finset.univ : Finset (Fin M)) \ T).card := by
        refine Finset.card_bij (fun p _ => p.1) ?_ ?_ ?_
        · intro p hp
          rcases Finset.mem_filter.mp hp with ⟨_, her⟩
          rw [Finset.mem_sdiff]
          refine ⟨Finset.mem_univ _, ?_⟩
          dsimp only
          rw [← her]
          exact Finset.notMem_erase _ _
        · intro p₁ hp₁ p₂ hp₂ heq
          rcases Finset.mem_filter.mp hp₁ with ⟨hp₁B, her₁⟩
          rcases Finset.mem_filter.mp hp₂ with ⟨hp₂B, her₂⟩
          have h1in : p₁.1 ∈ p₁.2 := (Finset.mem_filter.mp hp₁B).2
          have h2in : p₂.1 ∈ p₂.2 := (Finset.mem_filter.mp hp₂B).2
          have hp2eq : p₁.2 = p₂.2 := by
            dsimp only at heq
            rw [← Finset.insert_erase h1in, ← Finset.insert_erase h2in, her₁, her₂, heq]
          exact Prod.ext heq hp2eq
        · intro i hi
          have hiT : i ∉ T := (Finset.mem_sdiff.mp hi).2
          refine ⟨(i, insert i T), ?_, rfl⟩
          rw [Finset.mem_filter]
          refine ⟨Finset.mem_filter.mpr ⟨Finset.mem_product.mpr
            ⟨Finset.mem_univ i, Finset.mem_powersetCard.mpr ⟨Finset.subset_univ _, ?_⟩⟩,
            Finset.mem_insert_self i T⟩, Finset.erase_insert hiT⟩
          rw [Finset.card_insert_of_notMem hiT, hTcard]
      have hsdiff : ((Finset.univ : Finset (Fin M)) \ T).card = M - n := by
        rw [Finset.card_sdiff, Finset.inter_univ, Finset.card_univ, Fintype.card_fin, hTcard]
      rw [hbij, hsdiff]
    rw [Finset.sum_congr rfl hfib, ← Finset.mul_sum]
    rfl
  rw [hsplit, hA, hB]

/-- Exact expansion of the square of the degree-1 Krawtchouk mode. -/
theorem krawtchouk_sq_one (M : ℕ) (x : BitCube M) :
    krawtchouk M 1 x ^ 2 = 2 * krawtchouk M 2 x + (M : ℚ) := by
  have h := krawtchouk_one_mul_succ M 0 x
  simpa [sq, krawtchouk_zero] using h

/-! ## 4. The discrete Mehler / Bonami–Beckner semigroup -/

/-- Transition weight of the Bonami–Beckner bit-flip channel with parameter `ρ`. -/
def mehlerWeight {M : ℕ} (ρ : ℚ) (x y : BitCube M) : ℚ :=
  ∏ i : Fin M, (if x i = y i then (1 + ρ) / 2 else (1 - ρ) / 2)

/-- The discrete Mehler operator `T_ρ` on `BitCube M → ℚ`. -/
def discreteMehler (M : ℕ) (ρ : ℚ) (f : BitCube M → ℚ) (x : BitCube M) : ℚ :=
  ∑ y : BitCube M, mehlerWeight ρ x y * f y

theorem mehlerWeight_symm {M : ℕ} (ρ : ℚ) (x y : BitCube M) :
    mehlerWeight ρ x y = mehlerWeight ρ y x := by
  refine Finset.prod_congr rfl fun i _ => ?_
  by_cases h : x i = y i
  · simp [h]
  · simp [h, Ne.symm h]

theorem mehlerWeight_nonneg {M : ℕ} {ρ : ℚ} (h1 : -1 ≤ ρ) (h2 : ρ ≤ 1)
    (x y : BitCube M) : 0 ≤ mehlerWeight ρ x y := by
  refine Finset.prod_nonneg fun i _ => ?_
  by_cases h : x i = y i
  · simp [h]; linarith
  · simp [h]; linarith

theorem sum_mehlerWeight (M : ℕ) (ρ : ℚ) (x : BitCube M) :
    (∑ y : BitCube M, mehlerWeight ρ x y) = 1 := by
  unfold mehlerWeight
  rw [← Fintype.prod_sum (fun i b => if x i = b then (1 + ρ) / 2 else (1 - ρ) / 2)]
  refine Finset.prod_eq_one fun i _ => ?_
  cases x i <;> simp <;> ring

theorem sum_mehlerWeight_mul (M : ℕ) (ρ₁ ρ₂ : ℚ) (x y : BitCube M) :
    (∑ z : BitCube M, mehlerWeight ρ₁ x z * mehlerWeight ρ₂ z y) =
      mehlerWeight (ρ₁ * ρ₂) x y := by
  have hprod : (∑ z : BitCube M, mehlerWeight ρ₁ x z * mehlerWeight ρ₂ z y) =
      ∑ z : BitCube M, ∏ i : Fin M,
        ((if x i = z i then (1 + ρ₁) / 2 else (1 - ρ₁) / 2) *
          (if z i = y i then (1 + ρ₂) / 2 else (1 - ρ₂) / 2)) := by
    refine Finset.sum_congr rfl fun z _ => ?_
    unfold mehlerWeight
    rw [Finset.prod_mul_distrib]
  rw [hprod, ← Fintype.prod_sum
    (fun i b => (if x i = b then (1 + ρ₁) / 2 else (1 - ρ₁) / 2) *
      (if b = y i then (1 + ρ₂) / 2 else (1 - ρ₂) / 2))]
  unfold mehlerWeight
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Fintype.sum_bool]
  cases x i <;> cases y i <;> simp <;> ring

/-- Semigroup law for the discrete Mehler operator: `T_{ρ₁} ∘ T_{ρ₂} = T_{ρ₁ ρ₂}`. -/
theorem discreteMehler_comp (M : ℕ) (ρ₁ ρ₂ : ℚ) (f : BitCube M → ℚ) (x : BitCube M) :
    discreteMehler M ρ₁ (discreteMehler M ρ₂ f) x =
      discreteMehler M (ρ₁ * ρ₂) f x := by
  unfold discreteMehler
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun y _ => ?_
  have h : (∑ z : BitCube M, mehlerWeight ρ₁ x z * (mehlerWeight ρ₂ z y * f y)) =
      (∑ z : BitCube M, mehlerWeight ρ₁ x z * mehlerWeight ρ₂ z y) * f y := by
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun z _ => by ring
  rw [h, sum_mehlerWeight_mul]

/-- Self-adjointness of `discreteMehler` with respect to `cubeExpect M`. -/
theorem discreteMehler_selfAdjoint (M : ℕ) (ρ : ℚ) (f g : BitCube M → ℚ) :
    cubeExpect M (fun x => f x * discreteMehler M ρ g x) =
      cubeExpect M (fun x => discreteMehler M ρ f x * g x) := by
  unfold cubeExpect discreteMehler
  congr 1
  simp_rw [Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun x _ => Finset.sum_congr rfl fun y _ => ?_
  rw [mehlerWeight_symm ρ y x]
  ring

/-- Every Walsh character is an exact eigenfunction of `discreteMehler`. -/
theorem discreteMehler_walsh (M : ℕ) (ρ : ℚ) (S : Finset (Fin M)) (x : BitCube M) :
    discreteMehler M ρ (walsh S) x = ρ ^ S.card * walsh S x := by
  unfold discreteMehler
  have hexp : (∑ y : BitCube M, mehlerWeight ρ x y * walsh S y) =
      ∑ y : BitCube M, ∏ i : Fin M,
        ((if x i = y i then (1 + ρ) / 2 else (1 - ρ) / 2) *
          (if i ∈ S then bitSign (y i) else 1)) := by
    refine Finset.sum_congr rfl fun y _ => ?_
    unfold mehlerWeight
    rw [walsh_eq_prod_ite, Finset.prod_mul_distrib]
  rw [hexp, ← Fintype.prod_sum
    (fun i b => (if x i = b then (1 + ρ) / 2 else (1 - ρ) / 2) *
      (if i ∈ S then bitSign b else 1))]
  have hfac : (∏ i : Fin M, ∑ b : Bool,
      ((if x i = b then (1 + ρ) / 2 else (1 - ρ) / 2) *
        (if i ∈ S then bitSign b else 1))) =
      ∏ i : Fin M, (if i ∈ S then ρ * bitSign (x i) else 1) := by
    refine Finset.prod_congr rfl fun i _ => ?_
    rw [Fintype.sum_bool]
    by_cases hi : i ∈ S
    · simp only [hi, ↓reduceIte]
      cases x i <;> simp <;> ring
    · simp only [hi, ↓reduceIte, mul_one]
      cases x i <;> simp <;> ring
  rw [hfac]
  have hsplit : (∏ i : Fin M, (if i ∈ S then ρ * bitSign (x i) else 1)) =
      (∏ i : Fin M, (if i ∈ S then ρ else 1)) *
        (∏ i : Fin M, (if i ∈ S then bitSign (x i) else 1)) := by
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    by_cases hi : i ∈ S <;> simp [hi]
  rw [hsplit, ← walsh_eq_prod_ite]
  congr 1
  rw [Finset.prod_ite_mem, Finset.univ_inter, Finset.prod_const]

/-- Every unnormalized Krawtchouk mode of degree `n` is an exact eigenfunction of `T_ρ`
with eigenvalue `ρ ^ n`. -/
theorem discreteMehler_krawtchouk (M n : ℕ) (ρ : ℚ) (x : BitCube M) :
    discreteMehler M ρ (krawtchouk M n) x = ρ ^ n * krawtchouk M n x := by
  unfold discreteMehler krawtchouk
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  have hterm : ∀ S ∈ (Finset.univ : Finset (Fin M)).powersetCard n,
      (∑ y : BitCube M, mehlerWeight ρ x y * walsh S y) = ρ ^ n * walsh S x := by
    intro S hS
    have hcard : S.card = n := (Finset.mem_powersetCard.mp hS).2
    simpa [discreteMehler, hcard] using discreteMehler_walsh M ρ S x
  rw [Finset.sum_congr rfl hterm, ← Finset.mul_sum]

/-! ## 5. Exact dyadic Gaussian coordinate for `M = 4 ^ q` -/

/-- Exact dyadic Gaussian coordinate on `BitCube (4 ^ q)`: since `√(4 ^ q) = 2 ^ q`,
every value is an exact dyadic rational. -/
def dyadicGauss (q : ℕ) (x : BitCube (4 ^ q)) : ℚ :=
  krawtchouk (4 ^ q) 1 x / ((2 ^ q : ℕ) : ℚ)

theorem dyadicGauss_mean (q : ℕ) :
    cubeExpect (4 ^ q) (dyadicGauss q) = 0 := by
  have heq : (fun x => dyadicGauss q x) =
      fun x => (1 / ((2 ^ q : ℕ) : ℚ)) * (krawtchouk (4 ^ q) 1 x * krawtchouk (4 ^ q) 0 x) := by
    ext x
    simp [dyadicGauss, div_eq_mul_inv, mul_comm]
  change cubeExpect (4 ^ q) (fun x => dyadicGauss q x) = 0
  rw [heq, cubeExpect_smul, krawtchouk_inner]
  simp

theorem dyadicGauss_variance (q : ℕ) :
    cubeExpect (4 ^ q) (fun x => (dyadicGauss q x) ^ 2) = 1 := by
  have heq : (fun x => (dyadicGauss q x) ^ 2) =
      fun x => (1 / ((4 ^ q : ℕ) : ℚ)) *
        (krawtchouk (4 ^ q) 1 x * krawtchouk (4 ^ q) 1 x) := by
    ext x
    have h24 : ((2 ^ q : ℕ) : ℚ) ^ 2 = ((4 ^ q : ℕ) : ℚ) := by
      push_cast
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    simp only [dyadicGauss, ← h24, sq]
    ring
  rw [heq, cubeExpect_smul, krawtchouk_inner]
  simp only [↓reduceIte, Nat.choose_one_right]
  have hpos : ((4 ^ q : ℕ) : ℚ) ≠ 0 := by positivity
  field_simp

theorem dyadicGauss_fourth_moment (q : ℕ) :
    cubeExpect (4 ^ q) (fun x => (dyadicGauss q x) ^ 4) = 3 - 2 / ((4 ^ q : ℕ) : ℚ) := by
  let M : ℕ := 4 ^ q
  have hMpos : 1 ≤ M := Nat.one_le_pow q 4 (by norm_num)
  have hMne : (M : ℚ) ≠ 0 := by positivity
  have hpoly : ∀ x : BitCube M,
      krawtchouk M 1 x ^ 4 =
        4 * (krawtchouk M 2 x * krawtchouk M 2 x) +
          4 * (M : ℚ) * (krawtchouk M 2 x * krawtchouk M 0 x) +
          (M : ℚ) ^ 2 := by
    intro x
    have h2 := krawtchouk_sq_one M x
    calc krawtchouk M 1 x ^ 4
        = (krawtchouk M 1 x ^ 2) ^ 2 := by ring
      _ = (2 * krawtchouk M 2 x + (M : ℚ)) ^ 2 := by rw [h2]
      _ = 4 * (krawtchouk M 2 x * krawtchouk M 2 x) +
            4 * (M : ℚ) * (krawtchouk M 2 x * krawtchouk M 0 x) + (M : ℚ) ^ 2 := by
          simp [krawtchouk_zero]; ring
  have hexp4 : cubeExpect M (fun x => krawtchouk M 1 x ^ 4) =
      4 * (Nat.choose M 2 : ℚ) + (M : ℚ) ^ 2 := by
    have hf : (fun x => krawtchouk M 1 x ^ 4) =
        fun x => 4 * (krawtchouk M 2 x * krawtchouk M 2 x) +
          4 * (M : ℚ) * (krawtchouk M 2 x * krawtchouk M 0 x) + (M : ℚ) ^ 2 :=
      funext hpoly
    rw [hf, cubeExpect_add, cubeExpect_add, cubeExpect_smul, cubeExpect_smul,
      cubeExpect_const, krawtchouk_inner, krawtchouk_inner]
    simp
  have hchoose : 2 * (Nat.choose M 2 : ℚ) = (M : ℚ) * ((M : ℚ) - 1) := by
    have hc : Nat.choose M 2 * 2 = M * (M - 1) := by
      rw [Nat.choose_two_right, Nat.div_mul_cancel]
      exact Nat.even_mul_pred_self M |>.two_dvd
    have hc' : (Nat.choose M 2 : ℚ) * 2 = ((M * (M - 1) : ℕ) : ℚ) := by exact_mod_cast hc
    rw [Nat.cast_mul, Nat.cast_sub hMpos, Nat.cast_one] at hc'
    linarith
  have hscale : (fun x : BitCube M => (dyadicGauss q x) ^ 4) =
      fun x => (1 / ((M : ℚ) ^ 2)) * krawtchouk M 1 x ^ 4 := by
    ext x
    have h24 : ((2 ^ q : ℕ) : ℚ) ^ 4 = (M : ℚ) ^ 2 := by
      dsimp [M]
      push_cast
      rw [show (4 : ℚ) = 2 ^ 2 by norm_num, ← pow_mul, ← pow_mul, ← pow_mul]
      congr 1
      ring
    simp only [dyadicGauss, div_pow, h24]
    ring
  change cubeExpect M (fun x => (dyadicGauss q x) ^ 4) = 3 - 2 / (M : ℚ)
  rw [hscale, cubeExpect_smul, hexp4]
  field_simp [hMne]
  linarith [hchoose]

/-! ## 6. Polynomial representation vs. complexity obstructions -/

/-- Exact Walsh–Fourier coefficient of `f : BitCube M → ℚ` on subset `S`. -/
def walshCoeff {M : ℕ} (f : BitCube M → ℚ) (S : Finset (Fin M)) : ℚ :=
  cubeExpect M (fun x => f x * walsh S x)

/-- The full Walsh polynomial basis on `BitCube M` has dimension `2 ^ M`. -/
theorem card_walsh_basis (M : ℕ) : Fintype.card (Finset (Fin M)) = 2 ^ M := by
  simp [Fintype.card_finset]

/-- Completeness kernel of the Walsh basis on `BitCube M`. -/
theorem sum_walsh_mul (M : ℕ) (x y : BitCube M) :
    (∑ S : Finset (Fin M), walsh S y * walsh S x) =
      if y = x then ((2 ^ M : ℕ) : ℚ) else 0 := by
  have hprod : (∑ S : Finset (Fin M), walsh S y * walsh S x) =
      ∏ i : Fin M, (1 + bitSign (y i) * bitSign (x i)) := by
    have hpow : (∏ i : Fin M, (1 + bitSign (y i) * bitSign (x i))) =
        ∑ S ∈ (Finset.univ : Finset (Fin M)).powerset,
          ∏ i ∈ S, (bitSign (y i) * bitSign (x i)) :=
      Finset.prod_one_add Finset.univ
    rw [hpow, Finset.powerset_univ]
    refine Finset.sum_congr rfl fun S _ => ?_
    simp [walsh, Finset.prod_mul_distrib]
  rw [hprod]
  by_cases hyx : y = x
  · subst hyx
    simp only [↓reduceIte]
    have hfac : ∀ i : Fin M, 1 + bitSign (y i) * bitSign (y i) = (2 : ℚ) := by
      intro i
      rw [bitSign_mul_self]
      norm_num
    rw [Finset.prod_congr rfl fun i _ => hfac i, Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
    norm_cast
  · simp only [if_neg hyx]
    obtain ⟨i₀, hi₀⟩ := Function.ne_iff.mp hyx
    refine Finset.prod_eq_zero (Finset.mem_univ i₀) ?_
    cases h1 : y i₀ <;> cases h2 : x i₀ <;> simp_all [bitSign]

/-- Every function on `BitCube M` equals an exact multilinear Walsh polynomial. -/
theorem walsh_expansion (M : ℕ) (f : BitCube M → ℚ) (x : BitCube M) :
    f x = ∑ S : Finset (Fin M), walshCoeff f S * walsh S x := by
  have hden : ((2 ^ M : ℕ) : ℚ) ≠ 0 := two_pow_ne_zero_rat M
  have hsum : (∑ S : Finset (Fin M), walshCoeff f S * walsh S x) =
      (∑ y : BitCube M, f y * ∑ S : Finset (Fin M), walsh S y * walsh S x) /
        ((2 ^ M : ℕ) : ℚ) := by
    simp only [walshCoeff, cubeExpect, div_mul_eq_mul_div, ← Finset.sum_div]
    congr 1
    simp_rw [Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun y _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun S _ => by ring
  rw [hsum]
  have hker : (∑ y : BitCube M, f y * ∑ S : Finset (Fin M), walsh S y * walsh S x) =
      f x * ((2 ^ M : ℕ) : ℚ) := by
    have h1 : (∑ y : BitCube M, f y * ∑ S : Finset (Fin M), walsh S y * walsh S x) =
        ∑ y : BitCube M, if y = x then f y * ((2 ^ M : ℕ) : ℚ) else 0 := by
      refine Finset.sum_congr rfl fun y _ => ?_
      rw [sum_walsh_mul]
      split_ifs <;> simp
    rw [h1, Finset.sum_ite_eq']
    simp
  rw [hker, mul_div_cancel_right₀ _ hden]

/-- Maximal-degree parity function `∏ i, bitSign (x i)` on `BitCube M`. -/
def parity (M : ℕ) (x : BitCube M) : ℚ :=
  walsh (Finset.univ : Finset (Fin M)) x

/-- Parity is orthogonal to every Walsh character of degree strictly below `M`. -/
theorem parity_orth_low_degree (M : ℕ) (S : Finset (Fin M)) (hS : S.card < M) :
    cubeExpect M (fun x => parity M x * walsh S x) = 0 := by
  unfold parity
  rw [walsh_inner]
  have hne : (Finset.univ : Finset (Fin M)) ≠ S := by
    intro h
    have hcard : (Finset.univ : Finset (Fin M)).card = S.card := by rw [h]
    rw [Finset.card_univ, Fintype.card_fin] at hcard
    omega
  simp [hne]

/-- Every polynomial of degree `< M` has squared `L²` error at least `1` against parity. -/
theorem parity_low_degree_l2_error (M : ℕ) (c : Finset (Fin M) → ℚ)
    (hc : ∀ S, M ≤ S.card → c S = 0) :
    1 ≤ cubeExpect M (fun x =>
      (parity M x - ∑ S : Finset (Fin M), c S * walsh S x) ^ 2) := by
  let p : BitCube M → ℚ := fun x => ∑ S : Finset (Fin M), c S * walsh S x
  have hexp : (fun x => (parity M x - p x) ^ 2) =
      fun x => parity M x * parity M x - 2 * (parity M x * p x) + p x ^ 2 := by
    ext x
    ring
  change 1 ≤ cubeExpect M (fun x => (parity M x - p x) ^ 2)
  rw [hexp, cubeExpect_add, cubeExpect_sub, cubeExpect_smul]
  have hpar : cubeExpect M (fun x => parity M x * parity M x) = 1 := by
    unfold parity
    rw [walsh_inner]
    simp
  have hcross : cubeExpect M (fun x => parity M x * p x) = 0 := by
    have hp : (fun x => parity M x * p x) =
        fun x => ∑ S : Finset (Fin M), c S * (parity M x * walsh S x) := by
      ext x
      simp only [p, Finset.mul_sum]
      refine Finset.sum_congr rfl fun S _ => by ring
    rw [hp, cubeExpect_sum]
    refine Finset.sum_eq_zero fun S _ => ?_
    rw [cubeExpect_smul]
    by_cases hS : S.card < M
    · rw [parity_orth_low_degree M S hS, mul_zero]
    · rw [hc S (Nat.le_of_not_lt hS), zero_mul]
  have hsq : 0 ≤ cubeExpect M (fun x => p x ^ 2) :=
    cubeExpect_nonneg M _ (fun x => sq_nonneg (p x))
  rw [hpar, hcross]
  linarith

/-- The discrete Mehler semigroup attenuates parity exponentially as `ρ ^ M`. -/
theorem discreteMehler_parity (M : ℕ) (ρ : ℚ) (x : BitCube M) :
    discreteMehler M ρ (parity M) x = ρ ^ M * parity M x := by
  unfold parity
  simpa [Finset.card_univ, Fintype.card_fin] using
    discreteMehler_walsh M ρ Finset.univ x

/-- Point indicator of a single assignment `a : BitCube M` (needle-in-a-haystack witness). -/
def pointInd {M : ℕ} (a : BitCube M) (x : BitCube M) : ℚ :=
  if x = a then 1 else 0

/-- A unique satisfying assignment has `L²` norm squared `2 ^ (-M)` under `cubeExpect M`. -/
theorem pointInd_sq_expect (M : ℕ) (a : BitCube M) :
    cubeExpect M (fun x => pointInd a x ^ 2) = 1 / ((2 ^ M : ℕ) : ℚ) := by
  unfold cubeExpect pointInd
  have hsum : (∑ x : BitCube M, (if x = a then (1 : ℚ) else 0) ^ 2) =
      ∑ x : BitCube M, if x = a then (1 : ℚ) else 0 := by
    refine Finset.sum_congr rfl fun x _ => by split_ifs <;> norm_num
  rw [hsum, Finset.sum_ite_eq']
  simp

/-- Every Walsh coefficient of a point indicator has magnitude `2 ^ (-M)`. -/
theorem pointInd_walshCoeff (M : ℕ) (a : BitCube M) (S : Finset (Fin M)) :
    walshCoeff (pointInd a) S = walsh S a / ((2 ^ M : ℕ) : ℚ) := by
  unfold walshCoeff cubeExpect pointInd
  have hsum : (∑ x : BitCube M, (if x = a then (1 : ℚ) else 0) * walsh S x) =
      ∑ x : BitCube M, if x = a then walsh S x else 0 := by
    refine Finset.sum_congr rfl fun x _ => by split_ifs <;> simp
  rw [hsum, Finset.sum_ite_eq']
  simp

end BookProof.Ultrafinitism.ChapterKrawtchoukTail
