import BookProof.Ultrafinitism.ChapterKrawtchoukTail
import Mathlib.Logic.Equiv.Fin.Basic

/-!
# Chapter UltrafinitistTensor — Resource-Accounting Tensor Product

In the classical Solovay–Kopperman theory (`ChapterSolovayCoordinates`,
`ChapterSolovayCrossDim`, `ChapterSolovayHilbertTensor`), the tail `ℕ → ℝ`
satisfies Hilbert's Hotel `Γ ⊗ Γ ≅ Γ`, so head enlargement `N ↦ N + k` and
arbitrary tensor products carry zero resource cost.

In the ultrafinitist theory `U-SMK`, a tail has an explicit coordinate budget
`R : ℕ`:
`MultiTail R M := Fin R → BitCube M`.

* Head-only observables still decouple in `O(1)` (`ultra_inner_reduces_to_head`).
* Cross-dimensional enlargement `k ≤ R` *consumes* `k` tail coordinates, leaving
  residual tail budget `R - k` while conserving total capacity `N + (k + R) = (N + k) + R`
  (`ultra_enlarge_expect_eq`).
* Tensoring two systems adds their tail budgets `R₁ + R₂` (`ultra_tensor_expect_eq`,
  `ultra_tensor_inner_mul`).
* Hilbert's Hotel is strictly impossible (`no_hilbert_hotel_tail`).
* Any two priors matching on a bounded observable basis are indistinguishable on its
  span (`low_degree_indistinguishable`).
-/

namespace BookProof.Ultrafinitism.ChapterUltrafinitistTensor

open scoped BigOperators
open BookProof.Ultrafinitism.ChapterKrawtchoukTail

/-! ## 1. Multi-coordinate finite Gaussian tail -/

/-- A finite tail of `R` independent dyadic Gaussian coordinates of width `M`. -/
abbrev MultiTail (R M : ℕ) := Fin R → BitCube M

/-- Uniform expectation over `MultiTail R M`. -/
def tailExpect (R M : ℕ) (f : MultiTail R M → ℚ) : ℚ :=
  (∑ t : MultiTail R M, f t) / ((2 ^ (R * M) : ℕ) : ℚ)

theorem tailExpect_const (R M : ℕ) (c : ℚ) :
    tailExpect R M (fun _ => c) = c := by
  unfold tailExpect
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fun,
    Fintype.card_bool, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, ← pow_mul]
  have h : ((2 ^ (R * M) : ℕ) : ℚ) ≠ 0 := by positivity
  push_cast
  rw [mul_comm M R]
  field_simp

theorem tailExpect_zero (R M : ℕ) :
    tailExpect R M (fun _ => 0) = 0 := by
  simp [tailExpect]

theorem tailExpect_add (R M : ℕ) (f g : MultiTail R M → ℚ) :
    tailExpect R M (fun t => f t + g t) = tailExpect R M f + tailExpect R M g := by
  simp [tailExpect, Finset.sum_add_distrib, add_div]

theorem tailExpect_smul (R M : ℕ) (c : ℚ) (f : MultiTail R M → ℚ) :
    tailExpect R M (fun t => c * f t) = c * tailExpect R M f := by
  simp [tailExpect, ← Finset.mul_sum, mul_div_assoc]

/-- Splitting `k + R` tail coordinates into `k` coordinates and `R` coordinates. -/
def multiTailSplitEquiv (k R M : ℕ) :
    MultiTail (k + R) M ≃ MultiTail k M × MultiTail R M :=
  (Equiv.piCongrLeft (fun _ : Fin (k + R) => BitCube M)
    (finSumFinEquiv (m := k) (n := R))).symm.trans
    (Equiv.sumArrowEquivProdArrow (Fin k) (Fin R) (BitCube M))

/-- Fubini factorization for splitting `k` coordinates from a finite tail of budget `k + R`. -/
theorem tailExpect_split (k R M : ℕ) (f : MultiTail (k + R) M → ℚ) :
    tailExpect (k + R) M f =
      tailExpect k M (fun t₁ =>
        tailExpect R M (fun t₂ => f ((multiTailSplitEquiv k R M).symm (t₁, t₂)))) := by
  unfold tailExpect
  have hsum : (∑ t : MultiTail (k + R) M, f t) =
      ∑ p : MultiTail k M × MultiTail R M, f ((multiTailSplitEquiv k R M).symm p) := by
    exact (Fintype.sum_equiv (multiTailSplitEquiv k R M).symm _ _ (fun _ => rfl)).symm
  rw [hsum, Fintype.sum_prod_type]
  have hpow : ((2 ^ ((k + R) * M) : ℕ) : ℚ) =
      ((2 ^ (k * M) : ℕ) : ℚ) * ((2 ^ (R * M) : ℕ) : ℚ) := by
    push_cast
    rw [add_mul, pow_add]
  symm
  rw [← Finset.sum_div, div_div, mul_comm ((2 ^ (R * M) : ℕ) : ℚ), ← hpow]

/-! ## 2. Finite head probabilities and exact decoupling -/

/-- An arbitrary probability distribution on a finite head type `X`. -/
structure FiniteProb (X : Type*) [Fintype X] where
  weight : X → ℚ
  nonneg : ∀ x, 0 ≤ weight x
  sum_one : ∑ x, weight x = 1

/-- Product of two independent finite probability distributions. -/
def FiniteProb.prod {X Y : Type*} [Fintype X] [Fintype Y]
    (μ : FiniteProb X) (ν : FiniteProb Y) : FiniteProb (X × Y) where
  weight p := μ.weight p.1 * ν.weight p.2
  nonneg p := mul_nonneg (μ.nonneg p.1) (ν.nonneg p.2)
  sum_one := by
    rw [Fintype.sum_prod_type]
    simp_rw [← Finset.mul_sum, ν.sum_one, mul_one, μ.sum_one]

/-- The uniform tail probability distribution as a `FiniteProb`. -/
def uniformTailProb (R M : ℕ) : FiniteProb (MultiTail R M) where
  weight _ := 1 / ((2 ^ (R * M) : ℕ) : ℚ)
  nonneg _ := by positivity
  sum_one := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fun, Fintype.card_fun,
      Fintype.card_bool, Fintype.card_fin, Fintype.card_fin, nsmul_eq_mul, ← pow_mul]
    have h : ((2 ^ (R * M) : ℕ) : ℚ) ≠ 0 := by positivity
    push_cast
    rw [mul_comm M R]
    field_simp

/-- Expectation on the head–tail product state space `X × MultiTail R M`. -/
def stateExpect {X : Type*} [Fintype X] (μ : FiniteProb X) (R M : ℕ)
    (f : X × MultiTail R M → ℚ) : ℚ :=
  ∑ x : X, μ.weight x * tailExpect R M (fun t => f (x, t))

/-- **Exact decoupling:** inner products of head-only observables eliminate the
`R`-coordinate tail in `O(1)`. -/
theorem ultra_inner_reduces_to_head {X : Type*} [Fintype X]
    (μ : FiniteProb X) (R M : ℕ)
    (f g : X × MultiTail R M → ℚ) (f₀ g₀ : X → ℚ)
    (hf : ∀ z, f z = f₀ z.1) (hg : ∀ z, g z = g₀ z.1) :
    stateExpect μ R M (fun z => f z * g z) = ∑ x : X, μ.weight x * (f₀ x * g₀ x) := by
  unfold stateExpect
  refine Finset.sum_congr rfl fun x _ => ?_
  have hfg : (fun t => f (x, t) * g (x, t)) = fun _ => f₀ x * g₀ x := by
    ext t
    rw [hf (x, t), hg (x, t)]
  rw [hfg, tailExpect_const]

/-! ## 3. Budget-consuming enlargement and resource-accounting tensor product -/

/-- Enlarge the finite head by peeling `k` coordinates out of a tail of budget `k + R`,
leaving a residual tail of budget `R`. -/
def ultraEnlargeEquiv (X : Type*) (k R M : ℕ) :
    X × MultiTail (k + R) M ≃ (X × MultiTail k M) × MultiTail R M where
  toFun z := ((z.1, (multiTailSplitEquiv k R M z.2).1), (multiTailSplitEquiv k R M z.2).2)
  invFun w := (w.1.1, (multiTailSplitEquiv k R M).symm (w.1.2, w.2))
  left_inv z := by simp
  right_inv w := by simp

/-- **Budget-conserving cross-dimensional expectation:** enlarging the head by `k`
Gaussian coordinates leaves expectations unchanged while reducing tail capacity from
`k + R` to `R`. -/
theorem ultra_enlarge_expect_eq {X : Type*} [Fintype X]
    (μ : FiniteProb X) (k R M : ℕ)
    (f : (X × MultiTail k M) × MultiTail R M → ℚ) :
    stateExpect μ (k + R) M (fun z => f (ultraEnlargeEquiv X k R M z)) =
      stateExpect (μ.prod (uniformTailProb k M)) R M f := by
  unfold stateExpect
  have hL : ∀ x : X, tailExpect (k + R) M (fun t => f (ultraEnlargeEquiv X k R M (x, t))) =
      tailExpect k M (fun t₁ => tailExpect R M (fun t₂ => f ((x, t₁), t₂))) := by
    intro x
    rw [tailExpect_split]
    simp [ultraEnlargeEquiv]
  simp_rw [hL]
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x _ => ?_
  unfold tailExpect uniformTailProb FiniteProb.prod
  simp only [div_eq_mul_inv]
  rw [← mul_assoc, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun t₁ _ => ?_
  ring

/-- Combine two systems of tail budgets `R₁` and `R₂` into a single system of
additive tail budget `R₁ + R₂`. -/
def ultraTensorEquiv (X₁ X₂ : Type*) (R₁ R₂ M : ℕ) :
    (X₁ × MultiTail R₁ M) × (X₂ × MultiTail R₂ M) ≃
      (X₁ × X₂) × MultiTail (R₁ + R₂) M where
  toFun p := ((p.1.1, p.2.1), (multiTailSplitEquiv R₁ R₂ M).symm (p.1.2, p.2.2))
  invFun q :=
    ((q.1.1, (multiTailSplitEquiv R₁ R₂ M q.2).1), (q.1.2, (multiTailSplitEquiv R₁ R₂ M q.2).2))
  left_inv p := by simp
  right_inv q := by simp

/-- **Additive-budget tensor expectation.** -/
theorem ultra_tensor_expect_eq {X₁ X₂ : Type*} [Fintype X₁] [Fintype X₂]
    (μ₁ : FiniteProb X₁) (μ₂ : FiniteProb X₂) (R₁ R₂ M : ℕ)
    (f : (X₁ × X₂) × MultiTail (R₁ + R₂) M → ℚ) :
    stateExpect (μ₁.prod μ₂) (R₁ + R₂) M f =
      ∑ x₁ : X₁, ∑ x₂ : X₂, μ₁.weight x₁ * μ₂.weight x₂ *
        tailExpect R₁ M (fun t₁ => tailExpect R₂ M (fun t₂ =>
          f (ultraTensorEquiv X₁ X₂ R₁ R₂ M ((x₁, t₁), (x₂, t₂))))) := by
  unfold stateExpect
  rw [Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun x₁ _ => Finset.sum_congr rfl fun x₂ _ => ?_
  simp only [FiniteProb.prod]
  congr 1
  rw [tailExpect_split]
  simp [ultraTensorEquiv]

/-- **Multiplicativity on pure tensors** over the additive-budget tensor space. -/
theorem ultra_tensor_inner_mul {X₁ X₂ : Type*} [Fintype X₁] [Fintype X₂]
    (μ₁ : FiniteProb X₁) (μ₂ : FiniteProb X₂) (R₁ R₂ M : ℕ)
    (f₁ g₁ : X₁ × MultiTail R₁ M → ℚ) (f₂ g₂ : X₂ × MultiTail R₂ M → ℚ) :
    stateExpect (μ₁.prod μ₂) (R₁ + R₂) M (fun z =>
        let p := (ultraTensorEquiv X₁ X₂ R₁ R₂ M).symm z
        (f₁ p.1 * f₂ p.2) * (g₁ p.1 * g₂ p.2)) =
      stateExpect μ₁ R₁ M (fun z₁ => f₁ z₁ * g₁ z₁) *
        stateExpect μ₂ R₂ M (fun z₂ => f₂ z₂ * g₂ z₂) := by
  rw [ultra_tensor_expect_eq]
  have hinner : ∀ x₁ x₂,
      tailExpect R₁ M (fun t₁ => tailExpect R₂ M (fun t₂ =>
        (f₁ (x₁, t₁) * f₂ (x₂, t₂)) * (g₁ (x₁, t₁) * g₂ (x₂, t₂)))) =
      tailExpect R₁ M (fun t₁ => f₁ (x₁, t₁) * g₁ (x₁, t₁)) *
        tailExpect R₂ M (fun t₂ => f₂ (x₂, t₂) * g₂ (x₂, t₂)) := by
    intro x₁ x₂
    have h1 : ∀ t₁, tailExpect R₂ M (fun t₂ =>
        (f₁ (x₁, t₁) * f₂ (x₂, t₂)) * (g₁ (x₁, t₁) * g₂ (x₂, t₂))) =
        (f₁ (x₁, t₁) * g₁ (x₁, t₁)) *
          tailExpect R₂ M (fun t₂ => f₂ (x₂, t₂) * g₂ (x₂, t₂)) := by
      intro t₁
      have hfac : (fun t₂ => (f₁ (x₁, t₁) * f₂ (x₂, t₂)) * (g₁ (x₁, t₁) * g₂ (x₂, t₂))) =
          fun t₂ => (f₁ (x₁, t₁) * g₁ (x₁, t₁)) * (f₂ (x₂, t₂) * g₂ (x₂, t₂)) := by
        ext t₂; ring
      rw [hfac, tailExpect_smul]
    simp_rw [h1]
    have h2 : (fun t₁ => (f₁ (x₁, t₁) * g₁ (x₁, t₁)) *
        tailExpect R₂ M (fun t₂ => f₂ (x₂, t₂) * g₂ (x₂, t₂))) =
        fun t₁ => tailExpect R₂ M (fun t₂ => f₂ (x₂, t₂) * g₂ (x₂, t₂)) *
          (f₁ (x₁, t₁) * g₁ (x₁, t₁)) := by
      ext t₁; ring
    rw [h2, tailExpect_smul, mul_comm]
  simp only [Equiv.symm_apply_apply]
  simp_rw [hinner]
  unfold stateExpect
  rw [Finset.sum_mul]
  refine Finset.sum_congr rfl fun x₁ _ => ?_
  rw [Finset.mul_sum]
  refine Finset.sum_congr rfl fun x₂ _ => ?_
  ring

/-! ## 4. No Hilbert's Hotel and low-degree indistinguishability -/

/-- **No Hilbert's Hotel:** when `M > 0` and `R₂ > 0`, a finite tail of budget
`R₁ + R₂` is strictly larger than one of budget `R₁`, so no bijection
`MultiTail (R₁ + R₂) M ≃ MultiTail R₁ M` exists. -/
theorem no_hilbert_hotel_tail {R₁ R₂ M : ℕ} (hM : 0 < M) (hR₂ : 0 < R₂) :
    IsEmpty (MultiTail (R₁ + R₂) M ≃ MultiTail R₁ M) := by
  refine ⟨fun e => ?_⟩
  have hcard := Fintype.card_congr e
  simp only [Fintype.card_fun, Fintype.card_bool, Fintype.card_fin, ← pow_mul, mul_comm M] at hcard
  have hlt : R₁ * M < (R₁ + R₂) * M := by
    rw [add_mul]
    exact lt_add_of_pos_right (R₁ * M) (Nat.mul_pos hR₂ hM)
  have hpow := Nat.pow_lt_pow_right (by norm_num : 1 < 2) hlt
  exact absurd hcard hpow.ne'

/-- **Low-degree indistinguishability:** any two finite laws matching on a basis
of bounded-complexity observables `B i` assign identical expectations to every
linear combination of those observables. -/
theorem low_degree_indistinguishable {Ω : Type*} [Fintype Ω]
    (μ₁ μ₂ : FiniteProb Ω) {ι : Type*} [Fintype ι] (B : ι → Ω → ℚ)
    (hmatch : ∀ i, ∑ ω : Ω, μ₁.weight ω * B i ω = ∑ ω : Ω, μ₂.weight ω * B i ω)
    (c : ι → ℚ) :
    (∑ ω : Ω, μ₁.weight ω * ∑ i : ι, c i * B i ω) =
      ∑ ω : Ω, μ₂.weight ω * ∑ i : ι, c i * B i ω := by
  have expand : ∀ μ : FiniteProb Ω,
      (∑ ω : Ω, μ.weight ω * ∑ i : ι, c i * B i ω) =
        ∑ i : ι, c i * ∑ ω : Ω, μ.weight ω * B i ω := by
    intro μ
    simp_rw [Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    refine Finset.sum_congr rfl fun ω _ => by ring
  rw [expand μ₁, expand μ₂]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hmatch i]

end BookProof.Ultrafinitism.ChapterUltrafinitistTensor
