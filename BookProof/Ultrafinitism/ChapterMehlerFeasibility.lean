import BookProof.Ultrafinitism.ChapterKrawtchoukTail
import BookProof.Ultrafinitism.ChapterDeformedCCR
import Mathlib.Data.Matrix.Mul

/-!
# Chapter MehlerFeasibility — Mehler-Damped Effects, Sorites, and Parikh Bounds

Classical bivalent logic (`P² = P`, `BookProof.ChapterStatementOperator.ModelStatement`)
is incompatible with ultrafinitist feasibility because the induction step preserves truth
with zero loss, producing the Sorites paradox.

Here we formalize the finite-dimensional effect logic `FiniteEffect n` (the
ultrafinitist counterpart of `UncertainStatement`) and show that the discrete Mehler
semigroup `T_ρ` (`ρ = 1 - β`) acts as a **graded feasibility operator**:

* `sorites_consistency_theorem` — exact base `1`, local successor stability `≤ β`,
  exponential decay `≤ 1 / (1 + k * β)`, and dissolution below any threshold `ε > 0`
  long before the combinatorial ceiling `M` all hold simultaneously without contradiction.
* `parikh_proof_chain_drift` — quantitative internal Parikh bound: a derivation chain of
  `L` approximate steps of error `≤ β` drifts in truth value by at most `L * β * ‖v‖²`.
* `ultraMul`, `ultraMul_exact_below`, `ultraMul_overflow_moments` — unification of
  `ChapterFiniteArithmeticPrior` with the Krawtchouk–Gaussian tail: exact arithmetic inside
  `[0, B)` and explicit dyadic Gaussian tail uncertainty on overflow.
-/

namespace BookProof.Ultrafinitism.ChapterMehlerFeasibility

open scoped BigOperators Matrix
open BookProof.Ultrafinitism.ChapterKrawtchoukTail

/-! ## 1. Finite-dimensional effect logic -/

/-- Quadratic form `⟨v, A v⟩` on `Fin n → ℝ`. -/
def quadForm {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, v i * (A.mulVec v i)

/-- Squared Euclidean norm `‖v‖²` on `Fin n → ℝ`. -/
def sqNorm {n : ℕ} (v : Fin n → ℝ) : ℝ :=
  ∑ i : Fin n, v i ^ 2

theorem sqNorm_nonneg {n : ℕ} (v : Fin n → ℝ) : 0 ≤ sqNorm v :=
  Finset.sum_nonneg fun _ _ => sq_nonneg _

theorem quadForm_sub {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℝ) (v : Fin n → ℝ) :
    quadForm (A - B) v = quadForm A v - quadForm B v := by
  unfold quadForm
  simp_rw [Matrix.sub_mulVec, Pi.sub_apply, mul_sub, Finset.sum_sub_distrib]

theorem quadForm_one {n : ℕ} (v : Fin n → ℝ) :
    quadForm (1 : Matrix (Fin n) (Fin n) ℝ) v = sqNorm v := by
  unfold quadForm sqNorm
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.one_mulVec, sq]

theorem quadForm_diagonal {n : ℕ} (d : Fin n → ℝ) (v : Fin n → ℝ) :
    quadForm (Matrix.diagonal d) v = ∑ i : Fin n, d i * v i ^ 2 := by
  unfold quadForm
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_diagonal]
  ring

theorem quadForm_single {n : ℕ} (A : Matrix (Fin n) (Fin n) ℝ) (k : Fin n) :
    quadForm A (Pi.single k 1) = A k k := by
  unfold quadForm
  let v : Fin n → ℝ := Pi.single k 1
  change (∑ i : Fin n, v i * (A.mulVec v i)) = A k k
  have hterm : ∀ i : Fin n,
      v i * (A.mulVec v i) = if i = k then A k k else 0 := by
    intro i
    by_cases hik : i = k
    · subst hik
      simp [v, Matrix.mulVec, dotProduct, Pi.single_apply]
    · simp [v, hik]
  simp_rw [hterm]
  simp

/-- A finite-dimensional **effect** (uncertain statement): a symmetric operator `0 ≤ E ≤ I`
on `Fin n → ℝ`. -/
structure FiniteEffect (n : ℕ) where
  op : Matrix (Fin n) (Fin n) ℝ
  symm : opᵀ = op
  nonneg : ∀ v : Fin n → ℝ, 0 ≤ quadForm op v
  le_sqNorm : ∀ v : Fin n → ℝ, quadForm op v ≤ sqNorm v

/-- Truth value of a `FiniteEffect` on a model vector `v`. -/
def FiniteEffect.truthVal {n : ℕ} (E : FiniteEffect n) (v : Fin n → ℝ) : ℝ :=
  quadForm E.op v

theorem FiniteEffect.truthVal_nonneg {n : ℕ} (E : FiniteEffect n) (v : Fin n → ℝ) :
    0 ≤ E.truthVal v :=
  E.nonneg v

theorem FiniteEffect.truthVal_le_sqNorm {n : ℕ} (E : FiniteEffect n) (v : Fin n → ℝ) :
    E.truthVal v ≤ sqNorm v :=
  E.le_sqNorm v

/-- Negation `I - E` of a finite effect. -/
def FiniteEffect.not {n : ℕ} (E : FiniteEffect n) : FiniteEffect n where
  op := 1 - E.op
  symm := by rw [Matrix.transpose_sub, Matrix.transpose_one, E.symm]
  nonneg v := by
    rw [quadForm_sub, quadForm_one]
    exact sub_nonneg.mpr (E.le_sqNorm v)
  le_sqNorm v := by
    rw [quadForm_sub, quadForm_one]
    linarith [E.nonneg v]

theorem FiniteEffect.truthVal_not {n : ℕ} (E : FiniteEffect n) (v : Fin n → ℝ) :
    E.not.truthVal v = sqNorm v - E.truthVal v := by
  simp [FiniteEffect.truthVal, FiniteEffect.not, quadForm_sub, quadForm_one]

/-- Finite-dimensional counterpart of `ChapterStatementOperator.approximate_proof_error`. -/
theorem finite_approximate_proof_error {n : ℕ} (A P : FiniteEffect n) (ε : ℝ)
    (h : ∀ v : Fin n → ℝ, |quadForm (A.op - P.op) v| ≤ ε * sqNorm v)
    (v : Fin n → ℝ) :
    |A.truthVal v - P.truthVal v| ≤ ε * sqNorm v := by
  change |quadForm A.op v - quadForm P.op v| ≤ ε * sqNorm v
  rw [← quadForm_sub]
  exact h v

/-! ## 2. Mehler-damped feasibility and the Sorites consistency theorem -/

/-- The discrete Mehler semigroup `T_ρ` (`0 ≤ ρ ≤ 1`) as a `FiniteEffect` on the
`(M + 1)`-dimensional Krawtchouk degree space. -/
def mehlerFeasEffect (M : ℕ) (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    FiniteEffect (M + 1) where
  op := Matrix.diagonal (fun k : Fin (M + 1) => ρ ^ (k : ℕ))
  symm := Matrix.diagonal_transpose _
  nonneg v := by
    rw [quadForm_diagonal]
    exact Finset.sum_nonneg fun k _ => mul_nonneg (pow_nonneg h0 _) (sq_nonneg _)
  le_sqNorm v := by
    rw [quadForm_diagonal, sqNorm]
    refine Finset.sum_le_sum fun k _ => ?_
    have hle : ρ ^ (k : ℕ) ≤ 1 := pow_le_one₀ h0 h1
    nlinarith [sq_nonneg (v k)]

theorem mehlerFeas_grade (M : ℕ) (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1)
    (k : Fin (M + 1)) :
    (mehlerFeasEffect M ρ h0 h1).truthVal (Pi.single k 1) = ρ ^ (k : ℕ) := by
  simp [FiniteEffect.truthVal, mehlerFeasEffect, quadForm_single]

theorem mehlerFeas_zero (M : ℕ) (ρ : ℝ) (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) :
    (mehlerFeasEffect M ρ h0 h1).truthVal (Pi.single ⟨0, Nat.succ_pos M⟩ 1) = 1 := by
  rw [mehlerFeas_grade]
  simp

theorem mehlerFeas_successor_stable {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (n : ℕ) :
    |ρ ^ (n + 1) - ρ ^ n| ≤ 1 - ρ := by
  have hle : ρ ^ (n + 1) ≤ ρ ^ n := by
    rw [pow_succ]
    exact mul_le_of_le_one_right (pow_nonneg h0 n) h1
  rw [abs_of_nonpos (sub_nonpos.mpr hle)]
  have hfac : -(ρ ^ (n + 1) - ρ ^ n) = ρ ^ n * (1 - ρ) := by
    rw [pow_succ]; ring
  rw [hfac]
  exact mul_le_of_le_one_left (sub_nonneg.mpr h1) (pow_le_one₀ h0 h1)

theorem mehlerFeas_tensor_mul (ρ : ℝ) (n₁ n₂ : ℕ) :
    ρ ^ (n₁ + n₂) = ρ ^ n₁ * ρ ^ n₂ :=
  pow_add ρ n₁ n₂

private theorem bernoulli_ineq {β : ℝ} (h0 : 0 ≤ β) (n : ℕ) :
    1 + (n : ℝ) * β ≤ (1 + β) ^ n := by
  induction n with
  | zero => simp
  | succ n ih =>
    have h1 : 0 ≤ (1 + β) := by linarith
    have hmul : (1 + (n : ℝ) * β) * (1 + β) ≤ (1 + β) ^ n * (1 + β) :=
      mul_le_mul_of_nonneg_right ih h1
    have hsq : 0 ≤ (n : ℝ) * β ^ 2 := by positivity
    rw [pow_succ]
    push_cast
    linarith

/-- Quantitative decay `(1 - β)^n ≤ 1 / (1 + n * β)` for `0 ≤ β < 1`. -/
theorem one_sub_pow_le_inv {β : ℝ} (h0 : 0 ≤ β) (h1 : β < 1) (n : ℕ) :
    (1 - β) ^ n ≤ 1 / (1 + (n : ℝ) * β) := by
  have hpos : 0 < 1 + (n : ℝ) * β := by positivity
  rw [le_div_iff₀ hpos]
  have hprod : (1 - β) * (1 + β) ≤ 1 := by nlinarith
  have hpow : ((1 - β) * (1 + β)) ^ n ≤ 1 :=
    pow_le_one₀ (mul_nonneg (sub_nonneg.mpr h1.le) (by linarith)) hprod
  rw [mul_pow] at hpow
  have hbern := bernoulli_ineq h0 n
  have hmul : (1 - β) ^ n * (1 + (n : ℝ) * β) ≤ (1 - β) ^ n * (1 + β) ^ n :=
    mul_le_mul_of_nonneg_left hbern (pow_nonneg (sub_nonneg.mpr h1.le) n)
  exact hmul.trans hpow

/-- **Sorites Consistency Theorem for Mehler-Damped Feasibility:**
for any combinatorial horizon `M` and step dissipation `0 < β < 1`, the effect
`mehlerFeasEffect M (1 - β)` simultaneously satisfies:
1. exact base `1` at grade `0`;
2. local successor stability `≤ β` at every step `n < M`;
3. uniform inverse-linear decay `≤ 1 / (1 + k * β)`;
4. smooth dissolution below any `ε > 0` once `k ≥ (1 / ε - 1) / β`. -/
theorem sorites_consistency_theorem (M : ℕ) {β : ℝ} (h0 : 0 < β) (h1 : β < 1) :
    let F := mehlerFeasEffect M (1 - β) (by linarith) (by linarith)
    F.truthVal (Pi.single ⟨0, Nat.succ_pos M⟩ 1) = 1 ∧
      (∀ (n : ℕ) (hn : n < M),
        |F.truthVal (Pi.single ⟨n + 1, by omega⟩ 1) -
            F.truthVal (Pi.single ⟨n, by omega⟩ 1)| ≤ β) ∧
      (∀ k : Fin (M + 1), F.truthVal (Pi.single k 1) ≤ 1 / (1 + (k : ℝ) * β)) ∧
      (∀ (ε : ℝ), 0 < ε → ∀ k : Fin (M + 1),
        (1 / ε - 1) / β ≤ (k : ℝ) → F.truthVal (Pi.single k 1) ≤ ε) := by
  intro F
  refine ⟨mehlerFeas_zero M (1 - β) (by linarith) (by linarith), ?_, ?_, ?_⟩
  · intro n hn
    rw [mehlerFeas_grade, mehlerFeas_grade]
    simpa using mehlerFeas_successor_stable (ρ := 1 - β) (by linarith) (by linarith) n
  · intro k
    rw [mehlerFeas_grade]
    exact one_sub_pow_le_inv h0.le h1 (k : ℕ)
  · intro ε hε k hk
    have hk' : 1 / ε ≤ 1 + (k : ℝ) * β := by
      have := (div_le_iff₀ h0).mp hk
      linarith
    have hdec := one_sub_pow_le_inv h0.le h1 (k : ℕ)
    have hdiv : 1 / (1 + (k : ℝ) * β) ≤ ε := by
      have hpos : 0 < 1 + (k : ℝ) * β := by positivity
      rw [div_le_iff₀ hpos]
      have h1e : 1 ≤ ε * (1 + (k : ℝ) * β) := by
        have := mul_le_mul_of_nonneg_left hk' hε.le
        rwa [mul_one_div_cancel hε.ne'] at this
      linarith
    rw [mehlerFeas_grade]
    exact hdec.trans hdiv

/-! ## 3. Internal quantitative Parikh proof-length bound -/

/-- **Internal Parikh Bound:** across a derivation chain of `L` steps, each with
operator-difference error `≤ β`, total truth-value drift is at most `L * β * ‖v‖²`. -/
theorem parikh_proof_chain_drift {n : ℕ} (L : ℕ) (chain : Fin (L + 1) → FiniteEffect n)
    (β : ℝ)
    (hstep : ∀ i : Fin L, ∀ v : Fin n → ℝ,
      |quadForm ((chain i.succ).op - (chain i.castSucc).op) v| ≤ β * sqNorm v)
    (v : Fin n → ℝ) :
    |(chain (Fin.last L)).truthVal v - (chain 0).truthVal v| ≤
      (L : ℝ) * β * sqNorm v := by
  induction L with
  | zero => simp
  | succ L ih =>
    let chain' : Fin (L + 1) → FiniteEffect n := fun i => chain i.castSucc
    have hstep' : ∀ i : Fin L, ∀ w : Fin n → ℝ,
        |quadForm ((chain' i.succ).op - (chain' i.castSucc).op) w| ≤ β * sqNorm w := by
      intro i w
      exact hstep i.castSucc w
    have ihL := ih chain' hstep'
    have hlast : |(chain (Fin.last (L + 1))).truthVal v -
        (chain (Fin.last L).castSucc).truthVal v| ≤ β * sqNorm v := by
      have h := hstep (Fin.last L) v
      have heq1 : (Fin.last L).succ = Fin.last (L + 1) := by
        ext; simp
      rw [heq1] at h
      simpa [FiniteEffect.truthVal, quadForm_sub] using h
    have h0 : (chain' 0).truthVal v = (chain 0).truthVal v := rfl
    have hL : (chain' (Fin.last L)).truthVal v = (chain (Fin.last L).castSucc).truthVal v := rfl
    rw [h0, hL] at ihL
    have htri : |(chain (Fin.last (L + 1))).truthVal v - (chain 0).truthVal v| ≤
        |(chain (Fin.last (L + 1))).truthVal v - (chain (Fin.last L).castSucc).truthVal v| +
          |(chain (Fin.last L).castSucc).truthVal v - (chain 0).truthVal v| :=
      abs_sub_le _ _ _
    have hcomb := htri.trans (add_le_add hlast ihL)
    push_cast
    linarith

/-! ## 4. Unified horizon-bounded arithmetic with Gaussian tail uncertainty -/

/-- Outcome of an ultrafinitist arithmetic operation with exact table bound `B` and
Krawtchouk–Gaussian overflow tail of width `M`: either an exact representable value `< B`,
or an explicit tail prior model on `BitCube M`. -/
inductive UltraArithResult (B M : ℕ) where
  | exact (val : Fin B)
  | tailOverflow (mean scale : ℚ) (tailPrior : BitCube M → ℚ)

/-- Horizon-bounded multiplication returning an exact `Fin B` result when `a * b < B`,
and transitioning to the dyadic Krawtchouk–Gaussian tail `dyadicGauss q` on overflow. -/
def ultraMul (B q : ℕ) (a b : Fin B) : UltraArithResult B (4 ^ q) :=
  if h : (a : ℕ) * (b : ℕ) < B then
    UltraArithResult.exact ⟨(a : ℕ) * (b : ℕ), h⟩
  else
    UltraArithResult.tailOverflow ((a : ℕ) * (b : ℕ)) 1 (dyadicGauss q)

theorem ultraMul_exact_below {B q : ℕ} (a b : Fin B) (h : (a : ℕ) * (b : ℕ) < B) :
    ultraMul B q a b = UltraArithResult.exact ⟨(a : ℕ) * (b : ℕ), h⟩ := by
  simp [ultraMul, h]

theorem ultraMul_overflow_moments {B q : ℕ} (a b : Fin B) (h : ¬ (a : ℕ) * (b : ℕ) < B) :
    ∃ (mean scale : ℚ) (tailPrior : BitCube (4 ^ q) → ℚ),
      ultraMul B q a b = UltraArithResult.tailOverflow mean scale tailPrior ∧
        cubeExpect (4 ^ q) tailPrior = 0 ∧
        cubeExpect (4 ^ q) (fun x => tailPrior x ^ 2) = 1 := by
  refine ⟨(a : ℕ) * (b : ℕ), 1, dyadicGauss q, ?_, dyadicGauss_mean q,
    dyadicGauss_variance q⟩
  simp [ultraMul, h]

end BookProof.Ultrafinitism.ChapterMehlerFeasibility
