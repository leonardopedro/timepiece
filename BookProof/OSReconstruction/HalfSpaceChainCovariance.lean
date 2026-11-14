import Mathlib
import BookProof.OSReconstruction.HalfSpaceCovariancePushforward

/-!
# A banded covariance on an `n`-site chain

Plan: `cftproof.md`, **E3**, continuation of `HalfSpaceCovariancePushforward`, which builds the
non-diagonal covariance `[[1, ρ], [ρ, 1]]` on **two** sites.  This module extends it to an `n`-site
chain and shows that the resulting covariance is **banded** (a width-`1` band on the cycle) and
**Hilbert–Schmidt**.

The construction is additive-neighbour: with `σ` a permutation of the site set and `X` white noise,
the state is the law of

  `Y i = X i + ρ · X (σ i)`

i.e. the pushforward of `whiteNoise` along the band matrix `1 + ρ·P_σ`.  Its covariance is

  `Cov(Y i, Y j) = δ_{ij} + ρ (δ_{σ i, j} + δ_{i, σ j}) + ρ² δ_{ij}`

which is `1 + ρ²` on the diagonal and `ρ` exactly for *neighbouring* sites `j = σ i` or
`j = σ⁻¹ i`, and `0` for all other pairs: a banded Toeplitz-type matrix.  Restricting further to the
cycle `σ = finRotate (n+1)` with `n ≥ 2` (all cycles of length `≥ 3`) makes the three special
entries of every row distinct, and the squared Hilbert–Schmidt norm is
`(n+1) · ((1+ρ²)² + 2ρ²)`.

## Contents

* `whiteNoise` — the `n`-site reference law (independent unit Gaussians), with
  `integral_eval`, `integral_eval_sq`, `memLp_eval`, `covariance_eval_eval`;
* `chainMap`, `chainLaw` — **the band matrix and the pushforward state**;
* `chainCov` — the covariance matrix `δ + ρ(shift + shiftᵀ) + ρ²δ`, with
  `chainCov_diag`, `chainCov_neighbour_left`, `chainCov_neighbour_right`,
  **`chainCov_eq_zero`** (bandedness: every non-neighbour entry vanishes);
* **`chainLaw_cov`** — the state has exactly that covariance;
* **`chainCov_hsNormSq`** — the covariance is Hilbert–Schmidt, with squared HS norm
  `card ι · ((1+ρ²)² + 2ρ²)` when `σ` has no cycles of length `≤ 2`;
* `cycleShift`, `cycleChain`, `cycleChain_cov_hsNormSq` — the concrete `n`-site cycle.

## Boundary

* The matrix is banded but **not** `(−Δ+m²)⁻¹`: the inverse of a chain Laplacian is dense, so a
  banded covariance is the nearest-neighbour *truncation*, not the exact massive free-field
  covariance.  Only the two-site truncation is exact — see
  `HalfSpaceCovariancePushforward.covMatrix_eq_lapInv`.
* The construction is a one-step band: no second-neighbour terms, no interaction.
* `chainCov_hsNormSq` needs every cycle of `σ` to have length `≥ 3`.  What it uses is "no fixed
  point and no 2-cycle", which is what makes the three special entries of a row distinct; for
  `σ = finRotate (n+1)` this is `2 ≤ n`.
-/

namespace BookProof.OSReconstruction

open MeasureTheory ProbabilityTheory
open scoped BigOperators

noncomputable section

/-! ## The reference white noise -/

/-- **`n`-site white noise**: independent unit Gaussians on `ι → ℝ`. -/
def whiteNoise (ι : Type*) [Fintype ι] : Measure (ι → ℝ) :=
  Measure.pi (fun _ : ι => gaussianReal 0 1)

instance whiteNoise_isProbability (ι : Type*) [Fintype ι] :
    IsProbabilityMeasure (whiteNoise ι) := by
  unfold whiteNoise
  infer_instance

theorem measurable_eval {ι : Type*} (i : ι) : Measurable fun p : ι → ℝ => p i :=
  measurable_pi_apply i

/-- The mean of a coordinate of white noise is zero. -/
theorem integral_eval {ι : Type*} [Fintype ι] (i : ι) :
    ∫ p : ι → ℝ, p i ∂whiteNoise ι = 0 := by
  rw [whiteNoise, integral_comp_eval (μ := fun _ : ι => gaussianReal 0 1)
    (f := fun x : ℝ => x) (by fun_prop)]
  exact integral_id_gaussianReal

/-- The second moment of a coordinate of white noise is one. -/
theorem integral_eval_sq {ι : Type*} [Fintype ι] (i : ι) :
    ∫ p : ι → ℝ, p i ^ 2 ∂whiteNoise ι = 1 := by
  rw [whiteNoise, integral_comp_eval (μ := fun _ : ι => gaussianReal 0 1)
    (f := fun x : ℝ => x ^ 2) (by fun_prop)]
  exact integral_sq_gaussUnit

theorem memLp_eval {ι : Type*} [Fintype ι] (i : ι) :
    MemLp (fun p : ι → ℝ => p i) 2 (whiteNoise ι) := by
  rw [whiteNoise]
  exact (memLp_id_gaussianReal (μ := 0) (v := 1) 2).comp_measurePreserving
    (measurePreserving_eval (μ := fun _ : ι => gaussianReal 0 1) i)

theorem integrable_eval_sq {ι : Type*} [Fintype ι] (i : ι) :
    Integrable (fun p : ι → ℝ => p i ^ 2) (whiteNoise ι) :=
  (memLp_eval i).integrable_sq

/-- **The coordinates of white noise are uncorrelated**: `Cov(p i, p j) = δ_{ij}`. -/
theorem covariance_eval_eval {ι : Type*} [Fintype ι] [DecidableEq ι] (i j : ι) :
    cov[fun p : ι → ℝ => p i, fun p : ι → ℝ => p j; whiteNoise ι]
      = if i = j then 1 else 0 := by
  classical
  by_cases h : i = j
  · subst h
    rw [if_pos rfl, covariance_self (memLp_eval i).aemeasurable,
      variance_eq_integral (memLp_eval i).aemeasurable, integral_eval i]
    simpa using integral_eval_sq i
  · rw [if_neg h]
    have hind : iIndepFun (fun (k : ι) (p : ι → ℝ) => p k) (whiteNoise ι) := by
      change iIndepFun (fun (k : ι) (p : ι → ℝ) => p k)
        (Measure.pi fun _ : ι => gaussianReal 0 1)
      exact iIndepFun_pi (mX := fun _ => aemeasurable_id)
    exact (hind.indepFun h).covariance_eq_zero (memLp_eval i) (memLp_eval j)

/-! ## The band matrix and the chain state -/

/-- **The band matrix**: `p ↦ fun i => p i + ρ p (σ i)`. -/
def chainMap {ι : Type*} (σ : Equiv.Perm ι) (ρ : ℝ) : (ι → ℝ) → (ι → ℝ) :=
  fun p i => p i + ρ * p (σ i)

theorem measurable_chainMap {ι : Type*} (σ : Equiv.Perm ι) (ρ : ℝ) :
    Measurable (chainMap σ ρ) := by
  refine measurable_pi_lambda _ fun i => ?_
  have h1 : Measurable fun p : ι → ℝ => p i := measurable_pi_apply i
  have h2 : Measurable fun p : ι → ℝ => p (σ i) := measurable_pi_apply (σ i)
  exact h1.add (h2.const_mul ρ)

/-- **The chain state**: white noise pushed forward by the band matrix. -/
def chainLaw {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (ρ : ℝ) : Measure (ι → ℝ) :=
  (whiteNoise ι).map (chainMap σ ρ)

instance chainLaw_isProbability {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (ρ : ℝ) :
    IsProbabilityMeasure (chainLaw σ ρ) := by
  unfold chainLaw
  exact Measure.isProbabilityMeasure_map (measurable_chainMap σ ρ).aemeasurable

/-- The `i`-th coordinate of the chain state, read on the white noise. -/
def chainModel {ι : Type*} (σ : Equiv.Perm ι) (ρ : ℝ) (i : ι) : (ι → ℝ) → ℝ :=
  fun p => p i + ρ * p (σ i)

theorem chainModel_eq_add {ι : Type*} (σ : Equiv.Perm ι) (ρ : ℝ) (i : ι) :
    chainModel σ ρ i = (fun p : ι → ℝ => p i) + fun p : ι → ℝ => ρ * p (σ i) := rfl

theorem memLp_chainModel {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (ρ : ℝ) (i : ι) :
    MemLp (chainModel σ ρ i) 2 (whiteNoise ι) :=
  (memLp_eval i).add ((memLp_eval (σ i)).const_mul ρ)

/-- Expansion of the covariance of a sum of two pairs. -/
theorem covariance_add_add {ι : Type*} [Fintype ι] (a b c d : (ι → ℝ) → ℝ)
    (ha : MemLp a 2 (whiteNoise ι)) (hb : MemLp b 2 (whiteNoise ι))
    (hc : MemLp c 2 (whiteNoise ι)) (hd : MemLp d 2 (whiteNoise ι)) :
    cov[a + c, b + d; whiteNoise ι]
      = cov[a, b; whiteNoise ι] + cov[a, d; whiteNoise ι]
        + cov[c, b; whiteNoise ι] + cov[c, d; whiteNoise ι] := by
  rw [covariance_add_left ha hc (hb.add hd), covariance_add_right ha hb hd,
    covariance_add_right hc hb hd]
  ring

/-! ## The covariance matrix -/

/-- **The covariance matrix of the chain**: `δ_{ij} + ρ (δ_{σ i, j} + δ_{i, σ j}) + ρ² δ_{ij}`. -/
def chainCov {ι : Type*} (σ : Equiv.Perm ι) (ρ : ℝ) (i j : ι) : ℝ := by
  classical
  exact (if i = j then 1 else 0)
    + ρ * ((if σ i = j then 1 else 0) + (if i = σ j then 1 else 0))
    + ρ ^ 2 * (if i = j then 1 else 0)

/-- The covariance of the chain state is the explicit banded matrix. -/
theorem chainLaw_cov {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (ρ : ℝ) (i j : ι) :
    cov[fun z : ι → ℝ => z i, fun z : ι → ℝ => z j; chainLaw σ ρ] = chainCov σ ρ i j := by
  classical
  rw [chainLaw, covariance_map (Z := chainMap σ ρ)
    (Measurable.aestronglyMeasurable (measurable_eval i))
    (Measurable.aestronglyMeasurable (measurable_eval j))
    (measurable_chainMap σ ρ).aemeasurable]
  have hcomp : (fun z : ι → ℝ => z i) ∘ chainMap σ ρ = chainModel σ ρ i := rfl
  have hcomp' : (fun z : ι → ℝ => z j) ∘ chainMap σ ρ = chainModel σ ρ j := rfl
  rw [hcomp, hcomp', chainModel_eq_add, chainModel_eq_add]
  rw [covariance_add_add (fun p : ι → ℝ => p i) (fun p : ι → ℝ => p j)
    (fun p : ι → ℝ => ρ * p (σ i)) (fun p : ι → ℝ => ρ * p (σ j))
    (memLp_eval i) (memLp_eval j) ((memLp_eval (σ i)).const_mul ρ)
    ((memLp_eval (σ j)).const_mul ρ)]
  simp only [covariance_const_mul_left, covariance_const_mul_right, covariance_eval_eval]
  have hρ2 : ρ * (ρ * (if σ i = σ j then (1 : ℝ) else 0))
      = ρ ^ 2 * (if i = j then 1 else 0) := by
    by_cases h : i = j
    · subst h
      simp
      ring
    · have h' : σ i ≠ σ j := fun hh => h (σ.injective hh)
      simp [h, h']
  rw [hρ2]
  unfold chainCov
  ring

/-! ## Bandedness and the Hilbert–Schmidt norm -/

/-- **The diagonal entry**: `1 + ρ²` (when `σ` has no fixed point). -/
theorem chainCov_diag {ι : Type*} (σ : Equiv.Perm ι) (ρ : ℝ) (hσ : ∀ i, σ i ≠ i) (i : ι) :
    chainCov σ ρ i i = 1 + ρ ^ 2 := by
  classical
  unfold chainCov
  rw [if_pos rfl, if_neg (hσ i), if_neg (Ne.symm (hσ i))]
  ring

/-- **The `σ`-neighbour entry** is `ρ`. -/
theorem chainCov_neighbour_right {ι : Type*} (σ : Equiv.Perm ι) (ρ : ℝ)
    (hσ : ∀ i, σ i ≠ i) (hσ2 : ∀ i, σ i ≠ σ.symm i) (i : ι) :
    chainCov σ ρ i (σ i) = ρ := by
  classical
  have h1 : i ≠ σ i := (hσ i).symm
  have h2 : i ≠ σ (σ i) := by
    intro h
    have hsym : σ.symm i = σ i := by
      have := congrArg σ.symm h
      simpa using this
    exact hσ2 i hsym.symm
  unfold chainCov
  rw [if_neg h1, if_pos rfl, if_neg h2]
  ring

/-- **The `σ⁻¹`-neighbour entry** is `ρ`. -/
theorem chainCov_neighbour_left {ι : Type*} (σ : Equiv.Perm ι) (ρ : ℝ)
    (hσ : ∀ i, σ i ≠ i) (hσ2 : ∀ i, σ i ≠ σ.symm i) (i : ι) :
    chainCov σ ρ i (σ.symm i) = ρ := by
  classical
  have h1 : i ≠ σ.symm i := by
    intro h
    refine hσ i ?_
    calc σ i = σ (σ.symm i) := (congrArg σ h.symm).symm
      _ = i := Equiv.apply_symm_apply σ i
  have h3 : i = σ (σ.symm i) := by simp
  unfold chainCov
  rw [if_neg h1, if_neg (hσ2 i), if_pos h3]
  ring

/-- **Bandedness**: every entry off the star `{i, σ i, σ⁻¹ i}` vanishes. -/
theorem chainCov_eq_zero {ι : Type*} (σ : Equiv.Perm ι) (ρ : ℝ) {i j : ι}
    (h1 : j ≠ i) (h2 : j ≠ σ i) (h3 : j ≠ σ.symm i) : chainCov σ ρ i j = 0 := by
  classical
  have h4 : σ j ≠ i := by
    intro h
    refine h3 ?_
    rw [← h, Equiv.symm_apply_apply]
  unfold chainCov
  rw [if_neg (Ne.symm h1), if_neg (Ne.symm h2), if_neg (Ne.symm h4)]
  ring

/-- The three special sites of a row are distinct when `σ` has no cycle of length `≤ 2`. -/
theorem chainCov_row_sum {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (ρ : ℝ)
    (hσ : ∀ i, σ i ≠ i) (hσ2 : ∀ i, σ i ≠ σ.symm i) (i : ι) :
    (∑ j, chainCov σ ρ i j ^ 2) = (1 + ρ ^ 2) ^ 2 + ρ ^ 2 + ρ ^ 2 := by
  classical
  have hAi : i ≠ σ i := (hσ i).symm
  have hAC : i ≠ σ.symm i := by
    intro h
    refine hσ i ?_
    calc σ i = σ (σ.symm i) := (congrArg σ h.symm).symm
      _ = i := Equiv.apply_symm_apply σ i
  have hBC : σ i ≠ σ.symm i := hσ2 i
  have hzero : ∀ j ∈ (Finset.univ : Finset ι),
      j ∉ ({i, σ i, σ.symm i} : Finset ι) → chainCov σ ρ i j ^ 2 = 0 := by
    intro j _ hj
    simp only [Finset.mem_insert, Finset.mem_singleton, not_or] at hj
    rw [chainCov_eq_zero σ ρ hj.1 hj.2.1 hj.2.2]
    ring
  rw [← Finset.sum_subset (Finset.subset_univ _) hzero]
  rw [Finset.sum_insert (by simp [hAi, hAC]), Finset.sum_insert (by simp [hBC]),
    Finset.sum_singleton, chainCov_diag σ ρ hσ i,
    chainCov_neighbour_right σ ρ hσ hσ2 i, chainCov_neighbour_left σ ρ hσ hσ2 i]
  ring

/-- **The covariance is Hilbert–Schmidt**: its squared HS norm is `card ι · ((1+ρ²)² + 2ρ²)`. -/
theorem chainCov_hsNormSq {ι : Type*} [Fintype ι] (σ : Equiv.Perm ι) (ρ : ℝ)
    (hσ : ∀ i, σ i ≠ i) (hσ2 : ∀ i, σ i ≠ σ.symm i) :
    ∑ i, ∑ j, chainCov σ ρ i j ^ 2
      = (Fintype.card ι : ℝ) * ((1 + ρ ^ 2) ^ 2 + 2 * ρ ^ 2) := by
  simp only [chainCov_row_sum σ ρ hσ hσ2]
  rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  ring

/-! ## The concrete `n`-site cycle -/

/-- The shift of the `(n+1)`-site cycle: rotation by one site. -/
def cycleShift (n : ℕ) : Equiv.Perm (Fin (n + 1)) := finRotate (n + 1)

/-- **The `(n+1)`-site cyclic chain state** with banded covariance. -/
def cycleChain (n : ℕ) (ρ : ℝ) : Measure (Fin (n + 1) → ℝ) :=
  chainLaw (cycleShift n) ρ

instance cycleChain_isProbability (n : ℕ) (ρ : ℝ) : IsProbabilityMeasure (cycleChain n ρ) := by
  unfold cycleChain
  infer_instance

theorem cycleShift_apply (n : ℕ) (i : Fin (n + 1)) : cycleShift n i = i + 1 :=
  finRotate_succ_apply i

theorem cycleShift_symm_apply (n : ℕ) (i : Fin (n + 1)) : (cycleShift n).symm i = i - 1 :=
  finRotate_succ_symm_apply i

/-- The cyclic shift has no fixed point as soon as the cycle has at least two sites. -/
theorem cycleShift_ne_self (n : ℕ) (hn : 1 ≤ n) (i : Fin (n + 1)) : cycleShift n i ≠ i := by
  rw [cycleShift_apply]
  intro h
  have hv := congrArg Fin.val h
  rw [Fin.val_add_one] at hv
  split_ifs at hv with hlast
  · subst hlast
    simp at hv
    omega
  · omega

/-- No site is sent to its own predecessor once the cycle has at least three sites. -/
theorem cycleShift_ne_symm (n : ℕ) (hn : 2 ≤ n) (i : Fin (n + 1)) :
    cycleShift n i ≠ (cycleShift n).symm i := by
  rw [cycleShift_apply, cycleShift_symm_apply]
  intro h
  have hv := congrArg Fin.val h
  rw [Fin.val_add_one] at hv
  have hlast : ((0 : Fin (n + 1)) - 1) = Fin.last n := by
    rw [zero_sub]
    calc (-1 : Fin (n + 1)) = -(-Fin.last n) := by rw [Fin.neg_last]
      _ = Fin.last n := neg_neg _
  by_cases h0 : i = 0
  · subst h0
    rw [hlast] at hv
    simp only [Fin.val_zero, Fin.val_last, zero_add] at hv
    by_cases hLn : (0 : Fin (n + 1)) = Fin.last n
    · rw [if_pos hLn] at hv
      omega
    · rw [if_neg hLn] at hv
      omega
  · rw [Fin.val_sub_one_of_ne_zero h0] at hv
    split_ifs at hv with hlast2
    · subst hlast2
      simp at hv
      omega
    · omega

/-- **The cyclic `(n+1)`-site covariance is banded and Hilbert–Schmidt**, with squared HS norm
`(n+1) · ((1+ρ²)² + 2ρ²)`. -/
theorem cycleChain_cov_hsNormSq (n : ℕ) (hn : 2 ≤ n) (ρ : ℝ) :
    ∑ i : Fin (n + 1), ∑ j : Fin (n + 1),
        cov[fun z : Fin (n + 1) → ℝ => z i, fun z : Fin (n + 1) → ℝ => z j;
          cycleChain n ρ] ^ 2
      = ((n : ℝ) + 1) * ((1 + ρ ^ 2) ^ 2 + 2 * ρ ^ 2) := by
  have hcov : ∀ i j : Fin (n + 1),
      cov[fun z : Fin (n + 1) → ℝ => z i, fun z : Fin (n + 1) → ℝ => z j; cycleChain n ρ]
        = chainCov (cycleShift n) ρ i j := fun i j => chainLaw_cov (cycleShift n) ρ i j
  simp only [hcov]
  rw [chainCov_hsNormSq (cycleShift n) ρ (cycleShift_ne_self n (by omega))
    (cycleShift_ne_symm n hn)]
  norm_num [Fintype.card_fin]

/-- The cyclic covariance vanishes off the band `{i, σ i, σ⁻¹ i}`. -/
theorem cycleChain_cov_eq_zero (n : ℕ) (ρ : ℝ) {i j : Fin (n + 1)}
    (h1 : j ≠ i) (h2 : j ≠ cycleShift n i) (h3 : j ≠ (cycleShift n).symm i) :
    cov[fun z : Fin (n + 1) → ℝ => z i, fun z : Fin (n + 1) → ℝ => z j; cycleChain n ρ] = 0 := by
  unfold cycleChain
  rw [chainLaw_cov (cycleShift n) ρ i j]
  exact chainCov_eq_zero (cycleShift n) ρ h1 h2 h3

end

end BookProof.OSReconstruction
