import Mathlib
import BookProof.ReflectionPositivity.LatticeFreeField

/-!
# The normalising constant of the lattice free field

`BookProof.ReflectionPositivity.LatticeFreeField` proves that `latticeGFFMeasure m` — the Gibbs
measure `volume.withDensity (exp(−S))` of the free field on `2n + 1` slices — is exactly the
Feynman–Kac form `ρ ⊗ ν_z ⊗ ν_z`, and that its OS form is a square.  Reflection positivity is
invariant under a positive rescaling, so it never needed the partition function.  *Being a
probability measure* does:

```
Z(m, n) = ∫ exp(−S) dφ,        ν = Z⁻¹ · latticeGFFMeasure m.
```

This chapter evaluates what can be evaluated of `Z`, and shows that the bounds suffice for `ν` to
be a probability measure.

## Contents

* `sqSum`, `layerSq`, `latticeSq` — the squared norms `‖x‖² = Σ xᵢ²` of a slice, a half-space and a
  whole lattice configuration, i.e. the quadratic form of the *mass* term;
* **`integral_exp_neg_mul_sqSum`** — the reference Gaussian integral on `|S|` sites,
  `∫_{ℝ^S} exp(−c‖x‖²) dx = (√(π/c))^{|S|}`.  Fubini over the sites
  (`integral_fintype_prod_eq_pow`) plus the one-dimensional `integral_gaussian`; this is where the
  `π`'s come from;
* **`integral_exp_neg_mul_layerSq`**, **`integral_exp_neg_mul_latticeSq`** — the same over a stack
  of `n` slices and over the full configuration space: `∫ exp(−c‖φ‖²) = (√(π/c))^{(2n+1)|S|}`;
* **`latticeAction_ge_mass`** — the action dominates its mass term, `S ≥ (m/2)‖φ‖²` (the gradient
  terms are squares);
* **`latticeAction_le`** — and is dominated by `(4·2n + m/2)‖φ‖²` (`2ab ≤ a² + b²` on each of the
  `2n` links);
* **`lintegral_exp_neg_mul_latticeSq`** — the Gaussian integral in `ℝ≥0∞`, obtained from the real
  one by `integral_eq_lintegral_of_nonneg_ae` (so no integrability is ever assumed);
* `latticeGFFMass` — the total mass `Z` as a number in `ℝ≥0∞`, with its two bounds
  **`latticeGFFMass_le`** / **`latticeGFFMass_ge`**;
* **`latticeGFFMass_pos`**, **`latticeGFFMass_lt_top`** — hence `0 < Z < ∞`: the unnormalised Gibbs
  measure is finite and non-zero; `latticeGFFZ_eq_toReal` identifies the real-valued integral with
  it;
* **`latticeGFFMass_zero`** — the exact partition function in the degenerate case `n = 0`
  (a single slice): `Z = (2π/m)^{|S|/2}`;
* **`latticeGFFProbability`** — the normalised measure `Z⁻¹ · latticeGFFMeasure m`, with
  **`isProbabilityMeasure_latticeGFFProbability`**: it *is* a probability measure as soon as
  `m > 0`;
* **`latticeGFFProbability_reflectionPositive`** — normalising does not destroy reflection
  positivity: the OS form under `ν` is `Z⁻¹` times the OS form under the unnormalised measure.

## Honest boundary

The normalising constant is **evaluated exactly** wherever the quadratic form is diagonal: the
reference Gaussians (with all the constants) and the single-slice partition function
`latticeGFFMass_zero`.  For `n ≥ 1` the chapter gives the two-sided bound

```
(√(π/(4·2n + m/2)))^{(2n+1)|S|}  ≤  Z  ≤  (√(2π/m))^{(2n+1)|S|},
```

i.e. `Z` is pinned between two explicit numbers, hence finite and positive.  The *closed form* is
`(2π)^{N/2}/√det K` with `N = (2n+1)|S|` and `K` the tridiagonal lattice operator `2L + m·1`
(`L` the path Laplacian, tensored with the identity on the `|S|` sites).  Evaluating it needs the
slice-by-slice recursion of the effective mass

```
μ₀ = m/2,      μ_{j+1} = m/2 + μ_j/(1 + μ_j)
```

(equivalently the three-term determinant recursion for a tridiagonal matrix).  Section 5 below
proves the one step that recursion is made of, and
`BookProof.ReflectionPositivity.ChainPartition` iterates it to the closed form for a chain of
slices, proves the determinant identity `det K_N = ∏_{j<N}(1 + μ_j) · μ_N` of the
(single-site) tridiagonal operator, identifies the boundary-weight/half-space integral
`∫⁻ z ∫⁻ y ρ(z)ν_z(y)` with the chain partition function, and identifies `latticeGFFMass m n`
itself with `chainZ m (m/2) (2n)` by the measure-preserving relabelling of the `2n + 1` slices as a
chain (**`latticeGFFMass_eq_chainZ`**, that chapter's §7–8).  So the exact value is

```
Z = π^{(2n+1)|S|/2} / (det K_{2n})^{|S|/2},      K_N = 2 · chainMatrix m (m/2) N,
```

for the *single-site* operator of that chapter (`chainZ_closed_det`) — i.e. the textbook
`(2π)^{N/2}/√det K` — and the two-sided bounds of this chapter are the special case of it that
needed no recursion.  What is *not* claimed here: the tensor-product form of the operator on the
`|S|` sites, which is only used implicitly (the form is diagonal in the sites, so the
`|S|`-th power is exactly `(det K)^{|S|/2}`), and the same closed form for the interacting Wilson
measure.
Everything needs `m > 0`: for `m = 0` the measure is translation invariant and its total mass is
infinite, so no probability normalisation exists.

Nor is anything here a statement about the *interacting* Wilson measure: both bounds use only that
the action sits between two multiples of the free mass term, never the quartic plaquette term.
-/

namespace BookProof.ReflectionPositivity

open MeasureTheory
open scoped BigOperators ENNReal

noncomputable section

variable {S : Type*} [Fintype S]

/-! ## 1. The reference Gaussian integrals -/

/-- The squared Euclidean norm of a real-valued function on a finite type, `‖x‖² = ∑ i, (x i)²`. -/
def sqSum {ι : Type*} [Fintype ι] (x : ι → ℝ) : ℝ := ∑ i, x i ^ 2

theorem sqSum_nonneg {ι : Type*} [Fintype ι] (x : ι → ℝ) : 0 ≤ sqSum x := by
  simp only [sqSum]
  exact Finset.sum_nonneg fun i _ => sq_nonneg (x i)

/-- The squared norm of a stack of `n` slices of the lattice. -/
def layerSq {n : ℕ} (y : Fin n → S → ℝ) : ℝ := ∑ k, sqSum (y k)

theorem layerSq_nonneg {n : ℕ} (y : Fin n → S → ℝ) : 0 ≤ layerSq y := by
  simp only [layerSq]
  exact Finset.sum_nonneg fun k _ => sqSum_nonneg (y k)

/-- The squared norm of a full lattice configuration, summed over all `2n + 1` slices. -/
def latticeSq {n : ℕ} (p : (S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ))) : ℝ :=
  sqSum p.1 + layerSq p.2.1 + layerSq p.2.2

theorem latticeSq_nonneg {n : ℕ}
    (p : (S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ))) : 0 ≤ latticeSq p := by
  simp only [latticeSq]
  exact add_nonneg (add_nonneg (sqSum_nonneg p.1) (layerSq_nonneg p.2.1))
    (layerSq_nonneg p.2.2)

theorem measurable_sqSum {ι : Type*} [Fintype ι] :
    Measurable fun x : ι → ℝ => sqSum x := by
  simp only [sqSum]
  exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).pow_const 2

theorem measurable_layerSq {n : ℕ} :
    Measurable fun y : Fin n → S → ℝ => layerSq y := by
  simp only [layerSq]
  exact Finset.measurable_sum _ fun k _ =>
    (measurable_sqSum (ι := S)).comp (measurable_pi_apply k)

theorem measurable_latticeSq {n : ℕ} :
    Measurable fun p : (S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ)) => latticeSq p := by
  simp only [latticeSq]
  exact (measurable_sqSum (ι := S)).comp measurable_fst
    |>.add ((measurable_layerSq (S := S) (n := n)).comp
        (measurable_fst.comp measurable_snd))
    |>.add ((measurable_layerSq (S := S) (n := n)).comp
        (measurable_snd.comp measurable_snd))

/-- **The reference Gaussian integral over the sites**: `∫_{ℝ^S} exp(−c‖x‖²) dx = (√(π/c))^{|S|}`.
Fubini over the sites (`integral_fintype_prod_eq_pow`) plus the one-dimensional
`integral_gaussian`; this is where the normalising constant comes from. -/
theorem integral_exp_neg_mul_sqSum {ι : Type*} [Fintype ι] {c : ℝ} (_hc : 0 < c) :
    ∫ x : ι → ℝ, Real.exp (-(c * sqSum x)) = Real.sqrt (Real.pi / c) ^ Fintype.card ι := by
  have hfun : ∀ x : ι → ℝ, Real.exp (-(c * sqSum x))
      = ∏ i, Real.exp (-(c * (x i) ^ 2)) := by
    intro x
    rw [← Real.exp_sum]
    congr 1
    simp only [sqSum]
    rw [Finset.mul_sum, Finset.sum_neg_distrib]
  simp only [hfun]
  rw [integral_fintype_prod_volume_eq_pow (𝕜 := ℝ) (E := ℝ)
    (f := fun t : ℝ => Real.exp (-(c * t ^ 2)))]
  congr 1
  rw [← integral_gaussian c]
  congr 1
  funext t
  rw [neg_mul]

/-- The reference Gaussian integral over a stack of `n` slices. -/
theorem integral_exp_neg_mul_layerSq {c : ℝ} (hc : 0 < c) {n : ℕ} :
    ∫ y : Fin n → S → ℝ, Real.exp (-(c * layerSq y))
      = (Real.sqrt (Real.pi / c) ^ Fintype.card S) ^ n := by
  have hfun : ∀ y : Fin n → S → ℝ, Real.exp (-(c * layerSq y))
      = ∏ k, Real.exp (-(c * sqSum (y k))) := by
    intro y
    rw [← Real.exp_sum]
    congr 1
    simp only [layerSq]
    rw [Finset.mul_sum, Finset.sum_neg_distrib]
  simp only [hfun]
  rw [integral_fintype_prod_volume_eq_pow (𝕜 := ℝ) (E := S → ℝ)
    (f := fun x : S → ℝ => Real.exp (-(c * sqSum x)))]
  rw [integral_exp_neg_mul_sqSum hc, Fintype.card_fin]

/-- The reference measure of the configuration space, written out: the boundary slice, then the
past and the future half-spaces.  This is the measure `latticeGFFMeasure` is a density against. -/
def gffBaseMeasure {n : ℕ} : Measure ((S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ))) :=
  (volume : Measure (S → ℝ)).prod
    ((volume : Measure (Fin n → S → ℝ)).prod (volume : Measure (Fin n → S → ℝ)))

/-- **The reference Gaussian integral over a whole lattice configuration**:
`∫ exp(−c‖φ‖²) dφ = (√(π/c))^{(2n+1)|S|}`. -/
theorem integral_exp_neg_mul_latticeSq {c : ℝ} (hc : 0 < c) {n : ℕ} :
    ∫ p : (S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ)), Real.exp (-(c * latticeSq p))
        ∂(gffBaseMeasure (S := S) (n := n))
      = (Real.sqrt (Real.pi / c) ^ Fintype.card S) ^ (2 * n + 1) := by
  have hsplit : ∀ p : (S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ)),
      Real.exp (-(c * latticeSq p))
        = Real.exp (-(c * sqSum p.1))
            * (Real.exp (-(c * layerSq p.2.1)) * Real.exp (-(c * layerSq p.2.2))) := by
    intro p
    rw [latticeSq, mul_add, mul_add, ← Real.exp_add, ← Real.exp_add]
    congr 1
    ring
  simp only [hsplit, gffBaseMeasure]
  rw [integral_prod_mul (f := fun z : S → ℝ => Real.exp (-(c * sqSum z)))
    (g := fun w : (Fin n → S → ℝ) × (Fin n → S → ℝ) =>
      Real.exp (-(c * layerSq w.1)) * Real.exp (-(c * layerSq w.2)))]
  rw [integral_prod_mul (f := fun w : Fin n → S → ℝ => Real.exp (-(c * layerSq w)))
    (g := fun w : Fin n → S → ℝ => Real.exp (-(c * layerSq w)))]
  rw [integral_exp_neg_mul_sqSum hc, integral_exp_neg_mul_layerSq hc]
  ring

/-! ## 2. The action is squeezed between two multiples of its mass term -/

/-- The mass sum of a half-space is the squared norm of its slices:
`Σ_k Σ_i (φ_{k+1})ᵢ² = ‖y‖²`, because `chain z y (k+1) = y k`. -/
theorem sum_chain_succ_sq {n : ℕ} (z : S → ℝ) (y : Fin n → S → ℝ) :
    (∑ k : Fin n, ∑ i, (chain z y k.succ i) ^ 2) = layerSq y := by
  simp only [layerSq, sqSum]
  refine Finset.sum_congr rfl fun k _ => ?_
  have h : chain z y k.succ = y k := by
    simp only [chain]
    rw [Fin.cases_succ]
  rw [h]

/-- **The action dominates its mass term**: `S ≥ (m/2)‖φ‖²` for `m ≥ 0`. -/
theorem latticeAction_ge_mass (m : ℝ) (_hm : 0 ≤ m) {n : ℕ}
    (p : (S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ))) :
    (m / 2) * latticeSq p ≤ latticeAction m p := by
  have hgrad : ∀ (y : Fin n → S → ℝ), 0 ≤ ∑ k : Fin n, ∑ i,
      (chain p.1 y k.succ i - chain p.1 y k.castSucc i) ^ 2 := fun y =>
    Finset.sum_nonneg fun k _ => Finset.sum_nonneg fun i _ => sq_nonneg _
  simp only [latticeAction, halfAction, boundaryTerm, latticeSq, sum_chain_succ_sq, sqSum]
  nlinarith [hgrad p.2.1, hgrad p.2.2, _hm, sqSum_nonneg p.1, layerSq_nonneg p.2.1,
    layerSq_nonneg p.2.2]

/-- Every slice of a half-space has squared norm at most `‖z‖² + ‖y‖²`. -/
theorem sqSum_chain_le_add {n : ℕ} (z : S → ℝ) (y : Fin n → S → ℝ) (k : Fin (n + 1)) :
    sqSum (chain z y k) ≤ sqSum z + layerSq y := by
  induction k using Fin.cases with
  | zero =>
    have h : chain z y 0 = z := by simp only [chain]; simp
    rw [h]
    exact le_add_of_nonneg_right (layerSq_nonneg y)
  | succ j =>
    have h : chain z y (Fin.succ j) = y j := by
      simp only [chain]
      rw [Fin.cases_succ]
    rw [h]
    exact (Finset.single_le_sum (f := fun i => sqSum (y i))
      (fun i _ => sqSum_nonneg (y i)) (Finset.mem_univ j)).trans
      (le_add_of_nonneg_left (sqSum_nonneg z))

/-- Every slice of the configuration has squared norm at most `‖φ‖²`. -/
theorem sqSum_chain_le {n : ℕ} (p : (S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ)))
    (k : Fin (n + 1)) : sqSum (chain p.1 p.2.1 k) ≤ latticeSq p := by
  have hz : sqSum p.1 ≤ latticeSq p := by
    simp only [latticeSq]
    linarith [layerSq_nonneg p.2.1, layerSq_nonneg p.2.2]
  have hy : ∀ j : Fin n, sqSum (p.2.1 j) ≤ latticeSq p := by
    intro j
    have h1 : sqSum (p.2.1 j) ≤ layerSq p.2.1 :=
      Finset.single_le_sum (f := fun k => sqSum (p.2.1 k))
        (fun k _ => sqSum_nonneg (p.2.1 k)) (Finset.mem_univ j)
    simp only [latticeSq]
    linarith [layerSq_nonneg p.2.2, sqSum_nonneg p.1]
  induction k using Fin.cases with
  | zero => simpa only [chain] using hz
  | succ j => simpa only [chain, Fin.cases_succ] using hy j

/-- **The action is dominated by a multiple of the mass term**:
`S ≤ (4·2n + m/2)‖φ‖²` for `m ≥ 0`, by `(a − b)² ≤ 2a² + 2b²` on each of the `2n` links. -/
theorem latticeAction_le (m : ℝ) (_hm : 0 ≤ m) {n : ℕ}
    (p : (S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ))) :
    latticeAction m p ≤ (((4 * (2 * n) : ℕ) : ℝ) + m / 2) * latticeSq p := by
  have hlink : ∀ (y : Fin n → S → ℝ) (k : Fin n) (L : ℝ), sqSum p.1 + layerSq y ≤ L →
      (∑ i : S, (chain p.1 y k.succ i - chain p.1 y k.castSucc i) ^ 2) ≤ 4 * L := by
    intro y k L hL
    have hA : sqSum (chain p.1 y k.succ) ≤ L := by
      have h : chain p.1 y k.succ = y k := by
        simp only [chain]
        rw [Fin.cases_succ]
      rw [h]
      have hle := Finset.single_le_sum (f := fun j => sqSum (y j))
        (fun j _ => sqSum_nonneg (y j)) (Finset.mem_univ k)
      have hlay : layerSq y = ∑ j, sqSum (y j) := rfl
      linarith [hle, hL, sqSum_nonneg p.1, hlay]
    have hB : sqSum (chain p.1 y k.castSucc) ≤ L :=
      (sqSum_chain_le_add p.1 y k.castSucc).trans hL
    have hsq : (∑ i : S, (chain p.1 y k.succ i - chain p.1 y k.castSucc i) ^ 2)
        ≤ 2 * (sqSum (chain p.1 y k.succ) + sqSum (chain p.1 y k.castSucc)) := by
      simp only [sqSum]
      rw [mul_add, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_le_sum fun i _ => ?_
      nlinarith [sq_nonneg (chain p.1 y k.succ i - chain p.1 y k.castSucc i),
        sq_nonneg (chain p.1 y k.succ i + chain p.1 y k.castSucc i)]
    nlinarith [hsq, hA, hB]

  have hside : ∀ (y : Fin n → S → ℝ) (L : ℝ), sqSum p.1 + layerSq y ≤ L →
      (∑ k : Fin n, ∑ i : S, (chain p.1 y k.succ i - chain p.1 y k.castSucc i) ^ 2)
      ≤ (n : ℝ) * (4 * L) := by
    intro y L hL
    calc (∑ k : Fin n, ∑ i : S, (chain p.1 y k.succ i - chain p.1 y k.castSucc i) ^ 2)
        ≤ ∑ _k : Fin n, 4 * L := Finset.sum_le_sum fun k _ => hlink y k L hL
      _ = (n : ℝ) * (4 * L) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  have hkey : latticeAction m p
      = ((∑ k : Fin n, ∑ i, (chain p.1 p.2.1 k.succ i - chain p.1 p.2.1 k.castSucc i) ^ 2)
        + (∑ k : Fin n, ∑ i, (chain p.1 p.2.2 k.succ i - chain p.1 p.2.2 k.castSucc i) ^ 2))
        + (m / 2) * latticeSq p := by
    simp only [latticeAction, halfAction, boundaryTerm, sum_chain_succ_sq, latticeSq, sqSum]
    ring
  have hL1 : sqSum p.1 + layerSq p.2.1 ≤ latticeSq p := by
    simp only [latticeSq]
    linarith [layerSq_nonneg p.2.2]
  have hL2 : sqSum p.1 + layerSq p.2.2 ≤ latticeSq p := by
    simp only [latticeSq]
    linarith [layerSq_nonneg p.2.1]
  rw [hkey]
  have h1 := hside p.2.1 (latticeSq p) hL1
  have h2 := hside p.2.2 (latticeSq p) hL2
  push_cast
  nlinarith [h1, h2]

/-- `exp(−S)` is bounded by the reference Gaussian of variance `2/m`. -/
theorem exp_neg_latticeAction_le (m : ℝ) (hm : 0 ≤ m) {n : ℕ}
    (p : (S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ))) :
    Real.exp (-(latticeAction m p)) ≤ Real.exp (-((m / 2) * latticeSq p)) := by
  refine Real.exp_le_exp.mpr ?_
  have := latticeAction_ge_mass (S := S) m hm p
  linarith

/-- `exp(−S)` is bounded below by a reference Gaussian (of variance `2/(4·2n + m)`). -/
theorem le_exp_neg_latticeAction (m : ℝ) (hm : 0 ≤ m) {n : ℕ}
    (p : (S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ))) :
    Real.exp (-((((4 * (2 * n) : ℕ) : ℝ) + m / 2) * latticeSq p))
      ≤ Real.exp (-(latticeAction m p)) := by
  refine Real.exp_le_exp.mpr ?_
  have := latticeAction_le (S := S) m hm p
  linarith

/-! ## 3. The Gaussian integral in `ℝ≥0∞` and the total mass of the Gibbs measure -/

/-- **The reference Gaussian integral, in `ℝ≥0∞`**: this is the `lintegral` that the total mass of
the Gibbs measure is bounded by.  It is derived from the real integral, so no integrability is
needed. -/
theorem lintegral_exp_neg_mul_latticeSq {c : ℝ} (hc : 0 < c) {n : ℕ} :
    ∫⁻ p : (S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ)),
        ENNReal.ofReal (Real.exp (-(c * latticeSq p))) ∂(gffBaseMeasure (S := S) (n := n))
      = ENNReal.ofReal ((Real.sqrt (Real.pi / c) ^ Fintype.card S) ^ (2 * n + 1)) := by
  have hmeas : AEStronglyMeasurable (fun p : (S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ)) =>
      Real.exp (-(c * latticeSq p))) (gffBaseMeasure (S := S) (n := n)) :=
    (((measurable_latticeSq (S := S) (n := n)).const_mul c).neg).exp.aestronglyMeasurable
  have h := integral_eq_lintegral_of_nonneg_ae
    (μ := gffBaseMeasure (S := S) (n := n))
    (f := fun p : (S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ)) =>
      Real.exp (-(c * latticeSq p)))
    (Filter.Eventually.of_forall fun p => (Real.exp_pos _).le) hmeas
  rw [integral_exp_neg_mul_latticeSq hc] at h
  have hpos : 0 < (Real.sqrt (Real.pi / c) ^ Fintype.card S) ^ (2 * n + 1) :=
    pow_pos (pow_pos (Real.sqrt_pos.mpr (by positivity)) _) _
  have hne : (∫⁻ p : (S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ)),
      ENNReal.ofReal (Real.exp (-(c * latticeSq p))) ∂(gffBaseMeasure (S := S) (n := n)))
      ≠ ⊤ := by
    intro htop
    rw [htop, ENNReal.toReal_top] at h
    exact hpos.ne' h
  rw [← ENNReal.ofReal_toReal hne]
  congr 1
  simpa using h.symm

/-- **The total mass of the lattice free field**, `Z = ∫ exp(−S) dφ`, as a number in `ℝ≥0∞`. -/
def latticeGFFMass (m : ℝ) {n : ℕ} : ℝ≥0∞ :=
  latticeGFFMeasure (S := S) (n := n) m
    (Set.univ : Set ((S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ))))

theorem latticeGFFMass_eq_lintegral (m : ℝ) {n : ℕ} :
    @latticeGFFMass S _ m n
      = ∫⁻ p : (S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ)),
          ENNReal.ofReal (Real.exp (-(latticeAction m p)))
          ∂(gffBaseMeasure (S := S) (n := n)) := by
  rw [latticeGFFMass, latticeGFFMeasure, withDensity_apply _ MeasurableSet.univ,
    Measure.restrict_univ]
  rfl

/-- **Upper bound for the partition function**: `Z ≤ (√(2π/m))^{(2n+1)|S|}`. -/
theorem latticeGFFMass_le (m : ℝ) (hm : 0 < m) {n : ℕ} :
    @latticeGFFMass S _ m n
      ≤ ENNReal.ofReal ((Real.sqrt (Real.pi / (m / 2)) ^ Fintype.card S) ^ (2 * n + 1)) := by
  rw [latticeGFFMass_eq_lintegral, ← lintegral_exp_neg_mul_latticeSq (S := S) (n := n)
    (c := m / 2) (by linarith)]
  exact lintegral_mono fun p => ENNReal.ofReal_le_ofReal (exp_neg_latticeAction_le m hm.le p)

/-- **Lower bound for the partition function**: `(√(π/(8n + m/2)))^{(2n+1)|S|} ≤ Z`. -/
theorem latticeGFFMass_ge (m : ℝ) (hm : 0 < m) {n : ℕ} :
    ENNReal.ofReal ((Real.sqrt (Real.pi / ((((4 * (2 * n) : ℕ) : ℝ) + m / 2)))
          ^ Fintype.card S) ^ (2 * n + 1))
      ≤ @latticeGFFMass S _ m n := by
  rw [latticeGFFMass_eq_lintegral, ← lintegral_exp_neg_mul_latticeSq (S := S) (n := n)
    (c := (((4 * (2 * n) : ℕ) : ℝ) + m / 2)) (by positivity)]
  exact lintegral_mono fun p => ENNReal.ofReal_le_ofReal (le_exp_neg_latticeAction m hm.le p)

/-- **The partition function is positive and finite**: the unnormalised Gibbs measure of the
lattice free field is a finite, non-zero measure. -/
theorem latticeGFFMass_pos (m : ℝ) (hm : 0 < m) {n : ℕ} :
    0 < @latticeGFFMass S _ m n := by
  refine lt_of_lt_of_le ?_ (latticeGFFMass_ge m hm)
  refine ENNReal.ofReal_pos.mpr ?_
  exact pow_pos (pow_pos (Real.sqrt_pos.mpr (by positivity)) _) _

theorem latticeGFFMass_ne_zero (m : ℝ) (hm : 0 < m) {n : ℕ} :
    @latticeGFFMass S _ m n ≠ 0 := ne_of_gt (latticeGFFMass_pos m hm)

theorem latticeGFFMass_lt_top (m : ℝ) (hm : 0 < m) {n : ℕ} :
    @latticeGFFMass S _ m n < ⊤ :=
  lt_of_le_of_lt (latticeGFFMass_le m hm) ENNReal.ofReal_lt_top

/-- The real-valued partition function (`latticeGFFZ`) is the `toReal` of the mass. -/
theorem latticeGFFZ_eq_toReal (m : ℝ) {n : ℕ} :
    (∫ p : (S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ)),
        Real.exp (-(latticeAction m p)) ∂(gffBaseMeasure (S := S) (n := n)))
      = (@latticeGFFMass S _ m n).toReal := by
  rw [latticeGFFMass_eq_lintegral, integral_eq_lintegral_of_nonneg_ae
    (f := fun p : (S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ)) =>
      Real.exp (-(latticeAction m p)))
    (Filter.Eventually.of_forall fun p => (Real.exp_pos _).le)
    ((measurable_latticeAction (S := S) m (n := n)).neg.exp.aestronglyMeasurable)]

/-- **The exact partition function in the degenerate case `n = 0`** (a single slice, no
half-spaces): `S = (m/2)‖z‖²`, so `Z = (2π/m)^{|S|/2}`. -/
theorem latticeGFFMass_zero (m : ℝ) (hm : 0 < m) :
    @latticeGFFMass S _ m 0
      = ENNReal.ofReal (Real.sqrt (2 * Real.pi / m) ^ Fintype.card S) := by
  have hact : ∀ p : (S → ℝ) × ((Fin 0 → S → ℝ) × (Fin 0 → S → ℝ)),
      latticeAction m p = (m / 2) * latticeSq p := by
    intro p
    simp only [latticeAction, halfAction, boundaryTerm, latticeSq, layerSq, sqSum,
      Finset.univ_eq_empty, Finset.sum_empty, add_zero]
    ring
  have hcongr : ∀ p : (S → ℝ) × ((Fin 0 → S → ℝ) × (Fin 0 → S → ℝ)),
      ENNReal.ofReal (Real.exp (-(latticeAction m p)))
        = ENNReal.ofReal (Real.exp (-((m / 2) * latticeSq p))) := by
    intro p
    rw [hact p]
  rw [latticeGFFMass_eq_lintegral]
  simp only [hcongr]
  rw [lintegral_exp_neg_mul_latticeSq (S := S) (n := 0) (c := m / 2) (by linarith)]
  have hpi : Real.pi / (m / 2) = 2 * Real.pi / m := by field_simp
  rw [hpi]
  simp

/-! ## 4. The normalised measure is a probability measure -/

/-- **The lattice free field as a probability measure**: the Gibbs measure of
`BookProof.ReflectionPositivity.LatticeFreeField` rescaled by its total mass. -/
def latticeGFFProbability (m : ℝ) {n : ℕ} : Measure ((S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ))) :=
  (@latticeGFFMass S _ m n)⁻¹ • latticeGFFMeasure (S := S) m

theorem latticeGFFProbability_univ (m : ℝ) (hm : 0 < m) {n : ℕ} :
    latticeGFFProbability (S := S) (n := n) m
      (Set.univ : Set ((S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ)))) = 1 := by
  rw [latticeGFFProbability, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel (latticeGFFMass_ne_zero m hm)
    (ne_of_lt (latticeGFFMass_lt_top m hm))

/-- **`latticeGFFMeasure` normalised is a probability measure** (for `m > 0`). -/
theorem isProbabilityMeasure_latticeGFFProbability (m : ℝ) (hm : 0 < m) {n : ℕ} :
    IsProbabilityMeasure (latticeGFFProbability (S := S) (n := n) m) :=
  ⟨latticeGFFProbability_univ (S := S) m hm⟩

/-- **Normalising does not destroy reflection positivity**: the OS form under the probability
measure is `Z⁻¹` times the OS form under the unnormalised Gibbs measure, hence still
nonnegative. -/
theorem latticeGFFProbability_reflectionPositive (m : ℝ) (_hm : 0 < m) {n : ℕ}
    (F : (S → ℝ) → (Fin n → S → ℝ) → ℝ)
    (hint : Integrable
      (fun p : (S → ℝ) × ((Fin n → S → ℝ) × (Fin n → S → ℝ)) =>
        Real.exp (-(latticeAction m p)) * fkOSForm F p)
      (gffBaseMeasure (S := S) (n := n))) :
    0 ≤ ∫ p, fkOSForm F p ∂(latticeGFFProbability (S := S) (n := n) m) := by
  have hbase : (gffBaseMeasure (S := S) (n := n))
      = ((volume : Measure (S → ℝ)).prod
          ((volume : Measure (Fin n → S → ℝ)).prod (volume : Measure (Fin n → S → ℝ)))) := rfl
  rw [latticeGFFProbability, integral_smul_measure, smul_eq_mul]
  refine mul_nonneg ENNReal.toReal_nonneg ?_
  exact latticeGFF_reflectionPositive (S := S) m F (by rw [← hbase]; exact hint)
/-! ## 5. The effective-mass step of the slice recursion

The closed form `Z = (2π)^{N/2}/√det K` needs the slice-by-slice recursion of the effective mass
`μ₀ = m/2`, `μ_{j+1} = m/2 + μ_j/(1 + μ_j)`; `BookProof.ReflectionPositivity.ChainPartition`
iterates it, and proves the matching determinant identity for the tridiagonal operator.  This
section proves the one step that recursion is made of, and defines the sequence.

Integrating out one interior slice `w` of the half-space chain against
`exp(-(‖w - v‖² + c‖w‖²))` — its single gradient link to the next slice `v` plus its own mass
term of coefficient `c` — gives back a Gaussian in `v`, with coefficient `δ(c) = c/(1+c)` on
`‖v‖²` instead of `c`:
`∫ exp(-(‖w-v‖² + c‖w‖²)) dw = (√(π/(1+c)))^{|S|} · exp(-δ(c)‖v‖²)` (**`integral_exp_neg_slice_step`**).
That is precisely why the effective coefficient moves `c ↦ c/(1+c) + m/2` at the next slice in.
-/

/-- `δ(c) = 1 - 1/(1+c) = c/(1+c)`: the coefficient the next slice inherits. -/
def effCorr (c : ℝ) : ℝ := c / (1 + c)

/-- **The effective-mass recursion** of the free-field slice integration: `μ₀ = m/2` at the
innermost slice, `μ_{j+1} = m/2 + δ(μ_j)` at the next one. -/
def effMass (m : ℝ) : ℕ → ℝ
  | 0 => m / 2
  | (j + 1) => m / 2 + effCorr (effMass m j)

theorem effCorr_pos {c : ℝ} (hc : 0 < c) : 0 < effCorr c := by
  simp only [effCorr]
  positivity

theorem effCorr_lt_one {c : ℝ} (hc : 0 < c) : effCorr c < 1 := by
  simp only [effCorr]
  rw [div_lt_one (by linarith)]
  linarith

/-- The effective mass stays positive and bounded: `0 < μ_j < 1 + m/2`. -/
theorem effMass_pos (m : ℝ) (hm : 0 < m) (j : ℕ) : 0 < effMass m j := by
  induction j with
  | zero => simp only [effMass]; linarith
  | succ j ih => exact add_pos (by linarith) (effCorr_pos ih)

/-- The squared difference of two slices, `‖w - v‖² = ∑ i, (w i - v i)²`. -/
def diffSq (v w : S → ℝ) : ℝ := ∑ i, (w i - v i) ^ 2

/-- The one-dimensional step: completing the square and shifting by translation invariance of
Lebesgue measure. -/
theorem integral_exp_neg_slice_step_one {c : ℝ} (hc : 0 < c) (v : ℝ) :
    ∫ u : ℝ, Real.exp (-((u - v) ^ 2 + c * u ^ 2))
      = Real.sqrt (Real.pi / (1 + c)) * Real.exp (-(effCorr c * v ^ 2)) := by
  have hc1 : (1 + c) ≠ 0 := by positivity
  have hsq : ∀ u : ℝ, (u - v) ^ 2 + c * u ^ 2
      = (1 + c) * (u - v / (1 + c)) ^ 2 + effCorr c * v ^ 2 := by
    intro u
    simp only [effCorr]
    field_simp
    ring
  have hshift : ∫ u : ℝ, Real.exp (-((1 + c) * (u - v / (1 + c)) ^ 2))
      = ∫ t : ℝ, Real.exp (-((1 + c) * t ^ 2)) :=
    integral_sub_right_eq_self (fun t : ℝ => Real.exp (-((1 + c) * t ^ 2))) (v / (1 + c))
  have hstep : ∫ u : ℝ, Real.exp (-((1 + c) * (u - v / (1 + c)) ^ 2))
      = Real.sqrt (Real.pi / (1 + c)) := by
    rw [hshift]
    simpa only [neg_mul] using integral_gaussian (1 + c)
  calc ∫ u : ℝ, Real.exp (-((u - v) ^ 2 + c * u ^ 2))
      = ∫ u : ℝ, Real.exp (-((1 + c) * (u - v / (1 + c)) ^ 2))
          * Real.exp (-(effCorr c * v ^ 2)) := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun u => ?_)
        show Real.exp (-((u - v) ^ 2 + c * u ^ 2))
          = Real.exp (-((1 + c) * (u - v / (1 + c)) ^ 2)) * Real.exp (-(effCorr c * v ^ 2))
        rw [hsq u, show -((1 + c) * (u - v / (1 + c)) ^ 2 + effCorr c * v ^ 2)
            = -((1 + c) * (u - v / (1 + c)) ^ 2) + -(effCorr c * v ^ 2) by ring,
          Real.exp_add]
    _ = (∫ u : ℝ, Real.exp (-((1 + c) * (u - v / (1 + c)) ^ 2)))
          * Real.exp (-(effCorr c * v ^ 2)) := by
        rw [integral_mul_const]
    _ = Real.sqrt (Real.pi / (1 + c)) * Real.exp (-(effCorr c * v ^ 2)) := by rw [hstep]

/-- **The effective-mass step**: integrating one interior slice out of the half-space chain
multiplies the integral by `(√(π/(1+c)))^{|S|}` and replaces the coefficient `c` of `‖v‖²` by
`δ(c) = c/(1+c)`. -/
theorem integral_exp_neg_slice_step {c : ℝ} (hc : 0 < c) (v : S → ℝ) :
    ∫ w : S → ℝ, Real.exp (-(diffSq v w + c * sqSum w))
      = Real.sqrt (Real.pi / (1 + c)) ^ Fintype.card S * Real.exp (-(effCorr c * sqSum v)) := by
  have hfun : ∀ w : S → ℝ, Real.exp (-(diffSq v w + c * sqSum w))
      = ∏ i, Real.exp (-((w i - v i) ^ 2 + c * (w i) ^ 2)) := by
    intro w
    rw [← Real.exp_sum]
    congr 1
    simp only [diffSq, sqSum, Finset.mul_sum, ← Finset.sum_add_distrib]
    rw [Finset.sum_neg_distrib]
  simp only [hfun]
  rw [integral_fintype_prod_volume_eq_prod (𝕜 := ℝ) (E := fun _ : S => ℝ)
    (f := fun (i : S) (u : ℝ) => Real.exp (-((u - v i) ^ 2 + c * u ^ 2)))]
  rw [Finset.prod_congr rfl (fun i (_ : i ∈ Finset.univ) => integral_exp_neg_slice_step_one hc (v i))]
  rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, ← Real.exp_sum]
  congr 1
  simp only [sqSum, Finset.mul_sum, Finset.sum_neg_distrib]

end

end BookProof.ReflectionPositivity
