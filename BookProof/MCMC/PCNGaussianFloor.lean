import Mathlib

/-!
# Chapter PCNGaussianFloor — the pCN increment's density floor on a box

`BookProof/MCMC/PositivityCone` §27 computes the Doeblin constant `δ` for the pCN *occupation*
chain — a binomial thinning.  The pCN proposal on the *weight* space is not that: it is the Gaussian
increment

`y = ρ x + √(1 − ρ²) ξ`,  `ξ ~ N(0, σ²)`,

whose density the cone model's minorant needs bounded below on the bounded region the chain visits.
This chapter computes that floor, so the `δ` that §25 takes as a parameter is an inequality about
the architecture's own proposal rather than an unknown number.

## Contents

* `pcnQuad` — the squared increment `∑ᵢ (yᵢ − ρ xᵢ)²`, and `pcnQuad_nonneg`;
* `pcnDensity c s ρ x y = c · exp (−pcnQuad ρ x y / s)` — the proposal density with `c` the
  normalising constant and `s = 2σ²(1 − ρ²)` the scaled variance;
* `pcnDensity_le_of_quad_le` — the density is decreasing in the increment, so an upper bound `B` on
  `pcnQuad` gives the floor `c · exp (−B/s)`;
* **`pcnQuad_box_le`** — on the box `|xᵢ| ≤ R`, `|yᵢ| ≤ R` the increment is at most `d·(R(1+ρ))²`,
  since `|yᵢ − ρ xᵢ| ≤ (1 + ρ)R`;
* **`pcnDensity_floor`** — the resulting floor `c · exp (−d (R(1+ρ))²/s)`, and
  `pcnDensity_floor_pos` for `c > 0`;
* `pcnNorm`, `pcnNorm_pos` — the Gaussian normalising constant `(2πs)^(−d/2)` is positive, and
  `pcnScale_pos` the scaled variance `s = 2σ²(1 − ρ²) > 0` for `0 ≤ ρ < 1`, `σ > 0`;
* **`pcnGaussian_floor`**, `pcnGaussian_floor_pos` — the two together: the number itself;
* **§2, the passage to a measure** — `pcnBox` (`{|yᵢ| ≤ R}`, `measurableSet_pcnBox`,
  `mem_pcnBox`), **`pcnMeasure_minorant`** (a density floor on the box turns into a measure
  inequality: `volume.withDensity q ≥ F • volume.restrict box`, uniformly in the starting point)
  and its instance **`pcnMeasure_floor`** at the architecture's numbers, with
  `pcnMeasure_floor_pos`.

## Honest boundary

This is a *density* floor and the measure inequality it implies on a box — not a full Doeblin
theorem on the continuum.  §22–§26's machinery is stated on a finite state space, and the weight
space is not one.  What §2 adds is that the floor is a statement about the *proposal measure* on
`ℝ^d`, uniformly in the starting point, which is the form a minorant consumes; what it does not do
is name the target measure on `ℝ^d`, pass the Metropolis filter through the density, or produce a
rate: the minorant is a lower bound on the proposal's mass on the box, and turning it into a
contraction needs the acceptance probability and the target's own mass there, neither of which this
chapter states.
-/

noncomputable section

namespace BookProof.MCMC.PCNGaussianFloor

open Finset MeasureTheory

variable {d : ℕ}

/-- The squared pCN increment `∑ᵢ (yᵢ − ρ xᵢ)²`: the exponent of the Gaussian proposal. -/
def pcnQuad (ρ : ℝ) (x y : Fin d → ℝ) : ℝ := ∑ i, (y i - ρ * x i) ^ 2

theorem pcnQuad_nonneg (ρ : ℝ) (x y : Fin d → ℝ) : 0 ≤ pcnQuad ρ x y :=
  Finset.sum_nonneg fun i _ => sq_nonneg (y i - ρ * x i)

/-- The pCN proposal's density: `c · exp (−pcnQuad / s)`, with `c` the normalising constant and
`s = 2σ²(1 − ρ²)` the scaled variance of the increment. -/
def pcnDensity (c s ρ : ℝ) (x y : Fin d → ℝ) : ℝ :=
  c * Real.exp (-(pcnQuad ρ x y) / s)

/-- The density is decreasing in the increment: an upper bound `B` on `pcnQuad` gives the floor
`c · exp (−B/s)`. -/
theorem pcnDensity_le_of_quad_le {c s ρ B : ℝ} (hc : 0 ≤ c) (hs : 0 < s) {x y : Fin d → ℝ}
    (hB : pcnQuad ρ x y ≤ B) :
    c * Real.exp (-B / s) ≤ pcnDensity c s ρ x y := by
  have hdiv : pcnQuad ρ x y / s ≤ B / s := by
    exact div_le_div_of_nonneg_right hB hs.le
  have hexp : Real.exp (-B / s) ≤ Real.exp (-(pcnQuad ρ x y) / s) := by
    refine Real.exp_le_exp.mpr ?_
    rw [neg_div, neg_div]
    exact neg_le_neg hdiv
  exact mul_le_mul_of_nonneg_left hexp hc

/-- **The box bound on the increment**: if both `x` and `y` lie in the box `|·| ≤ R`, then every
coordinate of `y − ρx` is at most `(1 + ρ)R` in modulus. -/
theorem pcnQuad_box_le {ρ R : ℝ} (hρ0 : 0 ≤ ρ) (hR : 0 ≤ R) {x y : Fin d → ℝ}
    (hx : ∀ i, |x i| ≤ R) (hy : ∀ i, |y i| ≤ R) :
    pcnQuad ρ x y ≤ (d : ℝ) * (R * (1 + ρ)) ^ 2 := by
  have hR1 : 0 ≤ R * (1 + ρ) := mul_nonneg hR (by linarith)
  have hpt : ∀ i, (y i - ρ * x i) ^ 2 ≤ (R * (1 + ρ)) ^ 2 := by
    intro i
    have hyi := abs_le.mp (hy i)
    have hxi := abs_le.mp (hx i)
    have hlo : -(ρ * R) ≤ ρ * x i := by nlinarith [hxi.1, hρ0]
    have hhi : ρ * x i ≤ ρ * R := by nlinarith [hxi.2, hρ0]
    have habs : |y i - ρ * x i| ≤ R * (1 + ρ) := by
      rw [abs_le]
      constructor <;> nlinarith [hyi.1, hyi.2, hlo, hhi]
    calc (y i - ρ * x i) ^ 2 = |y i - ρ * x i| ^ 2 := (sq_abs _).symm
      _ ≤ (R * (1 + ρ)) ^ 2 := pow_le_pow_left₀ (abs_nonneg _) habs 2
  calc pcnQuad ρ x y ≤ ∑ _i : Fin d, (R * (1 + ρ)) ^ 2 := Finset.sum_le_sum fun i _ => hpt i
    _ = (d : ℝ) * (R * (1 + ρ)) ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The density floor on a box**: on `|xᵢ| ≤ R`, `|yᵢ| ≤ R`, the pCN proposal's density is at
least `c · exp (−d (R(1+ρ))²/s)`. -/
theorem pcnDensity_floor {c s ρ R : ℝ} (hc : 0 ≤ c) (hs : 0 < s) (hρ0 : 0 ≤ ρ) (hR : 0 ≤ R)
    {x y : Fin d → ℝ} (hx : ∀ i, |x i| ≤ R) (hy : ∀ i, |y i| ≤ R) :
    c * Real.exp (-((d : ℝ) * (R * (1 + ρ)) ^ 2) / s) ≤ pcnDensity c s ρ x y :=
  pcnDensity_le_of_quad_le hc hs (pcnQuad_box_le hρ0 hR hx hy)

theorem pcnDensity_floor_pos {c s ρ R : ℝ} (hc : 0 < c) :
    0 < c * Real.exp (-((d : ℝ) * (R * (1 + ρ)) ^ 2) / s) :=
  mul_pos hc (Real.exp_pos _)

/-- The scaled variance of the pCN increment: `s = 2σ²(1 − ρ²)`. -/
def pcnScale (σ ρ : ℝ) : ℝ := 2 * σ ^ 2 * (1 - ρ ^ 2)

theorem pcnScale_pos {σ ρ : ℝ} (hσ : 0 < σ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    0 < pcnScale σ ρ := by
  have h2 : 0 < 1 - ρ ^ 2 := by nlinarith
  simp only [pcnScale]
  positivity

/-- The Gaussian normalising constant `(2πs)^(−d/2)`. -/
def pcnNorm (d : ℕ) (s : ℝ) : ℝ := (2 * Real.pi * s) ^ (-(d : ℝ) / 2)

theorem pcnNorm_pos {s : ℝ} (hs : 0 < s) : 0 < pcnNorm d s := by
  have h : 0 < 2 * Real.pi * s := mul_pos (mul_pos two_pos Real.pi_pos) hs
  exact Real.rpow_pos_of_pos h _

/-- **The number §25 asks for.**  On the box `|xᵢ| ≤ R`, `|yᵢ| ≤ R` the pCN Gaussian increment has
density at least

`(2πs)^(−d/2) · exp (−d (R(1+ρ))² / s)`,  `s = 2σ²(1 − ρ²)`,

which is the Doeblin constant a finite-state minorant would consume. -/
theorem pcnGaussian_floor {σ ρ R : ℝ} (hσ : 0 < σ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hR : 0 ≤ R)
    {x y : Fin d → ℝ} (hx : ∀ i, |x i| ≤ R) (hy : ∀ i, |y i| ≤ R) :
    pcnNorm d (pcnScale σ ρ) * Real.exp (-((d : ℝ) * (R * (1 + ρ)) ^ 2) / pcnScale σ ρ)
      ≤ pcnDensity (pcnNorm d (pcnScale σ ρ)) (pcnScale σ ρ) ρ x y :=
  pcnDensity_floor (le_of_lt (pcnNorm_pos (pcnScale_pos hσ hρ0 hρ1)))
    (pcnScale_pos hσ hρ0 hρ1) hρ0 hR hx hy

theorem pcnGaussian_floor_pos {σ ρ R : ℝ} (hσ : 0 < σ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    0 < pcnNorm d (pcnScale σ ρ) * Real.exp (-((d : ℝ) * (R * (1 + ρ)) ^ 2) / pcnScale σ ρ) :=
  pcnDensity_floor_pos (pcnNorm_pos (pcnScale_pos hσ hρ0 hρ1))

/-! ## 2. The passage to a measure on `ℝ^d`

§1 is a pointwise inequality.  The step §1's honest boundary lists — from a density floor to a
statement about a *kernel* — is the measure-theoretic one: on the box the proposal's density
dominates a constant, so the proposal measure dominates that constant times Lebesgue restricted to
the box.  That is the continuum form of the Doeblin minorant a finite-state chain consumes
(`PositivityCone`'s `Minorant`), and it needs no integration theory beyond `withDensity`.
-/

/-- The box `{|yᵢ| ≤ R}` in `ℝ^d` — the region the pCN chain visits, where §1's floor holds. -/
def pcnBox (d : ℕ) (R : ℝ) : Set (Fin d → ℝ) := Set.pi Set.univ (fun _ => Set.Icc (-R) R)

theorem measurableSet_pcnBox (R : ℝ) : MeasurableSet (pcnBox d R) :=
  MeasurableSet.pi Set.countable_univ fun _ _ => measurableSet_Icc

theorem mem_pcnBox {R : ℝ} {y : Fin d → ℝ} : y ∈ pcnBox d R ↔ ∀ i, |y i| ≤ R := by
  simp only [pcnBox, Set.mem_pi, Set.mem_univ, true_implies, Set.mem_Icc, abs_le]

/-- **The floor as a minorant of the proposal measure.**  If the density is at least `F` on the box,
then the proposal's measure dominates `F` times Lebesgue restricted to that box — for every starting
point `x`, which is what makes the bound a *kernel*-level statement rather than a pointwise one. -/
theorem pcnMeasure_minorant {c s ρ R F : ℝ} {x : Fin d → ℝ}
    (hle : ∀ y ∈ pcnBox d R, F ≤ pcnDensity c s ρ x y) :
    ENNReal.ofReal F • (volume.restrict (pcnBox d R))
      ≤ (volume.restrict (pcnBox d R)).withDensity
          (fun y => ENNReal.ofReal (pcnDensity c s ρ x y)) := by
  rw [← withDensity_const]
  refine withDensity_mono ?_
  filter_upwards [ae_restrict_mem (measurableSet_pcnBox R)] with y hy
  exact ENNReal.ofReal_le_ofReal (hle y hy)

/-- **The continuum Doeblin minorant, at the architecture's numbers.**  On the box `|xᵢ| ≤ R`,
`|yᵢ| ≤ R` the proposal measure dominates `(2πs)^(−d/2)·exp(−d(R(1+ρ))²/s)` times Lebesgue, with
`s = 2σ²(1 − ρ²)` — §1's floor, now as a measure inequality on `ℝ^d`. -/
theorem pcnMeasure_floor {σ ρ R : ℝ} (hσ : 0 < σ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) (hR : 0 ≤ R)
    {x : Fin d → ℝ} (hx : ∀ i, |x i| ≤ R) :
    ENNReal.ofReal
        (pcnNorm d (pcnScale σ ρ) * Real.exp (-((d : ℝ) * (R * (1 + ρ)) ^ 2) / pcnScale σ ρ)) •
        (volume.restrict (pcnBox d R))
      ≤ (volume.restrict (pcnBox d R)).withDensity (fun y =>
          ENNReal.ofReal (pcnDensity (pcnNorm d (pcnScale σ ρ)) (pcnScale σ ρ) ρ x y)) := by
  refine pcnMeasure_minorant (F := pcnNorm d (pcnScale σ ρ)
    * Real.exp (-((d : ℝ) * (R * (1 + ρ)) ^ 2) / pcnScale σ ρ))
    ?_
  intro y hy
  exact pcnGaussian_floor hσ hρ0 hρ1 hR hx (mem_pcnBox.mp hy)

/-- The minorant is positive: the box carries positive proposal mass from every starting point. -/
theorem pcnMeasure_floor_pos {σ ρ R : ℝ} (hσ : 0 < σ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1) :
    0 < ENNReal.ofReal
      (pcnNorm d (pcnScale σ ρ) * Real.exp (-((d : ℝ) * (R * (1 + ρ)) ^ 2) / pcnScale σ ρ)) :=
  ENNReal.ofReal_pos.mpr (pcnGaussian_floor_pos (d := d) hσ hρ0 hρ1)

end BookProof.MCMC.PCNGaussianFloor
