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
  `pcnMeasure_floor_pos`;
* **§3, the Doeblin condition against a named target** — `pcnProposalMeasure`, `pcnTargetMeasure`,
  `pcnTargetMeasure_le_smul`, **`pcnDoeblin`**: `(F/B) • π ≤ P(x, ·)` on the box, for every starting
  point, where `F` is the proposal's floor and `B` the target's ceiling, and **`pcnDoeblin_apply`**
  set by set;
* **§4, the Metropolis acceptance through the density** — `pcnAccept`, `pcnMetropolisDensity`,
  `pcnAccept_le_one`, `pcnMetropolisDensity_le` (the adjusted density is dominated by the raw one),
  **`pcnAccept_floor`** and **`pcnMetropolis_floor`** (the acceptance has a floor when the target's
  density does not drop by more than `m`), and **`pcnMetropolis_minorant`** (the adjusted step's own
  measure minorant);
* **§5, the iterate and the rate** — `pcnIter` (the `n`-step measure on `ℝ^d`),
  `measurable_pcnIter`, `pcnIter_univ`, `pcnStat_iter` (invariance is inherited by the iterates),
  **`pcnIter_rate`** (the Doeblin bound `(1 − (1−c)^n)·μ(A) ≤ (pcnIter K n x)(A)`),
  **`exists_split_of_minorant`** (a probability step dominating `c • μ` splits as
  `c·μ + (1−c)·ν`), **`pcnIter_rate_of_minorant`** (so the minorant alone yields the rate), and
  `pcnMetropolisStep` (the §4 step as a step family);
* **§6, the Metropolis step as a probability** — `pcnProbabilityStep` (accepted density plus its
  rejection atom), **`pcnMetropolisStep_le_pcnProbabilityStep`**,
  **`pcnProbabilityStep_univ`** (mass `1` once the accepted mass is a real in `[0,1]`) and
  **`pcnProbabilityStep_rate`** (the whole chain: minorant → probability step → rate);
* **§7, the increment's mass** — `lintegral_exp_neg_sq_div` (`∫ exp (−(y−a)²/s) = √(π s)`) and
  **`pcnGaussMass_one`** (the normalised increment is a probability density on the line);
* **§8, the increment in `d` dimensions** — `pcnNorm1`, `pcnGaussStep` (`Measure.pi` of the
  coordinate factors), **`pcnGaussStep_univ`** (mass `1` in every dimension) and
  **`pcnExp_factor`** (`exp (−pcnQuad/s)` as the product of its coordinate factors);
* **§9, Fubini and the unconditional probability step** — `integral_pcnFactor`,
  `integral_prod_pcnFactor`, **`pcnGaussMass_d`** and **`pcnGaussMass_quad`** (the increment is a
  probability density on `ℝ^d` in `pcnDensity`'s own form), **`pcnBoxMass_le_one`**,
  **`pcnMetropolisStep_mass_le_one`** and **`pcnAbsorbingStep_univ`** (the Metropolis step with its
  rejection atom is a probability measure, with no mass hypothesis), and — the measurability §5's
  `bind` needs — `measurable_setLIntegral`, `measurable_withDensity_uncurry`,
  **`measurable_pcnMetropolisStep`**, `measurable_rejection` and **`measurable_pcnAbsorbingStep`**;
* **§10, the minorant for the step** — `pcnMetropolisStep_le_pcnAbsorbingStep` and
  **`pcnAbsorbingStep_minorant`**: `(mF/B) • π ≤ pcnAbsorbingStep` on the box, the Doeblin minorant
  for the step the chain takes;
* **§11, the return mass** — `pcnBox_volume` (`(2R)^d`), `withDensity_box_ge`,
  `pcnProposalMeasure_box_ge`, `pcnMetropolisStep_box_ge` and **`pcnAbsorbingStep_box_ge`**: the
  step puts at least `F · (2R)^d` of mass back in the box — for starts inside the box;
* **§12, small-set Doeblin, and the gap it does not close** — `bind_minorant_of_set` and
  **`pcnAbsorbingStep_twoStep_minorant`** (two steps dominate the target *given* a return
  estimate at every starting point), with the explicit note that §11 supplies that estimate only
  inside the box.
* **§13, confinement** — `pcnSumSq`, **`pcnQuad_le_of_mem_box`**
  (`pcnQuad ρ x y ≤ 2ρ²‖x‖² + 2dR²` on the box, for *every* start), `pcnDensity_start_floor`,
  `pcnReturnConst`, **`pcnProposalMeasure_box_ge_start`** and
  **`pcnAbsorbingStep_box_ge_start`**: the return mass from an arbitrary start, decaying like
  `exp (−2ρ²‖x‖²/s)` — §12's hypothesis, discharged start by start;
* **§14, reversibility** — `pcnPrior` (the Gaussian the increment leaves alone),
  **`pcnPrior_mul_density_comm`** (`pcnPrior x · q_x(y) = pcnPrior y · q_y(x)`),
  **`pcnMetropolisDensity_detailed`** (`τ · pcnPrior`, not `τ`, is the reversible reference for
  `min 1 (τ y/τ x)`) and **`pcnPrior_ne_one`** — the factor is not constant, so §3–§13's named
  target is the symmetric-proposal one;
* **§15, confinement** — `pcnAbsorbingStep_eq_zero_of_disjoint`, **`pcnAbsorbingStep_confined`**
  (`K x (box ∪ {x})ᶜ = 0`), `bind_eq_zero_of_support`, **`pcnIter_confined`**,
  `pcnSumSq_le_of_mem_box`, **`pcnIter_confined_ball`** (`‖z‖² ≤ max (dR²) ‖x‖²`),
  `pcnBallConst`, **`pcnAbsorbingStep_box_ge_ball`** (the return mass is one number on each ball of
  starts) and **`pcnAbsorbingStep_twoStep_minorant_ball`**;
* **§16, the reversible reference restated** — `pcnPriorTarget`
  (`volume.withDensity (τ · pcnPrior)`), **`pcnAbsorbingStep_minorant_prior`** and
  **`pcnAbsorbingStep_rate_prior`**;
* **§17, detailed balance into stationarity** — `doeblinStep`,
  **`bind_doeblinStep_stationary`** (Tonelli on the symmetric joint density: detailed balance plus a
  forward-mass bound give `π.bind K = π`), `measurable_setLIntegral`,
  `measurable_doeblinStep_apply`, **`pcnPriorTarget_stationary`** (the pCN instance) and
  **`pcnAbsorbingStep_rate_prior_of_stationary`** (the rate with invariance proved);
* **§18, the constants computed** — `pcnGaussLike` (a Gaussian likelihood), its ceiling
  **`pcnGaussLike_mul_pcnPrior_le_one`** (`B = 1`), its box floors `pcnGaussLike_floor`,
  `pcnPrior_floor`, and **`pcnAbsorbingStep_minorant_prior_gaussLike`**: §16's minorant with
  `B = 1` and `m = exp (−β dR²)` substituted;
* **§19, the reference's mass, and the probability hypothesis discharged** — `pcnPriorMass`
  (`pcnPriorTarget univ`, `pcnPriorMass_eq_lintegral`), **`pcnPriorMass_le`**,
  `pcnPriorMass_ne_top`, **`pcnPriorMass_pos`**, `pcnPriorProb` (the normalised reference) with
  **`pcnPriorProb_univ`** and `isProbabilityMeasure_pcnPriorProb`,
  **`pcnPriorProb_stationary`**, **`pcnPriorProb_minorant_of_target`** and
  **`pcnAbsorbingStep_rate_prob`** — the rate with `IsProbabilityMeasure` proved rather than
  assumed.  The mass is *not* one, and §19 says so: it is the box integral, bounded above by
  `(2R)^d` and below by a floor on the box.
* **§20, one number at every start — and where that is impossible** —
  **`pcnBallConst_no_uniform_floor`** (`ρ ≠ 0`: the ball constant tends to `0`, so §15's estimate
  has no start-uniform form), and at `ρ = 0` the opposite: `pcnReturnConst_zero`,
  **`pcnAbsorbingStep_box_ge_uniform`** and **`pcnAbsorbingStep_twoStep_minorant_uniform`**, a
  two-step minorant at one constant with no ball hypothesis at all;
* **§21, the reference's mass in closed form** — `gaussLike_mul_prior_eq_prod`,
  `box_integral_prod` and **`pcnPriorMass_gaussLike_eq`**: for the Gaussian likelihood the box
  integral is `(∫_{−R}^{R} exp (−κt²) dt)^d` with `κ = β + (1 − ρ²)/s`, with `boxInt_le_sqrt` and
  **`pcnPriorMass_gaussLike_le_sqrt`** bounding it by `(√(π/κ))^d`.

## Honest boundary

This is a *density* floor and the measure inequality it implies on a box — not a full Doeblin
theorem on the continuum.  §22–§26's machinery is stated on a finite state space, and the weight
space is not one.  What §2 adds is that the floor is a statement about the *proposal measure* on
`ℝ^d`, uniformly in the starting point, which is the form a minorant consumes; what it does not do
is name the target measure on `ℝ^d`, pass the Metropolis filter through the density, or produce a
rate — §3–§5 do all three, and the rate is the classical `1 − (1 − c)^n` — but the step family
the rate applies to must be a family of probability measures — §6 builds that family (accepted
density plus rejection atom) and proves its mass is `1`.  What stays open is the *value* of the
accepted mass: an integral of §4's density that the chapter does not compute.  Reversibility is now
proved as the pointwise identity of §14, and that is also the finding: the pCN increment is not
symmetric, so the measure `τ` of §3–§13 must be read as a likelihood against the prior `pcnPrior`,
and the target those sections name is the symmetric-proposal one.  Turning detailed balance into
stationarity is done in §17 — Tonelli on the symmetric joint density, with the accepted mass and the
rejection atom adding to the target — and §15 shows the chain never leaves `box ∪ {x}`, so §13's
decaying constant is one number on each ball of starts.
-/

noncomputable section

namespace BookProof.MCMC.PCNGaussianFloor

open Finset Filter MeasureTheory

open scoped Topology

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

/-! ## 3. The Doeblin condition against a named target on `ℝ^d`

§2 bounds the proposal's mass on the box.  What a Doeblin contraction consumes is a comparison with
the *target*, so this section names it: a target measure `τ` on `ℝ^d`, bounded above by `B` on the
box, and a proposal bounded below by `F` there, give `(F/B) • π ≤ P(x, ·)` — the minorant
`PositivityCone` states as `Minorant` on a finite state space, now on `ℝ^d` with both measures
named.

* `pcnProposalMeasure c s ρ R x` — the proposal as a measure on the box, `volume.withDensity` of
  §1's density;
* `pcnTargetMeasure R τ` — the named target, `volume.withDensity` of the density `τ`, restricted to
  the box;
* **`pcnTargetMeasure_le_smul`** — a bound `τ ≤ B` on the box gives `π ≤ B • volume.restrict box`;
* **`pcnDoeblin`** — the two bounds together: `(F/B) • π ≤ P(x, ·)` for *every* starting point `x`
  in the box, with `smul_measure_mono` and `ofReal_div_mul_ofReal` the only measure algebra
  needed.
-/

/-- The pCN proposal, as a measure on the box: the density of §1 against Lebesgue there. -/
def pcnProposalMeasure (c s ρ R : ℝ) (x : Fin d → ℝ) : Measure (Fin d → ℝ) :=
  (volume.restrict (pcnBox d R)).withDensity fun y => ENNReal.ofReal (pcnDensity c s ρ x y)

/-- The named target on `ℝ^d`: a density `τ` against Lebesgue restricted to the box. -/
def pcnTargetMeasure (R : ℝ) (τ : (Fin d → ℝ) → ℝ) : Measure (Fin d → ℝ) :=
  (volume.restrict (pcnBox d R)).withDensity fun y => ENNReal.ofReal (τ y)

theorem pcnTargetMeasure_le_smul {R B : ℝ} {τ : (Fin d → ℝ) → ℝ}
    (hτB : ∀ y ∈ pcnBox d R, τ y ≤ B) :
    pcnTargetMeasure (d := d) R τ ≤ ENNReal.ofReal B • (volume.restrict (pcnBox d R)) := by
  rw [pcnTargetMeasure, ← withDensity_const]
  refine withDensity_mono ?_
  filter_upwards [ae_restrict_mem (measurableSet_pcnBox (d := d) R)] with y hy
  exact ENNReal.ofReal_le_ofReal (hτB y hy)

theorem smul_measure_mono {α : Type*} [MeasurableSpace α] {μ ν : Measure α} {a : ENNReal}
    (h : μ ≤ ν) : a • μ ≤ a • ν := by
  refine Measure.le_iff.mpr fun s hs => ?_
  rw [Measure.smul_apply, Measure.smul_apply]
  exact mul_le_mul_right (h s) a

theorem ofReal_div_mul_ofReal {F B : ℝ} (hF : 0 ≤ F) (hB : 0 < B) :
    ENNReal.ofReal (F / B) * ENNReal.ofReal B = ENNReal.ofReal F := by
  rw [← ENNReal.ofReal_mul (by positivity)]
  congr 1
  field_simp

/-- **The Doeblin condition against a named target on `ℝ^d`.**  If the target's density is at most
`B` on the box and the proposal's density is at least `F` there, then the proposal dominates
`F/B` times the target — the minorant a Doeblin contraction consumes, with the target named. -/
theorem pcnDoeblin {c s ρ R F B : ℝ} {τ : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hF : 0 ≤ F) (hB : 0 < B) (hτB : ∀ y ∈ pcnBox d R, τ y ≤ B)
    (hle : ∀ y ∈ pcnBox d R, F ≤ pcnDensity c s ρ x y) :
    ENNReal.ofReal (F / B) • pcnTargetMeasure (d := d) R τ
      ≤ pcnProposalMeasure (d := d) c s ρ R x := by
  have hπ : pcnTargetMeasure (d := d) R τ ≤ ENNReal.ofReal B • (volume.restrict (pcnBox d R)) :=
    pcnTargetMeasure_le_smul hτB
  have hμ : ENNReal.ofReal F • (volume.restrict (pcnBox d R))
      ≤ pcnProposalMeasure (d := d) c s ρ R x := pcnMeasure_minorant hle
  calc ENNReal.ofReal (F / B) • pcnTargetMeasure (d := d) R τ
      ≤ ENNReal.ofReal (F / B) • (ENNReal.ofReal B • (volume.restrict (pcnBox d R))) :=
        smul_measure_mono hπ
    _ = ENNReal.ofReal F • (volume.restrict (pcnBox d R)) := by
        rw [smul_smul, ofReal_div_mul_ofReal hF hB]
    _ ≤ pcnProposalMeasure (d := d) c s ρ R x := hμ



/-! ## 4. The Metropolis acceptance through the density

§3 compares the proposal with a named target but assumes the proposal is the raw pCN increment.  The
pCNL step is its Metropolis-adjusted version, so this section carries the acceptance ratio through
the density: the acceptance is a contraction (`pcnAccept_le_one`), so the adjusted density is
*dominated* by the raw one, and — the useful direction — it has a floor of its own whenever the
target's density does not drop too far across the step (`pcnAccept_floor`, `pcnMetropolis_floor`).

* `pcnAccept π x y = min 1 (π y / π x)` — the Metropolis ratio of the pCN proposal;
* `pcnMetropolisDensity` — the accepted density, `pcnAccept · pcnDensity`;
* **`pcnAccept_le_one`**, `pcnAccept_nonneg`, `pcnMetropolisDensity_le` — the acceptance contracts,
  so the adjusted density never exceeds the raw one;
* **`pcnAccept_floor`** — `m·π x ≤ π y` with `m ≤ 1` gives acceptance at least `m`;
* **`pcnMetropolis_floor`** — the two floors multiply: `m·F` on the box;
* **`pcnMetropolis_minorant`** — and that is a measure minorant for the adjusted proposal, so the
  Doeblin condition of §3 holds for the Metropolis-adjusted step as well.
-/

/-- The Metropolis acceptance ratio of the pCN proposal, `min 1 (π y / π x)`. -/
def pcnAccept (π : (Fin d → ℝ) → ℝ) (x y : Fin d → ℝ) : ℝ := min 1 (π y / π x)

/-- The Metropolis-adjusted pCN density on the box: the pCN density times the acceptance. -/
def pcnMetropolisDensity (c s ρ : ℝ) (π : (Fin d → ℝ) → ℝ) (x y : Fin d → ℝ) : ℝ :=
  pcnAccept π x y * pcnDensity c s ρ x y

theorem pcnAccept_le_one (π : (Fin d → ℝ) → ℝ) (x y : Fin d → ℝ) : pcnAccept π x y ≤ 1 :=
  min_le_left _ _

theorem pcnAccept_nonneg {π : (Fin d → ℝ) → ℝ} {x y : Fin d → ℝ} (hx : 0 < π x)
    (hy : 0 ≤ π y) : 0 ≤ pcnAccept π x y :=
  le_min (by norm_num) (div_nonneg hy hx.le)

/-- **The acceptance's floor**: if the target's density does not drop by more than the factor
`m ≤ 1` across the step (`m·π x ≤ π y`), the acceptance is at least `m`. -/
theorem pcnAccept_floor {π : (Fin d → ℝ) → ℝ} {x y : Fin d → ℝ} {m : ℝ} (hm1 : m ≤ 1)
    (hx : 0 < π x) (h : m * π x ≤ π y) : m ≤ pcnAccept π x y := by
  refine le_min hm1 ?_
  rw [le_div_iff₀ hx]
  linarith

/-- The adjusted density never exceeds the raw one. -/
theorem pcnMetropolisDensity_le {c s ρ : ℝ} {π : (Fin d → ℝ) → ℝ} {x y : Fin d → ℝ}
    (hy : 0 ≤ pcnDensity c s ρ x y) :
    pcnMetropolisDensity c s ρ π x y ≤ pcnDensity c s ρ x y :=
  mul_le_of_le_one_left hy (pcnAccept_le_one π x y)

/-- **The adjusted floor**: an acceptance floor `m` and a density floor `F` multiply. -/
theorem pcnMetropolis_floor {c s ρ m F : ℝ} {π : (Fin d → ℝ) → ℝ} {x y : Fin d → ℝ}
    (hm0 : 0 ≤ m) (hF : 0 ≤ F) (hacc : m ≤ pcnAccept π x y)
    (hdens : F ≤ pcnDensity c s ρ x y) :
    m * F ≤ pcnMetropolisDensity c s ρ π x y := by
  unfold pcnMetropolisDensity
  exact mul_le_mul hacc hdens hF (le_trans hm0 hacc)

/-- **The Metropolis-adjusted proposal's measure minorant**: a floor `m·F` on the box for the
adjusted density gives the same measure inequality as §2, for the adjusted step. -/
theorem pcnMetropolis_minorant {c s ρ R m F : ℝ} {π : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hfloor : ∀ y ∈ pcnBox d R, m * F ≤ pcnMetropolisDensity c s ρ π x y) :
    ENNReal.ofReal (m * F) • (volume.restrict (pcnBox d R))
      ≤ (volume.restrict (pcnBox d R)).withDensity
          (fun y => ENNReal.ofReal (pcnMetropolisDensity c s ρ π x y)) := by
  rw [← withDensity_const]
  refine withDensity_mono ?_
  filter_upwards [ae_restrict_mem (measurableSet_pcnBox (d := d) R)] with y hy
  exact ENNReal.ofReal_le_ofReal (hfloor y hy)

/-- The Doeblin condition of §3, read set by set: `(F/B)·π(A) ≤ P(x, A)`. -/
theorem pcnDoeblin_apply {c s ρ R F B : ℝ} {τ : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hF : 0 ≤ F) (hB : 0 < B) (hτB : ∀ y ∈ pcnBox d R, τ y ≤ B)
    (hle : ∀ y ∈ pcnBox d R, F ≤ pcnDensity c s ρ x y) {A : Set (Fin d → ℝ)}
    (hA : MeasurableSet A) :
    ENNReal.ofReal (F / B) * pcnTargetMeasure (d := d) R τ A
      ≤ pcnProposalMeasure (d := d) c s ρ R x A := by
  have h := (Measure.le_iff.mp (pcnDoeblin (d := d) hF hB hτB hle)) A hA
  simpa [Measure.smul_apply, smul_eq_mul] using h
/-! ## 5. The iterate on `ℝ^d`, and the rate §3 yields

§2–§4 are one-step statements.  This section supplies the missing side of them: the *iterate* of a
step family on `ℝ^d` and the Doeblin bound it obeys.

* `pcnIter K n x` — the `n`-step measure, `pcnIter K 0 x = δ_x` and
  `pcnIter K (n+1) x = (K x).bind (pcnIter K n)`; `measurable_pcnIter` keeps it a measurable family
  of measures, as `Measure.bind` requires;
* `pcnIter_univ` — if every step is a probability, so is every iterate;
* `pcnStat_iter` — if the target is invariant under one step it is invariant under all of them;
* **`pcnIter_rate`** — the rate itself: a step family that splits as `c·μ + (1−c)·ν_x` with `ν_x` a
  probability contracts to `μ` as `(1 − (1−c)^n)·μ(A) ≤ (pcnIter K n x)(A)`;
* **`exists_split_of_minorant`** — every probability step dominating `c • μ` with `c < 1` has such a
  split (`Measure.sub` supplies the rest of the mass), so the split is not extra input;
* **`pcnIter_rate_of_minorant`** — hence the minorant alone yields the rate;
* **`pcnMetropolisStep`** — the §4 adjusted step as a step family, the object the rate is about.

## Honest boundary (continued)

The rate is a rate for a probability step family whose measures are the pCN/Metropolis ones; what is
still missing is the normalisation: `pcnMetropolis_minorant` bounds the adjusted *density*, whose
integral the corpus does not compute, so `pcnMetropolisStep` is a finite measure and not yet a
probability.  The invariance hypothesis is stated (it is what a reversibility proof would give), not
proved.
-/

/-- The `n`-step measure of the step family `K`, by right composition: the first step is `K`, then
its own iterate from the point reached. -/
def pcnIter (K : (Fin d → ℝ) → Measure (Fin d → ℝ)) :
    ℕ → (Fin d → ℝ) → Measure (Fin d → ℝ)
  | 0 => fun x => Measure.dirac x
  | n + 1 => fun x => (K x).bind (pcnIter K n)

theorem pcnIter_zero (K : (Fin d → ℝ) → Measure (Fin d → ℝ)) (x : Fin d → ℝ) :
    pcnIter K 0 x = Measure.dirac x := rfl

theorem pcnIter_succ (K : (Fin d → ℝ) → Measure (Fin d → ℝ)) (n : ℕ) (x : Fin d → ℝ) :
    pcnIter K (n + 1) x = (K x).bind (pcnIter K n) := rfl

theorem measurable_pcnIter {K : (Fin d → ℝ) → Measure (Fin d → ℝ)} (hK : Measurable K) :
    ∀ n, Measurable (pcnIter K n)
  | 0 => Measure.measurable_dirac
  | n + 1 => (Measure.measurable_bind' (measurable_pcnIter hK n)).comp hK

/-- Iterates of a probability step family are probability measures. -/
theorem pcnIter_univ {K : (Fin d → ℝ) → Measure (Fin d → ℝ)} (hK : Measurable K)
    (hmass : ∀ x, K x Set.univ = 1) (n : ℕ) (x : Fin d → ℝ) :
    pcnIter K n x Set.univ = 1 := by
  induction n generalizing x with
  | zero => simp [pcnIter]
  | succ n ih =>
      rw [pcnIter_succ, Measure.bind_apply MeasurableSet.univ
        ((measurable_pcnIter hK n).aemeasurable)]
      simp [ih, hmass x]

/-- **Invariance is inherited by the iterates**: a measure stationary for one step is stationary for
every iterate. -/
theorem pcnStat_iter {K : (Fin d → ℝ) → Measure (Fin d → ℝ)} {μ : Measure (Fin d → ℝ)}
    (hK : Measurable K) (hstat : μ.bind K = μ) (n : ℕ) :
    μ.bind (pcnIter K n) = μ := by
  induction n with
  | zero => simp [pcnIter]
  | succ n ih =>
      change μ.bind (fun x => (K x).bind (pcnIter K n)) = μ
      rw [← Measure.bind_bind hK.aemeasurable (measurable_pcnIter hK n).aemeasurable]
      rw [hstat]
      exact ih

/-- **The Doeblin contraction rate on `ℝ^d`.**  If every step splits as `c·μ + (1−c)·ν_x` with `ν_x`
a probability measure, and `μ` is invariant under the iterates, then from any starting point the
`n`-step measure of `A` is at least `(1 − (1−c)^n)·μ(A)` — the classical `1 − (1−c)^n` rate, on the
continuum, for the family `pcnIter` builds. -/
theorem pcnIter_rate {K : (Fin d → ℝ) → Measure (Fin d → ℝ)} {μ : Measure (Fin d → ℝ)}
    {c : ℝ} {ν : (Fin d → ℝ) → Measure (Fin d → ℝ)}
    (hc0 : 0 ≤ c) (hc1 : c ≤ 1) (hK : Measurable K)
    (hν : ∀ x, ν x Set.univ = 1)
    (hsplit : ∀ x, K x = ENNReal.ofReal c • μ + ENNReal.ofReal (1 - c) • ν x)
    (hstat : ∀ n, μ.bind (pcnIter K n) = μ)
    (n : ℕ) (x : Fin d → ℝ) {A : Set (Fin d → ℝ)} (hA : MeasurableSet A) :
    ENNReal.ofReal (1 - (1 - c) ^ n) * μ A ≤ pcnIter K n x A := by
  have hr0 : 0 ≤ 1 - c := by linarith
  have hg : ∀ n, Measurable (pcnIter K n) := measurable_pcnIter hK
  induction n generalizing x with
  | zero => simp [pcnIter]
  | succ n ih =>
      rw [pcnIter_succ, Measure.bind_apply hA (hg n).aemeasurable, hsplit x,
        lintegral_add_measure, lintegral_smul_measure, lintegral_smul_measure]
      have h1 : ∫⁻ y, pcnIter K n y A ∂μ = μ A := by
        rw [← Measure.bind_apply hA (hg n).aemeasurable, hstat n]
      have hpow : (1 - c) ^ n ≤ 1 := pow_le_one₀ hr0 (by linarith)
      have h2 : ENNReal.ofReal (1 - (1 - c) ^ n) * μ A
          ≤ ∫⁻ y, pcnIter K n y A ∂(ν x) := by
        calc ENNReal.ofReal (1 - (1 - c) ^ n) * μ A
            = ∫⁻ _y, ENNReal.ofReal (1 - (1 - c) ^ n) * μ A ∂(ν x) := by
              rw [lintegral_const]
              simp [hν x]
          _ ≤ ∫⁻ y, pcnIter K n y A ∂(ν x) := lintegral_mono fun y => ih y
      rw [h1, smul_eq_mul, smul_eq_mul]
      refine le_trans (le_of_eq ?_) (add_le_add (le_refl _)
        (mul_le_mul_of_nonneg_left h2 (zero_le _)))
      have hkey : 1 - (1 - c) ^ (n + 1) = c + (1 - c) * (1 - (1 - c) ^ n) := by ring
      rw [hkey, ENNReal.ofReal_add hc0 (mul_nonneg hr0 (by linarith)),
        ENNReal.ofReal_mul hr0, add_mul, mul_assoc]

/-- **Every probability step dominating `c • μ` splits as `c·μ + (1−c)·ν`** with `ν` a probability:
the remaining mass `σ − c•μ` is a measure (`Measure.sub`), and rescaling it by `1 − c` normalises
it.  So `pcnIter_rate`'s split is not extra input — a minorant is enough. -/
theorem exists_split_of_minorant {α : Type*} [MeasurableSpace α] {μ σ : Measure α}
    [IsProbabilityMeasure μ] [IsProbabilityMeasure σ] {c : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) (h : ENNReal.ofReal c • μ ≤ σ) :
    ∃ ν : Measure α, σ = ENNReal.ofReal c • μ + ENNReal.ofReal (1 - c) • ν ∧
      ν Set.univ = 1 := by
  haveI : IsFiniteMeasure (ENNReal.ofReal c • μ) :=
    ⟨by rw [Measure.smul_apply, smul_eq_mul, measure_univ, mul_one]
        exact ENNReal.ofReal_ne_top.lt_top⟩
  set a : ENNReal := ENNReal.ofReal (1 - c) with ha
  have hsub : (1 : ENNReal) - ENNReal.ofReal c = a := by
    rw [ha, ← ENNReal.ofReal_one, ← ENNReal.ofReal_sub 1 (le_of_lt hc0)]
  have hne : a ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith : (0 : ℝ) < 1 - c)).ne'
  have htop : a ≠ ⊤ := ENNReal.ofReal_ne_top
  set r : Measure α := σ - ENNReal.ofReal c • μ with hr
  have hmassr : r Set.univ = a := by
    rw [hr, Measure.sub_apply MeasurableSet.univ h, Measure.smul_apply, smul_eq_mul,
      measure_univ, measure_univ, mul_one, hsub]
  have hsum : r + ENNReal.ofReal c • μ = σ := by
    rw [hr]
    exact Measure.sub_add_cancel_of_le h
  refine ⟨a⁻¹ • r, ?_, ?_⟩
  · have hsmul : a • (a⁻¹ • r) = r := by
      rw [smul_smul, ENNReal.mul_inv_cancel hne htop, one_smul]
    calc σ = r + ENNReal.ofReal c • μ := hsum.symm
      _ = ENNReal.ofReal c • μ + a • (a⁻¹ • r) := by rw [hsmul, add_comm]
  · rw [Measure.smul_apply, smul_eq_mul, hmassr]
    exact ENNReal.inv_mul_cancel hne htop

/-- **The minorant alone yields the rate**: a measurable probability step family dominating `c • μ`
at every point, with `μ` invariant under its iterates and `0 < c < 1`, satisfies the Doeblin bound
`(1 − (1−c)^n)·μ(A) ≤ (pcnIter K n x)(A)`. -/
theorem pcnIter_rate_of_minorant {K : (Fin d → ℝ) → Measure (Fin d → ℝ)}
    {μ : Measure (Fin d → ℝ)} {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hK : Measurable K)
    (hmass : ∀ x, K x Set.univ = 1) [IsProbabilityMeasure μ]
    (hmin : ∀ x, ENNReal.ofReal c • μ ≤ K x)
    (hstat : ∀ n, μ.bind (pcnIter K n) = μ)
    (n : ℕ) (x : Fin d → ℝ) {A : Set (Fin d → ℝ)} (hA : MeasurableSet A) :
    ENNReal.ofReal (1 - (1 - c) ^ n) * μ A ≤ pcnIter K n x A := by
  haveI : ∀ x, IsProbabilityMeasure (K x) := fun x => ⟨hmass x⟩
  choose ν hsplit hνmass using fun x => exists_split_of_minorant hc0 hc1 (hmin x)
  exact pcnIter_rate hc0.le hc1.le hK hνmass hsplit hstat n x hA

/-- The Metropolis-adjusted pCN step of §4 as a step family on `ℝ^d`: the measure the rate of this
section is about. -/
def pcnMetropolisStep (c s ρ R : ℝ) (π : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    Measure (Fin d → ℝ) :=
  (volume.restrict (pcnBox d R)).withDensity
    fun y => ENNReal.ofReal (pcnMetropolisDensity c s ρ π x y)


/-! ## 6. The Metropolis step as a probability measure

§5's rate applies to a family of *probability* measures; §4's adjusted step is a density on a box
and carries no rejection mass.  This section supplies the missing part: the Metropolis step is the
accepted density plus the atom at the starting point holding the mass that was rejected, and *that*
is a probability measure — with one analytic input, the accepted mass `A x`.

* `pcnProbabilityStep` — `accepted density + (1 − A x)·δ_x`;
* **`pcnMetropolisStep_le_pcnProbabilityStep`** — the accepted part is dominated by the full step,
  so a minorant for the accepted part is one for the step;
* **`pcnProbabilityStep_univ`** — if the accepted part's mass is `A x ∈ [0,1]`, the step's total
  mass is `1`;
* **`pcnProbabilityStep_rate`** — the assembly: §4's minorant plus §6's normalisation plus §5's
  contraction give the `1 − (1−c)^n` bound for the Metropolis step.
-/

/-- The Metropolis-adjusted pCN step of §4 *with its rejection atom*: the accepted density plus the
rejected mass as an atom at the starting point.  This is the step a chain actually takes. -/
def pcnProbabilityStep (c s ρ R : ℝ) (π : (Fin d → ℝ) → ℝ)
    (A : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : Measure (Fin d → ℝ) :=
  pcnMetropolisStep c s ρ R π x + ENNReal.ofReal (1 - A x) • Measure.dirac x

/-- The rejection atom only adds mass: the accepted part is dominated by the full step, so any
minorant of the accepted part is a minorant of the step. -/
theorem pcnMetropolisStep_le_pcnProbabilityStep (c s ρ R : ℝ) (π : (Fin d → ℝ) → ℝ)
    (A : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    pcnMetropolisStep c s ρ R π x ≤ pcnProbabilityStep c s ρ R π A x := by
  rw [pcnProbabilityStep]
  exact Measure.le_add_right (le_refl _)

/-- **The Metropolis step is a probability measure.**  If the accepted part has mass `A x`, real and
in `[0,1]`, then accepted and rejected masses add to `1`.  The normalisation is therefore
bookkeeping; what is analytic is the value of `A`, i.e. the integral of the accepted density. -/
theorem pcnProbabilityStep_univ {c s ρ R : ℝ} {π : (Fin d → ℝ) → ℝ}
    {A : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hmass : (pcnMetropolisStep c s ρ R π x) Set.univ = ENNReal.ofReal (A x))
    (hA0 : 0 ≤ A x) (hA1 : A x ≤ 1) :
    pcnProbabilityStep c s ρ R π A x Set.univ = 1 := by
  rw [pcnProbabilityStep, Measure.add_apply, hmass, Measure.smul_apply,
    Measure.dirac_apply' x MeasurableSet.univ, Set.indicator_of_mem (Set.mem_univ x),
    Pi.one_apply, smul_eq_mul, mul_one]
  rw [← ENNReal.ofReal_add hA0 (by linarith), show A x + (1 - A x) = 1 by ring,
    ENNReal.ofReal_one]

/-- **The pCN rate, end to end.**  The accepted density of §4 together with its rejection atom is a
probability measure, the accepted part's minorant transfers to it, and §5's contraction yields the
`1 − (1−c)^n` bound for the Metropolis step itself.  What remains as hypothesis is the accepted mass
`A` (an integral of §4's density) and the invariance of `π` under the step. -/
theorem pcnProbabilityStep_rate {c s ρ R m : ℝ} {τ : (Fin d → ℝ) → ℝ}
    {π : Measure (Fin d → ℝ)} {A : (Fin d → ℝ) → ℝ}
    (hm0 : 0 < m) (hm1 : m < 1)
    (hmeas : Measurable (pcnProbabilityStep c s ρ R τ A))
    (hAc : ∀ x, (pcnMetropolisStep c s ρ R τ x) Set.univ = ENNReal.ofReal (A x))
    (hA0 : ∀ x, 0 ≤ A x) (hA1 : ∀ x, A x ≤ 1) [IsProbabilityMeasure π]
    (hmin : ∀ x, ENNReal.ofReal m • π ≤ pcnMetropolisStep c s ρ R τ x)
    (hstat : ∀ n, π.bind (pcnIter (pcnProbabilityStep c s ρ R τ A) n) = π)
    (n : ℕ) (x : Fin d → ℝ) {S : Set (Fin d → ℝ)} (hS : MeasurableSet S) :
    ENNReal.ofReal (1 - (1 - m) ^ n) * π S
      ≤ pcnIter (pcnProbabilityStep c s ρ R τ A) n x S := by
  refine pcnIter_rate_of_minorant hm0 hm1 hmeas ?_ ?_ hstat n x hS
  · intro x
    exact pcnProbabilityStep_univ (hAc x) (hA0 x) (hA1 x)
  · intro x
    exact le_trans (hmin x) (pcnMetropolisStep_le_pcnProbabilityStep c s ρ R τ A x)


/-! ## 7. The increment's mass: the one-dimensional normalisation

§6's step is a probability measure once the accepted mass is known to be at most `1`; that bound
is an integral of the accepted density.  This section computes the first such integral — the mass of
the *unnormalised* increment on the line:

* **`lintegral_exp_neg_sq_div`** — `∫ exp (−(y − a)²/s) dy = √(π s)` for `s > 0`;
* **`pcnGaussMass_one`** — the normalised increment `(√(π s))⁻¹ exp (−(y − a)²/s)` is a probability
  density on `ℝ`.

The `d`-dimensional statement is the product of these over the coordinates — `Measure.pi` and
Fubini — and is not written out here; nor is the *box-restricted, acceptance-weighted* integral that
§6's `A` actually is.
-/

/-- **The one-dimensional Gaussian integral in the pCN's own scaling**: for `s > 0`,
`∫ exp (−(y − a)²/s) dy = √(π s)`. -/
theorem lintegral_exp_neg_sq_div {s : ℝ} (hs : 0 < s) (a : ℝ) :
    ∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-((y - a) ^ 2) / s))
      = ENNReal.ofReal (Real.sqrt (Real.pi * s)) := by
  set v : NNReal := ⟨s / 2, by positivity⟩ with hvdef
  have hvcast : (v : ℝ) = s / 2 := rfl
  have hvc : (v : ℝ) ≠ 0 := by rw [hvcast]; positivity
  have hv : v ≠ 0 := fun h => hvc (by rw [h]; rfl)
  have hgauss : ∫⁻ y : ℝ,
      ENNReal.ofReal (ProbabilityTheory.gaussianPDFReal a v y) = 1 :=
    ProbabilityTheory.lintegral_gaussianPDF_eq_one a hv
  have hpt : ∀ y : ℝ, ENNReal.ofReal (Real.exp (-((y - a) ^ 2) / s))
      = ENNReal.ofReal (Real.sqrt (Real.pi * s))
        * ENNReal.ofReal (ProbabilityTheory.gaussianPDFReal a v y) := by
    intro y
    have h2 : (2 : ℝ) * (v : ℝ) = s := by rw [hvcast]; ring
    have hsq : Real.sqrt (2 * Real.pi * (v : ℝ)) = Real.sqrt (Real.pi * s) := by
      rw [show 2 * Real.pi * (v : ℝ) = Real.pi * s from by
        calc 2 * Real.pi * (v : ℝ) = Real.pi * (2 * (v : ℝ)) := by ring
          _ = Real.pi * s := by rw [h2]]
    rw [ProbabilityTheory.gaussianPDFReal, hsq, show -((y - a) ^ 2) / (2 * (v : ℝ))
      = -((y - a) ^ 2) / s by rw [h2], ← ENNReal.ofReal_mul (Real.sqrt_nonneg _)]
    congr 1
    field_simp
  calc ∫⁻ y : ℝ, ENNReal.ofReal (Real.exp (-((y - a) ^ 2) / s))
      = ∫⁻ y : ℝ, ENNReal.ofReal (Real.sqrt (Real.pi * s))
          * ENNReal.ofReal (ProbabilityTheory.gaussianPDFReal a v y) := by
        simp_rw [hpt]
    _ = ENNReal.ofReal (Real.sqrt (Real.pi * s)) * 1 := by
        rw [lintegral_const_mul _ (by fun_prop), hgauss]
    _ = ENNReal.ofReal (Real.sqrt (Real.pi * s)) := mul_one _

/-- **The normalised pCN increment is a probability density on the line**: with `s > 0`,
`(√(π s))⁻¹ exp (−(y − a)²/s)` integrates to `1`. -/
theorem pcnGaussMass_one {s : ℝ} (hs : 0 < s) (a : ℝ) :
    (volume.withDensity fun y : ℝ => ENNReal.ofReal
        ((Real.sqrt (Real.pi * s))⁻¹ * Real.exp (-((y - a) ^ 2) / s))) Set.univ = 1 := by
  rw [withDensity_apply _ MeasurableSet.univ]
  have hc : 0 ≤ (Real.sqrt (Real.pi * s))⁻¹ := by positivity
  have hsplit : ∀ y : ℝ,
      ENNReal.ofReal ((Real.sqrt (Real.pi * s))⁻¹ * Real.exp (-((y - a) ^ 2) / s))
        = ENNReal.ofReal ((Real.sqrt (Real.pi * s))⁻¹)
          * ENNReal.ofReal (Real.exp (-((y - a) ^ 2) / s)) := by
    intro y
    exact ENNReal.ofReal_mul hc
  simp_rw [hsplit, setLIntegral_univ]
  rw [lintegral_const_mul _ (by fun_prop), lintegral_exp_neg_sq_div hs a]
  rw [← ENNReal.ofReal_mul hc,
    inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (mul_pos Real.pi_pos hs))), ENNReal.ofReal_one]


/-! ## 8. The increment's mass in `d` dimensions

§7 integrates the increment on the line.  In `d` dimensions the increment is the product of its
coordinate factors — `pcnExp_factor` writes `exp (−pcnQuad/s)` as that product — and the product of
probability densities is a probability:

* `pcnNorm1` — the one-dimensional constant `(√(π s))⁻¹`;
* **`pcnGaussStep`** — the increment as `Measure.pi` of the normalised coordinate factors;
* **`pcnGaussStep_univ`** — its total mass is `1`: `Measure.pi_univ` reduces the statement to §7 at
  each coordinate;
* **`pcnExp_factor`** — `exp (−pcnQuad ρ x y / s) = ∏ᵢ exp (−(yᵢ − ρxᵢ)²/s)`, so the product measure
  is the one whose density is `pcnDensity` with the constant `pcnNorm1` raised to the number of
  coordinates.

What this section does *not* write is the identification of `Measure.pi` of the coordinate densities
with `withDensity` of their product over Lebesgue measure — a Fubini identity — so `pcnGaussStep` is
stated as the product measure rather than as `pcnProposalMeasure`.
-/

/-- The one-dimensional normalising constant `(√(π s))⁻¹` of the pCN increment. -/
def pcnNorm1 (s : ℝ) : ℝ := (Real.sqrt (Real.pi * s))⁻¹

/-- The `d`-dimensional pCN increment, as the product over the coordinates of the normalised
one-dimensional factors. -/
def pcnGaussStep (s ρ : ℝ) (x : Fin d → ℝ) : Measure (Fin d → ℝ) :=
  Measure.pi fun i => volume.withDensity
    (fun t : ℝ => ENNReal.ofReal (pcnNorm1 s * Real.exp (-((t - ρ * x i) ^ 2) / s)))

/-- **The increment is a probability measure in `d` dimensions**: the product over the
coordinates of the normalised factors has total mass `1`, because each factor is a probability
(§7). -/
theorem pcnGaussStep_univ {s ρ : ℝ} (hs : 0 < s) (x : Fin d → ℝ) :
    pcnGaussStep (d := d) s ρ x Set.univ = 1 := by
  haveI : ∀ i, SigmaFinite (volume.withDensity
      (fun t : ℝ => ENNReal.ofReal (pcnNorm1 s * Real.exp (-((t - ρ * x i) ^ 2) / s)))) :=
    fun i => inferInstance
  rw [pcnGaussStep, Measure.pi_univ]
  refine Finset.prod_eq_one fun i _ => ?_
  simpa [pcnNorm1] using pcnGaussMass_one hs (ρ * x i)

/-- **The pCN exponent factors over the coordinates**:
`exp (−pcnQuad ρ x y / s) = ∏ᵢ exp (−(yᵢ − ρxᵢ)²/s)`, so the product measure of the last
definition is the one carrying the pCN density, up to the constant. -/
theorem pcnExp_factor (s ρ : ℝ) (x y : Fin d → ℝ) :
    Real.exp (-(pcnQuad ρ x y) / s) = ∏ i, Real.exp (-((y i - ρ * x i) ^ 2) / s) := by
  rw [pcnQuad, ← Real.exp_sum]
  congr 1
  rw [← Finset.sum_neg_distrib, ← Finset.sum_div]


/-! ## 9. Fubini, and the Metropolis step as a probability with no mass hypothesis

§8 stated the increment as a product measure and left the identification with `withDensity` open.
This section closes it, using Mathlib's `integral_fintype_prod_eq_prod` rather than a bespoke
induction:

* `exp_eq_sqrt_mul_gaussianPDFReal`, `pcnFactor_eq_gaussianPDFReal` — each coordinate factor is
  Mathlib's Gaussian density at variance `s/2`;
* **`integral_pcnFactor`** — each factor integrates to `1`;
* **`integral_prod_pcnFactor`** — the product of the factors integrates to `1` over
  `Measure.pi`/Lebesgue on `Fin d → ℝ`;
* **`pcnGaussMass_d`** — hence `withDensity` of the product density has mass `1` (the Fubini
  identification, in the form the chapter's own definitions use);
* **`pcnGaussMass_quad`** — the same in `pcnDensity`'s form: with `c = (√(π s))^d` the increment
  is a probability density on `ℝ^d`;
* **`pcnBoxMass_le_one`** — restricted to the box, its mass is at most `1`;
* **`pcnMetropolisStep_le_proposal`**, **`pcnMetropolisStep_mass_le_one`** — the
  Metropolis-adjusted step is dominated by the increment, so its accepted mass is at most `1`,
  *with no hypothesis on the target*;
* `pcnAbsorbingStep`, **`pcnAbsorbingStep_univ`** — and with its rejection atom the pCNL Metropolis
  step is a probability measure, unconditionally.

What is still missing is invariance of the target under the step (a reversibility proof), and the
minormant's ceiling on the target's density — neither of which is a normalisation statement.
-/


/-- The coordinate factor of the pCN increment is `√(π s)` times Mathlib's Gaussian density at
variance `s/2`. -/
theorem exp_eq_sqrt_mul_gaussianPDFReal {s : ℝ} (hs : 0 < s) (a t : ℝ) :
    Real.exp (-((t - a) ^ 2) / s)
      = Real.sqrt (Real.pi * s)
        * ProbabilityTheory.gaussianPDFReal a ⟨s / 2, le_of_lt (by positivity)⟩ t := by
  set v : NNReal := ⟨s / 2, le_of_lt (by positivity)⟩ with hvdef
  have hvcast : (v : ℝ) = s / 2 := rfl
  have h2 : (2 : ℝ) * (v : ℝ) = s := by rw [hvcast]; ring
  have hsq : Real.sqrt (2 * Real.pi * (v : ℝ)) = Real.sqrt (Real.pi * s) := by
    rw [show 2 * Real.pi * (v : ℝ) = Real.pi * s from by
      calc 2 * Real.pi * (v : ℝ) = Real.pi * (2 * (v : ℝ)) := by ring
        _ = Real.pi * s := by rw [h2]]
  have hspos : 0 < Real.sqrt (Real.pi * s) := Real.sqrt_pos.mpr (mul_pos Real.pi_pos hs)
  rw [ProbabilityTheory.gaussianPDFReal, hsq,
    show -((t - a) ^ 2) / (2 * (v : ℝ)) = -((t - a) ^ 2) / s by rw [h2]]
  field_simp

/-- The coordinate factor as Mathlib's Gaussian density at variance `s/2`. -/
theorem pcnFactor_eq_gaussianPDFReal {s : ℝ} (hs : 0 < s) (a t : ℝ) :
    pcnNorm1 s * Real.exp (-((t - a) ^ 2) / s)
      = ProbabilityTheory.gaussianPDFReal a ⟨s / 2, le_of_lt (by positivity)⟩ t := by
  rw [exp_eq_sqrt_mul_gaussianPDFReal hs a t, pcnNorm1, ← mul_assoc,
    inv_mul_cancel₀ (ne_of_gt (Real.sqrt_pos.mpr (mul_pos Real.pi_pos hs))), one_mul]

/-- Each coordinate factor integrates to `1`. -/
theorem integral_pcnFactor {s : ℝ} (hs : 0 < s) (a : ℝ) :
    ∫ t : ℝ, pcnNorm1 s * Real.exp (-((t - a) ^ 2) / s) = 1 := by
  have hv : (⟨s / 2, le_of_lt (by positivity)⟩ : NNReal) ≠ 0 := by
    intro h
    have hc : ((⟨s / 2, le_of_lt (by positivity)⟩ : NNReal) : ℝ) = 0 := by rw [h]; rfl
    have hpos : (0 : ℝ) < ((⟨s / 2, le_of_lt (by positivity)⟩ : NNReal) : ℝ) := by positivity
    linarith
  simp_rw [pcnFactor_eq_gaussianPDFReal hs a]
  exact ProbabilityTheory.integral_gaussianPDFReal_eq_one a hv


/-- **Fubini over `Measure.pi`**: the product of the coordinate factors integrates to the product of
their integrals — here, to `1`. -/
theorem integral_prod_pcnFactor {s ρ : ℝ} (hs : 0 < s) (x : Fin d → ℝ) :
    ∫ y : Fin d → ℝ, ∏ i, pcnNorm1 s * Real.exp (-((y i - ρ * x i) ^ 2) / s) = 1 := by
  rw [integral_fintype_prod_volume_eq_prod (E := fun _ => ℝ)
    (f := fun i t => pcnNorm1 s * Real.exp (-((t - ρ * x i) ^ 2) / s))]
  simp [integral_pcnFactor hs]

/-- **The increment as a density in `d` dimensions integrates to `1`.** -/
theorem pcnGaussMass_d {s ρ : ℝ} (hs : 0 < s) (x : Fin d → ℝ) :
    (volume.withDensity fun y : Fin d → ℝ =>
      ENNReal.ofReal (∏ i, pcnNorm1 s * Real.exp (-((y i - ρ * x i) ^ 2) / s)))
      Set.univ = 1 := by
  rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
  have hInt : Integrable (fun y : Fin d → ℝ =>
      ∏ i, pcnNorm1 s * Real.exp (-((y i - ρ * x i) ^ 2) / s)) := by
    have h := Integrable.fintype_prod (ι := Fin d) (E := ℝ) (𝕜 := ℝ)
      (μ := fun _ => (volume : Measure ℝ))
      (f := fun i t => pcnNorm1 s * Real.exp (-((t - ρ * x i) ^ 2) / s))
      (fun i => (ProbabilityTheory.integrable_gaussianPDFReal (ρ * x i)
        ⟨s / 2, le_of_lt (by positivity)⟩).congr
        (Filter.Eventually.of_forall fun t => (pcnFactor_eq_gaussianPDFReal hs (ρ * x i) t).symm))
    simpa using h
  have hnn : 0 ≤ᵐ[volume] (fun y : Fin d → ℝ =>
      ∏ i, pcnNorm1 s * Real.exp (-((y i - ρ * x i) ^ 2) / s)) :=
    Filter.Eventually.of_forall fun y =>
      Finset.prod_nonneg fun i _ =>
        mul_nonneg (by simp only [pcnNorm1]; positivity) (Real.exp_pos _).le
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hInt hnn, integral_prod_pcnFactor hs x]
  norm_num


/-- **The increment in `pcnDensity`'s own form** integrates to `1`: with `c = (√(π s))^d` the
density `pcnDensity c s ρ x` is a probability density. -/
theorem pcnGaussMass_quad {s ρ : ℝ} (hs : 0 < s) (x : Fin d → ℝ) :
    (volume.withDensity fun y : Fin d → ℝ =>
      ENNReal.ofReal (pcnNorm1 s ^ d * Real.exp (-(pcnQuad ρ x y) / s))) Set.univ = 1 := by
  have h : ∀ y : Fin d → ℝ, (∏ i, pcnNorm1 s * Real.exp (-((y i - ρ * x i) ^ 2) / s))
      = pcnNorm1 s ^ d * Real.exp (-(pcnQuad ρ x y) / s) := by
    intro y
    rw [pcnExp_factor s ρ x y, Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ,
      Fintype.card_fin]
  have hfun : (fun y : Fin d → ℝ =>
        ENNReal.ofReal (pcnNorm1 s ^ d * Real.exp (-(pcnQuad ρ x y) / s)))
      = fun y : Fin d → ℝ =>
        ENNReal.ofReal (∏ i, pcnNorm1 s * Real.exp (-((y i - ρ * x i) ^ 2) / s)) := by
    funext y
    rw [h y]
  rw [hfun]
  exact pcnGaussMass_d (d := d) hs x

/-- **The increment restricted to the box has mass at most `1`.** -/
theorem pcnBoxMass_le_one {s ρ R : ℝ} (hs : 0 < s) (x : Fin d → ℝ) :
    ((volume.restrict (pcnBox d R)).withDensity fun y : Fin d → ℝ =>
      ENNReal.ofReal (pcnDensity (pcnNorm1 s ^ d) s ρ x y)) Set.univ ≤ 1 := by
  have hfull : (volume.withDensity fun y : Fin d → ℝ =>
      ENNReal.ofReal (pcnDensity (pcnNorm1 s ^ d) s ρ x y)) Set.univ = 1 :=
    pcnGaussMass_quad (d := d) hs x
  calc ((volume.restrict (pcnBox d R)).withDensity fun y : Fin d → ℝ =>
        ENNReal.ofReal (pcnDensity (pcnNorm1 s ^ d) s ρ x y)) Set.univ
      = ∫⁻ y, ENNReal.ofReal (pcnDensity (pcnNorm1 s ^ d) s ρ x y)
          ∂(volume.restrict (pcnBox d R)) := by
        rw [withDensity_apply _ MeasurableSet.univ, setLIntegral_univ]
    _ ≤ ∫⁻ y, ENNReal.ofReal (pcnDensity (pcnNorm1 s ^ d) s ρ x y) ∂volume :=
        lintegral_mono' Measure.restrict_le_self le_rfl
    _ = 1 := by
        rw [← setLIntegral_univ, ← withDensity_apply _ MeasurableSet.univ]
        exact hfull


/-- The Metropolis-adjusted step is dominated by the raw increment restricted to the box. -/
theorem pcnMetropolisStep_le_proposal {c s ρ R : ℝ} {π : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hc : 0 ≤ c) :
    pcnMetropolisStep c s ρ R π x ≤ pcnProposalMeasure (d := d) c s ρ R x := by
  rw [pcnMetropolisStep, pcnProposalMeasure]
  refine withDensity_mono ?_
  filter_upwards [ae_restrict_mem (measurableSet_pcnBox (d := d) R)] with y _
  refine ENNReal.ofReal_le_ofReal ?_
  have hd : 0 ≤ pcnDensity c s ρ x y := by
    rw [pcnDensity]
    exact mul_nonneg hc (Real.exp_pos _).le
  exact pcnMetropolisDensity_le hd

/-- **The accepted mass is at most `1`.**  The Metropolis step is dominated by the raw increment on
the box, and the increment's mass there is at most `1` (§9's `pcnBoxMass_le_one`) — so the rejection
atom of the next definition has nonnegative mass, with no hypothesis on the target. -/
theorem pcnMetropolisStep_mass_le_one {s ρ R : ℝ} (hs : 0 < s) (x : Fin d → ℝ)
    (π : (Fin d → ℝ) → ℝ) :
    (pcnMetropolisStep (pcnNorm1 s ^ d) s ρ R π x) Set.univ ≤ 1 := by
  refine le_trans ((Measure.le_iff.mp
    (pcnMetropolisStep_le_proposal (c := pcnNorm1 s ^ d) (π := π) (d := d)
      (by rw [pcnNorm1]; positivity))) Set.univ MeasurableSet.univ) ?_
  exact pcnBoxMass_le_one (d := d) hs x

/-- **The Metropolis step with its rejection atom**, at the increment's own constant
`c = (√(π s))^d`: the step a pCNL chain takes. -/
def pcnAbsorbingStep (s ρ R : ℝ) (π : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    Measure (Fin d → ℝ) :=
  pcnMetropolisStep (pcnNorm1 s ^ d) s ρ R π x
    + (1 - (pcnMetropolisStep (pcnNorm1 s ^ d) s ρ R π x) Set.univ) • Measure.dirac x

/-- **The pCNL Metropolis step is a probability measure** — with no hypothesis on the target and no
mass assumption: the rejection atom exactly absorbs what the accepted part leaves over. -/
theorem pcnAbsorbingStep_univ {s ρ R : ℝ} (hs : 0 < s) (x : Fin d → ℝ)
    (π : (Fin d → ℝ) → ℝ) :
    pcnAbsorbingStep (d := d) s ρ R π x Set.univ = 1 := by
  rw [pcnAbsorbingStep, Measure.add_apply, Measure.smul_apply,
    Measure.dirac_apply' x MeasurableSet.univ, Set.indicator_of_mem (Set.mem_univ x),
    Pi.one_apply, smul_eq_mul, mul_one, add_comm]
  exact tsub_add_cancel_of_le (pcnMetropolisStep_mass_le_one hs x π)

/-! ### Measurability of the step

§9 defines the step as a formula in the starting point; this block proves the family is a measurable
map into `Measure (Fin d → ℝ)`, which is what `Measure.bind` — hence `pcnIter` and the rate — needs.
The measure space on `Measure` is Mathlib's (`Measure.instMeasurableSpace`), and every fact below is
read off `Measure.measurable_of_measurable_coe`, so the proofs are statements about the coefficient
functions `x ↦ K x A`.

* **`measurable_setLIntegral`** — the mass into a set depends measurably on the start, from joint
  measurability of the density;
* **`measurable_withDensity_uncurry`** — a jointly measurable density gives a measurable family of
  `withDensity` measures;
* `measurable_pcnDensity_uncurry`, `measurable_pcnAccept_uncurry`,
  `measurable_pcnMetropolisDensity_uncurry` — the explicit formulas are jointly measurable;
* **`measurable_pcnMetropolisStep`**, `measurable_rejection`, **`measurable_pcnAbsorbingStep`** —
  the accepted part, the rejection atom, and their sum.
-/

/-- **The set integral is measurable in the starting point** — the step's mass into `A` depends
measurably on `x`, from joint measurability of the density. -/
theorem measurable_setLIntegral {α : Type*} [MeasurableSpace α] {ν : Measure α} [SFinite ν]
    {k : α → α → ENNReal}
    (hk : Measurable (Function.uncurry k)) {A : Set α} (hA : MeasurableSet A) :
    Measurable fun x => ∫⁻ y in A, k x y ∂ν := by
  classical
  have hind : Measurable fun p : α × α => k p.1 p.2 * (if p.2 ∈ A then 1 else 0) :=
    hk.mul (measurable_const.indicator (hA.preimage measurable_snd))
  have h := hind.lintegral_prod_right' (ν := ν)
  have hd : (fun x => ∫⁻ y, k x y * (if y ∈ A then 1 else 0) ∂ν)
      = fun x => ∫⁻ y in A, k x y ∂ν := by
    funext x
    rw [← lintegral_indicator hA (fun y => k x y)]
    exact lintegral_congr fun y => by by_cases hy : y ∈ A <;> simp [hy]
  rw [← hd]
  exact h

/-- **A jointly measurable density gives a measurable family of `withDensity` measures.** -/
theorem measurable_withDensity_uncurry {α : Type*} [MeasurableSpace α] {ν : Measure α} [SFinite ν]
    {k : α → α → ENNReal} (hk : Measurable (Function.uncurry k)) :
    Measurable fun x => ν.withDensity (k x) := by
  refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
  simp_rw [withDensity_apply _ hA]
  exact measurable_setLIntegral hk hA

/-- The pCN density is measurable in the pair (start, target), given a measurable acceptance
density. -/
theorem measurable_pcnDensity_uncurry (c s ρ : ℝ) :
    Measurable (Function.uncurry fun x y : Fin d → ℝ => pcnDensity c s ρ x y) := by
  have hquad : Measurable fun p : (Fin d → ℝ) × (Fin d → ℝ) => pcnQuad ρ p.1 p.2 := by
    unfold pcnQuad
    refine Finset.measurable_sum _ fun i _ => ?_
    refine (((measurable_pi_apply i).comp measurable_snd).sub
      (measurable_const.mul ((measurable_pi_apply i).comp measurable_fst))).pow_const 2
  unfold pcnDensity
  exact measurable_const.mul (Real.measurable_exp.comp (by fun_prop))

theorem measurable_pcnAccept_uncurry {τ : (Fin d → ℝ) → ℝ} (hτ : Measurable τ) :
    Measurable (Function.uncurry fun x y : Fin d → ℝ => pcnAccept τ x y) := by
  unfold pcnAccept
  refine Measurable.min measurable_const ?_
  exact (hτ.comp measurable_snd).div (hτ.comp measurable_fst)

theorem measurable_pcnMetropolisDensity_uncurry {τ : (Fin d → ℝ) → ℝ} (hτ : Measurable τ)
    (c s ρ : ℝ) :
    Measurable (Function.uncurry fun x y : Fin d → ℝ => pcnMetropolisDensity c s ρ τ x y) := by
  unfold pcnMetropolisDensity
  exact (measurable_pcnAccept_uncurry hτ).mul (measurable_pcnDensity_uncurry c s ρ)

theorem measurable_pcnMetropolisStep (c s ρ R : ℝ) {τ : (Fin d → ℝ) → ℝ} (hτ : Measurable τ) :
    Measurable (pcnMetropolisStep (d := d) c s ρ R τ) := by
  unfold pcnMetropolisStep
  exact measurable_withDensity_uncurry
    ((measurable_pcnMetropolisDensity_uncurry hτ c s ρ).ennreal_ofReal)

/-- The rejection atom is a measurable family `x ↦ (1 − mass x) • δ_x`. -/
theorem measurable_rejection (c s ρ R : ℝ) {τ : (Fin d → ℝ) → ℝ} (hτ : Measurable τ) :
    Measurable fun x => (1 - pcnMetropolisStep (d := d) c s ρ R τ x Set.univ)
      • Measure.dirac x := by
  refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
  have hmass : Measurable fun x => pcnMetropolisStep (d := d) c s ρ R τ x Set.univ :=
    (Measure.measurable_coe MeasurableSet.univ).comp (measurable_pcnMetropolisStep c s ρ R hτ)
  have hind : Measurable fun x : Fin d → ℝ => A.indicator (1 : (Fin d → ℝ) → ENNReal) x := by
    simpa using Measurable.indicator
      (measurable_const : Measurable fun _ : Fin d → ℝ => (1 : ENNReal)) hA
  have hprod : Measurable fun x : Fin d → ℝ =>
      (1 - pcnMetropolisStep (d := d) c s ρ R τ x Set.univ)
        * A.indicator (1 : (Fin d → ℝ) → ENNReal) x :=
    (measurable_const.sub hmass).mul hind
  rw [show (fun x => ((1 - pcnMetropolisStep (d := d) c s ρ R τ x Set.univ)
      • Measure.dirac x) A)
      = fun x => (1 - pcnMetropolisStep (d := d) c s ρ R τ x Set.univ)
          * A.indicator (1 : (Fin d → ℝ) → ENNReal) x from by
    funext x
    rw [Measure.smul_apply, Measure.dirac_apply' x hA, smul_eq_mul]]
  exact hprod

/-- **The pCN Metropolis step, with its rejection atom, is a measurable family of measures.** -/
theorem measurable_pcnAbsorbingStep (s ρ R : ℝ) {τ : (Fin d → ℝ) → ℝ} (hτ : Measurable τ) :
    Measurable (pcnAbsorbingStep (d := d) s ρ R τ) := by
  refine Measure.measurable_of_measurable_coe _ fun A hA => ?_
  have h1 : Measurable fun x => pcnMetropolisStep (d := d) (pcnNorm1 s ^ d) s ρ R τ x A :=
    ((Measure.measurable_coe hA).comp (measurable_pcnMetropolisStep (pcnNorm1 s ^ d) s ρ R hτ))
  have h2 := measurable_rejection (d := d) (pcnNorm1 s ^ d) s ρ R hτ
  have h2A : Measurable fun x => ((1 - pcnMetropolisStep (d := d) (pcnNorm1 s ^ d) s ρ R τ x
      Set.univ) • Measure.dirac x) A := (Measure.measurable_coe hA).comp h2
  rw [show (fun x => pcnAbsorbingStep (d := d) s ρ R τ x A) = fun x =>
      pcnMetropolisStep (d := d) (pcnNorm1 s ^ d) s ρ R τ x A
        + ((1 - pcnMetropolisStep (d := d) (pcnNorm1 s ^ d) s ρ R τ x Set.univ)
            • Measure.dirac x) A from by
    funext x
    rw [pcnAbsorbingStep, Measure.add_apply]]
  exact h1.add h2A


/-- **The rate for the unconditional step.**  `pcnAbsorbingStep` is a family of probability measures
with no mass hypothesis (`pcnAbsorbingStep_univ`), so §5's contraction applies to it wherever the
target is invariant under it and a minorant `c • π` below the step holds. -/
theorem pcnAbsorbingStep_rate {s ρ R c : ℝ} {τ : (Fin d → ℝ) → ℝ} {π : Measure (Fin d → ℝ)}
    (hc0 : 0 < c) (hc1 : c < 1) (hs : 0 < s) (hτ : Measurable τ) [IsProbabilityMeasure π]
    (hmin : ∀ x, ENNReal.ofReal c • π ≤ pcnAbsorbingStep (d := d) s ρ R τ x)
    (hstat : ∀ n, π.bind (pcnIter (pcnAbsorbingStep (d := d) s ρ R τ) n) = π)
    (n : ℕ) (x : Fin d → ℝ) {S : Set (Fin d → ℝ)} (hS : MeasurableSet S) :
    ENNReal.ofReal (1 - (1 - c) ^ n) * π S
      ≤ pcnIter (pcnAbsorbingStep (d := d) s ρ R τ) n x S :=
  have hmeas : Measurable (pcnAbsorbingStep (d := d) s ρ R τ) :=
    measurable_pcnAbsorbingStep s ρ R hτ
  pcnIter_rate_of_minorant hc0 hc1 hmeas (fun x => pcnAbsorbingStep_univ hs x τ) hmin hstat n x hS


/-! ## 10. The minorant for the step the chain takes

§3–§4's minorant is stated for the raw pCN proposal and for the accepted density; §9 supplies the
step a chain actually takes, with its rejection atom.  This section joins them:

* **`pcnMetropolisStep_le_pcnAbsorbingStep`** — the accepted part is dominated by the step;
* **`pcnAbsorbingStep_minorant`** — on the box, a target-density ceiling `B`, a proposal floor `F`
  and an acceptance floor `m` give `(mF/B) • π ≤ pcnAbsorbingStep`, the Doeblin minorant for the
  Metropolis step itself.

**A note on where it can be used.**  §5's contraction takes the minorant at *every* starting
point (`hmin : ∀ x`), because its lower bound is an infimum over the whole space.  The floor above
is a box statement — `pcnDensity_floor` needs `|xᵢ| ≤ R` — so applying the rate needs either the
chain to stay in the box or a minorant outside it, and neither is proved here.
-/


/-- The accepted part is dominated by the step *with* its rejection atom. -/
theorem pcnMetropolisStep_le_pcnAbsorbingStep (s ρ R : ℝ) (π : (Fin d → ℝ) → ℝ)
    (x : Fin d → ℝ) :
    pcnMetropolisStep (pcnNorm1 s ^ d) s ρ R π x ≤ pcnAbsorbingStep (d := d) s ρ R π x := by
  rw [pcnAbsorbingStep]
  exact Measure.le_add_right (le_refl _)

/-- **The Doeblin minorant for the step the chain actually takes.**  On the box, a target density
ceiling `B`, a proposal floor `F` and an acceptance floor `m` (the target's density drops by at
most the factor `m`) give `(mF/B) • π ≤ pcnAbsorbingStep`, i.e. a minorant for the Metropolis step
with its rejection atom. -/
theorem pcnAbsorbingStep_minorant {s ρ R F B m : ℝ} {τ : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hF : 0 ≤ F) (hB : 0 < B) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hτB : ∀ y ∈ pcnBox d R, τ y ≤ B) (hτx : 0 < τ x)
    (hτxy : ∀ y ∈ pcnBox d R, m * τ x ≤ τ y)
    (hdens : ∀ y ∈ pcnBox d R, F ≤ pcnDensity (pcnNorm1 s ^ d) s ρ x y) :
    ENNReal.ofReal (m * F / B) • pcnTargetMeasure (d := d) R τ
      ≤ pcnAbsorbingStep (d := d) s ρ R τ x := by
  have hmF0 : 0 ≤ m * F := mul_nonneg hm0 hF
  have hfloor : ∀ y ∈ pcnBox d R,
      m * F ≤ pcnMetropolisDensity (pcnNorm1 s ^ d) s ρ τ x y := by
    intro y hy
    exact pcnMetropolis_floor hm0 hF
      (pcnAccept_floor hm1 hτx (hτxy y hy)) (hdens y hy)
  have hπ : pcnTargetMeasure (d := d) R τ ≤ ENNReal.ofReal B • (volume.restrict (pcnBox d R)) :=
    pcnTargetMeasure_le_smul hτB
  have hμ : ENNReal.ofReal (m * F) • (volume.restrict (pcnBox d R))
      ≤ pcnMetropolisStep (pcnNorm1 s ^ d) s ρ R τ x :=
    pcnMetropolis_minorant hfloor
  calc ENNReal.ofReal (m * F / B) • pcnTargetMeasure (d := d) R τ
      ≤ ENNReal.ofReal (m * F / B) • (ENNReal.ofReal B • (volume.restrict (pcnBox d R))) :=
        smul_measure_mono hπ
    _ = ENNReal.ofReal (m * F) • (volume.restrict (pcnBox d R)) := by
        rw [smul_smul, ofReal_div_mul_ofReal hmF0 hB]
    _ ≤ pcnMetropolisStep (pcnNorm1 s ^ d) s ρ R τ x := hμ
    _ ≤ pcnAbsorbingStep (d := d) s ρ R τ x := pcnMetropolisStep_le_pcnAbsorbingStep s ρ R τ x


/-! ## 11. How much mass the step puts back in the box

§10's minorant is a box statement, while §5's contraction wants one at every starting point.  The
route between them is the standard one: the chain *returns* to the box with mass bounded below, so
two steps of it dominate a constant times the target everywhere.  This section supplies the return
mass:

* **`pcnBox_volume`** — the box's Lebesgue volume is `(2R)^d`;
* **`withDensity_box_ge`** — a density floor `F` on the box gives the `withDensity` measure at least
  `F · (2R)^d` of box mass;
* **`pcnProposalMeasure_box_ge`**, **`pcnMetropolisStep_box_ge`** — that floor for the proposal and
  for the Metropolis step;
* **`pcnAbsorbingStep_box_ge`** — and for the step the chain takes.

**What this does not give.**  The tempting composition is "minorant inside the box (§10) plus return
mass (§11), hence the two-step kernel has a Doeblin constant at every starting point".  That step
is *not* available, and §12 records why: this return mass is itself box-local.  The floor `F` comes
from
`pcnDensity_floor`, which needs `|xᵢ| ≤ R` for the *starting* point, and a pCN proposal started far
outside the box puts exponentially little mass in it — `exp (−∑ (yᵢ − ρxᵢ)²/s)` — so no uniform
return estimate follows from what is proved here.
-/


/-- **The box's volume**: `(2R)^d`. -/
theorem pcnBox_volume {R : ℝ} :
    (volume : Measure (Fin d → ℝ)) (pcnBox d R) = ENNReal.ofReal (2 * R) ^ d := by
  rw [show (volume : Measure (Fin d → ℝ)) = Measure.pi (fun _ : Fin d => (volume : Measure ℝ))
    from rfl]
  rw [pcnBox, Measure.pi_pi]
  rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  simp only [Real.volume_Icc, show R - -R = 2 * R from by ring]

/-- **A density floor on the box gives a box-mass floor**: `F · (2R)^d`. -/
theorem withDensity_box_ge {R F : ℝ} {f : (Fin d → ℝ) → ℝ}
    (hmF : 0 ≤ F) (hR : 0 ≤ R) (hle : ∀ y ∈ pcnBox d R, F ≤ f y) :
    ENNReal.ofReal (F * (2 * R) ^ d)
      ≤ ((volume.restrict (pcnBox d R)).withDensity fun y => ENNReal.ofReal (f y))
          (pcnBox d R) := by
  have hpt : ∀ y ∈ pcnBox d R, ENNReal.ofReal F ≤ ENNReal.ofReal (f y) :=
    fun y hy => ENNReal.ofReal_le_ofReal (hle y hy)
  calc ENNReal.ofReal (F * (2 * R) ^ d)
      = ENNReal.ofReal F * ENNReal.ofReal ((2 * R) ^ d) := by rw [ENNReal.ofReal_mul hmF]
    _ = ENNReal.ofReal F * ENNReal.ofReal (2 * R) ^ d := by
        rw [ENNReal.ofReal_pow (by linarith : (0 : ℝ) ≤ 2 * R)]
    _ = ENNReal.ofReal F * (volume : Measure (Fin d → ℝ)) (pcnBox d R) := by
        rw [pcnBox_volume]
    _ = ENNReal.ofReal F * ((volume.restrict (pcnBox d R)) (pcnBox d R)) := by
        rw [Measure.restrict_apply_self]
    _ = ∫⁻ y in pcnBox d R, ENNReal.ofReal F ∂(volume.restrict (pcnBox d R)) := by
        rw [setLIntegral_const]
    _ ≤ ∫⁻ y in pcnBox d R, ENNReal.ofReal (f y) ∂(volume.restrict (pcnBox d R)) :=
        setLIntegral_mono' (measurableSet_pcnBox (d := d) R) hpt
    _ = ((volume.restrict (pcnBox d R)).withDensity fun y => ENNReal.ofReal (f y))
          (pcnBox d R) := by
        rw [withDensity_apply _ (measurableSet_pcnBox (d := d) R)]

/-- **The proposal's mass on the box, from below** — the "return mass" a regeneration argument
consumes. -/
theorem pcnProposalMeasure_box_ge {c s ρ R F : ℝ} {x : Fin d → ℝ}
    (hF : 0 ≤ F) (hR : 0 ≤ R) (hle : ∀ y ∈ pcnBox d R, F ≤ pcnDensity c s ρ x y) :
    ENNReal.ofReal (F * (2 * R) ^ d) ≤ pcnProposalMeasure (d := d) c s ρ R x (pcnBox d R) :=
  withDensity_box_ge hF hR hle

/-- **The Metropolis step's mass on the box, from below**: the accepted density's floor times the
box's volume. -/
theorem pcnMetropolisStep_box_ge {c s ρ R F : ℝ} {π : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hF : 0 ≤ F) (hR : 0 ≤ R)
    (hle : ∀ y ∈ pcnBox d R, F ≤ pcnMetropolisDensity c s ρ π x y) :
    ENNReal.ofReal (F * (2 * R) ^ d)
      ≤ pcnMetropolisStep (d := d) c s ρ R π x (pcnBox d R) :=
  withDensity_box_ge hF hR hle

/-- **The step the chain takes returns to the box with mass at least `F · (2R)^d`.** -/
theorem pcnAbsorbingStep_box_ge {s ρ R F : ℝ} {π : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hF : 0 ≤ F) (hR : 0 ≤ R)
    (hle : ∀ y ∈ pcnBox d R, F ≤ pcnMetropolisDensity (pcnNorm1 s ^ d) s ρ π x y) :
    ENNReal.ofReal (F * (2 * R) ^ d)
      ≤ pcnAbsorbingStep (d := d) s ρ R π x (pcnBox d R) := by
  refine le_trans (pcnMetropolisStep_box_ge (c := pcnNorm1 s ^ d) hF hR hle) ?_
  refine Measure.le_iff.mp ?_ (pcnBox d R) (measurableSet_pcnBox (d := d) R)
  exact pcnMetropolisStep_le_pcnAbsorbingStep s ρ R π x


/-! ## 12. Doeblin from a small set, and why two steps do not close the gap

§10's minorant is box-local and §11's return mass is too, so §5's contraction still cannot consume
them.  This section states the general small-set lemma that a repair would use, proves the pCN
instance under an explicit return estimate, and — the part that matters — records that the estimate
§11 supplies is not the one needed.

* **`bind_minorant_of_set`** — general: if `ρ` gives a set `S` mass at least `c0`, and every step
  from `S` dominates `c1 • π`, then `ρ.bind K ≥ c0 · c1 • π`;
* **`pcnAbsorbingStep_twoStep_minorant`** — the pCN instance, *given* a return estimate
  `∀ y, ofReal c0 ≤ pcnAbsorbingStep y (box)`.

§11's return mass cannot discharge the hypothesis on its own: the density floor needs `|xᵢ| ≤ R` for
the starting point, and a Gaussian proposal started outside the box puts exponentially little mass
in it.  §13 supplies the missing start-dependence — a return mass decaying like
`exp (−2ρ²‖x‖²/s)` — so the hypothesis holds at every start, with a constant that is uniform only on
balls; §15 then shows where the chain actually goes.
-/


/-- **Doeblin from a small set**: if `ρ` puts at least `c0` of mass in a set `S` and every step from
`S` dominates `c1 • π`, then one step from `ρ` dominates `c0 · c1 • π`. -/
theorem bind_minorant_of_set {α : Type*} [MeasurableSpace α] {ρ π : Measure α}
    {K : α → Measure α} {S : Set α} (hS : MeasurableSet S) (hK : AEMeasurable K ρ)
    {c0 c1 : ENNReal} (hρS : c0 ≤ ρ S) (hmin : ∀ y ∈ S, c1 • π ≤ K y) :
    (c0 * c1) • π ≤ ρ.bind K := by
  refine Measure.le_iff.mpr fun A hA => ?_
  rw [Measure.smul_apply, smul_eq_mul, Measure.bind_apply hA hK]
  have h2 : c1 * π A * ρ S ≤ ∫⁻ y in S, K y A ∂ρ := by
    calc c1 * π A * ρ S = ∫⁻ _y in S, c1 * π A ∂ρ := by
          rw [setLIntegral_const]
      _ ≤ ∫⁻ y in S, K y A ∂ρ := by
          refine setLIntegral_mono' hS fun y hy => ?_
          exact (Measure.le_iff.mp (hmin y hy)) A hA
  calc c0 * c1 * π A = c1 * π A * c0 := by ring
    _ ≤ c1 * π A * ρ S := by gcongr
    _ ≤ ∫⁻ y in S, K y A ∂ρ := h2
    _ ≤ ∫⁻ y, K y A ∂ρ := setLIntegral_le_lintegral _ _


/-- **Two steps dominate the target everywhere — given a return estimate valid at every starting
point.**  If `π` bounds the target's density on the box, the acceptance and density floors hold
throughout the box (§10), and the step returns to the box with mass at least `c0` from *every*
starting point, then one step out of any `x` dominates `c0 · (mF/B) • π`.

§11 supplies the last hypothesis only for starts inside the box — `pcnDensity_floor` needs
`|xᵢ| ≤ R` — so this is a reduction, not an application: the return estimate outside the box is what
a confinement argument would have to provide. -/
theorem pcnAbsorbingStep_twoStep_minorant {s ρ R F B m c0 : ℝ} {τ : (Fin d → ℝ) → ℝ}
    {x : Fin d → ℝ} (hF : 0 ≤ F) (hB : 0 < B) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hτB : ∀ y ∈ pcnBox d R, τ y ≤ B)
    (hτpos : ∀ y ∈ pcnBox d R, 0 < τ y)
    (hτxy : ∀ y ∈ pcnBox d R, ∀ z ∈ pcnBox d R, m * τ y ≤ τ z)
    (hdens : ∀ y ∈ pcnBox d R, ∀ z ∈ pcnBox d R, F ≤ pcnDensity (pcnNorm1 s ^ d) s ρ y z)
    (hret : ∀ y, ENNReal.ofReal c0
      ≤ pcnAbsorbingStep (d := d) s ρ R τ y (pcnBox d R))
    (hτ : Measurable τ) :
    (ENNReal.ofReal c0 * ENNReal.ofReal (m * F / B)) • pcnTargetMeasure (d := d) R τ
      ≤ (pcnAbsorbingStep (d := d) s ρ R τ x).bind (pcnAbsorbingStep (d := d) s ρ R τ) :=
  bind_minorant_of_set (measurableSet_pcnBox (d := d) R)
    (measurable_pcnAbsorbingStep s ρ R hτ).aemeasurable (hret x)
    (fun y hy => pcnAbsorbingStep_minorant hF hB hm0 hm1 hτB (hτpos y hy) (hτxy y hy)
      (hdens y hy))

/-! ## 13. Confinement: the return mass from an arbitrary starting point

§11's return mass needs the *start* in the box, and §12 showed that this is exactly what blocks the
two-step composition.  This section removes the restriction on the start and replaces it with the
honest dependence: the increment's exponent grows at most like `2ρ²‖x‖² + 2dR²` on the box, so the
step returns to the box with mass bounded below by a constant that decays like `exp(−2ρ²‖x‖²/s)`.

* `pcnSumSq` — the start's squared radius `∑ᵢ xᵢ²`;
* **`pcnQuad_le_of_mem_box`** — on the box, `pcnQuad ρ x y ≤ 2ρ²·‖x‖² + 2dR²`, for every start `x`;
* **`pcnDensity_start_floor`**, `pcnReturnConst` — the resulting density floor, named;
* **`pcnProposalMeasure_box_ge_start`** — the proposal's box mass from any start;
* **`pcnAbsorbingStep_box_ge_start`** — the same for the step the chain takes (acceptance floor `m`
  enters through `τ x ≤ B` at the start only);
* and so §12's hypothesis is discharged by the constant `m · pcnReturnConst s ρ R x · (2R)^d` at
  every start: instantiate `pcnAbsorbingStep_twoStep_minorant`'s `c0` with it and its `hret` with
  `pcnAbsorbingStep_box_ge_start`.

**What is confinement here, and what is not.**  The constant is *not* uniform in `x`: it decays like
`exp (−2ρ²‖x‖²/s)`, which is the confinement content — on any fixed ball `‖x‖² ≤ M²` it is bounded
below by `exp (−(2ρ²M² + 2dR²)/s)`, positive, but the estimate alone does not say the chain stays in
such a ball, nor does it produce a rate uniform over starting points.  It does make §12's hypothesis
dischargeable, which a box-local return mass could not.
-/

/-- The start's squared radius `∑ᵢ xᵢ²`. -/
def pcnSumSq (x : Fin d → ℝ) : ℝ := ∑ i, x i ^ 2

theorem pcnSumSq_nonneg (x : Fin d → ℝ) : 0 ≤ pcnSumSq x :=
  Finset.sum_nonneg fun i _ => sq_nonneg (x i)

/-- **The increment's exponent from an arbitrary start**: on the box the increment is at most
`2ρ²‖x‖² + 2dR²`.  Each coordinate contributes `(yᵢ − ρxᵢ)² ≤ 2yᵢ² + 2ρ²xᵢ²`, and on the box
`∑ᵢ yᵢ² ≤ dR²`. -/
theorem pcnQuad_le_of_mem_box {ρ R : ℝ} {x y : Fin d → ℝ} (hy : y ∈ pcnBox d R) :
    pcnQuad ρ x y ≤ 2 * ρ ^ 2 * pcnSumSq x + 2 * (d : ℝ) * R ^ 2 := by
  have hb : ∀ i : Fin d, |y i| ≤ R := mem_pcnBox.mp hy
  have hcoord : ∀ i : Fin d,
      (y i - ρ * x i) ^ 2 ≤ 2 * (y i) ^ 2 + 2 * ρ ^ 2 * (x i) ^ 2 := by
    intro i
    nlinarith [sq_nonneg (y i + ρ * x i)]
  have hy2 : (∑ i, (y i) ^ 2) ≤ (d : ℝ) * R ^ 2 := by
    calc (∑ i, (y i) ^ 2) ≤ ∑ _i : Fin d, R ^ 2 :=
          Finset.sum_le_sum fun i _ => by
            have hi := abs_le.mp (hb i)
            nlinarith [hi.1, hi.2]
      _ = (d : ℝ) * R ^ 2 := by
          rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  calc pcnQuad ρ x y = ∑ i, (y i - ρ * x i) ^ 2 := rfl
    _ ≤ ∑ i, (2 * (y i) ^ 2 + 2 * ρ ^ 2 * (x i) ^ 2) := Finset.sum_le_sum fun i _ => hcoord i
    _ = 2 * (∑ i, (y i) ^ 2) + 2 * ρ ^ 2 * pcnSumSq x := by
        simp only [pcnSumSq, Finset.sum_add_distrib, ← Finset.mul_sum]
    _ ≤ 2 * ((d : ℝ) * R ^ 2) + 2 * ρ ^ 2 * pcnSumSq x := by nlinarith
    _ = 2 * ρ ^ 2 * pcnSumSq x + 2 * (d : ℝ) * R ^ 2 := by ring

/-- **The density's floor from an arbitrary start** — §1's floor with `2ρ²‖x‖² + 2dR²` in place of
the box-only bound. -/
theorem pcnDensity_start_floor {c s ρ R : ℝ} (hc : 0 ≤ c) (hs : 0 < s)
    {x y : Fin d → ℝ} (hy : y ∈ pcnBox d R) :
    c * Real.exp (-(2 * ρ ^ 2 * pcnSumSq x + 2 * (d : ℝ) * R ^ 2) / s)
      ≤ pcnDensity c s ρ x y :=
  pcnDensity_le_of_quad_le hc hs (pcnQuad_le_of_mem_box hy)

/-- The proposal's box mass from the start `x`: `(√(π s))^d · exp (−(2ρ²‖x‖² + 2dR²)/s)`. -/
def pcnReturnConst (s ρ R : ℝ) (x : Fin d → ℝ) : ℝ :=
  pcnNorm1 s ^ d * Real.exp (-(2 * ρ ^ 2 * pcnSumSq x + 2 * (d : ℝ) * R ^ 2) / s)

theorem pcnNorm1_pos {s : ℝ} (hs : 0 < s) : 0 < pcnNorm1 s := by
  unfold pcnNorm1
  exact inv_pos.mpr (Real.sqrt_pos.mpr (by positivity))

theorem pcnReturnConst_pos {s : ℝ} (hs : 0 < s) (ρ R : ℝ) (x : Fin d → ℝ) :
    0 < pcnReturnConst (d := d) s ρ R x := by
  unfold pcnReturnConst
  exact mul_pos (pow_pos (pcnNorm1_pos hs) _) (Real.exp_pos _)

/-- **The return mass from any starting point**: the proposal puts at least
`pcnReturnConst s ρ R x · (2R)^d` of mass in the box. -/
theorem pcnProposalMeasure_box_ge_start {s ρ R : ℝ} (hs : 0 < s) (hR : 0 ≤ R)
    (x : Fin d → ℝ) :
    ENNReal.ofReal (pcnReturnConst (d := d) s ρ R x * (2 * R) ^ d)
      ≤ pcnProposalMeasure (d := d) (pcnNorm1 s ^ d) s ρ R x (pcnBox d R) :=
  pcnProposalMeasure_box_ge (pcnReturnConst_pos hs ρ R x).le hR
    (fun _y hy => pcnDensity_start_floor (pow_nonneg (pcnNorm1_pos hs).le d) hs hy)

/-- **The step returns to the box from any start.**  The acceptance floor `m` needs the target's
density at the start bounded by `B` (`τ x ≤ B`) and at least `m·B` throughout the box; nothing else
about the start is needed. -/
theorem pcnAbsorbingStep_box_ge_start {s ρ R B m : ℝ} {τ : (Fin d → ℝ) → ℝ} {x : Fin d → ℝ}
    (hs : 0 < s) (hR : 0 ≤ R) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hτx : 0 < τ x) (hτxB : τ x ≤ B) (hτfloor : ∀ y ∈ pcnBox d R, m * B ≤ τ y) :
    ENNReal.ofReal (m * pcnReturnConst (d := d) s ρ R x * (2 * R) ^ d)
      ≤ pcnAbsorbingStep (d := d) s ρ R τ x (pcnBox d R) := by
  refine pcnAbsorbingStep_box_ge (hF := mul_nonneg hm0 (pcnReturnConst_pos hs ρ R x).le) hR ?_
  intro y hy
  exact pcnMetropolis_floor hm0 (pcnReturnConst_pos hs ρ R x).le
    (pcnAccept_floor hm1 hτx (by
      calc m * τ x ≤ m * B := mul_le_mul_of_nonneg_left hτxB hm0
        _ ≤ τ y := hτfloor y hy))
    (pcnDensity_start_floor (pow_nonneg (pcnNorm1_pos hs).le d) hs hy)
/-! ## 14. Reversibility: the prior the increment leaves alone

§3–§13 compare the step with `pcnTargetMeasure R τ = volume.withDensity τ` on the box.  That is the
reference measure of a *symmetric* Metropolis proposal, and the pCN increment is not symmetric:
`y = ρ x + √(1 − ρ²) ξ` has density `exp (−(yᵢ − ρxᵢ)²/s)` in the forward direction and
`exp (−(xᵢ − ρyᵢ)²/s)` in the reverse one.  The measure it does leave alone is the Gaussian prior.
This section states that exactly, and the consequence for the filter:

* **`pcnPrior`** — the prior's unnormalised density `exp (−(1 − ρ²)∑ᵢxᵢ²/s)`, i.e.
  `N(0, s/(2(1 − ρ²)))`;
* **`pcnPrior_mul_density_comm`** — the symmetry `pcnPrior x · q_x(y) = pcnPrior y · q_y(x)`:
  detailed balance for the *unfiltered* proposal against the prior;
* **`pcnMetropolisDensity_detailed`** — with the prior factor carried along, `τ · pcnPrior` is
  reversible under the chapter's acceptance `min 1 (τ y / τ x)`;
* **`pcnPrior_ne_one`** — and that factor is not constant, so `volume.withDensity τ` is not the
  measure the step is reversible for.

**What this changes in §3–§13.**  Their conclusions are about `volume.withDensity τ`; for the pCN
proposal the reversible measure is `volume.withDensity (τ · pcnPrior)`, so `τ` there plays the role
of a *likelihood* (a density with respect to the prior), not of a density against Lebesgue.  The box
floors are untouched — they bound `pcnDensity` and the acceptance, not the reference measure — and
the repair in the statements is to carry the factor, replacing `τ` by
`x ↦ τ x * pcnPrior s ρ x`.  The integral passage from detailed balance to stationarity is not
written here.
-/

/-- The pCN prior's unnormalised density: `exp (−(1 − ρ²)∑ᵢxᵢ² / s)`, i.e. the Gaussian
`N(0, s/(2(1−ρ²)))` the increment leaves invariant. -/
def pcnPrior (s ρ : ℝ) (x : Fin d → ℝ) : ℝ :=
  Real.exp (-((1 - ρ ^ 2) * pcnSumSq x) / s)

theorem pcnPrior_pos (s ρ : ℝ) (x : Fin d → ℝ) : 0 < pcnPrior s ρ x :=
  Real.exp_pos _

/-- **The increment is reversible with respect to its prior**: the forward and reverse joint
densities agree.  Per coordinate the identity is
`(1 − ρ²)xᵢ² + (yᵢ − ρxᵢ)² = (1 − ρ²)yᵢ² + (xᵢ − ρyᵢ)²`, whose difference is `(1 − ρ²)` times
`xᵢ² − yᵢ²` from both directions. -/
theorem pcnPrior_mul_density_comm {s : ℝ} (hs : s ≠ 0) (c ρ : ℝ) (x y : Fin d → ℝ) :
    pcnPrior s ρ x * pcnDensity c s ρ x y = pcnPrior s ρ y * pcnDensity c s ρ y x := by
  have hsum : (1 - ρ ^ 2) * pcnSumSq x + pcnQuad ρ x y
      = (1 - ρ ^ 2) * pcnSumSq y + pcnQuad ρ y x := by
    unfold pcnSumSq pcnQuad
    rw [Finset.mul_sum, Finset.mul_sum, ← Finset.sum_add_distrib,
      ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  have harg : -((1 - ρ ^ 2) * pcnSumSq x) / s + -(pcnQuad ρ x y) / s
      = -((1 - ρ ^ 2) * pcnSumSq y) / s + -(pcnQuad ρ y x) / s := by
    field_simp
    linarith
  calc pcnPrior s ρ x * pcnDensity c s ρ x y
      = c * (Real.exp (-((1 - ρ ^ 2) * pcnSumSq x) / s)
          * Real.exp (-(pcnQuad ρ x y) / s)) := by
        simp only [pcnPrior, pcnDensity]; ring
    _ = c * Real.exp (-((1 - ρ ^ 2) * pcnSumSq x) / s + -(pcnQuad ρ x y) / s) := by
        rw [Real.exp_add]
    _ = c * Real.exp (-((1 - ρ ^ 2) * pcnSumSq y) / s + -(pcnQuad ρ y x) / s) := by
        rw [harg]
    _ = pcnPrior s ρ y * pcnDensity c s ρ y x := by
        rw [Real.exp_add]; simp only [pcnPrior, pcnDensity]; ring

/-- The acceptance times the target's density at the start is the minimum of the two densities: the
algebra that turns `min 1 (π y / π x)` into an object symmetric in `x` and `y`. -/
theorem pcnAccept_mul_self {π : (Fin d → ℝ) → ℝ} {x y : Fin d → ℝ} (hx : 0 < π x) :
    π x * pcnAccept π x y = min (π x) (π y) := by
  by_cases h : π y ≤ π x
  · have h1 : min (π x) (π y) = π y := min_eq_right h
    have h2 : π y / π x ≤ 1 := (div_le_one hx).mpr h
    rw [pcnAccept, min_eq_right h2, h1, mul_div_cancel₀ _ hx.ne']
  · have h1 : min (π x) (π y) = π x := min_eq_left (le_of_lt (lt_of_not_ge h))
    have h2 : 1 ≤ π y / π x := (one_le_div hx).mpr (le_of_lt (lt_of_not_ge h))
    rw [pcnAccept, min_eq_left h2, h1, mul_one]

/-- **Detailed balance with the prior carried along.**  For any target density `τ`, the accepted
step is reversible for the measure whose density is `τ · pcnPrior` — not for `τ` alone. -/
theorem pcnMetropolisDensity_detailed {c s ρ : ℝ} {τ : (Fin d → ℝ) → ℝ} {x y : Fin d → ℝ}
    (hs : s ≠ 0) (hx : 0 < τ x) (hy : 0 < τ y) :
    (τ x * pcnPrior s ρ x) * pcnMetropolisDensity c s ρ τ x y
      = (τ y * pcnPrior s ρ y) * pcnMetropolisDensity c s ρ τ y x := by
  have hcomm := pcnPrior_mul_density_comm (c := c) (ρ := ρ) hs x y
  have h1 := pcnAccept_mul_self (π := τ) (x := x) (y := y) hx
  have h2 := pcnAccept_mul_self (π := τ) (x := y) (y := x) hy
  calc (τ x * pcnPrior s ρ x) * pcnMetropolisDensity c s ρ τ x y
      = (τ x * pcnAccept τ x y) * (pcnPrior s ρ x * pcnDensity c s ρ x y) := by
        simp only [pcnMetropolisDensity]; ring
    _ = min (τ x) (τ y) * (pcnPrior s ρ y * pcnDensity c s ρ y x) := by rw [h1, hcomm]
    _ = (τ y * pcnAccept τ y x) * (pcnPrior s ρ y * pcnDensity c s ρ y x) := by
        rw [h2, min_comm]
    _ = (τ y * pcnPrior s ρ y) * pcnMetropolisDensity c s ρ τ y x := by
        simp only [pcnMetropolisDensity]; ring

/-- The prior factor carried by the reversible measure is not constant: at `ρ = 1/2`, `s = 1` it is
`1` at the origin and `exp (−3/4)` at `x = 1`.  So `volume.withDensity τ` and
`volume.withDensity (τ · pcnPrior)` differ, and §3–§13's named target is the one a symmetric
proposal would have. -/
theorem pcnPrior_ne_one :
    pcnPrior (d := 1) 1 (1 / 2) 0 ≠ pcnPrior (d := 1) 1 (1 / 2) 1 := by
  simp only [pcnPrior, pcnSumSq, Pi.zero_apply, Pi.one_apply, Fin.sum_univ_one]
  norm_num
  intro h
  have h2 : Real.exp 0 = Real.exp (-(3 / 4)) := by rw [Real.exp_zero]; exact h
  have h3 := Real.exp_injective h2
  norm_num at h3

/-! ## 15. Confinement: the step stays in the box or at the start

§13 bounded the start's dependence but could not say where the chain *goes*.  This section does: the
accepted part is a density against `volume.restrict box`, so it lives in the box, and the rejection
atom lives at the start.  One step from `x` therefore never leaves `box ∪ {x}`, and neither does any
iterate.

* **`pcnAbsorbingStep_eq_zero_of_disjoint`** — a set measurable, disjoint from the box and not
  containing `x` gets no mass;
* **`pcnAbsorbingStep_confined`** — hence `K x (box ∪ {x})ᶜ = 0`;
* **`bind_eq_zero_of_support`** — a measure supported in `S` whose steps from `S` stay in `S` has
  its `bind` supported in `S`;
* **`pcnIter_confined`** — the `n`-step measure from `x` lives in `box ∪ {x}`;
* **`pcnSumSq_le_of_mem_box`**, **`pcnIter_confined_ball`** — in the radius `‖z‖²`, the iterate
  stays below `max (dR²) ‖x‖²`: the chain never drifts outwards;
* **`pcnBallConst`**, **`pcnAbsorbingStep_box_ge_ball`** — so the §13 return constant is *uniform*
  over the starts in a ball `‖x‖² ≤ M²`, at the price of replacing `‖x‖²` by `M²`;
* **`pcnAbsorbingStep_twoStep_minorant_ball`** — §12's two-step minorant with that uniform constant.

**What this is, and is not.**  Confinement here is confinement to `box ∪ {x}`: the chain cannot
drift further out than where it started, so the return estimate is uniform on each ball of starting
points rather than on `ℝ^d`.  It is not a uniform estimate over all starts — §13's constant
genuinely decays in `‖x‖²` — and it does not give the contraction a single constant; what it gives
is that the constant depends on the start only through the ball containing it.
-/

/-- The step has no mass outside the box and the starting point. -/
theorem pcnAbsorbingStep_eq_zero_of_disjoint {s ρ R : ℝ} {τ : (Fin d → ℝ) → ℝ}
    {x : Fin d → ℝ} {A : Set (Fin d → ℝ)} (hA : MeasurableSet A)
    (hbox : Disjoint A (pcnBox d R)) (hx : x ∉ A) :
    pcnAbsorbingStep (d := d) s ρ R τ x A = 0 := by
  have hvol : (volume.restrict (pcnBox d R)) A = 0 := by
    rw [Measure.restrict_apply hA, Set.disjoint_iff_inter_eq_empty.mp hbox, measure_empty]
  have hacc : pcnMetropolisStep (pcnNorm1 s ^ d) s ρ R τ x A = 0 := by
    rw [pcnMetropolisStep]
    exact (withDensity_absolutelyContinuous (volume.restrict (pcnBox d R))
      fun y => ENNReal.ofReal (pcnMetropolisDensity (pcnNorm1 s ^ d) s ρ τ x y)) hvol
  rw [pcnAbsorbingStep, Measure.add_apply, hacc, zero_add, Measure.smul_apply,
    Measure.dirac_apply' x hA, Set.indicator_of_notMem hx, smul_eq_mul, mul_zero]

/-- **The step is confined to the box and its own starting point.** -/
theorem pcnAbsorbingStep_confined {s ρ R : ℝ} {τ : (Fin d → ℝ) → ℝ} (x : Fin d → ℝ) :
    pcnAbsorbingStep (d := d) s ρ R τ x (pcnBox d R ∪ {x})ᶜ = 0 := by
  refine pcnAbsorbingStep_eq_zero_of_disjoint
    ((measurableSet_pcnBox (d := d) R).union (measurableSet_singleton x)).compl ?_ ?_
  · rw [Set.disjoint_compl_left_iff_subset]
    exact Set.subset_union_left
  · simp

/-- A measure that vanishes on `S` and whose steps vanish outside `S` stays inside `S`. -/
theorem bind_eq_zero_of_support {α : Type*} [MeasurableSpace α] {μ : Measure α}
    {K : α → Measure α} {S : Set α} (hS : MeasurableSet S) (hμ : μ Sᶜ = 0)
    (hK : AEMeasurable K μ) (hstep : ∀ y ∈ S, K y Sᶜ = 0) :
    (μ.bind K) Sᶜ = 0 := by
  rw [Measure.bind_apply hS.compl hK]
  have hcompl : ∀ᵐ y ∂μ, y ∈ S := by
    rw [MeasureTheory.ae_iff]
    simpa using hμ
  have hae : (fun y => K y Sᶜ) =ᵐ[μ] 0 := by
    filter_upwards [hcompl] with y hy
    exact hstep y hy
  rw [lintegral_congr_ae hae]
  simp

/-- **The iterates are confined too**: the `n`-step measure from `x` lives in `box ∪ {x}`. -/
theorem pcnIter_confined {s ρ R : ℝ} {τ : (Fin d → ℝ) → ℝ}
    (hτ : Measurable τ) (n : ℕ) (x : Fin d → ℝ) :
    pcnIter (pcnAbsorbingStep (d := d) s ρ R τ) n x (pcnBox d R ∪ {x})ᶜ = 0 := by
  have hmeas : Measurable (pcnAbsorbingStep (d := d) s ρ R τ) :=
    measurable_pcnAbsorbingStep s ρ R hτ
  induction n generalizing x with
  | zero =>
      rw [pcnIter_zero, Measure.dirac_apply' x
        ((measurableSet_pcnBox (d := d) R).union (measurableSet_singleton x)).compl]
      simp
  | succ n ih =>
      rw [pcnIter_succ]
      refine bind_eq_zero_of_support ((measurableSet_pcnBox (d := d) R).union
        (measurableSet_singleton x)) (pcnAbsorbingStep_confined (d := d) (s := s) (ρ := ρ)
          (R := R) (τ := τ) x) (measurable_pcnIter hmeas n).aemeasurable ?_
      intro y hy
      have hsub : (pcnBox d R ∪ {x})ᶜ ⊆ (pcnBox d R ∪ {y})ᶜ := by
        intro z hz
        simp only [Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff] at hz ⊢
        rintro (hzb | hzy)
        · exact hz (Or.inl hzb)
        · exact hz (hzy ▸ hy)
      exact measure_mono_null hsub (ih y)

/-- The return constant at a uniform radius `M`: `(√(π s))^d · exp (−(2ρ²M² + 2dR²)/s)`. -/
noncomputable def pcnBallConst (s ρ R M : ℝ) : ℝ :=
  pcnNorm1 s ^ d * Real.exp (-(2 * ρ ^ 2 * M ^ 2 + 2 * (d : ℝ) * R ^ 2) / s)

theorem pcnBallConst_pos {s ρ R M : ℝ} (hs : 0 < s) :
    0 < pcnBallConst (d := d) s ρ R M :=
  mul_pos (pow_pos (pcnNorm1_pos hs) _) (Real.exp_pos _)

/-- **The return mass is uniform on a ball of starting points**: if `‖x‖² ≤ M²`, the step returns
to the box with mass at least `m · pcnBallConst s ρ R M · (2R)^d`. -/
theorem pcnAbsorbingStep_box_ge_ball {s ρ R B m M : ℝ} {τ : (Fin d → ℝ) → ℝ}
    {x : Fin d → ℝ} (hs : 0 < s) (hR : 0 ≤ R) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hτx : 0 < τ x) (hτxB : τ x ≤ B) (hτfloor : ∀ y ∈ pcnBox d R, m * B ≤ τ y)
    (hxM : pcnSumSq x ≤ M ^ 2) :
    ENNReal.ofReal (m * pcnBallConst (d := d) s ρ R M * (2 * R) ^ d)
      ≤ pcnAbsorbingStep (d := d) s ρ R τ x (pcnBox d R) := by
  have hle : pcnBallConst (d := d) s ρ R M ≤ pcnReturnConst (d := d) s ρ R x := by
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
      (pow_nonneg (pcnNorm1_pos hs).le d)
    have hsq : 2 * ρ ^ 2 * pcnSumSq x ≤ 2 * ρ ^ 2 * M ^ 2 :=
      mul_le_mul_of_nonneg_left hxM (by nlinarith [sq_nonneg ρ])
    rw [neg_div, neg_div, neg_le_neg_iff, div_le_div_iff_of_pos_right hs]
    linarith
  refine le_trans (ENNReal.ofReal_le_ofReal ?_)
    (pcnAbsorbingStep_box_ge_start (d := d) (s := s) (ρ := ρ) (R := R) (B := B) (m := m)
      (τ := τ) (x := x) hs hR hm0 hm1 hτx hτxB hτfloor)
  refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hle hm0) ?_
  positivity

theorem pcnSumSq_le_of_mem_box {R : ℝ} {y : Fin d → ℝ} (hy : y ∈ pcnBox d R) :
    pcnSumSq y ≤ (d : ℝ) * R ^ 2 := by
  have hb : ∀ i : Fin d, |y i| ≤ R := mem_pcnBox.mp hy
  calc pcnSumSq y = ∑ i, y i ^ 2 := rfl
    _ ≤ ∑ _i : Fin d, R ^ 2 := Finset.sum_le_sum fun i _ => by
        have hi := abs_le.mp (hb i)
        nlinarith [hi.1, hi.2]
    _ = (d : ℝ) * R ^ 2 := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- **The chain stays in the ball of its start.**  Every point the `n`-step measure can reach has
`‖z‖² ≤ max (dR²) ‖x‖²`, so a start with `‖x‖² ≤ M²` keeps the chain inside `‖z‖² ≤ max (dR²) M²`.
That is the confinement the return constant `pcnBallConst` is uniform on. -/
theorem pcnIter_confined_ball {s ρ R : ℝ} {τ : (Fin d → ℝ) → ℝ}
    (hτ : Measurable τ) (n : ℕ) (x : Fin d → ℝ) :
    pcnIter (pcnAbsorbingStep (d := d) s ρ R τ) n x
      {z : Fin d → ℝ | max ((d : ℝ) * R ^ 2) (pcnSumSq x) < pcnSumSq z} = 0 := by
  have hmeas : Measurable (pcnAbsorbingStep (d := d) s ρ R τ) :=
    measurable_pcnAbsorbingStep s ρ R hτ
  refine measure_mono_null ?_
    (pcnIter_confined (d := d) (s := s) (ρ := ρ) (R := R) (τ := τ) hτ n x)
  intro z hz
  simp only [Set.mem_setOf_eq, Set.mem_compl_iff, Set.mem_union, Set.mem_singleton_iff,
    not_or] at hz ⊢
  refine ⟨?_, ?_⟩
  · intro hzb
    exact absurd (pcnSumSq_le_of_mem_box hzb)
      (not_le.mpr (lt_of_le_of_lt (le_max_left _ _) hz))
  · intro hzx
    rw [hzx] at hz
    exact absurd (le_max_right _ _) (not_le.mpr hz)

/-! ## 16. The reversible reference: `τ · pcnPrior`

§14 showed that the step's reversibility is with respect to `volume.withDensity (τ · pcnPrior)`, not
§3–§13's `volume.withDensity τ`.  This section restates what carries over: the minorant, its
prior-referenced form, and the rate, with the corrected reference named.

* **`pcnPriorTarget`** — the reference measure `volume.withDensity (τ · pcnPrior)` on the box;
* **`pcnAbsorbingStep_minorant_prior`** — the §10 minorant for that reference: the acceptance floors
  stay on `τ` (the likelihood), while the ceiling `B` and the target are on `τ · pcnPrior`;
* **`pcnAbsorbingStep_rate_prior`** — §9's rate with the corrected reference.
-/

/-- The reversible reference on the box: `volume.withDensity (τ · pcnPrior)`. -/
noncomputable def pcnPriorTarget (s ρ R : ℝ) (τ : (Fin d → ℝ) → ℝ) : Measure (Fin d → ℝ) :=
  pcnTargetMeasure (d := d) R fun y => τ y * pcnPrior s ρ y

/-- **The Doeblin minorant against the reversible reference.**  The acceptance floor is a statement
about the *likelihood* `τ`; the ceiling and the target are about `τ · pcnPrior`. -/
theorem pcnAbsorbingStep_minorant_prior {s ρ R F B m : ℝ} {τ : (Fin d → ℝ) → ℝ}
    {x : Fin d → ℝ} (hF : 0 ≤ F) (hB : 0 < B) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hB' : ∀ y ∈ pcnBox d R, τ y * pcnPrior s ρ y ≤ B) (hτx : 0 < τ x)
    (hτxy : ∀ y ∈ pcnBox d R, m * τ x ≤ τ y)
    (hdens : ∀ y ∈ pcnBox d R, F ≤ pcnDensity (pcnNorm1 s ^ d) s ρ x y) :
    ENNReal.ofReal (m * F / B) • pcnPriorTarget (d := d) s ρ R τ
      ≤ pcnAbsorbingStep (d := d) s ρ R τ x := by
  have hmF0 : 0 ≤ m * F := mul_nonneg hm0 hF
  have hfloor : ∀ y ∈ pcnBox d R,
      m * F ≤ pcnMetropolisDensity (pcnNorm1 s ^ d) s ρ τ x y :=
    fun y hy => pcnMetropolis_floor hm0 hF (pcnAccept_floor hm1 hτx (hτxy y hy)) (hdens y hy)
  have hπ : pcnPriorTarget (d := d) s ρ R τ
      ≤ ENNReal.ofReal B • (volume.restrict (pcnBox d R)) :=
    pcnTargetMeasure_le_smul hB'
  have hμ : ENNReal.ofReal (m * F) • (volume.restrict (pcnBox d R))
      ≤ pcnMetropolisStep (pcnNorm1 s ^ d) s ρ R τ x :=
    pcnMetropolis_minorant hfloor
  calc ENNReal.ofReal (m * F / B) • pcnPriorTarget (d := d) s ρ R τ
      ≤ ENNReal.ofReal (m * F / B) •
          (ENNReal.ofReal B • (volume.restrict (pcnBox d R))) := smul_measure_mono hπ
    _ = ENNReal.ofReal (m * F) • (volume.restrict (pcnBox d R)) := by
        rw [smul_smul, ofReal_div_mul_ofReal hmF0 hB]
    _ ≤ pcnMetropolisStep (pcnNorm1 s ^ d) s ρ R τ x := hμ
    _ ≤ pcnAbsorbingStep (d := d) s ρ R τ x :=
        pcnMetropolisStep_le_pcnAbsorbingStep s ρ R τ x

/-- **The rate with the reversible reference.**  §9's contraction with `π` the prior-referenced
target: the two remaining hypotheses are the minorant (supplied by
`pcnAbsorbingStep_minorant_prior` on the box) and invariance of `pcnPriorTarget` under the step. -/
theorem pcnAbsorbingStep_rate_prior {s ρ R c : ℝ} {τ : (Fin d → ℝ) → ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) (hs : 0 < s) (hτ : Measurable τ)
    [IsProbabilityMeasure (pcnPriorTarget (d := d) s ρ R τ)]
    (hmin : ∀ x, ENNReal.ofReal c • pcnPriorTarget (d := d) s ρ R τ
      ≤ pcnAbsorbingStep (d := d) s ρ R τ x)
    (hstat : ∀ n, (pcnPriorTarget (d := d) s ρ R τ).bind
      (pcnIter (pcnAbsorbingStep (d := d) s ρ R τ) n) = pcnPriorTarget (d := d) s ρ R τ)
    (n : ℕ) (x : Fin d → ℝ) {S : Set (Fin d → ℝ)} (hS : MeasurableSet S) :
    ENNReal.ofReal (1 - (1 - c) ^ n) * pcnPriorTarget (d := d) s ρ R τ S
      ≤ pcnIter (pcnAbsorbingStep (d := d) s ρ R τ) n x S :=
  pcnAbsorbingStep_rate hc0 hc1 hs hτ hmin hstat n x hS

/-- **Two steps with a constant uniform on a ball of starts.**  §12's two-step minorant with §15's
uniform return mass: for every start with `‖x‖² ≤ M²` the constant is the same,
`m · pcnBallConst s ρ R M · (2R)^d · (mF/B)`. -/
theorem pcnAbsorbingStep_twoStep_minorant_ball {s ρ R F B m M : ℝ} {τ : (Fin d → ℝ) → ℝ}
    {x : Fin d → ℝ} (hF : 0 ≤ F) (hB : 0 < B) (hm0 : 0 ≤ m) (hm1 : m ≤ 1)
    (hτB : ∀ y ∈ pcnBox d R, τ y ≤ B)
    (hτpos : ∀ y ∈ pcnBox d R, 0 < τ y)
    (hτxy : ∀ y ∈ pcnBox d R, ∀ z ∈ pcnBox d R, m * τ y ≤ τ z)
    (hdens : ∀ y ∈ pcnBox d R, ∀ z ∈ pcnBox d R, F ≤ pcnDensity (pcnNorm1 s ^ d) s ρ y z)
    (hτ : Measurable τ) (hs : 0 < s) (hR : 0 ≤ R) (hτx0 : 0 < τ x) (hτxB : τ x ≤ B)
    (hτfloor : ∀ y ∈ pcnBox d R, m * B ≤ τ y)
    (hxM : pcnSumSq x ≤ M ^ 2) :
    (ENNReal.ofReal (m * pcnBallConst (d := d) s ρ R M * (2 * R) ^ d)
        * ENNReal.ofReal (m * F / B)) • pcnTargetMeasure (d := d) R τ
      ≤ (pcnAbsorbingStep (d := d) s ρ R τ x).bind
          (pcnAbsorbingStep (d := d) s ρ R τ) :=
  bind_minorant_of_set (measurableSet_pcnBox (d := d) R)
    (measurable_pcnAbsorbingStep s ρ R hτ).aemeasurable
    (pcnAbsorbingStep_box_ge_ball (d := d) (s := s) (ρ := ρ) (R := R) (B := B) (m := m)
      (M := M) (τ := τ) (x := x) hs hR hm0 hm1 hτx0 hτxB hτfloor hxM)
    (fun y hy => pcnAbsorbingStep_minorant hF hB hm0 hm1 hτB (hτpos y hy) (hτxy y hy)
      (hdens y hy))

/-! ## 17. Detailed balance becomes stationarity

§14–§16 proved the step's reversibility *pointwise*: `τ · pcnPrior`-weighted detail balance on pairs
`(x, y)`.  This section does the passage to a statement about measures — `π.bind K = π` — which is
what the rate of §9 consumes.

* `doeblinStep ν k` — the general Metropolis step built from a joint density `k` against `ν`: the
  accepted part `ν.withDensity (k x)` plus the rejected mass as an atom at `x`;
* **`bind_doeblinStep_stationary`** — **detailed balance implies stationarity**: if
  `k x y · g x = k y x · g y` and no forward mass exceeds `1`, then `ν.withDensity g` is invariant
  under `doeblinStep ν k`.  The proof is Tonelli's theorem on the symmetric joint density: the
  accepted mass into `A` is `∫_A g · I` (`I y` the forward mass from `y`, via the symmetry), the
  rejection atom contributes `g · (1 − I)` on `A`, and `I + (1 − I) = 1` there;
* `measurable_setLIntegral`, `measurable_doeblinStep_apply` — the measurability inputs, from joint
  measurability of the density;
* **`pcnPriorTarget_stationary`** — the pCN instance: §16's reference
  `volume.withDensity (τ · pcnPrior)` is invariant under the pCN Metropolis step with its rejection
  atom — the theorem §14–§16 left as "the integral passage not written";
* **`pcnAbsorbingStep_rate_prior_of_stationary`** — and §16's rate with its invariance hypothesis
  discharged instead of assumed.

**What remains hypotheses.**  `Measurable τ` — a property of the target's formula — and, in the
rate, `IsProbabilityMeasure (pcnPriorTarget s ρ R τ)`.  The step's own measurability is *not* a
hypothesis:
§9's `measurable_pcnAbsorbingStep` proves it.  The probability hypothesis is replaced in §19 by the
reference's mass `M`, which §18's constants bound on both sides; it is not proved to be `1`, because
`∫_{box} τ · pcnPrior` is not `1` for a general target.
-/

variable {α : Type*} [MeasurableSpace α]

/-- The Metropolis-type step built from a joint density `k` against a base measure `ν`: the accepted
part `ν.withDensity (k x)` plus the rejected mass kept as an atom at the start. -/
noncomputable def doeblinStep (ν : Measure α) (k : α → α → ENNReal) (x : α) : Measure α :=
  ν.withDensity (k x) + (1 - ∫⁻ y, k x y ∂ν) • Measure.dirac x

theorem doeblinStep_apply {ν : Measure α} [SFinite ν] {k : α → α → ENNReal} {x : α}
    {A : Set α} (hA : MeasurableSet A) :
    doeblinStep ν k x A
      = ∫⁻ y in A, k x y ∂ν + (1 - ∫⁻ y, k x y ∂ν) * A.indicator 1 x := by
  classical
  rw [doeblinStep, Measure.add_apply, withDensity_apply _ hA, Measure.smul_apply,
    Measure.dirac_apply' x hA, smul_eq_mul]

theorem measurable_doeblinStep_apply {ν : Measure α} [SFinite ν] {k : α → α → ENNReal}
    (hk : Measurable (Function.uncurry k)) {A : Set α} (hA : MeasurableSet A) :
    Measurable fun x => doeblinStep ν k x A := by
  classical
  have hI : Measurable fun x => ∫⁻ y, k x y ∂ν := hk.lintegral_prod_right
  have hd : (fun x => doeblinStep ν k x A)
      = fun x => ∫⁻ y in A, k x y ∂ν + (1 - ∫⁻ y, k x y ∂ν) * A.indicator 1 x :=
    funext fun x => doeblinStep_apply (ν := ν) (k := k) (x := x) hA
  rw [hd]
  exact (measurable_setLIntegral hk hA).add ((by fun_prop : Measurable fun x => (1 : ENNReal)
    - ∫⁻ y, k x y ∂ν).mul (Measurable.indicator measurable_const hA))

/-- **Stationarity from detailed balance.**  If a joint density `k` against `ν` satisfies the
pointwise balance `k x y · g x = k y x · g y` against the unnormalised target density `g`, and no
forward mass exceeds `1`, then the Metropolis step `ν.withDensity (k x)` — with its rejection atom —
leaves `ν.withDensity g` invariant.

The proof is Tonelli on the symmetric joint density: the accepted mass into `A` is
`∫_A g · I`, where `I y` is the forward mass of the step from `y`, and the rejection atom
contributes `g · (1 − I)` on `A`; the two add to `g` there. -/
theorem bind_doeblinStep_stationary {ν : Measure α} [SFinite ν] {g : α → ENNReal}
    {k : α → α → ENNReal} (hg : Measurable g) (hk : Measurable (Function.uncurry k))
    (hKmeas : AEMeasurable (doeblinStep ν k) (ν.withDensity g))
    (hsym : ∀ x y, k x y * g x = k y x * g y)
    (hbound : ∀ x, ∫⁻ y, k x y ∂ν ≤ 1) :
    (ν.withDensity g).bind (doeblinStep ν k) = ν.withDensity g := by
  classical
  have hI : Measurable fun x => ∫⁻ y, k x y ∂ν := hk.lintegral_prod_right
  ext A hA
  have hKh := measurable_setLIntegral (ν := ν) hk hA
  have hstepA : Measurable fun x => doeblinStep ν k x A :=
    measurable_doeblinStep_apply hk hA
  rw [Measure.bind_apply hA hKmeas,
    lintegral_withDensity_eq_lintegral_mul ν hg hstepA, withDensity_apply _ hA]
  have hRHS : ∫⁻ x in A, g x ∂ν = ∫⁻ x, g x * A.indicator 1 x ∂ν := by
    rw [← lintegral_indicator hA (fun x => g x)]
    exact lintegral_congr fun x => by
      by_cases hx : x ∈ A <;> simp [hx]
  rw [hRHS]
  -- ### the accepted part, by Tonelli on the symmetric joint density
  have hswap : ∫⁻ x, g x * (∫⁻ y in A, k x y ∂ν) ∂ν
      = ∫⁻ y, A.indicator 1 y * (g y * ∫⁻ x, k y x ∂ν) ∂ν := by
    have h1 : ∫⁻ x, g x * (∫⁻ y in A, k x y ∂ν) ∂ν
        = ∫⁻ x, ∫⁻ y, g x * (k x y * A.indicator 1 y) ∂ν ∂ν := by
      refine lintegral_congr fun x => ?_
      calc g x * (∫⁻ y in A, k x y ∂ν)
          = g x * ∫⁻ y, A.indicator (fun y => k x y) y ∂ν := by
            rw [lintegral_indicator hA (fun y => k x y)]
        _ = ∫⁻ y, g x * A.indicator (fun y => k x y) y ∂ν :=
            (lintegral_const_mul (g x)
              ((hk.comp (measurable_prodMk_left (x := x))).indicator hA)).symm
        _ = ∫⁻ y, g x * (k x y * A.indicator 1 y) ∂ν := by
            refine lintegral_congr fun y => ?_
            congr 1
            by_cases hy : y ∈ A
            · rw [Set.indicator_of_mem hy, Set.indicator_of_mem hy, Pi.one_apply, mul_one]
            · rw [Set.indicator_of_notMem hy, Set.indicator_of_notMem hy, mul_zero]
    have h2 : Measurable fun p : α × α =>
        g p.1 * (k p.1 p.2 * (if p.2 ∈ A then 1 else 0)) :=
      (hg.comp measurable_fst).mul (hk.mul (measurable_const.indicator
        (hA.preimage measurable_snd)))
    have h3 : ∫⁻ x, ∫⁻ y, g x * (k x y * A.indicator 1 y) ∂ν ∂ν
        = ∫⁻ y, ∫⁻ x, g x * (k x y * A.indicator 1 y) ∂ν ∂ν :=
      lintegral_lintegral_swap h2.aemeasurable
    rw [h1, h3]
    refine lintegral_congr fun y => ?_
    calc ∫⁻ x, g x * (k x y * A.indicator 1 y) ∂ν
        = ∫⁻ x, (g x * k x y) * A.indicator 1 y ∂ν :=
          lintegral_congr fun x => by ring
      _ = (∫⁻ x, g x * k x y ∂ν) * A.indicator 1 y :=
          lintegral_mul_const _
            (hg.mul (hk.comp (measurable_prodMk_right (y := y))))
      _ = (g y * ∫⁻ x, k y x ∂ν) * A.indicator 1 y := by
          congr 1
          calc ∫⁻ x, g x * k x y ∂ν = ∫⁻ x, k y x * g y ∂ν :=
                lintegral_congr fun x => by rw [mul_comm (g x), hsym x y]
            _ = (∫⁻ x, k y x ∂ν) * g y :=
                lintegral_mul_const _ (hk.comp (measurable_prodMk_left (x := y)))
            _ = g y * ∫⁻ x, k y x ∂ν := mul_comm _ _
      _ = A.indicator 1 y * (g y * ∫⁻ x, k y x ∂ν) := mul_comm _ _
  -- ### the rejected atom
  have hsplit : ∫⁻ x, g x * (∫⁻ y in A, k x y ∂ν
      + (1 - ∫⁻ y, k x y ∂ν) * A.indicator 1 x) ∂ν
      = ∫⁻ x, g x * (∫⁻ y in A, k x y ∂ν) ∂ν
        + ∫⁻ x, g x * ((1 - ∫⁻ y, k x y ∂ν) * A.indicator 1 x) ∂ν := by
    have hpt : (fun x => g x * (∫⁻ y in A, k x y ∂ν
        + (1 - ∫⁻ y, k x y ∂ν) * A.indicator 1 x))
        = fun x => g x * (∫⁻ y in A, k x y ∂ν)
          + g x * ((1 - ∫⁻ y, k x y ∂ν) * A.indicator 1 x) :=
      funext fun x => mul_add _ _ _
    rw [hpt]
    exact lintegral_add_left (hg.mul hKh) _
  -- ### the two parts add to the target
  have hcancel : ∀ y, g y * ((1 - ∫⁻ x, k y x ∂ν) * A.indicator 1 y)
      + A.indicator 1 y * (g y * ∫⁻ x, k y x ∂ν) = g y * A.indicator 1 y := by
    intro y
    have h1 : (1 - ∫⁻ x, k y x ∂ν) + ∫⁻ x, k y x ∂ν = 1 :=
      tsub_add_cancel_of_le (hbound y)
    calc g y * ((1 - ∫⁻ x, k y x ∂ν) * A.indicator 1 y)
          + A.indicator 1 y * (g y * ∫⁻ x, k y x ∂ν)
        = (g y * A.indicator 1 y) * (1 - ∫⁻ x, k y x ∂ν)
            + (g y * A.indicator 1 y) * ∫⁻ x, k y x ∂ν := by ring
      _ = (g y * A.indicator 1 y) * ((1 - ∫⁻ x, k y x ∂ν) + ∫⁻ x, k y x ∂ν) := by ring
      _ = (g y * A.indicator 1 y) * 1 := by rw [h1]
      _ = g y * A.indicator 1 y := mul_one _
  simp only [Pi.mul_apply]
  rw [show (fun x => g x * doeblinStep ν k x A) = fun x => g x * (∫⁻ y in A, k x y ∂ν
      + (1 - ∫⁻ y, k x y ∂ν) * A.indicator 1 x) from
    funext fun x => by rw [doeblinStep_apply hA]]
  rw [hsplit, hswap, add_comm]
  have hf : Measurable fun x => g x * ((1 - ∫⁻ y, k x y ∂ν) * A.indicator 1 x) :=
    hg.mul ((by fun_prop : Measurable fun x => (1 : ENNReal) - ∫⁻ y, k x y ∂ν).mul
      (Measurable.indicator measurable_const hA))
  exact (lintegral_add_left hf
    fun x => A.indicator 1 x * (g x * ∫⁻ y, k x y ∂ν)).symm.trans
    (lintegral_congr fun x => hcancel x)

section PCN

theorem measurable_pcnPrior (s ρ : ℝ) :
    Measurable (pcnPrior (d := d) s ρ) := by
  have hsum : Measurable (pcnSumSq (d := d)) := by
    unfold pcnSumSq
    exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).pow_const 2
  unfold pcnPrior
  exact Real.measurable_exp.comp (by fun_prop)

theorem pcnMetropolisDensity_nonneg {c s ρ : ℝ} {τ : (Fin d → ℝ) → ℝ} {x y : Fin d → ℝ}
    (hc : 0 ≤ c) (hx : 0 < τ x) (hy : 0 ≤ τ y) :
    0 ≤ pcnMetropolisDensity c s ρ τ x y := by
  unfold pcnMetropolisDensity pcnDensity
  exact mul_nonneg (pcnAccept_nonneg hx hy) (mul_nonneg hc (Real.exp_pos _).le)

/-- The pCN Metropolis step *is* the abstract Metropolis step of this section, at the increment's
own constant `c = (√(π s))^d`. -/
theorem pcnAbsorbingStep_eq_doeblinStep (s ρ R : ℝ) (τ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) :
    pcnAbsorbingStep (d := d) s ρ R τ x
      = doeblinStep (volume.restrict (pcnBox d R))
          (fun _ y => ENNReal.ofReal (pcnMetropolisDensity (pcnNorm1 s ^ d) s ρ τ x y)) x := by
  rw [pcnAbsorbingStep, pcnMetropolisStep, doeblinStep, withDensity_apply _ MeasurableSet.univ,
    setLIntegral_univ]

/-- **The pCNL target measure is invariant under the Metropolis step.**  With the reversible
reference `pcnPriorTarget s ρ R τ = volume.withDensity (τ · pcnPrior)` of §16, the pCN Metropolis
step with its rejection atom leaves it invariant: detailed balance into `π.bind K = π` (§17).

The only hypothesis is the reference's measurability; the step's is `measurable_pcnAbsorbingStep`,
a property of its explicit formula. -/
theorem pcnPriorTarget_stationary (s ρ R : ℝ) {τ : (Fin d → ℝ) → ℝ} (hs : 0 < s)
    (hτ : Measurable τ) (hτpos : ∀ x, 0 < τ x) :
    (pcnPriorTarget (d := d) s ρ R τ).bind (pcnAbsorbingStep (d := d) s ρ R τ)
      = pcnPriorTarget (d := d) s ρ R τ := by
  have hstep : (fun x => pcnAbsorbingStep (d := d) s ρ R τ x)
      = fun x => doeblinStep (volume.restrict (pcnBox d R))
          (fun _ y => ENNReal.ofReal (pcnMetropolisDensity (pcnNorm1 s ^ d) s ρ τ x y)) x :=
    funext (pcnAbsorbingStep_eq_doeblinStep s ρ R τ)
  have hg : Measurable fun y : Fin d → ℝ => ENNReal.ofReal (τ y * pcnPrior s ρ y) :=
    (hτ.mul (measurable_pcnPrior s ρ)).ennreal_ofReal
  refine (congrArg (fun K => (pcnPriorTarget (d := d) s ρ R τ).bind K) hstep).trans ?_
  refine bind_doeblinStep_stationary hg
    ((measurable_pcnMetropolisDensity_uncurry hτ (pcnNorm1 s ^ d) s ρ).ennreal_ofReal) ?_ ?_ ?_
  · simpa [hstep] using (measurable_pcnAbsorbingStep s ρ R hτ).aemeasurable
  · intro x y
    have hdy : 0 ≤ pcnMetropolisDensity (pcnNorm1 s ^ d) s ρ τ y x :=
      pcnMetropolisDensity_nonneg (pow_nonneg (pcnNorm1_pos hs).le d) (hτpos y) (hτpos x).le
    have hdx : 0 ≤ pcnMetropolisDensity (pcnNorm1 s ^ d) s ρ τ x y :=
      pcnMetropolisDensity_nonneg (pow_nonneg (pcnNorm1_pos hs).le d) (hτpos x) (hτpos y).le
    rw [← ENNReal.ofReal_mul hdx, mul_comm (pcnMetropolisDensity (pcnNorm1 s ^ d) s ρ τ x y),
      pcnMetropolisDensity_detailed (c := pcnNorm1 s ^ d) (s := s) (ρ := ρ) (τ := τ)
        (x := x) (y := y) hs.ne' (hτpos x) (hτpos y)]
    change ENNReal.ofReal (τ y * pcnPrior s ρ y
        * pcnMetropolisDensity (pcnNorm1 s ^ d) s ρ τ y x)
      = ENNReal.ofReal (pcnMetropolisDensity (pcnNorm1 s ^ d) s ρ τ y x) *
        ENNReal.ofReal (τ y * pcnPrior s ρ y)
    rw [show τ y * pcnPrior s ρ y * pcnMetropolisDensity (pcnNorm1 s ^ d) s ρ τ y x
          = pcnMetropolisDensity (pcnNorm1 s ^ d) s ρ τ y x * (τ y * pcnPrior s ρ y) from by ring,
      ← ENNReal.ofReal_mul hdy]
  · intro x
    have hm := pcnMetropolisStep_mass_le_one (d := d) (s := s) (ρ := ρ) (R := R) hs x τ
    rwa [pcnMetropolisStep, withDensity_apply _ MeasurableSet.univ, setLIntegral_univ] at hm

/-- **The rate with invariance proved rather than assumed.**  §17 supplies stationarity
(`pcnPriorTarget_stationary`) and `pcnStat_iter` extends it to the iterates, so the only inputs left
are the minorant of §16 and the reference's normalisation. -/
theorem pcnAbsorbingStep_rate_prior_of_stationary (s ρ R : ℝ) {τ : (Fin d → ℝ) → ℝ}
    {c : ℝ} (hc0 : 0 < c) (hc1 : c < 1) (hs : 0 < s) (hτ : Measurable τ)
    (hτpos : ∀ x, 0 < τ x)
    [IsProbabilityMeasure (pcnPriorTarget (d := d) s ρ R τ)]
    (hmin : ∀ x, ENNReal.ofReal c • pcnPriorTarget (d := d) s ρ R τ
      ≤ pcnAbsorbingStep (d := d) s ρ R τ x)
    (n : ℕ) (x : Fin d → ℝ) {S : Set (Fin d → ℝ)} (hS : MeasurableSet S) :
    ENNReal.ofReal (1 - (1 - c) ^ n) * pcnPriorTarget (d := d) s ρ R τ S
      ≤ pcnIter (pcnAbsorbingStep (d := d) s ρ R τ) n x S :=
  pcnAbsorbingStep_rate_prior hc0 hc1 hs hτ hmin
    (fun n => pcnStat_iter (measurable_pcnAbsorbingStep s ρ R hτ)
      (pcnPriorTarget_stationary s ρ R hs hτ hτpos) n) n x hS

/-! ## 18. The minorant with its constants computed

§16's minorant takes the ceiling `B` and the acceptance floor `m` as parameters.  For the natural
family of targets these are numbers, not hypotheses: a Gaussian likelihood
`τ y = exp (−β‖y‖²)` satisfies

* `τ y · pcnPrior y ≤ 1` on the whole space (`pcnGaussLike_mul_pcnPrior_le_one`) — so `B = 1`;
* `m · τ x ≤ τ y` with `m = exp (−β dR²)` on the box, from `∑yᵢ² ≤ dR²`
  (`pcnGaussLike_floor`, `pcnGaussLike_le_one`).

* `pcnGaussLike` — the likelihood, with `pcnGaussLike_measurable`, `pcnGaussLike_pos`;
* `pcnGaussLike_le_one`, **`pcnGaussLike_floor`** — its bounds at `0` and on the box;
* `pcnPrior_le_one`, **`pcnPrior_floor`** — the same two for the prior factor;
* **`pcnGaussLike_mul_pcnPrior_le_one`** — the ceiling;
* **`pcnAbsorbingStep_minorant_prior_gaussLike`** — §16's minorant with `B = 1` and
  `m = exp (−β dR²)` substituted.

The proposal floor `F` stays a parameter: it is §1's floor on the box, and `pcnDensity_floor`
supplies it whenever the start is in the box.
-/

/-! ## 19. The reference's mass, and the rate with the probability hypothesis discharged

§16–§17's rate assumes `[IsProbabilityMeasure (pcnPriorTarget s ρ R τ)]`.  That hypothesis is *not*
free: `pcnPriorTarget = volume.withDensity (τ · pcnPrior)` on the box, whose total mass is
`∫_{box} τ · pcnPrior`, and it equals `1` only for the one `τ` that cancels the prior.  So this
section does not prove mass one — it names the mass and normalises by it.

* `pcnPriorMass` — the total mass, `pcnPriorTarget univ`, and `pcnPriorMass_eq_lintegral` identifies
  it as the box integral;
* **`pcnPriorMass_le`** — `≤ B · (2R)^d` from the ceiling, hence `pcnPriorMass_ne_top`;
* **`pcnPriorMass_pos`** — positive from a floor and a nondegenerate box;
* `pcnPriorProb` — the normalised reference `M⁻¹ • pcnPriorTarget`, with
  **`pcnPriorProb_univ`** and `isProbabilityMeasure_pcnPriorProb`;
* **`pcnPriorProb_stationary`** — invariance survives the normalisation (`Measure.bind_smul`);
* **`pcnPriorProb_minorant_of_target`** — a minorant against the unnormalised reference transfers
  to the normalised one, with the constant multiplied by `M`;
* **`pcnAbsorbingStep_rate_prob`** — the rate for the normalised reference, with
  `IsProbabilityMeasure` proved (`haveI`) rather than assumed;
* `pcnPriorMass_gaussLike_le`, `pcnPriorMass_gaussLike_pos` — §18's likelihood has
  `0 < M ≤ (2R)^d`.

**What this does and does not discharge.**  The rate no longer assumes the reference is a
probability: it assumes a mass `M` with `pcnPriorMass = ofReal M` and `0 < M`, which §18's constants
bound.  It does not compute `M` exactly, and the normalised reference is a different measure from
§3–§16's `volume.withDensity (τ · pcnPrior)` by the constant `M`.
-/

/-! ## 18. Explicit constants at a Gaussian likelihood -/

/-- A Gaussian likelihood `exp (−β‖y‖²)`. -/
noncomputable def pcnGaussLike (β : ℝ) (y : Fin d → ℝ) : ℝ := Real.exp (-(β * pcnSumSq y))

theorem pcnGaussLike_pos (β : ℝ) (y : Fin d → ℝ) : 0 < pcnGaussLike (d := d) β y :=
  Real.exp_pos _

theorem pcnGaussLike_measurable (β : ℝ) : Measurable (pcnGaussLike (d := d) β) := by
  have hsum : Measurable (pcnSumSq (d := d)) := by
    unfold pcnSumSq
    exact Finset.measurable_sum _ fun i _ => (measurable_pi_apply i).pow_const 2
  unfold pcnGaussLike
  exact Real.measurable_exp.comp (by fun_prop)

theorem pcnGaussLike_le_one {β : ℝ} (hβ : 0 ≤ β) (y : Fin d → ℝ) :
    pcnGaussLike (d := d) β y ≤ 1 := by
  rw [pcnGaussLike, Real.exp_le_one_iff]
  have h : 0 ≤ β * pcnSumSq y := mul_nonneg hβ (pcnSumSq_nonneg y)
  linarith

/-- The likelihood's floor on the box: `exp (−β dR²)`. -/
theorem pcnGaussLike_floor {β R : ℝ} (hβ : 0 ≤ β) {y : Fin d → ℝ} (hy : y ∈ pcnBox d R) :
    Real.exp (-(β * ((d : ℝ) * R ^ 2))) ≤ pcnGaussLike (d := d) β y := by
  rw [pcnGaussLike]
  refine Real.exp_le_exp.mpr ?_
  have h := pcnSumSq_le_of_mem_box hy
  have : β * pcnSumSq y ≤ β * ((d : ℝ) * R ^ 2) := mul_le_mul_of_nonneg_left h hβ
  linarith

theorem pcnPrior_le_one {s ρ : ℝ} (hs : 0 < s) (hρ : ρ ^ 2 ≤ 1) (y : Fin d → ℝ) :
    pcnPrior (d := d) s ρ y ≤ 1 := by
  rw [pcnPrior, Real.exp_le_one_iff]
  have h1 : 0 ≤ 1 - ρ ^ 2 := by linarith
  have h2 : 0 ≤ (1 - ρ ^ 2) * pcnSumSq y := mul_nonneg h1 (pcnSumSq_nonneg y)
  exact div_nonpos_of_nonpos_of_nonneg (by linarith) hs.le

/-- The prior's floor on the box: `exp (−(1 − ρ²) dR² / s)`. -/
theorem pcnPrior_floor {s ρ R : ℝ} (hs : 0 < s) (hρ : ρ ^ 2 ≤ 1) {y : Fin d → ℝ}
    (hy : y ∈ pcnBox d R) :
    Real.exp (-((1 - ρ ^ 2) * ((d : ℝ) * R ^ 2)) / s) ≤ pcnPrior (d := d) s ρ y := by
  rw [pcnPrior]
  refine Real.exp_le_exp.mpr ?_
  have h1 : 0 ≤ 1 - ρ ^ 2 := by linarith
  have h2 : (1 - ρ ^ 2) * pcnSumSq y ≤ (1 - ρ ^ 2) * ((d : ℝ) * R ^ 2) :=
    mul_le_mul_of_nonneg_left (pcnSumSq_le_of_mem_box hy) h1
  rw [neg_div, neg_div, neg_le_neg_iff]
  exact div_le_div_of_nonneg_right h2 hs.le

/-- The ceiling for the prior-referenced density: `τ · pcnPrior ≤ 1`. -/
theorem pcnGaussLike_mul_pcnPrior_le_one {s ρ β : ℝ} (hs : 0 < s) (hρ : ρ ^ 2 ≤ 1)
    (hβ : 0 ≤ β) (y : Fin d → ℝ) :
    pcnGaussLike (d := d) β y * pcnPrior (d := d) s ρ y ≤ 1 := by
  have h1 := pcnGaussLike_le_one hβ y
  have h2 := pcnPrior_le_one hs hρ y
  have h0 : 0 ≤ pcnPrior (d := d) s ρ y := (pcnPrior_pos s ρ y).le
  nlinarith [h1, h2, h0, pcnGaussLike_pos β y]

/-- **§16's minorant with its ceiling and acceptance floor computed**: for a Gaussian likelihood,
`B = 1` and `m = exp (−β dR²)`. -/
theorem pcnAbsorbingStep_minorant_prior_gaussLike {s ρ R F β : ℝ} {x : Fin d → ℝ}
    (hs : 0 < s) (hρ : ρ ^ 2 ≤ 1) (hβ : 0 ≤ β) (hF : 0 ≤ F)
    (hdens : ∀ y ∈ pcnBox d R, F ≤ pcnDensity (pcnNorm1 s ^ d) s ρ x y) :
    ENNReal.ofReal (Real.exp (-(β * ((d : ℝ) * R ^ 2))) * F / 1)
        • pcnPriorTarget (d := d) s ρ R (pcnGaussLike (d := d) β)
      ≤ pcnAbsorbingStep (d := d) s ρ R (pcnGaussLike (d := d) β) x := by
  refine pcnAbsorbingStep_minorant_prior (F := F) (B := 1)
    (m := Real.exp (-(β * ((d : ℝ) * R ^ 2)))) (τ := pcnGaussLike (d := d) β) (x := x)
    hF one_pos (Real.exp_pos _).le ?_ (fun y _ => pcnGaussLike_mul_pcnPrior_le_one hs hρ hβ y)
    (pcnGaussLike_pos β x) ?_ hdens
  · refine Real.exp_le_one_iff.mpr ?_
    have h : 0 ≤ β * ((d : ℝ) * R ^ 2) := mul_nonneg hβ (by positivity)
    linarith
  · intro y hy
    have h1 := pcnGaussLike_floor (d := d) hβ hy
    have h2 := pcnGaussLike_le_one hβ x
    have h0 : 0 ≤ Real.exp (-(β * ((d : ℝ) * R ^ 2))) := (Real.exp_pos _).le
    have hx0 : 0 < pcnGaussLike (d := d) β x := pcnGaussLike_pos β x
    nlinarith [h1, h2, h0, hx0]

/-! ## 19. The reference's mass and its normalisation -/

/-- The reference's total mass: `∫_{box} τ · pcnPrior`. -/
noncomputable def pcnPriorMass (s ρ R : ℝ) (τ : (Fin d → ℝ) → ℝ) : ENNReal :=
  pcnPriorTarget (d := d) s ρ R τ Set.univ

theorem pcnPriorMass_eq_lintegral {s ρ R : ℝ} {τ : (Fin d → ℝ) → ℝ} :
    pcnPriorMass s ρ R τ
      = ∫⁻ y in pcnBox d R, ENNReal.ofReal (τ y * pcnPrior s ρ y) ∂volume := by
  rw [pcnPriorMass, pcnPriorTarget, pcnTargetMeasure, withDensity_apply _ MeasurableSet.univ,
    setLIntegral_univ]

theorem pcnPriorMass_le {s ρ R B : ℝ} {τ : (Fin d → ℝ) → ℝ}
    (hB' : ∀ y ∈ pcnBox d R, τ y * pcnPrior s ρ y ≤ B) :
    pcnPriorMass s ρ R τ ≤ ENNReal.ofReal B * ENNReal.ofReal (2 * R) ^ d := by
  have h := (Measure.le_iff.mp (pcnTargetMeasure_le_smul (d := d) (R := R) (B := B) hB'))
    Set.univ MeasurableSet.univ
  simpa [pcnPriorMass, pcnPriorTarget, Measure.smul_apply, smul_eq_mul, pcnBox_volume,
    Measure.restrict_apply] using h

theorem pcnPriorMass_ne_top {s ρ R B : ℝ} {τ : (Fin d → ℝ) → ℝ}
    (hB' : ∀ y ∈ pcnBox d R, τ y * pcnPrior s ρ y ≤ B) :
    pcnPriorMass s ρ R τ ≠ ⊤ := by
  have h := pcnPriorMass_le (d := d) hB'
  exact ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
    (ENNReal.pow_ne_top ENNReal.ofReal_ne_top)) h

theorem pcnPriorMass_pos {s ρ R m : ℝ} {τ : (Fin d → ℝ) → ℝ} (hm : 0 < m) (hR : 0 < R)
    (hfloor : ∀ y ∈ pcnBox d R, m ≤ τ y * pcnPrior s ρ y) :
    0 < pcnPriorMass s ρ R τ := by
  have h1 : ENNReal.ofReal (m * (2 * R) ^ d) ≤ pcnPriorTarget (d := d) s ρ R τ (pcnBox d R) :=
    withDensity_box_ge (d := d) hm.le hR.le hfloor
  have h2 : pcnPriorTarget (d := d) s ρ R τ (pcnBox d R) ≤ pcnPriorMass s ρ R τ :=
    measure_mono (Set.subset_univ _)
  exact lt_of_lt_of_le
    (ENNReal.ofReal_pos.mpr (mul_pos hm (pow_pos (by linarith) d))) (le_trans h1 h2)

/-- **The reference, normalised to a probability**: `(τ · pcnPrior)`'s mass divided out. -/
noncomputable def pcnPriorProb (s ρ R : ℝ) (τ : (Fin d → ℝ) → ℝ) : Measure (Fin d → ℝ) :=
  (pcnPriorMass s ρ R τ)⁻¹ • pcnPriorTarget (d := d) s ρ R τ

theorem pcnPriorProb_univ {s ρ R : ℝ} {τ : (Fin d → ℝ) → ℝ}
    (h0 : pcnPriorMass s ρ R τ ≠ 0) (htop : pcnPriorMass s ρ R τ ≠ ⊤) :
    pcnPriorProb s ρ R τ Set.univ = 1 := by
  rw [pcnPriorProb, Measure.smul_apply, smul_eq_mul]
  exact ENNReal.inv_mul_cancel h0 htop

theorem isProbabilityMeasure_pcnPriorProb {s ρ R : ℝ} {τ : (Fin d → ℝ) → ℝ}
    (h0 : pcnPriorMass s ρ R τ ≠ 0) (htop : pcnPriorMass s ρ R τ ≠ ⊤) :
    IsProbabilityMeasure (pcnPriorProb s ρ R τ) :=
  ⟨pcnPriorProb_univ h0 htop⟩

theorem pcnPriorProb_stationary (s ρ R : ℝ) {τ : (Fin d → ℝ) → ℝ} (hs : 0 < s)
    (hτ : Measurable τ) (hτpos : ∀ x, 0 < τ x) :
    (pcnPriorProb s ρ R τ).bind (pcnAbsorbingStep (d := d) s ρ R τ) = pcnPriorProb s ρ R τ := by
  rw [pcnPriorProb, Measure.bind_smul, pcnPriorTarget_stationary s ρ R hs hτ hτpos]

/-- **The split, for a reference of finite mass `M`.** -/
theorem exists_split_of_minorant_mass {α : Type*} [MeasurableSpace α] {μ σ : Measure α}
    [IsProbabilityMeasure σ] {c M : ℝ} (hM : μ Set.univ = ENNReal.ofReal M)
    (hc0 : 0 < c) (hM0 : 0 < M) (hcM : c * M < 1) (h : ENNReal.ofReal c • μ ≤ σ) :
    ∃ ν : Measure α, σ = ENNReal.ofReal c • μ + ENNReal.ofReal (1 - c * M) • ν ∧
      ν Set.univ = 1 := by
  haveI : IsFiniteMeasure (ENNReal.ofReal c • μ) :=
    ⟨by rw [Measure.smul_apply, smul_eq_mul, hM]
        exact ENNReal.mul_lt_top ENNReal.ofReal_ne_top.lt_top ENNReal.ofReal_ne_top.lt_top⟩
  set a : ENNReal := ENNReal.ofReal (1 - c * M) with ha
  have hsub : (1 : ENNReal) - ENNReal.ofReal c * ENNReal.ofReal M = a := by
    rw [ha, ← ENNReal.ofReal_mul hc0.le, ← ENNReal.ofReal_one,
      ← ENNReal.ofReal_sub 1 (mul_pos hc0 hM0).le]
  have hne : a ≠ 0 := (ENNReal.ofReal_pos.mpr (by linarith)).ne'
  have htop : a ≠ ⊤ := ENNReal.ofReal_ne_top
  set r : Measure α := σ - ENNReal.ofReal c • μ with hr
  have hmassr : r Set.univ = a := by
    rw [hr, Measure.sub_apply MeasurableSet.univ h, Measure.smul_apply, smul_eq_mul,
      measure_univ, hM, hsub]
  have hsum : r + ENNReal.ofReal c • μ = σ := by
    rw [hr]
    exact Measure.sub_add_cancel_of_le h
  refine ⟨a⁻¹ • r, ?_, ?_⟩
  · have hsmul : a • (a⁻¹ • r) = r := by
      rw [smul_smul, ENNReal.mul_inv_cancel hne htop, one_smul]
    calc σ = r + ENNReal.ofReal c • μ := hsum.symm
      _ = ENNReal.ofReal c • μ + a • (a⁻¹ • r) := by rw [hsmul, add_comm]
  · rw [Measure.smul_apply, smul_eq_mul, hmassr]
    exact ENNReal.inv_mul_cancel hne htop

/-- **The mass, not a probability: the minorant transfers.**  A minorant against the reference
`τ · pcnPrior` with constant `c0` is a minorant against the normalised `pcnPriorProb` with constant
`c0 · M`, since `pcnPriorProb = M⁻¹ • pcnPriorTarget`. -/
theorem pcnPriorProb_minorant_of_target {s ρ R M : ℝ} {τ : (Fin d → ℝ) → ℝ}
    (hM : pcnPriorMass s ρ R τ = ENNReal.ofReal M) (hM0 : 0 < M)
    {K : (Fin d → ℝ) → Measure (Fin d → ℝ)} {c0 : ℝ}
    (hmin : ∀ x, ENNReal.ofReal c0 • pcnPriorTarget (d := d) s ρ R τ ≤ K x) :
    ∀ x, ENNReal.ofReal (c0 * M) • pcnPriorProb s ρ R τ ≤ K x := by
  have hMne : M ≠ 0 := hM0.ne'
  have hscal : ENNReal.ofReal (c0 * M) * ENNReal.ofReal M⁻¹ = ENNReal.ofReal c0 := by
    rcases le_total 0 c0 with hc0' | hc0'
    · rw [← ENNReal.ofReal_mul (mul_nonneg hc0' hM0.le)]
      congr 1
      field_simp
    · rw [ENNReal.ofReal_eq_zero.mpr (by nlinarith : c0 * M ≤ 0),
        ENNReal.ofReal_eq_zero.mpr hc0', zero_mul]
  intro x
  have h : ENNReal.ofReal (c0 * M) • pcnPriorProb s ρ R τ
      = ENNReal.ofReal c0 • pcnPriorTarget (d := d) s ρ R τ := by
    unfold pcnPriorProb
    rw [smul_smul, hM, ← ENNReal.ofReal_inv_of_pos hM0, hscal]
  rw [h]
  exact hmin x

/-- **The rate against the normalised reference, `IsProbabilityMeasure` proved not assumed.** -/
theorem pcnAbsorbingStep_rate_prob (s ρ R c : ℝ) {τ : (Fin d → ℝ) → ℝ} {M : ℝ}
    (hc0 : 0 < c) (hc1 : c < 1) (hs : 0 < s) (hτ : Measurable τ)
    (hτpos : ∀ x, 0 < τ x) (hM0 : 0 < M)
    (hM : pcnPriorMass s ρ R τ = ENNReal.ofReal M)
    (hmin : ∀ x, ENNReal.ofReal c • pcnPriorProb s ρ R τ
      ≤ pcnAbsorbingStep (d := d) s ρ R τ x)
    (n : ℕ) (x : Fin d → ℝ) {S : Set (Fin d → ℝ)} (hS : MeasurableSet S) :
    ENNReal.ofReal (1 - (1 - c) ^ n) * pcnPriorProb s ρ R τ S
      ≤ pcnIter (pcnAbsorbingStep (d := d) s ρ R τ) n x S := by
  have h0 : pcnPriorMass s ρ R τ ≠ 0 := by
    rw [hM]
    exact (ENNReal.ofReal_pos.mpr hM0).ne'
  have htop : pcnPriorMass s ρ R τ ≠ ⊤ := by
    rw [hM]
    exact ENNReal.ofReal_ne_top
  haveI := isProbabilityMeasure_pcnPriorProb (s := s) (ρ := ρ) (R := R) (τ := τ) h0 htop
  exact pcnAbsorbingStep_rate hc0 hc1 hs hτ hmin
    (fun n => pcnStat_iter (measurable_pcnAbsorbingStep s ρ R hτ)
      (pcnPriorProb_stationary s ρ R hs hτ hτpos) n) n x hS

/-- The Gaussian likelihood's reference is finite: `≤ (2R)^d`, from the ceiling `B = 1`. -/
theorem pcnPriorMass_gaussLike_le {s ρ R β : ℝ} (hs : 0 < s) (hρ : ρ ^ 2 ≤ 1) (hβ : 0 ≤ β) :
    pcnPriorMass s ρ R (pcnGaussLike (d := d) β) ≤ ENNReal.ofReal (2 * R) ^ d := by
  have h : pcnPriorMass s ρ R (pcnGaussLike (d := d) β)
      ≤ ENNReal.ofReal 1 * ENNReal.ofReal (2 * R) ^ d :=
    pcnPriorMass_le (d := d) (R := R) (B := 1) (τ := pcnGaussLike (d := d) β)
      (fun y _ => pcnGaussLike_mul_pcnPrior_le_one hs hρ hβ y)
  simpa using h

/-- The Gaussian likelihood's reference is positive on a nondegenerate box. -/
theorem pcnPriorMass_gaussLike_pos {s ρ R β : ℝ} (hs : 0 < s) (hρ : ρ ^ 2 ≤ 1) (hβ : 0 ≤ β)
    (hR : 0 < R) : 0 < pcnPriorMass s ρ R (pcnGaussLike (d := d) β) := by
  have hm0 : 0 < Real.exp (-(β * ((d : ℝ) * R ^ 2)))
      * Real.exp (-((1 - ρ ^ 2) * ((d : ℝ) * R ^ 2)) / s) :=
    mul_pos (Real.exp_pos _) (Real.exp_pos _)
  refine pcnPriorMass_pos hm0 hR (τ := pcnGaussLike (d := d) β) ?_
  intro y hy
  exact mul_le_mul (pcnGaussLike_floor (d := d) hβ hy) (pcnPrior_floor hs hρ hy)
    (Real.exp_pos _).le (le_trans (Real.exp_pos _).le (pcnGaussLike_floor (d := d) hβ hy))


/-! ## 20. One number at every start — and where that is impossible

§15's return constant is uniform on a *ball* of starts, `pcnBallConst s ρ R M` for `‖x‖² ≤ M²`.
This section asks for a number valid at *every* start, and answers in two directions.

* **`pcnBallConst_antitone`**, **`pcnBallConst_tendsto_zero`**,
  **`pcnBallConst_no_uniform_floor`** — for `ρ ≠ 0` the ball constant has no positive lower bound
  in `M`: it tends to `0`, so *no* start-uniform number comes out of this estimate.  This is not an
  artefact of the proof — a proposal from a far start puts exponentially little mass in the box;
* `pcnQuad_zero_left`, `pcnDensity_zero_left`, `pcnReturnConst_zero`, `pcnBallConst_zero_rho` —
  at `ρ = 0` the proposal forgets the start, so all of these collapse to one number;
* **`pcnAbsorbingStep_box_ge_uniform`** — the return mass is then start-independent;
* **`pcnAbsorbingStep_twoStep_minorant_uniform`** — and §12's two-step minorant holds at a single
  constant, for every start, with no ball hypothesis: the only input about `x` left is the density
  floor, which at `ρ = 0` is a statement about the box alone.

So the request "one number valid at every start" has a true form exactly at `ρ = 0` (an
independent-proposal step, whose chain is i.i.d.), and is false for `ρ ≠ 0`.
-/

/-- At `ρ = 0` the increment does not read the starting point. -/
theorem pcnQuad_zero_left (x y : Fin d → ℝ) : pcnQuad (d := d) 0 x y = pcnSumSq y := by
  simp [pcnQuad, pcnSumSq]

theorem pcnDensity_zero_left {c s : ℝ} (x y : Fin d → ℝ) :
    pcnDensity (d := d) c s 0 x y = c * Real.exp (-(pcnSumSq y) / s) := by
  rw [pcnDensity, pcnQuad_zero_left]

/-- The return constant at `ρ = 0`: one number, with no start in it. -/
theorem pcnReturnConst_zero {s R : ℝ} (x : Fin d → ℝ) :
    pcnReturnConst (d := d) s 0 R x
      = pcnNorm1 s ^ d * Real.exp (-(2 * (d : ℝ) * R ^ 2) / s) := by
  simp only [pcnReturnConst]
  norm_num

theorem pcnBallConst_zero_rho {s R M : ℝ} :
    pcnBallConst (d := d) s 0 R M
      = pcnNorm1 s ^ d * Real.exp (-(2 * (d : ℝ) * R ^ 2) / s) := by
  simp only [pcnBallConst]
  norm_num

/-- The acceptance floor `exp (−β dR²)` never exceeds `1`. -/
theorem pcnGaussLike_floor_le_one {β R : ℝ} (hβ : 0 ≤ β) :
    Real.exp (-(β * ((d : ℝ) * R ^ 2))) ≤ 1 :=
  Real.exp_le_one_iff.mpr (by
    have h : 0 ≤ β * ((d : ℝ) * R ^ 2) :=
      mul_nonneg hβ (mul_nonneg (Nat.cast_nonneg (α := ℝ) d) (sq_nonneg R))
    linarith)

/-- **The return mass, one number at every start.**  For `ρ = 0` the proposal forgets the starting
point, so §13's return estimate is the same number everywhere — no ball, no `M`. -/
theorem pcnAbsorbingStep_box_ge_uniform {s R β : ℝ} (hs : 0 < s) (hR : 0 ≤ R) (hβ : 0 ≤ β)
    (x : Fin d → ℝ) :
    ENNReal.ofReal (Real.exp (-(β * ((d : ℝ) * R ^ 2)))
        * (pcnNorm1 s ^ d * Real.exp (-(2 * (d : ℝ) * R ^ 2) / s)) * (2 * R) ^ d)
      ≤ pcnAbsorbingStep (d := d) s 0 R (pcnGaussLike (d := d) β) x (pcnBox d R) := by
  have h := pcnAbsorbingStep_box_ge_start (d := d) (s := s) (ρ := 0) (R := R) (B := 1)
    (m := Real.exp (-(β * ((d : ℝ) * R ^ 2)))) (τ := pcnGaussLike (d := d) β) (x := x)
    hs hR (Real.exp_pos _).le (pcnGaussLike_floor_le_one (d := d) hβ) (pcnGaussLike_pos β x)
    (pcnGaussLike_le_one hβ x) (fun y hy => by
      rw [mul_one]
      exact pcnGaussLike_floor (d := d) hβ hy)
  rwa [pcnReturnConst_zero] at h

/-- **Two steps at a single constant, for every start** (`ρ = 0`, Gaussian likelihood).  The ball
hypothesis `pcnSumSq x ≤ M²` of `pcnAbsorbingStep_twoStep_minorant_ball` is gone: the constant is
`m · (pcnNorm1 s^d · exp (−2dR²/s)) · (2R)^d · (mF/B)` with `m = exp (−β dR²)`, `B = 1`. -/
theorem pcnAbsorbingStep_twoStep_minorant_uniform {s R F β : ℝ} (hs : 0 < s) (hR : 0 ≤ R)
    (hβ : 0 ≤ β) (hF : 0 ≤ F)
    (hdens : ∀ z ∈ pcnBox d R, F ≤ pcnDensity (pcnNorm1 s ^ d) s 0 0 z) :
    ∀ x : Fin d → ℝ,
      (ENNReal.ofReal (Real.exp (-(β * ((d : ℝ) * R ^ 2)))
          * (pcnNorm1 s ^ d * Real.exp (-(2 * (d : ℝ) * R ^ 2) / s)) * (2 * R) ^ d)
        * ENNReal.ofReal (Real.exp (-(β * ((d : ℝ) * R ^ 2))) * F / 1))
        • pcnTargetMeasure (d := d) R (pcnGaussLike (d := d) β)
      ≤ (pcnAbsorbingStep (d := d) s 0 R (pcnGaussLike (d := d) β) x).bind
          (pcnAbsorbingStep (d := d) s 0 R (pcnGaussLike (d := d) β)) := by
  intro x
  have hm : Real.exp (-(β * ((d : ℝ) * R ^ 2))) ≤ 1 := pcnGaussLike_floor_le_one (d := d) hβ
  refine bind_minorant_of_set (measurableSet_pcnBox (d := d) R)
    (measurable_pcnAbsorbingStep s 0 R (pcnGaussLike_measurable β)).aemeasurable
    (pcnAbsorbingStep_box_ge_uniform (d := d) hs hR hβ x) (fun y hy => ?_)
  exact pcnAbsorbingStep_minorant hF one_pos (Real.exp_pos _).le hm
    (fun z _ => pcnGaussLike_le_one hβ z) (pcnGaussLike_pos β y)
    (fun z hz => by
      have h1 := pcnGaussLike_floor (d := d) hβ hz
      have h2 := pcnGaussLike_le_one hβ y
      have h0 : 0 ≤ Real.exp (-(β * ((d : ℝ) * R ^ 2))) := (Real.exp_pos _).le
      have hy0 : 0 < pcnGaussLike (d := d) β y := pcnGaussLike_pos β y
      nlinarith [h1, h2, h0, hy0])
    (fun z hz => by simpa [pcnDensity_zero_left] using hdens z hz)

/-- The ball constant is decreasing in the radius. -/
theorem pcnBallConst_antitone {s ρ R : ℝ} (hs : 0 < s) {M₁ M₂ : ℝ} (h0 : 0 ≤ M₁)
    (h12 : M₁ ≤ M₂) :
    pcnBallConst (d := d) s ρ R M₂ ≤ pcnBallConst (d := d) s ρ R M₁ := by
  refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_)
    (pow_nonneg (pcnNorm1_pos hs).le d)
  have hsq : M₁ ^ 2 ≤ M₂ ^ 2 := by nlinarith
  have hmono : 2 * ρ ^ 2 * M₁ ^ 2 ≤ 2 * ρ ^ 2 * M₂ ^ 2 :=
    mul_le_mul_of_nonneg_left hsq (by positivity)
  rw [neg_div, neg_div, neg_le_neg_iff]
  exact div_le_div_of_nonneg_right (by linarith) hs.le

/-- **The ball constant decays**: for `ρ ≠ 0` it tends to `0` as the ball grows. -/
theorem pcnBallConst_tendsto_zero {s ρ R : ℝ} (hs : 0 < s) (hρ : ρ ≠ 0) :
    Tendsto (fun M : ℝ => pcnBallConst (d := d) s ρ R M) atTop (𝓝 0) := by
  have hpos : (0 : ℝ) < 2 * ρ ^ 2 := by
    have h2 : 0 < ρ ^ 2 := pow_two_pos_of_ne_zero hρ
    linarith
  have hc0 : 0 ≤ 2 * (d : ℝ) * R ^ 2 := by positivity
  have h2 : Tendsto (fun M : ℝ => 2 * ρ ^ 2 * M ^ 2) atTop atTop :=
    tendsto_const_mul_pow_atTop (by norm_num) hpos
  have hpoly : Tendsto (fun M : ℝ => 2 * ρ ^ 2 * M ^ 2 + 2 * (d : ℝ) * R ^ 2)
      atTop atTop :=
    tendsto_atTop_mono' _ (Eventually.of_forall fun M => le_add_of_nonneg_right hc0) h2
  have hexp : Tendsto (fun M : ℝ =>
      Real.exp (-((2 * ρ ^ 2 * M ^ 2 + 2 * (d : ℝ) * R ^ 2) / s))) atTop (𝓝 0) :=
    Real.tendsto_exp_neg_atTop_nhds_zero.comp (hpoly.atTop_div_const hs)
  have hmul := (tendsto_const_nhds (x := pcnNorm1 s ^ d)).mul hexp
  have hfun : (fun M : ℝ => pcnBallConst (d := d) s ρ R M)
      = fun M : ℝ => pcnNorm1 s ^ d
          * Real.exp (-((2 * ρ ^ 2 * M ^ 2 + 2 * (d : ℝ) * R ^ 2) / s)) := by
    funext M
    simp only [pcnBallConst, neg_div]
  rw [hfun]
  simpa [mul_zero] using hmul

/-- **No ball-free constant, for `ρ ≠ 0`**: every positive `c` is beaten by the ball constant at a
large enough radius, so §15's estimate cannot be made start-uniform. -/
theorem pcnBallConst_no_uniform_floor {s ρ R : ℝ} (hs : 0 < s) (hρ : ρ ≠ 0) {c : ℝ}
    (hc : 0 < c) : ∃ M : ℝ, pcnBallConst (d := d) s ρ R M < c :=
  ((pcnBallConst_tendsto_zero (d := d) hs hρ).eventually (gt_mem_nhds hc)).exists


/-! ## 21. The reference's mass in closed form

§19 named `pcnPriorMass s ρ R τ = ∫_{box} τ · pcnPrior` and bounded it by `(2R)^d`; it did not
compute it.  For §18's Gaussian likelihood the product is again a Gaussian —
`τ · pcnPrior = exp (−κ‖y‖²)` with `κ = β + (1 − ρ²)/s` — so the box integral factorises and is the
`d`-th power of a one-dimensional interval integral.

* **`gaussLike_mul_prior_eq_prod`** — the product is `∏ᵢ exp (−κ yᵢ²)`;
* `box_indicator_prod`, `box_integral_prod` — Fubini over the box: the `d`-dimensional integral is
  `(∫_{−R}^{R} exp (−κt²) dt)^d`;
* **`pcnPriorMass_gaussLike_eq`** — the closed form
  `M = (∫_{−R}^{R} exp (−κt²) dt)^d`, with `κ = β + (1 − ρ²)/s`;
* `boxInt_nonneg`, **`boxInt_le_sqrt`** — the one-dimensional factor is nonnegative and at most
  `√(π/κ)`, its value on all of `ℝ`;
* **`pcnPriorMass_gaussLike_le_sqrt`** — hence `M ≤ (√(π/κ))^d`, the Gaussian ceiling that pairs
  with §19's `M ≤ (2R)^d`.

Mathlib has no Gauss error function, so the one-dimensional factor is kept as the interval integral
rather than evaluated in elementary terms; the reduction to `d = 1` is the content, and both
closed-form bounds on it are given.
-/

/-- **The Gaussian likelihood times the prior is one Gaussian**: `exp (−κ‖y‖²)` with
`κ = β + (1 − ρ²)/s`. -/
theorem gaussLike_mul_prior_eq_prod {s ρ β : ℝ} (hs : 0 < s) (y : Fin d → ℝ) :
    pcnGaussLike (d := d) β y * pcnPrior (d := d) s ρ y
      = ∏ i, Real.exp (-((β + (1 - ρ ^ 2) / s) * (y i) ^ 2)) := by
  rw [pcnGaussLike, pcnPrior, ← Real.exp_add, ← Real.exp_sum]
  congr 1
  rw [pcnSumSq, Finset.mul_sum, Finset.mul_sum, ← Finset.sum_neg_distrib,
    ← Finset.sum_neg_distrib, Finset.sum_div, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  field_simp
  ring

/-- The box's indicator of a coordinate product is the product of the coordinate intervals'
indicators. -/
theorem box_indicator_prod {R : ℝ} (g : ℝ → ℝ) (y : Fin d → ℝ) :
    (pcnBox d R).indicator (fun y => ∏ i, g (y i)) y
      = ∏ i, (Set.Icc (-R) R).indicator g (y i) := by
  by_cases h : y ∈ pcnBox d R
  · rw [Set.indicator_of_mem h]
    refine Finset.prod_congr rfl fun i _ => ?_
    exact (Set.indicator_of_mem (Set.mem_Icc.mpr (abs_le.mp ((mem_pcnBox.mp h) i))) g).symm
  · rw [Set.indicator_of_notMem h]
    have hex : ∃ j, y j ∉ Set.Icc (-R) R := by
      by_contra hcon
      push_neg at hcon
      exact h (mem_pcnBox.mpr fun i => abs_le.mpr (Set.mem_Icc.mp (hcon i)))
    obtain ⟨j, hj⟩ := hex
    exact (Finset.prod_eq_zero (Finset.mem_univ j) (Set.indicator_of_notMem hj g)).symm

/-- **Fubini over the box**: the product density's integral is the `d`-th power of the
one-dimensional one. -/
theorem box_integral_prod {R κ : ℝ} :
    ∫ y in pcnBox d R, (∏ i, Real.exp (-(κ * (y i) ^ 2)))
      = (∫ t in Set.Icc (-R) R, Real.exp (-(κ * t ^ 2))) ^ d := by
  rw [← integral_indicator (measurableSet_pcnBox (d := d) R)]
  rw [show (fun y : Fin d → ℝ => (pcnBox d R).indicator
        (fun y => ∏ i, Real.exp (-(κ * (y i) ^ 2))) y)
      = fun y : Fin d → ℝ => ∏ i, (Set.Icc (-R) R).indicator
          (fun t => Real.exp (-(κ * t ^ 2))) (y i) from
    funext fun y => box_indicator_prod (fun t => Real.exp (-(κ * t ^ 2))) y]
  rw [integral_fintype_prod_volume_eq_pow, integral_indicator measurableSet_Icc]
  simp

/-- **The reference's mass, in closed form** for a Gaussian likelihood:
`M = (∫_{−R}^{R} exp (−κt²) dt)^d`, `κ = β + (1 − ρ²)/s`. -/
theorem pcnPriorMass_gaussLike_eq {s ρ R β : ℝ} (hs : 0 < s)
    (hκ : 0 < β + (1 - ρ ^ 2) / s) :
    pcnPriorMass s ρ R (pcnGaussLike (d := d) β)
      = ENNReal.ofReal
          ((∫ t in Set.Icc (-R) R, Real.exp (-((β + (1 - ρ ^ 2) / s) * t ^ 2))) ^ d) := by
  rw [pcnPriorMass_eq_lintegral]
  have hcongr : (∫⁻ y in pcnBox d R,
        ENNReal.ofReal (pcnGaussLike (d := d) β y * pcnPrior (d := d) s ρ y) ∂volume)
      = ∫⁻ y in pcnBox d R,
          ENNReal.ofReal (∏ i, Real.exp (-((β + (1 - ρ ^ 2) / s) * (y i) ^ 2))) ∂volume :=
    setLIntegral_congr_fun (measurableSet_pcnBox (d := d) R)
      (fun y _ => by rw [gaussLike_mul_prior_eq_prod hs y])
  rw [hcongr]
  have hint : Integrable (fun y : Fin d → ℝ =>
      ∏ i, Real.exp (-((β + (1 - ρ ^ 2) / s) * (y i) ^ 2))) := by
    have h := Integrable.fintype_prod (ι := Fin d) (E := ℝ) (𝕜 := ℝ)
      (μ := fun _ => (volume : Measure ℝ))
      (f := fun _ t => Real.exp (-((β + (1 - ρ ^ 2) / s) * t ^ 2)))
      (fun _ => (integrable_exp_neg_mul_sq (b := β + (1 - ρ ^ 2) / s) hκ).congr
        (Eventually.of_forall fun t => by simp only [neg_mul]))
    simpa using h
  have hnn : 0 ≤ᵐ[volume.restrict (pcnBox d R)] (fun y : Fin d → ℝ =>
      ∏ i, Real.exp (-((β + (1 - ρ ^ 2) / s) * (y i) ^ 2))) :=
    Filter.Eventually.of_forall fun _ => Finset.prod_nonneg fun i _ => (Real.exp_pos _).le
  rw [← MeasureTheory.ofReal_integral_eq_lintegral_ofReal hint.restrict hnn]
  rw [box_integral_prod]

theorem boxInt_nonneg {R κ : ℝ} :
    0 ≤ ∫ t in Set.Icc (-R) R, Real.exp (-(κ * t ^ 2)) :=
  integral_nonneg fun _ => (Real.exp_pos _).le

/-- The one-dimensional factor is at most its value on all of `ℝ`, `√(π/κ)`. -/
theorem boxInt_le_sqrt {R κ : ℝ} (hκ : 0 < κ) :
    ∫ t in Set.Icc (-R) R, Real.exp (-(κ * t ^ 2)) ≤ Real.sqrt (Real.pi / κ) := by
  have hint : Integrable fun t : ℝ => Real.exp (-(κ * t ^ 2)) := by
    simpa using integrable_exp_neg_mul_sq hκ
  calc ∫ t in Set.Icc (-R) R, Real.exp (-(κ * t ^ 2))
      ≤ ∫ t : ℝ, Real.exp (-(κ * t ^ 2)) :=
        setIntegral_le_integral hint (Filter.Eventually.of_forall fun _ => (Real.exp_pos _).le)
    _ = Real.sqrt (Real.pi / κ) := by simpa using integral_gaussian κ

/-- **The mass ceiling from the Gaussian**: `M ≤ (√(π/κ))^d`, pairing with §19's `M ≤ (2R)^d`. -/
theorem pcnPriorMass_gaussLike_le_sqrt {s ρ R β : ℝ} (hs : 0 < s)
    (hκ : 0 < β + (1 - ρ ^ 2) / s) :
    pcnPriorMass s ρ R (pcnGaussLike (d := d) β)
      ≤ ENNReal.ofReal ((Real.sqrt (Real.pi / (β + (1 - ρ ^ 2) / s))) ^ d) := by
  rw [pcnPriorMass_gaussLike_eq hs hκ]
  refine ENNReal.ofReal_le_ofReal
    (pow_le_pow_left₀ (boxInt_nonneg (κ := β + (1 - ρ ^ 2) / s)) (boxInt_le_sqrt hκ) d)


end PCN

end BookProof.MCMC.PCNGaussianFloor
