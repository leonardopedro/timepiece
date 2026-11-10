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
  **`pcnExp_factor`** (`exp (−pcnQuad/s)` as the product of its coordinate factors).

## Honest boundary

This is a *density* floor and the measure inequality it implies on a box — not a full Doeblin
theorem on the continuum.  §22–§26's machinery is stated on a finite state space, and the weight
space is not one.  What §2 adds is that the floor is a statement about the *proposal measure* on
`ℝ^d`, uniformly in the starting point, which is the form a minorant consumes; what it does not do
is name the target measure on `ℝ^d`, pass the Metropolis filter through the density, or produce a
rate — §3–§5 do all three, and the rate is the classical `1 − (1 − c)^n` — but the step family
the rate applies to must be a family of probability measures — §6 builds that family (accepted
density plus rejection atom) and proves its mass is `1`.  What stays open is the *value* of the
accepted mass: an integral of §4's density that the chapter does not compute.  Proving the
invariance hypothesis rather than stating it is the other open link.
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


end BookProof.MCMC.PCNGaussianFloor
