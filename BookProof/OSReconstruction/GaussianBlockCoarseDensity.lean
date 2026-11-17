import Mathlib

/-!
# The coarse density of a Gaussian block step, iterated twice

Plan: `cftproof.md`, **C3a** — the exact coarse-graining step.  The plan states a
requirement that is easy to get wrong in prose and worth pinning down as a theorem:

> For a reference Gaussian `gamma` and coarse sigma-field `G`, the coarse density is
> `E_gamma[|Psi|² | G]`, not `|E_gamma[Psi | G]|²`.

This module makes that statement exact on the smallest nontrivial system: the reference
law is two independent unit Gaussians, the first coordinate is the *block* variable and the
second the *exterior* variable.  Coarse graining integrates out the block variable only,
so the coarse density of `f` is the partial integral

`blockIntegral f y = ∫ x, f (x, y) ∂gamma`

over the block coordinate at fixed exterior field `y`.

The second half of the module iterates the step: a second block coordinate (the *shell*) is
integrated out after the first, so the map becomes `∫ z, ∫ x, f (x, z, y)`.  That makes the
composition, its tower identity and the small-field covariance bound of plan packet **C3b**
statements about the same reference system rather than a new construction.

## Contents

* `blockUnit`, `blockLaw` — the one-coordinate law and the two-coordinate reference law;
* `blockIntegral`, `integral_blockIntegral` — the partial integral and the **tower identity**
  `∫ f d gamma = ∫ (blockIntegral f) d gamma_ext`;
* `blockIntegral_const`, `blockIntegral_add`, `blockIntegral_nonneg`, `blockIntegral_exterior`
  — the block step is a positive linear map normalised at `1` that fixes the exterior fields;
* `blockIntegral_mul_exterior` — `blockIntegral f` is *characterised* as the conditional
  expectation: pairing it against any exterior test function reproduces the joint integral;
* `blockField`, `blockIntegral_blockField`, `blockIntegral_blockField_sq` — for the cylinder
  observable `Psi_c (x, y) = x + c y`, the conditional mean is `c y` and the coarse density of
  `|Psi_c|²` is `1 + c² y²`;
* `coarseDensity`, `naiveDensity`, `coarseDensity_eq_naiveDensity_add`,
  `coarseDensity_ne_naiveDensity` — **the coarse density differs from the squared conditional
  mean, by exactly the conditional variance**;
* `integral_naiveDensity`, `integral_coarseDensity_eq_integral_blockField_sq` — the totals: the
  coarse density reproduces the mean of `|Psi|²`, the squared conditional mean does not;
* `variance_decomposition` — the full second moment is the covariance of the conditional means
  plus the mean conditional variance, which is the form in which the plan asks for conditional
  means and their covariances to be preserved.
* `blockChainLaw`, `blockStep`, `blockChainDensity`, `integral_blockChainDensity` — the **chain**:
  the block step is iterated twice, the second step being `blockIntegral` applied to the first,
  and the composed map is again a positive unital map fixing the exterior field, with its own
  tower identity;
* `blockChainField`, `blockStep_blockChainField`, `blockChainDensity_blockChainField` — the
  cylinder field on three coordinates: the conditional mean after two steps is the exterior part
  alone, so the interior coupling is irrelevant at the coarse scale and the background is stable;
* `blockChainDensity_blockChainField_sq`, `blockChainCovariance_eq`,
  `blockChainCovariance_small_field` — the **C3b small-field packet**: the covariance accumulated
  over the two steps is `1 + c²`, independent of the exterior background `y` and of the exterior
  coupling `d`, and bounded by `2` for `|c| ≤ 1`;
* `blockActivityNorm`, `integral_abs_blockIntegral_le`, `integral_abs_blockChainDensity_le` — the
  activity norm `∫ |f|` is contracted by a coarse step, which is the estimate a polymer activity
  needs;
* `integral_blockNaiveChainDensity`, `integral_blockChainDensity_sq`,
  `integral_blockChainDensity_eq_integral_naive_add` — the totals over the exterior field: the
  coarse total is `1 + c² + d²`, the naive one is `d²`, and they differ by exactly the
  accumulated covariance;
* `blockNaiveChainDensity_zero_background`, `blockChainDensity_sq_zero_background`,
  `blockChainCovariance_le_coupling_sq`, `blockChainCovariance_le_mul_density` — the **C3c
  complement** at reference scale: the covariance grows only quadratically in the coupling, the
  naive error is largest at zero background, and where the exterior field dominates the
  covariance is a relative fraction `ε` of the coarse density.

## Boundary

* One block, one shell and one exterior coordinate, real-valued fields, unit Gaussian reference
  law.  No gauge structure, no lattice, no measure-level pushforward and no iteration to
  arbitrarily many scales: the RG action is not represented, only two exact conditional steps of
  a reference Gaussian.  The chain is *not* an RG map — every coordinate is a fresh independent
  Gaussian variable, so nothing is rescaled, translated or renormalised between the steps.
* The C3b packet is small-field content *of this reference system only*: the covariance bound is
  an exact identity with an explicit constant, not an elliptic estimate for an interacting
  measure, and the activity estimate is L¹ contraction, not a polymer expansion with a summable
  activity ledger.  No scale-uniform derivative bound, no background-stability theorem for a
  non-Gaussian law and no running-coupling trajectory is proved here.
* The C3c complement is not a large-field theory: `blockChainCovariance_le_mul_density` says that
  where the background is large the *fixed* covariance is relatively negligible — it does not
  bound a fluctuation covariance, does not control the bad-block region of an interacting
  measure and proves no summable tail.  `blockChainCovariance_le_coupling_sq` bounds the
  covariance by `1 + M²` in the coupling `M`; it is not a large-field expansion.
* `blockIntegral_mul_exterior` is the characterising identity of the conditional expectation
  on cylinder test functions, not a `condExp` construction: no sigma-field is chosen and no
  existence theorem for conditional expectations is used.
* `coarseDensity_ne_naiveDensity` is a statement about one Gaussian system.  It shows the two
  prescriptions genuinely differ and that the error of the naive one is the conditional
  variance; it is not a lower bound for interacting or gauge systems.
-/

namespace BookProof.OSReconstruction

open MeasureTheory ProbabilityTheory

noncomputable section

/-! ## The reference law and the block integral -/

/-- The one-coordinate reference law: a unit Gaussian. -/
def blockUnit : Measure ℝ := gaussianReal 0 1

/-- **The two-coordinate reference law**: the block coordinate and the exterior coordinate are
independent unit Gaussians. -/
def blockLaw : Measure (ℝ × ℝ) := blockUnit.prod blockUnit

instance blockUnit_isProbability : IsProbabilityMeasure blockUnit := by
  unfold blockUnit
  infer_instance

instance blockLaw_isProbability : IsProbabilityMeasure blockLaw := by
  unfold blockLaw
  infer_instance

/-- **The block integral**: integrate the block coordinate out at fixed exterior field `y`.  Its
value at `y` is the coarse density of `f` at `y`. -/
def blockIntegral (f : ℝ × ℝ → ℝ) (y : ℝ) : ℝ := ∫ x, f (x, y) ∂blockUnit

/-- **The tower identity**: integrating the coarse density over the exterior fields reproduces
the joint integral.  This is the exact statement that coarse graining loses nothing for the
partition function, whatever it does to the density itself. -/
theorem integral_blockIntegral (f : ℝ × ℝ → ℝ) (hf : Integrable f blockLaw) :
    ∫ p, f p ∂blockLaw = ∫ y, blockIntegral f y ∂blockUnit := by
  rw [blockLaw, integral_prod_symm f hf]
  rfl

/-! ## The block step as a positive unital linear map -/

/-- Constants are fixed by the block step. -/
theorem blockIntegral_const (c y : ℝ) : blockIntegral (fun _ => c) y = c := by
  unfold blockIntegral
  rw [integral_const]
  simp

/-- The block step is additive on integrable slices. -/
theorem blockIntegral_add (f g : ℝ × ℝ → ℝ) (y : ℝ)
    (hf : Integrable (fun x => f (x, y)) blockUnit)
    (hg : Integrable (fun x => g (x, y)) blockUnit) :
    blockIntegral (f + g) y = blockIntegral f y + blockIntegral g y := by
  have hfun : ∀ x : ℝ, (f + g) (x, y) = f (x, y) + g (x, y) := fun _ => rfl
  unfold blockIntegral
  simp only [hfun]
  exact integral_add hf hg

/-- The block step is positive: a pointwise nonnegative observable has nonnegative coarse
density. -/
theorem blockIntegral_nonneg (f : ℝ × ℝ → ℝ) (y : ℝ) (hf : ∀ p, 0 ≤ f p) :
    0 ≤ blockIntegral f y := by
  unfold blockIntegral
  exact integral_nonneg fun x => hf (x, y)

/-- The block step fixes observables of the exterior field: no exterior field is integrated
out. -/
theorem blockIntegral_exterior (g : ℝ → ℝ) (y : ℝ) :
    blockIntegral (fun p => g p.2) y = g y := by
  unfold blockIntegral
  change ∫ _x : ℝ, g y ∂blockUnit = g y
  rw [integral_const]
  simp

/-- **The characterising identity of the coarse density.**  Pairing `blockIntegral f` against
an exterior test function reproduces the joint integral of `f` times that test function.  This
is what makes `blockIntegral f` the conditional expectation of `f` given the exterior field,
stated without choosing a sigma-field. -/
theorem blockIntegral_mul_exterior (f : ℝ × ℝ → ℝ) (g : ℝ → ℝ)
    (hf : Integrable (fun p => f p * g p.2) blockLaw) :
    ∫ y, blockIntegral f y * g y ∂blockUnit = ∫ p, f p * g p.2 ∂blockLaw := by
  rw [blockLaw, integral_prod_symm (fun p : ℝ × ℝ => f p * g p.2) hf]
  congr 1
  funext y
  show (∫ x : ℝ, f (x, y) ∂blockUnit) * g y = ∫ x : ℝ, f (x, y) * g y ∂blockUnit
  rw [integral_mul_const]

/-! ## One-coordinate moments -/

/-- The mean of the unit Gaussian. -/
theorem integral_id_blockUnit : ∫ x : ℝ, x ∂blockUnit = 0 := by
  unfold blockUnit
  rw [integral_id_gaussianReal]

/-- The second moment of the unit Gaussian. -/
theorem integral_sq_blockUnit : ∫ x : ℝ, x ^ 2 ∂blockUnit = 1 := by
  unfold blockUnit
  have h := variance_eq_sub (μ := gaussianReal 0 1) (X := id) (memLp_id_gaussianReal 2)
  simp only [id_eq, variance_id_gaussianReal, NNReal.coe_one, integral_id_gaussianReal] at h
  simpa using h.symm

/-- The mean of the first (block) coordinate of the reference law. -/
theorem integral_fst_blockLaw : ∫ p : ℝ × ℝ, p.1 ∂blockLaw = 0 := by
  unfold blockLaw
  rw [integral_fun_fst (f := fun x : ℝ => x)]
  simp only [blockUnit, integral_id_gaussianReal, smul_eq_mul, mul_zero]

/-- The second moment of the first (block) coordinate of the reference law. -/
theorem integral_fst_sq_blockLaw : ∫ p : ℝ × ℝ, p.1 ^ 2 ∂blockLaw = 1 := by
  unfold blockLaw
  rw [integral_fun_fst (f := fun x : ℝ => x ^ 2)]
  simp [integral_sq_blockUnit]

/-- The mixed moment of the reference law vanishes: block and exterior are independent. -/
theorem integral_fst_mul_snd_blockLaw : ∫ p : ℝ × ℝ, p.1 * p.2 ∂blockLaw = 0 := by
  unfold blockLaw
  rw [integral_prod_mul (f := fun x : ℝ => x) (g := fun y : ℝ => y)]
  simp [blockUnit, integral_id_gaussianReal]

/-- The second moment of the second (exterior) coordinate of the reference law. -/
theorem integral_snd_sq_blockLaw : ∫ p : ℝ × ℝ, p.2 ^ 2 ∂blockLaw = 1 := by
  unfold blockLaw
  rw [integral_fun_snd (f := fun y : ℝ => y ^ 2)]
  simp [integral_sq_blockUnit]

/-! ## The cylinder observable and its coarse density -/

/-- The cylinder observable `Psi_c (x, y) = x + c y`: a block field linearly coupled to the
exterior field, so that the conditional mean is nonzero. -/
def blockField (c : ℝ) : ℝ × ℝ → ℝ := fun p => p.1 + c * p.2

/-- **The conditional mean** of `Psi_c` is the linear regression `c y` on the exterior field. -/
theorem blockIntegral_blockField (c y : ℝ) :
    blockIntegral (blockField c) y = c * y := by
  have hx : Integrable (fun x : ℝ => x) blockUnit :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable (by norm_num)
  have hc : Integrable (fun _ : ℝ => c * y) blockUnit := integrable_const _
  have hfun : ∀ x : ℝ, blockField c (x, y) = x + c * y := fun _ => rfl
  unfold blockIntegral
  simp only [hfun]
  rw [integral_add hx hc, integral_const]
  simp [blockUnit, integral_id_gaussianReal]

/-- **The coarse density of `|Psi_c|²`** is `1 + c² y²`: the exterior-dependent part `c² y²` plus
the block variance `1`. -/
theorem blockIntegral_blockField_sq (c y : ℝ) :
    blockIntegral (fun p => (blockField c p) ^ 2) y = 1 + c ^ 2 * y ^ 2 := by
  have hx : Integrable (fun x : ℝ => x) blockUnit :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable (by norm_num)
  have hx2 : Integrable (fun x : ℝ => x ^ 2) blockUnit :=
    MemLp.integrable_sq (memLp_id_gaussianReal 2)
  have hlin : Integrable (fun x : ℝ => 2 * (c * y) * x) blockUnit := hx.const_mul _
  have hconst : Integrable (fun _ : ℝ => (c * y) ^ 2) blockUnit := integrable_const _
  have hfun : ∀ x : ℝ, (blockField c (x, y)) ^ 2
      = x ^ 2 + (2 * (c * y) * x + (c * y) ^ 2) := by
    intro x
    unfold blockField
    ring
  have hlin' : ∫ x : ℝ, 2 * (c * y) * x ∂blockUnit = 0 := by
    rw [integral_const_mul, integral_id_blockUnit, mul_zero]
  have hconst' : ∫ _x : ℝ, (c * y) ^ 2 ∂blockUnit = (c * y) ^ 2 := by
    rw [integral_const]
    simp
  unfold blockIntegral
  simp only [hfun]
  rw [integral_add (f := fun x : ℝ => x ^ 2)
      (g := fun x : ℝ => 2 * (c * y) * x + (c * y) ^ 2) hx2 (hlin.add hconst),
    integral_add (f := fun x : ℝ => 2 * (c * y) * x) (g := fun _ : ℝ => (c * y) ^ 2)
      hlin hconst,
    integral_sq_blockUnit, hlin', hconst']
  ring

/-- The **coarse density** of the observable `Psi_c`: the conditional expectation of `|Psi_c|²`. -/
def coarseDensity (c : ℝ) (y : ℝ) : ℝ := blockIntegral (fun p => (blockField c p) ^ 2) y

/-- **The naive density**: the square of the conditional mean of `Psi_c`, which is what one gets
by replacing `E[|Psi|² | G]` with `|E[Psi | G]|²`. -/
def naiveDensity (c : ℝ) (y : ℝ) : ℝ := (blockIntegral (blockField c) y) ^ 2

/-- **The coarse density is the squared conditional mean plus the conditional variance.**  For
the cylinder observable the conditional variance is the block variance `1`, independent of the
exterior field. -/
theorem coarseDensity_eq_naiveDensity_add (c y : ℝ) :
    coarseDensity c y = naiveDensity c y + 1 := by
  unfold coarseDensity naiveDensity
  rw [blockIntegral_blockField_sq, blockIntegral_blockField]
  ring

/-- **The two prescriptions differ.**  At zero exterior field the coarse density is `1` while the
squared conditional mean vanishes, so no hypothesis can make them equal: replacing
`E[|Psi|² | G]` by `|E[Psi | G]|²` is a genuine error, not a convention. -/
theorem coarseDensity_ne_naiveDensity (c : ℝ) :
    coarseDensity c 0 ≠ naiveDensity c 0 := by
  have hnaive : naiveDensity c 0 = 0 := by
    unfold naiveDensity
    rw [blockIntegral_blockField]
    ring
  intro h
  rw [hnaive] at h
  have hcoarse : coarseDensity c 0 = 1 := by
    rw [coarseDensity_eq_naiveDensity_add, hnaive]
    ring
  rw [hcoarse] at h
  norm_num at h

/-! ## Totals: the coarse density reproduces the mean, the naive density does not -/

/-- The mean of `|Psi_c|²` at the reference law. -/
theorem integral_blockField_sq (c : ℝ) :
    ∫ p, (blockField c p) ^ 2 ∂blockLaw = 1 + c ^ 2 := by
  have hX : MemLp (fun p : ℝ × ℝ => p.1) 2 blockLaw :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).comp_fst _
  have hY : MemLp (fun p : ℝ × ℝ => p.2) 2 blockLaw :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).comp_snd _
  have hx2 : Integrable (fun p : ℝ × ℝ => p.1 ^ 2) blockLaw := MemLp.integrable_sq hX
  have hsnd2 : Integrable (fun p : ℝ × ℝ => c ^ 2 * p.2 ^ 2) blockLaw :=
    (MemLp.integrable_sq hY).const_mul _
  have hx : Integrable (fun x : ℝ => x) blockUnit :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable (by norm_num)
  have hmul : Integrable (fun p : ℝ × ℝ => p.1 * p.2) blockLaw :=
    Integrable.mul_prod (f := fun x : ℝ => x) (g := fun y : ℝ => y) hx hx
  have hmix : Integrable (fun p : ℝ × ℝ => 2 * c * (p.1 * p.2)) blockLaw := hmul.const_mul _
  have hfun : ∀ p : ℝ × ℝ, (blockField c p) ^ 2
      = p.1 ^ 2 + (2 * c * (p.1 * p.2) + c ^ 2 * p.2 ^ 2) := by
    intro p
    unfold blockField
    ring
  simp only [hfun]
  rw [integral_add (f := fun p : ℝ × ℝ => p.1 ^ 2)
      (g := fun p : ℝ × ℝ => 2 * c * (p.1 * p.2) + c ^ 2 * p.2 ^ 2) hx2
      (hmix.add hsnd2),
    integral_add (f := fun p : ℝ × ℝ => 2 * c * (p.1 * p.2))
      (g := fun p : ℝ × ℝ => c ^ 2 * p.2 ^ 2) hmix hsnd2,
    integral_const_mul, integral_fst_mul_snd_blockLaw, integral_const_mul,
    integral_fst_sq_blockLaw, integral_snd_sq_blockLaw]
  ring

/-- **The mean of the naive density** is `c²`: the squared conditional mean captures the
exterior-dependent part and nothing else. -/
theorem integral_naiveDensity (c : ℝ) :
    ∫ y, naiveDensity c y ∂blockUnit = c ^ 2 := by
  have h : ∀ y : ℝ, naiveDensity c y = (c * y) ^ 2 := by
    intro y
    unfold naiveDensity
    rw [blockIntegral_blockField]
  have hsq : ∀ y : ℝ, (c * y) ^ 2 = c ^ 2 * y ^ 2 := fun y => by ring
  simp only [h, hsq]
  rw [integral_const_mul, integral_sq_blockUnit]
  ring

/-- **The coarse density is right and the naive density is wrong, by exactly the mean
conditional variance**: `∫ coarseDensity = ∫ |Psi|² = 1 + c²`, while `∫ naiveDensity = c²`. -/
theorem integral_naiveDensity_add_one (c : ℝ) :
    ∫ y, naiveDensity c y ∂blockUnit + 1 = 1 + c ^ 2 := by
  rw [integral_naiveDensity]
  ring

/-- **The tower identity at the observable level**: integrating the coarse density reproduces
the mean of `|Psi_c|²`. -/
theorem integral_coarseDensity_eq_integral_blockField_sq (c : ℝ) :
    ∫ y, coarseDensity c y ∂blockUnit = ∫ p, (blockField c p) ^ 2 ∂blockLaw := by
  have hX : MemLp (fun p : ℝ × ℝ => p.1) 2 blockLaw :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).comp_fst _
  have hY : MemLp (fun p : ℝ × ℝ => p.2) 2 blockLaw :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).comp_snd _
  have hPsi : MemLp (blockField c) 2 blockLaw := by
    have hsum : MemLp (fun p : ℝ × ℝ => p.1 + c * p.2) 2 blockLaw :=
      hX.add (hY.const_mul c)
    simpa [blockField] using hsum
  have hint : Integrable (fun p : ℝ × ℝ => (blockField c p) ^ 2) blockLaw :=
    MemLp.integrable_sq hPsi
  have h := integral_blockIntegral (fun p => (blockField c p) ^ 2) hint
  have hfun : blockIntegral (fun p => (blockField c p) ^ 2) = coarseDensity c := by
    funext y
    rfl
  rw [hfun] at h
  exact h.symm

/-- **Variance decomposition**: the full second moment is the second moment of the conditional
means plus the mean conditional variance.  This is the sense in which an exact coarse step
preserves the conditional means *and* their covariances. -/
theorem variance_decomposition (c : ℝ) :
    ∫ p, (blockField c p) ^ 2 ∂blockLaw
      = ∫ y, naiveDensity c y ∂blockUnit + 1 := by
  rw [integral_blockField_sq, integral_naiveDensity]
  ring

/-! ## The chain: the same block step, applied twice -/

/-- **The three-coordinate reference law**: an inner block, a shell and the exterior field, all
three independent unit Gaussians. -/
def blockChainLaw : Measure ((ℝ × ℝ) × ℝ) := blockLaw.prod blockUnit

instance blockChainLaw_isProbability : IsProbabilityMeasure blockChainLaw := by
  unfold blockChainLaw
  infer_instance

/-- **The first coarse step**: integrate the inner block out at fixed shell `z` and exterior
field `y`. -/
def blockStep (f : (ℝ × ℝ) × ℝ → ℝ) (z y : ℝ) : ℝ := blockIntegral (fun p => f (p, y)) z

/-- **The chain density**: apply the same block step to the shell.  This is the coarse density
of `f` after two steps of coarse graining. -/
def blockChainDensity (f : (ℝ × ℝ) × ℝ → ℝ) (y : ℝ) : ℝ := ∫ z, blockStep f z y ∂blockUnit

/-- The chain density is literally the block integral applied to the result of the first step:
the second step is not a new construction but the same map one scale down. -/
theorem blockChainDensity_eq_iterated (f : (ℝ × ℝ) × ℝ → ℝ) (y : ℝ) :
    blockChainDensity f y
      = blockIntegral (fun q : ℝ × ℝ => blockIntegral (fun p : ℝ × ℝ => f (p, q.2)) q.1) y :=
  rfl

/-- **The tower identity for two steps**: integrating the chain density over the exterior fields
recovers the joint integral of the three-coordinate law. -/
theorem integral_blockChainDensity (f : (ℝ × ℝ) × ℝ → ℝ) (hf : Integrable f blockChainLaw) :
    ∫ p, f p ∂blockChainLaw = ∫ y, blockChainDensity f y ∂blockUnit := by
  rw [blockChainLaw, integral_prod_symm f hf]
  refine integral_congr_ae ?_
  filter_upwards [hf.prod_left_ae] with y hy
  have h := integral_blockIntegral (fun q : ℝ × ℝ => f (q, y)) hy
  simpa [blockChainDensity, blockStep] using h

/-- The chain fixes constants. -/
theorem blockChainDensity_const (c y : ℝ) : blockChainDensity (fun _ => c) y = c := by
  have h : ∀ z, blockStep (fun _ => c) z y = c := by
    intro z
    unfold blockStep
    exact blockIntegral_const c z
  unfold blockChainDensity
  simp only [h]
  rw [integral_const]
  simp

/-- The chain is positive. -/
theorem blockChainDensity_nonneg (f : (ℝ × ℝ) × ℝ → ℝ) (y : ℝ) (hf : ∀ p, 0 ≤ f p) :
    0 ≤ blockChainDensity f y := by
  unfold blockChainDensity
  exact integral_nonneg fun z => blockIntegral_nonneg (fun p => f (p, y)) z fun p => hf (p, y)

/-- The chain is additive. -/
theorem blockChainDensity_add (f g : (ℝ × ℝ) × ℝ → ℝ) (y : ℝ)
    (hf : Integrable (fun p : ℝ × ℝ => f (p, y)) blockLaw)
    (hg : Integrable (fun p : ℝ × ℝ => g (p, y)) blockLaw) :
    blockChainDensity (f + g) y = blockChainDensity f y + blockChainDensity g y := by
  have hfi : Integrable (fun z : ℝ => ∫ x, f ((x, z), y) ∂blockUnit) blockUnit :=
    hf.integral_prod_right
  have hgi : Integrable (fun z : ℝ => ∫ x, g ((x, z), y) ∂blockUnit) blockUnit :=
    hg.integral_prod_right
  have hcongr : ∀ᵐ z ∂blockUnit,
      (∫ x, (f + g) ((x, z), y) ∂blockUnit)
        = (∫ x, f ((x, z), y) ∂blockUnit) + ∫ x, g ((x, z), y) ∂blockUnit := by
    filter_upwards [hf.prod_left_ae, hg.prod_left_ae] with z hfz hgz
    exact integral_add hfz hgz
  have hleft : blockChainDensity (f + g) y
      = ∫ z, ((∫ x, f ((x, z), y) ∂blockUnit) + ∫ x, g ((x, z), y) ∂blockUnit) ∂blockUnit := by
    unfold blockChainDensity blockStep blockIntegral
    rw [integral_congr_ae hcongr]
  rw [hleft]
  unfold blockChainDensity blockStep blockIntegral
  rw [integral_add hfi hgi]

/-- The chain fixes observables of the exterior field. -/
theorem blockChainDensity_exterior (g : ℝ → ℝ) (y : ℝ) :
    blockChainDensity (fun p => g p.2) y = g y := by
  have h : ∀ z, blockStep (fun p : (ℝ × ℝ) × ℝ => g p.2) z y = g y := by
    intro z
    unfold blockStep
    exact blockIntegral_const (g y) z
  unfold blockChainDensity
  simp only [h]
  rw [integral_const]
  simp

/-! ## The cylinder field across the two steps -/

/-- The three-coordinate cylinder field: inner block `x`, shell `z`, exterior `y`, with the two
couplings `c` and `d`. -/
def blockChainField (c d : ℝ) : (ℝ × ℝ) × ℝ → ℝ := fun p => p.1.1 + c * p.1.2 + d * p.2

/-- **The first step does not see the exterior coupling**: after the inner block is integrated
out the conditional mean is `c z + d y`, the sum of the shell and exterior parts. -/
theorem blockStep_blockChainField (c d z y : ℝ) :
    blockStep (blockChainField c d) z y = c * z + d * y := by
  have hx : Integrable (fun x : ℝ => x) blockUnit :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable (by norm_num)
  have hcz : Integrable (fun x : ℝ => c * z) blockUnit := integrable_const _
  have hdy : Integrable (fun _ : ℝ => d * y) blockUnit := integrable_const _
  have hfun : ∀ x : ℝ, blockChainField c d ((x, z), y) = (x + c * z) + d * y := fun _ => rfl
  unfold blockStep blockIntegral
  simp only [hfun]
  rw [integral_add (f := fun x : ℝ => x + c * z) (g := fun _ : ℝ => d * y)
      (hx.add hcz) hdy,
    integral_add (f := fun x : ℝ => x) (g := fun _ : ℝ => c * z) hx hcz,
    integral_id_blockUnit, integral_const, integral_const]
  simp

/-- **The second step removes the shell too**: the chain conditional mean is the exterior part
`d y` alone.  The interior coupling `c` is gone, which is the background-stability statement of
the small-field packet at this scale. -/
theorem blockChainDensity_blockChainField (c d y : ℝ) :
    blockChainDensity (blockChainField c d) y = d * y := by
  have hcz : Integrable (fun z : ℝ => c * z) blockUnit :=
    ((memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable (by norm_num)).const_mul c
  have hdy : Integrable (fun _ : ℝ => d * y) blockUnit := integrable_const _
  unfold blockChainDensity
  simp only [blockStep_blockChainField]
  rw [integral_add (f := fun z : ℝ => c * z) (g := fun _ : ℝ => d * y) hcz hdy,
    integral_const_mul, integral_id_blockUnit, mul_zero, integral_const]
  simp

/-- **The interior coupling is irrelevant at the coarse scale**: two different interior couplings
produce the same conditional mean after the second step. -/
theorem blockChainDensity_blockChainField_independent (c c' d y : ℝ) :
    blockChainDensity (blockChainField c d) y = blockChainDensity (blockChainField c' d) y := by
  rw [blockChainDensity_blockChainField, blockChainDensity_blockChainField]

/-! ## C3b: the small-field packet on the chain -/

/-- The square of a shifted unit Gaussian: `∫ (x + a)² = 1 + a²`.  This is the one block
variance that the two steps accumulate. -/
theorem integral_sq_add_blockUnit (a : ℝ) :
    ∫ x, (x + a) ^ 2 ∂blockUnit = 1 + a ^ 2 := by
  have h := blockIntegral_blockField_sq 1 a
  simpa [blockField] using h

/-- The block integral of a square with a shell-dependent shift: at fixed shell the shift is a
constant, so only its value at that shell matters. -/
theorem blockIntegral_sq_add (h : ℝ → ℝ) (z : ℝ) :
    blockIntegral (fun p : ℝ × ℝ => (p.1 + h p.2) ^ 2) z = 1 + (h z) ^ 2 := by
  unfold blockIntegral
  exact integral_sq_add_blockUnit (h z)

/-- **The first step of the density**: the inner block contributes its unit variance, and the
remaining shift is the shell-plus-exterior part. -/
theorem blockStep_blockChainField_sq (c d z y : ℝ) :
    blockStep (fun p => (blockChainField c d p) ^ 2) z y = 1 + (c * z + d * y) ^ 2 := by
  have hfun : ∀ p : ℝ × ℝ,
      (blockChainField c d (p, y)) ^ 2 = (p.1 + (c * p.2 + d * y)) ^ 2 := by
    intro p
    unfold blockChainField
    ring
  unfold blockStep
  simp only [hfun]
  exact blockIntegral_sq_add (fun z' => c * z' + d * y) z

/-- The second moment of an affine function of a unit Gaussian. -/
theorem integral_sq_affine_blockUnit (c d y : ℝ) :
    ∫ z, (c * z + d * y) ^ 2 ∂blockUnit = c ^ 2 + d ^ 2 * y ^ 2 := by
  have hz : Integrable (fun z : ℝ => z) blockUnit :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable (by norm_num)
  have hz2 : Integrable (fun z : ℝ => z ^ 2) blockUnit :=
    MemLp.integrable_sq (memLp_id_gaussianReal 2)
  have hc2 : Integrable (fun z : ℝ => c ^ 2 * z ^ 2) blockUnit := hz2.const_mul _
  have hlin : Integrable (fun z : ℝ => 2 * (c * (d * y)) * z) blockUnit := hz.const_mul _
  have hconst : Integrable (fun _ : ℝ => (d * y) ^ 2) blockUnit := integrable_const _
  have hfun : ∀ z : ℝ, (c * z + d * y) ^ 2
      = c ^ 2 * z ^ 2 + (2 * (c * (d * y)) * z + (d * y) ^ 2) := by
    intro z
    ring
  simp only [hfun]
  rw [integral_add (f := fun z : ℝ => c ^ 2 * z ^ 2)
      (g := fun z : ℝ => 2 * (c * (d * y)) * z + (d * y) ^ 2) hc2 (hlin.add hconst),
    integral_add (f := fun z : ℝ => 2 * (c * (d * y)) * z) (g := fun _ : ℝ => (d * y) ^ 2)
      hlin hconst,
    integral_const_mul, integral_const_mul, integral_id_blockUnit, integral_sq_blockUnit,
    integral_const, mul_zero]
  simp
  ring

/-- **The density after two steps**: both integrated directions contribute their unit variance.
The result is quadratic in the exterior field and carries each coupling once. -/
theorem blockChainDensity_blockChainField_sq (c d y : ℝ) :
    blockChainDensity (fun p => (blockChainField c d p) ^ 2) y = 1 + c ^ 2 + d ^ 2 * y ^ 2 := by
  have hmem : MemLp (fun z : ℝ => c * z + d * y) 2 blockUnit :=
    ((memLp_id_gaussianReal (μ := 0) (v := 1) 2).const_mul c).add (memLp_const (d * y))
  have hquad : Integrable (fun z : ℝ => (c * z + d * y) ^ 2) blockUnit :=
    MemLp.integrable_sq hmem
  have hone : Integrable (fun _ : ℝ => (1 : ℝ)) blockUnit := integrable_const _
  unfold blockChainDensity
  simp only [blockStep_blockChainField_sq]
  rw [integral_add (f := fun _ : ℝ => (1 : ℝ)) (g := fun z : ℝ => (c * z + d * y) ^ 2)
      hone hquad,
    integral_sq_affine_blockUnit]
  simp
  ring

/-- The **naive density after two steps**: the square of the chain conditional mean. -/
def blockNaiveChainDensity (c d : ℝ) (y : ℝ) : ℝ :=
  (blockChainDensity (blockChainField c d) y) ^ 2

/-- **The chain coarse density is the naive one plus the accumulated covariance.** -/
theorem blockChainDensity_eq_naive_add (c d y : ℝ) :
    blockChainDensity (fun p => (blockChainField c d p) ^ 2) y
      = blockNaiveChainDensity c d y + (1 + c ^ 2) := by
  unfold blockNaiveChainDensity
  rw [blockChainDensity_blockChainField_sq, blockChainDensity_blockChainField]
  ring

/-- **The conditional covariance accumulated over the two steps**. -/
def blockChainCovariance (c d : ℝ) (y : ℝ) : ℝ :=
  blockChainDensity (fun p => (blockChainField c d p) ^ 2) y
    - (blockChainDensity (blockChainField c d) y) ^ 2

/-- **The covariance is a constant**: `1 + c²`, the sum of the two integrated unit variances. -/
theorem blockChainCovariance_eq (c d y : ℝ) : blockChainCovariance c d y = 1 + c ^ 2 := by
  unfold blockChainCovariance
  rw [blockChainDensity_blockChainField_sq, blockChainDensity_blockChainField]
  ring

/-- **The covariance does not depend on the exterior background**, so it cannot grow with the
field strength: the stability of the chosen background at this scale. -/
theorem blockChainCovariance_independent_of_background (c d y y' : ℝ) :
    blockChainCovariance c d y = blockChainCovariance c d y' := by
  rw [blockChainCovariance_eq, blockChainCovariance_eq]

/-- **The scale-uniform local covariance bound** (the C3b small-field estimate on this system):
for `|c| ≤ 1` the covariance accumulated over two steps lies between `1` and `2`, uniformly in the
exterior field `y` and the exterior coupling `d`. -/
theorem blockChainCovariance_small_field (c d y : ℝ) (hc : |c| ≤ 1) :
    1 ≤ blockChainCovariance c d y ∧ blockChainCovariance c d y ≤ 2 := by
  have hc2 : c ^ 2 ≤ 1 := by
    rw [sq_le_one_iff_abs_le_one]
    exact hc
  rw [blockChainCovariance_eq]
  constructor <;> nlinarith

/-! ## The activity norm -/

/-- The **activity norm** of a local observable: its `L¹` norm at the reference law.  This is the
explicitly defined norm in which the small-field activity estimate is stated. -/
def blockActivityNorm (f : ℝ × ℝ → ℝ) : ℝ := ∫ p, |f p| ∂blockLaw

/-- The activity norm of a two-step observable. -/
def blockChainActivityNorm (f : (ℝ × ℝ) × ℝ → ℝ) : ℝ := ∫ p, |f p| ∂blockChainLaw

/-- **A coarse step contracts the activity norm**: a partial integral over a probability
measure cannot increase the `L¹` norm.  This is the estimate a polymer activity estimate needs,
stated for a general block measure. -/
theorem integral_abs_partialIntegral_le {α : Type*} [MeasurableSpace α]
    (μ : Measure α) [IsProbabilityMeasure μ] (f : α × ℝ → ℝ)
    (hf : Integrable f (μ.prod blockUnit)) :
    ∫ y, |∫ a, f (a, y) ∂μ| ∂blockUnit ≤ ∫ p, |f p| ∂(μ.prod blockUnit) := by
  have hn : Integrable (fun p : α × ℝ => |f p|) (μ.prod blockUnit) := by
    simpa only [Real.norm_eq_abs] using hf.norm
  have houter : Integrable (fun y : ℝ => ∫ a, |f (a, y)| ∂μ) blockUnit :=
    hn.integral_prod_right
  have hleft : Integrable (fun y : ℝ => |∫ a, f (a, y) ∂μ|) blockUnit := by
    simpa only [Real.norm_eq_abs] using (hf.integral_prod_right).norm
  calc ∫ y, |∫ a, f (a, y) ∂μ| ∂blockUnit
      ≤ ∫ y, (∫ a, |f (a, y)| ∂μ) ∂blockUnit :=
        integral_mono hleft houter fun y => by
          simpa only [Real.norm_eq_abs] using norm_integral_le_integral_norm (fun a => f (a, y))
    _ = ∫ p, |f p| ∂(μ.prod blockUnit) :=
        (integral_prod_symm (fun p : α × ℝ => |f p|) hn).symm

/-- The one-step activity contraction. -/
theorem integral_abs_blockIntegral_le (f : ℝ × ℝ → ℝ) (hf : Integrable f blockLaw) :
    ∫ y, |blockIntegral f y| ∂blockUnit ≤ blockActivityNorm f := by
  have h : ∫ y, |∫ x, f (x, y) ∂blockUnit| ∂blockUnit
      ≤ ∫ p, |f p| ∂(blockUnit.prod blockUnit) :=
    integral_abs_partialIntegral_le blockUnit f (by simpa [blockLaw] using hf)
  rw [blockActivityNorm, blockLaw]
  exact h

/-- **The two-step activity contraction**: the chain also cannot increase the activity norm. -/
theorem integral_abs_blockChainDensity_le (f : (ℝ × ℝ) × ℝ → ℝ)
    (hf : Integrable f blockChainLaw) :
    ∫ y, |blockChainDensity f y| ∂blockUnit ≤ blockChainActivityNorm f := by
  have hae : ∫ y, |blockChainDensity f y| ∂blockUnit
      = ∫ y, |∫ q, f (q, y) ∂blockLaw| ∂blockUnit := by
    refine integral_congr_ae ?_
    filter_upwards [hf.prod_left_ae] with y hy
    have hEq : blockChainDensity f y = ∫ q : ℝ × ℝ, f (q, y) ∂blockLaw := by
      unfold blockChainDensity blockStep blockIntegral
      exact (integral_prod_symm (fun q : ℝ × ℝ => f (q, y)) hy).symm
    rw [hEq]
  rw [hae, blockChainActivityNorm]
  exact integral_abs_partialIntegral_le blockLaw f (by simpa [blockChainLaw] using hf)

/-! ## The totals, and the large-field complement of the small-field packet

The small-field packet bounds the covariance where the background is small in *coupling*.
The complement of C3b is the regime where the background field itself is large, and on this
reference system that regime can be disposed of exactly: the covariance is fixed, so where the
coarse density is large the covariance is a negligible *relative* correction. -/

/-- **The mean of the naive coarse density** after two steps is `d²`, the exterior-dependent
part. -/
theorem integral_blockNaiveChainDensity (c d : ℝ) :
    ∫ y, blockNaiveChainDensity c d y ∂blockUnit = d ^ 2 := by
  have h : ∀ y : ℝ, blockNaiveChainDensity c d y = d ^ 2 * y ^ 2 := by
    intro y
    unfold blockNaiveChainDensity
    rw [blockChainDensity_blockChainField]
    ring
  have hy2 : Integrable (fun y : ℝ => y ^ 2) blockUnit :=
    MemLp.integrable_sq (memLp_id_gaussianReal 2)
  simp only [h]
  rw [integral_const_mul, integral_sq_blockUnit]
  ring

/-- **The total of the coarse density** after two steps: `1 + c² + d²`, one unit of variance
from each integrated coordinate plus the exterior term. -/
theorem integral_blockChainDensity_sq (c d : ℝ) :
    ∫ y, blockChainDensity (fun p => (blockChainField c d p) ^ 2) y ∂blockUnit
      = 1 + c ^ 2 + d ^ 2 := by
  have h : ∀ y : ℝ, blockChainDensity (fun p => (blockChainField c d p) ^ 2) y
      = 1 + (c ^ 2 + d ^ 2 * y ^ 2) := by
    intro y
    rw [blockChainDensity_blockChainField_sq]
    ring
  have hy2 : Integrable (fun y : ℝ => y ^ 2) blockUnit :=
    MemLp.integrable_sq (memLp_id_gaussianReal 2)
  have h1 : Integrable (fun _ : ℝ => (1 : ℝ)) blockUnit := integrable_const _
  have hrest : Integrable (fun y : ℝ => c ^ 2 + d ^ 2 * y ^ 2) blockUnit :=
    (integrable_const (c ^ 2)).add (hy2.const_mul (d ^ 2))
  have hc : Integrable (fun _ : ℝ => c ^ 2) blockUnit := integrable_const _
  have hd : Integrable (fun y : ℝ => d ^ 2 * y ^ 2) blockUnit := hy2.const_mul (d ^ 2)
  simp only [h]
  rw [integral_add (f := fun _ : ℝ => (1 : ℝ)) (g := fun y : ℝ => c ^ 2 + d ^ 2 * y ^ 2)
      h1 hrest,
    integral_add (f := fun _ : ℝ => c ^ 2) (g := fun y : ℝ => d ^ 2 * y ^ 2) hc hd,
    integral_const_mul, integral_sq_blockUnit, integral_const, integral_const]
  simp
  ring

/-- **The totals differ by exactly the accumulated covariance**: integrating the chain
coarse/naive gap over the exterior field returns `1 + c²`, the same constant that bounds the
covariance pointwise. -/
theorem integral_blockChainDensity_eq_integral_naive_add (c d : ℝ) :
    ∫ y, blockChainDensity (fun p => (blockChainField c d p) ^ 2) y ∂blockUnit
      = (∫ y, blockNaiveChainDensity c d y ∂blockUnit) + (1 + c ^ 2) := by
  rw [integral_blockChainDensity_sq, integral_blockNaiveChainDensity]
  ring

/-- The naive density vanishes at zero background. -/
theorem blockNaiveChainDensity_zero_background (c d : ℝ) :
    blockNaiveChainDensity c d 0 = 0 := by
  unfold blockNaiveChainDensity
  rw [blockChainDensity_blockChainField]
  ring

/-- The coarse density does **not** vanish there: at zero background it is the accumulated
covariance `1 + c²`.  So the error of the naive prescription is largest exactly at the
background where the small-field packet applies, which is why the large-field complement is
stated as a *relative* bound. -/
theorem blockChainDensity_sq_zero_background (c d : ℝ) :
    blockChainDensity (fun p => (blockChainField c d p) ^ 2) 0 = 1 + c ^ 2 := by
  rw [blockChainDensity_blockChainField_sq]
  ring

/-- **The covariance grows only quadratically in the coupling**: for `|c| ≤ M` it is at most
`1 + M²`.  The small-field bound is the case `M = 1`; there is no exponential growth in the
field strength. -/
theorem blockChainCovariance_le_coupling_sq (c d y M : ℝ) (hM : |c| ≤ M) :
    blockChainCovariance c d y ≤ 1 + M ^ 2 := by
  have hc2 : c ^ 2 ≤ M ^ 2 := by
    nlinarith [abs_le.mp hM]
  rw [blockChainCovariance_eq]
  linarith

/-- **The large-field complement of the small-field packet.**  Wherever the exterior part of the
field dominates, `√(2/ε) ≤ |d y|`, the covariance is at most the fraction `ε` of the coarse
density: the accumulated variance is a negligible correction relative to the density it
corrects.  With `ε = 1` this is the statement that on `|d y| ≥ √2` the correction is at most
half of the total. -/
theorem blockChainCovariance_le_mul_density (c d y ε : ℝ) (hε : 0 < ε) (hc : |c| ≤ 1)
    (hR : Real.sqrt (2 / ε) ≤ |d * y|) :
    blockChainCovariance c d y
      ≤ ε * blockChainDensity (fun p => (blockChainField c d p) ^ 2) y := by
  have hc2 : c ^ 2 ≤ 1 := by
    rw [sq_le_one_iff_abs_le_one]
    exact hc
  have hsq : (Real.sqrt (2 / ε)) ^ 2 ≤ |d * y| ^ 2 := by
    have hmul := mul_self_le_mul_self (Real.sqrt_nonneg (2 / ε)) hR
    simpa [pow_two] using hmul
  have h2 : 2 / ε ≤ d ^ 2 * y ^ 2 := by
    rw [Real.sq_sqrt (by positivity), sq_abs, mul_pow] at hsq
    exact hsq
  have hmul : ε * (2 / ε) = 2 := by
    field_simp
  rw [blockChainCovariance_eq, blockChainDensity_blockChainField_sq]
  nlinarith

end

end BookProof.OSReconstruction
