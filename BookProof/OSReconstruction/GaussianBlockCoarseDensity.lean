import Mathlib

/-!
# The coarse density of a Gaussian block step

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

## Boundary

* One block and one exterior coordinate, real-valued fields, unit Gaussian reference law.  No
  gauge structure, no lattice, no multi-block coarse-graining map and no scale iteration: the
  RG action is not represented, only the exact conditional step of a single reference Gaussian.
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

end

end BookProof.OSReconstruction
