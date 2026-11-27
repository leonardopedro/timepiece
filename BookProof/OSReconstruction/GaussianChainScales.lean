import BookProof.OSReconstruction.GaussianBlockCoarseDensity
import BookProof.OSReconstruction.GaussianMoments

/-!
# The block step through arbitrarily many scales

Plan: `cftproof.md`, **C3d** — the requirement that the coupling trajectory "stays in the
induction domain through arbitrarily many UV scales".  `GaussianBlockCoarseDensity` applies the
coarse-graining step twice, on a three-coordinate reference system.  This module makes the scale
index a parameter: the step is iterated `n` times, the accumulated covariance is computed in
closed form, and it is bounded **uniformly in `n`**.

The reference system is unchanged — independent unit Gaussians — but two things are made
scale-indexed:

* the **field** carries the geometric weights of a rescaling by `c` per scale, with the exterior
  background damped by `c` at every step; equivalently the background coupling *runs*,
  `d ↦ c d`, which is the one coupling trajectory this reference system supports;
* the **accumulated covariance** obeys `K_{n+1} = 1 + c² K_n` — one unit of variance per
  integrated scale — and hence `K_n ≤ 1/(1 − c²)` for every `n`, i.e. the small-field domain is
  preserved through arbitrarily many scales.

## Contents

* `shellLaw` — the law of `n` independent unit Gaussians on `Fin n → ℝ`;
* `shellDensity` — the `n`-fold partial integral: integrate out the first `n` coordinates of an
  observable on `Fin (n+1) → ℝ` at fixed value `y` of the last (exterior) coordinate;
* `streamField`, `streamField_cons` — the scale-indexed cylinder field, whose recursion
  `Psi_{n+1}(z, g) = z + c * Psi_n(g)` is the exponential weight `c` per scale;
* `streamCovariance`, `streamCovariance_succ` — the accumulated covariance `K_n = 1 + c² K_{n-1}`;
* `integral_quadratic_blockUnit` — the one-dimensional moment computation the induction needs;
* `shellDensity_quadratic` — **the scale-indexed density**: for every `n`, the coarse density of
  a quadratic functional of the field is the quadratic functional of the running mean
  `c^n d y` with the accumulated covariance `K_n` in place of the one-step variance;
* `shellDensity_streamField`, `shellDensity_streamField_sq` — the mean and the second moment;
* `streamCovariance_nonneg`, `streamCovariance_le_card`, `streamCovariance_le_inv` — `K_n` is
  nonnegative, at most `n`, and **at most `1/(1 − c²)` uniformly in `n`** whenever `c² < 1`;
* `integral_shellDensity_streamField_sq` — the total over the exterior field, `K_n + c^{2n} d²`;
* `integral_shellLaw_cons` — **the product law splits at every scale**: the law of `n + 2`
  coordinates is `blockUnit ⊗ shellLaw (n + 1)`, so each step of the density recursion is a
  genuine partial integral over the reference law, not only a formal iteration;
* `streamCovariance_inv_sub`, `streamCovariance_lt_inv`, `tendsto_streamCovariance` — **the fixed
  point**: `1/(1 − c²)` is the fixed point of `K ↦ 1 + c² K`, the exact error after `n` scales is
  `(c²)^n/(1 − c²)`, and the covariance converges to it geometrically in the number of scales;
* `tendsto_integral_shellDensity_streamField_sq` — the total, integrated over the exterior field,
  converges to the same fixed point at fixed background;
* `shellDensity_congr`, `shellDensity_nonneg` — the density respects equality of integrands and
  preserves pointwise nonnegativity (the two structural facts estimates need);
* `shellDensity_affine_field_le` — **Chebyshev for the step, with an affine threshold**: for any
  `a`, `b`, the density of `1{M ≤ |a·(field − running mean) + b|}` is at most
  `(a² K_n + b²)/M²`.  One step multiplies `a` by `c` and adds the unit variance of the new
  coordinate, which is exactly the recursion `K_{n+1} = 1 + c² K_n`;
* `shellTail`, `shellTail_le` — **the large-field tail at `n` scales**: the deviation probability
  is bounded by `K_n/M²`, so with `c² < 1` the tail is bounded uniformly in `n` — the
  large-field complement in the only form this reference system supports;
* `integral_shellLaw_cons_succ` — the product-law splitting of `integral_shellLaw_cons` with an
  `m`-dimensional shell, so that it applies at every scale including `m = 0`;
* `abs_shellDensity_le`, `measurable_streamField`, `measurable_comp_fin_cons`,
  `measurable_comp_fin_snoc`, `measurable_fin_snoc_prod` — the boundedness and measurability
  facts the tower induction needs;
* `shellDensity_eq_integral_snoc` — **the density is a reference-law integral**: at fixed exterior
  value `y`, `shellDensity n f y = ∫ g, f (Fin.snoc g y) ∂shellLaw n`.  This is the pointwise
  form of the tower, and it is what the tail is read through;
* `integral_shellDensity_eq` — **the tower identity at every scale**:
  `∫ y, shellDensity n f y ∂blockUnit = ∫ p, f p ∂shellLaw (n + 1)` for measurable bounded `f`;
* `shellTail_eq_integral_snoc` — the Chebyshev tail as a genuine reference-law expectation over
  the `n` inner coordinates at fixed exterior value, rather than a formal iterated integral;
* `shellDensity_subst_last`, `shellTail_eq_density_renorm` — the last coordinate of the vector
  always carries the exterior value, so reading it off inside the observable gives the same
  density;
* `renormField`, `shellLargeSet`, `shellTailLaw` — **the renormalised observable**
  `streamField − c^n d p_last`, the set where it exceeds `M`, and the **law-level tail**, i.e. the
  `shellLaw (n + 1)`-measure of that set (a probability, not a density);
* `integral_shellTail_eq`, `shellTailLaw_eq_integral` — the tower applied to the indicator: the
  density-level tail integrates to the law-level tail, which is the indicator's integral;
* `shellTailLaw_nonneg`, `shellTailLaw_le_one` — the law-level tail is in `[0, 1]`;
* `shellTailLaw_le`, `shellTailLaw_le_inv` — **Chebyshev at the level of the law**, and its
  scale-uniform form `≤ 1/((1 − c²)M²)` when `c² < 1`;
* `exists_shellTailLaw_le` — **tightness of the renormalised observables**: for every `ε > 0`
  there is a threshold `M > 0` with `shellTailLaw n c d M ≤ ε` at *every* number of scales `n`;
* `shellLaw_eq_productGauss`, `integral_shellLaw_prod_coord` — the reference law is the product
  Gaussian of `GaussianMoments`, and the multiplicity factorisation read at a tuple of sites;
* `integral_shellLaw_prod_coord_eq_wickSum`, `integral_shellLaw_prod_coord_odd`,
  `integral_shellLaw_prod_coord_even` — the multiplicity factorisation in **Wick form, uniformly
  in the number of fields**: at every `M` the moment is the weighted pairing sum, the odd-`M`
  moments vanish, and the even-`M` moments are the sum over the pairings;
* `exists_odd_card_fiber_three`, `integral_pow_odd_blockUnit`, `integral_shellLaw_coord_three`,
  `integral_shellLaw_coord_five` — **the three- and five-point functions vanish**, because an odd
  number of sites cannot all occur an even number of times;
* `pairingSet_four`, `wickSum_four`, `integral_shellLaw_coord_four` — **the four-point function is
  the sum over the three pairings**, `E[p_i p_j p_k p_l] = δ_ij δ_kl + δ_ik δ_jl + δ_il δ_jk`;
* `pairingSet_six`, `pairingSet_six_card`, `wickSum_six`, `integral_shellLaw_coord_six` — **the
  six-point function is the sum over the fifteen pairings**, the `3 · 5 · 1` perfect matchings of
  six sites, by Isserlis' theorem on the product Gaussian;
* `connectedFour`, `connectedFourShell_eq`, `connectedFourShell_eq_zero`,
  `connectedFour_coord_eq_zero` — **the connected four-point function vanishes**: the joint
  cumulant is the Möbius sum over the partitions of the four positions, the centred law keeps only
  the pairing partitions (`κ = m₁₂₃₄ − m₁₂ m₃₄ − m₁₃ m₂₄ − m₁₄ m₂₃`), and Isserlis makes it zero;
* `connectedFive`, `connectedFive_eq_zero`, `connectedFiveShell_eq_zero`,
  `connectedFive_coord_eq_zero` — **the connected five-point function vanishes**: the fifth joint
  cumulant is the Möbius sum over the 52 partitions of the five positions, and on five positions
  every partition has a block of one, three or five elements, whose moment is zero;
* `connectedSix`, `connectedSix_eq_reduced`, `connectedSixShell_eq_zero`,
  `connectedSix_coord_eq_zero` — **the connected six-point function vanishes too**: the sixth
  joint cumulant is the Möbius sum over the 203 partitions of the six positions, the odd blocks
  still drop out, and the surviving even partitions (`6`, `4 + 2`, `2 + 2 + 2`) cancel by
  Isserlis matching by matching, `1 - 3 + 2 = 0`;
* `shellMoment`, `shellMoment_eq_wickSum` — **Isserlis' theorem in pairing form at every order**:
  the joint moment of any finite set of positions is the `wickSum` of the `δ` covariance, by the
  general Wick recursion `wick_pi` for linear forms rather than by enumerating pairings;
* `cumulant`, `cumulant_eq_zero_of_wick`, `cumulant_wickSum_eq_zero` — **cumulants of arbitrary
  order and the vanishing of all higher ones**: the cumulant is the Möbius inversion of the
  moments over the partition lattice, every cumulant of order at least three of a Gaussian face
  vanishes, and its `wickSum` form is the matching cancellation (`1 - 3 + 2 = 0` at order six);
* `cumulant_shellMoment_eq_zero`, `cumulant_seven_eq_zero` — **every joint cumulant of the
  reference law of order at least three vanishes**, the seventh included.

## Boundary

* The `n` scales are `n` *fresh independent* Gaussians: the measure is a product, so no block map,
  no scaling of the lattice, no measure pushforward and no renormalisation of the law occurs
  between steps.  What runs is a *weight*, `c^n`, put in by hand; the covariance recursion is a
  consequence of independence, not of a flow.  The coupling trajectory `d ↦ c d` is therefore a
  definition, not a theorem about an interacting RG map.
* Hence this is not C3d in the plan's sense.  Nothing here shows that a coupling trajectory of an
  *interacting* effective action stays in an induction domain: there is no effective action, no
  counterterm, no marginal or irrelevant direction, no volume/insertion/separation dependence and
  no logarithmic running.  The `n`-uniform bound is a statement about a geometric series weighted
  by independent Gaussian variances, and its constancy in `n` is exactly the triviality of the
  reference flow.
* The bound `K_n ≤ 1/(1 − c²)` requires `c² < 1` and degenerates as `c² → 1`; it is not a
  statement about a critical point.  The tail bound `shellTail_le` is Chebyshev for the iterated
  partial integral: it uses only the second moment `K_n`, so it is a moment estimate, not a
  bad-block entropy or a polymer expansion, and it carries no gauge chart, volume or insertion
  dependence.  `M` is a threshold in the field's own units, not a normalized large-field region.
  The convergence of `K_n` to `1/(1 − c²)` is a statement about *this* recursion — a geometric
  series in `c²` — and not about the flow of an effective action reaching a critical fixed point.
  The tail bound is a second-moment (Chebyshev) estimate; there is still no bad-block entropy, no
  polymer expansion and no small-field/large-field *decomposition* of an interacting weight.  Its
  law-level form (`shellTailLaw_le_inv`, `exists_shellTailLaw_le`) is the tightness packet at the
  end of this file, which starts C3e; no limiting law and no correlation estimate is proved.
  The only multi-point functions here are those of the *reference* law
  (`integral_shellLaw_coord_three` through `integral_shellLaw_coord_six`, the vanishing connected
  four-, five- and six-point functions `connectedFour_coord_eq_zero`,
  `connectedFive_coord_eq_zero` and `connectedSix_coord_eq_zero`, and the vanishing cumulants of
  every order `cumulant_shellMoment_eq_zero` with the uniform Wick lemmas behind them), and they
  are Isserlis for independent unit Gaussians: they say nothing about the interacting theory, no
  cluster or separated connected-correlation statement is derived from them, and they are
  moments and cumulants, not a characterisation of Gaussianity.
* `shellDensity` is *defined* as the `n`-fold iterated partial integral: it integrates the first
  `n` coordinates at fixed value of the last one.  The **tower identity** `∫ y, shellDensity n f y
  ∂blockUnit = ∫ p, f p ∂shellLaw (n + 1)` *is* proved, but only for measurable **bounded**
  observables.  The proof does not permute coordinates: it fixes the exterior value as the *last*
  coordinate (`Fin.snoc`) and splits the product law at its *first* one, so the recursion's peel
  and the tower's split agree and no Fubini step is needed.  Boundedness is what supplies
  integrability of the sections (`Integrable.of_bound`), which is exactly the gap that a Fubini
  proof would have had to close.  Consequently the polynomial observables used for the moments
  (`streamField`'s square) are **not** covered: extending the tower to them needs `L¹` section
  hypotheses in place of a uniform bound, and the moment statements remain statements about the
  iterated integral.  What *is* covered is the indicator defining `shellTail`, since indicators
  are bounded, and that is how `shellTail_eq_integral_snoc` is derived.

  The tower says nothing about renormalisation, blocks or an interacting weight: it identifies two
  ways of integrating one observable over a product of independent Gaussians.  It is the
  coherence of the definitions, not a new estimate.
* The tightness packet is **tightness of one scalar sequence, not a compactness or convergence
  theorem**.  `exists_shellTailLaw_le` says the laws of the renormalised observables are tight on
  the line — for every `ε` one threshold works at all scales — which is the analytic hypothesis
  of Prokhorov's theorem, but Prokhorov's theorem itself, a limiting law, a Cauchy estimate for
  correlations and the four-point (or any multi-point) functions of C3e/C4 are not proved.  The
  renormalisation is the subtraction of the damped background `c^n d` read off the exterior
  coordinate, which is what makes the second moment scale-uniform; it is not a renormalisation of
  an interacting observable, and no observable is shown to converge.
* The affine packet generalises that tightness from one observable to a whole affine family:
  `shellAffineTailLaw n c d M a b` is the law-level tail of `a·renormField + b`, the iterated and
  law-level forms are identified (`shellAffineTail_eq`, `integral_shellAffineTail_eq`), its
  Chebyshev bound is `(a² K_n + b²)/M²` (`shellAffineTailLaw_le`), uniform bound
  `(a²/(1 − c²) + b²)/M²` (`shellAffineTailLaw_le_inv`), and `exists_shellAffineTailLaw_le`
  produces one threshold valid at every scale for a fixed `(a, b)`.  It is still a Chebyshev
  estimate at a *bounded* observable (an indicator): no expectation or variance of an affine image
  is computed, because that needs the `L¹` extension of the tower that the previous bullet records
  as missing (the later two-point packet computes the variance of the renormalised observable
  itself, but not of its affine images).  `shellAffineTailLaw_one_zero` shows the scalar packet is
  the case `a = 1`, `b = 0`.
* The `L¹` packet removes the boundedness restriction **at the level of totals**: the bounded
  tower is applied to the truncation `min (a·S + b)² (N : ℝ)`, the truncation's density is
  dominated by the exact quadratic value at every scale (`shellDensity_sq_min_le`) and converges
  to it (`tendsto_shellDensity_sq_min`), and monotone convergence then gives
  `lintegral_shellLaw_sq`.  From that come `integrable_sq_affine`, the moment identity
  `integral_shellLaw_sq`, the mean `integral_shellLaw_streamField` (`= 0` — the drift cancels
  once the exterior coordinate is averaged too), the variance
  `integral_shellLaw_centered_sq = K_n + (c^n d)²` and its scale-uniform bound
  `variance_shellLaw_le ≤ 1/(1 − c²) + d²`.  The per-`y` identity
  `shellDensity_eq_integral_snoc` is *still* bounded-only: what is gained is the law-level
  integral, obtained by truncation rather than by a Fubini/section-integrability argument.
* The two-point packet closes the covariance gap the previous bullet left open.
  `integral_shellLaw_coord` and `integral_shellLaw_coord_sq` compute a single coordinate's first
  two moments (`0` and `1`), and `integral_shellLaw_streamField_mul_last` gives the field's
  covariance with the exterior coordinate, `c^n·d`.  Subtracting the drift is therefore exactly a
  decorrelation: `integral_shellLaw_renormField_mul_last = 0`, and the renormalised observable's
  variance is the drift-free `integral_shellLaw_renormField_centered_sq = K_n`, uniformly
  `≤ 1/(1 − c²)` (`variance_renormField_le`); `covariance_pair_shellLaw` packages the `2×2`
  covariance matrix of `(streamField, p_last)`.  These are computed by Fubini for *integrable*
  functions (`integral_shellLaw_cons_succ`) with the domination
  `|S·p_last| ≤ (S² + p_last²)/2`, which is a stronger standard than the truncation the totals
  needed.
* The interior cross moments complete the kernel: `integral_shellLaw_coord_mul_coord` gives
  `E[p_i·p_j] = 1` on the diagonal and `0` off it, by the same split-at-the-first-coordinate
  induction.  With them the field's coefficient vector is explicit — `streamCoeff` is `c^j` on the
  interior and `c^n·d` on the exterior, and `streamField_eq_sum_coeff` identifies the field with
  that linear statistic — so the two-point kernel of *any* pair of linear statistics is an inner
  product of coefficient vectors (`integral_shellLaw_linear_mul_linear`), that of a statistic
  against a single coordinate is the corresponding coefficient
  (`integral_shellLaw_linear_mul_coord`), and the field against any statistic is the pairing with
  `streamCoeff` (`integral_shellLaw_streamField_mul_linear`).
* The cross-scale packet puts that kernel to work across two different numbers of scales.
  `truncCoeff` lifts a coefficient vector along `Fin.castLE` (zero on the extra coordinates),
  `sum_truncCoeff_mul` shows the lifted pairing is the small-space one, and
  `integral_shellLaw_streamField_mul_smaller` gives the covariance of the field at `n` scales with
  the field at `m < n` scales: `K_m + c^(2m)·d`.  The exterior coefficient `c^m·d` of the smaller
  field meets the *interior* coefficient `c^m` of the larger one, which is why the answer is not
  the smaller field's own second moment `K_m + (c^m d)²`: the larger field treats that coordinate
  as background, and the two readings differ by exactly that drift.
* The moment packet removes the pair restriction altogether in one step.
  `integral_shellLaw_prod_coord_pow` says every coordinate monomial factorises,
  `∫ ∏ i, (p i)^(e i) = ∏ i, ∫ z, z^(e i)`, by `integral_fintype_prod_eq_prod` on the product
  law — no induction, no truncation and no domination.
* The multi-point packet reads that factorisation at the *sites*.  `shellLaw_eq_productGauss`
  identifies the reference law with the product Gaussian of `GaussianMoments`, where Isserlis'
  theorem lives; `integral_shellLaw_prod_coord` is the multiplicity factorisation indexed by a
  tuple of sites rather than by an exponent vector.  Two moments follow.  The three-point function
  vanishes (`integral_shellLaw_coord_three`): the multiplicities of three sites sum to `3`, so one
  of them is odd, and `integral_pow_odd_blockUnit` kills that factor.  The four-point function is
  Isserlis' four-point theorem (`integral_shellLaw_coord_four`):
  `E[p_i p_j p_k p_l] = δ_ij δ_kl + δ_ik δ_jl + δ_il δ_jk`, obtained by identifying the multiplicity
  product with the pairing sum (`wickSum_identity_eq_prod_doubleFactorial`) and evaluating that sum
  on the three pairings of `Fin 4` (`pairingSet_four`, `wickSum_four`).  Still open: any
  Gaussianity statement (nothing here shows the moments force a Gaussian law), and every moment
  beyond the fourth.
-/

namespace BookProof.OSReconstruction

open MeasureTheory ProbabilityTheory Filter Topology

/-- The reference law of `n` independent unit Gaussians, indexed by `Fin n`. -/
noncomputable def shellLaw (n : ℕ) : Measure (Fin n → ℝ) := Measure.pi (fun _ => blockUnit)

instance shellLaw_isProbability (n : ℕ) : IsProbabilityMeasure (shellLaw n) := by
  unfold shellLaw
  infer_instance

/-- **The `n`-fold coarse-graining step**: integrate out the first `n` coordinates of an
observable on `Fin (n + 1) → ℝ`, at fixed value `y` of the last (exterior) coordinate.  The
recursion adds one integrated coordinate per step; the exterior coordinate is the last one. -/
noncomputable def shellDensity : (n : ℕ) → ((Fin (n + 1) → ℝ) → ℝ) → ℝ → ℝ
  | 0 => fun f y => f (fun _ => y)
  | n + 1 => fun f y => ∫ z, shellDensity n (fun g => f (Fin.cons z g)) y ∂blockUnit

/-- The defining equation of the step. -/
theorem shellDensity_succ (n : ℕ) (f : (Fin (n + 2) → ℝ) → ℝ) (y : ℝ) :
    shellDensity (n + 1) f y = ∫ z, shellDensity n (fun g => f (Fin.cons z g)) y ∂blockUnit :=
  rfl

/-- **The scale-indexed cylinder field.**  Coordinate `0` is the innermost block, coordinate `n`
the exterior field.  Each step weights the previous field by `c`, and the exterior background
carries the running weight `c^n d`: this is the coupling trajectory `d ↦ c d` per scale. -/
noncomputable def streamField (c d : ℝ) : (n : ℕ) → (Fin (n + 1) → ℝ) → ℝ
  | 0 => fun f => d * f 0
  | n + 1 => fun f => f 0 + c * streamField c d n (fun j => f j.succ)

/-- The defining recursion of the field. -/
theorem streamField_succ (c d : ℝ) (n : ℕ) (f : Fin (n + 2) → ℝ) :
    streamField c d (n + 1) f = f 0 + c * streamField c d n (fun j => f j.succ) :=
  rfl

/-- **The recursion in the form the density induction uses**: after one more coordinate `z` is
supplied, the field is `z` plus `c` times the previous field. -/
theorem streamField_cons (c d : ℝ) (n : ℕ) (z : ℝ) (g : Fin (n + 1) → ℝ) :
    streamField c d (n + 1) (Fin.cons z g) = z + c * streamField c d n g := by
  rw [streamField_succ]
  simp

/-- **The accumulated covariance over `n` steps**: one unit of variance per integrated scale,
with the recursion `K_{n+1} = 1 + c² K_n`. -/
noncomputable def streamCovariance : ℕ → ℝ → ℝ
  | 0, _ => 0
  | n + 1, c => 1 + c ^ 2 * streamCovariance n c

/-- The defining recursion of the covariance. -/
theorem streamCovariance_succ (n : ℕ) (c : ℝ) :
    streamCovariance (n + 1) c = 1 + c ^ 2 * streamCovariance n c :=
  rfl

/-- The moment computation the induction needs: the integral of a degree-two polynomial. -/
theorem integral_quadratic_blockUnit (p q r : ℝ) :
    ∫ z, (p + q * z + r * z ^ 2) ∂blockUnit = p + r := by
  have hz : Integrable (fun z : ℝ => z) blockUnit :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable (by norm_num)
  have hz2 : Integrable (fun z : ℝ => z ^ 2) blockUnit :=
    MemLp.integrable_sq (memLp_id_gaussianReal 2)
  have hp : Integrable (fun _ : ℝ => p) blockUnit := integrable_const _
  have hq : Integrable (fun z : ℝ => q * z) blockUnit := hz.const_mul q
  have hr : Integrable (fun z : ℝ => r * z ^ 2) blockUnit := hz2.const_mul r
  rw [integral_add (f := fun z : ℝ => p + q * z) (g := fun z : ℝ => r * z ^ 2)
      (hp.add hq) hr,
    integral_add (f := fun _ : ℝ => p) (g := fun z : ℝ => q * z) hp hq,
    integral_const_mul, integral_const_mul, integral_id_blockUnit, integral_sq_blockUnit,
    integral_const]
  simp

/-- **The scale-indexed density identity.**  For every number of scales `n`, the coarse density
of a quadratic functional of the field is the same quadratic functional evaluated at the running
mean `c^n d y`, with the accumulated covariance `K_n` replacing the one-step variance. -/
theorem shellDensity_quadratic :
    ∀ (n : ℕ) (c d A B C y : ℝ),
      shellDensity n (fun f => A + B * streamField c d n f + C * (streamField c d n f) ^ 2) y
        = A + B * (c ^ n * d * y) + C * (streamCovariance n c + (c ^ n * d * y) ^ 2) := by
  intro n
  induction n with
  | zero =>
    intro c d A B C y
    simp only [shellDensity, streamCovariance, streamField, pow_zero, one_mul]
    ring
  | succ n ih =>
    intro c d A B C y
    have hstep : shellDensity (n + 1)
        (fun f => A + B * streamField c d (n + 1) f
          + C * (streamField c d (n + 1) f) ^ 2) y
        = ∫ z, shellDensity n (fun g => A + B * (z + c * streamField c d n g)
            + C * (z + c * streamField c d n g) ^ 2) y ∂blockUnit := by
      rw [shellDensity_succ]
      refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
      simp only [streamField_cons]
    rw [hstep]
    have hpt : ∀ z : ℝ, shellDensity n (fun g => A + B * (z + c * streamField c d n g)
          + C * (z + c * streamField c d n g) ^ 2) y
        = (A + B * z + C * z ^ 2)
          + (B * c + 2 * C * c * z) * (c ^ n * d * y)
          + (C * c ^ 2) * (streamCovariance n c + (c ^ n * d * y) ^ 2) := by
      intro z
      have hfun : (fun g : Fin (n + 1) → ℝ => A + B * (z + c * streamField c d n g)
            + C * (z + c * streamField c d n g) ^ 2)
          = (fun g => (A + B * z + C * z ^ 2)
              + (B * c + 2 * C * c * z) * streamField c d n g
              + (C * c ^ 2) * (streamField c d n g) ^ 2) := by
        funext g
        ring
      rw [hfun, ih c d (A + B * z + C * z ^ 2) (B * c + 2 * C * c * z) (C * c ^ 2) y]
    rw [integral_congr_ae (Filter.Eventually.of_forall hpt)]
    set M := c ^ n * d * y with hM
    set K := streamCovariance n c with hK
    have hpoly : ∀ z : ℝ, ((A + B * z + C * z ^ 2) + (B * c + 2 * C * c * z) * M
          + (C * c ^ 2) * (K + M ^ 2))
        = (A + B * c * M + C * c ^ 2 * (K + M ^ 2)) + (B + 2 * C * c * M) * z + C * z ^ 2 := by
      intro z
      ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hpoly), integral_quadratic_blockUnit]
    rw [streamCovariance_succ, pow_succ]
    ring

/-- **The running mean through `n` scales** is `c^n d y`: the background is damped by `c` at
every step, which is the coupling trajectory `d ↦ c d` of this reference system. -/
theorem shellDensity_streamField (n : ℕ) (c d y : ℝ) :
    shellDensity n (streamField c d n) y = c ^ n * d * y := by
  have h := shellDensity_quadratic n c d 0 1 0 y
  simpa using h

/-- **The second moment through `n` scales**: the accumulated covariance plus the square of the
running mean. -/
theorem shellDensity_streamField_sq (n : ℕ) (c d y : ℝ) :
    shellDensity n (fun f => (streamField c d n f) ^ 2) y
      = streamCovariance n c + (c ^ n * d * y) ^ 2 := by
  have h := shellDensity_quadratic n c d 0 0 1 y
  simpa using h

/-- **The conditional covariance after `n` steps is `K_n`, independent of the background**: the
variance accumulated over the scales does not see the exterior field `y` or its coupling `d`. -/
theorem shellDensity_streamField_covariance (n : ℕ) (c d y : ℝ) :
    shellDensity n (fun f => (streamField c d n f) ^ 2) y
        - (shellDensity n (streamField c d n) y) ^ 2
      = streamCovariance n c := by
  rw [shellDensity_streamField_sq, shellDensity_streamField]
  ring

/-- The accumulated covariance is nonnegative. -/
theorem streamCovariance_nonneg (n : ℕ) (c : ℝ) : 0 ≤ streamCovariance n c := by
  induction n with
  | zero => simp [streamCovariance]
  | succ n ih =>
    rw [streamCovariance_succ]
    have := mul_nonneg (sq_nonneg c) ih
    linarith

/-- The recursion of a geometric partial sum, in the direction the covariance needs. -/
theorem sum_range_pow_succ (x : ℝ) (n : ℕ) :
    ∑ j ∈ Finset.range (n + 1), x ^ j = 1 + x * ∑ j ∈ Finset.range n, x ^ j := by
  rw [Finset.sum_range_succ']
  simp only [pow_succ', pow_zero]
  rw [← Finset.mul_sum]
  ring

/-- **The closed form**: the accumulated covariance is the geometric sum `∑_{j<n} c^{2j}`, one
term per integrated scale. -/
theorem streamCovariance_closed_form (n : ℕ) (c : ℝ) :
    streamCovariance n c = ∑ j ∈ Finset.range n, (c ^ 2) ^ j := by
  induction n with
  | zero => simp [streamCovariance]
  | succ n ih =>
    rw [streamCovariance_succ, ih, sum_range_pow_succ]

/-- In the small-field regime `c² ≤ 1` the accumulated covariance is at most one unit per
scale. -/
theorem streamCovariance_le_card (n : ℕ) (c : ℝ) (hc : c ^ 2 ≤ 1) :
    streamCovariance n c ≤ (n : ℝ) := by
  induction n with
  | zero => simp [streamCovariance]
  | succ n ih =>
    rw [streamCovariance_succ]
    have hK := streamCovariance_nonneg n c
    have hmul : c ^ 2 * streamCovariance n c ≤ 1 * streamCovariance n c :=
      mul_le_mul_of_nonneg_right hc hK
    push_cast
    linarith

/-- **The scale-uniform bound: the induction domain is preserved through arbitrarily many
scales.**  If `c² < 1`, the covariance accumulated over *any* number of steps stays below the
fixed constant `1/(1 − c²)`.  So a coupling trajectory that contracts by `c` per scale keeps the
local covariance inside the small-field domain, uniformly in the number of scales. -/
theorem streamCovariance_le_inv (n : ℕ) (c : ℝ) (hc : c ^ 2 < 1) :
    streamCovariance n c ≤ 1 / (1 - c ^ 2) := by
  induction n with
  | zero =>
    have hpos : 0 < 1 - c ^ 2 := by linarith
    simp only [streamCovariance]
    positivity
  | succ n ih =>
    rw [streamCovariance_succ]
    have hpos : 0 < 1 - c ^ 2 := by linarith
    have hmul : c ^ 2 * streamCovariance n c ≤ c ^ 2 * (1 / (1 - c ^ 2)) :=
      mul_le_mul_of_nonneg_left ih (sq_nonneg c)
    have key : 1 + c ^ 2 * (1 / (1 - c ^ 2)) = 1 / (1 - c ^ 2) := by
      field_simp
      ring
    linarith

/-- **The total through `n` scales**: integrating the coarse density over the exterior field gives
the accumulated covariance plus `c^{2n} d²`, the damped background term. -/
theorem integral_shellDensity_streamField_sq (n : ℕ) (c d : ℝ) :
    ∫ y, shellDensity n (fun f => (streamField c d n f) ^ 2) y ∂blockUnit
      = streamCovariance n c + c ^ (2 * n) * d ^ 2 := by
  have hpt : ∀ y : ℝ, shellDensity n (fun f => (streamField c d n f) ^ 2) y
      = streamCovariance n c + (c ^ n * d) ^ 2 * y ^ 2 := by
    intro y
    rw [shellDensity_streamField_sq]
    ring
  have hc : Integrable (fun _ : ℝ => streamCovariance n c) blockUnit := integrable_const _
  have hy2 : Integrable (fun y : ℝ => (c ^ n * d) ^ 2 * y ^ 2) blockUnit :=
    (MemLp.integrable_sq (memLp_id_gaussianReal 2)).const_mul ((c ^ n * d) ^ 2)
  rw [integral_congr_ae (Filter.Eventually.of_forall hpt),
    integral_add (f := fun _ : ℝ => streamCovariance n c)
      (g := fun y : ℝ => (c ^ n * d) ^ 2 * y ^ 2) hc hy2,
    integral_const_mul, integral_sq_blockUnit, integral_const]
  have hpow : (c ^ n * d) ^ 2 = c ^ (2 * n) * d ^ 2 := by
    rw [mul_pow, ← pow_mul]
    ring_nf
  simp [hpow]

/-! ## The product law splits at every scale -/

/-- **The reference law of `n + 2` coordinates splits at its innermost coordinate.**  Integrating
an observable over the product of `n + 2` unit Gaussians is the same as integrating its `Fin.cons`
form: the block law in the innermost coordinate, the `n + 1`-coordinate law in the shell.  This is
the measure-level content of one recursion step of `shellDensity`, and it holds at every scale. -/
theorem integral_shellLaw_cons (n : ℕ) (f : (Fin (n + 2) → ℝ) → ℝ)
    (hf : Integrable f (shellLaw (n + 2))) :
    ∫ p, f p ∂shellLaw (n + 2)
      = ∫ z, (∫ g, f (Fin.cons z g) ∂shellLaw (n + 1)) ∂blockUnit := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 2) => blockUnit) 0
  have hmeas := MeasurableEquiv.measurableEmbedding
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => ℝ) 0)
  have hcomp : (fun q : ℝ × (Fin (n + 1) → ℝ) => f (Fin.cons q.1 q.2))
      ∘ ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => ℝ) 0) = f := by
    funext x
    simp [Function.comp, Fin.cons_self_tail]
  have hcomp' : (fun x : Fin (n + 2) → ℝ =>
      f (Fin.cons ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => ℝ) 0) x).1
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 2) => ℝ) 0) x).2)) = f := by
    ext x
    simp [Fin.cons_self_tail]
  have hInt : Integrable (fun q : ℝ × (Fin (n + 1) → ℝ) => f (Fin.cons q.1 q.2))
      (blockUnit.prod (shellLaw (n + 1))) :=
    (hmp.integrable_comp_emb hmeas (g := fun q => f (Fin.cons q.1 q.2))).mp
      (hcomp ▸ hf)
  have hsplit : ∫ p, f p ∂shellLaw (n + 2)
      = ∫ q : ℝ × (Fin (n + 1) → ℝ), f (Fin.cons q.1 q.2)
          ∂(blockUnit.prod (shellLaw (n + 1))) := by
    have h := hmp.integral_comp hmeas (fun q => f (Fin.cons q.1 q.2))
    rw [hcomp'] at h
    simpa [shellLaw] using h
  rw [hsplit, integral_prod (f := fun q : ℝ × (Fin (n + 1) → ℝ) => f (Fin.cons q.1 q.2)) hInt]

/-! ## The fixed point of the reference flow -/

/-- **The exact error of the recursion**: the accumulated covariance is the fixed point
`1/(1 − c²)` of `K ↦ 1 + c² K` minus the geometric tail `(c²)^n/(1 − c²)`.  The scale-uniform
bound `streamCovariance_le_inv` is therefore the shadow of a convergent recursion, not merely an
inequality. -/
theorem streamCovariance_inv_sub (n : ℕ) (c : ℝ) (hc : c ^ 2 < 1) :
    1 / (1 - c ^ 2) - streamCovariance n c = (c ^ 2) ^ n / (1 - c ^ 2) := by
  have hpos : 0 < 1 - c ^ 2 := by linarith
  have hkey : streamCovariance n c + (c ^ 2) ^ n / (1 - c ^ 2) = 1 / (1 - c ^ 2) := by
    induction n with
    | zero =>
      simp only [streamCovariance, pow_zero]
      field_simp
      ring
    | succ n ih =>
      rw [streamCovariance_succ, pow_succ' (c ^ 2) n]
      have hstep : c ^ 2 * streamCovariance n c + c ^ 2 * (c ^ 2) ^ n / (1 - c ^ 2)
          = c ^ 2 * (streamCovariance n c + (c ^ 2) ^ n / (1 - c ^ 2)) := by
        field_simp
      have hreassoc : 1 + c ^ 2 * streamCovariance n c + c ^ 2 * (c ^ 2) ^ n / (1 - c ^ 2)
          = 1 + (c ^ 2 * streamCovariance n c + c ^ 2 * (c ^ 2) ^ n / (1 - c ^ 2)) := by
        ring
      rw [hreassoc, hstep, ih]
      field_simp
      ring
  linarith

/-- **The covariance stays strictly below the fixed point** whenever the weight is nontrivial:
with `c ≠ 0` every scale adds a positive amount of variance. -/
theorem streamCovariance_lt_inv (n : ℕ) (c : ℝ) (hc : c ^ 2 < 1) (hc0 : c ≠ 0) :
    streamCovariance n c < 1 / (1 - c ^ 2) := by
  have hpos : 0 < 1 - c ^ 2 := by linarith
  have hc2 : 0 < c ^ 2 := pow_two_pos_of_ne_zero hc0
  have hpow : 0 < (c ^ 2) ^ n := pow_pos hc2 n
  have htail : 0 < (c ^ 2) ^ n / (1 - c ^ 2) := div_pos hpow hpos
  have h := streamCovariance_inv_sub n c hc
  linarith

/-- **The accumulated covariance converges to the fixed point of the recursion**, geometrically in
the number of scales.  This is the sharp form of "the induction domain is preserved through
arbitrarily many scales": the domain is preserved because the trajectory converges inside it. -/
theorem tendsto_streamCovariance (c : ℝ) (hc : c ^ 2 < 1) :
    Tendsto (fun n => streamCovariance n c) atTop (𝓝 (1 / (1 - c ^ 2))) := by
  have hpow : Tendsto (fun n : ℕ => (c ^ 2) ^ n) atTop (𝓝 0) :=
    tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg c) hc
  have herr : Tendsto (fun n : ℕ => (c ^ 2) ^ n / (1 - c ^ 2)) atTop (𝓝 0) := by
    simpa using hpow.div_const (1 - c ^ 2)
  have hdiff : Tendsto (fun n : ℕ => 1 / (1 - c ^ 2) - streamCovariance n c) atTop (𝓝 0) := by
    refine herr.congr' ?_
    filter_upwards with n
    exact (streamCovariance_inv_sub n c hc).symm
  have hconst : Tendsto (fun _ : ℕ => 1 / (1 - c ^ 2)) atTop (𝓝 (1 / (1 - c ^ 2))) :=
    tendsto_const_nhds
  simpa using hconst.sub hdiff

/-- **The total through `n` scales converges to the same fixed point** at fixed background: the
damped background term `c^{2n} d²` vanishes, leaving the accumulated covariance. -/
theorem tendsto_integral_shellDensity_streamField_sq (c d : ℝ) (hc : c ^ 2 < 1) :
    Tendsto (fun n => ∫ y, shellDensity n (fun f => (streamField c d n f) ^ 2) y ∂blockUnit)
      atTop (𝓝 (1 / (1 - c ^ 2))) := by
  have hK := tendsto_streamCovariance c hc
  have hd : Tendsto (fun n : ℕ => (c ^ 2) ^ n * d ^ 2) atTop (𝓝 0) := by
    simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one (sq_nonneg c) hc).mul_const (d ^ 2)
  have hsum := hK.add hd
  have heq : (fun n => streamCovariance n c + (c ^ 2) ^ n * d ^ 2)
      =ᶠ[atTop] fun n => ∫ y, shellDensity n (fun f => (streamField c d n f) ^ 2) y ∂blockUnit := by
    filter_upwards with n
    rw [integral_shellDensity_streamField_sq, pow_mul]
  simpa using hsum.congr' heq

/-! ## The large-field tail at every scale -/

/-- The density of a pointwise-equal integrand is the same: the density is an iterated integral, and
equality of integrands passes through every partial integral. -/
theorem shellDensity_congr (n : ℕ) {f g : (Fin (n + 1) → ℝ) → ℝ} (h : ∀ x, f x = g x) (y : ℝ) :
    shellDensity n f y = shellDensity n g y := by
  induction n with
  | zero => simpa [shellDensity] using h (fun _ => y)
  | succ n ih =>
    rw [shellDensity_succ, shellDensity_succ]
    exact integral_congr_ae (Eventually.of_forall fun z => ih (fun g' => h (Fin.cons z g')))

/-- A pointwise nonnegative integrand has a nonnegative density: the density is an iterated integral
of a nonnegative function. -/
theorem shellDensity_nonneg (n : ℕ) {f : (Fin (n + 1) → ℝ) → ℝ} (hf : ∀ x, 0 ≤ f x) (y : ℝ) :
    0 ≤ shellDensity n f y := by
  induction n with
  | zero => simpa [shellDensity] using hf (fun _ => y)
  | succ n ih =>
    rw [shellDensity_succ]
    exact integral_nonneg_of_ae (Eventually.of_forall fun z => ih (fun g => hf (Fin.cons z g)))

/-- Polynomials of degree two are integrable against the one-dimensional block law. -/
theorem integrable_poly_blockUnit (a b : ℝ) :
    Integrable (fun z : ℝ => (a * z + b) ^ 2) blockUnit := by
  have hz : Integrable (fun z : ℝ => z) blockUnit :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable (by norm_num)
  have hz2 : Integrable (fun z : ℝ => z ^ 2) blockUnit :=
    MemLp.integrable_sq (memLp_id_gaussianReal 2)
  have hfun : (fun z : ℝ => (a * z + b) ^ 2)
      = fun z : ℝ => a ^ 2 * z ^ 2 + 2 * a * b * z + b ^ 2 := by
    funext z
    ring
  rw [hfun]
  exact ((hz2.const_mul (a ^ 2)).add (hz.const_mul (2 * a * b))).add
    (integrable_const (b ^ 2))

/-- **Chebyshev for the iterated step, with an affine threshold.**  For any affine function of the
excess over the running mean, the density of the large-deviation indicator is bounded by the
quadratic majorant `a² K_n + b²` divided by the square of the threshold.  The induction is the
reason the `n`-scale tail is uniform: one step multiplies `a` by the weight `c`, and the unit
variance of the newly integrated coordinate is exactly what `K_{n+1} = 1 + c² K_n` records. -/
theorem shellDensity_affine_field_le (n : ℕ) (c d y M a b : ℝ) (hM : 0 < M) :
    shellDensity n (fun f =>
      if M ≤ |a * (streamField c d n f - c ^ n * d * y) + b| then 1 else 0) y
      ≤ (a ^ 2 * streamCovariance n c + b ^ 2) / M ^ 2 := by
  induction n generalizing a b with
  | zero =>
    have h0 : shellDensity 0 (fun f =>
        if M ≤ |a * (streamField c d 0 f - c ^ 0 * d * y) + b| then 1 else 0) y
        = if M ≤ |b| then 1 else 0 := by
      simp [shellDensity, streamField]
    rw [h0]
    have hK : streamCovariance 0 c = 0 := rfl
    rw [hK]
    simp only [mul_zero, zero_add]
    have hM2 : (0 : ℝ) < M ^ 2 := by positivity
    by_cases hb : M ≤ |b|
    · rw [if_pos hb, one_le_div hM2]
      nlinarith [abs_nonneg b, sq_abs b]
    · rw [if_neg hb]
      positivity
  | succ n ih =>
    rw [shellDensity_succ]
    have hpt : ∀ z : ℝ, shellDensity n (fun g =>
        if M ≤ |a * (streamField c d (n + 1) (Fin.cons z g) - c ^ (n + 1) * d * y) + b|
          then 1 else 0) y
        ≤ ((a * c) ^ 2 * streamCovariance n c + (a * z + b) ^ 2) / M ^ 2 := by
      intro z
      refine le_trans (le_of_eq (shellDensity_congr n ?_ y)) (ih (a * c) (a * z + b))
      intro g
      have hsec : a * (streamField c d (n + 1) (Fin.cons z g) - c ^ (n + 1) * d * y) + b
          = a * c * (streamField c d n g - c ^ n * d * y) + (a * z + b) := by
        rw [streamField_cons, pow_succ' c n]
        ring
      rw [hsec]
    have hnonneg : ∀ z : ℝ, 0 ≤ shellDensity n (fun g =>
        if M ≤ |a * (streamField c d (n + 1) (Fin.cons z g) - c ^ (n + 1) * d * y) + b|
          then 1 else 0) y := by
      intro z
      refine shellDensity_nonneg n (fun g => ?_) y
      split_ifs <;> norm_num
    have hInt : Integrable (fun z : ℝ =>
        ((a * c) ^ 2 * streamCovariance n c + (a * z + b) ^ 2) / M ^ 2) blockUnit := by
      have hp : Integrable (fun z : ℝ => (a * z + b) ^ 2) blockUnit := integrable_poly_blockUnit a b
      exact ((integrable_const ((a * c) ^ 2 * streamCovariance n c)).add hp).div_const (M ^ 2)
    refine le_trans (integral_mono_of_nonneg (Eventually.of_forall hnonneg) hInt
      (Eventually.of_forall hpt)) ?_
    have hM2 : M ^ 2 ≠ 0 := by positivity
    have hval : ∫ z, ((a * c) ^ 2 * streamCovariance n c + (a * z + b) ^ 2) / M ^ 2
        ∂blockUnit = (a ^ 2 * streamCovariance (n + 1) c + b ^ 2) / M ^ 2 := by
      have hcongr : (fun z : ℝ => ((a * c) ^ 2 * streamCovariance n c + (a * z + b) ^ 2) / M ^ 2)
          = fun z : ℝ => ((a * c) ^ 2 * streamCovariance n c + b ^ 2) / M ^ 2
              + (2 * a * b / M ^ 2) * z + (a ^ 2 / M ^ 2) * z ^ 2 := by
        funext z
        field_simp
        ring
      rw [hcongr, integral_quadratic_blockUnit, streamCovariance_succ]
      field_simp
      ring
    rw [hval]

/-- **The large-field tail at `n` scales**: the probability, as seen by the iterated partial
integral, that the field deviates from its running mean by at least `M`. -/
noncomputable def shellTail (n : ℕ) (c d y M : ℝ) : ℝ :=
  shellDensity n (fun f => if M ≤ |streamField c d n f - c ^ n * d * y| then 1 else 0) y

/-- **Chebyshev at every scale**: the tail of the `n`-scale field is bounded by the accumulated
covariance over the square of the threshold, uniformly in `n` once `c² < 1`.  This is the
large-field complement in the only form the reference system supports, and it is exactly
summable in the sense that the bound does not grow with the number of scales. -/
theorem shellTail_le (n : ℕ) (c d y M : ℝ) (hM : 0 < M) :
    shellTail n c d y M ≤ streamCovariance n c / M ^ 2 := by
  have h := shellDensity_affine_field_le n c d y M 1 0 hM
  simpa [shellTail] using h

/-! ## The tower identity at every scale -/

/-- **Attaching the head and the tail commute**: building an `(n + 2)`-vector from a head `z`,
`n` middle entries `g` and a tail `y` gives the same vector in either order. -/
theorem fin_cons_snoc {n : ℕ} (z y : ℝ) (g : Fin n → ℝ) :
    Fin.cons (α := fun _ => ℝ) z (Fin.snoc (α := fun _ => ℝ) g y)
      = Fin.snoc (α := fun _ => ℝ) (Fin.cons (α := fun _ => ℝ) z g) y := by
  ext i
  refine Fin.cases ?_ ?_ i
  · simp
  intro k
  refine Fin.lastCases ?_ ?_ k
  · simp
  · intro j
    simp
    have hidx : (Fin.succ (Fin.castSucc j) : Fin ((n + 1) + 1)) = Fin.castSucc (Fin.succ j) :=
      Fin.ext rfl
    rw [hidx, Fin.snoc_castSucc, Fin.cons_succ]

/-- **Reading a vector off its last coordinate and its prefix returns it** — the `Fin` identity
that lets the last coordinate be the one held fixed. -/
theorem fin_snoc_castSucc_last {n : ℕ} (x : Fin (n + 1) → ℝ) :
    Fin.snoc (α := fun _ => ℝ) (fun j : Fin n => x j.castSucc) (x (Fin.last n)) = x := by
  ext i
  refine Fin.lastCases ?_ ?_ i <;> simp

/-- `g ↦ Fin.cons z g` is measurable. -/
theorem measurable_fin_cons (m : ℕ) (z : ℝ) :
    Measurable (fun g : Fin m → ℝ => Fin.cons (α := fun _ => ℝ) z g) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.cases ?_ ?_ i
  · simp
  · intro j
    simpa using measurable_pi_apply j

/-- `g ↦ Fin.snoc g y` is measurable. -/
theorem measurable_fin_snoc (m : ℕ) (y : ℝ) :
    Measurable (fun g : Fin m → ℝ => Fin.snoc (α := fun _ => ℝ) g y) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.lastCases ?_ ?_ i
  · simp
  · intro j
    simpa using measurable_pi_apply j

/-- `(y, g) ↦ Fin.snoc g y` is measurable on the product. -/
theorem measurable_fin_snoc_prod (m : ℕ) :
    Measurable (fun q : ℝ × (Fin m → ℝ) => Fin.snoc (α := fun _ => ℝ) q.2 q.1) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.lastCases ?_ ?_ i
  · simpa using measurable_fst
  · intro j
    simpa using (measurable_pi_apply j).comp measurable_snd

/-- Measurability survives fixing the head coordinate. -/
theorem measurable_comp_fin_cons {m : ℕ} {f : (Fin (m + 1) → ℝ) → ℝ} (hf : Measurable f)
    (z : ℝ) : Measurable (fun g : Fin m → ℝ => f (Fin.cons z g)) := by
  have h : Measurable ((fun h : Fin (m + 1) → ℝ => f h) ∘
      fun g : Fin m → ℝ => Fin.cons z g) :=
    hf.comp (measurable_fin_cons m z)
  simpa [Function.comp] using h

/-- Measurability survives fixing the last coordinate. -/
theorem measurable_comp_fin_snoc {m : ℕ} {f : (Fin (m + 1) → ℝ) → ℝ} (hf : Measurable f)
    (y : ℝ) : Measurable (fun g : Fin m → ℝ => f (Fin.snoc g y)) := by
  have h : Measurable ((fun h : Fin (m + 1) → ℝ => f h) ∘
      fun g : Fin m → ℝ => Fin.snoc g y) :=
    hf.comp (measurable_fin_snoc m y)
  simpa [Function.comp] using h

/-- **The law of `m + 1` coordinates splits at its innermost coordinate** — the `m`-general form
of `integral_shellLaw_cons`, stated with an `m`-dimensional shell so that it applies at every
scale, including `m = 0`. -/
theorem integral_shellLaw_cons_succ (m : ℕ) (F : (Fin (m + 1) → ℝ) → ℝ)
    (hF : Integrable F (shellLaw (m + 1))) :
    ∫ p, F p ∂shellLaw (m + 1) = ∫ z, (∫ g, F (Fin.cons z g) ∂shellLaw m) ∂blockUnit := by
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (m + 1) => blockUnit) 0
  have hmeas := MeasurableEquiv.measurableEmbedding
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0)
  have hcomp : (fun q : ℝ × (Fin m → ℝ) => F (Fin.cons q.1 q.2))
      ∘ ⇑(MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0) = F := by
    funext x
    simp [Function.comp, Fin.cons_self_tail]
  have hcomp' : (fun x : Fin (m + 1) → ℝ =>
      F (Fin.cons ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0) x).1
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0) x).2)) = F := by
    ext x
    simp [Fin.cons_self_tail]
  have hInt : Integrable (fun q : ℝ × (Fin m → ℝ) => F (Fin.cons q.1 q.2))
      (blockUnit.prod (shellLaw m)) :=
    (hmp.integrable_comp_emb hmeas (g := fun q => F (Fin.cons q.1 q.2))).mp
      (hcomp ▸ hF)
  have hsplit : ∫ p, F p ∂shellLaw (m + 1)
      = ∫ q : ℝ × (Fin m → ℝ), F (Fin.cons q.1 q.2)
          ∂(blockUnit.prod (shellLaw m)) := by
    have h := hmp.integral_comp hmeas (fun q => F (Fin.cons q.1 q.2))
    rw [hcomp'] at h
    simpa [shellLaw] using h
  rw [hsplit, integral_prod (f := fun q : ℝ × (Fin m → ℝ) => F (Fin.cons q.1 q.2)) hInt]

/-- **Bounded observables have bounded densities** at every scale. -/
theorem abs_shellDensity_le :
    ∀ (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℝ) (B : ℝ), 0 ≤ B → (∀ p, |f p| ≤ B) →
      ∀ y, |shellDensity n f y| ≤ B
  | 0, f, _, _, hB, y => by simpa [shellDensity] using hB (fun _ => y)
  | n + 1, f, B, hB0, hB, y => by
    have hmono : ∫ z, |shellDensity n (fun g => f (Fin.cons z g)) y| ∂blockUnit
        ≤ ∫ _z : ℝ, B ∂blockUnit :=
      integral_mono_of_nonneg (μ := blockUnit)
        (f := fun z => |shellDensity n (fun g => f (Fin.cons z g)) y|)
        (g := fun _ => B) (Eventually.of_forall fun _ => abs_nonneg _) (integrable_const B)
        (Eventually.of_forall fun z =>
          abs_shellDensity_le n (fun g => f (Fin.cons z g)) B hB0 (fun _ => hB _) y)
    have hconst : ∫ _z : ℝ, B ∂blockUnit = B := by
      rw [integral_const, probReal_univ, one_smul]
    calc |shellDensity (n + 1) f y|
        = |∫ z, shellDensity n (fun g => f (Fin.cons z g)) y ∂blockUnit| := rfl
      _ ≤ ∫ z, |shellDensity n (fun g => f (Fin.cons z g)) y| ∂blockUnit :=
        abs_integral_le_integral_abs
      _ ≤ ∫ _z : ℝ, B ∂blockUnit := hmono
      _ = B := hconst

/-- **The tower identity at one step**: the `n`-fold partial integral is the integral over the
reference law with the exterior coordinate fixed as the last one. -/
theorem shellDensity_eq_integral_snoc :
    ∀ (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℝ) (B : ℝ), 0 ≤ B → (∀ p, |f p| ≤ B) →
      Measurable f → ∀ y, shellDensity n f y = ∫ g, f (Fin.snoc g y) ∂shellLaw n
  | 0, f, _, _, hB, _, y => by
    haveI : Subsingleton (Fin 0 → ℝ) := ⟨fun a b => funext fun i => i.elim0⟩
    show f (fun _ : Fin (0 + 1) => y) = ∫ g : Fin 0 → ℝ, f (Fin.snoc g y) ∂shellLaw 0
    have hsnoc : (fun _ : Fin (0 + 1) => y) = Fin.snoc (fun _ : Fin 0 => (0 : ℝ)) y :=
      (Fin.snoc_zero _ _).symm
    rw [hsnoc]
    have hconst : ∫ g : Fin 0 → ℝ, f (Fin.snoc g y) ∂(shellLaw 0)
        = f (Fin.snoc (fun _ : Fin 0 => (0 : ℝ)) y) := by
      have hfun : (fun g : Fin 0 → ℝ => f (Fin.snoc g y))
          = fun _ => f (Fin.snoc (fun _ : Fin 0 => (0 : ℝ)) y) := by
        funext g
        rw [Subsingleton.elim g (fun _ : Fin 0 => (0 : ℝ))]
      rw [hfun, integral_const, probReal_univ, one_smul]
    exact hconst.symm
  | n + 1, f, B, hB0, hB, hf, y => by
    have hstep : shellDensity (n + 1) f y
        = ∫ z, shellDensity n (fun g => f (Fin.cons z g)) y ∂blockUnit := rfl
    rw [hstep]
    have hih : ∀ z, shellDensity n (fun g => f (Fin.cons z g)) y
        = ∫ g, f (Fin.cons z (Fin.snoc g y)) ∂shellLaw n := fun z =>
      shellDensity_eq_integral_snoc n (fun g => f (Fin.cons z g)) B hB0
        (fun p => hB _) (measurable_comp_fin_cons hf z) y
    rw [integral_congr_ae (Eventually.of_forall hih)]
    have hcongr : ∀ z, (∫ g, f (Fin.cons z (Fin.snoc g y)) ∂shellLaw n)
        = ∫ g, f (Fin.snoc (Fin.cons z g) y) ∂shellLaw n := fun z =>
      integral_congr_ae (Eventually.of_forall fun g => congrArg f (fin_cons_snoc z y g))
    rw [integral_congr_ae (Eventually.of_forall hcongr)]
    exact (integral_shellLaw_cons_succ n (fun h => f (Fin.snoc h y))
      (Integrable.of_bound (measurable_comp_fin_snoc hf y).aestronglyMeasurable B
        (Eventually.of_forall fun p => by simpa using hB (Fin.snoc p y)))).symm


/-- **The tower identity at every scale**: integrating the `n`-fold partial integral over the
exterior coordinate is integrating the observable over the reference law of `n + 1` independent
unit Gaussians. -/
theorem integral_shellDensity_eq (n : ℕ) (f : (Fin (n + 1) → ℝ) → ℝ) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ p, |f p| ≤ B) (hf : Measurable f) :
    ∫ y, shellDensity n f y ∂blockUnit = ∫ p, f p ∂shellLaw (n + 1) := by
  rw [integral_congr_ae (Eventually.of_forall fun y =>
    shellDensity_eq_integral_snoc n f B hB0 hB hf y)]
  have hInt : Integrable (fun q : ℝ × (Fin n → ℝ) => f (Fin.snoc q.2 q.1))
      (blockUnit.prod (shellLaw n)) :=
    Integrable.of_bound (hf.comp (measurable_fin_snoc_prod n)).aestronglyMeasurable B
      (Eventually.of_forall fun q => by simpa using hB (Fin.snoc q.2 q.1))
  rw [(integral_prod (f := fun q : ℝ × (Fin n → ℝ) => f (Fin.snoc q.2 q.1)) hInt).symm]
  have hmp := measurePreserving_piFinSuccAbove (fun _ : Fin (n + 1) => blockUnit) (Fin.last n)
  have hmeas := MeasurableEquiv.measurableEmbedding
    (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n))
  have hcomp : (fun x : Fin (n + 1) → ℝ =>
      f (Fin.snoc ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)) x).2
        ((MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n + 1) => ℝ) (Fin.last n)) x).1)) = f := by
    funext x
    simp
  have hpc := hmp.integral_comp hmeas (fun q : ℝ × (Fin n → ℝ) => f (Fin.snoc q.2 q.1))
  simpa [shellLaw, hcomp] using hpc.symm

/-- **The reference field is measurable** at every scale. -/
theorem measurable_streamField (c d : ℝ) : ∀ n, Measurable (streamField c d n)
  | 0 => by
    simpa [streamField] using measurable_const.mul (measurable_pi_apply (0 : Fin 1))
  | n + 1 => by
    have htail : Measurable (fun f : Fin (n + 2) → ℝ => fun j : Fin (n + 1) => f j.succ) :=
      measurable_pi_iff.2 fun j => measurable_pi_apply j.succ
    have hcomp : Measurable ((streamField c d n) ∘
        fun f : Fin (n + 2) → ℝ => fun j : Fin (n + 1) => f j.succ) :=
      (measurable_streamField c d n).comp htail
    have hmeas : Measurable (fun f : Fin (n + 2) → ℝ => streamField c d n (fun j => f j.succ)) := by
      simpa [Function.comp] using hcomp
    simpa [streamField] using
      ((measurable_pi_apply (0 : Fin (n + 2))).add (measurable_const.mul hmeas))

/-- **The tail is an expectation over the inner coordinates**: at a fixed exterior value, the
Chebyshev quantity `shellTail` is the reference-law expectation of its indicator, integrated over
the `n` inner coordinates.  This is the tower identity read at the level of the tail. -/
theorem shellTail_eq_integral_snoc (n : ℕ) (c d y M : ℝ) :
    shellTail n c d y M
      = ∫ g : Fin n → ℝ,
          (if M ≤ |streamField c d n (Fin.snoc g y) - c ^ n * d * y| then (1 : ℝ) else 0)
          ∂shellLaw n := by
  have hmeas : Measurable (fun f : Fin (n + 1) → ℝ =>
      if M ≤ |streamField c d n f - c ^ n * d * y| then (1 : ℝ) else 0) :=
    Measurable.ite (measurableSet_Ici.preimage
      (((measurable_streamField c d n).sub measurable_const).abs)) measurable_const measurable_const
  rw [shellTail]
  exact shellDensity_eq_integral_snoc n
    (fun f => if M ≤ |streamField c d n f - c ^ n * d * y| then (1 : ℝ) else 0) 1 zero_le_one
    (fun p => by dsimp only; split_ifs <;> norm_num) hmeas y

/-! ## The renormalised observable, and tightness at the level of the law -/

theorem shellDensity_subst_last :
    ∀ (n : ℕ) (G : ℝ → (Fin (n + 1) → ℝ) → ℝ) (y : ℝ),
      shellDensity n (fun p => G (p (Fin.last n)) p) y = shellDensity n (fun p => G y p) y
  | 0, G, y => rfl
  | n + 1, G, y => by
    have hcons : ∀ (z : ℝ) (g : Fin (n + 1) → ℝ),
        Fin.cons (α := fun _ => ℝ) z g (Fin.last (n + 1)) = g (Fin.last n) := by
      intro z g
      rw [← Fin.succ_last n, Fin.cons_succ]
    have hstep : ∀ (z : ℝ),
        shellDensity n (fun g : Fin (n + 1) → ℝ =>
          G (Fin.cons (α := fun _ => ℝ) z g (Fin.last (n + 1))) (Fin.cons z g)) y
          = shellDensity n (fun g : Fin (n + 1) → ℝ => G y (Fin.cons z g)) y := by
      intro z
      rw [show (fun g : Fin (n + 1) → ℝ =>
            G (Fin.cons (α := fun _ => ℝ) z g (Fin.last (n + 1))) (Fin.cons z g))
          = fun g => G (g (Fin.last n)) (Fin.cons z g) from funext fun g => by rw [hcons]]
      exact shellDensity_subst_last n (fun v h => G v (Fin.cons z h)) y
    rw [shellDensity_succ, shellDensity_succ]
    exact integral_congr_ae (Eventually.of_forall hstep)

/-- **The renormalised observable**: the `n`-scale reference field with the damped background
`c^n d` read off the exterior coordinate removed. -/
noncomputable def renormField (c d : ℝ) (n : ℕ) (p : Fin (n + 1) → ℝ) : ℝ :=
  streamField c d n p - c ^ n * d * p (Fin.last n)

/-- The set on which the renormalised observable exceeds `M` in absolute value. -/
def shellLargeSet (c d : ℝ) (n : ℕ) (M : ℝ) : Set (Fin (n + 1) → ℝ) :=
  {p | M ≤ |renormField c d n p|}

/-- **The law-level tail**: the probability, under the reference law of `n + 1` coordinates, that
the renormalised observable exceeds `M` in absolute value. -/
noncomputable def shellTailLaw (n : ℕ) (c d M : ℝ) : ℝ :=
  (shellLaw (n + 1)).real (shellLargeSet c d n M)

/-- The renormalised observable is measurable. -/
theorem measurable_renormField (c d : ℝ) (n : ℕ) :
    Measurable (renormField c d n) :=
  (measurable_streamField c d n).sub
    (measurable_const.mul (measurable_pi_apply (Fin.last n)))

/-- The large set is measurable. -/
theorem measurableSet_shellLargeSet (c d : ℝ) (n : ℕ) (M : ℝ) :
    MeasurableSet (shellLargeSet c d n M) :=
  measurableSet_Ici.preimage (measurable_renormField c d n).abs

/-- The indicator of the large set, in the form the integrals use. -/
theorem indicator_shellLargeSet (c d : ℝ) (n : ℕ) (M : ℝ) :
    (fun p : Fin (n + 1) → ℝ => if M ≤ |renormField c d n p| then (1 : ℝ) else 0)
      = (shellLargeSet c d n M).indicator (1 : (Fin (n + 1) → ℝ) → ℝ) := by
  classical
  funext p
  simp only [Set.indicator_apply, shellLargeSet, Set.mem_setOf_eq]
  by_cases h : M ≤ |renormField c d n p|
  · simp [if_pos h]
  · simp [if_neg h]

/-- **The tail at fixed exterior value is the law-level indicator at the last coordinate**: the
last coordinate of the configuration always carries the exterior value, so the density of the
indicator is the density of the renormalised observable. -/
theorem shellTail_eq_density_renorm (n : ℕ) (c d y M : ℝ) :
    shellTail n c d y M
      = shellDensity n (fun p => if M ≤ |renormField c d n p| then (1 : ℝ) else 0) y := by
  rw [shellTail]
  exact (shellDensity_subst_last n
    (fun v p => if M ≤ |streamField c d n p - c ^ n * d * v| then (1 : ℝ) else 0) y).symm

/-- **The law-level tail as the total of the density**: the tower identity, applied to the
indicator of the large set. -/
theorem integral_shellTail_eq (n : ℕ) (c d M : ℝ) :
    ∫ y, shellTail n c d y M ∂blockUnit
      = ∫ p, (if M ≤ |renormField c d n p| then (1 : ℝ) else 0) ∂shellLaw (n + 1) := by
  rw [integral_congr_ae (Eventually.of_forall fun y => shellTail_eq_density_renorm n c d y M)]
  refine integral_shellDensity_eq n
    (fun p => if M ≤ |renormField c d n p| then (1 : ℝ) else 0) 1 zero_le_one
    (fun p => ?_) ?_
  · beta_reduce
    split_ifs <;> norm_num
  · exact Measurable.ite (measurableSet_shellLargeSet c d n M) measurable_const measurable_const

/-- **The law-level tail is a probability** — it is the measure of the large set. -/
theorem shellTailLaw_eq_integral (n : ℕ) (c d M : ℝ) :
    shellTailLaw n c d M
      = ∫ p, (if M ≤ |renormField c d n p| then (1 : ℝ) else 0) ∂shellLaw (n + 1) := by
  rw [shellTailLaw, indicator_shellLargeSet]
  exact (integral_indicator_one (measurableSet_shellLargeSet c d n M)).symm

/-- The density-level tail is nonnegative. -/
theorem shellTail_nonneg (n : ℕ) (c d y M : ℝ) : 0 ≤ shellTail n c d y M := by
  rw [shellTail]
  exact shellDensity_nonneg n (fun f => by split_ifs <;> norm_num) y

/-- The law-level tail is nonnegative. -/
theorem shellTailLaw_nonneg (n : ℕ) (c d M : ℝ) : 0 ≤ shellTailLaw n c d M := by
  rw [shellTailLaw]
  exact measureReal_nonneg

/-- The law-level tail is at most one: it is a probability. -/
theorem shellTailLaw_le_one (n : ℕ) (c d M : ℝ) : shellTailLaw n c d M ≤ 1 := by
  rw [shellTailLaw_eq_integral]
  have hmono : ∫ p : Fin (n + 1) → ℝ,
        (if M ≤ |renormField c d n p| then (1 : ℝ) else 0) ∂shellLaw (n + 1)
      ≤ ∫ _p : Fin (n + 1) → ℝ, (1 : ℝ) ∂shellLaw (n + 1) :=
    integral_mono_of_nonneg
      (Eventually.of_forall fun p => by dsimp only; split_ifs <;> norm_num)
      (integrable_const 1)
      (Eventually.of_forall fun p => by dsimp only; split_ifs <;> norm_num)
  calc ∫ p : Fin (n + 1) → ℝ,
        (if M ≤ |renormField c d n p| then (1 : ℝ) else 0) ∂shellLaw (n + 1)
      ≤ ∫ _p : Fin (n + 1) → ℝ, (1 : ℝ) ∂shellLaw (n + 1) := hmono
    _ = 1 := by rw [integral_const, probReal_univ, one_smul]

/-- **Chebyshev at the law level**: the probability that the renormalised observable exceeds `M`
is at most the accumulated covariance over the square of the threshold. -/
theorem shellTailLaw_le (n : ℕ) (c d M : ℝ) (hM : 0 < M) :
    shellTailLaw n c d M ≤ streamCovariance n c / M ^ 2 := by
  rw [shellTailLaw_eq_integral, ← integral_shellTail_eq]
  have hmono : ∫ y, shellTail n c d y M ∂blockUnit
      ≤ ∫ _y : ℝ, streamCovariance n c / M ^ 2 ∂blockUnit :=
    integral_mono_of_nonneg (Eventually.of_forall fun y => shellTail_nonneg n c d y M)
      (integrable_const _) (Eventually.of_forall fun y => shellTail_le n c d y M hM)
  refine le_trans hmono ?_
  rw [integral_const, probReal_univ, one_smul]

/-- **Uniform Chebyshev bound**: for a contracting per-scale weight the law-level tail is bounded
by `1/((1 − c²)M²)` *uniformly in the number of scales*. -/
theorem shellTailLaw_le_inv (n : ℕ) (c d M : ℝ) (hc : c ^ 2 < 1) (hM : 0 < M) :
    shellTailLaw n c d M ≤ 1 / ((1 - c ^ 2) * M ^ 2) := by
  have hpos : 0 < 1 - c ^ 2 := by linarith
  refine le_trans (shellTailLaw_le n c d M hM) ?_
  have hmul : streamCovariance n c * (1 - c ^ 2) ≤ 1 := by
    have h1 : streamCovariance n c ≤ 1 / (1 - c ^ 2) := streamCovariance_le_inv n c hc
    have h2 : (1 / (1 - c ^ 2)) * (1 - c ^ 2) = 1 := by
      field_simp
    nlinarith [h1, h2, hpos]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hmul, hM, hpos]

/-- **Tightness of the renormalised observables**: for every `ε > 0` there is a threshold `M > 0`
beyond which the law-level tail is at most `ε` at *every* number of scales. -/
theorem exists_shellTailLaw_le (c d : ℝ) (hc : c ^ 2 < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ n, shellTailLaw n c d M ≤ ε := by
  have hpos : 0 < 1 - c ^ 2 := by linarith
  refine ⟨1 / ε + 1 / (1 - c ^ 2) + 1, by positivity, fun n => ?_⟩
  refine le_trans (shellTailLaw_le_inv n c d _ hc (by positivity)) ?_
  have hA : (0 : ℝ) < 1 / ε := by positivity
  have hB : (0 : ℝ) < 1 / (1 - c ^ 2) := by positivity
  have hsq : (1 / ε) * (1 / (1 - c ^ 2)) ≤ (1 / ε + 1 / (1 - c ^ 2) + 1) ^ 2 := by
    nlinarith [hA, hB]
  have hkey : ε * ((1 - c ^ 2) * ((1 / ε) * (1 / (1 - c ^ 2)))) = 1 := by
    field_simp
  have hprod : ε * ((1 - c ^ 2) * ((1 / ε) * (1 / (1 - c ^ 2))))
      ≤ ε * ((1 - c ^ 2) * (1 / ε + 1 / (1 - c ^ 2) + 1) ^ 2) := by
    have h1 : (1 - c ^ 2) * ((1 / ε) * (1 / (1 - c ^ 2)))
        ≤ (1 - c ^ 2) * (1 / ε + 1 / (1 - c ^ 2) + 1) ^ 2 :=
      mul_le_mul_of_nonneg_left hsq (le_of_lt hpos)
    exact mul_le_mul_of_nonneg_left h1 (le_of_lt hε)
  rw [div_le_iff₀ (by positivity)]
  linarith



/-! ## Affine images of the renormalised observable -/

/-- **The affine large set**: where an affine functional `a·renorm + b` of the renormalised
observable exceeds `M` in absolute value.  The affine family is what a shifted threshold (a
centred observable, a difference of two observables) is written in. -/
def shellAffineLargeSet (c d : ℝ) (n : ℕ) (M a b : ℝ) : Set (Fin (n + 1) → ℝ) :=
  {p | M ≤ |a * renormField c d n p + b|}

/-- An affine functional of the renormalised observable is measurable. -/
theorem measurable_affine_renormField (c d : ℝ) (n : ℕ) (a b : ℝ) :
    Measurable (fun p : Fin (n + 1) → ℝ => a * renormField c d n p + b) :=
  ((measurable_renormField c d n).const_mul a).add measurable_const

/-- The affine large set is measurable. -/
theorem measurableSet_shellAffineLargeSet (c d : ℝ) (n : ℕ) (M a b : ℝ) :
    MeasurableSet (shellAffineLargeSet c d n M a b) :=
  measurableSet_Ici.preimage (measurable_affine_renormField c d n a b).abs

/-- The indicator of the affine large set, in the form the integrals use. -/
theorem indicator_shellAffineLargeSet (c d : ℝ) (n : ℕ) (M a b : ℝ) :
    (fun p : Fin (n + 1) → ℝ =>
        if M ≤ |a * renormField c d n p + b| then (1 : ℝ) else 0)
      = (shellAffineLargeSet c d n M a b).indicator (1 : (Fin (n + 1) → ℝ) → ℝ) := by
  classical
  funext p
  simp only [Set.indicator_apply, shellAffineLargeSet, Set.mem_setOf_eq]
  by_cases h : M ≤ |a * renormField c d n p + b|
  · simp [if_pos h]
  · simp [if_neg h]

/-- The affine tail at a fixed exterior value, as an iterated partial integral. -/
noncomputable def shellAffineTail (n : ℕ) (c d y M a b : ℝ) : ℝ :=
  shellDensity n (fun p => if M ≤ |a * renormField c d n p + b| then (1 : ℝ) else 0) y

/-- **The affine tail is the affine Chebyshev density**: the last coordinate always carries the
exterior value, so the affine tail is exactly the density bounded by
`shellDensity_affine_field_le`. -/
theorem shellAffineTail_eq (n : ℕ) (c d y M a b : ℝ) :
    shellAffineTail n c d y M a b
      = shellDensity n (fun f =>
          if M ≤ |a * (streamField c d n f - c ^ n * d * y) + b| then (1 : ℝ) else 0) y := by
  show shellDensity n (fun p : Fin (n + 1) → ℝ =>
      if M ≤ |a * (streamField c d n p - c ^ n * d * p (Fin.last n)) + b| then (1 : ℝ) else 0) y = _
  exact shellDensity_subst_last n
    (fun v p => if M ≤ |a * (streamField c d n p - c ^ n * d * v) + b| then (1 : ℝ) else 0) y

/-- The affine tail is nonnegative. -/
theorem shellAffineTail_nonneg (n : ℕ) (c d y M a b : ℝ) :
    0 ≤ shellAffineTail n c d y M a b := by
  rw [shellAffineTail]
  exact shellDensity_nonneg n (fun f => by split_ifs <;> norm_num) y

/-- **Chebyshev for affine images at every scale**, in the iterated form: the density of the affine
large set is bounded by `(a² K_n + b²)/M²`. -/
theorem shellAffineTail_le (n : ℕ) (c d y M a b : ℝ) (hM : 0 < M) :
    shellAffineTail n c d y M a b ≤ (a ^ 2 * streamCovariance n c + b ^ 2) / M ^ 2 := by
  rw [shellAffineTail_eq]
  exact shellDensity_affine_field_le n c d y M a b hM

/-- **The law-level affine tail**: the probability, under the reference law of `n + 1`
coordinates, that `a·renorm + b` exceeds `M` in absolute value. -/
noncomputable def shellAffineTailLaw (n : ℕ) (c d M a b : ℝ) : ℝ :=
  (shellLaw (n + 1)).real (shellAffineLargeSet c d n M a b)

/-- **The affine tail as a total of the density**: the tower identity at the indicator of the
affine large set. -/
theorem integral_shellAffineTail_eq (n : ℕ) (c d M a b : ℝ) :
    ∫ y, shellAffineTail n c d y M a b ∂blockUnit
      = ∫ p, (if M ≤ |a * renormField c d n p + b| then (1 : ℝ) else 0)
          ∂shellLaw (n + 1) := by
  have hfun : (fun y => shellAffineTail n c d y M a b)
      = fun y => shellDensity n
          (fun p => if M ≤ |a * renormField c d n p + b| then (1 : ℝ) else 0) y := rfl
  rw [hfun]
  refine integral_shellDensity_eq n
    (fun p => if M ≤ |a * renormField c d n p + b| then (1 : ℝ) else 0) 1 zero_le_one
    (fun p => ?_) ?_
  · beta_reduce
    split_ifs <;> norm_num
  · exact Measurable.ite (measurableSet_shellAffineLargeSet c d n M a b)
      measurable_const measurable_const

/-- **The law-level affine tail is a probability** — it is the measure of the affine large set. -/
theorem shellAffineTailLaw_eq_integral (n : ℕ) (c d M a b : ℝ) :
    shellAffineTailLaw n c d M a b
      = ∫ p, (if M ≤ |a * renormField c d n p + b| then (1 : ℝ) else 0)
          ∂shellLaw (n + 1) := by
  rw [shellAffineTailLaw, indicator_shellAffineLargeSet]
  exact (integral_indicator_one (measurableSet_shellAffineLargeSet c d n M a b)).symm

/-- The law-level affine tail is nonnegative. -/
theorem shellAffineTailLaw_nonneg (n : ℕ) (c d M a b : ℝ) :
    0 ≤ shellAffineTailLaw n c d M a b := by
  rw [shellAffineTailLaw]
  exact measureReal_nonneg

/-- The law-level affine tail is at most one: it is a probability. -/
theorem shellAffineTailLaw_le_one (n : ℕ) (c d M a b : ℝ) :
    shellAffineTailLaw n c d M a b ≤ 1 := by
  rw [shellAffineTailLaw_eq_integral]
  have hmono : ∫ p : Fin (n + 1) → ℝ,
        (if M ≤ |a * renormField c d n p + b| then (1 : ℝ) else 0) ∂shellLaw (n + 1)
      ≤ ∫ _p : Fin (n + 1) → ℝ, (1 : ℝ) ∂shellLaw (n + 1) :=
    integral_mono_of_nonneg
      (Eventually.of_forall fun p => by dsimp only; split_ifs <;> norm_num)
      (integrable_const 1)
      (Eventually.of_forall fun p => by dsimp only; split_ifs <;> norm_num)
  calc ∫ p : Fin (n + 1) → ℝ,
        (if M ≤ |a * renormField c d n p + b| then (1 : ℝ) else 0) ∂shellLaw (n + 1)
      ≤ ∫ _p : Fin (n + 1) → ℝ, (1 : ℝ) ∂shellLaw (n + 1) := hmono
    _ = 1 := by rw [integral_const, probReal_univ, one_smul]

/-- **Chebyshev at the law level for affine images**: the probability that `a·renorm + b` exceeds
`M` is at most `(a² K_n + b²)/M²`. -/
theorem shellAffineTailLaw_le (n : ℕ) (c d M a b : ℝ) (hM : 0 < M) :
    shellAffineTailLaw n c d M a b ≤ (a ^ 2 * streamCovariance n c + b ^ 2) / M ^ 2 := by
  rw [shellAffineTailLaw_eq_integral, ← integral_shellAffineTail_eq]
  have hmono : ∫ y, shellAffineTail n c d y M a b ∂blockUnit
      ≤ ∫ _y : ℝ, (a ^ 2 * streamCovariance n c + b ^ 2) / M ^ 2 ∂blockUnit :=
    integral_mono_of_nonneg
      (Eventually.of_forall fun y => shellAffineTail_nonneg n c d y M a b)
      (integrable_const _) (Eventually.of_forall fun y => shellAffineTail_le n c d y M a b hM)
  refine le_trans hmono ?_
  rw [integral_const, probReal_univ, one_smul]

/-- **Uniform Chebyshev for affine images**: for a contracting weight the bound is
`(a²/(1 − c²) + b²)/M²`, *uniformly in the number of scales*. -/
theorem shellAffineTailLaw_le_inv (n : ℕ) (c d M a b : ℝ) (hc : c ^ 2 < 1) (hM : 0 < M) :
    shellAffineTailLaw n c d M a b ≤ (a ^ 2 / (1 - c ^ 2) + b ^ 2) / M ^ 2 := by
  have hpos : 0 < 1 - c ^ 2 := by linarith
  refine le_trans (shellAffineTailLaw_le n c d M a b hM) ?_
  have hK : a ^ 2 * streamCovariance n c ≤ a ^ 2 / (1 - c ^ 2) := by
    have h1 : streamCovariance n c ≤ 1 / (1 - c ^ 2) := streamCovariance_le_inv n c hc
    have h := mul_le_mul_of_nonneg_left h1 (sq_nonneg a)
    simpa [div_eq_mul_inv, mul_comm, mul_left_comm, mul_assoc] using h
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [hK, hM, sq_nonneg b, hpos]

/-- **Uniform concentration of the whole affine family**: for every `ε > 0` there is a single
threshold `M > 0` beyond which *every* affine image of the renormalised observable has law-level
tail at most `ε`, at *every* number of scales. -/
theorem exists_shellAffineTailLaw_le (c d a b : ℝ) (hc : c ^ 2 < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ M : ℝ, 0 < M ∧ ∀ n, shellAffineTailLaw n c d M a b ≤ ε := by
  have hpos : 0 < 1 - c ^ 2 := by linarith
  set C := a ^ 2 / (1 - c ^ 2) + b ^ 2 with hC
  have hC0 : 0 ≤ C := by
    rw [hC]
    have : 0 ≤ a ^ 2 / (1 - c ^ 2) := div_nonneg (sq_nonneg a) (le_of_lt hpos)
    linarith [sq_nonneg b]
  set M := 2 / ε + C + 1 with hM
  have hMpos : 0 < M := by rw [hM]; positivity
  refine ⟨M, hMpos, fun n => ?_⟩
  refine le_trans (shellAffineTailLaw_le_inv n c d M a b hc hMpos) ?_
  have hMge : 2 / ε ≤ M := by rw [hM]; linarith
  have hMC : C ≤ M := by
    rw [hM]
    have : 0 < 2 / ε := by positivity
    linarith
  have hstep : ε * M * (2 / ε) = 2 * M := by
    have hne : ε ≠ 0 := ne_of_gt hε
    field_simp
  have hmono : ε * M * (2 / ε) ≤ ε * M * M := by
    refine mul_le_mul_of_nonneg_left hMge ?_
    exact le_of_lt (by positivity)
  have hCM : C ≤ ε * M ^ 2 := by
    have : ε * M * M = ε * M ^ 2 := by ring
    nlinarith [hstep, hmono, hMC, this, hMpos]
  rw [div_le_iff₀ (by positivity)]
  exact hCM

/-- **Consistency with the scalar tail**: the affine family at `a = 1`, `b = 0` is the
renormalised tail of the previous section, so the affine packet is a strict generalisation of it. -/
theorem shellAffineTailLaw_one_zero (n : ℕ) (c d M : ℝ) :
    shellAffineTailLaw n c d M 1 0 = shellTailLaw n c d M := by
  rw [shellAffineTailLaw, shellTailLaw, shellAffineLargeSet, shellLargeSet]
  simp

/-! ## The moment identity: truncation, and monotone convergence through the recursion -/

/-- The second moment of an affine function with a constant shift, against the unit Gaussian. -/
theorem integral_sq_affine_const_blockUnit (a t : ℝ) :
    ∫ z, (a * z + t) ^ 2 ∂blockUnit = a ^ 2 + t ^ 2 := by
  have h := integral_sq_affine_blockUnit a 1 t
  simpa using h

/-- `(z, g) ↦ Fin.cons z g` is measurable jointly in the inserted value. -/
theorem measurable_fin_cons_prod (m : ℕ) :
    Measurable (fun q : ℝ × (Fin m → ℝ) => Fin.cons (α := fun _ => ℝ) q.1 q.2) := by
  refine measurable_pi_iff.2 fun i => ?_
  refine Fin.cases ?_ ?_ i
  · simpa using measurable_fst
  · intro j
    simpa using (measurable_pi_apply j).comp measurable_snd

/-- **The density is measurable in a parameter**: for a jointly measurable family of
observables, the iterated partial integral is measurable as a function of the parameter.  This is
what lets a dominated-convergence argument run through the recursion. -/
theorem measurable_shellDensity_param :
    ∀ (n : ℕ) {β : Type*} [MeasurableSpace β] (Ψ : β → (Fin (n + 1) → ℝ) → ℝ),
      Measurable (Function.uncurry Ψ) → ∀ y, Measurable (fun z : β => shellDensity n (Ψ z) y) := by
  intro n
  induction n with
  | zero =>
    intro β _ Ψ hΨ y
    have h : Measurable (fun z : β => Ψ z (fun _ : Fin 1 => y)) :=
      hΨ.comp (Measurable.prodMk measurable_id measurable_const)
    simpa [shellDensity] using h
  | succ n ih =>
    intro β _ Ψ hΨ y
    have hmap : Measurable (fun p : (β × ℝ) × (Fin (n + 1) → ℝ) =>
        (p.1.1, Fin.cons (α := fun _ => ℝ) p.1.2 p.2)) :=
      Measurable.prodMk (measurable_fst.comp measurable_fst)
        ((measurable_fin_cons_prod (n + 1)).comp
          (Measurable.prodMk (measurable_snd.comp measurable_fst) measurable_snd))
    have hΘ : Measurable (Function.uncurry fun (q : β × ℝ) (g : Fin (n + 1) → ℝ) =>
        Ψ q.1 (Fin.cons (α := fun _ => ℝ) q.2 g)) := by
      have h := hΨ.comp hmap
      simpa [Function.uncurry, Function.comp] using h
    have hIH : Measurable (fun q : β × ℝ => shellDensity n
        (fun g : Fin (n + 1) → ℝ => Ψ q.1 (Fin.cons (α := fun _ => ℝ) q.2 g)) y) :=
      ih (fun (q : β × ℝ) (g : Fin (n + 1) → ℝ) => Ψ q.1 (Fin.cons q.2 g)) hΘ y
    have hgoal : (fun z : β => shellDensity (n + 1) (Ψ z) y)
        = fun z => ∫ z' : ℝ, (fun q : β × ℝ => shellDensity n
            (fun g : Fin (n + 1) → ℝ => Ψ q.1 (Fin.cons (α := fun _ => ℝ) q.2 g)) y)
            (z, z') ∂blockUnit := by
      funext z
      rw [shellDensity_succ]
    rw [hgoal]
    exact (StronglyMeasurable.integral_prod_right
      (f := fun (z : β) (z' : ℝ) => shellDensity n
        (fun g : Fin (n + 1) → ℝ => Ψ z (Fin.cons (α := fun _ => ℝ) z' g)) y)
      hIH.stronglyMeasurable).measurable

/-- **The truncated second moment is bounded by the exact one, at every scale.**  This is the
induction that replaces a monotonicity lemma: the truncation `min (·) N` is dominated by the
explicit quadratic value of the untruncated density, and the domination is preserved one step at
a time, so no integrability of sections of the limit function is ever needed. -/
theorem shellDensity_sq_min_le (n : ℕ) (c d y a b N : ℝ) (hN : 0 ≤ N) :
    shellDensity n (fun p => min ((a * streamField c d n p + b) ^ 2) N) y
      ≤ a ^ 2 * streamCovariance n c + (a * (c ^ n * d * y) + b) ^ 2 := by
  induction n generalizing a b with
  | zero =>
    have h0 : shellDensity 0 (fun p => min ((a * streamField c d 0 p + b) ^ 2) N) y
        = min ((a * (d * y) + b) ^ 2) N := by
      simp [shellDensity, streamField]
    rw [h0, streamCovariance, mul_zero, zero_add]
    simp only [pow_zero, one_mul, mul_zero, zero_add]
    exact min_le_left _ _
  | succ n ih =>
    rw [shellDensity_succ]
    have hpt : ∀ z : ℝ, shellDensity n (fun g =>
        min ((a * streamField c d (n + 1) (Fin.cons z g) + b) ^ 2) N) y
        ≤ ((a * c) ^ 2 * streamCovariance n c
            + ((a * c) * (c ^ n * d * y) + (a * z + b)) ^ 2) := by
      intro z
      refine le_trans (le_of_eq (shellDensity_congr n ?_ y)) (ih (a * c) (a * z + b))
      intro g
      rw [streamField_cons]
      have hlin : a * (z + c * streamField c d n g) + b
          = (a * c) * streamField c d n g + (a * z + b) := by
        ring
      rw [hlin]
    have hnonneg : ∀ z : ℝ, 0 ≤ shellDensity n (fun g =>
        min ((a * streamField c d (n + 1) (Fin.cons z g) + b) ^ 2) N) y := by
      intro z
      exact shellDensity_nonneg n (fun g => le_min (sq_nonneg _) hN) y
    have hInt : Integrable (fun z : ℝ =>
        ((a * c) ^ 2 * streamCovariance n c + ((a * c) * (c ^ n * d * y) + (a * z + b)) ^ 2))
        blockUnit := by
      have hp : Integrable (fun z : ℝ => (a * z + (b + (a * c) * (c ^ n * d * y))) ^ 2)
          blockUnit := by
        simpa [add_comm, add_left_comm, add_assoc] using
          integrable_poly_blockUnit a (b + (a * c) * (c ^ n * d * y))
      refine (integrable_const _).add ?_
      have hcongr : (fun z : ℝ => ((a * c) * (c ^ n * d * y) + (a * z + b)) ^ 2)
          = fun z : ℝ => (a * z + (b + (a * c) * (c ^ n * d * y))) ^ 2 := by
        funext z
        ring
      rw [hcongr]
      exact hp
    refine le_trans (integral_mono_of_nonneg (Eventually.of_forall hnonneg) hInt
      (Eventually.of_forall hpt)) ?_
    have hval : ∫ z, ((a * c) ^ 2 * streamCovariance n c
        + ((a * c) * (c ^ n * d * y) + (a * z + b)) ^ 2) ∂blockUnit
        = a ^ 2 * streamCovariance (n + 1) c + (a * (c ^ (n + 1) * d * y) + b) ^ 2 := by
      have hfun : (fun z : ℝ => ((a * c) ^ 2 * streamCovariance n c
            + ((a * c) * (c ^ n * d * y) + (a * z + b)) ^ 2))
          = fun z : ℝ => (((a * c) ^ 2 * streamCovariance n c
                + (b + a * c * (c ^ n * d * y)) ^ 2))
            + (2 * a * (b + a * c * (c ^ n * d * y))) * z + a ^ 2 * z ^ 2 := by
        funext z
        ring
      rw [hfun, integral_quadratic_blockUnit, streamCovariance_succ, pow_succ]
      ring
    rw [hval]

/-- **Monotone convergence through the recursion**: the truncated second moment converges to the
exact quadratic value at every fixed exterior coordinate.  The induction is a dominated
convergence with the explicit quadratic majorant of `shellDensity_sq_min_le`, so the bounded
tower can be passed to its limit without any integrability assumption on sections. -/
theorem tendsto_shellDensity_sq_min (n : ℕ) (c d y a b : ℝ) :
    Tendsto (fun N : ℕ =>
        shellDensity n (fun p => min ((a * streamField c d n p + b) ^ 2) (N : ℝ)) y)
      atTop (𝓝 (a ^ 2 * streamCovariance n c + (a * (c ^ n * d * y) + b) ^ 2)) := by
  induction n generalizing a b with
  | zero =>
    have hval : a ^ 2 * streamCovariance 0 c + (a * (c ^ 0 * d * y) + b) ^ 2
        = (a * (d * y) + b) ^ 2 := by
      simp [streamCovariance]
    rw [hval]
    refine (tendsto_const_nhds (x := (a * (d * y) + b) ^ 2)).congr' ?_
    filter_upwards [(tendsto_natCast_atTop_atTop (R := ℝ)).eventually
      (eventually_ge_atTop ((a * (d * y) + b) ^ 2))] with N hN
    simp [shellDensity, streamField, min_eq_left hN]
  | succ n ih =>
    simp only [shellDensity_succ]
    set G : ℝ → ℝ := fun z => (a * c) ^ 2 * streamCovariance n c
      + ((a * c) * (c ^ n * d * y) + (a * z + b)) ^ 2 with hG
    have hGint : Integrable G blockUnit := by
      refine (integrable_const _).add ?_
      have hcongr : (fun z : ℝ => ((a * c) * (c ^ n * d * y) + (a * z + b)) ^ 2)
          = fun z : ℝ => (a * z + (b + (a * c) * (c ^ n * d * y))) ^ 2 := by
        funext z
        ring
      rw [hcongr]
      exact integrable_poly_blockUnit a (b + (a * c) * (c ^ n * d * y))
    have hGval : ∫ z, G z ∂blockUnit
        = a ^ 2 * streamCovariance (n + 1) c + (a * (c ^ (n + 1) * d * y) + b) ^ 2 := by
      have hfun : (fun z : ℝ => ((a * c) ^ 2 * streamCovariance n c
            + ((a * c) * (c ^ n * d * y) + (a * z + b)) ^ 2))
          = fun z : ℝ => (((a * c) ^ 2 * streamCovariance n c
                + (b + a * c * (c ^ n * d * y)) ^ 2))
            + (2 * a * (b + a * c * (c ^ n * d * y))) * z + a ^ 2 * z ^ 2 := by
        funext z
        ring
      rw [hG, hfun, integral_quadratic_blockUnit, streamCovariance_succ, pow_succ]
      ring
    rw [← hGval]
    refine tendsto_integral_of_dominated_convergence G ?_ hGint ?_ ?_
    · intro N
      have hΨ : Measurable (Function.uncurry fun (z : ℝ) (g : Fin (n + 1) → ℝ) =>
          min ((a * streamField c d (n + 1) (Fin.cons (α := fun _ => ℝ) z g) + b) ^ 2)
            (N : ℝ)) := by
        have hbase : Measurable (fun q : ℝ × (Fin (n + 1) → ℝ) =>
            a * streamField c d (n + 1) (Fin.cons (α := fun _ => ℝ) q.1 q.2) + b) :=
          (((measurable_streamField c d (n + 1)).comp
            (measurable_fin_cons_prod (n + 1))).const_mul a).add measurable_const
        have hcore : Measurable (fun q : ℝ × (Fin (n + 1) → ℝ) =>
            (a * streamField c d (n + 1) (Fin.cons (α := fun _ => ℝ) q.1 q.2) + b) ^ 2) := by
          simpa [pow_two] using hbase.mul hbase
        exact Measurable.min hcore measurable_const
      exact (measurable_shellDensity_param n _ hΨ y).aestronglyMeasurable
    · intro N
      filter_upwards with z
      have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      have hrewrite : shellDensity n (fun g =>
          min ((a * streamField c d (n + 1) (Fin.cons z g) + b) ^ 2) (N : ℝ)) y
          = shellDensity n (fun g => min
              (((a * c) * streamField c d n g + (a * z + b)) ^ 2) (N : ℝ)) y := by
        refine shellDensity_congr n (fun g => ?_) y
        rw [streamField_cons]
        have hlin : a * (z + c * streamField c d n g) + b
            = (a * c) * streamField c d n g + (a * z + b) := by
          ring
        rw [hlin]
      rw [hrewrite]
      have hnn : 0 ≤ shellDensity n (fun g =>
          min (((a * c) * streamField c d n g + (a * z + b)) ^ 2) (N : ℝ)) y :=
        shellDensity_nonneg n (fun g => le_min (sq_nonneg _) hN) y
      rw [Real.norm_of_nonneg hnn]
      exact shellDensity_sq_min_le n c d y (a * c) (a * z + b) (N : ℝ) hN
    · filter_upwards with z
      have hfun : (fun N : ℕ => shellDensity n (fun g =>
            min ((a * streamField c d (n + 1) (Fin.cons z g) + b) ^ 2) (N : ℝ)) y)
          = fun N : ℕ => shellDensity n (fun g =>
              min (((a * c) * streamField c d n g + (a * z + b)) ^ 2) (N : ℝ)) y := by
        funext N
        refine shellDensity_congr n (fun g => ?_) y
        rw [streamField_cons]
        have hlin : a * (z + c * streamField c d n g) + b
            = (a * c) * streamField c d n g + (a * z + b) := by
          ring
        rw [hlin]
      rw [hfun]
      exact (ih (a * c) (a * z + b)).comp tendsto_natCast_atTop_atTop

/-- **A bounded observable's density is measurable in the exterior coordinate**: by the tower
identity it is an integral of a jointly measurable function of the exterior value and the inner
coordinates. -/
theorem measurable_shellDensity (n : ℕ) {f : (Fin (n + 1) → ℝ) → ℝ} (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ p, |f p| ≤ B) (hf : Measurable f) :
    Measurable (fun y => shellDensity n f y) := by
  have hfun : (fun y => shellDensity n f y)
      = fun y => ∫ g, f (Fin.snoc g y) ∂shellLaw n :=
    funext fun y => shellDensity_eq_integral_snoc n f B hB0 hB hf y
  rw [hfun]
  have hjoint : StronglyMeasurable
      (Function.uncurry fun (y : ℝ) (g : Fin n → ℝ) => f (Fin.snoc g y)) :=
    (hf.comp (measurable_fin_snoc_prod n)).stronglyMeasurable
  exact (StronglyMeasurable.integral_prod_right hjoint).measurable

/-- The supremum of a convergent real sequence, read in `ℝ≥0∞`, is the `ℝ≥0∞` value of its
limit. -/
theorem ofReal_iSup_of_tendsto {u : ℕ → ℝ} {V : ℝ} (hu : Monotone u)
    (hV : Tendsto u atTop (𝓝 V)) :
    (⨆ N, ENNReal.ofReal (u N)) = ENNReal.ofReal V := by
  refine le_antisymm (iSup_le fun N => ENNReal.ofReal_le_ofReal
    (le_of_tendsto_of_tendsto tendsto_const_nhds hV
      (Eventually.mono (eventually_ge_atTop N) fun M hM => hu hM))) ?_
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hεpos : (0 : ℝ) < (ε : ℝ) := by exact_mod_cast hε
  have hlt : V - (ε : ℝ) < V := by linarith
  obtain ⟨N, hN⟩ := (hV.eventually (isOpen_Ioi.mem_nhds hlt)).exists
  have h1 : ENNReal.ofReal V
      ≤ ENNReal.ofReal (V - (ε : ℝ)) + ENNReal.ofReal (ε : ℝ) := by
    calc ENNReal.ofReal V ≤ ENNReal.ofReal ((V - (ε : ℝ)) + (ε : ℝ)) :=
          ENNReal.ofReal_le_ofReal (by linarith)
      _ ≤ ENNReal.ofReal (V - (ε : ℝ)) + ENNReal.ofReal (ε : ℝ) := ENNReal.ofReal_add_le
  have h2 : ENNReal.ofReal (V - (ε : ℝ)) ≤ ⨆ N, ENNReal.ofReal (u N) :=
    le_iSup_of_le N (ENNReal.ofReal_le_ofReal (le_of_lt hN))
  calc ENNReal.ofReal V ≤ ENNReal.ofReal (V - (ε : ℝ)) + ENNReal.ofReal (ε : ℝ) := h1
    _ ≤ (⨆ N, ENNReal.ofReal (u N)) + ENNReal.ofReal (ε : ℝ) := add_le_add h2 le_rfl
    _ = (⨆ N, ENNReal.ofReal (u N)) + ε := by rw [ENNReal.ofReal_coe_nnreal]

/-- The supremum of the truncations of a real, read in `ℝ≥0∞`. -/
theorem iSup_ofReal_min (x : ℝ) :
    (⨆ N : ℕ, ENNReal.ofReal (min x (N : ℝ))) = ENNReal.ofReal x := by
  refine le_antisymm (iSup_le fun N => ENNReal.ofReal_le_ofReal (min_le_left _ _)) ?_
  obtain ⟨N, hN⟩ := exists_nat_ge x
  exact le_iSup_of_le N (by rw [min_eq_left hN])

/-- **The truncated moments are the total of the densities**: the bounded tower applied to a
truncation, with the density kept on the exterior side. -/
theorem truncated_moment_eq (n : ℕ) {ψ : (Fin (n + 1) → ℝ) → ℝ} (hψm : Measurable ψ)
    (hψ0 : ∀ p, 0 ≤ ψ p) (N : ℕ) :
    ∫ p, min (ψ p) (N : ℝ) ∂shellLaw (n + 1)
      = ∫ y, shellDensity n (fun p => min (ψ p) (N : ℝ)) y ∂blockUnit := by
  have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
  refine (integral_shellDensity_eq n (fun p => min (ψ p) (N : ℝ)) (N : ℝ) hN ?_ ?_).symm
  · intro p
    have h0 : 0 ≤ min (ψ p) (N : ℝ) := le_min (hψ0 p) hN
    refine abs_le.mpr ⟨by linarith, by linarith [min_le_right (ψ p) (N : ℝ)]⟩
  · exact hψm.min measurable_const

/-- **The law-level `ℝ≥0∞` second moment of an affine function of the field**: the monotone
convergence of the truncated densities, read as an equality of Lebesgue integrals.  This is the
step that replaces the missing `L¹` extension of the tower. -/
theorem lintegral_shellLaw_sq (n : ℕ) (c d a b : ℝ) :
    ∫⁻ p, ENNReal.ofReal ((a * streamField c d n p + b) ^ 2) ∂shellLaw (n + 1)
      = ENNReal.ofReal (a ^ 2 * streamCovariance n c + (a * c ^ n * d) ^ 2 + b ^ 2) := by
  set ψ : (Fin (n + 1) → ℝ) → ℝ := fun p => (a * streamField c d n p + b) ^ 2 with hψ
  set Gf : ℝ → ℝ :=
    fun y => a ^ 2 * streamCovariance n c + (a * (c ^ n * d * y) + b) ^ 2 with hGf
  have hψ0 : ∀ p, 0 ≤ ψ p := fun p => sq_nonneg _
  have hψm : Measurable ψ := by
    rw [hψ]
    have hb : Measurable (fun p : Fin (n + 1) → ℝ => a * streamField c d n p + b) :=
      ((measurable_streamField c d n).const_mul a).add measurable_const
    simpa [pow_two] using hb.mul hb
  have hGf_int : Integrable Gf blockUnit := by
    have hcongr : Gf = fun y : ℝ =>
        a ^ 2 * streamCovariance n c + (a * c ^ n * d * y + b) ^ 2 := by
      rw [hGf]
      funext y
      ring
    rw [hcongr]
    exact (integrable_const _).add (integrable_poly_blockUnit (a * c ^ n * d) b)
  have hGf_val : ∫ y, Gf y ∂blockUnit
      = a ^ 2 * streamCovariance n c + (a * c ^ n * d) ^ 2 + b ^ 2 := by
    have hcongr : Gf = fun y : ℝ =>
        a ^ 2 * streamCovariance n c + (a * c ^ n * d * y + b) ^ 2 := by
      rw [hGf]
      funext y
      ring
    rw [hcongr, integral_add (integrable_const _) (integrable_poly_blockUnit (a * c ^ n * d) b),
      integral_sq_affine_const_blockUnit, integral_const, probReal_univ, one_smul]
    ring
  set u : ℕ → ℝ := fun N => ∫ p, min (ψ p) (N : ℝ) ∂shellLaw (n + 1) with hu
  have htrunc_int : ∀ N : ℕ, Integrable (fun p => min (ψ p) (N : ℝ)) (shellLaw (n + 1)) := by
    intro N
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    refine Integrable.of_bound (hψm.min measurable_const).aestronglyMeasurable (N : ℝ) ?_
    filter_upwards with p
    have h0 : 0 ≤ min (ψ p) (N : ℝ) := le_min (hψ0 p) hN
    refine abs_le.mpr ⟨by linarith, by linarith [min_le_right (ψ p) (N : ℝ)]⟩
  have hu_y : ∀ N : ℕ, u N
      = ∫ y, shellDensity n (fun p => min (ψ p) (N : ℝ)) y ∂blockUnit :=
    fun N => truncated_moment_eq n hψm hψ0 N
  have hconv_y : Tendsto (fun N : ℕ =>
      ∫ y, shellDensity n (fun p => min (ψ p) (N : ℝ)) y ∂blockUnit)
      atTop (𝓝 (∫ y, Gf y ∂blockUnit)) := by
    refine tendsto_integral_of_dominated_convergence Gf ?_ hGf_int ?_ ?_
    · intro N
      have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      refine (measurable_shellDensity n (N : ℝ) hN ?_
        (hψm.min measurable_const)).aestronglyMeasurable
      intro p
      have h0 : 0 ≤ min (ψ p) (N : ℝ) := le_min (hψ0 p) hN
      refine abs_le.mpr ⟨by linarith, by linarith [min_le_right (ψ p) (N : ℝ)]⟩
    · intro N
      filter_upwards with y
      have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
      have hnn : 0 ≤ shellDensity n (fun p => min (ψ p) (N : ℝ)) y :=
        shellDensity_nonneg n (fun p => le_min (hψ0 p) hN) y
      rw [Real.norm_of_nonneg hnn]
      have hval : shellDensity n (fun p => min (ψ p) (N : ℝ)) y
          = shellDensity n (fun p =>
              min ((a * streamField c d n p + b) ^ 2) (N : ℝ)) y := by rw [hψ]
      rw [hval]
      exact shellDensity_sq_min_le n c d y a b (N : ℝ) hN
    · filter_upwards with y
      have hfun : (fun N : ℕ => shellDensity n (fun p => min (ψ p) (N : ℝ)) y)
          = fun N : ℕ => shellDensity n (fun p =>
              min ((a * streamField c d n p + b) ^ 2) (N : ℝ)) y := by
        funext N
        rw [hψ]
      rw [hfun]
      exact tendsto_shellDensity_sq_min n c d y a b
  have hlim_u : Tendsto u atTop (𝓝 (∫ y, Gf y ∂blockUnit)) :=
    hconv_y.congr' (Eventually.of_forall fun N => (hu_y N).symm)
  have hu_mono : Monotone u := by
    refine monotone_nat_of_le_succ fun N => ?_
    have hN : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    have hle : (N : ℝ) ≤ ((N + 1 : ℕ) : ℝ) := by
      rw [Nat.cast_add_one]
      linarith
    refine integral_mono_of_nonneg
      (Eventually.of_forall fun p => le_min (hψ0 p) hN)
      (htrunc_int (N + 1))
      (Eventually.of_forall fun p => min_le_min (le_refl _) hle)
  have hchain : ∫⁻ p, ENNReal.ofReal (ψ p) ∂shellLaw (n + 1)
      = ⨆ N, ENNReal.ofReal (u N) := by
    have hfun : (fun p : Fin (n + 1) → ℝ => ENNReal.ofReal (ψ p))
        = fun p => ⨆ N : ℕ, ENNReal.ofReal (min (ψ p) (N : ℝ)) := by
      funext p
      exact (iSup_ofReal_min (ψ p)).symm
    rw [hfun]
    rw [lintegral_iSup
      (f := fun (N : ℕ) (p : Fin (n + 1) → ℝ) => ENNReal.ofReal (min (ψ p) (N : ℝ)))
      (fun N => ENNReal.measurable_ofReal.comp (hψm.min measurable_const))
      (monotone_nat_of_le_succ fun N p => ENNReal.ofReal_le_ofReal
        (min_le_min (le_refl _) (by exact_mod_cast Nat.le_succ N)))]
    exact iSup_congr fun N => (ofReal_integral_eq_lintegral_ofReal (htrunc_int N)
      (Eventually.of_forall fun p => le_min (hψ0 p) (Nat.cast_nonneg N))).symm
  have hsupV : (⨆ N, ENNReal.ofReal (u N)) = ENNReal.ofReal (∫ y, Gf y ∂blockUnit) :=
    ofReal_iSup_of_tendsto hu_mono hlim_u
  have hchain' : ∫⁻ p, ENNReal.ofReal ((a * streamField c d n p + b) ^ 2)
        ∂shellLaw (n + 1) = ⨆ N, ENNReal.ofReal (u N) := by
    rw [← hchain, hψ]
  rw [hchain', hsupV, hGf_val]

/-- **The second moment is finite**: the affine image of the reference field is square-integrable
under the reference law at every scale.  This is the `L¹` fact the density identity could not
supply. -/
theorem integrable_sq_affine (n : ℕ) (c d a b : ℝ) :
    Integrable (fun p => (a * streamField c d n p + b) ^ 2) (shellLaw (n + 1)) := by
  have hψm : Measurable (fun p : Fin (n + 1) → ℝ => (a * streamField c d n p + b) ^ 2) := by
    have hb : Measurable (fun p : Fin (n + 1) → ℝ => a * streamField c d n p + b) :=
      ((measurable_streamField c d n).const_mul a).add measurable_const
    simpa [pow_two] using hb.mul hb
  refine ⟨hψm.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun p => sq_nonneg _)]
  rw [lintegral_shellLaw_sq]
  exact ENNReal.ofReal_lt_top

/-- **The moment identity at the law level**: the second moment of an affine function of the
`n`-scale reference field, under the reference law of `n + 1` coordinates, is the accumulated
covariance plus the square of the drift.  This is the law-level statement the density identity
`shellDensity_quadratic` could not make: an honest integral against a probability measure,
obtained by driving the bounded tower to its limit along truncations. -/
theorem integral_shellLaw_sq (n : ℕ) (c d a b : ℝ) :
    ∫ p, (a * streamField c d n p + b) ^ 2 ∂shellLaw (n + 1)
      = a ^ 2 * streamCovariance n c + (a * c ^ n * d) ^ 2 + b ^ 2 := by
  have hψm : Measurable (fun p : Fin (n + 1) → ℝ => (a * streamField c d n p + b) ^ 2) := by
    have hb : Measurable (fun p : Fin (n + 1) → ℝ => a * streamField c d n p + b) :=
      ((measurable_streamField c d n).const_mul a).add measurable_const
    simpa [pow_two] using hb.mul hb
  have hofReal : ENNReal.ofReal (∫ p, (a * streamField c d n p + b) ^ 2 ∂shellLaw (n + 1))
      = ENNReal.ofReal (a ^ 2 * streamCovariance n c + (a * c ^ n * d) ^ 2 + b ^ 2) := by
    rw [ofReal_integral_eq_lintegral_ofReal (integrable_sq_affine n c d a b)
      (Eventually.of_forall fun p => sq_nonneg _), lintegral_shellLaw_sq]
  have hnonneg : 0 ≤ ∫ p, (a * streamField c d n p + b) ^ 2 ∂shellLaw (n + 1) :=
    integral_nonneg fun p => sq_nonneg _
  have hR : 0 ≤ a ^ 2 * streamCovariance n c + (a * c ^ n * d) ^ 2 + b ^ 2 := by
    exact add_nonneg (add_nonneg (mul_nonneg (sq_nonneg a) (streamCovariance_nonneg n c))
      (sq_nonneg _)) (sq_nonneg b)
  have h := congrArg ENNReal.toReal hofReal
  rwa [ENNReal.toReal_ofReal hnonneg, ENNReal.toReal_ofReal hR] at h

/-- The field itself is integrable under the reference law: it is dominated by its square. -/
theorem integrable_streamField (n : ℕ) (c d : ℝ) :
    Integrable (fun p => streamField c d n p) (shellLaw (n + 1)) := by
  have hsq : Integrable (fun p => (streamField c d n p) ^ 2) (shellLaw (n + 1)) := by
    simpa using integrable_sq_affine n c d 1 0
  have hdom : Integrable (fun p => (streamField c d n p) ^ 2 / 2 + 1 / 2)
      (shellLaw (n + 1)) :=
    (hsq.div_const 2).add (integrable_const (1 / 2))
  refine Integrable.mono' hdom (measurable_streamField c d n).aestronglyMeasurable ?_
  filter_upwards with p
  have h : |streamField c d n p| ≤ (streamField c d n p) ^ 2 / 2 + 1 / 2 := by
    have h1 : 0 ≤ (|streamField c d n p| - 1) ^ 2 := sq_nonneg _
    have h2 : |streamField c d n p| ^ 2 = (streamField c d n p) ^ 2 := sq_abs _
    nlinarith [abs_nonneg (streamField c d n p)]
  simpa [Real.norm_eq_abs] using h

/-- **The mean of the reference field is zero**: with the exterior coordinate also averaged, the
drift is symmetric and cancels.  This is the first honest expectation under the reference law. -/
theorem integral_shellLaw_streamField (n : ℕ) (c d : ℝ) :
    ∫ p, streamField c d n p ∂shellLaw (n + 1) = 0 := by
  have hS : Integrable (fun p => streamField c d n p) (shellLaw (n + 1)) :=
    integrable_streamField n c d
  have hS2 : Integrable (fun p => (streamField c d n p) ^ 2) (shellLaw (n + 1)) := by
    simpa using integrable_sq_affine n c d 1 0
  have hsq : ∫ p, (streamField c d n p) ^ 2 ∂shellLaw (n + 1)
      = streamCovariance n c + (c ^ n * d) ^ 2 := by
    have h := integral_shellLaw_sq n c d 1 0
    simpa using h
  have hshift : ∫ p, (streamField c d n p - 1) ^ 2 ∂shellLaw (n + 1)
      = streamCovariance n c + (c ^ n * d) ^ 2 + 1 := by
    have h := integral_shellLaw_sq n c d 1 (-1)
    simpa using h
  have hexp : ∫ p, (streamField c d n p - 1) ^ 2 ∂shellLaw (n + 1)
      = ∫ p, (streamField c d n p) ^ 2 ∂shellLaw (n + 1)
        - 2 * ∫ p, streamField c d n p ∂shellLaw (n + 1) + 1 := by
    have hfun : (fun p : Fin (n + 1) → ℝ => (streamField c d n p - 1) ^ 2)
        = fun p => (streamField c d n p) ^ 2 - (2 * streamField c d n p - 1) := by
      funext p
      ring
    have h2 : Integrable (fun p : Fin (n + 1) → ℝ => 2 * streamField c d n p - 1)
        (shellLaw (n + 1)) := (hS.const_mul 2).sub (integrable_const 1)
    rw [hfun, integral_sub hS2 h2]
    have h3 : ∫ p, (2 * streamField c d n p - 1) ∂shellLaw (n + 1)
        = 2 * ∫ p, streamField c d n p ∂shellLaw (n + 1) - 1 := by
      rw [integral_sub (hS.const_mul 2) (integrable_const 1), integral_const_mul,
        integral_const, probReal_univ, one_smul]
    rw [h3]
    ring
  rw [hexp, hsq] at hshift
  linarith

/-- **The variance of the reference field**: the second central moment under the reference law is
the accumulated covariance plus the doubled-drift term. -/
theorem integral_shellLaw_centered_sq (n : ℕ) (c d : ℝ) :
    ∫ p, (streamField c d n p - ∫ q, streamField c d n q ∂shellLaw (n + 1)) ^ 2
        ∂shellLaw (n + 1)
      = streamCovariance n c + (c ^ n * d) ^ 2 := by
  have hmean := integral_shellLaw_streamField n c d
  have hfun : (fun p : Fin (n + 1) → ℝ =>
        (streamField c d n p - ∫ q, streamField c d n q ∂shellLaw (n + 1)) ^ 2)
      = fun p => (streamField c d n p) ^ 2 := by
    funext p
    rw [hmean]
    ring
  rw [hfun]
  have h := integral_shellLaw_sq n c d 1 0
  simpa using h

/-- **The law-level variance is uniformly bounded in the number of scales**: for a contracting
per-scale weight the variance of the reference field never exceeds `1/(1 − c²) + d²`. -/
theorem variance_shellLaw_le (n : ℕ) (c d : ℝ) (hc : c ^ 2 < 1) :
    ∫ p, (streamField c d n p - ∫ q, streamField c d n q ∂shellLaw (n + 1)) ^ 2
        ∂shellLaw (n + 1)
      ≤ 1 / (1 - c ^ 2) + d ^ 2 := by
  rw [integral_shellLaw_centered_sq]
  have hK : streamCovariance n c ≤ 1 / (1 - c ^ 2) := streamCovariance_le_inv n c hc
  have hpow : (c ^ n) ^ 2 ≤ 1 := by
    have h : (c ^ 2) ^ n ≤ 1 := pow_le_one₀ (sq_nonneg c) (le_of_lt hc)
    have he : (c ^ n) ^ 2 = (c ^ 2) ^ n := by
      rw [← pow_mul, ← pow_mul, mul_comm]
    rwa [he]
  have hdrift : (c ^ n * d) ^ 2 ≤ d ^ 2 := by
    rw [mul_pow]
    exact mul_le_of_le_one_left (sq_nonneg d) hpow
  linarith

/-! ## The two-point functions of the reference law

The reference law is a product of independent unit Gaussians, so single coordinates have mean
`0` and unit second moment, and the cylinder field's covariance with the exterior coordinate is
explicit: `E[S_n · p_last] = c^n·d`.  That covariance is what the renormalised observable
subtracts, so the renormalised field is orthogonal to its own drift coordinate and its variance is
exactly `K_n`.

These are computed by Fubini for *integrable* functions (`integral_shellLaw_cons_succ`), which is
stronger than the truncation standard the total moment identity needed: the integrands here are
dominated by `(S_n² + p_last²)/2`, and both factors are known to lie in `L²`.
-/

/-- A coordinate has mean zero under the reference law. -/
theorem integral_shellLaw_coord (m : ℕ) (i : Fin m) :
    ∫ p, p i ∂shellLaw m = 0 := by
  have hz : ∫ z, z ∂blockUnit = 0 := by
    have := integral_quadratic_blockUnit 0 1 0
    simpa using this
  have h := MeasureTheory.integral_comp_eval (μ := fun _ : Fin m => blockUnit) (i := i)
    (f := fun z : ℝ => z) measurable_id.aestronglyMeasurable
  rw [show (∫ p : Fin m → ℝ, p i ∂shellLaw m) = ∫ z, z ∂blockUnit from h, hz]

/-- A coordinate is integrable under the reference law. -/
theorem integrable_shellLaw_coord (m : ℕ) (i : Fin m) :
    Integrable (fun p : Fin m → ℝ => p i) (shellLaw m) := by
  have hz : Integrable (fun z : ℝ => z) blockUnit :=
    (memLp_id_gaussianReal (μ := 0) (v := 1) 2).integrable (by norm_num)
  have h := MeasureTheory.integrable_comp_eval (μ := fun _ : Fin m => blockUnit) (i := i) hz
  simpa only [shellLaw] using h

/-- A coordinate square is integrable under the reference law. -/
theorem integrable_shellLaw_coord_sq (m : ℕ) (i : Fin m) :
    Integrable (fun p : Fin m → ℝ => (p i) ^ 2) (shellLaw m) := by
  have hz : Integrable (fun z : ℝ => z ^ 2) blockUnit :=
    MemLp.integrable_sq (memLp_id_gaussianReal (μ := 0) (v := 1) 2)
  have h := MeasureTheory.integrable_comp_eval (μ := fun _ : Fin m => blockUnit) (i := i) hz
  simpa only [shellLaw] using h

/-- A coordinate square has unit integral: the reference coordinates are unit variance. -/
theorem integral_shellLaw_coord_sq (m : ℕ) (i : Fin m) :
    ∫ p, (p i) ^ 2 ∂shellLaw m = 1 := by
  have hz : ∫ z, z ^ 2 ∂blockUnit = 1 := by
    have := integral_quadratic_blockUnit 0 0 1
    simpa using this
  have h := MeasureTheory.integral_comp_eval (μ := fun _ : Fin m => blockUnit) (i := i)
    (f := fun z : ℝ => z ^ 2) (measurable_id.pow_const 2).aestronglyMeasurable
  rw [show (∫ p : Fin m → ℝ, (p i) ^ 2 ∂shellLaw m) = ∫ z, z ^ 2 ∂blockUnit from h, hz]

/-- The field times the exterior coordinate is integrable: both factors lie in `L²`, so the
product is dominated by half the sum of their squares. -/
theorem integrable_streamField_mul_last (n : ℕ) (c d : ℝ) :
    Integrable (fun p : Fin (n + 1) → ℝ => streamField c d n p * p (Fin.last n))
      (shellLaw (n + 1)) := by
  have hsq : Integrable (fun p : Fin (n + 1) → ℝ => (streamField c d n p) ^ 2)
      (shellLaw (n + 1)) := by
    simpa using integrable_sq_affine n c d 1 0
  have hlast : Integrable (fun p : Fin (n + 1) → ℝ => (p (Fin.last n)) ^ 2)
      (shellLaw (n + 1)) := integrable_shellLaw_coord_sq (n + 1) (Fin.last n)
  refine Integrable.mono' ((hsq.add hlast).div_const 2)
    ((measurable_streamField c d n).mul (measurable_pi_apply (Fin.last n))).aestronglyMeasurable ?_
  filter_upwards with p
  have h1 : |streamField c d n p * p (Fin.last n)|
      ≤ ((streamField c d n p) ^ 2 + (p (Fin.last n)) ^ 2) / 2 := by
    have h2 : 0 ≤ (|streamField c d n p| - |p (Fin.last n)|) ^ 2 := sq_nonneg _
    rw [abs_mul]
    nlinarith [abs_nonneg (streamField c d n p), abs_nonneg (p (Fin.last n)),
      sq_abs (streamField c d n p), sq_abs (p (Fin.last n))]
  simpa [Real.norm_eq_abs] using h1

/-- **The two-point correlation of the field with the exterior coordinate.**  The field at `n`
scales, paired with the drift coordinate `p_last`, has expectation exactly the running drift
`c^n·d`: under the product law only that coordinate carries the drift, and it is the one the field
weights by `c^n·d`. -/
theorem integral_shellLaw_streamField_mul_last (n : ℕ) (c d : ℝ) :
    ∫ p, streamField c d n p * p (Fin.last n) ∂shellLaw (n + 1) = c ^ n * d := by
  induction n with
  | zero =>
      have hfun : (fun p : Fin 1 → ℝ => streamField c d 0 p * p (Fin.last 0))
          = fun p => d * (p 0) ^ 2 := by
        funext p
        simp [streamField]
        ring
      have hz : ∫ z, d * z ^ 2 ∂blockUnit = d := by
        have := integral_quadratic_blockUnit 0 0 d
        simpa using this
      have h := MeasureTheory.integral_comp_eval (μ := fun _ : Fin 1 => blockUnit)
        (i := (0 : Fin 1)) (f := fun z : ℝ => d * z ^ 2)
        ((measurable_const.mul (measurable_id.pow_const 2))).aestronglyMeasurable
      rw [hfun, show (∫ p : (Fin 1 → ℝ), d * (p 0) ^ 2 ∂shellLaw 1)
        = ∫ z, d * z ^ 2 ∂blockUnit from h, hz]
      simp
  | succ n ih =>
      have hF : Integrable (fun p : Fin (n + 2) → ℝ =>
          streamField c d (n + 1) p * p (Fin.last (n + 1))) (shellLaw (n + 2)) :=
        integrable_streamField_mul_last (n + 1) c d
      rw [integral_shellLaw_cons_succ (n + 1) _ hF]
      have hA : ∫ g : (Fin (n + 1) → ℝ), g (Fin.last n) ∂shellLaw (n + 1) = 0 :=
        integral_shellLaw_coord (n + 1) (Fin.last n)
      have hinner : ∀ z : ℝ, ∫ g : (Fin (n + 1) → ℝ),
          streamField c d (n + 1) (Fin.cons z g)
                * (Fin.cons z g : Fin (n + 2) → ℝ) (Fin.last (n + 1))
            ∂shellLaw (n + 1) = z * 0 + c * (c ^ n * d) := by
        intro z
        have hfun : (fun g : Fin (n + 1) → ℝ =>
            streamField c d (n + 1) (Fin.cons z g)
                * (Fin.cons z g : Fin (n + 2) → ℝ) (Fin.last (n + 1)))
            = fun g => g (Fin.last n) * z + c * (streamField c d n g * g (Fin.last n)) := by
          funext g
          have hlast : (Fin.cons z g : Fin (n + 2) → ℝ) (Fin.last (n + 1)) = g (Fin.last n) := by
            simp
          rw [streamField_cons, hlast]
          ring
        rw [hfun]
        have h1 : Integrable (fun g : Fin (n + 1) → ℝ => g (Fin.last n) * z)
            (shellLaw (n + 1)) :=
          (integrable_shellLaw_coord (n + 1) (Fin.last n)).mul_const z
        have h2 : Integrable (fun g : Fin (n + 1) → ℝ =>
            c * (streamField c d n g * g (Fin.last n))) (shellLaw (n + 1)) :=
          (integrable_streamField_mul_last n c d).const_mul c
        rw [integral_add h1 h2, integral_mul_const, hA, integral_const_mul, ih]
        ring
      have houter : (fun z : ℝ => ∫ g : (Fin (n + 1) → ℝ),
          streamField c d (n + 1) (Fin.cons z g)
                * (Fin.cons z g : Fin (n + 2) → ℝ) (Fin.last (n + 1))
            ∂shellLaw (n + 1)) = fun _ => c * (c ^ n * d) := by
        funext z
        rw [hinner z]
        ring
      rw [houter]
      have hone : ∫ _ : ℝ, c * (c ^ n * d) ∂blockUnit = c * (c ^ n * d) := by
        have := integral_quadratic_blockUnit (c * (c ^ n * d)) 0 0
        simpa using this
      rw [hone, pow_succ']
      ring

/-- The renormalised observable has mean zero under the reference law. -/
theorem integral_shellLaw_renormField (n : ℕ) (c d : ℝ) :
    ∫ p, renormField c d n p ∂shellLaw (n + 1) = 0 := by
  have hS := integral_shellLaw_streamField n c d
  have hlast := integral_shellLaw_coord (n + 1) (Fin.last n)
  have hfun : (fun p : Fin (n + 1) → ℝ => renormField c d n p)
      = fun p => streamField c d n p - (c ^ n * d) * p (Fin.last n) := by
    funext p
    rw [renormField]
  have h2 : Integrable (fun p : Fin (n + 1) → ℝ => (c ^ n * d) * p (Fin.last n))
      (shellLaw (n + 1)) :=
    (integrable_shellLaw_coord (n + 1) (Fin.last n)).const_mul (c ^ n * d)
  rw [hfun, integral_sub (integrable_streamField n c d) h2, integral_const_mul, hS, hlast]
  ring

/-- **The renormalised observable is orthogonal to its own drift coordinate.**  This is the
two-point identity the variance needs: the drift the renormalisation subtracts is exactly the
correlation the field has with the exterior coordinate, so nothing of it is left. -/
theorem integral_shellLaw_renormField_mul_last (n : ℕ) (c d : ℝ) :
    ∫ p, renormField c d n p * p (Fin.last n) ∂shellLaw (n + 1) = 0 := by
  have hcross := integral_shellLaw_streamField_mul_last n c d
  have hlast := integral_shellLaw_coord_sq (n + 1) (Fin.last n)
  have hfun : (fun p : Fin (n + 1) → ℝ => renormField c d n p * p (Fin.last n))
      = fun p => streamField c d n p * p (Fin.last n)
          - (c ^ n * d) * (p (Fin.last n)) ^ 2 := by
    funext p
    rw [renormField]
    ring
  have h2 : Integrable (fun p : Fin (n + 1) → ℝ => (c ^ n * d) * (p (Fin.last n)) ^ 2)
      (shellLaw (n + 1)) :=
    (integrable_shellLaw_coord_sq (n + 1) (Fin.last n)).const_mul (c ^ n * d)
  rw [hfun, integral_sub (integrable_streamField_mul_last n c d) h2, integral_const_mul,
    hcross, hlast]
  ring

/-- **The variance of the renormalised observable is exactly the accumulated covariance** `K_n`:
the drift is gone, and what remains is the sum of the `n` interior variances. -/
theorem integral_shellLaw_renormField_sq (n : ℕ) (c d : ℝ) :
    ∫ p, (renormField c d n p) ^ 2 ∂shellLaw (n + 1) = streamCovariance n c := by
  have hS2 : ∫ p, (streamField c d n p) ^ 2 ∂shellLaw (n + 1)
      = streamCovariance n c + (c ^ n * d) ^ 2 := by
    have h := integral_shellLaw_sq n c d 1 0
    simpa using h
  have hcross := integral_shellLaw_streamField_mul_last n c d
  have hlast := integral_shellLaw_coord_sq (n + 1) (Fin.last n)
  have hfun : (fun p : Fin (n + 1) → ℝ => (renormField c d n p) ^ 2)
      = fun p => (streamField c d n p) ^ 2
          - 2 * (c ^ n * d) * (streamField c d n p * p (Fin.last n))
          + (c ^ n * d) ^ 2 * (p (Fin.last n)) ^ 2 := by
    funext p
    rw [renormField]
    ring
  have hA : Integrable (fun p : Fin (n + 1) → ℝ => (streamField c d n p) ^ 2)
      (shellLaw (n + 1)) := by
    simpa using integrable_sq_affine n c d 1 0
  have hB : Integrable (fun p : Fin (n + 1) → ℝ =>
      2 * (c ^ n * d) * (streamField c d n p * p (Fin.last n))) (shellLaw (n + 1)) :=
    (integrable_streamField_mul_last n c d).const_mul (2 * (c ^ n * d))
  have hC : Integrable (fun p : Fin (n + 1) → ℝ => (c ^ n * d) ^ 2 * (p (Fin.last n)) ^ 2)
      (shellLaw (n + 1)) :=
    (integrable_shellLaw_coord_sq (n + 1) (Fin.last n)).const_mul ((c ^ n * d) ^ 2)
  have hX : Integrable (fun p : Fin (n + 1) → ℝ => (streamField c d n p) ^ 2
      - 2 * (c ^ n * d) * (streamField c d n p * p (Fin.last n))) (shellLaw (n + 1)) :=
    hA.sub hB
  rw [hfun, integral_add hX hC, integral_sub hA hB, integral_const_mul, integral_const_mul,
    hS2, hcross, hlast]
  ring

/-- The mean-subtracted second moment of the renormalised observable, in the form a variance is
usually quoted in. -/
theorem integral_shellLaw_renormField_centered_sq (n : ℕ) (c d : ℝ) :
    ∫ p, (renormField c d n p - ∫ q, renormField c d n q ∂shellLaw (n + 1)) ^ 2
        ∂shellLaw (n + 1) = streamCovariance n c := by
  have hmean := integral_shellLaw_renormField n c d
  have hfun : (fun p : Fin (n + 1) → ℝ =>
        (renormField c d n p - ∫ q, renormField c d n q ∂shellLaw (n + 1)) ^ 2)
      = fun p => (renormField c d n p) ^ 2 := by
    funext p
    rw [hmean]
    ring
  rw [hfun, integral_shellLaw_renormField_sq]

/-- **The variance of the renormalised observable is bounded uniformly in the number of scales**:
for a contracting weight it never exceeds `1/(1 − c²)`, with no drift term at all. -/
theorem variance_renormField_le (n : ℕ) (c d : ℝ) (hc : c ^ 2 < 1) :
    ∫ p, (renormField c d n p - ∫ q, renormField c d n q ∂shellLaw (n + 1)) ^ 2
        ∂shellLaw (n + 1) ≤ 1 / (1 - c ^ 2) := by
  rw [integral_shellLaw_renormField_centered_sq]
  exact streamCovariance_le_inv n c hc

/-- **The two-point function of the reference law, packaged.**  For `k = c^n·d` the pair
`(streamField, p_last)` has the covariance matrix `[[K_n + k², k], [k, 1]]`, and the renormalised
field's pair with `p_last` has zero off-diagonal and variance `K_n`. -/
theorem covariance_pair_shellLaw (n : ℕ) (c d : ℝ) :
    (∫ p, streamField c d n p * p (Fin.last n) ∂shellLaw (n + 1) = c ^ n * d)
      ∧ (∫ p, (p (Fin.last n)) ^ 2 ∂shellLaw (n + 1) = 1)
      ∧ (∫ p, renormField c d n p * p (Fin.last n) ∂shellLaw (n + 1) = 0)
      ∧ (∫ p, (renormField c d n p) ^ 2 ∂shellLaw (n + 1) = streamCovariance n c) :=
  ⟨integral_shellLaw_streamField_mul_last n c d, integral_shellLaw_coord_sq (n + 1) (Fin.last n),
    integral_shellLaw_renormField_mul_last n c d, integral_shellLaw_renormField_sq n c d⟩

/-- The product of two coordinates is integrable under the reference law. -/
theorem integrable_shellLaw_coord_mul (m : ℕ) (i j : Fin m) :
    Integrable (fun p : Fin m → ℝ => p i * p j) (shellLaw m) := by
  have hdom : Integrable (fun p : Fin m → ℝ => ((p i) ^ 2 + (p j) ^ 2) / 2) (shellLaw m) := by
    simpa using Integrable.div_const ((integrable_shellLaw_coord_sq m i).add
      (integrable_shellLaw_coord_sq m j)) 2
  refine Integrable.mono' hdom
    ((by fun_prop : Measurable fun p : Fin m → ℝ => p i * p j)).aestronglyMeasurable ?_
  filter_upwards with p
  have h1 : |p i * p j| ≤ ((p i) ^ 2 + (p j) ^ 2) / 2 := by
    have h2 : 0 ≤ (|p i| - |p j|) ^ 2 := sq_nonneg _
    rw [abs_mul]
    nlinarith [abs_nonneg (p i), abs_nonneg (p j), sq_abs (p i), sq_abs (p j)]
  simpa [Real.norm_eq_abs] using h1

/-- **The interior cross moments of the reference law**: distinct coordinates are uncorrelated and a
coordinate has second moment `1`.  Proved by splitting the product law at the first coordinate: the
newest coordinate multiplies either itself (one unit of variance) or a distinct coordinate (zero),
and the induction hypothesis carries the product of the two older coordinates. -/
theorem integral_shellLaw_coord_mul_coord (m : ℕ) (i j : Fin m) :
    ∫ p, p i * p j ∂shellLaw m = if i = j then 1 else 0 := by
  induction m with
  | zero => exact i.elim0
  | succ n ih =>
      rw [integral_shellLaw_cons_succ n _ (integrable_shellLaw_coord_mul (n + 1) i j)]
      refine Fin.cases ?_ ?_ i
      · refine Fin.cases ?_ ?_ j
        · have hz : (fun z : ℝ => ∫ g : (Fin n → ℝ), (Fin.cons z g : Fin (n + 1) → ℝ) 0
              * (Fin.cons z g : Fin (n + 1) → ℝ) 0 ∂shellLaw n) = fun z => z * z := by
            funext z
            simp
          have hzz : ∫ z : ℝ, z * z ∂blockUnit = 1 := by
            have := integral_quadratic_blockUnit 0 0 1
            simpa [pow_two] using this
          rw [hz, hzz]
          simp
        · intro j
          have hz : (fun z : ℝ => ∫ g : (Fin n → ℝ), (Fin.cons z g : Fin (n + 1) → ℝ) 0
              * (Fin.cons z g : Fin (n + 1) → ℝ) (Fin.succ j) ∂shellLaw n) = fun _ => 0 := by
            funext z
            simp only [Fin.cons_zero, Fin.cons_succ]
            rw [integral_const_mul, integral_shellLaw_coord n j, mul_zero]
          rw [hz, if_neg (Ne.symm (Fin.succ_ne_zero j))]
          simp
      · intro i
        refine Fin.cases ?_ ?_ j
        · have hz : (fun z : ℝ => ∫ g : (Fin n → ℝ),
              (Fin.cons z g : Fin (n + 1) → ℝ) (Fin.succ i)
              * (Fin.cons z g : Fin (n + 1) → ℝ) 0 ∂shellLaw n) = fun _ => 0 := by
            funext z
            simp only [Fin.cons_zero, Fin.cons_succ]
            rw [integral_mul_const, integral_shellLaw_coord n i, zero_mul]
          rw [hz, if_neg (Fin.succ_ne_zero i)]
          simp
        · intro j
          have hz : (fun z : ℝ => ∫ g : (Fin n → ℝ),
              (Fin.cons z g : Fin (n + 1) → ℝ) (Fin.succ i)
              * (Fin.cons z g : Fin (n + 1) → ℝ) (Fin.succ j) ∂shellLaw n)
              = fun _ => (if i = j then (1 : ℝ) else 0) := by
            funext z
            simp only [Fin.cons_succ]
            exact ih i j
          rw [hz]
          have hc : ∫ _ : ℝ, (if i = j then (1 : ℝ) else 0) ∂blockUnit
              = (if i = j then (1 : ℝ) else 0) := by
            rw [integral_const, probReal_univ, one_smul]
          rw [hc]
          by_cases h : i = j
          · subst h
            simp
          · have hne : (Fin.succ i : Fin (n + 1)) ≠ Fin.succ j :=
              fun hs => h (Fin.succ_inj.mp hs)
            simp [h, hne]

/-- **The coefficient vector of the cylinder field**: `c^j` on the interior coordinates and the
running drift `c^n·d` on the exterior one. -/
noncomputable def streamCoeff (c d : ℝ) (n : ℕ) : Fin (n + 1) → ℝ :=
  fun i => if i = Fin.last n then c ^ n * d else c ^ (i : ℕ)

/-- The field is the linear statistic with coefficient vector `streamCoeff`. -/
theorem streamField_eq_sum_coeff (n : ℕ) (c d : ℝ) (f : Fin (n + 1) → ℝ) :
    streamField c d n f = ∑ i, streamCoeff c d n i * f i := by
  induction n with
  | zero =>
      simp [streamField, streamCoeff]
  | succ n ih =>
      have h0 : streamCoeff c d (n + 1) 0 = 1 := by
        simp [streamCoeff, Fin.succ_ne_zero]
      have hs : ∀ i : Fin (n + 1),
          streamCoeff c d (n + 1) i.succ = c * streamCoeff c d n i := by
        intro i
        by_cases h : i = Fin.last n
        · subst h
          simp [streamCoeff, pow_succ']
          ring
        · have hne : (Fin.succ i : Fin (n + 1 + 1)) ≠ Fin.last (n + 1) := by
            intro hs'
            exact h (Fin.succ_inj.mp hs')
          simp only [streamCoeff, if_neg h, if_neg hne, Fin.val_succ]
          rw [pow_succ']
      rw [streamField_succ, ih (fun i => f i.succ)]
      conv_rhs => rw [Fin.sum_univ_succ]
      have hsum : (∑ i : Fin (n + 1), streamCoeff c d (n + 1) i.succ * f i.succ)
          = c * ∑ i : Fin (n + 1), streamCoeff c d n i * f i.succ := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl (fun i _ => ?_)
        rw [hs i]
        ring
      rw [hsum, h0]
      ring

/-- **The two-point kernel against a coordinate**: a linear statistic pairs with coordinate `j` by
its `j`-th coefficient. -/
theorem integral_shellLaw_linear_mul_coord (m : ℕ) (w : Fin m → ℝ) (j : Fin m) :
    ∫ p, (∑ i, w i * p i) * p j ∂shellLaw m = w j := by
  have hfun : (fun p : Fin m → ℝ => (∑ i, w i * p i) * p j)
      = fun p => ∑ i, (w i) * (p i * p j) := by
    funext p
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl (fun i _ => ?_)
    ring
  rw [hfun]
  rw [integral_finset_sum _ (fun i _ => (integrable_shellLaw_coord_mul m i j).const_mul (w i))]
  simp only [integral_const_mul, integral_shellLaw_coord_mul_coord, mul_ite, mul_one, mul_zero]
  simp

/-- **The full two-point kernel of linear statistics**: two linear statistics pair by the inner
product of their coefficient vectors. -/
theorem integral_shellLaw_linear_mul_linear (m : ℕ) (w v : Fin m → ℝ) :
    ∫ p, (∑ i, w i * p i) * (∑ j, v j * p j) ∂shellLaw m = ∑ i, w i * v i := by
  have hfun : (fun p : Fin m → ℝ => (∑ i, w i * p i) * (∑ j, v j * p j))
      = fun p => ∑ i, ∑ j, (w i * v j) * (p i * p j) := by
    funext p
    rw [Finset.sum_mul_sum]
    refine Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j _ => ?_))
    ring
  have hinner : ∀ i : Fin m, Integrable
      (fun p : Fin m → ℝ => ∑ j, (w i * v j) * (p i * p j)) (shellLaw m) :=
    fun i => integrable_finset_sum _ (fun j _ =>
      (integrable_shellLaw_coord_mul m i j).const_mul (w i * v j))
  rw [hfun, integral_finset_sum _ (fun i _ => hinner i)]
  have hterm : ∀ i : Fin m, ∫ p, (∑ j, (w i * v j) * (p i * p j)) ∂shellLaw m
      = w i * v i := by
    intro i
    rw [integral_finset_sum _ (fun j _ =>
      (integrable_shellLaw_coord_mul m i j).const_mul (w i * v j))]
    simp only [integral_const_mul, integral_shellLaw_coord_mul_coord, mul_ite, mul_one, mul_zero]
    simp
  simp only [hterm]

/-- **The field's two-point kernel against any linear statistic**: it pairs with the statistic by
the inner product of `streamCoeff` with that statistic's coefficient vector.  This is the form the
cross-scale covariance is read off from. -/
theorem integral_shellLaw_streamField_mul_linear (n : ℕ) (c d : ℝ) (w : Fin (n + 1) → ℝ) :
    ∫ p, streamField c d n p * (∑ i, w i * p i) ∂shellLaw (n + 1)
      = ∑ i, streamCoeff c d n i * w i := by
  have hfun : (fun p : Fin (n + 1) → ℝ =>
        streamField c d n p * (∑ i, w i * p i))
      = fun p => (∑ i, streamCoeff c d n i * p i) * (∑ i, w i * p i) := by
    funext p
    rw [streamField_eq_sum_coeff]
  rw [hfun, integral_shellLaw_linear_mul_linear]

/-! ## The cross-scale covariance, and every coordinate moment at once

The kernel of the previous section pairs the field at `n` scales with a linear statistic of the
same `n + 1` coordinates.  Two further readings of the reference law are available.

**Cross-scale pairing.**  A field of `m < n` scales is a statistic of the first `m + 1`
coordinates, so it enters the `n`-scale space by reading the extra coordinates with weight `0`
(`truncCoeff`).  The covariance is then an inner product in which the smaller field's exterior
coefficient `c^m·d` meets the *interior* coefficient `c^m` of the larger one, which is why the
answer is `K_m + c^(2m)·d` — not `K_m + (c^m d)²`, the smaller field's own second moment.  The
difference is exactly the drift the larger field assigns to the coordinate the smaller one
treats as its own exterior background.

**All coordinate moments.**  The reference law is a product, and `integral_fintype_prod_eq_prod`
says a product of one-variable functions integrates to the product of the one-variable integrals.
Applied to `∏ i, (p i)^(e i)` this computes *every* coordinate moment of the law at once; the
four-point function is the case in which the exponent vector `e` is supported on four indices, and
the Wick form of it is then a one-dimensional multiplicity computation rather than an integral.
-/

/-- **The lift of a coefficient vector along `Fin.castLE`**: a statistic of `m + 1` coordinates
becomes a statistic of `n + 1 ≥ m + 1` coordinates by reading the extra coordinates with weight
`0`. -/
noncomputable def truncCoeff {m n : ℕ} (v : Fin (m + 1) → ℝ) (_h : m ≤ n) :
    Fin (n + 1) → ℝ :=
  fun i => if hi : (i : ℕ) ≤ m then v ⟨i, Nat.lt_succ_of_le hi⟩ else 0

/-- The lift does nothing on the coordinates it came from. -/
theorem truncCoeff_castLE {m n : ℕ} (v : Fin (m + 1) → ℝ) (h : m ≤ n) (i : Fin (m + 1)) :
    truncCoeff v h (Fin.castLE (Nat.succ_le_succ h) i) = v i := by
  have hi : ((Fin.castLE (Nat.succ_le_succ h) i : Fin (n + 1)) : ℕ) ≤ m :=
    Nat.le_of_lt_succ i.isLt
  simp only [truncCoeff, hi, dif_pos]
  exact congrArg v (Fin.ext rfl)

/-- **The lifted sum is the smaller sum**: pairing a statistic of the big space with the lift of a
coefficient vector reads off the small space. -/
theorem sum_truncCoeff_mul {m n : ℕ} (v : Fin (m + 1) → ℝ) (h : m ≤ n)
    (g : Fin (n + 1) → ℝ) :
    (∑ i : Fin (n + 1), truncCoeff v h i * g i)
      = ∑ i : Fin (m + 1), v i * g (Fin.castLE (Nat.succ_le_succ h) i) := by
  have hfilter : (Finset.univ.filter (fun i : Fin (n + 1) => (i : ℕ) ≤ m))
      = Finset.univ.image (Fin.castLE (Nat.succ_le_succ h)) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro hi
      exact ⟨⟨i, Nat.lt_succ_of_le hi⟩, Fin.ext rfl⟩
    · rintro ⟨j, -, rfl⟩
      exact Nat.le_of_lt_succ j.isLt
  have hsplit : (∑ i : Fin (n + 1), truncCoeff v h i * g i)
      = (Finset.univ.filter (fun i : Fin (n + 1) => (i : ℕ) ≤ m)).sum
          (fun i => truncCoeff v h i * g i) := by
    refine (Finset.sum_subset (Finset.filter_subset _ _) ?_).symm
    intro i _ hi
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, not_le] at hi
    simp [truncCoeff, not_le.mpr hi]
  rw [hsplit, hfilter, Finset.sum_image]
  · exact Finset.sum_congr rfl (fun i _ => by rw [truncCoeff_castLE])
  · intro a _ b _ hab
    exact Fin.ext (by simpa using congrArg Fin.val hab)

/-- **The field's own coefficient pairing**: the coefficient vector of `S_m` against the coordinate
powers `c^j` is the accumulated covariance plus the exterior term.  The exterior coefficient
`c^m·d` meets `c^m`, hence `c^(2m)·d`. -/
theorem sum_streamCoeff_mul_pow (m : ℕ) (c d : ℝ) :
    (∑ i : Fin (m + 1), streamCoeff c d m i * c ^ (i : ℕ))
      = streamCovariance m c + c ^ (2 * m) * d := by
  rw [Fin.sum_univ_castSucc]
  have hlast : streamCoeff c d m (Fin.last m) * c ^ ((Fin.last m : Fin (m + 1)) : ℕ)
      = c ^ (2 * m) * d := by
    have hv : ((Fin.last m : Fin (m + 1)) : ℕ) = m := Fin.val_last m
    have hc : streamCoeff c d m (Fin.last m) = c ^ m * d := by
      simp [streamCoeff]
    rw [hc, hv]
    have hp : c ^ m * c ^ m = c ^ (2 * m) := by
      rw [← pow_add, two_mul]
    calc c ^ m * d * c ^ m = (c ^ m * c ^ m) * d := by ring
      _ = c ^ (2 * m) * d := by rw [hp]
  have hint : ∀ i : Fin m,
      streamCoeff c d m (Fin.castSucc i) * c ^ ((Fin.castSucc i : Fin (m + 1)) : ℕ)
        = (c ^ 2) ^ (i : ℕ) := by
    intro i
    have hne : (Fin.castSucc i : Fin (m + 1)) ≠ Fin.last m := Fin.castSucc_ne_last i
    have hv : ((Fin.castSucc i : Fin (m + 1)) : ℕ) = (i : ℕ) := Fin.val_castSucc i
    rw [show streamCoeff c d m (Fin.castSucc i) = c ^ (i : ℕ) by
      simp [streamCoeff, hne], hv, ← mul_pow, ← pow_two]
  rw [Finset.sum_congr rfl (fun i _ => hint i), hlast]
  have hK : streamCovariance m c = ∑ j ∈ Finset.range m, (c ^ 2) ^ j :=
    streamCovariance_closed_form m c
  rw [hK, Fin.sum_univ_eq_sum_range (fun j => (c ^ 2) ^ j)]

/-- **The field against a single coordinate** is that coordinate's coefficient. -/
theorem integral_shellLaw_streamField_mul_coord (n : ℕ) (c d : ℝ) (j : Fin (n + 1)) :
    ∫ p, streamField c d n p * p j ∂shellLaw (n + 1) = streamCoeff c d n j := by
  conv_lhs => rw [show (fun p : Fin (n + 1) → ℝ => streamField c d n p * p j)
    = fun p => (∑ i, streamCoeff c d n i * p i) * p j from by
      funext p; rw [streamField_eq_sum_coeff]]
  exact integral_shellLaw_linear_mul_coord (n + 1) (streamCoeff c d n) j

/-- **The cross-scale covariance**: the field at `n` scales against the field at `m < n` scales.
The smaller field is read in the larger space through `Fin.castLE`; its exterior coefficient
`c^m·d` then meets the larger field's interior coefficient `c^m`, so the answer is
`K_m + c^(2m)·d`. -/
theorem integral_shellLaw_streamField_mul_smaller {m n : ℕ} (hmn : m < n) (c d : ℝ) :
    ∫ p : Fin (n + 1) → ℝ, streamField c d n p
        * streamField c d m (fun i => p (Fin.castLE (Nat.succ_le_succ hmn.le) i))
      ∂shellLaw (n + 1) = streamCovariance m c + c ^ (2 * m) * d := by
  have hcoe : ∀ i : Fin (m + 1),
      streamCoeff c d n (Fin.castLE (Nat.succ_le_succ hmn.le) i) = c ^ (i : ℕ) := by
    intro i
    have hv : ((Fin.castLE (Nat.succ_le_succ hmn.le) i : Fin (n + 1)) : ℕ) = (i : ℕ) := rfl
    have hlt : (i : ℕ) < n := lt_of_le_of_lt (Nat.le_of_lt_succ i.isLt) hmn
    have hne : (Fin.castLE (Nat.succ_le_succ hmn.le) i : Fin (n + 1)) ≠ Fin.last n := by
      intro hs
      have := congrArg Fin.val hs
      rw [Fin.val_last, hv] at this
      omega
    simp only [streamCoeff, if_neg hne, hv]
  have hshift : ∀ p : Fin (n + 1) → ℝ,
      streamField c d m (fun i => p (Fin.castLE (Nat.succ_le_succ hmn.le) i))
        = ∑ i : Fin (n + 1), truncCoeff (streamCoeff c d m) hmn.le i * p i := by
    intro p
    rw [streamField_eq_sum_coeff, sum_truncCoeff_mul]
  have hcongr : (∫ p : Fin (n + 1) → ℝ, streamField c d n p
        * streamField c d m (fun i => p (Fin.castLE (Nat.succ_le_succ hmn.le) i))
        ∂shellLaw (n + 1))
      = ∫ p : Fin (n + 1) → ℝ, streamField c d n p
          * (∑ i, truncCoeff (streamCoeff c d m) hmn.le i * p i) ∂shellLaw (n + 1) :=
    integral_congr_ae (Eventually.of_forall fun p =>
      congrArg (fun x => streamField c d n p * x) (hshift p))
  rw [hcongr, integral_shellLaw_streamField_mul_linear]
  rw [show (∑ i : Fin (n + 1),
        streamCoeff c d n i * truncCoeff (streamCoeff c d m) hmn.le i)
      = ∑ i : Fin (n + 1),
        truncCoeff (streamCoeff c d m) hmn.le i * streamCoeff c d n i from
    Finset.sum_congr rfl (fun i _ => mul_comm _ _)]
  rw [sum_truncCoeff_mul]
  rw [Finset.sum_congr rfl (fun i _ => by rw [hcoe i])]
  exact sum_streamCoeff_mul_pow m c d

/-- **Every coordinate moment of the reference law factorises**: a monomial in the coordinates
integrates to the product of its one-dimensional moments.  The reference law is a product of unit
Gaussians, so this is `integral_fintype_prod_eq_prod` read coordinate by coordinate; the
four-point function is the exponent vector supported on four indices. -/
theorem integral_shellLaw_prod_coord_pow (m : ℕ) (e : Fin m → ℕ) :
    ∫ p : Fin m → ℝ, ∏ i, (p i) ^ (e i) ∂shellLaw m
      = ∏ i, ∫ z, z ^ (e i) ∂blockUnit := by
  have h := integral_fintype_prod_eq_prod (μ := fun _ : Fin m => blockUnit)
    (f := fun i z => z ^ (e i))
  simpa only [shellLaw] using h

/-! ## The three- to six-point functions of the reference law, uniformly in the fields

`shellLaw m` *is* Mathlib's product Gaussian on `Fin m → ℝ`, read through `blockUnit`, so Isserlis'
theorem on that product (`GaussianMoments`) computes every higher moment of the reference law.  This
section makes those computations the Gaussianity statements of the plan ask for.  The two general
statements come first and are uniform in the number of fields; the low moments are instances.

* `integral_shellLaw_prod_coord` — the multiplicity factorisation indexed by *sites*: a product of
  `M` coordinate values integrates to the product, over sites, of the one-dimensional moments of the
  multiplicities.  `integral_shellLaw_prod_coord_pow` above is the same statement written with an
  exponent vector instead of a tuple of indices.
* `integral_shellLaw_prod_coord_eq_wickSum`, `integral_shellLaw_prod_coord_odd`,
  `integral_shellLaw_prod_coord_even` — the same factorisation in Wick form, **for every `M`**: the
  product of one-dimensional moments is the weighted pairing sum with the identity-contraction
  weight (`wickSum_identity_eq_prod_doubleFactorial`), the pairing set is empty for odd `M`
  (`pairingSet_univ_odd`), and for even `M` it is the full pairing set (`pairingSet_univ_even`).
  Pairings are oriented by their smaller member, the convention of the matching sums in the QYM
  developments.
* `integral_shellLaw_coord_three`, `integral_shellLaw_coord_five` — the odd moments vanish: three
  or five sites cannot all occur an even number of times, so some factor is the integral of an odd
  power.
* `integral_shellLaw_coord_four` — the four-point function is the sum over the three pairings,
  `δ_ij δ_kl + δ_ik δ_jl + δ_il δ_jk`.  The pairing sum over four sites is evaluated by listing
  the three pairings of `Fin 4` (`pairingSet_four`, then `wickSum_four`).
* `integral_shellLaw_coord_six` — the six-point function is the sum over the fifteen pairings.  The
  fifteen perfect matchings of `Fin 6` are listed (`pairingSet_six`), counted
  (`pairingSet_six_card`), evaluated contraction by contraction (`pairingProdSix01` through
  `pairingProdSix15`, summed by `wickSum_six`) and read on the six indices.
* `connectedFour`, `connectedFourShell_eq_pair`, `connectedFourShell_eq_zero` — the connected
  four-point function: the fourth joint cumulant (the Möbius sum over the partitions of the four
  positions) reduces for this centred law to `m₁₂₃₄ − m₁₂ m₃₄ − m₁₃ m₂₄ − m₁₄ m₂₃`, which
  vanishes because every term is an Isserlis pairing.
* `connectedFive`, `connectedFive_eq_zero`, `connectedFiveShell_eq_zero` — the fifth joint cumulant,
  the Möbius sum over all 52 partitions of the five positions with coefficients
  `(-1)^(k-1) (k-1)!` (`connectedFive_one` checks the coefficient sum).  On five positions every
  partition contains a block of one, three or five elements (`shellFace5_card_one`,
  `shellFace5_card_three`, `shellFace5_univ_eq_zero`), and each such moment vanishes, so every
  product in the sum carries a zero factor and the cumulant is zero.
* `connectedSix`, `connectedSix_eq_reduced`, `connectedSixShell_eq_zero` — the sixth joint
  cumulant, the Möbius sum over all 203 partitions of the six positions with coefficients
  `(-1)^(k-1) (k-1)!` (`connectedSix_one` checks the coefficient sum).  One-point and three-point
  blocks vanish, a five-point block leaves a singleton, so the reduction
  `connectedSix_eq_reduced` keeps only the even partitions: the whole set, the fifteen `4 + 2`
  partitions and the fifteen `2 + 2 + 2` partitions (`shellFace6_four`, `shellFace6_pair`,
  `shellFace6_univ`).  Expanding every surviving moment by Isserlis leaves `1 - 3 + 2 = 0` per
  matching, so the cumulant is zero.

**Boundary.** These are the moments and the fourth, fifth and sixth cumulants of *this* reference
law.  `integral_shellLaw_coord_four` and `integral_shellLaw_coord_six` are Isserlis' theorem for
the covariance `1`, not a Gaussianity criterion: nothing here says a law with these moments is
Gaussian, the fourth, fifth and sixth cumulants are computed and vanish but no cumulant of
arbitrary order and no separated connected correlation is computed, and the vanishing is a
property of this law rather than a characterisation of Gaussianity.  The general-`M` statements
are uniform in the number of fields, but the per-pairing evaluation at four and six sites is
discharged by `decide` on the concrete index types `Fin 4` and `Fin 6`; no closed form for the
pairing count at arbitrary `M` is derived here.
-/

/-- The reference law is the product Gaussian of `GaussianMoments`: the same `Measure.pi` of `m`
independent unit Gaussians, with `blockUnit` unfolded. -/
theorem shellLaw_eq_productGauss (m : ℕ) : shellLaw m = productGauss (Fin m) := rfl

/-- **The multiplicity factorisation, indexed by sites**: the moment of a product of `M` coordinate
values is the product, over sites, of the one-dimensional moments of the multiplicities. -/
theorem integral_shellLaw_prod_coord {m M : ℕ} (f : Fin M → Fin m) :
    ∫ p : Fin m → ℝ, ∏ t, p (f t) ∂shellLaw m
      = ∏ a, ∫ z, z ^ (Fintype.card {t : Fin M // f t = a}) ∂blockUnit := by
  rw [shellLaw_eq_productGauss]
  simpa only [blockUnit] using integral_prod_coord_productGauss (ι := Fin m) (m := M) f

/-- The pairing `(0 1)(2 3)` of four sites. -/
def pairingSwap01 : Equiv.Perm (Fin 4) := Equiv.swap 0 1 * Equiv.swap 2 3

/-- The pairing `(0 2)(1 3)` of four sites. -/
def pairingSwap02 : Equiv.Perm (Fin 4) := Equiv.swap 0 2 * Equiv.swap 1 3

/-- The pairing `(0 3)(1 2)` of four sites. -/
def pairingSwap03 : Equiv.Perm (Fin 4) := Equiv.swap 0 3 * Equiv.swap 1 2

/-- **The pairings of four sites, listed**: the three ways to split `{0, 1, 2, 3}` into two pairs.
This is what turns the pairing sum into the three contractions of Isserlis' four-point theorem. -/
theorem pairingSet_four :
    pairingSet (Finset.univ : Finset (Fin 4))
      = {pairingSwap01, pairingSwap02, pairingSwap03} := by
  decide

/-- The pairing `(0 1)(2 3)` contributes the contraction `c 0 1 * c 2 3`. -/
theorem pairingProd01 (c : Fin 4 → Fin 4 → ℝ) :
    (∏ x ∈ Finset.univ.filter (fun x : Fin 4 => x < pairingSwap01 x), c x (pairingSwap01 x))
      = c 0 1 * c 2 3 := by
  rw [show Finset.univ.filter (fun x : Fin 4 => x < pairingSwap01 x) = {0, 2} from by decide]
  have h0 : pairingSwap01 0 = 1 := by decide
  have h2 : pairingSwap01 2 = 3 := by decide
  simp [h0, h2]

/-- The pairing `(0 2)(1 3)` contributes the contraction `c 0 2 * c 1 3`. -/
theorem pairingProd02 (c : Fin 4 → Fin 4 → ℝ) :
    (∏ x ∈ Finset.univ.filter (fun x : Fin 4 => x < pairingSwap02 x), c x (pairingSwap02 x))
      = c 0 2 * c 1 3 := by
  rw [show Finset.univ.filter (fun x : Fin 4 => x < pairingSwap02 x) = {0, 1} from by decide]
  have h0 : pairingSwap02 0 = 2 := by decide
  have h1 : pairingSwap02 1 = 3 := by decide
  simp [h0, h1]

/-- The pairing `(0 3)(1 2)` contributes the contraction `c 0 3 * c 1 2`. -/
theorem pairingProd03 (c : Fin 4 → Fin 4 → ℝ) :
    (∏ x ∈ Finset.univ.filter (fun x : Fin 4 => x < pairingSwap03 x), c x (pairingSwap03 x))
      = c 0 3 * c 1 2 := by
  rw [show Finset.univ.filter (fun x : Fin 4 => x < pairingSwap03 x) = {0, 1} from by decide]
  have h0 : pairingSwap03 0 = 3 := by decide
  have h1 : pairingSwap03 1 = 2 := by decide
  simp [h0, h1]

/-- **Isserlis' four-point sum, evaluated**: over four sites the weighted pairing sum is
`c 0 1 * c 2 3 + c 0 2 * c 1 3 + c 0 3 * c 1 2`. -/
theorem wickSum_four (c : Fin 4 → Fin 4 → ℝ) :
    wickSum c (Finset.univ : Finset (Fin 4))
      = c 0 1 * c 2 3 + c 0 2 * c 1 3 + c 0 3 * c 1 2 := by
  rw [wickSum, pairingSet_four, Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton, pairingProd01, pairingProd02, pairingProd03]
  ring

/-- An odd power of a centred Gaussian has zero integral: this is the parity half of the
multiplicity factorisation, `∫ z z^n = 0` for odd `n`. -/
theorem integral_pow_odd_blockUnit {n : ℕ} (hn : Odd n) : ∫ z, z ^ n ∂blockUnit = 0 := by
  have h := integral_pow_gaussianReal_one_moment n
  rw [show ∫ z : ℝ, z ^ n ∂blockUnit = ∫ z : ℝ, z ^ n ∂(gaussianReal 0 1) from rfl, h,
    if_neg (by rintro ⟨b, hb⟩; obtain ⟨a, ha⟩ := hn; omega)]

/-- **Three sites cannot all occur an even number of times**: the multiplicities sum to `3`, so one
of them is odd. -/
theorem exists_odd_card_fiber_three {m : ℕ} (f : Fin 3 → Fin m) :
    ∃ a, Odd (Fintype.card {t : Fin 3 // f t = a}) := by
  classical
  by_contra h
  have hall : ∀ a : Fin m, Even (Fintype.card {t : Fin 3 // f t = a}) := by
    intro a
    rcases Nat.even_or_odd (Fintype.card {t : Fin 3 // f t = a}) with he | ho
    · exact he
    · exact (h ⟨a, ho⟩).elim
  have hsum : ∑ a : Fin m, Fintype.card {t : Fin 3 // f t = a} = 3 := by
    have hfib := Finset.sum_fiberwise (Finset.univ : Finset (Fin 3)) f (fun _ => (1 : ℕ))
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, smul_eq_mul, mul_one] at hfib
    calc ∑ a : Fin m, Fintype.card {t : Fin 3 // f t = a}
        = ∑ a : Fin m, (Finset.univ.filter (fun t : Fin 3 => f t = a)).card :=
          Finset.sum_congr rfl fun a _ => Fintype.card_subtype _
      _ = 3 := hfib
  exact (by rw [hsum]; norm_num : ¬ Even (∑ a : Fin m,
    Fintype.card {t : Fin 3 // f t = a})) (Finset.even_sum _ fun a _ => hall a)

/-- **The three-point function vanishes**: with three coordinates some site is used an odd number
of times, and the corresponding one-dimensional moment — the integral of an odd power — is zero.
This is the parity half of the multiplicity factorisation, read at three sites. -/
theorem integral_shellLaw_coord_three (m : ℕ) (i j k : Fin m) :
    ∫ p : Fin m → ℝ, p i * p j * p k ∂shellLaw m = 0 := by
  classical
  set g : Fin 3 → Fin m := ![i, j, k] with hg
  have hprod : ∀ p : Fin m → ℝ, p i * p j * p k = ∏ t, p (g t) := by
    intro p
    rw [Fin.prod_univ_three]
    simp [g]
  rw [show (∫ p : Fin m → ℝ, p i * p j * p k ∂shellLaw m)
      = ∫ p : Fin m → ℝ, ∏ t, p (g t) ∂shellLaw m from
    integral_congr_ae (Eventually.of_forall hprod), integral_shellLaw_prod_coord g]
  obtain ⟨a, ha⟩ := exists_odd_card_fiber_three g
  exact Finset.prod_eq_zero (Finset.mem_univ a) (integral_pow_odd_blockUnit ha)

/-- **The four-point function**: `E[p_i p_j p_k p_l] = δ_ij δ_kl + δ_ik δ_jl + δ_il δ_jk`.

The multiplicity factorisation turns the moment into the product of the one-dimensional moments of
the four multiplicities; `wickSum_identity_eq_prod_doubleFactorial` identifies that product with the
weighted pairing sum, and `wickSum_four` evaluates the sum over the three pairings of `Fin 4`, each
pairing contributing the product of the two contractions. -/
theorem integral_shellLaw_coord_four (m : ℕ) (i j k l : Fin m) :
    ∫ p : Fin m → ℝ, p i * p j * p k * p l ∂shellLaw m
      = (if i = j then 1 else 0) * (if k = l then 1 else 0)
        + (if i = k then 1 else 0) * (if j = l then 1 else 0)
        + (if i = l then 1 else 0) * (if j = k then 1 else 0) := by
  classical
  set g : Fin 4 → Fin m := ![i, j, k, l] with hg
  have hprod : ∀ p : Fin m → ℝ, p i * p j * p k * p l = ∏ t, p (g t) := by
    intro p
    rw [Fin.prod_univ_four]
    simp [g]
  rw [show (∫ p : Fin m → ℝ, p i * p j * p k * p l ∂shellLaw m)
      = ∫ p : Fin m → ℝ, ∏ t, p (g t) ∂shellLaw m from
    integral_congr_ae (Eventually.of_forall hprod), integral_shellLaw_prod_coord g]
  rw [show (∏ a, ∫ z, z ^ (Fintype.card {t : Fin 4 // g t = a}) ∂blockUnit)
      = ∏ a, if Even (Fintype.card {t : Fin 4 // g t = a})
          then (Nat.doubleFactorial (Fintype.card {t : Fin 4 // g t = a} - 1) : ℝ) else 0 from
    Finset.prod_congr rfl fun a _ => by
      simpa only [blockUnit] using integral_pow_gaussianReal_one_moment
        (Fintype.card {t : Fin 4 // g t = a})]
  rw [← wickSum_identity_eq_prod_doubleFactorial g, wickSum_four]
  simp [g]

/-- **The Wick form of the multiplicity factorisation, uniformly in the number of fields**: for an
arbitrary tuple of `M` sites the moment is the weighted pairing sum with the identity-contraction
weight.  `M` is not fixed: the same statement covers every number of fields. -/
theorem integral_shellLaw_prod_coord_eq_wickSum {m M : ℕ} (f : Fin M → Fin m) :
    ∫ p : Fin m → ℝ, ∏ t, p (f t) ∂shellLaw m
      = wickSum (fun a b => if f a = f b then (1 : ℝ) else 0) Finset.univ := by
  rw [integral_shellLaw_prod_coord]
  rw [show (∏ a, ∫ z, z ^ (Fintype.card {t : Fin M // f t = a}) ∂blockUnit)
      = ∏ a, if Even (Fintype.card {t : Fin M // f t = a})
          then (Nat.doubleFactorial (Fintype.card {t : Fin M // f t = a} - 1) : ℝ) else 0 from
    Finset.prod_congr rfl fun a _ => by
      simpa only [blockUnit] using integral_pow_gaussianReal_one_moment
        (Fintype.card {t : Fin M // f t = a})]
  rw [← wickSum_identity_eq_prod_doubleFactorial f]

/-- **Odd moments vanish, uniformly in the number of fields**: with `2 * k + 1` sites the pairing
set is empty, so the weighted pairing sum — hence the moment — is zero for every `k`. -/
theorem integral_shellLaw_prod_coord_odd {m k : ℕ} (f : Fin (2 * k + 1) → Fin m) :
    ∫ p : Fin m → ℝ, ∏ t, p (f t) ∂shellLaw m = 0 := by
  rw [integral_shellLaw_prod_coord_eq_wickSum, wickSum, pairingSet_univ_odd, Finset.sum_empty]

/-- **Isserlis' theorem for the reference law, uniformly in the number of fields**: with `2 * k`
sites the moment is the sum over the pairings of those sites, with the identity-contraction weight.
This is the even partner of `integral_shellLaw_prod_coord_odd`, again at every `k`. -/
theorem integral_shellLaw_prod_coord_even {m k : ℕ} (f : Fin (2 * k) → Fin m) :
    ∫ p : Fin m → ℝ, ∏ t, p (f t) ∂shellLaw m
      = ∑ σ ∈ pairings (2 * k),
          ∏ a ∈ Finset.univ.filter (fun a : Fin (2 * k) => a < σ a),
            (if f a = f (σ a) then (1 : ℝ) else 0) := by
  rw [integral_shellLaw_prod_coord_eq_wickSum, wickSum, pairingSet_univ_even]

/-- **The five-point function vanishes**: five sites cannot all occur an even number of times, so
the odd-`M` form of the uniform Wick theorem applies. -/
theorem integral_shellLaw_coord_five (m : ℕ) (i j k l r : Fin m) :
    ∫ p : Fin m → ℝ, p i * p j * p k * p l * p r ∂shellLaw m = 0 := by
  classical
  set g : Fin 5 → Fin m := ![i, j, k, l, r] with hg
  have hprod : ∀ p : Fin m → ℝ, p i * p j * p k * p l * p r = ∏ t, p (g t) := by
    intro p
    rw [Fin.prod_univ_five]
    simp [g]
  rw [show (∫ p : Fin m → ℝ, p i * p j * p k * p l * p r ∂shellLaw m)
      = ∫ p : Fin m → ℝ, ∏ t, p (g t) ∂shellLaw m from
    integral_congr_ae (Eventually.of_forall hprod)]
  exact integral_shellLaw_prod_coord_odd (k := 2) g

/-- The pairing `(0 1)(2 3)(4 5)` of six sites. -/
def pairingSix01 : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 2 3 * Equiv.swap 4 5

/-- The pairing `(0 1)(2 4)(3 5)` of six sites. -/
def pairingSix02 : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 2 4 * Equiv.swap 3 5

/-- The pairing `(0 1)(2 5)(3 4)` of six sites. -/
def pairingSix03 : Equiv.Perm (Fin 6) := Equiv.swap 0 1 * Equiv.swap 2 5 * Equiv.swap 3 4

/-- The pairing `(0 2)(1 3)(4 5)` of six sites. -/
def pairingSix04 : Equiv.Perm (Fin 6) := Equiv.swap 0 2 * Equiv.swap 1 3 * Equiv.swap 4 5

/-- The pairing `(0 2)(1 4)(3 5)` of six sites. -/
def pairingSix05 : Equiv.Perm (Fin 6) := Equiv.swap 0 2 * Equiv.swap 1 4 * Equiv.swap 3 5

/-- The pairing `(0 2)(1 5)(3 4)` of six sites. -/
def pairingSix06 : Equiv.Perm (Fin 6) := Equiv.swap 0 2 * Equiv.swap 1 5 * Equiv.swap 3 4

/-- The pairing `(0 3)(1 2)(4 5)` of six sites. -/
def pairingSix07 : Equiv.Perm (Fin 6) := Equiv.swap 0 3 * Equiv.swap 1 2 * Equiv.swap 4 5

/-- The pairing `(0 3)(1 4)(2 5)` of six sites. -/
def pairingSix08 : Equiv.Perm (Fin 6) := Equiv.swap 0 3 * Equiv.swap 1 4 * Equiv.swap 2 5

/-- The pairing `(0 3)(1 5)(2 4)` of six sites. -/
def pairingSix09 : Equiv.Perm (Fin 6) := Equiv.swap 0 3 * Equiv.swap 1 5 * Equiv.swap 2 4

/-- The pairing `(0 4)(1 2)(3 5)` of six sites. -/
def pairingSix10 : Equiv.Perm (Fin 6) := Equiv.swap 0 4 * Equiv.swap 1 2 * Equiv.swap 3 5

/-- The pairing `(0 4)(1 3)(2 5)` of six sites. -/
def pairingSix11 : Equiv.Perm (Fin 6) := Equiv.swap 0 4 * Equiv.swap 1 3 * Equiv.swap 2 5

/-- The pairing `(0 4)(1 5)(2 3)` of six sites. -/
def pairingSix12 : Equiv.Perm (Fin 6) := Equiv.swap 0 4 * Equiv.swap 1 5 * Equiv.swap 2 3

/-- The pairing `(0 5)(1 2)(3 4)` of six sites. -/
def pairingSix13 : Equiv.Perm (Fin 6) := Equiv.swap 0 5 * Equiv.swap 1 2 * Equiv.swap 3 4

/-- The pairing `(0 5)(1 3)(2 4)` of six sites. -/
def pairingSix14 : Equiv.Perm (Fin 6) := Equiv.swap 0 5 * Equiv.swap 1 3 * Equiv.swap 2 4

/-- The pairing `(0 5)(1 4)(2 3)` of six sites. -/
def pairingSix15 : Equiv.Perm (Fin 6) := Equiv.swap 0 5 * Equiv.swap 1 4 * Equiv.swap 2 3

/-- **The pairings of six sites, listed**: the fifteen ways to split `{0, 1, 2, 3, 4, 5}` into
three pairs, in the order of their smallest elements.  This is what makes the six-point pairing sum
a sum of fifteen explicit terms. -/
theorem pairingSet_six :
    pairingSet (Finset.univ : Finset (Fin 6))
      = {pairingSix01, pairingSix02, pairingSix03, pairingSix04, pairingSix05, pairingSix06,
          pairingSix07, pairingSix08, pairingSix09, pairingSix10, pairingSix11, pairingSix12,
          pairingSix13, pairingSix14, pairingSix15} := by
  decide

/-- **There are fifteen pairings of six sites**: `5 · 3 · 1`.  This is the count behind the
fifteen-term six-point sum. -/
theorem pairingSet_six_card : (pairingSet (Finset.univ : Finset (Fin 6))).card = 15 := by
  rw [pairingSet_six]
  decide

theorem pairingProdSix01 (c : Fin 6 → Fin 6 → ℝ) :
    (∏ x ∈ Finset.univ.filter (fun x : Fin 6 => x < pairingSix01 x), c x (pairingSix01 x))
      = c 0 1 * c 2 3 * c 4 5 := by
  rw [show Finset.univ.filter (fun x : Fin 6 => x < pairingSix01 x) = {0, 2, 4} from by decide]
  have h0 : pairingSix01 0 = 1 := by decide
  have h2 : pairingSix01 2 = 3 := by decide
  have h4 : pairingSix01 4 = 5 := by decide
  simp [h0, h2, h4]
  ring

theorem pairingProdSix02 (c : Fin 6 → Fin 6 → ℝ) :
    (∏ x ∈ Finset.univ.filter (fun x : Fin 6 => x < pairingSix02 x), c x (pairingSix02 x))
      = c 0 1 * c 2 4 * c 3 5 := by
  rw [show Finset.univ.filter (fun x : Fin 6 => x < pairingSix02 x) = {0, 2, 3} from by decide]
  have h0 : pairingSix02 0 = 1 := by decide
  have h2 : pairingSix02 2 = 4 := by decide
  have h3 : pairingSix02 3 = 5 := by decide
  simp [h0, h2, h3]
  ring

theorem pairingProdSix03 (c : Fin 6 → Fin 6 → ℝ) :
    (∏ x ∈ Finset.univ.filter (fun x : Fin 6 => x < pairingSix03 x), c x (pairingSix03 x))
      = c 0 1 * c 2 5 * c 3 4 := by
  rw [show Finset.univ.filter (fun x : Fin 6 => x < pairingSix03 x) = {0, 2, 3} from by decide]
  have h0 : pairingSix03 0 = 1 := by decide
  have h2 : pairingSix03 2 = 5 := by decide
  have h3 : pairingSix03 3 = 4 := by decide
  simp [h0, h2, h3]
  ring

theorem pairingProdSix04 (c : Fin 6 → Fin 6 → ℝ) :
    (∏ x ∈ Finset.univ.filter (fun x : Fin 6 => x < pairingSix04 x), c x (pairingSix04 x))
      = c 0 2 * c 1 3 * c 4 5 := by
  rw [show Finset.univ.filter (fun x : Fin 6 => x < pairingSix04 x) = {0, 1, 4} from by decide]
  have h0 : pairingSix04 0 = 2 := by decide
  have h1 : pairingSix04 1 = 3 := by decide
  have h4 : pairingSix04 4 = 5 := by decide
  simp [h0, h1, h4]
  ring

theorem pairingProdSix05 (c : Fin 6 → Fin 6 → ℝ) :
    (∏ x ∈ Finset.univ.filter (fun x : Fin 6 => x < pairingSix05 x), c x (pairingSix05 x))
      = c 0 2 * c 1 4 * c 3 5 := by
  rw [show Finset.univ.filter (fun x : Fin 6 => x < pairingSix05 x) = {0, 1, 3} from by decide]
  have h0 : pairingSix05 0 = 2 := by decide
  have h1 : pairingSix05 1 = 4 := by decide
  have h3 : pairingSix05 3 = 5 := by decide
  simp [h0, h1, h3]
  ring

theorem pairingProdSix06 (c : Fin 6 → Fin 6 → ℝ) :
    (∏ x ∈ Finset.univ.filter (fun x : Fin 6 => x < pairingSix06 x), c x (pairingSix06 x))
      = c 0 2 * c 1 5 * c 3 4 := by
  rw [show Finset.univ.filter (fun x : Fin 6 => x < pairingSix06 x) = {0, 1, 3} from by decide]
  have h0 : pairingSix06 0 = 2 := by decide
  have h1 : pairingSix06 1 = 5 := by decide
  have h3 : pairingSix06 3 = 4 := by decide
  simp [h0, h1, h3]
  ring

theorem pairingProdSix07 (c : Fin 6 → Fin 6 → ℝ) :
    (∏ x ∈ Finset.univ.filter (fun x : Fin 6 => x < pairingSix07 x), c x (pairingSix07 x))
      = c 0 3 * c 1 2 * c 4 5 := by
  rw [show Finset.univ.filter (fun x : Fin 6 => x < pairingSix07 x) = {0, 1, 4} from by decide]
  have h0 : pairingSix07 0 = 3 := by decide
  have h1 : pairingSix07 1 = 2 := by decide
  have h4 : pairingSix07 4 = 5 := by decide
  simp [h0, h1, h4]
  ring

theorem pairingProdSix08 (c : Fin 6 → Fin 6 → ℝ) :
    (∏ x ∈ Finset.univ.filter (fun x : Fin 6 => x < pairingSix08 x), c x (pairingSix08 x))
      = c 0 3 * c 1 4 * c 2 5 := by
  rw [show Finset.univ.filter (fun x : Fin 6 => x < pairingSix08 x) = {0, 1, 2} from by decide]
  have h0 : pairingSix08 0 = 3 := by decide
  have h1 : pairingSix08 1 = 4 := by decide
  have h2 : pairingSix08 2 = 5 := by decide
  simp [h0, h1, h2]
  ring

theorem pairingProdSix09 (c : Fin 6 → Fin 6 → ℝ) :
    (∏ x ∈ Finset.univ.filter (fun x : Fin 6 => x < pairingSix09 x), c x (pairingSix09 x))
      = c 0 3 * c 1 5 * c 2 4 := by
  rw [show Finset.univ.filter (fun x : Fin 6 => x < pairingSix09 x) = {0, 1, 2} from by decide]
  have h0 : pairingSix09 0 = 3 := by decide
  have h1 : pairingSix09 1 = 5 := by decide
  have h2 : pairingSix09 2 = 4 := by decide
  simp [h0, h1, h2]
  ring

theorem pairingProdSix10 (c : Fin 6 → Fin 6 → ℝ) :
    (∏ x ∈ Finset.univ.filter (fun x : Fin 6 => x < pairingSix10 x), c x (pairingSix10 x))
      = c 0 4 * c 1 2 * c 3 5 := by
  rw [show Finset.univ.filter (fun x : Fin 6 => x < pairingSix10 x) = {0, 1, 3} from by decide]
  have h0 : pairingSix10 0 = 4 := by decide
  have h1 : pairingSix10 1 = 2 := by decide
  have h3 : pairingSix10 3 = 5 := by decide
  simp [h0, h1, h3]
  ring

theorem pairingProdSix11 (c : Fin 6 → Fin 6 → ℝ) :
    (∏ x ∈ Finset.univ.filter (fun x : Fin 6 => x < pairingSix11 x), c x (pairingSix11 x))
      = c 0 4 * c 1 3 * c 2 5 := by
  rw [show Finset.univ.filter (fun x : Fin 6 => x < pairingSix11 x) = {0, 1, 2} from by decide]
  have h0 : pairingSix11 0 = 4 := by decide
  have h1 : pairingSix11 1 = 3 := by decide
  have h2 : pairingSix11 2 = 5 := by decide
  simp [h0, h1, h2]
  ring

theorem pairingProdSix12 (c : Fin 6 → Fin 6 → ℝ) :
    (∏ x ∈ Finset.univ.filter (fun x : Fin 6 => x < pairingSix12 x), c x (pairingSix12 x))
      = c 0 4 * c 1 5 * c 2 3 := by
  rw [show Finset.univ.filter (fun x : Fin 6 => x < pairingSix12 x) = {0, 1, 2} from by decide]
  have h0 : pairingSix12 0 = 4 := by decide
  have h1 : pairingSix12 1 = 5 := by decide
  have h2 : pairingSix12 2 = 3 := by decide
  simp [h0, h1, h2]
  ring

theorem pairingProdSix13 (c : Fin 6 → Fin 6 → ℝ) :
    (∏ x ∈ Finset.univ.filter (fun x : Fin 6 => x < pairingSix13 x), c x (pairingSix13 x))
      = c 0 5 * c 1 2 * c 3 4 := by
  rw [show Finset.univ.filter (fun x : Fin 6 => x < pairingSix13 x) = {0, 1, 3} from by decide]
  have h0 : pairingSix13 0 = 5 := by decide
  have h1 : pairingSix13 1 = 2 := by decide
  have h3 : pairingSix13 3 = 4 := by decide
  simp [h0, h1, h3]
  ring

theorem pairingProdSix14 (c : Fin 6 → Fin 6 → ℝ) :
    (∏ x ∈ Finset.univ.filter (fun x : Fin 6 => x < pairingSix14 x), c x (pairingSix14 x))
      = c 0 5 * c 1 3 * c 2 4 := by
  rw [show Finset.univ.filter (fun x : Fin 6 => x < pairingSix14 x) = {0, 1, 2} from by decide]
  have h0 : pairingSix14 0 = 5 := by decide
  have h1 : pairingSix14 1 = 3 := by decide
  have h2 : pairingSix14 2 = 4 := by decide
  simp [h0, h1, h2]
  ring

theorem pairingProdSix15 (c : Fin 6 → Fin 6 → ℝ) :
    (∏ x ∈ Finset.univ.filter (fun x : Fin 6 => x < pairingSix15 x), c x (pairingSix15 x))
      = c 0 5 * c 1 4 * c 2 3 := by
  rw [show Finset.univ.filter (fun x : Fin 6 => x < pairingSix15 x) = {0, 1, 2} from by decide]
  have h0 : pairingSix15 0 = 5 := by decide
  have h1 : pairingSix15 1 = 4 := by decide
  have h2 : pairingSix15 2 = 3 := by decide
  simp [h0, h1, h2]
  ring

/-- **Isserlis' six-point sum, evaluated**: over six sites the weighted pairing sum is the sum of
the fifteen contractions, one per pairing of `{0, …, 5}`. -/
theorem wickSum_six (c : Fin 6 → Fin 6 → ℝ) :
    wickSum c (Finset.univ : Finset (Fin 6))
      = c 0 1 * c 2 3 * c 4 5 + c 0 1 * c 2 4 * c 3 5 + c 0 1 * c 2 5 * c 3 4
        + c 0 2 * c 1 3 * c 4 5 + c 0 2 * c 1 4 * c 3 5 + c 0 2 * c 1 5 * c 3 4
        + c 0 3 * c 1 2 * c 4 5 + c 0 3 * c 1 4 * c 2 5 + c 0 3 * c 1 5 * c 2 4
        + c 0 4 * c 1 2 * c 3 5 + c 0 4 * c 1 3 * c 2 5 + c 0 4 * c 1 5 * c 2 3
        + c 0 5 * c 1 2 * c 3 4 + c 0 5 * c 1 3 * c 2 4 + c 0 5 * c 1 4 * c 2 3 := by
  rw [wickSum, pairingSet_six]
  rw [Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  rw [pairingProdSix01, pairingProdSix02, pairingProdSix03, pairingProdSix04,
    pairingProdSix05, pairingProdSix06, pairingProdSix07, pairingProdSix08,
    pairingProdSix09, pairingProdSix10, pairingProdSix11, pairingProdSix12,
    pairingProdSix13, pairingProdSix14, pairingProdSix15]
  ring

/-- **The six-point function**: `E[p_i p_j p_k p_l p_r p_s]` is the sum of the fifteen pairings,
`Σ δ_ab δ_cd δ_ef` over the perfect matchings of the six indices. -/
theorem integral_shellLaw_coord_six (m : ℕ) (i j k l r s : Fin m) :
    ∫ p : Fin m → ℝ, p i * p j * p k * p l * p r * p s ∂shellLaw m
      = (if i = j then 1 else 0) * (if k = l then 1 else 0) * (if r = s then 1 else 0)
        + (if i = j then 1 else 0) * (if k = r then 1 else 0) * (if l = s then 1 else 0)
        + (if i = j then 1 else 0) * (if k = s then 1 else 0) * (if l = r then 1 else 0)
        + (if i = k then 1 else 0) * (if j = l then 1 else 0) * (if r = s then 1 else 0)
        + (if i = k then 1 else 0) * (if j = r then 1 else 0) * (if l = s then 1 else 0)
        + (if i = k then 1 else 0) * (if j = s then 1 else 0) * (if l = r then 1 else 0)
        + (if i = l then 1 else 0) * (if j = k then 1 else 0) * (if r = s then 1 else 0)
        + (if i = l then 1 else 0) * (if j = r then 1 else 0) * (if k = s then 1 else 0)
        + (if i = l then 1 else 0) * (if j = s then 1 else 0) * (if k = r then 1 else 0)
        + (if i = r then 1 else 0) * (if j = k then 1 else 0) * (if l = s then 1 else 0)
        + (if i = r then 1 else 0) * (if j = l then 1 else 0) * (if k = s then 1 else 0)
        + (if i = r then 1 else 0) * (if j = s then 1 else 0) * (if k = l then 1 else 0)
        + (if i = s then 1 else 0) * (if j = k then 1 else 0) * (if l = r then 1 else 0)
        + (if i = s then 1 else 0) * (if j = l then 1 else 0) * (if k = r then 1 else 0)
        + (if i = s then 1 else 0) * (if j = r then 1 else 0) * (if k = l then 1 else 0) := by
  classical
  set g : Fin 6 → Fin m := ![i, j, k, l, r, s] with hg
  have hprod : ∀ p : Fin m → ℝ, p i * p j * p k * p l * p r * p s = ∏ t, p (g t) := by
    intro p
    rw [Fin.prod_univ_six]
    simp [g]
  rw [show (∫ p : Fin m → ℝ, p i * p j * p k * p l * p r * p s ∂shellLaw m)
      = ∫ p : Fin m → ℝ, ∏ t, p (g t) ∂shellLaw m from
    integral_congr_ae (Eventually.of_forall hprod),
    integral_shellLaw_prod_coord_eq_wickSum, wickSum_six]
  simp [g]

/-! ## The connected four-point function of the reference law

The joint cumulant of four fields is the Möbius sum over the partitions of the four positions,

`κ = m₁₂₃₄ − (m₁₂ m₃₄ + m₁₃ m₂₄ + m₁₄ m₂₃) − (m₁ m₂₃₄ + m₂ m₁₃₄ + m₃ m₁₂₄ + m₄ m₁₂₃)
     + 2 (m₁₂ m₃ m₄ + … six terms) − 6 m₁ m₂ m₃ m₄`,

the partition formula used at three points by `connectedThree` in the QYM development
(`../OpenAI-YM-20261104/lean/MSPositionLabels.lean`; `../QCD` carries the frozen reference copy of
the same development).  Under the reference law every one-point function vanishes, so every term
with a singleton block drops out and only the partition into two pairs survives:

`κ = m₁₂₃₄ − m₁₂ m₃₄ − m₁₃ m₂₄ − m₁₄ m₂₃`.

Both the four-point function and the two-point functions are Isserlis pairings, so the cumulant is
zero: the reference law has no connected four-point part.
-/

/-- **The fourth joint cumulant**, as the Möbius sum over the partitions of the four positions.
`face s` is the joint moment of the positions in `s`; a partition into `k` blocks contributes
`(-1)^(k-1) (k-1)!` times the product of its block moments. -/
def connectedFour {R : Type*} [CommRing R] (face : Finset (Fin 4) → R) : R :=
  face Finset.univ
    - (face {0, 1} * face {2, 3} + face {0, 2} * face {1, 3} + face {0, 3} * face {1, 2})
    - (face {0} * face {1, 2, 3} + face {1} * face {0, 2, 3}
        + face {2} * face {0, 1, 3} + face {3} * face {0, 1, 2})
    + 2 * (face {0, 1} * face {2} * face {3} + face {0, 2} * face {1} * face {3}
        + face {0, 3} * face {1} * face {2} + face {1, 2} * face {0} * face {3}
        + face {1, 3} * face {0} * face {2} + face {2, 3} * face {0} * face {1})
    - 6 * face {0} * face {1} * face {2} * face {3}

/-- The joint moment of the positions in `s`, for the tuple of sites `f`. -/
noncomputable def shellFace (m : ℕ) (f : Fin 4 → Fin m) (s : Finset (Fin 4)) : ℝ :=
  ∫ p : Fin m → ℝ, ∏ t ∈ s, p (f t) ∂shellLaw m

@[simp] theorem shellFace_empty (m : ℕ) (f : Fin 4 → Fin m) :
    shellFace m f ∅ = 1 := by
  simp [shellFace]

/-- A single position has zero moment under the reference law. -/
theorem shellFace_singleton (m : ℕ) (f : Fin 4 → Fin m) (i : Fin 4) :
    shellFace m f {i} = 0 := by
  simp only [shellFace, Finset.prod_singleton]
  exact integral_shellLaw_coord m (f i)

/-- The connected four-point function of the reference law. -/
noncomputable def connectedFourShell (m : ℕ) (f : Fin 4 → Fin m) : ℝ :=
  connectedFour (shellFace m f)

/-- The reference law is centred, so the cumulant keeps only the partition into two pairs. -/
theorem connectedFourShell_eq (m : ℕ) (f : Fin 4 → Fin m) :
    connectedFourShell m f
      = shellFace m f Finset.univ - shellFace m f {0, 1} * shellFace m f {2, 3}
        - shellFace m f {0, 2} * shellFace m f {1, 3}
        - shellFace m f {0, 3} * shellFace m f {1, 2} := by
  simp only [connectedFourShell, connectedFour, shellFace_singleton]
  ring

/-- The full moment, read as a monomial in the four sites. -/
theorem shellFace_univ (m : ℕ) (f : Fin 4 → Fin m) :
    shellFace m f Finset.univ
      = ∫ p, p (f 0) * p (f 1) * p (f 2) * p (f 3) ∂shellLaw m := by
  simp only [shellFace]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp [Fin.prod_univ_four]

/-- A two-position face is a pair moment. -/
theorem shellFace_pair (m : ℕ) (f : Fin 4 → Fin m) {a b : Fin 4} (hab : a ≠ b) :
    shellFace m f {a, b} = ∫ p, p (f a) * p (f b) ∂shellLaw m := by
  simp only [shellFace]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  change (∏ t ∈ ({a, b} : Finset (Fin 4)), p (f t)) = p (f a) * p (f b)
  rw [Finset.prod_pair hab]

/-- **The four-point cumulant in moment language**: for this centred law the partition sum
collapses to the four-point function minus the three pairings. -/
theorem connectedFourShell_eq_pair (m : ℕ) (f : Fin 4 → Fin m) :
    connectedFourShell m f
      = (∫ p, p (f 0) * p (f 1) * p (f 2) * p (f 3) ∂shellLaw m)
        - (∫ p, p (f 0) * p (f 1) ∂shellLaw m) * (∫ p, p (f 2) * p (f 3) ∂shellLaw m)
        - (∫ p, p (f 0) * p (f 2) ∂shellLaw m) * (∫ p, p (f 1) * p (f 3) ∂shellLaw m)
        - (∫ p, p (f 0) * p (f 3) ∂shellLaw m) * (∫ p, p (f 1) * p (f 2) ∂shellLaw m) := by
  rw [connectedFourShell_eq, shellFace_univ,
    shellFace_pair m f (show (0 : Fin 4) ≠ 1 by decide),
    shellFace_pair m f (show (2 : Fin 4) ≠ 3 by decide),
    shellFace_pair m f (show (0 : Fin 4) ≠ 2 by decide),
    shellFace_pair m f (show (1 : Fin 4) ≠ 3 by decide),
    shellFace_pair m f (show (0 : Fin 4) ≠ 3 by decide),
    shellFace_pair m f (show (1 : Fin 4) ≠ 2 by decide)]

/-- **The connected four-point function vanishes.**  The four-point function is the three
pairings and every two-point function is a `δ`, so the cumulant is
`(δδ + δδ + δδ) − δδ − δδ − δδ = 0`. -/
theorem connectedFourShell_eq_zero (m : ℕ) (f : Fin 4 → Fin m) :
    connectedFourShell m f = 0 := by
  rw [connectedFourShell_eq_pair]
  have h4 : (∫ p, p (f 0) * p (f 1) * p (f 2) * p (f 3) ∂shellLaw m)
      = (if f 0 = f 1 then 1 else 0) * (if f 2 = f 3 then 1 else 0)
        + (if f 0 = f 2 then 1 else 0) * (if f 1 = f 3 then 1 else 0)
        + (if f 0 = f 3 then 1 else 0) * (if f 1 = f 2 then 1 else 0) :=
    integral_shellLaw_coord_four m (f 0) (f 1) (f 2) (f 3)
  have h01 : (∫ p, p (f 0) * p (f 1) ∂shellLaw m) = if f 0 = f 1 then 1 else 0 :=
    integral_shellLaw_coord_mul_coord m (f 0) (f 1)
  have h23 : (∫ p, p (f 2) * p (f 3) ∂shellLaw m) = if f 2 = f 3 then 1 else 0 :=
    integral_shellLaw_coord_mul_coord m (f 2) (f 3)
  have h02 : (∫ p, p (f 0) * p (f 2) ∂shellLaw m) = if f 0 = f 2 then 1 else 0 :=
    integral_shellLaw_coord_mul_coord m (f 0) (f 2)
  have h13 : (∫ p, p (f 1) * p (f 3) ∂shellLaw m) = if f 1 = f 3 then 1 else 0 :=
    integral_shellLaw_coord_mul_coord m (f 1) (f 3)
  have h03 : (∫ p, p (f 0) * p (f 3) ∂shellLaw m) = if f 0 = f 3 then 1 else 0 :=
    integral_shellLaw_coord_mul_coord m (f 0) (f 3)
  have h12 : (∫ p, p (f 1) * p (f 2) ∂shellLaw m) = if f 1 = f 2 then 1 else 0 :=
    integral_shellLaw_coord_mul_coord m (f 1) (f 2)
  rw [h4, h01, h23, h02, h13, h03, h12]
  ring

/-- **The connected four-point function at four coordinates**, derived: the full cumulant of
`p_i, p_j, p_k, p_l` is the four-point function minus the three pairings of the four indices. -/
theorem connectedFour_coord_eq (m : ℕ) (i j k l : Fin m) :
    connectedFour (fun s => ∫ p : Fin m → ℝ, ∏ t ∈ s, p (![i, j, k, l] t) ∂shellLaw m)
      = (∫ p, p i * p j * p k * p l ∂shellLaw m)
        - (∫ p, p i * p j ∂shellLaw m) * (∫ p, p k * p l ∂shellLaw m)
        - (∫ p, p i * p k ∂shellLaw m) * (∫ p, p j * p l ∂shellLaw m)
        - (∫ p, p i * p l ∂shellLaw m) * (∫ p, p j * p k ∂shellLaw m) := by
  have h := connectedFourShell_eq_pair m ![i, j, k, l]
  simpa using h

/-- **The connected four-point function at four coordinates vanishes**: the cumulant of
`p_i, p_j, p_k, p_l` is zero. -/
theorem connectedFour_coord_eq_zero (m : ℕ) (i j k l : Fin m) :
    connectedFour (fun s => ∫ p : Fin m → ℝ, ∏ t ∈ s, p (![i, j, k, l] t) ∂shellLaw m) = 0 :=
  connectedFourShell_eq_zero m ![i, j, k, l]

/-! ## The connected five-point function of the reference law

The fifth joint cumulant is the Möbius sum over the fifty-two partitions of the five positions,

`κ = Σ_π (-1)^(k(π)-1) (k(π)-1)! ∏_{B ∈ π} m(B)`,

the partition formula that gives the fourth cumulant in `connectedFour` and the third cumulant at
`connectedThree` in the QYM development (`../OpenAI-YM-20261104/lean/MSPositionLabels.lean`; the
frozen `../QCD` copy of that development carries the same convention).

On a five-element set every partition has a block of cardinality one, three or five: a partition
with a small block has a singleton whenever a block has at most two elements, a partition into a
two and a three has a triple, and the one-block partition is the whole set.  Under the reference
law all three of those moments vanish, so every product in the Möbius sum carries a zero factor
and the fifth cumulant is zero: the reference law has no connected five-point part.

This is the first cumulant above the fourth, and it is still one explicit partition sum.  No
cumulant of arbitrary order and no general partition-lattice Möbius inversion is claimed.
-/

/-- **The fifth joint cumulant**, as the Möbius sum over the 52 partitions of the five positions.
A partition into `k` blocks contributes `(-1)^(k-1) (k-1)!` times the product of its block
moments. -/
def connectedFive {R : Type*} [CommRing R] (face : Finset (Fin 5) → R) : R :=
  face Finset.univ
    - (face {0} * face {1, 2, 3, 4} + face {0, 1} * face {2, 3, 4} + face {0, 1, 2} * face {3, 4}
       + face {0, 1, 2, 3} * face {4} + face {0, 1, 2, 4} * face {3} + face {0, 1, 3} * face {2, 4}
       + face {0, 1, 3, 4} * face {2} + face {0, 1, 4} * face {2, 3} + face {0, 2} * face {1, 3, 4}
       + face {0, 2, 3} * face {1, 4} + face {0, 2, 3, 4} * face {1} + face {0, 2, 4} * face {1, 3}
       + face {0, 3} * face {1, 2, 4} + face {0, 3, 4} * face {1, 2} + face {0, 4} * face {1, 2, 3})
    + 2 * (face {0} * face {1} * face {2, 3, 4} + face {0} * face {1, 2} * face {3, 4}
           + face {0} * face {1, 2, 3} * face {4} + face {0} * face {1, 2, 4} * face {3}
           + face {0} * face {1, 3} * face {2, 4} + face {0} * face {1, 3, 4} * face {2}
           + face {0} * face {1, 4} * face {2, 3} + face {0, 1} * face {2} * face {3, 4}
           + face {0, 1} * face {2, 3} * face {4} + face {0, 1} * face {2, 4} * face {3}
           + face {0, 1, 2} * face {3} * face {4} + face {0, 1, 3} * face {2} * face {4}
           + face {0, 1, 4} * face {2} * face {3} + face {0, 2} * face {1} * face {3, 4}
           + face {0, 2} * face {1, 3} * face {4} + face {0, 2} * face {1, 4} * face {3}
           + face {0, 2, 3} * face {1} * face {4} + face {0, 2, 4} * face {1} * face {3}
           + face {0, 3} * face {1} * face {2, 4} + face {0, 3} * face {1, 2} * face {4}
           + face {0, 3} * face {1, 4} * face {2} + face {0, 3, 4} * face {1} * face {2}
           + face {0, 4} * face {1} * face {2, 3} + face {0, 4} * face {1, 2} * face {3}
           + face {0, 4} * face {1, 3} * face {2})
    - 6 * (face {0} * face {1} * face {2} * face {3, 4}
           + face {0} * face {1} * face {2, 3} * face {4}
           + face {0} * face {1} * face {2, 4} * face {3}
           + face {0} * face {1, 2} * face {3} * face {4}
           + face {0} * face {1, 3} * face {2} * face {4}
           + face {0} * face {1, 4} * face {2} * face {3}
           + face {0, 1} * face {2} * face {3} * face {4}
           + face {0, 2} * face {1} * face {3} * face {4}
           + face {0, 3} * face {1} * face {2} * face {4}
           + face {0, 4} * face {1} * face {2} * face {3})
    + 24 * (face {0} * face {1} * face {2} * face {3} * face {4})

/-- A check on the explicit partition list: five positions have `52 = Bell 5` partitions and the
Möbius coefficients `(-1)^(k-1) (k-1)!` sum to zero over them (the partition-lattice identity
`Σ_π μ(π, ⊤) = 0` for `n ≥ 2`). -/
theorem connectedFive_one : connectedFive (fun _ => (1 : ℤ)) = 0 := by
  decide

/-- The joint moment of the positions in `s`, for the tuple of five sites `f`. -/
noncomputable def shellFace5 (m : ℕ) (f : Fin 5 → Fin m) (s : Finset (Fin 5)) : ℝ :=
  ∫ p : Fin m → ℝ, ∏ t ∈ s, p (f t) ∂shellLaw m

/-- A single position has zero moment under the reference law. -/
theorem shellFace5_singleton (m : ℕ) (f : Fin 5 → Fin m) (i : Fin 5) :
    shellFace5 m f {i} = 0 := by
  simp only [shellFace5, Finset.prod_singleton]
  exact integral_shellLaw_coord m (f i)

/-- A block of one position has zero moment. -/
theorem shellFace5_card_one (m : ℕ) (f : Fin 5 → Fin m) {s : Finset (Fin 5)}
    (hs : s.card = 1) : shellFace5 m f s = 0 := by
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hs
  exact shellFace5_singleton m f i

/-- A block of three positions has zero moment under the reference law. -/
theorem shellFace5_card_three (m : ℕ) (f : Fin 5 → Fin m) {s : Finset (Fin 5)}
    (hs : s.card = 3) : shellFace5 m f s = 0 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs
  have hprod : ∀ p : Fin m → ℝ,
      (∏ t ∈ ({a, b, c} : Finset (Fin 5)), p (f t)) = p (f a) * p (f b) * p (f c) := by
    intro p
    rw [Finset.prod_insert (by simp [hab, hac]),
      Finset.prod_insert (by simp [hbc]), Finset.prod_singleton]
    ring
  rw [show shellFace5 m f {a, b, c}
      = ∫ p, p (f a) * p (f b) * p (f c) ∂shellLaw m from
    integral_congr_ae (Eventually.of_forall fun p => hprod p)]
  exact integral_shellLaw_coord_three m (f a) (f b) (f c)

/-- The whole set is the five-point function. -/
theorem shellFace5_univ (m : ℕ) (f : Fin 5 → Fin m) :
    shellFace5 m f Finset.univ
      = ∫ p, p (f 0) * p (f 1) * p (f 2) * p (f 3) * p (f 4) ∂shellLaw m := by
  simp only [shellFace5]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp [Fin.prod_univ_five]

/-- **The five-point function vanishes**: an odd number of sites cannot all occur an even number
of times. -/
theorem shellFace5_univ_eq_zero (m : ℕ) (f : Fin 5 → Fin m) :
    shellFace5 m f Finset.univ = 0 := by
  rw [shellFace5_univ]
  exact integral_shellLaw_coord_five m (f 0) (f 1) (f 2) (f 3) (f 4)

/-- The connected five-point function of the reference law. -/
noncomputable def connectedFiveShell (m : ℕ) (f : Fin 5 → Fin m) : ℝ :=
  connectedFive (shellFace5 m f)

/-- **A fifth cumulant vanishes when every block of one, three or five positions has zero
moment.**  On five positions every partition has such a block, so the Möbius sum is a sum of
products each carrying a zero factor. -/
theorem connectedFive_eq_zero {R : Type*} [CommRing R] (face : Finset (Fin 5) → R)
    (h1 : ∀ s, s.card = 1 → face s = 0) (h3 : ∀ s, s.card = 3 → face s = 0)
    (h5 : face Finset.univ = 0) : connectedFive face = 0 := by
  simp [connectedFive, h1, h3, h5]

/-- **The connected five-point function of the reference law vanishes.**  The centred law has no
connected five-point part. -/
theorem connectedFiveShell_eq_zero (m : ℕ) (f : Fin 5 → Fin m) :
    connectedFiveShell m f = 0 :=
  connectedFive_eq_zero _
    (fun _ hs => shellFace5_card_one m f hs)
    (fun _ hs => shellFace5_card_three m f hs)
    (shellFace5_univ_eq_zero m f)

/-- **The connected five-point function at five coordinates vanishes**: the fifth cumulant of
`p_i, p_j, p_k, p_l, p_r` is zero. -/
theorem connectedFive_coord_eq_zero (m : ℕ) (i j k l r : Fin m) :
    connectedFive
      (fun s => ∫ p : Fin m → ℝ, ∏ t ∈ s, p (![i, j, k, l, r] t) ∂shellLaw m) = 0 :=
  connectedFiveShell_eq_zero m ![i, j, k, l, r]
/-! ## The connected six-point function of the reference law

The sixth joint cumulant is the Möbius sum over the two hundred and three partitions of the six
positions,

`κ = Σ_π (-1)^(k(π)-1) (k(π)-1)! ∏_{B ∈ π} m(B)`,

the partition formula of `connectedFour` and `connectedFive`.  `connectedSix_one` checks the
explicit list: six positions have `203 = Bell 6` partitions and their coefficients sum to zero.

The odd-block argument that settled the fifth cumulant does not finish this one.  A partition with
a block of one position dies on the vanishing one-point moment, one with a block of three on the
vanishing three-point moment, and a block of five leaves a singleton.  What survives is exactly
the partitions into blocks of even cardinality: the whole set, the fifteen `4 + 2` partitions and
the fifteen `2 + 2 + 2` partitions.  Every surviving moment is an Isserlis sum, and their
coefficients cancel:

`1 - 3 + 2 = 0`.

Each of the fifteen matchings of six sites appears once in the six-point function, three times in
the `4 + 2` sum (once for each choice of the pair that is the two-block), and once in the
`2 + 2 + 2` sum, whose coefficient is `2`.  So every matching contributes `1 - 3 + 2 = 0` and the
sixth cumulant vanishes.

This is one explicit partition sum at one arity.  No cumulant of arbitrary order, no
partition-lattice Möbius inversion over general `n` and no general moment-cumulant theorem is
claimed.
-/

/-- **The sixth joint cumulant**, as the Möbius sum over the 203 partitions of the six positions.
A partition into `k` blocks contributes `(-1)^(k-1) (k-1)!` times the product of its block
moments. -/
def connectedSix {R : Type*} [CommRing R] (face : Finset (Fin 6) → R) : R :=
  face Finset.univ
    - (
        face {0, 1, 2, 3, 4} * face {5} + face {0, 1, 2, 3, 5} * face {4}
        + face {0, 1, 2, 3} * face {4, 5} + face {0, 1, 2, 4, 5} * face {3}
        + face {0, 1, 2, 4} * face {3, 5} + face {0, 1, 2, 5} * face {3, 4}
        + face {0, 1, 2} * face {3, 4, 5} + face {0, 1, 3, 4, 5} * face {2}
        + face {0, 1, 3, 4} * face {2, 5} + face {0, 1, 3, 5} * face {2, 4}
        + face {0, 1, 3} * face {2, 4, 5} + face {0, 1, 4, 5} * face {2, 3}
        + face {0, 1, 4} * face {2, 3, 5} + face {0, 1, 5} * face {2, 3, 4}
        + face {0, 1} * face {2, 3, 4, 5} + face {0, 2, 3, 4, 5} * face {1}
        + face {0, 2, 3, 4} * face {1, 5} + face {0, 2, 3, 5} * face {1, 4}
        + face {0, 2, 3} * face {1, 4, 5} + face {0, 2, 4, 5} * face {1, 3}
        + face {0, 2, 4} * face {1, 3, 5} + face {0, 2, 5} * face {1, 3, 4}
        + face {0, 2} * face {1, 3, 4, 5} + face {0, 3, 4, 5} * face {1, 2}
        + face {0, 3, 4} * face {1, 2, 5} + face {0, 3, 5} * face {1, 2, 4}
        + face {0, 3} * face {1, 2, 4, 5} + face {0, 4, 5} * face {1, 2, 3}
        + face {0, 4} * face {1, 2, 3, 5} + face {0, 5} * face {1, 2, 3, 4}
        + face {0} * face {1, 2, 3, 4, 5}
      )
    + 2 * (
        face {0, 1, 2, 3} * face {4} * face {5} + face {0, 1, 2, 4} * face {3} * face {5}
        + face {0, 1, 2, 5} * face {3} * face {4} + face {0, 1, 2} * face {3, 4} * face {5}
        + face {0, 1, 2} * face {3, 5} * face {4} + face {0, 1, 2} * face {3} * face {4, 5}
        + face {0, 1, 3, 4} * face {2} * face {5} + face {0, 1, 3, 5} * face {2} * face {4}
        + face {0, 1, 3} * face {2, 4} * face {5} + face {0, 1, 3} * face {2, 5} * face {4}
        + face {0, 1, 3} * face {2} * face {4, 5} + face {0, 1, 4, 5} * face {2} * face {3}
        + face {0, 1, 4} * face {2, 3} * face {5} + face {0, 1, 4} * face {2, 5} * face {3}
        + face {0, 1, 4} * face {2} * face {3, 5} + face {0, 1, 5} * face {2, 3} * face {4}
        + face {0, 1, 5} * face {2, 4} * face {3} + face {0, 1, 5} * face {2} * face {3, 4}
        + face {0, 1} * face {2, 3, 4} * face {5} + face {0, 1} * face {2, 3, 5} * face {4}
        + face {0, 1} * face {2, 3} * face {4, 5} + face {0, 1} * face {2, 4, 5} * face {3}
        + face {0, 1} * face {2, 4} * face {3, 5} + face {0, 1} * face {2, 5} * face {3, 4}
        + face {0, 1} * face {2} * face {3, 4, 5} + face {0, 2, 3, 4} * face {1} * face {5}
        + face {0, 2, 3, 5} * face {1} * face {4} + face {0, 2, 3} * face {1, 4} * face {5}
        + face {0, 2, 3} * face {1, 5} * face {4} + face {0, 2, 3} * face {1} * face {4, 5}
        + face {0, 2, 4, 5} * face {1} * face {3} + face {0, 2, 4} * face {1, 3} * face {5}
        + face {0, 2, 4} * face {1, 5} * face {3} + face {0, 2, 4} * face {1} * face {3, 5}
        + face {0, 2, 5} * face {1, 3} * face {4} + face {0, 2, 5} * face {1, 4} * face {3}
        + face {0, 2, 5} * face {1} * face {3, 4} + face {0, 2} * face {1, 3, 4} * face {5}
        + face {0, 2} * face {1, 3, 5} * face {4} + face {0, 2} * face {1, 3} * face {4, 5}
        + face {0, 2} * face {1, 4, 5} * face {3} + face {0, 2} * face {1, 4} * face {3, 5}
        + face {0, 2} * face {1, 5} * face {3, 4} + face {0, 2} * face {1} * face {3, 4, 5}
        + face {0, 3, 4, 5} * face {1} * face {2} + face {0, 3, 4} * face {1, 2} * face {5}
        + face {0, 3, 4} * face {1, 5} * face {2} + face {0, 3, 4} * face {1} * face {2, 5}
        + face {0, 3, 5} * face {1, 2} * face {4} + face {0, 3, 5} * face {1, 4} * face {2}
        + face {0, 3, 5} * face {1} * face {2, 4} + face {0, 3} * face {1, 2, 4} * face {5}
        + face {0, 3} * face {1, 2, 5} * face {4} + face {0, 3} * face {1, 2} * face {4, 5}
        + face {0, 3} * face {1, 4, 5} * face {2} + face {0, 3} * face {1, 4} * face {2, 5}
        + face {0, 3} * face {1, 5} * face {2, 4} + face {0, 3} * face {1} * face {2, 4, 5}
        + face {0, 4, 5} * face {1, 2} * face {3} + face {0, 4, 5} * face {1, 3} * face {2}
        + face {0, 4, 5} * face {1} * face {2, 3} + face {0, 4} * face {1, 2, 3} * face {5}
        + face {0, 4} * face {1, 2, 5} * face {3} + face {0, 4} * face {1, 2} * face {3, 5}
        + face {0, 4} * face {1, 3, 5} * face {2} + face {0, 4} * face {1, 3} * face {2, 5}
        + face {0, 4} * face {1, 5} * face {2, 3} + face {0, 4} * face {1} * face {2, 3, 5}
        + face {0, 5} * face {1, 2, 3} * face {4} + face {0, 5} * face {1, 2, 4} * face {3}
        + face {0, 5} * face {1, 2} * face {3, 4} + face {0, 5} * face {1, 3, 4} * face {2}
        + face {0, 5} * face {1, 3} * face {2, 4} + face {0, 5} * face {1, 4} * face {2, 3}
        + face {0, 5} * face {1} * face {2, 3, 4} + face {0} * face {1, 2, 3, 4} * face {5}
        + face {0} * face {1, 2, 3, 5} * face {4} + face {0} * face {1, 2, 3} * face {4, 5}
        + face {0} * face {1, 2, 4, 5} * face {3} + face {0} * face {1, 2, 4} * face {3, 5}
        + face {0} * face {1, 2, 5} * face {3, 4} + face {0} * face {1, 2} * face {3, 4, 5}
        + face {0} * face {1, 3, 4, 5} * face {2} + face {0} * face {1, 3, 4} * face {2, 5}
        + face {0} * face {1, 3, 5} * face {2, 4} + face {0} * face {1, 3} * face {2, 4, 5}
        + face {0} * face {1, 4, 5} * face {2, 3} + face {0} * face {1, 4} * face {2, 3, 5}
        + face {0} * face {1, 5} * face {2, 3, 4} + face {0} * face {1} * face {2, 3, 4, 5}
      )
    - 6 * (
        face {0, 1, 2} * face {3} * face {4} * face {5}
        + face {0, 1, 3} * face {2} * face {4} * face {5}
        + face {0, 1, 4} * face {2} * face {3} * face {5}
        + face {0, 1, 5} * face {2} * face {3} * face {4}
        + face {0, 1} * face {2, 3} * face {4} * face {5}
        + face {0, 1} * face {2, 4} * face {3} * face {5}
        + face {0, 1} * face {2, 5} * face {3} * face {4}
        + face {0, 1} * face {2} * face {3, 4} * face {5}
        + face {0, 1} * face {2} * face {3, 5} * face {4}
        + face {0, 1} * face {2} * face {3} * face {4, 5}
        + face {0, 2, 3} * face {1} * face {4} * face {5}
        + face {0, 2, 4} * face {1} * face {3} * face {5}
        + face {0, 2, 5} * face {1} * face {3} * face {4}
        + face {0, 2} * face {1, 3} * face {4} * face {5}
        + face {0, 2} * face {1, 4} * face {3} * face {5}
        + face {0, 2} * face {1, 5} * face {3} * face {4}
        + face {0, 2} * face {1} * face {3, 4} * face {5}
        + face {0, 2} * face {1} * face {3, 5} * face {4}
        + face {0, 2} * face {1} * face {3} * face {4, 5}
        + face {0, 3, 4} * face {1} * face {2} * face {5}
        + face {0, 3, 5} * face {1} * face {2} * face {4}
        + face {0, 3} * face {1, 2} * face {4} * face {5}
        + face {0, 3} * face {1, 4} * face {2} * face {5}
        + face {0, 3} * face {1, 5} * face {2} * face {4}
        + face {0, 3} * face {1} * face {2, 4} * face {5}
        + face {0, 3} * face {1} * face {2, 5} * face {4}
        + face {0, 3} * face {1} * face {2} * face {4, 5}
        + face {0, 4, 5} * face {1} * face {2} * face {3}
        + face {0, 4} * face {1, 2} * face {3} * face {5}
        + face {0, 4} * face {1, 3} * face {2} * face {5}
        + face {0, 4} * face {1, 5} * face {2} * face {3}
        + face {0, 4} * face {1} * face {2, 3} * face {5}
        + face {0, 4} * face {1} * face {2, 5} * face {3}
        + face {0, 4} * face {1} * face {2} * face {3, 5}
        + face {0, 5} * face {1, 2} * face {3} * face {4}
        + face {0, 5} * face {1, 3} * face {2} * face {4}
        + face {0, 5} * face {1, 4} * face {2} * face {3}
        + face {0, 5} * face {1} * face {2, 3} * face {4}
        + face {0, 5} * face {1} * face {2, 4} * face {3}
        + face {0, 5} * face {1} * face {2} * face {3, 4}
        + face {0} * face {1, 2, 3} * face {4} * face {5}
        + face {0} * face {1, 2, 4} * face {3} * face {5}
        + face {0} * face {1, 2, 5} * face {3} * face {4}
        + face {0} * face {1, 2} * face {3, 4} * face {5}
        + face {0} * face {1, 2} * face {3, 5} * face {4}
        + face {0} * face {1, 2} * face {3} * face {4, 5}
        + face {0} * face {1, 3, 4} * face {2} * face {5}
        + face {0} * face {1, 3, 5} * face {2} * face {4}
        + face {0} * face {1, 3} * face {2, 4} * face {5}
        + face {0} * face {1, 3} * face {2, 5} * face {4}
        + face {0} * face {1, 3} * face {2} * face {4, 5}
        + face {0} * face {1, 4, 5} * face {2} * face {3}
        + face {0} * face {1, 4} * face {2, 3} * face {5}
        + face {0} * face {1, 4} * face {2, 5} * face {3}
        + face {0} * face {1, 4} * face {2} * face {3, 5}
        + face {0} * face {1, 5} * face {2, 3} * face {4}
        + face {0} * face {1, 5} * face {2, 4} * face {3}
        + face {0} * face {1, 5} * face {2} * face {3, 4}
        + face {0} * face {1} * face {2, 3, 4} * face {5}
        + face {0} * face {1} * face {2, 3, 5} * face {4}
        + face {0} * face {1} * face {2, 3} * face {4, 5}
        + face {0} * face {1} * face {2, 4, 5} * face {3}
        + face {0} * face {1} * face {2, 4} * face {3, 5}
        + face {0} * face {1} * face {2, 5} * face {3, 4}
        + face {0} * face {1} * face {2} * face {3, 4, 5}
      )
    + 24 * (
        face {0, 1} * face {2} * face {3} * face {4} * face {5}
        + face {0, 2} * face {1} * face {3} * face {4} * face {5}
        + face {0, 3} * face {1} * face {2} * face {4} * face {5}
        + face {0, 4} * face {1} * face {2} * face {3} * face {5}
        + face {0, 5} * face {1} * face {2} * face {3} * face {4}
        + face {0} * face {1, 2} * face {3} * face {4} * face {5}
        + face {0} * face {1, 3} * face {2} * face {4} * face {5}
        + face {0} * face {1, 4} * face {2} * face {3} * face {5}
        + face {0} * face {1, 5} * face {2} * face {3} * face {4}
        + face {0} * face {1} * face {2, 3} * face {4} * face {5}
        + face {0} * face {1} * face {2, 4} * face {3} * face {5}
        + face {0} * face {1} * face {2, 5} * face {3} * face {4}
        + face {0} * face {1} * face {2} * face {3, 4} * face {5}
        + face {0} * face {1} * face {2} * face {3, 5} * face {4}
        + face {0} * face {1} * face {2} * face {3} * face {4, 5}
      )
    - 120 * (face {0} * face {1} * face {2} * face {3} * face {4} * face {5})
/-- A check on the explicit partition list: six positions have `203 = Bell 6` partitions and the
Möbius coefficients `(-1)^(k-1) (k-1)!` sum to zero over them (the partition-lattice identity
`Σ_π μ(π, ⊤) = 0` for `n ≥ 2`). -/
theorem connectedSix_one : connectedSix (fun _ => (1 : ℤ)) = 0 := by
  decide

/-- The joint moment of the positions in `s`, for the tuple of six sites `f`. -/
noncomputable def shellFace6 (m : ℕ) (f : Fin 6 → Fin m) (s : Finset (Fin 6)) : ℝ :=
  ∫ p : Fin m → ℝ, ∏ t ∈ s, p (f t) ∂shellLaw m

/-- A single position has zero moment under the reference law. -/
theorem shellFace6_singleton (m : ℕ) (f : Fin 6 → Fin m) (i : Fin 6) :
    shellFace6 m f {i} = 0 := by
  simp only [shellFace6, Finset.prod_singleton]
  exact integral_shellLaw_coord m (f i)

/-- A block of one position has zero moment. -/
theorem shellFace6_card_one (m : ℕ) (f : Fin 6 → Fin m) {s : Finset (Fin 6)}
    (hs : s.card = 1) : shellFace6 m f s = 0 := by
  obtain ⟨i, rfl⟩ := Finset.card_eq_one.mp hs
  exact shellFace6_singleton m f i

/-- A block of three positions has zero moment under the reference law. -/
theorem shellFace6_card_three (m : ℕ) (f : Fin 6 → Fin m) {s : Finset (Fin 6)}
    (hs : s.card = 3) : shellFace6 m f s = 0 := by
  obtain ⟨a, b, c, hab, hac, hbc, rfl⟩ := Finset.card_eq_three.mp hs
  have hprod : ∀ p : Fin m → ℝ,
      (∏ t ∈ ({a, b, c} : Finset (Fin 6)), p (f t)) = p (f a) * p (f b) * p (f c) := by
    intro p
    rw [Finset.prod_insert (by simp [hab, hac]),
      Finset.prod_insert (by simp [hbc]), Finset.prod_singleton]
    ring
  rw [show shellFace6 m f {a, b, c}
      = ∫ p, p (f a) * p (f b) * p (f c) ∂shellLaw m from
    integral_congr_ae (Eventually.of_forall fun p => hprod p)]
  exact integral_shellLaw_coord_three m (f a) (f b) (f c)

/-- The whole set is the six-point function. -/
theorem shellFace6_univ (m : ℕ) (f : Fin 6 → Fin m) :
    shellFace6 m f Finset.univ
      = ∫ p, p (f 0) * p (f 1) * p (f 2) * p (f 3) * p (f 4) * p (f 5) ∂shellLaw m := by
  simp only [shellFace6]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  simp [Fin.prod_univ_six]

/-- A two-position face is a pair moment. -/
theorem shellFace6_pair (m : ℕ) (f : Fin 6 → Fin m) {a b : Fin 6}
    (h : ({a, b} : Finset (Fin 6)).card = 2) :
    shellFace6 m f {a, b} = ∫ p, p (f a) * p (f b) ∂shellLaw m := by
  have hab : a ≠ b := by
    rintro rfl
    simp at h
  simp only [shellFace6]
  refine integral_congr_ae (Eventually.of_forall fun p => ?_)
  change (∏ t ∈ ({a, b} : Finset (Fin 6)), p (f t)) = p (f a) * p (f b)
  rw [Finset.prod_pair hab]

/-- A four-position face is a four-point function. -/
theorem shellFace6_four (m : ℕ) (f : Fin 6 → Fin m) {a b c d : Fin 6}
    (h : ({a, b, c, d} : Finset (Fin 6)).card = 4) :
    shellFace6 m f {a, b, c, d}
      = ∫ p, p (f a) * p (f b) * p (f c) * p (f d) ∂shellLaw m := by
  have hprod : ∀ p : Fin m → ℝ,
      (∏ t ∈ ({a, b, c, d} : Finset (Fin 6)), p (f t))
        = p (f a) * p (f b) * p (f c) * p (f d) := by
    intro p
    have ha : a ∉ ({b, c, d} : Finset (Fin 6)) := by
      intro hin
      have he : ({a, b, c, d} : Finset (Fin 6)) = {b, c, d} := by
        simpa using Finset.insert_eq_self.mpr hin
      have hle : ({b, c, d} : Finset (Fin 6)).card ≤ 3 := by
        have h1 : ({b, c, d} : Finset (Fin 6)).card ≤ ({c, d} : Finset (Fin 6)).card + 1 :=
          Finset.card_insert_le b ({c, d} : Finset (Fin 6))
        have h2 : ({c, d} : Finset (Fin 6)).card ≤ 2 := by
          have h3 := Finset.card_insert_le c ({d} : Finset (Fin 6))
          simpa using h3
        omega
      rw [he] at h
      omega
    have hb : b ∉ ({c, d} : Finset (Fin 6)) := by
      intro hin
      have he : ({b, c, d} : Finset (Fin 6)) = {c, d} := by
        simpa using Finset.insert_eq_self.mpr hin
      have hEq : ({a, b, c, d} : Finset (Fin 6)).card
          = 1 + ({c, d} : Finset (Fin 6)).card := by
        rw [show ({a, b, c, d} : Finset (Fin 6)) = insert a (insert b {c, d}) from rfl,
          Finset.card_insert_of_notMem ha, he]
        omega
      have h2 : ({c, d} : Finset (Fin 6)).card ≤ 2 := by
        have h3 := Finset.card_insert_le c ({d} : Finset (Fin 6))
        simpa using h3
      omega
    have hc : c ≠ d := by
      intro hcd
      have h2 : ({c, d} : Finset (Fin 6)).card = 1 := by
        rw [show ({c, d} : Finset (Fin 6)) = ({c} : Finset (Fin 6)) by simp [hcd]]
        simp
      have hEq : ({a, b, c, d} : Finset (Fin 6)).card = 3 := by
        rw [show ({a, b, c, d} : Finset (Fin 6)) = insert a (insert b {c, d}) from rfl,
          Finset.card_insert_of_notMem ha, Finset.card_insert_of_notMem hb, h2]
      omega
    rw [show ({a, b, c, d} : Finset (Fin 6)) = insert a (insert b (insert c {d})) from rfl,
      Finset.prod_insert ha, Finset.prod_insert hb,
      Finset.prod_insert (by simpa using hc), Finset.prod_singleton]
    ring
  rw [show shellFace6 m f {a, b, c, d}
      = ∫ p, p (f a) * p (f b) * p (f c) * p (f d) ∂shellLaw m from
    integral_congr_ae (Eventually.of_forall fun p => hprod p)]

/-- **Only the even partitions survive.**  In the Möbius sum over the six positions a block of one
position dies on the vanishing one-point moment, a block of three on the vanishing three-point
moment, and a block of five leaves a singleton.  What remains is the whole set, the fifteen
`4 + 2` partitions and the fifteen `2 + 2 + 2` partitions. -/
theorem connectedSix_eq_reduced {R : Type*} [CommRing R] (face : Finset (Fin 6) → R)
    (h1 : ∀ s, s.card = 1 → face s = 0) (h3 : ∀ s, s.card = 3 → face s = 0) :
    connectedSix face = face Finset.univ
      - (
        face {0, 1, 2, 3} * face {4, 5} + face {0, 1, 2, 4} * face {3, 5}
        + face {0, 1, 2, 5} * face {3, 4} + face {0, 1, 3, 4} * face {2, 5}
        + face {0, 1, 3, 5} * face {2, 4} + face {0, 1, 4, 5} * face {2, 3}
        + face {0, 2, 3, 4} * face {1, 5} + face {0, 2, 3, 5} * face {1, 4}
        + face {0, 2, 4, 5} * face {1, 3} + face {0, 3, 4, 5} * face {1, 2}
        + face {1, 2, 3, 4} * face {0, 5} + face {1, 2, 3, 5} * face {0, 4}
        + face {1, 2, 4, 5} * face {0, 3} + face {1, 3, 4, 5} * face {0, 2}
        + face {2, 3, 4, 5} * face {0, 1}
        )
      + 2 * (
        face {0, 1} * face {2, 3} * face {4, 5} + face {0, 1} * face {2, 4} * face {3, 5}
        + face {0, 1} * face {2, 5} * face {3, 4} + face {0, 2} * face {1, 3} * face {4, 5}
        + face {0, 2} * face {1, 4} * face {3, 5} + face {0, 2} * face {1, 5} * face {3, 4}
        + face {0, 3} * face {1, 2} * face {4, 5} + face {0, 3} * face {1, 4} * face {2, 5}
        + face {0, 3} * face {1, 5} * face {2, 4} + face {0, 4} * face {1, 2} * face {3, 5}
        + face {0, 4} * face {1, 3} * face {2, 5} + face {0, 4} * face {1, 5} * face {2, 3}
        + face {0, 5} * face {1, 2} * face {3, 4} + face {0, 5} * face {1, 3} * face {2, 4}
        + face {0, 5} * face {1, 4} * face {2, 3}
        )
    := by
  simp [connectedSix, h1, h3]
  ring

/-- The connected six-point function of the reference law. -/
noncomputable def connectedSixShell (m : ℕ) (f : Fin 6 → Fin m) : ℝ :=
  connectedSix (shellFace6 m f)

/-- **The connected six-point function of the reference law vanishes.**  The centred law has no
connected six-point part: after the odd blocks drop out, the six-point function and the fifteen
`4 + 2` partitions and the fifteen `2 + 2 + 2` partitions satisfy `1 - 3 + 2 = 0` matching by
matching. -/
theorem connectedSixShell_eq_zero (m : ℕ) (f : Fin 6 → Fin m) :
    connectedSixShell m f = 0 := by
  rw [connectedSixShell,
    connectedSix_eq_reduced _ (fun _ hs => shellFace6_card_one m f hs)
      (fun _ hs => shellFace6_card_three m f hs)]
  rw [shellFace6_univ]
  rw [shellFace6_four m f (a := 0) (b := 1) (c := 2) (d := 3) (by decide),
    shellFace6_four m f (a := 0) (b := 1) (c := 2) (d := 4) (by decide),
    shellFace6_four m f (a := 0) (b := 1) (c := 2) (d := 5) (by decide),
    shellFace6_four m f (a := 0) (b := 1) (c := 3) (d := 4) (by decide),
    shellFace6_four m f (a := 0) (b := 1) (c := 3) (d := 5) (by decide),
    shellFace6_four m f (a := 0) (b := 1) (c := 4) (d := 5) (by decide),
    shellFace6_four m f (a := 0) (b := 2) (c := 3) (d := 4) (by decide),
    shellFace6_four m f (a := 0) (b := 2) (c := 3) (d := 5) (by decide),
    shellFace6_four m f (a := 0) (b := 2) (c := 4) (d := 5) (by decide),
    shellFace6_four m f (a := 0) (b := 3) (c := 4) (d := 5) (by decide),
    shellFace6_four m f (a := 1) (b := 2) (c := 3) (d := 4) (by decide),
    shellFace6_four m f (a := 1) (b := 2) (c := 3) (d := 5) (by decide),
    shellFace6_four m f (a := 1) (b := 2) (c := 4) (d := 5) (by decide),
    shellFace6_four m f (a := 1) (b := 3) (c := 4) (d := 5) (by decide),
    shellFace6_four m f (a := 2) (b := 3) (c := 4) (d := 5) (by decide)]
  rw [shellFace6_pair m f (a := 0) (b := 1) (by decide),
    shellFace6_pair m f (a := 0) (b := 2) (by decide),
    shellFace6_pair m f (a := 0) (b := 3) (by decide),
    shellFace6_pair m f (a := 0) (b := 4) (by decide),
    shellFace6_pair m f (a := 0) (b := 5) (by decide),
    shellFace6_pair m f (a := 1) (b := 2) (by decide),
    shellFace6_pair m f (a := 1) (b := 3) (by decide),
    shellFace6_pair m f (a := 1) (b := 4) (by decide),
    shellFace6_pair m f (a := 1) (b := 5) (by decide),
    shellFace6_pair m f (a := 2) (b := 3) (by decide),
    shellFace6_pair m f (a := 2) (b := 4) (by decide),
    shellFace6_pair m f (a := 2) (b := 5) (by decide),
    shellFace6_pair m f (a := 3) (b := 4) (by decide),
    shellFace6_pair m f (a := 3) (b := 5) (by decide),
    shellFace6_pair m f (a := 4) (b := 5) (by decide)]
  simp only [integral_shellLaw_coord_six, integral_shellLaw_coord_four,
    integral_shellLaw_coord_mul_coord]
  ring

/-- **The connected six-point function at six coordinates vanishes**: the sixth cumulant of
`p_i, p_j, p_k, p_l, p_r, p_s` is zero. -/
theorem connectedSix_coord_eq_zero (m : ℕ) (i j k l r s : Fin m) :
    connectedSix
      (fun t => ∫ p : Fin m → ℝ, ∏ u ∈ t, p (![i, j, k, l, r, s] u) ∂shellLaw m) = 0 :=
  connectedSixShell_eq_zero m ![i, j, k, l, r, s]

/-! ## The joint cumulants of the reference law at every order

The moments and cumulants above are one order at a time.  The same statements hold at *every*
order, and this section proves them: `shellMoment m f s` is the joint moment of the positions in
`s` for the tuple of sites `f`, and

* `shellMoment_eq_wickSum` — **Isserlis' theorem in pairing form at every order**: the moment is
  the `wickSum` of the `δ` covariance `a b ↦ if f a = f b then 1 else 0`.  The proof is the
  general Wick recursion `wick_pi` for linear forms, at the unit vectors of the sites; it does not
  enumerate pairings.
* `shellMoment_empty`, `shellMoment_odd`, `shellMoment_wick` — the three Gaussian hypotheses of
  `cumulant_eq_zero_of_wick`: unit total mass, zero odd moments, and the Wick recursion.
* **`cumulant_shellMoment_eq_zero`** — **every joint cumulant of the reference law of order at
  least three vanishes**, at every order.  This is the general form of
  `connectedFourShell_eq_zero`, `connectedFiveShell_eq_zero` and `connectedSixShell_eq_zero`.
* **`cumulant_seven_eq_zero`** — the seventh cumulant, as the order-seven instance.

The order-six proof needed the explicit cancellation `1 - 3 + 2 = 0` of a matching, because the
surviving `4 + 2` and `2 + 2 + 2` partitions are even.  At odd order the parity argument already
suffices and no cancellation is left: every partition of seven positions has a block of odd
cardinality (`3 + 2 + 2` has its block of three, `5 + 2` its block of five, and the one-block
partition the whole set), and an odd-cardinality moment of this centred law vanishes.  The
`3 + 2 + 2` partitions therefore do not survive the odd-block test; the general theorem covers
them together with every other order.

**Boundary.** The vanishing is proved for this reference law, whose `Finset`-indexed moments are
those of the product standard Gaussian; nothing here characterises Gaussianity, computes a
separated connected correlation, or treats a face function that fails the Wick recursion.
-/

section AllOrders

variable {M : ℕ}

/-- The joint moment of the positions in `s`, for the tuple of sites `f`. -/
noncomputable def shellMoment (m : ℕ) (f : Fin M → Fin m) (s : Finset (Fin M)) : ℝ :=
  ∫ p : Fin m → ℝ, ∏ t ∈ s, p (f t) ∂shellLaw m

/-- **Isserlis' theorem in pairing form at every order**: the moment of the positions in `s` is
the `wickSum` with the `δ` covariance of the site map. -/
theorem shellMoment_eq_wickSum (m : ℕ) (f : Fin M → Fin m) (s : Finset (Fin M)) :
    shellMoment m f s = wickSum (fun a b => if f a = f b then (1 : ℝ) else 0) s := by
  have hfun : ∀ p : Fin m → ℝ, (∏ t ∈ s, p (f t))
      = ∏ j ∈ s, (Pi.single (f j) (1 : ℝ) : Fin m → ℝ) ⬝ᵥ p := by
    intro p
    exact Finset.prod_congr rfl fun j _ => by simp [dotProduct, Pi.single_apply]
  have hw : (fun a b =>
        (Pi.single (f a) (1 : ℝ) : Fin m → ℝ) ⬝ᵥ (Pi.single (f b) (1 : ℝ) : Fin m → ℝ))
      = fun a b => if f a = f b then (1 : ℝ) else 0 := by
    funext a b
    rw [dotProduct]
    by_cases h : f a = f b
    · rw [h]
      simp [Pi.single_apply]
    · have hne : f b ≠ f a := fun hh => h hh.symm
      simp [Pi.single_apply, h, hne]
  rw [shellMoment, shellLaw_eq_productGauss,
    show (∫ p, ∏ t ∈ s, p (f t) ∂productGauss (Fin m))
        = ∫ p, ∏ j ∈ s, (Pi.single (f j) (1 : ℝ) : Fin m → ℝ) ⬝ᵥ p
            ∂productGauss (Fin m) from
      MeasureTheory.integral_congr_ae (Filter.Eventually.of_forall hfun),
    wick_pi (fun j => (Pi.single (f j) (1 : ℝ) : Fin m → ℝ)) s, hw]

/-- The empty set of positions has moment one. -/
theorem shellMoment_empty (m : ℕ) (f : Fin M → Fin m) : shellMoment m f ∅ = 1 := by
  simp [shellMoment]

/-- An odd number of positions has zero moment. -/
theorem shellMoment_odd (m : ℕ) (f : Fin M → Fin m) {s : Finset (Fin M)} (h : Odd s.card) :
    shellMoment m f s = 0 := by
  rw [shellMoment_eq_wickSum]
  exact wickSum_eq_zero_of_odd _ h

/-- **The Wick recursion for the moments of the reference law.** -/
theorem shellMoment_wick (m : ℕ) (f : Fin M → Fin m) {s : Finset (Fin M)} (hs : s.Nonempty) :
    shellMoment m f s = ∑ b ∈ s.erase (s.min' hs),
      (if f (s.min' hs) = f b then (1 : ℝ) else 0) *
        shellMoment m f ((s.erase (s.min' hs)).erase b) := by
  rw [shellMoment_eq_wickSum, wickSum_rec _ hs]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [shellMoment_eq_wickSum]

/-- **All joint cumulants of the reference law of order at least three vanish.** -/
theorem cumulant_shellMoment_eq_zero (m : ℕ) (f : Fin M → Fin m) {s : Finset (Fin M)}
    (h3 : 3 ≤ s.card) : cumulant (shellMoment m f) s = 0 :=
  cumulant_eq_zero_of_wick (shellMoment m f) (fun a b => if f a = f b then (1 : ℝ) else 0)
    (shellMoment_empty m f) (fun _ h => shellMoment_odd m f h)
    (fun _ hs => shellMoment_wick m f hs) s h3

/-- **The seventh cumulant of the reference law vanishes.** -/
theorem cumulant_seven_eq_zero (m : ℕ) (f : Fin 7 → Fin m) :
    cumulant (shellMoment m f) Finset.univ = 0 :=
  cumulant_shellMoment_eq_zero m f (by simp)

end AllOrders

end BookProof.OSReconstruction







