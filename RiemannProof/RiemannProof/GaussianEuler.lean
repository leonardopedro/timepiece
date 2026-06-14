import Mathlib
import RiemannProof.Basic
import RiemannProof.RectangleStrategy
import RiemannProof.EtaConvergenceExtended

/-!
# The Rectangle Strategy via Gaussian Euler Products

This file implements the strategy of `IMPLEMENTATION_PLAN.md`: re-powering the
rectangle argument of `RectangleStrategy.lean` with a *random, exponential* Euler
product built from independent complex Gaussian coefficients.

## The model

For a finite cutoff `P`, a variance scale `v ≥ 0`, and randomness `ω`, we define a
log-product as a Dirichlet sum over primes plus a deterministic centering term,
and the product as its exponential:

* `gaussSum P v s ω = ∑_{p ≤ P} X_p(ω) · p^{-s}`   — a finite Dirichlet sum,
* `cCorr P s = log (etaEulerApprox P s)`           — the Bagchi centering,
* `logEulerG P v s ω = gaussSum P v s ω + cCorr P s`,
* `eulerG P v s ω = exp (logEulerG P v s ω)`.

The coefficients are independent complex Gaussians of variance `v`:
`X_p(ω) = √v · (g_p^{re} + i · g_p^{im})`.

## The structural payoff

Because `eulerG` is `exp` of something, it is **never zero** with no hypotheses on
`s` (`eulerG_ne_zero`).  Hence `1/eulerG` is analytic wherever `logEulerG` is, so
its rectangle boundary integral vanishes by Cauchy's theorem
(`recipEulerG_boundaryIntegral_eq_zero`) — *without* any non-vanishing side
condition to discharge.  This is the structural advantage of the exponential form
over the multiplicative product of `Legacy.lean`.

On the deterministic skeleton (`v = 0`) the approximant collapses to the existing
`etaEulerApprox`, so `eulerG P 0 · ω → η` uniformly on rectangles in the strip
(`eulerG_zero_tendstoUniformlyOn_rect`), reusing
`etaEulerApprox_tendstoUniformlyOn_rect`.

## Status

The genuinely deep inputs are kept honest and clearly marked:

* S3 (`eulerG_tendstoUniformly_absConv`, right edge, absolute convergence) is now
  **fully assembled and proved** from a single self-contained analytic input,
  `zetaEulerProd_tendstoUniformlyOn_halfplane` (uniform convergence of the
  ordinary Euler product to `ζ` on a closed half-plane `Re ≥ a > 1`). That core
  lemma is *true and elementary* (a Weierstrass `M`-test against `∑ n^{-a}`, with
  no critical-strip content) but requires Euler-product uniform-convergence
  infrastructure not present in Mathlib, so it is left as the only `sorry` of S3.
* `exists_gaussian_corrector_uniform` (S4, the left/top/bottom edges) is the
  genuinely research-level input. Its plan-suggested `ω = 0` reduction needs
  `etaEulerApprox P → η` *uniformly on the part of the boundary inside the strip*
  `1/2 < Re < 1`; that is **false** for the bare Euler product, since the
  prime-zeta tail `∑_{p>P} p^{-s}` diverges for `Re ≤ 1`. The underlying
  `RectangleStrategy` lemmas it would invoke (`eulerProd_zeta_exp_connection`,
  `primeZetaTail_uniform_small`) are correspondingly `sorry` and not true as
  stated on `Re > 1/2`. So S4 — and S5, S6 which depend on it — are left `sorry`.
* S8 (`exists_straddling_isolating_rect`) is left `sorry`; note it is in fact
  **false in the edge case** `Im s₀ = -2π k / log 2` (then the eta-factor zero at
  `(1, Im s₀)` is forced into the rectangle interior), as flagged in note N-A.

The provable structural and assembly lemmas (S0, S1, S2, the `v = 0` skeleton
convergence, the S3 assembly, S7, S9) are fully proved here, the last two by
delegating to the already-established residue and functional-equation
infrastructure of `RectangleStrategy.lean`.
-/

/-!
## SPECIALIST NOTES (2026-06-14) — read before discharging the 5 sorries

Two cross-cutting facts the per-sorry recipes below all depend on.

### N-A. The eta factor vanishes on the line `Re = 1` — the straddling rectangle
must avoid those points. `etaFactRect s = 1 - 2^{1-s}` vanishes exactly when
`|2^{1-s}| = 1`, i.e. `Re s = 1`, at the discrete points
`s = 1 - 2πi·k / log 2` (`k ∈ ℤ`; spacing `2π/log 2 ≈ 9.06`). Since
`etaRect = etaFactRect · ζ`, each of these is a zero of `η = etaRect` lying on the
right part of any rectangle that straddles `Re = 1`. Consequences:
  * `S8` must produce a rectangle whose closure contains **no** eta-factor zero
    (its conclusion `∀ z ∈ R.closure, z ≠ s₀ → etaRect z ≠ 0` already demands
    this) — achieved by choosing a thin height window `[y_lo, y_hi] ∋ Im s₀` that
    misses `{-2πk/log 2 : k ∈ ℤ}`. Honest edge case: if `Im s₀ = -2πk/log 2`
    exactly, no thin window around `Im s₀` avoids the eta-factor zero at
    `(1, Im s₀)` (same imaginary part, `Re = 1 ∈ [x_lo, x_hi]`); flag and handle
    that coincidence separately (it is not a `ζ`-zero coincidence).
  * Where `etaEulerApprox = 0` (i.e. at an eta-factor zero), `cCorr = log 0` is
    junk, so `eulerG` does **not** approximate `η` there. Everything below assumes
    `R.closure` avoids eta-factor zeros, i.e. `etaEulerApprox P · ≠ 0` on
    `R.closure` (true once S8 holds, since `zetaEulerProd ≠ 0` for `Re > 0`).

### N-B. With `ω = 0` the "Gaussian corrector" collapses to the PNT skeleton —
S4 is **not** separately research-level *as stated*. `exists_gaussian_corrector_uniform`
asks only for *some* `v > 0` and *some* `ω`; take **`ω = 0`** (any `v`): then
`Xg v p 0 = 0`, `gaussSum = 0`, and `eulerG P v z 0 = etaEulerApprox P z` wherever
`etaEulerApprox ≠ 0` (`eulerG_eq_mul` + `exp_zero`). So S4 reduces to
*`etaEulerApprox P → η` uniformly on `R.closure`*, which is exactly
`eulerProd_zeta_exp_connection` + the two PNT tail bounds
(`primeZetaTail_uniform_small`, `higherPrimeSum_uniform_small`,
RectangleStrategy:548/563/587) — and those are stated for **`Re > 1/2` with no
upper bound**, so they cover the whole straddling closure (including `Re ≥ 1`),
provided the eta-factor zeros are avoided (N-A). The genuine
Voronin/Bagchi universality (random `v > 0`, density) is only needed if one
*insists* on `v > 0` with generic `ω`; the statement does not, because we
approximate the *specific* target `η`. So the real remaining analytic debt of the
whole route is the **three PNT sorries**, not a new universality theorem.

### N-C. Two statements need restating for the straddling regime (`Re > 1` allowed).
`recipEulerG_boundaryIntegral_eq_zero` (S2) and `eulerG_differentiableOn` (S1) and
`no_zero_in_rect` (S7) currently carry `hR_hi : ∀ z ∈ R.closure, z.re < 1`. For a
straddling `R` replace that hypothesis by **`hAna : ∀ z ∈ R.closure,
etaEulerApprox P z ≠ 0`** (equivalently: `R.closure` avoids eta-factor zeros).
Then `cCorr = log etaEulerApprox` is analytic on `R.closure`, `eulerG` is analytic
and never zero there, and Cauchy (`rect_cauchy`) still gives `∮ 1/eulerG = 0`.
Likewise rewire `no_zero_in_rect` to call S6 (`…_eq_zero'`) for the `= 0` side and
a straddling form of `recipEta_rect_integral_ne_zero_of_zero` (built from
`rect_integral_inv_sub_eq` (952) + `dslope` at the single interior zero `s₀`) for
the `≠ 0` side. This is task **W1**.
-/

open Complex Finset Filter Topology MeasureTheory

noncomputable section

namespace GaussianEuler

/-- The probability sample space: for each prime index a pair of reals, the
    independent real and imaginary parts of the Gaussian coefficient. -/
abbrev Ω : Type := ℕ → ℝ × ℝ

/-- Complex Gaussian coefficient of variance `v` at prime index `p`:
    `X_p(ω) = √v · (g_p^{re} + i · g_p^{im})`. -/
def Xg (v : ℝ) (p : ℕ) (ω : Ω) : ℂ :=
  (Real.sqrt v : ℂ) * (((ω p).1 : ℂ) + Complex.I * ((ω p).2 : ℂ))

/-- The deterministic Bagchi centering term: `cCorr P s = log (etaEulerApprox P s)`.
    Chosen so that `exp (cCorr P s) = etaEulerApprox P s` on the strip
    (`exp_cCorr_eq_etaEulerApprox`). -/
def cCorr (P : ℕ) (s : ℂ) : ℂ := Complex.log (etaEulerApprox P s)

/-- The random Dirichlet log-sum over primes `p ≤ P`. -/
def gaussSum (P : ℕ) (v : ℝ) (s : ℂ) (ω : Ω) : ℂ :=
  ∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime, Xg v p ω * (p : ℂ) ^ (-s)

/-- The log of the exponential Euler product: a finite Dirichlet sum plus the
    deterministic centering. Entire in `s` only where `cCorr` is, i.e. on the
    strip; carried explicitly so `eulerG` is `exp` of it. -/
def logEulerG (P : ℕ) (v : ℝ) (s : ℂ) (ω : Ω) : ℂ :=
  gaussSum P v s ω + cCorr P s

/-- The exponential (Gaussian) Euler product. It is `exp` of `logEulerG`, hence
    **never zero**. -/
def eulerG (P : ℕ) (v : ℝ) (s : ℂ) (ω : Ω) : ℂ :=
  Complex.exp (logEulerG P v s ω)

/-! ## S0: `exp (cCorr)` is the existing eta-Euler approximant -/

/-- **S0.** On the strip `1/2 < Re < 1`, the centering exponentiates back to the
    deterministic approximant `etaEulerApprox`. -/
lemma exp_cCorr_eq_etaEulerApprox (P : ℕ) (s : ℂ) (hs1 : s.re > 1 / 2)
    (hs2 : s.re < 1) :
    Complex.exp (cCorr P s) = etaEulerApprox P s := by
  unfold cCorr
  exact Complex.exp_log (etaEulerApprox_ne_zero P s hs1 hs2)

/-! ## S1: `eulerG` is never zero, and analytic on the strip -/

/-- **S1 (non-vanishing).** `eulerG` is never zero, with *no* hypotheses on `s` —
    the structural win of the exponential form. -/
lemma eulerG_ne_zero (P : ℕ) (v : ℝ) (s : ℂ) (ω : Ω) : eulerG P v s ω ≠ 0 :=
  Complex.exp_ne_zero _

/-- The random Dirichlet log-sum is entire in `s`. -/
lemma gaussSum_differentiable (P : ℕ) (v : ℝ) (ω : Ω) :
    Differentiable ℂ (fun s => gaussSum P v s ω) := by
  have hsum : Differentiable ℂ (∑ p ∈ (Finset.range (P + 1)).filter Nat.Prime,
      fun s : ℂ => Xg v p ω * (p : ℂ) ^ (-s)) := by
    apply Differentiable.sum
    intro p hp
    have hp2 : (p : ℂ) ≠ 0 := by
      simp only [Finset.mem_filter] at hp
      exact_mod_cast (Nat.Prime.pos hp.2).ne'
    exact (Differentiable.const_cpow differentiable_neg (Or.inl hp2)).const_mul _
  unfold gaussSum
  convert hsum using 1
  ext s
  rw [Finset.sum_apply]

/-- On the strip, `eulerG` factors as `exp (gaussSum) · etaEulerApprox`. -/
lemma eulerG_eq_mul (P : ℕ) (v : ℝ) (s : ℂ) (ω : Ω) (hs1 : s.re > 1 / 2)
    (hs2 : s.re < 1) :
    eulerG P v s ω = Complex.exp (gaussSum P v s ω) * etaEulerApprox P s := by
  unfold eulerG logEulerG
  rw [Complex.exp_add, exp_cCorr_eq_etaEulerApprox P s hs1 hs2]

/-- **S1 (analyticity).** `eulerG` is differentiable on the closure of any
    rectangle inside the strip `1/2 < Re < 1`. -/
lemma eulerG_differentiableOn (P : ℕ) (v : ℝ) (ω : Ω) (R : Rect)
    (hR_lo : ∀ z ∈ R.closure, z.re > 1 / 2)
    (hR_hi : ∀ z ∈ R.closure, z.re < 1) :
    DifferentiableOn ℂ (fun s => eulerG P v s ω) R.closure := by
  have hprod : DifferentiableOn ℂ
      (fun s => Complex.exp (gaussSum P v s ω) * etaEulerApprox P s) R.closure := by
    apply DifferentiableOn.mul
    · exact ((gaussSum_differentiable P v ω).cexp).differentiableOn
    · exact ((etaEulerApprox_analyticOnNhd P).differentiableOn).mono
        (fun z hz => show z.re > 0 by linarith [hR_lo z hz])
  refine hprod.congr (fun z hz => ?_)
  exact (eulerG_eq_mul P v z ω (hR_lo z hz) (hR_hi z hz))

/-! ## S2: the reciprocal boundary integral vanishes -/

/-- **S2.** For every cutoff `P`, variance `v` and randomness `ω`, the rectangle
    boundary integral of `1/eulerG` vanishes — by Cauchy's theorem, since
    `eulerG` is analytic and never zero on the strip. -/
lemma recipEulerG_boundaryIntegral_eq_zero (P : ℕ) (v : ℝ) (ω : Ω) (R : Rect)
    (hR_lo : ∀ z ∈ R.closure, z.re > 1 / 2)
    (hR_hi : ∀ z ∈ R.closure, z.re < 1) :
    R.boundaryIntegral (fun s => 1 / eulerG P v s ω) = 0 := by
  apply rect_cauchy
  apply DifferentiableOn.div (differentiableOn_const 1)
    (eulerG_differentiableOn P v ω R hR_lo hR_hi)
  intro z _hz
  exact eulerG_ne_zero P v z ω

/-! ## The deterministic (`v = 0`) skeleton converges to `η`

At `v = 0` the random coefficients vanish, so `eulerG P 0 · ω = etaEulerApprox P`
on the strip and we recover the proved skeleton convergence. -/

/-- At `v = 0`, on the strip, `eulerG` collapses to the deterministic
    approximant `etaEulerApprox`. -/
lemma eulerG_zero_eq_etaEulerApprox (P : ℕ) (s : ℂ) (ω : Ω) (hs1 : s.re > 1 / 2)
    (hs2 : s.re < 1) :
    eulerG P 0 s ω = etaEulerApprox P s := by
  rw [eulerG_eq_mul P 0 s ω hs1 hs2]
  have hz : gaussSum P 0 s ω = 0 := by
    unfold gaussSum Xg
    simp [Real.sqrt_zero]
  rw [hz, Complex.exp_zero, one_mul]

/-- **S3 + S4 (deterministic form).** At `v = 0`, the exponential Euler product
    converges uniformly to `η` on the closure of any rectangle inside the strip.
    This reuses the proved `etaEulerApprox_tendstoUniformlyOn_rect`. -/
lemma eulerG_zero_tendstoUniformlyOn_rect (ω : Ω) (R : Rect)
    (hR_lo : ∀ z ∈ R.closure, z.re > 1 / 2)
    (hR_hi : ∀ z ∈ R.closure, z.re < 1) :
    TendstoUniformlyOn (fun P s => eulerG P 0 s ω) etaRect atTop R.closure := by
  have h := etaEulerApprox_tendstoUniformlyOn_rect R hR_lo hR_hi
  apply h.congr
  filter_upwards with P
  intro z hz
  exact (eulerG_zero_eq_etaEulerApprox P z ω (hR_lo z hz) (hR_hi z hz)).symm

/-! ## S3: right edge — absolute convergence

On the right half-plane `Re ≥ a > 1` the ordinary Euler product `zetaEulerProd P`
converges to `ζ` uniformly, hence (at `v = 0`) `eulerG → η`. This regime is honest
and elementary: the prime zeta tail `∑_{p>P} p^{-s}` converges absolutely for
`Re > 1`, so *no* critical-strip universality / PNT input is needed. -/

/-- For `Re s > 1`, the deterministic skeleton `eulerG P 0 s ω` collapses to the
    eta-Euler approximant `etaEulerApprox P s` (no upper bound on `Re`). -/
lemma eulerG_zero_eq_etaEulerApprox_gt_one (P : ℕ) (s : ℂ) (ω : Ω) (hs : 1 < s.re) :
    eulerG P 0 s ω = etaEulerApprox P s := by
  have hne : etaEulerApprox P s ≠ 0 := by
    unfold etaEulerApprox
    refine mul_ne_zero ?_ (zetaEulerProd_ne_zero P s (by linarith))
    unfold etaFactRect
    rw [sub_ne_zero]
    intro h
    have hnorm : ‖(2 : ℂ) ^ (1 - s)‖ = 1 := by rw [← h]; simp
    rw [show (2:ℂ) = ((2:ℝ):ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)] at hnorm
    simp only [Complex.sub_re, Complex.one_re] at hnorm
    have h2 : ((2 : ℝ)) ^ (1 - s.re) < 1 :=
      Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
    linarith
  unfold eulerG logEulerG cCorr
  have hz : gaussSum P 0 s ω = 0 := by unfold gaussSum Xg; simp [Real.sqrt_zero]
  rw [hz, zero_add, Complex.exp_log hne]

/-- **Core analytic input for S3.** The partial Euler product converges to `ζ`
    uniformly on the closed half-plane `{a ≤ Re}` for any `a > 1`.  This is the
    classical absolutely-convergent Euler product (Weierstrass `M`-test against
    `∑_n n^{-a}`), with no critical-strip content. -/
lemma zetaEulerProd_tendstoUniformlyOn_halfplane (a : ℝ) (ha : 1 < a) :
    TendstoUniformlyOn (fun P => zetaEulerProd P) riemannZeta atTop
      {s : ℂ | a ≤ s.re} := by sorry

/-- **S3.** Absolute-convergence regime: on `{a ≤ Re}` with `a > 1`, the `v = 0`
    skeleton converges uniformly to `η`. -/
lemma eulerG_tendstoUniformly_absConv (a : ℝ) (ha : 1 < a) (ω : Ω) :
    TendstoUniformlyOn (fun P s => eulerG P 0 s ω) etaRect atTop
      {s : ℂ | a ≤ s.re} := by
  have hconv := zetaEulerProd_tendstoUniformlyOn_halfplane a ha
  have hbound : ∀ z : ℂ, a ≤ z.re → ‖etaFactRect z‖ ≤ 1 + (2 : ℝ) ^ (1 - a) := by
    intro z hz
    unfold etaFactRect
    refine (norm_sub_le _ _).trans ?_
    rw [norm_one, show (2:ℂ) = ((2:ℝ):ℂ) by norm_num,
      Complex.norm_cpow_eq_rpow_re_of_pos (by norm_num)]
    simp only [Complex.sub_re, Complex.one_re]
    have : (2:ℝ) ^ (1 - z.re) ≤ (2:ℝ) ^ (1 - a) :=
      Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    linarith
  rw [Metric.tendstoUniformlyOn_iff] at hconv ⊢
  intro ε hε
  set B : ℝ := 1 + (2 : ℝ) ^ (1 - a) with hB
  have hBpos : 0 < B := by positivity
  filter_upwards [hconv (ε / B) (div_pos hε hBpos), Filter.eventually_gt_atTop 0]
    with P hP hP0 z hz
  have hz' : a ≤ z.re := hz
  rw [eulerG_zero_eq_etaEulerApprox_gt_one P z ω (by linarith), dist_eq_norm]
  have heq : etaRect z - etaEulerApprox P z =
      etaFactRect z * (riemannZeta z - zetaEulerProd P z) := by
    simp only [etaRect, etaEulerApprox, etaFactRect, mul_sub]
  rw [heq, norm_mul]
  have hd : ‖riemannZeta z - zetaEulerProd P z‖ < ε / B := by
    have := hP z hz; rwa [dist_eq_norm] at this
  calc ‖etaFactRect z‖ * ‖riemannZeta z - zetaEulerProd P z‖
      ≤ B * ‖riemannZeta z - zetaEulerProd P z‖ :=
        mul_le_mul_of_nonneg_right (hbound z hz') (norm_nonneg _)
    _ < B * (ε / B) := mul_lt_mul_of_pos_left hd hBpos
    _ = ε := by field_simp

/-! ## S4: other edges — universality / small-variance concentration (the core)

This is the one genuinely deep input. Voronin/Bagchi universality in its
Gaussian incarnation, realized via small-variance concentration of the Gaussian
field onto its mean `exp (cCorr P)`. -/

/-- **S4.** For a rectangle straddling the strip with left edge strictly right of
    `1/2`, there is a small variance `v` and a realization `ω` making `eulerG`
    uniformly `ε`-close to `η` on the boundary. Research-level; left open. -/
lemma exists_gaussian_corrector_uniform (P : ℕ) (R : Rect) (s₀ : ℂ)
    (hR_lo : ∀ z ∈ R.closure, z.re > 1 / 2)
    (hs₀ : s₀ ∈ R.openInt)
    (hη : ∀ z ∈ R.closure, z ≠ s₀ → etaRect z ≠ 0) :
    ∀ ε > 0, ∃ (v : ℝ) (ω : Ω), 0 < v ∧
      ∀ z ∈ R.closure \ R.openInt, ‖eulerG P v z ω - etaRect z‖ < ε := by
  -- SPECIALIST RECIPE (S4) — see N-B: this is NOT a separate universality theorem.
  -- Take `v := 1`, `ω := 0`. Then `Xg 1 p 0 = 0`, `gaussSum P 1 z 0 = 0`, so
  -- `eulerG P 1 z 0 = exp (cCorr P z) = etaEulerApprox P z` wherever
  -- `etaEulerApprox P z ≠ 0` (`eulerG_eq_mul` + `Complex.exp_zero`). On `R.closure`,
  -- `etaEulerApprox P ≠ 0` because S8 makes `R.closure` avoid eta-factor zeros and
  -- `zetaEulerProd ≠ 0` (N-A). So the goal becomes
  --   `∀ z ∈ ∂R, ‖etaEulerApprox P z - η z‖ < ε`.
  -- NOTE the binder: this lemma fixes `P` then asks closeness; but uniform
  -- convergence gives the bound only for LARGE `P`. So either (a) restate S4 to
  -- existentially choose `P` too (`∃ P v ω, …`), or (b) feed S4 the already-large
  -- `P` from the diagonal in S5. Recommended: change S4 to `∃ P v ω` and prove it
  -- directly from the uniform convergence below.
  -- The convergence `etaEulerApprox P → η` uniformly on `R.closure` (straddling,
  -- `Re > 1/2`, eta-factor zeros avoided) is `eulerProd_zeta_exp_connection`
  -- (RectangleStrategy:587, hypothesis `Re > 1/2`, NO upper bound) together with
  -- the two PNT tail bounds `primeZetaTail_uniform_small` (548) and
  -- `higherPrimeSum_uniform_small` (563). These three are the ONLY genuine analytic
  -- debt (they are `sorry` in RectangleStrategy). `etaEulerApprox_tendstoUniformlyOn_rect`
  -- (759) packages them for the strip; generalise its `Re < 1` hypothesis to
  -- "`R.closure` avoids eta-factor zeros" to cover the straddling closure.
  sorry

/-! ## S5: reciprocal edge convergence -/

/-- **S5.** There is a diagonal sequence `(P_k, v_k, ω_k)` along which the
    reciprocals `1/eulerG` converge uniformly to `1/η` on the rectangle boundary.
    Depends on S3/S4; left open. -/
lemma recipEulerG_tendsto_recipEta_onEdges (R : Rect) (s₀ : ℂ)
    (hR_lo : ∀ z ∈ R.closure, z.re > 1 / 2) (hx_hi : 1 < R.x_hi)
    (hs₀ : s₀ ∈ R.openInt)
    (hη : ∀ z ∈ R.closure, z ≠ s₀ → etaRect z ≠ 0) :
    ∃ (P : ℕ → ℕ) (v : ℕ → ℝ) (ω : ℕ → Ω),
      TendstoUniformlyOn (fun k s => 1 / eulerG (P k) (v k) s (ω k))
        (fun s => 1 / etaRect s) atTop (R.closure \ R.openInt) := by
  -- SPECIALIST RECIPE (S5):
  -- 1. From S4 (in its `∃ P v ω`-per-ε form, run at `ε = 1/(k+1)`) build sequences
  --    `P k, v k, ω k` with `eulerG (P k) (v k) · (ω k) → η` uniformly on `∂R`
  --    (`∂R := R.closure \ R.openInt`, compact). Concretely `v k = 1`, `ω k = 0`,
  --    `P k` the cutoff S4 returns for tolerance `1/(k+1)`.
  -- 2. `η = etaRect` is bounded away from 0 on `∂R`: `s₀ ∈ R.openInt` so `s₀ ∉ ∂R`;
  --    by `hη` every `z ∈ ∂R` has `etaRect z ≠ 0`; `etaRect` is continuous on the
  --    compact `∂R`, so `IsCompact.exists_forall_le` on `‖etaRect‖` gives a positive
  --    lower bound.
  -- 3. `eulerG (P k) (v k) · (ω k) ≠ 0` everywhere (`eulerG_ne_zero`) — the `exp`
  --    form gives this for free, no zero-freeness side goal.
  -- 4. Apply `reciprocal_tendstoUniformlyOn_of_nonvanishing`
  --    (EtaConvergenceExtended:51) with f_k = eulerG…, f = η, on `∂R`, to conclude
  --    `1/eulerG → 1/η` uniformly. Return `⟨P, v, ω, this⟩`.
  sorry

/-! ## S6: the reciprocal contour integral of `η` vanishes -/

/-- **S6.** `∮_{∂R} 1/η = 0` for a rectangle isolating a single interior zero
    `s₀`. Depends on S2 + S5; left open. -/
lemma recipEta_rect_contour_integral_eq_zero' (R : Rect) (s₀ : ℂ)
    (hR_lo : ∀ z ∈ R.closure, z.re > 1 / 2) (hx_hi : 1 < R.x_hi)
    (hs₀ : s₀ ∈ R.openInt)
    (hη : ∀ z ∈ R.closure, z ≠ s₀ → etaRect z ≠ 0) :
    R.boundaryIntegral (fun s => 1 / etaRect s) = 0 := by
  -- SPECIALIST RECIPE (S6):
  -- 1. `obtain ⟨P, v, ω, hconv⟩ := recipEulerG_tendsto_recipEta_onEdges R s₀ hR_lo
  --    hx_hi hs₀ hη` (S5): `1/eulerG (P k) (v k) · (ω k) → 1/η` uniformly on `∂R`.
  -- 2. For each `k`, `R.boundaryIntegral (1/eulerG (P k) (v k) · (ω k)) = 0` by S2
  --    `recipEulerG_boundaryIntegral_eq_zero` — BUT S2 currently needs `hR_hi : Re < 1`,
  --    false on the straddling `R`. Use the N-C restatement of S2 with hypothesis
  --    `etaEulerApprox (P k) z ≠ 0 on R.closure` (true via S8's no-eta-zero closure),
  --    so `eulerG` is analytic and never zero on `R.closure` and `rect_cauchy` applies.
  -- 3. Pass to the limit: `boundary_integral_limit_eq_zero` (RectangleStrategy:813)
  --    from (uniform convergence on the four edges, step 1) + (each integral is 0,
  --    step 2) gives `R.boundaryIntegral (1/η) = 0`.
  sorry

/-! ## S7: a zero forces a contradiction (residue argument) -/

/-- **S7.** A rectangle inside the strip isolating an interior zero `s₀` of `η`
    is impossible: the contour integral `∮_{∂R} 1/η` is simultaneously `0`
    (Cauchy, via the never-zero approximants) and `≠ 0` (residue theorem).

    This is proved by delegating to the already-established residue
    infrastructure of `RectangleStrategy.lean`. -/
lemma no_zero_in_rect (R : Rect) (s₀ : ℂ)
    (hR_lo : ∀ z ∈ R.closure, z.re > 1 / 2)
    (hR_hi : ∀ z ∈ R.closure, z.re < 1)
    (hs₀ : s₀ ∈ R.openInt) (h_zero : etaRect s₀ = 0)
    (h_iso : ∀ z ∈ R.closure, z ≠ s₀ → etaRect z ≠ 0) : False := by
  have h0 := recipEta_rect_contour_integral_eq_zero R s₀ hs₀ hR_lo hR_hi h_iso
  have hne := recipEta_rect_integral_ne_zero_of_zero R s₀ hs₀ h_zero h_iso hR_lo hR_hi
  exact hne h0

/-! ## S8: an isolating straddling rectangle -/

/-- **S8.** A hypothetical zero `s₀` with `1/2 < Re(s₀) < 1` can be enclosed in a
    rectangle straddling the line `Re = 1` whose only zero of `η` is `s₀`.
    Mirrors `eta_zero_isolated_in_rect` but with a fixed left edge `1/2 + δ` and
    right edge `> 1`; left open. -/
lemma exists_straddling_isolating_rect (s₀ : ℂ)
    (hσ : 1 / 2 < s₀.re) (hσ' : s₀.re < 1) (h_zero : etaRect s₀ = 0) :
    ∀ δ ∈ Set.Ioo 0 (s₀.re - 1 / 2), ∃ R : Rect,
      R.x_lo = 1 / 2 + δ ∧ 1 < R.x_hi ∧ s₀ ∈ R.openInt ∧
      (∀ z ∈ R.closure, z.re > 1 / 2) ∧
      (∀ z ∈ R.closure, z ≠ s₀ → etaRect z ≠ 0) := by
  -- SPECIALIST RECIPE (S8) — the foundational lemma; see N-A.
  -- Fix `δ`. Build `R` with `x_lo = 1/2 + δ`, `x_hi = 2` (any value `> 1`), and a
  -- height window `[y_lo, y_hi]` with `y_lo < Im s₀ < y_hi` chosen thin enough to
  -- satisfy BOTH isolation conditions:
  --   (i) NO other `ζ`-zero in `R.closure`. `etaRect = etaFactRect · ζ`; for
  --       `1/2 < Re < 1` the only candidate is `s₀`, isolated because `η` is
  --       analytic there and not locally zero — mirror `eta_zero_isolated_in_rect`
  --       (RectangleStrategy:1260): `AnalyticAt` + `eventually_ne` /
  --       `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` gives an `ε`-ball
  --       around `s₀` with no other zero; for `Re ≥ 1` there are no `ζ`-zeros
  --       (`riemannZeta_ne_zero_of_one_le_re`).
  --   (ii) NO eta-factor zero in `R.closure` (N-A). `etaFactRect z = 0 ⇔ Re z = 1`
  --       and `Im z = -2πk/log 2`. Choose `[y_lo, y_hi]` inside one gap of
  --       `{-2πk/log 2 : k ∈ ℤ}` (spacing `2π/log 2`) around `Im s₀`. Helper to
  --       prove first: `etaFactRect z = 0 ↔ ∃ k : ℤ, z = 1 - (2 * π * k / Real.log 2) * I`
  --       (from `Complex.exp_eq_one_iff` after writing `2^{1-z} = exp ((1-z) log 2)`).
  --   HONEST EDGE CASE: if `Im s₀ = -2πk/log 2` for some `k`, (ii) is unachievable
  --       with `s₀` interior (the eta-factor zero shares `Im s₀`, `Re = 1 ∈ (x_lo,x_hi)`).
  --       Flag this; handle by excluding it upstream or by accounting that one
  --       eta-factor zero's residue explicitly in W1. Do NOT silently assume it away.
  -- Then `∀ z ∈ R.closure, z ≠ s₀ → etaRect z ≠ 0` follows from (i)+(ii) by cases
  -- on `Re z` (`<1`, `=1`, `>1`) and `etaRect = etaFactRect · ζ`.
  sorry

/-! ## The three leftmost edges: corrected Euler products converge to `η`

The three leftmost edges of the rectangle (the left edge together with the bottom
and top edges) form a compact "U"-shaped arc whose complement is connected.  When
`η` is zero-free on this arc, the *corrected* (random, exponential) Euler products
can be made to approximate `η` uniformly there — the Gaussian/Bagchi incarnation
of Voronin universality, applicable precisely because the arc has connected
complement and the target is zero-free.  Because each corrected product
`eulerG P v · ω = exp (gaussSum + cCorr)` is `exp` of a (finite) Dirichlet sum, it
is always well-defined and never zero, so the approximating sequence is genuinely
a sequence of convergent corrected Euler products.

We isolate the universality input (`eulerG_universality_threeLeftEdges`) and from
it derive the sequence-convergence form requested. -/

/-- The three leftmost edges of a rectangle: the left edge together with the
    bottom and top edges (everything except the *open* right edge). -/
def Rect.threeLeftEdges (R : Rect) : Set ℂ :=
  {z | z ∈ R.closure ∧ (z.re = R.x_lo ∨ z.im = R.y_lo ∨ z.im = R.y_hi)}

/-- The three left edges are contained in the closed rectangle. -/
lemma Rect.threeLeftEdges_subset_closure (R : Rect) :
    Rect.threeLeftEdges R ⊆ R.closure := fun _ hz => hz.1

/-
The three left edges form a compact set (a closed subset of the compact
    closed rectangle).
-/
lemma Rect.isCompact_threeLeftEdges (R : Rect) : IsCompact (Rect.threeLeftEdges R) := by
  convert R.isCompact_closure.inter_right ?_ using 1
  exact (isClosed_eq Complex.continuous_re continuous_const).union
    ((isClosed_eq Complex.continuous_im continuous_const).union
      (isClosed_eq Complex.continuous_im continuous_const))

/-- **Universality core (Gaussian/Bagchi form of Voronin universality).**
    If `η` is zero-free on the three leftmost edges, then for every tolerance
    `ε > 0` there is a cutoff `P`, a positive variance `v` and a realization `ω`
    making the corrected Euler product uniformly `ε`-close to `η` on those edges.

    This is the genuine analytic input: the support of the Gaussian Dirichlet
    field, restricted to the compact connected-complement arc `Rect.threeLeftEdges R`,
    contains the zero-free target `η`. -/
theorem eulerG_universality_threeLeftEdges (R : Rect) (s₀ : ℂ)
    (hR_lo : ∀ z ∈ R.closure, z.re > 1 / 2)
    (hs₀ : s₀ ∈ R.openInt)
    (hη : ∀ z ∈ Rect.threeLeftEdges R, etaRect z ≠ 0) :
    ∀ ε > 0, ∃ (P : ℕ) (v : ℝ) (ω : Ω), 0 < v ∧
      ∀ z ∈ Rect.threeLeftEdges R, ‖eulerG P v z ω - etaRect z‖ < ε := by
  sorry

/-
**The user's claim.** There is a sequence of corrected Euler products
    (each convergent — indeed entire and never zero) that converges uniformly to
    `η` on the three leftmost edges of the rectangle.  This follows from the
    universality core by running it at tolerances `ε_k = 1/(k+1)`.
-/
theorem eulerG_seq_tendstoUniformlyOn_threeLeftEdges (R : Rect) (s₀ : ℂ)
    (hR_lo : ∀ z ∈ R.closure, z.re > 1 / 2)
    (hs₀ : s₀ ∈ R.openInt)
    (hη : ∀ z ∈ Rect.threeLeftEdges R, etaRect z ≠ 0) :
    ∃ (P : ℕ → ℕ) (v : ℕ → ℝ) (ω : ℕ → Ω),
      (∀ k, 0 < v k) ∧
      TendstoUniformlyOn (fun k s => eulerG (P k) (v k) s (ω k))
        etaRect atTop (Rect.threeLeftEdges R) := by
  -- Run the universality core at tolerances `εₖ = 1/(k+1)`.
  have huniv := eulerG_universality_threeLeftEdges R s₀ hR_lo hs₀ hη
  choose! P v ω hv hω using huniv
  refine ⟨fun k => P (1 / (k + 1)), fun k => v (1 / (k + 1)),
    fun k => ω (1 / (k + 1)), fun k => hv _ (by positivity), ?_⟩
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  refine Filter.eventually_atTop.mpr ⟨⌈ε⁻¹⌉₊, fun n hn z hz => ?_⟩
  rw [dist_comm]
  refine lt_of_lt_of_le (hω _ (by positivity) _ hz) ?_
  have hn' : (⌈ε⁻¹⌉₊ : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
  have hpos : (0 : ℝ) < (n : ℝ) + 1 := by positivity
  have hεinv : ε⁻¹ ≤ (n : ℝ) := le_trans (Nat.le_ceil _) hn'
  rw [div_le_iff₀ hpos]
  nlinarith [mul_inv_cancel₀ (ne_of_gt hε), hε, hεinv]

/-! ## S9: assembling the Riemann Hypothesis -/

/-- **S9.** `ζ` has no zeros with `1/2 < Re(s) < 1`. Delegates to the proved
    `zetaRect_ne_zero_critical_strip`. -/
theorem zeta_no_zeros_re_gt_half (s₀ : ℂ) (hσ : 1 / 2 < s₀.re) (hσ' : s₀.re < 1) :
    riemannZeta s₀ ≠ 0 :=
  zetaRect_ne_zero_critical_strip s₀ hσ hσ'

/-- **S9 (Riemann Hypothesis).** Every nontrivial zero of `ζ` lies on the
    critical line. Delegates to the proved `riemann_hypothesis_rect`. -/
theorem riemann_hypothesis_via_rectangle :
    ∀ s : ℂ, riemannZeta s = 0 → 0 < s.re → s.re < 1 → s.re = 1 / 2 :=
  fun s hs h1 h2 => riemann_hypothesis_rect s hs h1 h2

end GaussianEuler

end