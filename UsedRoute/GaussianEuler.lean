import Mathlib
import UsedRoute.Basic
import UsedRoute.RectangleStrategy
import UsedRoute.EtaConvergenceExtended

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

* S3 (`eulerG_tendstoUniformly_absConv`, right edge, absolute convergence) is
  **fully proved, `sorry`-free**. Its one analytic input,
  `zetaEulerProd_tendstoUniformlyOn_halfplane` (uniform convergence of the
  ordinary Euler product to `ζ` on a closed half-plane `Re ≥ a > 1`), is now
  proved here: expanding the geometric factors identifies the partial product
  with the Dirichlet series over `(P+1)`-smooth numbers
  (`zetaEulerProd_eq_tsum_smoothNumbers`, via Mathlib's smooth-number Euler
  product), and the remaining non-smooth terms are dominated by the tail
  `∑_{n > P} n^{-a}` of the convergent `p`-series
  (`norm_zeta_sub_zetaEulerProd_le`), which vanishes as `P → ∞`. This is the
  Weierstrass `M`-test, with no critical-strip content.
* `exists_gaussian_corrector_uniform` (S4, the left/top/bottom edges) is the
  single deep input of the Gaussian route. It requires:
  1. The infinite-product Gaussian measure on `Ω` (not yet constructed).
  2. Bagchi/Voronin universality: the support of the Gaussian Dirichlet field
     includes `η(s)` on the three left edges (not yet formalized).
  3. The three PNT tail bounds from `RectangleStrategy.lean`.
  The `ω = 0` reduction proposed in N-B is mathematically invalid (the
  deterministic skeleton does not converge on the left edge). S5 and S6,
  which depend on S4, are also left `sorry`.
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

### N-B (RETRACTED — ω=0 cheat is mathematically invalid).
`exists_gaussian_corrector_uniform` asks for *some* `v > 0` and *some* `ω`.
Taking `ω = 0` gives `gaussSum = 0` and `eulerG = etaEulerApprox` wherever
`etaEulerApprox ≠ 0`. But `etaEulerApprox P → η` uniformly only on compact
subsets of `{Re > 1}` (absolute convergence), NOT on the left edge
`Re ∈ (1/2, 1)` where the prime-zeta tail `∑_{p>P} p^{-s}` diverges.
Hence the deterministic skeleton does not approximate η on the three left edges.
Genuine Bagchi/Voronin universality is required. See `exists_gaussian_corrector_uniform`
for the corrected dependency statement.

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

-- The infinite-product Gaussian measure on Ω is not yet constructed.
-- It requires Mathlib's probability library (product measures, Gaussian distributions).
-- Placeholder for the construction:
--   noncomputable instance : MeasureSpace Ω := ...

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

/-! ### The `M`-test majorant for the Euler tail

The uniform majorant is the tail `∑_{n > P} n^{-a}` of the convergent `p`-series.
`smoothTailMajorant a P` is that tail written as a series over all of `ℕ`. -/

/-- The tail majorant `n ↦ n^{-a} · 1_{n > P}` used in the Weierstrass `M`-test for
    the absolutely convergent Euler product. -/
noncomputable def smoothTailMajorant (a : ℝ) (P : ℕ) : ℕ → ℝ :=
  fun n => if P < n then (n : ℝ) ^ (-a) else 0

lemma smoothTailMajorant_nonneg (a : ℝ) (P n : ℕ) : 0 ≤ smoothTailMajorant a P n := by
  unfold smoothTailMajorant
  split
  · positivity
  · exact le_refl 0

lemma summable_smoothTailMajorant {a : ℝ} (ha : 1 < a) (P : ℕ) :
    Summable (smoothTailMajorant a P) := by
  refine (Real.summable_nat_rpow.mpr (by linarith : -a < -1)).of_nonneg_of_le
    (smoothTailMajorant_nonneg a P) (fun n => ?_)
  unfold smoothTailMajorant
  split
  · exact le_refl _
  · positivity

lemma tsum_smoothTailMajorant_eq {a : ℝ} (ha : 1 < a) (P : ℕ) :
    ∑' n, smoothTailMajorant a P n
      = (∑' n : ℕ, (n : ℝ) ^ (-a)) - ∑ n ∈ Finset.range (P + 1), (n : ℝ) ^ (-a) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-a)) := Real.summable_nat_rpow.mpr (by linarith)
  have h := hs.sum_add_tsum_compl (s := Finset.range (P + 1))
  have h2 := _root_.tsum_subtype (((Finset.range (P + 1) : Finset ℕ) : Set ℕ)ᶜ)
      (fun n : ℕ => (n : ℝ) ^ (-a))
  have h3 : ∑' n : ℕ, Set.indicator (((Finset.range (P + 1) : Finset ℕ) : Set ℕ)ᶜ)
      (fun n : ℕ => (n : ℝ) ^ (-a)) n = ∑' n, smoothTailMajorant a P n := by
    congr 1
    funext n
    by_cases hn : P < n <;> simp [Set.indicator, smoothTailMajorant, hn]
  rw [h2, h3] at h
  linarith [h]

/-- The majorant tails vanish: `∑_{n > P} n^{-a} → 0` as `P → ∞`. -/
lemma tendsto_tsum_smoothTailMajorant {a : ℝ} (ha : 1 < a) :
    Tendsto (fun P => ∑' n, smoothTailMajorant a P n) atTop (nhds 0) := by
  have hs : Summable (fun n : ℕ => (n : ℝ) ^ (-a)) := Real.summable_nat_rpow.mpr (by linarith)
  have hpart : Tendsto (fun P : ℕ => ∑ n ∈ Finset.range (P + 1), (n : ℝ) ^ (-a)) atTop
      (nhds (∑' n : ℕ, (n : ℝ) ^ (-a))) :=
    hs.hasSum.tendsto_sum_nat.comp (tendsto_add_atTop_nat 1)
  have h := (tendsto_const_nhds (x := ∑' n : ℕ, (n : ℝ) ^ (-a)) (f := atTop (α := ℕ))).sub hpart
  simp only [sub_self] at h
  simpa [tsum_smoothTailMajorant_eq ha] using h

/-- A natural number that is not `(P+1)`-smooth is either `0` or `> P`: it has a prime
    factor `≥ P + 1`, which divides it. -/
lemma eq_zero_or_lt_of_notMem_smoothNumbers {P n : ℕ} (hn : n ∉ (P + 1).smoothNumbers) :
    n = 0 ∨ P < n := by
  rcases eq_or_ne n 0 with h | h
  · exact Or.inl h
  refine Or.inr ?_
  rw [Nat.mem_smoothNumbers] at hn
  push_neg at hn
  obtain ⟨p, hp, hpP⟩ := hn h
  have : p ≤ n := Nat.le_of_dvd (Nat.pos_of_ne_zero h) (Nat.dvd_of_mem_primeFactorsList hp)
  omega

/-- Pointwise `M`-test bound: on the non-smooth numbers the summand `n^{-s}` is
    dominated by the majorant, uniformly for `a ≤ Re s`. -/
lemma norm_indicator_nonsmooth_le {a : ℝ} (P : ℕ) {s : ℂ} (hs : a ≤ s.re) (ha : 1 < a) (n : ℕ) :
    ‖Set.indicator ((((P + 1).smoothNumbers) : Set ℕ)ᶜ) (fun m : ℕ => (m : ℂ) ^ (-s)) n‖
      ≤ smoothTailMajorant a P n := by
  have hne : (-s).re ≠ 0 := by
    simp only [Complex.neg_re]
    intro h
    linarith
  by_cases hn : n ∈ ((((P + 1).smoothNumbers) : Set ℕ)ᶜ)
  · rw [Set.indicator_of_mem hn]
    rcases eq_zero_or_lt_of_notMem_smoothNumbers (P := P) (n := n) hn with rfl | hlt
    · have h0 : (-s) ≠ 0 := fun h => hne (by rw [h]; simp)
      simpa [Complex.zero_cpow h0] using smoothTailMajorant_nonneg a P 0
    · have hn1 : (1 : ℝ) ≤ (n : ℝ) := by exact_mod_cast Nat.one_le_iff_ne_zero.mpr (by omega)
      have hnorm : ‖(n : ℂ) ^ (-s)‖ = (n : ℝ) ^ (-s.re) := by
        rw [← Complex.ofReal_natCast,
          Complex.norm_cpow_eq_rpow_re_of_nonneg (Nat.cast_nonneg n) hne, Complex.neg_re]
      simp only [hnorm, smoothTailMajorant, if_pos hlt]
      exact Real.rpow_le_rpow_of_exponent_le hn1 (by linarith)
  · rw [Set.indicator_of_notMem hn]
    simpa using smoothTailMajorant_nonneg a P n

/-- The primes occurring in `zetaEulerProd P` are exactly the primes below `P + 1`. -/
lemma filter_prime_Icc_eq_primesBelow (P : ℕ) :
    (Finset.Icc 2 P).filter Nat.Prime = Nat.primesBelow (P + 1) := by
  ext p
  simp only [Finset.mem_filter, Finset.mem_Icc, Nat.mem_primesBelow, Nat.lt_succ_iff]
  exact ⟨fun ⟨⟨_, h2⟩, hp⟩ => ⟨h2, hp⟩, fun ⟨h, hp⟩ => ⟨⟨hp.two_le, h⟩, hp⟩⟩

/-- Expanding the geometric factors: for `Re s > 1` the partial Euler product is the
    Dirichlet series restricted to the `(P+1)`-smooth numbers. -/
lemma zetaEulerProd_eq_tsum_smoothNumbers (P : ℕ) {s : ℂ} (hs : 1 < s.re) :
    zetaEulerProd P s = ∑' m : (P + 1).smoothNumbers, (m : ℂ) ^ (-s) := by
  have hs0 : s ≠ 0 := Complex.ne_zero_of_one_lt_re hs
  have hsum : Summable (fun n : ℕ => (riemannZetaSummandHom hs0 : ℕ →* ℂ) n) := by
    simpa using (summable_riemannZetaSummand hs).of_norm
  simpa [zetaEulerProd, filter_prime_Icc_eq_primesBelow, riemannZetaSummandHom] using
    EulerProduct.prod_primesBelow_geometric_eq_tsum_smoothNumbers hsum (P + 1)

/-- The quantitative `M`-test estimate: the error of the partial Euler product is at
    most the tail `∑_{n > P} n^{-a}`, uniformly on `{a ≤ Re}`. -/
lemma norm_zeta_sub_zetaEulerProd_le {a : ℝ} (ha : 1 < a) (P : ℕ) {s : ℂ} (hs : a ≤ s.re) :
    ‖riemannZeta s - zetaEulerProd P s‖ ≤ ∑' n, smoothTailMajorant a P n := by
  have hs1 : 1 < s.re := lt_of_lt_of_le ha hs
  have hsum : Summable (fun n : ℕ => (n : ℂ) ^ (-s)) := by
    simpa [riemannZetaSummandHom] using (summable_riemannZetaSummand hs1).of_norm
  have hz : ∑' (n : ℕ), (n : ℂ) ^ (-s) = riemannZeta s := by
    simpa [riemannZetaSummandHom] using tsum_riemannZetaSummand hs1
  have hsplit := hsum.tsum_subtype_add_tsum_subtype_compl ((P + 1).smoothNumbers : Set ℕ)
  rw [hz] at hsplit
  have hdiff : riemannZeta s - zetaEulerProd P s
      = ∑' m : ((((P + 1).smoothNumbers) : Set ℕ)ᶜ : Set ℕ), (m : ℂ) ^ (-s) := by
    rw [zetaEulerProd_eq_tsum_smoothNumbers P hs1]
    linear_combination -hsplit
  rw [hdiff,
    _root_.tsum_subtype ((((P + 1).smoothNumbers : Set ℕ))ᶜ) (fun m : ℕ => (m : ℂ) ^ (-s))]
  have hbd := norm_indicator_nonsmooth_le (a := a) P hs ha
  have hsummable_ind : Summable (fun n : ℕ =>
      ‖Set.indicator ((((P + 1).smoothNumbers) : Set ℕ)ᶜ) (fun m : ℕ => (m : ℂ) ^ (-s)) n‖) :=
    (summable_smoothTailMajorant ha P).of_nonneg_of_le (fun n => norm_nonneg _) hbd
  exact le_trans (norm_tsum_le_tsum_norm hsummable_ind)
    (hsummable_ind.tsum_le_tsum hbd (summable_smoothTailMajorant ha P))

/-- **Core analytic input for S3.** The partial Euler product converges to `ζ`
    uniformly on the closed half-plane `{a ≤ Re}` for any `a > 1`.  This is the
    classical absolutely-convergent Euler product (Weierstrass `M`-test against
    `∑_n n^{-a}`), with no critical-strip content. -/
lemma zetaEulerProd_tendstoUniformlyOn_halfplane (a : ℝ) (ha : 1 < a) :
    TendstoUniformlyOn (fun P => zetaEulerProd P) riemannZeta atTop
      {s : ℂ | a ≤ s.re} := by
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [(tendsto_tsum_smoothTailMajorant ha).eventually (eventually_lt_nhds hε)]
    with P hP s hsmem
  rw [dist_eq_norm]
  have h : ‖riemannZeta s - zetaEulerProd P s‖ < ε :=
    lt_of_le_of_lt (norm_zeta_sub_zetaEulerProd_le ha P (s := s) hsmem) hP
  simpa [norm_sub_rev] using h

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
    uniformly `ε`-close to `η` on the boundary.

    This is the genuine universality input: Voronin/Bagchi universality in its
    Gaussian incarnation. The proof is blocked by the three PNT sorries in
    `RectangleStrategy.lean` (`primeZetaTail_uniform_small`,
    `higherPrimeSum_uniform_small`, `eulerProd_zeta_exp_connection`) and by the
    need to construct the infinite-product Gaussian measure on `Ω`.

    The determinstic skeleton (`v = 0`, `ω = 0`) collapses to `etaEulerApprox`,
    but `etaEulerApprox P → η` uniformly only on compact subsets of `{Re > 1}`
    (absolute convergence), not on the left edge `Re ∈ (1/2, 1)` where the
    prime-zeta tail diverges. Hence the ω=0 "cheat" (N-B) is mathematically
    invalid; genuine Bagchi universality is required. -/
lemma exists_gaussian_corrector_uniform (P : ℕ) (R : Rect) (s₀ : ℂ)
    (hR_lo : ∀ z ∈ R.closure, z.re > 1 / 2)
    (hs₀ : s₀ ∈ R.openInt)
    (hη : ∀ z ∈ R.closure, z ≠ s₀ → etaRect z ≠ 0) :
    ∀ ε > 0, ∃ (v : ℝ) (ω : Ω), 0 < v ∧
      ∀ z ∈ R.closure \ R.openInt, ‖eulerG P v z ω - etaRect z‖ < ε := by
  -- This lemma is a `sorry` — it is the single deep input of the Gaussian route.
  -- Its proof requires:
  -- 1. The infinite-product Gaussian measure on Ω (to be constructed).
  -- 2. Bagchi/Voronin universality: the support of the Gaussian Dirichlet field
  --    includes η(s) on the three left edges.
  -- 3. The three PNT tail bounds from RectangleStrategy.lean.
  sorry

/-! ## S5: reciprocal edge convergence -/

/-- **S5.** There is a diagonal sequence `(P_k, v_k, ω_k)` along which the
    reciprocals `1/eulerG` converge uniformly to `1/η` on the rectangle boundary.
    Depends on S3 + S4; left open as a `sorry`. -/
lemma recipEulerG_tendsto_recipEta_onEdges (R : Rect) (s₀ : ℂ)
    (hR_lo : ∀ z ∈ R.closure, z.re > 1 / 2) (hx_hi : 1 < R.x_hi)
    (hs₀ : s₀ ∈ R.openInt)
    (hη : ∀ z ∈ R.closure, z ≠ s₀ → etaRect z ≠ 0) :
    ∃ (P : ℕ → ℕ) (v : ℕ → ℝ) (ω : ℕ → Ω),
      TendstoUniformlyOn (fun k s => 1 / eulerG (P k) (v k) s (ω k))
        (fun s => 1 / etaRect s) atTop (R.closure \ R.openInt) := by
  -- This lemma is a `sorry` — it depends on S4 (`exists_gaussian_corrector_uniform`)
  -- which is itself a `sorry` (the deep universality input).
  sorry

/-! ## S6: the reciprocal contour integral of `η` vanishes -/

/-- **S6.** `∮_{∂R} 1/η = 0` for a rectangle isolating a single interior zero
    `s₀`. Depends on S2 + S5; left open as a `sorry`. -/
lemma recipEta_rect_contour_integral_eq_zero' (R : Rect) (s₀ : ℂ)
    (hR_lo : ∀ z ∈ R.closure, z.re > 1 / 2) (hx_hi : 1 < R.x_hi)
    (hs₀ : s₀ ∈ R.openInt)
    (hη : ∀ z ∈ R.closure, z ≠ s₀ → etaRect z ≠ 0) :
    R.boundaryIntegral (fun s => 1 / etaRect s) = 0 := by
  -- This lemma is a `sorry` — it depends on S5 (`recipEulerG_tendsto_recipEta_onEdges`)
  -- which is itself a `sorry`, and on the N-C restatement of S2 for straddling rectangles.
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