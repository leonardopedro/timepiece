# Implementation Plan: Discharging the 7 Remaining Sorries

**Audience**: a Lean 4 formalization agent. Each section below gives the exact
current Lean statement, a verdict on provability, and a complete English proof
written at the level of detail needed to formalize directly. Mathlib lemma
names cited here have been **verified to exist in this project's Mathlib
snapshot** unless marked "(search)".

**Status**: 37 lemmas proved, 7 sorries remaining. Completed work:
`../IMPLEMENTED.md`. Strategy exposition: `zetanew.tex`.

| # | File | Lemma | Verdict |
|---|------|-------|---------|
| S1 | `ZeroLocation.lean` | `zero_location_contradiction` | **PROVABLE** (short, via H6) |
| S2 | `ConjugateReflection.lean` | `conjReflLimit_zero_order` | **PROVABLE** (direct, via H4/H5) |
| S3 | `ZeroLocation.lean` | `fourFoldApprox_tendstoUniformlyOn_boundary` | **PROVABLE after adding one hypothesis** (`Re < 1` on closure) |
| S4 | `MultiplicityOne.lean` | `even_multiplicity_contradiction` | **RESTATE in normalized coordinates** (current `h_order` is inconsistent → only vacuously provable; the corrected, normalized statement is the genuine core — see N1–N4 and S4) |
| S5 | `MultiplicityOne.lean` | `nonreal_edges_sum_zero` | **NOT PROVABLE AS STATED** — restatement + full proof of replacement given |
| S6 | `ConjugateReflection.lean` | `exists_isolating_rect` | **NOT PROVABLE AS STATED** — partial discharge + restatement given |
| S7 | `MultiplicityOne.lean` | `etaShifted_zeros_simple` | **FALSE AS STATED** — restatement (provable weaker form) given; the intended content is the open core |

Work in the order S1 → S2 → S3 → S4, then handle S5–S7 per their sections
(they require statement changes, which is safe: their only consumers are
themselves sorry'd or trivially adjusted).

---

## Part 0: Definitions and verified API

### Project definitions (exact)

```lean
-- EtaStrategy.lean
def dirichletEta (s : ℂ) : ℂ := (1 - (2:ℂ) ^ (1 - s)) * riemannZeta s
def etaFactor    (s : ℂ) : ℂ := 1 - (2:ℂ) ^ (1 - s)

-- RectangleStrategy.lean  (definitionally equal to dirichletEta!)
def etaRect (s : ℂ) : ℂ := (1 - (2:ℂ) ^ (1 - s)) * riemannZeta s

-- ShiftedEta.lean
def etaShifted (s : ℂ) : ℂ := dirichletEta (2 * s - 1)
def etaPartialShifted (n : ℕ) (s : ℂ) : ℂ :=
  ∑ k ∈ Finset.range n, (-1:ℂ)^k / ((k:ℂ)+1) ^ (2*s-1)
def targetH (s : ℂ) : ℂ := s - (3/4 : ℂ) - I
def hApprox (n : ℕ) (s : ℂ) : ℂ := targetH s + (1 / ((n:ℂ)+1))
def fApprox (n : ℕ) (s : ℂ) : ℂ := hApprox n s * etaPartialShifted n s

-- ConjugateReflection.lean
def conjReflApprox (n : ℕ) (s : ℂ) : ℂ :=
  starRingEnd ℂ (fApprox n (starRingEnd ℂ s)) * fApprox n s
def conjReflLimit (s : ℂ) : ℂ :=
  starRingEnd ℂ (targetH (starRingEnd ℂ s) * etaShifted (starRingEnd ℂ s)) *
    (targetH s * etaShifted s)

-- RectangleStrategy.lean
structure Rect where x_lo x_hi y_lo y_hi : ℝ; hx : x_lo < x_hi; hy : y_lo < y_hi
def Rect.closure (R) : Set ℂ := {z | x_lo ≤ re ∧ re ≤ x_hi ∧ y_lo ≤ im ∧ im ≤ y_hi}
def Rect.openInt (R) : Set ℂ := {z | strict versions}
def Rect.boundaryIntegral (R) (f) : ℂ :=
  ((∫ x in x_lo..x_hi, f (x + y_lo*I)) - (∫ x in x_lo..x_hi, f (x + y_hi*I)))
  + I • (∫ y in y_lo..y_hi, f (x_hi + y*I)) - I • (∫ y in y_lo..y_hi, f (x_lo + y*I))
```

### Proved project lemmas you will use

| Lemma | File | Statement |
|-------|------|-----------|
| `rect_cauchy` | RectangleStrategy:204 | `DifferentiableOn ℂ f R.closure → R.boundaryIntegral f = 0` |
| `etaRect_ne_zero_critical_strip` | RectangleStrategy:1320 | `1/2 < re s < 1 → etaRect s ≠ 0` ⚠ downstream of legacy sorries (see Part 3) |
| `zeta_symm` | Basic:15 | `0 < re < 1 → ζ s = 0 → ζ (1-s) = 0` |
| `etaFactor_ne_zero_re_lt_one` | EtaStrategy:87 | `re s < 1 → etaFactor s ≠ 0` |
| `dirichletEta_ne_zero_at_two` | EtaStrategy:482 | `dirichletEta 2 ≠ 0` |
| `etaShifted_functional_eq_zero` | ZeroLocation:53 | strip zero at s₀ → zero at 3/2−s₀ |
| `fApprox_tendstoUniformlyOn` | ShiftedEta:249 | `f_n → targetH·etaShifted` unif. on compact `K ⊂ {1/2<re<1}` |
| `tendstoUniformlyOn_conj_comp` | MultiplicityOne:25 | conv. on `conj '' K` → conj-composite conv. on `K` |
| `tendstoUniformlyOn_mul` | MultiplicityOne:35 | product of unif.-conv. **bounded** sequences |
| `conjReflApprox_tendstoUniformlyOn` | MultiplicityOne:64 | (its proof is the **template** for S3's boundedness blocks) |
| `targetH_differentiable`, `targetH_ne_zero` | ShiftedEta | — |
| `etaPartialShifted_differentiable` | ShiftedEta:110 | — |
| `isPreconnected_halfplane_minus_one` | EtaConvergence:260 | `{re > 1/2} \ {1}` preconnected |

### Verified Mathlib API (this snapshot)

| Name | Location | Signature (informal) |
|------|----------|----------------------|
| `riemannZeta_residue_one` | NumberTheory/LSeries/RiemannZeta.lean:217 | `Tendsto (fun s => (s-1) * ζ s) (𝓝[≠] 1) (𝓝 1)` |
| `conj_cpow` | Analysis/SpecialFunctions/Pow/Complex.lean:231 | `x.arg ≠ π → conj x ^ n = conj (x ^ conj n)` |
| `cpow_conj` | ibid:234 | `x.arg ≠ π → x ^ conj n = conj (conj x ^ n)` |
| `HasDerivAt.conj_conj` | Analysis/Calculus/Deriv/Star.lean:84 | `HasDerivAt f f' x → HasDerivAt (conj ∘ f ∘ conj) (conj f') (conj x)` |
| `DifferentiableAt.conj_conj` | ibid:89 | `DifferentiableAt ℂ f x → DifferentiableAt ℂ (conj ∘ f ∘ conj) (conj x)` |
| `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero` | Analysis/Analytic/IsolatedZeros.lean:130 | isolated zeros dichotomy |
| `analyticOrderAt`, `analyticOrderAt_eq_top` | Analysis/Analytic/Order.lean:48,76 | order of vanishing; `= ⊤ ↔ ∀ᶠ z in 𝓝 z₀, f z = 0` |
| `AnalyticAt.analyticOrderAt_eq_natCast` | Analysis/Analytic/Order.lean (≈45) | `order = n ↔ ∃ g, AnalyticAt ∧ g z₀ ≠ 0 ∧ ∀ᶠ z, f z = (z-z₀)^n • g z` |
| `isConnected_compl_singleton_of_one_lt_rank` | Analysis/Normed/Module/Connected.lean:125 | `1 < rank ℝ E → IsConnected {x}ᶜ` (use `rank_real_complex`: rank ℝ ℂ = 2) |
| `TendstoUniformlyOn.comp` | Topology/UniformSpace/UniformConvergence.lean:230 | `TendstoUniformlyOn F f p s → ∀ g, TendstoUniformlyOn (F · ∘ g) (f ∘ g) p (g ⁻¹' s)` |
| `differentiableAt_riemannZeta` | Mathlib | `s ≠ 1 → DifferentiableAt ℂ riemannZeta s` |
| `hasDerivAt_iff_tendsto_slope` | Mathlib | derivative as limit of difference quotients |
| `intervalIntegral.integral_nonneg`, `Complex.mul_conj`, `Complex.normSq_nonneg` | Mathlib | — |

**NOT available in this Mathlib snapshot**: `riemannZeta_conj` (Schwarz
reflection for ζ). It must be proved as helper H3 below.

---

## Part 1: Helper lemmas (prove these first — they unlock S1–S5)

Place H1–H5 at the top of `ConjugateReflection.lean` (all their dependencies
are already imported there), or in a new file imported by it. H6 can go in the
same place (its ingredients `etaRect_ne_zero_critical_strip`, `zeta_symm`,
`etaFactor_ne_zero_re_lt_one` are all transitively imported).

### H1. The junk value at 1 — `dirichletEta_one`

```lean
lemma dirichletEta_one : dirichletEta 1 = 0
```
**Proof.** Unfold: `(1 - 2^(1-1)) * ζ 1 = (1 - 2^(0:ℂ)) * ζ 1 = (1-1) * ζ 1 = 0`.
Use `Complex.cpow_zero`, then `sub_self`, `zero_mul`. One line:
`simp [dirichletEta, Complex.cpow_zero]`. ∎

Also record `etaShifted_one : etaShifted 1 = 0` (since `2*1-1 = 1`; `norm_num`
inside `etaShifted` then `dirichletEta_one`).

### H2. The true limit at 1 — `dirichletEta_tendsto_log_two`

```lean
lemma dirichletEta_tendsto_log_two :
    Tendsto dirichletEta (𝓝[≠] (1:ℂ)) (𝓝 (Complex.log 2))
```
This formalizes: *Mathlib's `riemannZeta` carries a junk value at 1, so
`dirichletEta` (defined as `etaFactor * ζ`) is **discontinuous** at 1: its
value there is 0 (H1) but its limit is `log 2 ≠ 0`.* This discontinuity is the
engine of S4 and the reason S7 is false as stated.

**Proof.**
1. **Factor through the pole.** For `w ≠ 1`,
   `dirichletEta w = (etaFactor w / (w-1)) * ((w-1) * riemannZeta w)`
   (multiply and divide by `w-1 ≠ 0`; `field_simp`/`ring`-style rewrite under
   the filter `𝓝[≠] 1` via `Filter.Tendsto.congr'` with
   `eventually_mem_nhdsWithin : ∀ᶠ w in 𝓝[≠] 1, w ∈ {1}ᶜ`).
2. **Second factor → 1.** Exactly `riemannZeta_residue_one`.
3. **First factor → log 2.** `etaFactor 1 = 0` (as in H1), so
   `etaFactor w / (w-1)` is the difference quotient (slope) of `etaFactor`
   at 1. Show `HasDerivAt etaFactor (Complex.log 2) 1`:
   - `etaFactor w = 1 - 2^(1-w)`. Since `(2:ℂ) ≠ 0`, rewrite
     `2^(1-w) = Complex.exp ((1-w) * Complex.log 2)` by
     `Complex.cpow_def_of_ne_zero` (mind the argument order of the product in
     that lemma — adjust with `mul_comm` as needed).
   - Chain rule: `u w := (1-w) * Complex.log 2` has `HasDerivAt u (-Complex.log 2) w`
     (`HasDerivAt.const_mul` of `((hasDerivAt_id w).const_sub 1)`, modulo
     argument order). Then `(Complex.hasDerivAt_exp _).comp` gives
     `HasDerivAt (fun w => exp (u w)) (exp (u 1) * (-log 2)) 1`, and
     `exp (u 1) = exp 0 = 1`. Finally
     `HasDerivAt (fun w => 1 - exp (u w)) (log 2) 1` by `HasDerivAt.const_sub`.
   - Convert with `hasDerivAt_iff_tendsto_slope`; `slope etaFactor 1 w`
     is definitionally `(etaFactor w - etaFactor 1) / (w - 1)`
     (`slope_def_field`, and `etaFactor 1 = 0` kills the subtraction —
     note Mathlib's `slope f a b = (f b - f a) / (b - a)`; match directions).
4. Multiply: `Tendsto.mul` of (3) and (2) gives limit `log 2 * 1 = log 2`. ∎

Corollary used later:
```lean
lemma etaShifted_tendsto_log_two :
    Tendsto etaShifted (𝓝[≠] (1:ℂ)) (𝓝 (Complex.log 2))
```
**Proof.** `etaShifted = dirichletEta ∘ (fun s => 2*s-1)`. The affine map
`s ↦ 2s-1` is continuous, sends 1 to 1, and is injective, so it maps
`𝓝[≠] 1 → 𝓝[≠] 1`: continuity gives `Tendsto _ (𝓝 1) (𝓝 1)`; refine to
`nhdsWithin` with `tendsto_nhdsWithin_iff` — the membership condition
`2*s-1 ≠ 1` follows from `s ≠ 1` (`by intro h; apply hs; linarith`-style on
real/imaginary parts, or `sub_ne_zero` + `mul_left_cancel₀`). Compose with H2. ∎

And the non-vanishing of the limit value:
`Complex.log 2 ≠ 0` — its real part is `Real.log 2 > 0`
(`Complex.log_re`-type simp lemmas, or: `Complex.log 2 = ↑(Real.log 2)` for the
positive real 2 via `Complex.ofReal_log` / `Complex.natCast_log` (search the
exact name), then `Real.log_pos one_lt_two`).

### H3. Schwarz reflection for ζ — `riemannZeta_conj'`

```lean
lemma riemannZeta_conj' (s : ℂ) (hs : s ≠ 1) :
    riemannZeta (starRingEnd ℂ s) = starRingEnd ℂ (riemannZeta s)
```
**Proof.** Let `A : ℂ → ℂ := fun z => conj (riemannZeta (conj z))` and
`U : Set ℂ := {z | z ≠ 1}`. We show `A = riemannZeta` on `U` by the identity
theorem; the goal then follows by applying `conj` to `A s = ζ s`
(`conj` is an involution: `Complex.conj_conj` / `RingHom.injective`-free
manipulation: from `conj (ζ (conj s)) = ζ s` conclude
`ζ (conj s) = conj (ζ s)` by applying `starRingEnd ℂ` to both sides and
`conj_conj`). **Careful**: the final goal has `conj s`, but the identity is
proved at the point `s`; both `s ∈ U` and that is all we need.

1. **`A` is analytic on `U`.** `U` is open (`isOpen_compl_singleton`). For
   `z ∈ U`: `conj z ≠ 1` (conj fixes 1; if `conj z = 1` then
   `z = conj (conj z) = conj 1 = 1`). So `differentiableAt_riemannZeta`
   applies at `conj z`, and `DifferentiableAt.conj_conj` (verified, Deriv/Star.lean:89)
   gives `DifferentiableAt ℂ (conj ∘ ζ ∘ conj) (conj (conj z)) = ... z`.
   Note the Mathlib lemma produces differentiability **at `conj x` given
   differentiability at `x`** — instantiate `x := conj z` and rewrite with
   `conj_conj`. Then `DifferentiableOn.analyticOnNhd` (open set).
2. **`riemannZeta` is analytic on `U`.** `differentiableAt_riemannZeta` +
   `DifferentiableOn.analyticOnNhd`.
3. **They agree on `{re > 1}`.** For `re z > 1` use the series
   `zeta_eq_tsum_one_div_nat_add_one_cpow` (or `zeta_eq_tsum_one_div_nat_cpow`;
   both exist for `1 < re`): `ζ z = ∑' n, 1 / (n+1)^z`. Then
   `conj (ζ (conj z)) = ∑' n, conj (1/(n+1)^(conj z))`
   (conjugation commutes with `tsum`: `conj` = `starRingEnd ℂ` is a continuous
   ring isomorphism; use `Complex.conj_tsum`-style: `map_tsum` with
   `Complex.continuous_conj`, or `(Complex.conjCLE : ℂ ≃L[ℝ] ℂ).map_tsum`
   (search: `ContinuousLinearEquiv.map_tsum` / `tsum_star`)). Termwise:
   `conj ((n+1)^(conj z)) = (n+1)^z` from `conj_cpow` with base `x = (n+1 : ℂ)`
   — a positive real, so `x.arg = 0 ≠ π` (`Complex.arg_natCast`-style /
   `Complex.arg_ofReal_of_nonneg`; conclude `≠ π` from `Real.pi_ne_zero`),
   `conj x = x` (`Complex.conj_natCast`), and `conj_conj`. And
   `conj (1/y) = 1/(conj y)` (`map_div₀`, `map_one`).
4. **Identity theorem.** `{re > 1}` is open and nonempty (contains 2), and
   `2 ∈ U`. Agreement on an open neighborhood of 2 gives
   `A =ᶠ[𝓝 2] riemannZeta`. `U` is preconnected:
   `(isConnected_compl_singleton_of_one_lt_rank (by rw [rank_real_complex]; norm_num) 1).isPreconnected`
   (verified name; `U = {1}ᶜ` after `Set.ext`). Apply
   `AnalyticOnNhd.eqOn_of_preconnected_of_eventuallyEq` (this exact pattern,
   with `frequently` variant, is already used in EtaConvergence.lean:304 —
   copy it). Conclude `A s = ζ s`. ∎

### H4. Schwarz reflection for the shifted eta — `etaShifted_conj`

```lean
lemma etaShifted_conj (s : ℂ) :
    etaShifted (starRingEnd ℂ s) = starRingEnd ℂ (etaShifted s)
```
**Proof.** Case `s = 1`: both sides are `0` by H1's corollary
(`conj 1 = 1`, `etaShifted 1 = 0`, `conj 0 = 0`). Case `s ≠ 1`: unfold
`etaShifted` and `dirichletEta`. Since `2 * conj s - 1 = conj (2*s - 1)`
(`map_mul`, `map_sub`, `Complex.conj_ofNat`/`map_one`), it suffices to show
`dirichletEta (conj w) = conj (dirichletEta w)` for `w := 2*s-1 ≠ 1`
(`w = 1 ↔ s = 1` by linear algebra on the equation). Two factors:
- `1 - 2^(1 - conj w) = conj (1 - 2^(1-w))`: `1 - conj w = conj (1 - w)`, then
  `conj (2^(1-w)) = 2^(conj (1-w))` from `conj_cpow 2 _ (arg 2 ≠ π)` — for the
  base: `(2:ℂ).arg = 0` since 2 is a positive real
  (`Complex.arg_ofNat`/`Complex.arg_two` (search); or rewrite `(2:ℂ) = ((2:ℝ):ℂ)`
  and use `Complex.arg_ofReal_of_nonneg`), and `0 ≠ π` by `Real.pi_ne_zero.symm`;
  also `conj (2:ℂ) = 2`.
- `ζ (conj w) = conj (ζ w)`: H3 with `w ≠ 1`.
Multiply with `map_mul`. ∎

### H5. Closed form of the conjugate-reflection limit — `conjReflLimit_eq`

```lean
lemma conjReflLimit_eq (s : ℂ) :
    conjReflLimit s = (s - 3/4 + I) * targetH s * (etaShifted s)^2
```
**Proof.** Unfold `conjReflLimit` and push `starRingEnd` through the product
(`map_mul`):
`conjReflLimit s = conj (targetH (conj s)) * conj (etaShifted (conj s)) * (targetH s * etaShifted s)`.
- `conj (targetH (conj s)) = conj (conj s - 3/4 - I) = s - 3/4 + I`
  (`map_sub`, `conj_conj`, `Complex.conj_I`, and `conj (3/4 : ℂ) = 3/4` via
  `map_div₀`/`map_ofNat` — the same simp set as in `fourFoldApprox_symm`
  (ZeroLocation:115) works).
- `conj (etaShifted (conj s)) = etaShifted s`: apply `conj` to H4 and use
  `conj_conj`.
Then `ring` (with `sq`/`pow_two`). ∎

**Consequence (record it):** `conjReflLimit` is ℂ-differentiable away from 1:
```lean
lemma etaShifted_differentiableAt {s : ℂ} (hs : s ≠ 1) :
    DifferentiableAt ℂ etaShifted s
```
(`etaFactor` part: `DifferentiableAt.const_cpow` with `Or.inl two_ne_zero`,
composed with the affine map; ζ part: `differentiableAt_riemannZeta` at
`2*s-1 ≠ 1`, composed with the affine map; product/composition rules.)
```lean
lemma conjReflLimit_differentiableOn :
    DifferentiableOn ℂ conjReflLimit {s | s ≠ 1}
```
(rewrite by H5 `funext`-style or via `DifferentiableOn.congr`; polynomial
factors are entire; `(etaShifted ·)^2` differentiable at `s ≠ 1`.)

### H6. All strip zeros lie on Re = 3/4 — `etaShifted_zero_re_eq`

```lean
lemma etaShifted_zero_re_eq (s₀ : ℂ) (hσ₁ : s₀.re > 1/2) (hσ₂ : s₀.re < 1)
    (h_zero : etaShifted s₀ = 0) : s₀.re = 3/4
```
⚠ **Dependency note**: this uses `etaRect_ne_zero_critical_strip`
(RectangleStrategy:1320), which is proved *in that file* but sits downstream
of RectangleStrategy's own sorries (see Part 3). The project already accepts
this kind of dependency: the **proved** lemma `fApprox_not_identically_zero`
(MultiplicityOne:381) already uses `riemann_hypothesis_rect` from the same
chain.

**Proof.** `etaShifted s₀ = dirichletEta (2s₀-1)` and `dirichletEta = etaRect`
**definitionally** (both unfold to `(1 - 2^(1-w)) * ζ w`; `rfl` after
unfolding, or `show etaRect (2*s₀-1) = 0 at h_zero`). Let `w := 2*s₀-1`; note
`w.re = 2*s₀.re - 1 ∈ (0, 1)` (`Complex.sub_re`, `Complex.mul_re`,
`Complex.ofNat_re` simp; then `linarith`). Trichotomy on `s₀.re` vs `3/4`:
- **`s₀.re > 3/4`**: then `w.re ∈ (1/2, 1)`, contradicting
  `etaRect_ne_zero_critical_strip w`.
- **`s₀.re = 3/4`**: done.
- **`s₀.re < 3/4`**: by `etaShifted_functional_eq_zero` — **but** that lemma
  lives in ZeroLocation.lean; to avoid an import cycle when H6 is placed in
  ConjugateReflection.lean, inline its 10-line proof (it only uses
  `etaFactor_ne_zero_re_lt_one` and `zeta_symm`, both available):
  from `etaRect w = 0` and `etaFactor w ≠ 0` (since `w.re < 1`) get
  `ζ w = 0`; `zeta_symm w` (with `0 < w.re < 1`) gives `ζ (1-w) = 0`; and
  `1 - w = 2*(3/2 - s₀) - 1`, with `(3/2-s₀).re = 3/2 - s₀.re ∈ (3/4, 1)`,
  so `(1-w).re = 2*(3/2-s₀).re - 1 ∈ (1/2, 1)`. Then
  `etaRect (1-w) = etaFactor (1-w) * ζ (1-w) = 0`, contradicting
  `etaRect_ne_zero_critical_strip (1-w)`. ∎

*(If H6 is only needed inside ZeroLocation.lean, the case `s₀.re < 3/4` can
simply call `etaShifted_functional_eq_zero` and then the first case at
`3/2 - s₀`.)*

### N. The normalization layer (required to repair S2's hypothesis and S4)

The contour argument was always intended to run in **normalized coordinates**:
the hypothetical zero `s₀ = σ₀ + i·t₀` is moved to the reference point
`3/4 + I` (height 1), which is where `targetH` plants its zero and where the
fixed half-rectangle geometry lives. The current Lean statements omit this
layer, which is exactly why `h_order`/`h_eta_order` came out inconsistent
(they force a factorization through the junk point `s = 1`; see S4). The
normalization treats x and y differently — **x is shifted and scaled, y is
only scaled** — but it must be implemented as a single *complex-affine
(conformal) map with real coefficients*; a coordinate map with two distinct
dilation factors for x and y is not holomorphic and would destroy Cauchy's
theorem.

**Definitions** (place next to H1–H6; parameters `σ₀ t₀ : ℝ` with `0 < t₀`):
```lean
/-- Affine normalization: sends the normalized plane to the original one.
    Coordinates: x ↦ t₀·x + (σ₀ - (3/4)·t₀),  y ↦ t₀·y.
    Sends the reference point 3/4 + I to s₀ = σ₀ + i·t₀. -/
def normMap (σ₀ t₀ : ℝ) (z : ℂ) : ℂ :=
  (t₀ : ℂ) * z + ((σ₀ : ℂ) - (3/4) * (t₀ : ℂ))

/-- The shifted eta function in normalized coordinates. -/
def etaShiftedNorm (σ₀ t₀ : ℝ) (z : ℂ) : ℂ := etaShifted (normMap σ₀ t₀ z)

/-- The pulled-back singular point: normMap σ₀ t₀ z₁ = 1.  NOTE: it is REAL. -/
def normBadPoint (σ₀ t₀ : ℝ) : ℂ := (3/4 : ℂ) + ((1 - σ₀) / t₀ : ℂ)
```

**N1. Basic properties** (each a few lines):
- `normMap_ref : normMap σ₀ t₀ (3/4 + I) = σ₀ + t₀*I` — `push_cast; ring`.
- `normMap_conj : normMap σ₀ t₀ (conj z) = conj (normMap σ₀ t₀ z)` — the
  coefficients are real (`Complex.conj_ofReal`, `map_mul`, `map_add`); this is
  what keeps the real axis and the Schwarz reflection intact.
- `normMap_real : (normMap σ₀ t₀ x).im = 0` for real `x` — immediate from the
  coordinate form (`Complex.add_im`, `Complex.mul_im`, `Complex.ofReal_im`).
- `normMap` is entire and injective for `t₀ ≠ 0` (affine with nonzero slope);
  differentiability: `(differentiable_const _).mul differentiable_id |>.add_const _`-style.
- `normMap_bad : normMap σ₀ t₀ (normBadPoint σ₀ t₀) = 1` — `field_simp; ring`
  (uses `t₀ ≠ 0`).
- WLOG `t₀ > 0`: zeros come in conjugate pairs — from H4,
  `etaShifted s₀ = 0 → etaShifted (conj s₀) = 0` (apply H4 at `s₀` and
  `map_eq_zero`); so a zero with `t₀ < 0` can be replaced by its reflection.
  Zeros with `t₀ = 0` (real zeros) are a separate elementary exclusion:
  on the real segment `(1/2, 1)` the value `dirichletEta (2σ-1)` is a
  *positive* real — provable from the paired-series representation
  `paired_tsum_eq_dirichletEta` (EtaConvergence.lean, proved): each paired
  term `1/(2j+1)^x - 1/(2j+2)^x` is positive for real `x ∈ (0,1)`, the sum of
  a summable sequence of positive terms is positive (`tsum_pos`). Record as
  `etaShifted_pos_of_real : ∀ σ ∈ Ioo (1/2) 1, 0 < (etaShifted σ).re`-style,
  or just `≠ 0`.

**N2. Reflection and zero transport**:
- `etaShiftedNorm_conj : etaShiftedNorm σ₀ t₀ (conj z) = conj (etaShiftedNorm σ₀ t₀ z)`
  — chain `normMap_conj` and H4.
- `etaShiftedNorm (3/4 + I) = etaShifted s₀` (by `normMap_ref`); in particular
  the normalized function vanishes at `3/4 + I` iff `etaShifted` vanishes at
  `s₀`, **and any local factorization of order m transports across the affine
  map** with `φ` rescaled by `t₀^m`:
  `etaShifted s = (s - s₀)^m · φ s  ↔  etaShiftedNorm z = (z - (3/4+I))^m · (t₀^m · φ (normMap z))`
  because `normMap z - s₀ = t₀ · (z - (3/4 + I))` (`ring`) and `mul_pow`.
- `etaShiftedNorm` is differentiable away from `normBadPoint σ₀ t₀`
  (composition: `etaShifted_differentiableAt` away from 1, `normMap` affine,
  `normMap z = 1 ↔ z = normBadPoint` by injectivity).

**N3. Geometry — the normalized rectangle excludes the bad point.** Use the
*fixed* half-rectangle `R := mkHalfRect (3/4 - δ) (3/4 + δ) T` with any
`T > 1` (e.g. `T = 2`) and any
`δ < min (σ₀ - 1/2) (1 - σ₀) / t₀`.
Then for `z ∈ R.closure`:
`(normMap σ₀ t₀ z).re = t₀ * (z.re - 3/4) + σ₀ ∈ (σ₀ - t₀δ, σ₀ + t₀δ) ⊂ (1/2, 1)`,
so the image of the rectangle stays in the critical strip, and in particular
`normBadPoint = 3/4 + (1-σ₀)/t₀` lies **outside** `R.closure` (its distance
from `3/4` along the real axis is `(1-σ₀)/t₀ > δ`). This is the normalized
analogue of the `hR_re'` hypothesis and removes the junk point from the
contour. Note the reference zero sits at height exactly 1, `s₀ ∈` image of
`R.openInt`, and the bottom edge maps into the real axis (`normMap_real`).

**N3½. Why the y-shift (height 1) is load-bearing — pole simplicity.** The
normalization must place the zero at height `y = 1`, strictly off the real
axis, and this is not cosmetic. In the conjugate-reflection product
`F_n(z) = conj (f_n (conj z)) · f_n z`, each zero `w` of `f_n` contributes a
zero of the *conjugated* factor at the **mirror point** `conj w`. The
`targetH` factor of `f_n` vanishes near `3/4 + I` (height `+1`); its mirror in
the conjugated factor vanishes near `3/4 - I` (height `−1`). Because of the
y-shift these are *distinct* points, two apart in y — so the corresponding
poles of `1/F_n` (and of the reciprocal of the limit) **remain simple**, one
in the upper half-plane and one in the lower. Without the y-shift (target on
the real axis, `targetH s = s - 3/4`) the zero and its mirror would *collide
at the same real point*: the product would acquire a double zero **on the
bottom edge of the contour**, `1/F_n` a double pole there, and both the
positivity argument and the residue accounting would break. The same
separation applies to the zero under study: `s₀` normalizes to `3/4 + I`
while its reflection partner sits at `3/4 - I`, outside the upper
half-rectangle. Any restatement or refactor must preserve this: **the
normalized zero has `im = 1`, never `im = 0`.**

**N4. Normalized approximants.** `fApproxNorm n z := fApprox n (normMap σ₀ t₀ z)`
is entire (composition of entire functions), satisfies the same Schwarz
reflection (`normMap_conj` + the conjugation identity for `fApprox` already
established inside `conjReflApprox_cauchy`, ConjugateReflection:144–149), so:
- the normalized conjugate-reflection product
  `conjReflApproxNorm n z := conj (fApproxNorm n (conj z)) * fApproxNorm n z`
  is entire, its rectangle boundary integral vanishes (same proof as
  `conjReflApprox_cauchy` — or directly: it *equals* `conjReflApprox n ∘ normMap`
  up to the conj-equivariance identities),
- it is `≥ 0` on the real axis (same `Complex.mul_conj` computation as
  `conjReflApprox_eq_normSq`, using `normMap_real`),
- uniform convergence on `R.closure` follows from
  `conjReflApprox_tendstoUniformlyOn` via `TendstoUniformlyOn.comp _ (normMap σ₀ t₀)`
  applied on the compact image `normMap '' R.closure ⊂ {1/2 < re < 1}` (N3),
- the limit has the closed form
  `(z - 3/4 + I) * (z - 3/4 - I) * (etaShiftedNorm z)^2` on `R.closure`
  (H5 composed with `normMap`, valid away from the bad point — excluded by N3).

---

## Part 2: The seven sorries

### S1. `zero_location_contradiction` (ZeroLocation.lean:145) — PROVABLE

```lean
lemma zero_location_contradiction (s₀ : ℂ)
    (hσ₁ : s₀.re > 1/2) (hσ₂ : s₀.re < 1)
    (h_zero : etaShifted s₀ = 0)
    (h_off_line : s₀.re ≠ 3/4) : False
```
**Proof.** `exact h_off_line (etaShifted_zero_re_eq s₀ hσ₁ hσ₂ h_zero)` —
H6 directly contradicts `h_off_line`. (In ZeroLocation.lean the `< 3/4` branch
of H6 may use the already-proved `etaShifted_functional_eq_zero` of the same
file, provided H6 is stated *after* it and *before* this lemma.) ∎

Note: this entirely bypasses the four-fold contour argument. The contour
machinery (S3) remains useful as independent infrastructure, but RH-side
closure for Stage 2 reduces, after S1, to the legacy sorries of Part 3.

### S2. `conjReflLimit_zero_order` (ConjugateReflection.lean:75) — PROVABLE

```lean
lemma conjReflLimit_zero_order (s₀ : ℂ) (m : ℕ) (hm : m ≥ 1)
    (h_eta_order : ∃ φ : ℂ → ℂ, Differentiable ℂ φ ∧ φ s₀ ≠ 0 ∧
      ∀ s, etaShifted s = (s - s₀)^m * φ s)
    (h_targetH : targetH s₀ ≠ 0)
    (h_targetH_conj : targetH (starRingEnd ℂ s₀) ≠ 0) :
    ∃ ψ : ℂ → ℂ, Differentiable ℂ ψ ∧ ψ s₀ ≠ 0 ∧
      ∀ s, conjReflLimit s = (s - s₀)^(2*m) * ψ s
```
**Proof.** Obtain `⟨φ, hφ_diff, hφ_ne, hφ_eq⟩ := h_eta_order`. Define
```lean
ψ : ℂ → ℂ := fun s => (s - 3/4 + I) * targetH s * (φ s)^2
```
1. **Factorization.** For every `s`, by H5 and `hφ_eq s`:
   `conjReflLimit s = (s-3/4+I) * targetH s * ((s-s₀)^m * φ s)^2
    = (s-s₀)^(2*m) * ψ s`.
   Power bookkeeping: `((s-s₀)^m)^2 = (s-s₀)^(m*2) = (s-s₀)^(2*m)` via
   `← pow_mul` and `Nat.mul_comm` (or `mul_pow` + `pow_mul'`); then `ring`.
2. **Differentiability.** `(· - 3/4 + I)` and `targetH` are entire
   (`targetH_differentiable`; the first by `fun_prop` or
   `(differentiable_id.sub_const _).add_const _`); `φ^2` by
   `hφ_diff.pow` (or `hφ_diff.mul hφ_diff`). Product rule twice.
3. **Non-vanishing at `s₀`.** `mul_ne_zero` twice:
   - `s₀ - 3/4 + I ≠ 0`: suppose it is 0. Apply `starRingEnd ℂ`:
     `conj (s₀ - 3/4 + I) = conj s₀ - 3/4 - I = targetH (conj s₀)`
     (same simp set as H5), and `conj 0 = 0`, contradicting `h_targetH_conj`.
     (Direction check: `map_eq_zero`-style — `starRingEnd ℂ x = 0 ↔ x = 0`,
     available as `map_eq_zero` for the ring hom or `star_eq_zero`.)
   - `targetH s₀ ≠ 0`: hypothesis.
   - `(φ s₀)^2 ≠ 0`: `pow_ne_zero _ hφ_ne`. ∎

**Remark (do not rely on it, but know it):** `h_eta_order` is actually
*inconsistent* — see S4. The direct proof above is preferred because it
survives any future repair of the hypothesis.

### S3. `fourFoldApprox_tendstoUniformlyOn_boundary` (ZeroLocation.lean:119) — PROVABLE AFTER ADDING `hR_re'`

```lean
-- CURRENT (cannot be proved):
lemma fourFoldApprox_tendstoUniformlyOn_boundary (R : Rect) (s₀ : ℂ)
    (hs₀ : s₀ ∈ R.openInt)
    (hR_re : ∀ s ∈ R.closure, s.re > 1/2)
    (h_unique : ∀ z ∈ R.closure, etaShifted z = 0 → z = s₀ ∨ z = 3/2 - s₀) :
    TendstoUniformlyOn (fun n => fourFoldApprox n) fourFoldLimit atTop
      (R.closure \ R.openInt)
```
**Required change**: add `(hR_re' : ∀ s ∈ R.closure, s.re < 1)`. Without it
the statement is **false**: if `1 ∈ R.closure \ R.openInt`, pointwise
convergence already fails at `s = 1` — `etaPartialShifted n 1 = ∑_{k<n} (-1)^k/(k+1)
→ log 2 ≠ 0`, while the limit `fourFoldLimit 1` contains the factor
`etaShifted 1 = 0` (H1); moreover the factor `fApprox n (3/2 - 1) =
fApprox n (1/2)` contains `etaPartialShifted n (1/2) = ∑_{k<n} (-1)^k`, which
oscillates between 1 and 0. This mirrors the `hR_re'` hypothesis that was
already added to the three edge-integral lemmas in MultiplicityOne.lean.
The lemma's only would-be consumer (`zero_location_contradiction`) is
discharged independently in S1, so the signature change is safe.

**Proof (with `hR_re'`).** Prove convergence on all of `K := R.closure`
(compact: `Rect.isCompact_closure`), then restrict with
`TendstoUniformlyOn.mono (Set.diff_subset)`.

Write `g : ℂ → ℂ := fun s => targetH s * etaShifted s`. By definition
(check associativity: both `fourFoldApprox` and `fourFoldLimit` are
left-associated products), `fourFoldApprox n = ((T₁ n * T₂ n) * T₃ n) * T₄ n`
and `fourFoldLimit = ((G₁ * G₂) * G₃) * G₄` where:

| i | `Tᵢ n s` | `Gᵢ s` | uniform convergence on `K` |
|---|----------|--------|----------------------------|
| 1 | `conj (fApprox n (conj s))` | `conj (g (conj s))` | `tendstoUniformlyOn_conj_comp` applied to `fApprox_tendstoUniformlyOn` on `conj '' K` — compact (`hK.image Complex.continuous_conj`), and `re (conj z) = re z` so both Re-bounds transfer (`aesop` handled this in conjReflApprox_tendstoUniformlyOn:68–75; copy). |
| 2 | `fApprox n s` | `g s` | `fApprox_tendstoUniformlyOn K hK hR_re hR_re'` (after converting the `R.closure`-quantified hypotheses; they are literally about `K`). |
| 3 | `fApprox n (3/2 - s)` | `g (3/2 - s)` | Let `r : ℂ → ℂ := fun s => 3/2 - s` and `K' := r '' K` (compact: image under the continuous `r`; for `z = 3/2 - w`, `z.re = 3/2 - w.re ∈ (1/2, 1)` because `w.re ∈ (1/2,1)` — this is where `hR_re'` is essential). Take `fApprox_tendstoUniformlyOn K' ...`, apply `TendstoUniformlyOn.comp _ r` to get convergence of `fun n => fApprox n ∘ r` on `r ⁻¹' K'`, and `K ⊆ r ⁻¹' K'` (each `w ∈ K` has `r w ∈ r '' K = K'`), finish with `.mono`. |
| 4 | `conj (fApprox n (3/2 - conj s))` | `conj (g (3/2 - conj s))` | Apply `tendstoUniformlyOn_conj_comp` to the **row-3 construction performed on the set `conj '' K`** (which is compact with the same Re-bounds): that gives uniform convergence of `fun n s => conj ((fApprox n ∘ r) (conj s))` on `K`, which is definitionally `T₄`. |

Now combine with `tendstoUniformlyOn_mul` three times. Each application needs
uniform-in-`n` bounds `∃ M, ∀ n, ∀ s ∈ K, ‖Tᵢ n s‖ ≤ M` (and for the partial
products, the product of the two bounds). The boundedness argument is already
implemented **twice** in this repo — copy the block from
`conjReflApprox_tendstoUniformlyOn` (MultiplicityOne.lean:77–140):
1. The limit `Gᵢ` is continuous on the relevant compact set (continuity of
   `targetH`, of `etaShifted` away from 1 — every point of `K`, `conj '' K`,
   `r '' K`, `r '' (conj '' K)` has `re < 1` hence `≠ 1`; use
   `etaShifted_differentiableAt.continuousAt` from H5's consequence, or copy
   the `differentiableAt_riemannZeta`-based continuity blocks at
   MultiplicityOne:83–87), so `IsCompact.exists_bound_of_continuousOn` gives
   `M'` with `‖Gᵢ‖ ≤ M'`.
2. By uniform convergence, eventually (say `n ≥ N`) `‖Tᵢ n s‖ ≤ M' + 1`.
3. For the finitely many `n < N`, each `Tᵢ n` is continuous on the compact set
   (finite sums/products of continuous functions — the blocks at
   MultiplicityOne:100–118 do exactly this), hence bounded; take the max.
4. `‖conj x‖ = ‖x‖` (`RCLike.norm_conj` / `Complex.norm_conj` (search exact
   name; `norm_star` also works)) transfers bounds through rows 1 and 4. ∎

### S4. `even_multiplicity_contradiction` (MultiplicityOne.lean:466) — RESTATE in normalized coordinates

```lean
-- CURRENT (do not prove as written):
lemma even_multiplicity_contradiction (R : Rect) (s₀ : ℂ) (m : ℕ)
    (hm : m ≥ 2) (hs₀ : s₀ ∈ R.openInt) (hR_bottom : R.y_lo = 0)
    (hR_re : ∀ s ∈ R.closure, s.re > 1/2)
    (hR_re' : ∀ s ∈ R.closure, s.re < 1)
    (h_unique : ∀ z ∈ R.closure, etaShifted z = 0 → z = s₀)
    (h_boundary_ne : ∀ z ∈ R.closure \ R.openInt, etaShifted z ≠ 0)
    (h_order : ∃ φ : ℂ → ℂ, Differentiable ℂ φ ∧ φ s₀ ≠ 0 ∧
      ∀ s, etaShifted s = (s - s₀)^m * φ s) :
    False
```

**Diagnosis (confirmed).** As written, `h_order` is *inconsistent*: the global
factorization `∀ s, etaShifted s = (s-s₀)^m * φ s` with `φ` entire forces
`etaShifted` to be continuous at `1`, contradicting H1 (value 0) vs H2 (limit
`log 2 ≠ 0`). So the current statement is only provable **vacuously**
(continuity argument + `tendsto_nhds_unique` on `𝓝[≠] 1`, which is `NeBot`
for ℂ), which formalizes nothing. **Do not take the vacuous route.** The root
cause is a missing modelling layer: the statement quantifies the factorization
over all of ℂ in *original* coordinates, where the junk point `s = 1` is in
scope. The intended setup normalizes coordinates first (see Part 1 N): the
zero `s₀ = σ₀ + i·t₀` is moved to the reference point `3/4 + I` by the affine
map `normMap` — x is shifted and scaled, y is only scaled — and all
hypotheses are then stated on the fixed normalized rectangle, from which the
pulled-back junk point `normBadPoint σ₀ t₀ = 3/4 + (1-σ₀)/t₀` (a **real**
point!) is excluded by the choice of `δ` (N3).

**Replacement statement** (consumers: only the S7 chain, itself being
restated — the signature change is safe):
```lean
lemma even_multiplicity_contradiction' (σ₀ t₀ : ℝ) (m : ℕ) (hm : 2 ≤ m)
    (hσ : 1/2 < σ₀) (hσ' : σ₀ < 1) (ht : 0 < t₀)
    (h_zero : etaShifted (σ₀ + t₀ * I) = 0)
    (h_order : ∃ φ : ℂ → ℂ,
      (∀ z, z ≠ normBadPoint σ₀ t₀ → DifferentiableAt ℂ φ z) ∧
      φ (3/4 + I) ≠ 0 ∧
      ∀ z, z ≠ normBadPoint σ₀ t₀ →
        etaShiftedNorm σ₀ t₀ z = (z - (3/4 + I))^m * φ z) :
    False
```
Notes on the shape:
- The factorization now lives on `ℂ \ {normBadPoint σ₀ t₀}` — exactly the
  set where `etaShiftedNorm` is differentiable (N2) — so `h_order` is
  **consistent** (it is satisfied by the true local order at any genuine zero,
  extended by `φ z := etaShiftedNorm z / (z - (3/4+I))^m` off the zero), and
  the lemma now carries its intended content: *no zero of order ≥ 2*.
- `WLOG t₀ > 0` and the exclusion of real zeros are handled *outside* this
  lemma by N1 (conjugate-pair symmetry; positivity of η on the real segment).
- The uniqueness/boundary hypotheses of the old statement are dropped here:
  they were tied to S6's unprovable isolation claim. If the eventual proof
  needs zero-freeness on the contour edges, add it back as an explicit
  hypothesis in normalized form (`∀ z ∈ R.closure \ R.openInt,
  etaShiftedNorm σ₀ t₀ z ≠ 0`) rather than re-deriving it from isolation.

**Status of the proof: genuine open core — research-level.** With the
normalization in place nothing is vacuous anymore, and the intended residue
argument becomes well-posed on the fixed rectangle
`R = mkHalfRect (3/4-δ) (3/4+δ) T`, `T > 1`, `δ < min (σ₀-1/2) (1-σ₀) / t₀`
(N3). The available pieces, all in normalized form via N4:
1. `conjReflApproxNorm n` is entire; `R.boundaryIntegral (conjReflApproxNorm n) = 0`
   (N4, via `conjReflApprox_cauchy` composed with `normMap`).
2. Uniform convergence on `R.closure` to the closed-form limit
   `(z-3/4+I)(z-3/4-I)·(etaShiftedNorm z)²` (N4); edge integrals converge
   (the proved edge lemmas, transported through `TendstoUniformlyOn.comp`).
3. Bottom edge: `conjReflApproxNorm n (x) = ‖fApproxNorm n x‖² ≥ 0` (N4), and
   strict positivity for large n (transport `real_axis_integral_pos`;
   its non-degeneracy input `fApprox_not_identically_zero` is proved).
4. `h_order` + N4's closed form give the limit a zero of order exactly
   `2m + 1 ≥ 5` at `3/4 + I`: `2m` from `etaShiftedNorm²` **plus 1** from the
   factor `(z - 3/4 - I)`, which vanishes there to order 1 — while its mirror
   factor `(z - 3/4 + I)` does **not** vanish at `3/4 + I` (it equals `2I`);
   it vanishes at the reflected point `3/4 - I`, outside the upper
   half-rectangle. This separation is exactly the point of the y-shift
   (N3½): the `targetH` zero and its conjugate mirror stay simple and apart
   instead of colliding into a double zero on the real axis. Net effect of
   the design: a simple zero (`m = 1`) gives the limit an order-3 zero at
   `3/4 + I`, while `m ≥ 2` gives order `2m + 1 ≥ 5`; the contradiction must
   separate these cases through the contour data.
5. The missing step is the actual contradiction: a residue/argument-principle
   computation for `1/limit` (pole of even order ≥ 6 at `3/4+I`) against the
   positive bottom edge, with the zero-free Euler approximants of Part 3
   replacing the partial sums wherever a reciprocal crosses the limit. The
   `dslope` machinery in RectangleStrategy.lean
   (`boundaryIntegral_recipEta_eq`, `recipEta_rect_integral_ne_zero_of_zero`)
   is the closest template. **No complete mathematical writeup of this step
   exists in the repo.** Formalize steps 1–4 (all within reach), then stop
   and report; do not improvise step 5.

### S5. `nonreal_edges_sum_zero` (MultiplicityOne.lean:350) — NOT PROVABLE AS STATED; restate

```lean
-- CURRENT:
lemma nonreal_edges_sum_zero (R : Rect) (s₀ : ℂ)
    (hs₀ : s₀ ∈ R.openInt)
    (h_boundary_ne : ∀ z ∈ R.closure \ R.openInt, conjReflLimit z ≠ 0) :
    ∫ x in R.x_lo..R.x_hi, conjReflLimit (x + R.y_hi * I) +
    ∫ y in R.y_lo..R.y_hi, conjReflLimit (R.x_hi + y * I) -
    ∫ y in R.y_lo..R.y_hi, conjReflLimit (R.x_lo + y * I) = 0
```
**Problems.** (a) Lean's `∫ x in a..b, e` notation extends to the end of the
expression, so the *first* integrand swallows the following `+ ∫ ... - ∫ ...`;
the statement does not say what its name suggests. (b) Even with intended
parenthesization, the combination lacks the `I`-weights of the Cauchy/Green
boundary orientation and omits the bottom edge, so it does not follow from
holomorphy and there is no reason for it to be true. (c) There are no
Re-bounds, so `1` may lie in `R.closure`, where `conjReflLimit` is not even
continuous (H1/H2 via H5).

**Replacement** (safe: the only consumers are S4, handled above, and prose):
```lean
lemma conjReflLimit_boundaryIntegral_zero (R : Rect)
    (hR_re' : ∀ s ∈ R.closure, s.re < 1) :
    R.boundaryIntegral conjReflLimit = 0
```
**Proof.** By H5 (as a `funext` or via `DifferentiableOn.congr`),
`conjReflLimit = fun s => (s - 3/4 + I) * targetH s * (etaShifted s)^2`.
Every `z ∈ R.closure` has `z.re < 1`, hence `z ≠ 1` (real parts differ), so
`etaShifted` is differentiable at `z` (`etaShifted_differentiableAt`, H5
consequence), and the polynomial factors are entire. Therefore
`DifferentiableOn ℂ conjReflLimit R.closure`
(`DifferentiableAt.differentiableWithinAt` pointwise). Apply
`rect_cauchy R conjReflLimit` (RectangleStrategy:204). ∎

If an "edges" reformulation is wanted afterwards, derive it by unfolding
`Rect.boundaryIntegral`:
`∫bottom = ∫top - I•∫right + I•∫left` — i.e. the real-axis (bottom) integral
equals the correctly-weighted combination of the three non-real edges. State
that as a corollary by `linear_combination` / `linarith`-style rearrangement
of the boundary identity.

### S6. `exists_isolating_rect` (ConjugateReflection.lean:159) — NOT PROVABLE AS STATED; partial + restate

```lean
-- CURRENT:
lemma exists_isolating_rect (s₀ : ℂ) (hσ₁ : s₀.re > 1/2) (hσ₂ : s₀.re < 1)
    (h_zero : etaShifted s₀ = 0) :
    ∃ (δ T : ℝ) (hδ : 0 < δ) (hT : s₀.im + 1 < T) (hx : ...) (hT' : 0 < T),
      let R := mkHalfRect (s₀.re - δ) (s₀.re + δ) T hx hT'
      s₀ ∈ R.openInt ∧ (∀ z ∈ R.closure, etaShifted z = 0 → z = s₀) ∧
      (∀ z ∈ R.closure \ R.openInt, etaShifted z ≠ 0)
```
**Why it cannot be proved.** Two independent obstructions:
1. If `s₀.im ≤ 0`, the first conjunct `s₀ ∈ R.openInt` is false for every
   admissible `R` (`y_lo = 0` forces `0 < s₀.im`), and the hypotheses cannot
   refute `s₀.im ≤ 0` for `s₀.re = 3/4` (zeros come in conjugate pairs, so
   lower-half-plane zeros are consistent with everything available).
2. Even with `0 < s₀.im`: by H6, every available zero has `re = 3/4`, so when
   `s₀.re = 3/4` the rectangle necessarily contains the critical segment
   `{3/4 + iy : 0 ≤ y ≤ T}` with `T > s₀.im + 1`, and **no available result
   excludes other zeros on that segment below height `T`** (in actual
   mathematics such zeros exist once `s₀.im` is large, so no proof can exist).

**What IS provable — formalize these two pieces:**

(i) *Vacuous discharge off the line*: if one adds the hypothesis
`s₀.re ≠ 3/4`, the lemma is provable by `exact absurd (etaShifted_zero_re_eq
s₀ hσ₁ hσ₂ h_zero) h_off` (H6). Not useful by itself, but it documents that
the only live case is `re = 3/4`.

(ii) *Isolation in a small square* (the honest replacement; prove it and leave
the original statement sorry'd or delete it after updating callers — it has
no proved consumers):
```lean
lemma etaShifted_isolated_zero (s₀ : ℂ) (hσ₁ : s₀.re > 1/2) (hσ₂ : s₀.re < 1) :
    ∃ ε > 0, ∀ z, z ≠ s₀ → ‖z - s₀‖ < ε → etaShifted z ≠ 0
```
**Proof.**
1. `s₀ ≠ 1` (`re < 1`). `etaShifted` is analytic at `s₀`:
   `etaShifted_differentiableAt` on the open set `{s | s ≠ 1}` upgraded with
   `DifferentiableOn.analyticAt` (the pattern at RectangleStrategy:1260,
   `eta_zero_isolated_in_rect`, does this for `etaRect`; compose with
   `s ↦ 2s-1` or redo directly).
2. Dichotomy `AnalyticAt.eventually_eq_zero_or_eventually_ne_zero`
   (IsolatedZeros.lean:130): either `etaShifted =ᶠ[𝓝 s₀] 0` or
   `∀ᶠ z in 𝓝[≠] s₀, etaShifted z ≠ 0`. The second alternative yields `ε` by
   `Metric.eventually_nhdsWithin_iff` / `Metric.mem_nhdsWithin_iff` unpacking.
3. Rule out the first alternative: if `etaShifted` vanishes on a neighborhood
   of `s₀`, then by the identity theorem it vanishes on the preconnected open
   set `U := {s | s.re > 1/2 ∧ s ≠ 1}` (preconnectedness:
   `isPreconnected_halfplane_minus_one`, EtaConvergence:260; analyticity of
   `etaShifted` on `U` as in step 1; use
   `AnalyticOnNhd.eqOn_zero_of_preconnected_of_eventuallyEq_zero` (search this
   family — the `frequently` variant is used at EtaConvergence:304)). But
   `(3/2 : ℂ) ∈ U` and `etaShifted (3/2) = dirichletEta 2 ≠ 0`
   (`dirichletEta_ne_zero_at_two`, EtaStrategy:482; the argument computation
   `2*(3/2)-1 = 2` is `norm_num`). Contradiction. ∎

This is the exact analogue of the proved `eta_zero_isolated_in_rect`
(RectangleStrategy:1260) — mirror its Lean structure.

### S7. `etaShifted_zeros_simple` (MultiplicityOne.lean:481) — FALSE AS STATED; restate

```lean
-- CURRENT:
theorem etaShifted_zeros_simple (s₀ : ℂ) (hσ₁ : s₀.re > 1/2)
    (hσ₂ : s₀.re < 1) (h_zero : etaShifted s₀ = 0) :
    ∃ φ : ℂ → ℂ, Differentiable ℂ φ ∧ φ s₀ ≠ 0 ∧
      ∀ s, etaShifted s = (s - s₀) * φ s
```
**Why it is false.** The conclusion forces `etaShifted` to be continuous at
`1` (product of continuous functions), but `etaShifted` is discontinuous at 1
(value 0 by H1, limit `log 2 ≠ 0` by H2). So the conclusion is refutable
whenever the hypotheses hold — and the hypotheses are satisfiable (zeros of η
on the critical line exist in actual mathematics, with `re = 3/4` after the
shift; nothing in scope refutes them). Hence no proof can exist. **Do not
attempt the statement as written.**

**Two-layer repair:**

*Layer 1 (provable now — existence of a finite order).* Prove:
```lean
theorem etaShifted_zero_finite_order (s₀ : ℂ) (hσ₁ : s₀.re > 1/2)
    (hσ₂ : s₀.re < 1) (h_zero : etaShifted s₀ = 0) :
    ∃ (m : ℕ) (φ : ℂ → ℂ), 0 < m ∧ AnalyticAt ℂ φ s₀ ∧ φ s₀ ≠ 0 ∧
      ∀ᶠ s in 𝓝 s₀, etaShifted s = (s - s₀)^m • φ s
```
**Proof.** `h_an : AnalyticAt ℂ etaShifted s₀` (S6 step 1).
`analyticOrderAt etaShifted s₀ ≠ ⊤`: by `analyticOrderAt_eq_top`
(Order.lean:76) it would mean `etaShifted =ᶠ[𝓝 s₀] 0`, refuted exactly as in
S6 step 3. So the order is a natural number `m`
(`ENat` case analysis / `ENat.ne_top_iff_exists`), and
`AnalyticAt.analyticOrderAt_eq_natCast` (Order.lean, statement quoted in
Part 0) provides `φ` with the eventual factorization. `0 < m`: if `m = 0` the
factorization at `s = s₀` gives `etaShifted s₀ = φ s₀ ≠ 0` (the `(s-s₀)^0 = 1`
case; evaluate the `∀ᶠ` at `s₀` itself — `Filter.Eventually.self_of_nhds`),
contradicting `h_zero`. (The `•` here is ℂ-scalar multiplication on ℂ, i.e.
multiplication; `smul_eq_mul` converts.) ∎

*Layer 2 (NOT provable — the open core).* `m = 1` (simplicity). This is the
genuine mathematical content of Stage 1 and nothing in the repository proves
it; simplicity of ζ-zeros is an open problem. Options: leave a sorry'd lemma
`etaShifted_order_eq_one` clearly marked as the open core, or restate
downstream results to carry `m` as data. Downstream impact:
`etaShifted_zeros_simple_on_line` (ZeroLocation:174) must be restated to use
the Layer-1 form (its other component, `etaShifted_zeros_on_critical_line`,
becomes fully proved once S1 lands). `riemann_hypothesis_via_shifted_eta` is
unaffected (it only uses the location theorem).

---

## Part 3: After S1–S7 — what actually remains, and where Bagchi enters

Once S1–S4 are formalized and S5–S7 are restated as above, the **only**
unproved inputs below `riemann_hypothesis_via_shifted_eta` are:

1. **The legacy chain under `etaRect_ne_zero_critical_strip`**
   (RectangleStrategy.lean), used by H6/S1 and by the already-proved
   `fApprox_not_identically_zero`:
   - `recipEta_rect_contour_integral_eq_zero` (line 913) — `∮ 1/η = 0` as a
     limit of `∮ 1/etaEulerApprox P = 0`. **This is where Bagchi
     universality is load-bearing**: the approximants must be *zero-free* on
     the rectangle (proved: `etaEulerApprox_ne_zero`) and converge uniformly
     (proved modulo the three PNT inputs:
     `etaEulerApprox_tendstoUniformlyOn_rect`); the reciprocal then converges
     uniformly by `reciprocal_tendstoUniformlyOn_of_nonvanishing`
     (EtaConvergenceExtended:51, proved). The raw partial sums `η_n` must NOT
     be used here — they have spurious zeros in the strip.
   - `rect_integral_inv_sub_eq` (line 952) — `∮ 1/(z-w) = 2πi` for `w` inside
     a rectangle (standard winding-number computation; Mathlib's
     `Complex.integral_boundary_rect_eq_zero...` family and
     `DiffContOnCl.circleIntegral_sub_inv_smul` are the raw material).
   - The three Bagchi/PNT inputs (lines 548, 563, 587):
     `primeZetaTail_uniform_small`, `higherPrimeSum_uniform_small`,
     `eulerProd_zeta_exp_connection`. The first is a genuine PNT consequence
     (Abel summation against `π(x) ~ x/log x`; Mathlib now has PNT-adjacent
     material in `Mathlib.NumberTheory.PrimeCounting` /
     `PrimeNumberTheoremAnd`-style results — survey before attempting). The
     second is elementary domination (`∑_p p^{-2σ}` summable for `σ > 1/2`).
     The third is the exp-log Euler identity (`Complex.exp_sum`,
     `riemannZeta_eulerProduct`-family lemmas exist in Mathlib:
     `riemannZeta_eulerProduct_exp_log` (search) is close).
2. **The simplicity core** (S7 Layer 2) — open mathematics; no plan can
   discharge it.
3. If S4's `h_order` hypothesis is ever repaired to its intended meaning
   (factorization away from `s = 1`), the residue argument reopens — see the
   "intended route" paragraph in S4.

### Recommended execution order for the formalizer

1. H1, H2 (self-contained; only Mathlib).
2. H3, H4, H5 (Schwarz reflection stack).
3. S2 (uses H4/H5 only).
4. H6, then S1 (note import placement: H6's reflection case can inline the
   functional-equation argument to avoid cycles).
5. S3 (after adding `hR_re'` to its statement).
6. S5 replacement, S6 replacement (`etaShifted_isolated_zero`), S7 Layer 1
   (`etaShifted_zero_finite_order`) — these three share S6-step-1's
   `AnalyticAt` infrastructure; build it once.
7. S4 last (vacuous; confirm with project owner before merging, per the
   warning).
8. `lake build` after each lemma; all listed project lemmas compile today, so
   any breakage is local to your edit.
