# Implementation Plan: RectangleStrategy.lean Sorry Elimination

## File: `RiemannProof/RiemannProof/RectangleStrategy.lean`

---

## Task 1: Prove `norm_exp_sub_one_le_two_norm` (line 593–596)

```lean
lemma norm_exp_sub_one_le_two_norm (w : ℂ)
    (hw : ‖w‖ < 1 / 2) :
    ‖Complex.exp w - 1‖ ≤ 2 * ‖w‖
```

**Mathlib lemma exists**: `Complex.norm_exp_sub_one_le` with signature:
```lean
@Complex.norm_exp_sub_one_le : ∀ {x : ℂ}, ‖x‖ ≤ 1 → ‖Complex.exp x - 1‖ ≤ 2 * ‖x‖
```

**Proof**:
```lean
lemma norm_exp_sub_one_le_two_norm (w : ℂ)
    (hw : ‖w‖ < 1 / 2) :
    ‖Complex.exp w - 1‖ ≤ 2 * ‖w‖ := by
  exact Complex.norm_exp_sub_one_le (le_of_lt (lt_of_lt hw (by norm_num)))
```
The condition `‖w‖ < 1/2` implies `‖w‖ ≤ 1` by `linarith` / `norm_num`.

---

## Task 2: Prove `zetaEulerProd_tendstoUniformlyOn_rect` (line 598–628)

```lean
lemma zetaEulerProd_tendstoUniformlyOn_rect (R : Rect)
    (hR_lo : ∀ z ∈ R.closure, z.re > 1 / 2)
    (hR_hi : ∀ z ∈ R.closure, z.re < 1) :
    TendstoUniformlyOn (fun P => zetaEulerProd P) riemannZeta
      atTop R.closure
```

**Context already computed** (lines 603–626):
- `hK : IsCompact R.closure`
- `hα : ∃ α > 0, ∀ z ∈ R.closure, z.re ≥ 1/2 + α`
- `M : ℝ` with `hM : ∀ z ∈ R.closure, ‖riemannZeta z‖ ≤ M`

**Proof strategy** — replace the final `sorry` at line 628:

Use `Metric.tendstoUniformlyOn_iff`:
```
∀ ε > 0, ∀ᶠ P in atTop, ∀ z ∈ R.closure,
  dist (riemannZeta z) (zetaEulerProd P z) < ε
```

Steps:
1. Fix `ε > 0`.
2. From `hα`, obtain `⟨α, hα_pos, hα_bound⟩`.
3. Apply `primeZetaTail_uniform_small R.closure hK ⟨α, hα_pos, hα_bound⟩`
   with `ε' := min (ε / (2 * (M + 1))) (1/4)` to get `P₁`.
4. Apply `higherPrimeSum_uniform_small R.closure hK ⟨α, hα_pos, hα_bound⟩`
   with same `ε'` to get `P₂`.
5. Set `P₀ := max P₁ P₂`.
6. For `P ≥ P₀` and `z ∈ R.closure`:
   - Let `w := -(primeZetaTail) - higherPrimeSum`.
   - `‖w‖ ≤ ‖primeZetaTail‖ + ‖higherPrimeSum‖ < 2ε' ≤ 1/2`.
   - By `eulerProd_zeta_exp_connection`:
     `zetaEulerProd P z = riemannZeta z * Complex.exp w`.
   - So `‖zetaEulerProd P z - riemannZeta z‖
       = ‖riemannZeta z‖ * ‖Complex.exp w - 1‖`.
   - By `norm_exp_sub_one_le_two_norm w ‖w‖<1/2`:
     `‖Complex.exp w - 1‖ ≤ 2‖w‖ < 4ε'`.
   - Therefore `‖...‖ < M * 4ε' ≤ M * 4 * ε/(2(M+1)) < ε`.

**Lean tactic sketch**:
```lean
rw [Metric.tendstoUniformlyOn_iff]
intro ε hε_pos
obtain ⟨α, hα_pos, hα_bound⟩ := hα
set ε' := min (ε / (2 * (M + 1))) (1 / 4)
have hε'_pos : ε' > 0 := by
  dsimp only [ε']; exact lt_min (div_pos hε_pos (by linarith)) (by norm_num)
have hε'_le : ε' ≤ 1 / 4 := min_le_right _ _
obtain ⟨P₁, hP₁⟩ := primeZetaTail_uniform_small R.closure hK
  ⟨α, hα_pos, hα_bound⟩ ε' hε'_pos
obtain ⟨P₂, hP₂⟩ := higherPrimeSum_uniform_small R.closure hK
  ⟨α, hα_pos, hα_bound⟩ ε' hε'_pos
use max P₁ P₂
intro P hP_ge
-- For z ∈ R.closure, bound the tail
intro z hz
set w := -(∑' p, if Nat.Prime p ∧ p > P then (p:ℂ)^(-z) else 0)
  - higherPrimeSum P z
have hw_lt_half : ‖w‖ < 1 / 2 := by ...  -- triangle ineq + bounds
have h_conn := eulerProd_zeta_exp_connection P z (by linarith [hR_lo z hz])
-- zetaEulerProd P z = riemannZeta z * exp w
-- ‖zetaEulerProd P z - riemannZeta z‖ = ‖riemannZeta z‖ * ‖exp w - 1‖
-- ≤ M * 2 * ‖w‖ < M * 2 * (2ε') ≤ ε
calc ...
```

**Key Mathlib lemmas**:
- `Metric.tendstoUniformlyOn_iff` (already checked, note: `dist (f x) (F n x)`)
- `norm_mul_le`, `norm_sub_le`, `norm_neg`
- `Filter.eventually_atTop` ↔ `∃ a, ∀ b ≥ a, p b`
- `Complex.norm_exp_sub_one_le` / `norm_exp_sub_one_le_two_norm`

---

## Task 3: Prove `etaEulerApprox_tendstoUniformlyOn_rect` (lines 696–723)

```lean
lemma etaEulerApprox_tendstoUniformlyOn_rect (R : Rect)
    (hR_lo : ∀ z ∈ R.closure, z.re > 1 / 2)
    (hR_hi : ∀ z ∈ R.closure, z.re < 1) :
    TendstoUniformlyOn (fun P => etaEulerApprox P) etaRect
      atTop R.closure
```

**Context already computed**:
- `h_euler_conv` (line 703): `TendstoUniformlyOn (fun P ↦ zetaEulerProd P) riemannZeta atTop R.closure`
- `h_bounded` (lines 706–720): `∃ B, ∀ z ∈ R.closure, ‖etaFactRect z‖ ≤ B`
- `⟨B, hB⟩` (line 722): the bound extracted

**Proof strategy** — replace `sorry` at line 723:

Since `etaEulerApprox P s = etaFactRect s * zetaEulerProd P s` and
`etaRect s = etaFactRect s * riemannZeta s`, the difference is:
```
‖etaEulerApprox P s - etaRect s‖ = ‖etaFactRect s‖ * ‖zetaEulerProd P s - riemannZeta s‖
                                 ≤ B * ‖zetaEulerProd P s - riemannZeta s‖
```

Steps:
1. Fix `ε > 0`.
2. Apply `Metric.tendstoUniformlyOn_iff` to `h_euler_conv` with `ε/(B+1)`.
3. Get `P₀` such that `∀ P ≥ P₀, ∀ z ∈ R.closure,
   dist (riemannZeta z) (zetaEulerProd P z) < ε/(B+1)`.
4. For `P ≥ P₀, z ∈ R.closure`:
   `‖etaEulerApprox P z - etaRect z‖ = ‖etaFactRect z‖ * ‖zetaEulerProd P z - riemannZeta z‖
    ≤ B * ε/(B+1) < ε`.

**Lean tactic sketch**:
```lean
rw [Metric.tendstoUniformlyOn_iff] at h_euler_conv ⊢
intro ε hε_pos
have hB_pos : B + 1 > 0 := by linarith [norm_nonneg _]
have := h_euler_conv (ε / (B + 1)) (div_pos hε_pos hB_pos)
-- this : ∀ᶠ P in atTop, ∀ z ∈ R.closure, dist (riemannZeta z) (zetaEulerProd P z) < ε/(B+1)
filter_upwards [this] with P hP z hz
unfold etaEulerApprox etaRect etaFactRect
-- ‖etaFactRect z * zetaEulerProd P z - etaFactRect z * riemannZeta z‖
-- = ‖etaFactRect z‖ * ‖zetaEulerProd P z - riemannZeta z‖
calc
  ‖etaFactRect z * (zetaEulerProd P z - riemannZeta z)‖
    = ‖etaFactRect z‖ * ‖zetaEulerProd P z - riemannZeta z‖ := norm_mul _ _
  _ ≤ B * ‖zetaEulerProd P z - riemannZeta z‖ :=
      mul_le_mul_of_nonneg_right (hB z hz) (norm_nonneg _)
  _ < B * (ε / (B + 1)) :=
      mul_lt_mul_of_nonneg_left (by simpa [dist_eq_norm] using hP z hz) (by linarith [hB z hz])
  _ ≤ ε := by
      rw [mul_div_assoc]; exact mul_le_of_le_one_left (by linarith) (by linarith)
```

**Note**: Use `dist_eq_norm'` (Mathlib: `dist a b = ‖a - b‖`) to convert
the `dist` in `h_euler_conv` to norm form.

---

## Task 4: Prove `etaPartialRect_tendstoUniformlyOn` (line 339–343)

```lean
lemma etaPartialRect_tendstoUniformlyOn (K : Set ℂ) (hK : IsCompact K)
    (hK_lower : ∀ z ∈ K, z.re > 1 / 2)
    (hK_upper : ∀ z ∈ K, z.re < 1) :
    TendstoUniformlyOn (fun n => etaPartialRect n) etaRect atTop K
```

**Difficulty: EASY** — Abel summation infrastructure already exists.

**Mathematical content**: The Dirichlet eta series
`η_n(s) = Σ_{k=1}^n (-1)^{k-1}/k^s` converges uniformly to
`η(s) = (1-2^{1-s})ζ(s)` on compact subsets of `{1/2 < Re < 1}`.

**Existing infrastructure in `Legacy.lean`**:
`bohr_cahen_algebraic_tail_bound` (lines 135–241) is a **fully proved**
Abel summation by parts lemma giving the uniform tail bound:
```lean
‖∑ n ∈ Icc m N, a_n / n^s‖ ≤ C · m^(σ₀ - σ)
```
where `C` depends on the partial sum bound `M_P`, `‖s - s₀‖`, and
`σ - σ₀`. The proof uses:
- `h_abel`: Abel summation identity `a_n/n^s = (S_n - S_{n-1}) · n^{s₀-s}`
- `h_bound`: Triangle inequality with `‖S_n‖ ≤ M_P`
- `h_mean_value`: MVT bound `‖n^{s₀-s} - (n+1)^{s₀-s}‖ ≤ ‖s-s₀‖ · n^{σ₀-σ-1}`
- Integral comparison for the telescoping sum

**Adaptation to `etaPartialRect`**: The eta series has coefficients
`a_k = (-1)^{k-1}` with partial sums `A_n = Σ_{k=1}^n (-1)^{k-1}`
satisfying `|A_n| ≤ 1`. This is much simpler than the Möbius case
(`μ(n)` with random perturbations `X_mult`) handled in Legacy.lean.

**Proof steps**:
1. Set `s₀ = 0` (or any point with `σ₀ = 0`). Then `A_n = Σ (-1)^{k-1}`
   has `‖A_n‖ ≤ 1` for all n (alternating 1, 0, 1, 0, ...).
2. Apply Abel summation by parts (same technique as `bohr_cahen`):
   `Σ_{k=m}^N (-1)^{k-1}/k^s = Σ (A_k - A_{k-1}) · k^{-s}`
   with `A_k = Σ_{j=1}^k (-1)^{j-1}`.
3. Tail bound: `‖Σ_{k=m}^∞ (-1)^{k-1}/k^s‖ ≤ C · m^{-σ}` where
   `C = 2 + ‖s‖ + ‖s‖/σ` and `σ = Re(s) > 0`.
4. On compact `K ⊂ {Re > 1/2}`: `σ ≥ 1/2 + α` uniformly, so
   `C` is uniformly bounded and `m^{-σ} ≤ m^{-1/2-α} → 0`.
5. This gives uniform Cauchy criterion → uniform convergence.
6. The limit equals `η(s) = (1-2^{1-s})ζ(s)` by the known identity
   for the alternating Dirichlet series.

**Key Lean pattern** (adapt from `bohr_cahen_algebraic_tail_bound`):
```lean
-- Alternating partial sums, bounded by 1
set A := fun k : ℕ => ∑ j ∈ Finset.Icc 1 k, (-1 : ℂ)^(j-1)
have hA : ∀ k, ‖A k‖ ≤ 1 := by
  intro k; cases Nat.even_or_odd k <;> simp_all [A, ...]
  -- A_k = 1 for odd k, 0 for even k
-- Abel summation by parts (copy pattern from bohr_cahen h_abel)
-- Tail bound (copy pattern from bohr_cahen h_bound + h_mean_value)
-- Uniform Cauchy → uniform convergence
```

---

## Task 5: Prove `etaPartialRect_tendstoUniformlyOn_closure` (lines 351–356)

```lean
lemma etaPartialRect_tendstoUniformlyOn_closure
    (R₀ : Rect)
    (hR₀_re_pos : ∀ z ∈ R₀.closure, z.re > 1 / 2)
    (hR₀_eta_factor : ∀ z ∈ R₀.closure, etaFactRect z ≠ 0) :
    TendstoUniformlyOn (fun n => etaPartialRect n) etaRect atTop R₀.closure
```

**Proof**: Direct application of `etaPartialRect_tendstoUniformlyOn`:
```lean
exact etaPartialRect_tendstoUniformlyOn R₀.closure
  R₀.isCompact_closure hR₀_re_pos hR₀_upper
```
where `hR₀_upper : ∀ z ∈ R₀.closure, z.re < 1` must be derived.
This requires `hR₀_eta_factor` — if any `z ∈ R₀.closure` has `z.re ≥ 1`,
then `etaFactRect z` could be zero (specifically at `s = 1`).
Since `hR₀_eta_factor` guarantees `etaFactRect z ≠ 0` for all
`z ∈ R₀.closure`, and the zeros of `etaFactRect` are at
`s = 1 + 2πik/ln 2`, we can show `z.re < 1` or `z` avoids those
specific points.

**If the rectangle extends to Re ≥ 1**: The eta series converges
absolutely for `Re > 1`, so the convergence still holds. The `hR₀_upper`
hypothesis can be relaxed. A cleaner approach:

Split R₀.closure into `{z | z.re ≤ 1}` and `{z | z.re > 1}`:
- For `z.re < 1`: alternating series convergence (Task 4)
- For `z.re ≥ 1`: absolute convergence of `Σ 1/k^s`
- Combine via `TendstoUniformlyOn.congr` on the union

**Practical approach**: Add `(hR₀_upper : ∀ z ∈ R₀.closure, z.re < 1)`
as an explicit hypothesis to avoid the case analysis, since the main
usage in Section 8 already assumes `hR_hi : ∀ z ∈ R.closure, z.re < 1`.

---

## Task 6: Prove `recipEta_rect_contour_integral_eq_zero` (lines 737–743)

```lean
lemma recipEta_rect_contour_integral_eq_zero (R : Rect) (s₀ : ℂ)
    (hs₀_int : s₀ ∈ R.openInt)
    (hR_lo : ∀ z ∈ R.closure, z.re > 1 / 2)
    (hR_hi : ∀ z ∈ R.closure, z.re < 1)
    (heta_nz_off_s₀ : ∀ z ∈ R.closure, z ≠ s₀ → etaRect z ≠ 0) :
    R.boundaryIntegral (fun s => 1 / etaRect s) = 0
```

**Proof strategy**:

1. From `etaEulerApprox_tendstoUniformlyOn_rect R hR_lo hR_hi`, we have:
   `TendstoUniformlyOn (fun P ↦ etaEulerApprox P) etaRect atTop R.closure`.

2. Since `s₀ ∈ R.openInt` and `etaRect s₀ = 0` (implied by the theorem's
   usage context — note: `etaRect s₀ = 0` is NOT a hypothesis here,
   but `heta_nz_off_s₀` says `etaRect z ≠ 0` for `z ≠ s₀` on the closure).

   **Wait**: Actually `etaRect s₀` might or might not be zero. The hypothesis
   `heta_nz_off_s₀` says `etaRect z ≠ 0` for `z ∈ R.closure, z ≠ s₀`.
   If `s₀ ∉ R.closure`, then `etaRect ≠ 0` everywhere on `R.closure`, and
   `1/etaRect` is continuous on `R.closure`. If `s₀ ∈ R.closure` (which it is,
   since `R.openInt ⊂ R.closure`), then `etaRect` could be zero at `s₀`,
   but `s₀` is in the open interior, NOT on the boundary edges.

3. The boundary integral `R.boundaryIntegral` only evaluates `f` on the
   four edges of R, which are subsets of `R.closure \ R.openInt`.
   Since `s₀ ∈ R.openInt`, `s₀` is NOT on any edge. So on all edges,
   `z ≠ s₀` and hence `etaRect z ≠ 0`.

4. From uniform convergence of `etaEulerApprox P → etaRect` on `R.closure`,
   and `etaRect z ≠ 0` on edges (with compactness giving
   `‖etaRect z‖ ≥ δ > 0` on edges):
   - `1/etaEulerApprox P → 1/etaRect` uniformly on edges.

5. For each P: `R.boundaryIntegral (recipEtaEulerApprox P) = 0`
   by `recipEulerApprox_rect_integral_eq_zero P R hR_lo hR_hi`.

6. The boundary integral is a finite sum of interval integrals, each of
   which converges by uniform convergence of the integrand.
   Therefore `R.boundaryIntegral (1/etaRect) = lim 0 = 0`.

**Key steps in Lean**:
- Show `s₀ ∉ edges`: `s₀ ∈ R.openInt` implies `s₀.re > R.x_lo`, etc.
- Show `∃ δ > 0, ∀ z ∈ edges, ‖etaRect z‖ ≥ δ` (compactness + continuity + nonzero).
- Use `TendstoUniformlyOn.inv` (if it exists) or prove directly:
  `‖1/etaEulerApprox P z - 1/etaRect z‖ = ‖etaRect z - etaEulerApprox P z‖ / (‖etaEulerApprox P z‖ * ‖etaRect z‖)`.
- Pass limit through the boundary integral using
  `intervalIntegral.tendsto_integral_of_tendstoUniformly`.

**Lean tactic outline**:
```lean
-- 1. s₀ not on edges
have hs₀_not_edge : ∀ z ∈ R.closure, z.re = R.x_lo ∨ z.re = R.x_hi
  ∨ z.im = R.y_lo ∨ z.im = R.y_hi → z ≠ s₀ := by ...
-- 2. etaRect nonzero on edges, get lower bound δ
have h_edges_nz : ∀ z ∈ R.closure, (z.re = R.x_lo ∨ ...) → etaRect z ≠ 0 := ...
obtain ⟨δ, hδ_pos, hδ⟩ : ∃ δ > 0, ∀ z ∈ edges, ‖etaRect z‖ ≥ δ := ...
-- 3. Uniform convergence of reciprocals on edges
have h_recip_conv : TendstoUniformlyOn (fun P => recipEtaEulerApprox P)
  (fun s => 1/etaRect s) atTop edges := ...
-- 4. Each approximant integral = 0
have hP_zero : ∀ P, R.boundaryIntegral (recipEtaEulerApprox P) = 0 :=
  fun P => recipEulerApprox_rect_integral_eq_zero P R hR_lo hR_hi
-- 5. Pass to limit
-- R.boundaryIntegral (1/etaRect) = lim R.boundaryIntegral (recipEtaEulerApprox P) = 0
```

---

## Task 7: Prove `rect_integral_inv_sub_eq` (lines 770–772)

```lean
lemma rect_integral_inv_sub_eq (R : Rect) (w : ℂ) (hw : w ∈ R.openInt) :
    R.boundaryIntegral (fun z => (z - w)⁻¹) = 2 * ↑Real.pi * I
```

**Mathematical content**: The contour integral of `(z-w)⁻¹` around a
rectangle containing `w` in its interior equals `2πi`.

**Proof approach**: Direct computation of the four edge integrals.

`R.boundaryIntegral (fun z ↦ (z-w)⁻¹)`
`= ∫_bottom - ∫_top + I·∫_right - I·∫_left`

Each edge integral is of the form `∫ (a + t·I - w)⁻¹ dt` which
evaluates to `Complex.log` differences. The four contributions sum
to `2πi` (the winding number of a rectangle around an interior point is 1).

**Alternative approach**: Use `rect_cauchy_integral_formula` with `f = 1`:
```lean
have := rect_cauchy_integral_formula R (fun z => 1) w hw
  (differentiableOn_const _)
-- gives R.boundaryIntegral (fun z => (z-w)⁻¹ * 1) = 2πi * 1
simpa using this
```
But this is circular since `rect_cauchy_integral_formula` itself uses
`rect_integral_inv_sub_eq`.

**Best approach**: Compute the integrals explicitly.

Bottom edge: `∫_{x_lo}^{x_hi} (x + y_lo·I - w)⁻¹ dx`
= `Complex.log (x_hi + y_lo·I - w) - Complex.log (x_lo + y_lo·I - w)`

Similarly for other edges. The four `Complex.log` differences form
a cycle around `w`, picking up `2πi` from the branch cut crossing.

**Key Mathlib lemmas**:
- `intervalIntegral.integral_inv_sub` or compute via antiderivative `Complex.log`
- `Complex.log_sub_log` with argument tracking
- `Complex.exp_two_pi_mul_I` (= 1) to verify the winding

**Practical note**: This is one of the more computationally intensive
proofs. An alternative is to prove it for a specific rectangle first
(centered at origin) and then use affine invariance.

---

## Task 8 (Minor): Prove `right_sub_integral_vanishes` (line 1249)

```lean
lemma right_sub_integral_vanishes (x_f y_i y_f : ℝ)
    (hxf : 1 < x_f) (hy : y_i < y_f) :
    ∀ᶠ n in atTop,
    (⟨1, x_f, y_i, y_f, hxf, hy⟩ : Rect)
      .boundaryIntegral (recipZetaApproxRect n) = 0
```

**Mathematical content**: The boundary integral of
`recipZetaApproxRect n = (1-2^{1-s}) / η_n(s)` over the right
sub-rectangle `[1, x_f] × [y_i, y_f]` vanishes for large `n`.

**Proof**: For `Re ≥ 1`, `η_n(s)` converges uniformly to `η(s) ≠ 0`
(since `ζ(s) ≠ 0` for `Re ≥ 1` and `etaFactRect ≠ 0` away from
`s = 1`). For large `n`, `η_n ≠ 0` on the rectangle, so
`recipZetaApproxRect n` is analytic, and the boundary integral vanishes
by `rect_cauchy`.

**Status**: Low priority — this is a supporting lemma for the
contour-analysis section, not needed for the main RH proof.

---

## Summary: Dependency Graph

```
Task 1 (norm_exp_sub_one_le_two_norm) ─── trivial via Mathlib
     │
Task 4 (etaPartialRect uniform conv) ─── EASY: adapt bohr_cahen Abel summation
     │  from Legacy.lean
     │
Task 5 (etaPartialRect on closure) ─── uses Task 4
     │
Task 2 (zetaEulerProd_tendstoUniformlyOn_rect)
     │  uses: Task 1, axioms primeZetaTail_uniform_small,
     │        higherPrimeSum_uniform_small, eulerProd_zeta_exp_connection
     │
Task 3 (etaEulerApprox_tendstoUniformlyOn_rect)
     │  uses: Task 0 (h_cont fix), Task 2
     │
Task 7 (rect_integral_inv_sub_eq) ─── independent, winding number = 2πi
     │
Task 6 (recipEta_rect_contour_integral_eq_zero)
     │  uses: Task 3, recipEulerApprox_rect_integral_eq_zero (already proved)
     │
Task 8 (right_sub_integral_vanishes) ─── minor, independent
     │
     └── All feed into etaRect_ne_zero_critical_strip → RH
```

---

## Priority Order for the Lean LLM

2. **Task 1** — Trivial Mathlib application (2 lines)
3. **Task 4** — Easy: adapt Abel summation from `bohr_cahen_algebraic_tail_bound` (~40 lines)
4. **Task 5** — Easy: uses Task 4 (~10 lines)
5. **Task 2** — Core Euler product convergence (uses axioms, ~40 lines)
6. **Task 3** — Eta convergence from Euler convergence (~25 lines)
7. **Task 7** — Rectangle winding number (~50-80 lines, hardest computation)
8. **Task 6** — Cauchy integral limit argument (~60 lines)
9. **Task 8** — Minor supporting lemma (low priority)

**Estimated total**: ~250-300 lines of Lean proof code across all tasks.

---

## Available Axioms (already in file)

| Axiom | Statement |
|-------|-----------|
| `primeZetaTail_uniform_small` | `‖Σ_{p>P} p^{-z}‖ < ε` uniformly on compact K ⊂ {Re ≥ 1/2+α} |
| `higherPrimeSum_uniform_small` | `‖higherPrimeSum P z‖ < ε` uniformly on compact K ⊂ {Re ≥ 1/2+α} |
| `eulerProd_zeta_exp_connection` | `zetaEulerProd P s = ζ(s) · exp(-tail - higher)` for Re > 1/2 |

## Available Proved Lemmas (in Legacy.lean, importable)

| Lemma | Statement |
|-------|-----------|
| `bohr_cahen_algebraic_tail_bound` | Abel summation by parts giving `‖Σ_{n=m}^N a_n/n^s‖ ≤ C·m^(σ₀-σ)` — **proved**, ~100 lines. Adapt for Task 4. |
| `uniform_cauchy_m_P` | Uniform Cauchy index from tail bound — **proved** |
| `zeta_no_zeros_right_half_plane` | `ζ(s)=0 ∧ Re>1/2 → False` — **proved** |

## Available Mathlib Lemmas (verified)

| Lemma | Signature |
|-------|-----------|
| `Complex.norm_exp_sub_one_le` | `‖x‖ ≤ 1 → ‖exp x - 1‖ ≤ 2‖x‖` |
| `ContinuousOn.const_cpow` | `ContinuousOn f s → b≠0 → ContinuousOn (b^f) s` |
| `Metric.tendstoUniformlyOn_iff` | `↔ ∀ ε>0, ∀ᶠ n, ∀ x∈s, dist (f x)(F n x) < ε` |
| `Filter.eventually_atTop` | `(∀ᶠ x in atTop, p x) ↔ ∃ a, ∀ b≥a, p b` |
| `TendstoUniformlyOn.mul` | uniform conv × uniform conv → uniform conv of product |

## Key Definitions (in file)

```lean
def etaFactRect (s : ℂ) := 1 - (2:ℂ)^(1-s)
def etaRect (s : ℂ) := (1 - (2:ℂ)^(1-s)) * riemannZeta s
def zetaEulerProd (P : ℕ) (s : ℂ) := ∏ p ∈ (Icc 2 P).filter Nat.Prime, (1 - (p:ℂ)^(-s))⁻¹
def etaEulerApprox (P : ℕ) (s : ℂ) := etaFactRect s * zetaEulerProd P s
def higherPrimeSum (P : ℕ) (s : ℂ) := ∑' p, if Prime p ∧ p>P then ∑' k, if k≥2 then p^(-k·s)/k else 0 else 0
```
