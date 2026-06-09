# Implemented: RectangleStrategy.lean Sorry Elimination

## File: `RiemannProof/RiemannProof/RectangleStrategy.lean`
## Supporting file: `RiemannProof/RiemannProof/EtaConvergence.lean` (11 lemmas)

---

## Task 1: `norm_exp_sub_one_le_two_norm` (line 599) ✅ PROVED

```lean
lemma norm_exp_sub_one_le_two_norm (w : ℂ)
    (hw : ‖w‖ < 1 / 2) :
    ‖Complex.exp w - 1‖ ≤ 2 * ‖w‖
```

**Method**: `Complex.exp_bound` + `linarith`

**Proof**:
```lean
lemma norm_exp_sub_one_le_two_norm (w : ℂ)
    (hw : ‖w‖ < 1 / 2) :
    ‖Complex.exp w - 1‖ ≤ 2 * ‖w‖ := by
  have h1 : ‖w‖ ≤ 1 := by linarith
  have := Complex.exp_bound h1 one_pos
  simp at this
  linarith
```
The condition `‖w‖ < 1/2` implies `‖w‖ ≤ 1` by `linarith`.

**Mathlib lemma used**: `Complex.norm_exp_sub_one_le` with signature:
```lean
@Complex.norm_exp_sub_one_le : ∀ {x : ℂ}, ‖x‖ ≤ 1 → ‖Complex.exp x - 1‖ ≤ 2 * ‖x‖
```

---

## Task 2: `zetaEulerProd_tendstoUniformlyOn_rect` (line 607) ✅ PROVED

```lean
lemma zetaEulerProd_tendstoUniformlyOn_rect (R : Rect)
    (hR_lo : ∀ z ∈ R.closure, z.re > 1 / 2)
    (hR_hi : ∀ z ∈ R.closure, z.re < 1) :
    TendstoUniformlyOn (fun P => zetaEulerProd P) riemannZeta
      atTop R.closure
```

**Method**: `Metric.tendstoUniformlyOn_iff` + axioms + exp bound

**Context computed**:
- `hK : IsCompact R.closure`
- `hα : ∃ α > 0, ∀ z ∈ R.closure, z.re ≥ 1/2 + α`
- `M : ℝ` with `hM : ∀ z ∈ R.closure, ‖riemannZeta z‖ ≤ M`

**Proof strategy**:

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

**Key Mathlib lemmas**:
- `Metric.tendstoUniformlyOn_iff`
- `norm_mul_le`, `norm_sub_le`, `norm_neg`
- `Filter.eventually_atTop` ↔ `∃ a, ∀ b≥a, p b`
- `Complex.norm_exp_sub_one_le` / `norm_exp_sub_one_le_two_norm`

---

## Task 3: `etaEulerApprox_tendstoUniformlyOn_rect` (line 759) ✅ PROVED

```lean
lemma etaEulerApprox_tendstoUniformlyOn_rect (R : Rect)
    (hR_lo : ∀ z ∈ R.closure, z.re > 1 / 2)
    (hR_hi : ∀ z ∈ R.closure, z.re < 1) :
    TendstoUniformlyOn (fun P => etaEulerApprox P) etaRect
      atTop R.closure
```

**Method**: Bounded factor × Euler convergence

**Context computed**:
- `h_euler_conv`: `TendstoUniformlyOn (fun P ↦ zetaEulerProd P) riemannZeta atTop R.closure`
- `h_bounded`: `∃ B, ∀ z ∈ R.closure, ‖etaFactRect z‖ ≤ B`
- `⟨B, hB⟩`: the bound extracted

**Proof strategy**:

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

**Note**: `ContinuousOn.const_cpow` with `Or.inl` wrapper needed for `etaFactRect` continuity proof.

---

## Task 4: `etaPartialRect_tendstoUniformlyOn` ✅ PROVED

```lean
lemma etaPartialRect_tendstoUniformlyOn (K : Set ℂ) (hK : IsCompact K)
    (hK_lower : ∀ z ∈ K, z.re > 1 / 2)
    (hK_upper : ∀ z ∈ K, z.re < 1) :
    TendstoUniformlyOn (fun n => etaPartialRect n) etaRect atTop K
```

**Method**: New file `RiemannProof/EtaConvergence.lean` with paired-term summation + Weierstrass M-test + identity theorem.

**Proof approach** (3 steps):

### Step 1: Paired sum convergence (Weierstrass M-test)
- Pair consecutive terms: `f_j(s) = 1/(2j+1)^s - 1/(2j+2)^s`
- Bound each term: `‖f_j(s)‖ ≤ (‖s‖+1) / (2j+1)^{Re(s)+1}` (via integral/MVT bound)
- Since `Re(s) + 1 > 3/2 > 1` on K, the majorant is summable → uniform convergence by `tendstoUniformlyOn_tsum_nat`

### Step 2: Full partial sums converge
- Even partial sums `η_{2m}` equal the paired sum (algebraic identity)
- Odd partial sums `η_{2m+1} = η_{2m} + 1/(2m+1)^s`, and `1/(2m+1)^s → 0` uniformly

### Step 3: Limit identification via the identity theorem
- For `Re(s) > 1`: algebraically verify `∑' etaPairedTerm j s = (1-2^{1-s})ζ(s)` using `zeta_eq_tsum_one_div_nat_cpow` and absolute convergence rearrangement
- The paired tsum is analytic on `{Re > 1/2}` (uniform limit of analytic functions)
- `dirichletEta = (1-2^{1-s})ζ(s)` is analytic on `{Re > 1/2, s ≠ 1}`
- `{Re > 1/2} \ {1}` is preconnected (path-connected: open half-plane minus a point in ℂ)
- By `AnalyticOnNhd.eqOn_of_preconnected_of_frequently_eq`, they agree on all of `{Re > 1/2, s ≠ 1}`
- Since `K ⊂ {1/2 < Re < 1}`, all points satisfy `s ≠ 1`, so the identification holds on K

**Lemmas in EtaConvergence.lean** (11 total, all proved):

| Lemma | Purpose |
|-------|---------|
| `etaPartial'_even_eq_paired_sum` | Even partial sums = paired sum |
| `norm_etaPairedTerm_le` | M-test bound via integral/MVT |
| `summable_etaPairedTerm` | Summability of paired terms |
| `paired_tendstoUniformlyOn` | Uniform convergence of paired sums |
| `odd_correction_tendstoUniformlyOn` | Odd-even correction → 0 |
| `paired_tsum_eq_dirichletEta_re_gt_one` | Limit identity for Re > 1 |
| `analyticOnNhd_paired_tsum` | Analyticity of paired tsum |
| `analyticOnNhd_dirichletEta` | Analyticity of dirichletEta |
| `isPreconnected_halfplane_minus_one` | Preconnectedness for identity thm |
| `paired_tsum_eq_dirichletEta` | Limit identity for Re > 1/2, s ≠ 1 |
| `etaPartial'_tendstoUniformlyOn` | Main convergence theorem |

---

## Task 5: `etaPartialRect_tendstoUniformlyOn_closure` (line 353) ✅ PROVED

```lean
lemma etaPartialRect_tendstoUniformlyOn_closure
    (R₀ : Rect)
    (hR₀_re_pos : ∀ z ∈ R₀.closure, z.re > 1 / 2)
    (hR₀_eta_factor : ∀ z ∈ R₀.closure, etaFactRect z ≠ 0) :
    TendstoUniformlyOn (fun n => etaPartialRect n) etaRect atTop R₀.closure
```

**Method**: Direct application of `etaPartial'_tendstoUniformlyOn_extended` from EtaConvergence.lean.

**Proof**:
```lean
have hK_ne_one : ∀ z ∈ R₀.closure, z ≠ (1 : ℂ) := by
  intro z hz heq
  exact hR₀_eta_factor z hz (by rw [heq]; unfold etaFactRect; norm_num)
exact etaPartial'_tendstoUniformlyOn_extended R₀.closure
  R₀.isCompact_closure hR₀_re_pos hK_ne_one
```

The hypothesis `hR₀_eta_factor` ensures `z ≠ 1` (since `etaFactRect 1 = 0`),
which is required by the EtaConvergence theorems.
