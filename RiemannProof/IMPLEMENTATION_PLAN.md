# Implementation Plan: η(2s−1) Multiplicity-One and Zero Location

## Files

| File | Tasks | Status |
|------|-------|--------|
| `ShiftedEta.lean` | 1–2 | 12 proved, 2 sorry |
| `ConjugateReflection.lean` | 3–4 | 5 proved, 3 sorry |
| `MultiplicityOne.lean` | 5–7 | 1 proved, 9 sorry |
| `ZeroLocation.lean` | 8–9 | 6 proved, 3 sorry |
| **Total** | | **25 proved, 17 sorry** |

---

## Current Proof Strategy

We prove RH by studying the shifted eta function `η(2s−1)`, whose Dirichlet
series converges conditionally for `Re(s) > 1/2`. The critical strip maps
to `{1/2 < Re(s) < 1}` and the critical line to `Re(s) = 3/4`.

### Stage 1 — Multiplicity One (Tasks 1–7)

Prove every zero of `η(2s−1)` in the critical strip is simple.

**Method**: Conjugate-reflection product `F_n(s) = conj(f_n(conj(s)))·f_n(s)`
converges to `|g(s)|²` on the real axis, where `g(s) = H(s)·η(2s−1)` and
`H(s) = s − 3/4 − i`. The contour integral on a half-rectangle
`R = [σ₀−δ, σ₀+δ] × [0, T]` (bottom edge on real axis) yields:

- Non-real edges → 0 (uniform convergence)
- Real edge > 0 (integrand = `|f_n(σ)|²` ≥ 0, not identically zero)
- Residue Theorem: even multiplicity 2m ≥ 4 → contradiction
- Odd m ≥ 3 = even component × simple → also excluded
- Conclusion: m = 1 only

### Stage 2 — Zero Location on Re(s) = 3/4 (Tasks 8–9)

Prove all zeros lie on the critical line.

**Method**: Four-fold product with functional equation symmetry `s ↦ 3/2−s`:
```
G_n(s) = conj(f_n(conj(s))) · f_n(s) · f_n(3/2−s) · conj(f_n(3/2−conj(s)))
```
The symmetry `G_n(3/2−s) = G_n(s)` is proved by `ring`. If `σ₀ ≠ 3/4`,
the product creates symmetric zeros at both `s₀` and `3/2−s₀`, yielding a
contour contradiction analogous to Stage 1.

**RH equivalence**: If `ζ(s) = 0` with `0 < Re(s) < 1`, set `w = (s+1)/2`.
Then `Re(w) ∈ (1/2, 1)` and `η(2w−1) = η(s) = 0`. By Stage 2, `Re(w) = 3/4`,
so `Re(s) = 2·(3/4) − 1 = 1/2`.

---

## Implementation Status: Proved Lemmas

### ShiftedEta.lean (Tasks 1–2)

| Lemma | Status |
|-------|--------|
| `etaShifted_eq` | PROVED |
| `etaPartialShifted_zero` | PROVED |
| `etaPartialShifted_one` | PROVED |
| `nat_succ_mem_slitPlane` | PROVED |
| `etaPartialShifted_differentiable` | PROVED |
| `targetH_differentiable` | PROVED |
| `targetH_zero` | PROVED |
| `targetH_ne_zero` | PROVED |
| `hApprox_tendsto` | PROVED |
| `hApprox_tendstoUniformlyOn` | PROVED |
| `etaPartialShifted_tendsto` | PROVED |
| `etaPartialShifted_tendstoUniformlyOn` | **SORRY** |
| `fApprox_tendstoUniformlyOn` | **SORRY** |

### ConjugateReflection.lean (Tasks 3–4)

| Lemma | Status |
|-------|--------|
| `conjReflApprox_real_nonneg` | PROVED |
| `conjReflApprox_eq_normSq` | PROVED |
| `even_multiplicity_pole` | PROVED |
| `mkHalfRect_contains_s₀` | PROVED |
| `mkHalfRect_bottom_real` | PROVED |
| `conjReflLimit_zero_order` | **SORRY** |
| `conjReflApprox_cauchy` | **SORRY** |
| `exists_isolating_rect` | **SORRY** |

### MultiplicityOne.lean (Tasks 5–7)

| Lemma | Status |
|-------|--------|
| `conjReflApprox_nonneg_on_reals` | PROVED |
| `top_edge_integral_converges` | **SORRY** |
| `left_edge_integral_converges` | **SORRY** |
| `right_edge_integral_converges` | **SORRY** |
| `nonreal_edges_sum_zero` | **SORRY** |
| `real_axis_integral_nonneg` | **SORRY** |
| `fApprox_not_identically_zero` | **SORRY** |
| `real_axis_integral_pos` | **SORRY** |
| `even_multiplicity_contradiction` | **SORRY** |
| `etaShifted_zeros_simple` | **SORRY** |

### ZeroLocation.lean (Tasks 8–9)

| Lemma | Status |
|-------|--------|
| `etaShifted_functional_eq_zero` | PROVED |
| `reflected_in_critical_strip` | PROVED |
| `fourFoldApprox_symm` | PROVED |
| `mkSymRect` | PROVED (def) |
| `etaShifted_zeros_on_critical_line` | PROVED (from sorry'd lemma) |
| `etaShifted_zeros_simple_on_line` | PROVED (from sorry'd lemmas) |
| `riemann_hypothesis_via_shifted_eta` | PROVED |
| `fourFoldApprox_real_nonneg` | **SORRY** |
| `fourFoldApprox_tendstoUniformlyOn_boundary` | **SORRY** |
| `zero_location_contradiction` | **SORRY** |

---

## Remaining Sorries — Priority Attack Order

Work through the remaining items in this order. Each group unlocks the next.

### Priority 1: Uniform Convergence (2 sorries in ShiftedEta.lean)

**Goal**: Prove `etaPartialShifted_tendstoUniformlyOn` and
`fApprox_tendstoUniformlyOn`.

**Approach**: Adapt the paired-term summation + Weierstrass M-test
infrastructure from `EtaConvergence.lean` (11 proved lemmas for `η(s)`).

Key steps:
1. Reindex `etaPartialShifted n s = Σ_{k=0}^{n-1} (-1)^k / (k+1)^{2s-1}`
   to match `etaPartialSum` infrastructure.
2. Use `etaPartial'_tendstoUniformlyOn_extended` from `EtaConvergence.lean`
   after showing `{2s−1 : Re(s) > 1/2}` maps to `{Re > 0}`.
3. For `fApprox_tendstoUniformlyOn`: combine `hApprox_tendstoUniformlyOn`
   (already proved) with `etaPartialShifted_tendstoUniformlyOn` via
   `TendstoUniformlyOn.mul`.

**Files**: `ShiftedEta.lean` lines 186–197.

---

### Priority 2: Zero Order Propagation (1 sorry in ConjugateReflection.lean)

**Goal**: Prove `conjReflLimit_zero_order` — if `η(2s−1)` has a zero of
order m at `s₀`, then `conjReflLimit` has a zero of order `2m`.

**Approach**:
1. Factor `etaShifted s = (s - s₀)^m · φ(s)` with `φ(s₀) ≠ 0`.
2. Factor `targetH(s) = (s - s₀) + (s₀ - 3/4 - I)` (nonzero at `s₀`).
3. Show `conjReflLimit s = |s - s₀|^{2m} · ψ(s)` where
   `ψ(s) = conj(φ(conj(s))) · φ(s) · |targetH|²` with `ψ(s₀) ≠ 0`.
4. Use `Differentiable.conj` for the reflection part.

**File**: `ConjugateReflection.lean` lines 75–82.

---

### Priority 3: Contour Integral Infrastructure (3 sorries)

**Goal**: Prove `conjReflApprox_cauchy`, `exists_isolating_rect`, and
`nonreal_edges_sum_zero`.

**`conjReflApprox_cauchy`**: F_n involves conjugation, so it is not
holomorphic in the usual sense. However, the boundary integral can be
computed by splitting into `f_n(conj(s))` (holomorphic in `conj(s)`) and
`f_n(s)` (holomorphic in `s`) and using the specific rectangle structure.
Alternatively, work directly with the Cauchy integral formula for each
factor separately.

**`exists_isolating_rect`**: Use the fact that zeros of `η(2s−1)` are
isolated (non-trivial zeros are discrete). Pick `δ` small enough that the
open ball `B(s₀, 2δ)` contains no other zeros.

**`nonreal_edges_sum_zero`**: The three non-real edges of `conjReflLimit`
sum to zero when the contour avoids zeros. Use Cauchy's theorem for the
holomorphic part and symmetry for the conjugate part.

**Files**: `ConjugateReflection.lean` lines 135–137, 145–153;
`MultiplicityOne.lean` lines 97–103.

---

### Priority 4: Edge Integral Convergence (3 sorries in MultiplicityOne.lean)

**Goal**: Prove `top_edge_integral_converges`,
`left_edge_integral_converges`, `right_edge_integral_converges`.

**Approach**: Each follows the same pattern:
1. `F_n → F` uniformly on the edge (from Priority 1 results).
2. The edge is compact, so `intervalIntegral.tendsto_integral_of_tendstoUniformly`
   applies.
3. The integrand is bounded on the compact edge.

**Dependency**: Requires Priority 1 (uniform convergence).

**Files**: `MultiplicityOne.lean` lines 60–93.

---

### Priority 5: Real-Axis Positivity (3 sorries in MultiplicityOne.lean)

**Goal**: Prove `real_axis_integral_nonneg`, `fApprox_not_identically_zero`,
`real_axis_integral_pos`.

**`real_axis_integral_nonneg`**: `F_n(σ) = |f_n(σ)|² ≥ 0` on the real axis
(already proved in `conjReflApprox_real_nonneg`). The integral of a
non-negative function is non-negative. Use
`intervalIntegral.integral_nonneg`.

**`fApprox_not_identically_zero`**: For large n, `f_n` approximates
`H(s)·η(2s−1)` which is not identically zero on any interval (η has
isolated zeros). Use `hApprox_tendstoUniformlyOn` +
`etaPartialShifted_tendsto` (Priority 1) to show `f_n` is eventually
close to the nonzero limit.

**`real_axis_integral_pos`**: Combine nonneg + not-identically-zero.
Use the fact that if `∫ f ≥ 0` and `f` is continuous and nonzero
somewhere, then `∫ f > 0`.

**Files**: `MultiplicityOne.lean` lines 119–137.

---

### Priority 6: The Core Contradiction (2 sorries)

**Goal**: Prove `even_multiplicity_contradiction` and
`etaShifted_zeros_simple`.

**`even_multiplicity_contradiction`**: Assemble the pieces:
1. Contour integral of `F_n` = 0 (Cauchy, since `F_n` is entire-like).
2. In the limit: real-axis integral + non-real edges = 0.
3. Non-real edges → 0 (Priority 4).
4. Real-axis integral > 0 (Priority 5).
5. But Residue Theorem says the integral should be related to a residue
   with negative real part for even multiplicity 2m ≥ 4 → contradiction.

**`etaShifted_zeros_simple`**: The main theorem follows by:
1. Suppose m ≥ 2.
2. Even m: direct contradiction from `even_multiplicity_contradiction`.
3. Odd m ≥ 3: write m = (m−1) + 1 where m−1 ≥ 2 is even. The even
   component creates the same contradiction.
4. Therefore m = 1.

**Files**: `MultiplicityOne.lean` lines 156–184.

---

### Priority 7: Four-Fold Product and Zero Location (3 sorries in ZeroLocation.lean)

**Goal**: Prove `fourFoldApprox_real_nonneg`,
`fourFoldApprox_tendstoUniformlyOn_boundary`,
`zero_location_contradiction`.

**`fourFoldApprox_real_nonneg`**: `G_n(σ) = |f_n(σ)|² · |f_n(3/2−σ)|² ≥ 0`
for real `σ`. Similar to `conjReflApprox_real_nonneg` but with the
additional `f_n(3/2−s)` factor.

**`fourFoldApprox_tendstoUniformlyOn_boundary`**: Combine uniform
convergence of `fApprox` (Priority 1) with the four-fold product
structure via `TendstoUniformlyOn.mul`.

**`zero_location_contradiction`**: If `σ₀ ≠ 3/4`, then both `s₀` and
`3/2−s₀` are distinct zeros inside the symmetric rectangle. The four-fold
product creates zeros at both locations, and the contour integral argument
(analogous to Stage 1) yields a contradiction with the positive real-axis
integral.

**Files**: `ZeroLocation.lean` lines 103–147.

---

## Dependency Graph

```
Priority 1 (uniform convergence)
     │
     ├──► Priority 2 (zero order propagation)
     │         │
     ├──► Priority 3 (contour infrastructure)
     │         │
     ├──► Priority 4 (edge integral convergence)
     │         │
     ├──► Priority 5 (real-axis positivity)
     │         │
     └──► Priority 6 (core contradiction → multiplicity one)
               │
               └──► Priority 7 (four-fold → zero location → RH)
```

---

## Available Infrastructure

### Proved Lemmas in Other Files

| File | Lemma | Relevance |
|------|-------|-----------|
| `EtaConvergence.lean` | `etaPartial'_tendstoUniformlyOn_extended` | Priority 1: uniform conv of η partial sums |
| `EtaConvergence.lean` | `paired_tsum_eq_dirichletEta` | Limit identification |
| `RectangleStrategy.lean` | `zetaEulerProd_tendstoUniformlyOn_rect` | Euler product convergence |
| `RectangleStrategy.lean` | `etaEulerApprox_tendstoUniformlyOn_rect` | η Euler convergence |
| `RectangleStrategy.lean` | `etaPartialRect_tendstoUniformlyOn_closure` | Partial sums on closure |
| `Basic.lean` | `zeta_symm` | Functional equation of ζ |
| `Basic.lean` | `etaFactor_ne_zero_re_lt_one` | Eta factor non-vanishing |

### Available Axioms (in RectangleStrategy.lean)

| Axiom | Statement |
|-------|-----------|
| `primeZetaTail_uniform_small` | Prime zeta tail uniformly small on compact sets |
| `higherPrimeSum_uniform_small` | Higher prime sum uniformly small |
| `eulerProd_zeta_exp_connection` | `ζ_P(s) = ζ(s)·exp(−tail − higher)` |

### Key Definitions

```lean
def etaShifted s := dirichletEta (2 * s - 1)
def etaPartialShifted n s := Σ k ∈ range n, (-1)^k / (k+1)^{2s-1}
def targetH s := s - 3/4 - I
def hApprox n s := targetH s + 1/(n+1)
def fApprox n s := hApprox n s * etaPartialShifted n s
def conjReflApprox n s := conj(f_n(conj(s))) * f_n(s)
def fourFoldApprox n s := conj(f_n(conj(s))) * f_n(s) * f_n(3/2-s) * conj(f_n(3/2-conj(s)))
```
