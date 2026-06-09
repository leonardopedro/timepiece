# Implementation Plan: η(2s−1) Multiplicity and Zero Location via Contour Contradiction

## Overview

We study the function **η(2s−1)**, where η(s) = (1 − 2^{1−s})ζ(s) is the
Dirichlet eta function. Its Dirichlet series

    η(2s−1) = Σ_{k=1}^∞ (−1)^{k−1} / k^{2s−1}

converges **conditionally for Re(s) > 1/2** (since the classical η(σ)
converges for σ > 0, and 2·Re(s) − 1 > 0 ⟺ Re(s) > 1/2).

The proof has two main stages:

1. **Multiplicity-one theorem**: Every zero of η(2s−1) in the critical
   strip has multiplicity exactly 1.
2. **Zero location theorem**: All such zeros lie on the vertical line
   Re(s) = 3/4 (the shifted critical line for η(2s−1)).

Both stages use the same core technique: construct a product of
approximants and their conjugate-reflections, then derive a contradiction
between the **Residue Theorem** (which gives a signed integral) and
**uniform convergence via Bagchi universality** (which forces the
integral to vanish or have the wrong sign).

---

## Stage 1: Zeros Have Multiplicity One

### Setup and y=1 scaling

Suppose η(2s−1) has a zero of multiplicity m ≥ 1 at s₀ = σ₀ + it₀
with 1/2 < σ₀ < 1 and t₀ > 0.

**We scale the y-coordinate so that the eta zero is at y = 1**, i.e.,
we set s₀ = σ₀ + i. This normalization places the zero at a fixed
imaginary height, simplifying the contour geometry. All subsequent
constructions (rectangle, approximants) are relative to this scaling.

### The contour: enclosing exactly one zero

Choose a **rectangle R** with vertices at:

    R = [σ₀ − δ, σ₀ + δ] × [0, T]

where:
- The **bottom edge lies on the real axis** (y = 0).
- T > 1 so that s₀ = σ₀ + i is in the interior.
- δ > 0 is small enough that **s₀ is the only zero of η(2s−1) inside R**
  (possible since zeros are isolated).

The contour must guarantee that **exactly one zero** is enclosed. This
is essential because we are testing whether that single zero could have
multiplicity m ≥ 2, which would create a pole of even multiplicity 2m
in the conjugate-reflection product.

### Construction of the approximants f_n = h_n · η_n

The approximant f_n is factored into two components:

    f_n(s) = h_n(s) · η_n(s)

where:

- **η_n(s)**: partial Dirichlet sums of η(2s−1), i.e.,
  η_n(s) = Σ_{k=1}^n (−1)^{k−1}/k^{2s−1}, which converge to η(2s−1)
  conditionally for Re(s) > 1/2.

- **h_n(s)**: a correcting factor that approximates the function

      H(s) = s − 3/4 − i

  uniformly **on the contour ∂R** (the boundary of the rectangle).

**Key property**: Since 1/η has simple poles at the zeros of η in the
critical strip, the function (s − 3/4 − i) can be uniformly approximated
by h_n **on the contour ∂R** via Bagchi universality. We do NOT require
H(s) to be pole-free inside R — we only need uniform approximation on
the boundary.

### The conjugate-reflection product

Define:

    F_n(s) = f_n*(2s*−1) · f_n(2s−1)

where * denotes complex conjugation of both coefficients and argument.
On the real axis (s = σ ∈ ℝ), this becomes:

    F_n(σ) = |f_n(2σ−1)|²  ≥ 0

If η(2s−1) has a zero of multiplicity m at s₀ = σ₀ + i, the product
F_n converges (on ∂R) to a function whose behavior near s₀ is:

    ((s − 3/4 − i)(s − 3/4 + i))^{2m} = |s − s₀|^{4m} · (angular factor)

The zero of multiplicity m in η(2s−1) becomes a pole of multiplicity
**2m** (always **even**) in 1/F_n.

### Why excluding even multiplicity suffices

The conjugate-reflection product F_n = f_n* · f_n always creates poles
of **even multiplicity 2m** in 1/F_n. This is the crucial structural
observation:

- If m = 1 (simple zero): 2m = 2 — **even** multiplicity pole.
- If m = 2 (double zero): 2m = 4 — **even** multiplicity pole.
- If m = 3 (triple zero): the pole of order 6 = pole of order 4 × simple
  pole. The even-multiplicity component (order 4) is what we exclude.
- In general, for odd m ≥ 3: 2m = (2m−2) + 2, i.e., the non-simple
  pole decomposes as (even multiplicity 2m−2) × (simple pole).

**Logical chain**:
1. We prove that poles of **even multiplicity** cannot exist (via the
   contour integral contradiction below).
2. Since any non-simple pole with odd multiplicity m ≥ 3 is the product
   of an even-multiplicity pole and a simple pole, excluding even
   multiplicities excludes them too.
3. Since 1/η does have simple poles in the critical strip (at the zeros
   of η), the only surviving possibility is m = 1.
4. **Conclusion**: All zeros of η(2s−1) in the critical strip are
   **simple** (multiplicity 1).

### The contradiction (excluding even multiplicity)

Consider the Cauchy integral:

    ∮_{∂R} F_n(s) ds

**On the three non-real edges** (top at y = T, left at x = σ₀−δ,
right at x = σ₀+δ):
- h_n → (s − 3/4 − i) uniformly **on ∂R** (Bagchi universality on the
  contour), so F_n converges uniformly on ∂R.
- The integrals over these three edges **tend to zero** as n → ∞,
  because F_n converges to a function that is analytic and nonzero on
  these edges (away from s₀), and the contour avoids the zero.

**On the bottom edge** (real axis, y = 0):
- F_n(σ) = |f_n(2σ−1)|² ≥ 0 (a real non-negative function).
- The integral ∫_{σ₀−δ}^{σ₀+δ} F_n(σ) dσ is **strictly positive**
  (since F_n ≥ 0 and not identically zero on a real interval).
- In the limit, this integral remains positive.

**By the Residue Theorem**:
- If η(2s−1) has a zero of multiplicity m ≥ 2 at s₀, the function
  1/F_n has a pole of **even** multiplicity 2m ≥ 4.
- The contour integral of 1/F_n around R equals 2πi times the residue,
  which for an even-multiplicity pole gives a contribution that is
  **negative** (or has a definite sign opposite to the positive
  real-axis integral).

**Contradiction**: The total integral equals the positive real-axis
integral (since the other three edges vanish), yet the Residue Theorem
requires it to be negative for even multiplicity ≥ 2. This is impossible.

**Therefore even-multiplicity poles cannot exist**, which (by the
logical chain above) implies η(2s−1) can only have zeros of
**multiplicity 1** in the critical strip.

### Key mathematical ingredients

| Component | Source |
|-----------|--------|
| y=1 scaling: s₀ = σ₀ + i | Normalization placing zero at fixed height |
| Contour encloses exactly one zero | Isolated zeros + choice of δ |
| f_n = h_n · η_n factorization | h_n corrects η_n via Bagchi universality |
| h_n → (s−3/4−i) uniformly on ∂R | Bagchi universality on the contour |
| F_n creates only **even**-multiplicity poles | Conjugate-reflection product structure |
| Even mult. excluded → all non-simple excluded | Odd m≥3 = even × simple; simple poles exist |
| Positivity on real axis | F_n(σ) = \|f_n(2σ−1)\|² ≥ 0 |
| Residue sign contradiction | Even-multiplicity pole gives negative residue |
| Edge integrals → 0 | Uniform convergence on ∂R + compactness |

---

## Stage 2: Zeros Lie on Re(s) = 3/4

### Setup

Having proved that all zeros of η(2s−1) in the critical strip have
multiplicity 1, we now prove they must lie on the line Re(s) = 3/4.

The key observation: η(s) satisfies the functional equation
η(s) = η(1−s) (up to a known factor), which for η(2s−1) implies a
symmetry under s ↦ 1−s*. A zero at s₀ = σ₀ + i implies a zero at
1 − σ₀ + i (the reflected point, using the y=1 scaling).

### The four-fold product

Define:

    G_n(s) = g_n*(s*) · g_n(s) · g_n(−s) · g_n*(−s*)

where g_n(s) approximates η(2s−1). This product has the symmetry:

    G_n(s) = G_n(1−s)  (functional equation symmetry)
    G_n(s) = G_n*(s*)  (conjugate symmetry)

If η(2s−1) has a zero at s₀ = σ₀ + i (with σ₀ ≠ 3/4), then by
the functional equation it also has a zero at 1−σ₀ + i. The product
G_n(s) converges to a function with zeros at:

    s₀, s₀̄, 1−s₀, 1−s₀̄  (four distinct points if σ₀ ≠ 3/4)

### The contour

Choose a rectangle R symmetric about Re(s) = 3/4:

    R = [3/4 − δ, 3/4 + δ] × [0, T]

with the bottom edge on the real axis.

### The contradiction

Consider ∮_{∂R} G_n(s) ds:

- **Real axis** (bottom edge): G_n(σ) ≥ 0 (product of conjugate pairs),
  so the integral is positive.
- **Other edges**: Uniform convergence (Bagchi) forces these integrals
  to zero.
- **Residue Theorem**: If σ₀ ≠ 3/4, there are zeros at both σ₀ and
  1−σ₀ inside R. The symmetry of the zero configuration forces the
  residue to have a sign **opposite** to the positive real-axis integral.

**Contradiction** unless σ₀ = 1 − σ₀, i.e., **σ₀ = 3/4**.

### Why Re(s) = 3/4 (not 1/2)

The function η(2s−1) shifts the critical strip: the classical critical
strip 0 < Re(σ) < 1 for η(σ) maps to 1/2 < Re(s) < 1 for s = (σ+1)/2.
The critical line Re(σ) = 1/2 maps to Re(s) = (1/2+1)/2 = **3/4**.

---

## Task Breakdown

### Task 1: Define η(2s−1), η_n, h_n, and f_n = h_n · η_n in Lean

**Goal**: Define:
- `etaShifted (s : ℂ) := dirichletEta (2*s - 1)` — the shifted eta
- `etaPartialShifted (n : ℕ) (s : ℂ)` — partial Dirichlet sums η_n(s)
- `targetH (s : ℂ) := s - 3/4 - I` — the target for h_n (pole at y=1)
- `hApprox (n : ℕ) (s : ℂ)` — h_n(s) approximating (s − 3/4 − i) on ∂R
- `fApprox (n : ℕ) (s : ℂ) := hApprox n s * etaPartialShifted n s` — the full approximant

**Lean sketch**:
```lean
noncomputable def etaShifted (s : ℂ) : ℂ :=
  dirichletEta (2 * s - 1)

-- Partial Dirichlet sums for η(2s−1)
noncomputable def etaPartialShifted (n : ℕ) (s : ℂ) : ℂ :=
  ∑ k in Finset.range n, (-1 : ℂ)^k / (k+1 : ℂ)^(2*s - 1)

-- Target function H(s) = s − 3/4 − i (pole at y=1 after scaling)
noncomputable def targetH (s : ℂ) : ℂ :=
  s - 3/4 - I

-- h_n approximates (s − 3/4 − i) on the CONTOUR ∂R
-- (universality on the boundary, not requiring pole-free inside R)

-- Full approximant: f_n = h_n · η_n
noncomputable def fApprox (n : ℕ) (s : ℂ) : ℂ :=
  hApprox n s * etaPartialShifted n s
```

**Key insight**: h_n → (s − 3/4 − i) uniformly **on ∂R** via Bagchi
universality. Since 1/η has simple poles at the zeros of η, we only
need approximation on the contour, not inside R.

**Dependencies**: `dirichletEta` from Basic.lean, `etaRect` from
RectangleStrategy.lean.

---

### Task 2: Prove h_n → (s − 3/4 − i) uniformly on the contour ∂R

**Goal**: Prove that h_n converges to (s − 3/4 − i) uniformly on the
boundary ∂R via Bagchi universality.

Since 1/η has simple poles at the zeros of η in the critical strip,
and (s − 3/4 − i) is analytic, universality allows h_n to approximate
(s − 3/4 − i) on ∂R. We do NOT need pole-free conditions inside R —
only uniform approximation on the boundary.

**Lean statement**:
```lean
lemma hApprox_tendstoUniformlyOn_boundary (R : Rect) (s₀ : ℂ)
    (hs₀ : s₀ ∈ R.openInt) (hs₀_im : s₀.im = 1)
    (h_unique : ∀ z ∈ R.closure, etaShifted z = 0 → z = s₀) :
    TendstoUniformlyOn hApprox targetH atTop R.boundary
```

### Task 2b: Prove η_n → η(2s−1) conditionally

**Goal**: Prove the partial Dirichlet sums η_n converge to η(2s−1)
conditionally for Re(s) > 1/2. This uses paired-term summation and the
alternating series test.

**Lean statement**:
```lean
lemma etaPartialShifted_tendsto (s : ℂ) (hs : s.re > 1/2) :
    Tendsto (fun n => etaPartialShifted n s) atTop (𝓝 (etaShifted s))
```

---

### Task 3: Define the conjugate-reflection product F_n

**Goal**: Define F_n(s) = f_n*(2s*−1) · f_n(2s−1) where
f_n = h_n · η_n, and prove its key properties:
- F_n(σ) = |f_n(2σ−1)|² ≥ 0 for σ ∈ ℝ
- F_n → limit uniformly on ∂R
- 1/F_n has poles of **even multiplicity 2m** at zeros of η(2s−1)

**Lean sketch**:
```lean
noncomputable def conjReflApprox (n : ℕ) (s : ℂ) : ℂ :=
  (star (fApprox n (star s))) * (fApprox n s)

lemma conjReflApprox_nonneg_real (n : ℕ) (σ : ℝ) :
    0 ≤ (conjReflApprox n σ).re ∧ (conjReflApprox n σ).im = 0
```

---

### Task 4: Rectangle contour integral setup

**Goal**: Define the rectangle R = [σ₀−δ, σ₀+δ] × [0, T] with:
- bottom edge on the real axis (y = 0)
- s₀ = σ₀ + i in the interior (y=1 scaling)
- exactly one zero of η(2s−1) inside R

Formalize the boundary integral of F_n.

**Lean sketch**:
```lean
-- Rectangle with bottom edge on real axis, scaled for y=1
def halfRect (x_lo x_hi T : ℝ) (hx : x_lo < x_hi) (hT : 1 < T) :
    Rect := ⟨x_lo, x_hi, 0, T, hx, hT⟩

lemma boundaryIntegral_conjReflApprox_decomp (R : halfRect ...) :
    R.boundaryIntegral (conjReflApprox P) =
      ∫_bottom + ∫_top + ∫_left + ∫_right
```

---

### Task 5: Prove edge integrals vanish (uniform convergence on ∂R)

**Goal**: Show that the top, left, and right edge integrals of F_n tend
to zero as n → ∞, using uniform convergence of h_n → (s − 3/4 − i)
on ∂R (Bagchi universality on the contour) and η_n → η(2s−1).

Since h_n converges uniformly on ∂R, the convergence F_n → F holds
uniformly on every edge of R, allowing us to pass the limit through
the integrals.

**Key Mathlib tools**:
- `Metric.tendstoUniformlyOn_iff` — extract uniform bounds
- `intervalIntegral.tendsto_integral_of_tendstoUniformly` — pass limit
- `IsCompact.exists_isMinOn` — lower bound on |η| on edges

---

### Task 6: Prove real-axis integral is positive

**Goal**: Show ∫_{σ₀−δ}^{σ₀+δ} F_n(σ) dσ > 0 for all n, and this
positivity is preserved in the limit.

**Approach**: F_n(σ) = |f_n(2σ−1)|² = |h_n(σ)|² · |η_n(2σ−1)|² ≥ 0.
Since h_n → H ≠ 0 on the real axis (H is pole-free) and η_n → η(2s−1)
which is nonzero on the real axis (for σ ≠ 1/2), f_n is not identically
zero on any real subinterval.

---

### Task 7: Residue theorem contradiction (even multiplicity excluded)

**Goal**: If η(2s−1) has a zero of multiplicity m ≥ 2 at s₀ = σ₀ + i,
compute the residue of 1/F_n at s₀ (a pole of even order 2m ≥ 4) and
show the contour integral must be negative, contradicting the positive
real-axis integral.

**Approach**: The even-multiplicity pole of order 2m at s₀ contributes:
- Residue involves the (2m−1)-th derivative, giving a sign that
  contradicts positivity when 2m ≥ 4 (even multiplicity).

**Then invoke the logical chain**:
- Even multiplicity excluded → odd multiplicity m ≥ 3 excluded too
  (since m ≥ 3 odd = even component × simple pole)
- Simple poles of 1/η exist → only m = 1 survives
- **All zeros of η(2s−1) are simple**

**This is the core contradiction that proves multiplicity one.**

---

### Task 8: Four-fold product G_n for zero location

**Goal**: Define G_n(s) = g_n*(s*)·g_n(s)·g_n(−s)·g_n*(−s*) and prove:
- G_n(σ) ≥ 0 for σ ∈ ℝ
- G_n has the symmetry G_n(s) = G_n(1−s)
- If zeros exist at both σ₀ and 1−σ₀ (with σ₀ ≠ 3/4), the residue
  contradicts the positive real-axis integral.

**Lean sketch**:
```lean
noncomputable def fourFoldApprox (P : ℕ) (s : ℂ) : ℂ :=
  (star (gApprox P (star s))) * (gApprox P s)
    * (gApprox P (-s)) * (star (gApprox P (-(star s))))
```

---

### Task 9: Conclude zeros on Re(s) = 3/4

**Goal**: From the four-fold contradiction, deduce that σ₀ = 1 − σ₀,
hence σ₀ = 3/4. Combined with Stage 1 (multiplicity one), this proves
that all zeros of η(2s−1) in the critical strip are simple and on
Re(s) = 3/4, which is equivalent to RH for the original η function.

---

## Dependency Graph

```
Task 1 (define etaShifted + approximants)
  │
Task 2 (uniform convergence via Bagchi)
  │
Task 3 (conjugate-reflection product F_n)
  │
  ├── Task 4 (rectangle contour setup)
  │     │
  │     ├── Task 5 (edge integrals → 0)
  │     │
  │     └── Task 6 (real-axis integral > 0)
  │
  └── Task 7 (residue contradiction → multiplicity 1)
        │  uses: Tasks 4, 5, 6
        │
Task 8 (four-fold product G_n → zero location)
  │  uses: Tasks 2, 3, 4, 5, 6 (adapted)
  │
Task 9 (conclude Re(s) = 3/4 → RH)
```

---

## Priority Order

1. **Tasks 1–3** — Definitions and convergence. These are foundational
   and mostly mechanical (adapting existing infrastructure from
   RectangleStrategy.lean to the shifted argument 2s−1).

2. **Tasks 4–6** — Contour integral machinery. Standard rectangle
   integral decomposition, edge bounds via uniform convergence, and
   real-axis positivity.

3. **Task 7** — The multiplicity-one contradiction. This is the core
   mathematical insight: residue sign vs. real-axis positivity.

4. **Tasks 8–9** — Zero location via four-fold product. Structurally
   similar to Task 7 but with the additional functional equation
   symmetry.

---

## Available Infrastructure

### From RectangleStrategy.lean (reusable):
| Lemma | Adaptation needed |
|-------|-------------------|
| `zetaEulerProd_tendstoUniformlyOn_rect` | Adapt to 2s−1 argument |
| `etaEulerApprox_tendstoUniformlyOn_rect` | Adapt to etaShifted |
| `recipEulerApprox_rect_integral_eq_zero` | Direct reuse for F_n |
| `rect_cauchy` | Direct reuse |
| `eta_zero_isolated_in_rect` | Adapt to etaShifted |

### From EtaConvergence.lean (reusable):
| Lemma | Adaptation needed |
|-------|-------------------|
| `etaPartialRect_tendstoUniformlyOn` | Adapt to 2s−1 (conditional convergence for Re > 1/2) |
| Dirichlet series partial sum bounds | Reuse with shifted argument |

### Axioms (from RectangleStrategy.lean):
| Axiom | Role |
|-------|------|
| `primeZetaTail_uniform_small` | Bagchi correction for prime zeta tail |
| `higherPrimeSum_uniform_small` | Higher prime sum absolutely convergent |
| `eulerProd_zeta_exp_connection` | ζ_P(s) = ζ(s)·exp(−tail − higher) |

### Key Mathlib tools:
| Lemma | Purpose |
|-------|---------|
| `Metric.tendstoUniformlyOn_iff` | Extract uniform convergence bounds |
| `intervalIntegral.tendsto_integral_of_tendstoUniformly` | Pass limit through integral |
| `IsCompact.exists_isMinOn` | Lower bound on compact sets |
| `Complex.hasDerivAt_log` | Antiderivative for contour integrals |
| `ContinuousOn.const_cpow` | Continuity of power functions |
