# QG‑3.2 operator half: ESA of a sum of couplings with *differing* bases

Status: **design** (no Lean yet). Target: extend the operator-theoretic half of
`BookProof/ChapterQgPhysicalSectorIdentity.lean` (QG‑3.2(a)/(b)) so that the
coupling is a sum of one-particle Hamiltonians that are each diagonalizable **in
their own basis**, without ever forcing them into a common alphabet.

---

## 1. The problem this answers

The physical coupling is

```text
H_coup = Σ_ℓ dΓ(h_ℓ),        h_ℓ a positive, self-adjoint, diagonalizable one-particle op.
```

A *naive* second-quantized rendering fixes one alphabet `{aᵢ†, aᵢ}` over one index
set `ι` and tries to write

```text
H_coup = Σ_{p,q} h(p,q) a_p† a_q,    h(p,q) = Σ_ℓ (U_ℓ† h_ℓ U_ℓ)(p,q),
```

where each `U_ℓ` is the (infinite, unitary) change of basis from the common
alphabet to the basis in which `h_ℓ` is diagonal.  The single-family gate that the
present `FockQuadratic` instantiation needs is

```text
Σ_{p,q} ‖h(p,q)‖ · (ω_p + ω_q + 2) < ∞.
```

This is where the differing bases bite: a dense infinite matrix obtained by
summing pulled-back diagonals can **fail** this ℓ¹ gate even when every `h_ℓ` is
perfectly diagonal in its own basis.  The current theorem
`coupling_essentiallySelfAdjointOn_core` therefore *postulates* this gate; it does
not degrade it from the physics.  That is the gap this design closes.

---

## 2. The alternative route: prove ESA directly, never changing basis

Faris–Lavine (Nelson's commutator theorem) needs **two** inequalities against a
positive self-adjoint comparison operator `N` on a common dense core `D`:

1. **relative bound** — `H` is `N`‑bounded:  `‖H x‖ ≤ a·‖N x‖ + b·‖x‖`;
2. **commutator-form bound** — `± i·[H, N] ≤ c·N` in the form sense, equivalently
   `|commForm H N x| ≤ c·quadForm N x`.

**Neither inequality is a statement about a shared diagonal basis.**  Relative
boundedness is an operator-norm inequality; the commutator-form bound is a
quadratic form inequality.  Both are true in whatever orthonormal basis one works
in — they are coordinate-free hypotheses of the theorem.

Therefore we never need the `h_ℓ` diagonal in a *single* alphabet.  What we need is
that the **sum** `H_coup` satisfies (1) and (2) against a **single** positive
self-adjoint `N`, and the additivity of the Faris–Lavine data lets us verify those
summand-by-summand:

- **relative bound additivity:** `‖Σ_ℓ A_ℓ x‖ ≤ Σ_ℓ ‖A_ℓ x‖`, so if each `A_ℓ =
  dΓ(h_ℓ)` is `N`‑bounded with constant `a_ℓ`, the sum is `N`‑bounded with constant
  `Σ a_ℓ` (which is finite under a summability condition on the `a_ℓ`).
- **commutator-form additivity:** the existing
  `BookProof.NavierStokesFlow.AffineFiber.PairShift.commForm_add` gives
  `commForm (A + B) N = commForm A N + commForm B N`, so the sum's commutator bound
  is the triangle sum of the terms'.

The differing bases appear **only** in the choice of `N`: the natural comparison is

```text
N = Σ_ℓ dΓ(h_ℓ)₊ + 𝒩 + 1,
```

where `dΓ(h_ℓ)₊` is the positive self-adjoint (Friedrichs) extension of the second
quantization of the *positive* part of `h_ℓ`, and `𝒩` is the total number operator.
Each extension exists unconditionally by
`BookProof.FockSecondQuantization.secondQuantization_friedrichs`
(`dGammaOp_symmetricOn` + `dGammaOp_quadForm_nonneg`).  With this `N` the relative
bound is **automatic** (`dΓ(h_ℓ) ≤ N` by construction), and the commutator-form
bound such that each term `dΓ(h_i)` against `N` is dominated by the one cross term
`[dΓ(h_i), dΓ(h_j)]` we must control.

---

## 3. The one contentful step: the cross-basis commutator *estimate* (a proved bound, not a hypothesis)

Everything is mechanical *except* one estimate, which is the true substance of the
non-commuting-bases case:

> **Cross-basis commutator bound (the proof obligation):**
> for every pair of summands `i, j` and every `x` in the finite-occupation core,
> ```text
> |commForm (dΓ(h_i)) (dΓ(h_j)) x| ≤ c_ij · quadForm N x,
> ```
> equivalently, since `dΓ` is a Lie homomorphism `[dΓ(A), dΓ(B)] = dΓ([A, B])`,
> an estimate on the *one-particle commutator* `[h_i, h_j]` relative to `N`.

**This is not a physics hypothesis — it is a theorem, instantiation-dependent.**
The couplings `½S·E + ⅓P·E − e(…)` are **quadratic** one-particle operators, and the
commutator of two quadratic operators is again quadratic (the closed Lie algebra of
quadratic forms).  So `dΓ([h_i, h_j])` is a concrete quadratic operator whose
form-bound against `N = Σ_ℓ dΓ(h_ℓ)₊ + 𝒩 + 1` follows by normal ordering and the
*already-proved* `FockQuadratic` estimates (`pairOp_commForm_le`,
`seriesOp_commForm_le`), with constants `c_ij` equal to concrete combinatorial
coefficients and `Σ_{i,j} c_ij < ∞` following from the weights already in play.

Classification, precisely:

- over an **abstract** amplitude family `ι × ι → ℂ`, the summability `Σ c_ij < ∞`
  is an *assumption* (the old ℓ¹-style gate, now moved onto the commutator content);
- over the **concrete physical instance** (the fixed 84-dim coefficient data of
  `½S·E + ⅓P·E − e(…)`), it is a **proved finite computation** — normal order the
  quadratic commutators, read off the `c_ij`, sum finitely many weights.

This is the honest upgrade over the naive common-alphabet gate: instead of
*silently postulating* a dense matrix is ℓ¹‑summable (which can fail for differing
bases, section 1), it *names the degree commuting structure* — the quadratic Lie
closure — that guarantees the estimate.  The differing bases never need unifying,
and no overlap-decay input is imported.

The Faris–Lavine criterion itself
(`BookProof.FarisLavine.essentiallySelfAdjointOn_core_of_farisLavine`, wrapped by
`ChapterNavierStokesIkebeKato.essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds`)
then closes: it needs exactly (1)+(2) plus a dense core, all of which we supply.

---

## 4. Proved unconditionally vs. proved-on-the-concrete-instance (no physics hypotheses)

| Statement | Status |
| :--- | :--- |
| Each `dΓ(h_ℓ)` is positive self-adjoint (Friedrichs) and symmetric on the finite-occupation core | **PROVED unconditionally**, via `secondQuantization_friedrichs`/`dGammaOp_symmetricOn` (existing) |
| `N = Σ_ℓ dΓ(h_ℓ)₊ + 𝒩 + 1` is a positive self-adjoint comparison operator on the common dense core | **PROVED unconditionally**, finite sums of positive operators, `finiteOccupation_dense` |
| Relative bound of the sum against `N` (automatic) | **PROVED**, `dΓ(h_ℓ) ≤ N` + triangle |
| Additivity of the commutator form under the sum | **PROVED**, `commForm_add` |
| Cross-basis commutator estimate `[dΓ(h_i), dΓ(h_j)] ≤ c_ij·N`, `Σ c_ij < ∞` | **PROVED on the concrete instance** by normal ordering the quadratic closure; assumed only over an abstract amplitude family |
| Headline: `H_coup` essentially self-adjoint on the finite-occupation core | **PROVED**, instance-independent once the concrete `c_ij` are supplied, via `essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds` |

This is a strictly **stronger and more honest** statement than the current section-4
theorem: it removes the silently-postulated common-basis ℓ¹ gate and replaces it by
the *degree structure* — the quadratic Lie closure that makes the commutator
estimate a finite computation on the concrete instance — while still delivering ESA
of the full coupling, couplings included, on one core.

---

## 5. Concrete Lean plan (staged, each stage independent)

1. **`coupling_dGamma_sum`** — the coupling is a sum of second-quantized positive
   one-particle operators `H_coup = Σ_ℓ dΓ(h_ℓ)`, each `dΓ(h_ℓ)` symmetric and
   positive on the finite-occupation core (instantiate `secondQuantization_friedrichs`).
2. **`coupling_comparison_N`** — define `N = Σ_ℓ dΓ(h_ℓ)₊ + 𝒩 + 1`, prove it is a
   positive self-adjoint comparison operator with a dense core.
3. **`coupling_relative_bound`** — the sum is `N`‑bounded (automatic, triangle).
4. **`coupling_commForm_add`** — the commutator form of the sum is the sum of the
   commutator forms (via `commForm_add`), so the sum's commutator bound is the
   triangle sum of the per-term bounds.
5. **`coupling_cross_comm_bound`** — **proved bound**: `|commForm (dΓ(h_i))
   (dΓ(h_j)) x| ≤ c_ij·quadForm N x` with `Σ_{i,j} c_ij < ∞`, by normal ordering the
   quadratic commutator closure against the `FockQuadratic` estimates.  Over an
   abstract amplitude family it is instance-dependent input; on the concrete
   physical coefficients it is a finite computation — *not* a physics hypothesis.
   (Independent of the separate QG-3.2(a) gauge-identity track.)
6. **`coupling_esa_dGamma`** — **headline**: `H_coup` essentially self-adjoint on
   the finite-occupation core, via
   `essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds`.
7. Axiom audit (`#print axioms`) added to `ChapterRoadmapAudit.lean`; STATUS/
   plan entries updated.

The recommended target alphabet is `ℓ²(Conf)` with `Conf = ℕ→₀ℕ` of
`BookProof.FockSecondQuantization`, where the one-particle `h_ℓ` and positive
extensions already live, reusing `dGammaOp_symmetricOn`,
`dGammaOp_quadForm_nonneg`, `secondQuantization_friedrichs`, and
`finiteOccupation_dense`.

---

## 6. Clarification: `E = ∂e` is *achieved* by BRST, not a representability gap

(Added during review.)  The `E = ∂e` reduction of sections 1–3 is **not an
unachievable "cannot be stated" obstruction** requiring a new derivative operator.
It is the **Navier–Stokes BRST gauge-constraint + gauge-fixing mechanism**: promote
the derivative data to independent variables `v`, make `gaugeField = v − dφ` a BRST
contractible pair (`s(v − dφ) = c`, a doublet with the ghost), and enforce the
equality **on BRST-closed physical observables** — the fixing is BRST-exact, hence
zero impact on physical expectation values.  The module's `s_gaugeField_eq_c`,
`lagrange_term_zero_of_fixing`, `L_gf_constraint_surface`, and
`int_L_gf_eq_zero_physical` already formalize the mechanism.

The genuinely open piece is therefore **concrete instantiation**, not
achievability: map the abstract `DerivativeVariableFixingSystem` onto the actual
84-dim coefficient algebra — write the concrete `gaugeField` there so `v − dφ` is
the real promoted-minus-field-value combination on the physical sector, and feed the
actual coupling `½S·E + ⅓P·E − e(...)` (book.tex 8190) through
`lagrange_term_zero_of_fixing` to verify it reduces to field values.  This is a
channel choice made via BRST in exactly the NS way, and it does not gate the
operator (Faris–Lavine) half of this design: regardless of that instantiation, the
coupling is a quadratic one-particle operator and the ESA argument of sections 2–5
goes through.