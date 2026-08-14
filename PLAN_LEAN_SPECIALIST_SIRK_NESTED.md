# Plan for the LLM–Lean 4 Specialist: The Hashimoto SIRK Approximation Orders Nest

Execution plan for an LLM–Lean-4-specialist agent. The goal is to **formalize the
claim that the SIRK approximation orders nest**: the order-`n+1` Hashimoto SIRK
approximation refines the order-`n` one — the finer uncertainty band is contained
in the coarser band, and the coarser approximant is the projection of the finer
one onto the order-`n` Krylov subspace.

This is a property of the **generic** SIRK machinery of `ChapterH1`–`H7` (the
Krylov–Hashimoto dimensional reduction). It constrains the Navier–Stokes
truncations of `PLAN_LEAN_SPECIALIST_NS_FLOW.md`, but it constrains any other
SIRK evolution equally; it is **not** Navier-Stokes-specific. Every statement is
finite-dimensional linear algebra over the decidable skeleton (Solovay–Mehler–
Kopperman: inner products over the infinite substrate collapse to finite head
integrals), so the whole part is **fully decidable** in that sense — no Crouzeix,
no infinite spectrum, no `EXTERNAL` hypothesis.

All new theorems must remain `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).

## Status

This plan is new. All ingredients except one compatibility lemma are already
proved:

- **Subspace nesting.** `krylovSpan_mono` (`BookProof/ChapterH5.lean:64`):
  `m ≤ n → krylovSpan H v m ≤ krylovSpan H v n`.
- **Monotone bound.** `sirk_error_bound_antitone` (`ChapterH6.lean:70`):
  `sirkBound` is non-increasing in the Krylov dimension; `sirk_error_decay_exponential`
  (`ChapterH6.lean:57`) and `sirk_error_tendsto_zero` (`ChapterH6.lean:85`) give
  the collapse to zero.
- **The Book discussion is already in place.** `Book/FreeField.lean` §"Dimensional
  Reduction" now carries the nested-orders paragraph and `#check`s the existing
  H5/H6/H7 proofs.

The missing piece is the **projection/block compatibility lemma** (item 2 below),
which is what turns "the subspaces nest" into "the *approximants* nest".

---

## 1. Mandatory commands (do not skip)

```bash
export PATH="/home/leo/.elan/bin:$PATH"
cd /home/leo/Projects/timepiece

lake build               # default targets: BookProof + Book + Singularity
./patches/build-book.sh  # ALWAYS the wrapper: patches → build → render → postprocess + asserts
```

Verify candidate Mathlib names first: `lake env lean --stdin <<< '#check <name>'`.

**Invariants that must hold after any change:**
- `grep -rn "sorry" BookProof/ Singularity/` shows only the two intentional
  `UnusedRoute/SchoenfeldPRA.lean:163,178` sorries (and the quarantined
  `UnusedRoute/Legacy.lean`, `UnusedRoute/RcpEuler.lean`).
- `grep -rn "^axiom" BookProof/` is empty.
- No `BookProof/` file imports `PnpProof`, `UnusedRoute`, or `UsedRoute`.
- Lines ≤ 100 chars, no trailing whitespace, no `sorry`/`admit` in committed code.

---

## 2. Honest scoping (read this first)

**What is proved.** For the nested Krylov bases `Vₙ : Fin n → E`,
`Vₙ₊₁ : Fin (n+1) → E` with `Vₙ i = Vₙ₊₁ (Fin.castSucc i)`, the compressions
`Bₙ = compress Vₙ X`, `Bₙ₊₁ = compress Vₙ₊₁ X` of any bounded operator `X`, and the
reduced-generator bound `sirkBound`:

> (a) the Krylov subspaces nest: `Kry n ⊆ Kry (n+1)`;
> (b) the order-`n` reduced generator is the top-left `n×n` block of the
>     order-`n+1` reduced generator (`sirk_compression_block`);
> (c) the order-`n` approximant is the order-`n+1` approximant projected back
>     into `Kry n` (`sirk_band_refinement`, `sirk_approx_projection`);
> (d) the error bands nest as sets: `[0, sirkBound(n+1)] ⊆ [0, sirkBound(n)]`
>     (`sirk_band_contained`), and the tower `sirk_nested_orders` assembles (a)+(d)
>     for all `n`.

Items (a), (d) are already proved; (b) is new (the missing compatibility lemma);
(c) follows from (b).

**What is NOT claimed (and why).** The numerical **width** of the bands — the
actual error inequality
`‖φ_k(A)v − Vₘ ψ(HₘKₘ⁻¹) Vₘ† v‖ ≤ sirkBound m` — is conditional on Crouzeix's
inequality, which enters only as the named `EXTERNAL` hypothesis
(`sirk_error_bound_decay`, `ChapterH4.lean:200`). The nesting (a)–(d) holds
whether or not Crouzeix is ever proved; only the *location of the true value
inside* the nested bands needs it. Do **not** claim the infinite-dimensional
limit or the numerical convergence rate.

---

## 3. New module and placement

Create **`BookProof/ChapterH8.lean`** (namespace `BookProof.ChapterH8`), and
register it in `BookProof.lean` immediately after the `ChapterH7` import
(`BookProof.lean:334`):

```lean
import BookProof.ChapterH8
```

The module imports `ChapterH4` (for `compress`, `compress_pow`,
`compress_transfer`, `compress_inv_transfer`), `ChapterH5` (for `krylovSpan`,
`krylovSpan_mono`), and `ChapterH6` (for `sirkBound`,
`sirk_error_bound_antitone`).

Work items in dependency order.

### Part 1 — subspace nesting (reuse)

**1.1** `sirk_krylov_tower : ∀ n, krylovSpan H v n ≤ krylovSpan H v (n+1)` —
the tower form of `krylovSpan_mono` (`ChapterH5.lean:64`). One line.

### Part 2 — the block compatibility lemma (NEW)

**2.1** `sirk_compression_block : ∀ i j : Fin n,
Bₙ i j = Bₙ₊₁ (Fin.castSucc i) (Fin.castSucc j)`
— the order-`n` reduced matrix is the leading `n×n` submatrix of the order-`n+1`
one. Proof shape: unfold `compress` (`ChapterH4.lean:84`), expand the inner
products as matrix entries, use orthonormality of `Vₙ₊₁` and the nesting
`Vₙ i = Vₙ₊₁ (Fin.castSucc i)`.

Equivalent matrix form: `reduceGenerator (n+1) … X` is `Matrix.fromBlocks Bₙ b c d`
with `b, c, d` the new row/column blocks. State whichever elaborates cleanly;
the block identity is the load-bearing form.

### Part 3 — the projection-refinement theorem (NEW, headline)

**3.1** `sirk_band_refinement : Vₙ (Vₙ† (r(Bₙ₊₁) v)) = r(Bₙ) v`
for `v ∈ Kry n` (i.e. `Vₙ (Vₙ† v) = v`) and `r` any polynomial/rational function
of the reduced generator.

**3.2** `sirk_approx_projection : ∀ v,
Vₙ (Vₙ† (Vₙ₊₁ (r(Bₙ₊₁) (Vₙ₊₁† v)))) = Vₙ (r(Bₙ) (Vₙ† v))`
— the order-`n` approximant equals the order-`n+1` approximant projected back
into `Kry n`, on the whole space.

Proof shape: for polynomials reduce to `sirk_compression_block` plus induction on
the power (reuse `compress_pow`/`compress_transfer`, `ChapterH4.lean:104/122`);
for rational functions use the resolvent transfer `compress_inv_transfer`
(`ChapterH4.lean:138`). This is the exact statement that "the order-`n+1`
uncertainty band, restricted to the order-`n` data, is the order-`n` band".

### Part 4 — the monotone band inequality (mostly reuse)

**4.1** `sirk_band_contained :
Set.Icc 0 (sirkBound C Dmin h nv (n+1)) ⊆ Set.Icc 0 (sirkBound C Dmin h nv n)`
with `0 ≤ C, Dmin, nv, h` — `sirk_error_bound_antitone` (`ChapterH6.lean:70`)
restated as a set inclusion.

**4.2** Reuse `sirk_error_decay_exponential` (`ChapterH6.lean:57`) /
`sirk_error_tendsto_zero` (`ChapterH6.lean:85`) to record that the nested band
family collapses to `{0}`.

### Part 5 — the tower (the "and so on")

**5.1** `sirk_nested_orders : ∀ n : ℕ,
krylovSpan H v n ≤ krylovSpan H v (n+1)
∧ (Set.Icc 0 (sirkBound C Dmin h nv (n+1)) ⊆ Set.Icc 0 (sirkBound C Dmin h nv n))`
— the whole nested family as a single statement over the skeleton.

### Part 6 — correspondence (prose + record)

**6.1** Module docstring mapping each theorem to its source: `ChapterH5.lean`
(Krylov span), `ChapterH6.lean` (bound antitone/decay), `ChapterH4.lean`
(compression transfer), and to the Book paragraph in `Book/FreeField.lean`
§"Dimensional Reduction".

**6.2** Record in the docstring the exact boundary: the nesting is
finite-dimensional and decidable; the numerical band width (Crouzeix) is the
`EXTERNAL` analytic input, never an axiom.

---

## 4. Style and conventions

1. Plain `namespace BookProof.ChapterH8` (no `section ProbabilisticRegularization`).
2. Before `linarith` after `set`, `dsimp only [α]` first (AGENTS.md rule 1).
3. Verify Mathlib identifiers: `lake env lean --stdin <<< '#check Fin.castSucc'`,
   `'#check Matrix.fromBlocks'`, `'#check Matrix.submatrix'`,
   `'#check BookProof.ChapterH4.compress'`, `'#check BookProof.ChapterH4.compress_transfer'`.
4. Lines ≤ 100 chars; no trailing whitespace; no extra alignment spaces.
5. Prefer term-mode proofs for direct lemma applications (AGENTS.md rule 6).

---

## 5. Definition of done

```bash
# 1. Builds green, no in-scope warnings
lake build
# 2. Book still builds through the wrapper (invariants asserted inside)
./patches/build-book.sh
# 3. Sorry/axiom audit
grep -rn "sorry" BookProof/ Singularity/ | grep -v UnusedRoute   # only the 2 intentional
grep -rn "^axiom" BookProof/                                      # empty
# 4. Registration + citation
grep -n "ChapterH8" BookProof.lean                                # import present
grep -n "sirk_nested_orders" Book/FreeField.lean                  # #check present
# 5. Headline theorems exist and are sorry-free
lake env lean --stdin <<< '#check BookProof.ChapterH8.sirk_nested_orders'
lake env lean --stdin <<< '#check BookProof.ChapterH8.sirk_band_refinement'
lake env lean --stdin <<< '#check BookProof.ChapterH8.sirk_approx_projection'
lake env lean --stdin <<< '#check BookProof.ChapterH8.sirk_compression_block'
```

All headline theorems `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).

---

## 6. Verification gate against the numerics

The nesting is a statement about the SIRK machinery used by the unfer solvers. The
numerical shadow is the flow-completeness/unitarity tests of the generic solver
(any model, not NS-specific):

```bash
cd /home/leo/Projects/unfer
cargo test -p fock_sirk        # SIRK solve, unitarity, norm preservation
```

(No change to `nested_fock_algebra`/`prob_kernel` is expected: this part is pure
Lean linear algebra, not a model change.)
