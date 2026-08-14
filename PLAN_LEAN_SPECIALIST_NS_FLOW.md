# Plan for the LLM–Lean 4 Specialist: The Navier–Stokes Hamiltonian Has a Complete Flow

Execution plan for an LLM–Lean-4-specialist agent. The goal is to **formalize the
claim that the Navier–Stokes Hamiltonian generates a complete flow (no finite-time
singularities)** in the finite-truncation setting, in a way that is `sorry`-free and
`axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`), and to record
explicitly what is *not* being claimed (the infinite-dimensional essential
self-adjointness of `book.tex` §4199-4208 remains a research target).

Every new theorem must remain `sorry`-free and `axiom`-free.

## Status

This plan is new. The supporting work is already in place and verified:

- **Numerics (unfer, gravity-parallel).** `nested_fock_algebra` now asserts the
  three structural facts the plan builds on, mirroring the existing
  `test_gravity_hamiltonian_terms` pattern: `test_navier_stokes_hermitian`
  (H = H† on sample states), `test_navier_stokes_low_degree` (every term ≤ 3
  ladder operators — the "polynomial of low degree" hypothesis), and
  `test_navier_stokes_brst_nilpotent` (Ω² = 0). `fock_sirk` asserts
  `navier_stokes_flow_complete_and_unitary` (h_proj Hermitian; `e^{-iHt}`
  norm-preserving for a sweep of times; coefficients finite — no blow-up on the
  truncation). `prob_kernel` verifies the divergence-constraint resolution
  symbolically in Cadabra2 (`VerifySubstitution` op + the
  `verify_navier_stokes_divergence_constraint_resolution` test).
- **Existing Lean assets.** The BRST ghost algebra is already formalized
  (`BookProof/ChapterNavierStokes.lean`: `ghost_CAR`, `ghostCreate_sq`, ...;
  `BookProof/ChapterGhostField.lean`: `brst_charge_nilpotent`); the finite
  unitary group machinery is in `BookProof/ChapterContinuityUnitary.lean`
  (`momentum_hermitian`, `exp_smul_I_unitary`, `continuityUnitary_unitary`,
  `unitary_preserves_normSq`); the graded superalgebra unifying CCR/CAR is in
  `BookProof/ChapterSuperBracket.lean`; the honest ESA/flow certificate layer is
  in `Singularity/Esa.lean` and `Singularity/Hamiltonian.lean`
  (`weyl_symmetrization_self_adjoint`, `nelson_essential_self_adjoint`).

---

## 1. Mandatory commands (do not skip)

```bash
export PATH="/home/leo/.elan/bin:$PATH"
cd /home/leo/Projects/timepiece

lake build               # default targets: BookProof + Book + Singularity
lake build RandomMap
./patches/build-book.sh  # ALWAYS the wrapper: patches → build → render → postprocess + asserts
```

Verify candidate Mathlib names first: `lake env lean --stdin <<< '#check <name>'`.

**Invariants that must hold after any change:**
- `grep -rn "sorry" BookProof/ Singularity/ RandomMap/` shows only the two
  intentional `UnusedRoute/SchoenfeldPRA.lean:163,178` sorries (and the
  quarantined `UnusedRoute/Legacy.lean`, `UnusedRoute/RcpEuler.lean`).
- `grep -rn "^axiom" BookProof/` is empty.
- No `BookProof/` file imports `PnpProof`, `UnusedRoute`, or `UsedRoute`.
- Lines ≤ 100 chars, no trailing whitespace, no `sorry`/`admit` in committed code.

---

## 2. Honest scoping (read this first)

**What is proved.** Let `H_N` be the Navier–Stokes Hamiltonian **restricted to a
finite truncation** (finitely many field modes `u_k, u_{k,j}, u_{k,jj}` and
bounded occupation numbers). Then:

> (a) `H_N` is Hermitian (`H_Nᴴ = H_N`);
> (b) `e^{-itH_N}` is a **one-parameter unitary group** (the flow is complete on
>     the truncation): `U(0) = 1`, `U(s)U(t) = U(s+t)`, `U(t)ᴴ = U(t)⁻¹`;
> (c) the flow is **norm-preserving**: `‖ψ(t)‖ = ‖ψ(0)‖`, and for any finite time
>     `t` every coefficient of `U(t)ψ` is finite — **no finite-time singularity
>     on the truncation**.

This is the numerical shadow of `book.tex` §4199-4208 ("it can be proved to be
essentially self-adjoint ... the solution ... exists and it is unique"), and it is
**genuinely provable** because a finite Hermitian matrix is self-adjoint.

**What is NOT claimed (and why).** The `book.tex` proof route uses a positive
auxiliary operator `H²` (Corollary 1.1 of `cmpux2f1103859517`). The project's own
ODE chapter demonstrates that **the same style of argument fails** for `ẋ = x²`:
there the polynomial `H = x²p̂ − i x̂` has degree 3 yet the flow `x₀/(1−tx₀)` is
incomplete, so `H` is *not* essentially self-adjoint on `L²(ℝ)` — the deficiency
argument requires the flow to be complete, and for NS the continuum/infinite-mode
flow completeness is the open Clay regularity problem. Therefore:

- **Do NOT claim** essential self-adjointness of the *untruncated* continuum
  operator `H = ∫ a†(πⁱ(u_j u_{i,j} − ν u_{i,jj}) + h.c.)a`.
- **Do NOT claim** global existence/uniqueness of the NS equations (Contention D5
  in `CONSOLIDATED_PLAN.md` — deliberate scope cut).
- The finite-truncation results (a)–(c) are the honest, defensible core; the
  infinite-dimensional extension is recorded as a research target in §7.

**How the numerics and the Lean proof line up.**

| Numerical test (unfer) | Lean theorem (this plan) | Meaning |
| :-- | :-- | :-- |
| `test_navier_stokes_hermitian` | `nsHamiltonian_hermitian` | H = H† (Weyl symmetrization), so `e^{-iHt}` is unitary |
| `test_navier_stokes_low_degree` | `nsHamiltonian_isPolynomial` (arity ≤ 3) | well-defined polynomial/symmetric operator on the dense domain — symmetry, not self-adjointness |
| `test_navier_stokes_brst_nilpotent` | `nsBrst_nilpotent` | Ω² = 0 (first-class constraint) |
| `navier_stokes_flow_complete_and_unitary` | `nsFlow_unitaryGroup` / `nsFlow_noBlowup` | complete flow, no singularity on the truncation |
| `verify_navier_stokes_divergence_constraint_resolution` | `nsDivergenceConstraint_resolution` | `u_{3,3}=u_{1,1}+u_{2,2}` solves `∂_j u_j = 0` (book.tex §4191-4197) |

---

## 3. New module and placement

Create **`BookProof/ChapterNavierStokesFlow.lean`** (namespace
`BookProof.NavierStokesFlow`), register it in `BookProof.lean` with

```lean
import BookProof.ChapterNavierStokesFlow
```

and, if a `Book/` chapter should `#check` the headline theorems, add the `#check`
block to `Book/FreeField.lean` (the chapter that carries the free-field half of
the NS mathematics) or `Book/YangMillsQuantization.lean` (Contention D5's
recommended pointer). Import `Mathlib`, plus the supporting modules:

```lean
import Mathlib
import BookProof.ChapterNavierStokes
import BookProof.ChapterGhostField
import BookProof.ChapterSuperBracket
import BookProof.ChapterContinuityUnitary
```

Work items in dependency order.

### Part A — The finite truncation is a finite Hermitian matrix

**A.1** `nsFieldModes : Fin 15` — the 15 field modes
(`u_k` k=0..2, `u_{k,j}` 3..11, `u_{k,jj}` 12..14). Define the NS interaction
operator on the truncation as a finite matrix `nsInteraction : Matrix (Fin N) (Fin N) ℂ`
mirroring `continuityHamiltonian` in `ChapterContinuityUnitary.lean`.

**A.2** `nsHamiltonian : Matrix (Fin N) (Fin N) ℂ` — the truncated
`H_N = Σ_i (π_i A_i + A_i π_i)` with `A_i = Σ_j u_j u_{i,j} − ν u_{12+i}`,
following the anti-commutator construction of `navier_stokes_hamiltonian` in
`nested_fock_algebra/src/models.rs:72`.

**A.3** `nsHamiltonian_hermitian : nsHamiltonianᴴ = nsHamiltonian` —
prove `π_i` is Hermitian (exactly `momentum_hermitian` in
`ChapterContinuityUnitary.lean`), `A_i` is Hermitian (each factor `u_j`, `u_{i,j}`
is a symmetric matrix; `ν ∈ ℝ`), and the anti-commutator of two Hermitian
matrices is Hermitian. *Hint:* reuse the `Matrix.conjTranspose_apply` + `ext i j`
+ `fin_cases` pattern already used throughout `ChapterNavierStokes.lean`.

**A.4** `nsHamiltonian_isPolynomial` — every entry of `nsHamiltonian` is a
polynomial of **degree ≤ 3** in the ladder operators; state it as: for each
`i j`, the `(i,j)`-entry is `∑ c · a†_{k₁} a_{k₂} a_{k₃}` with at most 3 factors
(`∃ terms : Finset ...`, each term a product of ≤ 3 ladder ops). This is the
formal statement of the "low degree in the fields" hypothesis (`book.tex` §4199).
**Role: symmetry, not self-adjointness.** Low degree shows `H_N` is a
well-defined *polynomial* operator (hence symmetric, defined on the dense
finite-particle domain, no renormalization). It does **not** by itself imply
self-adjointness — the correct criterion is flow completeness (Nelson), which is
exactly why Part B works on the *finite matrix* (where self-adjointness holds
automatically) rather than inferring it from the degree bound.

### Part B — Complete flow on the truncation (no singularities)

Reuse the already-proved finite machinery of `ChapterContinuityUnitary.lean`
(`exp_smul_I_unitary`, `continuityUnitary_unitary`, `continuityUnitary_add`,
`unitary_preserves_normSq`) — the same lemmas that power the `continuityUnitary`
package. The truncation matrix is finite, so `Matrix.exp` exists and is a matrix
unitary.

**B.1** `nsFlowUnitary (t : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
NormedSpace.exp (((t : ℂ) * Complex.I) • nsHamiltonian)` — matching the
`continuityUnitary` convention (`ChapterContinuityUnitary.lean:141-143`).

**B.2** `nsFlow_unitary (t) : (nsFlowUnitary t)ᴴ * nsFlowUnitary t = 1` —
unitarity of each `e^{-itH_N}`; a direct instance of `exp_smul_I_unitary`
(`ChapterContinuityUnitary.lean:124`) applied to `nsHamiltonian_hermitian`.

**B.3** `nsFlow_group (s t) : nsFlowUnitary (s + t) = nsFlowUnitary s * nsFlowUnitary t` —
the one-parameter group law, i.e. the flow is **complete** (defined for every
real time). Proof shape: `NormedSpace.exp_add`/`Matrix.exp_add_of_commute`
with `Commute.neg_left`-style commuting factors, exactly as in
`continuityUnitary_add` (`ChapterContinuityUnitary.lean:154`). The `(i t H)`
sign convention makes both orderings commute trivially.

**B.4** `nsFlow_zero : nsFlowUnitary 0 = 1` — `NormedSpace.exp_zero`
(as `continuityUnitary_zero`, `ChapterContinuityUnitary.lean:150`).

**B.5** `nsFlow_norm_preserving (t) (ψ : Fin N → ℂ) :
  ‖nsFlowUnitary t • ψ‖ = ‖ψ‖` — via `unitary_preserves_normSq`
(already in `ChapterContinuityUnitary.lean:198`).

**B.6** `nsFlow_noBlowup (t) (ψ : Fin N → ℂ) (k : Fin N) :
  (nsFlowUnitary t • ψ) k ≠ ∞` — trivially true since `ℂ` has no infinity;
  state it as `(nsFlowUnitary t • ψ) k : ℂ` well-typed / finite, i.e. the
  evolved coefficients are finite complex numbers for every finite `t`.

**B.7** `nsFlow_groupOnEvolved (t₁ t₂) : nsFlowUnitary t₁ • (nsFlowUnitary t₂ • ψ) =
  nsFlowUnitary (t₁ + t₂) • ψ` — the complete-flow statement acting on states
  (what the numerical `time_evolve`/`reconstruct` loop realizes).

### Part C — BRST constraint (mostly reuse)

**C.1** `nsBrst_nilpotent : Ω * Ω = 0` where
`Ω = Σ_j (u_{j,j} : Matrix (Fin N) (Fin N) ℂ) * (ghostAnnih j)` is the truncated
BRST charge. Reuse `brst_charge_nilpotent` (`ChapterGhostField.lean:124`) — the
nilpotency reduces to the ghost CAR/nilpotency already proved — plus the bosonic
fields commuting with each other.

**C.2** `nsDivergenceConstraint_resolution :
  (U11 + U22 + U33) with U33 := -(U11 + U22) = 0` — the formal statement of the
  symbolic `VerifySubstitution` test / book.tex §4191-4197: the divergence
  constraint `∂_j u_j = u_{1,1}+u_{2,2}+u_{3,3}` is solved by the replacement
  `u_{3,3} = u_{1,1}+u_{2,2}`. (Statement form: for `u11 u22 u33 : ℝ`,
  `h : u33 = -(u11+u22)`, conclude `u11 + u22 + u33 = 0` — `linarith`.)

**C.3** (optional) `nsBrst_hermitian : Ωᴴ = Ω` — the BRST charge is Hermitian
(same proof shape as `brst_charge_nilpotent`'s surroundings), tying C.1 to the
physical "project on ker Ω" construction of `fock_sirk`'s `brst.rs`.

### Part D — The book.tex correspondence (prose + record)

**D.1** Module docstring mapping each theorem to its `book.tex` line
(`chapter at book.tex:3699`, NS section `book.tex:4133-4216`, Hamiltonian
`book.tex:4184-4189`, constraint `book.tex:4191-4197`, self-adjointness claim
`book.tex:4199-4208`, existence/uniqueness `book.tex:4210-4216`), and to the
matching numerical test in unfer. Follow the honesty-flag style of
`Book/OdeSingularity.lean` and `BookProof/ChapterOdeComplexification.lean`
(`ae_no_real_singular_time`).

**D.2** Record in the docstring the exact boundary: the continuum operator's
essential self-adjointness and the NS existence/uniqueness claim are **not**
claimed here; the finite truncation is the honest provable core, and the
infinite-dimensional extension is the §7 research target.

The nesting of the finite SIRK approximation orders (the "n+1 band is contained
in the n band" statement) is **not** part of this NS-flow plan: it is a property
of the generic Krylov–Hashimoto machinery, not of Navier–Stokes, and it lives in
`PLAN_LEAN_SPECIALIST_SIRK_NESTED.md` (`BookProof/ChapterH8`).

---

## 4. Style and conventions

1. `section ProbabilisticRegularization ... end ProbabilisticRegularization` is
   NOT required here (that is for the `Ω/E/Var/X` names); use a plain
   `namespace BookProof.NavierStokesFlow`.
2. Before `linarith` after `set`, `dsimp only [α]` first (AGENTS.md rule 1).
3. Verify Mathlib identifiers: `lake env lean --stdin <<< '#check NormedSpace.exp'`,
   `'#check Matrix.exp_add_of_commute'`, `'#check Matrix.exp_conjTranspose'`,
   `'#check NormedSpace.exp_zero'`, `'#check BookProof.ContinuityUnitary.exp_smul_I_unitary'`.
4. Lines ≤ 100 chars; no trailing whitespace; no extra alignment spaces.
5. Prefer term-mode proofs for direct axiom/lemma applications
   (AGENTS.md rule 6).

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
grep -n "ChapterNavierStokesFlow" BookProof.lean                  # import present
grep -n "nsFlow_unitary" Book/FreeField.lean Book/YangMillsQuantization.lean  # #check present (if cited)
# 5. Headline theorems exist and are sorry-free
lake env lean --stdin <<< '#check BookProof.NavierStokesFlow.nsFlow_unitary'
lake env lean --stdin <<< '#check BookProof.NavierStokesFlow.nsFlow_noBlowup'
lake env lean --stdin <<< '#check BookProof.NavierStokesFlow.nsBrst_nilpotent'
lake env lean --stdin <<< '#check BookProof.NavierStokesFlow.nsDivergenceConstraint_resolution'
```

All headline theorems `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).

---

## 6. Verification gate against the numerics

After the Lean wave lands, re-run the unfer side so the correspondence in §2 stays
true:

```bash
cd /home/leo/Projects/unfer
cargo test -p nested_fock_algebra navier_stokes     # Hermiticity, low degree, BRST nilpotent
cargo test -p fock_sirk navier_stokes               # flow complete + unitary, no blow-up
# symbolic (cadabra2 is in the nix devShell; see AGENTS.md)
nix develop --command cargo test -p prob_kernel --lib symbolic
```

---

## 7. Research target (record, do not attempt)

The infinite-dimensional extension — essential self-adjointness of the continuum
operator `H = ∫ a†(πⁱ(u_j u_{i,j} − ν u_{i,jj}) + h.c.)a` on
`Γ^s(L²(ℝ¹⁵×ℤ₂³)) ⊗ Γ^a(L²(ℝ¹⁵×ℤ₂³))`, and hence global existence/uniqueness of
the NS equations — is **not** a plan item. The ODE chapter's `x' = x²` example is
the standing warning that a low-degree polynomial Hamiltonian need *not* be
essentially self-adjoint when the classical flow is incomplete; the book.tex
auxiliary-operator argument is exactly the one that project's ODE chapter corrects.
Any future attempt must first construct a genuinely complete classical-flow /
analytic realization, on the pattern of the ODE chapter's `w = 1/x` resolution —
and the honest current record is `BookProof/ChapterUnboundedPosition.lean` +
`BookProof/ChapterContinuityUnitaryInfinite.lean` (the `ℓ²(ℤ)` bounded layer) plus
the Stone-theorem-in-full-generality target already recorded in
`CONSOLIDATED_PLAN.md` §9.

Distinct from this research target: the *nesting* of the finite approximation
orders is **not** a research target — it is decidable, finite-dimensional linear
algebra, and is a separate plan item (`PLAN_LEAN_SPECIALIST_SIRK_NESTED.md`,
`BookProof/ChapterH8`), a property of the generic Krylov–Hashimoto machinery
rather than of Navier–Stokes. The Crouzeix-based numerical *width* of the nested
bands remains an `EXTERNAL` analytic input; the nesting itself does not depend on
it.
