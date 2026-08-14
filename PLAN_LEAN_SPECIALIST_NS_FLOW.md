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
  infinite-dimensional extension is recorded as a research target in §7, with
  Part B providing the concrete route (the Lagrangian change of variables turns
  advection into a positive 2nd-order Laplacian, so the ESA question becomes a
  Kato–Rellich relative-boundedness argument rather than the failed auxiliary-
  operator argument of `book.tex`).

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
import BookProof.ChapterF1        -- Part A: Bargmann-Fock fieldPhi/fieldPi/ccr_mv
import BookProof.ChapterFreeFieldConstraint  -- Part A.4: constraint commutation
```

Work items in dependency order.

### Part A — The field, its derivatives as fields, and the momentum constraint

This part formalizes the book.tex construction that *treats the derivatives of a
field as fields themselves* (`book.tex` §4151-4173: the `ℝ³³` degrees of freedom
are `3` space coordinates + `3` fields `u_k` + their derivatives `u_{k,j}`,
`u_{k,jj}`). The trick is an operator-valued field that is linear in the
position operator `X`:

```
φ(X) = φ + φ_i · (X_i − x_i)
```

where `X` is the position operator of the Fock model and `x_i` is its *eigenvalue*
defined by the creation/annihilation operators (`X_i` acts as `x_i` on the Fock
states). Acting on the Fock operators the field **collapses to its point value**:

```
φ(X) = φ        (on the Fock eigenstates of X)
```

so the first-order Taylor coefficients `φ_i` *are* the derivative fields
`u_{k,j}` of the truncation — they are independent canonical degrees of freedom
with their own conjugate momenta. The **momentum constraint** is then the CCR
family of `book.tex` §4163-4170, which is exactly what makes each derivative mode
a field:

```
[u_j, π^k]          = i·δ^k_j
[u_{j,k}, π^{mn}]   = i·δ^n_j·δ^m_k
[u_{i,jk}, π^{lmn}] = i·δ^l_i·δ^m_j·δ^n_k
```

Everything here is algebraic and finite-dimensional; the Bargmann–Fock machinery
(`ChapterF1.lean`: `fieldPhi = creat + annih`, `fieldPi`, `field_ccr`, `ccr_mv`)
already proves the single-mode and multi-mode cases.

**A.1** `positionOp : ℂ[X] →ₗ[ℂ] ℂ[X]` — the position operator of the
Bargmann–Fock model, `X = (creat + annih) = fieldPhi` (`ChapterF1.lean:98`), and
its eigenvalue map `x : Fin N → ℂ` with `Xᵢ` acting as `xᵢ` on the Fock
monomials (the diagonal action on `X^k`).

**A.2** `fieldTaylor (φ φi : …) : …` — the operator-valued field
`φ(X) = φ + φ_i · (X_i − x_i)`, and the headline
`field_evaluates_to_value : φ(X) |Fock⟩ = φ |Fock⟩`: acting on the Fock
eigenstates of `X` the field collapses to its point value. Proof shape:
on an `X`-eigenstate `(X_i − x_i)|Fock⟩ = 0`, so the first-order correction
vanishes (`ChapterF1` `bargmann`/monomial computations).

**A.3** `derivativeField_momentum` — the derivative modes are fields with their
own momenta: the multi-mode CCR `[u_{j,k}, π^{mn}] = i·δ^n_j·δ^m_k`
(`book.tex:4169`), reusing `ChapterF1.ccr_mv` (`ChapterF1.lean:76`) and
`field_ccr` (`ChapterF1.lean:107`). This is the formal "derivatives-as-fields"
statement the truncation of Part C builds on.

**A.4** `momentumConstraint_preserved` — the momentum constraint commutes with
the dynamics: `[[D, A], H] = −[D, [H, A]]` when `[D, H] = 0`, exactly as in
`ChapterFreeFieldConstraint.lean` (`constraint_commutation_identity`) — the
constraint is a first-class invariant, not an emergent one.

### Part B — The volume-preservation constraint (Lagrangian change of variables)

This part records the **Lagrangian (parcel) form** of the incompressibility
constraint, which is the honest candidate for the complete-flow realization that
§7 requires. The Eulerian NS operator, transformed to Lagrangian variables
`x = X(ξ, t)` with parcel velocity = canonical momentum `u_i(X(ξ)) = Ẋ_i(ξ) =
P_i(ξ)`, becomes a sum of four contributions whose operator *orders* are the key
structural fact:

| Eulerian term | Lagrangian form | operator order |
| :-- | :-- | :--: |
| advection `−u_j ∂_j u_i` | `−½ Δ_X = −½ Σ P_i(ξ)²` (kinetic Laplacian) | 2nd |
| viscosity `ν Δ_x u_i` | `−ν |∇_ξ P_i|²` (viscous Laplacian) | 2nd |
| pressure `−∂_i p` | `λ(ξ)·(det(∂X_i/∂ξ_j) − 1) + ghost` | 0th (constraint) |
| external force `f_i` | `−i·f_i(X(ξ))·(δ/δX_i)` | 1st (drift) |

**B.1** `lagrangian_velocity : u_i(X(ξ)) = P_i(ξ)` — the identification of the
parcel velocity with the canonical momentum of the trajectory operator.

**B.2** `volume_preservation_constraint : det(∂X_i/∂ξ_j) = 1` — incompressibility
in parcel space (`∇·u = 0` ⟺ volume preservation), the 0-order BRST constraint
with `λ(ξ)` the Lagrange multiplier / ghost field (the Lagrangian shadow of
`book.tex` §4187-4197). This is the finite-determinant, algebraic core.

**B.3** `transformed_hamiltonian_decomposition` — the four-term decomposition of
the full transformed operator `ĥ_full = −½Δ_X − νΔ_{ξ,X} − i·f(X)·∇_X +
Ĥ_constraint`, stated with its operator orders (2nd + 2nd + 1st + 0th). The
advection becoming a *positive* 2nd-order Laplacian is the structural change that
makes the ESA question tractable: a 2nd-order elliptic operator with a
relatively-bounded 1st-order drift (Kato–Rellich / Ikebe–Kato), plus a 0-order
constraint that commutes with the Laplacians.

**B.4** *Honesty flag.* The Kato–Rellich / Ikebe–Kato **ESA conclusion** for the
*continuum* trajectory-space operator is an analytic theorem (functional
Laplacian on `C_c^∞(trajectories)`, Sobolev embedding, relative boundedness) —
record it in the docstring as the §7 research **route**, exactly as the plan
already fences the continuum claim. What is provable *now* is the finite/
algebraic part: B.1 (the identification), B.2 (the determinant constraint), B.3
(the operator-order decomposition as a statement about the four terms), and the
finite-truncation completeness of Parts C–D. This part is the "w = 1/x"-style
change of variables for NS that the ODE chapter's resolution pattern
(`Book/OdeSingularity.lean`) suggests.

### Part C — The finite truncation is a finite Hermitian matrix

**C.1** `nsFieldModes : Fin 15` — the 15 field modes
(`u_k` k=0..2, `u_{k,j}` 3..11, `u_{k,jj}` 12..14) — the finite shadow of Part A's
field-with-derivatives construction. Define the NS interaction
operator on the truncation as a finite matrix `nsInteraction : Matrix (Fin N) (Fin N) ℂ`
mirroring `continuityHamiltonian` in `ChapterContinuityUnitary.lean`.

**C.2** `nsHamiltonian : Matrix (Fin N) (Fin N) ℂ` — the truncated
`H_N = Σ_i (π_i A_i + A_i π_i)` with `A_i = Σ_j u_j u_{i,j} − ν u_{12+i}`,
following the anti-commutator construction of `navier_stokes_hamiltonian` in
`nested_fock_algebra/src/models.rs:72`.

**C.3** `nsHamiltonian_hermitian : nsHamiltonianᴴ = nsHamiltonian` —
prove `π_i` is Hermitian (exactly `momentum_hermitian` in
`ChapterContinuityUnitary.lean`), `A_i` is Hermitian (each factor `u_j`, `u_{i,j}`
is a symmetric matrix; `ν ∈ ℝ`), and the anti-commutator of two Hermitian
matrices is Hermitian. *Hint:* reuse the `Matrix.conjTranspose_apply` + `ext i j`
+ `fin_cases` pattern already used throughout `ChapterNavierStokes.lean`.

**C.4** `nsHamiltonian_isPolynomial` — every entry of `nsHamiltonian` is a
polynomial of **degree ≤ 3** in the ladder operators; state it as: for each
`i j`, the `(i,j)`-entry is `∑ c · a†_{k₁} a_{k₂} a_{k₃}` with at most 3 factors
(`∃ terms : Finset ...`, each term a product of ≤ 3 ladder ops). This is the
formal statement of the "low degree in the fields" hypothesis (`book.tex` §4199).
**Role: symmetry, not self-adjointness.** Low degree shows `H_N` is a
well-defined *polynomial* operator (hence symmetric, defined on the dense
finite-particle domain, no renormalization). It does **not** by itself imply
self-adjointness — the correct criterion is flow completeness (Nelson), which is
exactly why Part D works on the *finite matrix* (where self-adjointness holds
automatically) rather than inferring it from the degree bound.

### Part D — Complete flow on the truncation (no singularities)

Reuse the already-proved finite machinery of `ChapterContinuityUnitary.lean`
(`exp_smul_I_unitary`, `continuityUnitary_unitary`, `continuityUnitary_add`,
`unitary_preserves_normSq`) — the same lemmas that power the `continuityUnitary`
package. The truncation matrix is finite, so `Matrix.exp` exists and is a matrix
unitary.

**D.1** `nsFlowUnitary (t : ℝ) : Matrix (Fin N) (Fin N) ℂ :=
NormedSpace.exp (((t : ℂ) * Complex.I) • nsHamiltonian)` — matching the
`continuityUnitary` convention (`ChapterContinuityUnitary.lean:141-143`).

**D.2** `nsFlow_unitary (t) : (nsFlowUnitary t)ᴴ * nsFlowUnitary t = 1` —
unitarity of each `e^{-itH_N}`; a direct instance of `exp_smul_I_unitary`
(`ChapterContinuityUnitary.lean:124`) applied to `nsHamiltonian_hermitian`.

**D.3** `nsFlow_group (s t) : nsFlowUnitary (s + t) = nsFlowUnitary s * nsFlowUnitary t` —
the one-parameter group law, i.e. the flow is **complete** (defined for every
real time). Proof shape: `NormedSpace.exp_add`/`Matrix.exp_add_of_commute`
with `Commute.neg_left`-style commuting factors, exactly as in
`continuityUnitary_add` (`ChapterContinuityUnitary.lean:154`). The `(i t H)`
sign convention makes both orderings commute trivially.

**D.4** `nsFlow_zero : nsFlowUnitary 0 = 1` — `NormedSpace.exp_zero`
(as `continuityUnitary_zero`, `ChapterContinuityUnitary.lean:150`).

**D.5** `nsFlow_norm_preserving (t) (ψ : Fin N → ℂ) :
  ‖nsFlowUnitary t • ψ‖ = ‖ψ‖` — via `unitary_preserves_normSq`
(already in `ChapterContinuityUnitary.lean:198`).

**D.6** `nsFlow_noBlowup (t) (ψ : Fin N → ℂ) (k : Fin N) :
  (nsFlowUnitary t • ψ) k ≠ ∞` — trivially true since `ℂ` has no infinity;
  state it as `(nsFlowUnitary t • ψ) k : ℂ` well-typed / finite, i.e. the
  evolved coefficients are finite complex numbers for every finite `t`.

**D.7** `nsFlow_groupOnEvolved (t₁ t₂) : nsFlowUnitary t₁ • (nsFlowUnitary t₂ • ψ) =
  nsFlowUnitary (t₁ + t₂) • ψ` — the complete-flow statement acting on states
  (what the numerical `time_evolve`/`reconstruct` loop realizes).

### Part E — BRST constraint (mostly reuse)

**E.1** `nsBrst_nilpotent : Ω * Ω = 0` where
`Ω = Σ_j (u_{j,j} : Matrix (Fin N) (Fin N) ℂ) * (ghostAnnih j)` is the truncated
BRST charge. Reuse `brst_charge_nilpotent` (`ChapterGhostField.lean:124`) — the
nilpotency reduces to the ghost CAR/nilpotency already proved — plus the bosonic
fields commuting with each other.

**E.2** `nsDivergenceConstraint_resolution :
  (U11 + U22 + U33) with U33 := -(U11 + U22) = 0` — the formal statement of the
  symbolic `VerifySubstitution` test / book.tex §4191-4197: the divergence
  constraint `∂_j u_j = u_{1,1}+u_{2,2}+u_{3,3}` is solved by the replacement
  `u_{3,3} = u_{1,1}+u_{2,2}`. (Statement form: for `u11 u22 u33 : ℝ`,
  `h : u33 = -(u11+u22)`, conclude `u11 + u22 + u33 = 0` — `linarith`.)

**E.3** (optional) `nsBrst_hermitian : Ωᴴ = Ω` — the BRST charge is Hermitian
(same proof shape as `brst_charge_nilpotent`'s surroundings), tying E.1 to the
physical "project on ker Ω" construction of `fock_sirk`'s `brst.rs`.

### Part F — The book.tex correspondence (prose + record)

**F.1** Module docstring mapping each theorem to its `book.tex` line
(`chapter at book.tex:3699`, NS section `book.tex:4133-4216`, degrees of freedom /
derivatives-as-fields `book.tex:4151-4173` (Part A), CCRs `book.tex:4163-4170`
(Part A.3), Hamiltonian `book.tex:4184-4189`, constraint `book.tex:4191-4197`,
self-adjointness claim `book.tex:4199-4208`, existence/uniqueness
`book.tex:4210-4216`), and to the matching numerical test in unfer. Follow the
honesty-flag style of `Book/OdeSingularity.lean` and
`BookProof/ChapterOdeComplexification.lean`
(`ae_no_real_singular_time`).

**F.2** Record in the docstring the exact boundary: the continuum operator's
essential self-adjointness and the NS existence/uniqueness claim are **not**
claimed here; the finite truncation is the honest provable core, and the
infinite-dimensional extension is the §7 research target (whose concrete route is
Part B's Lagrangian change of variables).

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
lake env lean --stdin <<< '#check BookProof.NavierStokesFlow.field_evaluates_to_value'
lake env lean --stdin <<< '#check BookProof.NavierStokesFlow.volume_preservation_constraint'
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

**The candidate route (recorded, not attempted): the Lagrangian change of
variables of Part B.** The Eulerian→Lagrangian transformation
(`u_i(X(ξ)) = P_i(ξ)`, `det(∂X_i/∂ξ_j) = 1`) turns the advection term into a
*positive* 2nd-order functional Laplacian `−½Δ_X`, the viscosity into a 2nd-order
term `−νΔ_{ξ,X}`, the force into a 1st-order drift `−i f(X)·∇_X`, and the
pressure into the 0-order volume-preservation constraint. The ESA claim then
becomes a **Kato–Rellich / Ikebe–Kato** relative-boundedness argument on the
continuum trajectory space (2nd-order elliptic symbol dominating a relatively-
bounded 1st-order drift), which is genuinely a functional-analytic theorem, not a
finite computation. That is why it is a research target, not a plan item — but it
is now a *named* route (with its operator-order skeleton in Part B), in the same
spirit as `Singularity/ChangeOfVars.lean`'s reciprocal/logarithmic maps.

Distinct from this research target: the *nesting* of the finite approximation
orders is **not** a research target — it is decidable, finite-dimensional linear
algebra, and is a separate plan item (`PLAN_LEAN_SPECIALIST_SIRK_NESTED.md`,
`BookProof/ChapterH8`), a property of the generic Krylov–Hashimoto machinery
rather than of Navier–Stokes. The Crouzeix-based numerical *width* of the nested
bands remains an `EXTERNAL` analytic input; the nesting itself does not depend on
it.
