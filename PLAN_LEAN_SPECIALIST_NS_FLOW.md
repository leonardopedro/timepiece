# Plan for the LLM–Lean 4 Specialist: The Navier–Stokes Hamiltonian Has a Complete Flow

Execution plan for an LLM–Lean-4-specialist agent. The goal is to **formalize the
claim that the Navier–Stokes Hamiltonian generates a complete flow (no finite-time
singularities)** in the finite-truncation setting, in a way that is `sorry`-free and
`axiom`-free (only `propext`, `Classical.choice`, `Quot.sound`), and to record
explicitly what is *not* being claimed (the infinite-dimensional essential
self-adjointness of `book.tex` §4199-4208 remains a research target).

Every new theorem must remain `sorry`-free and `axiom`-free.

## Status

**EXECUTED (2026-08-14→16).** This plan was carried out by the Aristotle
specialist in three waves; every headline item is `sorry`-free and `axiom`-free,
and the book and plan are in one-to-one correspondence. What was accomplished,
part by part (all registered in `BookProof.lean`, all `#check`-ed from
`Book/FreeField.lean`):

| Plan part | Where it landed | Headline theorems |
| :-- | :-- | :-- |
| A.1–A.4 field + momentum | `ChapterNavierStokesFlow.lean` | `fieldTaylor`, `field_evaluates_to_value`, `derivativeField_momentum`, `momentumConstraint_preserved` (A.1's position operator is `ChapterF1.fieldPhi = creat + annih`, now also available under the plan's name as `ChapterF1.positionOp`) |
| A.5 Eulerian constraints | `ChapterNavierStokesEulerian.lean` | `u_evaluates_to_value`, `eulerian_momentum_constraint`, `eulerian_momentum_dual`, `derivativeField_relates_to_field`, `derivativeField_second`, `derivativeField_consistency`, `eulerian_divergence_constraint`, `cyclicShear_divergence_free` |
| A.5 gauge generators | `ChapterNavierStokesGaugeY.lean` | `uField`, `genX`, `genY`, `genX_genX_commute`, `genX_genY_commute`, `genY_genY_commute`, `genY_uField`, `genY_uField_perturbed_ne_zero`, `setYZero_uField`, `hamiltonianOp_apply_of_y_zero` |
| A.6/A.7 second-order gauge generator | `ChapterNavierStokesGaugeY2.lean` | `uField2`, `uDField`, `genY2`, `uField2_pderiv_y`, `uField2_pderiv_y_twice`, `genY2_leibniz`, `genY2_uField2`, `genY2_uDField`, `genY2_nsSymbol2`, `genX_nsSymbol2`, `setYZero_nsSymbol2`, `genY_uField2_ne_zero`, `genY2_uField_ne_zero`, `genY2_uField2_perturbed_ne_zero`, `genY2_genY2_commute`, `genX_genY2_commute`, `genY_genY2_not_commute` |
| B Lagrangian + volume | `ChapterNavierStokesFlow.lean` | `lagrangian_velocity`, `volume_preservation_constraint`, `transformed_hamiltonian_decomposition`, `det_one_add_smul_hasDerivAt` |
| C finite truncation | `ChapterNavierStokesFlow.lean` | `nsHamiltonian`, `nsHamiltonian_hermitian`, `nsHamiltonian_isPolynomial`, `nsWord_length_le_three` |
| D complete flow | `ChapterNavierStokesFlow.lean` + `ChapterNavierStokesCauchy.lean` | `nsFlow_unitary`, `nsFlow_group`, `nsFlow_norm_preserving`, `nsFlow_noBlowup`, `nsCauchy_existsUnique`, `nsFlow_energy_conserved` |
| E BRST constraint | `ChapterNavierStokesFlow.lean` + `ChapterNavierStokesEulerian.lean` | `nsBrst_nilpotent`, `nsDivergenceConstraint_resolution`, and the **E.3 correction**: `nsBrst_not_hermitian` (Ω is *not* Hermitian when the divergence is non-zero; the honest Hermitian statement is `nsBrst_symmetrization_hermitian`). **E.5 (the derivative-field BRST charge) is ON HOLD — not part of the executed state.** |
| G Faris–Lavine | `ChapterFarisLavine.lean` + `ChapterNavierStokesHermiteFarisLavine.lean`, `FockManyMode.lean`, `MomentumEsa.lean`, `IkebeKato.lean`, `ShiftHamiltonian.lean`, `MomentumPerturbation.lean` | `essentiallySelfAdjointOn_of_farisLavine` (the criterion **proved**, Theorem 1 + Cor. 1.1), `nsH_essentiallySelfAdjointOn_core`, `fockH_essentiallySelfAdjointOn_core`, `ns_hamiltonian_essentiallySelfAdjointOn_core`, `navierStokes_fock_hamiltonian_essentiallySelfAdjointOn_core`, `pertHam_essentiallySelfAdjointOn_core` — both FL inequalities proved for the Hamiltonian itself, with a genuinely non-vanishing commutator `fock_commForm_ne_zero` |
| ESA criteria + limits | `ChapterNavierStokesEsa.lean`, `ChapterNavierStokesDeficiency.lean`, `ChapterNavierStokesFullEsa.lean`, `ChapterNavierStokesLagrangianEsa.lean`, `ChapterNavierStokesSecondQuant.lean` | `hasZeroDeficiencyOn_of_completeUnitaryFlow`, `hasZeroDeficiencyOn_of_total_eigenvectors`, `jacobi_symmetric_dense_not_esa` (the limit-circle counterexample), `exists_nsFullData_not_hasZeroDeficiencyOn`, `fockOp_hasZeroDeficiencyOn` (the one-particle→Fock lift) |

**Status of the numerics.** `nested_fock_algebra` asserts `test_navier_stokes_hermitian`,
`test_navier_stokes_low_degree`, `test_navier_stokes_brst_nilpotent`; `fock_sirk`
asserts `navier_stokes_flow_complete_and_unitary`; `prob_kernel` verifies the
divergence-constraint resolution symbolically in Cadabra2
(`verify_navier_stokes_divergence_constraint_resolution`).

**What remains open** is exactly the boundary recorded in §2/§7 and the honesty
flags: the *continuum* operator's essential self-adjointness and global
existence/uniqueness for NS. On the FL route the residual is now narrow and
concrete, not a "Sobolev/differential realization": the proved fiber is
`h = ½(πV + Vπ)` with `V = κu` **linear** in the field (on `L²(du)`, `π = −i∂/∂u`),
while the NS `A_i = u_j u_{i,j} − ν u_{i,jj}` is **quadratic** in the fields. The
step that remains is the FL *estimate* — the relative bound
`‖A_iψ‖² ≤ a‖N̂ψ‖² + b‖ψ‖²` and the form-commutator bound for that quadratic
`A_i` — once the Part-A constraints make the field variables legitimate. That is
a concrete calculation in the proved framework, not a research project needing
new analytic ideas. The Eulerian and Lagrangian routes are both named in §7. On
On top of that, the last open plan item **A.7** — the second-derivative
extension `genY2` of the Eulerian gauge generator (Eulerian variables only),
compensating the Laplacian modes `u_{i,jj}` in the second-order field expansion —
is now **executed** (2026-08-17, `ChapterNavierStokesGaugeY2.lean`), `sorry`-free
and `axiom`-free.

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
argument requires the flow to be complete. Therefore:

- **ESA is the key theorem; global existence of the flow is its corollary.**
  Once essential self-adjointness of the operator is proved — in the Hermite
  basis, where the comparison operator `N = π² + V² + I` is diagonal and the
  Hamiltonian `H = ½(πV + Vπ)` is a concrete shift on the oscillator basis —
  Stone's theorem applies: the closure generates a strongly continuous
  one-parameter unitary group `e^{-itH}` defined for **every** real `t`. That
  complete unitary flow **is** global existence of the operator evolution
  (no finite-time blow-up of the evolved state), which is exactly what `book.tex`
  §4210-4216 means by "the solution ... exists and it is unique" — the
  truncation already proves it as `nsCauchy_existsUnique`, and in the
  infinite-dimensional Hermite/Fock realizations it is a *corollary of the
  proved ESA*, not a separate research target.
- **The genuinely open boundary is the *classical* Navier–Stokes PDE
  (Contention D5, deliberate scope cut).** Completeness of the Hilbert-space
  unitary flow does **not** by itself settle the Clay regularity problem — global
  smooth existence/uniqueness of the classical NS solution is a statement about
  the PDE, not about the operator flow, and it is **not** claimed anywhere in this
  project. The classical-flow completeness (the `ẋ = x²` lesson) is exactly the
  ingredient that neither the degree bound nor the algebraic constraints supply.
  The residual operator-theoretic step is then the FL *estimate* for the actual
  quadratic NS symbol (see §7): once that lands, Stone's theorem delivers the
  complete flow for the continuum operator, with the classical PDE regularity
  remaining the separate, deliberate D5 scope cut.

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
import BookProof.ChapterU         -- Part G.1: prodEquiv (Fock of a Fock)
import BookProof.ChapterF2        -- Part G.3: numberOp/mass_gap comparison operator
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

**A.5** *The Eulerian constraints (the analog of Part B's volume preservation).*
Part B imposes `det(∂X_i/∂ξ_j) = 1` on the *Lagrangian* variables; the
derivatives-as-fields construction needs its **Eulerian** counterpart — the
constraints that make `u_{k,j}`, `u_{k,jj}` legitimate *Eulerian* canonical
variables rather than arbitrary tensors. The book distinguishes the two kinds
(Dirac's first-class / explicit-solution taxonomy, `book.tex` §"Gauge
transformations, constrained systems and conditioned probability", line
2222-2323): first-class constraints are *imposed by defining gauge generators*
("First-class constraints are the generators of a unitary gauge group",
`book.tex:2286`); constraints with an explicit solution need **no** gauge
generator ("There is no need to define a gauge symmetry for these constraints,
because there is an explicit solution", `book.tex:4128`, the holomorphic-fields
precedent). The constraints split exactly along that line:

- `u_evaluates_to_value : u_i(X) = u_i` — the Eulerian velocity field gets the
  *same* operator-valued construction as the generic field of A.2: `u_i(X) =
  u_i + u_{i,j}·(X_j − x_j)`, linear in the position operator `X` with eigenvalue
  `x_j` from the creation/annihilation operators, collapsing to its point value
  `u_i` on the Fock eigenstates of `X`. This is the Eulerian instance of
  `fieldTaylor`/`field_evaluates_to_value`, with the Taylor coefficient `u_{i,j}`
  the derivative mode (and `u_{i,jk}` at second order).
- `eulerian_momentum_constraint : [u_j, π^k] = i·δ^k_j` — the momentum constraint
  *for the Eulerian variables* (book.tex §4163-4170, the zeroth-order member of
  the CCR family), together with `[u_{j,k}, π^{mn}] = i·δ^n_j·δ^m_k` and
  `[u_{i,jk}, π^{lmn}] = i·δ^l_i·δ^m_j·δ^n_k` for the derivative modes. This is
  the book.tex momentum constraint that the derivatives-as-fields construction
  exists to make well-defined: each `u_{i,j}`, `u_{i,jk}` is a canonical variable
  with its own conjugate momentum. (A.3's `derivativeField_momentum` covers the
  first-derivative member; this item states the full family, including the
  zeroth-order `[u_j, π^k]` that couples the velocity field itself.)
- `derivativeField_relates_to_field : u_{i,j} = ∂_j u_i` — the *defining*
  constraint: the first-derivative modes are the actual partial derivatives of
  the field `u_i`. This is what makes `u_{k,j}` a derivative field and not an
  arbitrary tensor — the relation between `u_i` and its first derivatives — and
  it is a **gauge-generator constraint** (no explicit solution: it pins the
  first-derivative modes to the field, on the parametrization/gauge-group view
  `book.tex:2279-2286`, as the holomorphic-fields section's `[D_x, u+iv] = 0`).
- `derivativeField_second : u_{i,jk} = ∂_k u_{i,j}` — the second-derivative
  modes are the derivatives of the first-derivative modes (the same relation
  one level up: `u_{i,jk} = ∂_k ∂_j u_i`).
- `derivativeField_consistency : u_{i,jk} = u_{i,kj}` — Clairaut's condition,
  the *consequence* of `derivativeField_second` in the two orders: mixed
  partials commute, so the derivative modes are integrable and the 18
  second-derivative modes reduce to the 6 symmetric `u_{i,jk}`. It is listed
  separately because it is the algebraic identity a truncation actually states;
  but it is not the primary constraint — the primary one is
  `u_{i,j} = ∂_j u_i`, which relates each derivative to the field it derives
  from. All three are gauge-generator constraints.
- `eulerian_momentum_dual : π^{ij}` — the momentum conjugate to `u_{i,j}`,
  giving the Part-A.3 CCR `[u_{j,k}, π^{mn}] = iδ^n_j δ^m_k` the reading that
  the *derivative* degrees of freedom are canonical variables with their own
  momenta (book.tex §4163-4170). Together with the divergence constraint this
  is the Eulerian side of the change of variables: the Lagrangian `P_i(ξ) =
  Ẋ_i(ξ)` (B.1) becomes the Eulerian derivative modes `u_{i,j} = ∂_j u_i`.
- `eulerian_divergence_constraint : ∂_j u_j = u_{j,j} = 0` — incompressibility
  in Eulerian variables, the direct shadow of the Lagrangian
  `det(∂X_i/∂ξ_j) = 1` (incompressibility ⟺ volume preservation under the
  change of variables). This needs **no gauge generator**: the constraint has an
  explicit solution — the `u_{3,3} = −(u_{1,1}+u_{2,2})` substitution — so it is
  imposed by *initial conditions* that verify it, not by a gauge symmetry
  (`book.tex:4194-4197`: the divergence constraint "can be easily solved... and
  there is a wave-function which verifies it"). The BRST charge
  `Ω = u_{j,j} ⊗ ψ†` (Part E) is then, in book.tex's own words, "used only to
  allow a more elegant formulation without distinguishing one of the space
  indices and not to define the theory itself" — it is the elegant packaging of
  an explicit-solution constraint, not a first-class gauge constraint.

So the A.5 split mirrors the book's taxonomy: **gauge generators** for the
field-to-derivative relations (`u_{i,j} = ∂_j u_i`, `u_{i,jk} = ∂_k u_{i,j}`,
and their Clairaut consequence — no explicit solution), **initial conditions**
for the divergence (explicit `u_{3,3}` solution). Both are algebraic and
provable now; the BRST enforcement is Part E.

**A.6** *The second coordinate `y` and the two gauge generators (proved
2026-08-16, `ChapterNavierStokesGaugeY.lean`; add to the prose if the plan is
re-opened).* The constraint is stated properly only once a second coordinate `y`
is adjoined to the space coordinate `x`: the field that enters the Hamiltonian is
the expansion `u_i(y) = u_i + u_{i,j} y_j` (`uField`). Each coordinate then
carries a gauge generator — for `x` the standard momentum `genX = ∂/∂x_j`; for
`y` the generator built from the *derivatives of* `u_i`,
`genY = ∂/∂y_j − u_{i,j} ∂/∂u_i`, which translates `y` while shifting each
velocity mode by its own first derivative (`genY_shifts_velocity`). Both
annihilate the field and the NS symbol and commute (abelian, hence first class);
`u_{i,j}` is the *only* admissible coefficient of `y_j`
(`genY_uField_perturbed_ne_zero`) — the sharp statement that
`u_{i,j} = ∂u_i/∂y_j`. In the initial state `y` evaluates to `0`, so the field
collapses to its point value `u_i` and the Hamiltonian built from `u_i(y)` acts
as the ordinary Navier–Stokes one (`setYZero_uField`, `setYZero_nsSymbol`,
`hamiltonianOp_apply_of_y_zero`).

**A.7** *The second-derivative extension of `genY` (Eulerian variables only;
**proved 2026-08-17**, `ChapterNavierStokesGaugeY2.lean`).* The `genY` proved in A.6 compensates only the
*first*-derivative modes: it annihilates the linear field
`u_i(y) = u_i + u_{i,j} y_j`. The Eulerian constraint that makes the
second-derivative (Laplacian) modes `u_{i,jj}` legitimate too requires the field
expanded to second order in `y`, `u_i(y) = u_i + u_{i,j} y_j + u_{i,jj} y_j²`,
and the generator extended by the compensating `∂/∂u_{i,j}` term:

```
genY2 j = ∂/∂y_j − u_{i,j} ∂/∂u_i − u_{i,jj} ∂/∂u_{i,j}
```

(verification: `∂/∂y_j` gives `u_{i,j} + u_{i,jj} y_j`, `−u_{i,j}∂/∂u_i` gives
`−u_{i,j}`, `−u_{i,jj}∂/∂u_{i,j}` gives `−u_{i,jj} y_j` — total `0`, so
`genY2 j (uField2 i) = 0`). This is **Eulerian-variables only**: the Lagrangian
(parcel) side has no such field expansion — the transformed operator is built
from the trajectory momenta `P_i` and the viscous gradients `Q_i = ∇_ξ P_i`
directly, with no `u_{i,jj}` mode. Items: `uField2` (the second-order field),
`genY2` (the extended generator), `genY2_uField2` (annihilation), the sharpness
statement `genY2_uField2_perturbed_ne_zero` (the coefficient of `y_j²` is the
*only* admissible one), and `genY2_leibniz`/the abelian-commutation checks.
Reuse `ChapterNavierStokesGaugeY`'s `NSVar` (the `uL : Fin 3 → NSVar` mode is
already present as the Laplacian mode) and its polynomial-momentum machinery.

*As executed (2026-08-17).* One correction to the sketch above: the quadratic
term carries the Taylor coefficient `½`, i.e. the field is
`uField2 i = u_i + u_{i,j} y_j + ½ u_{i,jj} y_j²`; with the coefficient `1` no
generator of the stated shape annihilates it (the `∂/∂y_j` and the compensating
`∂/∂u_{i,j}` terms then differ by a factor `2`).  Beyond the listed items the
module also proves that the *derivative field*
`uDField i j = u_{i,j} + u_{i,jj} y_j` is `∂ u_i(y)/∂ y_j`
(`uField2_pderiv_y`), that `u_{i,jj} = ∂² u_i(y)/∂ y_j²`
(`uField2_pderiv_y_twice`), that the symbol built from the fields
`nsSymbol2 ν i = ∑_j u_j(y) u_{i,j}(y) − ν u_{i,jj}` is gauge invariant
(`genY2_nsSymbol2`, `genX_nsSymbol2`) and collapses on `y = 0` to the ordinary
NS symbol (`setYZero_nsSymbol2`), and — honestly — that the mixed bracket
`⁅genY j, genY2 j⁆` is **not** zero (`genY_genY2_not_commute`): the first- and
second-order generators are truncations of the same gauge transformation at
different orders, and only the second-order one is a symmetry of the
second-order field.

### Part B — The volume-preservation constraint (Lagrangian change of variables)

This part records the **Lagrangian (parcel) form** of the incompressibility
constraint, which is the honest candidate for the complete-flow realization that
§7 requires. The Eulerian NS operator, transformed to Lagrangian variables
`x = X(ξ, t)` with parcel velocity = canonical momentum `u_i(X(ξ)) = Ẋ_i(ξ) =
P_i(ξ)`, becomes a sum of four contributions whose operator *orders* are the key
structural fact. The Eulerian constraints that make this change of variables
coherent are Part A.5's (divergence, Clairaut consistency, derivative momenta);
Part B supplies the Lagrangian side (volume preservation `det(∂X_i/∂ξ_j) = 1`).

| Eulerian term | Lagrangian form | operator order |
| :-- | :-- | :--: |
| advection `−u_j ∂_j u_i` | `−½ Δ_X = −½ Σ P_i(ξ)²` (kinetic Laplacian) | 2nd |
| viscosity `ν Δ_x u_i` | `−ν |∇_ξ P_i|²` (viscous Laplacian) | 2nd |
| pressure `−∂_i p` | `λ(ξ)·(det(∂X_i/∂ξ_j) − 1) + ghost` | 0th (constraint) |
| external force `f_i` | `−i·f_i(X(ξ))·(δ/δX_i)` | 1st (drift) |

**B.1** `lagrangian_velocity : u_i(X(ξ)) = P_i(ξ)` — the identification of the
parcel velocity with the canonical momentum of the trajectory operator. On the
Eulerian side this is A.5's `eulerian_momentum_dual` + `derivativeField_consistency`:
the derivative modes `u_{i,j}` are the Lagrangian momenta pulled back to
Eulerian variables, subject to the divergence constraint.

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

**B.5** The four term-by-term identities (the precise functional-operator forms
of the Eulerian→Lagrangian change of variables, from the full classical NS
momentum equation `∂_t u_i = −u_j ∂_j u_i + νΔ_x u_i − ∂_i p + f_i`):

| Eulerian term | transformed operator identity | order |
| :-- | :-- | :--: |
| advection `∫ πⁱ(−u_j ∂_j u_i)` | `Ĥ_kin = −½ ∫d³ξ δ²/δX_i(ξ)²` | 2nd |
| viscosity `∫ πⁱ νΔ_x u_i` | `Ĥ_visc = −ν ∫d³ξ \|∇_ξ P_i(ξ)\|²` | 2nd |
| pressure `∫ πⁱ(−∂_i p)`, `∇·u=0` | `Ĥ_press = ∫d³ξ λ(ξ)(det(∂X_i/∂ξ_j)−1) + Ĥ_ghost` | 0th |
| external force `∫ πⁱ f_i` | `Ĥ_force = −i ∫d³ξ f_i(X(ξ)) δ/δX_i(ξ)` | 1st |

Here `P_i(ξ) = −i δ/δX_i(ξ)` is the trajectory momentum (so `Ĥ_kin = ½Σ P_i²`
is the flat positive functional Laplacian `Δ_X`, and `Ĥ_visc = −ν|∇_ξ P_i|²`
pulls the spatial Laplacian back to the ξ-gradient of the momentum). The
identities are statements about the *form* of the four terms under the canonical
change of variables `x = X(ξ,t)`, `u_i(X(ξ)) = Ẋ_i(ξ) = P_i(ξ)`,
`πⁱ(x) → P_i(ξ)`; the pressure identity is the 0-order BRST constraint with
`λ(ξ)` the Lagrange multiplier / ghost field projecting onto
`SDiff(ℝ³)` (volume-preserving diffeomorphisms).

**B.6** The full second-quantized operator (Step 3 of the transformation):
`Ĥ_NS = ∫ 𝒟X A†[X] ĥ_full[X] A[X]` on the second-level Fock space, where the
single-fluid operator is

```
ĥ_full[X] = ∫d³ξ [ −½ δ²/δX_i(ξ)²  − ν |∇_ξ (δ/δX_i(ξ))|²  − i f_i(X(ξ)) δ/δX_i(ξ) ]
            + Ĥ_constraint
```

i.e. `ĥ_full = −½Δ_X − νΔ_{ξ,X} − i f(X)·∇_X + Ĥ_constraint` with operator
orders 2nd + 2nd + 1st + 0th. The ESA structure argument (Step 4) is: the
operator is dominated by the two 2nd-order functional Laplacians (flat,
non-negative); the force drift is a 1st-order operator, *infinitesimally small*
relative to the 2nd-order Laplacians (Sobolev embedding / Kato-smallness); the
volume-preservation constraint commutes with the Laplacians because
volume-preserving diffeomorphisms conserve the L² kinetic norm. By Kato–Rellich
/ Ikebe–Kato this is the continuum ESA statement — recorded in §7 as the
research route, **not** claimed here (B.4). The algebraic part that *is* a plan
item: the `∫ a†(…)a` normal form of B.6 with the Fock-of-Fock degree bound of
Part G.2.

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

Per the A.5 taxonomy, the divergence constraint is an *explicit-solution*
constraint: book.tex's own note (`book.tex:4194-4197`) says it "can be easily
solved (e.g. using the replacement `u_{3,3}=u_{1,1}+u_{2,2}`) and there is a
wave-function which verifies it, so the BRST formalism is used only to allow a
more elegant formulation without distinguishing one of the space indices and
not to define the theory itself." So the BRST charge here is the *elegant
packaging* of the constraint — it is **not** a first-class gauge generator (the
derivative-field consistency of A.5 is the one that is). The module docstring
must record this distinction.

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
  `h : u33 = -(u11+u22)`, conclude `u11 + u22 + u33 = 0` — `linarith`.) This is
  the *explicit solution* that makes the constraint initial-condition-imposed
  (A.5): given any two divergence-independent modes, the third is fixed, so the
  constrained space is parameterized without any gauge generator.

**E.3** **SUPERSEDED by the executed wave (2026-08-16).** The plan's optional
`nsBrst_hermitian : Ωᴴ = Ω` is **false** whenever the divergence field is
non-zero: the wave proved `nsBrst_not_hermitian` (`ChapterNavierStokesEulerian.lean`)
together with the honest Hermitian packaging
`nsBrst_symmetrization_hermitian` (`Ω + Ω†` is Hermitian). The physical "project
on ker Ω" construction of `fock_sirk`'s `brst.rs` is tied to E.1's nilpotency,
not to hermiticity of `Ω` — `nsBrst_adjoint` (in `ChapterNavierStokesFlow.lean`)
gives the correct adjoint statement.

**E.4** *Honesty flag.* The module must state that E.1–E.3 formalize the
*packaging* role only: nilpotency of `Ω` and the `u_{3,3}` resolution, exactly
as book.tex describes. The divergence constraint itself needs no gauge generator
(A.5), so E.1–E.3 should **not** be read as a first-class-constraint/
ghost-counting statement about the physical Hilbert space. **The contrast is
E.5**: the derivative-field constraint `u_{i,j} = ∂_j u_i` *is* first-class (no
explicit solution), so its BRST charge `Ω_deriv` (E.5) is a genuine
gauge-enforcing construction — the ghost is load-bearing there, unlike in
E.1–E.3.

**E.5** **ON HOLD (2026-08-18, do not execute for now).** *The BRST charge of
the derivative-field constraint, in the Yang–Mills form (the gauge constraint
that defines `u_{i,j}` as the derivative of the field).* In A.5 the relation
`u_{i,j} = ∂_j u_i`
(`derivativeField_relates_to_field`) is the **gauge-generator** constraint —
first-class, no explicit solution — as opposed to the divergence `u_{j,j} = 0`,
imposed by initial conditions. Its BRST charge must be **analogous to the
Yang–Mills gauge constraints** (`book.tex:7084`), not to the divergence's
packaging `Ω = u_{j,j}⊗ψ†`. The Yang–Mills charge is built from the momentum
contracted with the ghost's **covariant derivative**:

```
Ω_YM = π^k_a ∂_k ψ†_a − π^k_a f_abc A_{k b} ψ†_c − (i/2) f_abc ψ†_a ψ†_b ψ_c
```

i.e. `π^k_a (D_k ψ†)_a + ghost³`, where `(D_k ψ†)_a = ∂_k ψ†_a − f_abc A_{k b} ψ†_c`
is the ghost transforming under the connection `A`, and the ghost self-interaction
`−(i/2) f_abc ψ†ψ†ψ` is what makes `Ω² = 0` when the structure constants are
non-zero. The derivative-field constraint is the *abelian connection* analogue:
`u_{i,j}` is the connection making the field `u_i` covariantly constant,
`D_j u_i = ∂_j u_i − u_{i,j} = 0`. Its BRST charge therefore has the same
three-part Yang–Mills shape, with the derivative-mode momentum `π^{ij}` playing
the role of `π^k_a` and one ghost `η_i` per field component:

```
Ω_deriv = π^{ij} ∂_j η†_i − π^{ij} u_{i,j} η†_i
```

(the `ghost³` term is absent because the constraint algebra is *abelian* —
`[u_{i,j}, u_{k,l}] = 0` — so the structure constants vanish; nilpotency still
holds, as the abelian limit of the Yang–Mills computation). Items:

- `derivConstraintConnection (i j) := u_{i,j} − ∂_j u_i` — the constraint as the
  covariant-constancy condition `D_j u_i = 0` (`D_j := ∂_j − u_{i,j}·`), the
  connection form of `derivativeField_relates_to_field` (same `dirDeriv` of
  `ChapterNavierStokesEulerian`);
- `derivBrstCharge := Σ_{i,j} π^{ij}·(∂_j η†_i − u_{i,j}·η†_i)` — the
  Yang–Mills-shaped charge: momentum × ghost's covariant derivative. This is the
  *generator* form (analogous to `Ω_YM`), not the naive `C ⊗ η†` product;
- **The commutation relations (the ordering that makes the charge well-defined).
  The field `u_i` commutes with the derivative-mode momentum: `[u_i, π^{jk}] = 0`
  (they are not conjugate — `π^{ij}` is the conjugate of the *derivative* mode
  `u_{i,j}`, `[u_{i,j}, π^{kl}] = iδ^k_i δ^l_j` by `derivativeField_momentum`).
  Therefore the charge pairs `π^{ij}` with *its own conjugate* `u_{i,j}` in the
  connection term, exactly as Yang–Mills pairs `π^k_a` with `A_{k a}` — and those
  do **not** commute. The product `π^{ij} u_{i,j}` must be Weyl-ordered
  (`½(π^{ij}u_{i,j} + u_{i,j}π^{ij})`, the same anticommutator convention as the
  NS Hamiltonian `H_N = Σ(π_i A_i + A_i π_i)`), and this ordering is part of the
  definition of `derivBrstCharge`, not a simplification.
- `derivBrst_nilpotent : Ω_deriv * Ω_deriv = 0` — nilpotency, **with the
  non-commutation of `π^{ij}` and `u_{i,j}` handled honestly**. The earlier claim
  that "the bosonic `π^{ij}`, `u_{i,j}` commute" is **wrong** — they are
  conjugate (`[u_{i,j}, π^{kl}] = iδ^k_i δ^l_j`). Two defensible routes:
  - *(i) the honest Yang–Mills computation.* The `ghost³` self-interaction term
    `−(i/2) f η†η†η` is *not* automatically zero here: it is exactly what
    cancels the `[π^{ij}, u_{i,j}] = −i` c-number contributions to `Ω²`, as in
    Yang–Mills. The abelian statement `f = 0` is a *theorem to prove* (the
    constraint algebra `[C_{ij}, C_{kl}] = 0` of the first-class constraints is
    abelian), not an assumption; with the Weyl ordering and the ghost CAR the
    computation is the Yang–Mills one with `f_abc = 0`, and `η†_i² = 0`
    (per-component `psiDag_sq`). This is the correct proof shape — use
    `brst_charge_nilpotent` + the ghost CAR, but *not* a claim that `π` and `u`
    commute.
  - *(ii) the standard first-class-constraint form (fallback, cleaner).* The
    textbook BRST charge of an *abelian* set of first-class constraints
    `{C_{ij} = 0}` is simply `Ω = Σ_{i,j} η†_{ij} C_{ij}` (one ghost per
    constraint, no `π`, no connection), and nilpotency follows from the abelian
    constraint algebra `[C_{ij}, C_{kl}] = 0` alone — provable with
    `brst_charge_nilpotent` directly. This avoids the ordering entirely and is
    the honest, minimal, provable statement. If route (ii) is taken, record in
    the docstring that the Yang–Mills-shaped `π D η†` form of E.5 is the
    *connection* refinement whose nilpotency requires the ghost³-cancellation
    argument of route (i).
- `derivBrst_adjoint : Ω_derivᴴ = Σ π^{ij}(∂_j η_i − u_{i,j} η_i)` — the charge
  is not Hermitian (ghost creation factors), so the physical space is the
  cohomology, mirroring `nsBrst_adjoint` and the Yang–Mills `Ω`;
- `derivBrst_kernel_relates_field` — the honest statement of what the cohomology
  computes: a state in `ker Ω_deriv` (ghost structure fixed) satisfies
  `u_{i,j} = ∂_j u_i` componentwise — the BRST form of
  `derivativeField_relates_to_field`.

This is the *first-class* BRST constraint, in contrast with the divergence's
explicit-solution packaging (E.4): here the ghost is load-bearing, because the
constraint has no explicit solution. The `Ω_deriv` construction is the BRST
shadow of the A.6/A.7 gauge generators (`genY`, `genY2`) — those are the
generators, `Ω_deriv` is their ghost-enforced BRST charge in the Yang–Mills
form. The structural parallel to record in the docstring: **the divergence
constraint is the `u_{j,j}` "abelian Gauss law" analogue (packaging BRST), while
the derivative-field constraint is the `D_j u_i = 0` "connection" analogue
(load-bearing BRST), exactly as `Ω = u_{j,j}ψ†` vs `Ω_YM = π D ψ† + ghost³`.
Eulerian-only: the Lagrangian parcel side has no such field-derivative
constraint.

**On-hold note (2026-08-18).** E.5 is **deferred**: it is a genuine plan item
(not yet proved, not yet in any `BookProof/` module) and is deliberately **not**
part of the current execution wave. The item is kept in full detail so it can be
executed later without re-derivation. E.1–E.4 are unaffected — they are already
proved and remain part of the done state. If a future pass wants to pick E.5 up,
the two open sub-decisions recorded above (the Weyl ordering of `π^{ij}u_{i,j}`,
and the nilpotency route (i) full Yang–Mills vs (ii) standard first-class form)
must be settled first.

### Part F — The book.tex correspondence (prose + record)

**F.1** Module docstring mapping each theorem to its `book.tex` line
(`chapter at book.tex:3699`, NS section `book.tex:4133-4216`, degrees of freedom /
derivatives-as-fields `book.tex:4151-4173` (Part A), CCRs `book.tex:4163-4170`
(Part A.3), Hamiltonian `book.tex:4184-4189`, constraint `book.tex:4191-4197`,
self-adjointness claim `book.tex:4199-4208`, existence/uniqueness
`book.tex:4210-4216`, the gauge-generator taxonomy `book.tex:2286`
("first-class constraints are the generators of a unitary gauge group"),
the explicit-solution no-gauge precedent `book.tex:4128`, and the
BRST-is-elegance-only note `book.tex:4194-4197`), and to the matching numerical
test in unfer. Follow the honesty-flag style of `Book/OdeSingularity.lean` and
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

### Part G — Essential self-adjointness via Faris–Lavine on the Fock-of-Fock
structure

This part records the ESA **theorem** for the transformed (Lagrangian)
Navier–Stokes Hamiltonian. It is the formalization of `book.tex` §4199-4208's own
route — *Faris & Lavine 1974, Corollary 1.1* (`cmpux2f1103859517`, confirmed at
`book.tex:10953`) — but applied to the Part-B transformed operator rather than to
the failed auxiliary-operator argument. The structural fact that makes the
comparison-operator bound plausible is that the second-quantized (Fock-of-Fock)
form of the transformed operator is **at most quadratic** in the creation and
annihilation operators of the outer Fock layer.

**G.1 — the Fock-of-Fock structure (reuse).** The Hilbert space of the NS flow is
a Fock space *over a Fock space*: `Γ(L²(ℝ¹⁵×ℤ₂³)) = Γ(Γ(L²(ℝ¹⁵×ℤ₂³))₀)` in the
second-quantized picture, and the algebraic identity that makes this concrete is
`prodEquiv : Sym(M × N) ≅ Sym M ⊗ Sym N` (`ChapterU.lean:125`) — the tensor
product of two Fock spaces is again a Fock space. State the second-quantized form
of the transformed operator: `Ĥ = ∫ 𝒟X A†[X] ĥ_full[X] A[X]` with `A[X]`,
`A†[X]` the outer (trajectory-indexed) ladder operators.

**G.2 — the operator is at-most-quadratic in the outer ladder operators.** The
four terms of `ĥ_full` (Part B) — kinetic `−½Δ_X`, viscous `−νΔ_{ξ,X}`, force
drift `−i f(X)·∇_X`, 0-order constraint — act on the *inner* field of one
trajectory; the outer ladder operators `A`, `A†` enter **at most quadratically**
(one `A†` times one `A` per term, the book's `∫ a†(…)a` normal form). State and
prove: `ns_outer_degree_le_two : ∀ term, term is a product of ≤ 2 outer ladder
operators` — the Fock-of-Fock shadow of Part C.4's low-degree hypothesis, but now
for the *outer* quantization.

**G.3 — the comparison operator (reuse).** Let `N` be the (number-operator /
harmonic-oscillator) comparison operator of the outer Fock layer, the second-
quantized `∫ 𝒟X A†[X] A[X]`. Reuse the existing number-operator lemmas:
`ChapterF1.numberOp`/`numberOp_monomial`, `ChapterF2.hamiltonian_commutes_numberOp`
and `mass_gap` (the positivity/gap structure), and `ChapterH7.generation_…` /
`compress_isSelfAdjoint` for the operator-algebra hygiene.

**G.4 — Faris–Lavine: the ESA theorem, conditional (the headline).** State the
Faris–Lavine commutator criterion (Faris & Lavine 1974, Corollary 1.1; Reed &
Simon Vol. II, Theorem X.28 = Sears' theorem for the quadratic-growth case) as a
**named theorem with citation docstring — never an axiom** (the `EXTERNAL`
pattern, as with Crouzeix in `ChapterH4`):

```
ns_esa_of_farisLavine
  (N : E →ₗ[ℂ] E) (H : E →ₗ[ℂ] E) (c1 c2 : ℝ)
  (hN : 0 < c1) (hNN : 0 < c2)
  (hHbound : ∀ ψ, ‖H ψ‖ ≤ c1 * ‖N ψ‖)            -- operator-norm bound (H rel.-bounded by N)
  (hCommutator : ∀ ψ, ‖⟨ψ, [H, N] ψ⟩‖ ≤ c2 * ⟨ψ, N ψ⟩)  -- form commutator bound
  : IsEssentiallySelfAdjoint H
```

with `IsEssentiallySelfAdjoint` defined as in `Singularity/Esa.lean`
(`isEssentiallySelfAdjoint`, deficiency indices `(0,0)`), and `H := ĥ_full`
(the transformed single-fluid operator, Part B) and `N` the outer number operator
(G.3). The two hypotheses `hHbound`, `hCommutator` are the two Faris–Lavine
inequalities; verifying them for the actual `ĥ_full` is the analytic step
recorded in G.5. Sears' theorem (Reed & Simon X.28) is the potential-specialized
form: `−Δ + V` with `V(x) ≥ −c|x|² − d` is ESA — which is exactly the shape of
the at-most-quadratic bound that G.2's degree-≤-2 structure supports.

**G.5 — honesty flag (the boundary).** The theorem `ns_esa_of_farisLavine` is the
*framing*; the two analytic inequalities (`hHbound`, `hCommutator`) for the
continuum `ĥ_full` are **not** proved in this plan — they are named hypotheses
with the Faris–Lavine/Sears/Reed–Simon citations, exactly as Crouzeix enters
`ChapterH4` as a named hypothesis. The finite-truncation completeness (Parts C–D)
remains the honest provable core; the continuum ESA conclusion is the §7 research
target, now with a *named theorem* (`ns_esa_of_farisLavine`) and a *named route*
(the Part-B Lagrangian change of variables turning advection into the positive
2nd-order Laplacian that the quadratic-growth condition needs). Do **not** present
`ns_esa_of_farisLavine` as a proved theorem; it is a conditional statement with
named analytic inputs, like `sirk_error_bound_decay`.

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
lake env lean --stdin <<< '#check BookProof.NavierStokesFlow.LagrangianNS.transformed_hamiltonian_decomposition'
lake env lean --stdin <<< '#check BookProof.NavierStokesFlow.ns_outer_degree_le_two'
lake env lean --stdin <<< '#check BookProof.NavierStokesFlow.ns_esa_of_farisLavine'
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
`Γ^s(L²(ℝ¹⁵×ℤ₂³)) ⊗ Γ^a(L²(ℝ¹⁵×ℤ₂³))` — is **not** a plan item. Note that
"and hence global existence/uniqueness" is *not* an additional claim here: once
ESA is proved, Stone's theorem gives the complete unitary flow (global existence
of the operator evolution) automatically — see §2. What genuinely remains open is
the **ESA of the continuum operator itself** (the FL estimate for the quadratic
symbol) and, as a separate deliberate scope cut, the *classical* NS PDE regularity
(Contention D5). The ODE chapter's `x' = x²` example is the standing warning that
a low-degree polynomial Hamiltonian need *not* be essentially self-adjoint when
the classical flow is incomplete; the book.tex auxiliary-operator argument is
exactly the one that project's ODE chapter corrects. Any future attempt must
first construct a genuinely complete classical-flow / analytic realization, on
the pattern of the ODE chapter's `w = 1/x` resolution — and the honest current
record is `BookProof/ChapterUnboundedPosition.lean` +
`BookProof/ChapterContinuityUnitaryInfinite.lean` (the `ℓ²(ℤ)` bounded layer, where
Stone's relation is discharged for multiplication operators) plus the
Stone-theorem-in-full-generality target already recorded in `CONSOLIDATED_PLAN.md`
§9.

**The candidate routes (recorded, not attempted): two viable paths — the
Lagrangian (Part B) and the Eulerian (Part A) — each completed by the
Faris–Lavine criterion of Part G.**

*Path (1): the Lagrangian change of variables of Part B.* The
Eulerian→Lagrangian transformation
(`u_i(X(ξ)) = P_i(ξ)`, `det(∂X_i/∂ξ_j) = 1`) turns the four terms of the full
NS momentum equation into the explicit identities of B.5: advection into the
*positive* 2nd-order functional Laplacian `Ĥ_kin = −½∫δ²/δX_i(ξ)²`, viscosity
into the 2nd-order `Ĥ_visc = −ν∫|∇_ξ P_i|²`, the force into the 1st-order drift
`Ĥ_force = −i∫f_i(X) δ/δX_i`, and the pressure into the 0-order volume-preservation
constraint `λ(ξ)(det(∂X_i/∂ξ_j)−1)` — assembled in B.6 into
`ĥ_full = −½Δ_X − νΔ_{ξ,X} − i f(X)·∇_X + Ĥ_constraint`. The ESA claim then
becomes either (a) a **Kato–Rellich / Ikebe–Kato** relative-boundedness argument
on the continuum trajectory space — 2nd-order elliptic principal symbol
dominating the Kato-small 1st-order drift (Sobolev embedding), constraint
commuting with the Laplacians because volume-preserving diffeomorphisms conserve
the L² kinetic norm — or (b) a **Faris–Lavine commutator** argument (Faris &
Lavine 1974, Corollary 1.1; Reed & Simon Vol. II Thm X.28 / Sears): the
Fock-of-Fock form of the transformed operator is at-most-quadratic in the outer
ladder operators (Part G.2), so with `N` the outer number operator the two
inequalities `‖Hψ‖ ≤ c₁‖Nψ‖` and `‖⟨ψ,[H,N]ψ⟩‖ ≤ c₂⟨ψ,Nψ⟩` are the right shape
to verify.

*Path (2): the Eulerian variables, staying in the derivatives-as-fields
picture of Part A.* Here the ESA route does **not** change variables: the
field-with-derivatives construction of Part A makes `u_{k,j}`, `u_{k,jj}`
Eulerian canonical variables (A.3 CCRs), the constraints of A.5 (divergence
`u_{j,j} = 0`, Clairaut consistency, the derivative momenta `π^{ij}`) keep them
honest, and the *momentum representation* of the fiber — where the comparison
operator `n = Σᵢπᵢ² + ΣᵢVᵢ² + I` is a multiplication operator — is where the two
Faris–Lavine inequalities are actually **verifiable in the finite-mode core**
(that is the wave already proved: `ChapterNavierStokesHermiteFarisLavine`,
`ChapterNavierStokesFockManyMode`, `ChapterNavierStokesMomentumEsa`, with the
Ikebe–Kato input `ChapterNavierStokesIkebeKato`). The Eulerian path is the one
the Aristotle wave took. The proved fiber is on `L²(du)` with `π = −i∂/∂u` — a
genuine differential operator — but with `V = κu` **linear** in the field; the
residual step is the FL *estimate* for the actual **quadratic** NS symbol
`A_i = u_j u_{i,j} − ν u_{i,jj}`, which is a concrete calculation in the proved
framework (the relative bound and form-commutator bound for that polynomial),
not a "Sobolev realization" gap.

The two paths are complementary: the Lagrangian one trades the nasty advection
`−u_j∂_j u_i` for a positive Laplacian (at the price of the nonlinear
`det = 1` constraint); the Eulerian one keeps the physical variables (at the
price of the linearized fiber Hamiltonian of the Hermite realization). Both
reduce to: a 2nd-order/at-most-quadratic operator plus a comparison-operator
Faris–Lavine verification. The residual on each route is the FL *estimate* for
the actual NS symbol — the relative bound and the form-commutator bound — which
is a concrete calculation in the already-proved framework (criterion + Ikebe–
Kato + comparison operator all in place), closer to a plan item than to a
research project needing new analytic machinery; the global-existence step
beyond ESA remains the honest research boundary. Both routes are *named* in full
detail (Part B.5/B.6's operator identities, Part A/A.5's Eulerian constraints,
Part G's theorem `ns_esa_of_farisLavine` with named hypotheses), in the same
spirit as
`Singularity/ChangeOfVars.lean`'s reciprocal/logarithmic maps.

Distinct from this research target: the *nesting* of the finite approximation
orders is **not** a research target — it is decidable, finite-dimensional linear
algebra, and is a separate plan item (`PLAN_LEAN_SPECIALIST_SIRK_NESTED.md`,
`BookProof/ChapterH8`), a property of the generic Krylov–Hashimoto machinery
rather than of Navier–Stokes. The Crouzeix-based numerical *width* of the nested
bands remains an `EXTERNAL` analytic input; the nesting itself does not depend on
it.
