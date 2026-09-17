# Which `N`? Comparison operators for the Faris–Lavine route — one per Hamiltonian

*2026‑09‑15.  Companion to the 2026‑09‑15 wave of `CONSOLIDATED_PLAN.md` ("the derivative
variables are eliminated by the spatial Fourier transform, not fixed by a BRST gauge
symmetry") and to §0.1 of `REVIEW_FARIS_LAVINE_20260911.md`.  This is a **design note**: every
statement below is a **candidate with a named obligation**; none of it is a proved Lean
theorem.  The load-bearing item of the wave is exactly the choice of `N`, because everything
else (the Fourier unitary, the convolution algebra, the `dΓ` lift) is the project's existing
machinery.*

## 0. What the criterion actually consumes

`BookProof.FarisLavine.essentiallySelfAdjointOn_of_farisLavine` (module
`BookProof.ChapterFarisLavineCore`) takes a common dense domain `D`, two linear maps `H, N : D →ₗ[ℂ] F`, a real `c ≥ 0`, and the four hypotheses

1. `SymmetricOn D H` and `SymmetricOn D N`;
2. `quadForm N x ≥ 0` (`N ≥ 0` in the form sense);
3. `N + 1` **onto** `F` (`∀ f, ∃ x, N x + x = f`);
4. `|commForm H N x| ≤ c · quadForm N x`,

and concludes `EssentiallySelfAdjointOn D H`.  Two points decide the whole design:

* **There is no relative-bound *smallness* hypothesis.**  Hypothesis (1) already says `H`
  lives on `𝒟(N)`; "`H` is `N`-bounded" is only the informal way of saying it, with **any**
  finite constant.  So the criterion is *not* a perturbative small-coupling statement.
* **(3) is free for a positive self-adjoint `N`** (`(N+1)⁻¹` is bounded), and the project
  supplies it for the lifted comparisons by `dsCompOp_surj`
  (`BookProof.QgOuterFockFL`, module `BookProof.ChapterQgOuterFockFarisLavine`).  So the real
  work is (4): a commutator that does not out-grow `N`.

## 1. Three design rules

The Hamiltonians of the wave divide along three rules, and that is *why* they get three
different `N`s.

* **R1 — positivity.**  If the Hamiltonian is a **positive sum of squares**, it has a
  Friedrichs extension, and the criterion holds in its `c = 0` form with `N` *the realization
  itself*: the commutator vanishes identically (the `Comparison`/`esa_self` idiom, already
  used for the full Lagrangian Navier–Stokes and for Yang–Mills).
* **R2 — degree closure.**  If the one-particle symbol is a **finite combination of
  quadratic monomials**, take `N = dΓ(n) + 𝒩 + 1` with `n` a positive quadratic comparison.
  Since `[quadratic, quadratic]` is quadratic, `[H, N]` does **not** raise the degree, and (4)
  becomes a finite quadratic-form inequality — the `SqFamily` route
  (`ChapterSqSumOuterFamily`, comparison `N₁ = −Δ + ‖x‖²/4`, constants `flK = 3km/2 + 4ab`,
  `flc = km/2 + 2ab`, uniform in the particle number).
* **R3 — the wall inside `N`.**  A potential that is **not** polynomial of degree ≤ 2 (the
  exponential scalaron wall) cannot live in the perturbation; it is moved *into* `N`, which is
  the lifted Friedrichs extension of `−Δ + V` with `V` on the fibre.

## 2. Quantum gravity, the full Hamiltonian — the comparison stands (R2 + R3)

After the elimination `D_{μν}^i = i k_μ e_ν^i` the torsion is **linear** in the vielbein,
`T_{μν}^i = i(k_μ e_ν^i − k_ν e_μ^i)`, so the one-body operator stays **quadratic** and the
scalaron couples to the trace with the full exponential potential.  Candidate:

```
N_QG = ι( Friedrichs( −∂²_φ + φ²/4 + V(φ) + σ_a ) ),
```

the `ℓ²`-lift (`dsComparison`, `dsCompOp_surj`) of the fibre Friedrichs operator with the
**wall inside it**; the certificate is `qgFullModes` (`κ = 855 + |g|`, band `36`).  This is
exactly what `qgFull_esa_farisLavine` / `qgFull_esa_core_fl` already consume, so the
elimination changes **nothing** here: the candidate is in the tree.  *Obligation: none new.*

*Why the elimination is harmless:* the derivative content of the gravity model was always
carried by the momentum weight `i k_μ` (§"the torsion becomes linear in the auxiliaries"),
so removing the auxiliary `D` variables only removes degrees of freedom that `N_QG` never
touched.

## 3. Navier–Stokes, Lagrangian — positivity (R1)

The material model is a positive sum of squares (kinetic, viscous, and the exact Piola term
`cof(F)ᵀ∇q`), each parcel contributing `H_n = ½Σπ² + ½ΣΦ_r²`.  Candidate:

```
N_L = ι( Friedrichs( H_n^red ) )  = `lagRedOuterN_esa`,  c = 0
                                 (the existing `lagFullOuterN_esa` is the identification,
                                  §6.3/§6.4 — not the reduced object itself),
```

the lifted Friedrichs comparison already built.  Symmetry, positivity and `N + 1` onto are
fibrewise; the commutator vanishes because `N` **is** the realization of `H` (`c = 0`).
*Obligation:* confirm the Fourier elimination keeps the sum-of-squares structure — that the
eliminated Piola term is still a square of the same degree (it is quadratic in the
deformation-gradient variables, so this is plausible).  If it does not, fall back to R2 with
`n_L = (1 + A_ξ + P_a)²` (material oscillator + material-momentum multiplier), as in §4.

## 4. Navier–Stokes, Eulerian — the genuinely new case

The eliminated Eulerian one-body symbol is

```
h_E = h_visc + h_advect,   h_visc ∼ |k|² π^i u_i        (quadratic in (u,π), two momentum powers),
                           h_advect ∼ k_j π^i u_j u_i    (cubic   in (u,π), one momentum power).
```

Two candidates, and they are not equal.

**(a) The positive completion (R1) — preferred, and worked out in §5.**  Apply the Fourier
elimination **inside the squares**: the advection enters **squared**, as `½((k·u)u_i)²`, alongside
the viscous and gauge-fixing squares — the square of a reduced form is its **modulus** square, i.e.
the sum of the squares of its real and imaginary parts, each real-coefficient and hence a symmetric
square (§5.2).  So the Hamiltonian stays a positive sum of squares, the nonlinearity is kept **in
full** (the reduced Hamiltonian is quartic and interacting, as Navier–Stokes requires), and the
candidate is the lifted Friedrichs comparison with `c = 0`.  §5 gives the construction, the
four hypotheses with `c = 0`, and the two obligations (uniformity under the cutoff, and the
identification with the momentum-space operator).

**(b) The degree-matched oscillator (R2) — the literal cubic.**  If the bare cubic symbol is
kept, take

```
N_E = dΓ(n_E) + 𝒩 + 1,     n_E = (1 + A_u + P)²,
```

with `A_u = ½(−Δ_u + ‖u‖²)` the **field oscillator** (inner Fock space) and `P = |p|²` the
spatial-momentum multiplier.  Since `A_u` and `P` act on different variables they commute,
`A_u + P` is positive self-adjoint with compact resolvent, so `n_E` is positive self-adjoint
and `n_E + 1` is onto: hypotheses (2) and (3) hold, and `dΓ` preserves them.

* **The N-bound holds.**  A product of the field operators is controlled by `A_u^{deg/2}`
  (the `pairOp_commForm_le` calculus of namespace `BookProof.FockQuadratic`, module
  `ChapterFockQuadraticEsa`; the general `seriesOp_commForm_le` of `BookProof.OperatorSeries`),
  and the momentum powers by `P^{·}`.
  The mixed Young estimate `X^{3/2}Y^{1/2} ≤ ¾X² + ¼Y²` (`X = A_u`, `Y = P`) puts the
  cubic-with-one-momentum kernel and the quadratic-with-two-momentum kernel both under
  `(1 + A_u + P)²` — the **square**, not the first power, is the degree that matches a
  cubic-times-momentum symbol.
* **The commutator bound is the open problem.**  `[h_E, A_u]` is again cubic, but pairing it
  with the *square* makes `[h_E, n_E]` formally degree 5: it out-grows `n_E`.  The sharp form
  of this — checked symbolically in §9 (D2/D3/D4/D5) — is that the leading symbol
  `{σ_{h_E}, σ_{n}}` of the commutator is **non-zero and homogeneous of degree `ord(n) + 1`**
  (`q + 1` for a comparison of degree `q`), so a comparison of growth `q` can satisfy (4) for
  symbols only up to degree `d = 2`, never for `d = 3`.  In the QG case the closure holds
  because `[quadratic, quadratic]` is exactly quadratic (rule R2, `d = 2`); a **cubic symbol
  loses the degree closure**, and no function-of-the-oscillator comparison can restore it.

So (b) buys (2), (3) and the N-bound but **not** the commutator bound as it stands; closing it
needs a genuinely different device — a comparison built from `h_E²` on the finite-energy core,
or the observation that the cubic is a total derivative on the physical sector (which is what
pushes one back to (a)).  That is the honest residual of the whole wave.

### 4.1 Route (b) in full — and why the direct replacement has no comparison (a no-go)

It is worth doing (b) properly, because the failure is structural and should be recorded as
such, not as a missing estimate.

**The best candidate, and its exact failure.**  The natural move is to match the *order* of the
comparison to the Hamiltonian rather than exceed it:

```
n_E := (A_u + P)^{3/2} + 1      (order 3, matching the cubic),      N_E := dΓ(n_E) + 𝒩 + 1.
```

This buys the N-bound: `h_E = h_visc + h_advect` is dominated by `n_E` (both the
cubic-with-one-momentum and the quadratic-with-two-momentum kernel are `≲ n_E`), and `n_E` is
positive self-adjoint (a function of the commuting positive `A_u + P`), so `n_E + 1` is onto.
What fails is the **commutator**.  With `𝒩_u := A_u − m/2` the field number, `h_E` has degree
`d = 3` and `n_E` degree `q = 3`, and the commutator form obeys

```
|⟨φ, [h_E, n_E]φ⟩| ≲ ‖𝒩_u^{(q−1)/2} h_E φ‖ · ‖𝒩_u^{q/2} φ‖ ≲ ‖𝒩_u^{(q+d−1)/2} φ‖ · ‖𝒩_u^{q/2} φ‖ ,
```

which is `≤ c‖𝒩_u^{q/2}φ‖²` **only if** `q + d − 1 ≤ q`, i.e. `d ≤ 1` in this bookkeeping — and
`d = 2` (which is what QG uses, and where the criterion *does* close, §1 rule R2) already
sits at the edge, so the exponents above are lossy by one power and are stated here only as a
heuristic.  The load-bearing version is the symbol computation of §9: the commutator's
leading symbol has degree `ord(n) + 1` and is non-zero, and a comparison of degree `q`
therefore cannot dominate a symbol of degree `3` — the failure is *independent of the power
chosen*: raising `q` cannot help, since both sides carry `q`.

**The no-go.**  The same computation in the (pseudo)differential language is decisive.  On the
one-particle space `h_E` has **order 3** with principal symbol
`σ_{h_E}(u, ξ, k) = (ξ·u)(u·k + …)`, a product of two indefinite linear forms.  For the N-bound
any comparison `n` must have order `e ≥ 3`.  The leading symbol of `[h_E, n]` is (up to `−i`)
the Poisson bracket `{σ_{h_E}, σ_n}`, and §9 (D2–D5) evaluates it: it is **non-zero** (the
principal symbols do not Poisson-commute) and **homogeneous of degree `ord(h_E) + ord(n) − 2 =
e + 1`** in the total-degree (Weyl) register the note uses.  With the pseudodifferential order
convention (`x = u`, `ξ` the field momentum, the mode `k` a parameter) the leading bracket is
the order-`e` object instead; either way the comparison is out-grown by exactly one degree in
the register that matters here.  Hence:

> **Proposition (no-go for the direct replacement).**  *No classical (pseudo)differential
> comparison operator `n` of order `≥ 3` satisfies both the N-bound and the commutator bound for
> the cubic `h_E`: the commutator always has order at least `ord(n) + 1`.*

The only way to make `[h_E, n]` vanish is to take `n = f(h_E)`, a function of `h_E` itself —
which **presupposes** that `h_E` is essentially self-adjoint, exactly the conclusion FL is meant
to produce.  The project's own counterexample
`not_farisLavine_criterion_of_relative_bound` is the sharpest instance of this circularity:
`N = H` satisfies both inequalities and proves nothing.

**The two escape hatches, and why neither is (b).**

1. **The cutoff.**  On the finite energy/momentum cutoff `|k| ≤ Λ` the one-body operator is
   *bounded*, so `n = 1 + h_E²` is bounded, positive and commutes with `h_E` (`c = 0`) — FL
   holds, but trivially, since a bounded symmetric operator is already self-adjoint.  The point
   is that `‖n‖` **grows with the cutoff** (`‖h_E‖ ≈ Λ³` there), so this is not a cutoff-uniform
   certificate and cannot survive removal of the cutoff.  This is exactly why the plan says
   "restricted to a finite energy/momentum cutoff".
2. **The positive completion.**  Keeping the constraint squared makes the one-particle symbol
   *quartic* and positive, and the comparison is then the Friedrichs realization itself with a
   vanishing commutator — §5.  But that is route (a), not (b).

**Conclusion.**  Route (b) — the literal one-body cubic — has **no** comparison operator `N` in
the class the criterion can use, and the obstruction is order counting, not a missing estimate.
The direct replacement is therefore not merely harder than route (a): it is *unavailable*, and §5
is the only route that defines the eliminated Eulerian Hamiltonian as a self-adjoint operator
uniformly in the cutoff.

## 5. Route (a) worked out — the Eulerian comparison by positive completion

This is the construction the wave commits to.  The point is that the elimination is applied
**inside the squares of every surviving form**, each of those squares being the *modulus* square of
a complex reduced form, i.e. the sum of the squares of its real and imaginary parts (§5.2) — so the
advection is squared along with the pressure–viscous symbol — and **positivity** — not a degree
estimate — is what supplies `N_E`.

### 5.1 The elimination as a substitution on the constraint forms

Keep the constraint-squared form of the sector Hamiltonian, already proved symmetric and
non-negative (`nsSectorHam_quadForm_nonneg`),

```
H_n = ½ Σ_m π_m² + ½ Σ_r Φ_r² ,      Φ_r the 19 constraint polynomials of the parcel,
```

and eliminate the coordinates that *represent derivatives* by the momentum-space substitution

```
σ(u_{i,j}) = i k_j u_i ,     σ(w_i) = −|k|² u_i ,     σ(y_j) = 0
```

(the mode `k` ranges over the finite-energy cutoff `|k| ≤ Λ` of Ch. 2 of `book.tex`).  Write
`Φ^E_r := σ(Φ_r)`; on the six velocity/pressure coordinates `(u_i, q_i)` per parcel these are

* the **residual** `R_i ⇒ i Σ_j k_j u_j u_i + q_i + ν|k|² u_i` — *quadratic* in `u` (the exact
  `u·∇u`) plus the linear pressure and viscous terms: the image of the nonlinearity;
* the **divergence** `Σ_j u_{j,j} ⇒ i Σ_j k_j u_j` — linear;
* the **gauge forms** — linear in the surviving coordinates after substitution.

### 5.2 The reduced Hamiltonian is a sum of squares — the honest one

```
H_n^red := ½ Σ_m π_m² + ½ Σ_r |σ(Φ_r)|² ,      H^red on ⊕ₙ L²(ℝ^{6n}),
```

where the sum runs over **every** constraint form of the sector — the three residuals, the
incompressibility, the derivative-gauge forms and the viscous-gauge forms — and `σ(Φ_r)` is the
form's reduced, complex image under the substitution.

> **Plan of record (2026‑09‑17b) — the square of a reduced form is its *modulus* square.**
> A gauge-fixing energy is the square of a **real** functional, so for each form
> `|σ(Φ_r)|² = (Re σ(Φ_r))² + (Im σ(Φ_r))²`, and both brackets have **real** coefficients, so each
> quantizes (via `weylOp` + `RealCoeff`) to a Weyl-ordered square of a **symmetric** operator.  For
> the residual, `Re σ(R_i) = q_i + ν|k|² u_i = fourierVisc` and `Im σ(R_i) = (k·u) u_i =
> fourierAdvect`, so **the nonlinear advection enters squared**, `½ ((k·u)u_i)²`, exactly as in the
> manuscript: this is the mainstream Navier–Stokes nonlinearity, and the reduced Hamiltonian is
> therefore **quartic (interacting)** — like the full sector, and unlike the real-symbol-only
> truncation.  The eliminated incompressibility contributes `½ (k·u)²` (`fourierDiv`), and `σ` sends
> the `y`-gauge forms to `0`, so those drop out rather than being dropped by hand.
>
> **What the skew observation does and does not say.**  `mulOp (i (k·u) u_i) = i·T` with `T`
> symmetric is skew-adjoint and `(iT)² = −T² ≤ 0`; that is a statement about the operator appearing
> *in the equation*, not about an energy.  With `L = mulOp σ(R_i) = iT + S` (`S = mulOp fourierVisc`),
> the energy is `L*L = T² + S² + i[S,T]`: the first two terms are the positive squares and the third
> is skew, so it contributes **nothing** to the quadratic form (`coreRep_quadForm_skew_zero`).  The
> modulus reading and the sum-of-squares reading therefore have the *same* quadratic form; what is
> neither symmetric nor positive is the **coefficientwise** square
> `σ(R_i)² = −a² + 2i a r + r²`, which is the object the earlier “the advection cannot be a square”
> note used by mistake.
>
> **Consequence for the comparison.**  `N` is free — positive, co-final with `H`, `N + 1` onto,
> commutator bound — so take `N_E = ι(Friedrichs(H_n^red))` with the honest `H_n^red` above: `N_E`
> then *contains* the advection square by construction, the commutator vanishes (`c = 0`) and **no
> commutator estimate is owed** (§5.3's four hypotheses are already the `c = 0` ones).  What *is*
> pending is a formalization delta, not analysis: the landed `redHam = weylOp (redPiN n) (redFieldN nu k n)`
> has `redFieldN` over the three **real** residual forms only, i.e. the Gaussian part of the honest
> Hamiltonian, and it must be extended to the real and imaginary parts of every surviving form
> (`realCoeff_fourierAdvect` is already proved, and `redHam_quadForm_nonneg` /
> `redHam_friedrichs_extension` are generic in the field family, so they re-elaborate unchanged).

### 5.3 The comparison `N_E`, and the four hypotheses with `c = 0`

```
N_E := ι( Friedrichs( H_n^red ) ) ,
```

the `ℓ²`-lift (`dsComparison`) of the fibrewise Friedrichs extension of `H_n^red` — the exact
pattern of `nsPosSym` / `nsFried` / `nsOuterComparison`, with the reduced `PosSymOp`.  All four
hypotheses hold **with `c = 0`**, by the same steps as `nsFullOuterN_esa`:

1. `H^red` symmetric on the finite-parcel core — the reduced analogue of `nsFockCore_dense`,
   i.e. the lifted Gauss core `dsCore (fun n => polyGaussCore (d := n * 6))` of the six
   surviving coordinates per parcel (the cited `nsFockCore_dense` is the **21**-coordinate
   core of `ChapterNavierStokesFullEulerianFock`, so it is the pattern, not the object);
2. `N_E ≥ 0` (the `pos` field of `PosSymOp`, i.e. `∀ x, 0 ≤ quadForm op x` — there is no
   separate `quadForm_nonneg` declaration on `PosSymOp`);
3. `N_E + 1` onto (`dsCompOp_surj`, fibrewise `friedrichsComparison`);
4. `commForm H^red N_E x = 0` on the core — `N_E` agrees with `H^red` there
   (`nsFried_op_core`), so the commutator vanishes.

`essentiallySelfAdjointOn_of_farisLavine` then gives **`nsRedOuterN_esa`**: the eliminated
Eulerian Hamiltonian is essentially self-adjoint on the domain of its lifted Friedrichs
comparison.  No positive `N` of oscillator type is needed, and the cubic's lost degree closure
(§4(b)) is simply irrelevant.

### 5.4 The two genuinely new obligations

1. **Uniformity (the `ℓ²`-lift).**  The reduced forms carry the mode coefficients `i k_j` and
   `−|k|²`; after the cutoff `|k| ≤ Λ` they are bounded by `O(Λ)`, and the relative bound
   `‖H_n x‖ ≤ K ‖(N_n + 1) x‖` holds with `K` **uniform in `n`** by the parcel-locality of the
   reduced forms — the analogue of the existing Schur data (`row_le`/`col_le`, independent of
   the parcel number).  Without the cutoff the coefficients are unbounded and the lift is not
   uniform, which is why the cutoff is load-bearing rather than cosmetic.
2. **The identification.**  That `H^red` *is* the momentum-space eliminated Hamiltonian of the
   strategy — the Navier–Stokes analogue of `torsion_eq_exact_of_gauge_fixed` /
   `gaugeReduce_extTorsionCoef`: on the derivative-gauge surface the extended forms equal the
   reduced ones, so the two constructions define the same operator.  **Shortcut:** the extended
   Hamiltonian already has a positive self-adjoint realization (`nsFullOuterN_esa`), and the
   elimination is the restriction to the surviving (gauge-fixed) modes, which preserves ESA by
   the restriction principle `restrict_essentiallySelfAdjointOn` / `gaugeFixedSubset_esa`.  So
   (2) can be discharged by restriction rather than by re-proving the lift.

### 5.5 Staged Lean plan — DONE 2026‑09‑17

All of the stages below are landed in `BookProof/ChapterNsFourierElimination.lean` (namespace
`BookProof.NsFullEuler`), `sorry`-free and `axiom`-free; the book chapter that narrates them is
`Book/FourierElimination.lean`.  The names are the ones the plan and the offline specialist should
cite:

1. **DONE** — `nsElimCoord`, `liftParcel`, `nsElimHom` (the substitution `σ` as a ring map), with
   `nsElimHom_X_u/_d/_w/_q/_y`; the reduced forms `Φ^E_r` are `fourierAdvect` (the real symbol
   `(k·u) u_i`), `fourierDiv` (`i (k·u)`), `fourierVisc` (`q_i + ν|k|² u_i`), and the two
   identities are `nsElimSubst_resPoly` (quadratic residual) and `nsElimSubst_divPoly` (linear
   divergence), with the degree bookkeeping split over `nsElimSubst_advect`, `_pressure`, `_viscous`.
2. **DONE** — the reduced sector Hamiltonian is `redHam nu k n = weylOp (redPiN n) (redFieldN nu k n)`,
   with `redHam_symmetricOn` and `redHam_quadForm_nonneg` (the names `nsRedSectorHam_*` of this
   section were the plan's provisional handles; `redVisc`/`redVisc_eq_liftParcel`/`realCoeff_redVisc`
   are *part* of the reduced forms that go inside the squares — the squares are the modulus squares
   of **all** the surviving forms (§5.2), so `redFieldN` covering only `redVisc` is the pending
   delta recorded as stage 8 below).
3. **DONE** — `redPosSym`, `redFried` (the reduced `PosSymOp` and its `friedrichsComparison` on
   `polyGaussCore_dense`), plus `polyGaussCore_le_redFriedDom` and `redFried_op_core`.
4. **DONE** — the lift: `nsRedFockCore`, `nsRedFockCore_dense`, `nsRedFullFockHam`,
   `nsRedFullFockHam_symmetricOn`, `nsRedFullFockHam_quadForm_nonneg`,
   `nsRedFullFock_friedrichs_extension`, `nsRedFullFockHam_sector`,
   `nsRedFullFockHam_number_conserving`; and the comparison `nsRedOuterComparison` with
   `nsRedOuterN_apply`, `nsRedFockCore_le_friedDom`, **`nsRedFullOuterN_esa`** (the ESA statement
   this section named as its target) and `nsRedFullOuterN_isPositiveSelfAdjointExtension`
   (the `N_E`-extends-`H^red` statement).
4. `nsRedOuterComparison`, `nsRedOuterN_apply` — the `ℓ²`-lift (`dsComparison`).
5. **`nsRedOuterN_esa`** — the headline, by `essentiallySelfAdjointOn_of_farisLavine` with
   `c = 0`, plus `nsRedOuterN_isPositiveSelfAdjointExtension` (mirror
   `nsFullOuterN_isPositiveSelfAdjointExtension`).
6. `nsRed_eq_momentumForm` — the identification of §5.4(2), via
   `restrict_essentiallySelfAdjointOn` / `gaugeFixedSubset_esa` on the gauge-fixing surface.
7. Axiom audit in `ChapterRoadmapAudit.lean`; the plan and this note updated.
8. **PENDING (2026‑09‑17b) — the honest reduced Hamiltonian.**  Extend `redFieldN` from the three
   *real* residual forms to the **real and imaginary parts of every surviving substituted form**:
   the residuals (`fourierVisc` *and* `fourierAdvect`), the incompressibility (`fourierDiv`), and
   the substituted derivative-gauge and viscous-gauge forms; the `y`-gauge forms need no entry
   because `σ` sends them to `0`.  This is what makes `redHam` the modulus-square Hamiltonian of
   §5.2 — quartic, interacting, with the advection square **inside** the positive operator whose
   Friedrichs extension is `N_E` — instead of the real-symbol-only truncation that is landed today.
   `weylOp` + `RealCoeff` cover the new forms (`realCoeff_fourierAdvect` is already proved), and the
   §5.3–§5.5 chain is generic in the field family, so it re-elaborates unchanged.

## 6. The Lagrangian determinant — `detPoly_pos` and the logarithmic volume square

The Lagrangian model carries one structural piece the Eulerian one lacks: the volume constraint
is built from `det F`, a **cubic** polynomial in the deformation gradient (`detPoly`, expanded
along the first row from the cofactors `cofPoly`).  `det F` **is** `detPoly` (§9 A1), and the
constraint *form* is `volumePoly := detPoly − 1`; it is that form which enters the energy
squared, `½ Σ_r Φ_r² ⊇ ½ (det F − 1)²`.  The elimination `F_{ij} ⇒ i ℓ_j ξ_i` (`ℓ` the material
wave-vector — written `a` in an earlier draft, which collides with the acceleration coordinate
`a_i` of `lagResPoly`) keeps `detPoly` cubic as a *polynomial in the reduced coordinates*, so the
reduced constraint square is sextic — still a square, hence `≥ 0`.

**Correction (2026-09-17): that degree statement is not evidence that the elimination works.**  At
each single mode the substitution makes `F` the **rank-one** matrix `ℓ ⊗ ξ`, and in three
dimensions every `2 × 2` minor of a rank-one matrix vanishes.  Hence `cof(F) = 0`, so the Piola
pressure term `Σ_j cof(F)_{ji} q_j` — the entire pressure coupling of the material momentum
equation `lagResPoly` — is annihilated by the elimination; and `det F = 0` for the same reason, so
the eliminated volume **form** is the constant `volumePoly ↦ −1`, whose square is `1`.  The `B1–B3`
rows of §9 are degree statements about `cofPoly`, `detPoly` and `volumePoly²` *before* the
substitution, and after it they are satisfied **trivially by the zero polynomial**; they cannot
discriminate.  The checks that do discriminate are `B4a–B4d` and `B5`/`B5b` of §9, which
machine-verify the degeneracy.  Consequently **the mode-wise Fourier elimination must not be
applied to the deformation gradient**: the determinant has to be carried as an independent scalar
mode, which is exactly what the logarithmic treatment below does — so §6.2 is not an alternative
to the elimination of `F`, it *replaces* it.  What does survive is the elimination of the velocity
gradient and of the viscous coordinate, `V_{ij} → i ℓ_j v_i` and `S_i → −|ℓ|² v_i`, leaving the
material momentum equation `σ(R_i) = a_i + |ℓ|² v_i` with no pressure term at all (see
`CONSOLIDATED_PLAN.md` item 6 for the corresponding Lean handoff).

Two facts make the determinant term a *good* constraint rather than merely a positive one.

### 6.1 `detPoly_pos` — the determinant is positive on the physical sector

`detPoly` is the `3 × 3` determinant of the deformation-gradient block.  A deformation gradient
of a non-degenerate, orientation-preserving flow has **positive** determinant, and in the model
this is an *open* condition, provable with no global geometry:

* **Neighbourhood of the identity (the main lemma).**  For `A : Matrix (Fin 3) (Fin 3) ℝ` with
  operator norm `‖A‖ < 1`, `0 < det (1 + A)`.  Proof: the smallest singular value obeys
  `σ_min (1 + A) ≥ 1 − ‖A‖ > 0`, so `|det (1 + A)| = ∏ σ_i ≥ (1 − ‖A‖)³ > 0`; and the *sign*
  is positive because `det` is continuous, `det 1 = 1 > 0`, and the ball `‖A‖ < 1` is connected.
  The polynomial ingredient — `det (1 + A) = 1 + tr A + m₂(A) + det A`, with `m₂` the sum of
  the principal `2 × 2` minors, hence constant term `1` — is checked symbolically in §9 (A6),
  and its isotropic section is `det (ε · 1) = ε³` (A7).
* **The statement on the polynomial itself.**  `detPoly_pos` is the version of the lemma for
  `detPoly`, i.e. on the deformation-gradient block: `‖F − 1‖ < 1 ⇒ 0 < detPoly F`, with the
  abstract matrix lemma above as its proof input (take `A = F − 1`).  It is this form, not the
  abstraction, that makes `Adm` non-empty and identifies the physical configurations.
* **Corroboration on the isotropic line.**  `detPoly_eval_testPt` already gives `det F = t³` at
  `F = t·I`, so `det F > 0` for `t > 0` (`detPoly_pos_isotropic`), with `volumePoly = t³ − 1`.
* **The admissible sector.**  Define `Adm p := {configurations : 0 < detPoly p}` — the
  orientation-preserving block, an open set containing the identity.  Every statement below
  lives on `Adm`, and `detPoly_pos` is exactly the lemma that `Adm` is non-empty and contains
  the physical configurations.

### 6.2 The logarithmic volume square

On `Adm` the logarithm of the determinant is a **real** smooth function,

```
volLog       := Real.log (detPoly p) ,        volLogSquare := (volLog)² ,
```

and this is the right form of the incompressibility constraint.  Three properties matter:

1. **Well defined.**  `det F > 0` on `Adm` (§6.1) is exactly what makes `log det F ∈ ℝ`; the
   constraint is `log det F = 0 ⟺ det F = 1`.
2. **Positive, and positive definite.**  `volLogSquare ≥ 0`, with equality iff `det F = 1`
   (`volLogSquare_eq_zero_iff`).  So the volume term is a **square of a real function**, like
   every other constraint — no degree argument is needed.
3. **Self-adjoint as a multiplication operator, with bounded gradient on `Adm`.**  A real
   non-negative continuous multiplication operator is self-adjoint on its maximal domain, so
   `volLogSquare` needs no boundary condition at `det F = 0`.  Its gradient is the classical
   Jacobi identity `∇ log det F = F^{−T}`, i.e. `cofPoly / detPoly` entrywise (`grad_logDet`),
   **finite precisely where `det F > 0`** — the reason the log form is better conditioned than
   `(det F − 1)²`: it controls the non-degeneracy of `F` at the same time as the volume.

**Equivalence with the polynomial square.**  On any compact `K ⊂ Adm` with
`det F ∈ [a, b]`, `0 < a ≤ b < ∞`, the two constraints are comparable:
`c₁ (volumePoly)² ≤ (log det F)² ≤ c₂ (volumePoly)²` (`volLogSquare_le_mul_volumePoly`, with
`volumePoly = det F − 1`).  So the
log square may replace `(det F − 1)²` in the energy without changing positivity or the
Faris–Lavine data, and it is the form invariant under a volume-preserving rescaling of the
time variable, which the polynomial form is not.

### 6.3 How it feeds the comparison

With `volLogSquare` a positive multiplication operator, the reduced Lagrangian sector operator

```
H_n^red = ½ Σ π² + ½ (volLogSquare) + ½ Σ (other constraint forms)²
```

is a **positive sum of squares** on `Adm`, hence symmetric on the Gauss–polynomial core and
bounded below by `0`.  Therefore

* its **Friedrichs extension exists unconditionally** by
  `FriedrichsExtension.friedrichs_extension_exists` — the theorem carrying *no* boundedness
  hypothesis — so the facts that `detPoly` is cubic and `volLog` is not polynomial at all cost
  nothing;
* the comparison is `N_L = lagRedOuterN_esa`, built from this reduced `PosSymOp` by the same
  `dsComparison` lift, with the criterion in its `c = 0` form; the *existing* full comparison
  `lagOuterComparison` / `lagFullOuterN_esa` (`ChapterNavierStokesFullLagrangianFock`) is then
  the identification of the two constructions on the `Adm`-gauge-fixed surface (§6.4).  So
  **`N_L` needs no redesign under the elimination** either — the naming above is the §3/§7
  agreement: the certificate is the reduced object, the existing lemma is the bridge.

This is the precise content of "easy because the determinant is positive": positivity of
`det F` turns the cubic constraint into a square of a real function, and a square is the one
thing `friedrichs_extension_exists` consumes.

### 6.4 Staged Lean plan

1. `detPoly_pos` — `‖A‖ < 1 ⇒ 0 < det (1 + A)` (singular-value bound); `detPoly_pos_isotropic`
   (`t > 0 ⇒ detPoly > 0`) from `detPoly_eval_testPt`.
2. `Adm`, `Adm_nonempty`, `mem_Adm_iff` — the open orientation-preserving sector.
3. `volLog`, `volLogSquare`, `volLogSquare_nonneg`, `volLogSquare_eq_zero_iff`.
4. `volLogSquare_isSelfAdjointOn` (real multiplication operator), `grad_logDet`
   (`∇ log det F = cofPoly / detPoly`).
5. `volLogSquare_le_mul_volumePoly` — the comparability constants on a compact sector.
6. `lagRedPosSym`, `lagRedFried`, `lagRedOuterComparison`, **`lagRedOuterN_esa`** — mirroring the
   Eulerian §5.5, with `lagFullOuterN_esa` as the fallback identification (`Adm`-restriction
   via `restrict_essentiallySelfAdjointOn`).

**Status of the stage plan (2026-09-17) — items 1–6 above are *not* done; the file is a handoff
scaffold.**  `BookProof/ChapterNsLagrangianFourierElimination.lean` (namespace
`BookProof.NsLagFourier`, unimported, in no Lake target) contains, `sorry`-free: the substitution
`lagElimCoord` / `lagLift` / `lagElimHom` and its coordinate values for `ξ_i`, `v_i`, `a_i`,
`q_i`, `y_j`, `S_i` (green), the rank-one degeneracy lemmas of §6 above and
`lagElimSubst_lagResPoly` (written, not yet elaborating because two `Fin 36`-index lemmas,
`lagElimCoord_fIdx` and `lagElimCoord_vgIdx`, exceed the heartbeat budget — proof engineering,
not a mathematical gap).  Items 1–5 of this stage plan (the `detPoly_pos` / `Adm` / `volLog`
chain) are untouched.  Both blocks are Lean work for the specialist; nothing in them is assumed
anywhere in the tree.

## 7. Summary

| Hamiltonian | rule | candidate `N` | obligation |
| :-- | :-- | :-- | :-- |
| QG, full | R2 + R3 | `ι(Friedrichs(−∂²_φ + φ²/4 + V(φ) + σ_a))`, wall inside | none new — `qgFull_esa_farisLavine` |
| NS, Lagrangian | R1 | `ι(Friedrichs(H_n^red))` = `lagRedOuterN_esa`, `c = 0` | **§6.1** `detPoly_pos`; **§6.2** the log square; Friedrichs unconditional |
| NS, Eulerian (squared) | R1 | `ι(Friedrichs(H_n^red))` = `nsRedOuterN_esa`, `c = 0` | **§5.4**: cutoff for uniformity; identification by restriction |
| NS, Eulerian (bare cubic) | — | `dΓ((A_u + P)^{3/2}) + 𝒩 + 1` | **§4.1 no-go** — N-bound ✔ but commutator out-grows `n`; no comparison exists, use §5 |

The one required `N` that is new mathematics is the positive comparison for the Eulerian
Hamiltonian; the other two are, respectively, already proved and already built.

## 8. Why one `N` per Hamiltonian, and not a uniform one

A single `N` across all three is not available, and the reason is structural: `N` must be
*co-final with the Hamiltonian* in the sense of (4), and the three Hamiltonians sit at
different degrees.

* The gravity one-body operator is **quadratic** with a non-polynomial potential, so its `N`
  must carry the wall (R3) while staying degree-two in the kinetic part (R2).
* The Lagrangian operator is **bounded below**, so its `N` is its own Friedrichs realization
  (R1) — the cheapest possible certificate, and it would be wasteful (and weaker) to force it
  into the oscillator form.
*The Eulerian operator is **cubic** in the literal momentum-space reading, which is exactly
the case neither R1 nor R2 covers — and §4.1 shows that reading has *no* comparison at all;
hence the split into (a) and (b) above, and the choice of (a).

Trying to use one `N` (for instance the gravity-style lifted Friedrichs extension for all
three) either fails positivity (Eulerian cubic is unbounded below) or fails (4) (the wall
comparison does not control a cubic advection).  This is the content of the leading wave's
phrase "one different `N` for each requested version of the Hamiltonian".

## 9. Symbolic verification — `DESIGN_COMPARISON_N_20260915.cdb`

Every polynomial and degree statement above is checked with the project's Cadabra2 module
conventions (the `../unfer/docs/*.cdb` modules), in the companion module of the same stem:

```
nix build "github:NixOS/nixpkgs/b5aa0fbd538984f6e3d201be0005b4463d8b09f8#cadabra2"
/nix/store/…-cadabra2-2.5.14-p1/bin/cadabra2-cli -q -n DESIGN_COMPARISON_N_20260915.cdb
```

(the pinned revision and CLI invocation are the ones `../unfer/docs/VERIFY_QG_DENSITIZED.md`
names; the three QG `docs/*.cdb` modules of that repository also run clean on this engine, so
the QG facts of §2 are the repository's own).

| check | statement | result |
| :-- | :-- | :-- |
| A1 | `detPoly` (first-row cofactor expansion) `= det F` (Leibniz) | `0` |
| A2 | `F · cof(F)ᵀ = det(F) · 1` (so `cofPoly` is the signed cofactor matrix) | `0` |
| A3 | `det(t G) = t³ det(G)` — cubic | `0` |
| A4 | `det(t · 1) = t³` (`detPoly_eval_testPt`) | `t³` |
| A5 | `volumePoly(t · 1) = t³ − 1` | `t³ − 1` |
| A6 | `det(1 + A) = 1 + tr A + m₂(A) + det A` (§6.1's ingredient) | `0` |
| A7 | `A = −(1 − ε)1 ⇒ det(1 + A) = ε³ > 0` (sharpness) | `ε³` |
| B1 | Piola F-part `Σ_j cof(F)_{j0} q_j` quadratic in `ξ` after `F_{ij} ⇒ i ℓ_j ξ_i` | `0` (trivial: the substituted object is zero, see B4) |
| B2 | `det F` cubic in `ξ` after the same substitution | `0` (trivial, see B4d) |
| B3 | `(det F − 1)²` sextic in `ξ` | `0` (trivial, see B5b) |
| B4a–B4c | every `2 × 2` minor of `F = i ℓ ⊗ ξ` vanishes (`cof F = 0`) | `0` |
| B4d | `det F = 0` at `F = i ℓ ⊗ ξ` (rank one in `d = 3`) | `0` |
| B5 | `volumePoly = det F − 1 ↦ −1` at the substitution | `−1` |
| B5b | hence `(volumePoly)² ↦ 1` | `0` |
| C1–C2 | Eulerian `R_i ⇒ i (k·u) u_i + q_i + ν|k|² u_i` | identity |
| C3 | the advection `Σ_j u_j u_{i,j}` is quadratic in `u` | `0` |
| C4–C5 | divergence `Σ_j u_{j,j} ⇒ i (k·u)`, linear | identity |
| D1 | `∂σ_h/∂ξ_i = u_i (u·k)`, `∂σ_h/∂u_i = ξ_i (u·k) + (ξ·u) k_i` | explicit |
| D2, D4 | `{σ_h, σ_n}` **non-zero** for `q = 2, 4` | non-zero |
| **D3, D5** | `{σ_h, σ_n}` homogeneous of **degree `q + 1`** (`8·b(1) = b(2)`, `32·b(1) = b(2)`) | `0` |
| E1 | momentum conservation of the convolution: `p − (k + q) = 0` (`p = k + q`) | `0` |
| E2 | the transfer weight `q_j` is **linear** in `q` (`2·q(1) − q(2) = 0`) | `0` |
| E3 | the advection integrand `q_j Û_j Û_i` has **degree 3** (`8·advI(1) − advI(2) = 0`) | `0` |

B4a–B5b are the correction recorded in §6 (2026-09-17): the Lagrangian substitution is
**degenerate** — it makes the deformation gradient rank one, so the cofactor (and with it the
whole Piola pressure coupling) is annihilated and the volume constraint collapses to a constant.
B1–B3, being degree statements, are satisfied trivially in this situation and were therefore
misleading on their own; this is why the Lagrangian route carries `det F` as an independent scalar
mode (§6.2) instead of eliminating it.

D3 and D5 are the correction recorded in §4/§4.1: the commutator gains **one** degree over the
comparison (degree `q + 1`, not the `q + 2` of an unqualified `ord h + ord n − 1`), which is
exactly what makes the quadratic closure of rule R2 work and the cubic case fail.

E1–E3 are the convolution bookkeeping of the momentum-space advection
`ℱ[u_j ∂_j u_i](Q) = (i/(2π)^{d/2}) ∫ q_j Û_j(Q − q) Û_i(q) dq` (momentum conservation, linearity
of the transfer weight, degree 3 of the integrand), and they are the same three checks that the
shared module `../unfer/docs/ns_qg_fourier_elimination.cdb` carries; the copy in this repository
(`DESIGN_COMPARISON_N_20260915.cdb`, which also carries A1–A7, B1–B5b, C1–C5, D1–D6) is the one that
matters offline.  **No reader of this repository needs the `../unfer/` copy or Cadabra2 itself**: the
results of every check are the table above, and the *Lean* side of each identity of §5–§6 is a named
theorem of `BookProof/` (see §5.5).
