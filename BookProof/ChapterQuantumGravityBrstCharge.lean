import BookProof.ChapterQuantumGravityBrstCharge.Part1
import BookProof.ChapterQuantumGravityBrstCharge.Part2

/-!
# The BRST charge of the 3D gauge-fixed gravity Hamiltonian: ghosts on `ℤ₂¹⁹` and nilpotency

`CONSOLIDATED_PLAN.md` §10.6.2 item 4 (and `PLAN_LEAN_SPECIALIST_QG_FLOW.md` **Part F**,
items F.6 and F.7) asks for the manuscript's BRST charge `G` — the diffeomorphism, local
Lorentz and translation constraints dressed with the `ℤ₂¹⁹` ghosts — and for its
nilpotency, on the field space of `BookProof/ChapterQuantumGravity3DGauge.lean`.

## What is proved

**The abstract theorem (the general non-abelian BRST charge).**  In any ring that is an
`ℝ`-algebra, for ghost operators satisfying the canonical anticommutation relations
(`BookProof.BRSTNilpotent.GhostCAR`) and constraints `G_a` that commute with the ghosts and
close into a Lie algebra with real structure constants `f`,

```
Ω = Σ_a G_a χ_a − ½ Σ_{a,b,e} f_{abe} χ_a χ_b β_e
```

satisfies **`brst_full_nilpotent`**: `Ω² = 0`.  This is the full charge, not only its cubic
ghost part: `BookProof.ChapterBRSTNilpotent.brst_charge_nilpotent` handles the cubic square
(where the Jacobi identity enters), `glin_sq` computes the square of the constraint part as
half the ghost-contracted constraint algebra, and `glin_mul_Q_add_Q_mul_glin` shows that the
cross terms produce exactly the opposite quantity — the classical cancellation that fixes
the coefficient `−½`.  Nilpotency of the *abelian* charge (`brst_abelian_nilpotent`) is the
special case `f = 0`, and needs no Jacobi identity.

**The ghost sector on `ℤ₂¹⁹` (F.7).**  The `19` diffeomorphism ghosts are realized on the
fermionic Fock space `ghostSpace = Λ(ℂ¹⁹)` (the exterior algebra — the `ℤ₂¹⁹` occupation
space), with `ghostCre a` the exterior multiplication by the `a`-th basis vector and
`ghostAnn a` the contraction against the `a`-th coordinate functional.  `ghost_car` is the
canonical anticommutation relations `{ψ_a, ψ†_b} = δ_{ab}`, `{ψ_a, ψ_b} = 0`,
`{ψ†_a, ψ†_b} = 0` in the `GhostCAR` form.

**The graded field-space (F.6).**  `QGState = ℂ[x₀,…,x₈₃] ⊗ Λ(ℂ¹⁹)` is the
Gauss–polynomial core of `L²(ℝ⁸⁴)` tensored with the ghost sector; `bosOp` and `ghostOp`
embed the operators of the two factors, `bosOp_ghostOp_comm` records that they commute, and
`qgGhostCar` transports the CAR to the graded space.

**The constraints.**  `elemGen j k` is the first-order operator `x_j ∂_k` on the
Gauss-weighted polynomial core and `linGen M = Σ_{j,k} M_{jk} x_j ∂_k` the generator of the
linear change `M` of the field coordinates — the form the diffeomorphism, Lorentz and
translation constraints take on the field space.  `elemGen_bracket` and `linGen_bracket`
prove that these generators **close into the matrix Lie algebra**:
`[linGen M, linGen N] = linGen (MN − NM)`.

**The BRST charge and its nilpotency (F.6).**  `qgBRST M f` is the charge built from a
family `M : Fin 19 → Matrix (Fin 84) (Fin 84) ℝ` of constraint generators, and
**`qgBRST_nilpotent`** proves `Ω² = 0` whenever the family closes with real structure
constants satisfying the Jacobi identity.  `qgBRST_abelian_nilpotent` is the
commuting-family instance, and `affMat`/`affF`/`affMat_close`/`affF_jacobi`/
`affBRST_nilpotent` a concrete **non-abelian** instance — the affine algebra `aff(1)`,
`[H, E] = E`, acting on the first two field coordinates, with `affMat_non_abelian`
recording that the two generators really fail to commute — so the construction is not
vacuous.

## Honest boundary

The charge is built on the *algebraic* graded core `ℂ[x] ⊗ Λ(ℂ¹⁹)` (polynomials times the
Gaussian, tensored with the finite ghost sector), which is the dense domain on which the
field-space Hamiltonian of `ChapterQuantumGravity3DGauge` is defined; no bounded extension
to the completed Hilbert space is claimed, and the reduction of the *dynamics* to BRST
cohomology is the separate `BookProof/ChapterBrstReducedTransfer.lean` (which assumes a
bounded charge).  The constraint family is data: the theorem says that *whenever* the
generators close with real structure constants obeying Jacobi, the charge is nilpotent, and
the `so(3)` instance exhibits a genuinely non-abelian family.  No mass gap and no global
existence statement is made.

Everything is `sorry`-free and `axiom`-free.
-/
