# Lagrangian Navier–Stokes: from the one-particle ESA proof to the outer Fock space

This note answers two questions. Which theorem in this project proves essential
self-adjointness (ESA) of the one-particle Hamiltonian in Lagrangian variables, and under
what assumptions? Can that proof be extended to the finite-particle domain of the outer
Fock space using the second-quantization theorem that is also in the project?

The extension is in `BookProof/ChapterNsLagrangianOuterFockEsa.lean`. That file is imported
by `BookProof.lean`, builds with no `sorry`, and uses only `propext`, `Classical.choice` and
`Quot.sound` (see `Work/NsLagrangianOuterFockAudit.lean`).

---

## 1. The one-particle theorem that already exists

**`BookProof.NavierStokesFlow.LagrangianCanonical.lagCan_esa`**
(`BookProof/ChapterNavierStokesLagrangianCanonical.lean`)

```lean
theorem lagCan_esa (hnu : 0 < nu) (f : Fin 3 → ℝ) :
    EssentiallySelfAdjointOn (lagCanData nu hnu f).D (lagrangianCore (lagCanData nu hnu f))
```

### What the statement says

| item | value in `lagCanData nu hnu f` |
| --- | --- |
| Hilbert space | `ℓ²(Fin 3 → ℕ)` (`L2I Vel`): the occupation-number (Hermite-coefficient) space of the three coordinates of **one parcel** |
| core `D` | `lpFiniteModes Vel`, the finitely supported sequences, i.e. the finite span of the Hermite states `e_β` |
| parcel coordinate | `Qᵢ = ω^{-1/2}(aᵢ + aᵢ†)/√2` |
| parcel momentum | `Pᵢ = ω^{1/2}·i(aᵢ† − aᵢ)/√2`, with `[Pᵢ,Qᵢ] = −i` (`comm_lagP_lagQ`) |
| frequency | `ω = √(2ν)` |
| operator | `h = ½ Σᵢ Pᵢ² + ν Σᵢ Qᵢ² + Σᵢ fᵢ Pᵢ` (`hFull = kinetic + viscous + drift + constraintOp`) |
| constraint term | `constraintOp = 0` |

### Explicit hypotheses
* `ν > 0`. This is needed for `ω = √(2ν) > 0` and for the rescaling of `P` and `Q`.
* `f : Fin 3 → ℝ`, an arbitrary **constant** force vector.

Nothing else is assumed. The proof has no open hypotheses and uses only the standard axioms.

### How it is proved
1. `lagT_eq_number` / `lagCan_secondOrder_eq`: `½ΣPᵢ² + νΣQᵢ² = ω(N + 3/2)`. The second-order
   part is the three-dimensional harmonic oscillator, and the Hermite states diagonalize it
   (`lagT_coreState`).
2. A total family of eigenvectors in the core gives ESA of the second-order part
   (`lagT_hasZeroDeficiencyOn`).
3. Kato–Rellich (`hFull_essentiallySelfAdjointOn_of_drive_eq_P` in
   `ChapterNavierStokesLagrangianKatoRellich.lean`): `‖Pᵢv‖ ≤ ε‖Tv‖ + (2ε)⁻¹‖v‖`, so the
   drift `f·P` has relative bound below 1. The constraint term is zero, which is trivially
   bounded. The relative-bound Kato–Rellich theorem is itself proved in the project
   (`KatoRellich.essentiallySelfAdjointOn_add_relBounded`).

### What the model does and does not contain
The following limits are part of how `lagCanData` is defined. They are not hypotheses of
the theorem, but they are what "Lagrangian NS Hamiltonian" means here:
* **No nonlinearity and no pressure.** The "advection" term is the parcel kinetic energy
  `½ΣP²`. The "viscosity" term is `νΣQ²`, a harmonic confinement in the parcel coordinate.
  The volume-preservation/pressure term (`constraintOp`) is set to `0`. So `h` is a
  three-dimensional harmonic oscillator shifted by a constant linear drift `f·P`. The
  abstract theorem `hFull_essentiallySelfAdjointOn` allows a **bounded** constraint term,
  but this instance does not use one.
* **One parcel, no interaction.** `h` acts on the three coordinates of one parcel only.
* **Hermite realization.** The space is `ℓ²(Fin 3 → ℕ)` with ladder operators. Reading it
  as `L²(ℝ³)` through the Hermite functions is the intended interpretation, but that unitary
  is not stated in this file.

### The other Lagrangian ESA results in the project (for comparison)
* `NsLagrangianDetFL.lagKoopman_esa_of_comparison_esa`
  (`ChapterNsLagrangianDetFarisLavine.lean`): a Galerkin Lagrangian NS Koopman generator
  with the exact determinant constraint imposed through the penalty `V_κ`. It is
  **conditional**: it assumes that `N_L = H_L² + E` is ESA.
* `NsFullLagrangian.lagFullOuterN_esa` (`ChapterNavierStokesFullLagrangianFock.lean`): this
  says that the lifted Friedrichs extension is ESA **on its own domain**, which is automatic
  for a self-adjoint operator (`Comparison.esa_self`). It is not ESA of the Hamiltonian on
  the finite-parcel core, and the module states that uniqueness is not claimed.
* `LagrangianKatoRellich.diagKR_hFull_essentiallySelfAdjointOn`: an abstract diagonal
  instance on `ℓ²(ℕ)`.

`lagCan_esa` is the only **unconditional** ESA proof for a Lagrangian one-parcel operator
on a proper core, so it is the one extended below.

---

## 2. The extension to the outer Fock space

The second-quantization theorem used is
**`BookProof.EsaOneParticle.dGamma_essentiallySelfAdjointOn_of_esa`**
(`ChapterEsaOneParticleDGamma.lean`). Its hypotheses are:

* `Hs` is complete,
* `D` is dense,
* `A : D → Hs` is symmetric on `D`,
* `A` is ESA on `D`.

Its conclusion is that `dΓ(A)` is ESA on the finite-particle domain
`𝓕_fin(D) = ⊕ₙ^{alg} D^{⊗n}` (the algebraic direct sum over `n` of the algebraic tensor
powers of `D`). The bosonic and fermionic versions are `FockStatistics.bosonicFock_esa`,
`fermionicFock_esa` and `hbosonicFock_esa`.

For `A = h = lagOneOp nu hnu f` and `D = lpFiniteModes Vel`, every hypothesis is
**discharged**:

| hypothesis | discharged by |
| --- | --- |
| completeness | `ℓ²` is complete (instance) |
| density | `lpFiniteModes_dense` |
| symmetry | `lagrangianCore_symmetricOn` |
| ESA on `D` | `lagCan_esa` |

### New theorems (all unconditional apart from `ν > 0`)
In `BookProof.NsLagrangianOuterFock`:
* `lagOne_dGamma_esa`: `dΓ(h)` is ESA on `𝓕_fin(D)`, where `D` is the Hermite core of one
  parcel. Concretely, the domain is the span of the finite-particle states
  `e_{β₁} ⊗ ⋯ ⊗ e_{βₙ}`, i.e. the finite-particle basis of the outer Fock space.
* `lagOne_dGamma_symmetricOn`: the matching symmetry statement.
* `lagOne_bosonicFock_esa`, `lagOne_fermionicFock_esa`: the same on the symmetric and
  antisymmetric outer Fock spaces (algebraic direct sum of the sectors).
* `lagOne_hbosonicFock_esa`: the same on the bosonic Fock space as a Hilbert space.

The conditional Koopman generator can be carried over in the same way:
* `lagKoopman_dGamma_esa_of_comparison_esa` and
  `lagKoopman_bosonicFock_esa_of_comparison_esa`: **if** `N_L` is ESA, then `dΓ(H_L)` is ESA
  on the finite-particle domain over the Gauss–polynomial core. The hypothesis is exactly the
  one in `lagKoopman_esa_of_comparison_esa`, and nothing is added.

### So: was "just extend it" enough?
**Yes, for the operator `dΓ(h)`.** The extension needed no new analysis. It is a direct
instance of the project's second-quantization theorem, whose hypotheses are exactly the
one-particle facts `lagCan_esa` already provides.

**Scope of the extension (why it does not go further):**
1. `dΓ(h)` is the **non-interacting, number-conserving** outer Hamiltonian
   `Σ_{ij} h_{ij} a†_i a_j`. On the `n`-parcel sector it is `Σ_p 1⊗⋯⊗h⊗⋯⊗1`. Parcels do not
   interact.
2. The interacting outer-Fock Lagrangian Hamiltonians of the project
   (`ChapterNavierStokesFullLagrangianFock`, whose gauge-fixing terms couple neighbouring
   parcels, with the Piola term and `det F − 1`) are **not** of the form `dΓ(one-body)`. So
   the second-quantization theorem does not apply to them. The existing `lagFullOuterN_esa`
   is only the tautological statement explained in §1. **Update (2026-09-25):** ESA of those
   Hamiltonians on the finite-parcel core is now proved by a different route; see the
   section "Update 2026-09-25" at the end of this file.
3. The one-particle model behind `lagCan_esa` has no nonlinearity and no pressure (§1).
   Every limitation of the one-particle statement carries over unchanged to the Fock-space
   statement.

## Update 2026-09-25 — the interacting Hamiltonian on the finite-parcel core

`BookProof/ChapterNsFullLagrangianFockEsa.lean` proves that the full, interacting Lagrangian
Hamiltonian `lagFullFockHam` of `ChapterNavierStokesFullLagrangianFock` is essentially
self-adjoint on the finite-parcel core `lagFockCore` (`lagFullFockHam_esa`), for all real
couplings `λ, λ', μ, g`. The same file does the Eulerian companion (`nsFullFockHam_esa`).
No new analysis was needed. Two theorems already in the project do the work:

1. **Each parcel-number sector.** `YangMillsNonAbelianEsa.weylPoly_esa` states that any
   `½ Σ_m π_{idx m}² + ½ Σ_j Φ_j²` on the Gauss–polynomial core of `L²(ℝᵈ)` is essentially
   self-adjoint when `idx` is injective and the `Φ_j` are real polynomials. Its proof writes
   `2H + 1 = −Δ_S + W` with `W = Σ Φ_j² + 1 ≥ 1` and uses the project's Kato-type theorem
   for degenerate Schrödinger operators with polynomial potentials (`hamCoreS_esa`). The
   `n`-parcel sector `lagSectorHam n` is such an operator by definition
   (`lagSectorHam_eq_weylPoly`, proved by `rfl`). The polynomials `Φ_j` include the
   parcel-coupling gauge-fixing forms, the Piola term and `det F − 1`, so the interaction
   is covered. Only the injectivity of the momentum coordinates had to be proved
   (`lagIdx_injective`). Result: `lagSectorHam_esa`.
2. **Gluing over sectors.** `DirectSumEsa.dsOp_essentiallySelfAdjointOn`: if every fibre
   is essentially self-adjoint on its core, the orthogonal direct sum is essentially
   self-adjoint on the algebraic direct-sum core. This is the "finite-parcel core from
   one-sector cores" theorem. Here the fibre is the whole `n`-parcel space
   `L²(ℝ^{36n})`, not a tensor power of a one-parcel space, which is why it applies to an
   interacting Hamiltonian where the second-quantization theorem does not.

A corollary, `lagFullFockHam_selfAdjointExtension_unique`, shows that any self-adjoint
extension of the Hamiltonian from the finite-parcel core has the same domain and values as
the lifted Friedrichs realization `lagOuterComparison`. It uses
`EsaClosure.isSelfAdjointExtension_unique_of_esa`.

**Scope.** The results are about the operator the earlier module builds: the auxiliary
positive sum of squares `½ Σ π² + ½ Σ form²` (constraint forms squared), not the
non-semibounded Koopman generator. They hold on each finite-parcel sector with the
polynomial model's discrete gauge-fixing (neighbouring parcels), with no continuum limit.
Audit: `Work/NsFullLagrangianFockEsaAudit.lean`; every listed theorem depends only on
`propext`, `Classical.choice` and `Quot.sound`.
