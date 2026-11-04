A comprehensive, mathematically rigorous research plan to establish an **analytical lower bound for the spectral separation $\beta_\infty > \theta_\infty$** within the *Timepiece* framework requires addressing the exact failure point identified in `ChapterTempleSeparationNecessary.lean`: **Rayleigh data and local residuals alone cannot prevent unseen eigenvalues from accumulating near the bottom of the spectrum.**

To prevent the Temple uncertainty $\delta = \frac{\eta^2}{\beta - \theta}$ from blowing up as the basis/truncation order $n \to \infty$, the separation $\beta_\infty - \theta_\infty \ge c > 0$ must be derived **analytically from the structural geometry of the continuous Hamiltonian**, rather than extracted numerically from truncated matrices.

---

### Research Roadmap Overview

```
[Phase 1: Geometric Characterization]
Identify flat directions of the Weyl potential V(A) = 1/2 B²
                     │
                     ▼
[Phase 2: Quantum Channel Taming (B. Simon Mechanism)]
Prove transverse zero-point energy lifts classical flat directions
                     │
                     ▼
[Phase 3: Construction of Gapped Reference Operator H_ref]
Build solvable comparison operator with certified discrete gap c_ref > 0
                     │
                     ▼
[Phase 4: Relative Form Bounding in Lean 4]
Prove H_YM ≥ c₁ H_ref - c₂ on the BRST physical core
                     │
                     ▼
[Phase 5: Spectral Isolation & Transfer to SIRK/Temple Pipeline]
Discharge hypothesis in ChapterRitzCertificate & SpectralGapStability
```

---

### Phase 1: Isolating the Soft-Mode Degeneracies

#### 1.1. The Origin of the Soft Modes
In the 3D Weyl-gauge Yang–Mills Hamiltonian:
$$H_W = \frac{1}{2} \sum_{i, a} \pi_{ia}^2 + \frac{1}{2} \sum_{i, a} B_{ia}^2$$
the magnetic potential is:
$$V(A) = \frac{1}{2} \sum_{i, a} \left( \epsilon_{ijk} \partial_j A_{ka} - \frac{1}{2} g f_{abc} \epsilon_{ijk} A_{jb} A_{kc} \right)^2$$
The potential $V(A)$ vanishes along the classical **flat directions**:
1. **Longitudinal gradients (pure gauge):** $A_i = \partial_i \phi$ (handled by the BRST charge $\Omega$).
2. **Abelian constant fields:** $A_i \in \mathfrak{t}$ (the Cartan subalgebra of $\mathfrak{su}(N)$), where $[A_j, A_k] = 0$.

Along the Cartan flat directions, $V(A) = 0$ extends to infinity in configuration space. In naive classical mechanics, this would allow particles to escape to infinity with zero potential energy, threatening a continuous spectrum starting at $\theta_\infty$ (i.e., $\beta_\infty - \theta_\infty = 0$).

#### 1.2. Milestone 1: BRST Reduction of the Pure-Gauge Directions
* **Task:** Show that the physical subspace $\mathcal{H}_{\text{phys}} = \ker \Omega / \overline{\operatorname{ran} \Omega}$ contains no longitudinal soft zero-modes.
* **Formalization:** Use `BookProof.BrstReducedTransfer` and `BookProof.QuantumGravityBrstCharge.glin_sq` to project the state space onto the transverse divergence-free subspace, eliminating the $\partial_i \phi$ flat directions before spectral analysis.

#### 1.3. Status (2026-10-31): the charge exists and is nilpotent; the *reduction* does not

This phase is the one place in the plan where the status line has to be negative, so it is worth
being precise about what is already in the corpus and what Milestone 1 still needs.  Nothing below
is an assumption of the later phases — it is a list of missing inputs.

**What is done** (all `sorry`-free, `axiom`-free; `lake build BookProof` compiles):

* `BookProof/ChapterBookBrstYangMills.lean` — the book's charge is **realized, not assumed**:
  `Ω(x) = π^μ_a ∂_μ ψ†_a − π^μ_a f_{abc} A_{μb} ψ†_c − (i/2) f_{abc} ψ†_a ψ†_b ψ_c` as operators
  on a concrete graded state space, with the canonical relations proved (`bookCCR`, `bookGhostCar`),
  the **Gauss-law algebra derived** from them (`gaussGen_bracket`,
  `[𝒢_c, 𝒢_e] = Σ_h f_{ceh} 𝒢_h`), and **`bookOmega_nilpotent`** = `Ω² = 0` for the full charge.
  `bookOmega_eq_brstCharge` identifies it with `i` times the abstract charge of
  `BookProof.QuantumGravityBrstCharge`, which is where `glin_sq` (the square of the constraint
  part) lives.
* `BookProof/ChapterBRSTNilpotent.lean` — `brst_charge_nilpotent`: the cubic ghost term squares to
  zero from the CAR plus the Jacobi identity alone (normal ordering: a quartic term killed by
  fermionic antisymmetry, two contractions killed by Jacobi).
* `BookProof/ChapterBrstReducedTransfer.lean` — the **descent to cohomology** for an abstract
  *bounded* nilpotent `Ω` commuting with a strongly continuous unitary group: `transfer` is a
  one-parameter group of linear automorphisms of `Cohomology Ω = ker Ω ⧸ closure (range Ω)`
  (`transfer_comp`, `transfer_bijective`), and the quotient norm is preserved
  (`infDist_exactStates_eq_of_comm_explicit`), with the Stone instance `stoneTransfer` for an
  unbounded self-adjoint Hamiltonian.
* `BookProof/ChapterBrstTruncationLeakage.lean` and `ChapterBrstUnboundedLeakage.lean` — the
  *leakage* side: for an unbounded exact generator and the compression `P T P` to a
  finite-dimensional retained subspace, `leakage_le` bounds `‖Ω(e^{-itB}x)‖` by `‖Ωx‖ + ‖Ω‖Kt`,
  and the exact dynamics itself does not leak.

So the algebra of §1.1 is *not* the gap: the non-abelian charge, its nilpotency, and the Gauss law
are all proved.  **What Milestone 1 needs is the passage from that algebra to a statement about
`H_phys` as a Hilbert space**, in four steps.  Step 2 is done, for a bounded charge and for a
closed densely defined one (see its status note); step 1 is done — decomposition *and* descent,
for a closed densely defined `Ω` (see its status note); steps 3 and 4 carry status notes too
(2026-11-02 and 2026-11-01).  All four are therefore addressed below, each with what it proves
*and* what it does not:

1. **An unbounded charge.**  `ChapterBrstReducedTransfer` needs `Ω` *bounded* (it uses `Ω` as an
   element of `H →L[ℂ] H`).  The field-theoretic `Ω` is a cubic differential operator, so the
   reduction lemmas have to be reproved for `Ω` closed and densely defined with `Ω² = 0` on a core
   invariant under the dynamics, and with `[H, Ω]` expressed as strong commutation of `e^{-itH}`
   with `Ω` on that core.  Until then the two chapters do not compose: one has a concrete `Ω` and
   no `H`, the other an abstract bounded `Ω` and an abstract `H`.  (The bounded `Ω` is now only
   needed for the *descent*, not for the decomposition — see the status note below.)

   **Status (2026-10-31): the norm side is done for a closed densely defined `Ω`.**
   `BookProof/ChapterBrstUnbounded.lean` (`BookProof.ChapterBrstUnbounded`, no `sorry`) reproves
   the harmonic decomposition for a partially defined charge `Om : H →ₗ.[ℂ] H` with **closed
   graph** (`HasClosedGraph`), **dense domain** and `Ω² = 0` on its domain (`IsNilpotent`, with the
   domain clause that a partial map needs).  Three things change relative to the bounded chapter:
   `isClosed_physicalStates` — the kernel of a closed operator is closed, by pulling the closed
   graph back along `x ↦ (x, 0)`, where the bounded case used continuity; the adjoint is now built
   by hand (`adjointDomain`, `adjointFun`, `adjoint`) because no bounded adjoint exists, and
   **density** is exactly what makes it a function (`adjoint_unique`: two representing vectors
   differ by a vector orthogonal to the dense domain), giving
   `exactStates_orthogonal` (`(closure (range Ω))ᗮ = ker Ω†`) and
   `range_orthogonal_eq_adjointKernel`; and the quotient-norm machinery carries over verbatim —
   `sup_exact_harmonic`, `disjoint_exact_harmonic`, `hodge_decomposition`
   (`harmonic ⊔ exact ⊔ coexact = ⊤`), `harmonicPart_mem`, `harmonicPart_eq_of_sub_mem_exact`,
   `exists_harmonic_decomposition` and `infDist_eq_norm_harmonicPart`
   (`infDist x (exactStates Ω) = ‖harmonicPart x‖`, still attained).

   **Status (2026-11-01): the descent is now done too.**
   `BookProof/ChapterBrstReducedTransferUnbounded.lean`
   (`BookProof.BrstReducedTransferUnbounded`, no `sorry`) closes what the note below used to call
   the bounded-only remainder.  For a partially defined `Ω` the commutation hypothesis
   `[H, Ω] = 0` cannot be one equation — `Ω (U y)` is not even a term unless `U y` is known to lie
   in the domain — so it splits in two, and neither half can be dropped:
   `DomPreserve Om U` (the evolution maps the domain into itself) and
   `StrongCommute Om U hdom` (`U (Ω y) = Ω (U y)` for `y` in the domain, read at `hdom y`).
   From those two, everything the bounded chapter proved carries over:
   `physicalStates_invariant` (nilpotency *not* needed: `Ω x = 0` is transported to
   `Ω (U x) = U (Ω x) = U 0 = 0`), `exactStates_invariant` (where it is **continuity of `U`**,
   not boundedness of `Ω`, that carries the range into its closure — the evolution is a
   continuous linear map throughout, which is exactly why the argument survives), `reducedMap`,
   the group `transfer` with `transfer_zero`, `transfer_comp`, `transfer_apply_transfer`,
   `transfer_bijective`, the quotient-norm preservation `infDist_exactStates_eq_of_comm_explicit`,
   and the Stone instance `stoneTransfer` with `stoneTransfer_zero` / `stoneTransfer_comp` /
   `stoneTransfer_bijective`, `stoneU_mem_physicalStates_of_comm_explicit`,
   `stoneU_sub_mem_exactStates_of_comm_explicit` and
   `infDist_exactStates_stoneU_eq_of_comm_explicit`.  The binder discipline of the bounded
   chapter (the hypotheses written in each theorem's binder list, so that a textual re-export
   cannot drop them and assert norm preservation for an arbitrary isometric family) is
   reproduced verbatim.

   Von Neumann's closed-range theorem `closure (range Ω†) = (ker Ω)ᵮ` is now proved for the
   unbounded chapter, in `BookProof/ChapterBrstUnbounded.lean` §7:
   `closure_range_adjoint_eq_coexact` (with `range_adjoint_orthogonal`: `(range Ω†)ᵮ = ker Ω`,
   `adjoint_adjoint_eq`: `Ω†† = Ω`, and `adjoint_domain_dense`: closedness and density pass to
   `Ω†`).  The proof is the graph rotation of `Submodule.adjoint` in `WithLp 2 (H × H)`: rotation
   is an involution on closed graphs (`adjoint_adjoint_of_isClosed`) and
   `Ω†.graph = Ω.graph.adjoint` (`graph_adjoint`), so the coexact sector defined as `(ker Ω)ᵮ`
   *is* `closure (range Ω†)`.  The earlier inclusion `range_adjoint_le_coexact` is now the easy
   half of an equality, and the third summand of the Hodge decomposition is named as in the
   bounded chapter.  (The harmonic sector, the exact sector and the quotient norm never depended
   on this identification.)
   The two chapters still do not *compose*, for the reason item 1 states: `[H, Ω] = 0` for a
   concrete `H` is not proved, so `hdom` / `hcomm` are hypotheses, not theorems, in a specific
   model.  The concrete `H` itself is no longer missing: the corpus carries the Yang–Mills and
   Standard-Model Hamiltonians in the nested Fock space — `ymHamiltonian`
   (`BookProof/Qym/ChapterYangMillsHermite.lean`, the Gauss–polynomial core of `L²(ℝ⁹⁹)`) and
   `smHamiltonian` (`BookProof/Sm/ChapterSmHamiltonian.lean`, `d = 163`) — so what is missing is
   the commutation with `Ω`, not the operator to commute with.  (The gauge/BRST symmetry it must
   commute with is in the corpus too: `ChapterBookBrstYangMills` and
   `ChapterBookBrstGaugeFixing`.)

   **Progress on the missing commutation (2026-11-03).**
   `BookProof/ChapterBrstYmCommute.lean` (`BookProof.BrstYmCommute`, no `sorry`, no `axiom`)
   now carries the **constraint half** of `[ymHamiltonian, Ω] = 0` for the concrete model, on
   the `99 = 3 + 24 + 72` coordinate space of `book.tex:7045`:

   * the Gauss generators `𝒢_d` realized as derivations of `ℂ[X_0…X_98]` extended to the **jet
     coordinates** `∂_j A_{ka}` — the extension is not cosmetic: a constraint that rotates only
     the `A`-slots leaves `X_D · (f A A)` cross terms in `[Σ_m B_m², 𝒢_d]` uncancelled;
   * `ymGaussDer_bracket` / `ymGaussPoly_bracket` / `ymGauss_bracket`:
     `[𝒢_c, 𝒢_e] = Σ_h f_{ceh} 𝒢_h`, reduced to the contracted field identity
     `field_identity_C` and applied block-by-block;
   * `ymConstraintAlgebra` and `ymOmega_nilpotent` — `Ω = i • brstCharge G.f 𝒢 χ β` on
     `ℂ[X_0…X_98] ⊗ Λ(ℂ⁸)` and `Ω² = 0`.

   **What this still does not give.**  The two Casimir lemmas the Hamiltonian half needs are
   not there, so `hdom` / `hcomm` remain hypotheses:
   `[Σ_m π_m², 𝒢_d] = 0` (needs the vector relation `[∂_{jc}, 𝒢_d] = Σ_b f_{bcd} ∂_{jb}`,
   hence `∂_i (ymGaussVec G d k)` by coordinate case split) and
   `[Σ_m B_m², 𝒢_d] = 0` (needs `𝒢_d(B_{ia}) = Σ_g f_{agd} B_{ig}`, i.e. the scalar
   contraction `Σ_e f_{aec}f_{ebd} + Σ_e f_{abe}f_{ecd} = Σ_g f_{agd}f_{gbc}` from
   `G.jacobi` + `G.antisymm` + `G.cyclic`).  Given those, `ymOmega_comm_ymH` is one
   application of `brstCharge_comm_of_comm`, and the module header records that route.  The
   regime is the constant gauge algebra `G.D = 0`, the same hypothesis
   `gaussDer_casimirPoly` / `casimir_bookOmega_comm` already carry.
2. **A quotient norm that exists.**  `infDist x (exactStates Ω)` is the norm of the class `[x]` in
   the quotient *only* when `exactStates Ω = closure (range Ω)` is a closed subspace of a Hilbert
   space.  On the ghost sector the natural form is indefinite, so the quotient norm has to come
   from the **harmonic (invariant) representative** — a Hodge-type decomposition
   `H = ker Ω ∩ ker Ω* ⊕ range Ω ⊕ range Ω*` — rather than from `infDist`.  This is the one
   genuinely functional-analytic (not merely bookkeeping) input of the phase; with it,
   `physicalStates_invariant` / `exactStates_invariant` transfer verbatim, without it they do not.

   **Status (2026-10-31): DONE for a bounded nilpotent `Ω`, and the decomposition is a theorem,
   not a redefinition.**  `BookProof.ChapterBrstHarmonicDecomposition`
   (`BookProof/ChapterBrstHarmonicDecomposition.lean`, no `sorry`) proves the Hodge decomposition
   on a complex Hilbert space from `Ω†` alone — the two orthogonal complements are
   `exactStates_orthogonal` (`(closure (range Ω))ᗮ = ker Ω†`, via `orthogonal_range` and
   `orthogonal_closure`) and `coexactStates_orthogonal` (`(closure (range Ω†))ᗮ = ker Ω`), so the
   harmonic states `harmonicStates = ker Ω ⊓ ker Ω†` are a *direct complement* of the exact ones
   inside the physical subspace (`sup_exact_harmonic`: `exact ⊔ harmonic = physicalStates`,
   `disjoint_exact_harmonic`) and the three summands span the space with pairwise orthogonal
   parts (`hodge_decomposition`: `harmonic ⊔ exact ⊔ coexact = ⊤`, with
   `disjoint_exact_coexact`, `disjoint_harmonic_coexact`).  The harmonic representative
   `harmonicPart x = x − P_{exact} x` is explicitly constructed, is harmonic for closed `x`
   (`harmonicPart_mem`), differs from `x` by an exact state (`sub_harmonicPart_mem_exact`), and
   depends only on the class (`harmonicPart_eq_of_sub_mem_exact`).  The plan's point 2 is then the
   **identity** `infDist_eq_norm_harmonicPart`:
   `infDist x (exactStates Ω) = ‖harmonicPart x‖` — the infimum is *attained*, so the harmonic norm
   is a norm on cohomology and agrees with `infDist`; and `exists_harmonic_decomposition` states
   the decomposition of a closed state with its orthogonality explicit.  The passage to a closed
   densely defined charge is now in `ChapterBrstUnbounded` (see the status note of item 1 above),
   which reproves the same statements for `Ω : H →ₗ.[ℂ] H` with closed graph and dense domain.
   The ghost-sector indefiniteness is not addressed in either chapter: both work with the
   Hilbert-space inner product, which is exactly why the decomposition exists.
3. **“Longitudinal = exact”.**  The claim “`H_phys` contains no longitudinal soft zero-mode” is the
   identification `closure (range Ω) = span{∂_i φ}` (the pure-gauge directions are *precisely* the
   BRST-exact states), followed by the observation that a longitudinal plane wave is not harmonic,
   i.e. is not in `ker Ω ∩ ker Ω*`.  At present the charge is realized on a graded polynomial
   algebra and `range Ω` is not identified with any longitudinal span; there is also no
   `H_phys` — no completion, no inner product — to speak of a zero-mode *in*.

   **Status (2026-11-02): the identification is a theorem at the level the algebraic realization
   carries it, and the observation half is a theorem too.**
   `BookProof/ChapterBrstLongitudinal.lean` (`BookProof.BrstLongitudinal`, no `sorry`) closes the
   algebraic half in the realization of `book.tex`, on the graded state space the corpus already
   works on, and sits on the gauge/BRST symmetry work already in `timepiece/BookProof/`:
   `ChapterBookBrstYangMills` (the charge realized with `bookCCR`, the Gauss-law algebra and
   `bookOmega_nilpotent`) and `ChapterBookBrstGaugeFixing` (gauge-invariant observables commute
   with the charge — `bookOmega_comm_of_comm` — and descend to `brstCohomology`,
   `mem_exactStates_of_comm`).

   * The gauge orbit of `A_{μa}` splits into the longitudinal gradient and the non-abelian
     remainder (`gaussVec_eq_longitudinal_add_comm`): `longitudinalGaugeVec` is the
     field-independent `−∂_μ α_a` — constant as a polynomial, which is what makes it a gradient
     (`longitudinalGaugeVec_eq_zero_iff` reads it off `G.D` alone) — and `commGaugeVec` is the
     `Σ_g f_{agc} X (μ, g)` bracket, which vanishes identically for `f = 0`
     (`commGaugeVec_eq_zero_of_abelian`).  So for an abelian gauge algebra the orbit *is* the
     longitudinal span: an equality, not an inclusion.
   * In that case the charge collapses to its derivative term (`bookOmega_abelian`), and the
     canonical relation `bookCCR` then fixes its commutator with the field:
     **`comm_bookOmega_Afield`** is `[Ω, A_{μa}] = −i · dChi G μ a`, with *no* commutator piece —
     the BRST variation of the field *is* the ghost-dressed longitudinal direction
     (`dChi_eq_longitudinal_dress`), so the directions the reduction removes are precisely the
     ones the charge produces.
   * The payoff is `longitudinal_mem_exactStates_of_physical`: applied to a BRST-closed `v`,
     `Ω (A_{μa} v) = −i · dChi G μ a v`, so the ghost-dressed longitudinal direction maps into
     `exactStates` and its class in `brstCohomology` is zero — "no longitudinal soft zero-mode"
     as far as the algebraic realization carries it.  The *observation* half — a longitudinal
     plane wave is not harmonic — is `ChapterBrstHarmonicDecomposition.no_longitudinal_zero_mode`:
     for any `L ≤ exactStates`, a state of `L` lying in `ker Ω ∩ ker Ω†` is zero, from
     `disjoint_exact_harmonic` alone, so it needs no field model.
   * The Hamiltonians this charge would have to commute with are in the corpus as well, in the
     nested Fock space: `ymHamiltonian` (`BookProof/Qym/ChapterYangMillsHermite.lean`, `L²(ℝ⁹⁹)`)
     and `smHamiltonian` (`BookProof/Sm/ChapterSmHamiltonian.lean`, `d = 163`).  `[H, Ω] = 0` for
     either is not proved here; that is the composition item 1 still records as open.

   **Honest boundary.**  What is proved is one direction, in the abelian case, as an identity of
   operators: `longitudinal ⊆ gauge orbit = exact`.  The converse — `closure (range Ω) =
   span{∂ᵢφ}` as an equality of *subspaces* — needs the gauge field to be a function on
   spacetime; `BookState N` carries no inner product and no completion, so it is not an equality
   of closures yet.  For `f ≠ 0` the orbit is strictly larger than the longitudinal span: the
   commutator picks up the `Σ_{bc} f_{abc} A_{μb} ψ†_c` term from applying `bookCCR` to the
   `f`-carrying summand of `bookOmega` — a shape, not a theorem.  And neither half speaks of a
   completed `H_phys`: the realization is algebraic on `BookState`, while the Hilbert-space
   statement lives in `ChapterBrstHarmonicDecomposition` (bounded) / `ChapterBrstUnbounded`
   (closed densely defined).
4. **Stability of the bottom under the elimination.**  Phases 2–5 bound the bottom and the first
excited level of the operator on the *unreduced* core (`degreeForm`, `barrierForm`, and the
   `FormDomination` certificate).  For the elimination to be legitimate those numbers must be those
   of the reduced operator: one needs that restriction to the transverse sector does not lower
   `θ∞`, or equivalently that the eliminated directions carry no spectral weight near the bottom.
   Without this, Phase 1 could remove exactly the directions that dominate the bottom and Phases
   2–5 would be bounding a different operator.

   **Status (2026-11-01): the statement is now a theorem for the diagonal forms of this corpus,
   and the reason it is short is itself the content.**  In `BookProof.YangMillsFormClosure`
   (section 5, no `sorry`):

   * `formBottom f = sInf (Set.range f)` is the bottom of the symbol, with
     `formBottom_le_of_bddBelow` reading it off.  `ℝ` is only *conditionally* complete, so there
     is no `⨅` into `ℝ`; every statement is therefore equally available in the "any lower bound
     `θ`" form, which is the form the plan's `c₁Δ_ref` already takes.
   * **`diagonalForm_ge_of_le_symbol`** / **`closedForm_ge_of_le_symbol`** — `θ · ‖·‖² ≤ q(x)`
     for every `θ ≤ f n`, on the core and on `L²`, and hence
     **`diagonalForm_ge_formBottom`** / **`closedForm_ge_formBottom`** at `θ = formBottom f`.
   * **`sector_bottom_ge_of_le_symbol`** / **`sector_bottom_ge_formBottom`** — for *any* set `S`
     of normalised retained states, `ofReal θ ≤ sInf (closedForm f '' S)`: the Rayleigh infimum
     over a sector is bounded below by the *same* constant as over the whole space.  That is
     exactly "restriction to the transverse sector does not lower `θ∞`", and it is where the
     plan's "the eliminated directions carry no spectral weight near the bottom" lands.

   **Why it is short, and what that costs.**  The bound is *symbolwise*: every term of
   `closedForm f x = ∑' n, ofReal (f n) · ofReal (‖x n‖²)` is indexed by one multi-index, so the
   form never mixes retained with eliminated directions and restriction cannot improve on a
   symbolwise estimate.  Diagonality is a property of the free, quartic and barrier forms the
   corpus models — it is the same hypothesis under which `formDomination_closed` transfers, and
   the same one its honest boundary says does not cover a magnetic interaction that mixes
   multi-indices.  So the item is closed *for the forms Phases 2–5 actually bound*; for an
   interacting form with off-diagonal blocks, "no spectral weight near the bottom in the
   eliminated directions" is a genuine statement about those blocks, and it is not proved here.
   The reduced space itself — the quotient `H/(exact ⊕ harmonic)` — is built in
   `ChapterBrstReducedTransfer` / `ChapterBrstUnbounded`; what is missing there is item 3 above,
   the identification `closure (range Ω) = span{∂_i φ}`, not the stability of the bottom.

   **The off-diagonal half (2026-11-04).**  The sentence above leaves one case open: a form whose
   blocks mix multi-indices, where the symbolwise argument has nothing to read.  It is closed for
   any interaction with finite Hilbert–Schmidt constant, in §4 of
   `BookProof.YangMillsFormClosureNonDiagonal`: the form bound `abs_kernelForm_le_of_hs` gives
   `kernelForm_ge_neg_of_hs` (`−σ‖c‖² ≤ qK`), so **`diagonalForm_add_kernelForm_ge`** bounds the
   interacting form below by `θ − σ` on the core whenever `θ` bounds the diagonal symbol, and
   **`sector_bottom_ge_interacting`** is the sector statement: over any nonempty set of
   *normalised* retained core states, `sInf` of the interacting form is at least `θ − σ`, with no
   hypothesis on which indices the kernel couples and no hypothesis on the sector.  So restriction
   cannot lower the bottom by more than the Hilbert–Schmidt constant of the interaction — the same
   constant `hopping_farisLavine` charges to the shift, and for the hopping matrix unit
   (`hopping_sector_bottom`) it is exactly `1`.

   **The `L²` lift (2026-11-04).**  §5 of the same module closes the lift this item was missing.
   Truncations were never the right tool here: `closedForm_eq_iSup_truncate` lifts the diagonal
   part because `closedForm` is the supremum of its truncations, and a non-diagonal kernel form is
   not monotone along truncations.  What replaces it is the operator: `closedKernelForm K x` is the
   weighted double series over **all** of `Idx d × Idx d`, absolutely convergent for every
   `x ∈ ℓ²`, and `abs_closedKernelForm_le` gives `|closedKernelForm K x| ≤ σ‖x‖²` with the *same*
   `σ` — one Cauchy–Schwarz with exponents `2, 2` in `ℓ²(Idx d × Idx d)` between the kernel and the
   product of the two coefficient rows (`tsum_sq_kernel_le`: the `σ²` is the total Hilbert–Schmidt
   mass, not a partial sum; `tsum_sq_weight_le`: the weight mass is `‖x‖⁴`).  On the core it *is*
   the core form (`closedKernelForm_coreEmbed`), so this is an extension and not a different form;
   `closed_diagonal_add_kernelForm_ge` gives `θ − σ ≤ closedForm f x + closedKernelForm K x` on the
   form domain (`closedForm f x ≠ ⊤`), and `closed_sector_bottom_ge_interacting` /
   `closed_hopping_sector_bottom` carry the sector statement to `L²`, so the reduced space itself
   can be a closed subspace of `ℓ²` and not only a set of core states.  Note what the hypothesis
   costs: finiteness of the total Hilbert–Schmidt mass holds at a **fixed cut-off**, where the
   interaction is an honest finite matrix, and it is not uniform in the cut-off — the number of
   coupled multi-indices and the magnetic matrix elements grow with the mode index, so no single
   `σ` survives the continuum limit, where the magnetic term is only relatively form bounded with
   `a < 1`.   Boundedness is a *sufficient* condition for closability (the interaction is then a
   continuous perturbation of the closed diagonal form, and the sum is closed on the same domain),
   the `a = 0` case of the Faris–Lavine branch; it is not the necessary one.  **The comparison is
   now stated on `L²` too (2026-11-04)**: §6 gives `closed_farisLavine_domination` — ratio
   `(1 − a)c₁ > 0`, shift `(1 − a)c₂ + b`, for a relative bound `a < 1` — with the finiteness of
   the closed forms as the only extra hypothesis, and `closed_dom_of_scaled_symbol` *derives* that
   hypothesis from a symbolwise inequality `c₁ f ≤ g + C` rather than assuming it (`toReal` of `⊤`
   is `0`, so the finiteness cannot be dropped).  What neither section supplies is a bound uniform
   in the cut-off: §7 computes it on a model — `magCutoffKernel_hs_mass` gives the magnetic ladder
   mass at most `d² C Λ^(d+1)`, i.e. a constant at most `d √C Λ^{(d+1)/2}` — which is a power of
   the cut-off and not a uniform `σ`, so the continuum still needs the `a < 1` branch with `a`
   bounded away from `1` uniformly.  The **ratio** is in fact uniform for free —
   `ladder_relative_bound_uniform` (§8) takes `a` as a free parameter, so `a(Λ) < 1` at every
   cut-off, because at fixed cut-off the ladder is bounded — so what fails in the continuum is the
   constant, not the ratio.  And the finiteness hypothesis of the comparison is not an extra
   assumption for the Yang–Mills symbol: `closed_dom_of_scaled_symbol_auto` derives it from the
   symbolwise inequality whenever the ratio is positive, and `magnetic_closed_dom_of_scaled` (§9)
   applies it to `magSymbol`, the symbol of `magneticEnergyForm` of `YangMillsMagneticQuartic`.
   One scope note, because the continuum *is* formalized elsewhere: the space-time derivative is an
   outer-Fock operator (`dGamma`, `momOp`) and coincident-point products of outer fields are never
   formed — they are the momentum convolutions of `dft_samePointProduct`,
   `momentumCol_samePointProduct`, `samePointProduct_form_eq_momentum`.  The reduced form here is
   diagonal (`yangMillsForm_eq_diagonalForm`), so the ladder is a model of the coupling rather than
   the eliminated theory's magnetic slot, and carrying `σ(Λ)` across needs the off-diagonal part of
   the reduced Hamiltonian — not done.

What Phase 1 does **not** need, and what the plan does not ask of it: any statement about the
*interacting* theory or about the existence of a mass gap.  Those remain Phases 4–5, and the
separation `β∞ − θ∞ ≥ c₁Δ_ref` is still an input there (see the status of Phase 4).

---

### Phase 2: Quantum Channel Taming (The B. Simon Mechanism)

#### 2.1. Analytical Principle
For non-Abelian gauge models, classical flat directions do **not** imply a continuous spectrum in quantum mechanics. 
* By **Barry Simon’s Theorem** (*Some Quantum Mechanical Problems with a Clean Spectrum*, 1983), potentials of the form $V(x, y) = x^2 y^2$ on $L^2(\mathbb{R}^2)$ have **purely discrete spectrum** despite the infinite cross-shaped valleys along the $x$- and $y$-axes.
* **Physical Mechanism:** As $|x| \to \infty$ along a valley, the transverse potential $V_x(y) = x^2 y^2$ becomes an oscillator in $y$ with frequency $\omega(x) = |x|$. By the Heisenberg uncertainty principle, the zero-point energy of the transverse motion is:
  $$E_0(x) = \frac{1}{2} \hbar \omega(x) = \frac{1}{2} g |x| \xrightarrow{|x| \to \infty} \infty$$
* The "cross-sectional width" of the valley shrinks so rapidly ($w(x) \sim 1/\sqrt{g|x|}$) that quantum wave-packets cannot penetrate deeply into the valley without paying an infinite kinetic energy penalty.

#### 2.2. Mathematical Formulation for $SU(N)$ Field Space
For Yang–Mills on the product Hermite core $L^2(\mathbb{R}^{d_N})$:
1. Split the gauge fields into **Cartan modes** $A_{\parallel} \in \mathfrak{t}$ and **off-diagonal root modes** $A_{\perp} \in \mathfrak{su}(N) \setminus \mathfrak{t}$.
2. Expand the magnetic potential:
   $$V(A) = V_{\text{linear}}(A) + \frac{1}{4} g^2 \sum_{j, k} \|[A_j, A_k]\|^2 \ge \frac{1}{4} g^2 \sum_{\alpha \in \text{roots}} (\alpha(A_{\parallel}))^2 \|A_{\perp, \alpha}\|^2$$
3. Treat $A_{\perp}$ as an oscillator in the background of $A_{\parallel}$. The effective zero-point Hamiltonian on the Cartan subspace is:
   $$H_{\text{eff}}(A_{\parallel}) = -\frac{1}{2} \Delta_{\parallel} + \frac{1}{2} g \sum_{\alpha \in \text{roots}} |\alpha(A_{\parallel})|$$
4. Since $\sum_{\alpha} |\alpha(A_{\parallel})| \to \infty$ whenever $\|A_{\parallel}\| \to \infty$ outside the origin, $H_{\text{eff}}$ is **strictly confining** in all directions.

#### 2.3. Milestone 2: Formalizing the Effective Confining Barrier
* **Task:** Prove the functional inequality in Lean 4:
  $$\langle \psi, H_W \psi \rangle \ge \langle \psi, \left( -\frac{1}{2} \Delta + c_g \|A\| - C_0 \right) \psi \rangle \quad \forall \psi \in \mathcal{D}_{\text{Hermite}} \cap \mathcal{H}_{\text{phys}}$$
* **Deliverable:** A Lean module `BookProof.YangMillsEffectiveBarrier.lean` establishing that $H_W$ is bounded below by a globally coercive operator.
* **Status (2026-10-30): the mechanism is DONE; the domination inequality is the input, as an interface.**
  `BookProof.YangMillsEffectiveBarrier` (`BookProof/YangMillsEffectiveBarrier.lean`, no `sorry`)
  carries the Cartan/root split of the degree form of `BookProof.YangMillsFormDomination` —
  `parallelDegree` (the Cartan occupation `N` of a multi-index), `perpDegree`, `rootCount`, with
  `parallelDegree_add_perpDegree` splitting `∑ i, nᵢ` — and Simon's barrier at one root mode:
  `zeroPoint g N = ½ g √(N + ½) = transFreq/2`.  The mechanism's content is the growth, and that
  is proved: `zeroPoint_nonneg`, `zeroPoint_lt` (strictly increasing in the background) and
  **`zeroPoint_coercive`** — for every target `M` there is `K` with `M ≤ zeroPoint g N` for all
  `N ≥ K`.  On the field side this is `effPotential T g N = rootCount · zeroPoint g N` and
  **`simon_valley_lifted`**: with at least one root direction and `g > 0`, the effective energy
  along the Cartan valley exceeds any bound, so the valley is confined.  In its original
  two-dimensional form the model `simonPotential g x y = g²x²y²` has an *exactly* flat valley
  (`simonPotential_flat`) whose effective energy `simonEffective g x = zeroPoint g |x|` is coercive
  (`simonEffective_coercive`) — Simon's theorem's phenomenon, without its discreteness conclusion.
  The barrier is sublinear (`sqrt_le_add_quarter`, `zeroPoint_le_linear`: `√x ≤ x + ¼`), which is
  why it never competes with the kinetic term, and the transverse/longitudinal trade-off is
  `two_mul_sqrt_le`.  On the core the barrier is the quadratic form `barrierForm` (nonnegative for
  `g ≥ 0`, `barrierForm_zero_g` at zero coupling).
  The coupling is not a free parameter here: the quartic `:N²:` interaction contains the Cartan/root
  cross term `2 N_∥ N_⊥` (`crossDegreeForm`, and `quarticDegreeForm_ge_crossDegreeForm` proves the
  quartic form dominates it), which at background occupation `N` is an oscillator of frequency
  `√(2N + 1)` (`transFreq_sqrt_two`); with `g = √2` the barrier is exactly its zero-point energy
  (`zeroPoint_sqrt_two`).  So `zeroPoint (√2)` — not an arbitrary `g` — is the barrier the magnetic
  potential itself produces, which is what §2.2 item 2 (`½g²∑‖[A_j,A_k]‖²`) asserts.
  The §2.3 inequality is packaged as the structure `IsBarrierBound T g q`
  (`q ≥ degreeForm + barrierForm − C‖·‖²` on the Gauss–polynomial core); `formDomination_of_barrier`
  turns it into the Phase-4 `FormDomination` certificate (ratio `c₁`, shift `c₁μ₀ + C`), and
  `barrier_gap` gives the separation `c₁ Δ_ref` with the barrier included.

  **The inequality now holds for the Yang–Mills form `q_W` itself** (2026-10-30) —
  `BookProof.YangMillsMagneticQuartic` (`BookProof/YangMillsMagneticQuartic.lean`, no `sorry`).
  The magnetic energy of the field strength is, per mode, the sum of the squares of its components,
  `q_mag(c) = ∑_n (∑_a B_a(n)²)‖c n‖²` with `B_a(n) = ∑_i A_{a i} nᵢ` (`magComp`,
  `magneticEnergyForm`); in the canonical Cartan basis the components are the occupations
  themselves (`magComp_diag`).  Cauchy–Schwarz and `0 ≤ B_a ≤ N` give the two comparisons with the
  normal-ordered `:N²:` form,
  `quarticDegreeForm c ≤ d · q_mag(c)` (`quarticDegreeForm_le_magnetic`) and
  `q_mag(c) ≤ d · quarticDegreeForm c` (`magnetic_le_quartic`), i.e. the magnetic form *is* the
  quartic `:N²:` form up to the explicit factor `card`.  Since `q_W = degreeForm + q_N² + barrier`
  on the core, `barrierBound_quartic` transfers to `q_W`: **`barrierBound_yangMillsForm`** is
  `IsBarrierBound T g (yangMillsForm T g)` with the *same* explicit shift `C = K + (1 + K)²/4`,
  `K = rootCount T · g/2`, and **`yangMillsForm_certifiedGap`** is the §4.1 separation
  `c₁ Δ_ref ‖c‖² ≤ q_W(c) + C‖c‖²` on the vacuum-orthogonal sector.  So the interface is
  inhabited by `q_W` itself, not by a model of its interaction.  What remains is deriving the
  components `B_a` from the concrete potential (the `∂A + g[A,A]` normal ordering of
  `ChapterFockInteractionStability`) and the root-mode normal form; the form comparison no longer
  depends on either.

  **The Cartan components `B_a` are now derived, not assumed** (2026-10-30) —
  `BookProof.YangMillsFieldStrength` (`BookProof/YangMillsFieldStrength.lean`, no `sorry`).  The
  potential component is a *nested pair* `c† diag(A_a) c` — an outer creation–annihilation pair
  with the inner self-adjoint operator in between (`sandwich`).  **No normal ordering is needed**:
  the nested algebra multiplies pairs by composing the inner operators, so the contraction of
  Wick's theorem *is* the inner matrix product and the double-creation term is not in the algebra;
  and the one constant that could hide — the `+1` distinguishing `c c†` from `c†c` — is absent,
  since **`hopWord_pair_same`** shows the ordered pair acts on `n` by exactly `n_j`, with no
  constant term.  Consequently **`sandwich_diag_single`** gives the diagonal pair's eigenvalue
  `∑ j, m_j n_j` and **`sandwich_diag_magComp`** gives `B_a(n) = magComp A a n`; the energy form
  `½ ∑_a B_a²` is `magneticEnergyForm` read componentwise (`magneticEnergyForm_eq_sum`).

  **The assembly `F = ∂A + g[A,A]` and the root sector are now done, on the corpus's own
  operator** (2026-10-30) — `BookProof.Qym.ChapterYangMillsFieldStrengthSplit`
  (`BookProof/Qym/ChapterYangMillsFieldStrengthSplit.lean`, no `sorry`), which works with the
  field strength already in the repository rather than a model of it: `magPoly` of
  `BookProof.YangMillsHermite` (`B_{ia} = ε_{ijk}(∂_j A_{k,a} + f_{abc}A_{j,b}A_{k,c})` on the
  Gauss–polynomial core of `L²(ℝ⁹⁹)`, the `B` of `ymHamiltonian`) and the same shape in
  `BookProof.Sm.ChapterSmHamiltonian` (`smMagG`, `smMagW`, `smMagB` with the coupling `g_s`
  explicit).  Results: **`magPoly_eq_deriv_add`** splits it into `magDeriv` (linear in the
  configuration) plus `magComm` (the `g[A,A]` term); **`magOps_apply_eq`** is the same identity for
  the operators on the core, and both halves are symmetric (`magOpsDeriv_symmetricOn`,
  `magOpsComm_symmetricOn`) since both have real coefficients; **`two_smul_levi_contract`** shows
  the `ε`-contraction of *any* bilinear form is the contraction of its antisymmetrisation, so the
  non-abelian term is `½ ε_{ijk}[A_j,A_k]` and **`magComm_eq_zero_of_symmetric`** kills it on the
  commuting (Cartan) sector — which is exactly why the components there are the *linear* forms
  `magComp`.  Off the Cartan directions the root sector is quartic: in the `su(2)` root plane
  `[a₁E₊ + b₁E₋, a₂E₊ + b₂E₋] = (a₁b₂ − b₁a₂)H` (**`rootField_commutator`**) and the magnetic
  energy of that component is the **square** of the root determinant, `½‖[A₁,A₂]‖² =
  ‖a₁b₂ − b₁a₂‖²` (`root_energy`, `root_energy_real`), zero exactly on parallel amplitudes
  (`root_energy_eq_zero_iff`) and equal to `4 (Im(a₁\bar a₂))²` for hermitian fields
  (`root_energy_hermitian`).  And the reason no normal ordering arises in the potential is
  explicit: multiplication operators compose exactly, `mulOp (p * q) = mulOp p ∘ mulOp q`
  (`mulOp_mul`), so the quartic `A_{j,b}A_{k,c}` needs no Weyl symmetrisation — unlike the `πA`
  cross terms, where `[A_j, π_j] = i`.  Not claimed: that a general `f_{abc}` decomposes into
  `su(2)` root blocks, or any dynamical statement.

  **The split is carried to the Standard Model field strengths of record** (2026-10-30) —
  `BookProof.Sm.ChapterSmFieldStrengthSplit` (`BookProof/Sm/ChapterSmFieldStrengthSplit.lean`, no
  `sorry`), on `smMagG` (gluons, `f_{abc}` with `g_s`) and `smMagW` (weak bosons, `ε_{mbd}` with
  `g`) — the `B`'s that enter `smHamiltonian = ½ Σ π² + ½ Σ B²`.  **`smMagG_eq_deriv_add`** and
  **`smMagW_eq_deriv_add`** split each into `smDerivG`/`smDerivW` (linear) plus
  `smCommG`/`smCommW` (the `g[A,A]` term).  Each half has real coefficients
  (`realCoeff_smDerivG`, `realCoeff_smCommG`, and the `W` pair), so each is a *symmetric
  multiplication operator* on the Gauss–polynomial core (`smDerivG_symmetricOn`,
  `smCommG_symmetricOn`, `smDerivW_symmetricOn`, `smCommW_symmetricOn`), and the split is an
  identity of operators, not only of polynomials (`smFieldG_apply_eq`, `smFieldW_apply_eq`).
  `two_smul_levi_contract` is proved for the lattice dimension of the Standard Model as well, so
  **`smCommG_eq_quarter_bracket`** / **`smCommW_eq_quarter_bracket`** identify the non-abelian
  terms as `¼ ε_{ijk} g [A_j,A_k]` — the outer `½` is the one in the definition of `B`, the inner
  one comes from antisymmetrising the `ε`-contraction — and
  **`smCommG_eq_zero_of_symmetric`** / **`smCommW_eq_zero_of_symmetric`** kill them on the
  commuting (Cartan) sector, where the field strength is the derivative part alone.  Left as they
  are: the hypercharge `smMagB` (abelian, already linear, no commutator part) and the Higgs
  covariant derivative `smCovD` (a bilinear form whose non-abelian structure is the generator
  action `tgen`/`ygen` on the doublet, a multiplication by given matrices, needing no bracket
  identity).  The fermions are not part of `smHamiltonian`, so they play no role here either.

  **But the §2.3 inequality is now proved unconditionally for the quartic `:N²:` form**
  (2026-10-30) — the form the magnetic potential itself produces (see the cross-term computation
  above).  `barrierForm_le_linear` bounds the barrier linearly in the occupation
  (`rootCount·zeroPoint g N ≤ K (N+1)`, `K = rootCount·g/2`, from `zeroPoint_le_linear`), and
  **`barrierBound_quartic`** (`BookProof/YangMillsEffectiveBarrier` §6) is the instance
  `IsBarrierBound T g (quarticDegreeForm)` with the explicit shift `C = K + (1 + K)²/4`: the quartic
  grows like `N²` and pays for the kinetic degree form *and* the `√N` barrier at once.  Through the
  existing chain this gives `quarticFormDomination` (a `FormDomination` for the pure interaction
  form, ratio `c₁`, shift `c₁μ₀ + C`) and **`quartic_certified_gap`**: on the vacuum-orthogonal
  sector `c₁ Δ_ref · ‖c‖² ≤ q_N²(c) + C‖c‖²`.  So in the `:N²:` model the separation `c₁ Δ_ref` no
  longer depends on the unproved estimate; what remains is the identification `q_W = q_N²` itself.
  Nothing here claims a discrete spectrum for `H_W`.

---

### Phase 3: Construction of a Solvable Gapped Reference Operator $H_{\text{ref}}$

Rather than attempting to calculate the spectrum of $H_W$ exactly, construct a reference operator $H_{\text{ref}}$ that satisfies three conditions:
1. It is explicitly solvable on the product Hermite core (e.g., an anisotropic harmonic oscillator or a radially symmetric gapped system).
2. Its eigenvalues and spectral gaps are known in closed form:
   $$\sigma(H_{\text{ref}}) = \{\mu_0, \mu_1, \mu_2, \dots\}, \quad \mu_1 - \mu_0 \ge \Delta_{\text{ref}} > 0$$
3. It lower-bounds $H_W$ at the quadratic-form level.

#### 3.1. Construction of $H_{\text{ref}}$
On the $d_N$-dimensional Gauss–polynomial core (PDF Ch. 27.9, where $d_3 = 99$ for $SU(3)$):
$$H_{\text{ref}} = \sum_{k=1}^{d_N} \left( -\frac{\partial^2}{\partial x_k^2} + \omega_k^2 x_k^2 \right) + V_0(P)$$
where:
* $\omega_k > 0$ are the harmonic frequencies of the background Gaussian measure (`PhysHSGaussian`).
* $V_0(P)$ is a parity/charge projection that assigns energy $0$ to the vacuum state $\Omega$ and energy at least $\Delta_{\text{ref}} = \min_k \omega_k$ to any state orthogonal to $\Omega$ (or odd under parity).

#### 3.2. Milestone 3: Closed-Form Spectrum of $H_{\text{ref}}$
* **Task:** Formalize the spectrum of $H_{\text{ref}}$ in Lean 4 using the existing harmonic oscillator theorems (`BookProof.HarmonicOscillator.harmonicOscOp`):
  ```lean
  theorem href_spectral_gap (k : ℕ) :
    ∀ ψ ∈ D(H_ref), ψ ⊥ Ω → ⟨ψ, H_ref ψ⟩ ≥ (μ₀ + Δ_ref) ‖ψ‖²
  ```
* **Deliverable:** `BookProof.ChapterReferenceGap.lean`.
* **Status (2026-10-30): DONE**, `BookProof.ReferenceGap` (`BookProof/ChapterReferenceGap.lean`, no `sorry`).
  The `d`-dimensional symbol `refEnergy ω n = ∑ i, ωᵢ (nᵢ + ½)` is a port of physlib's
  `QuantumMechanics.HarmonicOscillator.eigenEnergy` (`ℏ = 1`, general `ω`) together with
  `refEnergy_strictMono`; at `d = 1`, `ω = 1` it is this repository's `harmonicSymbol`
  (`refEnergy_one_eq_harmonicSymbol`), so it sits on `harmonicOscOp`.  The gap is
  `refGap ω = min_k ω_k`, positive and attained (`refGap_pos`, `exists_refGap_eq`), and every
  excited level clears the vacuum by it (`refEnergy_ge_vacuum_add_gap`).  On the
  Gauss–polynomial core (finite coefficient families `(Fin d → ℕ) →₀ ℂ`) the milestone is
  `href_spectral_gap` with `coreNormSq`/`coreForm` as `‖ψ‖²` and `⟨ψ, H_ref ψ⟩`, the parity
  sector is `href_spectral_gap_of_parity`, and the bound is attained at the vacuum
  (`coreForm_vacuum`), so `Δ_ref` is the exact gap there.  Not done here: the `L²` closure
  of the core (basis expansion/summability) and the Phase-4 form domination.

---

### Phase 4: Relative Form Bounding in Lean 4

Once $H_{\text{ref}}$ is constructed, the analytical lower bound on the separation $\beta_\infty$ is derived by proving that $H_W$ dominates $H_{\text{ref}}$ in the sense of quadratic forms.

#### 4.1. The Form-Domination Inequality
Prove that there exist constants $c_1 > 0$ and $c_2 \in \mathbb{R}$ such that on the common core $\mathcal{D}$:
$$q_{H_W}(\psi) \ge c_1 \, q_{H_{\text{ref}}}(\psi) - c_2 \|\psi\|^2 \quad \forall \psi \in \mathcal{D}$$

By the variational minimax principle (Courant–Fischer):
* Ground state: $\lambda_0(H_W) \ge c_1 \mu_0 - c_2$.
* First excited state (or lowest state in the orthogonal/odd sector): 
  $$\lambda_1(H_W) \ge c_1 \mu_1 - c_2$$
* Subtracting the two yields the **rigorous, parameter-independent lower bound on the spectral separation**:
  $$\beta_\infty - \theta_\infty \ge \lambda_1(H_W) - \lambda_0(H_W) \ge c_1 (\mu_1 - \mu_0) = c_1 \Delta_{\text{ref}} > 0$$

#### 4.2. Leveraging Existing *Timepiece* Modules
This step directly integrates into existing modules:
* Use `BookProof.ChapterFockFieldPerturbation.lean` to control the cross-terms between linear gradients and the cubic/quartic non-Abelian potential.
* Use `BookProof.ChapterFockInteractionStability.lean` to convert relative form bounds into explicit spectral shift inequalities.

#### 4.3. Milestone 4: Form-Domination Certificate
* **Task:** Prove in Lean 4:
  ```lean
  theorem ym_form_dominates_href :
    ∃ (c₁ : ℝ) (c₂ : ℝ), c₁ > 0 ∧
    ∀ ψ ∈ D_core, quadForm H_W ψ ≥ c₁ * quadForm H_ref ψ - c₂ * ‖ψ‖²
  ```
* **Deliverable:** `BookProof.YangMillsFormDomination.lean`.* **Status (2026-11-04): the implication, the domination inequality on the Gauss–polynomial core,
 the `L²` closure of that core, the Faris–Lavine comparison for a non-diagonal interaction, and
 the `L²` lift of the *interacting* form — its bottom bound *and* its Faris–Lavine comparison
 with relative bound `a < 1`, on the form domain — are DONE** (`BookProof.YangMillsFormClosure`,
 `BookProof.YangMillsFormClosureNonDiagonal`); what remains open is the *uniformity in the
 cut-off* of the Hilbert–Schmidt / relative bound, as described at the end of this item.
  `BookProof.YangMillsFormDomination` (`BookProof/YangMillsFormDomination.lean`, no `sorry`)
  carries the certificate as a structure, `FormDomination ω q` = ratio `c₁ > 0`, shift `c₂`, and
  `∀ c, c₁ · coreForm ω c − c₂ · coreNormSq c ≤ q c` on the Phase-3 core.
  `coreForm_ge_vacuum` puts the vacuum at the bottom of the reference form, so domination also
  bounds the ground level: `ground_bound` gives `c₁μ₀ − c₂`, `excited_bound`
  (`c 0 = 0`) gives `c₁(μ₀ + Δ_ref) − c₂`, and `certified_separation`/`certified_gap_pos` show
  the difference is exactly `c₁ Δ_ref > 0` — the uniform separation `β_∞ − θ_∞`.  The certificate
  is inhabited (`formDomination_self`, `q_ref` dominates itself), so the structure is not
  vacuous.  A **concrete, non-self-referential inhabitant** is `freeFormDomination`: the free
  (quadratic) part's form on the Hermite core — the *degree* form
  `degreeForm c = ∑ n, (∑ i, nᵢ)‖c n‖²`, i.e. the form of `−Δ` in oscillator units — dominates
  the reference form with ratio `c₁` and shift `c₂ = c₁μ₀` whenever `0 < c₁` and `c₁ωᵢ ≤ 1`
  (`scaled_refEnergy_sub_zero_le_degree` is the pointwise inequality; `exists_free_ratio`
  shows such a `c₁` always exists).  That instance yields a concrete gap:
  `degreeForm_ge_gap` — on the vacuum-orthogonal sector the kinetic form is at least
  `c₁Δ_ref · ‖c‖²`.  The **interacting (quartic) part** enters through monotonicity, not through a
  new estimate: the magnetic term is a sum of squares, so its form is nonnegative, and
  `FormDomination.mono` (a certificate for `q` is one for any `q' ≥ q`) shows it cannot spoil the
  comparison — `interactingFormDomination` is the certificate for
  `degreeForm + quarticDegreeForm` (`quarticDegreeForm` is the normal-ordered `:N²:` quartic),
  and `interactingForm_ge_gap` keeps the gap.  The Yang–Mills form itself is the last piece, and it
  is supplied by Phase 2, not by a new estimate: `yangMillsFormDomination`
  (`BookProof/YangMillsMagneticQuartic.lean`, the section “The consequence for `q_W`”) is the certificate
  `BookProof.YangMillsFormDomination.FormDomination ω (yangMillsForm T g)` with ratio `c₁` and shift
  `c₂ = c₁μ₀ + quarticShift T g`, `quarticShift T g = K + (1 + K)²/4`, `K = rootCount T · g/2`, so
  the plan's `ym_form_dominates_href` is inhabited by the Yang–Mills form of record and not by a
  model of it.
  The route that produces it is Phase 2: `BookProof.YangMillsEffectiveBarrier.formDomination_of_barrier`
  shows that a bound `q_W ≥ degreeForm + barrierForm − C‖·‖²` (`IsBarrierBound`, the §2.3 milestone
  with Simon's zero-point barrier included) already yields the certificate, with shift `c₁μ₀ + C`,
  and `barrier_gap` then gives the same `c₁ Δ_ref` separation.  So the remaining inequality may be
  taken in either form; the barrier version is the one the physics argument naturally produces,
  and it is now *proved* for the quartic `:N²:` form (`barrierBound_quartic`) **and for `q_W` itself**
  (`barrierBound_yangMillsForm`, §2.3 above), so neither the interface nor its `q_W` instance is an
  assumption any more; it also holds with shift `0` (`barrierBound_yangMillsForm_zeroShift`: the
  quartic form is nonnegative and sits in `q_W` beside both terms the inequality needs).

  **What the completed inequality does *not* depend on, and what is still open.**  The components
  are derived, not assumed: `B_a` is `magComp` read off the nested pair `c† diag(A_a) c`
  (`sandwich_diag_magComp`, §2.3), `F = ∂A + g[A,A]` splits on the corpus's own `magPoly`
  (`magPoly_eq_deriv_add`, `magComm_eq_zero_of_symmetric`, and the `smMagG`/`smMagW` twins), and
  the root sector is quartic with energy `‖a₁b₂ − b₁a₂‖²` (`rootField_commutator`, `root_energy`,
  `root_energy_eq_zero_iff`) — so the field-strength components and the root-mode structure are not
  inputs of §4.3, and the inequality needs neither the unbounded charge of Phase 1 nor the
  perturbation theory of §4.2.  The **`L²` closure of the Gauss–polynomial core** — the step this
  paragraph used to name as open — is now proved in `BookProof.YangMillsFormClosure`
  (`BookProof/YangMillsFormClosure.lean`, no `sorry`).  `L2 d = ℓ²(Idx d, ℂ)` receives the core by
  `coreEmbed` with `‖coreEmbed c‖² = coreNormSq c` (`norm_sq_coreEmbed`) and dense range
  (`dense_range_coreEmbed`, from `lp.hasSum_single` and the truncations).  All forms of the
  chapter are diagonal in the multi-index, `diagonalForm f c = ∑ n ∈ c.support, f n ‖c n‖²`, and
  the closed form `closedForm f x = ∑' n, ofReal (f n) · ofReal (‖x n‖²)` is *the closure of the
  core form*: it extends it (`closedForm_coreEmbed`), it is lower semicontinuous
  (`lowerSemicontinuous_closedForm`), and it is the supremum of the core forms of the truncations
  (`closedForm_eq_iSup_truncate`).  Domination transfers with no loss: `formDomination_symbol`
  reads a certificate as the symbolwise inequality `c₁μ(n) − c₂ ≤ g(n)`, and
  `formDomination_closed` gives
  `ofReal c₁ · closedForm μ x ≤ closedForm g x + ofReal (max c₂ 0) · closedNormSq x` for every
  `x : L²`.  The form of record is covered: `yangMillsForm T g` is diagonal
  (`Barrier.yangMillsForm_eq_diagonalForm`), so `yangMillsForm_closed` transfers its certificate
  and `closed_yangMillsGap` gives the `c₁Δ_ref` separation on the whole vacuum-orthogonal sector
  of `L²`.  What the closure still does not supply is the statement about the *spectrum* of `H_W`
  — discreteness and a mass gap need the self-adjoint operator, not only its closed form.

  **The non-diagonal interaction, on the core and on `L²` (2026-11-04).**  The second half of that boundary —
  "not for a magnetic interaction mixing multi-indices" — is addressed in
  `BookProof.YangMillsFormClosureNonDiagonal` (`BookProof/YangMillsFormClosureNonDiagonal.lean`, no
  `sorry`), and by the *Faris–Lavine* route rather than the termwise one.  The interaction is a
  kernel `K : (Fin d → ℕ) → (Fin d → ℕ) → ℂ` with kernel form
  `kernelForm K c = ∑ m ∈ supp c, ∑ n ∈ supp c, Re(K m n · c n · conj(c m))`, which couples
  distinct multi-indices whenever `K` is off the diagonal — the magnetic terms the diagonal theory
  cannot see.  The form bound the interaction enters through is a **Hilbert–Schmidt** one:
  `kernelForm_sq_le` is the two-index Cauchy–Schwarz inequality (square of the absolute form ≤
  Hilbert–Schmidt sum × `coreNormSq²`), so a kernel whose finite-square sums are bounded by `σ²`
  obeys `abs_kernelForm_le_of_hs`: `|kernelForm K c| ≤ σ · coreNormSq c` for **every** core state,
  with no support restriction.  `farisLavine_domination` is the comparison itself: if `q'`
  dominates the reference form with ratio `c₁` and shift `c₂`, and `|qK| ≤ a q' + b‖·‖²` with
  relative bound `a < 1`, then the **sum form** `q' + qK` dominates with ratio `(1 − a)c₁ > 0` and
  shift `(1 − a)c₂ + b` — the interaction may lower the form, and the factor `1 − a` is what that
  costs; the ratio never reaches zero, so the certified separation survives.  The bounded case is
  separate and sharper in the ratio: `farisLavine_of_bounded_interaction` (`a = 0`) keeps `c₁`
  unchanged and adds only `b` to the shift.  A concrete, genuinely off-diagonal instance is
  `hoppingKernel m₀ n₀` (the matrix unit at `(m₀, n₀)`): its Hilbert–Schmidt sums are bounded by
  `1` (`hoppingKernel_sq_sum_le`), so `abs_hoppingForm_le` gives the form bound with `σ = 1`, and
  **`hopping_farisLavine`** concludes that the Yang–Mills certificate plus the hopping interaction
  still dominates with the *same* ratio `c₁` and shift `c₂ + 1`.  `hopping_couples` shows the
  interaction really does read a product of coefficients rather than moduli — at `a₀ = b₀ = 1` it is
  `1`, at `a₀ = 1, b₀ = i` it is `0`, although both states have the same coefficient moduli — so no
  diagonal form can represent it.  **The `L²` lift of the interacting form is proved (2026-11-04)**:
  §5 of the same module defines `closedKernelForm K x` as the weighted double series over all of
  `Idx d × Idx d` (absolutely convergent for every `x : L²`), bounds it by `σ‖x‖²` for the *same*
  `σ` (`abs_closedKernelForm_le`, Hölder with exponents `2, 2`), identifies it with `kernelForm` on
  the core (`closedKernelForm_coreEmbed`), and proves the bottom bounds on the form domain:
  `closed_diagonal_add_kernelForm_ge` and `closed_sector_bottom_ge_interacting`.  So, *when the
  total Hilbert–Schmidt mass is finite*, the off-diagonal interaction is a bounded form
  perturbation of the closed diagonal form — continuous, hence closed on the same domain — and
  Phase 5's bottom statements hold on `L²`, not only on the core.  The **ratio** is carried over
  as well, in §6: `closed_farisLavine_domination` states `c₁ (closedForm μ x).toReal ≤
  (closedForm g x).toReal + closedKernelForm K x + shifts` with the relative bound `a < 1` intact,
  the finiteness `closedForm g x ≠ ⊤` being the only extra hypothesis.  What remains is uniformity
  in the cut-off: §7 shows the magnetic ladder's Hilbert–Schmidt mass is at most `d² C Λ^(d+1)` at
  cut-off `Λ` (`magCutoffKernel_hs_mass`), hence a constant of order `Λ^{(d+1)/2}` — so the `a = 0`
  branch is cut-off-local and the continuum has to use `a < 1` with `a` uniformly bounded away from
  `1`, which is not yet proved.  So
  Phase 5's `c₁Δ_ref` is certified on the core for the off-diagonal case, and on `L²` for the
  diagonal one at full strength — with the interacting term bounded below on `L²` by `−σ‖x‖²`,
  which preserves the *bottom* and not yet the *ratio* of the separation.

---

### Phase 5: Discharging Hypotheses in the Verification Pipeline

With $c_{\text{sep}} = c_1 \Delta_{\text{ref}} > 0$ established analytically:

#### 5.1. Supplying the Missing Input to Temple's Inequality
In `BookProof.ChapterRitzCertificate.lean`, replace the open hypothesis with the analytical bound:
$$\beta_\infty := \theta_\infty + c_1 \Delta_{\text{ref}}$$
The Temple denominator is now uniformly bounded away from zero for **all** approximation orders $n$:
$$\beta_n - \theta_n \ge \frac{1}{2} c_1 \Delta_{\text{ref}} > 0 \quad \forall n \ge n^*$$
Consequently, the Temple uncertainty:
$$\delta_n = \frac{\eta_n^2}{\beta_n - \theta_n} \le \frac{2 \eta_n^2}{c_1 \Delta_{\text{ref}}}$$
is strictly controlled. 

* **Status (2026-10-30): §5.1 is DONE; §5.2's arithmetic is DONE, its analytic transfer is not.**
  `BookProof.TempleSeparationBound` (`BookProof/Sirk/ChapterTempleSeparationBound.lean`) now carries
  the uniform residual bound: `temple_uncertainty_le_of_residual` proves §5.1's
  `δ_n = ε_n²/(β_n − θ_n) ≤ ε_n²/c ≤ η_n²/c` under `β − θ ≥ c`, and
  `certified_edge_of_uniform_residual` is the certificate statement `θ − η²/(c₁Δ_ref) ≤ l` with
  the analytic constant.  §5.2's displayed inequality is
  **`continuum_gap_unconditional`**: with `c₁, Δ_ref > 0`, a uniform residual `η_max` on the
  odd-sector vector and the variational upper bound `l_even ≤ θ_even`, the gap obeys
  `(θ_odd − θ_even) − 2η_max²/(c₁Δ_ref) ≤ l_odd − l_even`, and `continuum_gap_positive` shows it
  is strictly positive once the Ritz separation exceeds the correction — so the denominator no
  longer degrades with the order.  The transfer across the limit is in
  `BookProof.TempleContinuumGap` (`BookProof/Sirk/ChapterTempleContinuumGap.lean`): a spectral
  separation gives a *quantitative* gap at the window centre, `gapAt_of_separation`
  (`((β−l)/2)‖x‖ ≤ ‖(A − (l+β)/2)x‖`, from Pythagoras plus the Temple factor
  `factor_nonneg_of_separation`), at the plan's constant `gapAt_of_form_domination`
  (`c₁Δ_ref/2` at `l + c₁Δ_ref/2`), and by `SpectralGapStability.gapAt_of_tendsto` it survives an
  **operator-norm** limit unchanged (`gap_survives_norm_limit`), leaving a hole
  `c₁Δ_ref/2` in the limit's spectrum (`notMem_spectrum_of_separation_limit`,
  `continuum_gap_of_form_domination`).  The **strong-resolvent** mode of the same hypothesis is
  proved too (§6 of the chapter, 2026-10-31): `certifiedResolvent` is the left inverse of
  `A − λ` the gap guarantees, with `certifiedResolvent_left` and `certifiedResolvent_norm`
  (`‖Rξ‖ ≤ ‖ξ‖/d`); `gap_survives_strongResolvent` turns **pointwise** convergence of those
  certified resolvents to a left inverse of `B − (l+b)/2` into `GapAt B ((l+b)/2) ((b−l)/2)`,
  **without** assuming the uniform bound (it is `certifiedResolvent_norm`, read off the
  separation), and `continuum_gap_of_form_domination_strongResolvent` is the same at the plan's
  constant `c₁Δ_ref/2`, together with the spectral hole
  (`notMem_spectrum_of_strongResolvent_limit`).  The uniform bound is therefore free in both modes;
  what is still conditional is the uniform `SpectralSeparation` at the analytic constant, as §5.1
  assumes, and the fact that the truncation family converges at all — in either mode.

#### 5.2. Transferring Across the Strong-Resolvent Limit
Because $H_n \to H_F$ strongly in the resolvent sense (`weyl_hashimoto_selects_friedrichs`), apply the strong-resolvent spectral theorem (derived from Reed–Simon VIII.24 as discussed in the previous section):
```lean
theorem continuum_gap_unconditional :
  gap(H_F) ≥ (θ_odd - θ_even) - (2 * η_max² / (c₁ * Δ_ref)) > 0
```
This lifts through `ChapterFockNumberPreservingGap.lean` (`dGamma`), formally establishing that the full interacting continuum Hamiltonian possesses a strictly positive mass gap.

* **Status (2026-10-31): the nested-Fock lift, the coincident-point product and both convergence
modes (operator-norm and strong-resolvent) are now proved; the analytic separation and the fact
that the truncations converge are not.**  `BookProof.TempleContinuumGap`
  (`BookProof/Sirk/ChapterTempleContinuumGap.lean`) §3–4 put the lift on the actual Timepiece
  structure rather than beside it:
  - *nested Fock space / number conservation.*  A separation `spec T ⊆ {l} ∪ [β, ∞)` bounds the
    one-particle operator below (`sub_const_nonneg`, `form_gap_of_separation`), and
    `nestedFock_gap_of_separation` / `nestedFock_gap_of_certified_edge` lift it to the nested Fock
    space: `dΓ(opCol b A)` — built from `a†_j a_k` only, hence outer-particle-conserving —
    annihilates the vacuum and has Fock gap `l` on every vacuum-orthogonal finite-occupation
    state.  At the plan's constant the same theorem also delivers the one-particle `GapAt` of
    §5.1, so the two sides meet in one statement.
  - *the same-point product of outer fields.*  The interaction is a polynomial in the fields, so
    its coefficients contain products at a coincident Euclidean point, where a product of
    distributions is ambiguous.  The formalism never forms it: `dft_samePointProduct` (the
    product-to-convolution theorem) makes the momentum transform of the same-point product the
    convolution `n⁻¹ Σ_p F̂(p) Ĝ(k−p)`; `dft_mul_momentumCol` shows multiplication by a symbol is
    the momentum-transfer matrix `(k,i) ↦ n⁻¹V̂(k−i)` — an ordinary number-preserving
    one-particle matrix; `momentumCol_samePointProduct` shows the coefficient of a product of two
    fields is itself the convolution `n⁻² Σ_{p+q=k−i} F̂(p) Ĝ(q)`, every term carrying conserved
    momentum; `samePointProduct_form_eq_momentum` identifies the *form* the Phase-4 domination
    evaluates with that momentum convolution (Plancherel, `sum_conj_dft_mul_dft`); and
    `samePointProduct_real_self_form_nonneg` gives the positivity of the squared real field, i.e.
    the `IsPosCol`-shaped input the `dΓ` lift consumes.
  - *the strong-resolvent mode of the transfer.*  Both modes of §5.2's hypothesis are now proved:
    the operator-norm one (`gap_survives_norm_limit`) and the strong-resolvent one (§6:
    `gap_survives_strongResolvent`, `notMem_spectrum_of_strongResolvent_limit`,
    `continuum_gap_of_form_domination_strongResolvent`), the latter from pointwise convergence of
    the certified resolvents alone — strong-resolvent convergence is *weaker* than norm
    convergence, so this is the mode a truncation family actually delivers.
  - *What is still open.*  The uniform separation at `c₁Δ_ref` (Phases 1–4), the fact that the
    truncations converge to the limit in either mode (the chapter proves the transfer, not the
    convergence), the identification of the Yang–Mills one-particle operator with the abstract
    `T`, and the Källén–Lehmann/clustering step that would read the gap off the Euclidean
    two-point function.  No strictly positive mass gap of the physical continuum Hamiltonian is
    claimed.

---

### Summary of Tasks and Timeline

| Phase | Mathematical Objective | Lean 4 Target Module | Key Tools / References |
| :--- | :--- | :--- | :--- |
| **Phase 1** | Project out longitudinal gauge zero-modes via BRST cohomology | `BookProof.BrstReducedTransfer` | Nilpotent BRST charge $\Omega^2 = 0$ |
| **Phase 2** | Prove Simon channel-taming along Cartan flat directions | `BookProof.YangMillsEffectiveBarrier` | Transverse zero-point energy $\sim g|A|$ |
| **Phase 3** | Construct solvable gapped comparison operator $H_{\text{ref}}$ | `BookProof.ChapterReferenceGap` | `HarmonicOscillator.lean`, $SU(N)$ Hermite basis |
| **Phase 4** | Establish form-domination $q_{H_W} \ge c_1 q_{H_{\text{ref}}} - c_2$ | `BookProof.YangMillsFormDomination` | `ChapterFockFieldPerturbation.lean` |
| **Phase 5** | Inject analytical $\beta_\infty$ into SIRK/Temple certificate | `BookProof.SpectralGapStability` | `ChapterRitzCertificate.lean`, Trotter–Kato |

By following this plan, you replace the fragile numerical search for a separation constant with a **classical, non-perturbative coercive barrier** (the Simon mechanism on flat directions), providing the missing analytic constant that prevents the Temple uncertainty from blowing up in the infinite limit.
