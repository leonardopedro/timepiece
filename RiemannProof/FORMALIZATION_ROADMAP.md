# Formalization Roadmap for `book.tex`

**Purpose.** This document collects, chapter by chapter, every mathematically
formalizable statement in `book.tex` together with a *detailed English proof*
written so that an LLM-Lean specialist can implement it in Lean 4 / Mathlib
without having to reconstruct the mathematics. It is the single master
reference requested by the author.

**Explicitly out of scope (author's instruction).** Do **not** formalize:
- Ch. "Resolution of the singularity of the ODE x'=x²" (line 932) — has flaws to be corrected.
- Ch. "Selecting events is not rewriting the history of events" (line 8303) — the P≠NP chapter, flaws to be corrected.
- Ch. "Statistical Model Theory and Bayesian priors where the Riemann Hypothesis is true" (line 10536) — handled separately in `RcpEuler.lean`; skip here.

**Coverage policy.** Math-dense chapters (real theorem–proof content) are done
first and in full. Pure-physics *derivations* (Yang-Mills quantization, gravity,
Navier–Stokes free-field constructions, phase-space Euler-formula constructions)
are mined only for discrete, self-contained lemmas; the surrounding physical
modelling is flagged as non-formalizable and left as prose.

**Coverage revision (author's instruction, 2026-07-02).** The chapter *"Gauge
symmetry and dissipative dynamics in probability spaces"* (book line 2128) is
**promoted from "triaged non-formalizable" to a full work package**: the
definition of gauge transformations and their properties are important and *are*
formalizable. See the new **Chapter G** section below (queue item **N6**) — it
contains the full definition/property list with English proofs and pinned
Mathlib names, sized comparably to Chapters B–E combined.

**Coverage revision (author's instruction, 2026-07-06) — two `../unfer`
algorithms promoted to flagship work packages.** The author has flagged that
*"there are many chapters in `book.tex` still unformalized"* and that **"the
`Hashimoto.tex` and `QFM.tex` algorithms are very important and can be
formalized."** Both source documents live in the sibling repo `../unfer`
(the Rust reference implementation governed by §0 S7):
`../unfer/Hashimoto.md` (Hashimoto–Nodera, *Shift-invert Rational Krylov (SIRK)
method for an operator φ-function of an unbounded operator*, JJIAM 2019 — the
numerical-analysis backbone that `book.tex` cites at lines 1147 and 2055 to
justify the finite-energy/Krylov-convergence argument) and `../unfer/QFM.tex`
(*Wavefunction Flows in the `unfer` Kernel* — Quantum Flow Matching, the
generative-flow architecture built on the Mehler/Hashimoto/Fock formalism,
implemented in `../unfer/qfm/`). These become the two **new flagship packages
N13 (Hashimoto SIRK) and N14 (QFM)** — each large, self-contained, and
**heavily guided** (many independent sub-deliverables, per the volume mandate),
sitting at the **front of the queue**. Full English-proof specs with pinned
Mathlib names are in the N13/N14 queue entries below. Both follow §0 S7 (the
`../unfer` Mehler/Kopperman formalism) and reuse the on-disk Fock layer
(N12/`ChapterF1`) and Mehler chain (`PnpProof/SphereGaussian.lean`).

---

## ★ IMPLEMENTATION STATE (2026-07-06) — `BookProof` is on disk, 60 modules; the ENTIRE original queue N1–N12 (incl. N7(c)) is DONE; the only open work is the two NEW packages N13 (Hashimoto SIRK) + N14 (QFM)

**Thirty-nine waves of execution passes are complete** and the whole original
work-package queue is exhausted. **Waves 38–39 (2026-07-05/06, after the
wave-37 snapshot below) closed the last three items** — see
`ARISTOTLE_SUMMARY.md` (runs through `c14d1ff7`) and `BookProof/STATUS.md`:
- **Wave 38: N11 DONE + N12 DONE + S7 hygiene DONE.** `ChapterA4h.lean` +
  `ChapterA3w.lean` (the Wigner/Mackey/Weyl exhaustiveness bundle — external
  theorems as named hypotheses, conditional headlines proved) and
  `ChapterF1.lean` (the S7 Bargmann–Fock/CCR field package: `a = d/dX`,
  `a† = X·`, `[a,a†]=1`, number operator `numberOp`, the headline
  `quadratic_ordering_vacuum` `⟨0|H|0⟩ = 0` vs `symmetric_ordering_vacuum` `½`,
  BRST bridge). 8113 jobs green.
- **Wave 39: N7(c) DONE.** `ChapterF2.lean` (the Bargmann–Fock **mass gap**:
  `H := a†a = numberOp`, `H Xⁿ = n·Xⁿ`, vacuum energy `0`, gap `Δ = 1`,
  `deformedHamiltonian c := c•N` with `[H_c, N] = 0`). Latest re-verification
  run `c14d1ff7`: **8114 jobs green**, `BookProof` fully `sorry`/`axiom`-free.

**⇒ The original roadmap queue (N1–N12, including N7(c)) is now 100 % complete.
The genuinely open work is the two NEW, author-prioritized (2026-07-06)
flagship packages: N13 (Hashimoto SIRK, `../unfer/Hashimoto.md`) and N14 (QFM,
`../unfer/QFM.tex`).** Both are fully specified with English proofs + pinned
Mathlib names in the N13/N14 queue entries below; N14 reuses the on-disk
`ChapterF1.numberOp` (N12) and `PnpProof/SphereGaussian.lean`.

**The wave-4–37 base (56 modules) is recorded below for provenance:**

**Thirty-seven waves of execution passes** produced the 56-module base (see
`ARISTOTLE_SUMMARY.md` and `BookProof/STATUS.md`). Waves 1–3 (2026-07-02/03)
built the 20-module base recorded in the historical table below (N5, N6, N8,
§A.2 trichotomy, most of N1/N3). **Waves 4–37 (2026-07-03 → 2026-07-05, runs
`8296bfb3` … `e3a68ecc`, all committed & pushed) closed out the entire
queue:**

- **Wave 4** (`8296bfb3`): **N9 DONE** (`ChapterG2.lean`, G.8–G.12 all proved,
  incl. the Gribov headline `no_continuous_gauge_fixing_circle` and the BRST
  splitting `brstCohomology_equiv` + `brst_physical_iff_gauge_invariant`) and
  **N10 DONE** (`ChapterB7.lean`, B7.1–B7.4 incl.
  `koopman_indicatorConstLp` and `hadamard_not_deterministic`).
- **Waves 5–6** (`b7e12fd4`, `169671c5`): **N2 DONE IN FULL** — Prop 15
  (`ChapterA2d.lean`, `Rreal_isometric_iff_complexification_isometric`) and
  Prop 16 (`ChapterA2e.lean`, both the C-complex and C-pseudoreal
  dichotomies, using a proved Frobenius–Schur orthogonality
  `theta_inner_self_zero` and quaternion `rot` operators).
- **Waves 7–8** (`427d165b`, `e708899c`): **N1 DONE IN FULL** — the recorded
  `Y ⊥ JY` crux was dissolved by running Frobenius–Schur through the
  `ChapterA2c` linear/antilinear decomposition: `ChapterA1g.lean`
  (`realification_irreducible_of_not_isCReal`, `realification_irreducible_iff`,
  `realification_classification`) + `ChapterA1h.lean` (R-type trichotomy
  `rType_exhaustive` on the real side, `cxSystem_reducible_of_commuting_rImaginary`).
- **Waves 9–14, 18, 21** (`f422e952` → `92a957cc`, `444809e4`, `2d165ad4`):
  **§A.3 Lemma 48 COMPLETE in the concrete model** — `ChapterA3b` (Lemma 40
  charge conjugation; Prop 37 `real_pauli` around the `EXTERNAL`
  `PauliFundamental` named hypothesis; Prop 46 metric core), `ChapterA3c`
  (`Λ : Pin(3,1) → O(1,3)` as a 2-to-1 surjective homomorphism), `ChapterA3d`
  (Def 49, Ω double-covers Δ), `ChapterA3e` (Lie algebra `𝔰𝔭𝔦𝔫⁺(3,1)`,
  `Λ_*`), `ChapterA3f` (**`det_exp_eq_exp_trace`** — the Jacobi–Liouville
  formula, closing a listed Mathlib TODO), `ChapterA3g` (adjoint-exponential
  identity by a matrix-ODE argument; `spinLie_exp_hasLambda_lorentz`),
  `ChapterA3h` (Note 47, `Υ : SL(2,ℂ) → O(1,3)`), `ChapterA3i` (the Σ bridge
  **`lemma48_bridge`**: `Λ(Σ T Σ⁻¹) = Υ(T)`).
- **Waves 23, 26–37** (`06dab516`, `b3e483a9` → `e3a68ecc`): **Lemma 52
  machinery COMPLETE** — `ChapterA3j` (chiral γ⁵ base case, headline
  `chirality_not_parity_invariant`), `ChapterA3k` (tensor-square chirality
  blocks, `projLL_not_parity_invariant`), `ChapterA3l`/`A3m` (S₂/S₃
  braiding), `ChapterA3n`/`A3o`/`A3p`/`A3q` (arbitrary-`N` symmetrizer /
  antisymmetrizer / `N = 2` decomposition / `projMixed` complete system,
  headline `tensorPow_complete_reducibility`), `ChapterA3r`–`A3v` (projector
  ranks = summand dimensions at `N = 2,3,4,5,6` via the general orbit-count
  lemma `card_fixedTuples`; e.g. `20+4+40 = 64`, `84+0+4012 = 4096`).
- **Waves 15–17, 19–20, 22, 24–25** (`81e63149` → `8e508b5a`): **§A.4–A.5
  cores DONE + N3 DONE** — `ChapterA4` (Props 73/74/76 Majorana–Fourier
  unitarity via Plancherel + Θ-conjugation), `ChapterA4b` (Prop 61 unitarity,
  C*-algebra/CFC), `ChapterA4c`/`A4d` (Prop 79 little groups: massive =
  `SU(2)`, massless = `SE(2)`), `ChapterA4e` (Prop 88/Cor 1 core:
  energy-sign projectors, `energy_sign_not_conserved` — antiparticles),
  `ChapterA4f` (Prop 87's three exclusions incl. `no_tachyon`,
  `infinite_spin_excluded`), `ChapterA4g` (Prop 81 rep group laws),
  `ChapterA5` (CPT/energy-symbol mass-shell `energySymbolZ_sq`), plus
  `ChapterB3b` (**`denseCore_svd`** — finite-rank SVD `A = W·diag D·Uᴴ`) and
  the B.3c `conditional_operator_identity` added to `ChapterB3` — **N3 DONE**.

Everything is **`sorry`-free and `axiom`-free** (only `propext`,
`Classical.choice`, `Quot.sound`; checked per-wave with `#print axioms`);
`lake build` green (**8114 jobs as of the wave-39 re-verification run
`c14d1ff7`**, 60 modules; the only `sorry`s in the repo are the pre-existing
`RiemannProof/RcpEuler.lean` ones, out of scope here). Waves 38–39 (above)
added `ChapterA4h`, `ChapterA3w`, `ChapterF1`, `ChapterF2` — the N11, N12,
N7(c) closures.

**On disk after waves 1–3 (first 20 modules, root module `BookProof.lean`,
plus `STATUS.md`; the 36 wave-4–37 modules are listed in the wave summary
above and per-file in `BookProof/STATUS.md`):**

| File | Roadmap section (package) | Headline declarations |
|---|---|---|
| `BookProof/ChapterA.lean` | §A.0–A.2 foundational core | `System` (Def 1), `Commutes`, `IsNormal` (Def 24), `IsSubsystem`/`IsIrreducible` (Def 7); **Lemma 26** `orthogonal_isSubsystem`; **Lemma 27** `schur_normal_irreducible` (Schur property Def 13 = named hypothesis, per policy) |
| `BookProof/ChapterA1.lean` | §A.1 Def 8 scaffolding (N1) | `AntiUnitary V` (`V ≃ₗᵢ⋆[ℂ] V`) + `inner_map_map`/`comp_inner`; `IsConjugation` (Def 8.1), `IsRImaginary` (Def 8.2); `conjugation_avg_fixed`/`_antifixed`, `conjugation_decomp`, `rimaginary_orthogonal`, `rimaginary_symm_apply` |
| `BookProof/Complexification.lean` | §A.1 infrastructure (N1) | `Cx W` — complex Hilbert space structure on the complexification **built from scratch** (was "not in Mathlib"); `cxConj` anti-unitary involution, `cxMap` (operator complexification), `cxSystem`, `cxConj_isConjugation` (complexification of a real system is C-real) |
| `BookProof/ChapterA1b.lean` | §A.1 subspace correspondence (N1) | `Cx.complexify`/`Cx.realPart` with both round-trips + subsystem preservation; headline `irreducible_iff_no_conj_subsystem` (real irreducibility ⇔ no proper conjugation-invariant complex subsystem) |
| `BookProof/ChapterA1c.lean` | §A.1 C-type/R-type classification (N1) | Def 9 predicates `IsCReal`/`IsCPseudoreal`/`IsCComplex` + trichotomy `cType_exhaustive` + mutual exclusions; `cxSystem_isCReal`; `IsRReal` (Def 10) + **Prop 12 R-real case** `IsRReal.isIrreducible` |
| `BookProof/ChapterA1d.lean` | §A.1 realification dual (N1) | `rxMap`/`rxSystem` (restriction of scalars, via `rclikeToReal` as **local** instance), `Jmap` + `Jmap_sq`/`Jmap_isRImaginary`; `realSub`/`cplxSub` correspondence; headline `complex_irreducible_iff_no_Jinvariant_subsystem` |
| `BookProof/ChapterA2.lean` | §A.2 Lemma 14 (N2) | `CommutesUnitary`/`IsSchurUnitary` (Def 13, named predicate — never an axiom); **Lemma 14** `antiisometry_unique_up_to_phase` (two commuting anti-unitaries differ by a unit phase); `commuting_antiUnitary_scalar_multiple` |
| `BookProof/ChapterA3.lean` | §A.3 concrete model (N4) | `mgamma` (4×4 Majorana `iγ^μ`), `mgamma5`, `minkowski`, `dgamma`; `mgamma_clifford`/`dgamma_clifford` (Def 38, `decide` over ℤ then cast to ℂ), `mgamma_map_conj`, `mgamma_unitary`, `mgamma5_sq`/`_anticomm`/`_eq_prod` |
| `BookProof/ChapterB.lean` | §B.1–B.2 + **B.2′ (N3)** | `born_forward`, `born_backward`, `unit_vector_extends`; **`condKernel_disintegration`** (`ρ.fst.compProd ρ.condKernel = ρ`, the book's `p(y\|x)`) |
| `BookProof/ChapterC.lean` | §C.1 complete | `card_invertible`, `card_all`, `prob_invertible` (`n!/nⁿ`), `invertible_ratio_isEquivalent` (Stirling), `invertible_ratio_tendsto_zero` |
| `BookProof/ChapterD.lean` | §D.1 complete | `computable_countable`, `computable_bool_countable`, `computable_null`, `computable_bool_null` (atomless ⇒ computable functions null) |
| `BookProof/ChapterE.lean` | §E.1–E.4 complete | `cos_sq_surjective`, `exp_J`/`exp_J_mulVec`, `collapse_density`, `stochastic_uniform_to_vertex_singular`, `hadamard_uniformizes` (n=2), `exists_uniformizer` (general-n DFT "black hole"), `stickBreaking_surjective` |
| `BookProof/ChapterG.lean` | **Chapter G complete (N6 ✅)** | All of G.0–G.7: `gaugeGroup`, `gaugeOrbit_eq_fiber`, `gaugeInvariant_iff_factors`, `gaugeInvariantSubalgebra`/`gaugeInvariantOperators`, `expectation_gauge_invariant`, Dirac obstruction (`no_shift_invariant_probabilityMeasure`, `no_shift_invariant_unit_vector`), `exists_complete_gaugeFixing`, `haarAverage` + headline **`gauge_constraint_pushforward_full_measure`**, `BRST_nilpotent`, `koopmanEquiv`, `evolution_conserves_probability` |
| `BookProof/Substrate.lean` | **§0 glue complete (N5 ✅)** | `substrate_born_forward`, `substrate_born_backward`, `substrate_unit_vector_extends` — Ch. B instantiated at the `PnpProof` Kopperman substrate measure |
| `BookProof/ChapterU.lean` | **Chapter U complete (N8 ✅)** | **U.1 headline** `bornMeasure`/`conditionedState`/`born_conditioning` (Born collapse = `ProbabilityTheory.cond`); U.3 `prodEquiv : Sym(M×N) ≃ₐ[R] Sym M ⊗ Sym N` (Fock exponential, from two `lift`s + round-trips); U.4 `no_differentiable_trajectory`/`differentiable_trajectory_null` (around the `EXTERNAL` Lévy hypothesis, cited PWZ 1933/Bertoin 1994); U.5 `portfolio_risk_inv_sqrt`/`portfolio_std_inv_sqrt`; U.2 = cross-ref to `PnpProof/SphereGaussian.lean` |
| `BookProof/ChapterA1e.lean` | §A.1 `V ⊕ V̄` splitting (N1) | `JY` image subspace + involution `JY_JY`, closedness/invariance lemmas; headline **`realification_splits`** (a real subsystem of an irreducible complex system is trivial or splits `V` as the closure of `Y ⊕ JY`) + `proper_realification_subsystem_splits` |
| `BookProof/ChapterA1f.lean` | §A.1 R-real dichotomy (N1) | `conjFixed θ` real form as a subsystem of `V^r` (+ `ne_bot`/`ne_top`); headline **`realification_reducible_of_conjugation`**, `isCReal_realification_reducible`, `not_isCReal_of_realification_irreducible` |
| `BookProof/ChapterA2b.lean` | §A.2 Prop 17 (N2) | `IsSchurFull` (Schur named predicate), `commutant_eq_complex_scalars`; **Prop 17** `Rreal_commutant_eq_real_scalars` (R-real commutant = ℝ) + `CommutesConj` |
| `BookProof/ChapterA2c.lean` | **§A.2 Props 18–19 (N2 ✅ trichotomy complete)** | **Prop 18** `Rcomplex_realCommutant_eq_complex` (R-complex commutant = ℂ), **Prop 19** `Rpseudoreal_realCommutant_eq_quaternion` (R-pseudoreal commutant = ℍ, via `qembed : ℍ →ₐ[ℝ] (V →L[ℝ] V)` + `qembed_injective`); infrastructure `RealCommutes`, `mulI`, `thetaR`, `cembed`, `Plin`/`Qanti`/`cplxify` |
| `BookProof/ChapterB3.lean` | §B.3 partial-isometry API (N3) | `IsPartialIsometry` (`V V† V = V`) built from scratch (absent from Mathlib): `V†V`/`VV†` self-adjoint idempotents, `IsPartialIsometry.adjoint`, characterization `isPartialIsometry_iff_adjointComp_isIdempotent`, `norm_map_of_adjointComp_eq` |

**What remains open (2026-07-06). The ENTIRE original queue is exhausted —
N1–N12 are DONE (N11 + N12 in wave 38, N7(c) in wave 39) and N4's concrete/
algebraic content is DONE. The only genuinely open items are the two NEW,
author-prioritized flagship packages:**
- **N13 (NEW, 2026-07-06 — FLAGSHIP, author-prioritized: the Hashimoto SIRK
  package).** `../unfer/Hashimoto.md` formalized: the φ-functions and their
  recurrence, the exponential-integrator Duhamel identity, the resolvent /
  rational-Krylov algebra (the clean `X_j = (I + h(m−j)X_m)^{-1}X_m` identity
  and the rational-function characterization of the SIRK subspace), the
  Arnoldi/SIA/SIRK compression relations on the Kopperman core, and the SIRK
  `e^{-hm}` convergence headline *conditional* on a named `EXTERNAL` Crouzeix
  bound. A large package with ~12 independent deliverables — full spec in the
  N13 queue entry. Target `BookProof/ChapterH1.lean` (+ `ChapterH2.lean`)
  (both filenames verified free).
- **N14 (NEW, 2026-07-06 — FLAGSHIP, author-prioritized: the QFM package).**
  `../unfer/QFM.tex` formalized: continuity-Hamiltonian Hermiticity, the
  orthogonal-Fock disjoint-support identities, the diagonal-Gram closed-form
  `O(M)` training solution, exact commutativity/time-averaging, the vacuum
  projector (self-adjoint idempotent) and dressed-vacuum Bessel bound
  `Σεⱼ² ≤ 1`, the Mehler overlap `⟨0|xⱼ⟩ = εⱼ > 0`, and the tomographic-recovery
  algebra (Count-Sketch unbiasedness, unitary reduced flow, pseudo-inverse
  left-inverse). **Reuses the on-disk `ChapterF1.numberOp` (N12, wave 38) and
  `SphereGaussian.lean` — import, do not rebuild.** Another large package with
  ~12 deliverables — full spec in the N14 queue entry. Target
  `BookProof/ChapterF3.lean` (+ `ChapterF4.lean`) — **note `ChapterF1` (N12)
  and `ChapterF2` (N7(c) mass gap) are already on disk, so QFM uses F3/F4**.
- **DONE in wave 38 (no longer open): N11** — the Wigner/Mackey/Weyl
  exhaustiveness bundle, `ChapterA4h.lean` + `ChapterA3w.lean` (external
  theorems as named hypotheses, conditional headlines proved). **DONE in
  wave 38: N12** — the S7 Bargmann–Fock/CCR field package `ChapterF1.lean`
  (`quadratic_ordering_vacuum` headline). **DONE in wave 38: the S7 hygiene
  docstrings.** **DONE in wave 39: N7(c)** — the mass gap `ChapterF2.lean`.
  Their guided specs are retained below (now struck through as DONE) as
  documentation of what landed.
- **Beyond N13/N14: `book.tex` still has unformalized chapters** the author may
  promote next (author note 2026-07-06: "there are many chapters in `book.tex`
  still unformalized"). Treat the N13/N14 entries as the template for turning a
  cited algorithm into a fully-guided package when the author names the next one.
- **STOP RULE for the dimension-count thread**: waves 33–37 computed the
  complete-reducibility summand dimensions at `N = 2…6`; together with the
  general orbit-count lemma `card_fixedTuples` (any `N`, any `σ`) that thread
  is **closed**. Do NOT continue to `N = 7, 8, …` — additional instances add
  no new mathematics. Spend the pass on N13/N14 instead.
- E.5 is a cross-reference into §A.2 and is covered by the landed §A.2 files.
- Out of scope per this roadmap (not blockers): the fermionic
  (exterior-algebra) analogue of U.3 and the U.6 prose/software items.

**★ MANDATE for the next implementation pass (READ FIRST — author instruction
2026-07-03, still standing: "Make sure that there is a lot of guided work…
The last run was too fast to accomplish anything significant").** A pass that
lands a single package is an incomplete pass. Work through the queue below
**in order, landing SEVERAL work packages in one pass — target at least
four deliverable groups** — after finishing each, *continue to the next*;
re-verifying existing files does not count as progress, and (new, 2026-07-05)
**neither does another instance of an already-general result** — the
dimension-count thread is closed at `N = 6` (see the STOP RULE above), so a
pass consisting of `N = 7` and `N = 8` counts would be an empty pass.
**Restated 2026-07-06 (author, verbatim): "Make sure that there is a lot of
guided work for the LLM-Lean-specialist to do. The last run was too fast to
accomplish anything significant. Note that there are many chapters in
`book.tex` still unformalized (the `Hashimoto.tex` and `QFM.tex` algorithms
are very important and can be formalized)."** **The entire original queue
(N1–N12, including N7(c)) is already DONE (waves 4–39); the next pass is
exactly the two new flagship packages, and nothing else:** **N13** (the
Hashimoto SIRK package — `../unfer/Hashimoto.md`, ~12 deliverables H1.1–H2.4)
**+ N14** (the QFM package — `../unfer/QFM.tex`, ~12 deliverables F2.1–F3.5).
These two alone carry enough independent, fully-specified deliverables to fill
several substantial passes — there is no excuse for a "too fast" pass. **N14
reuses the on-disk `ChapterF1.numberOp` (N12, already landed wave 38) — no new
prerequisite work is needed.** Land as many H*/F* deliverables as the pass
allows, in order, continuing to the next after each; re-verifying the already-
green N1–N12 files is NOT progress.
**Standing rule (author, 2026-07-03): everything that involves fields or
field theory follows §0 S7 — the Mehler/Kopperman formalism as implemented in
the sibling repo `../unfer` (Hermitian field representation, quadratic
ordering, BRST commutation, `prob_kernel` Born layer; cite the crates in
docstrings).** Every package is fully specified in this document: statement +
detailed English proof + pinned Mathlib `file:line` names — implementing the
recipe *is* the task, so write the Lean proof. When a genuine obstruction
appears inside a package, prove the strongest provable variant, record the
obstruction in `BookProof/STATUS.md`, and **move on within the pass** — the
pass never stops on an obstruction. `EXTERNAL` named hypotheses are part of
the design, not blockers: introduce the hypothesis with a citation docstring
and prove everything around it. Definition of done for each package = **all**
listed deliverables compile `sorry`-free (or have a recorded per-deliverable
obstruction note) and `lake build BookProof` is green.

**Work-package queue (priority order — land as many as possible per pass).**
- ~~**N0 — Local re-verification.**~~ **DONE 2026-07-02**: `lake build BookProof`
  re-run locally, green (8032 jobs; only style-linter warnings — long lines /
  whitespace in `ChapterE.lean`, cosmetic).
- ~~**N5 — §0 substrate glue.**~~ **DONE (run `bee1f248`)**:
  `BookProof/Substrate.lean` instantiates Ch. B at the `PnpProof` Kopperman
  substrate measure — `substrate_born_forward`, `substrate_born_backward`,
  `substrate_unit_vector_extends`.
- ~~**N6 — Chapter G: gauge transformations.**~~ **DONE, COMPLETE (run
  `bee1f248`)**: `BookProof/ChapterG.lean` delivers all of G.0–G.7 (guided
  section below now serves as documentation), `sorry`/`axiom`-free, no
  `EXTERNAL` hypothesis, headline `gauge_constraint_pushforward_full_measure`
  included.
- ~~**N8 — Chapter U (unfer / unitary-inference source material).**~~ **DONE
  (run `e3ffd49f`)**: `BookProof/ChapterU.lean` delivers U.1 headline
  `born_conditioning` (Born collapse = `ProbabilityTheory.cond`), U.3
  `prodEquiv` (Fock exponential property, built from the two universal-property
  `lift`s + round-trips), U.4 `EXTERNAL` Lévy hypothesis + measure-theoretic
  wrappers, U.5 `portfolio_risk_inv_sqrt`/`portfolio_std_inv_sqrt`; U.2 =
  cross-reference into `PnpProof/SphereGaussian.lean` as designed. The guided
  "Chapter U" section below now serves as documentation. (The fermionic
  analogue of U.3 and the U.6 prose items stay out of scope; book.tex merge
  remains editorial, author's task.)
- ~~**N1 residue — §A.1 Prop 11 type assignment + Prop 12 converse.**~~
  **DONE (waves 7–8, runs `427d165b` + `e708899c`)**: `ChapterA1g.lean`
  (`realification_irreducible_of_not_isCReal`, `realification_irreducible_iff`,
  `realification_classification` — the `Y ⊥ JY` crux dissolved by running
  Frobenius–Schur through the `ChapterA2c` `Plin`/`Qanti` decomposition:
  `Q² = r·1` with `r > 0` ⇒ C-conjugation ⇒ C-real contradiction; `r = 0` ⇒
  `E` ℂ-linear ⇒ complex-reducibility contradiction) + `ChapterA1h.lean`
  (Prop 11 real side: `IsRRealType`/`IsRComplexType`/`IsRPseudorealType`,
  `rType_exhaustive`, `cxSystem_reducible_of_commuting_rImaginary`).
- ~~**N9 — Chapter G II.**~~ **DONE, COMPLETE (wave 4, run `8296bfb3`)**:
  `BookProof/ChapterG2.lean` delivers all of G.8–G.12 — `cond_of_null`,
  `no_translation_invariant_probabilityMeasure` (any countably infinite gauge
  group), the Gribov headline `no_continuous_gauge_fixing_circle` +
  `gauge_fixing_section_discontinuous`, the BRST layer
  `brstCohomology_equiv : H ≃ₗ[A] ker(·Q) × (A ⧸ (Q))` +
  `brst_physical_iff_gauge_invariant`, and the Haar projection triple. No
  `EXTERNAL` input. The guided "Chapter G II" section below is documentation.
- ~~**N10 — Ch. B §§7–9.**~~ **DONE, COMPLETE (wave 4, run `8296bfb3`)**:
  `BookProof/ChapterB7.lean` delivers B7.1–B7.4 (`koopman_comp`/`koopman_refl`/
  `koopmanRep_mul`, `koopman_const`, `eventMap_*` + `koopman_indicatorConstLp`,
  `hadamard_not_deterministic`). The guided section below is documentation.
- ~~**N2 leftover — §A.2 Props 15–16.**~~ **DONE — N2 COMPLETE IN FULL
  (waves 5–6, runs `b7e12fd4` + `169671c5`)**: `ChapterA2d.lean` (Prop 15
  `Rreal_isometric_iff_complexification_isometric`, via Lemma 14
  phase-rescaling) + `ChapterA2e.lean` (Prop 16 in both cases:
  `Ccomplex_iso_or_antiiso_iff_realification_iso` via Prop 18, and
  `Cpseudoreal_iso_or_antiiso_iff_realification_iso` via Prop 19 + quaternion
  `rot` operators + the proved Frobenius–Schur orthogonality
  `theta_inner_self_zero`). L20/28/34 stay `EXTERNAL` named hypotheses by
  design.
- ~~**N3 residue — Ch. B.3 dense-core SVD.**~~ **DONE — N3 COMPLETE (waves
  10 + 15, runs `2aed7ae0` + `81e63149`)**: `ChapterB3.lean` gained the B.3c
  `conditional_operator_identity` (`Ψ R Ψ† = W D U† R U D W†`), and
  `ChapterB3b.lean` delivers the finite-rank SVD **`denseCore_svd`**
  (`A = W·diagonal D·Uᴴ`, `W,U` unitary, `D ≥ 0`, via `gram_svd` spectral
  half + `svd_completion` orthonormal-basis extension) — exactly the §0 S3
  dense-core reduction target.
- ~~**N4 — §A.3 `EXTERNAL` layer + §A.4–A.5 cores.**~~ **DONE except the
  N11 exhaustiveness bundle (waves 9–37; see the wave summary above)**:
  Lemma 40 / Prop 37 (around `EXTERNAL` `PauliFundamental`) / Prop 46 group
  form / Def 49 / Lemma 48 **complete** incl. both covers `Λ`, `Υ`, the
  Jacobi–Liouville `det_exp_eq_exp_trace`, and the `lemma48_bridge`; Lemma 52
  mechanism + arbitrary-`N` complete-reducibility projector system +
  dimension counts `N = 2…6` **complete**; §A.4 Props 61/73/74/76 unitarity,
  Prop 79 little groups, Prop 81 rep laws, Prop 87 exclusions, Prop 88/Cor 1
  cores and §A.5 CPT/mass-shell **complete**. **What is left of N4 is
  exactly N11 below** (the Wigner/Mackey/Weyl exhaustiveness clauses).
- **N13 — the Hashimoto SIRK package (FLAGSHIP, author-prioritized 2026-07-06;
  FIRST OPEN ITEM). Source: `../unfer/Hashimoto.md`.** Target
  `BookProof/ChapterH1.lean` (φ-functions + exponential integrator + resolvent
  algebra) and `BookProof/ChapterH2.lean` (Krylov compression + convergence).
  §0 S7 governs (this is the numerical backbone of the Mehler/Hashimoto Fock
  formalism); §0 S3 core method carries every infinite-dim step to a
  finite-rank Mathlib fact then closes by density. **The design is the
  `IsSchurFull`/`EXTERNAL` pattern: the two genuinely deep analytic inputs
  (Crouzeix's inequality, the Göckler–Grimm/Hashimoto SIA/RK error theorems)
  are named hypotheses with citation docstrings, NEVER axioms; everything
  around them is proved.** Deliverables (each independent — land as many as the
  pass allows):
  - **H1.1 — the φ-functions and their values.** Define
    `phi : ℕ → ℂ → ℂ`, `phi 0 z = exp z`,
    `phi (k+1) z = ∫ s in 0..1, exp (s*z) * (1-s)^k / k!` (eq. 3). Prove
    `phi_zero : phi 0 = exp`, `phi_at_zero : phi k 0 = 1/k!`
    (`integral_pow`/`integral_const`), and the entire-ness of each `phi k`
    (a fixed convergent power series). Pin `integral_exp`
    (`Mathlib/Analysis/SpecialFunctions/Integrals/Basic.lean:235`),
    `integral_exp_mul_complex` (:241), `intervalIntegral`.
  - **H1.2 — the φ-recurrence.** `phi_succ_mul : z * phi (k+1) z = phi k z − 1/k!`
    for the entire functions (equivalently `phi (k+1) z = (phi k z − 1/k!)/z`
    for `z ≠ 0`), by integration by parts on the defining integral
    (`intervalIntegral.integral_mul_deriv_eq_deriv_mul` /
    `integral_deriv_mul_eq_sub`). Corollary `phi_one : z ≠ 0 → phi 1 z = (exp z − 1)/z`.
  - **H1.3 — the exponential-integrator Duhamel identity (scheme (4)).** For a
    bounded operator `A` (or a matrix on the core), the exact solution of
    `u' = A u + g` (`g` constant) over `[0,δ]` is
    `u δ = exp (δ • A) u₀ + δ • (phiOp 1 (δ • A)) g`, i.e. prove
    `∫ s in 0..δ, exp ((δ−s) • A) g = δ • phiOp 1 (δ • A) g` where
    `phiOp` is the operator φ-function of H1.5. Reduce to the scalar H1.1/H1.2
    identity on each spectral/finite-rank component (§0 S3). Pin
    `Matrix.exp`/`NormedSpace.exp` and `hasDerivAt` for `exp (t • A)`.
  - **H1.4 — the resolvent set-up and the numerical-range spectral inclusion.**
    Define `X γ A = resolvent A γ` (Mathlib `resolvent`,
    `Mathlib/Algebra/Algebra/Spectrum/Basic.lean:79`; `resolvent_eq` :159,
    `mem_resolventSet_iff` :134). Prove the easy half of the Toeplitz–Hausdorff
    setup: every eigenvalue lies in the numerical range —
    `Av = λ v, ‖v‖ = 1 → ⟪A v, v⟫ = λ` so `λ ∈ W(A)` (define `W A` as the set of
    Rayleigh quotients). *Convexity of `W(A)` (full Toeplitz–Hausdorff) may be a
    named `EXTERNAL` hypothesis with citation; the eigenvalue inclusion is
    proved.*
  - **H1.5 — the operator φ-function via the resolvent (Definition 2.4).** For
    bounded `X = (γ − A)⁻¹` define `phiOp k A := psi k γ ∘ (functional calculus at X)`
    with `psi k γ z = phi k (γ − z⁻¹)`, and prove the *defining identity*
    `psiOp k γ X = phiOp k A` on the finite-rank core (a rewrite of the CFC:
    `f_γ((γ−A)⁻¹) = f(A)`). This is the Taylor (1951)/Güttel (2010) definition;
    cite in docstring.
  - **H1.6 — the resolvent shift identity (the clean SIRK algebra core).** For
    `γ_j = N − h·j`, prove the operator identity
    `X_j = (I + h*(m−j) • X_m)⁻¹ * X_m` where `X_j = (γ_j − A)⁻¹`
    (§4 eq. between (10) and (11)); purely algebraic from the resolvent
    identity `X_j − X_m = (γ_m − γ_j) • X_j * X_m`. **Fully self-contained,
    no analysis — a high-value first deliverable.**
  - **H1.7 — the rational-Krylov subspace = rational functions of `X_m`
    (eq. 11).** With `Q_m {X_j} v = span{v, X₁v, X₂X₁v, …}` and
    `R_SIRK = {p/q : p ∈ 𝒫_{m−1}, q(z) = ∏_{i=1}^{m}(1 + h·i·z)}`, prove
    `Q_m {X_j} v = { r X_m v | r ∈ R_SIRK }` by induction on `m` using H1.6
    (each `X_j` applied to a degree-`d` rational in `X_m` raises the numerator
    degree by ≤1 and multiplies the denominator by one more `(1+h j z)` factor).
    Clean finite induction over the core.
  - **H2.1 — the Arnoldi/Krylov compression relation (eqs. 5, 7).** Given an
    orthonormal basis `{v₁,…,v_m}` of `𝒦_m(X, v)` on the core, the compression
    `Vₘ* X Vₘ = Hₘ` is upper-Hessenberg (`h_{i,j} = 0` for `i > j+1`), because
    `X 𝒦_j ⊆ 𝒦_{j+1}`. Use `LinearMap` restriction to the span + the
    orthonormal basis `OrthonormalBasis`; the Hessenberg vanishing is
    `⟪X vⱼ, vᵢ⟫ = 0` for `i > j+1` from the nesting.
  - **H2.2 — the SIRK compression `Vₘ* X_m Vₘ = Hₘ Kₘ⁻¹` (eq. 10).** Assemble
    from H1.6 + H2.1 + the RK relation (9), on the core (finite matrices).
  - **H2.3 — the SIRK convergence headline (Theorem 4.1), CONDITIONAL.**
    Introduce `CrouzeixBound` as a named `EXTERNAL` structure/hypothesis
    (`∀ f A, ‖f A‖ ≤ C * ‖f‖_{∞,W(A)}` with `C ∈ [2, 11.08]`; cite Crouzeix
    2007, Crouzeix–Palencia). Then prove, *given* `CrouzeixBound`, the SIRK
    error bound
    `‖phiOp k A v − Vₘ ψ(HₘKₘ⁻¹) Vₘ* v‖ ≤ 2C‖v‖ e^{−h m} · minᵣ ‖f_{k,N} − r‖_{∞,Σ}`
    (eq. 12), following the paper's proof (triangle inequality + the two
    `CrouzeixBound` applications (14)). The `e^{−h m}` decay is the payoff.
  - **H2.4 — the existing-methods comparison (Remark 4.2), optional.** State the
    SIA bound (15) as a conditional corollary of `CrouzeixBound` and record the
    `e^{−h m}` advantage of SIRK over SIA as an inequality of the two bounds.
  Definition of done: H1.1, H1.2, H1.4-eigenvalue, H1.6, H1.7, H2.1 are pure
  proofs (no `EXTERNAL`); H1.3/H1.5/H2.2 use the §0 S3 core reduction;
  H2.3/H2.4 are conditional on the one named `CrouzeixBound` hypothesis. No
  `axiom`, ever.
- **N14 — the QFM (Quantum Flow Matching) package (FLAGSHIP,
  author-prioritized 2026-07-06; SECOND OPEN ITEM). Source: `../unfer/QFM.tex`
  (impl `../unfer/qfm/`).** Target `BookProof/ChapterF3.lean` (continuity
  Hamiltonian + Fock encoding + training) and `BookProof/ChapterF4.lean`
  (tomographic recovery) — **`ChapterF1` (N12) and `ChapterF2` (N7(c) mass gap)
  are already on disk, so QFM uses F3/F4; both verified free.** §0 S7 governs
  (this IS the Mehler/Kopperman generative flow); **reuses N12's number
  operator `ChapterF1.numberOp` (already landed wave 38; `numberOp_monomial :
  N Xⁿ = n·Xⁿ`) and the Mehler chain in `PnpProof/SphereGaussian.lean` —
  import, never rebuild.** Deliverables:
  - **F2.1 — continuity-Hamiltonian Hermiticity (§4, eq. 4.2).** On the Schwartz
    / finite-support core, `x̂ⱼ` (multiplication) and `p̂ⱼ = −i ∂ⱼ` are symmetric,
    and the symmetrized `H = ½(p̂·v(x̂) + v(x̂)·p̂)` is symmetric
    (`IsSymmetric`), even though `p̂` and `v(x̂)` do not commute. Reuse the
    N12 `a†+a` symmetry pattern (§0 S7). Pin `LinearMap.IsSymmetric`,
    `integral_deriv_mul_eq_sub` (integration by parts for the `p̂` symmetry).
  - **F2.2 — conservative commutator form (§4, eqs. 4.4–4.6).** For
    `v = ∇V`, prove `H^c = i • [K, V(x̂)]` with `K = ½ p̂·p̂`, and the explicit
    action `(H^c Ψ)(x) = −(i/2)(Ψ ∇²V + 2 ∇V·∇Ψ)`. `i[K,V]` is symmetric since
    `K, V` are (a clean `IsSymmetric` corollary — commutator of symmetrics
    times `i`).
  - **F2.3 — orthogonal-Fock disjoint-support identities (§5.1, eqs. 5.2–5.4).**
    For packets `Ψⱼ` with pairwise a.e.-disjoint supports: `Ψⱼ * Ψₖ = 0` (`j≠k`)
    and `= Ψⱼ²` (`j=k`); `∇Ψⱼ · ∇Ψₖ = 0` (`j≠k`); `⟪Ψᵢ, Ψⱼ⟫ = δᵢⱼ` when unit-
    normalized. Pin `MeasureTheory` disjoint-support ⇒ product-zero /
    orthogonality (`Set.indicator`, `MeasureTheory.integral_eq_zero`); this is
    the "zero data loss" claim as a theorem.
  - **F2.4 — the diagonal-Gram closed-form training solution (§5.2,
    eqs. 5.7–5.9) — the `O(M)` payoff.** State the least-squares CFM problem
    `minimize ‖Σⱼ αⱼ gⱼ − b‖²` with `gⱼ = ∇Ψⱼ`. By F2.3 the Gram matrix
    `⟪gⱼ, gₖ⟫` is diagonal, so the minimizer is the per-coordinate closed form
    `αₖ = ⟪b, gₖ⟫ / ‖gₖ‖²` (orthogonal-projection coefficients). Prove it as:
    the minimizer of a quadratic over an orthogonal family decouples. Pin
    `Orthonormal`/`orthogonalProjection` and `inner_sum`. **Self-contained
    linear algebra; the "training is `O(M)` with zero data loss" theorem.**
  - **F2.5 — exact commutativity and time-averaging (§5.4).** Disjoint supports
    ⇒ `[ĥⱼ, ĥₖ] = 0` ⇒ `[H_t, H_{t'}] = 0`; therefore the time-ordered flow
    equals `exp(−i • H̄)` with the time-averaged generator
    `H̄ = ∫₀¹ H_t dt` (a commuting family ⇒ the Magnus/Dyson series truncates to
    the average). Prove on the finite-dim core: pairwise-commuting bounded
    generators ⇒ `∏ exp = exp(∑)` and the average identity.
  - **F2.6 — the vacuum projector `|0⟩⟨0|` (§5.3, `ProjectVacuum`).** The rank-1
    map `P s = ⟪ψ, s⟫ • ψ` (`ψ` unit) is self-adjoint, idempotent
    (`P∘P = P`), `‖P‖ = 1`, and `= orthogonalProjection (span{ψ})`. Pin
    `orthogonalProjection` (`Mathlib/Analysis/InnerProductSpace/Projection/Basic.lean:143`),
    `innerSL` (`Mathlib/Analysis/InnerProductSpace/Dual.lean:68`). Also
    `ProjectOnto ψ`: `H s = ⟪ψ,s⟫•ψ`, idempotent ⇔ `‖ψ‖ = 1` (the rank-1
    shortcut, eq. `rank1shortcut`).
  - **F2.7 — the diagonal generator's eigenstates (§5.5, eq. 5.13).** For
    `H_impl = |0⟩⟨0| + Σⱼ ᾱⱼ n̂ⱼ` with `n̂ⱼ` the N12 number operator,
    `H_impl |0⟩ = |0⟩` and `H_impl |xⱼ⟩ = ᾱⱼ |xⱼ⟩`. **Direct reuse of N12's
    `numberOp` eigenvalue lemma** — this is the concrete bridge that makes N12
    a prerequisite. The Born populations are stationary (phase-only evolution):
    `‖e^{−i H_impl t}|xⱼ⟩‖ = ‖|xⱼ⟩‖`.
  - **F2.8 — the Mehler overlap and the dressed-vacuum Bessel bound (§6,
    eqs. 6.16, 6.18).** The overlap `⟪0, xⱼ⟫ = εⱼ = ∏ᵢ √(w_{j,i}/2π)`: prove the
    single-arc integral `∫_arc √(1/w)·√(1/2π) dφ = √(w/2π)`
    (`integral_const`/`intervalIntegral`), and `εⱼ > 0` as a *finite* product of
    positives (the Kakutani-dichotomy point: finiteness ⇒ strict positivity;
    an infinite product of `<1` factors would vanish). Then the key bound
    `Σⱼ εⱼ² ≤ 1` is **exactly Bessel's inequality** for the orthonormal channel
    family `{xⱼ}`: pin `Orthonormal.sum_inner_products_le`
    (`Mathlib/Analysis/InnerProductSpace/Orthonormal.lean:431`) /
    `Orthonormal.tsum_inner_products_le` (:450). Hence the dressed vacuum
    `|0⟩ = c₀|vac⟩_F + Σ εⱼ Bⱼ†|vac⟩_F` with `c₀ = √(1 − Σεⱼ²)` is well-defined
    and unit-norm. **High-value, clean, and it grounds the whole "vacuum is not
    orthogonal to the channels" mechanism.**
  - **F2.9 — the Mehler projector as the off-diagonal generator (§5.3, §8).**
    The rank-1 projector `H₀ = |0⟩⟨0|` onto the dressed vacuum has channel
    matrix elements `⟪xᵢ, H₀ xⱼ⟫ = εᵢ εⱼ` (using `εⱼ` real ≥ 0). A one-line
    corollary of F2.6 + F2.8 that makes precise "the projector is by itself an
    off-diagonal generator."
  - **F3.1 — Count-Sketch linearity and unbiasedness (§8, `S₁`).** `S₁ : ℝ^d →
    ℝ^k`, `(S₁ x)_h = Σ_{c : h(c)=h} s(c) x_c`, is linear; and with Rademacher
    signs `s(c)` (`E[s(c) s(c')] = δ_{cc'}`) the sketch preserves inner products
    in expectation: `E[⟪S₁ x, S₁ y⟫] = ⟪x, y⟫` (the AMS/Count-Sketch estimator).
    Pin `ProbabilityTheory` independence + `Finset.sum`; **self-contained
    probabilistic identity, reuses the §0 S4 Rademacher/√2-indicator ONB idea.**
  - **F3.2 — the observable-matrix identities (§8, eqs. for `W_prob`, `Φ`).**
    With one-hot projectors `P_a = |a⟩⟨a|` and Krylov operator basis
    `E_{r,s} = |e_r⟩⟨e_s|`, prove `(W_prob)_{a,(r,s)} = Tr(E_{r,s}† W† P_a W) =
    conj(W_{a,r}) W_{a,s}` (outer-product-of-a-row identity), and likewise for
    the image basis `Φ`. Clean finite-matrix trace algebra
    (`Matrix.trace`, `Matrix.mul_apply`).
  - **F3.3 — the unitary reduced flow (§8 Phase 2; AGENTS.md §4 mandate).** For
    Hermitian `H_m`, `e^{−i H_m t}` is unitary, hence `‖c₁‖ = ‖c₀‖`
    (norm-preserving generation, the rev-14 `preserves_norm` test as a theorem).
    Pin `selfAdjoint.expUnitary`
    (`Mathlib/Analysis/CStarAlgebra/Exponential.lean:37`) /
    `Matrix.IsHermitian` spectral route. **The clean AGENTS.md §4 unitarity
    guarantee.**
  - **F3.4 — the pseudo-inverse left-inverse (§8, `Φ̃⁺`).** For full-column-rank
    `Φ̃`, the Moore–Penrose `Φ̃⁺ = (Φ̃ᵀΦ̃)⁻¹Φ̃ᵀ` satisfies `Φ̃⁺ Φ̃ = I` (the
    subspace-recovery guarantee). Pin `Matrix` invertibility of the Gram
    `Φ̃ᵀΦ̃` when columns are independent (`Matrix.PosDef`/`Matrix.det_ne_zero`).
  - **F3.5 (optional) — the Misra–Gries heavy-hitter bound (§8 Phase 4).** With
    `k` counters, the frequency estimate `f̂` of any item satisfies
    `f − N/k ≤ f̂ ≤ f` (the top-1 peak-recovery guarantee). A self-contained
    combinatorial deliverable; lower priority.
  Definition of done: F2.3, F2.4, F2.6, F2.7, F2.8, F2.9, F3.1, F3.2, F3.3,
  F3.4 are pure proofs; F2.1/F2.2/F2.5 use the §0 S3 core. No `EXTERNAL`, no
  `axiom` — the whole package is honestly formalizable. **Cite the `../unfer`
  crates in docstrings (§0 S7 hygiene): `qfm/src/sketch.rs` (F3.1),
  `qfm/src/observables.rs` (F3.2), `qfm/src/potential.rs` (F2.9/F3.3),
  `nested_fock_algebra` `ProjectVacuum`/`ProjectOnto` (F2.6),
  `qfm_hamiltonian` (F2.7).**
- ~~**N11 — the `EXTERNAL` Wigner/Mackey/Weyl exhaustiveness bundle.**~~
  **DONE (wave 38): `ChapterA4h.lean` + `ChapterA3w.lean` on disk,
  `sorry`/`axiom`-free.** The spec below is retained as documentation of what
  landed (external theorems as named hypotheses, conditional headlines proved).
  Target `BookProof/ChapterA4h.lean` (+
  `ChapterA3w.lean` for the Weyl half if cleaner). The single residue every
  wave since 22 has recorded. Design (matches the `IsSchurFull` pattern —
  named hypotheses with citation docstrings, *never* axioms, then prove the
  conditional headlines around them):
  - Structures/Props to introduce: `WignerClassification` (every unitary
    irrep of the Poincaré group with `m² ≥ 0` is induced from a little-group
    irrep; cite Wigner 1939), `MackeyImprimitivity` (transitive systems of
    imprimitivity = induced representations; cite Mackey 1949/1952,
    Varadarajan Thm 6.12), `WeylCompleteReducibility` (finite-dim reps of
    `SL(2,ℂ)` are completely reducible; cite Weyl; this is the Note 50
    hypothesis the `projMixed` identification needs).
  - Conditional headlines to prove: (i) **Prop 87 assembled** — given
    `WignerClassification` + `MackeyImprimitivity` and the on-disk exclusion
    cores (`no_tachyon`, `zeroMomentum_symbol`, `infinite_spin_excluded`,
    `ChapterA4f`), a localizable unitary Poincaré rep decomposes into
    massive/massless-discrete-helicity irreps; (ii) **Prop 88 + Cor 1
    assembled** — with the on-disk `spatialOp_swaps_pos` and
    `energy_sign_not_conserved`, conclude the antiparticle/CPT statement;
    (iii) **Lemma 52 assembled** — given `WeylCompleteReducibility`, identify
    the `tensorPow_complete_reducibility` summands (`ChapterA3q`) with the
    parity-glued `V_{(m,n)} ⊕ V_{(n,m)}` classification, reusing
    `chirality_not_parity_invariant` (`ChapterA3j`) and
    `projLL_not_parity_invariant` (`ChapterA3k`). Wrap each as
    `theorem … (h : WignerClassification …) … : …` — everything quantified,
    nothing asserted. Coordinate with the Lean-4 QFT project
    (arXiv:2603.15770) for statement shapes.
- ~~**N12 — S7 field package: the Bargmann–Fock/CCR polynomial model.**~~
  **DONE (wave 38): `ChapterF1.lean` on disk, `sorry`/`axiom`-free
  (`quadratic_ordering_vacuum` headline `⟨0|H|0⟩ = 0`, `numberOp`, BRST
  bridge).** N14's F2.7 reuses this file's `numberOp`/`numberOp_monomial`. The
  spec below is retained as documentation.
  Target `BookProof/ChapterF1.lean` (field-theory core; book "Quadratic
  ordering" ~line 4031, "Mass gap" ~4061; §0 S7 governs). **No `EXTERNAL`
  input** — the one-mode model is `ℂ[X]` (Mathlib `Polynomial`), the
  `n`-mode model is `MvPolynomial (Fin n) ℂ`; the vacuum `|0⟩` is `1`,
  `a := derivative` (annihilation), `a† := X * ·` (creation). Pinned names
  (mathlib clone v4.28.0): `Polynomial.derivative_mul`
  (`Mathlib/Algebra/Polynomial/Derivative.lean:247`), `MvPolynomial.pderiv`
  (`Mathlib/Algebra/MvPolynomial/PDeriv.lean:61`, a `Derivation`),
  `pderiv_X_self`/`pderiv_X_of_ne`/`pderiv_mul` (same file, :97/:100/:110).
  Deliverables:
  - F1.1 CCR: `a ∘ a† − a† ∘ a = 1` on `ℂ[X]` (Leibniz on `X·p`); `n`-mode
    `[a_i, a†_j] = δ_ij` via `pderiv_X_self`/`pderiv_X_of_ne`.
  - F1.2 Hermitian field rep (S7/`nested_fock_algebra`): `φ := a† + a`,
    `π := i • (a† − a)`, prove `[φ, π] = 2i•1` (or normalize `q = φ/√2` —
    state whichever is exact), and `φ`/`π` symmetric w.r.t. the Bargmann
    pairing `⟪Xᵐ, Xⁿ⟫ = n!·δ_{mn}` (define the pairing on monomials;
    finite sums only, no analysis needed).
  - F1.3 Number operator `N := a† ∘ a`, `N Xⁿ = n·Xⁿ`; spectrum on
    monomials = ℕ.
  - F1.4 **HEADLINE `quadratic_ordering_vacuum` (⟨0|H|0⟩ = 0)**: with the
    quadratically-ordered Hamiltonian `H := a† ∘ a` (NOT `(a a† + a†a)/2` —
    the `../unfer` quadratic-ordering rule drops the zero-point scalar),
    `H 1 = 0`, while the symmetric ordering gives `(1/2)·1 ≠ 0` — formalize
    both evaluations so the normalization choice is a theorem, and cite the
    `nested_fock_algebra` crate's quadratic-ordering implementation in the
    docstring (book line 4031; the mass-gap normalization).
  - F1.5 BRST bridge: one lemma connecting to the on-disk gauge layer —
    gauge invariance = commutation with the BRST operator, stated on the
    `ChapterG2` model (`x ∈ brstKer Q ↔ …` transported along F1.2's rep);
    docstring cites `fock_sirk`.
- **N7 — further mining (after N11 + N12).** (a) superseded by the DONE N10;
  (b) superseded by **N11** above. Remaining: (c) re-scan Ch. P for any
  inequality the author later isolates (mass gap) — author-dependent, ask
  before building; **any Ch.-P / field-theory lemma follows §0 S7** (the
  `../unfer` formalism: quadratic ordering, Hermitian field representation,
  BRST commutation).
- **Hygiene (each pass; the S7 item is STILL PENDING as of wave 37).**
  Narrow `import Mathlib` to targeted imports where cheap; silence remaining
  style linter warnings; keep `BookProof/STATUS.md` current (per-package
  deliverable checklist + obstruction notes). **Pending S7 item (comment-only
  edits, no proof changes — waves 4–37 did not pick it up):** add the
  `../unfer` cross-reference docstrings to the two on-disk field-adjacent
  headlines — `born_conditioning` in `ChapterU.lean` (cite the `prob_kernel`
  crate's `Session.condition`) and `prodEquiv` (cite `nested_fock_algebra`
  as the implemented Fock layer).

---

## Conventions for the Lean specialist

1. **Fields.** `𝔽` ranges over `ℝ` and `ℂ`. Use `RCLike 𝔽` (Mathlib) to write
   field-generic statements once. Quaternions are `Quaternion ℝ` (`ℍ`).
2. **Hilbert spaces.** A "Hilbert space `V` over `𝔽`" is
   `[NormedAddCommGroup V] [InnerProductSpace 𝔽 V] [CompleteSpace V]`.
   Inner product `⟪·,·⟫_𝔽`. Mathlib's convention is conjugate-linear in the
   **first** slot; the book is conjugate-linear in the first slot too
   (`<v,u>` linear in `u`). Keep this alignment; it matters for Defn. 2/3.
3. **Bounded operators.** `V →L[𝔽] V` (continuous linear maps). Adjoint
   `ContinuousLinearMap.adjoint`, written `S†`.
4. **Anti-linear maps.** Mathlib: `LinearMap` over the ring with
   `RingHom` = `starRingEnd ℂ` (a `ℂ →+* ℂ` semilinear map,
   `LinearMap ℂ ℂ (starRingEnd ℂ) V V` i.e. `V →ₛₗ[starRingEnd ℂ] V`). An
   *anti-unitary* is a `ℂ`-antilinear surjective norm-preserving map; there is
   no bespoke Mathlib bundle, so define a structure `AntiUnitary V` early.
5. **Systems.** The book's central object is a **system** `(M, V)`: a set `M`
   of bounded endomorphisms of a Hilbert space `V`. Model it as
   `structure System (𝔽 V) := (ops : Set (V →L[𝔽] V))`. Everything
   ("subsystem", "irreducible", "normal", "isometry", "Schur") is a predicate on
   `System`. This is the foundational file; build it first (see §A.0).
6. **`sorry`/`axiom` policy.** No `axiom` declarations. Genuine external
   theorems that Mathlib lacks (Mackey imprimitivity, Weyl complete
   reducibility, direct-integral decomposition) are to be introduced as **named
   hypotheses / typeclass assumptions**, never as `axiom`, and flagged `EXTERNAL`
   below so the author can decide whether to cite or build them.
7. **Numbering.** Statement numbers ("Prop 17", "Lemma 34") are the book's own;
   keep them in Lean docstrings for traceability, e.g. `/-- Prop. 17 (book). -/`.

---

## §0 — Governing strategy: Kopperman decidable-dense-subset + Mehler (MANDATORY)

**This is the house style for the whole formalization** (author's directive), and it
is available *because every space in `book.tex` is a separable Hilbert space, hence a
standard probability space, and the probabilistic content is the Mehler formalism.*
Follow it in every chapter. Source: `RiemannProof/Kopperman_Tutorial.p.tex`
("A Hilbert-Space Exchange Format…") and R. Kopperman, *The `L_{ω₁,ω₁}`-Theory of
Hilbert Spaces* (1967).

**S1 — Separable Hilbert space = standard probability space.** Model everything in a
**separable** real/complex Hilbert space `H`. Kopperman's representation theorem
(any model of the `L_{ω₁,ω₁}` Hilbert axioms ≅ a Hilbert space) is the ontological
guarantee; in Lean use `[SeparableSpace H]` / `Lp` directly. Separability ⇒ the
measure spaces are **standard Borel**, so disintegration (`Measure.condKernel`) and
atomless priors apply — this is the whole reason Chapters B–E go through.

**S2 — REUSE the existing substrate: the Kopperman/Mehler formalism is ALREADY
FORMALIZED in `PnpProof`** (three files) — do not rebuild any of it; `import` and
instantiate:
- `PnpProof/Kopperman.lean` — the substrate bundle: `Formalism (H)` (a separable
  inner-product space + atomless probability prior); `Substrate := Lp ℝ 2 unitMeasure`
  with `substrate_separable` (`= l2_separable`); `substrate_decidable_skeleton :
  ∃ D, D.Countable ∧ Dense D` — **the decidable dense subset** (finite
  ℚ-combinations of basis vectors); `MehlerPrior` (`= gammaMeasure`),
  `mehler_isProbability`, `mehler_concentrates_on_sphere`, `modelPrior_atomless`;
  `substrate_orthonormal_pair`, `koppermanSubstrate : Formalism Substrate`.
- `PnpProof/SphereGaussian.lean` — **the Mehler formalism proper, sorry-free**:
  `physHermite`/`gegenbauer`/`gegenbauerScaled_tendsto_hermite` (the Mehler/lopez99
  limit: rescaled Gegenbauer → Hermite), `weight_tendsto_gaussian` (hyperspherical
  weight → Gaussian), `hermite_sq_integral`/`hermite_normalization` (∫H_n²e^{−x²} =
  √π·2ⁿ·n!), `normalization_tendsto`, `sphereUniform` (uniform measure on the
  √k-sphere as Gaussian pushforward) with `sphereUniform_sphere` and
  `sphereUniform_rotation_invariant`, `gammaMeasure` (infinite Gaussian product),
  `gaussian_concentration_sphere` (a.s. concentration) and `poincare_borel_ae`
  (Poincaré–Borel: sphere normalization → Gaussian coordinates).
- `PnpProof/FunctionSpace.lean` — `l2_separable`, `linf_not_separable`,
  `sqrt_density_memLp`/`sqrt_density_norm` (the `√p` wave function — Ch. B.1's
  content in in-repo form), `polynomial_dense_L2`, `hilbert_classification`
  (all ∞-dim separable Hilbert spaces isometric), `exists_atomless_sphere_measure`.

**S3 — The decidable-dense-subset ("core") method — how to handle ALL infinite-dim
analysis.** Never invoke an infinite-dimensional analytic theorem Mathlib lacks.
Instead: (i) define the object/operator on the **core** `D₀` = finite-support vectors
(finite ℚ- or ℂ-combinations of an orthonormal basis); (ii) prove the statement on
`D₀`, where everything is effectively **finite-dimensional at each level** and Mathlib's
*finite-dim* results apply verbatim; (iii) **extend by density / closure** to all of `H`
(bounded-linear-extension `ContinuousLinearMap`, or graph-closure for unbounded
operators). This is exactly the `Kopperman_Tutorial` "Note on Totality": the ℚ-skeleton
is the computable core; completeness fills the gaps.
> **This resolves the two gaps found earlier.** The absent *infinite-dim compact
> self-adjoint spectral theorem / Hilbert–Schmidt* (Ch. B.3b SVD) is **not needed**:
> do the SVD **finite-rank on the core** via Mathlib's finite-dim
> `LinearMap.IsSymmetric.eigenvectorBasis`, then close. The partial isometry `V`
> ("pad to a unitary `W`") is the Kopperman **partial-isometry** layer (`V*V`, `VV*`
> projections, `VV*V=V`).

**S4 — Mehler formalism = the concrete probability parametrization (Chapters B, E).**
The uniform measure on the infinite-dim hypersphere converges to the **Gaussian
measure** (Mehler 1866); Hermite polynomials are the resulting orthonormal basis, and
the harmonic oscillator `a, a*, N` on `ℓ²` is its generator. **This is already
formalized in-repo** — `PnpProof/SphereGaussian.lean` proves the Mehler theorem chain
end-to-end (`gegenbauerScaled_tendsto_hermite`, `weight_tendsto_gaussian`,
`sphereUniform` + rotation invariance, `gaussian_concentration_sphere`,
`poincare_borel_ae`, `hermite_normalization`); import it rather than re-deriving
anything (see S2). The underlying Mathlib layers, if lower-level facts are needed:
- **Gaussian measure**: `Mathlib/Probability/Distributions/Gaussian/` — `gaussianReal`,
  `IsGaussian` (`Gaussian/Basic.lean:47`, `map L = gaussianReal …` for every dual `L`),
  `noAtoms_gaussianReal`, **Fernique** (`Gaussian/Fernique.lean`).
- **Hermite polynomials**: `Mathlib/RingTheory/Polynomial/Hermite/` incl.
  `Hermite/Gaussian.lean` (orthogonality wrt the Gaussian weight = the Mehler basis).
- This is the analytic engine behind **Ch. B** (Born parametrization = square-root of a
  density against the Mehler/Gaussian reference) and **Ch. E** (hyperspherical Born
  recursion = the finite-dim slices of the Mehler sphere).

**S5 — Countable-additivity caveat (measure only on the definable/Borel σ-algebra of
the fragment).** Assign the measure to the **formulas of the countable fragment**
(equivalently, the Borel sets generated by the dense subset), not the full power set.
Practically in Lean: always work with the Borel σ-algebra (`borel H`) — which is what
Mathlib measures use anyway — so this caveat is automatically satisfied and needs no
special handling. It *does* mean: avoid proofs that genuinely require an uncountable
union of null sets (flagged where relevant, e.g. the RH per-point→all-point lift,
which is out of scope here).

**S6 — Known gaps under this strategy (stay named hypotheses; not in Mathlib).**
Verified by whole-repo grep: **no `PartialIsometry` for operators**, **no Cuntz
algebra / creation-annihilation / Fock space**, **no essential self-adjointness /
Faris–Lavine** (Mathlib has bounded `IsSelfAdjoint` + finite-dim/CFC spectral only).
So the operator-algebra layer (partial isometries, Cuntz `O_∞`) and the unbounded-
operator ESA arguments (`iH` in §A.4; harmonic-oscillator Hamiltonian) are named
hypotheses or small bespoke builds on the core — never `axiom`s.

**S7 — FIELDS / FIELD THEORY: follow the Mehler/Kopperman formalism AS IMPLEMENTED
IN `../unfer` (author directive 2026-07-03, MANDATORY).** The sibling repository
**`../unfer`** (absolute:
`/media/leo/e7ed9d6f-5f0a-4e19-a74e-83424bc154ba/unfer`; `Kopperman_Tutorial.p.tex`
at its root, `AGENTS.md` + `docs/ARCHITECTURE.md` for orientation) is the
**reference implementation** of the formalism for everything field-theoretic. It is
Rust, not Lean — the rule is not "port the code" but "**formalize the same design
decisions**": whenever a package involves fields or field theory, the Lean
statements must mirror how `../unfer` sets the objects up, and their docstrings must
cite the corresponding crate/module. The load-bearing design decisions:
- **Fock layer** (`nested_fock_algebra` crate): fields live on (nested) Fock spaces
  over the Kopperman substrate — an **Outer** Fock space (the "multiverse", the
  probability-space-of-probability-spaces of book-Ch.-B §10 ensemble forecasting;
  bosonic or fermionic with Jordan–Wigner signs) whose coordinates each carry an
  **Inner** Fock space (local excitations); inner operators act as operators
  integrated over the outer field. Lean counterpart: the `SymmetricAlgebra`
  exponential layer of Ch. U.3 (`prodEquiv`, on disk) is the bosonic algebraic
  shadow; any further Fock work extends *that*, and the S6 gap (no analytic Fock
  space in Mathlib) stays a named-hypothesis boundary.
- **Hermitian field representation** (`AGENTS.md` §2): fields are `φ = a† + a`,
  conjugate momenta `π = i(a† − a)`. Any Lean statement about "a field" must use
  this presentation (as §A.4's Majorana–Fourier layer already does implicitly);
  never introduce a rival field presentation.
- **Quadratic ordering** (book 4031 as-implemented; `cas.rs`): pure scalar
  (zero-point) terms are **dropped** so that `⟨0|H|0⟩ = 0` — the mass-gap
  normalization. Any future Ch.-P/mass-gap lemma (N7(c)) states Hamiltonians in
  quadratic-ordered form.
- **Gauge/BRST** (`fock_sirk` BRST projection): gauge invariance of a physics
  Hamiltonian **is** commutation with the BRST charge `Ω`, and physical states are
  BRST-cohomology classes — exactly the G.6 (`BRST_nilpotent`, on disk) and G.11
  (`brst_physical_iff_gauge_invariant`, N9) layer. G.11's docstrings must cite
  `fock_sirk`'s BRST projection as the implemented counterpart.
- **Born-rule kernel** (`prob_kernel` crate: `Session` with
  `evolve`/`probability`/`condition`): conditioning-by-projection is the classical
  conditional measure — this is precisely Ch. U.1 `born_conditioning` (on disk);
  U.1's cross-reference docstring should name `prob_kernel`.
- **Spectral few-variables decomposition** (`fock_sirk` SIRK = Hashimoto
  shift-invert rational Krylov — the very references book-Ch.-B §10 cites): the
  computational realization of "decompose the spectrum into few-variable direct
  summands". Anything formalized from §10 later stays aligned with this (currently
  triaged prose — no Lean target).
Scope: this binds **N4 (§A.3–A.5)**, **N9 G.11 (BRST)**, **Ch. U** cross-references,
**N7(b)/(c)** and any future mining of the field-theory chapters (book 3699, 6486,
7125, 7881). It does *not* change any non-field package (Ch. B/C/D/E measure theory,
§A.0–A.2 representation theory, G.0–G.10/G.12).

---

## Chapter index & formalizability assessment

| # | Chapter (line) | Formalizable content | Status |
|---|----------------|----------------------|--------|
| A | Real representations / CPT (4218) | ~30 numbered Props/Lemmas: real↔complex systems, Schur classification (ℝ/ℂ/ℍ), imprimitivity, finite-dim Lorentz reps, unitary Poincaré reps, Majorana–Fourier/Energy transforms | **§A.0–A.2 DONE IN FULL** (`ChapterA`, `ChapterA1`–`A1h` + `Complexification`, `ChapterA2`–`A2e`: Defs 8–10, Props 11–12 both directions, L14 + P15–19; L20/28/34 `EXTERNAL` by design); **§A.3 DONE** (`ChapterA3`–`A3v`: Clifford model, L40/P37/P46/Def 49, Lemma 48 complete incl. `Υ`, `det exp = exp tr`, `lemma48_bridge`; Lemma 52 machinery + `N=2…6` dimensions); **§A.4–A.5 cores DONE** (`ChapterA4`–`A4g`, `ChapterA5`: P61/73/74/76 unitarity, P79 little groups, P81 rep laws, P87 exclusions, P88/Cor 1, CPT mass-shell). **Residue = N11 exhaustiveness bundle only** |
| B | Wave-function parametrization of a probability measure (1238) | §3: every conditional prob. measure on a standard space is a pullback; free-field/ONB parametrization | **DONE IN FULL** — `ChapterB.lean` (B.1–B.2 + `condKernel_disintegration`), `ChapterB3.lean` (`IsPartialIsometry` layer + B.3c `conditional_operator_identity`), `ChapterB3b.lean` (**`denseCore_svd`**, wave 15) |
| C | Entropy + irreversible deterministic time-evolution coexist (9474) | measure-dynamics coexistence statement | **C.1 DONE in Lean** (`BookProof/ChapterC.lean`); C.2 author-dependent |
| D | Aligned deep learning as random sampling (9606) | sampling-method equivalence lemma(s) | **D.1 DONE in Lean** (`BookProof/ChapterD.lean`) |
| E | Wave-function collapse vs Euler's formula (3229) | Euler-formula identities for phase spaces | **E.1–E.4 DONE in Lean** (`BookProof/ChapterE.lean`); E.5 = cross-ref into §A.2 |
| F | Reconstructing the classical trajectory (2494) | conditional-expectation trajectory statement | Triaged non-formalizable (prose); Wigner anchor = N7(b) |
| **G** | **Gauge symmetry & dissipative dynamics (2128) + Gribov chapter (7125)** | **gauge group of a parametrization, invariant subalgebras, gauge-fixing, Haar averaging, pushforward constraints, BRST nilpotency, Koopman; PLUS (G II): conditioning-fails-on-null, general Dirac obstruction, Gribov no-continuous-gauge-fixing, BRST cohomology, Haar projection** | **G.0–G.7 DONE in Lean** (`BookProof/ChapterG.lean`, run `bee1f248`); **G.8–G.12 DONE (N9 ✅, wave 4 run `8296bfb3`, `BookProof/ChapterG2.lean` incl. Gribov headline + BRST cohomology)** |
| H | Consciousness as a Bayesian prior (9122) | Bayesian-prior representation lemma(s) | Triaged non-formalizable (prose) |
| P | Physics-heavy (3699, 6486, 7125, 7522, 7881) | discrete lemmas only | Mined — no discrete lemmas beyond Ch. A/B/E reuse; deeper gauge content now lives in Ch. G |
| **U** | **Unitary inference / unfer (added 2026-07-02; source `../test` gitbook + pubpub ec0in, to be merged into book.tex)** | **Born-rule conditioning = classical conditional measure (`ProbabilityTheory.cond`), Fock exponential property `Sym(M×N) ≅ Sym M ⊗ Sym N`, 1/√n portfolio risk, Lévy nowhere-differentiability (`EXTERNAL`)** | **DONE in Lean** (`BookProof/ChapterU.lean`, run `e3ffd49f`: U.1 headline `born_conditioning`, U.3 `prodEquiv`, U.4 `EXTERNAL` + wrappers, U.5 portfolio; U.2 = cross-ref to `PnpProof/SphereGaussian.lean`); merge into book.tex remains editorial (author's task) |
| **SIRK** | **Hashimoto shift-invert rational Krylov (added 2026-07-06; source `../unfer/Hashimoto.md`; `book.tex` cites at 1147/2055)** | **φ-functions + recurrence, exponential-integrator Duhamel identity, resolvent/rational-Krylov algebra (`Xⱼ=(I+h(m−j)Xₘ)⁻¹Xₘ`, rational-function characterization), Arnoldi/SIRK compression, `e^{−hm}` convergence bound conditional on `EXTERNAL` Crouzeix** | **OPEN — N13 (FLAGSHIP, FIRST open item), full guided spec in queue; target `ChapterH1.lean`/`ChapterH2.lean`** |
| **QFM** | **Quantum Flow Matching (added 2026-07-06; source `../unfer/QFM.tex`, impl `../unfer/qfm/`)** | **continuity-Hamiltonian Hermiticity, orthogonal-Fock disjoint-support identities, diagonal-Gram `O(M)` closed-form training, exact commutativity/time-averaging, vacuum projector + dressed-vacuum Bessel bound `Σεⱼ²≤1`, Mehler overlap `⟨0\|xⱼ⟩=εⱼ>0`, Count-Sketch unbiasedness, unitary reduced flow, pseudo-inverse recovery** | **OPEN — N14 (FLAGSHIP, SECOND open item), full guided spec in queue; reuses on-disk `ChapterF1.numberOp` (N12) + `SphereGaussian.lean`; target `ChapterF3.lean`/`ChapterF4.lean` (F1/F2 already taken)** |

**Suggested Lean build order (dependencies).** A.0 (Systems core) → A.1
(real/complex map) → A.2 (Schur classification) → A.3 (imprimitivity, EXTERNAL
Mackey) → A.4/A.5 (Lorentz/Poincaré, depends on a Clifford-algebra layer) ;
B is independent (measure theory) and can proceed in parallel; C, D depend on B;
E is independent (elementary complex analysis); **G is independent of A and can
proceed in parallel with B** (G.0–G.4 are pure set/measure theory; G.5 needs
Haar; G.7 shares the Koopman layer with book-Ch.-B §7/§9); F, H depend on B.

---

## Existing formalizations to reuse (verified July 2026)

The rule is **reuse before rebuild**. The following was verified by grepping the
**actual Mathlib source** at rev `v4.28.0` (cloned locally via `lake exe cache get`,
July 2026); every ✅ row gives the exact declaration and `file:line`.

| Input (where used) | Exists? | Pinned Mathlib declaration — `file:line` |
|---|---|---|
| **Kopperman substrate: separable Hilbert + decidable dense subset + Mehler prior** (§0, Ch. B, E) | ✅ **in-repo** | **`RiemannProof/PnpProof/Kopperman.lean`** — `Formalism`, `Substrate := Lp ℝ 2 unitMeasure`, `substrate_separable`, `substrate_decidable_skeleton` (∃ countable dense D), `MehlerPrior`/`mehler_isProbability`/`mehler_concentrates_on_sphere`, `modelPrior_atomless`, `koppermanSubstrate`. **Import & instantiate; do not rebuild.** |
| **Mehler formalism proper: sphere→Gaussian, Hermite/Gegenbauer, Poincaré–Borel** (§0 S4, Ch. B, E) | ✅ **in-repo** | **`RiemannProof/PnpProof/SphereGaussian.lean`** (sorry-free) — `gegenbauerScaled_tendsto_hermite`, `weight_tendsto_gaussian`, `sphereUniform`/`sphereUniform_sphere`/`sphereUniform_rotation_invariant`, `hermite_sq_integral`/`hermite_normalization`, `gammaMeasure`, `gaussian_concentration_sphere`, `poincare_borel_ae`. Plus `PnpProof/FunctionSpace.lean`: `l2_separable`, `sqrt_density_memLp`/`sqrt_density_norm`, `polynomial_dense_L2`, `hilbert_classification`, `exists_atomless_sphere_measure`. |
| **Mehler measure = Gaussian (Mathlib layer)** (§0 S4, Ch. B, E) | ✅ | `Probability/Distributions/Gaussian/`: `gaussianReal`, `IsGaussian` (`Gaussian/Basic.lean:47`), `noAtoms_gaussianReal` (`Fernique.lean:234`), **Fernique** (`Gaussian/Fernique.lean`). |
| **Hermite polynomials (Mehler basis)** (§0 S4, Ch. B, E) | ✅ | `RingTheory/Polynomial/Hermite/` incl. `Hermite/Gaussian.lean` (Hermite ⟂ wrt Gaussian weight). |
| **Schur's lemma, algebraic** (§A.2 L20/21, §A.3 L40, Ch. E.5) | ✅ | `LinearMap.bijective_or_eq_zero` — `RingTheory/SimpleModule/Basic.lean:501`; `Module.End.instDivisionRing` — `…:521` (endomorphism ring of a simple module is a division ring). Finite-dim complex Schur (L20) directly. |
| **Frobenius ℝ/ℂ/ℍ classification** (§A.2 P17–19) | ❌ not in Mathlib | No Lean formalization. **Not needed**: Props 17–19 *reprove* the trichotomy from the R-real/complex/pseudoreal machinery + `Module.End.instDivisionRing`. (Math ref: arXiv:2405.01876.) |
| **Realification real inner product `⟪·,·⟫_r = re⟪·,·⟫`** (§A.0 Def 3, Prop 5) | ✅ | `Inner.rclikeToReal` — `Analysis/InnerProductSpace/Basic.lean:905` (`inner x y := re ⟪x,y⟫`, **exactly Def 3**); `InnerProductSpace.rclikeToReal` — `…:917`. |
| **Spectral theorem (self-adjoint)** (Ch. B.3b SVD) | ✅ finite-dim (enough via §0) | `LinearMap.IsSymmetric.eigenvectorBasis` — `Analysis/InnerProductSpace/Spectrum.lean:280`; spectral thm v1/v2 `…:180,:309`. **Finite-dim (`finrank 𝕜 E = n`).** No infinite-dim compact spectral theorem, **no `HilbertSchmidt`/`Schatten`** (grep: absent) — but **not needed**: under the §0 dense-core method do the SVD **finite-rank on `D₀`** with `eigenvectorBasis`, then close by density. |
| **Partial isometry / Cuntz algebra `O_∞`** (§0 S3/S6, Ch. B SVD `V`, A imprimitivity) | ❌ | No `PartialIsometry` for operators, no Cuntz/Fock/creation–annihilation in Mathlib (grep: absent). Build the small partial-isometry API (`V†V`, `VV†` projections, `VV†V=V`) directly, or take as named hypotheses. |
| **Essential self-adjointness / Faris–Lavine** (§0 S6, §A.4 `iH`, harmonic osc.) | ❌ | Not in Mathlib (only bounded `IsSelfAdjoint` + finite-dim/CFC spectral). Unbounded-operator ESA on the dense core = named hypothesis or bespoke build; cite Faris–Lavine. |
| **Fourier L² / Plancherel** (§A.4 Notes 62/76, Ch. B.3a) | ✅ **(correction: it landed)** | `MeasureTheory.Lp.fourierTransformₗᵢ : Lp F 2 ≃ₗᵢ[ℂ] Lp F 2` — `Analysis/Fourier/LpSpace.lean:49`; unitarity `Lp.norm_fourier_eq` (`…:87`), `Lp.inner_fourier_eq` (`…:92`). L¹ theory: `Analysis/Fourier/FourierTransform.lean`. **Use directly — do not hypothesize Plancherel.** |
| **Disintegration / regular conditional prob.** (Ch. B.2′) | ✅ | `MeasureTheory.Measure.condKernel` — `Probability/Kernel/Disintegration/StandardBorel.lean:360` (`irreducible_def`), `…_apply :364`. Standard-Borel disintegration = the book's regular conditional density. |
| **Stirling `n! ~ √(2πn)(n/e)ⁿ`** (Ch. C.1) | ✅ | `Stirling.factorial_isEquivalent_stirling` — `Analysis/SpecialFunctions/Stirling.lean:235` (`~[atTop]` `√(2*n*π)*(n/exp 1)^n`); `Stirling.tendsto_stirlingSeq_sqrt_pi` `…:228`. |
| **Computability ⇒ countable** (Ch. D.1) | ✅ | `Nat.Partrec.Code` — `Computability/PartrecCode.lean:76`; `Denumerable Code` instance `…:176` (⇒ countable); `Computable` — `Computability/Partrec.lean:246`. Countable-null: `Set.Countable.measure_zero` (`MeasureTheory/Measure/…`). |
| **Perm/function counts `n!`, `nⁿ`** (Ch. C.1) | ✅ | `Fintype.card_fun` — `Data/Fintype/BigOperators.lean:199`; `Fintype.card_perm` (`GroupTheory/Perm/…`). |
| **Gram–Schmidt / HilbertBasis** (Ch. B.2, E) | ✅ | `HilbertBasis` — `Analysis/InnerProductSpace/l2Space.lean:375`; `gramSchmidtOrthonormalBasis` — `Analysis/InnerProductSpace/GramSchmidtOrtho.lean:317`; `OrthonormalBasis`, `LinearIsometryEquiv`. |
| **`Lp` space, `MemLp`** (Ch. B) | ✅ | `MeasureTheory.Lp` — `MeasureTheory/Function/LpSpace/Basic.lean:88`; `MemLp` — `MeasureTheory/Function/LpSeminorm/Defs.lean`. |
| **`orthogonalProjection`** (§A.2 L26/27, Ch. G) | ✅ | `orthogonalProjection : E →L[𝕜] K` — `Analysis/InnerProductSpace/Projection/Basic.lean:143`. |
| **Haar measure on a compact group** (Ch. G.5) | ✅ | `MeasureTheory.Measure.haarMeasure` + normalization `haarMeasure_self` — `MeasureTheory/Measure/Haar/Basic.lean:537`; `Top (PositiveCompacts G)` instance for compact nonempty `G` — `Topology/Sets/Compacts.lean:563`. **No ready `IsProbabilityMeasure (haarMeasure ⊤)` instance** (grep: absent) — derive it in one line from `haarMeasure_self` at `K₀ = ⊤`. Left-invariance of integrals: `integral_mul_left_eq_self` — `MeasureTheory/Group/Integral.lean:91`. |
| **Koopman composition operator on `Lp`** (Ch. G.7; book-Ch.-B §7/§9 via N7) | ✅ | `MeasureTheory.Lp.compMeasurePreserving` — `MeasureTheory/Function/LpSpace/Basic.lean:548`; linear map `compMeasurePreservingₗ` `…:579`; **linear isometry** `compMeasurePreservingₗᵢ` `…:586` (needs `[Fact (1 ≤ p)]`). No `≃ₗᵢ` (unitary) version found — assemble it from the two isometries of a `MeasurableEquiv` (G.7a). |
| **Centralizer subalgebra (gauge-invariant operator algebra)** (Ch. G.2) | ✅ | `Subalgebra.centralizer : Set A → Subalgebra R A` — `Algebra/Algebra/Subalgebra/Basic.lean:924`. The gauge-invariant operator algebra *is* `Subalgebra.centralizer 𝔽 {U_g}` — no new structure needed. |
| **Pushforward of a probability measure is a probability measure** (Ch. G.5c/G.7c) | ✅ | `MeasureTheory.Measure.isProbabilityMeasure_map` — `MeasureTheory/Measure/Typeclasses/Probability.lean:124` (takes `AEMeasurable`); `Measure.map_apply` for the preimage computation. |
| **Transpositions / sections for the gauge group** (Ch. G.1/G.4) | ✅ | `Equiv.swap_apply_left` — `Logic/Equiv/Basic.lean:647`, `swap_apply_of_ne_of_ne` `…:654`; `Function.surjInv` — `Logic/Function/Basic.lean:424`, `surjInv_eq` `…:427`, `Function.injective_surjInv` (same file). |
| **`Matrix.exp`** (Ch. E.1b) | ✅ | `Analysis/Normed/Algebra/MatrixExponential.lean` (`Matrix.exp`). |
| **`cos_arccos` + trig** (Ch. E.1a/c) | ✅ | `Real.cos_arccos` — `Analysis/SpecialFunctions/Trigonometric/Inverse.lean:290`; `Real.sin_sq_add_cos_sq`, `Real.cos_two_mul`, `Real.cos_sq` (Trigonometric, standard). |
| **Quaternions `ℍ`** (§A.2 P19) | ✅ | `Quaternion` — `Algebra/Quaternion.lean:753` (`ℍ[R]`). |
| **DFT unitary** (Ch. E.3) | ⚠️ only `ZMod` | `Analysis/Fourier/ZMod.lean` (DFT over `ZMod n`, character orthogonality). **No `Matrix.dft`** (correction). Use the `ZMod` Fourier transform, or build the `n×n` unitary + `|·|²=1/n` by hand (Hadamard for `n=2`). |
| **Weyl complete reducibility** (§A.2 N23, §A.3 N50) | ❌ | Not formalized (Mathlib has semisimple *modules*, not Weyl for Lie groups). Named hypothesis; cite Hall/Weyl. |
| **Schur for unitary reps / Mackey imprimitivity** (§A.2 L28/34, N33; §A.4 N84) | ❌ | Not in any proof assistant. Named hypotheses; cite Mackey/Varadarajan. Biggest genuine gap. |
| **Pauli's fundamental theorem of γ-matrices** (§A.3 N36) | ❌ | Not formalized. Named hypothesis; cite Good 1955. (Concrete `4×4` Clifford relations *are* `decide`-able once hard-coded.) |
| **Wigner's symmetry theorem** (§A.4, Ch. F) | ❌ | **Not in Lean, Isabelle, or Coq** (verified). Named hypothesis. Related infra: Isabelle "Complex Bounded Operators" (arXiv:2512.05878). |
| **Wigner little-group Poincaré classification** (§A.4 N80–83) | ❌ | Not formalized. Named hypothesis; cite Wigner 1939. |
| **Free QFT / Poincaré-covariant fields** (§A.4–A.5; Ch. P) | 🚧 active Lean 4 | **arXiv:2603.15770 "Formalization of QFT"** (Lean 4): free bosonic field in 4D + Glimm–Jaffe/Osterwalder–Schrader axioms, on Mathlib. **Coordinate with it** for the field-theory/Poincaré layer. |
| **Conditional probability measure `μ[\|E]`** (Ch. U.1) | ✅ | `ProbabilityTheory.cond` — `Probability/ConditionalProbability.lean:74` (definitionally `(μ E)⁻¹ • μ.restrict E`); API `cond_apply`, `cond_cond_eq_cond_inter` same file. |
| **Density / indicator plumbing for the Born measure** (Ch. U.1) | ✅ | `MeasureTheory.withDensity_indicator` — `MeasureTheory/Measure/WithDensity.lean:188`; `withDensity_smul` (same file); `indicatorConstLp` — `MeasureTheory/Function/LpSpace/Indicator.lean:88`. |
| **Symmetric algebra (bosonic Fock, algebraic layer)** (Ch. U.3) | ✅ partial | `SymmetricAlgebra` — `LinearAlgebra/SymmetricAlgebra/Basic.lean:47` (with `lift` universal property). **No `Sym(M × N) ≃ₐ Sym M ⊗ Sym N` iso in Mathlib** (grep: absent) — build it from two `lift`s (U.3); graded/signed version: `GradedTensorProduct` — `LinearAlgebra/TensorProduct/Graded/External.lean` + `Internal.lean` (stretch only). |
| **Variance of independent sums** (Ch. U.5) | ✅ | `ProbabilityTheory.IndepFun.variance_add` — `Probability/Moments/Variance.lean:32`; `IndepFun.variance_sum` — `…:34` (pairwise-independent finite sums). |
| **Brownian motion / Lévy processes** (Ch. U.4) | ❌ | **Not in Mathlib v4.28.0** (grep: no `BrownianMotion`, no Wiener measure). Nowhere-differentiability of Lévy paths = `EXTERNAL` named hypothesis; cite Bertoin 1994 + Paley–Wiener–Zygmund 1933. Revisit when BM lands in Mathlib. |
| **Null conditioning** (G.8) | ✅ | `Measure.restrict_eq_zero` — `MeasureTheory/Measure/Restrict.lean:211`; `cond_isProbabilityMeasure` — `Probability/ConditionalProbability.lean:162` (positive-mass converse, cite); `cond_apply` — `…:214`. |
| **Circle exponential & its fibers** (G.10 Gribov) | ✅ | `Circle.exp` with `Circle.exp_eq_exp` (`exp x = exp y ↔ ∃ m : ℤ, x = y + m*(2π)`) — `Analysis/SpecialFunctions/Complex/Circle.lean:68`; `Circle.periodic_exp` — `…:74`; `Circle.exp_two_pi` — `…:76`; `Circle.exp_eq_one` — `…:84`. |
| **Continuous discrete-valued ⇒ constant on connected** (G.10) | ✅ | `IsPreconnected.constant` — `Topology/Connected/TotallyDisconnected.lean:297`; `PreconnectedSpace.constant` — `…:305`; or avoid via `intermediate_value_Icc` (`Topology/Order/IntermediateValue.lean`). |
| **Quotient-module algebra for BRST cohomology** (G.11) | ✅ | `Submodule.Quotient` + `Submodule.liftQ`, `Ideal.Quotient.mk`/`.lift` (core Mathlib, ubiquitous); `LinearMap.mulLeft` for `ker Q`. |
| **Fubini for the Haar projection** (G.12) | ✅ | `MeasureTheory.integral_integral_swap` — `MeasureTheory/Integral/Prod.lean:532`; `integral_mul_left_eq_self` — `MeasureTheory/Group/Integral.lean:91` (already pinned for G.5). |
| **Koopman composition layer** (B7.1–B7.3) | ✅ | `Lp.coeFn_compMeasurePreserving` — `MeasureTheory/Function/LpSpace/Basic.lean:559`; `MeasurePreserving.comp` — `Dynamics/Ergodic/MeasurePreserving.lean:93`; `MeasurableEquiv.trans`/`refl`; on-disk template `koopman_comp_left`/`_right` in `BookProof/ChapterG.lean`. |

**Net effect (after pinning against real source).** Chapters B.1/B.2, C.1, D.1, E,
and the algebraic Schur core of §A.2 are near-total *reuse* — every needed lemma is
a pinned Mathlib declaration above. Two of my earlier assumptions were **corrected by
the source**: (i) **Plancherel L² is already in Mathlib** (`Lp.fourierTransformₗᵢ`),
so §A.4 Fourier props and B.3a need no Plancherel hypothesis; (ii) **there is no
Hilbert–Schmidt/compact-spectral machinery**, so the *only* measure/analysis item
that must become a hypothesis is the **B.3b SVD** (or restrict it to finite rank).
The DFT is `ZMod`-only, a minor build for E.3. Everything else that stays a named
hypothesis is representation-theoretic (Weyl, unitary/imprimitivity Schur, Mackey,
Pauli, Wigner) — none exist anywhere, confirmed by whole-repo grep. That is the
minimal, now source-verified, external surface.

---

# Chapter A — Real representations, CPT theorem, relativistic position operator

Source: `book.tex` §"Systems on real and complex Hilbert spaces" (line 4755) and
following. This chapter's core (Defns 1–34) is an abstract theory of **systems**
`(M,V)` and a **functor-like map** between real and complex systems, culminating
in the trichotomy *R-real / R-complex / R-pseudoreal* whose commutant algebras
are `ℝ / ℂ / ℍ`. The physics (Lorentz/Poincaré) is applied on top.

## §A.0 — Foundations: systems, complexification, realification

### Def 1 (System)
`(M, V)`: `V` a Hilbert space over `𝔽`; `M ⊆ End_bdd(V)` a set of bounded
endomorphisms.
```
structure System (𝔽 : Type) [RCLike 𝔽] (V : Type) [NormedAddCommGroup V]
    [InnerProductSpace 𝔽 V] [CompleteSpace V] where
  ops : Set (V →L[𝔽] V)
```

### Def 2 (Complexification) — of a system on a **real** Hilbert space `W`
`W^c := ℂ ⊗_ℝ W` with scalar action `a(bw) = (ab)w`, and inner product
```
⟪v_r + i v_i, u_r + i u_i⟫_c := ⟪v_r,u_r⟫ + ⟪v_i,u_i⟫ + i⟪v_r,u_i⟫ − i⟪v_i,u_r⟫.
```
*Lean.* Mathlib has `Complexification`/`TensorProduct ℝ ℂ W` and
`InnerProductSpace.complexification` — **verify the exact name**; if the bundled
complex inner-product instance is missing, this formula is the definition to
install. Each `m : W →L[ℝ] W` lifts to `m^c := (id ℂ) ⊗ m` on `W^c`;
`M^c := m^c '' M`.

### Def 3 (Realification) — of a system on a **complex** Hilbert space `V`
`V^r := V` as a real Hilbert space (scalars restricted to `ℝ`), with
`⟪v,u⟫_r := (⟪v,u⟫ + ⟪u,v⟫)/2 = Re⟪v,u⟫`.
*Lean.* `InnerProductSpace.rclikeToReal` / `RCLike` restriction of scalars gives
exactly this real inner product (`re⟪·,·⟫`). Use it; don't re-derive.

### Note 4 ((anti-)unitary operator)
`U : H₁ → H₂` ((anti-)linear) is **(anti-)unitary** iff (1) surjective and
(2) `⟪U x, U x⟫ = ⟪x,x⟫` for all `x`. (Polarization ⇒ preserves the full inner
product; for antilinear `U`, `⟪Ux,Uy⟫ = conj⟪x,y⟫`.)
*Lean.* For linear: `LinearIsometryEquiv`. For antilinear: define
```
structure AntiUnitary (H₁ H₂) ... where
  toFun : H₁ → H₂
  map_add' : ...            -- additive
  map_smul' : ∀ (c:ℂ) x, toFun (c • x) = conj c • toFun x
  surjective : Function.Surjective toFun
  norm_map' : ∀ x, ⟪toFun x, toFun x⟫ = ⟪x,x⟫   -- ⇒ ⟪Ux,Uy⟫ = conj ⟪x,y⟫
```

### Prop 5 (realification preserves (anti-)unitarity)
*Statement.* `H₁,H₂` complex Hilbert; `U : H₁ → H₂`. Then `U` is (anti-)unitary
**iff** `U^r : H₁^r → H₂^r` (same underlying map) is (anti-)unitary.

*Proof (English, Lean-ready).* Two facts: (i) `⟪h,h⟫ = ⟪h,h⟫_r` for every `h`,
because `⟪h,h⟫` is already real (`= Re⟪h,h⟫`), and `⟪·,·⟫_r = Re⟪·,·⟫` by Def 3;
(ii) `U^r` has the same underlying set-map as `U`, so `U^r(h) = U(h)`.
Surjectivity is identical for `U` and `U^r`. The norm condition
`⟪U h, U h⟫ = ⟪h,h⟫` is literally the same equation as
`⟪U^r h, U^r h⟫_r = ⟪h,h⟫_r` by (i). Hence each of the two defining clauses holds
for `U` iff it holds for `U^r`. ∎
*Lean.* One-liner after `simp [inner_realPart_eq, ...]`; the content is
`⟪h,h⟫_ℂ = (⟪h,h⟫_ℝ : ℝ)` via `RCLike.inner_apply`/`re_inner_self`.

### Def 6 (Equivalence / normal endomorphism / isometry)
Given systems `(M,V)`, `(N,W)`:
1. **Normal endomorphism** of `(M,V)`: bounded `S : V → V` commuting with `S†`
   and with every `m ∈ M`. (In a complex space an *anti-endomorphism* means an
   antilinear such `S`.)
2. **Isometry** of `(M,V)`: unitary `S : V → V` commuting with every `m ∈ M`.
3. `(M,V) ≃ (N,W)` (**unitary equivalent**) iff ∃ isometry `α : V → W` with
   `N = {α m α† : m ∈ M}` (i.e. `α` intertwines and conjugates `M` onto `N`).
*Lean.* Predicates on `System`. "Commutant" `Comm (M) := {S | ∀ m ∈ M.ops, S∘m = m∘S}`.
Normal endomorphisms = `{S ∈ Comm M | S∘S† = S†∘S}` (call it `normalComm M`).

### Def 7 (Irreducibility)
`(M,W)` is a (topological) **subsystem** of `(M,V)` iff `W` is a closed subspace
invariant under every `m ∈ M`. `(M,V)` is **irreducible** iff its only subsystems
are `{0}` and `V`.
*Lean.* `Subsystem M W := IsClosed W ∧ ∀ m ∈ M.ops, ∀ w ∈ W, m w ∈ W`
(`W : Submodule 𝔽 V` with closedness). `Irreducible M := ∀ W, Subsystem M W → W = ⊥ ∨ W = ⊤`.

### Def 8 (Structures: C-conjugation, R-imaginary)
1. On complex `(M,V)`: a **C-conjugation** `θ` is an antiunitary **involution**
   (`θ² = 1`) commuting with every `m ∈ M`.
2. On real `(M,W)`: an **R-imaginary** `J` is an isometry with `J² = −1`,
   commuting with every `m`.

---

## §A.1 — The map from complex to real systems

### Def 9 (C-real / C-pseudoreal / C-complex) — irreducible complex `(M,V)`
- **C-real**: ∃ a C-conjugation operator.
- **C-pseudoreal**: no C-conjugation, but ∃ an antiunitary operator commuting with `M`.
- **C-complex**: no antiunitary operator commuting with `M` at all.

### Def 10 (R-real / R-pseudoreal / R-complex) — real `(M,W)`, complexification `W^c`
- **R-real** iff `(M,W^c)` is C-real irreducible.
- **R-pseudoreal** iff `(M,W^c) ≅ (M,V) ⊕ (M,V̄)` with `(M,V)` C-pseudoreal irreducible.
- **R-complex** iff same with `(M,V)` C-complex irreducible.
(Here `V̄` is the conjugate space; `W^c = V ⊕ V̄`.)

### Prop 11 (every irreducible **real** system is R-real/pseudoreal/complex)
*Statement.* If `(M,W)` on a real Hilbert space is irreducible, it is one of the
three types of Def 10.

*Proof (English, Lean-ready).*
Set `θ : W^c → W^c`, `θ(u+iv) := u−iv` (`u,v ∈ W`). Check `θ` is an antiunitary
involution and commutes with every `m^c` (since `m` is real-linear), and its
fixed set is `(W^c)_θ = W`.

Let `(M,X^c)` be a proper non-trivial subsystem of `(M,W^c)`. Define
`Y^c := {u + θv : u,v ∈ X^c}` and `Z^c := {u : u ∈ X^c ∧ θu ∈ X^c}`. Then `θ`
restricts to a C-conjugation on both, so each is the complexification of a real
invariant closed subspace: `Y^c = Y ⊕ iY`, `Z^c = Z ⊕ iZ` with
`Y := {½(1+θ)u : u ∈ Y^c}`, `Z := {½(1+θ)u : u ∈ Z^c}` invariant closed subspaces
of `W`.
- If `Y = {0}` then `Z = {0}` and `X^c = Y^c = {0}`, contradicting non-triviality.
- If `Z = W` then `Y = W` and `X^c = Z^c = W^c`, contradicting properness.
By irreducibility of the **real** `(M,W)` the only remaining case is `Z = {0}`,
`Y = W`, whence `Z^c = {0}`, `Y^c = W^c`.

Consequently the map `α : (X^c)^r → W`, `α(u) := u + θu` is a bijective
intertwining isometry (inverse `u+θu ↦ u`), so `(M,W) ≅ (M,(X^c)^r)`, i.e. `W` is
the realification of the complex irreducible subsystem `X^c`. Finally, if
`(M,X^c)` admitted its **own** C-conjugation `θ'`, then
`W_± := {½(1±θ')w : w ∈ W}` would be a proper non-trivial subsystem of `(M,W)`,
contradicting irreducibility — so the type of `X^c` (C-real/pseudoreal/complex)
is well-defined and gives the R-type of `W`. ∎
*Lean notes.* The `½(1±θ)` projections need `θ² = 1`; the "closed subspace"
bookkeeping is the main work. `Y,Z` invariance uses that `m^c` commutes with `θ`.

### Prop 12 (converse: each R-type is irreducible)
*Statement.* Any real system that is R-real, R-pseudoreal or R-complex is
irreducible.

*Proof (English, Lean-ready).* Dual construction. Start from an irreducible
complex `(M,V)`; put `J : V^r → V^r`, `J u := i·u`, an R-imaginary operator of
`(M,V^r)`. Given a proper non-trivial subsystem `(M,X^r)` of `(M,V^r)`, form
`Y^r := {u + Jv : u,v ∈ X^r}`, `Z^r := {u : u ∈ X^r ∧ Ju ∈ X^r}`; these carry a
complex structure via `(a+ib)y := a y + b J y` and become complex subsystems
`(M,Y),(M,Z)` of `(M,V)`. Irreducibility of the **complex** `(M,V)` forces
`Z={0}, Y=V`, so `V = (X^r)^c`. Then `θ(u+iv):=u−iv` (`u,v∈X^r`) is a
C-conjugation with `X^r = V_θ`. If `(M,V_θ)` had an R-imaginary operator `J'`,
then `V_± := {½(1±iJ')v}` would be proper non-trivial subsystems of `(M,V)`,
contradiction. Hence: `(M,V)` C-real ⇒ `(M,V_θ)` R-real irreducible; `(M,V)`
C-pseudoreal/C-complex ⇒ `(M,V_θ^r)` R-pseudoreal/R-complex irreducible. ∎

**Package A.1.** Props 11+12 = a bijection (up to equivalence) between
{irreducible real systems} and {irreducible complex systems + a chosen
antiunitary/none}, sorted into the three types. In Lean, state as two lemmas
plus a `theorem realComplex_trichotomy` combining them.

---

## §A.2 — Schur systems and the commutant classification (ℝ / ℂ / ℍ)

### Def 13 (Schur system)
Complex `(M,V)` is **Schur** iff its algebra of normal operators (normal
endomorphisms commuting with `M`) is isomorphic to `ℂ`. Real Schur R-real /
R-pseudoreal / R-complex defined via the complexification, matching Def 10.

### Lemma 14 (uniqueness of the antiisometry up to phase)
*Statement.* In a **Schur** `(M,V)`, an antiisometry (antiunitary commuting with
`M`), if it exists, is unique up to a unit complex phase.

*Proof.* If `θ₁,θ₂` are antiisometries, `θ₂θ₁` is an isometry of `(M,V)` (linear,
unitary, commutes with `M`), hence a normal operator of a Schur system, hence a
scalar of modulus 1: `θ₂θ₁ = e^{iφ}`. So `θ₂ = e^{iφ} θ₁`. Writing
`α := e^{iφ/2}`, `θ₂ = α θ₁ α^{-1}` (using antilinearity: `α θ₁ = θ₁ ᾱ`). ∎

### Prop 15 (R-real systems: iso ⇔ complexifications iso)
*Statement.* Two R-real Schur systems are isometric iff their complexifications
are isometric.
*Proof.* Take C-real Schur `(M,V),(N,W)` with C-conjugations `θ_M,θ_N`. Given an
intertwining isometry `α : V→W` (`αM=Nα`), `ϑ := α θ_M α^{-1}` is an antiisometry
of `(N,W)`; by Lemma 14 `θ_N = e^{iφ} ϑ`, so `e^{iφ/2} α` maps `V_{θ_M} → W_{θ_N}`
isometrically, i.e. the real forms are isometric. Converse: a real isometry
complexifies. ∎

### Prop 16 (C-complex/pseudoreal: iso-or-antiiso ⇔ realifications iso)
*Statement.* Two C-complex or C-pseudoreal Schur systems are isometric **or**
antiisometric iff their realifications are isometric.
*Proof.* With R-imaginary operators `J_M,J_N`: an intertwining isometry `α`
transports `J_M` to `K := α J_M α^{-1}`, an R-imaginary operator of `(N,W)`.
On the complex form `W_{J_N} := {(1−iJ_N)w}` compute `(1−J_N K)(1−K J_N) = r ≥ 0`.
If `r=0` then `K=−J_N` and `α` is an **antiisometry** of the complex forms; if
`r>0` then `(1−J_N K)α r^{-1/2}` is an **isometry**. ∎
*(Book has a typo `c`/`r`; use `r` throughout.)*

### Prop 17 (R-real commutant ≅ ℝ)
*Statement.* The normal-operator algebra of an R-real Schur system is `ℝ`.
*Proof.* On C-real Schur `(M,V)` with conjugation `θ`, any commuting endomorphism
`α` is a scalar `r e^{iφ}` (Schur). Restricting to the real form `V_θ` forces the
scalar to be **real** (it must commute with the antilinear `θ`, so `e^{iφ}=±1`
absorbed into `r∈ℝ`). ∎

### Prop 18 (R-complex commutant ≅ ℂ)
*Statement.* The normal-operator algebra of an R-complex Schur system is `ℂ`.
*Proof.* R-imaginary `J`. For a normal operator `α` of `(M,V)`, put
`K := α + JαJ`; then `KK†` is a normal operator of the C-complex Schur system
`(M,V_J)`, so `KK† = r ≥ 0`. If `r>0`, `K/√r` is unitary and makes `V_J ≅ V̄_J`,
forcing C-pseudoreal — contradiction. So `K=0`, i.e. `α` commutes with `J`; hence
`α = r e^{Jθ}`, an element of the field `ℝ[J] ≅ ℂ`. ∎

### Prop 19 (R-pseudoreal commutant ≅ ℍ)
*Statement.* The normal-operator algebra of an R-pseudoreal Schur system is the
quaternions `ℍ`.
*Proof.* R-imaginary `J`. Let `K` be a unitary of `(M,V)` anticommuting with `J`;
then `K² = e^{Jθ}` and commuting `K` with `e^{Jθ}` gives `K² = −1`. For a general
endomorphism `α` split `α = S + T`, `S := (α−JαJ)/2` (commutes with `J`),
`T := (α+JαJ)/2` (anticommutes with `J`). Then `SS†,TT†` are self-adjoint on the
C-complex Schur `(M,V_J)`, hence non-negative scalars. `S` normal & commuting `J`
⇒ `S = a + Jb`; `T` normal & anticommuting `J`, and `TK` normal commuting `J`,
⇒ `T = Kc + KJd`. Therefore `α = a + Jb + Kc + KJd` with real `a,b,c,d` and
relations `J²=K²=(JK)²=−1`, i.e. `α ∈ ℍ`. ∎

**Package A.2.** Props 17–19 are the payoff: the three real types have commutant
algebras `ℝ, ℂ, ℍ` respectively (the real analogue of the Frobenius/Schur
trichotomy). In Lean, define `AlgEquiv` targets `ℝ`, `ℂ`, `Quaternion ℝ`.
`EXTERNAL`: Lemma 20/28/34 below are **Schur's lemma** at three levels; Mathlib
has Schur for finite-dim over alg-closed fields (`LinearMap.End` simple modules)
but **not** the unitary/imprimitivity forms — introduce as hypotheses.

### Lemmas 20–34 (Schur's lemma layers, complete reducibility, imprimitivity)
- **Lemma 20** (Schur, finite-dim complex): endomorphisms of an irreducible
  finite-dim complex rep are scalars. *Mathlib*: available via simple-module
  Schur over `ℂ` (alg. closed). Use directly.
- **Lemma 21** (finite-dim type criterion): an irreducible finite-dim complex
  rep is C-real / C-pseudoreal / C-complex according to whether it has an
  antilinear involution / an antiisomorphism but no involution / no
  antiisomorphism. *Proof.* Antiisomorphism `S` ⇒ `S² = r e^{iφ}` commutes with
  antilinear `S` ⇒ `S² = ±r` ⇒ rescale to antiunitary. ∎
- **Note 23 (Weyl)** finite-dim reps of a semisimple Lie group are completely
  reducible. `EXTERNAL` (cite; Mathlib lacks Weyl's theorem in this generality).
- **Def 24 (normal system)**: `M` closed under `†`.
- **Lemma 26** (orthogonal complement is a subsystem, for normal systems).
  *Proof.* `⟪m x, w⟫ = ⟪x, m† w⟫ = 0` since `m†w ∈ W` (as `m†∈M`, `W` invariant)
  and `x ⟂ W`. Fully elementary — **do in Lean directly** (no external input).
- **Lemma 27** (a complex Schur **normal** system is irreducible). *Proof.* For
  subsystem `W` with complement `W^⊥`, the orthogonal projection `P` onto `W`
  satisfies `P²=P=P†` and commutes with every `m` (compute `mP=Pm` on `w+x`);
  Schur ⇒ `P ∈ {0,1}` ⇒ `W ∈ {0,V}`. **Do in Lean directly**; needs Lemma 26 +
  existence of orthogonal projection (`orthogonalProjection`, Mathlib).
- **Lemma 28** (Schur for unitary reps): normal operators commuting with an
  irreducible unitary rep are scalars. `EXTERNAL` (spectral-theorem argument;
  cite `Ramakrishnan1999Fourier`).
- **Note 30**: unitary reps of separable locally compact groups are completely
  reducible (direct integral). `EXTERNAL`.
- **Def 31/32, Note 33 (Mackey Imprimitivity Theorem)**: `EXTERNAL` — the single
  biggest external dependency. State `(V,E)` imprimitivity systems and the
  equivalence to induced `(V_L,E_L)` as a hypothesis bundle.
- **Lemma 34** (Schur for systems of imprimitivity): normal operators commuting
  with an irreducible imprimitivity system are scalars. *Proof.* Via Mackey:
  reducibility of `L` ↔ a commuting projection ↔ reducibility of `(V,E)`; then
  Lemma 28 on `L`. Depends on Note 33 + Lemma 28.

> **Lean guidance for §A.2 tail (updated with reuse findings).** Do Lemmas 26 & 27
> in full (elementary, high value). **Lemma 20 (finite-dim complex Schur) is in
> Mathlib** — reuse `Module.End.instDivisionRing` / the simple-module hom-is-0-or-iso
> result from `Mathlib.RingTheory.SimpleModule.Basic`; do **not** axiomatize it. Only
> the genuinely-absent inputs — Lemma 28 (Schur for *unitary* reps), Lemma 34 (Schur
> for *imprimitivity* systems), Note 23/30 (Weyl / direct-integral complete
> reducibility), Note 33 (Mackey) — go into a `structure SchurInputs` of named
> hypotheses. This keeps everything `sorry`- and `axiom`-free while minimizing the
> external surface to exactly what no library has.

---

## §A.3 — Finite-dimensional representations of the Lorentz group

Source: book line 5196. Clifford-algebra / gamma-matrix layer. **Infrastructure
to build first:** a concrete model of the (3,1) Clifford algebra as
`Matrix (Fin 4) (Fin 4) ℂ`, i.e. **Majorana matrices** `iγ^μ` — `4×4` complex
unitary matrices with `(iγ^μ)(iγ^ν)+(iγ^ν)(iγ^μ) = -2η^{μν}` (`η=diag(1,-1,-1,-1)`).
The explicit real-orthogonal Majorana basis in the text (book eq. at 5271) can be
hard-coded as `!![...]` and the Clifford relations proved by `decide`/`norm_num`
on the 16 entries. Mathlib's abstract `CliffordAlgebra (Q)` is an option but the
`4×4` matrix model is more directly usable for the later transforms.

### Note 36 (Pauli's fundamental theorem of gamma matrices) — `EXTERNAL`
Two sets `A^μ, B^μ` of `4×4` **complex** matrices with `{A^μ,A^ν}=-2η^{μν}` (same
for `B`) are related by an invertible `S` with `B^μ = S A^μ S^{-1}`, `S` unique up
to a nonzero scalar; if all `A^μ,B^μ` unitary then `S` unitary. **Cite**
(`Good1955Properties`); do not re-prove. Introduce as a hypothesis
`pauliFundamental`. Everything in §A.3 builds on it.

### Prop 37 (real Pauli theorem)
**Statement.** Two sets `α^μ, β^μ` of `4×4` **real** matrices with
`{α^μ,α^ν}=-2η^{μν}` (same for `β`) are related by a **real** `S`, `|det S|=1`,
`β^μ = S α^μ S^{-1}`, unique up to sign.
**Proof (Lean-ready, given Note 36).** By Note 36 get complex invertible `T'`
with `β^μ = T' α^μ T'^{-1}`, unique up to scalar; normalize `T := T'/|det T'|` so
`|det T| = 1`, unique up to a phase. Conjugate the relation (entries of `α,β` are
**real**): `β^μ = T̄ α^μ T̄^{-1}`, so `T̄ = e^{2iθ} T` for some real `θ`
(uniqueness up to scalar + `|det|=1` ⇒ the scalar is a phase). Then `S := e^{iθ}T`
satisfies `S̄ = S` (real), `|det S| = 1`, and is unique up to sign. ∎
*Lean.* `Matrix.det`, complex conjugation of matrices (`Matrix.map (starRingEnd ℂ)`),
`|det|=1`. The "unique up to scalar ⇒ conjugate differs by phase" step is the crux.

### Def 38–42, Lemma 40 (Majorana/Dirac/Pauli matrices, charge conjugation)
- `γ^μ := -i·(iγ^μ)` (Dirac). `iγ^5 := iγ^0 iγ^1 iγ^2 iγ^3`-type product.
- **Lemma 40 (charge conjugation `Θ`).** `Θ` is an antilinear involution commuting
  with all `iγ^μ`, unique up to a complex phase. **Proof.** In a Majorana basis,
  entrywise complex conjugation is such a `Θ`. If `Θ,Θ'` both work, `ΘΘ'` is a
  linear invertible matrix commuting with every `iγ^μ`, so by Note 36 `ΘΘ' = c`
  (scalar); `Θ' = c̄ Θ`; `Θ'² = 1` ⇒ `|c|² = 1`. ∎ *(This is the finite-dim
  instance of the C-conjugation of §A.0 Def 8.)*
- **Def 41 Majorana spinors** `Pinor := {u ∈ ℂ⁴ | Θ u = u}`: a **4-dim real**
  vector space (real form of `ℂ⁴`). `End(Pinor) ≅ Matrix (Fin 4) (Fin 4) ℝ`
  (16-dim, spanned by products of Majorana matrices). *(Lean: fixed points of an
  antilinear involution form a real subspace with real-dimension = complex-dim.)*
- **Def 42 Pauli** `σ^k` (`2×2` Hermitian unitary anticommuting); `Pauli := ℂ²`,
  real-4-dim; `Pauli^r ≅ Pinor`.

### Note 43 (Lorentz group), Def 44–45 (`Maj`, `Pin(3,1)`)
- `O(1,3) := {λ ∈ Matrix (Fin 4)(Fin 4) ℝ | λᵀ η λ = η}`; `SO⁺(1,3)` the
  `det=1, λ⁰₀>0` component; `Δ := {1,η,-η,-1}`; `O(1,3) = Δ ⋉ SO⁺(1,3)`.
- `Maj := span_ℝ {iγ^μ}` (4-dim). `Pin(3,1) := {S ∈ End(Pinor) | |det S|=1 ∧ ∀μ, S⁻¹(iγ^μ)S ∈ Maj}`.

### Prop 46 (`Λ : Pin(3,1) → O(1,3)` is a 2-to-1 surjective homomorphism)
**Statement & Proof (Lean-ready).** For `S ∈ Pin(3,1)`, since `{iγ^μ}` is a basis
of `Maj`, define `Λ(S)` by `Λ(S)^μ_ν iγ^ν = S⁻¹(iγ^μ)S` (unique real matrix).
- *Lands in `O(1,3)`:* compute
  `Λ(S)^μ_α η^{αβ} Λ(S)^ν_β = -½ Λ^μ_α{iγ^α,iγ^β}Λ^ν_β = -½ S{iγ^μ,iγ^ν}S⁻¹ = S η^{μν} S⁻¹ = η^{μν}`
  using the Clifford relation.
- *Surjective 2-to-1:* given `λ ∈ O(1,3)`, `α^μ := λ^μ_ν iγ^ν` satisfies the same
  Clifford relations (metric preserved), so **Prop 37** gives real `S_λ`,
  `|det|=1`, unique up to sign, with `α^μ = S_λ⁻¹(iγ^μ)S_λ`; hence `±S_λ ∈ Pin(3,1)`
  and `Λ(±S_λ)=λ`.
- *Homomorphism:* `Λ(S₁)Λ(S₂)` acts as `Λ(S₁S₂)` by the chain
  `Λ^μ_ν(S₁)Λ^ν_ρ(S₂)iγ^ρ = S₂⁻¹S₁⁻¹ iγ^μ S₁S₂`. ∎

### Note 47, Lemma 48, Def 49 (SL(2,ℂ), Spin⁺(3,1), discrete Pin subgroup Ω)
- `SL(2,ℂ) = {exp(θ^j iσ^j + b^j σ^j)}` simply connected; 2-to-1
  `Υ : SL(2,ℂ) → SO⁺(1,3)`, `Υ^μ_ν(T)σ^ν = T† σ^μ T`.
- **Lemma 48.** Via the explicit isomorphism `Σ : Pauli → Pinor` (book eq. 5468,
  matching `±`-eigenspaces of `γ⁰γ³` / `σ³`), `Spin⁺(3,1) := Σ∘SL(2,ℂ)∘Σ⁻¹` is a
  subgroup of `Pin(3,1)` and `Λ(S) = Υ(Σ⁻¹∘S∘Σ)`. **Proof** as in text: identity
  `-iγ⁰ Σ T† Σ⁻¹ iγ⁰ = Σ T⁻¹ Σ⁻¹`, then `S⁻¹iγ^μS = Υ^μ_ν(...)iγ^ν ∈ Maj`;
  `det S = 1` because all nontrivial Majorana-matrix products are traceless.
- **Def 49** `Ω := {±1, ±iγ⁰, ±γ⁰γ⁵, ±iγ⁵}`, the double cover of `Δ`; hence
  `Pin(3,1) = Ω ⋉ Spin⁺(3,1)`, a double cover of `O(1,3)`; `Spin⁺(3,1)∩SU(4) ≅ SU(2)`
  double-covers `SO(3)`.

### Notes 50–51, Lemma 52 (classification of finite-dim irreducible reps)
- **Note 50 (Weyl)** finite-dim reps of `SL(2,ℂ)` are completely reducible.
  `EXTERNAL` (as Note 23).
- **Note 51 (complex irreps).** Complex irreps of `SL(2,ℂ)` labelled `(m,n)`
  (`2m,2n ∈ ℕ`), `V_{(m,n)} = V⁺_m ⊗ V⁻_n` (symmetric tensor powers of Dirac
  spinors, `γ⁵`-eigenspaces). Under parity `(V⁺_m⊗V⁻_n) ↔ (V⁻_m⊗V⁺_n)`; under time
  reversal fixed. *(Standard; can cite or build on the `SL(2,ℂ)` rep theory.)*
- **Lemma 52 (real irreps — the payoff).** The finite-dim **real** irreducibles of
  `SL(2,ℂ)` are labelled `(m,n)` with `m ≥ n`, `W_{(m,n)}` defined (book eq. 5566)
  via the `½(1+(iγ⁵)₁⊗(iγ⁵)₁)` projection of `W_m⊗W_n` (`W_m` = symmetric Majorana
  tensors). **Proof (using §A.1 map).** For `m≠n` the complex irrep is **C-complex**,
  and `W_{(m,n)}^c = (V⁺_m⊗V⁻_n) ⊕ (V⁻_m⊗V⁺_n)` (so R-complex, §A.1). For `m=n` the
  complex irrep is **C-real** with explicit conjugation `θ(u⊗v)=v*⊗u*` and bijection
  `α : W_{(m,m)} → (V_{(m,m)})_θ`, `α(w)=½(1-i(iγ⁵)₁⊗1)w` (so R-real). By the
  §A.1–A.2 trichotomy these `W_{(m,n)}`, `m≥n`, are **all** the real irreps up to
  iso, and each is a projective rep of the **full** Lorentz group (`W_{(m,n)}^c ≅
  W_{(n,m)}^c`, invariant under parity & time reversal). ∎
  *This is the chapter's headline finite-dim result: unlike complex irreps, the
  real irreps are automatically full-Lorentz (parity+T) projective reps.*

> **Lean strategy for §A.3.** Build the `4×4` Majorana matrix model + Clifford
> relations (concrete, `decide`-able). Take Note 36 (Pauli) and Note 50 (Weyl) as
> named hypotheses. Then Prop 37, Lemma 40, Prop 46, Lemma 48, Lemma 52 are all
> provable. This is a large but self-contained sub-project; ~1–2k lines of Lean.
> Depends on §A.0–A.2 for the trichotomy used in Lemma 52.

## §A.4 — Unitary representations of the Poincaré group (Majorana–Fourier, CPT)

Source: book line 5636. **This is the deepest, heaviest sub-project.** It layers
the §A.3 Clifford model + Bargmann–Wigner fields + `EXTERNAL` Mackey imprimitivity
(§A.2 Note 33) + `EXTERNAL` Wigner little-group theory. **Field content follows
§0 S7 (author directive 2026-07-03): the Mehler/Kopperman formalism as implemented
in `../unfer`** — fields in Hermitian representation `φ = a† + a`,
`π = i(a† − a)`; Hamiltonians quadratic-ordered (`⟨0|H|0⟩ = 0`); Fock structure =
the U.3 `SymmetricAlgebra` layer, with `nested_fock_algebra` cited in docstrings. Recommendation: formalize
**last**, and split into (i) the "unitarity by direct computation" props (doable),
and (ii) the classification props (research-level; state carefully, lean on
external inputs). Everything below is `sorry`/`axiom`-free provided the named
external theorems are taken as hypotheses.

**Bargmann–Wigner scaffolding (Defs 53–60).**
- `Θ_H : Pauli ⊗_ℝ H → Pinor ⊗_ℝ H` the real-linear iso from the `Pauli^r ≅ Pinor`
  identification (Def 53); `U^Θ := Θ_{H₂}∘U∘Θ_{H₁}⁻¹` (Def 54) transports Pauli
  operators to Pinor operators.
- `Pinor(𝕏) := Pinor ⊗ L²(𝕏)`, `Pauli(𝕏) := Pauli ⊗ L²(𝕏)` (Defs 55–56).
- `Pinor_j` = symmetric tensor power of `2j` Majorana spinors (`Pinor₀` =
  antisymmetric pair) (Def 57); `Pinor_j(𝕏)` its `L²` version (Def 58).
- `BW_j` (real **Bargmann–Wigner fields**, Def 59): `Ψ ∈ Pinor_j(ℝ³)` with the
  Dirac constraint `(e^{iH(x)t})_k Ψ = (e^{iH(x)t})_1 Ψ` for all indices `k`,
  `t`; `Dirac_j(𝕏)` its complexification (Def 60). *(The "differentiable ⇒
  bounded extension" remark = `ContinuousLinearMap` density argument.)*

### Props 61, 73, 74, 76 (unitarity by direct computation) — **doable**
All four assert a specific operator is unitary and prove it by `A†A = 1 = AA†`.
- **Prop 61.** If `U : Pinor_j(ℝ³) → Pinor_j(𝕏)` is unitary with `U∘H² = E²∘U`
  (`iH = γ⁰∂̸ + iγ⁰m`, `E(X) ≥ m ≥ 0`), then
  `U' := (E + U H γ⁰ U†)/(√(E+m)·√(2E))` is unitary. **Proof.** `E=√(E²)` commutes
  with `U Hγ⁰ U†`; expand `(U')†U' = (E+Uγ⁰HU†)(E+UHγ⁰U†)/((E+m)2E)` and use
  `γ⁰H + Hγ⁰` and `H² = U†E²U` to collapse to `1`; symmetrically `U'(U')† = 1`. ∎
  *Lean:* functional calculus `√(E²)=E` on the positive operator `E²`
  (`cfc`/`ContinuousFunctionalCalculus`), operator algebra.
- **Note 62 / Prop 73 (Majorana–Fourier `𝓕_M`).** `𝓕_M := (𝓕_P)^Θ`, the Pauli
  Fourier transform `𝓕_P` **unitary on `L²` = Mathlib `MeasureTheory.Lp.fourierTransformₗᵢ`
  (`Analysis/Fourier/LpSpace.lean:49`, a `≃ₗᵢ[ℂ]`; Plancherel `Lp.norm_fourier_eq`)** —
  reuse directly, no Plancherel hypothesis — transported by `Θ`. Unitary because a `Θ`-conjugate of a
  unitary is unitary (`Θ` is a real-linear iso). **Prop 74** = its inverse
  `𝓕_M⁻¹ = (𝓕_P⁻¹)^Θ`.
- **Prop 76 (Energy transform `𝓔`).** `𝓔 := Θ_{L²}∘𝓕_P(-p⁰)∘Θ_{L²}⁻¹` (Fourier in
  the **time** coordinate). Unitary for the same conjugation reason. Composés
  `𝓔∘𝓕_M` (linear) and `𝓔∘𝓗_M` (spherical, `𝓗_M` a Majorana–Hankel transform)
  give the unitary energy-momentum transforms.
> These four are the tractable core of §A.4: given `𝓕_P` unitary and the `Θ`
> machinery, they reduce to "conjugate/algebraic combination of unitaries is
> unitary." **Do these in Lean.**

### Def 77–78, Prop 79, Notes 80–83 (little group + irrep classification)
- `IPin(3,1) := Pin(3,1) ⋉ ℝ⁴` (Def 77), `(A,a)(B,b)=(AB, a+Λ(A)b)`; `ISL(2,ℂ)`
  the `Spin⁺` sub. Little group `G_l := {g ∈ SL(2,ℂ) | g l̸ = l̸ g}` (Def 78).
- **Prop 79.** With intertwiners `α_k` (`α_k l̸ = k̸ α_k`),
  `H_k := {α_{Λ_S(k)}⁻¹ S α_k : S ∈ SL(2,ℂ)} = G_l`. **Proof.** `H_k ⊆ G_l`
  directly; for `s ∈ G_l`, `S := α_{Λ_S(k)} s α_k⁻¹` realizes `s ∈ H_k`. ∎ Concrete
  little groups: `i l̸ = iγ⁰ ⇒ G_l = SU(2)` (massive), `i l̸ = iγ⁰+iγ³ ⇒ G_l = SE(2)`
  (massless), with the explicit `α_p` boosts given.
- **Notes 80–83 (Bargmann–Wigner classification).** Massive (Note 80 complex /
  **Prop 81** real) and massless-discrete-helicity (Note 82 complex / Note 83 real)
  irreducible projective Poincaré reps, labelled by `j` (`2j ∈ ℕ` or `ℤ`), realized
  as symmetric Majorana/Dirac spinor tensor fields on 3-momentum space with the
  constraints `(γ⁰)_k Ψ = Ψ` (Dirac) / `(iγ⁰)_k Ψ = (iγ⁰)_1 Ψ` (Majorana) and
  explicit `L_S, T_a`. These are **standard Wigner classification** results recast
  in the Majorana formalism; `EXTERNAL` backbone (Wigner 1939) + explicit formulas
  to verify. In Lean: state the reps as structures and *verify* the group-rep
  axioms for the given `L_S,T_a` (checkable), citing Wigner for exhaustiveness.

### Localization: Notes 84–86, Props 87–88, Corollary 1 — **the CPT payoff**
- **Note 84** (`EXTERNAL`, Varadarajan Thm 6.12): complex imprimitivity systems on
  `ℝ³` ↔ `SU(2)` representations.
- **Def 85–86** covariant / localizable real unitary Poincaré rep: an imprimitivity
  system on `ℝ³` where at `x⁰=0, x⃗=0` the Lorentz transformations don't move the
  space coordinates (`L{Ψ}(0)=S Ψ(0)`).
- **Prop 87.** *Any* localizable unitary Poincaré rep is a **direct sum of
  irreducibles that are massive or massless-with-discrete-helicity.* **Proof
  (structure).** Decompose into irreducibles (Note 30/Mackey); Fourier-transform
  the translation action to `(U e^{J p⃗·a⃗} U⁻¹)Ψ(p⃗) = e^{iγ⁰ p⃗·a⃗}Ψ(p⃗)`, valid
  for all `p⃗`. This excludes `m²<0` (needs `p⃗²≥|m²|`) and `p=0` (needs `p⃗=0`) as
  subspaces, and excludes `m²=0` **infinite-spin** (a `z`-boost scales the `SE(2)`
  translation modulus by `E_p`, contradicting that `S := LΛ⁻¹` is `p⃗`-independent).
  Left: massive + massless-discrete-helicity. ∎ *(Heavy: little-group boosts,
  imprimitivity. State the three exclusions as lemmas.)*
- **Prop 88.** A **complex** localizable rep containing a positive-energy subrep
  also contains the corresponding negative-energy one. **Proof.** The `iγ⁰`-sign
  projectors are **not** conserved by the imprimitivity system, since `γ⁰` does not
  commute with the `γ⃗γ⁰` in the momentum→position map; back in position space the
  `iγ⁰`-projector becomes a time-translation equality outside the commuting ring of
  the `SU(2)` system. ∎ *(This is the "causality ⇒ antiparticles" statement.)*
- **Corollary 1 (CPT / position-operator payoff).** A localizable Poincaré rep is
  **irreducible under the full Poincaré group (including parity) iff it is (a) real
  and (b) massive spin ½ or massless helicity ½.** **Proof.** Full-Poincaré
  irreducibility can't use the non-conserved `iγ⁰`-projectors, which is possible
  only for a **real** rep with a **single spinor index** (`j=½`). ∎ In that case the
  position operator coincides with the Dirac-equation coordinates. The closing
  remarks (bump-function localizability vs no closed position subspace for `j>½`;
  frame-field/tetrad workaround carrying arbitrary spin; complex chiral massless
  admitting localized solutions with **antilinear** parity; causality via
  `Δ(x)=0` for spacelike `x`) are physics discussion — capture as docstrings, not
  theorems.

## §A.5 — Spinor frame & CPT (book line 6453)
Closing section: the CPT/energy operator `iH = ∂⃗·γ⃗γ⁰ + iγ⁰m₁ + γ⁰γ⁵m₂` and the
frame-field construction (4 orthogonal Majorana spinors carrying arbitrary spin,
enabling a position operator). Formalizable as concrete `4×4` operator identities
on the §A.3 Clifford model; low marginal value beyond §A.3/§A.4. Capture with §A.4.

> **Overall §A.4/A.5 recommendation.** Implement Props 61/73/74/76 (unitarity) on
> top of §A.3 — these are honest, self-contained Lean lemmas. Treat the
> classification (Notes 80–83, Props 87–88, Cor 1) as a **specification layer**:
> encode the statements and the explicit rep formulas, take Wigner little-group
> theory + Mackey imprimitivity + Varadarajan Thm 6.12 as named `EXTERNAL`
> hypotheses, and prove the *reductions* (the three exclusions in Prop 87, the
> projector-non-conservation in Prop 88/Cor 1). This keeps the whole chapter
> `axiom`-free while honestly delimiting what is genuinely new (the Majorana/real
> recasting + Cor 1) versus cited (Wigner/Mackey).

---

# Chapter B — Wave-function parametrization of a probability measure

Source: `book.tex` §3 (line 1392). **Headline result:** every joint probability
density on a product of standard measure spaces is the Born rule `|Ψ|²` of a unit
vector `Ψ ∈ L²`, equivalently the first "column" of a unitary
`𝒰 : ℓ²(ℤ) → L²(X×Y)`; and this is reversible. The book calls this "a commutative
version of Wigner's theorem." Everything here is standard measure theory + Hilbert
space theory and is a strong Mathlib target.

**Standing setup for Chapter B.** `X, Y` standard (standard Borel + σ-finite, or
just take them to be `ℝ`/countable — the theorem is stated up to null sets).
`μ, ν` the measures; `L²` always means complex `MeasureTheory.Lp ℂ 2`.
Densities are `p : X×Y → ℝ≥0∞` (or `ℝ≥0`) measurable with `∫⁻ p ∂(μ⊗ν) = 1`.
**Follow §0 (Kopperman/Mehler).** `L²(X×Y)` is separable; reuse the substrate
`PnpProof/Kopperman.lean` (`Substrate`, `substrate_decidable_skeleton`,
`MehlerPrior`). The reference marginal `p₀ > 0` is the **Mehler/Gaussian** measure
(`gaussianReal`/`IsGaussian`, `noAtoms_gaussianReal`), and `Ψ = √(p/p₀)` is the Born
square-root against it; the SVD (B.3b) is done finite-rank on the dense core `D₀` then
closed. So Chapter B is the abstract statement of the Kopperman "wave-function =
parametrization of a probability measure" substrate.

### B.1 — Born parametrization (the essential, fully self-contained core)
**Theorem B.1 (density ⇔ unit vector).**
1. *(Forward / square root.)* For every probability density `p` on `X×Y` there is
   `Ψ ∈ L²(X×Y; ℂ)` with `‖Ψ‖ = 1` and `|Ψ(x,y)|² = p(x,y)` a.e. One may take
   `Ψ := (Real.sqrt ∘ p : X×Y → ℝ) : → ℂ` (nonnegative real representative).
2. *(Backward / Born rule.)* For every `Ψ ∈ L²(X×Y)` with `‖Ψ‖ = 1`, the function
   `p := |Ψ|²` is a probability density: measurable, `≥ 0`, and `∫ p = ‖Ψ‖² = 1`.

*Proof (English, Lean-ready).*
(2) is immediate: `p = |Ψ|²` is measurable and nonnegative, and
`∫⁻ |Ψ|² ∂(μ⊗ν) = ‖Ψ‖_{L²}² = 1` by the definition of the `L²` norm
(`MeasureTheory.L2.norm_sq_eq_inner`/`lintegral_norm_sq`). 
(1): let `f := Real.sqrt ∘ p`. Then `f ≥ 0`, measurable, and `f² = p` pointwise
(as `p ≥ 0`, `Real.sq_sqrt`). Coerce to `ℂ`; membership in `L²` holds because
`∫⁻ ‖(f:ℂ)‖² = ∫⁻ f² = ∫⁻ p = 1 < ∞` (`MeasureTheory.memℒp_of_...`), and then
`‖Ψ‖² = 1`. Pointwise `|Ψ|² = f² = p`. ∎
*Lean hooks.* `Real.sqrt`, `Real.sq_sqrt`, `MeasureTheory.MemLp` (formerly `Memℒp`),
`MeasureTheory.Lp`, `MeasureTheory.L2.inner_def`, `lintegral_coe_eq_integral`.
This is the piece to implement first — no external theorems needed.

### B.2 — Unit vector extends to a unitary (`Ψ = 𝒰 e₀`)
**Theorem B.2.** Let `H` be a separable complex Hilbert space and `Ψ ∈ H` a unit
vector. Then there is a unitary (surjective linear isometry)
`𝒰 : ℓ²(ℤ; ℂ) → H` with `𝒰 (e₀) = Ψ`, where `e₀` is the standard basis vector at
`0 ∈ ℤ`. Applied to `H = L²(X×Y)` and `Ψ` from B.1 this yields the book's
`𝒰(y,x,0) = Ψ(x,y)` with `p(x,y) = |𝒰(y,x,0)|²`.

*Proof (English, Lean-ready).* Extend `{Ψ}` to a `HilbertBasis` of `H` indexed by
`ℤ` with `b 0 = Ψ`: since `H` is separable and infinite-dimensional it has a
`HilbertBasis ℤ ℂ H`; apply Gram–Schmidt starting from `Ψ` (Mathlib
`gramSchmidtOrthonormalBasis` / `HilbertBasis.mk` from a maximal orthonormal set
containing `Ψ`). Let `𝒰` be the isometry sending the standard Hilbert basis of
`ℓ²(ℤ)` to `b`; it is unitary (`HilbertBasis.repr`/`.reprSymm` is a
`LinearIsometryEquiv`). Then `𝒰 e₀ = b 0 = Ψ`. (If `H` is finite-dim of dim `n`,
use `ℓ²(Fin n)` / `Fin n` index; the book uses `ℤ` and a countable basis, so the
separable-infinite case is the intended one — pad with zeros as in the text when
the density's support basis is finite.) ∎
*Lean hooks.* `HilbertBasis`, `OrthonormalBasis`, `gramSchmidtOrthonormalBasis`,
`LinearIsometryEquiv`, `EuclideanSpace`/`lp 2`. No external theorems.

**Corollary B.2′ (converse, book's "bounded `B` with `tr(BB†)=1`").** A bounded
operator viewed as an `L²` kernel `B ∈ L²(X×Y)` with `‖B‖₂ = 1`
(`tr(BB†) = ‖B‖_{HS}² = 1`) defines `p := |B|²`, a probability density (B.1(2));
and on a standard space `p` admits a regular conditional density
`p(y|x) = p(x,y)/p₀(x)` wherever `p₀(x) := (B†B)(x,x) > 0`. The existence of the
regular conditional probability is Mathlib's **disintegration for standard Borel
spaces** (`MeasureTheory.Measure.condKernel`, `ProbabilityTheory.Kernel.disintegration`)
— use it; not external.

### B.3 — Operator form, Hilbert–Schmidt bound, SVD, and conditionals
The book upgrades `Ψ` to an operator `Ψ : L²(X) → L²(Y)` (integral kernel
`Ψ(x,y)`) and records:
- **B.3a (bounded).** `‖Ψ Φ‖²_{L²(Y)} = ∫ dy |∫ dx Ψ(x,y)Φ(x)|² ≤ ‖Φ‖² · ∫∫|Ψ|² = ‖Φ‖²`,
  by Cauchy–Schwarz in `x` pointwise in `y` then integrating. So `‖Ψ‖_op ≤ 1`. In
  fact `Ψ` is **Hilbert–Schmidt** with `‖Ψ‖_HS = ‖Ψ‖_{L²(X×Y)} = 1`.
  *Lean.* `MeasureTheory.L2.integral_inner`/`inner_mul_le_norm_mul_norm`
  (Cauchy–Schwarz), and the HS identity via Mathlib's `HilbertSchmidt` /
  `Schatten 2` if present; otherwise state HS norm = `L²` kernel norm as a lemma.
- **B.3b (SVD / polar).** A Hilbert–Schmidt (hence compact) operator admits a
  singular value expansion `Ψ = W D U†` with `D ≥ 0` diagonal, `U` unitary, `W`
  unitary (after padding the partial isometry to a unitary via Gram–Schmidt as in
  the text, `V V† W = V`). **Handled by the §0 dense-core method (S3), not a gap.**
  Mathlib's spectral theorem is finite-dim only (`LinearMap.IsSymmetric.eigenvectorBasis`,
  `Spectrum.lean:280`) and there is no `HilbertSchmidt`/`Schatten` or infinite-dim
  compact spectral theorem — but under Kopperman §0 you **never need them**: diagonalize
  `Ψ†Ψ` **on the finite-support core `D₀`** (finite-dim, `eigenvectorBasis` applies
  verbatim), obtaining the SVD level-by-level, then **extend by density/closure** to the
  full separable `H`. The partial isometry `V` (padded to unitary `W`, `V V† W = V`) is
  literally the Kopperman **partial-isometry** object (`V†V`, `VV†` projections). No
  named hypothesis, no `axiom` — just the core method.
- **B.3c (conditionals).** With `p₀` the reference marginal, `T p₀ T† = Ψ Ψ† = W D² W†`
  and generally `T p T† = Ψ (p/p₀) Ψ† = W D U† (p/p₀) U D W†`. This is the
  algebraic identity turning a change of marginal `p₀ → p` into conjugation by
  `√(p/p₀)`; formalize as an operator identity once `Ψ = WDU†` is available.

**What to build in Lean (Chapter B).** B.1 and B.2 (+B.2′ via `condKernel`) are
fully self-contained and should be implemented completely — they are the theorem.
B.3a is a clean Cauchy–Schwarz/Hilbert–Schmidt exercise. B.3b/B.3c depend on a
compact-operator SVD; package as a hypothesis if Mathlib lacks it, and flag for
the author. No `axiom`s anywhere.

> **Remark (Gleason contrast, non-formalized).** The book's comparison with
> Gleason's theorem (commuting vs non-commuting projections; pure vs mixed states;
> the explicit 2×2 counterexample showing no *pure* `ρ` matches both a diagonal
> and a `½[[1,1],[1,1]]` projection value ½ simultaneously, while a *mixed* `ρ`
> does) is a worked numerical example, not a theorem to formalize — but the 2×2
> counterexample **is** a nice standalone `example` (finite-dim, decidable) worth
> adding as a sanity check: `∄ ρ pure, tr(ρ P₁)=½ ∧ tr(ρ P₂)=½` for
> `P₁=[[1,0],[0,0]]`, `P₂=½[[1,1],[1,1]]`. Low priority.

---

# Chapter C — Entropy and irreversible deterministic time-evolution coexist

Source: `book.tex` line 9474. The chapter is mostly physics/cosmology prose
(baryon asymmetry, Standard Model CP violation, cosmological amplification) —
**not formalizable**. Two extractable mathematical nuggets:

### C.1 — Vanishing probability of an invertible partition map (Stirling)
**Statement.** Partition `[0,1]²` into `n²` equal squares; index rows/columns by
`Fin n`. A "discrete function" is any `f : Fin n → Fin n`; it is *invertible* iff
`f` is a bijection (a permutation). Under the uniform measure on `(Fin n)^(Fin n)`
(all `nⁿ` functions equally likely), the probability that `f` is invertible is
`n!/nⁿ`, and
```
n!/nⁿ  ~  √(2πn) · e^{-n}   (n → ∞),   and   n!/nⁿ → 0.
```
**Proof (Lean-ready).** Count: `#{permutations} = n!`, `#{all functions} = nⁿ`, so
the probability is `n!/nⁿ` (`Fintype.card_perm`, `Fintype.card_fun`). For the
limit and asymptotic, use Mathlib's **Stirling**:
`Stirling.factorial_isEquivalent_stirling : (n! : ℝ) ~ √(2πn) (n/e)ⁿ`. Dividing by
`nⁿ` gives `n!/nⁿ ~ √(2πn) (1/e)ⁿ = √(2πn) e^{-n}`. Since `√(2πn) e^{-n} → 0`
(exponential beats `√`), `n!/nⁿ → 0` by `Asymptotics.IsEquivalent.tendsto_nhds` /
squeeze. **Fully self-contained; do in Lean directly.** Good first exercise.

### C.2 — "A randomly sampled map is a.s. non-singular (injective)" (informal)
The claim that a function sampled to be consistent with the continuous uniform
measure is almost surely non-singular (maps positive-measure sets to
positive-measure sets), because conditional probabilities on positive-measure
sets stay continuous, is a genuine measure-theoretic statement but is stated
loosely in the text (no precise probability space for "a random measurable map").
**Recommendation:** do not formalize as-is; it needs the author to pin down the
sampling measure. Flag for the author. The `n!/nⁿ → 0` computation (C.1) is the
rigorous shadow of the same idea (permutations are exponentially rare).

*Everything else in Chapter C (baryon asymmetry, CP violation, cosmology) is
physics prose — no formalization.*

---

# Chapter D — Aligned deep learning as a random sampling method

Source: `book.tex` line 9606. Overwhelmingly an essay on AI alignment, Bayesian
inference vs deep learning, epistemics — **not formalizable**. One crisp,
genuinely formalizable mathematical statement anchors the argument:

### D.1 — Almost all functions are uncomputable (computable ⇒ countable)
**Statement.** The set of computable functions `ℕ → ℕ` is countable; hence it is a
"negligible" subset of the uncountable set of all functions `ℕ → ℕ` — under any
atomless/product measure on `(ℕ → ℕ)` (or on `ℕ → Bool`) it has measure zero, and
topologically it is meager. This is the precise content of the book's "under
reasonable assumptions, almost all functions are not computable."
**Proof (Lean-ready).**
1. *Countability.* Every computable function has a code (index of a Turing machine
   / a `Nat.Partrec` code), and codes are naturally indexed by `ℕ`. Mathlib:
   `Nat.Partrec.Code` is (computably) encodable/countable (`Encodable`), and the
   evaluation `Code → (ℕ →. ℕ)` is surjective onto the partial computable
   functions. Therefore `{f : ℕ → ℕ | Computable f}` is the image of a countable
   type under a map, hence **countable** (`Set.Countable`), via
   `Set.countable_range`/`Countable` of `Nat.Partrec.Code`.
2. *Negligibility.* `ℕ → ℕ` (equivalently `ℕ → Bool ≃ Cantor space`) is
   uncountable; a countable subset of an atomless probability space has measure 0
   (`MeasureTheory.Measure.countable_setOf... ` / a countable set is null for any
   measure with no atoms). For `ℕ → Bool` with the `(½,½)` Bernoulli product
   measure (`MeasureTheory.Measure.pi`/`bernoulli`), singletons are null, so any
   countable set is null: `measure {computable} = 0`.
**Lean hooks.** `Nat.Partrec.Code`, `Computable`, `Encodable`, `Set.Countable`,
`MeasureTheory.Measure.pi`, `measure_countable` (countable ⇒ null under atomless).
The countability half is clean and self-contained; the measure-zero half needs the
Bernoulli/product measure on `ℕ → Bool` and "atomless ⇒ countable is null."
No external theorems, no `axiom`.

### D.2 — (context, non-formalized)
The surrounding claims — universal approximation theorem, Wilks' theorem, "deep
nets sample computable models," "no non-informative priors" — are either external
cited theorems or informal modelling. Not formalized. D.1 is the one theorem.

---

# Chapter E — Wave-function collapse versus Euler's formula

Source: `book.tex` line 3229. Elementary but genuinely theorem-rich: the
wave-function as a "multi-dimensional Euler formula" parametrizing any probability
distribution, with collapse = "taking the real part." All finite-dimensional and
concrete (2×2 and `n×n` real matrices) except E.4's infinite recursion. Strong,
low-risk Mathlib target; good confidence-builder before the Clifford chapters.
**Per §0**, E.4's countable recursion is the Kopperman **dense-core** picture — the
finite slices `E.1`–`E.3` are exactly the finite-support core `D₀`, and the `ℕ`-limit
is the Mehler hypersphere→Gaussian passage (`substrate_decidable_skeleton` + tail
product → 0); prove on `Fin N` first, then close.

### E.1 — The 2-state probability clock
Let `J := !![0,-1;1,0]` (rotation generator) and `J' := !![0,1;-1,0]` (`J'² = -I`).
Define `Ψ t := !![Real.cos t; Real.sin t]` (a `Fin 2 → ℝ` unit vector).
**E.1a (surjectivity).** `∀ p, 0 ≤ p → p ≤ 1 → ∃ t, Real.cos t ^ 2 = p`. *Proof.*
`t := Real.arccos (Real.sqrt p)`; `cos t = √p` on `[0,1]`, so `cos²t = p`
(`Real.cos_arccos`, `Real.sq_sqrt`). ∎
**E.1b (Euler rotation).** `Matrix.exp (t • J) = !![cos t, -sin t; sin t, cos t]`
and hence `(Matrix.exp (t•J)) *ᵥ ![1,0] = ![cos t, sin t] = Ψ t`, and
`Ψ (t+a) = (Matrix.exp (a•J)) *ᵥ Ψ t`. *Lean.* `Matrix.exp` of a `2×2`
skew matrix; either compute via the known closed form or via
`Matrix.exp_conj`/series. Mathlib has `Matrix.exp` and the rotation-matrix
identities may need a short lemma from `J² = -I`.
**E.1c (density-matrix Euler decomposition).**
`Ψ t ⬝ (Ψ t)ᵀ = !![cos²t, cos t·sin t; cos t·sin t, sin²t]`
`= ½•(1:Matrix) + ½•(!![1,0;0,-1]) ⬝ (cos(2t)•1 + sin(2t)•J')`. And the diagonal
part (`collapse`) is `!![cos²t,0;0,sin²t] = ½ + ½·cos(2t)•!![1,0;0,-1]`. *Proof.*
Direct `2×2` computation + double-angle (`Real.cos_sq`, `Real.cos_two_mul`,
`Real.sin_two_mul`). Purely computational — `by ext i j; fin_cases i <;> fin_cases j <;> simp [...]`. ∎
This is the sense in which collapse = "real part": zero the `J'`-component.

### E.2 — Classification of probability-preserving linear maps (2-state)
A linear `M : ℝ² → ℝ²` maps the probability simplex `Δ = {(p,q) | p,q≥0, p+q=1}`
into itself iff `M` is **column-stochastic**: both columns lie in `Δ`. The book's
`M(a,b) = !![cos²a, cos²b; sin²a, sin²b]` is exactly the general column-stochastic
`2×2` matrix (via E.1a each column is an arbitrary point of `Δ`).
**E.2a (stochastic ⇔ preserves simplex).** `M *ᵥ Δ ⊆ Δ ↔ (∀ j, 0 ≤ M · j ∧ ∑ᵢ Mᵢⱼ = 1)`.
*Proof.* (⇐) convex combination of columns stays in `Δ`. (⇒) apply `M` to the
vertices `![1,0]`, `![0,1]`, which must land in `Δ`. ∎
**E.2b (uniform→vertex forces singular).** If `M` is column-stochastic and
`M *ᵥ ![1/2,1/2] = ![1,0]`, then `det M = 0` (so `M` is **not** an invertible
symmetry). *Proof.* Second coordinate: `(M₂₁+M₂₂)/2 = 0` with `M₂₁,M₂₂ ≥ 0`
⇒ `M₂₁ = M₂₂ = 0`; column sums `= 1` ⇒ `M₁₁ = M₁₂ = 1`; so `M = !![1,1;0,0]`,
`det = 0`. ∎ Fully elementary; **do in Lean directly**. This is the book's point
that the wave-function (rotations, invertible) beats the probability simplex
(stochastic maps, can be singular) as a carrier of a symmetry group.

### E.3 — "Black hole": a unitary that uniformizes every basis state
**Statement.** For every `n`, there is a unitary `U : ℂⁿ → ℂⁿ` with
`|(U (e_i))_j|² = 1/n` for all `i,j` — i.e. `U` maps each computational basis
state to the uniform Born distribution. *Proof.* Take the **DFT** matrix
`U_{jk} = ω^{jk}/√n`, `ω = exp(2πi/n)`; `|U_{jk}|² = 1/n`. `U` is unitary by
character orthogonality. **Reuse:** Mathlib's DFT is `ZMod`-based
(`Analysis/Fourier/ZMod.lean`) — there is *no* `Matrix.dft`; either use the `ZMod n`
Fourier transform or build the `n×n` unitary + `|·|²=1/n` directly. For `n=2` this
is Hadamard `!![1,1;1,-1]/√2` (by hand). ∎ This makes precise the book's
"there is always a unitary such that the distribution is constant for all initial
basis states," used for the information-erasure/black-hole remark. Formalizable;
the black-hole physics discussion itself is prose (not formalized).

### E.4 — Generic phase space: hyperspherical Born recursion onto the simplex
**Statement (the general parametrization theorem).** For a countable state space
(`Fin N` or `ℕ`), every probability distribution `P` on it is realized by the Born
rule of a **real** unit vector `v₁` built from angles `θ₁,θ₂,…` by the recursion
`vₙ = cos θₙ · lₙ + sin θₙ · vₙ₊₁` (`{lₙ}` an orthonormal basis), with
```
P(n) = |⟪v₁, lₙ⟫|² = (∏_{k=1}^{n-1} sin²θ_k) · cos²θ_n     (last term: no cos for ℕ tail).
```
Equivalently, the "stick-breaking" map `Θ : (angles) → simplex`,
`Θ(θ)ₙ = (∏_{k<n} sin²θ_k) cos²θ_n`, is **surjective** onto the probability simplex
`Δ_N = {P | P ≥ 0, ∑ P = 1}` (finite `N`) and onto the `ℓ¹` simplex on `ℕ`.
**Proof (Lean-ready).**
- *Well-defined / sums to 1.* By induction, `∑_{n≤N} P(n) + ∏_{k≤N} sin²θ_k = 1`
  (telescoping `cos²θ + sin²θ = 1`). For `Fin N` terminate with `c_N = 1`
  (`θ_N` chosen so the last factor is `1`), giving `∑ = 1`; for `ℕ` the tail
  product `∏ sin²θ_k → 0` gives `∑_{n} P(n) = 1` (a convergent series).
- *Surjectivity (stick-breaking).* Given target `P ∈ Δ`, define the conditional
  `cos²θ_n := P(n) / P(n or above)` where `P(n or above) := ∑_{k≥n} P(k)`
  (set `θ_n` arbitrary if the tail is `0`). Then `sin²θ_n = P(n+1 or above)/P(n or above)`,
  and `∏_{k<n} sin²θ_k = P(n or above)` telescopes, so `Θ(θ)_n = P(n)`. This is
  exactly the book's `P(n) = (∏_{k<n} P(k+1↑|k↑)) · P(n|n↑)` chain-rule identity. ∎
**Lean hooks.** `Finset.prod`, induction, `Real.sin_sq_add_cos_sq`, and for the `ℕ`
case `tsum`/`HasSum` + `Filter.Tendsto` of the tail product to `0`. The density-
matrix / projection statements (`vₙvₙ† = ½ + ½(lₙlₙ† − vₙ₊₁vₙ₊₁†)(cos2θ + Jₙ sin2θ)`,
`Jₙ = lₙvₙ₊₁† − vₙ₊₁lₙ†`, `Jₙ² = −1` on the 2-plane `span{lₙ,vₙ₊₁}`) generalize
E.1c and are optional decoration; the **surjectivity onto the simplex is the
theorem**. This is the finite/countable, real-Hilbert shadow of Chapter B.1–B.2.

### E.5 — Real/complex/quaternionic wave-functions (cross-reference)
The closing subsection (line 3651) invokes the **real Schur lemma trichotomy**:
the commutant of {projections ∪ unitary group rep} with no invariant subspace is a
real division algebra `≅ ℝ, ℂ, or ℍ`, giving real/complex/quaternionic
wave-functions. This is **exactly Chapter A §A.2 Props 17–19** — do not re-prove;
in Lean, `import` the A.2 results and instantiate. The quaternionic recursion
`vₙvₙ† = cₙ²lₙlₙ† + sₙ²vₙ₊₁vₙ₊₁† + cₙsₙ(lₙvₙ₊₁† + vₙ₊₁lₙ†)` is E.4 over `ℍ`.

---

# Chapter G — Gauge transformations in probability spaces (book line 2128) — **PROMOTED, work package N6**

**Status change (author's instruction, 2026-07-02).** This chapter was
previously triaged non-formalizable; that triage is **superseded**. The
definitions of gauge transformation / gauge group / gauge-invariant algebra /
gauge-fixing and their properties **are formalizable and important** — they are
the mathematical backbone that the Yang–Mills, Gribov, parity and gravity
chapters (Ch. P) all lean on. Formalize the whole package below into
`BookProof/ChapterG.lean` (split a `ChapterG/Koopman.lean` if the file grows
past ~600 lines). **None of G.0–G.7 needs an `EXTERNAL` hypothesis.** Book
sources: §"Gauge transformations, constrained systems and conditioned
probability" (line 2223, the core), §"Wave-function parametrization of
dissipative dynamics" (2184), §"Quantization of a classical Gauge Mechanics
system" (2403).

Throughout, `X Y : Type*` are sample/parameter spaces; add `[MeasurableSpace _]`
only where a measure appears. Keep every statement generic first (as Ch. B did);
the §0 substrate instantiation is N5's job.

### G.0 — Def (parametrization and its gauge group)

**Book (2240–2251).** A *parametrization* is a surjection `π : X → Y` from
parameter space onto the parametrized space; the *gauge group* is the group of
transformations of `X` that do not modify the corresponding point of `Y`.

**Lean.**
```lean
/-- The gauge group of a parametrization `π : X → Y`: permutations of the
parameter space that preserve every fiber of `π` (book line 2247). -/
def gaugeGroup (π : X → Y) : Subgroup (Equiv.Perm X) where
  carrier := {g | ∀ x, π (g x) = π x}
  one_mem' := fun x => rfl
  mul_mem' := ...   -- π (g (h x)) = π (h x) = π x
  inv_mem' := ...   -- apply the hypothesis at `g⁻¹ x`: π (g (g⁻¹ x)) = π (g⁻¹ x)
```
**Proof detail for `inv_mem'`** (the only non-rfl step): given
`hg : ∀ x, π (g x) = π x` and a point `x`, rewrite
`π (g⁻¹ x) = π (g (g⁻¹ x))` (by `hg (g⁻¹ x)` read right-to-left) `= π x`
(by `Equiv.apply_symm_apply`). ~25 lines total.

### G.1 — Props (orbits = fibers; invariance ⇔ factoring through `π`)

The book's claim *"as a matter of principle, for all parametrizations we can
define a gauge group … thus all parametrizations are solutions to constraint
equations requiring gauge invariance"* (2247–2251, cite `norton_2003`) is two
precise lemmas:

**(a) Transpositions are gauge transformations, hence orbit = fiber.**
```lean
theorem swap_mem_gaugeGroup {x x' : X} (h : π x = π x') :
    Equiv.swap x x' ∈ gaugeGroup π

theorem gaugeOrbit_eq_fiber (x : X) :
    MulAction.orbit (gaugeGroup π) x = π ⁻¹' {π x}
```
*Proof (a1).* For any `z`, `Equiv.swap x x' z` is `x'`, `x`, or `z` by cases
(`Equiv.swap_apply_left`, `swap_apply_right`, `swap_apply_of_ne_of_ne` — pinned);
in each case `π` of it equals `π z` using `h`. *Proof (a2).* `⊆`: an orbit
element is `g x` with `g ∈ gaugeGroup π`, and `π (g x) = π x` by definition.
`⊇`: if `π x' = π x`, then `x' = (Equiv.swap x x') x ∈ orbit` by (a1). The
`MulAction` instance on `X` is the standard `Equiv.Perm` action restricted to
the subgroup (`Subgroup.instMulAction` / `Submonoid.smul` — it is already
there; write `g • x` and unfold with `Equiv.Perm.smul_def`). ~40 lines.

**(b) Gauge-invariant functions are exactly the functions of the parametrized
point.**
```lean
theorem gaugeInvariant_iff_factors (hπ : Function.Surjective π) (f : X → Z) :
    (∀ g ∈ gaugeGroup π, ∀ x, f (g x) = f x) ↔ ∃ h : Y → Z, f = h ∘ π
```
*Proof.* (⇐) immediate: `f (g x) = h (π (g x)) = h (π x) = f x`.
(⇒) First show `f` is constant on fibers: if `π x = π x'` then by invariance
applied to `Equiv.swap x x'` (in the group by (a)) at the point `x`:
`f x' = f (swap x x' x) = f x` (`Equiv.swap_apply_left`). Now set
`h := f ∘ Function.surjInv hπ`; for any `x`,
`h (π x) = f (surjInv hπ (π x))`, and `π (surjInv hπ (π x)) = π x` by
`Function.surjInv_eq`, so constancy-on-fibers gives `= f x`. ~35 lines.
This is the chapter's Def-level headline: *every parametrization is the
solution of the constraint "be gauge-invariant"*.

### G.2 — Gauge-invariant subalgebras; gauge-independence of expectation values

**(a) Function version (the commutative algebra).**
```lean
/-- Gauge-invariant observables form a subalgebra of `X → R`
(book 2277–2289: "translation-invariant subalgebra of the commutative
von Neumann algebra"). -/
def gaugeInvariantSubalgebra (R) [CommSemiring R] (π : X → Y) :
    Subalgebra R (X → R) where
  carrier := {f | ∀ g ∈ gaugeGroup π, ∀ x, f (g x) = f x}
  ...
```
All five closure fields are one-line pointwise computations (`add_mem'`:
`(f+f') (g x) = f (g x) + f' (g x) = f x + f' x`, etc.; `algebraMap_mem'`:
constants are invariant). By G.1(b) this subalgebra is *isomorphic to
`Y → R`* when you want the stronger statement — optional
`gaugeInvariantSubalgebra_equiv` via `h ↦ h ∘ π`. ~40 lines (+~30 optional).

**(b) Operator version — zero new definitions.** The gauge-invariant *operator*
algebra of a family of gauge unitaries `U : G → (V →L[𝔽] V)` is
`Subalgebra.centralizer 𝔽 (Set.range U)` — **pinned Mathlib, nothing to
build**; add a `abbrev gaugeInvariantOperators` + docstring tying it to the
book's "sub-algebra … which commutes with the gauge generator" (2444).

**(c) Expectation values are gauge-independent on equivalence classes**
(book 2344–2347: *"the expectation value of any operator of the commutative
algebra which commutes with the gauge generators is the same at each
equivalence class"*):
```lean
theorem expectation_gauge_invariant {V : Type*} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [CompleteSpace V]
    (U : V →L[ℂ] V) (hU : U ∈ unitary (V →L[ℂ] V))
    (A : V →L[ℂ] V) (hA : A * U = U * A) (Ψ : V) :
    ⟪U Ψ, A (U Ψ)⟫_ℂ = ⟪Ψ, A Ψ⟫_ℂ
```
*Proof.* `⟪UΨ, A(UΨ)⟫ = ⟪UΨ, U(AΨ)⟫` (rewrite `A (U Ψ) = U (A Ψ)` from `hA`
applied to `Ψ`, note `(A * U) Ψ = A (U Ψ)` is `ContinuousLinearMap.mul_apply`);
then `⟪UΨ, U(AΨ)⟫ = ⟪(U† * U)Ψ, AΨ⟫ = ⟪Ψ, AΨ⟫` by
`ContinuousLinearMap.adjoint_inner_left` and `unitary.star_mul_self` (star on
`V →L[ℂ] V` *is* `adjoint`). ~20 lines. This lemma is the whole reason
gauge-fixing is allowed to be incomplete (book 2338–2347).

### G.3 — The Dirac obstruction: no gauge-invariant normalized state

**Book (2277–2289).** The translation gauge symmetry `e_k → e_{k+1}` on a
discrete basis indexed by `ℤ` admits **no** invariant probability measure and
**no** invariant unit wave-function — while the invariant *subalgebra* is
nontrivial. Both halves are cleanly formalizable and make the "it is the
algebra, not the Hilbert space, that is gauge-invariant" thesis a theorem.

**(a) No shift-invariant probability measure on `ℤ`.**
```lean
theorem no_shift_invariant_probabilityMeasure :
    ¬ ∃ μ : Measure ℤ, IsProbabilityMeasure μ ∧
      ∀ s : Set ℤ, μ ((· + 1) ⁻¹' s) = μ s
```
*Proof.* Invariance at singletons gives `μ {k - 1} = μ {k}` (the preimage of
`{k}` under `(· + 1)` is `{k - 1}`), so by two-sided induction
`μ {k} = μ {0} =: c` for all `k`. `ℤ` is countable with
`MeasurableSingletonClass`, and `Set.univ = ⋃ k, {k}` pairwise-disjointly, so
`1 = μ univ = ∑' k : ℤ, c` (`measure_iUnion`). `ENNReal.tsum_const` (or
`tsum_const` + `ENNReal` arithmetic) evaluates the sum to `0` if `c = 0` and
`∞` if `c ≠ 0` (infinite index type) — both contradict `= 1`. ~50 lines;
the only care point is doing the induction with `Int.induction_on`.

**(b) No shift-invariant unit vector in `ℓ²(ℤ)`.**
```lean
theorem shift_invariant_l2_eq_zero (Ψ : lp (fun _ : ℤ => ℂ) 2)
    (hΨ : ∀ k, Ψ (k + 1) = Ψ k) : Ψ = 0

theorem no_shift_invariant_unit_vector :
    ¬ ∃ Ψ : lp (fun _ : ℤ => ℂ) 2, ‖Ψ‖ = 1 ∧ ∀ k, Ψ (k + 1) = Ψ k
```
*Proof.* `hΨ` + `Int.induction_on` ⇒ `Ψ k = Ψ 0` for all `k`. Membership in
`lp _ 2` gives `Summable (fun k => ‖Ψ k‖ ^ 2)` (`lp.memℓp` + `memℓp_gen_iff`).
A summable function tends to `0` along `cofinite`
(`Summable.tendsto_cofinite_zero`); a constant function tends to its value; so
`‖Ψ 0‖ ^ 2 = 0`, i.e. `Ψ = 0` by `lp.ext` + the constancy. The corollary is
immediate (`‖0‖ = 0 ≠ 1`). ~45 lines.

**(c) Contrast remark (one-liner).** `1 ∈ gaugeInvariantSubalgebra` /
the constants: the invariant algebra is nonempty-nontrivial even though the
invariant state set is empty. State it as a `theorem` so the thesis is checked
by Lean, not prose.

### G.4 — Gauge-fixing: complete / unconstrained; sections always exist

**Book (2291–2304).** Gauge-fixing = representing each gauge equivalence class
by (at least) one point; *complete* = at most one crossing per class;
Dirac brackets need complete **and** unconstrained, which Gribov obstructs.

**Lean.**
```lean
/-- A gauge-fixing slice for `π`: a set of parameter points. It is *complete*
if it crosses each gauge orbit (= fiber, by `gaugeOrbit_eq_fiber`) at most
once (book 2294–2296). -/
def IsCompleteGaugeFixing (π : X → Y) (S : Set X) : Prop :=
  ∀ ⦃x x'⦄, x ∈ S → x' ∈ S → π x = π x' → x = x'

/-- Every parametrization admits a total complete gauge-fixing (a section);
constructively this is choice — `Function.surjInv`. -/
theorem exists_complete_gaugeFixing (hπ : Function.Surjective π) :
    ∃ S : Set X, IsCompleteGaugeFixing π S ∧ π '' S = Set.univ
```
*Proof.* Take `S := Set.range (Function.surjInv hπ)`. Completeness: if
`surjInv hπ y = x`, `surjInv hπ y' = x'` and `π x = π x'`, then
`y = π (surjInv hπ y) = π x = π x' = y'` (`Function.surjInv_eq`), so `x = x'`.
Totality: `π (surjInv hπ y) = y` gives `π '' S = univ`. ~30 lines.

**Measurable gauge-fixing = disintegration (cross-reference, no new proof).**
The book's opening move — *"in standard measure spaces it is always possible to
define regular conditional probabilities, then in principle it is always
possible to implement exact constraints … without null measure"* (2226–2230) —
is **exactly `MeasureTheory.Measure.condKernel`** (pinned in the reuse table),
i.e. work-package **N3 (B.2′) is also the load-bearing measure-theoretic lemma
of this chapter**; say so in the docstring and do N3 in the same pass.
"Unconstrained" gauge-fixing and the Gribov ambiguity (2301–2314) are
operator-algebraic/prose — leave as docstring commentary, no Lean obligation.

### G.5 — Haar averaging (invariantization) and the pushforward headline

**Book (2350–2392).** For a compact (finite-dimensional, per the book's
declared scope) gauge group: the Haar measure *"always exists which allows to
create a functional which is gauge invariant"*, and the *goal* of the chapter:
*"the pushforward measure … implements the exact constraints in a separable
probability space without attributing to the constrained space null probability
measure."*

Setup: `G` a compact topological group, `[MeasurableSpace G]`, Borel; Haar
probability `μG`. Mathlib route (pinned in the reuse table): `haarMeasure ⊤`
using the `Top (PositiveCompacts G)` instance; `IsProbabilityMeasure` follows
in one line from `haarMeasure_self`. `G` acts on `X` (`[MulAction G X]`,
measurable action).

**(a) The averaging operator and its four properties.**
```lean
noncomputable def haarAverage (f : X → ℝ) (x : X) : ℝ := ∫ g, f (g⁻¹ • x) ∂μG

theorem haarAverage_smul (hf : ...) (g₀ : G) (x : X) :
    haarAverage f (g₀ • x) = haarAverage f x                  -- invariance
theorem haarAverage_of_invariant (hf : ∀ g x, f (g • x) = f x) :
    haarAverage f = f                                          -- projection
theorem haarAverage_one : haarAverage (fun _ => 1) = fun _ => 1 -- unital
theorem haarAverage_nonneg (hf : 0 ≤ f) : 0 ≤ haarAverage f    -- positive
```
*Proofs.* Invariance: `haarAverage f (g₀ • x) = ∫ g, f ((g₀⁻¹ * g)⁻¹ • x) ∂μG`
(rewrite `g⁻¹ • g₀ • x = (g₀⁻¹ * g)⁻¹ • x` by `smul_smul` + `mul_inv_rev`),
then substitute `g ↦ g₀ * g` by **`integral_mul_left_eq_self`** (pinned) to
recover `∫ g, f (g⁻¹ • x)`. Projection: the integrand is constantly `f x`
(`f (g⁻¹ • x) = f x` by `hf`), and `∫ const = const` for a probability measure
(`integral_const`, `measure_univ`). Unital = projection at `f = 1`; positivity
= `integral_nonneg`. Carry integrability as an explicit hypothesis
`(hf : Integrable (fun g => f (g⁻¹ • x)) μG)` where needed (continuous `f` on
compact `G` discharges it via `Continuous.integrable_of_hasCompactSupport` /
`isCompact_univ`; provide that as a convenience lemma). ~120 lines. This makes
the book's "gauge-invariant functional always exists" a theorem: for **any**
integrable `f`, `haarAverage f` is an invariant functional agreeing with `f`
on invariants.

**(b) THE HEADLINE — pushforward implements exact constraints without null
measure** (book 2374–2386, "which is our goal"):
```lean
theorem gauge_constraint_pushforward_full_measure
    {X : Type*} [MeasurableSpace X] (μ : Measure X) [IsProbabilityMeasure μ]
    (q : X → X) (hq : Measurable q)          -- the projection onto the
    (C : Set X) (hC : MeasurableSet C)       -- constrained spectrum
    (hrange : ∀ x, q x ∈ C) :
    IsProbabilityMeasure (μ.map q) ∧ (μ.map q) C = 1
```
*Proof.* First conjunct: pinned `Measure.isProbabilityMeasure_map`
(`hq.aemeasurable`). Second: `Measure.map_apply hq hC`, and
`q ⁻¹' C = Set.univ` by `hrange`, so `= μ univ = 1`. ~15 lines — deliberately
easy, because the mathematical content is the *statement*: the constrained set
`C` carries measure **1**, not 0, under the pushforward; contrast docstring
with the naive "constraint surface has null measure" failure (2219–2220,
2485–2488). Add the composite corollary `haarAverage`-projection + pushforward
for a `G`-equivariant `q` if time permits (optional, ~40 lines).

### G.6 — BRST ghost algebra of the gauge-mechanics example (nilpotency)

**Book (2403–2452).** The Hilbert space is `L²(ℝ² × ℤ₂)`; the `ℤ₂` (ghost)
factor makes all the new algebra **finite-dimensional**, so this formalizes
completely without unbounded operators: `L²(ℝ²×ℤ₂) ≅ L²(ℝ²) ⊕ L²(ℝ²)`, i.e.
operators are `2×2` matrices over the operator algebra `A` of the continuous
factor. Keep `A` abstract (`[Ring A]`): the CCR pair `(φ, π)` is unbounded and
stays out of scope (docstring note); everything asserted below is exact.

```lean
def ghostAnnih : Matrix (Fin 2) (Fin 2) A := !![0, 1; 0, 0]  -- ψ   (book: ψ{Ψ}(·,k)=Ψ(·,0)δ_{k1})
def ghostCreat : Matrix (Fin 2) (Fin 2) A := !![0, 0; 1, 0]  -- ψ†  (book: ψ†{Ψ}(·,k)=Ψ(·,1)δ_{k0})

theorem ghost_car    : ghostAnnih * ghostCreat + ghostCreat * ghostAnnih = 1  -- {ψ,ψ†}=1
theorem ghost_annih_sq : ghostAnnih * ghostAnnih = (0 : Matrix _ _ A)
theorem ghost_creat_sq : ghostCreat * ghostCreat = (0 : Matrix _ _ A)
theorem ghost_creat_conjTranspose :                    -- over ℂ: ψ† is the adjoint of ψ
    (ghostAnnih (A := ℂ))ᴴ = ghostCreat

/-- BRST charge Ω = Q·ψ† for a gauge generator Q : A (book: Ω=(πφ+π*φ*)ψ†). -/
def BRST (Q : A) : Matrix (Fin 2) (Fin 2) A := !![0, 0; Q, 0]

theorem BRST_nilpotent (Q : A) : BRST Q * BRST Q = 0          -- Ω² = 0
theorem BRST_eq_smul (Q : A) (hQ : Commute ...) : ...          -- optional: Ω = Q•ψ† form
```
*Proofs.* All by `ext i j; fin_cases i <;> fin_cases j <;>
simp [Matrix.mul_apply, Fin.sum_univ_two, ghostAnnih, ghostCreat]` (or
`Matrix.mul_fin_two`). `BRST_nilpotent` is the same computation — the entry
`(1,0)` of the square is `Q·0 + 0·Q = 0`. ~80 lines including docstrings.
The docstrings must carry the book's physics reading: nilpotency of the BRST
charge is what makes the ghost construction consistent, and it holds **for
every** gauge generator `Q` — no constraint-solving needed, which is the
chapter's point. Optional garnish: `ghostNumber := ψ†ψ = !![0,0;0,1]` commutes
with every diagonal matrix but `ghostAnnih` does not (the "gauge generator is
excluded from the commutative algebra" remark, 2444–2452) — two 5-line lemmas.

### G.7 — Dissipative dynamics: Koopman evolution (book §2184)

**Book.** Dissipative classical systems (the two damped coupled oscillators,
eq. at 2199) have no conserved energy / no classical Hamiltonian, *"but the
pendulums do not disappear and thus the probability is conserved"* — the
quantum (Koopman) formalism applies whenever probability is conserved.

**(a) Koopman unitary from a measure-preserving equivalence.** Mathlib pins
the isometry (`Lp.compMeasurePreservingₗᵢ`, reuse table) but **not** the
unitary equiv (grep: absent). Build it:
```lean
noncomputable def koopmanEquiv (f : α ≃ᵐ β) (hf : MeasurePreserving f μ ν)
    [Fact (1 ≤ p)] : Lp E p ν ≃ₗᵢ[ℝ] Lp E p μ
```
from the two isometries `compMeasurePreservingₗᵢ f hf` and
`compMeasurePreservingₗᵢ f.symm hf.symm` — the two composition identities
(`left_inv`/`right_inv`) follow by `Lp.ext` + `compMeasurePreserving_comp`-style
simp lemmas (prove the two `∀ u, comp (comp u f) f.symm = u` identities a.e.:
`(u ∘ f) ∘ f.symm =ᵐ u` since `f (f.symm x) = x` everywhere). Note
`MeasurePreserving.symm` exists for `MeasurableEquiv` (grep
`MeasurePreserving.symm` — it is in
`Mathlib/Dynamics/Ergodic/MeasurePreserving.lean`). ~70 lines. This is the
chapter's "probability conserved ⇒ unitary wave-function evolution", and it is
**also the N7(a) deliverable** for book-Ch.-B §7/§9 — write it once here.

**(b) The damped-coupled-oscillator flow is a one-parameter group.** First-order
form: state `v = (x₁, ẋ₁, x₂, ẋ₂) : Fin 4 → ℝ`, system matrix
```lean
def dampedCoupledMatrix (l₁ l₂ w₁ w₂ c₁ c₂ : ℝ) : Matrix (Fin 4) (Fin 4) ℝ :=
  !![0, 1, 0, 0;  -w₁^2, -l₁, c₂, 0;  0, 0, 0, 1;  c₁, 0, -w₂^2, -l₂]

theorem dampedFlow_add (M : Matrix (Fin 4) (Fin 4) ℝ) (s t : ℝ) :
    Matrix.exp ℝ ((s + t) • M) = Matrix.exp ℝ (s • M) * Matrix.exp ℝ (t • M)
```
*Proof.* `(s • M)` and `(t • M)` commute (`Commute.smul_left/right` of
`Commute.refl M`), then `Matrix.exp_add_of_commute` (pinned via Ch. E.1b —
`Analysis/Normed/Algebra/MatrixExponential.lean`; reuse the `exp_J` technique
from `ChapterE.lean`). Add `dampedFlow_zero : exp(0•M) = 1` (`Matrix.exp_zero`).
~30 lines. Docstring: this is the book's eq.-2199 system in companion form —
a dynamics with **no** Lagrangian/classical-Hamiltonian description still has a
globally defined flow group, which is all Koopman needs.

**(c) Probability is conserved (the honest formal shadow of "the pendulums do
not disappear").** For any measurable evolution map `T : X → X` and probability
`μ`, `μ.map T` is a probability measure — instance
`Measure.isProbabilityMeasure_map` (pinned); state it once as a named corollary
`evolution_conserves_probability` with the book quote in the docstring, ~8
lines. (Do **not** claim Koopman unitarity for the dissipative flow w.r.t.
Lebesgue measure — the flow contracts phase-space volume; unitarity in (a) is
w.r.t. the *conserved/evolved* probability measure. Docstring must make this
distinction — it is exactly the book's point.)

**Chapter G deliverable checklist (definition of done for N6):** `gaugeGroup`,
`swap_mem_gaugeGroup`, `gaugeOrbit_eq_fiber`, `gaugeInvariant_iff_factors`,
`gaugeInvariantSubalgebra`, `gaugeInvariantOperators` (abbrev),
`expectation_gauge_invariant`, `no_shift_invariant_probabilityMeasure`,
`shift_invariant_l2_eq_zero` + `no_shift_invariant_unit_vector`,
`IsCompleteGaugeFixing` + `exists_complete_gaugeFixing`, `haarAverage` + its
four lemmas, `gauge_constraint_pushforward_full_measure`, `ghostAnnih`/
`ghostCreat` + `ghost_car`/`ghost_annih_sq`/`ghost_creat_sq`/
`ghost_creat_conjTranspose`, `BRST` + `BRST_nilpotent`, `koopmanEquiv`,
`dampedCoupledMatrix` + `dampedFlow_add`/`dampedFlow_zero`,
`evolution_conserves_probability`. All `sorry`-free, no `axiom`, no `EXTERNAL`.

---

# Chapter G II — Gribov ambiguity, BRST cohomology, deeper constraint implementation — **work package N9** (NEW 2026-07-03, author: "the gauge transformations definition and properties is very important")

G.0–G.7 are DONE (`BookProof/ChapterG.lean`). This package mines the **rest**
of the gauge chapter (book 2223–2455) plus the gauge-fixing core of the
"Timepiece and the Gribov ambiguity" chapter (book 7125): the parts of the
gauge story that G.0–G.7 did not touch. Target file
**`BookProof/ChapterG2.lean`** (import `BookProof.ChapterG` — build on its
`gaugeGroup`/`IsCompleteGaugeFixing`/`haarAverage`/BRST definitions, never
re-derive). Everything below is self-contained mathematics with pinned Mathlib
names; **no `EXTERNAL` hypothesis anywhere in this package**.

### G.8 — Conditioning fails on null constraint sets (the chapter's motivating claim)

**Book (2230–2245).** *"…it is always possible to implement exact constraints
in a separable probability space without attributing to the constrained space
null probability measure"* — because plain conditioning is **impossible** when
the constraint set is null. G.5's headline
(`gauge_constraint_pushforward_full_measure`) is the positive half; this is
the negative half that motivates it.

**Statements.**
```lean
theorem cond_of_null (μ : Measure Ω) (hC : μ C = 0) : μ[|C] = 0
theorem not_isProbabilityMeasure_cond_null (μ : Measure Ω) (hC : μ C = 0) :
    ¬ IsProbabilityMeasure μ[|C]
```
**Proof.** `ProbabilityTheory.cond` is definitionally
`(μ C)⁻¹ • μ.restrict C` (`Probability/ConditionalProbability.lean:74`);
`Measure.restrict_eq_zero` (`MeasureTheory/Measure/Restrict.lean:211`) gives
`μ.restrict C = 0` from `hC`, and `smul_zero` finishes. The second statement:
`(0 : Measure Ω) Set.univ = 0 ≠ 1`. ~15 lines. Add the contrast docstring:
for a gauge constraint the pushforward construction of G.5 yields measure 1
on the same set where conditioning yields the zero measure. Optionally add the
positive-mass converse `cond_isProbabilityMeasure`
(`ConditionalProbability.lean:162`, already in Mathlib — cite, don't re-prove).

### G.9 — The Dirac obstruction in general form (any infinite gauge group)

**Book (2270–2292 + Dirac 1955 quote).** G.3 proved "no shift-invariant
probability measure / unit vector" **for ℤ**. Generalize to any countably
infinite group — the honest formal form of *"there are some symmetries of the
commutative von Neumann algebra which the probability measure cannot have"*.

**Statements** (`G` a group, `[Countable G]`, `[Infinite G]`, measurable space
`⊤` on `G`):
```lean
theorem no_translation_invariant_probabilityMeasure :
    ¬ ∃ μ : Measure G, IsProbabilityMeasure μ ∧ ∀ g x, μ {g * x} = μ {x}
theorem translation_invariant_l2_eq_zero (Ψ : lp (fun _ : G => ℂ) 2)
    (hΨ : ∀ g, ∀ x, Ψ (g * x) = Ψ x) : Ψ = 0
theorem no_translation_invariant_unit_vector : …
```
**Proof.** Copy the ℤ proofs from `ChapterG.lean`
(`no_shift_invariant_probabilityMeasure` :143,
`shift_invariant_l2_eq_zero` :170) — they use only: invariance ⇒ all
singletons have equal mass (transitivity of the left action of `G` on itself:
`{g} = (g * ·) '' {1}`), countable additivity over `⋃_{g} {g} = univ`
(`measure_iUnion` on the countable type), and "constant summable family on an
infinite index type is zero". The generalization is a rename plus replacing
`n + 1`-induction by the group translation; ~60 lines. Keep the ℤ versions in
`ChapterG.lean` untouched; state these as the general form and (optional
1-liner) re-derive the ℤ case as `example` from the general one.

### G.10 — HEADLINE: the Gribov ambiguity — no *continuous* complete gauge fixing

**Book (2294–2340 + 7125–7180).** Complete gauge fixings always exist
set-theoretically (G.4 `exists_complete_gaugeFixing`, by choice) — but the
Dirac-bracket picture needs them *regular* (continuous/measurable-structure-
compatible), and *"which is not possible in general due to the Gribov
ambiguity"*. Formalize the minimal honest instance: the circle parametrized by
the real line, gauge group = `2πℤ` translations (fibers of `Circle.exp` = gauge
orbits, exactly G.0's `gaugeGroup (Circle.exp)` picture).

**Statement.**
```lean
theorem no_continuous_gauge_fixing_circle :
    ¬ ∃ s : Circle → ℝ, Continuous s ∧ ∀ z, Circle.exp (s z) = z
```
**Proof (fully elementary, IVT route).** Suppose `s` exists. Consider
`F : ℝ → ℝ, F t := s (Circle.exp t) - t`. It is continuous (`Circle.exp` is
continuous; composition). Every value of `F` is an integer multiple of `2π`:
from `Circle.exp (s (Circle.exp t)) = Circle.exp t` and
`Circle.exp_eq_exp` (`Analysis/SpecialFunctions/Complex/Circle.lean:68`:
`exp x = exp y ↔ ∃ m : ℤ, x = y + m * (2π)`). A continuous function on `[0, 2π]`
with values in `(2π)ℤ` is constant: if `F t₁ ≠ F t₂` they differ by ≥ `2π`, and
`intermediate_value_Icc` produces a value strictly between two consecutive
multiples — contradiction (alternatively: `t ↦ F t / (2π)` is continuous and
integer-valued, use `IsPreconnected.constant`
(`Topology/Connected/TotallyDisconnected.lean:297`) /
`PreconnectedSpace.constant` (:305) after factoring through `ℤ`-valued — the
IVT route avoids needing discreteness of the range). So `F 0 = F (2π)`, i.e.
`s (Circle.exp 0) - 0 = s (Circle.exp (2π)) - 2π`. But
`Circle.exp_two_pi` (:76) and `exp_zero` give `Circle.exp 0 = Circle.exp (2π)`,
hence `0 = -2π` — contradiction with `Real.pi_pos`. ~80 lines.

**Corollaries (short).**
```lean
theorem gauge_fixing_section_discontinuous
    (s : Circle → ℝ) (hs : ∀ z, Circle.exp (s z) = z) : ¬ Continuous s
```
and the pairing docstring: by G.4, complete gauge fixings of this
parametrization **exist** (choice) — the Gribov ambiguity is precisely the gap
between set-theoretic existence and continuous existence. This is the formal
content of *"the Dirac brackets require the gauge-fixing to be both
unconstrained and complete… which is not possible in general"*.

### G.11 — BRST cohomology of the gauge-mechanics model: physical states = gauge-invariant states

**Book (2403–2455).** The ghost sector is 2-dimensional (`k ∈ ℤ₂`), the BRST
charge is `Ω = Q ψ†` with gauge generator `Q`; G.6 proved `Ω² = 0`. Compute the
**cohomology** and identify the physical (ghost-number-0) sector with the
gauge-invariant states — the chapter's actual punchline ("the wave-function
needs not be gauge-invariant, just the observables").

**Setting.** Work over a commutative ring `A` (the abstract role of the
`Q`-diagonalized function algebra); states of the 2×2 model are `Fin 2 → A`,
`Ω` acts by `(BRST Q).mulVec` (reuse `BRST` from `ChapterG.lean`).

**Deliverables.**
```lean
def brstKer (Q : A) : Submodule A (Fin 2 → A)   -- kernel of mulVec (BRST Q)
def brstIm  (Q : A) : Submodule A (Fin 2 → A)   -- range  of mulVec (BRST Q)
theorem brstIm_le_brstKer (Q : A) : brstIm Q ≤ brstKer Q          -- from Ω²=0
def brstCohomology (Q : A) := brstKer Q ⧸ (brstIm Q).comap (brstKer Q).subtype
theorem mem_brstKer_iff (v) : v ∈ brstKer Q ↔ Q * v 0 = 0
theorem mem_brstIm_iff  (v) : v ∈ brstIm Q ↔ v 0 = 0 ∧ ∃ a, v 1 = Q * a
noncomputable def brstCohomology_equiv :
    brstCohomology Q ≃ₗ[A] LinearMap.ker (LinearMap.mulLeft A Q) × (A ⧸ Ideal.span {Q})
```
**Proof recipe.** `(BRST Q).mulVec v = ![0, Q * v 0]` by
`Matrix.mulVec`-unfolding (`Fin.sum_univ_two`, exactly the `fin_cases` style
already used in G.6). Hence the two `iff`s are direct. The equivalence: send
`[v] ↦ (v 0, Ideal.Quotient.mk _ (v 1))` — well-defined because shifting by
`brstIm` changes `v 1` by a multiple of `Q` and leaves `v 0` fixed; inverse by
choosing representatives (`Submodule.liftQ` + `Ideal.Quotient.lift`;
surjectivity/injectivity by computation). ~150 lines, pure module algebra.

**Headline corollary (ghost-number-0 sector).**
```lean
theorem brst_physical_iff_gauge_invariant (a : A) :
    (![a, 0] ∈ brstKer Q) ↔ Q * a = 0
```
with the docstring: a ghost-free state is BRST-closed **iff** it is annihilated
by the gauge generator — "physical states are the gauge-invariant ones", while
generic states need not be (Dirac's standard-ket remark, G.9). ~10 lines.
**Per §0 S7**, the G.11 docstrings must cite the implemented counterpart: the
BRST projection of the `fock_sirk` crate in `../unfer` (physics Hamiltonians
are required to commute with `Ω`; gauge invariance is verified as commutation
with the BRST charge — this Lean layer is its mathematical content).
Optional: over `[StarRing A]` add `BRST_adjoint : (BRST Q)ᴴ = !![0, star Q; 0, 0]`
and the BRST Laplacian `ΩΩᴴ + ΩᴴΩ = !![star Q * Q, 0; 0, Q * star Q]`
(`fin_cases` computation, ~25 lines) — the "Casimir in both ghost sectors".

### G.12 — Haar averaging is the invariant projection and preserves invariant expectations

**Book (2350–2392, completing G.5).** G.5 proved `haarAverage` is invariant-on-
invariants, unital, positive. Missing: (a) the average is **itself
gauge-invariant**, (b) averaging is **idempotent** (a projection), (c) averaging
**preserves expectations** under an invariant measure — *"the expectation value
of any operator of the commutative algebra which commutes with the gauge
generators is the same at each equivalence class"*.

**Statements** (same setting as G.5: compact group `G`, Haar probability `μG`,
measurable action on `X`):
```lean
theorem haarAverage_invariant (f : X → ℝ) (g : G) (x : X) :
    haarAverage (μG := μG) f (g • x) = haarAverage (μG := μG) f x
theorem haarAverage_idempotent (f : X → ℝ) :
    haarAverage (μG := μG) (haarAverage (μG := μG) f) = haarAverage (μG := μG) f
theorem integral_haarAverage (μ : Measure X) [IsProbabilityMeasure μ]
    (hμ : ∀ g : G, μ.map (g • ·) = μ) (f : X → ℝ) (hf : Integrable f μ) … :
    ∫ x, haarAverage (μG := μG) f x ∂μ = ∫ x, f x ∂μ
```
**Proofs.** (a) `∫ h, f (h⁻¹ • g • x) ∂μG = ∫ h, f ((g⁻¹h)⁻¹ • x) ∂μG` and
left-invariance `integral_mul_left_eq_self`
(`MeasureTheory/Group/Integral.lean:91`, already pinned for G.5). (b) is (a) +
`haarAverage_of_invariant` (on disk). (c) swap the two integrals
(`integral_integral_swap`, `MeasureTheory/Integral/Prod.lean:532`; integrability
side conditions may be taken as hypotheses — state the strongest provable
variant, e.g. bounded measurable `f`, and record any residual generality gap in
`STATUS.md`), then for each fixed `h` use `hμ` (`MeasurePreserving.integral_comp`
or `integral_map`) to see the inner integral is `∫ f ∂μ`, then `μG` is a
probability. ~90 lines.

**Chapter G II deliverable checklist (definition of done for N9):**
`cond_of_null`, `not_isProbabilityMeasure_cond_null`,
`no_translation_invariant_probabilityMeasure`,
`translation_invariant_l2_eq_zero` + `no_translation_invariant_unit_vector`,
**`no_continuous_gauge_fixing_circle`** + `gauge_fixing_section_discontinuous`,
`brstKer`/`brstIm`/`brstIm_le_brstKer`/`mem_brstKer_iff`/`mem_brstIm_iff`/
`brstCohomology` + `brstCohomology_equiv` + `brst_physical_iff_gauge_invariant`,
`haarAverage_invariant`/`haarAverage_idempotent`/`integral_haarAverage`.
All `sorry`-free, no `axiom`, no `EXTERNAL`.

---

# Chapter B §§7–9 — Symmetries, conservative and deterministic transformations — **work package N10** (promotes the former N7(a) mining note to a full package)

**Book (1857–2005).** §7: any time-indexed conditional probability measure is
parametrized by unitaries — symmetry groups act by unitary representations on
wave-functions. §8: conservative transformations preserve the measure. §9:
**deterministic transformations are exactly the unitaries that preserve the
commutative algebra of events**, and complementarity (non-commuting
observables) is the signature of a *non-deterministic* symmetry
transformation. Target file **`BookProof/ChapterB7.lean`** (import
`BookProof.ChapterG` for `koopmanEquiv` — G.7 built the single-map case; this
package adds the group/algebra structure). §§10–11 (ensemble
forecasting/classical limit) remain prose — triaged, cite-only. **No
`EXTERNAL` hypothesis anywhere in this package.**

### B7.1 — The Koopman representation is functorial (symmetry groups act unitarily, book §7)

**Statements.**
```lean
theorem koopman_comp (f : α ≃ᵐ β) (g : β ≃ᵐ γ) (hf : MeasurePreserving f μ ν)
    (hg : MeasurePreserving g ν ρ) (u : Lp E p ρ) :
    koopmanEquiv f hf (koopmanEquiv g hg u) = koopmanEquiv (f.trans g) (hg.comp hf … ) u
theorem koopman_refl (u : Lp E p μ) : koopmanEquiv (MeasurableEquiv.refl α) … u = u
```
**Proof.** Same `Lp.ext` + `Lp.coeFn_compMeasurePreserving`
(`MeasureTheory/Function/LpSpace/Basic.lean:559`) a.e.-computation as
`koopman_comp_left`/`koopman_comp_right` in `ChapterG.lean` — that template is
on disk; composition of the two a.e. identities plus
`MeasurePreserving.comp` (`Dynamics/Ergodic/MeasurePreserving.lean:93`).
~60 lines. **Corollary (the book's §7 statement):** for a group `G` acting on
`(α, μ)` by measure-preserving equivalences `ρ : G → (α ≃ᵐ α)` with
`ρ (g*h) = ρ h |>.trans (ρ g)` (an action), `g ↦ koopmanEquiv (ρ g) …` is a
group homomorphism into the isometric equivalences of `Lp` — package as
`koopmanRep_mul : K (g * h) = (K g).trans (K h)` (orientation as forced by the
contravariance of composition; state whichever variance the computation gives
and document it). ~30 lines.

### B7.2 — Koopman fixes constants (the vacuum/counting state, book §8)

```lean
theorem koopman_const [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (c : E) :
    koopmanEquiv (E := E) (p := p) f hf (Lp.const … c) = Lp.const … c
```
(or with `indicatorConstLp _ MeasurableSet.univ … c` if `Lp.const` is not
available at the pinned version — grep first). **Proof:** `coeFn` of the
composition is a.e. the constant. ~15 lines. Docstring: the measure `μ` itself
(the "vacuum") is the fixed state of every conservative transformation.

### B7.3 — Deterministic transformations preserve the event algebra (book §9)

**Book:** *"an automorphism `U` is deterministic if and only if `P_A` and
`U P_B U†` commute for all events `A, B`"* — deterministic evolutions are the
ones that map indicators to indicators. Formal shadow, two layers:

**(a) Event-algebra automorphism.** For `f : α ≃ᵐ α` with
`hf : MeasurePreserving f μ μ`, the preimage map on events is a
measure-preserving Boolean automorphism:
```lean
theorem eventMap_measure   (A) : μ (f ⁻¹' A) = μ A          -- hf.measure_preimage
theorem eventMap_inter/union/compl : f ⁻¹' (A ∩ B) = f ⁻¹' A ∩ f ⁻¹' B, …
theorem eventMap_leftInverse : f.symm ⁻¹' (f ⁻¹' A) = A
```
All are `Set.preimage_*` rewrites + `MeasurableEquiv` simp lemmas; ~40 lines
of API glue with docstrings tying each to the book's `U L∞ U† = L∞`.

**(b) Koopman conjugation sends indicators to indicators.**
```lean
theorem koopman_indicatorConstLp (hA : MeasurableSet A) (hμA : μ A ≠ ∞) (c : E) :
    koopmanEquiv f hf (indicatorConstLp p hA hμA c)
      = indicatorConstLp p (hA.preimage f.measurable) … c
```
**Proof.** `coeFn` both sides: `(Set.indicator A (fun _ => c)) ∘ f =
Set.indicator (f ⁻¹' A) (fun _ => c)` — `Set.indicator_comp_right` (grep
`indicator_comp` in `Mathlib/Order/SetNotation`/`Data/Set/Function` for the
exact name) + `Lp.coeFn_compMeasurePreserving` + `indicatorConstLp_coeFn`
(pinned `MeasureTheory/Function/LpSpace/Indicator.lean` region, reuse-table row
from N8). ~50 lines. Docstring: this IS "deterministic ⇒ diagonal stays
diagonal"; combined with B.2′ (`condKernel_disintegration`) the associated
conditional density is the Radon–Nikodym derivative, as the book says.

### B7.4 — Complementarity: a non-deterministic unitary (book §9, contrast)

**Statement.** In `ℂ² = Fin 2 → ℂ` (finite model, reuse Ch. E's Hadamard):
```lean
theorem hadamard_not_deterministic :
    ∃ (P Q : Matrix (Fin 2) (Fin 2) ℂ), P * P = P ∧ Q * Q = Q ∧
      (P * (hadamardU * Q * hadamardUᴴ) ≠ (hadamardU * Q * hadamardUᴴ) * P)
```
with `P = !![1,0;0,0] = Q` diagonal projections and `hadamardU` the Hadamard
unitary already in `ChapterE.lean` (`hadamard_uniformizes` infrastructure —
import, don't rebuild). **Proof:** direct 2×2 computation (`fin_cases` /
`Matrix.mul_apply` / `norm_num`), the conjugated projection is
`(1/2)!![1,1;1,1]`, which does not commute with `diag(1,0)`. ~40 lines.
Docstring: complementarity of position/momentum-type pairs = the conjugating
symmetry is not deterministic; quantum mechanics generalizes classical
statistical mechanics exactly here (book §9's conclusion).

**Chapter B §§7–9 deliverable checklist (definition of done for N10):**
`koopman_comp`, `koopman_refl`, `koopmanRep_mul`, `koopman_const`,
`eventMap_*` API (measure/inter/union/compl/leftInverse),
`koopman_indicatorConstLp`, `hadamard_not_deterministic`. All `sorry`-free,
no `axiom`, no `EXTERNAL`.

---

# Chapter U — Unitary inference / unfer (NEW SOURCE MATERIAL, 2026-07-02) — **work package N8**

**Provenance & merge plan (author's instruction, 2026-07-02).** New content to be
**merged into `book.tex`** and formalized lives in two places:
1. the gitbook repository at **`../test`** (relative to the repo root:
   `/media/leo/e7ed9d6f-5f0a-4e19-a74e-83424bc154ba/test`, site "airma.de") —
   the mathematically substantive files are `unfer/intro.md` (unitary
   inference), `unfer/bayes.md` (Bayesianism vs. hallucinations/undecidability;
   Fock space as state of knowledge; sphere→Gaussian limits), `unfer/kernel.md`
   (the unfer Bayesian-verifier kernel), `unfer/foundations.md`
   (hashing/zero-knowledge), `basics/bond.md` (knowledge in a market economy;
   CLT `1/√n`; proofs as quantum time evolution), `software/searchllm.md`
   (Bayesian verifier = general intelligence);
2. the PubPub collection **https://timepiece.pubpub.org/ec0in** ("ec0.in") —
   its pubs ("Knowledge in a market economy", "Unfer: Unitary inference", …)
   **overlap the gitbook content**; treat the gitbook files as the canonical
   text when merging.

**Merge mapping (editorial step, precedes/accompanies formalization):**
`unfer/intro.md` → motivation section adjacent to the book's Introduction /
Chapter B (the continuous-time-randomness inconsistency and the Mehler-1866
priority claim); `unfer/bayes.md` → merge with Chapter B + the Kopperman/Mehler
material (§0 of this roadmap — the equations in it are *already formalized*,
see U.2); `basics/bond.md` → adjacent to Chapter H (Bayesian-prior essay) with
its two math nuggets extracted (U.5, U.6); `unfer/kernel.md`,
`unfer/foundations.md`, `software/*` → prose/software appendix (non-formalizable
except U.1 which formalizes the kernel's `prob_kernel` claim). The LaTeX merge
itself is an authorial/editorial task; the Lean specialist's obligation is the
**formalization targets U.1–U.6 below**, which do not depend on the merge being
done first.

### U.1 — Born-rule conditioning is Bayesian updating by projection (HEADLINE)

**Source** (`unfer/kernel.md` "`prob_kernel` — the Born rule": *"an event is a
predicate over Fock states; its probability is the squared-amplitude mass of
the states that satisfy it. Conditioning on data zeroes the non-matching
components and renormalizes — a Bayesian update done by projection"*; also
`unfer/bayes.md`'s vacuum-as-prior). This is the precise quantum⇄Bayes bridge
and it is **fully formalizable now** on top of `ChapterB.lean`.

Setting: measure space `(X, μ)`, wave-function `Ψ : X → ℂ` with `MemLp Ψ 2 μ`
and `∫ ‖Ψ‖² = 1`. Definitions and deliverables:
```lean
/-- The Born probability measure |Ψ|²·μ of a wave-function. -/
noncomputable def bornMeasure (Ψ : X → ℂ) (μ : Measure X) : Measure X :=
  μ.withDensity (fun x => ENNReal.ofReal (‖Ψ x‖ ^ 2))

theorem bornMeasure_isProbability (hΨ : ...) : IsProbabilityMeasure (bornMeasure Ψ μ)
  -- = Chapter B `born_backward` re-packaged; `withDensity_apply` + the L² norm.

/-- Conditioning by projection: zero the non-matching components, renormalize. -/
noncomputable def conditionedState (Ψ : X → ℂ) (E : Set X) : X → ℂ :=
  fun x => (Real.sqrt ((bornMeasure Ψ μ) E).toReal)⁻¹ • E.indicator Ψ x

theorem conditionedState_memLp / conditionedState_norm  -- unit vector when μ|Ψ|²(E) ≠ 0

/-- THE BRIDGE: the Born measure of the projected-renormalized state IS the
classical conditional measure (Mathlib `ProbabilityTheory.cond`, `μ[|E]`). -/
theorem born_conditioning (hE : MeasurableSet E) (hpos : bornMeasure Ψ μ E ≠ 0) :
    bornMeasure (conditionedState Ψ E) μ = (bornMeasure Ψ μ)[|E]
```
*Proof of the bridge.* Unfold both sides. LHS density is
`‖c⁻¹ • E.indicator Ψ‖² = c⁻² · E.indicator ‖Ψ‖²` with `c² = (bornMeasure Ψ μ) E`;
`MeasureTheory.withDensity_indicator` (pinned:
`MeasureTheory/Measure/WithDensity.lean:188`) turns
`withDensity (E.indicator f)` into `(μ.restrict E).withDensity f`, and the
scalar factors out (`withDensity_smul`). RHS: `ProbabilityTheory.cond` is
*by definition* `(μ' E)⁻¹ • μ'.restrict E`
(`Probability/ConditionalProbability.lean:74`) with `μ' = bornMeasure Ψ μ`;
`restrict` commutes with `withDensity` (`withDensity_restrict` /
`restrict_withDensity`). Match the two `ENNReal` scalars
(`ENNReal.ofReal_inv_of_pos`, `sq_sqrt`). ~120 lines including the norm
lemmas. Docstring: this theorem is the book-level claim that **quantum
conditioning (wave-function collapse onto an event) and Bayesian conditioning
are the same operation** — the formal content of the unfer kernel's
`prob_kernel` layer.

### U.2 — Sphere→Gaussian / Gegenbauer→Hermite (already formalized — cross-reference)

The three displayed equations of `unfer/bayes.md` ("Relating the Fock-space
with a uniform measure in an infinite-dimensional sphere") are **exactly the
PnpProof Mehler chain, already `sorry`-free in-repo** (§0 S2/S4; reuse table):
the Lopez99 limit `(α/2)^{-n/2} C_n^{(α/2)}(√(2/α)x) → H_n(x)/n!` =
`gegenbauerScaled_tendsto_hermite`; the weight limit `√(1-2x²/α)^{α-1} → e^{-x²}`
= `weight_tendsto_gaussian`; the Hermite normalization `∫ H_n² e^{-x²} = √π·2ⁿ·n!`
= `hermite_normalization` (`PnpProof/SphereGaussian.lean`). **Do not re-derive**;
when this content merges into `book.tex`, its formalization pointer is the
existing PnpProof declarations (and the N5 substrate glue). *Optional stretch
targets only if the author asks:* the closed-form Gegenbauer normalization
`N_n^{(α)}` (first displayed equation — needs Gegenbauer integral identities
not in Mathlib) and the `k`-sphere area-element product formula (chart-level;
`sphereUniform` already provides the measure abstractly).

### U.3 — Fock-space layer: the exponential property

**Source** (`unfer/bayes.md`: *"the tensor product of two Fock spaces produces
another Fock-space, so we do not need an infinite-dimensional tensor-product"*).
The algebraic core is the **exponential property of Fock functors**:
`Fock(V ⊕ W) ≅ Fock(V) ⊗ Fock(W)`. Mathlib now has both ingredients but
**not the isomorphism itself** (grep v4.28.0: absent):
- `SymmetricAlgebra` (bosonic Fock, algebraic layer) —
  `LinearAlgebra/SymmetricAlgebra/Basic.lean:47` (`RingQuot (SymRel R M)`);
- `ExteriorAlgebra` (fermionic) + **graded tensor products**
  `LinearAlgebra/TensorProduct/Graded/External.lean` / `Internal.lean`.

Deliverables (algebraic level — no analytic completion, which honestly matches
the source's "appears as a completion of a countable basis" remark):
```lean
def SymmetricAlgebra.prodEquiv :
    SymmetricAlgebra R (M × N) ≃ₐ[R] (SymmetricAlgebra R M ⊗[R] SymmetricAlgebra R N)
```
*Proof route.* Both sides are commutative `R`-algebras with the same universal
property: algebra maps out of `Sym(M × N)` = linear maps from `M × N` =
pairs of linear maps = pairs of algebra maps out of `Sym M`, `Sym N` = algebra
maps out of the tensor product (`Algebra.TensorProduct.lift` for commutative
targets). Construct both directions by universal property and check the
compositions on generators (`SymmetricAlgebra.ι`, `algebraMap`) — the standard
`ext`-on-generators pattern (`RingQuot.ringQuot_ext`-style). Moderate,
~150 lines. The fermionic (`ExteriorAlgebra`, ℤ/2-graded-sign) analogue via
`GradedTensorProduct` is a stretch goal — attempt it after the symmetric case;
if the sign bookkeeping stalls, record the obstruction and keep the symmetric
result. The vacuum-as-prior remark ("a null-measure set becomes a vacuum
state, i.e. complete ignorance, not zero probability") is Chapter B + N5
material — docstring cross-reference, no new theorem.

### U.4 — Non-differentiability of stochastic trajectories — `EXTERNAL` + wrapper

**Source** (`unfer/intro.md`): Wiener-process paths are a.s. nowhere
differentiable, and (bertoin94) every Lévy process with strictly positive
Gaussian part has a.s. nowhere-differentiable paths — the argument that
continuous-time randomness contradicts Newtonian differentiable trajectories.
**Mathlib v4.28.0 has no Brownian motion** (grep: `Probability/Process/` has
Kolmogorov-extension infrastructure only — `Kolmogorov.lean`,
`FiniteDimensionalLaws.lean`; no `BrownianMotion`). So per the coverage
policy: introduce the Paley–Wiener–Zygmund/bertoin94 statement as an
**`EXTERNAL` named hypothesis** (`levy_paths_nowhere_differentiable`, cite
Bertoin 1994 + Paley–Wiener–Zygmund 1933) and prove the *formalizable wrapper*:
```lean
theorem no_differentiable_trajectory (hext : ∀ᵐ ω ∂ℙ, ∀ t, ¬ DifferentiableAt ℝ (path ω) t) :
    ℙ {ω | ∃ t, DifferentiableAt ℝ (path ω) t}ᶜ = 1   -- and the P(differentiable)=0 corollary
```
— a measure-theoretic triviality (~20 lines) whose value is fixing the
*statement* in Lean so the hypothesis is precisely scoped. Revisit if/when
Brownian motion lands in Mathlib (it is an active mathlib4 project).

### U.5 — Independent components: portfolio risk falls like `1/√n`

**Source** (`basics/bond.md`: *"the Central Limit theorem implies that the
overall risk in a Portfolio approximately decreases with `1/√n`"* — also quoted
by `unfer/foundations.md`). The precise formalizable statement needs no CLT,
only additivity of variance for independent variables — **pinned:**
`ProbabilityTheory.IndepFun.variance_add` / `IndepFun.variance_sum`
(`Probability/Moments/Variance.lean:32/34`).
```lean
theorem portfolio_risk_inv_sqrt (X : Fin n → Ω → ℝ) (hindep : iIndepFun X ℙ)
    (hmem : ∀ i, MemLp (X i) 2 ℙ) (hvar : ∀ i, variance (X i) ℙ = σ ^ 2) :
    variance (fun ω => (∑ i, X i ω) / n) ℙ = σ ^ 2 / n
```
*Proof.* `variance_sum` gives `Var(Σ Xᵢ) = n·σ²`; scaling
`variance_smul` (`Var(c·Y) = c²·Var Y`) with `c = 1/n` gives `n·σ²/n² = σ²/n`.
Standard-deviation corollary: `√(σ²/n) = σ/√n` (`Real.sqrt_div`). ~40 lines.
Docstring ties it to the source's Catastrophe-Bond argument: `n` independent
similar-risk components ⇒ aggregate risk `σ/√n`.

### U.6 — Non-formalizable remainder (triage)

- `basics/bond.md` §"Mathematical proofs as a subcase of quantum-time
  evolution" (theorem = statement, proof = amplitude computation, `|result|` is
  1 if true / 0 if false; undecidability = no Hamiltonian exists): a modelling
  *definition*, not a theorem — its formal shadow is the `{0,1}`-indicator
  amplitude idea already at work in `RcpEuler.lean`; **flag for the author** if
  a precise statement is wanted.
- `unfer/foundations.md`: elastic/funnel hashing (Farach-Colton–Krapivin–
  Kuszmaul) and Ilango's non-interactive perfectly-sound zero-knowledge are
  **external papers' theorems** — formalizing them is out of scope of the book
  roadmap (they would be their own projects); cite, do not hypothesize.
- Economics/superintelligence/market prose in `basics/*`, and the software
  architecture pages (`software/alias.md`, `sovereign.md`, `velyst.md`,
  `altgit.md`, `bai.md`, `math.md`): prose, no formalizable statements.
- `unfer/bayes.md` claims on logic ("real Hilbert-space theory is complete and
  decidable", Kopperman): meta-theoretic — represented in-repo by the
  `PnpProof/Kopperman.lean` substrate (`substrate_decidable_skeleton`), not by
  a new Lean theorem *about* Lean.

**Chapter U deliverable checklist (definition of done for N8):** `bornMeasure`
+ `bornMeasure_isProbability`, `conditionedState` + norm lemmas,
**`born_conditioning`** (headline), `SymmetricAlgebra.prodEquiv` (+ exterior
stretch), `levy_paths_nowhere_differentiable` (`EXTERNAL` hypothesis) +
`no_differentiable_trajectory` wrapper, `portfolio_risk_inv_sqrt` + std-dev
corollary. Target file `BookProof/ChapterU.lean`. U.2 = cross-reference only
(no new code beyond N5 glue).

---

# Chapters F, H — assessment (little/no formalizable content)

These two chapters were triaged and found to be essentially prose (conceptual
physics / philosophy), not theorem–proof mathematics. Numbered theorems: none.
(*Chapter G was originally triaged here too; that triage was **superseded** by
the author's 2026-07-02 instruction — G is now the full work package above,
queue item N6.*)

- **F. Reconstructing the classical trajectory of any isolated quantum system**
  (line 2494). A conceptual argument (presentism/eternalism; "preparation that is
  a function of time" vs "stochastic process indexed by time"; relation to Bell's
  and Wigner's theorems). The only crisp mathematical anchor is **Wigner's theorem**
  (symmetries of a Hilbert space = (anti)unitaries up to phase), which is a cited
  external theorem, not proved here. *No new formalizable statement here*, but
  Wigner's theorem **as infrastructure** is queue item N7(b): an `EXTERNAL`
  named-hypothesis bundle shared with §A.4 (Mathlib does not have it).
- **H. Consciousness as a representation of a Bayesian prior** (line 9122). Pure
  prose (0 equations); an interpretive essay mapping consciousness onto the
  Bayesian-prior formalism of Chapter B. *No formalizable statement*; any content
  reduces to Chapter B's parametrization theorem.

**Recommendation:** no Lean effort on F and H beyond the N7(b) Wigner bundle.

---

# Chapter P — Physics-heavy chapters (lemma mining result)

Chapters mined: **Free-field parametrization / Navier–Stokes** (3699),
**Quantization / Yang–Mills** (6486), **Timepiece & Gribov ambiguity** (7125),
**On the physical parity transformation & antiparticles** (7522),
**Diffeomorphisms & gravity** (7881).

**Finding:** none of these chapters contains a *numbered* Theorem / Proposition /
Lemma / Corollary. They are physics **constructions and derivations**
(Hamiltonian/BRST quantization of gauge fields, mass-gap argument, Navier–Stokes
free-field parametrization, Electroweak parity/CP structure, tetrad gravity),
built on the *same* mathematical apparatus already formalized in Chapter A and
the measure/wave-function apparatus of Chapters B & E. Per the coverage policy
("physics derivations mined only for discrete self-contained lemmas"), the
discrete formalizable content reduces to items already listed:

- **Reused from Chapter A:** Clifford/gamma-matrix identities, the Lorentz/Poincaré
  representation theory, `Pin(3,1)`/`Spin⁺` group structure, real/complex/quaternionic
  commutant trichotomy. The parity/antiparticle and gravity chapters use `iγ⁵` as
  the imaginary unit and the CPT/frame-field construction of §A.4–A.5 — no new
  standalone lemma.
- **Reused from Chapters B/E/G:** "gauge-invariant operators ↔ a commutative von
  Neumann algebra / constraint subspace carrying a well-defined probability
  measure" is the Chapter B parametrization + the **Chapter G package** (N6):
  `gaugeInvariantOperators`, `gauge_constraint_pushforward_full_measure`, the
  Haar averaging lemmas, and the BRST nilpotency cover the discrete mathematical
  content that the Yang–Mills/Gribov chapters lean on. The
  "translation-invariant operators in the center-of-mass" bookkeeping is a
  linear-algebra constraint, not a theorem.
- **Mass gap / Navier–Stokes / Yang–Mills quantization:** these are the physics
  claims of the programme; they are **not** stated as discrete mathematical lemmas
  in `book.tex` and are out of scope for formalization here (they would require
  first *defining* the theory, which the book does constructively, not as a
  theorem to prove). Flag for the author if a specific inequality (e.g. a spectral
  gap bound) is later isolated as a standalone claim.

**Conclusion:** no additional Lean targets beyond Chapters A, B, C.1, D.1, E
and the (2026-07-02-promoted) Chapter G package.

---

## Status summary

Legend: **English proof** = written in this document, Lean-ready.
**Lean DONE** = implemented sorry/axiom-free in `BookProof/` (see the
★ IMPLEMENTATION STATE section at the top and `BookProof/STATUS.md`);
`lake build` green through **wave 39 (8114 jobs, run `c14d1ff7`, 60 modules)**.
The entire original queue N1–N12 (incl. N7(c)) is DONE; the only open items are
the two NEW packages **N13 (Hashimoto SIRK)** and **N14 (QFM)**.

| Section | Content | English proof | Lean status |
|---|---|---|---|
| §A.0–A.2 core | Systems framework, Lemma 26 (orthogonal complement), Lemma 27 (Schur ⇒ irreducible) | **Complete** | **DONE** — `ChapterA.lean` (Schur property = named hypothesis) |
| §A.1 | real↔complex trichotomy (Defs 8–10, Props 11–12) | **Complete** | **DONE IN FULL (waves 7–8)** — `ChapterA1`–`A1f` + `Complexification` as before, plus `ChapterA1g.lean` (**Prop 12 converse** `realification_irreducible_of_not_isCReal` + `realification_classification`) and `ChapterA1h.lean` (**Prop 11 real-side trichotomy** `rType_exhaustive`) |
| §A.2 proper | commutant classification ℝ/ℂ/ℍ (L14, P15–19, L20–34) | **Complete** (L20/28/34 `EXTERNAL`) | **DONE IN FULL (waves 5–6)** — `ChapterA2.lean` (L14), `ChapterA2b.lean` (**P17**), `ChapterA2c.lean` (**P18–P19**), `ChapterA2d.lean` (**P15** `Rreal_isometric_iff_complexification_isometric`), `ChapterA2e.lean` (**P16** both dichotomies) |
| §A.3 | Clifford model, Pauli-real theorem, `Pin(3,1)→O(1,3)`, real irrep classification | **Complete** (Pauli/Weyl `EXTERNAL`) | **DONE (waves 9–14, 18, 21, 23, 26–37)** — `ChapterA3`–`A3v`: L40/P37 (`EXTERNAL` `PauliFundamental`)/P46/Def 49; **Lemma 48 complete** (`Λ`, `Υ`, `det_exp_eq_exp_trace`, adjoint-exponential ODE, **`lemma48_bridge`**); **Lemma 52 machinery complete** (chirality/parity mechanism, arbitrary-`N` `projSym`/`projAnti`/`projMixed` + `tensorPow_complete_reducibility`, summand dimensions `N = 2…6` via `card_fixedTuples`). **Residue: the Weyl identification of `projMixed` summands with `V_{(m,n)}` = N11** |
| §A.4–A.5 | Bargmann–Wigner, Majorana–Fourier/Energy unitarity, localizable-rep classification, CPT/Cor 1 | **Written**; unitarity props doable, classification `EXTERNAL` Wigner/Mackey | **Cores DONE (waves 15–17, 19–20, 22, 24–25)** — `ChapterA4`–`A4g` (P61/73/74/76 unitarity, P79 little groups `SU(2)`/`SE(2)`, P81 rep laws, P87 exclusions, P88/Cor 1 energy-sign cores), `ChapterA5` (CPT/mass-shell). **Residue: exhaustiveness clauses = N11, DONE wave 38 (`ChapterA4h`/`ChapterA3w`)** |
| Ch. B.1–B.2 | Born parametrization both ways + `Ψ = 𝒰 e₀` | **Complete** | **DONE** — `ChapterB.lean` |
| Ch. B.2′/B.3 | condKernel disintegration converse; operator form/SVD via §0 dense-core | **Complete** | **DONE IN FULL (N3 ✅, waves 10 + 15)** — `condKernel_disintegration` (`ChapterB.lean`); `ChapterB3.lean` (`IsPartialIsometry` layer + B.3c `conditional_operator_identity`); `ChapterB3b.lean` (**`denseCore_svd`** finite-rank SVD) |
| Ch. C | C.1 `n!/nⁿ→0` (Stirling) | **Complete**; C.2 author-dependent | **DONE** — `ChapterC.lean` |
| Ch. D | D.1 computable ⇒ countable ⇒ a.e. uncomputable | **Complete**; D.2 non-math | **DONE** — `ChapterD.lean` |
| Ch. E | 2-state clock, stochastic-map classification, Hadamard/DFT uniformization, hyperspherical Born recursion onto simplex | **Complete** | **DONE** — `ChapterE.lean` (E.5 = cross-ref into §A.2) |
| §0 substrate glue | instantiate Ch. B/E at `koppermanSubstrate` / `MehlerPrior` | — (already formalized in `PnpProof`) | **DONE** — `Substrate.lean` (N5 ✅) |
| **Ch. G (G.0–G.7)** | gauge group of a parametrization, orbit=fiber, invariance⇔factoring, invariant subalgebras, gauge-independent expectations, Dirac no-invariant-state obstruction, gauge-fixing sections, Haar averaging, **pushforward-implements-constraints headline**; BRST Ω²=0; Koopman `koopmanEquiv`; damped-oscillator flow group | **Complete** (this doc, 2026-07-02; all Mathlib names pinned) | **DONE** — `ChapterG.lean` (N6 ✅, run `bee1f248`, no `EXTERNAL`) |
| **Ch. G II (G.8–G.12)** | conditioning fails on null constraint sets; Dirac obstruction for any infinite gauge group; **Gribov headline `no_continuous_gauge_fixing_circle`**; BRST cohomology + `brst_physical_iff_gauge_invariant`; Haar averaging = invariant projection, expectation-preserving | **Complete** (this doc, 2026-07-03; all Mathlib names pinned; no `EXTERNAL`) | **DONE** — `ChapterG2.lean` (N9 ✅, wave 4 run `8296bfb3`, all of G.8–G.12) |
| **Ch. B §§7–9** | Koopman functoriality (`koopman_comp`/`koopmanRep_mul` — symmetry groups act unitarily), constants fixed, deterministic = event-algebra automorphism (`koopman_indicatorConstLp`), complementarity contrast (`hadamard_not_deterministic`) | **Complete** (this doc, 2026-07-03; builds on on-disk `koopmanEquiv`; no `EXTERNAL`) | **DONE** — `ChapterB7.lean` (N10 ✅, wave 4 run `8296bfb3`, B7.1–B7.4) |
| **N13 Hashimoto SIRK** | φ-functions + recurrence, exponential-integrator Duhamel, resolvent shift identity `Xⱼ=(I+h(m−j)Xₘ)⁻¹Xₘ`, rational-Krylov = rational functions of `Xₘ`, Arnoldi/SIRK compression, `e^{−hm}` SIRK convergence conditional on `EXTERNAL` Crouzeix (~12 deliverables H1.1–H2.4) | **Full guided spec in the N13 queue entry** (2026-07-06; pins verified: `resolvent`, `integral_exp`, `Orthonormal`) | **Open (N13 — FLAGSHIP, FIRST open item; source `../unfer/Hashimoto.md`; target `ChapterH1.lean` / `ChapterH2.lean`)** |
| **N14 QFM** | continuity-Hamiltonian Hermiticity, orthogonal-Fock disjoint-support identities, diagonal-Gram `O(M)` closed-form training, exact commutativity/time-averaging, vacuum projector + dressed-vacuum Bessel `Σεⱼ²≤1`, Mehler overlap `εⱼ>0`, Count-Sketch unbiasedness, unitary reduced flow, pseudo-inverse recovery (~12 deliverables F2.1–F3.5) | **Full guided spec in the N14 queue entry** (2026-07-06; pins verified: `orthogonalProjection`, `selfAdjoint.expUnitary`, Bessel) | **Open (N14 — FLAGSHIP, SECOND open item; source `../unfer/QFM.tex`; reuses on-disk `ChapterF1.numberOp` (N12) + `SphereGaussian.lean`; target `ChapterF3.lean` / `ChapterF4.lean` — F1/F2 taken)** |
| **N11 exhaustiveness bundle** | `WignerClassification` + `MackeyImprimitivity` + `WeylCompleteReducibility` named hypotheses; conditional assemblies of Props 81/87/88 + Cor 1 and of Lemma 52's `V_{(m,n)}` identification | **Complete** | **DONE (wave 38)** — `ChapterA4h.lean` + `ChapterA3w.lean`, `sorry`/`axiom`-free |
| **N12 S7 field package** | Bargmann–Fock polynomial CCR model: `[a, a†] = 1`, Hermitian rep `φ = a†+a` / `π = i(a†−a)`, number operator, **`quadratic_ordering_vacuum` (⟨0\|H\|0⟩ = 0)** headline, BRST bridge to `ChapterG2`; docstrings cite `../unfer` crates (§0 S7) | **Complete** | **DONE (wave 38)** — `ChapterF1.lean` (`numberOp`, `quadratic_ordering_vacuum`; reused by N14 F2.7) |
| **N7(c) mass gap** | Bargmann–Fock mass gap: `H := a†a = numberOp`, `H Xⁿ = n·Xⁿ`, vacuum energy 0, gap `Δ = 1`, `deformedHamiltonian c := c•N`, `[H_c, N] = 0` | **Complete** | **DONE (wave 39)** — `ChapterF2.lean` (`mass_gap`) |
| **Ch. U (U.1–U.5)** | Born conditioning = `ProbabilityTheory.cond` (headline), Fock exponential property `SymmetricAlgebra.prodEquiv`, 1/√n portfolio risk, Lévy nowhere-differentiability (`EXTERNAL` + wrappers), sphere→Gaussian cross-ref | **Complete** (this doc, 2026-07-02; source = `../test` gitbook + pubpub ec0in) | **DONE** — `ChapterU.lean` (N8 ✅, run `e3ffd49f`: `born_conditioning`, `prodEquiv`, `no_differentiable_trajectory`/`differentiable_trajectory_null`, `portfolio_risk_inv_sqrt`/`portfolio_std_inv_sqrt`; U.2 = cross-ref into `PnpProof/SphereGaussian.lean`) |
| Ch. U (U.6 + fermionic U.3) | hashing/ZK/economics prose = cite-only; exterior-algebra analogue of the Fock property | **Triaged out of scope** | — |
| Ch. F, H | trajectory / consciousness | **Triaged non-formalizable** (F's Wigner anchor = N7(b) `EXTERNAL` bundle) | — |
| Book-Ch.-B §§10–11 | ensemble forecasting, classical limit | Triaged prose, cite-only (§§7–9 are now the full N10 package above) | — |
| Ch. P | Navier–Stokes / Yang–Mills / Gribov / parity / gravity | **No discrete lemmas** — reuse Ch. A/B/E/G | — |
| — | ODE, P≠NP, Riemann-Hypothesis chapters | **Excluded by author** | (P≠NP model & RH route live in `PnpProof`/`RiemannProof`) |

**Global policy honoured (and verified in `BookProof`):** no `axiom`
declarations anywhere — `#print axioms` shows only `propext`,
`Classical.choice`, `Quot.sound`; every genuine external theorem (Pauli's
fundamental theorem, Weyl complete reducibility, Schur for
unitary/imprimitivity, Mackey imprimitivity, Wigner little-group
classification, Varadarajan Thm 6.12, Wigner's symmetry theorem) is flagged
`EXTERNAL` and introduced as a **named hypothesis** (as Lemma 27 already does
for the Schur property), never asserted. No `sorry` anywhere in `BookProof`.

**Remaining implementation order (updated 2026-07-06). The ENTIRE original
queue N1–N12 (including N7(c), the mass gap) is DONE — N11 + N12 in wave 38,
N7(c) in wave 39; `BookProof` is 60 modules, green at 8114 jobs. The author
(2026-07-06) then prioritized two new `../unfer` algorithm packages and asked
for "a lot of guided work", so the only remaining order is:**
**N13 (the Hashimoto SIRK package `ChapterH1`/`H2`: φ-functions + recurrence,
Duhamel, the resolvent shift identity, rational-Krylov characterization,
Arnoldi/SIRK compression, `e^{−hm}` bound conditional on `EXTERNAL` Crouzeix —
~12 deliverables H1.1–H2.4, source `../unfer/Hashimoto.md`)** →
**N14 (the QFM package `ChapterF3`/`F4`: continuity-Hamiltonian Hermiticity,
disjoint-Fock identities, `O(M)` diagonal-Gram training, commutativity/
time-averaging, vacuum projector + Bessel `Σεⱼ²≤1`, Mehler overlap,
Count-Sketch unbiasedness, unitary flow, pseudo-inverse recovery — ~12
deliverables F2.1–F3.5, source `../unfer/QFM.tex`; REUSES the on-disk
`ChapterF1.numberOp` (N12) + `SphereGaussian.lean`, no new prerequisite)**.
Then — only when the author names it — the next `book.tex` chapter promoted to
a package (author note: "there are many chapters in `book.tex` still
unformalized"). **The dimension-count thread (`ChapterA3r`–`A3v`) is CLOSED at
`N = 6`** — do not extend it; a useful pass lands the N13 + N14
sub-deliverables, not more instances of already-general results, and not a
re-verification of the already-green N1–N12 files (see the ★ MANDATE and STOP
RULE at the top). Treat N13/N14 as the template for turning a cited algorithm
into a fully-guided package.
