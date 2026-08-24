# CONSOLIDATED_PLAN.md — The Single Plan

One plan that supersedes the per-thread plans for **future work**. It (1) collects
everything that is still **open** from `BOOK_PROOF_PLAN.md`,
`PLAN_LEAN_SPECIALIST_UNPROVED.md`, `SPECIALIST_PLAN_REMAINING.md`,
`PLAN_LEAN_SPECIALIST_COHERENT.md`, `PLAN_A_BOOK_FORMALIZATION.md`,
`PLAN_B_PROSE_VERIFICATION.md`, `SINGULARITY_DETECTION_PLAN.md` and
`PLAN_A_EXECUTION_REPORT.md`, and (2) gives a **disposition for every item** in
`Issues.md` and `Contention.md`. Work already landed is listed in §2 so it is not
re-done or re-listed.

**Status (2026-08-24 — the Aristotle SIRK / QG Hermite / Friedrichs / Fermion-Fock
wave merged into this repository; §8 gate NOT re-run here (not compiled, by
instruction).**

The parallel Aristotle lineage was merged in as commit `590d1e0` (2026-08-24):
26 new `BookProof` modules (Fermion/Fock second quantization, the `ℤ₂`-graded
Fock and its Hashimoto/SIRK selection, Krylov shift-span, the differential
Faris–Lavine NS estimate, the QG Hermite core / Friedrichs / oscillator ESA, the
scalaron densitized transfer, and the SIRK reliability chain) plus
`Book/SirkReliability.lean`, with `Book.lean`, `BookProof.lean`,
`CONSOLIDATED_PLAN.md`, `ARISTOTLE_SUMMARY.md`, `Issues.md` and six `Book/`
chapters merged (both-lineages content combined).  **All merged `BookProof`
modules are `sorry`-free and `axiom`-free** (verified in this repository: the only
Lean `sorry`s are the 43 quarantined ones under `UsedRoute/`/`UnusedRoute/`); every
new module is registered in `BookProof.lean` and the `Book/` `#check` citations
resolve against the copied namespaces.

* **§8 gate — NOT re-run in this repository.**  The merge was made **without
  compiling** (per instruction, the build is left to the Lean 4 specialist).  The
  claims in the 2026-08-24a…d blocks below ("gate re-run green") were verified in
  the *producing* workspace, **not** in this repository snapshot.  The specialist
  must `lake build`, `lake build RandomMap`, `lake build UsedRoute`,
  `./patches/build-book.sh`, `./patches/check-katex.sh`, then re-run the
  sorry/axiom and isolation audits, and confirm the four new Book chapters
  (`Starobinsky`, `NavierStokesHashimoto`, `CarlemanFlux`, `SirkReliability`)
  build and their `#check` citations resolve.  See item 1 of "Work available for
  the Lean 4 specialist" below.

**Status (2026-08-24d — §12 Gap 4c closed on its remaining, existence side: the Gram
whitening the solver performs is an orthonormalization of the retained Krylov subspace,
and one exists).**

* **`BookProof/ChapterSirkGramWhitening.lean`** (namespace
  `BookProof.ChapterSirkGramWhitening`, `sorry`-free / `axiom`-free) supplies what
  `ChapterSirkWhitening` assumed.  That module shows the reduction depends only on the
  retained subspace, but conditionally on being handed an isometric embedding `V∗V = 1`;
  the numerics is handed nothing — it forms the Gram matrix `G_{ij} = ⟪w_i, w_j⟫` of the
  raw (rational) Krylov vectors and whitens with a `T` such that `T∗ G T = 1`.  Now:
  * `synthesis w` (`c ↦ ∑ i, c i • w i`), `range_synthesis`, `synthesis_adjoint_eq`,
    `synthesis_injective_of_linearIndependent`;
  * `gramOp w = (synthesis w)∗(synthesis w)` with `gramOp_apply` (it acts by the Gram
    matrix), `gramOp_isSelfAdjoint`, `gramOp_nonneg`, and the matrix layer `gramMatrix`,
    `gramMatrix_conjTranspose`, `gramOp_eq_toEuclideanCLM`, `IsWhiteningMatrix`,
    `isWhitening_of_matrix`;
  * **`whitened_adjoint_comp_self`** — a whitening *is* an isometric embedding, with
    `range_whitened` identifying its range with the retained subspace;
  * **`exists_isWhitening`** — such a `T` exists for linearly independent raw vectors, so
    the whitening-independence theorems are never vacuous; and
    `exists_isometry_range_eq_span` — in general an orthonormalization exists with
    reduced dimension equal to the *rank*: the exact, lossless form of the code's rank
    truncation of a degenerate Gram matrix (the quantified near-degenerate bound stays
    `ChapterSirkTruncation`);
  * `sirkApprox_gram_whitening_eq`, `compress_gram_whitening_conj` — the end statements
    for two Gram whitenings of the same vectors;
  * `norm_defect_synthesis_le` and `sirk_end_to_end_truncated_gram` — the quantified
    version: if every raw vector sits within `δ` of the retained subspace, a reduced
    state loses at most `δ √m ‖c‖`, which is the additive term in the end-to-end bound
    (`δ = 0` recovers the lossless case).
* Cited from the Verso chapter `Book/SirkReliability.lean`; **§8 gate — re-run green in
  this wave.**

**Status (2026-08-24c — §12 Gap 4b extended to the *resolvent* side: the rational Krylov
space of the shift-invert scheme is identified with the ordinary Krylov space).**

* **`BookProof/ChapterKrylovShiftSpan.lean`** (namespace `BookProof.KrylovShiftSpan`,
  `sorry`-free / `axiom`-free) proves, over an arbitrary module over an arbitrary
  commutative ring and for an arbitrary shift schedule:
  * `forwardSpan_eq_krylovSpan` / `forwardSpan_eq_forwardSpan` — the operator-product
    form of the multi-shift span identity already proved for vectors over a field in
    `ChapterSirkMultiShift`;
  * `tailProd_eq_forwardProd_rev` / `tailSpan_eq_krylovSpan` — the tail products
    `(H − z_{k−1}) ⋯ (H − z_j)` are the forward products of the reversed schedule, so
    they span the Krylov space as well;
  * **`resolventSpan_eq_map_krylovSpan`** — with `X i` a two-sided inverse of `H − z i`,
    `span{v, X₀v, X₁X₀v, …, X_{k−1}⋯X₀v} = (X_{k−1}⋯X₀) '' span{v, Hv, …, Hᵏv}`; the
    supporting algebra is `commute_resolvent_shiftOp`, `commute_resolvent`,
    `commute_resProd_shiftOp` and `resProd_mul_tailProd`;
  * `resProd_mul_forwardProd` / `forwardProd_mul_resProd` /
    `krylovSpan_eq_map_resolventSpan` — the identity read backwards, the two products
    being mutually inverse — and `resVec` / `resolventSpan_eq_span_resVec`, the same span
    written with the vectors the solver computes;
  * **`resolventSpan_of_perm`** — the rational Krylov space is unchanged by reordering the
    first `k` shifts (`resProd_of_perm`), the flag it passes through is not.
* This complements `ChapterHashimotoComplexShifts.sirkDen_rkVec` (the same space seen as
  rational functions of one fixed resolvent) and is cited from the Verso chapter
  `Book/SirkReliability.lean`.
* **§8 gate — re-run green in this wave.**

**Status (2026-08-24b — §10.6.2 item 3: the graded Hamiltonian's analytic layer is finished:
it is an *even* operator for the `ℤ₂` grading, the Hashimoto/SIRK shift-invert limit selects
its Friedrichs extension, and it generates a global unitary flow).**

* **`BookProof/ChapterGradedHashimoto.lean`** (namespace `BookProof.GradedHashimoto`,
  `sorry`-free / `axiom`-free) builds on `ChapterGradedFriedrichs` (which had proved that
  `H = dΓˢ(A) ⊗ 1 + 1 ⊗ dΓᵃ(B)` is densely defined, symmetric and positive on
  `ℓ²(Conf × FConf)` itself, hence has a positive self-adjoint extension) and adds what the
  two factors already had separately:
  * **evenness** — `parityF_creVecF` and `parityF_dGammaF` (the fermionic second
    quantization is a sum of products of two odd operators, hence even) give
    `gradeOp_gradedHamiltonianAlg`: `(−1)^{N_f} H = H (−1)^{N_f}`, so `H` preserves the
    even and the odd subspace (`gradedHamiltonianAlg_evenPart`,
    `gradedHamiltonianAlg_oddPart`);
  * **the SIRK selection** — `gradedHamiltonianB`, `graded_hashimoto_selects`,
    `gradedSecondQuantization_hashimoto_selects`, with `gradedEnum` and
    `gradedNumber_hashimoto_selects` (total number operator `N_b ⊗ 1 + 1 ⊗ N_f`) making it
    non-vacuous;
  * **the flow** — `graded_stone_flow`, `gradedNumber_stone_flow`: the selected extension
    generates a global unitary group solving the Schrödinger equation on its domain;
  * `gradedHamiltonianAlg_otimes`: energies add on elementary tensors.
* **What of item 3 is still open.**  Only the *specific* one-particle space: the graded
  statements are proved for the one-particle `ℓ²(ℕ)` of an arbitrary Hilbert basis, not for
  `L²(ℝ⁸⁴ × ℤ₂¹⁹)` with the gauge-fixed gravity Hamiltonian (that is §10.6.2 item 4).
  §10.6.1 targets 2/3/4 (exponential potential), §10.6.2 items 1 and 4, and research
  boundary **A1** are unchanged.
* **§8 gate — re-run green in this wave** (`lake build` over the default targets, with the
  `#print axioms` audit lines for the new module reporting only `propext`,
  `Classical.choice`, `Quot.sound`).

**Status (2026-08-24 — §10.6.2 item 3: the fermionic (CAR) half of the second quantization
is built, and with it the graded Fock space `Γˢ ⊗ Γᵃ` carrying the `ℤ₂`-graded
superalgebra; the abstract BRST ghost relations are now realized by concrete operators).**

* **The antisymmetric factor `Γᵃ`, CLOSED.**  `BookProof/ChapterFermionFock.lean`
  (namespace `BookProof.FermionFock`, `sorry`-free / `axiom`-free) mirrors
  `ChapterFockSecondQuantization` on the fermionic side: a configuration *is* its finite
  set of occupied modes (`FConf = Finset ℕ`, Pauli built into the type), the Jordan–Wigner
  sign `fsign j S = (−1)^{#\{i ∈ S : i < j\}}` defines `creF`/`annF`, and all four
  canonical **anti**commutation relations hold (`car_annF_creF_self`, `car_creF_creF` with
  `creF_creF_self`, `car_annF_annF`, `car_annF_creF_of_ne`).  Creation and annihilation are
  formal adjoints (`inner_creF_left`), the second quantization `dGammaF` restricts to the
  one-particle operator (`dGammaF_one_particle`), is symmetric and positive for a
  Hermitian positive one-particle matrix, hence has a Friedrichs extension
  (`dGammaF_friedrichs_extension`, `secondQuantizationF_friedrichs`) that the
  Hashimoto/SIRK shift-invert limit selects (`dGammaF_hashimoto_selects`,
  `secondQuantizationF_hashimoto_selects`, non-vacuous via `fermiEnum`).
* **The BRST hypotheses are not vacuous.**  `ghostCAR_creF_annF` realizes
  `BookProof.BRSTNilpotent.GhostCAR` with the operators built here, and
  `brst_charge_nilpotent_fermiFock` is the resulting concrete `Q² = 0`.
* **The graded space `Γˢ ⊗ Γᵃ`, and the book's unified relation.**
  `BookProof/ChapterGradedFock.lean` (namespace `BookProof.GradedFock`) builds elementary
  tensors `otimes` and the two operator lifts `liftFst`/`liftSnd` (`liftFst_liftSnd_comm`:
  operators on different factors commute), then defines the graded Fock space over
  `Conf × FConf` with its even (`bcre`, `bann`) and odd (`fcre`, `fann`) operators, and
  proves **`super_canonical`**: with the Koszul sign of `ChapterSuperBracket`,
  `⟦a(p,j), a†(q,k)⟧ = δ_{pq} δ_{jk}` — one formula giving the bosonic commutator CCR, the
  fermionic anticommutator CAR and the vanishing mixed brackets, with
  `super_canonical_cre`/`super_canonical_ann` alongside.  The `ℤ₂` grading `(−1)^{N_f}`
  (`parityF`, `gradeOp`) is an involution, even on the bosonic operators, odd on the
  fermionic ones, and splits the space (`even_add_odd`, `gradeOp_evenPart`,
  `gradeOp_oddPart`).  `ChapterFockSecondQuantization` gained the off-diagonal bosonic
  relations (`ccr_annA_creA_of_ne`, `ccr_annA_annA`, `ccr_creA_creA`) that this needs.
* **What of item 3 is still open.**  The *analytic* graded conclusion — the Friedrichs
  theory of `dΓˢ(A) ⊗ 1 + 1 ⊗ dΓᵃ(B)` on `ℓ²(Conf × FConf)` itself rather than factorwise —
  and the specific `ℝ⁸⁴ × ℤ₂¹⁹` one-particle space.  §10.6.1 targets 2/3/4 (for the
  exponential potential), §10.6.2 items 1 and 4, and research boundary **A1** are
  unchanged.
* **§8 gate — re-run green in this wave** (see `BookProof/STATUS.md`).

**Status (2026-08-23j — the Friedrichs extension is proved *canonical*: it is the unique
self-adjoint extension whose domain lies inside the form domain, in the positive and in the
merely semibounded case, with the QG scalaron and reduced-sector instances).**

* **The canonicity half of the Friedrichs theorem, CLOSED.**
  `BookProof/ChapterFriedrichsCanonical.lean` (namespace `BookProof.FriedrichsCanonical`,
  `sorry`-free / `axiom`-free) packages the construction of §11.4 as a named operator —
  `formDomain P` (the form domain `Q(H)`), `friedrichsDomain P`, `friedrichsOp P hdense` —
  re-proves the existence statement for it
  (`friedrichsOp_isPositiveSelfAdjointExtension`), and then proves what the existential
  form could not say: **`friedrichs_canonical`**, every symmetric extension of `H` with
  domain inside `Q(H)` is a restriction of `A_F`, and hence
  **`friedrichs_unique_selfAdjoint`**, `A_F` is the *unique* self-adjoint extension with
  that property (Reed–Simon Vol. II, Thm X.23).  The classical semibounded statement comes
  with it (`shiftedPosSymOp`, `semiboundedFriedrichsOp`,
  `semiboundedFriedrichsOp_isSemiboundedSelfAdjointExtension`,
  `semibounded_friedrichs_unique`).
* **§10.6.1 — the QG instances.**  `qgOneParticleHermite_friedrichs_canonical` /
  `qgOneParticleHermite_friedrichs_unique`: on the Gauss–polynomial (Hermite) core of
  `L²(ℝ)` the scalaron Hamiltonian `−Δ + V(φ)` has exactly one positive self-adjoint
  realization whose domain stays inside the form domain.
  `qgOneParticleSector_friedrichs_canonical` / `qgOneParticleSector_friedrichs_unique`: the
  same for the reduced `(R_c, φ)` sector with the lower bound of its potential.
* **Not vacuous.**  `unbounded_friedrichs_canonical_example` applies the construction and
  the uniqueness statement to the genuinely unbounded diagonal operator `A eₙ = n eₙ` on
  the finite-mode domain of `ℓ²(ℕ, ℂ)`.
* **The honest boundary is unchanged.**  Uniqueness within the energy-form class is *not*
  essential self-adjointness — extensions leaving `Q(H)` are not excluded by it — so the
  ESA half of §10.6.1 target 4 is still open for the exponentially growing scalaron
  potential (closed only for the parabolic potential and its bounded perturbations).
  Target 2 still needs restating, target 3 (flux/Carleman) is untouched, and the standing
  research boundary **A1** is unchanged.
* **§8 gate — re-run green in this wave** (see `BookProof/STATUS.md` for the counts).

**Status (2026-08-23i — §10.6.1: the one-particle Hamiltonian on the Gauss–polynomial
(Hermite) core is symmetric and semibounded, hence has a canonical Friedrichs realization;
and for the harmonic (conformal-mode) potential — and any bounded perturbation of it — it
is **essentially** self-adjoint on that core, with its Stone flow.  For the exponentially
growing scalaron potential the uniqueness (ESA) half of target 4 is still open).**

* **§10.6.1 target 4 — the realization exists and is canonical (the existence half).**
  `BookProof/ChapterQgHermiteFriedrichs.lean` (namespace `BookProof.QgHermiteFriedrichs`,
  `sorry`-free / `axiom`-free) puts the operator structure on the domain that the previous
  wave fixed.  Differentiation acts on the polynomial factor as the twisted derivative
  `coreD j p = ∂ⱼp − (xⱼ/2)p` (`hasDerivAt_pgFun_coord` certifies this is the coordinate
  derivative of `p(x)e^{−‖x‖²/4}`), so `kinPoly p = −∑ⱼ coreD j (coreD j p)` is `−Δ` on the
  core and `hamCore` is `−Δ + W` for any continuous `ExpBounded` potential.  Gaussian
  integration by parts (`gaussInt_coreD`, `gaussInt_kinPoly`) gives symmetry
  (`hamCore_symmetricOn`) and the identity `Re⟪ψ, −Δψ⟫ = ∑ⱼ‖Dⱼψ‖² ≥ 0`
  (`re_gaussInt_kinPoly_self`), hence the lower bound `hamCore_quadForm_ge`: `W ≥ c` implies
  `c‖ψ‖² ≤ Re⟪ψ, Hψ⟫` on the core.  With `polyGaussCore_dense` this is exactly the input of
  the project's Friedrichs statements (named hypotheses, never axioms), giving
  `hermiteCore_friedrichs_extension` / `hermiteCore_friedrichs_extension_of_nonneg` and the
  two QG instances: `qgOneParticleHermite_friedrichs` (scalaron on `L²(ℝ)`, *positive*
  extension, since `V ≥ 0` for `α > 0`) and `qgOneParticleSector_friedrichs` (the reduced
  `(R_c, φ)` sector, semibounded by `−M⁴/(16α)`).
* **§10.6.1 target 4 — CLOSED for the harmonic (conformal-mode) potential, in every
  dimension.**  `BookProof/ChapterQgHermiteOscillatorEsa.lean` (namespace
  `BookProof.QgHermiteOscillator`, `sorry`-free / `axiom`-free) proves a general criterion —
  `essentiallySelfAdjointOn_of_eigenbasis`: an operator with an orthonormal Hilbert basis of
  eigenvectors with real eigenvalues inside its domain has trivial deficiency at every
  non-real point — and then supplies the eigenbasis for `−Δ + ‖x‖²/4`: on polynomials
  `−Dⱼ² + xⱼ²/4 = a†ⱼaⱼ + ½` (`coreD_sq_add_harm`, `kinPoly_add_harmPoly`) and
  `a†ᵢaᵢHe_α = αᵢHe_α` (`crePoly_annPoly_hermiteMv`), so the product Hermite functions
  satisfy `Hψ_α = (|α| + d/2)ψ_α` (`harmCore_hermiteMvLp`).  Conclusion:
  **`harmonicCore_essentiallySelfAdjoint`** — unconditional essential self-adjointness on
  the Gauss–polynomial core of `L²(ℝᵈ)` — with `harmonicCore_stone_flow` the Stone flow the
  target also asks for.  A Kato–Rellich step (`norm_potLp_le`, `hamCore_add_potential`)
  extends it to `−Δ + ‖x‖²/4 + B` for every continuous *bounded* real `B`
  (`harmonic_add_bounded_essentiallySelfAdjoint`).
* **The honest boundary.**  For the *exponentially growing* scalaron potential what is
  proved is *a* self-adjoint realization together with a canonical choice of it — **not**
  essential self-adjointness; the ESA half of target 4 is closed only for the parabolic
  potential and its bounded perturbations, which do not include `V(φ)`.  Target 2 (which
  still needs restating) and target 3 (the flux/Carleman route) remain open.  The
  standing research boundary **A1** (continuum ESA for `□ + V` on `L²(ℝ⁸⁴)`) is unchanged.
* **§8 gate — re-run green in this wave** (see `BookProof/STATUS.md` for the counts).

**Status (2026-08-23h — §10.6.1 target 1 CLOSED: the gauge-fixed one-particle Hamiltonian is
well defined on the Gauss–polynomial (Hermite) core, in one variable and in every
dimension).**

* **§10.6.1 target 1 — well-definedness on the core, CLOSED.**
  `BookProof/ChapterQgHermiteCore.lean` (namespace `BookProof.QgHermiteCore`, `sorry`-free /
  `axiom`-free) proves the Gaussian-tail dominance as the formal inequality the plan asks
  for — `exp_abs_le_const_mul_exp_sq`: `e^{c|x|} ≤ e^{2c²}e^{x²/8}` for every real `c`, `x`
  — introduces the **exponential growth class** `ExpBounded` (`|f x| ≤ C e^{c‖x‖}`, on an
  arbitrary normed space; closed under sums, products, scalar multiples and coordinate
  composition), shows it contains every polynomial and the scalaron potential
  (`expBounded_poly`, `expBounded_starobinskyV`), and concludes that multiplication by any
  continuous exp-bounded potential maps the Gauss–polynomial core into `L²`
  (`memLp_mul_gaussPoly_of_expBounded`, `memLp_starobinskyV_mul_gaussPoly`,
  `memLp_scalaronFull1D_mul_gaussPoly`).  Since the core is invariant under differentiation
  (`hasDerivAt_gaussPoly`, `deriv2_gaussPoly`), **`H ψ = −ψ'' + Wψ` lands in `L²` for every
  core element** (`memLp_hamiltonian_gaussPoly`, `memLp_scalaronHamiltonian_gaussPoly`).
  In arbitrary dimension the same argument runs on the project's product core
  (`exists_exp_bound_mvPolyEval`, `memLp_mul_pgFun_of_expBounded`), with the reduced
  two-variable sector `(R_c, φ)` as the named instance
  (`memLp_scalaronSectorPotential_mul_pgFun`).
* **Still open in §10.6.1:** target 2 (the relative bound) **needs restating** — an
  inequality of relative-bound form on a dense core extends to a genuine relative bound,
  which fails for an exponentially growing potential in one dimension, so the literal
  statement in §10.6.1 should not be formalized as written; target 3 (the flux/Carleman
  route) and target 4 (the closing unconditional ESA on the core) are untouched.
* **§8 gate — re-run green in this wave** (see `BookProof/STATUS.md` for the counts).

**Status (2026-08-23g — the two measurement-side items of §12 Gap 2 CLOSED: the Ritz
values are identified with the bottom of the spectrum (QYM), and the laminar decay rate
is proved and shown to survive the reduction (NS Lagrangian); §8 gate re-run green).**

* **§12 Gap 2 — "the Ritz/gap values converge to the spectrum of the Friedrichs
  extension", CLOSED (bounded regime).**  `BookProof/ChapterSirkRitzSpectrum.lean`
  (namespace `BookProof.ChapterSirkRitzSpectrum`, `sorry`-free / `axiom`-free) proves
  `le_rayleigh_iff_le_spectrum` — for a bounded self-adjoint `T`, `c‖x‖² ≤ Re⟪x, Tx⟫` for
  every `x` iff `c ≤ μ` for every `μ ∈ spectrum ℝ T`, via the C*-algebra fact that a
  self-adjoint element is nonnegative iff its spectrum is, applied to `T − c` — then
  `spectrum_real_nonempty`, `spectrum_real_bddBelow`, and
  `sInf_spectrum_eq_rayleighInf` (**bottom of the spectrum = bottom of the numerical
  range**).  Density and continuity give
  `ritzInf_finiteModeDomain_eq_rayleighInf`, and
  `ritzInf_tendsto_sInf_spectrum` / `galerkin_ritz_tendsto_sInf_spectrum_of_selected`
  conclude: the Rayleigh–Ritz values of the Hermite/Galerkin truncations converge to the
  bottom of the spectrum of the extension the algorithm selects.
* **§12 Gap 2 — "the diffusive decay statement (the laminar `νk²` decay rate)", CLOSED.**
  `BookProof/ChapterSirkDiffusiveDecay.lean` defines the parabolic semigroup
  `heatFlow A t = exp(−t • A)`, proves it solves `u' = −A u`
  (`hasDerivAt_heatFlow_apply`) with the energy identity `hasDerivAt_heatFlow_normSq`,
  and — for a coercive generator, `IsCoercive A μ` — the decay bound
  `norm_heatFlow_apply_le`: `‖e^{−tA} v‖ ≤ e^{−μt}‖v‖` for `t ≥ 0`, and `norm_heatFlow_le`
  in operator norm.  `isCoercive_compress` shows the SIRK compression along an isometry
  keeps the *same* constant, so `norm_heatFlow_compress_apply_le` gives the reduced model
  the same laminar rate at every reduction order.  What remains an input, not a theorem,
  is the identification of `μ` with `νk²` for a particular discretisation, and the value
  of `ν`.
* **Still open in §12:** the *numerical values* of `C` and `Dmin` (Crouzeix's inequality
  and the `e^{−hm}` deformation remain named hypotheses with citations, never axioms) and
  Gap 6 (finite precision, out of scope by design).  The standing research boundary is
  unchanged: **A1**, the continuum ESA for `□ + V` on `L²(ℝ⁸⁴)`.
* **§8 gate — re-run green in this wave** (see `BookProof/STATUS.md` for the counts).

**Status (2026-08-23f — §12 Gap 3 CLOSED (both halves); §12 Gap 2 closed for the last two
Lagrangian realizations; §8 gate re-run green).**

* **§12 Gap 3 — the Trotter/Kato half, CLOSED.**  `BookProof/ChapterSirkTrotterKato.lean`
  (namespace `BookProof.ChapterSirkTrotterKato`, `sorry`-free / `axiom`-free) proves the
  transfer for the *unbounded* self-adjoint operators of `ChapterStoneResolvent`: if the
  resolvents converge strongly, `(Aₙ − i)⁻¹ y → (A − i)⁻¹ y` for every `y`
  (`StrongResolventConvergence`), then the unitary flows converge strongly, `e^{−itAₙ}v →
  e^{−itA}v`, **uniformly for `t` in a bounded interval**
  (`trotterKato_uniform_on_interval`, `trotterKato_tendsto`, and the packaged
  `trotterKato_tendstoUniformlyOn`).  The argument is the Duhamel/commutator one:
  `resolvent_commutator_eq` (`Aₛ Rₛ − Rₛ A = (R − Rₛ)(A − i)`), the weak product rule
  `hasDerivAt_stoneU_const_sub_apply`, the Duhamel derivative `hasDerivAt_duhamel` and the
  mean-value bound `norm_res_stoneU_sub_stoneU_res_le`; then a density step
  (`exists_res_domain_approx`) extends it from the resolvent range to all of `H`, and a
  compactness step (`tendsto_uniformly_on_isCompact_of_tendsto`) makes it uniform in `t`.
  Together with the bound half of the previous wave, **Gap 3 is closed**.
* **The Galerkin instance.**  `BookProof/ChapterSirkTrotterKatoGalerkin.lean` applies the
  transfer to the Rayleigh–Ritz compressions: `ofBounded` presents a bounded self-adjoint
  operator as an `UnboundedSelfAdjoint` with full domain, `resCLM_ofBounded` identifies
  its resolvent with `−(A − i)⁻¹`, and `galerkin_flow_transfer` / `galerkin_flow_tendsto`
  conclude that the flows of the compressions converge to the flow of the selected
  generator on every bounded time interval — the last link between what the algorithm
  propagates and what the selected extension propagates.
* **§12 Gap 2 — the two remaining Lagrangian realizations.**
  `BookProof/ChapterSirkLagrangianCanonical.lean` supplies the Hashimoto/SIRK companion
  that the canonical (non-commuting ladder) realization and the Fock/momentum (continuum
  symbols) realization lacked: `lagCan_hashimoto_selects`, `lagCan_shiftInvert_selects`,
  `lagCan_sirk_crouzeix_domain`, and `fockLag_esa`, `fockLag_hashimoto_selects`,
  `fockLag_shiftInvert_selects`, `fockLag_sirk_crouzeix_domain`, `fockLag_stone_flow`.
  Every Lagrangian realization the project defines now has its selected generator, its
  Crouzeix disc of radius `|Im γ|⁻¹`, and (for the continuum one) its Stone flow.
* **Still open in §12:** the *numerical values* of `C` and `Dmin` (Crouzeix's inequality
  and the `e^{−hm}` deformation remain named hypotheses with citations, never axioms) and
  Gap 6 (finite precision, out of scope by design).  The standing research boundary is
  unchanged: **A1**, the continuum ESA for `□ + V` on `L²(ℝ⁸⁴)`.
* **§8 gate — re-run green in this wave.**  `lake build` **8702 jobs**, 0 errors;
  `lake build RandomMap` **8039 jobs**; the 25 new `#print axioms` lines of
  `BookProof/ChapterRoadmapAudit.lean` all report only `propext`, `Classical.choice`,
  `Quot.sound`; no `sorry` and no `axiom` declaration in `BookProof/`, `Book/`,
  `Singularity/`, `RandomMap/` or `PnpProof/`; `./patches/build-book.sh` renders the book
  with its assertions holding (no `<base>`, fragment links present) and
  `./patches/check-katex.sh` reports **2668 snippets, 0 failures**.

**Status (2026-08-23e — §12 Gap 2 CLOSED for the Crouzeix geometry, generically and for
every system whose selection theorem exists; the QG shift-invert constructed; §8 gate
re-run green).**

* **§12 Gap 2 — the Crouzeix domain, CLOSED.**  §12.2 Gap 2 asks for the finite-`m`
  constants "from the actual spectral geometry".  The constants `C` and `Dmin` of the
  eq.-(12) bound are only meaningful relative to a set `Σ` on which `‖ψ − r‖_{∞,Σ}` is
  measured, and `ChapterSirkEndToEnd.crouzeix_domain_transfer` had already shown that a
  single convex `Σ ⊇ W(X)` serves the full operator *and* every compression.  What was
  missing was `Σ` itself, for the operator the algorithm actually iterates — the
  shift-invert.  `BookProof/ChapterSirkSpectralGeometry.lean` (namespace
  `BookProof.ChapterSirkSpectralGeometry`, `sorry`-free / `axiom`-free) supplies it in
  the two regimes the project uses:
  * **positive generator, real shift `γ > 0`**: the shift-invert `R = (A + γ)⁻¹` is
    self-adjoint (`IsShiftInvert.isSelfAdjoint`) with `‖R‖ ≤ γ⁻¹` and nonnegative
    Rayleigh quotients (`IsShiftInvert.inner_nonneg`), so
    `numRange_subset_realSegment_of_shiftInvert` puts `W(R)` inside the **real segment**
    `realSegment 0 γ⁻¹` — a degenerate convex set, the sharpest possible domain — and
    `crouzeix_domain_shiftInvert` inherits it for `convexHull (W(V∗RV))` at every order.
  * **indefinite generator, non-real shift**: `‖X‖ ≤ |Im γ|⁻¹` gives the **disc** of that
    radius (`numRange_subset_closedBall_of_shiftInvertC`,
    `crouzeix_domain_shiftInvertC`).

  `sirk_end_to_end_crouzeix_domain` is the end-to-end bound in *domain form* — the two
  Crouzeix estimates are assumed conditionally on `W(·) ⊆ Σ`, and the compression side of
  that condition is discharged here — with the two ready-made instances
  `sirk_end_to_end_shiftInvert` and `sirk_end_to_end_shiftInvertC`.  In every case `Σ`
  depends on the **shift alone**: not on the reduction order `m`, not on the seed.
* **§12 Gap 2 — per system.**  `BookProof/ChapterSirkPerSystem.lean` instantiates the
  domain for every Hamiltonian whose selection theorem the project proves:
  `ym_sirk_crouzeix_domain` (QYM, the Friedrichs route, the segment `[0, γ⁻¹]`),
  `ns_sirk_crouzeix_domain` (NS Eulerian, sequence space) and
  `nsDiff_sirk_crouzeix_domain` (NS Eulerian, differential, on the Hermite core of
  `L²(ℝ³)`), `lagrangian_sirk_crouzeix_domain` (NS Lagrangian, abstract) with the
  concrete Kato–Rellich instance `diagKR_sirk_crouzeix_domain`, and
  `qgR2_sirk_crouzeix_domain` (QG, the gauge-fixed `R + αR²` mode Hamiltonian) — the last
  three families all on the disc of radius `|Im γ|⁻¹`, which is the formal counterpart of
  the numerics' sensitivity to how far the shift is taken from the real axis in the
  two-signed case.
* **The QG shift-invert is new.**  `qgR2_shiftInvert_selects` constructs the resolvent of
  the gauge-fixed `R + αR²` mode Hamiltonian at every non-real shift, from the
  ESA-selected extension (`Starobinsky.qgR2_stone_flow`) and
  `ChapterHashimotoComplexShifts.exists_isShiftInvertC`, with `‖X‖ ≤ |Im γ|⁻¹`.  The
  project previously had the essential self-adjointness and the Stone flow but no
  resolvent object for QG: the two-signed fiber symbol `(1/16)a² − (1/24)b²` rules out
  the positivity the real-shift route needs, and the complex-shift route needs none.
* **Book.**  `Book/SirkReliability.lean` gains two sections ("Which Region the Constants
  Are Measured On", "The Four Systems") citing the ten new results; the chapter count is
  unchanged.
* **Still open in §12:** the *numerical values* of `C` and `Dmin` on the domains fixed
  here (Crouzeix's inequality and the `e^{−hm}` deformation remain named hypotheses with
  citations, never axioms), the Trotter/Kato half of Gap 3, the rank-truncated
  (near-singular Gram) half of Gap 4c, and Gap 6 (finite precision, out of scope by
  design).  The standing research boundary is unchanged: **A1**, the continuum ESA for
  `□ + V` on `L²(ℝ⁸⁴)`.
* **§8 gate — re-run green in this wave.**  `lake build` **8697 jobs**, 0 errors; the
  17 new `#print axioms` lines of `BookProof/ChapterRoadmapAudit.lean` all report only
  `propext`, `Classical.choice`, `Quot.sound`; no `sorry` and no `axiom` declaration in
  `BookProof/`, `Book/`, `Singularity/`, `RandomMap/` or `PnpProof/`;
  `./patches/build-book.sh` renders the book with its assertions holding
  (no `<base>`, fragment links present) and `./patches/check-katex.sh` reports
  **2659 snippets, 0 failures**.

**Status (2026-08-23d — §12 Gap 1 CLOSED, together with the bound half of Gap 3 and
Gaps 4a/4b/4c and Gap 5; §8 gate re-run green).**

* **§12 Gap 1 — CLOSED (the end-to-end assembly).**
  `BookProof/ChapterSirkEndToEnd.lean` (namespace `BookProof.ChapterSirkEndToEnd`,
  `sorry`-free / `axiom`-free) is the system-independent composition §12.3 step 1 asks
  for.  The enabling observation is that the rational transfer
  `r(X)v = V r(B) V∗v` of `ChapterH8.compress_rational_transfer` is only available **on
  the range of `V`**, while `ChapterH4.sirk_error_bound` demanded it as an operator
  identity — yet its proof uses it at the seed only.  `sirk_error_bound_at` is that
  weakening, and with it **`sirk_end_to_end` carries no transfer hypothesis at all**:
  it is discharged from `V∗V = 1`, the Krylov invariance of the range and the
  invertibility of the rational denominator, giving the eq.-(12) bound
  `‖flow v − V ψ(B) V∗ v‖ ≤ 2C e^{−hm} Dmin ‖v‖` in the explicit `ChapterH6.sirkBound`
  form.  `crouzeix_domain_transfer` justifies the silent step of the informal argument —
  **one** convex Crouzeix domain `Σ ⊇ W(X)` serves both estimates, because
  `convexHull (W(V∗XV)) ⊆ Σ` (`ChapterH9.numRange_compress_subset`) — with the
  unconditional `crouzeix_domain_uniform` on the disc of radius `‖X‖`.
  `sirk_end_to_end_satisfiable` shows the hypothesis set is simultaneously satisfiable
  with a nonzero generator.
* **§12 Gap 3 — the bound half CLOSED.**  `sirk_flow_error_tendsto_zero` is the
  convergence of the reduced flows in the reduction order, and
  `sirk_flow_error_uniform_in_time` upgrades it to convergence **uniform over the time
  axis** whenever the constants can be chosen time-independently.  (The Trotter/Kato
  strong-resolvent-to-unitary-group transfer itself is still open.)
* **§12 Gap 4a — CLOSED.**  `BookProof/ChapterSirkRestart.lean`:
  `restart_error_accumulation` — two contractive propagators differing by `ε` in the
  strong sense differ by at most `n·ε` after `n` restart cycles, with no commutation
  used — plus the SIRK instance `restart_error_accumulation_sirk` and
  `restart_error_tendsto_zero`.  **§12 Gap 5 — CLOSED** by the same telescoping:
  `brst_leakage_zero_of_exact` (a propagator commuting with the BRST charge keeps a
  physical state physical) and `brst_leakage_bound`
  (`‖Ω Sⁿ v‖ ≤ ‖Ω‖ · n · ε · ‖v‖`) bound the leakage of the *truncated* dynamics out
  of the physical subspace by the truncation error; `ChapterBRSTNilpotent` supplies
  `Ω² = 0` and `[H, Ω] = 0`.  The reconstruction half is
  `ChapterSirkEndToEnd.sirkReconstruction_isIdempotent`/`_isSelfAdjoint`: `V ∘ V∗` is
  the orthogonal projection onto the retained subspace.
* **§12 Gap 4b — CLOSED.**  `BookProof/ChapterSirkMultiShift.lean`:
  `krylov_multiShift_eq_standard` — the forward sequence `w₀ = v₀`,
  `wₖ₊₁ = (H − zₖ I) wₖ` of an *arbitrary* shift schedule spans exactly
  `Kry m(H, v₀)` — hence `krylov_multiShift_span_eq_of_shifts`: the shifts change the
  basis, never the compressed space.  The general principle is
  `triangularSpan_eq_krylovSpan`, and `multiShiftSeq_const` identifies `ChapterH5`'s
  single-shift sequence as the constant-schedule instance.  The *resolvent* half is
  `BookProof/ChapterKrylovShiftSpan.lean`: `resolventSpan_eq_map_krylovSpan` identifies
  the rational Krylov space `span{v, X₀v, X₁X₀v, …}` with the image of the ordinary
  Krylov space under `X_{k−1}⋯X₀`.
* **§12 Gap 4c — CLOSED (non-degenerate case).**
  `BookProof/ChapterSirkWhitening.lean`: whitening independence in coordinate-free form.
  `rangeProj_eq_of_range_eq` (same range ⟹ same orthogonal projection), `whiteningEquiv`
  with `whiteningEquiv_isometry`/`whiteningEquiv_left_inverse` (the change of whitening
  is unitary), `compress_conj_whitening` (the two reduced operators are unitarily
  conjugate, so same spectrum, numerical range and Ritz values) and
  `sirkApprox_eq_of_range_eq` (the reconstructed operator is literally the same, `P X P`).
  The rank-truncated (near-singular Gram) quantitative case is **not** covered.
* **Book.**  `Book/SirkReliability.lean` is the pedagogical chapter citing all four
  modules.  It is `{include}`d in `Book.lean`, and so are the three chapters of the
  previous waves that had been imported but never included (`Book/Starobinsky.lean`,
  `Book/NavierStokesHashimoto.lean`, `Book/CarlemanFlux.lean`): the root `#doc` now
  carries **39 `{include}`s / 40 chapter files** (`Issues.md` §0b updated).
* **Still open in §12:** Gap 2 (the per-system constants, all four Hamiltonians), the
  Trotter/Kato half of Gap 3, the rank-truncated half of Gap 4c, and Gap 6 (finite
  precision, out of scope by design).  Crouzeix's inequality and the
  `e^{−hm}` deformation remain named hypotheses with citations, never axioms.
* **§8 gate — re-run green in this wave.**  `lake build` **8695 jobs**,
  `lake build RandomMap` **8039 jobs**, `lake build UsedRoute` **8049 jobs**, all with
  0 errors; every `#print axioms` line of `BookProof/ChapterRoadmapAudit.lean` reports
  only `propext`, `Classical.choice`, `Quot.sound`; no `sorry` and no `axiom`
  declaration in `BookProof/`, `Book/`, `Singularity/`, `RandomMap/` or `PnpProof/`
  (the quarantined legacy `UsedRoute/`/`UnusedRoute/` sorries are unchanged and in no
  default target); the isolation greps are empty; `./patches/build-book.sh` renders
  the book with its assertions holding and `./patches/check-katex.sh` reports
  **2652 snippets, 0 failures**.  Note: the `patches/*.sh` executable bits had again
  been lost in this snapshot and have been restored (and re-staged as mode `100755`).

**Status (2026-08-23c — A5 step 2 CLOSED: the conformal-mode potential after the
densitized change of variables; §8 gate re-run green).**

* **A5 step 2 — CLOSED.**  `BookProof/ChapterScalaronDensitizedTransfer.lean`
  (namespace `BookProof.ScalaronDensitized`, `sorry`-free / `axiom`-free) carries the
  `R + αR²` conformal-mode potential bound through the densitized change of variables
  `e = y²`, in the continuum realisation.  `densConfV M α y = V₃(y²)` is the pullback of
  `V₃` along `y = √e` (`densConfV_comp_densY`); **the bound survives**
  (`densConfV_ge`, `densConfV_bddBelow`: `−M⁴/(16α) ≤ densConfV M α y`), and
  `densConfV_zero_alpha_tendsto_atBot` shows it is bought by the `αR²` term and not by
  the densitization.  The half-density unitary of
  `ChapterQuantumGravityHalfDensity` carries the bounded-energy core of
  `L²((0,∞), de)` onto that of `L²((0,∞), 2y dy)` and intertwines the two
  multiplication Hamiltonians (`halfDensityUnitary_mem_densConfCore`,
  `halfDensityUnitary_densConfCore_surjective`, `halfDensityUnitary_intertwines`), so
  `qg_halfDensity_transfer` turns `densConf_hasZeroDeficiencyOn` into
  **`physConf_hasZeroDeficiencyOn_transfer`** — the physical statement obtained by
  transfer — with the Stone flows on both sides (`densConf_stone_flow`,
  `physConf_stone_flow`).  At the operator level `multOp_quadForm_eq` /
  `multOp_quadForm_ge` turn a pointwise lower bound on a multiplier into semiboundedness
  of the multiplication operator, giving `densConfOp_quadForm_ge` and
  `physConfOp_quadForm_ge`.  Honest boundary: this is the potential half in the one
  conformal variable; the full continuum `L²(ℝ⁸⁴)` statement still needs the Strichartz
  finite-speed / direct-integral input, which is the standing residue of A1.

**Remaining research boundary: A1 (the QG continuum ESA with a general Faris–Lavine
potential — equivalently the Strichartz finite-speed / hyperbolic direct-integral
gluing), which is also the standing residue of the A5 continuum assembly.**
*Update (2026-08-24, user clarification): for the physical QG potential of the
`R²` action this is moot — in densitized variables the potential is bounded below
and well-defined on the Hermite core, so no ESA for an unbounded-below-and-above
potential is needed; the semibounded (Friedrichs) realization suffices and is done.
A1 now concerns only the abstract general Faris–Lavine class.*

**Status (2026-08-23b — A4 CLOSED: the two Faris–Lavine inequalities for the
*differential* Navier–Stokes symbol; §8 gate re-run green).**

* **A4 — CLOSED.**  `BookProof/ChapterNavierStokesDiffFarisLavine.lean` (namespace
  `BookProof.NavierStokesFlow.DiffFarisLavine`, `sorry`-free / `axiom`-free) proves
  the two Faris–Lavine inequalities for the Navier–Stokes quadratic symbol **as an
  actual differential operator** on `L²(du₁du₂du₃)`, against a *differential*
  comparison operator `nsDiffN μ = 2μ ∑ᵢ (πᵢ² + uᵢ²/4) + 1`.  The bridge is the
  polynomial identity `oscPoly_eq` / `oscOp_eq_number` — on the Gauss–polynomial
  core, `πᵢ² + uᵢ²/4 = aᵢ†aᵢ + ½` — together with `embedCore_surjective`, which says
  that core *is* the transported finite-mode core; hence `intertwined_nsDiffN` /
  `velNcore_eq_diagMax`.  Payoffs: `nsDiffN_symmetricOn`,
  `nsDiffN_quadForm_ge_norm_sq`, **`nsDiffH_relative_bound`**
  (`‖Hf‖² ≤ a‖Nf‖² + b‖f‖²`), **`nsDiffH_commForm_bound`**
  (`|⟪f, i[H,N]f⟫| ≤ c⟪f, Nf⟫`), the maximal-domain layer (`diffMaxDom`, `diffMaxN`,
  `diffMaxH`, `diffMaxH_symmetricOn`, `diffMaxN_quadForm_nonneg`,
  `diffMaxN_add_one_surjective`, `diffMaxN_core_approx`, `diffMaxH_relative_bound`,
  `diffMaxH_commForm_bound`, `diffMaxH_restrict`) and the headline
  **`nsDiffH_esa_of_farisLavine`** — essential self-adjointness obtained from the
  Faris–Lavine criterion applied *in `L²(ℝ³)` itself*, the alternative route to
  `ChapterNavierStokesDifferentialL2.nsDiffH_essentiallySelfAdjointOn_core`.
  Registered in `BookProof.lean`, certified in `ChapterRoadmapAudit.lean` (19 new
  `#print axioms`), recorded in `BookProof/STATUS.md`, cited from
  `Book/FreeField.lean`.  Honest boundary unchanged (Contention D5): nothing here
  claims global regularity of the classical Navier–Stokes equation.
* **§8 gate — re-run green in this wave**, including the previous wave's merged
  state (`lake build`, `lake build RandomMap`, `lake build UsedRoute`,
  `./patches/build-book.sh`, `./patches/check-katex.sh`, and the `sorry` / `axiom` /
  isolation greps).

**Remaining research boundaries: A1 (the QG continuum ESA with a general
Faris–Lavine potential / hyperbolic direct integral) and the continuum densitized
change of variables of A5 step 2** — the latter closed in the 2026-08-23c wave above.

**Status (2026-08-23 — Aristotle wave: the scalaron strand lands at the continuum
and Fock levels; the Book gains three pedagogical chapters citing the new proofs).**
This wave merges the Aristotle output for the Starobinsky/scalaron strand (plan
item **A5**) and the pedagogical Book updates that cite it:

* **A5 — the continuum core step is now CLOSED.**
  `BookProof/ChapterScalaronCoreEsa.lean` (namespace `BookProof.ScalaronEsa`)
  removes the temperate-growth restriction that left the continuum Starobinsky
  potential open at 2026-08-22f: on the dense core of smooth compactly supported
  functions no growth hypothesis is needed at all.  Multiplication by any smooth
  real potential is symmetric with trivial deficiency at every non-real point
  (`smoothPotential_symmetric`, `smoothPotential_deficiencyTrivial`,
  `smoothPotential_essentiallySelfAdjoint`); the Einstein-frame scalaron potential
  is smooth (`contDiff_starobinskyV`) and `starobinskyV_not_hasTemperateGrowth`
  records why the earlier theorem did not apply; the combination with the kinetic
  term (wave + truncated scalaron) is essentially self-adjoint by the finite-speed
  argument (`wave_add_scalaronTruncated_esa`, `wave_add_scalaron_esa_of_finiteSpeed`)
  with the complete unitary flow (`qgScalaron_stone_flow`).
* **A5 — the Fock step is CLOSED (2026-08-22h).**
  `BookProof/ChapterScalaronFockEsa.lean` (namespace `BookProof.ScalaronFock`)
  links `ScalaronCoreEsa` with `ChapterDirectSumEsa`: essential self-adjointness is
  fibrewise, so the one-particle theorems glue to the nested Fock space
  `⊕ₙ L²(Eₙ)`.  The many-body gauge-fixed potential `∑ⱼ(V₃(R_cⱼ) + V(φⱼ))` is
  smooth (`contDiff_qgManyPotential`), bounded below by `−n·M⁴/(16α)`
  (`qgManyPotential_ge`), equal to the one-particle potential at `n = 1`
  (`qgManyPotential_one`), and the second-quantised scalaron Hamiltonian is
  essentially self-adjoint with the full unitary group `e^{−itH}`
  (`qgScalaronFock_esa`, `qgScalaronFock_stone_flow`; mode realisation
  `qgScalaronModeFock_*`).
* **Book — three pedagogical chapters added.**  `Book/Starobinsky.lean` (the
  scalaron: ghost-free scalar–tensor form, the square potential, conformal-mode
  regularization, continuum ESA, Fock statement), `Book/NavierStokesHashimoto.lean`
  (the shift-invert selection theorem for the differential Navier–Stokes
  generator) and `Book/CarlemanFlux.lean` (the general-hop flux criterion), all
  imported by `Book.lean` and citing the new proofs with `#check` blocks.  This
  also completes the item-5 pedagogical note below (`ChapterCarlemanGeneralHop`
  now has its book citation).
* **§8 gate — NOT re-run in this wave (by instruction).**  The project was
  updated but **not compiled**; the Lean 4 specialist must re-run the gate, verify
  the new modules and the three new Book chapters build, and confirm the new
  `#check` citations resolve against the namespaces `BookProof.Starobinsky`,
  `BookProof.ScalaronEsa`, `BookProof.ScalaronFock`, `BookProof.NavierStokesFlow`,
  `BookProof.CarlemanGeneralHop`.

**Remaining research boundaries after this wave:** A1 (general Faris–Lavine
potential / hyperbolic direct integral); A4 (the alternative FL-estimate route on
the NS differential symbol) was closed in the 2026-08-23b wave above; A5 is now closed at the mode, continuum-core and
Fock levels, with only the §8-gate confirmation of the merged state outstanding.
The `ChapterRoadmapAudit` certificate sweep (import-everything + `#print axioms`)
now covers the whole merged library.

**Status (2026-08-22f — A6 closed, `ChapterCarlemanGeneralHop` registered, the
Starobinsky potentials landed, §8 gate re-run green).**  This wave resolves the
three actionable items flagged in the 2026-08-22d block below:

* **A6 — CLOSED.**  `BookProof/ChapterNavierStokesDiffHashimoto.lean` (namespace
  `BookProof.NavierStokesFlow.DiffHashimoto`) proves
  **`nsDiffH_hashimoto_selects`** on the *differential* realization on
  `L²(du₁du₂du₃)`.  The missing ingredient was symmetry of the differential
  operator on its own Gauss–polynomial core: `nsDiffPoly` writes the Weyl-ordered
  `∑ᵢ ½(πᵢVᵢ + Vᵢπᵢ)` at the polynomial level, `nsDiffPoly_polySym` proves it Gauss
  symmetric, and `nsDiffH_eq_coreOp` identifies its transport with `nsDiffH`.  With
  the already-proved ESA this gives `nsDiffH_selfAdjoint_extension(_unique)` and then
  `EsaClosure.hashimoto_multishift_selects_esa` instantiates to the headline; also
  `nsDiffH_shiftInvert_selects`, `nsQuadraticDiffH_hashimoto_selects`, and
  `exists_l2dHilbertBasisNat` / `exists_hermiteEnum` for non-vacuity.  Cited from
  `Book/FreeField.lean`.  Honest boundary unchanged (Contention D5).
* **`ChapterCarlemanGeneralHop` — REGISTERED.**  Repaired for the Mathlib revision
  pinned in this repository (an `abs_sub` implicit-argument name, two `Finset.mem_coe`
  coercions, one sum-splitting rewrite), imported by `BookProof.lean`, certified in
  `ChapterRoadmapAudit.lean` (`hshift_hshift`, `sum_ltG`, `sum_hop_im`,
  `flux_bound_gen`, `flux_identityH`, `ladderH_eq_zero`) and recorded in
  `BookProof/STATUS.md`.
* **A5 — steps 1 and, at the mode level, 3/4 landed.**
  `BookProof/ChapterStarobinskyPotential.lean` (namespace `BookProof.Starobinsky`):
  `fR_eq_scalarTensor` is the ghost-free scalar–tensor identity
  `f(R) = (M²/2)ψR − U(ψ)`; `starobinskyV_nonneg`, `starobinskyV_zero`,
  `starobinskyV_tendsto_plateau`, `starobinskyV_tendsto_atBot_atTop` are the
  Einstein-frame scalaron potential's sign, vacuum, plateau and wall;
  `confV_completed_square`, `confV_ge`, `confV_bddBelow` are the conformal-mode bound
  `V₃ ≥ −M⁴/(16α)` and `confV_zero_alpha_tendsto_atBot` the `α = 0` (pure GR)
  unbounded case; and at the operator level `qgR2Mode_potential_ge`,
  `mulSymbolDomain_dense`, `qgR2Mode_symmetric`, `qgR2Mode_esa`,
  `qgR2Mode_deficiencyTrivialAt` and the deliverable **`qgR2_stone_flow`**.  Cited from
  `Book/DiffeomorphismsGravity.lean`.  **Still open in A5:** step 2 — carrying the
  potential bound through the densitized change of variables in the *continuum*
  `L²(ℝ⁸⁴)` setting, which is the same Strichartz finite-speed / direct-integral
  residue as A1.  What is proved above is the mode (Hermite-basis) realization, where
  the fiber operator is a multiplication operator.
* **§8 gate — RE-RUN GREEN (2026-08-22f).**  `lake build` **8683 jobs** (BookProof +
  Book + Singularity), `lake build RandomMap` **8039 jobs**, `lake build UsedRoute`
  **8049 jobs**, all with 0 errors; every `#print axioms` line in
  `BookProof/ChapterRoadmapAudit.lean` reports only `propext`, `Classical.choice`,
  `Quot.sound` (no `sorryAx`); no `sorry` and no `^axiom` in `BookProof/`, `Book/`,
  `Singularity/`, `RandomMap/` or `PnpProof/` (the quarantined legacy
  `UnusedRoute/*.lean` sorries are unchanged and expected).  `./patches/build-book.sh`
  and `./patches/check-katex.sh` re-run: see the B1 entry in §9 for the recorded
  figures.

**Remaining research boundaries after this wave:** A1 (general Faris–Lavine
potential / hyperbolic direct integral), A4 (the alternative FL-estimate route on
the NS differential symbol), and A5 step 2 as scoped above.

**Status (2026-08-22d, merged from the Aristotle output — the quadratic strand is
closed at *all* mode counts, and the gluing half of the direct-integral step is
landed).**  This merge adds **22 new `sorry`-free / `axiom`-free `BookProof`
modules** — **21 of them registered** in `BookProof.lean`, certified in
`BookProof/ChapterRoadmapAudit.lean`, and cited pedagogically from the book, plus
one complete *leaf* module (`ChapterCarlemanGeneralHop`) that is not yet
registered (flagged below):

* **The finite-dimensional quadratic strand is closed entirely (2026-08-22/22b).**
  The Carleman flux argument on the Hermite lattice
  (`ChapterHermiteCarlemanEsa`, `ChapterCarlemanTwoStep`, `ChapterModeQuadraticEsa`,
  `ChapterCarlemanSimplex`) replaces the relative-bound / completed-square routes:
  *every* real quadratic-plus-linear Hamiltonian in `d` degrees of freedom —
  `∑_{i,j}(Pᵢⱼπᵢπⱼ + Qᵢⱼxᵢxⱼ + Sᵢⱼ·½(xᵢπⱼ + πⱼxᵢ)) + ∑ᵢ(bᵢxᵢ + b'ᵢπᵢ)`, arbitrary real
  matrices and vectors, no ellipticity, no definiteness, no non-degeneracy, no
  classical equilibrium — is essentially self-adjoint on the plain
  Gauss–polynomial core (`ChapterFullQuadraticEsa.fqOp_essentiallySelfAdjoint`),
  with the dilation and angular-momentum generators as corollaries.
* **The infinite-mode strand (2026-08-22c).**  `ChapterOperatorSeriesEsa` (the two
  Faris–Lavine inequalities are additive; a summable family of symmetric operators
  sums to an essentially self-adjoint one) + `ChapterFockQuadraticEsa`: the
  second-quantized Hamiltonian `∑ᵢ ωᵢaᵢ†aᵢ + ∑ₖ(gₖa^{†Pₖ}a^{Qₖ} + conj(gₖ)a^{†Qₖ}a^{Pₖ})`
  on the boson Fock space `ℓ²(ι →₀ ℕ)` over an arbitrary mode set is essentially
  self-adjoint on the finite-particle core under the weighted summability
  `∑ₖ‖gₖ‖(ω(Pₖ)+ω(Qₖ)+2) < ∞` (Bogoliubov pair creation included).
* **The gluing half of the direct-integral step (2026-08-22d).**
  `ChapterDirectSumEsa`: essential self-adjointness passes from the fibres of an
  orthogonal direct sum to the whole space (`dsOp_essentiallySelfAdjointOn`), with
  the payoff that the continuum parcel Hamiltonian `ĥ = ∫ w(ξ)a†(ξ)a(ξ)dξ` is
  essentially self-adjoint on the *whole* Fock space `⊕ₙ L²(ℝⁿ)` for an arbitrary
  measurable field `w` (`fockH_hasZeroDeficiencyOn`, `fockH_stone_flow`).
* **The supporting instruments (2026-08-21g/21h/21i).**  `ChapterUnboundedSpectralModel`
  closes backlog item **A2** (the spectral theorem in multiplication form for
  unbounded self-adjoint operators, via the Cayley/resolvent route);
  `ChapterFourierMultiplierEsa`, `ChapterMixedLinearEsa`, `ChapterQuadratureEsa`
  close the first-order residue of the quadratic family; `ChapterStoneEigenflow`
  makes the dynamics explicit on the eigenbasis (`U t ψ = e^{−iλt}ψ`).

**What remains open** (unchanged research boundaries, now sharply scoped):

* **A1 (the single genuinely open analytic target):** the QG *continuum* ESA with a
  *general* Faris–Lavine potential — `□ + V` with `V` bounded above by a quadratic
  but not itself a quadratic.  The diagonal-quadratic, rotated, shifted, singular,
  mode-diagonal, fully coupled and infinitely-many-mode cases are all closed; the
  fibrewise / direct-integral step that would pass ESA to the general such `V` is
  not, and the new `ChapterDirectSumEsa` gluing is orthogonal only.  **Update
  (2026-08-24, user clarification):** this open target is not needed for the
  physical QG potential of the `R²` action.  In *densitized* variables that
  potential is **bounded below** (conformal-mode parabola `≥ −M⁴/(16α)`, scalaron
  `V(φ) ≥ 0`) and is **well-defined on the Hermite core** — for the inner
  Fock-space's one-particle sector and for the one-particle state in the outer
  Fock-space — so **no ESA for an unbounded-below-and-above potential** is
  required; the semibounded (Friedrichs) realization that the physical case needs
  is already done (`qgOneParticleSector_friedrichs`,
  `ChapterQgHermiteFriedrichs`).
* **A4 — CLOSED (2026-08-23b).**  The alternative Faris–Lavine-estimate route for
  the Navier–Stokes quadratic symbol as an actual differential operator is proved in
  `BookProof/ChapterNavierStokesDiffFarisLavine.lean`
  (`nsDiffH_relative_bound`, `nsDiffH_commForm_bound`, `nsDiffH_esa_of_farisLavine`).
* **A5 (new plan item, §10.5):** ESA and the **continuous flow** of the
  R + αR² (Starobinsky) gauge-fixed Hamiltonian, derived in
  `../unfer/docs/qg_starobinsky_hamiltonian.cdb` — the αR² term makes the
  conformal-mode potential bounded below (`V3 ≥ −M⁴/(16α)`) and the scalaron
  potential non-negative (`V(φ) ≥ 0`), the correct bound for ESA after the
  densitized change of variables; deliverable `qgR2_stone_flow`.
* **A6 (new plan item, §9):** the **Hashimoto/SIRK selection on the NS
  differential realization** — `nsDiffH_essentiallySelfAdjointOn_core` on
  `L²(du₁du₂du₃)` is ESA but has no Hashimoto theorem (only the abstract
  `ℓ²(Vel)` layer has `ns_hashimoto_selects`); deliverable `nsDiffH_hashimoto_selects`
  via the `velUnitary` transport or the product-Hermite basis.
* **New flag for the specialist:** `BookProof/ChapterCarlemanGeneralHop.lean` (633
  lines, namespace `BookProof.CarlemanGeneralHop`, built on `ChapterCarlemanTwoStep`
  — a Carleman criterion for general lattice hops, including the non-monotone
  `α ↦ α ± (eᵢ − eⱼ)`) is a complete *leaf* module in this merge but is **not yet
  registered** in `BookProof.lean`, `ChapterRoadmapAudit.lean` or
  `BookProof/STATUS.md`.  First task: verify it compiles (`lake build`), register
  it, add its `#print axioms` to the audit and its wave entry to `STATUS.md`, and
  (optionally) cite it from `Book/DiffeomorphismsGravity.lean`.
* **Gate:** the §8 gate was last recorded green at 2026-08-22d in the Aristotle
  snapshot; re-run `lake build`, the book wrapper and the audits after this merge.

**Status (2026-08-21, consolidated: all named §9 plan items are closed; the
remaining work is the recorded research boundaries).** This snapshot closes the
last realization-layer gaps of the Navier–Stokes thread and reaches *parity of
realization* across the Eulerian and Lagrangian variable pictures:

* **§9 item 4 (NS differential realization) — CLOSED (2026-08-20k).** The full
  quadratic symbol `A_i = u_j u_{i,j} − ν u_{i,jj}` is essentially self-adjoint on
  the Hermite core of `L²(du₁du₂du₃)` (`ChapterHermiteProductBasis.lean` +
  `ChapterNavierStokesDifferentialL2.lean`: `velUnitary ≃ L²(ℝ³)`, `momOp = −i∂/∂uᵢ`,
  `[πᵢ,u_k] = −iδ_{ik}`, `nsDiffH_essentiallySelfAdjointOn_core`,
  `nsQuadraticDiffH_essentiallySelfAdjointOn_core`).
* **§9 item 11 (Lagrangian/Eulerian parity) — CLOSED (2026-08-20j).** The
  canonical/ladder realization of the Lagrangian second-order part on the
  trajectory-space Hermite basis (`ChapterNavierStokesLagrangianCanonical.lean`:
  `lagQ`/`lagP`, `comm_lagP_lagQ`, `T = ½ΣPᵢ² + νΣQᵢ² = ω(N+3/2)`,
  `lagCan_esa`, `lagCan_stone_flow`).
* **§9 items 8/9 and the general Stone theorem — CLOSED (2026-08-20d/20e/20i).**
  The ESA-closure + Hashimoto/SIRK selection, the Lagrangian Kato–Rellich route,
  and the complete unitary flows via `ChapterStoneResolvent`–`ChapterStoneSeparable`
  + `ChapterStoneBridge`/`ChapterStoneFlows`.
* **Quadratic-Hamiltonian ESA — extended to the indefinite inhomogeneous case
  (2026-08-21e).**  `ChapterShiftedHermiteCore.lean` +
  `ChapterShiftedQuadraticEsa.lean`: for diagonal weights `cᵢ ≠ 0` of *arbitrary
  sign* and arbitrary real `b, b'`, `∑ᵢ (cᵢ(πᵢ² + xᵢ²/4) + bᵢxᵢ + b'ᵢπᵢ)` is
  symmetric and essentially self-adjoint on the translated, modulated
  Gauss–polynomial core (`shiftedHOp_essentiallySelfAdjoint`), by completing the
  square rather than by a relative bound.  See the A1 backlog entry.
* **Quadratic-Hamiltonian ESA — extended to cross terms and to *singular* forms,
  and the dynamics made explicit (2026-08-21f/21g).**
  `ChapterShiftedQuadraticMatrixEsa.lean` removes the diagonality restriction of
  the wave above (every real symmetric *invertible* `A` of arbitrary signature);
  `ChapterShiftedQuadraticDegenerate.lean` then removes invertibility itself: the
  classical equilibrium equations `A a = −2b`, `A k = −b'/2` are solvable exactly
  when `b, b' ⊥ ker A` (`exists_equilibrium_iff`), and under that condition
  `H_A + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)` is symmetric and essentially self-adjoint on the
  translated, modulated core for **every** real symmetric `A`
  (`shiftedHMatOp_essentiallySelfAdjoint_of_equilibrium`,
  `exists_shiftedHMat_esa_of_kernel_orthogonal`).
  `ChapterStoneEigenflow.lean` turns Stone's existence statement into explicit
  dynamics: any unitary flow of a self-adjoint `T` acts on an eigenvector by the
  phase `e^{−iλt}` (`stoneFlow_apply_eigenvector`), so the Schrödinger equation for
  the whole quadratic family is solved in closed form on the Hermite eigenbasis
  (`exists_diagonal_stone_flow`, `exists_shiftedHMat_diagonal_flow`,
  `exists_shiftedH_diagonal_flow`).  `ChapterFourierMultiplierEsa.lean` extracts the
  Plancherel argument as an instrument (`essentiallySelfAdjointOn_of_real_symbol`) and
  covers the *first-order* operators the second-order family could not reach
  (`firstOrderOp_essentiallySelfAdjoint`, `mixedOp_essentiallySelfAdjoint`).  See the A1
  backlog entry.
* **GAP-1 / GAP-2 — CLOSED.** The §4 hygiene items are landed; the two documented
  gaps are closed in `BookProof/STATUS.md`.

**What is now NOT a plan item** (recorded boundaries / closed items, each with
its own entry below).  Closed: the *continuum Laplacian* ESA and the *fibrewise*
ESA of the continuum Navier–Stokes operator.  Genuinely open (scope cuts /
research targets): the *classical* Navier–Stokes regularity question (Contention
D5), the QG / NS mass gaps (author's decision), and — the single genuinely open
analytic step — the **QG continuum ESA with an unbounded potential**:
* **NS fibrewise / continuum ESA (closed).** `ChapterNavierStokesFockContinuum`
  proves essential self-adjointness in the genuinely continuum situation: the
  one-parcel operator is multiplication by a real field `w` on the parcel domain,
  so it has **continuous spectrum** and no eigenvectors.  `multOp_hasZeroDeficiencyOn`
  is the headline — multiplication by an arbitrary real measurable function is
  essentially self-adjoint on the bounded-energy core — and
  `sectorHamiltonian_hasZeroDeficiencyOn` applies it to the second-quantized
  `ĥ = ∫ w(ξ)a†(ξ)a(ξ)dξ` on the `n`-parcel sector `L²(Ωⁿ)`.  The NS continuum
  fibrewise step is therefore done.
* **QG continuum ESA with an unbounded potential (OPEN).** The QG Hamiltonian's
  fibrewise / continuum ESA is **not** closed, because the potential is
  unbounded.  `ChapterWaveUnboundedPotential` proves the *position-space half*
  (`potentialOp_essentiallySelfAdjoint` for temperate-growth potentials,
  `multiplierOp_essentiallySelfAdjoint`, and the truncations
  `wave_add_truncatedPotential_essentiallySelfAdjoint`), and the sign-correct
  `-d²/dx² + x²/4` oscillator is `ChapterHarmonicOscillatorEsa`; but the
  *hyperbolic fibrewise / direct-integral* step that would pass ESA to the full
  `□ + V` with `V` bounded above by a quadratic (the `-d²/dx² − x⁴` sign record,
  §9.5, the Faris–Lavine class) remains **unproved for a general such `V`**.
  **Update (2026-08-21):** the *diagonal-quadratic* case of that mixture is now
  closed — `ChapterHyperbolicQuadraticEsa` proves that
  `H_c = ∑ᵢ cᵢ(−∂ᵢ² + xᵢ²/4)` is essentially self-adjoint on the product-Hermite
  core of `L²(ℝᵈ)` for *every* real weight vector `c`, hyperbolic signatures
  included, together with the pointwise identification of the differential
  expression; with the Minkowski weights this is `□ + V`,
  `V(t,x) = (t² − ‖x‖²)/4`, the sign-correct indefinite quadratic potential.
  **Update (2026-08-21c/d):** the *diagonality* restriction is gone as well.
  `ChapterQuadraticRotationEsa` proves that for **every** real symmetric matrix `A`
  the operator `H_A = ∑_{k,l} A_{kl}(π_k π_l + x_k x_l/4)` — arbitrary signature, no
  sign condition — is symmetric and essentially self-adjoint on the same core, via
  the orthogonal substitution and the spectral theorem for real symmetric matrices;
  and `ChapterQuadraticRotationPerturbed` upgrades that substitution to an honest
  unitary of `L²(ℝᵈ)` and adds an arbitrary unbounded *first-order* term, giving the
  general **inhomogeneous elliptic** quadratic Hamiltonian
  `H_A + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)` for positive definite `A`.  What is still open is the
  general Faris–Lavine potential (the joint eigenbasis used here exists only for the
  quadratic family), and that is the remaining open analytic research target.
  **Update (2026-08-24, user clarification):** the open general Faris–Lavine
  target is **not needed for the physical QG potential of the `R²` action**.  In
  *densitized* variables that potential is **bounded below** (conformal-mode
  parabola `≥ −M⁴/(16α)`, scalaron `V(φ) ≥ 0`) and is **well-defined on the
  Hermite core** — for the inner Fock-space's one-particle sector and for the
  one-particle state in the outer Fock-space — so **no ESA for an
  unbounded-below-and-above potential** is required.  The semibounded (Friedrichs)
  realization that the physical case needs is already done
  (`qgOneParticleSector_friedrichs`, `ChapterQgHermiteFriedrichs`); A1 therefore
  reduces to the *abstract* question of the general Faris–Lavine class, decoupled
  from the QG potential itself.
* **Stone's theorem applied to the continuum Laplacian (closed).** The concrete
  ESA step is `constCoeffOp_essentiallySelfAdjoint`
  (`BookProof/ChapterStrichartzWave.lean`), whose real quadratic symbol covers the
  continuum Laplacian (`c = (1,…,1)`), and the general
  `polyharmonic_multiplier_essentiallySelfAdjoint` / `multiplierOp_essentiallySelfAdjoint`.
  ESA on the Schwartz core gives the complete unitary flow by the general Stone
  theorem (`ChapterStoneResolvent`–`ChapterStoneSeparable`).

**Work available for the Lean 4 specialist.** All *named* plan items are closed;
the backlog below is the recorded research boundaries and editorial residue.  It
is prioritized (the full, detailed write-up is the consolidated section at the
end of §9; each item points to the module / plan section where it is recorded):

1. **Re-run the §8 verification gate for the merged Aristotle wave — OUTSTANDING in
   this repository (highest priority).**  The gate was verified green in the
   *producing* workspaces (last recorded 2026-08-21, and per-wave re-runs through
   2026-08-24d in the source), and the historical all-targets record stands; but
   the Aristotle SIRK / QG Hermite / Friedrichs / Fermion-Fock wave (26 new
   `BookProof` modules + 4 new Book chapters) was merged into this repository
   **without compiling**.  The specialist must, in order: `lake build`, `lake
   build RandomMap`, `lake build UsedRoute`, `./patches/build-book.sh`,
   `./patches/check-katex.sh` (book + KaTeX asserts), then the sorry/axiom audit
   (expect only the 43 quarantined `UsedRoute/`/`UnusedRoute/` sorries) and the
   isolation greps, and confirm the new modules build and the four new Book
   chapters' `#check` citations resolve.  See item B1 at the end of §9 and the
   leading 2026-08-24 merge status block.
2. **Close the QG continuum ESA with an unbounded potential** (research target) —
   the hyperbolic fibrewise / direct-integral step for `□ + V` with `V` bounded
   above by a quadratic (§9.5, the Faris–Lavine class; the `-d²/dx² − x⁴` sign
   record).  The NS fibrewise / continuum ESA is done
   (`ChapterNavierStokesFockContinuum`), and the **diagonal-quadratic** case of the
   QG mixture is now done too (`ChapterHyperbolicQuadraticEsa`, 2026-08-21); what
   remains is the general potential bounded above by a quadratic.  **Update
   (2026-08-24, user clarification):** for the physical QG potential of the `R²`
   action this target is moot — in *densitized* variables that potential is
   **bounded below** (the conformal-mode parabola is `≥ −M⁴/(16α)`) and is
   **well-defined on the Hermite core** for the inner Fock-space's one-particle
   sector and for the one-particle state in the outer Fock-space, so no ESA for an
   *unbounded-below-and-above* potential is needed.  What the physical case needs
   is only the semibounded (Friedrichs) realization, which is already done
   (`qgOneParticleSector_friedrichs`, `ChapterQgHermiteFriedrichs`).
3. **Prove the spectral theorem for unbounded self-adjoint operators** (research
   target) — the *existence* of the diagonalizing unitary.  `ChapterUnitaryTransport`
   and `ChapterSpectralMultiplication` carry the reduction *given* such a unitary;
   the existence step itself is the open layer (see §9 item 3 and
   `ChapterUnitaryTransport` module docstring).
4. **Formalize the NS sign-flip unitary** `x_n ↦ (−1)ⁿ x_n` to drop the `c_j ≥ 0`
   restriction in the affine-block ESA (`ChapterNavierStokesAffineBlockEsa`, §9
   item 4 boundary).
5. **Editorial / prose residue** (small, one-line edits): Contention **D1**
   (intro-slogan internal tension) and **D2** (ODE overclaim honesty sentence);
   re-mark the curated-edition coverage table (Issues §5 item 2, the "deferred"
   physics-chapters list); restate remaining long `#check` types as clean
   `example`s.
6. **Keep the Book ↔ BookProof one-to-one correspondence** on any edit (the
   `#check` blocks in `Book/` must stay in sync with the module names in
   `BookProof/`).

**Status (2026-08-20k, the differential realization of the full Navier–Stokes
quadratic symbol on `L²(du₁du₂du₃)`):** the last named plan item, §9 item 4, is
now closed by two `sorry`-free / `axiom`-free modules, registered in
`BookProof.lean`, `#print axioms`-certified in `BookProof/ChapterRoadmapAudit.lean`
and cited from `Book/FreeField.lean`:

* **`BookProof/ChapterHermiteProductBasis.lean`** (namespace
  `BookProof.HermiteProductBasis`) builds the product Hermite orthonormal basis of
  `L²(ℝᵈ)`: the normalized Gauss–polynomial functions `hermiteMvLp`, their
  orthonormality (`orthonormal_hermiteMvLp`, by Fubini from the 1-D
  `hermiteInner_eq`), the identification of their span with the Gauss–polynomial
  core (`span_hermiteMvLp`), the Hilbert basis `hermiteMvBasis`, the partial
  derivative `pderiv_hermiteMv` (`∂ᵢHe_α = αᵢHe_{α−eᵢ}`) and the ladder actions
  `crePoly_hermiteMvLp` (`a†ψ_α = √(αᵢ+1)ψ_{α+eᵢ}`) and `annPoly_hermiteMvLp`
  (`aψ_α = √αᵢ ψ_{α−eᵢ}`).
* **`BookProof/ChapterNavierStokesDifferentialL2.lean`** (namespace
  `BookProof.NavierStokesFlow.DifferentialL2`) is the differential realization
  itself.  `posOp i` is multiplication by the coordinate `uᵢ`
  (`posOp_apply_eq_mul`) and `momOp i` is `πᵢ = −i ∂/∂uᵢ`: the analytic lemma
  `hasDerivAt_pgFun_sec` differentiates `p(u)e^{−‖u‖²/4}` along one coordinate, and
  `momOp_apply_eq_differential` states that the value of `momOp i` at that function
  is pointwise `−i` times Mathlib's `deriv` along the `i`-th coordinate.
  `comm_momOp_posOp` is the CCR `[πᵢ, u_k] = −i δ_{ik}` for these genuinely
  differential operators.  The transport is `velUnitary : ℓ²(Vel) ≃ₗᵢ L²(ℝ³)`,
  the Hilbert-basis isomorphism given by the product Hermite functions indexed by
  the three-mode multi-indices (`velBasis`); it carries the finite-mode core onto
  the Gauss–polynomial core (`velUnitary_mem_core`, `embedCore`) and the abstract
  ladder operators onto the differential ones (`intertwine_ann`, `intertwine_cre`),
  hence the canonical pairs (`intertwined_pos`, `intertwined_mom`) and the
  canonical Hamiltonian onto the differentially written one (`intertwined_canH`).
* **The conclusions.** `nsDiffH_essentiallySelfAdjointOn_core`: for every real
  velocity gradient `A` and every real constant part `c`, the Weyl-ordered
  `∑ᵢ ½(πᵢVᵢ + Vᵢπᵢ)` with `πᵢ = −i ∂/∂uᵢ` and `Vᵢ` multiplication by
  `∑ₖ A_{ik}uₖ + cᵢ` is essentially self-adjoint on the Hermite core of
  `L²(du₁du₂du₃)`.  `nsQuadraticDiffH_essentiallySelfAdjointOn_core` spells the
  coefficients out as the Navier–Stokes ones (`ν`, `u_{i,j}`, `u_{i,jj}`).
  Non-vacuity: `nsDiffH_not_bounded` (the operator is unbounded) and
  `nsDiffH_domain_dense` (the domain is dense).

Honest boundaries unchanged: nothing here claims global regularity of the
*classical* Navier–Stokes PDE (Contention D5, the deliberate scope cut); the
theorem is about the Hilbert-space operator at one Eulerian fiber, where the
derivative fields `u_{i,j}`, `u_{i,jj}` are independent canonical coordinates.

**Status (2026-08-20j, the Lagrangian / Eulerian parity closure: the
canonical/ladder realization of the Lagrangian second-order part on the
trajectory-space Hermite basis):** the 2026-08-20h next-step item (§9 item 11)
is now closed by one further `sorry`-free / `axiom`-free module,
`BookProof/ChapterNavierStokesLagrangianCanonical.lean` (namespace
`BookProof.NavierStokesFlow.LagrangianCanonical`), registered in `BookProof.lean`,
`#print axioms`-certified in `BookProof/ChapterRoadmapAudit.lean` and cited from
`Book/FreeField.lean`:

* **Canonical pairs on the trajectory space.** The ladder operators of the
  Hermite basis of the trajectory space are mutually adjoint on the finite-mode
  core (`inner_ann_cre`, `inner_cre_ann`), so the position and momentum
  operators are symmetric (`pos_isSymmetricDom`, `mom_isSymmetricDom`) and
  `posSq_add_momSq` is the number-operator identity `uᵢ² + πᵢ² = 2Nᵢ + 1`.
  Rescaling by `omega nu = √(2ν)` gives the Lagrangian canonical pair
  `lagQ`, `lagP` with the CCR `comm_lagP_lagQ` (`[Pᵢ, Qᵢ] = −i`) and
  `comm_lagP_lagQ_of_ne` (commuting for `i ≠ k`).
* **The identity.** `half_lagPSq_add_nu_lagQSq` is the componentwise
  `½Pᵢ² + νQᵢ² = ω(Nᵢ + ½)`, and `lagCan_secondOrder_eq` identifies the
  second-order part of the bundled data `lagCanData` with `lagT nu`, i.e.
  `T = ½ΣPᵢ² + νΣQᵢ² = ω(N + 3/2)` — the Lagrangian analogue of
  `canH_eq_velH` in `ChapterNavierStokesCanonicalVector`.
* **ESA and the flow.** `lagT_hasZeroDeficiencyOn` /
  `lagCan_secondOrder_hasZeroDeficiencyOn` give zero deficiency on the Hermite
  core, `lagCan_esa` the essential self-adjointness of the full Lagrangian
  generator (the drift discharged by the Kato–Rellich route already in place),
  and `lagCan_stone_flow` the complete unitary group `e^{-itT}` via the
  2026-08-20i Stone bridge.  Non-vacuity: `lagT_not_bounded` shows the operator
  is genuinely unbounded, so nothing here is a bounded-operator artefact.

With this the Lagrangian variables version of NS has the canonical/ladder
reading that the Eulerian version already had; the rigor-parity gap recorded at
2026-08-20h is closed at the realization layer.  Honest boundaries unchanged:
nothing here claims global regularity of the *classical* Navier–Stokes PDE
(Contention D5), and the *differential* realization of the full NS quadratic
symbol on `L²(du₁du₂du₃)` (§9 item 4) remains a recorded research boundary.

**Status (2026-08-20i, the Stone bridge and the concrete flows: the complete
unitary flow for the Eulerian NS, Lagrangian NS and QYM Hamiltonians):** the
2026-08-20f bridge item (§9 item 11) is now closed by two further `sorry`-free /
`axiom`-free modules, registered in `BookProof.lean` and cited from
`Book/FreeField.lean`:

* `BookProof/ChapterStoneBridge.lean` (namespace `BookProof.StoneBridge`) is the
  packaging step between the selection predicates and the bundled structure that
  Stone's theorem consumes.  `dense_domain_of_isSelfAdjointExtension` and
  `isSelfAdjointOn_of_isSelfAdjointExtension` pull the two missing conjuncts out
  of `IsSelfAdjointExtension` / `IsPositiveSelfAdjointExtension`, and
  `unboundedSelfAdjointOf` assembles the `UnboundedSelfAdjoint` bundle.  The
  complete unitary group is packaged as `IsStoneFlow` (`U 0 = 1`, the group law,
  isometry of each `U t`, and the Schrödinger equation on the domain);
  `isStoneFlow_stoneU` shows the abstractly constructed Stone group is such a
  flow; and `exists_stone_flow_of_selfAdjointExtension` / `of_positive` / `of_esa`
  are the three entry points — from a selected self-adjoint extension, from a
  positive (Friedrichs) one, and directly from essential self-adjointness of a
  symmetric core.
* `BookProof/ChapterStoneFlows.lean` (namespace `BookProof.StoneFlows`) runs the
  bridge on the three concrete Hamiltonians: `ns_stone_flow` (the Eulerian fiber
  generator `velCore A c` on `ℓ²(Vel)`, unique closure, no positivity),
  `lagrangian_stone_flow` / `diagKR_stone_flow` (the transformed parcel
  Hamiltonian, from `EssentiallySelfAdjointOn L.D (lagrangianCore L)`, with the
  unbounded `ℓ²(ℕ)` drift discharged by Kato–Rellich), and `ym_fock_stone_flow`
  (the second-quantized QYM Hamiltonian `dΓ(½Σπ² + ½ΣB²)` on the Fock space over
  the Gauss core of `L²(ℝ⁹⁹)`, Friedrichs extension).  Each conclusion is the
  `IsStoneFlow` package: `U 0 = 1`, the group law, isometry (hence unitarity),
  and the Schrödinger equation on the domain — global in `t`.

  This is exactly step **(c)** of §9 item 11 (applying the Stone group to obtain
  the complete flow), and it is instantiated for all three concrete Hamiltonians.
  Honest boundaries unchanged: the flow is that of the selected extension in the
  abstract realization; nothing claims global regularity of the *classical*
  Navier–Stokes PDE (Contention D5) or a Yang–Mills mass gap.

  **Build not re-run in this snapshot:** the §8 verification gate must be re-run
  by the next Lean 4 specialist after these waves are copied in.

**Status (2026-08-20h, the canonical realization of the full Navier–Stokes
quadratic symbol, and the Lagrangian/Eulerian rigor-parity record):** the
canonical-realization wave from the parallel lineage lands here on top of the
2026-08-20e Stone / 2026-08-20f bridge / 2026-08-20g Fock-of-Fock waves (the
parallel lineage's own label "2026-08-20e" is renamed 2026-08-20h to avoid
colliding with the current project's Stone wave of that date).  One further
module, `sorry`-free / `axiom`-free, registered in `BookProof.lean`, certified
in `BookProof/ChapterRoadmapAudit.lean` and cited from `Book/FreeField.lean`,
advances §9 item 4 (the differential/canonical realization of the full NS
quadratic symbol):

* `BookProof/ChapterNavierStokesCanonicalVector.lean` (namespace
  `BookProof.NavierStokesFlow.CanonicalVector`) builds the canonical pairs
  *inside* the Hermite sequence space of the three velocity components and shows
  that the hopping matrix of `ChapterNavierStokesThreeComponent` **is** the
  Weyl-ordered expression it was meant to be.  On the finite-mode core of
  `ℓ²(Fin 3 → ℕ)` the three ladder pairs `ann i`, `cre i` are the coordinate
  shifts `(a_i X)(β) = √(β_i+1) X(β+e_i)`, `(a_i† X)(β) = √β_i X(β−e_i)`; the
  full CCR is proved (`comm_ann_cre_of_ne`, `comm_ann_cre`), and the resulting
  `pos i = (a_i + a_i†)/√2`, `mom i = i(a_i† − a_i)/√2` are three commuting
  canonical pairs (`comm_mom_pos`, `comm_mom_pos_of_ne`).  Writing
  `canH = ∑_i ½(π_i V_i + V_i π_i)` with `V_i(u) = ∑_k A_{ik} u_k + c_i`
  literally in those operators and expanding by the commutation relations gives,
  hop by hop, exactly the twenty-four Hermite hopping amplitudes (`canFun_eq_ladFun`,
  `canH_eq_velH`).  Consequences: `canH_essentiallySelfAdjointOn_core` (the
  canonically written full quadratic symbol is essentially self-adjoint on the
  Hermite core, for arbitrary real `A` and `c`), `canH_not_bounded`,
  `canH_domain_dense`, and — with the coefficients spelled out the way the
  Navier–Stokes symbol supplies them, linear part the velocity gradient and
  constant part `−ν` times the velocity Laplacian at the fiber —
  `nsQuadraticH_essentiallySelfAdjointOn_core`.

  Honest boundary: the canonical pairs here are abstract, characterized by their
  commutation relations inside the sequence space; the unitary transport of the
  picture to `L²(du₁du₂du₃)`, where `u_i` is multiplication and `π_i`
  differentiation, is not built (the §9 item 4 record below), and nothing is
  claimed about the classical Navier–Stokes regularity problem (Contention D5,
  unchanged).

  **The rigor-parity record (the Lagrangian-variables version of NS vs. the
  Eulerian version).**  The Eulerian NS strand now has **four** realization
  layers, each verified: **(a)** sequence-space ESA on the finite-mode core
  (`velCore_esa`, `velH_essentiallySelfAdjointOn_core`); **(b)** the canonical /
  ladder reading of the full quadratic symbol (`ChapterNavierStokesCanonicalVector`:
  `canH_eq_velH`, `canH_essentiallySelfAdjointOn_core`,
  `nsQuadraticH_essentiallySelfAdjointOn_core`); **(c)** the Hermite/differential
  realization of the *fiber* generator on `L²(du)` (`ChapterNavierStokesHermiteCanonical`:
  `hamiltonian_eq`, `comparison_eq`, `canonical_essentiallySelfAdjointOn_core`);
  and **(d)** the Hashimoto/SIRK selection (`ns_hashimoto_selects`).  The
  Lagrangian strand matches on ESA, selection and the Fock lifting — Kato–Rellich
  relative-bound ESA (`hFull_hasZeroDeficiencyOn_of_drive_eq_P`), the
  Hashimoto/SIRK selection (`lagrangian_hashimoto_selects`), the concrete
  `ℓ²(ℕ)` instance `diagKR`, and the Fock-of-Fock trajectory-space realization
  (`fockLagrangian_hasZeroDeficiencyOn`, `hTwoLevel_hasZeroDeficiencyOn`) — and,
  with the 2026-08-20i Stone-flow wave, on the complete flow.  What the
  Lagrangian side does **not** yet have is the canonical/ladder and
  Hermite/differential realization of its second-order part `T` on the
  trajectory-space `L²` (the analogue of `CanonicalVector`/`HermiteCanonical`):
  `T` is realized concretely only on the abstract diagonal instance `diagKR`.
  That gap is recorded as the open Lagrangian item in §9 item 9 below, so the two
  versions of NS are at parity *except* for that one realization layer.

  **Build not re-run in this snapshot:** the §8 verification gate must be re-run
  by the next Lean 4 specialist after these waves are copied in.

**Status (2026-08-20g, the Fock-of-Fock / second-quantization lifting is
recorded, and the honest boundary is narrowed):** the point that the Fock-space
and Fock-of-Fock constructions already lift essential self-adjointness from a
one-particle (one-parcel) operator to the Hamiltonian on the Fock space — the
finite-particle basis — is correct and is now recorded precisely.  The lifting
theorems are proved, not named:

* `fockOp_hasZeroDeficiencyOn` (`BookProof/ChapterNavierStokesSecondQuant.lean`)
  — the direct-sum half of Reed–Simon Vol. I §VIII.10: **if every sector
  operator is essentially self-adjoint on its sector domain, then the second
  quantization is essentially self-adjoint on the finite-particle domain** —
  for NS this is exactly "ESA of the one-particle Hamiltonian implies ESA of the
  Hamiltonian on the Fock space", and it needs **no** positivity and **no**
  diagonalizability of the one-particle operator.  The diagonal companion
  `dGamma_hasZeroDeficiencyOn` (`ChapterNavierStokesFockEsa.lean`) covers the
  occupation-number case of the NS comparison operator.
* `secondQuantization_friedrichs` (`BookProof/ChapterFockSecondQuantization.lean`)
  — the *positive* lifting: a symmetric positive one-particle operator gives a
  positive (Friedrichs) self-adjoint extension of `dΓ(A)` on the finite-
  occupation domain.
* `fockLagrangian_hasZeroDeficiencyOn` (`BookProof/ChapterNavierStokesFockParcels.lean`)
  and `hTwoLevel_hasZeroDeficiencyOn` (`ChapterNavierStokesFockEsa.lean`) — the
  **Fock-of-Fock** realization: the transformed Navier–Stokes Hamiltonian is
  second-quantized on the continuum Fock space over `ParcelConf Ω = Σ n, Fin n →
  Ω` (`fockMeasure`), quadratic in the outer ladder operators
  (`twoLevelSymbol = ext + confEnergy`), and essentially self-adjoint there with
  no boundedness assumptions — the Lagrangian trajectory-space realization is
  **built on the continuum Fock space**, and `nsFullData_hasZeroDeficiencyOn_of_fockLagrangian`
  transports it back to the Eulerian operator.

What this *corrects* is the old wording that "the trajectory-space `L²`
realization (the Fock-of-Fock space) remains the only part of the route not yet
carried": that realization **is** carried, on the continuum Fock space, not on a
single-particle `L²(Ω)`.  The Eulerian side lifts too: for NS, **ESA of the
one-particle Hamiltonian implies ESA of the Hamiltonian on the Fock space
(finite-particle basis)** — that is exactly the direct-sum half
`fockOp_hasZeroDeficiencyOn`, which needs **only sector-wise ESA**, *not*
positivity and *not* diagonalizability of the one-particle operator.  Concretely,
`velCore` is already proved essentially self-adjoint on the finite-mode core
(`velCore_esa`, `ChapterNavierStokesHashimoto`; and the three-component
`velH_essentiallySelfAdjointOn_core`, `ChapterNavierStokesThreeComponent`), so
the Fock-space Hamiltonian over the fiber is essentially self-adjoint on the
finite-particle domain by the same lifting — the earlier draft's claim that the
Eulerian lift is blocked by lack of positivity or of a Hermite diagonalization
was **wrong** on both counts.  (`secondQuantization_friedrichs` is the
*positive* companion used on the QYM side; its non-applicability here is
irrelevant to the ESA lifting, which is positivity-free.)  What remains the
genuine boundary is the **differential realization**: the three-component
Eulerian operator is an essentially self-adjoint operator given by its matrix in
the Hermite/sequence-space basis, and its genuinely differential realization on
`L²(du₁du₂du₃)` — the step from the matrices to `π = −i∂/∂u` — is the open step
(no lifting theorem, positive or diagonal, would supply it).

Nothing here claims global regularity of the *classical* Navier–Stokes PDE
(Contention D5, unchanged); the operator-flow global existence follows from ESA
by the Stone theorem of 2026-08-20e (the §9 item 11 bridge), which is the only
remaining *application* step.  **Build not re-run in this snapshot:** the §8
verification gate must be re-run by the next Lean 4 specialist after these waves
are copied in.

**Status (2026-08-20e, Stone's theorem in full generality on separable Hilbert
spaces):** the research boundary that the passes below kept pointing at — "the
unitary group `e^{-itA}` of an unbounded self-adjoint operator, i.e. Stone's
theorem in full generality" — is now **proved** by nine new `sorry`-free /
`axiom`-free modules, registered in `BookProof.lean` and cited from
`Book/FreeField.lean`:

* `BookProof/ChapterStoneResolvent.lean` — the analytic core: the resolvents
  `(A − il)⁻¹` at real `l ≠ 0`. Self-adjointness makes `A − il` a bijection of
  the domain onto the whole space (`shift_bijective`), so the resolvent is
  bounded with `‖(A − il)⁻¹‖ ≤ 1/|l|` (`resCLM`, `norm_resCLM_apply_le`), its
  adjoint is the resolvent at `−l` (`inner_res`), and resolvents at different
  parameters commute (`res_comm`).
* `BookProof/ChapterStoneGroup.lean` — the bounded **Yosida approximations**
  `A_n = n²A(A² + n²)⁻¹`: bounded, self-adjoint, mutually commuting, converging
  to `A` on its domain (`yosida_tendsto`), with the first resolvent identity
  `res_sub` as engine.
* `BookProof/ChapterStoneEvolution.lean` — the bounded unitary groups
  `e^{-itA_n}` (unitary because the generator is skew-adjoint,
  `approxU_mem_unitary`).
* `BookProof/ChapterStoneUnitary.lean` — the strong limit
  `U t = e^{-itA}` (`stoneU`, `tendsto_stoneU`): unitary, group law, strongly
  continuous (`continuous_stoneU_apply`), hence weakly measurable.
* `BookProof/ChapterStoneGenerator.lean` — the group leaves the domain invariant
  (`stoneU_mem_domain`), commutes with `A` there, and solves the Schrödinger
  equation `d/dt (U t x) = −iA(U t x)` on the domain
  (`hasDerivAt_stoneU_zero`, `hasDerivAt_stoneU`).
* `BookProof/ChapterStoneMeasurable.lean` — the converse, separable half:
  von Neumann's averaging argument promotes weak measurability to strong
  continuity (`norm_apply_avgVec_sub_le`, `dense_avgSpan`, `continuous_apply`).
* `BookProof/ChapterStoneConverse.lean` — the infinitesimal generator
  `A x = i d/dt|₀ U t x` on the domain of differentiable orbits (`genDomain`,
  `genOp`): densely defined, symmetric, then self-adjoint (`gen`).
* `BookProof/ChapterStoneTheorem.lean` — the assembly: the generator of
  `e^{-itA}` is `A` again (`gen_stoneGroup_eq`), every weakly measurable group is
  `e^{-itA}` for its generator (`gen_stoneU_eq`), so the correspondence is a
  bijection (`stone_bijection`), and the forward direction is bundled as
  `stoneGroup : UnboundedSelfAdjoint H → WeakMeasurableUnitaryGroup H`.
* `BookProof/ChapterStoneSeparable.lean` — the capstone: `stone_exists_unique_group`
  / `stone_exists_unique_generator` in `∃!` form, the explicit bijection
  `stoneEquiv : UnboundedSelfAdjoint H ≃ WeakMeasurableUnitaryGroup H`, and a
  genuinely unbounded instance on `ℓ²(ℤ)` — multiplication by a real field on
  its natural domain (`mulSA`, unbounded for the position field,
  `mulSA_position_unbounded`) whose abstractly constructed group is the explicit
  phase group `(e^{-itA}ψ)_k = e^{-it f k} ψ_k` (`stoneU_mulSA`).

This closes the "Stone's theorem in full generality" boundary of §4.8/§4.9, the
§8 verification-gate pointer in item 1 below, and the Step-(c) note of §9 item 8:
the passage from essential self-adjointness of a generator to the complete
unitary flow is now a proved theorem, applicable to any essentially self-adjoint
operator on a separable Hilbert space (the classical *global existence* claim for
the Navier–Stokes PDE remains, as always, the deliberate D5 scope cut — Stone
gives the operator flow, not PDE regularity).  **What is not yet done is the
instantiation:** the theorem is stated for the bundled `UnboundedSelfAdjoint`
structure, while the QYM/NS threads produce `IsSelfAdjointExtension` /
`IsPositiveSelfAdjointExtension` operators; the wrapper lemma plus a `stoneGroup`
application would yield the explicit flows `e^{-itA}` for the QYM, Eulerian-NS
and Lagrangian-NS Hamiltonians (§9 item 11).  **Build not re-run in this
snapshot:** the §8 verification gate must be re-run by the next Lean 4 specialist
after these waves are copied in.

**Status (2026-08-20d, the Lagrangian route: Kato–Rellich relative-boundedness
and the Hashimoto/SIRK selection on the parcel side):** the residual that §9
item 9 named for the Lagrangian (parcel) route is now closed by two new
`sorry`-free / `axiom`-free modules (both registered in `BookProof.lean`,
certified in `BookProof/ChapterRoadmapAudit.lean`, cited from
`Book/FreeField.lean`):

* `BookProof/ChapterKatoRellichRelative.lean` (`BookProof.KatoRellich`) proves
  the Kato–Rellich theorem for a **relatively bounded** — possibly unbounded —
  symmetric perturbation: `‖Bx‖ ≤ a‖Hx‖ + b‖x‖` with `0 ≤ a < 1` on the common
  domain preserves essential self-adjointness
  (`essentiallySelfAdjointOn_add_relBounded`), by an explicit Neumann iteration
  at a large non-real shift — no closures, no spectral theorem — with the new
  ingredient `norm_le_of_relBound` (for symmetric `H`,
  `‖Hx − eix‖² = ‖Hx‖² + e²‖x‖²`, so the relative bound becomes the contraction
  bound `a + b/|e|`).  The previously available
  `essentiallySelfAdjointOn_add_bounded` is recovered as the case `a = 0`.
* `BookProof/ChapterNavierStokesLagrangianKatoRellich.lean`
  (`BookProof.NavierStokesFlow.LagrangianKatoRellich`) applies it to the
  transformed Hamiltonian.  The positivity gain of the Lagrangian variables
  *is* the relative bound: `‖Pᵢv‖² = ⟪v,Pᵢ²v⟫ ≤ 2⟪v,Tv⟫ ≤ 2‖v‖‖Tv‖` for
  `T = ½∑Pⱼ² + ν∑Qⱼ²`, since every other term of that quadratic form is
  nonnegative; with `√(2AB) ≤ εB + A/(2ε)` this gives
  `‖Pᵢv‖ ≤ ε‖Tv‖ + (2ε)⁻¹‖v‖` for every `ε > 0` (`norm_P_le`) — the
  Ikebe–Kato interpolation of the 1st-order drift against the 2nd-order
  Laplacian.  Hence `hFull_hasZeroDeficiencyOn`: ESA of the positive
  second-order part alone gives ESA of the **full** transformed Hamiltonian
  (`hFull_hasZeroDeficiencyOn_of_drive_eq_P` in the physical case `Dᵢ = Pᵢ`),
  transported back to the Eulerian operator by
  `hasZeroDeficiencyOn_of_lagrangian_katoRellich`.  On top of it the
  Hashimoto/SIRK selection is proved on the Lagrangian side —
  `lagrangian_selfAdjoint_extension`, `..._unique`,
  `lagrangian_hashimoto_selects`, `lagrangian_shiftInvert_selects` — from this
  ESA and therefore independently of the Eulerian item 8.  Non-vacuity: the
  `ℓ²(ℕ)` instance `diagKR` has a genuinely **unbounded** drift
  (`diagKR_drift_not_bounded`), so the bounded Kato–Rellich theorem does not
  cover it, while the relative one does (`diagKR_hashimoto_selects`).
  Sharpness: `jacobiLag_drift_not_relativelyBounded` shows the counterexample
  `exists_lagrangianFullData_not_hasZeroDeficiencyOn` fails exactly the
  domination hypothesis, so that hypothesis is not decorative.

With this, **both** NS routes are executed: the Eulerian/Hashimoto selection of
item 8 (2026-08-20d, ESA-closure) and the Lagrangian/parcel selection of item 9.
The Eulerian fiber generator is not an abstract model in disguise: it is verified
**on the Hermite core of `L²(du)`** as the genuinely differential operator
`½(πV + Vπ)` with `π = −i∂/∂u`, `V(u) = κu` — `BookProof/ChapterNavierStokesHermiteCanonical`
proves `hamiltonian_eq`/`comparison_eq` (the Hermite-basis matrix *is* the
differential operator) and `canonical_essentiallySelfAdjointOn_core` /
`nsH_essentiallySelfAdjointOn_core` (ESA there, with no hypothesis left), so the
differential realization on `L²(du)` is **proved for the fiber generator**, and
the same canonical identification underlies the QG and QYM Hermite cores
(`hermiteCoreOp_essentiallySelfAdjoint`, `oscillator_essentiallySelfAdjoint_on_hermiteCore`).
What remains differential-realization-wise is the *full* quadratic-symbol /
three-component continuum operator and the *Lagrangian* second-order part `T`
(whose concrete ESA instance is the abstract `diagKR` on `ℓ²(ℕ)`); global
regularity of the *classical* Navier–Stokes equation remains the deliberate D5
scope cut.  **Build not re-run in this snapshot:** the §8 verification gate must
be re-run by the next Lean 4 specialist after these waves are copied in.

**Status (2026-08-20c, arbitrary signs and the three coupled velocity
components):** the two boundaries kept in the passes below — the sign condition
`c ≥ 0` on the fiber constant, and the restriction to a single velocity
component — are now removed, by three new `sorry`-free / `axiom`-free modules
(all registered in `BookProof.lean`, certified in
`BookProof/ChapterRoadmapAudit.lean`, cited from `Book/FreeField.lean`):

* `BookProof/ChapterNavierStokesSignFlip.lean` (`BookProof.NavierStokesFlow.SignFlip`)
  formalizes the sign-flip unitary. Essential self-adjointness on a core is
  proved to be a *unitary invariant*
  (`essentiallySelfAdjointOn_of_intertwine` and companions); the sign flip
  `(Ux)_β = (−1)^{pβ} x_β` is built as a `LinearIsometryEquiv` (`flipU`) with the
  conjugation rule `shiftH_flip`, so the affine fiber and block Hamiltonians are
  essentially self-adjoint for a fiber constant of **arbitrary sign**
  (`saffH_essentiallySelfAdjointOn_core`, `sblockH_essentiallySelfAdjointOn_core`),
  with the `±1` hopping genuinely present (`saffH_coord_succ`,
  `saffH_ne_zero_of_shear`).
* `BookProof/ChapterNavierStokesSignedShift.lean`
  (`BookProof.NavierStokesFlow.SignedShift`) drops both remaining bookkeeping
  restrictions on a hopping term at once: a `SignedHop` carries an **arbitrary
  real** amplitude dominated in absolute value by `¼σ + K` (neither non-negative
  nor monotone along the shift), and the two Faris–Lavine inequalities and
  essential self-adjointness are proved against the majorant `¼σ + K`
  (`hopH_symmetricOn`, `hopH_relative_bound`, `hopH_commForm_bound`,
  `hopH_essentiallySelfAdjointOn_core`).  `listH` sums a finite family sharing one
  comparison symbol (`listH_essentiallySelfAdjointOn_core`), which yields
  `gaffH_essentiallySelfAdjointOn_core`: the one-component affine fiber
  Hamiltonian with **no sign hypothesis at all** on `κ` and `c`.
* `BookProof/ChapterNavierStokesThreeComponent.lean`
  (`BookProof.NavierStokesFlow.ThreeComponent`) carries **all three coupled
  velocity components**: the Hermite index is `Vel = Fin 3 → ℕ`, the fiber fields
  are the affine `V_i(u) = ∑_k A_{ik} u_k + c_i` for an **arbitrary real** `3 × 3`
  matrix `A` (no symmetry, positivity or sign assumption) and an arbitrary real
  vector `c`, and `H = ∑_i ½(π_i V_i + V_i π_i)` becomes twenty-four hopping terms
  — including the number-conserving *vorticity* hopping whose amplitude is not
  monotone along its shift, exactly what the signed instrument above was built
  for.  Headline: `velH_essentiallySelfAdjointOn_core`, with the strain/vorticity
  matrix entries computed (`velH_coord_pair`, `velH_coord_rot`,
  `velH_coord_shear`, `velH_coord_diag`), non-vacuity
  (`velH_ne_zero_of_strain` / `velH_ne_zero_of_vorticity`) and unboundedness
  (`velH_not_bounded`).

Together with the earlier `E.6` pass (`BookProof/ChapterGaugeFixing.lean`, the
BRST-doublet / Gauge-Fixing-Fermion skeleton, executed 2026-08-20 and recorded in
`PLAN_LEAN_SPECIALIST_NS_FLOW.md`), the Navier–Stokes thread is now fully executed:
the fiber generator is verified on the Hermite core of `L²(du)` as the genuine
differential operator `½(πV + Vπ)` (`ChapterNavierStokesHermiteCanonical`:
`hamiltonian_eq`, `comparison_eq`, `canonical_essentiallySelfAdjointOn_core`), and
only the *full* quadratic-symbol / three-component and Lagrangian `T` differential
realizations remain open; global regularity of the *classical* Navier–Stokes
equation remains the deliberate D5 scope cut.  **Build not re-run in this
snapshot:** the §8 verification gate must be re-run by the next
Lean 4 specialist after these waves are copied in.

**Status (2026-08-20b, the viscous term and the cross terms):** the boundary
kept in the pass below — the *affine* fiber field `V(u) = κ_j u + c_j` produced
by the viscous term `−ν u_{i,jj}` and the `j ≠ i` cross terms, i.e. a `±1` shift
on top of the `±2` shift — is now removed, by two new `sorry`-free /
`axiom`-free modules, `BookProof/ChapterNavierStokesAffineFiberEsa.lean` and
`BookProof/ChapterNavierStokesAffineBlockEsa.lean` (both registered in
`BookProof.lean`, certified in `BookProof/ChapterRoadmapAudit.lean`, cited from
`Book/FreeField.lean`).  The instrument is that the Faris–Lavine hypotheses are
**stable under sums**: `‖(H₁+H₂)x‖² ≤ 2‖H₁x‖² + 2‖H₂x‖²`, the commutator form is
additive in `H`, and the relative bound carries no smallness requirement, so two
hopping operators sharing one comparison operator may simply be added.  With the
number operator `μ(2n+1)+1`, `μ = κ + c + 1`, dominating both the `±2`-hopping
`(κ/2)√((n+1)(n+2))` of `κ·½(πu+uπ)` and the `±1`-hopping `(c/√2)√(n+1)` of
`c·π`, the affine fiber Hamiltonian is symmetric and essentially self-adjoint on
the finite-mode core (`affH_symmetricOn`, `affH_essentiallySelfAdjointOn_core`),
with both hoppings genuinely present (`affH_coord_succ`,
`affH_coord_succ_succ`, `affH_ne_zero_of_pos_shear`) and the operator unbounded
(`affH_not_bounded`).  Running the block decomposition again with the affine
fiber gives `affBlockH_symmetricOn`, `deficiencyTrivialAt_affBlockH`, the
headline `affBlockH_essentiallySelfAdjointOn_core` and
`affBlockH_not_bounded`.  **Boundary kept:** `c_j ≥ 0` is assumed (a hopping
amplitude must be non-negative; the sign-flip unitary `x_n ↦ (−1)ⁿ x_n` that
would remove the restriction is not formalized), only one velocity component is
carried, and global regularity of the *classical* Navier–Stokes equation remains
the deliberate D5 scope cut.  The full §8 gate was re-run in this pass and is
green: `lake build` (8637 jobs, no warnings), `lake build RandomMap`,
`lake build UsedRoute`, `./patches/build-book.sh`, `./patches/check-katex.sh`
(2208 snippets, 0 failures), the sorry/axiom audit and the isolation audit.

**Status (2026-08-20, the bilinear/quadratic NS symbol):** the residual named in
§9 item 4 and in the "what is missing from `PLAN_LEAN_SPECIALIST_NS_FLOW.md`"
record — the Faris–Lavine step for the *quadratic* Navier–Stokes symbol
`A_i = ∑_j u_j u_{i,j} − ν u_{i,jj}` — is executed for the **bilinear advection
term** by the new `sorry`-free / `axiom`-free module
`BookProof/ChapterNavierStokesBilinearEsa.lean` (registered in `BookProof.lean`,
certified in `BookProof/ChapterRoadmapAudit.lean`, cited from
`Book/FreeField.lean`).  The instrument is a **block decomposition**, not a
global Faris–Lavine estimate, and the reason is structural: in the Eulerian
derivatives-as-fields picture the Hamiltonian carries momenta only for the
velocity modes, so the derivative modes commute with it and are constants of the
motion.  Diagonalising the derivative field splits the space as `ℓ²(ℕ × J)` —
Hermite levels of the velocity fiber times the spectrum `J` of the derivative
field — and in the block `j` the bilinear symbol `A = u_{,1}·u` is the *linear*
advection field `V(u) = κ_j u`, whose fiber Hamiltonian is exactly the `nsH (κ)`
for which the two Faris–Lavine inequalities are already proved
(`ChapterNavierStokesHermiteFarisLavine`).  Because the strain rates `κ_j` range
over the (in general unbounded) spectrum, **no** single pair of Faris–Lavine
constants can serve the whole operator — but the deficiency problem decomposes
over the blocks.  Proved: `bilH_symmetricOn`, `deficiencyTrivialAt_bilH`, the
headline `bilH_essentiallySelfAdjointOn_core` (arbitrary, possibly unbounded
`κ : J → ℝ` with `0 ≤ κ`), and the non-vacuity/unboundedness facts
`bilH_ne_zero` and `bilH_not_bounded`.  **Boundary kept:** the viscous term and
the `j ≠ i` cross terms add a constant to the fiber field — an affine
`V(u) = κ_j u + c_j`, a `±1` shift on top of the `±2` shift — and are not
covered; global regularity of the *classical* Navier–Stokes equation remains the
deliberate D5 scope cut.  The full §8 gate was re-run in this pass and is green:
`lake build` (8635 jobs, no warnings), `lake build RandomMap`,
`lake build UsedRoute`, `./patches/build-book.sh` (its `<base>`/fragment-link
assertions hold), `./patches/check-katex.sh` (2193 snippets, 0 failures), the
sorry/axiom audit (`BookProof/`, `PnpProof/`, `Singularity/`, `RandomMap/` carry
no `sorry` and no `axiom`) and the isolation audit.  The `patches/*.sh`
executable bits had again reverted to mode 644 in this snapshot and were
restored in git.

**Status (2026-08-18c, the non-commuting mixed case):**
`BookProof/ChapterHarmonicOscillatorEsa.lean` (`sorry`-free / `axiom`-free,
registered in `BookProof.lean`, certified in `BookProof/ChapterRoadmapAudit.lean`)
closes the gap left by the wave below — a differential kinetic term plus a
non-commuting unbounded polynomial potential — in the elliptic normalization:
the harmonic oscillator `-d²/dx² + x²/4` is essentially self-adjoint on the
Hermite core of `L²(ℝ)` (`harmonicOsc_essentiallySelfAdjoint`), is symmetric there
(`harmonicOsc_symmetric`) and is genuinely unbounded (`harmonicOsc_not_bounded`).
The substance is `harmonicOscOp_apply_eq_differential`, identifying the diagonal
operator with eigenvalues `n + ½` with the differential expression
`x ↦ -ψ''(x) + (x²/4) ψ(x)` on the Hermite basis (Mathlib's `deriv`), on top of
`hermiteC_oscillator`.  The hyperbolic mixture, with the sign correction recorded
below, remains the open boundary.  Details: `STRICHARTZ_WAVE_ESA.md`.

**Status (2026-08-18b, §9.5 unbounded-potential item executed as far as it is
true):** `BookProof/ChapterWaveUnboundedPotential.lean` (`sorry`-free /
`axiom`-free, registered in `BookProof.lean`, certified in
`BookProof/ChapterRoadmapAudit.lean`) carries out steps (a) and (b) of the
localization plan of §9.5 and closes both *commuting* halves of the problem with
unbounded coefficients: an arbitrary real potential of temperate growth — every
polynomial, unbounded and with no semiboundedness assumption — is essentially
self-adjoint on the Schwartz core (`potentialOp_essentiallySelfAdjoint`,
`polynomialPotential_essentiallySelfAdjoint`), and dually every real *symbol* of
temperate growth gives an essentially self-adjoint Fourier multiplier
(`multiplierOp_essentiallySelfAdjoint`, with `constCoeffOp_eq_multiplierOp`
showing this generalizes the quadratic-symbol theorem of
`ChapterStrichartzWave`).  For the mixture, `□ + W` is proved to be a well-defined
symmetric operator on the Schwartz core for every real `W` of temperate growth
(`wave_add_potentialOp_symmetric`), and essentially self-adjoint for every
truncation `W_R` of it (`wave_add_truncatedPotential_essentiallySelfAdjoint`).
Step (c) is **not** taken, and the plan item's hypothesis needs a **sign
correction**: with this project's convention `□ = -∂_t² + Δ_x`, a potential
bounded *below* makes the time-Fourier fibre `-Δ_x - W` unbounded below (for
`W = x⁴` the limit-circle operator `-d²/dx² - x⁴`, deficiency indices `(2,2)` — a
classical fact quoted from the literature, not formalized here), so essential
self-adjointness genuinely fails; the closable hypothesis is `W` bounded
*above* by a quadratic here, equivalently `W` bounded below in the
opposite-signature convention `□ = ∂_t² - Δ_x` of the physics literature.  Details:
`STRICHARTZ_WAVE_ESA.md`; the wave is cited from `Book/DiffeomorphismsGravity.lean`.

**Status (2026-08-19, §11.4 + Part F closed):** the two plan items of §11.4 (the
unbounded Friedrichs existence theorem and the continuum-realization decision)
are executed by `BookProof/ChapterFriedrichsExtension.lean`; see §9 item 6 and
the update at the end of §11.4.  The field-space realization is now **executed,
not just well-defined**: `BookProof/ChapterHermiteProductCore.lean` and
`BookProof/ChapterYangMillsHermite.lean` build the product Hermite (Gauss–
polynomial) core of `L²(ℝ⁹⁹)` and define the coordinate/momentum/magnetic-field
operators, the Weyl ordering (`[A_j, π_j] = i`) and the positive sum-of-squares
Hamiltonian on it, instantiating the Friedrichs + Hashimoto theorems; the
second quantization on the finite-occupation states is executed in
`BookProof/ChapterFockSecondQuantization.lean`.  See the closing updates of
§11.3/§11.4 and `PLAN_LEAN_SPECIALIST_QYM_FLOW.md` Part F.

**Status (2026-08-17, QG + QYM plan items executed):** the two "suggested next
step" plan items of §10.3 and §11.3 are now **closed**.  Both are written up as
plans in the NS-FLOW style — `PLAN_LEAN_SPECIALIST_QG_FLOW.md` and
`PLAN_LEAN_SPECIALIST_QYM_FLOW.md` — and executed by two new `sorry`-free /
`axiom`-free modules, registered in `BookProof.lean`, certified in
`BookProof/ChapterRoadmapAudit.lean` and cited from the book:

* `BookProof/ChapterQuantumGravityDensitized.lean` (§10, cited from
  `Book/DiffeomorphismsGravity.lean`) — Part A the densitized change of variables
  (`densY`, `densTetrad`, the absorption identity `1/e = 4(∂y/∂e)²`
  — note the factor `4`, which §10.1's prose omits — the densitized form of the two
  singular kinetic terms, and `tendsto_inv_det_atTop` vs `tendsto_densY_zero`);
  Part B the flat principal part (`qgSymbol`, `qgSymbol_eq_metric_form`,
  `qgMetric_det_ne_zero`, `qgSymbol_indefinite` — hyperbolic, not elliptic — and
  `christoffel_eq_zero_of_const`, the vanishing of the connection corrections for a
  constant field-space metric, plus the operator-order decomposition
  `qgFullSymbol_scaling`); Part C the Hermite-basis realization, where the
  operator is unbounded, essentially self-adjoint on its maximal domain and has
  trivial deficiency at *every* non-real `z`
  (`qgModeHamiltonian_essentiallySelfAdjoint`,
  `qgModeHamiltonian_deficiencyTrivialAt`, `qgModeHamiltonian_not_bounded`); and
  Part D Strichartz as a **named hypothesis, never an axiom**
  (`strichartz_esa_of_finiteSpeed`, shown satisfiable by
  `strichartz_finiteSpeed_satisfiable`), the Faris–Lavine alternative
   (`qg_esa_of_farisLavine`) and the half-density transfer step
   (`densitized_hasZeroDeficiencyOn_transfer`).  **2026-08-19:** the book's full
   quantum Hilbert space and its 3D gauge-fixed operator are the next targets,
   written up as Part E (second quantization on the graded Fock space
   `Γˢ⊗Γᵃ`, fermionic CAR half) and Part F (concrete densitized/Weyl-ordered
   field-space Hamiltonian + BRST charge `G`) of
   `PLAN_LEAN_SPECIALIST_QG_FLOW.md`.
* `BookProof/ChapterYangMillsFriedrichs.lean` (§11, cited from
  `Book/YangMillsQuantization.lean`) — Part A the densely-defined Weyl-gauge
  Hamiltonian (`weylOpDom`, `weylOpDom_symmetricOn`, `weylOpDom_quadForm` the sum
  of squares, `weylOpDom_quadForm_nonneg` semi-boundedness); Part B the quadratic
  form and its closure (`formInner`, `formNormSq_ge_normSq`, Cauchy–Schwarz
  `re_formInner_sq_le` and the headline `form_closable`, applied as
  `weylForm_closable`); Part C the Friedrichs extension as a **named theorem**
  (`IsPositiveSelfAdjointExtension`, `friedrichs_extension_of_semibounded`,
  satisfiability `friedrichs_hypothesis_satisfiable`, and the conditional
  conclusion `weyl_friedrichs_extension`); Part D the proved SIRK supporting facts
  (`weylKrylov_bestApprox_antitone`, `weylKrylov_bestApprox_tendsto_zero`).  The
  §11.2 uniqueness sentence ("the infinite Hashimoto limit selects the Friedrichs
  extension") stays a **conjecture recorded in prose**: it is not written as a Lean
  statement, because it needs the limit operator of the Krylov flag, which is not
  constructed.

The honest boundaries of §10.3 and §11.3 are unchanged: nothing is claimed about
essential self-adjointness of the continuum gravity operator, about
self-adjointness of the continuum Yang–Mills operator (which is, however,
*well-defined on the Hermite core* — see the 2026-08-18 refinement in
§11.3/§11.4), about the mass gap, or about global existence in either theory.

After this wave the full §8 gate was re-run and is green: `lake build` over the
default targets (no warnings), `lake build RandomMap`, `./patches/build-book.sh`
(the `<base>`-removal and fragment-link assertions pass, and the new QG/QYM
citations render), the sorry/axiom audit (`BookProof/`, `PnpProof/`,
`Singularity/`, `RandomMap/` are `sorry`-free and `axiom`-free) and the isolation
audit (no `import PnpProof` / `import UnusedRoute` in the in-scope libraries).

**Status (2026-08-17, verification-gate pass + plan item A.7 closed):** the §8
verification gate was re-run in this repository and is green (`lake build` over the
default targets, `lake build RandomMap`, the sorry/axiom audit and the isolation
audit); this discharges the "verification gate not yet run in this repo" note of
§9. The one open plan item recorded in §9 — **A.7** of
`PLAN_LEAN_SPECIALIST_NS_FLOW.md`, the second-derivative extension `genY2` of the
Eulerian gauge generator — is now **closed** by the new `sorry`-free /
`axiom`-free module `BookProof/ChapterNavierStokesGaugeY2.lean`: the second-order
field `u_i(y) = u_i + u_{i,j} y_j + ½ u_{i,jj} y_j²` (`uField2`), the derivative
field `u_{i,j}(y)` (`uDField`), the generator
`G²_j = ∂/∂y_j − u_{i,j} ∂/∂u_i − u_{i,jj} ∂/∂u_{i,j}` (`genY2`), the annihilation
theorems (`genY2_uField2`, `genY2_uDField`), the gauge invariance of the symbol
built from the fields (`genY2_nsSymbol2`, `genX_nsSymbol2`) and its `y = 0`
collapse (`setYZero_nsSymbol2`), the sharpness statements
(`genY_uField2_ne_zero`, `genY2_uField_ne_zero`,
`genY2_uField2_perturbed_ne_zero`) and the first-class (abelian) property
(`genY2_genY2_commute`, `genX_genY2_commute`), together with the honest
non-commutation of the *mixed* bracket (`genY_genY2_not_commute`). The module is
registered in `BookProof.lean`, certified in `ChapterRoadmapAudit.lean` and cited
from `Book/FreeField.lean`. The cosmetic A.1 name was also closed:
`ChapterF1.positionOp` is now an alias of `fieldPhi = creat + annih`.

**Status (2026-08-13, maintenance + analytic layer pass):** the §8 verification gate
was re-run and is green (`lake build` over the default targets, `lake build
RandomMap`, `./patches/build-book.sh`, `./patches/check-katex.sh`, the sorry/axiom
audit and the isolation audit). No plan item was open; the pass therefore advanced
the *standing open layer* recorded in §9.3 (the infinite-dimensional analytic
realization behind §4.8) with three new `sorry`-free / `axiom`-free modules —
`BookProof/ChapterContinuityUnitaryInfinite.lean` (the dynamics-based unitary as
bounded operators on `ℓ²(ℤ)`, with countably additive Born recovery),
`BookProof/ChapterBornMeasure.lean` (`P(B) = ∫_B |Ψ|² dμ` as a genuine probability
*measure* on an arbitrary measure space, for the evolved state of any bounded
self-adjoint generator) and `BookProof/ChapterUnboundedPosition.lean` (the lattice
position operator: densely defined, symmetric, and provably unbounded) — all
registered in `BookProof.lean`, certified in `ChapterRoadmapAudit.lean` and cited
from `Book/ConditionalUnitary.lean` and the `Book/ProofPlans.lean` §E boundary. A
second wave the same day took `ChapterUnboundedPosition` past symmetry: the maximal
multiplication operator on `ℓ²(ℤ)` is proved **self-adjoint**
(`adjointDomain_eq_mulDomain`, `adjoint_eq_mulOp` — the adjoint domain is exactly
the natural domain, and the adjoint acts by the same multiplication), and it
**generates its unitary group** (`phaseUnitary`, a `LinearIsometryEquiv`, with
`phaseUnitary_zero`/`phaseUnitary_add` the one-parameter group law,
`tendsto_phaseUnitary` strong continuity at `0` for every state with no domain
hypothesis, and `tendsto_slope_phaseUnitary` Stone's relation `dU/dt|₀ = iA` in
`ℓ²(ℤ)` on the natural domain).  What was still open — the same package for
unbounded operators that are *not* multiplication operators in the ambient basis
(the continuum Laplacian), i.e. Stone's theorem in full generality — is now
**proved** (2026-08-20e, `BookProof/ChapterStoneResolvent` through
`ChapterStoneSeparable`).
The executable bits on
`patches/*.sh` were restored in git (they had reverted to mode 644, which broke
`./patches/build-book.sh`).

**Status (2026-08-12, final pass):** the last two formalization targets are now
closed — `weakValue` (§4.7, `BookProof/ChapterWeakValue.lean`) and
`continuityUnitary` (§4.8, `BookProof/ChapterContinuityUnitary.lean`) are proved,
`sorry`-free and `axiom`-free, registered in `BookProof.lean`, certified in
`BookProof/ChapterRoadmapAudit.lean`, and cited from `Book/DoubleSlit.lean` and
`Book/ConditionalUnitary.lean`; the `Book/ProofPlans.lean` appendix §D/§E now record
them as PROVED. The keep-or-delete decision on `Book/Trivial.lean` (§7) is settled:
**keep** (see §7). No plan item remains open.

**Status (2026-08-12):** the default build (`lake build`: `BookProof`, `Book`,
`Singularity`), `lake build RandomMap`, `lake build book` + `lake exe book` +
`./patches/postprocess-html.sh`, and the `#print axioms` audit are all green with
no in-scope warnings. `BookProof/` is `sorry`-free / `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`); every `Book/*.lean` chapter is included in
`Book.lean` (35 `{include}`s, 36 chapter files; `Book/Trivial.lean` is unused
scaffolding and is not `{include}`d). Of the two historical
mathematical gaps, **both GAP-1 (2026-08-10) and GAP-2 (2026-08-12) are now
CLOSED** (§3); no `BookProof/` module is left unproved and none remains to be
`#check`-ed from `Book/`. The remaining work is the two medium-value
formalization targets `weakValue` (§4.7) and `continuityUnitary` (§4.8), and the
keep-or-delete decision on `Book/Trivial.lean` (§7). The Issues.md doc refresh is
done (chapter count 35/36 and §1 default-targets wording).

---

## 1. Mandatory commands (do not skip)

```bash
export PATH="/home/leo/.elan/bin:$PATH"
cd /home/leo/Projects/timepiece   # repository root (BOOK_PROOF_PLAN.md's /media/… path is stale)

lake build               # default targets: BookProof + Book + Singularity
lake build RandomMap
lake build book
./patches/build-book.sh  # ALWAYS use this wrapper: patches → build → render → postprocess + asserts
                         # NEVER bare `lake exe book` — it skips the <base>-removal step.
```

Reserve `lake build` and `lake build book` for the end of a pass; `lake serve` is
the day-to-day tool. Verify candidate Mathlib names with
`lake env lean --stdin <<< '#check <name>'` before relying on them.

**Invariants that must hold after any change:**
- `grep -rn "sorry" BookProof/ PnpProof/ Singularity/ RandomMap/ UsedRoute/` shows
  only the intentional `UnusedRoute/SchoenfeldPRA.lean:163,178` (and the
  historical `UnusedRoute/Legacy.lean`, `UnusedRoute/RcpEuler.lean` sorries, which
  are quarantined, not default-reachable).
- `grep -rn "^axiom" BookProof/ PnpProof/` is empty.
- No `BookProof/` file imports `PnpProof`, `UnusedRoute`, or `UsedRoute`;
  `grep -rn "import UnusedRoute" RandomMap/` is empty.
- After a fresh clone / `lake update`, run `./patches/apply-verso-patches.sh`
  (`.lake/` is gitignored; the two Verso patches must be re-applied).

---

## 2. Already done (do not redo)

- **Book build pipeline hardened (2026-08-10, this session).** Root cause of the
  non-portable PDF bookmarks: Verso emits `<base href="./">`, so the browser
  resolves `#fragment` ToC links against an absolute `file://` location and a
  printed PDF gets browser-opening bookmarks. `./patches/build-book.sh` now runs
  the patches, the build, the render, `postprocess-html.sh` (removes the base,
  the redirect, the `find/?domain` permalinks, injects screen-only ToC CSS/JS) and
  **asserts** `no <base>` + fragment links. `AGENTS.md` documents it as the only
  supported build path. Current `_out/html-single/index.html` verified clean
  (base count 0, redirect 0, permalinks 0, 316 fragment links with 0 missing
  targets).
- **`BookProof` coherence (2026-07→08).** Every wave of
  `PLAN_LEAN_SPECIALIST_COHERENT.md` landed — Parts A–G plus all attention-layer,
  information-theoretic, control-layer, soft-maximum/circuit and
  decoding/locality packages (≈40 new `Chapter*` files, all registered in
  `BookProof.lean`, certified in `BookProof/ChapterRoadmapAudit.lean`,
  `#check`-ed in `Book/CoherentState.lean`, all `sorry`-free/`axiom`-free).
- **`tailSplitEquiv_map`** and **`mehler_unique_by_finite_marginals`** proved
  (`ChapterSolovayCoordinates.lean`, `ChapterMehlerUniqueness.lean`); the Solovay
  `sorry` is closed.
- **`ChapterSelectingEvents` hardened:** the `True`-placeholders were replaced
  with real conclusions — `exists_regular_conditional_probability` (via
  `condDistrib`/`compProd_map_condDistrib`), `vonNeumann_abelian_classification_typeI`
  (the genuine `Iₙ` case), `exists_continuous_atomic_decomposition`,
  `selecting_events_not_rewriting_history`; the two `axiom : True` lines were
  removed (kept commented-out for the record).
- **Part G isolation closed:** the RH spine moved to `UnusedRoute/`;
  `RandomMap/RandomMap2.lean` imports `BookProof.PhysMehler`, not
  `UnusedRoute.SchoenfeldPRA`; `RcpRandomMap2Bridge.lean` and
  `RandomMap2Phase7.lean` moved; `grep -rn "import UnusedRoute" RandomMap/` empty;
  the promoted `Phys*` modules (`PhysMeasureBasis`, `PhysFunctionalAnalysis`,
  `PhysHSGaussian`, `PhysMehler`) are line-length-clean.
- **Priority 1/2 of `BOOK_PROOF_PLAN.md`** (ODE honesty + PA-free completion):
  all DONE; Priority 4 (26-`{include}` Verso limit) DONE via
  `patches/verso-0001-annotate-subparts.patch`; Priority 5 (honesty-flag refresh)
  DONE; Priority 7 (`book.tex` claims) DONE; Priority 8 (Issues-derived) DONE.
- **GAP-2 closed (2026-08-12).** The abelian von Neumann exhaustiveness wave
  landed: `ChapterLinftyMaximalAbelian`, `ChapterAbelianAtomicCondensation`,
  `ChapterTensorCompleteness`, `ChapterAbelianGelfandModel`,
  `ChapterSpectralMultiplication`, `ChapterSpectralCommutant`,
  `ChapterCyclicDecomposition`, `ChapterCyclicDirectSum`, `ChapterSpectralDirectSum`,
  `ChapterAbelianCyclicModel`, `ChapterAbelianCyclicCommutant`, `ChapterAbelianDirectSum`,
  `ChapterMeasureAtomicDiffuse`, `ChapterDiffuseCdfModel`, `ChapterDiffuseUnitaryModel`,
  `ChapterAtomicDiagonalModel`, `ChapterLpRestrictSplit`, `ChapterLpScaleMeasure`,
  `ChapterAbelianClassificationList`, `ChapterStandardBorelClassification`,
  `ChapterSeparableSpectrum`, `ChapterSeparableL2Model` — all `sorry`-free/`axiom`-free,
  registered in `BookProof.lean`, certified in `ChapterRoadmapAudit.lean`,
  `#check`-ed in `Book/NullMeasure.lean`. The metrizability residue is removed; only a
  nonseparably *acting* algebra is outside the statement.
- **`BookProof` §4 and GAP-1 (2026-08-08→12).** `ChapterCoherentThermalFidelity`
  (displaced-thermal fidelity → `thermalTemperature_eq_fidelity_width_sub_coherent_half`,
  closing **GAP-1**), `ChapterSolovayTailDimension`, `ChapterSolovaySeparableExistence`,
  `ChapterSolovayHilbertTensor`, `ChapterSolovayCrossDim` — closing §4.1–4.6. The
  finite algebraic core (`ChapterThermalTemperatureCore`) is also proved.
- **Verso integrated** on v4.28.0; single-page output decided and locked
  (`emitHtmlSingle := .immediately`, `emitHtmlMulti := .no`).
- **Book prose coverage of §4.7/§4.8 landed (2026-08-12).** The *prose* halves of
  the two BookProof targets are written up and `#check`-ed from the book: the "Weak
  Measurements / weak values" section of `Book/DoubleSlit.lean` (weak-value ratio,
  ABL core in `ChapterTrajectory`, see Proof-Plans appendix §D) and the "Less
  Arbitrary Construction / dynamics-based unitary" sections of
  `Book/ConditionalUnitary.lean` (continuity Hamiltonian `H = ½(p̂·v + v·p̂)`,
  tensor-product identification, Born-rule recovery; Proof-Plans appendix §E).
  The BookProof modules are now **DONE** as well (see §4.7/§4.8 and §9), and the
  unbounded *continuum* generator that was outside the formalized statement is now
  covered by the general Stone theorem (2026-08-20e,
  `ChapterStoneResolvent`–`ChapterStoneSeparable`).
- **Weak measurements / weak values proved (2026-08-12).** `ChapterWeakValue`
  formalizes `⟨A⟩_w = ⟨f|A|i⟩/⟨f|i⟩` on `Fin n → ℂ` (`weakValue_wellDefined`,
  `weakValue_diag`, `weakValue_linear`, `weakValue_proj_sum`,
  `jointProb_eq_normSq_weakNumerator`, `condProb_eq_weakNumerator_ratio`,
  `dslit_weakValue`), closing §4.7. See §4.7 and Proof-Plans appendix §D.
- **Dynamics-based unitary proved (2026-08-12).** `ChapterContinuityUnitary`
  builds `H = ½(p·v + v·p)` on the cyclic lattice, the unitary `e^{iHt}`, the
  Born-rule recovery `bornRecover` and the capstone `condProb_of_continuity`,
  closing §4.8. See §4.8 and Proof-Plans appendix §E.
- **Analytic layer wave (2026-08-13).** `ChapterContinuityUnitaryInfinite` runs
  the dynamics-based construction on `ℓ²(ℤ)` with bounded operators
  (`momentum_isSelfAdjoint`, `velocityOp_isSelfAdjoint`,
  `continuityHamiltonian_isSelfAdjoint`, `continuityUnitary_unitary`,
  `bornRecover_tsum_univ`, `condProb_of_continuity_infinite`);
  `ChapterBornMeasure` proves `P(B) = ∫_B |Ψ|² dμ` is a probability measure on any
  measure space (`bornMeasure`, `isProbabilityMeasure_bornMeasure`,
  `bornMeasure_absolutelyContinuous`, `condProb_of_bounded_dynamics`);
  `ChapterUnboundedPosition` proves the lattice position operator is densely
  defined, symmetric and genuinely unbounded, then self-adjoint
  (`adjointDomain_eq_mulDomain`, `adjoint_eq_mulOp`) and generates its unitary
  group with Stone's relation (`phaseUnitary`, `tendsto_phaseUnitary`,
  `tendsto_slope_phaseUnitary`); `ChapterUnitaryTransport` carries the whole
  package through any unitary change of Hilbert space
  (`transport_isSelfAdjointOn`, `tendsto_transportUnitary`,
  `tendsto_slope_transportUnitary`, `transported_position_isSelfAdjointOn`).
  What remains is the *existence* of a diagonalizing unitary for a general
  unbounded self-adjoint operator (the spectral theorem behind a continuum
  Laplacian) — a research target, not a plan item (see §9).
- **Display-math fix (2026-08-12).** Five display equations in
  `Book/FreeField.lean` and `Book/SolovayTensor.lean` wrote `$$` on its own line,
  which Verso emits as literal text + a plain `<code>` block that KaTeX never
  touches. Rewritten in the working form (`$$` immediately before the backtick);
  rebuilt book + `check-katex.sh` (1818 snippets, 0 failures). A remaining
  `Issues.md` §0b/§4 count (38/39) was refreshed to the actual 35 `{include}`s /
  36 chapter files.
- **The Navier–Stokes thread is now proved (2026-08-14→15, the
  `PLAN_LEAN_SPECIALIST_NS_FLOW.md` wave).** The whole plan landed in 27 new
  `BookProof/ChapterNavierStokes*.lean` + `ChapterFarisLavine.lean` +
  `ChapterH8*.lean` + `ChapterH9.lean` modules (registered in `BookProof.lean`),
  all `sorry`-free / `axiom`-free, `#check`-ed from the book. In dependency
  order: the **truncation** — `ChapterNavierStokesFlow` (Hermitian
  `nsHamiltonian`, polynomial of degree ≤ 3, complete unitary flow
  `nsFlow_unitary`/`nsFlow_noBlowup`, zero deficiency `nsHamiltonian_hasZeroDeficiency`),
  `ChapterNavierStokesCauchy` (unique global solution `nsCauchy_existsUnique`),
  the BRST/divergence constraint `nsBrst_nilpotent`/`nsDivergenceConstraint_resolution`,
  the Lagrangian change of variables (`volume_preservation_constraint`,
  `transformed_hamiltonian_decomposition` with positive kinetic/viscous terms);
  then the **analytic layer** — `ChapterNavierStokesEsa` (Nelson's complete-flow
  criterion `hasZeroDeficiencyOn_of_completeUnitaryFlow`, bounded-symmetric ESA on
  a proper dense domain), `ChapterNavierStokesDeficiency` (the limit-circle Jacobi
  counterexample: symmetry alone is not ESA), `ChapterNavierStokesFarisLavineLift`
  + `ChapterNavierStokesFock*` (second quantization, the comparison operator
  `n = Σπᵢ² + ΣVᵢ² + I` with `N̂ ≥ I`, the Fock-of-Fock lift where the
  form-commutator bound lifts but the operator bound does not,
  `not_forall_norm_sum_le_of_pointwise`), `ChapterNavierStokesIkebeKato`
  (maximal-domain multiplication operators: `N+1` onto, finite-mode graph cores),
  `ChapterNavierStokesMomentumEsa` (ESA of the one-particle and Fock-space
  Navier–Stokes Hamiltonian on the finite-mode core), and
  `ChapterNavierStokesHermiteFarisLavine`/`ChapterNavierStokesFockFarisLavine`/
  `ChapterNavierStokesShiftHamiltonian`/`ChapterNavierStokesFockManyMode` (the two
  Faris–Lavine inequalities **proved** for the Hamiltonian itself — relative bound
  `‖Hx‖² ≤ ½‖Nx‖² + …` and commutator bound `|⟨x,i[H,N]x⟩| ≤ c⟨x,Nx⟩` — with a
  genuinely non-vanishing commutator `fock_commForm_ne_zero`).
- **Faris–Lavine commutator criterion proved (2026-08-15h).**
  `BookProof/ChapterFarisLavine.lean` proves Theorem 1 and Corollary 1.1 of Faris
  & Lavine, *Commutators and self-adjointness of Hamiltonian operators*, CMP 35
  (1974) 39–48 — `essentiallySelfAdjointOn_of_farisLavine`,
  `essentiallySelfAdjointOn_core_of_farisLavine`, the resolvent-estimate core
  `deficiencyTrivialAt_of_farisLavine` and the sharpness refutation
  `not_farisLavine_criterion_of_relative_bound` (relative-bound-only is false,
  via the limit-circle Jacobi operator). The criterion that
  `ns_esa_of_farisLavine_dense` carried as a named hypothesis is now a proved
  theorem, and `hasZeroDeficiencyOn_of_farisLavine` delivers it in the chapter's
  own predicate.
- **SIRK nesting completed (2026-08-14→15, `PLAN_LEAN_SPECIALIST_SIRK_NESTED.md`
  + its spectral side).** `ChapterH8` proves the approximant nesting — the
  subspace tower `sirk_krylov_tower`, block compatibility `sirk_compression_block`,
  the projection identities `sirk_band_refinement(_poly/_rational)` and
  `sirk_approx_projection(_poly/_rational)`, with hypothesis-free realizations via
  orthonormal Krylov bases (`krylovOrthonormal_span`, `sirk_band_refinement_krylov`);
  `ChapterH8Bases` provides the Gram–Schmidt orthonormal Krylov bases; `ChapterH9`
  adds the spectral face — the numerical ranges nest
  `W(Bₘ) ⊆ W(Bₙ) ⊆ W(X)` (`sirk_numRange_nested_orders`, `sirk_numRange_krylov`),
  the norms nest, Ritz values and Ritz spectra nest
  (`ritz_mem_numRange(_compress)`), and the *unconditional* best-approximation
  antitone/tend-to-zero (`krylov_bestApprox_antitone`,
  `krylov_bestApprox_tendsto_zero`, no Crouzeix constant). Honest boundaries kept:
Crouzeix's inequality stays a named hypothesis; no rate; no Toeplitz–Hausdorff
   convexity; `W(Bₙ)` grows with the order so band decay comes from approximation
   quality.
- **Eulerian constraints + gauge generators landed (2026-08-16,
  `PLAN_LEAN_SPECIALIST_NS_FLOW.md` Part A.5 + Part E.3).** Two new modules,
  `ChapterNavierStokesEulerian.lean` and `ChapterNavierStokesGaugeY.lean`
  (registered in `BookProof.lean`, cited from `Book/FreeField.lean`), both
  `sorry`-free / `axiom`-free, completing the Eulerian side of the
  derivatives-as-fields construction:
  - `ChapterNavierStokesEulerian` — the Eulerian counterpart of the Lagrangian
    constraints: the Eulerian field collapse `u_evaluates_to_value`
    (`u_i(X) = u_i + u_{i,j}(X_j − x_j)` → `u_i` on position eigenstates), the
    full momentum CCR family `eulerian_momentum_constraint` (`[u_j, π^k] =
    iδ^k_j` plus the derivative-mode CCRs) and `eulerian_momentum_dual`, the
    gauge-generator derivative relations `derivativeField_relates_to_field`
    (`u_{i,j} = ∂_j u_i`), `derivativeField_second`, `derivativeField_consistency`
    (Clairaut), the initial-condition-imposed `eulerian_divergence_constraint`
    (`u_{3,3}` substitution) with non-empty witness
    `cyclicShear_divergence_free` — and the correction to optional E.3:
    `nsBrst_not_hermitian` (the BRST charge is **not** Hermitian when the
    divergence is non-zero; the honest Hermitian statement is the symmetrized
    packaging `nsBrst_symmetrization_hermitian`).
  - `ChapterNavierStokesGaugeY` — the second-coordinate refinement: the field in
    the Hamiltonian is `u_i(y) = u_i + u_{i,j}y_j` (`uField`), with two gauge
    generators — `genX = ∂/∂x_j` (the standard momentum) and
    `genY = ∂/∂y_j − u_{i,j}∂/∂u_i` (the generator built from the derivatives of
    `u_i`). Both annihilate the field and the NS symbol, commute (abelian, hence
    first class), the coefficient `u_{i,j}` is the *only* admissible one
    (`genY_uField_perturbed_ne_zero`), and at the initial state `y = 0` the field
    collapses to `u_i` and the Hamiltonian acts as the ordinary NS one
    (`setYZero_uField`, `hamiltonianOp_apply_of_y_zero`).
- **Quantum Gravity + Quantum Yang–Mills plan items executed, plus the
  Hashimoto/Galerkin–Friedrichs extension (2026-08-17).** The §10.3 / §11.3
  "suggested next step" items are written up as `PLAN_LEAN_SPECIALIST_QG_FLOW.md`
  and `PLAN_LEAN_SPECIALIST_QYM_FLOW.md` and executed by new `sorry`-free /
  `axiom`-free modules (see the leading Status block for the full name-by-name
  accounting). Three further modules extend the Hashimoto/Galerkin machinery that
  backs the QYM Friedrichs route:
  - `ChapterHermiteGalerkinFriedrichs.lean` — a Galerkin/Rayleigh–Ritz truncation
    in a complete (Hermite) basis converges to the Friedrichs (energy-form)
    extension; `galerkinCompression`, `ritzInf_antitone`,
    `ritzInf_tendsto_domainInf`, `galerkinCompression_tendsto`, strong resolvent
    convergence `galerkinResolvent_tendsto`, `positive_selfadjoint_extension_unique`
    (Hellinger–Toeplitz + density), headline `hermiteGalerkin_selects_friedrichs`.
    The bounded case is discharged (`finiteModeRestrict_selects_operator`); the
    unbounded non-ESA case is not claimed. Doc-map: `HERMITE_GALERKIN_FRIEDRICHS.md`.
  - `ChapterHashimotoShiftInvert.lean` — the shift-invert trick frees the
    Galerkin–Friedrichs theory of its boundedness hypothesis: for a positive
    Hamiltonian `H`, `‖(H+γ)x‖ ≥ γ‖x‖` makes `R = (H+γ)⁻¹` bounded (`‖R‖ ≤ 1/γ`)
    however unbounded `H` is; `R` determines `H` (`shiftInvert_determines`), and
    `hashimoto_shiftInvert_selects_friedrichs` reaches unbounded Hamiltonians, with
    the number operator on `ℓ²(ℕ,ℂ)` as the genuinely unbounded example.
  - `ChapterHashimotoComplexShifts.lean` — the same theory for the complex, non-real
    shifts of the Hashimoto–Nodera Shift-invert Rational Krylov method: `|Im γ|`
    alone bounds `‖(γ−A)x‖` (no positivity), the resolvent `X = (γI−A)⁻¹` has
    `‖X‖ ≤ 1/|Im γ|`, the resolvent identity and rational-Krylov structure
    (`shiftInvertC_resolvent_identity`, `shiftInvertC_commute`), and
    `hashimoto_multishift_selects_friedrichs`. Doc-map: `HASHIMOTO_COMPLEX_SHIFTS.md`.
  All are registered in `BookProof.lean`, certified in
  `ChapterRoadmapAudit.lean` (`#print axioms`, only `propext`,
  `Classical.choice`, `Quot.sound`), and cited from
  `Book/DiffeomorphismsGravity.lean` and `Book/YangMillsQuantization.lean`.
- **Strichartz wave-operator ESA + Hermite core + unbounded Friedrichs (2026-08-18,
  the "wave" of §11.4 items 1–2 and the QG Strichartz step).** Seven new modules,
  all `sorry`-free / `axiom`-free, registered in `BookProof.lean` and certified in
  `ChapterRoadmapAudit.lean`:
  - `ChapterStrichartzWave` — `□ = −∂_t² + Δ_x` plus a real constant is essentially
    self-adjoint on the Schwartz core of `L²(ℝ^{1+n})`; all constant-coefficient
    real-symbol operators too (`constCoeffOp_essentiallySelfAdjoint`), by the
    Fourier/multiplier argument (Plancherel + real symbol), with the smooth cut-off
    lemma `exists_smooth_cutoff` as the first ingredient of the general energy
    argument.
  - `ChapterKatoRellichDeficiency` — bounded symmetric perturbations preserve ESA,
    from scratch in the deficiency formulation (explicit Neumann series, no
    closure/spectral theory): `essentiallySelfAdjointOn_add_bounded`.
  - `ChapterWaveBoundedPotential` — `□ + V` is ESA on the Schwartz core for every
    essentially bounded real `V`.
  - `ChapterHermiteFunctions` — the genuine Hermite orthonormal basis of `L²(ℝ)`
    (`hermiteBasis`, completeness via Fourier uniqueness, `hermiteFun_oscillator`).
  - `ChapterStrichartzHermiteQG` — the Hermite core (finite combinations of Hermite
    functions, dense), diagonal operators on it with real symbol (ESA on the core,
    trivial deficiency at every non-real `z`, unbounded), the harmonic oscillator,
    and the 3D gauge-fixed QG mode Hamiltonian
    `qg3D_essentiallySelfAdjoint_on_hermiteCore` (now realized on `L²(ℝ)`, not
    abstractly on `ℓ²(ℕ)`).
  - `ChapterFriedrichsExtension` — the **Friedrichs extension theorem with no
    boundedness hypothesis** (`friedrichs_extension_exists`): the form inner
    product, its completion `FormSpace`, injectivity of the extension
    (`formExt_injective`, the closability step), Riesz representation of
    `(H+1)⁻¹`, and `A = S⁻¹ − 1`. `friedrichs_hypothesis_holds` retires the named
    hypothesis of `friedrichs_extension_of_semibounded`;
    `weyl_friedrichs_extension_unconditional` gives the Weyl-gauge conclusion;
    `friedrichs_hashimoto_selects` / `weyl_hashimoto_selects_friedrichs` combine it
    with shift-invert (the Hashimoto/SIRK limit selects the constructed extension,
    unbounded), and `unbounded_friedrichs_example` (A eₙ = n·eₙ) shows it is not
    vacuous. **This closes §11.4 items 1 and 2** (item 2 settled in favour of the
    occupation-number/Hermite realization, Part E of
    `PLAN_LEAN_SPECIALIST_QYM_FLOW.md`). Doc-maps: `STRICHARTZ_WAVE_ESA.md`,
    `HERMITE_CORE_STRICHARTZ.md`.
  - `UsedRoute` wave: `RectangleWinding` (the Cauchy-integral/rect winding-number
    core), `GaussianEuler` (+147, re-powering the rectangle strategy with Gaussian
    Euler products) and `RectangleStrategy` (+49); registered in `UsedRoute.lean`.

---

## 3. The two documented mathematical gaps (BookProof, high value)

**Update (2026-08-12): both historical gaps are now CLOSED.**

- **GAP-1 closed** (2026-08-10) by `ChapterCoherentThermalFidelity` — the zero-point
  half of `τ = n̄ + ½` is derived from the coherent-state overlap, not postulated.
- **GAP-2 closed** (2026-08-12) by the abelian-classification wave — the five-type
  exhaustiveness is established; only a nonseparably *acting* algebra is outside
  the statement.

Both were **documented gaps, not `sorry`s** — and remain so. The sections below
record the history and the explicit closure; do not reopen them.

### GAP-1 — Physical derivation of `τ = n̄ + ½` (Part A.4 / F.4)

Status: **CLOSED (2026-08-10).** The finite algebraic core was proved first
(`ChapterThermalTemperatureCore.lean`: `geometricOccupancy_mean`,
`geometricOccupancy_variance`, `half_integer_floor`, `thermal_temperature_eq_mean_half`).
The physical derivation is `ChapterCoherentThermalFidelity.lean`:

- `coherentThermalFidelity nbar lam = ∑ₙ |⟨β|n⟩|²·Pr_th(n)` — thermal state vs
  coherent state in Fock coordinates;
- `coherentThermalFidelity_eq` — collapses to `exp(−λ/(n̄+1))/(n̄+1)`, a Gaussian of
  width `n̄ + 1`;
- `coherentThermalFidelity_vacuum_eq_fidelityC` — at `n̄ = 0` this is the coherent
  fidelity `exp(−‖q−k‖²)`, fixing the coherent-state width `coherentWidth = ½`
  (via `fidelityC_width` `½ + ½ = 1`);
- `coherentThermalFidelity_width_eq` — widths add: `n̄ + 1 = τ + ½`;
- **headline** `thermalTemperature_eq_fidelity_width_sub_coherent_half` — the width
  of the fidelity determines the temperature (`τ = w − ½`), so `τ = n̄ + ½` is *read
  off* the fidelity. The extra half is exactly the coherent-state overlap.

`sorry`-free / `axiom`-free, registered in `BookProof.lean`, `#check`-ed in
`Book/CoherentState.lean`. Recorded as CLOSED in `BookProof/STATUS.md` (wave
2026-08-10).

### GAP-2 — Exhaustiveness of the abelian von Neumann classification (Part B.4 / F.5)

Status: **CLOSED (2026-08-12).** The four concrete classes were proved first —
finite `Iₙ` (`ChapterAbelianDiagonal`), countable `ℓ∞(ℕ)`
(`ChapterAbelianDiagonalCountable`), diffuse `L∞(μ)` (`ChapterLinftyMultiplication`),
mixed atomic-plus-diffuse (`ChapterAbelianMixture`). The exhaustiveness claim —
every abelian `*`-algebra on separable `L²` is `*`-iso to one of the five standard
types — is now established (the full von Neumann theorem, out of Mathlib).

**Update (2026-08-12): essentially closed.** The condensation was carried out in
full: `ChapterLpRestrictSplit` (the `L²` splitting along a measurable set),
`ChapterLpScaleMeasure` (rescaling the measure is a unitary),
`ChapterAbelianClassificationList` (the five-type list for a Borel probability
measure on the line) and `ChapterStandardBorelClassification` (Borel-isomorphism
transport; every summand of the general abelian model realises one of the five
standard types, for a compact metrizable spectrum). All `sorry`-free / `axiom`-free.

**Update (2026-08-12, later the same day): the metrizability residue is closed.**
`ChapterSeparableSpectrum` proves that, for a compact Hausdorff spectrum,
metrizability of the spectrum is *equivalent* to separability of the algebra of
continuous functions, and discharges it for every separable commutative unital
C*-algebra via Gelfand duality.  `ChapterSeparableL2Model` then removes it outright
in the separably acting case: a separable `L²` is carried, by a countable dense
family of continuous functions, unitarily onto an `L²` over a standard Borel space,
so every abelian algebra of operators on a separable complex Hilbert space is a
countable direct sum of multiplication algebras each realising one of the five
standard types.  Both modules are `sorry`-free / `axiom`-free.  The only case now
left outside the statement is a nonseparably *acting* algebra.

Definition of done: attempt the provable condensation — e.g."every abelian,
star-closed, unital algebra on `L²` whose projections are purely atomic is
`*`-isomorphic to `ℓ∞(ℕ)` (or `Iₙ`)"; finite convex combinations reduce to the
mixture class. If out of reach, record the exact obstruction in
`BookProof/STATUS.md` — do **not** `sorry`.

---

## 4. BookProof tasks from the older plans (medium value, isolated)

**Update (2026-08-12): these are now all LANDED** — the copied wave closed every
item originally listed here. They are kept as a record only; do not redo them.

- **4.1 `tail_infinite_dimensional` (Task B2b).** DONE — `ChapterSolovayTailDimension`
  proves `¬ FiniteDimensional ℝ InnerTail` (infinite orthonormal family).
- **4.2 Hilbert-space tensor identification (Task B2, "heavier" half).** DONE —
  `ChapterSolovayHilbertTensor` gives `solovayTensorEquiv` (the Hilbert-space form
  of the tensor isomorphism, with `solovayTensorEquiv_map` / `solovayTensorUnitary`).
- **4.3 Cross-dimensional inner product (Task B5 / `BOOK_PROOF_PLAN.md` 6.6).**
  DONE — `ChapterSolovayCrossDim`: `cross_dim_embedding` (enlarging `N ↦ N + k` is
  measure-preserving) and the expectation/norm-pairing identities via
  `inner_reduces_to_head`.
- **4.4 `joint_prob_has_wavefunction` (Task D1).** DONE —
  `ChapterSolovaySeparableExistence` proves `joint_prob_has_wavefunction` and the
  product form `joint_prob_has_wavefunction_prod`.
- **4.5 `exists_separable_prob_with_arbitrary_finite_law` (Task D3).** DONE —
  `ChapterSolovaySeparableExistence` proves
  `exists_separable_prob_with_arbitrary_finite_law` (and the substrate form).
- **4.6 Disintegration via `prod_disintegrate` (Task D2).** DONE —
  `ChapterSolovaySeparableExistence` carries the explicit `prod_disintegration`
  companion (`μ = μ.fst ⊗ₘ κ`) alongside the `condDistrib` route in
  `ChapterSelectingEvents`.

All of the above are `sorry`-free / `axiom`-free, registered in `BookProof.lean`,
certified in `BookProof/ChapterRoadmapAudit.lean`, and `#check`-ed from
`Book/CoherentState.lean`, `Book/NullMeasure.lean` and `Book/SolovayTensor.lean`.

No remaining work item of this section is open.

**Addition (2026-08): weak measurements / weak values (book.tex "Reconstruction of
the trajectory"; the double-slit chapter's "Weak Measurements" section).** The
post-selection / ABL core is proved (`ChapterTrajectory`); the weak-value ratio
itself is not. Medium value, small and self-contained — a natural next target:

- **4.7 `weakValue` (ChapterWeakValue).** **DONE (2026-08-12).**
  `BookProof/ChapterWeakValue.lean` defines `ip` (the standard inner product on
  `Fin n → ℂ`) and `weakValue i f A = ip f (A *ᵥ i) / ip f i`, and proves
  `weakValue_wellDefined` + `weakValue_unique` (the ratio is the unique solution of
  `w·⟨f|i⟩ = ⟨f|A|i⟩` when `⟨f|i⟩ ≠ 0`), `weakValue_diag` and
  `weakValue_diag_isReal`, `weakValue_add`/`weakValue_smul`/`weakValue_linear`,
  `weakValue_proj`/`weakValue_proj_sum`, the ABL ties
  `jointProb_eq_normSq_weakNumerator` and `condProb_eq_weakNumerator_ratio`, and the
  double-slit capstone `dslit_weakValue`. `sorry`-free / `axiom`-free, registered in
  `BookProof.lean`, certified in `ChapterRoadmapAudit.lean`, cited from
  `Book/DoubleSlit.lean`.

- **4.8 `continuityUnitary` (ChapterContinuityUnitary).** **DONE (2026-08-12).**
  `BookProof/ChapterContinuityUnitary.lean` works on the cyclic lattice `ZMod N`
  with the symmetric-difference momentum: `continuityHamiltonian v = ½(p·v + v·p)`
  with `continuityHamiltonian_hermitian` (and
  `momentum_mul_velocityOp_not_hermitian`, showing the symmetrization is needed),
  `continuityUnitary v t = exp (i t H)` with `continuityUnitary_unitary`,
  `continuityUnitary_zero`, `continuityUnitary_add`, the Born recovery
  `bornRecover` (`_nonneg`, `_empty`, `_union`, `_mono`, `_univ`) and `bornPMF`,
  the finite tensor identification `tensorIsom`/`tensorIsom_tmul` with
  `bornRecover_product_state`, and the capstone `condProb_of_continuity`.
  `sorry`-free / `axiom`-free, registered in `BookProof.lean`, certified in
  `ChapterRoadmapAudit.lean`, cited from `Book/ConditionalUnitary.lean`. The
  infinite-dimensional analytic layer is now also proved for the bounded case and
  for the lattice position operator (§4.9), and the continuum Laplacian's
  diagonalizing unitary — Stone's theorem in full generality — is now proved
  outright (2026-08-20e, `ChapterStoneResolvent`–`ChapterStoneSeparable`).

- **4.9 The analytic layer of §4.8 (2026-08-13, DONE as bounded + lattice).**
  `ChapterContinuityUnitaryInfinite` (the construction on `ℓ²(ℤ)` with bounded
  operators), `ChapterBornMeasure` (the Born law as a probability measure on any
  measure space), `ChapterUnboundedPosition` (the lattice position operator is
   densely defined, symmetric, unbounded, then self-adjoint and generating its
   unitary group with Stone's relation) and `ChapterUnitaryTransport` (unitary
   invariance of the whole package). The general Stone theorem — the generation of
   the unitary group for *any* unbounded self-adjoint operator on a separable
   Hilbert space — is now proved (2026-08-20e,
   `ChapterStoneResolvent`–`ChapterStoneSeparable`); what remains open is the
   spectral theorem (the *existence* of the diagonalizing unitary for a specific
   continuum operator such as the Laplacian). See §2 and §9.

---

## 5. Issues.md — full disposition

| § | Item | Status now | Action required |
| :-- | :-- | :-- | :-- |
| 0 | verso-blueprint needs Lean ≥ v4.29.0 (project pinned v4.28.0) | **[BLOCKER]** | **Keep Verso v4.28.0 manual as the deliverable.** Adopt blueprint **only** when a toolchain exists that is *both* blueprint-compatible *and* supported by `aristotle.harmonic.fun` (see `BOOK_PROOF_PLAN.md` §3.2). Do not bump toolchain/Mathlib in this repo meanwhile. |
| 0b | Current state of this deliverable | **RESOLVED (2026-08-12)** | Issues.md §0b refreshed to the actual tree: 35 `{include}`s / 36 chapter files (`Book/Trivial.lean` unused scaffolding, not `{include}`d). Re-verify only when the chapter set next changes. |
| 1 | Transitive dependency pins (subverso/MD4Lean/plausible chosen by date) | **LOW RISK, untracked** | Leave pinned; re-derive **only** if a Verso/Mathlib upgrade is ever attempted. Do not upgrade in this repo. |
| 1 | Full `lake build BookProof` recompile integrity | **RESOLVED** | Re-run once per release cycle; the latest `lake build` is green. |
| 1 | `book` is intentionally not a default target | **RESOLVED** | `defaultTargets` is now `["BookProof", "Book", "Singularity"]`; `Issues.md` §1 records the `["PnpProof", "BookProof"]` wording as **UPDATED**. Re-verify only if `lakefile.toml` changes. |
| 2 | Curated-edition coverage table | **RESOLVED (verified 2026-08-21i)** | The "deferred" physics chapters have since been **written up**: `GaugeSymmetry`, `PhysicalParity`, `YangMillsQuantization`, `RealRepresentations`, `DiffeomorphismsGravity`, `AlignedDeepLearning`, `GribovAmbiguity`, `ConsciousnessBayesianPrior` all exist under `Book/` and are **included** in `Book.lean`. The §6 "deferred" list should be re-marked `DONE (framing settled)` or moved to Contention dispositions. |
| 2 | Sketch proofs re-derived, not transcribed | **OPEN, editorial** | No build action; cross-check any less-standard claim against `book.tex` before publication (see Contention §7). |
| 3 | `newproof.md` layers (verified core vs philosophical claim) | **RESOLVED** | `Book/PaFreeHilbert.lean` keeps the compartments separate; no action. |
| 4 | KaTeX coverage | **RESOLVED (2026-08-18b)** | `./patches/build-book.sh` followed by `./patches/check-katex.sh` re-renders every math snippet of the built page with `throwOnError: true`: **2129 snippets, 0 failures**, matrices included. Re-run the two scripts after any chapter edit. |
| 4 | Long `#check` types | **MOSTLY RESOLVED** | Readable prose paraphrases exist for the worst offenders; restate any remaining unwieldy `#check` as a clean `example` when a chapter is next edited. |
| 4 | Single-page, menu-free HTML decision | **DONE** | Locked in `BookMain.lean`. |
| 4 | 26-`{include}` limit | **DONE** | Verso patch `verso-0001`; re-apply after fresh clones. |
| 4 | Multi-line `**bold**` wrapping inline math | **GOTCHA (live rule)** | Keep bold-with-math on one line; re-check on any edit to a `Book/*.lean` chapter. |
| 5 | Output formats (single-page HTML; TeX/PDF disabled) | **DECIDED** | Single-page HTML is the deliverable. The PDF-bookmark fix in §2 was the PDF concern; do **not** enable `emitTeX` unless author explicitly asks. |
| 7 | Abstract measure-theoretic layer of `book.tex` §3 | **RESOLVED (2026-08-12)** | The finite core + `condDistrib` kernel was done; the abstract layer (five-type classification, `≅ L∞` commutative-von-Neumann passage, disintegration on standard Borel) is now **CLOSED** by the GAP-2 wave (§3) + §4.6. Only a nonseparably *acting* algebra is outside the statement. |
| 7 | Remaining non-deferred gaps (two) | **GAP-1 CLOSED (08-10); GAP-2 CLOSED (08-12)** | No mathematical target remains; see §3. |

---

## 6. Contention.md — full disposition

Governing rule (from `Book/Introduction.lean` and Contention's conventions): the
book is a **deliberate re-selection** ("selects the threads whose mathematics is
both self-contained and already formalized"), and nothing in `Book/` contradicts
`book.tex`. Dispositions:

| Item | Claim vs `book.tex` | Status | Action required |
| :-- | :-- | :-- | :-- |
| D1 | Intro slogan "QM is what probability theory looks like…" (drops the "(not of probability theory)" caveat) vs the caveat *preserved* in `DeterministicTransformations` | **INTERNAL TENSION** | **Resolve the internal disagreement.** Either add the caveat to `Introduction` (align with `DeterministicTransformations`) or explicitly frame the slogan as rhetoric with the caveat in a footnote that cross-references `DeterministicTransformations`. Should be a one-line edit; flag to author. |
| D2 | ODE chapter claims both blow-up problems resolved; manuscript says the second is "not completely satisfactory" | **OVERCLAIM** | Add one honesty sentence to `Book/OdeSingularity.lean` (near lines 45–48) reporting the manuscript's own caveat, mirroring the honesty-flag style used for the ODE theorems. |
| D3 | Essential self-adjointness reduced to algebraic certificate layer | **DISCLOSED** | Keep as is; ProofPlans A.1–A.2 already defer the analytic realization. |
| D4 | "most general formalism" softened to "generalizes statistical mechanics" | **DELIBERATE** | Keep. |
| D5 | Navier–Stokes existence/uniqueness thesis not carried by any chapter | **PARTIALLY ADDRESSED (2026-08-15)** | Keep the scope discipline — no theorem claims continuum NS existence/uniqueness. But `Book/FreeField.lean` now carries a full "Navier–Stokes Hamiltonian: a Complete Flow on the Truncation" section (complete unitary flow, unique global Cauchy solution, BRST constraint, Lagrangian change of variables, Faris–Lavine route), and `Book/YangMillsQuantization.lean` now has the one-line pointer to that formalized subset. |
| D6 | Weak holomorphicity weakened to strong pointwise | **DISCLOSED** | Keep; documented in the module; not imported by any chapter. |
| D7 | Arrow of time reframed from unitarity to dissipation/set theory | **DELIBERATE REFRAME** | Keep; it is the thesis of Chapters III. If the author wants the manuscript's "due to unitarity" framing, that is a prose decision, not a Lean one. |
| D8 | Consciousness thesis reduced | **NOW LARGELY RESOLVED** | A full `Book/ConsciousnessBayesianPrior.lean` chapter now exists (no-best-prior, prior dependence, null-measure). Verify it expresses "no prior / no point is special" faithfully and re-mark Contention D8 as addressed; the AI-hallucination/misalignment half stays out of scope. |
| D9 | Handwritten RH claim dropped; only the metamathematical motivation kept | **DELIBERATE** | Keep; `PaFreeHilbert` + `SolovayTensor` are the intended replacement. |
| S1–S10 | Scope selections (narrowing, not contradiction) | **DELIBERATE** | Keep. No action. |
| A1–A8 | Additions (content in `Book/` not in manuscript) | **DELIBERATE, fine** | Keep. Optionally mark them "additions per author" in the Contention doc. |

**Concrete now-actionable items: D1 and D2** (prose honesty/consistency, one-line
edits each). Everything else is already deliberate or already addressed by the
now-written chapters.

---

## 7. Hygiene residue (small, cosmetic)

- `BookProof/B1_randomMap2_axioms.lean` and `BookProof/randomMap2_axioms.lean`
  still `import` RH modules (`UnusedRoute.SchoenfeldPRA`). They are in **no build
  target**, so the default build is clean. **DONE (2026-08-12):** both now carry an
  explicit "Audit-only module (not in any build target)" docstring and are kept as
  the audit trail.
- Root `RiemannProof.lean` now `import UnusedRoute.RcpRandomMap2Bridge` (repointed
  in this wave); the §7 "repoint the import" item is **RESOLVED**.
- `patches/build-book.sh` is tracked; `patches/check-katex.sh` is tracked with the
  executable bit set (mode `100755`) — the §7 "untracked" item is **RESOLVED**.
- `SpecialFiles`: **DECIDED (2026-08-12) — keep `Book/Trivial.lean`.** It is a
  two-section scaffold used to reproduce the Verso section-count threshold; it is
  not `{include}`d, costs nothing to build, and is worth retaining as a minimal
  reproducer should the Verso patches ever need to be re-derived. The file now says
  so in its own text.
- **`UsedRoute` build repaired (2026-08-17).** `UsedRoute/TwoLimits.lean` carried no
  imports at all and `UsedRoute/SimplifiedStrategy.lean` was missing
  `UsedRoute.Basic` / `UnusedRoute.Legacy`, so `lake build UsedRoute` failed. The
  missing imports were added and `lake build UsedRoute` is now green (0 errors).
  `UsedRoute` is **not** a default target, and `RandomMap` only imports the
  sorry-free `UsedRoute.Basic` / `UsedRoute.SolovayHilbert`, so this does not affect
  the §8 gate. Residue: **26** legacy RH-route declarations still use `sorry`
  (was 33). In this wave `UsedRoute/SimplifiedStrategy.lean` went from 10 to 4:
  `σ_P_lt_one` (restated with the necessary hypothesis `2 ≤ P`; the original claim
  is false for `P ≤ 1`), `σ_P_tendsto`, `corrected_partial_sums_bounded`,
  `S_smooth_analyticAt`, `f_P_analyticOnNhd`, `eulerProd_analyticOnNhd`,
  `eulerProd_ne_zero` and `eulerProd_tendsto` are now proved. The four remaining
  ones there (`corrected_bohr_cahen_tail`, `f_P_converges_to_recip_zeta_above_one`,
  `f_P_uniform_convergence`, `simplified_euler_approx_on_ball`) are the deep
  RH-equivalent content and stay open.

---

## 8. Definition of done (whole consolidated plan)

```bash
# 1. Builds green, no in-scope warnings
lake build && lake build RandomMap
# 2. Book builds through the wrapper, invariants hold
./patches/build-book.sh     # asserts: no <base>, fragment links present
# 3. Sorry/axiom audit
grep -rn "sorry" BookProof/ PnpProof/ Singularity/ RandomMap/ UsedRoute/ | grep -v UnusedRoute
grep -rn "^axiom" BookProof/ PnpProof/    # empty
# 4. Isolation audit
grep -rn "import PnpProof" BookProof/ Book/ Singularity/ RandomMap/
grep -rn "import UnusedRoute" RandomMap/
# 5. GAP-1 / GAP-2 closures recorded in BookProof/STATUS.md (proved, no sorry)
```

No mathematical gap (§3) remains; both GAP-1 and GAP-2 are closed and their
closures are already recorded in `BookProof/STATUS.md` (waves 2026-08-10 and
2026-08-11/12).

---

## 9. Suggested attack order for the next agent

**Update (2026-08-17): the NS thread, the QG route and the QYM route are all
executed; the remaining work is the recorded research boundaries.** D1/D2 prose
cleanups are done, **GAP-1** and **GAP-2** are closed, §4 is fully landed, the
Navier–Stokes thread (`PLAN_LEAN_SPECIALIST_NS_FLOW.md`, 29+ modules) is proved
including its Eulerian/GaugeY side and — 2026-08-20/20b/20c/20d — its abstract
sequence-space ESA chain (bilinear, affine, arbitrary signs, three coupled
components), the ESA-closure/Hashimoto selection of item 8 and the Lagrangian
Kato–Rellich route of item 9, plus the `E.6` BRST-doublet / Gauge-Fixing-Fermion
skeleton, the §8
gate is green, the **general Stone theorem** is proved in full on separable
Hilbert spaces (2026-08-20e, `ChapterStoneResolvent`–`ChapterStoneSeparable`),
and the two further plan items are closed:
* **Quantum Gravity** (`PLAN_LEAN_SPECIALIST_QG_FLOW.md`, executed by
  `ChapterQuantumGravityDensitized.lean` + `ChapterQuantumGravityHalfDensity.lean`,
  cited from `Book/DiffeomorphismsGravity.lean`) — the densitized change of
  variables, the flat hyperbolic principal part, the Hermite-basis ESA (unbounded,
  trivial deficiency at every non-real `z`), Strichartz as a named hypothesis, and
  the *constructed* half-density unitary transfer.
* **Quantum Yang–Mills** (`PLAN_LEAN_SPECIALIST_QYM_FLOW.md`, executed by
  `ChapterYangMillsFriedrichs.lean` + `ChapterYangMillsFriedrichsLimit.lean`, cited
  from `Book/YangMillsQuantization.lean`) — the Weyl-gauge sum-of-squares form, its
  closability, the Friedrichs extension as a named theorem, and the Hashimoto-limit
  identification proved in the bounded regime. Plus the supporting Hashimoto
  extension (`ChapterHermiteGalerkinFriedrichs`, `ChapterHashimotoShiftInvert`,
  `ChapterHashimotoComplexShifts`).

For a future pass, the remaining work is the **recorded research boundaries** —
none of which is a plan item:

1. Re-run the **§8 verification gate** after any change. **Done (2026-08-17):**
   the gate is green in this repository on all the copied-in waves (see the
   leading Status block).  **Re-run 2026-08-18c and green:** `lake build`
   (8630 jobs), `lake build RandomMap` (8039 jobs) and `lake build UsedRoute` all
   complete with no errors; no `sorry` and no `axiom` declaration in `BookProof/`,
   `PnpProof/`, `Singularity/`, `RandomMap/` (only prose mentions); the isolation
   greps are empty; `./patches/build-book.sh` re-renders the book with its asserts
   holding and `./patches/check-katex.sh` reports 2135 snippets, 0 failures.  The
   quarantined legacy RH route still carries 28 `sorry`ed declarations in
   `UsedRoute/` / `UnusedRoute/` (neither is a default target).
   **Re-run 2026-08-18b and green:** `lake build`
   (BookProof + Book + Singularity) and `lake build RandomMap` complete with no
   errors; no `sorry` and no `axiom` declaration in `BookProof/`, `PnpProof/`,
   `Singularity/`, `RandomMap/` (the only `sorry`s left in the tree are the
   quarantined legacy RH-route ones in `UsedRoute/`/`UnusedRoute/`, which are in
   no default target); the isolation greps are empty; `./patches/build-book.sh`
   renders `_out/html-single/index.html` and its assertions (no `<base>`,
   fragment links present) hold; `./patches/check-katex.sh` reports 2129 math
   snippets, 0 failures.  Note: the `patches/*.sh` scripts had lost their
   executable bit in this snapshot and it has been restored.
**Next specialist: re-run for the 2026-08-20…20k waves.** The
    Navier–Stokes modules (`BilinearEsa`, `AffineFiber`/`AffineBlock`,
    `SignFlip`, `SignedShift`, `ThreeComponent`, `EsaClosure`,
    `NavierStokesHashimoto`, `KatoRellichRelative`,
    `NavierStokesLagrangianKatoRellich`, `NavierStokesCanonicalVector`),
    `ChapterGaugeFixing.lean`, the
    Stone-theorem modules (`ChapterStoneResolvent` through `ChapterStoneSeparable`),
    the bridge/flows modules (`ChapterStoneBridge`, `ChapterStoneFlows`), and the
    realization wave (`ChapterHermiteProductBasis`,
    `ChapterNavierStokesDifferentialL2`, `ChapterNavierStokesLagrangianCanonical`)
    were verified green in the producing workspace, but the §8 gate has **not**
    been re-run in this repository snapshot; the first action of the next
    Lean 4 specialist is `lake build`, `lake build RandomMap`, the book wrapper
    and the sorry/axiom/isolation audits.
2. Keep `Issues.md` §0b in sync when the chapter set changes.
3. The infinite-dimensional analytic layer (§4.8's boundary): Stone's theorem in
   full generality for operators that are not multiplication operators — the
   continuum Laplacian — is **proved** (2026-08-20e,
   `ChapterStoneResolvent`–`ChapterStoneSeparable`); what remains is the concrete
   *application* to the continuum Laplacian itself, i.e. proving that operator is
   self-adjoint on a core (the ESA step), not the generation of the flow from it.
4. **The NS continuum ESA — materially advanced (2026-08-20/20b/20c, canonical
    realization 2026-08-20h).** The
 abstract sequence-space ESA chain is now complete: the quadratic-symbol
     Hamiltonian is essentially self-adjoint on the finite-mode core of `ℓ²(ℕ × J)`
     (`BilinearEsa.bilH_essentiallySelfAdjointOn_core`), then with the affine fiber
     field covering the viscous and cross terms (`AffineFiber` / `AffineBlock`),
     with fiber constants of arbitrary sign (`SignFlip`), with coefficients of
     arbitrary sign (`SignedShift`), and finally with all three coupled velocity
     components and an arbitrary real velocity gradient
     (`ThreeComponent.velH_essentiallySelfAdjointOn_core`).  The step from the
     abstract sequence model to the differential operator is **already taken for
     the fiber generator**: `ChapterNavierStokesHermiteCanonical` proves the
     Hermite-basis matrix *is* the differential operator `½(πV + Vπ)` with
     `π = −i∂/∂u`, `V(u) = κu` (`hamiltonian_eq`, `comparison_eq`), and
     `canonical_essentiallySelfAdjointOn_core` gives ESA on the Hermite core of
     `L²(du)` with no hypothesis left.  The **canonical/ladder reading of the
     full quadratic symbol** (2026-08-20h) is also now carried inside the
     sequence space: `ChapterNavierStokesCanonicalVector` proves the
     Weyl-ordered expression `canH = ∑_i ½(π_i V_i + V_i π_i)` written in the
     three ladder pairs equals the hopping matrix (`canH_eq_velH`) and is
     essentially self-adjoint on the Hermite core (`canH_essentiallySelfAdjointOn_core`,
     `nsQuadraticH_essentiallySelfAdjointOn_core`).  **Closed (2026-08-20k):** the
     unitary transport of that canonical picture to `L²(du₁du₂du₃)` — the genuine
     differential realization of the *full* quadratic symbol
     `A_i = u_j u_{i,j} − ν u_{i,jj}` (the coupled three-component and viscous
     terms beyond the linear fiber) — is now built by
     `BookProof/ChapterHermiteProductBasis.lean` and
     `BookProof/ChapterNavierStokesDifferentialL2.lean`: `velUnitary` is the
     product-Hermite unitary `ℓ²(Vel) ≃ L²(ℝ³)`, `momOp` is `−i ∂/∂uᵢ` as a genuine
     derivative (`momOp_apply_eq_differential`) with `[πᵢ, u_k] = −i δ_{ik}`
     (`comm_momOp_posOp`), the transport intertwines the two pictures
     (`intertwined_canH`), and
     `nsDiffH_essentiallySelfAdjointOn_core` /
     `nsQuadraticDiffH_essentiallySelfAdjointOn_core` are the ESA of the
     differentially written symbol on the Hermite core of `L²(du₁du₂du₃)`.
     What remains from this item is only
     the Lagrangian second-order part on its trajectory-space `L²`.  ESA then
     gives the complete flow via Stone. Global existence of the *classical* NS
     equation is a separate, deliberate D5 scope cut.
5. **QG continuum ESA — materially advanced (2026-08-18).** The wave-operator
   ESA that was "entered as a named hypothesis" is now **proved**:
   `BookProof/ChapterStrichartzWave.lean` proves `□ + κ` (real constant) and all
   constant-coefficient real-symbol operators are essentially self-adjoint on the
   Schwartz core of `L²(ℝ^{1+n})` (via the Fourier/multiplier argument),
   `ChapterKatoRellichDeficiency.lean` proves the bounded-perturbation
   Kato–Rellich theorem, and `ChapterWaveBoundedPotential.lean` gives `□ + V` for
   essentially bounded real `V`. On the gravity side, `ChapterStrichartzHermiteQG`
   builds the genuine Hermite core of `L²(ℝ)` (`ChapterHermiteFunctions`:
   `hermiteBasis`, completeness) and proves the 3D gauge-fixed mode Hamiltonian
   `qg3D_essentiallySelfAdjoint_on_hermiteCore` (unbounded, trivial deficiency at
   every non-real `z`). Plan-to-Lean map: `STRICHARTZ_WAVE_ESA.md`.
   **Next target (the author's claim, 2026-08-18): the potential is polynomial
   and bounded below ⟹ `□ + V` is ESA.** The bounded-below-polynomial case is the
   genuine Strichartz step: a polynomial is unbounded, so the *bounded* `V`
   results do not apply, but it is bounded on every compact set, which is exactly
   what the finite-speed/localized energy argument needs (boundedness below is
   the global growth control that keeps the local estimates uniform). The plan:
   (a) localize with the proved `exists_smooth_cutoff` — on each ball of radius
   `R` the truncated `V_R` is essentially bounded; (b) apply the proved
   `wave_add_potential_essentiallySelfAdjoint` to `□ + V_R` — ESA per truncation;
   (c) pass ESA to `□ + V` in the limit `R → ∞` by the finite-speed/energy (or
   form-locality) argument, with the boundedness-below of `V` making the gluing
   uniform. This is a plan item (the cut-off lemma is already proved); the
   remaining boundary is the gauge/BRST-sector transfer check.
   **Update (2026-08-18b): executed as far as it is true.**
   `BookProof/ChapterWaveUnboundedPotential.lean` proves (a)+(b) — for every
   radius `R` a truncation `W_R` of temperate growth agreeing with `W` on the ball
   of radius `R` with `□ + W_R` essentially self-adjoint
   (`wave_add_truncatedPotential_essentiallySelfAdjoint`) — plus the two commuting
   halves with unbounded coefficients: an arbitrary real potential of temperate
   growth is essentially self-adjoint on the Schwartz core
   (`potentialOp_essentiallySelfAdjoint`) and so is every real-symbol Fourier
   multiplier of temperate growth (`multiplierOp_essentiallySelfAdjoint`, which
   contains `constCoeffOp_essentiallySelfAdjoint` via
   `constCoeffOp_eq_multiplierOp`).  Step (c) is **not** taken: with the convention
   `□ = -∂_t² + Δ_x` used in this project, a potential bounded *below* makes the
   time-Fourier fibre `-Δ_x - W` unbounded below — for `W = x⁴` this is the
   limit-circle operator `-d²/dx² - x⁴` with deficiency indices `(2,2)`, a
   classical fact quoted from the literature and not formalized here — so the
   claim as worded is false for this signature.  The correct hypothesis is `W`
   bounded *above* by a quadratic here (equivalently bounded below for
   `□ = ∂_t² - Δ_x`), which is the Sears / Faris–Lavine class; proving that case
    needs the fibrewise (direct-integral) argument and remains the open boundary.
    **Clarification (2026-08-19, the sign question):** the sign is *not* an
    artifact removable by convention, initial conditions, or the overall sign of
    `□` — essential self-adjointness is invariant under negation (`S` ESA ⟺ `−S`
    ESA), and the relevant sign is the *inner* one of `W` relative to the spatial
    `Δ_x` in the time-Fourier fibre, which is fixed by the operator.  The
    `(2,2)` claim for `-d²/dx² - x⁴` is a classical fact quoted from the
    literature, *not* formalized here (only a discrete limit-circle Jacobi
    counterexample is proved, `ChapterNavierStokesDeficiency.lean`).  The
    genuine open question is the sign of `Ṽ` in `H₀ + H₁ - Ṽ` after the
    densitizing/half-density unitary from the book's 3D gauge-fixed `ℋ`; the
    densitized mode symbol is `+V` and the book's `-e(𝒯-terms)` is `≤ 0` (good
    sign for `□ = -∂_t² + Δ_x`), but neither indicator is proved — see
    `PLAN_LEAN_SPECIALIST_QG_FLOW.md` Part D.6.
    **Update (2026-08-18c): the non-commuting mixed case is closed in the elliptic
   normalization.**  `BookProof/ChapterHarmonicOscillatorEsa.lean` proves that the
   harmonic oscillator `-d²/dx² + x²/4` — a differential kinetic term plus an
   unbounded polynomial potential that does not commute with it — is essentially
   self-adjoint on the Hermite core of `L²(ℝ)`
   (`harmonicOsc_essentiallySelfAdjoint`), with the differential identification
   `harmonicOscOp_apply_eq_differential` and unboundedness
   `harmonicOsc_not_bounded`.  This is the sign-correct (potential bounded below)
   case; the hyperbolic direct-integral argument is still open.
6. **QYM unbounded continuum — CLOSED (2026-08-18).** Both plan items of §11.4
   are executed by `BookProof/ChapterFriedrichsExtension.lean` (`sorry`-free /
   `axiom`-free, registered in `BookProof.lean`, certified in
   `ChapterRoadmapAudit.lean`, cited from `Book/YangMillsQuantization.lean`):
   item (1) is `friedrichs_extension_exists` — the Friedrichs extension theorem
   proved with **no boundedness hypothesis**, via the form inner product, its
   completion, Riesz representation of `(H+1)⁻¹` and `A = S⁻¹ − 1` — with
   `friedrichs_hypothesis_holds` discharging the named hypothesis of
   `friedrichs_extension_of_semibounded` and
   `weyl_friedrichs_extension_unconditional` giving the Weyl-gauge conclusion;
   item (2) is settled in favour of the occupation-number/Hermite realization
   (Part E of `PLAN_LEAN_SPECIALIST_QYM_FLOW.md`), and the combined statement —
   the extension exists *and* the Hashimoto/SIRK limit selects it, unbounded —
   is `friedrichs_hashimoto_selects` / `weyl_hashimoto_selects_friedrichs`, with
    `unbounded_friedrichs_example` showing it is not vacuous. What remains is
    only the recorded boundary: the mass gap, deliberately out of scope.
    **Refinement (2026-08-18):** option (b) is *not* a research boundary — the
    book's base `ℝ⁹⁹` is finite-dimensional and `H₁ = ½Σππ + ½ΣBB` is a
    finite-degree polynomial-coefficient differential operator, so the operator
    is **well-defined and symmetric on the product Hermite core** of `L²(ℝ⁹⁹)`
    (the `A`/`∂` ladder structure; same pattern as
    `harmonicOscOp_apply_eq_differential`).  It is a construction task: build
    `A`, `π = −iδ/δA`, `B` on that core and prove core-invariance/symmetry/
    positivity, with the Weyl ordering of the non-commuting `πA` cross-terms and
    the sign of book.tex:7077 as the two caveats.  See the §11.3/§11.4 closing
    updates.  **Executed (2026-08-18/19):** the construction task is done —
    `BookProof/ChapterHermiteProductCore.lean` (Gauss–polynomial core of
    `L²(ℝ⁹⁹)`, dense orthonormal basis whose finite-mode domain is the core)
    and `BookProof/ChapterYangMillsHermite.lean` (coordinate/momentum/
    magnetic-field operators, `[A_j, π_j] = i`, Weyl ordering `weylProd`, positive
    sum-of-squares `ymHamiltonian`, symmetry/positivity, instantiating the
    Friedrichs + Hashimoto theorems), plus the second quantization on
    finite-occupation states in `BookProof/ChapterFockSecondQuantization.lean`.
    Both caveats (Weyl ordering, sign) are settled *inside* the modules; only the
    mass gap remains out of scope.
7. Pedagogical polish (small, editorial): the new plan/doc files
   (`PLAN_LEAN_SPECIALIST_QG_FLOW.md`, `PLAN_LEAN_SPECIALIST_QYM_FLOW.md`,
   `HASHIMOTO_COMPLEX_SHIFTS.md`, `HERMITE_GALERKIN_FRIEDRICHS.md`) and the Book
   prose are in place; keep them in one-to-one correspondence with the proof
   modules on any future edit.
8. **The NS Hashimoto shift-invert selection theorem — EXECUTED (2026-08-20d).**
   **Closed by two new `sorry`-free / `axiom`-free modules**, registered in
   `BookProof.lean`, certified in `BookProof/ChapterRoadmapAudit.lean` and cited
   from `Book/FreeField.lean`:
   * `BookProof/ChapterEsaClosure.lean` (`BookProof.EsaClosure`) — the missing
     abstract step.  The deficiency-space form of essential self-adjointness is
     turned into the operator it selects: the graph closure (`opGraph`,
     `clGraph`, `clDom`, `clExt`) is built explicitly and proved to be a
     self-adjoint extension (`exists_isSelfAdjointExtension_of_esa`), it is the
     **only** one (`selfAdjointExtension_eq_adjoint`,
     `isSelfAdjointExtension_unique_of_esa`), and for an essentially
     self-adjoint operator the Friedrichs extension *is* that closure
     (`positiveExtension_eq_closure_of_esa`).
     `hashimoto_multishift_selects_esa` is the positivity-free version of
     `hashimoto_multishift_selects_friedrichs`.  A Cayley-transform section
     (`norm_add_I_eq_norm_sub_I`, `exists_cayley_unitary`,
     `exists_selfAdjointExtension_and_cayley_of_esa`) takes the selected
     operator to a unitary of the whole space without Stone's theorem.
   * `BookProof/ChapterNavierStokesHashimoto.lean`
     (`BookProof.NavierStokesFlow.NSHashimoto`) — the instantiation for the NS
     fiber generator `velCore`: `ns_selfAdjoint_extension`,
     `ns_selfAdjoint_extension_unique`, `ns_shiftInvert_selects` and the
     headline `ns_hashimoto_selects`, plus `exists_velHilbertBasis` /
     `exists_velEnum` for non-vacuity.
   Note the deviation from the plan text below, and it is the honest one: the
   NS Hamiltonian is **not** positive, so the extension the algorithm selects is
   labelled the *closure* (the unique self-adjoint extension) rather than the
   Friedrichs extension — the two coincide exactly when the operator is
   positive, which is what `positiveExtension_eq_closure_of_esa` records.  The
selection is therefore guaranteed by ESA itself, as step (b) of the plan
    anticipated, and the non-real shift replaces positivity in making the
    resolvent exist.  Step (c) (Stone's theorem, the flow) is now closed by the
    general theorem (2026-08-20e, `ChapterStoneResolvent`–`ChapterStoneSeparable`):
    for any essentially self-adjoint operator on a separable Hilbert space the
    selected closure generates the complete unitary flow `e^{-itA}`; what remains
    is applying it to a *differential* realization (the ESA step), not the flow
    generation itself.  The original plan text follows.

   **The NS Hashimoto shift-invert selection theorem — ORIGINAL PLAN ITEM (2026-08-20).**
   The unbounded Hashimoto/SIRK selection theorem — the Galerkin compressions of
   the shift-inverted resolvent converge to the Friedrichs extension, which the
   shift-invert data determine uniquely — is already proved in full generality
   (`BookProof/ChapterHashimotoShiftInvert.lean`:
   `hashimoto_shiftInvert_selects_friedrichs`, and the uniform instantiations
   `friedrichs_hashimoto_selects` / `weyl_hashimoto_selects_friedrichs` in
   `BookProof/ChapterFriedrichsExtension.lean`), and it is instantiated for the
   Yang–Mills Hamiltonian (`ym_hermite_hashimoto_selects`,
   `ym_fock_hashimoto_selects`).  It has **not** been instantiated for the
   Navier–Stokes Hamiltonian.  This item closes that gap: apply the same selection
   theorem to the NS generator on its dense core, after fixing the gauge of the
   derivative fields.

   **The gauge fixing (the substance of the item).**  In the Eulerian
   derivatives-as-fields picture the spatial derivatives of the velocity are
   *independent canonical field coordinates*: `u_{i,j}` and `u_{i,jj}` are separate
   modes, and the Hamiltonian carries momenta only for the velocity modes, which
   is exactly why the derivative field is a constant of the motion and why the
   block decomposition of `BilinearEsa`/`AffineBlock` diagonalises it (the blocks
   are indexed by the spectrum `J` of the derivative field).  The gauge fixing of
   "the field derivatives in space to the corresponding variables" is the
   A.6/A.7 machinery of `PLAN_LEAN_SPECIALIST_NS_FLOW.md`:
   `ChapterNavierStokesGaugeY.lean` / `ChapterNavierStokesGaugeY2.lean`
   (`genX`, `genY`, and the second-order generator
   `genY2 j = ∂/∂y_j − u_{i,j}∂/∂u_i − u_{i,jj}∂/∂u_{i,j}` annihilating the
   Taylor field `u_i(y) = u_i + u_{i,j} y_j + ½ u_{i,jj} y_j²`, with the honest
   mixed-bracket statement `genY_genY2_not_commute`).  The plan of attack:

   (a) **State the gauge-fixed operator.**  Build the NS Hamiltonian on the full
   (unbounded) space as a symmetric operator on a dense core: the finite-mode core
   of `ℓ²(ℕ × J)` in the block picture (the `BilinearEsa.bilH` /
   `AffineBlock.affBlockH` / `ThreeComponent.velH` chain already gives symmetry
   and essential self-adjointness on that core), with the derivative-field blocks
   identified with the gauge variables fixed by `genY`/`genY2`.  The constraints
   are ESA as well: the incompressibility/divergence condition `u_{j,j} = 0`, the
   Clairaut consistency conditions and the derivative momenta `π^{ij}` of plan
   A.5, together with the `genY`/`genY2` gauge generators, all cut out a
   constraint surface on which the restricted operator is again essentially
   self-adjoint.

   (b) **Run the selection theorem.**  The selection is **guaranteed by ESA
   itself**: an essentially self-adjoint operator has a unique self-adjoint
   extension (its closure), so the Galerkin compressions of its resolvent — and
   hence any consistent Hashimoto/SIRK approximation — converge to that extension
   by strong resolvent convergence, and the resolvent determines the operator
   uniquely.  The formalized `hashimoto_shiftInvert_selects_friedrichs` is the
   *positive* instantiation of this principle (it labels the extension as the
   Friedrichs extension, which for an ESA operator coincides with the closure when
   the operator is positive); with the core carried by a Hilbert basis of the
   finite modes (the Hermite basis of `ChapterHermiteFunctions`, or the block/
   `Vel` bases of the ESA chain), instantiate it following the exact pattern of
   `ym_fock_hashimoto_selects`: for a shift `γ > 0` the shift-inverted operator
   `R = (A + γ)⁻¹` is bounded with `‖R‖ ≤ γ⁻¹` and self-adjoint, its Galerkin
   truncations converge strongly and in the resolvent sense, and `R` determines
   the self-adjoint (Friedrichs) extension uniquely.

   (c) **Connect to the flow.**  By Stone's theorem the resulting self-adjoint
   extension generates the complete unitary group `e^{-itA}` for every real `t` —
   global existence of the operator flow with no finite-time blow-up — and the
   SIRK/Krylov machinery already proved for the truncation
   (`ChapterH1`–`H8`; `sirk_nested_orders`, the Crouzeix error bounds) supplies
   the finite-dimensional approximations that converge to that flow.

   **Suggested names** (following the QYM convention):
   `ns_hashimoto_selects_friedrichs`,
   `ns_shiftInvert_selects`, `ns_friedrichs_selected_by_hashimoto`,
   and the companion `ns_hashimoto_flow_tendsto` for the SIRK-to-flow convergence.
   Register in `BookProof.lean`, certify with `#print axioms` in
   `BookProof/ChapterRoadmapAudit.lean`, and cite from `Book/FreeField.lean` with a
   paragraph tying the gauge-fixed ESA chain to the Hashimoto selection.

**Honest boundary.**  Nothing here claims global regularity of the *classical*
    Navier–Stokes PDE (Contention D5, still the deliberate scope cut): the theorem
    concerns the Hilbert-space operator flow selected by the Hashimoto/SIRK limit.
    The gauge choice (which derivative fields are fixed to which velocity variables)
    and the sign/positivity of the quadratic form on the gauge-fixed space are
    construction steps to be settled inside the module, exactly as the Weyl-ordering
    and sign caveats of the QYM route were settled inside `ChapterYangMillsHermite`.
9. **The Lagrangian route — NON-PRIORITY PLAN ITEM (2026-08-20).**  The Eulerian
   route (items 4 and 8) is the priority; this item is the *independent*,
   parallel route of `PLAN_LEAN_SPECIALIST_NS_FLOW.md` Part B, recorded as
   **non-priority** because nothing here is required by the already-landed Eulerian
   chain — the two routes share many theorems, but neither supplies an input to the
   other, and in particular the Eulerian Hashimoto selection of item 8 is
   guaranteed by the Eulerian ESA itself (item 8), not by any positivity borrowed
   from the Lagrangian picture.  Its value is as an alternative realization of the
   same operator: in the trajectory (parcel) picture the transformed Hamiltonian
   is a positive sum of squares (the advection term becomes a positive
   second-order Laplacian), which is the structure a *separate* self-adjointness
   and Hashimoto-selection proof would exploit.  A large part of the route is
   **already proved**; a future pass would assemble it rather than start from
   scratch:

   * **The change of variables and its unitarity.**  The finite-truncation
     Eulerian→Lagrangian change of variables is formalized in
     `BookProof/ChapterNavierStokesFlow.lean` (`lagrangian_velocity`,
     `transformed_hamiltonian_decomposition`,
     `transformed_hamiltonian_hermitian`), and the truncated Lagrangian flow is
     unitary and complete (`flowUnitary_unitary`, `flowUnitary_group`,
     `cauchy_existsUnique`).  At the operator level the change of variables is a
     unitary transfer of essential self-adjointness:
     `LagrangianEsa.hasZeroDeficiencyOn_of_linearIsometryEquiv` and
     `LagrangianEsa.NSFullData.hasZeroDeficiencyOn_of_lagrangian` — proving ESA
     after passing to the Lagrangian variables proves it for the Eulerian
     operator it came from.
   * **The gauge fixing of the derivative-field variables.**  In the Lagrangian
     picture the field-derivative variables appear not in the Hamiltonian but in
     the constraint: the volume-preservation determinant
     `volume_preservation_constraint : det(∂X_i/∂ξ_j) = 1` with the derivative
     `det_one_add_smul_hasDerivAt` (the Lagrangian shadow of the Eulerian A.6/A.7
     `genY`/`genY2` / Method B gauge fixing of `Book/FreeField.lean`), and the
     zeroth-order constraint term `Ĥ_constraint` in the four-term decomposition.
   * **The positivity gain and the untruncated instances.**  After the change of
     variables the advection term is **positive**: `kinetic_posSemidef`,
     `viscous_posSemidef` and `LagrangianFullData.kinetic_nonneg` /
     `viscous_nonneg` (the kinetic and viscous quadratic forms are `½∑‖Pᵢv‖²` and
     `ν∑‖Qᵢv‖²`).  The untruncated operator is already essentially self-adjoint
     on two genuinely infinite-dimensional instances (`latticeLag_hasZeroDeficiencyOn`
     on `ℓ²(ℤ)`, `diagLag_hasZeroDeficiencyOn` on `ℓ²(ℕ)`, the latter genuinely
     unbounded), and the sharpness record
     `exists_lagrangianFullData_not_hasZeroDeficiencyOn` shows the positivity
     hypothesis is necessary, not decorative.

   The trajectory-space realization **is** the Fock-of-Fock space, and it is
   carried (2026-08-20g, recorded above): the transformed Hamiltonian is
   second-quantized on the continuum Fock space over `ParcelConf Ω` and
   essentially self-adjoint there (`fockLagrangian_hasZeroDeficiencyOn`,
   `hTwoLevel_hasZeroDeficiencyOn`).  The Eulerian side lifts to the Fock space
   as well — for NS, ESA of the one-particle Hamiltonian implies ESA of the
   Fock-space Hamiltonian on the finite-particle basis
   (`fockOp_hasZeroDeficiencyOn`, the positivity-free, diagonality-free
   direct-sum half of Reed–Simon §VIII.10; `velCore_esa` gives the
   hypothesis).  The remaining boundary is the *differential* realization, not
   the Fock lifting: the three-component Eulerian operator is ESA as a
   sequence-space operator (its matrix in the Hermite/`Vel` basis), and the
   genuinely differential step to `π = −i∂/∂u` on `L²(du₁du₂du₃)` is the honest
   open step.  The Kato–Rellich / Ikebe–Kato
   relative-boundedness control of the 1st-order drift against the 2nd-order
   Laplacian — the self-contained ESA/Hashimoto-selection proof on the Lagrangian
   side, independent of the Eulerian item 8 — is now **EXECUTED (2026-08-20d)**,
   see the two modules below.  Nothing here claims global regularity of the
   *classical* Navier–Stokes PDE (Contention D5, unchanged).

   **EXECUTED (2026-08-20d).**  The residual named above is closed by two new
   `sorry`-free, axiom-clean modules.

   * `BookProof/ChapterKatoRellichRelative.lean` proves the Kato–Rellich theorem
     for a **relatively bounded** — possibly unbounded — symmetric perturbation:
     `‖Bx‖ ≤ a‖Hx‖ + b‖x‖` with `a < 1` on the common domain preserves essential
     self-adjointness (`essentiallySelfAdjointOn_add_relBounded`), by an explicit
     Neumann iteration at a large non-real shift, no closure and no spectral
     theorem.  The previously available `essentiallySelfAdjointOn_add_bounded`
     is recovered as the case `a = 0`.
   * `BookProof/ChapterNavierStokesLagrangianKatoRellich.lean` applies it to the
     transformed Hamiltonian.  The positivity gain of the Lagrangian variables
     *is* the relative bound: `‖Pᵢv‖² = ⟪v,Pᵢ²v⟫ ≤ 2⟪v,Tv⟫ ≤ 2‖v‖‖Tv‖` for
     `T = ½∑Pⱼ² + ν∑Qⱼ²`, since every other term of that form is nonnegative;
     with `√(2AB) ≤ εB + A/(2ε)` this gives `‖Pᵢv‖ ≤ ε‖Tv‖ + (2ε)⁻¹‖v‖` for every
     `ε > 0` (`norm_P_le`) — the Ikebe–Kato interpolation of the 1st-order drift
     against the 2nd-order Laplacian.  Hence `hFull_hasZeroDeficiencyOn`: ESA of
     the positive second-order part alone gives ESA of the **full** transformed
     Hamiltonian (`hFull_hasZeroDeficiencyOn_of_drive_eq_P` in the physical case
     `Dᵢ = Pᵢ`), transported back to the Eulerian operator by
     `hasZeroDeficiencyOn_of_lagrangian_katoRellich`.  On top of it the
     Hashimoto/SIRK selection is proved on the Lagrangian side —
     `lagrangian_selfAdjoint_extension`, `..._unique`,
     `lagrangian_hashimoto_selects`, `lagrangian_shiftInvert_selects` — from this
     ESA and therefore independently of the Eulerian item 8.  Non-vacuity: the
     `ℓ²(ℕ)` instance `diagKR` has a genuinely **unbounded** drift
     (`diagKR_drift_not_bounded`), so the bounded Kato–Rellich theorem does not
     cover it, and `diagKR_hashimoto_selects` instantiates the selection there.
     Sharpness: `jacobiLag_drift_not_relativelyBounded` shows the counterexample
     `exists_lagrangianFullData_not_hasZeroDeficiencyOn` fails exactly the
     domination hypothesis.  All headlines are `#print axioms`-certified in
`BookProof/ChapterRoadmapAudit.lean`.  The trajectory-space `L²`
      realization is the one already carried by
      `BookProof/ChapterNavierStokesFockLagrangian.lean`.  **The Lagrangian /
      Eulerian rigor-parity gap (2026-08-20h record).**  Unlike the Eulerian
      side — which has both the canonical/ladder reading
      (`ChapterNavierStokesCanonicalVector`: `canH_eq_velH`,
      `canH_essentiallySelfAdjointOn_core`, `nsQuadraticH_essentiallySelfAdjointOn_core`)
      and the Hermite/differential realization of the fiber generator on
      `L²(du)` by
      `ChapterNavierStokesHermiteCanonical`), the Lagrangian second-order part
      `T` is realized concretely only on the abstract `ℓ²(ℕ)` diagonal instance
      `diagKR`; its canonical/ladder and Hermite/differential realization on the
      trajectory-space `L²` is **not** built.  **Superseded (2026-08-20j):** the
      canonical/ladder realization on the trajectory-space Hermite basis is now
      built by `BookProof/ChapterNavierStokesLagrangianCanonical.lean`
      (`lagQ`/`lagP`, `comm_lagP_lagQ`, `lagCan_secondOrder_eq`, `lagCan_esa`,
      `lagCan_stone_flow`), so this gap is closed; what remains open is the
      *differential* realization of the full quadratic symbol on `L²(du)`,
      §9 item 4.  The 2026-08-20h record, kept for the history, read: this is
      the single realization
      layer on which the Lagrangian variables version of NS is *behind* the
      Eulerian version (the ESA, the Hashimoto selection, the Fock-of-Fock
      lifting and — with 2026-08-20i — the Stone flows are at parity); it is
      recorded as the open next-step item for a specialist below.  Nothing here
      claims global regularity of the *classical* Navier–Stokes PDE (Contention
      D5, unchanged).
10. **The general Stone theorem — EXECUTED (2026-08-20e).** The last recorded
    research boundary — "the unitary group `e^{-itA}` of an unbounded self-adjoint
    operator" — is now a proved theorem, by the nine-module chain
    `BookProof/ChapterStoneResolvent` → `ChapterStoneSeparable` (see the leading
    Status block for the per-module headlines; the linear import chain is
    Resolvent → Group → Evolution → Unitary → Generator → Measurable → Converse →
    Theorem → Separable).  **Next step for a specialist (a plan item, not a
    research target): apply the theorem to a genuinely differential operator.**
    The natural first application is the quantum-harmonic-oscillator /
    continuum-Laplacian case, where the missing piece is exactly the *ESA step*
    on a core of `L²(ℝ)` — e.g. `-d²/dx² + x²/4` on the Schwartz core or the
    Hermite core (the ESA machinery already exists in `ChapterHarmonicOscillatorEsa`
    and `ChapterStrichartzHermiteQG`), so `stoneGroup` then manufactures
    `e^{-itH}` for it.  The Stone bijection (`stoneEquiv`) gives the *identity*
    check: the abstractly constructed group equals the explicit
    `(e^{-itH}ψ)(x)` formula.  This would make the "operator-flow global
    existence" of the NS/Lagrangian ESA chain, and of the continuum Laplace
    operator, an explicit theorem rather than a pointer.
    **As of 2026-08-20i, the flow *is* instantiated for QYM/NS:** the bridge
    `BookProof/ChapterStoneBridge.lean` turns the
    `IsSelfAdjointExtension` / `IsPositiveSelfAdjointExtension` predicates into
    the bundled `UnboundedSelfAdjoint` structure (`unboundedSelfAdjointOf`,
    `dense_domain_of_isSelfAdjointExtension`,
    `isSelfAdjointOn_of_isSelfAdjointExtension`), packages the complete unitary
    group as `IsStoneFlow` (`U 0 = 1`, the group law, isometry, and the
    Schrödinger equation on the domain), and proves `isStoneFlow_stoneU` plus
    `exists_stone_flow_of_selfAdjointExtension` / `of_positive` / `of_esa`.
    `BookProof/ChapterStoneFlows.lean` then instantiates the complete flow for
    the three concrete Hamiltonians: `ns_stone_flow` (Eulerian NS `velCore` on
    `ℓ²(Vel)`), `lagrangian_stone_flow` / `diagKR_stone_flow` (Lagrangian NS from
    `EssentiallySelfAdjointOn L.D (lagrangianCore L)`, with the unbounded
    `ℓ²(ℕ)` drift discharged by Kato–Rellich), and `ym_fock_stone_flow`
    (Friedrichs flow of `dΓ(½Σπ²+½ΣB²)` on the Fock space over the Gauss core
    of `L²(ℝ⁹⁹)`).  Step **(c)** of item 11 is thereby closed for all three.

11. **The Stone link to the QYM and NS flows — the explicit bridge (2026-08-20f,
    EXECUTED 2026-08-20i).**  Item 10 proved the *abstract* theorem; this item is the exact
    linkage of `stoneGroup`/`stoneEquiv` to the three concrete Hamiltonians whose
    ESA/selection is already proved.  Each requires the same three mechanical
    steps: **(a)** the wrapper lemma turning `IsSelfAdjointExtension` (or its
    positive companion) into the bundled `UnboundedSelfAdjoint` structure —
    density, symmetry and adjoint-domain equality are all conjuncts of the
    predicate, so only packaging is missing; **(b)** completeness and
    separability of the concrete Hilbert space (the Stone forward direction needs
    only completeness; the bijection `stoneEquiv` adds separability); **(c)**
    applying `stoneGroup` to obtain the complete unitary flow `e^{-itA}`.
    All three steps are now carried by `BookProof/ChapterStoneBridge.lean` and
    `BookProof/ChapterStoneFlows.lean` (2026-08-20i, see item 10's note): the
    wrapper `unboundedSelfAdjointOf` packages the predicate into
    `UnboundedSelfAdjoint`, `IsStoneFlow`/`isStoneFlow_stoneU`/
    `exists_stone_flow_of_selfAdjointExtension` / `of_positive` / `of_esa`
    deliver the complete unitary flow, and the instantiations are `ns_stone_flow`
    (Eulerian NS), `lagrangian_stone_flow` / `diagKR_stone_flow` (Lagrangian NS)
    and `ym_fock_stone_flow` (QYM).
    * **QYM (Fock / occupation-number realization).**
      `ym_hermite_hashimoto_selects` / `ym_fock_hashimoto_selects`
      (`ChapterFockSecondQuantization.lean`) give
      `IsPositiveSelfAdjointExtension (dGammaOpB ε …) A` with
      `A : Dom →ₗ[ℂ] Fock` on the Fock space over `Conf = ℕ →₀ ℕ` (separable,
      complete).  The bridge yields `e^{-itA}` for the positive
      (Friedrichs) extension — the flow of the QYM Hamiltonian.
    * **NS, Eulerian variables.**
      `ns_hashimoto_selects` (`ChapterNavierStokesHashimoto.lean:122`) gives
      `IsSelfAdjointExtension (velCore A c) G` — the unique self-adjoint
      extension (the closure) on `ℓ²(Vel)`.  The bridge yields `e^{-itG}`.
      The NS Hamiltonian is **not** positive, so there is no Friedrichs label:
      the flow is that of the unique closure, and the non-real shift replaces
      positivity in making the resolvent exist.
    * **NS, Lagrangian variables.**
      `lagrangian_hashimoto_selects` (`ChapterNavierStokesLagrangianKatoRellich.lean`)
      gives the analogous `IsSelfAdjointExtension` for the transformed
      Hamiltonian on the trajectory-space `ℓ²(ℕ)` instance `diagKR` (and its
      `L²` realization).  The transformed operator **is** a positive sum of
      squares, so here the Friedrichs and closure labels coincide
      (`positiveExtension_eq_closure_of_esa`); the bridge yields `e^{-itT}`.
    Honest boundaries unchanged (D5: no global regularity of the classical NS
    PDE; no mass gap for YM; the full continuum differential realization on
    `L²(du)` remains a recorded boundary).

    **Next step for a specialist (plan item, 2026-08-20h): the Lagrangian /
    Eulerian parity closure — EXECUTED (2026-08-20j) by
    `BookProof/ChapterNavierStokesLagrangianCanonical.lean`; see the leading
    Status block for the headlines.  Original wording retained below.**  The Eulerian variables version of NS now has a
    canonical/ladder reading of the full quadratic symbol
    (`ChapterNavierStokesCanonicalVector`) and a Hermite/differential
    realization of the fiber generator on `L²(du)`
    (`ChapterNavierStokesHermiteCanonical`); the Lagrangian variables version of
    NS has ESA, Hashimoto selection, the Fock-of-Fock trajectory-space lifting
    and (2026-08-20i) the Stone flows, but the second-order part `T` is realized
    concretely only on the abstract `ℓ²(ℕ)` diagonal instance `diagKR`.  To bring
    the two versions to full parity, build the analogue of the canonical/ladder
    reading for the transformed operator on the trajectory-space `L²` — canonical
    pairs `(Pᵢ, Qᵢ)` as the shift and number operators of a Hermite basis of the
    trajectory space, the CCR, and the identity `T = ½ΣPᵢ² + νΣQᵢ²` with ESA on
    the trajectory-space Hermite core — mirroring `ChapterNavierStokesCanonicalVector`
    and `ChapterNavierStokesHermiteCanonical` (see §9 item 9's parity record).

### What is missing from `PLAN_LEAN_SPECIALIST_NS_FLOW.md` (record, 2026-08-16;
updated 2026-08-20/20b/20c)

The plan is **executed** — every headline of Parts A–G is proved and `#check`-ed
(see the plan's Status table). What is *missing* is exactly the boundary the plan
itself drew, plus one small item and one correction:

- **The continuum ESA conclusion (the §7 research target, not a plan item).** The
  two Faris–Lavine inequalities are proved for the fiber Hamiltonian with
  `V = κu` **linear** in the field (on `L²(du)`, `π = −i∂/∂u` — a genuine
  differential operator; `ℓ²(ℕ)` is just its Hermite basis), and for the Fock /
  momentum realizations. **2026-08-20/20b/20c update:** the *quadratic* symbol is
  now covered in the abstract sequence-space models — the bilinear Hamiltonian on
  `ℓ²(ℕ × J)`, its affine extension (viscous + cross terms), arbitrary sign
  (`SignFlip`, `SignedShift`) and all three coupled components with an arbitrary
  real gradient (`ThreeComponent`).  What is *still* not proved is the two
  inequalities for the quadratic NS symbol `A_i = u_j u_{i,j} − ν u_{i,jj}` as an
  actual differential operator on `L²(du)`: the abstract models give the operator
  by its matrix in the Hermite basis only, and the differential realization (the
  step from the matrices to `π = −i∂/∂u` on `L²(du)`) is the remaining research
  target.  Both candidate routes are named (§7): the Lagrangian change of
  variables (Part B, advection → positive 2nd-order Laplacian) and the Eulerian
  derivatives-as-fields picture (Part A, momentum representation with the
  multiplication-operator comparison).  The residual is a concrete FL *estimate*
  for that quadratic `A_i` (a relative bound + form-commutator bound) in the
  already-proved framework — not a "Sobolev/differential realization" gap, and
  not a research project needing new analytic machinery.
- **Global existence of the flow is a corollary of ESA, not a separate gap.** Once
  ESA is proved (in the Hermite basis, where `N = π² + V² + I` is diagonal and
  `H = ½(πV + Vπ)` is a concrete shift), Stone's theorem gives the complete
  unitary group `e^{-itH}` for every real `t` — global existence of the operator
  evolution, no finite-time blow-up. This is now a proved theorem, not a
  promise (2026-08-20e, `BookProof/ChapterStoneResolvent` through
  `ChapterStoneSeparable`: `stoneGroup`, `stoneEquiv`). This is what
  `book.tex` §4210-4216's "the
  solution ... exists and it is unique" means; the truncation already proves it as
  `nsCauchy_existsUnique`. It is **not** an additional theorem to chase beyond
  ESA.
- **The genuinely open scope cut is the *classical* NS PDE (Contention D5).**
  Completeness of the Hilbert-space unitary flow does not by itself settle the
  Clay regularity problem (global smooth solutions of the classical NS equation),
  which is a statement about the PDE, not about the operator flow, and is not
  claimed anywhere. Recorded in `CONSOLIDATED_PLAN.md` §6 and the book's
  honest-boundary prose.
- **The NS Hashimoto/SIRK selection is now a named target (2026-08-20).** The
  unbounded Hashimoto shift-invert selection theorem is proved in general and
  instantiated for Yang–Mills but not for Navier–Stokes; applying it to the NS
  Hamiltonian after the gauge fixing of the derivative fields (the A.6/A.7
  `genY`/`genY2` generators) is the new §9 item 8.
- **`PLAN_LEAN_SPECIALIST_NS_FLOW.md` A.1 `positionOp`.** CLOSED (2026-08-17): the
  alias `BookProof.ChapterF1.positionOp` now carries the plan's name (the position
  operator is realized as `ChapterF1.fieldPhi = creat + annih`, ChapterF1.lean:98).
  Nothing mathematical was missing; the name now matches.
- **The optional E.3 was corrected, not closed.** The plan's optional
  `nsBrst_hermitian : Ωᴴ = Ω` is **false** when the divergence field is non-zero;
  the Aristotle wave proved `nsBrst_not_hermitian` and the honest Hermitian
  packaging `nsBrst_symmetrization_hermitian` (`Ω + Ω†`). The plan's E.3 text
  should be read as superseded by that correction.
- **The second-coordinate `y` (GaugeY, plan A.6) and its second-derivative
  extension (plan A.7) are both CLOSED (2026-08-17).** The `genX`/`genY`
  construction and the `y = 0` collapse are in `ChapterNavierStokesGaugeY.lean`
  (A.6); the extension `genY2 j = ∂/∂y_j − u_{i,j}∂/∂u_i − u_{i,jj}∂/∂u_{i,j}`
  annihilating the second-order field `u_i(y) = u_i + u_{i,j} y_j + ½ u_{i,jj}
  y_j²` is in `ChapterNavierStokesGaugeY2.lean` (A.7) — Eulerian-only (the
  Lagrangian parcel side has no such field expansion). The executed A.7 carries
  the Taylor coefficient `½` on the quadratic term (with coefficient `1` no
  generator of that shape annihilates the field), adds the derivative field
  `uDField`, the gauge-invariant symbol `nsSymbol2` and the honest mixed-bracket
  statement `genY_genY2_not_commute`.
- **Verification gate: run (2026-08-17).** `lake build` (default targets) and
  `lake build RandomMap` are green in this repository, and the sorry/axiom and
  isolation audits are clean.
- **The canonical realization of the full NS quadratic symbol is carried
  (2026-08-20h).** `ChapterNavierStokesCanonicalVector` proves the canonical /
  ladder reading of the full symbol inside the Hermite sequence space
  (`canH_eq_velH`, `canH_essentiallySelfAdjointOn_core`,
  `nsQuadraticH_essentiallySelfAdjointOn_core`); its unitary transport to
  `L²(du₁du₂du₃)` remains the recorded differential-realization boundary, and
  the Lagrangian second-order part still lacks the analogous canonical/ladder
  realization on its trajectory-space `L²` (the parity item recorded under §9
  item 11's next step).
- **The Stone bridge to the QYM/NS flows is carried (2026-08-20i).**
  `ChapterStoneBridge.lean` packages the ESA predicates into `UnboundedSelfAdjoint`
  and `IsStoneFlow`, and `ChapterStoneFlows.lean` instantiates the complete
  unitary flow for Eulerian NS (`ns_stone_flow`), Lagrangian NS
  (`lagrangian_stone_flow`, `diagKR_stone_flow`) and QYM (`ym_fock_stone_flow`),
  closing §9 item 11's step (c).
- **The Lagrangian canonical/ladder realization is carried (2026-08-20j).**
  `ChapterNavierStokesLagrangianCanonical.lean` proves the trajectory-space
  canonical pair (`lagQ`, `lagP`), the CCR (`comm_lagP_lagQ`), the identity
  `T = ½ΣPᵢ² + νΣQᵢ² = ω(N + 3/2)` (`lagCan_secondOrder_eq`), ESA on the Hermite
  core (`lagCan_esa`) and the resulting flow (`lagCan_stone_flow`), closing the
  Lagrangian/Eulerian parity item; the differential realization on `L²(du)`
  remains the recorded boundary.
- **Verification gate: re-run (2026-08-20j).** `lake build` (default targets
  BookProof + Book + Singularity, 8657 jobs) and `lake build RandomMap` /
  `lake build UsedRoute` complete; `./patches/build-book.sh` renders the book and
  its invariants hold (no `<base>`, fragment links present); `./patches/check-katex.sh`
  reports 2288 math snippets, 0 KaTeX failures; the sorry/axiom and isolation
  audits are clean (the only remaining `sorry`s are the quarantined legacy RH
  route under `UsedRoute/`/`UnusedRoute/`, which are not default targets).

None of these is a mathematical gap in the provable core: they are the recorded
boundary (continuum ESA + classical NS regularity), a closed cosmetic name (A.1),
a superseded optional item (E.3), and the closed A.6/A.7 gauge-generator items.
With the gate green and A.7 landed, `PLAN_LEAN_SPECIALIST_NS_FLOW.md` is fully
executed.
5. Pedagogical polish (small, editorial): the Eulerian/GaugeY prose in
   `Book/FreeField.lean` is in place; the plan's A.6/A.7 now carry the
   second-coordinate `y` and the second-order generator `genY2` as named plan
   items, so the plan and the proof modules are in one-to-one correspondence.

### Consolidated next steps for the Lean 4 specialist (2026-08-21)

**UPDATE (2026-08-22d, after the quadratic-ESA closure merge):** the list below is
superseded by the status block at the top of this file.  In priority order, the
concrete next steps for the Lean 4 specialist are:

**UPDATE (2026-08-22f):** items 1 and 2 below are **done** —
`ChapterCarlemanGeneralHop` is registered and repaired, and the §8 gate has been
re-run green (see the leading status block and the 2026-08-22f B1 entry).  Items 3
and 4 (A1, A4) remain, joined by A5 step 2.

**UPDATE (2026-08-23, after the scalaron wave):** the "QG continuum ESA with an
unbounded potential" step — recorded below as the one genuinely open analytic
step — is now **closed** by `ChapterScalaronCoreEsa` (compactly supported smooth
core: no growth hypothesis) and `ChapterScalaronFockEsa` (fibrewise gluing to the
nested Fock space), and A5 is closed at the mode, continuum-core and Fock levels.
What remains for the specialist, in priority order: (a) **re-run the §8 gate on
the merged state** — the Book now has three new chapters
(`Book/Starobinsky.lean`, `Book/NavierStokesHashimoto.lean`,
`Book/CarlemanFlux.lean`) so the Book build and the new `#check` citations must be
verified against the namespaces `BookProof.Starobinsky`, `BookProof.ScalaronEsa`,
`BookProof.ScalaronFock`, `BookProof.NavierStokesFlow`,
`BookProof.CarlemanGeneralHop`; (b) close **A1** (general Faris–Lavine potential /
hyperbolic direct integral) and **A4** (the FL-estimate route on the NS
differential symbol); (c) confirm the **A5-step-2 residue** (carrying the
potential bound through the densitized change of variables at the continuum
`L²(ℝ⁸⁴)` level) is subsumed by the proved core ESA, or record the precise
remaining statement.

1. **Register `BookProof/ChapterCarlemanGeneralHop.lean`.** — DONE (2026-08-22f).  It is a complete,
   self-contained leaf module (a Carleman criterion for general lattice hops,
   covering the non-monotone hops `α ↦ α ± (eᵢ − eⱼ)` alongside the monotone ones)
   but it is not imported by `BookProof.lean`, not certified in
   `ChapterRoadmapAudit.lean`, and not recorded in `BookProof/STATUS.md`.  Verify it
   compiles (`lake build`), add the import and the `#print axioms` block to the
   audit, write the STATUS wave entry, and re-run the §8 gate.
2. **Re-run the §8 verification gate after this merge** — DONE (2026-08-22f).  `lake build` (BookProof +
   Book + Singularity), `lake build RandomMap`, `lake build UsedRoute`,
   `./patches/build-book.sh`, `./patches/check-katex.sh`, the sorry/axiom audit and
   the isolation greps.  The Aristotle snapshot recorded it green at 2026-08-22d
   (8680 jobs; 2507 KaTeX snippets, 0 failures); confirm nothing regressed in this
   repository state.
3. **Close A1's remaining case: the general Faris–Lavine potential.**  The natural
   next instrument is the direct-integral analogue of the now-proved orthogonal
   direct-sum gluing (`ChapterDirectSumEsa`): produce the fibre decomposition of
   `□ + V` over fibres where `V` is bounded above by a quadratic, and run the
   deficiency-space gluing fibre-by-fibre.  The honest boundary is recorded in the
   A1 backlog entry: the gluing proved so far needs mutually orthogonal invariant
   fibres, and the QG fibre decomposition still has to be produced.
4. **A4: the NS quadratic-symbol Faris–Lavine estimate as an actual differential
   operator** — the alternative route recorded at the end of the A4 backlog entry,
   now that `ChapterOperatorSeriesEsa` / `ChapterFockQuadraticEsa` have made the
   additive Faris–Lavine instrument reusable.
5. **Pedagogical polish (optional):** every *registered* new module is already
   cited from the book (`Book/DiffeomorphismsGravity.lean` carries the whole
   quadratic-ESA narrative, `Book/FreeField.lean` the direct-sum gluing,
   `Book/ConditionalUnitary.lean` the unbounded spectral model); only the
   unregistered `ChapterCarlemanGeneralHop` lacks a book citation, which should
   follow its registration.

All *named* §9 plan items are now closed; nothing below is a plan item. These are
the concrete actions that would most improve the project, in order of value.
Status of the previously-listed analytic boundaries (see the leading Status
block): the **NS fibrewise / continuum ESA** is closed
(`ChapterNavierStokesFockContinuum.multOp_hasZeroDeficiencyOn`,
`sectorHamiltonian_hasZeroDeficiencyOn`), and the **Stone→continuum Laplacian**
step is closed (`BookProof/ChapterStrichartzWave.constCoeffOp_essentiallySelfAdjoint`
covers the Laplacian symbol; ESA then yields the complete flow by the general
Stone theorem).  The **QG continuum ESA with an unbounded potential** remains
**open** — this is the one genuinely open analytic step.  The full open backlog,
in priority order, is:

#### A. Substantial mathematics (research targets — new Lean theorems)

These are the highest-value, genuinely-open items.  Each is a real theorem to
prove, not a hygiene task, and each is already scoped by the named hypotheses and
the `sorry`-free machinery already in place.

**A1 — UPDATE (2026-08-21): the diagonal-quadratic case is now CLOSED; the general
Faris–Lavine potential stays open.**  `BookProof/ChapterHyperbolicQuadraticEsa.lean`
(namespace `BookProof.HyperbolicQuadratic`) proves that for *every* real weight
vector `c : Fin d → ℝ` — no sign condition, so the signature may be hyperbolic —
the operator `H_c = ∑ᵢ cᵢ(−∂ᵢ² + xᵢ²/4)` is symmetric
(`quadOp_symmetric`) and essentially self-adjoint (`quadOp_essentiallySelfAdjoint`)
on the Gauss–polynomial (product Hermite) core of `L²(ℝᵈ)`, is genuinely unbounded
(`quadOp_not_bounded`) on a dense core (`polyGaussCore_dense_L2`), and *is* the
differential expression pointwise (`quadPoly_apply_eq_differential`, with Mathlib's
`deriv` twice along each coordinate line).  With the Minkowski weights
`c = (1, −1, …, −1)` this is exactly `□ + V` with the indefinite quadratic potential
`V(t,x) = (t² − ‖x‖²)/4` in the convention `□ = −∂_t² + Δ_x`
(`wave_indefiniteQuadratic_essentiallySelfAdjoint`,
`minkowski_apply_eq_differential`): unbounded above and below, non-commuting with
`□`, and bounded above by a quadratic — the Faris–Lavine sign.  The route is the
joint eigenbasis, packaged as the reusable instruments `symmetricOn_of_diagonal` and
`deficiencyTrivialAt_of_diagonal`.  **Still open:** a *general* potential bounded
above by a quadratic (the joint eigenbasis exists only for the diagonal quadratic
family), i.e. the fibrewise / direct-integral gluing described below.

**A1 — UPDATE (2026-08-21b): unbounded *first-order* perturbations are now also
closed, in the elliptic case.**  `BookProof/ChapterHermiteRelativeBound.lean`
(namespace `BookProof.HermiteRelative`) proves that for strictly positive weights
`cᵢ ≥ c₀ > 0` the position and momentum operators are symmetric on the Hermite core
(`posL_symmetric`, `momL_symmetric`) and satisfy the form identity
`⟪u, (πᵢ² + xᵢ²/4)u⟫ = ‖πᵢu‖² + ‖xᵢu‖²/4` (`re_inner_oscL_eq`); with the symbol
comparison `c₀(αᵢ + ½) ≤ ∑ⱼ cⱼ(αⱼ + ½)` (`re_inner_oscL_le_quadOp`, from the reusable
instrument `re_inner_diagonal_le`) this gives the *arbitrarily small* relative bounds
`‖xᵢu‖, ‖πᵢu‖ ≤ ε‖H_c u‖ + (2/(c₀ε))‖u‖` (`norm_posL_le`, `norm_momL_le`).  The
relative Kato–Rellich theorem then gives
`quadOp_add_firstOrder_essentiallySelfAdjoint`: `H_c + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)` is
essentially self-adjoint on the same core for arbitrary real coefficients — an
*unbounded* perturbation — and in particular the Stark-shifted oscillator
`−Δ + ‖x‖²/4 + ⟨b, x⟩` (`harmonicOsc_add_linearPotential_essentiallySelfAdjoint`,
with `foOp_linear_apply_eq_mul` identifying the perturbation as multiplication by
`x ↦ ⟨b, x⟩`).  **Still open:** the hyperbolic (mixed sign) case of this widening —
there the symbol vanishes on infinitely many multi-indices, so `H_c` does not
dominate the number operator — and the general Faris–Lavine potential below.

**A1 — UPDATE (2026-08-21c): the diagonality restriction is CLOSED.**
`BookProof/ChapterQuadraticRotationEsa.lean` (namespace `BookProof.QuadraticRotation`)
proves that for **every** real symmetric matrix `A` — no sign condition, so the
signature may be elliptic, hyperbolic or degenerate — the operator
`H_A = ∑_{k,l} A_{kl}(π_k π_l + x_k x_l/4)` with `π_k = −i∂/∂x_k` is symmetric
(`quadOpMat_symmetric`) and essentially self-adjoint
(`quadOpMat_essentiallySelfAdjoint`) on the Gauss–polynomial core, and is genuinely
unbounded whenever `A ≠ 0` (`quadOpMat_not_bounded`).  The route is the orthogonal
substitution `rotPoly O` on polynomial coordinates plus rotation invariance of the
Gaussian: the canonical pair transforms contravariantly with the *same* matrix
(`rotPoly_mulXPoly`, `rotPoly_momPoly`), so `H_c` is carried onto
`H_{O diag(c) Oᵀ}` (`quadPolyMat_rotPoly`) and the rotated product Hermite functions
are an orthonormal family of joint eigenvectors spanning the core; the spectral
theorem for real symmetric matrices supplies `O` and `c` (`exists_rotConj`).  With
the rotated Minkowski form this is `□ + V` in rotated coordinates, where *neither*
the kinetic form nor the potential is diagonal
(`wave_rotated_essentiallySelfAdjoint`).

**A1 — UPDATE (2026-08-21d): the general *inhomogeneous elliptic* quadratic
Hamiltonian is CLOSED.**  `BookProof/ChapterQuadraticRotationPerturbed.lean`
(namespace `BookProof.QuadraticRotationPerturbed`) combines the two updates above:
for a **positive definite** real symmetric `A` and arbitrary real `b, b'`, the
operator `H_A + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)` — a general elliptic quadratic form with cross
terms plus a general unbounded first-order term — is symmetric
(`quadOpMat_add_firstOrder_symmetric`) and essentially self-adjoint
(`quadOpMat_add_firstOrder_essentiallySelfAdjoint`) on the same core; with `b' = 0`
this is an anisotropic oscillator with cross terms in a constant external field
(`anisotropicOsc_add_linearPotential_essentiallySelfAdjoint`).  The eigenbasis route
no longer suffices (the perturbation is not diagonal), so the rotated Hermite
functions are upgraded to a Hilbert basis (`rotHermiteBasis`) and the substitution to
an honest unitary `rotU` of `L²(ℝᵈ)`, which on the core *is* the polynomial
substitution (`rotU_pgLp`) and carries the first-order symbol with coefficients
`b, b'` onto the one with `Ob, Ob'` (`rotPoly_foPoly`, `rotU_intertwine`); essential
self-adjointness is a unitary invariant, so the relative Kato–Rellich theorem
transfers.  **Still open:** the indefinite case of *this* widening (positive
definiteness is used exactly once, in `exists_lower_bound_eigenvalues`, and the
relative bound genuinely fails without it), and the general Faris–Lavine potential
below.

**A1 — UPDATE (2026-08-21e): the *indefinite* inhomogeneous quadratic case is
CLOSED (diagonal weights).**  `BookProof/ChapterShiftedHermiteCore.lean`
(namespace `BookProof.ShiftedHermiteCore`) and
`BookProof/ChapterShiftedQuadraticEsa.lean` (namespace
`BookProof.ShiftedQuadratic`) remove the sign condition left open by the two
updates above, by changing the *core* instead of estimating the perturbation.
For weights `cᵢ ≠ 0` of **arbitrary sign** and arbitrary real `b, b'`, completing
the square in position and in momentum at once,
`cᵢ(πᵢ² + xᵢ²/4) + bᵢxᵢ + b'ᵢπᵢ = cᵢ((πᵢ + b'ᵢ/(2cᵢ))² + (xᵢ + 2bᵢ/cᵢ)²/4) − b'ᵢ²/(4cᵢ) − bᵢ²/cᵢ`
(`shiftedHPoly_term`, `shiftedHPoly_eq_quadPoly`), rewrites the operator as the
*same* `H_c` plus a real constant in the frame recentred at the classical
equilibrium `aᵢ = −2bᵢ/cᵢ` and boosted to the classical momentum
`kᵢ = −b'ᵢ/(2cᵢ)`.  Translation and modulation are unitary substitutions of
`L²(ℝᵈ)`, so the translated, modulated Gauss–polynomial functions
`p(x−a)e^{−‖x−a‖²/4}e^{i⟨k,x⟩}` are again a dense core
(`polyGaussCoreT_dense`, `shiftedCore_dense`) carrying an orthonormal, total
Hermite family (`orthonormal_hermiteTLp`, `hermiteTLp_total`), on which the full
operator acts diagonally with real eigenvalues
`∑ᵢ cᵢ(αᵢ + ½) + ∑ᵢ(−b'ᵢ²/(4cᵢ) − bᵢ²/cᵢ)` (`shiftedHOp_hermiteTLp`).  The
diagonal instruments then give `shiftedHOp_symmetric`,
`shiftedHOp_deficiencyTrivialAt` and `shiftedHOp_essentiallySelfAdjoint`, with
`shiftedHOp_not_bounded` (genuine unboundedness), `shiftedHOp_stone_flow` (the
complete unitary Schrödinger flow, via Stone) and
`shiftedHPoly_apply_eq_differential` (pointwise, `H` really is
`∑ᵢ (cᵢ(−∂ᵢ²f + xᵢ²f/4) + bᵢxᵢf + b'ᵢ(−i∂ᵢf))` with Mathlib's `deriv`).  With the
Minkowski weights this is `wave_indefiniteQuadratic_linear_essentiallySelfAdjoint`:
`□ + V` with `V(t,x) = (t² − ‖x‖²)/4` plus an arbitrary constant external field
and an arbitrary constant boost.  No domination and no sign condition is used —
only `cᵢ ≠ 0`, which is necessary for the completion of the square.  Recorded in
the book in `Book/DiffeomorphismsGravity.lean`.  **Still open:** the indefinite
case with *cross terms* (i.e. a general indefinite symmetric `A` plus a
first-order term; the rotation route of 2026-08-21c composes with this one only
when the rotated first-order coefficients are handled, which needs `A` invertible
and is not yet formalized), and the general Faris–Lavine potential below.

**A1 — UPDATE (2026-08-21f/21g): cross terms and the *singular* case are CLOSED, and
the dynamics is now explicit.**  `BookProof/ChapterShiftedQuadraticMatrixEsa.lean`
(namespace `BookProof.ShiftedQuadraticMatrix`) removes the diagonality restriction left
by 2026-08-21e: for every real symmetric **invertible** `A` of arbitrary signature and
arbitrary real `b, b'`, `H_A + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)` is symmetric
(`shiftedHMatOp_symmetric`) and essentially self-adjoint
(`shiftedHMatOp_essentiallySelfAdjoint`) on the translated, modulated core with
`a = −2A⁻¹b`, `k = −A⁻¹b'/2`, is genuinely unbounded (`shiftedHMatOp_not_bounded`) and
generates a complete unitary flow (`shiftedHMatOp_stone_flow`); the rotated Minkowski
corollary is `wave_rotated_linear_essentiallySelfAdjoint`.  Completing the square in
matrix form (`shiftedHMatPoly_eq_quadPolyMat`) combines the orthogonal diagonalization
of 2026-08-21c with the phase-space translation of 2026-08-21e, and the translated,
modulated, *rotated* Hermite functions are the eigenbasis (`hermiteTRLp_total`).

`BookProof/ChapterShiftedQuadraticDegenerate.lean` (namespace
`BookProof.ShiftedQuadraticDegenerate`) then removes invertibility.  Completing the
square needs only a *solution* of the classical equilibrium equations `A a = −2b`,
`A k = −b'/2`, and for symmetric `A` solvability is exactly orthogonality to the kernel
(`equilibrium_orthogonal_to_kernel`, `exists_equilibrium`, `exists_equilibrium_iff`).
So for **every** real symmetric `A` — invertible or singular, of arbitrary signature —
admitting a classical equilibrium, the operator is symmetric
(`shiftedHMatOp_symmetric_of_equilibrium`) and essentially self-adjoint
(`shiftedHMatOp_essentiallySelfAdjoint_of_equilibrium`) on the translated, modulated
core, with the intrinsic form `exists_shiftedHMat_esa_of_kernel_orthogonal` and the
concrete degenerate diagonal instance `diagonal_degenerate_essentiallySelfAdjoint`
(weights allowed to vanish).

`BookProof/ChapterStoneEigenflow.lean` (namespace `BookProof.StoneEigenflow`) makes the
resulting dynamics explicit: a self-adjoint extension keeps the eigenvectors of the core
operator (`isSelfAdjointExtension_eigenvector`) and *any* Stone flow acts on an
eigenvector by the phase `e^{−iλt}` (`stoneFlow_apply_eigenvector`), proved from the
Schrödinger equation and the equality case of Cauchy–Schwarz rather than from the
spectral theorem; `exists_diagonal_stone_flow` packages it, and
`exists_shiftedHMat_diagonal_flow` / `exists_shiftedH_diagonal_flow` solve the
Schrödinger equation in closed form on the Hermite eigenbasis of the quadratic family.
`BookProof/ChapterFourierMultiplierEsa.lean` (namespace `BookProof.FourierMultiplierEsa`)
handles the purely-momentum part of the residual case by the other route: the Plancherel
argument of `ChapterStrichartzWave` is extracted as an instrument — a Fourier multiplier
with a real, smooth symbol is symmetric and essentially self-adjoint on the Schwartz core
(`symmetricOn_of_real_symbol`, `essentiallySelfAdjointOn_of_real_symbol`) — and applied to
`∑ᵢ cᵢ(−i∂_{wᵢ})` (`firstOrderOp_essentiallySelfAdjoint`,
`momentumOp_essentiallySelfAdjoint`) and to `∑ᵢ cᵢ∂_{wᵢ}² + ∑ᵢ aᵢ(−i∂_{wᵢ}) + κ`
(`mixedOp_essentiallySelfAdjoint`).
**Still open:** a kernel direction mixing a linear potential with a momentum term
(`bᵢxᵢ + b'ᵢπᵢ` with both coefficients non-zero: no `L²` eigenvector for the Hermite
route, no constant-coefficient form for the Fourier route) and the general Faris–Lavine
potential below.

**A1 — UPDATE (2026-08-21i): the quadrature `∑ᵢ(bᵢxᵢ + b'ᵢπᵢ)` is CLOSED on the
Gauss–polynomial core too.**  `BookProof/ChapterQuadratureEsa.lean` (namespace
`BookProof.QuadratureEsa`) proves that for **arbitrary** real coefficients `b, b'`
the quadrature `foOp b b' = ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)` is essentially self-adjoint on the
Gauss–polynomial (product Hermite) core of `L²(ℝᵈ)`
(`foOp_essentiallySelfAdjoint`), hence generates a complete unitary flow
(`foOp_stone_flow`).  `ChapterMixedLinearEsa` had settled the same operator on the
**Schwartz** core, by a quadratic gauge; this closes it on the core the whole
quadratic family actually lives on, where neither of the two routes used elsewhere
applies (no `L²` eigenvector, not constant-coefficient).  Three ingredients:
(i) a **moment lemma with no `L²` hypothesis** (`ae_eq_zero_of_moments'`), which is
what makes the deficiency equation of a *multiplication* operator solvable on this
core, and gives `foOp_pos_essentiallySelfAdjoint` for the positional quadrature
`x ↦ ∑ᵢbᵢxᵢ`; (ii) the **ladder form** of the quadrature on the basis
(`foOp_hermiteCore`: raising amplitude `wᵢ = bᵢ + ib'ᵢ/2`, lowering amplitude
`conj wᵢ`); (iii) the **metaplectic rotation realized as a diagonal phase**
(`phaseBasis`, `phaseU`, `phaseU_foOp_hermiteCore`): multiplying `ψ_α` by `ζ^α`,
`ζᵢ = wᵢ/|wᵢ|`, is a unitary preserving the core which carries `∑ᵢ|wᵢ|xᵢ` onto
`∑ᵢ(bᵢxᵢ + b'ᵢπᵢ)`.  **Still open** in this strand: a quadratic `H_A` *plus* a
first-order term in a direction with no classical equilibrium; the recorded route is
the ℓ²-side instrument
`NavierStokesIkebeKato.essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds`.

**A1 — UPDATE (2026-08-22): the quadratic-plus-first-order case with no classical
equilibrium is CLOSED, and so is the *general mode-diagonal* quadratic (squeezing
included).**  Two new modules, both `sorry`-free and axiom-clean, replace the
relative-bound / completed-square routes by a **Carleman flux argument** on the
lattice of multi-indices of the product Hermite basis.
  (i) `BookProof/ChapterHermiteCarlemanEsa.lean` (namespace
  `BookProof.HermiteCarleman`).  A square-summable family satisfying the
  nearest-neighbour recursion `lam α u_α + ∑ᵢ(conj(wᵢ)√(αᵢ+1) u_{α+eᵢ} + wᵢ√αᵢ u_{α−eᵢ})
  = z u_α` with a **real** diagonal at a non-real `z` vanishes (`ladder_eq_zero`): the
  imaginary part, summed over the cube `{α : ∀i, αᵢ ≤ N}`, telescopes to the flux
  through the boundary faces (`flux_identity`), which is at most `√(N+1)` times the
  mass of those faces (`flux_bound`); the faces are disjoint, so that mass is summable,
  while `∑ 1/√(N+1) = ∞`.  Consequence (`mixOp_essentiallySelfAdjoint`): for
  **arbitrary** real weights `c` — any signs, zeros allowed — and **arbitrary** real
  `b, b'`, the operator `∑ᵢ cᵢ(πᵢ² + xᵢ²/4) + ∑ᵢ(bᵢxᵢ + b'ᵢπᵢ)` is essentially
  self-adjoint on the **plain** Gauss–polynomial core, with a complete unitary flow
  (`mixOp_stone_flow`) and the Minkowski corollary
  (`wave_indefiniteQuadratic_firstOrder_essentiallySelfAdjoint`).  No ellipticity, no
  sign condition, no classical equilibrium, no change of core — this subsumes the
  elliptic (`ChapterHermiteRelativeBound`) and shifted-core
  (`ChapterShiftedQuadratic*`) results on that core, and closes the item left open on
  2026-08-21i.
  (ii) `BookProof/ChapterCarlemanTwoStep.lean` + `BookProof/ChapterModeQuadraticEsa.lean`
  (namespaces `BookProof.CarlemanTwoStep`, `BookProof.ModeQuadratic`).  The harmonic
  form `πᵢ² + xᵢ²/4` is only a *line* inside the three-dimensional space of one-mode
  real quadratic forms; the other directions contain `aᵢ†²` and `aᵢ²`, which move an
  excitation number by **two** with amplitude `O(αᵢ)`.  `ladder2_eq_zero` proves the
  Carleman criterion for such a two-step recursion: the boundary layer is made two
  thick, the growth rate rises from `√N` to `N`, disjointness of the faces is replaced
  by a multiplicity bound (`sum_range_of_multiplicity`, `faceK_multiplicity`:
  each multi-index lies in at most two faces), and the divergence used is
  `∑ 1/(N+1) = ∞`.  Consequence (`mqOp_essentiallySelfAdjoint`): for **arbitrary** real
  `p, q, s, b, b'` the general mode-diagonal quadratic Hamiltonian
  `∑ᵢ (pᵢπᵢ² + qᵢxᵢ² + sᵢ·½(xᵢπᵢ + πᵢxᵢ)) + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)` is essentially
  self-adjoint on the plain Gauss–polynomial core and generates a complete unitary flow
  (`mqOp_stone_flow`) — elliptic, hyperbolic or parabolic in each mode, any signs,
  degenerate modes allowed.  In particular the **generator of dilations**
  `½∑ᵢ(xᵢπᵢ + πᵢxᵢ)` is essentially self-adjoint there
  (`dilation_essentiallySelfAdjoint`, `dilation_stone_flow`).  Symmetry comes from the
  Weyl ordering `weylProd` of the (symmetric) canonical pair, so the ordering caveat of
  §9 is settled by construction.  **Still open** in this strand: quadratic terms which
  *couple distinct modes* off-diagonally (`xᵢxⱼ`, `πᵢπⱼ`, `xᵢπⱼ` with `i ≠ j`) — the
  flux argument should extend, but the hop bookkeeping is no longer one-dimensional.

**A1 — UPDATE (2026-08-22b): the *general* real quadratic Hamiltonian is CLOSED —
distinct modes may now be coupled arbitrarily.**  Two new modules, both `sorry`-free
and axiom-clean, remove the mode-diagonality restriction left open on 2026-08-22.
  (i) `BookProof/ChapterCarlemanSimplex.lean` (namespace `BookProof.CarlemanSimplex`).
  The cube grading is the wrong one for cross terms; the right one is the **simplex**
  grading by total degree `|α| = ∑ᵢ αᵢ` (`deg`).  A product of two of `x, π` splits in
  the ladder variables into pair creation `α ↦ α + eᵢ + eⱼ`, pair annihilation
  `α ↦ α − eᵢ − eⱼ` and mode exchange `α ↦ α − eⱼ + eᵢ` (`pvec`, `shiftm`).  Only the
  first two change `|α|`, and by exactly `±2`, so they leak through a shell of
  thickness two, whose multiplicity is controlled (`sBd_multiplicity`,
  `shifted_sBd_multiplicity`, `sBd_mass_le`, `flux_bound_on`).  The exchange hops
  preserve `|α|` and carry **zero** flux: their amplitude matrix is Hermitian, so the
  shell sum is real and the imaginary part cancels pairwise (`sum_mterm_conj`,
  `sum_mterm_im`).  The flux identity is `flux_identityQ` and the divergence used is
  `∑ 1/(N+2) = ∞` (`not_summable_inv_natCast_add_two`).  Headline `ladderQ_eq_zero`:
  a square-summable family satisfying the general quadratic ladder recursion
  `LadderRecQ` at a non-real point vanishes identically.
  (ii) `BookProof/ChapterFullQuadraticEsa.lean` (namespace `BookProof.FullQuadratic`).
  `lop_lop_hermiteMv_gen` / `weyl_hermiteMv_gen` give the two-index ladder algebra
  uniformly in `i, j` (the diagonal `i = j` differs only by an extra constant);
  `fqQuadPoly`, `fqPoly`, `fqOp` assemble the Hamiltonian from Weyl-ordered products
  of the canonical pair, hence symmetric on the core (`fqOp_symmetric`), and
  `fqQuadPoly_hermiteMv` / `fqOp_hermiteCore` put it in ladder form: real diagonal
  `fqSymbol`, pair amplitude `fqAmp = Qᵢⱼ − Pᵢⱼ/4 + i Sᵢⱼ/2`, Hermitian exchange
  matrix `fqExch` (`fqExch_hermitian`) and one-step amplitude `bᵢ + i b'ᵢ/2`.
  Consequence (`fqOp_essentiallySelfAdjoint`): for **arbitrary** real matrices
  `P, Q, S` and **arbitrary** real vectors `b, b'`, the operator
  `H = ∑_{i,j} (Pᵢⱼπᵢπⱼ + Qᵢⱼxᵢxⱼ + Sᵢⱼ·½(xᵢπⱼ + πⱼxᵢ)) + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)` — every
  real quadratic-plus-linear Hamiltonian in `d` degrees of freedom, with no
  ellipticity, no definiteness, no non-degeneracy and no classical equilibrium — is
  essentially self-adjoint on the plain Gauss–polynomial core and generates a complete
  unitary flow (`fqOp_stone_flow`).  In particular so does the purely off-diagonal
  cross term `½(xᵢπⱼ + πⱼxᵢ) + ½(xⱼπᵢ + πᵢxⱼ)` (`crossTerm_essentiallySelfAdjoint`,
  `crossTerm_stone_flow`), and — for an *antisymmetric* exchange matrix, where
  `∑_{i,j} Sᵢⱼ·½(xᵢπⱼ + πⱼxᵢ) = ∑_{i<j} Sᵢⱼ(xᵢπⱼ − xⱼπᵢ)` — the **angular-momentum
  generators** `xₖπ_l − x_lπₖ` (`rotMat`, `fqQuadPoly_rotMat`,
  `angularMomentum_essentiallySelfAdjoint`, `angularMomentum_stone_flow`), the compact
  counterparts of the dilation generator of the previous wave.  This closes the finite-dimensional quadratic strand
  entirely; what remains open in A1 is the **continuum** statement below.

**A1 — UPDATE (2026-08-22c): the quadratic strand now runs at *infinitely many
modes*, on the boson Fock space.**  Two further modules, both `sorry`-free and
axiom-clean (`propext`, `Classical.choice`, `Quot.sound` only), lift the closed
finite-dimensional quadratic result of 2026-08-22b to an arbitrary mode set.
  (i) `BookProof/ChapterOperatorSeriesEsa.lean` (namespace
  `BookProof.OperatorSeries`).  The two Faris–Lavine inequalities relative to a
  positive comparison operator `N` — the relative bound `‖Hx‖ ≤ A‖Nx‖` and the
  commutator-form bound `|⟪x, i[H, N]x⟫| ≤ B⟪x, Nx⟫` — are *additive*, and
  `commForm_eq_neg_two_im` exhibits the commutator form as `−2 Im⟪Hx, Nx⟫`, which
  makes the additivity transparent and the passage to a limit an exchange of a sum
  with an imaginary part.  `seriesOp` sums a family `T : κ → (maxDom c →ₗ L2I ι)`
  whose relative bounds `a k` are summable; `seriesOp_symmetricOn`,
  `seriesOp_norm_le` and `seriesOp_commForm_le` carry the three properties to the
  sum with constants `∑' a k` and `∑' b k`, and
  `essentiallySelfAdjointOn_finiteModes_of_series` is the resulting instrument:
  a summable family of symmetric operators, each relatively bounded by `N` and each
  with commutator form dominated by `N`, sums to an operator essentially
  self-adjoint on the finite-mode core.
  (ii) `BookProof/ChapterFockQuadraticEsa.lean` (namespace
  `BookProof.FockQuadratic`).  The Hilbert space is the boson Fock space
  `ℓ²(ι →₀ ℕ)` of occupation-number configurations over an *arbitrary* mode set
  `ι`; the comparison symbol is `σ(α) = ω(α) + |α| + 1` (`sig`), the free energy
  (`wsum`) plus the total occupation number (`deg`) plus one — the free Hamiltonian
  plus the number operator plus one.  `fall`, `amp` and `tgt` are the falling
  factorial of a multi-index, the ladder amplitude of the monomial `a^{†P}a^{Q}` and
  the configuration it hops to; `amp_symm` is the self-adjointness of the amplitude
  under `(P, Q) ↦ (Q, P)`, and `amp_le_sig` / `amp_le_sig_tgt` are the two-sided
  bound `amp ≤ 2σ` at both ends of the hop, which is exactly what a quadratic
  monomial `|P| + |Q| ≤ 2` satisfies.  `hopOp` realizes the monomial on the maximal
  domain of `σ`, with `hopOp_norm_le` (relative bound `2`) and `hopOp_pairing` (the
  adjoint relation `⟪a^{†P}a^{Q}x, y⟫ = ⟪x, a^{†Q}a^{P}y⟫`, proved by reindexing the
  coefficient sum along the hop bijection `hopEquiv`).  `pairOp` is the Hermitian
  combination `g a^{†P}a^{Q} + conj(g) a^{†Q}a^{P}`; `pairOp_commForm_le` is the
  substantive estimate: the two halves of the pairing recombine so that only the
  *difference* `σ(α) − σ(α − P + Q)` survives in the imaginary part, and that
  difference is bounded by `ω(P) + ω(Q) + 2` while the amplitude is dominated by an
  AM–GM step (`amp_mul_le`), giving
  `|commForm(pairOp)| ≤ 4‖g‖(ω(P) + ω(Q) + 2)·quadForm N`.  The free part `freeOp`
  is symmetric, dominated by `N` and *commutes* with it (`freeOp_commForm = 0`).
  Headline `fockH_essentiallySelfAdjointOn_core`: for an arbitrary mode set, an
  arbitrary non-negative — in particular possibly unbounded — dispersion `ω`, and an
  arbitrary family of quadratic monomials with couplings `g` subject only to the
  weighted absolute summability `∑ₖ ‖gₖ‖(ω(Pₖ) + ω(Qₖ) + 2) < ∞`, the second-quantized
  Hamiltonian `H = ∑ᵢ ωᵢ aᵢ†aᵢ + ∑ₖ (gₖ a^{†Pₖ}a^{Qₖ} + conj(gₖ) a^{†Qₖ}a^{Pₖ})` is
  essentially self-adjoint on the finite-particle core of the Fock space.
  `bogoliubov_essentiallySelfAdjointOn_core` is the pair-creation (Bogoliubov)
  specialization `Pₖ = e_{mₖ} + e_{nₖ}`, `Qₖ = 0`, whose hypothesis reads
  `∑ₖ ‖gₖ‖(ω_{mₖ} + ω_{nₖ} + 2) < ∞`.  Both modules are registered in
  `BookProof.lean` and certified in `BookProof/ChapterRoadmapAudit.lean`.  What
  remains open in A1 is still the **continuum** statement below.

**A1 — UPDATE (2026-08-22d): the *gluing* half of the direct-integral step is CLOSED, in
its orthogonal-direct-sum form, and the continuum Navier–Stokes Fock Hamiltonian is now
essentially self-adjoint on the whole Fock space.**  `BookProof/ChapterDirectSumEsa.lean`
(namespace `BookProof.DirectSumEsa`) isolates the step that passes essential
self-adjointness from the fibres of an orthogonal decomposition to the whole space.  A
deficiency vector of `⊕ᵢ Hᵢ` tested against a state living in a single fibre satisfies
exactly the fibre deficiency identity, so each of its coordinates vanishes
(`dsOp_deficiencyTrivialAt`); hence `dsOp_essentiallySelfAdjointOn` — if every fibre
operator is essentially self-adjoint on its core `Dᵢ`, the direct sum is essentially
self-adjoint on the algebraic direct sum `dsCore D` of the cores.  No relative bound, no
comparison operator and no commutator estimate enter, and `dsCore_dense` adds density of
the glued core.  `dsOpD`, `dsOpD_hasZeroDeficiencyOn`, `dsOpD_isSymmetricDom` are the
domain-preserving forms used by the Navier–Stokes chapters.  Payoff: on the *whole*
continuum Fock space `⊕ₙ L²(ℝⁿ)` of the parcel picture, `fockH_hasZeroDeficiencyOn` gives
essential self-adjointness of the second-quantized Hamiltonian `ĥ = ∫ w(ξ)a†(ξ)a(ξ)dξ` for
an **arbitrary measurable** field `w` (`fockCore_dense`, `fockH_isSymmetricDom`);
`ChapterNavierStokesFockContinuum` had this one parcel sector at a time.  A second pass
adds `essentiallySelfAdjointOn_of_hasZeroDeficiencyOn` (the domain-preserving
formulation implies the ambient-space one) and runs the Stone bridge on it:
`dsOpD_stone_flow` is the general glued instrument — dense fibre cores with symmetric
fibre operators of vanishing deficiency give a self-adjoint extension of the glued
operator together with the unitary group it generates — and `fockH_stone_flow` is its
specialization, the complete unitary group `e^{−itĥ}` on the whole continuum Fock space.
**Still open:**
the gluing is *orthogonal* (mutually orthogonal invariant fibres), so it is the discrete
form of the direct-integral step, and the QG continuum item below — producing the fibre
decomposition for `□ + V` with a general Faris–Lavine potential — is untouched by it.

**A1. QG continuum ESA with an unbounded potential (the hyperbolic fibrewise /
direct-integral step).**  The step that would pass ESA to the full `□ + V` with
`V` bounded above by a quadratic (§9.5, the Faris–Lavine class; the
`-d²/dx² − x⁴` sign record) is **not** proved.  `ChapterWaveUnboundedPotential`
supplies the position-space half (`potentialOp_essentiallySelfAdjoint` for
temperate-growth potentials, `multiplierOp_essentiallySelfAdjoint`,
`wave_add_truncatedPotential_essentiallySelfAdjoint`) and
`ChapterHarmonicOscillatorEsa` the sign-correct `-d²/dx² + x²/4` oscillator; what
is missing is the fibrewise / direct-integral gluing.  This is the distinction
from the NS case, where the fibrewise step is done.  Start: read §9.5 and
`STRICHARTZ_WAVE_ESA.md`; the target is a `□ + V_esa`-style theorem for the
unbounded-below-by-a-quadratic (Faris–Lavine) class, using the already-proved
cut-off lemma and the finite-speed/localized-energy argument.

**A2 — CLOSED (2026-08-21h).**  `BookProof/ChapterUnboundedSpectralModel.lean`
(namespace `BookProof.UnboundedSpectralModel`) supplies the missing existence
step, by the classical resolvent (Cayley) route.  For a densely defined
self-adjoint `A` (the `UnboundedSelfAdjoint` bundle of `ChapterStoneResolvent`)
the resolvent `R = (A − i)⁻¹` is a *bounded* operator (`resOp`) which is injective
(`resOp_injective`), has range exactly `dom A` (`exists_resOp_eq`), has adjoint
the resolvent at the conjugate point (`adjoint_resCLM`) and commutes with it, so
it is **normal** (`isStarNormal_resOp`).  The bounded multiplication model of
`ChapterSpectralMultiplication` / `ChapterSpectralDirectSum` therefore applies to
`R`, and `A = R⁻¹ + i` is read back off it (`model_mem`, `model_apply`).  The
symmetry of `A` in the model forces the multiplication operator by the Cayley
symbol `Im z − |z|²` to vanish (`mulRep_cayleyFn_eq_zero`), so the representing
measure is carried by the Cayley circle `|z|² = Im z` (`model_ae_circle`) and
gives no mass to `z = 0` (`model_ae_ne_zero`); consequently the multiplier
`1/z + i` agrees a.e. with the **real** function `Re z/|z|²`
(`model_ae_real_multiplier`).  Headlines:
`unbounded_multiplication_model_cyclic` (cyclic resolvent vector),
`unbounded_multiplication_model_general` (**every** densely defined self-adjoint
operator on a complex Hilbert space, no cyclic vector and no separability), and
`unbounded_multiplication_model_separable` (countably many summands on a
separable space).  All `sorry`-free and axiom-clean; certified in
`ChapterRoadmapAudit` and cited from `Book/ConditionalUnitary.lean`.

**A2 (stale, superseded by the update above). Spectral theorem for unbounded
self-adjoint operators (the diagonalizing unitary).**  `ChapterUnitaryTransport` carries self-adjointness, the unitary
group and Stone's relation through any *given* unitary change of Hilbert space,
and `ChapterSpectralMultiplication` gives the spectral theorem in
multiplication-operator form for a *cyclic* vector; but the *existence* of the
diagonalizing unitary for a general unbounded self-adjoint operator is still
missing (recorded in the `ChapterUnitaryTransport` module docstring and §9 item
3).  This is the step "behind a continuum Laplacian" and is the natural
completion of the general Stone theorem
(`ChapterStoneResolvent`–`ChapterStoneSeparable`).  Substantial, self-contained
project.

**A3 — ALREADY CLOSED (verified 2026-08-21; the item below is stale).**  The
sign-flip unitary *is* formalized, in
`BookProof/ChapterNavierStokesSignFlip.lean` (namespace
`BookProof.NavierStokesFlow.SignFlip`): `flipU`, `shiftH_flip`,
`essentiallySelfAdjointOn_of_intertwine`, `saffH_essentiallySelfAdjointOn_core`
(arbitrary real `c`) and the block assembly `sblockH_essentiallySelfAdjointOn_core`
for a family `c : J → ℝ` of arbitrary signs; `ChapterNavierStokesSignedShift`
removes the sign and monotonicity restrictions on a hopping amplitude altogether.
The `c_j ≥ 0` sentence that survives in the `ChapterNavierStokesAffineBlockEsa` and
`ChapterNavierStokesAffineFiberEsa` docstrings is a *local* boundary of those two
modules, not a gap in the development.

**A3. NS sign-flip unitary (drop the `c_j ≥ 0` restriction).**  In the affine-block
ESA the hopping amplitude is assumed non-negative (`ChapterNavierStokesAffineBlockEsa`,
§9 item 4 boundary); the sign-flip unitary `x_n ↦ (−1)ⁿ x_n` that would remove
the restriction is recorded but **not formalized**.  This is a small, concrete,
bounded theorem in the already-proved framework (mirror the `SignFlip`
`essentiallySelfAdjointOn_of_intertwine` pattern).

**A4 — CLOSED (2026-08-23b).**  `BookProof/ChapterNavierStokesDiffFarisLavine.lean`
(namespace `BookProof.NavierStokesFlow.DiffFarisLavine`) carries out exactly the
route described in the item below: the comparison operator is the *differential*
harmonic oscillator `nsDiffN μ = 2μ ∑ᵢ (πᵢ² + uᵢ²/4) + 1`, identified with the
transported number operator by `oscOp_eq_number` (`πᵢ² + uᵢ²/4 = aᵢ†aᵢ + ½` on the
Gauss–polynomial core) and `embedCore_surjective`; the relative bound
`nsDiffH_relative_bound` and the form-commutator bound `nsDiffH_commForm_bound` hold
for the differential operator, and their maximal-domain versions feed the
Faris–Lavine criterion in `L²(ℝ³)` to give `nsDiffH_esa_of_farisLavine`.  The item
below is retained for the record.

**A4. NS quadratic-symbol FL estimate as an actual differential operator.**  The
two Faris–Lavine inequalities for the quadratic symbol
`A_i = u_j u_{i,j} − ν u_{i,jj}` as a differential operator on `L²(du)` (§9 item
4 residual, lines above) are a concrete FL *estimate* (relative bound +
form-commutator bound) in the already-proved framework — not a research project
needing new analytic machinery.  Note: the 2026-08-20k differential realization
(`ChapterNavierStokesDifferentialL2.nsQuadraticDiffH_essentiallySelfAdjointOn_core`)
already establishes ESA of the differentially-written symbol by a different
(basis) route; this item is the alternative FL-estimate proof that would unify
the abstract and differential pictures and is the plan's original §7 route.

**A5 update (2026-08-22h, one particle → the nested Fock space).**  The scalaron
Hamiltonian is now carried from the one-particle Hilbert space to the
finite-particle (nested) Fock space, in `BookProof/ChapterScalaronFockEsa.lean`
(namespace `BookProof.ScalaronFock`), by *linking already-proved theorems*: the
one-particle statements of `ChapterScalaronCoreEsa` on the dense compactly supported
smooth core, and the orthogonal direct-sum gluing instrument of
`ChapterDirectSumEsa` (`dsCore_dense`, `dsOp_symmetricOn`,
`dsOp_deficiencyTrivialAt`, `dsOp_essentiallySelfAdjointOn`).  Contents: the generic
instrument `fockSmoothPotential_esa` / `fockSmoothPotential_stone_flow` for an
arbitrary family of *smooth* `n`-particle potentials on `⊕ₙ L²(Eₙ)` (no growth, no
boundedness, no semiboundedness); the many-body gauge-fixed `R + αR²` potential
`qgManyPotential = ∑ⱼ (V₃(R_c ⱼ) + V(φ ⱼ))` on `qgSector n = ℝ^(n×2)`, smooth
(`contDiff_qgManyPotential`), bounded below by `−n·M⁴/(16α)` (`qgManyPotential_ge`)
and equal at `n = 1` to the one-particle potential (`qgManyPotential_one`); and the
Fock statements `qgFockCore_dense`, `qgScalaronFock_symmetric`,
`qgScalaronFock_deficiencyTrivialAt`, `qgScalaronFock_esa` and
`qgScalaronFock_stone_flow` (the unitary group `e^{−itH}` on
`⊕ₙ L²(ℝ^(n×2))`), together with the same in the mode (Hermite) realisation
(`qgScalaronModeFock_esa`, `qgScalaronModeFock_stone_flow`).  Honest boundary: the
gluing is over an *orthogonal* direct sum, i.e. the Hamiltonian preserves particle
number — exactly the finite-particle situation; sector-changing interactions and the
unlocalized `□ + V` continuum gluing are unchanged.

**A5 update (2026-08-22g, the scalaron sector).**  The exponential wall of the
Einstein-frame scalaron potential is now settled, in
`BookProof/ChapterScalaronCoreEsa.lean` (namespace `BookProof.ScalaronEsa`):
`starobinskyV_not_hasTemperateGrowth` proves the potential is *not* of temperate
growth, so `potentialOp_essentiallySelfAdjoint` does not apply to it; but on the
dense compactly supported smooth core `ccDomain` (`ccDomain_dense`) multiplication
by an **arbitrary smooth** real potential is essentially self-adjoint
(`smoothPotential_essentiallySelfAdjoint`) with no growth, boundedness or
semiboundedness hypothesis.  Hence `starobinskyV_essentiallySelfAdjoint`, the full
gauge-fixed potential `scalaronFullPotential_essentiallySelfAdjoint` with its lower
bound `scalaronFullPotential_ge ≥ −M⁴/(16α)`, the symmetry of `□ + V` on that dense
core (`wave_add_scalaron_symmetric`), the truncation theorem with temperate growth
removed (`wave_add_smoothTruncatedPotential_essentiallySelfAdjoint`,
`wave_add_scalaronTruncated_esa`), and at the mode level the Hamiltonian *including*
the scalaron potential with its flow (`qgScalaronMode_esa`,
`qgScalaronMode_potential_ge`, `qgScalaron_stone_flow`).  The residual is unchanged
and is the *gluing* (Strichartz finite speed / direct integral) for the unlocalized
continuum sum — neither the polynomial degree nor the exponential wall.

**A5. R + αR² (Starobinsky) gravity: ESA and the continuous flow of the
gauge-fixed Hamiltonian, with the potential bound after the densitized change of
variables — steps 1 and (at the mode level) 3/4 LANDED (2026-08-22f,
`BookProof/ChapterStarobinskyPotential.lean`, deliverable `qgR2_stone_flow`); step 2,
the continuum densitized change of variables, CLOSED 2026-08-23c
(`BookProof/ChapterScalaronDensitizedTransfer.lean`: `densConfV_ge`,
`halfDensityUnitary_intertwines`, `physConf_hasZeroDeficiencyOn_transfer`,
`densConfOp_quadForm_ge`), leaving only the same Strichartz/direct-integral residue
as A1.**  New plan item (2026-08-22, full write-up in §10.5), derived from
`../unfer/docs/qg_starobinsky_hamiltonian.cdb`.  The αR² term gives the
conformal-mode potential the bound pure GR lacks: `V3(R_c) = α(R_c − M²/(4α))² −
M⁴/(16α) ≥ −M⁴/(16α)`, and the Einstein-frame scalaron potential is
`V(φ) = (M⁴/16α)(1 − e^{−√(2/3)φ/M})² ≥ 0`.  Steps: (1) formalize the two
bounds; (2) carry the bound through the densitized change of variables
(`ChapterQuantumGravityDensitized` / `ChapterQuantumGravityHalfDensity`), proving
the transformed potential is bounded below — the sign the ESA routes need and
the step that fails for pure GR (§10.3, the `−d²/dx² − x⁴` record); (3) ESA of
the full Hamiltonian — elliptic scalaron sector via the Kato–Rellich / Sears
route, hyperbolic conformal mode via the proved mode-by-mode machinery; (4) the
**continuous flow** via the Stone bridge: `qgR2_stone_flow`, the QG analogue of
`ns_stone_flow` / `ym_fock_stone_flow`, with `ChapterStoneEigenflow` giving the
explicit phase action on the eigenbasis.  Natural first sub-target: the
one-variable scalaron `−Δ + V(φ)` (`V ≥ 0`, smooth, exponential wall).  Honest
boundary: the continuum `L²(ℝ⁸⁴)` statement and the gauge/BRST sector remain as
in §10.3 — the residual is the Strichartz finite-speed *gluing*, **not** the
polynomial degree: the R² potential is a high-degree polynomial in the
densitized fields and their spatial derivatives, and that class is already
covered by the proved theorems (`potentialOp_essentiallySelfAdjoint`,
`polynomialPotential_essentiallySelfAdjoint`, and the mode-level
`qgModeHamiltonian_essentiallySelfAdjoint` with trivial deficiency at every
non-real `z`).

**A6. NS differential-realization Hashimoto/SIRK selection (the missing layer on
`L²(du₁du₂du₃)`) — CLOSED (2026-08-22f,
`BookProof/ChapterNavierStokesDiffHashimoto.lean`; see the leading status block).**  The Hashimoto/SIRK selection theorem for the Navier–Stokes
generator is proved on the *abstract sequence-space* realization
(`ChapterNavierStokesHashimoto.ns_hashimoto_selects`: the fiber generator
`velCore` on `ℓ²(Vel)`, `Vel = Fin 3 → ℕ`), while the *differential* realization
— `ChapterNavierStokesDifferentialL2.nsDiffH_essentiallySelfAdjointOn_core` /
`nsQuadraticDiffH_essentiallySelfAdjointOn_core`, the operator written with
`πᵢ = −i∂/∂uᵢ` and `uᵢ` a genuine multiplication operator on the Hermite core of
`L²(du₁du₂du₃)`, the one that “is” the physics — is **ESA but has no Hashimoto
theorem yet**.  Goal: **`nsDiffH_hashimoto_selects`** — for an arbitrary
sequence of non-real shifts the SIRK resolvents of the differential operator
exist, are bounded by `1/|Im γ_j|`, share the domain of the generator, satisfy
the resolvent identity and the Hashimoto–Nodera rational-Krylov relation, have
strongly convergent Galerkin truncations (product-Hermite basis of `L²(ℝ³)`), and
each determines the generator completely — the unique self-adjoint extension
(the closure), no positivity.  Route: the abstract
`EsaClosure.hashimoto_multishift_selects_esa` is already stated for an *arbitrary*
Hilbert basis, and `velUnitary : ℓ²(Vel) ≃ₗᵢ L²(ℝ³)` transports the core
(`map_finiteModes`) and intertwines the operators (`intertwine_ann` /
`intertwine_cre`, `conj_canH`), so the selection transports along it; or
instantiate `hashimoto_multishift_selects_esa` directly with the product-Hermite
basis.  This completes the parity recorded in the 2026-08-20d rigor-parity note:
every realization layer of the Eulerian fiber generator (and, via
`lagrangian_hashimoto_selects`, the Lagrangian one) is then covered by the SIRK
selection.  Complement of A4 (the alternative FL-estimate proof on the same
operator, which would unify the abstract and differential pictures); honest
boundary unchanged (Contention D5).

#### B. Verification — the §8 gate (highest priority, no new mathematics)

**B1 — RE-RUN AND GREEN (2026-08-22f, after the differential-Hashimoto /
general-hop-registration / Starobinsky wave).**  `lake build` (**8683 jobs**,
BookProof + Book + Singularity), `lake build RandomMap` (**8039 jobs**),
`lake build UsedRoute` (**8049 jobs**), `./patches/build-book.sh` (368 jobs;
`<base>`/fragment-link asserts passing) and `./patches/check-katex.sh`
(**2526 snippets, 0 KaTeX failures**) all succeed, including the new
`Book/FreeField.lean` paragraph citing
`BookProof.NavierStokesFlow.DiffHashimoto.*` and the new
`Book/DiffeomorphismsGravity.lean` section citing `BookProof.Starobinsky.*`.  All 825
`#print axioms` lines of `BookProof/ChapterRoadmapAudit.lean` report only `propext`,
`Classical.choice`, `Quot.sound`; no `sorryAx` anywhere.  The sorry/axiom audit is
unchanged and clean: no `sorry` and no `^axiom` declaration occurs outside a docstring
or comment under `BookProof/`, `Book/`, `Singularity/`, `RandomMap/`, `PnpProof/`; the
only `sorry`s in the repository remain in the quarantined legacy RH route under
`UsedRoute/`/`UnusedRoute/`.  The `patches/*.sh` executable bit had again been lost in
this snapshot and was restored.

**B1 — RE-RUN AND GREEN (2026-08-22d, after the direct-sum gluing wave).**
`lake build` (**8680 jobs**, BookProof + Book + Singularity), `lake build RandomMap`
(**8039 jobs**), `lake build UsedRoute` (**8049 jobs**), `./patches/build-book.sh`
(`<base>`/fragment-link asserts passing) and `./patches/check-katex.sh`
(**2507 snippets, 0 KaTeX failures**) all succeed, including the new `Book/FreeField.lean`
paragraph citing `BookProof.DirectSumEsa.*`.  Every `#print axioms` line of the new module
in `BookProof/ChapterRoadmapAudit.lean` reports only `propext`, `Classical.choice`,
`Quot.sound`.  The sorry/axiom audit is unchanged and clean: no `sorry` and no `^axiom`
declaration occurs outside a docstring or comment under `BookProof/`, `Book/`,
`Singularity/`, `RandomMap/`, `PnpProof/`; the only `sorry`s in the repository remain in
the quarantined legacy RH route under `UsedRoute/`/`UnusedRoute/`.

**B1 — RE-RUN AND GREEN (2026-08-22c, after the infinite-mode Fock wave).**
`lake build` (**8679 jobs**, BookProof + Book + Singularity), `lake build RandomMap`
(**8039 jobs**), `lake build UsedRoute` (**8049 jobs**), `./patches/build-book.sh`
(368 jobs; `<base>`/fragment-link asserts passing) and `./patches/check-katex.sh`
(**2507 snippets, 0 KaTeX failures**) all succeed, including the new
`Book/DiffeomorphismsGravity.lean` paragraph citing `BookProof.OperatorSeries.*` and
`BookProof.FockQuadratic.*`.  The sorry/axiom audit is unchanged and clean: no `sorry`
and no `^axiom` declaration occurs outside a docstring or comment under `BookProof/`,
`Book/`, `Singularity/`, `RandomMap/`, `PnpProof/`; the only `sorry`s in the repository
remain in the quarantined legacy RH route under `UsedRoute/`/`UnusedRoute/`.  The
`patches/*.sh` executable bit had again been lost in this snapshot and was restored and
committed.

**B1 — RE-RUN AND GREEN (2026-08-22b, after the simplex-Carleman /
general-quadratic wave).**  `lake build` (**8677 jobs**, BookProof + Book +
Singularity), `lake build RandomMap` (**8039 jobs**), `lake build UsedRoute`
(**8049 jobs**), `./patches/build-book.sh` (368 jobs; `<base>`/fragment-link
asserts passing) and `./patches/check-katex.sh` (**2490 snippets, 0 KaTeX
failures**) all succeed, including the new `Book/DiffeomorphismsGravity.lean`
paragraph citing `BookProof.CarlemanSimplex.*` and `BookProof.FullQuadratic.*`.
The sorry/axiom audit is unchanged and clean: no `sorry` and no `^axiom`
declaration occurs outside a docstring or comment under `BookProof/`, `Book/`,
`Singularity/`, `RandomMap/`, `PnpProof/`; the only `sorry`s in the repository
remain in the quarantined legacy RH route under `UsedRoute/`/`UnusedRoute/`.
The `patches/*.sh` executable bit had again been lost in this snapshot and was
restored and committed.

**B1 — RE-RUN AND GREEN (2026-08-22a, after the two-step Carleman /
mode-diagonal-quadratic wave).**  `lake build` (**8675 jobs**, BookProof + Book +
Singularity), `lake build RandomMap` (**8039 jobs**), `lake build UsedRoute`
(**8049 jobs**), `./patches/build-book.sh` (368 jobs; `<base>`/fragment-link
asserts passing) and `./patches/check-katex.sh` (**2466 snippets, 0 KaTeX
failures**) all succeed, including the two new `Book/DiffeomorphismsGravity.lean`
paragraphs citing `BookProof.HermiteCarleman.*`, `BookProof.CarlemanTwoStep.*`
and `BookProof.ModeQuadratic.*`.  The sorry/axiom audit is unchanged and clean:
no `sorry` and no `^axiom` declaration occurs outside a docstring or comment
under `BookProof/`, `Book/`, `Singularity/`, `RandomMap/`, `PnpProof/`; the only
`sorry`s in the repository remain in the quarantined legacy RH route under
`UsedRoute/`/`UnusedRoute/`.  The `patches/*.sh` executable bit had again been
lost in this snapshot and was restored and committed.

**B1 — RE-RUN AND GREEN (2026-08-21i, after the quadrature wave).**  `lake build`
(8672 jobs, BookProof + Book + Singularity), `lake build RandomMap` (8039 jobs),
`lake build UsedRoute` (8049 jobs), `./patches/build-book.sh` (with the
`<base>`/fragment-link asserts passing) and `./patches/check-katex.sh` (**2441
snippets, 0 KaTeX failures**) all succeed.  The sorry/axiom audit and the isolation
greps are unchanged and clean: no `sorry` and no `^axiom` occurs outside a docstring
or comment under `BookProof/`, `Book/`, `Singularity/`, `RandomMap/`, `PnpProof/`,
and the only `sorry`s in the repository remain in the quarantined legacy RH route
under `UsedRoute/`/`UnusedRoute/`.  The `patches/*.sh` executable bit had again been
lost in this snapshot and is restored and committed.

**B1 — RE-RUN AND GREEN (2026-08-21g, after the singular-form and eigenflow waves).**
`lake build` (8668 jobs, BookProof + Book + Singularity), `lake build RandomMap` (8039
jobs), `lake build UsedRoute` (8049 jobs), `./patches/build-book.sh` (with the
`<base>`/fragment-link asserts passing) and `./patches/check-katex.sh` (**2402 snippets,
0 KaTeX failures**) all succeed.  The sorry/axiom audit and the isolation greps are
unchanged and clean: the only `sorry`s in the repository are in the quarantined legacy
RH route under `UsedRoute/`/`UnusedRoute/`, and every remaining textual match for
`sorry` or `axiom` under `BookProof/`, `Book/`, `Singularity/`, `RandomMap/`,
`PnpProof/` is inside a docstring or comment.  The `patches/*.sh` executable bit had
again been lost in this snapshot and is restored and committed.

**B1 — RE-RUN AND GREEN (2026-08-21d, after the two new quadratic waves).**
`lake build` (8663 jobs, BookProof + Book + Singularity), `lake build RandomMap`,
`lake build UsedRoute`, `./patches/build-book.sh` (with the `<base>`/fragment-link
asserts passing) and `./patches/check-katex.sh` (**2353 snippets, 0 KaTeX failures**)
all succeed.  The sorry/axiom audit and the isolation greps are unchanged and clean:
the only `sorry`s in the repository are in the quarantined legacy RH route under
`UsedRoute/`/`UnusedRoute/`, and every remaining textual match for `sorry` or `axiom`
under `BookProof/`, `Book/`, `Singularity/`, `RandomMap/`, `PnpProof/` is inside a
docstring or comment.  The `patches/*.sh` executable bit had again been lost in this
snapshot and is now restored **and committed**, so the repair should not recur.

**B1 — DONE (2026-08-21, earlier repository snapshot).**  The gate was re-run here and
is green: `lake build` (BookProof + Book + Singularity), `lake build RandomMap`,
`lake build UsedRoute`, `./patches/build-book.sh` (patches → render → postprocess,
with the `<base>`/fragment-link asserts passing) and `./patches/check-katex.sh`
(**2300 snippets, 0 KaTeX failures**) all succeed.  Audits: no `sorry` and no
`^axiom` in `BookProof/`, `PnpProof/`, `Singularity/`, `RandomMap/`; the only
`sorry`s are in the quarantined legacy RH route under `UsedRoute/` and
`UnusedRoute/`, neither of which is a default target.  Isolation: no `BookProof/`
file reachable from a build target imports `PnpProof`, `UnusedRoute` or
`UsedRoute` (the two audit-only files `BookProof/B1_randomMap2_axioms.lean` and
`BookProof/randomMap2_axioms.lean` are in no target, as their docstrings record),
and `RandomMap/` does not import `UnusedRoute`.  One hygiene repair was needed:
the four scripts under `patches/` had lost their executable bit in this snapshot
and could not be run; the mode is restored.

**B1. Re-run the §8 verification gate.**  The gate was last verified green at
2026-08-18c; the 2026-08-20…20k waves (all the Navier–Stokes modules,
`ChapterGaugeFixing`, the Stone-theorem and bridge/flows modules, and the
`ChapterHermiteProductBasis` / `ChapterNavierStokesDifferentialL2` /
`ChapterNavierStokesLagrangianCanonical` realization wave) **and** the Aristotle
2026-08-24 SIRK / QG Hermite / Friedrichs / Fermion-Fock wave (26 new modules +
4 new Book chapters) were verified only in the producing workspace, **not** in
this repository snapshot (the merge into this repo was made without compiling).
First actions, in order: `lake build`, `lake build RandomMap`, `lake build UsedRoute`,
`./patches/build-book.sh`, `./patches/check-katex.sh`, then the sorry/axiom audit
(only the quarantined legacy RH route under `UsedRoute/`/`UnusedRoute/` may carry
`sorry`s) and the isolation greps.  Record the results in the §8 gate note and in
`BookProof/STATUS.md`.

#### C. Editorial / prose residue (small, one-line edits, no new mathematics)

**C1–C3 — VERIFIED ALREADY CLOSED IN THIS SNAPSHOT (2026-08-21i); the three items
below are stale.**  C1: `Book/Introduction.lean` already frames the slogan as
rhetoric and attaches the manuscript's caveat ("a generalization of *classical
statistical mechanics*, *not* of probability theory itself"), cross-referencing the
deterministic-transformations and collapse chapters — exactly the resolution the
item asks for.  C2: `Book/OdeSingularity.lean` already carries the honesty flag
reporting that the method is "*not completely satisfactory*" for the second blow-up
problem.  C3: `Issues.md` §6 is already headed "Formerly deferred chapters — **DONE
(framing settled, August 2026)**", and §0b/§5 record the current chapter set; only
the §5 row of this plan still said STALE, and it is now corrected.  C4 remains a
standing rule rather than a task.

**C1. Contention D1** — resolve the intro-slogan internal tension
(`Book/Introduction.lean` vs `Book/DeterministicTransformations`): either add the
"(not of probability theory)" caveat to the Introduction or frame it as rhetoric
with a cross-referencing footnote.  One-line edit; flag to author.

**C2. Contention D2** — add one honesty sentence to `Book/OdeSingularity.lean`
(near lines 45–48) reporting the manuscript's own caveat on the second blow-up
problem, mirroring the honesty-flag style used for the ODE theorems.

**C3. Curated-edition coverage table** — re-mark the "deferred" physics chapters
(`GaugeSymmetry`, `PhysicalParity`, `YangMillsQuantization`, `RealRepresentations`,
`DiffeomorphismsGravity`, `AlignedDeepLearning`, `GribovAmbiguity`,
`ConsciousnessBayesianPrior`) as `DONE (framing settled)` in the Issues §5
disposition (item 2) now that they exist under `Book/` and are `{include}`d in
`Book.lean`.

**C4. Long `#check` types** — restate any remaining unwieldy `#check` as a clean
`example` (with a readable prose paraphrase) when a chapter is next edited.

#### E. On-going discipline (applies to every edit)

**E1. Keep the Book ↔ BookProof correspondence exact.**  The `#check` blocks in
`Book/` (in particular `Book/FreeField.lean`, now the single point of pedagogy
for the NS/QG/QYM/realization waves) must stay in one-to-one sync with the module
and theorem names in `BookProof/`.  Any new BookProof theorem cited in the Book
must be registered in `BookProof.lean` and `#print axioms`-certified in
`BookProof/ChapterRoadmapAudit.lean`.

**E2. Do not re-open closed items.**  Do not re-open GAP-1 / GAP-2 or any closed
§9 item without a concrete new mathematical question.  The classical NS
regularity question (Contention D5) and the QG / NS mass gaps remain the author's
explicit scope cuts and are out of scope unless the author changes that decision.

---

## 10. Quantum Gravity: the ESA of the 3D gauge-fixed Hamiltonian (candidate
route, record — not a proved Lean theorem)

The manuscript's *final, 3D gauge-fixed* gravity Hamiltonian
(`book.tex` §"Classical Hamiltonian" / §"Quantum Hamiltonian", ~8138–8310, on
`Γ^s(L²(ℝ⁸⁴×ℤ₂¹⁹)) ⊗ Γ^a(L²(ℝ⁸⁴×ℤ₂¹⁹))`, the `ℝ⁸⁴` = 4 coordinates + 16 tetrads
`e_μ^a` + their derivatives, `ℤ₂¹⁹` the diffeomorphism ghosts) contains the
**singular** kinetic terms

```
H = (1/16e) S^{ab} S_ab − (1/24e) P² + …
```

whose `1/e` denominator (with `e = det(e_i^a)`) diverges as the tetrad
determinant vanishes. This record states the *candidate route* the manuscript's
own analytic-layer pattern (the NS-FLOW wave) suggests, following the same
honesty discipline: **named theorems, never claimed Lean results.**

### 10.1 The change of variables: densitized tetrads

Perform the canonical change of variables to **densitized tetrad variables**

```
y   = √e            (= (det e_i^a)^{1/2})
ẽ_i^a = √e · e_i^a
```

Under this change the `1/e` factors of the singular kinetic terms are absorbed
into the field derivatives, and the transformed kinetic operator becomes a
**flat d'Alembertian (wave operator)** in field space:

```
H_transformed = ( 1/16 Δ_{S̃} − 1/24 ∂²/∂y² )  +  H_1  −  Ṽ(ẽ, ∂ẽ)
                └─────── flat hyperbolic H₀ ───────┘
```

The principal part `H₀` is a flat second-order hyperbolic operator; `H_1` is
first-order, and `Ṽ` a (polynomial) potential built from the densitized tetrads
and their first derivatives. The densitized coordinates are special in that the
field-space metric is *flat* there: the kinetic term has constant coefficients
`(1/16, −1/24)`, so the Christoffel symbols and curvature vanish and the
connection ("quantum potential") corrections that a generic point transformation
would produce drop out — the unitary image is exactly `H₀ + H₁ − Ṽ` (see §10.3
for the Jacobian half-density that makes the map unitary).

### 10.2 The ESA theorem: Strichartz

The ESA claim for `H_transformed` rests on **Strichartz's theorem** (R. S.
Strichartz, *Essential self-adjointness of powers of generators of hyperbolic
equations*, J. Funct. Anal. **13** (1973) 82–93): a second-order differential
operator whose principal part is a **flat d'Alembertian on `L²(ℝ^N)`** with a
(smooth, polynomial) potential is essentially self-adjoint, because waves
propagate at finite speed in field space. This is the hyperbolic analogue of
Sears' theorem (Reed & Simon Vol. II, Thm X.28) that Part G of the NS plan uses
for the elliptic case.

### 10.2a A proof outline for the Strichartz ESA (plan item)

This subsection records a *concrete proof outline* a Lean–specialist could
execute, in the project's honesty style. The target is the continuum operator
`H = H₀ + V` on `D = C_c^∞(ℝ^N)`, with `H₀` the flat d'Alembertian (principal
part `diag(1/16, −1/24)`) and `V` a smooth polynomial potential. The theorem to
prove (as a named theorem with citation, **never an axiom**, exactly like
Crouzeix in `ChapterH4`):

```
strichartz_esa
  (H₀ : (C_c^∞(ℝ^N)) →ₗ[ℂ] L²(ℝ^N))   -- the flat d'Alembertian, symmetric on D
  (V : ℝ^N → ℂ) (hV : smooth polynomial)
  : EssentiallySelfAdjointOn C_c^∞(ℝ^N) (H₀ + V)
```

**The proof route — via the deficiency/range machinery already in
`BookProof/ChapterFarisLavine` and `BookProof/ChapterNavierStokesEsa`.** The
project already proves the *abstract* spine of the argument; the Strichartz input
is exactly the one analytic hypothesis that feeds it:

1. **Symmetry on `D`.** `H₀` is formally self-adjoint on `C_c^∞` (integration by
   parts on the flat d'Alembertian), `V` is real-valued, so
   `H = H₀ + V` is symmetric on `D`. This is `SymmetricOn` in
   `ChapterFarisLavine`/`ChapterNavierStokesFullEsa`.
2. **The resolvent/range argument (the part the project already has).** ESA of a
   symmetric operator is equivalent to the two ranges
   `(H − i·1)(D)` and `(H + i·1)(D)` being *dense* — the
   `deficiencyTrivialAt_of_dense_range` / `essentiallySelfAdjointOn_of_farisLavine`
   machinery of `ChapterFarisLavine` (Thm 1: with `N` a positive comparison
   operator, `N+1` onto, and the commutator bound, ESA follows). The remaining
   work is to *verify the two Faris–Lavine hypotheses* for the specific
   `H₀ + V` with comparison operator `N = H₀² + 1` (the book.tex auxiliary-operator
   choice) — or to bypass them via finite-speed propagation.
3. **The Strichartz input: finite-speed propagation.** The genuinely new analytic
   content, and the one thing Mathlib does not yet contain: solutions of the
   hyperbolic equation `(∂_t² − Δ_x)φ = 0` propagate at finite speed, so a
   deficiency vector `w` of `H*` (satisfying `H*w = ±i w`) has *empty* domain of
   dependence: by finite speed it would have to propagate out of any compact set,
   contradicting square-integrability. Formally: for a flat d'Alembertian with a
   smooth polynomial potential, `ker(H* − z) = 0` for `Im z ≠ 0` — a **unique
   continuation / finite-speed** statement. This is the named input, recorded with
   its citation (Strichartz 1973; the hyperbolic analogue of the elliptic
   Kato–Rellich/Sears argument).
4. **Conclusion.** With `ker(H* ± i) = 0` (both deficiency indices `(0,0)`),
   `H` is essentially self-adjoint on `D` — matching the project's
   `EssentiallySelfAdjointOn` predicate and, through
   `hasZeroDeficiencyOn_of_farisLavine` / the deficiency-predicate bridge, the
   `HasZeroDeficiencyOn` form the QG/NS chapters use.

**Honest flag.** Steps 1, 2 and 4 are provable in the existing framework. Step 3
 is the analytic core — *finite-speed propagation / unique continuation for the
 flat d'Alembertian with a polynomial potential* — and it is the part recorded as
 a named hypothesis (with citation), exactly as `ns_esa_of_farisLavine` and
 Crouzeix are named rather than assumed. A specialist who formalizes step 3 (e.g.
 the standard energy-estimate + finite-speed argument for the wave equation, or
 Mathlib's `Laplacian`/`MemElap` machinery extended to the wave operator) would
 turn the whole outline into a proof; until then it is a plan item, not a claimed
 theorem.

**Update (2026-08-18): step 3 is now *half-proved* and its precise residual is
the bounded-below-polynomial case.** `BookProof/ChapterStrichartzWave.lean`
proved the *free* wave operator `□ + κ` is ESA on the Schwartz core (Fourier
multiplier), `ChapterKatoRellichDeficiency.lean` proved bounded perturbations
preserve ESA, and `ChapterWaveBoundedPotential.lean` reached `□ + V` for
*essentially bounded* `V`. The author's claim — **`V` polynomial and bounded
below ⟹ `□ + V` ESA** — is the exact remaining content of step 3: a polynomial
is unbounded (so the bounded-`V` results do not apply) but bounded on every
compact set (so the finite-speed/localized energy argument applies, with
boundedness below the uniform growth control). Plan: (a) truncate `V` to
essentially bounded `V_R` on balls using the proved `exists_smooth_cutoff`;
(b) apply the proved `wave_add_potential_essentiallySelfAdjoint` to `□ + V_R`;
(c) pass ESA to `□ + V` by `R → ∞` via the finite-speed/energy (or form-locality)
argument. See §9 item 5.

### 10.3 Honest boundary (same as the NS-FLOW wave)

- **What is provable now** is the *algebraic* content, mirroring the NS plan:
  the change of variables itself, `y = √e`, `ẽ_i^a = √e·e_i^a`; the identity
  that `1/e = (∂y/∂e)²` absorbs the singular denominator into a field
  derivative; the operator-order decomposition of `H_transformed` (2nd + 1st +
  0th); and the positive/flat character of `H₀`. None of this requires the
  continuum analytic theorem.
- **ESA in the transformed variables transfers to the original variables ONLY
  when the transformation is made unitary — and it can be.** The crucial scope
  point is that the raw point map `e ↦ (y, ẽ)` (a nonlinear diffeomorphism of
  field space) is **not** by itself a Hilbert-space unitary: the pushforward
  `(Uψ)(ẽ,y) = ψ(e(ẽ,y))` changes the norm because `Dẽ = J·De`. The standard
  repair is the **Jacobian half-density (metaplectic / van Vleck) factor**:
  `(Uψ)(ẽ,y) = |J|^{−1/2}·ψ(e(ẽ,y))`, `J = det ∂ẽ/∂e`, which makes `U` a genuine
  unitary on `L²(Dẽ Dy)`. With that factor and the ordering chosen to respect it
  (the naive `(1/16e)S² → (1/16)S̃²` holds only for the consistent ordering; a
  generic point transformation conjugates a flat Laplacian into a Sturm–Liouville
  operator with a "quantum potential" `Q[y] ~ (∇y/y)²`), the transformed
  operator is exactly `H₀ + H₁ − Ṽ` with flat principal part. **Then ESA
  transfers by unitary equivalence**, via the project's own
  `hasZeroDeficiencyOn_of_linearIsometryEquiv` (`ChapterNavierStokesLagrangianEsa`):
  vanishing adjoint deficiency is invariant under a unitary `W`, so ESA of the
  flat `H₀`-dominated operator implies ESA of the physical Hamiltonian. (This is
  the same mechanism as the NS Eulerian ⟷ Lagrangian transfer — that change was
  *already* unitary; the densitized one becomes unitary exactly by including the
  half-density.) Honest caveat: the *gauge/BRST sector* is not covered by this
  argument alone — a full BRST-reduced transfer needs `U` to map the physical
  (gauge-invariant) subspace to itself, which the `1/e`-absorption guarantees
  for the kinetic/conformal part but must be checked for `H₁ − Ṽ` once the full
  constraint structure is imposed.
- **What is recorded, not claimed**: the **Strichartz ESA of the flat
  d'Alembertian** is now *proved* in `BookProof/ChapterStrichartzWave.lean`
  (`wave_essentiallySelfAdjoint`, plus `□ + W` for bounded/truncated `W`), and
  the **bounded-below polynomial potential** `W x = ‖x‖^(2k)` is proved as a
  pure potential (`polynomialPotential_essentiallySelfAdjoint`).  What is *not*
  claimed is the **full-potential** continuum conclusion — ESA of `H₀ + H₁ − Ṽ`
  for the untruncated polynomial `Ṽ` on `L²(ℝ⁸⁴)`.  This is **not** a mere
  `R → ∞` limit: under this project's sign convention (`□ = −∂_t² + Δ_x`) a
  bounded-*below* `W` puts the fibre `−Δ_x − W` in the limit-circle regime where
  ESA **fails** (`−d²/dx² − x⁴` has deficiency `(2,2)`); the localization closes
  only under the opposite sign (module docstring of
  `ChapterWaveUnboundedPotential.lean`).  Whether the QG `Ṽ` lies in the proved
  or the failing regime is the analytic core that decides the boundary (cf.
  step (c) of §9.5; see also `PLAN_LEAN_SPECIALIST_QG_FLOW.md` Part D, updated
  2026-08-19).  The project's ODE chapter's `ẋ = x²` warning applies here too:
  the *singular* `1/e` form shows that the *raw* tetrad operator is not even
  well-defined as an operator on a fixed domain, so the change of variables is
  load-bearing, not cosmetic.
- **Do NOT claim**: ESA of the continuum gravity operator, global existence, or
  any unitary-evolution result as a *proved Lean theorem*. The book's own
  existence/uniqueness claims for gravity are in the same scope-cut class as
  Contention D5 for NS.
- **Suggested next step (a plan item, like the NS waves) — CLOSED (2026-08-17):**
  `PLAN_LEAN_SPECIALIST_QG_FLOW.md` now exists and is executed by
  `BookProof/ChapterQuantumGravityDensitized.lean`.  The original wording of the
  item follows.  A
  `PLAN_LEAN_SPECIALIST_QG_FLOW.md` in the NS-FLOW style — Part A (the
  densitized change of variables `√e`, `√e·e_i^a` and the `1/e = (∂y/∂e)²`
  identity), Part B (the flat d'Alembertian principal part and the operator
  decomposition), Part C (the finite truncation on `Fin N` modes with its
  complete unitary flow), Part D (Strichartz/Sears as a named hypothesis, never
  an axiom, exactly as `ns_esa_of_farisLavine` is named in the NS plan). Reuse
   the `Singularity/ChangeOfVars.lean` reciprocal/logarithmic-map pattern and the
   `DiffeomorphismsGravity` book chapter.
- **Next targets (2026-08-19): the book's full quantum Hilbert space and its
  gauge-fixed 3D operator.**  Parts A–D formalize the *one-particle densitized
  operator's* ESA.  To match the book's own definition (book.tex:8247–8320)
  there remain (a) the second quantization on the graded Fock space
  `Γˢ(L²(ℝ⁸⁴×ℤ₂¹⁹)) ⊗ Γᵃ(L²(ℝ⁸⁴×ℤ₂¹⁹))` with the `ℤ₂`-graded superalgebra and
  the fermionic CAR half — the gravity analogue of
  `BookProof/ChapterFockSecondQuantization.lean`; and (b) the concrete 3D
  gauge-fixed field-space Hamiltonian (densitized, Weyl-ordered, positive
  sum-of-squares) plus the BRST charge `G` with the ghosts on `ℤ₂¹⁹`.  These are
  written up as **Part E and Part F of `PLAN_LEAN_SPECIALIST_QG_FLOW.md`** for
  the Lean-specialist.  The mass gap and global existence remain out of scope by
  the author's decision.

### 10.4 The three-theorem toolbox (record)

The manuscript's analytic-layer conclusions draw on three named theorems, all
recorded in this project's honesty style:

| Theorem | Reference | Use in this manuscript |
| :-- | :-- | :-- |
| Strichartz | Strichartz, J. Funct. Anal. 13 (1973) 82–93 | flat d'Alembertian principal part ⟹ ESA (hyperbolic kinetic term, incl. the gravity `H₀`). **Proved** in `ChapterStrichartzWave.lean` (`wave_essentiallySelfAdjoint`); the full-potential `H₀ + H₁ − Ṽ` step remains a boundary (2026-08-19) |
| Sears / Reed–Simon X.28 | Sears, Canad. J. Math. 3 (1951); Reed & Simon Vol. II Thm X.28 | `−Δ + V` with `V ≥ −c|x|² − d` ⟹ ESA (elliptic/quadratic-growth case, NS Part G) |
| Faris–Lavine | Faris & Lavine, CMP 35 (1974) 39–48, Cor. 1.1 | comparison-operator commutator criterion (proved in `ChapterFarisLavine`, NS Part G) |

None of these is an `axiom` in `BookProof/`; each enters as a named theorem with
a citation docstring when a plan requires it.  Of the three, the Strichartz (flat
d'Alembertian) and Faris–Lavine ESA theorems are now **proved** in-repo; the
Sears/Reed–Simon one is used only as a named route for the NS elliptic case.

### 10.5 The R + αR² (Starobinsky) Hamiltonian: the regularized conformal mode
and its continuous flow (plan item, 2026-08-22)

This is a **new plan item**: formalize the ESA and the continuous unitary flow of
the 3D gauge-fixed Hamiltonian of the **R + αR² (Starobinsky) theory** — the
`f(R)` extension of the Einstein–Hilbert action with `f(R) = (M²/2)R + αR²`,
`α > 0`, `M` the reduced Planck mass — starting from the derivation in the
Cadabra2 module `../unfer/docs/qg_starobinsky_hamiltonian.cdb` (quantized
numerically in `fock_sirk/tests/qg_starobinsky_validation.rs` and
`qg_starobinsky_derivative_variable.rs`).

The point of the αR² term is exactly the **conformal-mode regularization** that
pure GR lacks.  The cdb derives, with every check resolving identically:

* the **ghost-free scalar-tensor equivalence**: `ψ = 1 + 4αR/M²` and
  `f(R) = (M²/2)ψR − U(ψ)` with `U(ψ) = (M⁴/16α)(ψ−1)²` — R² gravity is a
  *second-order* scalar-tensor theory (no Ostrogradsky ghost);
* the **Einstein-frame scalaron potential**, manifestly non-negative (a square):
  `V(φ) = (M⁴/16α)(1 − e^{−√(2/3)φ/M})² ≥ 0`, with `V(0) = 0` (flat Minkowski
  vacuum), the large-field plateau `M⁴/(16α)` and the exponential wall as
  `φ → −∞`;
* the **conformal-mode spatial potential** as the α-stabilized parabola,
  bounded below:
  `V3(R_c) = −(M²/2)R_c + αR_c² = α(R_c − M²/(4α))² − M⁴/(16α) ≥ −M⁴/(16α)`
  (the linear `−(M²/2)R_c` term — whose negative conformal-mode gradient energy
  made pure GR unbounded below — is regularized by the positive `αR_c²`);
* the **3D gauge-fixed Hamiltonian** (synchronous gauge, NS-style fixing of the
  spatial derivative variables, Legendre transform, Hamiltonian constraint
  solved):
  `H = ½π² + ½(∂φ)² + V(φ) + (2/M²)Π² + (M²/8)dqsq − (M²/2)R_c + αR_c²`,
  with the reduced physical form `H_final = ½π² + ½(∂φ)² + V(φ)` on the scalar
  sector.

**Plan item — the formalization (for the Lean 4 specialist):**

1. **The potential bounds (the “correct bound” for ESA).**  Formalize the two
   boundedness statements: `V(φ) ≥ 0` (a square) and `V3(R_c) ≥ −M⁴/(16α)`
   (completion of the square).  One-variable inequalities, small and
   self-contained (`sq_nonneg` + the completed-square identity), verified against
   the cdb's `V3_check`/`Vphi` computations.
2. **The bound after the change to densitized variables.**  Express the
   conformal-mode potential in the densitized fields (the `y = √e` change of
   `ChapterQuantumGravityDensitized`, with the half-density unitary of
   `ChapterQuantumGravityHalfDensity`) and prove the bound survives the unitary
   transfer (`densitized_hasZeroDeficiencyOn_transfer`): the transformed
   potential is bounded below (`V3 ≥ −M⁴/(16α)`), which is the correct sign for
   the elliptic scalaron sector and for every relative-bound / commutator-form
   combination of kinetic and potential — exactly what pure GR lacks (§10.3: the
   `−d²/dx² − x⁴` limit-circle record).  (Where the hyperbolic convention
   applies the opposite bound is the Faris–Lavine sign; the mode-level /
   maximal-domain statements of step 3 avoid the sign question entirely.)
3. **ESA of the full Hamiltonian.**  The scalaron sector is the *elliptic* case
   `½π² + ½(∂φ)² + V(φ)` with `V ≥ 0` bounded below (the correct sign for this
   convention — cf. the elliptic Kato–Rellich / Sears route,
   `ChapterHermiteRelativeBound`, `ChapterKatoRellichRelative`); the conformal
   mode is the *hyperbolic* case with the stabilized parabola.  **The potential
   may be a high-degree polynomial in the fields and their spatial
   derivatives — this is not an obstruction:** the proved machinery already
   covers arbitrary temperate polynomials as multiplication operators
   (`ChapterWaveUnboundedPotential.potentialOp_essentiallySelfAdjoint`, with
   **no** boundedness and **no** semiboundedness hypothesis;
   `polynomialPotential_essentiallySelfAdjoint` for `W x = ‖x‖^(2k)`), and in
   the densitized variables the fiber operator is multiplication by the mode
   symbol `(1/16)a_k² − (1/24)b_k² + V_k` with *any* potential `V_k`, for which
   `qgModeHamiltonian_essentiallySelfAdjoint` proves ESA on the maximal domain
   with deficiency trivial at **every** non-real `z` — no sign condition at the
   mode level (`qg3D_essentiallySelfAdjoint_on_hermiteCore` is the 3D instance).
   What the bound controls is only the *combination* of kinetic and potential
   (the relative-bound / commutator-form step, and the continuum fibre gluing),
   and there the R² potential has the correct one.  The honest residual is the
   same as §10.2a/10.3: the *continuum* `L²(ℝ⁸⁴)` statement with the full
   polynomial `Ṽ` still needs the Strichartz finite-speed / unique-continuation
   input (`strichartz_esa_of_finiteSpeed`; `wave_add_potentialOp_symmetric` is
   proved but the general unbounded `□ + W` ESA is not claimed — the step-(c)
   sign record) — but that residual is the *gluing*, not the polynomial degree.
4. **The continuous flow.**  Feed the achieved ESA into the Stone bridge
   (`ChapterStoneResolvent`–`ChapterStoneSeparable` + `ChapterStoneBridge` /
   `ChapterStoneFlows`): produce **`qgR2_stone_flow`** — the complete unitary
   group `e^{−itH}` solving the Schrödinger equation on the domain, the QG
   analogue of `ns_stone_flow` / `ym_fock_stone_flow` and the first continuous
   flow for the gauge-fixed gravity Hamiltonian; on the Hermite/scalaron
   eigenbasis `ChapterStoneEigenflow` makes it explicit
   (`U t ψ_α = e^{−iE_αt} ψ_α`).

**Honest boundaries.**  The cdb file is a symbolic computation; this item
formalizes the mathematics it states (the equivalence, the bounds, the Legendre
transform), not the Cadabra2 program.  The gauge/BRST sector and the full
continuum statement remain as recorded in §10.3: the continuum `L²(ℝ⁸⁴)`
conclusion still needs the Strichartz finite-speed input, and the *high degree*
of the R² potential (quartic in the densitized fields and their spatial
derivatives) is **not** what stands in the way — the mode-level and
multiplication-level theorems above are proved for arbitrary temperate
polynomials.  No mass gap and no globalexistence are claimed.  **Natural first sub-target:** the pure one-variable
scalaron Hamiltonian `−Δ + V(φ)` with the Starobinsky potential.  It has the
correct semi-bound — `V ≥ 0` (a square, global minimum at `φ = 0`), the
strongest form of the correct sign for the elliptic case (Sears / Faris–Lavine:
`V ≥ −c‖x‖² − d` suffices) — and the **exponential wall is not an obstruction**:
the wall is *upper* growth, and ESA of the elliptic sum needs only the lower
bound plus local regularity of `V`.  (The wall does disqualify the
*temperate-growth* multiplication-operator theorem
`potentialOp_essentiallySelfAdjoint`, but that theorem concerns the potential
alone and is not needed here.)  Route: the proved Faris–Lavine criterion of
`ChapterFarisLavine` with the concrete relative-bound / commutator-form estimates
for this `V`, or the Sears argument as the named alternative; the flow isthe scalar mode of `qgR2_stone_flow`.

### 10.6 What is missing for QG: the one-particle ESA on the Hermite
(Gauss–polynomial) core, and the remaining QG gaps

#### 10.6.1 The missing statement (the focus of this subsection)

**The one-particle continuum ESA of the full gauge-fixed `R + αR²` Hamiltonian
on the dense Hermite (Gauss–polynomial) core is not proved.**  What exists is
modal: the *mode-level* operator — multiplication by the full symbol
`(1/16)a_k² − (1/24)b_k² + V₃(R_c k) + V(φ_k)` on the maximal domain of `ℓ²(ℕ)` —
is ESA unconditionally (`qgR2Mode_esa`, `qgScalaronMode_esa`, both with Stone
flows), and the *continuum* combination of kinetic + scalaron potential on the
compactly-supported smooth core is ESA only **conditionally** on the Strichartz
finite-speed / unique-continuation hypothesis
(`wave_add_scalaron_esa_of_finiteSpeed` — the premise is a hypothesis, never an
axiom, and nothing asserts it for the continuum operator).  The Fock statement
(`qgScalaronFock_esa`) is potential-only; its honest boundary states the kinetic
is not part of it.  There is **no** continuum one-particle statement on the
Gauss–polynomial core — the basis in which the SIRK numerics actually work.

**Why the Hermite core is the right domain for this potential.**  The scalaron
potential is *only* exponential: as `φ → −∞`, `V(φ) = (M⁴/16α)(1 −
e^{−√(2/3)φ/M})²` grows like `e^{c|φ|}`, `c = 2√(2/3)/M` (and is bounded, even a
square, elsewhere; the conformal-mode part `V₃` is a parabola).  The
Gauss–polynomial core — `p(x)e^{−‖x‖²/4}` for polynomials `p` — has a Gaussian
tail that **dominates every exponential**: for all `c > 0`,
`e^{c‖x‖}e^{−‖x‖²/4} → 0` as `‖x‖ → ∞`.  Hence:
* the Hamiltonian is **well defined on the core**: for every Gauss polynomial
  `ψ`, `V·ψ ∈ L²` (smooth `V`, Gaussian tail), and `Hψ` lands in `L²` — the
  domain question that §10.3 flags for the raw operator is answered explicitly
  in this basis;
* the potential is a **small (relatively bounded) perturbation** of the kinetic
  part on this core, so the Kato–Rellich / Faris–Lavine machinery
  (`ChapterHermiteRelativeBound`, `ChapterFarisLavine`) applies with the
  semi-bound `V ≥ −M⁴/(16α)` — the correct sign for the elliptic scalaron
  sector, exactly the §10.5 sub-target's route, but now on the basis-adapted
  domain instead of the abstract one.

The exponential wall disqualifies the *temperate-growth* multiplication
operator theorem (`ChapterWaveUnboundedPotential.potentialOp_essentiallySelfAdjoint`,
as recorded in §10.5) — that is precisely why the basis route is the natural one
for this potential.

**What to prove (named targets for the Lean 4 specialist):**
1. **Well-definedness on the core.**  For the Gauss–polynomial core of `L²(ℝ)`
   (one variable, the scalaron) and of `L²(ℝ²)` (the reduced sector `(R_c, φ)`):
   `starobinskyV` and the full potential `V₃ + V(φ)` are in `L²` against every
   core element — the Gaussian-tail dominance as a formal inequality
   (`∀ c > 0, ∃ C, ∀ x, e^{c|x|} ≤ C e^{‖x‖²/8}` style), giving
   `memLp`/`ContDiff` statements that `H` maps the core into `L²`.
2. **The relative bound.**  Extend `ChapterHermiteRelativeBound` (currently
   linear/quadratic perturbations with arbitrarily small relative bound) to the
   exponential potential: `V(φ)` is `(−Δ)`-bounded with arbitrarily small
   relative bound on the Gauss core (the Gaussian tail makes `‖Vψ‖` small
   against `‖(−Δ)ψ‖` outside a large ball), and the same for the full
   potential with the conformal-mode parabola.  This is the genuinely new
   mathematics: the existing relative-bound theorems cover polynomials, not
   exponentials.
3. **The flux (Carleman) extension (alternative route).**  The flux criteria
   (`ChapterHermiteCarlemanEsa`, `ChapterCarlemanTwoStep`,
   `ChapterCarlemanGeneralHop`) control *finite-hop* (polynomial) potentials on
   the Hermite lattice; the exponential potential has unbounded hops (the
   Hermite recursion of `e^{c x}` has unbounded support).  A new flux statement
   — or the weighted-space bound of target 2 — is required for the exponential
   case; both are the same content in two languages.
4. **The closing ESA.**  `−Δ + V(φ)` (the §10.5 first sub-target) and, on the
   reduced two-variable sector, the full one-particle gauge-fixed operator with
   both potentials, ESA on the Gauss–polynomial core, **unconditional** — no
   finite-speed hypothesis — plus the Stone flow, as the continuum counterpart
   of `qgScalaronMode_esa` (`qgOneParticleHermite_esa`,
   `qgOneParticleHermite_stone_flow`).

**Relation to the open boundaries.**  This does **not** close the hyperbolic
side: the *differential realization* of the conformal-mode kinetic
`(1/16)Δ_S̃ − (1/24)∂²_y` on the Gauss core of `L²(ℝ⁸⁴)` is the same Strichartz /
direct-integral residue as A1 / A5-step-2, and the §12 reliability chain
(finite-`m` flow error, restarts, whitening) applies to whichever one-particle
domain is fixed here.  What it does is: (i) remove the finite-speed hypothesis
for the **elliptic scalaron sector**; (ii) give an explicit dense domain on which
the full operator is well defined (the Gauss–polynomial core — the basis the
numerics use); and (iii) provide the natural Hilbert-space setting for the §12
instantiation of the SIRK reliability theorem for QG.

#### 10.6.2 The remaining QG gaps (recap, cross-referenced)

1. **The full-potential continuum conclusion** `H₀ + H₁ − Ṽ` on `L²(ℝ⁸⁴)` for
the untruncated polynomial `Ṽ` — the Strichartz finite-speed / direct-integral
residue (§10.3, §10.5 step 3, A1).  The §10.6.1 Hermite-core route is the
*basis* alternative to this *gluing* route; both remain open.
2. **The one-particle Hermite-core ESA** of §10.6.1 — the new item above.
3. **The second quantization** on the graded Fock space
`Γˢ(L²(ℝ⁸⁴×ℤ₂¹⁹)) ⊗ Γᵃ(L²(ℝ⁸⁴×ℤ₂¹⁹))` with the `ℤ₂`-graded superalgebra and the
fermionic CAR half — the gravity analogue of `ChapterFockSecondQuantization`
(Part E of `PLAN_LEAN_SPECIALIST_QG_FLOW.md`; the scalaron Fock statement of
`ChapterScalaronFockEsa` is the bosonic, potential-only seed).
4. **The concrete 3D gauge-fixed field-space Hamiltonian** (densitized,
Weyl-ordered, positive sum of squares) **plus the BRST charge** `G` with the
ghosts on `ℤ₂¹⁹` (Part F), and the **BRST-reduced transfer** of the half-density
unitary `U` (it must map the physical subspace to itself — §10.3's caveat).
5. **Out of scope, unchanged:** the mass gap and global existence.

#### 10.6.3 Attack order and definition of done

Attack the one-variable scalaron first (`−Δ + V(φ)` on the Gauss core of
`L²(ℝ)`, targets 1→2→4), then the reduced two-variable sector `(R_c, φ)`, then
(reuse for the QG bullet of §12.2 Gap 2) the finite-`m` SIRK reliability
instance on that core.  Done = the named `qgOneParticleHermite_esa` /
`_stone_flow` theorems with every hypothesis discharged (no axiom, no
finite-speed premise), the §8 gate green, and the §12.2 Gap-2 QG bullet updated
to reference the Hermite-core domain.

---

## 11. Quantum Yang–Mills: Friedrichs extension of the 3D gauge-fixed Hamiltonian
(candidate route, record — not a proved Lean theorem)

The manuscript's 3D gauge-fixed Quantum Yang–Mills Hamiltonian
(`book.tex` §"Quantization due to time-evolution: Yang-Mills and Classical
Statistical Field Theory", ~7037–7120, on
`Γ^s(L²(ℝ⁹⁹×ℤ₂³¹)) ⊗ Γ^a(L²(ℝ⁹⁹×ℤ₂³¹))`, the `ℝ⁹⁹` = 3 coordinates + 24 SU(3)
gauge fields `A_{k,a}` + their derivatives, `ℤ₂³¹` the 8 ghosts + derivatives
minus one) is, in the Weyl gauge and **in the Hermite (oscillator) basis**,

```
H(x) = −½ πⁱ_a πⁱ_a − ½ B_{i a} B_{i a}
```

with the BRST charge `Ω = ∫ π^k_a ∂_k ψ†_a − π^k_a f_abc A_{k b} ψ†_c
− (i/2) f_abc ψ†_a ψ†_b ψ_c`. The sign is the convention of the classical
action; up to that sign the Weyl-gauge Hamiltonian is a **sum of squares of the
self-adjoint electric- and magnetic-field operators** (`½Σ(πⁱ_a)² + ½Σ(B_{i a})²`),
i.e. **positive (bounded below by 0)** — already formalized as
`weylHamiltonian_isPositive` in `BookProof/ChapterWeylHamiltonian.lean`.

### 11.1 The theorem: Friedrichs extension

Because `H` is **symmetric and bounded below** (semi-bounded), the classical
**Friedrichs extension theorem** applies: a densely defined, symmetric,
semi-bounded operator on a Hilbert space admits a canonical self-adjoint
extension — the *Friedrichs extension* — obtained by closing its quadratic form
and taking the operator of the closure. Key properties:

- it is the self-adjoint extension whose domain is contained in the form domain
  of the closure, and it is the *largest* (in the sense of the partial order on
  extensions) self-adjoint extension;
- it is **canonical**: it depends only on the operator (and its lower bound), not
  on any choice of auxiliary data — which is exactly the uniqueness the
  Hashimoto-limit claim below needs;
- for a *positive* operator (`H ≥ 0`, the Weyl-gauge case) the Friedrichs
  extension is `√(H*)√(H)`-based and its quadratic form is the closure of the
  original form.

Reference: M. Reed & B. Simon, *Methods of Modern Mathematical Physics, Vol. I*,
Thm X.23 (the Friedrichs extension); K. Friedrichs, *Spektraltheorie
halb-beschränkter Operatoren*, Math. Ann. **109** (1934) 465–487.

### 11.2 The uniqueness claim: the infinite Hashimoto limit selects it

The project's Hashimoto–SIRK machinery (`PLAN_LEAN_SPECIALIST_SIRK_NESTED.md`,
`BookProof/ChapterH8`/`ChapterH9`) builds the order-`n` Krylov approximations
`Bₙ = Vₙ* X Vₙ` whose *spectral side nests*:
`W(Bₘ) ⊆ W(Bₙ) ⊆ W(X)` for `m ≤ n` (`sirk_numRange_nested_orders`), the Ritz
spectra nest, and the best-approximation error is antitone in the order
(`krylov_bestApprox_antitone`), tending to `0` for a cyclic seed
(`krylov_bestApprox_tendsto_zero`). The uniqueness claim to record is:

> **The infinite limit of the Hashimoto algorithm selects the Friedrichs
> extension** — the self-adjoint extension recovered as the order-`n` Krylov
> approximations refine is the canonical one, i.e. the Friedrichs extension of
> §11.1, because the Friedrichs extension is the only self-adjoint extension
> that is *determined by the quadratic form alone* (no boundary condition at
> infinity is imposed beyond the form domain), and the nested-orders
> convergence of the approximants is form-domain-preserving.

### 11.3 Honest boundary

- **What is provable now** (mirroring the NS-FLOW and QG waves): the
  *algebraic* content — the Weyl-gauge Hamiltonian is a sum of squares
  (`weylHamiltonian_isPositive`, already proved); the Hermite-basis (oscillator)
  realization of the fiber, where the comparison/number operator is diagonal and
  the electric/magnetic fields are concrete shifts; the form
  `q(x) = ½Σ‖πⁱ_a x‖² + ½Σ‖B_{i a} x‖²` and its positivity; the BRST charge
  `Ω` and its nilpotency (`nsBrst_nilpotent`-style, via `ChapterGhostField`).
  None of this requires the continuum analytic theorem.
- **What is recorded, not claimed**: the **Friedrichs extension** for the
  continuum `L²(ℝ⁹⁹)` operator, and the **uniqueness by the infinite Hashimoto
  limit**, are named theorems / named claims (Friedrichs 1934, Reed–Simon
  X.23), in the same honesty class as Strichartz (§10) and the NS continuum FL
  inequalities. The Hasimoto-limit-uniqueness sentence in §11.2 is a *conjecture
  to be proved* (a research item), not a proved statement: the current SIRK
  results give nesting, monotone approximation error and (for cyclic seeds)
  tend-to-zero, but the identification of the *limit operator* with the
  Friedrichs extension is not yet formalized.
- **Refinement (2026-08-18): the continuum operator is well-defined on the
  Hermite core, so the remaining boundary is a construction task, not a gap.**
  The base `ℝ⁹⁹` is finite-dimensional (3 + 24 + 72 coordinates, book.tex:
  7045-7048), `H₁ = ½Σππ + ½ΣBB` is a finite-degree polynomial-coefficient
  differential operator, and `A`, `∂` act on the product Hermite basis as ladder
  operators — so `H₁` is well-defined and symmetric on the Hermite core (same
  pattern as `harmonicOscOp_apply_eq_differential` in 1D).  What is not yet
  built is the *Lean construction* of that operator on the product Hermite core
  of `L²(ℝ⁹⁹)`, plus the proofs of core-invariance/symmetry/positivity; the two
  delicate points are the Weyl ordering of the non-commuting `πA` cross-terms in
  `B²` and the sign reconciliation of book.tex:7077 with the positive
  sum-of-squares form.  See the closing update of §11.4.  **(2026-08-18: this
  construction task is now executed — `BookProof/ChapterHermiteProductCore.lean`
  and `BookProof/ChapterYangMillsHermite.lean`; both caveats are settled inside
  the modules.)**  **(2026-08-19: the remaining Part F.11 row — the *second
  quantization* of that one-particle Hamiltonian on the finite-occupation states
  over the core — is executed too, in
  `BookProof/ChapterFockSecondQuantization.lean`: the occupation-number Fock
  space `ℓ²(ℕ →₀ ℕ)`, the ladder operators with `[a_j, a_j†] = 1`,
  `dΓ(A) = Σ ⟪e_j, A e_k⟫ a_j† a_k`, its symmetry, positivity and Friedrichs
  extension, ending in `ym_fock_friedrichs_extension`, together with the
  Hashimoto/SIRK selection of that extension (`ym_fock_hashimoto_selects`).
  Still **not** claimed:
  the mass gap or global existence.)**
- **Do NOT claim**: self-adjointness of the continuum QYM operator, the mass
  gap, or global existence as *proved Lean theorems*. The Yang–Mills existence
  and mass-gap Millennium problem is deliberately out of scope (the book's own
  "if the Hamiltonian is positive-definite then ... with or without a mass gap"
  is a conditional, not a claim).
- **Suggested next step (a plan item) — CLOSED (2026-08-17):**
  `PLAN_LEAN_SPECIALIST_QYM_FLOW.md` now exists and is executed by
  `BookProof/ChapterYangMillsFriedrichs.lean` (Part D.4, the identification of the
  Hashimoto limit with the Friedrichs extension, is deliberately left as a recorded
  conjecture).  The original wording of the item follows.  A
  `PLAN_LEAN_SPECIALIST_QYM_FLOW.md`
  in the NS-FLOW style — Part A (the Hermite-basis fiber: `πⁱ_a`, `B_{i a}` as
  concrete oscillator shifts, `H` a sum of squares, `Ω` nilpotent), Part B (the
  quadratic form and its closure), Part C (the Friedrichs extension as a named
  theorem — never an axiom), Part D (the Hashimoto-limit identification: state
  `sirk_limit_eq_friedrichs` as the research conjecture, with the proved
  `sirk_numRange_nested_orders`/`krylov_bestApprox_tendsto_zero` as the
  supporting nesting facts). Reuse `ChapterWeylHamiltonian`,
  `ChapterGhostField`, `ChapterSuperBracket` and `ChapterH8`/`ChapterH9`.

### 11.4 The unbounded continuum case: precise status and the two plan items
(record, 2026-08-17)

The executed wave proves **more** than §11.3's "What is recorded, not claimed"
records, and it is worth being precise about what is and is not in hand, so a
future specialist knows exactly what to attack.

**What the unbounded case already has (proved, no boundedness):**
`hashimoto_shiftInvert_selects_friedrichs`
(`BookProof/ChapterHashimotoShiftInvert.lean`) reaches *unbounded* Hamiltonians:
for any positive self-adjoint extension `A` of an unbounded symmetric positive
`H`, the shift-inverted operator `R = (A + γ)⁻¹` exists, is **bounded**
(`‖R‖ ≤ 1/γ`), and the whole bounded Galerkin theory applies to `R` — strong
convergence of the truncations, strong resolvent convergence at every non-real
`z`, and `R` uniquely determines `A`. So the *convergence/selection* half is
done for unbounded operators, with no boundedness hypothesis anywhere.

**The two things that prevent a full claim (both plan-sized, not research):**

1. **The extension `A` is input, not constructed.** The headline takes
   `A : Dom →ₗ[ℂ] F` with `hA : IsPositiveSelfAdjointExtension H A` as a
   *hypothesis*: it proves the algorithm converges to whichever extension it is
   given (and that the limit is unique). It does **not** prove that the unbounded
   `H` *has* such an extension — that existence is the Friedrichs theorem, which
   for unbounded operators is still the named hypothesis
   `friedrichs_extension_of_semibounded`, discharged by construction only in the
   bounded regime (`friedrichs_of_bounded`). **Plan item:** prove the existence
   of the positive self-adjoint extension for the specific Weyl-gauge operator —
   an analytic form-closure theorem (the domain of the closed form of
   `½Σ‖πⁱx‖² + ½Σ‖Bₐx‖²` on the actual domain, i.e. the unbounded analogue of
   `weylForm_closable` feeding `friedrichs_of_bounded` without the boundedness
   hypothesis). This is the same kind of content as the QG finite-speed step:
   a genuine but bounded task, recorded in the honesty framework as a plan item.
2. **The continuum realization is a definitional choice, not a gap.** The
    theorems live on an abstract Hilbert space `F` with a `HilbertBasis ℕ ℂ F`,
    and the concrete models are `ℓ²(ℕ,ℂ)` (occupation/Hermite-basis
    representations); the field-space differential realization on
    `L²(ℝ⁹⁹×ℤ₂³¹)` with the magnetic-field operator
    `B_{i a} = ε_{ijk}(∂_j A_{k,a} + f_{abc}A_{j,b}A_{k,c})` is not built. **Two
    defensible choices:** either (a) accept the occupation-number/Hermite
    realization as *the* definition of the quantum theory (then `ℓ²(ℕ,ℂ)` *is*
    the continuum in the Fock sense, and only item 1 remains), or (b) realize
    `B_{i a}` concretely as a field-space differential operator (needing
    Mathlib's Sobolev/differential-operator machinery, the same boundary as the
    NS and QG continuum). **Plan item:** state the choice in
    `PLAN_LEAN_SPECIALIST_QYM_FLOW.md`; if (b), add the concrete realization as a
    Part-E-style item.

With items 1 and 2 settled, the full claim — *the unbounded continuum Weyl-gauge
Hamiltonian has a Friedrichs extension, and the infinite Hashimoto/SIRK limit
selects exactly it* — becomes a theorem of the proved machinery. The mass gap is
out of scope by the author's decision.

**Update (2026-08-18): both items are CLOSED; the claim above is now a proved
theorem.** `BookProof/ChapterFriedrichsExtension.lean` proves the Friedrichs
extension theorem itself with no boundedness hypothesis —
`friedrichs_extension_exists` (form inner product → `FormDom`/`FormSpace`
completion → `formExt_injective`, the closability step → Riesz representation
`friedrichsResolvent` = `(H+1)⁻¹` → `A = S⁻¹ − 1` through the module's own
`invShiftOperator`) — so item 1 is discharged in full generality, not just for
the Weyl operator (`weyl_friedrichs_extension_unconditional`), and
`friedrichs_hypothesis_holds` retires the named hypothesis. Item 2 is decided in
favour of **(a)**, the occupation-number/Hermite realization, recorded as Part E
of `PLAN_LEAN_SPECIALIST_QYM_FLOW.md`; the field-space differential realization
(b) is not built and stays the recorded boundary shared with the NS and QG
threads. The combined unbounded statement is `friedrichs_hashimoto_selects` and
`weyl_hashimoto_selects_friedrichs`, and `unbounded_friedrichs_example` exhibits
it on the genuinely unbounded `A eₙ = n eₙ` on `ℓ²(ℕ, ℂ)`.

**Update (2026-08-18, the Hermite-core well-definedness refinement):** the
conclusion of the previous update is *not* that the field-space realization (b)
is out of reach — it is well-defined on the Hermite core, which turns the
remaining boundary into a concrete construction task rather than a research gap.
The book's base is **finite-dimensional**: `ℝ⁹⁹` = 3 coordinates + 24 gauge
fields `A_{k,a}` + 72 derivatives `∂_j A_{k,a}` (book.tex:7045-7048), so
`L²(ℝ⁹⁹)` carries the explicit product Hermite basis built from the 1D
`hermiteBasis` of `BookProof/ChapterHermiteFunctions.lean` (dense, via
`hermiteCore_dense`).  The one-particle Hamiltonian
`H₁ = ½Σπⁱ_aπⁱ_a + ½ΣB_{i a}B_{i a}` with
`B_{i a} = ε_{ijk}(∂_j A_{k,a} + f_{abc}A_{j,b}A_{k,c})` is a **finite-degree
polynomial-coefficient differential operator**: coordinate multiplication by
`A_{k,a}` and the derivative `∂_j` act on Hermite functions as ladder operators,
so `H₁` maps each Hermite basis vector to a *finite* Hermite combination — hence
it is well-defined and symmetric on the Hermite core, and the second-quantized
`H` is well-defined on the finite-occupation states over it.  This is the same
pattern the repo already proves in 1D:
`harmonicOscOp_apply_eq_differential` identifies the diagonal operator `n + ½`
with the differential expression `x ↦ -ψₙ''(x) + (x²/4)ψₙ(x)` on the Hermite
basis (`BookProof/ChapterHarmonicOscillatorEsa.lean`).  So option (b) is a
well-scoped **construction task**: build the product Hermite core of `L²(ℝ⁹⁹)`,
define `A`, `π = −iδ/δA`, `B` on it, prove core-invariance, symmetry and
positivity of `H₁`, then feed the proved `friedrichs_extension_exists` +
`friedrichs_hashimoto_selects`.  Two genuine caveats to settle before executing:
  - **ordering:** the `πA` cross-terms inside `B²` do not commute
    (`[A_{j,a}, π^k_b] = iδ^k_j δ_{ab}`, book.tex:7060-7061) — the product needs
    Weyl ordering (`½(πA + Aπ)`), the *same* subtlety as the NS Hamiltonian
    `H_N = Σ(π_i A_i + A_i π_i)` and the E.5 BRST charge of
    `PLAN_LEAN_SPECIALIST_NS_FLOW.md`;
  - **sign:** book.tex:7077 writes `H(x) = −½ππ − ½BB`, while the plan and the
    formalized theorems use the positive sum-of-squares `H = ½Σπ² + ½ΣB²`
    (bounded below by 0, the Friedrichs hypothesis) — the book's literal sign
    must be reconciled before the operator is fed to the machinery (same style
    of sign correction already recorded for `□` in §9.5).

**Update (2026-08-18, the field-space realization (b) is EXECUTED).**  The
construction task above is done, `sorry`-free and `axiom`-free, in two new
modules.  `BookProof/ChapterHermiteProductCore.lean` builds the Gauss–polynomial
(product Hermite) core of `L²(ℝᵈ)`: `pgMap : ℂ[X₀,…,X_{d−1}] →ₗ[ℂ] L²(ℝᵈ)`,
`p ↦ p·e^{-‖x‖²/4}`, is injective (`pgMap_injective`), its range
`polyGaussCore` is dense (`polyGaussCore_dense`, by the `d`-dimensional
Fourier/moment argument), Gaussian integration by parts holds
(`gaussInt_pderiv`), and Gram–Schmidt on the enumerated monomials gives an
orthonormal basis `coreBasis` whose finite-mode domain *is* the core
(`span_range_coreBasis`).  `BookProof/ChapterYangMillsHermite.lean` defines the
operators at the polynomial level and transports them through the injection
(`CoreRep`): multiplication by a coordinate (`mulOp`, symmetric for real
coefficients), the momentum `π_j = −i ∂_j` (`momOp`, symmetric by
`gaussInt_pderiv`), the magnetic field
`B_{ia} = ε_{ijk}(∂_j A_{k,a} + f_{abc}A_{j,b}A_{k,c})` as multiplication by the
real polynomial `magPoly` over the `99 = 3 + 24 + 72` coordinates, the Weyl
ordering `weylProd` with `weylProd_polySym`, and the commutation relation
`commutator_coord_mom` (`[A_j, π_j] = i`) that forces it.  The Hamiltonian
`ymHamiltonian = ½Σπ² + ½ΣB²` — the positive sign, the caveat above settled — is
symmetric (`ymHamiltonian_symmetricOn`) with sum-of-squares quadratic form
(`ymHamiltonian_quadForm`, `ymHamiltonian_quadForm_nonneg`), so
`ym_hermite_friedrichs_extension` instantiates `friedrichs_extension_exists` and
`ym_hermite_hashimoto_selects` instantiates
`weyl_hashimoto_selects_friedrichs`.  Nothing about the mass gap or global
existence is claimed.
  With ordering and sign fixed, this Hermite-core construction is the remaining
  link between the abstract theorem and the book's operator.  The mass gap stays
  out of scope by the author's decision.

## 12. The full reliability of the SIRK/Hashimoto numerics: the end-to-end
flow-approximation theorem (all systems, incl. NS in Lagrangian variables)

This section collects what is still missing for a **complete formalization of the
reliability of the SIRK/Hashimoto numerical approximations**: a chain of formal
theorems, instantiated for every physics system (NS Eulerian, NS Lagrangian, QG,
QYM), that bounds the distance between what the inverse-free rational-Krylov
algorithm computes at finite Krylov dimension `m` and the *continuous* unitary
flow `e^{−itH}` of the **selected** self-adjoint extension.  The selection side of
the chain is closed for every system; the approximation side is not.

### 12.1 What is already formalized (the pieces)

The chain has four stages; each stage has formal content, but the stages are not
assembled and the per-system constants are not instantiated.

* **Stage 0 — the algorithm (generic).**  The φ-function/resolvent calculus
  (`ChapterH1`), the Arnoldi/Krylov Hessenberg compression (`ChapterH2`), the
  inversion-free forward-sequence shortcut — `wₖ = (H̄ − γI)wₖ₋₁` spans exactly
  the standard Krylov subspace (`ChapterH5.krylov_no_inversion_eq_standard`,
  `krylov_subspace_span`, `shift_pow_sub_pow_mem`), the exponential-decay error
  bound (`ChapterH4.sirk_error_bound_decay`, `ChapterH6.sirk_error_decay_exponential`),
  the Hermitian reduced generator with spectrum contained in the numerical range
  (`ChapterH7`), and the nesting of orders and numerical ranges
  (`ChapterH8`, `ChapterH9`, `ChapterH8Bases`).
* **Stage 1 — the shift-invert selection (generic).**  The bounded resolvent
  `R = (A + γ)⁻¹`, `‖R‖ ≤ 1/γ` by positivity (`ChapterHashimotoShiftInvert`),
  and the non-real-shift bound `‖(γ − A)x‖ ≥ |Im γ|‖x‖` with no positivity
  (`ChapterHashimotoComplexShifts`); Galerkin/Rayleigh–Ritz strong-resolvent
  convergence to the Friedrichs extension (`ChapterHermiteGalerkinFriedrichs`);
  the multi-shift selection `hashimoto_multishift_selects_friedrichs` / `_esa`.
* **Stage 2 — the per-system selection theorems.**  NS Eulerian sequence space
  (`ns_hashimoto_selects`), NS Eulerian differential
  (`nsDiffH_hashimoto_selects`, `nsDiffH_shiftInvert_selects`), **NS Lagrangian**
  (`lagrangian_hashimoto_selects`, `lagrangian_shiftInvert_selects`, the
  concrete `diagKR_hashimoto_selects` — the Kato–Rellich/positive-part route),
  QYM (`ym_hermite_hashimoto_selects` — the Friedrichs route), and QG (the
  Galerkin strong-resolvent convergence over the Strichartz/scalaron ESA — no
  positivity, so no Friedrichs label).
* **Stage 3 — the continuous flows.**  `ns_stone_flow`, `lagrangian_stone_flow`,
  `diagKR_stone_flow`, `ym_fock_stone_flow`, `qgR2_stone_flow`,
  `qgScalaronFock_stone_flow` (via `ChapterStoneBridge` / `ChapterStoneFlows`;
  the explicit eigenbasis form in `ChapterStoneEigenflow`).

### 12.2 What is missing (the gaps, in priority order)

**Gap 1 — the end-to-end reliability theorem (the assembly).**  There is no
single formal statement connecting the four stages:

```
‖e^{−itH} v − V_m e^{−itB_m} V_m∗ v‖ ≤ bound(m, shifts, t, spectral geometry)
```

The ingredients exist as separate modules — the φ-function calculus of `ChapterH1`
/`ChapterH4` (the unitary-group case `φ_k(A)` with the resolvent definition),
`ChapterH4.sirk_error_bound_decay` (conditional on the compression transfer `hrt`
and the two closeness hypotheses `hcx1`, `hcx2`), and the per-system selection
theorems — but no theorem *composes* them into a flow-approximation statement for
a concrete Hamiltonian.  The H4 bound is conditional exactly where the work is:
`hrt` (the reduced generator is the compression `V∗XV` of the *selected*
extension), `hcx1`/`hcx2` (the rational approximant is `ε`-close to the resolvent
and to its reduction), and the decay `D ≤ e^{−hm}·Dmin`.

**Gap 2 — the finite-`m` quantitative bounds per system.**  Instantiate the
constants `C`, `Dmin`, `h` and the shift set `{z_j}` for each Hamiltonian, from
the actual spectral geometry:
* **QYM** (positive sum of squares `½Σπ² + ½ΣB²`, quartic `B(A)²`): the
  Friedrichs route gives the resolvent geometry; missing the explicit constants
  and the statement that the Ritz/gap values converge to the spectrum of the
  Friedrichs extension as `m → ∞` (the numerics' mass-gap Ritz value `≈ g²/2`).
* **NS Lagrangian** (positive parabolic part `½ΣPᵢ² + νΣQᵢ²` + drift): the
  ν-dependent constants; the diffusive decay statement (the laminar `νk²` decay
  rate the numerics measure); the transfer of the selection to the canonical
  non-commuting realization (`ChapterNavierStokesLagrangianCanonical` — its
  Hermite-basis `Pᵢ, Qᵢ` lack a `hashimoto_selects` companion or a transfer
  theorem), and the Fock-of-Fock lifting
  (`ChapterNavierStokesFockLagrangian`) selection/flow.
* **NS Eulerian** (indefinite — strain, vorticity, constant hoppings of arbitrary
  sign): the complex-shift route (`ChapterHashimotoComplexShifts` bounds exist;
  the *decay-rate* version at non-real shifts is not instantiated); the flow
  bound on the Hermite core of `L²(ℝ³)` (differential) and on `ℓ²(Vel)`
  (sequence space).
* **QG** (hyperbolic two-signed fiber symbol `(1/16)a_k² − (1/24)b_k² + V_k`):
  the resolvent geometry of the indefinite operator (the numerics' sensitivity of
  the Hermiticity tolerance for the two-signed case); the scalaron Fock case
  (semibounded below by `−nM⁴/(16α)` — a Friedrichs-type route per sector may
  apply, `qgManyPotential_ge`); **the one-particle Hermite-core ESA of §10.6.1**
  — the Gauss–polynomial core is the domain the finite-`m` bound must be stated
  on (the potential is only exponential, the Gaussian tail dominates it, so the
  operator is well defined in this basis); the continuum `L²(ℝ⁸⁴)` residue
  remains the A1 / A5-step-2 boundary.

**Gap 3 — time-uniformity and the unitary-group transfer.**  The per-system
strong-resolvent convergence exists; the transfer to the unitary group —
`e^{−itA_m} → e^{−itA}` strongly, locally uniformly in `t` (the Trotter/Kato
step) — is not formalized, and nothing is stated about the long-time behavior for
the indefinite Hamiltonians.

**Gap 4 — the numerics' specifics are not the formalized algorithm.**
* *Restarted Krylov + reconstruction:* the H-series is single-shot.  The numerics
  restart (`evolve_restarted`) and reconstruct the full state from the reduced
  coefficients.  Missing: the restart cycle as a formal object, the per-restart
  error accumulation over a long interval, and the statement that reconstruction
  is the orthogonal projection of the evolved reduced state.  (The H8/H9 nesting
  — the coarse approximant is the fine one projected back — is the machinery;
  no accumulated-bound theorem exists.)
* *Multi-shift forward-sequence span identity:* `ChapterH5` covers the
  single-shift polynomial shortcut.  The identity
  `span{v₀, (H − z₁)v₀, (H − z₂)(H − z₁)v₀, …} = span{v₀, X₁v₀, X₂X₁v₀, …}`
  for *distinct complex* shifts (the resolvent side is in the selection
  theorems; the forward-sequence side is not) is unstated.
* *Gram whitening = orthogonal projection:* **closed except for the quantified
  near-degenerate bound.**  `ChapterSirkWhitening` identifies the whitened reduced
  operator with the compression `V∗XV` and shows the answer depends only on the
  retained subspace; `ChapterSirkGramWhitening` supplies the missing existence
  half — the Gram construction the code performs (`T∗ G T = 1` for
  `G = (synthesis)∗(synthesis)`) really is an isometric embedding of that
  subspace (`whitened_adjoint_comp_self`, `range_whitened`), such a `T` exists
  (`exists_isWhitening`), and for dependent raw vectors an orthonormalization
  exists at the rank (`exists_isometry_range_eq_span`), the exact form of the
  rank truncation, and the near-degenerate case is quantified through the
  geometric parameter `δ` (`norm_defect_synthesis_le`,
  `sirk_end_to_end_truncated_gram`).  Still missing: the link between `δ` and the
  discarded Gram *eigenvalues* at the numerical cutoff `rel_tol = 1e-12` —
  relevant precisely for the indefinite Hamiltonians whose Gram can be
  near-singular — and, beyond it, the floating-point analysis of Gap 6.

**Gap 5 — the physical-subspace (BRST) leakage.**  The truncated dynamics do
not preserve the physical subspace: the numerics document Ω-content growth under
aggressive truncation, which is why the solver rides a BRST projector along.
Missing: a formal bound on the leakage `‖Ωψ(t)‖` in terms of the truncation, for
the BRST-closed generators (`ChapterBRSTNilpotent` gives `Ω² = 0` and
`[H, Ω] = 0`; the truncation-leakage statement does not exist).

**Gap 6 — finite precision (the outermost boundary, recorded).**  Rounding-error
analysis of the Krylov iteration and of the reduced `m × m` matrix exponential is
entirely absent, and exact-real arithmetic cannot address it.  The formal results
are the exact-algorithm limits that the floating-point numerics approximate; a
backward-error statement (the computed quantities are the exact quantities of a
nearby shifted problem) is the only way to close the loop, and is out of scope for
the Lean formalization.  Recorded so the boundary is explicit.

### 12.3 Suggested attack order (for the Lean 4 specialist)

1. **Assemble the end-to-end theorem on the generic machinery first** — a
   system-independent lemma composing `ChapterH1`/`ChapterH4`'s φ-calculus with
   `ChapterH2`/`ChapterH7`'s compression and the `ChapterH6` decay, with abstract
   `C, Dmin, h` (Gap 1 + the abstract half of Gap 2).  This is the highest-value,
   lowest-risk step: it does not touch any physics.
2. **Instantiate per system, simplest spectral geometry first:** QYM (positive →
   Friedrichs), then NS Lagrangian (positive parabolic + ν), then NS Eulerian
   (indefinite → complex shifts), then QG (hyperbolic/indefinite + scalaron
   Fock).  Each instantiation discharges `hrt`, `hcx1`, `hcx2` from the existing
   selection/ESA modules and fixes the constants (Gap 2).
3. **The numerics-specifics as system-independent modules:** restarted Krylov
   (Gap 4a), the multi-shift span identity (Gap 4b), Gram-whitening-as-projection
   (Gap 4c), then the time-uniform unitary-group transfer (Gap 3).
4. **The two hardest, last:** the BRST leakage bound (Gap 5, NS Eulerian) and
   the Lagrangian Fock-of-Fock selection/flow (Gap 2, NS Lagrangian).

### 12.4 Definition of done (for §12)

For each of the four systems (NS Eulerian sequence-space and differential, NS
Lagrangian incl. the canonical realization and the Fock-of-Fock lifting, QG incl.
the scalaron Fock sector, QYM), a **named theorem** of the form
`‖e^{−itH} v − V_m e^{−itB_m} V_m∗ v‖ ≤ bound(m, {z_j}, t, constants)`, with every
hypothesis discharged from the existing modules, the constants explicit, the
restart/whitening specifics covered by the generic Gap-4 modules, and the §8 gate
green.  No global existence and no mass gap are claimed anywhere (unchanged; the
reliability statement is about the *selected generator and its flow*, exactly the
scope D5 already fixes).

