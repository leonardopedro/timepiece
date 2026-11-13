# The Standard-Model honest boundaries: what is now a Lean theorem, and what is not

> **Current work order — 2026-11-09:**
> [SM_ESA_COMPLETION_PLAN.md](SM_ESA_COMPLETION_PLAN.md), P0–P8, supersedes
> “SM refinements” and any reading of the model assembly results below as a proof
> for the complete manuscript matter interaction. Bosonic ESA and its enclosure
> are proved. The existing coupled matter theorem uses only two real Higgs
> components, a finite CAR factor and fixed Dirac matrix; the constant-background
> gauge theorem is separate. Full four-component/chiral data, operator-valued
> gauge coupling, spatial Dirac derivative, physical reduction and their common
> outer lift remain to be assembled and proved. Continuum CAR alone does not
> supply the corresponding infinite-mode Hamiltonian.
>
> Physical numerical acceptance means Hashimoto-SIRK approximation of that same
> complete inner operator and its actual joint-state outer enclosure. Legacy
> independent-momentum, contraction-dropping, scalar and decoupled builders are
> comparisons, not full-SM validation. See `../unfer/docs/SM_HAMILTONIAN_AUDIT.md`.
> The source audit below is not a new compilation or renewed numerical run.

**Numerical execution — 2026-11-09c:** the complete E1 component assembly
and graded joint-state rational Hashimoto solver now run in `unfer`, with
37 targeted Cargo tests and actual Cadabra export/import verification. See
[the implementation account](../unfer/docs/SM_FULL_IMPLEMENTATION.md).
This closes numerical implementation deferrals; L12 remains the formal
common-core, full-matter ESA and physical/graded lift work. No Lean compilation
was performed for this update.

**Current state of record** (updated 2026-09-23 after the closure wave, the book-BRST wave,
and the accounting identity of §2026-09-23d in `CONSOLIDATED_PLAN.md`).  Every theorem
cited here is intended to compile inside `lake build BookProof` with no `sorry` and no
`axiom` beyond the usual `propext`, `Classical.choice`, `Quot.sound`; the axiom audits are
`Work/SmStandardModelAudit.lean`, `Work/SmHonestBoundariesAudit.lean`, and
`Work/BookBrstAudit.lean`, and (for L2, closed 2026-09-23g) `Work/SmComparisonEsaAudit.lean`.  Historical boundary quotes that the tree has since *closed*
are kept only as section titles of the form *“…was open”* — the live list is **§L** below.

> **Supersession.**  Earlier drafts of this file left §1’s “Still open” line
> (*continuum CAR*, *gauge connection inside `D`*, *ghost/BRST sector*) standing after
> §5 had already closed all three.  Those three items are **not open**.  §5.5’s
> “everything of §§1–4” was likewise wrong for them.  This rewrite reconciles the ledger
> with the modules.

---

## §L. Still open, and explicitly not claimed

This is the only live “not claimed” list for the SM wave.  Everything else in the file is
either a closed boundary (theorem now in tree) or a historical quote.

| # | Boundary | Why it stays open |
| :-- | :-- | :-- |
| L1 | **Majorana masses and the see-saw** | `book.tex` works *“in the absence of Majorana masses”*; only the Dirac-type Yukawa `M_ν φ ν_R` and its biunitary/PMNS algebra are in `h`. |
| L2 | **Unconditional bosonic ESA** `sm_h_esa` — **closed (2026-09-23g)** | Fermionic half: `sm_fermi_fl_i/ii/iii`, `sm_fermi_esa`.  Bosonic half: `BookProof/Sm/ChapterSmFarisLavine.lean` proves both Faris–Lavine inequalities against `N = 2h + Σ_m q_m² + c₀` (`sm_commForm_le`, `c = 1`; `sm_norm_le_shift`, `K = 1`; `smComparison` provably cannot serve, §2bis) and reduces `sm_h_esa` to essential self-adjointness of `N` on `polyGaussCore 163` (`sm_h_esa_of_comparison_esa`).  That former hypothesis — a Kato-type statement for a coupled quartic Schrödinger operator in 163 variables, which Faris–Lavine structurally cannot supply — is now a **theorem**: `SmComparisonEsa.smFlN_esa` (every `c₀ : ℝ`), via `smFlN_eq_hamCoreS` (`N = −Δ_S + W`, `W = Σ_r Φ_r² + Σ_m q_m² + c₀`), `HermiteGraphApprox.hamCoreS_esa` (polynomial-core transfer), and `DegKatoEsa.ccHamS_esa` (Kato's theorem for `−Δ_S + W`, `W ≥ 1` smooth, on `C_c^∞`).  Hence **`SmComparisonEsa.sm_h_esa`** is proved with no hypothesis beyond `P : SmParams`.  Axioms: `propext`, `Classical.choice`, `Quot.sound` only (`Work/SmComparisonEsaAudit.lean`).  **Enclosure (2026-09-24b):** `BookProof/Sm/ChapterSmFockEsa.lean` lifts this to the bosonic Hamiltonian of record — `smSectorHam_esa` (every number sector of `⊕ₙ L²(ℝ^{163n})`), `smFockHam_esa` (`smFockHam` ESA on the finite-particle core `smFockCore`), and `sm_dGamma_esa` (`dΓ(h)` in the creation-left/annihilation-right spelling ESA on the finite-particle domain over `polyGaussCore 163`); axioms as above (`Work/EnclosureEsaAudit.lean`).  **Full assembly (2026-09-24c):** `BookProof/Sm/ChapterSmFullEnclosure.lean` — `smFullHam = h_B ⊗ 1 + 1 ⊗ (smDirac + smYukawa)` on `L²(ℝ¹⁶³) ⊗̂ FermiFock n` (Yukawa in a fixed Higgs background: a tensor sum, no boson–fermion coupling operator), `smFull_h_esa` (one-particle, on `polyGaussCore 163 ⊗ FermiFock n`) and `smFull_dGamma_esa` (`dΓ(h_full)` ESA on the finite-particle domain); audit `Work/FullEnclosureAudit.lean`.  **Operator-valued Yukawa (2026-09-24d):** `BookProof/Sm/ChapterSmYukawaCoupling.lean` — `smYukawaFullHam = h_B ⊗ 1 + 1 ⊗ smDirac + φ₀ ⊗ smYukawa M 1 + φ₁ ⊗ smYukawa M i` (a genuine boson–fermion coupling; `smYukawa_eq_re_im` recovers the fixed background), `smYukawa_h_esa` and `smYukawa_dGamma_esa` for `λ > 0`, via `higgsMul_relBound` (relative bound `0` from the Higgs wall) and `TensorKatoRellich.essentiallySelfAdjointOn_tensorSum_add_coupling` (Kato–Rellich for product couplings with a finite-dimensional factor); audit `Work/SmYukawaCouplingAudit.lean`. |
| L3 | **Continuum spectrum / mass gap** of the bosonic `dΓ(h)`; QCD confinement | Spectral claims are only the finite-mode fermionic spectrum/gap and the one-particle relativistic energies. |
| L4 | **EWSB as dynamics**; measured CKM/PMNS parameters | Statics only (vacuum manifold, Goldstone flatness, radial curvature, mass form of broken generators). No expansion of `H` around the vacuum, no `W/Z` mass value, no Wolfenstein/PMNS angles, phases, ordering or absolute masses — only unitarity identities and `yukawa_entry_bound`. |
| L5 | **Size of the BRST cohomology** `ker Ω / im Ω` | The quotient is defined and well defined (`exactStates_le_physicalStates`); its dimension is not claimed. |
| L6 | **Continuum local Gauss law** | The local gauge algebra is a finite-dimensional Lie algebra with derivations `∂_μ` (book’s totally antisymmetric `SU(N)` structure constants); Gauss law closes in that algebra, not at every point of continuum space. |
| L7 | **Faddeev–Popov determinant (SM/book formalism)** | The book’s BRST formalism uses none and none is constructed. (The separate QYM abelian FP sector is `ChapterYangMillsGhostSector.lean`, not part of the SM `h`/`N` record.) |
| L8 | **Continuum CAR beyond the Fock representation** | `ChapterSmCarContinuum` builds the Fock rep on the vacuum over `ℓ²(ℕ)` / arbitrary separable one-particle space; nothing about inequivalent representations, the C\*-completion, or a Hamiltonian on that space. |
| L9 | **Gauge-field dynamics / continuum limit of `D`** | Connection in `ChapterSmGaugeConnection` is a constant collective-coordinate background: `D_j = i(k_j + A_j)` carries `ik_j`, not an unbounded derivative, so that module’s `[D_j, D_l]` sees only the non-abelian part of `F` (`∂A = 0` by construction). The **full** `F_{μν} = ∂_μ A_ν − ∂_ν A_μ + [A_μ, A_ν]` (curl **and** `f^{abc}AA`) is in the tree as `smMagG`/`smMagW`/`smMagB` — but no gauge-field dynamics (time evolution of `A`) and no continuum limit of `D` on `L²(ℝ³)` is claimed. **Route correction (2026-11-09):** retain the stated SM jet coordinates. The NS/QG derivative-convolution elimination does not redefine this operator; its missing full matter bridge is P0–P4 in the current completion plan. |
| L10 | **Finite mode set for the SM BRST multiplet** | One plane-wave matter multiplet + twelve ghosts (and the book’s `N`-colour realization); not a full continuum field BRST. |
| L11 | **QG accounting identity in the SM form** | QG 3D reduction is **non-ADM** (`book.tex` ~8226–8244): `v^μ = δ^μ_0`, ghosts constant in the timepiece, charge with 4D functional form; frame fermion `{G, i b_j A_0^j}` is **not** covered by `bookGfTerm_eq_zero_of_Afield0`. |
| L12 | **ESA of the complete manuscript matter assembly and physical outer lift** | The model results in L2 remain valid within their scope. Full four-real-Higgs/chiral data, operator-valued gauge coupling, spatial Dirac derivative and the common-core physical reduction/lift require `SM_ESA_COMPLETION_PLAN.md` P0–P6. The infinite-mode operator requires P7 where intended. **P5's kinematic half is now closed (2026-11-12, plan §44):** `BookProof/Sm/ChapterSmPhysicalReductionEsa.lean` proves the closure-level parity reduction — `deficiencyTrivialAt_iff_sectors`, `smNormalForm_esd_iff_parity_sectors` under `ParityGradedCoeffs` alone, plus `topologicalClosure_evenCore`/`topologicalClosure_oddCore` — so the deficiency space of the full normal form is trivial iff both parity sectors are, and each sector restriction has a dense graph core. This does **not** prove ESA of either sector: that is P4's `PotSelfBound`/`FormDomainComparison`, unchanged and still a hypothesis, and the graded outer lift `Γ_s ⊗ Γ_a` consumes it. **Two follow-ups landed the same day.** (i) The parity split does *not* weaken P4 (plan §45): `BookProof/Sm/ChapterSmSectorFormDomain.lean` proves every elementary tensor is a parity eigenvector (`coupledParity_deltaFun`), so the whole inner test class sits inside each sector and a sector-only relative bound already gives the scalar one (`scalarBound_of_evenSectorBound`, `scalarBound_of_oddSectorBound`); `PotSelfBound`/`FormDomainComparison` is therefore one open problem, not two, and the parity sector is not an easier route. (ii) The BRST *algebra* is now built (plan §46, `BookProof/Sm/ChapterSmBrstQuotient.lean`): nilpotency ⇒ `im Q ⊆ ker Q`, ghost nullity for a charge symmetric for the charge form, well-definedness of that form on the cohomology (`kform_well_defined`), parity descent of `ker Q`/`im Q`, orthogonality of the sectors for the charge form, and sector-by-sector positivity. The Kugo–Ojima condition `PhysicalPositivity` remains a **named input, not a theorem** — the quartet structure of the model's charge is not built — so still no positive physical inner product is claimed. **Two more follow-ups (2026-11-12, plan §47–§48).** (iii) The quartet *mechanism* is now proved (plan §47, `BookProof/Sm/ChapterSmQuartet.lean`): from `Q P + P Q = 1 − V` with `V`'s range in `ker Q` one derives `V Q = 0`, the decomposition `x = Q (P x) + V x` of every closed `x`, the reduction `⟨x,x⟩_η = ⟨V x, V x⟩_η`, and hence `PhysicalPositivity` itself (`physicalPositivity_of_quartet`), sector by sector as well (`physicalPositivity_of_quartet_sectors`); `exQuartet` is a non-vacuous 2⊕1-dimensional instance whose cohomology is one-dimensional (`exE2_not_exact`), and `isBrst_smBrstCharge` links the SM charge. The SM's own `(P, V)` is still missing, so this is a mechanism, not an SM proof. (iv) P4's reverse estimate is now **derived from one algebraic hypothesis** (plan §48, `ChapterSmReverseEllipticQuartic.lean`): `GradDom` (`∑_j ‖(∂_j W) p‖² ≤ a ‖W p‖² + b ‖p‖²`) implies `∃ β, PotSelfBound P c₀ β` (`exists_potSelfBound_of_gradDom`), by the identity `‖B‖² = Re ⟪B,N⟫ − Re ⟪B,k⟫` plus §23's weighted integration by parts, Cauchy–Schwarz and Young — **no elliptic regularity is used**. `GradDom` holds for a coercive quartic (`gradDom_coercive_quartic`) and fails for the flat `X₀²X₁²` (`not_gradDom_flat_quartic`), and it is *not* established for `smPotPoly`, so `PotSelfBound` remains a hypothesis — P4 is now one algebraic question about the 49 field polynomials rather than an analytic statement about `−Δ_S + W`. **(v) The 49 flat directions do not refute `GradDom` (plan §49, `ChapterSmGradDomStructural.lean`):** the magnetic forms *are* of the `X₀²X₁²` type (their squares vanish on `G = 0`), yet `W` carries the coercive quadratic `∑_m q_m²` and every `∂_j Φ_r` is linear in the momentum coordinates, so `pointwise_dom_of_sq_sum` gives `∑_j (∂_j W)² ≤ a W² + b` with explicit `a, b`; the model `X₀²X₁² + X₀² + X₁²` obeys it with `a = 40, b = 24` (`gradDom_flat_plus_quadratic`) where the bare `X₀²X₁²` obeys nothing. Not formalized: the per-form support table for the 49 forms and the pointwise→`L²` transfer (the `l2_gradDom_of_pointwise` once cited in §48's docstring did not exist at that date; it was supplied later — plan §52, see (viii)). So `PotSelfBound` remains a hypothesis, with the algebraic question now answered affirmatively and only those two bookkeeping steps open. **(vi) The physical projector is constructed, not assumed (plan §50):** from a b-ghost satisfying `Q P Q = Q` and `P Q P = P`, `V = 1 − (Q P + P Q) + Q P² Q` is a projector with `Q V = V Q = 0` and `Q (P − Q P²) + (P − Q P²) Q = 1 − V` (`quartetOfHomotopy`), so `PhysicalPositivity` follows from **one** input (`physicalPositivity_of_homotopy`); a parity-even b-ghost gives a parity-even `V` (`physProjOf_commute_parity`, `physProjOf_mem_even`) and `physicalPositivity_of_homotopy_sectors` is the ghost-parity-even statement. The SM's own b-ghost is still missing, so `PhysicalPositivity` for `smBrstCharge` is still a named input — now a single one. **(vii) The per-form support table is the single remaining input for `PotSelfBound` (plan §51–§52):** `linForm`/`polyW_linForm`, the Cauchy–Schwarz bound `sq_polyW_linForm_le` and `gradBound_of_linear` show that a support table `∂_j Φ_r = ∑_{i∈L} b_i x_i` with `L ⊆ smS` *is* `GradBound`, coefficients included; `smPotPoly_eq_wsSum` identifies `smPotPoly` with `wsSum`; `ChapterSmGradDomTransfer` integrates the pointwise bound (`l2_gradDom_of_pointwise`) and `exists_potSelfBound_of_gradBound` composes the chain into `∃ β, PotSelfBound P c₀ β`. What then remained was the `pderiv` computation for the five families (none of which meets a derivative coordinate) — one finite algebraic input, discharged in (viii). **(viii) `PotSelfBound` is proved — P4's elliptic input is discharged (2026-11-13, plan §53, `BookProof/Sm/ChapterSmGradTable.lean`):** the per-form `pderiv` table is supplied not form by form but by a *normal form*: `Biform A T` carries the polynomial together with its coefficients (a constant, linear atoms in `T`, bilinear atoms in `A`), `pderiv_eq` reads the derivative at `j ∈ A` off that data (`∂ poly = ∑_v C (sqf j v + sqf v j) · X v`, the linear part vanishing because `A ∩ T = ∅`), and `sq_le` is Cauchy–Schwarz against the coercive quadratic on `A`. The five families are `Biform smS (univ \ smS)` by shape alone — no `levi`/`fabc`/`eabc`/`tgen`/`ygen` bookkeeping, and no numerical constant: `gradBound_smPhi`'s constant is the total squared coefficient. Hence **`exists_potSelfBound_sm : 0 ≤ c₀ → ∃ β, PotSelfBound P c₀ β`** for every parameter set, by §52's `exists_potSelfBound_of_gradBound`. The six prose blocks that recorded the self-bound as open (§22, §23, §26, §27, §35 of `BookProof.lean` and `ChapterSmKineticGarding`'s docstring) are corrected in the same commit, since the route they proposed — interpolating `∇` against the graph norm, or the Hessian sign identity — is not the route that works. What (viii) does **not** give: `PhysicalPositivity` still has no matter-model quartet data (L12 (iii)/(vi) stand), no physical inner product is claimed, `PotSelfBound` is an estimate about `W` rather than a spectral statement about the joint operator, and `β` is produced, not computed sharply. **(ix) The produced constant is *used*, and the normal form's reuse has a proved boundary (2026-11-13, plan §54):** `ChapterSmGradTable` §5 turns §53's `∃ β` into the downstream statements instead of leaving them conditional — `PotSelfBound_mono` (monotone in `β`), `exists_potSelfBound_sm_nonneg` (`∃ β, 0 ≤ β ∧ PotSelfBound P c₀ β`), then **§19's `hpoly`** (`exists_kineticSum_bound_sm`) and **§15's P2 relative bound** (`exists_smNormalForm_norm_le`), both by the §26/§15 lemmas at that `β`. The four hypotheses §15's lemma carries but does not consume (`_hpos`, `_hkin`, `_hcoord`, `_hmass`) are kept `_`-prefixed and documented, so the statements are drop-in replacements rather than silently strengthened. On the cross-model question — does the same normal form prove QYM's and NS's gradient domination "the same way"? — the answer is split, and the split is the result: `Biform`, `pderiv_eq` and `sq_le` are dimension- and model-generic, so the QYM and NS forms *are* normal forms with their derivative table and Cauchy–Schwarz bound, but **`GradDom` is false for the QYM potential**. `weylPotPoly Φ = ∑_j Φ_j² + 1` carries no coercive quadratic; at a single bilinear form it is `weylFlat`, identified with `YangMillsNonAbelianEsa.weylPotPoly (fun _ : Fin 1 => X₀X₁)` by `weylFlat_eq_weylPotPoly`, and `not_gradDom_weylFlat` refutes the domination on the curve `(t, 1/t)`, where the gradient terms give `4/t² + 4t²` while `W` stays `2` — §48's flat mechanism, now at the model that needs it. What this does **not** say: nothing about QYM's or NS's elliptic estimates beyond that obstruction, and no positive result for those models — their coercive input (a confining term, a mass term, an anisotropic weight) must come from their own structure, not from the SM's `∑_m q_m²`, and only the QYM instance was formalised at that date — the NS half stood as the proof template, which (xi) below now replaces with a proved NS statement. **(x) The obstruction is sharp, and the quartet attempt is withdrawn (2026-11-13, plan §55):** putting the coercive term back identifies the whole difference — `weylCoercive Φ M = weylPotPoly Φ + ∑_{m∈M} X_m²` is `wsSum Φ M 1` (`weylCoercive_eq_wsSum`), so §49's estimate applies unchanged (`gradDom_weylCoercive`) and at `X₀X₁` gives `a = 40`, `b = 24` (`gradDom_weylCoercive_flat`) against §54's `not_gradDom_weylFlat` for the same potential without the term. So what QYM/NS lack is a term, not a technique; choosing it is modelling, and no sharp constant is computed. On the quartet: the request to build the SM's own b-ghost was **not** carried through and nothing was upgraded. The abelian (`f3 = 0`) sector was attempted — `c† ⊗ T` over the matter space with `b ⊗ S` for a generalized inverse `S` — and withdrawn for two reasons: this Mathlib has no product inner-product space (so the two-slot model cannot feed `IsBrst`/`BrstQuartet` without an `EuclideanSpace` reformulation), and, decisively, the ghost-pairing metric `(u,v) ↦ (v,u)` satisfies `η (V x) = V (η x)` but **not** the `η (V y) = V y` that the no-ghost theorem needs — invariance of the physical subspace is not definiteness of it. `PhysicalPositivity` for `smBrstCharge` therefore remains a named input, now with two named missing objects (a contracting homotopy for the non-abelian complex, and a Krein metric fixing the physical subspace) rather than one. **(xii) The b-ghost is built, on an index-restricted space (2026-11-13, plan §57, `BookProof/Sm/ChapterSmIndexGhostQuartet.lean`):** the `EuclideanSpace` reformulation (x) named as missing exists, and the second obstruction was a property of the *pairing* metric rather than of the model.  On `Space n m = EuclideanSpace ℂ ((Fin n × Bool) ⊕ Fin m)` — ghost `(a, false)`, antighost `(a, true)`, physical `inr j` — the charge shifts ghost→antighost, the b-ghost shifts back, and the index-swap metric `Eta` is proved to fix the *computed* projector's range (`eta_physProj`), because that projector lands on the physical coordinates where `Eta` is the identity.  Every hypothesis of `physicalPositivity_of_homotopy` is discharged at every `n, m` (`Q_nil`, `QPQ`, `PQP`, `krein`, `symm` via `Eta_inner`/`Eta_involutive`, `eta_physProj`), so `physicalPositivity` carries **no hypotheses**, and `physVec_not_exact` keeps it from being vacuous (a physical mode is closed and not a gauge orbit).  This is **not** `smBrstCharge`: that charge is a `Module.End` on `FermiFock (m + 12)`, so what remains is an inner product on that Fock space and the identification of its twelve ghost modes with the index pattern — an identification, no longer quartet data.  Nothing is upgraded for the SM until that identification is written down. **(xiii) The Fock side: the product was never missing, the identification is partial (2026-11-13, plan §60, `BookProof/Sm/ChapterSmIndexGhostFock.lean`):** (xii) named "an inner product on that Fock space" as the remaining gap, and read literally that is wrong — `FermiFock n = EuclideanSpace ℂ (Finset (Fin n))` *is* an ℓ² space, `occ_inner` is its orthonormal occupation basis and `inner_creat_left` makes the CAR operators its adjoints.  What is proved there instead: the twelve ghost modes `ghostMode m a` inject into `Fin (m + 12)`, their occupation vectors `ghostVec` are orthonormal (`ghostVec_orthonormal`, so the one-particle ghost sector is an isometric copy of `EuclideanSpace ℂ (Fin 12)`), that copy is the orbit of the vacuum under `ghostCre` (`ghostCre_vac`), and the metric pairing the index model calls `η` is the Fock adjunction `b_a = (c^a)†` (`ghost_pairing`).  What is **not** identified: `smBrstCharge` is a degree-one derivation `∑ χ_a G^a − ½ ∑ f χ β`, so it does not preserve the one-particle ghost sector — a single ghost does not map to a single antighost — and the index quartet is therefore the free part of the ghost complex rather than a subcomplex of the SM charge.  The open object is the b-ghost of the derivation. **(xv) `VolDom` is refuted on the normal form, and the repair is a different model (2026-11-13, plan §61, `BookProof/Ns/ChapterNsVolDomShear.lean`):** the penalty across the shear family leads with `(εt)²/2`, and `shear_grad_sq` is the exact identity `∑(∂V)² = V²(4/t² + 4/ε²)`; `not_volDom_shear` then shows `¬ ∃ A B` bounding the gradient by the potential, by the single family `(1/d, d)` on which the potential is the constant `1/2` while the gradient grows like `1/d`.  **The bridge from the model's literal `volPot` to this normal form is not formalized** — it is the §58.1 second-order expansion plus a measurement — so the refutation is stated for the normal form, in the module and in the plan.  A deformation norm `V_κ + (μ/2)∑(1+|k|²)|ξ̂|²` does appear to repair the estimate (measured sup `≈ 21` at `μ = 0.01`, and the shear ratio *decreases* as the tilt shrinks, unlike `μ = 0`), but that is a measurement on a truncation of a *changed* Lagrangian, and the `μ = 0` column below `ε = 1e-4` is floating-point cancellation, not data.
(xvi) The b-ghost of the derivation exists and contracts onto matter (2026-11-13, plan §62, `BookProof/Sm/ChapterSmIndexGhostDerivation.lean`):** the antighost sum `b = ∑_a β_a` satisfies `{∑_a χ_a G^a, ∑_b β_b} = ∑_a G^a` (`bGhost_anticomm`), so `bGhost_no_contraction` says a homotopy for the derivation would force the Gauss generators to sum to the identity, and `bGhost_anticomm_abelian` identifies §57's index quartet with the `∑ G^a = 0` fibre.  **The structure-constant half of `smBrstCharge` is not covered**, so `{Ω, b}` picks up an `f`-carrying ghost bilinear that is not written down, and `PhysicalPositivity` for `smBrstCharge` stays a named input.
(xiv) The sector refinement cannot be read globally (2026-11-13, plan §59, `BookProof/Sm/ChapterSmIndexGhostSectors.lean`):** `physicalPositivity_of_homotopy_sectors` asks for non-negativity *and* definiteness of the charge form on the whole of each parity sector, and `global_sectors_force_zero` shows those four hypotheses make the form positive definite on the whole space, whence `Q = 0` for any nilpotent self-adjoint charge — so they cannot hold for any nonzero BRST charge, and `parity_globals_fail` witnesses it on the index model.  Read on the closed space they *do* hold for the ghost parity (`Par` = `−1` on ghosts and antighosts, `+1` on physical modes): `kform_even_nonneg` on even closed vectors, `kform_odd_closed` on odd ones, assembled by `kform_nonneg_closed` and stated as `sector_hypotheses_closed`.  The radical half still needs `eta_physProj`; the sector route supplies only non-negativity. **(xi) The NS model's own potential is settled in the other direction (2026-11-13, plan §56, `BookProof/Ns/ChapterNsGradDomCoercive.lean`):** the Lagrangian energy `lagEnergy = 1 + ½|v|² + V_κ` carries its coercive quadratic natively, so `∂_{v_j}E = v_j` gives `∑_j (∂_{v_j}E)² = ∑_j v_j² ≤ 2E` (`lagEnergy_vel_gradDom`) with **no constant term**, and the Lyapunov displacement block contributes `2 · ½∑ξ²` exactly (`disp_grad_sum`) — no term has to be added, which is precisely the difference from §55's `weylCoercive`. What remains is the volume penalty's own estimate, named `VolDom A B` on `V_κ`, and `lagGradDom_of_volDom` reduces the whole potential to it with `a = 2A + 3`, `b = 2B + 3`. **The input is false, not merely hard (2026-11-13, plan §58):** `not_gradDom_flatSextic` shows that non-negativity plus degree six cannot supply it, and the model's own penalty fails it as well — the *shears* are flat for `V_κ` (`det(I + tN) = 1` for every amplitude `t` when `N = e_x ⊗ e_y`, `N² = 0`, so `V_κ = 0` along them) while `V_κ` still varies transversally like `ε t`: with a tilt `εB`, `B = e_y ⊗ e_x`, one has `det F − 1 = −ε t + O(ε²)`, hence `V_κ ≈ (κ/2)ε²t²` and `|∇V_κ|²/V_κ² → 4/ε²`, unbounded as `ε → 0`. So **no finite `A, B` make `VolDom` hold for `volPot`**, `lagGradDom_of_volDom`'s hypothesis is unsatisfiable, and the NS Lyapunov energy is *not* gradient-dominated: the §49 chain does not reach it. `scripts/eval-vol-dom.py` evaluates the two-mode truncation exactly (dual-number gradients) and reproduces the `4/ε²` saturation at `t` up to `1e5`, `ε` down to `1e-4`. The two coercive blocks above are unaffected. Not claimed: any numerical `A, B` (there are none), and no ESA of the Lagrangian generator `N_L`, which stays the explicit hypothesis of `lagKoopman_esa_of_comparison_esa`.

|

---

# 0. Faris–Lavine Corollary 1.1: where it already lived

The criterion itself is **proved**, not assumed, in

* `BookProof/Toolbox/ChapterFarisLavineCore.lean` — `BookProof.FarisLavine`:
  `essentiallySelfAdjointOn_of_farisLavine` (Theorem 1 of Faris–Lavine 1974) and
  **`essentiallySelfAdjointOn_core_of_farisLavine`** (Corollary 1.1), with
  `essentiallySelfAdjointOn_restrict_of_graph_core`;
* split copies `ChapterFarisLavineCore/Part1.lean`, `Part2.lean`;
* users elsewhere: `ChapterNavierStokesFlow.lean`, `ChapterNavierStokesAffineFiberEsa*.lean`,
  `ChapterNavierStokesDiffFarisLavine*.lean`, `ChapterNavierStokesHermiteFarisLavine*.lean`,
  `ChapterNavierStokesFockFarisLavine.lean`, `ChapterNavierStokesIkebeKato.lean`,
  `ChapterNavierStokesMomentumEsa.lean`, `ChapterNavierStokesFockManyMode.lean`.

What was missing for the SM was never the criterion; it was the **hypotheses** for the SM
operators and the algebra the fermionic operators live on — both now supplied for the
fermionic sector and (Cadabra-certified) for the bosonic algebraic content.

---

# 1. Closed: finite CAR, Dirac/Yukawa, spinor structure

**Was:** *“The Dirac and Yukawa operators are not formalized (they need the CAR/Grassmann
algebra) — only the mixing algebra they rest on is.”*  
**Now:** formalized for a finite mode set.

* `BookProof/Sm/ChapterSmCarAlgebra.lean` — `FermiFock n = ℓ²(Finset (Fin n))`, Jordan–Wigner
  ladders, the four CAR relations, adjointness, contractivity, occupation number,
  `fermiBilin`, `fermiEnergy_occ`, **`fermi_mass_gap`**.
* `BookProof/Sm/ChapterSmDiracYukawa.lean` — `smDirac`, `smYukawa`, `smFermiHam`;
  `isMixing_mul`, **`yukawa_entry_bound`**; Fermionic FL **`sm_fermi_fl_i/ii/iii`**,
  **`sm_fermi_esa`**.
* `BookProof/Sm/ChapterSmDiracSpinor.lean` — `diracOneParticle` Hermitian, mass-shell
  `H² = (k² + m₁² + m₂²)`, energies `±√(k² + m₁² + m₂²)`, `diracFieldHam`,
  **`dirac_field_esa`**.

*Module-header note in `ChapterSmCarAlgebra` still says continuum CAR / spinor / ghost are
“not built here” — true **of that file**; the boundary is closed by the modules of §5.*

---

# 2. Closed for the fermionic sector and (since 2026-09-23g) for the bosonic sector (L2)

**Was:** *“The three Faris–Lavine hypotheses of §D6b-SM.3 remain symbolic.”*

**Now Lean theorems for the fermionic sector** with
`N = Σ_i ω_i a†_i a_i + c₀` (`ω_i ≥ 0`, `c₀ ≥ 1`):

| hypothesis | theorem | constant |
| :-- | :-- | :-- |
| (i) `±h ≤ c₁N` | `sm_fermi_fl_i` | `c₁ = Σ_{i,j} ‖h_{ij}‖` |
| (ii) `|⟨ψ,[h,N]ψ⟩| ≤ c₂⟨ψ,Nψ⟩` | `sm_fermi_fl_ii` | `c₂ = 2c₁Ω` |
| (iii) `|⟨ψ,[N,[N,h]]ψ⟩| ≤ c₃⟨ψ,N²ψ⟩` | `sm_fermi_fl_iii` | `c₃ = 4c₁Ω²` |

side conditions: `smFermiN_symmetricOn`, `sm_fermi_N_ge_one`, `sm_fermi_N_add_one_surjective`;
conclusion **`sm_fermi_esa`**; spinor instance `dirac_field_esa`.

**Bosonic half (L2), current state.**  `BookProof/Sm/ChapterSmFarisLavine.lean` is in the tree
and `sorry`-free.  It proves the two inequalities the Lean Faris–Lavine theorems actually
consume — the form commutator bound `sm_commForm_le` (`c = 1`) and the relative bound
`sm_norm_le_shift` (`K = 1`) — and instantiates Theorem 1 / Corollary 1.1 through the new
abstract last mile `CoreData.esa_core`.  Two honest qualifications:

* the comparison operator is **not** the `smComparison` of §D6b-SM.2 but
  `N = 2h + Σ_m q_m² + c₀` (see §2bis for why the quartic uncoupled `N₀` cannot work);
* the conclusion is **conditional**: `sm_h_esa_of_graph_core` assumes
  `IsGraphCore (smFlComparison P hc₀) (polyGaussCore 163)`, and `isGraphCore_of_esa` turns
  that into the plainer `sm_h_esa_of_comparison_esa`, which assumes only
  `EssentiallySelfAdjointOn (polyGaussCore 163) (smFlN P c₀)`.  Both are named hypotheses,
  never axioms.  The unconditional `sm_h_esa` was therefore
  not claimed by that module alone.

**Update 2026-09-23g — the hypothesis is discharged.**  `BookProof/Sm/ChapterSmComparisonEsa.lean`
proves `smFlN_esa : EssentiallySelfAdjointOn (polyGaussCore 163) (smFlN P c₀)` for every
`c₀ : ℝ` and hence the unconditional **`sm_h_esa P`**.  The Kato-type input is supplied by

* `BookProof/Toolbox/ChapterDegKatoEsa.lean` — `ccHamS_esa`: `−Δ_S + W` (kinetic part on any
  coordinate subset `S`, `W` smooth, `W ≥ 1`) is essentially self-adjoint on `C_c^∞(ℝᵈ)`
  (mollifier + cut-off energy argument; no elliptic regularity);
* `BookProof/Toolbox/ChapterHermiteGraphApprox.lean` with `BookProof/Toolbox/ChapterHermiteLadderOrder.lean`
  — `hamCoreS_esa`: for a real polynomial `W ≥ 1`, every `C_c^∞` vector is a graph-norm limit
  of Gauss–polynomial vectors, so essential self-adjointness transfers to `polyGaussCore`;
* `smFlN_eq_hamCoreS` — on the core `N = −Δ_S + W` with `S` the 40 momentum coordinates and
  `W = Σ_r Φ_r² + Σ_m q_m² + c₀ ≥ 1` for `c₀ ≥ 1`; other `c₀` by a bounded shift.

No named hypothesis and no axiom remains on this route; `#print axioms` reports only
`propext`, `Classical.choice`, `Quot.sound`.

Not needed for the Friedrichs route (`sm_friedrichs_extension`,
`sm_dGamma_friedrichs_extension`).  The Cadabra module
`../unfer/docs/faris_lavine_n_sm.cdb` certifies *algebraic shape* (CHECK 1–28 + PART F) at
exit 0; a shape check is not the inequality, and the Lean FL theorems consume symmetry +
positivity + surjectivity of `N+1` + the form commutator, not the double commutator (iii).

---

# 2bis. Why `smComparison` cannot be the Faris–Lavine comparison operator

Write `h = ½T + V_h` and `N = T + V_N + c₀` with `T = Σ_m π_m²`.  The commutator is first
order,

```
i[h, N] = Σ_m (π_m G_m + G_m π_m),   G = ∇(½V_N − V_h),
```

so `± i[h,N] ≤ c N` forces the pointwise bound `|G|² ≤ c²(V_N + c₀)`: test the form on a
wave packet `e^{iξ·x}φ` concentrated at a point and optimize in `ξ` (the optimum is at
`ξ = G/c`, not at `ξ = G`).  For `smComparison`, `V_N = Σ_m q_m⁴ + …` is quartic and `G` is
cubic.  Along a single gluon direction `G^1_1 = R` the totally antisymmetric structure
constants kill the non-abelian magnetic energy and `φ = 0` kills the covariant Higgs
derivative, so `∇V_h = 0` there and the requirement reads `4R⁶ ≤ c²R⁴` — false for large
`R`.  The obstruction is caused by the quartic confinement of `N` itself and is already
present for the free Hamiltonian; it is not an artefact of the interaction.

The cure — the one Faris and Lavine use in their own application — is to let the comparison
operator contain the Hamiltonian, so that `∇V_h` cancels: with `V_N = 2V_h + Σ_m q_m²` one
gets `G = ½∇(Σ_m q_m²)`, which is linear, and both inequalities hold with absolute
constants.  That is `smFlN`.  The price is that graph-core-ness of `N` is no longer free.

That price has now been paid (2026-09-23g): Faris–Lavine indeed cannot produce
essential self-adjointness of `N` — any admissible `N` contains `2V_h` and is a coupled
quartic Schrödinger operator in 163 variables — so it is supplied by an independent
Kato-type theorem, `DegKatoEsa.ccHamS_esa`, transferred to the Gauss–polynomial core by
`HermiteGraphApprox.hamCoreS_esa`.  The result is `SmComparisonEsa.smFlN_esa` and the
unconditional `SmComparisonEsa.sm_h_esa`.

---

# 3. Closed: derivative-coordinate summands of `N₀`

**Was:** *“The derivative-coordinate summands of `N₀` lie outside the ESA chain.”*

**Now closed** in `BookProof/Sm/ChapterSmComparisonFull.lean`:
`smoothPotential_essentiallySelfAdjoint` / **`deriv_coordinate_esa`** ⇒ each derivative
coordinate is an `EsaOp`; **`sm_N_full_esa`** (all 160 summands),
`sm_N_full_stone_flow`, **`smFullChain_length = 1+36+3+120 = 160`**.
Framework: `ChapterTensorSumChain.lean`.

---

# 4. Still open in part: spectrum, gap, dynamics, measured parameters (L3, L4)

**Addressed where the content is a theorem:**

* Fermionic spectrum/gap: `fermiEnergy_occ`, **`fermi_mass_gap`**;
  one-particle relativistic energies: `diracOneParticle_eigenvalue_sq`.
* EWSB **statics**: `ChapterSmHiggsVacuum.lean` — `higgsV_eq_min_iff`,
  `higgs_goldstone`, `higgs_radial`, `gaugeMassForm_eq_zero_iff`.

**Still open (L3, L4):** continuum spectrum/mass gap of bosonic `dΓ(h)`; QCD confinement;
EWSB as dynamics; any measured CKM/PMNS parameter beyond unitarity + entry bound.

---

# 5. The closure wave: the three §1 boundaries that are now theorems

The old §1 boundary line was: *“Still open: the continuum CAR algebra over an
infinite-dimensional one-particle space, the gauge connection inside `D`, the ghost/BRST
sector, and Majorana masses / the see-saw.”*  
The **first three are closed**; only **Majorana / see-saw (L1)** remains from that sentence.

## 5.1 Closed: continuum CAR — `BookProof/Sm/ChapterSmCarContinuum.lean`

Mode set `ℕ`, one-particle space `ℓ²(ℕ)` (any separable one-particle space via a Hilbert
basis), Fock space `CFock = ℓ²(Finset ℕ)`.

* `cAnn`/`cCre`, four CAR relations, adjointness;
* smeared `cCreS f`/`cAnnS f` for arbitrary `f ∈ ℓ²(ℕ)`;
  **`car_smeared`**: `{a(f), a†(g)} = ⟪f, g⟫`; `norm_cCreS_le`: `‖a†(f)‖ ≤ ‖f‖`;
* `oneParticleIsometry`, `norm_cCreS_eq`;
* **`car_hilbert`** over an arbitrary separable one-particle Hilbert space.

*Still open here (L8):* Fock representation on the vacuum only; no inequivalent
representations, no C\*-completion claim, no Hamiltonian on this space.

## 5.2 Closed: gauge connection inside `D` — `BookProof/Sm/ChapterSmGaugeConnection.lean`

Minimal coupling in the constant collective-coordinate background:
`D_j = i(k_j + A_j)`, `A_j = g Σ_a A^a_j T_a`.

* `conn_conjTranspose`, `covD_conjTranspose`, `covD_zero_coupling`;
* **`covD_commutator`** — non-abelian field strength (operator form of
  `W^j_{μν} = −(i/g) tr([D_μ,D_ν]τ^j)` / the `g_s f^{abc} G^b_j G^c_k` term);
* `covD_conj`, `conn_gauge_transform` — gauge covariance;
* `diracGaugeMat`, `diracGaugeField`, **`dirac_gauge_field_esa`** — second quantization
  and ESA through the Fermionic FL hypotheses.

*Still open here (L9):* constant background (`ik_j`, not ∂), so this module’s
`[D_j, D_l]` sees only the non-abelian part of `F` (`∂A = 0`); the full
`F = ∂A − ∂A + [A,A]` lives in `smMagG`/`smMagW`/`smMagB`; no gauge-field
dynamics, no continuum limit of `D`. **Route correction (2026-11-09):** the SM realization retains its independent jet coordinates. The current completion plan P0–P4 supplies the missing operator-valued connection and spatial Dirac assembly; no NS/QG jet elimination is used.

## 5.3 Closed: ghost / BRST sector — `ChapterSmBrstGhost.lean` + `ChapterSmGaugeRepresentation.lean`

* `smStruct f₃` with **`smStruct_antisymm`**, **`smStruct_jacobi`**;
* twelve ghosts on the CAR algebra, `smGhostCAR`, `ghostNumber`;
* **`fermiBilin_lie`** ⇒ Gauss generators close; **`brstCharge_nilpotent`**,
  **`smBrstCharge_nilpotent`**;
* `ChapterSmGaugeRepresentation`: `su2gen_closes`, `smGen_closes`,
  **`sm_brst_nilpotent_rep`** on the 18-mode Fock space (6 matter + 12 ghosts), with `su(3)`
  antisymmetry/Jacobi **derived** from the two defining relations
  (`BookProof.YangMillsSU3`).

*Still open here (L5, L7, L10):* cohomology size; no Faddeev–Popov determinant; finite
mode set.

## 5.3bis Closed: BRST **as `book.tex` defines it** — `ChapterBookBrstYangMills`,
`ChapterBookBrstGaugeFixing`, `ChapterBookBrstInstances`

Book density
`Ω = π^μ_a ∂_μψ†_a − π^μ_a f_{abc} A_{μb} ψ†_c − (i/2) f_{abc} ψ†_aψ†_bψ_c`
with `[A,π] = i δ`, `{ψ,ψ†} = δ`:

* **`bookCCR`**, **`bookGhostCar`**, **`bookOmega`**, **`gaussGen_bracket`** (Gauss law
  derived), **`bookOmega_nilpotent`**, `bookOmega_eq_brstCharge`;
* gauge-fixing fermion `Ψ = i ψ_a A_{0a}`: **`bookGfTerm_eq`**, **`bookGfTerm_brst_closed`**;
* **Accounting identity (h, N unchanged):** **`gfFermion_eq_zero`**,
  **`bookGfFermion_eq_zero_of_Afield0`**, **`bookGfTerm_eq_zero_of_Afield0`**, instances
  **`su2_bookGfTerm_eq_zero_of_Afield0`**, **`sm_bookGfTerm_eq_zero_of_Afield0`**
  (Cadabra CHECK 29, 30a–c, exit 0); QG form **not** asserted (L11);
* cohomology `brstCohomology` well defined; observables via `brstCharge_comm_of_comm`,
  `su2_casimir_bookOmega_comm`;
* `innerDeriv_leibniz`, `su2BookAlgebra`, `smBookAlgebra`,
  **`sm_bookOmega_nilpotent`**, `su2_gaussGenPoly_ne_zero`.

*Still open here (L5–L7):* continuum local Gauss law; no FP determinant; cohomology size.

## 5.4 From the original §1 sentence, only this remains open

**Majorana masses and the see-saw (L1)** — plus everything in **§L** (L3–L11; L2 was closed on 2026-09-23g and is kept in the table
with its closing theorems).

## 5.5 Accounting identity (2026-09-23d): no extra gauge-fixing/ghost summand in `h` or `N`

**Answered.**  On `A₀ = 0` the whole BRST-exact term `{Ω, Ψ}` vanishes; `h` and `N` are
structurally complete without an extra summand.

* Lean: `gfFermion_eq_zero`, `bookGfFermion_eq_zero_of_Afield0`,
  **`bookGfTerm_eq_zero_of_Afield0`** (`ChapterBookBrstGaugeFixing.lean` §2b);
  **`su2_bookGfTerm_eq_zero_of_Afield0`**, **`sm_bookGfTerm_eq_zero_of_Afield0`**
  (`ChapterBookBrstInstances.lean` §5); audit `Work/BookBrstAudit.lean` §4b.
* Cadabra: PART F CHECK 29, 30a–c of `../unfer/docs/faris_lavine_n_sm.cdb`, exit 0,
  trailing `ALL SM ACCOUNTING IDENTITY CHECKS DONE (QYM spatial-only; QG non-ADM)`
  (`VERIFY_SM_FARIS_LAVINE.md`).
* **QYM:** Weyl gauge may use only spatial components
  (`ChapterQymTimeIndependentFlow.lean`).
* **QG non-ADM (L11):** `book.tex` ~8226–8244 — `v^μ = δ^μ_0`, ghosts constant in the
  timepiece, charge with 4D functional form; frame fermion `{G, i b_j A_0^j}` is **not**
  covered by the `A₀ = 0` vanishing
  (`ChapterQuantumGravityBrstCharge.lean`, `ChapterQuantumGravity3DGauge.lean`,
  `Book/Starobinsky.lean`).

*Still open here:* does **not** close L1–L4, L5–L10.

---

## Module map (closed boundaries → files)

| Boundary | Modules |
| :-- | :-- |
| Finite CAR / Dirac / Yukawa / spinor | `ChapterSmCarAlgebra`, `ChapterSmDiracYukawa`, `ChapterSmDiracSpinor` |
| Continuum CAR | `ChapterSmCarContinuum` |
| Gauge connection in `D` | `ChapterSmGaugeConnection` |
| Ghost / BRST (abstract + rep) | `ChapterSmBrstGhost`, `ChapterSmGaugeRepresentation` |
| Book BRST + accounting identity | `ChapterBookBrstYangMills`, `ChapterBookBrstGaugeFixing`, `ChapterBookBrstInstances` |
| `N` all summands ESA | `ChapterSmComparison` (`sm_N_positive`, `sm_N_dyn_esa`), `ChapterSmComparisonFull` (`sm_N_full_esa`) |
| Fermionic FL | `ChapterSmDiracYukawa` (`sm_fermi_fl_*`, `sm_fermi_esa`) |
| Operator-valued Yukawa coupling | `ChapterTensorKatoRellich`, `ChapterSmYukawaCoupling` (`smYukawa_h_esa`, `smYukawa_dGamma_esa`) |
| Friedrichs (bosonic, independent) | `ChapterSmHamiltonian`, `ChapterSmOuterFock` |
| Cadabra certificate (h, N, FL algebra, PART F) | `../unfer/docs/faris_lavine_n_sm.cdb`, `VERIFY_SM_FARIS_LAVINE.md` |
| Bosonic FL / L2 **closed (2026-09-23g)** | **`ChapterSmFarisLavine`** (`sm_commForm_le`, `sm_norm_le_shift`, `sm_h_esa_of_comparison_esa`) + **`ChapterSmComparisonEsa`** (`smFlN_eq_hamCoreS`, `smFlN_esa`, `sm_h_esa`), on the instrument chapters `ChapterDegSchrodingerCore`, `ChapterMollifierL2`, `ChapterConvolutionCalc`, `ChapterDegEnergyEstimate`, `ChapterDegKatoEsa`, `ChapterHermiteLadderOrder`, `ChapterHermiteGraphApprox`; audits `Work/SmFarisLavineAudit.lean`, `Work/SmComparisonEsaAudit.lean` |
| Bosonic enclosure ESA **(2026-09-24b)** | **`ChapterSmFockEsa`** (`smSectorHam_esa`, `smFockHam_esa`, `sm_dGamma_esa`) on **`ChapterYangMillsNonAbelianEsa`** (`weylPoly_esa`); audit `Work/EnclosureEsaAudit.lean` |
| Full (bosonic ⊗ fermionic) enclosure ESA **(2026-09-24c)** | **`ChapterSmFullEnclosure`** (`smFullHam`, `smFull_h_esa`, `smFull_dGamma_esa`) on `ChapterTensorSumEsa` (`essentiallySelfAdjointOn_cpairDom_esa`); audit `Work/FullEnclosureAudit.lean` |
