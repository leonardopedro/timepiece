# Current work order — one pointer per track

> **What this file is.** A routing table, not a source of truth. Every row points at
> the section of `CONSOLIDATED_PLAN.md` that the corpus currently treats as the
> authoritative work order for that track, plus the documents that section supersedes.
> Where the corpus disagrees with itself, the row says so and names the disagreement
> rather than picking a winner — picking one would make this file a second authority,
> which is the condition it exists to end.
>
> **Why it exists.** `CONSOLIDATED_PLAN.md` is ~16,400 lines of append-only dated state
> entries. Supersession is real and well marked *inside* it, but it is marked in prose
> and the entry point is stated once, in a header that has since fallen behind its own
> file. The plan's `G-T2` finding named this exactly: *"many parallel PLAN_* and REVIEW_*
> documents plus 15k-line CONSOLIDATED_PLAN. Supersession is stated in prose, not
> machine readable."* This is the machine-readable half of that sentence, kept honest
> by pointing rather than by restating.
>
> **How to read a row.** `current` is the entry point. `superseded as a reading guide`
> means the document remains the *detail* and must not be re-read as the order;
> `superseded outright` means do not implement from it.
>
> **Citations are content-based, deliberately.** Every reference below is a section
> heading or a quoted phrase, never a line number. `CONSOLIDATED_PLAN.md` is ~16,400
> lines and is append-only, but it is also *edited at the top* — fixing the stale
> header shifted every line number below it by 13 and invalidated every positional
> citation in this file at once. Line numbers into a document that grows and whose
> head gets rewritten are not a stable interface. The project already learned this
> with the Cadabra modules, where two stale line references were converted to
> content-based ones "so future header edits cannot rot them"; this file follows
> that precedent. If you need a position, grep the quoted phrase.
>
> **No Lean code is written or compiled for this file.** Every item below is a work
> order for the LLM-Lean4-specialist.

**House conventions this table inherits** (from the 21 state entries in
`CONSOLIDATED_PLAN.md`): entries are appended, never deleted; a new entry's preamble
says which prior entry it supersedes as the reading guide; status letters are **U**
unconditional, **C** conditional (hypothesis named and unproved), **N** negative or
obstructive, **B** boundary (explicitly not covered).

---

## The table

Anchor shorthand used below: **§09-25** = `CONSOLIDATED_PLAN.md` §"State of the project —
2026-09-25 (consolidated)"; **§10-04** = §"State of the project — 2026-10-04: the mass-gap
proof in Lean4"; **§10-04b** = §"State of the project — 2026-10-04b"; **§10-06** = §"State of
the project — 2026-10-06: PLAN M (planner side) landed, and the work orders its findings
create"; **§10-06b** = §"State of the project — 2026-10-06b: the sector correction — the
campaign measured a diagnostic, and §M4.9 gates §M4.3".

| Track | Current work order | Superseded as a reading guide | Superseded outright |
|---|---|---|---|
| **NS** (Navier–Stokes) | §09-25 **§5, item 3** ("NS: discharge the standing ESA hypotheses"), baseline in §09-25 **§2** (`**NS:**` row); the Lagrangian half closed 2026-10-16 — §"State of the project — 2026-10-16: the Koopman comparison `N_L = H_L² + E` is ESA — closed-by pointers" — remaining: the Eulerian square-comparison input and energy surjectivity (§"State of the project — 2026-10-16" step 4) | the 2026-09-24a…e state entries as entry points — each preamble supersedes its predecessor in place | `PLAN_LEAN_SPECIALIST_NS_FLOW.md` — self-marked `**EXECUTED (2026-08-14→16).**`; its **E.3** is marked `SUPERSEDED by the executed wave (2026-08-16)`; demoted globally by §09 route map ("supersedes the spread of routes in §9–§12 **and the per-thread plans**") |
| **QYM** (Yang–Mills) | §“State of the project — 2026-11-08f”, **S1–S2**, refines the interpretation and reuses the new source-present `ChapterYangMillsMehlerBridge` (pointwise conjugation and target signature; `L²`/core/product transfer still separate); §09-25 **§5, item 4** ("Non-abelian QYM one-particle form gap"); restated as the programme's top analytic input in §10-04b **§N2**; S2 to date: §2026-11-11g (normalization constant, `n`-coordinate norm transfer), §2026-11-11h (derivative transfer, `qymCore` domain, field-strength degree class), and §"State of the project — 2026-11-11m: the coloured actions are bounded operators" (`colourActCLM` at constant `1/2` from the pointwise identity `‖T^a v‖ = ‖v‖/2`, and `colourEnergyCLM` as `C_F` times the identity on the completion), §"State of the project — 2026-11-11n: the colour operators are a representation of su(2)" (`[A^a, A^b] = i ε A^c` on the completion without a domain hypothesis, and `Σ_a (A^a)² = colourEnergyCLM = C_F · 1`), §2026-11-11r (the norm `1/2` is **attained** — `‖A^a f‖ = ‖f‖/2` — and the exponentiated action is a one-parameter group of bounded operators at constant `2`; *not* a unitary group, see the entry's boundary note), §2026-11-11s (the field-strength merge conflict is resolved and the aggregate re-verified at 8968 jobs), and §2026-11-12a (**a genuine unitary group**, `colourGroupActHilbert a θ ∈ unitary (fundHilbert d →L[ℂ] fundHilbert d)` on the Hilbert completion, with isometry and group law; plus the module's heartbeat options scoped and the two missing inputs for the QYM flow recorded), and §2026-11-12k (**the QYM flow exists**: `dense_colouredCore` supplies the density the Stone bridge needed, `colouredHamiltonian_symmetricOn`/`colouredHamiltonian_esa` the symmetry and essential self-adjointness, so `exists_stone_flow_of_colouredHamiltonian` yields a self-adjoint extension of `H ⊗ 1 + 1 ⊗ C` and a complete unitary flow on `colourSpace N`; the colour matrix on the fundamental fibre is identified with the `hilbActCLM` operator of the `fundHilbert` completion), and §2026-11-12l (**the flow is of a determined operator**: `colourMix` is a linear isometric equivalence of `colourSpace N` for every unitary colour matrix and every `N`, and `colouredHamiltonian_extension_eq_closure` pins the self-adjoint extension to `clExt` on `clDom`, so no boundary condition is left to choose; the completion embeds the common colour fibre at `hilbFibre`, and both sides act on it through `colourVecAct`), and §2026-11-12n (**colour conjugation and the spectrum verdict**: `colourMix_clExt_colouredHamiltonian` carries the closure of `H ⊗ 1 + 1 ⊗ (U* C U)` onto the closure of `H ⊗ 1 + 1 ⊗ C` by `1 ⊗ U`; colour eigenvalues are eigenvectors of the colour half (`colourMix_colourSpread_eigenvector`); the requested closure-spectrum containment is *not* provable here and is recorded as a boundary — no unbounded spectrum, no bundled `H ⊗ 1`, no real-axis resolvent; and `ymFock_dGamma_extension_eq_closure` pins the `ChapterQymTimeIndependentFlow` generator to `clExt` under ESA), and §2026-11-12p (**the ESA reduction, the P1 bound, and the unbounded spectrum**: `ymFockCol_essentiallySelfAdjointOn_core_of_symbolGates` discharges the Fock half of the ESA of `dΓ(H₁)` and leaves exactly the three weighted symbol gates on `ymFockCol` — named, not proved; `BookProof.UnboundedSpectrum` supplies `ResolventAt`/`resolventSet`/`spectrumOf`, the Neumann transport `resolventAt_add_of_norm_mul_lt_one` and the imaginary-shift instance `resolventAt_selfAdjoint_imag`, the real-axis resolvent remaining the boundary), and §2026-11-12q (**the `L²` transfer and the resolvent identity**: `BookProof.Sm.ChapterSmGradDomTransfer` turns the pointwise gradient domination into `GradDom`, so `PotSelfBound` rests on the per-form `GradBound` table alone; the unbounded-spectrum module gains `resolvent_identity`, `resolventAt_shift` and `mem_resolventSet_of_near_imag`; the `ymFockCol` symbol gates are still open), §2026-11-12v (**gate additivity**: `WRowBound.add`, `WColBound.add`, `WCommBound.add` in `ChapterFockWeightedSchurEsa`, so the gates compose over a row split), §2026-11-13b (**C** — the row and column gates are proved for the Hermite-basis matrix `ymHermCol` at `w_k = (deg k + 1)²` (`ymHermCol_row_col_gates`), and `ymHermCol_essentiallySelfAdjointOn_core_of_commBound` leaves the commutator gate `WCommBound (ymW e) (ymHermCol e fabc) B` as its *only* hypothesis), §2026-11-13a and §2026-11-13c (the colour-decomposition entries, unrelated to the gates), and §2026-11-13d (**correction, and read this before §2026-11-13b's prose**: the band calculus cannot *supply* the commutator gate and cannot refute it either — it bounds entries only from above by `C(deg+1)²`, and no lower bound on any entry is proved, so the gate is open, not false; an earlier draft claimed sharper and was withdrawn. The gates are stated for `ymHermCol`, not for `ymFockCol`: the two matrices differ by the Gram–Schmidt versus product-Hermite basis, and no bridge between them is proved for arbitrary `e` — but the *last* step of that bridge is now a theorem: §2026-11-13g proves all three gates are invariant under diagonal phases `col'_{kj} = u_k conj(u_j) col_{kj}`, `‖u_k‖ = 1`, so once the two bases are known to differ by one phase per level the gate theorems transfer unchanged; and §2026-11-13i proves the two inputs that bridge argument was missing — the monomial–Hermite vanishing `inner_monomial_hermiteMvLp_eq_zero` and the projection form of the Gram–Schmidt vector `gramSchmidt_eq_smul_of_decomp` — then states the bridge `coreBasis e k = u_k • ψ_{e k}`, `‖u_k‖ = 1` as an explicit hypothesis and derives the gates and the ESA conclusion for the `coreBasis` matrix `ymCoreCol e fabc` (`ymCoreCol_row_col_gates`, `ymCoreCol_essentiallySelfAdjointOn_core_of_ymCommBound`, conditional on the commutator gate; **the bridge itself was still not proved** at that point), and §2026-11-13j (**the bridge is closed, with no phase at all**: degree-compatible enumerations `DegreeCompatible` give the monomial–Hermite triangularity `x^α − He_α ∈ span{deg < |α|}` from the three-term recurrence (`monomial_sub_hermiteMv_mem`, no monicity input), the decomposition `x^{e k} e^{-‖x‖²/4} = w + c • ψ_{e k}` with `c = ‖ψ_{e k}‖` (`coreFamily_sub_hermiteMvLp_mem`), the unit-modulus phase lemma `gramSchmidtNormed_eq_phase_of_decomp`, and then `coreBasis e k = hermBasisN e k` exactly (`coreBasis_eq_hermBasisN`); in the QYM module `bridgePhases_one` discharges `BridgePhases` and `ymCoreCol_essentiallySelfAdjointOn_core_of_degreeCompatible` leaves the commutator gate as the *only* hypothesis; the gate itself is unchanged — still open, still expected false for `f_abc ≠ 0`, and now refutable from a single weighted entry via `not_wCommBound_of_entry` in `ChapterFockWeightedGateSharpness`), and §2026-11-13k (**the enumeration is constructed and the quartic entry is computed**: `BookProof.DegreeEnumeration` builds degree blocks with `Fintype.ofInjective`, their cardinalities, the offsets and a rank bijection, so `exists_degreeCompatible` supplies a degree-compatible enumeration for every `0 < d` and `ymCoreCol_essentiallySelfAdjointOn_core` needs no basis hypothesis at all; `BookProof.HermiteQuartic` proves the entries `⟨ψ_{n+4}, x⁴ ψ_n⟩ = √((n+1)(n+2)(n+3)(n+4))` and `⟨ψ_{n+2}, x² ψ_n⟩ = √((n+1)(n+2))` by monic cancellation plus the vanishing lemma; and `not_wCommBound_quartic` shows that a unit quartic coefficient across a band of radius `4` defeats `WCommBound` for every `B` — so the gate's remaining obligation is the *coefficient* of a quartic monomial in `(magPoly)²`, not its magnitude; `¬ WCommBound (ymW e) (ymHermCol e fabc) B` is still unproved for every `fabc`) | `REVIEW_AND_PLAN_20260907.md` — but note §09-25 records that it *extends* `REVIEW_THREADS_20260906.md` and "supersedes nothing in" it | `PLAN_LEAN_SPECIALIST_QYM_FLOW.md` — "the continuous flow is **not yet instantiated for QYM**"; its own §11.4 "closed" claims are superseded by its later status block |
| **QG** (quantum gravity) | §09-25 **§5, item 2** ("QG: the density as a canonical variable"); record operator pinned in §09-25 **§1**; the QG-D-C branch now closes at §"State of the project — 2026-10-17: QG-D-C.1 (`hflat`) closed" (step **2a**, the assembled-side alignment, **closed 2026-10-19b** by `BookProof/Qg/ChapterQgAssembledFlatTransfer.lean` — §"State of the project — 2026-10-19b"; stated for any unitary onto the flat core, since `halfDensityUnitary` is one-dimensional) | the 2026-08-29e QG order (`**QG-ESA-C — the reassembly …**`); §"2026-10-15b"'s R1/R2 ordering for QG-D-C.1 — superseded by the factorisation route of §"2026-10-17" | `PLAN_LEAN_SPECIALIST_QG_FLOW.md` — status `executed` (2026-08-17); its densitized subject is demoted by §09-25 §1's "separate, labeled realizations — **never the record**" |
| **SM** (Standard Model) | §“State of the project — 2026-11-09c: complete SM E1 numerical assembly and joint rational Hashimoto integration” closes the E1 numerical implementation deferrals of §2026-11-09/09b; formal work remains `SM_ESA_COMPLETION_PLAN.md` **P0 → P1 → P2 → P3 → P4 → P5 → P6 → P8**, with P7 for the intended infinite-mode realization; **P0 executed 2026-11-09d** (`ChapterSmPhysicalData`, §10), **P1 executed 2026-11-09e** (`ChapterSmMatterRepresentation` + `ChapterSmFullYukawaData`, §11) **P2 executed 2026-11-09f** (`ChapterSmFullMatterHamiltonian`: the coupled inner operator on the common Mehler core, normal form action/symmetry/parity, §12) and **P3 scalar half executed 2026-11-09g** (`ChapterSmFullComparisonEsa`: `N_SM` as `−Δ_S + W` on the 43-coordinate kinetic subset, identification with `2h_B + Σq² + Σ(πⱼ²+xⱼ²) + c`, symmetry/positivity/dense core/ESA, §13), **P3 remainder + the P4 transfer engine executed 2026-11-09h** (`ChapterSmFullCoupledCore`: the coupled comparison `N_SM ⊗ I` as a Friedrichs `Comparison`, the transfer of both Faris–Lavine inequalities to the coupled space, the coupled `CoreData` with `h ⊗ I` essentially self-adjoint, and `smNormalForm_norm_le` giving the relative bound of the full normal form from per-family scalar bounds, §14), and **the P1 coefficient matrices executed 2026-11-09h** (`ChapterSmFullYukawaCoeffs`: `fockMatrix`, `fockMatrix_star`, `fockMatrix_parity`, `SmInternalData.toNormalForm` with `HermitianCoeffs`/`ParityGradedCoeffs`, §14); **the first-order per-family bounds executed 2026-11-10a** (`ChapterSmFullFamilyBounds`: `smPi_norm_le_shift`, `smMomField_norm_le_shift`/`smPos_smCoord_norm_le_shift`, `smField_norm_le_shift` all with constant 1 against `N`, `smNormalForm_norm_le_support`, and the P1 payoff `SmInternalData.toNormalForm_norm_le` — the relative bound of the P1 normal form, unconditional in `πⱼ²` because that family is zero there, §15); the commutator form of the full normal form with general coefficient matrices, the canonical placement of the Higgs components, and the reduction of the second-order family to one elliptic estimate executed 2026-11-10b (`ChapterSmFullNormalFormBounds`: `smNormalForm_commForm_le` at the shifted-graph-norm level, `SmInternalData.canonical` discharging `hpos` by `rfl` via `smCanonicalPos_harmonic`, and `pderiv_pderiv_comm`/`derOp_comp_comm`/`momOp_comp_comm`/`smPi_comp_comm` + `sq_norm_comp_le_sum` giving `smPi_sq_norm_le_kineticSum` and `smKinetic_norm_le_shift`, which leave only `‖Σₘ πₘ²x‖ ≤ c‖Nx + x‖` — the elliptic step — as the `hkin` input, §16); the same commutator bound with support-restricted family hypotheses and its P1/canonical instantiations (`smNormalForm_commForm_le_support`, `SmInternalData.canonical_toNormalForm_commForm_le` — no family and no placement hypothesis left), together with the diagonal-coefficient specialization that reaches the quadratic-form level (`coupledOp_diagonal_commForm_le`, `smHamiltonian_diagonal_commForm_le`), executed 2026-11-10c (`ChapterSmFullCommFormDiagonal`, §17); the block-diagonal generalization whose four blocks carry the four Higgs components (`blockMat`/`blockOp` with `sum_blockMat` reassembling `diag d`, the identity `blockOp_commForm_eq`, the quadratic-form bound `blockOp_commForm_le`, the norm-level sibling `blockOp_norm_le`, and `smCanonical_smPos_block_commForm_le` with no placement hypothesis left), executed 2026-11-10d (`ChapterSmFullCommFormBlock`, §18); and the identification of the SM kinetic sum with the **plain** partial Laplacian `kinPolyS smS` (`kineticSum_apply_pgLp`, `kineticSum_norm_pgLp`, `smFlN_apply_pgLp`), which **corrects §17's derivative-mismatch reading** — `kinPoly p = −Σ coreDⱼ(coreDⱼ p)` is the plain Laplacian of `pgFun p = p·e^{−‖x‖²/4}` (`lapCS_pgFun`), so `norm_kinPoly_le_shiftNorm` *is* the plain-derivative analogue — together with the interpolation half of the elliptic step (`sq_norm_le_norm_comp_mul_norm`, its ε-form `sq_norm_le_of_comp_self_eps`, `smMom_norm_le_shift_of_kineticSum`, and `smNormalForm_norm_le_of_kineticSum`, which removes §15's momentum hypothesis `hmom`), executed 2026-11-10e (`ChapterSmKineticElliptic`, §19), where §16's `hkin` is reduced to the **single polynomial inequality** `‖pgLp (kinPolyS smS p)‖ ≤ c‖pgLp (kinPolyS smS p + smPotPoly P c₀ * p) + pgLp p‖` (`kineticSum_norm_le_of_poly`); the block-diagonal operator with **non-diagonal Hermitian block interiors** (`blockOpMat T M = Σ_a T_a ⊗ M_a` with §18's `blockOp` as the diagonal case, the support condition `blockOpMat_apply_of_supp`, the weighted Cauchy–Schwarz `sq_sum_mul_le_sum_mul_sq`, and Schur's test `‖blockOpMat T M f‖ ≤ c√(ρκ)‖N⊗1 f + f‖` from `blockOpMat_norm_sq_le`/`blockOpMat_norm_le`, whose Schur sums reduce to §18's `K` for a diagonal interior — `rowSum_blockMat`/`colSum_blockMat` — plus `smCanonical_smPos_blockMat_commForm_le`), executed 2026-11-10f (`ChapterSmFullCommFormBlockHermitian`, §20); that bound instantiated at the **P1 Yukawa dictionary's four Higgs coefficient matrices** `p1HiggsMat D a` — their identification with the normal form's coordinate family (`SmInternalData.toNormalForm_coord_eq`, `toNormalForm_coord_eq_p1HiggsMat`), their Hermiticity `p1HiggsMat_hermitian`, the `ℓ¹` entry bound `fockMatrix_entry_norm_le`, and `smCanonical_smPos_p1Higgs_commForm_le` — executed 2026-11-10g (`ChapterSmFullCommFormBlockP1`, §21); and the Gårding factorization of the quartic step (`kinetic_le_shift_add_pot`, the self-bound `PotSelfBound P c₀ β`, `kineticSum_norm_le_of_pot_self_bound` with `c = 1 + β`, and `smNormalForm_norm_le_of_pot_self_bound`, which makes the whole P2 relative bound rest on `PotSelfBound` alone), executed 2026-11-10h (`ChapterSmKineticGarding`, §22); the weighted integration-by-parts identity on the Gauss–polynomial core that §22 named as missing — `gaussInt_weighted_kinPolyS`/`inner_weighted_kinPolyS` (the pairing of `Q u` with `−Δ_S u` is the weighted Dirichlet energy plus the commutator term), the pointwise form `eval_weighted_self_re`, the non-negativity `gaussInt_weighted_self_nonneg`/`inner_weighted_kinPolyS_dirichlet_nonneg` (`‖√W∇u‖² ≥ 0`), the sign `inner_weighted_kinPolyS_ge`, and the SM instance at the quartic potential (`smPotPoly_nonneg`, `sm_weighted_kinetic_ibp`, `sm_weighted_kinetic_ibp_ge`) — executed 2026-11-10k (`ChapterSmGaussWeightedIbp`, §23); the P1 Schur sums made **explicit numbers** instead of hypotheses (`p1HiggsMass`/`p1HiggsMassTotal`/`fockMass`, the radii `p1HiggsRowRadius`/`p1HiggsColRadius`, `rowSum_p1Higgs_le`/`colSum_p1Higgs_le`, and `smCanonical_smPos_p1Higgs_commForm_le_radius`), executed 2026-11-10i (`ChapterSmFullCommFormBlockP1Schur`, §24); and the operator-valued Schur test with **no block-diagonal support condition** (`weightSum`/`rowSumGen`/`colSumGen` with `weightSum_eq_of_supp` recovering §20 exactly, `blockOpMat_apply_general`, `blockOpMat_norm_sq_le_general`/`blockOpMat_norm_le_general`, `smPos_blockMat_commForm_le_general`, and the P1 payoff `smCanonical_p1Higgs_commForm_le_unconditional` with no hypothesis beyond `0 ≤ c₀`), executed 2026-11-10j (`ChapterSmFullCommFormBlockGeneral`, §25) — the quartic self-bound `PotSelfBound` itself **still open**, now with its sign identity proved (§23) *and* the gradient interpolation proved from it (§26: `dirichlet_le_weighted_form`, `∑_{j∈S}‖∇ⱼp‖² ≤ 2Re⟪Wp,−Δ_S p⟫ + ∑_{j∈S}‖(∂ⱼW)p‖²`), which does **not** close it: the cubic-term is not absorbable (`|∇W|²` has degree six, `W` degree four, so no `|∇W|² ≤ CW` exists), and the direction is wrong — the interpolation bounds `∇` by the form, while the self-bound needs `‖Wp‖` dominated by it, which §26 proves is equivalent to §19's `hpoly` (`potSelfBound_of_kinetic_bound`); **that reverse elliptic (Gårding) inequality is the next analytic input**; the P1 Schur radii are now **operator norms** instead of `ℓ¹` masses (§27: `p1HiggsOpRowRadius`/`p1HiggsOpColRadius`, provably sharper than §24's by `p1HiggsOpRowRadius_le_rowRadius`, `fockMass` gone, payoff `smCanonical_p1Higgs_commForm_le_opRadius_unconditional`), and §25's mixing-block test is applied to a family that **provably mixes** (§28: `mixYuk`, `mixYuk_unsupported` showing no `blk` satisfies §20's support condition, both general Schur sums `2`, `p1HiggsMix` for the dictionary with the mixing added); the basis mass is settled (§29: `fockBasis_norm`, `fockMass = 2 ^ 96`, so §24's radii carry no unknown factor); the dictionary's actual block structure is computed (§30: `p1HiggsMat_card_eq`, occupation number, the same blocks for all four components and hence too coarse for §20, plus `degHiggs_no_support` — a degenerate doublet for which **no** per-component `blk` exists, so §25's support-free test is necessary rather than convenient); and the reverse estimate itself is reduced to an equation (§31: `potSelfBound_one_iff_remainder`, `PotSelfBound P c₀ 1` **is** non-negativity of `‖Δ_S p‖² + 2ℜ⟪−Δ_S p, Wp+p⟫`, with the sharpest sign-route condition `potSelfBound_one_of_grad_residual` stated and **not** proved) — so `PotSelfBound` is now known to need a form-domain (elliptic-regularity) argument, which the corpus does not have, and it **stays a hypothesis**; that input is now **named** (§32: `FormDomainComparison`, the graph norm of `−Δ_S + W + 1` dominating the `H²` norm, with reductions both ways and `exists_potSelfBound_iff_exists_formDomainComparison` proving the name is *not* a weaker hypothesis, plus the coercive half `form_coercive`/`norm_le_shiftNorm_of_coercive`); the **quadratic** weight is the case the corpus already proves (§33: `reverseEstimate_harm` at `c = 3`, `selfBound_harm` at `β = 3`, `coercive_harm`, all from `norm_kinPoly_le_shiftNorm`/`norm_harmPoly_mul_le_shiftNorm`, and it does **not** transfer to the quartic `W`); and the degenerate doublet of §30 is now quantified (§34: `weightSum_degHiggs` = `4 * card`, `rowSumGen_degHiggs`/`colSumGen_degHiggs`, both sums `≤ 384`, `degHiggs_constant` = `1536`, `degHiggs_commForm_le`); the quartic analogue of the harmonic uncertainty bound is stated and only **one** direction proved (§35: `quarticUncertainty_of_gradResidual`, so the analogue is *weaker* than §31's condition; the converse needs an upper bound on `ℜ⟪Wp,−Δ_S p⟫` that §23 does not give, so **no transfer** and `PotSelfBound` unchanged); `384` is shown to be the **exact** Schur radius of the degenerate doublet (§36: `rowSumGen_degHiggs_univ`, `degHiggs_rowRadius_sharp`), so `1536` cannot be lowered by a better uniform radius; and the quadratic-weight lemmas are classified for a weight dominated by `harmPoly` (§37: potential bound, identity bound, self-bound (`selfBound_of_potBound`) and coercivity survive, the reverse `H²` estimate does **not**), together with coordinated `../unfer/docs/SM_HAMILTONIAN_AUDIT.md` **N0–N5** with the executed E1 dictionary/solver as input; the **missing upper bound of §35 is now proved as an identity** (§38: `coreD_mul_add`, `gaussInt_cpoly`, `two_re_gaussInt`, `commutator_cross_eq` and `crossTerm_eq` — `2ℜ⟪Q p, −Δ_S p⟫ = 2·weightedDirichlet − hessForm`, so the commutator term is a **Hessian weight** with no derivative left on the weight; `crossTerm_upper` is §23's missing direction from a non-negative Hessian weight, reduced to the sign of the Hessian trace by `hessForm_eq_trace`/`hessForm_nonneg` and stated at the SM weight as `sm_crossTerm_upper`; `weightedDirichlet_add`/`weightedDirichlet_one` make the weight `W+1` alone, giving the exact `residual_eq_hessForm` and `potSelfBound_one_iff_hessForm` — `PotSelfBound P c₀ 1` **is** the Hessian gap, a comparison of two quadratic forms with the degree-six density gone, still unproved), and the `ExpBounded` route to the form-domain inclusion is **checked and closed** (§39, no module: the class is scale-blind and its Kato chain is qualitative, so it supplies the graph norm's existence and ESA but not the relative bound; the quadratic case works only because of the domination `|W| ≤ λ harmW + μ` and `norm_sq_harmPoly_mul_le`, both degree-two facts), with the hypothesis now stated for readers in the book (§`The Gårding Estimate Behind the Relative Bound: Still a Hypothesis` in `Book/StandardModel.lean`, which also records that `sm_h_esa` does not need it). Reuse proved bosonic ESA; complete full chiral/four-Higgs/gauge-coordinate/spatial-Dirac assembly and its physical nested-Fock enclosure. Numerical acceptance is full-operator Hashimoto approximation; the SM-facing input that landed under a QYM heading is §2026-11-12p/§2026-11-12q (`BookProof/Sm/ChapterSmGradDomTransfer` turns the pointwise gradient domination into `GradDom`, so `PotSelfBound` rests on the per-form `GradBound` table alone). | §09-25 §5 item 6 “SM refinements”; older broad closure prose for fixed-background/two-component matter models; `HONEST_BOUNDARIES_SM.md` remains the detailed ledger with new L12 | `smComparison` as the live Faris–Lavine comparison; reduced/free/radial legacy diagnostics presented as full-SM validation; §40–§42 record the p=1 Hessian-gap test, **corrected 2026-11-11**: on the twisted core `p = 1` is the Gaussian, so the test is `E[Δ_S W] ≤ 105 + ½ E[(W+1)‖x_S‖²]` and **not** a threshold on `λ v₀²` — the earlier `λ v₀² ≥ 10 + 6 λ (+ E[G]/(8λ))` dropped the weighted Dirichlet term and is withdrawn; §42 gives the explicit gradient tail `E[G] = 3g_s²D_f + 3g_w²D_e + 12g_w²T + 12g_y²Y` (entering on the left), and the module's p=1 values are proved (`coreD_one`, `kinPolyS_one`, `hessForm_one`, `weightedDirichlet_one_one`); the data-dependent Hessian-trace sign (`80 − 8 λ v₀²` at the origin) stands |
| **RandomMap** (RH) | ⚠ **no current work order exists** — see flag **F2** | — | `IMPLEMENTATION_PLAN.md` — its own text marks the conjugate-reflection route "**Legacy / off-critical-path files (the superseded …)**"; `RandomMap_old.md` (superseded by `RandomMap.md`); `RandomMap2LegacyDraft.md` — "kept as historical material because several declarations use **obsolete APIs or state invalid proposals**"; `newproof.md` (superseded per `RandomMap.md`'s "Adaptation notes (what this plan adopts from `newproof.md`, and what supersedes it)"); `IMPLEMENTATION_PLAN_RCP.md`'s C2–C4 and Phase 3 — "C2–C4 are retained below **for historical context only** — do not implement" |
| **book** (Verso / pedagogical) | §“State of the project — 2026-11-08f: source audit, nested-Fock interpretation, and specialist handoff”, **S0** (compile/name-check this pedagogical wave; book wrapper and KaTeX), **S1–S3** (operator and OS boundaries), and **§4** (edited chapters); no compilation in this wave. Earlier closure records and the build contract below remain historical evidence. | §09-25 §5 item 1 **for the six chapters touched by §"2026-10-16"** (`Book/OdeSingularity`, `Book/ProofPlans`, `Book/NsComparisonOperator`, `Book/NsOneParticleHamiltonian`, `Book/SecondQuantizationEsa`, `Book/DiffeomorphismsGravity`) — that entry's preamble supersedes it for those chapters only; the §4 BookProof task list — "now all LANDED … kept as a record only; do not redo them" | `SPECIALIST_PLAN_REMAINING.md` — "**Plan A is fully executed.**"; `BOOK_PROOF_PLAN.md` Priorities 1–2 (COMPLETE) |
| **BookProof layout** (repo hygiene / split) | §"State of the project — 2026-10-17b: `BookProof/` split plan and the redundancy / legacy / dead-end inventory" + `BOOKPROOF_SPLIT_PLAN.md` — phases 0–4 with per-phase acceptance (orphan `PartN` deletion → foldering independent parts → folder the core after the cross-import matrix → renames → perpetual gates); execution is the LLM-Lean4-specialist, compile per phase; **2026-10-18 addendum**: Phase 1.5 (convert 91 downloaded Prove2.me proofs into `Toolbox/Prove2me/`), §6 download inventory, §7 missions our corpus can feed, §8 sibling-project imports (70 more downloads for `../unfer` + `../dynamic-arctic`; `../australVM`/`../emthin` not present in this workspace — earmarks deferred) — pointers in `CONSOLIDATED_PLAN.md` §"2026-10-17c"/§"2026-10-17d"; **executed 2026-10-18** (§"State of the project — 2026-10-18: Prove2.me downloads converted …", `BOOKPROOF_SPLIT_PLAN.md` §9): Phases 0, 1, 2 done and green; Phase 1.5 landed in `converted/` (all 161 manifest solutions compiled after the platform library was supplied, §"2026-10-19"); **2026-10-19b**: Phase 0 residue (9 empty stubs removed), Phase 2.2b (the 237-module residue foldered by reading, `BOOKPROOF_PHASE2B_MOVES.md`) and Phase 3 (Weyl `Sl2`→`SL2Algebra`; other renames declined by cite density) executed — §"State of the project — 2026-10-19b" | — (no row superseded; the plan file is the detail, the §"2026-10-17b"/§"2026-10-17c" entries are the entry points) | — |
| **mass-gap** | §10-06b (the sector correction; **M4.9 gates M4.3**) → work order **§M4.9** in `../unfer/PLAN_MASS_GAP.md` §7; the proof itself remains §10-04 **§M4** | §13 (T1–T12, "the Lean4 plan"), `MASS_GAP_CERTIFIED.md`, `unfer_contracts/MASS_GAP_SPEC.md`, `unfer_contracts/MASS_GAP_REGENERATION.md` — §10-04 consolidates and supersedes all four "as a reading guide"; they "**remain the detailed record**"; §10-06's campaign tables are read under §10-06b (diagnostics) | — (§13.1's honesty boundaries and §13.6's definition of done still stand) |
| **math28** (`math/` results as hypotheses) | §"State of the project — 2026-10-20: `math28/` — `math/` results as named hypotheses on Lean v4.28.0; BookProof import graph repaired" + `math28/README.md` — named hypotheses only, never theorems of this repo | — | the 2026-10-20 request to compile `math/` wholesale on v4.28.0 (withdrawn; copy removed) |
| **BayesianTransformer** (nGPT geometry / SG-pCNL) | §"State of the project — 2026-10-21: `BayesianTransformer/` imported (uncompiled), `Book/BayesianTransformer.lean` read pedagogically, final-Hamiltonian convention re-verified, `../unfer/pcnl` comparator milestone" — work order §4 steps 0–3 (name-level check of the import, `#check` smoke block into the Book chapter, bridge lemmas under the convention, `DOC_INDEX` regen); **plus** §"State of the project — 2026-11-08b: `K_drift` for a polynomial potential — the composition with the letter `∂ⱼ`, its ladder-word family, and the band of `polyMul` (`FockLangevinOperator` §9.6–§9.8)" — the Module 3 operator closure: `diffHermite` (the letter `∂ⱼ = (aⱼ − aⱼ†)/√2`), **`polyDrift`** as `−Σⱼ polyMul (∂ⱼ Φ) ∘ diffHermite j` with its ladder-word family (`polyDrift_eq_ladderWords`, `polyDrift_eq_hopWords`), the band of the polynomial operator (`polyMul_band`: degree `≤ K` maps `{N ≤ N₀}` into `{N ≤ N₀ + K}`), and the band of the drift itself (**`polyDrift_band`**, §7 addendum: `K_drift` has band `K`, the derivative's loss and the letter's gain cancelling); its §6 lists what stays open (the norm estimate behind `DriftFormBound`, `K_reject`); **plus** §8 of that entry — `FockLangevinOperator` §9.9–§9.10: the drift's `ℓ¹` estimate (`coreL1`, `hopStep_l1_le`, `hopWord_l1_sector`, **`polyDrift_l1_le`** with the explicit sector constant `driftL1Bound`) and the pCNL Hamiltonian built from `polyDrift` instead of `driftOpCoeff` (**`pcnlPolyHamiltonian`**, **`pcnlPolyHamiltonian_band`**, `polyDrift_linear`), plus §10 of that entry — `FockLangevinOperator` §10: the coordinates of one ladder letter (`hopStep_coord_lower`, `hopStep_coord_raise`), the letter norms (`coreNormSq_hopStep_lower`: `‖a_j c‖² = ∑ₙ n_j‖c n‖²`; `coreNormSq_hopStep_raise`: `∑ₙ (n_j+1)‖c n‖²`) with their mode sums, and the **`oscillator_identity`** `∑_j (‖a_j c‖² + ‖a_j† c‖²) = 2⟪c,Nc⟫ + d‖c‖²`, and **`driftFormBound_holds`** — `DriftFormBound` itself proved in §11 of the chapter (`driftOpCoeff_form_bound`: Cauchy–Schwarz in the core pairing `norm_corePair_le` plus the mode-index Cauchy–Schwarz `sum_coreNorm_hopStep_le`, and `two_mul_le_add_div` giving the plan's constant `B²d/(2δ) + Bd`), leaving only `K_reject` open, because §12 of the chapter now supplies the coefficient family (`driftWeight`/`driftScale`, `driftOperator β σ Φ = (β²σ²/2) • polyDrift Φ`, `driftOperator_linear`, and `driftOperator_form_bound_eps` with `M_ε = K/ε`) and §13 the semiboundedness corollary (`corePair_numberOp_re`, `semibounded_of_form_bound`, `numberOp_add_driftOpCoeff_semibounded`, `pcnlDrift_semibounded_eps`: `N + K_drift` bounded below by a constant of order `ε⁻²`), the remaining analytic input being the core-side realization of `∇Φ_ε` as `polyMul (∂ⱼΦ_ε)`; **and** §13 of that entry — the hypothesis's `M_ε = K/ε` itself: `BayesianTransformer.epsProj_fderiv_le` proves `‖∇(g ∘ Ŵ)‖ ≤ 2K/ε` on `‖W‖ ≥ ε` for the additive normalization `Ŵ = W/(‖W‖ + ε)` (`epsProj`, `epsProj_fderiv_opNorm_le`), and `driftScale_eps_arch` reads it into the drift's `B = β²σ²K/ε`; §9 of the same entry adds `scripts/test_check_links.py`, the regression tests for the `check-links` tracked-vs-ignored scope; **and** §14 of that entry — `FockLangevinOperator` §14: the gradient bound `hgrad` is a *sector* statement, not a global one (`polyMul_X_unbounded` refutes the global form, since `xⱼ` raises the occupation and `‖xⱼ eₙ‖` grows like `√n`), while `polyMul_norm_sector_le` and `gradSectorBound` prove it on `{N ≤ N₀}` with an explicit constant (`coreNorm_add_le`, the sector letter norms, `coreNorm_mulHermiteList_sector_le`), so `polyDrift_form_bound_sector`, `driftOperator_form_bound_sector` and `pcnlDrift_semibounded_sector` are §11–§13 with no hypothesis at all on each truncated sector; **and** §15 of that entry — `FockLangevinOperator` §15–§16 close the two inputs §14 still listed: the Metropolis filter `K_reject` is `rejectOp ρ`, a *diagonal* multiplication by an acceptance probability (`rejectOp_apply`, `rejectOp_single`, `rejectOp_comp`) with band `0` (`rejectOp_band`), a contraction for `ρ = metropolisReject ΔV = min 1 (exp(−ΔV))` (`coreNorm_rejectOp_le`), and nonnegative in the form (`re_corePair_rejectOp_nonneg`), so the assembled step `pcnlFull = N + K_drift + K_reject` keeps §14's band (`pcnlFull_band`) and lower bound (`pcnlFull_semibounded_sector`, `pcnlFull_metropolis_semibounded`); and the coefficient-level comparison with the architecture's `M_ε = 2K/ε` is a theorem (`coeffMass`, `coeffMass_pderiv_le`: `coeffMass (∂ⱼΦ) ≤ deg Φ · coeffMass Φ`, so `GradCoeffBound` holds for every `Φ`; `driftScale_gradSectorBound_le_eps`: `GradCoeffBound Φ_ε (2K/ε)` gives `B ≤ β²σ²K/ε` times the level factor `d·(2√(N+2+deg Φ))^{deg Φ}`, with `driftScale_gradSectorBound_le_coeffMass` the hypothesis-free case); **and** §16 of that entry — the reading closed in `BookProof/MCMC/CoeffMap` (the coefficient map `linCoeff F x j = D F(x)[eⱼ]`, `linPart`, `pderiv_linPart`, and **`gradCoeffBound_epsProj`**: `epsProj_fderiv_le`'s `‖dŴ‖ ≤ 2K/ε` gives `GradCoeffBound (linPart (g ∘ Ŵ) W) (2K/ε)` with no hypothesis, at the linear order that a first-derivative bound controls; `eval_pderiv_norm_le_coeffMass` puts the two sides in the same units), plus `FockLangevinOperator` §18–§19 — the plan's diagonal `P₀ = ρ^N` (`baseOp`, band `0`, `baseOp_vac` fixes the vacuum with `λ_0 = 1`, `coreNorm_baseOp_sector_le` contracts the rest by `ρ`), the drift's norm constant `driftStepBound`, the assembled operator **`pcnlKernel = P₀ + K_drift + K_reject`** with `pcnlKernel_band` / `coreNorm_pcnlKernel_le` / `coreNorm_pcnlKernel_sector_le`, the iterate band `pcnlKernel_iter_band` and product bound `coreNorm_pcnlKernel_iter_le`, and the convergence that holds — `tendsto_iter_baseOp`: `P₀`'s iterates converge to the invariant state at rate `ρ`; the full step's convergence is stated as needing the Markov structure (positivity, `P 1 = 1`) the core lacks  ; **and** §17 of that entry — `FockLangevinOperator` §20, the stochastic split: the Metropolis complement `rejectComplement ρ = 1 − ρ^N` makes the diagonal half the identity (**`baseOp_add_rejectOp_complement`**: `P₀ + K_reject = 1`, so `pcnlKernel = 1 + K_drift` via `pcnlKernel_complement`), which is the normalisation `P 1 = 1` exactly; the diagonal half is positive (`re_baseOp_nonneg`, `re_rejectOp_nonneg`) and `ℓ¹`-bounded (`coreL1_baseOp_le`, `coreL1_rejectOp_le`), with `coreL1_pcnlKernel_complement_le` showing it contributes no `ℓ¹` contraction — so the remaining input for a convergence theorem is the drift's *sign* (its negative part), not the normalisation; **and** §18 of that entry — `FockLangevinOperator` §21 computes that sign and finds it points the wrong way (`polyDrift_X`, `driftOperator_X`, `drift_X_single_eq`, and **`coreL1_single_lt_add_drift_X`**: the linear potential's drift *adds* mass on every basis vector, `ℓ¹(e_n + K_drift e_n) = 1 + (β²σ²/2)·2⁻¹ᐟ²·(√(nⱼ+1) + √(nⱼ))`), so a weighted `ℓ¹` is needed rather than a further norm; and `BookProof/MCMC/PositivityCone` (§22) proves the convergence in the cone model — `P 1 = 1` (`step_one`), cone and mass preservation (`step_nonneg`, `mass_step`), the Doeblin contraction `osc (P f) ≤ (1 − (m+1)δ)·osc f` (`osc_step_le`), **`tendsto_iter_step`** (every starting density converges to the invariant state `mass f / (m+1)` at rate `1 − (m+1)δ`) and its instance `tendsto_iter_uniformStep`; the Module 4–5 gap hypotheses are now cited from §18 (`module45_hypotheses_cited`, `module45_iterate_bound`); **and** §19 of that entry — §23 of the same module drops the uniform-target restriction: with a prescribed target `π` (`Target`), the Doeblin condition `ε π b ≤ Q a b` (`Minorant`) and stationarity (`Stationary`), the `ℓ¹` mass contracts by `1 − ε` (`sum_abs_sub_minorant`, `l1_apply_le`, `l1_apply_iter_le`) and **`tendsto_iter_target`** gives `‖f Qⁿ − π‖₁ ≤ (1 − ε)ⁿ‖f − π‖₁ → 0`, coordinatewise in `tendsto_iter_target_pointwise`; the concrete `targetKernel ε π` instantiates it (`targetKernel_rowStoch`, `targetKernel_minorant`, `targetKernel_stationary`, `tendsto_iter_targetKernel`) and `uniformStep_eq_targetKernel` identifies §22's kernel as the flat-target special case; **and** §20 of that entry — §24 of the same module derives §23's Doeblin condition for the Metropolis kernel: `mhKernel q π` (acceptance `mhAcc π a b = min 1 (π b/π a)`) is row stochastic by construction (`mhKernel_rowStoch`), satisfies `Minorant (mhKernel q π) π (δ/supv π)` when every proposal entry is at least `δ` (**`mhKernel_minorant`**, via `div_supv_mul_le` and `mul_mhAcc`), is reversible (`mhKernel_detailed`) and stationary (`mhKernel_stationary`), so **`tendsto_iter_mhKernel`** gives `ℓ¹` convergence to `π` at rate `1 − δ/supv π`; **and** §21 of that entry — §25 of the same module removes the target from the constant: `supv π ≤ 1` on a probability target (`target_le_one`), so the minorant is the proposal's floor `δ` (**`mhKernel_minorant_one`**) and the rate is `1 − δ` (`tendsto_iter_mhKernel_delta`, `l1_iter_mhKernel_le`), with the concrete symmetric proposal `uniformStep t` giving **`tendsto_iter_metropolis_uniformStep`** at rate `1 − t` for any probability target (`l1_iter_metropolis_uniformStep_le`); what remains is the single number `δ`; **and** §22 of that entry — §26 of the same module gives Module 5's total variation from the same contraction: `tv` is half the `ℓ¹` distance (`tv_le_l1`), `l1_iter_target_le` is the iterate bound and **`tendsto_iter_target_tv`** gives `tv (f Qⁿ) π → 0` at the Doeblin rate (`tv_iter_le`), with the Metropolis instances `tendsto_iter_mhKernel_tv` (rate `1 − δ`) and `tendsto_iter_metropolis_uniformStep_tv` (rate `1 − t`); **and** §23 of that entry — §27 of the same module computes the floor `δ` for the occupation model: the pCN noise is the binomial thinning (`binomPmf`, `pcnRefresh`, `binomPmf_sum` via `add_pow`), every entry is at least `c ^ m` for `c = min ρ (1 − ρ)` (**`binomPmf_floor`**, `pcnFloor_pos`), and the independent proposal needs the independence sampler's filter (`indAcc`, `indKernel`, `mul_indAcc`, `indKernel_detailed`, `indKernel_stationary`), whose minorant is that floor alone (`indKernel_minorant`), giving **`tendsto_iter_pcnRefresh`** at rate `1 − (min ρ (1 − ρ)) ^ m` (`tendsto_iter_indKernel_tv` for total variation); what remains is the weight-space Gaussian increment's floor.; **and** §24 of that entry — the new chapter `BookProof/MCMC/PCNGaussianFloor` proves the weight-space floor as a density inequality: `pcnQuad`/`pcnDensity`, the box bound **`pcnQuad_box_le`** (`≤ d(R(1+ρ))²`), **`pcnDensity_floor`** and **`pcnGaussian_floor`** (`(2πs)^(−d/2)·exp(−d(R(1+ρ))²/s)` with `s = 2σ²(1 − ρ²)`), positive by `pcnGaussian_floor_pos`; the kernel-level passage on `ℝ^d` is not claimed; **and** §25 of that entry — `FockLangevinOperator` §21.5 closes the weighted-`ℓ¹` route: `coreW1 w c = ∑ₙ w n·‖c n‖` (`coreW1_one` for the flat `w ≡ 1` mass), the diagonal acts on the weight as `w ↦ w·ρ^{natDeg n}` (`coreW1_baseOp`) so in `wInv ρ n = (ρ^{natDeg n})⁻¹` it cancels exactly (**`coreW1_baseOp_wInv`**: `coreW1 (wInv ρ) (P₀ c) = coreL1 c`, with `coreL1_le_coreW1_wInv`), while the drift grows the weighted mass on every basis vector for *every* strictly positive weight (`coreW1_single_lt_add_drift_X`), with the excess explicit in the cancelling weight (**`coreW1_wInv_add_drift_X`**: `1 + q(√(nⱼ+1)/ρ + ρ√(nⱼ))`, plus `natDeg_lowerIdx`), so **`no_weighted_nonexpansive`** — no weight makes `1 + K_drift` nonexpansive, and the remaining pCNL items are the operator's own gap and the continuum passage of §24; **and** §26 of that entry — `FockLangevinOperator` §21.6 computes the quadratic potential `Φ_λ = (λ/2)∑ⱼ xⱼ²` (the equality case of `Hess Φ = λ·I`) and finds the Hessian in the constant, not the gap: `a_j†` is the right adjoint of `a_j` (**`corePair_hopStep_adjoint`**), the double letters cancel in real part (`corePair_double_raise_re_eq`), so `Re⟪c, x_j∂_j c⟫ = −½‖c‖²` (`re_corePair_mulHermite_diffHermite`) and `Re⟪c, Σⱼ x_j∂_j c⟫ = −(d/2)‖c‖²`; with `pderiv_quadPotential` giving `∂ⱼ Φ_λ = λxⱼ` and `driftOperator_quadPotential` giving `K_drift = −λ Σⱼ xⱼ∂ⱼ`, **`re_corePair_quadHamiltonian`** makes the form `numberForm + E₀‖c‖²`, `E₀ = (β²σ²/2)·λd/2`, and **`quadForm_gap`** the gap `1` off the vacuum (sharp, `quadForm_degree_one`; bottom `quadForm_vac`) — so `pcnl_spectral_gap_of_hessian`'s `γ = λ` is the wrong target for this form; **and** §27 of that entry — `FockLangevinOperator` §21.7 composes the drift for an affine-gradient potential `Φ = Φ_λ + Σⱼ aⱼxⱼ` (the class a Hessian bound describes): `polyDrift_add` and `driftOperator_add` split it into §26's exact quadratic form (constant `E₀ = (β²σ²/2)·λd/2`) and §12's `driftOperator_linear_form_bound` (cost `δ·⟪c,Nc⟫ + C_δ‖c‖²`), so **`re_corePair_affineHamiltonian`** gives `(1 − δ)·⟪c,Nc⟫ + (E₀ − C_δ)‖c‖²` and `affineForm_gap` reads it off the vacuum — the Hessian's `λ` entirely in the constant, the number-form coefficient `1 − δ`; the open items are the `L²(π)`-side gap for a general `V_eff` and the continuum passage; **and** §28 of that entry — `FockLangevinOperator` §21.8 optimises §27's free `δ` and closes P3's question: `√(2A) ≤ δ + A/(2δ)` (`sqrt_two_mul_le_add_div`) yields **`affineForm_coefficient_le`** — the coefficient of `‖c‖²` is at most `1 + E₀ − driftScale·d − driftScale·√(2d)` for *every* `δ > 0`, so the free parameter is spent against itself and minimising over it cancels it — hence when `1 + E₀ < driftScale·(d + √(2d))` the best constant is negative (`affineForm_best_coefficient_neg`), and at the implementation's numbers (`β = 0.3`, `σ = 0.35`, `M = 2·10⁶`, `d = 16672`, `λ = 1`) it is below `−10⁷` (`affineForm_architecture_coefficient`): the relative-form bound is a semiboundedness licence for `pcnlHamiltonian`, not a gap certificate, and the `L²(π)`-side gap for a general `V_eff` and the continuum passage remain the open items; **and** §29 of that entry — three items: `FockLangevinOperator` §21.9 formalizes the `L²(π)` side (`Veff`, `genDiff`, and **`genDiff_groundScale`**: `A(e^{Φ/2}g) = e^{Φ/2}(g'' − V_eff g)`, so the generator on `L²(π)` is similar to `Δ − V_eff` through the ground state; `Veff_quadOne` for `Φ_λ`; and the oscillator in letters, **`re_corePair_oscillatorOp`** and **`re_corePair_oscFreqOp`** with form `ω·numberForm`, so **`oscFreqOp_gap`** is the gap `ω = λ/2`), `PCNGaussianFloor` §2 turns the density floor into a measure minorant on the box (**`pcnMeasure_minorant`**, **`pcnMeasure_floor`**: `volume.withDensity q ≥ F · volume.restrict box`, uniformly in the starting point), and `pcnl.md` carries the track's honest boundary as a single two-list summary — proved (structure, semiboundedness, the finite-chain convergence, the closed weighted-`ℓ¹` route, the Hessian in the constant, the `L²(π)` identity and oscillator, the two floors) and not claimed (the core's own gap, a Hilbert-space model, the continuum chain and its rate, the infinite-dimensional Fock space, the implementation); still open are the `L²(π)` measure space and the rate of the floor; **and** §30 of that entry — the three items §29 left: `FockLangevinOperator` §21.10 lifts the identity to `ℝ^d` (**`genDiffD_groundScale`**, `coordDeriv`/`coordDerivTwo`, `genDiffD`, `VeffD`); the new chapter `GroundStateConjugation` proves the algebraic content of the spectral step (**`rayleigh_groundState`**, `flatPair_groundState`, `rayleigh_range_groundState`, and **`sInf_rayleigh_eq`**: a ground-state conjugation preserves the Rayleigh quotient and its infimum over the ground-state-orthogonal subspace); and `PCNGaussianFloor` §3 names the continuum target (`pcnProposalMeasure`, `pcnTargetMeasure`, `pcnTargetMeasure_le_smul`) and proves **`pcnDoeblin`** (`(F/B) • π ≤ P(x, ·)` on the box, for every starting point) — `Minorant` on `ℝ^d`; **and** §31 of that entry — `VeffD_quadSum` (`V_eff = ¼λ²‖x‖² − ½λd` for the quadratic potential, from the exact coordinate slice) and the Metropolis acceptance carried through the pCN density (`pcnAccept_floor`, `pcnMetropolis_floor`, `pcnMetropolis_minorant`), so the Doeblin condition holds for the adjusted step as well; and **§32** — the iterate `pcnIter` on `ℝ^d` with **`pcnIter_rate`** (`(1−(1−c)^n)·μ(A) ≤ (pcnIter K n x)(A)`), **`exists_split_of_minorant`** and **`pcnIter_rate_of_minorant`**, so the minorant alone yields the rate.  and **§33** — the Metropolis step itself as a probability measure (`pcnProbabilityStep`, `pcnProbabilityStep_univ`) with the rate attached (`pcnProbabilityStep_rate`).  And **§34** — the increment's mass on the line (`lintegral_exp_neg_sq_div`, `pcnGaussMass_one`), the first exact normalisation.  And **§35** — the increment in `d` dimensions (`pcnGaussStep`, `pcnGaussStep_univ`, `pcnExp_factor`), mass `1` in every dimension.  And **§36** — the Fubini identification (`pcnGaussMass_d`, `pcnGaussMass_quad`: the increment's mass is `1` in `pcnDensity`'s own form), hence accepted mass at most `1` (`pcnMetropolisStep_mass_le_one`) and the Metropolis step with its rejection atom as a probability measure with no mass hypothesis (`pcnAbsorbingStep_univ`, `pcnAbsorbingStep_rate`).  And **§37** — the Doeblin minorant for that step (`pcnAbsorbingStep_minorant`: `(mF/B) • π ≤ pcnAbsorbingStep` on the box), with the caveat that the floor is a box statement while the contraction quantifies over every starting point.  And **§38** — the box's volume and the return mass (`pcnBox_volume`, `withDensity_box_ge`, `pcnAbsorbingStep_box_ge`): the step returns at least `F·(2R)^d` of mass to the box, the second factor of a two-step argument for a global minorant.  And **§39** — the small-set reduction (`bind_minorant_of_set`, `pcnAbsorbingStep_twoStep_minorant`)
  together with the negative finding that closes §38's sketch: the return mass is box-local, so the
  two-step composition is a reduction with an explicit hypothesis (a multi-step confinement
  estimate), not a consequence of §37–§38.  And **§40** — the two items that followed: the per-start
  confinement estimate (`pcnQuad_le_of_mem_box`, `pcnReturnConst`,
  `pcnProposalMeasure_box_ge_start`, `pcnAbsorbingStep_box_ge_start`: return mass decaying like
  `exp(−2ρ²‖x‖²/s)`, so §39's hypothesis holds at every start, uniformly only on balls) and
  reversibility (`pcnPrior_mul_density_comm`, `pcnMetropolisDensity_detailed`), which finds that the
  reversible reference is `τ · pcnPrior` and not `τ` — §3–§39's `pcnTargetMeasure R τ` is the
  symmetric-proposal target, and `τ` must be read as a likelihood against the Gaussian prior.  Then
  confinement (`pcnAbsorbingStep_confined`, `pcnIter_confined`, `pcnIter_confined_ball`,
  `pcnBallConst`, `pcnAbsorbingStep_box_ge_ball`, `pcnAbsorbingStep_twoStep_minorant_ball`): the
  accepted part lives in the box and the rejection atom at the start, so one step from `x` never
  leaves `box ∪ {x}`, every iterate satisfies `‖z‖² ≤ max (dR²) ‖x‖²`, and the `exp(−2ρ²‖x‖²/s)`
  constant becomes a single number on each ball of starts — uniform on balls, not on `ℝ^d`, which is
  the best available since the constant genuinely decays; and the prior-referenced restatement
  (`pcnPriorTarget`, `pcnAbsorbingStep_minorant_prior`, `pcnAbsorbingStep_rate_prior`), where the
  ceiling and the target are about `τ · pcnPrior` while the acceptance floor stays about `τ`; and
  stationarity (`doeblinStep`, `bind_doeblinStep_stationary`: detailed balance plus a forward-mass
  bound give `π.bind K = π` by Tonelli on the symmetric joint density; `pcnPriorTarget_stationary`
  is the pCN instance, and `pcnAbsorbingStep_rate_prior_of_stationary` drops `hstat` from the rate).
  The 2026-11-11 entry closes the three inputs that row listed: the step's measure-valued
  measurability (`measurable_withDensity_uncurry`, `measurable_pcnMetropolisStep`,
  `measurable_rejection`, `measurable_pcnAbsorbingStep` — every `hmeas` hypothesis becomes
  `Measurable τ`), the minorant's constants at a Gaussian likelihood (`pcnGaussLike`,
  `pcnGaussLike_mul_pcnPrior_le_one` for `B = 1`, `pcnGaussLike_floor` for `m = exp (−β dR²)`,
  `pcnAbsorbingStep_minorant_prior_gaussLike`), and the reference's "normalisation" — which is *not*
  mass one (`pcnPriorMass` is the box integral `∫ τ · pcnPrior`, finite by `pcnPriorMass_le` and
  positive by `pcnPriorMass_pos`), so the rate is stated for the normalised `pcnPriorProb` with
  `IsProbabilityMeasure` proved (`pcnPriorProb_stationary`, `pcnPriorProb_minorant_of_target`,
  `pcnAbsorbingStep_rate_prob`).  What remains open is the *value* of that mass.  Its predecessor is the 2026-11-08 entry (`§9.3–§9.5`: the mode calculus, `polyMul_mul`, the derivative side), and the 2026-10-21 steps 0–3 are **not** superseded and remain open | `pcnl.md`'s Module 3 status prose — "the induction that *feeds*" §9.2, "the derivative polynomials `∂_j Φ` … not carried out here", and the operator composition with `∂ⱼ` — is superseded as a reading guide by the 2026-11-08 and 2026-11-08b entries for the pCNL/Module 3 track only; the rest of `pcnl.md` (Modules 1–2, 4–5, the review of the empirical claims) stands; the 2026-11-08f entry additionally supersedes the 2026-10-21 and 2026-11-08/08b–e *interpretive* orders (their theorem statements and build reports remain the historical record) and withdraws three readings — the Gaussian pCN identified with spherical Brownian motion, a scalar `b` substituted for a variable loss gradient, and the differential drift treated as an exact finite-step kernel correction | — |
| **OS / Euclidean reconstruction** | §“State of the project — 2026-11-08f: source audit, nested-Fock interpretation, and specialist handoff”, **§2, S3**; `cftproof.md` supplies the detailed positive-time construction. Reuse the conditional multiplier self-adjoint generator and norm-gap equivalence; construct the physical representation and full ground projection. | Older assertions that spectral/Stone machinery is absent, or that a `MulModel` hypothesis constructs the interacting theory | Two-sided contractive self-adjoint transfer groups as a nontrivial Euclidean theory |
**Priority decision (2026-11-11): the QYM row before the SM's remaining analytic row.**

The SM thread has been driven to a definite stopping point and should not continue on the same
rail. The reasons, in order:

1. **The SM's open item is not an SM item.** `PotSelfBound` (§22), `FormDomainComparison` (§32)
   and the Hessian gap (§38) are three spellings of one missing input: a graph-norm domination
   for `−Δ_S + W + 1` with a quartic weight. §39 closed the `ExpBounded` route to it, and §43
   closes the "choose a better test function" route: the sharp tests are spread-out rescalings
   that leave the polynomial core, and the sharpest closed-form rung (`p = x₀`) is only
   `0.944` against the boundary value `1`.
2. **QYM's gap is the same input on a smaller object.** The one-particle form gap is named the
   programme's top analytic input (§10-04b §N2, §09-25 §5 item 4). It has one particle, no
   Yukawa dictionary, no 49-form coefficient bookkeeping, and the same structure: dominate a
   potential by the graph norm of `−Δ + W + 1`. A method found there transfers to the SM; a
   method found in the SM's 49-form setting does not transfer back cheaply.
3. **The SM's numerical and structural half is complete and does not need this.** E1 assembly,
   the P1 dictionary, the P2 coupled transfer and the P3 scalar half are landed; what remains is
   P4–P8, all of which consume the same elliptic input rather than supplying it.
4. **Parking is explicit, not implicit.** The SM thread reopens when the form-domain input
   lands; §43.5 records the degree-one test `ρ(x₀) ≤ 1` as the first check any new candidate
   must pass, so the resumption point is written down.

Nothing else changes: the RH analytic `sorry` rows stay parked (flag **F2**), and the QG / NS /
book rows keep their recorded orders. This is a prioritization, not a claim about either
estimate.

**The single most load-bearing supersession sentence for the book track** is buried inside
the 2026-08-27 wave block, not in any header: *"One plan that supersedes the per-thread
plans for future work"* — it absorbs everything still open from `BOOK_PROOF_PLAN.md`,
`PLAN_LEAN_SPECIALIST_UNPROVED.md`, `SPECIALIST_PLAN_REMAINING.md`,
`PLAN_LEAN_SPECIALIST_COHERENT.md`, `PLAN_A_BOOK_FORMALIZATION.md`,
`PLAN_B_PROSE_VERIFICATION.md`, `SINGULARITY_DETECTION_PLAN.md` and
`PLAN_A_EXECUTION_REPORT.md`. It sits inside the 2026-08-27 wave block, not in any header.

---

## Recent board entries — per track

> **What this section is.** The table above says *which document is authoritative*.
> This one says *what the shared board currently records* for the same track, so
> a specialist can see recent observations without reading the whole 16k-line plan.
> Entries are cited by **board cursor**, which is a stable monotonic id, not a line
> number — the same content-based discipline the rest of this file uses.
>
> **Where they come from.** `BOARD.ndjson`, the board's NDJSON snapshot, read by
> `scripts/board_rollup.py`. `Board::write` assigns no timestamp, deliberately: adding
> wall-clock would make the log non-deterministic, and the cursor ordering is what
> everything depends on. A month therefore comes from the snapshot's mtime unless a
> writer supplies `ts`.
>
> ⚠ **`BOARD.ndjson` is currently a seed corpus**, transcribed from the plan entries
> and flags this file already cites — not observations captured from live agent runs.
> It exists so the rollup path is exercisable and auditable before any agent writes
> to it. Treat these as restatements, not as new evidence; when real workers write
> entries they will carry the same shape and the same cursors continue.

| Track | Recent board entries |
|---|---|
| **NS** (Navier–Stokes) | cursor 2 `FACT` — `not_nsEnergy_surjective` refuted, so `nsKoopman_esa_of_energy_comparison` is vacuous as stated; cursor 3 `CLAIM` — `unfer_contracts/prob_kernel`, NS derivative fixing |
| **QYM** (Yang–Mills) | §“State of the project — 2026-11-08f”, **S1–S2**, refines the interpretation and reuses the new source-present `ChapterYangMillsMehlerBridge` (pointwise conjugation and target signature; `L²`/core/product transfer still separate); cursor 4 `FACT` — the one-particle form gap is the programme's top analytic input; cursor 5 `FAIL` — `PLAN_LEAN_SPECIALIST_QYM_FLOW.md` §11.4 "closed" is superseded by its own later status block |
| **QG** (quantum gravity) | cursor 8 `FACT` — the density is a canonical variable; the record operator is pinned separately and is **never** the density |
| **SM** (Standard Model) | cursor 9 `CLAIM` — `HONEST_BOUNDARIES_SM.md`, fermionic completion boundary ledger; cursor 10 `FAIL` — `smComparison` as a comparison operator is refuted by the 09-23f wave though still defined and proved positive |
| **RandomMap** (RH) | cursor 1 `FAIL` — `AGENTS.md` still lists three already-proved items as next (see **F2**). No `CLAIM` recorded: this is the one track with no order and nobody has taken it |
| **book** (Verso / pedagogical) | §“State of the project — 2026-11-08f: source audit, nested-Fock interpretation, and specialist handoff”, **S0** (compile/name-check this pedagogical wave; book wrapper and KaTeX), **S1–S3** (operator and OS boundaries), and **§4** (edited chapters); no compilation in this wave. Earlier closure records and the build contract below remain historical evidence. |
| **mass-gap** | cursor 11 `FACT` — the order is §M4 in the 10-04 entry; §13 and `MASS_GAP_CERTIFIED.md` remain the detailed record but are superseded as a reading guide |

**Rolling up.** `python3 scripts/board_rollup.py --list-months` shows what is present;
`--month YYYY-MM --dry-run` prints the block without writing. The script **appends only**
— `CONSOLIDATED_PLAN.md` is append-only by house rule and this one never edits it — and
refuses to write a second rollup for a month that already has one, because a duplicate
would be indistinguishable from a correction. Use `--force` to append anyway; the earlier
block is kept rather than replaced. `FAIL` entries sort first, `OBSERVED` last and
usually not at all: they are conclusions-free notes, and surfacing them would bury the
entries that tell a specialist something.

---

## Repo hygiene — the 2026-11-11 merge and the ignore scope

Not a track and not a contradiction, but it changed the shape of the tree, so it is
recorded here rather than left to `git log` archaeology.

**The merge (`32a3647`).** Remote `main` (the QYM S2 normalization wave) was merged
into the local pCN branch. Three files conflicted and all three were **prose or
docstrings** — no theorem statement, hypothesis or proof term was touched, so the
resolution cannot affect any row of the table above:

| File | Resolution |
|---|---|
| `softmodes.md` | Kept the branch's `BookProof.lean` live-inventory wording; dropped the other side's stale `YANG_MILLS_MASS_GAP_LEAN.md` claim. |
| `CONSOLIDATED_PLAN.md` | Kept a single "newest entry" header block. The file is append-only by house rule, so no dated entry was removed from either side. |
| `BookProof/MCMC/FockLangevinOperator.lean` | Module docstring §21.9/§21.10 merged, with one consolidated "Honest boundary" paragraph instead of the two overlapping ones. |

**The ignore scope (`d1afca2`).** `Downloads/` is a ~2 GB verbatim input corpus for the
Prove2.me conversion, and it is regenerable: `scripts/prove2me_convert.py` and
`scripts/prove2me_deps_convert.py` consume it, and the artifact that is kept is
`converted/`. It was untracked and therefore appeared in every `git status`, so it is now
ignored — the same treatment `/math/` already had. `/Scratch*.lean` and `/prompts.save`
are local scratch and are ignored too.

Two removals matter more than the additions:

- **`/.github/` is no longer ignored.** The repo tracks four workflows there
  (`ci.yml`, `axiom-gate.yml`, `linkcheck.yml`, `verify-invariants.yml`), so the rule
  contradicted the tree it was supposed to protect and would have silently swallowed any
  new workflow.
- **A duplicated `/math/` line was dropped.** It changed no behaviour; it was noise in the
  one file people read to answer "is this tracked?".

`DOC_INDEX.md` and `state/doc_index.json` were already untracked, with `scripts/health.sh`
and `.github/workflows/ci.yml` gating on rebuild determinism instead of tracked-file
freshness (`ae01e2f`). A missing index is therefore not a failed gate.

**Build note — `lake build` has no job cap.** Lake 5.0.0-src+7e01a1b (Lean 4.28.0) exposes
no `-j`/`--jobs` and no `LAKE_JOBS` knob; the aggregate `BookProof` build runs 14
concurrent `lean` processes, several near 1.7 GB, and available memory falls from 11 GB to
~600 MB within minutes, at which point the kernel OOM-kills a worker. Measured twice on
2026-11-11 (died at 8630/8968, 8654/8968, 8616/8948 and 8592/8948 jobs, no `error:` line).

**CPU affinity is the lever, because lake sizes its worker pool from the number of visible
CPUs.** Same 8-module set, measured 2026-11-11: `taskset -c 0-3` → 5 `lean` workers and
8.7 GB free; `taskset -c 0-5` → 12 workers and 703 MB free, i.e. an OOM in waiting. An
earlier entry here claimed affinity does not help; that probe was run while an orphaned
build was still compiling, so its count was meaningless and the claim was wrong. Chunk size
alone is *not* a bound either — a chunk of 8 unpinned fanned out to 18 workers and died at
830 MB.

Use `bash scripts/build-bookproof.sh` (default: 4 CPUs via `taskset`, chunks of 8, and a
`--min-free 4000` MB gate before every chunk). It resolves the out-of-date modules from the
import closure, builds them one `lake build` at a time, and traps signals so an interrupted
run does not leave orphaned `lean` children behind. Measured on the 156 out-of-date
`BookProof` modules: peak 9 workers, available memory never below 8.2 GB, zero errors.

Run it detached: `setsid nohup bash scripts/build-bookproof.sh > /tmp/build.log 2>&1 &`.
A build launched as a normal background tool command is killed when the runner's command
broker drops (`exitCode: null` plus a `terminal command broker protocol response was missing`
entry), which is *not* the same failure as the OOM kill and is indistinguishable from it in
the build log alone. Neither failure prints an `error:` line, so always check the process is
still alive before concluding that a silent stop means an elaboration failure.

---

## Flags — where the corpus contradicts itself

These are recorded, not resolved. Each names who would have to decide.

### ⚠ F1 — the `CONSOLIDATED_PLAN.md` header was stale *(fixed)*

The header read **"Start here (2026-09-25)"** and named the 09-25 entry as the newest,
while two newer entries followed it in the same file: **§10-04** (the mass-gap entry) and
**§10-04b**. The header mentioned neither. §10-04 is 11 commits of context the header never
saw, and it supersedes §13 for the mass-gap track.

*Fixed alongside this file:* the header now names the newest entry, points here, and states
that the RH track has no order. The 09-25 paragraph is **kept, not rewritten** — the house
rule is append, never delete.

**Side effect worth recording:** that edit shifted every line number below the header by 13,
which invalidated every positional citation this file had been drafted with. Hence the
content-based citation policy above. If you add a state entry to `CONSOLIDATED_PLAN.md`,
expect to re-verify any `file:line` reference elsewhere in the repo.

### ⚠ F2 — RandomMap/RH has no order, and three documents claim to have one

This is the one track with **no current work order at all**, and the only genuine hole in
the table above.

- `AGENTS.md`'s "Priority Attack Order for Next Agent" section publishes
  `uniform_variance_bound`, `jensen_bohr`, `convergent_series_has_no_poles`. All three are
  marked ***Sorry*** in its own Formalization State table. **They are already proved**:
  `FORMALIZATION_ROADMAP.md` lists them as "proved", and `CONSOLIDATED_PLAN.md` confirms
  the `RandomMap2` chain is "`sorry`-free in both trees". `AGENTS.md` is stale here, and it
  is the file an agent is most likely to read first.
- `IMPLEMENTATION_PLAN_RCP.md` declares itself, in its own first line, "**NEW STRATEGY
  (maintainer), AUTHORITATIVE. READ THIS FIRST.**" — a self-declared authority, last
  touched 2026-07-22.
- `FORMALIZATION_ROADMAP.md` says "**No UsedRoute/ or UnusedRoute/ work — RH work out of
  scope.**"

Meanwhile the open question has been on the table since August and never answered, in the
same paragraph that records the `sorry`-free chain: *"Confirm with the plan's RH section
whether the route `sorry`s are next in queue or parked behind the QG/QYM/operator thread."*
Corroborating signal: `DOC_INDEX.md` lists `RandomMap.md`, `RandomMap_old.md` and
`RandomMap2LegacyDraft.md` under **Never linked** — nothing in the corpus points at them.

*Needs an owner's decision:* is the RH route in the queue or parked? Until then this row
is deliberately empty rather than filled with a guess.

### ⚠ F3 — two `C` (conditional) NS items rest on a refuted reduction

§09-25 §5 item 3 keeps ESA of `N_NS` and of `N_L` as explicit **C** hypotheses. But §09-25
§2 records the mainstream surjectivity hypothesis as **refuted** — `not_nsEnergy_surjective`
(**N**), with `nsKoopman_esa_of_energy_comparison` "vacuous as stated" — and §3 repeats it.
The NS order was rewritten around a refutation and still names two unproved hypotheses.

Not a contradiction in the logic — an *ordering* hazard: an agent reading item 3 alone will
not see that the energy comparison it leans on was refuted. Read item 3 together with the
§2 NS row.

### ⚠ F4 — the last book wave landed with no plan entry

Commit `7fa2b6c` (2026-09-30) added Orientation and Status sections to 48 `Book/` chapters
— the most recent substantive work in the repo — and appended **no** corresponding entry to
`CONSOLIDATED_PLAN.md`. The nearest plan-facing artifact, `Book/ProofPlans.lean`, defers
elsewhere: *"A more detailed, machine-oriented version lives in `CONSOLIDATED_PLAN.md` at the
repository root."*

### ⚠ F5 — `ARISTOTLE_SUMMARY.md` claims a run whose artifacts are absent *(resolved 2026-10-16)*

The summary copied from `../internal-final_aristotle` (run `8c1a652e…`) describes
`BookProof/Ns/ChapterNsLagrangianComparisonEsa.lean` (`lagComparison_esa`, `lagKoopman_esa` —
the `N_L = H_L² + E` comparison proved ESA **with no extra hypotheses**), the
`ChapterKvnKato*` chapters newly imported from `BookProof.lean`, two added `#print axioms`
lines in `ChapterRoadmapAudit.lean`, and `§"2026-10-16"` entries in `STATUS.md` and
`CONSOLIDATED_PLAN.md`. None of these exist: no such files anywhere in the workspace, no
`§"2026-10-16"` entry in either document, and the claim contradicts the 2026-10-15c row,
which records the `N_L` hypothesis as **still explicit**.

*Search closed 2026-10-16 (negative).* The attachment `../internal-final_aristotle` was
searched exhaustively (`rg` over the whole tree, `.lake` included): no
`ChapterNsLagrangianComparison*`, no `ChapterKvnKato*`, no `lagComparison_esa`. The full
git history of all eight local repos under `/home/leo/Projects` (timepiece included —
`git log --all --diff-filter=A`, `--grep=8c1a652e`, `git stash list`, every reachable tree
via `ls-tree`) contains no commit that ever added these paths; neither do timepiece's
remote-tracking branches `origin/main` or `origin/aristotle-331`, and `git fetch
--dry-run` reports nothing new. The artifacts are therefore not restorable from anything
persisted in this workspace.

*Resolved 2026-10-16 (same day, later).*  The search above stands as a record — the
artifacts were in fact nowhere in the workspace, git history, or remotes — but the run's
contents arrived in the repo as `MISSING_FILES_CONTENTS.md`, the manifest of run
`e9b2b456`: full text of the eight modules (the seven `ChapterKvnKato*` chapters +
`ChapterNsLagrangianComparisonEsa.lean`), the `BookProof.lean` import line, the two
`#print axioms` lines for `ChapterRoadmapAudit.lean`, and the `STATUS.md` /
`CONSOLIDATED_PLAN.md` sections.  All were regenerated from it; every claim of
`ARISTOTLE_SUMMARY.md` §"2026-10-16" checks out against the restored files, the
`N_L`-hypothesis work-order step closed on the ordered route, and
`CONSOLIDATED_PLAN.md`'s final entry records the closure.  The "do not implement from
the summary" warning is lifted.

---

## Maintaining this file

1. **Append a state entry** to `CONSOLIDATED_PLAN.md`, in house style, with the
   supersession clause in its preamble.
2. **Repoint the affected row(s)** above at the new entry.
3. **Move** each predecessor from `current` to the appropriate superseded column — never
   delete a row, and never rewrite a superseded row's history.
4. **Update the header** of `CONSOLIDATED_PLAN.md` if the new entry is the newest.
5. **Cite by heading or quoted phrase, never by line number** — see the note above.
6. **Re-run** `python3 scripts/doc_index.py` — this file is indexed, and its `In`/`Out`
   counts are part of the corpus's link health.

If a row's `current` cell is empty, that is a finding, not an omission. F2 is what an
empty cell looks like when nobody has decided yet.

Related: `DOC_INDEX.md` (backlink graph, regenerated by `scripts/doc_index.py`),
`STATUS.md`, `HONEST_BOUNDARIES_SM.md` (the SM boundary ledger, the model for what an
honest track ledger should look like).
