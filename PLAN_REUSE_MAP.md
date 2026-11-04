# Reuse map for the three plans — `cftproof.md`, `softmodes.md`, `pcnl.md`

*Search run 2026-10-30 by the workspace agent. Sources: the prove2.me catalogue (API
`0.13.6`, matching `prove2me_workspace/SKILL.md` `metadata.version` — skill not stale), the
local Lean libraries `physlib/` (Lean `v4.35.0`), `math/lean/` (OpenAI snapshot, `v4.34.1`) and
`timepiece/` (`v4.28.0`).*

The query helper is `prove2me_workspace/scripts/search_theorems.sh QUERY [LIMIT]` (reads the
access token from `/tmp/p2m_token.txt`, never from the repo).

## How to read a row

| verdict | meaning |
| :-- | :-- |
| **in-repo** | already proved in `timepiece`; just `import` it |
| **restate** | proved elsewhere at a Lean version `timepiece` cannot import; transcribe (state it, or port it) — Mathlib-only statements port, platform-local definitions must be abstracted first |
| **platform-import** | a *Proved* prove2.me node: cite it as a lemma when submitting to the platform (that is a legal reduction), not as a `timepiece` import |
| **open on platform** | the exact statement is already posed and unsolved on prove2.me — a submission target, not a source |
| **nothing found** | searched prove2.me + all three libraries; the step is new mathematics |

---

## A. `cftproof.md` — Bałaban's Euclidean programme, OS reconstruction

### A.1 Phase 1 — 4D Hermite core and the Mehler measure

| need | source | verdict |
| :-- | :-- | :-- |
| 4D Hermite basis, totality | `BookProof/EuclideanFock4D/CoreBasis.lean` — `euclideanHermiteBasis4D`, `euclideanHermiteNet4D` | in-repo |
| Mehler measure, `O(4)` invariance | `BookProof/EuclideanFock4D/MehlerMeasure.lean` — `mehlerMeasure4D`, **`mehler4D_O4_invariant`**, `sphereUniform4D` | in-repo |
| tensor Hermite basis on a product Gaussian | `math/lean/OAI/Analysis/FreeEntropy/TensorHermite.lean` — `productGaussian`, `tensorHermite`, `tensorWeight`, `tensorHermite_integrable`, `tensorHermite_mul_integrable` | restate (v4.34 → v4.28; `realHermite` exists here too) |
| Hermite recurrence / derivative / parity | `physlib/Physlib/Mathematics/SpecialFunctions/PhysHermite.lean` — `physHermite_succ`, `deriv_physHermite`, `physHermite_neg`, `natDegree_physHermite` | restate (v4.35) |
| multi-dimensional Hermite eigenfunctions, orthonormality | `physlib/Physlib/QuantumMechanics/HarmonicOscillator/Eigenstates.lean` — `eigenfunction_eq_prod_oneDim`, `eigenstates_orthonormal` | restate |
| Hermite oscillator equation (already public) | platform *Proved* `BookProof.HermiteStrichartzQG.oscillator_eigenfunction`, `BookProof.HermiteCore.natDegree_hermiteR` | platform-import |

### A.2 Phase 2 — block-averaging RG

| need | source | verdict |
| :-- | :-- | :-- |
| scale decomposition `F_total = ⊕_k ℱ_k` | `BookProof/BalabanRG/MultiscaleSpace.lean` — `Sector`, `FTotal`, `rgOnTotal_norm_le`, `psiSeq` | in-repo |
| `‖Q_k‖ ≤ 1`, idempotence | `BookProof/BalabanRG/BlockOperator.lean` — `blockAveragingOp_norm_le` | in-repo |
| increment bound ⟹ limit | `BookProof/BalabanRG/Convergence.lean` — `summable_of_increment_bound`, `psiSeq_cauchy`, `balaban_rg_convergence` | in-repo, **conditional** |
| Bałaban's polymer estimate `‖Ψ_{N+1} − Ψ_N‖ ≤ C L^{−εN}` | — | **nothing found** (no hit for block averaging / polymer / RG contraction in prove2.me, `physlib`, `math`) |

### A.3 Phase 3 — reflection positivity

| need | source | verdict |
| :-- | :-- | :-- |
| `θ` on `ℝ⁴` and on configurations | `BookProof/ReflectionPositivity/Involution.lean`, `BlockCommute.lean` (`theta_commutes_blockAveraging`) | in-repo |
| positive-time algebra, `θ : 𝔄₊ → 𝔄₋` | `BookProof/ReflectionPositivity/HalfSpaceAlgebra.lean` | in-repo |
| `osForm`, `IsReflectionPositive`, continuum limit | `BookProof/ReflectionPositivity/Proof.lean` — `reflection_positivity_continuum` | in-repo |
| half-space positivity, why the full-algebra version trivialises | `BookProof/OSReconstruction/ReflectionKernel.lean` — `IsReflectionPositiveOn`, `isReflectionPositiveOn_of_factorization`, **`mk_thetaObs_eq_mk`** | in-repo |
| platform's `YangMills.IsReflectionPositive` ⟺ state-level OS positivity | `BookProof/OSReconstruction/YangMillsBridge.lean` — **`osBilin_gram`**, `osBilin_gram_nonneg`, **`complex_sum_quadform`**, **`isReflectionPositive_yangMills`**, `isReflectionPositiveOn_loopProd` | in-repo |
| OS-form Cauchy–Schwarz (already public) | platform *Proved* `YangMills.os_positivity_cauchy_schwarz` | platform-import |
| **the lattice OS identity itself** | platform *Open* `YangMills.lattice_reflection_positivity`, `YangMills.wilson_action_reflection_positivity`, `YangMillsMassGap.wilson_reflection_positivity` | open on platform — the plan's hypothesis *is* a posed mission node |

### A.4 Phase 3.3 — the Wick/Isserlis step (general covariance)

| need | source | verdict |
| :-- | :-- | :-- |
| Isserlis, standard covariance | `BookProof/OSReconstruction/GaussianMoments.lean` — `productGauss`, **`isserlis_productGauss`**, `integral_prod_coord_productGauss` | in-repo (standard covariance only) |
| pairings `= (2n−1)‼`, zero-fixed-point involutions ≃ pairings | `physlib/Physlib/Mathematics/ForMathlib/Fin/Involutions.lean` — **`involutionNoFixed_card_mul_two`**, `involutionNoFixed_card_even`, `involutionNoFixedZeroEquivProd` | restate (v4.35) |
| Wick contractions enumerated, `card = cardFun` | `physlib/Physlib/QFT/PerturbationTheory/WickContraction/Card.lean` — **`card_eq_cardFun`**, `wickContraction_zero_some_eq_mul`; `…/Basic.lean`, `…/Sign/`, `…/TimeContract.lean` | restate |
| Gaussian moment flow / Stein | `math/lean/OAI/MeasureTheory/FalconerCompletion/Measures/GaussianMomentFlow.lean`, `OAI/Analysis/FreeEntropy/GaussianMvStein.lean` | restate |

The plan's todo item 1 (general covariance `C p q = Σ_a v a p * v a q`) is therefore
**physlib's pairing combinatorics + the in-repo Isserlis**, glued by the existing
multinomial/coordinate-factorisation step.

### A.5 Phase 4 — OS reconstruction and the physical Hilbert space

| need | source | verdict |
| :-- | :-- | :-- |
| bilinearity, symmetry, positivity, Cauchy–Schwarz, `Radical`, `osNorm_triangle` | `BookProof/OSReconstruction/PhysicalSpace.lean` | in-repo |
| inner product on `𝔄/𝔑`, completion `H_phys`, contractive evolution | `BookProof/OSReconstruction/HilbertSpace.lean` — `physCore`, `physInnerProductSpace`, `Hphys`, `physEvolCompletion` | in-repo |
| momentum-space / Källén–Lehmann form | `BookProof/OSReconstruction/MomentumBasis.lean` | in-repo |
| Wightman axioms, `E → R`, `R → E` | platform *Open* `YangMillsMassGap.os_theorem_E_to_R`, `YangMillsMassGap.os_theorem_R_to_E`, `YangMillsMassGap.wightman_functions_satisfy_axioms` | open on platform |

**Publishing gap:** the platform has **no** node for `BookProof.OSReconstruction`,
`BookProof.ReflectionPositivity` or `BookProof.MCMC` (queries on those namespace prefixes and
on `osForm`, `physCore`, `reflection_positivity_continuum` return 0 matches), while
`BookProof.Sirk` carries 326 proved nodes. Phases 3–4 of `cftproof.md` and Modules 4–5 of
`pcnl.md` are therefore proved locally and invisible to the rest of the platform — submitting
them (definitions first, then the theorems) is the cheapest way to make them reusable.

### A.6 Phase 5 — gap and clustering

Platform *Open*: `YangMills.strong_coupling_clustering`, `YangMills.strong_coupling_area_law`,
`YangMills.strong_coupling_thermodynamic_limit`, `YangMillsMassGap.mass_gap_implies_clustering`,
`YangMills.two_dimensional_rectangle_law`, and the three `yang_mills_existence_and_mass_gap`
nodes. Local receivers: `BookProof/Sirk/ChapterRitzCertificate.lean`,
`BookProof/ChapterSpectralGapStability.lean`.

---

## B. `softmodes.md` — analytic spectral separation `β_∞ > θ_∞`

### B.1 Phase 3 — `H_ref` with a certified gap (the best-covered phase)

| need | source | verdict |
| :-- | :-- | :-- |
| `H = −d²/dx² + x²/4` on the Hermite core, eigenvalue equation, essential self-adjointness | `BookProof/ChapterHarmonicOscillatorEsa.lean` — `harmonicOscOp`, **`harmonicOscOp_hermiteLp`** (`Hψ_n = (n+½)ψ_n`), `harmonicOscOp_apply_eq_differential`, `harmonicOsc_symmetric`, `harmonicOsc_essentiallySelfAdjoint`, `harmonicOsc_not_bounded` | in-repo |
| **d-dimensional** oscillator: explicit spectrum, strict monotonicity, eigenvectors, orthonormal basis | `physlib/Physlib/QuantumMechanics/HarmonicOscillator/Eigenstates.lean` — `eigenEnergy_eq` (`∑ ℏω_i(n_i+½)`), **`eigenEnergy_strictMono`**, `hamiltonian_eigenstate`, `eigenstates_orthonormal` | restate (v4.35) — this *is* `Δ_ref = min_k ℏω_k` |
| quadratic form on the Schwartz core | `physlib/…/HarmonicOscillator/NumberOperator.lean` — `hamiltonian_inner_schwartz`, `schwartzSubmodule_le_hamiltonian_domain`, `numberOperator_isSymmetric` | restate |
| ladder algebra `x = (a + a†)/√2`, `∂ = (a − a†)/√2` | `physlib/…/HarmonicOscillator/LadderOperators.lean` — `position_eq_lowering_add_raising`, `momentum_eq_raising_sub_lowering`, `lowering_commutation_raising`, `raising_eigenfunction`, `lowering_eigenfunction`, `loweringOperator_isFormalAdjoint_raisingOperator` | restate |

### B.2 Phase 4 — form domination `q_{H_W} ≥ c₁ q_{H_ref} − c₂`

| need | source | verdict |
| :-- | :-- | :-- |
| cross-term control between the linear gradient and the cubic/quartic potential | `BookProof/Toolbox/ChapterFockFieldPerturbation.lean` | in-repo |
| relative form bound ⟹ spectral shift | `BookProof/Toolbox/ChapterFockInteractionStability.lean` | in-repo |
| a *worked* coercive form bound to imitate | platform *Proved* `BookProof.ScalaronDensitized.physConfOp_quadForm_ge` (`quadForm ≥ −(M⁴/16α)‖f‖²` on the core) | platform-import |
| coercive self-adjoint ⟹ bijective (the Hilbert-space half of the argument) | platform *Proved* `VectorSpaceOpt.coercive_selfadjoint_bijective` | platform-import |
| Simon's channel taming (`V(x,y)=x²y²` has discrete spectrum) | — | **nothing found** in any source; Phase 2 is genuinely new |

### B.3 Phase 5 — Temple receiver

| need | source | verdict |
| :-- | :-- | :-- |
| Temple's inequality, finite certificate | `BookProof/Sirk/ChapterSirkFinitePrecision.lean` — **`temple_lower_bound`**; `BookProof/Sirk/ChapterRitzCertificate.lean` | in-repo |
| Temple, textbook form | platform *Proved* `TeschlQM.MinMax.temple` (Teschl Thm 4.13), `BookProof.SirkFinitePrecision.temple_lower_bound` | platform-import |
| separation is *necessary* | `BookProof/Sirk/ChapterTempleSeparationNecessary.lean` — `separation_necessary` | in-repo |
| uniform enclosure from an analytic separation constant | `BookProof/Sirk/ChapterTempleSeparationBound.lean` — **`temple_lower_bound_analytic`**, `temple_band_width_le_analytic`, `temple_uncertainty_tendsto_zero`, `separation_constant_pos`, **`temple_lower_bound_of_form_domination`** | in-repo (new) |
| gap survives the limit (operator norm) | `BookProof/ChapterSpectralGapStability.lean` — `gapAt_perturb`, `gapAt_of_tendsto`, `notMem_spectrum_of_uniform_gap`, `spectrum_disjoint_of_uniform_window` | in-repo, **bounded/operator-norm only** |

### B.4 ⚠ Blockers found on the platform

1. **`weyl_friedrichs_extension_of_complete_explicit` is DISPROVED on prove2.me** (node
   `31b729d5-5d48-4a87-b03c-b88f1ef5c4c3`, accepted disproof). The counterexample: on the
   non-closed subspace `span{e_n} ⊔ ℂf` of `ℓ²`, a symmetric Jacobi matrix `π` with
   `⟨πv, f⟩ = i⟨v, f⟩` makes `f` an eigenvector of `H* = (½π²)*` at `−½`, so no positive
   self-adjoint extension exists. The cause is the hypothesis profile: the statement only
   assumes `[NormedAddCommGroup F] [InnerProductSpace ℂ F]`, with no `[CompleteSpace F]`.
   `timepiece`'s own statement has **the same profile** (`BookProof/Toolbox/ChapterFriedrichsExtension.lean:83`),
   so this needs checking before Phase 5 leans on `weyl_hashimoto_selects_friedrichs`.
   Disproved alongside it: `friedrichs_extension_exists_of_complete_explicit`, `friedrichs_hypothesis_holds_of_complete_explicit`,
   `friedrichs_extension_semibounded_of_complete_explicit`.
2. **`BookProof.BrstReducedTransfer.*` — 4 disproved nodes** (`stoneU_mem_physicalStates_of_comm_explicit`,
   `stoneU_sub_mem_exactStates_of_comm_explicit`, `infDist_exactStates_stoneU_eq_of_comm_explicit`, `infDist_exactStates_eq_of_comm_explicit`).
   Phase 1 cites `BrstReducedTransfer` for the projection onto transverse states.
3. **`BookProof.ChapterSpectralDirectSum.spectral_multiplication_model_{general,separable}`**
   — 2 disproved nodes. `pcnl.md` §3 cites the spectral theorem via
   `BookProof.ChapterSpectralMultiplication`.

19 `BookProof.*` nodes in total are `Disproved` on the platform; the rest are
`ChapterSolidHarmonic` (4), `ChapterAbelianCyclicCommutant`/`ChapterAbelianCyclicModel`/
`ChapterAbelianGelfandModel` (3) and `FockDegreesOfFreedom.Gravity.ghostRawCard` — outside these
three plans.

---

## C. `pcnl.md` — pCNL as a linear operator on `L²(π)`

### C.1 Modules 4–5 — already done locally

| need | source | verdict |
| :-- | :-- | :-- |
| spectral gap ⟹ geometric ergodicity, discrete time | `BookProof/MCMC/GeometricErgodicity.lean` — `inner_fixed_apply_eq_zero`, `iterate_orthogonal`, `norm_iterate_le_of_orthogonal`, **`norm_iterate_sub_invariant_le`**, `tendsto_iterate` | in-repo |
| coercive generator ⟹ `‖e^{−tA}v‖ ≤ e^{−μt}‖v‖` (continuous time twin) | `BookProof/Sirk/ChapterSirkDiffusiveDecay.lean` — **`isCoercive_compress`**, `norm_heatFlow_apply_le` | in-repo |
| missing leg: `‖ν − π‖_TV ≤ ½‖dν/dπ − 1‖_{L²}` | — | **nothing found** (recorded as boundary in the file above) |

### C.2 Module 1 — Gegenbauer spectrum of the spherical pCN step

| need | source | verdict |
| :-- | :-- | :-- |
| three-term recurrence of the rescaled Gegenbauer family | `BookProof/Toolbox/PhysHSGaussian/Part3.lean` — `gegenbauerScaled_rec` | in-repo |
| `C_i'(1)/C_i(1) = i(i+d−2)/(d−1)`, harmonic dimensions | platform *Proved* `SphereSOS.Rate.gegenbauer_deriv_one`, `SpherePacking.Gegenbauer.harmonicDimension_branch_sum` | platform-import |
| `C_i(t) ≥ C_i'(1)(t−1) + C_i(1)` on `[−1,1]` | platform *Open* `SphereSOS.Rate.proposition_18` | open on platform |
| `sphericalMarkovStep`, `pcnGegenbauerMatrix` themselves | — | **nothing found** (no `pcn`/`markovStep` hit in `timepiece`, `physlib`, `math`, or prove2.me) |

### C.3 Module 2 — scaled limit to the Fock semigroup (already proved)

`BookProof/Toolbox/PhysHSGaussian/Part1.lean` — **`gegenbauerScaled_tendsto_hermite`**
(`(α/2)^{−n/2} C_n^{(α/2)}(√(2/α)x) → H_n(x)/n!`) and **`weight_tendsto_gaussian`**
(`(1 − x²/α)^{(α−1)/2} → e^{−x²/2}`): the plan's items 1 and 2 are already in the corpus.
Item 3 (the operator limit `P₀^{(∞)} = ρ^N`) has no statement yet.

### C.4 Module 3 — ladder representation of the drift

| need | source | verdict |
| :-- | :-- | :-- |
| `a, a†` on the Hermite core, CCR | `physlib/Physlib/QFT/PerturbationTheory/CreateAnnihilate.lean`; `…/HarmonicOscillator/LadderOperators.lean` (`lowering_commutation_raising`, `position_eq_lowering_add_raising`, `momentum_eq_raising_sub_lowering`) | restate |
| finite-band hopping / Carleman structure | `BookProof/Toolbox/ChapterCarlemanGeneralHop.lean` | in-repo |
| multi-mode Hermite basis on the product Gaussian | `math/lean/OAI/Analysis/FreeEntropy/TensorHermite.lean` | restate |

### C.5 Supporting Markov / mixing machinery on the platform (all *Proved*)

Finite state: `MarkovChain.tendsto_vecMul_pow_of_doeblin` (Doeblin ⟹ convergence),
`MarkovChain.isStationary_of_reversible`, `MarkovChain.tvDist_metric`,
`MarkovChain.tvDist_le_one`, `LIDT.PMF.totalVariationDistance_eq_sum_max_sub`.
General chains: `MarkovMixing.convergence_theorem`, `MarkovMixing.detailed_balance_stationary`,
`MarkovMixing.path_coupling` + `path_coupling_mixing` (Bubley–Dyer),
`MarkovMixing.metropolis_stationary`, `MarkovMixing.metropolized_stationary`,
`TierneyMH.Mixture.maxMHKernel_reversible` (maximal Metropolis–Hastings kernel satisfies
detailed balance), `MarkovMixing.heat_kernel_convergence`.
Spectral/diffusive: `CountingMatroid.Analysis.OnePairObservablePoincare.one_pair_observable_poincare`,
`CountingMatroid.Analysis.ObservableEnergyDual.observable_energy_dual`,
`LogSobolevMC.ChiSquare.theorem_3_7` (log-Sobolev ⟹ χ² convergence),
`LogSobolevMC.Entropy.lemma_2_5_ent`.
Gaussian/OU: `GaussianMatrix.ou_semigroup_invariant`, `ou_semigroup_commutation`,
`ou_entropy_hasDerivAt`, `gaussian_logsobolev`, `gaussian_logsobolev_one_dim`.
In `math/`: `OAI/Analysis/AffineBernstein/WeightedPoincare.lean` (`weighted_poincare`),
`…/VarianceSeparation.lean` (`variance_lower_of_separated_sets`) — the variance/spectral-gap
translation the plan needs, at `v4.34.1`.

---

## D. Cross-cutting notes

* **Nothing can be `import`ed across these libraries.** `timepiece` is `v4.28.0`; `physlib` is
  `v4.35.0`, `math/lean` is `v4.34.1`, and the platform's default environment is `v4.33.1`
  (it also offers `v4.30.0` and `v4.29.0-rc3` — pick `v4.30.0` when transcribing a `timepiece`
  statement, it is the closest offered and has the fewest API drifts). Every "restate" row is a
  transcription job, and platform-local definitions (`Def_MarkovChain`,
  `Def_TeschlQM_MinMax_spectrum`, `Def_GaussianMatrix_basic`, `Def_YangMills_Wilson_lattice`)
  must be re-declared minimally first.
* **The Yang–Mills problem cluster is the plans' own frontier.** 16 open `YangMills*` nodes
  (reflection positivity, `E→R`/`R→E`, Wightman, clustering, area law, existence+mass gap) and
  225 proved `BookProof.YangMills*` nodes — `cftproof.md` Phases 3–5 and `softmodes.md`
  Phase 5 map onto them one-to-one, so a proof written for the plan can be submitted directly.
* **Two chapters the plans cite carry disproved nodes on the platform**
  (`FriedrichsExtension`, `BrstReducedTransfer`, plus `ChapterSpectralDirectSum`): the
  disproofs are about statements transcribed *without* a completeness/side hypothesis, so the
  first action is to diff each platform statement against the in-repo one before building on it.
* **Where the plans are thinnest:** Bałaban's polymer estimate (`cftproof` 2.3), Simon's
  channel-taming / confining barrier (`softmodes` 2), the pCN Gegenbauer eigenrelation
  (`pcnl` 1). No library, on any of the four sources, has anything for these three.

## E. Suggested order of work

1. Diff the 19 `Disproved` nodes against the in-repo statements; fix or qualify the
   `FriedrichsExtension` cluster before `softmodes` Phase 5.
2. Port `physlib`'s `involutionNoFixed_card_mul_two` + `WickContraction/Card.card_eq_cardFun`
   to generalise `GaussianMoments.isserlis_productGauss` (`cftproof` todo 1) — the only step of
   `cftproof`'s Phase 3.3 with all ingredients in hand.
3. Port `physlib`'s `HarmonicOscillator` spectrum (`eigenEnergy_eq`, `eigenEnergy_strictMono`)
   as `H_ref` and discharge `softmodes` Phase 3 with `Δ_ref = min_k ℏω_k`; feed
   `ChapterTempleSeparationBound.temple_lower_bound_of_form_domination`.
4. Publish `BookProof.OSReconstruction.*` and `BookProof.MCMC.GeometricErgodicity` to
   prove2.me — proved, uncited, and reusable by both `cftproof` and `pcnl`.
