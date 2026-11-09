# Executing `cftproof.md`: Euclidean 4D CFT → 3D CFT

This note records what was built for `timepiece/cftproof.md`, module by module, with the
distinction that matters for the MM0 pipeline: **what is a theorem**, and **what is boundary**.

No declaration in the modules below contains `sorry`; every statement is proved, and every
statement that could not be proved is *stated as a hypothesis* with the reason recorded in the
module docstring, not silently assumed.

## Modules

| Plan phase | Module | Contents |
|---|---|---|
| 1.1 | `BookProof/EuclideanFock4D/CoreBasis.lean` | `euclideanHermiteBasis4D` (= corpus `hermiteMvBasis` at `d = 4`), orthonormality, totality, the `ℕ`-enumerated `euclideanHermiteNet4D`, the colour basis |
| 1.2 | `BookProof/EuclideanFock4D/MehlerMeasure.lean` | `mehlerMeasure4D := gaussianE 4`, `mehler4D_O4_invariant`, `sphereUniform4D` and its `O(4)` invariance |
| 2.1 | `BookProof/BalabanRG/MultiscaleSpace.lean` | `Sector k`, `FTotal = ⊕_k ℱ_k` as an `ℓ²` sum, `rgOnTotal`, `rgOnTotal_norm_le`, `psiSeq` |
| 2.2 | `BookProof/BalabanRG/BlockOperator.lean` | `blockConst`, `blockAveragingOp`, **`blockAveragingOp_norm_le` (`‖Q_k‖ ≤ 1`)**, idempotence, image in the coarse subspace |
| 2.3 | `BookProof/BalabanRG/Convergence.lean` | `summable_of_increment_bound`, `psiSeq_has_limit`, `psiSeq_cauchy`, `balaban_rg_convergence` |
| 3.1 | `BookProof/ReflectionPositivity/Involution.lean` | `timeReflection` on `ℝ⁴` (`θ² = 1`, coordinate formula), **`timeReflection_measure_invariant`**, the lattice cell involution `flipCell`, `fieldReflection` on configurations |
| 3.1 | `BookProof/ReflectionPositivity/BlockCommute.lean` | **`blockOf_reflectCoord`** (the block partition is `θ`-stable), `mem_blockConst_fieldReflectionSector`, **`fieldReflectionSector_blockAveragingOp` / `theta_commutes_blockAveraging`** (`θ Q_k = Q_k θ`) |
| 3.2 | `BookProof/ReflectionPositivity/HalfSpaceAlgebra.lean` | `PositiveTimeAlgebra`, `CylindricalObservables`, `positiveTimeAlgebra_cylindrical`, `thetaObs` and **`thetaObs_dependsOn_negTime` (`θ : 𝔄₊ → 𝔄₋`)** |
| 3.3 | `BookProof/ReflectionPositivity/Proof.lean` | `osForm`, `IsReflectionPositive`, **`reflection_positivity_continuum`**, `psiSeq_component_tendsto` |
| 3.3 | `BookProof/ReflectionPositivity/FeynmanKac.lean` | `freeTransferKernel` (the one-step Gaussian weight `exp(-(lam/2) Σ (z' i - z i)²)`) with **`freeTransferKernel_pos`**, `fkKernelProduct` with **`fkKernelProduct_pos`**; `freeAction` with **`freeAction_cross_vanishes`** (Markov property: block-tridiagonal precision ⇒ no past–future coupling) and **`freeAction_reflect`**, `freeDensity_factorises`; `fkMeasure ρ ν = ρ ⊗ ν ⊗ ν`, `fkOSForm`, **`fk_integral_eq`** (`∫ θF·F d(ρ⊗ν⊗ν) = ∫ z, (∫ y, F z y ∂ν)² ∂ρ`) and **`fk_reflectionPositive`** — reflection positivity for every integrable half-space observable, polynomials included |
| 3.3 | `BookProof/ReflectionPositivity/QuadraticWick.lean` | `osQuadForm` (the Isserlis sum of a quadratic half-space observable), `kern`, **`pairing_swap`** (the two Wick pairings of a symmetric quadratic observable agree), **`osQuadForm_eq_two_mul_kern`** (`= 2 Σ_{i j} a_{i j}(KAK)_{i j}`), `kern_transfer`, **`osQuadForm_eq_two_sum_sq`** (`= 2 Σ_{x y} w_x w_y (Σ_{i j} a_{i j} u_{x i} u_{y j})²` for a Källén–Lehmann covariance), **`osQuadForm_nonneg`** (the `w ≥ 0` case) — the degree-two lift. Degrees 1–2 are where the Isserlis route is proved to match the transfer form; degree 3 is refuted by the odd-subspace counterexample and even degrees ≥ 4 are not analysed |
| 4.1 | `BookProof/OSReconstruction/PhysicalSpace.lean` | bilinearity, symmetry, positivity, `osForm_expand`, **Cauchy–Schwarz**, `Radical`, `osForm_well_defined`, `osNorm_triangle` |
| 4.2 | `BookProof/OSReconstruction/Hamiltonian.lean` | `TimeTranslation`, semigroup law, **`osNorm_evolution_antitone`**, `radical_invariant`, `timeEvolution_well_defined` |
| 3.2 + 3.3 | `BookProof/OSReconstruction/ReflectionKernel.lean` | `IsReflectionPositiveOn` (positivity on a set of observables), **`isReflectionPositiveOn_of_factorization`** (`ω(θF·G) = ωF·ωG` on `𝔄₊` ⇒ `⟨F,F⟩ = (ωF)² ≥ 0`), `isReflectionPositiveOn_positiveTimeAlgebra_of_factorization`, `IsPositiveFunctional`, `thetaObs_sub_self`, **`osBilin_sub_theta_self_eq_zero`**, `sub_theta_self_mem_radical`, **`mk_thetaObs_eq_mk`** (`[θF] = [F]` in `𝔄/𝔑`) |
| 3.3 + 4.1 + 5 | `BookProof/OSReconstruction/MomentumBasis.lean` | **`dft_convolution`**, **`dft_mul_eq_convolution`** (products of fields in space are convolutions in momentum), **`reflection_positivity_momentum`** (the transfer-factorised reflected two-point form is a weighted sum of modulus squares), **`covarianceForm_eq_dft`** (a translation-invariant covariance's form is the weighted Plancherel sum `∑ k, w k * ‖𝓕F k‖²`), the momentum/lattice overlap `overlap` with **`overlap_orthonormal`** and **`overlap_orthonormal_pos`**, **`cellLatticeOverlap_unitary`** (orthonormal momentum cells have orthonormal lattice profiles), **`exactHamiltonian`** and **`exactHamiltonian_eigenvector`** (the exact Hamiltonian in the lattice basis, transported with no truncation), **`compressed_hamiltonian_tendsto`** (the compressed lattice Hamiltonian converges strongly to the exact one), **`freePropagator_reflect_eq_transfer`** (the Källén–Lehmann factorization derives `transferKernel` for the explicit free propagator), **`freeOSForm_eq_momentum`** / `free_reflection_positive` (the half-space free OS form is a sum of modulus squares), **`compressed_flow_tendsto`** / **`bounded_flow_tendsto_unbounded`** (the SIRK/Trotter–Kato transfer: the bounded lattice flows converge to the unbounded generator in the limit), **`compressed_strongResolventConvergence`** (the SIRK resolvent hypothesis for the compressions), and **`galerkin_strongResolventConvergence`** / `galerkin_compressed_flow_tendsto` (the instantiation with a common-space nested block/Galerkin refinement) |
| 3.3 + 4.1 (bridge) | `BookProof/OSReconstruction/YangMillsBridge.lean` | `loopProd`, `thetaObs_loopProd`, **`osBilin_gram`** (the Gram identity), `osBilin_gram_nonneg`, **`complex_sum_quadform`** (a complex quadratic form of a symmetric real matrix is real; imaginary part cancels), **`isReflectionPositive_yangMills`**, `isReflectionPositiveOn_loopProd` — the dictionary to `Definitions.Def_YangMills`'s `YangMills.IsReflectionPositive` |
| 4.1 + 4.2 | `BookProof/OSReconstruction/HilbertSpace.lean` | `OSState`, `physForm` (descent via `LinearMap.liftQ₂`), `physCore` (**definiteness**), **`physInnerProductSpace`** (`InnerProductSpace.ofCore`), **`Hphys`** (`UniformSpace.Completion`, `HilbertSpace`), `physNorm_mk`, `physNorm_eq_zero_iff`, `physEvol`, **`physEvol_contractive`**, **`physEvolCompletion` with `norm_physEvolCompletion_le`** |

### Half-space quotient and forward semigroup (2026-11-09, `cftproof.md` E3)

| Plan phase | Module | Contents |
|---|---|---|
| 3.3 + 4.1 | `BookProof/OSReconstruction/HalfSpaceState.lean` | `HalfSpaceState` (θ-invariant functional, reflection positive **on `PositiveTimeAlgebra` only**, `ω 1 = 1`), `hsBilin` with bilinearity / symmetry / `hsBilin_expand` / **`hsBilin_cauchy_schwarz`**, the null **subspace** `HsRadical` (`mem_hsRadical_of_self_eq_zero`, `hsBilin_well_defined`), the quotient `HsSpace` with its inner product (`hsForm_mk`, `hsForm_self_eq_zero_iff`), the completion `Hhalf`, and `hsVacuum = [1]` with **`hsVacuum_norm : ‖Ω_OS‖ = 1`** |
| 4.2 | `BookProof/OSReconstruction/HalfSpaceHilbert.lean` | `PreservesPositiveTime`, `hsEvol`, `HsHinv`, **`hsRadical_invariant`** (forward translation preserves `𝔑₊`), `hsQuotMap` and `hsQuotMap_contractive`, `P(0) = I` (`hsEvolCompletion_zero`), `P(s+t) = P(s)P(t)` (`hsEvolCompletion_add`), `hsEvolCompletionFun_contractive`, **`tendsto_hsEvolCompletionFun`** (strong continuity at `0⁺` from matrix-element continuity), and **`hsEvolCompletion_isSelfAdjoint`** (`P(τ)* = P(τ)`) from the two-point symmetry hypothesis `HsSymmetric` |

These are the first declarations in the corpus whose carrier is the **positive-time** algebra
rather than the full observable algebra, which is the correction `ReflectionKernel.mk_thetaObs_eq_mk`
forces. `PreservesPositiveTime`, `HsHinv`, `HsSymmetric` and matrix-element continuity are
hypotheses, not theorems: the corpus has no concrete lattice `TimeTranslation`, no measure on
`Config = Fin latticeDim → ℝ`, and no instantiated two-point function. The quotient is used as a
vector space (no ideal claim), and the space is real — the complexification is not built. The
generator domain/resolvent on `𝔄₊/𝔑₊` remains open; `SemigroupGenerator` proves the corresponding
statements for `Hphys` under `HinvRight`.

## The five statements that carry the mathematics

1. **`blockAveragingOp_norm_le`** — the block-averaging projections are contractions.  Proved as
   a property of the orthogonal projection onto block-constant fields
   (`Submodule.norm_starProjection_apply_le`).
2. **`rgOnTotal_norm_le` / `norm_rgOnTotal_le`** — the total-space RG step is a contraction,
   `‖Q‖ ≤ 1`, via the `ℓ²` norm computation with the pointwise bound `‖Q_k x‖ ≤ ‖x‖`.
3. **`balaban_rg_convergence`** — a geometric bound on the increments of `Ψ_N` makes the sequence
   converge in the complete space `F_total`, with the limit exhibited as
   `Ψ₀ + Σ (Ψ_{n+1} − Ψ_n)`.
4. **`reflection_positivity_continuum`** — reflection positivity passes to the continuum limit
   along pointwise convergence, and `psiSeq_component_tendsto` supplies that convergence from the
   Phase 2 limit.  This is the plan's "the limit is reflection positive".
5. **`osForm_cauchy_schwarz` + `Radical` + `osForm_well_defined`** — the OS form of a reflection
   positive functional is an inner product modulo its radical; Cauchy–Schwarz is derived from
   positivity by minimising `t ↦ ⟨F + tG, F + tG⟩`.

## Boundary (recorded, never assumed)

* **Fock space, colour factor, `S^∞`.**  `ℱ_k` is modelled by its one-particle content, and the
  `su(N)` factor appears only as `CoreBasis.colourBasis`.  The *instruments* for a Fock/tensor
  lift do exist in the corpus and are not used here: `BookProof.Toolbox.ChapterTensorCompleteness`
  (`L²(μ ⊗ ν)` as the Hilbert tensor product, via `ChapterSolovayHilbertTensor.inner_tensorLp`),
  Mathlib's `Analysis.InnerProductSpace.TensorProduct`, and the `ℓ²` Fock spaces
  `BookProof.Ns.ChapterNavierStokesFockSpace.FockL2` / `BookProof.ChapterSqSumOuterFamily.outerFock`
  with `dGamma` (`ChapterFockSchurEsa`, `ChapterNsOneBodyDGamma`).  What is missing is the
  instantiation of *this* chapter's Gaussian-measure Fock space; the `S^∞` projective limit is
  not built.
* **Scale measures `dγ_k`.**  Only `dγ₀ = mehlerMeasure4D` exists; the pushforward under `Q_k` is
  not constructed.  `θ`'s commutation with `Q_k` **is** now proved:
  `ReflectionPositivity.BlockCommute.fieldReflectionSector_blockAveragingOp` (per sector) and
  `theta_commutes_blockAveraging` (on `F_total`).  This required making the block structure
  `θ`-stable: a block is the set of `nComponents` components `A_μ` at one lattice cell
  (`BalabanRG.MultiscaleSpace.coordOf`), which is exactly the partition `reflectCoord` permutes.
* **Lattice reflection positivity — and why the hypothesis must be the half-space one.**
  `ω_N(θF F) ≥ 0` for `F ∈ 𝔄₊` is a theorem of the literature, not a Lean bookkeeping fact; it
  enters as the hypothesis of `reflection_positivity_continuum`.  The corpus states it over the
  *whole* observable algebra (`IsReflectionPositive`), which is strictly stronger and, for a
  genuine state, degenerate: `OSReconstruction/ReflectionKernel.lean` proves
  `osBilin_sub_theta_self_eq_zero` — `θ(F − θF) = −(F − θF)` turns `⟨G,G⟩ = ω(θG·G)` into
  `−ω(G²)`, so state positivity (`IsPositiveFunctional`) and reflection positivity squeeze it to
  `0` — and hence `mk_thetaObs_eq_mk : [θF] = [F]` **in `𝔄/𝔑`**.  Under full-algebra positivity the
  reflection is the identity on `ℋ` and the reconstruction has no time direction left; that is
  exactly the failure `𝔄₊` avoids, since there `F` and `θF` live in different algebras and the
  argument does not apply.  The `PhysicalSpace`–`HilbertSpace` chain still assumes the
  full-algebra form (it is the form the quotient construction consumes); rebuilding it on
  `𝔄₊/𝔑` — which also needs “`T_τ` preserves `𝔄₊`” as an explicit hypothesis — is the open work,
  and `IsReflectionPositive.isReflectionPositiveOn` records that the half-space form follows from
  the one in place.
  The *mechanism* is momentum space, not a factorisation of the state.  `isReflectionPositiveOn_of_factorization`
  is only the **uncorrelated** (white-noise) case: it needs the two halves to be independent,
  `ω(θF · G) = ωF · ωG`, which a free field with a nonzero propagator does not satisfy.  The
  correlated theorem is `OSReconstruction/MomentumBasis.lean`:
  `dft_mul_eq_convolution` proves that a product of fields at a lattice site is a convolution of
  their momentum transforms (`𝓕(F·G) = n⁻¹ • (𝓕F ⋆ 𝓕G)`, the finite-torus twin of
  `NsAdvectionConvolution.fourier_mul_eq_convolution`), and `reflection_positivity_momentum`
  proves that a reflected two-point kernel in transfer-factorised (Källén–Lehmann) form
  `K(x,y) = ∑ i, w i * u i x * conj (u i y)`, `w i ≥ 0` — which is what the momentum modes
  `u_k(t,x) = ρ_k^t χ_k(x)` supply — has an OS form that is a weighted sum of modulus squares,
  hence nonnegative.  Pointwise positivity of the momentum symbol is **not** enough: what the
  half-space does is turn the reflected covariance into the transfer kernel above — its modes
  live on the half-space, where `C(θx − y)` factorises — and that factorisation is what produces
  the squares.  That is the precise content the earlier wording got wrong.  Still missing is the Gaussian/Wick step from this
  two-point form to all polynomial observables: the corpus has `mehlerMeasure4D` on spacetime but
  no measure on the lattice configurations `Fin latticeDim → ℝ`.
* **Bounded Hamiltonian → unbounded Hamiltonian (SIRK), and the one remaining input.**  The
  Källén–Lehmann factorization is now a theorem, not a supplied kernel:
  `MomentumBasis.freePropagator_reflect_eq_transfer` proves that the reflected free propagator on
  the future half-space equals `transferKernel (freeMode mom ρ) w`, and `freeOSForm_eq_momentum`
  identifies its OS form with the modulus-square sum.  The bounded → unbounded step is wired
  through the SIRK chapters: `compressed_flow_tendsto` (pointwise) and `compressed_flow_transfer`
  (locally uniform in `t`) compose `compressed_hamiltonian_tendsto` with
  `ChapterSirkTrotterKatoGalerkin.flow_tendsto_of_strong_tendsto`, so the lattice Hamiltonians'
  flows converge to the flow of the exact operator read as the unbounded `ofBounded A`;
  `bounded_flow_tendsto_unbounded` states the genuinely unbounded case — strong resolvent
  convergence of the bounded approximations to an unbounded self-adjoint `T` gives convergence of
  their flows to `T`'s (Trotter–Kato).  `compressed_strongResolventConvergence` closes the SIRK
  resolvent hypothesis for the compressions (strong operator convergence of contractions implies
  strong resolvent convergence), and `galerkin_strongResolventConvergence` /
  `galerkin_compressed_flow_tendsto` instantiate it with a **common-space nested block/Galerkin
  refinement**: the orthogonal projections onto the spans of a Hilbert basis are contractions
  converging strongly to the identity (`galerkinProj_tendsto`), and `galerkinCompression` is
  exactly `Pₘ A Pₘ`.  **Still not instantiated with `BalabanRG.blockAveragingOp` itself:** that
  operator is `Sector k → Sector (k+1)` at a *fixed* block partition, so it is not a common-space
  refining family; `blockAveragingOp_norm_le` supplies only the contraction.  The Galerkin
  instantiation is the same construction over a partition that actually refines.
* **Hilbert-space assembly.**  Done, in `OSReconstruction/HilbertSpace.lean`:
  `physForm` descends the OS form to `Observable ⧸ Radical Λ.ω` (`LinearMap.liftQ₂`),
  `physCore` is an `InnerProductSpace.Core` there — definiteness is a theorem, since
  `⟨F,F⟩ = 0` puts `F` in the radical (`mem_radical_of_self_eq_zero`) — and
  `physInnerProductSpace` is `InnerProductSpace.ofCore`.  `Hphys Λ` is
  `UniformSpace.Completion (Observable ⧸ Radical Λ.ω)` with Mathlib's completion instances, so it
  is a `HilbertSpace ℝ (Hphys Λ)`; `physNorm_mk` identifies the norm with `√⟨F,F⟩` on the dense
  subspace and `physNorm_eq_zero_iff` records that the seminorm is a norm.  The evolution
  descends (`Submodule.mapQ` + `radical_invariant`), is a contraction there
  (`physEvol_contractive`) and extends to `ℋ` by `LinearMap.extendOfNorm`, with
  `‖physEvolCompletion τ‖ ≤ 1` and agreement on the dense image (`physEvolCompletion_coe`).
  The reflection-positivity hypothesis is bundled as `OSState` precisely so that the norm
  instances are keyed on a first-order parameter rather than on a free proof term.
  **Still open:** functoriality of the construction (Phase 4.1's last sentence), and the
  instantiation of the generator — see the next bullet.
* **Spectral theorem / `emergent_hamiltonian_selfAdjoint` / `nonnegative`.**  The instruments are
  **proved in `BookProof`, not missing**: Stone's theorem in full generality
  (`Toolbox.ChapterStoneResolvent`–`ChapterStoneTheorem`: `UnboundedSelfAdjoint`, `stoneU`,
  `continuous_stoneU_apply`, `stone_bijection`); the Friedrichs extension with no boundedness
  hypothesis (`Toolbox.ChapterFriedrichsExtension.friedrichs_extension_exists_of_complete_explicit`); essential
  self-adjointness by Faris–Lavine (`Toolbox.ChapterFarisLavineCore.essentiallySelfAdjointOn_of_farisLavine`);
  the bridge from an extension to a unitary flow (`Toolbox.ChapterStoneBridge.exists_stone_flow_of_positive`,
  `_of_esa`); the spectral theorem in multiplication form for unbounded self-adjoint operators
  (`ChapterUnboundedSpectralModel.unbounded_multiplication_model_general`, `_separable`); and the
  contraction semigroup with its generator and spectral bound (`ChapterNonnegSemigroup`,
  `ChapterNonnegSemigroupGenerator`).  What is still needed is the *instantiation*: a densely
  defined symmetric, nonnegative operator built from the transfer matrix on `Hphys`
  (`ChapterNonnegSemigroupGenerator` wants a strongly continuous semigroup; a bare
  `TimeTranslation` is not one — strong continuity of `τ ↦ physEvolCompletion τ` is not
  available).  What is proved today is the semigroup law, contractivity in the OS norm, the
  descent to `𝔄/𝔑`, and the contractive extension to `ℋ`.

## MM0 emission: what this pipeline can and cannot carry

`cftproof.md`'s premise is that "the end goal is to convert everything to MM0".  For these
modules that goal is **not** reachable through `australVM/scripts/lean2mm0` as it stands, and no
artifact was emitted.  The reasons are in the emitter itself, not in the mathematics:

* `SOURCES` artifacts (the `*_certificate` files) are transpiled from a *pinned,
nanoda-verified lean4export NDJSON* and consist of Lean `def …_checked : Bool` computations over
scaled naturals plus `theorem …_verified : … = true := rfl`.  They live in the int64/DeltaNet
fragment (`docs/cic.mm0`: `tint`, `tprim`, `teq`, …).  The CFT modules prove no such
Bool-rfl certificate: they are `Prop`-valued statements about inner product spaces, `Quot`,
completions and Cauchy–Schwarz.
* `STATEMENTS` artifacts (the `*_7_8` file) assert *one* statement of record over imported
`metamath/set.mm0`.  The generator is not general — `generate_statement` evaluates the
quasi-Riemann bound from the export and writes a fixed set.mm shape with a pinned label table
(`SETMM_LABELS`).  set.mm has no inner product spaces, no completions, and no ℝ⁴, so
`physEvol_contractive` or `norm_physEvolCompletion_le` cannot be written in that language at all.
* There is also no export to transpile: generating the NDJSON requires a nanoda-verified
lean4export run of the module, which drags in all of Mathlib transitively, and the emitter's
`Export`/`Evaluator` only understand the int64 fragment (docs/lean4mm0.md §9.2).

The pipeline itself is green (`australVM` `python3 scripts/lean2mm0 check`: "generated MM0/MM1 in
sync with the pinned exports").  What would be needed to carry these statements is a third
artifact class — a statement-of-record target for analysis, i.e. a new MM0 theory with
inner-product-space primitives plus a generator that maps Lean statements into it.  Asserting
the CFT theorems as axioms over set.mm or over `cic.mm0` would emit files that type-check while
saying nothing, which is the one failure mode this pipeline is built to prevent.
* **Phase 5 (beta function, Legendre transform) and Phase 6 (3D CFT).**  Out of scope of this
  execution: they depend on the OS Hilbert space and on estimates about the effective action that
  are not formalized anywhere.

## Reproducing

```bash
cd timepiece
lake build BookProof.EuclideanFock4D.CoreBasis \
           BookProof.EuclideanFock4D.MehlerMeasure \
           BookProof.BalabanRG.MultiscaleSpace \
           BookProof.BalabanRG.BlockOperator \
           BookProof.BalabanRG.Convergence \
           BookProof.ReflectionPositivity.Involution \
           BookProof.ReflectionPositivity.HalfSpaceAlgebra \
           BookProof.ReflectionPositivity.Proof \
           BookProof.ReflectionPositivity.BlockCommute \
           BookProof.ReflectionPositivity.QuadraticWick \
           BookProof.ReflectionPositivity.FeynmanKac \
           BookProof.OSReconstruction.PhysicalSpace \
           BookProof.OSReconstruction.Hamiltonian \
           BookProof.OSReconstruction.HilbertSpace \
           BookProof.OSReconstruction.ReflectionKernel \
           BookProof.OSReconstruction.MomentumBasis \
           BookProof.OSReconstruction.Clustering
```

`BookProof.OSReconstruction.Clustering` is Phase 5's receiver: it proves that Euclidean clustering
at mass `m` is equivalent to the transfer operator's decay at rate `m` off the vacuum, that the
`O(4)` invariance transfers temporal decay to spatial decay at the same rate, and — since
2026-10-30 — that the decay gives a *separation*: the norm gap `1 − √C e^{−mτ}` of `I − T_τ`
(`osNorm_sub_evol_ge`) and the form gap `m(1 − ε)` of the effective generator `(I − T_τ)/τ`
(`genForm_ge_of_contraction`, `genForm_gap_of_clustering`), which is the `SpectralSeparation`
input of the Temple/SIRK chain in the bounded form the corpus can state (the unbounded generator
`H_phys` itself is not constructed — see Phase 4.2 above).

(`lake build BookProof` is the real gate: it builds the aggregate target over all 3,300 lines of
`BookProof.lean`'s imports and finishes green (`Build completed successfully (8863 jobs)` when this
note was last updated, 2026-10-30).  The per-module commands above are kept because they finish in
seconds, whereas the aggregate includes `BookProof/RoadmapAudit/ChapterRoadmapAudit.lean`, which
alone costs ~25 minutes of CPU.)

The dependencies of the new modules that live outside Mathlib are the corpus chapters
`BookProof.Toolbox.ChapterHermiteProductBasis` (the `L²(ℝᵈ)` Hermite basis) and
`BookProof.Toolbox.PhysHSGaussian` (the Gaussian and sphere measures), both pre-existing and
already imported by `BookProof.lean`.
