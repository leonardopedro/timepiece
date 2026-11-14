# The E3 reconstruction chain: state, carrier, generator, exponential

A standalone map of the half-space (Euclidean → OS → Hamiltonian) reconstruction actually formalised
in this repository, with the Lean name of every link and, at the end, the hypotheses that are still
inputs rather than theorems.

Scope: `cftproof.md` item **E3** ("reconstruct on the positive-time algebra and build forward
evolution"). Nothing here claims a continuum theory, an interacting infinite-volume state, or a
mass gap — the only infinite-volume object built is the ultralocal free-field *reference* measure
(§2.7). This page is a reading aid over `BookProof/OSReconstruction/HalfSpace*.lean`, not a new
result.

---

## 1. The chain at a glance

```text
  state ω                        ω θ-invariant, reflection positive on 𝔄₊, ω 1 = 1
    │                            HalfSpaceState
    ├─ OS form ⟪F,G⟫ = ω(θF·G)    hsBilin, hsBilin_symm
    ├─ null subspace 𝔑₊           HsRadical  (a subspace, not claimed an ideal)
    ├─ quotient 𝔄₊/𝔑₊             HsSpace, hsForm, hsForm_self_eq_zero_iff
    ├─ completion ℋ               Hhalf Λ = Completion (HsSpace Λ)
    ├─ vacuum Ω_OS = [1]          hsVacuum, hsVacuum_norm
    │
    ├─ evolution P(τ)             hsEvol → hsQuotMap → hsEvolCompletion (a CLM on ℋ)
    │                            P(0)=I, P(s+t)=P(s)P(t), contraction, P(τ)*=P(τ)
    ├─ generator A = −H           hsGenerator : ℋ →ₗ[ℝ] ℋ (LinearPMap, dense domain)
    │
    ├─ bounded H                  hsExpOp τ = NormedSpace.exp (τ • −H)
    │                            semigroup, symmetry, contraction, C⁰ at 0⁺, generator −H
    ├─ identification             P(τ) = e^{−τH} under the flow hypothesis (Grönwall)
    │
    └─ unbounded H                HsMulModel: P(τ) = e⁻¹ ∘ (mult. by e^{−τ f}) ∘ e
                                 flow laws + generator −M_f on {z | f·e z ∈ L²(ν)},
                                 that domain dense, and −M_f self-adjoint
```

Two carriers exist side by side: the **real** one above, and its complexification
(`HalfSpaceComplex`: `HhalfC`, `hsComplexForm`, `instHilbertSpaceHhalfC`) which is what the OS
theorem and `HilbertSpace ℂ` consumers use. The real OS form is the restriction of the complex one
(`hsComplexForm_ofReal`).

---

## 2. Link by link

### 2.1 The state and the OS form

| Link | Lean | Module |
| :--- | :--- | :--- |
| Half-space state | `HalfSpaceState` | `HalfSpaceState.lean` |
| OS form and its algebra | `hsBilin`, `hsBilin_apply`, `hsBilin_add_left`, `hsBilin_smul_left`, `hsBilin_symm` | same |
| Positivity, Cauchy–Schwarz, quadratic expansion | `hsBilin_self_nonneg`, `hsBilin_cauchy_schwarz`, `hsBilin_expand` | same |
| Null subspace | `HsRadical`, `mem_hsRadical_iff`, `mem_hsRadical_of_self_eq_zero` | same |
| Descent to the quotient | `hsBilin_well_defined`, `hsBilinMap`, `hsForm`, `hsForm_mk` | same |
| Quotient is an inner-product space | `hsPreCore`, `hsCore`, `hsInnerProductSpace`, `instSeminormedHsSpace` | same |
| Completion, vacuum | `Hhalf`, `hsVacuum`, `hsVacuum_norm` | same |

`HsRadical` is deliberately **not** called an algebra ideal: ideal stability of the null subspace is
never proved, and no consumer needs it.

### 2.2 Forward evolution

| Link | Lean | Module |
| :--- | :--- | :--- |
| `𝔄₊` is preserved by forward translation | `PreservesPositiveTime` | `HalfSpaceHilbert.lean` |
| Restricted evolution | `hsEvol`, `hsEvol_coe`, `hsEvol_zero`, `hsEvol_add` | same |
| Contractivity hypothesis on the OS form | `HsHinv` | same |
| Null space invariance, descent, contractivity | `hsRadical_invariant`, `hsQuotMap`, `hsQuotMap_contractive` | same |
| Extension to the completion | `hsEvolCompletion`, `hsEvolCompletion_coe` | same |
| All-time version (0 off `τ ≥ 0`) | `hsEvolCompletionFun`, `hsEvolCompletionFun_of_nonneg` | same |
| Semigroup laws | `hsEvolCompletion_zero`, `hsEvolCompletion_add`, `hsEvolCompletionFun_comp` | same |
| Strong continuity at `0⁺` | `tendsto_hsEvolCompletionFun` | same |
| `P(τ)* = P(τ)` | `HsSymmetric`, `hsEvolCompletion_isSelfAdjoint` | same |

### 2.3 The generator

| Link | Lean | Module |
| :--- | :--- | :--- |
| Difference quotient | `hsDiffQuot` (+ additivity, homogeneity) | `HalfSpaceGenerator.lean` |
| One-sided domain, value, generator | `HsHasGen`, `hsGenDomain`, `hsGenValue`, `hsGenerator` | same |
| Closedness, dissipativity, resolvent bound | `hsGenerator_isClosed`, `hsGenerator_inner_le_zero`, `hsGenerator_resolvent_bound` | same |
| Integral representation of the orbit | `hsEvol_sub_eq_integral`, `tendsto_average_hsEvol` | same |
| `H = −A` (conditional on the flow) | `hsGenerator_eq_neg`, `hsGenerator_inner_eq_neg` | same |

Surjectivity of `λ − A` (the range condition of Lumer–Phillips) is **not** proved here; it is the
multiplier model's job (`range_sub_generatorRight_mulModel` in `MultiplierGenerator.lean`).

### 2.4 The bounded exponential

`BookProof/OSReconstruction/HalfSpaceExponential.lean`, for `H : Hhalf Λ →L[ℝ] Hhalf Λ`:

| Property | Lean |
| :--- | :--- |
| Definition, `exp(τ • −H)` | `hsExpOp`, `hsExpOp_apply` |
| `P(0) = I` | `hsExpOp_zero` |
| `P(s+t) = P(s)P(t)` | `hsExpOp_add` (via `commute_smul_neg`) |
| `P(τ)* = P(τ)` for self-adjoint `H` | `hsExpOp_isSelfAdjoint` |
| Operator derivative `P'(τ) = P(τ)·(−H)` | `hasDerivAt_hsExpOp` |
| Orbit derivative `−H(P(τ)z)` | `hasDerivAt_hsExpOp_apply` |
| `d/dτ P(τ)z = −H z` at `0⁺`, all `z` | `hsExpOp_hasDerivWithinAt_zero` |
| Contractivity for `0 ≤ ⟪H z, z⟫` | `norm_hsExpOp_antitone`, `norm_hsExpOp_le` |
| Continuity, strong continuity at `0⁺` | `continuous_hsExpOp`, `tendsto_hsExpOp_zero` |

The last "generator" row is exactly the shape `hsGenerator_eq_neg` consumes, so that hypothesis is
non-vacuous.

### 2.5 The identification (bounded case)

`BookProof/OSReconstruction/HalfSpaceExpIdentification.lean`. Under the flow hypothesis `hflow`
(`∀ z, HasDerivWithinAt (fun τ => hsEvolCompletionFun Λ hT hinv τ z) (−H z) (Ioi 0) 0`):

| Step | Lean |
| :--- | :--- |
| Semigroup commutes with `H` (`A P(τ) = P(τ) A`) | `hsEvolCompletionFun_comp_neg` |
| Orbit derivative `−H(P(τ)z)` at every `τ ≥ 0` | `hasDerivWithinAt_hsEvol_flow` |
| **`P(τ)z = e^{−τH}z`** (Grönwall on `v' = −H v`, `v(0)=0`) | `hsEvolCompletionFun_eq_hsExpOp` |
| Generator is `−H` **and** the flow is the exponential | `hsGenerator_eq_neg_exp` |
| `hflow` ⟺ `P` is the exponential | `hsExpOp_iff_flow` |

So `hflow` is not extra information about the flow: it determines it completely.

### 2.6 The unbounded case (multiplier model)

`BookProof/OSReconstruction/HalfSpaceUnboundedExp.lean`, built on `L2Multiplier`
(`expFlow`, `expFlow_comp`, `expFlow_contractive`, `tendsto_expFlow_slope`). The datum
`HsMulModel Λ X` is a measure `ν`, a measurable `f ≥ 0` a.e., and an **isometric equivalence**
`e : Hhalf Λ ≃ₗᵢ[ℝ] L²(ν)`.

| Property | Lean |
| :--- | :--- |
| Natural domain `{z | f · e z ∈ L²(ν)}` | `HsMulModel.domain` |
| The operator on it (`e w = −f · e z`) | `HsMulModel.opValue`, `e_opValue`, `opValue_congr` |
| The flow `e⁻¹ ∘ e^{−τf} ∘ e` | `HsMulModel.flow`, `flow_apply` |
| `P(0) = I`, `P(s+t)=P(s)P(t)`, contraction | `flow_zero`, `flow_comp`, `flow_contractive` |
| Strong continuity at `0⁺` (on the domain) | `flow_tendsto` |
| **Generator statement** `d/dτ P(τ)z = −M_f z` at `0⁺` | `hasDerivWithinAt_flow` |
| Domain is everything when `f` is bounded | `mem_domain_of_bounded` |

This is the honest meaning of "`e^{−τH}` for unbounded `H`": `NormedSpace.exp` is never applied to an
unbounded operator; the exponential *is* the multiplier `e^{−τf}`, transported along `e`.

### 2.6b Domain density and self-adjointness

`BookProof/OSReconstruction/HalfSpaceMultiplierAdjoint.lean`, for **every** measurable real `f` — no
boundedness, no positivity, no flow:

| Property | Lean |
| :--- | :--- |
| `‖v‖² = ∫ v²` on `L²(ν)` | `norm_sq_eq_integral` |
| Truncations `1_{|f| ≤ n}·u` lie in the domain | `truncFun_f_memLp` |
| …and converge to `u` in norm | `tendsto_truncFun_toLp` |
| **The domain is dense in `Hhalf Λ`** | `dense_domain` |
| The operator on its domain, as a `LinearPMap` | `hamiltonian`, `e_hamiltonian` |
| Matrix elements as integrals | `inner_hamiltonian_left`, `inner_hamiltonian_right` |
| Symmetry | `isFormalAdjoint_hamiltonian` |
| `dom H† ⊆ dom H` (comparison multiplier `(1+|f|)⁻¹`) | `mem_domain_of_mem_adjoint_domain` |
| `H† ≤ H`, then `H ≤ H†` by symmetry + density | `le_adjoint_hamiltonian` |
| **`H` is self-adjoint** | `hamiltonian_isSelfAdjoint` |

Mechanism: with `φ = (1 + |f|)⁻¹`, `f φ` is bounded by one, so `e⁻¹ (φ · u) ∈ dom H` for every
`u ∈ L²`; the adjoint relation `⟪w, g⟫ = ⟪v, H g⟫` then says `∫ u · (φ(e w) + φ f (e v)) = 0` for all
`u`, and testing on the bracket itself forces `f · e v = −(e w)`. So `HsMulModel` is now a
self-adjoint Hamiltonian, not merely a symmetric one; what it still assumes is the identification of
the carrier with `L²(ν)`.

### 2.7 The concrete state and its reflection positivity

| Link | Lean | Module |
| :--- | :--- | :--- |
| Finite-volume Gibbs functional | `gibbsFun`, `gibbsFun_one`, `gibbs_reflectionPositive`, `gibbsHalfSpaceState` | `HalfSpaceFreeState.lean` |
| State as a measure on `Config` | `gibbsAtom`, `gibbsMeasure` | same |
| Integral split of the measure | `integral_splitMap_gffConfigMeasure` | `HalfSpaceSplit.lean` §8 |
| OS form nonnegative | `gffConfigMeasure_osForm_nonneg` | same |
| Reflection positivity of the state | `gffConfigMeasure_isReflectionPositive` | same |
| Infinite-volume free-field state | `freeFieldInfinite`, `freeFieldInfinite_isProbability` | `HalfSpaceInfiniteVolumeGaussian.lean` |
| It *is* the Ionescu–Tulcea measure | `freeFieldInfinite_eq_infinitePiNat` | same |
| Cylinder marginals | `freeFieldInfinite_restrict`, `freeFieldInfinite_pi` | same |
| One-block pushforward | `blockProj`, `map_blockProj_freeFieldInfinite` | same |
| Its reflection positivity | `splitFreeField`, `chainReflect`, `posCylinder`, `posCylinder_reflectionPositive` | `HalfSpaceInfiniteVolumePositivity.lean` |
| Non-diagonal covariance pushforward | `corrMap`, `corrLaw`, `corrLaw_cov`, `corrLaw_var` | `HalfSpaceCovariancePushforward.lean` |
| Covariance is a multiple of `(−Δ+m²)⁻¹` | `covMatrix_hsNormSq`, `covMatrix_eq_lapInv` | same |
| Banded `n`-site covariance | `chainMap`, `chainLaw`, `chainLaw_cov` | `HalfSpaceChainCovariance.lean` |
| Bandedness (zero off `{i, σ i, σ⁻¹ i}`) | `chainCov_eq_zero`, `chainCov_diag` | same |
| Hilbert–Schmidt norm on the `(n+1)`-cycle | `chainCov_hsNormSq`, `cycleChain_cov_hsNormSq` | same |
| RP on general positive-time cylinders | `map_pi_prod_pi`, `posCyl`, `posCyl_reflectionPositive` | `HalfSpaceInfiniteVolumePositivity.lean` |
| RP for a *coupled* (covariant) state | `covState`, `covState_reflectionPositive` | `HalfSpaceCovariantReflectionPositivity.lean` |
| Covariance matrix of the coupled state | `shiftCov`, `covState_cov_fst_fst`, `covState_cov_snd_snd`, `covState_cov_fst_snd` | `HalfSpaceCovStateCovariance.lean` |
| Its blocks are `[[Cov T + 1, Cov T], [Cov T, Cov T + 1]]` | same three, plus `memLp_eval_chainLaw` | same |
| Banded *coupled* state (off-diagonal block `chainCov`) | `covState_chainLaw_cov_fst_snd`, `covState_chainLaw_cov_fst_snd_eq_zero` | same |
| Width-`k` band state and covariance | `bandMap`, `bandLaw`, `bandLaw_cov` | `HalfSpaceChainBandCovariance.lean` |
| Width-`k` bandedness (zero off `{σ^d i : \|d\| ≤ k}`) | `bandCov_eq_zero` | same |
| Diagonal `1 + ρ²k`, and `k = 1` is `chainCov` | `bandCov_diag`, `bandCov_one` | same |
| Banded *coupled* state, width `k` | `covState_bandLaw_cov_fst_snd`, `covState_bandLaw_cov_fst_snd_eq_zero` | same |

### 2.7b The one-sided semigroup, and a step that inhabits it

`TimeTranslation` is `ℝ`-indexed, and §4.1.1 records why no lattice step can instantiate it. The API
is therefore weakened to an `ℕ`-indexed semigroup — the shape a lattice transfer matrix has — and
the weakened version is inhabited by a concrete step.

| Link | Lean | Module |
| :--- | :--- | :--- |
| One-sided semigroup | `DiscreteTimeTranslation` (`map_zero`, `map_add`), `discreteTimeTranslation_semigroup` | `HalfSpaceDiscreteSemigroup.lean` |
| Old API embeds in the new one | `ofTimeTranslation`, `hsEvolNat_ofTimeTranslation`, `hsHinvNat_of_hsHinv` | same |
| Support at integral times | `PreservesPositiveTimeNat`, `hsEvolNat` (+ `_zero`, `_add`) | same |
| Contractivity hypothesis | `HsHinvNat` | same |
| Null space, quotient, contraction | `hsRadical_invariantNat`, `hsQuotMapNat` (+ `_contractive`, `_zero`, `_add`) | same |
| The concrete step | `cellHalfRotate`, `siteHalfRotate`, `isPosTime_siteHalfRotate_pow_iff` | `HalfSpaceLatticeShiftSemigroup.lean` |
| **`PreservesPositiveTimeNat` holds** | `preservesPositiveTimeNat_halfRotateTranslation` | same |
| Step commutes with the reflection | `siteHalfRotate_reflectCoord`, `siteHalfRotate_pow_reflectCoord`, `thetaObs_obsHalfRotate` | same |
| Gibbs functional is step-invariant | `gibbsFun_obsHalfRotate` (given `IsHalfRotateInvariant V`) | same |
| **`HsHinvNat` for the Gibbs state** | `hsHinvNat_gibbsHalfSpaceState` (an equality) | same |
| An explicit invariant grid | `constGrid`, `mem_constGrid`, `isHalfRotateInvariant_constGrid` | same |
| **`HsHinvNat` with no hypothesis** | `hsHinvNat_constGrid`, `constGrid_transfer_contractive` | same |

### 2.8 The complex carrier

| Link | Lean | Module |
| :--- | :--- | :--- |
| Complexification | `HhalfC` | `HalfSpaceComplex.lean` |
| Complex OS form, its definiteness, restriction | `hsComplexForm`, `hsComplexForm_self_eq_zero_iff`, `hsComplexForm_ofReal` | same |
| Complex inner-product structure and completeness | `hsComplexPreCore`, `hsComplexSeminormed`, `instInnerProductSpaceHhalfC`, `instHilbertSpaceHhalfC` | same |

---

## 3. The hypothesis ledger

Everything below is an **input**. None of it is derived from lattice data anywhere in the corpus;
each line says what it is and what would discharge it.

| Hypothesis | Where | What it says | Discharged by |
| :--- | :--- | :--- | :--- |
| `PreservesPositiveTime T` | `HalfSpaceHilbert` | forward translation keeps `𝔄₊` inside `𝔄₊` | proving the support statement for the chosen `T` |
| `HsHinv Λ hT` | `HalfSpaceHilbert` | the OS form is contractive along `𝔄₊` at `τ ≥ 0` | a concrete state with that estimate |
| `HsSymmetric Λ hT` | `HalfSpaceHilbert` | dense two-point symmetry of the evolution | a reflection-invariant state and an explicit computation |
| `hcont` (matrix-element continuity) | `HalfSpaceHilbert`, `HalfSpaceExpIdentification` | `τ ↦ ω(θ(T τ F)·F)` continuous at `0` | the OS time-translation axiom, for the concrete state |
| `hflow` | `HalfSpaceGenerator`, `HalfSpaceExpIdentification` | `d/dτ P(τ)z = −H z` at `0⁺` | the identification itself: `hsExpOp_iff_flow` shows it holds iff `P = e^{−τH}` |
| `HsMulModel` datum (`ν`, `f`, `hf`, `hpos`, `e`) | `HalfSpaceUnboundedExp` | the carrier *is* `L²(ν)` and the Hamiltonian is multiplication by `f` | producing that isometry for the concrete half-space theory (density and self-adjointness no longer need it, §2.6b) |
| `MemLp (f · e z)` | `HalfSpaceUnboundedExp` | the vector lies in the unbounded operator's domain | automatic when `f` is bounded (`mem_domain_of_bounded`) |
| `IsHalfRotateInvariant V` | `HalfSpaceLatticeShiftSemigroup` | the declared finite grid of half-configurations is closed under the cell rotation | satisfied by every grid invariant under a permutation of `HalfIdx`; no such grid is constructed in the corpus |

---

## 4. What is *not* established

1. **An infinite-volume *interacting* or continuum state.** The free-field *reference* state now
   exists: `HalfSpaceInfiniteVolumeGaussian.freeFieldInfinite` is `ℕ` independent blocks of
   `freeFieldMeasure`, i.e. the ultralocal free field, with its Ionescu–Tulcea identification and its
   one-block marginal proved. What is still missing is (i) any coupling between blocks — the state's
   covariance is the identity, not `(−Δ+m²)⁻¹`, whose Hilbert–Schmidt square root is the route of
   §4.2.3 item 5 — and (ii) any relation to the interacting state:   `gibbsMeasure` is supported on the
   declared finite grid, is not a marginal of `freeFieldInfinite`, and `gibbsFun` is the mass
   (ultralocal) functional, not the nearest-neighbour one.  Reflection positivity *on that reference
   state* is proved for positive-time cylinder observables (`HalfSpaceInfiniteVolumePositivity`).
2. **The carrier identification `Hhalf Λ ≃ₗᵢ L²(ν)`.** Density of the domain and self-adjointness of
   the multiplication operator *are* proved (`HalfSpaceMultiplierAdjoint`, §2.6b), for any measurable
   real `f`. What remains an input is that the half-space carrier is the multiplier `L²(ν)` at all;
   constructing that isometry for the concrete theory is the open step, and it is what
   `MultiplierSelfAdjoint.MulModel` replaces by a dense-range isometry plus the multiplier law.
3. **Surjectivity of `λ − A`** on the half-space carrier (Lumer–Phillips' range condition); only the
   a priori estimate and injectivity are proved in `HalfSpaceGenerator`.
4. **Matching the abstract translation with the concrete lattice one**, i.e. deriving `hflow` from
   `T` rather than assuming it — see the audit below.
5. **Separability of the complexified carrier** and the unitarity `ℋ_OS → ℱ_out` (B2/B3): untouched.

### 4.1 `hflow`: the lattice shift, and the two-point form

`hflow` is a statement about two inputs of the E3 modules: the semigroup `P` (built from a
`TimeTranslation T`) and a bounded operator `H`.

#### 4.1.1 The concrete lattice translation, and why it cannot satisfy the hypothesis

`TimeTranslation` (`Hamiltonian.lean:56`) is an abstract structure — `toFun : ℝ → Observable →ₗ
Observable` with the group laws — and the repository contained no instance.  It now has the
concrete lattice candidate, `BookProof/OSReconstruction/HalfSpaceLatticeTranslation.lean`:
`cellRotate = finRotate cellsPerBlock` rotates the 16 cells of a block, `siteShift` lifts it to
sites (keeping the field component `μ`), and `obsShiftₗ k` (`k : ℤ`) precomposes with
`siteShift ^ k`.  It is an automorphism of the observable algebra: `obsShift_add` (group law),
`obsShift_zero`, `obsShift_mul`, `obsShift_one`, `obsShift_comp_neg`.

Two things follow, and both are theorems rather than caveats:

1. **No `TimeTranslation` can be this shift.**  The lattice supplies a `ℤ`-action (on one block,
   in fact `ℤ/16`), while `TimeTranslation` is `ℝ`-indexed; there is no nontrivial homomorphism
   `ℝ → ℤ/16`.  So `obsShift` is the concrete translation, but it is not an instance of the
   corpus's type.
2. **`PreservesPositiveTime` is false for it.**  The hypothesis quantifies over *all* real `τ`, and
   it already fails at `τ = 1`: the last positive-time cell (`7`) is rotated onto the first
   negative-time cell (`8`).  `cellRotate_lastPos` records the step, and
   `not_preservesPositiveTime_of_shift` proves that any `TimeTranslation` whose time-one map is the
   shift fails the hypothesis; `obsShift_one_not_mem_positiveTime` is the concrete witness
   (the coordinate functional at the last positive-time site maps outside `𝔄₊`).

So step 1 of the earlier decomposition ("give the concrete `T` and prove `PreservesPositiveTime`")
was **not achievable as stated**: the correct statement is the one-sided semigroup `τ ≥ 0` on a
half-infinite direction, which is exactly the hypothesis `HsHinv` already restricts to.  Instantiating
`hsEvol` for all `τ` therefore requires either an infinite/half-infinite lattice (absent) or a
change of the API to a one-sided semigroup.  That is an API decision, recorded here, not a proof
obligation.

#### 4.1.2 What `hflow` still needs

The remaining decomposition is:

1. identify `P` with the concrete transfer semigroup (definitional, once a suitable `T` exists);
2. prove `H` is the generator of `P` — the spectral/Stone step, currently available only in the
   multiplier model (`HalfSpaceMultiplierAdjoint.hamiltonian_isSelfAdjoint`), which assumes the
   carrier identification rather than producing it.

Step 2 is where `hflow` actually lives, and `hsExpOp_iff_flow` shows the hypothesis is not a side
condition that can be checked independently: under the standing assumptions it holds **iff**
`P τ = e^{−τH}`.  Deriving it from `T` would mean constructing the Hamiltonian's spectral
decomposition from the translation group — Stone's theorem for this OS quotient, i.e. the B2/B3
work.

The weaker target that *is* provable is now proved, in
`BookProof/OSReconstruction/HalfSpaceFlowMatrixElement.lean`:

* `hasDerivWithinAt_inner_hsEvol` — `hflow` implies that every scalar orbit
  `τ ↦ ⟪y, P τ z⟫` has right derivative `⟪y, −H z⟫` at `0⁺` (via `HasDerivWithinAt.inner`);
* `tendsto_slope_inner_hsEvol` — the same in slope form.

The converse is not merely unproved but **false from these data**: weak convergence plus a uniform
norm bound does not give strong convergence (`e_n` in `ℓ²` is weakly null with `‖e_n‖ = 1`).  So the
two-point form cannot replace `hflow`; recovering it needs the semigroup's continuity in `τ`, which
is the Stone content above.

### 4.2 What an infinite-volume state would require (survey)

This section is a survey, not a report of work in progress: **no infinite-volume state exists in
this corpus, and the carrier is not even the right shape for one.**  The inventory below says what
is missing where, so that the next attempt starts from the right end.

#### 4.2.1 Where the corpus stops

`gibbsMeasure (V : GibbsVolume)` is a finite sum of Diracs on the *fixed* carrier
`Config = Fin latticeDim → ℝ` (`latticeDim = 64`), with atoms `configEquiv.symm (x, y)` and weights
`w x · w y` supported on `V.support × V.support`; `freeFieldMeasure` is
`Measure.pi (fun _ : Fin latticeDim => gaussianReal 0 ⟨1/2, _⟩)`, a product Gaussian on that same
block.  The module's own boundary note states that no infinite-volume limit is claimed.

Two structural points, both decisive:

* **Varying the volume does not vary the space.**  Every `gibbsMeasure V` is a measure on the same
  `Config`; `V` changes only the finite grid of atoms, not the lattice.  An infinite-volume limit
  needs a *different* carrier per region plus restriction maps between them; there is no such
  family here, so there is not even a candidate projective system.
* **No countable lattice exists in the corpus.**  The block is `Fin latticeDim`, one block of 16
  cells; `IsProjectiveMeasureFamily`/`IsProjectiveLimit` are about `Π i : ι` for an index type `ι`
  (in the usable instance, `ι = ℕ`).

#### 4.2.2 What Mathlib already supplies

Contrary to the impression the corpus's silence gives, the measure-theoretic backbone is largely
present:

| Mathlib API | use |
| :--- | :--- |
| `MeasureTheory.Measure.pi` (`Constructions/Pi.lean`) | product measures — but `[Fintype ι]` only, so it cannot build an infinite product |
| `IsProjectiveMeasureFamily`, `IsProjectiveLimit` (`Constructions/Projective.lean`) | the consistency predicate for `P : ∀ J : Finset ι, Measure (Π j : J, α j)`, with `congr_cylinder` / `measure_univ_eq` for checking it |
| `projectiveFamilyContent` (`Constructions/ProjectiveFamilyContent.lean`) | a content on measurable cylinders from a consistent family, with `projectiveFamilyContent_iUnion_le` (the countable-subadditivity step of a Carathéodory extension) |
| `closedCompactCylinders` (`Constructions/ClosedCompactCylinders.lean`) | compact closed cylinders, the regularity input an extension theorem needs |
| `MeasureTheory.traj`, `isProjectiveLimit_trajFun` (`Probability/Kernel/IonescuTulcea/Traj.lean`) | the Ionescu–Tulcea construction: from Markov kernels `κ n : Kernel (Π i : Iic n, X i) (X (n+1))` an actual measure on `Π n, X n`, with its finite-dimensional marginals proved (`isProjectiveLimit_trajFun`, and `isProjectiveLimit_nat_iff` to check limits on `Iic n` only) |
| `ProbabilityTheory.gaussianReal` | the one-dimensional Gaussian, so independent Gaussian coordinates are available |
| `MeasureTheory.IsGaussian` (`Probability/Distributions/Gaussian/Basic.lean`) | a *predicate* on measures on a Banach space (continuous linear images are Gaussian), not an existence theorem for a prescribed covariance |
| `instCompactSpace_probabilityMeasure` (`Measure/Prokhorov.lean`) | `ProbabilityMeasure E` is compact when `E` is compact — the compactness input for a limit-point argument on states |

So "Mathlib has no Kolmogorov extension" is **false as stated**; what Mathlib has is an extension
theory *conditional on consistency*, plus the countable Ionescu–Tulcea machine.  The earlier version
of this section said otherwise and is corrected here.

#### 4.2.3 The actual obstructions, in order of difficulty

1. **No projective system.**  To apply the table above one needs (i) a countable index `ι` (e.g.
   `ℤ^3` or `ℕ`), (ii) a finite carrier `Π i : Λ, ℝ` per finite `Λ ⊆ ι`, (iii) restriction maps
   `Π i : Λ', ℝ → Π i : Λ, ℝ` for `Λ ⊆ Λ'`.  None of the three exists; `Config` is a single block
   and `HalfIdx` is a fixed finite type.
2. **The Gibbs family is not consistent.**  With free boundary conditions the marginal of
   `μ_{Λ'}` on `Λ` is not `μ_Λ` (the two actions and normalizations differ), so
   `IsProjectiveMeasureFamily` fails.  With a fixed boundary condition it holds only along nested
   volumes sharing that boundary, i.e. the family is indexed by the boundary, not by the volume.
   This is the standard reason the interacting infinite-volume object is a *DLR measure* rather than
   a projective limit, and the corpus has **no DLR/Gibbs-specification notion at all**.
3. **To get a limit without consistency** one needs compactness of the state space: a limit point of
   `{ω_Λ}` in the weak-`*` topology, then DLR verification.  `ProbabilityMeasure E` is compact only
   for compact `E`, so this needs a compactification of `ℝ^ι` (product of one-point
   compactifications, or the closed ball of `WeakDual`), and the observables would have to be
   restricted to bounded cylindrical functions — `IsReflectionPositiveOn` here quantifies over *all*
   `Observable = Config → ℝ`, which is not a Banach space at all.
4. **Transfer of OS positivity.**  Reflection positivity is a closed condition, so a limit point of
   reflection-positive finite-volume states is reflection positive *provided* the limit is taken in a
   topology making `F ↦ ω(θF · F)` continuous — that step is plausible but needs the bounded-cylinder
   restriction of item 3, and then the OS form's domain changes.
5. **The free field is genuinely easier, and is the right first target.**  Its covariance is known,
   so no consistency proof is needed: build independent `gaussianReal 0 1` coordinates on `ℕ` through
   Ionescu–Tulcea with constant kernels (the countable product that `Measure.pi` cannot give), then
   push forward by the square root of the covariance.  The pushforward is a Gaussian measure exactly
   when that square root is Hilbert–Schmidt (trace-class covariance), which holds for `(−Δ+m²)⁻¹`
   in dimension `d ≥ 2`.  **The first half of this is now done**
   (`HalfSpaceInfiniteVolumeGaussian`): the countable product of the block laws exists, is a
   probability measure, coincides with Mathlib's explicit Ionescu–Tulcea tower
   (`freeFieldInfinite_eq_infinitePiNat`), and its one-block marginal is `freeFieldMeasure`
   (`map_blockProj_freeFieldInfinite`).  **Still missing**: the Hilbert–Schmidt pushforward by the
   square root of a *non-diagonal* covariance.  With independent blocks the covariance is the
   identity, so the construction gives the ultralocal free field; the massive covariance
   `(−Δ+m²)⁻¹` would need the off-diagonal kernel expressed as a Hilbert–Schmidt operator and its
   square root applied to the product law.  **The two-site truncation of this is now done**
   (`HalfSpaceCovariancePushforward`): the Cholesky pushforward `p ↦ (p.1, ρ p.1 + s p.2)` of two
   unit Gaussians has covariance `ρ` off the diagonal and `1` on it (`corrLaw_cov`, `corrLaw_var`),
   its covariance matrix has finite Hilbert–Schmidt norm `2 + 2ρ²` (`covMatrix_hsNormSq`), and for
   `ρ = 1/(1+m²)` it equals `λ • (−Δ+m²)⁻¹` entrywise (`covMatrix_eq_lapInv`).  What is still missing
   is the *chain* case: an infinite covariance operator and its square root, which Mathlib cannot
   supply (there is no multivariate Gaussian pushforward, only `IsGaussian` transport).
   **The `n`-site chain is now built** (`HalfSpaceChainCovariance`): the additive-neighbour
   pushforward `Y i = X i + ρ X (σ i)` of white noise has covariance
   `δ_{ij} + ρ(δ_{σ i,j} + δ_{i,σ j}) + ρ²δ_{ij}` (`chainLaw_cov`), which *vanishes off the band*
   `{i, σ i, σ⁻¹ i}` (`chainCov_eq_zero`) and has squared Hilbert–Schmidt norm
   `card ι · ((1+ρ²)² + 2ρ²)` (`chainCov_hsNormSq`), instantiated on the `(n+1)`-site cycle as
   `cycleChain_cov_hsNormSq`.  The honest caveat: this banded matrix is the nearest-neighbour
   *truncation* of `(−Δ+m²)⁻¹` (whose inverse is a chain Laplacian, hence a dense matrix), so only
   the two-site case is an exact `λ • (−Δ+m²)⁻¹`; and the chain is finite (a fixed `n`), so no
   infinite covariance operator is involved.
   **The band width is now arbitrary** (`HalfSpaceChainBandCovariance`): the pushforward by
   `1 + ρ ∑_{a=1}^{k} P_σ^a` has covariance
   `δ_{ij} + ρ ∑_a (δ_{σ^a i,j} + δ_{i,σ^a j}) + ρ² ∑_{a,b} δ_{σ^a i,σ^b j}` (`bandLaw_cov`),
   supported exactly on the band `{σ^d i : |d| ≤ k}` (`bandCov_eq_zero`), with diagonal `1 + ρ²k` on
   a site with no short cycle (`bandCov_diag`; the cyclic double sum counts `k` paths) and with the
   width-`1` case returning `chainCov` (`bandCov_one`).  Off-diagonal coefficients are
   `ρ + ρ²(k - d)` at distance `d`, not the single `ρ` of the width-`1` case, because `k - d` paths
   of length `d` overlap; the module records the vanishing pattern and the diagonal only.
   **The covariance matrix of the coupled state is now proved, not merely described**
   (`HalfSpaceCovStateCovariance`): for a shift law `ν` with second moments (`hν`), the blocks of
   `covState ν` are `Cov T + 1` on the diagonal (`covState_cov_fst_fst`, `covState_cov_snd_snd`) and
   `Cov T` off it (`covState_cov_fst_snd`), because a covariance only reads the marginal it uses
   (`covariance_fst_fst_prod`, `covariance_snd_snd_prod`).  Feeding in the chain law makes that
   statement concrete: the cross-covariance of the two halves of `covState (chainLaw σ ρ)` is
   `chainCov σ ρ` and vanishes off `{i, σ i, σ⁻¹ i}`
   (`covState_chainLaw_cov_fst_snd_eq_zero`), and the width-`k` version vanishes off the width-`k`
   band (`covState_bandLaw_cov_fst_snd_eq_zero`).  The coupled state is therefore banded, not
   diagonal — the coupling the earlier modules could only posit is now an equality.

Bottom line: the finite-volume OS estimates are the strongest statements available, and calling any
of them "the infinite-volume state" would be an overclaim.  The shortest honest route to a real
infinite-volume statement is item 5 (free field, via Ionescu–Tulcea plus a Hilbert–Schmidt
pushforward), not a projective limit of the interacting `gibbsMeasure` family.

---

## 5. Verification

```bash
export PATH="/home/leo/.elan/bin:$PATH"

lake build BookProof.OSReconstruction.HalfSpaceExponential      # bounded exponential
lake build BookProof.OSReconstruction.HalfSpaceExpIdentification # identification
lake build BookProof.OSReconstruction.HalfSpaceUnboundedExp     # unbounded (multiplier model)
lake build BookProof.OSReconstruction.HalfSpaceMultiplierAdjoint # density + self-adjointness
lake build BookProof.OSReconstruction.HalfSpaceLatticeTranslation # concrete shift, no PosTime
lake build BookProof.OSReconstruction.HalfSpaceFlowMatrixElement # two-point form of hflow
lake build BookProof.OSReconstruction.HalfSpaceDiscreteSemigroup  # one-sided API
lake build BookProof.OSReconstruction.HalfSpaceLatticeShiftSemigroup # inhabited step, HsHinvNat
lake build BookProof.OSReconstruction.HalfSpaceInfiniteVolumeGaussian # infinite-volume free field
lake build BookProof.OSReconstruction.HalfSpaceInfiniteVolumePositivity # RP on that state
lake build BookProof.OSReconstruction.HalfSpaceCovariancePushforward # non-diagonal covariance
lake build BookProof.OSReconstruction.HalfSpaceChainCovariance # banded n-site covariance
lake build BookProof.OSReconstruction.HalfSpaceCovariantReflectionPositivity # RP for a coupled state
lake build BookProof.OSReconstruction.HalfSpaceCovStateCovariance # covariance matrix of that state
lake build BookProof.OSReconstruction.HalfSpaceChainBandCovariance # width-k band covariance
lake build BookProof.OSReconstruction.HalfSpaceChainBandHSNorm # width-k off-diagonal coefficients
lake build BookProof.OSReconstruction.HalfSpaceInfiniteBandedCovariance # infinite-volume banded kernel

# axiom footprints — every theorem must be [propext, Classical.choice, Quot.sound]
lake env lean Work/HalfSpaceExponentialAudit.lean
lake env lean Work/HalfSpaceExpIdentificationAudit.lean
lake env lean Work/HalfSpaceUnboundedExpAudit.lean
lake env lean Work/HalfSpaceMultiplierAdjointAudit.lean
lake env lean Work/HalfSpaceLatticeTranslationAudit.lean
lake env lean Work/HalfSpaceFlowMatrixElementAudit.lean
lake env lean Work/HalfSpaceSplitAudit.lean
lake env lean Work/HalfSpaceDiscreteSemigroupAudit.lean
lake env lean Work/HalfSpaceLatticeShiftSemigroupAudit.lean
lake env lean Work/HalfSpaceInfiniteVolumeGaussianAudit.lean
lake env lean Work/HalfSpaceInfiniteVolumePositivityAudit.lean
lake env lean Work/HalfSpaceCovariancePushforwardAudit.lean
lake env lean Work/HalfSpaceChainCovarianceAudit.lean
lake env lean Work/HalfSpaceCovariantReflectionPositivityAudit.lean
lake env lean Work/HalfSpaceCovStateCovarianceAudit.lean
lake env lean Work/HalfSpaceChainBandCovarianceAudit.lean
```

Note on the direct `lean` invocations: the lakefile sets `maxSynthPendingDepth = 10`, which
`lake env lean <file>` does not pick up; add `-DmaxSynthPendingDepth=10` or build through `lake build`.
The three exponential modules also carry per-declaration `set_option synthInstance.maxHeartbeats`
overrides, because instance search through `Hhalf Λ = Completion (HsSpace Λ)` exceeds the default
budget.

Status at 2026-11-14: all sixteen audit files report `[propext, Classical.choice, Quot.sound]` only,
and all modules build with no `sorry` and no warnings from their own files. The nine later audits
(`HalfSpaceDiscreteSemigroup`, `HalfSpaceLatticeShiftSemigroup`, `HalfSpaceInfiniteVolumeGaussian`,
`HalfSpaceInfiniteVolumePositivity`, `HalfSpaceCovariancePushforward`, `HalfSpaceChainCovariance`,
`HalfSpaceCovariantReflectionPositivity`, `HalfSpaceCovStateCovariance`,
`HalfSpaceChainBandCovariance`) cover 10, 21, 5, 8, 8, 11, 3, 11, 8, 1 and 1 declarations
respectively.
