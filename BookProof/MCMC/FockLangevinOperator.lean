import Mathlib
import BookProof.MCMC.UnadjustedPCNGap
import BookProof.Toolbox.ChapterFockFieldPerturbation

/-!
# Chapter FockLangevinOperator — the drift as a finite-band hopping matrix

Plan: `pcnl.md`, Module 3.  §2.2 writes the pCNL transition operator as
`P_pCNL = P₀ + K_drift + K_reject`, where `P₀` is diagonal (`ρ^N`) and the drift is the
polynomial `−½β²∇Φ`.  In the Hermite/Fock basis a polynomial becomes a **finite combination of
ladder words** in `(a_j, a_j†)`, and a ladder word moves the occupation numbers of only the
modes it touches, by one per letter — so the drift is a *finite-band* matrix: a monomial of
degree `k` hops the total degree `N = ∑ i, nᵢ` by at most `k`.

This chapter makes that structural fact precise on the Gauss–polynomial core
`CoreCoeff d = (Fin d → ℕ) →₀ ℂ` of `BookProof.ReferenceGap`, whose degree function
`natDeg` and pCN weights `pcnWeight` are those of `BookProof.MCMC.UnadjustedPCN`.

## Contents

* `raiseIdx`, `lowerIdx`, `stepIdx` — `a_j†` and `a_j` as operations on occupations;
  `natDeg_raiseIdx` (`N ↦ N + 1`) and `natDeg_lowerIdx_le` (`N ↦ ≤ N`);
* `stepAmp` — the Hermite/Fock amplitude `√(n_j + 1)` of a raising step and `√(n_j)` of a
  lowering step, and `stepAmp_norm_le` — **on the degree-`≤ N` sector every step amplitude is at
  most `√(N + 1)`**, the growth the relative-bound argument of the plan's Module 3 needs;
* `hopStep`, `hopWord`, `driftOp` — one ladder step, a word of steps, and a finite family of
  words (the drift monomials) acting on the core;
* **`hopWord_band`** and **`driftOp_band`** — the finite-band property: a word of length `k` maps
  the sector `{N ≤ N₀}` into `{N ≤ N₀ + k}`, and a family of words of length `≤ K` into
  `{N ≤ N₀ + K}`;
* `numberOp` — the diagonal Fock number operator `N` on the core, whose support is unchanged, so
  that `numberOp + driftOp W` is the `pcnlHamiltonian` shape of the plan's milestone;
* **§5, the `ε`-regularized relative form bound** — `corePair` (the `ℓ²` pairing), `numberForm`
  (`⟪c, N c⟫`), `driftOpCoeff` (`K_drift = −Σ_j b_j ∂_j` with `∂_j = (a_j − a_j†)/√2` as a hopping
  operator), and  **`DriftFormBound`**, the plan's Module 3 target stated as a `Prop` with the
  plan's constant;
* **§6, the same bound proved** — `driftField` (the drift on the corpus Fock space,
  `creVec − annVec`), `abs_re_inner_driftField_le` (its `N^{1/2}` estimate) and
  **`driftField_relative_form_bound`**:
  relative bound zero against the number form, as a theorem, reusing
  `BookProof.FockFieldPerturbation`;
* **§7, the index identification** — `idxEquiv` (occupation vectors on `d` modes *are* finite
  multisets) and `natDeg_idxEquiv` (the grading is the particle number);
* **§8, the `Fin d` sector** — the other half of the identification: `reindex`,
  `sum_sq_reindex` and `numberForm_reindex` move the core `ℓ²` isometrically onto configuration
  vectors on multisets; `sectorVec` and `l2norm_sectorVec` embed a `Fin d` coupling as a
  one-particle vector on the first `d` modes, and `driftField_sector_relative_form_bound` is
  Module 3's bound with the `Fin d` constants; `InSector`, `numberQuad_eq_sum_fin` and
  `InSector.driftField` are the corresponding sector of the Fock model and its invariance under
  the drift;
* **§9.3, the mode calculus** — letters at distinct modes commute (`stepIdx_comm`,
  `hopStep_comm`, `mulHermite_comm`), so a word of multiplication laws depends only on the multiset
  of its modes (`mulHermiteList_perm`); `monomialList` is the mode list of a monomial, additive in
  the exponent (`monomialList_append_perm`, `mulHermiteList_monomialList_add,`
  `monomialList_single`);
* **§9.4, the polynomial interpolation** — `polyMul Φ`, the sum of the monomial word families of a
  potential, with `polyMul_add`, `polyMul_monomial`, `polyMul_X` (the dictionary: `X j ↦ mulHermite
  j`) and **`polyMul_mul`**: the operator is multiplicative, i.e. it is the polynomial's word
  expansion for *every* `Φ`, which is the `MvPolynomial` induction the plan recorded as missing;
* **§9.5, the derivative side** — `polyMul` applied to `MvPolynomial.pderiv`: `∂ⱼ Φ` is a finite
  sum of monomial word families with each exponent lowered by one in mode `j`
  (`polyMul_derivative`), spelled out as an explicit ladder-word family
  (`polyMul_derivative_eq_ladderWords`); `polyMul_C`/`polyMul_one` are the constant case and
  `polyMul_derivative_X` checks the dictionary at the generators, `∂ⱼ xₖ = δⱼₖ`;
* **§9.6, the band of a polynomial** — `polyMul Φ` maps the sector `{N ≤ N₀}` into
  `{N ≤ N₀ + K}` when `deg Φ ≤ K`: `mulHermite_band`, `mulHermiteList_band`,
  `monomialList_length` (a monomial's word family has one letter per unit of degree), and
  **`polyMul_band`** over `Φ.support` — finite band for *every* potential, not just a linear one;
* **§9.7, the drift of a polynomial potential** — `diffHermite` (the letter `∂ⱼ = (aⱼ − aⱼ†)/√2`),
  **`polyDrift`** as the composition `−Σⱼ polyMul (∂ⱼ Φ) ∘ ∂ⱼ`, its ladder-word family
  (`polyDrift_eq_ladderWords`, `polyDrift_eq_hopWords`), and
  `driftOpCoeff_eq_neg_sum_diffHermite`, which recovers §5's constant-coefficient drift;
* **§9.8, the band of the drift** — `diffHermite_band`, `natDeg_lowerExp` (a lowered exponent
  loses exactly one degree) and **`polyDrift_band`**: a potential of degree `≤ K` maps
  `{N ≤ N₀}` into `{N ≤ N₀ + K}`, the derivative's loss and the letter's gain cancelling, so
  `K_drift` has band `K` — the finite-band property for the drift itself, not only its factors;
* **§9.9, the size of the drift** — `coreL1` (the `ℓ¹` mass, with the triangle inequality in the
  forms the word family consumes), `hopStep_l1_le` and `hopWord_l1_sector` (a ladder word of length
  `k` multiplies the mass by at most `(√(M + 1))^k`, `M` bounding the degrees the word meets),
  and **`polyDrift_l1_le`**: `coreL1 (K_drift c) ≤ driftL1Bound Φ M * coreL1 c` with an explicit
  sector constant — `stepAmp_norm_le` combined with §9.8's band, the estimate §9.7 listed as
  missing;
* **§9.10, the pCNL Hamiltonian of a polynomial potential** — `pcnlPolyHamiltonian Φ =
  numberOp + polyDrift Φ`, with **`pcnlPolyHamiltonian_band`** (degree `≤ K`, so the sector
  `N₀ ↦ N₀ + K`: the same finite-band shape §4 gives for a word list, now for the drift operator
  itself) and `polyDrift_linear` (a linear `Φ` gives exactly §5's `driftOpCoeff b`);
* **§10, the `ℓ²` action of one letter** — the coordinates of `a_j` and `a_j†`
  (`hopStep_coord_lower`, `hopStep_coord_raise`, the saturation at `m_j = 0` made explicit), the
  letter norms **`coreNormSq_hopStep_lower`** (`‖a_j c‖² = ∑ₙ nⱼ‖c n‖²`) and
  **`coreNormSq_hopStep_raise`** (`∑ₙ (nⱼ + 1)‖c n‖²`) with their mode sums, and the **oscillator
  identity** `∑ⱼ (‖a_j c‖² + ‖a_j† c‖²) = 2⟪c, N c⟫ + d‖c‖²` — the plan's "only input that is not
  bookkeeping", now a theorem on the core;
* **§11, the relative form bound proved** — `coreNorm` (the core `ℓ²` norm), the pairing's algebra
  (`corePair_eq_sum`, `corePair_smul`, `corePair_add`, `corePair_finset_sum`),
  **`norm_corePair_le`** (Cauchy–Schwarz), `sum_coreNorm_hopStep_le` (Cauchy–Schwarz in the mode
  index), `sqrt_add_le` / `two_mul_le_add_div`, and
  **`driftOpCoeff_form_bound`** with `driftFormBound_holds`: `‖⟪c, K c⟫‖ ≤ δ·⟪c, N c⟫ +
  (B²d/(2δ) + Bd)·‖c‖²` for every `δ > 0`, so §5's `DriftFormBound` is a theorem, not a target;
* **§12, the coefficients come from the potential** — `driftWeight` (the SG-pCNL weight `β²σ²/2`)
  and `driftScale` (`B = (β²σ²/2)·M`), the drift `driftOperator β σ Φ` as `polyDrift Φ` scaled by
  that weight (`driftOpCoeff_smul` is the scaling law it rests on), and
  **`driftOperator_linear`**: for a linear `Φ` the operator is exactly §5's `driftOpCoeff`, with
  `bⱼ = (β²σ²/2)·∂ⱼΦ`.  `driftOperator_form_bound` carries a potential's gradient bound `M` into
  the constant `B = driftScale β σ M`, and **`driftOperator_form_bound_eps`** specializes it to
  `M_ε = K/ε`, where the constant is the plan's displayed
  `(β²σ²M_ε)²/(8δ) + β²σ²M_ε/2` times `d‖c‖²` — the `ε` of the drift enters only here; the
  architecture supplies that `M_ε` (`BayesianTransformer.epsProj_fderiv_le`: `2K/ε` for the
  `ε`-regularized normalization), and `driftScale_eps_arch` reads it through the weight as
  `B = β²σ²K/ε`;
* **§13, semiboundedness** — `numberOp_apply` and **`corePair_numberOp_re`** (the pairing
  `⟪c, N c⟫` *is* §5's number form), **`semibounded_of_form_bound`**: a relative form bound with
  `δ ≤ 1` gives `−C‖c‖² ≤ ⟪c, (N + K)c⟫`, the KLMN conclusion taken before any completion; and
  its two instances **`numberOp_add_driftOpCoeff_semibounded`** (`−B²d/(2δ) − Bd`) and
  **`pcnlDrift_semibounded_eps`**, whose lower bound is
  `−((β²σ²M_ε)²d/(8δ) + β²σ²M_ε·d/2)·‖c‖²` for `M_ε = K/ε`;
* **§14, the gradient bound is a sector statement** — the core norm calculus (`coreNorm_add_le`,
  `coreNorm_smul`, `coreNorm_finset_sum_le`), the letters and the multiplication law with their
  `ℓ²` sizes on a sector (`coreNorm_hopStep_sector_le`, `coreNorm_mulHermite_sector_le`,
  `coreNorm_mulHermiteList_sector_le`), **`polyMul_norm_sector_le`** with the explicit constant
  `polyMulSectorBound`, and **`gradSectorBound`** — the `hgrad` of §12 as a theorem on the sector
  `{N ≤ N₀ + 1}`; `polyDrift_form_bound_sector`, `driftOperator_form_bound_sector` and
  **`pcnlDrift_semibounded_sector`** are §11–§13 with that constant in place of the hypothesis;
  and **`polyMul_X_unbounded`** shows the global form is unattainable — `xⱼ` raises the
  occupation, so `polyMul (X j) eₙ` grows like `√n`;
* **§15, the Metropolis rejection filter `K_reject`** — `rejectOp` (multiplication of the
  occupation-`n` coefficient by an acceptance probability, hence `rejectOp_apply`,
  `rejectOp_single` and `rejectOp_comp`: a diagonal damping, not a hopping matrix), the
  Metropolis probability `metropolisReject ΔV = min 1 (exp(−ΔV))` with
  `metropolisReject_nonneg`/`metropolisReject_le_one`, the filter's band and size
  (`rejectOp_band`: band `0`, so `{N ≤ N₀} ↦ {N ≤ N₀}`; `coreNormSq_rejectOp_le`,
  `coreNorm_rejectOp_le`: a contraction for `0 ≤ ρ ≤ 1`), its form (`corePair_rejectOp`,
  **`re_corePair_rejectOp_nonneg`**: the filter only adds to `Re ⟪c, K_reject c⟫`), and the
  assembled step **`pcnlFull` = `N + K_drift + K_reject`** with **`pcnlFull_band`** (band `K`,
  the drift's — rejection contributes none) and **`pcnlFull_semibounded_sector`** /
  **`pcnlFull_metropolis_semibounded`** (the KLMN bound survives, with the Metropolis
  probability discharging the positivity hypothesis);
* **§16, the sector constant as a coefficient bound** — `coeffMass` (the `ℓ¹` mass of a
  polynomial's coefficients) with `polyMulSectorBound_eq_coeffMass`, its algebra
  (`coeffMass_monomial`, `coeffMass_add_le`, `coeffMass_finset_sum_le`), the automatic
  coefficient bound **`coeffMass_pderiv_le`** (`coeffMass (∂ⱼΦ) ≤ deg Φ · coeffMass Φ`, via
  `totalDegree_pderiv_le`) and **`gradCoeffBound_totalDegree_mul_coeffMass`** (`GradCoeffBound`
  holds for every `Φ`), and the comparison with the architecture:
  `gradSectorBound_le_of_gradCoeffBound`, `driftScale_gradSectorBound_le` and
  **`driftScale_gradSectorBound_le_eps`** — `GradCoeffBound Φ (2K/ε)` gives
  `B ≤ β²σ²K/ε` times the level factor `d·(2√(N+2+deg Φ))^{deg Φ}`, so the architecture's
  `ε⁻¹` is the drift constant's `ε⁻¹`; `driftScale_gradSectorBound_le_coeffMass` is the
  unconditional case `K = deg Φ · coeffMass Φ`;
* **§17, the coefficient map** (separate module `BookProof.MCMC.CoeffMap`) — the reading §16 left
  open, at the order the architecture bounds: `linCoeff F x j = D F(x)[eⱼ]` and its polynomial
  `linPart F x` (`pderiv_linPart`, `coeffMass_pderiv_linPart`), the `ℓ²`-to-`ℓ¹` step
  `norm_linCoeff_le`, **`gradCoeffBound_linPart`** and **`gradCoeffBound_epsProj`** (`‖dŴ‖ ≤ 2K/ε`
  gives `GradCoeffBound (linPart (g ∘ Ŵ) W) (2K/ε)` with no hypothesis), the drift corollary
  `driftScale_linPart_le_eps_proj`, and the units match `eval_pderiv_norm_le_coeffMass` (a
  coefficient mass bounds the derivative on the unit cube), so `GradCoeffBound` and
  `epsProj_fderiv_le` are statements of the same kind;
* **§18, the plan's `P₀` and the full step** — `baseOp` (the diagonal `ρ^N`, `baseOp_apply`,
  `baseOp_band` band `0`, `baseOp_comp`, and `baseOp_vac`: it fixes the vacuum, `λ_0 = 1`), the
  contraction `coreNorm_baseOp_le` and its strict form off the vacuum
  `coreNorm_baseOp_sector_le` (`‖P₀ c‖ ≤ ρ‖c‖` on `{N ≥ 1}`, the spectral gap `1 − ρ`); the drift's
  norm on a sector (`coreNorm_diffHermite_sector_le`, `coreNorm_polyDrift_sector_le`,
  `coreNorm_driftOperator_sector_le'`, with the constant `driftStepBound`); and the assembled
  operator **`pcnlKernel ρ_H β σ Φ ρ_acc = P₀ + K_drift + K_reject`** with `pcnlKernel_band`
  (band `K`, the drift's) and the contractions `coreNorm_pcnlKernel_le` /
  `coreNorm_pcnlKernel_sector_le`;
* **§19, iterating the step** — `pcnlKernel_iter_band` (n steps widen the band by `n·K`),
  `coreNorm_pcnlKernel_iter_le` (the norm is bounded by the product of the level constants), and
  the convergence that *does* hold: `coreNorm_iter_baseOp_le` / **`tendsto_iter_baseOp`** — `P₀`
  contracts the non-vacuum core by `ρⁿ` and fixes the vacuum, so its iterates converge to the
  invariant state `e₀` at the plan's rate `λ_n = ρⁿ`;
* **§20, the stochastic split** — `rejectComplement ρ n = 1 − ρ^{natDeg n}` is the Metropolis
  complement of `P₀`, in `[0,1]` for `0 ≤ ρ ≤ 1` (`rejectComplement_nonneg`,
  `rejectComplement_le_one`); **`baseOp_add_rejectOp_complement`**: with it, `P₀ + K_reject = 1`,
  so the normalisation `P 1 = 1` holds exactly and `pcnlKernel_complement` reads the step as
  `1 + K_drift`; the diagonal half is positive (`re_baseOp_nonneg`, `re_rejectOp_nonneg`) and
  `ℓ¹`-bounded (`coreL1_baseOp_le`, `coreL1_rejectOp_le`), and
  `coreL1_pcnlKernel_complement_le` shows it contributes **no** `ℓ¹` contraction — the step's mass
  grows by at most `1 + driftWeight · driftL1Bound`;
* **§21, the drift's sign against the flat `ℓ¹` measure** — §20's remaining gap was the drift's
  *negative* part.  The computation says there is none: on a basis vector the linear potential's
  drift adds mass (`drift_X_single_eq`, `coreL1_single_lt_add_drift_X`, value
  `1 + (β²σ²/2)·2⁻¹ᐟ²·(√(nⱼ+1) + √(nⱼ))`), so the pairing of `K_drift` with the flat `ℓ¹` is
  positive everywhere and cannot supply the contraction.  The structure a convergence theorem
  uses is a *weighted* `ℓ¹`/cone model, supplied in `BookProof.MCMC.PositivityCone` (§22);
* **§21.5, the weighted `ℓ¹` route closed** — `coreW1` is the weighted mass (`coreW1_one`: the
  flat one is `w ≡ 1`), the diagonal cancels exactly in the weight `wInv ρ n = (ρ^{natDeg n})⁻¹`
  (`coreW1_baseOp`, **`coreW1_baseOp_wInv`**: `coreW1 (wInv ρ) (P₀ c) = coreL1 c`, with
  `coreL1_le_coreW1_wInv`), and the drift breaks that weight on *every* basis vector
  (`coreW1_single_lt_add_drift_X`), the excess being explicit in the cancelling weight
  (`coreW1_wInv_add_drift_X`).  Hence **`no_weighted_nonexpansive`**: no strictly positive weight
  makes the normalised step `1 + K_drift` nonexpansive, so the `ℓ¹` route is closed by the
  computation rather than left as the next thing to try;
* **§21.6, the Hessian's `λ` is a constant, the gap is the degree** — `a_j†` is the right adjoint of
  `a_j` in the core pairing (**`corePair_hopStep_adjoint`**), so `Re⟪c, a†a c⟫ = ‖a c‖²`,
  `Re⟪c, aa† c⟫ = ‖a† c‖²` and the double letters cancel in real part
  (`corePair_double_raise_re_eq`); hence `Re⟪c, x_j∂_j c⟫ = −½‖c‖²`
  (`re_corePair_mulHermite_diffHermite`) and `Re⟪c, Σⱼ x_j∂_j c⟫ = −(d/2)‖c‖²`.  For the
  quadratic potential `Φ_λ = (λ/2)Σⱼ xⱼ²` (`pderiv_quadPotential`, `polyDrift_quadPotential`,
  `driftOperator_quadPotential`) the pCNL form is `numberForm + E₀‖c‖²` with
  `E₀ = (β²σ²/2)·λd/2` (**`re_corePair_quadHamiltonian`**), so off the vacuum it is
  `≥ (E₀ + 1)‖c‖²` (**`quadForm_gap`**, sharp at `quadForm_degree_one`, bottom `quadForm_vac`):
  the Bakry–Émery bound shifts the constant and leaves the gap at the number operator's `1`;
* **§21.7, affine gradients** — the drift is additive in the potential (`polyDrift_add`,
  `driftOperator_add`), so for `Φ = Φ_λ + Σⱼ aⱼxⱼ` — gradient `λx + a`, the class a Hessian bound
  describes — the exact quadratic form of §21.6 combines with §12's
  `driftOperator_linear_form_bound`: **`re_corePair_affineHamiltonian`** bounds the form below by
  `(1 − δ)·⟪c,Nc⟫ + (E₀ − C_δ)‖c‖²`, and `affineForm_gap` reads it off the vacuum.  The Hessian's
  `λ` is entirely in the constant; the number-form coefficient stays `1 − δ`;
* **§21.8, the best constant and the crossover** — the `δ`-optimisation is `√(2A) ≤ δ + A/(2δ)`
  (`sqrt_two_mul_le_add_div`), so the coefficient of `‖c‖²` is at most
  `1 + E₀ − driftScale·d − driftScale·√(2d)` for *every* `δ` (**`affineForm_coefficient_le`**); when
  `1 + E₀ < driftScale·(d + √(2d))` the best constant is negative
  (`affineForm_best_coefficient_neg`), and at the implementation's numbers it is below `−10⁷`
  (`affineForm_architecture_coefficient`).  The form bound is a licence for the Hamiltonian, not a
  gap certificate;
* **§21.9, the `L²(π)` side** — the ground-state transform: `Veff`, `genDiff`, and
  **`genDiff_groundScale`** (`A(e^{Φ/2}g) = e^{Φ/2}(g'' − V_eff g)`, so the generator on `L²(π)` is
  similar to the Schrödinger operator); `Veff_quadOne` for `Φ_λ`, and the oscillator in letters
  (**`re_corePair_oscFreqOp`**: form `ω·numberForm`) with its gap (`oscFreqOp_gap`);
* **§21.10, the same in `d` dimensions** — `coordDeriv`/`coordDerivTwo` (the coordinate partials
  through slices), `genDiffD`, `VeffD`, and **`genDiffD_groundScale`**, the coordinate sum of
  §21.9's identity.

## Honest boundary

What is proved is the *band structure* — the combinatorial content of "the drift is a
finite-band hopping matrix" — together with the size of the hopping amplitudes, the Hermite
expansion of an arbitrary polynomial potential as a finite family of ladder words (§9.4), and
the `ε`-regularized relative form bound on the core (§11).  The plan's Module 3 inputs are now
covered: the drift band and its size (§9.6–§9.9), the form bound and semiboundedness (§11–§13)
without the unattainable global `hgrad` (§14), the Metropolis step `K_reject` (§15), the
coefficient-level comparison with the architecture's `M_ε = 2K/ε` (§16) and the coefficient map
that derives it from `epsProj_fderiv_le` (§17, `CoeffMap`), plus the plan's diagonal `P₀` and the
assembled operator with its band and contraction facts (§18–§19).

The relative form bound is stated in §5 (`DriftFormBound`, the plan's constant `B²d/(2δ) + Bd`),
proved in the Fock model in §6, and **proved on the core in §11**.  The inputs it needed are all
present: §9.4–§9.9 supply the expansion (`polyMul` on `Φ` for the multiplication laws `xⱼ`, on
`MvPolynomial.pderiv j Φ` for the derivative, `polyMul_band` and `polyDrift_band` for the band `K`,
and `polyDrift_l1_le` for the sector size), §10 supplies the letter norms
`‖a_j c‖² = ∑ₙ nⱼ‖c n‖²`, `‖a_j† c‖² = ∑ₙ (nⱼ + 1)‖c n‖²` and the oscillator identity
`Σ_j (‖a_j c‖² + ‖a_j† c‖²) = 2⟪c, N c⟫ + d‖c‖²` — the input the plan calls analytic rather than
bookkeeping — and §11 supplies Cauchy–Schwarz in the core pairing `corePair`, Cauchy–Schwarz in the
mode index, and the `2ab ≤ δa² + b²/δ` chain that assemble those norms into the stated constant.
Semiboundedness is not a further hypothesis: §13 turns that bound into
`−C‖c‖² ≤ ⟪c, (N + K_drift)c⟫`.

The identification of the two models is a modelling step that remains: `CoreCoeff d` indexes by
occupation *vectors* `Fin d → ℕ`, the Fock toolbox by finite *multisets* of modes, and §7–§8 now
carry the isometry between them.  The *coefficient family* is §12: `bⱼ = (β²σ²/2)·∂ⱼΦ` is the
weighted gradient, `driftOperator_linear` is the dictionary back to §5's constant-coefficient
drift, and the `ε`-dependence is isolated in `B = (β²σ²/2)M_ε` with `M_ε = K/ε`.  The core-side
bound that identification needs is §14: §12's `hgrad` — "multiplication by `∂ⱼΦ` is bounded by a
constant `M` on the whole core" — cannot hold (`polyMul_X_unbounded`), but on every sector it
does, with the explicit constant `gradSectorBound Φ N`, and §11–§13 then need no hypothesis at all
on a truncated sector (`pcnlDrift_semibounded_sector`).  §16 supplies the *coefficient-level*
comparison of that sector constant with the architecture's weight-space `M_ε = 2K/ε`
(`BayesianTransformer.epsProj_fderiv_le`): the two bounds live in different models, so the link is
a bound on the coefficients of `∂ⱼΦ_ε`, and `coeffMass_pderiv_le` makes it automatic — every
polynomial satisfies `GradCoeffBound Φ (deg Φ · coeffMass Φ)`, and with the architecture's `2K/ε`
the drift constant is `β²σ²K/ε` (§16.3).  §17 (`BookProof/MCMC/CoeffMap`) supplies the *reading*
that link needed: `linCoeff F x j` is the coefficient functional `D F(x)[eⱼ]`, `linPart` its
polynomial, and `gradCoeffBound_epsProj` derives `GradCoeffBound (linPart (g ∘ Ŵ) W) (2K/ε)` from
`epsProj_fderiv_le` — at the **linear** order, which is the only order a bound on `∇Φ_ε` controls.
A general nonlinear `Φ_ε` would need bounds on its higher derivatives, which the architecture's
Theorem 1 does not supply; that is the boundary §17 states.

§15 closes the rejection input: `K_reject` is a multiplication operator, so it has band `0`
(`rejectOp_band`), it is a contraction for a Metropolis acceptance probability
(`coreNorm_rejectOp_le`), and its form is nonnegative (`re_corePair_rejectOp_nonneg`) — which is
why `pcnlFull_band` and `pcnlFull_semibounded_sector` are the drift's statements unchanged.

§18–§19 assemble the plan's operator `P₀ + K_drift + K_reject` and say exactly how far its
iteration goes.  `P₀ = ρ^N` is diagonal, has band `0`, fixes the vacuum (`baseOp_vac`, i.e.
`λ_0 = 1`) and contracts the rest by `ρ` (`coreNorm_baseOp_sector_le`), so **its iterates converge
to the invariant state `e₀` at the plan's rate** (`coreNorm_iter_baseOp_le`, `tendsto_iter_baseOp`).
The full step's band is the drift's (`pcnlKernel_band`) and its iterates widen it linearly
(`pcnlKernel_iter_band`), but its norm is only bounded by the product of the *level* constants
(`coreNorm_pcnlKernel_iter_le`, with `driftStepBound β σ Φ N` growing in `N`), so no uniform
contraction follows.  What a convergence theorem for `P_pCNL` still needs is therefore not an
operator estimate but the Markov structure the core `ℓ²` model does not carry: positivity and the
normalisation `P 1 = 1` on the completed space, where `numberOp`'s unboundedness (§14) no longer
blocks the argument.  In particular the model's own invariant state is the vacuum, not the pCNL
invariant measure.  §20 sharpens the statement: the normalisation is *in* the model once the
acceptance probability is the complement of `P₀` (`baseOp_add_rejectOp_complement`:
`P₀ + K_reject = 1`, hence `pcnlKernel = 1 + K_drift`), and the diagonal half is positive and
`ℓ¹`-bounded (`re_baseOp_nonneg`, `re_rejectOp_nonneg`, `coreL1_baseOp_le`).  So what is actually
missing for a convergence theorem is a **weighted** `ℓ¹` in which the drift is a contraction — not
the flat one.  §21 rules the flat pairing out by computation: `coreL1_single_lt_add_drift_X` shows
the linear potential's drift *raises* the flat `ℓ¹` mass on every basis vector, and §20's
`coreL1_pcnlKernel_complement_le` shows the normalised step's `ℓ¹` size is
`1 + driftWeight · driftL1Bound`, i.e. no decay at all.  The cone model — `P 1 = 1`, a Doeblin
minorant, and the oscillation contraction `osc (P f) ≤ (1 − (m+1)δ)·osc f` — is
`BookProof.MCMC.PositivityCone` (§22), which proves the iterates converge to the invariant state
there (`tendsto_iter_step`).  Translating that model back to the core's unbounded `numberOp` (i.e.
naming the weighted norm) is what remains in this file.
-/

noncomputable section

namespace BookProof.MCMC.FockLangevin

open Finset
open BookProof.ReferenceGap
open BookProof.MCMC.UnadjustedPCN

variable {d : ℕ}

/-! ## 1. Ladder steps on occupations -/

/-- `a_j†`: raise the occupation of mode `j` by one. -/
def raiseIdx (j : Fin d) (n : Fin d → ℕ) : Fin d → ℕ := Function.update n j (n j + 1)

/-- `a_j`: lower the occupation of mode `j` by one, saturating at `0`. -/
def lowerIdx (j : Fin d) (n : Fin d → ℕ) : Fin d → ℕ := Function.update n j (n j - 1)

/-- The occupation shift of one ladder letter: `true` raises (creation), `false` lowers
(annihilation). -/
def stepIdx (b : Bool) (j : Fin d) (n : Fin d → ℕ) : Fin d → ℕ :=
  if b then raiseIdx j n else lowerIdx j n

/-- Splitting the total degree at one mode. -/
theorem sum_erase (f : Fin d → ℕ) (j : Fin d) :
    f j + ∑ i ∈ Finset.univ.erase j, f i = ∑ i, f i :=
  Finset.add_sum_erase _ f (Finset.mem_univ j)

theorem sum_erase_update (n : Fin d → ℕ) (j : Fin d) (v : ℕ) :
    ∑ i ∈ Finset.univ.erase j, Function.update n j v i = ∑ i ∈ Finset.univ.erase j, n i :=
  Finset.sum_congr rfl fun i hi => by simp [Finset.ne_of_mem_erase hi]

/-- **Creation raises the total degree by one.** -/
theorem natDeg_raiseIdx (j : Fin d) (n : Fin d → ℕ) : natDeg (raiseIdx j n) = natDeg n + 1 := by
  have h1 := sum_erase n j
  have h2 := sum_erase (Function.update n j (n j + 1)) j
  have h3 := sum_erase_update n j (n j + 1)
  have h4 : Function.update n j (n j + 1) j = n j + 1 := by simp
  unfold natDeg raiseIdx
  omega

/-- **Annihilation does not raise the total degree.** -/
theorem natDeg_lowerIdx_le (j : Fin d) (n : Fin d → ℕ) : natDeg (lowerIdx j n) ≤ natDeg n := by
  have h1 := sum_erase n j
  have h2 := sum_erase (Function.update n j (n j - 1)) j
  have h3 := sum_erase_update n j (n j - 1)
  have h4 : Function.update n j (n j - 1) j = n j - 1 := by simp
  unfold natDeg lowerIdx
  omega

/-- The degree change of one ladder letter, in the two cases. -/
theorem natDeg_stepIdx_raise (j : Fin d) (n : Fin d → ℕ) :
    natDeg (stepIdx true j n) = natDeg n + 1 := natDeg_raiseIdx j n

theorem natDeg_stepIdx_lower (j : Fin d) (n : Fin d → ℕ) :
    natDeg (stepIdx false j n) ≤ natDeg n := natDeg_lowerIdx_le j n

/-- Every ladder letter changes the total degree by at most one. -/
theorem natDeg_stepIdx_le (b : Bool) (j : Fin d) (n : Fin d → ℕ) :
    natDeg (stepIdx b j n) ≤ natDeg n + 1 := by
  cases b with
  | true => rw [natDeg_stepIdx_raise]
  | false => have := natDeg_stepIdx_lower j n; omega

/-! ## 2. The step amplitudes -/

/-- The Hermite/Fock matrix element of one ladder letter: `√(n_j + 1)` for `a_j†`, `√(n_j)` for
`a_j`. -/
def stepAmp (b : Bool) (j : Fin d) (n : Fin d → ℕ) : ℂ :=
  if b then ((Real.sqrt (n j + 1) : ℝ) : ℂ) else ((Real.sqrt (n j) : ℝ) : ℂ)

theorem stepAmp_raise (j : Fin d) (n : Fin d → ℕ) :
    stepAmp true j n = ((Real.sqrt (n j + 1) : ℝ) : ℂ) := rfl

theorem stepAmp_lower (j : Fin d) (n : Fin d → ℕ) :
    stepAmp false j n = ((Real.sqrt (n j) : ℝ) : ℂ) := rfl

/-- **The step amplitude is `≤ √(N + 1)` on the degree-`≤ N` sector.**  This is the size estimate
the plan's relative-bound argument needs: `K_drift` grows only like the square root of the
background occupation. -/
theorem stepAmp_norm_le (b : Bool) (j : Fin d) {n : Fin d → ℕ} {N : ℕ} (hn : natDeg n ≤ N) :
    ‖stepAmp b j n‖ ≤ Real.sqrt ((N : ℝ) + 1) := by
  have hle : n j ≤ N := le_trans (Finset.single_le_sum (f := n) (fun i _ => Nat.zero_le _)
    (Finset.mem_univ j)) hn
  have hleR : (n j : ℝ) ≤ (N : ℝ) := by exact_mod_cast hle
  cases b with
  | true =>
    rw [stepAmp_raise, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (by linarith)
  | false =>
    rw [stepAmp_lower, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact Real.sqrt_le_sqrt (by linarith)

/-! ## 3. The hopping operators -/

/-- **One ladder step on the core**, with its amplitude: the monomial `a_j†` or `a_j` acting on a
coefficient family. -/
def hopStep (p : Fin d × Bool) (c : CoreCoeff d) : CoreCoeff d :=
  c.sum fun n a => Finsupp.single (stepIdx p.2 p.1 n) (stepAmp p.2 p.1 n * a)

/-- Membership in the support of a one-step hop: the new index is a ladder shift of an old one. -/
theorem mem_support_hopStep {p : Fin d × Bool} {c : CoreCoeff d} {m : Fin d → ℕ}
    (hm : m ∈ (hopStep p c).support) : ∃ n ∈ c.support, m = stepIdx p.2 p.1 n := by
  unfold hopStep at hm
  have hsub : (c.sum fun n a =>
      Finsupp.single (stepIdx p.2 p.1 n) (stepAmp p.2 p.1 n * a)).support ⊆
      c.support.biUnion (fun n => (Finsupp.single (stepIdx p.2 p.1 n)
        (stepAmp p.2 p.1 n * c n)).support) := Finsupp.support_sum
  obtain ⟨n, hn, hmn⟩ := Finset.mem_biUnion.mp (hsub hm)
  have hm' : m = stepIdx p.2 p.1 n := by
    simpa using Finsupp.support_single_subset hmn
  exact ⟨n, hn, hm'⟩

/-- **The one-step band**: a ladder letter maps the sector `{N ≤ N₀}` into `{N ≤ N₀ + 1}`. -/
theorem hopStep_band {p : Fin d × Bool} {c : CoreCoeff d} {N : ℕ}
    (hc : ∀ n ∈ c.support, natDeg n ≤ N) {m : Fin d → ℕ} (hm : m ∈ (hopStep p c).support) :
    natDeg m ≤ N + 1 := by
  obtain ⟨n, hn, rfl⟩ := mem_support_hopStep hm
  have hnN : natDeg n ≤ N := hc n hn
  exact le_trans (natDeg_stepIdx_le p.2 p.1 n) (by omega)

/-- A **word** of ladder letters, applied left to right. -/
def hopWord : List (Fin d × Bool) → CoreCoeff d → CoreCoeff d
  | [], c => c
  | p :: w, c => hopWord w (hopStep p c)

/-- **The finite-band property of a ladder word**: a word of length `k` maps the sector
`{N ≤ N₀}` into `{N ≤ N₀ + k}`.  This is `pcnl.md` §2.2's "finite-band hopping matrix". -/
theorem hopWord_band (w : List (Fin d × Bool)) :
    ∀ (c : CoreCoeff d) (N : ℕ), (∀ n ∈ c.support, natDeg n ≤ N) →
      ∀ m ∈ (hopWord w c).support, natDeg m ≤ N + w.length := by
  induction w with
  | nil =>
    intro c N hc m hm
    rw [hopWord] at hm
    have := hc m hm
    simpa using this
  | cons p w ih =>
    intro c N hc m hm
    rw [hopWord] at hm
    have hstep : ∀ n ∈ (hopStep p c).support, natDeg n ≤ N + 1 := fun n hn =>
      hopStep_band hc hn
    have := ih (hopStep p c) (N + 1) hstep m hm
    simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using this

/-- **The drift operator**: a finite family of ladder words (one per monomial of the potential),
summed.  This is the plan's `K_drift`. -/
def driftOp : List (List (Fin d × Bool)) → CoreCoeff d → CoreCoeff d
  | [], _ => 0
  | w :: ws, c => hopWord w c + driftOp ws c

/-- **The drift is finite-band.**  If every monomial has degree at most `K`, then `K_drift` maps
the sector `{N ≤ N₀}` into `{N ≤ N₀ + K}`: applying the drift can change the occupation only by
a bounded amount, which is the structural fact behind the plan's relative bound. -/
theorem driftOp_band (words : List (List (Fin d × Bool))) {K : ℕ}
    (hK : ∀ w ∈ words, w.length ≤ K) (c : CoreCoeff d) {N : ℕ}
    (hc : ∀ n ∈ c.support, natDeg n ≤ N) {m : Fin d → ℕ}
    (hm : m ∈ (driftOp words c).support) : natDeg m ≤ N + K := by
  induction words with
  | nil => simp [driftOp] at hm
  | cons w ws ih =>
    rw [driftOp] at hm
    have hw : w.length ≤ K := hK w (List.mem_cons_self)
    have hws : ∀ w' ∈ ws, w'.length ≤ K := fun w' hw' => hK w' (List.mem_cons_of_mem _ hw')
    have hmem := Finset.mem_union.mp (Finsupp.support_add hm)
    rcases hmem with h1 | h2
    · exact le_trans (hopWord_band w c N hc m h1) (by omega)
    · exact ih hws h2

/-! ## 4. The number operator, and the pCNL shape -/

/-- The Fock number operator `N = ∑ a_j† a_j` on the core: diagonal, with eigenvalue `natDeg n`. -/
def numberOp (c : CoreCoeff d) : CoreCoeff d :=
  c.sum fun n a => Finsupp.single n ((natDeg n : ℂ) * a)

/-- The number operator is diagonal, hence does not move the support. -/
theorem mem_support_numberOp {c : CoreCoeff d} {m : Fin d → ℕ}
    (hm : m ∈ (numberOp c).support) : m ∈ c.support := by
  unfold numberOp at hm
  have hsub : (c.sum fun n a => Finsupp.single n ((natDeg n : ℂ) * a)).support ⊆
      c.support := by
    refine Finset.Subset.trans Finsupp.support_sum ?_
    intro x hx
    obtain ⟨n, hn, hxn⟩ := Finset.mem_biUnion.mp hx
    have hxeq : x = n := by simpa using Finsupp.support_single_subset hxn
    rwa [hxeq]
  exact hsub hm

/-- `pcnl.md` §2.2's operator shape on the core: the sum of the diagonal `P₀`/number part and the
finite-band drift.  (`P₀` itself is the diagonal contraction `pcnWeight` of
`BookProof.MCMC.UnadjustedPCN`; the Metropolis filter is a multiplication operator and is outside
this model.) -/
def pcnlHamiltonian (words : List (List (Fin d × Bool))) (c : CoreCoeff d) : CoreCoeff d :=
  numberOp c + driftOp words c

/-- **The pCNL Hamiltonian is finite-band around the diagonal.**  Its drift part moves the degree
by at most `K`, so the operator has bandwidth `K` in the occupation grading — the reason a
truncation at degree `N₀` couples only to degrees `≤ N₀ + K`. -/
theorem pcnlHamiltonian_band (words : List (List (Fin d × Bool))) {K : ℕ}
    (hK : ∀ w ∈ words, w.length ≤ K) (c : CoreCoeff d) {N : ℕ}
    (hc : ∀ n ∈ c.support, natDeg n ≤ N) {m : Fin d → ℕ}
    (hm : m ∈ (pcnlHamiltonian words c).support) : natDeg m ≤ N + K := by
  rw [pcnlHamiltonian] at hm
  rcases Finset.mem_union.mp (Finsupp.support_add hm) with h1 | h2
  · exact le_trans (hc m (mem_support_numberOp h1)) (by omega)
  · exact driftOp_band words hK c hc h2

/-! ## 5. The `ε`-regularized relative form bound (Module 3 target) -/

/-- The `ℓ²` pairing `⟪c, c'⟫ = ∑ₙ c n · conj (c' n)`, summed over the union of the two supports:
both are finitely supported, so no completion of the core is needed. -/
def corePair (c c' : CoreCoeff d) : ℂ :=
  ∑ n ∈ c.support ∪ c'.support, c n * star (c' n)

/-- The quadratic form of the number operator, `⟪c, N c⟫ = ∑ₙ (∑ᵢ nᵢ)·‖c n‖²` — the object that
`‖N^{1/2}ψ‖²` of the plan is, read on the core. -/
def numberForm (c : CoreCoeff d) : ℝ :=
  ∑ n ∈ c.support, (natDeg n : ℝ) * ‖c n‖ ^ 2

theorem numberForm_nonneg (c : CoreCoeff d) : 0 ≤ numberForm c :=
  Finset.sum_nonneg fun n _ => mul_nonneg (Nat.cast_nonneg _) (by positivity)

/-- `1/√2`, the normalization in `∂_j = (a_j − a_j†)/√2`. -/
def invSqrtTwo : ℝ := 1 / Real.sqrt 2

/-- **The drift as a hopping operator with coefficients**, `K_drift = −∑_j b_j ∂_j`:
`∑_j [ (−b_j/√2)·a_j + (b_j/√2)·a_j† ]`, each letter being a `hopStep`.  The plan's `K_drift` is
this operator with `b_j = (β²σ²/2)·∂_jΦ_ε`, so `|b_j| ≤ B` with `B = β²σ²M_ε/2`. -/
def driftOpCoeff (b : Fin d → ℝ) (c : CoreCoeff d) : CoreCoeff d :=
  Finset.univ.sum fun j : Fin d =>
    (((-(b j)) * invSqrtTwo : ℝ) : ℂ) • hopStep (j, false) c +
      (((b j) * invSqrtTwo : ℝ) : ℂ) • hopStep (j, true) c

/-- **Module 3's `ε`-regularized relative form bound for `K_drift`**, stated as a proposition so
that the shape the plan asks for is pinned down in one place (it is proved in §11).

For every coefficient family `b : Fin d → ℝ` with `|b j| ≤ B`, every `δ > 0` and every core state
`c`,

`‖⟪c, K_drift c⟫‖ ≤ δ·⟪c, N c⟫ + (B²·d/(2δ) + B·d)·‖c‖²`,

with `d` the number of modes (the plan's `P`) and `B = β²σ²M_ε/2`, `M_ε = K/ε` the gradient bound of
the `ε`-regularized architecture.  `δ` is arbitrary, so the relative bound is **zero**: `K_drift` is
infinitesimally form-small with respect to `N`, which is what makes `N + K_drift` self-adjoint and
bounded below by KLMN.

The plan's constant is reproduced by the chain
`|⟪c, K c⟫| ≤ (B/√2)·‖c‖·∑_j (‖a_j c‖ + ‖a_j† c‖)`, then
`≤ B·√d·‖c‖·√(2⟪c,Nc⟫ + d‖c‖²)`, then `√(x + y) ≤ √x + √y` and `2ab ≤ δa² + b²/δ`; the
oscillator identity
`Σ_j (‖a_j c‖² + ‖a_j† c‖²) = 2⟪c, N c⟫ + d·‖c‖²` is the only input that is not bookkeeping.
**It is a theorem** — `driftFormBound_holds` in §11 — so no input is missing from the estimate
itself.  What it pins down — and what the plan needs — is that the only `ε`-dependence enters
through `B`, and hence quadratically as `ε⁻²`, which is why the bound certifies semiboundedness
and cannot supply the gap.  The remaining modelling step is the *identification* of `b` with
`∂Φ_ε` (see the module's honest boundary). -/
def DriftFormBound (B : ℝ) (b : Fin d → ℝ) : Prop :=
  (∀ j, |b j| ≤ B) →
    ∀ (δ : ℝ), 0 < δ →
      ∀ c : CoreCoeff d,
        ‖corePair c (driftOpCoeff b c)‖ ≤
          δ * numberForm c + (B ^ 2 * (d : ℝ) / (2 * δ) + B * (d : ℝ)) * coreNormSq c

/-! ## 6. The same bound as a theorem, in the corpus Fock model

`DriftFormBound` above lives on the coefficient core `CoreCoeff d` and is proved there in §11.
This section proves the independent twin in the corpus's Fock model, whose analytic machinery is
already attached —
`BookProof.FockFieldPerturbation` proves the relative form bound for the field operator
`Φ(f) = a†(f) + a(f)` against the number form.  The plan's drift is the *difference*
`K_drift = Σⱼ (bⱼ/√2)(a†ⱼ − aⱼ) = creVec f − annVec f` with `f = b/√2`, so the same estimate gives
the bound with relative bound zero, and here it is a theorem rather than a statement.

The two models are identified by §7–§8: `CoreCoeff d` indexes by occupancy *vectors* `Fin d → ℕ`,
the Fock toolbox by finite *multisets* of modes (`Conf →₀ ℂ`), and `idxEquiv` with
`numberForm_reindex` is the isometry between them.  This section is kept as the independent twin:
it derives the same constant from `BookProof.FockFieldPerturbation`'s field-operator estimate, so
§11 and this section agree on the bound by two different routes.
-/

open BookProof.FockFieldPerturbation
open BookProof.FockSecondQuantization

/-- **The drift on the corpus Fock space**: `Σⱼ (fⱼ a†ⱼ + conj fⱼ aⱼ)` is `creVec f + annVec f`;
for a *real* coefficient family the plan's `−Σⱼ bⱼ ∂ⱼ` is the difference `creVec f − annVec f` with
`f = b/√2`. -/
def driftField (f : ℕ →₀ ℂ) : FockAlg →ₗ[ℂ] FockAlg := creVec f - annVec f

theorem driftField_apply (f : ℕ →₀ ℂ) (u : FockAlg) :
    driftField f u = creVec f u - annVec f u := rfl

/-- **The `N^{1/2}` estimate for the drift**, the difference form of
`abs_re_inner_fieldVec_le`: `|Re⟪u, K u⟫| ≤ 2‖f‖·⟪u, N u⟫^{1/2}·‖u‖`. -/
theorem abs_re_inner_driftField_le (f : ℕ →₀ ℂ) (u : FockAlg) :
    |(inner ℂ (toLp u) (toLp (driftField f u)) : ℂ).re|
      ≤ 2 * l2norm f * Real.sqrt (numberQuad u) * ‖toLp u‖ := by
  have hsplit : (inner ℂ (toLp u) (toLp (driftField f u)) : ℂ)
      = inner ℂ (toLp u) (toLp (creVec f u)) - inner ℂ (toLp u) (toLp (annVec f u)) := by
    have hsub : toLp (driftField f u) = toLp (creVec f u) - toLp (annVec f u) := by
      have hs := map_sub toLpL (creVec f u) (annVec f u)
      simpa only [toLpL_apply, driftField_apply] using hs
    rw [hsub, inner_sub_right]
  have hbound : ‖toLp (annVec f u)‖ * ‖toLp u‖
      ≤ l2norm f * Real.sqrt (numberQuad u) * ‖toLp u‖ :=
    mul_le_mul_of_nonneg_right (norm_annVec_le f u) (norm_nonneg _)
  have h1 : |((inner ℂ (toLp u) (toLp (creVec f u)) : ℂ)).re|
      ≤ l2norm f * Real.sqrt (numberQuad u) * ‖toLp u‖ := by
    rw [inner_creVec_annVec]
    calc |(inner ℂ (toLp (annVec f u)) (toLp u) : ℂ).re|
        ≤ ‖(inner ℂ (toLp (annVec f u)) (toLp u) : ℂ)‖ := Complex.abs_re_le_norm _
      _ ≤ ‖toLp (annVec f u)‖ * ‖toLp u‖ := norm_inner_le_norm _ _
      _ ≤ _ := hbound
  have h2 : |((inner ℂ (toLp u) (toLp (annVec f u)) : ℂ)).re|
      ≤ l2norm f * Real.sqrt (numberQuad u) * ‖toLp u‖ := by
    calc |(inner ℂ (toLp u) (toLp (annVec f u)) : ℂ).re|
        ≤ ‖(inner ℂ (toLp u) (toLp (annVec f u)) : ℂ)‖ := Complex.abs_re_le_norm _
      _ ≤ ‖toLp u‖ * ‖toLp (annVec f u)‖ := norm_inner_le_norm _ _
      _ = ‖toLp (annVec f u)‖ * ‖toLp u‖ := mul_comm _ _
      _ ≤ _ := hbound
  rw [hsplit, Complex.sub_re]
  calc |(inner ℂ (toLp u) (toLp (creVec f u)) : ℂ).re
          - (inner ℂ (toLp u) (toLp (annVec f u)) : ℂ).re|
      ≤ |(inner ℂ (toLp u) (toLp (creVec f u)) : ℂ).re|
        + |(inner ℂ (toLp u) (toLp (annVec f u)) : ℂ).re| := by
        simpa [sub_eq_add_neg] using abs_add_le (a := (inner ℂ (toLp u) (toLp (creVec f u)) : ℂ).re)
          (b := -((inner ℂ (toLp u) (toLp (annVec f u)) : ℂ).re))
    _ ≤ 2 * l2norm f * Real.sqrt (numberQuad u) * ‖toLp u‖ := by linarith

/-- **Module 3's bound as a theorem (Fock model).**  For every coupling vector `f` and every
`t > 0`,

`|Re⟪u, K_drift u⟫| ≤ t·⟪u, N u⟫ + (‖f‖²/t)·‖u‖²`,

so the relative bound is zero: `K_drift` is infinitesimally form-small with respect to the number
operator.  `t` is the plan's `δ` and `‖f‖²/t` its `C_δ`. -/
theorem driftField_relative_form_bound (f : ℕ →₀ ℂ) {t : ℝ} (ht : 0 < t) (u : FockAlg) :
    |(inner ℂ (toLp u) (toLp (driftField f u)) : ℂ).re|
      ≤ t * numberQuad u + l2norm f ^ 2 / t * ‖toLp u‖ ^ 2 := by
  have h1 := abs_re_inner_driftField_le f u
  have h2 := two_mul_sqrt_le (c := l2norm f) (n := ‖toLp u‖) (N := numberQuad u) (t := t)
    (numberQuad_nonneg u) ht
  linarith

/-! ## 7. The index-level model identification: occupation vectors are multisets

`CoreCoeff d` indexes by occupation *vectors* `Fin d → ℕ`; the corpus Fock toolbox
(`BookProof.FockSecondQuantization`) indexes by finite *multisets* of modes.  On a finite mode set
the two are the same data — `Fin d` is finite, so every `Fin d → ℕ` is finitely supported, and
`Finsupp.equivFunOnFinite` is the bijection.  This section records the bijection and checks that
the degree grading (§1's `natDeg`, the `N` of the number operator) is read through it, so the
sector structure of §4's band lemmas is the sector structure of the Fock model.

Section 8 carries out the rest: the `ℓ²` reindexing along `idxEquiv` (`reindex`,
`sum_sq_reindex`, `numberForm_reindex`), and the restriction to the `Fin d` mode sector
(`sectorVec`, `l2norm_sectorVec`, `driftField_sector_relative_form_bound`, `InSector`).  What is
still *not* claimed is that §5's `DriftFormBound` follows — see the note in §8. -/

/-- **Occupation vectors on `d` modes are finite multisets of modes.** -/
def idxEquiv (d : ℕ) : (Fin d → ℕ) ≃ (Fin d →₀ ℕ) :=
  Finsupp.equivFunOnFinite.symm

@[simp] theorem idxEquiv_apply (n : Fin d → ℕ) (i : Fin d) : idxEquiv d n i = n i := rfl

@[simp] theorem idxEquiv_symm_apply (s : Fin d →₀ ℕ) (i : Fin d) : (idxEquiv d).symm s i = s i :=
  rfl

/-- **The degree is the particle number of the multiset**: `N` on an occupation vector is the total
count of the corresponding multiset, so the grading is the same on both sides of `idxEquiv`. -/
theorem natDeg_idxEquiv (n : Fin d → ℕ) :
    (idxEquiv d n).sum (fun _ m => m) = natDeg n := by
  rw [Finsupp.sum_fintype]
  · rfl
  · intro i
    rfl

/-! ## 8. The `Fin d` mode sector: the `ℓ²` reindexing and the sector restriction

§7 identified the *indices* — an occupation vector on `d` modes is a finite multiset of modes.
This section completes the identification on the two objects the relative bound is stated for.

**The states.**  `reindex` reads a core state `CoreCoeff d` as a configuration vector on
multisets.  `sum_sq_reindex` says it is an isometry of the core `ℓ²`, and `numberForm_reindex`
says it carries the core's number form `∑ n, N(n)‖c n‖²` to `∑ s, (s.sum id)‖ĉ s‖²` — the shape of
`⟪u, N u⟫` in the corpus Fock model.

**The coupling.**  The toolbox's modes are all of `ℕ`; this chapter's are `Fin d`.
`sectorVec` embeds a `Fin d` coupling as a one-particle vector supported on `{0, …, d−1}`,
`l2norm_sectorVec` reindexes its `ℓ²` norm, and `driftField_sector_relative_form_bound` is
Module 3's bound with the `Fin d` constants `∑ᵢ‖bᵢ‖²` and the `d`-mode sum.

**The sector.**  `InSector` is the subspace of states whose excited modes are all in the first
`d`; `annA_eq_zero_of_sector` kills the modes beyond it, `numberQuad_eq_sum_fin` reindexes the
number form onto `Fin d`, and `InSector.driftField` shows a `Fin d` coupling cannot carry a state
out of the sector.

What this section deliberately does **not** claim is that `DriftFormBound` follows.  That needs
two more steps, and they are of different kinds: (i) the real coupling `b : Fin d → ℝ` of
`driftOpCoeff` is the field `driftField (sectorVec (b : Fin d → ℂ))` only after the Hermite
expansion `∂_j = (a_j − a_j†)/√2` of the potential — the missing input named in the module's
honest boundary; (ii) `numberQuad` is the form of the number operator on the *configuration*
space, whereas `numberForm` is its form on the core, so transporting the estimate from one to the
other is the reindexing `sum_sq_reindex` / `numberForm_reindex` *plus* the identification of the
quadratic forms, again via the Hermite basis.  What is now fixed is the model: the constants,
the grading, the sector and the `ℓ²` structures agree. -/

section Sector

/-- **The `ℓ²` reindexing of the core**: a core state, read as a configuration vector on the
multisets of the `d` modes (`idxEquiv`). -/
def reindex (c : CoreCoeff d) : (Fin d →₀ ℕ) →₀ ℂ := Finsupp.mapDomain (idxEquiv d) c

/-- The degree of a multiset of modes: its total particle number. -/
def confDeg (s : Fin d →₀ ℕ) : ℕ := s.sum fun _ m => m

theorem confDeg_idxEquiv (n : Fin d → ℕ) : confDeg (idxEquiv d n) = natDeg n := natDeg_idxEquiv n

@[simp] theorem reindex_apply (c : CoreCoeff d) (n : Fin d → ℕ) :
    reindex c (idxEquiv d n) = c n :=
  Finsupp.mapDomain_apply (idxEquiv d).injective c n

theorem support_reindex (c : CoreCoeff d) :
    (reindex c).support = c.support.image (idxEquiv d) :=
  Finsupp.mapDomain_support_of_injective (idxEquiv d).injective c

/-- **The reindexing is an isometry of the core `ℓ²`**: the squared norm of a core state,
computed in the multiset indexing, is `coreNormSq`. -/
theorem sum_sq_reindex (c : CoreCoeff d) :
    ∑ s ∈ (reindex c).support, ‖reindex c s‖ ^ 2 = coreNormSq c := by
  rw [support_reindex, coreNormSq, Finset.sum_image]
  · exact Finset.sum_congr rfl fun n _ => by rw [reindex_apply]
  · intro x _ y _ hxy
    exact (idxEquiv d).injective hxy

/-- **The number form is the multiset form.**  Under the reindexing, `numberForm` becomes
`∑ s, (∂eg s)·‖ĉ s‖²` — the degree weight read off the multiset, which is the shape of the Fock
number form `⟪u, N u⟫`. -/
theorem numberForm_reindex (c : CoreCoeff d) :
    ∑ s ∈ (reindex c).support, ((confDeg s : ℕ) : ℝ) * ‖reindex c s‖ ^ 2 = numberForm c := by
  rw [support_reindex, numberForm, Finset.sum_image]
  · refine Finset.sum_congr rfl fun n _ => ?_
    rw [reindex_apply, confDeg_idxEquiv]
  · intro x _ y _ hxy
    exact (idxEquiv d).injective hxy

/-- **A `Fin d` coupling as a one-particle vector of the Fock model**, supported on the modes
`{0, …, d−1}`. -/
def sectorVec (b : Fin d → ℂ) : ℕ →₀ ℂ :=
  Finsupp.onFinset (Finset.range d) (fun j => if h : j < d then b ⟨j, h⟩ else 0)
    (fun j hj => by
      by_contra hmem
      have hnd : ¬ j < d := by simpa [Finset.mem_range] using hmem
      exact hj (by simp [hnd]))

@[simp] theorem sectorVec_apply (b : Fin d → ℂ) (j : ℕ) :
    sectorVec b j = if h : j < d then b ⟨j, h⟩ else 0 := by
  simp [sectorVec]

theorem sectorVec_apply_of_lt (b : Fin d → ℂ) {j : ℕ} (hj : j < d) :
    sectorVec b j = b ⟨j, hj⟩ := by
  rw [sectorVec_apply, dif_pos hj]

theorem sectorVec_apply_of_ge (b : Fin d → ℂ) {j : ℕ} (hj : d ≤ j) : sectorVec b j = 0 := by
  rw [sectorVec_apply, dif_neg (by omega)]

theorem support_sectorVec (b : Fin d → ℂ) : (sectorVec b).support ⊆ Finset.range d :=
  Finsupp.support_onFinset_subset

/-- **The `ℓ²` norm of a `Fin d` coupling**: the one-particle vector carries exactly the
coefficient norm `√(∑ᵢ‖bᵢ‖²)`. -/
theorem sum_sq_sectorVec (b : Fin d → ℂ) :
    ∑ j ∈ (sectorVec b).support, ‖sectorVec b j‖ ^ 2 = ∑ i : Fin d, ‖b i‖ ^ 2 := by
  rw [Finset.sum_subset (support_sectorVec b) (fun j _ hmem => by
    rw [Finsupp.notMem_support_iff.mp hmem, norm_zero]
    simp)]
  rw [Finset.sum_range (fun j => ‖sectorVec b j‖ ^ 2)]
  exact Finset.sum_congr rfl fun i _ => by rw [sectorVec_apply_of_lt b i.isLt]

theorem l2norm_sectorVec (b : Fin d → ℂ) :
    l2norm (sectorVec b) = Real.sqrt (∑ i : Fin d, ‖b i‖ ^ 2) := by
  rw [l2norm, sum_sq_sectorVec]

theorem l2norm_sectorVec_sq (b : Fin d → ℂ) :
    l2norm (sectorVec b) ^ 2 = ∑ i : Fin d, ‖b i‖ ^ 2 := by
  rw [l2norm_sectorVec, Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)]

/-- **Module 3's bound in the `Fin d` sector.**  For every coupling `b` on the `d` modes and every
`t > 0`,

`|Re⟪u, Σᵢ(bᵢ/√2)(aᵢ† − aᵢ)u⟫| ≤ t⟪u, N u⟫ + (∑ᵢ‖bᵢ‖²/t)‖u‖²`,

which is `driftField_relative_form_bound` with the `ℓ²` norm of the coupling written in the
chapter's own indexing: `d` is the number of modes, the coupling is a `Fin d` family, and the
constant is the coefficient norm rather than a `ℕ`-supported `Finsupp`. -/
theorem driftField_sector_relative_form_bound (b : Fin d → ℂ) {t : ℝ} (ht : 0 < t)
    (u : FockAlg) :
    |(inner ℂ (toLp u) (toLp (driftField (sectorVec b) u)) : ℂ).re|
      ≤ t * numberQuad u + (∑ i : Fin d, ‖b i‖ ^ 2) / t * ‖toLp u‖ ^ 2 := by
  have h := driftField_relative_form_bound (sectorVec b) ht u
  rw [l2norm_sectorVec_sq] at h
  exact h

/-! ### The sector of the Fock model -/

/-- A Fock state **lives in the `Fin d` mode sector** when every mode any of its configurations
excites is one of the first `d`. -/
def InSector (d : ℕ) (u : FockAlg) : Prop := modes u ⊆ Finset.range d

theorem support_sub_subset (u v : FockAlg) :
    (u - v).support ⊆ u.support ∪ v.support := by
  intro β hβ
  rw [Finset.mem_union]
  by_contra h
  push_neg at h
  obtain ⟨h1, h2⟩ := h
  exact (Finsupp.mem_support_iff.mp hβ) (by
    rw [Finsupp.sub_apply, Finsupp.notMem_support_iff.mp h1, Finsupp.notMem_support_iff.mp h2,
      sub_zero])

theorem modes_add_subset (u v : FockAlg) : modes (u + v) ⊆ modes u ∪ modes v := by
  intro k hk
  obtain ⟨β, hβ, hkβ⟩ := Finset.mem_biUnion.mp hk
  rcases Finset.mem_union.mp (Finsupp.support_add hβ) with h | h
  · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨β, h, hkβ⟩)
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨β, h, hkβ⟩)

theorem modes_sub_subset (u v : FockAlg) : modes (u - v) ⊆ modes u ∪ modes v := by
  intro k hk
  obtain ⟨β, hβ, hkβ⟩ := Finset.mem_biUnion.mp hk
  rcases Finset.mem_union.mp (support_sub_subset u v hβ) with h | h
  · exact Finset.mem_union_left _ (Finset.mem_biUnion.mpr ⟨β, h, hkβ⟩)
  · exact Finset.mem_union_right _ (Finset.mem_biUnion.mpr ⟨β, h, hkβ⟩)

theorem modes_smul_subset (c : ℂ) (u : FockAlg) : modes (c • u) ⊆ modes u := by
  intro k hk
  obtain ⟨β, hβ, hkβ⟩ := Finset.mem_biUnion.mp hk
  exact Finset.mem_biUnion.mpr ⟨β, Finsupp.support_smul hβ, hkβ⟩

theorem modes_annA_subset (j : ℕ) (u : FockAlg) : modes (annA j u) ⊆ modes u := by
  intro k hk
  obtain ⟨β, hβ, hkβ⟩ := Finset.mem_biUnion.mp hk
  obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp (support_annA j u hβ)
  exact Finset.mem_biUnion.mpr ⟨α, hα, support_dn j α hkβ⟩

theorem modes_creA_subset (j : ℕ) (u : FockAlg) : modes (creA j u) ⊆ insert j (modes u) := by
  intro k hk
  obtain ⟨β, hβ, hkβ⟩ := Finset.mem_biUnion.mp hk
  obtain ⟨α, hα, rfl⟩ := Finset.mem_image.mp (support_creA j u hβ)
  rcases Finset.mem_insert.mp (support_up j α hkβ) with h | h
  · exact Finset.mem_insert.mpr (Or.inl h)
  · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_biUnion.mpr ⟨α, hα, h⟩))

theorem modes_sum_subset {ι : Type*} (s : Finset ι) (g : ι → FockAlg) :
    modes (∑ i ∈ s, g i) ⊆ s.biUnion (fun i => modes (g i)) := by
  classical
  induction s using Finset.induction with
  | empty => simp [modes]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.biUnion_insert]
    exact (modes_add_subset _ _).trans
      (Finset.union_subset_union (Finset.Subset.refl _) ih)

theorem modes_annVec_subset (f : ℕ →₀ ℂ) (u : FockAlg) : modes (annVec f u) ⊆ modes u := by
  rw [annVec_apply]
  refine (modes_sum_subset f.support (fun j => ((starRingEnd ℂ) (f j)) • annA j u)).trans ?_
  intro k hk
  obtain ⟨j, _, hkj⟩ := Finset.mem_biUnion.mp hk
  exact (modes_smul_subset _ _).trans (modes_annA_subset j u) hkj

theorem modes_creVec_subset (f : ℕ →₀ ℂ) (u : FockAlg) :
    modes (creVec f u) ⊆ f.support ∪ modes u := by
  rw [creVec_apply]
  refine (modes_sum_subset f.support (fun j => (f j) • creA j u)).trans ?_
  intro k hk
  obtain ⟨j, hj, hkj⟩ := Finset.mem_biUnion.mp hk
  have h1 : k ∈ modes (creA j u) := (modes_smul_subset (f j) (creA j u)) hkj
  rcases Finset.mem_insert.mp (modes_creA_subset j u h1) with h | h
  · exact Finset.mem_union_left _ (h ▸ hj)
  · exact Finset.mem_union_right _ h

/-- **The drift cannot leave the `Fin d` mode sector.**  Annihilation does not change the modes
at all, and creation only adds modes drawn from the coupling's support, so a coupling supported
on the first `d` modes maps the sector into itself. -/
theorem modes_driftField_subset (f : ℕ →₀ ℂ) (u : FockAlg) :
    modes (driftField f u) ⊆ f.support ∪ modes u := by
  rw [driftField_apply]
  refine (modes_sub_subset (creVec f u) (annVec f u)).trans ?_
  refine Finset.union_subset (modes_creVec_subset f u) ?_
  exact (modes_annVec_subset f u).trans Finset.subset_union_right

theorem InSector.driftField (b : Fin d → ℂ) {u : FockAlg} (h : InSector d u) :
    InSector d (driftField (sectorVec b) u) :=
  (modes_driftField_subset (sectorVec b) u).trans
    (Finset.union_subset (support_sectorVec b) h)

/-- In the sector, every mode beyond `d` is annihilated: `a_k = 0` on the sector for `k ≥ d`. -/
theorem annA_eq_zero_of_sector {u : FockAlg} (h : InSector d u) {k : ℕ} (hk : d ≤ k) :
    annA k u = 0 := by
  refine annA_eq_zero_of_not_mem_modes (fun hmem => ?_)
  have hm := h hmem
  rw [Finset.mem_range] at hm
  omega

/-- **The number form reindexed onto `Fin d`.**  On the sector, `⟪u, N u⟫` is the sum of the
`d` mode contributions `‖aᵢ u‖²` — the corpus form of §5's `numberForm`. -/
theorem numberQuad_eq_sum_fin {u : FockAlg} (h : InSector d u) :
    numberQuad u = ∑ i : Fin d, ‖toLp (annA (i : ℕ) u)‖ ^ 2 := by
  rw [numberQuad_eq_sum (K := Finset.range d) h]
  exact Finset.sum_range (fun j => ‖toLp (annA j u)‖ ^ 2)

end Sector

/-! ## 9. The Hermite expansion of the gradient: the multiplication law `x_j = (a_j + a_j†)/√2`

The module's honest boundary recorded the Hermite expansion of `∇Φ` as the missing input of
Module 3.  Half of it is the multiplication law, and that half is here: `x_j` on the core is the
two-letter ladder word `(a_j† + a_j)/√2`, with the *same* Hermite amplitudes `√(n_j + 1)` and
`√(n_j)` the drift uses.  Together with `driftOpCoeff` (the gradient `∂_j = (a_j − a_j†)/√2`),
this is the dictionary that turns a polynomial in `(x, ∂)` into a finite family of ladder words:
every `x_j` and every `∂_j` is a word of length one, and a monomial of degree `k` becomes a word
of length `≤ k`. -/

/-- **The Hermite multiplication `x_j = (a_j + a_j†)/√2` on the core**: two ladder words of length
one with the Hermite normalization `1/√2`.  This is the `x_j = (a_j + a_j†)/√2` half of the
expansion, the mirror image of `driftOpCoeff`'s `∂_j = (a_j − a_j†)/√2`. -/
def mulHermite (j : Fin d) (c : CoreCoeff d) : CoreCoeff d :=
  (invSqrtTwo : ℂ) • (hopStep (j, true) c + hopStep (j, false) c)

/-- A ladder letter sends the zero family to zero. -/
theorem hopStep_zero (p : Fin d × Bool) : hopStep p (0 : CoreCoeff d) = 0 := by
  unfold hopStep
  simp

/-- **A ladder letter is additive** on the core: linearity in the coefficient family, the first
half of the linearity the expansion needs. -/
theorem hopStep_add (p : Fin d × Bool) (x y : CoreCoeff d) :
    hopStep p (x + y) = hopStep p x + hopStep p y := by
  unfold hopStep
  exact Finsupp.sum_add_index' (fun a => by simp) (fun a b₁ b₂ => by simp [mul_add])

/-- A ladder letter commutes with finite sums. -/
theorem hopStep_sum {ι : Type*} (p : Fin d × Bool) (s : Finset ι) (g : ι → CoreCoeff d) :
    hopStep p (∑ i ∈ s, g i) = ∑ i ∈ s, hopStep p (g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [hopStep_zero]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, hopStep_add, ih]

/-- **Words concatenate**: applying `w₁` and then `w₂` is applying the concatenated word. -/
theorem hopWord_append : ∀ (w₁ w₂ : List (Fin d × Bool)) (c : CoreCoeff d),
    hopWord (w₁ ++ w₂) c = hopWord w₂ (hopWord w₁ c) := by
  intro w₁
  induction w₁ with
  | nil => intro w₂ c; rfl
  | cons p w ih =>
    intro w₂ c
    change hopWord (w ++ w₂) (hopStep p c) = hopWord w₂ (hopWord w (hopStep p c))
    exact ih w₂ (hopStep p c)

/-- A two-letter word, spelled out: the letters are applied right to left. -/
theorem hopWord_two (p q : Fin d × Bool) (c : CoreCoeff d) :
    hopWord [p, q] c = hopStep q (hopStep p c) := rfl

/-- A one-letter word is a single letter. -/
theorem hopWord_single (p : Fin d × Bool) (c : CoreCoeff d) :
    hopWord [p] c = hopStep p c := rfl

/-- **A ladder letter is `ℂ`-linear** on the core (scalar half). -/
theorem hopStep_smul (p : Fin d × Bool) (r : ℂ) (x : CoreCoeff d) :
    hopStep p (r • x) = r • hopStep p x := by
  unfold hopStep
  rw [Finsupp.sum_smul_index' (fun i => by simp)]
  simp only [Finsupp.smul_single, smul_eq_mul, mul_left_comm, Finsupp.sum, Finset.smul_sum]

/-- The multiplication law is additive on the core. -/
theorem mulHermite_add (j : Fin d) (x y : CoreCoeff d) :
    mulHermite j (x + y) = mulHermite j x + mulHermite j y := by
  simp only [mulHermite, hopStep_add, smul_add]
  abel

/-- The multiplication law is `ℂ`-linear on the core. -/
theorem mulHermite_smul (j : Fin d) (r : ℂ) (c : CoreCoeff d) :
    mulHermite j (r • c) = r • mulHermite j c := by
  rw [mulHermite, mulHermite, hopStep_smul, hopStep_smul, smul_add, smul_add, smul_smul,
    smul_smul, mul_comm (invSqrtTwo : ℂ) r, smul_add, smul_smul, smul_smul]

/-- **The two-mode product law**: multiplying twice is `1/2` times the sum of the four length-two
ladder words.  This is the first nontrivial case of the multimode expansion — the `2^2` word
family with the amplitudes carried by the `hopStep`s. -/
theorem mulHermite_comp (j k : Fin d) (c : CoreCoeff d) :
    mulHermite k (mulHermite j c)
      = ((invSqrtTwo : ℂ) * invSqrtTwo) •
          (hopWord [(j, true), (k, true)] c + hopWord [(j, true), (k, false)] c
            + hopWord [(j, false), (k, true)] c + hopWord [(j, false), (k, false)] c) := by
  rw [mulHermite, mulHermite, hopStep_smul, hopStep_smul, hopStep_add, hopStep_add]
  rw [← smul_add, ← smul_smul]
  congr 1
  rw [← hopWord_two, ← hopWord_two, ← hopWord_two, ← hopWord_two]
  abel

/-- **The multiplication law, written as the sum of its two ladder words** — the form the
expansion consumes, with the coefficient `1/√2` pushed onto each letter. -/
theorem mulHermite_eq_ladderWords (j : Fin d) (c : CoreCoeff d) :
    mulHermite j c
      = ((invSqrtTwo : ℝ) : ℂ) • hopStep (j, true) c
        + ((invSqrtTwo : ℝ) : ℂ) • hopStep (j, false) c := by
  simp only [mulHermite, smul_add]

/-- **The gradient's ladder words**, symmetrically: `K_drift = −Σ_j b_j ∂_j` is the two-letter
family `−b_j/√2 · a_j` and `+b_j/√2 · a_j†`, separated into the lowering and raising sums. -/
theorem driftOpCoeff_eq_ladderWords (b : Fin d → ℝ) (c : CoreCoeff d) :
    driftOpCoeff b c
      = ∑ j : Fin d, (((-(b j)) * invSqrtTwo : ℝ) : ℂ) • hopStep (j, false) c
        + ∑ j : Fin d, (((b j) * invSqrtTwo : ℝ) : ℂ) • hopStep (j, true) c :=
  Finset.sum_add_distrib

/-- **The dictionary is complete for linear potentials.**  If `Φ(u) = Σ_j c_j u_j` then
`∂_j Φ = c_j`, so the drift coefficient is `b_j = (β²σ²/2)·c_j` and `K_drift` is the ladder-word
family of `driftOpCoeff`.  This is the case of the Hermite expansion in which `∇Φ` is constant,
proved for every mode family `b`; the polynomial case needs the induction over `MvPolynomial`
that composes `mulHermite` (the words of `x`) with `driftOpCoeff` (the words of `∂`), which the
corpus does not yet have. -/
-- the coefficients of a linear potential's gradient need no further identity: `b` *is* `∇Φ` up
-- to the constant `β²σ²/2`, and `driftOpCoeff` is by definition the ladder-word expansion of it.
example (b : Fin d → ℝ) (c : CoreCoeff d) :
    driftOpCoeff b c
      = ∑ j : Fin d, (((-(b j)) * invSqrtTwo : ℝ) : ℂ) • hopStep (j, false) c
        + ∑ j : Fin d, (((b j) * invSqrtTwo : ℝ) : ℂ) • hopStep (j, true) c :=
  driftOpCoeff_eq_ladderWords b c

/-! ## 9.2 The multimode expansion: the `2^k` word family

§9.1 proved the multiplication law and its two-mode composition.  The general statement of
`pcnl.md` Module 3 is the expansion of a *product* of multiplication laws, i.e. of a monomial
`∏ⱼ xⱼ`, and it is a finite family of words: one ladder word per choice of raise or lower letter
at each of the modes in the list, with the Hermite normalization `2^{-k/2}`.

The family is generated recursively (`mulWords`), so the `2^k` count is a theorem
(`mulWords_card`) and the disjointness that a `Finset.biUnion` needs is not combinatorial
bookkeeping but the statement that a word determines the modes it was built from: dropping the
head recovers the tail (`sum_mulWords_cons`).  Linearity of a word (`hopWord_add`,
`hopWord_smul`) then makes the induction on the mode list a single `smul_add` per step. -/

/-- **The word family of a mode list**: one ladder letter per mode, for each of the `2^k` choices
of raise or lower. -/
def mulWords : List (Fin d) → Finset (List (Fin d × Bool))
  | [] => {[]}
  | j :: js => (mulWords js).biUnion fun w => {((j, true) :: w), ((j, false) :: w)}

/-- **Splitting the word family at a leading mode.**  The two words built from a tail `w` are
distinct, and the families over different tails are disjoint because a word determines its tail
through `List.tail`.  Hence the sum over the doubled family is the sum of the two shifted sums,
which is the induction step of the multimode expansion. -/
theorem sum_mulWords_cons {M : Type*} [AddCommMonoid M] (j : Fin d) (js : List (Fin d))
    (F : List (Fin d × Bool) → M) :
    ∑ u ∈ mulWords (j :: js), F u
      = ∑ w ∈ mulWords js, (F ((j, true) :: w) + F ((j, false) :: w)) := by
  classical
  have hdisj : ∀ a ∈ mulWords js, ∀ b ∈ mulWords js, a ≠ b →
      Disjoint ({((j, true) :: a), ((j, false) :: a)} : Finset (List (Fin d × Bool)))
        {((j, true) :: b), ((j, false) :: b)} := by
    intro a _ b _ hab
    refine Finset.disjoint_left.2 fun x hx hx' => ?_
    have ha : List.tail x = a := by
      rcases Finset.mem_insert.mp hx with h | h
      · rw [h]; rfl
      · rw [Finset.mem_singleton.mp h]; rfl
    have hb : List.tail x = b := by
      rcases Finset.mem_insert.mp hx' with h | h
      · rw [h]; rfl
      · rw [Finset.mem_singleton.mp h]; rfl
    exact hab (ha.symm.trans hb)
  rw [mulWords, Finset.sum_biUnion hdisj]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [Finset.sum_insert (by simp), Finset.sum_singleton]

/-- **The `2^k` count**: a product of `k` multiplication laws expands in exactly `2^k` ladder
words. -/
theorem mulWords_card (js : List (Fin d)) : (mulWords js).card = 2 ^ js.length := by
  classical
  induction js with
  | nil => simp [mulWords]
  | cons j js ih =>
    have hdisj : ∀ a ∈ mulWords js, ∀ b ∈ mulWords js, a ≠ b →
        Disjoint ({((j, true) :: a), ((j, false) :: a)} : Finset (List (Fin d × Bool)))
          {((j, true) :: b), ((j, false) :: b)} := by
      intro a _ b _ hab
      refine Finset.disjoint_left.2 fun x hx hx' => ?_
      have ha : List.tail x = a := by
        rcases Finset.mem_insert.mp hx with h | h
        · rw [h]; rfl
        · rw [Finset.mem_singleton.mp h]; rfl
      have hb : List.tail x = b := by
        rcases Finset.mem_insert.mp hx' with h | h
        · rw [h]; rfl
        · rw [Finset.mem_singleton.mp h]; rfl
      exact hab (ha.symm.trans hb)
    have hpair : ∀ w ∈ mulWords js,
        ({((j, true) :: w), ((j, false) :: w)} : Finset (List (Fin d × Bool))).card = 2 := by
      intro w _
      rw [Finset.card_insert_of_notMem (by simp), Finset.card_singleton]
    rw [mulWords, Finset.card_biUnion hdisj]
    rw [Finset.sum_congr rfl hpair, Finset.sum_const, ih, List.length_cons, pow_succ]
    simp [Nat.mul_comm]

/-- A ladder word sends the zero family to zero. -/
theorem hopWord_zero (w : List (Fin d × Bool)) : hopWord w (0 : CoreCoeff d) = 0 := by
  induction w with
  | nil => rfl
  | cons p w ih => rw [hopWord, hopStep_zero, ih]

/-- A ladder word is additive on the core. -/
theorem hopWord_add (w : List (Fin d × Bool)) (x y : CoreCoeff d) :
    hopWord w (x + y) = hopWord w x + hopWord w y := by
  induction w generalizing x y with
  | nil => rfl
  | cons p w ih =>
    rw [hopWord, hopWord, hopWord, hopStep_add]
    exact ih _ _

/-- A ladder word is `ℂ`-linear on the core. -/
theorem hopWord_smul (w : List (Fin d × Bool)) (r : ℂ) (x : CoreCoeff d) :
    hopWord w (r • x) = r • hopWord w x := by
  induction w generalizing x with
  | nil => rfl
  | cons p w ih =>
    rw [hopWord, hopWord, hopStep_smul]
    exact ih _

/-- **Multiplying by a list of modes**: the multiplication laws applied in order. -/
def mulHermiteList : List (Fin d) → CoreCoeff d → CoreCoeff d
  | [], c => c
  | j :: js, c => mulHermiteList js (mulHermite j c)

@[simp] theorem mulHermiteList_nil (c : CoreCoeff d) : mulHermiteList [] c = c := rfl

theorem mulHermiteList_cons (j : Fin d) (js : List (Fin d)) (c : CoreCoeff d) :
    mulHermiteList (j :: js) c = mulHermiteList js (mulHermite j c) := rfl

/-- The two shifted one-letter sums are the sum over the doubled family: a word on `(j, b) :: w`
is by definition `w` applied after `hopStep (j, b)`. -/
theorem sum_mulWords_hopStep (j : Fin d) (js : List (Fin d)) (c : CoreCoeff d) :
    ∑ w ∈ mulWords js, (hopWord w (hopStep (j, true) c) + hopWord w (hopStep (j, false) c))
      = ∑ u ∈ mulWords (j :: js), hopWord u c := by
  rw [sum_mulWords_cons]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [hopWord, hopWord]

/-- **The general multimode Hermite expansion — `pcnl.md` Module 3.**  A product of `k`
multiplication laws is `2^{-k/2}` times the sum of the `2^k` ladder words over the modes, one word
per choice of raise or lower letter.  Each word carries the Hermite amplitudes `√(nⱼ+1)` and
`√(nⱼ)` of its letters through `hopStep`, so this is the expansion of `∏ⱼ xⱼ` — hence of every
monomial of a potential `Φ`, and with `driftOpCoeff` (the same dictionary for `∂`) of every
`∂`-monomial as well.  It is the general case of §9.1's two-mode product law. -/
theorem mulHermiteList_eq_ladderWords (js : List (Fin d)) (c : CoreCoeff d) :
    mulHermiteList js c
      = ((invSqrtTwo ^ js.length : ℝ) : ℂ) • ∑ w ∈ mulWords js, hopWord w c := by
  induction js generalizing c with
  | nil => simp [mulHermiteList, mulWords, hopWord]
  | cons j js ih =>
    have hstep : ∀ w ∈ mulWords js,
        hopWord w (((invSqrtTwo : ℝ) : ℂ) • hopStep (j, true) c
            + ((invSqrtTwo : ℝ) : ℂ) • hopStep (j, false) c)
          = ((invSqrtTwo : ℝ) : ℂ) •
              (hopWord w (hopStep (j, true) c) + hopWord w (hopStep (j, false) c)) := by
      intro w _
      rw [hopWord_add, hopWord_smul, hopWord_smul, smul_add]
    rw [mulHermiteList_cons, ih, mulHermite_eq_ladderWords, List.length_cons,
      Finset.sum_congr rfl hstep, ← Finset.smul_sum, sum_mulWords_hopStep, smul_smul]
    congr 1
    rw [← Complex.ofReal_mul, ← pow_succ]

/-- The two-mode product law of §9.1 is the `k = 2` case of the multimode expansion. -/
theorem mulHermiteList_pair (j k : Fin d) (c : CoreCoeff d) :
    mulHermiteList [j, k] c
      = ((invSqrtTwo ^ 2 : ℝ) : ℂ) • ∑ w ∈ mulWords [j, k], hopWord w c :=
  mulHermiteList_eq_ladderWords [j, k] c

/-- The `k = 2` word family has four elements, as `mulHermite_comp` displays them. -/
theorem mulWords_pair_card (j k : Fin d) : (mulWords [j, k]).card = 4 :=
  mulWords_card [j, k]

/-! ## 9.3 The mode calculus: letters at distinct modes commute

`pcnl.md` Module 3's last unfinished item is "the induction that *feeds*" §9.2's expansion: a
general potential `Φ` is a sum of monomials `∏ⱼ xⱼ ^ (m ⱼ)`, so interpolating a polynomial from
its monomial expansions is bookkeeping over `MvPolynomial`.  That bookkeeping needs one
*mathematical* input the earlier sections do not carry: the multiplication laws of **distinct**
modes commute on the core, so a monomial's word family may be listed in any mode order.  Without it
`monomialList (m + n)` and `monomialList m ++ monomialList n` are different lists of the same
letters, and no exponent can be read back from the words.

This section proves the input (`hopStep_comm`, `mulHermite_comm`), records its list form
(`mulHermiteList_perm`) and its exponent form (`mulHermiteList_monomialList_add`), and defines the
mode list of a monomial (`monomialList`).  §9.4 then carries out the interpolation itself.

**Why commutation is not free.**  At a *single* mode the letters do not commute
(`aⱼ aⱼ† − aⱼ† aⱼ = 1`): the amplitudes shift by the occupation.  At distinct modes they do,
and the proof is exactly that the two updates touch disjoint coordinates — `stepIdx_comm` —
together with the amplitude factorization `stepAmp_stepIdx_of_ne`.
-/

/-- A core state is the sum of its single-occupation terms.  This is what turns a ladder word into a
finite sum of single-letter computations. -/
theorem eq_sum_singles (x : CoreCoeff d) :
    x = ∑ n ∈ x.support, Finsupp.single n (x n) :=
  (Finsupp.sum_single x).symm

/-- A ladder letter at one mode leaves another mode's occupation alone. -/
theorem stepIdx_apply_of_ne {j k : Fin d} (hjk : j ≠ k) (b : Bool) (n : Fin d → ℕ) :
    stepIdx b k n j = n j := by
  cases b <;> simp [stepIdx, raiseIdx, lowerIdx, Function.update_of_ne hjk]

/-- **Ladder letters at distinct modes commute** on occupations. -/
theorem stepIdx_comm {j k : Fin d} (hjk : j ≠ k) (b b' : Bool) (n : Fin d → ℕ) :
    stepIdx b j (stepIdx b' k n) = stepIdx b' k (stepIdx b j n) := by
  funext i
  by_cases hij : i = j
  · subst hij
    cases b <;> cases b' <;>
      simp [stepIdx, raiseIdx, lowerIdx, Function.update_of_ne hjk]
  · by_cases hik : i = k
    · subst hik
      cases b <;> cases b' <;>
        simp [stepIdx, raiseIdx, lowerIdx, Function.update_of_ne hij]
    · cases b <;> cases b' <;>
        simp [stepIdx, raiseIdx, lowerIdx, Function.update_of_ne hij, Function.update_of_ne hik]

/-- **The amplitude of a letter at one mode is untouched by a letter at another.**  This is the
factorization `amp_j ∘ update_k = amp_j` that makes the two commuted compositions have the same
coefficient. -/
theorem stepAmp_stepIdx_of_ne {j k : Fin d} (hjk : j ≠ k) (b b' : Bool) (n : Fin d → ℕ) :
    stepAmp b j (stepIdx b' k n) = stepAmp b j n := by
  have h : stepIdx b' k n j = n j := stepIdx_apply_of_ne hjk b' n
  cases b <;> simp [stepAmp, h]

/-- One ladder letter on a single occupation: a single shifted occupation with the Hermite
amplitude. -/
theorem hopStep_single (j : Fin d) (b : Bool) (m : Fin d → ℕ) (a : ℂ) :
    hopStep (j, b) (Finsupp.single m a)
      = Finsupp.single (stepIdx b j m) (stepAmp b j m * a) := by
  unfold hopStep
  rw [Finsupp.sum_single_index (by simp)]

/-- **Ladder letters at distinct modes commute** on the core.  Proved by writing the state as the
sum of its single-occupation terms (`hopStep` is additive, `hopStep_sum`) and checking one pair of
letters, where `stepIdx_comm` matches the occupations and `stepAmp_stepIdx_of_ne` the amplitudes. -/
theorem hopStep_comm {j k : Fin d} (hjk : j ≠ k) (b b' : Bool) (c : CoreCoeff d) :
    hopStep (j, b) (hopStep (k, b') c) = hopStep (k, b') (hopStep (j, b) c) := by
  conv_lhs => rw [eq_sum_singles c]
  conv_rhs => rw [eq_sum_singles c]
  rw [hopStep_sum, hopStep_sum, hopStep_sum, hopStep_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [hopStep_single, hopStep_single, hopStep_single, hopStep_single, stepIdx_comm hjk b b' n,
    stepAmp_stepIdx_of_ne hjk b b' n, stepAmp_stepIdx_of_ne hjk.symm b' b n, mul_left_comm]

/-- **The multiplication laws of distinct modes commute.**  Multiplication by `xⱼ` and by `xₖ`
act on the core as operators that commute; this is what lets a monomial be expanded with its
letters in any order.  The two `mulHermite_comp` expansions list the same four two-letter words. -/
theorem mulHermite_comm {j k : Fin d} (hjk : j ≠ k) (c : CoreCoeff d) :
    mulHermite j (mulHermite k c) = mulHermite k (mulHermite j c) := by
  rw [mulHermite_comp k j c, mulHermite_comp j k c]
  congr 1
  simp only [hopWord_two]
  rw [hopStep_comm hjk true true c, hopStep_comm hjk false true c,
    hopStep_comm hjk true false c, hopStep_comm hjk false false c]
  abel_nf

/-- **Words concatenate**: applying `l₁` and then `l₂` is applying the concatenated word. -/
theorem mulHermiteList_append (l₁ l₂ : List (Fin d)) (c : CoreCoeff d) :
    mulHermiteList (l₁ ++ l₂) c = mulHermiteList l₂ (mulHermiteList l₁ c) := by
  induction l₁ generalizing c with
  | nil => rfl
  | cons j js ih => simp only [List.cons_append, mulHermiteList_cons, ih]

/-- A word of multiplication laws is additive on the core. -/
theorem mulHermiteList_add (l : List (Fin d)) (x y : CoreCoeff d) :
    mulHermiteList l (x + y) = mulHermiteList l x + mulHermiteList l y := by
  induction l generalizing x y with
  | nil => rfl
  | cons j js ih => simp only [mulHermiteList_cons, mulHermite_add, ih]

/-- A word of multiplication laws is `ℂ`-linear on the core. -/
theorem mulHermiteList_smul (l : List (Fin d)) (r : ℂ) (x : CoreCoeff d) :
    mulHermiteList l (r • x) = r • mulHermiteList l x := by
  induction l generalizing x with
  | nil => rfl
  | cons j js ih => simp only [mulHermiteList_cons, mulHermite_smul, ih]

/-- **A word of multiplication laws depends only on the multiset of its modes**: permuting the
mode list leaves the operator unchanged.  The `swap'` case is `mulHermite_comm` (or triviality when
the two swapped modes coincide). -/
theorem mulHermiteList_perm {l₁ l₂ : List (Fin d)} (h : List.Perm l₁ l₂) (c : CoreCoeff d) :
    mulHermiteList l₁ c = mulHermiteList l₂ c := by
  induction h using List.Perm.recOnSwap' generalizing c with
  | nil => rfl
  | cons x _ ih => simpa only [mulHermiteList_cons] using ih (mulHermite x c)
  | swap' x y _ ih =>
    by_cases hxy : x = y
    · subst hxy
      simpa only [mulHermiteList_cons] using ih (mulHermite x (mulHermite x c))
    · simp only [mulHermiteList_cons]
      rw [mulHermite_comm (Ne.symm hxy)]
      exact ih (mulHermite x (mulHermite y c))
  | trans _ _ ih₁ ih₂ => exact (ih₁ c).trans (ih₂ c)

/-- **The mode list of a monomial `∏ⱼ xⱼ ^ (m ⱼ)`**: mode `j` appears `m j` times, in the
canonical mode order `0, 1, …, d − 1`.  Its operator is the monomial's word family
(`monomialList_append_perm` below says the list is additive up to that order). -/
def monomialList (m : Fin d → ℕ) : List (Fin d) :=
  (List.finRange d).flatMap fun j => List.replicate (m j) j

/-- **Pointwise addition of exponents is concatenation of mode lists, up to permutation.**  The two
lists list the same letters: the interleaved `m j + n j` copies against all `m` copies followed by
all `n` copies of the same mode. -/
theorem flatMap_replicate_perm (l : List (Fin d)) (m n : Fin d → ℕ) :
    List.Perm ((l.flatMap fun j => List.replicate (m j) j)
        ++ (l.flatMap fun j => List.replicate (n j) j))
      (l.flatMap fun j => List.replicate (m j + n j) j) :=
  (List.flatMap_append_perm l (fun j => List.replicate (m j) j)
      (fun j => List.replicate (n j) j)).trans
    (List.Perm.flatMap_left l fun j _ => by rw [List.replicate_add])

/-- The exponent form of `flatMap_replicate_perm` for `monomialList`. -/
theorem monomialList_append_perm (m n : Fin d → ℕ) :
    List.Perm (monomialList m ++ monomialList n) (monomialList fun j => m j + n j) :=
  flatMap_replicate_perm (List.finRange d) m n

/-- **The monomial word family is multiplicative in the exponent**: the operator of `m + n` is the
operator of `m` followed by the operator of `n`.  This is the identity the polynomial interpolation
of §9.4 consumes. -/
theorem mulHermiteList_monomialList_add (m n : Fin d → ℕ) (c : CoreCoeff d) :
    mulHermiteList (monomialList fun j => m j + n j) c
      = mulHermiteList (monomialList n) (mulHermiteList (monomialList m) c) := by
  rw [mulHermiteList_perm (monomialList_append_perm m n).symm c, mulHermiteList_append]

/-- The two orders of two monomial word families agree: the exponent of the composed word is a sum,
and sums commute. -/
theorem mulHermiteList_monomialList_comm (m n : Fin d → ℕ) (c : CoreCoeff d) :
    mulHermiteList (monomialList m) (mulHermiteList (monomialList n) c)
      = mulHermiteList (monomialList n) (mulHermiteList (monomialList m) c) := by
  rw [← mulHermiteList_monomialList_add n m, ← mulHermiteList_monomialList_add m n]
  congr 1
  exact congrArg monomialList (funext fun j => Nat.add_comm (n j) (m j))

/-- No mode in a list excludes a mode, so the unit exponent is supported nowhere. -/
theorem flatMap_replicate_single_of_notMem (l : List (Fin d)) {j : Fin d} (hj : j ∉ l) :
    l.flatMap (fun k => List.replicate ((Finsupp.single j (1 : ℕ)) k) k) = [] := by
  induction l with
  | nil => rfl
  | cons a as ih =>
    have ha : a ≠ j := fun h => hj (by rw [← h]; exact List.mem_cons_self)
    have has : j ∉ as := fun h => hj (by simp only [List.mem_cons]; exact Or.inr h)
    rw [List.flatMap_cons, ih has]
    have h0 : (Finsupp.single j (1 : ℕ)) a = 0 := by simp [ha]
    rw [h0, List.replicate_zero, List.nil_append]

/-- The unit exponent's mode list is the single mode. -/
theorem flatMap_replicate_single (l : List (Fin d)) {j : Fin d} (hl : l.Nodup) (hj : j ∈ l) :
    l.flatMap (fun k => List.replicate ((Finsupp.single j (1 : ℕ)) k) k) = [j] := by
  induction l with
  | nil => exact absurd hj (List.not_mem_nil)
  | cons a as ih =>
    have htl : a ∉ as := (List.nodup_cons.mp hl).1
    have hnd : as.Nodup := (List.nodup_cons.mp hl).2
    rw [List.flatMap_cons]
    by_cases ha : a = j
    · subst ha
      rw [flatMap_replicate_single_of_notMem as htl]
      simp
    · have has : j ∈ as := by
        rcases List.mem_cons.mp hj with h | h
        · exact absurd h.symm ha
        · exact h
      have h0 : (Finsupp.single j (1 : ℕ)) a = 0 := by simp [ha]
      rw [h0, List.replicate_zero, List.nil_append]
      exact ih hnd has

/-- **The mode list of the unit exponent is the single mode**, so the word family of `X j` is the
single multiplication law `xⱼ = (aⱼ + aⱼ†)/√2` of §9.1. -/
theorem monomialList_single (j : Fin d) :
    monomialList (fun k => (Finsupp.single j (1 : ℕ)) k) = [j] :=
  flatMap_replicate_single (List.finRange d) (List.nodup_finRange d) (List.mem_finRange j)

/-! ## 9.4 The polynomial interpolation: `Φ` is a finite sum of monomial word families

`pcnl.md` Module 3's expansion, at the polynomial level.  §9.2 proved that *one monomial* is a
finite family of ladder words; `mulHermiteList_monomialList_add` above makes the family
multiplicative in the exponent, so the only remaining step is the finite sum over the monomials of
`Φ`.

`polyMul Φ` is that sum: for every monomial of `Φ` its word family of §9.2, weighted by the
coefficient.  `polyMul_mul` is the interpolation theorem — `polyMul` is multiplicative, i.e. it is
the algebra homomorphism `X j ↦ mulHermite j` continued to `MvPolynomial (Fin d) ℂ` — and
`polyMul_X` checks the dictionary at the generators.  That is the content `FockLangevinOperator`
was missing: the drift's ladder expansion for an arbitrary potential `Φ`, not only for a linear
one.

**Boundary.**  This is the *multiplication* side.  `K_drift = −Σⱼ bⱼ ∂ⱼ` needs the same
interpolation for the *derivative* polynomials `∂ⱼ Φ`, which is a second application of `polyMul`
to `MvPolynomial.derivative` — not carried out here — plus the Metropolis filter `K_reject`,
which is not a finite-band operator at all.
-/

/-- **The operator of a polynomial**: the sum of its monomial word families, weighted by the
coefficients — `pcnl.md` Module 3's expansion for a general potential. -/
def polyMul (Φ : MvPolynomial (Fin d) ℂ) (c : CoreCoeff d) : CoreCoeff d :=
  ∑ m ∈ Φ.support, MvPolynomial.coeff m Φ • mulHermiteList (monomialList fun j => m j) c

@[simp] theorem polyMul_zero (c : CoreCoeff d) :
    polyMul (0 : MvPolynomial (Fin d) ℂ) c = 0 := by
  classical
  simp [polyMul]

/-- **The polynomial operator is additive** in the polynomial. -/
theorem polyMul_add (Φ Ψ : MvPolynomial (Fin d) ℂ) (c : CoreCoeff d) :
    polyMul (Φ + Ψ) c = polyMul Φ c + polyMul Ψ c := by
  classical
  unfold polyMul
  rw [Finset.sum_subset (MvPolynomial.support_add (p := Φ) (q := Ψ)) (fun m _ hm => by
    have h0 : MvPolynomial.coeff m (Φ + Ψ) = 0 := by
      by_contra h
      exact hm (Finsupp.mem_support_iff.mpr h)
    simp [h0])]
  simp only [MvPolynomial.coeff_add, add_smul, Finset.sum_add_distrib]
  congr 1
  · exact (Finset.sum_subset Finset.subset_union_left (fun m _ hm => by
      have h0 : MvPolynomial.coeff m Φ = 0 := by
        by_contra h
        exact hm (Finsupp.mem_support_iff.mpr h)
      simp [h0])).symm
  · exact (Finset.sum_subset Finset.subset_union_right (fun m _ hm => by
      have h0 : MvPolynomial.coeff m Ψ = 0 := by
        by_contra h
        exact hm (Finsupp.mem_support_iff.mpr h)
      simp [h0])).symm

/-- Additivity over a finite family of polynomials. -/
theorem polyMul_sum {ι : Type*} (s : Finset ι) (f : ι → MvPolynomial (Fin d) ℂ)
    (c : CoreCoeff d) :
    polyMul (∑ i ∈ s, f i) c = ∑ i ∈ s, polyMul (f i) c := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, polyMul_add, ih]

/-- **The operator of a monomial is its word family** — `polyMul` evaluated on the monomial
basis. -/
theorem polyMul_monomial (m : Fin d →₀ ℕ) (a : ℂ) (c : CoreCoeff d) :
    polyMul (MvPolynomial.monomial m a) c
      = a • mulHermiteList (monomialList fun j => m j) c := by
  classical
  unfold polyMul
  rw [Finset.sum_subset MvPolynomial.support_monomial_subset (fun x hx hx' => by
    have h0 : MvPolynomial.coeff x (MvPolynomial.monomial m a) = 0 := by
      by_contra h
      exact hx' (Finsupp.mem_support_iff.mpr h)
    simp [h0])]
  rw [Finset.sum_singleton]
  simp

/-- **The dictionary at the generators**: the operator of `X j` is the multiplication law
`mulHermite j = (1/√2)(aⱼ† + aⱼ)` of §9.1.  So `polyMul` really is "multiply by `Φ`". -/
theorem polyMul_X (j : Fin d) (c : CoreCoeff d) :
    polyMul (MvPolynomial.X j) c = mulHermite j c := by
  simp only [MvPolynomial.X, polyMul_monomial, monomialList_single, one_smul,
    mulHermiteList_cons, mulHermiteList_nil]

/-- The polynomial operator is additive in the state. -/
theorem polyMul_add_arg (Φ : MvPolynomial (Fin d) ℂ) (x y : CoreCoeff d) :
    polyMul Φ (x + y) = polyMul Φ x + polyMul Φ y := by
  classical
  unfold polyMul
  simp only [mulHermiteList_add, smul_add, Finset.sum_add_distrib]

/-- The polynomial operator is `ℂ`-linear in the state. -/
theorem polyMul_smul_arg (Φ : MvPolynomial (Fin d) ℂ) (r : ℂ) (x : CoreCoeff d) :
    polyMul Φ (r • x) = r • polyMul Φ x := by
  classical
  unfold polyMul
  rw [Finset.smul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mulHermiteList_smul, smul_smul, smul_smul, mul_comm (MvPolynomial.coeff m Φ)]

/-- **`pcnl.md` Module 3, the polynomial interpolation.**  `polyMul` is multiplicative: the
operator of a product is the composite of the operators.  This is the `MvPolynomial` induction the
plan's status note records as the missing input — every potential `Φ`, not just a linear one, is
a finite sum of monomial word families. -/
theorem polyMul_mul (Φ Ψ : MvPolynomial (Fin d) ℂ) (c : CoreCoeff d) :
    polyMul (Φ * Ψ) c = polyMul Φ (polyMul Ψ c) := by
  classical
  induction Ψ using MvPolynomial.induction_on' with
  | add Ψ₁ Ψ₂ ih₁ ih₂ =>
    rw [mul_add, polyMul_add, ih₁, ih₂, polyMul_add, polyMul_add_arg]
  | monomial m a =>
    have hphi : Φ * MvPolynomial.monomial m a
        = ∑ m' ∈ Φ.support,
            MvPolynomial.monomial (m' + m) (MvPolynomial.coeff m' Φ * a) := by
      conv_lhs => rw [MvPolynomial.as_sum Φ]
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun m' _ => by rw [MvPolynomial.monomial_mul]
    rw [hphi, polyMul_sum]
    simp only [polyMul_monomial, polyMul_smul_arg, Finsupp.add_apply]
    rw [polyMul, Finset.smul_sum]
    refine Finset.sum_congr rfl fun m' _ => ?_
    rw [mulHermiteList_monomialList_add, mulHermiteList_monomialList_comm m m' c]
    simp only [smul_smul]
    rw [mul_comm (MvPolynomial.coeff m' Φ) a]

/-! ## 9.5 The derivative side: `∂ⱼ Φ` is a finite sum of monomial word families

§9.4 expanded the *multiplication* side of the dictionary — `xⱼ = (aⱼ + aⱼ†)/√2` — for an
arbitrary potential.  The drift needs the other side.  `K_drift = −Σⱼ bⱼ ∂ⱼ` with
`bⱼ = (β²σ²/2)·∂ⱼ Φ_ε`, so `∂ⱼ Φ` has to be a ladder-word object too — and it is, for the same
reason: the partial derivative of a polynomial is a polynomial, so `polyMul` applies to it
verbatim.  Mathlib's `MvPolynomial.pderiv` is the algebraic `∂ⱼ`, and on a monomial it does exactly
one thing,

`monomial m a ↦ monomial (m − single j 1) (a · m j)`

(`MvPolynomial.pderiv_monomial`) — each monomial of `Φ` is replaced by one monomial of smaller
exponent.  So `polyMul_derivative` is §9.4's interpolation with `m` replaced by
`m − single j 1` and the coefficient multiplied by `m j`; `polyMul_derivative_eq_ladderWords`
spells the same statement out as the explicit family `∑_{w ∈ mulWords js} hopWord w c` of §9.2, so
`∂ⱼ Φ` is literally a finite family of ladder words with the Hermite amplitudes carried by the
letters; and `polyMul_derivative_X` checks the dictionary at the generators, `∂ⱼ xₖ = δⱼₖ` — the
mirror of `polyMul_X`'s `xⱼ ↦ mulHermite j`.

**Boundary.**  What is *not* here is the composition itself: `K_drift` acts as
`−Σⱼ (β²σ²/2)(∂ⱼ Φ)(x) ∂ⱼ`, i.e. as §9.5's operator composed with the ladder letter
`∂ⱼ = (aⱼ − aⱼ†)/√2` of §5 (`driftOpCoeff`).  Composing the two is a statement about an operator
product, not about either expansion, and it is not formalized.  `K_reject` is a multiplication
operator and is not finite-band at all.
-/

/-- The exponent vector of `∂ⱼ (x ^ m)`: `m` with one copy of mode `j` removed.  `Finsupp`
subtraction on `ℕ`-valued families is truncated at zero, which is exactly right here — if mode `j`
is absent from `m`, the exponent vector is unchanged and the coefficient `m j = 0` kills the term
in `polyMul_derivative`. -/
abbrev lowerExp (m : Fin d →₀ ℕ) (j : Fin d) : Fin d → ℕ :=
  fun k => (m - Finsupp.single j 1 : Fin d →₀ ℕ) k

/-- The defining equation of `lowerExp`, as a rewrite rule. -/
@[simp] theorem lowerExp_apply (m : Fin d →₀ ℕ) (j k : Fin d) :
    lowerExp m j k = (m - Finsupp.single j 1 : Fin d →₀ ℕ) k := rfl

/-- The mode list of the zero exponent is empty: `x ^ 0 = 1` is the empty word. -/
theorem monomialList_zero : monomialList (fun _ : Fin d => 0) = [] := by
  simp [monomialList]

/-- **The operator of a constant polynomial is multiplication by that constant**: `C a` is the
monomial of exponent `0`, whose mode list is empty. -/
theorem polyMul_C (a : ℂ) (c : CoreCoeff d) : polyMul (MvPolynomial.C a) c = a • c := by
  have h : (fun j : Fin d => (0 : Fin d →₀ ℕ) j) = fun _ => 0 := rfl
  rw [MvPolynomial.C_apply, polyMul_monomial, h, monomialList_zero, mulHermiteList_nil]

/-- The operator of `1` is the identity — the `k = 0` case of the monomial dictionary, and the
ingredient that turns `∂ⱼ xₖ = 1` into `polyMul_one`. -/
theorem polyMul_one (c : CoreCoeff d) : polyMul (1 : MvPolynomial (Fin d) ℂ) c = c := by
  rw [← MvPolynomial.C_1, polyMul_C, one_smul]

/-- **The derivative of a monomial, expanded.**  `∂ⱼ (a·x^m) = a·mⱼ·x^{m − eⱼ}`, so its word
family is the family of the lowered exponent, with the coefficient multiplied by `m j` — one
`polyMul_monomial` after `MvPolynomial.pderiv_monomial`. -/
theorem polyMul_derivative_monomial (j : Fin d) (m : Fin d →₀ ℕ) (a : ℂ) (c : CoreCoeff d) :
    polyMul (MvPolynomial.pderiv j (MvPolynomial.monomial m a)) c
      = (a * (m j : ℂ)) • mulHermiteList (monomialList (lowerExp m j)) c := by
  rw [MvPolynomial.pderiv_monomial, polyMul_monomial]

/-- **The derivative side of the interpolation** — `pcnl.md` Module 3.  For an arbitrary potential
`Φ`, `∂ⱼ Φ` is a finite sum of monomial word families: one per monomial of `Φ`, with the exponent
lowered by one in mode `j` and the coefficient multiplied by that mode's exponent.  Applying
`polyMul` to `MvPolynomial.pderiv j` is therefore all the interpolation the gradient needs — the
same `Φ.support` sum as §9.4, over shorter monomials. -/
theorem polyMul_derivative (j : Fin d) (Φ : MvPolynomial (Fin d) ℂ) (c : CoreCoeff d) :
    polyMul (MvPolynomial.pderiv j Φ) c
      = ∑ m ∈ Φ.support, (MvPolynomial.coeff m Φ * (m j : ℂ)) •
          mulHermiteList (monomialList (lowerExp m j)) c := by
  classical
  conv_lhs => rw [MvPolynomial.as_sum Φ]
  rw [map_sum, polyMul_sum]
  exact Finset.sum_congr rfl fun m _ => polyMul_derivative_monomial j m _ c

/-- **The derivative's ladder words.**  The same statement with §9.2's word family written out, so
`∂ⱼ Φ` is literally a finite sum of ladder words with the Hermite amplitudes carried by the
letters — the form the drift consumes. -/
theorem polyMul_derivative_eq_ladderWords (j : Fin d) (Φ : MvPolynomial (Fin d) ℂ)
    (c : CoreCoeff d) :
    polyMul (MvPolynomial.pderiv j Φ) c
      = ∑ m ∈ Φ.support,
          (MvPolynomial.coeff m Φ * (m j : ℂ)
              * ((invSqrtTwo ^ (monomialList (lowerExp m j)).length : ℝ) : ℂ)) •
            ∑ w ∈ mulWords (monomialList (lowerExp m j)), hopWord w c := by
  rw [polyMul_derivative]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [mulHermiteList_eq_ladderWords, smul_smul]

/-- **The dictionary at the derivative generators**: `∂ⱼ xₖ = δⱼₖ`, so the operator of
`∂ⱼ (X k)` is the identity when `j = k` and zero otherwise.  With `polyMul_X`'s
`X j ↦ mulHermite j` this closes the two sides of the dictionary of §9.1. -/
theorem polyMul_derivative_X (j k : Fin d) (c : CoreCoeff d) :
    polyMul (MvPolynomial.pderiv j (MvPolynomial.X k)) c = if j = k then c else 0 := by
  by_cases h : j = k
  · subst h
    rw [MvPolynomial.pderiv_X_self, polyMul_one, if_pos rfl]
  · rw [MvPolynomial.pderiv_X_of_ne (Ne.symm h), polyMul_zero, if_neg h]

/-! ## 9.6 The band of the polynomial operator: degree `≤ K` moves the sector by `K`

§9.4 expanded `Φ` as a finite sum of monomial word families.  This section adds the *size* half of
that expansion — `pcnl.md` §2.2's "finite-band hopping matrix" for a general potential: if
`deg Φ ≤ K`, then `polyMul Φ` maps the sector `{N ≤ N₀}` into `{N ≤ N₀ + K}`, so truncating at
degree `N₀` couples only to degrees `≤ N₀ + K`.

The chain is entirely §1–§3's degree bookkeeping: one multiplication law is a sum of two ladder
letters (`mulHermite_band`), a product of `k` laws is `k` letters (`mulHermiteList_band`), the mode
list of a monomial has length equal to its degree (`monomialList_length`), and a single monomial's
band is therefore its degree (`polyMul_monomial_band`).  The only `MvPolynomial` input is
`MvPolynomial.le_totalDegree`, which reads the degree of a monomial of `Φ` off `Φ.totalDegree`;
`polyMul_band` is then the finite sum over `Φ.support` (`band_finset_sum`).
-/

/-- A `ℂ`-scaled family stays in the sector of the family. -/
theorem mem_support_smul {r : ℂ} {c : CoreCoeff d} {m : Fin d → ℕ}
    (hm : m ∈ (r • c).support) : m ∈ c.support :=
  Finsupp.support_smul hm

/-- A difference of two families stays in the union of their supports. -/
theorem core_support_sub_subset (x y : CoreCoeff d) :
    (x - y).support ⊆ x.support ∪ y.support := by
  rw [sub_eq_add_neg]
  refine Finset.Subset.trans Finsupp.support_add ?_
  rw [Finsupp.support_neg]

/-- **One multiplication law stays in the sector**: `xⱼ` is a sum of the two ladder letters. -/
theorem mulHermite_band {j : Fin d} {c : CoreCoeff d} {N : ℕ}
    (hc : ∀ n ∈ c.support, natDeg n ≤ N) {m : Fin d → ℕ}
    (hm : m ∈ (mulHermite j c).support) : natDeg m ≤ N + 1 := by
  have hs : m ∈ (hopStep (j, true) c + hopStep (j, false) c).support := mem_support_smul hm
  rcases Finset.mem_union.mp (Finsupp.support_add hs) with h | h
  · exact hopStep_band hc h
  · exact hopStep_band hc h

/-- **A product of `k` multiplication laws stays in the sector `{N ≤ N₀ + k}`** — the band of
§9.2's word family, one ladder letter per mode. -/
theorem mulHermiteList_band (js : List (Fin d)) :
    ∀ (c : CoreCoeff d) (N : ℕ), (∀ n ∈ c.support, natDeg n ≤ N) →
      ∀ m ∈ (mulHermiteList js c).support, natDeg m ≤ N + js.length := by
  induction js with
  | nil =>
    intro c N hc m hm
    simpa using hc m hm
  | cons j js ih =>
    intro c N hc m hm
    rw [mulHermiteList_cons] at hm
    have hstep : ∀ n ∈ (mulHermite j c).support, natDeg n ≤ N + 1 :=
      fun n hn => mulHermite_band hc hn
    have hres := ih (mulHermite j c) (N + 1) hstep m hm
    simpa [List.length_cons, Nat.add_assoc, Nat.add_comm, Nat.add_left_comm] using hres

/-- **The length of a monomial's mode list is its degree**: the mode list of `∏ⱼ xⱼ ^ (m ⱼ)` has
`∑ⱼ m ⱼ` letters, so §9.2's word family of a monomial of degree `k` has words of length `k`. -/
theorem monomialList_length (m : Fin d → ℕ) : (monomialList m).length = natDeg m := by
  rw [monomialList, List.length_flatMap, natDeg, Fin.sum_univ_def]
  simp only [List.length_replicate]

/-- The degree of an occupation vector, read on the `Finsupp` exponent of a monomial. -/
theorem natDeg_ofFinsupp (m : Fin d →₀ ℕ) : natDeg (fun j => m j) = m.sum (fun _ e => e) := by
  rw [natDeg, Finsupp.sum_fintype]
  simp

/-- **A monomial of degree `k` stays in the sector `{N ≤ N₀ + k}`.** -/
theorem polyMul_monomial_band (m : Fin d →₀ ℕ) (a : ℂ) (c : CoreCoeff d) {N : ℕ}
    (hc : ∀ n ∈ c.support, natDeg n ≤ N) {m' : Fin d → ℕ}
    (hm : m' ∈ (polyMul (MvPolynomial.monomial m a) c).support) :
    natDeg m' ≤ N + (m.sum fun _ e => e) := by
  rw [polyMul_monomial] at hm
  have hm0 : m' ∈ (mulHermiteList (monomialList fun j => m j) c).support := mem_support_smul hm
  have hb := mulHermiteList_band (monomialList fun j => m j) c N hc m' hm0
  rw [monomialList_length, natDeg_ofFinsupp] at hb
  exact hb

/-- A finite sum of families stays in the sector of its summands. -/
theorem band_finset_sum {ι : Type*} (s : Finset ι) (g : ι → CoreCoeff d) {N K : ℕ}
    (hg : ∀ i ∈ s, ∀ n ∈ (g i).support, natDeg n ≤ N + K) {m : Fin d → ℕ}
    (hm : m ∈ (∑ i ∈ s, g i).support) : natDeg m ≤ N + K := by
  classical
  induction s using Finset.induction with
  | empty => simp at hm
  | insert a s ha ih =>
    rw [Finset.sum_insert ha] at hm
    rcases Finset.mem_union.mp (Finsupp.support_add hm) with h | h
    · exact hg a (Finset.mem_insert_self a s) m h
    · exact ih (fun i hi => hg i (Finset.mem_insert_of_mem hi)) h

/-- **The band of the polynomial operator**: a potential of degree `≤ K` maps the sector
`{N ≤ N₀}` into `{N ≤ N₀ + K}` — `pcnl.md` §2.2's finite-band property for an arbitrary `Φ`, not
only for the linear potentials of §5. -/
theorem polyMul_band {K : ℕ} {Φ : MvPolynomial (Fin d) ℂ} (hK : Φ.totalDegree ≤ K)
    (c : CoreCoeff d) {N : ℕ} (hc : ∀ n ∈ c.support, natDeg n ≤ N) {m : Fin d → ℕ}
    (hm : m ∈ (polyMul Φ c).support) : natDeg m ≤ N + K := by
  classical
  have hsum : polyMul Φ c
      = ∑ m' ∈ Φ.support,
          polyMul (MvPolynomial.monomial m' (MvPolynomial.coeff m' Φ)) c := by
    conv_lhs => rw [MvPolynomial.as_sum Φ]
    exact polyMul_sum Φ.support _ c
  rw [hsum] at hm
  refine band_finset_sum Φ.support _ (fun m' hm' n hn => ?_) hm
  refine le_trans (polyMul_monomial_band m' (MvPolynomial.coeff m' Φ) c hc hn) ?_
  have := MvPolynomial.le_totalDegree hm'
  omega

/-- **The band in the sector form the plan states it.** -/
theorem polyMul_band_sector {K : ℕ} {Φ : MvPolynomial (Fin d) ℂ} (hK : Φ.totalDegree ≤ K)
    (c : CoreCoeff d) {N : ℕ} (hc : ∀ n ∈ c.support, natDeg n ≤ N) :
    ∀ m ∈ (polyMul Φ c).support, natDeg m ≤ N + K :=
  fun _ hm => polyMul_band hK c hc hm

/-! ## 9.7 The drift of a polynomial potential: `K_drift = −Σⱼ (∂ⱼ Φ)(x) ∂ⱼ`

§9.5 expanded `∂ⱼ Φ` as a ladder-word object; what was still missing was the *operator* — the plan's
`K_drift` for a potential, `−Σⱼ (β²σ²/2)(∂ⱼ Φ)(x) ∂ⱼ`, whose coefficient multiplies *after* the
letter `∂ⱼ`.  Both halves now have expansions, so the composition is a definition:

* `diffHermite j` is the letter `∂ⱼ = (aⱼ − aⱼ†)/√2` of §5, as a transformation of the core;
* `polyDrift Φ` is the composition `−Σⱼ polyMul (∂ⱼ Φ) ∘ diffHermite j` — `∂ⱼ` applied to the
  state, then multiplied by the derivative polynomial;
* **`polyDrift_eq_ladderWords`** and **`polyDrift_eq_hopWords`** spell out the resulting family:
  one word per `(j, m, w)`, where `w` runs over the derivative's `2^k` words of §9.2 and the letter
  `∂ⱼ` sits at the *head* of `w` (`hopWord_diffHermite`), the two halves subtracting and the
  Hermite normalization `1/√2` of the letter carried explicitly.

`driftOpCoeff_eq_neg_sum_diffHermite` is the check that this generalizes §5 rather than replacing
it: for a *linear* potential `Φ(u) = Σⱼ cⱼ uⱼ` the derivative `∂ⱼ Φ = cⱼ` is constant, `polyMul` of
a constant is a scalar multiplication (`polyMul_C`), and the composition collapses to §5's
`driftOpCoeff` — the drift with constant coefficients.

**Boundary.**  This is the expansion of `K_drift`, not the relative form bound: `DriftFormBound`
of §5 is still a target (proved in the corpus Fock model in §6), the amplitude estimate
`stepAmp_norm_le` is not yet combined with the band of §9.6 into a norm bound on `polyDrift`, and
`K_reject` — a multiplication operator, hence not finite-band — is outside this model.
-/

/-- The ladder letter `∂ⱼ = (aⱼ − aⱼ†)/√2` of §5, as a transformation of the core. -/
def diffHermite (j : Fin d) (c : CoreCoeff d) : CoreCoeff d :=
  ((invSqrtTwo : ℝ) : ℂ) • (hopStep (j, false) c - hopStep (j, true) c)

/-- A ladder letter sends a negated family to the negated image. -/
theorem hopStep_neg (p : Fin d × Bool) (x : CoreCoeff d) : hopStep p (-x) = -hopStep p x := by
  have h := hopStep_smul p (-1) x
  simpa using h

/-- A ladder letter is additive for differences. -/
theorem hopStep_sub (p : Fin d × Bool) (x y : CoreCoeff d) :
    hopStep p (x - y) = hopStep p x - hopStep p y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, hopStep_add, hopStep_neg]

/-- A ladder word is additive for differences. -/
theorem hopWord_sub (w : List (Fin d × Bool)) (x y : CoreCoeff d) :
    hopWord w (x - y) = hopWord w x - hopWord w y := by
  induction w generalizing x y with
  | nil => rfl
  | cons p w ih => rw [hopWord, hopWord, hopWord, hopStep_sub]; exact ih _ _

/-- The defining equation of `hopWord` at a leading letter, as a rewrite rule. -/
theorem hopWord_cons (p : Fin d × Bool) (w : List (Fin d × Bool)) (c : CoreCoeff d) :
    hopWord (p :: w) c = hopWord w (hopStep p c) := rfl

/-- **The derivative letter inside a word.**  `∂ⱼ` is two ladder letters, so a word ending in `∂ⱼ`
is two ladder words of one letter more, with opposite signs — the identity that turns §9.5's family
for `∂ⱼ Φ` into a family of genuine ladder words. -/
theorem hopWord_diffHermite (j : Fin d) (w : List (Fin d × Bool)) (c : CoreCoeff d) :
    hopWord w (diffHermite j c)
      = ((invSqrtTwo : ℝ) : ℂ) • hopWord ((j, false) :: w) c
        - ((invSqrtTwo : ℝ) : ℂ) • hopWord ((j, true) :: w) c := by
  simp only [diffHermite, hopWord_smul, hopWord_sub, smul_sub]
  rw [hopWord_cons, hopWord_cons]

/-- The letter `∂ⱼ`, with its two scalar coefficients written out. -/
theorem diffHermite_eq_ladderWords (j : Fin d) (c : CoreCoeff d) :
    diffHermite j c
      = ((invSqrtTwo : ℝ) : ℂ) • hopStep (j, false) c
        - ((invSqrtTwo : ℝ) : ℂ) • hopStep (j, true) c := by
  simp only [diffHermite, smul_sub]

/-- **`K_drift` for a polynomial potential**: `−Σⱼ (∂ⱼ Φ)(x) ∂ⱼ`, read on the core as the
composition of §9.5's operator with the letter `∂ⱼ`.  The constant `β²σ²/2` of the plan is
absorbed into `Φ`, exactly as `bⱼ = (β²σ²/2)∂ⱼΦ_ε` is in §5's `driftOpCoeff`. -/
def polyDrift (Φ : MvPolynomial (Fin d) ℂ) (c : CoreCoeff d) : CoreCoeff d :=
  -∑ j : Fin d, polyMul (MvPolynomial.pderiv j Φ) (diffHermite j c)

/-- **The linear-potential case is §5's drift**: with scalar coefficients the composition is
`driftOpCoeff`, so `polyDrift` generalizes `−Σⱼ bⱼ ∂ⱼ` rather than replacing it. -/
theorem driftOpCoeff_eq_neg_sum_diffHermite (b : Fin d → ℝ) (c : CoreCoeff d) :
    driftOpCoeff b c = -∑ j : Fin d, ((b j : ℝ) : ℂ) • diffHermite j c := by
  have hterm : ∀ j : Fin d,
      (((-(b j)) * invSqrtTwo : ℝ) : ℂ) • hopStep (j, false) c +
        (((b j) * invSqrtTwo : ℝ) : ℂ) • hopStep (j, true) c
      = -(((b j : ℝ) : ℂ) • diffHermite j c) := by
    intro j
    have hs : (((b j) * invSqrtTwo : ℝ) : ℂ) = (b j : ℂ) * ((invSqrtTwo : ℝ) : ℂ) := by
      rw [← Complex.ofReal_mul]
    have hs' : (((-(b j)) * invSqrtTwo : ℝ) : ℂ)
        = -((b j : ℂ) * ((invSqrtTwo : ℝ) : ℂ)) := by
      rw [← Complex.ofReal_mul, ← Complex.ofReal_neg]
      congr 1
      ring
    rw [hs, hs', diffHermite, smul_smul, smul_sub, neg_sub, neg_smul]
    abel
  rw [driftOpCoeff, ← Finset.sum_neg_distrib]
  exact Finset.sum_congr rfl fun j _ => hterm j

/-- **The drift's ladder-word family** — `pcnl.md` Module 3's last piece.  For a general potential
`Φ`, `K_drift` is a finite family of ladder words: one per mode `j`, per monomial `m` of `Φ` and per
choice `w` of the derivative's letters (§9.2's `2^k` words), with the Hermite normalization of both
the derivative's letters and the letter `∂ⱼ` carried explicitly. -/
theorem polyDrift_eq_ladderWords (Φ : MvPolynomial (Fin d) ℂ) (c : CoreCoeff d) :
    polyDrift Φ c
      = -∑ j : Fin d, ∑ m ∈ Φ.support,
          (MvPolynomial.coeff m Φ * (m j : ℂ)
              * ((invSqrtTwo ^ (monomialList (lowerExp m j)).length : ℝ) : ℂ)) •
            ∑ w ∈ mulWords (monomialList (lowerExp m j)), hopWord w (diffHermite j c) := by
  rw [polyDrift]
  congr 1
  exact Finset.sum_congr rfl fun j _ => polyMul_derivative_eq_ladderWords j Φ (diffHermite j c)

/-- **The drift's word family, spelled out as ladder words**: the same family, with `∂ⱼ` expanded
by `hopWord_diffHermite`, so every summand is a genuine ladder word of the core — the letter `∂ⱼ` at
the head of the derivative's word `w`, with the two signs of `∂ⱼ = (aⱼ − aⱼ†)/√2`. -/
theorem polyDrift_eq_hopWords (Φ : MvPolynomial (Fin d) ℂ) (c : CoreCoeff d) :
    polyDrift Φ c
      = -∑ j : Fin d, ∑ m ∈ Φ.support,
          ((MvPolynomial.coeff m Φ * (m j : ℂ)
              * ((invSqrtTwo ^ (monomialList (lowerExp m j)).length : ℝ) : ℂ))
            * ((invSqrtTwo : ℝ) : ℂ)) •
            ∑ w ∈ mulWords (monomialList (lowerExp m j)),
              (hopWord ((j, false) :: w) c - hopWord ((j, true) :: w) c) := by
  rw [polyDrift_eq_ladderWords]
  congr 1
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun m _ => ?_
  rw [Finset.smul_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [hopWord_diffHermite, smul_sub, smul_sub, smul_smul, smul_smul]

/-! ## 9.8 The band of the drift: a potential of degree `≤ K` moves the sector by exactly `K`

§9.6 gave the band of the *multiplication* operator and §9.7 built `K_drift` as a composition.
The two together give the band of the drift itself, with the sharp constant: `−Σⱼ (∂ⱼ Φ)(x) ∂ⱼ`
maps `{N ≤ N₀}` into `{N ≤ N₀ + K}` when `deg Φ ≤ K`, so a truncation at degree `N₀` couples only
to `≤ N₀ + K` — the finite-band property of `pcnl.md` §2.2 for the operator the plan calls
`K_drift`, not only for the linear `driftOpCoeff` of §3.

The two degrees cancel exactly, which is why the constant is `K` and not `K + 1`: the derivative
`∂ⱼ Φ` costs one degree (§9.5's lowered exponents), and the letter `∂ⱼ` gives it back.  The
accounting is `diffHermite_band` (the letter moves `N` by at most one), `natDeg_lowerExp` (a
*lowered* exponent has one degree less, `natDeg_lowerIdx_of_pos` being the occupation form of the
same fact), then `polyMul_derivative`'s monomial sum with `polyMul_monomial`'s band.  Note the
`m' j = 0` case: there the coefficient is `0` and the term is absent, which is exactly what makes
the bound sharp at a monomial whose mode `j` is not occupied.
-/

/-- **The letter `∂ⱼ` stays in the sector `{N ≤ N₀ + 1}`**: it is a difference of two ladder
letters, and a ladder letter moves the degree by at most one. -/
theorem diffHermite_band {j : Fin d} {c : CoreCoeff d} {N : ℕ}
    (hc : ∀ n ∈ c.support, natDeg n ≤ N) {m : Fin d → ℕ}
    (hm : m ∈ (diffHermite j c).support) : natDeg m ≤ N + 1 := by
  rw [diffHermite_eq_ladderWords] at hm
  rcases Finset.mem_union.mp (core_support_sub_subset _ _ hm) with h | h
  · exact hopStep_band hc (mem_support_smul h)
  · exact hopStep_band hc (mem_support_smul h)

/-- **Lowering one occupation lowers the total degree by exactly one**, when that occupation is
non-zero — the equality strengthening `natDeg_lowerIdx_le`. -/
theorem natDeg_lowerIdx_of_pos (j : Fin d) (n : Fin d → ℕ) (hn : 0 < n j) :
    natDeg (lowerIdx j n) = natDeg n - 1 := by
  have h1 := sum_erase n j
  have h2 := sum_erase (Function.update n j (n j - 1)) j
  have h3 := sum_erase_update n j (n j - 1)
  have h4 : Function.update n j (n j - 1) j = n j - 1 := by simp
  unfold natDeg lowerIdx
  omega

/-- The exponent of `∂ⱼ (x ^ m)` is `lowerIdx` at mode `j`, read on the occupation vector — the
bridge between §9.5's `lowerExp` and §1's ladder steps. -/
theorem lowerExp_eq_lowerIdx (m : Fin d →₀ ℕ) (j : Fin d) :
    lowerExp m j = fun k => lowerIdx j (fun i => m i) k := by
  funext k
  by_cases hk : k = j
  · subst hk
    simp [lowerExp, lowerIdx]
  · simp [lowerExp, lowerIdx, hk]

/-- **Lowering an exponent lowers the degree by one**, when that mode is occupied: the `Finsupp`
form of `natDeg_lowerIdx_of_pos`, and the identity that keeps §9.8's band sharp. -/
theorem natDeg_lowerExp {m : Fin d →₀ ℕ} {j : Fin d} (hmj : m j ≠ 0) :
    natDeg (lowerExp m j) = natDeg (fun k => m k) - 1 := by
  rw [lowerExp_eq_lowerIdx]
  exact natDeg_lowerIdx_of_pos j (fun i => m i) (Nat.pos_of_ne_zero hmj)

/-- **The band of the drift: `K_drift` is finite-band with band `K`.**  A potential of degree
`≤ K` maps the sector `{N ≤ N₀}` into `{N ≤ N₀ + K}`: the derivative costs one degree and the
letter `∂ⱼ` gives it back, so the plan's `K_drift` couples a truncation at `N₀` only to degrees
`≤ N₀ + K`. -/
theorem polyDrift_band {K : ℕ} {Φ : MvPolynomial (Fin d) ℂ} (hK : Φ.totalDegree ≤ K)
    (c : CoreCoeff d) {N : ℕ} (hc : ∀ n ∈ c.support, natDeg n ≤ N) {m : Fin d → ℕ}
    (hm : m ∈ (polyDrift Φ c).support) : natDeg m ≤ N + K := by
  classical
  rw [polyDrift, Finsupp.support_neg] at hm
  refine band_finset_sum Finset.univ
    (fun j => polyMul (MvPolynomial.pderiv j Φ) (diffHermite j c)) ?_ hm
  intro j _ n hn
  beta_reduce at hn
  rw [polyMul_derivative] at hn
  refine band_finset_sum Φ.support (fun m' =>
    (MvPolynomial.coeff m' Φ * (m' j : ℂ)) •
      mulHermiteList (monomialList (lowerExp m' j)) (diffHermite j c)) ?_ hn
  intro m' hm' n' hn'
  by_cases hmj : m' j = 0
  · simp [hmj] at hn'
  · have hb := mulHermiteList_band (monomialList (lowerExp m' j)) (diffHermite j c) (N + 1)
      (fun x hx => diffHermite_band hc hx) n' (mem_support_smul hn')
    rw [monomialList_length] at hb
    have hdeg : natDeg (fun k => m' k) ≤ K := by
      rw [natDeg_ofFinsupp]
      exact le_trans (MvPolynomial.le_totalDegree hm') hK
    have hle : m' j ≤ natDeg (fun k => m' k) :=
      Finset.single_le_sum (f := fun k => (m' k : ℕ)) (fun i _ => Nat.zero_le _)
        (Finset.mem_univ j)
    have hpos : 0 < natDeg (fun k => m' k) :=
      lt_of_lt_of_le (Nat.pos_of_ne_zero hmj) hle
    have hlow := natDeg_lowerExp hmj
    omega

/-- **The drift's band, in sector form.** -/
theorem polyDrift_band_sector {K : ℕ} {Φ : MvPolynomial (Fin d) ℂ} (hK : Φ.totalDegree ≤ K)
    (c : CoreCoeff d) {N : ℕ} (hc : ∀ n ∈ c.support, natDeg n ≤ N) :
    ∀ m ∈ (polyDrift Φ c).support, natDeg m ≤ N + K :=
  fun _ hm => polyDrift_band hK c hc hm

/-! ## 9.9 The size of the drift: an `ℓ¹` bound from `stepAmp_norm_le` and the band

§9.8 says *where* the drift sends a state; this section says *how big* the image is.  The size used
is the `ℓ¹` mass `coreL1 c = ∑ₙ ‖c n‖`, which needs no orthogonality — only that a ladder letter
moves each source index once, so the two halves of a letter cannot interfere.

* `coreL1`, with `coreL1_add_le`, `coreL1_smul_le`, `coreL1_neg`, `coreL1_finset_sum_le`,
  `coreL1_sub_le` — the triangle inequality in the form the word family consumes;
* **`hopStep_l1_le`** — one letter multiplies the mass by at most `√(N + 1)` on the sector
  `{N ≤ N}`: `stepAmp_norm_le` at every source index;
* **`hopWord_l1_sector`** — a word of length `k` multiplies the mass by at most `(√(M + 1))^k`,
  where `M ≥ N + k` bounds the degrees the word meets (a word walks the sector up one degree per
  letter, §3's `hopStep_band`);
* **`polyDrift_l1_le`** — the drift's own estimate: on `{N ≤ N}` with `M ≥ N + deg Φ + 1`,
  `coreL1 (polyDrift Φ c) ≤ driftL1Bound Φ M * coreL1 c`, `driftL1Bound` being an explicit sector
  constant.  §9.2's `2^k` word count (`mulWords_card`), the degree bound `k ≤ deg Φ`
  (`natDeg_lowerExp_le` with `MvPolynomial.le_totalDegree`) and the normalization `1/√2 ≤ 1` are
  what keep the constant explicit rather than existential.
-/

/-- The `ℓ¹` mass of a core state: the sum of the absolute values of its coefficients.  It is the
cheapest size that survives a ladder letter — no orthogonality is needed, only that a letter moves
every source index once. -/
def coreL1 (c : CoreCoeff d) : ℝ :=
  ∑ n ∈ c.support, ‖c n‖

theorem coreL1_nonneg (c : CoreCoeff d) : 0 ≤ coreL1 c :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

theorem coreL1_single_le (m : Fin d → ℕ) (a : ℂ) : coreL1 (Finsupp.single m a) ≤ ‖a‖ := by
  classical
  refine le_trans (Finset.sum_le_sum_of_subset_of_nonneg Finsupp.support_single_subset
    (fun _ _ _ => norm_nonneg _)) ?_
  rw [Finset.sum_singleton, Finsupp.single_eq_same]

theorem coreL1_add_le (x y : CoreCoeff d) : coreL1 (x + y) ≤ coreL1 x + coreL1 y := by
  classical
  have hzero : ∀ (z : CoreCoeff d) {n : Fin d → ℕ}, n ∉ z.support → z n = 0 :=
    fun z _ hn => Finsupp.notMem_support_iff.mp hn
  calc coreL1 (x + y)
      ≤ ∑ n ∈ x.support ∪ y.support, ‖(x + y) n‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg Finsupp.support_add (fun _ _ _ => norm_nonneg _)
    _ ≤ ∑ n ∈ x.support ∪ y.support, (‖x n‖ + ‖y n‖) :=
        Finset.sum_le_sum fun n _ => norm_add_le _ _
    _ = ∑ n ∈ x.support ∪ y.support, ‖x n‖ + ∑ n ∈ x.support ∪ y.support, ‖y n‖ :=
        Finset.sum_add_distrib
    _ = ∑ n ∈ x.support, ‖x n‖ + ∑ n ∈ y.support, ‖y n‖ := by
        rw [(Finset.sum_subset Finset.subset_union_left
              (fun n _ hn => by rw [hzero x hn]; simp)).symm,
            (Finset.sum_subset Finset.subset_union_right
              (fun n _ hn => by rw [hzero y hn]; simp)).symm]

theorem coreL1_smul_le (r : ℂ) (c : CoreCoeff d) : coreL1 (r • c) ≤ ‖r‖ * coreL1 c := by
  classical
  calc coreL1 (r • c)
      ≤ ∑ n ∈ c.support, ‖(r • c) n‖ :=
        Finset.sum_le_sum_of_subset_of_nonneg Finsupp.support_smul (fun _ _ _ => norm_nonneg _)
    _ = ∑ n ∈ c.support, ‖r‖ * ‖c n‖ := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [Finsupp.smul_apply, norm_smul]
    _ = ‖r‖ * coreL1 c := (Finset.mul_sum _ _ _).symm

theorem coreL1_neg (c : CoreCoeff d) : coreL1 (-c) = coreL1 c := by
  unfold coreL1
  rw [Finsupp.support_neg]
  exact Finset.sum_congr rfl fun n _ => by rw [Finsupp.neg_apply, norm_neg]

theorem coreL1_finset_sum_le {ι : Type*} (s : Finset ι) (g : ι → CoreCoeff d) :
    coreL1 (∑ i ∈ s, g i) ≤ ∑ i ∈ s, coreL1 (g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [coreL1]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    have h1 := coreL1_add_le (g a) (∑ x ∈ s, g x)
    linarith

/-- **A ladder letter multiplies the `ℓ¹` mass by at most `√(N + 1)`** on the degree-`≤ N`
sector: each source index is moved once, and every amplitude is at most `√(N + 1)`
(`stepAmp_norm_le`). -/
theorem hopStep_l1_le (p : Fin d × Bool) (c : CoreCoeff d) {N : ℕ}
    (hc : ∀ n ∈ c.support, natDeg n ≤ N) :
    coreL1 (hopStep p c) ≤ Real.sqrt ((N : ℝ) + 1) * coreL1 c := by
  classical
  rw [hopStep, Finsupp.sum]
  calc coreL1 (∑ n ∈ c.support,
        Finsupp.single (stepIdx p.2 p.1 n) (stepAmp p.2 p.1 n * c n))
      ≤ ∑ n ∈ c.support,
          coreL1 (Finsupp.single (stepIdx p.2 p.1 n) (stepAmp p.2 p.1 n * c n)) :=
        coreL1_finset_sum_le _ _
    _ ≤ ∑ n ∈ c.support, ‖stepAmp p.2 p.1 n‖ * ‖c n‖ :=
        Finset.sum_le_sum fun n _ => le_trans (coreL1_single_le _ _) (by rw [norm_mul])
    _ ≤ ∑ n ∈ c.support, Real.sqrt ((N : ℝ) + 1) * ‖c n‖ := by
        refine Finset.sum_le_sum fun n hn => ?_
        exact mul_le_mul_of_nonneg_right (stepAmp_norm_le p.2 p.1 (hc n hn)) (norm_nonneg _)
    _ = Real.sqrt ((N : ℝ) + 1) * coreL1 c := (Finset.mul_sum _ _ _).symm

/-- **A ladder word multiplies the `ℓ¹` mass by at most `(√(M + 1))^k`**, where `M` bounds the
degree of every index the word meets: on the sector `{N ≤ N}` a word of length `k` only ever sees
degrees `≤ N + k ≤ M`, and each of its `k` letters costs a factor `√(M + 1)`. -/
theorem hopWord_l1_sector (w : List (Fin d × Bool)) :
    ∀ (c : CoreCoeff d) (N M : ℕ), N + w.length ≤ M →
      (∀ n ∈ c.support, natDeg n ≤ N) →
      coreL1 (hopWord w c) ≤ Real.sqrt ((M : ℝ) + 1) ^ w.length * coreL1 c := by
  induction w with
  | nil =>
    intro c N M _ _
    have h : coreL1 (hopWord [] c) = coreL1 c := rfl
    rw [h]
    simp
  | cons p w ih =>
    intro c N M hM hc
    rw [hopWord, List.length_cons]
    have hNM : N + 1 + w.length ≤ M := by
      rw [List.length_cons] at hM
      omega
    have hN1 : N + 1 ≤ M := by omega
    refine le_trans (ih (hopStep p c) (N + 1) M hNM (fun n hn => hopStep_band hc hn)) ?_
    have hstep := hopStep_l1_le p c hc
    have hroot : Real.sqrt ((N : ℝ) + 1) ≤ Real.sqrt ((M : ℝ) + 1) := by
      refine Real.sqrt_le_sqrt ?_
      have hR : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : N ≤ M)
      linarith
    calc Real.sqrt ((M : ℝ) + 1) ^ w.length * coreL1 (hopStep p c)
        ≤ Real.sqrt ((M : ℝ) + 1) ^ w.length
            * (Real.sqrt ((N : ℝ) + 1) * coreL1 c) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ ≤ Real.sqrt ((M : ℝ) + 1) ^ w.length
            * (Real.sqrt ((M : ℝ) + 1) * coreL1 c) := by
          refine mul_le_mul_of_nonneg_left ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right hroot (coreL1_nonneg c)
      _ = Real.sqrt ((M : ℝ) + 1) ^ (w.length + 1) * coreL1 c := by
          rw [pow_succ]
          ring

theorem coreL1_sub_le (x y : CoreCoeff d) : coreL1 (x - y) ≤ coreL1 x + coreL1 y := by
  have h := coreL1_add_le x (-y)
  rw [coreL1_neg] at h
  simpa [sub_eq_add_neg] using h

/-- Every word of a mode list's family has the mode list's length. -/
theorem mulWords_length (js : List (Fin d)) : ∀ w ∈ mulWords js, w.length = js.length := by
  induction js with
  | nil =>
    intro w hw
    rw [mulWords, Finset.mem_singleton] at hw
    rw [hw]
    rfl
  | cons j js ih =>
    intro w hw
    rw [mulWords] at hw
    obtain ⟨a, ha, hw'⟩ := Finset.mem_biUnion.mp hw
    rcases Finset.mem_insert.mp hw' with h | h
    · simp [h, ih a ha]
    · simp [Finset.mem_singleton.mp h, ih a ha]

/-- A lowered exponent never has more degree than the exponent it came from. -/
theorem natDeg_lowerExp_le (m : Fin d →₀ ℕ) (j : Fin d) :
    natDeg (lowerExp m j) ≤ natDeg (fun k => m k) := by
  rw [lowerExp_eq_lowerIdx]
  exact natDeg_lowerIdx_le j _

/-- `1/√2` is nonnegative. -/
theorem invSqrtTwo_nonneg : 0 ≤ invSqrtTwo := by
  rw [invSqrtTwo]
  positivity

/-- `1/√2 ≤ 1`, the normalization bound the `ℓ¹` chain needs. -/
theorem invSqrtTwo_le_one : invSqrtTwo ≤ 1 := by
  rw [invSqrtTwo, one_div]
  exact inv_le_one_of_one_le₀ (Real.one_le_sqrt.mpr (by norm_num))

/-- The sector-uniform `ℓ¹` constant of the drift, at sector parameter `M`. -/
def driftL1Bound (Φ : MvPolynomial (Fin d) ℂ) (M : ℕ) : ℝ :=
  ∑ j : Fin d, ∑ m ∈ Φ.support,
    ‖MvPolynomial.coeff m Φ * (m j : ℂ)‖ * ((2 : ℝ) ^ Φ.totalDegree * 2)
      * Real.sqrt ((M : ℝ) + 1) ^ (Φ.totalDegree + 1)

/-- **The drift's `ℓ¹` bound.**  On the sector `{N ≤ N}` the drift is bounded by the explicit
sector constant `driftL1Bound Φ M`, where `M ≥ N + deg Φ + 1` bounds the degrees met by the
expansion: every ladder word of the family contributes `(√(M + 1))^{k+1}`
(`hopWord_l1_sector`, built from `stepAmp_norm_le`), and there are `2^k` such words per monomial
(`mulWords_card`), with `k ≤ deg Φ` (`natDeg_lowerExp_le` and `le_totalDegree`). -/
theorem polyDrift_l1_le {N M : ℕ} {Φ : MvPolynomial (Fin d) ℂ}
    (hNM : N + Φ.totalDegree + 1 ≤ M) (c : CoreCoeff d)
    (hc : ∀ n ∈ c.support, natDeg n ≤ N) :
    coreL1 (polyDrift Φ c) ≤ driftL1Bound Φ M * coreL1 c := by
  classical
  have hL := coreL1_nonneg c
  have hroot1 : (1 : ℝ) ≤ Real.sqrt ((M : ℝ) + 1) := by
    refine Real.one_le_sqrt.mpr ?_
    have hM0 : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
    linarith
  -- the per-monomial estimate
  have hkey : ∀ (j : Fin d) {m : Fin d →₀ ℕ}, m ∈ Φ.support →
      coreL1 (((MvPolynomial.coeff m Φ * (m j : ℂ)
            * ((invSqrtTwo ^ (monomialList (lowerExp m j)).length : ℝ) : ℂ))
          * ((invSqrtTwo : ℝ) : ℂ)) •
          ∑ w ∈ mulWords (monomialList (lowerExp m j)),
            (hopWord ((j, false) :: w) c - hopWord ((j, true) :: w) c))
      ≤ ‖MvPolynomial.coeff m Φ * (m j : ℂ)‖
          * (((2 : ℝ) ^ Φ.totalDegree * 2)
              * (Real.sqrt ((M : ℝ) + 1) ^ (Φ.totalDegree + 1) * coreL1 c)) := by
    intro j m hm
    set js := monomialList (lowerExp m j) with hjs
    set A : ℂ := (MvPolynomial.coeff m Φ * (m j : ℂ)
        * ((invSqrtTwo ^ js.length : ℝ) : ℂ)) * ((invSqrtTwo : ℝ) : ℂ) with hA
    have hkD : js.length ≤ Φ.totalDegree := by
      rw [hjs, monomialList_length]
      refine le_trans (natDeg_lowerExp_le _ _) ?_
      rw [natDeg_ofFinsupp]
      exact MvPolynomial.le_totalDegree hm
    have hAnorm : ‖A‖ ≤ ‖MvPolynomial.coeff m Φ * (m j : ℂ)‖ := by
      have hpow : ‖((invSqrtTwo ^ js.length : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (pow_nonneg invSqrtTwo_nonneg _)]
        exact pow_le_one₀ invSqrtTwo_nonneg invSqrtTwo_le_one
      have hbase : ‖((invSqrtTwo : ℝ) : ℂ)‖ ≤ 1 := by
        rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg invSqrtTwo_nonneg]
        exact invSqrtTwo_le_one
      have hX : (0 : ℝ) ≤ ‖MvPolynomial.coeff m Φ‖ * ‖((m j : ℂ))‖ := by positivity
      rw [hA, norm_mul, norm_mul, norm_mul]
      calc ‖MvPolynomial.coeff m Φ‖ * ‖((m j : ℂ))‖ * ‖((invSqrtTwo ^ js.length : ℝ) : ℂ)‖
            * ‖((invSqrtTwo : ℝ) : ℂ)‖
          ≤ ‖MvPolynomial.coeff m Φ‖ * ‖((m j : ℂ))‖ * 1 * 1 := by
            refine mul_le_mul (mul_le_mul_of_nonneg_left hpow hX) hbase (by positivity) ?_
            exact mul_nonneg hX (by norm_num)
        _ = ‖MvPolynomial.coeff m Φ‖ * ‖((m j : ℂ))‖ := by ring
    have hword : ∀ (b : Bool) {w : List (Fin d × Bool)}, w ∈ mulWords js →
        coreL1 (hopWord ((j, b) :: w) c)
          ≤ Real.sqrt ((M : ℝ) + 1) ^ (js.length + 1) * coreL1 c := by
      intro b w hw
      have hwlen : w.length = js.length := mulWords_length js w hw
      have hlen : ((j, b) :: w).length = js.length + 1 := by simp [hwlen]
      have h1 := hopWord_l1_sector ((j, b) :: w) c N M (by rw [hlen]; omega) hc
      rwa [hlen] at h1
    have hsum : ∑ w ∈ mulWords js,
        (coreL1 (hopWord ((j, false) :: w) c) + coreL1 (hopWord ((j, true) :: w) c))
        ≤ ((2 : ℝ) ^ Φ.totalDegree * 2)
            * (Real.sqrt ((M : ℝ) + 1) ^ (Φ.totalDegree + 1) * coreL1 c) := by
      have hstep : ∀ w ∈ mulWords js,
          (coreL1 (hopWord ((j, false) :: w) c) + coreL1 (hopWord ((j, true) :: w) c))
            ≤ 2 * (Real.sqrt ((M : ℝ) + 1) ^ (js.length + 1) * coreL1 c) := by
        intro w hw
        have h1 := hword false hw
        have h2 := hword true hw
        linarith
      have hcard : ((mulWords js).card : ℝ) = (2 : ℝ) ^ js.length := by
        rw [mulWords_card, Nat.cast_pow, Nat.cast_ofNat]
      have hpow2 : (2 : ℝ) ^ js.length ≤ (2 : ℝ) ^ Φ.totalDegree :=
        pow_le_pow_right₀ (by norm_num) hkD
      have hpowr : Real.sqrt ((M : ℝ) + 1) ^ (js.length + 1)
          ≤ Real.sqrt ((M : ℝ) + 1) ^ (Φ.totalDegree + 1) :=
        pow_le_pow_right₀ hroot1 (by omega)
      have hnon : (0 : ℝ) ≤ Real.sqrt ((M : ℝ) + 1) ^ (js.length + 1) * coreL1 c :=
        mul_nonneg (by positivity) hL
      calc ∑ w ∈ mulWords js,
            (coreL1 (hopWord ((j, false) :: w) c) + coreL1 (hopWord ((j, true) :: w) c))
          ≤ ∑ _w ∈ mulWords js,
              2 * (Real.sqrt ((M : ℝ) + 1) ^ (js.length + 1) * coreL1 c) :=
            Finset.sum_le_sum hstep
        _ = ((mulWords js).card : ℝ)
              * (2 * (Real.sqrt ((M : ℝ) + 1) ^ (js.length + 1) * coreL1 c)) := by
            rw [Finset.sum_const, nsmul_eq_mul]
        _ = ((2 : ℝ) ^ js.length * 2)
              * (Real.sqrt ((M : ℝ) + 1) ^ (js.length + 1) * coreL1 c) := by
            rw [hcard]; ring
        _ ≤ ((2 : ℝ) ^ Φ.totalDegree * 2)
              * (Real.sqrt ((M : ℝ) + 1) ^ (Φ.totalDegree + 1) * coreL1 c) := by
            refine mul_le_mul (mul_le_mul_of_nonneg_right hpow2 (by norm_num))
              (mul_le_mul_of_nonneg_right hpowr hL) (by positivity) (by positivity)
    calc coreL1 (A • ∑ w ∈ mulWords js,
          (hopWord ((j, false) :: w) c - hopWord ((j, true) :: w) c))
        ≤ ‖A‖ * coreL1 (∑ w ∈ mulWords js,
            (hopWord ((j, false) :: w) c - hopWord ((j, true) :: w) c)) :=
          coreL1_smul_le A _
      _ ≤ ‖A‖ * ∑ w ∈ mulWords js,
            (coreL1 (hopWord ((j, false) :: w) c) + coreL1 (hopWord ((j, true) :: w) c)) := by
          refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg A)
          exact le_trans (coreL1_finset_sum_le _ _)
            (Finset.sum_le_sum fun w _ => coreL1_sub_le _ _)
      _ ≤ ‖A‖ * (((2 : ℝ) ^ Φ.totalDegree * 2)
            * (Real.sqrt ((M : ℝ) + 1) ^ (Φ.totalDegree + 1) * coreL1 c)) :=
          mul_le_mul_of_nonneg_left hsum (norm_nonneg A)
      _ ≤ ‖MvPolynomial.coeff m Φ * (m j : ℂ)‖ * (((2 : ℝ) ^ Φ.totalDegree * 2)
            * (Real.sqrt ((M : ℝ) + 1) ^ (Φ.totalDegree + 1) * coreL1 c)) :=
          mul_le_mul_of_nonneg_right hAnorm (by positivity)
  rw [polyDrift_eq_hopWords, coreL1_neg]
  calc coreL1 (∑ j : Fin d, ∑ m ∈ Φ.support,
        ((MvPolynomial.coeff m Φ * (m j : ℂ)
            * ((invSqrtTwo ^ (monomialList (lowerExp m j)).length : ℝ) : ℂ))
          * ((invSqrtTwo : ℝ) : ℂ)) •
          ∑ w ∈ mulWords (monomialList (lowerExp m j)),
            (hopWord ((j, false) :: w) c - hopWord ((j, true) :: w) c))
      ≤ ∑ j : Fin d, coreL1 (∑ m ∈ Φ.support,
          ((MvPolynomial.coeff m Φ * (m j : ℂ)
              * ((invSqrtTwo ^ (monomialList (lowerExp m j)).length : ℝ) : ℂ))
            * ((invSqrtTwo : ℝ) : ℂ)) •
            ∑ w ∈ mulWords (monomialList (lowerExp m j)),
              (hopWord ((j, false) :: w) c - hopWord ((j, true) :: w) c)) :=
        coreL1_finset_sum_le _ _
    _ ≤ ∑ j : Fin d, ∑ m ∈ Φ.support,
          ‖MvPolynomial.coeff m Φ * (m j : ℂ)‖ * (((2 : ℝ) ^ Φ.totalDegree * 2)
              * (Real.sqrt ((M : ℝ) + 1) ^ (Φ.totalDegree + 1) * coreL1 c)) := by
        refine Finset.sum_le_sum fun j _ => ?_
        exact le_trans (coreL1_finset_sum_le _ _) (Finset.sum_le_sum fun m hm => hkey j hm)
    _ = driftL1Bound Φ M * coreL1 c := by
        rw [driftL1Bound, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Finset.sum_mul]
        exact Finset.sum_congr rfl fun m _ => by ring

/-! ## 9.10 The pCNL Hamiltonian of a polynomial potential

§4 built the pCNL shape `P₀ + K_drift` from a *list* of ladder words.  The drift is now
`polyDrift` itself (§9.7), so the same shape is available for an arbitrary polynomial potential,
and its band is §9.8's sharp `K` rather than a word-length count:

* `pcnlPolyHamiltonian Φ = numberOp + polyDrift Φ` — the diagonal `P₀`/number part plus `K_drift`;
* **`pcnlPolyHamiltonian_band`** — a potential of degree `≤ K` maps the sector `{N ≤ N₀}` into
  `{N ≤ N₀ + K}`: the number part does not move the degree at all (`mem_support_numberOp`) and the
  drift contributes `K` (§9.8), so a truncation at `N₀` couples only to degrees `≤ N₀ + K`;
* `polyDrift_linear` — for a linear potential `Φ(u) = Σₖ bₖ uₖ` the drift *is* §5's
  `driftOpCoeff b`, so the new Hamiltonian generalizes the `driftOpCoeff` one rather than
  replacing it.
-/

/-- **The pCNL Hamiltonian of a polynomial potential**: the diagonal number part plus `K_drift`
itself (`polyDrift`, §9.7), rather than a list of ladder words as in §4. -/
def pcnlPolyHamiltonian (Φ : MvPolynomial (Fin d) ℂ) (c : CoreCoeff d) : CoreCoeff d :=
  numberOp c + polyDrift Φ c

/-- **Finite band for the pCNL Hamiltonian of a polynomial potential.**  A potential of degree
`≤ K` maps the sector `{N ≤ N₀}` into `{N ≤ N₀ + K}`: the diagonal part stays in the sector, the
drift moves it by `K` (§9.8). -/
theorem pcnlPolyHamiltonian_band {K : ℕ} {Φ : MvPolynomial (Fin d) ℂ} (hK : Φ.totalDegree ≤ K)
    (c : CoreCoeff d) {N : ℕ} (hc : ∀ n ∈ c.support, natDeg n ≤ N) {m : Fin d → ℕ}
    (hm : m ∈ (pcnlPolyHamiltonian Φ c).support) : natDeg m ≤ N + K := by
  rw [pcnlPolyHamiltonian] at hm
  rcases Finset.mem_union.mp (Finsupp.support_add hm) with h1 | h2
  · exact le_trans (hc m (mem_support_numberOp h1)) (by omega)
  · exact polyDrift_band hK c hc h2

/-- **The linear potential is §5's drift.**  For `Φ(u) = Σₖ bₖ uₖ` the derivative is the constant
`bⱼ`, so `polyDrift Φ` is §5's `driftOpCoeff b` — the sense in which §9.7 and §9.10 generalize
`−Σⱼ bⱼ ∂ⱼ` rather than replacing it. -/
theorem polyDrift_linear (b : Fin d → ℝ) (c : CoreCoeff d) :
    polyDrift (∑ k : Fin d, MvPolynomial.C ((b k : ℝ) : ℂ) * MvPolynomial.X k) c
      = driftOpCoeff b c := by
  classical
  have hpderiv : ∀ j : Fin d,
      MvPolynomial.pderiv j (∑ k : Fin d, MvPolynomial.C ((b k : ℝ) : ℂ) * MvPolynomial.X k)
        = MvPolynomial.C ((b j : ℝ) : ℂ) := by
    intro j
    rw [map_sum]
    refine (Finset.sum_eq_single j ?_ ?_).trans ?_
    · intro k _ hk
      rw [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X_of_ne hk, mul_zero]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
    · rw [MvPolynomial.pderiv_C_mul, MvPolynomial.pderiv_X_self, mul_one]
  rw [polyDrift, driftOpCoeff_eq_neg_sum_diffHermite]
  congr 1
  exact Finset.sum_congr rfl fun j _ => by rw [hpderiv j, polyMul_C]

/-! ## 10. The `ℓ²` action of one letter: coordinates, norms, and the oscillator identity

§9.9 measured a state by its `ℓ¹` mass.  The relative form bound of §5 is an `ℓ²` statement, and the
one input the plan's chain names as *not bookkeeping* is the oscillator identity
`∑ⱼ (‖a_j c‖² + ‖a_j† c‖²) = 2⟪c, N c⟫ + d‖c‖²`.  This section proves it on the core.

* `hopStep_coord_lower` / `hopStep_coord_raise` — the *coordinates* of one letter:
  `(a_j c)(m) = √(m_j + 1)·c(m + e_j)` and `(a_j† c)(m) = √(m_j)·c(m − e_j)`.  The lowering formula
  hides something: `m` has *two* preimages under `lowerIdx` when `m_j = 0` (`m` itself and
  `m + e_j`), and they collapse into one formula because the extra term carries `√(m_j) = 0`.
  Raising is injective (`raiseIdx_injective`), so its formula has one preimage;
* **`coreNormSq_hopStep_lower`** — `‖a_j c‖² = ∑ₙ nⱼ‖c n‖²`, via the bijection `m ↦ m + e_j` from
  the support of `a_j c` onto the `j`-occupied part of `c`'s support (`hopStep_coord_lower_at` gives
  the value on it, `mem_support_hopStep_lower` the support bookkeeping);
* **`coreNormSq_hopStep_raise`** — `‖a_j† c‖² = ∑ₙ (nⱼ + 1)‖c n‖²`, the same with the bijection in
  the other direction, `m ↦ m − e_j`;
* `sum_coreNormSq_hopStep_lower` / `sum_coreNormSq_hopStep_raise` — the two mode sums:
  `∑ⱼ ‖a_j c‖² = ⟪c, N c⟫` and `∑ⱼ ‖a_j† c‖² = ⟪c, N c⟫ + d‖c‖²`;
* **`oscillator_identity`** — their sum, the identity the plan's chain needs.

**Boundary.**  What is still not here is the Cauchy–Schwarz step in the core pairing and the
`2ab ≤ δa² + b²/δ` chain that turn these norms into `DriftFormBound` (§5).  The norms themselves —
and with them the one input the earlier notes called analytic rather than bookkeeping — are proved.
-/

/-- Lowering mode `j` at mode `j`. -/
theorem lowerIdx_apply_same (j : Fin d) (n : Fin d → ℕ) : lowerIdx j n j = n j - 1 := by
  simp [lowerIdx, Function.update_self]

/-- Lowering mode `j` leaves another mode alone. -/
theorem lowerIdx_apply_of_ne {j k : Fin d} (hk : k ≠ j) (n : Fin d → ℕ) :
    lowerIdx j n k = n k := by
  simp [lowerIdx, hk]

/-- Raising mode `j` at mode `j`. -/
theorem raiseIdx_apply_same (j : Fin d) (n : Fin d → ℕ) : raiseIdx j n j = n j + 1 := by
  simp [raiseIdx, Function.update_self]

/-- Raising mode `j` leaves another mode alone. -/
theorem raiseIdx_apply_of_ne {j k : Fin d} (hk : k ≠ j) (n : Fin d → ℕ) :
    raiseIdx j n k = n k := by
  simp [raiseIdx, hk]

/-- Raising a *lowered* occupation gives the occupation back, when that mode is occupied: the
saturation at `0` is what the hypothesis rules out. -/
theorem raiseIdx_lowerIdx_of_pos (j : Fin d) {n : Fin d → ℕ} (hn : n j ≠ 0) :
    raiseIdx j (lowerIdx j n) = n := by
  funext k
  by_cases hk : k = j
  · subst hk
    rw [raiseIdx_apply_same, lowerIdx_apply_same]
    omega
  · rw [raiseIdx_apply_of_ne hk, lowerIdx_apply_of_ne hk]

/-- Lowering a raised occupation gives it back, unconditionally. -/
theorem lowerIdx_raiseIdx (j : Fin d) (n : Fin d → ℕ) : lowerIdx j (raiseIdx j n) = n := by
  funext k
  by_cases hk : k = j
  · subst hk; rw [lowerIdx_apply_same, raiseIdx_apply_same]; simp
  · rw [lowerIdx_apply_of_ne hk, raiseIdx_apply_of_ne hk]

/-- The lowering step is `lowerIdx`. -/
theorem stepIdx_false (j : Fin d) (n : Fin d → ℕ) : stepIdx false j n = lowerIdx j n := rfl

/-- The raising step is `raiseIdx`. -/
theorem stepIdx_true (j : Fin d) (n : Fin d → ℕ) : stepIdx true j n = raiseIdx j n := rfl

/-- **The coordinates of a lowered state**: `(a_j c)(m) = √(m_j + 1) · c(m + e_j)`.  The two
preimages of `m` under `lowerIdx` (namely `m` itself, when `m_j = 0`, and `m + e_j`) collapse to a
single formula because the `m`-term carries the amplitude `√(m_j) = 0`. -/
theorem hopStep_coord_lower (j : Fin d) (c : CoreCoeff d) (m : Fin d → ℕ) :
    hopStep (j, false) c m
      = ((Real.sqrt ((m j : ℝ) + 1) : ℝ) : ℂ) * c (raiseIdx j m) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp [hopStep_zero]
  | add x y hx hy =>
    rw [hopStep_add, Finsupp.add_apply, hx, hy, Finsupp.add_apply, mul_add]
  | single n a =>
    rw [hopStep_single, stepIdx_false, stepAmp_lower, Finsupp.single_apply,
      Finsupp.single_apply]
    by_cases hn : n j = 0
    · have hlow : lowerIdx j n = n := by
        funext k
        by_cases hk : k = j
        · subst hk; rw [lowerIdx_apply_same, hn]
        · rw [lowerIdx_apply_of_ne hk]
      have hneq : n ≠ raiseIdx j m := by
        intro he
        have hc := congrFun he j
        rw [raiseIdx_apply_same] at hc
        omega
      rw [hlow, if_neg hneq]
      simp [hn]
    · by_cases h : lowerIdx j n = m
      · have hnval : n j = m j + 1 := by
          have := congrFun h j
          rw [lowerIdx_apply_same] at this
          omega
        have hne : n = raiseIdx j m := by
          funext k
          by_cases hk : k = j
          · subst hk; rw [hnval, raiseIdx_apply_same]
          · rw [raiseIdx_apply_of_ne hk]
            have := congrFun h k
            rwa [lowerIdx_apply_of_ne hk] at this
        rw [if_pos h, if_pos hne, hnval]
        push_cast
        ring
      · have hne : n ≠ raiseIdx j m := fun he => h (by rw [he, lowerIdx_raiseIdx])
        rw [if_neg h, if_neg hne, mul_zero]

/-- **The coordinates of a raised state**: `(a_j† c)(m) = √(m_j) · c(m − e_j)`.  Raising is
injective, so every target has at most one preimage. -/
theorem hopStep_coord_raise (j : Fin d) (c : CoreCoeff d) (m : Fin d → ℕ) :
    hopStep (j, true) c m
      = ((Real.sqrt (m j : ℝ) : ℝ) : ℂ) * c (lowerIdx j m) := by
  classical
  induction c using Finsupp.induction_linear with
  | zero => simp [hopStep_zero]
  | add x y hx hy =>
    rw [hopStep_add, Finsupp.add_apply, hx, hy, Finsupp.add_apply, mul_add]
  | single n a =>
    rw [hopStep_single, stepIdx_true, stepAmp_raise, Finsupp.single_apply,
      Finsupp.single_apply]
    by_cases h : raiseIdx j n = m
    · have hmn : m = raiseIdx j n := h.symm
      have hmj : lowerIdx j m = n := by rw [hmn, lowerIdx_raiseIdx]
      have hval : m j = n j + 1 := by rw [hmn, raiseIdx_apply_same]
      rw [if_pos h, if_pos hmj.symm, hval]
      push_cast
      ring
    · rw [if_neg h]
      by_cases hmj : n = lowerIdx j m
      · have hm0 : m j = 0 := by
          by_contra hm0
          exact h (by rw [hmj]; exact raiseIdx_lowerIdx_of_pos j hm0)
        rw [if_pos hmj, hm0]
        simp
      · rw [if_neg hmj, mul_zero]

theorem raiseIdx_injective (j : Fin d) : Function.Injective (raiseIdx j) := by
  intro x y h
  have := congrArg (lowerIdx j) h
  simpa [lowerIdx_raiseIdx] using this

/-- The coordinates of a raised state, at the raised index of an occupied one. -/
theorem hopStep_coord_raise_at (j : Fin d) (c : CoreCoeff d) (n : Fin d → ℕ) :
    hopStep (j, true) c (raiseIdx j n)
      = ((Real.sqrt ((n j : ℝ) + 1) : ℝ) : ℂ) * c n := by
  rw [hopStep_coord_raise, raiseIdx_apply_same, lowerIdx_raiseIdx]
  push_cast
  ring

/-- The coordinates of a lowered state, at the lowered index of an occupied one. -/
theorem hopStep_coord_lower_at (j : Fin d) (c : CoreCoeff d) {n : Fin d → ℕ} (hn : n j ≠ 0) :
    hopStep (j, false) c (lowerIdx j n)
      = ((Real.sqrt (n j : ℝ) : ℝ) : ℂ) * c n := by
  rw [hopStep_coord_lower, raiseIdx_lowerIdx_of_pos j hn]
  have h1 : 1 ≤ n j := Nat.one_le_iff_ne_zero.mpr hn
  have h2 : ((lowerIdx j n j : ℕ) : ℝ) + 1 = (n j : ℝ) := by
    rw [lowerIdx_apply_same, Nat.cast_sub h1]
    push_cast
    ring
  rw [h2]

/-- Raising is supported: the raised index of a supported index is supported. -/
theorem mem_support_hopStep_raise {j : Fin d} {c : CoreCoeff d} {n : Fin d → ℕ}
    (hn : n ∈ c.support) : raiseIdx j n ∈ (hopStep (j, true) c).support := by
  rw [Finsupp.mem_support_iff, hopStep_coord_raise_at]
  have hc : c n ≠ 0 := Finsupp.mem_support_iff.mp hn
  have hsqrt : ((Real.sqrt ((n j : ℝ) + 1) : ℝ) : ℂ) ≠ 0 := by
    have hpos : (0 : ℝ) < Real.sqrt ((n j : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    exact_mod_cast ne_of_gt hpos
  exact mul_ne_zero hsqrt hc

/-- The mode of a supported index of a raised state is occupied. -/
theorem mem_support_hopStep_raise_pos {j : Fin d} {c : CoreCoeff d} {m : Fin d → ℕ}
    (hm : m ∈ (hopStep (j, true) c).support) : m j ≠ 0 := by
  have hcoord := hopStep_coord_raise j c m
  have hne : ((Real.sqrt (m j : ℝ) : ℝ) : ℂ) * c (lowerIdx j m) ≠ 0 := by
    rw [← hcoord]
    exact Finsupp.mem_support_iff.mp hm
  intro h0
  have : ((Real.sqrt (m j : ℝ) : ℝ) : ℂ) = 0 := by
    rw [h0]; simp
  exact hne (by rw [this, zero_mul])

/-- Raising is supported down to an occupied index: `m − e_j` is supported by `a_j† c`. -/
theorem mem_support_hopStep_raise_lower {j : Fin d} {c : CoreCoeff d} {m : Fin d → ℕ}
    (hm : m ∈ (hopStep (j, true) c).support) : lowerIdx j m ∈ c.support := by
  have hcoord := hopStep_coord_raise j c m
  have hne : ((Real.sqrt (m j : ℝ) : ℝ) : ℂ) * c (lowerIdx j m) ≠ 0 := by
    rw [← hcoord]
    exact Finsupp.mem_support_iff.mp hm
  exact Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hne)

/-- Lowering is supported above `0`: if `m` is supported by `a_j c`, then `m + e_j` is occupied. -/
theorem mem_support_hopStep_lower {j : Fin d} {c : CoreCoeff d} {m : Fin d → ℕ}
    (hm : m ∈ (hopStep (j, false) c).support) :
    raiseIdx j m ∈ c.support ∧ (raiseIdx j m) j ≠ 0 := by
  classical
  have hcoord := hopStep_coord_lower j c m
  have hne : ((Real.sqrt ((m j : ℝ) + 1) : ℝ) : ℂ) * c (raiseIdx j m) ≠ 0 := by
    rw [← hcoord]
    exact Finsupp.mem_support_iff.mp hm
  refine ⟨Finsupp.mem_support_iff.mpr (right_ne_zero_of_mul hne), ?_⟩
  rw [raiseIdx_apply_same]
  omega

/-- **The norm of a raised state**: `‖a_j† c‖² = ∑ₙ (nⱼ + 1)‖c n‖²`. -/
theorem coreNormSq_hopStep_raise (j : Fin d) (c : CoreCoeff d) :
    coreNormSq (hopStep (j, true) c)
      = ∑ n ∈ c.support, ((n j : ℝ) + 1) * ‖c n‖ ^ 2 := by
  classical
  have hval : ∀ m ∈ (hopStep (j, true) c).support,
      ‖hopStep (j, true) c m‖ ^ 2 = (m j : ℝ) * ‖c (lowerIdx j m)‖ ^ 2 := by
    intro m _
    rw [hopStep_coord_raise, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (by positivity)]
  rw [coreNormSq]
  rw [Finset.sum_bij (fun m _ => lowerIdx j m)]
  · -- image in the target support
    intro m hm
    exact mem_support_hopStep_raise_lower hm
  · -- injective on the source support
    intro m₁ hm₁ m₂ hm₂ h
    have h1 := mem_support_hopStep_raise_pos hm₁
    have h2 := mem_support_hopStep_raise_pos hm₂
    rw [← raiseIdx_lowerIdx_of_pos j h1, ← raiseIdx_lowerIdx_of_pos j h2, h]
  · -- surjective onto the target support
    intro n hn
    exact ⟨raiseIdx j n, mem_support_hopStep_raise hn, lowerIdx_raiseIdx j n⟩
  · -- the values agree
    intro m hm
    have hmj := mem_support_hopStep_raise_pos hm
    have h1 : 1 ≤ m j := Nat.one_le_iff_ne_zero.mpr hmj
    have h2 : ((lowerIdx j m j : ℕ) : ℝ) + 1 = (m j : ℝ) := by
      rw [lowerIdx_apply_same, Nat.cast_sub h1]
      push_cast
      ring
    rw [hval m hm, ← h2]

/-- **The norm of a lowered state**: `‖a_j c‖² = ∑ₙ nⱼ‖c n‖²`.  The bijection is between the
support of `a_j c` and the occupied-at-`j` part of `c`'s support, `m ↦ m + e_j`; the terms with
`nⱼ = 0` are dropped, and they are `0` anyway. -/
theorem coreNormSq_hopStep_lower (j : Fin d) (c : CoreCoeff d) :
    coreNormSq (hopStep (j, false) c) = ∑ n ∈ c.support, (n j : ℝ) * ‖c n‖ ^ 2 := by
  classical
  have hdrop : ∑ n ∈ c.support.filter (fun n => n j ≠ 0), (n j : ℝ) * ‖c n‖ ^ 2
      = ∑ n ∈ c.support, (n j : ℝ) * ‖c n‖ ^ 2 := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun n _ => ?_
    by_cases hn : n j = 0 <;> simp [hn]
  rw [← hdrop, coreNormSq]
  refine Finset.sum_bij (fun m _ => raiseIdx j m) ?_ ?_ ?_ ?_
  · intro m hm
    exact Finset.mem_filter.mpr (mem_support_hopStep_lower hm)
  · intro a₁ _ a₂ _ h
    exact raiseIdx_injective j h
  · intro n hn
    obtain ⟨hnc, hnj⟩ := Finset.mem_filter.mp hn
    refine ⟨lowerIdx j n, ?_, raiseIdx_lowerIdx_of_pos j hnj⟩
    rw [Finsupp.mem_support_iff, hopStep_coord_lower_at j c hnj]
    have hc : c n ≠ 0 := Finsupp.mem_support_iff.mp hnc
    have hsqrt : ((Real.sqrt (n j : ℝ) : ℝ) : ℂ) ≠ 0 := by
      have hpos : (0 : ℝ) < Real.sqrt (n j : ℝ) :=
        Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hnj)
      exact_mod_cast ne_of_gt hpos
    exact mul_ne_zero hsqrt hc
  · intro m hm
    rw [hopStep_coord_lower, Complex.norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), mul_pow, Real.sq_sqrt (by positivity)]
    beta_reduce
    rw [raiseIdx_apply_same]
    push_cast
    ring

/-- **The number form is the sum of the lowering letters' norms**: `∑ⱼ ‖a_j c‖² = ⟪c, N c⟫`. -/
theorem sum_coreNormSq_hopStep_lower (c : CoreCoeff d) :
    ∑ j : Fin d, coreNormSq (hopStep (j, false) c) = numberForm c := by
  classical
  rw [numberForm]
  simp only [coreNormSq_hopStep_lower, natDeg, Nat.cast_sum, Finset.sum_mul]
  rw [Finset.sum_comm]

/-- **The sum of the raising letters' norms**: `∑ⱼ ‖a_j† c‖² = ⟪c, N c⟫ + d·‖c‖²`. -/
theorem sum_coreNormSq_hopStep_raise (c : CoreCoeff d) :
    ∑ j : Fin d, coreNormSq (hopStep (j, true) c)
      = numberForm c + (d : ℝ) * coreNormSq c := by
  classical
  have hexp : ∀ j : Fin d, coreNormSq (hopStep (j, true) c)
      = ∑ n ∈ c.support, (n j : ℝ) * ‖c n‖ ^ 2 + ∑ n ∈ c.support, ‖c n‖ ^ 2 := by
    intro j
    rw [coreNormSq_hopStep_raise, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun n _ => ?_
    ring
  simp only [hexp, Finset.sum_add_distrib]
  have h1 : ∑ j : Fin d, ∑ n ∈ c.support, (n j : ℝ) * ‖c n‖ ^ 2 = numberForm c := by
    rw [numberForm]
    simp only [natDeg, Nat.cast_sum, Finset.sum_mul]
    rw [Finset.sum_comm]
  have h2 : ∑ _j : Fin d, ∑ n ∈ c.support, ‖c n‖ ^ 2 = (d : ℝ) * coreNormSq c := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, coreNormSq]
  rw [h1, h2]

/-- **The oscillator identity on the core** — the one analytic input of the plan's chain that is not
bookkeeping: `∑ⱼ (‖a_j c‖² + ‖a_j† c‖²) = 2⟪c, N c⟫ + d·‖c‖²`.  With the two letter-norm
identities it is a rearrangement: each letter costs the mode's occupation, the raising letter one
particle more, and the `d` modes contribute the `d‖c‖²`. -/
theorem oscillator_identity (c : CoreCoeff d) :
    ∑ j : Fin d, (coreNormSq (hopStep (j, false) c) + coreNormSq (hopStep (j, true) c))
      = 2 * numberForm c + (d : ℝ) * coreNormSq c := by
  rw [Finset.sum_add_distrib, sum_coreNormSq_hopStep_lower, sum_coreNormSq_hopStep_raise]
  ring

/-- The letter-cost of the drift at mode `j`: `∑ₙ (nⱼ + 1)‖c n‖² = ⟪c, N c⟫ + ‖c‖²` at a single
mode, the raising part of the oscillator identity. -/
theorem coreNormSq_hopStep_raise_eq (j : Fin d) (c : CoreCoeff d) :
    coreNormSq (hopStep (j, true) c)
      = (∑ n ∈ c.support, (n j : ℝ) * ‖c n‖ ^ 2) + coreNormSq c := by
  rw [coreNormSq_hopStep_raise, coreNormSq, ← Finset.sum_add_distrib]
  exact Finset.sum_congr rfl fun n _ => by ring

/-! ## 11. The relative form bound: Cauchy–Schwarz and the `2ab` chain

§5 stated `DriftFormBound` as a target and §10 proved the oscillator identity it leans on.  This
section closes the target.  The drift `K = −∑ⱼ bⱼ ∂ⱼ` with `|bⱼ| ≤ B` satisfies

`‖⟪c, K c⟫‖ ≤ δ·⟪c, N c⟫ + (B²·d/(2δ) + B·d)·‖c‖²`

for every `δ > 0`, so it is infinitesimally form-small with respect to the number operator — the
KLMN hypothesis that makes `N + K` self-adjoint and bounded below.

* `coreNorm` — the core `ℓ²` norm `‖c‖ = √(∑ₙ ‖c n‖²)`, with `coreNorm_sq` and
  `sum_sq_subset` (the mass over any finset containing the support);
* `corePair_eq_sum` — the ambient finset in `corePair` is bookkeeping: once it contains both
  supports the sum does not depend on it.  That is what makes the pairing's algebraic laws
  provable at all;
* `corePair_smul`, `corePair_add`, `corePair_finset_sum` — the pairing is conjugate-linear in its
  second slot, hence additive over the drift's letter family;
* **`norm_corePair_le`** — Cauchy–Schwarz in the core pairing, `‖⟪c, c'⟫‖ ≤ ‖c‖·‖c'‖`, the step
  §5's note listed as the second half of the missing `ℓ²` input;
* `sum_coreNorm_hopStep_le` — Cauchy–Schwarz in the *mode* index,
  `∑ⱼ ‖a_j c‖ ≤ √d·√(⟪c, N c⟫)` and the raising twin against `⟪c, N c⟫ + d‖c‖²`, i.e. §10's
  oscillator identity read as a mode average;
* `sqrt_add_le`, `two_mul_le_add_div` — the two elementary steps of the chain, `√(x + y) ≤
  √x + √y` and `2uv ≤ δu² + v²/δ`;
* **`driftOpCoeff_form_bound`** — the estimate with the plan's constant `B²d/(2δ) + Bd`;
* **`driftFormBound_holds`** — `DriftFormBound` itself, for every `B` and every `b`: §5's target
  is no longer a target.

The chain, with `‖c‖ = coreNorm c` and `N c` the number form.  The letters contribute
`‖⟪c, a_j c⟫‖ ≤ ‖c‖·‖a_j c‖`, so

`‖⟪c, K c⟫‖ ≤ (B/√2)·‖c‖·∑ⱼ (‖a_j c‖ + ‖a_j† c‖) ≤ B·√d·‖c‖·√(2⟪c, N c⟫ + d‖c‖²)`;

then `√(x + y) ≤ √x + √y` splits the radical into `2√(⟪c, N c⟫)` and `√d·‖c‖`, and
`2uv ≤ δu² + v²/δ` spends its `δ` on the number form: the first half costs `δ·⟪c, N c⟫` plus
`B²d/(2δ)·‖c‖²`, the second half is exactly `B·d·‖c‖²` (the slack `1/√2 ≤ 1` absorbs the
normalization).  The constant is the plan's, term for term.

**Boundary.**  What is still not here is the *identification* of the coefficient family: that
`b_j = (β²σ²/2)·∂_jΦ_ε`, i.e. that the `ε`-regularized potential's gradient supplies these
`b_j` through the Hermite expansion.  That identification is where the `ε`-dependence enters —
through `B = β²σ²M_ε/2` with `M_ε = K/ε`, hence quadratically as `ε⁻²`.  The estimate itself,
which is what the KLMN argument consumes, is a theorem.
-/

theorem coreNormSq_nonneg (c : CoreCoeff d) : 0 ≤ coreNormSq c :=
  Finset.sum_nonneg fun n _ => by positivity

/-- The core `ℓ²` norm, the square root of `coreNormSq`. -/
def coreNorm (c : CoreCoeff d) : ℝ := Real.sqrt (coreNormSq c)

theorem coreNorm_nonneg (c : CoreCoeff d) : 0 ≤ coreNorm c := Real.sqrt_nonneg _

theorem coreNorm_sq (c : CoreCoeff d) : coreNorm c ^ 2 = coreNormSq c :=
  Real.sq_sqrt (coreNormSq_nonneg c)

/-- The `ℓ²` mass over any finset containing the support is the mass. -/
theorem sum_sq_subset {c : CoreCoeff d} {s : Finset (Fin d → ℕ)} (h : c.support ⊆ s) :
    ∑ n ∈ s, ‖c n‖ ^ 2 = coreNormSq c := by
  rw [coreNormSq]
  exact (Finset.sum_subset h fun x _ hx => by
    rw [Finsupp.notMem_support_iff.mp hx]; simp).symm

/-- The `ℓ²` pairing over a common finset: as long as the finset contains both supports, the
sum does not depend on it. -/
theorem corePair_eq_sum {c c' : CoreCoeff d} {s : Finset (Fin d → ℕ)}
    (hc : c.support ⊆ s) (hc' : c'.support ⊆ s) :
    corePair c c' = ∑ n ∈ s, c n * star (c' n) := by
  rw [corePair]
  exact Finset.sum_subset (fun x hx => by
    rcases Finset.mem_union.mp hx with h | h
    exacts [hc h, hc' h]) fun x _ hx => by
    rw [Finset.mem_union, not_or] at hx
    rw [Finsupp.notMem_support_iff.mp hx.1, Finsupp.notMem_support_iff.mp hx.2]
    simp

/-- **Cauchy–Schwarz in the core pairing**: `‖⟪c, c'⟫‖ ≤ ‖c‖·‖c'‖`. -/
theorem norm_corePair_le (c c' : CoreCoeff d) : ‖corePair c c'‖ ≤ coreNorm c * coreNorm c' := by
  rw [corePair]
  refine (norm_sum_le _ _).trans ?_
  simp only [norm_mul, norm_star]
  refine (Real.sum_mul_le_sqrt_mul_sqrt _ _ _).trans ?_
  rw [sum_sq_subset Finset.subset_union_left, sum_sq_subset Finset.subset_union_right]
  rfl

theorem corePair_zero_right (c : CoreCoeff d) : corePair c 0 = 0 := by
  simp [corePair]

/-- The pairing is conjugate-linear in its second slot. -/
theorem corePair_smul (c : CoreCoeff d) (r : ℂ) (c' : CoreCoeff d) :
    corePair c (r • c') = star r * corePair c c' := by
  classical
  have h1 : (r • c').support ⊆ c.support ∪ c'.support :=
    Finsupp.support_smul.trans Finset.subset_union_right
  rw [corePair_eq_sum (s := c.support ∪ c'.support) Finset.subset_union_left h1,
    corePair_eq_sum (s := c.support ∪ c'.support) Finset.subset_union_left
      Finset.subset_union_right, Finset.mul_sum]
  exact Finset.sum_congr rfl fun n _ => by
    rw [Finsupp.smul_apply, smul_eq_mul, star_mul]; ring

/-- The pairing is additive in its second slot. -/
theorem corePair_add (c x y : CoreCoeff d) : corePair c (x + y) = corePair c x + corePair c y := by
  classical
  have hc : c.support ⊆ c.support ∪ x.support ∪ y.support :=
    Finset.subset_union_left.trans Finset.subset_union_left
  have hx : x.support ⊆ c.support ∪ x.support ∪ y.support :=
    Finset.subset_union_right.trans Finset.subset_union_left
  have hy : y.support ⊆ c.support ∪ x.support ∪ y.support := Finset.subset_union_right
  have hxy : (x + y).support ⊆ c.support ∪ x.support ∪ y.support :=
    Finsupp.support_add.trans (Finset.union_subset hx hy)
  rw [corePair_eq_sum hc hxy, corePair_eq_sum hc hx, corePair_eq_sum hc hy]
  simp only [Finsupp.add_apply, star_add, mul_add]
  rw [Finset.sum_add_distrib]

/-- The pairing is additive over a finite sum in its second slot. -/
theorem corePair_finset_sum {ι : Type*} (s : Finset ι) (g : ι → CoreCoeff d) (c : CoreCoeff d) :
    corePair c (∑ j ∈ s, g j) = ∑ j ∈ s, corePair c (g j) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp [corePair]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, corePair_add, ih]

/-- `√(x + y) ≤ √x + √y`. -/
theorem sqrt_add_le {x y : ℝ} (hx : 0 ≤ x) (hy : 0 ≤ y) :
    Real.sqrt (x + y) ≤ Real.sqrt x + Real.sqrt y := by
  rw [Real.sqrt_le_iff]
  refine ⟨by positivity, ?_⟩
  nlinarith [Real.sq_sqrt hx, Real.sq_sqrt hy, Real.sqrt_nonneg x, Real.sqrt_nonneg y,
    mul_nonneg (Real.sqrt_nonneg x) (Real.sqrt_nonneg y)]

/-- The elementary `2uv ≤ δu² + v²/δ`, the form-bound's free parameter. -/
theorem two_mul_le_add_div (δ u v : ℝ) (hδ : 0 < δ) : 2 * u * v ≤ δ * u ^ 2 + v ^ 2 / δ := by
  have h : 0 ≤ (v - δ * u) ^ 2 := sq_nonneg _
  have key : 2 * u * v * δ ≤ (δ * u ^ 2 + v ^ 2 / δ) * δ := by
    field_simp
    nlinarith
  exact (mul_le_mul_iff_of_pos_right hδ).mp key

theorem invSqrtTwo_sq : invSqrtTwo ^ 2 = 1 / 2 := by
  have h2 : (Real.sqrt 2) ^ 2 = 2 := Real.sq_sqrt (by norm_num)
  rw [invSqrtTwo, div_pow, one_pow, h2]

/-- The mode sum of the letter norms, by Cauchy–Schwarz in the mode index. -/
theorem sum_coreNorm_hopStep_le (b : Bool) (c : CoreCoeff d) :
    ∑ j : Fin d, coreNorm (hopStep (j, b) c)
      ≤ Real.sqrt (d : ℝ) * Real.sqrt (if b then numberForm c + (d : ℝ) * coreNormSq c
          else numberForm c) := by
  classical
  have h := Real.sum_mul_le_sqrt_mul_sqrt (Finset.univ : Finset (Fin d))
    (fun _ : Fin d => (1 : ℝ)) (fun j : Fin d => coreNorm (hopStep (j, b) c))
  simp only [one_mul, one_pow] at h
  have hcard : ∑ _j : Fin d, (1 : ℝ) = (d : ℝ) := by simp
  have hsum : ∑ j : Fin d, coreNorm (hopStep (j, b) c) ^ 2
      = if b then numberForm c + (d : ℝ) * coreNormSq c else numberForm c := by
    cases b
    · simp only [Bool.false_eq_true, if_false, coreNorm_sq]
      exact sum_coreNormSq_hopStep_lower c
    · simp only [if_true, coreNorm_sq]
      exact sum_coreNormSq_hopStep_raise c
  rw [hcard, hsum] at h
  exact h

/-- **The `ε`-regularized relative form bound for the drift, proved.**

`K_drift = −∑ⱼ bⱼ ∂ⱼ` with `|bⱼ| ≤ B` satisfies
`‖⟪c, K_drift c⟫‖ ≤ δ·⟪c, N c⟫ + (B²d/(2δ) + Bd)·‖c‖²` for every `δ > 0`.  Since `δ` is
arbitrary, `K_drift` is infinitesimally form-small with respect to `N`.

The chain: Cauchy–Schwarz in the core pairing (`norm_corePair_le`) gives
`‖⟪c, a_j c⟫‖ ≤ ‖c‖·‖a_j c‖`; the mode sums are bounded by Cauchy–Schwarz in the mode index
(`sum_coreNorm_hopStep_le`) using the oscillator identity of §10; then `√(x+y) ≤ √x + √y` and
`2uv ≤ δu² + v²/δ`. -/
theorem driftOpCoeff_form_bound (B : ℝ) (b : Fin d → ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ j, |b j| ≤ B) (δ : ℝ) (hδ : 0 < δ) (c : CoreCoeff d) :
    ‖corePair c (driftOpCoeff b c)‖ ≤
      δ * numberForm c + (B ^ 2 * (d : ℝ) / (2 * δ) + B * (d : ℝ)) * coreNormSq c := by
  classical
  have hinv0 : (0 : ℝ) ≤ invSqrtTwo := invSqrtTwo_nonneg
  have hinv1 : invSqrtTwo ≤ 1 := invSqrtTwo_le_one
  have hX0 : 0 ≤ numberForm c := numberForm_nonneg c
  have hN0 : 0 ≤ coreNormSq c := coreNormSq_nonneg c
  have hR0 : 0 ≤ coreNorm c := coreNorm_nonneg c
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  -- the coefficients, in absolute value
  have hcoef : ∀ j : Fin d,
      ‖star (((-(b j)) * invSqrtTwo : ℝ) : ℂ)‖ = |b j| * invSqrtTwo ∧
        ‖star (((b j) * invSqrtTwo : ℝ) : ℂ)‖ = |b j| * invSqrtTwo := by
    intro j
    have h1 : ‖star (((-(b j)) * invSqrtTwo : ℝ) : ℂ)‖ = |b j| * invSqrtTwo := by
      rw [norm_star, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_neg,
        abs_of_nonneg hinv0]
    have h2 : ‖star (((b j) * invSqrtTwo : ℝ) : ℂ)‖ = |b j| * invSqrtTwo := by
      rw [norm_star, Complex.norm_real, Real.norm_eq_abs, abs_mul, abs_of_nonneg hinv0]
    exact ⟨h1, h2⟩
  -- 1. expand the drift into its letters
  have hdecomp : corePair c (driftOpCoeff b c)
      = ∑ j : Fin d,
          (star (((-(b j)) * invSqrtTwo : ℝ) : ℂ) * corePair c (hopStep (j, false) c)
            + star (((b j) * invSqrtTwo : ℝ) : ℂ) * corePair c (hopStep (j, true) c)) := by
    rw [driftOpCoeff, corePair_finset_sum]
    exact Finset.sum_congr rfl fun j _ => by rw [corePair_add, corePair_smul, corePair_smul]
  -- 2. bound the letters and their coefficients
  have hS : ‖corePair c (driftOpCoeff b c)‖
      ≤ B * invSqrtTwo * ∑ j : Fin d,
          (‖corePair c (hopStep (j, false) c)‖ + ‖corePair c (hopStep (j, true) c)‖) := by
    rw [hdecomp]
    have hterm : ∀ j : Fin d,
        ‖star (((-(b j)) * invSqrtTwo : ℝ) : ℂ) * corePair c (hopStep (j, false) c)
            + star (((b j) * invSqrtTwo : ℝ) : ℂ) * corePair c (hopStep (j, true) c)‖
          ≤ B * invSqrtTwo * (‖corePair c (hopStep (j, false) c)‖
              + ‖corePair c (hopStep (j, true) c)‖) := by
      intro j
      calc ‖star (((-(b j)) * invSqrtTwo : ℝ) : ℂ) * corePair c (hopStep (j, false) c)
              + star (((b j) * invSqrtTwo : ℝ) : ℂ) * corePair c (hopStep (j, true) c)‖
            ≤ ‖star (((-(b j)) * invSqrtTwo : ℝ) : ℂ) * corePair c (hopStep (j, false) c)‖
                + ‖star (((b j) * invSqrtTwo : ℝ) : ℂ) * corePair c (hopStep (j, true) c)‖ :=
          norm_add_le _ _
        _ = |b j| * invSqrtTwo * ‖corePair c (hopStep (j, false) c)‖
              + |b j| * invSqrtTwo * ‖corePair c (hopStep (j, true) c)‖ := by
          rw [norm_mul, norm_mul, (hcoef j).1, (hcoef j).2]
        _ = |b j| * invSqrtTwo * (‖corePair c (hopStep (j, false) c)‖
              + ‖corePair c (hopStep (j, true) c)‖) := by ring
        _ ≤ B * invSqrtTwo * (‖corePair c (hopStep (j, false) c)‖
              + ‖corePair c (hopStep (j, true) c)‖) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact mul_le_mul_of_nonneg_right (hB j) hinv0
    refine (norm_sum_le _ _).trans ?_
    refine (Finset.sum_le_sum fun j _ => hterm j).trans ?_
    rw [Finset.mul_sum]
  -- 3. the letter sum against the norm and the mode sums
  have hSle : ∑ j : Fin d,
        (‖corePair c (hopStep (j, false) c)‖ + ‖corePair c (hopStep (j, true) c)‖)
      ≤ coreNorm c * (Real.sqrt (d : ℝ) * Real.sqrt (numberForm c)
          + Real.sqrt (d : ℝ) * Real.sqrt (numberForm c + (d : ℝ) * coreNormSq c)) := by
    rw [Finset.sum_add_distrib]
    have h1 : ∑ j : Fin d, ‖corePair c (hopStep (j, false) c)‖
        ≤ coreNorm c * (Real.sqrt (d : ℝ) * Real.sqrt (numberForm c)) := by
      refine (Finset.sum_le_sum fun j _ => norm_corePair_le c _).trans ?_
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ hR0
      simpa using sum_coreNorm_hopStep_le false c
    have h2 : ∑ j : Fin d, ‖corePair c (hopStep (j, true) c)‖
        ≤ coreNorm c * (Real.sqrt (d : ℝ) * Real.sqrt (numberForm c + (d : ℝ) * coreNormSq c)) := by
      refine (Finset.sum_le_sum fun j _ => norm_corePair_le c _).trans ?_
      rw [← Finset.mul_sum]
      refine mul_le_mul_of_nonneg_left ?_ hR0
      simpa using sum_coreNorm_hopStep_le true c
    calc ∑ j : Fin d, ‖corePair c (hopStep (j, false) c)‖
            + ∑ j : Fin d, ‖corePair c (hopStep (j, true) c)‖
          ≤ coreNorm c * (Real.sqrt (d : ℝ) * Real.sqrt (numberForm c))
              + coreNorm c * (Real.sqrt (d : ℝ)
                * Real.sqrt (numberForm c + (d : ℝ) * coreNormSq c)) := add_le_add h1 h2
      _ = coreNorm c * (Real.sqrt (d : ℝ) * Real.sqrt (numberForm c)
            + Real.sqrt (d : ℝ) * Real.sqrt (numberForm c + (d : ℝ) * coreNormSq c)) := by
          ring
  -- 4. assemble the two
  have hmain : ‖corePair c (driftOpCoeff b c)‖
      ≤ B * invSqrtTwo * coreNorm c * (Real.sqrt (d : ℝ) * Real.sqrt (numberForm c)
          + Real.sqrt (d : ℝ) * Real.sqrt (numberForm c + (d : ℝ) * coreNormSq c)) := by
    refine hS.trans ?_
    refine (mul_le_mul_of_nonneg_left hSle (mul_nonneg hB0 hinv0)).trans (le_of_eq ?_)
    ring
  -- 5. the bracket: `√(x + y) ≤ √x + √y`, then `√d·√d = d`
  have hbracket : Real.sqrt (d : ℝ) * Real.sqrt (numberForm c)
        + Real.sqrt (d : ℝ) * Real.sqrt (numberForm c + (d : ℝ) * coreNormSq c)
      ≤ 2 * Real.sqrt (d : ℝ) * Real.sqrt (numberForm c) + (d : ℝ) * coreNorm c := by
    have hdN : 0 ≤ (d : ℝ) * coreNormSq c := mul_nonneg hd0 hN0
    have hs := sqrt_add_le hX0 hdN
    have hmul : Real.sqrt ((d : ℝ) * coreNormSq c) = Real.sqrt (d : ℝ) * coreNorm c := by
      rw [Real.sqrt_mul hd0]; rfl
    have hdd : Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) = (d : ℝ) :=
      Real.mul_self_sqrt hd0
    have step1 : Real.sqrt (d : ℝ) * Real.sqrt (numberForm c + (d : ℝ) * coreNormSq c)
        ≤ Real.sqrt (d : ℝ)
          * (Real.sqrt (numberForm c) + Real.sqrt ((d : ℝ) * coreNormSq c)) :=
      mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)
    rw [hmul, mul_add, ← mul_assoc, hdd] at step1
    linarith
  have hstep5 : B * invSqrtTwo * coreNorm c * (Real.sqrt (d : ℝ) * Real.sqrt (numberForm c)
        + Real.sqrt (d : ℝ) * Real.sqrt (numberForm c + (d : ℝ) * coreNormSq c))
      ≤ B * invSqrtTwo * coreNorm c
        * (2 * Real.sqrt (d : ℝ) * Real.sqrt (numberForm c) + (d : ℝ) * coreNorm c) :=
    mul_le_mul_of_nonneg_left hbracket (mul_nonneg (mul_nonneg hB0 hinv0) hR0)
  -- 6. `2uv ≤ δu² + v²/δ` and the slack `invSqrtTwo ≤ 1`
  have hxsq : Real.sqrt (numberForm c) ^ 2 = numberForm c := Real.sq_sqrt hX0
  have hdsq : Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) = (d : ℝ) := Real.mul_self_sqrt hd0
  have hv : 2 * Real.sqrt (numberForm c) * (B * invSqrtTwo * coreNorm c * Real.sqrt (d : ℝ))
      ≤ δ * numberForm c + B ^ 2 * (d : ℝ) * coreNorm c ^ 2 / (2 * δ) := by
    have ham := two_mul_le_add_div δ (Real.sqrt (numberForm c))
      (B * invSqrtTwo * coreNorm c * Real.sqrt (d : ℝ)) hδ
    have hv2 : (B * invSqrtTwo * coreNorm c * Real.sqrt (d : ℝ)) ^ 2 / δ
        = B ^ 2 * (d : ℝ) * coreNorm c ^ 2 / (2 * δ) := by
      have e : (B * invSqrtTwo * coreNorm c * Real.sqrt (d : ℝ)) ^ 2
          = B ^ 2 * invSqrtTwo ^ 2 * coreNorm c ^ 2 * (Real.sqrt (d : ℝ)) ^ 2 := by ring
      rw [e, invSqrtTwo_sq, Real.sq_sqrt hd0]
      ring
    calc 2 * Real.sqrt (numberForm c) * (B * invSqrtTwo * coreNorm c * Real.sqrt (d : ℝ))
          ≤ δ * Real.sqrt (numberForm c) ^ 2
              + (B * invSqrtTwo * coreNorm c * Real.sqrt (d : ℝ)) ^ 2 / δ := ham
      _ = δ * numberForm c + B ^ 2 * (d : ℝ) * coreNorm c ^ 2 / (2 * δ) := by
          rw [hxsq, hv2]
  have hslack : B * invSqrtTwo * (d : ℝ) * coreNorm c ^ 2 ≤ B * (d : ℝ) * coreNorm c ^ 2 := by
    have hle : B * invSqrtTwo ≤ B := by
      have := mul_le_mul_of_nonneg_left hinv1 hB0
      simpa using this
    have := mul_le_mul_of_nonneg_right hle (mul_nonneg hd0 (sq_nonneg (coreNorm c)))
    calc B * invSqrtTwo * (d : ℝ) * coreNorm c ^ 2
        = (B * invSqrtTwo) * ((d : ℝ) * coreNorm c ^ 2) := by ring
      _ ≤ B * ((d : ℝ) * coreNorm c ^ 2) := this
      _ = B * (d : ℝ) * coreNorm c ^ 2 := by ring
  -- 7. the last multiplication out
  have hfinal : B * invSqrtTwo * coreNorm c
        * (2 * Real.sqrt (d : ℝ) * Real.sqrt (numberForm c) + (d : ℝ) * coreNorm c)
      ≤ δ * numberForm c + (B ^ 2 * (d : ℝ) / (2 * δ) + B * (d : ℝ)) * coreNormSq c := by
    have e : B * invSqrtTwo * coreNorm c
          * (2 * Real.sqrt (d : ℝ) * Real.sqrt (numberForm c) + (d : ℝ) * coreNorm c)
        = 2 * Real.sqrt (numberForm c) * (B * invSqrtTwo * coreNorm c * Real.sqrt (d : ℝ))
          + B * invSqrtTwo * (d : ℝ) * coreNorm c ^ 2 := by
      ring
    rw [e, ← coreNorm_sq]
    have hsum := add_le_add hv hslack
    have harith : (δ * numberForm c + B ^ 2 * (d : ℝ) * coreNorm c ^ 2 / (2 * δ))
          + B * (d : ℝ) * coreNorm c ^ 2
        = δ * numberForm c + (B ^ 2 * (d : ℝ) / (2 * δ) + B * (d : ℝ)) * coreNorm c ^ 2 := by
      field_simp
      ring
    linarith
  linarith [hmain.trans (hstep5.trans hfinal)]

/-- **`DriftFormBound` (§5) is no longer a target** — it holds for every coefficient family and
every `B`.  The only case the bound needs beyond `driftOpCoeff_form_bound` is the degenerate
`B < 0`, which forces `d = 0`: with no modes both sides vanish. -/
theorem driftFormBound_holds (B : ℝ) (b : Fin d → ℝ) : DriftFormBound B b := by
  intro hB δ hδ c
  by_cases hB0 : 0 ≤ B
  · exact driftOpCoeff_form_bound B b hB0 hB δ hδ c
  · have hBneg : B < 0 := lt_of_not_ge hB0
    have hd0 : d = 0 := by
      rcases Nat.eq_zero_or_pos d with h | h
      · exact h
      · exfalso
        have hle := hB ⟨0, h⟩
        have h0 := abs_nonneg (b ⟨0, h⟩)
        linarith
    subst hd0
    have hdrift : driftOpCoeff b c = 0 := by simp [driftOpCoeff]
    have hnum : numberForm c = 0 := by simp [numberForm, natDeg]
    rw [hdrift, corePair_zero_right, norm_zero, hnum]
    simp

/-! ## 12. The coefficients come from the potential: `bⱼ = (β²σ²/2)·∂ⱼΦ_ε` -/

/-- The SG-pCNL drift weight `β²σ²/2` of `pcnl.md` §2.2. -/
def driftWeight (β σ : ℝ) : ℝ := β ^ 2 * σ ^ 2 / 2

/-- The plan's `B = (β²σ²/2)·M`: the constant `driftOpCoeff_form_bound` consumes, when the
gradient bound `M` comes from the potential rather than from an assumption on `b`. -/
def driftScale (β σ M : ℝ) : ℝ := driftWeight β σ * M

theorem driftWeight_nonneg (β σ : ℝ) : 0 ≤ driftWeight β σ := by
  simp only [driftWeight]; positivity

theorem driftScale_nonneg {β σ M : ℝ} (hM : 0 ≤ M) : 0 ≤ driftScale β σ M :=
  mul_nonneg (driftWeight_nonneg β σ) hM

/-- With the gradient bound `M_ε = K/ε` of the `ε`-regularized architecture, the drift's constant is
`β²σ²K/(2ε)`: the `ε` of the drift enters *only* here. -/
theorem driftScale_eps {β σ K ε : ℝ} (hε : ε ≠ 0) :
    driftScale β σ (K / ε) = β ^ 2 * σ ^ 2 * K / (2 * ε) := by
  simp only [driftScale, driftWeight]
  field_simp

/-- **The architecture's gradient bound, in the drift's own constant.**  The `ε`-regularized
normalization `Ŵ = W/(‖W‖ + ε)` has `‖dŴ‖ ≤ 2/ε`, so a potential that sees `W` only through `Ŵ`
has `‖∇Φ_ε‖ ≤ 2K/ε` (`BayesianTransformer.epsProj_fderiv_le`).  With `M_ε = 2K/ε`, §12's weight
is `B = β²σ²K/ε`: the `ε` bounds the drift's form by `ε⁻¹` and §13's lower bound by `ε⁻²`,
which is why the regularization cannot be dropped (`ε = 0` is the unbounded case). -/
theorem driftScale_eps_arch {β σ K ε : ℝ} (hε : ε ≠ 0) :
    driftScale β σ (2 * K / ε) = β ^ 2 * σ ^ 2 * K / ε := by
  simp only [driftScale, driftWeight]
  field_simp

/-- **The plan's `K_drift` for a potential**: `−Σⱼ bⱼ ∂ⱼ` with `bⱼ = (β²σ²/2)·∂ⱼ Φ`, i.e. §9.7's
`polyDrift Φ` scaled by the drift weight. -/
def driftOperator (β σ : ℝ) (Φ : MvPolynomial (Fin d) ℂ) (c : CoreCoeff d) : CoreCoeff d :=
  ((driftWeight β σ : ℝ) : ℂ) • polyDrift Φ c

theorem driftOpCoeff_smul (r : ℝ) (a : Fin d → ℝ) (c : CoreCoeff d) :
    driftOpCoeff (fun j => r * a j) c = ((r : ℝ) : ℂ) • driftOpCoeff a c := by
  simp only [driftOpCoeff, smul_add, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : (((-(r * a j)) * invSqrtTwo : ℝ) : ℂ)
      = ((r : ℝ) : ℂ) * (((-(a j)) * invSqrtTwo : ℝ) : ℂ) := by push_cast; ring
  have h2 : (((r * a j) * invSqrtTwo : ℝ) : ℂ)
      = ((r : ℝ) : ℂ) * (((a j) * invSqrtTwo : ℝ) : ℂ) := by push_cast; ring
  rw [h1, h2, smul_smul, smul_smul]

theorem driftOperator_linear (β σ : ℝ) (a : Fin d → ℝ) (c : CoreCoeff d) :
    driftOperator β σ (∑ k : Fin d, MvPolynomial.C ((a k : ℝ) : ℂ) * MvPolynomial.X k) c
      = driftOpCoeff (fun j => driftScale β σ (a j)) c := by
  rw [driftOperator, polyDrift_linear, ← driftOpCoeff_smul]
  rfl

theorem driftOperator_linear_form_bound (β σ : ℝ) {a : Fin d → ℝ} {M : ℝ}
    (hM : 0 ≤ M) (ha : ∀ j, |a j| ≤ M)
    (δ : ℝ) (hδ : 0 < δ) (c : CoreCoeff d) :
    ‖corePair c (driftOperator β σ (∑ k : Fin d, MvPolynomial.C ((a k : ℝ) : ℂ)
          * MvPolynomial.X k) c)‖
      ≤ δ * numberForm c + (driftScale β σ M ^ 2 * (d : ℝ) / (2 * δ)
          + driftScale β σ M * (d : ℝ)) * coreNormSq c := by
  rw [driftOperator_linear]
  refine driftOpCoeff_form_bound (driftScale β σ M) _ (driftScale_nonneg hM) ?_ δ hδ c
  intro j
  have h1 : |driftScale β σ (a j)| = driftWeight β σ * |a j| := by
    rw [driftScale, abs_mul, abs_of_nonneg (driftWeight_nonneg β σ)]
  rw [h1]
  exact mul_le_mul_of_nonneg_left (ha j) (driftWeight_nonneg β σ)

/-- **The end of the chain, factored out.**  If a drift's letter sum is bounded by
`(B/√2)·‖c‖·(√X + √(X + d‖c‖²))` with `X = ⟪c, N c⟫`, then the plan's constant follows:
`√(x + y) ≤ √x + √y` splits the radical, `2uv ≤ δu² + v²/δ` spends the free parameter on the
number form, and `1/√2 ≤ 1` absorbs the normalization's slack. -/
theorem form_bound_of_sqrt_sum {T : CoreCoeff d → CoreCoeff d} {B : ℝ} (hB0 : 0 ≤ B)
    (hbound : ∀ c : CoreCoeff d, ‖corePair c (T c)‖
      ≤ B * invSqrtTwo * coreNorm c * (Real.sqrt (d : ℝ) * Real.sqrt (numberForm c)
          + Real.sqrt (d : ℝ) * Real.sqrt (numberForm c + (d : ℝ) * coreNormSq c)))
    (δ : ℝ) (hδ : 0 < δ) (c : CoreCoeff d) :
    ‖corePair c (T c)‖
      ≤ δ * numberForm c + (B ^ 2 * (d : ℝ) / (2 * δ) + B * (d : ℝ)) * coreNormSq c := by
  have hinv0 : (0 : ℝ) ≤ invSqrtTwo := invSqrtTwo_nonneg
  have hinv1 : invSqrtTwo ≤ 1 := invSqrtTwo_le_one
  have hX0 : 0 ≤ numberForm c := numberForm_nonneg c
  have hN0 : 0 ≤ coreNormSq c := coreNormSq_nonneg c
  have hR0 : 0 ≤ coreNorm c := coreNorm_nonneg c
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hbracket : Real.sqrt (d : ℝ) * Real.sqrt (numberForm c)
        + Real.sqrt (d : ℝ) * Real.sqrt (numberForm c + (d : ℝ) * coreNormSq c)
      ≤ 2 * Real.sqrt (d : ℝ) * Real.sqrt (numberForm c) + (d : ℝ) * coreNorm c := by
    have hdN : 0 ≤ (d : ℝ) * coreNormSq c := mul_nonneg hd0 hN0
    have hs := sqrt_add_le hX0 hdN
    have hmul : Real.sqrt ((d : ℝ) * coreNormSq c) = Real.sqrt (d : ℝ) * coreNorm c := by
      rw [Real.sqrt_mul hd0]; rfl
    have hdd : Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) = (d : ℝ) :=
      Real.mul_self_sqrt hd0
    have step1 : Real.sqrt (d : ℝ) * Real.sqrt (numberForm c + (d : ℝ) * coreNormSq c)
        ≤ Real.sqrt (d : ℝ)
          * (Real.sqrt (numberForm c) + Real.sqrt ((d : ℝ) * coreNormSq c)) :=
      mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)
    rw [hmul, mul_add, ← mul_assoc, hdd] at step1
    linarith
  have hstep5 : B * invSqrtTwo * coreNorm c * (Real.sqrt (d : ℝ) * Real.sqrt (numberForm c)
        + Real.sqrt (d : ℝ) * Real.sqrt (numberForm c + (d : ℝ) * coreNormSq c))
      ≤ B * invSqrtTwo * coreNorm c
        * (2 * Real.sqrt (d : ℝ) * Real.sqrt (numberForm c) + (d : ℝ) * coreNorm c) :=
    mul_le_mul_of_nonneg_left hbracket (mul_nonneg (mul_nonneg hB0 hinv0) hR0)
  have hxsq : Real.sqrt (numberForm c) ^ 2 = numberForm c := Real.sq_sqrt hX0
  have hv : 2 * Real.sqrt (numberForm c) * (B * invSqrtTwo * coreNorm c * Real.sqrt (d : ℝ))
      ≤ δ * numberForm c + B ^ 2 * (d : ℝ) * coreNorm c ^ 2 / (2 * δ) := by
    have ham := two_mul_le_add_div δ (Real.sqrt (numberForm c))
      (B * invSqrtTwo * coreNorm c * Real.sqrt (d : ℝ)) hδ
    have hv2 : (B * invSqrtTwo * coreNorm c * Real.sqrt (d : ℝ)) ^ 2 / δ
        = B ^ 2 * (d : ℝ) * coreNorm c ^ 2 / (2 * δ) := by
      have e : (B * invSqrtTwo * coreNorm c * Real.sqrt (d : ℝ)) ^ 2
          = B ^ 2 * invSqrtTwo ^ 2 * coreNorm c ^ 2 * (Real.sqrt (d : ℝ)) ^ 2 := by ring
      rw [e, invSqrtTwo_sq, Real.sq_sqrt hd0]
      ring
    calc 2 * Real.sqrt (numberForm c) * (B * invSqrtTwo * coreNorm c * Real.sqrt (d : ℝ))
          ≤ δ * Real.sqrt (numberForm c) ^ 2
              + (B * invSqrtTwo * coreNorm c * Real.sqrt (d : ℝ)) ^ 2 / δ := ham
      _ = δ * numberForm c + B ^ 2 * (d : ℝ) * coreNorm c ^ 2 / (2 * δ) := by
          rw [hxsq, hv2]
  have hslack : B * invSqrtTwo * (d : ℝ) * coreNorm c ^ 2 ≤ B * (d : ℝ) * coreNorm c ^ 2 := by
    have hle : B * invSqrtTwo ≤ B := by
      have := mul_le_mul_of_nonneg_left hinv1 hB0
      simpa using this
    have := mul_le_mul_of_nonneg_right hle (mul_nonneg hd0 (sq_nonneg (coreNorm c)))
    calc B * invSqrtTwo * (d : ℝ) * coreNorm c ^ 2
        = (B * invSqrtTwo) * ((d : ℝ) * coreNorm c ^ 2) := by ring
      _ ≤ B * ((d : ℝ) * coreNorm c ^ 2) := this
      _ = B * (d : ℝ) * coreNorm c ^ 2 := by ring
  have hfinal : B * invSqrtTwo * coreNorm c
        * (2 * Real.sqrt (d : ℝ) * Real.sqrt (numberForm c) + (d : ℝ) * coreNorm c)
      ≤ δ * numberForm c + (B ^ 2 * (d : ℝ) / (2 * δ) + B * (d : ℝ)) * coreNormSq c := by
    have e : B * invSqrtTwo * coreNorm c
          * (2 * Real.sqrt (d : ℝ) * Real.sqrt (numberForm c) + (d : ℝ) * coreNorm c)
        = 2 * Real.sqrt (numberForm c) * (B * invSqrtTwo * coreNorm c * Real.sqrt (d : ℝ))
          + B * invSqrtTwo * (d : ℝ) * coreNorm c ^ 2 := by ring
    rw [e, ← coreNorm_sq]
    have hsum := add_le_add hv hslack
    have harith : (δ * numberForm c + B ^ 2 * (d : ℝ) * coreNorm c ^ 2 / (2 * δ))
          + B * (d : ℝ) * coreNorm c ^ 2
        = δ * numberForm c + (B ^ 2 * (d : ℝ) / (2 * δ) + B * (d : ℝ)) * coreNorm c ^ 2 := by
      field_simp
      ring
    linarith
  exact (hbound c).trans (hstep5.trans hfinal)

/-- The pairing of a negated state is the negated pairing. -/
theorem corePair_neg (c x : CoreCoeff d) : corePair c (-x) = -corePair c x := by
  have h := corePair_smul c (-1) x
  simpa using h

/-- The pairing is additive for differences. -/
theorem corePair_sub (c x y : CoreCoeff d) : corePair c (x - y) = corePair c x - corePair c y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, corePair_add, corePair_neg]

/-- Multiplication by a polynomial is additive for differences. -/
theorem polyMul_sub (Φ : MvPolynomial (Fin d) ℂ) (x y : CoreCoeff d) :
    polyMul Φ (x - y) = polyMul Φ x - polyMul Φ y := by
  rw [sub_eq_add_neg, sub_eq_add_neg, polyMul_add_arg]
  congr 1
  have := polyMul_smul_arg Φ (-1) y
  simpa using this

/-- One derivative letter, bounded: `‖⟪c, Ψⱼ ∂ⱼ c⟫‖ ≤ (1/√2)·M·‖c‖·(‖aⱼc‖ + ‖aⱼ†c‖)`. -/
theorem corePair_polyMul_diffHermite_le {Ψ : Fin d → MvPolynomial (Fin d) ℂ} {M : ℝ}
    (hgrad : ∀ j : Fin d, ∀ c : CoreCoeff d, coreNorm (polyMul (Ψ j) c) ≤ M * coreNorm c)
    (c : CoreCoeff d) (j : Fin d) :
    ‖corePair c (polyMul (Ψ j) (diffHermite j c))‖
      ≤ invSqrtTwo * (M * coreNorm c)
        * (coreNorm (hopStep (j, false) c) + coreNorm (hopStep (j, true) c)) := by
  have hinv0 : (0 : ℝ) ≤ invSqrtTwo := invSqrtTwo_nonneg
  have hmain : ‖corePair c (polyMul (Ψ j) (hopStep (j, false) c - hopStep (j, true) c))‖
      ≤ M * coreNorm c
        * (coreNorm (hopStep (j, false) c) + coreNorm (hopStep (j, true) c)) := by
    rw [polyMul_sub, corePair_sub]
    calc ‖corePair c (polyMul (Ψ j) (hopStep (j, false) c))
            - corePair c (polyMul (Ψ j) (hopStep (j, true) c))‖
          ≤ ‖corePair c (polyMul (Ψ j) (hopStep (j, false) c))‖
            + ‖corePair c (polyMul (Ψ j) (hopStep (j, true) c))‖ := norm_sub_le _ _
      _ ≤ coreNorm c * (M * coreNorm (hopStep (j, false) c))
            + coreNorm c * (M * coreNorm (hopStep (j, true) c)) := by
          refine add_le_add ?_ ?_
          · exact (norm_corePair_le c _).trans
              (mul_le_mul_of_nonneg_left (hgrad j _) (coreNorm_nonneg c))
          · exact (norm_corePair_le c _).trans
              (mul_le_mul_of_nonneg_left (hgrad j _) (coreNorm_nonneg c))
      _ = M * coreNorm c
            * (coreNorm (hopStep (j, false) c) + coreNorm (hopStep (j, true) c)) := by ring
  have hsplit : diffHermite j c
      = ((invSqrtTwo : ℝ) : ℂ) • (hopStep (j, false) c - hopStep (j, true) c) := rfl
  have hstar : star ((invSqrtTwo : ℝ) : ℂ) = ((invSqrtTwo : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  rw [hsplit, polyMul_smul_arg, corePair_smul, hstar, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hinv0]
  calc invSqrtTwo
        * ‖corePair c (polyMul (Ψ j) (hopStep (j, false) c - hopStep (j, true) c))‖
      ≤ invSqrtTwo * (M * coreNorm c
          * (coreNorm (hopStep (j, false) c) + coreNorm (hopStep (j, true) c))) :=
        mul_le_mul_of_nonneg_left hmain hinv0
    _ = invSqrtTwo * (M * coreNorm c)
          * (coreNorm (hopStep (j, false) c) + coreNorm (hopStep (j, true) c)) := by ring

/-- **The form bound of a family of derivative letters**: the `ℓ²` step of
`−Σⱼ polyMul (Ψⱼ) ∘ ∂ⱼ` when each `Ψⱼ` is bounded by `M` as a multiplication operator.  Stated for
a family rather than for `pderiv j Φ` so the proof's terms stay small; the potential's case is
`polyDrift_form_bound` below. -/
theorem form_bound_of_letter_family {Ψ : Fin d → MvPolynomial (Fin d) ℂ} {M : ℝ} (hM0 : 0 ≤ M)
    (hgrad : ∀ j : Fin d, ∀ c : CoreCoeff d, coreNorm (polyMul (Ψ j) c) ≤ M * coreNorm c)
    (δ : ℝ) (hδ : 0 < δ) (c : CoreCoeff d) :
    ‖corePair c (∑ j : Fin d, polyMul (Ψ j) (diffHermite j c))‖
      ≤ δ * numberForm c + (M ^ 2 * (d : ℝ) / (2 * δ) + M * (d : ℝ)) * coreNormSq c := by
  classical
  have hbound : ∀ c : CoreCoeff d,
      ‖corePair c (∑ j : Fin d, polyMul (Ψ j) (diffHermite j c))‖
      ≤ M * invSqrtTwo * coreNorm c * (Real.sqrt (d : ℝ) * Real.sqrt (numberForm c)
          + Real.sqrt (d : ℝ) * Real.sqrt (numberForm c + (d : ℝ) * coreNormSq c)) := by
    intro c
    have hletter : ∀ j : Fin d, ‖corePair c (polyMul (Ψ j) (diffHermite j c))‖
        ≤ invSqrtTwo * (M * coreNorm c)
          * (coreNorm (hopStep (j, false) c) + coreNorm (hopStep (j, true) c)) :=
      fun j => corePair_polyMul_diffHermite_le hgrad c j
    have hstep : ‖corePair c (∑ j : Fin d, polyMul (Ψ j) (diffHermite j c))‖
        ≤ ∑ j : Fin d, ‖corePair c (polyMul (Ψ j) (diffHermite j c))‖ := by
      rw [corePair_finset_sum]
      exact norm_sum_le _ _
    have hsum1 : ∑ j : Fin d, ‖corePair c (polyMul (Ψ j) (diffHermite j c))‖
        ≤ invSqrtTwo * (M * coreNorm c)
            * (∑ j : Fin d, coreNorm (hopStep (j, false) c)
              + ∑ j : Fin d, coreNorm (hopStep (j, true) c)) := by
      refine (Finset.sum_le_sum fun j _ => hletter j).trans (le_of_eq ?_)
      rw [← Finset.mul_sum, Finset.sum_add_distrib]
    have hsum2 : ∑ j : Fin d, coreNorm (hopStep (j, false) c)
          + ∑ j : Fin d, coreNorm (hopStep (j, true) c)
        ≤ Real.sqrt (d : ℝ) * Real.sqrt (numberForm c)
          + Real.sqrt (d : ℝ) * Real.sqrt (numberForm c + (d : ℝ) * coreNormSq c) :=
      add_le_add (sum_coreNorm_hopStep_le false c) (sum_coreNorm_hopStep_le true c)
    refine hstep.trans (hsum1.trans ?_)
    have hshape : invSqrtTwo * (M * coreNorm c)
          * (∑ j : Fin d, coreNorm (hopStep (j, false) c)
            + ∑ j : Fin d, coreNorm (hopStep (j, true) c))
        = M * invSqrtTwo * coreNorm c
          * (∑ j : Fin d, coreNorm (hopStep (j, false) c)
            + ∑ j : Fin d, coreNorm (hopStep (j, true) c)) := by ring
    rw [hshape]
    exact mul_le_mul_of_nonneg_left hsum2
      (mul_nonneg (mul_nonneg hM0 invSqrtTwo_nonneg) (coreNorm_nonneg c))
  exact form_bound_of_sqrt_sum hM0 hbound δ hδ c

/-- **The form bound of a potential's drift.**  If the gradient `∂ⱼ Φ` is bounded by `M` as a
multiplication operator on the core, then `polyDrift Φ` is dominated by the number form with the
plan's constant — the `ℓ²` step for a potential that is *not* linear, with the gradient bound
entering only through `M`. -/
theorem polyDrift_form_bound {Φ : MvPolynomial (Fin d) ℂ} {M : ℝ} (hM0 : 0 ≤ M)
    (hgrad : ∀ j : Fin d, ∀ c : CoreCoeff d,
      coreNorm (polyMul (MvPolynomial.pderiv j Φ) c) ≤ M * coreNorm c)
    (δ : ℝ) (hδ : 0 < δ) (c : CoreCoeff d) :
    ‖corePair c (polyDrift Φ c)‖
      ≤ δ * numberForm c + (M ^ 2 * (d : ℝ) / (2 * δ) + M * (d : ℝ)) * coreNormSq c := by
  have hmain := form_bound_of_letter_family (Ψ := fun j => MvPolynomial.pderiv j Φ) hM0
    (fun j c => hgrad j c) δ hδ c
  have hnorm : ‖corePair c (polyDrift Φ c)‖
      = ‖corePair c (∑ j : Fin d, polyMul (MvPolynomial.pderiv j Φ) (diffHermite j c))‖ := by
    rw [polyDrift, corePair_neg, norm_neg]
  rw [hnorm]
  exact hmain

/-- **The plan's drift for a potential, with the plan's constant.**  `K_drift = −Σⱼ bⱼ ∂ⱼ` with
`bⱼ = (β²σ²/2)·∂ⱼ Φ` is `driftOperator β σ Φ`, and its form bound has `B = (β²σ²/2)·M` — the
`ε`-dependence of `M_ε = K/ε` is the only place `ε` enters. -/
theorem driftOperator_form_bound (β σ : ℝ) {Φ : MvPolynomial (Fin d) ℂ} {M : ℝ} (hM0 : 0 ≤ M)
    (hgrad : ∀ j : Fin d, ∀ c : CoreCoeff d,
      coreNorm (polyMul (MvPolynomial.pderiv j Φ) c) ≤ M * coreNorm c)
    (δ : ℝ) (hδ : 0 < δ) (c : CoreCoeff d) :
    ‖corePair c (driftOperator β σ Φ c)‖
      ≤ δ * numberForm c + (driftScale β σ M ^ 2 * (d : ℝ) / (2 * δ)
          + driftScale β σ M * (d : ℝ)) * coreNormSq c := by
  classical
  have hw0 : 0 ≤ driftWeight β σ := driftWeight_nonneg β σ
  have hnorm : ‖corePair c (driftOperator β σ Φ c)‖
      = driftWeight β σ * ‖corePair c (polyDrift Φ c)‖ := by
    rw [driftOperator, corePair_smul]
    have hstar : star ((driftWeight β σ : ℝ) : ℂ) = ((driftWeight β σ : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal]
    rw [hstar, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
  rcases lt_or_eq_of_le hw0 with hwpos | hwzero
  · have hδw : 0 < δ / driftWeight β σ := div_pos hδ hwpos
    have hbound := polyDrift_form_bound hM0 hgrad (δ / driftWeight β σ) hδw c
    rw [hnorm]
    refine (mul_le_mul_of_nonneg_left hbound (le_of_lt hwpos)).trans (le_of_eq ?_)
    show driftWeight β σ * (δ / driftWeight β σ * numberForm c
          + (M ^ 2 * (d : ℝ) / (2 * (δ / driftWeight β σ)) + M * (d : ℝ)) * coreNormSq c)
        = δ * numberForm c + (driftScale β σ M ^ 2 * (d : ℝ) / (2 * δ)
            + driftScale β σ M * (d : ℝ)) * coreNormSq c
    rw [show driftScale β σ M = driftWeight β σ * M from rfl]
    field_simp
  · have hdrift : driftOperator β σ Φ c = 0 := by
      rw [driftOperator, ← hwzero]
      simp
    have hB0 : driftScale β σ M = 0 := by
      rw [driftScale, ← hwzero, zero_mul]
    rw [hdrift, corePair_zero_right, norm_zero, hB0]
    have hzero : (0 : ℝ) ^ 2 * (d : ℝ) / (2 * δ) + 0 * (d : ℝ) = 0 := by ring
    rw [hzero, zero_mul, add_zero]
    exact mul_nonneg (le_of_lt hδ) (numberForm_nonneg c)

/-- **The `ε`-dependence is exactly quadratic.**  With the gradient bound `M_ε = K/ε` of the
`ε`-regularized architecture, the drift's constant is `(β²σ²M_ε)²·d/(8δ) + (β²σ²M_ε)·d/2` — the
formula `pcnl.md` displays, with the `ε` in it. -/
theorem driftOperator_form_bound_eps (β σ : ℝ) {Φ : MvPolynomial (Fin d) ℂ} {K ε : ℝ}
    (hK : 0 ≤ K) (hε : 0 < ε)
    (hgrad : ∀ j : Fin d, ∀ c : CoreCoeff d,
      coreNorm (polyMul (MvPolynomial.pderiv j Φ) c) ≤ (K / ε) * coreNorm c)
    (δ : ℝ) (hδ : 0 < δ) (c : CoreCoeff d) :
    ‖corePair c (driftOperator β σ Φ c)‖
      ≤ δ * numberForm c
        + ((β ^ 2 * σ ^ 2 * K) ^ 2 / (8 * δ * ε ^ 2) + β ^ 2 * σ ^ 2 * K / (2 * ε))
          * (d : ℝ) * coreNormSq c := by
  have hM0 : 0 ≤ K / ε := div_nonneg hK (le_of_lt hε)
  have hεne : ε ≠ 0 := ne_of_gt hε
  have hδne : δ ≠ 0 := ne_of_gt hδ
  refine (driftOperator_form_bound β σ (Φ := Φ) hM0 hgrad δ hδ c).trans (le_of_eq ?_)
  rw [driftScale_eps hεne]
  field_simp
  ring


/-! ## 13. Semiboundedness: `N + K_drift` is bounded below -/

/-- The number operator is diagonal, with eigenvalue the occupation degree. -/
theorem numberOp_apply (c : CoreCoeff d) (m : Fin d → ℕ) : numberOp c m = (natDeg m : ℂ) * c m := by
  classical
  rw [numberOp, Finsupp.sum_apply]
  rw [Finsupp.sum]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  by_cases hm : m ∈ c.support
  · simp [hm]
  · rw [if_neg hm, Finsupp.notMem_support_iff.mp hm, mul_zero]

/-- **The number operator's pairing is the number form**: `⟪c, N c⟫ = ∑ₙ (∑ᵢ nᵢ)‖c n‖²`. -/
theorem corePair_numberOp_re (c : CoreCoeff d) : (corePair c (numberOp c)).re = numberForm c := by
  classical
  have hsub : (numberOp c).support ⊆ c.support := fun m hm => mem_support_numberOp hm
  rw [corePair_eq_sum (c' := numberOp c) Finset.Subset.rfl hsub, Complex.re_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [numberOp_apply]
  have hz : c n * star (c n) = ((‖c n‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hst : star ((natDeg n : ℂ)) = ((natDeg n : ℝ) : ℂ) := by
    rw [show ((natDeg n : ℂ)) = ((natDeg n : ℝ) : ℂ) by push_cast; ring, Complex.star_def,
      Complex.conj_ofReal]
  have h : c n * star ((natDeg n : ℂ) * c n) = (((natDeg n : ℝ) * ‖c n‖ ^ 2 : ℝ) : ℂ) := by
    rw [star_mul, hst, ← mul_assoc, hz, ← Complex.ofReal_mul]
    congr 1
    ring
  rw [h, Complex.ofReal_re]

/-- **Semiboundedness from a relative form bound.**  If a drift's form is dominated by
`δ·⟪c, N c⟫ + C‖c‖²` with `δ ≤ 1`, then the quadratic form of `N + K` is bounded below by `−C‖c‖²`
— the KLMN conclusion, taken before any completion. -/
theorem semibounded_of_form_bound {K : CoreCoeff d → CoreCoeff d} {δ C : ℝ} (hδ1 : δ ≤ 1)
    (h : ∀ c : CoreCoeff d, ‖corePair c (K c)‖ ≤ δ * numberForm c + C * coreNormSq c)
    (c : CoreCoeff d) :
    -C * coreNormSq c ≤ (corePair c (numberOp c + K c)).re := by
  rw [corePair_add, Complex.add_re, corePair_numberOp_re]
  have hre : -(‖corePair c (K c)‖) ≤ (corePair c (K c)).re := by
    have := Complex.abs_re_le_norm (corePair c (K c))
    have := neg_abs_le (corePair c (K c)).re
    linarith
  have hbound : -(δ * numberForm c + C * coreNormSq c) ≤ -(‖corePair c (K c)‖) := by
    have := h c
    linarith
  have hnonneg : 0 ≤ (1 - δ) * numberForm c := by
    have := numberForm_nonneg c
    nlinarith
  linarith

/-- **`N + K_drift` is bounded below**, with the plan's constant: for `|bⱼ| ≤ B` and every
`δ ∈ (0, 1]`, the quadratic form of `numberOp + driftOpCoeff b` is at least
`−(B²d/(2δ) + Bd)·‖c‖²`. -/
theorem numberOp_add_driftOpCoeff_semibounded (b : Fin d → ℝ) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ j, |b j| ≤ B) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (c : CoreCoeff d) :
    -(B ^ 2 * (d : ℝ) / (2 * δ) + B * (d : ℝ)) * coreNormSq c
      ≤ (corePair c (numberOp c + driftOpCoeff b c)).re :=
  semibounded_of_form_bound hδ1 (fun c => driftOpCoeff_form_bound B b hB0 hB δ hδ c) c

/-- **The plan's drift is semibounded, with the `ε` in the constant**: for the gradient bound
`M_ε = K/ε`, the form of `numberOp + driftOperator β σ Φ_ε` is bounded below by
`−((β²σ²M_ε)²d/(8δ) + β²σ²M_ε·d/2)·‖c‖²`, hence by a constant of order `ε⁻²`. -/
theorem pcnlDrift_semibounded_eps (β σ : ℝ) {Φ : MvPolynomial (Fin d) ℂ} {K ε : ℝ}
    (hK : 0 ≤ K) (hε : 0 < ε)
    (hgrad : ∀ j : Fin d, ∀ c : CoreCoeff d,
      coreNorm (polyMul (MvPolynomial.pderiv j Φ) c) ≤ (K / ε) * coreNorm c)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (c : CoreCoeff d) :
    -(((β ^ 2 * σ ^ 2 * K) ^ 2 / (8 * δ * ε ^ 2) + β ^ 2 * σ ^ 2 * K / (2 * ε))
        * (d : ℝ)) * coreNormSq c
      ≤ (corePair c (numberOp c + driftOperator β σ Φ c)).re :=
  semibounded_of_form_bound hδ1
    (fun c => driftOperator_form_bound_eps β σ (Φ := Φ) hK hε hgrad δ hδ c) c
/-! ## 14. The gradient bound is a sector statement, not a global one

§12–§13 carried the gradient bound `M` of a potential into the drift's constant and into its lower
bound.  That `M` was a hypothesis (`hgrad`): "multiplication by `∂ⱼΦ` is bounded by `M` on the
core".  This section says what that hypothesis can and cannot be.

* **It cannot hold globally.**  Multiplication by `xⱼ` raises the occupation, and on the basis
  vector `eₙ` the image already has norm `√(nⱼ + 1)/√2` (`polyMul_X_unbounded` chooses, for every
  `M`, a state whose image exceeds `M‖c‖`).  A non-constant potential is therefore not a bounded
  multiplier, so §12's `hgrad` is unattainable as stated — the level is part of the statement, not
  an artefact of the proof.
* **It holds on every sector, with an explicit constant.**  On `{N ≤ N₀}` a degree-`K` polynomial
  acts through `≤ 2^k` ladder words of length `≤ K`, and each letter costs at most `√(N₀ + K + 1)`
  by §10's letter norms: `polyMul_norm_sector_le` gives `‖polyMul Φ c‖ ≤ polyMulSectorBound Φ M·‖c‖`
  for `M ≥ N₀ + deg Φ`, and `pderiv_norm_sector_le` reads it for `∂ⱼΦ` at the level `N₀ + 1` the
  drift actually reaches.  `gradSectorBound Φ N` is the resulting constant.
* **The estimate and the lower bound then need no hypothesis.**  `polyDrift_form_bound_sector`,
  `driftOperator_form_bound_sector` and `pcnlDrift_semibounded_sector` restate §11–§13 with
  `M := gradSectorBound Φ N`; the only input is that the state lies in the sector, which is exactly
  the truncation a finite-band computation works on.

The chain is the `ℓ²` mirror of §9.9's `ℓ¹` estimate: `coreNorm_add_le` (Cauchy–Schwarz in the core
pairing) for the triangle inequality, §10's letter norms on the sector for the powers, and the
sector band `hopStep_band`/`mulHermite_band` to know which sector the intermediate states reach.
-/

/-! ### 14.1 The norm calculus of the core -/

theorem coreNorm_zero : coreNorm (0 : CoreCoeff d) = 0 := by
  simp [coreNorm, coreNormSq]

theorem coreNormSq_neg (c : CoreCoeff d) : coreNormSq (-c) = coreNormSq c := by
  rw [coreNormSq, coreNormSq, Finsupp.support_neg]
  exact Finset.sum_congr rfl fun n _ => by rw [Finsupp.neg_apply, norm_neg]

theorem coreNorm_neg (c : CoreCoeff d) : coreNorm (-c) = coreNorm c := by
  simp only [coreNorm, coreNormSq_neg]

theorem coreNormSq_smul (r : ℂ) (c : CoreCoeff d) :
    coreNormSq (r • c) = ‖r‖ ^ 2 * coreNormSq c := by
  classical
  rw [← sum_sq_subset (c := r • c) Finsupp.support_smul, coreNormSq, Finset.mul_sum]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [Finsupp.smul_apply, smul_eq_mul, norm_mul, mul_pow]

theorem coreNorm_smul (r : ℂ) (c : CoreCoeff d) : coreNorm (r • c) = ‖r‖ * coreNorm c := by
  rw [coreNorm, coreNormSq_smul, Real.sqrt_mul (by positivity), coreNorm,
    Real.sqrt_sq (norm_nonneg r)]

theorem coreNormSq_add_le_sq (x y : CoreCoeff d) :
    coreNormSq (x + y) ≤ (coreNorm x + coreNorm y) ^ 2 := by
  classical
  set s := x.support ∪ y.support with hs
  have hx : x.support ⊆ s := Finset.subset_union_left
  have hy : y.support ⊆ s := Finset.subset_union_right
  have h1 : coreNormSq (x + y) ≤ ∑ n ∈ s, (‖x n‖ + ‖y n‖) ^ 2 := by
    refine (Finset.sum_le_sum_of_subset_of_nonneg Finsupp.support_add
      (fun _ _ _ => by positivity)).trans ?_
    refine Finset.sum_le_sum fun n _ => ?_
    have hval : ‖(x + y) n‖ = ‖x n + y n‖ := by rw [Finsupp.add_apply]
    rw [hval]
    nlinarith [norm_nonneg (x n + y n), norm_nonneg (x n), norm_nonneg (y n),
      norm_add_le (x n) (y n)]
  have h2 : ∑ n ∈ s, (‖x n‖ + ‖y n‖) ^ 2
      = coreNormSq x + 2 * (∑ n ∈ s, ‖x n‖ * ‖y n‖) + coreNormSq y := by
    have hstep : ∀ n ∈ s, (‖x n‖ + ‖y n‖) ^ 2
        = ‖x n‖ ^ 2 + 2 * (‖x n‖ * ‖y n‖) + ‖y n‖ ^ 2 := fun n _ => by ring
    rw [Finset.sum_congr rfl hstep, Finset.sum_add_distrib, Finset.sum_add_distrib,
      ← Finset.mul_sum, sum_sq_subset hx, sum_sq_subset hy]
  have h3 : ∑ n ∈ s, ‖x n‖ * ‖y n‖ ≤ coreNorm x * coreNorm y := by
    have hcs := Real.sum_mul_le_sqrt_mul_sqrt s (fun n => ‖x n‖) (fun n => ‖y n‖)
    rw [sum_sq_subset hx, sum_sq_subset hy] at hcs
    simpa [coreNorm] using hcs
  rw [h2] at h1
  rw [← coreNorm_sq x, ← coreNorm_sq y] at h1
  nlinarith [coreNorm_nonneg x, coreNorm_nonneg y]

/-- **The triangle inequality in the core `ℓ²` norm**, `‖x + y‖ ≤ ‖x‖ + ‖y‖`, from
Cauchy–Schwarz in the pairing.  It is what turns the `2^k` word family into one estimate. -/
theorem coreNorm_add_le (x y : CoreCoeff d) : coreNorm (x + y) ≤ coreNorm x + coreNorm y := by
  have h := coreNormSq_add_le_sq x y
  have hnn : 0 ≤ coreNorm x + coreNorm y := add_nonneg (coreNorm_nonneg x) (coreNorm_nonneg y)
  calc coreNorm (x + y) = Real.sqrt (coreNormSq (x + y)) := rfl
    _ ≤ Real.sqrt ((coreNorm x + coreNorm y) ^ 2) := Real.sqrt_le_sqrt h
    _ = coreNorm x + coreNorm y := Real.sqrt_sq hnn

theorem coreNorm_finset_sum_le {ι : Type*} (s : Finset ι) (g : ι → CoreCoeff d) :
    coreNorm (∑ i ∈ s, g i) ≤ ∑ i ∈ s, coreNorm (g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [coreNorm_zero]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (coreNorm_add_le _ _).trans (add_le_add le_rfl ih)

/-! ### 14.2 The letters and the multiplication law on a sector -/

/-- **One letter costs `√(N + 1)` in `ℓ²` on the sector**: §10's letter norms with `nⱼ ≤ N`. -/
theorem coreNormSq_hopStep_sector_le (p : Fin d × Bool) {N : ℕ} (c : CoreCoeff d)
    (hc : ∀ n ∈ c.support, natDeg n ≤ N) :
    coreNormSq (hopStep p c) ≤ ((N : ℝ) + 1) * coreNormSq c := by
  classical
  obtain ⟨j, b⟩ := p
  have hcoord : ∀ n ∈ c.support, (n j : ℝ) + 1 ≤ (N : ℝ) + 1 := by
    intro n hn
    have hle : n j ≤ N :=
      le_trans (Finset.single_le_sum (f := n) (fun i _ => Nat.zero_le _) (Finset.mem_univ j))
        (hc n hn)
    have hR : (n j : ℝ) ≤ (N : ℝ) := by exact_mod_cast hle
    linarith
  cases b with
  | true =>
    rw [coreNormSq_hopStep_raise]
    refine (Finset.sum_le_sum fun n hn =>
      mul_le_mul_of_nonneg_right (hcoord n hn) (by positivity)).trans (le_of_eq ?_)
    rw [← Finset.mul_sum, coreNormSq]
  | false =>
    rw [coreNormSq_hopStep_lower]
    calc ∑ n ∈ c.support, (n j : ℝ) * ‖c n‖ ^ 2
        ≤ ∑ n ∈ c.support, ((N : ℝ) + 1) * ‖c n‖ ^ 2 := by
          refine Finset.sum_le_sum fun n hn => ?_
          exact mul_le_mul_of_nonneg_right (by linarith [hcoord n hn]) (by positivity)
      _ = ((N : ℝ) + 1) * coreNormSq c := by rw [← Finset.mul_sum, coreNormSq]

/-- The square-root form of `coreNormSq_hopStep_sector_le`. -/
theorem coreNorm_hopStep_sector_le (p : Fin d × Bool) {N : ℕ} (c : CoreCoeff d)
    (hc : ∀ n ∈ c.support, natDeg n ≤ N) :
    coreNorm (hopStep p c) ≤ Real.sqrt ((N : ℝ) + 1) * coreNorm c := by
  have h := coreNormSq_hopStep_sector_le p c hc
  calc coreNorm (hopStep p c) = Real.sqrt (coreNormSq (hopStep p c)) := rfl
    _ ≤ Real.sqrt (((N : ℝ) + 1) * coreNormSq c) := Real.sqrt_le_sqrt h
    _ = Real.sqrt ((N : ℝ) + 1) * coreNorm c := by
        rw [Real.sqrt_mul (by positivity)]
        rfl

/-- **The multiplication law `xⱼ` costs `2√(N + 1)` on the sector**: it is the sum of its two
ladder letters, with the Hermite normalization `1/√2 ≤ 1` dropped. -/
theorem coreNorm_mulHermite_sector_le (j : Fin d) {N : ℕ} (c : CoreCoeff d)
    (hc : ∀ n ∈ c.support, natDeg n ≤ N) :
    coreNorm (mulHermite j c) ≤ 2 * Real.sqrt ((N : ℝ) + 1) * coreNorm c := by
  have h1 := coreNorm_hopStep_sector_le (j, true) c hc
  have h2 := coreNorm_hopStep_sector_le (j, false) c hc
  have hsum : coreNorm (hopStep (j, true) c + hopStep (j, false) c)
      ≤ 2 * Real.sqrt ((N : ℝ) + 1) * coreNorm c := by
    have := coreNorm_add_le (hopStep (j, true) c) (hopStep (j, false) c)
    linarith
  have hnorm : coreNorm (mulHermite j c)
      = invSqrtTwo * coreNorm (hopStep (j, true) c + hopStep (j, false) c) := by
    rw [mulHermite, coreNorm_smul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg invSqrtTwo_nonneg]
  rw [hnorm]
  refine (mul_le_mul invSqrtTwo_le_one hsum (coreNorm_nonneg _) (by norm_num)).trans (le_of_eq ?_)
  ring

/-- **A word of `k` multiplication laws costs `(2√(M + 1))^k`** on `{N ≤ N}`, where `M ≥ N + k`
bounds the degrees the word meets (`mulHermite_band`). -/
theorem coreNorm_mulHermiteList_sector_le (js : List (Fin d)) :
    ∀ (c : CoreCoeff d) (N M : ℕ), N + js.length ≤ M →
      (∀ n ∈ c.support, natDeg n ≤ N) →
      coreNorm (mulHermiteList js c)
        ≤ (2 * Real.sqrt ((M : ℝ) + 1)) ^ js.length * coreNorm c := by
  induction js with
  | nil =>
    intro c N M _ _
    simp
  | cons j js ih =>
    intro c N M hM hc
    rw [mulHermiteList_cons, List.length_cons]
    have hNM : N + 1 + js.length ≤ M := by
      rw [List.length_cons] at hM
      omega
    have hband : ∀ n ∈ (mulHermite j c).support, natDeg n ≤ N + 1 :=
      fun n hn => mulHermite_band hc hn
    refine (ih (mulHermite j c) (N + 1) M hNM hband).trans ?_
    have hstep := coreNorm_mulHermite_sector_le j c hc
    have hroot : Real.sqrt ((N : ℝ) + 1) ≤ Real.sqrt ((M : ℝ) + 1) := by
      refine Real.sqrt_le_sqrt ?_
      have hR : (N : ℝ) ≤ (M : ℝ) := by exact_mod_cast (by omega : N ≤ M)
      linarith
    have hstep' : coreNorm (mulHermite j c) ≤ 2 * Real.sqrt ((M : ℝ) + 1) * coreNorm c :=
      hstep.trans (mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_left hroot (by norm_num)) (coreNorm_nonneg c))
    calc (2 * Real.sqrt ((M : ℝ) + 1)) ^ js.length * coreNorm (mulHermite j c)
        ≤ (2 * Real.sqrt ((M : ℝ) + 1)) ^ js.length
            * (2 * Real.sqrt ((M : ℝ) + 1) * coreNorm c) :=
          mul_le_mul_of_nonneg_left hstep' (by positivity)
      _ = (2 * Real.sqrt ((M : ℝ) + 1)) ^ (js.length + 1) * coreNorm c := by
          rw [pow_succ]
          ring


/-! ### 14.3 The polynomial operator on a sector -/

/-- A monomial of degree `k` costs `‖a‖·(2√(M + 1))^k` on the sector. -/
theorem coreNorm_polyMul_monomial_le {m : Fin d →₀ ℕ} (a : ℂ) {N M : ℕ}
    (hNM : N + natDeg (fun j => m j) ≤ M) (c : CoreCoeff d)
    (hc : ∀ n ∈ c.support, natDeg n ≤ N) :
    coreNorm (polyMul (MvPolynomial.monomial m a) c)
      ≤ ‖a‖ * (2 * Real.sqrt ((M : ℝ) + 1)) ^ natDeg (fun j => m j) * coreNorm c := by
  rw [polyMul_monomial, coreNorm_smul]
  refine (mul_le_mul_of_nonneg_left
    (coreNorm_mulHermiteList_sector_le (monomialList fun j => m j) c N M
      (by rw [monomialList_length]; exact hNM) hc) (norm_nonneg a)).trans (le_of_eq ?_)
  rw [monomialList_length]
  ring

/-- The sector constant of the multiplication operator: the coefficients of `Φ` times the word
constant `(2√(M+1))^{deg Φ}`.  It is the mirror of §9.9's `driftL1Bound`, with the `ℓ²` norm of
the letters instead of the `ℓ¹` mass. -/
def polyMulSectorBound (Φ : MvPolynomial (Fin d) ℂ) (M : ℕ) : ℝ :=
  ∑ m ∈ Φ.support,
    ‖MvPolynomial.coeff m Φ‖ * (2 * Real.sqrt ((M : ℝ) + 1)) ^ Φ.totalDegree

theorem polyMulSectorBound_nonneg (Φ : MvPolynomial (Fin d) ℂ) (M : ℕ) :
    0 ≤ polyMulSectorBound Φ M :=
  Finset.sum_nonneg fun _ _ => by positivity

/-- **The multiplication operator is bounded on every sector**, with the explicit constant
`polyMulSectorBound Φ M` for `M ≥ N + deg Φ`: the `ℓ²` mirror of §9.9's `driftL1Bound`. -/
theorem polyMul_norm_sector_le {Φ : MvPolynomial (Fin d) ℂ} {N M : ℕ}
    (hNM : N + Φ.totalDegree ≤ M) (c : CoreCoeff d)
    (hc : ∀ n ∈ c.support, natDeg n ≤ N) :
    coreNorm (polyMul Φ c) ≤ polyMulSectorBound Φ M * coreNorm c := by
  classical
  have hsum : polyMul Φ c
      = ∑ m ∈ Φ.support,
          polyMul (MvPolynomial.monomial m (MvPolynomial.coeff m Φ)) c := by
    conv_lhs => rw [MvPolynomial.as_sum Φ]
    exact polyMul_sum Φ.support _ c
  rw [hsum]
  have hterm : ∀ m ∈ Φ.support,
      coreNorm (polyMul (MvPolynomial.monomial m (MvPolynomial.coeff m Φ)) c)
        ≤ ‖MvPolynomial.coeff m Φ‖ * (2 * Real.sqrt ((M : ℝ) + 1)) ^ Φ.totalDegree
            * coreNorm c := by
    intro m hm
    have hdeg : natDeg (fun j => m j) ≤ Φ.totalDegree := by
      rw [natDeg_ofFinsupp]
      exact MvPolynomial.le_totalDegree hm
    have hNM' : N + natDeg (fun j => m j) ≤ M := by omega
    refine (coreNorm_polyMul_monomial_le (MvPolynomial.coeff m Φ) hNM' c hc).trans ?_
    refine mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left ?_
      (norm_nonneg (MvPolynomial.coeff m Φ))) (coreNorm_nonneg c)
    refine pow_le_pow_right₀ ?_ hdeg
    have h1 : (1 : ℝ) ≤ Real.sqrt ((M : ℝ) + 1) := by
      refine Real.one_le_sqrt.mpr ?_
      have : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg M
      linarith
    linarith
  refine (coreNorm_finset_sum_le _ _).trans ?_
  rw [polyMulSectorBound, Finset.sum_mul]
  exact Finset.sum_le_sum hterm

/-- **The gradient bound on a sector.**  The multiplier `polyMul (∂ⱼΦ)` is bounded by the
explicit constant `gradSectorBound Φ N` on states of degree `≤ N + 1`.  The level `N + 1` is one
letter above the state's own sector: that is where the drift sends a state of sector `N`. -/
def gradSectorBound (Φ : MvPolynomial (Fin d) ℂ) (N : ℕ) : ℝ :=
  ∑ j : Fin d, polyMulSectorBound (MvPolynomial.pderiv j Φ)
    (N + 1 + (MvPolynomial.pderiv j Φ).totalDegree)

theorem gradSectorBound_nonneg (Φ : MvPolynomial (Fin d) ℂ) (N : ℕ) :
    0 ≤ gradSectorBound Φ N :=
  Finset.sum_nonneg fun _ _ => polyMulSectorBound_nonneg _ _

/-- **The `hgrad` of §12, on a sector**: `∂ⱼΦ` acts as a bounded multiplier at the level the
drift reaches, `{N ≤ N₀ + 1}`, with the constant `gradSectorBound Φ N₀`. -/
theorem pderiv_norm_sector_le {Φ : MvPolynomial (Fin d) ℂ} {N : ℕ} (j : Fin d)
    (c : CoreCoeff d) (hc : ∀ n ∈ c.support, natDeg n ≤ N + 1) :
    coreNorm (polyMul (MvPolynomial.pderiv j Φ) c) ≤ gradSectorBound Φ N * coreNorm c := by
  have h := polyMul_norm_sector_le (Φ := MvPolynomial.pderiv j Φ) (N := N + 1)
    (M := N + 1 + (MvPolynomial.pderiv j Φ).totalDegree) (by omega) c hc
  refine h.trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (coreNorm_nonneg c)
  exact Finset.single_le_sum (f := fun i => polyMulSectorBound (MvPolynomial.pderiv i Φ)
    (N + 1 + (MvPolynomial.pderiv i Φ).totalDegree))
    (fun i _ => polyMulSectorBound_nonneg _ _) (Finset.mem_univ j)

/-! ### 14.4 The estimate and the lower bound, on a sector -/

/-- §11's closing arithmetic at a single state: the uniform hypothesis of
`form_bound_of_sqrt_sum` weakened to the one state the estimate is about. -/
theorem form_bound_of_pointwise {T : CoreCoeff d → CoreCoeff d} {B : ℝ} (hB0 : 0 ≤ B)
    {c : CoreCoeff d}
    (hbound : ‖corePair c (T c)‖
      ≤ B * invSqrtTwo * coreNorm c * (Real.sqrt (d : ℝ) * Real.sqrt (numberForm c)
          + Real.sqrt (d : ℝ) * Real.sqrt (numberForm c + (d : ℝ) * coreNormSq c)))
    (δ : ℝ) (hδ : 0 < δ) :
    ‖corePair c (T c)‖
      ≤ δ * numberForm c + (B ^ 2 * (d : ℝ) / (2 * δ) + B * (d : ℝ)) * coreNormSq c := by
  have hinv0 : (0 : ℝ) ≤ invSqrtTwo := invSqrtTwo_nonneg
  have hinv1 : invSqrtTwo ≤ 1 := invSqrtTwo_le_one
  have hX0 : 0 ≤ numberForm c := numberForm_nonneg c
  have hN0 : 0 ≤ coreNormSq c := coreNormSq_nonneg c
  have hR0 : 0 ≤ coreNorm c := coreNorm_nonneg c
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
  have hbracket : Real.sqrt (d : ℝ) * Real.sqrt (numberForm c)
        + Real.sqrt (d : ℝ) * Real.sqrt (numberForm c + (d : ℝ) * coreNormSq c)
      ≤ 2 * Real.sqrt (d : ℝ) * Real.sqrt (numberForm c) + (d : ℝ) * coreNorm c := by
    have hdN : 0 ≤ (d : ℝ) * coreNormSq c := mul_nonneg hd0 hN0
    have hs := sqrt_add_le hX0 hdN
    have hmul : Real.sqrt ((d : ℝ) * coreNormSq c) = Real.sqrt (d : ℝ) * coreNorm c := by
      rw [Real.sqrt_mul hd0]; rfl
    have hdd : Real.sqrt (d : ℝ) * Real.sqrt (d : ℝ) = (d : ℝ) :=
      Real.mul_self_sqrt hd0
    have step1 : Real.sqrt (d : ℝ) * Real.sqrt (numberForm c + (d : ℝ) * coreNormSq c)
        ≤ Real.sqrt (d : ℝ)
          * (Real.sqrt (numberForm c) + Real.sqrt ((d : ℝ) * coreNormSq c)) :=
      mul_le_mul_of_nonneg_left hs (Real.sqrt_nonneg _)
    rw [hmul, mul_add, ← mul_assoc, hdd] at step1
    linarith
  have hstep5 : B * invSqrtTwo * coreNorm c * (Real.sqrt (d : ℝ) * Real.sqrt (numberForm c)
        + Real.sqrt (d : ℝ) * Real.sqrt (numberForm c + (d : ℝ) * coreNormSq c))
      ≤ B * invSqrtTwo * coreNorm c
        * (2 * Real.sqrt (d : ℝ) * Real.sqrt (numberForm c) + (d : ℝ) * coreNorm c) :=
    mul_le_mul_of_nonneg_left hbracket (mul_nonneg (mul_nonneg hB0 hinv0) hR0)
  have hxsq : Real.sqrt (numberForm c) ^ 2 = numberForm c := Real.sq_sqrt hX0
  have hv : 2 * Real.sqrt (numberForm c) * (B * invSqrtTwo * coreNorm c * Real.sqrt (d : ℝ))
      ≤ δ * numberForm c + B ^ 2 * (d : ℝ) * coreNorm c ^ 2 / (2 * δ) := by
    have ham := two_mul_le_add_div δ (Real.sqrt (numberForm c))
      (B * invSqrtTwo * coreNorm c * Real.sqrt (d : ℝ)) hδ
    have hv2 : (B * invSqrtTwo * coreNorm c * Real.sqrt (d : ℝ)) ^ 2 / δ
        = B ^ 2 * (d : ℝ) * coreNorm c ^ 2 / (2 * δ) := by
      have e : (B * invSqrtTwo * coreNorm c * Real.sqrt (d : ℝ)) ^ 2
          = B ^ 2 * invSqrtTwo ^ 2 * coreNorm c ^ 2 * (Real.sqrt (d : ℝ)) ^ 2 := by ring
      rw [e, invSqrtTwo_sq, Real.sq_sqrt hd0]
      ring
    calc 2 * Real.sqrt (numberForm c) * (B * invSqrtTwo * coreNorm c * Real.sqrt (d : ℝ))
          ≤ δ * Real.sqrt (numberForm c) ^ 2
              + (B * invSqrtTwo * coreNorm c * Real.sqrt (d : ℝ)) ^ 2 / δ := ham
      _ = δ * numberForm c + B ^ 2 * (d : ℝ) * coreNorm c ^ 2 / (2 * δ) := by
          rw [hxsq, hv2]
  have hslack : B * invSqrtTwo * (d : ℝ) * coreNorm c ^ 2 ≤ B * (d : ℝ) * coreNorm c ^ 2 := by
    have hle : B * invSqrtTwo ≤ B := by
      have := mul_le_mul_of_nonneg_left hinv1 hB0
      simpa using this
    have := mul_le_mul_of_nonneg_right hle (mul_nonneg hd0 (sq_nonneg (coreNorm c)))
    calc B * invSqrtTwo * (d : ℝ) * coreNorm c ^ 2
        = (B * invSqrtTwo) * ((d : ℝ) * coreNorm c ^ 2) := by ring
      _ ≤ B * ((d : ℝ) * coreNorm c ^ 2) := this
      _ = B * (d : ℝ) * coreNorm c ^ 2 := by ring
  have hfinal : B * invSqrtTwo * coreNorm c
        * (2 * Real.sqrt (d : ℝ) * Real.sqrt (numberForm c) + (d : ℝ) * coreNorm c)
      ≤ δ * numberForm c + (B ^ 2 * (d : ℝ) / (2 * δ) + B * (d : ℝ)) * coreNormSq c := by
    have e : B * invSqrtTwo * coreNorm c
          * (2 * Real.sqrt (d : ℝ) * Real.sqrt (numberForm c) + (d : ℝ) * coreNorm c)
        = 2 * Real.sqrt (numberForm c) * (B * invSqrtTwo * coreNorm c * Real.sqrt (d : ℝ))
          + B * invSqrtTwo * (d : ℝ) * coreNorm c ^ 2 := by ring
    rw [e, ← coreNorm_sq]
    have hsum := add_le_add hv hslack
    have harith : (δ * numberForm c + B ^ 2 * (d : ℝ) * coreNorm c ^ 2 / (2 * δ))
          + B * (d : ℝ) * coreNorm c ^ 2
        = δ * numberForm c + (B ^ 2 * (d : ℝ) / (2 * δ) + B * (d : ℝ)) * coreNorm c ^ 2 := by
      field_simp
      ring
    linarith
  exact hbound.trans (hstep5.trans hfinal)

/-- One derivative letter, bounded on a sector: `corePair_polyMul_diffHermite_le` with the
multiplier bound taken at the sector `{N ≤ N₀ + 1}` its two ladder images land in. -/
theorem corePair_polyMul_diffHermite_sector_le {Ψ : Fin d → MvPolynomial (Fin d) ℂ} {M : ℝ}
    {N : ℕ}
    (hgrad : ∀ j : Fin d, ∀ c : CoreCoeff d, (∀ n ∈ c.support, natDeg n ≤ N + 1) →
      coreNorm (polyMul (Ψ j) c) ≤ M * coreNorm c)
    (c : CoreCoeff d) (hc : ∀ n ∈ c.support, natDeg n ≤ N) (j : Fin d) :
    ‖corePair c (polyMul (Ψ j) (diffHermite j c))‖
      ≤ invSqrtTwo * (M * coreNorm c)
        * (coreNorm (hopStep (j, false) c) + coreNorm (hopStep (j, true) c)) := by
  have hinv0 : (0 : ℝ) ≤ invSqrtTwo := invSqrtTwo_nonneg
  have hmain : ‖corePair c (polyMul (Ψ j) (hopStep (j, false) c - hopStep (j, true) c))‖
      ≤ M * coreNorm c
        * (coreNorm (hopStep (j, false) c) + coreNorm (hopStep (j, true) c)) := by
    rw [polyMul_sub, corePair_sub]
    calc ‖corePair c (polyMul (Ψ j) (hopStep (j, false) c))
            - corePair c (polyMul (Ψ j) (hopStep (j, true) c))‖
          ≤ ‖corePair c (polyMul (Ψ j) (hopStep (j, false) c))‖
            + ‖corePair c (polyMul (Ψ j) (hopStep (j, true) c))‖ := norm_sub_le _ _
      _ ≤ coreNorm c * (M * coreNorm (hopStep (j, false) c))
            + coreNorm c * (M * coreNorm (hopStep (j, true) c)) := by
          refine add_le_add ?_ ?_
          · exact (norm_corePair_le c _).trans (mul_le_mul_of_nonneg_left
              (hgrad j _ (fun n hn => hopStep_band hc hn)) (coreNorm_nonneg c))
          · exact (norm_corePair_le c _).trans (mul_le_mul_of_nonneg_left
              (hgrad j _ (fun n hn => hopStep_band hc hn)) (coreNorm_nonneg c))
      _ = M * coreNorm c
            * (coreNorm (hopStep (j, false) c) + coreNorm (hopStep (j, true) c)) := by ring
  have hsplit : diffHermite j c
      = ((invSqrtTwo : ℝ) : ℂ) • (hopStep (j, false) c - hopStep (j, true) c) := rfl
  have hstar : star ((invSqrtTwo : ℝ) : ℂ) = ((invSqrtTwo : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  rw [hsplit, polyMul_smul_arg, corePair_smul, hstar, norm_mul, Complex.norm_real,
    Real.norm_eq_abs, abs_of_nonneg hinv0]
  calc invSqrtTwo
        * ‖corePair c (polyMul (Ψ j) (hopStep (j, false) c - hopStep (j, true) c))‖
      ≤ invSqrtTwo * (M * coreNorm c
          * (coreNorm (hopStep (j, false) c) + coreNorm (hopStep (j, true) c))) :=
        mul_le_mul_of_nonneg_left hmain hinv0
    _ = invSqrtTwo * (M * coreNorm c)
          * (coreNorm (hopStep (j, false) c) + coreNorm (hopStep (j, true) c)) := by ring

/-- **§11's letter-family estimate from a sector hypothesis**: the same constant,
`δ·⟪c, N c⟫ + (M²d/(2δ) + Md)‖c‖²`, with `hgrad` required only on `{N ≤ N₀ + 1}`. -/
theorem form_bound_of_letter_family_sector {Ψ : Fin d → MvPolynomial (Fin d) ℂ} {M : ℝ}
    (hM0 : 0 ≤ M) {N : ℕ}
    (hgrad : ∀ j : Fin d, ∀ c : CoreCoeff d, (∀ n ∈ c.support, natDeg n ≤ N + 1) →
      coreNorm (polyMul (Ψ j) c) ≤ M * coreNorm c)
    (δ : ℝ) (hδ : 0 < δ) (c : CoreCoeff d) (hc : ∀ n ∈ c.support, natDeg n ≤ N) :
    ‖corePair c (∑ j : Fin d, polyMul (Ψ j) (diffHermite j c))‖
      ≤ δ * numberForm c + (M ^ 2 * (d : ℝ) / (2 * δ) + M * (d : ℝ)) * coreNormSq c := by
  classical
  have hletter : ∀ j : Fin d, ‖corePair c (polyMul (Ψ j) (diffHermite j c))‖
      ≤ invSqrtTwo * (M * coreNorm c)
        * (coreNorm (hopStep (j, false) c) + coreNorm (hopStep (j, true) c)) :=
    fun j => corePair_polyMul_diffHermite_sector_le hgrad c hc j
  have hstep : ‖corePair c (∑ j : Fin d, polyMul (Ψ j) (diffHermite j c))‖
      ≤ ∑ j : Fin d, ‖corePair c (polyMul (Ψ j) (diffHermite j c))‖ := by
    rw [corePair_finset_sum]
    exact norm_sum_le _ _
  have hsum1 : ∑ j : Fin d, ‖corePair c (polyMul (Ψ j) (diffHermite j c))‖
      ≤ invSqrtTwo * (M * coreNorm c)
          * (∑ j : Fin d, coreNorm (hopStep (j, false) c)
            + ∑ j : Fin d, coreNorm (hopStep (j, true) c)) := by
    refine (Finset.sum_le_sum fun j _ => hletter j).trans (le_of_eq ?_)
    rw [← Finset.mul_sum, Finset.sum_add_distrib]
  have hsum2 : ∑ j : Fin d, coreNorm (hopStep (j, false) c)
        + ∑ j : Fin d, coreNorm (hopStep (j, true) c)
      ≤ Real.sqrt (d : ℝ) * Real.sqrt (numberForm c)
        + Real.sqrt (d : ℝ) * Real.sqrt (numberForm c + (d : ℝ) * coreNormSq c) :=
    add_le_add (sum_coreNorm_hopStep_le false c) (sum_coreNorm_hopStep_le true c)
  have hshape : invSqrtTwo * (M * coreNorm c)
        * (∑ j : Fin d, coreNorm (hopStep (j, false) c)
          + ∑ j : Fin d, coreNorm (hopStep (j, true) c))
      = M * invSqrtTwo * coreNorm c
        * (∑ j : Fin d, coreNorm (hopStep (j, false) c)
          + ∑ j : Fin d, coreNorm (hopStep (j, true) c)) := by ring
  have hbound : ‖corePair c (∑ j : Fin d, polyMul (Ψ j) (diffHermite j c))‖
      ≤ M * invSqrtTwo * coreNorm c * (Real.sqrt (d : ℝ) * Real.sqrt (numberForm c)
          + Real.sqrt (d : ℝ) * Real.sqrt (numberForm c + (d : ℝ) * coreNormSq c)) := by
    refine hstep.trans (hsum1.trans ?_)
    rw [hshape]
    exact mul_le_mul_of_nonneg_left hsum2
      (mul_nonneg (mul_nonneg hM0 invSqrtTwo_nonneg) (coreNorm_nonneg c))
  exact form_bound_of_pointwise (T := fun c => ∑ j : Fin d, polyMul (Ψ j) (diffHermite j c))
    hM0 hbound δ hδ

/-- **`polyDrift_form_bound` without `hgrad`**: on `{N ≤ N₀}` the drift's form is dominated by
the number form with `M := gradSectorBound Φ N₀`, no hypothesis on the potential. -/
theorem polyDrift_form_bound_sector {Φ : MvPolynomial (Fin d) ℂ} {N : ℕ} (δ : ℝ)
    (hδ : 0 < δ) (c : CoreCoeff d) (hc : ∀ n ∈ c.support, natDeg n ≤ N) :
    ‖corePair c (polyDrift Φ c)‖
      ≤ δ * numberForm c
        + (gradSectorBound Φ N ^ 2 * (d : ℝ) / (2 * δ) + gradSectorBound Φ N * (d : ℝ))
            * coreNormSq c := by
  have hmain := form_bound_of_letter_family_sector (Ψ := fun j => MvPolynomial.pderiv j Φ)
    (gradSectorBound_nonneg Φ N) (fun j _ hc' => pderiv_norm_sector_le j _ hc') δ hδ c hc
  have hnorm : ‖corePair c (polyDrift Φ c)‖
      = ‖corePair c (∑ j : Fin d, polyMul (MvPolynomial.pderiv j Φ) (diffHermite j c))‖ := by
    rw [polyDrift, corePair_neg, norm_neg]
  rw [hnorm]
  exact hmain


/-- `semibounded_of_form_bound` from a form bound at the single state — the KLMN conclusion a
sector estimate supports. -/
theorem semibounded_of_pointwise {T : CoreCoeff d → CoreCoeff d} {δ C : ℝ} (hδ1 : δ ≤ 1)
    {c : CoreCoeff d}
    (h : ‖corePair c (T c)‖ ≤ δ * numberForm c + C * coreNormSq c) :
    -C * coreNormSq c ≤ (corePair c (numberOp c + T c)).re := by
  rw [corePair_add, Complex.add_re, corePair_numberOp_re]
  have hre : -(‖corePair c (T c)‖) ≤ (corePair c (T c)).re := by
    have h1 := Complex.abs_re_le_norm (corePair c (T c))
    have h2 := neg_abs_le (corePair c (T c)).re
    linarith
  have hbound : -(δ * numberForm c + C * coreNormSq c) ≤ -(‖corePair c (T c)‖) := by
    linarith
  have hnonneg : 0 ≤ (1 - δ) * numberForm c := by
    have := numberForm_nonneg c
    nlinarith
  linarith

/-- **The plan's drift bound on a sector**, with `B = driftScale β σ (gradSectorBound Φ N₀)`. -/
theorem driftOperator_form_bound_sector (β σ : ℝ) {Φ : MvPolynomial (Fin d) ℂ} {N : ℕ}
    (δ : ℝ) (hδ : 0 < δ) (c : CoreCoeff d) (hc : ∀ n ∈ c.support, natDeg n ≤ N) :
    ‖corePair c (driftOperator β σ Φ c)‖
      ≤ δ * numberForm c
        + (driftScale β σ (gradSectorBound Φ N) ^ 2 * (d : ℝ) / (2 * δ)
          + driftScale β σ (gradSectorBound Φ N) * (d : ℝ)) * coreNormSq c := by
  classical
  have hw0 : 0 ≤ driftWeight β σ := driftWeight_nonneg β σ
  have hnorm : ‖corePair c (driftOperator β σ Φ c)‖
      = driftWeight β σ * ‖corePair c (polyDrift Φ c)‖ := by
    rw [driftOperator, corePair_smul]
    have hstar : star ((driftWeight β σ : ℝ) : ℂ) = ((driftWeight β σ : ℝ) : ℂ) := by
      rw [Complex.star_def, Complex.conj_ofReal]
    rw [hstar, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hw0]
  rcases lt_or_eq_of_le hw0 with hwpos | hwzero
  · have hδw : 0 < δ / driftWeight β σ := div_pos hδ hwpos
    have hbound := polyDrift_form_bound_sector (Φ := Φ) (N := N) (δ / driftWeight β σ)
      hδw c hc
    rw [hnorm]
    refine (mul_le_mul_of_nonneg_left hbound (le_of_lt hwpos)).trans (le_of_eq ?_)
    show driftWeight β σ * (δ / driftWeight β σ * numberForm c
          + (gradSectorBound Φ N ^ 2 * (d : ℝ) / (2 * (δ / driftWeight β σ))
            + gradSectorBound Φ N * (d : ℝ)) * coreNormSq c)
        = δ * numberForm c + (driftScale β σ (gradSectorBound Φ N) ^ 2 * (d : ℝ) / (2 * δ)
            + driftScale β σ (gradSectorBound Φ N) * (d : ℝ)) * coreNormSq c
    rw [show driftScale β σ (gradSectorBound Φ N) = driftWeight β σ * gradSectorBound Φ N
      from rfl]
    field_simp
  · have hdrift : driftOperator β σ Φ c = 0 := by
      rw [driftOperator, ← hwzero]
      simp
    have hB0 : driftScale β σ (gradSectorBound Φ N) = 0 := by
      rw [driftScale, ← hwzero, zero_mul]
    rw [hdrift, corePair_zero_right, norm_zero, hB0]
    have hzero : (0 : ℝ) ^ 2 * (d : ℝ) / (2 * δ) + 0 * (d : ℝ) = 0 := by ring
    rw [hzero, zero_mul, add_zero]
    exact mul_nonneg (le_of_lt hδ) (numberForm_nonneg c)

/-- **`N + K_drift` is bounded below on each sector**, with the sector constant and no gradient
hypothesis: §13's `pcnlDrift_semibounded_eps` with `M` read off the sector instead of assumed. -/
theorem pcnlDrift_semibounded_sector (β σ : ℝ) {Φ : MvPolynomial (Fin d) ℂ} {N : ℕ}
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (c : CoreCoeff d)
    (hc : ∀ n ∈ c.support, natDeg n ≤ N) :
    -((driftScale β σ (gradSectorBound Φ N) ^ 2 * (d : ℝ) / (2 * δ)
        + driftScale β σ (gradSectorBound Φ N) * (d : ℝ))) * coreNormSq c
      ≤ (corePair c (numberOp c + driftOperator β σ Φ c)).re :=
  semibounded_of_pointwise hδ1
    (driftOperator_form_bound_sector β σ (Φ := Φ) (N := N) δ hδ c hc)

/-! ### 14.5 The global hypothesis is not attainable -/

theorem coreNormSq_single (m : Fin d → ℕ) (a : ℂ) :
    coreNormSq (Finsupp.single m a) = ‖a‖ ^ 2 := by
  rw [← sum_sq_subset (c := Finsupp.single m a) (s := {m}) (by
    intro x hx
    simpa using Finsupp.support_single_subset hx)]
  simp

/-- A basis vector has the norm of its coefficient, the computation the refutation uses. -/
theorem coreNorm_single (m : Fin d → ℕ) (a : ℂ) :
    coreNorm (Finsupp.single m a) = ‖a‖ := by
  rw [coreNorm, coreNormSq_single, Real.sqrt_sq (norm_nonneg a)]

/-- Basis vectors pair to `a·conj b` at equal indices and to `0` at distinct ones — the
orthogonality that lets `corePair_raise_polyMul_X` read one ladder letter at a time. -/
theorem corePair_single_single (m m' : Fin d → ℕ) (a b : ℂ) :
    corePair (Finsupp.single m a) (Finsupp.single m' b) = if m = m' then a * star b else 0 := by
  classical
  by_cases h : m = m'
  · subst h
    rw [if_pos rfl,
      corePair_eq_sum (c := Finsupp.single m a) (c' := Finsupp.single m b) (s := {m})
        Finsupp.support_single_subset Finsupp.support_single_subset]
    simp
  · rw [if_neg h,
      corePair_eq_sum (c := Finsupp.single m a) (c' := Finsupp.single m' b) (s := {m, m'})
        (fun x hx => by
          have hx1 := Finsupp.support_single_subset hx
          simp only [Finset.mem_singleton] at hx1
          subst hx1
          exact Finset.mem_insert_self _ _)
        (fun x hx => by
          have hx1 := Finsupp.support_single_subset hx
          simp only [Finset.mem_singleton] at hx1
          rw [hx1]
          exact Finset.mem_insert_of_mem (Finset.mem_singleton_self m'))]
    refine Finset.sum_eq_zero fun x hx => ?_
    rcases Finset.mem_insert.mp hx with hm | hx
    · rw [hm, Finsupp.single_eq_same, Finsupp.single_eq_of_ne (a := m') (a' := m) h]
      simp
    · rw [Finset.mem_singleton.mp hx, Finsupp.single_eq_of_ne (a := m) (a' := m') (Ne.symm h)]
      simp

theorem raiseIdx_ne_lowerIdx (j : Fin d) (n : Fin d → ℕ) : raiseIdx j n ≠ lowerIdx j n := by
  intro h
  have h1 := congrFun h j
  rw [raiseIdx_apply_same, lowerIdx_apply_same] at h1
  omega

/-- **The value of `xⱼ` on a basis vector.**  Pairing `polyMul (X j) eₙ` against the raised test
vector `e_{n + eⱼ}` isolates the raising letter: the value is `√(nⱼ + 1)/√2`. -/
theorem corePair_raise_polyMul_X (j : Fin d) (n : Fin d → ℕ) :
    corePair (Finsupp.single (raiseIdx j n) (1 : ℂ))
        (polyMul (MvPolynomial.X j) (Finsupp.single n (1 : ℂ)))
      = ((Real.sqrt ((n j : ℝ) + 1) : ℝ) : ℂ) * ((invSqrtTwo : ℝ) : ℂ) := by
  have hstar : star ((invSqrtTwo : ℝ) : ℂ) = ((invSqrtTwo : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  have hraise : hopStep (j, true) (Finsupp.single n (1 : ℂ))
      = Finsupp.single (raiseIdx j n) (((Real.sqrt ((n j : ℝ) + 1) : ℝ) : ℂ)) := by
    rw [hopStep_single, stepAmp_raise, stepIdx]
    simp
  have hlower : hopStep (j, false) (Finsupp.single n (1 : ℂ))
      = Finsupp.single (lowerIdx j n) (((Real.sqrt (n j : ℝ) : ℝ) : ℂ)) := by
    rw [hopStep_single, stepAmp_lower, stepIdx]
    simp
  have hzero : corePair (Finsupp.single (raiseIdx j n) (1 : ℂ))
      (hopStep (j, false) (Finsupp.single n (1 : ℂ))) = 0 := by
    rw [hlower, corePair_single_single, if_neg (raiseIdx_ne_lowerIdx j n)]
  rw [polyMul_X, mulHermite, corePair_smul, hstar, corePair_add, hzero, add_zero, hraise,
    corePair_single_single, if_pos rfl, one_mul, Complex.star_def, Complex.conj_ofReal]
  ring


/-- **The growth of `xⱼ`**: `‖polyMul (X j) eₙ‖ ≥ √(nⱼ + 1)/√2`, by Cauchy–Schwarz read
backwards from the pairing value. -/
theorem sqrt_invSqrtTwo_le_coreNorm_polyMul_X {j : Fin d} (n : Fin d → ℕ) :
    Real.sqrt ((n j : ℝ) + 1) * invSqrtTwo
      ≤ coreNorm (polyMul (MvPolynomial.X j) (Finsupp.single n (1 : ℂ))) := by
  have hle := norm_corePair_le (Finsupp.single (raiseIdx j n) (1 : ℂ))
    (polyMul (MvPolynomial.X j) (Finsupp.single n (1 : ℂ)))
  rw [corePair_raise_polyMul_X] at hle
  have hval : ‖((Real.sqrt ((n j : ℝ) + 1) : ℝ) : ℂ) * ((invSqrtTwo : ℝ) : ℂ)‖
      = Real.sqrt ((n j : ℝ) + 1) * invSqrtTwo := by
    rw [norm_mul, Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (Real.sqrt_nonneg _), abs_of_nonneg invSqrtTwo_nonneg]
  rw [hval, coreNorm_single, norm_one, one_mul] at hle
  exact hle

/-- **The global `hgrad` is unattainable.**  For every `M` some state has
`M‖c‖ < ‖polyMul (X j) c‖`: multiplication by a non-constant polynomial is unbounded on the core,
so the sector level of §14.1–§14.4 is part of the statement. -/
theorem polyMul_X_unbounded (j : Fin d) (M : ℝ) :
    ∃ c : CoreCoeff d, M * coreNorm c < coreNorm (polyMul (MvPolynomial.X j) c) := by
  obtain ⟨n, hn⟩ := exists_nat_gt (max (2 * M ^ 2) 1)
  have hn2 : 2 * M ^ 2 < (n : ℝ) := lt_of_le_of_lt (le_max_left _ _) hn
  have hn1 : (1 : ℝ) < (n : ℝ) := lt_of_le_of_lt (le_max_right _ _) hn
  have hnpos : 0 < n := by exact_mod_cast (by linarith : (0 : ℝ) < (n : ℝ))
  refine ⟨Finsupp.single (Function.update (fun _ => 0 : Fin d → ℕ) j (n - 1)) (1 : ℂ), ?_⟩
  have hidx : (Function.update (fun _ => 0 : Fin d → ℕ) j (n - 1)) j = n - 1 := by simp
  have hbound := sqrt_invSqrtTwo_le_coreNorm_polyMul_X (j := j)
    (Function.update (fun _ => 0 : Fin d → ℕ) j (n - 1))
  have hMlt : M < Real.sqrt (n : ℝ) * invSqrtTwo := by
    have hsq : Real.sqrt (2 * M ^ 2) < Real.sqrt (n : ℝ) := Real.sqrt_lt_sqrt (by positivity) hn2
    have habs : Real.sqrt (2 * M ^ 2) = Real.sqrt 2 * |M| := by
      rw [Real.sqrt_mul (by norm_num), Real.sqrt_sq_eq_abs]
    have hle : Real.sqrt 2 * M ≤ Real.sqrt 2 * |M| :=
      mul_le_mul_of_nonneg_left (le_abs_self M) (Real.sqrt_nonneg 2)
    have h2 : Real.sqrt 2 * M < Real.sqrt (n : ℝ) := by rw [habs] at hsq; linarith
    have hpos2 : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
    calc M = (Real.sqrt 2 * M) / Real.sqrt 2 := by field_simp
      _ < Real.sqrt (n : ℝ) / Real.sqrt 2 := div_lt_div_of_pos_right h2 hpos2
      _ = Real.sqrt (n : ℝ) * invSqrtTwo := by
          rw [invSqrtTwo, one_div, div_eq_mul_inv]
  have hsqrt : Real.sqrt (((Function.update (fun _ => 0 : Fin d → ℕ) j (n - 1)) j : ℝ) + 1)
      = Real.sqrt (n : ℝ) := by
    rw [hidx]
    congr 1
    have hcast : (((n - 1 : ℕ)) : ℝ) = (n : ℝ) - 1 := by
      rcases n with _ | k
      · exact absurd hnpos (Nat.lt_irrefl 0)
      · simp
    linarith
  have hc : coreNorm (Finsupp.single (Function.update (fun _ => 0 : Fin d → ℕ) j (n - 1))
      (1 : ℂ)) = 1 := by rw [coreNorm_single, norm_one]
  rw [hc, mul_one]
  rw [← hsqrt] at hMlt
  exact lt_of_lt_of_le hMlt hbound

/-! ## 15. The Metropolis rejection filter `K_reject`

Plan `pcnl.md` §2.2 writes the pCNL step as `P₀ + K_drift + K_reject`, and §14 settled the middle
term.  This section supplies the third.  The filter is **not** a hopping operator — it multiplies
the occupation-`n` coefficient by an acceptance probability `ρ n` — so its band is `0` and it acts
as a diagonal damping.  The two facts the step actually needs are that the band is the drift's
(`pcnlFull_band`: `N₀ ↦ N₀ + K`, unaffected by the filter) and that the KLMN lower bound survives
(`pcnlFull_semibounded_sector`: the filter's contribution to the form is nonnegative).
-/

/-! ### 15.1 The filter as a diagonal multiplication -/

/-- The rejection filter: multiply the coefficient at occupation `n` by the acceptance
probability `ρ n`, leaving every other coefficient alone.  This is `K_reject` of the plan. -/
def rejectOp (ρ : (Fin d → ℕ) → ℝ) (c : CoreCoeff d) : CoreCoeff d :=
  c.sum fun n a => Finsupp.single n (((ρ n : ℝ) : ℂ) * a)

theorem rejectOp_apply (ρ : (Fin d → ℕ) → ℝ) (c : CoreCoeff d) (n : Fin d → ℕ) :
    rejectOp ρ c n = ((ρ n : ℝ) : ℂ) * c n := by
  classical
  rw [rejectOp, Finsupp.sum_apply, Finsupp.sum]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  by_cases hn : n ∈ c.support
  · simp [hn]
  · rw [if_neg hn, Finsupp.notMem_support_iff.mp hn, mul_zero]

/-- The filter is diagonal: on a basis vector it only rescales the coefficient, so it never moves
the occupation. -/
theorem rejectOp_single (ρ : (Fin d → ℕ) → ℝ) (n : Fin d → ℕ) (a : ℂ) :
    rejectOp ρ (Finsupp.single n a) = Finsupp.single n (((ρ n : ℝ) : ℂ) * a) := by
  classical
  rw [rejectOp, Finsupp.sum_single_index]
  simp

/-- Acceptance probability `1` everywhere is the identity filter. -/
theorem rejectOp_one (c : CoreCoeff d) : rejectOp (fun _ => 1) c = c := by
  refine Finsupp.ext fun n => ?_
  rw [rejectOp_apply]
  simp

/-- Two filters compose to the product filter — the diagonal structure that makes the rejection
step a multiplication operator rather than a hopping one. -/
theorem rejectOp_comp (ρ ρ' : (Fin d → ℕ) → ℝ) (c : CoreCoeff d) :
    rejectOp ρ (rejectOp ρ' c) = rejectOp (fun n => ρ n * ρ' n) c := by
  refine Finsupp.ext fun n => ?_
  rw [rejectOp_apply, rejectOp_apply, rejectOp_apply, ← mul_assoc, ← Complex.ofReal_mul]

/-! ### 15.2 The acceptance probability -/

/-- The Metropolis acceptance probability of a move whose potential energy changes by `ΔV`:
`min 1 (exp(−ΔV))`.  This is the `ρ` of the rejection filter. -/
def metropolisReject (ΔV : (Fin d → ℕ) → ℝ) : (Fin d → ℕ) → ℝ :=
  fun n => min 1 (Real.exp (-(ΔV n)))

theorem metropolisReject_nonneg (ΔV : (Fin d → ℕ) → ℝ) (n : Fin d → ℕ) :
    0 ≤ metropolisReject ΔV n :=
  le_min zero_le_one (Real.exp_pos _).le

theorem metropolisReject_le_one (ΔV : (Fin d → ℕ) → ℝ) (n : Fin d → ℕ) :
    metropolisReject ΔV n ≤ 1 :=
  min_le_left _ _

/-! ### 15.3 The band and the size of the filter -/

/-- The filter never enlarges the support of a state. -/
theorem mem_support_rejectOp {ρ : (Fin d → ℕ) → ℝ} {c : CoreCoeff d} {m : Fin d → ℕ}
    (hm : m ∈ (rejectOp ρ c).support) : m ∈ c.support := by
  rw [Finsupp.mem_support_iff] at hm ⊢
  intro hc
  rw [rejectOp_apply, hc, mul_zero] at hm
  exact hm rfl

/-- **The filter has band `0`**: it maps the sector `{N ≤ N₀}` into itself. -/
theorem rejectOp_band {ρ : (Fin d → ℕ) → ℝ} (c : CoreCoeff d) {N : ℕ}
    (hc : ∀ n ∈ c.support, natDeg n ≤ N) {m : Fin d → ℕ}
    (hm : m ∈ (rejectOp ρ c).support) : natDeg m ≤ N :=
  hc m (mem_support_rejectOp hm)

/-- The `ℓ²` mass of a filtered state, as an explicit sum over the original support. -/
theorem coreNormSq_rejectOp (ρ : (Fin d → ℕ) → ℝ) (c : CoreCoeff d) :
    coreNormSq (rejectOp ρ c) = ∑ n ∈ c.support, (ρ n) ^ 2 * ‖c n‖ ^ 2 := by
  classical
  rw [← sum_sq_subset (c := rejectOp ρ c) (s := c.support) fun x hx => mem_support_rejectOp hx]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [rejectOp_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

/-- **A filter with `0 ≤ ρ ≤ 1` is a contraction** in the core `ℓ²` norm — the stability the
pCNL step needs from its rejection half. -/
theorem coreNormSq_rejectOp_le {ρ : (Fin d → ℕ) → ℝ} (h0 : ∀ n, 0 ≤ ρ n)
    (h1 : ∀ n, ρ n ≤ 1) (c : CoreCoeff d) : coreNormSq (rejectOp ρ c) ≤ coreNormSq c := by
  rw [coreNormSq_rejectOp, coreNormSq]
  refine Finset.sum_le_sum fun n _ => ?_
  have hsq : (ρ n) ^ 2 ≤ 1 := by nlinarith [h0 n, h1 n]
  calc (ρ n) ^ 2 * ‖c n‖ ^ 2 ≤ 1 * ‖c n‖ ^ 2 :=
        mul_le_mul_of_nonneg_right hsq (by positivity)
    _ = ‖c n‖ ^ 2 := one_mul _

theorem coreNorm_rejectOp_le {ρ : (Fin d → ℕ) → ℝ} (h0 : ∀ n, 0 ≤ ρ n)
    (h1 : ∀ n, ρ n ≤ 1) (c : CoreCoeff d) : coreNorm (rejectOp ρ c) ≤ coreNorm c := by
  calc coreNorm (rejectOp ρ c) = Real.sqrt (coreNormSq (rejectOp ρ c)) := rfl
    _ ≤ Real.sqrt (coreNormSq c) := Real.sqrt_le_sqrt (coreNormSq_rejectOp_le h0 h1 c)
    _ = coreNorm c := rfl

/-! ### 15.4 The filter's contribution to the form -/

/-- The pairing of a state with its own filtered image is the `ρ`-weighted mass. -/
theorem corePair_rejectOp (ρ : (Fin d → ℕ) → ℝ) (c : CoreCoeff d) :
    corePair c (rejectOp ρ c) = ∑ n ∈ c.support, (((ρ n * ‖c n‖ ^ 2 : ℝ)) : ℂ) := by
  classical
  rw [corePair_eq_sum (c' := rejectOp ρ c) (s := c.support) Finset.Subset.rfl
    fun x hx => mem_support_rejectOp hx]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [rejectOp_apply]
  have hz : c n * star (c n) = ((‖c n‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  have hcast : star (((ρ n : ℝ) : ℂ)) = ((ρ n : ℝ) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  rw [star_mul, hcast, ← mul_assoc, hz, ← Complex.ofReal_mul, mul_comm (‖c n‖ ^ 2) (ρ n)]

/-- **The filter only adds to the form.**  With a nonnegative acceptance probability,
`0 ≤ Re ⟪c, K_reject c⟫`, which is why it cannot spoil §13's lower bound. -/
theorem re_corePair_rejectOp_nonneg {ρ : (Fin d → ℕ) → ℝ} (h0 : ∀ n, 0 ≤ ρ n)
    (c : CoreCoeff d) : 0 ≤ (corePair c (rejectOp ρ c)).re := by
  rw [corePair_rejectOp, Complex.re_sum]
  refine Finset.sum_nonneg fun n _ => ?_
  rw [Complex.ofReal_re]
  exact mul_nonneg (h0 n) (by positivity)

/-! ### 15.5 The full pCNL step -/

/-- The whole step `P₀ + K_drift + K_reject` on the core: the number operator, the polynomial
drift of §12, and the rejection filter. -/
def pcnlFull (β σ : ℝ) (Φ : MvPolynomial (Fin d) ℂ) (ρ : (Fin d → ℕ) → ℝ)
    (c : CoreCoeff d) : CoreCoeff d :=
  numberOp c + driftOperator β σ Φ c + rejectOp ρ c

/-- **The full step is finite-band.**  Rejection contributes band `0`, so one step maps the sector
`{N ≤ N₀}` into `{N ≤ N₀ + K}` when the potential has degree `≤ K`: the band is the drift's. -/
theorem pcnlFull_band {K : ℕ} {Φ : MvPolynomial (Fin d) ℂ} (hK : Φ.totalDegree ≤ K)
    (β σ : ℝ) (ρ : (Fin d → ℕ) → ℝ) (c : CoreCoeff d) {N : ℕ}
    (hc : ∀ n ∈ c.support, natDeg n ≤ N) {m : Fin d → ℕ}
    (hm : m ∈ (pcnlFull β σ Φ ρ c).support) : natDeg m ≤ N + K := by
  classical
  rw [pcnlFull] at hm
  rcases Finset.mem_union.mp (Finsupp.support_add hm) with h | h
  · rcases Finset.mem_union.mp (Finsupp.support_add h) with h1 | h2
    · exact le_trans (hc m (mem_support_numberOp h1)) (Nat.le_add_right N K)
    · rw [driftOperator] at h2
      exact polyDrift_band hK c hc (mem_support_smul h2)
  · exact le_trans (rejectOp_band c hc h) (Nat.le_add_right N K)

/-- **The KLMN lower bound for the full step.**  §14's sector semiboundedness
(`pcnlDrift_semibounded_sector`) plus §15.4's positivity: the filter only shifts the form up. -/
theorem pcnlFull_semibounded_sector (β σ : ℝ) {Φ : MvPolynomial (Fin d) ℂ}
    {ρ : (Fin d → ℕ) → ℝ} {N : ℕ} (hρ0 : ∀ n, 0 ≤ ρ n)
    (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (c : CoreCoeff d)
    (hc : ∀ n ∈ c.support, natDeg n ≤ N) :
    -((driftScale β σ (gradSectorBound Φ N) ^ 2 * (d : ℝ) / (2 * δ)
        + driftScale β σ (gradSectorBound Φ N) * (d : ℝ))) * coreNormSq c
      ≤ (corePair c (pcnlFull β σ Φ ρ c)).re := by
  have hbase := pcnlDrift_semibounded_sector β σ (Φ := Φ) (N := N) δ hδ hδ1 c hc
  have hpos := re_corePair_rejectOp_nonneg hρ0 c
  rw [pcnlFull, corePair_add, Complex.add_re]
  linarith

/-- **The pCNL step with the Metropolis filter is semibounded with no hypothesis.**
`ρ = metropolisReject ΔV` discharges §15.5's positivity condition outright: acceptance
probabilities are nonnegative by construction. -/
theorem pcnlFull_metropolis_semibounded (β σ : ℝ) {Φ : MvPolynomial (Fin d) ℂ}
    (ΔV : (Fin d → ℕ) → ℝ) {N : ℕ} (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (c : CoreCoeff d) (hc : ∀ n ∈ c.support, natDeg n ≤ N) :
    -((driftScale β σ (gradSectorBound Φ N) ^ 2 * (d : ℝ) / (2 * δ)
        + driftScale β σ (gradSectorBound Φ N) * (d : ℝ))) * coreNormSq c
      ≤ (corePair c (pcnlFull β σ Φ (metropolisReject ΔV) c)).re :=
  pcnlFull_semibounded_sector β σ (metropolisReject_nonneg ΔV) δ hδ hδ1 c hc

/-- **The Metropolis filter is a contraction** on the core, so the step's rejection half costs
nothing when iterated. -/
theorem coreNorm_pcnlFull_reject_le (ΔV : (Fin d → ℕ) → ℝ) (c : CoreCoeff d) :
    coreNorm (rejectOp (metropolisReject ΔV) c) ≤ coreNorm c :=
  coreNorm_rejectOp_le (metropolisReject_nonneg ΔV) (metropolisReject_le_one ΔV) c

/-! ## 16. The sector constant is a coefficient bound

§14 replaced the unattainable global `hgrad` by the sector constant `gradSectorBound Φ N`.  What
that constant has to be compared with is the architecture's weight-space bound `M_ε = 2K/ε`
(`BayesianTransformer.epsProj_fderiv_le`); the two live in different models, so the comparison is
a statement about **coefficients**.  `coeffMass (∂ⱼΦ)` is the `ℓ¹` mass of the derivative's
coefficients and `GradCoeffBound Φ M` says every one of them is at most `M`.  §16.1 computes the
sector constant in those terms, §16.2 shows the coefficient bound is automatic
(`M = deg Φ · coeffMass Φ`), and §16.3 carries it through §14's constant into §12's `B`, giving
`B ≤ β²σ²K/ε` times the explicit level factor: the `ε⁻¹` of the architecture's Theorem 1, with the
truncation level entering only polynomially.
-/

/-! ### 16.1 The coefficient mass -/

/-- The `ℓ¹` mass of a polynomial's coefficients. -/
def coeffMass (Φ : MvPolynomial (Fin d) ℂ) : ℝ :=
  ∑ m ∈ Φ.support, ‖MvPolynomial.coeff m Φ‖

theorem coeffMass_nonneg (Φ : MvPolynomial (Fin d) ℂ) : 0 ≤ coeffMass Φ :=
  Finset.sum_nonneg fun _ _ => norm_nonneg _

/-- §14's `polyMulSectorBound` is the coefficient mass times the level factor — the constant is a
coefficient quantity already, this reads it as one. -/
theorem polyMulSectorBound_eq_coeffMass (Φ : MvPolynomial (Fin d) ℂ) (M : ℕ) :
    polyMulSectorBound Φ M
      = coeffMass Φ * (2 * Real.sqrt ((M : ℝ) + 1)) ^ Φ.totalDegree := by
  rw [polyMulSectorBound, coeffMass, Finset.sum_mul]

theorem polyMulSectorBound_mono (Φ : MvPolynomial (Fin d) ℂ) {M M' : ℕ} (h : M ≤ M') :
    polyMulSectorBound Φ M ≤ polyMulSectorBound Φ M' := by
  rw [polyMulSectorBound_eq_coeffMass, polyMulSectorBound_eq_coeffMass]
  refine mul_le_mul_of_nonneg_left ?_ (coeffMass_nonneg Φ)
  have hR : (M : ℝ) ≤ (M' : ℝ) := by exact_mod_cast h
  have h2 : Real.sqrt ((M : ℝ) + 1) ≤ Real.sqrt ((M' : ℝ) + 1) := by
    refine Real.sqrt_le_sqrt ?_
    linarith
  exact pow_le_pow_left₀ (by positivity) (by linarith) _

/-- A monomial's coefficient mass is the size of its coefficient. -/
theorem coeffMass_monomial (m : Fin d →₀ ℕ) (a : ℂ) :
    coeffMass (MvPolynomial.monomial m a) = ‖a‖ := by
  classical
  rw [coeffMass]
  by_cases ha : a = 0
  · simp [ha]
  · rw [MvPolynomial.support_monomial, if_neg ha, Finset.sum_singleton]
    simp

/-- The mass over any finset of exponents is at most the mass of the support. -/
theorem sum_norm_coeff_le (Φ : MvPolynomial (Fin d) ℂ) (s : Finset (Fin d →₀ ℕ)) :
    ∑ m ∈ s, ‖MvPolynomial.coeff m Φ‖ ≤ coeffMass Φ := by
  classical
  rw [coeffMass]
  refine (Finset.sum_le_sum_of_subset_of_nonneg (Finset.subset_union_left :
    s ⊆ s ∪ Φ.support) (fun _ _ _ => norm_nonneg _)).trans_eq ?_
  refine (Finset.sum_subset (Finset.subset_union_right :
    Φ.support ⊆ s ∪ Φ.support) ?_).symm
  intro x hx hxΦ
  have hzero : MvPolynomial.coeff x Φ = 0 := by
    by_contra h
    exact hxΦ (MvPolynomial.mem_support_iff.mpr h)
  rw [hzero, norm_zero]

theorem coeffMass_add_le (Φ Ψ : MvPolynomial (Fin d) ℂ) :
    coeffMass (Φ + Ψ) ≤ coeffMass Φ + coeffMass Ψ := by
  classical
  have h1 : (∑ m ∈ (Φ + Ψ).support, ‖MvPolynomial.coeff m (Φ + Ψ)‖)
      ≤ ∑ m ∈ (Φ + Ψ).support,
          (‖MvPolynomial.coeff m Φ‖ + ‖MvPolynomial.coeff m Ψ‖) :=
    Finset.sum_le_sum fun m _ => by
      rw [MvPolynomial.coeff_add]
      exact norm_add_le _ _
  have h2 : (∑ m ∈ (Φ + Ψ).support,
        (‖MvPolynomial.coeff m Φ‖ + ‖MvPolynomial.coeff m Ψ‖))
      ≤ coeffMass Φ + coeffMass Ψ := by
    rw [Finset.sum_add_distrib]
    refine add_le_add ?_ ?_
    · exact sum_norm_coeff_le Φ _
    · exact sum_norm_coeff_le Ψ _
  rw [coeffMass]
  exact h1.trans h2

theorem coeffMass_finset_sum_le {ι : Type*} (s : Finset ι)
    (g : ι → MvPolynomial (Fin d) ℂ) :
    coeffMass (∑ i ∈ s, g i) ≤ ∑ i ∈ s, coeffMass (g i) := by
  classical
  induction s using Finset.induction with
  | empty => simp [coeffMass]
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (coeffMass_add_le _ _).trans (add_le_add (le_refl _) ih)

/-! ### 16.2 A derivative's coefficient mass: the bound is automatic -/

/-- The coefficient form of the architecture's gradient bound: every coefficient of `∂ⱼΦ` is at
most `M`, uniformly in `j`.  This is the hypothesis `M_ε = 2K/ε` reads as. -/
def GradCoeffBound (Φ : MvPolynomial (Fin d) ℂ) (M : ℝ) : Prop :=
  ∀ j : Fin d, coeffMass (MvPolynomial.pderiv j Φ) ≤ M

/-- One exponent is at most the total degree of its monomial. -/
theorem apply_le_finsupp_sum (m : Fin d →₀ ℕ) (j : Fin d) :
    m j ≤ m.sum (fun _ e => e) := by
  classical
  rw [Finsupp.sum]
  by_cases h : m j = 0
  · simp [h]
  · refine Finset.single_le_sum (f := fun a => m a) (fun _ _ => Nat.zero_le _) ?_
    rw [Finsupp.mem_support_iff]
    exact h

theorem totalDegree_finset_sum_le {ι : Type*} (s : Finset ι)
    (g : ι → MvPolynomial (Fin d) ℂ) {K : ℕ} (hg : ∀ i ∈ s, (g i).totalDegree ≤ K) :
    (∑ i ∈ s, g i).totalDegree ≤ K := by
  classical
  induction s using Finset.induction with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    refine (MvPolynomial.totalDegree_add _ _).trans ?_
    rw [max_le_iff]
    exact ⟨hg a (Finset.mem_insert_self a s),
      ih fun i hi => hg i (Finset.mem_insert_of_mem hi)⟩

theorem sum_sub_single_le (m : Fin d →₀ ℕ) (j : Fin d) :
    ((m - Finsupp.single j 1).sum fun _ e => e) ≤ m.sum fun _ e => e := by
  classical
  have hpt : ∀ a ∈ (m - Finsupp.single j 1).support,
      ((m - Finsupp.single j 1 : Fin d →₀ ℕ) a) ≤ m a := by
    intro a _
    rw [Finsupp.tsub_apply]
    exact tsub_le_self
  calc (m - Finsupp.single j 1).sum (fun _ e => e)
      = ∑ a ∈ (m - Finsupp.single j 1).support,
          ((m - Finsupp.single j 1 : Fin d →₀ ℕ) a) := rfl
    _ ≤ ∑ a ∈ (m - Finsupp.single j 1).support, m a := Finset.sum_le_sum hpt
    _ ≤ ∑ a ∈ m.support, m a :=
        Finset.sum_le_sum_of_subset_of_nonneg Finsupp.support_tsub
          (fun _ _ _ => Nat.zero_le _)
    _ = m.sum (fun _ e => e) := rfl

/-- Differentiation does not raise the total degree. -/
theorem totalDegree_pderiv_le (j : Fin d) (Φ : MvPolynomial (Fin d) ℂ) :
    (MvPolynomial.pderiv j Φ).totalDegree ≤ Φ.totalDegree := by
  classical
  have hmono : ∀ m ∈ Φ.support,
      (MvPolynomial.pderiv j (MvPolynomial.monomial m (MvPolynomial.coeff m Φ))).totalDegree
        ≤ Φ.totalDegree := by
    intro m hm
    rw [MvPolynomial.pderiv_monomial]
    refine (MvPolynomial.totalDegree_monomial_le _ _).trans ?_
    exact (sum_sub_single_le m j).trans (MvPolynomial.le_totalDegree hm)
  have hexp : MvPolynomial.pderiv j Φ
      = ∑ m ∈ Φ.support,
          MvPolynomial.pderiv j (MvPolynomial.monomial m (MvPolynomial.coeff m Φ)) := by
    conv_lhs => rw [MvPolynomial.as_sum Φ]
    simp only [map_sum]
  rw [hexp]
  exact totalDegree_finset_sum_le _ _ hmono

/-- **The derivative's coefficient mass is bounded by the degree times the mass.**  This is the
coefficient-level content of a Lipschitz gradient: differentiating multiplies each coefficient by
its exponent, and no exponent exceeds the degree. -/
theorem coeffMass_pderiv_le (j : Fin d) (Φ : MvPolynomial (Fin d) ℂ) :
    coeffMass (MvPolynomial.pderiv j Φ) ≤ (Φ.totalDegree : ℝ) * coeffMass Φ := by
  classical
  have hexp : MvPolynomial.pderiv j Φ
      = ∑ m ∈ Φ.support,
          MvPolynomial.monomial (m - Finsupp.single j 1)
            (MvPolynomial.coeff m Φ * (m j : ℂ)) := by
    conv_lhs => rw [MvPolynomial.as_sum Φ]
    simp only [map_sum, MvPolynomial.pderiv_monomial]
  rw [hexp]
  have hstep : ∀ m ∈ Φ.support,
      coeffMass (MvPolynomial.monomial (m - Finsupp.single j 1)
        (MvPolynomial.coeff m Φ * (m j : ℂ))) = ‖MvPolynomial.coeff m Φ‖ * (m j : ℝ) := by
    intro m _
    rw [coeffMass_monomial, norm_mul, Complex.norm_natCast]
  refine (coeffMass_finset_sum_le _ _).trans ?_
  rw [Finset.sum_congr rfl hstep]
  calc ∑ m ∈ Φ.support, ‖MvPolynomial.coeff m Φ‖ * (m j : ℝ)
      ≤ ∑ m ∈ Φ.support, ‖MvPolynomial.coeff m Φ‖ * (Φ.totalDegree : ℝ) := by
        refine Finset.sum_le_sum fun m hm => ?_
        refine mul_le_mul_of_nonneg_left ?_ (norm_nonneg _)
        have h1 : m j ≤ Φ.totalDegree :=
          (apply_le_finsupp_sum m j).trans (MvPolynomial.le_totalDegree hm)
        exact_mod_cast h1
    _ = (Φ.totalDegree : ℝ) * coeffMass Φ := by
        rw [coeffMass, Finset.mul_sum]
        exact Finset.sum_congr rfl fun m _ => by ring

/-- **The coefficient bound is automatic.**  Every polynomial satisfies `GradCoeffBound` with
`M = deg Φ · coeffMass Φ`, so §16.3 applies with no hypothesis on `Φ`. -/
theorem gradCoeffBound_totalDegree_mul_coeffMass (Φ : MvPolynomial (Fin d) ℂ) :
    GradCoeffBound Φ ((Φ.totalDegree : ℝ) * coeffMass Φ) :=
  fun j => coeffMass_pderiv_le j Φ

/-! ### 16.3 The comparison with the architecture's `M_ε = 2K/ε` -/

/-- §14's sector constant, in coefficient terms: `d` derivative masses, each at most `M`, times
the level factor `(2√(N + 2 + deg Φ))^{deg Φ}`. -/
theorem gradSectorBound_le_of_gradCoeffBound {Φ : MvPolynomial (Fin d) ℂ} {M : ℝ}
    (hM : 0 ≤ M) (h : GradCoeffBound Φ M) (N : ℕ) :
    gradSectorBound Φ N
      ≤ (d : ℝ) * M * (2 * Real.sqrt ((N : ℝ) + 2 + (Φ.totalDegree : ℝ))) ^ Φ.totalDegree := by
  classical
  have hterm : ∀ j : Fin d, polyMulSectorBound (MvPolynomial.pderiv j Φ)
        (N + 1 + (MvPolynomial.pderiv j Φ).totalDegree)
      ≤ M * (2 * Real.sqrt ((N : ℝ) + 2 + (Φ.totalDegree : ℝ))) ^ Φ.totalDegree := by
    intro j
    have hdeg := totalDegree_pderiv_le j Φ
    have hd : ((MvPolynomial.pderiv j Φ).totalDegree : ℝ) ≤ (Φ.totalDegree : ℝ) := by
      exact_mod_cast hdeg
    have hbase : 2 * Real.sqrt ((↑(N + 1 + (MvPolynomial.pderiv j Φ).totalDegree) : ℝ) + 1)
        ≤ 2 * Real.sqrt ((N : ℝ) + 2 + (Φ.totalDegree : ℝ)) := by
      have harg : ((↑(N + 1 + (MvPolynomial.pderiv j Φ).totalDegree) : ℝ) + 1)
          ≤ (N : ℝ) + 2 + (Φ.totalDegree : ℝ) := by
        push_cast
        linarith
      have := Real.sqrt_le_sqrt harg
      linarith
    have hone : (1 : ℝ)
        ≤ 2 * Real.sqrt ((↑(N + 1 + (MvPolynomial.pderiv j Φ).totalDegree) : ℝ) + 1) := by
      have h1 : (1 : ℝ)
          ≤ Real.sqrt ((↑(N + 1 + (MvPolynomial.pderiv j Φ).totalDegree) : ℝ) + 1) := by
        refine Real.one_le_sqrt.mpr ?_
        push_cast
        have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
        linarith
      linarith
    rw [polyMulSectorBound_eq_coeffMass]
    refine mul_le_mul (h j) ?_ (by positivity) hM
    calc (2 * Real.sqrt ((↑(N + 1 + (MvPolynomial.pderiv j Φ).totalDegree) : ℝ) + 1))
          ^ (MvPolynomial.pderiv j Φ).totalDegree
        ≤ (2 * Real.sqrt ((↑(N + 1 + (MvPolynomial.pderiv j Φ).totalDegree) : ℝ) + 1))
            ^ Φ.totalDegree := pow_le_pow_right₀ hone hdeg
      _ ≤ (2 * Real.sqrt ((N : ℝ) + 2 + (Φ.totalDegree : ℝ))) ^ Φ.totalDegree :=
          pow_le_pow_left₀ (by positivity) hbase _
  calc gradSectorBound Φ N
      = ∑ j : Fin d, polyMulSectorBound (MvPolynomial.pderiv j Φ)
          (N + 1 + (MvPolynomial.pderiv j Φ).totalDegree) := rfl
    _ ≤ ∑ _j : Fin d, M * (2 * Real.sqrt ((N : ℝ) + 2 + (Φ.totalDegree : ℝ))) ^ Φ.totalDegree :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = (d : ℝ) * M * (2 * Real.sqrt ((N : ℝ) + 2 + (Φ.totalDegree : ℝ))) ^ Φ.totalDegree := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

/-- **The drift constant is `(β²σ²/2)` times the coefficient bound.**  A coefficient-level
gradient bound `GradCoeffBound Φ M` turns §14's sector constant `gradSectorBound Φ N` into §12's
`B = (β²σ²/2)·M`, up to the explicit level factor `d·(2√(N+2+deg Φ))^{deg Φ}`. -/
theorem driftScale_gradSectorBound_le (β σ : ℝ) {Φ : MvPolynomial (Fin d) ℂ} {M : ℝ}
    (hM : 0 ≤ M) (h : GradCoeffBound Φ M) (N : ℕ) :
    driftScale β σ (gradSectorBound Φ N)
      ≤ β ^ 2 * σ ^ 2 / 2 * M
        * ((d : ℝ) * (2 * Real.sqrt ((N : ℝ) + 2 + (Φ.totalDegree : ℝ))) ^ Φ.totalDegree) := by
  have hb := gradSectorBound_le_of_gradCoeffBound hM h N
  have hw : 0 ≤ β ^ 2 * σ ^ 2 / 2 := by positivity
  rw [driftScale, driftWeight]
  calc β ^ 2 * σ ^ 2 / 2 * gradSectorBound Φ N
      ≤ β ^ 2 * σ ^ 2 / 2 * ((d : ℝ) * M
          * (2 * Real.sqrt ((N : ℝ) + 2 + (Φ.totalDegree : ℝ))) ^ Φ.totalDegree) :=
        mul_le_mul_of_nonneg_left hb hw
    _ = β ^ 2 * σ ^ 2 / 2 * M
          * ((d : ℝ) * (2 * Real.sqrt ((N : ℝ) + 2 + (Φ.totalDegree : ℝ))) ^ Φ.totalDegree) := by
        ring

/-- **The `ε`-scaling, read on the sector.**  With the architecture's gradient bound in
coefficient form, `GradCoeffBound Φ (2K/ε)`, §12's drift constant `B` is at most `β²σ²K/ε` times
the explicit level factor.  So the `ε⁻¹` of the architecture's Theorem 1 is exactly the `ε⁻¹` of
the drift's constant, with the truncation level entering as a separate polynomial factor. -/
theorem driftScale_gradSectorBound_le_eps (β σ : ℝ) {Φ : MvPolynomial (Fin d) ℂ} {K ε : ℝ}
    (hK : 0 ≤ K) (hε : 0 < ε) (h : GradCoeffBound Φ (2 * K / ε)) (N : ℕ) :
    driftScale β σ (gradSectorBound Φ N)
      ≤ β ^ 2 * σ ^ 2 * K / ε
        * ((d : ℝ) * (2 * Real.sqrt ((N : ℝ) + 2 + (Φ.totalDegree : ℝ))) ^ Φ.totalDegree) := by
  have hM : 0 ≤ 2 * K / ε := by positivity
  have hstep := driftScale_gradSectorBound_le β σ hM h N
  refine hstep.trans (le_of_eq ?_)
  field_simp

/-- The drift constant with no hypothesis on `Φ` at all: the coefficient bound is
`M = deg Φ · (coefficient mass)`, which every polynomial satisfies. -/
theorem driftScale_gradSectorBound_le_coeffMass (β σ : ℝ) (Φ : MvPolynomial (Fin d) ℂ) (N : ℕ) :
    driftScale β σ (gradSectorBound Φ N)
      ≤ β ^ 2 * σ ^ 2 / 2 * ((Φ.totalDegree : ℝ) * coeffMass Φ)
        * ((d : ℝ) * (2 * Real.sqrt ((N : ℝ) + 2 + (Φ.totalDegree : ℝ))) ^ Φ.totalDegree) :=
  driftScale_gradSectorBound_le β σ
    (mul_nonneg (Nat.cast_nonneg _) (coeffMass_nonneg Φ))
    (gradCoeffBound_totalDegree_mul_coeffMass Φ) N

/-! ## 18. The plan's diagonal `P₀ = ρ^N`, and the full `P₀ + K_drift + K_reject`

§15 modelled the step's rejection half and §14 the drift's band; the plan's §2.2 operator is
`P_pCNL = P₀ + K_drift + K_reject` with `P₀` the *diagonal* `ρ^N` — the unadjusted pCN kernel, whose
spectrum is `λ_n = ρⁿ` (Module 1).  This section adds `P₀` and assembles the plan's operator on the
core.

* **`P₀` is diagonal with eigenvalue `ρ^{natDeg n}`** (`baseOp`, `baseOp_apply`), fixes the vacuum
  (`baseOp_vac`: `natDeg 0 = 0`, so `λ_0 = 1`) and composes (`baseOp_comp`), so it moves no
  occupation: `baseOp_band` gives it band `0`.
* **It is a contraction, and a strict one off the vacuum**: `coreNorm_baseOp_le` for `0 ≤ ρ ≤ 1`,
  and `coreNorm_baseOp_sector_le` — `‖P₀ c‖ ≤ ρ‖c‖` on `{N ≥ 1}`, the spectral gap `1 − ρ` read on
  the core.
* **The drift's norm on a sector** (§18.2): `coreNorm_diffHermite_sector_le` and
  `coreNorm_polyDrift_sector_le` give `‖K_drift c‖ ≤ driftStepBound β σ Φ N · ‖c‖`
  (`coreNorm_driftOperator_sector_le'`), the norm counterpart of §14's form bound, with
  `driftStepBound β σ Φ N = (β²σ²/2)·2√(N+1)·gradSectorBound Φ N`.
* **The assembled operator** (§18.3): `pcnlKernel ρ_H β σ Φ ρ_acc = P₀ + K_drift + K_reject`, with
  `pcnlKernel_band` (band `K`, the drift's — `P₀` and the filter contribute none) and the two
  contraction statements `coreNorm_pcnlKernel_le` (any sector, `P₀` at most `1`) and
  `coreNorm_pcnlKernel_sector_le` (`P₀` at most `ρ` off the vacuum).

§19 then iterates the operator: the band widens by `n·K` (`pcnlKernel_iter_band`), the norm is
bounded by the product of the level constants (`coreNorm_pcnlKernel_iter_le`), and `P₀` alone
converges to the invariant state geometrically at rate `ρ` (`coreNorm_iter_baseOp_le`,
`tendsto_iter_baseOp`).
-/

/-! ### 18.1 The diagonal, its vacuum, and its gap -/

/-- The plan's `P₀`: the diagonal `ρ^N`, multiplication by `ρ^{natDeg n}`. -/
def baseOp (ρ : ℝ) (c : CoreCoeff d) : CoreCoeff d :=
  c.sum fun n a => Finsupp.single n (((ρ ^ natDeg n : ℝ) : ℂ) * a)

theorem baseOp_apply (ρ : ℝ) (c : CoreCoeff d) (n : Fin d → ℕ) :
    baseOp ρ c n = ((ρ ^ natDeg n : ℝ) : ℂ) * c n := by
  classical
  rw [baseOp, Finsupp.sum_apply, Finsupp.sum]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_ite_eq']
  by_cases hn : n ∈ c.support
  · simp [hn]
  · rw [if_neg hn, Finsupp.notMem_support_iff.mp hn, mul_zero]

theorem mem_support_baseOp {ρ : ℝ} {c : CoreCoeff d} {m : Fin d → ℕ}
    (hm : m ∈ (baseOp ρ c).support) : m ∈ c.support := by
  rw [Finsupp.mem_support_iff] at hm ⊢
  intro hc
  rw [baseOp_apply, hc, mul_zero] at hm
  exact hm rfl

theorem baseOp_band {ρ : ℝ} (c : CoreCoeff d) {N : ℕ}
    (hc : ∀ n ∈ c.support, natDeg n ≤ N) {m : Fin d → ℕ}
    (hm : m ∈ (baseOp ρ c).support) : natDeg m ≤ N :=
  hc m (mem_support_baseOp hm)

/-- `P₀` does not move the support. -/
theorem support_iter_baseOp (ρ : ℝ) (c : CoreCoeff d) :
    ∀ n : ℕ, ∀ m ∈ ((baseOp ρ)^[n] c).support, m ∈ c.support := by
  intro n
  induction n with
  | zero => intro m hm; simpa using hm
  | succ n ih =>
    intro m hm
    rw [Function.iterate_succ_apply'] at hm
    exact ih m (mem_support_baseOp hm)

theorem baseOp_one (c : CoreCoeff d) : baseOp 1 c = c := by
  refine Finsupp.ext fun n => ?_
  rw [baseOp_apply]
  simp

theorem baseOp_comp (ρ ρ' : ℝ) (c : CoreCoeff d) :
    baseOp ρ (baseOp ρ' c) = baseOp (ρ * ρ') c := by
  refine Finsupp.ext fun n => ?_
  rw [baseOp_apply, baseOp_apply, baseOp_apply, mul_pow, ← mul_assoc, ← Complex.ofReal_mul]

/-- **`P₀` fixes the vacuum**: `natDeg 0 = 0`, so `ρ^0 = 1` on `e₀` for every `ρ`.  This is the
plan's `λ_0 = 1` — the reason `P₀` is a contraction but never a strict one on the whole core. -/
theorem baseOp_vac (ρ : ℝ) :
    baseOp ρ (Finsupp.single (0 : Fin d → ℕ) 1) = Finsupp.single (0 : Fin d → ℕ) 1 := by
  refine Finsupp.ext fun n => ?_
  rw [baseOp_apply]
  by_cases hn : n = 0
  · subst hn
    rw [Finsupp.single_eq_same, natDeg_zero, pow_zero]
    simp
  · simp [Ne.symm hn]

theorem coreNormSq_baseOp (ρ : ℝ) (c : CoreCoeff d) :
    coreNormSq (baseOp ρ c) = ∑ n ∈ c.support, (ρ ^ natDeg n) ^ 2 * ‖c n‖ ^ 2 := by
  classical
  rw [← sum_sq_subset (c := baseOp ρ c) (s := c.support) fun x hx => mem_support_baseOp hx]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [baseOp_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow, sq_abs]

/-- A diagonal with coefficients `aₙ` of size at most `a` is a contraction by `a`. -/
theorem coreNorm_baseOp_le_of_bound {ρ a : ℝ} {c : CoreCoeff d} (ha : 0 ≤ a)
    (h : ∀ n ∈ c.support, ‖ρ ^ natDeg n‖ ≤ a) :
    coreNorm (baseOp ρ c) ≤ a * coreNorm c := by
  have hsq : coreNormSq (baseOp ρ c) ≤ a ^ 2 * coreNormSq c := by
    rw [coreNormSq_baseOp, coreNormSq, Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hb := h n hn
    have h1 : (ρ ^ natDeg n) ^ 2 ≤ a ^ 2 := by
      rw [← sq_abs (ρ ^ natDeg n)]
      exact pow_le_pow_left₀ (abs_nonneg _) (by simpa [Real.norm_eq_abs] using hb) 2
    calc (ρ ^ natDeg n) ^ 2 * ‖c n‖ ^ 2 ≤ a ^ 2 * ‖c n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = a ^ 2 * ‖c n‖ ^ 2 := rfl
  calc coreNorm (baseOp ρ c) = Real.sqrt (coreNormSq (baseOp ρ c)) := rfl
    _ ≤ Real.sqrt (a ^ 2 * coreNormSq c) := Real.sqrt_le_sqrt hsq
    _ = a * coreNorm c := by
        rw [Real.sqrt_mul (sq_nonneg a), Real.sqrt_sq ha]
        rfl

theorem coreNorm_baseOp_le {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (c : CoreCoeff d) :
    coreNorm (baseOp ρ c) ≤ coreNorm c := by
  refine (coreNorm_baseOp_le_of_bound (ρ := ρ) (a := 1) zero_le_one fun n _ => ?_).trans_eq
    (one_mul _)
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 _)]
  exact pow_le_one₀ h0 h1

/-- **`P₀` contracts the non-vacuum core by `ρ`.**  The spectral gap `1 − ρ` of the pCN step, read
on the core: on `{N ≥ 1}` the eigenvalue `ρ^N` is at most `ρ`. -/
theorem coreNorm_baseOp_sector_le {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) {c : CoreCoeff d}
    (hc : ∀ n ∈ c.support, 1 ≤ natDeg n) :
    coreNorm (baseOp ρ c) ≤ ρ * coreNorm c := by
  refine coreNorm_baseOp_le_of_bound (a := ρ) h0 fun n hn => ?_
  have hdeg := hc n hn
  have hle : ρ ^ natDeg n ≤ ρ ^ 1 := pow_le_pow_of_le_one h0 h1 hdeg
  rw [Real.norm_eq_abs, abs_of_nonneg (pow_nonneg h0 _), pow_one] at *
  exact hle

/-- A diagonal with coefficients of size at most `r` scales the norm by `r` — the general form of
the rejection filter's contraction, with `r` the largest acceptance probability. -/
theorem coreNorm_rejectOp_le_of_bound {ρ : (Fin d → ℕ) → ℝ} {r : ℝ} (hr : ∀ n, ‖ρ n‖ ≤ r)
    (c : CoreCoeff d) : coreNorm (rejectOp ρ c) ≤ r * coreNorm c := by
  classical
  have hsq : coreNormSq (rejectOp ρ c) ≤ r ^ 2 * coreNormSq c := by
    rw [coreNormSq_rejectOp, coreNormSq, Finset.mul_sum]
    refine Finset.sum_le_sum fun n _ => ?_
    have h1 : (ρ n) ^ 2 ≤ r ^ 2 := by
      rw [← sq_abs (ρ n)]
      exact pow_le_pow_left₀ (abs_nonneg _) (by simpa [Real.norm_eq_abs] using hr n) 2
    calc (ρ n) ^ 2 * ‖c n‖ ^ 2 ≤ r ^ 2 * ‖c n‖ ^ 2 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = r ^ 2 * ‖c n‖ ^ 2 := rfl
  have hr0 : 0 ≤ r := le_trans (norm_nonneg _) (hr 0)
  calc coreNorm (rejectOp ρ c) = Real.sqrt (coreNormSq (rejectOp ρ c)) := rfl
    _ ≤ Real.sqrt (r ^ 2 * coreNormSq c) := Real.sqrt_le_sqrt hsq
    _ = r * coreNorm c := by
        rw [Real.sqrt_mul (sq_nonneg r), Real.sqrt_sq hr0]
        rfl

/-! ### 18.2 The drift's norm on a sector -/

theorem coreNorm_sub_le (x y : CoreCoeff d) :
    coreNorm (x - y) ≤ coreNorm x + coreNorm y := by
  rw [sub_eq_add_neg]
  exact (coreNorm_add_le x (-y)).trans (le_of_eq (by rw [coreNorm_neg]))

/-- The letter's norm on a sector: `‖∂ⱼ c‖ ≤ 2√(N+1)·‖c‖` for `c` in `{N ≤ N₀}`. -/
theorem coreNorm_diffHermite_sector_le {j : Fin d} {N : ℕ} (c : CoreCoeff d)
    (hc : ∀ n ∈ c.support, natDeg n ≤ N) :
    coreNorm (diffHermite j c) ≤ 2 * Real.sqrt ((N : ℝ) + 1) * coreNorm c := by
  have hR : (0 : ℝ) ≤ Real.sqrt ((N : ℝ) + 1) := Real.sqrt_nonneg _
  have hstep : ∀ p : Fin d × Bool,
      coreNorm (hopStep p c) ≤ Real.sqrt ((N : ℝ) + 1) * coreNorm c := fun p =>
    coreNorm_hopStep_sector_le p c hc
  have hcoef : ‖(((invSqrtTwo : ℝ) : ℂ))‖ = invSqrtTwo := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg invSqrtTwo_nonneg]
  have h2 : invSqrtTwo * (2 * Real.sqrt ((N : ℝ) + 1)) ≤
      2 * Real.sqrt ((N : ℝ) + 1) := by
    have h1 : invSqrtTwo ≤ 1 := invSqrtTwo_le_one
    nlinarith [hR]
  calc coreNorm (diffHermite j c)
      = coreNorm (((invSqrtTwo : ℝ) : ℂ) •
          (hopStep (j, false) c - hopStep (j, true) c)) := rfl
    _ = invSqrtTwo * coreNorm (hopStep (j, false) c - hopStep (j, true) c) := by
        rw [coreNorm_smul, hcoef]
    _ ≤ invSqrtTwo *
          (coreNorm (hopStep (j, false) c) + coreNorm (hopStep (j, true) c)) := by
        refine mul_le_mul_of_nonneg_left (coreNorm_sub_le _ _) invSqrtTwo_nonneg
    _ ≤ invSqrtTwo * (2 * (Real.sqrt ((N : ℝ) + 1) * coreNorm c)) := by
        refine mul_le_mul_of_nonneg_left ?_ invSqrtTwo_nonneg
        have h1 := hstep (j, false)
        have h2' := hstep (j, true)
        linarith
    _ = (invSqrtTwo * (2 * Real.sqrt ((N : ℝ) + 1))) * coreNorm c := by ring
    _ ≤ (2 * Real.sqrt ((N : ℝ) + 1)) * coreNorm c := by
        refine mul_le_mul_of_nonneg_right h2 (coreNorm_nonneg c)

/-- **`K_drift`'s norm on a sector**, with the constant `driftStepBound`. -/
theorem coreNorm_polyDrift_sector_le (Φ : MvPolynomial (Fin d) ℂ) {N : ℕ} (c : CoreCoeff d)
    (hc : ∀ n ∈ c.support, natDeg n ≤ N) :
    coreNorm (polyDrift Φ c)
      ≤ 2 * Real.sqrt ((N : ℝ) + 1) * gradSectorBound Φ N * coreNorm c := by
  have hR : (0 : ℝ) ≤ Real.sqrt ((N : ℝ) + 1) := Real.sqrt_nonneg _
  have hterm : ∀ j : Fin d,
      coreNorm (polyMul (MvPolynomial.pderiv j Φ) (diffHermite j c))
        ≤ polyMulSectorBound (MvPolynomial.pderiv j Φ)
            (N + 1 + (MvPolynomial.pderiv j Φ).totalDegree)
          * (2 * Real.sqrt ((N : ℝ) + 1) * coreNorm c) := by
    intro j
    refine (polyMul_norm_sector_le (Φ := MvPolynomial.pderiv j Φ) (N := N + 1)
      (M := N + 1 + (MvPolynomial.pderiv j Φ).totalDegree) (by omega)
      (diffHermite j c) (fun m hm => diffHermite_band hc hm)).trans ?_
    refine mul_le_mul_of_nonneg_left (coreNorm_diffHermite_sector_le c hc) ?_
    exact polyMulSectorBound_nonneg _ _
  calc coreNorm (polyDrift Φ c)
      = coreNorm (-∑ j : Fin d, polyMul (MvPolynomial.pderiv j Φ) (diffHermite j c)) := by
        rw [polyDrift]
    _ = coreNorm (∑ j : Fin d, polyMul (MvPolynomial.pderiv j Φ) (diffHermite j c)) := by
        rw [coreNorm_neg]
    _ ≤ ∑ j : Fin d,
          coreNorm (polyMul (MvPolynomial.pderiv j Φ) (diffHermite j c)) :=
        coreNorm_finset_sum_le _ _
    _ ≤ ∑ j : Fin d, polyMulSectorBound (MvPolynomial.pderiv j Φ)
            (N + 1 + (MvPolynomial.pderiv j Φ).totalDegree)
          * (2 * Real.sqrt ((N : ℝ) + 1) * coreNorm c) := Finset.sum_le_sum fun j _ => hterm j
    _ = (∑ j : Fin d, polyMulSectorBound (MvPolynomial.pderiv j Φ)
            (N + 1 + (MvPolynomial.pderiv j Φ).totalDegree))
          * (2 * Real.sqrt ((N : ℝ) + 1) * coreNorm c) := by
        rw [Finset.sum_mul]
    _ = 2 * Real.sqrt ((N : ℝ) + 1) * gradSectorBound Φ N * coreNorm c := by
        rw [gradSectorBound]
        ring

theorem coreNorm_driftOperator_sector_le (β σ : ℝ) (Φ : MvPolynomial (Fin d) ℂ) {N : ℕ}
    (c : CoreCoeff d) (hc : ∀ n ∈ c.support, natDeg n ≤ N) :
    coreNorm (driftOperator β σ Φ c)
      ≤ driftWeight β σ * (2 * Real.sqrt ((N : ℝ) + 1) * gradSectorBound Φ N)
        * coreNorm c := by
  have hcoef : ‖(((driftWeight β σ : ℝ) : ℂ))‖ = driftWeight β σ := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (driftWeight_nonneg β σ)]
  rw [driftOperator, coreNorm_smul, hcoef]
  calc driftWeight β σ * coreNorm (polyDrift Φ c)
      ≤ driftWeight β σ * (2 * Real.sqrt ((N : ℝ) + 1) * gradSectorBound Φ N
          * coreNorm c) :=
        mul_le_mul_of_nonneg_left (coreNorm_polyDrift_sector_le Φ c hc) (driftWeight_nonneg β σ)
    _ = driftWeight β σ * (2 * Real.sqrt ((N : ℝ) + 1) * gradSectorBound Φ N)
          * coreNorm c := by ring

/-- The drift's sector constant in §18's shape. -/
def driftStepBound (β σ : ℝ) (Φ : MvPolynomial (Fin d) ℂ) (N : ℕ) : ℝ :=
  driftWeight β σ * (2 * Real.sqrt ((N : ℝ) + 1) * gradSectorBound Φ N)

theorem driftStepBound_nonneg (β σ : ℝ) (Φ : MvPolynomial (Fin d) ℂ) (N : ℕ) :
    0 ≤ driftStepBound β σ Φ N := by
  rw [driftStepBound]
  exact mul_nonneg (driftWeight_nonneg β σ)
    (mul_nonneg (by positivity) (gradSectorBound_nonneg Φ N))

theorem coreNorm_driftOperator_sector_le' (β σ : ℝ) (Φ : MvPolynomial (Fin d) ℂ) {N : ℕ}
    (c : CoreCoeff d) (hc : ∀ n ∈ c.support, natDeg n ≤ N) :
    coreNorm (driftOperator β σ Φ c) ≤ driftStepBound β σ Φ N * coreNorm c :=
  coreNorm_driftOperator_sector_le β σ Φ c hc

/-! ### 18.3 The plan's `P₀ + K_drift + K_reject` -/

/-- The plan's transition operator `P_pCNL = P₀ + K_drift + K_reject` on the core, with `P₀` the
diagonal `ρ^N` of §18 and `K_reject` the Metropolis filter of §15. -/
def pcnlKernel (ρH : ℝ) (β σ : ℝ) (Φ : MvPolynomial (Fin d) ℂ)
    (ρacc : (Fin d → ℕ) → ℝ) (c : CoreCoeff d) : CoreCoeff d :=
  baseOp ρH c + driftOperator β σ Φ c + rejectOp ρacc c

/-- **The band of the plan's step is the drift's**: `P₀` and `K_reject` are diagonal, so a step
maps `{N ≤ N₀}` into `{N ≤ N₀ + K}` when `deg Φ ≤ K`. -/
theorem pcnlKernel_band {K : ℕ} {Φ : MvPolynomial (Fin d) ℂ} (hK : Φ.totalDegree ≤ K)
    (ρH β σ : ℝ) (ρacc : (Fin d → ℕ) → ℝ) (c : CoreCoeff d) {N : ℕ}
    (hc : ∀ n ∈ c.support, natDeg n ≤ N) {m : Fin d → ℕ}
    (hm : m ∈ (pcnlKernel ρH β σ Φ ρacc c).support) : natDeg m ≤ N + K := by
  classical
  rw [pcnlKernel] at hm
  rcases Finset.mem_union.mp (Finsupp.support_add hm) with h | h
  · rcases Finset.mem_union.mp (Finsupp.support_add h) with h1 | h2
    · exact le_trans (baseOp_band c hc h1) (Nat.le_add_right N K)
    · rw [driftOperator] at h2
      exact polyDrift_band hK c hc (mem_support_smul h2)
  · exact le_trans (rejectOp_band c hc h) (Nat.le_add_right N K)

/-- **The step is a contraction on the non-vacuum sector.**  The diagonal part contributes `ρ^N ≤ ρ`
(§18), the filter `r`, and the drift `driftStepBound β σ Φ N`. -/
theorem coreNorm_pcnlKernel_sector_le {ρH r : ℝ} (β σ : ℝ) {Φ : MvPolynomial (Fin d) ℂ}
    {ρacc : (Fin d → ℕ) → ℝ} {N : ℕ} (hρ0 : 0 ≤ ρH) (hρ1 : ρH ≤ 1)
    (hr : ∀ n, ‖ρacc n‖ ≤ r) (c : CoreCoeff d)
    (hc : ∀ n ∈ c.support, natDeg n ≤ N) (hc1 : ∀ n ∈ c.support, 1 ≤ natDeg n) :
    coreNorm (pcnlKernel ρH β σ Φ ρacc c)
      ≤ (ρH + driftStepBound β σ Φ N + r) * coreNorm c := by
  set D := driftStepBound β σ Φ N with hD
  have hbase := coreNorm_baseOp_sector_le hρ0 hρ1 hc1
  have hdrift := coreNorm_driftOperator_sector_le' β σ Φ c hc
  have hrej := coreNorm_rejectOp_le_of_bound hr c
  have hsum : coreNorm (pcnlKernel ρH β σ Φ ρacc c)
      ≤ ρH * coreNorm c + D * coreNorm c + r * coreNorm c := by
    rw [pcnlKernel]
    exact (coreNorm_add_le _ _).trans (add_le_add ((coreNorm_add_le _ _).trans
      (add_le_add hbase hdrift)) hrej)
  calc coreNorm (pcnlKernel ρH β σ Φ ρacc c)
      ≤ ρH * coreNorm c + D * coreNorm c + r * coreNorm c := hsum
    _ = (ρH + D + r) * coreNorm c := by ring

/-! ## 19. Iterating the step

The band and the norm of the iterates, and the part of the picture that *does* converge.  §19 is
where the pCNL track's remaining gap is stated precisely: `P₀` alone converges to the vacuum at the
plan's rate `ρ`, while the full step's sector constants grow with the level — so a convergence
theorem for `P_pCNL` needs the Markov structure (positivity and `P 1 = 1`) that the core `ℓ²`
model does not carry.
-/

/-! ### 19.1 The iterates' band and norm -/

/-- `n` steps widen the band by `n·K`. -/
theorem pcnlKernel_iter_band {K : ℕ} {Φ : MvPolynomial (Fin d) ℂ} (hK : Φ.totalDegree ≤ K)
    (ρH β σ : ℝ) (ρacc : (Fin d → ℕ) → ℝ) (c : CoreCoeff d) {N : ℕ}
    (hc : ∀ n ∈ c.support, natDeg n ≤ N) :
    ∀ n : ℕ, ∀ m ∈ ((pcnlKernel ρH β σ Φ ρacc)^[n] c).support, natDeg m ≤ N + n * K := by
  intro n
  induction n with
  | zero =>
    intro m hm
    simpa using hc m hm
  | succ n ih =>
    intro m hm
    rw [Function.iterate_succ_apply'] at hm
    have := pcnlKernel_band hK ρH β σ ρacc ((pcnlKernel ρH β σ Φ ρacc)^[n] c)
      (fun m' hm' => ih m' hm') hm
    simpa [Nat.succ_mul, Nat.add_assoc] using this

/-! ### 19.2 `P₀` converges to the invariant state -/

/-- **Geometric decay of `P₀` off the vacuum.**  `n` iterates of `P₀` contract the non-vacuum
sector by `ρⁿ`, so the iterates converge to the unique invariant state `e₀` at rate `ρ` — the
plan's `λ_n = ρⁿ` read on the core. -/
theorem coreNorm_iter_baseOp_le {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) {c : CoreCoeff d}
    (hc : ∀ n ∈ c.support, 1 ≤ natDeg n) (n : ℕ) :
    coreNorm ((baseOp ρ)^[n] c) ≤ ρ ^ n * coreNorm c := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', pow_succ]
    have hsupp : ∀ m ∈ ((baseOp ρ)^[n] c).support, 1 ≤ natDeg m :=
      fun m hm => hc m (support_iter_baseOp ρ c n m hm)
    calc coreNorm (baseOp ρ ((baseOp ρ)^[n] c))
        ≤ ρ * coreNorm ((baseOp ρ)^[n] c) := coreNorm_baseOp_sector_le h0 h1 hsupp
      _ ≤ ρ * (ρ ^ n * coreNorm c) := mul_le_mul_of_nonneg_left ih h0
      _ = ρ ^ n * ρ * coreNorm c := by ring

theorem tendsto_iter_baseOp {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ < 1) {c : CoreCoeff d}
    (hc : ∀ n ∈ c.support, 1 ≤ natDeg n) :
    Filter.Tendsto (fun n : ℕ => coreNorm ((baseOp ρ)^[n] c)) Filter.atTop (nhds 0) := by
  refine squeeze_zero (fun n => coreNorm_nonneg _)
    (fun n => coreNorm_iter_baseOp_le h0 h1.le hc n) ?_
  simpa using (tendsto_pow_atTop_nhds_zero_of_lt_one h0 h1).mul_const (coreNorm c)

/-- The one-step bound without the non-vacuum hypothesis: `P₀` contributes at most `1`. -/
theorem coreNorm_pcnlKernel_le {r : ℝ} (β σ : ℝ) {Φ : MvPolynomial (Fin d) ℂ}
    {ρH : ℝ} {ρacc : (Fin d → ℕ) → ℝ} {N : ℕ} (hρ0 : 0 ≤ ρH) (hρ1 : ρH ≤ 1)
    (hr : ∀ n, ‖ρacc n‖ ≤ r) (c : CoreCoeff d) (hc : ∀ n ∈ c.support, natDeg n ≤ N) :
    coreNorm (pcnlKernel ρH β σ Φ ρacc c)
      ≤ (1 + driftStepBound β σ Φ N + r) * coreNorm c := by
  set D := driftStepBound β σ Φ N with hD
  have hbase := coreNorm_baseOp_le hρ0 hρ1 c
  have hdrift := coreNorm_driftOperator_sector_le' β σ Φ c hc
  have hrej := coreNorm_rejectOp_le_of_bound hr c
  have hsum : coreNorm (pcnlKernel ρH β σ Φ ρacc c)
      ≤ coreNorm c + D * coreNorm c + r * coreNorm c := by
    rw [pcnlKernel]
    exact (coreNorm_add_le _ _).trans (add_le_add ((coreNorm_add_le _ _).trans
      (add_le_add hbase hdrift)) hrej)
  calc coreNorm (pcnlKernel ρH β σ Φ ρacc c)
      ≤ coreNorm c + D * coreNorm c + r * coreNorm c := hsum
    _ = (1 + D + r) * coreNorm c := by ring

/-- **The iterated step's growth bound.**  `n` steps widen the band by `n·K` and multiply the norm
by the product of the level constants; this is the exact shape a convergence theorem would consume.
It cannot decay for a non-constant potential: `driftStepBound β σ Φ N` grows with `N`, so the
product is `≥ (1 + r)^n`. -/
theorem coreNorm_pcnlKernel_iter_le {r : ℝ} (β σ : ℝ) {Φ : MvPolynomial (Fin d) ℂ}
    {K N₀ : ℕ} (hK : Φ.totalDegree ≤ K) {ρH : ℝ} {ρacc : (Fin d → ℕ) → ℝ}
    (hρ0 : 0 ≤ ρH) (hρ1 : ρH ≤ 1) (hr : ∀ n, ‖ρacc n‖ ≤ r) (c : CoreCoeff d)
    (hc : ∀ n ∈ c.support, natDeg n ≤ N₀) (n : ℕ) :
    coreNorm ((pcnlKernel ρH β σ Φ ρacc)^[n] c)
      ≤ (∏ k ∈ Finset.range n, (1 + driftStepBound β σ Φ (N₀ + k * K) + r)) * coreNorm c := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Function.iterate_succ_apply', Finset.prod_range_succ]
    have hsec : ∀ m ∈ ((pcnlKernel ρH β σ Φ ρacc)^[n] c).support,
        natDeg m ≤ N₀ + n * K := pcnlKernel_iter_band hK ρH β σ ρacc c hc n
    have hstep := coreNorm_pcnlKernel_le (Φ := Φ) β σ hρ0 hρ1 hr
      ((pcnlKernel ρH β σ Φ ρacc)^[n] c) hsec
    calc coreNorm (pcnlKernel ρH β σ Φ ρacc ((pcnlKernel ρH β σ Φ ρacc)^[n] c))
        ≤ (1 + driftStepBound β σ Φ (N₀ + n * K) + r)
            * coreNorm ((pcnlKernel ρH β σ Φ ρacc)^[n] c) := hstep
      _ ≤ (1 + driftStepBound β σ Φ (N₀ + n * K) + r)
            * ((∏ k ∈ Finset.range n,
                (1 + driftStepBound β σ Φ (N₀ + k * K) + r)) * coreNorm c) :=
          mul_le_mul_of_nonneg_left ih (by
            have h1 := driftStepBound_nonneg β σ Φ (N₀ + n * K)
            have h2 : (0 : ℝ) ≤ r := le_trans (norm_nonneg _) (hr 0)
            linarith)
      _ = ((∏ k ∈ Finset.range n, (1 + driftStepBound β σ Φ (N₀ + k * K) + r))
            * (1 + driftStepBound β σ Φ (N₀ + n * K) + r)) * coreNorm c := by ring

/-! ## 20. The stochastic split: `P₀ + K_reject = 1`

§19 left one gap in the iteration story: it said a convergence theorem needs the Markov structure
"positivity and `P 1 = 1`" that the core model does not carry.  This section shows the
normalisation is *in* the model — it is what pins the acceptance probability to the complement of
`P₀` — and that what is actually missing is the drift's *sign*, not its normalisation.

* `rejectComplement ρ n = 1 − ρ^{natDeg n}` is the Metropolis complement of `P₀ = ρ^N`; it lies in
  `[0, 1]` for `0 ≤ ρ ≤ 1` (`rejectComplement_nonneg`, `rejectComplement_le_one`).
* **`baseOp_add_rejectOp_complement`**: `P₀ + K_reject = 1`.  The diagonal half of the step is the
  identity, i.e. the normalisation `P 1 = 1` holds exactly, and `pcnlKernel_complement` reads the
  step as `1 + K_drift` — the shape the Markov argument consumes.
* **Positivity**: `re_baseOp_nonneg` and `re_rejectOp_nonneg` — the diagonal half preserves
  nonnegative real parts, so it is a positive operator.
* **The `ℓ¹` side**: `coreL1_baseOp_le` and `coreL1_rejectOp_le` (diagonal parts scale the mass by
  at most their coefficient size), and `coreL1_pcnlKernel_complement_le`: with the normalisation the
  step's `ℓ¹` size is exactly `1 + driftWeight · driftL1Bound`, i.e. the diagonal half contributes
  **no** contraction.

What the `ℓ¹` normalisation therefore rules out is a contraction by *norm*: on the probability
simplex the step is `1 + K_drift`, and only the drift's negative part can remove mass.  A
convergence theorem for `P_pCNL` needs that sign structure — the acceptance/rejection balance at
each occupation — and the norm estimates of §14–§18 cannot supply it.
-/

/-! ### 20.1 The complementary acceptance probability -/

/-- The acceptance probability complementary to `P₀ = ρ^N`: the Metropolis rule's `1 − ρ^N`. -/
def rejectComplement (ρ : ℝ) : (Fin d → ℕ) → ℝ :=
  fun n => 1 - ρ ^ natDeg n

theorem rejectComplement_nonneg {ρ : ℝ} (h0 : 0 ≤ ρ) (h1 : ρ ≤ 1) (n : Fin d → ℕ) :
    0 ≤ rejectComplement ρ n := by
  have h := pow_le_one₀ h0 h1 (n := natDeg n)
  simp only [rejectComplement]
  linarith

theorem rejectComplement_le_one {ρ : ℝ} (h0 : 0 ≤ ρ) (n : Fin d → ℕ) :
    rejectComplement ρ n ≤ 1 := by
  have h := pow_nonneg h0 (natDeg n)
  simp only [rejectComplement]
  linarith

/-- **The accept/reject split is the identity.**  With `ρ_acc = 1 − ρ^N` — the Metropolis
complement of `P₀` — the diagonal half of the step is `P₀ + K_reject = 1`. -/
theorem baseOp_add_rejectOp_complement (ρ : ℝ) (c : CoreCoeff d) :
    baseOp ρ c + rejectOp (rejectComplement ρ) c = c := by
  refine Finsupp.ext fun n => ?_
  rw [Finsupp.add_apply, baseOp_apply, rejectOp_apply, rejectComplement]
  push_cast
  ring

/-- **The normalised step is `1 + K_drift`.**  With the complementary acceptance probability the
pCNL operator's diagonal half cancels, so the step is the identity plus the drift — the shape the
Markov argument needs. -/
theorem pcnlKernel_complement (ρ β σ : ℝ) (Φ : MvPolynomial (Fin d) ℂ) (c : CoreCoeff d) :
    pcnlKernel ρ β σ Φ (rejectComplement ρ) c = c + driftOperator β σ Φ c := by
  rw [pcnlKernel, add_assoc, add_comm (driftOperator β σ Φ c), ← add_assoc,
    baseOp_add_rejectOp_complement]

/-! ### 20.2 Positivity of the diagonal half -/

/-- The diagonal half preserves nonnegative real parts — it is a positive (Markov) operator. -/
theorem re_baseOp_nonneg {ρ : ℝ} (hρ : 0 ≤ ρ) {c : CoreCoeff d}
    (hc : ∀ n, 0 ≤ (c n).re) (n : Fin d → ℕ) : 0 ≤ (baseOp ρ c n).re := by
  have h : (baseOp ρ c n).re = ρ ^ natDeg n * (c n).re := by
    rw [baseOp_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [h]
  exact mul_nonneg (pow_nonneg hρ _) (hc n)

theorem re_rejectOp_nonneg {ρ : (Fin d → ℕ) → ℝ} (hρ : ∀ n, 0 ≤ ρ n) {c : CoreCoeff d}
    (hc : ∀ n, 0 ≤ (c n).re) (n : Fin d → ℕ) : 0 ≤ (rejectOp ρ c n).re := by
  have h : (rejectOp ρ c n).re = ρ n * (c n).re := by
    rw [rejectOp_apply, Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im]
    ring
  rw [h]
  exact mul_nonneg (hρ n) (hc n)

/-! ### 20.3 The `ℓ¹` side: no contraction from the diagonal half -/

/-- Mass over any superset of the support. -/
theorem coreL1_eq_sum {c : CoreCoeff d} {s : Finset (Fin d → ℕ)} (h : c.support ⊆ s) :
    ∑ n ∈ s, ‖c n‖ = coreL1 c :=
  (Finset.sum_subset h fun x _ hx => by
    rw [Finsupp.notMem_support_iff.mp hx]; simp).symm

theorem coreL1_baseOp_le {ρ r : ℝ} {c : CoreCoeff d}
    (h : ∀ n ∈ c.support, ‖ρ ^ natDeg n‖ ≤ r) : coreL1 (baseOp ρ c) ≤ r * coreL1 c := by
  classical
  rw [← coreL1_eq_sum (c := baseOp ρ c) (s := c.support) fun x hx => mem_support_baseOp hx]
  calc ∑ n ∈ c.support, ‖baseOp ρ c n‖
      = ∑ n ∈ c.support, ‖ρ ^ natDeg n‖ * ‖c n‖ := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [baseOp_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ n ∈ c.support, r * ‖c n‖ :=
        Finset.sum_le_sum fun n hn => mul_le_mul_of_nonneg_right (h n hn) (norm_nonneg _)
    _ = r * coreL1 c := by rw [coreL1, Finset.mul_sum]

theorem coreL1_rejectOp_le {ρ : (Fin d → ℕ) → ℝ} {r : ℝ} (hr : ∀ n, ‖ρ n‖ ≤ r)
    (c : CoreCoeff d) : coreL1 (rejectOp ρ c) ≤ r * coreL1 c := by
  classical
  rw [← coreL1_eq_sum (c := rejectOp ρ c) (s := c.support) fun x hx => mem_support_rejectOp hx]
  calc ∑ n ∈ c.support, ‖rejectOp ρ c n‖
      = ∑ n ∈ c.support, ‖ρ n‖ * ‖c n‖ := by
        refine Finset.sum_congr rfl fun n _ => ?_
        rw [rejectOp_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs]
    _ ≤ ∑ n ∈ c.support, r * ‖c n‖ :=
        Finset.sum_le_sum fun n _ => mul_le_mul_of_nonneg_right (hr n) (norm_nonneg _)
    _ = r * coreL1 c := by rw [coreL1, Finset.mul_sum]

/-- **The normalised step does not contract the `ℓ¹` mass.**  With `P₀ + K_reject = 1` the only
factor is the drift: on a sector the iterated step's `ℓ¹` size is `1 + driftL1Bound`.  This is the
precise sense in which the stochastic normalisation rules out a *norm* contraction: what remains to
be used is the drift's sign (its negative part), not its size. -/
theorem coreL1_pcnlKernel_complement_le (β σ : ℝ) {Φ : MvPolynomial (Fin d) ℂ} {N M : ℕ}
    (hNM : N + Φ.totalDegree + 1 ≤ M) {ρ : ℝ} (c : CoreCoeff d)
    (hc : ∀ n ∈ c.support, natDeg n ≤ N) :
    coreL1 (pcnlKernel ρ β σ Φ (rejectComplement ρ) c)
      ≤ (1 + driftWeight β σ * driftL1Bound Φ M) * coreL1 c := by
  rw [pcnlKernel_complement]
  have hdrift : coreL1 (driftOperator β σ Φ c)
      ≤ driftWeight β σ * driftL1Bound Φ M * coreL1 c := by
    rw [driftOperator]
    refine (coreL1_smul_le _ _).trans ?_
    have h := polyDrift_l1_le (Φ := Φ) hNM c hc
    have hw : (0 : ℝ) ≤ driftWeight β σ * coreL1 c :=
      mul_nonneg (driftWeight_nonneg β σ) (coreL1_nonneg c)
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (driftWeight_nonneg β σ)]
    calc driftWeight β σ * coreL1 (polyDrift Φ c)
        ≤ driftWeight β σ * (driftL1Bound Φ M * coreL1 c) :=
          mul_le_mul_of_nonneg_left h (driftWeight_nonneg β σ)
      _ = driftWeight β σ * driftL1Bound Φ M * coreL1 c := by ring
  calc coreL1 (c + driftOperator β σ Φ c)
      ≤ coreL1 c + coreL1 (driftOperator β σ Φ c) := coreL1_add_le _ _
    _ ≤ coreL1 c + driftWeight β σ * driftL1Bound Φ M * coreL1 c :=
        add_le_add le_rfl hdrift
    _ = (1 + driftWeight β σ * driftL1Bound Φ M) * coreL1 c := by ring

/-! ## 21. The drift's sign against the flat `ℓ¹` measure

§20 sharpened the remaining gap to a *sign*: on the normalised step `1 + K_drift` the only way mass
leaves is through the drift's negative part, and the norm estimates of §14–§18 bound `K_drift` from
above, so they cannot see it.  This section computes that sign on the core's basis vectors and finds
there is none to use.

* **The linear potential's drift is a ladder letter**: `polyDrift_X` gives
  `polyDrift (Xⱼ) c = −∂ⱼc` and `driftOperator_X` reads it as `w·(aⱼ − aⱼ†)c` with
  `w = (β²σ²/2)·2⁻¹ᐟ²`.
* **On a basis vector it raises the `ℓ¹` mass**, and by an explicit amount:
  `drift_X_single_eq` (the image is the two-term vector
  `w√(nⱼ+1) e_{n+eⱼ} − w√(nⱼ) e_{n−eⱼ}`) and `coreL1_single_lt_add_drift_X`, whose value
  `1 + (β²σ²/2)·2⁻¹ᐟ²·(√(nⱼ+1) + √(nⱼ))` is computed by
  `coreL1_single_add_sub_single_of_ne` from the pairwise disjointness of the three occupation
  vectors.

So the drift's pairing with the flat `ℓ¹` measure is *positive* at every basis vector: there is no
state at which `ℓ¹` mass is destroyed, and the strict contraction §20 identified as the missing
ingredient cannot come from the drift's sign on this model.  The pair `(K_drift, ℓ¹)` is not a
dissipative pair; what is missing is a *weighted* `ℓ¹` (one the drift contracts), and the cone model
of `BookProof.MCMC.PositivityCone` (§22) is where that structure is supplied.
-/

/-! ## §21 The drift's sign against the flat ℓ¹ measure -/

/-- The drift of the linear potential `Φ = Xⱼ` is `−∂ⱼ`: `∂ₖ Xⱼ = δₖⱼ` and `polyMul 1 = id`. -/
theorem polyDrift_X (j : Fin d) (c : CoreCoeff d) :
    polyDrift (MvPolynomial.X j) c = -diffHermite j c := by
  classical
  rw [polyDrift, Finset.sum_eq_single j]
  · rw [MvPolynomial.pderiv_X_self, polyMul_one]
  · intro k _ hne
    have hzero : (Pi.single k (1 : MvPolynomial (Fin d) ℂ) : Fin d → MvPolynomial (Fin d) ℂ) j
        = 0 := by
      rw [Pi.single_eq_of_ne (Ne.symm hne)]
    rw [MvPolynomial.pderiv_X, hzero]
    simp [polyMul]
  · intro hj
    exact absurd (Finset.mem_univ j) hj

/-- The drift operator of a linear potential, in ladder letters. -/
theorem driftOperator_X (β σ : ℝ) (j : Fin d) (c : CoreCoeff d) :
    driftOperator β σ (MvPolynomial.X j) c
      = ((driftWeight β σ * invSqrtTwo : ℝ) : ℂ) •
          (hopStep (j, true) c - hopStep (j, false) c) := by
  rw [driftOperator, polyDrift_X, smul_neg, diffHermite, smul_smul, ← Complex.ofReal_mul,
    ← smul_neg, neg_sub]

theorem raiseIdx_ne_self (j : Fin d) (n : Fin d → ℕ) : raiseIdx j n ≠ n := by
  intro h
  have h1 := congrFun h j
  rw [raiseIdx_apply_same] at h1
  omega

theorem lowerIdx_ne_self {j : Fin d} {n : Fin d → ℕ} (hn : 0 < n j) : lowerIdx j n ≠ n := by
  intro h
  have h1 := congrFun h j
  rw [lowerIdx_apply_same] at h1
  omega

theorem invSqrtTwo_pos : (0 : ℝ) < invSqrtTwo := by
  rw [invSqrtTwo]
  positivity

/-- The raising half of the letter is orthogonal to the state it came from. -/
theorem corePair_single_hopStep_raise (j : Fin d) (n : Fin d → ℕ) :
    corePair (Finsupp.single n 1) (hopStep (j, true) (Finsupp.single n 1)) = 0 := by
  have hraise : hopStep (j, true) (Finsupp.single n 1)
      = Finsupp.single (raiseIdx j n) (((Real.sqrt ((n j : ℝ) + 1) : ℝ) : ℂ)) := by
    rw [hopStep_single, stepAmp_raise, stepIdx]
    simp
  rw [hraise, corePair_single_single, if_neg (raiseIdx_ne_self j n).symm]

/-- The lowering half is orthogonal too — and vanishes outright at a saturated mode. -/
theorem corePair_single_hopStep_lower (j : Fin d) (n : Fin d → ℕ) :
    corePair (Finsupp.single n 1) (hopStep (j, false) (Finsupp.single n 1)) = 0 := by
  have hlower : hopStep (j, false) (Finsupp.single n 1)
      = Finsupp.single (lowerIdx j n) (((Real.sqrt (n j : ℝ) : ℝ) : ℂ)) := by
    rw [hopStep_single, stepAmp_lower, stepIdx]
    simp
  rw [hlower]
  by_cases hn : n j = 0
  · have hz : ((Real.sqrt (n j : ℝ) : ℝ) : ℂ) = 0 := by
      rw [hn]
      simp
    rw [hz, Finsupp.single_zero, corePair_zero_right]
  · rw [corePair_single_single, if_neg (lowerIdx_ne_self (by omega)).symm]

/-- **The drift is mass-neutral against the state** (`ℓ²` pairing): on a basis vector both ladder
images live at other occupations, so `⟪eₙ, K_drift eₙ⟫ = 0`. -/
theorem corePair_drift_X_single (β σ : ℝ) (j : Fin d) (n : Fin d → ℕ) :
    corePair (Finsupp.single n 1) (driftOperator β σ (MvPolynomial.X j)
      (Finsupp.single n 1)) = 0 := by
  have hstar : star (((driftWeight β σ * invSqrtTwo : ℝ)) : ℂ)
      = (((driftWeight β σ * invSqrtTwo : ℝ)) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  rw [driftOperator_X, corePair_smul, hstar, corePair_sub,
    corePair_single_hopStep_raise, corePair_single_hopStep_lower, sub_zero, mul_zero]

/-- `coreL1` of a basis vector. -/
theorem coreL1_single (m : Fin d → ℕ) (a : ℂ) :
    coreL1 (Finsupp.single m a) = ‖a‖ := by
  classical
  rw [coreL1, Finset.sum_subset Finsupp.support_single_subset (fun x hx hx' => ?_)]
  · simp
  · rw [Finsupp.notMem_support_iff.mp hx', norm_zero]

/-- `coreL1` is additive on states with disjoint supports. -/
theorem coreL1_add_of_disjoint {x y : CoreCoeff d}
    (h : Disjoint x.support y.support) : coreL1 (x + y) = coreL1 x + coreL1 y := by
  classical
  have h1 : ∑ n ∈ (x + y).support, ‖(x + y) n‖
      = ∑ n ∈ x.support ∪ y.support, ‖(x + y) n‖ := by
    refine Finset.sum_subset Finsupp.support_add (fun z _ hz => ?_)
    rw [Finsupp.notMem_support_iff.mp hz, norm_zero]
  rw [coreL1, coreL1, coreL1, h1, Finset.sum_union h]
  congr 1
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finsupp.add_apply, Finsupp.notMem_support_iff.mp (Finset.disjoint_left.mp h hn),
      add_zero]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finsupp.add_apply, Finsupp.notMem_support_iff.mp (Finset.disjoint_right.mp h hn),
      zero_add]

theorem disjoint_single_single {m n : Fin d → ℕ} (h : m ≠ n) (a b : ℂ) :
    Disjoint (Finsupp.single m a).support (Finsupp.single n b).support := by
  refine Finset.disjoint_left.mpr fun x hx hy => ?_
  have hx' : x = m := by simpa using Finsupp.support_single_subset hx
  have hy' : x = n := by simpa using Finsupp.support_single_subset hy
  exact h (hx'.symm.trans hy')

theorem coreL1_single_add_single_of_ne {m n : Fin d → ℕ} (h : m ≠ n) (a b : ℂ) :
    coreL1 (Finsupp.single m a + Finsupp.single n b) = ‖a‖ + ‖b‖ := by
  rw [coreL1_add_of_disjoint (disjoint_single_single h a b), coreL1_single, coreL1_single]

theorem coreL1_single_sub_single_of_ne {m n : Fin d → ℕ} (h : m ≠ n) (a b : ℂ) :
    coreL1 (Finsupp.single m a - Finsupp.single n b) = ‖a‖ + ‖b‖ := by
  rw [sub_eq_add_neg, ← Finsupp.single_neg, coreL1_single_add_single_of_ne h, norm_neg]

/-- **The drift's action on a basis vector**, with the two ladder images at distinct occupations. -/
theorem drift_X_single_eq {β σ : ℝ} {j : Fin d} {n : Fin d → ℕ} (_hn : 0 < n j) :
    driftOperator β σ (MvPolynomial.X j) (Finsupp.single n 1)
      = ((driftWeight β σ * invSqrtTwo : ℝ) : ℂ) •
          (Finsupp.single (raiseIdx j n)
              (((Real.sqrt ((n j : ℝ) + 1) : ℝ) : ℂ))
            - Finsupp.single (lowerIdx j n) (((Real.sqrt (n j : ℝ) : ℝ) : ℂ))) := by
  rw [driftOperator_X, hopStep_single, hopStep_single, stepAmp_raise, stepAmp_lower, stepIdx,
    stepIdx]
  simp

/-- **The drift raises the flat `ℓ¹` mass.**  On a basis vector the linear potential's drift adds
`(β²σ²/2)·2⁻¹ᐟ²·(√(nⱼ+1) + √(nⱼ))` to the mass — it never removes any.  So there is no state at
which the drift's pairing with the flat `ℓ¹` measure is negative: the strict contraction §20 asks
for cannot come from this sign. -/
theorem coreL1_single_add_sub_single_of_ne {m k l : Fin d → ℕ} (hmk : m ≠ k) (hml : m ≠ l)
    (hkl : k ≠ l) (a b c : ℂ) :
    coreL1 (Finsupp.single m a + (Finsupp.single k b - Finsupp.single l c))
      = ‖a‖ + ‖b‖ + ‖c‖ := by
  have h1 : Finsupp.single k b - Finsupp.single l c
      = Finsupp.single k b + Finsupp.single l (-c) := by
    rw [sub_eq_add_neg, ← Finsupp.single_neg]
  have hdisj : Disjoint (Finsupp.single m a + Finsupp.single k b).support
      (Finsupp.single l (-c)).support := by
    refine Finset.disjoint_left.mpr fun x hx hy => ?_
    have hy' : x = l := by simpa using Finsupp.support_single_subset hy
    rcases Finset.mem_union.mp (Finsupp.support_add hx) with hx1 | hx1
    · have hx2 : x = m := by simpa using Finsupp.support_single_subset hx1
      exact hml (hx2.symm.trans hy')
    · have hx2 : x = k := by simpa using Finsupp.support_single_subset hx1
      exact hkl (hx2.symm.trans hy')
  rw [h1, ← add_assoc, coreL1_add_of_disjoint hdisj,
    coreL1_single_add_single_of_ne hmk a b, coreL1_single, norm_neg]

/-- **The drift raises the flat `ℓ¹` mass.**  On a basis vector the linear potential's drift adds
`(β²σ²/2)·2⁻¹ᐟ²·(√(nⱼ+1) + √(nⱼ))` to the mass — it never removes any.  So there is no state at
which the drift's pairing with the flat `ℓ¹` measure is negative: the strict contraction §20 asks
for cannot come from this sign. -/
theorem coreL1_single_lt_add_drift_X (β σ : ℝ) (j : Fin d) (n : Fin d → ℕ) (hn : 1 ≤ n j)
    (hw : 0 < driftWeight β σ) :
    coreL1 (Finsupp.single n 1)
      < coreL1 (Finsupp.single n 1 + driftOperator β σ (MvPolynomial.X j)
          (Finsupp.single n 1)) := by
  have hn0 : 0 < n j := hn
  have hw0 : ‖((driftWeight β σ * invSqrtTwo : ℝ) : ℂ)‖ = driftWeight β σ * invSqrtTwo := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (driftWeight_nonneg β σ) invSqrtTwo_nonneg)]
  have hs1 : ‖((Real.sqrt ((n j : ℝ) + 1) : ℝ) : ℂ)‖ = Real.sqrt ((n j : ℝ) + 1) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hs2 : ‖((Real.sqrt (n j : ℝ) : ℝ) : ℂ)‖ = Real.sqrt (n j : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hmain : coreL1 (Finsupp.single n 1 + driftOperator β σ (MvPolynomial.X j)
        (Finsupp.single n 1))
      = 1 + driftWeight β σ * invSqrtTwo
          * (Real.sqrt ((n j : ℝ) + 1) + Real.sqrt (n j : ℝ)) := by
    rw [drift_X_single_eq hn0, smul_sub, Finsupp.smul_single, Finsupp.smul_single]
    simp only [smul_eq_mul]
    rw [coreL1_single_add_sub_single_of_ne (raiseIdx_ne_self j n).symm
        (lowerIdx_ne_self hn0).symm (raiseIdx_ne_lowerIdx j n) 1,
      norm_mul, hw0, hs1, norm_mul, hw0, hs2, norm_one]
    ring
  rw [hmain, coreL1_single, norm_one]
  have hpos : 0 < invSqrtTwo * (Real.sqrt ((n j : ℝ) + 1) + Real.sqrt (n j : ℝ)) := by
    have h1 : 0 < Real.sqrt ((n j : ℝ) + 1) := Real.sqrt_pos.mpr (by positivity)
    have h2 : 0 ≤ Real.sqrt (n j : ℝ) := Real.sqrt_nonneg _
    nlinarith [invSqrtTwo_pos]
  nlinarith [hw, hpos]


/-! ## 21.5 The weighted `ℓ¹`: what the diagonal cancels, the drift breaks

§20–§21 left one candidate open: a *weighted* `ℓ¹` in which the drift term becomes a contraction.
This section closes it in both directions.

* `coreW1 w c = ∑ₙ w n · ‖c n‖`, the weighted mass (`coreW1_single`, `coreW1_add_of_disjoint`,
  `coreW1_single_add_sub_single_of_ne`, and `coreW1_one`: the flat §9.9 mass is the `w ≡ 1`
  instance);
* **`coreW1_baseOp`** — the diagonal acts on the weight as `w ↦ w·ρ^{natDeg n}`, so with
  `wInv ρ n = (ρ^{natDeg n})⁻¹` the diagonal cancels exactly (**`coreW1_baseOp_wInv`**:
  `coreW1 (wInv ρ) (P₀ c) = coreL1 c`), and `coreL1_le_coreW1_wInv` says the flat mass is the
  smaller one in that weight.  This is the norm a Markov argument would choose;
* **`coreW1_single_lt_add_drift_X`** — the drift breaks it: on a basis vector the two ladder
  images sit off `n` and enter the weighted sum with strictly positive coefficients, while the
  source term `w n` is untouched, so the weighted mass grows for *every* weight;
  **`coreW1_wInv_add_drift_X`** computes the excess in the cancelling weight,
  `wInv ρ n · (1 + q(√(nⱼ+1)/ρ + ρ√(nⱼ)))` with `q = (β²σ²/2)/√2`, and `natDeg_lowerIdx` is the
  degree bookkeeping behind it;
* **`no_weighted_nonexpansive`** — hence no strictly positive weight makes the normalised step
  `1 + K_drift` nonexpansive (`exists_coreW1_lt_pcnlKernel`).  The strict decay §20 asked the
  drift's sign for cannot be recovered by reweighting; the convergence theorem comes from the
  stochastic structure (§20's positivity and `P 1 = 1`, and `PositivityCone`'s Doeblin minorant)
  or from the form bound, not from a norm.
-/

/-- The weighted `ℓ¹` mass of a core state: `coreL1` with the coefficients weighted by `w`. -/
def coreW1 (w : (Fin d → ℕ) → ℝ) (c : CoreCoeff d) : ℝ :=
  ∑ n ∈ c.support, w n * ‖c n‖

theorem coreW1_nonneg {w : (Fin d → ℕ) → ℝ} (hw : ∀ n, 0 ≤ w n) (c : CoreCoeff d) :
    0 ≤ coreW1 w c :=
  Finset.sum_nonneg fun _ _ => mul_nonneg (hw _) (norm_nonneg _)

/-- The flat weight recovers `coreL1`. -/
theorem coreW1_one (c : CoreCoeff d) : coreW1 (fun _ => 1) c = coreL1 c := by
  rw [coreW1, coreL1]
  exact Finset.sum_congr rfl fun _ _ => one_mul _

theorem coreW1_eq_sum {w : (Fin d → ℕ) → ℝ} {c : CoreCoeff d}
    {s : Finset (Fin d → ℕ)} (h : c.support ⊆ s) : ∑ n ∈ s, w n * ‖c n‖ = coreW1 w c :=
  (Finset.sum_subset h fun x _ hx => by
    rw [Finsupp.notMem_support_iff.mp hx]; simp).symm

theorem coreW1_single (w : (Fin d → ℕ) → ℝ) (m : Fin d → ℕ) (a : ℂ) :
    coreW1 w (Finsupp.single m a) = w m * ‖a‖ := by
  classical
  rw [coreW1, Finset.sum_subset Finsupp.support_single_subset (fun x _ hx => ?_)]
  · simp
  · rw [Finsupp.notMem_support_iff.mp hx, norm_zero, mul_zero]

theorem coreW1_add_of_disjoint {w : (Fin d → ℕ) → ℝ} {x y : CoreCoeff d}
    (h : Disjoint x.support y.support) : coreW1 w (x + y) = coreW1 w x + coreW1 w y := by
  classical
  have hzero : ∀ (z : CoreCoeff d) {n : Fin d → ℕ}, n ∉ z.support → z n = 0 :=
    fun z _ hn => Finsupp.notMem_support_iff.mp hn
  have h1 : ∑ n ∈ (x + y).support, w n * ‖(x + y) n‖
      = ∑ n ∈ x.support ∪ y.support, w n * ‖(x + y) n‖ := by
    refine Finset.sum_subset Finsupp.support_add (fun z _ hz => ?_)
    rw [Finsupp.notMem_support_iff.mp hz, norm_zero, mul_zero]
  rw [coreW1, coreW1, coreW1, h1, Finset.sum_union h]
  congr 1
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finsupp.add_apply, Finsupp.notMem_support_iff.mp (Finset.disjoint_left.mp h hn),
      add_zero]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [Finsupp.add_apply, Finsupp.notMem_support_iff.mp (Finset.disjoint_right.mp h hn),
      zero_add]

theorem coreW1_single_add_single_of_ne {w : (Fin d → ℕ) → ℝ} {m n : Fin d → ℕ} (h : m ≠ n)
    (a b : ℂ) : coreW1 w (Finsupp.single m a + Finsupp.single n b) = w m * ‖a‖ + w n * ‖b‖ := by
  rw [coreW1_add_of_disjoint (disjoint_single_single h a b), coreW1_single, coreW1_single]

theorem coreW1_single_sub_single_of_ne {w : (Fin d → ℕ) → ℝ} {m n : Fin d → ℕ} (h : m ≠ n)
    (a b : ℂ) : coreW1 w (Finsupp.single m a - Finsupp.single n b) = w m * ‖a‖ + w n * ‖b‖ := by
  rw [sub_eq_add_neg, ← Finsupp.single_neg, coreW1_single_add_single_of_ne h, norm_neg]

theorem coreW1_single_add_sub_single_of_ne {w : (Fin d → ℕ) → ℝ} {m k l : Fin d → ℕ}
    (hmk : m ≠ k) (hml : m ≠ l) (hkl : k ≠ l) (a b c : ℂ) :
    coreW1 w (Finsupp.single m a + (Finsupp.single k b - Finsupp.single l c))
      = w m * ‖a‖ + w k * ‖b‖ + w l * ‖c‖ := by
  have h1 : Finsupp.single k b - Finsupp.single l c
      = Finsupp.single k b + Finsupp.single l (-c) := by
    rw [sub_eq_add_neg, ← Finsupp.single_neg]
  have hdisj : Disjoint (Finsupp.single m a + Finsupp.single k b).support
      (Finsupp.single l (-c)).support := by
    refine Finset.disjoint_left.mpr fun x hx hy => ?_
    have hy' : x = l := by simpa using Finsupp.support_single_subset hy
    rcases Finset.mem_union.mp (Finsupp.support_add hx) with hx1 | hx1
    · have hx2 : x = m := by simpa using Finsupp.support_single_subset hx1
      exact hml (hx2.symm.trans hy')
    · have hx2 : x = k := by simpa using Finsupp.support_single_subset hx1
      exact hkl (hx2.symm.trans hy')
  rw [h1, ← add_assoc, coreW1_add_of_disjoint hdisj,
    coreW1_single_add_single_of_ne hmk a b, coreW1_single, norm_neg]

/-- **The diagonal computed in a weight**: `coreW1 w (P₀ c)` is the mass of `c` under the weight
`w n · ρ^{natDeg n}`. -/
theorem coreW1_baseOp {ρ : ℝ} (hρ : 0 ≤ ρ) (w : (Fin d → ℕ) → ℝ) (c : CoreCoeff d) :
    coreW1 w (baseOp ρ c) = coreW1 (fun n => w n * ρ ^ natDeg n) c := by
  classical
  rw [← coreW1_eq_sum (c := baseOp ρ c) (s := c.support) fun x hx => mem_support_baseOp hx]
  rw [coreW1]
  refine Finset.sum_congr rfl fun n _ => ?_
  rw [baseOp_apply, norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (pow_nonneg hρ _)]
  ring

/-- The weight that cancels the diagonal: `(ρ^{natDeg n})⁻¹`. -/
def wInv (ρ : ℝ) (n : Fin d → ℕ) : ℝ := (ρ ^ natDeg n)⁻¹

theorem wInv_pos {ρ : ℝ} (hρ : 0 < ρ) (n : Fin d → ℕ) : 0 < wInv ρ n := by
  rw [wInv]
  exact inv_pos.mpr (pow_pos hρ _)

/-- **The weight `wInv ρ` cancels the diagonal exactly**: in it, `P₀`'s weighted mass is the *flat*
mass of the source, `∑ₙ ‖c n‖`.  This is the norm in which the diagonal `ρ^N` costs nothing — the
weight a Markov argument would choose. -/
theorem coreW1_baseOp_wInv {ρ : ℝ} (hρ : 0 < ρ) (c : CoreCoeff d) :
    coreW1 (wInv ρ) (baseOp ρ c) = coreL1 c := by
  rw [coreW1_baseOp (le_of_lt hρ), ← coreW1_one]
  refine Finset.sum_congr rfl fun n _ => ?_
  simp only [wInv]
  rw [inv_mul_cancel₀ (ne_of_gt (pow_pos hρ _)), one_mul]

/-- In the cancelling weight the flat mass is the smaller one: `wInv ρ n ≥ 1` for `ρ ≤ 1`. -/
theorem coreL1_le_coreW1_wInv {ρ : ℝ} (hρ0 : 0 < ρ) (hρ1 : ρ ≤ 1) (c : CoreCoeff d) :
    coreL1 c ≤ coreW1 (wInv ρ) c := by
  rw [coreL1, coreW1]
  refine Finset.sum_le_sum fun n _ => ?_
  have h1 : (1 : ℝ) ≤ wInv ρ n := by
    rw [wInv, one_le_inv₀ (pow_pos hρ0 _)]
    exact pow_le_one₀ (le_of_lt hρ0) hρ1
  calc ‖c n‖ = 1 * ‖c n‖ := (one_mul _).symm
    _ ≤ wInv ρ n * ‖c n‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)

/-- **The drift raises every weighted `ℓ¹` mass**, not just the flat one: on a basis vector the
two ladder images sit off `n` and enter the weighted sum with positive coefficients, while the
source term itself is unchanged. -/
theorem coreW1_single_lt_add_drift_X {β σ : ℝ} {j : Fin d} {n : Fin d → ℕ}
    (w : (Fin d → ℕ) → ℝ) (hw : ∀ m, 0 < w m) (hn : 1 ≤ n j)
    (hD : 0 < driftWeight β σ) :
    coreW1 w (Finsupp.single n 1)
      < coreW1 w (Finsupp.single n 1 + driftOperator β σ (MvPolynomial.X j)
          (Finsupp.single n 1)) := by
  have hn0 : 0 < n j := hn
  set q : ℝ := driftWeight β σ * invSqrtTwo with hq
  have hqpos : 0 < q := by rw [hq]; exact mul_pos hD invSqrtTwo_pos
  have hqnorm : ‖(((driftWeight β σ * invSqrtTwo : ℝ)) : ℂ)‖ = q := by
    rw [hq, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (le_of_lt hqpos)]
  have hA : ‖(((Real.sqrt ((n j : ℝ) + 1) : ℝ) : ℂ))‖ = Real.sqrt ((n j : ℝ) + 1) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hB : ‖(((Real.sqrt (n j : ℝ) : ℝ) : ℂ))‖ = Real.sqrt (n j : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hmain : coreW1 w (Finsupp.single n 1 + driftOperator β σ (MvPolynomial.X j)
        (Finsupp.single n 1))
      = w n * 1 + w (raiseIdx j n) * (q * Real.sqrt ((n j : ℝ) + 1))
        + w (lowerIdx j n) * (q * Real.sqrt (n j : ℝ)) := by
    rw [drift_X_single_eq hn0, smul_sub, Finsupp.smul_single, Finsupp.smul_single]
    simp only [smul_eq_mul]
    rw [coreW1_single_add_sub_single_of_ne (raiseIdx_ne_self j n).symm
      (lowerIdx_ne_self hn0).symm (raiseIdx_ne_lowerIdx j n) 1]
    rw [norm_one, norm_mul, norm_mul, hqnorm, hA, hB]
  rw [hmain, coreW1_single, norm_one]
  have hp1 : 0 < w (raiseIdx j n) * (q * Real.sqrt ((n j : ℝ) + 1)) :=
    mul_pos (hw _) (mul_pos hqpos (Real.sqrt_pos.mpr (by positivity)))
  have hp2 : 0 < w (lowerIdx j n) * (q * Real.sqrt (n j : ℝ)) :=
    mul_pos (hw _) (mul_pos hqpos (Real.sqrt_pos.mpr (by positivity)))
  nlinarith [hw n]

/-- The total degree after annihilation is one less. -/
theorem natDeg_lowerIdx {j : Fin d} {n : Fin d → ℕ} (hn : 1 ≤ n j) :
    natDeg (lowerIdx j n) = natDeg n - 1 := by
  have h1 := sum_erase n j
  have h2 := sum_erase (Function.update n j (n j - 1)) j
  have h3 := sum_erase_update n j (n j - 1)
  have h4 : Function.update n j (n j - 1) j = n j - 1 := by simp
  unfold natDeg lowerIdx
  omega

/-- **The excess, computed in the cancelling weight.**  In the weight `wInv ρ` that removes the
diagonal, the drift's two images weigh `ρ⁻¹` and `ρ` times the source weight, so the step's
weighted mass is `wInv ρ n · (1 + q(√(nⱼ+1)/ρ + ρ√(nⱼ)))` with `q = (β²σ²/2)/√2` — strictly more
than the source, by that explicit factor. -/
theorem coreW1_wInv_add_drift_X {β σ ρ : ℝ} (hρ : 0 < ρ) {j : Fin d} {n : Fin d → ℕ}
    (hn : 1 ≤ n j) :
    coreW1 (wInv ρ) (Finsupp.single n 1 + driftOperator β σ (MvPolynomial.X j)
        (Finsupp.single n 1))
      = wInv ρ n * (1 + driftWeight β σ * invSqrtTwo *
          (ρ⁻¹ * Real.sqrt ((n j : ℝ) + 1) + ρ * Real.sqrt (n j : ℝ))) := by
  have hn0 : 0 < n j := hn
  have hN : 1 ≤ natDeg n := le_trans hn (Finset.single_le_sum (f := n)
    (fun i _ => Nat.zero_le _) (Finset.mem_univ j))
  have hqnorm : ‖(((driftWeight β σ * invSqrtTwo : ℝ)) : ℂ)‖
      = driftWeight β σ * invSqrtTwo := by
    rw [Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg (driftWeight_nonneg β σ) invSqrtTwo_nonneg)]
  have hA : ‖(((Real.sqrt ((n j : ℝ) + 1) : ℝ) : ℂ))‖ = Real.sqrt ((n j : ℝ) + 1) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hB : ‖(((Real.sqrt (n j : ℝ) : ℝ) : ℂ))‖ = Real.sqrt (n j : ℝ) := by
    rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (Real.sqrt_nonneg _)]
  have hraise : wInv ρ (raiseIdx j n) = ρ⁻¹ * wInv ρ n := by
    rw [wInv, wInv, natDeg_raiseIdx, pow_succ, mul_inv_rev]
  have hpow : ρ ^ natDeg n = ρ ^ (natDeg n - 1) * ρ := by
    rw [← pow_succ, Nat.sub_add_cancel hN]
  have hlower : ρ * wInv ρ n = wInv ρ (lowerIdx j n) := by
    rw [wInv, wInv, natDeg_lowerIdx hn, hpow, mul_inv_rev, ← mul_assoc,
      mul_inv_cancel₀ (ne_of_gt hρ), one_mul]
  have hmain : coreW1 (wInv ρ) (Finsupp.single n 1 + driftOperator β σ (MvPolynomial.X j)
        (Finsupp.single n 1))
      = wInv ρ n * 1 + wInv ρ (raiseIdx j n) * (driftWeight β σ * invSqrtTwo
          * Real.sqrt ((n j : ℝ) + 1))
        + wInv ρ (lowerIdx j n) * (driftWeight β σ * invSqrtTwo * Real.sqrt (n j : ℝ)) := by
    rw [drift_X_single_eq hn0, smul_sub, Finsupp.smul_single, Finsupp.smul_single]
    simp only [smul_eq_mul]
    rw [coreW1_single_add_sub_single_of_ne (raiseIdx_ne_self j n).symm
      (lowerIdx_ne_self hn0).symm (raiseIdx_ne_lowerIdx j n) 1]
    rw [norm_one, norm_mul, norm_mul, hqnorm, hA, hB]
  rw [hmain, hraise, ← hlower]
  ring

/-- **The failure is not a choice of norm.**  For every strictly positive weight there is a state
whose weighted mass the normalised step *increases* — the input to `no_weighted_nonexpansive`. -/
theorem exists_coreW1_lt_pcnlKernel {ρ β σ : ℝ} (j : Fin d) (w : (Fin d → ℕ) → ℝ)
    (hw : ∀ m, 0 < w m) (hD : 0 < driftWeight β σ) :
    ∃ c : CoreCoeff d, coreW1 w c
      < coreW1 w (pcnlKernel ρ β σ (MvPolynomial.X j) (rejectComplement ρ) c) := by
  refine ⟨Finsupp.single (Function.update (0 : Fin d → ℕ) j 1) 1, ?_⟩
  rw [pcnlKernel_complement]
  exact coreW1_single_lt_add_drift_X w hw (by simp) hD

/-- **The weighted `ℓ¹` route is closed.**  The normalised pCNL step `1 + K_drift` is not
nonexpansive in *any* strictly positive weight, so there is no weighted `ℓ¹` in which the step is a
contraction — the strict decay §20 asked the drift's sign for cannot be recovered by reweighting.
The convergence theorem has to come from the stochastic structure (positivity, `P 1 = 1`, the
Doeblin minorant of the cone model) or from the form bound, not from a norm. -/
theorem no_weighted_nonexpansive {ρ β σ : ℝ} (j : Fin d) (hD : 0 < driftWeight β σ) :
    ¬ ∃ w : (Fin d → ℕ) → ℝ, (∀ m, 0 < w m) ∧ ∀ c : CoreCoeff d,
      coreW1 w (pcnlKernel ρ β σ (MvPolynomial.X j) (rejectComplement ρ) c) ≤ coreW1 w c := by
  rintro ⟨w, hw, hle⟩
  obtain ⟨c, hc⟩ := exists_coreW1_lt_pcnlKernel j w hw hD
  exact absurd (hle c) (not_le.mpr hc)


/-! ## 21.6 The quadratic potential: the Hessian's `λ` is a constant, the gap is the degree

§21 named the gap's source: not the drift's size but its sign structure.  This section computes the
case the plan's Bakry–Émery hypothesis singles out — `Φ_λ(u) = (λ/2)∑ⱼ uⱼ²`, the equality case
`Hess Φ = λ·I` — and finds that the Hessian enters the *constant*, not the gap.

The one ingredient is adjunction.  `corePair_hopStep_adjoint` proves `a_j†` is the right adjoint of
`a_j` in the core pairing (raising is a bijection onto the occupied part of the support and the
amplitudes `√(nⱼ + 1)` match), which is the `ℓ²` statement the `ℓ¹` computations of §9.9–§21 never
needed.  From it:

* `corePair_raise_lower_re`, `corePair_lower_raise_re` — `⟪c, a†a c⟫ = ‖a c‖²` and
  `⟪c, aa† c⟫ = ‖a† c‖²`;
* **`corePair_double_raise_re_eq`** — the double letters have equal real pairing,
  `Re⟪c, a†²c⟫ = Re⟪c, a²c⟫` (they are complex conjugates), so `x_j∂_j = (a² − a†²)/2 − 1/2`
  contributes only its `−1/2`;
* **`re_corePair_mulHermite_diffHermite`** — therefore `Re⟪c, x_j∂_j c⟫ = −½‖c‖²`, and
  `re_corePair_sum_mulHermite_diffHermite` sums it to `−(d/2)‖c‖²`;
* **`pderiv_quadPotential`** — the potential's gradient is `λx` (`pderiv` of `∑ X k²` is `2X j`,
  and `polyMul_smul_poly` is the `ℂ`-homogeneity of the polynomial operator), so
  **`polyDrift_quadPotential`** / **`driftOperator_quadPotential`** give `K_drift = −λ Σⱼ xⱼ∂ⱼ`;
* **`re_corePair_quadHamiltonian`** — the pCNL form is `numberForm c + E₀‖c‖²` with
  `E₀ = (β²σ²/2)·λd/2`;
* **`quadForm_gap`** — off the vacuum it is at least `(E₀ + 1)‖c‖²` (`numberForm_ge_of_vac`), so the
  gap is the number operator's `1`; `quadForm_vac` shows the bottom is `E₀` and
  `quadForm_degree_one` that the bound is sharp.

So a Hessian bound `λ I` makes the form coercive with constant `E₀ ∝ λ d` and leaves the Fock gap at
`1`: the plan's `γ = λ` is a statement about the generator on `L²(π_Φ)`, not about this form.
-/

/-- The pairing is conjugation-symmetric: `⟪c, c'⟫ = conj ⟪c', c⟫`. -/
theorem corePair_comm_conj (c c' : CoreCoeff d) : corePair c c' = star (corePair c' c) := by
  classical
  have hunion : c.support ∪ c'.support = c'.support ∪ c.support := Finset.union_comm _ _
  rw [corePair, corePair, hunion]
  simp only [star_sum]
  exact Finset.sum_congr rfl fun n _ => by rw [star_mul, star_star]

/-- `⟪c, c⟫` is the `ℓ²` mass. -/
theorem corePair_self_re (x : CoreCoeff d) : (corePair x x).re = coreNormSq x := by
  classical
  rw [corePair_eq_sum (s := x.support) (Finset.Subset.refl _) (Finset.Subset.refl _),
    coreNormSq, Complex.re_sum]
  exact Finset.sum_congr rfl fun n _ => by
    rw [Complex.star_def, Complex.mul_conj, Complex.ofReal_re, Complex.normSq_eq_norm_sq]

/-- **`a_j†` is the right adjoint of `a_j`** in the core pairing:
`⟪a_j c, c'⟫ = ⟪c, a_j† c'⟫`.  Raising is a bijection onto the occupied part of the support, and
the amplitudes `√(nⱼ + 1)` match on the two sides. -/
theorem corePair_hopStep_adjoint (j : Fin d) (c c' : CoreCoeff d) :
    corePair (hopStep (j, false) c) c' = corePair c (hopStep (j, true) c') := by
  classical
  have hL : corePair (hopStep (j, false) c) c'
      = ∑ n ∈ (hopStep (j, false) c).support, hopStep (j, false) c n * star (c' n) := by
    rw [corePair_eq_sum (s := (hopStep (j, false) c).support ∪ c'.support)
      Finset.subset_union_left Finset.subset_union_right]
    exact (Finset.sum_subset Finset.subset_union_left fun x _ hx => by
      rw [Finsupp.notMem_support_iff.mp hx, zero_mul]).symm
  have hR : corePair c (hopStep (j, true) c')
      = ∑ n ∈ c.support, c n * star (hopStep (j, true) c' n) := by
    rw [corePair_eq_sum (s := c.support ∪ (hopStep (j, true) c').support)
      Finset.subset_union_left Finset.subset_union_right]
    exact (Finset.sum_subset Finset.subset_union_left fun x _ hx => by
      rw [Finsupp.notMem_support_iff.mp hx, zero_mul]).symm
  rw [hL, hR]
  have hdrop : ∑ m ∈ c.support.filter (fun m => m j ≠ 0), c m * star (hopStep (j, true) c' m)
      = ∑ m ∈ c.support, c m * star (hopStep (j, true) c' m) := by
    rw [Finset.sum_filter]
    refine Finset.sum_congr rfl fun m _ => ?_
    by_cases hm : m j = 0
    · rw [if_neg (by simp [hm]), hopStep_coord_raise, hm]
      simp
    · rw [if_pos (by simp [hm])]
  rw [← hdrop]
  refine Finset.sum_bij (fun n _ => raiseIdx j n) ?_ ?_ ?_ ?_
  · intro n hn
    exact Finset.mem_filter.mpr (mem_support_hopStep_lower hn)
  · intro a _ b _ h
    exact raiseIdx_injective j h
  · intro m hm
    obtain ⟨hmc, hmj⟩ := Finset.mem_filter.mp hm
    refine ⟨lowerIdx j m, ?_, raiseIdx_lowerIdx_of_pos j hmj⟩
    rw [Finsupp.mem_support_iff, hopStep_coord_lower_at j c hmj]
    refine mul_ne_zero ?_ (Finsupp.mem_support_iff.mp hmc)
    have hpos : (0 : ℝ) < Real.sqrt (m j : ℝ) := by
      exact Real.sqrt_pos.mpr (by exact_mod_cast Nat.pos_of_ne_zero hmj)
    exact_mod_cast ne_of_gt hpos
  · intro n hn
    dsimp only
    rw [hopStep_coord_lower, hopStep_coord_raise, lowerIdx_raiseIdx, raiseIdx_apply_same]
    have hcast : ∀ x : ℝ, star ((Real.sqrt x : ℝ) : ℂ) = ((Real.sqrt x : ℝ) : ℂ) := fun x => by
      rw [Complex.star_def, Complex.conj_ofReal]
    rw [star_mul, hcast]
    have harg : ((n j + 1 : ℕ) : ℝ) = (n j : ℝ) + 1 := by push_cast; ring
    rw [harg]
    ring

/-- **`⟪c, a_j† a_j c⟫ = ‖a_j c‖²`**, from the adjunction. -/
theorem corePair_raise_lower_re (j : Fin d) (c : CoreCoeff d) :
    (corePair c (hopStep (j, true) (hopStep (j, false) c))).re
      = coreNormSq (hopStep (j, false) c) := by
  rw [← corePair_hopStep_adjoint j c (hopStep (j, false) c), corePair_self_re]

/-- **`⟪c, a_j a_j† c⟫ = ‖a_j† c‖²`**, from the adjunction read the other way. -/
theorem corePair_lower_raise_re (j : Fin d) (c : CoreCoeff d) :
    (corePair c (hopStep (j, false) (hopStep (j, true) c))).re
      = coreNormSq (hopStep (j, true) c) := by
  rw [corePair_comm_conj, corePair_hopStep_adjoint j (hopStep (j, true) c) c,
    Complex.star_def, Complex.conj_re, corePair_self_re]

/-- **The double letters have equal real pairing**: `Re⟪c, a_j†² c⟫ = Re⟪c, a_j² c⟫`, because the
two are complex conjugates of each other. -/
theorem corePair_double_raise_re_eq (j : Fin d) (c : CoreCoeff d) :
    (corePair c (hopStep (j, true) (hopStep (j, true) c))).re
      = (corePair c (hopStep (j, false) (hopStep (j, false) c))).re := by
  have h1 : corePair (hopStep (j, false) c) (hopStep (j, true) c)
      = corePair c (hopStep (j, true) (hopStep (j, true) c)) :=
    corePair_hopStep_adjoint j c (hopStep (j, true) c)
  have h2 : corePair c (hopStep (j, false) (hopStep (j, false) c))
      = star (corePair (hopStep (j, false) c) (hopStep (j, true) c)) := by
    rw [corePair_comm_conj, corePair_hopStep_adjoint j (hopStep (j, false) c) c]
  have hkey : corePair c (hopStep (j, true) (hopStep (j, true) c))
      = star (corePair c (hopStep (j, false) (hopStep (j, false) c))) := by
    calc corePair c (hopStep (j, true) (hopStep (j, true) c))
        = corePair (hopStep (j, false) c) (hopStep (j, true) c) := h1.symm
      _ = star (star (corePair (hopStep (j, false) c) (hopStep (j, true) c))) :=
          (star_star _).symm
      _ = star (corePair c (hopStep (j, false) (hopStep (j, false) c))) := by rw [← h2]
  rw [hkey, Complex.star_def, Complex.conj_re]


/-! ## The form of `x_j ∂_j` -/

/-- The mode's lowering in the `ℓ²` mass exceeds its raising by exactly the mass. -/
theorem coreNormSq_lower_sub_raise (j : Fin d) (c : CoreCoeff d) :
    coreNormSq (hopStep (j, false) c) - coreNormSq (hopStep (j, true) c) = -coreNormSq c := by
  rw [coreNormSq_hopStep_lower, coreNormSq_hopStep_raise_eq, coreNormSq]
  ring

/-- **The letters `x_j` and `∂_j` composed**, expanded into the four double letters. -/
theorem mulHermite_diffHermite_eq (j : Fin d) (c : CoreCoeff d) :
    mulHermite j (diffHermite j c)
      = (((invSqrtTwo * invSqrtTwo : ℝ)) : ℂ) •
          (hopStep (j, true) (hopStep (j, false) c)
            - hopStep (j, true) (hopStep (j, true) c)
            + hopStep (j, false) (hopStep (j, false) c)
            - hopStep (j, false) (hopStep (j, true) c)) := by
  rw [mulHermite, diffHermite, hopStep_smul, hopStep_smul, hopStep_sub, hopStep_sub]
  module

/-- **`x_j ∂_j` has a strictly negative real pairing**: only the `a†a` and `aa†` letters survive
(the double letters cancel in real part) and their norms differ by the mass. -/
theorem re_corePair_mulHermite_diffHermite (j : Fin d) (c : CoreCoeff d) :
    (corePair c (mulHermite j (diffHermite j c))).re = -(1 / 2) * coreNormSq c := by
  rw [mulHermite_diffHermite_eq]
  have hk : star (((invSqrtTwo * invSqrtTwo : ℝ)) : ℂ)
      = (((invSqrtTwo * invSqrtTwo : ℝ)) : ℂ) := by
    rw [Complex.star_def, Complex.conj_ofReal]
  rw [corePair_smul, hk, corePair_sub, corePair_add, corePair_sub]
  simp only [Complex.mul_re, Complex.ofReal_re, Complex.ofReal_im, Complex.sub_re,
    Complex.add_re, zero_mul, sub_zero]
  rw [corePair_raise_lower_re, corePair_lower_raise_re, ← corePair_double_raise_re_eq]
  have hsq : invSqrtTwo * invSqrtTwo = 1 / 2 := by
    rw [← sq]; exact invSqrtTwo_sq
  have hgrp : coreNormSq (hopStep (j, false) c)
        - (corePair c (hopStep (j, true) (hopStep (j, true) c))).re
        + (corePair c (hopStep (j, true) (hopStep (j, true) c))).re
        - coreNormSq (hopStep (j, true) c)
      = coreNormSq (hopStep (j, false) c) - coreNormSq (hopStep (j, true) c) := by ring
  rw [hgrp, hsq, coreNormSq_lower_sub_raise]
  ring

/-- **The sum over the modes**: `Re⟪c, Σ_j x_j ∂_j c⟫ = −(d/2)‖c‖²`. -/
theorem re_corePair_sum_mulHermite_diffHermite (c : CoreCoeff d) :
    (corePair c (∑ j : Fin d, mulHermite j (diffHermite j c))).re
      = -((d : ℝ) / 2) * coreNormSq c := by
  classical
  rw [corePair_finset_sum, Complex.re_sum]
  simp only [re_corePair_mulHermite_diffHermite]
  rw [← Finset.sum_mul, Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  ring

/-! ## The quadratic potential: the Hessian's `λ` is a constant, not a gap -/

/-- The quadratic potential `Φ_λ(u) = (λ/2)∑ⱼ uⱼ²` — the equality case `Hess Φ = λ·I` of the
Bakry–Émery hypothesis. -/
def quadPotential (lam : ℝ) : MvPolynomial (Fin d) ℂ :=
  MvPolynomial.C (((lam / 2 : ℝ)) : ℂ) * ∑ j : Fin d, MvPolynomial.X j ^ 2

theorem pderiv_sum_squares (j : Fin d) :
    MvPolynomial.pderiv j (∑ k : Fin d, (MvPolynomial.X k : MvPolynomial (Fin d) ℂ) ^ 2)
      = (2 : MvPolynomial (Fin d) ℂ) * MvPolynomial.X j := by
  rw [map_sum]
  rw [Finset.sum_eq_single j]
  · rw [MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X, Pi.single_eq_same]
    simp
  · intro k _ hk
    rw [MvPolynomial.pderiv_pow, MvPolynomial.pderiv_X, Pi.single_apply, if_neg hk]
    simp
  · intro h; exact absurd (Finset.mem_univ j) h

/-- **The quadratic potential's gradient is `λx`** — the Hessian bound in its equality case. -/
theorem pderiv_quadPotential (lam : ℝ) (j : Fin d) :
    MvPolynomial.pderiv j (quadPotential lam) = ((lam : ℂ)) • MvPolynomial.X j := by
  rw [quadPotential, MvPolynomial.pderiv_mul, MvPolynomial.pderiv_C, zero_mul, zero_add,
    pderiv_sum_squares, MvPolynomial.smul_eq_C_mul]
  have h2 : (2 : MvPolynomial (Fin d) ℂ) = MvPolynomial.C (2 : ℂ) :=
    (map_ofNat MvPolynomial.C 2).symm
  rw [← mul_assoc, h2, ← MvPolynomial.C_mul]
  congr 1
  push_cast
  ring_nf

/-- The polynomial operator is `ℂ`-homogeneous in the potential. -/
theorem polyMul_smul_poly (r : ℂ) (Φ : MvPolynomial (Fin d) ℂ) (c : CoreCoeff d) :
    polyMul (r • Φ) c = r • polyMul Φ c := by
  rw [MvPolynomial.smul_eq_C_mul, polyMul_mul, polyMul_C]

/-- **The drift of the quadratic potential**: `K_drift = −λ Σⱼ xⱼ ∂ⱼ`. -/
theorem polyDrift_quadPotential (lam : ℝ) (c : CoreCoeff d) :
    polyDrift (quadPotential lam) c
      = -(((lam : ℝ)) : ℂ) • ∑ j : Fin d, mulHermite j (diffHermite j c) := by
  unfold polyDrift
  have hterm : ∀ j : Fin d,
      polyMul (MvPolynomial.pderiv j (quadPotential lam)) (diffHermite j c)
        = ((lam : ℂ)) • mulHermite j (diffHermite j c) := by
    intro j
    rw [pderiv_quadPotential, polyMul_smul_poly, polyMul_X]
  rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.smul_sum, ← neg_smul]


/-- **The drift operator of the quadratic potential**: `K_drift = −(β²σ²/2)λ Σⱼ xⱼ ∂ⱼ`. -/
theorem driftOperator_quadPotential (β σ lam : ℝ) (c : CoreCoeff d) :
    driftOperator β σ (quadPotential lam) c
      = -(((driftWeight β σ * lam : ℝ)) : ℂ) •
          ∑ j : Fin d, mulHermite j (diffHermite j c) := by
  rw [driftOperator, polyDrift_quadPotential, smul_smul]
  congr 1
  push_cast
  ring

/-- **The pCNL form of the quadratic potential**: the number form plus a constant.  The Hessian
`Hess Φ_λ = λ·I` enters only through `E₀ = (β²σ²/2)·λd/2`; the degree grading supplies the rest. -/
theorem re_corePair_quadHamiltonian (β σ lam : ℝ) (c : CoreCoeff d) :
    (corePair c (numberOp c + driftOperator β σ (quadPotential lam) c)).re
      = numberForm c + driftWeight β σ * (lam * (d : ℝ) / 2) * coreNormSq c := by
  rw [corePair_add, Complex.add_re, corePair_numberOp_re, driftOperator_quadPotential]
  have hneg : star (-(((driftWeight β σ * lam : ℝ)) : ℂ))
      = -(((driftWeight β σ * lam : ℝ)) : ℂ) := by
    rw [star_neg, Complex.star_def, Complex.conj_ofReal]
  rw [corePair_smul, hneg, Complex.mul_re,
    re_corePair_sum_mulHermite_diffHermite]
  simp only [Complex.ofReal_re, Complex.ofReal_im, Complex.neg_re, Complex.neg_im]
  ring

/-- The total degree is positive away from the vacuum. -/
theorem natDeg_pos_of_ne_zero {n : Fin d → ℕ} (hn : n ≠ 0) : 0 < natDeg n := by
  by_contra h
  have h0 : natDeg n = 0 := Nat.eq_zero_of_not_pos h
  refine hn (funext fun i => ?_)
  simp only [Pi.zero_apply]
  have hi : n i ≤ natDeg n :=
    Finset.single_le_sum (f := n) (fun k _ => Nat.zero_le _) (Finset.mem_univ i)
  omega

/-- Away from the vacuum the number form dominates the `ℓ²` mass. -/
theorem numberForm_ge_of_vac {c : CoreCoeff d} (h : c (0 : Fin d → ℕ) = 0) :
    coreNormSq c ≤ numberForm c := by
  classical
  rw [coreNormSq, numberForm]
  refine Finset.sum_le_sum fun n hn => ?_
  have hn0 : n ≠ 0 := by
    intro hz
    exact Finsupp.mem_support_iff.mp hn (by rw [hz]; exact h)
  have hge : (1 : ℝ) ≤ (natDeg n : ℝ) := by
    exact_mod_cast natDeg_pos_of_ne_zero hn0
  calc ‖c n‖ ^ 2 = 1 * ‖c n‖ ^ 2 := (one_mul _).symm
    _ ≤ (natDeg n : ℝ) * ‖c n‖ ^ 2 := mul_le_mul_of_nonneg_right hge (by positivity)

/-- **The Hessian's `λ` is not the gap.**  For the quadratic potential — the equality case
`Hess Φ = λ·I` of the Bakry–Émery hypothesis — the pCNL form is `numberForm + E₀‖c‖²`, so off the
vacuum it is at least `(E₀ + 1)‖c‖²`: the Hessian bound shifts the bottom of the spectrum by
`E₀ = (β²σ²/2)·λd/2` and leaves the gap at the number operator's `1`.  The plan's `γ = λ` is a
statement about the generator on `L²(π)`, not about this form. -/
theorem quadForm_gap (β σ lam : ℝ) {c : CoreCoeff d} (h : c (0 : Fin d → ℕ) = 0) :
    (1 + driftWeight β σ * (lam * (d : ℝ) / 2)) * coreNormSq c
      ≤ (corePair c (numberOp c + driftOperator β σ (quadPotential lam) c)).re := by
  rw [re_corePair_quadHamiltonian]
  have hn := numberForm_ge_of_vac h
  nlinarith

theorem numberForm_single (m : Fin d → ℕ) (a : ℂ) :
    numberForm (Finsupp.single m a) = (natDeg m : ℝ) * ‖a‖ ^ 2 := by
  rw [numberForm, Finset.sum_subset Finsupp.support_single_subset (fun x _ hx => ?_)]
  · simp
  · rw [Finsupp.notMem_support_iff.mp hx, norm_zero]
    ring

/-- The bottom of the form is `E₀ = (β²σ²/2)·λd/2`, attained at the vacuum. -/
theorem quadForm_vac (β σ lam : ℝ) :
    (corePair (Finsupp.single (0 : Fin d → ℕ) 1)
      (numberOp (Finsupp.single (0 : Fin d → ℕ) 1)
        + driftOperator β σ (quadPotential lam) (Finsupp.single (0 : Fin d → ℕ) 1))).re
      = driftWeight β σ * (lam * (d : ℝ) / 2) := by
  rw [re_corePair_quadHamiltonian, numberForm_single, coreNormSq_single, norm_one,
    natDeg_zero]
  push_cast
  ring

/-- The gap is sharp: on the first excited sector the form equals `E₀ + 1`. -/
theorem quadForm_degree_one (β σ lam : ℝ) (j : Fin d) :
    (corePair (Finsupp.single (raiseIdx j 0) 1)
      (numberOp (Finsupp.single (raiseIdx j 0) 1)
        + driftOperator β σ (quadPotential lam) (Finsupp.single (raiseIdx j 0) 1))).re
      = 1 + driftWeight β σ * (lam * (d : ℝ) / 2) := by
  rw [re_corePair_quadHamiltonian, numberForm_single, coreNormSq_single, norm_one,
    natDeg_raiseIdx, natDeg_zero]
  push_cast
  ring




/-! ## 21.7 Affine gradients: the Hessian in the constant, the linear part in §11

§21.6 computed the quadratic potential.  The next class up is the one a Hessian bound actually
describes: a potential whose gradient is affine, `∇Φ = λx + a`, i.e. `Φ = Φ_λ + Σⱼ aⱼxⱼ`.  Its drift
splits, and the two halves have different sources:

* `polyDrift_add` / `driftOperator_add` — the drift is additive in the potential, so
  `K_drift(Φ_λ + lin) = K_drift Φ_λ + K_drift(lin)`;
* the quadratic half is the exact form of §21.6 (`re_corePair_quadHamiltonian`), contributing
  `λ·E₀` to the constant;
* the linear half is §12's `driftOperator_linear_form_bound`, so it costs `δ·⟪c,Nc⟫` plus
  `driftScale²·(B²d/(2δ) + Bd)‖c‖²`.

**`re_corePair_affineHamiltonian`** is the sum: on the degree-`≥ 1` sector (and away from the
vacuum, `affineForm_gap`) the form is at least `(1 − δ)·⟪c,Nc⟫` plus
`(E₀ − C_δ)‖c‖²`, with `E₀ = (β²σ²/2)·λd/2`.  The Hessian's `λ` therefore sits entirely in the
constant and the *number-form coefficient* stays `1 − δ`, which is P3's point with the quadratic
case isolated: a Hessian bound gives coercivity, and the gap on this side is the degree grading.
-/

/-- The polynomial drift is additive in the potential. -/
theorem polyDrift_add (Φ Ψ : MvPolynomial (Fin d) ℂ) (c : CoreCoeff d) :
    polyDrift (Φ + Ψ) c = polyDrift Φ c + polyDrift Ψ c := by
  unfold polyDrift
  simp only [map_add, polyMul_add]
  rw [Finset.sum_add_distrib, neg_add]

theorem driftOperator_add (β σ : ℝ) (Φ Ψ : MvPolynomial (Fin d) ℂ) (c : CoreCoeff d) :
    driftOperator β σ (Φ + Ψ) c = driftOperator β σ Φ c + driftOperator β σ Ψ c := by
  rw [driftOperator, driftOperator, driftOperator, polyDrift_add, smul_add]

/-- **The pCNL form of an affine-gradient potential.**  For `Φ = Φ_λ + Σⱼ aⱼ xⱼ` — gradient
`λx + a`, the constant-Hessian-`λ` class — the form is the exact quadratic form (§21.6) plus the
linear part, which §11 bounds: `(1 − δ)·⟪c,Nc⟫` plus constants, the Hessian's `λ` contributing
`E₀ = (β²σ²/2)·λd/2`. -/
theorem re_corePair_affineHamiltonian (β σ lam M : ℝ) (a : Fin d → ℝ) (hM0 : 0 ≤ M)
    (ha : ∀ j, |a j| ≤ M) (δ : ℝ) (hδ : 0 < δ) (c : CoreCoeff d) :
    (1 - δ) * numberForm c + (driftWeight β σ * (lam * (d : ℝ) / 2)
        - (driftScale β σ M ^ 2 * (d : ℝ) / (2 * δ) + driftScale β σ M * (d : ℝ)))
        * coreNormSq c
      ≤ (corePair c (numberOp c + driftOperator β σ (quadPotential lam
          + ∑ k : Fin d, MvPolynomial.C (((a k : ℝ)) : ℂ) * MvPolynomial.X k) c)).re := by
  have hsplit : corePair c (numberOp c + driftOperator β σ (quadPotential lam
        + ∑ k : Fin d, MvPolynomial.C (((a k : ℝ)) : ℂ) * MvPolynomial.X k) c)
      = corePair c (numberOp c + driftOperator β σ (quadPotential lam) c)
        + corePair c (driftOperator β σ
            (∑ k : Fin d, MvPolynomial.C (((a k : ℝ)) : ℂ) * MvPolynomial.X k) c) := by
    rw [driftOperator_add, ← add_assoc, corePair_add, corePair_add]
  rw [hsplit, Complex.add_re, re_corePair_quadHamiltonian]
  have hb := driftOperator_linear_form_bound β σ hM0 ha δ hδ c
  have hre : ‖corePair c (driftOperator β σ
        (∑ k : Fin d, MvPolynomial.C (((a k : ℝ)) : ℂ) * MvPolynomial.X k) c)‖
      ≤ δ * numberForm c + (driftScale β σ M ^ 2 * (d : ℝ) / (2 * δ)
          + driftScale β σ M * (d : ℝ)) * coreNormSq c := hb
  have hlow : -(δ * numberForm c + (driftScale β σ M ^ 2 * (d : ℝ) / (2 * δ)
        + driftScale β σ M * (d : ℝ)) * coreNormSq c)
      ≤ (corePair c (driftOperator β σ
          (∑ k : Fin d, MvPolynomial.C (((a k : ℝ)) : ℂ) * MvPolynomial.X k) c)).re := by
    have habs := Complex.abs_re_le_norm (corePair c (driftOperator β σ
      (∑ k : Fin d, MvPolynomial.C (((a k : ℝ)) : ℂ) * MvPolynomial.X k) c))
    have hneg := neg_abs_le (corePair c (driftOperator β σ
      (∑ k : Fin d, MvPolynomial.C (((a k : ℝ)) : ℂ) * MvPolynomial.X k) c)).re
    linarith
  nlinarith

/-- **The gap of an affine-gradient potential**, off the vacuum: `((1 − δ) + E₀ − C_δ)‖c‖²`, the
`λ`-term in the constant and the number-form coefficient `1 − δ` independent of `λ`. -/
theorem affineForm_gap (β σ lam M : ℝ) (a : Fin d → ℝ) (hM0 : 0 ≤ M)
    (ha : ∀ j, |a j| ≤ M) (δ : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) {c : CoreCoeff d}
    (hc : c (0 : Fin d → ℕ) = 0) :
    ((1 - δ) + driftWeight β σ * (lam * (d : ℝ) / 2)
        - (driftScale β σ M ^ 2 * (d : ℝ) / (2 * δ) + driftScale β σ M * (d : ℝ)))
        * coreNormSq c
      ≤ (corePair c (numberOp c + driftOperator β σ (quadPotential lam
          + ∑ k : Fin d, MvPolynomial.C (((a k : ℝ)) : ℂ) * MvPolynomial.X k) c)).re := by
  have hmain := re_corePair_affineHamiltonian β σ lam M a hM0 ha δ hδ c
  have hnum := numberForm_ge_of_vac hc
  nlinarith



/-! ## 21.8 The best constant of the affine form bound, and the crossover

§21.7 bounded the affine class's form by `(1 − δ)·⟪c,Nc⟫ + (E₀ − C_δ)‖c‖²` with
`C_δ = A/(2δ) + driftScale·d` and `A = driftScale²·d`.  That leaves `δ` free, and P3 asks whether
*some* `δ` certifies a gap.  The answer is a computation:

* `sqrt_two_mul_le_add_div` — `√(2A) ≤ δ + A/(2δ)` for `δ > 0`, from `(A − 2δ²)² ≥ 0`;
* **`affineForm_coefficient_le`** — the coefficient of `‖c‖²` is at most
  `1 + E₀ − driftScale·d − driftScale·√(2d)` for *every* `δ`: the AM-GM step cancels the free
  parameter, so no choice of `δ` recovers more;
* **`affineForm_best_coefficient_neg`** — hence, whenever `1 + E₀ < driftScale·(d + √(2d))`, the
  best constant is negative and the §11 route certifies no gap off the vacuum for this class;
* **`affineForm_architecture_coefficient`** — at the implementation's numbers
  (`β = 0.3`, `σ = 0.35`, `M = 2·10⁶`, `d = 16672`, `λ = 1`) the best constant is below `−10⁷`.

So the relative-form bound is a licence for `pcnlHamiltonian` and not a gap certificate — P3's
observation, with the `δ`-optimisation done and the architecture's numbers checked.
-/

/-- **The AM-GM step behind the constant**: `√(2A) ≤ δ + A/(2δ)` for `δ > 0`, by
`(A − 2δ²)² ≥ 0`. -/
theorem sqrt_two_mul_le_add_div {A δ : ℝ} (hA : 0 ≤ A) (hδ : 0 < δ) :
    Real.sqrt (2 * A) ≤ δ + A / (2 * δ) := by
  rw [Real.sqrt_le_iff]
  refine ⟨?_, ?_⟩
  · have h1 : 0 ≤ A / (2 * δ) := by positivity
    linarith
  · have h1 : 0 ≤ A / (2 * δ) := by positivity
    field_simp
    nlinarith [sq_nonneg (A - 2 * δ ^ 2), hδ, hA]

/-- **The best constant of the affine form bound.**  For every `δ > 0` the coefficient of `‖c‖²` in
`re_corePair_affineHamiltonian` is at most `1 + E₀ − driftScale·d − driftScale·√(2d)`: the AM-GM
step spends `δ` against `δ + A/(2δ) ≥ √(2A)`, so no choice of `δ` recovers more. -/
theorem affineForm_coefficient_le (β σ M lam : ℝ) (hM0 : 0 ≤ M) (δ : ℝ) (hδ : 0 < δ) :
    (1 - δ) + driftWeight β σ * (lam * (d : ℝ) / 2)
        - (driftScale β σ M ^ 2 * (d : ℝ) / (2 * δ) + driftScale β σ M * (d : ℝ))
      ≤ 1 + driftWeight β σ * (lam * (d : ℝ) / 2)
        - driftScale β σ M * (d : ℝ) - driftScale β σ M * Real.sqrt (2 * (d : ℝ)) := by
  have hdw : 0 ≤ driftScale β σ M := driftScale_nonneg hM0
  have hA : 0 ≤ driftScale β σ M ^ 2 * (d : ℝ) := by positivity
  have h := sqrt_two_mul_le_add_div (A := driftScale β σ M ^ 2 * (d : ℝ)) (δ := δ) hA hδ
  have hsq : Real.sqrt (2 * (driftScale β σ M ^ 2 * (d : ℝ)))
      = driftScale β σ M * Real.sqrt (2 * (d : ℝ)) := by
    rw [show (2 * (driftScale β σ M ^ 2 * (d : ℝ)))
      = (driftScale β σ M) ^ 2 * (2 * (d : ℝ)) by ring,
      Real.sqrt_mul (by positivity), Real.sqrt_sq hdw]
  rw [hsq] at h
  linarith

/-- **The crossover.**  When `1 + E₀ < driftScale·(d + √(2d))` the best constant is negative, so the
§11 route to a gap — with *any* `δ` — certifies nothing off the vacuum for this class. -/
theorem affineForm_best_coefficient_neg (β σ M lam : ℝ) (hM0 : 0 ≤ M)
    (hcross : 1 + driftWeight β σ * (lam * (d : ℝ) / 2)
      < driftScale β σ M * ((d : ℝ) + Real.sqrt (2 * (d : ℝ))))
    (δ : ℝ) (hδ : 0 < δ) :
    (1 - δ) + driftWeight β σ * (lam * (d : ℝ) / 2)
        - (driftScale β σ M ^ 2 * (d : ℝ) / (2 * δ) + driftScale β σ M * (d : ℝ)) < 0 := by
  have := affineForm_coefficient_le (d := d) β σ M lam hM0 δ hδ
  linarith

/-- **The implementation's numbers.**  With `β = 0.3`, `σ = 0.35`, `M = 2·10⁶` (the `K/ε` gradient
bound at `ε = 10⁻⁶`, `K = 1`), `d = 16672` and `λ = 1`, the best constant of the form bound is below
`−10⁷`: at these parameters *no* `δ` certifies a gap, which is P3's point (2) as an inequality. -/
theorem affineForm_architecture_coefficient :
    1 + driftWeight (3 / 10) (7 / 20) * ((1 : ℝ) * (16672 : ℝ) / 2)
        - driftScale (3 / 10) (7 / 20) 2000000
            * ((16672 : ℝ) + Real.sqrt (2 * (16672 : ℝ)))
      < -(10000000 : ℝ) := by
  set s : ℝ := Real.sqrt (2 * (16672 : ℝ)) with hdef
  have hsb : (182 : ℝ) ≤ s := by
    rw [hdef, Real.le_sqrt (by norm_num) (by norm_num)]
    norm_num
  have hval : driftScale (3 / 10) (7 / 20) 2000000 = 11025 := by
    norm_num [driftScale, driftWeight]
  have hE : driftWeight (3 / 10) (7 / 20) * ((1 : ℝ) * 16672 / 2) = 459522 / 10000 := by
    norm_num [driftWeight]
  rw [hval, hE]
  nlinarith [hsb]



/-! ## 21.9 The `L²(π)` side: the ground-state transform, and the oscillator's gap

§21.5–§21.8 were about the core's own form.  The plan's remaining gap item is on the *other* side:
the operator `A = Δ − ∇Φ·∇` the pCNL kernel discretizes is symmetric in `L²(π)`, `π ∝ e^{−Φ}`, and
its spectral gap is the Poincaré constant of `π`.  This section states the identity that makes "the
`L²(π)` side" a well-posed object for a *general* `Φ` (hence for a general `V_eff`), and computes
the case the plan's Bakry–Émery hypothesis singles out.

* `Veff Φ = ¼|Φ'|² − ½Φ''` — the effective potential of the ground-state transform;
* `genDiff Φ f = f'' − Φ'·f'` — the pCNL generator in one dimension, and `groundScale Φ = e^{Φ/2}`
  the ground-state multiplier;
* **`genDiff_groundScale`** — the conjugation `A(e^{Φ/2}g) = e^{Φ/2}(g'' − V_eff·g)`: the generator
  on `L²(π)` is similar, through multiplication by `e^{Φ/2}`, to the Schrödinger operator
  `Δ − V_eff`.  A similarity preserves the spectrum, so the `L²(π)`-side gap is the gap of
  `−Δ + V_eff` — the object the plan's `pcnl_spectral_gap_of_hessian` needs;
* **`Veff_quadOne`** — for the quadratic potential `Φ_λ = (λ/2)y²` the effective potential is
  `¼λ²y² − ½λ`: the oscillator with its zero-point constant subtracted;
* `oscillatorOp` and **`re_corePair_oscillatorOp`** — the unit-frequency Schrödinger operator in
  letters, `∑ⱼ (aⱼ†aⱼ + aⱼaⱼ†)`, has form `2·numberForm + d‖c‖²`: `oscillator_identity` read as an
  operator identity rather than a norm identity;
* **`oscFreqOp`**, **`re_corePair_oscFreqOp`** — the frequency-`ω` oscillator
  `(ω/2)∑ⱼ(aⱼ†aⱼ + aⱼaⱼ†) − (ωd/2)` has form exactly `ω·numberForm c`, i.e. `ω·N` in letters;
* **`oscFreqOp_gap`** — hence off the vacuum its form is at least `ω‖c‖²`: the oscillator's gap,
  in the `L²(π)` variable, is `ω`, which is `γ = λ` for `λ = 2ω` — the plan's
  `pcnl_spectral_gap_of_hessian` on the side where it is true.

**Honest boundary.**  The identity is one-dimensional and pointwise; the `d`-dimensional statement
is its coordinate sum, which this section does not write out, and the passage from the similarity of
operators to a spectral statement (that it preserves the infimum of the Rayleigh quotient over the
mean-zero subspace) is the analytic step still open.  What is *not* claimed is a gap for the core's
own form — §21.6–§21.8 computed that side and it has none.  The gap lives on `L²(π)`, and the
oscillator computation above is its exactly solvable case.
-/

/-- The effective potential of the ground-state transform in one dimension,
`V_eff = ¼|Φ'|² − ½Φ''`. -/
def Veff (Φ : ℝ → ℝ) (x : ℝ) : ℝ := (deriv Φ x) ^ 2 / 4 - iteratedDeriv 2 Φ x / 2

/-- The pCNL generator `Δ − ∇Φ·∇` in one dimension. -/
def genDiff (Φ f : ℝ → ℝ) (x : ℝ) : ℝ := iteratedDeriv 2 f x - deriv Φ x * deriv f x

/-- The ground-state multiplier `e^{Φ/2}`. -/
def groundScale (Φ : ℝ → ℝ) (x : ℝ) : ℝ := Real.exp (Φ x / 2)

theorem groundScale_hasDerivAt {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 2 Φ) (x : ℝ) :
    HasDerivAt (groundScale Φ) (groundScale Φ x * (deriv Φ x / 2)) x := by
  have h : HasDerivAt (fun y => Φ y / 2) (deriv Φ x / 2) x :=
    (hΦ.differentiable (by norm_num)).differentiableAt.hasDerivAt.div_const 2
  simpa [groundScale] using h.exp

theorem groundScale_deriv {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 2 Φ) (x : ℝ) :
    deriv (groundScale Φ) x = groundScale Φ x * (deriv Φ x / 2) :=
  (groundScale_hasDerivAt hΦ x).deriv

theorem groundScale_contDiff {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 2 Φ) :
    ContDiff ℝ 2 (groundScale Φ) := by
  have h : ContDiff ℝ 2 (fun y => Φ y / 2) := hΦ.div_const 2
  exact Real.contDiff_exp.comp h

theorem groundScale_iteratedDeriv_two {Φ : ℝ → ℝ} (hΦ : ContDiff ℝ 2 Φ) (x : ℝ) :
    iteratedDeriv 2 (groundScale Φ) x
      = groundScale Φ x * ((deriv Φ x / 2) ^ 2 + iteratedDeriv 2 Φ x / 2) := by
  have hg : ContDiffAt ℝ 2 Real.exp (Φ x / 2) :=
    Real.contDiff_exp.contDiffAt
  have hf : ContDiffAt ℝ 2 (fun y => Φ y / 2) x := hΦ.contDiffAt.div_const 2
  have hcomp := iteratedDeriv_comp_two (g := Real.exp) (f := fun y => Φ y / 2) (x := x) hg hf
  have hexp2 : iteratedDeriv 2 Real.exp (Φ x / 2) = Real.exp (Φ x / 2) := by
    simp [iteratedDeriv_succ', Real.deriv_exp]
  have hexp1 : deriv Real.exp (Φ x / 2) = Real.exp (Φ x / 2) := by
    rw [Real.deriv_exp]
  have hhalf2 : iteratedDeriv 2 (fun y => Φ y / 2) x = iteratedDeriv 2 Φ x / 2 := by
    have hfun : (fun y => Φ y / 2) = fun y => (1 / 2 : ℝ) * Φ y := by
      funext y; ring
    rw [hfun, iteratedDeriv_const_mul (1 / 2) hΦ.contDiffAt]
    ring
  have hhalf1 : deriv (fun y => Φ y / 2) x = deriv Φ x / 2 := by
    have hfun : (fun y => Φ y / 2) = fun y => (1 / 2 : ℝ) * Φ y := by
      funext y; ring
    rw [hfun, deriv_const_mul (1 / 2) (hΦ.differentiable (by norm_num)).differentiableAt]
    ring
  change iteratedDeriv 2 (Real.exp ∘ fun y => Φ y / 2) x = _
  rw [hcomp]
  simp only [hexp2, hexp1, hhalf1, hhalf2, groundScale]
  ring

theorem genDiff_groundScale {Φ f : ℝ → ℝ} (hΦ : ContDiff ℝ 2 Φ) (hf : ContDiff ℝ 2 f)
    (x : ℝ) :
    genDiff Φ (fun y => groundScale Φ y * f y) x
      = groundScale Φ x * (iteratedDeriv 2 f x - Veff Φ x * f x) := by
  have hE : ContDiff ℝ 2 (groundScale Φ) := groundScale_contDiff hΦ
  have hmul := iteratedDeriv_mul (n := 2) (x := x) (f := groundScale Φ) (g := f)
    hE.contDiffAt hf.contDiffAt
  have hsum : ∑ i ∈ Finset.range (2 + 1), ((Nat.choose 2 i : ℕ) : ℝ)
        * iteratedDeriv i (groundScale Φ) x * iteratedDeriv (2 - i) f x
      = groundScale Φ x * iteratedDeriv 2 f x
        + 2 * (groundScale Φ x * (deriv Φ x / 2)) * deriv f x
        + (groundScale Φ x * ((deriv Φ x / 2) ^ 2 + iteratedDeriv 2 Φ x / 2)) * f x := by
    simp [Finset.sum_range_succ, groundScale_deriv hΦ x, groundScale_iteratedDeriv_two hΦ x]
  have hderiv : deriv (groundScale Φ * f) x
      = groundScale Φ x * (deriv Φ x / 2) * f x + groundScale Φ x * deriv f x := by
    rw [deriv_mul (hE.differentiable (by norm_num)).differentiableAt
      (hf.differentiable (by norm_num)).differentiableAt, groundScale_deriv hΦ x]
  unfold genDiff Veff
  change iteratedDeriv 2 (groundScale Φ * f) x - deriv Φ x * deriv (groundScale Φ * f) x = _
  rw [hmul, hsum, hderiv]
  ring

/-! ### oscillator part -/

/-- The unit-frequency oscillator `−Δ + |x|²` in letters: `∑ⱼ (aⱼ† aⱼ + aⱼ aⱼ†)`. -/
def oscillatorOp (c : CoreCoeff d) : CoreCoeff d :=
  ∑ j, (hopStep (j, true) (hopStep (j, false) c) + hopStep (j, false) (hopStep (j, true) c))

theorem re_corePair_oscillatorOp (c : CoreCoeff d) :
    (corePair c (oscillatorOp c)).re = 2 * numberForm c + (d : ℝ) * coreNormSq c := by
  unfold oscillatorOp
  rw [corePair_finset_sum, Complex.re_sum]
  simp only [corePair_add, Complex.add_re, corePair_raise_lower_re,
    corePair_lower_raise_re]
  exact oscillator_identity c

/-- The oscillator of frequency `ω` in the unit letters, `(ω/2)·∑ⱼ(aⱼ†aⱼ + aⱼaⱼ†) − (ωd/2)`. -/
def oscFreqOp (ω : ℝ) (c : CoreCoeff d) : CoreCoeff d :=
  ((ω / 2 : ℝ) : ℂ) • oscillatorOp c - (((ω * (d : ℝ) / 2)) : ℂ) • c

theorem star_ofReal_real (r : ℝ) : star ((r : ℝ) : ℂ) = ((r : ℝ) : ℂ) := by
  rw [Complex.star_def, Complex.conj_ofReal]

theorem re_corePair_oscFreqOp (ω : ℝ) (c : CoreCoeff d) :
    (corePair c (oscFreqOp ω c)).re = ω * numberForm c := by
  unfold oscFreqOp
  rw [sub_eq_add_neg, corePair_add, corePair_smul, ← neg_smul, corePair_smul, star_neg]
  have hcast : star ((↑ω * ((d : ℝ) : ℂ) / 2 : ℂ)) = ((ω * (d : ℝ) / 2 : ℝ) : ℂ) := by
    rw [show (↑ω * ((d : ℝ) : ℂ) / 2 : ℂ) = ((ω * (d : ℝ) / 2 : ℝ) : ℂ) by push_cast; ring,
      star_ofReal_real]
  rw [hcast, star_ofReal_real, neg_mul]
  rw [Complex.add_re, Complex.neg_re, Complex.re_ofReal_mul, Complex.re_ofReal_mul,
    re_corePair_oscillatorOp, corePair_self_re]
  ring

theorem oscFreqOp_gap {ω : ℝ} (hω : 0 ≤ ω) {c : CoreCoeff d}
    (hc : c (0 : Fin d → ℕ) = 0) :
    ω * coreNormSq c ≤ (corePair c (oscFreqOp ω c)).re := by
  rw [re_corePair_oscFreqOp]
  exact mul_le_mul_of_nonneg_left (numberForm_ge_of_vac hc) hω

/-- The one-dimensional quadratic potential `Φ_λ(y) = (λ/2)y²`, whose derivative is `λx`. -/
theorem deriv_quadOne (lam x : ℝ) :
    deriv (fun y : ℝ => (lam / 2) * y ^ 2) x = lam * x := by
  have h : HasDerivAt (fun y : ℝ => y ^ 2) (2 * x) x := by
    simpa using hasDerivAt_pow 2 x
  have h2 : HasDerivAt (fun y : ℝ => (lam / 2) * y ^ 2) ((lam / 2) * (2 * x)) x :=
    h.const_mul (lam / 2)
  rw [h2.deriv]
  ring

theorem iteratedDeriv_two_quadOne (lam x : ℝ) :
    iteratedDeriv 2 (fun y : ℝ => (lam / 2) * y ^ 2) x = lam := by
  have h1 : deriv (fun y : ℝ => (lam / 2) * y ^ 2) = fun y => lam * y := by
    funext y; exact deriv_quadOne lam y
  rw [show (2 : ℕ) = 1 + 1 from rfl, iteratedDeriv_succ', iteratedDeriv_one, h1]
  have h2 : HasDerivAt (fun y : ℝ => lam * y) lam x := by
    simpa using (hasDerivAt_id (x := x)).const_mul lam
  exact h2.deriv

/-- **`V_eff` of the quadratic potential**: `¼|Φ'|² − ½Φ'' = ¼λ²x² − ½λ`, the oscillator's
potential with its zero-point constant subtracted — the effective potential `P3` names. -/
theorem Veff_quadOne (lam x : ℝ) :
    Veff (fun y : ℝ => (lam / 2) * y ^ 2) x = lam ^ 2 * x ^ 2 / 4 - lam / 2 := by
  unfold Veff
  rw [deriv_quadOne, iteratedDeriv_two_quadOne]
  ring


/-! ## 21.10 The identity in `d` dimensions: the coordinate sum

§21.9 proves `genDiff_groundScale` in one dimension.  The `d`-dimensional statement is its
coordinate sum, and this section writes it out, because the pCNL potential lives on `ℝ^d` with
`d = 16672` modes and "the `L²(π)` side" would otherwise be a one-dimensional remark.

* `coordDir j` — the unit vector `eⱼ`; `coordDeriv f x j` (the derivative at `0` of the slice
  `t ↦ f (x + t·eⱼ)`) and `coordDerivTwo f x j` — the coordinate partials `∂ⱼ` and `∂ⱼ²`;
* `genDiffD Φ f = ∑ⱼ (∂ⱼ²f − ∂ⱼΦ·∂ⱼf)` — the pCNL generator `Δ − ∇Φ·∇` in coordinates, `VeffD Φ`
  the effective potential `∑ⱼ (¼(∂ⱼΦ)² − ½∂ⱼ²Φ)`, and `groundScaleD Φ = e^{Φ/2}`;
* **`genDiffD_groundScale`** — `A(e^{Φ/2}g) = e^{Φ/2}(Δg − V_eff·g)`, the same conjugation as
  §21.9, obtained by applying the one-dimensional identity to each slice and summing.  The
  one-dimensional theorem is used, not reproved: each slice is `ContDiff` because the affine map
  `t ↦ x + t·eⱼ` is (`coordSlice_contDiff`).

With §21.9's `Veff_quadOne` this gives the effective potential of the quadratic potential in `d`
dimensions as the coordinate sum, `¼λ²∑ⱼ xⱼ² − ½λd`; the identity itself is the general statement.
-/

/-- The unit vector `eⱼ` in `Fin d → ℝ`. -/
def coordDir (j : Fin d) : Fin d → ℝ := Pi.single j 1

/-- The coordinate derivative `∂ⱼ` at `x`: the derivative at `0` of the slice `t ↦ f (x + t·eⱼ)`. -/
def coordDeriv (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (j : Fin d) : ℝ :=
  deriv (fun t : ℝ => f (x + t • coordDir j)) 0

/-- The second coordinate derivative `∂ⱼ²` at `x`. -/
def coordDerivTwo (f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) (j : Fin d) : ℝ :=
  iteratedDeriv 2 (fun t : ℝ => f (x + t • coordDir j)) 0

/-- The `d`-dimensional pCNL generator `Δ − ∇Φ·∇`, in coordinates. -/
def genDiffD (Φ f : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ j, (coordDerivTwo f x j - coordDeriv Φ x j * coordDeriv f x j)

/-- The `d`-dimensional effective potential, in coordinates. -/
def VeffD (Φ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ :=
  ∑ j, ((coordDeriv Φ x j) ^ 2 / 4 - coordDerivTwo Φ x j / 2)

/-- The ground-state multiplier `e^{Φ/2}` in `d` dimensions. -/
def groundScaleD (Φ : (Fin d → ℝ) → ℝ) (x : Fin d → ℝ) : ℝ := Real.exp (Φ x / 2)

theorem coordSlice_contDiff (x v : Fin d → ℝ) :
    ContDiff ℝ 2 (fun t : ℝ => x + t • v) :=
  contDiff_const.add (contDiff_id.smul contDiff_const)

theorem genDiffD_groundScale {Φ f : (Fin d → ℝ) → ℝ} (hΦ : ContDiff ℝ 2 Φ)
    (hf : ContDiff ℝ 2 f) (x : Fin d → ℝ) :
    genDiffD Φ (fun y => groundScaleD Φ y * f y) x
      = groundScaleD Φ x * (∑ j, coordDerivTwo f x j - VeffD Φ x * f x) := by
  have hterm : ∀ j : Fin d,
      coordDerivTwo (fun y => groundScaleD Φ y * f y) x j
        - coordDeriv Φ x j * coordDeriv (fun y => groundScaleD Φ y * f y) x j
      = groundScaleD Φ x * (coordDerivTwo f x j
          - ((coordDeriv Φ x j) ^ 2 / 4 - coordDerivTwo Φ x j / 2) * f x) := by
    intro j
    have hline := coordSlice_contDiff (d := d) x (coordDir j)
    have h := genDiff_groundScale (Φ := fun t : ℝ => Φ (x + t • coordDir j))
      (f := fun t : ℝ => f (x + t • coordDir j)) (hΦ.comp hline) (hf.comp hline) 0
    simpa [genDiff, Veff, groundScale, coordDeriv, coordDerivTwo, groundScaleD] using h
  unfold genDiffD VeffD
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  conv_rhs =>
    rw [mul_sub, Finset.mul_sum, ← mul_assoc, Finset.mul_sum, Finset.sum_mul,
      ← Finset.sum_sub_distrib]
  exact Finset.sum_congr rfl fun j _ => by ring


end BookProof.MCMC.FockLangevin
