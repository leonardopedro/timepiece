import Mathlib
import BookProof.MCMC.GaussianPCNCompleteness
import BookProof.MCMC.ConvergenceTheorem

/-!
# Chapter GaussianPCNGap — the `|ρ|` contraction rate on the non-constant Hermite modes

Plan: `pcnl.md`, packet **T1**.  `GaussianPCNCompleteness` shows that the Hermite classes are an
eigenbasis of `L²(π)` and `GaussianPCNSpectrum` gives the eigenvalues `ρⁿ`.  This chapter reads
off the resulting **spectral gap**: on every Hermite combination with no constant term the pCN
operator contracts by the factor `|ρ| < 1`, so the `n`-th mode carries the geometric rate `|ρ|ⁿ`.

## What is proved here

* `abs_rho_lt_one` — for `ρ² + s² = 1` and `s ≠ 0`, `|ρ| < 1` (the nondegenerate proposal).
* `abs_rho_pow_le` — `|ρ|ⁿ ≤ |ρ|` for `n ≥ 1`, the monotonicity of the geometric decay.
* `hermiteLpNorm` — the normalised Hermite classes `[Heₙ] / √(n!)`.
* **`inner_hermiteLpNorm`**, `orthonormal_hermiteLpNorm` — they are **orthonormal** in
  `Lp ℂ 2 π`: `⟪[Heₘ]/√m!, [Heₙ]/√n!⟫ = δₘₙ`.  This is the `Lp` form of
  `integral_hermiteRealComplex_mul` together with `n! = ∫ Heₙ² ∂π`.
* **`gaussianPCNOp_hermiteLpNorm`** — the eigenrelation in the orthonormal scale:
  `P eₙ = ρⁿ • eₙ`.
* `norm_gaussianPCNOp_hermiteLpNorm` — the **mode rate** `‖P eₙ‖ = |ρ|ⁿ ‖eₙ‖`: each non-constant
  mode decays geometrically.
* **`norm_gaussianPCNOp_finset_sum_le`** — **the contraction at rate `|ρ|`**: for any finite
  Hermite combination `f = Σ_{n ∈ S} cₙ eₙ` with `0 ∉ S`,
  `‖P f‖ ≤ |ρ| ‖f‖`.  The proof is Parseval on the orthonormal family
  (`Orthonormal.inner_sum`): `‖f‖² = Σ ‖cₙ‖²` and `‖P f‖² = Σ ‖cₙ‖² |ρ|^{2n}`, and
  `|ρ|^{2n} ≤ |ρ|²` for `n ≥ 1`.
* `gaussianPCNOp_pow_hermiteLpNorm`, `gaussianPCNOp_pow_finset_sum` — the `k`-step form
  `Pᵏ eₙ = ρ^{kn} • eₙ` and `Pᵏ f = Σ cₙ ρ^{kn} • eₙ`.
* **`norm_gaussianPCNOp_pow_finset_sum_le`** — **the exponential rate**
  `‖Pᵏ f‖ ≤ |ρ|ᵏ ‖f‖` for every `k`, on the same non-constant finite combinations.
* `span_hermiteLpNorm_eq_span_toLp`, `dense_span_hermiteLpNorm` — the normalised classes span the
  same dense subspace as the unnormalised ones.
* **`gaussianPCNHilbertBasis`** — the orthonormal Hermite family packaged as a `HilbertBasis` of
  `L²(π)`.
* `hasSum_hermiteLpNorm` — the basis expansion `f = ∑' n, ⟨eₙ, f⟩ eₙ`.
* **`gaussianPCNOp_eq_tsum`** — **the diagonalisation**: `P f = ∑' n, (⟨eₙ, f⟩ ρⁿ) eₙ`.
* **`norm_gaussianPCNOp_le_of_inner_eq_zero`** — **the gap on the whole mean-zero subspace**: for
  every `f ⊥ e₀`, `‖P f‖ ≤ |ρ| ‖f‖`.  The closure step is done by closedness of the set where the
  inequality holds: the partial sums of the expansion lie in it (finite-sum lemma, with the `n = 0`
  term vanishing), and `HasSum` converges to `f`.
* **`norm_gaussianPCNOp_pow_le_of_inner_eq_zero`** — the same at every `k`: `‖Pᵏ f‖ ≤ |ρ|ᵏ ‖f‖`
  on the mean-zero subspace.
* `gaussianPCNOpZero_pow_hermiteLpNorm` — the `s = 0` isometry transports the modes:
  `P₀ᵏ eₙ = ρ^{kn} • eₙ`.
* **`tsum_norm_inner_hermiteLpNorm`** — **Parseval**: `∑' n, ‖⟨eₙ, f⟩‖² = ‖f‖²`.
* **`hasSum_gaussianPCNOp`**, **`inner_gaussianPCNOp_comm`** — the diagonal form as a `HasSum`, and
  **`P` is symmetric**: `⟨P f, g⟩ = ⟨f, P g⟩`.
* **`gaussianPCNOp_isSelfAdjoint`** — **`P` is self-adjoint**; with the complete orthonormal
  eigenbasis and real eigenvalues this is a genuine (discrete) spectral decomposition.
* **`gaussianPCNOp_eq_tsum_rankOne`** — the resolution-of-identity form
  `P f = ∑' n, ρⁿ • (⟨eₙ, f⟩ eₙ)`, against `∑' n, ⟨eₙ, f⟩ eₙ = f`.
* **`norm_gaussianPCNOp_pow_sub_const_le`** — **the `L²` rate of the pCN chain**:
  `‖Pᵏ f − ⟨e₀, f⟩ e₀‖ ≤ |ρ|ᵏ ‖f − ⟨e₀, f⟩ e₀‖`; consequently
  `tendsto_gaussianPCNOp_pow` (`Pᵏ f → ⟨e₀, f⟩ e₀`, the equilibrium constant) and
  `tendsto_gaussianPCNOp_pow_of_inner_eq_zero` (mean-zero data → `0`).  The invariant mode is
  `gaussianPCNOp_pow_hermiteLpNorm_zero` (`Pᵏ e₀ = e₀`).
* `inner_hermiteLpNorm_gaussianPCNOp` — the coefficient form of the diagonalisation,
  `⟨eₙ, P f⟩ = ρⁿ ⟨eₙ, f⟩`, and `exists_inner_hermiteLpNorm_ne_zero` — a nonzero `L²` vector has
  a nonzero Hermite coefficient (from `f = ∑' n, ⟨eₙ, f⟩ eₙ`).
* **`gaussianPCNOp_eigenvalue_eq_rho_pow`** — **the converse spectral statement**: every nonzero
  eigenvalue of `P` on `L²(π)` is one of the numbers `ρⁿ`.  With the eigenrelation `P eₙ = ρⁿ eₙ`
  this pins the eigenvalue list exactly to the geometric sequence.
* **`gaussianPCNOp_re_inner_eq_tsum`** — **the quadratic form**: `Re ⟪P f, f⟫ = ∑' n, ρⁿ ‖⟨eₙ,f⟩‖²`,
  the eigenvalues weighting the nonnegative coefficients that sum to `‖f‖²` (Parseval).
* **`gaussianPCNOp_re_inner_nonneg`**, **`gaussianPCNOp_isPositiveOp`** — **`P` is positive when
  `ρ ≥ 0`**: it is self-adjoint and its quadratic form is nonnegative.
  `gaussianPCNOp_eigenvalue_mem_Icc` records that the eigenvalues then lie in `[0, 1]`.
* **`gaussianPCN_tv_geometric_convergence`** — **total-variation rate `|ρ|ᵐ`**: composing the
  `L²` rate with the corpus's Born-to-variation bound (`ConvergenceTheorem.tvDist_le_half_l2`),
  `‖ν m − π‖_TV ≤ ofReal ((‖f‖/2) |ρ|ᵐ)` for iterates whose density deviations have the `L²`
  norms of `Pᵐ f`, `f ⊥ e₀`.
* **`gaussianPCNOp_pow_coeFn`** — **the a.e. transport**: the operator iterate `Pᵐ f` is
  represented `π`-almost everywhere by the `m`-fold pointwise kernel action on a representative of
  `f` (induction from `gaussianPCNOp_coeFn`, transporting representatives with
  `markovOpFun_congr`).
* `pcnIterateDensity`, `pcnIterateMeasure` — the density `1 + Re (κᵐ f)` of the `m`-th iterate and
  its `withDensity` measure, both *functions of `x`*, with `pcnIterateDeviation_ae_eq_re`,
  `memLp_pcnIterateDeviation`, `integral_pcnIterateDeviation_zero` (mean zero: `e₀` coefficients
  are conserved by every power, §11 at `n = 0`) and `sqrt_integral_pcnIterateDeviation_sq_le`
  (`‖d_m − 1‖₂ ≤ ‖Pᵐ f‖`) proved.
* **`gaussianPCN_tv_geometric_convergence_of_density`** — **the `|ρ|ᵐ` total-variation rate with the
  transport discharged**: `ν m` and `d m` are produced from `f`, and the only hypothesis left is
  that the densities are nonnegative.
* `gaussianPCNOp_eigenvalue_mem_spectrum`, `tendsto_eigenvalue_pow_zero`,
  **`zero_mem_spectrum_gaussianPCNOp`** — **`0` is in the spectrum of `P`**, as the limit of the
  eigenvalues `ρⁿ` inside the closed spectrum; `zero_not_eigenvalue_gaussianPCNOp` shows (for
  `ρ ≠ 0`) that `0` is an accumulation point and not an eigenvalue.
* **`hermiteSpectralMeasure`** — **the explicit spectral measure of `f`**: mass `‖⟨eₙ, f⟩‖²` at
  `ρⁿ`, with `hermiteSpectralMeasure_univ` (total mass `‖f‖²`), `hermiteSpectralMeasure_compl_range`
  (supported on `{ρⁿ}`), `summable_norm_inner_hermiteLpNorm`,
  `integrable_id_hermiteSpectralMeasure` and `integral_hermiteSpectralMeasure_id`
  (`∫ t dμ_f = Re ⟪P f, f⟫`).
* **`hermiteDiagonal`, `pcnFunctionalCalculus`** — **the bounded functional calculus of `P`**: for
  `φ` bounded by `1` on the spectrum `[-1, 1]`, `φ(P) f = ∑' n, φ(ρⁿ) ⟨eₙ, f⟩ eₙ`, constructed
  through the Hilbert-basis identification with `ℓ²(ℕ)` and proved to be a contraction
  (`norm_pcnFunctionalCalculus_le`); `pcnFunctionalCalculus_pow` identifies `t ↦ tᵐ` with `Pᵐ`.
* **`integral_hermiteSpectralMeasure_eq_re_inner`** — **the change-of-variables formula**
  `∫ φ dμ_f = Re ⟪φ(P) f, f⟫` for **every** `φ` bounded by `1` on the spectrum — no continuity
  or measurability is needed, the measure being discrete — with the left side computed as
  `∑' n, φ(ρⁿ) ‖⟨eₙ, f⟩‖²` (`integral_hermiteSpectralMeasure_of_bound`).
* **`integral_hermiteSpectralMeasure_pow`** — **all the moments**: `∫ tᵐ dμ_f = Re ⟪Pᵐ f, f⟫` for
  every `m`, of which §16's first-moment identity is the case `m = 1`.
* `norm_kernelIntegral_le`, `norm_kernelIntegral_iterate_le` — **a pointwise bound survives the
  kernel action**, because every state measure of a Markov kernel is a probability measure.
* **`pcnIterateDensity_nonneg_of_bound`** — **the densities are nonnegative when `‖f‖∞ ≤ 1`**, so
  §13's `hpos` hypothesis is *proved* for bounded data rather than assumed.
* **`gaussianPCN_tv_geometric_convergence_of_bounded`** — **the TV rate with no modelling
  assumption**: mean-zero `f` bounded by `1` gives `‖ν m − π‖_TV ≤ ofReal ((‖f‖/2) |ρ|ᵐ)` with the
  densities constructed and their nonnegativity derived.
* `hermiteDiagB` — **the uniformly bounded Hermite-diagonal operator** on complex eigenvalue
  sequences (`hermiteDiagonal` is the bound-`1` real case), with `repr_hermiteDiagB`,
  `hasSum_hermiteDiagB`, `inner_hermiteDiagB` (`⟪eₙ, D f⟫ = μₙ ⟪eₙ, f⟫`) and the bound
  `norm_hermiteDiagB_le` (`‖D f‖ ≤ C ‖f‖` for `‖μₙ‖ ≤ C`).
* **`spectrum_gaussianPCNOp_eq_closure`** — **the spectrum is exactly the eigenvalue closure**:
  `spectrum ℂ P = closure {ρⁿ | n : ℕ}`.  The missing inclusion is proved by exhibiting the
  inverse of `λ • 1 − P` when `λ` is off that closure: on coordinates it multiplies by
  `λ − ρⁿ`, so the diagonal with coefficients `(λ − ρⁿ)⁻¹` inverts it
  (`exists_pos_le_norm_sub_eigenvalue`, `not_mem_spectrum_of_not_mem_closure`,
  `smul_one_sub_gaussianPCNOp_invertible`).
* **`spectrum_gaussianPCNOp_subset_closedBall`** — the spectrum lies in the closed unit disc.
* **`hermiteDiagBCLM`** — the uniformly bounded Hermite-diagonal operator as a **continuous linear
  map**, with `‖hermiteDiagBCLM μ‖ ≤ C` (`hermiteDiagB_add`, `hermiteDiagB_smul`,
  `hermiteDiagBCLM_apply`, `norm_hermiteDiagBCLM_le`).
* **`exists_resolvent_hermiteDiagB`** — **the resolvent of `P`, explicit and bounded**: for `λ` off
  `closure {ρⁿ}` there is `R` inverting `λ • 1 − P` on both sides with
  `‖R‖ ≤ (infDist λ {ρⁿ})⁻¹`.
* **`isCompactOperator_gaussianPCNOp`** — **`P` is a compact operator.**  Truncating the eigenvalue
  sequence gives the finite-rank operators `truncDiag ρ hρ1 N` (`truncDiag_apply`,
  `range_truncDiag_le_span`, `isCompactOperator_truncDiag`), and `‖P − truncDiag N‖ ≤ |ρ| ^ N → 0`
  (`norm_gaussianPCNOp_sub_truncDiag_le`, `tendsto_truncDiag`) makes `P` a norm limit of compact
  operators.  The finite-rank input `isCompactOperator_of_finiteDimensional_range` is proved here
  for arbitrary complex normed spaces, since Mathlib has no finite-rank form of it.
* **`spectrum_gaussianPCNOp_eq_insert_zero`** — for `|ρ| < 1` the spectrum is *exactly* the
  eigenvalue list together with `0`: `spectrum ℂ P = {0} ∪ {ρⁿ | n : ℕ}`.  The two ingredients are
  that the eigenvalue list is injective (`pow_ne_pow_of_abs_lt_one`) and separated
  (`norm_pow_sub_pow_ge`: `|ρ| ^ min m n * (1 - |ρ|) ≤ ‖ρᵐ - ρⁿ‖`).
* **`spectralRadius_gaussianPCNOp`** — **the spectral radius of `P` is `1`** (`1 = ρ⁰` is an
  eigenvalue; the spectrum lies in the closed unit disc).
* **`countable_spectrum_gaussianPCNOp`**, **`exists_ball_inter_spectrum_eq`**,
  **`zero_mem_closure_spectrum_diff`** — the compact-operator shape of the spectrum, read off the
  closed form above: it is **countable**, every **nonzero spectral point is isolated** (some ball
  around it meets the spectrum only at itself), and `0` **is** an accumulation point when `ρ ≠ 0`.
* **`exists_resolvent_norm_eq`** — **the resolvent norm identity**:
  `‖(λ • 1 − P)⁻¹‖ = (infDist λ {ρⁿ})⁻¹` for `λ` off `closure {ρⁿ}`, i.e.
  `‖(λ − P)⁻¹‖ = 1/dist(λ, σ P)`.  The lower bound `inv_infDist_le_norm_resolvent` comes from any
  right inverse acting diagonally (`apply_hermiteLpNorm_of_inverse`: `R eₙ = (λ − ρⁿ)⁻¹ • eₙ`, using
  `‖eₙ‖ = 1`).
* **`exists_selfAdjoint_resolvent_norm_eq`**, **`star_eq_self_of_inverse`** — for a **real**
  parameter the resolvent of the self-adjoint `P` is itself **self-adjoint** (`star R = R`), with
  the norm identity above.
* **`resolvent_sub_eq`**, **`resolvent_commute`**, **`norm_resolvent_sub_le`** — the **resolvent
  equation** `R(λ) − R(μ) = (μ − λ) R(λ) R(μ)` (proved algebraically, for any two-sided inverses),
  commutativity of resolvents at distinct parameters, and the Lipschitz bound
  `‖R(λ) − R(μ)‖ ≤ ‖μ − λ‖ ‖R(λ)‖ ‖R(μ)‖` (§23).
* **`norm_gaussianPCNOp_pow_le`**, **`opNorm_gaussianPCNOp_pow_le`** — **`P` is a contraction**:
  `‖Pᵏ f‖ ≤ ‖f‖` for every `f`, `k`, and `‖Pᵏ‖ ≤ 1` in operator norm (§24).
* **`summable_resolvent_series`**, **`hasSum_resolvent_series`**, **`norm_tsum_resolvent_series`** —
  **the Neumann series at infinity**: for `1 < ‖λ‖` the series `∑ₙ (λ ^ (n + 1))⁻¹ • Pⁿ` converges
  absolutely in operator norm to the resolvent of `λ • 1 − P` (partial sums telescope to
  `1 − (λ^N)⁻¹ P^N`), and its norm is `(infDist λ {ρⁿ})⁻¹` (§24).
* **`closure_range_pow_subset_closedUnitBall`**, **`resolvent_series_of_one_lt_norm`** — the
  **spectrum is bounded** by the closed unit disc, so every `λ` off it is in the resolvent set
  (§25).
* **`gaussianPCN_spectral_theorem`** — **the spectral theorem for `P` in measure form**: the three
  statements above, packaged: finite, supported on the eigenvalues, total mass `‖f‖²`, first moment
  the quadratic form.

## Honest boundary

* The contraction holds on the **mean-zero subspace** `{f | ⟨e₀, f⟩ = 0}`, not on all of `L²(π)`:
  the constant mode `e₀` is an eigenvalue of `P` with eigenvalue `1`, so no contraction is possible
  there.  `‖P e₁‖ = |ρ| ‖e₁‖` shows the constant `|ρ|` is attained, so it is the optimal factor on
  the mean-zero subspace.
* The eigenvalue list is proved to be exactly `{ρⁿ | n : ℕ}` (`gaussianPCNOp_eigenvalue_eq_rho_pow`)
  and `0` is proved to lie in the spectrum (`zero_mem_spectrum_gaussianPCNOp`).  For `ρ ≠ 0` that
  `0` is *not* an eigenvalue (`zero_not_eigenvalue_gaussianPCNOp`), so it is a genuine accumulation
  point; for `ρ = 0` the eigenvalue `0` already occurs at `n ≥ 1`.  §19 completes the picture:
  `spectrum ℂ P` is exactly `closure {ρⁿ | n : ℕ}` (`spectrum_gaussianPCNOp_eq_closure`), hence
  contained in the closed unit disc.  §20 adds the quantitative half: the resolvent is exhibited
  explicitly and bounded, `‖(λ − P)⁻¹‖ ≤ (infDist λ {ρⁿ})⁻¹`, and `P` is **compact**
  (`isCompactOperator_gaussianPCNOp`), and §22 sharpens it to an **identity**,
  `‖(λ − P)⁻¹‖ = (infDist λ {ρⁿ})⁻¹`, with the resolvent at a real parameter self-adjoint — both
  proved from the diagonal form, not from an abstract spectral theorem.  §21 then gives the spectrum
  the shape compact operators
  usually have — countable, spectral radius `1`, nonzero points isolated, `0` the only possible
  accumulation point — but it does so by reading the closed form `spectrum = {0} ∪ {ρⁿ}` off §19,
  *not* through Riesz/Fredholm theory.  In particular the hypothesis `|ρ| < 1` is assumed, not
  derived from compactness: for `|ρ| = 1` the spectrum is the unit circle, and turning that into a
  contradiction with compactness is precisely the Fredholm input that is **not** formalized.  No
  Gelfand formula `spectralRadius = lim ‖Pⁿ‖ ^ (1/n)`, no essential spectrum, no spectral
  projections.  §23 supplies the resolvent equation and §24 the power series at infinity: for
  `1 < ‖λ‖` the Neumann series `∑ₙ (λ ^ (n + 1))⁻¹ • Pⁿ` converges in operator norm to the resolvent
  and has norm `(infDist λ {ρⁿ})⁻¹`.  That is analyticity in its *power-series* form only: no
  differentiability statement for `λ ↦ R(λ)` is formalized, the series is only used on
  `1 < ‖λ‖`, and no analytic continuation to the rest of the resolvent set is
  performed.  The self-adjointness
  statement needs a real parameter — for non-real `λ` the resolvent is not self-adjoint.
* The spectral measure is *discrete by construction* — a `Measure.sum` of weighted Diracs over
  `ℕ` — and its total mass and all its moments are computed.  The functional calculus is built for
  `φ` bounded by `1` on the spectrum only; general bounded `φ` is the scaled case and is not
  stated, no spectral projections or polar decompositions are defined, and Mathlib's abstract
  spectral theorem is not invoked.  The calculus is *not* extended to unbounded `φ` (so `P`'s
  inverse or `log P` are not available), and `φ(P)` is only compared with `Pᵐ` for `φ = tᵐ`.
* The identity `∫ φ dμ_f = Re ⟪φ(P) f, f⟫` needs **no regularity of `φ`** beyond the bound on the
  spectrum: `μ_f` is a countable sum of weighted Dirac masses, so `φ` is automatically integrable
  (`aestronglyMeasurable_sum_measure_iff`, `AEStronglyMeasurable.smul_measure`) and only its
  values at the eigenvalues matter.  What is *not* claimed is the corresponding statement for a
  general (non-discrete) spectral measure, where measurability would have to be assumed.
* Positivity needs `ρ ≥ 0` as an extra hypothesis, which is *not* implied by `ρ² + s² = 1` and
  `s ≠ 0`: for `ρ < 0` the operator is indefinite, the odd modes carrying negative eigenvalues.
  Mathlib's `ContinuousLinearMap.IsPositive` is stated only for real scalars (`LE 𝕜`), so
  `gaussianPCNOp_isPositiveOp` records the two components (self-adjointness and the nonnegative
  quadratic form) rather than that predicate; it is not a C*-algebraic positivity statement.
* The total-variation statement `gaussianPCN_tv_geometric_convergence` keeps its transport as a
  hypothesis `hdnorm`; the transport itself is proved in §14 and used in
  `gaussianPCN_tv_geometric_convergence_of_density`, which constructs the densities.  What remains
  there is `hpos`: the constructed densities are nonnegative.  That is a statement about the model
  (the deviation stays above `-1`), not an analytic identity, and it is not implied by `f ∈ L²`.
  The *rate* `|ρ|ᵐ` is never assumed — it is derived from
  `norm_gaussianPCNOp_pow_le_of_inner_eq_zero`.  The density deviation is the real part of `Pᵐ f`,
  so its `L²` norm is only bounded by `‖Pᵐ f‖`, not equal to it; the total-variation bound survives
  because that is the direction it needs.  Nothing about almost-sure convergence, mixing time, or
  chains started from non-`L²` laws is claimed.
* `hpos` is replaced by a hypothesis in `gaussianPCN_tv_geometric_convergence_of_bounded`: the
  *representative* of `f` is bounded by `1` in sup-norm.  This is a smallness condition on the
  input, not an assumption about the chain, and it is what the kernel argument needs — a pointwise
  bound is propagated by the kernel, while an `L²` bound is not (the `pCN` transition density has
  unbounded `L²(π)` norm in `x`, so small `‖f‖₂` does not bound the deviation pointwise).  Note
  that the hypothesis is about the chosen representative of the `Lp` class, since the constructed
  density is too; it is not invariant under changing representatives.
* The hypotheses are `ρ² + s² = 1` and `s ≠ 0` (nondegenerate proposal).  The `s = 0` step is an
  isometry (`GaussianPCNSpectrum.gaussianPCNOpZero`), so no decay is claimed there; its `k`-step
  mode transport is recorded in §7.
-/

noncomputable section

namespace BookProof.MCMC

open MeasureTheory ProbabilityTheory Filter
open scoped ENNReal NNReal Polynomial Topology

/-! ## 1. The rate `|ρ| < 1` -/

/-- **The nondegenerate pCN multiplier has `|ρ| < 1`.**  From `ρ² + s² = 1` and `s ≠ 0`,
`ρ² < 1`. -/
theorem abs_rho_lt_one {ρ s : ℝ} (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) : |ρ| < 1 := by
  have hs2 : 0 < s ^ 2 := by positivity
  rw [abs_lt]
  constructor <;> nlinarith

/-- **Geometric monotonicity**: `|ρ|ⁿ ≤ |ρ|` for `n ≥ 1` when `|ρ| ≤ 1`. -/
theorem abs_rho_pow_le {ρ s : ℝ} (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) {n : ℕ} (hn : 1 ≤ n) :
    |ρ| ^ n ≤ |ρ| :=
  pow_le_of_le_one (abs_nonneg ρ) (abs_rho_lt_one hρs hs).le
    (Nat.one_le_iff_ne_zero.mp hn)

/-! ## 2. The orthonormal Hermite family in `L²(π)` -/

/-- The **normalised Hermite classes** `[Heₙ] / √(n!)`: the orthonormal system of eigenfunctions
of the pCN operator. -/
noncomputable def hermiteLpNorm (n : ℕ) : Lp ℂ 2 (gaussianReal 0 1) :=
  ((Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) •
    MemLp.toLp (hermiteRealComplex n) (memLp_two_hermiteReal n)

/-- The `Lp` inner product of two unnormalised Hermite classes: `⟪[Heₘ], [Heₙ]⟫ = δₘₙ n!`. -/
theorem inner_hermiteLp (m n : ℕ) :
    inner ℂ (MemLp.toLp (hermiteRealComplex m) (memLp_two_hermiteReal m))
        (MemLp.toLp (hermiteRealComplex n) (memLp_two_hermiteReal n))
      = if m = n then ((n.factorial : ℝ) : ℂ) else 0 := by
  rw [L2.inner_def]
  refine (integral_congr_ae ?_).trans (integral_hermiteRealComplex_mul m n)
  filter_upwards [MemLp.coeFn_toLp (memLp_two_hermiteReal m),
    MemLp.coeFn_toLp (memLp_two_hermiteReal n)] with x h1 h2
  rw [h1, h2, RCLike.inner_apply]
  simp only [hermiteRealComplex_apply, Complex.conj_ofReal]
  ring

/-- **Orthonormal in `Lp ℂ 2 π`**: `⟪[Heₘ]/√m!, [Heₙ]/√n!⟫ = δₘₙ`. -/
theorem inner_hermiteLpNorm (m n : ℕ) :
    inner ℂ (hermiteLpNorm m) (hermiteLpNorm n) = if m = n then 1 else 0 := by
  have hfac : ∀ k : ℕ, (0 : ℝ) < (k.factorial : ℝ) := fun k => by positivity
  rw [hermiteLpNorm, hermiteLpNorm, inner_smul_left, inner_smul_right, inner_hermiteLp]
  simp only [← Complex.ofReal_inv, Complex.conj_ofReal]
  by_cases h : m = n
  · rw [if_pos h, if_pos h, h]
    have hprod : (Real.sqrt (n.factorial : ℝ))⁻¹ *
        ((Real.sqrt (n.factorial : ℝ))⁻¹ * (n.factorial : ℝ)) = 1 := by
      have hs : Real.sqrt (n.factorial : ℝ) ≠ 0 :=
        ne_of_gt (Real.sqrt_pos.2 (hfac n))
      field_simp
      rw [Real.sq_sqrt (hfac n).le]
    rw [← Complex.ofReal_mul, ← Complex.ofReal_mul, hprod, Complex.ofReal_one]
  · rw [if_neg h, if_neg h]
    ring

/-- The normalised Hermite classes are orthonormal in `Lp ℂ 2 π`. -/
theorem orthonormal_hermiteLpNorm : Orthonormal ℂ hermiteLpNorm := by
  rw [orthonormal_iff_ite]
  exact inner_hermiteLpNorm

/-- **The eigenrelation in the orthonormal scale**: `P eₙ = ρⁿ • eₙ`. -/
theorem gaussianPCNOp_hermiteLpNorm (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (n : ℕ) :
    gaussianPCNOp ρ s hρs hs (hermiteLpNorm n) = (ρ : ℂ) ^ n • hermiteLpNorm n := by
  rw [hermiteLpNorm, map_smul, gaussianPCNOp_hermiteReal, smul_smul, smul_smul, mul_comm]

/-- **The mode rate**: each normalised eigenfunction decays geometrically,
`‖P eₙ‖ = |ρ|ⁿ ‖eₙ‖`. -/
theorem norm_gaussianPCNOp_hermiteLpNorm (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (n : ℕ) :
    ‖gaussianPCNOp ρ s hρs hs (hermiteLpNorm n)‖ = |ρ| ^ n * ‖hermiteLpNorm n‖ := by
  rw [gaussianPCNOp_hermiteLpNorm, norm_smul, norm_pow]
  congr 1
  rw [Complex.norm_real, Real.norm_eq_abs]

/-! ## 3. The contraction at rate `|ρ|` on non-constant Hermite combinations -/

/-- `‖z‖²` of a complex number is the real part of `conj z * z`. -/
theorem re_conj_mul_self (z : ℂ) : (starRingEnd ℂ z * z).re = ‖z‖ ^ 2 := by
  rw [Complex.sq_norm, Complex.normSq_apply]
  simp [Complex.mul_re, Complex.conj_re, Complex.conj_im]

/-- **The spectral gap on non-constant Hermite combinations.**  For a finite combination
`f = Σ_{n ∈ S} cₙ eₙ` of normalised Hermite classes with `0 ∉ S`, the pCN operator contracts by
the sharp factor `|ρ| < 1`: `‖P f‖ ≤ |ρ| ‖f‖`. -/
theorem norm_gaussianPCNOp_finset_sum_le {ρ s : ℝ} (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ n) (c : ℕ → ℂ) :
    ‖gaussianPCNOp ρ s hρs hs (∑ n ∈ S, c n • hermiteLpNorm n)‖
      ≤ |ρ| * ‖∑ n ∈ S, c n • hermiteLpNorm n‖ := by
  set f : Lp ℂ 2 (gaussianReal 0 1) := ∑ n ∈ S, c n • hermiteLpNorm n with hf
  have hPf : gaussianPCNOp ρ s hρs hs f
      = ∑ n ∈ S, (c n * (ρ : ℂ) ^ n) • hermiteLpNorm n := by
    rw [hf, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_smul, gaussianPCNOp_hermiteLpNorm, smul_smul]
  have hnorm_f : ‖f‖ ^ 2 = ∑ n ∈ S, ‖c n‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) f, hf,
      Orthonormal.inner_sum orthonormal_hermiteLpNorm c c S]
    show (∑ n ∈ S, (starRingEnd ℂ) (c n) * c n).re = ∑ n ∈ S, ‖c n‖ ^ 2
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun n _ => re_conj_mul_self (c n)
  have hnorm_Pf : ‖gaussianPCNOp ρ s hρs hs f‖ ^ 2
      = ∑ n ∈ S, ‖c n * (ρ : ℂ) ^ n‖ ^ 2 := by
    rw [← inner_self_eq_norm_sq (𝕜 := ℂ) (gaussianPCNOp ρ s hρs hs f), hPf,
      Orthonormal.inner_sum orthonormal_hermiteLpNorm
        (fun n => c n * (ρ : ℂ) ^ n) (fun n => c n * (ρ : ℂ) ^ n) S]
    show (∑ n ∈ S, (starRingEnd ℂ) (c n * (ρ : ℂ) ^ n) * (c n * (ρ : ℂ) ^ n)).re
        = ∑ n ∈ S, ‖c n * (ρ : ℂ) ^ n‖ ^ 2
    rw [Complex.re_sum]
    exact Finset.sum_congr rfl fun n _ => re_conj_mul_self (c n * (ρ : ℂ) ^ n)
  have hle : ∑ n ∈ S, ‖c n * (ρ : ℂ) ^ n‖ ^ 2 ≤ |ρ| ^ 2 * ∑ n ∈ S, ‖c n‖ ^ 2 := by
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun n hn => ?_
    have hρn : ‖(ρ : ℂ) ^ n‖ ≤ |ρ| := by
      rw [norm_pow, Complex.norm_real]
      exact abs_rho_pow_le hρs hs (hS n hn)
    have hstep : ‖c n * (ρ : ℂ) ^ n‖ ≤ |ρ| * ‖c n‖ := by
      rw [norm_mul, mul_comm]
      exact mul_le_mul_of_nonneg_right hρn (norm_nonneg _)
    calc ‖c n * (ρ : ℂ) ^ n‖ ^ 2 ≤ (|ρ| * ‖c n‖) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) hstep 2
      _ = |ρ| ^ 2 * ‖c n‖ ^ 2 := by ring
  have hsq : ‖gaussianPCNOp ρ s hρs hs f‖ ^ 2 ≤ (|ρ| * ‖f‖) ^ 2 := by
    calc ‖gaussianPCNOp ρ s hρs hs f‖ ^ 2
        = ∑ n ∈ S, ‖c n * (ρ : ℂ) ^ n‖ ^ 2 := hnorm_Pf
      _ ≤ |ρ| ^ 2 * ∑ n ∈ S, ‖c n‖ ^ 2 := hle
      _ = |ρ| ^ 2 * ‖f‖ ^ 2 := by rw [← hnorm_f]
      _ = (|ρ| * ‖f‖) ^ 2 := by ring
  calc ‖gaussianPCNOp ρ s hρs hs f‖
      = Real.sqrt (‖gaussianPCNOp ρ s hρs hs f‖ ^ 2) := (Real.sqrt_sq (norm_nonneg _)).symm
    _ ≤ Real.sqrt ((|ρ| * ‖f‖) ^ 2) := Real.sqrt_le_sqrt hsq
    _ = |ρ| * ‖f‖ := Real.sqrt_sq (by positivity)

/-! ## 4. The `k`-step rate -/

/-- **The `k`-step mode rate**: `Pᵏ eₙ = ρ^{kn} • eₙ`. -/
theorem gaussianPCNOp_pow_hermiteLpNorm (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (k n : ℕ) :
    ((gaussianPCNOp ρ s hρs hs) ^ k) (hermiteLpNorm n)
      = (ρ : ℂ) ^ (k * n) • hermiteLpNorm n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, ih, map_smul,
      gaussianPCNOp_hermiteLpNorm, smul_smul, ← pow_add, Nat.succ_mul]

/-- **`Pᵏ` on a finite Hermite combination** keeps the same shape, with each coefficient scaled
by `ρ^{kn}`. -/
theorem gaussianPCNOp_pow_finset_sum (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (k : ℕ) (S : Finset ℕ) (c : ℕ → ℂ) :
    ((gaussianPCNOp ρ s hρs hs) ^ k) (∑ n ∈ S, c n • hermiteLpNorm n)
      = ∑ n ∈ S, (c n * (ρ : ℂ) ^ (k * n)) • hermiteLpNorm n := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ', ContinuousLinearMap.mul_apply, ih, map_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [map_smul, gaussianPCNOp_hermiteLpNorm, smul_smul, mul_assoc, ← pow_add, Nat.succ_mul]

/-- **The exponential contraction rate**: on a non-constant finite Hermite combination,
`‖Pᵏ f‖ ≤ |ρ|ᵏ ‖f‖` for every `k`. -/
theorem norm_gaussianPCNOp_pow_finset_sum_le {ρ s : ℝ} (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (k : ℕ) (S : Finset ℕ) (hS : ∀ n ∈ S, 1 ≤ n) (c : ℕ → ℂ) :
    ‖((gaussianPCNOp ρ s hρs hs) ^ k) (∑ n ∈ S, c n • hermiteLpNorm n)‖
      ≤ |ρ| ^ k * ‖∑ n ∈ S, c n • hermiteLpNorm n‖ := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hpow := gaussianPCNOp_pow_finset_sum ρ s hρs hs k S c
    rw [pow_succ', ContinuousLinearMap.mul_apply, hpow]
    calc ‖gaussianPCNOp ρ s hρs hs
          (∑ n ∈ S, (c n * (ρ : ℂ) ^ (k * n)) • hermiteLpNorm n)‖
        ≤ |ρ| * ‖∑ n ∈ S, (c n * (ρ : ℂ) ^ (k * n)) • hermiteLpNorm n‖ :=
          norm_gaussianPCNOp_finset_sum_le hρs hs S hS (fun n => c n * (ρ : ℂ) ^ (k * n))
      _ = |ρ| * ‖((gaussianPCNOp ρ s hρs hs) ^ k) (∑ n ∈ S, c n • hermiteLpNorm n)‖ := by
          rw [hpow]
      _ ≤ |ρ| * (|ρ| ^ k * ‖∑ n ∈ S, c n • hermiteLpNorm n‖) :=
          mul_le_mul_of_nonneg_left ih (abs_nonneg ρ)
      _ = |ρ| ^ (k + 1) * ‖∑ n ∈ S, c n • hermiteLpNorm n‖ := by ring

/-! ## 5. The Hilbert basis and the diagonalisation

`dense_span_hermiteReal` gives density of the span of the *unnormalised* classes; the normalised
classes span the same subspace, so `orthonormal_hermiteLpNorm` + density give a
`HilbertBasis` of `L²(π)`, and the eigenrelation turns into a series expansion of `P`.
-/

/-- The normalised and unnormalised Hermite classes span the same subspace of `L²(π)`: each is a
nonzero complex multiple of the other. -/
theorem span_hermiteLpNorm_eq_span_toLp :
    Submodule.span ℂ (Set.range hermiteLpNorm)
      = Submodule.span ℂ (Set.range (fun n : ℕ =>
          MemLp.toLp (hermiteRealComplex n) (memLp_two_hermiteReal n))) := by
  refine Submodule.span_eq_span ?_ ?_
  · rintro _ ⟨n, rfl⟩
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨n, rfl⟩)
  · rintro _ ⟨n, rfl⟩
    have hfac : (0 : ℝ) < (n.factorial : ℝ) := by positivity
    have hsqrt : Real.sqrt (n.factorial : ℝ) ≠ 0 := (Real.sqrt_pos.2 hfac).ne'
    have hc : ((Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ) ≠ 0 := by
      simpa using inv_ne_zero hsqrt
    have hmem : hermiteLpNorm n ∈ Submodule.span ℂ (Set.range hermiteLpNorm) :=
      Submodule.subset_span ⟨n, rfl⟩
    have h := Submodule.smul_mem (Submodule.span ℂ (Set.range hermiteLpNorm))
      (((Real.sqrt (n.factorial : ℝ))⁻¹ : ℂ)⁻¹) hmem
    rwa [hermiteLpNorm, smul_smul, inv_mul_cancel₀ hc, one_smul] at h

/-- **The normalised Hermite classes are dense in `L²(π)`**. -/
theorem dense_span_hermiteLpNorm :
    ⊤ ≤ (Submodule.span ℂ (Set.range hermiteLpNorm)).topologicalClosure := by
  rw [span_hermiteLpNorm_eq_span_toLp]
  exact dense_span_hermiteReal

/-- **The Hermite classes form a Hilbert basis of `L²(π)`**: the orthonormal family `eₙ = [Heₙ]/√n!`
with dense span, packaged as a `HilbertBasis`. -/
noncomputable def gaussianPCNHilbertBasis :
    HilbertBasis ℕ ℂ (Lp ℂ 2 (gaussianReal 0 1)) :=
  HilbertBasis.mk orthonormal_hermiteLpNorm dense_span_hermiteLpNorm

@[simp]
theorem gaussianPCNHilbertBasis_apply (n : ℕ) :
    gaussianPCNHilbertBasis n = hermiteLpNorm n := by
  simp [gaussianPCNHilbertBasis]

/-- **The diagonalisation of the pCN operator**: every `f ∈ L²(π)` expands in the Hermite basis
with coefficients `⟨eₙ, f⟩`, and `P` acts diagonally with eigenvalues `ρⁿ`:
`P f = ∑' n, (⟨eₙ, f⟩ ρⁿ) eₙ`. -/
theorem gaussianPCNOp_eq_tsum (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (f : Lp ℂ 2 (gaussianReal 0 1)) :
    gaussianPCNOp ρ s hρs hs f
      = ∑' n, (inner ℂ (hermiteLpNorm n) f * (ρ : ℂ) ^ n) • hermiteLpNorm n := by
  have hsum : HasSum (fun n => inner ℂ (hermiteLpNorm n) f • hermiteLpNorm n) f :=
    by
      have h := gaussianPCNHilbertBasis.hasSum_repr f
      simpa [HilbertBasis.repr_apply_apply] using h
  conv_lhs => rw [← hsum.tsum_eq]
  rw [ContinuousLinearMap.map_tsum (gaussianPCNOp ρ s hρs hs) hsum.summable]
  exact tsum_congr fun n => by
    rw [map_smul, gaussianPCNOp_hermiteLpNorm, smul_smul]

/-- The basis expansion of an `L²(π)` function in the normalised Hermite classes. -/
theorem hasSum_hermiteLpNorm (f : Lp ℂ 2 (gaussianReal 0 1)) :
    HasSum (fun n => inner ℂ (hermiteLpNorm n) f • hermiteLpNorm n) f :=
  by
    have h := gaussianPCNHilbertBasis.hasSum_repr f
    simpa [HilbertBasis.repr_apply_apply] using h

/-! ## 6. The contraction on the whole mean-zero subspace

The finite-combination bound plus closedness of `{g | ‖P g‖ ≤ |ρ| ‖g‖}` upgrades the estimate to
every `f` orthogonal to the constant mode, because `f` is a limit of finite partial sums of its
Hermite expansion and the terms with `n = 0` vanish on that space.
-/

/-- **The spectral gap on the whole mean-zero subspace**: if `f ⊥ e₀` then `‖P f‖ ≤ |ρ| ‖f‖`. -/
theorem norm_gaussianPCNOp_le_of_inner_eq_zero (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1)
    (hs : s ≠ 0) {f : Lp ℂ 2 (gaussianReal 0 1)}
    (h0 : inner ℂ (hermiteLpNorm 0) f = 0) :
    ‖gaussianPCNOp ρ s hρs hs f‖ ≤ |ρ| * ‖f‖ := by
  set c : ℕ → ℂ := fun n => inner ℂ (hermiteLpNorm n) f with hc
  have hc0 : c 0 = 0 := by simpa [hc] using h0
  have hclosed : IsClosed {g : Lp ℂ 2 (gaussianReal 0 1) |
      ‖gaussianPCNOp ρ s hρs hs g‖ ≤ |ρ| * ‖g‖} := by
    refine isClosed_le (gaussianPCNOp ρ s hρs hs).continuous.norm ?_
    exact continuous_const.mul continuous_norm
  have hzero : ∀ n : ℕ, (∑ i ∈ Finset.range n, c i • hermiteLpNorm i)
      = ∑ i ∈ (Finset.range n).erase 0, c i • hermiteLpNorm i := by
    have hz : c 0 • hermiteLpNorm 0 = 0 := by rw [hc0, zero_smul]
    exact fun n => (Finset.sum_erase (Finset.range n) hz).symm
  have htend : Tendsto
      (fun n : ℕ => ∑ i ∈ (Finset.range n).erase 0, c i • hermiteLpNorm i) atTop (𝓝 f) := by
    have hfun : (fun n : ℕ => ∑ i ∈ (Finset.range n).erase 0, c i • hermiteLpNorm i)
        = fun n : ℕ => ∑ i ∈ Finset.range n, c i • hermiteLpNorm i :=
      funext fun n => (hzero n).symm
    rw [hfun]
    exact (hasSum_hermiteLpNorm f).tendsto_sum_nat
  refine hclosed.mem_of_tendsto htend (Eventually.of_forall fun n => ?_)
  refine norm_gaussianPCNOp_finset_sum_le hρs hs ((Finset.range n).erase 0) ?_ c
  intro i hi
  exact Nat.one_le_iff_ne_zero.mpr (Finset.ne_of_mem_erase hi)

/-- **The `k`-step exponential rate on the whole mean-zero subspace**: for `f ⊥ e₀`,
`‖Pᵏ f‖ ≤ |ρ|ᵏ ‖f‖` for every `k`. -/
theorem norm_gaussianPCNOp_pow_le_of_inner_eq_zero (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1)
    (hs : s ≠ 0) (k : ℕ) {f : Lp ℂ 2 (gaussianReal 0 1)}
    (h0 : inner ℂ (hermiteLpNorm 0) f = 0) :
    ‖((gaussianPCNOp ρ s hρs hs) ^ k) f‖ ≤ |ρ| ^ k * ‖f‖ := by
  set c : ℕ → ℂ := fun n => inner ℂ (hermiteLpNorm n) f with hc
  have hc0 : c 0 = 0 := by simpa [hc] using h0
  have hclosed : IsClosed {g : Lp ℂ 2 (gaussianReal 0 1) |
      ‖((gaussianPCNOp ρ s hρs hs) ^ k) g‖ ≤ |ρ| ^ k * ‖g‖} := by
    refine isClosed_le ((gaussianPCNOp ρ s hρs hs) ^ k).continuous.norm ?_
    exact continuous_const.mul continuous_norm
  have hzero : ∀ n : ℕ, (∑ i ∈ Finset.range n, c i • hermiteLpNorm i)
      = ∑ i ∈ (Finset.range n).erase 0, c i • hermiteLpNorm i := by
    have hz : c 0 • hermiteLpNorm 0 = 0 := by rw [hc0, zero_smul]
    exact fun n => (Finset.sum_erase (Finset.range n) hz).symm
  have htend : Tendsto
      (fun n : ℕ => ∑ i ∈ (Finset.range n).erase 0, c i • hermiteLpNorm i) atTop (𝓝 f) := by
    have hfun : (fun n : ℕ => ∑ i ∈ (Finset.range n).erase 0, c i • hermiteLpNorm i)
        = fun n : ℕ => ∑ i ∈ Finset.range n, c i • hermiteLpNorm i :=
      funext fun n => (hzero n).symm
    rw [hfun]
    exact (hasSum_hermiteLpNorm f).tendsto_sum_nat
  refine hclosed.mem_of_tendsto htend (Eventually.of_forall fun n => ?_)
  refine norm_gaussianPCNOp_pow_finset_sum_le hρs hs k ((Finset.range n).erase 0) ?_ c
  intro i hi
  exact Nat.one_le_iff_ne_zero.mpr (Finset.ne_of_mem_erase hi)

/-! ## 7. The `s = 0` isometry: mode transport -/

/-- **The `k`-step degenerate mode rate** in the orthonormal scale:
`P₀ᵏ eₙ = ρ^{kn} • eₙ`.  Since `P₀` is an isometry there is no decay here, only the transported
eigenvalue. -/
theorem gaussianPCNOpZero_pow_hermiteLpNorm (ρ : ℝ) (hρ : ρ ^ 2 = 1) (k n : ℕ) :
    ((gaussianPCNOpZero ρ hρ) ^ k) (hermiteLpNorm n) = (ρ : ℂ) ^ (k * n) • hermiteLpNorm n := by
  rw [hermiteLpNorm, map_smul, gaussianPCNOpZero_pow_toLp, smul_smul, smul_smul]
  congr 1
  rw [← Complex.ofReal_pow, mul_comm]

/-! ## 8. Parseval: the Hermite coefficients are an `ℓ²` isometry

`HilbertBasis.tsum_inner_mul_inner` computes `⟪f, f⟫` as the sum of the coefficient products;
identifying `‖f‖²` with that complex number turns it into `∑ₙ ‖⟨eₙ, f⟩‖² = ‖f‖²`.
-/

/-- `‖z‖²`, read as a complex number, is `conj z * z`. -/
theorem ofReal_norm_sq_eq_conj_mul_self (z : ℂ) :
    ((‖z‖ ^ 2 : ℝ) : ℂ) = (starRingEnd ℂ z) * z := by
  rw [Complex.sq_norm, Complex.normSq_eq_conj_mul_self]

/-- **Parseval for the pCN Hermite basis**: `∑' n, ‖⟨eₙ, f⟩‖² = ‖f‖²`.  Equivalently, the
coefficient map `f ↦ (⟨eₙ, f⟩)ₙ` is an isometry of `L²(π)` into `ℓ²(ℕ)`. -/
theorem tsum_norm_inner_hermiteLpNorm (f : Lp ℂ 2 (gaussianReal 0 1)) :
    ∑' n, ‖inner ℂ (hermiteLpNorm n) f‖ ^ 2 = ‖f‖ ^ 2 := by
  have hself : inner ℂ f f = ((‖f‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
    rfl
  have hcoe : ((∑' n, ‖inner ℂ (hermiteLpNorm n) f‖ ^ 2 : ℝ) : ℂ)
      = ∑' n, inner ℂ f (hermiteLpNorm n) * inner ℂ (hermiteLpNorm n) f := by
    rw [Complex.ofReal_tsum]
    refine tsum_congr fun n => ?_
    rw [← inner_conj_symm (𝕜 := ℂ) f (hermiteLpNorm n)]
    exact ofReal_norm_sq_eq_conj_mul_self _
  have htotal : (∑' n, inner ℂ f (hermiteLpNorm n) * inner ℂ (hermiteLpNorm n) f)
      = ((‖f‖ ^ 2 : ℝ) : ℂ) := by
    have h := gaussianPCNHilbertBasis.tsum_inner_mul_inner f f
    simpa [hself] using h
  exact Complex.ofReal_injective (hcoe.trans htotal)

/-! ## 9. `P` is self-adjoint

Only the forward eigenrelation is known; but `P` acts by `ρⁿ` on `eₙ` with the eigenvalues `ρⁿ`
real, and that is enough for symmetry.  Each side of `⟨P f, g⟩ = ⟨f, P g⟩` is evaluated by
expanding `P` applied to one argument, and the two sums agree termwise.
-/

/-- **The diagonal form as a `HasSum`**: the expansion of `P f` in the Hermite basis. -/
theorem hasSum_gaussianPCNOp (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (f : Lp ℂ 2 (gaussianReal 0 1)) :
    HasSum (fun n => (inner ℂ (hermiteLpNorm n) f * (ρ : ℂ) ^ n) • hermiteLpNorm n)
      (gaussianPCNOp ρ s hρs hs f) := by
  have h := (hasSum_hermiteLpNorm f).map (gaussianPCNOp ρ s hρs hs)
    (gaussianPCNOp ρ s hρs hs).continuous
  have hcomp :
      (⇑(gaussianPCNOp ρ s hρs hs) ∘ fun n => inner ℂ (hermiteLpNorm n) f • hermiteLpNorm n)
        = fun n => (inner ℂ (hermiteLpNorm n) f * (ρ : ℂ) ^ n) • hermiteLpNorm n := by
    funext n
    rw [Function.comp_apply, map_smul, gaussianPCNOp_hermiteLpNorm, smul_smul]
  rw [hcomp] at h
  exact h

/-- **`P` is symmetric**: `⟨P f, g⟩ = ⟨f, P g⟩` for all `f, g ∈ L²(π)`. -/
theorem inner_gaussianPCNOp_comm (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (f g : Lp ℂ 2 (gaussianReal 0 1)) :
    inner ℂ (gaussianPCNOp ρ s hρs hs f) g = inner ℂ f (gaussianPCNOp ρ s hρs hs g) := by
  set c : ℕ → ℂ := fun n => inner ℂ (hermiteLpNorm n) f with hc
  set d : ℕ → ℂ := fun n => inner ℂ (hermiteLpNorm n) g with hd
  have hge : ∀ n : ℕ, inner ℂ g (hermiteLpNorm n) = (starRingEnd ℂ) (d n) := by
    intro n
    have h : (starRingEnd ℂ) (inner ℂ g (hermiteLpNorm n)) = d n := by
      rw [inner_conj_symm]
    calc inner ℂ g (hermiteLpNorm n)
        = (starRingEnd ℂ) ((starRingEnd ℂ) (inner ℂ g (hermiteLpNorm n))) :=
          (Complex.conj_conj _).symm
      _ = (starRingEnd ℂ) (d n) := by rw [h]
  have htermL : ∀ n : ℕ,
      (starRingEnd ℂ) ((innerSL ℂ g) ((c n * (ρ : ℂ) ^ n) • hermiteLpNorm n))
        = (starRingEnd ℂ (c n)) * d n * (ρ : ℂ) ^ n := by
    intro n
    rw [innerSL_apply_apply, inner_smul_right, hge n]
    simp only [map_mul, map_pow, Complex.conj_conj, Complex.conj_ofReal]
    ring
  have hL : inner ℂ (gaussianPCNOp ρ s hρs hs f) g
      = ∑' n, inner ℂ f (hermiteLpNorm n) * d n * (ρ : ℂ) ^ n := by
    have hh := (hasSum_gaussianPCNOp ρ s hρs hs f).map (innerSL ℂ g)
      (innerSL ℂ g).continuous
    have hhsum : (∑' n, (innerSL ℂ g) ((c n * (ρ : ℂ) ^ n) • hermiteLpNorm n))
        = (innerSL ℂ g) (gaussianPCNOp ρ s hρs hs f) := by
      simpa only [Function.comp_def, innerSL_apply_apply] using hh.tsum_eq
    have hval : (starRingEnd ℂ) ((innerSL ℂ g) (gaussianPCNOp ρ s hρs hs f))
        = inner ℂ (gaussianPCNOp ρ s hρs hs f) g := by
      rw [innerSL_apply_apply]
      exact inner_conj_symm (𝕜 := ℂ) (gaussianPCNOp ρ s hρs hs f) g
    calc inner ℂ (gaussianPCNOp ρ s hρs hs f) g
        = (starRingEnd ℂ) ((innerSL ℂ g) (gaussianPCNOp ρ s hρs hs f)) := hval.symm
      _ = (starRingEnd ℂ) (∑' n, (innerSL ℂ g)
            ((c n * (ρ : ℂ) ^ n) • hermiteLpNorm n)) := by rw [hhsum]
      _ = ∑' n, (starRingEnd ℂ) ((innerSL ℂ g)
            ((c n * (ρ : ℂ) ^ n) • hermiteLpNorm n)) := Complex.conj_tsum _
      _ = ∑' n, (starRingEnd ℂ (c n)) * d n * (ρ : ℂ) ^ n := tsum_congr htermL
      _ = ∑' n, inner ℂ f (hermiteLpNorm n) * d n * (ρ : ℂ) ^ n := by
            refine tsum_congr fun n => ?_
            rw [hc, inner_conj_symm]
  have hR : inner ℂ f (gaussianPCNOp ρ s hρs hs g)
      = ∑' n, inner ℂ f (hermiteLpNorm n) * d n * (ρ : ℂ) ^ n := by
    have hh := (hasSum_gaussianPCNOp ρ s hρs hs g).map (innerSL ℂ f)
      (innerSL ℂ f).continuous
    have hhsum : (∑' n, (innerSL ℂ f) ((d n * (ρ : ℂ) ^ n) • hermiteLpNorm n))
        = (innerSL ℂ f) (gaussianPCNOp ρ s hρs hs g) := by
      simpa only [Function.comp_def, innerSL_apply_apply] using hh.tsum_eq
    have hterm : ∀ n : ℕ, (innerSL ℂ f) ((d n * (ρ : ℂ) ^ n) • hermiteLpNorm n)
        = inner ℂ f (hermiteLpNorm n) * d n * (ρ : ℂ) ^ n := by
      intro n
      rw [innerSL_apply_apply, inner_smul_right]
      ring
    calc inner ℂ f (gaussianPCNOp ρ s hρs hs g)
        = (innerSL ℂ f) (gaussianPCNOp ρ s hρs hs g) := rfl
      _ = ∑' n, (innerSL ℂ f) ((d n * (ρ : ℂ) ^ n) • hermiteLpNorm n) := hhsum.symm
      _ = ∑' n, inner ℂ f (hermiteLpNorm n) * d n * (ρ : ℂ) ^ n := tsum_congr hterm
  rw [hL, hR]

/-- **`P` is self-adjoint on `L²(π)`**: `P = P*`.  Combined with the diagonalisation this makes
the eigenvalue list `ρⁿ` a genuine spectral decomposition: `P` is a self-adjoint contraction that
acts by the real scalars `ρⁿ` on the complete orthonormal system `eₙ`. -/
theorem gaussianPCNOp_isSelfAdjoint (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) :
    IsSelfAdjoint (gaussianPCNOp ρ s hρs hs) := by
  rw [ContinuousLinearMap.isSelfAdjoint_iff']
  refine ContinuousLinearMap.ext fun g => ?_
  refine ext_inner_left (𝕜 := ℂ) fun v => ?_
  calc inner ℂ v ((ContinuousLinearMap.adjoint (gaussianPCNOp ρ s hρs hs)) g)
      = (starRingEnd ℂ) (inner ℂ ((ContinuousLinearMap.adjoint
          (gaussianPCNOp ρ s hρs hs)) g) v) :=
        (inner_conj_symm (𝕜 := ℂ) v ((ContinuousLinearMap.adjoint
          (gaussianPCNOp ρ s hρs hs)) g)).symm
    _ = (starRingEnd ℂ) (inner ℂ g ((gaussianPCNOp ρ s hρs hs) v)) := by
        rw [ContinuousLinearMap.adjoint_inner_left]
    _ = inner ℂ ((gaussianPCNOp ρ s hρs hs) v) g :=
        inner_conj_symm (𝕜 := ℂ) ((gaussianPCNOp ρ s hρs hs) v) g
    _ = inner ℂ v ((gaussianPCNOp ρ s hρs hs) g) :=
        inner_gaussianPCNOp_comm ρ s hρs hs v g

/-- **`P` as a sum of scaled rank-one projections**: with `Pₙ f = ⟨eₙ, f⟩ eₙ`,
`P f = ∑' n, ρⁿ • Pₙ f`.  Together with `hasSum_hermiteLpNorm` (`∑' n, Pₙ f = f`) this is the
resolution of the identity along which `P` is diagonal. -/
theorem gaussianPCNOp_eq_tsum_rankOne (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (f : Lp ℂ 2 (gaussianReal 0 1)) :
    gaussianPCNOp ρ s hρs hs f
      = ∑' n, ((ρ : ℂ) ^ n) • (inner ℂ (hermiteLpNorm n) f • hermiteLpNorm n) := by
  rw [gaussianPCNOp_eq_tsum]
  exact tsum_congr fun n => by rw [smul_smul, mul_comm]

/-! ## 10. The `L²` rate of the pCN chain

The gap on the mean-zero subspace is exactly an `L²` convergence statement for the chain: starting
from mean-zero data the `k`-step law decays geometrically, and from general data it approaches the
equilibrium constant `⟨e₀, f⟩ e₀` (the projection onto the invariant mode) at rate `|ρ|ᵏ`.
-/

/-- **Mean-zero data decays geometrically in `L²`**:
`‖Pᵏ f‖ ≤ |ρ|ᵏ ‖f‖ → 0` for `f ⊥ e₀`. -/
theorem tendsto_norm_gaussianPCNOp_pow_of_inner_eq_zero (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1)
    (hs : s ≠ 0) {f : Lp ℂ 2 (gaussianReal 0 1)}
    (h0 : inner ℂ (hermiteLpNorm 0) f = 0) :
    Tendsto (fun k : ℕ => ‖((gaussianPCNOp ρ s hρs hs) ^ k) f‖) atTop (𝓝 0) := by
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) (by
    simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (r := |ρ|)
      (by simpa using abs_rho_lt_one hρs hs)).mul_const ‖f‖)
  exact norm_gaussianPCNOp_pow_le_of_inner_eq_zero ρ s hρs hs k h0

/-- **Mean-zero data converges to `0` in `L²`**, i.e. to the zero of the mean-zero subspace. -/
theorem tendsto_gaussianPCNOp_pow_of_inner_eq_zero (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1)
    (hs : s ≠ 0) {f : Lp ℂ 2 (gaussianReal 0 1)}
    (h0 : inner ℂ (hermiteLpNorm 0) f = 0) :
    Tendsto (fun k : ℕ => ((gaussianPCNOp ρ s hρs hs) ^ k) f) atTop (𝓝 0) := by
  rw [tendsto_zero_iff_norm_tendsto_zero]
  simpa using tendsto_norm_gaussianPCNOp_pow_of_inner_eq_zero ρ s hρs hs h0

/-- The invariant mode: `Pᵏ e₀ = e₀`, so constants are fixed by every step of the chain. -/
theorem gaussianPCNOp_pow_hermiteLpNorm_zero (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (k : ℕ) : ((gaussianPCNOp ρ s hρs hs) ^ k) (hermiteLpNorm 0) = hermiteLpNorm 0 := by
  induction k with
  | zero => simp
  | succ k ih =>
      rw [pow_succ']
      show gaussianPCNOp ρ s hρs hs (((gaussianPCNOp ρ s hρs hs) ^ k) (hermiteLpNorm 0))
        = hermiteLpNorm 0
      rw [ih]
      simpa using gaussianPCNOp_hermiteLpNorm ρ s hρs hs 0

/-- **The `L²` convergence rate of the pCN chain**: from any `f`, the `k`-step iterate is within
`|ρ|ᵏ ‖f - ⟨e₀, f⟩ e₀‖` of the invariant constant `⟨e₀, f⟩ e₀`. -/
theorem norm_gaussianPCNOp_pow_sub_const_le (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (k : ℕ) (f : Lp ℂ 2 (gaussianReal 0 1)) :
    ‖((gaussianPCNOp ρ s hρs hs) ^ k) f
        - inner ℂ (hermiteLpNorm 0) f • hermiteLpNorm 0‖
      ≤ |ρ| ^ k * ‖f - inner ℂ (hermiteLpNorm 0) f • hermiteLpNorm 0‖ := by
  have hsplit : ((gaussianPCNOp ρ s hρs hs) ^ k) f
        - inner ℂ (hermiteLpNorm 0) f • hermiteLpNorm 0
      = ((gaussianPCNOp ρ s hρs hs) ^ k)
          (f - inner ℂ (hermiteLpNorm 0) f • hermiteLpNorm 0) := by
    rw [map_sub, map_smul, gaussianPCNOp_pow_hermiteLpNorm_zero ρ s hρs hs k]
  have hzero : inner ℂ (hermiteLpNorm 0)
      (f - inner ℂ (hermiteLpNorm 0) f • hermiteLpNorm 0) = 0 := by
    rw [inner_sub_right, inner_smul_right]
    have hnorm : inner ℂ (hermiteLpNorm 0) (hermiteLpNorm 0) = 1 := by
      rw [inner_self_eq_norm_sq_to_K, orthonormal_hermiteLpNorm.1 0]
      norm_num
    rw [hnorm, mul_one, sub_self]
  rw [hsplit]
  exact norm_gaussianPCNOp_pow_le_of_inner_eq_zero ρ s hρs hs k hzero

/-- **The chain converges to its equilibrium constant** in `L²`: `Pᵏ f → ⟨e₀, f⟩ e₀`. -/
theorem tendsto_gaussianPCNOp_pow (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (f : Lp ℂ 2 (gaussianReal 0 1)) :
    Tendsto (fun k : ℕ => ((gaussianPCNOp ρ s hρs hs) ^ k) f) atTop
      (𝓝 (inner ℂ (hermiteLpNorm 0) f • hermiteLpNorm 0)) := by
  rw [tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero (fun k => norm_nonneg _) (fun k => ?_) (by
    simpa using (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (r := |ρ|)
      (by simpa using abs_rho_lt_one hρs hs)).mul_const
        ‖f - inner ℂ (hermiteLpNorm 0) f • hermiteLpNorm 0‖)
  exact norm_gaussianPCNOp_pow_sub_const_le ρ s hρs hs k f

/-! ## 11. The converse spectral statement: nonzero eigenvalues are `ρⁿ`

§9 showed that `P` is self-adjoint and diagonalised by the complete orthonormal system `eₙ`
with eigenvalues `ρⁿ`, so every `ρⁿ` *is* an eigenvalue (of the mode `eₙ`).  This section
proves the converse, which is what makes the diagonalisation a complete description of the
eigenvalue list: any eigenvalue of `P` on `L²(π)` is one of the numbers `ρⁿ`.

The proof is coefficient matching.  Expanding both sides of `P f = μ f` in the Hermite basis,
the `n`-th coordinates give `ρⁿ ⟨eₙ, f⟩ = μ ⟨eₙ, f⟩`; since a nonzero `f` has at least one
nonzero coefficient (`hasSum_hermiteLpNorm`), `μ = ρⁿ` for that `n`.
-/

/-- **The Hermite coefficients of `P f` are `ρⁿ` times those of `f`**:
`⟨eₙ, P f⟩ = ρⁿ ⟨eₙ, f⟩`.  This is the basis coefficient form of the diagonalisation; it is
proved from symmetry (`inner_gaussianPCNOp_comm`) and the eigenrelation `P eₙ = ρⁿ eₙ`, so it
does not need summability of the expansion. -/
theorem inner_hermiteLpNorm_gaussianPCNOp (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (n : ℕ) (f : Lp ℂ 2 (gaussianReal 0 1)) :
    inner ℂ (hermiteLpNorm n) (gaussianPCNOp ρ s hρs hs f)
      = (ρ : ℂ) ^ n * inner ℂ (hermiteLpNorm n) f := by
  calc inner ℂ (hermiteLpNorm n) (gaussianPCNOp ρ s hρs hs f)
      = (starRingEnd ℂ) (inner ℂ (gaussianPCNOp ρ s hρs hs f) (hermiteLpNorm n)) :=
        (inner_conj_symm (𝕜 := ℂ) (hermiteLpNorm n) (gaussianPCNOp ρ s hρs hs f)).symm
    _ = (starRingEnd ℂ) (inner ℂ f (gaussianPCNOp ρ s hρs hs (hermiteLpNorm n))) := by
        rw [inner_gaussianPCNOp_comm ρ s hρs hs f (hermiteLpNorm n)]
    _ = (starRingEnd ℂ) (((ρ : ℂ) ^ n) * inner ℂ f (hermiteLpNorm n)) := by
        rw [gaussianPCNOp_hermiteLpNorm ρ s hρs hs n, inner_smul_right]
    _ = (ρ : ℂ) ^ n * inner ℂ (hermiteLpNorm n) f := by
        rw [map_mul, map_pow, Complex.conj_ofReal,
          inner_conj_symm (𝕜 := ℂ) (hermiteLpNorm n) f]

/-- **A nonzero vector has a nonzero Hermite coefficient.**  Immediate from the basis expansion
`f = ∑' n, ⟨eₙ, f⟩ eₙ`: if every coefficient vanished the sum would be zero. -/
theorem exists_inner_hermiteLpNorm_ne_zero {f : Lp ℂ 2 (gaussianReal 0 1)} (hf : f ≠ 0) :
    ∃ n : ℕ, inner ℂ (hermiteLpNorm n) f ≠ 0 := by
  by_contra h
  push_neg at h
  apply hf
  rw [← (hasSum_hermiteLpNorm f).tsum_eq]
  simp [h]

/-- **The converse spectral statement: `P` has no eigenvalue outside `{ρⁿ}`.**  If
`P f = μ f` with `f ≠ 0` and `μ ≠ 0`, then `μ = ρⁿ` for some `n`.  Together with
`gaussianPCNOp_hermiteLpNorm` (`ρⁿ` is attained on `eₙ`) this pins the eigenvalue list of `P`
exactly to the geometric sequence `ρⁿ`, `n : ℕ`. -/
theorem gaussianPCNOp_eigenvalue_eq_rho_pow (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    {f : Lp ℂ 2 (gaussianReal 0 1)} {μ : ℂ} (hf : f ≠ 0)
    (heig : gaussianPCNOp ρ s hρs hs f = μ • f) :
    ∃ n : ℕ, μ = (ρ : ℂ) ^ n := by
  obtain ⟨n, hn⟩ := exists_inner_hermiteLpNorm_ne_zero hf
  refine ⟨n, ?_⟩
  have hleft : inner ℂ (hermiteLpNorm n) (gaussianPCNOp ρ s hρs hs f)
      = (ρ : ℂ) ^ n * inner ℂ (hermiteLpNorm n) f :=
    inner_hermiteLpNorm_gaussianPCNOp ρ s hρs hs n f
  have hright : inner ℂ (hermiteLpNorm n) (gaussianPCNOp ρ s hρs hs f)
      = μ * inner ℂ (hermiteLpNorm n) f := by
    rw [heig, inner_smul_right]
  have hcancel : (ρ : ℂ) ^ n = μ := mul_right_cancel₀ hn (hleft.symm.trans hright)
  exact hcancel.symm

/-! ## 12. Positivity: `P` has nonnegative spectrum

Mathlib's `ContinuousLinearMap.IsPositive` is stated for real scalars (`LE 𝕜`), so it does not
apply to the complex Hilbert space `L²(π)` directly.  The two components of positivity are
recorded separately instead, exactly as `ContinuousLinearMap.isPositive_iff` splits them for
real scalars: self-adjointness (§9, `gaussianPCNOp_isSelfAdjoint`) and the nonnegativity of the
real part of the quadratic form, which is this section.

The quadratic form is computed from the diagonal expansion: with `cₙ = ⟨eₙ, f⟩`,
`Re ⟪P f, f⟫ = ∑' n, ρⁿ ‖cₙ‖²`.  This is the spectral-measure reading — the eigenvalues weight
the nonnegative coefficients `‖cₙ‖²`, which themselves sum to `‖f‖²` by Parseval — so when
`ρ ≥ 0` (the pCN case `ρ = cos θ`, `θ ∈ (0, π/2)`) every term is nonnegative.  Note that the
hypothesis `0 ≤ ρ` is *not* removable: `P` is an indefinite operator when `ρ < 0`, the odd modes
carrying the negative eigenvalues.
-/

/-- A real cast times `conj z * z` has real part `r ‖z‖²`.  The scalar bookkeeping behind the
quadratic-form computation. -/
theorem re_conj_mul_pow_mul (r : ℝ) (n : ℕ) (z : ℂ) :
    ((starRingEnd ℂ) z * (r : ℂ) ^ n * z).re = r ^ n * ‖z‖ ^ 2 := by
  rw [← Complex.ofReal_pow]
  have h : (starRingEnd ℂ) z * ((r ^ n : ℝ) : ℂ) * z
      = ((r ^ n : ℝ) : ℂ) * ((starRingEnd ℂ) z * z) := by ring
  rw [h, Complex.re_ofReal_mul, re_conj_mul_self]

/-- **The quadratic form of `P`, diagonalised**: `Re ⟪P f, f⟫ = ∑' n, ρⁿ ‖⟨eₙ, f⟩‖²`.  Each
term is an eigenvalue times a nonnegative coefficient, i.e. the spectral-measure integral of
`id` against the Hermite spectral measure of `f`. -/
theorem gaussianPCNOp_re_inner_eq_tsum (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (f : Lp ℂ 2 (gaussianReal 0 1)) :
    (inner ℂ (gaussianPCNOp ρ s hρs hs f) f).re
      = ∑' n : ℕ, ρ ^ n * ‖inner ℂ (hermiteLpNorm n) f‖ ^ 2 := by
  have hP : (starRingEnd ℂ) ((innerSL ℂ f) (gaussianPCNOp ρ s hρs hs f))
      = inner ℂ (gaussianPCNOp ρ s hρs hs f) f := by
    rw [innerSL_apply_apply]
    exact inner_conj_symm (𝕜 := ℂ) (gaussianPCNOp ρ s hρs hs f) f
  have h1 := (hasSum_gaussianPCNOp ρ s hρs hs f).map (innerSL ℂ f)
    (innerSL ℂ f).continuous
  have h2 := h1.map (starRingEnd ℂ) continuous_star
  have hterm : ∀ n : ℕ,
      ((starRingEnd ℂ) ((innerSL ℂ f)
        (((inner ℂ (hermiteLpNorm n) f) * (ρ : ℂ) ^ n) • hermiteLpNorm n))).re
        = ρ ^ n * ‖inner ℂ (hermiteLpNorm n) f‖ ^ 2 := by
    intro n
    rw [innerSL_apply_apply, inner_smul_right, map_mul, map_mul, map_pow, Complex.conj_ofReal,
      inner_conj_symm (𝕜 := ℂ) (hermiteLpNorm n) f]
    exact re_conj_mul_pow_mul ρ n (inner ℂ (hermiteLpNorm n) f)
  rw [← hP, ← h2.tsum_eq]
  rw [Complex.re_tsum h2.summable]
  exact tsum_congr hterm

/-- **`P` is positive when `ρ ≥ 0`**: the real part of the quadratic form is nonnegative,
`0 ≤ Re ⟪P f, f⟫` for every `f ∈ L²(π)`. -/
theorem gaussianPCNOp_re_inner_nonneg (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (hρ0 : 0 ≤ ρ) (f : Lp ℂ 2 (gaussianReal 0 1)) :
    0 ≤ (inner ℂ (gaussianPCNOp ρ s hρs hs f) f).re := by
  rw [gaussianPCNOp_re_inner_eq_tsum ρ s hρs hs f]
  exact tsum_nonneg fun n => mul_nonneg (pow_nonneg hρ0 n) (sq_nonneg _)

/-- **`P` is a positive operator**: self-adjoint, with a nonnegative quadratic form.  These are
the two components of `ContinuousLinearMap.IsPositive` (which Mathlib states only for real
scalars), so this is the positivity statement in the complex `L²` setting. -/
theorem gaussianPCNOp_isPositiveOp (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (hρ0 : 0 ≤ ρ) :
    IsSelfAdjoint (gaussianPCNOp ρ s hρs hs) ∧
      ∀ f : Lp ℂ 2 (gaussianReal 0 1),
        0 ≤ (inner ℂ (gaussianPCNOp ρ s hρs hs f) f).re :=
  ⟨gaussianPCNOp_isSelfAdjoint ρ s hρs hs,
    fun f => gaussianPCNOp_re_inner_nonneg ρ s hρs hs hρ0 f⟩

/-- **The eigenvalues of a positive `P` lie in `[0, 1]`**: with `0 ≤ ρ` and `|ρ| < 1`, the mode
`eₙ` is an eigenvector for the real eigenvalue `ρⁿ`, which is nonnegative and at most `1`.  So
the diagonalisation of `P` is a spectral decomposition against a genuine (nonnegative, bounded)
spectral measure, of total mass `1 = ‖eₙ‖²` on each mode.  Note that `0` is an eigenvalue when
`ρ = 0` (`n ≥ 1`), so the interval is closed at the left end. -/
theorem gaussianPCNOp_eigenvalue_mem_Icc (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (hρ0 : 0 ≤ ρ) (n : ℕ) :
    ((ρ : ℂ) ^ n).re ∈ Set.Icc (0 : ℝ) 1 := by
  rw [← Complex.ofReal_pow, Complex.ofReal_re]
  refine ⟨pow_nonneg hρ0 n, pow_le_one₀ hρ0 ?_⟩
  have hρ1 := abs_rho_lt_one hρs hs
  rw [abs_lt] at hρ1
  exact le_of_lt hρ1.2

/-! ## 13. Total-variation convergence at the same rate

`BookProof.MCMC.ConvergenceTheorem` proves the *Born-to-variation* bound
`‖ν − π‖_TV ≤ ½ √(∫ (g − 1)²)` for a density `g` of `ν` against a probability measure `π`
(`tvDist_le_half_l2`).  Composing it with the `L²` rate of §10 turns a geometric `L²` decay of a
density ratio into geometric convergence in total variation at the same factor: the pCN chain's
TV rate is `|ρ|ᵐ`, the spectral gap itself, with the constant `½‖f‖` coming from the initial
`L²` distance to the invariant constant.

The hypothesis `hdnorm` is the *transport* between the two levels — it identifies the `L²` norm
of the `m`-th density deviation with the norm of the `m`-th operator iterate applied to the
initial deviation class.  It is what would follow from the a.e. identification of the operator
iterate with the pointwise kernel action; that identification is a chapter of its own
(`MarkovOperatorCondExp` builds the a.e. action), so it is carried as a hypothesis here rather
than assumed silently.
-/

/-- **Total-variation geometric convergence of the pCN chain at rate `|ρ|`.**  If the iterates
`ν m` have densities `d m` with `∫ d m = 1`, the deviations `d m − 1` are in `L²(π)`, and their
`L²` norms are those of the operator iterates `Pᵐ f` for a mean-zero deviation class `f`, then
`‖ν m − π‖_TV ≤ ofReal ((‖f‖/2) |ρ|ᵐ)`.  The rate is exactly the contraction factor of §10; no
separate mixing-rate hypothesis is introduced. -/
theorem gaussianPCN_tv_geometric_convergence (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (f : Lp ℂ 2 (gaussianReal 0 1)) (hmean : inner ℂ (hermiteLpNorm 0) f = 0)
    (ν : ℕ → Measure ℝ) (d : ℕ → ℝ → ℝ)
    (hdens : ∀ m : ℕ, ∀ t : Set ℝ, MeasurableSet t →
      (ν m t).toReal = ∫ x in t, d m x ∂(gaussianReal 0 1))
    (hd1 : ∀ m : ℕ, ∫ x, d m x ∂(gaussianReal 0 1) = 1)
    (hd2 : ∀ m : ℕ, MemLp (fun x => d m x - 1) (ENNReal.ofReal 2) (gaussianReal 0 1))
    (hdnorm : ∀ m : ℕ, Real.sqrt (∫ x, (d m x - 1) ^ 2 ∂(gaussianReal 0 1))
      = ‖((gaussianPCNOp ρ s hρs hs) ^ m) f‖) :
    ∀ m : ℕ, tvDist (ν m) (gaussianReal 0 1)
      ≤ ENNReal.ofReal ((‖f‖ / 2) * |ρ| ^ m) := by
  intro m
  -- the `L²` distance at step `m`, from the operator rate of §10
  have hstep : Real.sqrt (∫ x, (d m x - 1) ^ 2 ∂(gaussianReal 0 1)) ≤ ‖f‖ * |ρ| ^ m := by
    rw [hdnorm m]
    calc ‖((gaussianPCNOp ρ s hρs hs) ^ m) f‖ ≤ |ρ| ^ m * ‖f‖ :=
          norm_gaussianPCNOp_pow_le_of_inner_eq_zero ρ s hρs hs m hmean
      _ = ‖f‖ * |ρ| ^ m := mul_comm _ _
  refine le_trans (tvDist_le_half_l2 (d m) (ν m) (hdens m) (hd1 m) (hd2 m)) ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hhalf := mul_le_mul_of_nonneg_left hstep (by norm_num : (0:ℝ) ≤ 1 / 2)
  nlinarith

/-! ## 14. The a.e. transport: the operator iterate is the pointwise kernel action

§13's total-variation statement carried the transport `hdnorm` (density-deviation `L²` norms equal
operator-iterate norms) as a hypothesis, because the operator lives on `L²(π)` classes while a
density is a *function*.  This section supplies that identification.

The pointwise pCN action is `kernelIntegral κ f x = ∫ y, f y ∂(κ x)`, and
`LpKernelOperator.gaussianPCNOp_coeFn` says the class `P f` is represented by it `π`-almost
everywhere.  Iterating gives **`gaussianPCNOp_pow_coeFn`**: `Pᵐ f` is represented almost
everywhere by the `m`-fold iterate of the pointwise action applied to a representative of `f`.
The density of the `m`-th iterate is then the real function `pcnIterateDensity`, and its `L²`
deviation norm is at most `‖Pᵐ f‖` (`sqrt_integral_pcnIterateDeviation_sq_le`).

The remaining hypothesis of the total-variation theorem
(`gaussianPCN_tv_geometric_convergence_of_density`) is `hpos`: the densities are nonnegative.
That is a statement about the model — the iterated deviation stays above `-1` — not about the
transport, and it is what makes the constructed `withDensity` a probability measure at all.
-/

/-- The `m`-fold pointwise pCN action applied to a representative of an `L²(π)` class. -/
noncomputable def pcnKernelAction (ρ s : ℝ) (m : ℕ) (f : Lp ℂ 2 (gaussianReal 0 1)) :
    ℝ → ℂ :=
  (kernelIntegral (gaussianPCNKernel ρ s))^[m] (f : ℝ → ℂ)

/-- **The a.e. transport.**  The `m`-th operator power `Pᵐ f` is represented `π`-almost
everywhere by the `m`-fold pointwise kernel action on a representative of `f`.  The `m = 0` case
is the identity; the step is the `m = 1` identification `gaussianPCNOp_coeFn` applied to
`Pᵐ f`, with `markovOpFun_congr` transporting the a.e. equality of representatives through the
kernel (which is where `κ x ≪ π` is used). -/
theorem gaussianPCNOp_pow_coeFn (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) (m : ℕ)
    (f : Lp ℂ 2 (gaussianReal 0 1)) :
    ((((gaussianPCNOp ρ s hρs hs) ^ m) f : Lp ℂ 2 (gaussianReal 0 1)) : ℝ → ℂ)
      =ᵐ[gaussianReal 0 1] pcnKernelAction ρ s m f := by
  induction m with
  | zero =>
      simp [pcnKernelAction, Function.iterate_zero]
  | succ m ih =>
      have h1 := gaussianPCNOp_coeFn ρ s hρs hs (((gaussianPCNOp ρ s hρs hs) ^ m) f)
      filter_upwards [h1] with x hx
      rw [pow_succ', ContinuousLinearMap.mul_apply]
      simp only [pcnKernelAction, Function.iterate_succ_apply']
      rw [hx]
      exact markovOpFun_congr (gaussianPCNKernel ρ s) (gaussianReal 0 1)
        (gaussianPCNKernel_absolutelyContinuous hs) ih x

/-- The deviation of the `m`-th pCN iterate from the stationary density, read through the
pointwise kernel action: `pcnIterateDeviation ρ s m f x = Re ((κᵐ f) x)`.  Real-valued by
construction, which is what a density needs. -/
noncomputable def pcnIterateDeviation (ρ s : ℝ) (m : ℕ) (f : Lp ℂ 2 (gaussianReal 0 1)) :
    ℝ → ℝ :=
  fun x => (pcnKernelAction ρ s m f x).re

/-- The density of the `m`-th iterate: the stationary density `1` plus the deviation. -/
noncomputable def pcnIterateDensity (ρ s : ℝ) (m : ℕ) (f : Lp ℂ 2 (gaussianReal 0 1)) :
    ℝ → ℝ :=
  fun x => 1 + pcnIterateDeviation ρ s m f x

/-- The measure of the `m`-th iterate, with density `pcnIterateDensity` against `π`.  It is a
probability measure exactly when that density is nonnegative. -/
noncomputable def pcnIterateMeasure (ρ s : ℝ) (m : ℕ) (f : Lp ℂ 2 (gaussianReal 0 1)) :
    Measure ℝ :=
  (gaussianReal 0 1).withDensity
    (fun x => ENNReal.ofReal (pcnIterateDensity ρ s m f x))

/-- The deviation is the real part of the operator iterate, almost everywhere: the transported
density and the `L²` class agree off a null set. -/
theorem pcnIterateDeviation_ae_eq_re (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (m : ℕ) (f : Lp ℂ 2 (gaussianReal 0 1)) :
    pcnIterateDeviation ρ s m f
      =ᵐ[gaussianReal 0 1]
        fun x => (((((gaussianPCNOp ρ s hρs hs) ^ m) f : Lp ℂ 2 (gaussianReal 0 1)) :
          ℝ → ℂ) x).re := by
  filter_upwards [(gaussianPCNOp_pow_coeFn ρ s hρs hs m f).symm] with x hx
  rw [pcnIterateDeviation, hx]

/-- **The `L²` class of the transported deviation.**  `pcnIterateDeviation` is `MemLp 2` because
it is, almost everywhere, the real part of a representative of `Pᵐ f ∈ L²(π)`; the real part of a
complex `L²` function is `L²` since `|Re z| ≤ ‖z‖`. -/
theorem memLp_pcnIterateDeviation (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (m : ℕ) (f : Lp ℂ 2 (gaussianReal 0 1)) :
    MemLp (pcnIterateDeviation ρ s m f) 2 (gaussianReal 0 1) := by
  have hmem : MemLp
      (fun x => (((((gaussianPCNOp ρ s hρs hs) ^ m) f : Lp ℂ 2 (gaussianReal 0 1)) :
        ℝ → ℂ) x).re) 2 (gaussianReal 0 1) :=
    MemLp.of_le (Lp.memLp _)
      (Complex.continuous_re.comp_aestronglyMeasurable
        (Lp.memLp _).aestronglyMeasurable)
      (ae_of_all _ fun x => by
        simpa [Real.norm_eq_abs] using Complex.abs_re_le_norm _)
  exact (memLp_congr_ae (pcnIterateDeviation_ae_eq_re ρ s hρs hs m f)).mpr hmem

/-- The constant mode `e₀ = [He₀]` is the class of the constant function `1`. -/
theorem hermiteLpNorm_zero_coeFn :
    (hermiteLpNorm 0 : ℝ → ℂ) =ᵐ[gaussianReal 0 1] fun _ => (1 : ℂ) := by
  filter_upwards [MemLp.coeFn_toLp (memLp_two_hermiteReal 0),
    Lp.coeFn_smul (((Real.sqrt (Nat.factorial 0 : ℝ))⁻¹ : ℂ))
      (MemLp.toLp (hermiteRealComplex 0) (memLp_two_hermiteReal 0))] with x h1 h2
  rw [hermiteLpNorm, h2, Pi.smul_apply, h1, hermiteRealComplex_apply, hermiteReal_zero]
  norm_num

/-- **Integration against `π` is the `e₀` coefficient**: since `e₀` is the class of `1`,
`∫ g ∂π = ⟨e₀, g⟩` for every `g ∈ L²(π)`. -/
theorem integral_coeFn_eq_inner_hermiteLpNorm_zero (g : Lp ℂ 2 (gaussianReal 0 1)) :
    ∫ x, ((g : ℝ → ℂ) x) ∂(gaussianReal 0 1) = inner ℂ (hermiteLpNorm 0) g := by
  rw [L2.inner_def]
  refine integral_congr_ae ?_
  filter_upwards [hermiteLpNorm_zero_coeFn] with x hx
  rw [hx, RCLike.inner_apply, map_one, mul_one]

/-- **The mean-zero subspace is invariant**: `⟨e₀, Pᵐ g⟩ = ⟨e₀, g⟩` for every power `m`.  This
is the `n = 0` case of the coefficient lemma of §11, iterated. -/
theorem inner_hermiteLpNorm_zero_gaussianPCNOp_pow (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1)
    (hs : s ≠ 0) (m : ℕ) (g : Lp ℂ 2 (gaussianReal 0 1)) :
    inner ℂ (hermiteLpNorm 0) (((gaussianPCNOp ρ s hρs hs) ^ m) g)
      = inner ℂ (hermiteLpNorm 0) g := by
  induction m with
  | zero => simp
  | succ m ih =>
      rw [pow_succ', ContinuousLinearMap.mul_apply,
        inner_hermiteLpNorm_gaussianPCNOp ρ s hρs hs 0, pow_zero, one_mul]
      exact ih

/-- **The transported deviation has mean zero**: `∫ Re (κᵐ f) ∂π = 0` for mean-zero `f`.  The
real part of the integral is the `e₀` coefficient, which is conserved by every power of `P`.
-/
theorem integral_pcnIterateDeviation_zero (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (m : ℕ) {f : Lp ℂ 2 (gaussianReal 0 1)}
    (h0 : inner ℂ (hermiteLpNorm 0) f = 0) :
    ∫ x, pcnIterateDeviation ρ s m f x ∂(gaussianReal 0 1) = 0 := by
  have hmem : MemLp (pcnKernelAction ρ s m f) 2 (gaussianReal 0 1) :=
    (memLp_congr_ae (gaussianPCNOp_pow_coeFn ρ s hρs hs m f)).mp (Lp.memLp _)
  have hint : Integrable (pcnKernelAction ρ s m f) (gaussianReal 0 1) :=
    hmem.integrable (by norm_num)
  have hre : ∫ x, pcnIterateDeviation ρ s m f x ∂(gaussianReal 0 1)
      = (∫ x, pcnKernelAction ρ s m f x ∂(gaussianReal 0 1)).re := by
    rw [show pcnIterateDeviation ρ s m f
        = fun x => Complex.reCLM (pcnKernelAction ρ s m f x) from rfl]
    rw [ContinuousLinearMap.integral_comp_comm Complex.reCLM hint]
    rfl
  rw [hre]
  have hint' : ∫ x, pcnKernelAction ρ s m f x ∂(gaussianReal 0 1)
      = ∫ x, (((((gaussianPCNOp ρ s hρs hs) ^ m) f : Lp ℂ 2 (gaussianReal 0 1)) :
          ℝ → ℂ) x) ∂(gaussianReal 0 1) :=
    integral_congr_ae (gaussianPCNOp_pow_coeFn ρ s hρs hs m f).symm
  rw [hint', integral_coeFn_eq_inner_hermiteLpNorm_zero,
    inner_hermiteLpNorm_zero_gaussianPCNOp_pow ρ s hρs hs m f, h0]
  simp

/-- **Squares of an `L²` representative integrate to the square of the class norm**:
`∫ x, ‖g x‖² ∂π = ‖g‖²`.  This is `L2.inner_def` at `(g, g)` (whose integrand is
`conj (g x) * g x`, of real part `‖g x‖²`) read through `inner_self_eq_norm_sq_to_K`. -/
theorem integral_norm_sq_coeFn (g : Lp ℂ 2 (gaussianReal 0 1)) :
    ∫ x, ‖((g : ℝ → ℂ) x)‖ ^ 2 ∂(gaussianReal 0 1) = ‖g‖ ^ 2 := by
  have hint : Integrable (fun x => ‖((g : ℝ → ℂ) x)‖ ^ 2) (gaussianReal 0 1) :=
    (Lp.memLp g).integrable_norm_pow (p := 2) (by norm_num)
  have hinner : inner ℂ g g
      = ∫ x, ((‖((g : ℝ → ℂ) x)‖ ^ 2 : ℝ) : ℂ) ∂(gaussianReal 0 1) := by
    rw [L2.inner_def]
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [RCLike.inner_apply]
    rw [mul_comm, ofReal_norm_sq_eq_conj_mul_self]
  have hofReal : (∫ x, ((‖((g : ℝ → ℂ) x)‖ ^ 2 : ℝ) : ℂ) ∂(gaussianReal 0 1))
      = ((∫ x, ‖((g : ℝ → ℂ) x)‖ ^ 2 ∂(gaussianReal 0 1) : ℝ) : ℂ) :=
    ContinuousLinearMap.integral_comp_comm Complex.ofRealCLM hint
  refine Complex.ofReal_injective ?_
  rw [← hofReal, ← hinner, inner_self_eq_norm_sq_to_K, Complex.ofReal_pow]
  rfl

/-- **The transported deviation's `L²` norm is at most the operator iterate's.**  Pointwise
`(Re z)² ≤ ‖z‖²`, and `∫ ‖Pᵐ f‖² = ‖Pᵐ f‖²` by `integral_norm_sq_coeFn`. -/
theorem sqrt_integral_pcnIterateDeviation_sq_le (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1)
    (hs : s ≠ 0) (m : ℕ) (f : Lp ℂ 2 (gaussianReal 0 1)) :
    Real.sqrt (∫ x, pcnIterateDeviation ρ s m f x ^ 2 ∂(gaussianReal 0 1))
      ≤ ‖((gaussianPCNOp ρ s hρs hs) ^ m) f‖ := by
  have hI1 : Integrable (fun x => pcnIterateDeviation ρ s m f x ^ 2) (gaussianReal 0 1) :=
    (memLp_pcnIterateDeviation ρ s hρs hs m f).integrable_norm_pow (p := 2)
      (by norm_num) |>.congr (ae_of_all _ fun x => by
        change ‖pcnIterateDeviation ρ s m f x‖ ^ 2 = pcnIterateDeviation ρ s m f x ^ 2
        rw [Real.norm_eq_abs, sq_abs])
  have hI2 : Integrable
      (fun x => ‖(((((gaussianPCNOp ρ s hρs hs) ^ m) f : Lp ℂ 2 (gaussianReal 0 1)) :
        ℝ → ℂ) x)‖ ^ 2) (gaussianReal 0 1) :=
    (Lp.memLp _).integrable_norm_pow (p := 2) (by norm_num)
  have hle : ∫ x, pcnIterateDeviation ρ s m f x ^ 2 ∂(gaussianReal 0 1)
      ≤ ∫ x, ‖(((((gaussianPCNOp ρ s hρs hs) ^ m) f : Lp ℂ 2 (gaussianReal 0 1)) :
          ℝ → ℂ) x)‖ ^ 2 ∂(gaussianReal 0 1) := by
    refine integral_mono_ae hI1 hI2 ?_
    filter_upwards [pcnIterateDeviation_ae_eq_re ρ s hρs hs m f] with x hx
    rw [hx]
    calc (((((gaussianPCNOp ρ s hρs hs) ^ m) f : Lp ℂ 2 (gaussianReal 0 1)) : ℝ → ℂ) x).re ^ 2
        = |(((((gaussianPCNOp ρ s hρs hs) ^ m) f : Lp ℂ 2 (gaussianReal 0 1)) :
            ℝ → ℂ) x).re| ^ 2 := by rw [sq_abs]
      _ ≤ ‖(((((gaussianPCNOp ρ s hρs hs) ^ m) f : Lp ℂ 2 (gaussianReal 0 1)) :
            ℝ → ℂ) x)‖ ^ 2 :=
          pow_le_pow_left₀ (abs_nonneg _) (Complex.abs_re_le_norm _) 2
  calc Real.sqrt (∫ x, pcnIterateDeviation ρ s m f x ^ 2 ∂(gaussianReal 0 1))
      ≤ Real.sqrt (‖((gaussianPCNOp ρ s hρs hs) ^ m) f‖ ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        exact hle.trans (le_of_eq (integral_norm_sq_coeFn _))
    _ = ‖((gaussianPCNOp ρ s hρs hs) ^ m) f‖ := Real.sqrt_sq (norm_nonneg _)

/-- **Total-variation geometric convergence of the pCN chain, densities constructed.**

This is §13's statement with the transport discharged.  The densities are *defined* from the
operator iterates (`pcnIterateDensity`), the measures are their `withDensity` (`pcnIterateMeasure`),
and the deviation norms, the mean-one property and the set-wise density relation are all proved
here rather than assumed.  The only remaining hypothesis is `hpos`: those densities are
nonnegative, i.e. the chain's iterates really are probability densities.  The rate is the
spectral gap `|ρ|ᵐ` of §10. -/
theorem gaussianPCN_tv_geometric_convergence_of_density (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1)
    (hs : s ≠ 0) (f : Lp ℂ 2 (gaussianReal 0 1)) (hmean : inner ℂ (hermiteLpNorm 0) f = 0)
    (hpos : ∀ (m : ℕ) (x : ℝ), 0 ≤ pcnIterateDensity ρ s m f x) :
    ∀ m : ℕ, tvDist (pcnIterateMeasure ρ s m f) (gaussianReal 0 1)
      ≤ ENNReal.ofReal ((‖f‖ / 2) * |ρ| ^ m) := by
  intro m
  have hdev : MemLp (pcnIterateDeviation ρ s m f) 2 (gaussianReal 0 1) :=
    memLp_pcnIterateDeviation ρ s hρs hs m f
  have hd2 : MemLp (fun x => pcnIterateDensity ρ s m f x - 1) 2 (gaussianReal 0 1) := by
    refine (memLp_congr_ae (f := fun x => pcnIterateDeviation ρ s m f x) ?_).mp hdev
    filter_upwards with x
    simp [pcnIterateDensity]
  have hd1 : ∫ x, pcnIterateDensity ρ s m f x ∂(gaussianReal 0 1) = 1 := by
    have hint : Integrable (pcnIterateDeviation ρ s m f) (gaussianReal 0 1) :=
      hdev.integrable (by norm_num)
    rw [show pcnIterateDensity ρ s m f
        = fun x => (1 : ℝ) + pcnIterateDeviation ρ s m f x from rfl]
    rw [integral_add (integrable_const 1) hint, integral_pcnIterateDeviation_zero ρ s hρs hs m
      hmean, integral_const, smul_eq_mul, mul_one, probReal_univ]
    norm_num
  have hdens : ∀ t : Set ℝ, MeasurableSet t →
      (pcnIterateMeasure ρ s m f t).toReal
        = ∫ x in t, pcnIterateDensity ρ s m f x ∂(gaussianReal 0 1) := by
    intro t ht
    have hint : Integrable (pcnIterateDeviation ρ s m f) (gaussianReal 0 1) :=
      hdev.integrable (by norm_num)
    have : Integrable (pcnIterateDensity ρ s m f) (gaussianReal 0 1) := by
      rw [show pcnIterateDensity ρ s m f
          = fun x => (1 : ℝ) + pcnIterateDeviation ρ s m f x from rfl]
      exact (integrable_const 1).add hint
    exact withDensity_toReal_eq_integral (pcnIterateDensity ρ s m f) this (hpos m) ht
  refine le_trans (tvDist_le_half_l2 (pcnIterateDensity ρ s m f) (pcnIterateMeasure ρ s m f)
    hdens hd1 (by simpa using hd2)) ?_
  refine ENNReal.ofReal_le_ofReal ?_
  have hsq : (fun x => (pcnIterateDensity ρ s m f x - 1) ^ 2)
      = fun x => pcnIterateDeviation ρ s m f x ^ 2 := by
    funext x
    simp only [pcnIterateDensity]
    ring
  have hstep : Real.sqrt (∫ x, (pcnIterateDensity ρ s m f x - 1) ^ 2 ∂(gaussianReal 0 1))
      ≤ ‖f‖ * |ρ| ^ m := by
    rw [hsq]
    calc Real.sqrt (∫ x, pcnIterateDeviation ρ s m f x ^ 2 ∂(gaussianReal 0 1))
        ≤ ‖((gaussianPCNOp ρ s hρs hs) ^ m) f‖ :=
          sqrt_integral_pcnIterateDeviation_sq_le ρ s hρs hs m f
      _ ≤ |ρ| ^ m * ‖f‖ :=
          norm_gaussianPCNOp_pow_le_of_inner_eq_zero ρ s hρs hs m hmean
      _ = ‖f‖ * |ρ| ^ m := mul_comm _ _
  have hhalf := mul_le_mul_of_nonneg_left hstep (by norm_num : (0 : ℝ) ≤ 1 / 2)
  nlinarith

/-! ## 15. `0` lies in the spectrum, as a limit point of the eigenvalues

§11 pinned the eigenvalue *list* to `{ρⁿ}`, and §12 showed the eigenvalues are nonnegative.  The
converse direction — that the spectrum is larger than the eigenvalue list — was left open there.
Since `|ρ| < 1` the eigenvalues accumulate at `0`, so the closed spectrum
(`spectrum.isClosed`) must contain `0`.  This section makes that argument a theorem:
`zero_mem_spectrum_gaussianPCNOp`.  Together with `zero_not_eigenvalue_gaussianPCNOp` (for
`ρ ≠ 0`, `0` is not an eigenvalue, because `P f = ⟨e₀, f⟩ e₀` kills only mean-zero data and
`gaussianPCNOp_eigenvalue_eq_rho_pow` would force `0 = ρⁿ`), this says `0` is a genuine
accumulation point of the spectrum rather than an eigenvalue.
-/

/-- **Every `ρⁿ` is in the spectrum of `P`.**  `eₙ` is an eigenvector, so `P − ρⁿ • 1` kills the
nonzero vector `eₙ`; a unit of the endomorphism ring is injective (it has a left inverse), hence
`P − ρⁿ • 1` is not a unit, i.e. `ρⁿ` is in the spectrum. -/
theorem gaussianPCNOp_eigenvalue_mem_spectrum (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (n : ℕ) : (ρ : ℂ) ^ n ∈ spectrum ℂ (gaussianPCNOp ρ s hρs hs) := by
  rw [spectrum.mem_iff]
  intro hunit
  obtain ⟨v, hv⟩ := hunit.exists_left_inv
  have hker : ((algebraMap ℂ (Lp ℂ 2 (gaussianReal 0 1) →L[ℂ] Lp ℂ 2 (gaussianReal 0 1))
      ((ρ : ℂ) ^ n)) - gaussianPCNOp ρ s hρs hs) (hermiteLpNorm n) = 0 := by
    rw [ContinuousLinearMap.sub_apply]
    have hmap : (algebraMap ℂ (Lp ℂ 2 (gaussianReal 0 1) →L[ℂ]
        Lp ℂ 2 (gaussianReal 0 1)) ((ρ : ℂ) ^ n)) (hermiteLpNorm n)
        = (ρ : ℂ) ^ n • hermiteLpNorm n := by
      rw [Algebra.algebraMap_eq_smul_one, ContinuousLinearMap.smul_apply,
        ContinuousLinearMap.one_apply]
    rw [hmap, gaussianPCNOp_hermiteLpNorm, sub_self]
  have h1 : v (((algebraMap ℂ (Lp ℂ 2 (gaussianReal 0 1) →L[ℂ]
      Lp ℂ 2 (gaussianReal 0 1)) ((ρ : ℂ) ^ n)) - gaussianPCNOp ρ s hρs hs)
        (hermiteLpNorm n)) = 0 := by
    rw [hker, map_zero]
  have h2 : v (((algebraMap ℂ (Lp ℂ 2 (gaussianReal 0 1) →L[ℂ]
      Lp ℂ 2 (gaussianReal 0 1)) ((ρ : ℂ) ^ n)) - gaussianPCNOp ρ s hρs hs)
        (hermiteLpNorm n)) = hermiteLpNorm n := by
    rw [← ContinuousLinearMap.mul_apply, hv, ContinuousLinearMap.one_apply]
  have hzero : hermiteLpNorm n = 0 := by rw [← h2, h1]
  have hnorm := orthonormal_hermiteLpNorm.1 n
  rw [hzero, norm_zero] at hnorm
  exact zero_ne_one hnorm

/-- **The eigenvalues accumulate at `0`**: `(ρ : ℂ)ⁿ → 0`, since `|ρ| < 1`. -/
theorem tendsto_eigenvalue_pow_zero (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) :
    Tendsto (fun n : ℕ => (ρ : ℂ) ^ n) atTop (𝓝 0) := by
  have h : Tendsto (fun n : ℕ => ((ρ ^ n : ℝ) : ℂ)) atTop (𝓝 ((0 : ℝ) : ℂ)) :=
    (Complex.continuous_ofReal.tendsto 0).comp
      (tendsto_pow_atTop_nhds_zero_of_abs_lt_one (abs_rho_lt_one hρs hs))
  simpa [Complex.ofReal_pow] using h

/-- **`0` is in the spectrum of `P`.**  It is the limit of the eigenvalues `ρⁿ`, each of which
lies in the spectrum, and the spectrum of a bounded operator is closed. -/
theorem zero_mem_spectrum_gaussianPCNOp (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) :
    0 ∈ spectrum ℂ (gaussianPCNOp ρ s hρs hs) :=
  (spectrum.isClosed _).mem_of_tendsto (tendsto_eigenvalue_pow_zero ρ s hρs hs)
    (Eventually.of_forall fun n => gaussianPCNOp_eigenvalue_mem_spectrum ρ s hρs hs n)

/-- **`0` is not an eigenvalue when `ρ ≠ 0`**: so the `0` found above is an accumulation point of
the spectrum, not an eigenvector's eigenvalue.  If `P f = 0` with `f ≠ 0`, the converse spectral
statement would give `0 = ρⁿ`, which is impossible for `ρ ≠ 0`. -/
theorem zero_not_eigenvalue_gaussianPCNOp (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (hρ0 : ρ ≠ 0) {f : Lp ℂ 2 (gaussianReal 0 1)} (hf : f ≠ 0) :
    gaussianPCNOp ρ s hρs hs f ≠ 0 := by
  intro hzero
  have heig : gaussianPCNOp ρ s hρs hs f = (0 : ℂ) • f := by rw [hzero, zero_smul]
  obtain ⟨n, hn⟩ := gaussianPCNOp_eigenvalue_eq_rho_pow ρ s hρs hs hf heig
  exact pow_ne_zero n (by exact_mod_cast hρ0) hn.symm

/-! ## 16. The explicit spectral measure

The Hermite coefficients of §8–§11 are `ℓ²` data; this section packages them as an honest Borel
measure on the eigenvalue set: the weights `‖⟨eₙ, f⟩‖²` carried to the points `ρⁿ`
(`hermiteSpectralMeasure`).  It is the spectral measure of `f` for `P`, in the sense that its
total mass is `‖f‖²` (Parseval, §8), it is supported on `{ρⁿ | n}`, and it integrates the
identity to the quadratic form of `P` (`integral_hermiteSpectralMeasure_id`, i.e. §12 read as an
integral).  Everything is a `tsum` over `ℕ`, so no measure-theoretic generality of Mathlib's
spectral theorem is needed — the discreteness is the whole content.
-/

/-- **The Hermite spectral measure of `f`**: mass `‖⟨eₙ, f⟩‖²` at the eigenvalue `ρⁿ`. -/
noncomputable def hermiteSpectralMeasure (ρ : ℝ) (f : Lp ℂ 2 (gaussianReal 0 1)) :
    Measure ℝ :=
  Measure.sum fun n : ℕ =>
    ENNReal.ofReal (‖inner ℂ (hermiteLpNorm n) f‖ ^ 2) • Measure.dirac ((ρ : ℝ) ^ n)

/-- **The coefficient sequence is summable**: `∑ n, ‖⟨eₙ, f⟩‖² < ∞`.  This is the summability
half of Parseval, from the `ℓ²` summability of the Hermite coefficient products
(`HilbertBasis.summable_inner_mul_inner`) and the fact that each product's real part is
`‖⟨eₙ, f⟩‖²`. -/
theorem summable_norm_inner_hermiteLpNorm (f : Lp ℂ 2 (gaussianReal 0 1)) :
    Summable fun n : ℕ => ‖inner ℂ (hermiteLpNorm n) f‖ ^ 2 := by
  have hb : Summable fun n : ℕ =>
      inner ℂ f (hermiteLpNorm n) * inner ℂ (hermiteLpNorm n) f :=
    (by simpa using gaussianPCNHilbertBasis.summable_inner_mul_inner f f)
  refine (hb.map (Complex.reCLM : ℂ →+ ℝ) Complex.reCLM.continuous).congr fun n => ?_
  change Complex.re (inner ℂ f (hermiteLpNorm n) * inner ℂ (hermiteLpNorm n) f)
    = ‖inner ℂ (hermiteLpNorm n) f‖ ^ 2
  rw [← inner_conj_symm (𝕜 := ℂ) f (hermiteLpNorm n)]
  exact re_conj_mul_self _

/-- **The weights sum to `‖f‖²`** (the `ℝ≥0∞` form of Parseval, which is what the measure's mass
needs). -/
theorem tsum_ofReal_norm_inner_hermiteLpNorm (f : Lp ℂ 2 (gaussianReal 0 1)) :
    ∑' n : ℕ, ENNReal.ofReal (‖inner ℂ (hermiteLpNorm n) f‖ ^ 2)
      = ENNReal.ofReal (‖f‖ ^ 2) := by
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun n => sq_nonneg _)
    (summable_norm_inner_hermiteLpNorm f), tsum_norm_inner_hermiteLpNorm f]

/-- **The total mass is `‖f‖²`.** -/
theorem hermiteSpectralMeasure_univ (ρ : ℝ) (f : Lp ℂ 2 (gaussianReal 0 1)) :
    hermiteSpectralMeasure ρ f Set.univ = ENNReal.ofReal (‖f‖ ^ 2) := by
  rw [hermiteSpectralMeasure, Measure.sum_apply _ MeasurableSet.univ]
  refine (tsum_congr fun n => ?_).trans (tsum_ofReal_norm_inner_hermiteLpNorm f)
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply,
    Set.indicator_of_mem (Set.mem_univ _)]
  simp

instance isFiniteMeasure_hermiteSpectralMeasure (ρ : ℝ) (f : Lp ℂ 2 (gaussianReal 0 1)) :
    IsFiniteMeasure (hermiteSpectralMeasure ρ f) :=
  ⟨by rw [hermiteSpectralMeasure_univ]; exact ENNReal.ofReal_lt_top⟩

/-- **The spectral measure is supported on the eigenvalue set**: no mass off `{ρⁿ | n : ℕ}`. -/
theorem hermiteSpectralMeasure_compl_range (ρ : ℝ) (f : Lp ℂ 2 (gaussianReal 0 1)) :
    hermiteSpectralMeasure ρ f (Set.range (fun n : ℕ => (ρ : ℝ) ^ n))ᶜ = 0 := by
  classical
  have hmeas : MeasurableSet (Set.range (fun n : ℕ => (ρ : ℝ) ^ n))ᶜ :=
    (Set.countable_range _).measurableSet.compl
  rw [hermiteSpectralMeasure, Measure.sum_apply _ hmeas]
  refine (tsum_congr fun n => ?_).trans tsum_zero
  rw [Measure.smul_apply, smul_eq_mul, Measure.dirac_apply, Set.indicator_apply]
  have hmem : ¬ ((ρ : ℝ) ^ n ∈ (Set.range (fun n : ℕ => (ρ : ℝ) ^ n))ᶜ) := by
    simp
  rw [if_neg hmem, mul_zero]

/-- **The identity is integrable against the spectral measure.**  Its `ℝ≥0∞` integral is bounded by
the total mass, because `‖ρⁿ‖ ≤ 1` for every `n`. -/
theorem integrable_id_hermiteSpectralMeasure (ρ : ℝ) (hρ : |ρ| ≤ 1)
    (f : Lp ℂ 2 (gaussianReal 0 1)) :
    Integrable (fun t : ℝ => t) (hermiteSpectralMeasure ρ f) := by
  have hstep : ∀ n : ℕ,
      ∫⁻ t : ℝ, ‖t‖ₑ ∂(ENNReal.ofReal (‖inner ℂ (hermiteLpNorm n) f‖ ^ 2) •
        Measure.dirac ((ρ : ℝ) ^ n))
        ≤ ENNReal.ofReal (‖inner ℂ (hermiteLpNorm n) f‖ ^ 2) := by
    intro n
    rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
    refine mul_le_of_le_one_right' ?_
    rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs, abs_pow]
    refine le_trans (ENNReal.ofReal_le_ofReal (pow_le_one₀ (abs_nonneg ρ) hρ)) ?_
    simp
  refine ⟨continuous_id.aestronglyMeasurable, ?_⟩
  rw [hasFiniteIntegral_iff_enorm, hermiteSpectralMeasure, lintegral_sum_measure]
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hstep) ?_
  rw [tsum_ofReal_norm_inner_hermiteLpNorm]
  exact ENNReal.ofReal_lt_top

/-- **The spectral theorem for `P`, as an integral identity**: the spectral measure of `f`
integrates the identity to the quadratic form of `P`,
`∫ t dμ_f = Re ⟨P f, f⟩`.  With `μ_f` of total mass `‖f‖²` this is the discrete spectral
decomposition `Re ⟨P f, f⟩ = ∑ n, ρⁿ ‖⟨eₙ, f⟩‖²` of §12, written as an integral against a
measure on the spectrum. -/
theorem integral_hermiteSpectralMeasure_id (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (f : Lp ℂ 2 (gaussianReal 0 1)) :
    ∫ t : ℝ, t ∂(hermiteSpectralMeasure ρ f)
      = (inner ℂ (gaussianPCNOp ρ s hρs hs f) f).re := by
  have hint : Integrable (fun t : ℝ => t) (hermiteSpectralMeasure ρ f) :=
    integrable_id_hermiteSpectralMeasure ρ (abs_rho_lt_one hρs hs).le f
  have hterm : ∀ n : ℕ,
      ∫ t : ℝ, t ∂(ENNReal.ofReal (‖inner ℂ (hermiteLpNorm n) f‖ ^ 2) •
        Measure.dirac ((ρ : ℝ) ^ n))
        = ρ ^ n * ‖inner ℂ (hermiteLpNorm n) f‖ ^ 2 := by
    intro n
    rw [integral_smul_measure, integral_dirac, smul_eq_mul, ENNReal.toReal_ofReal (sq_nonneg _)]
    ring
  rw [hermiteSpectralMeasure, integral_sum_measure hint, tsum_congr hterm,
    ← gaussianPCNOp_re_inner_eq_tsum ρ s hρs hs f]

/-- **The spectral theorem for the pCN operator, in measure form.**  For every `f ∈ L²(π)` the
measure `hermiteSpectralMeasure ρ f` is a finite Borel measure on the spectrum of `P`, supported
on the eigenvalues `{ρⁿ}`, with total mass `‖f‖²`, and its first moment is the quadratic form
`Re ⟨P f, f⟩`. -/
theorem gaussianPCN_spectral_theorem (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (f : Lp ℂ 2 (gaussianReal 0 1)) :
    hermiteSpectralMeasure ρ f Set.univ = ENNReal.ofReal (‖f‖ ^ 2) ∧
      hermiteSpectralMeasure ρ f (Set.range (fun n : ℕ => (ρ : ℝ) ^ n))ᶜ = 0 ∧
      (∫ t : ℝ, t ∂(hermiteSpectralMeasure ρ f))
        = (inner ℂ (gaussianPCNOp ρ s hρs hs f) f).re :=
  ⟨hermiteSpectralMeasure_univ ρ f, hermiteSpectralMeasure_compl_range ρ f,
    integral_hermiteSpectralMeasure_id ρ s hρs hs f⟩

/-! ## 17. The bounded functional calculus of `P`

The spectral picture of §16 gives `P` the real eigenvalues `ρⁿ` on the Hermite classes.  A
bounded function of those eigenvalues therefore acts diagonally on the Hermite coefficients,
`φ(P) f = ∑' n, φ(ρⁿ) ⟨eₙ, f⟩ eₙ`.  This section constructs that operator for `φ` bounded by `1`
on the spectrum `[-1, 1]`, proves it is a contraction, proves the change-of-variables formula
`∫ φ dμ_f = Re ⟪φ(P) f, f⟫`, and takes `φ = tᵐ` to obtain the higher moments
`∫ tᵐ dμ_f = Re ⟪Pᵐ f, f⟫`.
-/


/-- `|ρⁿ| ≤ 1` when `|ρ| ≤ 1`. -/
theorem abs_pow_le_one {ρ : ℝ} (hρ : |ρ| ≤ 1) (n : ℕ) : |ρ ^ n| ≤ 1 := by
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg ρ) hρ

/-- Every power of a point of `[-1, 1]` stays in `[-1, 1]`. -/
theorem pow_mem_Icc {ρ : ℝ} (hρ : |ρ| ≤ 1) (n : ℕ) : ρ ^ n ∈ Set.Icc (-1 : ℝ) 1 :=
  Set.mem_Icc.mpr (abs_le.mp (abs_pow_le_one hρ n))

/-- `|(ρⁿ)ᵐ| ≤ 1` when `|ρ| ≤ 1`. -/
theorem abs_pow_pow_le_one {ρ : ℝ} (hρ : |ρ| ≤ 1) (m n : ℕ) : |(ρ ^ n) ^ m| ≤ 1 := by
  rw [abs_pow]
  exact pow_le_one₀ (abs_nonneg _) (abs_pow_le_one hρ n)

/-- **The `λ`-weighted coefficient sequence is `ℓ²`**: `∑ n, ‖λₙ ⟨eₙ, f⟩‖² < ∞` whenever
`|λₙ| ≤ 1`. -/
theorem summable_norm_mul_inner (lam : ℕ → ℝ) (hlam : ∀ n, |lam n| ≤ 1)
    (f : Lp ℂ 2 (gaussianReal 0 1)) :
    Summable fun n : ℕ => ‖(lam n : ℂ) * inner ℂ (hermiteLpNorm n) f‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    (summable_norm_inner_hermiteLpNorm f)
  rw [norm_mul, mul_pow]
  refine mul_le_of_le_one_left (by positivity) ?_
  rw [Complex.sq_norm, Complex.normSq_ofReal]
  simpa [pow_two] using (sq_le_one_iff_abs_le_one (lam n)).mpr (hlam n)

/-- The `λ`-weighted coefficient tuple lies in `ℓ²(ℕ)`. -/
theorem memℓp_mul_inner (lam : ℕ → ℝ) (hlam : ∀ n, |lam n| ≤ 1)
    (f : Lp ℂ 2 (gaussianReal 0 1)) :
    Memℓp (fun n => (lam n : ℂ) * inner ℂ (hermiteLpNorm n) f) 2 := by
  refine memℓp_gen ?_
  simpa [Real.rpow_two] using summable_norm_mul_inner lam hlam f

/-- **The Hermite-diagonal operator with eigenvalue sequence `lam`**: multiplication of the `n`-th
Hermite coefficient by `lam n`.  It is defined through the Hilbert-basis identification of `L²(π)`
with `ℓ²(ℕ)`, so it exists for any real sequence; boundedness below uses `|lam n| ≤ 1`. -/
noncomputable def hermiteDiagonal (lam : ℕ → ℝ) (hlam : ∀ n, |lam n| ≤ 1)
    (f : Lp ℂ 2 (gaussianReal 0 1)) : Lp ℂ 2 (gaussianReal 0 1) :=
  gaussianPCNHilbertBasis.repr.symm
    ⟨fun n => (lam n : ℂ) * inner ℂ (hermiteLpNorm n) f, memℓp_mul_inner lam hlam f⟩

/-- The defining series of `hermiteDiagonal`. -/
theorem hasSum_hermiteDiagonal (lam : ℕ → ℝ) (hlam : ∀ n, |lam n| ≤ 1)
    (f : Lp ℂ 2 (gaussianReal 0 1)) :
    HasSum (fun n => ((lam n : ℂ) * inner ℂ (hermiteLpNorm n) f) • hermiteLpNorm n)
      (hermiteDiagonal lam hlam f) := by
  have h := gaussianPCNHilbertBasis.hasSum_repr_symm
    (⟨fun n => (lam n : ℂ) * inner ℂ (hermiteLpNorm n) f, memℓp_mul_inner lam hlam f⟩ :
      ℓ²(ℕ, ℂ))
  simpa [hermiteDiagonal, gaussianPCNHilbertBasis_apply] using h

/-- `hermiteDiagonal` depends on the eigenvalue sequence only pointwise. -/
theorem hermiteDiagonal_congr {lam mu : ℕ → ℝ} (h : ∀ n, lam n = mu n)
    (hlam : ∀ n, |lam n| ≤ 1) (hmu : ∀ n, |mu n| ≤ 1)
    (f : Lp ℂ 2 (gaussianReal 0 1)) :
    hermiteDiagonal lam hlam f = hermiteDiagonal mu hmu f := by
  refine (hasSum_hermiteDiagonal lam hlam f).unique ?_
  simpa [h] using hasSum_hermiteDiagonal mu hmu f

/-- The unit eigenvalue sequence gives back `f`. -/
theorem hermiteDiagonal_one (f : Lp ℂ 2 (gaussianReal 0 1)) :
    hermiteDiagonal (fun _ => 1) (fun _ => by simp) f = f := by
  refine (hasSum_hermiteDiagonal _ _ f).unique ?_
  simpa using hasSum_hermiteLpNorm f

/-- **`hermiteDiagonal` is a contraction**: with `|lam n| ≤ 1` for every `n`,
`‖hermiteDiagonal lam f‖ ≤ ‖f‖`. -/
theorem norm_hermiteDiagonal_le (lam : ℕ → ℝ) (hlam : ∀ n, |lam n| ≤ 1)
    (f : Lp ℂ 2 (gaussianReal 0 1)) : ‖hermiteDiagonal lam hlam f‖ ≤ ‖f‖ := by
  have hnorm : ‖hermiteDiagonal lam hlam f‖
      = Real.sqrt (∑' n : ℕ, ‖(lam n : ℂ) * inner ℂ (hermiteLpNorm n) f‖ ^ 2) := by
    rw [hermiteDiagonal, LinearIsometryEquiv.norm_map,
      lp.norm_eq_tsum_rpow (p := (2 : ℝ≥0∞)) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.sqrt_eq_rpow]
  have hf2 : ‖f‖ = Real.sqrt (∑' n : ℕ, ‖inner ℂ (hermiteLpNorm n) f‖ ^ 2) := by
    rw [tsum_norm_inner_hermiteLpNorm f, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg f)]
  rw [hnorm, hf2]
  refine Real.sqrt_le_sqrt (Summable.tsum_le_tsum (fun n => ?_)
    (summable_norm_mul_inner lam hlam f) (summable_norm_inner_hermiteLpNorm f))
  rw [norm_mul, mul_pow]
  refine mul_le_of_le_one_left (by positivity) ?_
  rw [Complex.sq_norm, Complex.normSq_ofReal]
  simpa [pow_two] using (sq_le_one_iff_abs_le_one (lam n)).mpr (hlam n)

/-- **The quadratic form of a Hermite-diagonal operator**:
`Re ⟪hermiteDiagonal lam f, f⟫ = ∑' n, lam n ‖⟨eₙ, f⟩‖²`. -/
theorem re_inner_hermiteDiagonal (lam : ℕ → ℝ) (hlam : ∀ n, |lam n| ≤ 1)
    (f : Lp ℂ 2 (gaussianReal 0 1)) :
    (inner ℂ (hermiteDiagonal lam hlam f) f).re
      = ∑' n : ℕ, lam n * ‖inner ℂ (hermiteLpNorm n) f‖ ^ 2 := by
  have hP : (starRingEnd ℂ) ((innerSL ℂ f) (hermiteDiagonal lam hlam f))
      = inner ℂ (hermiteDiagonal lam hlam f) f := by
    rw [innerSL_apply_apply]
    exact inner_conj_symm (𝕜 := ℂ) (hermiteDiagonal lam hlam f) f
  have h1 := (hasSum_hermiteDiagonal lam hlam f).map (innerSL ℂ f)
    (innerSL ℂ f).continuous
  have h2 := h1.map (starRingEnd ℂ) continuous_star
  have hterm : ∀ n : ℕ,
      ((starRingEnd ℂ) ((innerSL ℂ f)
        (((lam n : ℂ) * inner ℂ (hermiteLpNorm n) f) • hermiteLpNorm n))).re
        = lam n * ‖inner ℂ (hermiteLpNorm n) f‖ ^ 2 := by
    intro n
    rw [innerSL_apply_apply, inner_smul_right, map_mul, map_mul, Complex.conj_ofReal,
      inner_conj_symm (𝕜 := ℂ) (hermiteLpNorm n) f, mul_assoc, Complex.re_ofReal_mul,
      re_conj_mul_self]
  rw [← hP, ← h2.tsum_eq]
  rw [Complex.re_tsum h2.summable]
  exact tsum_congr hterm

/-- **A Hermite-diagonal operator commutes with `P` in the expected way**: `P` multiplies the
eigenvalues by `ρⁿ`. -/
theorem gaussianPCNOp_hermiteDiagonal (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (lam : ℕ → ℝ) (hlam : ∀ n, |lam n| ≤ 1)
    (hρ : |ρ| ≤ 1) (f : Lp ℂ 2 (gaussianReal 0 1)) :
    gaussianPCNOp ρ s hρs hs (hermiteDiagonal lam hlam f)
      = hermiteDiagonal (fun n => ρ ^ n * lam n)
          (fun n => by
            rw [abs_mul]
            exact mul_le_one₀ (abs_pow_le_one hρ n) (abs_nonneg _) (hlam n)) f := by
  refine ((hasSum_hermiteDiagonal lam hlam f).map _ (gaussianPCNOp ρ s hρs hs).continuous).unique
    ?_
  have hcomp : (⇑(gaussianPCNOp ρ s hρs hs) ∘
      fun n => ((lam n : ℂ) * inner ℂ (hermiteLpNorm n) f) • hermiteLpNorm n)
      = fun n => (((ρ ^ n * lam n : ℝ) : ℂ) * inner ℂ (hermiteLpNorm n) f) •
          hermiteLpNorm n := by
    funext n
    rw [Function.comp_apply, map_smul, gaussianPCNOp_hermiteLpNorm, smul_smul]
    congr 1
    push_cast
    ring
  rw [hcomp]
  exact hasSum_hermiteDiagonal _ _ f

/-- **`Pᵐ` is the Hermite-diagonal operator with eigenvalues `(ρⁿ)ᵐ`.** -/
theorem hermiteDiagonal_gaussianPCNOp_pow (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (hρ : |ρ| ≤ 1) :
    ∀ (m : ℕ) (f : Lp ℂ 2 (gaussianReal 0 1)),
      (gaussianPCNOp ρ s hρs hs)^[m] f
        = hermiteDiagonal (fun n => (ρ ^ n) ^ m) (abs_pow_pow_le_one hρ m) f := by
  intro m
  induction m with
  | zero =>
    intro f
    rw [Function.iterate_zero_apply]
    have h1 : hermiteDiagonal (fun n => (ρ ^ n) ^ 0) (abs_pow_pow_le_one hρ 0) f
        = hermiteDiagonal (fun _ => 1) (fun _ => by simp) f :=
      hermiteDiagonal_congr (fun n => by simp) _ _ f
    rw [h1, hermiteDiagonal_one]
  | succ m ih =>
    intro f
    rw [Function.iterate_succ_apply', ih]
    rw [gaussianPCNOp_hermiteDiagonal ρ s hρs hs (fun n => (ρ ^ n) ^ m)
      (abs_pow_pow_le_one hρ m) hρ f]
    exact hermiteDiagonal_congr (fun n => by rw [pow_succ]; ring) _ _ f

/-- **The functional calculus of `P`**: for `φ` bounded by `1` on the spectrum `[-1, 1]`, `φ(P)`
is the Hermite-diagonal operator with eigenvalues `φ(ρⁿ)`.  No regularity of `φ` is assumed: only
its values on the spectrum enter, and those are bounded by `1`. -/
noncomputable def pcnFunctionalCalculus (ρ : ℝ) (hρ : |ρ| ≤ 1) (φ : ℝ → ℝ)
    (hφ : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |φ t| ≤ 1)
    (f : Lp ℂ 2 (gaussianReal 0 1)) : Lp ℂ 2 (gaussianReal 0 1) :=
  hermiteDiagonal (fun n => φ (ρ ^ n)) (fun n => hφ _ (pow_mem_Icc hρ n)) f

/-- The defining series of `φ(P)`. -/
theorem hasSum_pcnFunctionalCalculus (ρ : ℝ) (hρ : |ρ| ≤ 1) (φ : ℝ → ℝ)
    (hφ : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |φ t| ≤ 1) (f : Lp ℂ 2 (gaussianReal 0 1)) :
    HasSum (fun n => ((φ (ρ ^ n) : ℂ) * inner ℂ (hermiteLpNorm n) f) • hermiteLpNorm n)
      (pcnFunctionalCalculus ρ hρ φ hφ f) := by
  simpa [pcnFunctionalCalculus, mul_assoc] using hasSum_hermiteDiagonal
    (fun n => φ (ρ ^ n)) (fun n => hφ _ (pow_mem_Icc hρ n)) f

/-- **`φ(P)` is a contraction on `L²(π)`**: `‖φ(P) f‖ ≤ ‖f‖` for `φ` bounded by `1` on the
spectrum. -/
theorem norm_pcnFunctionalCalculus_le (ρ : ℝ) (hρ : |ρ| ≤ 1) (φ : ℝ → ℝ)
    (hφ : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |φ t| ≤ 1) (f : Lp ℂ 2 (gaussianReal 0 1)) :
    ‖pcnFunctionalCalculus ρ hρ φ hφ f‖ ≤ ‖f‖ :=
  norm_hermiteDiagonal_le _ _ f

/-- **Change of variables**: the spectral measure of `f` integrates `φ` to the quadratic form of
`φ(P)`, `∫ φ dμ_f = Re ⟪φ(P) f, f⟫`. -/
theorem re_inner_pcnFunctionalCalculus (ρ : ℝ) (hρ : |ρ| ≤ 1) (φ : ℝ → ℝ)
    (hφ : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |φ t| ≤ 1) (f : Lp ℂ 2 (gaussianReal 0 1)) :
    (inner ℂ (pcnFunctionalCalculus ρ hρ φ hφ f) f).re
      = ∑' n : ℕ, φ (ρ ^ n) * ‖inner ℂ (hermiteLpNorm n) f‖ ^ 2 :=
  re_inner_hermiteDiagonal _ _ f

/-- **`Pᵐ` is the functional calculus of `t ↦ tᵐ`.** -/
theorem pcnFunctionalCalculus_pow (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (m : ℕ) (f : Lp ℂ 2 (gaussianReal 0 1)) :
    pcnFunctionalCalculus ρ (abs_rho_lt_one hρs hs).le (fun t => t ^ m)
        (fun t ht => by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg t) (abs_le.mpr ht)) f
      = (gaussianPCNOp ρ s hρs hs)^[m] f := by
  rw [hermiteDiagonal_gaussianPCNOp_pow ρ s hρs hs (abs_rho_lt_one hρs hs).le m f]
  exact hermiteDiagonal_congr (fun n => rfl) _ _ f

/-- **The spectral integral of a bounded function**: for *any* `φ` bounded by `1` on the spectrum,
`∫ φ dμ_f = ∑' n, φ(ρⁿ) ‖⟨eₙ, f⟩‖²`.  No regularity of `φ` is needed: the spectral measure is a
countable sum of weighted Dirac masses, and every function is a.e. strongly measurable for a Dirac
mass (`AEStronglyMeasurable.smul_measure`), so the bound on the spectrum alone makes `φ`
integrable. -/
theorem integral_hermiteSpectralMeasure_of_bound (ρ : ℝ) (hρ : |ρ| ≤ 1) (φ : ℝ → ℝ)
    (hφ : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |φ t| ≤ 1)
    (f : Lp ℂ 2 (gaussianReal 0 1)) :
    ∫ t : ℝ, φ t ∂(hermiteSpectralMeasure ρ f)
      = ∑' n : ℕ, φ (ρ ^ n) * ‖inner ℂ (hermiteLpNorm n) f‖ ^ 2 := by
  have hstep : ∀ n : ℕ,
      ∫⁻ t : ℝ, ‖φ t‖ₑ ∂(ENNReal.ofReal (‖inner ℂ (hermiteLpNorm n) f‖ ^ 2) •
        Measure.dirac ((ρ : ℝ) ^ n))
        ≤ ENNReal.ofReal (‖inner ℂ (hermiteLpNorm n) f‖ ^ 2) := by
    intro n
    rw [lintegral_smul_measure, lintegral_dirac, smul_eq_mul]
    refine mul_le_of_le_one_right' ?_
    rw [← ofReal_norm_eq_enorm, Real.norm_eq_abs]
    exact le_trans (ENNReal.ofReal_le_ofReal (hφ _ (pow_mem_Icc hρ n))) (by simp)
  have haesm : AEStronglyMeasurable (fun t : ℝ => φ t) (hermiteSpectralMeasure ρ f) := by
    rw [hermiteSpectralMeasure, aestronglyMeasurable_sum_measure_iff]
    intro n
    exact aestronglyMeasurable_dirac.smul_measure _
  have hint : Integrable (fun t : ℝ => φ t) (hermiteSpectralMeasure ρ f) := by
    refine ⟨haesm, ?_⟩
    rw [hasFiniteIntegral_iff_enorm, hermiteSpectralMeasure, lintegral_sum_measure]
    refine lt_of_le_of_lt (ENNReal.tsum_le_tsum hstep) ?_
    rw [tsum_ofReal_norm_inner_hermiteLpNorm]
    exact ENNReal.ofReal_lt_top
  have hterm : ∀ n : ℕ,
      ∫ t : ℝ, φ t ∂(ENNReal.ofReal (‖inner ℂ (hermiteLpNorm n) f‖ ^ 2) •
        Measure.dirac ((ρ : ℝ) ^ n))
        = φ (ρ ^ n) * ‖inner ℂ (hermiteLpNorm n) f‖ ^ 2 := by
    intro n
    rw [integral_smul_measure, integral_dirac, smul_eq_mul,
      ENNReal.toReal_ofReal (sq_nonneg _)]
    ring
  rw [hermiteSpectralMeasure, integral_sum_measure hint]
  exact tsum_congr hterm

/-- **The change-of-variables formula for the spectral measure**: `∫ φ dμ_f = Re ⟪φ(P) f, f⟫`,
for every `φ` bounded by `1` on the spectrum — no continuity or measurability of `φ` is needed,
since the spectral measure is discrete. -/
theorem integral_hermiteSpectralMeasure_eq_re_inner (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1)
    (hs : s ≠ 0) (φ : ℝ → ℝ)
    (hφ : ∀ t ∈ Set.Icc (-1 : ℝ) 1, |φ t| ≤ 1) (f : Lp ℂ 2 (gaussianReal 0 1)) :
    ∫ t : ℝ, φ t ∂(hermiteSpectralMeasure ρ f)
      = (inner ℂ (pcnFunctionalCalculus ρ (abs_rho_lt_one hρs hs).le φ hφ f) f).re := by
  rw [integral_hermiteSpectralMeasure_of_bound ρ (abs_rho_lt_one hρs hs).le φ hφ f,
    re_inner_pcnFunctionalCalculus]

/-- **The higher moments of the spectral measure**: for every `m`,
`∫ tᵐ dμ_f = Re ⟪Pᵐ f, f⟫`. -/
theorem integral_hermiteSpectralMeasure_pow (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (m : ℕ) (f : Lp ℂ 2 (gaussianReal 0 1)) :
    ∫ t : ℝ, t ^ m ∂(hermiteSpectralMeasure ρ f)
      = (inner ℂ ((gaussianPCNOp ρ s hρs hs)^[m] f) f).re := by
  rw [integral_hermiteSpectralMeasure_of_bound ρ (abs_rho_lt_one hρs hs).le (fun t => t ^ m)
      (fun t ht => by
        rw [abs_pow]; exact pow_le_one₀ (abs_nonneg t) (abs_le.mpr ht)) f]
  rw [← re_inner_pcnFunctionalCalculus ρ (abs_rho_lt_one hρs hs).le (fun t => t ^ m)
      (fun t ht => by rw [abs_pow]; exact pow_le_one₀ (abs_nonneg t) (abs_le.mpr ht)) f,
    pcnFunctionalCalculus_pow]

/-! ## 18. Positivity of the constructed densities from a sup-norm bound

The §14 transport produces the density `1 + Re (κᵐ f)` of the `m`-th iterate, and §13's
total-variation estimate needs those densities to be nonnegative.  Here that is *proved*, from a
pointwise bound `‖f‖∞ ≤ 1` on the representative of `f`: the pCN kernel is a probability kernel,
so a pointwise bound is preserved by the kernel action, and a deviation bounded by `1` keeps the
density above `0`. -/

/-- **The kernel action preserves a pointwise bound**: if `‖g y‖ ≤ C` for every `y`, then
`‖∫ y, g y ∂(κ x)‖ ≤ C`, because every state measure of a Markov kernel is a probability
measure. -/
theorem norm_kernelIntegral_le (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] (g : ℝ → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hg : ∀ y, ‖g y‖ ≤ C) (x : ℝ) : ‖kernelIntegral κ g x‖ ≤ C := by
  have h1 : ‖kernelIntegral κ g x‖ₑ ≤ ∫⁻ y, ‖g y‖ₑ ∂(κ x) :=
    enorm_integral_le_lintegral_enorm g
  have h2 : ∫⁻ y, ‖g y‖ₑ ∂(κ x) ≤ ENNReal.ofReal C := by
    calc ∫⁻ y, ‖g y‖ₑ ∂(κ x) ≤ ∫⁻ _y, ENNReal.ofReal C ∂(κ x) := by
          refine lintegral_mono fun y => ?_
          rw [← ofReal_norm_eq_enorm]
          exact ENNReal.ofReal_le_ofReal (hg y)
      _ = ENNReal.ofReal C := by rw [lintegral_const, measure_univ, mul_one]
  rw [← ENNReal.ofReal_le_ofReal_iff hC, ofReal_norm_eq_enorm]
  exact h1.trans h2

/-- **The iterated kernel action preserves a pointwise bound.** -/
theorem norm_kernelIntegral_iterate_le (κ : Kernel ℝ ℝ) [IsMarkovKernel κ] (g : ℝ → ℂ) {C : ℝ}
    (hC : 0 ≤ C) (hg : ∀ y, ‖g y‖ ≤ C) (m : ℕ) (x : ℝ) :
    ‖(kernelIntegral κ)^[m] g x‖ ≤ C := by
  induction m generalizing x with
  | zero => simpa using hg x
  | succ m ih =>
      rw [Function.iterate_succ_apply']
      exact norm_kernelIntegral_le κ _ hC ih x

/-- **The `m`-fold pointwise pCN action preserves a pointwise bound.** -/
theorem norm_pcnKernelAction_le (ρ s : ℝ) (f : Lp ℂ 2 (gaussianReal 0 1)) {C : ℝ}
    (hC : 0 ≤ C) (hb : ∀ x, ‖((f : Lp ℂ 2 (gaussianReal 0 1)) : ℝ → ℂ) x‖ ≤ C) (m : ℕ)
    (x : ℝ) : ‖pcnKernelAction ρ s m f x‖ ≤ C :=
  norm_kernelIntegral_iterate_le (gaussianPCNKernel ρ s) _ hC hb m x

/-- **The constructed densities are nonnegative when `‖f‖∞ ≤ 1`**: the deviation is a real part
of a quantity bounded by `1`, so it is at least `-1`. -/
theorem pcnIterateDensity_nonneg_of_bound (ρ s : ℝ)
    (f : Lp ℂ 2 (gaussianReal 0 1))
    (hb : ∀ x, ‖((f : Lp ℂ 2 (gaussianReal 0 1)) : ℝ → ℂ) x‖ ≤ 1) :
    ∀ (m : ℕ) (x : ℝ), 0 ≤ pcnIterateDensity ρ s m f x := by
  intro m x
  have hre : -(1 : ℝ) ≤ (pcnKernelAction ρ s m f x).re := by
    have hnorm : ‖pcnKernelAction ρ s m f x‖ ≤ 1 :=
      norm_pcnKernelAction_le ρ s f zero_le_one hb m x
    have h := (abs_le.mp (Complex.abs_re_le_norm (pcnKernelAction ρ s m f x))).1
    linarith
  change 0 ≤ 1 + (pcnKernelAction ρ s m f x).re
  linarith

/-- **Total-variation geometric convergence with no modelling assumption**: for a mean-zero `f`
whose representative is bounded by `1`, the iterates of the pCN chain satisfy
`‖ν m − π‖_TV ≤ ofReal ((‖f‖/2) |ρ|ᵐ)` — the densities are constructed, and their
nonnegativity is derived rather than assumed. -/
theorem gaussianPCN_tv_geometric_convergence_of_bounded (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1)
    (hs : s ≠ 0) (f : Lp ℂ 2 (gaussianReal 0 1))
    (hmean : inner ℂ (hermiteLpNorm 0) f = 0)
    (hb : ∀ x, ‖((f : Lp ℂ 2 (gaussianReal 0 1)) : ℝ → ℂ) x‖ ≤ 1) :
    ∀ m : ℕ, tvDist (pcnIterateMeasure ρ s m f) (gaussianReal 0 1)
      ≤ ENNReal.ofReal ((‖f‖ / 2) * |ρ| ^ m) :=
  gaussianPCN_tv_geometric_convergence_of_density ρ s hρs hs f hmean
    (pcnIterateDensity_nonneg_of_bound ρ s f hb)

/-! ## 19. The spectrum is the closure of the eigenvalues

§15 proved that `0` lies in the spectrum as a limit of the eigenvalues, and §11 that the eigenvalue
list is exactly `{ρⁿ}`.  This section completes the spectral picture: the spectrum of `P` is
*exactly* the closure of the eigenvalue set, `spectrum ℂ P = closure {ρⁿ | n}`.

The inclusion `closure {ρⁿ} ⊆ spectrum` is closedness of the spectrum plus
`gaussianPCNOp_eigenvalue_mem_spectrum`.  For the converse, a `λ` at positive distance `ε` from
every eigenvalue makes `λ • 1 − P` invertible, and the inverse is exhibited rather than cited: on
Hermite coordinates `λ • 1 − P` multiplies the `n`-th coefficient by `λ − ρⁿ`
(`inner_smul_one_sub_gaussianPCNOp`), so the Hermite-diagonal operator with coefficients
`(λ − ρⁿ)⁻¹` — uniformly bounded by `ε⁻¹` — inverts it, giving injectivity and surjectivity.  The
diagonal construction `hermiteDiagB` used for this is the general uniformly bounded Hermite-diagonal
operator on complex coefficients, of which §17's `hermiteDiagonal` is the bound-`1` real case.
-/


/-- **The `λ`-weighted coefficients are summable in squares** when `‖μₙ‖ ≤ C`. -/
theorem summable_norm_mul_inner_of_bound (mu : ℕ → ℂ) {C : ℝ}
    (hmu : ∀ n, ‖mu n‖ ≤ C) (f : Lp ℂ 2 (gaussianReal 0 1)) :
    Summable fun n : ℕ => ‖mu n * inner ℂ (hermiteLpNorm n) f‖ ^ 2 := by
  refine Summable.of_nonneg_of_le (fun n => by positivity) (fun n => ?_)
    ((summable_norm_inner_hermiteLpNorm f).mul_left (C ^ 2))
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hmu n) 2) (by positivity)

/-- The weighted coefficient tuple lies in `ℓ²(ℕ)`. -/
theorem memℓp_mul_inner_of_bound (mu : ℕ → ℂ) {C : ℝ}
    (hmu : ∀ n, ‖mu n‖ ≤ C) (f : Lp ℂ 2 (gaussianReal 0 1)) :
    Memℓp (fun n => mu n * inner ℂ (hermiteLpNorm n) f) 2 :=
  memℓp_gen (by simpa [Real.rpow_two] using summable_norm_mul_inner_of_bound mu hmu f)

/-- **A Hermite-diagonal operator with a uniformly bounded complex eigenvalue sequence.** -/
noncomputable def hermiteDiagB (mu : ℕ → ℂ) {C : ℝ} (hmu : ∀ n, ‖mu n‖ ≤ C)
    (f : Lp ℂ 2 (gaussianReal 0 1)) : Lp ℂ 2 (gaussianReal 0 1) :=
  gaussianPCNHilbertBasis.repr.symm
    ⟨fun n => mu n * inner ℂ (hermiteLpNorm n) f, memℓp_mul_inner_of_bound mu hmu f⟩

/-- The coordinates of `hermiteDiagB`. -/
theorem repr_hermiteDiagB (mu : ℕ → ℂ) {C : ℝ} (hmu : ∀ n, ‖mu n‖ ≤ C)
    (f : Lp ℂ 2 (gaussianReal 0 1)) :
    gaussianPCNHilbertBasis.repr (hermiteDiagB mu hmu f)
      = ⟨fun n => mu n * inner ℂ (hermiteLpNorm n) f,
          memℓp_mul_inner_of_bound mu hmu f⟩ :=
  LinearIsometryEquiv.apply_symm_apply _ _

/-- The defining series of `hermiteDiagB`. -/
theorem hasSum_hermiteDiagB (mu : ℕ → ℂ) {C : ℝ} (hmu : ∀ n, ‖mu n‖ ≤ C)
    (f : Lp ℂ 2 (gaussianReal 0 1)) :
    HasSum (fun n => (mu n * inner ℂ (hermiteLpNorm n) f) • hermiteLpNorm n)
      (hermiteDiagB mu hmu f) := by
  have h := gaussianPCNHilbertBasis.hasSum_repr_symm
    (⟨fun n => mu n * inner ℂ (hermiteLpNorm n) f,
      memℓp_mul_inner_of_bound mu hmu f⟩ : ℓ²(ℕ, ℂ))
  simpa [hermiteDiagB, gaussianPCNHilbertBasis_apply] using h

/-- **The diagonal acts on a coordinate as multiplication**: `⟪eₙ, D f⟫ = μₙ ⟪eₙ, f⟫`. -/
theorem inner_hermiteDiagB (mu : ℕ → ℂ) {C : ℝ} (hmu : ∀ n, ‖mu n‖ ≤ C)
    (n : ℕ) (f : Lp ℂ 2 (gaussianReal 0 1)) :
    inner ℂ (hermiteLpNorm n) (hermiteDiagB mu hmu f)
      = mu n * inner ℂ (hermiteLpNorm n) f := by
  have h := HilbertBasis.repr_apply_apply gaussianPCNHilbertBasis (hermiteDiagB mu hmu f) n
  rw [repr_hermiteDiagB] at h
  simpa [gaussianPCNHilbertBasis_apply] using h.symm

/-- `hermiteDiagB` depends on the eigenvalue sequence only pointwise. -/
theorem hermiteDiagB_congr {mu nu : ℕ → ℂ} (h : ∀ n, mu n = nu n) {C D : ℝ}
    (hmu : ∀ n, ‖mu n‖ ≤ C) (hnu : ∀ n, ‖nu n‖ ≤ D)
    (f : Lp ℂ 2 (gaussianReal 0 1)) :
    hermiteDiagB mu hmu f = hermiteDiagB nu hnu f := by
  refine gaussianPCNHilbertBasis.repr.injective ?_
  rw [repr_hermiteDiagB, repr_hermiteDiagB]
  refine lp.ext ?_
  funext n
  simp only [h n]

/-- **A uniformly bounded Hermite-diagonal operator is bounded by its bound**:
`‖D f‖ ≤ C ‖f‖`. -/
theorem norm_hermiteDiagB_le (mu : ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C) (hmu : ∀ n, ‖mu n‖ ≤ C)
    (f : Lp ℂ 2 (gaussianReal 0 1)) : ‖hermiteDiagB mu hmu f‖ ≤ C * ‖f‖ := by
  have hnorm : ‖hermiteDiagB mu hmu f‖
      = Real.sqrt (∑' n : ℕ, ‖mu n * inner ℂ (hermiteLpNorm n) f‖ ^ 2) := by
    rw [hermiteDiagB, LinearIsometryEquiv.norm_map,
      lp.norm_eq_tsum_rpow (p := (2 : ℝ≥0∞)) (by norm_num)]
    simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.sqrt_eq_rpow]
  have hf2 : ‖f‖ = Real.sqrt (∑' n : ℕ, ‖inner ℂ (hermiteLpNorm n) f‖ ^ 2) := by
    rw [tsum_norm_inner_hermiteLpNorm f, Real.sqrt_sq_eq_abs, abs_of_nonneg (norm_nonneg f)]
  rw [hnorm, hf2, ← Real.sqrt_sq hC, ← Real.sqrt_mul (sq_nonneg C)]
  refine Real.sqrt_le_sqrt ?_
  rw [← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun n => ?_)
    (summable_norm_mul_inner_of_bound mu hmu f)
    ((summable_norm_inner_hermiteLpNorm f).mul_left (C ^ 2))
  rw [norm_mul, mul_pow]
  exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (norm_nonneg _) (hmu n) 2) (by positivity)

/-- **`P` acts as the Hermite-diagonal operator with eigenvalues `ρⁿ`**, in the uniformly bounded
form. -/
theorem gaussianPCNOp_eq_hermiteDiagB (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (f : Lp ℂ 2 (gaussianReal 0 1)) :
    gaussianPCNOp ρ s hρs hs f
      = hermiteDiagB (fun n : ℕ => (ρ : ℂ) ^ n) (C := 1)
          (fun n => by
            rw [norm_pow, Complex.norm_real]
            exact pow_le_one₀ (abs_nonneg ρ) (abs_rho_lt_one hρs hs).le) f := by
  refine (hasSum_gaussianPCNOp ρ s hρs hs f).unique ?_
  have h := hasSum_hermiteDiagB (fun n : ℕ => (ρ : ℂ) ^ n) (C := 1)
    (fun n => by
      rw [norm_pow, Complex.norm_real]
      exact pow_le_one₀ (abs_nonneg ρ) (abs_rho_lt_one hρs hs).le) f
  simpa [mul_comm] using h

/-- **The coordinate form of `λ • 1 − P`**: `⟪eₙ, (λ − P) f⟫ = (λ − ρⁿ) ⟪eₙ, f⟫`. -/
theorem inner_smul_one_sub_gaussianPCNOp (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (lam : ℂ) (n : ℕ) (f : Lp ℂ 2 (gaussianReal 0 1)) :
    inner ℂ (hermiteLpNorm n)
        ((lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
          - gaussianPCNOp ρ s hρs hs) f)
      = (lam - (ρ : ℂ) ^ n) * inner ℂ (hermiteLpNorm n) f := by
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, inner_sub_right, inner_smul_right,
    gaussianPCNOp_eq_hermiteDiagB ρ s hρs hs f, inner_hermiteDiagB]
  ring

/-- **Coordinates determine a vector**: if `⟪eₙ, h⟫ = ⟪eₙ, g⟫` for every `n`, then `h = g`. -/
theorem eq_of_inner_hermiteLpNorm_eq {h g : Lp ℂ 2 (gaussianReal 0 1)}
    (H : ∀ n : ℕ, inner ℂ (hermiteLpNorm n) h = inner ℂ (hermiteLpNorm n) g) : h = g := by
  have h1 := hasSum_hermiteLpNorm h
  have h2 := hasSum_hermiteLpNorm g
  rw [show (fun n : ℕ => inner ℂ (hermiteLpNorm n) h • hermiteLpNorm n)
      = fun n : ℕ => inner ℂ (hermiteLpNorm n) g • hermiteLpNorm n from
    funext fun n => by rw [H n]] at h1
  exact h1.unique h2

/-- **A positive distance from the eigenvalue closure**: if `λ` is not a limit of eigenvalues then
`ε = infDist λ {ρⁿ}` is positive and `ε ≤ ‖λ − ρⁿ‖` for every `n`. -/
theorem exists_pos_le_norm_sub_eigenvalue (ρ : ℝ) {lam : ℂ}
    (hlam : lam ∉ closure (Set.range fun n : ℕ => (ρ : ℂ) ^ n)) :
    ∃ ε : ℝ, 0 < ε ∧ ∀ n : ℕ, ε ≤ ‖lam - (ρ : ℂ) ^ n‖ := by
  have hne : (Set.range fun n : ℕ => (ρ : ℂ) ^ n).Nonempty := ⟨_, Set.mem_range_self 0⟩
  have hε : 0 < Metric.infDist lam (Set.range fun n : ℕ => (ρ : ℂ) ^ n) :=
    (Metric.infDist_pos_iff_notMem_closure hne).1 hlam
  refine ⟨_, hε, fun n => ?_⟩
  have h := Metric.infDist_le_dist_of_mem (x := lam) (s := Set.range fun n : ℕ => (ρ : ℂ) ^ n)
    (Set.mem_range_self n)
  simpa [dist_eq_norm] using h

/-- **`λ • 1 − P` is inverted by the diagonal of the reciprocal eigenvalue gaps.**  With
`ε ≤ ‖λ − ρⁿ‖` the diagonal operator with eigenvalues `(λ − ρⁿ)⁻¹` inverts `λ • 1 − P` on
coordinates, hence everywhere. -/
theorem smul_one_sub_gaussianPCNOp_invertible (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    {lam : ℂ} {eps : ℝ} (hne : ∀ n : ℕ, lam - (ρ : ℂ) ^ n ≠ 0)
    (hbound : ∀ n : ℕ, ‖(lam - (ρ : ℂ) ^ n)⁻¹‖ ≤ eps⁻¹)
    (g : Lp ℂ 2 (gaussianReal 0 1)) :
    (lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
        - gaussianPCNOp ρ s hρs hs)
      (hermiteDiagB (fun n : ℕ => (lam - (ρ : ℂ) ^ n)⁻¹) hbound g) = g := by
  refine eq_of_inner_hermiteLpNorm_eq fun n => ?_
  rw [inner_smul_one_sub_gaussianPCNOp ρ s hρs hs lam n
    (hermiteDiagB (fun n : ℕ => (lam - (ρ : ℂ) ^ n)⁻¹) hbound g), inner_hermiteDiagB,
    ← mul_assoc, mul_inv_cancel₀ (hne n), one_mul]

/-- **`λ ∉ closure {ρⁿ}` implies `λ` is not in the spectrum.**  The operator `λ • 1 − P` is
bijective: the coordinate form makes injectivity and surjectivity the invertibility of the scalar
factors `λ − ρⁿ`, which are bounded away from `0`. -/
theorem not_mem_spectrum_of_not_mem_closure (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    {lam : ℂ} (hlam : lam ∉ closure (Set.range fun n : ℕ => (ρ : ℂ) ^ n)) :
    lam ∉ spectrum ℂ (gaussianPCNOp ρ s hρs hs) := by
  obtain ⟨eps, heps, hdist⟩ := exists_pos_le_norm_sub_eigenvalue ρ hlam
  have hne : ∀ n : ℕ, lam - (ρ : ℂ) ^ n ≠ 0 := by
    intro n h0
    have h1 := hdist n
    rw [h0, norm_zero] at h1
    linarith
  have hbound : ∀ n : ℕ, ‖(lam - (ρ : ℂ) ^ n)⁻¹‖ ≤ eps⁻¹ := by
    intro n
    simpa [one_div] using one_div_le_one_div_of_le heps (hdist n)
  set T := lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
    - gaussianPCNOp ρ s hρs hs with hT
  have hinj : Function.Injective ⇑T := by
    intro f g hfg
    refine eq_of_inner_hermiteLpNorm_eq fun n => ?_
    have h0 := inner_smul_one_sub_gaussianPCNOp ρ s hρs hs lam n f
    have h1 := inner_smul_one_sub_gaussianPCNOp ρ s hρs hs lam n g
    exact mul_left_cancel₀ (hne n) (by rw [← h0, ← h1, hfg])
  have hsurj : Function.Surjective ⇑T := fun g =>
    ⟨hermiteDiagB (fun n : ℕ => (lam - (ρ : ℂ) ^ n)⁻¹) hbound g,
      smul_one_sub_gaussianPCNOp_invertible ρ s hρs hs hne hbound g⟩
  intro hspec
  rw [spectrum.mem_iff] at hspec
  have halg : (algebraMap ℂ ((Lp ℂ 2 (gaussianReal 0 1)) →L[ℂ] (Lp ℂ 2 (gaussianReal 0 1)))
        lam) = lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1)) := by
    rw [Algebra.algebraMap_eq_smul_one]
    rfl
  rw [halg] at hspec
  exact hspec ((ContinuousLinearMap.isUnit_iff_bijective).2 ⟨hinj, hsurj⟩)

/-- **The spectrum of `P` is the closure of its eigenvalues**: for `ρ² + s² = 1` and `s ≠ 0`,
`spectrum ℂ P = closure {ρⁿ | n : ℕ}`. -/
theorem spectrum_gaussianPCNOp_eq_closure (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) :
    spectrum ℂ (gaussianPCNOp ρ s hρs hs)
      = closure (Set.range fun n : ℕ => (ρ : ℂ) ^ n) := by
  refine Set.Subset.antisymm (fun lam hlam => ?_) ?_
  · by_contra h
    exact not_mem_spectrum_of_not_mem_closure ρ s hρs hs h hlam
  · refine (spectrum.isClosed (gaussianPCNOp ρ s hρs hs)).closure_subset_iff.2 ?_
    rintro _ ⟨n, rfl⟩
    exact gaussianPCNOp_eigenvalue_mem_spectrum ρ s hρs hs n

/-- **The spectrum of `P` lies in the closed unit disc**, since every eigenvalue `ρⁿ` has modulus
at most `1` and the disc is closed. -/
theorem spectrum_gaussianPCNOp_subset_closedBall (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1)
    (hs : s ≠ 0) :
    spectrum ℂ (gaussianPCNOp ρ s hρs hs) ⊆ Metric.closedBall (0 : ℂ) 1 := by
  rw [spectrum_gaussianPCNOp_eq_closure]
  refine Metric.isClosed_closedBall.closure_subset_iff.2 ?_
  rintro z ⟨n, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right, norm_pow, Complex.norm_real]
  exact pow_le_one₀ (abs_nonneg ρ) (abs_rho_lt_one hρs hs).le

/-! ## 20. The resolvent as a Hermite-diagonal operator, and compactness of `P`

Two loose ends left open by §19 are settled here.

First, the diagonal `hermiteDiagB` is upgraded to a continuous linear map `hermiteDiagBCLM` with
`‖hermiteDiagBCLM μ‖ ≤ C` (`hermiteDiagB_add`, `hermiteDiagB_smul`,
`norm_hermiteDiagBCLM_le`).  This makes the inverse of `λ • 1 − P` a bounded operator rather than a
bare function: for `λ` outside `closure {ρⁿ}` the resolvent is exhibited explicitly and bounded by
`(infDist λ {ρⁿ})⁻¹` (`hermiteDiagB_smul_one_sub_gaussianPCNOp`,
`exists_resolvent_hermiteDiagB`), inverting on both sides.

Second, `P` is proved **compact**.  Truncating the eigenvalue sequence to its first `N` terms gives
a finite-rank operator `truncDiag ρ hρ1 N`, whose range lies in the span of `e_0, …, e_{N-1}`
(`range_truncDiag_le_span`, `truncDiag_apply`) and is therefore compact
(`isCompactOperator_of_finiteDimensional_range` — stated for arbitrary complex normed spaces,
since Mathlib has no finite-rank form of compactness); and `‖P − truncDiag N‖ ≤ |ρ| ^ N → 0`
(`norm_gaussianPCNOp_sub_truncDiag_le`, `tendsto_truncDiag`), so `P` is a norm limit of compact
operators (`isCompactOperator_gaussianPCNOp`).  Compactness is the standard reason `0` is the only
possible accumulation point of the spectrum — which §19 and §15 already show concretely; that
general consequence is not formalized as a separate statement.
-/


/-- `hermiteDiagB` is additive in the vector. -/
theorem hermiteDiagB_add (mu : ℕ → ℂ) {C : ℝ} (hmu : ∀ n, ‖mu n‖ ≤ C)
    (f g : Lp ℂ 2 (gaussianReal 0 1)) :
    hermiteDiagB mu hmu (f + g) = hermiteDiagB mu hmu f + hermiteDiagB mu hmu g := by
  refine eq_of_inner_hermiteLpNorm_eq fun n => ?_
  simp only [inner_hermiteDiagB, inner_add_right, mul_add]

/-- `hermiteDiagB` is homogeneous. -/
theorem hermiteDiagB_smul (mu : ℕ → ℂ) {C : ℝ} (hmu : ∀ n, ‖mu n‖ ≤ C) (c : ℂ)
    (f : Lp ℂ 2 (gaussianReal 0 1)) :
    hermiteDiagB mu hmu (c • f) = c • hermiteDiagB mu hmu f := by
  refine eq_of_inner_hermiteLpNorm_eq fun n => ?_
  simp only [inner_hermiteDiagB, inner_smul_right]
  ring

/-- **The uniformly bounded Hermite-diagonal operator as a continuous linear map.** -/
noncomputable def hermiteDiagBCLM (mu : ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hmu : ∀ n, ‖mu n‖ ≤ C) :
    Lp ℂ 2 (gaussianReal 0 1) →L[ℂ] Lp ℂ 2 (gaussianReal 0 1) :=
  ({ toFun := hermiteDiagB mu hmu
     map_add' := hermiteDiagB_add mu hmu
     map_smul' := hermiteDiagB_smul mu hmu } :
      Lp ℂ 2 (gaussianReal 0 1) →ₗ[ℂ] Lp ℂ 2 (gaussianReal 0 1)).mkContinuous C
    (norm_hermiteDiagB_le mu hC hmu)

theorem hermiteDiagBCLM_apply (mu : ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hmu : ∀ n, ‖mu n‖ ≤ C) (f : Lp ℂ 2 (gaussianReal 0 1)) :
    hermiteDiagBCLM mu hC hmu f = hermiteDiagB mu hmu f := rfl

theorem norm_hermiteDiagBCLM_le (mu : ℕ → ℂ) {C : ℝ} (hC : 0 ≤ C)
    (hmu : ∀ n, ‖mu n‖ ≤ C) : ‖hermiteDiagBCLM mu hC hmu‖ ≤ C :=
  ContinuousLinearMap.opNorm_le_bound _ hC fun f => by
    rw [hermiteDiagBCLM_apply]
    exact norm_hermiteDiagB_le mu hC hmu f

/-- The diagonal of reciprocal eigenvalue gaps inverts `λ • 1 − P` on the left. -/
theorem hermiteDiagB_smul_one_sub_gaussianPCNOp (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1)
    (hs : s ≠ 0) {lam : ℂ} {eps : ℝ} (hne : ∀ n : ℕ, lam - (ρ : ℂ) ^ n ≠ 0)
    (hbound : ∀ n : ℕ, ‖(lam - (ρ : ℂ) ^ n)⁻¹‖ ≤ eps⁻¹)
    (f : Lp ℂ 2 (gaussianReal 0 1)) :
    hermiteDiagB (fun n : ℕ => (lam - (ρ : ℂ) ^ n)⁻¹) hbound
      ((lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
        - gaussianPCNOp ρ s hρs hs) f) = f := by
  refine eq_of_inner_hermiteLpNorm_eq fun n => ?_
  rw [inner_hermiteDiagB, inner_smul_one_sub_gaussianPCNOp, ← mul_assoc,
    inv_mul_cancel₀ (hne n), one_mul]

/-- **The resolvent of `P` off the spectrum, with an explicit inverse.**  For `λ` outside
`closure {ρⁿ}` the map `λ • 1 − P` is inverted by the Hermite-diagonal operator with eigenvalues
`(λ − ρⁿ)⁻¹`, and the inverse is bounded by `(infDist λ {ρⁿ})⁻¹`. -/
theorem exists_resolvent_hermiteDiagB (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    {lam : ℂ} (hlam : lam ∉ closure (Set.range fun n : ℕ => (ρ : ℂ) ^ n)) :
    ∃ R : Lp ℂ 2 (gaussianReal 0 1) →L[ℂ] Lp ℂ 2 (gaussianReal 0 1),
      (∀ g : Lp ℂ 2 (gaussianReal 0 1),
        (lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
          - gaussianPCNOp ρ s hρs hs) (R g) = g) ∧
      (∀ f : Lp ℂ 2 (gaussianReal 0 1),
        R ((lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
          - gaussianPCNOp ρ s hρs hs) f) = f) ∧
      ‖R‖ ≤ (Metric.infDist lam (Set.range fun n : ℕ => (ρ : ℂ) ^ n))⁻¹ := by
  have hne0 : (Set.range fun n : ℕ => (ρ : ℂ) ^ n).Nonempty := ⟨_, Set.mem_range_self 0⟩
  have hinf : 0 < Metric.infDist lam (Set.range fun n : ℕ => (ρ : ℂ) ^ n) :=
    (Metric.infDist_pos_iff_notMem_closure hne0).1 hlam
  have hdist : ∀ n : ℕ,
      Metric.infDist lam (Set.range fun n : ℕ => (ρ : ℂ) ^ n) ≤ ‖lam - (ρ : ℂ) ^ n‖ := by
    intro n
    have h := Metric.infDist_le_dist_of_mem (x := lam)
      (s := Set.range fun n : ℕ => (ρ : ℂ) ^ n) (Set.mem_range_self n)
    simpa [dist_eq_norm] using h
  have hne : ∀ n : ℕ, lam - (ρ : ℂ) ^ n ≠ 0 := by
    intro n h0
    have h1 := hdist n
    rw [h0, norm_zero] at h1
    linarith
  have hbound : ∀ n : ℕ,
      ‖(lam - (ρ : ℂ) ^ n)⁻¹‖ ≤ (Metric.infDist lam (Set.range fun n : ℕ => (ρ : ℂ) ^ n))⁻¹ := by
    intro n
    simpa [one_div] using one_div_le_one_div_of_le hinf (hdist n)
  have hC : (0 : ℝ) ≤ (Metric.infDist lam (Set.range fun n : ℕ => (ρ : ℂ) ^ n))⁻¹ :=
    inv_nonneg.2 hinf.le
  refine ⟨hermiteDiagBCLM (fun n : ℕ => (lam - (ρ : ℂ) ^ n)⁻¹) hC hbound, ?_, ?_, ?_⟩
  · intro g
    simpa [hermiteDiagBCLM_apply] using
      smul_one_sub_gaussianPCNOp_invertible ρ s hρs hs hne hbound g
  · intro f
    simpa [hermiteDiagBCLM_apply] using
      hermiteDiagB_smul_one_sub_gaussianPCNOp ρ s hρs hs hne hbound f
  · exact norm_hermiteDiagBCLM_le _ hC hbound

/-- A continuous linear map with finite-dimensional range is a compact operator. -/
theorem isCompactOperator_of_finiteDimensional_range {E F : Type*} [NormedAddCommGroup E]
    [NormedSpace ℂ E] [NormedAddCommGroup F] [NormedSpace ℂ F] (T : E →L[ℂ] F)
    (hfin : FiniteDimensional ℂ (LinearMap.range T.toLinearMap)) : IsCompactOperator T := by
  set p := LinearMap.range T.toLinearMap with hp
  haveI : FiniteDimensional ℂ p := hfin
  haveI : ProperSpace p := FiniteDimensional.proper ℂ p
  refine (isCompactOperator_iff_image_closedBall_subset_compact (T : E →ₗ[ℂ] F)
    zero_lt_one).2
    ⟨((↑) : p → F) '' Metric.closedBall (0 : p) ‖T‖,
      (isCompact_closedBall (0 : p) ‖T‖).image continuous_subtype_val, ?_⟩
  rintro _ ⟨x, hx, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right] at hx
  refine ⟨⟨T x, (LinearMap.mem_range).2 ⟨x, rfl⟩⟩, ?_, rfl⟩
  rw [Metric.mem_closedBall, dist_zero_right]
  exact (T.le_opNorm x).trans (mul_le_of_le_one_right (norm_nonneg T) hx)

/-- **The coordinates of `P`**: `⟪eₙ, P f⟫ = ρⁿ ⟪eₙ, f⟫`. -/
theorem inner_gaussianPCNOp (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) (n : ℕ)
    (f : Lp ℂ 2 (gaussianReal 0 1)) :
    inner ℂ (hermiteLpNorm n) (gaussianPCNOp ρ s hρs hs f)
      = (ρ : ℂ) ^ n * inner ℂ (hermiteLpNorm n) f := by
  rw [gaussianPCNOp_eq_hermiteDiagB, inner_hermiteDiagB]

/-- The eigenvalue bound for the truncated sequence. -/
theorem norm_ite_pow_le_one (ρ : ℝ) (hρ1 : |ρ| ≤ 1) (N n : ℕ) :
    ‖if n < N then (ρ : ℂ) ^ n else 0‖ ≤ 1 := by
  by_cases h : n < N
  · rw [if_pos h, norm_pow, Complex.norm_real]
    exact pow_le_one₀ (abs_nonneg ρ) hρ1
  · rw [if_neg h]
    simp

/-- **The truncation of `P` to its first `N` eigenvalues.** -/
noncomputable def truncDiag (ρ : ℝ) (hρ1 : |ρ| ≤ 1) (N : ℕ) :
    Lp ℂ 2 (gaussianReal 0 1) →L[ℂ] Lp ℂ 2 (gaussianReal 0 1) :=
  hermiteDiagBCLM (fun n : ℕ => if n < N then (ρ : ℂ) ^ n else 0) (C := 1) zero_le_one
    (norm_ite_pow_le_one ρ hρ1 N)

/-- The truncation in terms of the basis: a finite sum of rank-one pieces. -/
theorem truncDiag_apply (ρ : ℝ) (hρ1 : |ρ| ≤ 1) (N : ℕ)
    (f : Lp ℂ 2 (gaussianReal 0 1)) :
    truncDiag ρ hρ1 N f
      = ∑ n ∈ Finset.range N, ((ρ : ℂ) ^ n * inner ℂ (hermiteLpNorm n) f) • hermiteLpNorm n := by
  rw [show truncDiag ρ hρ1 N f
      = hermiteDiagB (fun n : ℕ => if n < N then (ρ : ℂ) ^ n else 0)
          (norm_ite_pow_le_one ρ hρ1 N) f from rfl]
  rw [← (hasSum_hermiteDiagB _ (norm_ite_pow_le_one ρ hρ1 N) f).tsum_eq]
  rw [tsum_eq_sum (L := SummationFilter.unconditional ℕ) (s := Finset.range N) ?_]
  · refine Finset.sum_congr rfl fun n hn => ?_
    rw [if_pos (Finset.mem_range.1 hn)]
  · intro b hb
    rw [Finset.mem_range, not_lt] at hb
    rw [if_neg (not_lt.2 hb), zero_mul, zero_smul]

/-- The range of the truncation lies in a finite-dimensional subspace. -/
theorem range_truncDiag_le_span (ρ : ℝ) (hρ1 : |ρ| ≤ 1) (N : ℕ) :
    LinearMap.range (truncDiag ρ hρ1 N).toLinearMap
      ≤ Submodule.span ℂ (hermiteLpNorm '' (↑(Finset.range N) : Set ℕ)) := by
  rintro _ ⟨f, rfl⟩
  change truncDiag ρ hρ1 N f ∈ Submodule.span ℂ (hermiteLpNorm '' (↑(Finset.range N) : Set ℕ))
  rw [truncDiag_apply]
  refine Submodule.sum_mem _ fun n hn => Submodule.smul_mem _ _ (Submodule.subset_span ?_)
  exact Set.mem_image_of_mem _ (Finset.mem_coe.2 hn)

/-- The truncation has finite-dimensional range. -/
theorem finiteDimensional_range_truncDiag (ρ : ℝ) (hρ1 : |ρ| ≤ 1) (N : ℕ) :
    FiniteDimensional ℂ (LinearMap.range (truncDiag ρ hρ1 N).toLinearMap) := by
  haveI : FiniteDimensional ℂ
      (Submodule.span ℂ (hermiteLpNorm '' (↑(Finset.range N) : Set ℕ))) :=
    FiniteDimensional.span_of_finite ℂ
      (Set.Finite.image _ (Finset.finite_toSet (Finset.range N)))
  exact Submodule.finiteDimensional_of_le (range_truncDiag_le_span ρ hρ1 N)

/-- **The truncations of `P` are compact operators.** -/
theorem isCompactOperator_truncDiag (ρ : ℝ) (hρ1 : |ρ| ≤ 1) (N : ℕ) :
    IsCompactOperator (truncDiag ρ hρ1 N) :=
  isCompactOperator_of_finiteDimensional_range _ (finiteDimensional_range_truncDiag ρ hρ1 N)

/-- The residual eigenvalue sequence is bounded by `|ρ| ^ N` from index `N` on. -/
theorem norm_ite_zero_pow_le (ρ : ℝ) (hρ1 : |ρ| ≤ 1) (N : ℕ) :
    ∀ n : ℕ, ‖if n < N then (0 : ℂ) else (ρ : ℂ) ^ n‖ ≤ |ρ| ^ N := by
  intro n
  by_cases h : n < N
  · rw [if_pos h]
    simp
  · rw [if_neg h, norm_pow, Complex.norm_real]
    exact pow_le_pow_of_le_one (abs_nonneg ρ) hρ1 (Nat.le_of_not_lt h)

/-- **`P` minus its truncation** is the diagonal operator on the residual eigenvalues. -/
theorem gaussianPCNOp_sub_truncDiag_apply (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (hρ1 : |ρ| ≤ 1) (N : ℕ) (f : Lp ℂ 2 (gaussianReal 0 1)) :
    (gaussianPCNOp ρ s hρs hs - truncDiag ρ hρ1 N) f
      = hermiteDiagB (fun n : ℕ => if n < N then 0 else (ρ : ℂ) ^ n)
          (norm_ite_zero_pow_le ρ hρ1 N) f := by
  refine eq_of_inner_hermiteLpNorm_eq fun n => ?_
  rw [ContinuousLinearMap.sub_apply, inner_sub_right, inner_gaussianPCNOp]
  rw [show truncDiag ρ hρ1 N f
      = hermiteDiagB (fun n : ℕ => if n < N then (ρ : ℂ) ^ n else 0)
          (norm_ite_pow_le_one ρ hρ1 N) f from rfl, inner_hermiteDiagB, inner_hermiteDiagB]
  by_cases h : n < N <;> simp [h]

/-- **The truncation error is bounded by `|ρ| ^ N`.** -/
theorem norm_gaussianPCNOp_sub_truncDiag_le (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (hρ1 : |ρ| ≤ 1) (N : ℕ) (f : Lp ℂ 2 (gaussianReal 0 1)) :
    ‖(gaussianPCNOp ρ s hρs hs - truncDiag ρ hρ1 N) f‖ ≤ |ρ| ^ N * ‖f‖ := by
  rw [gaussianPCNOp_sub_truncDiag_apply]
  exact norm_hermiteDiagB_le _ (by positivity) _ f

/-- **`P` is a norm limit of its truncations.** -/
theorem tendsto_truncDiag (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (hρ1 : |ρ| ≤ 1) :
    Tendsto (fun N : ℕ => truncDiag ρ hρ1 N) atTop (𝓝 (gaussianPCNOp ρ s hρs hs)) := by
  have hb : ∀ N : ℕ, ‖truncDiag ρ hρ1 N - gaussianPCNOp ρ s hρs hs‖ ≤ |ρ| ^ N := by
    intro N
    refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun f => ?_
    have h := norm_gaussianPCNOp_sub_truncDiag_le ρ s hρs hs hρ1 N f
    rw [ContinuousLinearMap.sub_apply, norm_sub_rev]
    simpa only [ContinuousLinearMap.sub_apply] using h
  have h2 := squeeze_zero_norm hb
    (tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg ρ) (abs_rho_lt_one hρs hs))
  have h3 : Tendsto (fun N : ℕ => (truncDiag ρ hρ1 N - gaussianPCNOp ρ s hρs hs)
      + gaussianPCNOp ρ s hρs hs) atTop (𝓝 (0 + gaussianPCNOp ρ s hρs hs)) :=
    h2.add tendsto_const_nhds
  simpa using h3

/-- **`P` is a compact operator**: it is the norm limit of the finite-rank truncations. -/
theorem isCompactOperator_gaussianPCNOp (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) :
    IsCompactOperator (gaussianPCNOp ρ s hρs hs) :=
  isCompactOperator_of_tendsto
    (tendsto_truncDiag ρ s hρs hs (abs_rho_lt_one hρs hs).le)
    (Eventually.of_forall fun N =>
      isCompactOperator_truncDiag ρ (abs_rho_lt_one hρs hs).le N)

/-! ## 21. The spectrum is discrete off `0`, countable, and has spectral radius `1`

§19 identified `spectrum ℂ P = closure {ρⁿ}`, §20 proved `P` compact.  Those two facts are made
explicit here in the form a compact operator's spectrum normally takes — a discrete set whose only
possible accumulation point is `0`.

* `pow_ne_pow_of_abs_lt_one` — the eigenvalue list is **injective** for `0 < |ρ| < 1`.
* `norm_pow_sub_pow_ge` — the eigenvalues are **separated**:
  `|ρ| ^ min m n * (1 - |ρ|) ≤ ‖ρᵐ - ρⁿ‖`.
* `spectrum_gaussianPCNOp_eq_insert_zero` — for `|ρ| < 1` the spectrum is *exactly*
  `{0} ∪ {ρⁿ | n : ℕ}`: the closure adds `0` and nothing else.
* `countable_spectrum_gaussianPCNOp` — the spectrum is countable.
* `spectralRadius_gaussianPCNOp` — **the spectral radius of `P` is `1`**.
* `exists_ball_inter_spectrum_eq` — every nonzero spectral point is isolated, so `0` is the only
  possible accumulation point.
* `zero_mem_closure_spectrum_diff` — and `0` *is* an accumulation point when `ρ ≠ 0`.

The `|ρ| < 1` hypothesis is not a convenience: for `|ρ| = 1` the closure of the eigenvalue list is
the whole unit circle, which no compact operator's spectrum can be — but that general consequence
(Riesz/Fredholm theory) is not formalized, so the hypothesis is kept explicit instead of derived
from compactness.
-/


/-- Distinct powers of `ρ` are distinct when `0 < |ρ| < 1`: `ρ ^ m = ρ ^ n` with `m ≠ n` would
force `|ρ| ^ |n - m| = 1`, contradicting `|ρ| < 1`. -/
theorem pow_ne_pow_of_abs_lt_one {ρ : ℝ} (hρ0 : ρ ≠ 0) (hρ1 : |ρ| < 1) {m n : ℕ}
    (hmn : m ≠ n) : ρ ^ m ≠ ρ ^ n := by
  intro h
  have hne : ∀ k : ℕ, |ρ| ^ k ≠ 0 := fun k => pow_ne_zero k (abs_ne_zero.2 hρ0)
  have hlt : ∀ k : ℕ, 0 < k → |ρ| ^ k < 1 := fun k hk =>
    pow_lt_one₀ (abs_nonneg ρ) hρ1 hk.ne'
  have hpow : |ρ| ^ m = |ρ| ^ n := by rw [← abs_pow, ← abs_pow, h]
  rcases lt_or_gt_of_ne hmn with hmn' | hmn'
  · have h2 : |ρ| ^ n = |ρ| ^ m * |ρ| ^ (n - m) := by
      rw [← pow_add, Nat.add_sub_cancel' hmn'.le]
    have h1 : |ρ| ^ (n - m) = 1 := mul_left_cancel₀ (hne m) (by rw [← h2, hpow, mul_one])
    exact absurd h1 (hlt (n - m) (by omega)).ne
  · have h2 : |ρ| ^ m = |ρ| ^ n * |ρ| ^ (m - n) := by
      rw [← pow_add, Nat.add_sub_cancel' hmn'.le]
    have h1 : |ρ| ^ (m - n) = 1 := mul_left_cancel₀ (hne n) (by rw [← h2, ← hpow, mul_one])
    exact absurd h1 (hlt (m - n) (by omega)).ne

/-- **The eigenvalues of `P` are separated**: for `|ρ| < 1` and `m ≠ n`,
`|ρ| ^ min m n * (1 - |ρ|) ≤ ‖ρᵐ - ρⁿ‖`.  This is a reverse-triangle bound: the two norms differ
by `|ρ| ^ min m n * (1 - |ρ| ^ |n - m|)`, and `|ρ| ^ |n - m| ≤ |ρ|`. -/
theorem norm_pow_sub_pow_ge {ρ : ℝ} (hρ1 : |ρ| < 1) {m n : ℕ} (hmn : m ≠ n) :
    |ρ| ^ min m n * (1 - |ρ|) ≤ ‖(ρ : ℂ) ^ m - (ρ : ℂ) ^ n‖ := by
  have hnorm : ∀ k : ℕ, ‖(ρ : ℂ) ^ k‖ = |ρ| ^ k := fun k => by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
  rcases lt_or_gt_of_ne hmn with hlt | hlt
  · rw [min_eq_left hlt.le]
    have hrev := norm_sub_norm_le ((ρ : ℂ) ^ m) ((ρ : ℂ) ^ n)
    rw [hnorm m, hnorm n] at hrev
    have hstep : |ρ| ^ n ≤ |ρ| ^ m * |ρ| := by
      have := pow_le_pow_of_le_one (abs_nonneg ρ) hρ1.le (show m + 1 ≤ n by omega)
      rwa [pow_succ] at this
    nlinarith [hrev, hstep]
  · rw [min_eq_right hlt.le, norm_sub_rev]
    have hrev := norm_sub_norm_le ((ρ : ℂ) ^ n) ((ρ : ℂ) ^ m)
    rw [hnorm m, hnorm n] at hrev
    have hstep : |ρ| ^ m ≤ |ρ| ^ n * |ρ| := by
      have := pow_le_pow_of_le_one (abs_nonneg ρ) hρ1.le (show n + 1 ≤ m by omega)
      rwa [pow_succ] at this
    nlinarith [hrev, hstep]

/-- **The spectrum of `P` for `|ρ| < 1` is exactly the eigenvalue list together with `0`**: the
eigenvalues `ρⁿ` have no other accumulation point, because `‖ρⁿ‖ → 0` decays geometrically while
the powers grow apart from each other. -/
theorem spectrum_gaussianPCNOp_eq_insert_zero (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (hρ1 : |ρ| < 1) :
    spectrum ℂ (gaussianPCNOp ρ s hρs hs) = insert 0 (Set.range fun n : ℕ => (ρ : ℂ) ^ n) := by
  rw [spectrum_gaussianPCNOp_eq_closure ρ s hρs hs]
  have hlim : Tendsto (fun n : ℕ => ‖(ρ : ℂ) ^ n‖) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => |ρ| ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg ρ) hρ1
    simpa [norm_pow, Complex.norm_real, Real.norm_eq_abs] using h
  refine Set.Subset.antisymm (fun lam hlam => ?_) (fun lam hlam => ?_)
  · by_cases h0 : lam = 0
    · exact Set.mem_insert_iff.2 (Or.inl h0)
    · refine Set.mem_insert_iff.2 (Or.inr ?_)
      have hpos : 0 < ‖lam‖ := norm_pos_iff.2 h0
      obtain ⟨N, hN⟩ : ∃ N : ℕ, ∀ n ≥ N, ‖(ρ : ℂ) ^ n‖ < ‖lam‖ / 2 := by
        obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hlim) (‖lam‖ / 2) (by positivity)
        exact ⟨N, fun n hn => by
          have h := hN n hn
          rwa [Real.dist_eq, sub_zero, abs_norm] at h⟩
      have hsplit : Set.range (fun n : ℕ => (ρ : ℂ) ^ n)
          = (fun n : ℕ => (ρ : ℂ) ^ n) '' {n : ℕ | n < N}
            ∪ (fun n : ℕ => (ρ : ℂ) ^ n) '' {n : ℕ | N ≤ n} := by
        rw [← Set.image_univ, ← Set.image_union]
        congr 1
        refine (Set.eq_univ_of_forall fun n => ?_).symm
        rcases lt_or_ge n N with h | h
        · exact Or.inl h
        · exact Or.inr h
      have hAfin : ((fun n : ℕ => (ρ : ℂ) ^ n) '' {n : ℕ | n < N}).Finite :=
        Set.Finite.image _ (Set.finite_Iio N)
      have hsub : Set.range (fun n : ℕ => (ρ : ℂ) ^ n)
          ⊆ (fun n : ℕ => (ρ : ℂ) ^ n) '' {n : ℕ | n < N}
            ∪ Metric.closedBall (0 : ℂ) (‖lam‖ / 2) := by
        rintro _ ⟨n, rfl⟩
        by_cases hn : n < N
        · exact Or.inl ⟨n, hn, rfl⟩
        · refine Or.inr ?_
          rw [Metric.mem_closedBall, dist_zero_right]
          exact (hN n (by omega)).le
      have hclosed : IsClosed ((fun n : ℕ => (ρ : ℂ) ^ n) '' {n : ℕ | n < N}
          ∪ Metric.closedBall (0 : ℂ) (‖lam‖ / 2)) :=
        hAfin.isClosed.union Metric.isClosed_closedBall
      rcases hclosed.closure_subset_iff.2 hsub hlam with hfin | hball
      · obtain ⟨n, _, rfl⟩ := hfin
        exact Set.mem_range_self n
      · rw [Metric.mem_closedBall, dist_zero_right] at hball
        linarith
  · rcases Set.mem_insert_iff.1 hlam with rfl | ⟨n, rfl⟩
    · rw [Metric.mem_closure_iff]
      intro ε hε
      obtain ⟨N, hN⟩ : ∃ N : ℕ, ‖(ρ : ℂ) ^ N‖ < ε := by
        obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hlim) ε hε
        exact ⟨N, by simpa [Real.dist_eq, sub_zero, abs_norm] using hN N le_rfl⟩
      exact ⟨_, Set.mem_range_self N, by simpa using hN⟩
    · exact subset_closure (Set.mem_range_self n)

/-- **The spectrum of `P` is countable** when `|ρ| < 1`: it is the eigenvalue list plus `0`. -/
theorem countable_spectrum_gaussianPCNOp (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (hρ1 : |ρ| < 1) : (spectrum ℂ (gaussianPCNOp ρ s hρs hs)).Countable := by
  rw [spectrum_gaussianPCNOp_eq_insert_zero ρ s hρs hs hρ1]
  exact Set.Countable.insert 0 (Set.countable_range _)

/-- **The spectral radius of `P` is `1`**: `1 = ρ⁰` is an eigenvalue, so `1 ≤ spectralRadius`, and
the spectrum lies in the closed unit disc, so `spectralRadius ≤ 1`. -/
theorem spectralRadius_gaussianPCNOp (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) :
    spectralRadius ℂ (gaussianPCNOp ρ s hρs hs) = 1 := by
  refine le_antisymm ?_ ?_
  · rw [spectralRadius]
    refine iSup₂_le (α := ℝ≥0∞) fun k hk => ?_
    have h := spectrum_gaussianPCNOp_subset_closedBall ρ s hρs hs hk
    rw [Metric.mem_closedBall, dist_zero_right] at h
    exact ENNReal.coe_le_coe.2 (by rw [← NNReal.coe_le_coe, coe_nnnorm]; exact h)
  · rw [spectralRadius]
    have h1 : (1 : ℂ) ∈ spectrum ℂ (gaussianPCNOp ρ s hρs hs) := by
      simpa using gaussianPCNOp_eigenvalue_mem_spectrum ρ s hρs hs 0
    have := le_iSup₂ (f := fun k (_ : k ∈ spectrum ℂ (gaussianPCNOp ρ s hρs hs)) =>
      (‖k‖₊ : ℝ≥0∞)) (1 : ℂ) h1
    simpa using this

/-- **All nonzero spectral points of `P` are isolated**: for `|ρ| < 1` and `0 ≠ λ ∈ spectrum`, some
ball around `λ` meets the spectrum only at `λ`.  Since `0` is also a limit point of the eigenvalues,
`0` is the *only* accumulation point of the spectrum. -/
theorem exists_ball_inter_spectrum_eq (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (hρ0 : ρ ≠ 0) (hρ1 : |ρ| < 1) {lam : ℂ}
    (hlam : lam ∈ spectrum ℂ (gaussianPCNOp ρ s hρs hs)) (hne : lam ≠ 0) :
    ∃ ε > 0, ∀ mu ∈ spectrum ℂ (gaussianPCNOp ρ s hρs hs), ‖mu - lam‖ < ε → mu = lam := by
  rw [spectrum_gaussianPCNOp_eq_insert_zero ρ s hρs hs hρ1] at hlam ⊢
  rcases Set.mem_insert_iff.1 hlam with rfl | ⟨n, rfl⟩
  · exact absurd rfl hne
  · have hpos : 0 < ‖(ρ : ℂ) ^ n‖ := by
      rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
      exact pow_pos (abs_pos.2 hρ0) n
    have hgap : 0 < |ρ| ^ n * (1 - |ρ|) := by
      have : 0 < 1 - |ρ| := by linarith
      exact mul_pos (pow_pos (abs_pos.2 hρ0) n) this
    refine ⟨min (‖(ρ : ℂ) ^ n‖ / 2) (|ρ| ^ n * (1 - |ρ|) / 2), ?_, fun mu hmu hdist => ?_⟩
    · positivity
    · rcases Set.mem_insert_iff.1 hmu with rfl | ⟨m, rfl⟩
      · have h2 : ‖(0 : ℂ) - (ρ : ℂ) ^ n‖ = ‖(ρ : ℂ) ^ n‖ := by rw [zero_sub, norm_neg]
        rw [h2] at hdist
        have : ‖(ρ : ℂ) ^ n‖ / 2 < ‖(ρ : ℂ) ^ n‖ := by linarith
        linarith [min_le_left (‖(ρ : ℂ) ^ n‖ / 2) (|ρ| ^ n * (1 - |ρ|) / 2)]
      · by_contra hmn
        have hmn' : m ≠ n := fun h => hmn (by rw [h])
        have hge := norm_pow_sub_pow_ge hρ1 hmn'
        have hmono : |ρ| ^ n * (1 - |ρ|) ≤ |ρ| ^ min m n * (1 - |ρ|) := by
          have hle := pow_le_pow_of_le_one (abs_nonneg ρ) hρ1.le (min_le_right m n)
          have : 0 ≤ 1 - |ρ| := by linarith
          exact mul_le_mul_of_nonneg_right hle this
        have : |ρ| ^ n * (1 - |ρ|) / 2 < |ρ| ^ n * (1 - |ρ|) := by linarith
        linarith [min_le_right (‖(ρ : ℂ) ^ n‖ / 2) (|ρ| ^ n * (1 - |ρ|) / 2)]

/-- **`0` is an accumulation point of the spectrum** when `ρ ≠ 0`: the eigenvalues `ρⁿ → 0` are
nonzero spectral points converging to `0`. -/
theorem zero_mem_closure_spectrum_diff (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    (hρ0 : ρ ≠ 0) :
    0 ∈ closure (spectrum ℂ (gaussianPCNOp ρ s hρs hs) \ {0}) := by
  have hnorm : ∀ n : ℕ, ‖(ρ : ℂ) ^ n‖ = |ρ| ^ n := fun n => by
    rw [norm_pow, Complex.norm_real, Real.norm_eq_abs]
  have hlim : Tendsto (fun n : ℕ => ‖(ρ : ℂ) ^ n‖) atTop (𝓝 0) := by
    have h : Tendsto (fun n : ℕ => |ρ| ^ n) atTop (𝓝 0) :=
      tendsto_pow_atTop_nhds_zero_of_lt_one (abs_nonneg ρ) (abs_rho_lt_one hρs hs)
    simpa [hnorm] using h
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨N, hN⟩ := (Metric.tendsto_atTop.1 hlim) ε hε
  refine ⟨(ρ : ℂ) ^ (N + 1), ⟨gaussianPCNOp_eigenvalue_mem_spectrum ρ s hρs hs (N + 1), ?_⟩, ?_⟩
  · simp only [Set.mem_singleton_iff]
    exact pow_ne_zero _ (Complex.ofReal_ne_zero.2 hρ0)
  · have h := hN (N + 1) (by omega)
    have hlt : ‖(ρ : ℂ) ^ (N + 1)‖ < ε := by
      rwa [Real.dist_eq, sub_zero, abs_norm] at h
    simpa [dist_eq_norm] using hlt


/-! ## 22. The resolvent: self-adjointness and the norm identity

`P` is self-adjoint (§9, `gaussianPCNOp_isSelfAdjoint`), and for a self-adjoint operator the
resolvent obeys `‖(λ - P)⁻¹‖ = 1 / dist(λ, σ P)`, with the resolvent self-adjoint when `λ` is real.
Both statements are proved here from the diagonal form, for *any* inverse of `λ • 1 - P`; no
abstract Hilbert-space spectral theorem is invoked.

* `norm_hermiteLpNorm` — the orthonormal eigenfunctions are unit vectors, `‖eₙ‖ = 1`.
* `smul_one_sub_gaussianPCNOp_hermiteLpNorm` — `(λ • 1 - P) eₙ = (λ - ρⁿ) • eₙ`.
* `apply_hermiteLpNorm_of_inverse` — **any right inverse of `λ • 1 - P` acts diagonally**:
  `R eₙ = (λ - ρⁿ)⁻¹ • eₙ`.
* `inv_infDist_le_norm_resolvent` — hence `(infDist λ {ρⁿ})⁻¹ ≤ ‖R‖` for such an `R`: the reciprocal
  distance is a **lower** bound for the norm.  The matching upper bound is §20's
  `norm_hermiteDiagBCLM_le` inside `exists_resolvent_hermiteDiagB`.
* `exists_resolvent_norm_eq` — **the norm identity**
  `‖(λ - P)⁻¹‖ = (infDist λ {ρⁿ})⁻¹` for `λ` off `closure {ρⁿ}`.
* `star_eq_self_of_inverse` — **the resolvent at a real spectral parameter is self-adjoint**:
  `star R = R`.
* `exists_selfAdjoint_resolvent_norm_eq` — both statements at once.

The lower bound uses only the eigenrelation and `‖eₙ‖ = 1`, so it holds for *every* inverse of
`λ • 1 - P`; the explicit diagonal construction enters only in the upper bound.  The eigenvalue list
plays the role of the spectrum here: `closure {ρⁿ}` is the spectrum by §19.
-/


/-- The orthonormal Hermite classes are unit vectors. -/
theorem norm_hermiteLpNorm (n : ℕ) : ‖hermiteLpNorm n‖ = 1 := by
  have h1 : inner ℂ (hermiteLpNorm n) (hermiteLpNorm n) = 1 := by
    rw [orthonormal_iff_ite.1 orthonormal_hermiteLpNorm n n, if_pos rfl]
  have h2 : ((‖hermiteLpNorm n‖ : ℂ)) ^ 2 = 1 := by
    have h := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (hermiteLpNorm n)
    rw [h1] at h
    exact h.symm
  have h3 : ‖hermiteLpNorm n‖ ^ 2 = 1 := by exact_mod_cast h2
  nlinarith [norm_nonneg (hermiteLpNorm n)]

/-- **`λ • 1 - P` acts on the eigenfunctions as a scalar**: `(λ • 1 - P) eₙ = (λ - ρⁿ) • eₙ`. -/
theorem smul_one_sub_gaussianPCNOp_hermiteLpNorm (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1)
    (hs : s ≠ 0) (lam : ℂ) (n : ℕ) :
    ((lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
        - gaussianPCNOp ρ s hρs hs) (hermiteLpNorm n))
      = (lam - (ρ : ℂ) ^ n) • hermiteLpNorm n := by
  rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.id_apply, gaussianPCNOp_hermiteLpNorm, sub_smul]

/-- **A right inverse of `λ • 1 - P` acts diagonally**: it sends `eₙ` to `(λ - ρⁿ)⁻¹ • eₙ`.  This
needs no information about *which* inverse was chosen — only the inverse equation. -/
theorem apply_hermiteLpNorm_of_inverse (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    {lam : ℂ} (hlam : lam ∉ closure (Set.range fun n : ℕ => (ρ : ℂ) ^ n))
    (R : Lp ℂ 2 (gaussianReal 0 1) →L[ℂ] Lp ℂ 2 (gaussianReal 0 1))
    (hR : ∀ f, R (((lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
        - gaussianPCNOp ρ s hρs hs)) f) = f) (n : ℕ) :
    R (hermiteLpNorm n) = (lam - (ρ : ℂ) ^ n)⁻¹ • hermiteLpNorm n := by
  have hne : lam - (ρ : ℂ) ^ n ≠ 0 := by
    intro h0
    apply hlam
    have hmem : lam ∈ Set.range fun n : ℕ => (ρ : ℂ) ^ n :=
      ⟨n, (sub_eq_zero.1 h0).symm⟩
    exact subset_closure hmem
  have h1 : R (((lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
      - gaussianPCNOp ρ s hρs hs)) (hermiteLpNorm n)) = hermiteLpNorm n := hR _
  rw [smul_one_sub_gaussianPCNOp_hermiteLpNorm, map_smul] at h1
  calc R (hermiteLpNorm n)
      = (lam - (ρ : ℂ) ^ n)⁻¹ • ((lam - (ρ : ℂ) ^ n) • R (hermiteLpNorm n)) := by
        rw [smul_smul, inv_mul_cancel₀ hne, one_smul]
    _ = (lam - (ρ : ℂ) ^ n)⁻¹ • hermiteLpNorm n := by rw [h1]


/-- **The resolvent's norm is at least the reciprocal distance to the eigenvalue list**: a right
inverse `R` of `λ • 1 - P` satisfies `(infDist λ {ρⁿ})⁻¹ ≤ ‖R‖`, because `R` sends `eₙ` to
`(λ - ρⁿ)⁻¹ • eₙ` and `‖eₙ‖ = 1`. -/
theorem inv_infDist_le_norm_resolvent (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    {lam : ℂ} (hlam : lam ∉ closure (Set.range fun n : ℕ => (ρ : ℂ) ^ n))
    (R : Lp ℂ 2 (gaussianReal 0 1) →L[ℂ] Lp ℂ 2 (gaussianReal 0 1))
    (hR : ∀ f, R (((lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
        - gaussianPCNOp ρ s hρs hs)) f) = f) :
    (Metric.infDist lam (Set.range fun n : ℕ => (ρ : ℂ) ^ n))⁻¹ ≤ ‖R‖ := by
  set S : Set ℂ := Set.range fun n : ℕ => (ρ : ℂ) ^ n with hS
  have hne : S.Nonempty := ⟨_, Set.mem_range_self 0⟩
  have hinf : 0 < Metric.infDist lam S := (Metric.infDist_pos_iff_notMem_closure hne).1 hlam
  have hact : ∀ n : ℕ, R (hermiteLpNorm n) = (lam - (ρ : ℂ) ^ n)⁻¹ • hermiteLpNorm n :=
    apply_hermiteLpNorm_of_inverse ρ s hρs hs hlam R hR
  have hdist : ∀ n : ℕ, Metric.infDist lam S ≤ ‖lam - (ρ : ℂ) ^ n‖ := by
    intro n
    have h := Metric.infDist_le_dist_of_mem (x := lam) (s := S) (Set.mem_range_self n)
    simpa [dist_eq_norm] using h
  have hle : ∀ e : ℝ, 0 < e → (Metric.infDist lam S + e)⁻¹ ≤ ‖R‖ := by
    intro e he
    have hlt : Metric.infDist lam S < Metric.infDist lam S + e := lt_add_of_pos_right _ he
    obtain ⟨y, hy, hyd⟩ := (Metric.infDist_lt_iff hne).1 hlt
    obtain ⟨n, rfl⟩ := hy
    have hpos : 0 < ‖lam - (ρ : ℂ) ^ n‖ := lt_of_lt_of_le hinf (hdist n)
    have hd : dist lam ((ρ : ℂ) ^ n) = ‖lam - (ρ : ℂ) ^ n‖ := dist_eq_norm _ _
    rw [hd] at hyd
    have hstep : (Metric.infDist lam S + e)⁻¹ ≤ (‖lam - (ρ : ℂ) ^ n‖)⁻¹ :=
      by simpa [one_div] using one_div_le_one_div_of_le hpos hyd.le
    have hRe : ‖R (hermiteLpNorm n)‖ = (‖lam - (ρ : ℂ) ^ n‖)⁻¹ := by
      rw [hact n, norm_smul, norm_inv, norm_hermiteLpNorm, mul_one]
    calc (Metric.infDist lam S + e)⁻¹ ≤ (‖lam - (ρ : ℂ) ^ n‖)⁻¹ := hstep
      _ = ‖R (hermiteLpNorm n)‖ := hRe.symm
      _ ≤ ‖R‖ * ‖hermiteLpNorm n‖ := ContinuousLinearMap.le_opNorm R _
      _ = ‖R‖ := by rw [norm_hermiteLpNorm, mul_one]
  have htend : Tendsto (fun e : ℝ => (Metric.infDist lam S + e)⁻¹) (𝓝[>] (0 : ℝ))
      (𝓝 (Metric.infDist lam S)⁻¹) := by
    have hcont : ContinuousAt (fun e : ℝ => (Metric.infDist lam S + e)⁻¹) 0 := by
      have h1 : ContinuousAt (fun e : ℝ => Metric.infDist lam S + e) 0 :=
        continuousAt_const.add continuousAt_id
      exact h1.inv₀ (by simpa using hinf.ne')
    have h1 : Tendsto (fun e : ℝ => (Metric.infDist lam S + e)⁻¹) (𝓝 (0 : ℝ))
        (𝓝 (Metric.infDist lam S)⁻¹) := by
      simpa using hcont.tendsto
    exact h1.mono_left nhdsWithin_le_nhds
  refine le_of_tendsto htend ?_
  filter_upwards [self_mem_nhdsWithin] with e he using hle e he


/-- **The norm identity for the resolvent**: `λ • 1 - P` is invertible off the spectrum, and every
inverse has norm exactly `(infDist λ {ρⁿ})⁻¹` — the reciprocal distance from `λ` to the eigenvalue
list.  This is the concrete form of the classical statement `‖(λ - P)⁻¹‖ = 1 / dist(λ, σ P)` for a
self-adjoint operator. -/
theorem exists_resolvent_norm_eq (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) {lam : ℂ}
    (hlam : lam ∉ closure (Set.range fun n : ℕ => (ρ : ℂ) ^ n)) :
    ∃ R : Lp ℂ 2 (gaussianReal 0 1) →L[ℂ] Lp ℂ 2 (gaussianReal 0 1),
      (∀ g : Lp ℂ 2 (gaussianReal 0 1),
        ((lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
          - gaussianPCNOp ρ s hρs hs)) (R g) = g) ∧
      (∀ f : Lp ℂ 2 (gaussianReal 0 1),
        R (((lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
          - gaussianPCNOp ρ s hρs hs)) f) = f) ∧
      ‖R‖ = (Metric.infDist lam (Set.range fun n : ℕ => (ρ : ℂ) ^ n))⁻¹ := by
  obtain ⟨R, hleft, hright, hle⟩ := exists_resolvent_hermiteDiagB ρ s hρs hs hlam
  exact ⟨R, hleft, hright,
    le_antisymm hle (inv_infDist_le_norm_resolvent ρ s hρs hs hlam R hright)⟩

/-- **The resolvent of a self-adjoint `P` at a real spectral parameter is self-adjoint**: any
two-sided inverse of `a • 1 - P` with `a : ℝ` satisfies `star R = R`.  (`P` itself is self-adjoint
by `gaussianPCNOp_isSelfAdjoint`.) -/
theorem star_eq_self_of_inverse (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) (a : ℝ)
    (R : Lp ℂ 2 (gaussianReal 0 1) →L[ℂ] Lp ℂ 2 (gaussianReal 0 1))
    (hleft : ∀ g : Lp ℂ 2 (gaussianReal 0 1),
      ((a : ℂ) • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
        - gaussianPCNOp ρ s hρs hs) (R g) = g)
    (hright : ∀ f : Lp ℂ 2 (gaussianReal 0 1),
      R (((a : ℂ) • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
        - gaussianPCNOp ρ s hρs hs) f) = f) :
    star R = R := by
  set A : Lp ℂ 2 (gaussianReal 0 1) →L[ℂ] Lp ℂ 2 (gaussianReal 0 1) :=
    (a : ℂ) • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
      - gaussianPCNOp ρ s hρs hs with hAdef
  have hP : star (gaussianPCNOp ρ s hρs hs) = gaussianPCNOp ρ s hρs hs :=
    ContinuousLinearMap.isSelfAdjoint_iff'.1 (gaussianPCNOp_isSelfAdjoint ρ s hρs hs)
  have hA : star A = A := by
    have hid : star (ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1)))
        = ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1)) :=
      ContinuousLinearMap.adjoint_id
    simp only [hAdef, star_sub, star_smul, hid, hP]
    simp
  have h1 : A * R = 1 := ContinuousLinearMap.ext hleft
  have h2 : R * A = 1 := ContinuousLinearMap.ext hright
  have h3 : star R * A = 1 := by
    have h := congrArg star h1
    rwa [star_mul, hA, star_one] at h
  calc star R = star R * 1 := (mul_one _).symm
    _ = star R * (A * R) := by rw [h1]
    _ = (star R * A) * R := (mul_assoc _ _ _).symm
    _ = 1 * R := by rw [h3]
    _ = R := one_mul R


/-- **The resolvent of `P` at a real spectral parameter is self-adjoint and has norm exactly the
reciprocal distance to the eigenvalue list** — the classical pair of statements for a self-adjoint
operator, here proved from the diagonal representation. -/
theorem exists_selfAdjoint_resolvent_norm_eq (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    {a : ℝ} (ha : (a : ℂ) ∉ closure (Set.range fun n : ℕ => (ρ : ℂ) ^ n)) :
    ∃ R : Lp ℂ 2 (gaussianReal 0 1) →L[ℂ] Lp ℂ 2 (gaussianReal 0 1),
      (∀ g : Lp ℂ 2 (gaussianReal 0 1),
        ((a : ℂ) • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
          - gaussianPCNOp ρ s hρs hs) (R g) = g) ∧
      (∀ f : Lp ℂ 2 (gaussianReal 0 1),
        R (((a : ℂ) • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
          - gaussianPCNOp ρ s hρs hs) f) = f) ∧
      star R = R ∧
      ‖R‖ = (Metric.infDist (a : ℂ) (Set.range fun n : ℕ => (ρ : ℂ) ^ n))⁻¹ := by
  obtain ⟨R, hleft, hright, hnorm⟩ := exists_resolvent_norm_eq ρ s hρs hs ha
  exact ⟨R, hleft, hright, star_eq_self_of_inverse ρ s hρs hs a R hleft hright, hnorm⟩

/-! ## 23. The resolvent equation

With `A_λ = λ • 1 - P`, the resolvents `R(λ) = A_λ⁻¹` satisfy the **first resolvent identity**

`R(λ) - R(μ) = (μ - λ) • R(λ) R(μ)`.

The proof is pure algebra: telescope `R(λ) - R(μ) = R(λ)(A_μ - A_λ)R(μ)` and use
`A_μ - A_λ = (μ - λ) • 1`.  Only two of the four inverse identities are needed — `R(λ) A_λ = 1`
and `A_μ R(μ) = 1` — and no information about the diagonal form is used.

* `resolvent_sub_eq` — the resolvent equation.
* `resolvent_commute` — **resolvents at distinct parameters commute**.
* `norm_resolvent_sub_le` — **the resolvent map is Lipschitz**:
  `‖R(λ) - R(μ)‖ ≤ ‖μ - λ‖ ‖R(λ)‖ ‖R(μ)‖`.
* `exists_resolvent_sub_eq` — the existence form: both resolvents exist off `closure {ρⁿ}`, obey the
  equation, and `‖R(λ) - R(μ)‖ ≤ ‖μ - λ‖ / (dist(λ, {ρⁿ}) dist(μ, {ρⁿ}))` by §22's norm identity.

The norm bound is what makes the resolvent continuous in `λ` off the spectrum.  It is not a
differentiability statement, and the equation is stated for two parameters — no analytic
continuation or resolvent calculus (Riesz projections, Dunford calculus) is built here.
-/

/-- **The resolvent equation (first resolvent identity)** for `P`: for two-sided inverses `Rl` of
`lam • 1 - P` and `Rm` of `mu • 1 - P`, `Rl - Rm = (mu - lam) • (Rl * Rm)`.  The proof is the
algebraic telescoping `Rl - Rm = Rl (A_mu - A_lam) Rm`; only the two inverse identities
`Rl * A_lam = 1` and `A_mu * Rm = 1` enter.  No spectral information is used. -/
theorem resolvent_sub_eq (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) (lam mu : ℂ)
    (Rl Rm : Lp ℂ 2 (gaussianReal 0 1) →L[ℂ] Lp ℂ 2 (gaussianReal 0 1))
    (hl : Rl * ((lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
        - gaussianPCNOp ρ s hρs hs)) = 1)
    (hr : ((mu • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
        - gaussianPCNOp ρ s hρs hs)) * Rm = 1) :
    Rl - Rm = (mu - lam) • (Rl * Rm) := by
  set P := gaussianPCNOp ρ s hρs hs with hP
  set A : Lp ℂ 2 (gaussianReal 0 1) →L[ℂ] Lp ℂ 2 (gaussianReal 0 1) :=
    lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1)) - P with hAdef
  set B : Lp ℂ 2 (gaussianReal 0 1) →L[ℂ] Lp ℂ 2 (gaussianReal 0 1) :=
    mu • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1)) - P with hBdef
  have hBA : B - A = (mu - lam) • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1)) := by
    rw [hAdef, hBdef, sub_sub_sub_cancel_right, sub_smul]
  have hkey : Rl - Rm = Rl * (B - A) * Rm := by
    calc Rl - Rm = Rl * 1 - 1 * Rm := by rw [mul_one, one_mul]
      _ = Rl * (B * Rm) - (Rl * A) * Rm := by rw [hr, hl, mul_one, one_mul]
      _ = Rl * (B - A) * Rm := by noncomm_ring
  rw [hkey, hBA, mul_smul_comm, smul_mul_assoc]
  congr 1

/-- **Resolvents at distinct spectral parameters commute** — a corollary of the resolvent equation
applied twice, with the roles of `lam` and `mu` exchanged. -/
theorem resolvent_commute (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) {lam mu : ℂ}
    (Rl Rm : Lp ℂ 2 (gaussianReal 0 1) →L[ℂ] Lp ℂ 2 (gaussianReal 0 1))
    (hl : Rl * ((lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
        - gaussianPCNOp ρ s hρs hs)) = 1)
    (hr : ((mu • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
        - gaussianPCNOp ρ s hρs hs)) * Rm = 1)
    (hl' : ((lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
        - gaussianPCNOp ρ s hρs hs)) * Rl = 1)
    (hr' : Rm * ((mu • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
        - gaussianPCNOp ρ s hρs hs)) = 1) (hne : mu ≠ lam) :
    Rl * Rm = Rm * Rl := by
  have h1 := resolvent_sub_eq ρ s hρs hs lam mu Rl Rm hl hr
  have h2 := resolvent_sub_eq ρ s hρs hs mu lam Rm Rl hr' hl'
  have h3 : (mu - lam) • (Rm * Rl) = Rl - Rm := by
    have hcoef : mu - lam = -(lam - mu) := by ring
    rw [hcoef, neg_smul, ← h2, neg_sub]
  have h4 : (mu - lam) • (Rl * Rm - Rm * Rl) = 0 := by
    rw [smul_sub, ← h1, h3, sub_self]
  have hne' : mu - lam ≠ 0 := sub_ne_zero.2 hne
  have h5 : Rl * Rm - Rm * Rl = 0 := by
    rcases smul_eq_zero.1 h4 with h | h
    · exact absurd h hne'
    · exact h
  exact sub_eq_zero.1 h5

/-- **The resolvent map is Lipschitz in the spectral parameter**:
`‖R(λ) - R(μ)‖ ≤ ‖μ - λ‖ ‖R(λ)‖ ‖R(μ)‖`. -/
theorem norm_resolvent_sub_le (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) {lam mu : ℂ}
    (Rl Rm : Lp ℂ 2 (gaussianReal 0 1) →L[ℂ] Lp ℂ 2 (gaussianReal 0 1))
    (hl : Rl * ((lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
        - gaussianPCNOp ρ s hρs hs)) = 1)
    (hr : ((mu • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
        - gaussianPCNOp ρ s hρs hs)) * Rm = 1) :
    ‖Rl - Rm‖ ≤ ‖mu - lam‖ * ‖Rl‖ * ‖Rm‖ := by
  rw [resolvent_sub_eq ρ s hρs hs lam mu Rl Rm hl hr, norm_smul, mul_assoc]
  exact mul_le_mul_of_nonneg_left (norm_mul_le Rl Rm) (norm_nonneg _)

/-- **The resolvent equation for `P`, in existence form**: for two parameters off the spectrum both
resolvents exist, satisfy `Rl - Rm = (mu - lam) • (Rl * Rm)`, and obey the Lipschitz bound
`‖Rl - Rm‖ ≤ ‖mu - lam‖ / (dist(lam, {ρⁿ}) dist(mu, {ρⁿ}))`. -/
theorem exists_resolvent_sub_eq (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) {lam mu : ℂ}
    (hlam : lam ∉ closure (Set.range fun n : ℕ => (ρ : ℂ) ^ n))
    (hmu : mu ∉ closure (Set.range fun n : ℕ => (ρ : ℂ) ^ n)) :
    ∃ Rl Rm : Lp ℂ 2 (gaussianReal 0 1) →L[ℂ] Lp ℂ 2 (gaussianReal 0 1),
      (∀ f : Lp ℂ 2 (gaussianReal 0 1),
        Rl (((lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
          - gaussianPCNOp ρ s hρs hs)) f) = f) ∧
      (∀ g : Lp ℂ 2 (gaussianReal 0 1),
        ((lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
          - gaussianPCNOp ρ s hρs hs)) (Rl g) = g) ∧
      (∀ f : Lp ℂ 2 (gaussianReal 0 1),
        Rm (((mu • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
          - gaussianPCNOp ρ s hρs hs)) f) = f) ∧
      (∀ g : Lp ℂ 2 (gaussianReal 0 1),
        ((mu • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
          - gaussianPCNOp ρ s hρs hs)) (Rm g) = g) ∧
      Rl - Rm = (mu - lam) • (Rl * Rm) ∧
      ‖Rl - Rm‖ ≤ ‖mu - lam‖
        * (Metric.infDist lam (Set.range fun n : ℕ => (ρ : ℂ) ^ n))⁻¹
        * (Metric.infDist mu (Set.range fun n : ℕ => (ρ : ℂ) ^ n))⁻¹ := by
  obtain ⟨Rl, hll, hlr, hln⟩ := exists_resolvent_norm_eq ρ s hρs hs hlam
  obtain ⟨Rm, hml, hmr, hmn⟩ := exists_resolvent_norm_eq ρ s hρs hs hmu
  have hl : Rl * ((lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
      - gaussianPCNOp ρ s hρs hs)) = 1 := ContinuousLinearMap.ext hlr
  have hr : ((mu • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
      - gaussianPCNOp ρ s hρs hs)) * Rm = 1 := ContinuousLinearMap.ext hml
  refine ⟨Rl, Rm, hlr, hll, hmr, hml, ?_, ?_⟩
  · exact resolvent_sub_eq ρ s hρs hs lam mu Rl Rm hl hr
  · have h := norm_resolvent_sub_le ρ s hρs hs (lam := lam) (mu := mu) Rl Rm hl hr
    rw [hln, hmn] at h
    exact h

/-! ## 24. Analyticity at infinity: the Neumann series

Off the closed unit disc the resolvent is a power series in `1 / λ`:

`R(λ) = (λ • 1 - P)⁻¹ = ∑ₙ (λ ^ (n + 1))⁻¹ • Pⁿ`,  for `1 < ‖λ‖`.

Since `P` is a contraction (§24's `norm_gaussianPCNOp_pow_le`), the series converges absolutely in
operator norm, and its partial sums telescope:
`(λ • 1 - P) * ∑_{n<N} (λ ^ (n + 1))⁻¹ • Pⁿ = 1 - (λ ^ N)⁻¹ • P^N → 1`.

* `norm_gaussianPCNOp_pow_le` — **`P` is a contraction**: `‖Pᵏ f‖ ≤ ‖f‖` for every `f`, `k`.
* `opNorm_gaussianPCNOp_pow_le` — `‖Pᵏ‖ ≤ 1` in operator norm.
* `summable_resolvent_series` — the Neumann series is absolutely convergent for `1 < ‖λ‖`.
* `hasSum_resolvent_series` — **the series sums to the resolvent**.
-/


/-- **`P` is a contraction in `L²(π)`**: `‖Pᵏ f‖ ≤ ‖f‖` for every `f` and every `k`.  Split `f` into
its component along `e₀` (which `P` fixes) and the orthogonal complement (on which `Pᵏ` decays by
`|ρ|ᵏ`); the two parts stay orthogonal, so Pythagoras gives the bound. -/
theorem norm_gaussianPCNOp_pow_le (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) (k : ℕ)
    (f : Lp ℂ 2 (gaussianReal 0 1)) :
    ‖((gaussianPCNOp ρ s hρs hs) ^ k) f‖ ≤ ‖f‖ := by
  set P := gaussianPCNOp ρ s hρs hs with hP
  have hPstar : star P = P :=
    ContinuousLinearMap.isSelfAdjoint_iff'.1 (gaussianPCNOp_isSelfAdjoint ρ s hρs hs)
  have hPs : star (P ^ k) = P ^ k := by
    induction k with
    | zero => simp
    | succ k ih =>
        rw [pow_succ, star_mul, ih, hPstar]
        simpa using pow_mul_comm P 1 k
  set a : ℂ := inner ℂ (hermiteLpNorm 0) f with ha
  set g : Lp ℂ 2 (gaussianReal 0 1) := f - a • hermiteLpNorm 0 with hg
  have hsplit : f = a • hermiteLpNorm 0 + g := by
    rw [hg]; abel
  have h11 : inner ℂ (hermiteLpNorm 0) (hermiteLpNorm 0) = 1 := by
    rw [orthonormal_iff_ite.1 orthonormal_hermiteLpNorm 0 0, if_pos rfl]
  have hg0 : inner ℂ (hermiteLpNorm 0) g = 0 := by
    rw [hg, inner_sub_right, inner_smul_right, ha, h11]
    ring
  have hfix : (P ^ k) (a • hermiteLpNorm 0) = a • hermiteLpNorm 0 := by
    rw [map_smul, gaussianPCNOp_pow_hermiteLpNorm]
    simp
  have hcoef0 : inner ℂ (hermiteLpNorm 0) ((P ^ k) g) = 0 := by
    have h1 : inner ℂ (hermiteLpNorm 0) ((P ^ k) g)
        = inner ℂ ((star (P ^ k)) (hermiteLpNorm 0)) g :=
      (ContinuousLinearMap.adjoint_inner_left (P ^ k) g (hermiteLpNorm 0)).symm
    rw [h1, hPs, gaussianPCNOp_pow_hermiteLpNorm]
    simp [hg0]
  have horth : inner ℂ ((P ^ k) (a • hermiteLpNorm 0)) ((P ^ k) g) = 0 := by
    rw [hfix, inner_smul_left, hcoef0]
    simp
  have hdec : (P ^ k) f = (P ^ k) (a • hermiteLpNorm 0) + (P ^ k) g := by
    rw [hsplit, map_add]
  have hpy : ‖(P ^ k) f‖ ^ 2
      = ‖(P ^ k) (a • hermiteLpNorm 0)‖ ^ 2 + ‖(P ^ k) g‖ ^ 2 := by
    rw [hdec]
    simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ horth
  have hgdec : ‖f‖ ^ 2 = ‖a • hermiteLpNorm 0‖ ^ 2 + ‖g‖ ^ 2 := by
    have h : inner ℂ (a • hermiteLpNorm 0) g = 0 := by
      rw [inner_smul_left, hg0]; simp
    rw [hsplit]
    simpa [pow_two] using norm_add_sq_eq_norm_sq_add_norm_sq_of_inner_eq_zero _ _ h
  have hstep : ‖(P ^ k) g‖ ^ 2 ≤ ‖g‖ ^ 2 := by
    have hle := norm_gaussianPCNOp_pow_le_of_inner_eq_zero ρ s hρs hs k hg0
    have h1 : |ρ| ^ k ≤ 1 := pow_le_one₀ (abs_nonneg ρ) (abs_rho_lt_one hρs hs).le
    have hle' : ‖(P ^ k) g‖ ≤ ‖g‖ := by
      refine hle.trans ?_
      nlinarith [h1, norm_nonneg g]
    exact pow_le_pow_left₀ (norm_nonneg _) hle' 2
  have hsq : ‖(P ^ k) f‖ ^ 2 ≤ ‖f‖ ^ 2 := by
    calc ‖(P ^ k) f‖ ^ 2
        = ‖(P ^ k) (a • hermiteLpNorm 0)‖ ^ 2 + ‖(P ^ k) g‖ ^ 2 := hpy
      _ = ‖a • hermiteLpNorm 0‖ ^ 2 + ‖(P ^ k) g‖ ^ 2 := by rw [hfix]
      _ ≤ ‖a • hermiteLpNorm 0‖ ^ 2 + ‖g‖ ^ 2 := by linarith
      _ = ‖f‖ ^ 2 := hgdec.symm
  have habs : |‖(P ^ k) f‖| ≤ |‖f‖| := sq_le_sq.1 hsq
  simpa using habs


theorem opNorm_gaussianPCNOp_pow_le (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) (k : ℕ) :
    ‖(gaussianPCNOp ρ s hρs hs) ^ k‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun f => ?_
  simpa using norm_gaussianPCNOp_pow_le ρ s hρs hs k f

theorem summable_resolvent_series (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) {lam : ℂ}
    (hlam : 1 < ‖lam‖) :
    Summable (fun n : ℕ => (lam ^ (n + 1))⁻¹ • (gaussianPCNOp ρ s hρs hs) ^ n) := by
  have h0 : (0 : ℝ) ≤ ‖lam‖⁻¹ := by positivity
  have h1 : ‖lam‖⁻¹ < 1 := by
    rw [inv_lt_one_iff₀]
    exact Or.inr hlam
  have hgeom : Summable (fun n : ℕ => (‖lam‖ ^ (n + 1))⁻¹) := by
    have h := (summable_geometric_of_lt_one h0 h1).mul_left ‖lam‖⁻¹
    simpa [inv_pow, pow_succ] using h
  refine Summable.of_norm_bounded (f := fun n : ℕ =>
    (lam ^ (n + 1))⁻¹ • (gaussianPCNOp ρ s hρs hs) ^ n) hgeom fun n => ?_
  rw [norm_smul, norm_inv, norm_pow]
  have h2 : ‖(gaussianPCNOp ρ s hρs hs) ^ n‖ ≤ 1 :=
    opNorm_gaussianPCNOp_pow_le ρ s hρs hs n
  calc (‖lam‖ ^ (n + 1))⁻¹ * ‖(gaussianPCNOp ρ s hρs hs) ^ n‖
      ≤ (‖lam‖ ^ (n + 1))⁻¹ * 1 := by
        refine mul_le_mul_of_nonneg_left h2 (by positivity)
    _ = (‖lam‖ ^ (n + 1))⁻¹ := by rw [mul_one]


private abbrev H := Lp ℂ 2 (gaussianReal 0 1) →L[ℂ] Lp ℂ 2 (gaussianReal 0 1)

theorem hasSum_resolvent_series (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) {lam : ℂ}
    (hlam : 1 < ‖lam‖) :
    ∃ R : H,
      (∀ g : Lp ℂ 2 (gaussianReal 0 1),
        ((lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
          - gaussianPCNOp ρ s hρs hs)) (R g) = g) ∧
      (∀ f : Lp ℂ 2 (gaussianReal 0 1),
        R (((lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
          - gaussianPCNOp ρ s hρs hs)) f) = f) ∧
      HasSum (fun n : ℕ => (lam ^ (n + 1))⁻¹ •
        (gaussianPCNOp ρ s hρs hs) ^ n) R := by
  set P := gaussianPCNOp ρ s hρs hs with hP
  set A : H := lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1)) - P with hAdef
  set T : ℕ → H := fun n => (lam ^ (n + 1))⁻¹ • P ^ n with hT
  set u : ℕ → H := fun n => (lam ^ n)⁻¹ • P ^ n with hu
  have hlam0 : lam ≠ 0 := by
    intro h; rw [h, norm_zero] at hlam; linarith
  have hS : Summable T := summable_resolvent_series ρ s hρs hs hlam
  set S : H := ∑' n, T n with hSdef
  have hcoef : ∀ n : ℕ, (lam ^ (n + 1))⁻¹ * lam = (lam ^ n)⁻¹ := by
    intro n
    rw [pow_succ, mul_inv]
    field_simp
  have hpowL : ∀ n : ℕ, A * P ^ n = lam • P ^ n - P ^ (n + 1) := by
    intro n
    rw [hAdef, sub_mul, smul_mul_assoc, ← pow_succ']
    congr 1
  have hpowR : ∀ n : ℕ, P ^ n * A = lam • P ^ n - P ^ (n + 1) := by
    intro n
    rw [hAdef, mul_sub, mul_smul_comm, ← pow_succ]
    congr 1
  have htermL : ∀ n : ℕ, A * T n = u n - u (n + 1) := by
    intro n
    have h1 : A * T n = (lam ^ (n + 1))⁻¹ • (A * P ^ n) := by
      rw [hT, mul_smul_comm]
    rw [h1, hpowL, smul_sub, smul_smul, hcoef, hu]
  have htermR : ∀ n : ℕ, T n * A = u n - u (n + 1) := by
    intro n
    have h1 : T n * A = (lam ^ (n + 1))⁻¹ • (P ^ n * A) := by
      rw [hT, smul_mul_assoc]
    rw [h1, hpowR, smul_sub, smul_smul, hcoef, hu]
  have htelL : ∀ N : ℕ, ∑ n ∈ Finset.range N, A * T n = 1 - (lam ^ N)⁻¹ • P ^ N := by
    intro N
    have hfun : (fun n => A * T n) = fun n => u n - u (n + 1) := funext htermL
    rw [hfun, Finset.sum_range_sub']
    simp [hu]
  have htelR : ∀ N : ℕ, ∑ n ∈ Finset.range N, T n * A = 1 - (lam ^ N)⁻¹ • P ^ N := by
    intro N
    have hfun : (fun n => T n * A) = fun n => u n - u (n + 1) := funext htermR
    rw [hfun, Finset.sum_range_sub']
    simp [hu]
  have hrem : Tendsto (fun N : ℕ => (lam ^ N)⁻¹ • P ^ N) atTop (𝓝 0) := by
    have hgeom : Tendsto (fun N : ℕ => (‖lam‖⁻¹) ^ N) atTop (𝓝 0) := by
      refine tendsto_pow_atTop_nhds_zero_of_lt_one (by positivity) ?_
      rw [inv_lt_one_iff₀]
      exact Or.inr hlam
    refine squeeze_zero_norm (fun N => ?_) hgeom
    rw [norm_smul, norm_inv, norm_pow, ← inv_pow]
    exact mul_le_of_le_one_right (by positivity)
      (opNorm_gaussianPCNOp_pow_le ρ s hρs hs N)
  have hlimL : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, A * T n) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : H)) (f := atTop)).sub hrem
    simpa [htelL] using h
  have hlimR : Tendsto (fun N : ℕ => ∑ n ∈ Finset.range N, T n * A) atTop (𝓝 1) := by
    have h := (tendsto_const_nhds (x := (1 : H)) (f := atTop)).sub hrem
    simpa [htelR] using h
  have hSumL : HasSum (fun n => A * T n) (A * S) := by
    have h := hS.hasSum.mul_left A
    rwa [← hSdef] at h
  have hSumR : HasSum (fun n => T n * A) (S * A) := by
    have h := hS.hasSum.mul_right A
    rwa [← hSdef] at h
  have hleft : A * S = 1 := tendsto_nhds_unique hSumL.tendsto_sum_nat hlimL
  have hright : S * A = 1 := tendsto_nhds_unique hSumR.tendsto_sum_nat hlimR
  refine ⟨S, ?_, ?_, ?_⟩
  · intro g
    have := congrArg (fun X : H => X g) hleft
    simpa using this
  · intro f
    have := congrArg (fun X : H => X f) hright
    simpa using this
  · have h := hS.hasSum
    rw [← hSdef] at h
    simpa [hT] using h

/-- **The spectrum of `P` lies in the closed unit disc**, so every `lam` with `1 < ‖lam‖` is off the
spectrum — the region where the Neumann series of `hasSum_resolvent_series` is available. -/
theorem notMem_closure_of_one_lt_norm (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    {lam : ℂ} (hlam : 1 < ‖lam‖) :
    lam ∉ closure (Set.range fun n : ℕ => (ρ : ℂ) ^ n) := by
  intro hmem
  have hsub : closure (Set.range fun n : ℕ => (ρ : ℂ) ^ n) ⊆ {x : ℂ | ‖x‖ ≤ 1} := by
    refine closure_minimal ?_ (isClosed_le continuous_norm continuous_const)
    rintro x ⟨n, rfl⟩
    simpa [norm_pow] using
      pow_le_one₀ (abs_nonneg ρ) (abs_rho_lt_one hρs hs).le (n := n)
  have h1 : ‖lam‖ ≤ 1 := hsub hmem
  linarith

/-- **The norm of the Neumann series is the reciprocal distance to the eigenvalue list**: the series
sum of `hasSum_resolvent_series` is a two-sided inverse of `lam • 1 - P`, so by §22's norm identity
its norm is `(infDist lam {ρⁿ})⁻¹`. -/
theorem norm_tsum_resolvent_series (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) {lam : ℂ}
    (hlam : 1 < ‖lam‖) :
    ‖∑' n : ℕ, (lam ^ (n + 1))⁻¹ • (gaussianPCNOp ρ s hρs hs) ^ n‖
      = (Metric.infDist lam (Set.range fun n : ℕ => (ρ : ℂ) ^ n))⁻¹ := by
  set P := gaussianPCNOp ρ s hρs hs with hP
  obtain ⟨R, hRl, hRr, hRs⟩ := hasSum_resolvent_series ρ s hρs hs hlam
  have hmem := notMem_closure_of_one_lt_norm ρ s hρs hs hlam
  obtain ⟨R', hR'l, hR'r, hR'n⟩ := exists_resolvent_norm_eq ρ s hρs hs hmem
  have hA : ∀ (X : H), X * ((lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1)) - P)) = 1 →
      ∀ (Y : H), ((lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1)) - P)) * Y = 1 →
      X = Y := by
    intro X hX Y hY
    calc X = X * 1 := (mul_one X).symm
      _ = X * (((lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1)) - P)) * Y) := by
          rw [hY]
      _ = (X * ((lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1)) - P))) * Y :=
          (mul_assoc _ _ _).symm
      _ = 1 * Y := by rw [hX]
      _ = Y := one_mul Y
  have hRe : R = R' :=
    hA R (ContinuousLinearMap.ext hRr) R' (ContinuousLinearMap.ext hR'l)
  have hsum : (∑' n : ℕ, (lam ^ (n + 1))⁻¹ • (gaussianPCNOp ρ s hρs hs) ^ n) = R' := by
    rw [← hRe]
    exact hRs.tsum_eq
  rw [hsum, hR'n]


/-! ## 25. What compactness does and does not give: the Riesz-theoretic input

The literature story is: `P` is compact and self-adjoint, so (Riesz/Fredholm) its spectrum is
`{0} ∪ {eigenvalues}`, the nonzero eigenvalues are isolated with finite multiplicity, and they
accumulate only at `0`.  §§19–21 obtain exactly this *shape* for `P`, but from the diagonal
representation rather than from compactness.

Two points belong in the record.

* The hypothesis `|ρ| < 1` used from §5 on is **not** a consequence of compactness.  A compact
  self-adjoint operator can have the eigenvalue `1` (a rank-one projection does), so compactness
  alone permits `|ρ| = 1`.  Here `|ρ| < 1` instead follows from the proposal being non-degenerate:
  `ρ² + s² = 1` with `s ≠ 0` gives `|ρ| < 1` (`abs_rho_lt_one`).
* What *does* follow from the contraction bound `‖Pᵏ‖ ≤ 1` is boundedness of the spectrum: the
  closure of the eigenvalue list lies in the closed unit disc
  (`closure_range_pow_subset_closedUnitBall`), so every `λ` with `1 < ‖λ‖` lies in the resolvent
  set, with the Neumann series of §24 as its resolvent (`resolvent_series_of_one_lt_norm`).

The general Riesz/Fredholm theorem for compact operators on a Banach space — finite multiplicity of
each nonzero eigenvalue, `0` the only possible accumulation point, spectral projections — is
**not** formalized here, and is not needed: §§19–21 reach the same conclusions from the explicit
eigenvalue list.
-/


/-- **The closure of the eigenvalue list lies in the closed unit disc.**  This is the
Riesz-theoretic bound "the spectrum is contained in the closed disc of radius `‖P‖`", here read off
from `|ρ| < 1`: every eigenvalue `ρⁿ` has modulus at most `1`, and the closed unit disc is
closed. -/
theorem closure_range_pow_subset_closedUnitBall (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0) :
    closure (Set.range fun n : ℕ => (ρ : ℂ) ^ n) ⊆ {x : ℂ | ‖x‖ ≤ 1} := by
  refine closure_minimal ?_ (isClosed_le continuous_norm continuous_const)
  rintro x ⟨n, rfl⟩
  simpa [norm_pow] using pow_le_one₀ (abs_nonneg ρ) (abs_rho_lt_one hρs hs).le (n := n)

/-- **Every point off the closed unit disc is in the resolvent set of `P`**, with the Neumann series
of §24 as its resolvent.  This is the direction of Riesz/Fredholm theory that the diagonal
representation makes elementary: the spectrum is *bounded* by the contraction bound. -/
theorem resolvent_series_of_one_lt_norm (ρ s : ℝ) (hρs : ρ ^ 2 + s ^ 2 = 1) (hs : s ≠ 0)
    {lam : ℂ} (hlam : 1 < ‖lam‖) :
    ∃ R : Lp ℂ 2 (gaussianReal 0 1) →L[ℂ] Lp ℂ 2 (gaussianReal 0 1),
      (∀ g : Lp ℂ 2 (gaussianReal 0 1),
        ((lam • ContinuousLinearMap.id ℂ (Lp ℂ 2 (gaussianReal 0 1))
          - gaussianPCNOp ρ s hρs hs)) (R g) = g) ∧
      HasSum (fun n : ℕ => (lam ^ (n + 1))⁻¹ •
        (gaussianPCNOp ρ s hρs hs) ^ n) R := by
  obtain ⟨R, hl, _, hs'⟩ := hasSum_resolvent_series ρ s hρs hs hlam
  exact ⟨R, hl, hs'⟩

end BookProof.MCMC
