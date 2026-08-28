import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Reliability of the Shift-Invert Rational Krylov Scheme" =>
%%%
tag := "sirk-reliability"
%%%

# What the Numerics Compute

:::paragraph
For QYM, QED, QG, and NS, the Hamiltonian presented to the full nested-Fock
numerics is always the outer enclosure of the sector's inner one-particle
Hamiltonian: `H = Σᵢⱼ hᵢⱼ C†(eᵢ) A(eⱼ)`. Creation is on the left and outer
annihilation on the right. Inner pair terms remain in `h`; only an allowed
scalar shift of `h` may be made for positivity. Therefore the full Hamiltonian
annihilates the outer vacuum exactly.
:::

:::paragraph
This chapter keeps the three operator levels distinct: the one-particle Hamiltonian, its
finite Krylov/Galerkin truncations, and the nested Fock lift. The current certificate
formalizes the finite/truncated level. The new proof layer now supplies a conditional version of that target. `ChapterRitzCertificate.lean` derives finite Temple bands; `ChapterBandEnclosure.lean` and `ChapterSpectralGapStability.lean` describe enclosure and limit stability; `ChapterFockOneParticleGap.lean` identifies the one-particle edge; and `ChapterFockNumberPreservingGap.lean` lifts it through the free, number-preserving `dGamma` Hamiltonian. The concrete QYM instantiation and its analytic convergence hypotheses remain specialist work. The same distinction applies to QED, QG, and NS: the final full-theory operator is always the outer creation-left/annihilation-right enclosure of the sector's inner one-particle Hamiltonian.
:::

:::paragraph
The solver evolves a state by projecting the generator onto a Krylov subspace,
exponentiating the resulting $`m \times m` matrix, and lifting the answer back.
Written out, the approximation is
$`V_m \, \psi(B_m) \, V_m^{*} v`$, where $`V_m`$ is an isometric embedding of the
retained subspace, $`B_m = V_m^{*} X V_m`$ is the compression of the shift-invert
resolvent $`X`$, and $`\psi`$ is the function whose calculus at $`X`$ reproduces
the propagator. The reliability question is how far that is from the exact
$`\varphi_k(A) v`$.
:::

:::paragraph
The ingredients were proved separately: the $`\varphi`$-function calculus, the
compression transfer, the rational-transfer identity, and the exponential decay
of the error bound in the reduction order. What was missing was a theorem that
*composes* them. `BookProof/ChapterSirkEndToEnd.lean` is that composition.
:::

# New Proof Layer: What a Ritz Certificate Can and Cannot Say

:::paragraph
`ChapterRitzCertificate.lean` proves the finite statement used by the numerical pipeline: a normalized trial vector has a computable Rayleigh quotient and residual, and—provided the next spectral region is separated—Temple's inequality places the relevant eigenvalue in a certified interval. `ChapterTempleSeparationNecessary.lean` supplies the essential warning: without separation, even perfect Rayleigh data can coexist with an arbitrarily lower unseen eigenvalue. Thus the separation condition is a real certificate input, not a cosmetic technicality.
:::

:::paragraph
For the physical lift, `ChapterFockNumberPreservingGap.lean` proves that a positive one-particle gap produces the corresponding free Fock gap on vacuum-orthogonal finite-particle states. `ChapterFockInteractionStability.lean` replaces exact number preservation by a quantitative bounded/form-bounded interaction estimate, while `ChapterFockFieldPerturbation.lean` develops the field-form estimates needed to instantiate that result. These theorems deliberately stop short of claiming the unbounded interacting QYM case.
:::

# Why the Transfer Identity Has To Be Pointwise

:::paragraph
The rational transfer $`r(X) v = V_m \, r(B_m) \, V_m^{*} v`$ is not an operator
identity: it holds only for states already inside the retained subspace. The
Krylov seed is such a state, and the triangle-inequality core only ever uses the
identity at the seed. Weakening the hypothesis accordingly is what allows the
transfer to be *discharged* rather than assumed, so the assembled statement
carries no transfer hypothesis at all.
:::

```
#check @BookProof.ChapterSirkEndToEnd.sirk_error_bound_at
#check @BookProof.ChapterSirkEndToEnd.sirk_end_to_end
#check @BookProof.ChapterSirkEndToEnd.sirk_end_to_end_satisfiable
```

# One Crouzeix Domain For Both Bounds

:::paragraph
The two operator-norm estimates that remain — for the full operator and for its
compression — are usually quoted with the same constant and the same sup-norm.
That is legitimate because the numerical range of a compression is contained in
the numerical range of the operator, so any *convex* region containing the latter
also contains the convex hull of the former.
:::

```
#check @BookProof.ChapterSirkEndToEnd.crouzeix_domain_transfer
#check @BookProof.ChapterSirkEndToEnd.crouzeix_domain_uniform
```

# Convergence, and Uniformity in Time

:::paragraph
With the constants fixed, the bound decays exponentially in the reduction order,
so the reduced flows converge to the exact one. If the constants can be chosen
independently of the time, the same estimate gives convergence uniform over the
whole time axis.
:::

```
#check @BookProof.ChapterSirkEndToEnd.sirk_flow_error_tendsto_zero
#check @BookProof.ChapterSirkEndToEnd.sirk_flow_error_uniform_in_time
```

# The Specifics of the Implementation

:::paragraph
Three features of the actual solver are covered separately. *Restarting*: over
$`n` cycles the error of two contractive propagators that differ by $`\varepsilon`
grows at most like $`n\varepsilon`, so restarting multiplies the per-cycle
guarantee by the cycle count and nothing worse. *Whitening*: the reduced operator
depends only on the retained subspace — two orthonormalizations of the same raw
Krylov vectors give unitarily conjugate reduced operators and literally the same
reconstructed operator on the ambient space. *Shift schedules*: the forward
sequence built from an arbitrary schedule of shifts spans exactly the standard
Krylov subspace, so the shifts change the basis but never the space.
:::

```
#check @BookProof.ChapterSirkRestart.restart_error_accumulation
#check @BookProof.ChapterSirkRestart.restart_error_accumulation_sirk
#check @BookProof.ChapterSirkWhitening.compress_conj_whitening
#check @BookProof.ChapterSirkWhitening.sirkApprox_eq_of_range_eq
#check @BookProof.ChapterSirkMultiShift.krylov_multiShift_eq_standard
#check @BookProof.ChapterSirkMultiShift.krylov_multiShift_span_eq_of_shifts
```

:::paragraph
The same freedom holds on the *rational* side of the scheme, and there it is a
statement about the resolvents rather than about the shifted operators. Writing
$`X_i` for a two-sided inverse of $`H - z_i`, the rational Krylov space
$`\mathrm{span}\{v, X_0v, X_1X_0v, \dots, X_{k-1}\cdots X_0v\}` that the solver
actually assembles is exactly the image of the ordinary Krylov space
$`\mathrm{span}\{v, Hv, \dots, H^kv\}` under the single invertible factor
$`X_{k-1}\cdots X_0`. Nothing analytic enters: the identity holds for an arbitrary
module over a commutative ring and an arbitrary schedule of shifts, the proof being
that the tail products $`(H - z_{k-1})\cdots(H - z_j)` are the forward products of
the reversed schedule and so span the Krylov space as well.  Because the resolvents
commute, their product does not see the order of the schedule either, so reordering the
shifts changes the intermediate flag the algorithm passes through but not the subspace
it arrives at.
:::

```
#check @BookProof.KrylovShiftSpan.forwardSpan_eq_krylovSpan
#check @BookProof.KrylovShiftSpan.forwardSpan_eq_forwardSpan
#check @BookProof.KrylovShiftSpan.tailSpan_eq_krylovSpan
#check @BookProof.KrylovShiftSpan.resolventSpan_eq_map_krylovSpan
#check @BookProof.KrylovShiftSpan.krylovSpan_eq_map_resolventSpan
#check @BookProof.KrylovShiftSpan.resolventSpan_of_perm
```

:::paragraph
Whitening was described above as a hypothesis: hand the reduction an isometric
embedding of the retained subspace and the answer does not depend on which one.
The solver, however, does not receive such an embedding — it builds one, from the
Gram matrix $`G_{ij} = \langle w_i, w_j\rangle` of the raw Krylov vectors, by
whitening with a factor $`T` satisfying $`T^*GT = 1`. That step is now covered as
well. The synthesis map $`c \mapsto \sum_i c_i w_i` has the retained subspace as
its range and $`G` as $`(\text{synthesis})^*(\text{synthesis})`; any $`T` with
$`T^*GT = 1` therefore turns it into an isometric embedding, whose range is the
retained subspace as soon as $`T` is onto. And such a $`T` exists whenever the raw
vectors are independent, so the hypotheses of the whitening-independence theorems
are never vacuous. When the raw vectors are dependent, an orthonormalization still
exists, indexed by the rank rather than by the vectors — the exact, lossless form
of the rank truncation the code performs on a degenerate Gram matrix.
:::

```
#check @BookProof.ChapterSirkGramWhitening.range_synthesis
#check @BookProof.ChapterSirkGramWhitening.gramOp_apply
#check @BookProof.ChapterSirkGramWhitening.whitened_adjoint_comp_self
#check @BookProof.ChapterSirkGramWhitening.range_whitened
#check @BookProof.ChapterSirkGramWhitening.exists_isWhitening
#check @BookProof.ChapterSirkGramWhitening.exists_isometry_range_eq_span
#check @BookProof.ChapterSirkGramWhitening.isWhitening_of_matrix
#check @BookProof.ChapterSirkGramWhitening.sirkApprox_gram_whitening_eq
```

:::paragraph
Truncating the rank is then a matter of how far the discarded directions really
were from the retained subspace. If every raw vector sits within $`\delta` of it,
a state assembled with coefficients $`c` loses at most $`\delta\sqrt{m}\lVert c
\rVert`, and that is exactly the additive term the end-to-end bound pays for a
rank-truncated reduction — the exponential term in the reduction order is
untouched, and $`\delta = 0` returns the lossless case.
:::

```
#check @BookProof.ChapterSirkGramWhitening.norm_defect_synthesis_le
#check @BookProof.ChapterSirkGramWhitening.sirk_end_to_end_truncated_gram
```

:::paragraph
That leaves the question of where $`\delta` comes from, since it is not what the
code measures: the code diagonalizes the Gram matrix and discards the eigenpairs
whose eigenvalue falls below a tolerance. The two are related by a single
estimate. The synthesized eigenvectors $`W u_k` are orthogonal with squared norms
the eigenvalues $`\lambda_k`, so expanding a state along the eigenbasis and
dropping the discarded directions costs $`\bigl(\sum_{k\ \text{discarded}}
|c_k|^2\lambda_k\bigr)^{1/2} \le \sqrt{\mathrm{tol}}\,\lVert c\rVert`. Since the
projection $`VV^*x` is the closest point of the retained subspace to $`x`, every
raw Krylov vector is within $`\sqrt{\mathrm{tol}}` of it: the geometric parameter
obeys $`\delta \le \sqrt{\mathrm{tol}}`, and the end-to-end bound can be stated
in the numerical cutoff alone. The eigendecomposition it assumes always exists —
the Gram operator is self-adjoint — and the embedding the solver builds from the
retained eigenpairs, $`V = WU_R\Lambda_R^{-1/2}`, is an isometric embedding of
the retained subspace, so the estimate applies to the object the code produces
rather than to an abstract substitute.
:::

```
#check @BookProof.ChapterSirkGramCutoff.exists_gramEigen
#check @BookProof.ChapterSirkGramCutoff.norm_sub_proj_le_of_mem_range
#check @BookProof.ChapterSirkGramCutoff.dist_synthesis_retained_le
#check @BookProof.ChapterSirkGramCutoff.defect_le_sqrt_cutoff
#check @BookProof.ChapterSirkGramCutoff.sirk_end_to_end_truncated_cutoff
#check @BookProof.ChapterSirkGramCutoff.retainedEmbedding_isometry
#check @BookProof.ChapterSirkGramCutoff.defect_le_sqrt_cutoff_retained
```

# Leakage Out of the Physical Subspace

:::paragraph
The truncated dynamics do not preserve the physical subspace picked out by the
BRST charge, which is why the solver carries a projector along. The telescoping
estimate bounds the damage: the exact flow keeps a physical state physical, so
all of the leakage comes from the truncation, and after $`n` cycles it is at most
$`\lVert \Omega \rVert \, n \varepsilon \lVert v \rVert`.
:::

```
#check @BookProof.ChapterSirkRestart.brst_leakage_zero_of_exact
#check @BookProof.ChapterSirkRestart.brst_leakage_bound
```

:::paragraph
That estimate takes the per-cycle distance between the exact and the truncated
propagator as given. One level down, at the generators the algorithm truncates, the
distance is not an assumption but a consequence, and the leakage rate becomes an
explicit block of the Hamiltonian. For a bounded self-adjoint generator the flow
$`e^{-itH}` is unitary and commutes with the charge, so the exact dynamics keeps the
charge content of a state constant. Comparing the exact flow with the truncated one
along the path $`s \mapsto e^{-i(t-s)H} e^{-isB} v` gives a derivative equal to
$`e^{-i(t-s)H} \bigl(i(H - B)\bigr) e^{-isB} v`, whose norm — both groups being unitary —
is just $`\lVert (H-B) e^{-isB} v \rVert`. Integrating is the whole estimate.
:::

:::paragraph
What makes the constant sharp rather than crude is that the truncated flow keeps a
retained state inside the retained subspace, so the defect $`H - PHP` is only ever
applied to states in the range of $`P`, where it equals the discarded off-diagonal
block $`(1-P)HP`. The leakage of a physical, retained state after time $`t` is
therefore at most $`\lVert \Omega \rVert \, \lVert (1-P)HP \rVert \, \lVert v \rVert \, t`:
it is controlled by exactly the part of the Hamiltonian the truncation throws away, and
vanishes with it. Restarting with a fresh truncation each cycle accumulates the bound
linearly in the number of cycles.
:::

```
#check @BookProof.BrstLeakage.norm_omega_flow_eq
#check @BookProof.BrstLeakage.hasDerivAt_duhamel
#check @BookProof.BrstLeakage.norm_flow_sub_flow_apply_le
#check @BookProof.BrstLeakage.leakage_le
#check @BookProof.BrstLeakage.flow_truncGen_mem
#check @BookProof.BrstLeakage.truncation_leakage_le_of_physical
#check @BookProof.BrstLeakage.leakage_iterate_le
#check @BookProof.BrstLeakage.brst_leakage_bound_of_generator
```

:::paragraph
The field-theoretic Hamiltonian is not bounded, and the estimate does not need it to
be. Let $`T` be an unbounded self-adjoint operator with the unitary group $`e^{-itT}`
that Stone's theorem produces, and let the retained subspace be finite-dimensional and
inside the domain of $`T` — the finite-$`m` situation of the algorithm. Then the
compression $`PTP` is a bounded self-adjoint operator, its flow keeps a retained state
retained, and the same comparison path can be differentiated: the group is only
strongly continuous, so the product rule is replaced by the observation that an
isometric, strongly continuous family applied to a curve vanishing at the base point is
differentiable with the expected derivative. What comes out is the same pair of bounds
with the same constant: the flow error
$`\lVert e^{-itPTP} v - e^{-itT} v \rVert \le \lVert (1-P)TP \rVert \lVert v \rVert t`
and the leakage
$`\lVert \Omega e^{-itPTP} v \rVert \le \lVert \Omega v \rVert + \lVert \Omega \rVert
\lVert (1-P)TP \rVert \lVert v \rVert t`, for an observable commuting with the exact
group. Unboundedness of the Hamiltonian costs nothing; what is used is that the
discarded block acts on the retained subspace alone. Restarting with a fresh retained
subspace each cycle again accumulates the bound linearly in the number of cycles.
:::

```
#check @BookProof.BrstUnboundedLeakage.hasDerivAt_isometry_apply
#check @BookProof.BrstUnboundedLeakage.hasDerivAt_duhamel_stone
#check @BookProof.BrstUnboundedLeakage.norm_flow_sub_stoneU_le
#check @BookProof.BrstUnboundedLeakage.truncGen_isSelfAdjoint
#check @BookProof.BrstUnboundedLeakage.flow_truncGen_mem
#check @BookProof.BrstUnboundedLeakage.norm_flow_truncGen_sub_stoneU_le
#check @BookProof.BrstUnboundedLeakage.truncation_leakage_le
#check @BookProof.BrstUnboundedLeakage.truncation_leakage_le_of_physical
#check @BookProof.BrstUnboundedLeakage.restart_leakage_le
```

# Which Region the Constants Are Measured On

:::paragraph
The constants are only as meaningful as the region on which the deformation is
measured, and that region is decided by the operator the algorithm actually
iterates: not the Hamiltonian, which is unbounded, but its shift-invert. Two
regimes cover every system in this development. If the generator is positive and
the shift is a positive real $`\gamma`, the shift-invert is self-adjoint with
norm at most $`\gamma^{-1}` and nonnegative Rayleigh quotients, so its numerical
range collapses onto the segment $`[0, \gamma^{-1}]` of the real axis. If the
generator is indefinite, the algorithm runs at a shift off the real axis, and the
numerical range sits in the disc of radius $`|\operatorname{Im}\gamma|^{-1}`.
Either way the region depends on the shift alone — not on the reduction order,
not on the seed — and is inherited by every compression.
:::

```
#check @BookProof.ChapterSirkSpectralGeometry.numRange_subset_realSegment_of_shiftInvert
#check @BookProof.ChapterSirkSpectralGeometry.numRange_subset_closedBall_of_shiftInvertC
#check @BookProof.ChapterSirkSpectralGeometry.crouzeix_domain_shiftInvert
#check @BookProof.ChapterSirkSpectralGeometry.crouzeix_domain_shiftInvertC
#check @BookProof.ChapterSirkSpectralGeometry.sirk_end_to_end_crouzeix_domain
```

# The Four Systems

:::paragraph
Each physical Hamiltonian falls into one of the two regimes. Yang–Mills is a sum
of squares, so the Friedrichs route applies and the region is a segment.
Navier–Stokes in Eulerian variables is indefinite in both its sequence-space and
its differential realization, and so is the Lagrangian generator once the drift
is included; all three take the disc. So does the gauge-fixed $`R + \alpha R^2`
gravity Hamiltonian, whose fiber symbol is two-signed — and whose resolvent had
to be constructed first, from the extension that essential self-adjointness
selects, since no positivity is available to supply one.
:::

```
#check @BookProof.ChapterSirkPerSystem.ym_sirk_crouzeix_domain
#check @BookProof.ChapterSirkPerSystem.ns_sirk_crouzeix_domain
#check @BookProof.ChapterSirkPerSystem.nsDiff_sirk_crouzeix_domain
#check @BookProof.ChapterSirkPerSystem.lagrangian_sirk_crouzeix_domain
#check @BookProof.ChapterSirkPerSystem.diagKR_sirk_crouzeix_domain
#check @BookProof.ChapterSirkPerSystem.qgR2_shiftInvert_selects
#check @BookProof.ChapterSirkPerSystem.qgR2_sirk_crouzeix_domain
```

# One Named Bound Per System

:::paragraph
Fixing the region is not yet a reliability statement about a particular
Hamiltonian: the assembly and the geometry still have to be composed. Doing so
gives one named theorem per system, in which the selected extension, its
shift-invert, the region on which the constants are measured, the Krylov transfer
identity and the reconstruction projection are all discharged from results the
development already proves. What is left as an input is exactly what should be:
the two deformation estimates on the fixed region, and the spectral consistency
that identifies the propagator with the calculus of the shift-invert. The
reduction data of a single order $`m` — the rational approximant, its
denominators and the reduced propagator — are bundled, which also lets a whole
family over $`m` be quantified at once; the family form is what gives the
convergence of the reduced flows as the retained subspace grows. Two small
observations remove clutter along the way: an isometric embedding automatically
satisfies $`V^{*}V = 1` and has a contractive adjoint, so neither needs to be
assumed.
:::

```
#check @BookProof.ChapterSirkPerSystemFlowBound.adjoint_comp_self_of_isometry
#check @BookProof.ChapterSirkPerSystemFlowBound.norm_adjoint_apply_le_of_isometry
#check @BookProof.ChapterSirkPerSystemFlowBound.sirk_scheme_bound
#check @BookProof.ChapterSirkPerSystemFlowBound.sirk_scheme_tendsto
#check @BookProof.ChapterSirkPerSystemFlowBound.ym_sirk_flow_error_bound
#check @BookProof.ChapterSirkPerSystemFlowBound.ym_sirk_flow_error_tendsto_zero
#check @BookProof.ChapterSirkPerSystemFlowBound.ns_sirk_flow_error_bound
#check @BookProof.ChapterSirkPerSystemFlowBound.nsDiff_sirk_flow_error_bound
#check @BookProof.ChapterSirkPerSystemFlowBound.lagrangian_sirk_flow_error_bound
#check @BookProof.ChapterSirkPerSystemFlowBound.diagKR_sirk_flow_error_bound
#check @BookProof.ChapterSirkPerSystemFlowBound.qgR2_sirk_flow_error_bound
#check @BookProof.ChapterSirkPerSystemFlowBound.qgR2_sirk_flow_error_tendsto_zero
```

# From the Reduced Generator to the Flow

:::paragraph
Everything above compares the algorithm with a *fixed* generator. The other half
of reliability is the passage to the limit: the reduced generators approximate
the selected extension, and one wants the propagators they generate to
approximate its flow. For bounded generators this is elementary and quantitative
— the exponential is Lipschitz on balls of a Banach algebra, so two propagators
differ by at most $`|t| \, \|a - b\| \, e^{|t| M}` on the ball of radius $`M`,
uniformly on every bounded time interval.
:::

```
#check @BookProof.ChapterSirkGroupTransfer.norm_exp_sub_exp_le
#check @BookProof.ChapterSirkGroupTransfer.norm_groupFlow_sub_le
#check @BookProof.ChapterSirkGroupTransfer.groupFlow_transfer_uniform_on_interval
```

:::paragraph
For the unbounded selected extension there is no such rate, and the transfer is
the Trotter–Kato theorem: strong convergence of the resolvents
$`(A_n - i)^{-1} \to (A - i)^{-1}` forces $`e^{-itA_n} v \to e^{-itA} v`,
uniformly for $`t` in a bounded interval. The proof is a Duhamel argument. The
curve $`r \mapsto e^{-i(t-r)A_n} (A_n - i)^{-1} e^{-irA} \chi` has to be
differentiated even though the flow is only strongly continuous — so no operator
product rule is available and the derivative is taken from the definition — and
its derivative is computed by the algebraic identity
$`A_n R_n - R_n A = (R - R_n)(A - i)` on the domain. The mean value inequality
then bounds the difference of the flows by the resolvent difference along an
orbit, which is a compact set, so pointwise convergence of the resolvents is
automatically uniform there.
:::

```
#check @BookProof.ChapterSirkTrotterKato.hasDerivAt_stoneU_const_sub_apply
#check @BookProof.ChapterSirkTrotterKato.resolvent_commutator_eq
#check @BookProof.ChapterSirkTrotterKato.hasDerivAt_duhamel
#check @BookProof.ChapterSirkTrotterKato.norm_res_stoneU_sub_stoneU_res_le
#check @BookProof.ChapterSirkTrotterKato.trotterKato_uniform_on_interval
#check @BookProof.ChapterSirkTrotterKato.trotterKato_tendsto
#check @BookProof.ChapterSirkTrotterKato.trotterKato_tendstoUniformlyOn
```

:::paragraph
The hypothesis is exactly what the Rayleigh–Ritz analysis supplies. In the regime
where the generator is bounded on its domain — the regime in which the Galerkin
limit is identified with the selected extension — the compressions converge
strongly, hence so do their resolvents, hence the flows they generate converge to
the flow of the selected generator, uniformly on bounded time intervals. That is
the last link of the chain: what the algorithm propagates converges to what the
selected extension propagates.
:::

```
#check @BookProof.ChapterSirkTrotterKato.strongResolventConvergence_ofBounded
#check @BookProof.ChapterSirkTrotterKato.flow_transfer_of_strong_tendsto
#check @BookProof.ChapterSirkTrotterKato.galerkin_flow_transfer
#check @BookProof.ChapterSirkTrotterKato.galerkin_flow_tendsto
```

# The Two Remaining Lagrangian Realizations

:::paragraph
The list of systems above stops at the Kato–Rellich instance of the Lagrangian
generator, whose constituents commute. Two further realizations of the same
Lagrangian data had essential self-adjointness but no shift-invert companion: the
canonical realization, in which the parcel momenta and the viscous gradients
are genuinely non-commuting canonical pairs of the trajectory-space Hermite basis,
and the Fock/momentum realization, in which the constituents are
multiplication operators by arbitrary measurable symbols, so the spectrum is in
general purely continuous and there is no eigenvector to work with at all. Since
both are essentially self-adjoint on their core, the abstract Lagrangian selection
theory applies verbatim: the multi-shift data determine one self-adjoint operator,
the single-shift resolvent obeys the bound $`\lVert X \rVert \le |\operatorname{Im} \gamma|^{-1}`, and the
Crouzeix region is the disc of that radius for the generator and for every
order-$`m` compression. The continuum realization also acquires its Stone
flow, so the reliability chain has a flow to compare the algorithm with in every
realization the project defines.
:::

```
#check @BookProof.ChapterSirkLagrangianCanonical.lagCan_hashimoto_selects
#check @BookProof.ChapterSirkLagrangianCanonical.lagCan_sirk_crouzeix_domain
#check @BookProof.ChapterSirkLagrangianCanonical.fockLag_esa
#check @BookProof.ChapterSirkLagrangianCanonical.fockLag_hashimoto_selects
#check @BookProof.ChapterSirkLagrangianCanonical.fockLag_sirk_crouzeix_domain
#check @BookProof.ChapterSirkLagrangianCanonical.fockLag_stone_flow
```

# What the Ritz Values Converge To

:::paragraph
The algorithm reports, at each reduction order, the smallest Rayleigh quotient
available in the retained subspace — the Ritz value the numerics read as a
ground-state energy. That these values decrease to the bottom of the energy form
was already proved; what was missing is that the limit is a *spectral* quantity of
the operator the algorithm selects. It is: for a bounded self-adjoint operator the
bottom of the spectrum coincides with the bottom of the numerical range, because a
shift $`T - c` is a nonnegative element of the algebra exactly when its spectrum is
nonnegative, and exactly when $`c\lVert x\rVert^{2} \le \operatorname{Re}\langle x, Tx\rangle` for every
$`x`. The finite-mode domain is dense and the Rayleigh quotient is continuous, so the
truncations see the whole numerical range, and the Ritz values converge to the bottom
of the spectrum of the selected extension.
:::

```
#check @BookProof.ChapterSirkRitzSpectrum.le_rayleigh_iff_le_spectrum
#check @BookProof.ChapterSirkRitzSpectrum.sInf_spectrum_eq_rayleighInf
#check @BookProof.ChapterSirkRitzSpectrum.ritzInf_finiteModeDomain_eq_rayleighInf
#check @BookProof.ChapterSirkRitzSpectrum.ritzInf_tendsto_sInf_spectrum
#check @BookProof.ChapterSirkRitzSpectrum.galerkin_ritz_tendsto_sInf_spectrum_of_selected
```

# The Laminar Decay Rate

:::paragraph
For the parabolic side of the Lagrangian generator the quantity the numerics measure
is not an energy but a rate: the exponential decay of the state in the laminar
regime. Formally the rate is the coercivity constant of the generator. The semigroup
solves $`u'(t) = -A u(t)`, so the energy $`\lVert u(t)\rVert^{2}` has derivative
$`-2\operatorname{Re}\langle u(t), A u(t)\rangle`, which coercivity bounds by
$`-2\mu \lVert u(t)\rVert^{2}`; weighting by $`e^{2\mu t}` makes the result monotone and
gives $`\lVert e^{-tA} v\rVert \le e^{-\mu t}\lVert v\rVert`. The reduction does not
change the constant: the compression of a coercive generator along an isometry is
coercive with the same $`\mu`, so the reduced propagator obeys the same bound at every
order — the decay the numerics read off the reduced model is not an artefact of the
reduction.
:::

```
#check @BookProof.ChapterSirkDiffusiveDecay.hasDerivAt_heatFlow_apply
#check @BookProof.ChapterSirkDiffusiveDecay.hasDerivAt_heatFlow_normSq
#check @BookProof.ChapterSirkDiffusiveDecay.norm_heatFlow_apply_le
#check @BookProof.ChapterSirkDiffusiveDecay.norm_heatFlow_le
#check @BookProof.ChapterSirkDiffusiveDecay.isCoercive_compress
#check @BookProof.ChapterSirkDiffusiveDecay.norm_heatFlow_compress_apply_le
```

# From Exact Arithmetic To Certified Enclosures

:::paragraph
Everything above is stated in exact arithmetic, while the solver runs in binary64.
The gap is closed not by trusting the floating-point numbers but by proving *around*
them. Three theorems do the work. The residual bound is a-posteriori: for any vector
whatsoever — in particular the computed one — and any real value $`\theta`, some
eigenvalue of the *exact* compression lies within $`\lVert H\psi - \theta\psi\rVert`
of $`\theta`. The backward-error model of a symmetric eigensolver says the computed
eigenpairs are exact eigenpairs of a nearby operator, and Weyl's inequality — in the
enclosure form, which is all a certificate needs — transports its eigenvalues back.
The remaining term is an interval evaluation with outward rounding, whose soundness is
a handful of order facts about endpoints.
:::

```
#check @BookProof.SirkFinitePrecision.exists_eigenvalue_dist_le_residual
#check @BookProof.SirkFinitePrecision.exists_eigenvalue_dist_le_residual_unit
#check @BookProof.SirkFinitePrecision.backward_error_weyl
#check @BookProof.SirkFinitePrecision.backward_error_weyl_symm
#check @BookProof.SirkFinitePrecision.observable_propagation
#check @BookProof.SirkFinitePrecision.observable_propagation_band
#check @BookProof.SirkFinitePrecision.CertInterval.mem_mul
#check @BookProof.SirkFinitePrecision.CertInterval.mem_widen
#check @BookProof.SirkFinitePrecision.CertInterval.dist_le_width
```

# Which Half Of The Bracket Is Free

:::paragraph
The variational principle gives the upper half of the bracket for nothing: a Rayleigh
quotient of a unit vector is never below the lowest eigenvalue. The lower half is not
free, and it is worth being precise about why. A small residual certifies that *some*
eigenvalue is close to the computed value; it does not certify that the *lowest* one
is. Temple's inequality supplies the missing lower bound from the same computed data
plus one separation constant: if every eigenvalue is either the lowest or at least
$`\beta`, and the computed quotient sits below $`\beta`, then the lowest eigenvalue
is at least $`\theta - (\lVert H\psi\rVert^2 - \theta^2)/(\beta - \theta)`.
:::

```
#check @BookProof.SirkFinitePrecision.ground_le_rayleigh
#check @BookProof.SirkFinitePrecision.temple_lower_bound
#check @BookProof.SirkFinitePrecision.ground_ge_of_no_eigenvalue_below
```

# The Certified Gap Of The Truncated Hamiltonian

:::paragraph
The current emitted certificate is expressed through invariant even/odd blocks of the
finite truncated operator. For the nested-Fock interpretation, the physical observable
is instead the lowest positive one-particle energy after a constant shift. The parity
certificate can be used for that observable only after the specialist proves the
one-particle vacuum/first-excitation identification. Until then, `1.932` is a rigorous
truncated value, not a real-Hamiltonian Fock gap.
:::

:::paragraph
For the intended outer-enclosed model, choose `μ > 0` so the shifted one-particle
Hamiltonian satisfies `h₊ ≥ μ I`. Then the full Hamiltonian
`H = Σᵢⱼ (h₊)ᵢⱼ C†ᵢ Aⱼ` has vacuum energy zero because the outer annihilator kills
it, while every non-vacuum finite-particle energy is
a sum of one-particle energies and is at least `μ`. A one-particle creation attains the
lowest edge once the infinite one-particle band limit is proved.
:::

:::paragraph
The same bound can be read against the analytic strong-coupling expectation. Writing
the measured sector Ritz difference as $`g^2/2` plus a correction — the magnetic term
that the strong-coupling expansion excludes — the certified statement becomes
$`\text{gap} \ge g^2/2 + \text{corr} - (\delta^o + \delta^e)`. The correction is carried
explicitly as a parameter rather than absorbed into the widths, so nothing about the
excluded term is quietly assumed.
:::

```
#check @BookProof.SirkCertifiedGap.paritySector_invariant
#check @BookProof.SirkCertifiedGap.sectorRestrict_isSymmetric
#check @BookProof.SirkCertifiedGap.sectorGround_eq_inf_eigenvalues
#check @BookProof.SirkCertifiedGap.sectorGround_ge_temple
#check @BookProof.SirkCertifiedGap.certified_parity_gap
#check @BookProof.SirkCertifiedGap.certified_parity_gap_pos
#check @BookProof.SirkCertifiedGap.certified_parity_gap_strong_coupling
#check @BookProof.SirkCertifiedGap.rayleigh_odd_ge_of_certified
#check @BookProof.SirkCertifiedGap.resolvent_commutes_parity
```

# When A Computation Is A Proof

:::paragraph
The stopping rule is the certificate itself. `ChapterH8` proves that the next SIRK
prediction refines the current approximation and that the generic error bands nest and
shrink. The remaining specialist composition is to show that the corresponding bands
enclose the lowest positive edge of one fixed QYM one-particle Friedrichs operator.
Then a positive limiting edge lifts to the real free nested-Fock Hamiltonian through
`dGamma`; a positive value at only one finite order still certifies only the truncated
operator.
:::

```
#check @BookProof.SirkCertifiedGap.certifiedGap_tendsto
#check @BookProof.SirkCertifiedGap.certifiedGap_eventually_pos
#check @BookProof.SirkCertifiedGap.certifiedGap_sound
#check @BookProof.SirkCertifiedGap.gap_ge_of_certificate
#check @BookProof.SirkCertifiedGap.qcdG2M4_certified_gap
```

# From The Emitted Certificate To The Theorem

:::paragraph
A certificate is only useful if it can be *read*. The solver writes one flat JSON
object per line: a parity label, the sector Ritz value and the assembled width. The
reader parses those lines into the parameters of the gap theorem, and it does so
without ever producing a floating-point number: a decimal literal is stored exactly,
as a mantissa together with a power of ten, so that the value the proof consumes is a
rational and not a rounded approximation. A line that is missing a field, or whose
number is not a decimal, or which asserts a negative width, fails to parse rather than
being defaulted.
:::

:::paragraph
What the reader then proves is the gap theorem with the parsed numbers substituted in:
given the two enclosures the certificate asserts, the certified difference
$`\theta^o - \theta^e - (\delta^o + \delta^e)`$ is a lower bound for the parity gap of
the truncated Hamiltonian. Worked through on the recorded run — measured gap $`1.9875`,
assembled width $`0.0555` — the emitted text alone yields a certified gap of at least
$`1.932`, in particular a strictly positive one.
:::

```
#check @BookProof.SirkCertificateReader.parseDec_example
#check @BookProof.SirkCertificateReader.parseDec_reject
#check @BookProof.SirkCertificateReader.gap_ge_of_ndjson
#check @BookProof.SirkCertificateReader.gap_pos_of_ndjson
#check @BookProof.SirkCertificateReader.formatExample_lower
#check @BookProof.SirkCertificateReader.formatExample_certified_gap
```

# A Table Of Couplings, And The Finite-Size Limit

:::paragraph
One certificate certifies one operator. Adding the two reverse enclosures turns the
one-sided bound into a genuine enclosure of the gap, and the same statement can then be
made a row at a time: for each coupling constant, a measured difference and an
assembled width, and a proof that the gap of *that* truncated Hamiltonian lies in *that*
window. The analytic strong-coupling value $`g^2/2` is compared against the window
rather than assumed: at $`g = 2` the prediction is $`2`, and the certified window of the
recorded run is $`[1.932, 2.043]`, which contains it.
:::

:::paragraph
The finite-size study asks a different question — what the gap tends to as the lattice
grows. If the finite-size correction is a pure power $`C \, l^{-p}`, the Richardson
combination of two lattice sizes returns the limit exactly, and if the two values are
known only to within $`\varepsilon`$, the extrapolant is off by at most
$`\varepsilon (1 + 2/X)`, where $`X` is the extrapolation denominator. That is a
theorem. The number obtained by feeding the recorded lattice data into it is not: it is
a numerical estimate, and the passage to the thermodynamic limit is not claimed.
:::

```
#check @BookProof.SirkGapTable.certified_gap_mem_interval
#check @BookProof.SirkGapTable.certified_gap_table
#check @BookProof.SirkGapTable.certified_gap_table_interval
#check @BookProof.SirkGapTable.qcdG2M4_strongCoupling_consistent
#check @BookProof.SirkGapTable.richardson_exact
#check @BookProof.SirkGapTable.richardson_error
```

# What Would Close The One-Particle Limit

:::paragraph
Everything certified above is about the truncated operator. For QYM, the
Friedrichs/Hashimoto results already identify the selected operator with the real
one-particle Hamiltonian. The remaining step is the one-particle positive spectral-edge
convergence and its lift through the free number-preserving `dGamma` construction.
The strict shift `h₊ ≥ μ I` contributes `μ N`, leaves the vacuum unchanged, and makes
all non-vacuum finite-particle energies positive.
:::

:::paragraph
The optional shifted-square witness gives a spectral reformulation, but the primary
observable is the one-particle energy measured through creation and destruction.
:::

:::paragraph
What the continuum claim needs is that the gap is not destroyed in the limit, and that implication — as opposed to
the convergence itself — can be proved. Say an operator has a *quantitative gap* $`d` at
a point $`\lambda` when no vector is moved by less than $`d\|x\|`: for a bounded
self-adjoint operator that is exactly the statement that $`\lambda` is at distance at
least $`d` from the spectrum. Such a gap degrades by at most the size of a perturbation,
and it therefore survives an operator-norm limit with no loss at all. So a family of
approximants with a *uniform* gap on an interval forces the limit to have no spectrum in
that interval.
:::

:::paragraph
That is the shape of the missing leg, and it makes the remaining question precise: what
is open is not whether a uniform gap passes to the limit — it does — but whether the
truncation family converges in the sense required. Nothing here asserts that it does.
:::

```
#check @BookProof.SpectralGapStability.gapAt_perturb
#check @BookProof.SpectralGapStability.gapAt_of_tendsto
#check @BookProof.SpectralGapStability.notMem_spectrum_of_gapAt
#check @BookProof.SpectralGapStability.spectrum_disjoint_of_uniform_window
```

# The Honest Boundary

:::paragraph
For QYM, the selected Hashimoto operator is already identified in the formal development
with the real Friedrichs Hamiltonian. The remaining mass-gap target is narrower: prove
that the certified nested bands converge to the lowest positive one-particle edge, then
use the free number-preserving `dGamma` lift. The finite certificate and generic SIRK
error bands must not be described as a completed continuum mass-gap proof.
:::

:::paragraph
The QYM operator-identification step is already proved: the Hashimoto limit selects the
real Friedrichs Hamiltonian. The remaining gap is the explicit one-particle positive-edge
certificate/limit and its free `dGamma` lift. Crouzeix's inequality and the deferred
hypotheses with citations, not theorems of this development. What is fixed per
system is the region on which the deformation is measured, not a numerical value
for it. Strong resolvent convergence is the hypothesis of the Trotter–Kato
statement, supplied per system by the selection theorems, not proved there.
Finite precision is no longer outside the statements, but the certified claims are
about the *truncated* operator: the gap theorem is a theorem about the finite
compression the solver diagonalises, and the numbers of a particular run enter as
data, with the theorem conditional on the enclosures the certificate asserts. The
passage to the continuum — a gap-preserving norm-resolvent convergence of the
truncation family — is not proved here and is assumed nowhere.
:::
