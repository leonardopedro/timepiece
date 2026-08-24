import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Reliability of the Shift-Invert Rational Krylov Scheme" =>
%%%
tag := "sirk-reliability"
%%%

# What the Numerics Compute

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

# The Honest Boundary

:::paragraph
Crouzeix's inequality and the deferred deformation of the error bound are named
hypotheses with citations, not theorems of this development. What is fixed per
system is the region on which the deformation is measured, not a numerical value
for it. Strong resolvent convergence is the hypothesis of the Trotter–Kato
statement, supplied per system by the selection theorems, not proved there.
Nothing is said about floating-point arithmetic: the statements are about the
exact algorithm that the finite-precision computation approximates.
:::
