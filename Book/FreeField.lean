import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Free Fields: the Gaussian and the Uniform Sphere" =>
%%%
tag := "free-field"
%%%

# The Problem: There Is No Infinite-Dimensional Lebesgue Measure

The finite-dimensional Born parametrization puts a uniform-looking measure on the
sphere and pushes it to the simplex. To pass to *field theory* — infinitely many
degrees of freedom — we would like a uniform (Lebesgue-like) measure on an
infinite-dimensional sphere. There is an immediate obstruction:

*There is no non-zero, translation-invariant measure that is finite on bounded sets in an infinite-dimensional normed space.*

The proof is a clean volume argument. In a translation-invariant measure, all balls
of a given radius have the same measure. In infinite dimension a ball of radius
$`r` contains *infinitely many* disjoint balls of radius $`r/2` (because there is
an infinite orthonormal set, and the small balls around well-separated points are
disjoint). If the small balls have measure $`m > 0`, the big ball has infinite
measure; if $`m = 0`, countable additivity is not even needed to see the big ball
has measure $`0` once it is covered by countably many null balls in the
finite-on-bounded case. Either way, no measure can be both translation-invariant and
finite and non-zero on bounded sets.

The verified statements (module `BookProof.ChapterNoLebesgue`):

```
#check @ChapterNoLebesgue.measure_ball_eq_measure_ball_zero
#check @ChapterNoLebesgue.not_exists_nonzero_isAddLeftInvariant_finite_on_bounded
```

This is the rigorous content of the manuscript's claim that "there is no
non-informative prior" on a continuous infinite-dimensional space, and it forces the
free-field construction to build its uniform measure *out of the Gaussian* rather
than out of a nonexistent Lebesgue measure.

# The Substitute: the Rotation-Invariant Gaussian

The standard Gaussian on $`\mathbb{R}^n`,

$$`\gamma_n(dx) = (2\pi)^{-n/2} e^{-\|x\|^2/2}\, dx,`

depends only on the radius $`\|x\|`. Consequently it is *rotation-invariant*:
pushing it forward by any orthogonal map $`L` leaves it unchanged. Its
characteristic function $`t \mapsto e^{-\|t\|^2/2}` likewise depends only on
$`\|t\|`, which pins down the measure and makes the invariance manifest.

The verified statements (module `BookProof.ChapterFreeFieldGaussian`):

```
#check @ChapterFreeFieldGaussian.instIsProbabilityMeasure_stdGaussian
#check @ChapterFreeFieldGaussian.charFun_stdGaussian
#check @ChapterFreeFieldGaussian.stdGaussian_map_linearIsometryEquiv
```

The last is the headline: $`(\gamma_n).\mathrm{map}(L) = \gamma_n` for every
orthogonal $`L`. The Gaussian is the canonical *rotation-invariant probability
prior*, the finite-dimensional stand-in for the uniform measure that does not exist
in infinite dimension.

# Pushing the Gaussian to the Sphere

Because the Gaussian has no atom at the origin (in dimension $`n \ge 1`), radial
normalization $`x \mapsto x/\|x\|` is defined almost everywhere and pushes
$`\gamma_n` to a probability measure *on the unit sphere*. By rotation-invariance
of the Gaussian, this induced sphere measure is itself rotation-invariant — it is
the *uniform measure on the sphere*, constructed without ever invoking a
Lebesgue measure on the infinite-dimensional ambient space. This is the
manuscript's free-field prior: "a uniform measure of an infinite-dimensional sphere
defined using the Gaussian measure and the Fock space."

This uniform sphere measure is the *Mehler measure*, and it is the exception to the
slogan this chapter opened with. There is no _Lebesgue_ uniform probability measure
on an infinite-dimensional space, but the Gaussian-built sphere measure is a genuine
uniform prior on the infinite-dimensional hypersphere. It is genuinely
non-informative — invariant under every symmetry the language can express — in the
{ref "solovay-tensor"}[Solovay–Kopperman space], where the restricted decidable
language forbids the reparametrizations that would otherwise turn a uniform prior
into an informative one ({ref "sequential-bayes"}[non-informativeness is
coordinate-dependent]). The free-field construction is the finite-dimensional shadow
of that infinite-dimensional exception.

# Why the Gaussian Is the Uniform Measure on the Infinite Sphere: the Mehler Limit

The claim that the Gaussian is the uniform measure "on an infinite-dimensional
sphere" is not a slogan; it is a genuine limit, due in spirit to Mehler (1866) and
made quantitative by López and Temme. On the surface of a $`k`-sphere the
rotation-invariant (uniform) area element factorizes into single-coordinate weights
$`(1-x^2)^{(\alpha-1)/2}` — exactly the *Gegenbauer* weight of order $`\alpha`.
The uniform hyperspherical measure is therefore the natural *prior*: it assigns equal
weight to every direction, expressing that we have no information. Its orthogonal
polynomials are the Gegenbauer polynomials $`C_n^{(\alpha/2)}`.

The infinite-dimensional limit is where the identification becomes the Gaussian.
Rescale the coordinate $`x \mapsto \sqrt{2/\alpha}\,x` and let $`\alpha \to \infty`.
The single-coordinate hyperspherical weight tends to the Gaussian weight
$`e^{-x^2}`:

$$`\lim_{\alpha\to\infty}\Bigl(1 - \tfrac{x^2}{\alpha}\Bigr)^{\alpha-1/2} = e^{-x^2}.`

The verified statement (module `BookProof.PhysHSGaussian`):

```
#check @PhysHSGaussian.weight_tendsto_gaussian
```

At the same time the Gegenbauer polynomials become the Hermite polynomials
$`H_n/n!` (with the physicists' $`H_n` defined by the recurrence
$`H_0 = 1, H_1 = 2x, H_{n+2} = 2x H_{n+1} - 2(n+1)H_n`), in the scaled limit

$$`\lim_{\alpha\to\infty}\Bigl(\tfrac{\alpha}{2}\Bigr)^{-n/2}
  C_n^{(\alpha/2)}\Bigl(\sqrt{\tfrac{2}{\alpha}}\,x\Bigr)
   = \frac{H_n(x)}{n!}.`

The verified statement (module `BookProof.PhysHSGaussian`):

```
#check @PhysHSGaussian.physHermite
#check @PhysHSGaussian.gegenbauer
#check @PhysHSGaussian.gegenbauerScaled
#check @PhysHSGaussian.gegenbauerScaled_tendsto_hermite
```

The normalizations converge consistently as well: the (squared) Gegenbauer
normalization integral against the hyperspherical weight tends to the Hermite
normalization integral against the Gaussian weight,

$$`\int_\mathbb{R}\Bigl[\frac{H_n(x)}{n!}\Bigr]^2 e^{-x^2}\,dx
   = \frac{\sqrt{\pi}\,2^n}{n!}.`

The verified statements (module `BookProof.PhysHSGaussian`):

```
#check @PhysHSGaussian.hermite_normalization
#check @PhysHSGaussian.normalization_tendsto
```

This is the precise sense in which the uniform (hyperspherical) prior and the
Gaussian (Fock) vacuum coincide, and in which the orthogonal excitations of the Fock
space are the images of the hyperspherical harmonics. The dictionary is complete:

| Finite hypersphere ($`\alpha < \infty`) | Infinite-dimensional limit (Fock) |
| :--- | :--- |
| uniform surface measure $`d\sigma` | Gaussian measure $`e^{-x^2}dx` |
| Gegenbauer weight $`(1-x^2)^{(\alpha-1)/2}` | Gaussian weight $`e^{-x^2}` |
| Gegenbauer polynomials $`C_n^{(\alpha/2)}` | Hermite polynomials $`H_n/n!` |
| hyperspherical harmonics | number states $`\ket{n}` |
| uniform "no-information" prior | Gaussian source qsample $`\Psi_0 = \ket{0}` |

That the Gaussian pushes forward to the *uniform* sphere measure, and is itself
rotation-invariant, is proved in the same module (and is the mechanism used above to
build the sphere measure in the first place):

```
#check @PhysHSGaussian.gaussianE_rotation_invariant
#check @PhysHSGaussian.sphereUniform_rotation_invariant
```

And the concentration is quantitative: for an almost-every sequence of standard
Gaussian coordinates, the empirical squared norm $`\sum_{i<k}\omega_i^2` grows like
$`k`, i.e. the Gaussian sample sits on the sphere of radius $`\sqrt{k}` in the
limit — the strong-law form of "the Gaussian concentrates on the sphere":

```
#check @PhysHSGaussian.gaussian_concentration_sphere
```

So the free-field prior is not merely *a* rotation-invariant measure: it is the
infinite-dimensional limit of the family of uniform hyperspherical priors, with the
Fock excitations as the limits of the hyperspherical harmonics. This is what makes
the Gaussian source qsample $`\sqrt{p_0}` of a flow model coincide with the Fock
vacuum that the companion algebra manipulates natively.

# Born Pushes the Sphere to the Simplex

Composing the two maps — normalize the Gaussian to the sphere, then apply the Born
rule $`\psi \mapsto |\psi|^2` — parametrizes the probability simplex by the
Gaussian-built sphere measure. The finite-dimensional Born map is continuous and
surjective ({ref "born-reproduces"}[The Born rule reproduces every distribution]),
and its fibers are the phase/sign gauge of
{ref "born-fiber"}[the gauge ambiguity]. The simplex is thus realized as a
*quotient* of the Gaussian-built sphere by the gauge group, with a canonical
rotation-invariant measure on top.

# Differentiability in the Fourier-Transformed Space

The manuscript's free-field section is careful about a cost of the parametrization:
because the uniform prior attributes null measure to *deterministic* functions, one
*sacrifices point-evaluation* of a classical field, and so "continuity and
differentiability notions must be redefined for quantum fields". Its justification
that this is not a problem is that *the smooth wave-functions are dense in the
Hilbert space* — an approximation statement.

That justification is correct but incomplete. The stronger fact is that, in the
Fourier-transformed space, the field is already smooth almost everywhere, not merely
approximable by smooth functions. The momentum constraint of the free-field section
is $`iD_x = 0` with $`p` the eigenvalue of the derivative operator that the Fourier
transform diagonalizes: in the Fourier picture, differentiation is multiplication by
a real frequency, and the (Fourier-transformed) wave-function that defines the
creation operator is the analytic continuation of that frequency function. Analytic
functions are smooth everywhere, so the represented field is smooth on the
transformed space — the null-measure caveat of the manuscript's point-evaluation
discussion is discharged in the Fourier domain *before* any density argument is
needed.

The same phenomenon appears in number-theoretic series: the series used in
Bagchi's universality theorem (and the Dirichlet series it is built from) is
convergent and analytic on a half-plane, and its analytic continuation is smooth
almost everywhere in the transformed (frequency) variable. There too the smoothness
is not an approximation imposed by a choice of prior; it is a property the analytic
continuation already has. The manuscript's density argument describes what is true
in the *original* (position) space; the sharper statement is that the *Fourier* or
frequency representation of the same object is already smooth, so the
differentiability notions the manuscript says must be "redefined" are in fact
satisfied pointwise (almost everywhere) on the transformed side.

The density assertion the manuscript relies on is itself verified
(`polynomial_dense_L2` in `BookProof.PhysFunctionalAnalysis`: polynomials — hence
smooth functions — are dense in $`L^2` with respect to the uniform
(unit-interval) measure):

```
#check @PhysFunctionalAnalysis.polynomial_dense_L2
```

This is the approximation statement: it says smooth functions are *close* to every
$`L^2` field. The Fourier-domain observation above is the strictly stronger one: in
the transformed space the field is already smooth a.e., so no approximation step is
needed there. Both facts coexist — the former concerns the original space, the
latter concerns its Fourier representation.

This is consistent with, and sharpens, the rest of the free-field thread: the
Gaussian-built uniform measure is rotation-invariant, its Fourier transform is the
same Gaussian (self-dual), and the frequency representation of a field drawn from
that prior is a smooth, analytically-continuable object rather than a merely
approximable one.

# A Countability Sanity Check

One last measure-theoretic fact keeps the countable Euler-angle parametrization of
{ref "born-reproduces"}[the Born-rule chapter] honest. The manuscript asserts that
"any partition of the phase-space (where each part has a non-null Lebesgue measure)
is countable." This is a general fact about s-finite measures: a pairwise-disjoint
family of measurable sets, *every* one of positive measure, must be countable —
because in each measure band $`[1/(k+1), 1/k]` there can be only finitely many
disjoint sets, and a countable union of finite sets is countable.

The verified statements (module `BookProof.ChapterCountablePartition`):

```
#check @ChapterCountablePartition.countable_of_partition_pos
#check @ChapterCountablePartition.prob_partition_countable
```

So when the book indexes the parts of a phase-space partition by a countable
orthonormal basis (the setting of the countable stick-breaking chain), it is not
making an extra assumption: positivity of the part measures *forces* the index set
to be countable.

# Dimensional Reduction: the Krylov Shortcut and the Compiled Sketch

:::paragraph
The same Gaussian/Fock substrate is what makes the *computational* side of the
free-field thread tractable. Two reductions do the work. The first is the
inversion-free Krylov shortcut: the Krylov subspace
$`\mathrm{Kry}_m(\bar H, v_0) = \mathrm{span}\{v_0, \bar H v_0, \dots, \bar H^{m-1}v_0\}`
is unchanged when the generator is shifted by a multiple of the identity, because
the shift only adds lower-order terms. So the sequence $`w_k = (\bar H - \gamma I)w_{k-1}`,
which never solves a linear system, spans exactly the same subspace as the
rational construction that would; and pre-conditioning the seed makes the
resolvent merely lower the polynomial degree. The generator itself is bounded —
the Mehler projector is rank-one, the number operators diagonal.
:::

```
#check @BookProof.ChapterH5.krylovSpan
#check @BookProof.ChapterH5.krylov_subspace_span
#check @BookProof.ChapterH5.shift_pow_sub_pow_mem
#check @BookProof.ChapterH5.krylovSpan_shift_eq
#check @BookProof.ChapterH5.inversion_free_seed
#check @BookProof.ChapterH5.generator_bounded_of_rankOneProjector
#check @BookProof.ChapterH5.krylov_no_inversion_eq_standard
```

:::paragraph
The second reduction reads the Krylov projection as a *spectral low-pass filter*.
The compression $`\bar H_{\text{reduced}} = V^{\mathsf H}\bar H V` has the
restricted quadratic form, so each of its eigenvalues is a Rayleigh quotient of
the full generator and can never exceed its norm: the projection keeps
frequencies, it does not invent them. What it discards costs only the $`e^{-hm}`
term already carried by the SIRK error bound, which decays to zero as the
retained dimension grows. And generation is then a *single* matrix exponential
of an explicitly $`m \times m` object.
:::

```
#check @BookProof.ChapterH6.sirk_error_decay_exponential
#check @BookProof.ChapterH6.sirk_error_bound_antitone
#check @BookProof.ChapterH6.krylov_rayleigh_transfer
#check @BookProof.ChapterH6.krylovRetainsDominantSpectrum
#check @BookProof.ChapterH6.reduce_generator_mul_m
#check @BookProof.ChapterH6.generation_single_exponential
```

:::paragraph
The reductions form a *nested tower of approximation orders*, and this nesting is
itself a decidable, finite-dimensional statement — the part of the Hashimoto
convergence guarantee that needs no analytic input. Write $`\mathrm{Kry}_n`$ for
the order-$`n`$ Krylov subspace $`\mathrm{Kry}_n(\bar H, v_0)`$. Two facts are
purely algebraic. First, the subspaces nest:
$`\mathrm{Kry}_n \subseteq \mathrm{Kry}_{n+1}`$
($`\mathrm{krylovSpan\_mono}`$): the order-$`n`$ basis is the first $`n`$ vectors
of the order-($`n`+1) basis. Second, the order-$`n`$ reduced generator is the
top-left $`n \times n`$ block of the order-($`n`+1) reduced generator, because the
compression is upper-Hessenberg — so the order-$`n`$ approximant is the
*projection* of the order-($`n`+1) approximant onto $`\mathrm{Kry}_n`$: the finer
band, restricted to the coarser information, reproduces the coarser band exactly.
And the error bound is monotone in the same direction: the band
$`[0, \mathrm{sirkBound}(n+1)]`$ is contained in $`[0, \mathrm{sirkBound}(n)]`$
($`\mathrm{sirk\_error\_bound\_antitone}`$), and the bands collapse to $`\{0\}`$
as $`n`$ grows ($`\mathrm{sirk\_error\_decay\_exponential}`$).
:::

```
#check @BookProof.ChapterH5.krylovSpan_mono
#check @BookProof.ChapterH5.krylovSpan_map_le
#check @BookProof.ChapterH6.sirk_error_bound_antitone
#check @BookProof.ChapterH6.sirk_error_decay_exponential
#check @BookProof.ChapterH6.sirk_error_tendsto_zero
#check @BookProof.ChapterH7.compress_isSelfAdjoint
#check @BookProof.ChapterH7.compression_eigenvalue_mem_numericalRange
#check @BookProof.ChapterH8.sirk_krylov_tower
#check @BookProof.ChapterH8.sirk_compression_block
#check @BookProof.ChapterH8.sirk_compression_submatrix
#check @BookProof.ChapterH8.sirk_band_refinement
#check @BookProof.ChapterH8.sirk_band_refinement_proj
#check @BookProof.ChapterH8.sirk_approx_projection
#check @BookProof.ChapterH8.sirk_band_refinement_poly
#check @BookProof.ChapterH8.sirk_band_refinement_rational
#check @BookProof.ChapterH8.sirk_approx_projection_poly
#check @BookProof.ChapterH8.sirk_approx_projection_rational
#check @BookProof.ChapterH8.sirk_band_refinement_of_orthonormal
#check @BookProof.ChapterH8.sirk_compression_submatrix_of_orthonormal
#check @BookProof.ChapterH8.krylovOrthonormal_span
#check @BookProof.ChapterH8.krylovEmbedding_range
#check @BookProof.ChapterH8.sirk_band_refinement_krylov
#check @BookProof.ChapterH8.sirk_band_contained
#check @BookProof.ChapterH8.sirk_band_contained_le
#check @BookProof.ChapterH8.sirk_compression_submatrix_le
#check @BookProof.ChapterH8.sirk_nested_orders
#check @BookProof.ChapterH8.sirk_nested_orders_le
```

:::paragraph
The honest boundary: the *nesting* above is finite-dimensional linear algebra over
the decidable skeleton (Solovay–Mehler–Kopperman: every inner product over the
infinite substrate collapses to a finite head integral), so it is provable
without any analytic hypothesis. What the nesting does *not* supply is the
numerical *width* of the bands: that the true error lies inside
$`\mathrm{sirkBound}(n)`$ is conditional on Crouzeix's inequality
($`\mathrm{sirk\_error\_bound\_decay}`$, `ChapterH4`), which is recorded in
`BookProof/` as a named hypothesis rather than an axiom. The band-containment
statement itself — order-($`n`$+1) refines order-$`n`$, iterated — is proved in
`ChapterH8`: the block identity $`\mathrm{sirk\_compression\_block}`$, the
projection identities $`\mathrm{sirk\_band\_refinement}`$ and
$`\mathrm{sirk\_approx\_projection}`$, and the tower
$`\mathrm{sirk\_nested\_orders}`$ — which holds not only one step at a time but
between any two orders $`m \le n`$ ($`\mathrm{sirk\_nested\_orders\_le}`$, with
the leading-block identity $`\mathrm{sirk\_compression\_submatrix\_le}`$). The
refinement is not restricted to powers of
the generator: it holds for an arbitrary polynomial of the reduced generator
($`\mathrm{sirk\_band\_refinement\_poly}`$) and for the rational functions the
SIRK step actually evaluates — numerator polynomial over an invertible
denominator whose compression is invertible
($`\mathrm{sirk\_band\_refinement\_rational}`$), with the whole-space projection
forms $`\mathrm{sirk\_approx\_projection\_poly}`$ and
$`\mathrm{sirk\_approx\_projection\_rational}`$. The hypotheses are not vacuous:
any pair of nested orthonormal Krylov bases realizes them, through the embedding
of an orthonormal family and the coordinate inclusion along $`\mathrm{castLE}`$,
which gives the hypothesis-free instances
$`\mathrm{sirk\_band\_refinement\_of\_orthonormal}`$ and
$`\mathrm{sirk\_compression\_submatrix\_of\_orthonormal}`$. Those bases exist:
Gram–Schmidt on the Krylov sequence $`k \mapsto H^k v`$ produces one orthonormal
sequence whose prefixes are orthonormal, nested by construction and span the
Krylov subspaces ($`\mathrm{krylovOrthonormal\_span}`$,
$`\mathrm{krylovEmbedding\_range}`$), which gives the refinement statement for the
Krylov flag itself ($`\mathrm{sirk\_band\_refinement\_krylov}`$, under the
hypothesis that the Krylov sequence has not broken down before the finer order).
Two provisos are recorded
there. The refinement of the *approximants* needs the order-$`n`$ subspace to be
invariant under the compressed operator — the block-triangularity that makes the
leading block a generator in its own right; and the whole-space form of the projection
identity needs that subspace to *reduce* the operator (invariance under the
adjoint as well), since without it the leading block controls only the coarse
data.
:::

:::paragraph
The nesting has a spectral face as well: not only do the approximants refine, the
*frequencies* the reduced generators can see nest. Writing $`W(\cdot)`$ for the
numerical range — the set of Rayleigh quotients over unit vectors — the reduced
generators $`B_k = V_k^{*} X V_k`$ satisfy
$`W(B_m) \subseteq W(B_n) \subseteq W(X)`$ for $`m \le n`$
($`\mathrm{sirk\_numRange\_nested\_orders}`$, and
$`\mathrm{sirk\_numRange\_krylov}`$ for the Krylov flag the method actually
builds), with the matching norm chain $`\|B_m\| \le \|B_n\| \le \|X\|`$ and the
uniform envelope $`W(X) \subseteq \{|z| \le \|X\|\}`$. Every Ritz value of a
coarse order is therefore a Rayleigh quotient of every finer order, and of the
full generator ($`\mathrm{ritz\_mem\_numRange}`$,
$`\mathrm{ritz\_mem\_numRange\_compress}`$): refining the order can only *add*
frequencies, and never one the physics does not already have. Since a
finite-dimensional reduced generator has only eigenvalues in its spectrum, the
whole Ritz *spectrum* nests the same way
($`\mathrm{spectrum\_compress\_subset\_numRange\_orthonormal}`$). Positivity and any
real window $`[a,b]`$ of the quadratic form survive compression at every order
($`\mathrm{compress\_nonneg}`$, $`\mathrm{compress\_re\_inner\_mem\_Icc}`$). The
direction matters for honesty: since the numerical ranges *grow* with the order,
a Crouzeix-type bound $`C \sup_{W(B)}|f|`$ is non-decreasing in the order — the
band decay of $`\mathrm{sirkBound}`$ comes from the approximation quality, not
from shrinking numerical ranges. Convexity of the numerical range
(Toeplitz–Hausdorff) is neither used nor claimed. The approximation quality
itself does improve, unconditionally: the Krylov subspaces are
finite-dimensional, so the orthogonal projection onto them exists, and since they
nest, the best-approximation error is antitone in the order — for $`m \le n`$ the
order-$`n`$ subspace approximates any target at least as well as the order-$`m`$
one ($`\mathrm{krylov\_bestApprox\_antitone}`$), and when the Krylov flag is
dense — a cyclic seed — the error tends to $`0`$
($`\mathrm{krylov\_bestApprox\_tendsto\_zero}`$). Those statements need no
Crouzeix constant; what they do *not* give is a rate.
:::

```
#check @BookProof.ChapterH9.numRange_compress_subset
#check @BookProof.ChapterH9.numRange_compress_mono
#check @BookProof.ChapterH9.numRange_compress_chain
#check @BookProof.ChapterH9.numRange_subset_closedBall
#check @BookProof.ChapterH9.convexHull_numRange_compress_mono
#check @BookProof.ChapterH9.norm_compress_le
#check @BookProof.ChapterH9.norm_compress_mono
#check @BookProof.ChapterH9.ritz_mem_numRange
#check @BookProof.ChapterH9.ritz_mem_numRange_compress
#check @BookProof.ChapterH9.ritz_re_mem_Icc_of_fine
#check @BookProof.ChapterH9.compress_nonneg
#check @BookProof.ChapterH9.compress_re_inner_mem_Icc
#check @BookProof.ChapterH9.numRange_compress_orthonormal_mono
#check @BookProof.ChapterH9.spectrum_compress_subset_numRange
#check @BookProof.ChapterH9.spectrum_compress_subset_numRange_compress
#check @BookProof.ChapterH9.spectrum_compress_subset_numRange_orthonormal
#check @BookProof.ChapterH9.sirk_numRange_nested_orders
#check @BookProof.ChapterH9.sirk_numRange_krylov
#check @BookProof.ChapterH9.norm_sub_starProjection_antitone
#check @BookProof.ChapterH9.krylov_bestApprox_antitone
#check @BookProof.ChapterH9.krylov_bestApprox_tendsto_zero
```

:::paragraph
Finally, the offline stage: a two-level sketch hashes raw coordinates into $`k`
features and places the features on distinct modes of a $`K_2`-mode Fock space,
producing a genuine single-excitation state from which the features can be read
back; and all observables of the reduced space are pre-projected into a complete
basis of $`m^2` matrix units. The corpus size enters only there — the online
cost carries no such term.
:::

```
#check @BookProof.ChapterF8.singleExcitation
#check @BookProof.ChapterF8.twoLevelHash_total
#check @BookProof.ChapterF8.featureHash_decodes
#check @BookProof.ChapterF8.offline_operatorBasis
#check @BookProof.ChapterF8.online_cost_independent_of_M
#check @BookProof.ChapterF8.tsr_offline_compiles
```

:::paragraph
Two properties make the reduction safe to *run*. First, when the full generator
is self-adjoint the compression is self-adjoint too, so every eigenvalue of the
reduced generator is real and is pinned between any bounds satisfied by the
quadratic form of the full generator: the reduced dynamics can neither go
complex nor leave the frequency band of the physics it came from. Second, the
reduced propagator $`e^{-\mathrm{i}t\bar H}` of a Hermitian generator is
unitary, hence generation conserves the $`\ell^2` mass exactly — the generated
state is a state, at every step and for every horizon $`t`.
:::

```
#check @BookProof.ChapterH7.compress_isSelfAdjoint
#check @BookProof.ChapterH7.compression_rayleigh_real
#check @BookProof.ChapterH7.compression_eigenvalue_mem_numericalRange
#check @BookProof.ChapterH7.reduceGenerator_isHermitian
#check @BookProof.ChapterH7.generationOperator_mem_unitaryGroup
#check @BookProof.ChapterH7.generation_preserves_l2
```

# The Navier–Stokes Hamiltonian: a Complete Flow on the Truncation

:::paragraph
The same free-field parametrization is what the manuscript applies to the
Navier–Stokes equations: the velocity field, *its derivatives* $`u_{k,j}`,
$`u_{k,jj}`, and the conjugate momenta $`\pi^i` are all treated as independent
canonical degrees of freedom, and the Hamiltonian is the Weyl-symmetrized
$`H = \sum_i (\pi_i A_i + A_i \pi_i)` with
$`A_i = \sum_j u_j u_{i,j} - \nu\, u_{i,jj}`. That the derivatives may be treated
as fields is an operator statement: an operator-valued field
$`\varphi(X) = \varphi + \varphi_i (X_i - x_i)` collapses to its point value on
the position eigenstates, so the first-order Taylor coefficients are free modes
with commutation relations of their own.
:::

```
#check @BookProof.NavierStokesFlow.fieldTaylor
#check @BookProof.NavierStokesFlow.field_evaluates_to_value
#check @BookProof.NavierStokesFlow.field_evaluates_to_value_diagonal
#check @BookProof.NavierStokesFlow.ccr_field
#check @BookProof.NavierStokesFlow.derivativeField_momentum
#check @BookProof.NavierStokesFlow.secondDerivativeField_momentum
#check @BookProof.NavierStokesFlow.momentumConstraint_preserved
```

:::paragraph
The Eulerian side of that construction carries its own constraints, and the
manuscript's own taxonomy splits them in two. The relations that *define* the
derivative modes — $`u_{i,j} = \partial_j u_i` and $`u_{i,jk} = \partial_k
u_{i,j}` — have no explicit solution, so they are the ones a gauge generator has
to impose; their consequence is Clairaut's condition $`u_{i,jk} = u_{i,kj}`,
which makes the second-derivative modes symmetric. The momenta conjugate to the
derivative modes pair with them by a Kronecker delta, which is what makes each
derivative an independent canonical variable. Incompressibility
$`\partial_j u_j = 0`, by contrast, *does* have an explicit solution — the
substitution $`u_{3,3} = -(u_{1,1}+u_{2,2})` — so it is imposed by initial data
rather than by a gauge symmetry, and it is satisfied by genuinely non-constant
fields such as the cyclic shear $`u_i(x) = x_{i+1}`.
:::

```
#check @BookProof.NavierStokesEulerian.u_evaluates_to_value
#check @BookProof.NavierStokesEulerian.eulerian_momentum_constraint
#check @BookProof.NavierStokesEulerian.eulerian_momentum_dual
#check @BookProof.NavierStokesEulerian.derivativeField_relates_to_field
#check @BookProof.NavierStokesEulerian.derivativeField_second
#check @BookProof.NavierStokesEulerian.derivativeField_consistency
#check @BookProof.NavierStokesEulerian.eulerian_divergence_constraint
#check @BookProof.NavierStokesEulerian.cyclicShear_divergence_free
```

:::paragraph
The constraint is stated properly only once a *second coordinate* $`y` is
adjoined to the space coordinate $`x`: the field that enters the Hamiltonian is
the expansion $`u_i(y) = u_i + u_{i,j} y_j` in that second coordinate. Each
coordinate then comes with a gauge generator. For $`x` it is the standard
momentum $`\pi^j = \partial/\partial x_j`; for $`y` it is the generator built
from the *derivatives of* $`u_i`,
$`G_j = \partial/\partial y_j - u_{i,j}\,\partial/\partial u_i`, which translates
the second coordinate while shifting each velocity mode by its own first
derivative. Both generators annihilate $`u_i(y)` and the Hamiltonian symbol
$`A_i = u_j(y) u_{i,j} - \nu u_{i,jj}`, and they commute among themselves, so the
constraints are first class; and the coefficient $`u_{i,j}` is the only one for
which the invariance holds, which is exactly the content of
$`u_{i,j} = \partial u_i/\partial y_j`. In the initial state the second
coordinate evaluates to $`y = 0`, so the field collapses to its point value
$`u_i` there and the Hamiltonian acts as the ordinary Navier–Stokes one: the
second coordinate carries the constraint without changing the dynamics of the
initial data.
:::

```
#check @BookProof.NavierStokesGaugeY.uField
#check @BookProof.NavierStokesGaugeY.genX
#check @BookProof.NavierStokesGaugeY.genY
#check @BookProof.NavierStokesGaugeY.uField_pderiv_y
#check @BookProof.NavierStokesGaugeY.genX_ccr_x
#check @BookProof.NavierStokesGaugeY.genY_ccr_y
#check @BookProof.NavierStokesGaugeY.genY_shifts_velocity
#check @BookProof.NavierStokesGaugeY.genY_uField
#check @BookProof.NavierStokesGaugeY.genX_uField
#check @BookProof.NavierStokesGaugeY.genY_uField_perturbed_ne_zero
#check @BookProof.NavierStokesGaugeY.genY_genY_commute
#check @BookProof.NavierStokesGaugeY.genX_genY_commute
#check @BookProof.NavierStokesGaugeY.genY_nsSymbol
#check @BookProof.NavierStokesGaugeY.setYZero_uField
#check @BookProof.NavierStokesGaugeY.setYZero_nsSymbol
#check @BookProof.NavierStokesGaugeY.uFieldOp_apply_of_y_zero
#check @BookProof.NavierStokesGaugeY.hamiltonianOp_apply_of_y_zero
```

:::paragraph
That generator compensates only the *first* derivatives, so the Laplacian modes
$`u_{i,jj}` — the ones the viscous term is built from — are still spectators of
the expansion. Carrying the Taylor expansion in the second coordinate one order
further repairs this. The field is
$`u_i(y) = u_i + u_{i,j} y_j + \tfrac12 u_{i,jj} y_j^2`, its $`y`-derivative is
the *derivative field* $`u_{i,j}(y) = u_{i,j} + u_{i,jj} y_j`, and the gauge
generator becomes
$`G^2_j = \partial/\partial y_j - u_{i,j}\,\partial/\partial u_i
- u_{i,jj}\,\partial/\partial u_{i,j}`: it shifts the velocity modes by their
first derivatives *and* the first-derivative modes by the Laplacian modes.
$`G^2_j` annihilates both fields, hence the symbol
$`A_i(y) = u_j(y)u_{i,j}(y) - \nu u_{i,jj}` built from them, and the
second-order generators still commute with each other and with the momenta, so
the constraints remain first class. The two orders are genuinely different: the
first-order generator leaves $`u_{i,jj}\,y_j` behind on the second-order field,
the second-order generator does not annihilate the first-order field, and the
Taylor coefficient $`\tfrac12` is the only one that works. On the initial state
$`y = 0` the second-order symbol collapses, once more, to the ordinary
Navier–Stokes symbol $`u_j u_{i,j} - \nu u_{i,jj}`.
:::

```
#check @BookProof.NavierStokesGaugeY2.uField2
#check @BookProof.NavierStokesGaugeY2.uDField
#check @BookProof.NavierStokesGaugeY2.genY2
#check @BookProof.NavierStokesGaugeY2.uField2_pderiv_y
#check @BookProof.NavierStokesGaugeY2.uField2_pderiv_y_twice
#check @BookProof.NavierStokesGaugeY2.genY2_leibniz
#check @BookProof.NavierStokesGaugeY2.genY2_uField2
#check @BookProof.NavierStokesGaugeY2.genY2_uDField
#check @BookProof.NavierStokesGaugeY2.genY_uField2_ne_zero
#check @BookProof.NavierStokesGaugeY2.genY2_uField_ne_zero
#check @BookProof.NavierStokesGaugeY2.genY2_uField2_perturbed_ne_zero
#check @BookProof.NavierStokesGaugeY2.genY2_genY2_commute
#check @BookProof.NavierStokesGaugeY2.genX_genY2_commute
#check @BookProof.NavierStokesGaugeY2.genY_genY2_not_commute
#check @BookProof.NavierStokesGaugeY2.genY2_nsSymbol2
#check @BookProof.NavierStokesGaugeY2.genX_nsSymbol2
#check @BookProof.NavierStokesGaugeY2.setYZero_nsSymbol2
```

:::paragraph
On a *finite truncation* — finitely many modes, each a Hermitian matrix, the
field modes commuting as multiplication operators do — the whole claim is
provable. The Hamiltonian is Hermitian (the anticommutator of two Hermitian
factors is Hermitian), it is a polynomial of degree at most three in the
generators, and therefore $`U(t) = e^{\mathrm{i}tH_N}` is a one-parameter
unitary group defined for *every* real time: the flow is complete, it preserves
the $`\ell^2` mass, and every coefficient of the evolved state stays bounded by
the initial mass — no finite-time singularity on the truncation. The truncated
generator also has vanishing deficiency, which on a finite-dimensional space is
exactly essential self-adjointness.
:::

```
#check @BookProof.NavierStokesFlow.NSTruncation
#check @BookProof.NavierStokesFlow.nsHamiltonian
#check @BookProof.NavierStokesFlow.nsHamiltonian_hermitian
#check @BookProof.NavierStokesFlow.nsHamiltonian_isPolynomial
#check @BookProof.NavierStokesFlow.nsWord_length_le_three
#check @BookProof.NavierStokesFlow.nsHamiltonian_ne_zero_example
#check @BookProof.NavierStokesFlow.nsFlow_zero
#check @BookProof.NavierStokesFlow.nsFlow_group
#check @BookProof.NavierStokesFlow.nsFlow_unitary
#check @BookProof.NavierStokesFlow.nsFlow_norm_preserving
#check @BookProof.NavierStokesFlow.nsFlow_noBlowup
#check @BookProof.NavierStokesFlow.nsFlow_groupOnEvolved
#check @BookProof.NavierStokesFlow.nsHamiltonian_hasZeroDeficiency
```

:::paragraph
Completeness of the flow has a differential counterpart, which is the form in
which the manuscript states existence and uniqueness. On the truncation the
curve $`\psi(t) = U(t)\psi` is differentiable and solves
$`\dot\psi(t) = \mathrm{i}H_N\psi(t)`, and it is the *only* solution: any
differentiable curve satisfying the same equation with the same initial value
coincides with it at every time. So the Cauchy problem has exactly one global
solution, defined for all $`t\in\mathbb{R}` and confined to the sphere of the
initial mass. The proof of uniqueness is the classical one — the derivative of
$`t \mapsto U(-t)y(t)` vanishes, so that curve is constant. Along the way the
energy is conserved too: the expectation of $`H_N` in the evolved state does not
depend on time.
:::

```
#check @BookProof.NavierStokesFlow.nsFlow_hasDerivAt
#check @BookProof.NavierStokesFlow.nsFlow_solves_schrodinger
#check @BookProof.NavierStokesFlow.nsFlow_unique_solution
#check @BookProof.NavierStokesFlow.nsCauchy_existsUnique
#check @BookProof.NavierStokesFlow.nsFlow_energy_conserved
#check @BookProof.NavierStokesFlow.nsFlow_continuous
```

:::paragraph
The divergence constraint enters à la BRST. Its resolution is the book's own
substitution $`u_{3,3} = -(u_{1,1} + u_{2,2})`, and the truncated BRST charge
$`\Omega = u_{j,j}\otimes\psi^\dagger` is nilpotent because the ghost creation
operator is — the charge itself is not Hermitian, which is why the physical
space is a cohomology and not an eigenspace. In parcel (Lagrangian) variables
the constraint becomes volume preservation: a unit Jacobian determinant
preserves the volume of every set, and its infinitesimal form is exactly
$`\nabla\cdot u = 0`, since the derivative of $`t \mapsto \det(1 + tA)` at
$`t = 0` is $`\operatorname{tr} A`. In those variables the advection term is a
*positive* second-order operator (a sum of squares of the parcel momenta), the
viscosity likewise, the force a first-order drift and the pressure the 0-order
constraint.
:::

```
#check @BookProof.NavierStokesFlow.nsDivergenceConstraint_resolution
#check @BookProof.NavierStokesFlow.nsBrstCharge
#check @BookProof.NavierStokesFlow.nsBrst_nilpotent
#check @BookProof.NavierStokesFlow.nsBrst_adjoint
#check @BookProof.NavierStokesEulerian.nsBrst_not_hermitian
#check @BookProof.NavierStokesEulerian.nsBrst_symmetrization_hermitian
#check @BookProof.NavierStokesFlow.lagrangian_velocity
#check @BookProof.NavierStokesFlow.volume_preservation_constraint
#check @BookProof.NavierStokesFlow.det_one_add_smul_hasDerivAt
#check @BookProof.NavierStokesFlow.LagrangianNS.transformed_hamiltonian_decomposition
#check @BookProof.NavierStokesFlow.LagrangianNS.kinetic_posSemidef
#check @BookProof.NavierStokesFlow.LagrangianNS.viscous_posSemidef
#check @BookProof.NavierStokesFlow.LagrangianNS.transformed_hamiltonian_hermitian
#check @BookProof.NavierStokesFlow.LagrangianNS.flowUnitary_unitary
#check @BookProof.NavierStokesFlow.LagrangianNS.flowUnitary_group
#check @BookProof.NavierStokesFlow.LagrangianNS.cauchy_existsUnique
```

:::paragraph
Because that transformed operator is Hermitian on the truncation, everything
said about the flow of $`H_N` holds for it verbatim: $`e^{\mathrm{i}t\hat h}` is
a one-parameter unitary group and the corresponding Cauchy problem has exactly
one global solution. That is the truncated form of the Lagrangian route — the
continuum statement remains unclaimed.
:::

:::paragraph
The honest boundary. Nothing above claims essential self-adjointness of the
*untruncated continuum* operator — and with it, nothing claims global
existence/uniqueness for the *classical* Navier–Stokes equations (the Clay
regularity problem, deliberately out of scope). The distinction matters: once
ESA *is* proved, global existence of the operator flow follows automatically
(Stone's theorem: a self-adjoint operator generates a complete unitary group for
every real time) — that is exactly what `book.tex` §4210-4216 means by "the
solution ... exists and it is unique", and the truncation already proves it as
`nsCauchy_existsUnique`. The open step is ESA itself for the continuum operator,
not a separate global-existence claim. The ODE chapter is the standing warning:
for $`\dot x = x^2` the Hamiltonian $`x^2\hat p - \mathrm{i}\hat x` is a
polynomial of degree three whose classical flow is incomplete, so "low degree in
the fields" cannot by itself give self-adjointness — it gives symmetry. The
continuum route that remains is the Faris–Lavine commutator criterion applied to
the Lagrangian-transformed operator, whose second-quantized form on the
Fock-of-a-Fock space is at most *quadratic* in the outer ladder operators, and
whose comparison operator is the (positive) outer number operator. That
criterion is recorded as a named hypothesis, never an axiom, exactly as
Crouzeix's inequality is in `ChapterH4`; its two analytic inequalities for the
continuum operator are a research target, not a result.
:::

```
#check @BookProof.NavierStokesFlow.nsFockOfFock
#check @BookProof.NavierStokesFlow.nsSecondQuant
#check @BookProof.NavierStokesFlow.ns_outer_degree_le_two
#check @BookProof.NavierStokesFlow.nsNumberOp
#check @BookProof.NavierStokesFlow.nsNumberOp_eq_secondQuant
#check @BookProof.NavierStokesFlow.nsNumberOp_posSemidef
#check @BookProof.NavierStokesFlow.HasZeroDeficiency
#check @BookProof.NavierStokesFlow.symmetric_hasZeroDeficiency
#check @BookProof.NavierStokesFlow.ns_esa_of_farisLavine
```

:::paragraph
The named hypothesis has to be the *honest* criterion. Stated without the
symmetry of the operator it is contradictory — $`H = \mathrm{i}\cdot 1` with
comparison operator the identity satisfies both inequalities while having a full
deficiency space — so a conditional theorem resting on it would be vacuous. With
symmetry the criterion is satisfiable, and for operators defined on the whole
space it is automatic: symmetry alone already forces the deficiency to vanish.
The analytic content of Faris–Lavine therefore lives entirely in the densely
defined case, where the deficiency spaces are those of the *adjoint*; that is
the predicate under which the conditional theorem is restated, and where the
truncation — whose domain is the whole space — is the only case proved here.
:::

```
#check @BookProof.NavierStokesFlow.farisLavine_without_symmetry_forces_trivial
#check @BookProof.NavierStokesFlow.farisLavine_holds_of_everywhereDefined
#check @BookProof.NavierStokesFlow.HasZeroDeficiencyOn
#check @BookProof.NavierStokesFlow.hasZeroDeficiencyOn_top_of_symmetric
#check @BookProof.NavierStokesFlow.nsHamiltonian_hasZeroDeficiencyOn
#check @BookProof.NavierStokesFlow.ns_esa_of_farisLavine_dense
```

:::paragraph
There is one criterion under which the passage from the truncation to an
infinite-dimensional operator is not a change of kind: *a complete flow*. If a
symmetric operator on a dense domain generates a norm-preserving flow that is
defined for *every* real time and leaves the domain invariant, then the
deficiency spaces of its adjoint vanish — the operator is essentially
self-adjoint. The proof is the classical orbit argument: a deficiency vector
$`w` with $`H^{*}w = \pm\mathrm{i}w` makes the orbit function
$`g(t) = \langle w, U(t)v\rangle` satisfy $`g' = \pm g`, so $`g(t) = g(0)e^{\pm t}`,
while unitarity of the flow keeps $`|g|` bounded on the whole line; hence
$`g(0) = \langle w, v\rangle = 0` for every $`v` in the dense domain, and
$`w = 0`. Completeness is exactly the hypothesis that a finite-time blow-up
would destroy, which is why the ODE chapter's $`\dot x = x^{2}` example is the
standing warning for the continuum case.
:::

```
#check @BookProof.NavierStokesFlow.eq_zero_of_hasDerivAt_smul_of_bounded
#check @BookProof.NavierStokesFlow.hasZeroDeficiencyOn_of_completeUnitaryFlow
#check @BookProof.NavierStokesFlow.nsHamiltonian_hasZeroDeficiencyOn_of_flow
```

:::paragraph
The criterion is applied where its hypotheses are actually available: to the
truncation, whose flow is complete by construction. Nothing is claimed for the
untruncated generator, whose flow completeness is the open problem.

A second, genuinely infinite-dimensional case is available on the bounded
$`\ell^{2}(\mathbb{Z})` layer: a bounded symmetric operator is essentially
self-adjoint on *every* dense invariant domain, and the Weyl-symmetrized
continuity generator $`H = \tfrac12(pv + vp)` leaves the domain of finitely
supported modes invariant. That domain is dense but is *not* the whole space, so
this is the first instance in the development of vanishing adjoint deficiency on
a proper dense domain — the setting in which the notion has analytic content.
:::

```
#check @BookProof.NavierStokesFlow.hasZeroDeficiencyOn_of_bounded_symmetric
#check @BookProof.NavierStokesFlow.finiteModes
#check @BookProof.NavierStokesFlow.finiteModes_dense
#check @BookProof.NavierStokesFlow.finiteModes_ne_top
#check @BookProof.NavierStokesFlow.continuityHamiltonian_hasZeroDeficiencyOn_finiteModes
```

:::paragraph
Both criteria are needed, because symmetry on a dense domain is by itself never
enough. On $`\ell^{2}(\mathbb{N})`, with the finitely supported states as domain,
the tridiagonal operator
$`(Hf)(0) = a_{0}f(1)`, $`(Hf)(n+1) = a_{n}f(n) + a_{n+1}f(n+2)` with real
weights $`a_{0} = 2`, $`a_{n+1} = 4a_{n}+2` is symmetric on that dense domain,
yet the square-summable geometric sequence $`w(n) = (\mathrm{i}/2)^{n}` satisfies
$`Hw = \mathrm{i}w` coefficientwise and is therefore a deficiency vector of the
adjoint: essential self-adjointness *fails*. The one computation behind both
statements is the discrete Green identity — the truncated sum of Wronskian
increments telescopes to a boundary term, which vanishes for finitely supported
states.

So the "polynomial of low degree in the fields" hypothesis, which gives symmetry
on the finite-particle domain, cannot by itself yield essential self-adjointness;
an analytic input — a complete flow, boundedness, or the Faris–Lavine
inequalities — is required.
:::

```
#check @BookProof.NavierStokesFlow.JacobiDeficiency.jacobi_wronskian
#check @BookProof.NavierStokesFlow.JacobiDeficiency.jacobiOp_symmetric
#check @BookProof.NavierStokesFlow.JacobiDeficiency.defState_deficiency
#check @BookProof.NavierStokesFlow.JacobiDeficiency.jacobiOp_not_hasZeroDeficiencyOn
#check @BookProof.NavierStokesFlow.JacobiDeficiency.jacobi_symmetric_dense_not_esa
```

:::paragraph
Unboundedness by itself is not the obstruction either. A symmetric operator that
carries a *total* family of eigenvectors inside its domain — only the zero
vector is orthogonal to all of them — is essentially self-adjoint, because
testing the deficiency identity against an eigenvector `e` with real eigenvalue
$`\lambda` gives $`(\lambda \mp \mathrm{i})\langle e, w\rangle = 0`. A diagonal
operator on $`\ell^{2}(\mathbb{N})` with an arbitrary, possibly unbounded, real
sequence of entries satisfies this on the same finitely supported domain on
which the tridiagonal example fails. What separates the two is whether the
domain carries enough eigenvectors. That diagonal operator is genuinely
unbounded whenever its sequence of entries is: no constant dominates it on the
finite-mode domain, so essential self-adjointness there is not a boundedness
phenomenon in disguise.
:::

```
#check @BookProof.NavierStokesFlow.hasZeroDeficiencyOn_of_total_eigenvectors
#check @BookProof.NavierStokesFlow.DiagonalEsa.diagOp
#check @BookProof.NavierStokesFlow.DiagonalEsa.diagOp_basis
#check @BookProof.NavierStokesFlow.DiagonalEsa.diagOp_hasZeroDeficiencyOn
#check @BookProof.NavierStokesFlow.DiagonalEsa.diagOp_not_bounded
```

:::paragraph
The Lagrangian change of variables is what turns these criteria into a statement
about the Navier–Stokes generator itself. Writing the flow in parcel
coordinates — the trajectory operators $`X(\xi)` with conjugate momenta
$`P(\xi) = \dot X(\xi) = u(X(\xi))` in place of the Eulerian velocity — the
operator becomes
$`\hat h_{\mathrm{full}} = \tfrac12\sum_i P_i^{2} + \nu\sum_i Q_i^{2}
+ \sum_i f_i D_i + C`: two second-order terms, a first-order force drift and the
zeroth-order volume-preservation constraint. Untruncated — all of these are
(possibly unbounded) operators on a dense domain of an arbitrary complex
inner-product space — the transformed operator is symmetric, and the quadratic
forms of its two second-order terms are $`\tfrac12\sum_i\|P_i v\|^{2}` and
$`\nu\sum_i\|Q_i v\|^{2}`: the advection term, which in Eulerian variables is
the troublesome $`-u_j\partial_j u_i`, has become *positive*.
:::

```
#check @BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData
#check @BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hFull
#check @BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hFull_isSymmetricDom
#check @BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.kinetic_inner
#check @BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.kinetic_nonneg
#check @BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.viscous_nonneg
```

:::paragraph
Essential self-adjointness then follows in the transformed variables. A total
family of common eigenvectors of the constituents — the Lagrangian momentum
representation — makes the full transformed Hamiltonian essentially
self-adjoint, with eigenvalue
$`\tfrac12\sum_i p_i^{2} + \nu\sum_i q_i^{2} + \sum_i f_i d_i + c`; and because
vanishing adjoint deficiency is invariant under a unitary change of variables,
what is proved after the change of variables holds for the operator it came
from. Two untruncated realizations make this unconditional: on
$`\ell^{2}(\mathbb{Z})`, with the parcel momenta the symmetric-difference
lattice momentum — so $`\tfrac12\sum_i P_i^{2}` is a discrete Laplacian — the
transformed Hamiltonian is essentially self-adjoint on the *proper* dense domain
of finitely supported modes and is not the zero operator; on
$`\ell^{2}(\mathbb{N})`, with diagonal constituents of arbitrary real symbols,
it is essentially self-adjoint while being genuinely unbounded. The limits are
equally explicit: an unbounded first-order drift term alone already destroys the
property, so no criterion-free statement about the transformed data is
available, and essential self-adjointness of the *continuum* transformed
generator — the operator-flow global existence would follow from ESA by Stone's
theorem, but the classical global existence for Navier–Stokes would not — is not
claimed here.
:::

```
#check @BookProof.NavierStokesFlow.LagrangianEsa.LagrangianFullData.hasZeroDeficiencyOn_of_commonEigenvectors
#check @BookProof.NavierStokesFlow.LagrangianEsa.hasZeroDeficiencyOn_iff_of_linearIsometryEquiv
#check @BookProof.NavierStokesFlow.LagrangianEsa.NSFullData.hasZeroDeficiencyOn_of_lagrangian
#check @BookProof.NavierStokesFlow.LagrangianEsa.latticeLag_hasZeroDeficiencyOn
#check @BookProof.NavierStokesFlow.LagrangianEsa.latticeLag_hFull_ne_zero
#check @BookProof.NavierStokesFlow.LagrangianEsa.diagLag_hasZeroDeficiencyOn
#check @BookProof.NavierStokesFlow.LagrangianEsa.diagLag_not_bounded
#check @BookProof.NavierStokesFlow.LagrangianEsa.exists_lagrangianFullData_not_hasZeroDeficiencyOn
```

:::paragraph
The last step of the chain is the passage from one particle to the Fock space,
and it is where the comparison operator of the Faris–Lavine criterion has to be
rebuilt. Fock space here is the $`\ell^{2}` direct sum of the particle sectors,
and the finite-particle domain is the span of states supported in finitely many
sectors with each component in that sector's core. That domain is dense as soon
as every sector core is, and it is a *proper* subspace of the Fock space, so
nothing below is a statement about a boundedly extended operator. The second
quantization $`d\Gamma(A)` acts sector by sector, and vanishing adjoint
deficiency lifts: if every sector operator has it on its own core, so does
$`d\Gamma(A)` on the finite-particle domain. Applied to a one-particle
comparison operator this is the "cage" the criterion needs.
:::

```
#check @BookProof.NavierStokesFlow.SecondQuant.fockCore
#check @BookProof.NavierStokesFlow.SecondQuant.fockCore_dense
#check @BookProof.NavierStokesFlow.SecondQuant.fockOp
#check @BookProof.NavierStokesFlow.SecondQuant.fockOp_hasZeroDeficiencyOn
#check @BookProof.NavierStokesFlow.SecondQuant.fockCore_ne_top
```

:::paragraph
The one-particle comparison operator is $`n = \sum_i \pi_i^{2} + \sum_i V_i^{2}
+ I`, with the $`\pi_i` the fiber momenta and the $`V_i` the fiber realization
of the advection field, all symmetric on a common dense domain. Because both
families enter squared, the quadratic form of $`n` is
$`\sum_i\|\pi_i v\|^{2} + \sum_i\|V_i v\|^{2} + \|v\|^{2}`, so $`n \ge I` — the
strict positivity that a comparison operator must have. In the momentum
representation, where the constituents are diagonal with arbitrary real symbols,
$`n` is essentially self-adjoint on the finite-mode domain and is genuinely
unbounded whenever its symbols are; second-quantizing that realization gives a
Fock-space comparison operator that is essentially self-adjoint on the
finite-particle domain, and it inherits `N̂ ≥ I` from the sectors.
:::

```
#check @BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData
#check @BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData.comparison
#check @BookProof.NavierStokesFlow.FarisLavineLift.ComparisonData.comparison_ge_norm_sq
#check @BookProof.NavierStokesFlow.FarisLavineLift.diagComparison_hasZeroDeficiencyOn
#check @BookProof.NavierStokesFlow.FarisLavineLift.diagComparison_not_bounded
#check @BookProof.NavierStokesFlow.SecondQuant.fockComparison_hasZeroDeficiencyOn
#check @BookProof.NavierStokesFlow.SecondQuant.fockOp_ge_norm_sq
#check @BookProof.NavierStokesFlow.SecondQuant.fockComparison_ge_norm_sq
#check @BookProof.NavierStokesFlow.SecondQuant.fockComparison_domain_ne_top
```

:::paragraph
The two Faris–Lavine bounds then have to survive the lift, and here the two
halves behave differently. The form-commutator bound does lift as expected: the
commutator of the sums is the sum of the commutators once distinct particles
commute, and summing $`|\langle v, [h_k, n_k] v\rangle| \le c_2 \langle v, n_k
v\rangle` over the particles gives the same bound for the totals — stated with a
modulus on the left, since for symmetric constituents the commutator expectation
is purely imaginary and its real part carries no information. The operator bound
does *not* lift by the triangle inequality alone: the informal chain
$`\|\sum_k h_k v\| \le \sum_k\|h_k v\| \le c_1\sum_k\|n_k v\| \le c_1\|\sum_k n_k
v\|` uses a last step that is false, and two two-by-two operator pairs with
$`\|h_k x\| \le \|n_k x\|` for every $`x` but $`\|(n_0+n_1)v\| <
\|(h_0+h_1)v\|` witness the failure. What does lift is the pairwise-dominated
form of the hypothesis, and with the two bounds in that shape the Faris–Lavine
criterion — taken as a named hypothesis, not an axiom — yields vanishing adjoint
deficiency for the second-quantized Hamiltonian on the finite-particle domain.
Essential self-adjointness of the *continuum* Navier–Stokes Hamiltonian is not
claimed; the operator-flow global existence would follow from it by Stone's
theorem, while classical global existence is a separate, deliberately out-of-
scope statement.
:::

```
#check @BookProof.NavierStokesFlow.FarisLavineLift.norm_sum_le_of_pairwise
#check @BookProof.NavierStokesFlow.FarisLavineLift.not_forall_norm_sum_le_of_pointwise
#check @BookProof.NavierStokesFlow.FarisLavineLift.norm_inner_commutator_sum_le
#check @BookProof.NavierStokesFlow.SecondQuant.fockOp_norm_le_of_sectors
#check @BookProof.NavierStokesFlow.SecondQuant.fockOp_norm_inner_le_of_sectors
#check @BookProof.NavierStokesFlow.SecondQuant.fockOp_hasZeroDeficiencyOn_of_farisLavine
```

:::paragraph
That last statement still carries the criterion as a hypothesis, and in the shape
it is stated there — a relative bound plus a commutator bound, with no positivity
of $`N` and no surjectivity of $`N+1` — the criterion is in fact refutable, by the
limit-circle Jacobi operator. The remedy is to supply exactly the input the
Faris–Lavine proof uses, and this the momentum representation does provide. Take
the comparison operator on its *maximal* domain in $`\ell^{2}`: multiplication by
the symbol $`\sigma`, defined on every state whose product with $`\sigma` is
again square summable. For a non-negative symbol that operator is symmetric,
positive, $`N+1` maps the maximal domain onto the whole space because
$`(\sigma+1)^{-1}` is a contraction, and the finite-mode states — the
momentum-space stand-in for $`C_c^\infty` — are an operator core, since the
truncations of a state converge to it in the graph norm. That package is the
Ikebe–Kato-type input, and it is proved, not assumed: for a non-negative symbol,
multiplication by $`\sigma` is essentially self-adjoint already on the finite-mode
core, and self-adjoint on its maximal domain.
:::

```
#check @BookProof.NavierStokesFlow.IkebeKato.maxDom
#check @BookProof.NavierStokesFlow.IkebeKato.diagMax
#check @BookProof.NavierStokesFlow.IkebeKato.diagMax_quadForm_ge_norm_sq
#check @BookProof.NavierStokesFlow.IkebeKato.diagMax_add_one_surjective
#check @BookProof.NavierStokesFlow.IkebeKato.exists_finiteModes_graph_approx
#check @BookProof.NavierStokesFlow.IkebeKato.diagMax_essentiallySelfAdjointOn
#check @BookProof.NavierStokesFlow.IkebeKato.ikebeKato_momentum
```

:::paragraph
With that input the Faris–Lavine theorem of the criterion chapter applies with no
hypothesis left over: any symmetric Hamiltonian on the maximal domain which is
relatively bounded by $`N` and whose form commutator with $`N` is dominated by
$`N` is essentially self-adjoint on the finite-mode core. Specialised to the
Navier–Stokes symbol $`\sigma(k)=\sum_i p_i(k)^2+\sum_i q_i(k)^2+1` this is the
one-particle statement, and the restriction of the maximal-domain operator to the
core is literally the comparison operator $`n=\sum_i\pi_i^2+\sum_i V_i^2+I` of the
fiber. In the occupation-number representation the bosonic Fock space over the
fiber is $`\ell^{2}` over the configurations $`\alpha:\mathbb{N}\to_{f}\mathbb{N}`
and $`\hat N = d\Gamma(n)+I` is again a multiplication operator, by the total
energy $`\Sigma(\alpha)=\sum_k \alpha(k)\,n(k)+1`; so the same theorem gives
essential self-adjointness of the second-quantized Navier–Stokes Hamiltonian on
the finite-particle, finite-mode core. What remains hypothetical are exactly the
two Faris–Lavine inequalities for the Hamiltonian itself; they are not vacuous —
an unbounded Hamiltonian $`N+B` with a rank-two perturbation satisfies both while
its commutator with $`N` is non-zero. Essential self-adjointness of the
*continuum* generator, and global existence, are still not claimed.
:::

```
#check @BookProof.NavierStokesFlow.IkebeKato.essentiallySelfAdjointOn_finiteModes_of_farisLavine_bounds
#check @BookProof.NavierStokesFlow.MomentumEsa.nsComparison_restrict_eq
#check @BookProof.NavierStokesFlow.MomentumEsa.nsComparison_ikebeKato
#check @BookProof.NavierStokesFlow.MomentumEsa.ns_hamiltonian_essentiallySelfAdjointOn_core
#check @BookProof.NavierStokesFlow.MomentumEsa.fockSymbol
#check @BookProof.NavierStokesFlow.MomentumEsa.fockSymbol_add
#check @BookProof.NavierStokesFlow.MomentumEsa.fockComparison_ikebeKato
#check @BookProof.NavierStokesFlow.MomentumEsa.navierStokes_fock_hamiltonian_essentiallySelfAdjointOn_core
#check @BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_essentiallySelfAdjointOn_core
#check @BookProof.NavierStokesFlow.MomentumPerturbation.pertHam_not_bounded
#check @BookProof.NavierStokesFlow.MomentumPerturbation.exists_commForm_ne_zero
```

# Summary

The free-field thread replaces the nonexistent infinite-dimensional Lebesgue measure
with the rotation-invariant Gaussian, pushes it to a uniform measure on the sphere,
and then applies the Born rule to parametrize the simplex — all the while the gauge
fibers keep track of the invisible phase. The two negative results (no Lebesgue
measure; positive-measure partitions are countable) are not obstacles but the precise
statements that make the construction both necessary and well-defined.

The same free-field parametrization carries the Navier–Stokes thread: the velocity
field and its derivatives are independent canonical degrees of freedom, and on a
finite truncation the Weyl-symmetrized Hamiltonian has a complete, norm-preserving
flow, a unique global solution to the Cauchy problem, and a nilpotent BRST
constraint — with the honest boundary drawn at the continuum operator, whose
essential self-adjointness is exactly where the Faris–Lavine commutator criterion
(taken as a named hypothesis) sits. The *classical* existence/uniqueness claim of
`book.tex` (the Clay regularity problem) is not carried by any theorem here — the
operator-flow global existence would follow from ESA by Stone's theorem, but the
ESA of the continuum operator is itself the open step; see
`Book/YangMillsQuantization.lean` for the pointer to this formalized subset.
