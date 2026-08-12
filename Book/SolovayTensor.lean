import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The Solovay–Kopperman Tensor Product" =>
%%%
tag := "solovay-tensor"
%%%

# The Question

:::paragraph
The Introduction posed a concrete open problem. Engineering needs a probability
space over real functions of real variables, but:
:::

:::paragraph
"no one has found yet a systematic way to define a separable probability space with
an arbitrary probability measure over real functions of real variables (and
infinite-dimensional spaces in general)."
:::

:::paragraph
The difficulty is the infinite-dimensional part. A separable space is one whose
elements can be approximated by a countable set; a non-separable space has elements
that "cannot be approximated by a finite set of elements, up to an arbitrarily small
error" — and then they cannot be distinguished, named, or computed. So we want a
space that is infinite-dimensional (to carry a field, or a trajectory, or a
wave-function) yet still separable (so its elements remain approximable), and on
which we may still choose a probability measure.
:::

:::paragraph
The manuscript also repeatedly forms *tensor products of sample spaces*. A joint
probability density lives on a product $`X \times Y`; the prior wave-function can be
"redefined as a tensor product of two Fock-spaces"; and often "we are interested in a
tensor product of sample spaces, some of which have finite degrees of freedom," for
instance $`\mathbb{Z}_2^n \times \mathbb{R}^m`. The construction below answers the
Introduction's problem precisely by building such a tensor product: a
*finite-dimensional* factor that carries an *arbitrary* probability law, tensored
with a *separable infinite-dimensional* factor that carries a *forced* law.
:::

:::paragraph
A simpler finite-dimensional instance of the same problem arises in
{ref "double-slit"}[the double-slit chapter]: given only the final screen position,
can one reconstruct the intermediate "which slit" trajectory? The
Aharonov–Bergmann–Lebowitz (ABL) two-state reconstruction answers this affirmatively.
The reconstruction is a finite-phase-space version of the same idea: a quantum
trajectory can be measured directly only at its final time, but the intermediate
instants can be recovered from the statistics of runs that ended in a chosen final
outcome — using probabilities conditional on the final state and the same quantum
time-evolution.
:::

# The Three-Instant ABL Reconstruction

:::paragraph
Model three instants — initial, intermediate, final — on a finite phase space. A unit
initial wave-function $`\Psi` is evolved by a unitary $`U` to the intermediate time,
where a measurement in the standard basis yields outcome $`a` with the Born
probability and *collapses* the state to $`e_a`:
:::

```
#check @midProb
```

:::paragraph
The collapsed state is then evolved by a unitary $`V` to the final time, where outcome
$`f` occurs with probability
:::

```
#check @transProb
```

:::paragraph
Both are genuine probabilities — non-negative, and each sums to one over its outcomes:
:::

```
#check @midProb_nonneg
#check @midProb_sum
#check @transProb_sum
```

# The Joint and Marginal Laws

:::paragraph
The joint law of the intermediate outcome $`a` and the final outcome $`f` is the
product of the two Born factors:
:::

```
#check @jointProb
```

:::paragraph
Summing over the intermediate outcome gives the marginal law of the final outcome:
:::

```
#check @finalProb
```

:::paragraph
The collapsed three-instant process is a genuine probability law: the marginal final
probabilities sum to one. This uses only the unitarity of $`U` and $`V` and the
normalization $`\|\Psi\| = 1`:
:::

```
#check @finalProb_total
```

# Post-Selection: the Reconstruction Formula

:::paragraph
Now condition on the final outcome $`f`. The *post-selected* law of the intermediate
outcome — the probability that the trajectory passed through $`a`, given that it ended
at $`f` — is the conditional probability
:::

$$`\mathrm{condProb}(f, a) = \frac{\mathrm{jointProb}(f, a)}{\mathrm{finalProb}(f)}.`

```
#check @condProb
#check @condProb_nonneg
```

:::paragraph
For each fixed final outcome $`f`, this is again a probability distribution over the
intermediate outcomes:
:::

```
#check @condProb_sum
```

:::paragraph
This is the reconstruction: although $`a` was not recorded, its conditional
distribution is determined by the final outcome and the same unitary evolution, and it
is a honest probability law.
:::

# Consistency of the Reconstruction

:::paragraph
The reconstruction does not depend on which final outcome one post-selects. Summing
the post-selected joint law over *all* final outcomes recovers the original
intermediate Born distribution:
:::

```
#check @jointProb_sum_final_eq_midProb
```

:::paragraph
So the intermediate statistics are stable: marginalizing the reconstructed joint law
back over the final outcomes returns exactly the Born probabilities one would have
measured directly at the intermediate time. The post-selection adds information about
individual runs without distorting the ensemble.
:::

# The Solovay–Kopperman Tensor Product

:::paragraph
The ABL reconstruction is a finite-phase-space instance of the general problem. The
general construction — the Solovay–Kopperman tensor product — answers the
Introduction's question directly: it is a systematic separable probability space
carrying an arbitrary law on a finite part and a controlled (forced) law on an
infinite part.
:::

# The Two Factors

:::paragraph
The total sample space splits as a finite *head* times an infinite *tail*:
:::

```
#check @InnerSpace
#check @InnerHead
#check @InnerTail
```

:::paragraph
The head $`\mathrm{InnerHead}\,N = \mathrm{Fin}\,N \to \mathbb{R} \cong \mathbb{R}^N`$
is an ordinary finite-dimensional Euclidean Hilbert space. The tail
$`\mathrm{InnerTail}` is the Kopperman *substrate*, the standard separable real
Hilbert space $`L^2([0,1])`. Its separability is the topological precondition for
everything that follows, and it is verified directly:
:::

```
#check @kopperman_substrate_separable
#check @substrate_decidable_skeleton
```

:::paragraph
Separable, but not small: the tail carries a *countable* orthonormal family — the
normalized indicators of the disjoint intervals $`(1/(n+2),\,1/(n+1)]` — and
therefore has infinitely many independent directions. The head–tail split is not a
finite-dimensional artefact:
:::

```
#check @BookProof.ChapterSolovayTailDimension.substrateBasisVector_orthonormal
#check @BookProof.ChapterSolovayTailDimension.substrate_infinite_dimensional
#check @BookProof.ChapterSolovayTailDimension.tail_infinite_dimensional
```

:::paragraph
Thus the tail is infinite-dimensional but *separable*: it possesses a countable
dense skeleton of computable approximants. This is exactly the property the
Introduction asked for. The finite head is the part we _know_; the separable infinite
tail is the part we are _uncertain_ about.
:::

# Decidable Languages Close Under Tensor Product

:::paragraph
A *language* here is an explicit Boolean decision procedure: a classifier
$`\mathrm{decide} : \alpha \to \mathrm{Bool}`. The tensor product of two languages is
conjunction on pairs — a point of the product carrier is accepted exactly when both
components accept it:
:::

```
#check @tensor_decide_apply
```

:::paragraph
Because a conjunction of two decidable propositions is decidable, membership in the
tensor language is decidable for every point of the product carrier:
:::

```
#check @tensor_language_membership_decidable
```

:::paragraph
This is the first half of the author's goal: *the tensor product of two decidable
languages is a decidable language.* The same closure holds for the
Hilbert-space languages used in this book. The "cylindrical" observables — those that
depend only on the finite head — form a decidable language, because the head is
finite-dimensional and hence Tarski-decidable. A tensor product of two such
finite-head observables is again a finite-head observable on the combined head:
:::

```
#check @tensorHeadObservable_dependsOnlyOnHead
#check @tensor_language_decidable
```

:::paragraph
The combined head is split into its two finite blocks by an explicit equivalence, so
"tensor product of languages" and "concatenation of finite heads" are the same
operation:
:::

```
#check @headSumEquiv
```

# The Tensor-Product Hilbert Space

:::paragraph
The tensor product of the two factors is the total space
$`\mathrm{InnerSpace}\,N = \mathrm{InnerHead}\,N \times \mathrm{InnerTail}`, and its
Hilbert completion is the *Solovay–Hilbert space*:
:::

```
#check @SolovayHilbertSpace
```

:::paragraph
The infinite tail itself tensors with a copy of itself back into a single tail: two
infinite Gaussian coordinate sequences interleave into one, and the product Mehler
law is carried exactly to the Mehler law. This is the measure-theoretic content of
$`\Gamma \otimes \Gamma \cong \Gamma` for the infinite factor:
:::

```
#check @tailTensorEquiv
#check @tailTensorEquiv_map
```

:::paragraph
The embedding of a wave-function into the completed space preserves the inner
product, so the completion is a genuine Hilbert-space tensor product rather than a
mere product of sets:
:::

```
#check @toSolovay_inner
```

:::paragraph
In the coordinate model the tensor identification is available in full. Two Solovay
systems combine into one — the finite heads concatenate and the two Mehler tails
interleave — and the combination carries the *product* of the two state laws to the
state law of the combined system. That measure-preserving isomorphism induces a
unitary of the corresponding $`L^2` spaces, which is the Hilbert-space form of
$`H(N_1) \otimes H(N_2) \cong H(N_1+N_2)`:
:::

```
#check @BookProof.ChapterSolovayHilbertTensor.solovayTensorEquiv
#check @BookProof.ChapterSolovayHilbertTensor.solovayTensorEquiv_map
#check @BookProof.ChapterSolovayHilbertTensor.solovayTensorUnitary
```

:::paragraph
And the elementary tensors behave as elementary tensors must: a product
$`f(x)g(y)` of two square-integrable factors is square-integrable for the product
law, and the inner product of two such pure tensors is the product of the two
inner products.
:::

```
#check @BookProof.ChapterSolovayHilbertTensor.tensorLp
#check @BookProof.ChapterSolovayHilbertTensor.inner_tensorLp
```

:::paragraph
The completeness half holds too, for any two finite laws: the closed linear span
of the pure tensors is *all* of $`L^2(\mu \otimes \nu)`. The proof is the classical
π–λ argument — the indicator of a measurable rectangle $`s \times t` is the pure
tensor $`1_s \otimes 1_t`; the measurable sets whose indicator lies in the closed
span contain the rectangles and are stable under complements and countable
disjoint unions, hence are all of them; and indicators generate $`L^2`. Written as
an approximation statement, this is *separation of variables*: every
square-integrable function of two variables is an $`L^2`-limit of finite sums
$`\sum_k f_k(x)g_k(y)`. Together with the multiplicativity of the inner product on
pure tensors, it says that $`L^2(\mu \otimes \nu)` *is* the Hilbert tensor product
of $`L^2(\mu)` and $`L^2(\nu)` — a statement one can make here even though the
library has no Hilbert tensor product to name:
:::

```
#check @BookProof.ChapterTensorCompleteness.pureTensors
#check @BookProof.ChapterTensorCompleteness.indicator_mem_tensorSpan
#check @BookProof.ChapterTensorCompleteness.tensorSpan_eq_top
#check @BookProof.ChapterTensorCompleteness.pureTensors_dense
#check @BookProof.ChapterTensorCompleteness.exists_tensor_approx
```

:::paragraph
The practical corollary is the *product basis*. Writing $`u \otimes v` for the pure
tensor of two $`L^2` elements, the inner product multiplies and the norm
multiplies, the operation is bilinear and continuous in each slot; so the products
$`e_i \otimes f_j` of two orthonormal families are orthonormal, and if both
families are total then so is the family of products. A basis of the two-factor
state space is therefore obtained by multiplying a basis of each factor — the
familiar bookkeeping of a composite quantum system:
:::

```
#check @BookProof.ChapterTensorCompleteness.tensorOf
#check @BookProof.ChapterTensorCompleteness.inner_tensorOf
#check @BookProof.ChapterTensorCompleteness.norm_tensorOf
#check @BookProof.ChapterTensorCompleteness.orthonormal_tensorOf
#check @BookProof.ChapterTensorCompleteness.tensorFamily_span_eq_top
```

:::paragraph
Orthonormality and totality can be packaged into a single object. Given a Hilbert
basis $`(b_i)` of $`L^2(\mu)` and a Hilbert basis $`(c_j)` of $`L^2(\nu)`, the
products $`b_i \otimes c_j`, indexed by pairs, *are* a Hilbert basis of
$`L^2(\mu \otimes \nu)`. Its coefficients are the two-variable Fourier
coefficients $`\langle b_i \otimes c_j, F\rangle`, every square-integrable
function of two variables is the unconditional sum of its components, and
Parseval holds in the product form
$`\sum_{i,j} |\langle b_i \otimes c_j, F\rangle|^2 = \|F\|^2`. This is the
bookkeeping a composite quantum system actually uses:
:::

```
#check @BookProof.ChapterTensorCompleteness.tensorHilbertBasis
#check @BookProof.ChapterTensorCompleteness.coe_tensorHilbertBasis
#check @BookProof.ChapterTensorCompleteness.tensorHilbertBasis_repr_apply
#check @BookProof.ChapterTensorCompleteness.hasSum_tensorHilbertBasis
#check @BookProof.ChapterTensorCompleteness.hasSum_sq_norm_inner_tensorHilbertBasis
```

:::paragraph
The decisive simplification is the *decoupling theorem*: because the cylindrical
wave-functions depend only on the finite head, and the tail measure is an independent
probability measure, the $`L^2` inner product over the infinite-dimensional total
space collapses exactly to a finite-dimensional integral over the head
$`\mathbb{R}^N`:
:::

```
#check @inner_reduces_to_head
```

:::paragraph
This is the dimensional reduction that makes the whole construction _decidable_: an
a-priori infinite-dimensional computation reduces to a finite Tarski-decidable
integral. It is the formal version of the manuscript's claim that probabilities let
us relate arbitrarily complex random events to standard, intuitive ones.
:::

# An Arbitrary Law on the Finite Part

:::paragraph
On the finite head we may choose *any* probability law. Given any probability
measure $`\mathrm{headDist}` on $`\mathbb{R}^N`, the product with the tail law is a
probability measure on the total space, and its finite marginal is exactly the law we
chose:
:::

```
#check @stateMeasure_isProbability
#check @stateMeasure_finite_marginal
```

:::paragraph
Put together, that is precisely the Introduction's question answered: a separable
probability space, over an infinite-dimensional carrier, on which the law of the
finite part may be chosen arbitrarily while the infinite part carries the Mehler
law — in the coordinate model and in the abstract substrate model alike:
:::

```
#check @BookProof.ChapterSolovaySeparableExistence.exists_separable_prob_with_arbitrary_finite_law
#check @BookProof.ChapterSolovaySeparableExistence.exists_separable_prob_with_arbitrary_finite_law_substrate
#check @BookProof.ChapterSolovaySeparableExistence.separable_carrier_tail_infinite_dimensional
```

:::paragraph
On the finite part the wave-function parametrization is always available: any
finite joint law is the squared modulus of a wave-function, and taking the
marginal of the Born probabilities gives the marginal of the law. And any joint
law whose second factor is standard Borel factors as its own marginal composed
with a Markov kernel — the disintegration used to condition without rewriting
history:
:::

```
#check @BookProof.ChapterSolovaySeparableExistence.joint_prob_has_wavefunction
#check @BookProof.ChapterSolovaySeparableExistence.joint_prob_has_wavefunction_prod
#check @BookProof.ChapterSolovaySeparableExistence.prod_disintegration
```

:::paragraph
The same statement in the explicit coordinate model, where the tail is a countable
product of standard Gaussians:
:::

```
#check @coordinateStateMeasure
#check @coordinateStateMeasure_isProbability
```

:::paragraph
This is the finite-dimensional freedom the author wants: *our knowledge of the
finite-dimensional part is an arbitrary probability distribution.* Nothing
constrains it; it is the part we are free to choose.
:::

# Only the Mehler Measure on the Infinite Part

:::paragraph
The infinite tail is different. The Kopperman language is *cylindrical*: it can
query only finitely many coordinates at a time. Consequently it cannot distinguish
two tail points that agree on every finite set of coordinates — no individual element
of the infinite-dimensional Hilbert space can be named or singled out. (This is the
same mechanism as {ref "pa-free-chapter"}[Completeness without Peano Arithmetic]:
adding a named infinite element to the language would destroy decidability.)
:::

:::paragraph
A probability law on the tail that respects this blindness must be *atomless* (no
single state carries mass) and *invariant* under the symmetries the language can
express. The selected Mehler/Kopperman prior has precisely these admissibility
properties:
:::

```
#check @TailPriorAdmissible
#check @only_mehler_on_tail
```

:::paragraph
Concretely, the tail prior is atomless, and it is invariant under every admitted
finite orthogonal symmetry:
:::

```
#check @tailMeasure_singleton
#check @mehler_invariant_under_finite_orthogonal
```

:::paragraph
And it really lives on the infinite-dimensional sphere: the normalized empirical
squared norm of the first $`k` coordinates converges to $`1` almost surely
(Poincaré–Borel / the strong law), which is Mehler's 1866 limit of the uniform
measure on the high-dimensional sphere:
:::

```
#check @mehler_concentrates_on_unit_sphere
```

:::paragraph
Mehler's 1866 statement is not a slogan; it is a genuine limit, and it is the
single most important structural fact of this part. On the surface of a $`k`-sphere
the rotation-invariant (uniform) area element factorizes into single-coordinate
weights $`(1-x^2)^{(\alpha-1)/2}` — exactly the *Gegenbauer* weight of order
$`\alpha`. The uniform hyperspherical measure is therefore the natural *prior*: it
assigns equal weight to every direction, expressing that we have no information.
Rescale the coordinate $`x \mapsto \sqrt{2/\alpha}\,x` and let
$`\alpha \to \infty`. The single-coordinate hyperspherical weight tends to the
Gaussian weight $`e^{-x^2}`:
:::

$$
`\lim_{\alpha\to\infty}\Bigl(1 - \tfrac{x^2}{\alpha}\Bigr)^{\alpha-1/2} = e^{-x^2}.`

:::paragraph
At the same time the Gegenbauer polynomials $`C_n^{(\alpha/2)}` (orthogonal with
respect to the uniform measure, and defining the hyperspherical harmonics) become
the Hermite polynomials $`H_n/n!` (with the physicists' $`H_n` from the recurrence
$`H_0 = 1, H_1 = 2x, H_{n+2} = 2x H_{n+1} - 2(n+1)H_n`), in the scaled limit
:::

$$
`\lim_{\alpha\to\infty}\Bigl(\tfrac{\alpha}{2}\Bigr)^{-n/2}
  C_n^{(\alpha/2)}\Bigl(\sqrt{\tfrac{2}{\alpha}}\,x\Bigr)
   = \frac{H_n(x)}{n!}.`

:::paragraph
And the normalizations converge consistently: the (squared) Gegenbauer
normalization integral against the hyperspherical weight tends to the Hermite
normalization integral against the Gaussian weight, $`\int_\mathbb{R}[H_n(x)/n!]^2
e^{-x^2}dx = \sqrt{\pi}\,2^n/n!`. The verified statements live in
`BookProof.PhysHSGaussian`:
:::

```
#check @PhysHSGaussian.physHermite
#check @PhysHSGaussian.gegenbauer
#check @PhysHSGaussian.gegenbauerScaled
#check @PhysHSGaussian.gegenbauerScaled_tendsto_hermite
#check @PhysHSGaussian.weight_tendsto_gaussian
#check @PhysHSGaussian.hermite_normalization
#check @PhysHSGaussian.normalization_tendsto
#check @PhysHSGaussian.gaussian_concentration_sphere
```

:::paragraph
This is the precise sense in which the uniform (hyperspherical) prior and the
Gaussian (Fock) vacuum coincide, and in which the orthogonal excitations of the Fock
space are the images of the hyperspherical harmonics. The dictionary is complete:
:::

| Finite hypersphere ($`\alpha < \infty`) | Infinite-dimensional limit (Fock) |
| :--- | :--- |
| uniform surface measure $`d\sigma` | Gaussian measure $`e^{-x^2}dx` |
| Gegenbauer weight $`(1-x^2)^{(\alpha-1)/2}` | Gaussian weight $`e^{-x^2}` |
| Gegenbauer polynomials $`C_n^{(\alpha/2)}` | Hermite polynomials $`H_n/n!` |
| hyperspherical harmonics | number states $`\ket{n}` |
| uniform "no-information" prior | Gaussian source qsample $`\Psi_0 = \ket{0}` |

:::paragraph
So the tail prior that the blind language is forced to adopt is not merely *a*
rotation-invariant measure: it is the infinite-dimensional *limit* of the family of
uniform hyperspherical priors, with the Fock number states as the limits of the
hyperspherical harmonics. This is why the free-field prior of
{ref "free-field"}[the free-field chapter] is the same object, and why the Gaussian
source qsample $`\sqrt{p_0}` of a flow model coincides with the Fock vacuum. The
finite-hypersphere-to-Fock dictionary is the structural backbone of this part and of
the whole book.
:::

:::paragraph
In the coordinate model the forcing is explicit. The language sees only finite
coordinate sets, and restriction to any finite set has the corresponding finite
product Gaussian law:
:::

```
#check @finiteCoordinateMarginal
```

:::paragraph
So the only data the language can observe is the family of finite-dimensional
marginals, and a probability measure on $`\mathbb{N} \to \mathbb{R}` is determined by
its finite marginals. The intended conclusion — that the Mehler measure is the
_unique_ probability law whose every finite marginal is the standard Gaussian product,
and hence the _only_ law the blind language can use — is now proved: cylinder sets
form a generating π-system, so a projective limit of finite measures is unique.
:::

```
#check @BookProof.ChapterMehlerUniqueness.mehler_unique_by_finite_marginals
#check @BookProof.ChapterMehlerUniqueness.mehler_characterization
#check @BookProof.ChapterMehlerUniqueness.language_blind_implies_mehler
#check @BookProof.ChapterMehlerUniqueness.solovay_kopperman_probability_classification
```

:::paragraph
The other half is admissibility: the Mehler law is a probability measure, atomless,
and invariant. The two halves together give the author's classification:
:::

```
#check @head_vs_tail_admissibility
```

:::paragraph
The invariance half is now available in *concrete coordinates*, not only at the
abstract measure-preserving interface. The characteristic function of the standard
$`k`-dimensional Gaussian is $`\exp(-\|t\|^2/2)`, a function of the norm alone, so
the finite Gaussian head is invariant under the whole orthogonal group $`O(k)`; and
rotating the first $`k` coordinates of the infinite tail therefore leaves the Mehler
law unchanged:
:::

```
#check @BookProof.ChapterMehlerOrthogonalInvariance.charFun_stdGaussianEuclidean
#check @BookProof.ChapterMehlerOrthogonalInvariance.stdGaussianEuclidean_map_isometry
#check @BookProof.ChapterMehlerOrthogonalInvariance.gaussianHead_map_orthogonal
#check @BookProof.ChapterMehlerOrthogonalInvariance.coordinateTailMeasure_map_headRotation
```

:::paragraph
*Heads admit an arbitrary law; the tail admits the Mehler law.* That single
statement is the probabilistic content of the Solovay–Kopperman tensor product.
:::

# The Cross-Dimensional Inner Product

:::paragraph
Because the Mehler tail *splits* — the first $`k` Gaussian coordinates separate off
as an independent finite Gaussian block, leaving a fresh copy of the tail — we may
enlarge the finite head by adjoining $`k` tail coordinates:
:::

```
#check @tailSplitEquiv
#check @enlargeEquiv
```

:::paragraph
This makes the inner product well-defined *across dimensions*: an element with
$`N` head-coordinates and an element with $`N+k` head-coordinates can be compared
after padding the smaller one with $`k` fresh Gaussian coordinates, and the result
does not depend on the padding, because the added coordinates integrate to $`1`. The
finite dimensions "match" precisely because the Mehler measure is a product. The
measure-preservation of the coordinate tail-split — the theorem that splitting off
the first $`k` coordinates carries the Mehler law to the product of a finite Gaussian
head with a fresh copy of the tail — is proved:
:::

```
#check @tailSplitEquiv_map
```

:::paragraph
The cross-dimensional statement is now a theorem, not just an assertion: the
enlargement map $`N \mapsto N+k` is a *measure-preserving isomorphism* of the
corresponding state spaces, so it is a genuine embedding of the $`N`-dimensional
coordinate model into the $`(N+k)`-dimensional one. Consequently every expectation,
and in particular the $`L^2` inner product of two wave-functions, is unchanged when
it is computed after enlarging the head — the value does not depend on which head
dimension the computation is performed in. This is the manuscript's "the inner
product is well defined across head dimensions," made precise:
:::

```
#check @BookProof.ChapterSolovayCrossDim.cross_dim_embedding
#check @BookProof.ChapterSolovayCrossDim.integral_cross_dim_well_defined
#check @BookProof.ChapterSolovayCrossDim.inner_cross_dim_well_defined
#check @BookProof.ChapterSolovayCrossDim.lintegral_cross_dim_well_defined
#check @BookProof.ChapterSolovayCrossDim.cross_dim_isProbability
```

# What Is Proved and What Is Planned

:::paragraph
This edition separates the verified layer from the open one.
:::

:::paragraph
*Verified.* The ABL three-instant reconstruction (midProb, transProb, jointProb,
condProb, consistency); the two factors and their separability; closure of decidable
languages under tensor product; the tensor-product Hilbert space and the decoupling
theorem; the arbitrary finite-head law and its marginal; the admissibility of the
Mehler tail (probability, atomlessness, invariance, concentration on the sphere);
and the self-interleaving of the infinite tail. Every theorem cited above is
`sorry`-free.
:::

:::paragraph
*Newly verified.* The two statements previously quarantined as planned are now
theorems: the *uniqueness* of the Mehler tail law from its finite marginals
(`mehler_unique_by_finite_marginals`, the forcing half of "only the Mehler
measure") and the *measure-preservation* of the coordinate tail-split
(`tailSplitEquiv_map`), from which the cross-dimensional inner product follows —
together with the coordinate-level orthogonal invariance of the Mehler law cited
above.
:::

# Why This Matters Here

:::paragraph
The ABL reconstruction shows that even when only the final outcome is known, the
intermediate trajectory can be recovered as a probability law — a finite-phase-space
instance of the general principle. The Solovay–Kopperman tensor product extends
this to the infinite-dimensional case: it is a systematic separable probability
space carrying an arbitrary law on a finite part and a controlled (forced) law on an
infinite part. Together they explain the recurring tensor products of the manuscript
— a joint density on $`X \times Y`, a prior as a tensor product of two
Fock-spaces, a sample space $`\mathbb{Z}_2^n \times \mathbb{R}^m` — as instances of a
single principle: tensor a finite, freely-chosen factor with a separable infinite
factor whose law is forced by the very fact that the language cannot distinguish its
elements. Probability on the infinite part is not a choice; it is the Mehler measure.
:::

:::paragraph
This also identifies the construction as the *single exception* to the slogan
"there are no non-informative priors." On a general continuous space a uniform prior
stops being uniform under a change of coordinates
({ref "sequential-bayes"}[non-informativeness is coordinate-dependent]); here the
cylindrical language admits no such change — arbitrary unitary transforms are not
defined on the non-metrically-complete restricted space — so the Mehler prior on the
infinite-dimensional hypersphere stays uniform under every symmetry the language can
express. It is uniform not by a parametrization-dependent trick (the finite case) but
intrinsically, because the offending reparametrizations are absent from the language.
:::
