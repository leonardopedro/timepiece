import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Euclidean Moments and Reflection Positivity at the Regulator" =>
%%%
tag := "euclidean-moments"
%%%

:::paragraph
The continuum-limit programme (`cftproof.md`) builds the Euclidean reconstruction in
stages. _C0_ fixes the manifest of assumptions, _C1_ constructs the finite-cutoff
massive Gaussian control in Mehler coordinates and proves its reflection positivity for
bounded cylinder observables, and _C2_ asks for the *interacting* regulated state together
with its Euclidean dictionary. This chapter documents the part of _C2_ that is formalized:
the Euclidean moment hierarchy, the separated-time two-point functions, and reflection
positivity of the reflected (Osterwalder–Schrader) form at the regulator. The interacting
closure is not part of what is proved here, and the last section says exactly where the
boundary lies.
:::

:::paragraph
The mathematical content is small and worth stating before any code. Fix a bounded
operator $`K` on a Hilbert space and a unit reference vector $`\Omega`. The Euclidean
evolution is $`e^{-hK}`; a *word* of insertions $`(\Delta_1, A_1), \dots, (\Delta_n, A_n)`
produces the operator product
$`A\,e^{-\Delta_1 K} A_1 \cdots e^{-\Delta_n K} A_n`, and its *moment* is that operator
sandwiched between $`\Omega`. This is the finite-mode regulator: every operator is bounded,
every moment is a finite scalar, and no domain question arises. The interesting structure is
not the existence of the moments but their *positivity* under time reflection.
:::

# The Moment Hierarchy

The Euclidean evolution and its semigroup law are the only dynamics the hierarchy needs.

```
BookProof.OSReconstruction.euclidEvol K h = NormedSpace.exp ((-(h : ℂ)) • K)
BookProof.OSReconstruction.euclidEvol_zero   : euclidEvol K 0 = 1
BookProof.OSReconstruction.euclidEvol_add  : euclidEvol K (s + t) = euclidEvol K s * euclidEvol K t
```

Words are ordered products, and the _extension convention_ says that splitting a word at
a gap composes the two operator products — appending a word is composing with the operator
of the appended word.

```
BookProof.OSReconstruction.euclidWord_append :
  euclidWord K A (l₁ ++ l₂) = euclidWord K (euclidWord K A l₁) l₂
```

The empty word and the normalization of the reference vector are the base case:

```
BookProof.OSReconstruction.euclidMoment_nil      : euclidMoment K Ω A [] = ⟪Ω, A Ω⟫
BookProof.OSReconstruction.euclidMoment_one_nil  : ‖Ω‖ = 1 → euclidMoment K Ω 1 [] = 1
```

# Separated-Time Two-Point Functions

The two-point function of the hierarchy inserts $`A` at time $`0` and $`B` at the later
time $`h`:

```
BookProof.OSReconstruction.twoPoint K Ω A B h = euclidMoment K Ω A [(h, B)]
BookProof.OSReconstruction.twoPoint_eq        : twoPoint K Ω A B h = ⟪Ω, A (euclidEvol K h (B Ω))⟫
BookProof.OSReconstruction.twoPoint_zero      : twoPoint K Ω A B 0 = ⟪Ω, A (B Ω)⟫
```

At zero separation the observable paired with its adjoint gives the square that all of the
positivity is built on:

```
BookProof.OSReconstruction.twoPoint_adjoint_zero :
  twoPoint K Ω (ContinuousLinearMap.adjoint A) A 0 = ((‖A Ω‖ ^ 2 : ℝ) : ℂ)
```

# Reflection Positivity of the Reflected Form

Time reflection sends an insertion of $`A_i` at time $`+s_i` to an insertion of $`A_i^\dagger`
at time $`-s_i`. Pairing the reflected family with the original family gives the
_reflected form_

```
reflectedForm K Ω f  =  Σ_i Σ_j ⟨A_i Ω, e^{-(s_i + s_j) K} A_j Ω⟩,
```

whose individual entries are exactly the separated-time two-point functions of the previous
section.

The reflection-positivity statement at the regulator is that this doubly-summed form is a
squared norm. It needs only that the Euclidean evolutions be self-adjoint — which holds
whenever the generator is, since the exponent $`-hK` is a real multiple of a self-adjoint
operator and the exponential preserves self-adjointness.

```
BookProof.OSReconstruction.euclidEvol_isSelfAdjoint :
  IsSelfAdjoint K → IsSelfAdjoint (euclidEvol K s)
BookProof.OSReconstruction.euclidMoment_adjoint_eq_inner :
  euclidMoment K Ω (adjoint A) [(s + t, B)] = ⟪e^{-sK}(A Ω), e^{-tK}(B Ω)⟫
BookProof.OSReconstruction.reflectedForm_eq_inner :
  reflectedForm K Ω f = ⟪reflectedVector K Ω f, reflectedVector K Ω f⟫,
    reflectedVector K Ω f = Σ_i e^{-s_i K}(A_i Ω)
BookProof.OSReconstruction.reflectedForm_re_nonneg :
  0 ≤ (reflectedForm K Ω f).re
```

No degree restriction appears anywhere: the norm square is produced by the sum
factorization, not by Wick's theorem on individual moments. Writing out the two-insertion
case makes the mechanism visible — the four-term reflected form of insertions at times
$`s` and $`t` is the squared norm of a sum of two evolved vectors:

```
BookProof.OSReconstruction.twoPoint_reflected_eq_normSq :
  ⟨A† e^{-2sK} A⟩ + ⟨A† e^{-(s+t)K} B⟩ + ⟨B† e^{-(s+t)K} A⟩ + ⟨B† e^{-2tK} B⟩
    = ‖e^{-sK}(A Ω) + e^{-tK}(B Ω)‖ ^ 2
BookProof.OSReconstruction.twoPoint_reflected_re_nonneg :
  the real part of the left-hand side is nonnegative
```
# The Interacting Half-Space Inequality

The form above is an inner-product identity on a Hilbert space, not a statement about a measure.
The measure-level version lives in the half-space modules and reads: for the state `covState ν`,
a pair of fields on the two halves that share a random shift, and a bounded measurable observable
`F` of one half,

```
BookProof.OSReconstruction.covState_reflectionPositive :
  0 ≤ ∫ z, F z.2 * F z.1 ∂covState ν
```

The reverse ordering in the integrand is the reflection: `ρ` swaps the halves, so the reflected
observable is `F` evaluated on the *first* coordinate. An interaction turns that inequality into a
question about a non-Gaussian state, and there is exactly one class of interactions where the
answer is inherited without any expansion: the ones whose Boltzmann weight factorizes across the
reflection plane.

```
ρ(z) = g z₁ * g z₂,   g ≥ 0 a positive-time weight,
BookProof.OSReconstruction.intWeight g z
BookProof.OSReconstruction.intState ν g          = (covState ν).withDensity (intWeight g)
BookProof.OSReconstruction.intState_univ         : mass = ∫⁻ ρ ∂(covState ν)
```

This is the lattice form of $`e^{-V}` with $`V = V_+ + \theta V_+`: an interaction built from
positive-time fields together with its reflection, the Dyson–Lieb–Simon class. Reflecting it costs
nothing, because the two factors are already one per half. The interacting Osterwalder–Schrader
form then *is* the free form of a different observable — each factor of the weight joins the
observable on its own side —

```
⟨θF F⟩_int = ∫ θF F · g₁ g₂ dμ₀ = ∫ θ(F g) (F g) dμ₀ ≥ 0
```

and the last inequality is the free statement applied to $`F g`$:

```
BookProof.OSReconstruction.intState_reflectionPositive :
  0 ≤ ∫ z, F z.2 * F z.1 ∂intState ν g        (g bounded, measurable, nonnegative)
BookProof.OSReconstruction.intState_expectation_re_nonneg :
  the normalized form 0 ≤ ⟨θF F⟩_int / ∫ 1 ∂intState ν g
```

The point is what the proof does *not* need: no cluster expansion, no smallness of the coupling,
no Gaussian approximation, and no cutoff removal. The interaction has to factorize, not to be
weak. That is also the honest limit of the statement — a general reflection-invariant positive
density does not preserve reflection positivity, and nothing here claims a converse. The weight is
a positive-time weight on the free state rather than a Gibbs measure with a pressure and a
thermodynamic limit, each term's weight `g` and the observable `F` are bounded (the mixture is
not), and `F` is a cylinder observable of one half rather than an element of the $`L^2`$ closure
of the positive-time algebra.

Nothing above used the fact that the weight has one term. A nonnegative *series* of factorized
weights is reflection positive term by term — the OS form of the mixture is the series of the OS
forms, and a series of nonnegative numbers is nonnegative — so the same argument covers

```
ρ(z) = ∑' i, (g i) z₁ * (g i) z₂,   every g i bounded,   Σᵢ C² Dᵢ² < ∞
BookProof.OSReconstruction.intStateSum ν g            = ∑' i, intState ν (g i)
BookProof.OSReconstruction.intStateSum_univ           : mass = ∑' i, ∫⁻ ρᵢ ∂μ₀
BookProof.OSReconstruction.intStateSum_reflectionPositive :
  0 ≤ ∫ z, F z.2 * F z.1 ∂intStateSum ν g
```

Such a density is not bounded: the bounds $`D_i`$ grow with $`i`$, so this is an unbounded
$`V_+`$ written as a sum of bounded pieces, and the summability $`\sum_i C^2 D_i^2 < \infty`$ is
exactly what makes the total form finite. What it is *not* is a general $`V_+`$: the weight still
has to decompose into matched factorized pairs, so a density outside the cone generated by the
$`g_1g_2`$ remains out of reach.

The boundedness of `F` is removable too, for a reason internal to the proof: the bound is used
only to make the triple product integrable. Stated as what it is — the OS form is finite — the
statement covers unbounded `F` and unbounded `g` alike.

```
BookProof.OSReconstruction.covState_reflectionPositive_of_integrable :
  0 ≤ ∫ z, H z.2 * H z.1 ∂covState ν          (H measurable, form integrable)
BookProof.OSReconstruction.intState_reflectionPositive_of_integrable :
  0 ≤ ∫ z, F z.2 * F z.1 ∂intState ν g        (g ≥ 0 measurable, no bound; form integrable)
```

The mean-of-squares representation $`\langle \theta H, H\rangle = \int (S_t H)^2\,d\nu`$ is
unchanged, so finiteness is the only hypothesis left — and it is a hypothesis that can be
*discharged*, not merely narrowed. The two halves of the form are integrated against shifted copies
of the same Gaussian, so an $`L^2`$ statement about the shift lives one product measure away from
the integrand. That distance is closed by two measure-preserving projections:

```
measurePreserving_covMarginal_left  : (t, x, y) ↦ (t, x)  pushes  ν ⊗ (γ ⊗ γ)  to  ν ⊗ γ
measurePreserving_covMarginal_right : (t, x, y) ↦ (t, y)  pushes  ν ⊗ (γ ⊗ γ)  to  ν ⊗ γ
```

Both are `Prod.map id Prod.fst` and `Prod.map id Prod.snd`, so `Measure.map_prod_map` reduces each
to the marginal law of a single Gaussian, and that marginal is $`\gamma`$ itself because $`\gamma`$
is a probability. Lifting `MemLp` along them and multiplying the two halves by Hölder
(`MemLp.integrable_mul`) produces the triple integrability, hence

```
BookProof.OSReconstruction.covState_reflectionPositive_of_memLp :
  0 ≤ ∫ z, H z.2 * H z.1 ∂covState ν      (H measurable, H(· + ·) ∈ L²(ν ⊗ γ))
```

The bounded-truncation argument is *not* what closes this, and the reason is worth recording: the
truncations $`H \wedge N \vee (-N)`$ converge with a dominator only if some integrable majorant of
$`(S_t H)^2`$ exists, which is the finiteness being proved. The lift-and-Hölder route has no such
circle, and it needs no boundedness anywhere.


# Sandwiching the Free Regulator Against the C1 Slices

C1 fixes the free Gaussian control in Mehler coordinates. In the slice coordinates
$`x_0 = (y_+ - y_-)/\sqrt2` and $`x_1 = (y_+ + y_-)/\sqrt2` its two-slice covariance is

```
C = [[A, B], [B, A]],   A = (v₊ + v₋)/2,   B = (v₊ − v₋)/2,
```

with Mehler variances $`v_+ = 1/(\lambda + 1)` and $`v_- = 1/(\lambda + 3)`. The diagonal is
the slice variance, and the cross term is positive — the sign responsible for C1's
reflected-covariance positivity.

The C2 hierarchy reproduces this covariance as a two-point function. In the state of norm
$`\sqrt A`, the free one-mode regulator with mass $`m` has

```
⟨Ω, e^{-hK} Ω⟩ = A · e^{-h m},
```

so choosing $`e^{-m} = B/A` — the Mehler covariance ratio, which lies in $`(0,1)` —
produces diagonal $`A` and unit-separation cross term $`B`:

```
BookProof.OSReconstruction.sliceDiagonal, sliceCross
BookProof.OSReconstruction.sliceCross_pos            : 0 < B
BookProof.OSReconstruction.sliceCross_lt_sliceDiagonal : B < A
BookProof.OSReconstruction.euclidMoment_scalarK_sqrt :
  euclidMoment (scalarK m) (√A) 1 [(h, 1)] = ↑(A * Real.exp (-(h * m)))
BookProof.OSReconstruction.free_regulator_reproduces_slice_covariance :
  ∃ m ≥ 0, (zero-separation moment = A) ∧ (unit-separation moment = B)
BookProof.OSReconstruction.free_regulator_twoPoint_reflected_re_nonneg :
  reflection positivity at this calibration
```

This is the bridge between the two constructions: the covariance C1 obtains by inverting a
two-slice Gaussian is, at one mode and unit separation, the two-point function of a free
transfer semigroup — and reflection positivity of that semigroup is the same norm-square
identity as above.

# The Reflected Form Is a Positive Semidefinite Form

Reflection positivity gives nonnegativity on the diagonal. That is already enough to obtain
the object the reconstruction needs, because the reflected form turns out to *be* an inner
product of explicitly given vectors, with no measure theory involved.

Pair two finite families rather than one, and the reflected form becomes a sesquilinear
form on the positive-time observables:

```
reflectedPair K Ω f g = Σ_i Σ_j ⟨A_i Ω, e^{-(s_i + s_j) K} B_j Ω⟩
reflectedPair_self        : reflectedPair K Ω f f = reflectedForm K Ω f
reflectedPair_eq_inner    : reflectedPair K Ω f g = ⟪reflectedVector K Ω f, reflectedVector K Ω g⟫
reflectedPair_conj_swap   : reflectedPair K Ω g f = conj (reflectedPair K Ω f g)
```

Three consequences make the pair form usable rather than merely nonnegative:

```
reflectedForm_re_eq_normSq     : (reflectedForm K Ω f).re = ‖reflectedVector K Ω f‖ ^ 2
reflectedForm_eq_zero_iff      : reflectedForm K Ω f = 0 ↔ reflectedVector K Ω f = 0
reflectedPair_eq_zero_of_null  : reflectedForm K Ω f = 0 → reflectedPair K Ω f g = 0
reflectedPair_cauchy_schwarz   : ‖reflectedPair K Ω f g‖
                                   ≤ √(reflectedForm K Ω f).re * √(reflectedForm K Ω g).re
```

The middle two say the null space of the form is exactly the kernel of the reflected vector,
so the pairing descends to the quotient of positive-time observables by null families — the
first well-definedness obligation of the reconstructed inner product. The last is
Cauchy–Schwarz, obtained from the ordinary Hilbert-space inequality applied to the reflected
vectors.

Applying it to a pair of insertions gives the standard Osterwalder–Schrader bound on the
two-point function: the two-by-two reflected matrix of `A` at time $`s` and `B` at time $`t`
is positive semidefinite, so

```
twoPoint_cauchy_schwarz :
  ‖⟨A† e^{-(s+t)K} B⟩‖ ^ 2
    ≤ ⟨A† e^{-2sK} A⟩.re * ⟨B† e^{-2tK} B⟩.re
```

Nothing beyond self-adjointness of the generator enters. In particular no spectral
hypothesis, no positivity of the evolution in an ordered space, and no Gaussian assumption is
used: the inequality is a consequence of RP and of the semigroup alone.

# The Reconstructed Pre-Hilbert Space

Having a nonnegative form and a well-defined quotient is not yet a Hilbert space. What makes
the reconstruction work at the regulator is that the quotient can be *realized*: keep each
family's insertion times separate from its operators, and the reflected vector becomes a
function of the operator family alone.

```
familyVector K Ω s A   = Σ_i e^{-s_i K} (A_i Ω)
familyVector_add       : familyVector K Ω s (A + A') = familyVector + familyVector
familyVector_smul      : familyVector K Ω s (c • A) = c • familyVector K Ω s A
```

So `familyVector` is the underlying map of a complex-linear map `familyVectorLM` into the
regulator Hilbert space, and the reflected pairing is simply the ambient inner product of
the images:

```
familyPair K Ω s A t B = ⟪familyVector K Ω s A, familyVector K Ω t B⟫
familyForm K Ω s A     = familyPair K Ω s A s A
```

`familyPair_eq_reflectedPair` checks that this is the same pairing as the double sum over
separated-time two-point functions, so nothing has been redefined along the way. The
consequences read as the inner-product axioms on classes:

```
familyPair_add_left, familyPair_add_right   linearity in each family
familyForm_eq_normSq                        familyForm = ↑‖familyVector‖ ^ 2
familyForm_re_nonneg                        the diagonal is nonnegative
familyForm_eq_zero_iff                      form = 0  ↔  reflected vector = 0
familyPair_eq_zero_of_null                  null families pair to zero
familyPair_congr_left                       the pairing depends only on the class
familyForm_sub_re_eq_dist_sq                class distance = ambient distance
familyPair_cauchy_schwarz                   the class pairing obeys Cauchy–Schwarz
```

Together these are what `reflected_reconstruction` bundles: the reflected pairing is the
inner product of the images of a linear map, its kernel is exactly the null families, the
diagonal is nonnegative, and the pairing obeys Cauchy–Schwarz. The quotient of positive-time
families by null families is therefore a pre-Hilbert space, isometric to the range of the
reconstruction map inside the regulator space; completing it is the only step still missing
to obtain the reconstructed Hilbert space at the regulator.

# The Coarse Density of a Block Step

The C3 programme begins with a step that contains no estimate at all: integrating a block of
the reference Gaussian out. The plan states its requirement as a warning — the coarse density
of $`|\Psi|^2` is $`E[|\Psi|^2 \mid G]`, not $`|E[\Psi \mid G]|^2` — and since these are
different functionals the warning is a theorem, not a convention.

Take the reference law to be two independent unit Gaussians, the first coordinate the block
and the second the exterior field. Coarse graining integrates out the block at fixed exterior
field:

```
blockIntegral f y      = ∫ x, f (x, y) ∂gamma
integral_blockIntegral : ∫ f d (gamma ⊗ gamma) = ∫ (blockIntegral f) ∂gamma
```

The second line is the tower identity: the partition-function content survives the step
intact. What does *not* survive is the density. The block step is additive on integrable
slices, pointwise nonnegative, normalised at constants, and fixes observables of the exterior
field — a positive unital linear map — and it is characterised as the conditional expectation
by pairing:

```
blockIntegral_add, blockIntegral_nonneg
blockIntegral_const, blockIntegral_exterior
blockIntegral_mul_exterior : ∫ (blockIntegral f) g ∂gamma = ∫ f (g ∘ snd) d (gamma ⊗ gamma)
```

Nothing in that last identity chooses a sigma-field: it is the characterising property of the
conditional expectation on cylinder test functions, stated as an equality of integrals.

For the cylinder observable $`\Psi_c(x,y) = x + c y` the two prescriptions can be read off:

```
blockIntegral_blockField           : blockIntegral (blockField c) y = c * y
blockIntegral_blockField_sq        : blockIntegral (fun p => blockField c p ^ 2) y = 1 + c^2*y^2
coarseDensity_eq_naiveDensity_add  : coarseDensity c y = naiveDensity c y + 1
coarseDensity_ne_naiveDensity      : coarseDensity c 0 ≠ naiveDensity c 0
integral_naiveDensity              : ∫ naiveDensity = c^2   while   ∫ |\Psi|^2 = 1 + c^2
variance_decomposition             : ∫ |\Psi|^2 = ∫ naiveDensity + 1
```

The conditional mean is the linear regression $`c y`; the coarse density is $`1 + c^2 y^2`,
and the squared conditional mean is $`c^2 y^2`. The difference is the conditional variance of
the block coordinate — $`1`, independent of both $`y` and $`c` — which is exactly the quantity
the plan insists must be preserved alongside the conditional means. At $`y = 0` the coarse
density is $`1` and the naive one vanishes, so no hypothesis can reconcile them; and the
totals differ by the same `1`, which is why the naive density cannot be repaired by a
normalisation.

# Two Block Steps, and the Small-Field Packet

A single step proves that the coarse density is the conditional second moment, but the
programme needs the step to be _iterable_. The same construction is therefore applied twice,
with a second block coordinate — the shell — integrated out after the first. Nothing new is
introduced: the second step is `blockIntegral` applied to the result of the first.

```
blockChainLaw                   = (gamma ⊗ gamma) ⊗ gamma
blockStep f z y                 = ∫ x, f (x, z, y) ∂gamma
blockChainDensity f y           = ∫ z, blockStep f z y ∂gamma
integral_blockChainDensity      : ∫ f d blockChainLaw = ∫ (blockChainDensity f) ∂gamma
blockChainDensity_const, blockChainDensity_nonneg, blockChainDensity_add
blockChainDensity_exterior
```

The composed map is again a positive unital linear map fixing the exterior field, and the
tower identity holds for it in the same form, so coarse graining twice loses nothing of the
partition function. The interesting content is what happens to the conditional mean and to
its covariance.

For the three-coordinate cylinder field $`\Psi_{c,d}(x,z,y) = x + c z + d y`:

```
blockStep_blockChainField             : blockStep (blockChainField c d) z y = c*z + d*y
blockChainDensity_blockChainField     : blockChainDensity (blockChainField c d) y = d*y
blockChainDensity_blockChainField_sq  : blockChainDensity (|blockChainField c d|^2) y
                                          = 1 + c^2 + d^2*y^2
blockChainCovariance_eq               : covariance = 1 + c^2
blockChainCovariance_small_field      : |c| ≤ 1 -> 1 ≤ covariance ≤ 2
```

The first step leaves the shell and exterior parts untouched; the second removes the shell
too. So the conditional mean after two steps is $`d y` alone: the interior coupling $`c` has
become invisible (`blockChainDensity_blockChainField_independent`), which is the
background-stability statement at this scale. The covariance tells the complementary story.
Each integrated direction contributes its unit variance, so the accumulated covariance is
$`1 + c^2` — independent of the exterior field $`y` and of the exterior coupling $`d`
(`blockChainCovariance_independent_of_background`), hence bounded by the explicit constant
$`2` under the small-field hypothesis $`|c| \le 1`. This is the C3b packet on the reference
system: an identity with an explicit constant, uniform in the background.

The small-field estimate the plan asks for is an _activity_ estimate in a norm, so the norm is
defined rather than implied, and the one estimate that a coarse step owes it is proved:

```
blockActivityNorm      f = ∫ |f| d (gamma ⊗ gamma)
blockChainActivityNorm f = ∫ |f| d blockChainLaw
integral_abs_partialIntegral_le   : ∫ |∫ f| ∂gamma ≤ ∫ |f| d (mu ⊗ gamma)
integral_abs_blockIntegral_le     : one step contracts blockActivityNorm
integral_abs_blockChainDensity_le : the chain contracts blockChainActivityNorm
```

The first line is the general statement, for a block coordinate carrying any probability
measure: a partial integral cannot increase the $`L^1` norm. That is the estimate a polymer
activity needs, and it is the honest content of "an activity estimate in an explicitly
defined norm" at this level — an $`L^1` contraction, not a polymer expansion.

# The Totals, and the Large-Field Complement

Integrating the two-step identities over the exterior field closes the bookkeeping and exposes
the regime the small-field packet does not cover:

```
integral_blockNaiveChainDensity          : ∫ naive = d^2
integral_blockChainDensity_sq            : ∫ coarse = 1 + c^2 + d^2
integral_blockChainDensity_eq_integral_naive_add
                                         : ∫ coarse = ∫ naive + (1 + c^2)
blockNaiveChainDensity_zero_background   : naive at y = 0 is 0
blockChainDensity_sq_zero_background     : coarse at y = 0 is 1 + c^2
```

The coarse total exceeds the naive one by exactly the constant that bounds the covariance
pointwise, and at zero background the naive density vanishes while the coarse one is
$`1 + c^2`. So the error of the naive prescription is _largest precisely where the background
is small_ — the regime the small-field packet addresses — and the complement of C3b therefore
has to be a statement in which the covariance is small _relative_ to the density it corrects:

```
blockChainCovariance_le_coupling_sq   : |c| ≤ M -> covariance ≤ 1 + M^2
blockChainCovariance_le_mul_density   : sqrt(2/eps) ≤ |d*y| -> covariance ≤ eps * coarse
```

The first line shows the covariance degrades only quadratically in the field strength, with no
exponential growth. The second is the C3c statement at this scale: wherever the exterior part
of the field dominates, the accumulated variance is at most the fraction $`\varepsilon` of the
coarse density, so with $`\varepsilon = 1` and $`|d y| \ge \sqrt 2` the correction is at most
half the total. That is what "large fields are easy, small fields are the work" means once the
covariance is a fixed constant rather than a field-dependent quantity.

# Arbitrarily Many Scales

The plan's C3d asks that the coupling trajectory "stay in the induction domain through
arbitrarily many UV scales". The reference system can be made scale-indexed, and then that
requirement — in the only form available here — is a theorem. The number of steps becomes a
parameter $`n`:

```
shellLaw n        = gamma^{⊗ n}  on  Fin n → ℝ
shellDensity n f y : the n-fold partial integral of f at fixed exterior value y
streamField c d n : Psi_n(z, g) = z + c * Psi_{n-1}(g),  exterior weight c^n * d
```

The field therefore carries the geometric weights of a rescaling by $`c` per scale, and the
exterior background is damped by $`c` at every step: the coupling runs, $`d \mapsto c d`. That is
the one coupling trajectory a product of independent Gaussians supports. Against it, the
density identity is a single induction with the quadratic invariant
$`A + B \Psi + C \Psi^2`:

```
shellDensity_quadratic : E_n[A + B Psi_n + C Psi_n^2] y
                           = A + B * (c^n * d * y) + C * (K_n + (c^n * d * y)^2)
shellDensity_streamField        : the running mean is c^n * d * y
shellDensity_streamField_sq     : the running second moment is K_n + (c^n d y)^2
shellDensity_streamField_covariance : second moment - mean^2 = K_n
```

The covariance after $`n` steps is $`K_n`, independent of the exterior field and of its
coupling, and it obeys the recursion

```
streamCovariance_succ        : K_{n+1} = 1 + c^2 * K_n
streamCovariance_closed_form : K_n = sum_{j<n} c^{2j}
streamCovariance_le_card     : c^2 ≤ 1 -> K_n ≤ n
streamCovariance_le_inv      : c^2 < 1 -> K_n ≤ 1/(1 - c^2)      -- uniformly in n
integral_shellDensity_streamField_sq : ∫ coarse = K_n + c^{2n} d^2
```

Each integrated Gaussian contributes exactly one unit of variance, so the accumulated covariance
is the geometric sum; it grows at most linearly in the number of scales, and if the per-scale
weight contracts ($`c^2 < 1`) it stays below the fixed constant $`1/(1-c^2)` for _every_
number of scales $`n`. That is the sense in which the small-field domain is preserved through
arbitrarily many scales: the bound does not degrade with the number of steps.

The recursion has a fixed point, and reading the statement that way is sharper than a uniform
bound. With $`c^2 < 1`$ the map $`K \mapsto 1 + c^2 K`$ has the unique fixed point
$`1/(1-c^2)`$, and the error after $`n`$ scales is exactly geometric:

```
streamCovariance_inv_sub  : K_n - 1/(1 - c^2) = - (c^2)^n / (1 - c^2)
streamCovariance_lt_inv   : c^2 < 1, c ≠ 0 -> K_n < 1/(1 - c^2)    -- strictly, at every n
tendsto_streamCovariance  : c^2 < 1 -> K_n -> 1/(1 - c^2)
tendsto_integral_shellDensity_streamField_sq
                          : the total K_n + c^{2n} d^2 tends to the same fixed point
```

So the accumulated covariance does not merely stay under a constant: it approaches the fixed
point from below at rate $`c^2`$ per scale, and the second summand of the total, $`c^{2n}d^2`$,
decays for the same reason. The uniform bound of the previous paragraph is the monotone half of
this statement; the convergence is what makes the domain statement quantitative rather than
merely uniform.

The two-step tower identity of the earlier section generalises, and the induction needs one
coordinate permutation rather than one per scale. The pointwise form pins the exterior value as
the *last* coordinate,

```
shellDensity_eq_integral_snoc : shellDensity n f y = ∫ g, f (Fin.snoc g y) ∂shellLaw n
```

and the induction splits the product law at its *first* coordinate —
`integral_shellLaw_cons_succ` at scale $`n + 1`, with `integral_shellLaw_cons` at the base —
peeling the coordinate the recursion peels. The permutation is the recentring
`piFinSuccAbove` at the last coordinate, performed once and reused at every scale; it is not a
Fubini shuffle of $`n`$ coordinates. The result is the tower identity at every scale:

```
integral_shellDensity_eq : ∫ y, shellDensity n f y ∂blockUnit = ∫ p, f p ∂shellLaw (n + 1)
```

for measurable bounded $`f`$, where `abs_shellDensity_le` and the `measurable_*` facts are what
the induction needs. This repairs a caveat the earlier section had to carry: the tower was proved
there only for two steps. It is now a theorem at every number of scales, and
`shellTail_eq_integral_snoc` reads the Chebyshev tail through it, so the tail bound is an
expectation over the reference law rather than a formal iterated integral.

That reading is what the large-field complement needs at $`n`$ scales, which is C3c in its
general-scale form:

```
shellDensity_nonneg          : f >= 0 -> shellDensity n f y >= 0
shellDensity_affine_field_le : density of {M <= |a (field - running mean) + b|}
                                 <= (a^2 K_n + b^2) / M^2
shellTail, shellTail_le      : the deviation tail at n scales is at most K_n / M^2
```

The affine form is one-step Chebyshev composed with the recursion: one more integrated scale
multiplies the coefficient $`a`$ by $`c`$ and adds a unit of variance, which is exactly
$`K_{n+1} = 1 + c^2 K_n`$. So the large-field region at any number of scales is controlled by the
same accumulated covariance the small-field packet bounds, and under $`c^2 < 1`$ the constant does
not grow with $`n`$. The estimate uses only $`K_n`$, so it is a second-moment bound, not a
bad-block entropy and not a polymer expansion, and $`M`$ is a threshold in the field's own units
rather than a normalised large-field region.

The tail bound is a statement about the *density* at fixed exterior value. Removing the damped
background from the field turns it into a statement about the law. The renormalised observable
subtracts the background read off the exterior coordinate, and its large set has a law-measure
that is an honest probability, uniformly bounded in the number of scales:

```
renormField                  : Ψ - c^n d (last coordinate)
shellTailLaw                 : (shellLaw (n+1)).real {p | M ≤ |renormField p|}
integral_shellTail_eq        : ∫ y, shellTail n c d y M = ∫ p, indicator ∂shellLaw (n+1)
shellTailLaw_le_inv          : c^2 < 1 -> shellTailLaw n c d M ≤ 1/((1 - c^2) M^2)
exists_shellTailLaw_le       : ε > 0 -> ∃ M > 0, ∀ n, shellTailLaw n c d M ≤ ε
```

The last line is **tightness**: one threshold works at every scale, which is the analytic premise
of Prokhorov's theorem for the sequence of laws of the renormalised observables. That is the
first rung of the observable limit estimate (C3e) and no more: Prokhorov's theorem itself and a
limiting law are not proved here, and the renormalisation is the subtraction of the background
rather than of an interacting divergence. The multi-point functions and the connected four-,
five- and six-point functions that *are* proved later in this chapter
(`integral_shellLaw_coord_three` through `integral_shellLaw_coord_six`,
`connectedFour_coord_eq_zero`, `connectedFive_coord_eq_zero`, `connectedSix_coord_eq_zero`) are
statements about this reference law, not about any limit.

The scalar sequence is not the only object that behaves this way. Replacing the renormalised
observable by an affine image of it keeps every step intact: the last coordinate still carries the
exterior value, so the iterated tail of an affine functional is the density the Chebyshev induction
already bounds, and the tower at its indicator moves the estimate to the law. What comes out is a
threshold that works at every scale for a whole affine family at once:

```
shellAffineLargeSet         : {p | M <= |a * renormField p + b|}
shellAffineTailLaw          : (shellLaw (n+1)).real (the affine large set)
integral_shellAffineTail_eq : integral of the density = law-level integral of the indicator
shellAffineTailLaw_le_inv   : c^2 < 1 -> tail <= (a^2/(1 - c^2) + b^2)/M^2
exists_shellAffineTailLaw_le: eps > 0 -> exists M > 0, forall n, tail <= eps
```

A shifted threshold is what a *centred* observable, or a difference of two observables, is written
in, and the price of the shift is the additive `b^2` in the numerator — which is the right scaling
for a second-moment estimate: doubling the shift quadruples the bound, and the number of scales
does not enter it at all. The scalar packet is the case `a = 1`, `b = 0`
(`shellAffineTailLaw_one_zero`), so this is a strict generalisation of it, and it shares its
ceiling: the estimate is a probability statement about an *indicator*, so no expectation, variance
or covariance of an affine image is computed. Those need the `L^1` extension of the tower named in
the qualification below.

The `L^1` gap closes at the level of *totals*, and that is where the expectations live. The
bounded tower is applied to the truncation of the square rather than to the square; the truncated
density is dominated, at every number of scales, by the exact quadratic value the induction
already produces, and it rises to that value as the truncation is raised. Monotone convergence
then turns the equality of real integrals into an equality of Lebesgue integrals, and the finiteness
of the right-hand side is what makes the square integrable:

```
truncated_moment_eq      : the bounded tower at the truncation min (psi) N
shellDensity_sq_min_le   : truncated density <= a^2 K_n + (a c^n d y + b)^2
tendsto_shellDensity_sq_min : the truncated density rises to that value
lintegral_shellLaw_sq    : the Lebesgue integral of the square is the same number
integrable_sq_affine     : hence the square is integrable
integral_shellLaw_sq     : its integral is a^2 K_n + (a c^n d)^2 + b^2
integrable_streamField   : the field is integrable as well
integral_shellLaw_centered_sq : the variance is K_n + (c^n d)^2
variance_shellLaw_le     : c^2 < 1 -> variance <= 1/(1 - c^2) + d^2
```

Two consequences are worth naming. The mean of the reference field is zero: the drift `c^n d`
multiplies the exterior coordinate, whose average is zero, so the moment formula at a shift `b = t`
and at `b = 0` differ only by `t^2`, and the cross term forces the mean to vanish. The variance is
therefore `K_n + (c^n d)^2`, and for a contracting weight it is bounded by `1/(1 - c^2) + d^2`
uniformly in the number of scales — the same uniformity the small-field bound had, now for an
honest second moment rather than for a Chebyshev count of indicators.

The renormalised observable's variance then follows from one more computation: its covariance with
the coordinate it is renormalised against. Under the product law a single coordinate has mean zero
and unit second moment, and the field's pairing with the exterior coordinate is exactly the running
drift:

```
integral_shellLaw_coord           : E[p_j] = 0
integral_shellLaw_coord_sq        : E[p_j^2] = 1
integral_shellLaw_streamField_mul_last : E[S_n · p_last] = c^n d
integral_shellLaw_renormField_mul_last : E[renorm · p_last] = 0
integral_shellLaw_renormField_sq  : E[renorm^2] = K_n
variance_renormField_le           : c^2 < 1 -> E[renorm^2] <= 1/(1 - c^2)
```

So the subtraction of the damped background is precisely a decorrelation, not merely a recentring:
the drift term is the whole of the field's correlation with the exterior coordinate, and removing it
leaves the accumulated covariance `K_n` alone — the same scale-uniform object the small-field bound
was built on. These integrals are taken by Fubini for integrable functions, with the domination
`|S · p_last| <= (S^2 + p_last^2)/2`, which is stronger than the truncation the totals needed; what
is *not* available here is anything beyond the pair. The interior cross moments, the cross-scale
pairing and the four-point function are supplied below; any statement that the law is Gaussian
remains outside.

The pair computed above is a special case of a complete second-moment calculus. Distinct
coordinates are uncorrelated and a coordinate has unit variance, so the coordinates behave, as far
as two-point functions are concerned, like the standard basis:

```
integral_shellLaw_coord_mul_coord : E[p_i p_j] = 1 if i = j, else 0
streamField_eq_sum_coeff          : S_n = sum over j of streamCoeff(c, d, n, j) * p_j
integral_shellLaw_linear_mul_coord : E[(sum w_j p_j) * p_k] = w_k
integral_shellLaw_linear_mul_linear : E[(sum w_j p_j)(sum v_j p_j)] = sum w_j v_j
integral_shellLaw_streamField_mul_linear : E[S_n (sum w_j p_j)] = sum streamCoeff_j w_j
```

The coefficient vector is explicit: `c^j` on the interior coordinates and the running drift
`c^n d` on the exterior one. So a two-point function costs an inner product, and the whole family of
second moments of linear statistics — the field, the renormalised field, any affine image of
either — is a computation rather than an estimate. What the calculus does not contain at this
point is the cross-scale pairing between two different numbers of scales, which needs the
coefficient vector reindexed along the inclusion of the smaller shell, and the four-point function,
for which the pairing of four coordinates is no longer an inner product; both are supplied below.

A second moment is not the end of what the reference law computes. Two further statements are
proved in the same module, and the second is a complete moment calculus.

The first puts two different numbers of scales in the same space. A field of `m < n` scales is a
statistic of the first `m + 1` coordinates; lifting its coefficient vector along the inclusion and
reading the extra coordinates with weight `0` (`truncCoeff`, `sum_truncCoeff_mul`) makes it a
statistic of the `n`-scale space, and the kernel then pairs it with the larger field:

```
integral_shellLaw_streamField_mul_smaller :
    E[S_n · S_m] = K_m + c^(2m) · d        (m < n)
```

The point worth pausing on is the exponent. The smaller field's exterior coefficient is `c^m·d`;
in the larger space that coordinate is *interior* with coefficient `c^m`. So the answer is not the
smaller field's own second moment `K_m + (c^m d)²` — the two differ by exactly the drift the larger
field assigns to a coordinate the smaller one treats as background. Cross-scale covariance is
therefore a property of the trajectory, not of either field alone.

The second statement is not a moment but all of them. Because the reference law is a product,

```
integral_shellLaw_prod_coord_pow :
    E[∏ i, (p i)^(e i)] = ∏ i, E[z^(e i)]
```

by a single application of `integral_fintype_prod_eq_prod` — no induction on the number of
coordinates, no truncation, no domination. Every coordinate moment of the law is a product of
one-dimensional moments. The four-point function is the case in which the exponent vector is
supported on four coordinates: with multiplicities `2, 2` the product is `1`, with multiplicities
`1, 1, 1, 1` it is `0`, and with a single multiplicity `4` it is `3`, which is the Wick sum
`δ_ij δ_kl + δ_ik δ_jl + δ_il δ_jk` read through the pattern of equalities among the four indices.

That reading is also a proof, and it does not need a case analysis over the equality pattern. The
reference law *is* Mathlib's product Gaussian, so Isserlis' theorem applies at the level of the
sites: `integral_shellLaw_prod_coord` is the same factorization indexed by a tuple of coordinates,
the product of one-dimensional moments is identified with the weighted pairing sum by
`wickSum_identity_eq_prod_doubleFactorial`, and the pairing sum over four sites is a sum of exactly
three terms, because `Fin 4` has three pairings — listed by `pairingSet_four` and evaluated by
`wickSum_four`:

```
integral_shellLaw_coord_four :
    E[p_i p_j p_k p_l] = δ_ij δ_kl + δ_ik δ_jl + δ_il δ_jk
```

The parity that kills the `1, 1, 1, 1` and `3, 1` patterns is also the three-point function. Three
sites cannot all occur an even number of times — their multiplicities sum to `3` — so one factor of
the multiplicity product is an odd power of a centred Gaussian, and `integral_pow_odd_blockUnit`
says that factor is zero:

```
integral_shellLaw_coord_three :
    E[p_i p_j p_k] = 0
```

The same factorization does not stop at four fields, and the statements above are instances of one
theorem stated for an arbitrary number of them. Reading the multiplicity product as a weighted sum
over pairings gives the moment at *every* tuple of sites: odd tuples have no pairing to sum over,
even tuples sum over all of them, and the number of fields is a parameter rather than a case:

```
integral_shellLaw_prod_coord_eq_wickSum :
    E[∏_t p_(f t)] = wickSum (fun a b => if f a = f b then 1 else 0) univ
integral_shellLaw_prod_coord_odd :
    E[∏_t p_(f t)] = 0                            (2k+1 sites)
integral_shellLaw_prod_coord_even :
    E[∏_t p_(f t)] = sum over the pairings            (2k sites)
```

The five-point function is the odd case at `k = 2`, and it vanishes for the same reason the
three-point function does — five sites cannot all occur an even number of times:

```
integral_shellLaw_coord_five :
    E[p_i p_j p_k p_l p_r] = 0
```

The six-point function is the even case at `k = 3`, where the pairings of six sites are fifteen —
`5 · 3 · 1`, the perfect matchings of `{0, …, 5}` — listed, counted, and evaluated contraction by
contraction:

```
pairingSet_six      : the fifteen pairings of Fin 6, listed
pairingSet_six_card : 15 pairings
wickSum_six         : the pairing sum is the fifteen contractions
integral_shellLaw_coord_six :
    E[p_i p_j p_k p_l p_r p_s] = sum of δ_ab δ_cd δ_ef over the fifteen pairings
```

Each contraction is read exactly as in the four-point case: the filter `{a | a < σ a}` orients every
pair by its smaller member, and the product over the filter is the product of the three
contractions. This is the shape of a matching sum — perfect matchings, oriented by their smaller
member — and it is the same presentation the QYM developments use for their `Matching` and `corners`
constructions.

The moments are not the only thing the pairing structure computes. The joint cumulant of four
fields is the Möbius sum over the partitions of the four positions — the same partition formula
the QYM development uses at three points (`connectedThree` in `MSPositionLabels.lean`) — and under
the centred reference law every term with a singleton block vanishes, leaving the four-point
function minus the three pairings:

```
connectedFour :
    m1234 - (m12 m34 + m13 m24 + m14 m23) - (single-block terms)
      + 2(...) - 6 m1 m2 m3 m4
connectedFourShell_eq_pair :
    kappa = m1234 - m12 m34 - m13 m24 - m14 m23
connectedFourShell_eq_zero :
    kappa = 0
```

Both `m1234` and the pair moments are Isserlis pairings, so substituting the `δ`-forms gives
`(δδ + δδ + δδ) − δδ − δδ − δδ = 0`: the reference law has no connected four-point part. This is
the statement that a Gaussian's fourth cumulant vanishes, proved for this law rather than assumed.
It is a property of the law, not a criterion for one: a vanishing fourth cumulant does not make a
law Gaussian, and `connectedFour_coord_eq_zero` does not assert that it does.

The same partition formula runs one order higher. The fifth joint cumulant is the Möbius sum over
the fifty-two partitions of five positions, with coefficients `(-1)^(k-1) (k-1)!` — the coefficient
identity `connectedFive_one` checks the list — and on five positions every partition contains a
block of one, three or five elements:

```
connectedFive :
    m12345 - (the fifteen 1+4 and 2+3 partitions) + 2(the 1+1+3 and 1+2+2 partitions)
      - 6(the 1+1+1+2 partitions) + 24 m1 m2 m3 m4 m5
connectedFive_eq_zero :
    (blocks of card 1 vanish) -> (blocks of card 3 vanish) -> face univ = 0 -> kappa = 0
connectedFiveShell_eq_zero :
    kappa = 0
```

Each such block has zero moment under the reference law (`shellFace5_card_one`,
`shellFace5_card_three`, `shellFace5_univ_eq_zero`), so every product in the Möbius sum carries a
zero factor and the fifth cumulant vanishes: the reference law has no connected five-point part.
This is still one explicit partition sum; no cumulant of arbitrary order and no general
partition-lattice Möbius inversion is claimed.

The sixth cumulant is where the vanishing stops being purely a count of block sizes. The Möbius
sum runs over the two hundred and three partitions of six positions, with the same coefficients
`(-1)^(k-1) (k-1)!` (`connectedSix_one` checks the list). Blocks of one and three positions still
have zero moment and a block of five positions leaves a singleton, so the odd blocks drop out:

```
connectedSix :
    m123456 - (the thirty-one two-block partitions) + 2(the ninety three-block partitions)
      - 6(the sixty-five four-block partitions) + 24(the fifteen five-block partitions)
      - 120 m1 m2 m3 m4 m5 m6
connectedSix_eq_reduced :
    (blocks of card 1 vanish) -> (blocks of card 3 vanish) ->
      kappa = m123456 - (the fifteen 4+2 terms) + 2(the fifteen 2+2+2 terms)
connectedSixShell_eq_zero :
    kappa = 0
```

What survives is the whole set, the fifteen partitions into a four and a two, and the fifteen
partitions into three pairs. Every surviving moment is an Isserlis sum, and the coefficients
cancel matching by matching: one of the fifteen matchings of six sites appears once in `m123456`,
three times in the `4 + 2` sum (once for each choice of the pair that is the two-block), and once
with coefficient `2` in the `2 + 2 + 2` sum, so each contributes `1 - 3 + 2 = 0`. The sixth
cumulant vanishes as well, now by a cancellation of Isserlis sums rather than by a zero factor.
This is still one explicit partition sum at one arity.

At every higher order the same vanishing holds, and the general statement is now proved rather
than repeated arity by arity. The cumulant of a moment function on `Finset (Fin M)` is defined as
the Möbius inversion over the partition lattice, computed by splitting off the block of the least
position:

```
cumulant :
    kappa s = face s - (sum over the proper blocks t containing min s of kappa t * face (s \ t))
moment_eq_sum_cumulant :
    face s = (that sum) + kappa s
cumulant_pair_of_lt :
    kappa {x, y} = face {x, y} - face {x} * face {y}          (x < y)
sum_two_block :
    (sum over the two-element blocks) = (sum over b in s.erase (min s), at {min s, b})
cumulant_eq_zero_of_wick :
    face empty = 1 -> (odd moments vanish) -> (Wick recursion) -> 3 <= #s -> kappa s = 0
```

Only the two-element blocks survive the induction, and reindexing them by their second element
turns the recursion into the Wick recursion (`sum_two_block`). For the reference law the moment of
any finite set of positions is the pairing sum at every order, obtained from the general Wick
recursion for linear forms (`wick_pi`) rather than from a pairing enumeration:

```
shellMoment_eq_wickSum :
    E[prod over t in s of p_(f t)] = wickSum (fun a b => if f a = f b then 1 else 0) s
shellMoment_wick :
    E[...] = sum over b in s.erase (min s) of (delta) * E[... on the rest]
cumulant_shellMoment_eq_zero :
    3 <= #s -> kappa s = 0
cumulant_seven_eq_zero :
    kappa univ = 0                                   (seven positions)
```

The seventh cumulant is the order-seven instance and needs no matching cancellation: every
partition of seven positions has a block of odd cardinality, and odd-cardinality moments vanish.
The `3 + 2 + 2` partitions do not survive, because their block of three has zero moment; neither
does `5 + 2`, nor the one-block partition. At odd order the vanishing is therefore a zero factor
again, and the `1 - 3 + 2 = 0` of the sixth cumulant is not the last matching cancellation — at
order eight the same argument runs, now with the general theorem in place of a hand-built
partition list.

What stays open is not these moments but their converse. `integral_shellLaw_coord_four` is
Isserlis' theorem for the covariance `1`: it computes the four-point function of *this* law, and
nothing in the module shows that a law with these moments is Gaussian, or computes a connected
correlation at separated points. The general statements are uniform in the number of fields, and
the vanishing of every higher cumulant is now a theorem (`cumulant_shellMoment_eq_zero`) rather
than a list of arities; the per-pairing evaluation at four and six sites remains a finite
computation, so no closed form for the number of pairings at arbitrary `M` is derived here, but
the general vanishing no longer depends on one. So Gaussianity as a property of a limit law is
still unproved; only its moments and the vanishing of its higher cumulants are.

Two honest qualifications belong here rather than in a footnote. First, the flow is a
_weight_, not a renormalisation: `streamField` multiplies by `c`, the law is still a product of
fresh independent Gaussians, and $`d \mapsto c d` is a definition, not a theorem about an
effective action. Second, `shellDensity` is defined as the $`n`-fold iterated integral, and the
*tower identity* $`\int f \,d\gamma^{\otimes (n+1)} = \int y, \mathrm{shellDensity}_n f y`
is proved at every scale above, but only for measurable *bounded* observables — the induction's
boundedness input is `abs_shellDensity_le`. Nothing here is a theory of the iterated integrals in
$`L^1`$, and the density is still *defined* as an iterated partial integral rather than derived
from a conditional expectation on a sigma-field. Nothing here is C3d in the plan's sense — there
is no effective action, counterterm, marginal direction or logarithmic running, and the
$`n`-uniformity is exactly what the triviality of the reference flow buys.

# What Is Verified, and What Is Open

Four honest boundaries delimit this chapter.

*First, the calibration is a covariance statement, not an identification of laws.* The
scalar regulator's moments are not the Mehler path measure; no field law, transfer operator
or interacting dynamics is constructed. The mass is the free mass that reproduces the ratio
$`B/A`, not the physical cutoff mass.

*Second, "reflection positivity at the regulator" has two forms, and only one of them is
general.* The Hilbert-space identity $`\langle \theta F, F\rangle = \|\cdot\|^2` for bounded
observables and their words holds for any self-adjoint generator. The *interacting* half-space
inequality $`\langle \theta F, F\rangle_{\mathrm{int}} \ge 0` holds here for the interactions whose
weight factorizes across the reflection plane, $`\rho = g_1 g_2` with a bounded positive-time
weight $`g` — where it is a consequence of the free statement, not an approximation to it.
An unbounded $`V_+`$ is covered only when it expands as a convergent series of
factorized weights — a mixture class, not a general interaction. That is not a gap to be closed by
more work on this mechanism: reflection positivity is a positivity condition on the reflected
kernel, not a consequence of reflection invariance, and a general density demonstrably fails it
and that failure is itself a theorem of the module, not a remark. For any probability `μ₀` and any
measurable `h` with $`|h| \le 1`$, $`\int h = 0`$ and $`\int h^2 = 1`$, and any
$`0 < \epsilon < 1`$,

```
BookProof.OSReconstruction.generalWeight_pos      : 0 < 1 - ε h z₁ h z₂
BookProof.OSReconstruction.generalWeight_swap     : reflection invariance
BookProof.OSReconstruction.generalWeight_osForm   : ⟨θh, h⟩_ρ = -ε
BookProof.OSReconstruction.not_reflectionPositive_of_generalWeight :
  ∃ W, (∀ z, 0 < W z) ∧ (∀ z, W (z.2, z.1) = W z) ∧ ∫ h z.2 h z.1 W z d(μ₀ ⊗ μ₀) < 0
```

The sign is the whole story: `1 + ε h₁h₂` has OS form `+ε`, and that sign is the coefficient of the
rank-one term. So the general case is false rather than open, and what a general `V` needs is a
*positivity structure* — $`V = V_+ + \theta V_+`$, a decomposition into individually
reflection-positive terms, or a convergent expansion in a stable regime — not more work on this
mechanism. The $`L^2`$ question splits, and both halves are now settled at the level of the form:
for the free covariant state the finiteness is *derived*, not assumed, from the single hypothesis
$`H(\cdot + \cdot) \in L^2(\nu \otimes \gamma)`$ (`covState_reflectionPositive_of_memLp`, resting
on the two marginal projections), and the interacting state inherits it verbatim -- `intState` is
the free state reweighted by the product $`g z_1 g z_2`$, so the weight rides along with the
observable and `intState_reflectionPositive_of_memLp` derives the weighted form's finiteness from
$`g F \in L^2(\nu \otimes \gamma)`$. For the factorized weights of C2/E3 that condition is itself a
theorem rather than a hypothesis: they are *bounded*, and a bounded nonnegative factor can only
shrink the norm, so `memLp_shift_mul_of_bound` derives $`g F \in L^2`$ from $`F \in L^2`$ and
`intState_reflectionPositive_of_memLp_of_bounded` states the interacting inequality with no bound
on the observable and no finiteness assumption anywhere. An *unbounded* $`V_+`$ is covered by
Hölder instead of by a bound: `intState_reflectionPositive_of_memLp_unbounded` asks for the weight
and the observable to be $`L^4`$ against the Gaussian, and `memLp_shift_mul_of_memLp` turns those
two $`L^4`$ hypotheses into the $`L^2`$ hypothesis of the theorem above — so `g` may be unbounded
(every polynomial growth is in every finite $`L^p`$ of a Gaussian), what must be finite is the
exponent and not the sup norm.
Separated-time *diagonal* positivity $`\langle A^\dagger e^{-hK} A\rangle \ge 0` at $`h > 0` is
likewise not claimed: it needs a positive (spectral) evolution, a hypothesis this slice does not
establish. The unbounded generator $`h_\sigma`, its closure and its selection, the field-law
representation, and the positivity-preserving semigroup with a ground function all remain open.
Nothing here is evidence that an interaction survives cutoff removal.

_Third, the reconstruction is now a Hilbert space, and the algebra's product closes on it._
The positivity-preserving form is built from bounded observables and a bounded `K`. Section 7 of
`BookProof.OSReconstruction.EuclideanMomentHierarchy` realizes the quotient by null families
isometrically inside the regulator space. Two things were missing there, and section 8 supplies
them. The realization was a span, not a closed space: `reconSpace` is its closure, so it is closed
by construction (`reconSpace_isClosed`), complete (`reconSpace_complete`), inherits the ambient
inner product, contains every family class (`familyVector_mem_reconSpace`), and is the *smallest*
closed subspace that does (`reconSpace_minimal`) — the completion, not one of several. And nothing
there said what the product of two families is: `familyProduct` takes the joint insertion family on
`ι ⊕ κ`, and its reflected vector is the *sum* of the two vectors (`familyVector_sum`), so a
product of families is again a family, its form is the squared norm of that sum and hence
nonnegative with no hypothesis (`familyForm_familyProduct`), and the product is continuous
(`norm_familyVector_le_add`), which is what lets it descend to the completion.
The *pointwise* product is a different operation, and it closes only against an essentially
bounded factor: `memLp_mul_of_memLp_top` is Hölder at `(2, ∞)`, and without that hypothesis the
statement is false — `l2_not_closed_under_pointwise_mul` exhibits, on $`(0,1)`$ with Lebesgue
measure, the function $`x^{-1/3}`$: square integrable, since its exponent $`-2/3`$ is above $`-1`$,
while its pointwise square has exponent $`-4/3`$ and is not. So the $`L^2`$ closure is a module
over the essentially bounded observables rather than an algebra under pointwise multiplication.
Cauchy–Schwarz is still derived from the explicit norm identity rather than from abstract form
theory. The OS inequality proved is the finite-family one;
the interacting version is the factorized-weight one above, and any field law remains outside this
chapter.

_Fourth, the coarse-graining step is one, two or arbitrarily many blocks of a reference
Gaussian._ The chain iterates the operation and, once indexed by $`n`, the number of scales
— but every coordinate remains a fresh independent Gaussian, so nothing is renormalised
between steps, the per-scale weight is put in by hand, and neither the chain nor the indexed
family is an RG map. There is no measure-level pushforward, no gauge transport and no
lattice. `blockIntegral_mul_exterior` is the characterising identity of the conditional
expectation on cylinder test functions rather than a construction of conditional
expectations, and `coarseDensity_ne_naiveDensity` shows the two prescriptions differ in this
one system without giving a lower bound for interacting or gauge theories. The C3b packet is
correspondingly narrow: `blockChainCovariance_small_field` is an exact identity with an
explicit constant, not an elliptic or derivative estimate for an interacting measure, and
`integral_abs_blockChainDensity_le` is $`L^1` contraction, not a polymer expansion with a
summable activity ledger. The C3c complement here is not a large-field theory either:
`blockChainCovariance_le_mul_density` says the _fixed_ covariance is relatively negligible
where the background is large; it does not bound a fluctuation covariance, control a bad-block
region or prove a summable tail, and `blockChainCovariance_le_coupling_sq` is a quadratic bound
in the coupling, not a large-field expansion. Running couplings (C3d) and the observable limit
estimate (C3e) remain open.

Everything proved in this chapter is `sorry`-free, and every declaration listed above
depends only on Lean's standard `propext`, `Classical.choice` and `Quot.sound`
(`Work/EuclideanMomentAudit.lean`, 195 declarations).
