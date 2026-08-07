import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The Gauge Ambiguity of the Born Parametrization" =>
%%%
tag := "born-fiber"
%%%

# The Parametrization Is Many-to-One

We have seen that the Born map — sending a unit wave-function $`\psi` to the
distribution $`p_k = |\psi_k|^2` — is *surjective*: every distribution is reached.
It is emphatically *not injective*: many different wave-functions give the same
probabilities. The most familiar example is the global phase: over the complex
numbers, $`\psi` and $`e^{i\theta}\psi` give identical Born probabilities.

The natural question is: _exactly_ how many wave-functions map to a given
distribution? The answer, made precise below, is that two wave-functions give the
same Born probabilities *if and only if* they differ by an invisible phase (or
sign, in the real case) at each coordinate. This invisible redundancy is the
*gauge ambiguity* of the parametrization, and it is the seed of gauge symmetry.

# The Complex Fiber: Coordinate-wise Phases

For complex wave-functions $`u, v : \{0,\dots,n-1\} \to \mathbb{C}`, the Born
probabilities agree, $`|u_k|^2 = |v_k|^2` for all $`k`, *if and only if* each
coordinate differs by a phase $`e^{i\theta_k}`:

$$`|u_k| = |v_k| \;\Longleftrightarrow\; \exists \theta_k,\; v_k = e^{i\theta_k} u_k.`

The single-coordinate fact is just the polar form of a complex number; the
multi-coordinate statement is its pointwise application:

```
#check @ChapterBornPhaseFiber.Complex.normSq_eq_iff_exists_phase
#check @ChapterBornPhaseFiber.born_fiber_complex
```

So the *fiber* of the Born map over a distribution with all-positive entries is an
$`n`-torus $`(S^1)^n`: one independent phase per coordinate. A wave-function is a
probability distribution together with a choice of these invisible phases.

# The Real Fiber: Coordinate-wise Signs

Over the *real* numbers the only numbers with a given squared value differ by a
*sign* $`\pm 1`, so the fiber is the finite group $`\{\pm 1\}^n`:

```
#check @ChapterBornPhaseFiber.sq_eq_iff_exists_sign
#check @ChapterBornPhaseFiber.born_fiber_real
```

The real parametrization of {ref "born-reproduces"}[the previous chapter] thus
double-covers the interior of the simplex: each strictly-positive distribution is
the Born image of $`2^n` real wave-functions, related by coordinate-wise sign flips.

# Why This Is "Gauge"

A redundancy in a parametrization that has no observable effect is precisely what
physicists call a *gauge freedom*. Here the observables are the probabilities
$`p_k = |\psi_k|^2`, and the gauge transformations are the coordinate-wise phases
$`\psi_k \mapsto e^{i\theta_k}\psi_k` (or signs, over $`\mathbb{R}`). Two
wave-functions related by such a transformation describe the *same* physical
probability distribution.

The manuscript's refrain — "two wave-functions are always related by a rotation of
the hypersphere" — is the geometric version of this: the Born fibers are the orbits
of a group of invisible rotations, and the simplex is the *quotient* of the sphere
by that group. Making that quotient precise (the sphere modulo the phase/sign gauge)
is the subject of the free-field chapters; the fiber computation above is its
algebraic core.

# A Consequence: No Continuous Symmetry on the Simplex

Recall from {ref "probability-clock"}[the probability clock] that the only linear
maps preserving the probability simplex are stochastic matrices, and the
collapse-to-a-vertex one is singular. The gauge picture explains _why_ the genuine
(invertible) symmetries live one level up, on the wave-function: a symmetry of the
probabilities must lift to a symmetry of the sphere that respects the fibers, i.e. a
*unitary* transformation. The phases we just identified are exactly the kernel of
the projection from unitary dynamics on the sphere to stochastic dynamics on the
simplex.
