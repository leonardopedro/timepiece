import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Resolution of the Singularity of an ODE" =>
%%%
tag := "ode-chapter"
%%%

This chapter replaces the ODE chapter of the source manuscript. It follows the
expanded, operator-theoretic treatment of `ODE.tex`, and is honest about which parts
are formally verified and which remain open (see the proof-plan appendix).

# The Blow-Up

Consider the scalar autonomous ODE

$$`\dot x = x^2, \qquad x(0) = x_0 \in \mathbb{R}.`

Its unique maximal solution is

$$`x(t) = \frac{x_0}{1 - t\,x_0},`

defined only on $`(-\infty, 1/x_0)` when $`x_0 > 0`. As $`t \to 1/x_0`, the
solution **blows up**: $`|x(t)| \to \infty`. There is no global, deterministic
solution defined for all time.

This finite-time blow-up creates two problems:

 * **Undetectability** — if a numerical integrator fails to converge, one cannot
   tell a genuine singularity from insufficient resolution.
 * **Degeneracy** — the blow-up allows unrelated initial conditions to be glued
   before and after the singular time, destroying uniqueness of the initial-value
   problem.

The blow-up time is a concrete, verifiable quantity. In the repository's
`Singularity` library (module `Singularity.Singularity`), the blow-up time of
$`\dot x = x^2` is computed:

```
#check @blowupTime_x_sq
```

# The Central Idea: Admit Uncertainty

The manuscript's central claim is that **both problems are resolved by admitting a
finite amount of uncertainty in the initial condition**. Instead of a point
$`x_0 \in \mathbb{R}`, take a probability measure $`\mu_0` on $`\mathbb{R}` —
equivalently, by the Born parametrization of Part II, a wave-function
$`\psi_0 \in L^2(\mathbb{R})` with $`|\psi_0|^2 = \mu_0` — and evolve it under a
**unitary** group. The resulting evolution is globally defined in time,
non-deterministic in the coordinate $`x`, and reduces to the classical solution in
the zero-uncertainty limit.

This is the same philosophy as the rest of the book: replace a point of the
probability space by a wave-function, and gain structure (here, global unitary
evolution) in return.

# Koopman–von Neumann: Classical Mechanics as Quantum Mechanics

Given a sample space $`\Omega = \mathbb{R}` with a probability measure $`\mu`, one
may always define a wave-function $`\psi = \sqrt{d\mu/dx}` (up to a phase). The
**Koopman–von Neumann** formulation recasts classical statistical mechanics as a
special case of quantum mechanics in which the algebra of observables is
commutative (because the underlying time-evolution is deterministic).

Since $`\mathbb{R}` is a simply connected Lie group under addition, Bargmann's
theorem lifts any strongly-continuous projective unitary representation to a genuine
unitary representation $`U(t)`, and **Stone's theorem** then gives a unique
self-adjoint **Hamiltonian** $`H` with

$$`U(t) = e^{-iHt}.`

So the program is: turn the ODE into a Hamiltonian $`H`, and the (possibly
singular) classical flow into a (globally-defined) unitary group $`e^{-iHt}`.

# Weyl Quantization: From ODE to Hamiltonian

The passage from the classical vector field $`\dot x = f(x)` to a self-adjoint
Hamiltonian is **Weyl quantization**. Because $`x` and the momentum
$`\hat p = -i\,\partial_x` do not commute, the classical product $`f(x)\,p` must be
**symmetrized**. For $`\dot x = x^2` the (formal) Hamiltonian is

$$`H = x^2 \hat p - i\,\hat x,`

where the $`-i\hat x` term is the symmetrization correction. The repository defines
this Weyl-symmetrized Hamiltonian on a normal-ordered operator algebra (module
`Singularity.Hamiltonian` and `Singularity.Poly`):

```
#check @odeToHamiltonian
```

The normal-ordered operator algebra (module `Singularity.Poly`) represents an
operator on $`M` bosonic modes as a finitely-supported function recording
creation/annihilation counts per mode, and implements the **Wick recursion** for
multiplication. This part of the formalization is genuine and `sorry`-free.

# Nelson's Theorem and Essential Self-Adjointness

For the unitary evolution $`e^{-iHt}` to exist globally, the Hamiltonian must be
**essentially self-adjoint** (its closure must be self-adjoint, so that the spectral
theorem applies). **Nelson's theorem** gives a criterion: a symmetric operator is
essentially self-adjoint on a domain if it has a dense set of **analytic vectors**.
For an ODE-derived Hamiltonian, the relevant analytic vectors are tied to the
**completeness of the classical flow**: roughly, if the classical flow exists for
all time, the Hamiltonian is essentially self-adjoint, and conversely.

The repository states this connection (module `Singularity.Esa`):

```
#check @nelson_essential_self_adjoint
```

**Honesty note.** This statement is currently a **placeholder**, not a proof: the
repository marks it as such, and the body discards its hypothesis. Nelson's theorem
is a deep result of functional analysis, and its formal proof (together with the
self-adjointness of the Weyl Hamiltonian, also currently a placeholder proving only
`True`) is one of the main open items, routed to the proof-plan appendix.

# The Resolution: Complexification

The cleanest mathematical argument that the singularity disappears is
**complexification**. Pass from $`L^2(\mathbb{R})` to $`L^2(\mathbb{R}^2)` and the
real variable $`x(t)` to a complex one $`z(t) = x(t) + i y(t)` satisfying
$`\dot z = z^2`. The solution is

$$`z(t) = \frac{z(0)}{1 - t\,z(0)},`

with a singularity when $`1 - t\,z(0) = 0`, i.e. $`t = 1/z(0)`. For this singular
time to be **real**, we need $`\operatorname{Im}(1/z(0)) = 0`, which forces
$`y(0) = 0`. But the line $`y(0) = 0` is a **null-measure subset** of
$`\mathbb{R}^2` (this is exactly the measure-theoretic phenomenon of
{ref "null-measure"}[Null-measure sets need not be small]). Therefore, for **almost
every** initial condition in $`L^2(\mathbb{R}^2)`, the singular time is non-real,
and **there is no finite-time singularity**.

Moreover, the imaginary part $`y(0)` can be concentrated arbitrarily close to zero,
so the unitary solution in $`L^2(\mathbb{R}^2)` recovers the (non-unitary,
isometric) solution in $`L^2(\mathbb{R})` in the limit $`y(0) \to 0`. Changing the
sample space effectively changes the equation: $`y(0) = 0` strictly is not
achievable in $`L^2(\mathbb{R}^2)`.

A complementary argument uses **energy-bounded initial conditions**: a finite-time
singularity would make the time-derivative of the wave-function diverge; but the
time-derivative corresponds to the Hamiltonian, whose spectral measure is conserved
by unitary evolution, so an initial condition using only eigenfunctions below some
$`E_{\max}` cannot produce a divergent time-derivative.

**Honesty note.** This complexification argument is the mathematical heart of the
resolution, but it is **not yet formalized** in the repository. It is the central
item of the ODE section of the proof-plan appendix.

# What Is Verified, and What Is Open

The repository's `Singularity` library is `sorry`-free, but its theorems split into
two classes:

: Genuinely proved

  The normal-ordered operator algebra and Wick recursion (`Singularity.Poly`); the
  flow-analysis machinery and blow-up criteria (`Singularity.Flow`), including the
  fact that an even-degree monomial flow blows up and that linear flows are
  complete; and the explicit blow-up time of $`x^2` (`blowupTime_x_sq`).

  ```
  #check @blowup_criterion_scalar
  #check @linear_flow_complete
  #check @even_degree_monomial_blowup
  ```

: Placeholders or open

  Nelson's essential-self-adjointness theorem (`nelson_essential_self_adjoint`) and
  the self-adjointness of the Weyl Hamiltonian (`weyl_symmetrization_self_adjoint`)
  are **placeholders**. The analytic **complexification resolution** (no
  finite-time singularity in $`L^2(\mathbb{R}^2)`) and the energy-bounded argument
  are **not formalized**. These are the subject of the ODE proof plans in the
  appendix.

# The Price: Non-Determinism

The resolution comes at a cost the manuscript is explicit about: the evolution is
deterministic in the coordinate $`x` but **non-deterministic** in the
energy-bounded sample space. The Hamiltonian's spectral measure is conserved, but
the map from spectral variables to coordinates is non-trivial. This non-determinism
is the price paid for removing the singularity — and it is of a piece with the
book's recurring theme that passing from a probability distribution to a
wave-function trades determinism of the observable for the richer, reversible
structure of the wave-function.
