import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Timepiece and the Gribov Ambiguity" =>
%%%
tag := "gribov-ambiguity"
%%%

# Orientation and Status

The manuscript ranges from the abelian free-field example to a proposed non-abelian
field theory. This chapter keeps those levels separate: the abelian gauge-invariance
and conditional number-shift identities are available. Set-level comprehensive
fixing and observable-extension theorems are also proved. Their measurable
field-model realization, physical dynamics and a continuum Yang–Mills mass-gap
conclusion are separate obligations.

:::paragraph
In the tour this chapter closes the Standard-Model thread of the part, after
{ref "quantization-time-evolution"}[quantization by time-evolution]. It is the
place to distinguish orbit coverage from regular gauge sections, local abelian
identities from global gauge-fixing claims, and a number-shift model from the
absolute inner lower bound needed by the final nested-Fock Hamiltonian.
:::

:::paragraph
The route: the question, the abelian field strength and gauge invariance, the
mass gap and observable invariance, the mass gap in the numerical validation,
and the algebraic-ideals view of gauge.
:::

:::paragraph
The proofs include `BookProof/FreeEMField`, `BookProof/MassGap`, and the
comprehensive/incomplete-fixing chapters explained in
{ref "gauge-symmetry"}[the gauge chapter].
:::

# The Question

:::paragraph
The manuscript's chapter on the Gribov ambiguity considers statistical field
theories in Minkowski space-time where the (classical) canonical coordinates,
when modified by a non-deterministic time-evolution, verify the canonical
commutation relations. Gauge symmetries are defined through algebraic ideals, and
the chapter proposes definitions for Quantum Yang–Mills and Quantum Gravity,
testing consistency with the quantization of the free electromagnetic field. The
verified content here is the algebraic core: the abelian field strength and its
gauge invariance (the "no Gribov ambiguity" case), and the mass-gap / observable
invariance argument.
:::

# The Abelian Field Strength and Gauge Invariance

:::paragraph
The identity here concerns the abelian field strength
$`F_{jk}=\delta_jA_k-\delta_kA_j`. Commuting partial derivations imply that
$`A\mapsto A+\partial\theta` leaves it unchanged. This proves a local
observable identity; it does not construct a global representative map or
settle its zero modes, boundary conditions and regularity. Calling this alone
“no Gribov ambiguity” would conflate those questions.
:::

```
#check @BookProof.FreeEMField.emFieldStrength
#check @BookProof.FreeEMField.emFieldStrength_antisymm
#check @BookProof.FreeEMField.emFieldStrength_gauge_invariant
```

:::paragraph
The reduction from the non-abelian case is explicit: when the connection
components commute, the non-abelian field strength loses its quadratic
$`[A_j,A_k]` correction and becomes the linear abelian one — which is why the
Hamiltonian is quadratic in the fields in this case:
:::

```
#check @BookProof.FreeEMField.fieldStrengthMul_eq_emFieldStrength_of_commute
#check @BookProof.FreeEMField.Fbook_eq_emFieldStrength_of_commute
```

:::paragraph
Finally, the curl of self-adjoint operator fields is self-adjoint — the book's
"local self-adjoint operator $`\partial\times\pi`, the curl of the Electric Field":
:::

```
#check @BookProof.FreeEMField.emFieldStrength_isSelfAdjoint
```

# The Mass Gap and Observable Invariance

:::paragraph
The number-shift identity has explicit commutation assumptions:
$`[H,N]=0` and $`[O,N]=0` imply that Heisenberg evolution of this observable
$`O` is unchanged by replacing $`H` with $`H+\lambda N` in the stated
operator-algebra model. This is equality on a specified observable commutant.
It is not equality of the Hamiltonians, their spectra or all matrix elements,
and it is not permission to change a prescribed physical operator. The
shifted-gapless-spectrum theorem concerns the separately defined shifted model.
:::

```
#check @BookProof.MassGap.numberOp
#check @BookProof.MassGap.heisenberg_number_shift_invariant
#check @BookProof.MassGap.shiftedSpectrum_vacuum
#check @BookProof.MassGap.shiftedSpectrum_excited
#check @BookProof.MassGap.massGap_shifted_gapless
```

:::paragraph
The positivity proofs in
{ref "quantization-time-evolution"}[the quantization chapter] apply to their
specified operators. Positivity alone need not be strict. For the nested-Fock
record, $`d\Gamma(h+cI)=d\Gamma(h)+cN_{\rm out}`: an inner constant changes
occupied outer sectors, even though the outer vacuum still has zero energy.
A gauge choice cannot silently absorb that change.
:::

# Reading the Numerical Comparisons

:::paragraph
The final operator is the outer enclosure of the complete inner operator,
$`H=\sum_{i,j}C^\dagger(e_i)h_{ij}A(e_j)`, with every inner constant and
interaction retained. Its outer vacuum is annihilated by the rightmost operator.
To call it a ground requires $`h\ge0`; to establish a strict vacuum gap
requires an absolute positive inner lower bound. An inner excitation gap or a
shifted finite Ritz minimum is a different statement.
:::

:::paragraph
The companion `unfer` corpus contains gauge-fixed QYM computations, abelian
soft-mode controls, lattice comparison benchmarks and finite SM constraint
probes. Their model labels matter. A lattice electric occupation gap, a
reflection-parity gap and a full gauge-fixed one-particle lower bound do not
measure the same object. Historical numerical values are documented evidence,
not new runs in this book revision. The
{ref "sirk-reliability"}[reliability chapter] explains the applicable residual,
full-action and spectral-exclusion requirements.
:::

:::paragraph
Comprehensive fixing prevents orbit loss at the set level; it does not certify
a numerical window. A window must retain the relevant action or bound its
missing images. The SM density probe deliberately lacks a full nilpotent
charge, while its 44-state longitudinal band leaks under the full operator.
Those observations motivate a better physical-reduction construction rather
than supplying a physical spectrum. See
{ref "gauge-symmetry"}[the current gauge-fixing evidence] and
`../unfer/docs/SM_RESEARCH_PLAN.md` N7–N10.
:::

# What the Topology Theorem Actually Excludes

:::paragraph
Classical choice supplies an orbit representative set. The available topology
theorem excludes a *clopen* complete comprehensive subset for a nontrivial free
action on a nonempty preconnected carrier. It does not exclude every smooth
slice or continuous representative map, and does not construct a global
nonabelian field-space gauge fixing. The comprehensive but incomplete approach
keeps all orbits and the compatibility conditions on their observables. The
next analytic tasks are a measurable physical realization, compatible domains
and a dynamics intertwiner.
:::

# The Algebraic-Ideals View of Gauge

:::paragraph
The manuscript describes gauge through a physical observable algebra, excluding
redundant generators from the observables. The available orbit theorem states
that invariant functions factor through the orbit quotient. A comprehensive
fixing retains these functions faithfully even when it retains multiple points
per orbit. This is the useful algebraic content. A literal ideal quotient,
a commutant and a BRST state cohomology are distinct constructions; an
identification among them requires a map and a proof.
:::

# Scope of the Results

The abelian curl identities, set-level orbit theorems and conditional
number-shift equality are reusable. For the full field theory, one still needs
the concrete measure and physical-state construction, a positive physical
metric, compatible closed dynamics and a certificate for the specified operator.
These obligations remain visible in {ref "proof-plans"}[the specialist plan].
