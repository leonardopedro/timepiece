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
and number-shift identities are verified, whereas a global non-abelian gauge-fixing
and a continuum Yang--Mills mass-gap theorem are not yet formalized.

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
The Gribov ambiguity is a problem of *non-abelian* gauge fixing: the Dirac
bracket requires a gauge-fixing that is both complete and unconstrained, which is
not always possible. In the *abelian* (electromagnetic) case the situation is
clean. The field strength is the linear curl
$`F_{jk} = \delta_j A_k - \delta_k A_j`, which is *gauge invariant* — invariant
under $`A_j \mapsto A_j + \partial_j\theta`, the curl of a gradient vanishing by
commutativity of the partial derivatives. This is the manuscript's "no Gribov
ambiguity" for the abelian theory:
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
The manuscript's mass-gap discussion rests on a subtle point: the number operator
$`N` commutes with the observable algebra, so one can add $`\lambda N` to the
Hamiltonian $`H` without changing any observable consequence. The verified content
is that Heisenberg evolution under $`H + \lambda N` equals that under $`H` — the
mass-gap shift has no observable consequence — and that for a gapless free field
the shifted mass gap equals $`\lambda` (arbitrary):
:::

```
#check @BookProof.MassGap.numberOp
#check @BookProof.MassGap.heisenberg_number_shift_invariant
#check @BookProof.MassGap.shiftedSpectrum_vacuum
#check @BookProof.MassGap.shiftedSpectrum_excited
#check @BookProof.MassGap.massGap_shifted_gapless
```

:::paragraph
The manuscript connects this to the positive-definiteness of the Weyl-gauge
Hamiltonian (verified in
{ref "quantization-time-evolution"}[the quantization chapter]): the mass gap is
read off a positive operator, and the number-operator shift is unobservable.
:::

# The Mass Gap in the Numerical Validation

The mass-gap discussion above is not only a formal statement about Heisenberg
evolution: it is exactly the quantity the companion numerical validation measures.
The free gluon one-particle operator is *gapless* — its lowest one-gluon
energy tends to $`0` as $`k \to 0`. The final free-field Hamiltonian used for
full nested-Fock interpretation is its outer enclosure
$`H = \sum_{i,j} h_{ij} C_i^\dagger A_j`, and the numerical suite confirms
the one-particle soft-mode energy is below $`0.02` in the solver's units. By
contrast, the comparison-model lattice Hamiltonian, whose electric term
$`(g^2/2)\sum n_\ell` is a genuine number operator, has a *positive* even-to-odd
gap of $`\approx g^2/2` in the strong-coupling limit — a comparison-model lattice benchmark, not the final gauge-fixed nested-Fock
Hamiltonian and not a Millennium-Prize confinement proof. The two regimes
are separate validation models, while the final-theory statement is the outer
creation/annihilation enclosure described above: the free field is gapless
because its spectrum is the continuous line $`|k| \ge 0`, while the number-operator
shift $`\lambda N` — unobservable, as `heisenberg_number_shift_invariant` shows —
is precisely what creates a gap when it is the *electric* term of a confined
theory. The same contrast, between a gapless free field and a gapped confined
one, is what the SIRK cross-sector solve reproduces numerically. For the
physical theory discussed in the current validation, however, the final
Hamiltonian is the gauge-fixed one-particle operator enclosed at the outer level
with creation on the left and annihilation on the right. Its outer vacuum is
therefore the exact ground after the permitted one-particle shift; a parity or
squeezed inner-sector result is not a replacement for that conclusion.

# The Algebraic-Ideals View of Gauge

:::paragraph
The manuscript's distinctive proposal is that gauge symmetries are defined through
*algebraic ideals* — the gauge generators are excluded from the physical
(gauge-invariant) algebra rather than being imposed as constraints on a larger
phase-space. The verified seed of this idea is the constraint-conservation
identity: a constraint $`D` that commutes with the Hamiltonian is conserved by the
flow (see {ref "gauge-symmetry"}[the gauge chapter]). The Gribov ambiguity is
precisely the statement that no gauge-fixing can be simultaneously complete and
unconstrained in general; the abelian case above is the exceptional case where it
can be.
:::

# Summary

The algebraic core of the manuscript's Gribov-ambiguity chapter:

 * the abelian field strength is gauge invariant (the "no Gribov ambiguity" case);
 * the non-abelian field strength reduces to the abelian one when the connection commutes;
 * the curl of self-adjoint operator fields is self-adjoint;
 * the mass-gap shift by the number operator is unobservable (Heisenberg-invariant), and the Weyl-gauge Hamiltonian is positive.