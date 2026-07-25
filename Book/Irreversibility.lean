import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Irreversibility: Injective but Not Surjective" =>
%%%
tag := "irreversibility"
%%%

# What "Irreversible" Means, Precisely

A deterministic time-evolution is a function $`f` from the state space to itself.
It is **reversible** exactly when $`f` is a bijection: every state has a unique
predecessor, so the past can be reconstructed from the present. It is
**irreversible** when the past is lost — when $`f` is **injective but not
surjective**: distinct states stay distinct (no two histories merge), but some
states have no predecessor (the dynamics has a "missing past").

The manuscript's claim is that a dissipative deterministic dynamics is exactly this:
injective, not surjective, and hence time-asymmetric.

# A Finite World Cannot Be Irreversible

There is a sharp dichotomy. On a **finite** state space, injectivity already forces
surjectivity: an injection from a finite set to itself is automatically a bijection
(the pigeonhole principle). So:

```
#check @ChapterIrreversibleDynamics.finite_injective_iff_surjective
#check @ChapterIrreversibleDynamics.finite_no_irreversible
```

There is **no** injective-but-not-surjective self-map of a finite set. A genuinely
irreversible deterministic dynamics is therefore impossible in a purely finite
(discrete, bounded) world. This is the precise form of the manuscript's remark that
"the rationals are not enough": irreversibility requires the **continuum** (an
infinite, Dedekind-infinite state space).

# The Continuum Admits Irreversibility

On an infinite state space the dichotomy breaks. There always exists an injective,
non-surjective self-map; the simplest is the successor $`n \mapsto n+1` on
$`\mathbb{N}`, which misses $`0`:

```
#check @ChapterIrreversibleDynamics.exists_injective_not_surjective
#check @ChapterIrreversibleDynamics.nat_succ_injective_not_surjective
```

# A Concrete Dissipative Map on the Interval

The manuscript needs more than mere non-surjectivity: it needs a **non-singular,
dissipative** map. The model example is the halving map

$$`f : [0,1] \to [0,1], \qquad f(x) = x/2.`

It has all the required properties at once:

 * **Injective** — distinct inputs give distinct outputs.
 * **Not surjective** — the value $`1` (indeed anything in $`(1/2, 1]`) is never
   reached; the past of those states is missing.
 * **Dissipative** — it sends an interval $`[a,b]` to $`[a/2, b/2]`, **halving** its
   Lebesgue length.
 * **Non-singular** — a set of positive length is sent to a set of positive (halved)
   length; null sets stay null and positive-measure sets stay positive-measure.

The verified statements (module `BookProof.ChapterIrreversibleDynamics`):

```
#check @ChapterIrreversibleDynamics.dissipative_injective
#check @ChapterIrreversibleDynamics.dissipative_not_surjective_unitInterval
#check @ChapterIrreversibleDynamics.dissipative_volume_Icc
#check @ChapterIrreversibleDynamics.dissipative_nonsingular_Icc
```

# The Arrow of Time From Pure Set Theory

The conclusion is striking: the **arrow of time** — the fact that the future is
determined but the past is not recoverable — needs no thermodynamics to appear at
the kinematic level. It is forced the moment a deterministic dynamics on a continuum
is dissipative (volume-contracting): such a map is injective but cannot be
surjective, so it has a built-in time asymmetry. The next two chapters quantify how
_generic_ this is (a random map is almost surely non-invertible) and how it coexists
with the measure-theoretic subtleties (null-measure sets) that the continuum
introduces.
