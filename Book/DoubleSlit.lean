import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The Double-Slit Experiment" =>
%%%
tag := "double-slit"
%%%

# The Puzzle

The ensemble interpretation, by itself, does not explain why an electron's
wave-function appears to **interfere with itself** in Young's double-slit experiment
— that would seem to require the wave-function to describe an _individual_ system.
This chapter fills the gap using the result of
{ref "time-translation-stochastic"}[the previous chapter]: the time-evolution is a
stochastic process only when it is deterministic.

# The Two Transformations

After the electron is fired (call this instant $`S_1`), its evolution to the
detector ($`F`) is the product of **two** non-deterministic symmetry
transformations:

 * $`S_1 \to S_2`: passing through one slit or the other, with probability
   $`50/50`;
 * $`S_2 \to F`: a non-deterministic propagation from the slits to the screen.

Because **both** transformations are non-deterministic, the theorem of the previous
chapter says that no stochastic process can be defined through the intermediate
instant $`S_2`. The only stochastic process that exists connects $`S_1` directly to
$`F`; the transformations through $`S_2` "never occurred" as a sequence of random
events. This is why one cannot say which slit the electron went through.

# A Two-by-Two Model

Restrict to the electrons that reach the detector along one of two angles. The
wave-function at $`S_1` is

$$`\Psi = \begin{pmatrix} 1 \\ 0 \end{pmatrix}.`

The propagation from the slits to the screen is the **Hadamard** matrix, which adds
the two slit-amplitudes for the first angle and subtracts them for the second:

$$`H = \frac{1}{\sqrt 2}\begin{pmatrix} 1 & 1 \\ 1 & -1 \end{pmatrix}.`

The verified properties of $`H` (module `BookProof.ChapterDoubleSlit`):

```
#check @ChapterDoubleSlit.H_unitary
#check @ChapterDoubleSlit.H_involutive
#check @ChapterDoubleSlit.Hpsi0
```

The matrix is unitary (probability-conserving) and **involutive**: $`H^2 = \mathbf 1`.
Acting once on $`\Psi` it produces the balanced superposition
$`H\Psi = \tfrac{1}{\sqrt 2}(1,1)`.

# One Slit Closed: 50/50

With the second slit **closed**, only the propagation $`S_2 \to F` acts, so the
state at the screen is $`H\Psi = \tfrac{1}{\sqrt 2}(1,1)`. Born's rule gives equal
probability for the two angles:

```
#check @ChapterDoubleSlit.slit_closed_born
```

# Both Slits Open: 100/0

With the second slit **open**, both transformations act: first $`S_1 \to S_2`
(which is again $`H`, putting the electron into an equal superposition of the two
slits), then $`S_2 \to F` (another $`H`). The state at the screen is

$$`H\,(H\Psi) = H^2 \Psi = \Psi = \begin{pmatrix} 1 \\ 0 \end{pmatrix},`

because $`H` is involutive. Born's rule now gives probability $`1` for the first
angle and $`0` for the second:

```
#check @ChapterDoubleSlit.slit_open_state
#check @ChapterDoubleSlit.slit_open_born
```

Opening the second slit has turned a $`50/50` distribution into a $`100/0`
distribution. The first angle is **constructive** interference (the two
slit-amplitudes add), the second **destructive** (they cancel).

# Where the Mystery Goes

The "mystery" is the same as for the probability clock: how can $`50/50` become
$`100/0`? The answer is that $`H \cdot H` is **not** a stochastic process in which
$`H` is applied and then $`H` is applied again with a collapse in between. If one
_collapses_ after the first $`H` (i.e. actually measures which slit), the
interference is destroyed and one recovers $`50/50`. The coherent product $`H^2` and
the incoherent sequence give different answers, and there is no reason they should
agree — because time plays no fundamental role, and there is no probability
distribution at the intermediate instant $`S_2`.

The verified contrast between the coherent and the incoherent composition (module
`BookProof.ChapterTrajectory`):

```
#check @ChapterTrajectory.jointProb_sum_final_eq_midProb
#check @ChapterTrajectory.dslit_finalProb
#check @ChapterTrajectory.dslit_coherentFinal
```

The first says that if one _does_ record the intermediate outcome (summing the joint
probabilities over the final index), one recovers the middle distribution. The
second, `dslit_finalProb`, is the **collapsed** (incoherent) final law: once the
intermediate measurement is made, the outcome is uniform $`50/50`. The third,
`dslit_coherentFinal`, is the **coherent** double-slit result: without intermediate
measurement, the state is $`(1,0)`. The difference between them is exactly the
interference cross term — present in the coherent product, erased by the
intermediate measurement.

# Summary

 * The electron's evolution is a product of two non-deterministic transformations, so
   no stochastic process exists through the slits; "which slit?" has no answer.
 * In a two-angle model the propagation is the involutive Hadamard $`H`.
 * One slit closed: state $`H\Psi`, giving $`50/50` at the two angles.
 * Both slits open: state $`H^2\Psi = \Psi`, giving $`100/0` — constructive and
   destructive interference.
 * The coherent product $`H^2` differs from an incoherent, measured sequence; the
   difference is the interference cross term.
