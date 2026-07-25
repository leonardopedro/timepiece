import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "The Born Rule Reproduces Every Distribution" =>
%%%
tag := "born-reproduces"
%%%

# From Two States to n States

The probability clock parametrized a two-outcome distribution by one angle. The
same idea extends to any finite number $`n` of outcomes using
$`n-1` **Euler angles** $`\theta_0, \dots, \theta_{n-2}`. The construction is a
telescoping **stick-breaking** process: at step $`k` we break off a fraction
$`\cos^2\theta_k` of the probability mass that remains, and pass the rest
$`\sin^2\theta_k` onward.

Concretely, define the **tail product** (the mass still unassigned before outcome
$`m`)

$$`T(\theta, m) = \prod_{i < m} \sin^2 \theta_i,`

and the **Born probability** of outcome $`k`

$$`\mathrm{bornProb}(\theta, n, k) = T(\theta, k)\,\cos^2\theta_k = \Big(\prod_{i<k}\sin^2\theta_i\Big)\cos^2\theta_k,`

with the last outcome $`k = n-1` carrying the remaining product of sines (no cosine
factor).

# It Always Sums to One

The first thing to check is that this really is a probability distribution, for
_every_ choice of angles. The proof is a telescoping sum: since
$`\cos^2\theta_k = 1 - \sin^2\theta_k`, the partial sums collapse:

$$`\sum_{k < n} \mathrm{bornProb}(\theta, n, k) = 1 - T(\theta, n) + T(\theta,n)\cdot(\text{last term}) = 1.`

The verified statement (module `BookProof.ChapterEulerNState`):

```
#check @ChapterEulerNState.euler_sum_one
#check @ChapterEulerNState.euler_wave_unit
```

The second of these says the underlying **Euler wave-function**
$`\varphi_k = (\prod_{i<k}\sin\theta_i)\cos\theta_k` is a **unit vector**,
$`\sum_k \varphi_k^2 = 1`; the Born probabilities are its squared coordinates
$`\mathrm{bornProb} = \varphi_k^2`.

# It Reaches Every Distribution

The converse is the substantive claim: **every** probability distribution on
$`n` outcomes arises this way. Given $`p_0, \dots, p_{n-1} \ge 0` summing to one,
choose the angles backwards from the tail. The key elementary fact is that every
number in $`[0,1]` is a $`\cos^2` (and a $`\sin^2`) of some angle:

```
#check @ChapterEulerNState.exists_cos_sq
```

Setting $`\cos^2\theta_k = p_k / T(\theta,k)` — the fraction of the _remaining_ mass
that outcome $`k` should carry — reproduces $`p` exactly:

```
#check @ChapterEulerNState.euler_reproduces
```

This is the finite-dimensional heart of the book's thesis: the Born-rule
parametrization is **surjective** onto the simplex. No distribution is left out.

# The Countable Case: an Infinite Stick-Breaking Chain

The manuscript emphasizes that "the recursion does not need to stop." For a
**countably infinite** partition, write the conditional probabilities
$`c_n = P(n \mid n \text{ or above}) \in [0,1]` and define

$$`T(c, N) = \prod_{k < N} (1 - c_k), \qquad P(n) = T(c,n)\, c_n.`

The same telescoping gives the exact finite normalization

$$`\sum_{n < N} P(n) = 1 - T(c, N),`

and if the tail $`T(c,N) \to 0` (the stick is eventually fully broken), the point
masses sum to exactly one:

```
#check @ChapterEulerCountableChain.partial_sum
#check @ChapterEulerCountableChain.stick_tsum_one
```

Writing $`c_n = \cos^2\theta_n` recovers the Euler-angle form
$`P(n) = (\prod_{k<n}\sin^2\theta_k)\cos^2\theta_n`, the countable analogue of the
finite formula:

```
#check @ChapterEulerCountableChain.euler_tsum_one
```

# Complex and Quaternionic Wave-functions

So far the wave-function has been real. Over the **complex** numbers, the Born
probability of coordinate $`k` is $`|v_k|^2 = (\operatorname{Re} v_k)^2 + (\operatorname{Im} v_k)^2`:
a complex wave-function is just a real one on a state space with **twice** as many
outcomes, and its Born probability is the sum of the two real Born probabilities.
The manuscript's quaternionic case is the same with **four** real coordinates,
$`P(n) = \sum_{m=1}^{4} P(n,m)`:

```
#check @ChapterEulerComplexQuat.complex_born_split
#check @ChapterEulerComplexQuat.quat_born_split
```

And the surjectivity survives: every distribution is still reproduced by a complex
(resp. quaternionic) unit wave-function:

```
#check @ChapterEulerComplexQuat.complex_reproduces
#check @ChapterEulerComplexQuat.quat_reproduces
```

This justifies the book's use of complex (and quaternionic) Hilbert spaces while
keeping the real Euler-angle parametrization as the underlying construction: passing
to $`\mathbb{C}` or $`\mathbb{H}` does not change which distributions are
reachable, only how many real coordinates each outcome hides.
