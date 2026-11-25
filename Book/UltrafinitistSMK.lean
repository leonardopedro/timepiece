import VersoManual

open Verso.Genre Manual
open Verso.Genre.Manual.InlineLean

#doc (Manual) "Ultrafinitist Solovay–Mehler–Kopperman Theory" =>
%%%
tag := "ultrafinitist-smk"
%%%

# Orientation: From Decidable to Ultrafinitist

The foundation laid in {ref "pa-free-chapter"}[Completeness without Peano Arithmetic],
{ref "solovay-tensor"}[the Solovay–Kopperman tensor product], and
{ref "statistical-model-theory"}[statistical model theory] is _decidable_ in its pure
geometric fragment, but it is *not ultrafinitist*. Five structural features still rely
on actual infinity or super-polynomial resources:

1. *Hilbert's Hotel in the tail:* `tailTensorEquiv_map` ($`\Gamma \otimes \Gamma \cong \Gamma`)
   and `enlargeEquiv_map` ($`N \mapsto N+k`) duplicate and consume infinite coordinates at
   zero resource cost.
2. *Actual limits and uncountable scalars:* the infinite product $`(\mathbb{R}^{\mathbb{N}}, \gamma)`
   takes the $`d \to \infty` Mehler limit over uncountable $`\mathbb{R}` and passes to a
   Cauchy completion.
3. *Non-elementary decision complexity:* full first-order real-closed-field decision
   (Tarski / Solovay–Arthan–Harrison) has a doubly exponential $`2^{2^{\Omega(q)}}` lower
   bound in quantifier alternations $`q`.
4. *Unbounded ladder algebra:* the canonical commutation relation $`[a, a^\dagger] = I`
   forces unbounded operators (the Wintner–Wielandt obstruction).
5. *Sorites inconsistency under idempotent logic:* sharp projections ($`P^2 = P`) cannot
   support a locally stable feasibility predicate without contradiction.

This chapter derives an *Ultrafinitist Solovay–Mehler–Kopperman theory*
($`\mathrm{U\text{-}SMK}`) directly from those ingredients by replacing the
$`M, D \to \infty` limit with a strictly finite dyadic pre-limit and replacing sharp
projections with Mehler-damped effects. The entire formal development lives in the
self-contained `BookProof/Ultrafinitism/` component (`sorry`-free and custom-axiom-free).

# The Strictly Finite Krawtchouk–Mehler Tail

Fix a coordinate capacity $`R \in \mathbb{N}` and a microscopic block width $`M = 4^q`
($`q \in \mathbb{N}`). Instead of $`\mathbb{R}^{\mathbb{N}}` with the infinite product
Gaussian $`\gamma`, each tail coordinate lives on the finite Boolean hypercube
$`\Omega_M = \{-1, +1\}^M` (`BitCube M`) with the uniform rational expectation
$`\mathbb{E}_M` (`cubeExpect M`). Every point $`\xi \in \Omega_M^R` has exact norm
squared $`RM`, yet distinct coordinate blocks are strictly independent.

For $`M = 4^q`, $`\sqrt{M} = 2^q` is an integer, so the scaled coordinate sum
$`Z^{(q)}(\xi) = 2^{-q}\sum_{i=1}^{4^q} \xi_i` (`dyadicGauss q`) takes only exact
dyadic rational values, with exact mean $`0`, exact variance $`1`, and exact fourth
moment $`3 - 2/4^q`. No real numbers, $`\pi`, $`e^{-x^2}`, or metric completion are used.

```
#check @BookProof.Ultrafinitism.ChapterKrawtchoukTail.dyadicGauss_mean
#check @BookProof.Ultrafinitism.ChapterKrawtchoukTail.dyadicGauss_variance
#check @BookProof.Ultrafinitism.ChapterKrawtchoukTail.dyadicGauss_fourth_moment
```

Replacing the continuous Hermite polynomials are the *unnormalized Krawtchouk modes*
$`K_n^{(M)}` (`krawtchouk M n`), defined as sums of degree-$`n` Walsh characters
`walsh S`. They vanish identically above the degree horizon $`n > M` (`krawtchouk_gt`),
satisfy exact integer orthogonality with squared norm $`\binom{M}{n}`, and obey the exact
finite-horizon ladder identity:

$$`K_1^{(M)}\,K_{n+1}^{(M)} = (n+2)\,K_{n+2}^{(M)} + (M - n)\,K_n^{(M)}.`

Because every factor is an integer, multiplying polynomials closes strictly inside
degrees $`0 \le n \le M` over $`\mathbb{Q}`. Moreover, the Bonami–Beckner bit-flip channel
`discreteMehler M ρ` is a self-adjoint Markov semigroup whose exact eigenfunctions are
the Krawtchouk modes, with eigenvalues $`\rho^n`.

```
#check @BookProof.Ultrafinitism.ChapterKrawtchoukTail.walsh_inner
#check @BookProof.Ultrafinitism.ChapterKrawtchoukTail.krawtchouk_inner
#check @BookProof.Ultrafinitism.ChapterKrawtchoukTail.krawtchouk_gt
#check @BookProof.Ultrafinitism.ChapterKrawtchoukTail.krawtchouk_one_mul_succ
#check @BookProof.Ultrafinitism.ChapterKrawtchoukTail.discreteMehler_krawtchouk
#check @BookProof.Ultrafinitism.ChapterKrawtchoukTail.discreteMehler_selfAdjoint
#check @BookProof.Ultrafinitism.ChapterKrawtchoukTail.discreteMehler_comp
```

# Deformed CCR and Resolution of Wintner–Wielandt

On the $`(M+1)`-dimensional Krawtchouk degree space, the finite-horizon ladder factor
$`c_n = \sqrt{(n+1)(1 - n/M)}` (`ladderCoeff M n`) defines bounded adjoint ladder
operators `creOp M` ($`a_M^\dagger`) and `annOp M` ($`a_M`). Creation automatically halts
at the ceiling $`n = M` (`creOp_top`), both operators have norm squared bounded by
$`M + 1`, and they satisfy the *deformed canonical commutation relation*:

$$`[a_M, a_M^\dagger] = I - \frac{2}{M}\,\hat{N}.`

Taking the trace over $`0 \le k \le M` gives $`\sum_{k=0}^M (1 - 2k/M) = 0` identically
(`trace_deformed_ccr_eq_zero`), dissolving the Wintner–Wielandt obstruction (`ChapterCcrNoBounded`).
On every feasible grade $`k \le d \ll M`, the commutator defect from $`I` is bounded
explicitly by $`2d/M` (`deformed_ccr_defect_bound`).

```
#check @BookProof.Ultrafinitism.ChapterDeformedCCR.annOp_vac
#check @BookProof.Ultrafinitism.ChapterDeformedCCR.creOp_top
#check @BookProof.Ultrafinitism.ChapterDeformedCCR.dot_creOp_eq_dot_annOp
#check @BookProof.Ultrafinitism.ChapterDeformedCCR.deformed_ccr
#check @BookProof.Ultrafinitism.ChapterDeformedCCR.trace_deformed_ccr_eq_zero
#check @BookProof.Ultrafinitism.ChapterDeformedCCR.deformed_ccr_defect_bound
#check @BookProof.Ultrafinitism.ChapterDeformedCCR.creOp_norm_sq_le
#check @BookProof.Ultrafinitism.ChapterDeformedCCR.annOp_norm_sq_le
```

# Resource-Accounting Tensor Product and No Hilbert's Hotel

In $`\mathrm{U\text{-}SMK}`, every system carries an explicit tail coordinate budget
$`R \in \mathbb{N}`: the carrier is $`X \times \Omega_M^R` (`X × MultiTail R M`), with
an arbitrary rational probability `FiniteProb X` on the head and the uniform dyadic
Gaussian law on the tail.

* *Head-only decoupling:* inner products of head-only observables eliminate the entire
  $`R`-coordinate tail in $`O(1)` (`ultra_inner_reduces_to_head`).
* *Budget-consuming enlargement:* peeling $`k` Gaussian coordinates from a tail of
  capacity $`k + R` leaves a residual tail of capacity $`R` while conserving total
  coordinates (`ultra_enlarge_expect_eq`).
* *Additive-budget tensor product:* combining systems of capacities $`R_1` and $`R_2`
  adds their tail budgets to $`R_1 + R_2`, and pure-tensor inner products multiply
  (`ultra_tensor_expect_eq`, `ultra_tensor_inner_mul`).
* *No Hilbert's Hotel:* whenever $`M > 0` and $`R_2 > 0`, no bijection exists between
  `MultiTail (R₁ + R₂) M` and `MultiTail R₁ M` (`no_hilbert_hotel_tail`).
* *Low-degree indistinguishability:* any two finite laws agreeing on a bounded
  observable basis yield identical expectations across its linear span
  (`low_degree_indistinguishable`).

```
#check @BookProof.Ultrafinitism.ChapterUltrafinitistTensor.tailExpect_split
#check @BookProof.Ultrafinitism.ChapterUltrafinitistTensor.ultra_inner_reduces_to_head
#check @BookProof.Ultrafinitism.ChapterUltrafinitistTensor.ultra_enlarge_expect_eq
#check @BookProof.Ultrafinitism.ChapterUltrafinitistTensor.ultra_tensor_expect_eq
#check @BookProof.Ultrafinitism.ChapterUltrafinitistTensor.ultra_tensor_inner_mul
#check @BookProof.Ultrafinitism.ChapterUltrafinitistTensor.no_hilbert_hotel_tail
#check @BookProof.Ultrafinitism.ChapterUltrafinitistTensor.low_degree_indistinguishable
```

# Feasible Polynomial-Time Gram Decidability

Instead of unbounded quantifier alternations in real closed fields, a finite-channel
rational query over $`m` vectors in a residual subspace of capacity $`R` asks whether a
symmetric rational $`m \times m` Gram matrix $`G \in \mathbb{Q}^{m \times m}` is positive
semidefinite of rank at most $`R` (`HasBoundedGramFactor G R`).

The computable function `decideGram G R` runs $`O(m^3)` rational Schur-complement
elimination over $`\mathbb{Q}` (zero square roots, zero floating point). Both
*soundness* (`decideGram_sound`) and *completeness* (`decideGram_complete`) are
proved for every symmetric rational matrix `G`: `decideGram G R = true` holds if and
only if $`G` admits an exact positive-diagonal factorization of rank $`\le R`
(`decideGram_iff`).

Running `decideGram` on the two-channel example from {ref "solovay-tensor"}[the tensor
chapter] reproduces the geometric thresholds while enforcing finite capacity:
$`\left(\begin{smallmatrix}1&3/5\\3/5&1\end{smallmatrix}\right)` passes at capacity
$`R = 2` and fails at $`R = 1`, $`\left(\begin{smallmatrix}1&6/5\\6/5&1\end{smallmatrix}\right)`
fails at every capacity, and the $`3 \times 3` identity fails at capacity $`R = 2`.

```
#check @BookProof.Ultrafinitism.ChapterGramPolyDecision.HasBoundedGramFactor
#check @BookProof.Ultrafinitism.ChapterGramPolyDecision.decideGram
#check @BookProof.Ultrafinitism.ChapterGramPolyDecision.decideGram_sound
#check @BookProof.Ultrafinitism.ChapterGramPolyDecision.decideGram_complete
#check @BookProof.Ultrafinitism.ChapterGramPolyDecision.decideGram_iff
#check @BookProof.Ultrafinitism.ChapterGramPolyDecision.isRatPSD_of_decideGram
#check @BookProof.Ultrafinitism.ChapterGramPolyDecision.twoChannel_three_fifths_rank2
#check @BookProof.Ultrafinitism.ChapterGramPolyDecision.twoChannel_three_fifths_rank1_false
#check @BookProof.Ultrafinitism.ChapterGramPolyDecision.twoChannel_six_fifths_false
#check @BookProof.Ultrafinitism.ChapterGramPolyDecision.id3_gram_rank2_false
```

# Mehler-Damped Feasibility, Sorites Consistency, and Parikh Bounds

Replacing sharp projections (`ModelStatement`) with finite symmetric effects
$`0 \le E \le I` (`FiniteEffect`) turns the discrete Mehler semigroup $`T_\rho`
($`\rho = 1 - \beta`, $`0 < \beta < 1`) into an internal *graded feasibility operator*
`mehlerFeasEffect M (1 - β)`. On grade-$`k` states, its truth value is $`(1 - \beta)^k`.

The theorem `sorites_consistency_theorem` proves that four seemingly conflicting
ultrafinitist requirements hold *simultaneously without contradiction*:
1. grade $`0` has exact truth value $`1`;
2. each step $`n \to n + 1` changes truth value by at most $`\beta`;
3. at every grade $`k \le M`, truth value is bounded by $`(1 + k\beta)^{-1}`;
4. for any detection threshold $`\varepsilon > 0`, every grade
   $`k \ge (\varepsilon^{-1} - 1)/\beta` falls below $`\varepsilon` — dissolving
   smoothly into Gaussian noise long before hitting the hard combinatorial wall $`M`.

Along any deduction chain of $`L` approximate steps with per-step operator error $`\le \beta`,
`parikh_proof_chain_drift` proves that the total truth-value drift is bounded by
$`L\,\beta\,\|v\|^2` — an internal quantitative version of Parikh's proof-length bound.
Finally, `ultraMul` unifies `ChapterFiniteArithmeticPrior` with the Krawtchouk tail:
multiplication is exact inside `[0, B)`, and overflow transitions to `dyadicGauss q`
with certified mean $`0` and variance $`1`.

```
#check @BookProof.Ultrafinitism.ChapterMehlerFeasibility.FiniteEffect
#check @BookProof.Ultrafinitism.ChapterMehlerFeasibility.FiniteEffect.truthVal_not
#check @BookProof.Ultrafinitism.ChapterMehlerFeasibility.finite_approximate_proof_error
#check @BookProof.Ultrafinitism.ChapterMehlerFeasibility.mehlerFeasEffect
#check @BookProof.Ultrafinitism.ChapterMehlerFeasibility.sorites_consistency_theorem
#check @BookProof.Ultrafinitism.ChapterMehlerFeasibility.parikh_proof_chain_drift
#check @BookProof.Ultrafinitism.ChapterMehlerFeasibility.ultraMul
#check @BookProof.Ultrafinitism.ChapterMehlerFeasibility.ultraMul_exact_below
#check @BookProof.Ultrafinitism.ChapterMehlerFeasibility.ultraMul_overflow_moments
```

# Honest Boundary

Everything in `BookProof/Ultrafinitism/` is `sorry`-free and relies only on Lean's
standard axioms (with `ChapterKrawtchoukTail`, `ChapterUltrafinitistTensor`, and the
executable `decideGram` witnesses purely constructive over `ℚ`). The asymptotic
analytic bridge showing convergence of `BitCube M` marginals and Krawtchouk moments to
the continuous Gaussian laws of `ChapterSolovayCoordinates` and `PhysHSGaussian` as
$`M, D \to \infty` (via Berry–Esseen and Diaconis–Freedman) is a separate meta-theoretic
companion task, deliberately kept outside the strictly finite object theory.
