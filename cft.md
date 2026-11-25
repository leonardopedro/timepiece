"A: If you look into www.airma.de , I can prove existence and do rigorous numerical approximationsto observables in the timepiece approach. However, for the mass gap the rigorous maximum approximation uncertainty is always too big (unlike for most observables, where it converges). Could Balaban's approach combined with the work already done in the Timepiece approach, prove the mass gap?
B: Also, in book.tex it is discussed how an artificial (non-physical) mass gap can be introduced in the theory (can be easily proved) by adding another layer to the nested Fock-space and shifting the ground state of the new layer (using the fact that the number operator commutes with the one-free-particle version of the Hamiltonian). While this has no interest for pphysics directly, it does satisfy formally the conditions of the Millenium Prize. I am not expecting to be given the prize for this trivial proof of the mass gap. However, the Prize exists also because a proof of the mass gap is relevant for formal reasons, to prove  relevant properties of constructive field theory (including Balaban's approach, most likely). How can this artificial mass gap be used to prove some of those relevant properties that need a mass gap in the theory?"

## A. What a Bałaban comparison could establish

The October archive proves existence of a Wilson hierarchy along an allowed
refinement. It supplies a selected reconstruction, separated OPE and trace data.
A positive mass gap and uniqueness across admissible continuum realizations remain
open. For the nested theory, first match the gauge-invariant smeared observables,
state, positive-time form and semigroup of one such realization.
[Formalization plan](cftproof.md) · [Archive statement](../OpenAI-YM-20261028/ChallengeSpec.lean)

The scale distinction matters for Temple's inequality. Integrating short-distance
fluctuations controls ultraviolet errors. A lower bound on the *next* spectral
edge above a trial Rayleigh quotient requires a separate infrared estimate on the
physical space. Coarse graining alone gives no value for that denominator. One
possible route is to bound the complementary form, price its coupling to the
retained Mehler packets and certify the ordered low spectral edges. The packets
are functions of continuous momentum. The Wilson lattice occurs in the comparison
used to construct Euclidean correlations.

For a strong coupling at a specified physical scale, the acceptance test is a mass
estimate greater than its entire error in energy units. The bound must cover every
admitted Krylov rank and account for omitted low-energy states. An absolute bound
on the complete inner Hamiltonian lifts to a gap above the empty outer vacuum.
A gap relative to a populated physical ground transfers to the selected reconstructed
theory only through its ground projection and generator. The artificial number
shift discussed in B changes the energies of occupied outer sectors.
[Spectral work order](softmodes.md) · [Scope of the conditional theorems](CFT_REVIEW.md)

## B. What the artificial number shift controls

For the nested Hamiltonian $H=d\Gamma(h)$, adding $\mu N_{\rm out}$ lifts the inner
shift $h+\mu I$. On the sector with $n$ outer quanta it adds the constant $n\mu$.
Within that sector excitation spacings and the Temple denominator $\beta-\theta$
are unchanged. For number-preserving observables the associated phase cancels in
Heisenberg evolution under the stated commutation and domain hypotheses. This is a
useful control for the solver and for transporting such observables.

If $H$ is nonnegative, the shifted heat semigroup on the complement of the empty
outer vacuum has norm at most $e^{-t\mu}$, and the shifted inverse there has norm
at most $1/\mu$. These are estimates on the modified generator. At fixed populated
occupation the same shift cancels again upon subtracting the reference ground
energy. One must bound the *unshifted* complement to infer a physical mass gap.

For the Wilson comparison, estimates on gauge-invariant connected correlations must
hold in the selected physical state and survive the mesh and volume limits.
Temporal damping for a shifted operator alone supplies neither those estimates nor
spatial clustering, an isolated relativistic mass shell, or a convergent polymer
expansion. Such conclusions require their own covariance, locality and uniform
multiscale bounds. [Review of the artificial shift](CFT_REVIEW.md)
