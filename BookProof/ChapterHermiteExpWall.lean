import BookProof.ChapterHermiteExpWall.Part1
import BookProof.ChapterHermiteExpWall.Part2

/-!
# The exponential wall is not a relatively bounded perturbation (plan §10.6.1, target 2)

`CONSOLIDATED_PLAN.md` §10.6.1 target 2 proposes to obtain essential self-adjointness of
the one-particle scalaron Hamiltonian on the Gauss–polynomial (Hermite) core by a
Kato–Rellich argument: *"`V(φ)` is `(−Δ)`-bounded with arbitrarily small relative bound on
the Gauss core"*.  The plan itself flags that this target "needs restating".  This module
proves that it is in fact **false**, in the strongest sense: the scalaron potential is not
relatively bounded on the Hermite core with respect to the kinetic term, nor with respect
to the harmonic (conformal-mode) oscillator `−Δ + x²/4` — not with a small relative bound,
and not with *any* pair of constants.

## The mechanism

On the monomial core elements `ψ_N(x) = x^N e^{−x²/4}` the reference operators grow only
polynomially in `N`, because they act on the core by polynomial maps of fixed degree
increment:

* `osc_psi` — `(−d²/dx² + x²/4)(x^N e^{−x²/4}) = ((N + ½)x^N − N(N−1)x^{N−2})e^{−x²/4}`,
  so `‖H₀ψ_N‖ ≤ (N² + 1)‖ψ_N‖` (`l2_osc_le`);
* `neg_deriv2_psi` — `−d²/dx²(x^N e^{−x²/4}) = ((N + ½)x^N − N(N−1)x^{N−2} − ¼x^{N+2})e^{−x²/4}`,
  so `‖−ψ_N''‖ ≤ (N² + 1)‖ψ_N‖` (`l2_kin_le`).

The exponential wall, on the other hand, grows *super-polynomially* along the same family.
The quadratic form of the potential is an exponentially tilted Gaussian moment, and
expanding the tilt to eighth order gives

* `gaussMoment_tilt_ge` — `∫ e^{−2sx}x^{2N}e^{−x²/2}dx ≥ (2s⁸/315)·M_{2N+8}`,
* `gaussMoment_shift_eight` — `M_{2N+8} = (2N+7)(2N+5)(2N+3)(2N+1)·M_{2N}`,

hence `⟪ψ_N, Vψ_N⟫ ≥ c₀(K N⁴ − 1)‖ψ_N‖²` with `K = 8s⁸/315` (`quadForm_scalaron_ge`), and
Cauchy–Schwarz turns this into `‖Vψ_N‖ ≥ c₀(K N⁴ − 1)‖ψ_N‖` (`l2_scalaron_ge`).  A quartic
lower bound against a cubic upper bound is the contradiction.

## What is proved

* `not_relatively_bounded_of_cubic` — the abstract form: no operator whose norm along the
  monomial family grows at most cubically can dominate the scalaron potential;
* **`scalaronV_not_kinetic_relativelyBounded`** — there are **no** constants `a, b` with
  `‖Vψ‖ ≤ a‖ψ''‖ + b‖ψ‖` for all Gauss polynomials `ψ`;
* **`scalaronV_not_oscillator_relativelyBounded`** — there are **no** constants `a, b` with
  `‖Vψ‖ ≤ a‖(−Δ + x²/4)ψ‖ + b‖ψ‖` for all Gauss polynomials `ψ`.

Consequently the Kato–Rellich route of §10.6.1 target 2 — and, a fortiori, the
"arbitrarily small relative bound" it asks for — cannot be taken for the exponential wall,
either against the free kinetic term or against the conformal-mode oscillator whose Hermite
functions define the core.  This is a genuine obstruction, not a gap in the argument: it is
why `BookProof.ChapterQgHermiteOscillatorEsa` can only reach *bounded* perturbations of the
oscillator by Kato–Rellich, and why the exponential case in
`BookProof.ChapterScalaronHermiteEsa` had to be handled by a Fourier/moment argument
instead.

Everything is `sorry`-free and `axiom`-free.
-/
