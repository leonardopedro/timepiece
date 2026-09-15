import BookProof.ChapterHermiteGalerkinFriedrichs.Part1
import BookProof.ChapterHermiteGalerkinFriedrichs.Part2

/-!
# The Hermite-basis Galerkin (Rayleigh–Ritz) truncation and the Friedrichs extension

This module formalizes the argument that a Krylov/Galerkin algorithm run in a
complete basis (the Hermite/oscillator basis) does not have to be told which
self-adjoint extension of a semi-bounded symmetric Hamiltonian to use: the
truncation is a Rayleigh–Ritz minimization of the *energy form*, and the
sequence of finite-dimensional energy minimizations converges to the extension
determined by the energy form — the Friedrichs extension.

The informal argument has three steps; here is what each becomes.

**Step 1 (the Rayleigh–Ritz connection).**  Truncating to the span of the first
`m` basis vectors replaces `H` by the compression `Pₘ H Pₘ`, and on that
subspace the compression carries *exactly* the energy form of `H`
(`inner_galerkinCompression`, `quadForm_galerkinCompression`).  The
associated Ritz values are the infima of the energy over unit vectors of the
subspace; they are antitone in `m` (`ritzInf_antitone`) and converge to the
infimum of the energy form over the whole domain
(`ritzInf_tendsto_domainInf`).  Moreover that limit dominates the ground-state
energy of *every* positive self-adjoint extension (`ritzInf_extension_le`), the
extension attaining it being the one whose energy form is the closure of the
form of `H` — the Friedrichs extension.  **No boundedness is used here.**

**Step 2 (the flag exhausts the form domain).**  For the Hermite basis the
domain is the span of the basis vectors, and *every* domain vector already lies
in a finite Galerkin subspace (`exists_mem_galerkinSpan`), while the subspaces
increase to a dense subspace (`galerkinSpan_iSup_dense`), so the projections
converge strongly to the identity (`galerkinProj_tendsto`).  This is the
formal content of "`Pₘ → I` because the Hermite functions are complete", and of
"the finite matrices explore larger and larger subspaces of the energy form".

**Step 3 (the limit is the Friedrichs extension).**  In the regime where the
operator is bounded on its domain — the regime in which the limit of the
truncations exists as an operator, and the only regime claimed here — we prove:

* the compressions converge strongly to the extension
  (`galerkinCompression_tendsto`, `compression_tendsto_of_starProjection_tendsto`);
* the *resolvents* of the truncations converge strongly to the resolvent of the
  extension, for every non-real spectral parameter
  (`resolvent_tendsto_of_strong_tendsto`, `galerkinResolvent_tendsto`) — this is
  the Galerkin/Rayleigh–Ritz strong-resolvent-convergence statement quoted in
  the informal argument;
* the extension so obtained is the **unique** positive self-adjoint extension
  (`positive_selfadjoint_extension_unique`), i.e. the algorithm has no freedom
  left: what it converges to is the Friedrichs extension.

The headline combination is `hermiteGalerkin_selects_friedrichs`.

## Scope — what is *not* claimed

* Everything in Step 3 carries an explicit boundedness hypothesis on the
  operator, exactly as in `BookProof.ChapterYangMillsFriedrichsLimit`.  For a
  genuinely unbounded, non-essentially-self-adjoint operator the identification
  of the Galerkin limit with the Friedrichs extension is **not** proved here;
  only Steps 1 and 2 (the variational content) are unconditional.
* Nothing about the indeterminate Stieltjes moment problem, Padé approximants or
  Nevanlinna-extremal measures is formalized.
* The Hermite basis enters through the property that actually matters — it is a
  Hilbert basis indexed by `ℕ`, so its finite spans increase to a dense
  subspace.  No property of Hermite polynomials beyond completeness and
  orthonormality is used, and the results apply verbatim to any complete
  orthonormal basis.
-/
