import BookProof.ChapterFriedrichsCanonical.Part1
import BookProof.ChapterFriedrichsCanonical.Part2

/-!
# The Friedrichs extension is **canonical**

`BookProof.ChapterFriedrichsExtension` proves the *existence* half of the
Friedrichs theorem: a densely defined positive symmetric operator `H` on a
complex Hilbert space has a positive self-adjoint extension, constructed as
`A_F = S⁻¹ − 1` for the form resolvent `S = (H + 1)⁻¹`
(`friedrichs_extension_exists`).  What that statement does *not* say is *which*
extension it is — and a symmetric operator generally has many.

This module supplies the missing half, the one that makes the Friedrichs
extension **the canonical self-adjoint realization**:

* the construction is packaged as a *named* operator rather than an existential:
  `friedrichsDomain P`, `friedrichsOp P hdense`, with
  `friedrichsOp_isPositiveSelfAdjointExtension` re-proving the existence
  statement for it;
* `formDomain P` — the range of the embedding of the form completion, i.e. the
  *form domain* `Q(H)` — contains the domain of `H` (`dom_le_formDomain`) and the
  Friedrichs domain (`friedrichsDomain_le_formDomain`);
* **`friedrichs_canonical`**: *every* symmetric extension of `H` whose domain is
  contained in the form domain is a restriction of `A_F`.  So `A_F` is the
  largest such extension;
* **`friedrichs_unique_selfAdjoint`**: consequently `A_F` is the **unique**
  self-adjoint extension of `H` with domain inside the form domain — the
  classical characterization of the Friedrichs extension (Reed–Simon Vol. II,
  Thm X.23; Kato, Thm VI.2.11).  Both the domain and the action are pinned down.

The named instance is the one `CONSOLIDATED_PLAN.md` §10.6.1 asks about: the
quantum-gravity one-particle scalaron Hamiltonian `−Δ + V(φ)` on the
Gauss–polynomial (Hermite) core of `L²(ℝ)` has a *canonical* self-adjoint
realization (`qgOneParticleHermite_friedrichs_canonical`,
`qgOneParticleHermite_friedrichs_unique`).

**Honest boundary.**  Uniqueness *among extensions with domain in the form
domain* is not essential self-adjointness: an operator that is not essentially
self-adjoint still has other self-adjoint extensions, whose domains necessarily
leave `Q(H)`.  Nothing here claims otherwise.
-/
