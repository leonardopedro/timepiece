import BookProof.ChapterNavierStokesFockSpace.Part1
import BookProof.ChapterNavierStokesFockSpace.Part2

/-!
# The Fock space of a Fock space, and its ladder operators

The Lagrangian form of the Navier–Stokes Hamiltonian of
`BookProof.ChapterNavierStokesLagrangianEsa` is a *second* quantization: the
Eulerian field `u` is already an operator on a Fock space, and passing to the
parcel variables `X(ξ)` — one field-carrying parcel for each label `ξ` in a
continuous domain — quantizes the parcels themselves.  The state space is
therefore a Fock space **whose one-particle space is itself a Fock space**, and
the Hamiltonian is *quadratic* in the outer (parcel) creation and annihilation
operators.

This module builds that state space concretely, in the occupation-number
representation, together with both levels of ladder operators.

* `lpDiag`, `lpBasis` — a general diagonal operator with a real symbol on the
  finitely supported modes of `ℓ²(ι)`, its eigenbasis, symmetry, essential
  self-adjointness (`lpDiag_hasZeroDeficiencyOn`) and unboundedness
  (`lpDiag_not_bounded`).
* `Conf M = M →₀ ℕ`, `FockL2 M = ℓ²(Conf M)`, `FockDom M` — the Fock space over
  the mode index `M` in the occupation-number representation and its dense
  domain of finite-particle, finite-mode states.
* `annih m`, `creat m` — the annihilation and creation operators, with
  `annih_basis`, `creat_basis` (the usual `√n` factors), `creat_adjoint`
  (`⟪a†v, w⟫ = ⟪v, a w⟫`) and the canonical commutation relations
  `ccr_same`, `ccr_ne`.
* `numberOp m = a†ₘ aₘ` and `numberOp_basis` — the mode occupation operator.
* `FockOfFockL2 J K = FockL2 (J × Conf K)` — **the Fock space of a Fock space**:
  the outer one-particle modes are indexed by a parcel mode `j : J` *together
  with* an inner Fock (occupation) state `c : Conf K`.  `outerOneParticle` shows
  that the outer creation operator applied to the vacuum creates exactly one
  parcel carrying the inner Fock state `c`.

The Hamiltonian itself, its integral over the continuous parcel domain and its
essential self-adjointness are in `BookProof.ChapterNavierStokesFockEsa`.
-/
