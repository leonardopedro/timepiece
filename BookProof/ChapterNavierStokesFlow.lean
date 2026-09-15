import BookProof.ChapterNavierStokesFlow.Part1
import BookProof.ChapterNavierStokesFlow.Part2

/-!
# Chapter "Free field parametrization … Navier–Stokes": the truncated
Navier–Stokes Hamiltonian generates a **complete flow**

Source: `book.tex`, chapter *"Free field parametrization in Classical Statistical
Field Theory and Navier–Stokes equations"*, §*"Free field parametrization in
Navier–Stokes equations"* (`book.tex` ~4133–4216).  The correspondence between
the book's text and the theorems proved here is:

* ~4151–4173, degrees of freedom, derivatives treated as fields:
  `fieldTaylor`, `field_evaluates_to_value`;
* ~4163–4170, the canonical commutation relations of the modes: `ccr_field`,
  `derivativeField_momentum`, `secondDerivativeField_momentum`;
* ~4184–4189, the Navier–Stokes Hamiltonian: `nsHamiltonian`,
  `nsHamiltonian_hermitian`;
* ~4199, "polynomial of low degree in the fields":
  `nsHamiltonian_isPolynomial` (words of length ≤ 3);
* ~4191–4197, the divergence constraint and its resolution:
  `nsDivergenceConstraint_resolution`, `nsBrst_nilpotent`;
* ~4199–4208, self-adjointness: `nsHamiltonian_hasZeroDeficiency`,
  `nsHamiltonian_hasZeroDeficiencyOn` (**truncation only**) and the conditional
  `ns_esa_of_farisLavine`, `ns_esa_of_farisLavine_dense`;
* ~4210–4216, existence and uniqueness of the solution: `nsFlow_group`,
  `nsFlow_groupOnEvolved`, `nsFlow_noBlowup` (**truncation only**); the
  differential form — the evolution equation `ψ̇ = i H_N ψ` and the unique
  solvability of its Cauchy problem — is in the companion module
  `BookProof.ChapterNavierStokesCauchy`.

## What is proved

Let `H_N` be the Navier–Stokes Hamiltonian **restricted to a finite truncation**
(finitely many field modes `u_k`, `u_{k,j}`, `u_{k,jj}`, each realized by a
Hermitian matrix on a finite-dimensional state space, the modes commuting with
one another as multiplication operators do).  Then

* `nsHamiltonian_hermitian` — `H_Nᴴ = H_N`;
* `nsHamiltonian_isPolynomial` — every term of `H_N` is a word of length at most
  three in the generators `u_k`, `π_i` (the "low degree in the fields"
  hypothesis of `book.tex` ~4199);
* `nsFlow_zero`, `nsFlow_group`, `nsFlow_unitary` — `U(t) = e^{i t H_N}` is a
  one-parameter **unitary group**, defined for *every* real time: the flow of the
  truncation is complete;
* `nsFlow_norm_preserving`, `nsFlow_noBlowup` — the flow preserves the `ℓ²` mass
  and every coefficient of the evolved state stays bounded by the initial mass,
  uniformly in `t`: **no finite-time singularity on the truncation**;
* `nsHamiltonian_hasZeroDeficiency` — the truncated Hamiltonian has vanishing
  deficiency: `H_N ψ = ± i ψ` forces `ψ = 0`.

Alongside the truncation the file records the algebraic core of the surrounding
construction: the derivatives-as-fields Taylor operator (`Part A`), the
Lagrangian change of variables and the volume-preservation constraint
(`Part B`), the BRST ghost charge (`Part E`), and the Faris–Lavine framing of
the continuum essential-self-adjointness question (`Part G`).

## What is *not* claimed

The essential self-adjointness of the **untruncated continuum** operator
`H = ∫ a†(πⁱ(u_j u_{i,j} − ν u_{i,jj}) + h.c.) a`, and with it global existence
and uniqueness for the Navier–Stokes equations, is **not** claimed anywhere in
this file.  The project's own ODE chapter is the standing warning: for `ẋ = x²`
the Hamiltonian `x²p̂ − i x̂` is a polynomial of degree 3 whose classical flow
`x₀/(1 − t x₀)` is incomplete, so a low-degree polynomial Hamiltonian need *not*
be essentially self-adjoint.  Accordingly:

* the degree bound `nsHamiltonian_isPolynomial` is recorded as a **symmetry**
  statement (a well-defined polynomial operator), never as self-adjointness;
* `HasZeroDeficiency` is the deficiency-index-`(0,0)` condition *for the operator
  itself*; on a finite-dimensional space (where the operator is bounded and
  everywhere defined) this is exactly essential self-adjointness, and it is
  proved for the truncation.  For an unbounded operator the deficiency spaces
  are those of the *adjoint*, so the finite statement does not transfer;
* `ns_esa_of_farisLavine` and its densely-defined form
  `ns_esa_of_farisLavine_dense` are **conditional**: the Faris–Lavine commutator
  criterion (Faris–Lavine 1974, Corollary 1.1; Reed–Simon Vol. II Theorem X.28)
  enters as a *named hypothesis*, never as an `axiom`, exactly as Crouzeix's
  inequality does in `BookProof.ChapterH4`.  Verifying its two analytic
  inequalities for the continuum operator is a research target, not a result of
  this file.  The hypothesis is carried in its honest form: symmetry of the
  operator is part of it, since without symmetry the criterion is contradictory
  and the conditional theorem would be vacuous
  (`farisLavine_without_symmetry_forces_trivial`), while with symmetry it is
  satisfiable (`farisLavine_holds_of_everywhereDefined`) — indeed automatic for
  everywhere-defined operators, which is precisely why the analytic content sits
  in the dense-domain predicate `HasZeroDeficiencyOn`.

Everything here is `sorry`-free and `axiom`-free (only `propext`,
`Classical.choice`, `Quot.sound`).
-/
