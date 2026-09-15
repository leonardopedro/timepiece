import BookProof.ChapterSqSumFarisLavine.Part1
import BookProof.ChapterSqSumFarisLavine.Part2

/-!
# The two Faris–Lavine inequalities for `½ Σ_j κ_j π_j² + ½ Σ_r L_r²`

This module proves, on the Gauss–polynomial core of `L²(ℝᴰ)`, the two inequalities that
Theorem 1 of Faris–Lavine asks of a Hamiltonian and its comparison operator, for the
**kinetic-plus-squares Hamiltonian**

`H = ½ Σ_j κ_j π_j² + ½ Σ_r L_r²`,  `L_r = Σ_i v_{ri} x_i`,

of `BookProof.QgOuterFock.sqSumOp`, against the harmonic comparison operator
`N = −Δ + ‖x‖²/4` (`harmCore`).  The signature `κ` is an arbitrary *real* vector — no sign,
no ellipticity — and the family of linear forms `L_r` is arbitrary and finite.

What matters for the Fock lift is the *shape of the constants*: both are expressed through

* `km`, a bound on `|κ_j|`, and
* Schur-type `ℓ¹` bounds on the coefficient matrix `v` of the linear forms

and **not** through the dimension `D`.  This is exactly what makes the same two constants
serve every particle-number sector of the outer Fock space simultaneously, which is the
hypothesis the `ℓ²`-direct-sum Faris–Lavine theorem of
`BookProof.ChapterQgOuterFockFarisLavine` needs.

## What is proved

* `schur_bound` — the Schur test for a real matrix with bounded row and column `ℓ¹` norms;
* `linFun`, `potFun`, `potPoly`, `gradPoly`, `gradFun`, `kinPart` — the data of the
  Hamiltonian, and `sqSumPoly_apply`, its splitting into kinetic and potential parts;
* `potFun_le_of_schur`, `sum_gradFun_sq_le_of_schur` — the pointwise bounds
  `V(x) ≤ (ab/2)‖x‖²` and `Σ_k (∂_k V)(x)² ≤ (ab)²‖x‖²` from the Schur data of `v`;
* `commPoly`, `commPoly_eq` — the commutator `[H, N]` computed in polynomial coordinates:
  it is again first order, with the gradient of the potential as its coefficient;
* `commForm_eq_im`, `abs_im_gaussInt_le` — the commutator form as a Gaussian integral;
* **`commForm_sqSumOp_le`** — the Faris–Lavine commutator bound
  `|⟪u, i[H,N]u⟫| ≤ (km/2 + 2M)·⟪u, Nu⟫`, with `M` a bound on the gradient of the
  potential;
* **`norm_sqSumOp_le`** — the relative bound `‖Hu‖ ≤ (3km/2 + 8B)·‖(N+1)u‖`, with `B` a
  bound on the potential.

Everything is `sorry`-free and `axiom`-free.
-/
