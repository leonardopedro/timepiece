import BookProof.ChapterYangMillsHermite.Part1
import BookProof.ChapterYangMillsHermite.Part2

/-!
# The gauge-fixed Yang–Mills Hamiltonian on the Gauss–polynomial core of `L²(ℝ⁹⁹)`

`PLAN_LEAN_SPECIALIST_QYM_FLOW.md` Part F asks for the **field-space** (option
(b)) realization of the Weyl-gauge Yang–Mills Hamiltonian: the fields must act as
genuine multiplication and differentiation operators on a dense core of
`L²(ℝ⁹⁹)`, not merely abstractly on an occupation-number space.

The core is `BookProof.HermiteProductCore.polyGaussCore`, the span of the product
Hermite functions `p(x) e^{-‖x‖²/4}`.  Because the map `p ↦ p · e^{-‖x‖²/4}` is
an injective linear map from `ℂ[X₀,…,X₉₈]`, every operator can be defined at the
purely algebraic level of polynomials and transported to the core (`CoreRep`).

* `mulOp f` — multiplication by a polynomial (F.2, the coordinate operators
  `A_{k,a}`);
* `derOp j`, `momOp j` — the true derivative `∂_j` of `p·e^{-‖x‖²/4}` written back
  on the polynomial factor, and the momentum `π_j = −i ∂_j` (F.3);
* `magPoly i a` — the magnetic field
  `B_{i a} = ε_{ijk}(∂_j A_{k,a} + f_{abc} A_{j,b} A_{k,c})`, a *real* polynomial
  in the `99 = 3 + 24 + 72` coordinates (3 spatial, 24 fields `A_{j,a}`, 72
  independent derivative coordinates `∂_j A_{k,a}`), acting by multiplication
  (F.4);
* `weylProd` — the Weyl ordering `½(PQ + QP)`, symmetric whenever `P` and `Q`
  are (F.5); the canonical commutation relation `[A_{j}, π_{j}] = i` is
  `commutator_coord_mom`;
* `ymHamiltonian` — `H₁ = ½ Σ π² + ½ Σ B²`, the *positive* sum of squares (the
  sign of `book.tex:7077` reconciled), well defined, symmetric and positive on
  the core (F.6–F.8);
* `ym_hermite_friedrichs_extension` (F.9) and `ym_hermite_hashimoto_selects`
  (F.10) — the instantiation of the already-proved
  `BookProof.FriedrichsExtension.friedrichs_extension_exists` and
  `BookProof.FriedrichsExtension.weyl_hashimoto_selects_friedrichs`.

Nothing here claims a mass gap or global existence; the Millennium problem stays
out of scope.
-/
