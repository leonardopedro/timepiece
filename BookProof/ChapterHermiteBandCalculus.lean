import BookProof.ChapterHermiteBandCalculus.Part1
import BookProof.ChapterHermiteBandCalculus.Part2

/-!
# The graded band calculus of the product Hermite basis: a real quadratic Hamiltonian has a
# band matrix whose entries grow like the degree

`BookProof.ChapterHermiteProductBasis` makes the product Hermite functions
`ψ_α = He_α · e^{-‖x‖²/4} / ‖·‖` an orthonormal basis of `L²(ℝᵈ)` and records the ladder
relations `a†ᵢψ_α = √(αᵢ+1) ψ_{α+eᵢ}`, `aᵢψ_α = √αᵢ ψ_{α−eᵢ}`.  This chapter turns those
relations into a **calculus of band operators**, whose purpose is the input of the weighted
Schur gate of `BookProof.ChapterFockWeightedSchurEsa`: a one-particle matrix that is
band-limited in the degree, has boundedly many entries per column, and whose entries grow
at most like `deg + 1`.

## What is proved

* `hpsi`, `pgLp_hpsi`, `hcomb` — the normalized Hermite *polynomial* `ψ_α`, its `L²` vector,
  and the finite combination `Σ_β f_β ψ_β` of Hermite states.
* `crePoly_hpsi`, `annPoly_hpsi` — the ladder relations at the level of polynomials.
* `Band T r M C g` — the band predicate: `T ψ_α` is a combination of at most `M` Hermite
  states whose degrees differ from `deg α` by at most `r`, with coefficients bounded by
  `C · g (deg α)`.  The two growths used are `g1 n = √(n+1)` (first order) and
  `g2 n = n + 1` (second order).
* `Band.add`, `Band.smul`, `Band.mono`, `Band.toBand2` — the closure properties.
* `band_crePoly`, `band_annPoly` — the ladder operators are first-order band operators with
  `M = C = 1`.
* **`Band.comp`** — the composition of two first-order band operators is a second-order one:
  `M₁M₂` entries, band `2`, and the growth `2 M₁ C₁ C₂ (deg α + 1)`; the analytic content is
  `√(deg α + 1) · √(deg γ + 1) ≤ 2 (deg α + 1)` for `|deg γ − deg α| ≤ 1`.
* `IsBand1` / `IsBand2` — the existential forms, closed under sums, scalar multiples, finite
  sums and (for `IsBand1`) composition.
* `mulXPoly_eq`, `momPoly_eq` — the coordinate and momentum operators are the ladder
  combinations `xᵢ = aᵢ† + aᵢ` and `πᵢ = (i/2)(aᵢ† − aᵢ)`, hence first-order.
* **`isBand2_fqPoly`** — the headline: the general real quadratic Hamiltonian
  `fqPoly P Q S b b'` of `BookProof.ChapterFullQuadraticEsa` — an arbitrary Weyl-ordered
  quadratic form in the coordinates and momenta, plus a first-order term — is a second-order
  band operator.

Everything is `sorry`-free and `axiom`-free.
-/
