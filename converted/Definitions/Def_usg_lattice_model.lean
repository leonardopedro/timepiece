/-
prove2.me platform library module `Definitions.Def_usg_lattice_model`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_usg_lattice_model.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

set_option autoImplicit false

namespace UndecidableSpectralGap

/-- The sites of the `L × L` square lattice `Λ(L) = {1,…,L}²`.
The first component is the row index, the second the column index. -/
abbrev Site (L : ℕ) := Fin L × Fin L

/-- A standard basis state of the lattice system with local dimension `d`:
an assignment of a level in `Fin d` to every site. -/
abbrev Config (L d : ℕ) := Site L → Fin d

/-- The directed horizontal (row) edges of `Λ(L)` with **open** boundary conditions:
pairs of sites in the same row whose column indices are consecutive. -/
def rowEdges (L : ℕ) : Finset (Site L × Site L) :=
  Finset.univ.filter fun e => e.1.1 = e.2.1 ∧ (e.1.2 : ℕ) + 1 = (e.2.2 : ℕ)

/-- The directed vertical (column) edges of `Λ(L)` with **open** boundary conditions:
pairs of sites in the same column whose row indices are consecutive. -/
def colEdges (L : ℕ) : Finset (Site L × Site L) :=
  Finset.univ.filter fun e => e.1.2 = e.2.2 ∧ (e.1.1 : ℕ) + 1 = (e.2.1 : ℕ)

/-- The two-body interaction `h` acting on the pair of sites `(p, q)` of the lattice,
written in the standard product basis: it acts as `h` on the factors `p` and `q`
and as the identity on all other sites. -/
def embedTwo {L d : ℕ} (p q : Site L) (h : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Config L d) (Config L d) ℂ :=
  fun c c' => if ∀ s, s ≠ p → s ≠ q → c s = c' s then h (c p, c q) (c' p, c' q) else 0

/-- The on-site interaction `h` acting on the site `p`, written in the standard product
basis: it acts as `h` on the factor `p` and as the identity on all other sites. -/
def embedOne {L d : ℕ} (p : Site L) (h : Matrix (Fin d) (Fin d) ℂ) :
    Matrix (Config L d) (Config L d) ℂ :=
  fun c c' => if ∀ s, s ≠ p → c s = c' s then h (c p) (c' p) else 0

/-- The translationally invariant nearest-neighbour Hamiltonian
`H^{Λ(L)} = Σ_rows h_row + Σ_columns h_col + Σ_sites h₁`
on the `L × L` square lattice with open boundary conditions, local dimension `d`,
on-site term `h₁`, horizontal interaction `hrow` and vertical interaction `hcol`. -/
noncomputable def latticeHam (L d : ℕ) (h1 : Matrix (Fin d) (Fin d) ℂ)
    (hrow hcol : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) :
    Matrix (Config L d) (Config L d) ℂ :=
  (∑ e ∈ rowEdges L, embedTwo e.1 e.2 hrow) + (∑ e ∈ colEdges L, embedTwo e.1 e.2 hcol)
    + ∑ p : Site L, embedOne p h1

/-- The operator norm (largest singular value) of a square complex matrix,
viewed as an operator on the Euclidean space of its index type. -/
noncomputable def opNorm {n : Type*} [Fintype n] [DecidableEq n] (A : Matrix n n ℂ) : ℝ :=
  ‖Matrix.toEuclideanCLM (𝕜 := ℂ) A‖

/-- The local interaction strength `max{‖h₁‖, ‖h_row‖, ‖h_col‖}` of a lattice model. -/
noncomputable def localInteractionStrength {d : ℕ} (h1 : Matrix (Fin d) (Fin d) ℂ)
    (hrow hcol : Matrix (Fin d × Fin d) (Fin d × Fin d) ℂ) : ℝ :=
  max (opNorm h1) (max (opNorm hrow) (opNorm hcol))

/-- `phi n` is the rational number `φ(n) ∈ [0,1)` whose binary fractional expansion consists
of the binary digits of `n` in reverse order after the point: if `n = b_{k-1}…b_1b_0` in
binary, then `φ(n) = 0.b_0b_1…b_{k-1}`. -/
def phi (n : ℕ) : ℚ :=
  ∑ i ∈ Finset.range n.size, if n.testBit i then (2 : ℚ) ^ (-(i + 1 : ℤ)) else 0

/-- `phiLen n` is the number `|φ(n)|` of binary digits of `n`, i.e. the length of the
fractional expansion of `φ(n)`. -/
def phiLen (n : ℕ) : ℕ := n.size

end UndecidableSpectralGap
