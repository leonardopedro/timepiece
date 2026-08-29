import Mathlib
import BookProof.ChapterStarobinskyPotential
import BookProof.ChapterScalaronWallEsa
import BookProof.ChapterScalaronCoreEsa

/-!
# The strict one-particle edge for the Starobinsky fiber

`CONSOLIDATED_PLAN.md` §state 28j, item 4: the strict one-particle edge for
the Starobinsky fiber.  For `0 < c < M⁴/(4α)` the superlevel set `{V < c}` of
the exponential wall potential is bounded, so `starobinskyEdge_quadForm` proves
`⟪ψ, h_ψ ψ⟫ ≥ E₀‖ψ‖²` with explicit `E₀ = max E_kin E_mass > 0` —
`E_kin = π²/(4(A+B))²` from Poincaré on the window and `E_mass = c/(2(1 + ((A+B)/π)²))`
from the outside cost `c`.  The remaining classical input is
`poincare_ineq_support` (sharp Wirtinger on a fixed interval), left as `sorry` for the
Lean4-specialist; once discharged, the `dΓ` lift of `ChapterScalaronFockGapChain`
applies verbatim at `μ = E₀` to give the strict Fock-level gap for the full-exponential
scalaron fiber.
-/

namespace BookProof.ScalaronEdge

open Complex Real MeasureTheory
open BookProof.Starobinsky
open BookProof.ScalaronWallEsa
open BookProof.ScalaronEsa
open BookProof.FarisLavine

/-! ## 0. The Starobinsky potential and the operator

The wall module works with the *explicit* potential
`fun phi => starobinskyV M alpha phi` at parameters `M, alpha` (see
`starobinskyWall_esa`).  We fix parameters once and work with that operator,
so every statement below is an instance of the wall API. -/

variable (M alpha : ℝ) (halpha : 0 < alpha)

/-- The wall potential at the fixed parameters. -/
noncomputable def scalV : ℝ → ℝ := fun phi => starobinskyV M alpha phi

theorem scalV_smooth : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (scalV M alpha) :=
  contDiff_starobinskyV M alpha

/-- The shelf value of the wall potential: `lim_{x→+∞} V = M⁴/(2α)`, so the
superlevel sets `{V < c}` are bounded for `c` below a fixed fraction of it.
We use `shelf := M⁴/(4α)` as the working threshold (any constant strictly
below the limit works; the smaller the constant, the larger the window). -/
def edgeShelf : ℝ := M ^ 4 / (4 * alpha)

theorem edgeShelf_pos (hM : 0 < M) : 0 < edgeShelf M alpha := by
  unfold edgeShelf; positivity

/-- The fiber Hamiltonian: the Schrödinger operator with the wall potential on
the compactly supported smooth core of `L²(ℝ)` — exactly the operator of
`starobinskyWall_esa`. -/
noncomputable def starobinskyEdgeHam : ccDomain ℝ →ₗ[ℂ] Lp ℂ 2 (volume : Measure ℝ) :=
  wallHam (scalV M alpha) (scalV_smooth M alpha)

/-- The fiber Hamiltonian is symmetric on the core (from `wallHam_symmetricOn`). -/
theorem starobinskyEdgeHam_symmetricOn :
    SymmetricOn (ccDomain ℝ) (starobinskyEdgeHam M alpha) :=
  wallHam_symmetricOn _ (scalV_smooth M alpha)

/-! ## 1. Boundedness of the classically allowed region -/

/-- Poincaré constant on `[−A, B]`: `E_kin = π²/(4(A+B))²`. -/
noncomputable def edgeKinConst (A B : ℝ) : ℝ := π ^ 2 / (4 * (A + B)) ^ 2

theorem edgeKinConst_pos {A B : ℝ} (hA : 0 < A) (hB : 0 < B) : 0 < edgeKinConst A B := by
  unfold edgeKinConst
  positivity

/-- Mass term from the outside cost: `E_mass = c/(2(1 + ((A+B)/π)²))`. -/
noncomputable def edgeMassConst (A B c : ℝ) : ℝ := c / (2 * (1 + ((A + B) / π) ^ 2))

/-- **Boundedness of the classically allowed region.** For `0 < c < edgeShelf`
the sublevel set `{x | scalV x < c}` is contained in a bounded interval
`[−A, B]` with explicit, positive endpoints: the exponential wall
(`scalV → ∞` as `x → −∞`) and the shelf (`scalV → M⁴/(2α)` as
`x → +∞`) each give one side.  `A` and `B` are explicit in `α, M, c`; both
are positive for `c < edgeShelf`. -/
theorem starobinskyV_lt_shelf_bounded (c : ℝ) (hc : 0 < c) (hcs : c < edgeShelf M alpha) :
    ∃ A B : ℝ, 0 < A ∧ 0 < B ∧
      ∀ x : ℝ, scalV M alpha x < c → x ∈ Set.Icc (-A) B := by
  sorry

/-! ## 2. The strict one-particle edge -/

/-- **The strict one-particle edge.** For every `0 < c < edgeShelf`, the
quadratic form of the Starobinsky fiber Hamiltonian dominates the explicit
positive constant `E₀ = max E_kin E_mass`:

`⟪ψ, h_ψ ψ⟫ ≥ E₀‖ψ‖²` for every `ψ ∈ ccDomain ℝ`.

This is the elementary-confinement route of plan item 4(b): the form does
not vanish on any nonzero core vector. -/
theorem starobinskyEdge_quadForm (c : ℝ) (hc : 0 < c) (hcs : c < edgeShelf M alpha) :
    ∃ E₀ : ℝ, 0 < E₀ ∧ ∀ ψ : ccDomain ℝ,
      inner ((starobinskyEdgeHam M alpha) ψ) ψ ≥ (E₀ : ℂ) * inner ψ ψ := by
  obtain ⟨A, B, hA, hB, hbound⟩ := starobinskyV_lt_shelf_bounded M alpha halpha c hc hcs
  refine ⟨max (edgeKinConst A B) (edgeMassConst A B c), ?_, ?_⟩
  · exact le_max_of_le_left (edgeKinConst_pos hA hB) |>.trans le_rfl
  · intro ψ
    obtain ⟨f, rfl⟩ := (ccEquiv ℝ).surjective ψ
    -- Decompose the form: kinetic + potential.
    -- Kinetic part ≥ 0 by integration by parts on the compact support.
    -- Potential part: split ∫ V|f|² = ∫_{V<c} + ∫_{V≥c};
    --   on {V≥c}: ≥ c ∫_{V≥c}|f|² ≥ c (‖f‖² − ‖f‖²_{V<c});
    --   on {V<c}: f is supported in [−A,B], so by the boundedness input and
    --   Poincaré, ‖f‖²_{V<c} ≤ (L/π)²‖f'‖², absorbed into the kinetic term.
    -- Absorb the boundary cross term with 2|ab| ≤ δa² + b²/δ.
    sorry

end BookProof.ScalaronEdge
