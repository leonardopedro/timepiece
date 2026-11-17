import BookProof.Sm.ChapterSmBrstGhost
import Work.SmSu3Constants

/-!
# The ghost-number-two matrix of the cubic charge

`scripts/sm-cubic-kernel-basis.py` computes, exactly over `Q(sqrt 3)`, the `66 x 220` matrix of
`Omega_3` on `Lambda^2 C^12` and certifies its rank `55` with one `55 x 55` nonzero minor.  This
file
formalises the part of that certificate that needs no exact arithmetic: the two sectors as types
with
their cardinalities (`66` and `220`), the matrix itself as a `Matrix`, and the minor as a `Prop`.

The minor's *proof* is open, for three concrete reasons:

* the physical structure constants are not Lean data — `smStruct` takes `f3 : Fin 8 → Fin 8 → Fin 8
→ ℝ`
  as a parameter, and the `lambda_a / 2` derivation that fixes it lives only in the script;
* the determinant lives in `Q(sqrt 3)`, for which this development has no arithmetic layer (the
script
  carries `a + b * sqrt 3` as a pair of `fractions.Fraction`s);
* `native_decide` is excluded: its proof term does not reduce in `nanoda`, and the axiom audit in
  `Work/SmQuartetConstructedAudit.lean` would report `Lean.ofReduceBool`.

So this file states the target and nothing else.  It is not part of the build.
-/

namespace BookProof.SmBrstGhost

open BookProof.SmCar BookProof.BRSTNilpotent

/-- The ghost-number-two sector: the two-element subsets of the twelve ghost modes. -/
abbrev GhostDegreeTwo := { S : Finset (Fin 12) // S.card = 2 }

/-- The ghost-number-three sector, the ambient space of the cubic charge's image. -/
abbrev GhostDegreeThree := { T : Finset (Fin 12) // T.card = 3 }

/-- `dim Lambda^2 C^12 = 66`, the number of two-ghost states. -/
theorem card_ghostDegreeTwo : Fintype.card GhostDegreeTwo = 66 := by
  rw [Fintype.card_subtype]
  have h : (Finset.univ.filter (fun S : Finset (Fin 12) => S.card = 2))
      = (Finset.univ : Finset (Fin 12)).powersetCard 2 := by
    ext S
    simp [Finset.mem_powersetCard]
  rw [h, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  decide

/-- `dim Lambda^3 C^12 = 220`, the number of three-ghost states. -/
theorem card_ghostDegreeThree : Fintype.card GhostDegreeThree = 220 := by
  rw [Fintype.card_subtype]
  have h : (Finset.univ.filter (fun T : Finset (Fin 12) => T.card = 3))
      = (Finset.univ : Finset (Fin 12)).powersetCard 3 := by
    ext T
    simp [Finset.mem_powersetCard]
  rw [h, Finset.card_powersetCard, Finset.card_univ, Fintype.card_fin]
  decide

/-- **The cubic charge on ghost number two, as a matrix**: the entry at `(S, T)` is the coefficient
of
the three-ghost state `occ T` in `Omega_3 (occ S)`, i.e. its inner product with the unit vector
`occ T`.  This is the matrix the script eliminates. -/
noncomputable def smGhostMatrix (f3 : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    Matrix GhostDegreeTwo GhostDegreeThree ℂ :=
  fun S T => inner ℂ (occ T.val) ((smGhostCharge 0 f3) (occ S.val))

/-- **The physical matrix**: the cubic charge on ghost number two, with `f3` instantiated by the
constants derived from the Gell-Mann generators in `Work/SmSu3Constants.lean`.  This is the matrix
the
script eliminates; what is still missing is the literal `55 x 55` minor and its determinant proof.
-/
noncomputable def smGhostMatrixPhys : Matrix GhostDegreeTwo GhostDegreeThree ℂ :=
  smGhostMatrix BookProof.SmSu3.smF3

/-- **The rank certificate as a statement**: a `55 x 55` minor of `smGhostMatrix` is nonsingular.
With
the rank bound `rank ≤ 55` from the elimination this gives `rank = 55`, hence `dim ker = 66 - 55 =
11`.

The script certifies this with `det = -3^12 / 2^35` for explicit row and column lists; producing the
`rows` and `cols` here and proving this `Prop` is the open part. -/
noncomputable def ghostMinorStatement (f3 : Fin 8 → Fin 8 → Fin 8 → ℝ)
    (rows : Fin 55 → GhostDegreeThree) (cols : Fin 55 → GhostDegreeTwo) : Prop :=
  Matrix.det (Matrix.submatrix (smGhostMatrix f3) cols rows) ≠ 0

end BookProof.SmBrstGhost
