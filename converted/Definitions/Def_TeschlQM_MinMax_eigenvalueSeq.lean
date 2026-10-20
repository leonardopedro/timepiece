/-
prove2.me platform library module `Definitions.Def_TeschlQM_MinMax_eigenvalueSeq`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_MinMax_eigenvalueSeq.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib
import Definitions.Def_TeschlQM_MinMax_essentialSpectrum

namespace TeschlQM.MinMax

/-- `inf σ_ess(A)` as an extended real: the infimum of the real points of the essential spectrum
(for a self-adjoint `A` every point of `σ(A)` is real). It is `+∞` when `σ_ess(A) = ∅` and `−∞`
when `σ_ess(A)` is unbounded below. -/
noncomputable def infEssSpectrum {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →ₗ.[ℂ] H) : EReal :=
  sInf ((fun x : ℝ => (x : EReal)) '' {x : ℝ | (x : ℂ) ∈ essentialSpectrum A})

/-- The span of the eigenvectors of `A` for the eigenvalues `μ ≤ x` lying below the essential
spectrum (`μ < inf σ_ess(A)`): the (algebraic) sum of the eigenspaces `Ker(A − μ)` over these
`μ`. Its dimension counts the eigenvalues `≤ x` below the essential
spectrum according to their multiplicity (eigenspaces of distinct eigenvalues of a
self-adjoint operator are orthogonal, Lemma 2.20). -/
noncomputable def eigenspaceBelow {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →ₗ.[ℂ] H) (x : ℝ) : Submodule ℂ H :=
  ⨆ (μ : ℝ) (_ : (μ : EReal) < infEssSpectrum A ∧ μ ≤ x), eigenspace A (μ : ℂ)

/-- Teschl, p. 118–119 (the numbers `E_n` of Theorem 4.10): `E₁ ≤ E₂ ≤ E₃ ≤ ⋯` are the
eigenvalues of `A` below the essential spectrum, counted according to their multiplicity, and
`E_n = inf σ_ess(A)` once there are no more eigenvalues left. Encoded as
`E_n = inf ({x < inf σ_ess(A) | #{eigenvalues ≤ x below σ_ess(A), with multiplicity} ≥ n} ∪ {inf σ_ess(A)})`
in `EReal`; the multiplicity count is the (cardinal) dimension of `eigenspaceBelow A x`.
The index starts at `n = 1` as in the book (`eigenvalueSeq A 0` is `−∞` and never used).
If `A` is not bounded below the value is `−∞`; if `σ_ess(A) = ∅` and the eigenvalues run out,
the value is `+∞`. -/
noncomputable def eigenvalueSeq {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] (A : H →ₗ.[ℂ] H) (n : ℕ) : EReal :=
  sInf ({y : EReal | ∃ x : ℝ, y = (x : EReal) ∧ (x : EReal) < infEssSpectrum A ∧
      (n : Cardinal) ≤ Module.rank ℂ (eigenspaceBelow A x)} ∪ {infEssSpectrum A})

end TeschlQM.MinMax
