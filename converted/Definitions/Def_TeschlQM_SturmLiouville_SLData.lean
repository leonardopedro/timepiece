/-
prove2.me platform library module `Definitions.Def_TeschlQM_SturmLiouville_SLData`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_TeschlQM_SturmLiouville_SLData.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace TeschlQM.SturmLiouville

open MeasureTheory

/-- Teschl, Sec. 9.1, pp. 181–182: the data of a Sturm–Liouville expression
`τ f = (1/r) (−(p f′)′ + q f)` (9.1) on an arbitrary open interval `I = (a, b) ⊆ ℝ`.
The endpoints are extended reals, so `a = −∞` and `b = +∞` are allowed. The standing
requirements of p. 181 are fields of the structure:
(i) `p⁻¹ ∈ L¹_loc(I)`, `p` positive; (ii) `q ∈ L¹_loc(I)`, real-valued (`q : ℝ → ℝ`);
(iii) `r ∈ L¹_loc(I)`, `r` positive. Values of `p, q, r` outside `I` play no role. -/
structure SLData where
  /-- left endpoint `a ∈ [−∞, ∞)` -/
  a : EReal
  /-- right endpoint `b ∈ (−∞, ∞]` -/
  b : EReal
  hab : a < b
  p : ℝ → ℝ
  q : ℝ → ℝ
  r : ℝ → ℝ
  p_pos : ∀ x : ℝ, a < (x : EReal) → (x : EReal) < b → 0 < p x
  r_pos : ∀ x : ℝ, a < (x : EReal) → (x : EReal) < b → 0 < r x
  p_inv_loc : LocallyIntegrableOn (fun x => (p x)⁻¹) {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b}
  q_loc : LocallyIntegrableOn q {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b}
  r_loc : LocallyIntegrableOn r {x : ℝ | a < (x : EReal) ∧ (x : EReal) < b}

namespace SLData

/-- The open interval `I = (a, b)` as a subset of `ℝ`. -/
def I (L : SLData) : Set ℝ := {x : ℝ | L.a < (x : EReal) ∧ (x : EReal) < L.b}

/-- The weighted measure `r(x) dx` on `I`, so that `L²(I, r dx)` (9.2) is `Lp ℂ 2 L.measure`,
with inner product `⟨f, g⟩ = ∫_a^b f(x)* g(x) r(x) dx`. -/
noncomputable def measure (L : SLData) : Measure ℝ :=
  (volume.restrict L.I).withDensity (fun x => ENNReal.ofReal (L.r x))

/-- The filter `x → a` inside `I` (i.e. `x ↓ a` if `a` is finite, `x → −∞` if `a = −∞`). -/
noncomputable def atLeft (L : SLData) : Filter ℝ :=
  Filter.comap (fun x : ℝ => (x : EReal)) (nhdsWithin L.a (Set.Ioi L.a))

/-- The filter `x → b` inside `I` (i.e. `x ↑ b` if `b` is finite, `x → +∞` if `b = +∞`). -/
noncomputable def atRight (L : SLData) : Filter ℝ :=
  Filter.comap (fun x : ℝ => (x : EReal)) (nhdsWithin L.b (Set.Iio L.b))

end SLData

end TeschlQM.SturmLiouville
