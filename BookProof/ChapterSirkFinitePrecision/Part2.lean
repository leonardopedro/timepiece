import Mathlib
import BookProof.ChapterSirkFinitePrecision.Part1

/-!
# Chapter SirkFinitePrecision — the finite-precision certificate layer (T1–T5)

`CONSOLIDATED_PLAN.md` §13.3, `MASS_GAP_CERTIFIED.md` §4: the SIRK/Hashimoto
reliability chain of §12 is stated in *exact* arithmetic, while the kernel runs in
`f64`.  This chapter formalises the layers that turn a computed number into a
*rigorous enclosure*, with every constant explicit.  Nothing here trusts a
floating-point value: the theorems consume only residuals, backward-error bounds and
interval enclosures, all of which enter as hypotheses or as certified data.

## Deliverables

* `HasRealEigenvalue` — a real eigenvalue of an operator; `rayleigh` — the Rayleigh
  quotient `re ⟪x, T x⟫`, the quantity the kernel reports as a Ritz value.
* The spectral expansion of a symmetric operator in its eigenbasis
  (`repr_apply_of_symmetric`, `norm_sq_eq_sum_repr`, `rayleigh_eq_sum_eigenvalues`,
  `norm_apply_sq_eq_sum_eigenvalues`).
* **T2 (Rayleigh–Ritz residual bound, Layer 3, §4.3)**
  `exists_eigenvalue_dist_le_residual` / `exists_eigenvalue_dist_le_residual_unit`:
  for *any* vector `x ≠ 0` and any real `θ` there is an eigenvalue `lam` of the
  exact operator with `|lam − θ| · ‖x‖ ≤ ‖T x − θ x‖`.  This is Parlett's
  a-posteriori bound: it applies to the *computed* vector and the *exact* operator,
  so no infinite-precision hypothesis is needed at the theorem level.
* **T1/T3 (backward error + Weyl, Layer 1, §4.1)** `backward_error_weyl` and
  `backward_error_weyl_symm`: if the computed eigenpairs are exact eigenpairs of a
  perturbed operator `S` with `‖T x − S x‖ ≤ ε ‖x‖` (the LAPACK backward-error
  model, `ε = c(n) · u · ‖Ĝ‖`), then the eigenvalues of `S` and of `T` are within
  `ε` of each other.  This is Weyl's inequality in the enclosure (Hausdorff) form —
  the form the certificate consumes.
* **The Rayleigh–Ritz upper bound** `ground_le_rayleigh`: the lowest eigenvalue
  never exceeds a computed Rayleigh quotient — the direction that is
  unconditionally sound.
* **Temple's inequality** `temple_lower_bound`: the rigorous *lower* bound for the
  lowest eigenvalue from a computed Rayleigh quotient and an a-priori separation
  constant `β`.  (The bound `λ₀ ≥ θ − ‖r‖` used informally in
  `MASS_GAP_CERTIFIED.md` §3.4 step 1 is *not* valid without extra information — a
  small residual only certifies that *some* eigenvalue is near `θ`.  Temple's
  inequality and `ground_ge_of_no_eigenvalue_below` are the two honest
  replacements, and they are what `ChapterSirkCertifiedGap` uses.)
* **T4 (certified-observable propagation, §5.2)** `observable_propagation`:
  `|⟨O⟩_u − ⟨O⟩_w| ≤ ‖O‖ (‖u‖ + ‖w‖) ‖u − w‖`, and the `2‖O‖ · band · ‖v‖` form
  `observable_propagation_band`.
* **T5 (the interval-enclosure core, Layer 2, §4.2/§4.4)** `CertInterval` with
  `add`/`neg`/`sub`/`mul`/`widen` and their soundness theorems
  (`mem_add`, `mem_neg`, `mem_sub`, `mem_mul`, `mem_widen`), the outward-rounding
  model `mem_ofRounded`, the certified supremum `le_sup_bound_of_isotone` /
  `abs_le_of_isotone`, and the half-width extraction `dist_le_width`.

Everything is `sorry`-free and `axiom`-free.
-/

noncomputable section

namespace BookProof.SirkFinitePrecision

open scoped InnerProductSpace
open Finset

variable {n : ℕ} {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E]
  [FiniteDimensional ℂ E]
/-! ## 5. T4 — certified propagation to observables -/

/-- **T4, Cauchy–Schwarz propagation.**  Two states that are close in norm give close
expectations of a bounded observable. -/
theorem observable_propagation {F : Type*} [NormedAddCommGroup F] [InnerProductSpace ℂ F]
    (O : F →L[ℂ] F) (u w : F) :
    |(inner ℂ u (O u)).re - (inner ℂ w (O w)).re| ≤ ‖O‖ * (‖u‖ + ‖w‖) * ‖u - w‖ := by
  have hsplit : inner ℂ u (O u) - inner ℂ w (O w)
      = inner ℂ (u - w) (O u) + inner ℂ w (O (u - w)) := by
    have hO : O (u - w) = O u - O w := by simp
    rw [hO, inner_sub_left, inner_sub_right]
    ring
  have h1 : ‖inner ℂ (u - w) (O u)‖ ≤ ‖u - w‖ * (‖O‖ * ‖u‖) :=
    le_trans (norm_inner_le_norm _ _)
      (mul_le_mul_of_nonneg_left (O.le_opNorm u) (norm_nonneg _))
  have h2 : ‖inner ℂ w (O (u - w))‖ ≤ ‖w‖ * (‖O‖ * ‖u - w‖) :=
    le_trans (norm_inner_le_norm _ _)
      (mul_le_mul_of_nonneg_left (O.le_opNorm (u - w)) (norm_nonneg _))
  have hre : |(inner ℂ u (O u)).re - (inner ℂ w (O w)).re|
      ≤ ‖inner ℂ u (O u) - inner ℂ w (O w)‖ := by
    rw [← Complex.sub_re]
    exact Complex.abs_re_le_norm _
  refine hre.trans ?_
  rw [hsplit]
  refine (norm_add_le _ _).trans ?_
  nlinarith [h1, h2]

/-- The `2‖O‖ · R · band` form of T4 used by the kernel's `certify`: if both states
are bounded by `R` and differ by at most `band`, the expectations differ by at most
`2‖O‖ · R · band`. -/
theorem observable_propagation_band {F : Type*} [NormedAddCommGroup F]
    [InnerProductSpace ℂ F] (O : F →L[ℂ] F) (u w : F) {R band : ℝ}
    (hu : ‖u‖ ≤ R) (hw : ‖w‖ ≤ R) (hband : ‖u - w‖ ≤ band) :
    |(inner ℂ u (O u)).re - (inner ℂ w (O w)).re| ≤ 2 * ‖O‖ * R * band := by
  refine (observable_propagation O u w).trans ?_
  have hO : (0 : ℝ) ≤ ‖O‖ := norm_nonneg _
  have hR : (0 : ℝ) ≤ R := le_trans (norm_nonneg u) hu
  have hb : (0 : ℝ) ≤ ‖u - w‖ := norm_nonneg _
  have h1 : ‖u‖ + ‖w‖ ≤ 2 * R := by linarith
  calc ‖O‖ * (‖u‖ + ‖w‖) * ‖u - w‖ ≤ ‖O‖ * (2 * R) * ‖u - w‖ :=
        mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hO) hb
    _ ≤ ‖O‖ * (2 * R) * band := mul_le_mul_of_nonneg_left hband (by positivity)
    _ = 2 * ‖O‖ * R * band := by ring

/-! ## 6. T5 — the interval-enclosure core

The only new *trusted* component of the certificate architecture is the
directed-rounding interval layer.  Here it is: a two-sided enclosure type, the
soundness of its arithmetic, an explicit outward-rounding model (a computed endpoint
pair is admissible as soon as it brackets the exact value, which is exactly what
directed rounding guarantees), and the two consequences the mass-gap certificate
uses — a certified supremum over a box from an inclusion-isotone extension, and the
extraction of a certified half-width from an enclosure. -/

/-- A closed real interval, used as an enclosure. -/
structure CertInterval where
  /-- The (rounded-down) lower endpoint. -/
  lo : ℝ
  /-- The (rounded-up) upper endpoint. -/
  hi : ℝ

namespace CertInterval

/-- Membership: `x` is enclosed by `I`. -/
def Mem (I : CertInterval) (x : ℝ) : Prop := I.lo ≤ x ∧ x ≤ I.hi

/-- The width of an enclosure. -/
def width (I : CertInterval) : ℝ := I.hi - I.lo

/-- The midpoint of an enclosure — the "delivered value". -/
def mid (I : CertInterval) : ℝ := (I.lo + I.hi) / 2

/-- Interval addition. -/
def add (I J : CertInterval) : CertInterval := ⟨I.lo + J.lo, I.hi + J.hi⟩

/-- Interval negation. -/
def neg (I : CertInterval) : CertInterval := ⟨-I.hi, -I.lo⟩

/-- Interval subtraction. -/
def sub (I J : CertInterval) : CertInterval := ⟨I.lo - J.hi, I.hi - J.lo⟩

/-- Interval multiplication (the four-corner rule). -/
def mul (I J : CertInterval) : CertInterval :=
  ⟨min (min (I.lo * J.lo) (I.lo * J.hi)) (min (I.hi * J.lo) (I.hi * J.hi)),
   max (max (I.lo * J.lo) (I.lo * J.hi)) (max (I.hi * J.lo) (I.hi * J.hi))⟩

/-- Outward inflation by `ε ≥ 0` — the directed-rounding step. -/
def widen (I : CertInterval) (ε : ℝ) : CertInterval := ⟨I.lo - ε, I.hi + ε⟩

theorem mem_add {I J : CertInterval} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (I.add J).Mem (x + y) :=
  ⟨add_le_add hx.1 hy.1, add_le_add hx.2 hy.2⟩

theorem mem_neg {I : CertInterval} {x : ℝ} (hx : I.Mem x) : I.neg.Mem (-x) :=
  ⟨neg_le_neg hx.2, neg_le_neg hx.1⟩

theorem mem_sub {I J : CertInterval} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (I.sub J).Mem (x - y) :=
  ⟨sub_le_sub hx.1 hy.2, sub_le_sub hx.2 hy.1⟩

private theorem mul_bracket_left (c ylo y yhi : ℝ) (h1 : ylo ≤ y) (h2 : y ≤ yhi) :
    min (c * ylo) (c * yhi) ≤ c * y ∧ c * y ≤ max (c * ylo) (c * yhi) := by
  rcases le_total 0 c with hc | hc
  · exact ⟨le_trans (min_le_left _ _) (by nlinarith), le_trans (by nlinarith) (le_max_right _ _)⟩
  · exact ⟨le_trans (min_le_right _ _) (by nlinarith), le_trans (by nlinarith) (le_max_left _ _)⟩

private theorem mul_bracket_right (xlo x xhi c : ℝ) (h1 : xlo ≤ x) (h2 : x ≤ xhi) :
    min (xlo * c) (xhi * c) ≤ x * c ∧ x * c ≤ max (xlo * c) (xhi * c) := by
  rcases le_total 0 c with hc | hc
  · exact ⟨le_trans (min_le_left _ _) (by nlinarith), le_trans (by nlinarith) (le_max_right _ _)⟩
  · exact ⟨le_trans (min_le_right _ _) (by nlinarith), le_trans (by nlinarith) (le_max_left _ _)⟩

theorem mem_mul {I J : CertInterval} {x y : ℝ} (hx : I.Mem x) (hy : J.Mem y) :
    (I.mul J).Mem (x * y) := by
  obtain ⟨hx1, hx2⟩ := hx
  obtain ⟨hy1, hy2⟩ := hy
  obtain ⟨h1, h1'⟩ := mul_bracket_left I.lo J.lo y J.hi hy1 hy2
  obtain ⟨h2, h2'⟩ := mul_bracket_left I.hi J.lo y J.hi hy1 hy2
  obtain ⟨h3, h3'⟩ := mul_bracket_right I.lo x I.hi y hx1 hx2
  exact ⟨le_trans (min_le_min h1 h2) h3, le_trans h3' (max_le_max h1' h2')⟩

theorem mem_widen {I : CertInterval} {x ε : ℝ} (hx : I.Mem x) (hε : 0 ≤ ε) :
    (I.widen ε).Mem x :=
  ⟨by simp only [widen]; linarith [hx.1], by simp only [widen]; linarith [hx.2]⟩

/-- **The outward-rounding model.**  A floating-point computation delivers a pair of
endpoints; directed (outward) rounding guarantees that the rounded lower endpoint lies
below, and the rounded upper endpoint above, the exact value.  That guarantee — and
nothing about the floating-point values themselves — is what the certificate
consumes. -/
theorem mem_ofRounded {x lo hi : ℝ} (h1 : lo ≤ x) (h2 : x ≤ hi) :
    (CertInterval.mk lo hi).Mem x := ⟨h1, h2⟩

/-- **The certified half-width.**  If both the exact value and the delivered value are
enclosed by the same interval, they differ by at most its width — this is the `h_O`
term of the §4.4 assembled width. -/
theorem dist_le_width {I : CertInterval} {x y : ℝ} (hx : I.Mem x) (hy : I.Mem y) :
    |x - y| ≤ I.width := by
  rw [abs_le]
  exact ⟨by simp only [width]; linarith [hx.1, hy.2],
    by simp only [width]; linarith [hx.2, hy.1]⟩

/-- **The certified supremum (Layer 2, §4.2).**  An interval evaluator that encloses
`f` on every point of the box gives a rigorous upper bound for `f` on the whole box —
unlike the grid maximum computed by the code, which is only a lower bound for the
supremum. -/
theorem le_sup_bound_of_isotone {α : Type*} (f : α → ℝ) (S : Set α) (I : CertInterval)
    (hF : ∀ z ∈ S, I.Mem (f z)) {z : α} (hz : z ∈ S) :
    f z ≤ I.hi := (hF z hz).2

/-- The degenerate enclosure of a constant. -/
theorem mem_const (c : ℝ) : (CertInterval.mk c c).Mem c := ⟨le_rfl, le_rfl⟩

/-- Horner evaluation of a polynomial (coefficients in increasing degree) at a real
point. -/
def polyEval : List ℝ → ℝ → ℝ
  | [], _ => 0
  | c :: cs, x => polyEval cs x * x + c

/-- The interval (Horner) evaluation of the same polynomial: the *interval extension*
that an interval-arithmetic evaluator computes. -/
def evalHorner : List ℝ → CertInterval → CertInterval
  | [], _ => CertInterval.mk 0 0
  | c :: cs, I => ((evalHorner cs I).mul I).add (CertInterval.mk c c)

/-- **The interval evaluator is inclusion-isotone**: the exact value at any point of
the input interval is enclosed by the interval evaluation.  This is the property that
turns a computed enclosure into a rigorous bound over the whole box. -/
theorem mem_evalHorner : ∀ (cs : List ℝ) (I : CertInterval) (x : ℝ), I.Mem x →
    (evalHorner cs I).Mem (polyEval cs x)
  | [], I, x, _ => by
      simpa [evalHorner, polyEval] using mem_const (0 : ℝ)
  | c :: cs, I, x, hx => by
      have hrec := mem_evalHorner cs I x hx
      exact mem_add (mem_mul hrec hx) (mem_const c)

/-- The certified supremum of a polynomial over a box, from one interval evaluation:
no grid, no sampling. -/
theorem polyEval_le_of_mem (cs : List ℝ) (I : CertInterval) {x : ℝ} (hx : I.Mem x) :
    polyEval cs x ≤ (evalHorner cs I).hi := (mem_evalHorner cs I x hx).2

/-- The two-sided version: a certified bound `R_cert ≥ sup |p|` over the box. -/
theorem abs_polyEval_le_of_mem (cs : List ℝ) (I : CertInterval) {x : ℝ} (hx : I.Mem x) :
    |polyEval cs x| ≤ max |(evalHorner cs I).lo| |(evalHorner cs I).hi| := by
  have h := mem_evalHorner cs I x hx
  rw [abs_le]
  constructor
  · have h1 : -|(evalHorner cs I).lo| ≤ (evalHorner cs I).lo := neg_abs_le _
    have h2 : -max |(evalHorner cs I).lo| |(evalHorner cs I).hi| ≤ -|(evalHorner cs I).lo| :=
      neg_le_neg (le_max_left _ _)
    linarith [h.1]
  · have h1 : (evalHorner cs I).hi ≤ |(evalHorner cs I).hi| := le_abs_self _
    have h2 : |(evalHorner cs I).hi| ≤ max |(evalHorner cs I).lo| |(evalHorner cs I).hi| :=
      le_max_right _ _
    linarith [h.2]

/-- The two-sided form, `‖f − p/q‖_{∞,Σ} ≤ R_cert`. -/
theorem abs_le_of_isotone {α : Type*} (f : α → ℝ) (S : Set α) (I : CertInterval)
    (hF : ∀ z ∈ S, I.Mem (f z)) (R : ℝ) (hR : max |I.lo| |I.hi| ≤ R) {z : α} (hz : z ∈ S) :
    |f z| ≤ R := by
  have h := hF z hz
  have h1 : |I.lo| ≤ R := le_trans (le_max_left _ _) hR
  have h2 : |I.hi| ≤ R := le_trans (le_max_right _ _) hR
  rw [abs_le]
  exact ⟨by linarith [neg_abs_le I.lo, h.1], by linarith [le_abs_self I.hi, h.2]⟩

end CertInterval

end BookProof.SirkFinitePrecision

end
