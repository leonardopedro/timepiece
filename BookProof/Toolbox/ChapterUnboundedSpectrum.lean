import Mathlib
import BookProof.Toolbox.ChapterStoneResolvent

/-!
# Resolvent sets and spectra of unbounded operators, and their transport by a bounded

# perturbation

The corpus has two pictures of an unbounded operator and never a spectrum of one: the closure
of a graph (`BookProof.EsaClosure`) and the resolvent `(A - i l)⁻¹` of a self-adjoint operator at
*imaginary* shifts (`BookProof.ChapterStoneResolvent`).  Every `spectrum` in the tree is a
spectrum of a *bounded* operator (or of the bounded Cayley transform).  This module supplies the
missing notion and the one perturbation-theoretic tool that a spectral-containment argument
needs, in the form that does not require the spectral theorem.

## What is proved

* `ResolventAt T z R` — the honest statement that the bounded operator `R` inverts `T - z`:
  `R ((T - z) x) = x` for `x` in the domain and `(T - z) (R y) = y` with `R y` in the domain, for
  every `y` in the Hilbert space.
* `resolventSet T`, `spectrumOf T` — the complement of the set of such `z`, so an unbounded
  spectrum exists as a set; `mem_spectrumOf_iff` unfolds it, and the two membership bridges
  are the complement unfolding.
* `isUnit_one_add_clm_comp` — `1 + B R` is invertible as soon as `‖B‖ ‖R‖ < 1`, by
  `isUnit_one_sub_of_norm_lt_one` applied to `-(B R)`.
* **`resolventAt_add_of_norm_mul_lt_one`** — the Neumann transport: if `R` inverts `T - z` and
  `‖B‖ ‖R‖ < 1`, then `R (1 + B R)⁻¹` inverts `(T + B) - z`, where `T + B` is the operator
  `perturb T B` on the same domain with `B` composed with the domain inclusion.  Both directions
  are the two-line computation `(T - z) x = w`, `R w = x`, hence `w + B x = (1 + B R) w`; nothing
  else is used.
* **`not_mem_spectrumOf_add_of_norm_mul_lt_one`** — the one-sided containment in the form the
  argument takes: a point is *not* in the spectrum of `T + B` as soon as it is out of the
  spectrum of `T` with an explicit resolvent whose norm beats `‖B‖`.
* **`resolventAt_selfAdjoint_imag`, `selfAdjoint_imag_mem_resolventSet`** — the instance: for a
  self-adjoint operator the imaginary shifts `i l` (`l ≠ 0`) are resolvent points, with the
  explicit inverse `T.resCLM l` of `BookProof.ChapterStoneResolvent`.  So the spectrum defined
  here is not exotic: it omits at least the imaginary axis minus the origin.

## What is *not* proved, and why the containment still needs more

A spectral *containment* `σ(T + B) ⊆ σ(T) + S` needs a resolvent for `T` at the points it is
supposed to omit.  The transport above supplies that implication with the hypothesis
`‖B‖ ‖R(z)‖ < 1` **at a point where a resolvent exists**, so it converts a resolvent bound into a
containment and never produces one.  For a self-adjoint `T` the resolvents available in this tree
are `T.resCLM l`, i.e. `z = i l` — the imaginary axis — and `T + B` is self-adjoint there anyway,
so a bound at those points carries no spectral information.  §4 adds the resolvent identity in the
spectral parameter (`resolvent_identity`, `resolventAt_shift`), which makes the resolvent set open
with an explicit Neumann inverse and propagates the imaginary-axis resolvent to the disc of radius
`|l|` about `i l` (`mem_resolventSet_of_near_imag`) — a disc that touches the real axis only in the
limit `l → ∞`.  The missing input is the
**real-axis resolvent bound** `‖(T - x)⁻¹‖ ≤ 1/dist(x, σ(T))` for real `x`, which is a theorem of
the spectral theorem (or of the resolvent identity plus self-adjointness), together with the
characterization of `σ(T)` for self-adjoint `T` as the set of real `x` at which `T - x` fails to
be boundedly invertible.  Neither exists in this tree; see the spectrum boundary note of
`BookProof/Qym/ChapterYangMillsNonAbelianEsa.lean`.
-/

namespace BookProof.UnboundedSpectrum

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H]

/-! ## The resolvent predicate, the resolvent set and the spectrum -/

/-- **`R` inverts `T - z`.**  `R` is bounded (it is a continuous linear map), while `T` is only
densely defined, so both directions are stated on the right sets: `R` is a left inverse of
`T - z` on the domain, and `R` lands in the domain where `T - z` is a right inverse. -/
structure ResolventAt {D : Submodule ℂ H} (T : D →ₗ[ℂ] H) (z : ℂ) (R : H →L[ℂ] H) : Prop where
  /-- `R` inverts `T - z` on the domain. -/
  apply_op : ∀ x : D, R (T x - z • (x : H)) = x
  /-- `R` takes values in the domain, where `T - z` inverts it. -/
  op_apply : ∀ y : H, ∃ h : R y ∈ D, T ⟨R y, h⟩ - z • R y = y

/-- The **resolvent set** of an unbounded operator: the points at which `T - z` has a bounded
two-sided inverse. -/
def resolventSet {D : Submodule ℂ H} (T : D →ₗ[ℂ] H) : Set ℂ :=
  {z | ∃ R, ResolventAt T z R}

/-- The **spectrum** of an unbounded operator, as the complement of the resolvent set. -/
def spectrumOf {D : Submodule ℂ H} (T : D →ₗ[ℂ] H) : Set ℂ :=
  (resolventSet T)ᶜ

theorem mem_resolventSet_iff {D : Submodule ℂ H} {T : D →ₗ[ℂ] H} {z : ℂ} :
    z ∈ resolventSet T ↔ ∃ R, ResolventAt T z R := Iff.rfl

theorem mem_spectrumOf_iff {D : Submodule ℂ H} {T : D →ₗ[ℂ] H} {z : ℂ} :
    z ∈ spectrumOf T ↔ ¬ ∃ R, ResolventAt T z R := Iff.rfl

/-- The spectrum is the complement of the resolvent set, in the usable direction: a point of the
resolvent set is not a spectral point. -/
theorem not_mem_spectrumOf_of_mem_resolventSet {D : Submodule ℂ H} {T : D →ₗ[ℂ] H} {z : ℂ}
    (h : z ∈ resolventSet T) : z ∉ spectrumOf T := by
  simpa only [spectrumOf, Set.mem_compl_iff, not_not] using h

/-- And conversely a spectral point has no bounded inverse of `T - z`. -/
theorem not_mem_resolventSet_of_mem_spectrumOf {D : Submodule ℂ H} {T : D →ₗ[ℂ] H} {z : ℂ}
    (h : z ∈ spectrumOf T) : z ∉ resolventSet T := by
  simpa only [spectrumOf, Set.mem_compl_iff] using h

/-- **The bounded perturbation of an unbounded operator**, on the same domain: `B` composed
with the domain inclusion.  This is the operator `T + B` of the Neumann transport below. -/
def perturb {D : Submodule ℂ H} (T : D →ₗ[ℂ] H) (B : H →L[ℂ] H) : D →ₗ[ℂ] H :=
  T + B.toLinearMap.comp D.subtype

theorem perturb_apply {D : Submodule ℂ H} (T : D →ₗ[ℂ] H) (B : H →L[ℂ] H) (x : D) :
    perturb T B x = T x + B (x : H) := rfl

/-- **The resolvent identity.**  Two left inverses of `T - ·` at different parameters differ by
`(z - w) R_z R_w`, applied to the range of `R_w`. -/
theorem resolvent_identity {D : Submodule ℂ H} {T : D →ₗ[ℂ] H} {w z : ℂ} {Rw Rz : H →L[ℂ] H}
    (hRw : ResolventAt T w Rw) (hRz : ResolventAt T z Rz) (y : H) :
    Rz y = Rw y + (z - w) • Rz (Rw y) := by
  have hmem : Rw y ∈ D := (hRw.op_apply y).1
  have hleft := hRz.apply_op ⟨Rw y, hmem⟩
  have hright : T ⟨Rw y, hmem⟩ - z • Rw y = y - (z - w) • Rw y := by
    have hw := (hRw.op_apply y).2
    calc T ⟨Rw y, hmem⟩ - z • Rw y
        = (T ⟨Rw y, hmem⟩ - w • Rw y) - (z - w) • Rw y := by module
      _ = y - (z - w) • Rw y := by rw [hw]
  rw [hright, map_sub, map_smul] at hleft
  have hsub : Rz y = Rw y + (z - w) • Rz (Rw y) := by
    have := sub_eq_iff_eq_add.mp hleft
    simpa using this
  exact hsub

/-! ## The Neumann transport of a resolvent by a bounded perturbation -/

section Complete

variable [CompleteSpace H]

open BookProof.ChapterStoneResolvent

/-- `1 + B R` is invertible when `‖B‖ ‖R‖ < 1`: the Neumann series converges, and the abstract
statement is `isUnit_one_sub_of_norm_lt_one` applied to `-(B R)`. -/
theorem isUnit_one_add_clm_comp {B R : H →L[ℂ] H} (h : ‖B‖ * ‖R‖ < 1) :
    IsUnit (1 + B.comp R) := by
  have hlt : ‖(-(B.comp R) : H →L[ℂ] H)‖ < 1 := by
    rw [norm_neg]
    exact lt_of_le_of_lt (B.opNorm_comp_le R) h
  simpa [sub_neg_eq_add] using isUnit_one_sub_of_norm_lt_one hlt

/-- The inverse of `1 + B R` as a continuous linear map. -/
noncomputable def neumannInv (B R : H →L[ℂ] H) (h : ‖B‖ * ‖R‖ < 1) : H →L[ℂ] H :=
  ((isUnit_one_add_clm_comp h).unit⁻¹ : (H →L[ℂ] H)ˣ)

theorem neumannInv_mul (B R : H →L[ℂ] H) (h : ‖B‖ * ‖R‖ < 1) :
    neumannInv B R h * (1 + B.comp R) = 1 := by
  unfold neumannInv
  exact IsUnit.val_inv_mul (isUnit_one_add_clm_comp h)

theorem mul_neumannInv (B R : H →L[ℂ] H) (h : ‖B‖ * ‖R‖ < 1) :
    (1 + B.comp R) * neumannInv B R h = 1 := by
  unfold neumannInv
  exact IsUnit.mul_val_inv (isUnit_one_add_clm_comp h)

/-- The two applications of the Neumann inverse, in the exact shape the transport uses. -/
theorem neumannInv_apply_mul (B R : H →L[ℂ] H) (h : ‖B‖ * ‖R‖ < 1) (w : H) :
    neumannInv B R h ((1 + B.comp R) w) = w := by
  rw [← ContinuousLinearMap.mul_apply, neumannInv_mul B R h, ContinuousLinearMap.one_apply]

theorem mul_neumannInv_apply (B R : H →L[ℂ] H) (h : ‖B‖ * ‖R‖ < 1) (y : H) :
    (1 + B.comp R) (neumannInv B R h y) = y := by
  rw [← ContinuousLinearMap.mul_apply, mul_neumannInv B R h, ContinuousLinearMap.one_apply]

/-- **The Neumann transport.**  If `R` inverts `T - z` and `‖B‖ ‖R‖ < 1`, then
`R (1 + B R)⁻¹` inverts `(T + B) - z`.  The identity behind it: for a domain vector `x` with
`w = (T - z) x` one has `(T + B - z) x = w + B x = (1 + B R) w`. -/
theorem resolventAt_add_of_norm_mul_lt_one
    {D : Submodule ℂ H} {T : D →ₗ[ℂ] H} {z : ℂ} {R : H →L[ℂ] H} (hR : ResolventAt T z R)
    {B : H →L[ℂ] H} (hB : ‖B‖ * ‖R‖ < 1) :
    ResolventAt (perturb T B) z (R.comp (neumannInv B R hB)) := by
  have hsplit : ∀ w : H, ((1 + B.comp R) w : H) = w + B (R w) := by
    intro w
    simp
  constructor
  · intro x
    have hRx : R (T x - z • (x : H)) = (x : H) := hR.apply_op x
    have hw : perturb T B x - z • (x : H) = (1 + B.comp R) (T x - z • (x : H)) := by
      calc perturb T B x - z • (x : H)
          = (T x - z • (x : H)) + B (x : H) := by rw [perturb_apply]; abel
        _ = (T x - z • (x : H)) + B (R (T x - z • (x : H))) := by rw [hRx]
        _ = (1 + B.comp R) (T x - z • (x : H)) := (hsplit _).symm
    rw [ContinuousLinearMap.comp_apply, hw, neumannInv_apply_mul B R hB]
    exact hRx
  · intro y
    have hmem : R (neumannInv B R hB y) ∈ D := (hR.op_apply (neumannInv B R hB y)).1
    refine ⟨hmem, ?_⟩
    have hu := (hR.op_apply (neumannInv B R hB y)).2
    have hval : perturb T B ⟨R (neumannInv B R hB y), hmem⟩ - z • R (neumannInv B R hB y)
        = (1 + B.comp R) (neumannInv B R hB y) := by
      calc perturb T B ⟨R (neumannInv B R hB y), hmem⟩ - z • R (neumannInv B R hB y)
          = (T ⟨R (neumannInv B R hB y), hmem⟩ - z • R (neumannInv B R hB y))
              + B (R (neumannInv B R hB y)) := by rw [perturb_apply]; abel
        _ = (neumannInv B R hB y) + B (R (neumannInv B R hB y)) := by rw [hu]
        _ = (1 + B.comp R) (neumannInv B R hB y) := (hsplit _).symm
    simp only [ContinuousLinearMap.comp_apply]
    rw [hval]
    exact mul_neumannInv_apply B R hB y

/-- The one-sided containment, in the form a spectral argument consumes: a point at which `T` has
a resolvent of norm beating `1/‖B‖` is not in the spectrum of `T + B`. -/
theorem not_mem_spectrumOf_add_of_norm_mul_lt_one
    {D : Submodule ℂ H} {T : D →ₗ[ℂ] H} {z : ℂ} {R : H →L[ℂ] H} (hR : ResolventAt T z R)
    {B : H →L[ℂ] H} (hB : ‖B‖ * ‖R‖ < 1) :
    z ∉ spectrumOf (perturb T B) := by
  intro h
  exact h ⟨_, resolventAt_add_of_norm_mul_lt_one hR hB⟩

/-! ## The instance: imaginary shifts of a self-adjoint operator

This is what makes `spectrumOf` a real definition rather than an empty one, and it is exactly the
resolvent the tree already has: `T.resCLM l` inverts `T - i l`.  Note that no spectral
information is produced — `i l` is imaginary and `T + B` is self-adjoint there too — which is why
the containment of the module docstring still needs a real-axis input.
-/

/-- The imaginary shift `i l` of a self-adjoint operator is a resolvent point, with the explicit
bounded inverse `T.resCLM l`. -/
theorem resolventAt_selfAdjoint_imag (T : UnboundedSelfAdjoint H) {l : ℝ} (hl : l ≠ 0) :
    ResolventAt T.op ((l : ℂ) * Complex.I) (T.resCLM l) := by
  constructor
  · intro x
    show (T.resCLM l) (T.op x - ((l : ℂ) * Complex.I) • (x : H)) = (x : H)
    rw [← UnboundedSelfAdjoint.shift_apply T l x, UnboundedSelfAdjoint.resCLM_apply T]
    exact congrArg Subtype.val (UnboundedSelfAdjoint.res_shift T hl x)
  · intro y
    exact ⟨UnboundedSelfAdjoint.resCLM_mem T l y, UnboundedSelfAdjoint.shift_res T hl y⟩

theorem selfAdjoint_imag_mem_resolventSet (T : UnboundedSelfAdjoint H) {l : ℝ} (hl : l ≠ 0) :
    ((l : ℂ) * Complex.I) ∈ resolventSet T.op :=
  ⟨_, resolventAt_selfAdjoint_imag T hl⟩

theorem selfAdjoint_imag_not_mem_spectrumOf (T : UnboundedSelfAdjoint H) {l : ℝ} (hl : l ≠ 0) :
    ((l : ℂ) * Complex.I) ∉ spectrumOf T.op :=
  not_mem_spectrumOf_of_mem_resolventSet (selfAdjoint_imag_mem_resolventSet T hl)

/-! ## 4. The resolvent identity: transport in the spectral parameter

The transport of §3 moves the *operator* by a bounded perturbation at a fixed parameter.  The
transport below moves the *parameter* at a fixed operator, which is what makes the resolvent set
open and is the algebraic form of the resolvent identity
`R_z - R_w = (z - w) R_z R_w`.  Nothing here is specific to self-adjoint operators: it is the
identity `(T - z) = (1 - (z - w) R_w) (T - w)` read at the level of bounded inverses. -/

/-- `1 - (z - w) R` is invertible when `‖z - w‖ ‖R‖ < 1`; the Neumann series of §3 in the
spectral parameter. -/
theorem isUnit_one_sub_smul (R : H →L[ℂ] H) {w z : ℂ} (h : ‖z - w‖ * ‖R‖ < 1) :
    IsUnit (1 - (z - w) • R : H →L[ℂ] H) := by
  have hnorm : ‖(z - w) • R‖ < 1 := lt_of_le_of_lt (norm_smul_le _ _) h
  simpa [sub_eq_add_neg] using isUnit_one_sub_of_norm_lt_one hnorm

/-- **The resolvent set is open, with the Neumann inverse as witness.**  If `R` inverts `T - w` and
`‖z - w‖ ‖R‖ < 1`, then `R (1 - (z - w) R)⁻¹` inverts `T - z`.  So a resolvent point `w` propagates
to the whole disc of radius `1/‖R‖` around it, which is the step a spectral-containment argument
uses at a point where a resolvent is already known. -/
theorem resolventAt_shift {D : Submodule ℂ H} {T : D →ₗ[ℂ] H} {w z : ℂ} {R : H →L[ℂ] H}
    (hR : ResolventAt T w R) (h : ‖z - w‖ * ‖R‖ < 1) :
    ResolventAt T z
      (R.comp ((((isUnit_one_sub_smul R h).unit)⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H)) := by
  set N : H →L[ℂ] H := 1 - (z - w) • R with hNdef
  have hu : IsUnit N := isUnit_one_sub_smul R h
  set u : H →L[ℂ] H := ((hu.unit⁻¹ : (H →L[ℂ] H)ˣ) : H →L[ℂ] H) with hudef
  have huN : u * N = 1 := IsUnit.val_inv_mul hu
  have hNu : N * u = 1 := IsUnit.mul_val_inv hu
  have hleft : ∀ y : H, u (N y) = y := by
    intro y
    rw [← ContinuousLinearMap.mul_apply, huN, ContinuousLinearMap.one_apply]
  have hright : ∀ y : H, N (u y) = y := by
    intro y
    rw [← ContinuousLinearMap.mul_apply, hNu, ContinuousLinearMap.one_apply]
  have hN_apply : ∀ y : H, N y = y - (z - w) • R y := by
    intro y
    rw [hNdef, ContinuousLinearMap.sub_apply, ContinuousLinearMap.one_apply,
      ContinuousLinearMap.smul_apply]
  constructor
  · intro x
    have hx : R (T x - w • (x : H)) = (x : H) := hR.apply_op x
    have hNw : N (T x - w • (x : H)) = T x - z • (x : H) := by
      rw [hN_apply, hx]
      module
    change (R.comp u) (T x - z • (x : H)) = (x : H)
    rw [← hNw, ContinuousLinearMap.comp_apply, hleft, hx]
  · intro y
    have hmem : R (u y) ∈ D := (hR.op_apply (u y)).1
    refine ⟨hmem, ?_⟩
    have hstep := (hR.op_apply (u y)).2
    change T ⟨R (u y), hmem⟩ - z • R (u y) = y
    calc T ⟨R (u y), hmem⟩ - z • R (u y)
        = (T ⟨R (u y), hmem⟩ - w • R (u y)) - (z - w) • R (u y) := by module
      _ = u y - (z - w) • R (u y) := by rw [hstep]
      _ = N (u y) := by rw [hN_apply]
      _ = y := hright y

/-- **Resolvents exist in a strip around the imaginary axis, by the resolvent identity.**  With the
explicit bound `‖(T - i l)⁻¹‖ ≤ 1/|l|` of `BookProof.ChapterStoneResolvent`, the parameter transport
above propagates that resolvent point to every `z` with `‖z - i l‖ < |l|`:

  `‖z - i l‖ ‖(T - i l)⁻¹‖ ≤ ‖z - i l‖ / |l| < 1`.

This is the real content the resolvent identity buys: the resolvent set contains the open disc of
radius `|l|` about `i l`, i.e. it reaches the real axis only in the limit `l → ∞`.  The bound is
*not* a real-axis bound — the distance from `i l` to the real axis is exactly `|l|`, so no choice of
`l` puts a real point strictly inside the disc without first knowing a resolvent there. -/
theorem mem_resolventSet_of_near_imag (T : UnboundedSelfAdjoint H) {l : ℝ} (hl : l ≠ 0) {z : ℂ}
    (hz : ‖z - (l : ℂ) * Complex.I‖ * (1 / |l|) < 1) : z ∈ resolventSet T.op := by
  have hlpos : 0 < |l| := abs_pos.mpr hl
  have hop : ‖T.resCLM l‖ ≤ 1 / |l| :=
    ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun y =>
      UnboundedSelfAdjoint.norm_resCLM_apply_le T l y
  refine ⟨_, resolventAt_shift (resolventAt_selfAdjoint_imag T hl) ?_⟩
  exact lt_of_le_of_lt (mul_le_mul_of_nonneg_left hop (norm_nonneg _)) hz

/-- **The resolvent set of an unbounded operator is open**, and consequently its spectrum is
closed.  This is `resolventAt_shift` read as a neighbourhood statement: at a resolvent point `w`
with inverse `R`, the disc of radius `1/(‖R‖ + 1)` about `w` stays in the resolvent set. -/
theorem isOpen_resolventSet {D : Submodule ℂ H} (T : D →ₗ[ℂ] H) : IsOpen (resolventSet T) := by
  refine Metric.isOpen_iff.mpr fun z hz => ?_
  obtain ⟨R, hR⟩ := hz
  refine ⟨1 / (‖R‖ + 1), by positivity, fun z' hz' => ?_⟩
  have hball : ‖z' - z‖ < 1 / (‖R‖ + 1) := by
    simpa [dist_eq_norm] using hz'
  have hRpos : (0 : ℝ) < ‖R‖ + 1 := by positivity
  have h1 : ‖z' - z‖ * ‖R‖ ≤ (1 / (‖R‖ + 1)) * ‖R‖ :=
    mul_le_mul_of_nonneg_right hball.le (norm_nonneg R)
  have h2 : (1 / (‖R‖ + 1)) * ‖R‖ < 1 := by
    rw [div_mul_eq_mul_div, one_mul, div_lt_one hRpos]
    linarith [norm_nonneg R]
  exact ⟨_, resolventAt_shift hR (lt_of_le_of_lt h1 h2)⟩

/-- **The spectrum of an unbounded operator is closed.** -/
theorem isClosed_spectrumOf {D : Submodule ℂ H} (T : D →ₗ[ℂ] H) : IsClosed (spectrumOf T) := by
  have h := isOpen_resolventSet T
  simpa only [spectrumOf] using h.isClosed_compl

end Complete

end BookProof.UnboundedSpectrum
