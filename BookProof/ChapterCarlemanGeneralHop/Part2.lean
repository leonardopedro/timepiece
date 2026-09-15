import Mathlib
import BookProof.ChapterCarlemanTwoStep
import BookProof.ChapterCarlemanGeneralHop.Part1

/-!
# A Carleman criterion for general lattice hops

`BookProof.ChapterHermiteCarlemanEsa` and `BookProof.ChapterCarlemanTwoStep` prove
Carleman (flux) criteria for recursions whose hops move a **single** excitation number,
by one or by two.  That covers every **mode-diagonal** quadratic Hamiltonian.  A quadratic
Hamiltonian which couples two *distinct* modes — `xᵢxⱼ`, `πᵢπⱼ`, `xᵢπⱼ` with `i ≠ j` —
produces hops `α ↦ α ± (eᵢ + eⱼ)` and `α ↦ α ± (eᵢ − eⱼ)`, and the second kind is **not**
monotone: the shift lowers one coordinate while raising another.

This module runs the flux argument for a hop of the completely general shape
`α ↦ α + p − m` (`hshift`), with `p` and `m` multi-indices.

## What is proved

* `hshift`, `hshift_hshift` — the shift and its inverse on the set where it is defined.
* `rtG`, `ltG`, `hopB`, `sum_ltG`, `sum_hop_im` — **the abstract flux cancellation.**  For
  a Hermitian hop family, the contributions from pairs `α, α + p − m` which both lie in a
  finite set `A` cancel in the imaginary part, so the imaginary part of the total is
  carried by two boundary layers: the *outgoing* layer `A \ B` (points of `A` whose image
  leaves `A`) and the *incoming* layer `B \ A` (points outside `A` whose image lands in
  `A`).  For a monotone hop (`m = 0`) the incoming layer is empty and this specialises to
  the situation of the two earlier modules.
-/

namespace BookProof.CarlemanGeneralHop

open Finset
open BookProof.HermiteCarleman
open BookProof.CarlemanTwoStep

noncomputable section

variable {d : ℕ}

variable {u : (Fin d →₀ ℕ) → ℂ}
/-! ## 6. The recursion and the criterion -/

/-- **A general-hop ladder recursion.**  A real diagonal `lam`, and a finite family of
Hermitian hops `α ↦ α + p h − m h` with constant amplitudes `w h`. -/
def LadderRecH (u : (Fin d →₀ ℕ) → ℂ) (lam : (Fin d →₀ ℕ) → ℝ) {ι : Type*} [Fintype ι]
    (p m : ι → (Fin d →₀ ℕ)) (c c' : ι → (Fin d →₀ ℕ) → ℝ) (w : ι → ℂ) (z : ℂ) : Prop :=
  ∀ a : Fin d →₀ ℕ,
    ((lam a : ℝ) : ℂ) * u a
      + ∑ h : ι, ((starRingEnd ℂ) (w h) * ((c h a : ℝ) : ℂ) * u (hshift (p h) (m h) a)
          + w h * ((c' h a : ℝ) : ℂ) * u (hshift (m h) (p h) a))
      = z * u a

variable {ι : Type*} [Fintype ι] {lam : (Fin d →₀ ℕ) → ℝ} {p m : ι → (Fin d →₀ ℕ)}
  {c c' : ι → (Fin d →₀ ℕ) → ℝ} {w : ι → ℂ} {z : ℂ}

/-- **The flux identity** for a general-hop recursion. -/
theorem flux_identityH
    (hcomp : ∀ (h : ι) (b : Fin d →₀ ℕ), (∀ k, m h k ≤ b k) →
      c' h (hshift (p h) (m h) b) = c h b)
    (hvanL : ∀ (h : ι) (a : Fin d →₀ ℕ), ¬ (∀ k, p h k ≤ a k) → c' h a = 0)
    (hrec : LadderRecH u lam p m c c' w z) (N : ℕ) :
    z.im * (∑ a ∈ cube d N, ‖u a‖ ^ 2)
      = ∑ h : ι, ((∑ a ∈ cube d N \ hopB (cube d N) (p h) (m h),
            rtG u (w h) (c h) (p h) (m h) a).im
          - (∑ b ∈ hopB (cube d N) (p h) (m h) \ cube d N,
            rtG u (w h) (c h) (p h) (m h) b).im) := by
  classical
  have hcm : ∀ v : ℂ, (starRingEnd ℂ) v * v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    intro v; rw [Complex.conj_mul']; norm_cast
  have hpt : ∀ a : Fin d →₀ ℕ, (starRingEnd ℂ) (u a) * (z * u a)
      = ((lam a : ℝ) : ℂ) * ((‖u a‖ ^ 2 : ℝ) : ℂ)
        + ∑ h : ι, (rtG u (w h) (c h) (p h) (m h) a
            + ltG u (w h) (c' h) (p h) (m h) a) := by
    intro a
    rw [← hrec a, mul_add, Finset.mul_sum]
    congr 1
    · rw [← hcm (u a)]; ring
    · refine Finset.sum_congr rfl fun h _ => ?_
      rw [rtG, ltG]; ring
  have hL : ∑ a ∈ cube d N, (starRingEnd ℂ) (u a) * (z * u a)
      = z * ((∑ a ∈ cube d N, ‖u a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hcm (u a)]; ring
  have hR : ∑ a ∈ cube d N, (starRingEnd ℂ) (u a) * (z * u a)
      = ((∑ a ∈ cube d N, lam a * ‖u a‖ ^ 2 : ℝ) : ℂ)
        + ∑ h : ι, ∑ a ∈ cube d N, (rtG u (w h) (c h) (p h) (m h) a
            + ltG u (w h) (c' h) (p h) (m h) a) := by
    calc ∑ a ∈ cube d N, (starRingEnd ℂ) (u a) * (z * u a)
        = ∑ a ∈ cube d N, (((lam a : ℝ) : ℂ) * ((‖u a‖ ^ 2 : ℝ) : ℂ)
            + ∑ h : ι, (rtG u (w h) (c h) (p h) (m h) a
              + ltG u (w h) (c' h) (p h) (m h) a)) :=
          Finset.sum_congr rfl fun a _ => hpt a
      _ = (∑ a ∈ cube d N, ((lam a : ℝ) : ℂ) * ((‖u a‖ ^ 2 : ℝ) : ℂ))
            + ∑ a ∈ cube d N, ∑ h : ι, (rtG u (w h) (c h) (p h) (m h) a
              + ltG u (w h) (c' h) (p h) (m h) a) := Finset.sum_add_distrib
      _ = ((∑ a ∈ cube d N, lam a * ‖u a‖ ^ 2 : ℝ) : ℂ)
            + ∑ h : ι, ∑ a ∈ cube d N, (rtG u (w h) (c h) (p h) (m h) a
              + ltG u (w h) (c' h) (p h) (m h) a) := by
          rw [Finset.sum_comm (s := cube d N) (t := Finset.univ)]
          push_cast
          ring_nf
  have hEq := hL.symm.trans hR
  have hLim : (z * ((∑ a ∈ cube d N, ‖u a‖ ^ 2 : ℝ) : ℂ)).im
      = z.im * (∑ a ∈ cube d N, ‖u a‖ ^ 2) := by
    rw [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add]
  rw [← hLim, hEq, Complex.add_im, Complex.ofReal_im, zero_add, Complex.im_sum]
  exact Finset.sum_congr rfl fun h _ => sum_hop_im (hcomp h) (hvanL h) (cube d N)

/-- **The general-hop Carleman criterion.**  A square-summable family satisfying a
recursion with a real diagonal, hops of size at most two which lower at most one
excitation number, and amplitudes of size `O(N)` on the cube of side `N`, at a point off
the real axis, vanishes identically. -/
theorem ladderH_eq_zero {B Camp : ℝ} (hz : z.im ≠ 0) (hCamp : 0 ≤ Camp)
    (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B)
    (hp : ∀ (h : ι) (k : Fin d), p h k ≤ 2) (hm1 : ∀ (h : ι) (k : Fin d), m h k ≤ 1)
    (hcomp : ∀ (h : ι) (b : Fin d →₀ ℕ), (∀ k, m h k ≤ b k) →
      c' h (hshift (p h) (m h) b) = c h b)
    (hvanL : ∀ (h : ι) (a : Fin d →₀ ℕ), ¬ (∀ k, p h k ≤ a k) → c' h a = 0)
    (hvanR : ∀ (h : ι) (a : Fin d →₀ ℕ), ¬ (∀ k, m h k ≤ a k) → c h a = 0)
    (hbnd : ∀ (h : ι) (a : Fin d →₀ ℕ) (N : ℕ), (∀ k, a k ≤ N) →
      |c h a| ≤ Camp * ((N : ℝ) + 1))
    (hrec : LadderRecH u lam p m c c' w z) : ∀ a, u a = 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨a₀, ha₀⟩ := hcon
  set massO : ℕ → ι → ℝ := fun N h =>
    (∑ a ∈ obd d N (p h) (m h),
      (‖u a‖ ^ 2 + ‖u (hshift (p h) (m h) a)‖ ^ 2)) / 2 with hmassO
  set massI : ℕ → ι → ℝ := fun N h =>
    (∑ b ∈ ibd d N (m h),
      (‖u b‖ ^ 2 + ‖u (hshift (p h) (m h) b)‖ ^ 2)) / 2 with hmassI
  set A : ℕ → ℝ := fun N => ∑ h : ι, ‖w h‖ * (massO N h + massI N h) with hAdef
  have hmassO_nonneg : ∀ N h, 0 ≤ massO N h := by
    intro N h
    have : 0 ≤ ∑ a ∈ obd d N (p h) (m h),
        (‖u a‖ ^ 2 + ‖u (hshift (p h) (m h) a)‖ ^ 2) :=
      Finset.sum_nonneg fun a _ => by positivity
    rw [hmassO]; positivity
  have hmassI_nonneg : ∀ N h, 0 ≤ massI N h := by
    intro N h
    have : 0 ≤ ∑ b ∈ ibd d N (m h),
        (‖u b‖ ^ 2 + ‖u (hshift (p h) (m h) b)‖ ^ 2) :=
      Finset.sum_nonneg fun a _ => by positivity
    rw [hmassI]; positivity
  have hAnn : ∀ N, 0 ≤ A N := by
    intro N
    exact Finset.sum_nonneg fun h _ =>
      mul_nonneg (norm_nonneg _) (by linarith [hmassO_nonneg N h, hmassI_nonneg N h])
  -- the total boundary mass is finite
  have hmass_sum : ∀ (h : ι) (M : ℕ),
      ∑ N ∈ Finset.range M, (massO N h + massI N h) ≤ 3 * B := by
    intro h M
    have h1 := obd_mass_le (u := u) hbes (p h) (m h) (hp h) M
    have h2 := obd_shift_mass_le (u := u) hbes (p h) (m h) (hp h) M
    have h3 := ibd_mass_le (u := u) hbes (m h) M
    have h4 := ibd_shift_mass_le (u := u) hbes (p h) (m h) M
    have hO : ∀ N : ℕ, massO N h
        = ((∑ a ∈ obd d N (p h) (m h), ‖u a‖ ^ 2)
            + ∑ a ∈ obd d N (p h) (m h), ‖u (hshift (p h) (m h) a)‖ ^ 2) / 2 := by
      intro N; simp only [hmassO]; rw [Finset.sum_add_distrib]
    have hI : ∀ N : ℕ, massI N h
        = ((∑ b ∈ ibd d N (m h), ‖u b‖ ^ 2)
            + ∑ b ∈ ibd d N (m h), ‖u (hshift (p h) (m h) b)‖ ^ 2) / 2 := by
      intro N; simp only [hmassI]; rw [Finset.sum_add_distrib]
    simp_rw [hO, hI]
    rw [Finset.sum_add_distrib, ← Finset.sum_div, ← Finset.sum_div,
      Finset.sum_add_distrib, Finset.sum_add_distrib]
    linarith
  have hApart : ∀ M, ∑ N ∈ Finset.range M, A N ≤ (∑ h : ι, ‖w h‖) * (3 * B) := by
    intro M
    rw [hAdef, Finset.sum_comm, Finset.sum_mul]
    refine Finset.sum_le_sum fun h _ => ?_
    calc ∑ N ∈ Finset.range M, ‖w h‖ * (massO N h + massI N h)
        = ‖w h‖ * ∑ N ∈ Finset.range M, (massO N h + massI N h) := by rw [Finset.mul_sum]
      _ ≤ ‖w h‖ * (3 * B) := mul_le_mul_of_nonneg_left (hmass_sum h M) (norm_nonneg _)
  have hsummable : Summable A := summable_of_sum_range_le hAnn hApart
  -- the flux bound with the uniform amplitude bound `2·Camp·(N+1)`
  have hCn : ∀ N : ℕ, (0 : ℝ) ≤ 2 * Camp * ((N : ℝ) + 1) := by
    intro N; positivity
  have hCO : ∀ (N : ℕ) (h : ι), ∀ a ∈ obd d N (p h) (m h),
      |c h a| ≤ 2 * Camp * ((N : ℝ) + 1) := by
    intro N h a ha
    rw [mem_obd] at ha
    have := hbnd h a N ha.1
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hCI : ∀ (N : ℕ) (h : ι), ∀ b ∈ ibd d N (m h),
      |c h b| ≤ 2 * Camp * ((N : ℝ) + 1) := by
    intro N h b hb
    rw [mem_ibd] at hb
    have := hbnd h b (N + 1) hb.1
    push_cast at this
    nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have hkey : ∀ N : ℕ,
      |z.im| * (∑ a ∈ cube d N, ‖u a‖ ^ 2) ≤ (2 * Camp * ((N : ℝ) + 1)) * A N := by
    intro N
    have hS : 0 ≤ ∑ a ∈ cube d N, ‖u a‖ ^ 2 := Finset.sum_nonneg fun a _ => by positivity
    have h1 : |z.im| * (∑ a ∈ cube d N, ‖u a‖ ^ 2)
        = |∑ h : ι, ((∑ a ∈ cube d N \ hopB (cube d N) (p h) (m h),
              rtG u (w h) (c h) (p h) (m h) a).im
            - (∑ b ∈ hopB (cube d N) (p h) (m h) \ cube d N,
              rtG u (w h) (c h) (p h) (m h) b).im)| := by
      rw [← flux_identityH hcomp hvanL hrec N, abs_mul, abs_of_nonneg hS]
    rw [h1]
    have hterm : ∀ h : ι,
        |(∑ a ∈ cube d N \ hopB (cube d N) (p h) (m h),
            rtG u (w h) (c h) (p h) (m h) a).im
          - (∑ b ∈ hopB (cube d N) (p h) (m h) \ cube d N,
            rtG u (w h) (c h) (p h) (m h) b).im|
        ≤ (2 * Camp * ((N : ℝ) + 1)) * (‖w h‖ * (massO N h + massI N h)) := by
      intro h
      have hO := flux_bound_gen (u := u) (w := w h) (c := c h) (p := p h) (m := m h)
        (cube d N \ hopB (cube d N) (p h) (m h)) (obd d N (p h) (m h))
        (fun a ha hna => amp_eq_zero_of_not_mem_obd (hvanR h) ha hna) (hCn N) (hCO N h)
      have hI := flux_bound_gen (u := u) (w := w h) (c := c h) (p := p h) (m := m h)
        (hopB (cube d N) (p h) (m h) \ cube d N) (ibd d N (m h))
        (fun b hb hnb => absurd (in_mem_ibd (hm1 h) hb) hnb) (hCn N) (hCI N h)
      have habs := abs_sub (G := ℝ) ((∑ a ∈ cube d N \ hopB (cube d N) (p h) (m h),
            rtG u (w h) (c h) (p h) (m h) a).im)
          ((∑ b ∈ hopB (cube d N) (p h) (m h) \ cube d N,
            rtG u (w h) (c h) (p h) (m h) b).im)
      rw [hmassO, hmassI]
      simp only
      nlinarith [hO, hI, habs]
    calc |∑ h : ι, ((∑ a ∈ cube d N \ hopB (cube d N) (p h) (m h),
              rtG u (w h) (c h) (p h) (m h) a).im
            - (∑ b ∈ hopB (cube d N) (p h) (m h) \ cube d N,
              rtG u (w h) (c h) (p h) (m h) b).im)|
        ≤ ∑ h : ι, |(∑ a ∈ cube d N \ hopB (cube d N) (p h) (m h),
              rtG u (w h) (c h) (p h) (m h) a).im
            - (∑ b ∈ hopB (cube d N) (p h) (m h) \ cube d N,
              rtG u (w h) (c h) (p h) (m h) b).im| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ h : ι, (2 * Camp * ((N : ℝ) + 1)) * (‖w h‖ * (massO N h + massI N h)) :=
          Finset.sum_le_sum fun h _ => hterm h
      _ = (2 * Camp * ((N : ℝ) + 1)) * A N := by rw [hAdef, Finset.mul_sum]
  -- the cube mass is bounded below
  set N₀ : ℕ := Finset.univ.sup (fun i : Fin d => a₀ i) with hN₀
  have hlow : ∀ N : ℕ, N₀ ≤ N → ‖u a₀‖ ^ 2 ≤ ∑ a ∈ cube d N, ‖u a‖ ^ 2 := by
    intro N hN
    refine Finset.single_le_sum (f := fun a => ‖u a‖ ^ 2) (fun a _ => by positivity) ?_
    rw [mem_cube]
    intro i
    exact le_trans (Finset.le_sup (f := fun i : Fin d => a₀ i) (Finset.mem_univ i)) hN
  have hcpos : 0 < |z.im| * ‖u a₀‖ ^ 2 := by
    have h1 : 0 < |z.im| := abs_pos.mpr hz
    have h2 : 0 < ‖u a₀‖ := norm_pos_iff.mpr ha₀
    positivity
  have hCpos : 0 < Camp := by
    by_contra hle
    push_neg at hle
    have hC0 : Camp = 0 := le_antisymm hle hCamp
    have := hkey N₀
    rw [hC0] at this
    simp only [mul_zero, zero_mul] at this
    have := hlow N₀ le_rfl
    nlinarith [abs_pos.mpr hz, sq_nonneg ‖u a₀‖]
  have hAlow : ∀ N : ℕ, N₀ ≤ N →
      ((|z.im| * ‖u a₀‖ ^ 2) / (2 * Camp)) * ((N : ℝ) + 1)⁻¹ ≤ A N := by
    intro N hN
    have hpos : (0 : ℝ) < 2 * Camp * ((N : ℝ) + 1) := by positivity
    have h1 := hkey N
    have h2 := hlow N hN
    have h3 : |z.im| * ‖u a₀‖ ^ 2 ≤ (2 * Camp * ((N : ℝ) + 1)) * A N := by
      nlinarith [abs_nonneg z.im]
    have h5 : ((|z.im| * ‖u a₀‖ ^ 2) / (2 * Camp)) * ((N : ℝ) + 1)⁻¹
        = (|z.im| * ‖u a₀‖ ^ 2) / (2 * Camp * ((N : ℝ) + 1)) := by
      field_simp
    rw [h5, div_le_iff₀ hpos]
    linarith [h3, mul_comm (2 * Camp * ((N : ℝ) + 1)) (A N)]
  have hshiftA : Summable (fun N : ℕ => A (N + N₀)) := (summable_nat_add_iff N₀).mpr hsummable
  have hcomp2 : Summable (fun N : ℕ =>
      ((|z.im| * ‖u a₀‖ ^ 2) / (2 * Camp)) * (((N + N₀ : ℕ) : ℝ) + 1)⁻¹) := by
    refine Summable.of_nonneg_of_le (fun N => by positivity) (fun N => ?_) hshiftA
    exact hAlow (N + N₀) (Nat.le_add_left _ _)
  have h4 : Summable (fun N : ℕ => (((N + N₀ : ℕ) : ℝ) + 1)⁻¹) := by
    have hne : ((|z.im| * ‖u a₀‖ ^ 2) / (2 * Camp)) ≠ 0 := by positivity
    have h5 := hcomp2.mul_left ((|z.im| * ‖u a₀‖ ^ 2) / (2 * Camp))⁻¹
    refine h5.congr fun N => ?_
    field_simp
  exact CarlemanTwoStep.not_summable_inv_natCast_succ ((summable_nat_add_iff N₀).mp h4)

end

end BookProof.CarlemanGeneralHop
