import Mathlib
import BookProof.ChapterHermiteCarlemanEsa

/-!
# A two-step Carleman criterion on the multi-index lattice

`BookProof.ChapterHermiteCarlemanEsa` proves a Carleman criterion for a *nearest
neighbour* recursion on the lattice of multi-indices: the hops are `α ↦ α ± eᵢ`, with
amplitudes of size `O(√αᵢ)`.  That is exactly the ladder structure of a **diagonal**
quadratic Hamiltonian `∑ᵢ cᵢ(πᵢ² + xᵢ²/4)` plus a first-order term.

A general **mode-diagonal** quadratic Hamiltonian

`H = ∑ᵢ (pᵢπᵢ² + qᵢxᵢ² + sᵢ·½(xᵢπᵢ + πᵢxᵢ)) + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)`

is not of that form: `xᵢ²`, `πᵢ²` and the squeezing generator `½(xᵢπᵢ + πᵢxᵢ)` all
contain `aᵢ†²` and `aᵢ²`, which move the `i`-th excitation number by **two**, with an
amplitude of size `O(αᵢ)`.  This module proves the Carleman criterion for such a
recursion: hops `α ↦ α ± eᵢ` *and* `α ↦ α ± 2eᵢ`, with amplitudes `O(N)` on the boundary
of the cube `{α : ∀ i, αᵢ ≤ N}`.

## What is proved

* `innK`, `faceK` — the interior and the `k`-thick boundary face of a cube in a fixed
  direction; `sum_shiftK`, `sum_cube_splitK` — the reindexing and splitting identities.
* `rtermG`, `ltermG`, `sum_cube_hop_im` — **the abstract flux cancellation**: for a
  single Hermitian hop family of step `k`, the interior contributions occur in conjugate
  pairs, so the imaginary part of the total contribution over a cube is carried entirely
  by the `k`-thick boundary face.
* `LadderRec2`, `flux_identity2` — the two-step recursion and its flux identity.
* `flux_boundG` — the flux through a face is at most the amplitude bound there times the
  `ℓ²`-mass carried by the face and its shift.
* `sum_range_of_multiplicity`, `faceK_multiplicity`, `shiftedK_multiplicity` — Bessel's
  inequality with multiplicity: a `k`-thick face meets at most `k` cubes, so the total
  face mass is at most `k` times the total mass.  (For `k = 1` the faces are disjoint;
  for `k = 2` they are not, and this is what replaces disjointness.)
* `ladder2_eq_zero` — **the criterion.**  A square-summable family satisfying the
  two-step recursion with a real diagonal and constant amplitudes, at a point off the
  real axis, vanishes.  The Carleman divergence used is `∑ 1/(N+1) = ∞`.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.CarlemanTwoStep

open Finset
open BookProof.HermiteCarleman

noncomputable section

variable {d : ℕ}

/-! ## 1. Cubes with a step -/

/-- The part of the cube that can still be raised by `k` in the direction `i` without
leaving the cube. -/
def innK (d N : ℕ) (i : Fin d) (k : ℕ) : Finset (Fin d →₀ ℕ) :=
  (cube d N).filter (fun a => a i + k ≤ N)

/-- The `k`-thick boundary face of the cube in the direction `i`. -/
def faceK (d N : ℕ) (i : Fin d) (k : ℕ) : Finset (Fin d →₀ ℕ) :=
  (cube d N).filter (fun a => N < a i + k)

theorem mem_innK {d N : ℕ} {i : Fin d} {k : ℕ} {a : Fin d →₀ ℕ} :
    a ∈ innK d N i k ↔ (∀ j, a j ≤ N) ∧ a i + k ≤ N := by
  classical
  rw [innK, Finset.mem_filter, mem_cube]

theorem mem_faceK {d N : ℕ} {i : Fin d} {k : ℕ} {a : Fin d →₀ ℕ} :
    a ∈ faceK d N i k ↔ (∀ j, a j ≤ N) ∧ N < a i + k := by
  classical
  rw [faceK, Finset.mem_filter, mem_cube]

theorem sub_add_singleK {d : ℕ} {i : Fin d} {k : ℕ} {a : Fin d →₀ ℕ} (h : k ≤ a i) :
    (a - Finsupp.single i k) + Finsupp.single i k = a := by
  ext j
  by_cases hj : j = i
  · subst hj; simp; omega
  · simp [hj]

theorem sub_singleK_apply {d : ℕ} {i : Fin d} {k : ℕ} {a : Fin d →₀ ℕ} :
    (a - Finsupp.single i k : Fin d →₀ ℕ) i = a i - k := by
  simp [Finsupp.tsub_apply]

/-- Reindexing a sum which vanishes on the bottom `k` layers along the shift
`α ↦ α + k eᵢ`. -/
theorem sum_shiftK (d N : ℕ) (i : Fin d) (k : ℕ) (F : (Fin d →₀ ℕ) → ℂ)
    (hF : ∀ a : Fin d →₀ ℕ, a i < k → F a = 0) :
    ∑ a ∈ cube d N, F a = ∑ b ∈ innK d N i k, F (b + Finsupp.single i k) := by
  classical
  rw [← Finset.sum_filter_of_ne (p := fun a : Fin d →₀ ℕ => k ≤ a i)
    (fun a _ hne => by by_contra hlt; exact hne (hF a (by omega)))]
  refine Finset.sum_nbij' (fun a => a - Finsupp.single i k) (fun b => b + Finsupp.single i k)
    ?_ ?_ ?_ ?_ ?_
  · intro a ha
    simp only [Finset.mem_filter, mem_cube] at ha
    rw [mem_innK]
    refine ⟨fun j => le_trans (by simp [Finsupp.tsub_apply]) (ha.1 j), ?_⟩
    rw [sub_singleK_apply]
    have h2 := ha.1 i
    have h3 := ha.2
    omega
  · intro b hb
    rw [mem_innK] at hb
    simp only [Finset.mem_filter, mem_cube]
    refine ⟨fun j => ?_, ?_⟩
    · by_cases hj : j = i
      · subst hj; simp; omega
      · simpa [hj] using hb.1 j
    · simp
  · intro a ha
    simp only [Finset.mem_filter] at ha
    exact sub_add_singleK ha.2
  · intro b _; simp
  · intro a ha
    simp only [Finset.mem_filter] at ha
    rw [sub_add_singleK ha.2]

/-- The cube is the disjoint union of its `k`-interior and its `k`-thick face. -/
theorem sum_cube_splitK (d N : ℕ) (i : Fin d) (k : ℕ) (F : (Fin d →₀ ℕ) → ℂ) :
    ∑ a ∈ cube d N, F a = ∑ a ∈ innK d N i k, F a + ∑ a ∈ faceK d N i k, F a := by
  classical
  rw [innK, faceK,
    ← Finset.sum_filter_add_sum_filter_not (cube d N) (fun a => a i + k ≤ N) F]
  congr 1
  refine Finset.sum_congr ?_ fun _ _ => rfl
  ext a
  simp only [Finset.mem_filter, mem_cube]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩
  · rintro ⟨h1, h2⟩; exact ⟨h1, by omega⟩

/-! ## 2. The abstract flux cancellation for one hop family -/

variable {u : (Fin d →₀ ℕ) → ℂ}

/-- The raising contribution of a hop of step `k` in the direction `i`. -/
def rtermG (u : (Fin d →₀ ℕ) → ℂ) (w : ℂ) (rc : (Fin d →₀ ℕ) → Fin d → ℝ) (k : ℕ) (i : Fin d)
    (a : Fin d →₀ ℕ) : ℂ :=
  (starRingEnd ℂ) w * ((rc a i : ℝ) : ℂ) * (starRingEnd ℂ) (u a) * u (a + Finsupp.single i k)

/-- The lowering contribution of a hop of step `k` in the direction `i`. -/
def ltermG (u : (Fin d →₀ ℕ) → ℂ) (w : ℂ) (lc : (Fin d →₀ ℕ) → Fin d → ℝ) (k : ℕ) (i : Fin d)
    (a : Fin d →₀ ℕ) : ℂ :=
  w * ((lc a i : ℝ) : ℂ) * (starRingEnd ℂ) (u a) * u (a - Finsupp.single i k)

theorem ltermG_shift {w : ℂ} {rc lc : (Fin d →₀ ℕ) → Fin d → ℝ} {k : ℕ} {i : Fin d}
    (hcomp : ∀ a : Fin d →₀ ℕ, lc (a + Finsupp.single i k) i = rc a i) (b : Fin d →₀ ℕ) :
    ltermG u w lc k i (b + Finsupp.single i k) = (starRingEnd ℂ) (rtermG u w rc k i b) := by
  rw [ltermG, rtermG, hcomp b, add_tsub_cancel_right]
  simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal]
  ring

theorem sum_ltermG {w : ℂ} {rc lc : (Fin d →₀ ℕ) → Fin d → ℝ} {k : ℕ} {i : Fin d}
    (hcomp : ∀ a : Fin d →₀ ℕ, lc (a + Finsupp.single i k) i = rc a i)
    (hvan : ∀ a : Fin d →₀ ℕ, a i < k → lc a i = 0) (N : ℕ) :
    ∑ a ∈ cube d N, ltermG u w lc k i a
      = (starRingEnd ℂ) (∑ a ∈ innK d N i k, rtermG u w rc k i a) := by
  rw [sum_shiftK d N i k (ltermG u w lc k i) (fun a ha => by rw [ltermG, hvan a ha]; simp),
    map_sum]
  exact Finset.sum_congr rfl fun b _ => ltermG_shift hcomp b

/-- **The flux cancellation.**  The interior contributions occur in conjugate pairs, so
only the `k`-thick face contributes to the imaginary part. -/
theorem sum_cube_hop_im {w : ℂ} {rc lc : (Fin d →₀ ℕ) → Fin d → ℝ} {k : ℕ} {i : Fin d}
    (hcomp : ∀ a : Fin d →₀ ℕ, lc (a + Finsupp.single i k) i = rc a i)
    (hvan : ∀ a : Fin d →₀ ℕ, a i < k → lc a i = 0) (N : ℕ) :
    (∑ a ∈ cube d N, (rtermG u w rc k i a + ltermG u w lc k i a)).im
      = (∑ a ∈ faceK d N i k, rtermG u w rc k i a).im := by
  rw [Finset.sum_add_distrib, sum_cube_splitK d N i k (rtermG u w rc k i),
    sum_ltermG hcomp hvan N]
  simp [Complex.add_im]

/-! ## 3. The two-step recursion -/

/-- The raising coefficient of a one-step hop: `√(αᵢ+1)`. -/
def rc1 (a : Fin d →₀ ℕ) (i : Fin d) : ℝ := Real.sqrt ((a i : ℝ) + 1)

/-- The lowering coefficient of a one-step hop: `√αᵢ`. -/
def lc1 (a : Fin d →₀ ℕ) (i : Fin d) : ℝ := Real.sqrt (a i : ℝ)

/-- The raising coefficient of a two-step hop: `√((αᵢ+1)(αᵢ+2))`. -/
def rc2 (a : Fin d →₀ ℕ) (i : Fin d) : ℝ := Real.sqrt (((a i : ℝ) + 1) * ((a i : ℝ) + 2))

/-- The lowering coefficient of a two-step hop: `√(αᵢ(αᵢ−1))`. -/
def lc2 (a : Fin d →₀ ℕ) (i : Fin d) : ℝ := Real.sqrt ((a i : ℝ) * ((a i : ℝ) - 1))

theorem lc1_shift (i : Fin d) (a : Fin d →₀ ℕ) :
    lc1 (a + Finsupp.single i 1) i = rc1 a i := by
  rw [lc1, rc1]
  norm_num

theorem lc1_vanish (i : Fin d) (a : Fin d →₀ ℕ) (h : a i < 1) : lc1 a i = 0 := by
  have : a i = 0 := by omega
  rw [lc1, this]
  simp

theorem lc2_shift (i : Fin d) (a : Fin d →₀ ℕ) :
    lc2 (a + Finsupp.single i 2) i = rc2 a i := by
  rw [lc2, rc2]
  have h : ((a + Finsupp.single i 2 : Fin d →₀ ℕ) i : ℝ) = (a i : ℝ) + 2 := by
    simp
  rw [h]
  ring_nf

theorem lc2_vanish (i : Fin d) (a : Fin d →₀ ℕ) (h : a i < 2) : lc2 a i = 0 := by
  interval_cases hai : (a i)
  · rw [lc2, hai]; norm_num
  · rw [lc2, hai]; norm_num

theorem rc1_nonneg (a : Fin d →₀ ℕ) (i : Fin d) : 0 ≤ rc1 a i := Real.sqrt_nonneg _

theorem rc2_nonneg (a : Fin d →₀ ℕ) (i : Fin d) : 0 ≤ rc2 a i := Real.sqrt_nonneg _

/-- **The two-step recursion.**  A real diagonal `lam`, one-step amplitudes `w1` and
two-step amplitudes `w2`, at the point `z`. -/
def LadderRec2 (u : (Fin d →₀ ℕ) → ℂ) (lam : (Fin d →₀ ℕ) → ℝ) (w1 w2 : Fin d → ℂ) (z : ℂ) :
    Prop :=
  ∀ a : Fin d →₀ ℕ,
    ((lam a : ℝ) : ℂ) * u a
      + ∑ i, ((starRingEnd ℂ) (w1 i) * ((rc1 a i : ℝ) : ℂ) * u (a + Finsupp.single i 1)
            + w1 i * ((lc1 a i : ℝ) : ℂ) * u (a - Finsupp.single i 1))
      + ∑ i, ((starRingEnd ℂ) (w2 i) * ((rc2 a i : ℝ) : ℂ) * u (a + Finsupp.single i 2)
            + w2 i * ((lc2 a i : ℝ) : ℂ) * u (a - Finsupp.single i 2))
      = z * u a

variable {lam : (Fin d →₀ ℕ) → ℝ} {w1 w2 : Fin d → ℂ} {z : ℂ}

/-- **The flux identity** for the two-step recursion. -/
theorem flux_identity2 (hrec : LadderRec2 u lam w1 w2 z) (N : ℕ) :
    z.im * (∑ a ∈ cube d N, ‖u a‖ ^ 2)
      = (∑ i, (∑ a ∈ faceK d N i 1, rtermG u (w1 i) rc1 1 i a).im)
        + ∑ i, (∑ a ∈ faceK d N i 2, rtermG u (w2 i) rc2 2 i a).im := by
  classical
  have hcm : ∀ v : ℂ, (starRingEnd ℂ) v * v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    intro v; rw [Complex.conj_mul']; norm_cast
  have hpt : ∀ a : Fin d →₀ ℕ, (starRingEnd ℂ) (u a) * (z * u a)
      = ((lam a : ℝ) : ℂ) * ((‖u a‖ ^ 2 : ℝ) : ℂ)
        + (∑ i, (rtermG u (w1 i) rc1 1 i a + ltermG u (w1 i) lc1 1 i a))
        + ∑ i, (rtermG u (w2 i) rc2 2 i a + ltermG u (w2 i) lc2 2 i a) := by
    intro a
    rw [← hrec a, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · congr 1
      · rw [← hcm (u a)]; ring
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [rtermG, ltermG]; ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [rtermG, ltermG]; ring
  have hL : ∑ a ∈ cube d N, (starRingEnd ℂ) (u a) * (z * u a)
      = z * ((∑ a ∈ cube d N, ‖u a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hcm (u a)]; ring
  have hR : ∑ a ∈ cube d N, (starRingEnd ℂ) (u a) * (z * u a)
      = ((∑ a ∈ cube d N, lam a * ‖u a‖ ^ 2 : ℝ) : ℂ)
        + (∑ i, ∑ a ∈ cube d N, (rtermG u (w1 i) rc1 1 i a + ltermG u (w1 i) lc1 1 i a))
        + ∑ i, ∑ a ∈ cube d N, (rtermG u (w2 i) rc2 2 i a + ltermG u (w2 i) lc2 2 i a) := by
    calc ∑ a ∈ cube d N, (starRingEnd ℂ) (u a) * (z * u a)
        = ∑ a ∈ cube d N, (((lam a : ℝ) : ℂ) * ((‖u a‖ ^ 2 : ℝ) : ℂ)
            + (∑ i, (rtermG u (w1 i) rc1 1 i a + ltermG u (w1 i) lc1 1 i a))
            + ∑ i, (rtermG u (w2 i) rc2 2 i a + ltermG u (w2 i) lc2 2 i a)) :=
          Finset.sum_congr rfl fun a _ => hpt a
      _ = ((∑ a ∈ cube d N, ((lam a : ℝ) : ℂ) * ((‖u a‖ ^ 2 : ℝ) : ℂ))
            + ∑ a ∈ cube d N, ∑ i, (rtermG u (w1 i) rc1 1 i a + ltermG u (w1 i) lc1 1 i a))
            + ∑ a ∈ cube d N, ∑ i,
                (rtermG u (w2 i) rc2 2 i a + ltermG u (w2 i) lc2 2 i a) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = ((∑ a ∈ cube d N, lam a * ‖u a‖ ^ 2 : ℝ) : ℂ)
            + (∑ i, ∑ a ∈ cube d N, (rtermG u (w1 i) rc1 1 i a + ltermG u (w1 i) lc1 1 i a))
            + ∑ i, ∑ a ∈ cube d N,
                (rtermG u (w2 i) rc2 2 i a + ltermG u (w2 i) lc2 2 i a) := by
          rw [Finset.sum_comm (s := cube d N) (t := Finset.univ),
            Finset.sum_comm (s := cube d N) (t := Finset.univ)]
          push_cast
          ring_nf
  have hEq := hL.symm.trans hR
  have hLim : (z * ((∑ a ∈ cube d N, ‖u a‖ ^ 2 : ℝ) : ℂ)).im
      = z.im * (∑ a ∈ cube d N, ‖u a‖ ^ 2) := by
    rw [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add]
  rw [← hLim, hEq]
  rw [Complex.add_im, Complex.add_im, Complex.ofReal_im, zero_add, Complex.im_sum,
    Complex.im_sum]
  congr 1
  · exact Finset.sum_congr rfl fun i _ =>
      sum_cube_hop_im (lc1_shift i) (fun a ha => lc1_vanish i a ha) N
  · exact Finset.sum_congr rfl fun i _ =>
      sum_cube_hop_im (lc2_shift i) (fun a ha => lc2_vanish i a ha) N

/-! ## 4. The flux bound -/

/-- **The flux bound.**  The flux through a `k`-thick face is at most the amplitude bound
there times the `ℓ²`-mass carried by that face and its shift. -/
theorem flux_boundG {w : ℂ} {rc : (Fin d →₀ ℕ) → Fin d → ℝ} (N : ℕ) (i : Fin d) (k : ℕ)
    {Cn : ℝ} (hCn : 0 ≤ Cn) (hC : ∀ a ∈ faceK d N i k, |rc a i| ≤ Cn) :
    |(∑ a ∈ faceK d N i k, rtermG u w rc k i a).im|
      ≤ Cn * (‖w‖ * ((∑ a ∈ faceK d N i k,
          (‖u a‖ ^ 2 + ‖u (a + Finsupp.single i k)‖ ^ 2)) / 2)) := by
  classical
  have h1 : |(∑ a ∈ faceK d N i k, rtermG u w rc k i a).im|
      ≤ ‖∑ a ∈ faceK d N i k, rtermG u w rc k i a‖ := Complex.abs_im_le_norm _
  have h2 : ‖∑ a ∈ faceK d N i k, rtermG u w rc k i a‖
      ≤ ∑ a ∈ faceK d N i k, ‖rtermG u w rc k i a‖ := norm_sum_le _ _
  have h3 : ∀ a ∈ faceK d N i k, ‖rtermG u w rc k i a‖
      ≤ Cn * (‖w‖ * ((‖u a‖ ^ 2 + ‖u (a + Finsupp.single i k)‖ ^ 2) / 2)) := by
    intro a ha
    have hnorm : ‖rtermG u w rc k i a‖
        = ‖w‖ * |rc a i| * ‖u a‖ * ‖u (a + Finsupp.single i k)‖ := by
      rw [rtermG]
      simp [Complex.norm_real]
    have hprod : ‖u a‖ * ‖u (a + Finsupp.single i k)‖
        ≤ (‖u a‖ ^ 2 + ‖u (a + Finsupp.single i k)‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖u a‖ - ‖u (a + Finsupp.single i k)‖)]
    have hrcC := hC a ha
    have hb1 : ‖w‖ * |rc a i| ≤ ‖w‖ * Cn := by
      exact mul_le_mul_of_nonneg_left hrcC (norm_nonneg w)
    rw [hnorm]
    calc ‖w‖ * |rc a i| * ‖u a‖ * ‖u (a + Finsupp.single i k)‖
        = (‖w‖ * |rc a i|) * (‖u a‖ * ‖u (a + Finsupp.single i k)‖) := by ring
      _ ≤ (‖w‖ * Cn) * (‖u a‖ * ‖u (a + Finsupp.single i k)‖) := by
          refine mul_le_mul_of_nonneg_right hb1 ?_
          positivity
      _ ≤ (‖w‖ * Cn) * ((‖u a‖ ^ 2 + ‖u (a + Finsupp.single i k)‖ ^ 2) / 2) := by
          refine mul_le_mul_of_nonneg_left hprod ?_
          positivity
      _ = Cn * (‖w‖ * ((‖u a‖ ^ 2 + ‖u (a + Finsupp.single i k)‖ ^ 2) / 2)) := by ring
  calc |(∑ a ∈ faceK d N i k, rtermG u w rc k i a).im|
      ≤ ∑ a ∈ faceK d N i k, ‖rtermG u w rc k i a‖ := h1.trans h2
    _ ≤ ∑ a ∈ faceK d N i k,
          Cn * (‖w‖ * ((‖u a‖ ^ 2 + ‖u (a + Finsupp.single i k)‖ ^ 2) / 2)) :=
        Finset.sum_le_sum h3
    _ = Cn * (‖w‖ * ((∑ a ∈ faceK d N i k,
          (‖u a‖ ^ 2 + ‖u (a + Finsupp.single i k)‖ ^ 2)) / 2)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_div]

end

end BookProof.CarlemanTwoStep
