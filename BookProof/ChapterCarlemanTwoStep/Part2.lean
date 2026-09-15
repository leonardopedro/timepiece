import Mathlib
import BookProof.ChapterHermiteCarlemanEsa
import BookProof.ChapterCarlemanTwoStep.Part1

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

variable {u : (Fin d →₀ ℕ) → ℂ}
variable {lam : (Fin d →₀ ℕ) → ℝ} {w1 w2 : Fin d → ℂ} {z : ℂ}
/-! ## 5. Bessel's inequality with multiplicity -/

/-- If every multi-index lies in at most `m` of the sets `G N`, the total mass they carry
is at most `m` times the total mass. -/
theorem sum_range_of_multiplicity {B : ℝ} (m : ℕ)
    (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B)
    (G : ℕ → Finset (Fin d →₀ ℕ))
    (hm : ∀ (a : Fin d →₀ ℕ) (M : ℕ),
      (((Finset.range M).filter (fun N => a ∈ G N)).card) ≤ m)
    (M : ℕ) : ∑ N ∈ Finset.range M, ∑ a ∈ G N, ‖u a‖ ^ 2 ≤ (m : ℝ) * B := by
  classical
  set T : Finset (Fin d →₀ ℕ) := (Finset.range M).biUnion G with hT
  have hsub : ∀ N ∈ Finset.range M, G N ⊆ T := by
    intro N hN a ha
    exact Finset.mem_biUnion.mpr ⟨N, hN, ha⟩
  have hstep1 : ∀ N ∈ Finset.range M,
      ∑ a ∈ G N, ‖u a‖ ^ 2 = ∑ a ∈ T, if a ∈ G N then ‖u a‖ ^ 2 else 0 := by
    intro N hN
    rw [← Finset.sum_filter]
    refine (Finset.sum_congr ?_ fun _ _ => rfl).symm
    ext a
    simp only [Finset.mem_filter]
    exact ⟨fun h => h.2, fun h => ⟨hsub N hN h, h⟩⟩
  have hstep2 : ∀ a : Fin d →₀ ℕ,
      ∑ N ∈ Finset.range M, (if a ∈ G N then ‖u a‖ ^ 2 else 0)
        = (((Finset.range M).filter (fun N => a ∈ G N)).card : ℝ) * ‖u a‖ ^ 2 := by
    intro a
    rw [← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]
  calc ∑ N ∈ Finset.range M, ∑ a ∈ G N, ‖u a‖ ^ 2
      = ∑ N ∈ Finset.range M, ∑ a ∈ T, (if a ∈ G N then ‖u a‖ ^ 2 else 0) :=
        Finset.sum_congr rfl hstep1
    _ = ∑ a ∈ T, ∑ N ∈ Finset.range M, (if a ∈ G N then ‖u a‖ ^ 2 else 0) := Finset.sum_comm
    _ = ∑ a ∈ T, (((Finset.range M).filter (fun N => a ∈ G N)).card : ℝ) * ‖u a‖ ^ 2 :=
        Finset.sum_congr rfl fun a _ => hstep2 a
    _ ≤ ∑ a ∈ T, (m : ℝ) * ‖u a‖ ^ 2 := by
        refine Finset.sum_le_sum fun a _ => ?_
        refine mul_le_mul_of_nonneg_right ?_ (by positivity)
        exact_mod_cast hm a M
    _ = (m : ℝ) * ∑ a ∈ T, ‖u a‖ ^ 2 := by rw [Finset.mul_sum]
    _ ≤ (m : ℝ) * B := by
        refine mul_le_mul_of_nonneg_left (hbes T) (by positivity)

theorem faceK_multiplicity (i : Fin d) (k : ℕ) (a : Fin d →₀ ℕ) (M : ℕ) :
    (((Finset.range M).filter (fun N => a ∈ faceK d N i k)).card) ≤ k := by
  classical
  have hsub : ((Finset.range M).filter (fun N => a ∈ faceK d N i k))
      ⊆ Finset.Ico (a i) (a i + k) := by
    intro N hN
    simp only [Finset.mem_filter] at hN
    rw [mem_faceK] at hN
    exact Finset.mem_Ico.mpr ⟨hN.2.1 i, hN.2.2⟩
  calc (((Finset.range M).filter (fun N => a ∈ faceK d N i k)).card)
      ≤ (Finset.Ico (a i) (a i + k)).card := Finset.card_le_card hsub
    _ = k := by rw [Nat.card_Ico]; omega

theorem shiftedK_multiplicity (i : Fin d) (k : ℕ) (b : Fin d →₀ ℕ) (M : ℕ) :
    (((Finset.range M).filter
      (fun N => b ∈ (faceK d N i k).image (fun a => a + Finsupp.single i k))).card) ≤ k := by
  classical
  have hsub : ((Finset.range M).filter
        (fun N => b ∈ (faceK d N i k).image (fun a => a + Finsupp.single i k)))
      ⊆ Finset.Ico (b i - k) (b i) := by
    intro N hN
    simp only [Finset.mem_filter, Finset.mem_image] at hN
    obtain ⟨a, ha, hab⟩ := hN.2
    rw [mem_faceK] at ha
    have hbi : b i = a i + k := by
      rw [← hab]; simp
    refine Finset.mem_Ico.mpr ⟨?_, ?_⟩
    · have := ha.1 i; omega
    · have := ha.2; omega
  calc (((Finset.range M).filter
        (fun N => b ∈ (faceK d N i k).image (fun a => a + Finsupp.single i k))).card)
      ≤ (Finset.Ico (b i - k) (b i)).card := Finset.card_le_card hsub
    _ ≤ k := by rw [Nat.card_Ico]; omega

theorem facesK_le {B : ℝ}
    (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (i : Fin d) (k M : ℕ) :
    ∑ N ∈ Finset.range M, ∑ a ∈ faceK d N i k, ‖u a‖ ^ 2 ≤ (k : ℝ) * B :=
  sum_range_of_multiplicity k hbes (fun N => faceK d N i k) (faceK_multiplicity i k) M

theorem shifted_facesK_le {B : ℝ}
    (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (i : Fin d) (k M : ℕ) :
    ∑ N ∈ Finset.range M, ∑ a ∈ faceK d N i k, ‖u (a + Finsupp.single i k)‖ ^ 2
      ≤ (k : ℝ) * B := by
  classical
  have hinj : ∀ N : ℕ, ∑ a ∈ faceK d N i k, ‖u (a + Finsupp.single i k)‖ ^ 2
      = ∑ b ∈ (faceK d N i k).image (fun a => a + Finsupp.single i k), ‖u b‖ ^ 2 := by
    intro N
    rw [Finset.sum_image]
    intro x _ y _ hxy
    exact add_right_cancel hxy
  simp_rw [hinj]
  exact sum_range_of_multiplicity k hbes
    (fun N => (faceK d N i k).image (fun a => a + Finsupp.single i k))
    (shiftedK_multiplicity i k) M

/-- The Carleman divergence at growth rate `N`: `∑ 1/(N+1) = ∞`. -/
theorem not_summable_inv_natCast_succ : ¬ Summable (fun N : ℕ => ((N : ℝ) + 1)⁻¹) := by
  intro h
  refine Real.not_summable_one_div_natCast ?_
  refine (summable_nat_add_iff 1).mp ?_
  refine h.congr fun N => ?_
  push_cast
  rw [one_div]

/-! ## 6. The criterion -/

/-- **The two-step Carleman criterion.**  A square-summable family satisfying the
two-step recursion, with a real diagonal and constant amplitudes, at a point off the real
axis, vanishes identically. -/
theorem ladder2_eq_zero {B : ℝ} (hz : z.im ≠ 0)
    (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B)
    (hrec : LadderRec2 u lam w1 w2 z) : ∀ a, u a = 0 := by
  classical
  by_contra hcon
  push_neg at hcon
  obtain ⟨a₀, ha₀⟩ := hcon
  -- the boundary mass functional
  set mass : ℕ → Fin d → ℕ → ℝ := fun N i k =>
    (∑ a ∈ faceK d N i k, (‖u a‖ ^ 2 + ‖u (a + Finsupp.single i k)‖ ^ 2)) / 2 with hmass
  set A : ℕ → ℝ := fun N =>
    (∑ i, ‖w1 i‖ * mass N i 1) + ∑ i, ‖w2 i‖ * mass N i 2 with hAdef
  have hmass_nonneg : ∀ N i k, 0 ≤ mass N i k := by
    intro N i k
    have hs : 0 ≤ ∑ a ∈ faceK d N i k, (‖u a‖ ^ 2 + ‖u (a + Finsupp.single i k)‖ ^ 2) :=
      Finset.sum_nonneg fun a _ => by positivity
    rw [hmass]
    positivity
  have hAnn : ∀ N, 0 ≤ A N := by
    intro N
    have h1 : 0 ≤ ∑ i, ‖w1 i‖ * mass N i 1 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (hmass_nonneg N i 1)
    have h2 : 0 ≤ ∑ i, ‖w2 i‖ * mass N i 2 :=
      Finset.sum_nonneg fun i _ => mul_nonneg (norm_nonneg _) (hmass_nonneg N i 2)
    rw [hAdef]
    linarith
  -- the total boundary mass is finite
  have hmass_sum : ∀ (i : Fin d) (k M : ℕ),
      ∑ N ∈ Finset.range M, mass N i k ≤ (k : ℝ) * B := by
    intro i k M
    have h1 := facesK_le hbes i k M
    have h2 := shifted_facesK_le hbes i k M
    have hpt : ∀ N : ℕ, mass N i k
        = ((∑ a ∈ faceK d N i k, ‖u a‖ ^ 2)
            + ∑ a ∈ faceK d N i k, ‖u (a + Finsupp.single i k)‖ ^ 2) / 2 := by
      intro N; simp only [hmass]; rw [Finset.sum_add_distrib]
    simp_rw [hpt]
    rw [← Finset.sum_div, Finset.sum_add_distrib]
    linarith
  have hApart : ∀ M, ∑ N ∈ Finset.range M, A N
      ≤ ((∑ i, ‖w1 i‖) * (1 * B)) + (∑ i, ‖w2 i‖) * (2 * B) := by
    intro M
    have hsplit : ∑ N ∈ Finset.range M, A N
        = (∑ N ∈ Finset.range M, ∑ i, ‖w1 i‖ * mass N i 1)
          + ∑ N ∈ Finset.range M, ∑ i, ‖w2 i‖ * mass N i 2 := by
      rw [hAdef, ← Finset.sum_add_distrib]
    have hb : ∀ (k : ℕ) (W : Fin d → ℂ),
        ∑ N ∈ Finset.range M, ∑ i, ‖W i‖ * mass N i k
          ≤ (∑ i, ‖W i‖) * ((k : ℝ) * B) := by
      intro k W
      rw [Finset.sum_comm, Finset.sum_mul]
      refine Finset.sum_le_sum fun i _ => ?_
      calc ∑ N ∈ Finset.range M, ‖W i‖ * mass N i k
          = ‖W i‖ * ∑ N ∈ Finset.range M, mass N i k := by rw [Finset.mul_sum]
        _ ≤ ‖W i‖ * ((k : ℝ) * B) :=
            mul_le_mul_of_nonneg_left (hmass_sum i k M) (norm_nonneg _)
    have h1 := hb 1 w1
    have h2 := hb 2 w2
    rw [hsplit]
    push_cast at h1 h2
    linarith
  have hsummable : Summable A := summable_of_sum_range_le hAnn hApart
  -- the flux bound, with the uniform amplitude bound `2(N+1)`
  have hCn : ∀ N : ℕ, (0 : ℝ) ≤ 2 * ((N : ℝ) + 1) := by intro N; positivity
  have hC1 : ∀ (N : ℕ) (i : Fin d), ∀ a ∈ faceK d N i 1, |rc1 a i| ≤ 2 * ((N : ℝ) + 1) := by
    intro N i a ha
    rw [mem_faceK] at ha
    have hai : ((a i : ℝ)) ≤ (N : ℝ) := by exact_mod_cast ha.1 i
    have h1 : rc1 a i ≤ (N : ℝ) + 1 := by
      rw [rc1]
      have : Real.sqrt ((a i : ℝ) + 1) ≤ Real.sqrt (((N : ℝ) + 1) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        nlinarith [Nat.cast_nonneg (α := ℝ) N]
      rwa [Real.sqrt_sq (by positivity)] at this
    rw [abs_of_nonneg (rc1_nonneg a i)]
    linarith
  have hC2 : ∀ (N : ℕ) (i : Fin d), ∀ a ∈ faceK d N i 2, |rc2 a i| ≤ 2 * ((N : ℝ) + 1) := by
    intro N i a ha
    rw [mem_faceK] at ha
    have hai : ((a i : ℝ)) ≤ (N : ℝ) := by exact_mod_cast ha.1 i
    have h1 : rc2 a i ≤ (N : ℝ) + 2 := by
      rw [rc2]
      have : Real.sqrt (((a i : ℝ) + 1) * ((a i : ℝ) + 2)) ≤ Real.sqrt (((N : ℝ) + 2) ^ 2) := by
        refine Real.sqrt_le_sqrt ?_
        nlinarith [Nat.cast_nonneg (α := ℝ) (a i)]
      rwa [Real.sqrt_sq (by positivity)] at this
    rw [abs_of_nonneg (rc2_nonneg a i)]
    have : (0 : ℝ) ≤ (N : ℝ) := Nat.cast_nonneg N
    linarith
  have hkey : ∀ N : ℕ,
      |z.im| * (∑ a ∈ cube d N, ‖u a‖ ^ 2) ≤ (2 * ((N : ℝ) + 1)) * A N := by
    intro N
    have hS : 0 ≤ ∑ a ∈ cube d N, ‖u a‖ ^ 2 := Finset.sum_nonneg fun a _ => by positivity
    have h1 : |z.im| * (∑ a ∈ cube d N, ‖u a‖ ^ 2)
        = |(∑ i, (∑ a ∈ faceK d N i 1, rtermG u (w1 i) rc1 1 i a).im)
            + ∑ i, (∑ a ∈ faceK d N i 2, rtermG u (w2 i) rc2 2 i a).im| := by
      rw [← flux_identity2 hrec N, abs_mul, abs_of_nonneg hS]
    rw [h1]
    have hb1 : |∑ i, (∑ a ∈ faceK d N i 1, rtermG u (w1 i) rc1 1 i a).im|
        ≤ (2 * ((N : ℝ) + 1)) * ∑ i, ‖w1 i‖ * mass N i 1 := by
      calc |∑ i, (∑ a ∈ faceK d N i 1, rtermG u (w1 i) rc1 1 i a).im|
          ≤ ∑ i, |(∑ a ∈ faceK d N i 1, rtermG u (w1 i) rc1 1 i a).im| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, (2 * ((N : ℝ) + 1)) * (‖w1 i‖ * mass N i 1) :=
            Finset.sum_le_sum fun i _ => flux_boundG N i 1 (hCn N) (hC1 N i)
        _ = (2 * ((N : ℝ) + 1)) * ∑ i, ‖w1 i‖ * mass N i 1 := by rw [Finset.mul_sum]
    have hb2 : |∑ i, (∑ a ∈ faceK d N i 2, rtermG u (w2 i) rc2 2 i a).im|
        ≤ (2 * ((N : ℝ) + 1)) * ∑ i, ‖w2 i‖ * mass N i 2 := by
      calc |∑ i, (∑ a ∈ faceK d N i 2, rtermG u (w2 i) rc2 2 i a).im|
          ≤ ∑ i, |(∑ a ∈ faceK d N i 2, rtermG u (w2 i) rc2 2 i a).im| :=
            Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, (2 * ((N : ℝ) + 1)) * (‖w2 i‖ * mass N i 2) :=
            Finset.sum_le_sum fun i _ => flux_boundG N i 2 (hCn N) (hC2 N i)
        _ = (2 * ((N : ℝ) + 1)) * ∑ i, ‖w2 i‖ * mass N i 2 := by rw [Finset.mul_sum]
    have habs := abs_add_le (∑ i, (∑ a ∈ faceK d N i 1, rtermG u (w1 i) rc1 1 i a).im)
      (∑ i, (∑ a ∈ faceK d N i 2, rtermG u (w2 i) rc2 2 i a).im)
    rw [hAdef]
    simp only
    rw [mul_add]
    linarith
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
    have h2 : 0 < ‖u a₀‖ ^ 2 := by
      have : 0 < ‖u a₀‖ := norm_pos_iff.mpr ha₀
      positivity
    positivity
  have hAlow : ∀ N : ℕ, N₀ ≤ N →
      ((|z.im| * ‖u a₀‖ ^ 2) / 2) * ((N : ℝ) + 1)⁻¹ ≤ A N := by
    intro N hN
    have hpos : (0 : ℝ) < 2 * ((N : ℝ) + 1) := by positivity
    have h1 := hkey N
    have h2 := hlow N hN
    have h3 : |z.im| * ‖u a₀‖ ^ 2 ≤ (2 * ((N : ℝ) + 1)) * A N := by
      have := mul_le_mul_of_nonneg_left h2 (abs_nonneg z.im)
      linarith
    have h5 : ((|z.im| * ‖u a₀‖ ^ 2) / 2) * ((N : ℝ) + 1)⁻¹
        = (|z.im| * ‖u a₀‖ ^ 2) / (2 * ((N : ℝ) + 1)) := by
      field_simp
    rw [h5, div_le_iff₀ hpos]
    linarith [h3, mul_comm (2 * ((N : ℝ) + 1)) (A N)]
  have hshift : Summable (fun N : ℕ => A (N + N₀)) := (summable_nat_add_iff N₀).mpr hsummable
  have hcomp : Summable (fun N : ℕ =>
      ((|z.im| * ‖u a₀‖ ^ 2) / 2) * (((N + N₀ : ℕ) : ℝ) + 1)⁻¹) := by
    refine Summable.of_nonneg_of_le (fun N => by positivity) (fun N => ?_) hshift
    exact hAlow (N + N₀) (Nat.le_add_left _ _)
  have h4 : Summable (fun N : ℕ => (((N + N₀ : ℕ) : ℝ) + 1)⁻¹) := by
    have h5 := hcomp.mul_left ((|z.im| * ‖u a₀‖ ^ 2) / 2)⁻¹
    refine h5.congr fun N => ?_
    field_simp
  exact not_summable_inv_natCast_succ ((summable_nat_add_iff N₀).mp h4)

end

end BookProof.CarlemanTwoStep
