import Mathlib
import BookProof.ChapterCarlemanTwoStep
import BookProof.ChapterCarlemanSimplex.Part2

/-!
# A Carleman criterion on simplex shells: hops which couple distinct modes

`BookProof.ChapterHermiteCarlemanEsa` and `BookProof.ChapterCarlemanTwoStep` run the
Carleman flux argument on **cubes** `{α : ∀ i, αᵢ ≤ N}`, for hops which move a *single*
excitation number: `α ↦ α ± eᵢ` and `α ↦ α ± 2eᵢ`.  That is exactly the ladder structure
of a quadratic Hamiltonian which does not couple distinct modes.

A general real quadratic Hamiltonian does couple them: `xᵢxⱼ`, `πᵢπⱼ` and `xᵢπⱼ` with
`i ≠ j` produce the hops `α ↦ α ± (eᵢ + eⱼ)` and `α ↦ α + eᵢ − eⱼ`.  On a cube the
bookkeeping of such hops is awkward — a hop leaves a cube through *two* faces at once,
and the mixed hop `α ↦ α + eᵢ − eⱼ` leaves it through one face while entering through
another.

This module reruns the argument on the **simplex shells** `{α : |α| ≤ N}`, where
`|α| = ∑ᵢ αᵢ` is the total degree.  The exhaustion is adapted to the grading by total
excitation number, and everything becomes uniform:

* a hop which *raises* the total degree by `k` (`α ↦ α + P` with `|P| = k`) leaks only
  through the shell `{N − k < |α| ≤ N}`, which meets at most `k` of the shells;
* a hop which *preserves* the total degree (`α ↦ α + eᵢ − eⱼ`) never leaves a shell, so
  it contributes **nothing at all** to the flux: the corresponding sum over a shell is
  real as soon as its amplitude matrix is Hermitian.

## What is proved

* `deg`, `simplexF`, `sInn`, `sBd` — the total degree, the simplex shells and their
  interiors and boundaries.
* `sum_simplex_hop_im` — **the abstract flux cancellation** for a hop `α ↦ α + P` of an
  arbitrary shift `P`: the interior contributions occur in conjugate pairs, so only the
  boundary shell contributes to the imaginary part.
* `sum_mterm_im` — **the degree-preserving hops carry no flux**: for a Hermitian
  amplitude matrix the total contribution of the hops `α ↦ α + eᵢ − eⱼ` over a shell is
  real.
* `LadderRecQ`, `flux_identityQ` — the recursion of a *general* quadratic ladder — one
  step, two steps, pair creation/annihilation and mode exchange — and its flux identity.
* `flux_bound_on`, `sBd_multiplicity`, `shifted_sBd_multiplicity` — the flux bound and
  the summability of the boundary mass (each index lies in at most `k` boundary shells).
* `ladderQ_eq_zero` — **the criterion.**  A square-summable family satisfying the general
  quadratic recursion, with a real diagonal, constant amplitudes and a Hermitian exchange
  matrix, at a point off the real axis, vanishes.  The Carleman divergence used is
  `∑ 1/(N+2) = ∞`.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.CarlemanSimplex

open Finset
open BookProof.HermiteCarleman BookProof.CarlemanTwoStep

noncomputable section

variable {d : ℕ}
variable {u : (Fin d →₀ ℕ) → ℂ}
variable {lam : (Fin d →₀ ℕ) → ℝ} {w : Fin d → ℂ} {W M : Fin d → Fin d → ℂ} {z : ℂ}
/-! ## 5. The flux bound and the boundary mass -/

/-- **The flux bound** on an arbitrary finite set of multi-indices. -/
theorem flux_bound_on {w : ℂ} {rc : (Fin d →₀ ℕ) → ℝ} (F : Finset (Fin d →₀ ℕ))
    (P : Fin d →₀ ℕ) {Cn : ℝ} (hC : ∀ a ∈ F, |rc a| ≤ Cn) :
    |(∑ a ∈ F, rtermP u w rc P a).im|
      ≤ Cn * (‖w‖ * ((∑ a ∈ F, (‖u a‖ ^ 2 + ‖u (a + P)‖ ^ 2)) / 2)) := by
  classical
  have h1 : |(∑ a ∈ F, rtermP u w rc P a).im| ≤ ‖∑ a ∈ F, rtermP u w rc P a‖ :=
    Complex.abs_im_le_norm _
  have h2 : ‖∑ a ∈ F, rtermP u w rc P a‖ ≤ ∑ a ∈ F, ‖rtermP u w rc P a‖ := norm_sum_le _ _
  have h3 : ∀ a ∈ F, ‖rtermP u w rc P a‖
      ≤ Cn * (‖w‖ * ((‖u a‖ ^ 2 + ‖u (a + P)‖ ^ 2) / 2)) := by
    intro a ha
    have hnorm : ‖rtermP u w rc P a‖ = ‖w‖ * |rc a| * ‖u a‖ * ‖u (a + P)‖ := by
      rw [rtermP]
      simp [Complex.norm_real]
    have hprod : ‖u a‖ * ‖u (a + P)‖ ≤ (‖u a‖ ^ 2 + ‖u (a + P)‖ ^ 2) / 2 := by
      nlinarith [sq_nonneg (‖u a‖ - ‖u (a + P)‖)]
    have hb1 : ‖w‖ * |rc a| ≤ ‖w‖ * Cn := mul_le_mul_of_nonneg_left (hC a ha) (norm_nonneg w)
    have hCn : 0 ≤ Cn := le_trans (abs_nonneg _) (hC a ha)
    rw [hnorm]
    calc ‖w‖ * |rc a| * ‖u a‖ * ‖u (a + P)‖
        = (‖w‖ * |rc a|) * (‖u a‖ * ‖u (a + P)‖) := by ring
      _ ≤ (‖w‖ * Cn) * (‖u a‖ * ‖u (a + P)‖) := by
          refine mul_le_mul_of_nonneg_right hb1 ?_
          positivity
      _ ≤ (‖w‖ * Cn) * ((‖u a‖ ^ 2 + ‖u (a + P)‖ ^ 2) / 2) := by
          refine mul_le_mul_of_nonneg_left hprod ?_
          positivity
      _ = Cn * (‖w‖ * ((‖u a‖ ^ 2 + ‖u (a + P)‖ ^ 2) / 2)) := by ring
  calc |(∑ a ∈ F, rtermP u w rc P a).im|
      ≤ ∑ a ∈ F, ‖rtermP u w rc P a‖ := h1.trans h2
    _ ≤ ∑ a ∈ F, Cn * (‖w‖ * ((‖u a‖ ^ 2 + ‖u (a + P)‖ ^ 2) / 2)) := Finset.sum_le_sum h3
    _ = Cn * (‖w‖ * ((∑ a ∈ F, (‖u a‖ ^ 2 + ‖u (a + P)‖ ^ 2)) / 2)) := by
        rw [← Finset.mul_sum, ← Finset.mul_sum, Finset.sum_div]

theorem sBd_multiplicity (k : ℕ) (a : Fin d →₀ ℕ) (M : ℕ) :
    (((Finset.range M).filter (fun N => a ∈ sBd d N k)).card) ≤ k := by
  classical
  have hsub : ((Finset.range M).filter (fun N => a ∈ sBd d N k))
      ⊆ Finset.Ico (deg a) (deg a + k) := by
    intro N hN
    simp only [Finset.mem_filter] at hN
    rw [mem_sBd] at hN
    exact Finset.mem_Ico.mpr ⟨hN.2.1, hN.2.2⟩
  calc (((Finset.range M).filter (fun N => a ∈ sBd d N k)).card)
      ≤ (Finset.Ico (deg a) (deg a + k)).card := Finset.card_le_card hsub
    _ = k := by rw [Nat.card_Ico]; omega

theorem shifted_sBd_multiplicity (P : Fin d →₀ ℕ) (b : Fin d →₀ ℕ) (M : ℕ) :
    (((Finset.range M).filter
      (fun N => b ∈ (sBd d N (deg P)).image (fun a => a + P))).card) ≤ deg P := by
  classical
  have hsub : ((Finset.range M).filter
        (fun N => b ∈ (sBd d N (deg P)).image (fun a => a + P)))
      ⊆ Finset.Ico (deg b - deg P) (deg b) := by
    intro N hN
    simp only [Finset.mem_filter, Finset.mem_image] at hN
    obtain ⟨a, ha, hab⟩ := hN.2
    rw [mem_sBd] at ha
    have hbd : deg b = deg a + deg P := by rw [← hab, deg_add]
    refine Finset.mem_Ico.mpr ⟨by omega, by omega⟩
  calc (((Finset.range M).filter
        (fun N => b ∈ (sBd d N (deg P)).image (fun a => a + P))).card)
      ≤ (Finset.Ico (deg b - deg P) (deg b)).card := Finset.card_le_card hsub
    _ ≤ deg P := by rw [Nat.card_Ico]; omega

theorem sBd_mass_le {B : ℝ}
    (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (k M : ℕ) :
    ∑ N ∈ Finset.range M, ∑ a ∈ sBd d N k, ‖u a‖ ^ 2 ≤ (k : ℝ) * B :=
  sum_range_of_multiplicity k hbes (fun N => sBd d N k) (sBd_multiplicity k) M

theorem shifted_sBd_mass_le {B : ℝ}
    (hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ B) (P : Fin d →₀ ℕ) (M : ℕ) :
    ∑ N ∈ Finset.range M, ∑ a ∈ sBd d N (deg P), ‖u (a + P)‖ ^ 2 ≤ ((deg P : ℕ) : ℝ) * B := by
  classical
  have hinj : ∀ N : ℕ, ∑ a ∈ sBd d N (deg P), ‖u (a + P)‖ ^ 2
      = ∑ b ∈ (sBd d N (deg P)).image (fun a => a + P), ‖u b‖ ^ 2 := by
    intro N
    rw [Finset.sum_image]
    intro x _ y _ hxy
    exact add_right_cancel hxy
  simp_rw [hinj]
  exact sum_range_of_multiplicity (deg P) hbes
    (fun N => (sBd d N (deg P)).image (fun a => a + P))
    (shifted_sBd_multiplicity P) M

/-- The Carleman divergence at growth rate `N`: `∑ 1/(N+2) = ∞`. -/
theorem not_summable_inv_natCast_add_two : ¬ Summable (fun N : ℕ => ((N : ℝ) + 2)⁻¹) := by
  intro h
  refine not_summable_inv_natCast_succ ?_
  refine (summable_nat_add_iff 1).mp ?_
  refine h.congr fun N => ?_
  push_cast
  ring_nf

end

end BookProof.CarlemanSimplex
