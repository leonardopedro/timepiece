import Mathlib
import BookProof.ChapterCarlemanTwoStep
import BookProof.ChapterCarlemanSimplex.Part1

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
/-! ## 4. The general quadratic recursion -/

/-- The shift of the pair hop `(i, j)`: `eᵢ + eⱼ`. -/
def pvec (i j : Fin d) : Fin d →₀ ℕ := Finsupp.single i 1 + Finsupp.single j 1

theorem deg_pvec (i j : Fin d) : deg (pvec (d := d) i j) = 2 := by
  rw [pvec, deg_add, deg_single, deg_single]

/-- The raising amplitude of the pair hop: `√((αᵢ+1)(αⱼ+1))` for `i ≠ j`, and
`√((αᵢ+1)(αᵢ+2))` for `i = j`. -/
def rcp (a : Fin d →₀ ℕ) (i j : Fin d) : ℝ :=
  Real.sqrt ((a j : ℝ) + 1) * Real.sqrt ((((a + Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℝ) + 1)

/-- The lowering amplitude of the pair hop: `√(αᵢαⱼ)` for `i ≠ j`, and `√(αᵢ(αᵢ−1))` for
`i = j`. -/
def lcp (a : Fin d →₀ ℕ) (i j : Fin d) : ℝ :=
  Real.sqrt ((a i : ℝ)) * Real.sqrt ((((a - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) : ℝ))

theorem rcp_nonneg (a : Fin d →₀ ℕ) (i j : Fin d) : 0 ≤ rcp a i j :=
  mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _)

theorem lcp_shift (i j : Fin d) (a : Fin d →₀ ℕ) :
    lcp (a + pvec i j) i j = rcp a i j := by
  classical
  by_cases hij : i = j
  · subst hij
    have h1 : ((a + pvec i i : Fin d →₀ ℕ) i : ℕ) = a i + 2 := by
      simp [pvec]
    have h2 : (((a + pvec i i) - Finsupp.single i 1 : Fin d →₀ ℕ) i : ℕ) = a i + 1 := by
      simp [pvec, Finsupp.tsub_apply]
    have h3 : (((a + Finsupp.single i 1 : Fin d →₀ ℕ)) i : ℕ) = a i + 1 := by simp
    rw [lcp, rcp, h1, h2, h3]
    push_cast
    ring_nf
  · have h1 : ((a + pvec i j : Fin d →₀ ℕ) i : ℕ) = a i + 1 := by
      simp [pvec, hij]
    have h2 : (((a + pvec i j) - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) = a j + 1 := by
      simp [pvec, Finsupp.tsub_apply, Ne.symm hij]
    have h3 : (((a + Finsupp.single j 1 : Fin d →₀ ℕ)) i : ℕ) = a i := by
      simp [Ne.symm hij]
    rw [lcp, rcp, h1, h2, h3]
    push_cast
    ring

theorem lcp_vanish (i j : Fin d) (a : Fin d →₀ ℕ) (h : ¬ pvec i j ≤ a) : lcp a i j = 0 := by
  classical
  rcases eq_or_ne i j with rfl | hij
  · have hle : ¬ (2 ≤ a i) := by
      intro h2
      refine h ?_
      rw [Finsupp.le_def]
      intro k
      by_cases hk : k = i
      · subst hk
        simpa [pvec] using h2
      · simp [pvec, Ne.symm hk]
    rcases Nat.lt_or_ge (a i) 1 with h0 | h1
    · have hai : a i = 0 := by omega
      rw [lcp, hai]
      simp
    · have hz : ((a - Finsupp.single i 1 : Fin d →₀ ℕ) i : ℕ) = 0 := by
        simp only [Finsupp.tsub_apply, Finsupp.single_eq_same]
        omega
      rw [lcp, hz]
      simp
  · have hor : a i = 0 ∨ a j = 0 := by
      by_contra hc
      push_neg at hc
      refine h ?_
      rw [Finsupp.le_def]
      intro k
      by_cases hki : k = i
      · subst hki
        have hp : (pvec k j : Fin d →₀ ℕ) k = 1 := by
          simp [pvec, hij]
        rw [hp]
        omega
      · by_cases hkj : k = j
        · subst hkj
          have hp : (pvec i k : Fin d →₀ ℕ) k = 1 := by
            simp [pvec, Ne.symm hki]
          rw [hp]
          omega
        · simp [pvec, Ne.symm hki, Ne.symm hkj]
    rcases hor with h0 | h0
    · rw [lcp, h0]
      simp
    · have hz : ((a - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) = 0 := by
        simp only [Finsupp.tsub_apply, Finsupp.single_apply, h0]
        omega
      rw [lcp, hz]
      simp

/-- **The general quadratic recursion**: a real diagonal `lam`, one-step amplitudes `w`,
pair creation/annihilation amplitudes `W`, and a mode-exchange matrix `M`. -/
def LadderRecQ (u : (Fin d →₀ ℕ) → ℂ) (lam : (Fin d →₀ ℕ) → ℝ) (w : Fin d → ℂ)
    (W M : Fin d → Fin d → ℂ) (z : ℂ) : Prop :=
  ∀ a : Fin d →₀ ℕ,
    ((lam a : ℝ) : ℂ) * u a
      + ∑ i, ((starRingEnd ℂ) (w i) * ((rc1 a i : ℝ) : ℂ) * u (a + Finsupp.single i 1)
            + w i * ((lc1 a i : ℝ) : ℂ) * u (a - Finsupp.single i 1))
      + ∑ i, ∑ j, ((starRingEnd ℂ) (W i j) * ((rcp a i j : ℝ) : ℂ) * u (a + pvec i j)
            + W i j * ((lcp a i j : ℝ) : ℂ) * u (a - pvec i j))
      + ∑ i, ∑ j, (M i j * ((rcm a i j : ℝ) : ℂ) * u (shiftm a i j))
      = z * u a

variable {lam : (Fin d →₀ ℕ) → ℝ} {w : Fin d → ℂ} {W M : Fin d → Fin d → ℂ} {z : ℂ}

theorem lc1_vanish' (i : Fin d) (a : Fin d →₀ ℕ) (h : ¬ Finsupp.single i 1 ≤ a) :
    lc1 a i = 0 := by
  classical
  refine lc1_vanish i a ?_
  by_contra hge
  refine h ?_
  rw [Finsupp.le_def]
  intro k
  by_cases hk : k = i
  · subst hk
    simpa using (by omega : 1 ≤ a k)
  · simp [Ne.symm hk]

/-- **The flux identity** for the general quadratic recursion. -/
theorem flux_identityQ (hM : ∀ i j, M j i = (starRingEnd ℂ) (M i j))
    (hrec : LadderRecQ u lam w W M z) (N : ℕ) :
    z.im * (∑ a ∈ simplexF d N, ‖u a‖ ^ 2)
      = (∑ i, (∑ a ∈ sBd d N 1, rtermP u (w i) (fun b => rc1 b i) (Finsupp.single i 1) a).im)
        + ∑ i, ∑ j,
            (∑ a ∈ sBd d N 2, rtermP u (W i j) (fun b => rcp b i j) (pvec i j) a).im := by
  classical
  have hcm : ∀ v : ℂ, (starRingEnd ℂ) v * v = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    intro v; rw [Complex.conj_mul']; norm_cast
  have hpt : ∀ a : Fin d →₀ ℕ, (starRingEnd ℂ) (u a) * (z * u a)
      = ((lam a : ℝ) : ℂ) * ((‖u a‖ ^ 2 : ℝ) : ℂ)
        + (∑ i, (rtermP u (w i) (fun b => rc1 b i) (Finsupp.single i 1) a
                  + ltermP u (w i) (fun b => lc1 b i) (Finsupp.single i 1) a))
        + (∑ i, ∑ j, (rtermP u (W i j) (fun b => rcp b i j) (pvec i j) a
                  + ltermP u (W i j) (fun b => lcp b i j) (pvec i j) a))
        + ∑ i, ∑ j, mterm u M a i j := by
    intro a
    rw [← hrec a, mul_add, mul_add, mul_add, Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]
    congr 1
    · congr 1
      · congr 1
        · rw [← hcm (u a)]; ring
        · refine Finset.sum_congr rfl fun i _ => ?_
          rw [rtermP, ltermP]; ring
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [rtermP, ltermP]; ring
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [mterm]; ring
  have hL : ∑ a ∈ simplexF d N, (starRingEnd ℂ) (u a) * (z * u a)
      = z * ((∑ a ∈ simplexF d N, ‖u a‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← hcm (u a)]; ring
  have hR : ∑ a ∈ simplexF d N, (starRingEnd ℂ) (u a) * (z * u a)
      = ((∑ a ∈ simplexF d N, lam a * ‖u a‖ ^ 2 : ℝ) : ℂ)
        + (∑ i, ∑ a ∈ simplexF d N, (rtermP u (w i) (fun b => rc1 b i) (Finsupp.single i 1) a
                  + ltermP u (w i) (fun b => lc1 b i) (Finsupp.single i 1) a))
        + (∑ i, ∑ j, ∑ a ∈ simplexF d N, (rtermP u (W i j) (fun b => rcp b i j) (pvec i j) a
                  + ltermP u (W i j) (fun b => lcp b i j) (pvec i j) a))
        + ∑ i, ∑ j, ∑ a ∈ simplexF d N, mterm u M a i j := by
    calc ∑ a ∈ simplexF d N, (starRingEnd ℂ) (u a) * (z * u a)
        = ∑ a ∈ simplexF d N, (((lam a : ℝ) : ℂ) * ((‖u a‖ ^ 2 : ℝ) : ℂ)
            + (∑ i, (rtermP u (w i) (fun b => rc1 b i) (Finsupp.single i 1) a
                  + ltermP u (w i) (fun b => lc1 b i) (Finsupp.single i 1) a))
            + (∑ i, ∑ j, (rtermP u (W i j) (fun b => rcp b i j) (pvec i j) a
                  + ltermP u (W i j) (fun b => lcp b i j) (pvec i j) a))
            + ∑ i, ∑ j, mterm u M a i j) :=
          Finset.sum_congr rfl fun a _ => hpt a
      _ = ((∑ a ∈ simplexF d N, ((lam a : ℝ) : ℂ) * ((‖u a‖ ^ 2 : ℝ) : ℂ))
            + ∑ a ∈ simplexF d N, ∑ i,
                (rtermP u (w i) (fun b => rc1 b i) (Finsupp.single i 1) a
                  + ltermP u (w i) (fun b => lc1 b i) (Finsupp.single i 1) a)
            + ∑ a ∈ simplexF d N, ∑ i, ∑ j,
                (rtermP u (W i j) (fun b => rcp b i j) (pvec i j) a
                  + ltermP u (W i j) (fun b => lcp b i j) (pvec i j) a))
            + ∑ a ∈ simplexF d N, ∑ i, ∑ j, mterm u M a i j := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, Finset.sum_add_distrib]
      _ = ((∑ a ∈ simplexF d N, lam a * ‖u a‖ ^ 2 : ℝ) : ℂ)
            + (∑ i, ∑ a ∈ simplexF d N,
                (rtermP u (w i) (fun b => rc1 b i) (Finsupp.single i 1) a
                  + ltermP u (w i) (fun b => lc1 b i) (Finsupp.single i 1) a))
            + (∑ i, ∑ j, ∑ a ∈ simplexF d N,
                (rtermP u (W i j) (fun b => rcp b i j) (pvec i j) a
                  + ltermP u (W i j) (fun b => lcp b i j) (pvec i j) a))
            + ∑ i, ∑ j, ∑ a ∈ simplexF d N, mterm u M a i j := by
          rw [Finset.sum_comm (s := simplexF d N) (t := Finset.univ)]
          rw [Finset.sum_comm (s := simplexF d N) (t := Finset.univ)
            (f := fun a i => ∑ j, (rtermP u (W i j) (fun b => rcp b i j) (pvec i j) a
                  + ltermP u (W i j) (fun b => lcp b i j) (pvec i j) a))]
          rw [Finset.sum_comm (s := simplexF d N) (t := Finset.univ)
            (f := fun a i => ∑ j, mterm u M a i j)]
          have e1 : ∀ i : Fin d, ∑ a ∈ simplexF d N, ∑ j,
              (rtermP u (W i j) (fun b => rcp b i j) (pvec i j) a
                + ltermP u (W i j) (fun b => lcp b i j) (pvec i j) a)
              = ∑ j, ∑ a ∈ simplexF d N,
                  (rtermP u (W i j) (fun b => rcp b i j) (pvec i j) a
                    + ltermP u (W i j) (fun b => lcp b i j) (pvec i j) a) := fun i =>
            Finset.sum_comm
          have e2 : ∀ i : Fin d, ∑ a ∈ simplexF d N, ∑ j, mterm u M a i j
              = ∑ j, ∑ a ∈ simplexF d N, mterm u M a i j := fun i => Finset.sum_comm
          rw [Finset.sum_congr rfl fun i _ => e1 i, Finset.sum_congr rfl fun i _ => e2 i]
          push_cast
          ring_nf
  have hEq := hL.symm.trans hR
  have hLim : (z * ((∑ a ∈ simplexF d N, ‖u a‖ ^ 2 : ℝ) : ℂ)).im
      = z.im * (∑ a ∈ simplexF d N, ‖u a‖ ^ 2) := by
    rw [Complex.mul_im, Complex.ofReal_im, Complex.ofReal_re, mul_zero, zero_add]
  rw [← hLim, hEq]
  rw [Complex.add_im, Complex.add_im, Complex.add_im, Complex.ofReal_im, zero_add,
    sum_mterm_im hM N, add_zero, Complex.im_sum, Complex.im_sum]
  congr 1
  · refine Finset.sum_congr rfl fun i _ => ?_
    have h := sum_simplex_hop_im (u := u) (w := w i) (rc := fun b => rc1 b i)
      (lc := fun b => lc1 b i) (P := Finsupp.single i 1)
      (fun a => lc1_shift i a) (fun a ha => lc1_vanish' i a ha) N
    rwa [deg_single] at h
  · refine Finset.sum_congr rfl fun i _ => ?_
    rw [Complex.im_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    have h := sum_simplex_hop_im (u := u) (w := W i j) (rc := fun b => rcp b i j)
      (lc := fun b => lcp b i j) (P := pvec i j)
      (fun a => lcp_shift i j a) (fun a ha => lcp_vanish i j a ha) N
    rwa [deg_pvec] at h

end

end BookProof.CarlemanSimplex
