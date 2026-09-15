import Mathlib
import BookProof.ChapterCarlemanSimplex
import BookProof.ChapterModeQuadraticEsa
import BookProof.ChapterFullQuadraticEsa.Part1

/-!
# The general real quadratic Hamiltonian on the Gauss–polynomial core

`BookProof.ChapterModeQuadraticEsa` proves essential self-adjointness, on the plain
Gauss–polynomial (product Hermite) core of `L²(ℝᵈ)`, of the general **mode-diagonal**
quadratic Hamiltonian

`∑ᵢ (pᵢπᵢ² + qᵢxᵢ² + sᵢ·½(xᵢπᵢ + πᵢxᵢ)) + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)`

for arbitrary real `p, q, s, b, b'`.  What that leaves open is the coupling of **distinct**
modes: `xᵢxⱼ`, `πᵢπⱼ` and `xᵢπⱼ` with `i ≠ j`.

This module removes that restriction.  For arbitrary real matrices `P, Q, S` and arbitrary
real vectors `b, b'` the Weyl-ordered operator

`H = ∑_{i,j} (Pᵢⱼ πᵢπⱼ + Qᵢⱼ xᵢxⱼ + Sᵢⱼ·½(xᵢπⱼ + πⱼxᵢ)) + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)`

— i.e. *every* real quadratic-plus-linear Hamiltonian in `d` degrees of freedom, with no
ellipticity, no definiteness, no non-degeneracy and no classical equilibrium — is
essentially self-adjoint on the plain Gauss–polynomial core, and hence generates a
complete unitary flow.

## The mechanism

In the ladder variables `xᵢ = aᵢ† + aᵢ`, `πᵢ = (i/2)(aᵢ† − aᵢ)` a product of two of them
is a sum of four hops of the multi-index `α`:

* `α ↦ α + eᵢ + eⱼ` (pair creation), amplitude `√((αᵢ+1)(αⱼ+1))`;
* `α ↦ α − eᵢ − eⱼ` (pair annihilation), amplitude `√(αᵢαⱼ)`;
* `α ↦ α + eᵢ − eⱼ` (mode exchange), amplitude `√(αⱼ(αᵢ+1))`;

plus, when `i = j`, a constant diagonal.  The first two change the total degree `|α|` by
`±2`, the third preserves it.  `BookProof.ChapterCarlemanSimplex` runs the Carleman flux
argument on the simplex shells `{|α| ≤ N}`, which is exactly adapted to this grading: the
mode-exchange hops carry no flux at all (their contribution over a shell is real, because
their amplitude matrix is Hermitian), and the degree-changing hops leak only through a
two-thick boundary shell.

## What is proved

* `lop_lop_hermiteMv_gen`, `weyl_hermiteMv_gen` — the two-index ladder algebra, uniform in
  `i` and `j` (the diagonal `i = j` differs only by an extra constant).
* `fqQuadPoly`, `fqPoly`, `fqOp` — the Hamiltonian, assembled from Weyl-ordered products
  of the canonical pair, hence symmetric on the core (`fqOp_symmetric`).
* `fqQuadPoly_hermiteMv`, `fqOp_hermiteCore` — its ladder form: a real constant diagonal,
  the pair amplitude `Qᵢⱼ − Pᵢⱼ/4 + i Sᵢⱼ/2`, the Hermitian exchange matrix
  `fqExch`, and the one-step amplitude `bᵢ + i b'ᵢ/2` of the first-order part.
* `fqOp_deficiencyTrivialAt`, `fqOp_essentiallySelfAdjoint` — **the headline**, by the
  simplex Carleman criterion `BookProof.CarlemanSimplex.ladderQ_eq_zero`.
* `fqOp_stone_flow` — the resulting complete unitary flow, by Stone's theorem.
* `crossTerm_essentiallySelfAdjoint`, `crossTerm_stone_flow` — the corollary for the
  purely off-diagonal cross term `½(xᵢπⱼ + πⱼxᵢ) + ½(xⱼπᵢ + πᵢxⱼ)`.
* `rotMat`, `fqQuadPoly_rotMat`, `angularMomentum_essentiallySelfAdjoint`,
  `angularMomentum_stone_flow` — an *antisymmetric* exchange matrix realizes the
  angular-momentum generator `xₖπ_l − x_lπₖ`, the compact counterpart of the dilation
  generator; it too is essentially self-adjoint on the core, with a complete flow.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.FullQuadratic

open Finset MeasureTheory MvPolynomial
open BookProof.HermiteProductCore BookProof.HermiteProductBasis
open BookProof.FarisLavine
open BookProof.HyperbolicQuadratic
open BookProof.NavierStokesFlow.DifferentialL2
open BookProof.HermiteRelative
open BookProof.QuadratureEsa
open BookProof.CarlemanTwoStep
open BookProof.CarlemanSimplex
open BookProof.ModeQuadratic
open BookProof.StoneBridge BookProof.EsaClosure BookProof.ChapterStoneResolvent

noncomputable section

variable {d : ℕ}
/-! ### Transport to the orthonormal basis -/

theorem hermiteMvNorm_add_pvec (i j : Fin d) (a : Fin d →₀ ℕ) :
    hermiteMvNorm (a + pvec i j) = hermiteMvNorm a * rcp a i j := by
  rw [← add_pvec_eq, hermiteMvNorm_add_single i (a + Finsupp.single j 1),
    hermiteMvNorm_add_single j a, rcp]
  ring

theorem ascendP_Lp (i j : Fin d) (a : Fin d →₀ ℕ) :
    ((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • pgLp (hermiteMv (a + pvec i j))
      = ((rcp a i j : ℝ) : ℂ) • hermiteMvLp (a + pvec i j) := by
  rw [pgLp_hermiteMv_eq, smul_smul, hermiteMvNorm_add_pvec]
  congr 1
  have hne : ((hermiteMvNorm a : ℝ) : ℂ) ≠ 0 := hermiteMvNorm_ne_zero a
  push_cast
  field_simp

/-- The exchange hop, transported to the orthonormal basis. -/
theorem exchange_Lp (i j : Fin d) (a : Fin d →₀ ℕ) (c : ℂ) :
    ((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • ((c * (a j : ℂ)) • pgLp (hermiteMv (shiftm a i j)))
      = (c * ((rcm a i j : ℝ) : ℂ)) • hermiteMvLp (shiftm a i j) := by
  rcases Nat.eq_zero_or_pos (a j) with h0 | hpos
  · have hrcm : rcm a i j = 0 := rcm_of_zero h0
    rw [hrcm, h0]
    simp
  · have hle : 1 ≤ a j := hpos
    have hnorm : hermiteMvNorm a
        = hermiteMvNorm (a - Finsupp.single j 1) * Real.sqrt ((a j : ℝ)) :=
      hermiteMvNorm_sub_single hle
    have hshift : hermiteMvNorm (shiftm a i j)
        = hermiteMvNorm (a - Finsupp.single j 1)
            * Real.sqrt ((((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℝ) + 1) := by
      rw [shiftm, hermiteMvNorm_add_single]
    have hsj : Real.sqrt ((a j : ℝ)) * Real.sqrt ((a j : ℝ)) = (a j : ℝ) :=
      Real.mul_self_sqrt (by positivity)
    have hsjne : ((Real.sqrt ((a j : ℝ)) : ℝ) : ℂ) ≠ 0 := by
      simp only [ne_eq, Complex.ofReal_eq_zero]
      have : (0 : ℝ) < Real.sqrt ((a j : ℝ)) := Real.sqrt_pos.mpr (by exact_mod_cast hpos)
      linarith
    have hbne : ((hermiteMvNorm (a - Finsupp.single j 1) : ℝ) : ℂ) ≠ 0 :=
      hermiteMvNorm_ne_zero _
    rw [pgLp_hermiteMv_eq, smul_smul, smul_smul, hshift, rcm, hnorm]
    congr 1
    push_cast
    field_simp
    rw [show ((a j : ℂ)) = ((Real.sqrt ((a j : ℝ)) : ℝ) : ℂ) * ((Real.sqrt ((a j : ℝ)) : ℝ) : ℂ)
      by rw [← Complex.ofReal_mul, hsj]; simp]
    ring

/-- The pair-annihilation hop, transported to the orthonormal basis. -/
theorem descendP_Lp (i j : Fin d) (a : Fin d →₀ ℕ) (c : ℂ) :
    ((hermiteMvNorm a : ℝ) : ℂ)⁻¹ •
        ((c * (a j : ℂ) * (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℂ))
          • pgLp (hermiteMv (a - pvec i j)))
      = (c * ((lcp a i j : ℝ) : ℂ)) • hermiteMvLp (a - pvec i j) := by
  have hco : c * (a j : ℂ) * (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℂ)
      = c * (a i : ℂ) * (((a - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) : ℂ) := by
    rw [mul_assoc, mul_assoc, swap_prodC]
  rw [hco]
  rcases Nat.eq_zero_or_pos (a i) with h0 | hposi
  · have hlcp : lcp a i j = 0 := by rw [lcp, h0]; simp
    rw [hlcp, h0]
    simp
  · rcases Nat.eq_zero_or_pos ((a - Finsupp.single i 1 : Fin d →₀ ℕ) j) with h0 | hposj
    · have hlcp : lcp a i j = 0 := by rw [lcp, h0]; simp
      rw [hlcp, h0]
      simp
    · have hn1 : hermiteMvNorm a
          = hermiteMvNorm (a - Finsupp.single i 1) * Real.sqrt ((a i : ℝ)) :=
        hermiteMvNorm_sub_single hposi
      have hn2 : hermiteMvNorm (a - Finsupp.single i 1)
          = hermiteMvNorm (a - Finsupp.single i 1 - Finsupp.single j 1)
              * Real.sqrt ((((a - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) : ℝ)) :=
        hermiteMvNorm_sub_single hposj
      have hsub : a - Finsupp.single i 1 - Finsupp.single j 1 = a - pvec i j := by
        rw [sub_pvec_eq a j i, pvec_comm]
      have hsi : Real.sqrt ((a i : ℝ)) * Real.sqrt ((a i : ℝ)) = (a i : ℝ) :=
        Real.mul_self_sqrt (by positivity)
      have hsj : Real.sqrt ((((a - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) : ℝ))
            * Real.sqrt ((((a - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) : ℝ))
          = (((a - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) : ℝ) :=
        Real.mul_self_sqrt (by positivity)
      have hsine : ((Real.sqrt ((a i : ℝ)) : ℝ) : ℂ) ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        have : (0 : ℝ) < Real.sqrt ((a i : ℝ)) := Real.sqrt_pos.mpr (by exact_mod_cast hposi)
        linarith
      have hsjne : ((Real.sqrt ((((a - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) : ℝ)) : ℝ) : ℂ)
          ≠ 0 := by
        simp only [ne_eq, Complex.ofReal_eq_zero]
        have : (0 : ℝ) < Real.sqrt ((((a - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) : ℝ)) :=
          Real.sqrt_pos.mpr (by exact_mod_cast hposj)
        linarith
      have hbne : ((hermiteMvNorm (a - pvec i j) : ℝ) : ℂ) ≠ 0 := hermiteMvNorm_ne_zero _
      rw [hsub] at hn2
      rw [pgLp_hermiteMv_eq, smul_smul, smul_smul, lcp, hn1, hn2]
      congr 1
      set m : ℕ := a i with hm
      set n : ℕ := ((a - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) with hn
      have hc1 : ((m : ℂ)) = ((Real.sqrt ((m : ℝ)) : ℝ) : ℂ) * ((Real.sqrt ((m : ℝ)) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, hsi]
        simp
      have hc2 : ((n : ℂ)) = ((Real.sqrt ((n : ℝ)) : ℝ) : ℂ) * ((Real.sqrt ((n : ℝ)) : ℝ) : ℂ) := by
        rw [← Complex.ofReal_mul, hsj]
        simp
      push_cast
      field_simp
      rw [hc1, hc2]
      ring

set_option maxHeartbeats 1600000 in
-- the core coercions make the elaboration of this transport expensive
/-- **The ladder form of the Hamiltonian on the product Hermite basis.** -/
theorem fqOp_hermiteCore (P Q S : Fin d → Fin d → ℝ) (b b' : Fin d → ℝ) (a : Fin d →₀ ℕ) :
    fqOp P Q S b b' (hermiteCore a)
      = ((fqSymbol P Q : ℝ) : ℂ) • hermiteMvLp a
        + (∑ i, ∑ j, ((fqAmp P Q S i j * ((rcp a i j : ℝ) : ℂ))
                    • hermiteMvLp (a + pvec i j)
                + ((starRingEnd ℂ) (fqAmp P Q S i j) * ((lcp a i j : ℝ) : ℂ))
                    • hermiteMvLp (a - pvec i j)
                + (fqExch P Q S i j * ((rcm a i j : ℝ) : ℂ))
                    • hermiteMvLp (shiftm a i j)))
        + ∑ i, ((foAmp b b' i * ((Real.sqrt ((a i : ℝ) + 1) : ℝ) : ℂ))
                  • hermiteMvLp (a + Finsupp.single i 1)
                + ((starRingEnd ℂ) (foAmp b b' i) * ((Real.sqrt ((a i : ℝ)) : ℝ) : ℂ))
                  • hermiteMvLp (a - Finsupp.single i 1)) := by
  have hcoe : (fqOp P Q S b b' (hermiteCore a) : L2d d)
      = ((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • pgMap (fqPoly P Q S b b' (hermiteMv a)) := by
    have h := coreOp_coe (fqPoly P Q S b b') (((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • hermiteMv a)
    rw [← HermiteProductBasis.pgMap_apply, map_smul (fqPoly P Q S b b'),
      map_smul (pgMap (d := d))] at h
    exact h
  rw [hcoe, fqPoly, LinearMap.add_apply, fqQuadPoly_hermiteMv, map_add, map_add, map_sum,
    smul_add, smul_add, Finset.smul_sum]
  congr 1
  · congr 1
    · rw [map_smul, smul_comm, HermiteProductBasis.pgMap_apply, pgLp_hermiteMv_eq, smul_smul,
        smul_smul, mul_assoc, inv_mul_cancel₀ (hermiteMvNorm_ne_zero a), mul_one]
    · refine Finset.sum_congr rfl fun i _ => ?_
      rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [map_add, map_add, smul_add, smul_add, map_smul, map_smul, map_smul]
      congr 1
      · congr 1
        · rw [smul_comm, HermiteProductBasis.pgMap_apply, ascendP_Lp, smul_smul]
        · rw [HermiteProductBasis.pgMap_apply]
          exact descendP_Lp i j a ((starRingEnd ℂ) (fqAmp P Q S i j))
      · rw [HermiteProductBasis.pgMap_apply]
        exact exchange_Lp i j a (fqExch P Q S i j)
  · have hfo : ((foOp b b' (hermiteCore a) : L2d d))
        = ((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • pgMap (foPoly b b' (hermiteMv a)) := by
      have h := coreOp_coe (foPoly b b') (((hermiteMvNorm a : ℝ) : ℂ)⁻¹ • hermiteMv a)
      rw [← HermiteProductBasis.pgMap_apply, map_smul (foPoly b b'),
        map_smul (pgMap (d := d))] at h
      exact h
    rw [← hfo, foOp_hermiteCore]

/-! ## 4. Essential self-adjointness -/

set_option maxHeartbeats 1600000 in
-- the core coercions make the elaboration of the deficiency computation expensive
/-- **The deficiency spaces vanish at every non-real point.** -/
theorem fqOp_deficiencyTrivialAt (P Q S : Fin d → Fin d → ℝ) (b b' : Fin d → ℝ)
    {z : ℂ} (hz : z.im ≠ 0) :
    DeficiencyTrivialAt (polyGaussCore (d := d)) (fqOp P Q S b b') z := by
  classical
  intro w hw
  set u : (Fin d →₀ ℕ) → ℂ := fun a => (inner ℂ (hermiteMvLp (d := d) a) w : ℂ) with hu
  have hbes : ∀ F : Finset (Fin d →₀ ℕ), ∑ a ∈ F, ‖u a‖ ^ 2 ≤ ‖w‖ ^ 2 := fun F =>
    Orthonormal.sum_inner_products_le (𝕜 := ℂ) w (orthonormal_hermiteMvLp (d := d))
  have hM : ∀ i j : Fin d, (fun i j => (starRingEnd ℂ) (fqExch P Q S i j)) j i
      = (starRingEnd ℂ) ((fun i j => (starRingEnd ℂ) (fqExch P Q S i j)) i j) := by
    intro i j
    simp only [Complex.conj_conj]
    exact fqExch_hermitian P Q S j i
  have hrec : LadderRecQ u (fun _ => fqSymbol P Q) (foAmp b b') (fqAmp P Q S)
      (fun i j => (starRingEnd ℂ) (fqExch P Q S i j)) z := by
    intro a
    have h := hw (hermiteCore a)
    rw [fqOp_hermiteCore P Q S b b' a, inner_add_left, inner_add_left, inner_smul_left,
      Complex.conj_ofReal, sum_inner, sum_inner] at h
    rw [hermiteCore_coe] at h
    have hq : ∀ i : Fin d,
        (inner ℂ (∑ j, ((fqAmp P Q S i j * ((rcp a i j : ℝ) : ℂ))
                    • hermiteMvLp (d := d) (a + pvec i j)
                + ((starRingEnd ℂ) (fqAmp P Q S i j) * ((lcp a i j : ℝ) : ℂ))
                    • hermiteMvLp (d := d) (a - pvec i j)
                + (fqExch P Q S i j * ((rcm a i j : ℝ) : ℂ))
                    • hermiteMvLp (d := d) (shiftm a i j))) w : ℂ)
        = ∑ j, ((starRingEnd ℂ) (fqAmp P Q S i j) * ((rcp a i j : ℝ) : ℂ)
              * u (a + pvec i j)
            + fqAmp P Q S i j * ((lcp a i j : ℝ) : ℂ) * u (a - pvec i j)
            + (starRingEnd ℂ) (fqExch P Q S i j) * ((rcm a i j : ℝ) : ℂ)
              * u (shiftm a i j)) := by
      intro i
      rw [sum_inner]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [inner_add_left, inner_add_left, inner_smul_left, inner_smul_left, inner_smul_left]
      simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal, hu]
    have hf : ∀ i : Fin d,
        (inner ℂ (((foAmp b b' i * ((Real.sqrt ((a i : ℝ) + 1) : ℝ) : ℂ))
              • hermiteMvLp (d := d) (a + Finsupp.single i 1)
            + ((starRingEnd ℂ) (foAmp b b' i) * ((Real.sqrt ((a i : ℝ)) : ℝ) : ℂ))
              • hermiteMvLp (d := d) (a - Finsupp.single i 1))) w : ℂ)
        = (starRingEnd ℂ) (foAmp b b' i) * ((rc1 a i : ℝ) : ℂ) * u (a + Finsupp.single i 1)
          + foAmp b b' i * ((lc1 a i : ℝ) : ℂ) * u (a - Finsupp.single i 1) := by
      intro i
      rw [inner_add_left, inner_smul_left, inner_smul_left]
      simp only [map_mul, Complex.conj_conj, Complex.conj_ofReal, hu, rc1, lc1]
    rw [Finset.sum_congr rfl (fun i _ => hq i), Finset.sum_congr rfl (fun i _ => hf i)] at h
    have hsplit : ∀ i : Fin d,
        ∑ j, ((starRingEnd ℂ) (fqAmp P Q S i j) * ((rcp a i j : ℝ) : ℂ) * u (a + pvec i j)
            + fqAmp P Q S i j * ((lcp a i j : ℝ) : ℂ) * u (a - pvec i j)
            + (starRingEnd ℂ) (fqExch P Q S i j) * ((rcm a i j : ℝ) : ℂ) * u (shiftm a i j))
        = ∑ j, ((starRingEnd ℂ) (fqAmp P Q S i j) * ((rcp a i j : ℝ) : ℂ) * u (a + pvec i j)
              + fqAmp P Q S i j * ((lcp a i j : ℝ) : ℂ) * u (a - pvec i j))
          + ∑ j, ((starRingEnd ℂ) (fqExch P Q S i j) * ((rcm a i j : ℝ) : ℂ)
              * u (shiftm a i j)) := by
      intro i
      rw [← Finset.sum_add_distrib]
    rw [Finset.sum_congr rfl (fun i _ => hsplit i), Finset.sum_add_distrib] at h
    linear_combination h
  have hzero : ∀ a, u a = 0 := ladderQ_eq_zero hz hbes hM hrec
  exact hermiteMvLp_total w fun a => hzero a

/-- **HEADLINE.**  For *arbitrary* real matrices `P, Q, S` and *arbitrary* real vectors
`b, b'`, the general real quadratic Hamiltonian

`H = ∑_{i,j} (Pᵢⱼπᵢπⱼ + Qᵢⱼxᵢxⱼ + Sᵢⱼ·½(xᵢπⱼ + πⱼxᵢ)) + ∑ᵢ (bᵢxᵢ + b'ᵢπᵢ)`

is essentially self-adjoint on the Gauss–polynomial (product Hermite) core of `L²(ℝᵈ)`.
Distinct modes may be coupled arbitrarily; there is no ellipticity, no sign condition, no
non-degeneracy, no classical equilibrium and no change of core. -/
theorem fqOp_essentiallySelfAdjoint (P Q S : Fin d → Fin d → ℝ) (b b' : Fin d → ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (fqOp P Q S b b') :=
  ⟨fqOp_deficiencyTrivialAt P Q S b b' (by simp),
    fqOp_deficiencyTrivialAt P Q S b b' (by simp)⟩

/-- **The complete unitary flow** generated by the closure of the Hamiltonian. -/
theorem fqOp_stone_flow (P Q S : Fin d → Fin d → ℝ) (b b' : Fin d → ℝ) :
    ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)),
      IsSelfAdjointExtension (fqOp P Q S b b') T.op ∧ IsStoneFlow T U :=
  exists_stone_flow_of_esa _ polyGaussCore_dense (fqOp_symmetric P Q S b b')
    (fqOp_essentiallySelfAdjoint P Q S b b')

/-- **The purely off-diagonal cross term.**  For `i ≠ j` the Weyl-ordered mixed generator
`½(xᵢπⱼ + πⱼxᵢ) + ½(xⱼπᵢ + πᵢxⱼ)` — the quadratic Hamiltonian which couples two distinct
modes and nothing else — is essentially self-adjoint on the plain Gauss–polynomial
core. -/
theorem crossTerm_essentiallySelfAdjoint (S : Fin d → Fin d → ℝ) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (fqOp 0 0 S 0 0) :=
  fqOp_essentiallySelfAdjoint 0 0 S 0 0

/-- The unitary flow generated by a purely off-diagonal cross term. -/
theorem crossTerm_stone_flow (S : Fin d → Fin d → ℝ) :
    ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)),
      IsSelfAdjointExtension (fqOp (d := d) 0 0 S 0 0) T.op ∧ IsStoneFlow T U :=
  fqOp_stone_flow 0 0 S 0 0

/-! ## 5. The angular-momentum generators

An **antisymmetric** exchange matrix `S` picks out the rotation generators: since `xᵢ`
and `πⱼ` commute for `i ≠ j` and the diagonal of `S` vanishes,
`∑_{i,j} Sᵢⱼ·½(xᵢπⱼ + πⱼxᵢ) = ∑_{i<j} Sᵢⱼ (xᵢπⱼ − xⱼπᵢ)`.  The elementary antisymmetric
matrix therefore realizes the angular-momentum generator `xₖπ_l − x_lπₖ`, the compact
counterpart of the dilation generator of `BookProof.ModeQuadratic`. -/

/-- The elementary antisymmetric matrix `E_{kl} − E_{lk}`. -/
def rotMat (k l : Fin d) : Fin d → Fin d → ℝ := fun i j =>
  (if i = k then (if j = l then (1 : ℝ) else 0) else 0)
    - (if i = l then (if j = k then (1 : ℝ) else 0) else 0)

/-- With the elementary antisymmetric exchange matrix the quadratic part is exactly the
**angular-momentum generator** `xₖπ_l − x_lπₖ` (Weyl-ordered). -/
theorem fqQuadPoly_rotMat (k l : Fin d) :
    fqQuadPoly (d := d) 0 0 (rotMat k l)
      = BookProof.YangMillsHermite.weylProd (mulXPoly k) (momPoly l)
        - BookProof.YangMillsHermite.weylProd (mulXPoly l) (momPoly k) := by
  classical
  simp only [fqQuadPoly, Pi.zero_apply, Complex.ofReal_zero, zero_smul, zero_add, rotMat,
    Complex.ofReal_sub, sub_smul, Finset.sum_sub_distrib]
  simp

/-- **The angular-momentum generator is essentially self-adjoint** on the plain
Gauss–polynomial core, for every pair of coordinate directions. -/
theorem angularMomentum_essentiallySelfAdjoint (k l : Fin d) :
    EssentiallySelfAdjointOn (polyGaussCore (d := d)) (fqOp 0 0 (rotMat k l) 0 0) :=
  fqOp_essentiallySelfAdjoint 0 0 (rotMat k l) 0 0

/-- The complete unitary rotation flow generated by an angular-momentum generator. -/
theorem angularMomentum_stone_flow (k l : Fin d) :
    ∃ (T : UnboundedSelfAdjoint (L2d d)) (U : ℝ → (L2d d →L[ℂ] L2d d)),
      IsSelfAdjointExtension (fqOp (d := d) 0 0 (rotMat k l) 0 0) T.op ∧ IsStoneFlow T U :=
  fqOp_stone_flow 0 0 (rotMat k l) 0 0

end

end BookProof.FullQuadratic
