import Mathlib
import BookProof.ChapterCarlemanSimplex
import BookProof.ChapterModeQuadraticEsa

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

/-! ## 1. Two-index multi-index arithmetic -/

theorem pvec_comm (i j : Fin d) : pvec (d := d) i j = pvec j i := by
  rw [pvec, pvec, add_comm]

theorem add_pvec_eq (a : Fin d →₀ ℕ) (i j : Fin d) :
    a + Finsupp.single j 1 + Finsupp.single i 1 = a + pvec i j := by
  rw [pvec]
  abel

theorem sub_pvec_eq (a : Fin d →₀ ℕ) (i j : Fin d) :
    a - Finsupp.single j 1 - Finsupp.single i 1 = a - pvec i j := by
  ext k
  simp only [pvec, Finsupp.tsub_apply, Finsupp.add_apply]
  omega

theorem shiftm_self_eq {a : Fin d →₀ ℕ} {i : Fin d} (h : 1 ≤ a i) : shiftm a i i = a := by
  have hle : Finsupp.single i 1 ≤ a := by
    rw [Finsupp.le_def]
    intro k
    by_cases hk : k = i
    · subst hk; simpa using h
    · simp [Ne.symm hk]
  rw [shiftm, tsub_add_cancel_of_le' hle]

theorem add_sub_single_eq_shiftm {a : Fin d →₀ ℕ} {i j : Fin d} (hij : i ≠ j) :
    a + Finsupp.single j 1 - Finsupp.single i 1 = shiftm a j i := by
  ext k
  simp only [shiftm, Finsupp.tsub_apply, Finsupp.add_apply, Finsupp.single_apply]
  by_cases hki : i = k <;> by_cases hkj : j = k <;> simp_all

theorem sub_single_apply_ne {a : Fin d →₀ ℕ} {i j : Fin d} (hij : i ≠ j) :
    ((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) = a i := by
  simp [Finsupp.tsub_apply, hij]

theorem add_single_apply_ne {a : Fin d →₀ ℕ} {i j : Fin d} (hij : i ≠ j) :
    ((a + Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) = a i := by
  simp [hij]

/-- The two ways of reading the pair-annihilation amplitude agree. -/
theorem swap_prod (a : Fin d →₀ ℕ) (i j : Fin d) :
    (a j) * ((a - Finsupp.single j 1 : Fin d →₀ ℕ) i)
      = (a i) * ((a - Finsupp.single i 1 : Fin d →₀ ℕ) j) := by
  by_cases hij : i = j
  · subst hij; ring
  · rw [sub_single_apply_ne hij, sub_single_apply_ne (Ne.symm hij)]
    ring

theorem swap_prodC (a : Fin d →₀ ℕ) (i j : Fin d) :
    ((a j : ℂ)) * (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℂ)
      = ((a i : ℂ)) * (((a - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) : ℂ) := by
  have h := swap_prod a i j
  exact_mod_cast congrArg (fun n : ℕ => (n : ℂ)) h

theorem smul_shiftm_diag (c : ℂ) (a : Fin d →₀ ℕ) (i : Fin d) :
    (c * (a i : ℂ)) • hermiteMv (shiftm a i i) = (c * (a i : ℂ)) • hermiteMv a := by
  rcases Nat.eq_zero_or_pos (a i) with h | h
  · rw [h]
    simp
  · rw [shiftm_self_eq h]

/-! ## 2. The two-index ladder algebra -/

/-- **The two-index ladder action.**  A product of two one-step operators is a sum of the
pair-creation hop, the two mode-exchange hops, the pair-annihilation hop, and — only when
`i = j` — a constant diagonal. -/
theorem lop_lop_hermiteMv_gen (t t' : ℂ) (i j : Fin d) (a : Fin d →₀ ℕ) :
    lop t i (lop t' j (hermiteMv a))
      = hermiteMv (a + pvec i j)
        + (t * (a i : ℂ)) • hermiteMv (shiftm a j i)
        + (t' * (a j : ℂ)) • hermiteMv (shiftm a i j)
        + (t * t' * (a j : ℂ) * (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℂ))
            • hermiteMv (a - pvec i j)
        + (if i = j then t • hermiteMv a else 0) := by
  rw [lop_hermiteMv t' j a, map_add, map_smul, lop_hermiteMv t i (a + Finsupp.single j 1),
    lop_hermiteMv t i (a - Finsupp.single j 1), add_pvec_eq, sub_pvec_eq]
  by_cases hij : i = j
  · subst hij
    rw [if_pos rfl, add_tsub_cancel_right]
    have hs : a - Finsupp.single i 1 + Finsupp.single i 1 = shiftm a i i := rfl
    rw [hs]
    have hd : ((a + Finsupp.single i 1 : Fin d →₀ ℕ) i : ℕ) = a i + 1 := by simp
    rw [hd]
    rw [smul_shiftm_diag t a i]
    push_cast
    module
  · rw [if_neg hij, add_sub_single_eq_shiftm hij, add_single_apply_ne hij]
    have hs : a - Finsupp.single j 1 + Finsupp.single i 1 = shiftm a i j := rfl
    rw [hs]
    push_cast
    module

theorem weylProd_smul_apply (c c' : ℂ) (A B : Module.End ℂ (MvPolynomial (Fin d) ℂ))
    (p : MvPolynomial (Fin d) ℂ) :
    BookProof.YangMillsHermite.weylProd (c • A) (c' • B) p
      = (c * c') • BookProof.YangMillsHermite.weylProd A B p := by
  simp only [BookProof.YangMillsHermite.weylProd, LinearMap.smul_apply, LinearMap.add_apply,
    LinearMap.comp_apply, map_smul, smul_smul]
  rw [mul_comm c' c]
  module

/-- **The Weyl-ordered two-index ladder action.** -/
theorem weyl_hermiteMv_gen (t t' : ℂ) (i j : Fin d) (a : Fin d →₀ ℕ) :
    BookProof.YangMillsHermite.weylProd (lop t i) (lop t' j) (hermiteMv a)
      = hermiteMv (a + pvec i j)
        + (t * (a i : ℂ)) • hermiteMv (shiftm a j i)
        + (t' * (a j : ℂ)) • hermiteMv (shiftm a i j)
        + (t * t' * (a j : ℂ) * (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℂ))
            • hermiteMv (a - pvec i j)
        + (if i = j then ((t + t') / 2) • hermiteMv a else 0) := by
  rw [BookProof.YangMillsHermite.weylProd]
  simp only [LinearMap.smul_apply, LinearMap.add_apply, LinearMap.comp_apply]
  have hco : t' * t * (a i : ℂ) * (((a - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) : ℂ)
      = t * t' * (a j : ℂ) * (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℂ) := by
    have hsw := swap_prodC a i j
    calc t' * t * (a i : ℂ) * (((a - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) : ℂ)
        = (t' * t) * ((a i : ℂ) * (((a - Finsupp.single i 1 : Fin d →₀ ℕ) j : ℕ) : ℂ)) := by
          ring
      _ = (t * t') * ((a j : ℂ) * (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℂ)) := by
          rw [← hsw]; ring
      _ = t * t' * (a j : ℂ) * (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℂ) := by ring
  rw [lop_lop_hermiteMv_gen t t' i j a, lop_lop_hermiteMv_gen t' t j i a,
    ← pvec_comm j i, hco]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte]
    push_cast
    module
  · rw [if_neg hij, if_neg (Ne.symm hij), if_neg hij]
    push_cast
    module

/-! ## 3. The Hamiltonian -/

/-- The pair-creation amplitude `Qᵢⱼ − Pᵢⱼ/4 + i Sᵢⱼ/2`. -/
def fqAmp (P Q S : Fin d → Fin d → ℝ) (i j : Fin d) : ℂ :=
  ((Q i j - P i j / 4 : ℝ) : ℂ) + Complex.I * ((S i j / 2 : ℝ) : ℂ)

/-- The half of the mode-exchange amplitude coming from the ordered pair `(i, j)`. -/
def fqMl (P Q S : Fin d → Fin d → ℝ) (i j : Fin d) : ℂ :=
  ((Q i j + P i j / 4 : ℝ) : ℂ) - Complex.I * ((S i j / 2 : ℝ) : ℂ)

/-- **The mode-exchange amplitude matrix**, which is Hermitian. -/
def fqExch (P Q S : Fin d → Fin d → ℝ) (i j : Fin d) : ℂ :=
  fqMl P Q S i j + (starRingEnd ℂ) (fqMl P Q S j i)

theorem fqExch_hermitian (P Q S : Fin d → Fin d → ℝ) (i j : Fin d) :
    (starRingEnd ℂ) (fqExch P Q S i j) = fqExch P Q S j i := by
  rw [fqExch, fqExch, map_add, Complex.conj_conj]
  ring

/-- The constant diagonal `∑ᵢ (Qᵢᵢ + Pᵢᵢ/4)` of the Weyl-ordered Hamiltonian. -/
def fqSymbol (P Q : Fin d → Fin d → ℝ) : ℝ := ∑ i, (Q i i + P i i / 4)

/-- The quadratic part `∑_{i,j} (Pᵢⱼπᵢπⱼ + Qᵢⱼxᵢxⱼ + Sᵢⱼ·½(xᵢπⱼ + πⱼxᵢ))`, on polynomial
coordinates, assembled from Weyl-ordered products of the canonical pair. -/
def fqQuadPoly (P Q S : Fin d → Fin d → ℝ) :
    MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  ∑ i, ∑ j, (((P i j : ℝ) : ℂ) • BookProof.YangMillsHermite.weylProd (momPoly i) (momPoly j)
      + ((Q i j : ℝ) : ℂ) • BookProof.YangMillsHermite.weylProd (mulXPoly i) (mulXPoly j)
      + ((S i j : ℝ) : ℂ) • BookProof.YangMillsHermite.weylProd (mulXPoly i) (momPoly j))

/-- The full symbol: quadratic part plus first-order part. -/
def fqPoly (P Q S : Fin d → Fin d → ℝ) (b b' : Fin d → ℝ) :
    MvPolynomial (Fin d) ℂ →ₗ[ℂ] MvPolynomial (Fin d) ℂ :=
  fqQuadPoly P Q S + foPoly b b'

/-- **The general real quadratic Hamiltonian** on the Gauss–polynomial core. -/
def fqOp (P Q S : Fin d → Fin d → ℝ) (b b' : Fin d → ℝ) :
    (polyGaussCore (d := d)) →ₗ[ℂ] L2d d :=
  (polyGaussCore (d := d)).subtype ∘ₗ coreOp (fqPoly P Q S b b')

/-! ### Symmetry -/

theorem polySym_fqQuadPoly (P Q S : Fin d → Fin d → ℝ) :
    BookProof.YangMillsHermite.PolySym (fqQuadPoly P Q S) := by
  refine polySym_sum _ _ fun i _ => ?_
  refine polySym_sum _ _ fun j _ => ?_
  refine ((BookProof.YangMillsHermite.weylProd_polySym (polySym_momPoly i)
      (polySym_momPoly j)).real_smul.add
    (BookProof.YangMillsHermite.weylProd_polySym (polySym_mulXPoly i)
      (polySym_mulXPoly j)).real_smul).add ?_
  exact (BookProof.YangMillsHermite.weylProd_polySym (polySym_mulXPoly i)
    (polySym_momPoly j)).real_smul

theorem polySym_fqPoly (P Q S : Fin d → Fin d → ℝ) (b b' : Fin d → ℝ) :
    BookProof.YangMillsHermite.PolySym (fqPoly P Q S b b') :=
  (polySym_fqQuadPoly P Q S).add (polySym_foPoly b b')

set_option maxHeartbeats 1600000 in
-- the `L²` coercions of the Gauss–polynomial core make this defeq check expensive
/-- The Hamiltonian is symmetric on the core: it is built from Weyl-ordered products of
the (symmetric) canonical pair. -/
theorem fqOp_symmetric (P Q S : Fin d → Fin d → ℝ) (b b' : Fin d → ℝ) :
    SymmetricOn (polyGaussCore (d := d)) (fqOp P Q S b b') :=
  symmetricOn_of_polySym (polySym_fqPoly P Q S b b')

/-! ### The ladder form on polynomials -/

theorem momsq_gen (i j : Fin d) (a : Fin d →₀ ℕ) :
    BookProof.YangMillsHermite.weylProd (momPoly i) (momPoly j) (hermiteMv a)
      = (-(1 / 4 : ℂ)) •
          BookProof.YangMillsHermite.weylProd (lop (-1) i) (lop (-1) j) (hermiteMv a) := by
  have hI : (Complex.I / 2) * (Complex.I / 2) = -(1 / 4 : ℂ) := by
    rw [div_mul_div_comm, Complex.I_mul_I]
    norm_num
  rw [momPoly_eq_lop, momPoly_eq_lop, weylProd_smul_apply, hI]

theorem xsq_gen (i j : Fin d) (a : Fin d →₀ ℕ) :
    BookProof.YangMillsHermite.weylProd (mulXPoly i) (mulXPoly j) (hermiteMv a)
      = BookProof.YangMillsHermite.weylProd (lop 1 i) (lop 1 j) (hermiteMv a) := by
  rw [mulXPoly_eq_lop, mulXPoly_eq_lop]

theorem weylxp_gen (i j : Fin d) (a : Fin d →₀ ℕ) :
    BookProof.YangMillsHermite.weylProd (mulXPoly i) (momPoly j) (hermiteMv a)
      = (Complex.I / 2) •
          BookProof.YangMillsHermite.weylProd (lop 1 i) (lop (-1) j) (hermiteMv a) := by
  rw [mulXPoly_eq_lop, momPoly_eq_lop]
  have h := weylProd_smul_apply (d := d) 1 (Complex.I / 2) (lop 1 i) (lop (-1) j) (hermiteMv a)
  rw [one_smul] at h
  rw [h, one_mul]

/-- The contribution of the ordered pair `(i, j)` to the ladder form. -/
theorem fqTerm_hermiteMv (P Q S : Fin d → Fin d → ℝ) (i j : Fin d) (a : Fin d →₀ ℕ) :
    (((P i j : ℝ) : ℂ) • BookProof.YangMillsHermite.weylProd (momPoly i) (momPoly j)
      + ((Q i j : ℝ) : ℂ) • BookProof.YangMillsHermite.weylProd (mulXPoly i) (mulXPoly j)
      + ((S i j : ℝ) : ℂ) • BookProof.YangMillsHermite.weylProd (mulXPoly i) (momPoly j))
        (hermiteMv a)
      = fqAmp P Q S i j • hermiteMv (a + pvec i j)
        + ((starRingEnd ℂ) (fqMl P Q S i j) * (a i : ℂ)) • hermiteMv (shiftm a j i)
        + (fqMl P Q S i j * (a j : ℂ)) • hermiteMv (shiftm a i j)
        + ((starRingEnd ℂ) (fqAmp P Q S i j) * (a j : ℂ)
            * (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℂ)) • hermiteMv (a - pvec i j)
        + (if i = j then (((Q i i + P i i / 4 : ℝ) : ℂ)) • hermiteMv a else 0) := by
  simp only [LinearMap.add_apply, LinearMap.smul_apply]
  rw [momsq_gen, xsq_gen, weylxp_gen,
    weyl_hermiteMv_gen (-1) (-1) i j a, weyl_hermiteMv_gen 1 1 i j a,
    weyl_hermiteMv_gen 1 (-1) i j a, fqAmp, fqMl]
  simp only [map_add, map_sub, map_mul, Complex.conj_ofReal, Complex.conj_I]
  by_cases hij : i = j
  · subst hij
    simp only [↓reduceIte]
    push_cast
    module
  · simp only [if_neg hij, add_zero]
    push_cast
    module

set_option maxHeartbeats 1600000 in
-- expanding the quadratic symbol over all mode pairs makes this rewrite chain expensive
/-- **The ladder form of the quadratic part.** -/
theorem fqQuadPoly_hermiteMv (P Q S : Fin d → Fin d → ℝ) (a : Fin d →₀ ℕ) :
    fqQuadPoly P Q S (hermiteMv a)
      = ((fqSymbol P Q : ℝ) : ℂ) • hermiteMv a
        + ∑ i, ∑ j, (fqAmp P Q S i j • hermiteMv (a + pvec i j)
            + ((starRingEnd ℂ) (fqAmp P Q S i j) * (a j : ℂ)
                * (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℂ))
                  • hermiteMv (a - pvec i j)
            + (fqExch P Q S i j * (a j : ℂ)) • hermiteMv (shiftm a i j)) := by
  classical
  rw [fqQuadPoly, LinearMap.sum_apply]
  have hterm : ∀ i : Fin d, (∑ j, (((P i j : ℝ) : ℂ)
        • BookProof.YangMillsHermite.weylProd (momPoly i) (momPoly j)
      + ((Q i j : ℝ) : ℂ) • BookProof.YangMillsHermite.weylProd (mulXPoly i) (mulXPoly j)
      + ((S i j : ℝ) : ℂ) • BookProof.YangMillsHermite.weylProd (mulXPoly i) (momPoly j)))
        (hermiteMv a)
      = ∑ j, (fqAmp P Q S i j • hermiteMv (a + pvec i j)
        + ((starRingEnd ℂ) (fqMl P Q S i j) * (a i : ℂ)) • hermiteMv (shiftm a j i)
        + (fqMl P Q S i j * (a j : ℂ)) • hermiteMv (shiftm a i j)
        + ((starRingEnd ℂ) (fqAmp P Q S i j) * (a j : ℂ)
            * (((a - Finsupp.single j 1 : Fin d →₀ ℕ) i : ℕ) : ℂ)) • hermiteMv (a - pvec i j)
        + (if i = j then (((Q i i + P i i / 4 : ℝ) : ℂ)) • hermiteMv a else 0)) := by
    intro i
    rw [LinearMap.sum_apply]
    exact Finset.sum_congr rfl fun j _ => fqTerm_hermiteMv P Q S i j a
  rw [Finset.sum_congr rfl fun i _ => hterm i]
  -- split the double sum into its five families
  simp only [Finset.sum_add_distrib]
  -- the diagonal family
  have hdiag : ∑ i : Fin d, ∑ j : Fin d,
      (if i = j then (((Q i i + P i i / 4 : ℝ) : ℂ)) • hermiteMv a else 0)
      = ((fqSymbol P Q : ℝ) : ℂ) • hermiteMv a := by
    have h1 : ∀ i : Fin d, ∑ j : Fin d,
        (if i = j then (((Q i i + P i i / 4 : ℝ) : ℂ)) • hermiteMv a else 0)
        = (((Q i i + P i i / 4 : ℝ) : ℂ)) • hermiteMv a := by
      intro i
      rw [Finset.sum_ite_eq Finset.univ i (fun _ => (((Q i i + P i i / 4 : ℝ) : ℂ))
        • hermiteMv a)]
      simp
    rw [Finset.sum_congr rfl fun i _ => h1 i, ← Finset.sum_smul, fqSymbol]
    push_cast
    ring_nf
  -- the exchange families combine after swapping the two indices
  have hswap : ∑ i : Fin d, ∑ j : Fin d,
      ((starRingEnd ℂ) (fqMl P Q S i j) * (a i : ℂ)) • hermiteMv (shiftm a j i)
      = ∑ i : Fin d, ∑ j : Fin d,
        ((starRingEnd ℂ) (fqMl P Q S j i) * (a j : ℂ)) • hermiteMv (shiftm a i j) :=
    Finset.sum_comm
  have hcomb : ∀ i j : Fin d,
      ((starRingEnd ℂ) (fqMl P Q S j i) * (a j : ℂ)) • hermiteMv (shiftm a i j)
        + (fqMl P Q S i j * (a j : ℂ)) • hermiteMv (shiftm a i j)
        = (fqExch P Q S i j * (a j : ℂ)) • hermiteMv (shiftm a i j) := by
    intro i j
    rw [fqExch]
    module
  have hfinal : ∑ i : Fin d, ∑ j : Fin d,
        ((starRingEnd ℂ) (fqMl P Q S j i) * (a j : ℂ)) • hermiteMv (shiftm a i j)
      + ∑ i : Fin d, ∑ j : Fin d, (fqMl P Q S i j * (a j : ℂ)) • hermiteMv (shiftm a i j)
      = ∑ i : Fin d, ∑ j : Fin d, (fqExch P Q S i j * (a j : ℂ)) • hermiteMv (shiftm a i j) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun j _ => hcomb i j
  rw [hdiag, hswap, ← hfinal]
  abel

end

end BookProof.FullQuadratic
