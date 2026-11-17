/-
Copyright (c) 2026.  All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: BookProof

# The Fourier reconstruction of `det F − 1`, as far as it is algebraic

§63 was careful about where its proof stopped: `normForm_grad_sq` and `not_volDom_normForm` are
statements about the *normal form* `c(εt)²`, and the passage from the model's own penalty
`volPot kappa kv = (κ/2) Σ_q |(det F − 1)^(q)|²` to that normal form was measurement — the Fourier
reconstruction of `det F − 1` — not proof.

This file moves part of that boundary.  The five numbered statements below are what is proved here,
and nothing more.

**1. The discrete grid is orthogonal.**  On an `N`-point grid with `ω = exp(2πi/N)`,

  `∑_{j<N} ω^{mj} = 0` unless `N ∣ m`, and `= N` when `m = 0`      (`dft_orthogonal`, `dft_zero`),

which is the algebraic content of "the dual grid is orthogonal": a single mode is invisible to every
other mode's average.  No measure theory is involved — the grid is finite, and this is the geometric
series plus `ω^N = 1`.

**2. A single-mode residual is exactly its coefficient.**  If the residual's spectrum is supported at
the zero mode — the definition, on a finite grid, of a *spatially constant* residual — then the penalty
is the constant's square:

  `volPot kappa kv = (κ/2) Λ²`      (`volPot_of_single_mode`),

and with `Λ = c·ε·t` on §63's shear family,

  `volPot kappa kv = (κ/2)(c·ε·t)²`      (`volPot_of_shear_constant`),

i.e. exactly the coefficient `c` of the normal form `normForm c` that §63 refutes domination for.  So
the *transfer of the constant* is a theorem.

**3. `hspec` is derived, not assumed.**  §3 below is the assembly.  The discrete transform is
inverted on a grid — `coeff_eq_zero_of_grid_vanishing`, the step in which the identity
`(1/N) Σ_j |R(a_j)|² = Σ_q |R̂_q|²` is used — and a residual that is *spatially constant* on the grid
therefore has no nonzero frequency: `detCoef_eval_eq_zero_of_constant`, `volCoef_eq_zero_of_constant`,
`volCoef_zero_eq_of_constant`, hence `volPot_of_single_mode_of_constant` and
`volPot_of_shear_constant_of_const`, in which the former hypothesis `hspec` no longer appears.  The
inputs are now a modelling fact (`hconst`: `det F` is constant on the grid) and the unitarity of the
transform on that grid (`horth`) — not "the spectrum happens to be supported at the zero mode".

**4. `horth` is reduced to commensurability.**  §4 below discharges the abstract unitarity hypothesis at
the grid it is meant for: on the `N`-point grid `j ↦ j•e` along a direction `e ≠ 0`, the pairing of two
modes is `ζ^{m·j}` for `ζ = e^{2πi/N}` as soon as `⟨q − q', e⟩ = 2πm/N` (`phase_smul_eq_gridRoot`), the
geometric sum is `N` exactly when `N ∣ m` (`geom_sum_gridRoot`), and so **`horth_of_commensurate`**
derives `horth` from a labelling of the wave numbers by integers mod `N`.  `grid_card` and
`grid_nonempty` supply the cardinality and non-emptiness, and
`volPot_of_single_mode_of_commensurate` / `volPot_of_shear_constant_of_commensurate` are the §3 theorems
with `horth` replaced by that labelling.

**5. Aliasing across directions.**  §5 replaces the line by a three-dimensional box
`j ↦ Σ_x j x • e x` with `j x < N`, the coordinates of `e` being independent (`latPoint_injective`,
`gridBox_card`).  The phase factorises (`phase_latPoint`), so does the geometric sum
(`geom_sum_latBox`): it is `N³` exactly when *every* component of the residue vector vanishes, and one
non-commensurate direction sends the whole sum to zero.  Hence orthogonality on the box
(`horth_of_lattice_commensurate`) requires commensurability in all three directions at once, and
`latBox_character_one_iff` identifies the alias classes: two wave numbers are indistinguishable on the
box exactly when each dual component differs by a multiple of `2π`, i.e. `q − q' ∈ N·Λ*` — the total
wave number plays no role.  `volPot_of_single_mode_of_lattice_commensurate` is the assembly.

**What is still not proved.**  The labelling itself.  `horth` is gone from the statements, but its
replacement is a modelling hypothesis: that each pairwise difference of wave numbers is a *lattice
fraction* `2πm/N` along `e`, with the residue distinguishing the modes (`N ∤ m` iff `q ≠ q'`), and in
§5 that this holds in each of the three directions.  None of it is derived from `kv` — that would be a
statement about which modes the model is truncated to, and it is false for a generic choice.  The box
is one truncation and its coordinates are assumed independent; `latBox_character_one_iff` says which
modes collide *on that truncation*, not which modes the model has.  Nothing about ESA or about the
penalty's value off the constant family is claimed.
-/

import BookProof.Ns.ChapterNsLagrangianDetConvolution
import BookProof.Ns.ChapterNsVolDomExpansion
import Mathlib.RingTheory.RootsOfUnity.Complex

namespace BookProof.NsVolDomReconstruction

open MvPolynomial
open BookProof.NsVolDomExpansion BookProof.NsLagrangianDet

noncomputable section

/-! ## 1. The discrete grid is orthogonal -/

/-- The `N`-th root of unity used by the grid. -/
def gridRoot (N : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / N)

/-- **Discrete orthogonality.**  The grid average of a nonzero mode vanishes: multiplying by
`ω^{m·j}` and summing over the grid kills everything the grid cannot resolve, i.e. everything whose
mode number is not a multiple of `N`. -/
theorem dft_orthogonal (N : ℕ) (hN : 0 < N) (m : ℕ) (h : ¬ N ∣ m) :
    ∑ j ∈ Finset.range N, gridRoot N ^ (m * j) = 0 := by
  have hζ := Complex.isPrimitiveRoot_exp N hN.ne'
  have hne : gridRoot N ^ m ≠ 1 := fun h1 => h ((hζ.pow_eq_one_iff_dvd m).mp h1)
  have hne' : Complex.exp (2 * Real.pi * Complex.I / N) ^ m ≠ 1 := hne
  simp only [gridRoot, pow_mul]
  rw [geom_sum_eq hne']
  have hpow : (Complex.exp (2 * Real.pi * Complex.I / N) ^ m) ^ N = 1 := by
    rw [← pow_mul, pow_mul', hζ.pow_eq_one, one_pow]
  rw [hpow]
  simp

/-- The zero mode is counted with full weight `N`: the grid is normalised so that a constant
survives its own average. -/
theorem dft_zero (N : ℕ) : ∑ _j ∈ Finset.range N, gridRoot N ^ (0 * _j) = (N : ℂ) := by
  simp

/-! ## 2. A single-mode residual is its coefficient -/

open Classical in
/-- **The reconstruction at a single mode.**  If the residual `det F − 1` has no nonzero Fourier
coefficient and its zero coefficient is the real constant `Λ`, then the penalty is `(κ/2)Λ²` — the
constant is carried through without distortion.  This is the step §63 called measurement; what is
assumed is the spectrum (`hspec`, `hz`), what is proved is that nothing else enters. -/
theorem volPot_of_single_mode {K : Type*} [Fintype K] (kappa Λ : ℝ) (kv : K → Fin 3 → ℝ)
    (h0 : ((0 : Fin 3 → ℝ) : Fin 3 → ℝ) ∈ waveSet kv)
    (hspec : ∀ q ∈ waveSet kv, q ≠ 0 → volCoef kv q = 0)
    (hz : volCoef kv 0 = MvPolynomial.C ((Λ : ℝ) : ℂ)) :
    volPot kappa kv = MvPolynomial.C (((kappa / 2) * Λ ^ 2 : ℝ) : ℂ) := by
  classical
  unfold volPot
  rw [Finset.sum_eq_single (0 : Fin 3 → ℝ)]
  · rw [hz]
    have hc : conjP (K := K) (MvPolynomial.C ((Λ : ℝ) : ℂ))
        = MvPolynomial.C ((Λ : ℝ) : ℂ) := by
      simp [conjP]
    rw [hc, MvPolynomial.smul_eq_C_mul]
    repeat rw [← map_mul]
    congr 1
    push_cast
    ring
  · intro q hq hq0
    rw [hspec q hq hq0]
    simp
  · intro hnot
    exact absurd h0 hnot

open Classical in
/-- **The constant transfers on the shear family.**  If the residual's spectrum is the single mode
`Λ = c·ε·t` — the shear amplitude times the tilt times `c` — then the model's penalty is
`(κ/2)(c·ε·t)²`, i.e. `(κ/2)` times the value of §63's normal form `normForm c` at `(t, ε)`.  So
the `c` that `not_volDom_normForm` refutes for every `c ≠ 0` is the *measured* constant, not a
re-scaling of the model. -/
theorem volPot_of_shear_constant {K : Type*} [Fintype K] (kappa c ε t : ℝ) (kv : K → Fin 3 → ℝ)
    (h0 : ((0 : Fin 3 → ℝ) : Fin 3 → ℝ) ∈ waveSet kv)
    (hspec : ∀ q ∈ waveSet kv, q ≠ 0 → volCoef kv q = 0)
    (hz : volCoef kv 0 = MvPolynomial.C (((c * ε * t : ℝ) : ℂ))) :
    volPot kappa kv
      = MvPolynomial.C (((kappa / 2) * (c * ε * t) ^ 2 : ℝ) : ℂ) :=
  volPot_of_single_mode kappa (c * ε * t) kv h0 hspec hz

/-- The same statement against §63's normal form: the penalty's value is `(κ/2)` times
`normForm c` evaluated at the shear amplitude and tilt. -/
theorem volPot_of_shear_constant_normForm {K : Type*} [Fintype K] (kappa c ε t : ℝ)
    (kv : K → Fin 3 → ℝ)
    (h0 : ((0 : Fin 3 → ℝ) : Fin 3 → ℝ) ∈ waveSet kv)
    (hspec : ∀ q ∈ waveSet kv, q ≠ 0 → volCoef kv q = 0)
    (hz : volCoef kv 0 = MvPolynomial.C (((c * ε * t : ℝ) : ℂ))) :
    volPot kappa kv = MvPolynomial.C ((kappa / 2 : ℝ) : ℂ) *
      MvPolynomial.C (((c * ε * t) ^ 2 : ℝ) : ℂ) := by
  rw [volPot_of_shear_constant kappa c ε t kv h0 hspec hz, ← map_mul]
  congr 1
  push_cast
  ring

/-! ## 3. The Plancherel assembly: a spatially constant residual has one frequency -/

/-- **Real points separate complex polynomials.**  General form of
`HermiteProductCore.mvpoly_eq_zero_of_eval_real` for an arbitrary index type: it suffices to test
against points whose coordinates are real. -/
theorem mvpoly_eq_zero_of_eval_real_fintype {σ : Type*} {p : MvPolynomial σ ℂ}
    (h : ∀ x : σ → ℝ, MvPolynomial.eval (fun i => ((x i : ℝ) : ℂ)) p = 0) : p = 0 := by
  classical
  refine MvPolynomial.funext_set (fun _ => Set.range ((↑) : ℝ → ℂ)) (fun _ => ?_) ?_
  · exact Set.infinite_range_of_injective Complex.ofReal_injective
  · intro x hx
    choose y hy using fun i => hx i (Set.mem_univ i)
    have hx' : x = fun i => ((y i : ℝ) : ℂ) := by funext i; exact (hy i).symm
    rw [hx']
    exact h y

/-- Conjugation of a plane wave is the plane wave at the negated wave vector. -/
theorem phase_conj (w a : Fin 3 → ℝ) : (starRingEnd ℂ) (phase w a) = phase (-w) a := by
  have hlin : ((∑ x, (-w) x * a x : ℝ) : ℂ) = -((∑ x, w x * a x : ℝ) : ℂ) := by
    push_cast
    rw [← Finset.sum_neg_distrib]
    exact Finset.sum_congr rfl fun x _ => by
      simp only [Pi.neg_apply]; push_cast; ring
  unfold phase
  rw [← Complex.exp_conj, hlin]
  congr 1
  rw [map_mul, Complex.conj_I, Complex.conj_ofReal]
  ring

/-- The pairing of two plane waves is the plane wave at the difference of the wave vectors. -/
theorem phase_mul_conj (q q' a : Fin 3 → ℝ) :
    phase q a * (starRingEnd ℂ) (phase q' a) = phase (q - q') a := by
  rw [phase_conj]
  have hlin : ((∑ x, (q - q') x * a x : ℝ) : ℂ)
      = ((∑ x, q x * a x : ℝ) : ℂ) + ((∑ x, (-q') x * a x : ℝ) : ℂ) := by
    push_cast
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun x _ => by
      simp only [Pi.sub_apply, Pi.neg_apply]; push_cast; ring
  unfold phase
  rw [hlin, ← Complex.exp_add]
  congr 1
  ring

/-- **Discrete Fourier inversion on a grid.**  `horth` is the unitarity of the discrete transform on
the grid — the assembly `(1/N) Σ_j |R(a_j)|² = Σ_q |R̂_q|²` in the form the argument needs.  Under
it, a residual whose Fourier series vanishes at every grid point has vanishing coefficients. -/
theorem coeff_eq_zero_of_grid_vanishing
    (S : Finset (Fin 3 → ℝ)) (c : (Fin 3 → ℝ) → ℂ) (G : Finset (Fin 3 → ℝ))
    (hG : G.Nonempty)
    (horth : ∀ q ∈ S, ∀ q' ∈ S,
      ∑ a ∈ G, phase (q - q') a = if q = q' then (G.card : ℂ) else 0)
    (hzero : ∀ a ∈ G, ∑ q ∈ S, c q * phase q a = 0) :
    ∀ q' ∈ S, c q' = 0 := by
  classical
  intro q' hq'
  have key : ∑ a ∈ G, (∑ q ∈ S, c q * phase q a) * (starRingEnd ℂ) (phase q' a) = 0 := by
    refine Finset.sum_eq_zero fun a ha => ?_
    rw [hzero a ha, zero_mul]
  have h1 : ∑ a ∈ G, (∑ q ∈ S, c q * phase q a) * (starRingEnd ℂ) (phase q' a)
      = ∑ q ∈ S, c q * (∑ a ∈ G, phase (q - q') a) := by
    simp only [Finset.sum_mul, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun a _ => ?_
    rw [mul_assoc, phase_mul_conj]
  have hdiag : ∑ a ∈ G, phase ((q' - q') : Fin 3 → ℝ) a = (G.card : ℂ) := by
    have hh := horth q' hq' q' hq'
    rw [if_pos rfl, sub_self] at hh
    simpa using hh
  have h2 : ∑ q ∈ S, c q * (∑ a ∈ G, phase (q - q') a) = c q' * (G.card : ℂ) := by
    rw [Finset.sum_eq_single (f := fun q => c q * ∑ a ∈ G, phase (q - q') a) q']
    · rw [hdiag]
    · intro q hq hne
      rw [horth q hq q' hq', if_neg hne, mul_zero]
    · intro hnot
      exact absurd hq' hnot
  have h3 : c q' * (G.card : ℂ) = 0 := by rw [← h2, ← h1]; exact key
  have hcard : (G.card : ℂ) ≠ 0 := by
    have hpos : 0 < G.card := Finset.card_pos.mpr hG
    exact_mod_cast hpos.ne'
  exact (mul_eq_zero.mp h3).resolve_right hcard

/-- **The constant case.**  If the series equals the single mode `Λ` at every grid point — i.e. the
residual is spatially constant — then every nonzero coefficient vanishes. -/
theorem coeff_eq_zero_of_grid_const
    (S : Finset (Fin 3 → ℝ)) (c : (Fin 3 → ℝ) → ℂ) (G : Finset (Fin 3 → ℝ))
    (h0 : (0 : Fin 3 → ℝ) ∈ S) (hG : G.Nonempty)
    (horth : ∀ q ∈ S, ∀ q' ∈ S,
      ∑ a ∈ G, phase (q - q') a = if q = q' then (G.card : ℂ) else 0)
    (Λ : ℂ) (hconst : ∀ a ∈ G, ∑ q ∈ S, c q * phase q a = Λ) :
    ∀ q' ∈ S, q' ≠ 0 → c q' = 0 := by
  classical
  set c' : (Fin 3 → ℝ) → ℂ := fun q => c q - if q = 0 then Λ else 0 with hc'
  have hzero : ∀ a ∈ G, ∑ q ∈ S, c' q * phase q a = 0 := by
    intro a ha
    have hsplit : ∑ q ∈ S, c' q * phase q a
        = ∑ q ∈ S, c q * phase q a - Λ * phase (0 : Fin 3 → ℝ) a := by
      have h1 : ∑ q ∈ S, c' q * phase q a
          = ∑ q ∈ S, (c q * phase q a - (if q = 0 then Λ else 0) * phase q a) := by
        refine Finset.sum_congr rfl fun q _ => ?_
        simp only [hc']
        ring
      rw [h1, Finset.sum_sub_distrib]
      congr 1
      simp only [ite_mul, zero_mul]
      rw [Finset.sum_ite_eq' S 0 (fun q => Λ * phase q a), if_pos h0]
    rw [hsplit, hconst a ha, phase_zero, mul_one, sub_self]
  have hres := coeff_eq_zero_of_grid_vanishing S c' G hG horth hzero
  intro q' hq' hq0
  have := hres q' hq'
  simpa [hc', hq0] using this

variable {K : Type*} [Fintype K]

/-- **Constancy on the grid kills the nonzero frequencies.**  If the deformation gradient's
determinant is the constant `1 + Λ` at every grid point, then the residual's Fourier coefficients
vanish away from the zero mode — this is the Plancherel assembly, and it is what the hypothesis
`hspec` used to assume. -/
theorem detCoef_eval_eq_zero_of_constant (kv : K → Fin 3 → ℝ) (Λ : ℝ)
    (G : Finset (Fin 3 → ℝ)) (hG : G.Nonempty)
    (horth : ∀ q ∈ waveSet kv, ∀ q' ∈ waveSet kv,
      ∑ a ∈ G, phase (q - q') a = if q = q' then (G.card : ℂ) else 0)
    (h0 : (0 : Fin 3 → ℝ) ∈ waveSet kv)
    (hconst : ∀ (y : DIdx K → ℝ) (a : Fin 3 → ℝ), a ∈ G →
      (1 + dispGrad kv y a).det = 1 + ((Λ : ℝ) : ℂ))
    (y : DIdx K → ℝ) (q : Fin 3 → ℝ) (hq : q ∈ waveSet kv) (hq0 : q ≠ 0) :
    ev y (detCoef kv q) = 0 := by
  refine coeff_eq_zero_of_grid_const (waveSet kv) (fun q => ev y (detCoef kv q)) G h0 hG horth
    (1 + ((Λ : ℝ) : ℂ)) ?_ q hq hq0
  intro a ha
  rw [← det_deformation_eq kv y a]
  exact hconst y a ha

/-- The residual's coefficients are polynomials, and vanishing at every real point is vanishing. -/
theorem volCoef_eq_zero_of_constant (kv : K → Fin 3 → ℝ) (Λ : ℝ)
    (G : Finset (Fin 3 → ℝ)) (hG : G.Nonempty)
    (horth : ∀ q ∈ waveSet kv, ∀ q' ∈ waveSet kv,
      ∑ a ∈ G, phase (q - q') a = if q = q' then (G.card : ℂ) else 0)
    (h0 : (0 : Fin 3 → ℝ) ∈ waveSet kv)
    (hconst : ∀ (y : DIdx K → ℝ) (a : Fin 3 → ℝ), a ∈ G →
      (1 + dispGrad kv y a).det = 1 + ((Λ : ℝ) : ℂ))
    (q : Fin 3 → ℝ) (hq : q ∈ waveSet kv) (hq0 : q ≠ 0) :
    volCoef kv q = 0 := by
  classical
  have h : volCoef kv q = detCoef kv q := by
    unfold volCoef
    rw [if_neg hq0, sub_zero]
  rw [h]
  exact mvpoly_eq_zero_of_eval_real_fintype fun y =>
    detCoef_eval_eq_zero_of_constant kv Λ G hG horth h0 hconst y q hq hq0

/-- The zero mode is the constant `Λ` itself. -/
theorem volCoef_zero_eq_of_constant (kv : K → Fin 3 → ℝ) (Λ : ℝ)
    (G : Finset (Fin 3 → ℝ)) (hG : G.Nonempty)
    (horth : ∀ q ∈ waveSet kv, ∀ q' ∈ waveSet kv,
      ∑ a ∈ G, phase (q - q') a = if q = q' then (G.card : ℂ) else 0)
    (h0 : (0 : Fin 3 → ℝ) ∈ waveSet kv)
    (hconst : ∀ (y : DIdx K → ℝ) (a : Fin 3 → ℝ), a ∈ G →
      (1 + dispGrad kv y a).det = 1 + ((Λ : ℝ) : ℂ)) :
    volCoef kv 0 = MvPolynomial.C ((Λ : ℝ) : ℂ) := by
  classical
  have hcoeval : ∀ y : DIdx K → ℝ, ev y (detCoef kv 0) = 1 + ((Λ : ℝ) : ℂ) := by
    intro y
    obtain ⟨a₀, ha₀⟩ := hG
    have hne : G.Nonempty := ⟨a₀, ha₀⟩
    have hh := hconst y a₀ ha₀
    rw [det_deformation_eq kv y a₀] at hh
    rw [Finset.sum_eq_single (0 : Fin 3 → ℝ)] at hh
    · rw [phase_zero, mul_one] at hh
      exact hh
    · intro q hq hqe
      have hz : ev y (detCoef kv q) = 0 :=
        detCoef_eval_eq_zero_of_constant kv Λ G hne horth h0 hconst y q hq hqe
      rw [hz, zero_mul]
    · intro hnot
      exact absurd h0 hnot
  have hsub : volCoef kv 0 - MvPolynomial.C ((Λ : ℝ) : ℂ) = 0 := by
    refine mvpoly_eq_zero_of_eval_real_fintype fun y => ?_
    have hv0 : ev y (volCoef kv 0) = ((Λ : ℝ) : ℂ) := by
      have hsplit : volCoef kv 0 = detCoef kv 0 - 1 := by
        unfold volCoef
        simp
      rw [hsplit, map_sub, hcoeval y, map_one]
      ring
    have hgoal : ev y (volCoef kv 0 - MvPolynomial.C ((Λ : ℝ) : ℂ)) = 0 := by
      rw [map_sub, hv0]
      have hC : ev y (MvPolynomial.C ((Λ : ℝ) : ℂ)) = ((Λ : ℝ) : ℂ) := by
        simp [ev]
      rw [hC, sub_self]
    exact hgoal
  exact sub_eq_zero.mp hsub

/-- **The penalty at a spatially constant residual**, with `hspec` derived rather than assumed: the
grid is orthogonal (`horth`), the residual is constant (`hconst`), and the penalty's value is the
constant's square. -/
theorem volPot_of_single_mode_of_constant (kappa Λ : ℝ) (kv : K → Fin 3 → ℝ)
    (G : Finset (Fin 3 → ℝ)) (hG : G.Nonempty)
    (horth : ∀ q ∈ waveSet kv, ∀ q' ∈ waveSet kv,
      ∑ a ∈ G, phase (q - q') a = if q = q' then (G.card : ℂ) else 0)
    (h0 : (0 : Fin 3 → ℝ) ∈ waveSet kv)
    (hconst : ∀ (y : DIdx K → ℝ) (a : Fin 3 → ℝ), a ∈ G →
      (1 + dispGrad kv y a).det = 1 + ((Λ : ℝ) : ℂ)) :
    volPot kappa kv = MvPolynomial.C (((kappa / 2) * Λ ^ 2 : ℝ) : ℂ) :=
  volPot_of_single_mode kappa Λ kv h0
    (fun q hq hq0 => volCoef_eq_zero_of_constant kv Λ G hG horth h0 hconst q hq hq0)
    (volCoef_zero_eq_of_constant kv Λ G hG horth h0 hconst)

/-- **The shear family**, reconstructed: a constant residual `Λ = c·ε·t` gives the penalty
`(κ/2)(c·ε·t)²` — the value of §63's normal form, with no `hspec` assumed. -/
theorem volPot_of_shear_constant_of_const (kappa c ε t : ℝ) (kv : K → Fin 3 → ℝ)
    (G : Finset (Fin 3 → ℝ)) (hG : G.Nonempty)
    (horth : ∀ q ∈ waveSet kv, ∀ q' ∈ waveSet kv,
      ∑ a ∈ G, phase (q - q') a = if q = q' then (G.card : ℂ) else 0)
    (h0 : (0 : Fin 3 → ℝ) ∈ waveSet kv)
    (hconst : ∀ (y : DIdx K → ℝ) (a : Fin 3 → ℝ), a ∈ G →
      (1 + dispGrad kv y a).det = 1 + (((c * ε * t : ℝ)) : ℂ)) :
    volPot kappa kv = MvPolynomial.C (((kappa / 2) * (c * ε * t) ^ 2 : ℝ) : ℂ) :=
  volPot_of_single_mode_of_constant kappa (c * ε * t) kv G hG horth h0 hconst

/-! ## 4. `horth` at the commensurate grid: the unitarity hypothesis is discharged -/

/-- **The grid along one direction**: `N` equally spaced points `j • e`, `j < N`. -/
noncomputable def grid (N : ℕ) (e : Fin 3 → ℝ) : Finset (Fin 3 → ℝ) :=
  (Finset.range N).image fun j : ℕ => (j : ℝ) • e

/-- The grid points are distinct as soon as the direction is nonzero: the `j`-th point is recovered
from any nonzero coordinate. -/
theorem grid_injOn {N : ℕ} {e : Fin 3 → ℝ} (he : e ≠ 0) :
    Set.InjOn (fun j : ℕ => (j : ℝ) • e) ↑(Finset.range N) := by
  obtain ⟨x, hx⟩ : ∃ x, e x ≠ 0 := by
    by_contra h
    push_neg at h
    exact he (funext h)
  intro j _ k _ hjk
  have h1 : (j : ℝ) * e x = (k : ℝ) * e x := by
    have := congrFun hjk x
    simpa only [Pi.smul_apply, smul_eq_mul] using this
  exact Nat.cast_injective (mul_right_cancel₀ hx h1)

theorem grid_card {N : ℕ} {e : Fin 3 → ℝ} (he : e ≠ 0) : (grid N e).card = N := by
  rw [grid, Finset.card_image_of_injOn (grid_injOn he), Finset.card_range]

theorem grid_nonempty {N : ℕ} (hN : 0 < N) (e : Fin 3 → ℝ) : (grid N e).Nonempty :=
  ⟨_, Finset.mem_image.mpr ⟨0, Finset.mem_range.mpr hN, rfl⟩⟩

/-- **The geometric sum on the grid**, for an integer mode number: `Σ_{j<N} ζ^{mj}` is `N` exactly
when `N ∣ m` and zero otherwise.  This is §1's `dft_orthogonal` with the mode number allowed to be
negative (via `exp_int_mul` and conjugation), which is what a difference of two real wave numbers
produces. -/
theorem geom_sum_gridRoot (N : ℕ) (hN : 0 < N) (m : ℤ) :
    ∑ j ∈ Finset.range N, gridRoot N ^ (m * (j : ℤ))
      = if (N : ℤ) ∣ m then (N : ℂ) else 0 := by
  have hζ : IsPrimitiveRoot (gridRoot N) N := by
    simpa [gridRoot] using Complex.isPrimitiveRoot_exp N hN.ne'
  by_cases hdvd : (N : ℤ) ∣ m
  · rw [if_pos hdvd]
    have hone : gridRoot N ^ m = 1 := (hζ.zpow_eq_one_iff_dvd m).mpr hdvd
    have hterm : ∀ j ∈ Finset.range N, gridRoot N ^ (m * (j : ℤ)) = 1 := by
      intro j _
      rw [zpow_mul, hone, one_zpow]
    rw [Finset.sum_congr rfl hterm, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
  · rw [if_neg hdvd]
    have hx : gridRoot N ^ m ≠ 1 := fun h => hdvd ((hζ.zpow_eq_one_iff_dvd m).mp h)
    have hterm : ∀ j ∈ Finset.range N, gridRoot N ^ (m * (j : ℤ)) = (gridRoot N ^ m) ^ j := by
      intro j _
      rw [zpow_mul, zpow_natCast]
    rw [Finset.sum_congr rfl hterm, geom_sum_eq hx]
    have hxN : (gridRoot N ^ m) ^ N = 1 := by
      have h1 : (gridRoot N ^ m) ^ (N : ℤ) = 1 := by
        rw [← zpow_mul, mul_comm, zpow_mul,
          (hζ.zpow_eq_one_iff_dvd (N : ℤ)).mpr (dvd_refl _), one_zpow]
      rwa [zpow_natCast] at h1
    rw [hxN]
    simp

/-- **A commensurate mode is a power of the grid's root of unity.**  If the two wave numbers differ
by `2πm/N` along the grid direction, the plane wave's value at the `j`-th grid point is `ζ^{mj}`. -/
theorem phase_smul_eq_gridRoot (N : ℕ) (hN : 0 < N) (e w : Fin 3 → ℝ) (m : ℤ)
    (h : (∑ x, w x * e x) = 2 * Real.pi * (m : ℝ) / N) (j : ℕ) :
    phase w ((j : ℝ) • e) = gridRoot N ^ (m * (j : ℤ)) := by
  have hsum : (∑ x, w x * (((j : ℝ) • e) x)) = (j : ℝ) * (∑ x, w x * e x) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hNc : ((N : ℂ)) ≠ 0 := by exact_mod_cast hN.ne'
  unfold phase gridRoot
  rw [hsum, h, ← Complex.exp_int_mul]
  congr 1
  push_cast
  field_simp

/-- **The unitarity hypothesis is derived, not assumed.**  On the `N`-point grid along `e ≠ 0`,
orthogonality of the modes follows from a labelling of their pairwise differences by integers mod
`N`: `⟨q − q', e⟩ = 2πm/N`, with the residue `m` vanishing mod `N` exactly on the diagonal.  So the
Plancherel step needs no abstract `horth` — only that the model's wave numbers are commensurate with
the grid. -/
theorem horth_of_commensurate (N : ℕ) (hN : 0 < N) (e : Fin 3 → ℝ) (he : e ≠ 0)
    (S : Finset (Fin 3 → ℝ)) (m : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℤ)
    (hp : ∀ q ∈ S, ∀ q' ∈ S,
      (∑ x, (q - q') x * e x) = 2 * Real.pi * ((m q q' : ℤ) : ℝ) / N)
    (hdvd : ∀ q ∈ S, ∀ q' ∈ S, ((N : ℤ) ∣ m q q' ↔ q = q')) :
    ∀ q ∈ S, ∀ q' ∈ S, ∑ a ∈ grid N e, phase (q - q') a
      = if q = q' then ((grid N e).card : ℂ) else 0 := by
  intro q hq q' hq'
  rw [grid, Finset.sum_image (grid_injOn he)]
  rw [Finset.sum_congr rfl fun j _ =>
    phase_smul_eq_gridRoot N hN e (q - q') (m q q') (hp q hq q' hq') j]
  rw [geom_sum_gridRoot N hN (m q q')]
  by_cases h : q = q'
  · rw [if_pos ((hdvd q hq q' hq').mpr h), if_pos h]
    congr 1
    exact (grid_card he).symm
  · rw [if_neg (fun hd => h ((hdvd q hq q' hq').mp hd)), if_neg h]

/-- **The penalty at a constant residual, with no abstract unitarity input**: the grid is the
commensurate one, the residual is constant on it, and the penalty is the constant's square. -/
theorem volPot_of_single_mode_of_commensurate (kappa Λ : ℝ) (kv : K → Fin 3 → ℝ)
    (N : ℕ) (hN : 0 < N) (e : Fin 3 → ℝ) (he : e ≠ 0)
    (m : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℤ)
    (hp : ∀ q ∈ waveSet kv, ∀ q' ∈ waveSet kv,
      (∑ x, (q - q') x * e x) = 2 * Real.pi * ((m q q' : ℤ) : ℝ) / N)
    (hdvd : ∀ q ∈ waveSet kv, ∀ q' ∈ waveSet kv, ((N : ℤ) ∣ m q q' ↔ q = q'))
    (h0 : (0 : Fin 3 → ℝ) ∈ waveSet kv)
    (hconst : ∀ (y : DIdx K → ℝ) (a : Fin 3 → ℝ), a ∈ grid N e →
      (1 + dispGrad kv y a).det = 1 + ((Λ : ℝ) : ℂ)) :
    volPot kappa kv = MvPolynomial.C (((kappa / 2) * Λ ^ 2 : ℝ) : ℂ) :=
  volPot_of_single_mode_of_constant kappa Λ kv (grid N e) (grid_nonempty hN e)
    (horth_of_commensurate N hN e he (waveSet kv) m hp hdvd) h0 hconst

/-- The same on §63's shear family: `Λ = c·ε·t`, so the penalty is `(κ/2)(c·ε·t)²` with no `hspec`
and no abstract `horth`. -/
theorem volPot_of_shear_constant_of_commensurate (kappa c ε t : ℝ) (kv : K → Fin 3 → ℝ)
    (N : ℕ) (hN : 0 < N) (e : Fin 3 → ℝ) (he : e ≠ 0)
    (m : (Fin 3 → ℝ) → (Fin 3 → ℝ) → ℤ)
    (hp : ∀ q ∈ waveSet kv, ∀ q' ∈ waveSet kv,
      (∑ x, (q - q') x * e x) = 2 * Real.pi * ((m q q' : ℤ) : ℝ) / N)
    (hdvd : ∀ q ∈ waveSet kv, ∀ q' ∈ waveSet kv, ((N : ℤ) ∣ m q q' ↔ q = q'))
    (h0 : (0 : Fin 3 → ℝ) ∈ waveSet kv)
    (hconst : ∀ (y : DIdx K → ℝ) (a : Fin 3 → ℝ), a ∈ grid N e →
      (1 + dispGrad kv y a).det = 1 + (((c * ε * t : ℝ)) : ℂ)) :
    volPot kappa kv = MvPolynomial.C (((kappa / 2) * (c * ε * t) ^ 2 : ℝ) : ℂ) :=
  volPot_of_single_mode_of_commensurate kappa (c * ε * t) kv N hN e he m hp hdvd h0 hconst

/-! ## 5. A three-dimensional lattice: aliasing is a residue condition in every direction

§4 used a line of `N` points, so a mode `q − q'` had a single wave number to be commensurate with.
On the box `j ↦ Σ_x j x • e x` (`j x < N`) the exponent is a *sum* of three pairings, so the geometric
sum factorises into one factor per direction.  Two things follow and one does not:

* orthogonality needs commensurability in **every** direction — one non-commensurate direction makes
the whole sum vanish (`geom_sum_latBox`), so a mode cannot be repaired direction by direction;
* the alias classes are the residues mod `N` of the coefficient vector (`latBox_character_one_iff`):
`q` and `q'` are indistinguishable on the box exactly when each dual component differs by a multiple
of `N`, i.e. `q − q' ∈ N·Λ*`, and the *total* wave number plays no role.

What is still **not** proved: that the model's wave numbers land on this lattice at all.  The box is
one truncation; `latBox_character_one_iff` is a statement about it, and the independence hypothesis on
`e` is a property of the coordinates, not of `kv`. -/

/-- **A lattice-box point**: `Σ_x j x • e x`, with `j x < N` in each direction.  The first index of
`e` labels the basis vector, the second its spatial component. -/
noncomputable def latPoint (N : ℕ) (e : Fin 3 → Fin 3 → ℝ) (j : Fin 3 → Fin N) : Fin 3 → ℝ :=
  fun y => ∑ x, (j x : ℝ) * e x y

/-- **The lattice box**: the image of `j < N` in each direction. -/
noncomputable def gridBox (N : ℕ) (e : Fin 3 → Fin 3 → ℝ) : Finset (Fin 3 → ℝ) :=
  Finset.univ.image (latPoint N e)

/-- The box points are distinct as soon as the three directions are independent: the coefficient
vector of a vanishing combination is zero, and its entries are differences of natural numbers. -/
theorem latPoint_injective (N : ℕ) (e : Fin 3 → Fin 3 → ℝ)
    (hindep : ∀ c : Fin 3 → ℝ, (∀ y, ∑ x, c x * e x y = 0) → c = 0) :
    Function.Injective (latPoint N e) := by
  intro j j' h
  have hcoef : (fun x => (j x : ℝ) - (j' x : ℝ)) = 0 := by
    refine hindep _ fun y => ?_
    have h1 : (∑ x, ((j x : ℝ) - (j' x : ℝ)) * e x y)
        = (∑ x, (j x : ℝ) * e x y) - ∑ x, (j' x : ℝ) * e x y := by
      rw [← Finset.sum_sub_distrib]
      exact Finset.sum_congr rfl fun x _ => by ring
    rw [h1]
    have h2 := congrFun h y
    simp only [latPoint] at h2
    rw [h2, sub_self]
  funext x
  have hx : (j x : ℝ) = (j' x : ℝ) := by
    have h := congrFun hcoef x
    simp only [Pi.zero_apply] at h
    exact sub_eq_zero.mp h
  have hv : (j x).val = (j' x).val := by exact_mod_cast hx
  exact Fin.ext hv

theorem gridBox_card (N : ℕ) (e : Fin 3 → Fin 3 → ℝ)
    (hindep : ∀ c : Fin 3 → ℝ, (∀ y, ∑ x, c x * e x y = 0) → c = 0) :
    (gridBox N e).card = N ^ 3 := by
  simp [gridBox, Finset.card_image_of_injective _ (latPoint_injective N e hindep)]

theorem gridBox_nonempty (N : ℕ) (hN : 0 < N) (e : Fin 3 → Fin 3 → ℝ) :
    (gridBox N e).Nonempty :=
  ⟨_, Finset.mem_image.mpr
    ⟨fun _ => ⟨0, hN⟩, Finset.mem_univ _, rfl⟩⟩

/-- **The phase on the box is a power of the root of unity**: with a per-direction pairing
`⟨w, e x⟩ = 2πm x/N`, the plane wave at `Σ_x j x • e x` is `ζ^{Σ_x m x · j x}`. -/
theorem phase_latPoint (N : ℕ) (_hN : 0 < N) (e : Fin 3 → Fin 3 → ℝ) (w : Fin 3 → ℝ)
    (m : Fin 3 → ℤ) (hin : ∀ x, ∑ y, w y * e x y = 2 * Real.pi * (m x : ℝ) / N)
    (j : Fin 3 → Fin N) :
    phase w (latPoint N e j) = gridRoot N ^ (∑ x, m x * (j x : ℤ)) := by
  have h1 : ∀ y : Fin 3, w y * (latPoint N e j) y = ∑ x, (j x : ℝ) * (w y * e x y) := by
    intro y
    rw [latPoint, Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  have hsum : (∑ y, w y * (latPoint N e j) y) = ∑ x, (j x : ℝ) * (∑ y, w y * e x y) :=
    calc (∑ y, w y * (latPoint N e j) y)
        = ∑ y, ∑ x, (j x : ℝ) * (w y * e x y) := Finset.sum_congr rfl fun y _ => h1 y
      _ = ∑ x, ∑ y, (j x : ℝ) * (w y * e x y) := Finset.sum_comm
      _ = ∑ x, (j x : ℝ) * ∑ y, w y * e x y := by
            refine Finset.sum_congr rfl fun x _ => ?_
            rw [Finset.mul_sum]
  have hsum' : (∑ y, w y * (latPoint N e j) y)
      = (2 * Real.pi / N) * ∑ x, (m x : ℝ) * (j x : ℝ) := by
    rw [hsum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [hin x]
    ring
  have hexp : Complex.I * (((2 * Real.pi / N) * ∑ x, (m x : ℝ) * (j x : ℝ) : ℝ) : ℂ)
      = (((∑ x, m x * (j x : ℤ) : ℤ)) : ℂ)
        * (Complex.I * ((2 * Real.pi / N : ℝ) : ℂ)) := by
    push_cast
    ring
  unfold phase gridRoot
  rw [hsum', hexp, Complex.exp_int_mul]
  congr 2
  push_cast
  ring

/-- Summing a power over `Fin N` is summing it over `range N`. -/
theorem sum_fin_zpow' (N : ℕ) (c : ℂ) (a : ℤ) :
    (∑ j : Fin N, c ^ (a * (j : ℤ))) = ∑ j ∈ Finset.range N, c ^ (a * (j : ℤ)) := by
  rw [Finset.sum_fin_eq_sum_range]
  refine Finset.sum_congr rfl fun j hj => ?_
  rw [dif_pos (Finset.mem_range.mp hj)]

/-- **The geometric sum factorises over the three directions**, and is `N³` exactly when the residue
vector vanishes: commensurability is needed in *every* direction, and one failure sends the whole sum
to zero. -/
theorem geom_sum_latBox (N : ℕ) (hN : 0 < N) (m : Fin 3 → ℤ) :
    ∑ j : Fin 3 → Fin N, gridRoot N ^ (∑ x, m x * (j x : ℤ))
      = if (∀ x, (N : ℤ) ∣ m x) then (N : ℂ) ^ 3 else 0 := by
  have hζ : gridRoot N ≠ 0 := by
    unfold gridRoot
    exact Complex.exp_ne_zero _
  have hfac : ∀ (j : Fin 3 → Fin N), gridRoot N ^ (∑ x, m x * (j x : ℤ))
      = ∏ x, gridRoot N ^ (m x * (j x : ℤ)) := by
    intro j
    rw [Fin.prod_univ_three, Fin.sum_univ_three, zpow_add₀ hζ, zpow_add₀ hζ]
  simp only [hfac]
  have hsingle : ∀ x : Fin 3, (∑ j : Fin N, gridRoot N ^ (m x * ((j : ℕ) : ℤ)))
      = if (N : ℤ) ∣ m x then (N : ℂ) else 0 := by
    intro x
    rw [sum_fin_zpow' N (gridRoot N) (m x)]
    exact geom_sum_gridRoot N hN (m x)
  have hbox := Finset.sum_prod_piFinset (Finset.univ : Finset (Fin N))
    (fun x j => gridRoot N ^ (m x * (j : ℤ)))
  rw [Fintype.piFinset_univ] at hbox
  rw [show (∑ j : Fin 3 → Fin N, ∏ x, gridRoot N ^ (m x * (j x : ℤ)))
      = ∏ x, ∑ j ∈ (Finset.univ : Finset (Fin N)), gridRoot N ^ (m x * (j : ℤ))
      from hbox]
  simp only [hsingle]
  by_cases hall : ∀ x, (N : ℤ) ∣ m x
  · rw [if_pos hall, Finset.prod_congr rfl fun x _ => if_pos (hall x), Finset.prod_const,
      Finset.card_univ, Fintype.card_fin]
  · rw [if_neg hall]
    obtain ⟨x0, hx0⟩ : ∃ x, ¬ (N : ℤ) ∣ m x := by
      by_contra h
      push_neg at h
      exact hall h
    exact Finset.prod_eq_zero (Finset.mem_univ x0) (if_neg hx0)

/-- **Aliasing is a residue condition in each direction.**  On the box, two wave numbers are
indistinguishable exactly when each of their three dual pairings differs by a multiple of `2π`:
the alias classes are the residue vectors mod `N`, so `q − q' ∈ N·Λ*`, and the *total* wave number is
irrelevant. -/
theorem latBox_character_one_iff (N : ℕ) (hN : 0 < N) (e : Fin 3 → Fin 3 → ℝ) (w : Fin 3 → ℝ)
    (m : Fin 3 → ℤ) (hin : ∀ x, ∑ y, w y * e x y = 2 * Real.pi * (m x : ℝ) / N) :
    (∀ j : Fin 3 → Fin N, phase w (latPoint N e j) = 1) ↔ ∀ x, (N : ℤ) ∣ m x := by
  have hζ : IsPrimitiveRoot (gridRoot N) N := by
    simpa [gridRoot] using Complex.isPrimitiveRoot_exp N hN.ne'
  constructor
  · intro h
    have hconst : ∀ j : Fin 3 → Fin N,
        gridRoot N ^ (∑ x, m x * (j x : ℤ)) = 1 := fun j => by
      rw [← phase_latPoint N hN e w m hin j, h j]
    have hval : (∑ j : Fin 3 → Fin N, gridRoot N ^ (∑ x, m x * (j x : ℤ)))
        = ((Fintype.card (Fin 3 → Fin N) : ℕ) : ℂ) := by
      rw [Finset.sum_congr rfl fun j _ => hconst j, Finset.sum_const, Finset.card_univ,
        nsmul_eq_mul, mul_one]
    rw [geom_sum_latBox N hN m] at hval
    by_cases hall : ∀ x, (N : ℤ) ∣ m x
    · exact hall
    · rw [if_neg hall] at hval
      have hne : ((Fintype.card (Fin 3 → Fin N) : ℕ) : ℂ) ≠ 0 := by
        simp [Fintype.card_fin, hN.ne']
      exact absurd hval.symm hne
  · intro hdiv j
    rw [phase_latPoint N hN e w m hin j]
    have hdvd : (N : ℤ) ∣ ∑ x, m x * (j x : ℤ) := by
      refine Finset.dvd_sum fun x _ => ?_
      exact Dvd.dvd.mul_right (hdiv x) ((j x : ℕ) : ℤ)
    rw [(hζ.zpow_eq_one_iff_dvd _).mpr hdvd]

/-- **The unitarity hypothesis on a three-dimensional lattice.**  As on the line, orthogonality of
the modes on the box follows from a per-direction labelling of their differences by integers mod
`N`; what is new is that the labelling must hold in all three directions at once. -/
theorem horth_of_lattice_commensurate (N : ℕ) (hN : 0 < N) (e : Fin 3 → Fin 3 → ℝ)
    (hindep : ∀ c : Fin 3 → ℝ, (∀ y, ∑ x, c x * e x y = 0) → c = 0)
    (S : Finset (Fin 3 → ℝ)) (m : (Fin 3 → ℝ) → (Fin 3 → ℝ) → Fin 3 → ℤ)
    (hp : ∀ q ∈ S, ∀ q' ∈ S, ∀ x,
      ∑ y, (q - q') y * e x y = 2 * Real.pi * ((m q q' x : ℤ) : ℝ) / N)
    (hdvd : ∀ q ∈ S, ∀ q' ∈ S, (∀ x, (N : ℤ) ∣ m q q' x) ↔ q = q') :
    ∀ q ∈ S, ∀ q' ∈ S, ∑ a ∈ gridBox N e, phase (q - q') a
      = if q = q' then ((gridBox N e).card : ℂ) else 0 := by
  intro q hq q' hq'
  rw [gridBox, Finset.sum_image (latPoint_injective N e hindep).injOn]
  rw [Finset.sum_congr rfl fun j _ =>
    phase_latPoint N hN e (q - q') (m q q') (hp q hq q' hq') j]
  rw [geom_sum_latBox N hN (m q q')]
  have hcard : ((gridBox N e).card : ℂ) = (N : ℂ) ^ 3 := by
    rw [gridBox_card N e hindep, Nat.cast_pow]
  by_cases h : q = q'
  · rw [if_pos ((hdvd q hq q' hq').mpr h), if_pos h]
    exact hcard.symm
  · rw [if_neg (fun hd => h ((hdvd q hq q' hq').mp hd)), if_neg h]

/-- **The penalty at a constant residual on a three-dimensional lattice**, with no abstract unitarity
input: the box is commensurate in every direction and the residual is constant on it. -/
theorem volPot_of_single_mode_of_lattice_commensurate (kappa Λ : ℝ) (kv : K → Fin 3 → ℝ)
    (N : ℕ) (hN : 0 < N) (e : Fin 3 → Fin 3 → ℝ)
    (hindep : ∀ c : Fin 3 → ℝ, (∀ y, ∑ x, c x * e x y = 0) → c = 0)
    (m : (Fin 3 → ℝ) → (Fin 3 → ℝ) → Fin 3 → ℤ)
    (hp : ∀ q ∈ waveSet kv, ∀ q' ∈ waveSet kv, ∀ x,
      ∑ y, (q - q') y * e x y = 2 * Real.pi * ((m q q' x : ℤ) : ℝ) / N)
    (hdvd : ∀ q ∈ waveSet kv, ∀ q' ∈ waveSet kv, (∀ x, (N : ℤ) ∣ m q q' x) ↔ q = q')
    (h0 : (0 : Fin 3 → ℝ) ∈ waveSet kv)
    (hconst : ∀ (y : DIdx K → ℝ) (a : Fin 3 → ℝ), a ∈ gridBox N e →
      (1 + dispGrad kv y a).det = 1 + ((Λ : ℝ) : ℂ)) :
    volPot kappa kv = MvPolynomial.C (((kappa / 2) * Λ ^ 2 : ℝ) : ℂ) :=
  volPot_of_single_mode_of_constant kappa Λ kv (gridBox N e) (gridBox_nonempty N hN e)
    (horth_of_lattice_commensurate N hN e hindep (waveSet kv) m hp hdvd) h0 hconst

/-! ## 6. A non-orthogonal basis: aliases are the dual lattice, not `N·Λ*`

§5 never used orthogonality.  The geometric sum needs only bilinearity, and the residue criterion is a
statement about the three pairings `⟨w, e_x⟩`; what *is* basis-dependent is the **labelling** of the
alias class.  In an orthogonal basis it is read as `q − q' ∈ N·Λ*`, with `Λ* = 2π·ℤ³`; in a general
basis the coordinates are the dual pairings, so the class is the `2π`-multiple of the **dual lattice**,
the ℤ-span of the dual basis `f` fixed by `⟨f_x, e_{x'}⟩ = δ_{x x'}`.

* `dual_pairing`: the dual basis contracts as it should,
  `Σ_y (Σ_x k_x · f_{x,y}) · e_{x',y} = k_{x'}` — this is all the "reciprocal lattice" is here;
* `phase_dualComb`: a dual-lattice vector `2π Σ_x k_x f_x` has trivial phase on every box point, so it
  is an alias of `0`;
* `alias_class_dual`: conversely, a residue has trivial phase only if it is such a vector.  Hence the
  alias class is exactly `2π·(dual lattice)`: divisibility by `N` in dual coordinates is the whole
  criterion, and the total wave number plays no role in a skew basis either.

The duality relation already fixes the dual coordinates, so none of this needs `e` to be independent —
that hypothesis belonged to counting the box points (`latPoint_injective`), not to aliasing. -/

/-- **The dual basis** of a lattice basis: `Σ_y f_{x,y} · e_{x',y} = δ_{x x'}`. -/
def IsDualBasis (e f : Fin 3 → Fin 3 → ℝ) : Prop :=
  ∀ x x' : Fin 3, ∑ y, f x y * e x' y = if x = x' then 1 else 0

/-- A **dual-lattice vector**, `2π Σ_x k_x · f_x`: the alias displacements of the box written in the
dual basis. -/
noncomputable def dualComb (f : Fin 3 → Fin 3 → ℝ) (k : Fin 3 → ℤ) : Fin 3 → ℝ :=
  fun y => 2 * Real.pi * ∑ x, (k x : ℝ) * f x y

/-- A **residue in dual coordinates**, `(2π/N) Σ_x m_x · f_x`: the form in which a wave number is
commensurate with the box. -/
noncomputable def dualResidue (N : ℕ) (f : Fin 3 → Fin 3 → ℝ) (m : Fin 3 → ℤ) : Fin 3 → ℝ :=
  fun y => (2 * Real.pi / N) * ∑ x, (m x : ℝ) * f x y

/-- **The dual basis contracts.**  A dual-lattice vector has dual coordinates `k` itself, which is
what makes `dualComb` the natural generator of the alias lattice in a non-orthogonal basis. -/
theorem dual_pairing (e f : Fin 3 → Fin 3 → ℝ) (hdual : IsDualBasis e f) (k : Fin 3 → ℤ)
    (x' : Fin 3) :
    ∑ y, (∑ x, (k x : ℝ) * f x y) * e x' y = (k x' : ℝ) := by
  have hterm : ∀ y : Fin 3,
      (∑ x, (k x : ℝ) * f x y) * e x' y = ∑ x, (k x : ℝ) * (f x y * e x' y) := by
    intro y
    rw [Finset.sum_mul]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [Finset.sum_congr rfl fun y _ => hterm y, Finset.sum_comm]
  have hinner : ∀ x : Fin 3,
      (∑ y, (k x : ℝ) * (f x y * e x' y)) = (k x : ℝ) * (if x = x' then 1 else 0) := by
    intro x
    rw [← Finset.mul_sum, hdual x x']
  rw [Finset.sum_congr rfl fun x _ => hinner x]
  rw [Finset.sum_eq_single (f := fun x : Fin 3 => (k x : ℝ) * (if x = x' then 1 else 0)) x']
  · simp
  · intro x _ hx
    rw [if_neg hx, mul_zero]
  · intro hx
    exact absurd (Finset.mem_univ x') hx

/-- **The pairing of a residue in dual coordinates with the lattice directions**: the wave number
`(2π/N) Σ_x m_x f_x` reads off `2π m_{x'}/N` against `e_{x'}`.  This is `dual_pairing` with the
scalar pulled out, and it is the form in which the torus grid of §10 is commensurate. -/
theorem dualResidue_pairing (N : ℕ) (e f : Fin 3 → Fin 3 → ℝ) (hdual : IsDualBasis e f)
    (m : Fin 3 → ℤ) (x : Fin 3) :
    ∑ y, (dualResidue N f m) y * e x y = 2 * Real.pi * (m x : ℝ) / N := by
  have hw : ∀ y : Fin 3, (dualResidue N f m) y * e x y
      = (2 * Real.pi / N) * ((∑ x', (m x' : ℝ) * f x' y) * e x y) := by
    intro y
    rw [dualResidue]
    ring
  calc ∑ y, (dualResidue N f m) y * e x y
      = ∑ y, (2 * Real.pi / N) * ((∑ x', (m x' : ℝ) * f x' y) * e x y) :=
          Finset.sum_congr rfl fun y _ => hw y
    _ = (2 * Real.pi / N) * ∑ y, (∑ x', (m x' : ℝ) * f x' y) * e x y := by
          rw [← Finset.mul_sum]
    _ = (2 * Real.pi / N) * (m x : ℝ) := by rw [dual_pairing e f hdual m x]
    _ = 2 * Real.pi * ((m x : ℤ) : ℝ) / N := by ring

/-- **The pairing of a dual-lattice vector is its integer coordinate**: the dual coordinates are
what a plane wave `2π Σ_x k_x f_x` reads off against the lattice directions. -/
theorem dualComb_pairing (e f : Fin 3 → Fin 3 → ℝ) (hdual : IsDualBasis e f) (k : Fin 3 → ℤ)
    (x : Fin 3) : ∑ y, (dualComb f k) y * e x y = 2 * Real.pi * (k x : ℝ) := by
  have hw : ∀ y : Fin 3, (dualComb f k) y * e x y
      = 2 * Real.pi * ((∑ x', (k x' : ℝ) * f x' y) * e x y) := by
    intro y
    rw [dualComb]
    ring
  calc ∑ y, (dualComb f k) y * e x y
      = ∑ y, 2 * Real.pi * ((∑ x', (k x' : ℝ) * f x' y) * e x y) :=
          Finset.sum_congr rfl fun y _ => hw y
    _ = 2 * Real.pi * ∑ y, (∑ x', (k x' : ℝ) * f x' y) * e x y := by
          rw [← Finset.mul_sum]
    _ = 2 * Real.pi * (k x : ℝ) := by rw [dual_pairing e f hdual k x]

/-- **A dual-lattice vector has trivial phase on the box**: `2π Σ_x k_x f_x` is an alias of zero in
any basis. -/
theorem phase_dualComb (N : ℕ) (hN : 0 < N) (e f : Fin 3 → Fin 3 → ℝ) (hdual : IsDualBasis e f)
    (k : Fin 3 → ℤ) (j : Fin 3 → Fin N) :
    phase (dualComb f k) (latPoint N e j) = 1 := by
  have hin : ∀ x : Fin 3, ∑ y, (dualComb f k) y * e x y
      = 2 * Real.pi * (((fun x => N * k x) x : ℤ) : ℝ) / N := by
    intro x
    rw [dualComb_pairing e f hdual k x]
    have hNk : (((fun x => N * k x) x : ℤ) : ℝ) = (N : ℝ) * (k x : ℝ) := by
      push_cast
      ring
    rw [hNk]
    field_simp
  rw [phase_latPoint N hN e _ (fun x => N * k x) hin j]
  have hdvd : (N : ℤ) ∣ ∑ x, (N * k x) * (j x : ℤ) :=
    ⟨∑ x, k x * (j x : ℤ), by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun x _ => by ring⟩
  have hζ : IsPrimitiveRoot (gridRoot N) N := by
    simpa [gridRoot] using Complex.isPrimitiveRoot_exp N hN.ne'
  rw [(hζ.zpow_eq_one_iff_dvd _).mpr hdvd]

/-- **An alias is a dual-lattice vector, and conversely.**  A residue in dual coordinates has
trivial phase on the box exactly when its integer labelling is divisible by `N`, i.e. exactly when it
`2π` times an integer combination of the dual basis.  This is the non-orthogonal form of
`q − q' ∈ N·Λ*`. -/
theorem alias_class_dual (N : ℕ) (hN : 0 < N) (e f : Fin 3 → Fin 3 → ℝ)
    (hdual : IsDualBasis e f) (m : Fin 3 → ℤ) :
    (∀ j : Fin 3 → Fin N, phase (dualResidue N f m) (latPoint N e j) = 1) ↔
      ∃ k : Fin 3 → ℤ, dualResidue N f m = dualComb f k := by
  have hin := dualResidue_pairing N e f hdual m
  rw [latBox_character_one_iff N hN e _ m hin]
  constructor
  · intro hdiv
    choose k hk using hdiv
    refine ⟨k, ?_⟩
    funext y
    have hsum : ∑ x, (m x : ℝ) * f x y = (N : ℝ) * ∑ x, (k x : ℝ) * f x y := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun x _ => ?_
      rw [hk x]
      push_cast
      ring
    rw [dualResidue, dualComb, hsum]
    field_simp
  · rintro ⟨k, hk⟩ x
    have hp : ∑ y, (dualResidue N f m) y * e x y = 2 * Real.pi * (k x : ℝ) := by
      rw [hk]
      exact dualComb_pairing e f hdual k x
    rw [hin x] at hp
    have hNz : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have h2 : ((m x : ℤ) : ℝ) = (N : ℝ) * (k x : ℝ) := by
      field_simp at hp
      nlinarith [hp, Real.pi_pos]
    refine ⟨k x, ?_⟩
    have h3 : ((m x : ℤ) : ℝ) = ((N * k x : ℤ) : ℝ) := by
      rw [h2]
      push_cast
      ring
    exact_mod_cast h3

end

/-! ## 7. The labelling hypothesis is periodicity of the field

§74 (and §5) carried, as a hypothesis, that the model's wave numbers have pairings
`⟨w, e_x⟩ = 2π m_x/N` with integer `m_x`.  That is not a separate assumption about the dispersion: it
*is* periodicity of the field under the box translations `x ↦ x + N·e_x`, which is what "a model on
the `N³` box" means.  The translation acts on a plane wave as multiplication by
`phase w (N·e_x) = exp(i·N·⟨w, e_x⟩)`, so invariance pins `N·⟨w, e_x⟩` to `2πℤ` and the labelling
`m` follows.

So the labelling half of §74 is **settled**: it is the same statement as living on the box.  What
stays open is only the *distinctness* half (`hdvd` in §5) — that no two distinct wave numbers of the
model differ by an element of `2π·(dual lattice)` — which is a non-degeneracy property of the wave
set, not a commensurability condition. -/

/-- **Periodicity under the box translations is exactly the commensurability labelling.**  If every
plane wave of the model is invariant under the shifts `x ↦ x + N·e_x`, then its pairings are
multiples of `2π/N`, which is §5's hypothesis. -/
theorem commensurate_of_periodic (N : ℕ) (hN : 0 < N) (e : Fin 3 → Fin 3 → ℝ) (w : Fin 3 → ℝ)
    (h : ∀ x : Fin 3, phase w (fun y => (N : ℝ) * e x y) = 1) :
    ∃ m : Fin 3 → ℤ, ∀ x, ∑ y, w y * e x y = 2 * Real.pi * (m x : ℝ) / N := by
  have hpair : ∀ x, ∃ n : ℤ, (N : ℝ) * (∑ y, w y * e x y) = 2 * Real.pi * (n : ℝ) := by
    intro x
    have hpx := h x
    have harg : (∑ y, w y * ((fun y => (N : ℝ) * e x y) y) : ℝ)
        = (N : ℝ) * ∑ y, w y * e x y := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun y _ => by ring
    unfold phase at hpx
    rw [harg] at hpx
    obtain ⟨n, hn⟩ := Complex.exp_eq_one_iff.mp hpx
    refine ⟨n, ?_⟩
    have hIn : Complex.I * (((N : ℝ) * ∑ y, w y * e x y : ℝ) : ℂ)
        = Complex.I * (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) := by
      rw [hn]
      push_cast
      ring
    have hs : (((N : ℝ) * ∑ y, w y * e x y : ℝ) : ℂ)
        = (((n : ℝ) * (2 * Real.pi) : ℝ) : ℂ) :=
      mul_left_cancel₀ Complex.I_ne_zero hIn
    exact (Complex.ofReal_injective hs).trans (by ring)
  choose n hn using hpair
  refine ⟨n, fun x => ?_⟩
  have hNz : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  rw [← hn x]
  field_simp

/-! ## 8. Distinctness: what `hdvd` says, and when it is implied

§7 reduced the labelling half of §74 to periodicity.  This section settles the remaining half — the
`hdvd` of §4–§5 — by saying exactly what it is and when it follows from the other data.

Two facts.

* **Distinctness is separation by the box's characters.**  Under the labelling `hp`,
  `hdvd` is *equivalent* to: no two distinct wave numbers of the model have the same value on every
  box point (`hdvd_iff_characters_separate`).  So `hdvd` is not a hypothesis about the labelling at all
  — it is the statement that the truncation does not identify two modes of the model, which is what
  "the `N³` box resolves the wave set" means.
* **It follows from a first-Brillouin bound.**  If every pairing of a difference of two wave numbers is
  smaller than `2π` in absolute value, then two such pairs differ by a nonzero multiple of `2π` only
  when the difference vanishes, so distinctness holds (`hdvd_of_pairing_lt`).  The bound is checkable on
  the model's wave set, and it is the only case in which distinctness can be *derived*: a wave set
  containing a mode and its alias fails it, and then `hdvd` is simply false for that set.

Neither statement needs `e` independent; the pairing hypothesis `hp` already fixes the coordinates. -/

/-- **A zero pairing forces a zero label**, so no divisibility is lost when a pairing vanishes: with
`⟨w, e_x⟩ = 2π m_x/N` and `N ≠ 0`, `⟨w, e_x⟩ = 0` implies `m_x = 0`, hence `N ∣ m_x`. -/
theorem int_label_eq_zero_of_pairing_eq_zero (N : ℕ) (hN : 0 < N) (e : Fin 3 → Fin 3 → ℝ)
    (w : Fin 3 → ℝ) (m : Fin 3 → ℤ)
    (hin : ∀ x, ∑ y, w y * e x y = 2 * Real.pi * (m x : ℝ) / N) {x : Fin 3}
    (h : ∑ y, w y * e x y = 0) : m x = 0 := by
  have hN' : ((N : ℝ)) ≠ 0 := by exact_mod_cast hN.ne'
  have h0 : 2 * Real.pi * ((m x : ℤ) : ℝ) / N = 0 := by rw [← hin x, h]
  rw [div_eq_zero_iff] at h0
  rcases h0 with h0 | h0
  · have hm : ((m x : ℤ) : ℝ) = 0 := by
      rcases mul_eq_zero.mp h0 with h2 | h2
      · rcases mul_eq_zero.mp h2 with h3 | h3
        · exact absurd h3 (by norm_num)
        · exact absurd h3 Real.pi_ne_zero
      · exact h2
    exact_mod_cast hm
  · exact absurd h0 hN'

/-- **Distinctness from a first-Brillouin bound.**  If every pairing of a difference of two wave
numbers is smaller than `2π` in absolute value, then no two distinct wave numbers of the set are
labels of each other: divisibility of all three labels by `N` forces each label to vanish, hence all
three pairings to vanish, and the wave numbers to agree. -/
theorem hdvd_of_pairing_lt (N : ℕ) (hN : 0 < N) (e : Fin 3 → Fin 3 → ℝ)
    (S : Finset (Fin 3 → ℝ)) (m : (Fin 3 → ℝ) → (Fin 3 → ℝ) → Fin 3 → ℤ)
    (hp : ∀ q ∈ S, ∀ q' ∈ S, ∀ x,
      ∑ y, (q - q') y * e x y = 2 * Real.pi * ((m q q' x : ℤ) : ℝ) / N)
    (hsep : ∀ q ∈ S, ∀ q' ∈ S, (∀ x, ∑ y, (q - q') y * e x y = 0) → q = q')
    (hsmall : ∀ q ∈ S, ∀ q' ∈ S, ∀ x, |∑ y, (q - q') y * e x y| < 2 * Real.pi) :
    ∀ q ∈ S, ∀ q' ∈ S, (∀ x, (N : ℤ) ∣ m q q' x) ↔ q = q' := by
  intro q hq q' hq'
  constructor
  · intro hd
    refine hsep q hq q' hq' fun x => ?_
    have hNz : (0 : ℝ) < N := by exact_mod_cast hN
    have hpi : (0 : ℝ) < 2 * Real.pi := by linarith [Real.pi_pos]
    -- the label is smaller than `N` in absolute value
    have hsplit : |2 * Real.pi * ((m q q' x : ℤ) : ℝ) / N|
        = 2 * Real.pi * |((m q q' x : ℤ) : ℝ)| / N := by
      rw [abs_div, abs_mul, abs_of_pos hNz,
        abs_of_pos (by positivity : (0 : ℝ) < 2 * Real.pi)]
    have hlt : |m q q' x| < (N : ℤ) := by
      have hs := hsmall q hq q' hq' x
      rw [hp q hq q' hq' x, hsplit] at hs
      have h2 : 2 * Real.pi * |((m q q' x : ℤ) : ℝ)| < 2 * Real.pi * (N : ℝ) :=
        (div_lt_iff₀ hNz).mp hs
      have h3 : |((m q q' x : ℤ) : ℝ)| < (N : ℝ) := lt_of_mul_lt_mul_left h2 hpi.le
      rw [← Int.cast_abs] at h3
      exact_mod_cast h3
    have hz : m q q' x = 0 := by
      obtain ⟨c, hc⟩ := hd x
      rw [hc] at hlt
      rw [abs_mul, Nat.abs_cast] at hlt
      have hNpos : (0 : ℤ) < (N : ℤ) := by exact_mod_cast hN
      have hcabs : |c| < 1 := by
        have h4 : (N : ℤ) * |c| < (N : ℤ) * 1 := by rw [mul_one]; exact hlt
        exact lt_of_mul_lt_mul_left h4 hNpos.le
      rw [Int.abs_lt_one_iff] at hcabs
      rw [hc, hcabs, mul_zero]
    rw [hp q hq q' hq' x, hz]
    push_cast
    simp
  · intro hqq
    subst hqq
    intro x
    rw [int_label_eq_zero_of_pairing_eq_zero N hN e (q - q) (m q q) (hp q hq q hq')
      (x := x) (by simp)]
    exact dvd_zero (N : ℤ)

/-- **Distinctness is separation by the box's characters.**  Under the labelling `hp`, `hdvd` holds
exactly when no two distinct wave numbers of the model take the value `1` together on every point of
the box.  So `hdvd` is a statement about the truncation resolving the model's modes, not about the
labelling. -/
theorem hdvd_iff_characters_separate (N : ℕ) (hN : 0 < N) (e : Fin 3 → Fin 3 → ℝ)
    (S : Finset (Fin 3 → ℝ)) (m : (Fin 3 → ℝ) → (Fin 3 → ℝ) → Fin 3 → ℤ)
    (hp : ∀ q ∈ S, ∀ q' ∈ S, ∀ x,
      ∑ y, (q - q') y * e x y = 2 * Real.pi * ((m q q' x : ℤ) : ℝ) / N) :
    (∀ q ∈ S, ∀ q' ∈ S, (∀ x, (N : ℤ) ∣ m q q' x) ↔ q = q') ↔
      (∀ q ∈ S, ∀ q' ∈ S,
        (∀ j : Fin 3 → Fin N, phase (q - q') (latPoint N e j) = 1) → q = q') := by
  have key := fun q hq q' hq' =>
    latBox_character_one_iff N hN e (q - q') (m q q') (hp q hq q' hq')
  constructor
  · intro h q hq q' hq' hj
    exact (h q hq q' hq').mp ((key q hq q' hq').mp hj)
  · intro h q hq q' hq'
    constructor
    · intro hd
      exact h q hq q' hq' ((key q hq q' hq').mpr hd)
    · intro hqq
      subst hqq
      intro x
      rw [int_label_eq_zero_of_pairing_eq_zero N hN e (q - q) (m q q) (hp q hq q hq')
        (x := x) (by simp)]
      exact dvd_zero (N : ℤ)

/-! ## 9. A concrete wave set: the `N`-torus grid, where distinctness holds on the nose

§8 reduced distinctness to a first-Brillouin bound that a *model* must satisfy.  This section
exhibits a wave set that does: the modes of the `N³` torus on the coordinate axes,

  `torusWave N j = fun y => 2π · j_y / N`,   `j : Fin 3 → Fin N`.

Two components of a difference lie in `[-(N-1), N-1]`, so every pairing is `< 2π` in absolute value
and §8's bound applies; the labels are the integer differences `j_x - j'_x`, and divisibility by `N`
then forces each component to agree.  Hence the penalty theorem needs **no distinctness hypothesis**
at this grid — only that the model's wave numbers lie on it.

The independence and pairing lemmas are for the standard axis basis `axis x`, so `gridBox N axis`
is the ordinary `N³` box; §10 removes that restriction — the same first-Brillouin argument runs in
any basis once the wave numbers are written in its dual basis. -/

/-- The standard basis vector `e_x` of `Fin 3 → ℝ`. -/
noncomputable def axis (x : Fin 3) : Fin 3 → ℝ := fun y => if y = x then 1 else 0

/-- **The axis basis contracts**: `Σ_y q_y · (e_x)_y = q_x`. -/
theorem axis_pairing (q : Fin 3 → ℝ) (x : Fin 3) : ∑ y, q y * axis x y = q x := by
  rw [Finset.sum_eq_single x (fun b _ hb => ?_) (fun hx => absurd (Finset.mem_univ x) hx)]
  · simp [axis]
  · have hz : axis x b = 0 := by simp [axis, hb]
    rw [hz, mul_zero]

/-- **The axis basis is independent** in the form §5 uses. -/
theorem axis_indep : ∀ c : Fin 3 → ℝ, (∀ y, ∑ x, c x * axis x y = 0) → c = 0 := by
  intro c h
  funext y
  have hy := h y
  rw [Finset.sum_eq_single y] at hy
  · simpa [axis] using hy
  · intro b _ hb
    have hz : axis b y = 0 := by simp [axis, Ne.symm hb]
    rw [hz, mul_zero]
  · intro hy'
    exact absurd (Finset.mem_univ y) hy'

/-- **The `N`-torus grid**: modes `2π·j/N` with `j < N` in each direction. -/
noncomputable def torusWave (N : ℕ) (j : Fin 3 → Fin N) : Fin 3 → ℝ :=
  fun y => 2 * Real.pi * (j y : ℝ) / N

/-- **The pairing of a difference of two torus modes is the integer label**, divided by `N`: the
label of `q - q'` in direction `x` is `j_x - j'_x`. -/
theorem torusWave_pairing {N : ℕ} (j j' : Fin 3 → Fin N) (x : Fin 3) :
    ∑ y, (torusWave N j - torusWave N j') y * axis x y
      = 2 * Real.pi * ((j x : ℝ) - (j' x : ℝ)) / N := by
  rw [axis_pairing]
  simp only [Pi.sub_apply, torusWave]
  rw [← sub_div, ← mul_sub]

/-- A nonzero multiple of `N` is at least `N` in absolute value, so a nonzero integer divisible by
`N` cannot be smaller than `N`. -/
private theorem abs_eq_zero_of_dvd_of_abs_lt {N m : ℤ} (hN : 0 < N) (hd : N ∣ m)
    (h : |m| < N) : m = 0 := by
  obtain ⟨c, rfl⟩ := hd
  have habs : |N * c| = N * |c| := by rw [abs_mul, abs_of_pos hN]
  rw [habs] at h
  have h' : N * |c| < N * 1 := by rw [mul_one]; exact h
  have hc1 : |c| < 1 := lt_of_mul_lt_mul_left h' hN.le
  rw [Int.abs_lt_one_iff] at hc1
  rw [hc1, mul_zero]

/-- **Distinctness holds for the torus grid with no extra hypothesis.**  If every wave number of `S`
is a torus mode, then the labels `m` determined by the pairings separate `S`: divisibility of all
three labels by `N` forces each component difference to vanish, and the modes to coincide. -/
theorem hdvd_torus (N : ℕ) (hN : 0 < N) (S : Finset (Fin 3 → ℝ))
    (hS : ∀ q ∈ S, ∃ j : Fin 3 → Fin N, q = torusWave N j)
    (m : (Fin 3 → ℝ) → (Fin 3 → ℝ) → Fin 3 → ℤ)
    (hp : ∀ q ∈ S, ∀ q' ∈ S, ∀ x,
      ∑ y, (q - q') y * axis x y = 2 * Real.pi * ((m q q' x : ℤ) : ℝ) / N) :
    ∀ q ∈ S, ∀ q' ∈ S, (∀ x, (N : ℤ) ∣ m q q' x) ↔ q = q' := by
  intro q hq q' hq'
  obtain ⟨j, hj⟩ := hS q hq
  obtain ⟨j', hj'⟩ := hS q' hq'
  subst hj
  subst hj'
  -- the labels are exactly the component differences
  have hlabel : ∀ x, m (torusWave N j) (torusWave N j') x = (j x : ℤ) - (j' x : ℤ) := by
    intro x
    have hp' := hp (torusWave N j) hq (torusWave N j') hq' x
    rw [torusWave_pairing j j' x] at hp'
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have h2 : (((m (torusWave N j) (torusWave N j') x : ℤ)) : ℝ)
        = ((j x : ℝ) - (j' x : ℝ)) := by
      have h3 := hp'
      field_simp at h3
      linarith [h3]
    exact_mod_cast h2
  constructor
  · intro hd
    funext x
    have hcomp : (j x : ℤ) = (j' x : ℤ) := by
      have hzero : m (torusWave N j) (torusWave N j') x = 0 := by
        refine abs_eq_zero_of_dvd_of_abs_lt (by exact_mod_cast hN) (hd x) ?_
        rw [hlabel x, abs_lt]
        constructor <;> [skip; skip] <;>
          · have h1 := (j x).isLt
            have h2 := (j' x).isLt
            omega
      rw [hlabel x] at hzero
      omega
    have h3 : (j x : ℝ) = (j' x : ℝ) := by exact_mod_cast hcomp
    simp only [torusWave]
    rw [h3]
  · intro hqq x
    have hzero : ((m (torusWave N j) (torusWave N j') x : ℤ) : ℝ) = 0 := by
      have hpz := hp (torusWave N j) hq (torusWave N j') hq' x
      rw [sub_eq_zero.mpr hqq] at hpz
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hpz
      have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      rcases div_eq_zero_iff.mp hpz.symm with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' hpi
        · exact h'
      · exact absurd h hN'
    have hm : m (torusWave N j) (torusWave N j') x = 0 := by exact_mod_cast hzero
    rw [hm]
    exact dvd_zero (N : ℤ)

/-- **The penalty on the torus grid needs no distinctness hypothesis.**  This is
`volPot_of_single_mode_of_lattice_commensurate` on the axis box with `hdvd` discharged by
`hdvd_torus`: the only content left is (i) the model's wave numbers are torus modes and (ii) their
labels are the pairings — both properties of the model's spectrum, not of the truncation. -/
theorem volPot_of_single_mode_of_torus {K : Type*} [Fintype K] (kappa Λ : ℝ)
    (kv : K → Fin 3 → ℝ)
    (N : ℕ) (hN : 0 < N)
    (m : (Fin 3 → ℝ) → (Fin 3 → ℝ) → Fin 3 → ℤ)
    (hS : ∀ q ∈ waveSet kv, ∃ j : Fin 3 → Fin N, q = torusWave N j)
    (hp : ∀ q ∈ waveSet kv, ∀ q' ∈ waveSet kv, ∀ x,
      ∑ y, (q - q') y * axis x y = 2 * Real.pi * ((m q q' x : ℤ) : ℝ) / N)
    (h0 : (0 : Fin 3 → ℝ) ∈ waveSet kv)
    (hconst : ∀ (y : DIdx K → ℝ) (a : Fin 3 → ℝ), a ∈ gridBox N axis →
      (1 + dispGrad kv y a).det = 1 + ((Λ : ℝ) : ℂ)) :
    volPot kappa kv = MvPolynomial.C (((kappa / 2) * Λ ^ 2 : ℝ) : ℂ) :=
  volPot_of_single_mode_of_lattice_commensurate kappa Λ kv N hN axis axis_indep m hp
    (hdvd_torus N hN (waveSet kv) hS m hp) h0 hconst

/-- The same on §63's shear family at the torus grid: the penalty is `(κ/2)(c·ε·t)²` with neither
`hspec`, `horth` nor a distinctness hypothesis. -/
theorem volPot_of_shear_constant_of_torus {K : Type*} [Fintype K] (kappa c ε t : ℝ)
    (kv : K → Fin 3 → ℝ)
    (N : ℕ) (hN : 0 < N)
    (m : (Fin 3 → ℝ) → (Fin 3 → ℝ) → Fin 3 → ℤ)
    (hS : ∀ q ∈ waveSet kv, ∃ j : Fin 3 → Fin N, q = torusWave N j)
    (hp : ∀ q ∈ waveSet kv, ∀ q' ∈ waveSet kv, ∀ x,
      ∑ y, (q - q') y * axis x y = 2 * Real.pi * ((m q q' x : ℤ) : ℝ) / N)
    (h0 : (0 : Fin 3 → ℝ) ∈ waveSet kv)
    (hconst : ∀ (y : DIdx K → ℝ) (a : Fin 3 → ℝ), a ∈ gridBox N axis →
      (1 + dispGrad kv y a).det = 1 + (((c * ε * t : ℝ)) : ℂ)) :
    volPot kappa kv = MvPolynomial.C (((kappa / 2) * (c * ε * t) ^ 2 : ℝ) : ℂ) :=
  volPot_of_single_mode_of_torus kappa (c * ε * t) kv N hN m hS hp h0 hconst

/-! ## 10. A skew box: the same first-Brillouin argument in an arbitrary basis

§9 discharged distinctness on the coordinate box, where the wave numbers are `2π j_x/N` along the
axes.  Nothing in that argument used orthogonality.  What it used is that the *dual* coordinates
of a difference of two wave numbers are the integer differences `j_x − j'_x`, so `|j_x − j'_x| < N`
makes every pairing smaller than `2π` and §8's bound applies.

So let `e` generate the box `gridBox N e` — an arbitrary, possibly skew, triple of directions — and
put the wave numbers in the basis `f` dual to it (`IsDualBasis`, `⟨f_x, e_{x'}⟩ = δ_{x x'}`):

  `skewWave N f j = (2π/N) Σ_x j_x · f_x`.

Then `skewWave_pairing` evaluates the pairing as `2π(j_x − j'_x)/N` — §9's formula with the
coordinates replaced by dual coordinates — and `hdvd_skew` repeats §9's divisibility argument
verbatim: three integer labels divisible by `N`, each smaller than `N` in modulus, hence all zero,
hence `j = j'`, hence `q = q'`.  The axis case is recovered in `skewWave_axis`: `axis` is its own
dual basis, so `torusWave` *is* `skewWave` there.

**Boundary.**  `hdvd_skew` still takes the labelling `hp` as an input.  The dual basis supplies the
*pairing formula*, not the assertion that the model's spectrum lies on the grid: the latter is §7's
periodicity condition (`commensurate_of_periodic`), read with the skew lattice generated by `e`. -/

/-- **The `N`-torus grid of a skew box**: the wave numbers `(2π/N) Σ_x j_x · f_x`, in the basis `f`
dual to the box's directions. -/
noncomputable def skewWave (N : ℕ) (f : Fin 3 → Fin 3 → ℝ) (j : Fin 3 → Fin N) : Fin 3 → ℝ :=
  dualResidue N f fun x => (j x : ℤ)

/-- **The axis case is recovered**: `axis` is its own dual basis, so `skewWave` at `axis` is §9's
`torusWave`. -/
theorem skewWave_axis (N : ℕ) (j : Fin 3 → Fin N) : skewWave N axis j = torusWave N j := by
  funext y
  have hsum : ∑ x, (((j x : ℤ)) : ℝ) * axis x y = (((j y : ℤ)) : ℝ) := by
    rw [Finset.sum_eq_single y (fun b _ hb => ?_)
      (fun hy => absurd (Finset.mem_univ y) hy)]
    · simp [axis]
    · have hz : axis b y = 0 := by simp [axis, Ne.symm hb]
      rw [hz, mul_zero]
  rw [skewWave, dualResidue, hsum, Int.cast_natCast]
  simp only [torusWave]
  ring

/-- **The pairing of a difference of two skew-torus modes is the integer label**: in the box's own
directions, `q − q'` reads off `j_x − j'_x`, scaled by `2π/N`. -/
theorem skewWave_pairing {N : ℕ} (e f : Fin 3 → Fin 3 → ℝ) (hdual : IsDualBasis e f)
    (j j' : Fin 3 → Fin N) (x : Fin 3) :
    ∑ y, (skewWave N f j - skewWave N f j') y * e x y
      = 2 * Real.pi * ((j x : ℝ) - (j' x : ℝ)) / N := by
  have h1 := dualResidue_pairing N e f hdual (fun x => (j x : ℤ)) x
  have h2 := dualResidue_pairing N e f hdual (fun x => (j' x : ℤ)) x
  have hsplit : ∀ y : Fin 3, (skewWave N f j - skewWave N f j') y * e x y
      = (dualResidue N f fun x => (j x : ℤ)) y * e x y
        - (dualResidue N f fun x => (j' x : ℤ)) y * e x y := by
    intro y
    simp only [skewWave, Pi.sub_apply, sub_mul]
  rw [Finset.sum_congr rfl fun y _ => hsplit y, Finset.sum_sub_distrib, h1, h2]
  push_cast
  ring

/-- **Distinctness holds on a skew box with no extra hypothesis**, given the dual basis:
divisibility of all three labels by `N` forces every dual component to agree, and the modes to
coincide.  This is `hdvd_torus` with the box directions `e` and the wave numbers in the dual basis
`f`. -/
theorem hdvd_skew (N : ℕ) (hN : 0 < N) (e f : Fin 3 → Fin 3 → ℝ) (hdual : IsDualBasis e f)
    (S : Finset (Fin 3 → ℝ))
    (hS : ∀ q ∈ S, ∃ j : Fin 3 → Fin N, q = skewWave N f j)
    (m : (Fin 3 → ℝ) → (Fin 3 → ℝ) → Fin 3 → ℤ)
    (hp : ∀ q ∈ S, ∀ q' ∈ S, ∀ x,
      ∑ y, (q - q') y * e x y = 2 * Real.pi * ((m q q' x : ℤ) : ℝ) / N) :
    ∀ q ∈ S, ∀ q' ∈ S, (∀ x, (N : ℤ) ∣ m q q' x) ↔ q = q' := by
  intro q hq q' hq'
  obtain ⟨j, hj⟩ := hS q hq
  obtain ⟨j', hj'⟩ := hS q' hq'
  subst hj
  subst hj'
  have hlabel : ∀ x, m (skewWave N f j) (skewWave N f j') x
      = (j x : ℤ) - (j' x : ℤ) := by
    intro x
    have hp' := hp (skewWave N f j) hq (skewWave N f j') hq' x
    rw [skewWave_pairing e f hdual j j' x] at hp'
    have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
    have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
    have h2 : (((m (skewWave N f j) (skewWave N f j') x : ℤ)) : ℝ)
        = ((j x : ℝ) - (j' x : ℝ)) := by
      have h3 := hp'
      field_simp at h3
      linarith [h3]
    exact_mod_cast h2
  constructor
  · intro hd
    have hcomp : ∀ x, j x = j' x := by
      intro x
      have hzero : m (skewWave N f j) (skewWave N f j') x = 0 := by
        refine abs_eq_zero_of_dvd_of_abs_lt (by exact_mod_cast hN) (hd x) ?_
        rw [hlabel x, abs_lt]
        constructor
        · have h1 := (j x).isLt
          have h2 := (j' x).isLt
          omega
        · have h1 := (j x).isLt
          have h2 := (j' x).isLt
          omega
      have hz : (j x : ℤ) = (j' x : ℤ) := by
        rw [hlabel x] at hzero
        exact sub_eq_zero.mp hzero
      exact Fin.ext (by exact_mod_cast hz)
    rw [funext hcomp]
  · intro hqq x
    have hzero : (((m (skewWave N f j) (skewWave N f j') x : ℤ)) : ℝ) = 0 := by
      have hpz := hp (skewWave N f j) hq (skewWave N f j') hq' x
      rw [sub_eq_zero.mpr hqq] at hpz
      simp only [Pi.zero_apply, zero_mul, Finset.sum_const_zero] at hpz
      have hN' : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
      have hpi : (2 * Real.pi : ℝ) ≠ 0 := by positivity
      rcases div_eq_zero_iff.mp hpz.symm with h | h
      · rcases mul_eq_zero.mp h with h' | h'
        · exact absurd h' hpi
        · exact h'
      · exact absurd h hN'
    have hm : m (skewWave N f j) (skewWave N f j') x = 0 := by exact_mod_cast hzero
    rw [hm]
    exact dvd_zero (N : ℤ)

/-- **The penalty on a skew torus grid needs no distinctness hypothesis.**  `hdvd` is discharged by
`hdvd_skew`; what remains is that the model's wave numbers are the dual-basis modes of the box and
that they are labelled by the pairings. -/
theorem volPot_of_single_mode_of_skew_torus {K : Type*} [Fintype K] (kappa Λ : ℝ)
    (kv : K → Fin 3 → ℝ)
    (N : ℕ) (hN : 0 < N) (e f : Fin 3 → Fin 3 → ℝ) (hdual : IsDualBasis e f)
    (hindep : ∀ c : Fin 3 → ℝ, (∀ y, ∑ x, c x * e x y = 0) → c = 0)
    (m : (Fin 3 → ℝ) → (Fin 3 → ℝ) → Fin 3 → ℤ)
    (hS : ∀ q ∈ waveSet kv, ∃ j : Fin 3 → Fin N, q = skewWave N f j)
    (hp : ∀ q ∈ waveSet kv, ∀ q' ∈ waveSet kv, ∀ x,
      ∑ y, (q - q') y * e x y = 2 * Real.pi * ((m q q' x : ℤ) : ℝ) / N)
    (h0 : (0 : Fin 3 → ℝ) ∈ waveSet kv)
    (hconst : ∀ (y : DIdx K → ℝ) (a : Fin 3 → ℝ), a ∈ gridBox N e →
      (1 + dispGrad kv y a).det = 1 + ((Λ : ℝ) : ℂ)) :
    volPot kappa kv = MvPolynomial.C (((kappa / 2) * Λ ^ 2 : ℝ) : ℂ) :=
  volPot_of_single_mode_of_lattice_commensurate kappa Λ kv N hN e hindep m hp
    (hdvd_skew N hN e f hdual (waveSet kv) hS m hp) h0 hconst

/-- The shear family on a skew torus grid: `(κ/2)(c·ε·t)²` with neither `hspec`, `horth` nor a
distinctness hypothesis. -/
theorem volPot_of_shear_constant_of_skew_torus {K : Type*} [Fintype K] (kappa c ε t : ℝ)
    (kv : K → Fin 3 → ℝ)
    (N : ℕ) (hN : 0 < N) (e f : Fin 3 → Fin 3 → ℝ) (hdual : IsDualBasis e f)
    (hindep : ∀ c : Fin 3 → ℝ, (∀ y, ∑ x, c x * e x y = 0) → c = 0)
    (m : (Fin 3 → ℝ) → (Fin 3 → ℝ) → Fin 3 → ℤ)
    (hS : ∀ q ∈ waveSet kv, ∃ j : Fin 3 → Fin N, q = skewWave N f j)
    (hp : ∀ q ∈ waveSet kv, ∀ q' ∈ waveSet kv, ∀ x,
      ∑ y, (q - q') y * e x y = 2 * Real.pi * ((m q q' x : ℤ) : ℝ) / N)
    (h0 : (0 : Fin 3 → ℝ) ∈ waveSet kv)
    (hconst : ∀ (y : DIdx K → ℝ) (a : Fin 3 → ℝ), a ∈ gridBox N e →
      (1 + dispGrad kv y a).det = 1 + (((c * ε * t : ℝ)) : ℂ)) :
    volPot kappa kv = MvPolynomial.C (((kappa / 2) * (c * ε * t) ^ 2 : ℝ) : ℂ) :=
  volPot_of_single_mode_of_skew_torus kappa (c * ε * t) kv N hN e f hdual hindep m hS hp h0 hconst

/-! ## 11. The shear family's constant residual is a determinant

§2 and §9–§10 carry the *constancy* of the residual as a hypothesis: `hconst` says that on the grid
the determinant of `1 + ∇ξ` is the constant `1 + Λ`, independently of the configuration and of the
point.  For §63's shear family that constant is `c·ε·t`, and here the determinant half of it is
proved.

The deformation gradient of the family is

  `1 + t·e_x⊗e_y + ε·e_y⊗e_x`,

whose determinant is `1 − εt` (`det_one_add_shearGrad`) — the `(εt)²` of the penalty's normal form
is the square of exactly this number.  So a model whose gradient at every configuration and every
grid point is this matrix has `hconst` with `Λ = −εt` (`hconst_of_dispGrad_shear`), and therefore
the penalty `(κ/2)(εt)²` (`volPot_of_shearGrad_of_torus`).

**Boundary.**  What is not proved here, and does not follow from the grid, is that a concrete finite
Fourier model *has* this gradient: `dispGrad` is a sum of `i w_c ξ̂_{m,r} e^{i w·a}` over the
model's modes, so its value at a configuration is fixed by that configuration's coefficients, and
the identification with the shear matrix is a statement about which configuration and which
truncation.
The theorems here make that identification the single remaining input, and discharge everything
downstream of it. -/

/-- **§63's shear family, as a deformation gradient**: `1 + t·e_x⊗e_y + ε·e_y⊗e_x`, i.e. the matrix
with `(x,y)` entry `t` and `(y,x)` entry `ε`. -/
noncomputable def shearGrad (t ε : ℝ) : Matrix (Fin 3) (Fin 3) ℂ :=
  !![0, (t : ℂ), 0; (ε : ℂ), 0, 0; 0, 0, 0]

/-- **The shear's determinant is `1 − εt`**: the residual of the family is `−εt`, which is what
§63's normal form `(c·ε·t)²` is the square of. -/
theorem det_one_add_shearGrad (t ε : ℝ) :
    (1 + shearGrad t ε).det = 1 + ((-(ε * t) : ℝ) : ℂ) := by
  rw [Matrix.det_fin_three]
  simp [shearGrad, Matrix.add_apply]
  ring

/-- **The deformation-gradient constancy hypothesis holds for the shear family**, once the model's
gradient is identified with the shear matrix: `hconst` at `Λ = −εt`. -/
theorem hconst_of_dispGrad_shear {K : Type*} [Fintype K] (kv : K → Fin 3 → ℝ) (t ε : ℝ)
    (G : Finset (Fin 3 → ℝ))
    (h : ∀ (y : DIdx K → ℝ) (a : Fin 3 → ℝ), dispGrad kv y a = shearGrad t ε) :
    ∀ (y : DIdx K → ℝ) (a : Fin 3 → ℝ), a ∈ G →
      (1 + dispGrad kv y a).det = 1 + ((-(ε * t) : ℝ) : ℂ) := by
  intro y a _
  rw [h y a, det_one_add_shearGrad]

/-- **The penalty on the shear family at the torus grid**: `(κ/2)(εt)²`, with the determinant half
of `hconst` proved and only the gradient identification assumed. -/
theorem volPot_of_shearGrad_of_torus {K : Type*} [Fintype K] (kappa t ε : ℝ)
    (kv : K → Fin 3 → ℝ)
    (N : ℕ) (hN : 0 < N) (e f : Fin 3 → Fin 3 → ℝ) (hdual : IsDualBasis e f)
    (hindep : ∀ c : Fin 3 → ℝ, (∀ y, ∑ x, c x * e x y = 0) → c = 0)
    (m : (Fin 3 → ℝ) → (Fin 3 → ℝ) → Fin 3 → ℤ)
    (hS : ∀ q ∈ waveSet kv, ∃ j : Fin 3 → Fin N, q = skewWave N f j)
    (hp : ∀ q ∈ waveSet kv, ∀ q' ∈ waveSet kv, ∀ x,
      ∑ y, (q - q') y * e x y = 2 * Real.pi * ((m q q' x : ℤ) : ℝ) / N)
    (h0 : (0 : Fin 3 → ℝ) ∈ waveSet kv)
    (h : ∀ (y : DIdx K → ℝ) (a : Fin 3 → ℝ), dispGrad kv y a = shearGrad t ε) :
    volPot kappa kv = MvPolynomial.C (((kappa / 2) * (t * ε) ^ 2 : ℝ) : ℂ) := by
  rw [volPot_of_single_mode_of_skew_torus kappa (-(ε * t)) kv N hN e f hdual hindep m hS hp h0
    (hconst_of_dispGrad_shear kv t ε (gridBox N e) h)]
  rw [show ((kappa / 2) * (-(ε * t)) ^ 2 : ℝ) = (kappa / 2) * (t * ε) ^ 2 by ring]

end BookProof.NsVolDomReconstruction
