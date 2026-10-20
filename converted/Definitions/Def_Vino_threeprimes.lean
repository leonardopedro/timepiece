/-
prove2.me platform library module `Definitions.Def_Vino_threeprimes`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_Vino_threeprimes.lean` (platform Mathlib rev c5ea00351c28).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

/-
# Vinogradov's three primes theorem, conditional on Siegel–Walfisz — statement and reduction

## What this file is

The three primes theorem (every sufficiently large odd `n` is a sum of three primes) is
proved by the Hardy–Littlewood–Vinogradov circle method.  Its major-arc analysis needs the
prime number theorem in arithmetic progressions with an error term uniform in the modulus
`q ≤ (log N)^A` — the **Siegel–Walfisz theorem** — which Mathlib does not have.  This file

1. states Siegel–Walfisz as a `Prop` (`SiegelWalfisz`), in the *Dirichlet character* form;
2. states the weighted asymptotic `R(n) = ½ 𝔖(n) n² + o(n²)` and the existence theorem,
   both conditional on `SiegelWalfisz`;
3. reduces them to explicitly stated pieces, each proved here or AVAILABLE on the platform
   (the file is now complete: every piece is discharged);
4. proves the assembly bookkeeping, the passage from the asymptotic to the existence
   statement, the major-arc main-term identity, and the elementary estimates.

The structural template is `Solutions/M_waring_final.lean` (the proved Waring assembly).

## Why the character form of Siegel–Walfisz

`Vino.vmSum_coprime_char_expansion` (platform, Proved) writes the coprime part of the
exponential sum at a rational point as

  `φ(q) ∑_{n<N, (n,q)=1} Λ(n) e(bn/q) = ∑_{χ mod q} χ⁻¹(b) τ(χ) ψ(N, χ⁻¹)`,

so the input the major arcs actually consume is a bound on `ψ(N,χ) = ∑_{n<N} Λ(n)χ(n)` for
*every* character `χ` mod `q`, uniformly in `q ≤ (log N)^A`.  This is also the form in which
Siegel–Walfisz is proved (zero-free regions of `L(s,χ)` plus Siegel's theorem); the
arithmetic-progression form `ψ(N;q,a) = N/φ(q) + O(N e^{-c√log N})` is *derived* from it by
finite character orthogonality, and conversely, so nothing is lost.  Finally, the character
form makes the principal-character case explicit: `χ = 1` is the prime number theorem with
the de la Vallée-Poussin error term, up to the `O(log q · log N)` contribution of the
`n` sharing a factor with `q`.

## Parameters

`N = n + 1` (so `∑_{a,b,c<N}` captures every representation of `n`);
`P = ⌊(log n)^B⌋₊ + 1` with `B > 12` fixed (the major arcs are `|α − a/q| ≤ P/N`, `q ≤ P`);
Farey order `Q = ⌊N/P⌋` for the dissection.  On the minor arcs `q > P`, and the Vaughan bound
gives `‖S‖ ≪ N (log N)^{4 − B/2}`; with Parseval `∫|S|² ≤ N (log N)²` the minor-arc integral is
`≪ N² (log N)^{6 − B/2} = o(N²)`.  On the major arcs Siegel–Walfisz with `A = B` gives
`S(a/q+β) = μ(q)/φ(q)·v(β) + O(q (1+|β|N) N (log N)^{-B'})`, and the total major-arc error is
`≪ N² P⁵ (log N)^{2−B'} = o(N²)` for `B' > 5B + 2`.
-/
import Definitions.Def_CircleMethod_char
import Definitions.Def_Vino_primes
import Definitions.Def_Vino_ramanujan
import Definitions.Def_Vino_dirichlet
import Theorems.Thm_Vino_three_primes_count
import Theorems.Thm_Vino_integral_cube_orthogonality
import Theorems.Thm_Vino_vmSum_coprime_char_expansion
import Theorems.Thm_Vino_vmSum_split_coprime
import Theorems.Thm_Vino_vmSum_add_one
import Theorems.Thm_Vino_vmSum_zero_len
import Theorems.Thm_Vino_norm_vmSum_le
import Theorems.Thm_Vino_norm_vmSum_le_mul_log
import Theorems.Thm_Vino_psi_le
import Theorems.Thm_Vino_psi_nonneg
import Theorems.Thm_Vino_continuous_e
import Theorems.Thm_Vino_intervalIntegrable_e
import Theorems.Thm_CircleMethod_divisor_bound
import Theorems.Thm_Vino_norm_ramanujan_le
import Theorems.Thm_Vino_ramanujan_mul_unit
import Theorems.Thm_Vino_ramanujan_neg
import Theorems.Thm_Vino_ramanujan_eq_sum_units
import Theorems.Thm_Vino_singSeriesDvd_eq_prod
import Theorems.Thm_Vino_singSeriesDvd_ne_zero_of_odd
import Theorems.Thm_Vino_singSeries_euler_product
import Theorems.Thm_Vino_prod_threePrimeFactor_pos
import Theorems.Thm_Vino_threePrimeFactor_two_of_odd
import Theorems.Thm_Vino_threePrimeFactor_pos_of_odd
import Theorems.Thm_Vino_card_coprime_filter
import Theorems.Thm_Vaughan_norm_vmSum_minor_le
import Theorems.Thm_CircleMethod_farey_cover_coprime
import Theorems.Thm_CircleMethod_rat_sep
import Theorems.Thm_CircleMethod_norm_sum_e_le
import Theorems.Thm_CircleMethod_norm_sum_e_le_inv_nrm
import Theorems.Thm_CircleMethod_integral_e_orthogonality
import Theorems.Thm_CircleMethod_e_add
import Theorems.Thm_CircleMethod_e_neg
import Theorems.Thm_CircleMethod_e_zero
import Theorems.Thm_CircleMethod_e_intCast
import Theorems.Thm_CircleMethod_e_add_intCast
import Theorems.Thm_CircleMethod_e_sub_intCast
import Theorems.Thm_CircleMethod_norm_e
import Theorems.Thm_CircleMethod_nrm_le
import Theorems.Thm_CircleMethod_nrm_le_half
import Theorems.Thm_CircleMethod_nrm_nonneg
import Mathlib.NumberTheory.ArithmeticFunction.VonMangoldt
import Mathlib.NumberTheory.ArithmeticFunction.Moebius
import Mathlib.NumberTheory.DirichletCharacter.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Pow.Asymptotics
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Asymptotics.Lemmas
import Mathlib.Analysis.Asymptotics.Defs
import Mathlib.MeasureTheory.Integral.Bochner.Set
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Basic
import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic
import Mathlib.MeasureTheory.Function.LocallyIntegrable
import Mathlib.MeasureTheory.Measure.Lebesgue.Integral
import Mathlib.Topology.Algebra.InfiniteSum.NatInt
import Mathlib.Analysis.Normed.Group.InfiniteSum
import Mathlib.Data.Nat.Totient
import Mathlib.Data.Nat.Factorization.Induction
import Mathlib.Data.Nat.Squarefree
import Mathlib.Data.Nat.Log
import Mathlib.Analysis.PSeries
import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
import Mathlib.NumberTheory.Divisors
import Theorems.Thm_CircleMethod_sum_e_div_orthogonality
import Theorems.Thm_CircleMethod_norm_e_sub_one_le_two_pi_mul
import Mathlib.NumberTheory.DirichletCharacter.Orthogonality
import Mathlib.NumberTheory.DirichletCharacter.Bounds
import Mathlib.RingTheory.RootsOfUnity.AlgebraicallyClosed
import Mathlib.Analysis.Complex.Polynomial.Basic
import Mathlib.FieldTheory.IsSepClosed
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.BigOperators.Module
import Mathlib.Data.ZMod.Units

open CircleMethod Vino Finset Filter Asymptotics MeasureTheory
open scoped Topology

namespace ThreePrimes

open Classical in
/-- **Siegel–Walfisz** (character form).  For every `A > 0` there are constants `C` and
`c > 0` such that for every modulus `q ≥ 1`, every Dirichlet character `χ` mod `q`, and every
`N ≥ 2` with `q ≤ (log N)^A`,

  `‖ψ(N, χ) − δ_χ N‖ ≤ C N exp(−c √(log N))`,

where `ψ(N,χ) = ∑_{n<N} Λ(n) χ(n)` (`Vino.vmSumChar`) and `δ_χ = 1` for the principal
character and `0` otherwise.  (The `χ = 1` case is the prime number theorem with the de la
Vallée-Poussin error term, up to the `O(log q · log N)` mass of the `n` not coprime to `q`.) -/
def SiegelWalfisz : Prop :=
  ∀ A : ℝ, 0 < A → ∃ C c : ℝ, 0 < c ∧
    ∀ (q : ℕ), 1 ≤ q → ∀ (χ : DirichletCharacter ℂ q) (N : ℕ), 2 ≤ N →
      (q : ℝ) ≤ Real.log N ^ A →
        ‖vmSumChar q χ N - (if χ = 1 then (N : ℂ) else 0)‖
          ≤ C * (N : ℝ) * Real.exp (-c * Real.sqrt (Real.log N))

open Classical in
/-- The power-of-logarithm saving that the circle method actually consumes: for all `A, B > 0`,
`‖ψ(N,χ) − δ_χ N‖ ≤ C N (log N)^{−B}` uniformly for `q ≤ (log N)^A`. -/
def SiegelWalfiszLog : Prop :=
  ∀ A B : ℝ, 0 < A → 0 < B → ∃ C : ℝ,
    ∀ (q : ℕ), 1 ≤ q → ∀ (χ : DirichletCharacter ℂ q) (N : ℕ), 2 ≤ N →
      (q : ℝ) ≤ Real.log N ^ A →
        ‖vmSumChar q χ N - (if χ = 1 then (N : ℂ) else 0)‖
          ≤ C * (N : ℝ) * Real.log N ^ (-B)

/-- `R(n) = ∑_{n₁+n₂+n₃=n} Λ(n₁)Λ(n₂)Λ(n₃)`, the weighted number of representations of `n`
as a sum of three prime powers (`Λ`-weighted). -/
noncomputable def R (n : ℕ) : ℝ :=
  ∑ a ∈ range (n + 1), ∑ b ∈ range (n + 1), ∑ c ∈ range (n + 1),
    if a + b + c = n then
      (ArithmeticFunction.vonMangoldt a : ℝ) * (ArithmeticFunction.vonMangoldt b : ℝ)
        * (ArithmeticFunction.vonMangoldt c : ℝ)
    else 0

/-- The singular series of the three primes problem,
`𝔖(n) = ∑_{q ≥ 1} μ(q) c_q(n) / φ(q)³` (the `q = 0` term of `Vino.singTerm` is `0`). -/
noncomputable def singSeries (n : ℤ) : ℂ := ∑' q : ℕ, singTerm q n

/-- The main term `½ 𝔖(n) n²`. -/
noncomputable def mainTerm (n : ℕ) : ℂ := (1 / 2 : ℂ) * singSeries (n : ℤ) * (n : ℂ) ^ 2

/-- The circle-method integrand `S(α, n+1)³ e(−nα)`. -/
noncomputable def integrand (n : ℕ) (α : ℝ) : ℂ :=
  (vmSum α (n + 1)) ^ 3 * e (-(n : ℝ) * α)

/-- **The weighted three primes asymptotic** (conditional):
`R(n) = ½ 𝔖(n) n² + o(n²)`.  Stated here; proved in §9 (`three_primes_asymptotic`) from the
pieces of §§3–8. -/
def ThreePrimesAsymptotic : Prop :=
  (fun n : ℕ => (R n : ℂ) - mainTerm n) =o[atTop] (fun n : ℕ => (n : ℝ) ^ 2)

/-- **Vinogradov's three primes theorem** (conditional): every sufficiently large odd `n` is
a sum of three primes.  Stated here; proved in §9 (`three_primes`). -/
def ThreePrimesExistence : Prop :=
  ∃ N₀ : ℕ, ∀ n : ℕ, N₀ ≤ n → Odd n →
    ∃ p₁ p₂ p₃ : ℕ, p₁.Prime ∧ p₂.Prime ∧ p₃.Prime ∧ p₁ + p₂ + p₃ = n

/-- `P = ⌊(log N)^B⌋₊ + 1` with `N = n + 1`. -/
noncomputable def arcParam (B : ℝ) (n : ℕ) : ℕ := ⌊Real.log ((n : ℝ) + 1) ^ B⌋₊ + 1

/-- The half-width `ρ = P / N` of the major arcs. -/
noncomputable def rad (B : ℝ) (n : ℕ) : ℝ := (arcParam B n : ℝ) / ((n : ℝ) + 1)

/-- The Farey pairs `(q, a)` with `1 ≤ a ≤ q ≤ P`, `(a, q) = 1`. -/
def fareyPairs (P : ℕ) : Finset (ℕ × ℕ) :=
  (Finset.Icc 1 P).biUnion fun q =>
    ((Finset.Icc 1 q).filter fun a => Nat.Coprime a q).image fun a => (q, a)

/-- The major arcs. -/
noncomputable def major (B : ℝ) (n : ℕ) : Set ℝ :=
  ⋃ p ∈ fareyPairs (arcParam B n),
    Set.Icc ((p.2 : ℝ) / (p.1 : ℝ) - rad B n) ((p.2 : ℝ) / (p.1 : ℝ) + rad B n)

/-- The minor arcs. -/
noncomputable def minor (B : ℝ) (n : ℕ) : Set ℝ :=
  Set.Ico (rad B n) (1 + rad B n) \ major B n

/-- `v(β) = ∑_{m<N} e(βm)`, the main-term generating function. -/
noncomputable def v (β : ℝ) (N : ℕ) : ℂ := ∑ m ∈ range N, e (β * (m : ℝ))

/-- The arithmetic factor `μ(q)/φ(q)` of the main term at `a/q`. -/
noncomputable def arith (q : ℕ) : ℂ :=
  ((ArithmeticFunction.moebius q : ℤ) : ℂ) / (Nat.totient q : ℂ)

/-- The truncated singular integral `J(n, ρ) = ∫_{−ρ}^{ρ} v(β)³ e(−nβ) dβ` (with `N = n+1`). -/
noncomputable def singIntTrunc (n : ℕ) (ρ : ℝ) : ℂ :=
  ∫ β in (-ρ)..ρ, (v β (n + 1)) ^ 3 * e (-(n : ℝ) * β)

/-- The truncated singular series `∑_{q ≤ P} μ(q) c_q(n) / φ(q)³`. -/
noncomputable def truncSeries (P : ℕ) (n : ℤ) : ℂ := ∑ q ∈ Finset.Icc 1 P, singTerm q n

/-- The error made on the arc around `a/q` when `S³` is replaced by `(arith(q) v)³`. -/
noncomputable def arcErr (n : ℕ) (q a : ℕ) (ρ : ℝ) : ℂ :=
  ∫ β in (-ρ)..ρ, ((vmSum ((a : ℝ) / (q : ℝ) + β) (n + 1)) ^ 3 - (arith q * v β (n + 1)) ^ 3)
    * e (-(n : ℝ) * β)

/-- The five quantities entering the assembly. -/
noncomputable def minorInt (B : ℝ) (n : ℕ) : ℂ := ∫ α in minor B n, integrand n α

noncomputable def majorInt (B : ℝ) (n : ℕ) : ℂ := ∫ α in major B n, integrand n α

noncomputable def J (B : ℝ) (n : ℕ) : ℂ := singIntTrunc n (rad B n)

noncomputable def T (B : ℝ) (n : ℕ) : ℂ := truncSeries (arcParam B n) (n : ℤ)

noncomputable def target (n : ℕ) : ℝ := (n : ℝ) ^ 2

/-- The prime powers `p^k ≤ n` with `k ≥ 2`. -/
noncomputable def primePowNonPrime (n : ℕ) : Finset ℕ :=
  (range (n + 1)).filter fun a => IsPrimePow a ∧ ¬ a.Prime

end ThreePrimes
