/-
prove2.me platform library module `Definitions.Def_ArtinSieve`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_ArtinSieve.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

namespace ArtinPrimitiveRoots

open Real

/-! ## The sieve parameters of §10 -/

/-- The roughness condition `P^-(m) > y` of §10 (after (10.1)): `m` is a positive integer all of
whose prime factors exceed `y`. Here `P^-(m)` is the least prime factor of `m > 1`, and
`P^-(1) = ∞`. -/
def IsRough (y : ℝ) (m : ℕ) : Prop :=
  0 < m ∧ ∀ p ∈ m.primeFactors, y < (p : ℝ)

/-- The product `V(y) = ∏_{p ≤ y} (1 - 1/p)` over primes, (10.1). -/
noncomputable def mertensProduct (y : ℝ) : ℝ :=
  ∏ p ∈ (Finset.range (⌊y⌋₊ + 1)).filter Nat.Prime, (1 - 1 / (p : ℝ))

/-- The roughness level `W = exp(L^{0.24})`, where `L = log x`, (10.1). -/
noncomputable def sieveLevel (x : ℝ) : ℝ :=
  exp (log x ^ (0.24 : ℝ))

/-! ## Prime groups and marks, (10.2)–(10.4) -/

/-- The prime group `𝒫 = {p prime : exp(L^a) ≤ p ≤ exp(2 L^a)}` with `L = log x`, (10.2);
the `i`th group `𝒫_i` is `primeGroup x (a i)`. -/
noncomputable def primeGroup (x a : ℝ) : Finset ℕ :=
  (Finset.range (⌊exp (2 * log x ^ a)⌋₊ + 1)).filter
    (fun p => p.Prime ∧ exp (log x ^ a) ≤ (p : ℝ))

/-- The set `⋃_i 𝒫_i` of group primes for the band exponents `a_1, …, a_K`, (10.2). -/
noncomputable def groupPrimes (x : ℝ) {K : ℕ} (a : Fin K → ℝ) : Finset ℕ :=
  Finset.univ.biUnion fun i => primeGroup x (a i)

/-- The complete group part `h_𝒫 = ∏_{p ∈ ⋃_i 𝒫_i} p^{v_p(h)}` of `h`, (10.3). -/
noncomputable def groupPart (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (h : ℕ) : ℕ :=
  ∏ p ∈ groupPrimes x a, p ^ h.factorization p

/-- The reciprocal sum `V_i = ∑_{p ∈ 𝒫_i} 1/p` of a prime group, (10.4). -/
noncomputable def groupReciprocalSum (x a : ℝ) : ℝ :=
  ∑ p ∈ primeGroup x a, 1 / (p : ℝ)

/-- `ω_i(h) = ∑_{p ∈ 𝒫_i} 1_{p ∣ h}`, the number of primes of the group dividing `h`, (10.4). -/
noncomputable def groupOmega (x a : ℝ) (h : ℕ) : ℕ :=
  ((primeGroup x a).filter (· ∣ h)).card

/-- `ω(h) = ∑_{i=1}^K ω_i(h)`, (10.4). -/
noncomputable def markOmega (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (h : ℕ) : ℕ :=
  ∑ i, groupOmega x (a i) h

/-- The mark `𝒲(h) = q^{ω(h) - K} ∏_{i=1}^K ω_i(h) / V_i` with parameter `q`, (10.4). -/
noncomputable def mark (q x : ℝ) {K : ℕ} (a : Fin K → ℝ) (h : ℕ) : ℝ :=
  q ^ ((markOmega x a h : ℤ) - K) *
    ∏ i, (groupOmega x (a i) h : ℝ) / groupReciprocalSum x (a i)

/-! ## The rough-number density, (10.11) -/

/-- The terms `D_{γ,j}(w)` of (10.11): `D_{γ,1}(w) = 1/w` and, for `j ≥ 2`,
`D_{γ,j}(w) = (1/j!) ∫_{t_i ≥ γ (i < j), ∑_{i<j} t_i ≤ w - γ} (w - ∑_{i<j} t_i)⁻¹ ∏_{i<j} dt_i/t_i`.
The value at `j = 0` is `0` (the sum in (10.11) starts at `j = 1`). -/
noncomputable def roughDensityTerm (γ w : ℝ) : ℕ → ℝ
  | 0 => 0
  | 1 => 1 / w
  | j + 2 => (1 / ((j + 2).factorial : ℝ)) *
      ∫ t in {t : Fin (j + 1) → ℝ | (∀ i, γ ≤ t i) ∧ ∑ i, t i ≤ w - γ},
        (w - ∑ i, t i)⁻¹ * ∏ i, (t i)⁻¹

/-- The rough-number density `D_γ(w) = ∑_{j ≥ 1} D_{γ,j}(w)` for `w > γ > 0`, (10.11). -/
noncomputable def roughDensity (γ w : ℝ) : ℝ :=
  ∑' j : ℕ, roughDensityTerm γ w j

/-! ## The weights of §12, (12.2) and (12.5) -/

/-- `F(h) = 1{h / h_𝒫 = cQ for a prime Q > x^{0.9}}`, (12.2). -/
noncomputable def predecessorIndicator (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (c h : ℕ) : ℝ := by
  classical
  exact if ∃ Q : ℕ, Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧ h / groupPart x a h = c * Q then 1 else 0

/-- The weight `w(d) = 1{d ≡ u (mod M)} Ψ(d/x) F(d - 1) 𝒲(d - 1)` for `d ≥ 2`, with marks of
parameter `q = 1/2`, (12.2); and `w(1) = 0` (also `w(0) = 0`). -/
noncomputable def constructionWeight (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (x : ℝ) {K : ℕ}
    (a : Fin K → ℝ) (d : ℕ) : ℝ := by
  classical
  exact if 2 ≤ d ∧ (d : ℤ) ≡ u [ZMOD M] then
    Ψ (d / x) * predecessorIndicator x a c (d - 1) * mark (1 / 2) x a (d - 1) else 0

/-- `R_γ(m) = 1{P^-(m) > x^γ}`, (12.5). -/
noncomputable def roughIndicator (x γ : ℝ) (m : ℕ) : ℝ := by
  classical
  exact if IsRough (x ^ γ) m then 1 else 0

/-- `B_γ(m) = D_γ(log m / L) / (L V(W)) · 1{P^-(m) > W}`, (12.5). -/
noncomputable def roughProxy (x γ : ℝ) (m : ℕ) : ℝ := by
  classical
  exact roughDensity γ (log m / log x) / (log x * mertensProduct (sieveLevel x)) *
    if IsRough (sieveLevel x) m then 1 else 0

/-! ## Masses and local densities of §12, (12.8), (12.12), (12.19) -/

/-- A group integer: a positive integer all of whose prime divisors belong to `⋃_i 𝒫_i`
(including `1`), §12.1. -/
def IsGroupInteger (x : ℝ) {K : ℕ} (a : Fin K → ℝ) (r : ℕ) : Prop :=
  0 < r ∧ ∀ p ∈ r.primeFactors, p ∈ groupPrimes x a

/-- The harmonic mass `J_0 = ∑_r 𝒲(r)/r` over group integers `r`, with `q = 1/2`, (12.8). -/
noncomputable def harmonicMass (x : ℝ) {K : ℕ} (a : Fin K → ℝ) : ℝ :=
  ∑' r : {r : ℕ // IsGroupInteger x a r}, mark (1 / 2) x a r / (r : ℝ)

/-- `A_r(ℓ) = ∑_{Q > x^{0.9} prime, crQ+1 ≡ u (mod M), ℓ ∣ crQ+1} Ψ((crQ+1)/x)`, (12.8) and
(12.12); `A_r = A_r(1)`. -/
noncomputable def predecessorMassDvd (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (x : ℝ) (r ℓ : ℕ) : ℝ :=
  ∑' Q : {Q : ℕ // Q.Prime ∧ x ^ (0.9 : ℝ) < Q ∧
      ((c * r * Q + 1 : ℕ) : ℤ) ≡ u [ZMOD M] ∧ ℓ ∣ c * r * Q + 1},
    Ψ (((c * r * Q.1 + 1 : ℕ) : ℝ) / x)

/-- `A_r = ∑_{Q > x^{0.9} prime, crQ+1 ≡ u (mod M)} Ψ((crQ+1)/x)`, (12.8). -/
noncomputable def predecessorMass (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (x : ℝ) (r : ℕ) : ℝ :=
  predecessorMassDvd M c u Ψ x r 1

/-- The total mass `X_0 = ∑_d w(d)`, (12.8). -/
noncomputable def totalMass (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (x : ℝ) {K : ℕ}
    (a : Fin K → ℝ) : ℝ :=
  ∑' d : ℕ, constructionWeight M c u Ψ x a d

/-- The local density `g_r(ℓ) = 1{(ℓ, Mr) = 1} / φ(ℓ)`, (12.12). -/
noncomputable def localDensity (M r ℓ : ℕ) : ℝ :=
  if Nat.Coprime ℓ (M * r) then 1 / (Nat.totient ℓ : ℝ) else 0

/-- The remainder `E_r(ℓ) = A_r(ℓ) - g_r(ℓ) A_r`, (12.12). -/
noncomputable def massRemainder (M c : ℕ) (u : ℤ) (Ψ : ℝ → ℝ) (x : ℝ) (r ℓ : ℕ) : ℝ :=
  predecessorMassDvd M c u Ψ x r ℓ - localDensity M r ℓ * predecessorMass M c u Ψ x r

/-- The constant `𝔖_M = 2 ∏_{p>2} (1 - 1/(p-1)^2) ∏_{p ∣ M, p > 2} (1 - 1/(p-1))⁻¹`, (12.19). -/
noncomputable def singularSeries (M : ℕ) : ℝ :=
  2 * (∏' p : {p : ℕ // p.Prime ∧ 2 < p}, (1 - 1 / ((p.1 : ℝ) - 1) ^ 2)) *
    ∏ p ∈ M.primeFactors.filter (2 < ·), (1 - 1 / ((p : ℝ) - 1))⁻¹

/-! ## Prime counting in progressions (for the classical inputs) -/

/-- `π(Y; q, v) = #{p ≤ Y prime : p ≡ v (mod q)}`. -/
noncomputable def primeCountingAP (Y : ℝ) (q v : ℕ) : ℕ :=
  ((Finset.range (⌊Y⌋₊ + 1)).filter fun p => p.Prime ∧ p ≡ v [MOD q]).card

/-- The logarithmic integral `Li(Y) = ∫_2^Y dt / log t`, as in (12.16). -/
noncomputable def logIntegral (Y : ℝ) : ℝ :=
  ∫ t in (2 : ℝ)..Y, 1 / log t

end ArtinPrimitiveRoots
