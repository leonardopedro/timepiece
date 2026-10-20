/-
prove2.me platform library module `Definitions.Def_Giddings1999_AdSModes`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_Giddings1999_AdSModes.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

/-!
# Giddings (1999), *Boundary S matrix and the AdS to CFT dictionary* — definitions

Free scalar field of mass `m` on global AdS_{d+1} of radius `R`, metric (eq. 2)
`ds² = R² sec² r (−dt² + dr² + sin² r dΩ²_{d−1})`, `0 ≤ r < π/2`.
A mode `φ = e^{−iωt} Y_{l m⃗}(Ω) χ(r)` solves `(□ − m²) φ = 0` (eq. 3) iff the radial
profile `χ` solves the radial equation encoded in `IsRadialSolution`.
-/

namespace Giddings1999

open Real

/-- Eq. (4): `ν = ½ √(d² + 4 m² R²)`. -/
noncomputable def nu (d : ℕ) (m R : ℝ) : ℝ :=
  Real.sqrt ((d : ℝ) ^ 2 + 4 * m ^ 2 * R ^ 2) / 2

/-- Eq. (4): `2h₊ = d/2 + ν`. -/
noncomputable def twoHPlus (d : ℕ) (m R : ℝ) : ℝ := (d : ℝ) / 2 + nu d m R

/-- Eq. (4): `2h₋ = d/2 − ν`. -/
noncomputable def twoHMinus (d : ℕ) (m R : ℝ) : ℝ := (d : ℝ) / 2 - nu d m R

/-- Eq. (7): the discrete eigenfrequencies `ω_{nl} = 2h₊ + 2n + l`. -/
noncomputable def omegaNL (d : ℕ) (m R : ℝ) (n l : ℕ) : ℝ :=
  twoHPlus d m R + 2 * (n : ℝ) + (l : ℝ)

/-- Radial reduction of the free equation (3) in the metric (2): `χ` is `C²` on `(0, π/2)` and
`χ'' + (d−1)/(sin r cos r) χ' + ω² χ − l(l+d−2)/sin² r · χ − m²R²/cos² r · χ = 0` there.
(`l(l+d−2)` is the eigenvalue of `−Δ_{S^{d−1}}` on the spherical harmonic `Y_{l m⃗}`.) -/
def IsRadialSolution (d : ℕ) (m R ω : ℝ) (l : ℕ) (χ : ℝ → ℝ) : Prop :=
  ContDiffOn ℝ 2 χ (Set.Ioo 0 (π / 2)) ∧
  ∀ r ∈ Set.Ioo 0 (π / 2),
    deriv (deriv χ) r + ((d : ℝ) - 1) / (sin r * cos r) * deriv χ r + ω ^ 2 * χ r
      - (l : ℝ) * ((l : ℝ) + d - 2) / sin r ^ 2 * χ r - m ^ 2 * R ^ 2 / cos r ^ 2 * χ r = 0

/-- Regularity at the centre `r = 0` of AdS: `χ` stays bounded as `r → 0⁺`. -/
def IsRegularAtOrigin (χ : ℝ → ℝ) : Prop :=
  BddAbove ((fun r => |χ r|) '' Set.Ioc 0 (π / 4))

/-- Finite Klein–Gordon norm: on a constant-`t` slice the KG norm of `e^{−iωt} Y χ` is a constant
multiple of `∫₀^{π/2} tan^{d−1} r · χ(r)² dr`. -/
def HasFiniteKGNorm (d : ℕ) (χ : ℝ → ℝ) : Prop :=
  MeasureTheory.IntegrableOn (fun r => tan r ^ (d - 1) * χ r ^ 2) (Set.Ioo 0 (π / 2))

/-- A normalizable mode of angular momentum `l` and frequency `ω`: a nonzero radial solution that
is regular at the origin and has finite Klein–Gordon norm. -/
def IsNormalizableMode (d : ℕ) (m R ω : ℝ) (l : ℕ) (χ : ℝ → ℝ) : Prop :=
  IsRadialSolution d m R ω l χ ∧ (∃ r ∈ Set.Ioo 0 (π / 2), χ r ≠ 0) ∧
  IsRegularAtOrigin χ ∧ HasFiniteKGNorm d χ

/-- Generalized binomial coefficient `binom(a, j) = a(a−1)⋯(a−j+1)/j!` for real `a`. -/
noncomputable def gbinom (a : ℝ) (j : ℕ) : ℝ :=
  (descPochhammer ℝ j).eval a / (j.factorial : ℝ)

/-- Jacobi polynomial
`P_n^{(α,β)}(x) = Σ_{s=0}^{n} binom(n+α, n−s) binom(n+β, s) ((x−1)/2)^s ((x+1)/2)^{n−s}`. -/
noncomputable def jacobiP (n : ℕ) (α β x : ℝ) : ℝ :=
  ∑ s ∈ Finset.range (n + 1),
    gbinom (n + α) (n - s) * gbinom (n + β) s * ((x - 1) / 2) ^ s * ((x + 1) / 2) ^ (n - s)

/-- Eq. (5): the radial profile `χ_{nl}` of the normalizable mode (explicit form from the paper's
ref. [10]): `χ_{nl}(r) = sin^l r · cos^{2h₊} r · P_n^{(l + d/2 − 1, ν)}(cos 2r)`. -/
noncomputable def modeRadial (d : ℕ) (m R : ℝ) (n l : ℕ) (r : ℝ) : ℝ :=
  sin r ^ l * cos r ^ (twoHPlus d m R) * jacobiP n ((l : ℝ) + (d : ℝ) / 2 - 1) (nu d m R) (cos (2 * r))

/-! ### Integral-kernel form of the boundary S matrix (eqs. 23, 42–44)

`X` is the bulk with volume measure `dV`, `B` the boundary with measure `db`,
`K b x = G_{B∂}(b, x)` the bulk–boundary propagator, `GT` the truncated bulk Green function
`⟨0|T ∏ₐ F(xₐ)|0⟩_T` of `N` points, `Z a` the wave-function renormalizations and `f a` the boundary
wave-packet profiles (in- and out-packets listed together). -/

/-- Eq. (23): the bulk wave packet `φ_f(x) = ∫ db f(b) G_{B∂}(b, x)`. -/
noncomputable def wavePacket {X B : Type*} [MeasurableSpace B] (db : MeasureTheory.Measure B)
    (K : B → X → ℂ) (f : B → ℂ) (x : X) : ℂ :=
  ∫ b, f b * K b x ∂db

/-- Right-hand side of the LSZ formula (42):
`∫ ∏ₐ [dVₐ φ_{fₐ}(xₐ)/Zₐ] ⟨0|T ∏ₐ F(xₐ)|0⟩_T`. -/
noncomputable def lszBoundarySMatrix {X B : Type*} [MeasurableSpace X] [MeasurableSpace B]
    {N : ℕ} (dV : MeasureTheory.Measure X) (db : MeasureTheory.Measure B) (K : B → X → ℂ)
    (Z : Fin N → ℂ) (f : Fin N → B → ℂ) (GT : (Fin N → X) → ℂ) : ℂ :=
  ∫ x, (∏ a, wavePacket db K (f a) (x a) / Z a) * GT x ∂(MeasureTheory.Measure.pi fun _ => dV)

end Giddings1999
