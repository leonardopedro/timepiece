import Mathlib
import BookProof.Qym.ChapterYangMillsBandBounds
import BookProof.Toolbox.ChapterFockWeightedSchurEsa

/-!
# The weighted Schur gates for the non-abelian Yang–Mills Hermite matrix

`BookProof.YangMillsBandBounds.ym_hermCol_band_bounds` says the Hermite matrix of the
gauge-fixed Yang–Mills Hamiltonian has at most `M` entries per column, band radius `4` in the
degree, and entries bounded by `C (deg + 1)²`.  The weighted Schur theory of
`BookProof.FockWeightedSchur` turns three gates on a one-particle matrix into essential
self-adjointness of its second quantization, for a symbol `w` with `w ≥ 1`.

The symbol that matches the entry growth is `w_k = (deg k + 1)²`: with it the entry bound is
*exactly* a multiple of `w`, so the row gate is the card bound times the entry bound, and the
column gate needs one extra observation — over a band of radius `4` in the degree a weight
`(deg+1)²` can drop by at most a factor `49`.

## What is proved

* `ymW` — the symbol `w_k = ((deg (e k) : ℝ) + 1)²`, with `ymW_nonneg` and `ymW_one_le`.
* `ymW_le_of_band` — across a degree band of radius `4` the weight grows by at most `49`.
* `ymHermCol_row_col_gates` — **the row and column gates hold**, with a single explicit
  constant: `∃ K ≥ 0, WRowBound (ymW e) (ymHermCol e fabc) K ∧ WColBound … K`.
* `ymHermCol_essentiallySelfAdjointOn_core_of_commBound` — **one hypothesis left**: given the
  commutator gate, `dΓ(H₁)` is essentially self-adjoint on the finite-occupation core.

## Honest boundary — and a correction

The commutator gate is **not proved here, and the band calculus cannot supply it.**  With
`w = (deg+1)²` the gate's weight factor is
`|w_j² − w_k²| / (w_k w_j) = |w_j/w_k − w_k/w_j|`, which across a band of fixed radius in the
degree behaves like `D/deg`; the band calculus offers only the *upper* bound
`|A_{kj}| ≤ C (deg k + 1)²` on the entries, so that bound alone is consistent with gate terms
of size `Θ(deg)`, not with a bounded sum.  The gate therefore needs information the band
calculus does not carry — decay of the actual coefficients, not their degree — and nothing
below supplies it.  This is the order obstruction the header of
`BookProof.YangMillsBandBounds` records: the gate route is order-`2`-adapted, and the
non-abelian magnetic field makes `H₁` order `4`.  The second theorem above is explicitly
conditional on the gate.

**Correction (2026-11-13b).**  An earlier revision of this header asserted that the gate is
*false* for this symbol, on the grounds that the entries are `Θ(deg²)`.  That was wrong: only an
*upper* bound `C(deg+1)²` is available, and no lower bound on any entry is proved anywhere in the
corpus, so no failure of the gate is established — nor could one be, on upper bounds alone.
What is established is the weaker, still useful statement: the three gates are not all
derivable from the band bounds, and the missing one is the commutator gate.

Everything is `sorry`-free and `axiom`-free.
-/

namespace BookProof.YangMillsWeightedGates

noncomputable section

open BookProof.YangMillsBandBounds BookProof.FockWeightedSchur
open BookProof.FockSecondQuantization BookProof.NavierStokesFlow BookProof.FarisLavine

/-- The symbol matched to the Yang–Mills entry growth: `w_k = ((deg (e k) : ℝ) + 1)²`. -/
def ymW (e : ℕ ≃ (Fin 99 →₀ ℕ)) (k : ℕ) : ℝ := (((e k).degree : ℝ) + 1) ^ 2

theorem ymW_nonneg (e : ℕ ≃ (Fin 99 →₀ ℕ)) (k : ℕ) : 0 ≤ ymW e k := by
  have h : (0 : ℝ) ≤ ((e k).degree : ℝ) + 1 := by positivity
  exact pow_nonneg h 2

theorem ymW_one_le (e : ℕ ≃ (Fin 99 →₀ ℕ)) (k : ℕ) : 1 ≤ ymW e k := by
  have h : (1 : ℝ) ≤ ((e k).degree : ℝ) + 1 := by
    have h0 : (0 : ℝ) ≤ ((e k).degree : ℝ) := Nat.cast_nonneg _
    linarith
  calc (1 : ℝ) = 1 ^ 2 := by norm_num
    _ ≤ (((e k).degree : ℝ) + 1) ^ 2 := pow_le_pow_left₀ (by norm_num) h 2

/-- **The weight is slowly varying across the degree band**: if `deg (e j)` and `deg (e k)`
differ by at most `4`, then `w_j ≤ 49 w_k`. -/
theorem ymW_le_of_band {e : ℕ ≃ (Fin 99 →₀ ℕ)} {j k : ℕ}
    (h : (((e k).degree : ℤ) - ((e j).degree : ℤ)).natAbs ≤ 4) :
    ymW e j ≤ 49 * ymW e k := by
  have hle : ((e j).degree : ℤ) ≤ ((e k).degree : ℤ) + 4 := by omega
  have hcast : ((e j).degree : ℝ) ≤ ((e k).degree : ℝ) + 4 := by exact_mod_cast hle
  have hr : ((e j).degree : ℝ) + 1 ≤ 7 * (((e k).degree : ℝ) + 1) := by
    rcases le_or_gt (e j).degree 3 with h3 | h4
    · have h3' : ((e j).degree : ℝ) ≤ 3 := by exact_mod_cast h3
      have hk : (0 : ℝ) ≤ ((e k).degree : ℝ) := Nat.cast_nonneg _
      linarith
    · have h4' : (4 : ℝ) ≤ ((e j).degree : ℝ) := by exact_mod_cast h4
      linarith
  calc ymW e j = (((e j).degree : ℝ) + 1) ^ 2 := rfl
    _ ≤ (7 * (((e k).degree : ℝ) + 1)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hr 2
    _ = 49 * (((e k).degree : ℝ) + 1) ^ 2 := by ring
    _ = 49 * ymW e k := rfl

/-- **The row and column gates of the weighted Schur theory hold for the Yang–Mills Hermite
matrix**, with the symbol `(deg+1)²` and a single constant for both. -/
theorem ymHermCol_row_col_gates (e : ℕ ≃ (Fin 99 →₀ ℕ))
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) :
    ∃ K : ℝ, 0 ≤ K ∧ WRowBound (ymW e) (ymHermCol e fabc) K ∧
      WColBound (ymW e) (ymHermCol e fabc) K := by
  obtain ⟨M, C, hC, hcard, hband, hent⟩ := ym_hermCol_band_bounds e fabc
  have hM : (0 : ℝ) ≤ (M : ℝ) := Nat.cast_nonneg _
  refine ⟨49 * (M : ℝ) * C, by positivity, ?_, ?_⟩
  · -- rows: at most `M` entries, each at most `C * w_k`
    intro k
    have hb : ∀ j ∈ (ymHermCol e fabc k).support,
        ‖ymHermCol e fabc k j‖ ≤ C * ymW e k := fun j _ => hent k j
    have hcardR : ((ymHermCol e fabc k).support.card : ℝ) ≤ (M : ℝ) := by
      exact_mod_cast hcard k
    have hw : 0 ≤ C * ymW e k := mul_nonneg hC (ymW_nonneg e k)
    have hone : 1 ≤ ymW e k := ymW_one_le e k
    calc ∑ j ∈ (ymHermCol e fabc k).support, ‖ymHermCol e fabc k j‖
        ≤ ∑ _j ∈ (ymHermCol e fabc k).support, C * ymW e k := Finset.sum_le_sum hb
      _ = ((ymHermCol e fabc k).support.card : ℝ) * (C * ymW e k) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (M : ℝ) * (C * ymW e k) := mul_le_mul_of_nonneg_right hcardR hw
      _ ≤ 49 * (M : ℝ) * C * ymW e k := by nlinarith [mul_nonneg hM hC]
  · -- columns: at most `M` entries, each at most `49 C`
    intro j
    have hb : ∀ k ∈ (ymHermCol e fabc j).support,
        ‖ymHermCol e fabc j k‖ / ymW e k ≤ 49 * C := by
      intro k hk
      have he : ‖ymHermCol e fabc j k‖ ≤ C * ymW e j := hent j k
      have hwjk : ymW e j ≤ 49 * ymW e k := ymW_le_of_band (hband j k hk)
      have hpos : 0 < ymW e k := lt_of_lt_of_le zero_lt_one (ymW_one_le e k)
      have hratio : ymW e j / ymW e k ≤ 49 := by
        rw [div_le_iff₀ hpos]
        nlinarith [ymW_nonneg e j]
      calc ‖ymHermCol e fabc j k‖ / ymW e k
          ≤ (C * ymW e j) / ymW e k := div_le_div_of_nonneg_right he hpos.le
        _ = C * (ymW e j / ymW e k) := by ring
        _ ≤ C * 49 := by nlinarith [hratio]
        _ = 49 * C := by ring
    calc ∑ k ∈ (ymHermCol e fabc j).support, ‖ymHermCol e fabc j k‖ / ymW e k
        ≤ ∑ _k ∈ (ymHermCol e fabc j).support, 49 * C := Finset.sum_le_sum hb
      _ = ((ymHermCol e fabc j).support.card : ℝ) * (49 * C) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (M : ℝ) * (49 * C) := by
          refine mul_le_mul_of_nonneg_right ?_ (by positivity)
          exact_mod_cast hcard j
      _ = 49 * (M : ℝ) * C := by ring

/-- **One hypothesis left.**  Given the commutator gate for the symbol `(deg+1)²`, the second
quantization of the non-abelian gauge-fixed Yang–Mills Hamiltonian is essentially self-adjoint
on the finite-occupation core.  The row and column gates are supplied by
`ymHermCol_row_col_gates`; the commutator gate is the open input (see the module header). -/
theorem ymHermCol_essentiallySelfAdjointOn_core_of_commBound (e : ℕ ≃ (Fin 99 →₀ ℕ))
    (fabc : Fin 8 → Fin 8 → Fin 8 → ℝ) {B : ℝ}
    (hBg : WCommBound (ymW e) (ymHermCol e fabc) B) :
    EssentiallySelfAdjointOn (lpFiniteModes Conf) (dGammaOp (ymHermCol e fabc)) := by
  obtain ⟨K, hK0, hrow, hcolg⟩ := ymHermCol_row_col_gates e fabc
  exact dGamma_essentiallySelfAdjointOn_core_w (ymW_one_le e) (isHermCol_ymHermCol e fabc)
    hrow hcolg hK0 hBg

end

end BookProof.YangMillsWeightedGates
