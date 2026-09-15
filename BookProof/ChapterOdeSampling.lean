import Mathlib
import BookProof.ChapterShannonSampling
import BookProof.ChapterOdeUnitaryFlow

/-!
# Sampling a wave-function of the blow-up ODE at the points `x_n = -T/n`

Source: `book.tex`, chapter *"Resolution of the singularity of the ODE x'=x² when the
initial x has uncertainties"*, §*Resolution of the singularity using the uncertainties in x*:

> "Since the Hamiltonian differs from the translation in space by a change of variables
> `y → 1/x`, then using the Whittaker–Shannon interpolation (also called sinc interpolation)
> before the change of variables `y → 1/x`, we can completely define the wave-function in
> coordinate space through its values at discrete points in space `xₙ = Δ/n`, where `n` is an
> integer number (different from zero) and `Δ` is a constant proportional to the maximum
> energy."

`BookProof.ChapterOdeUnitaryFlow` proves the first half of that sentence — the time-evolution
of the chapter *is* the translation group in the chart `w = -1/x` (`odeKoop_chartW`) — and
`BookProof.ChapterShannonSampling` proves the sampling theorem used in the second half.  This
file puts the two together, which is exactly the chapter's conclusion: **a wave-function whose
chart transform is band-limited is completely determined by its values at the discrete points
`xₙ = -T/n`, `n` a nonzero integer** (the energy bound enters as the bandwidth `T`, the book's
`Δ`, and the points accumulate at `0`, i.e. at `x = ∞` before the change of variables).

* `chartW_sample` — the sample of the chart transform at the lattice point `n/T` is
  `(T/n) · ψ (-T/n)`: sampling the chart at `n/T` *is* evaluating the wave-function at `-T/n`;
* **`eq_of_sample_eq_on_lattice`** — two wave-functions with band-limited chart transforms and
  the same values at every `-T/n` (`n ≠ 0`) agree at every nonzero point.

* **`hasSum_wavefunction_interpolation`** — the explicit cardinal-sine series recovering the
  wave-function at every nonzero point from those values.

Everything is `sorry`-free and uses only the standard axioms.
-/

namespace BookProof.ChapterOdeSampling

open BookProof.ChapterShannonSampling BookProof.OdeUnitaryFlow
open MeasureTheory AddCircle

variable {T : ℝ} [hT : Fact (0 < T)]

/-- Sampling the chart transform at `n/T` is evaluating the wave-function at `-T/n`. -/
theorem chartW_sample (ψ : ℝ → ℂ) {n : ℤ} (hn : n ≠ 0) :
    chartW ψ ((n : ℝ) / T) = ((T / n : ℝ) : ℂ) * ψ (-(T / n)) := by
  have hT0 : (0 : ℝ) < T := hT.out
  have hn' : (n : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hn
  have hinv : invMap ((n : ℝ) / T) = -(T / n) := by
    simp only [invMap]
    field_simp
  rw [chartW, hinv]
  congr 1
  push_cast
  field_simp

/-- At the origin of the lattice the chart transform vanishes, whatever the wave-function:
the point `x = 0` of the chart corresponds to the infinite coordinate. -/
theorem chartW_zero (ψ : ℝ → ℂ) : chartW ψ 0 = 0 := by simp [chartW]

/-- **The wave-function of the blow-up ODE is determined by its values at `xₙ = -T/n`.**

If the chart transforms `w ↦ (Wψ)(w) = ψ(-1/w)/w` of two wave-functions are band-limited with
bandwidth `T` — the book's energy bound — and the two wave-functions agree at every point
`-T/n` with `n` a nonzero integer, then they agree at every nonzero point. -/
theorem eq_of_sample_eq_on_lattice (ψ φ : ℝ → ℂ)
    (F G : Lp ℂ 2 (haarAddCircle (T := T)))
    (hψ : ∀ w : ℝ, chartW ψ w = bandSignal (T := T) (F : AddCircle T → ℂ) w)
    (hφ : ∀ w : ℝ, chartW φ w = bandSignal (T := T) (G : AddCircle T → ℂ) w)
    (hsample : ∀ n : ℤ, n ≠ 0 → ψ (-(T / n)) = φ (-(T / n)))
    {x : ℝ} (hx : x ≠ 0) : ψ x = φ x := by
  have hT0 : (0 : ℝ) < T := hT.out
  -- the two spectra have the same samples on the whole lattice
  have hlattice : ∀ n : ℤ, bandSignal (T := T) (F : AddCircle T → ℂ) ((n : ℝ) / T)
      = bandSignal (T := T) (G : AddCircle T → ℂ) ((n : ℝ) / T) := by
    intro n
    rcases eq_or_ne n 0 with rfl | hn
    · rw [← hψ, ← hφ]
      simp [chartW_zero]
    · rw [← hψ, ← hφ, chartW_sample ψ hn, chartW_sample φ hn, hsample n hn]
  -- hence the two band-limited chart transforms agree everywhere
  have hall : ∀ w : ℝ, chartW ψ w = chartW φ w := by
    intro w
    rw [hψ, hφ]
    exact bandSignal_eq_of_samples_eq F G hlattice w
  -- and the chart is invertible away from the origin
  have hw : invMap x ≠ 0 := invMap_ne_zero hx
  have := hall (invMap x)
  rw [chartW, chartW, invMap_invMap hx] at this
  have hwc : ((invMap x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw
  field_simp at this
  exact this

/-- **The interpolation formula for the wave-function itself.**  With the chart transform
band-limited of bandwidth `T`, the wave-function is recovered at every nonzero point from its
values at the lattice `xₙ = -T/n` by the cardinal-sine series of the chapter. -/
theorem hasSum_wavefunction_interpolation (ψ : ℝ → ℂ) (F : Lp ℂ 2 (haarAddCircle (T := T)))
    (hψ : ∀ w : ℝ, chartW ψ w = bandSignal (T := T) (F : AddCircle T → ℂ) w)
    {x : ℝ} (hx : x ≠ 0) :
    HasSum (fun n : ℤ => if n = 0 then 0 else
        ((-(T / ((n : ℝ) * x)) : ℝ) : ℂ) * ψ (-(T / n)) * (sinc (T * (-1 / x) - n) : ℝ))
      (ψ x) := by
  have hT0 : (0 : ℝ) < T := hT.out
  have hw : invMap x ≠ 0 := invMap_ne_zero hx
  have hwc : ((invMap x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hw
  have hbase := (bandSignal_hasSum_sinc (T := T) F (invMap x)).mul_left ((invMap x : ℝ) : ℂ)
  have htotal : ((invMap x : ℝ) : ℂ) * bandSignal (T := T) (F : AddCircle T → ℂ) (invMap x)
      = ψ x := by
    rw [← hψ, chartW, invMap_invMap hx, ← mul_assoc, mul_inv_cancel₀ hwc, one_mul]
  rw [htotal] at hbase
  refine hbase.congr_fun fun n => ?_
  rcases eq_or_ne n 0 with rfl | hn
  · simp [← hψ, chartW_zero]
  · rw [if_neg hn, ← hψ, chartW_sample ψ hn]
    have hxc : ((x : ℝ) : ℂ) ≠ 0 := by exact_mod_cast hx
    have hnc : ((n : ℝ) : ℂ) ≠ 0 := by
      exact_mod_cast (Int.cast_ne_zero (α := ℝ)).mpr hn
    have hinv : ((invMap x : ℝ) : ℂ) = -1 / (x : ℂ) := by
      simp [invMap]
    have harg : T * invMap x - (n : ℝ) = T * (-1 / x) - n := by
      simp [invMap]
    rw [harg, hinv]
    push_cast
    field_simp

end BookProof.ChapterOdeSampling
