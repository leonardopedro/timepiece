import Mathlib
import PnpProof.Foundations
import PnpProof.Counting

/-!
# Part 4: The model — Tier B definitions and lemmas

Dyadic discretization, the inverse-transform verifier, machine computation of a
selection function, and the concrete atomless prior on selection functions.
-/

open MeasureTheory Set
open scoped BigOperators ENNReal

noncomputable section

namespace PnpProof

/-- The compact parameter / sample space `[0,1]` as a subtype. -/
abbrev K := ↥(Icc (0:ℝ) 1)

instance : MeasurableSpace (C(K, ℝ)) := borel _
instance : BorelSpace (C(K, ℝ)) := ⟨rfl⟩

/-! ### M1. Dyadic discretization -/

/-- The `i`-th dyadic interval at resolution `k`. -/
def dyadic (k : ℕ) (i : Fin (2^k)) : Set ℝ := Ico ((i : ℝ) / 2^k) (((i : ℝ) + 1) / 2^k)

/-- The dyadic index of `x` at resolution `k` (clamped into `Fin (2^k)`). -/
def dyadicIndex (k : ℕ) (x : ℝ) : Fin (2^k) :=
  ⟨min (⌊2^k * x⌋).toNat (2^k - 1), by
    have h : 0 < 2^k := by positivity
    omega⟩

theorem dyadic_disjoint (k : ℕ) :
    Pairwise (fun i j => Disjoint (dyadic k i) (dyadic k j)) := by
  intro i j hij; rw [ Set.disjoint_left ] ; intro x hx hx'; simp_all +decide [ dyadic ] ;
  exact hij ( Fin.ext <| Nat.le_antisymm ( Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; ring_nf at *; nlinarith [ inv_pos.mpr ( show ( 0 : ℝ ) < 2 ^ k by positivity ) ] ) ( Nat.le_of_lt_succ <| by rw [ ← @Nat.cast_lt ℝ ] ; push_cast; ring_nf at *; nlinarith [ inv_pos.mpr ( show ( 0 : ℝ ) < 2 ^ k by positivity ) ] ) )

theorem mem_dyadic_index {k : ℕ} {x : ℝ} (hx : x ∈ Ico (0:ℝ) 1) :
    x ∈ dyadic k (dyadicIndex k x) := by
  constructor <;> norm_num [ dyadicIndex ] at *;
  · rw [ div_le_iff₀ ] <;> norm_cast <;> norm_num;
    exact Or.inl ⟨ by linarith [ Int.floor_le ( 2 ^ k * x ) ], hx.1 ⟩;
  · rw [ lt_div_iff₀ ] <;> norm_cast <;> norm_num [ Nat.pow_succ' ] at *;
    rw [ min_def, max_def ] ; split_ifs <;> nlinarith [ Int.floor_le ( 2 ^ k * x ), Int.lt_floor_add_one ( 2 ^ k * x ), show ( 2 ^ k : ℝ ) ≥ 1 by exact one_le_pow₀ one_le_two ] ;

theorem dyadic_width {k : ℕ} {i : Fin (2^k)} {x y : ℝ}
    (hx : x ∈ dyadic k i) (hy : y ∈ dyadic k i) : |x - y| < (2^k : ℝ)⁻¹ := by
  norm_num [ abs_lt, dyadic ] at *;
  grind

/-! ### M2. The inverse-transform verifier -/

/-- The verification predicate: at resolution `k`, the candidate output interval
    `i` is accepted for sample `u` iff the conditional CDF `G` crosses `u` inside
    that interval. -/
def verify (G : ℝ → ℝ) (u : ℝ) (k : ℕ) (i : Fin (2^k)) : Prop :=
  G ((i : ℝ) / 2^k) ≤ u ∧ u ≤ G (((i : ℝ) + 1) / 2^k)

/-
If `G` is monotone with `G 0 ≤ u ≤ G 1`, some interval verifies.
-/
theorem verify_exists (G : ℝ → ℝ) (hG : Monotone G) (u : ℝ) (k : ℕ)
    (h0 : G 0 ≤ u) (h1 : u ≤ G 1) : ∃ i : Fin (2^k), verify G u k i := by
  revert u h0 h1;
  induction' k with k ih;
  · exact fun u hu₀ hu₁ => ⟨ ⟨ 0, by norm_num ⟩, ⟨ by simpa using hu₀, by simpa using hu₁ ⟩ ⟩;
  · intro u hu₀ hu₁
    obtain ⟨i, hi⟩ := ih u hu₀ hu₁;
    -- Consider the two subintervals of the verified interval at resolution `k`.
    by_cases h_case : u ≤ G ((i.val + 1 / 2 : ℝ) / 2^k);
    · refine' ⟨ ⟨ i.val * 2, _ ⟩, _, _ ⟩ <;> norm_num at *;
      · rw [ pow_succ' ] ; linarith [ Fin.is_lt i ];
      · convert hi.1 using 1 ; ring;
      · convert h_case using 2 ; ring;
    · refine' ⟨ ⟨ i * 2 + 1, _ ⟩, _, _ ⟩ <;> norm_num [ verify ] at *;
      · rw [ pow_succ' ] ; linarith [ Fin.is_lt i ];
      · grind;
      · convert hi.2 using 1 ; ring

/-! ### M3. Machine computation of a selection function -/

/-- A code `c` computes the continuous selection `g` on `[0,1)` if at every
    resolution `k` it maps `(k, dyadic index of x)` to the dyadic index of
    `g x`, for every `x` with `x.val ∈ [0,1)`. -/
def ComputesSelection (c : Nat.Partrec.Code) (g : C(K, ℝ)) : Prop :=
  ∀ k : ℕ, ∀ x : K, (x : ℝ) ∈ Ico (0:ℝ) 1 → g x ∈ Ico (0:ℝ) 1 ∧
    c.eval (Nat.pair k (dyadicIndex k (x : ℝ)))
      = Part.some (dyadicIndex k (g x))

theorem computesSelection_unique (c : Nat.Partrec.Code) (g h : C(K, ℝ))
    (hg : ComputesSelection c g) (hh : ComputesSelection c h) : g = h := by
  apply ContinuousMap.ext
  intro x
  by_cases hx : x.val ∈ Set.Ico (0 : ℝ) 1;
  · have h_eq : ∀ k : ℕ, dyadicIndex k (g x) = dyadicIndex k (h x) := by
      intro k
      have := hg k x hx
      have := hh k x hx
      aesop;
    have h_eq : ∀ k : ℕ, |g x - h x| < (2^k : ℝ)⁻¹ := by
      intro k
      have h_eq : g x ∈ dyadic k (dyadicIndex k (g x)) ∧ h x ∈ dyadic k (dyadicIndex k (h x)) := by
        exact ⟨ mem_dyadic_index ( hg k x hx |>.1 ), mem_dyadic_index ( hh k x hx |>.1 ) ⟩;
      have := dyadic_width h_eq.1 ( by simpa [ ‹∀ k : ℕ, dyadicIndex k ( g x ) = dyadicIndex k ( h x ) › k ] using h_eq.2 ) ; aesop;
    exact sub_eq_zero.mp ( by simpa using le_antisymm ( le_of_tendsto_of_tendsto' tendsto_const_nhds ( tendsto_inv_atTop_zero.comp ( tendsto_pow_atTop_atTop_of_one_lt one_lt_two ) ) fun k => le_of_lt ( h_eq k ) ) ( abs_nonneg _ ) );
  · -- Since $x = 1$, we can use the fact that $g$ and $h$ are continuous on $K$ to conclude that $g(1) = h(1)$.
    have h_cont : Filter.Tendsto (fun x : K => g x) (nhdsWithin ⟨1, by norm_num⟩ {⟨1, by norm_num⟩}ᶜ) (nhds (g ⟨1, by norm_num⟩)) ∧ Filter.Tendsto (fun x : K => h x) (nhdsWithin ⟨1, by norm_num⟩ {⟨1, by norm_num⟩}ᶜ) (nhds (h ⟨1, by norm_num⟩)) := by
      exact ⟨ g.continuous.continuousWithinAt, h.continuous.continuousWithinAt ⟩;
    have h_eq : ∀ᶠ x in nhdsWithin ⟨1, by norm_num⟩ {⟨1, by norm_num⟩}ᶜ, g x = h x := by
      have h_eq : ∀ x : K, x.val ∈ Set.Ico (0 : ℝ) 1 → g x = h x := by
        intro x hx
        have h_eq : ∀ k : ℕ, dyadicIndex k (g x) = dyadicIndex k (h x) := by
          intro k
          have := hg k x hx
          have := hh k x hx
          aesop;
        have h_eq : ∀ k : ℕ, |g x - h x| < (2^k : ℝ)⁻¹ := by
          intro k
          have h_eq : g x ∈ dyadic k (dyadicIndex k (g x)) ∧ h x ∈ dyadic k (dyadicIndex k (h x)) := by
            exact ⟨ mem_dyadic_index ( hg k x hx |>.1 ), mem_dyadic_index ( hh k x hx |>.1 ) ⟩;
          grind +suggestions;
        exact sub_eq_zero.mp ( by simpa using le_antisymm ( le_of_tendsto_of_tendsto' tendsto_const_nhds ( tendsto_inv_atTop_zero.comp ( tendsto_pow_atTop_atTop_of_one_lt one_lt_two ) ) fun k => le_of_lt ( h_eq k ) ) ( abs_nonneg _ ) );
      rw [ eventually_nhdsWithin_iff ];
      rw [ Metric.eventually_nhds_iff ];
      grind +qlia;
    convert tendsto_nhds_unique h_cont.1 ( h_cont.2.congr' <| by filter_upwards [ h_eq ] with x hx; aesop ) using 1;
    · grind;
    · grind +qlia

theorem countable_computable_selections :
    {g : C(K, ℝ) | ∃ c, ComputesSelection c g}.Countable := by
  -- The set of computable functions is countable.
  have h_countable : Set.Countable {c : Nat.Partrec.Code | ∃ g : C(K, ℝ), ComputesSelection c g} := by
    exact Set.to_countable _;
  have h_inj : ∀ c : Nat.Partrec.Code, Set.Subsingleton {g : C(K, ℝ) | ComputesSelection c g} := by
    exact fun c => fun g hg h hh => computesSelection_unique c g h hg hh;
  exact Set.Countable.mono ( fun g hg => by aesop ) ( h_countable.biUnion fun c hc => Set.Subsingleton.countable ( h_inj c ) )

/-! ### M4. The prior: a concrete atomless measure on selection functions -/

/-- The selected output for parameter `t` and uniform sample `u`. -/
def select (t u : ℝ) : ℝ := u ^ (1 / (1 + t))

theorem select_continuous :
    Continuous (fun p : K × K => select (p.1 : ℝ) (p.2 : ℝ)) := by
  refine' Continuous.rpow _ _ _;
  · fun_prop;
  · exact Continuous.div continuous_const ( continuous_const.add <| continuous_subtype_val.comp continuous_fst ) fun p => by linarith [ p.1.2.1 ] ;
  · exact fun x => Or.inr ( one_div_pos.mpr ( by linarith [ x.1.2.1 ] ) )

theorem select_continuous_right (t : K) :
    Continuous (fun u : K => select (t : ℝ) (u : ℝ)) := by
  convert PnpProof.select_continuous.comp ( show Continuous fun u : K => ( t, u ) from continuous_const.prodMk continuous_id' ) using 1

/-- The selection functions as continuous maps on the sample space. -/
def selMap (t : K) : C(K, ℝ) :=
  ⟨fun u => select (t : ℝ) (u : ℝ), select_continuous_right t⟩

theorem selMap_continuous : Continuous selMap := by
  refine' ContinuousMap.continuous_of_continuous_uncurry _ _;
  convert PnpProof.select_continuous using 1

theorem selMap_injective : Function.Injective selMap := by
  intro t t' h_eq
  have h_exp : (1 / 2 : ℝ) ^ (1 / (1 + t.val)) = (1 / 2 : ℝ) ^ (1 / (1 + t'.val)) := by
    convert congr_arg ( fun f : C(K, ℝ) => f ⟨ 1 / 2, by norm_num ⟩ ) h_eq using 1
  have h_exp_eq : 1 / (1 + t.val) = 1 / (1 + t'.val) := by
    norm_num [ Real.rpow_def_of_pos ] at * ; aesop
  have h_t_eq : t.val = t'.val := by
    grind
  exact Subtype.ext h_t_eq

/-- The prior: pushforward of the uniform measure on `[0,1]` under `t ↦ selMap t`. -/
def prior : Measure (C(K, ℝ)) := (volume : Measure K).map selMap

instance prior_isProbability : IsProbabilityMeasure prior := by
  constructor;
  erw [ MeasureTheory.Measure.map_apply ] <;> norm_num [ selMap_continuous.measurable ]

theorem prior_atomless : ∀ g : C(K, ℝ), prior {g} = 0 := by
  unfold prior;
  intro g
  have h_preimage : (volume (selMap ⁻¹' {g})) = 0 := by
    exact Set.Subsingleton.measure_zero ( fun x hx y hy => by have := PnpProof.selMap_injective ( by aesop : selMap x = selMap y ) ; aesop ) _;
  rw [ MeasureTheory.Measure.map_apply ] <;> norm_num [ h_preimage, selMap_continuous.measurable ]

end PnpProof