import BookProof.Ultrafinitism.ChapterUltrafinitistTensor
import Mathlib.LinearAlgebra.Matrix.Symmetric
import Mathlib.Data.Matrix.Mul

/-!
# Chapter GramPolyDecision — Computable Polynomial-Time Gram Decidability

In the classical Solovay–Kopperman theory (`Book/SolovayTensor.lean`), the
pure Hilbert-space fragment reduces to real closed fields (Tarski / Solovay–Arthan–
Harrison), which has doubly exponential complexity in quantifier alternations.

In the ultrafinitist theory `U-SMK`, a finite-channel rational Gram query over a
residual tail of coordinate capacity `R` reduces to deciding:
`G ⪰ 0` AND `rank(G) ≤ R` (`HasBoundedGramFactor G R`).

This module implements a **100% computable** `O(m³)` rational Schur-elimination
decision procedure `decideGram G R` and proves both its **soundness**
(`decideGram_sound`) and its **completeness** (`decideGram_complete`) for every
rational symmetric matrix `G`, with zero `noncomputable`, zero `sorry`, and zero
`native_decide`.
-/

namespace BookProof.Ultrafinitism.ChapterGramPolyDecision

open scoped BigOperators Matrix

/-! ## 1. Rational quadratic forms and bounded-rank Gram factorizations -/

/-- Rational quadratic form `vᵀ G v` on `Fin m → ℚ`. -/
def ratQuad {m : ℕ} (G : Matrix (Fin m) (Fin m) ℚ) (v : Fin m → ℚ) : ℚ :=
  ∑ i : Fin m, ∑ j : Fin m, v i * G i j * v j

/-- Positive semidefiniteness of a rational matrix. -/
def IsRatPSD {m : ℕ} (G : Matrix (Fin m) (Fin m) ℚ) : Prop :=
  ∀ v : Fin m → ℚ, 0 ≤ ratQuad G v

/-- A rational matrix admits an exact positive-diagonal factorization of rank `≤ R`
(the exact condition for realizability inside a finite capacity `R` subspace). -/
def HasBoundedGramFactor {m : ℕ} (G : Matrix (Fin m) (Fin m) ℚ) (R : ℕ) : Prop :=
  ∃ (k : ℕ), k ≤ R ∧ ∃ (d : Fin k → ℚ) (L : Matrix (Fin k) (Fin m) ℚ),
    (∀ r, 0 < d r) ∧ ∀ i j, G i j = ∑ r : Fin k, d r * L r i * L r j

theorem isRatPSD_of_hasBoundedGramFactor {m R : ℕ} {G : Matrix (Fin m) (Fin m) ℚ}
    (h : HasBoundedGramFactor G R) : IsRatPSD G := by
  rcases h with ⟨k, _, d, L, hd, hL⟩
  intro v
  unfold ratQuad
  have hexp : (∑ i : Fin m, ∑ j : Fin m, v i * G i j * v j) =
      ∑ r : Fin k, d r * (∑ i : Fin m, L r i * v i) ^ 2 := by
    simp_rw [hL, Finset.mul_sum, Finset.sum_mul]
    have hstep1 : (∑ i : Fin m, ∑ j : Fin m, ∑ r : Fin k, v i * (d r * L r i * L r j) * v j) =
        ∑ i : Fin m, ∑ r : Fin k, ∑ j : Fin m, v i * (d r * L r i * L r j) * v j :=
      Finset.sum_congr rfl fun _ _ => Finset.sum_comm
    rw [hstep1, Finset.sum_comm]
    refine Finset.sum_congr rfl fun r _ => ?_
    rw [sq, Finset.sum_mul]
    simp_rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  rw [hexp]
  exact Finset.sum_nonneg fun r _ => mul_nonneg (hd r).le (sq_nonneg _)

theorem symm_of_hasBoundedGramFactor {m R : ℕ} {G : Matrix (Fin m) (Fin m) ℚ}
    (h : HasBoundedGramFactor G R) : Gᵀ = G := by
  rcases h with ⟨k, _, d, L, _, hL⟩
  ext i j
  simp only [Matrix.transpose_apply, hL]
  refine Finset.sum_congr rfl fun r _ => by ring

/-! ## 2. Rational Schur complement and quadratic decomposition -/

/-- Rational Schur complement of `G` after eliminating pivot `p`. -/
def schurComp {n : ℕ} (G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ) (p : Fin (n + 1)) :
    Matrix (Fin n) (Fin n) ℚ :=
  fun a b =>
    G (p.succAbove a) (p.succAbove b) -
      G (p.succAbove a) p * G p (p.succAbove b) / G p p

theorem schurComp_symm {n : ℕ} {G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ}
    (hG : Gᵀ = G) (p : Fin (n + 1)) : (schurComp G p)ᵀ = schurComp G p := by
  ext a b
  have h1 : G (p.succAbove b) (p.succAbove a) = G (p.succAbove a) (p.succAbove b) := by
    simpa using congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ =>
      M (p.succAbove a) (p.succAbove b)) hG
  have h2 : G (p.succAbove b) p = G p (p.succAbove b) := by
    simpa using congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ =>
      M p (p.succAbove b)) hG
  have h3 : G p (p.succAbove a) = G (p.succAbove a) p := by
    simpa using congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ =>
      M (p.succAbove a) p) hG
  simp only [Matrix.transpose_apply, schurComp, h1, h2, h3]
  ring

private theorem sum_fin_succAbove {n : ℕ} (p : Fin (n + 1)) (f : Fin (n + 1) → ℚ) :
    (∑ i : Fin (n + 1), f i) = f p + ∑ a : Fin n, f (p.succAbove a) := by
  have h := Fin.sum_univ_succAbove f p
  exact h

/-- Quadratic form Schur decomposition at a nonzero diagonal pivot `G p p ≠ 0`. -/
theorem ratQuad_schur_decomp {n : ℕ} {G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ}
    (hG : Gᵀ = G) (p : Fin (n + 1)) (hp : G p p ≠ 0) (v : Fin (n + 1) → ℚ) :
    ratQuad G v =
      G p p * (v p + (∑ a : Fin n, G p (p.succAbove a) * v (p.succAbove a)) / G p p) ^ 2 +
        ratQuad (schurComp G p) (fun a => v (p.succAbove a)) := by
  unfold ratQuad schurComp
  have hsym : ∀ a : Fin n, G (p.succAbove a) p = G p (p.succAbove a) := by
    intro a
    have hc := congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ =>
      M (p.succAbove a) p) hG
    simpa using hc.symm
  have hexp : (∑ i : Fin (n + 1), ∑ j : Fin (n + 1), v i * G i j * v j) =
      v p * G p p * v p +
        2 * v p * (∑ a : Fin n, G p (p.succAbove a) * v (p.succAbove a)) +
        ∑ a : Fin n, ∑ b : Fin n,
          v (p.succAbove a) * G (p.succAbove a) (p.succAbove b) * v (p.succAbove b) := by
    rw [sum_fin_succAbove p]
    simp_rw [sum_fin_succAbove p]
    rw [Finset.sum_add_distrib]
    have hcross : (∑ a : Fin n, v (p.succAbove a) * G (p.succAbove a) p * v p) =
        ∑ a : Fin n, v p * G p (p.succAbove a) * v (p.succAbove a) := by
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [hsym a]; ring
    rw [hcross]
    have h2 : (∑ a : Fin n, v p * G p (p.succAbove a) * v (p.succAbove a)) =
        v p * ∑ a : Fin n, G p (p.succAbove a) * v (p.succAbove a) := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => by ring
    rw [h2]
    ring
  have hsch : (∑ a : Fin n, ∑ b : Fin n,
      v (p.succAbove a) *
        (G (p.succAbove a) (p.succAbove b) -
          G (p.succAbove a) p * G p (p.succAbove b) / G p p) *
        v (p.succAbove b)) =
      (∑ a : Fin n, ∑ b : Fin n,
        v (p.succAbove a) * G (p.succAbove a) (p.succAbove b) * v (p.succAbove b)) -
        (∑ a : Fin n, G p (p.succAbove a) * v (p.succAbove a)) ^ 2 / G p p := by
    have hterm : ∀ a b : Fin n,
        v (p.succAbove a) *
          (G (p.succAbove a) (p.succAbove b) -
            G (p.succAbove a) p * G p (p.succAbove b) / G p p) *
          v (p.succAbove b) =
        v (p.succAbove a) * G (p.succAbove a) (p.succAbove b) * v (p.succAbove b) -
          (G p (p.succAbove a) * v (p.succAbove a)) *
            (G p (p.succAbove b) * v (p.succAbove b)) / G p p := by
      intro a b
      rw [hsym a]
      ring
    simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.sum_div, sq, Finset.sum_mul,
      Finset.mul_sum]
  rw [hexp, hsch]
  field_simp [hp]
  ring

/-! ## 3. Computable Schur-elimination decision procedure -/

/-- Find the first strictly positive diagonal entry, if any. -/
def findPosDiag {m : ℕ} (G : Matrix (Fin m) (Fin m) ℚ) : Option (Fin m) :=
  (List.finRange m).find? (fun i => decide (0 < G i i))

/-- Test whether any diagonal entry is strictly negative. -/
def hasNegDiag {m : ℕ} (G : Matrix (Fin m) (Fin m) ℚ) : Bool :=
  (List.finRange m).any (fun i => decide (G i i < 0))

/-- Test whether every entry of `G` is zero. -/
def isZeroMatrix {m : ℕ} (G : Matrix (Fin m) (Fin m) ℚ) : Bool :=
  (List.finRange m).all (fun i =>
    (List.finRange m).all (fun j => decide (G i j = 0)))

/-- **Polynomial-time (`O(m³)`) rational decision procedure** for `G ⪰ 0 ∧ rank(G) ≤ R`. -/
def decideGram : ∀ {m : ℕ}, Matrix (Fin m) (Fin m) ℚ → ℕ → Bool
  | 0, _, _ => true
  | _ + 1, G, R =>
    if hasNegDiag G then false
    else match findPosDiag G with
      | none => isZeroMatrix G
      | some p =>
        match R with
        | 0 => false
        | R' + 1 => decideGram (schurComp G p) R'

private theorem findPosDiag_some {m : ℕ} {G : Matrix (Fin m) (Fin m) ℚ} {p : Fin m}
    (hp : findPosDiag G = some p) : 0 < G p p := by
  have h := List.find?_some hp
  simpa using h

private theorem findPosDiag_none {m : ℕ} {G : Matrix (Fin m) (Fin m) ℚ}
    (hnone : findPosDiag G = none) (i : Fin m) : ¬ 0 < G i i := by
  have h := List.find?_eq_none.mp hnone i (List.mem_finRange i)
  simpa using h

private theorem hasNegDiag_false {m : ℕ} {G : Matrix (Fin m) (Fin m) ℚ}
    (hf : hasNegDiag G = false) (i : Fin m) : 0 ≤ G i i := by
  have h : ¬ (G i i < 0) := by
    have ha := (List.any_eq_false.mp hf) i (List.mem_finRange i)
    simpa using ha
  linarith

private theorem hasNegDiag_eq_false_of_nonneg {m : ℕ} {G : Matrix (Fin m) (Fin m) ℚ}
    (h : ∀ i : Fin m, 0 ≤ G i i) : hasNegDiag G = false := by
  apply List.any_eq_false.mpr
  intro i _
  simp [not_lt.mpr (h i)]

private theorem isZeroMatrix_true_iff {m : ℕ} {G : Matrix (Fin m) (Fin m) ℚ} :
    isZeroMatrix G = true ↔ ∀ i j : Fin m, G i j = 0 := by
  unfold isZeroMatrix
  simp [List.all_eq_true]

/-! ## 4. Soundness of `decideGram` -/

/-- **Soundness:** if `G` is symmetric and `decideGram G R = true`, then `G` admits an
exact positive-diagonal factorization of rank `≤ R` (and in particular `IsRatPSD G`). -/
theorem decideGram_sound : ∀ {m : ℕ} {G : Matrix (Fin m) (Fin m) ℚ} {R : ℕ},
    Gᵀ = G → decideGram G R = true → HasBoundedGramFactor G R
  | 0, G, R, _, _ => by
    refine ⟨0, Nat.zero_le R, Fin.elim0, fun r => Fin.elim0 r, fun r => Fin.elim0 r, ?_⟩
    intro i
    exact Fin.elim0 i
  | n + 1, G, R, hG, hdec => by
    unfold decideGram at hdec
    by_cases hneg : hasNegDiag G = true
    · simp [hneg] at hdec
    · have hneg' : hasNegDiag G = false := Bool.eq_false_iff.mpr hneg
      simp only [hneg', Bool.false_eq_true, ↓reduceIte] at hdec
      cases hfind : findPosDiag G with
      | none =>
        simp only [hfind] at hdec
        have hzero := isZeroMatrix_true_iff.mp hdec
        refine ⟨0, Nat.zero_le R, Fin.elim0, fun r => Fin.elim0 r, fun r => Fin.elim0 r, ?_⟩
        intro i j
        simp [hzero i j]
      | some p =>
        simp only [hfind] at hdec
        cases R with
        | zero => simp at hdec
        | succ R' =>
          simp only at hdec
          have hp : 0 < G p p := findPosDiag_some hfind
          have hpne : G p p ≠ 0 := hp.ne'
          obtain ⟨k, hk, d, L, hd, hL⟩ :=
            decideGram_sound (schurComp_symm hG p) hdec
          refine ⟨k + 1, Nat.succ_le_succ hk, Fin.cons (G p p) d,
            Fin.cons (fun j => G p j / G p p)
              (fun r => @Fin.insertNth _ (fun _ => ℚ) p 0 (L r)), ?_, ?_⟩
          · intro r
            refine Fin.cases hp hd r
          · intro i j
            rw [Fin.sum_univ_succ]
            simp only [Fin.cons_zero, Fin.cons_succ]
            rcases eq_or_ne i p with hip | hi
            · rw [hip]
              rcases eq_or_ne j p with hjp | hj
              · rw [hjp]
                simp [hpne]
              · obtain ⟨b, rfl⟩ := Fin.exists_succAbove_eq hj
                have hz : ∀ x : Fin k,
                    @Fin.insertNth _ (fun _ => ℚ) p 0 (L x) p = 0 := fun x =>
                  @Fin.insertNth_apply_same _ (fun _ => ℚ) p 0 (L x)
                simp only [hz, mul_zero, zero_mul, Finset.sum_const_zero, add_zero]
                field_simp [hpne]
            · obtain ⟨a, rfl⟩ := Fin.exists_succAbove_eq hi
              rcases eq_or_ne j p with hjp | hj
              · rw [hjp]
                have hsym : G p (p.succAbove a) = G (p.succAbove a) p := by
                  simpa using congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ =>
                    M (p.succAbove a) p) hG
                have hz : ∀ x : Fin k,
                    @Fin.insertNth _ (fun _ => ℚ) p 0 (L x) p = 0 := fun x =>
                  @Fin.insertNth_apply_same _ (fun _ => ℚ) p 0 (L x)
                simp only [hz, mul_zero, Finset.sum_const_zero, add_zero, hsym]
                field_simp [hpne]
              · obtain ⟨b, rfl⟩ := Fin.exists_succAbove_eq hj
                have ha : ∀ x : Fin k,
                    @Fin.insertNth _ (fun _ => ℚ) p 0 (L x) (p.succAbove a) = L x a := fun x =>
                  @Fin.insertNth_apply_succAbove _ (fun _ => ℚ) p 0 (L x) a
                have hb : ∀ x : Fin k,
                    @Fin.insertNth _ (fun _ => ℚ) p 0 (L x) (p.succAbove b) = L x b := fun x =>
                  @Fin.insertNth_apply_succAbove _ (fun _ => ℚ) p 0 (L x) b
                simp_rw [ha, hb]
                have hsym : G p (p.succAbove a) = G (p.succAbove a) p := by
                  simpa using congrArg (fun M : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ =>
                    M (p.succAbove a) p) hG
                rw [← hL a b, schurComp, hsym]
                field_simp [hpne]
                ring

theorem isRatPSD_of_decideGram {m R : ℕ} {G : Matrix (Fin m) (Fin m) ℚ}
    (hG : Gᵀ = G) (h : decideGram G R = true) : IsRatPSD G :=
  isRatPSD_of_hasBoundedGramFactor (decideGram_sound hG h)

/-! ## 5. Elementary rational rank-reduction and completeness of `decideGram` -/

private def wDot {k : ℕ} (d x y : Fin k → ℚ) : ℚ :=
  ∑ r : Fin k, d r * x r * y r

private def rDot {k : ℕ} (x y : Fin k → ℚ) : ℚ :=
  ∑ r : Fin k, x r * y r

private theorem wDot_symm {k : ℕ} (d x y : Fin k → ℚ) : wDot d x y = wDot d y x := by
  refine Finset.sum_congr rfl fun r _ => by ring

private theorem wDot_self_pos {k : ℕ} {d : Fin k → ℚ} (hd : ∀ r, 0 < d r)
    {w : Fin k → ℚ} (hw : w ≠ 0) : 0 < wDot d w w := by
  have hnonneg : ∀ r : Fin k, 0 ≤ d r * w r * w r := fun r => by
    have : d r * w r * w r = d r * (w r) ^ 2 := by ring
    rw [this]
    exact mul_nonneg (hd r).le (sq_nonneg _)
  have hex : ∃ r₀ : Fin k, w r₀ ≠ 0 := by
    by_contra h
    push_neg at h
    exact hw (funext h)
  obtain ⟨r₀, hr₀⟩ := hex
  have hpos : 0 < d r₀ * w r₀ * w r₀ := by
    have : d r₀ * w r₀ * w r₀ = d r₀ * (w r₀) ^ 2 := by ring
    rw [this]
    exact mul_pos (hd r₀) (sq_pos_of_ne_zero hr₀)
  exact Finset.sum_pos' (fun r _ => hnonneg r) ⟨r₀, Finset.mem_univ r₀, hpos⟩

private theorem wDot_succ {m : ℕ} (d x y : Fin (m + 1) → ℚ) :
    wDot d x y = d 0 * x 0 * y 0 + wDot (Fin.tail d) (Fin.tail x) (Fin.tail y) := by
  unfold wDot
  rw [Fin.sum_univ_succ]
  rfl

private theorem rDot_succ {m : ℕ} (x y : Fin (m + 1) → ℚ) :
    rDot x y = x 0 * y 0 + rDot (Fin.tail x) (Fin.tail y) := by
  unfold rDot
  rw [Fin.sum_univ_succ]
  rfl

private def PPerp (k : ℕ) : Prop :=
  ∀ (d : Fin k → ℚ), (∀ r, 0 < d r) → ∀ (w : Fin k → ℚ), w ≠ 0 →
    ∃ (d' : Fin (k - 1) → ℚ) (φ : Fin (k - 1) → Fin k → ℚ),
      (∀ r, 0 < d' r) ∧
        ∀ x y : Fin k → ℚ, wDot d w x = 0 → wDot d w y = 0 →
          wDot d x y = ∑ r : Fin (k - 1), d' r * rDot (φ r) x * rDot (φ r) y

private def PRank1 (k : ℕ) : Prop :=
  ∀ (d : Fin k → ℚ), (∀ r, 0 < d r) → ∀ (α : ℚ), 0 ≤ α → ∀ (w : Fin k → ℚ),
    ∃ (d' : Fin k → ℚ) (φ : Fin k → Fin k → ℚ),
      (∀ r, 0 < d' r) ∧
        ∀ x y : Fin k → ℚ,
          wDot d x y + α * wDot d w x * wDot d w y =
            ∑ r : Fin k, d' r * rDot (φ r) x * rDot (φ r) y

private theorem perp_and_rank1 : ∀ k : ℕ, PPerp k ∧ PRank1 k
  | 0 => by
    constructor
    · intro d _ w hw
      exact False.elim (hw (Subsingleton.elim w 0))
    · intro d _ α _ w
      refine ⟨Fin.elim0, fun r => Fin.elim0 r, fun r => Fin.elim0 r, ?_⟩
      intro x y
      simp [wDot]
  | m + 1 => by
    obtain ⟨ih_perp, ih_rank1⟩ := perp_and_rank1 m
    have hperp : PPerp (m + 1) := by
      intro d hd w hw
      by_cases hw0 : w 0 = 0
      · have htail_ne : Fin.tail w ≠ 0 := by
          intro h
          apply hw
          ext i
          refine Fin.cases hw0 (fun j => ?_) i
          exact congrFun h j
        have hmpos : 0 < m := by
          by_contra hm0
          have hm : m = 0 := by omega
          subst hm
          exact htail_ne (Subsingleton.elim _ _)
        obtain ⟨d'', φ'', hd'', hφ''⟩ :=
          ih_perp (Fin.tail d) (fun j => hd j.succ) (Fin.tail w) htail_ne
        let e : Fin (m - 1 + 1) ≃ Fin m := finCongr (by omega)
        let dCons : Fin (m - 1 + 1) → ℚ := Fin.cons (d 0) d''
        let φCons : Fin (m - 1 + 1) → Fin (m + 1) → ℚ :=
          Fin.cons (Pi.single (0 : Fin (m + 1)) 1) (fun s => Fin.cons 0 (φ'' s))
        let d' : Fin ((m + 1) - 1) → ℚ := fun r => dCons (e.symm r)
        let φ : Fin ((m + 1) - 1) → Fin (m + 1) → ℚ := fun r => φCons (e.symm r)
        refine ⟨d', φ, ?_, ?_⟩
        · intro r
          exact Fin.cases (motive := fun s => 0 < dCons s) (hd 0) hd'' (e.symm r)
        · intro x y hx hy
          have hx' : wDot (Fin.tail d) (Fin.tail w) (Fin.tail x) = 0 := by
            simpa [wDot_succ, hw0] using hx
          have hy' : wDot (Fin.tail d) (Fin.tail w) (Fin.tail y) = 0 := by
            simpa [wDot_succ, hw0] using hy
          have hsub := hφ'' (Fin.tail x) (Fin.tail y) hx' hy'
          rw [wDot_succ, hsub]
          have hreidx : (∑ r : Fin m, d' r * rDot (φ r) x * rDot (φ r) y) =
              ∑ s : Fin (m - 1 + 1), dCons s * rDot (φCons s) x * rDot (φCons s) y :=
            (Fintype.sum_equiv e.symm _ _ (fun _ => rfl))
          change d 0 * x 0 * y 0 +
              ∑ t : Fin (m - 1), d'' t * rDot (φ'' t) (Fin.tail x) * rDot (φ'' t) (Fin.tail y) =
              ∑ r : Fin m, d' r * rDot (φ r) x * rDot (φ r) y
          rw [hreidx, Fin.sum_univ_succ]
          have h0x : rDot (φCons 0) x = x 0 := by
            change rDot (Pi.single (0 : Fin (m + 1)) 1) x = x 0
            simp [rDot, Pi.single_apply]
          have h0y : rDot (φCons 0) y = y 0 := by
            change rDot (Pi.single (0 : Fin (m + 1)) 1) y = y 0
            simp [rDot, Pi.single_apply]
          have htx : ∀ t : Fin (m - 1),
              rDot (φCons t.succ) x = rDot (φ'' t) (Fin.tail x) := by
            intro t
            change rDot (Fin.cons 0 (φ'' t)) x = _
            rw [rDot_succ]; simp
          have hty : ∀ t : Fin (m - 1),
              rDot (φCons t.succ) y = rDot (φ'' t) (Fin.tail y) := by
            intro t
            change rDot (Fin.cons 0 (φ'' t)) y = _
            rw [rDot_succ]; simp
          have hdc0 : dCons 0 = d 0 := rfl
          have hdcs : ∀ t : Fin (m - 1), dCons t.succ = d'' t := fun _ => rfl
          rw [hdc0, h0x, h0y]
          simp_rw [hdcs, htx, hty]
      · let α : ℚ := 1 / (d 0 * w 0 ^ 2)
        have hα : 0 ≤ α := by
          dsimp [α]
          exact div_nonneg zero_le_one (mul_nonneg (hd 0).le (sq_nonneg _))
        obtain ⟨d', φ_tail, hd', hφ'⟩ :=
          ih_rank1 (Fin.tail d) (fun j => hd j.succ) α hα (Fin.tail w)
        refine ⟨d', fun r => Fin.cons 0 (φ_tail r), hd', ?_⟩
        intro x y hx hy
        have hx' : d 0 * w 0 * x 0 = -wDot (Fin.tail d) (Fin.tail w) (Fin.tail x) := by
          have := hx
          rw [wDot_succ] at this
          linarith
        have hy' : d 0 * w 0 * y 0 = -wDot (Fin.tail d) (Fin.tail w) (Fin.tail y) := by
          have := hy
          rw [wDot_succ] at this
          linarith
        have hd0 : d 0 ≠ 0 := (hd 0).ne'
        have hlead : d 0 * x 0 * y 0 =
            α * wDot (Fin.tail d) (Fin.tail w) (Fin.tail x) *
              wDot (Fin.tail d) (Fin.tail w) (Fin.tail y) := by
          dsimp [α]
          have hdw : d 0 * w 0 ^ 2 ≠ 0 := mul_ne_zero hd0 (pow_ne_zero 2 hw0)
          calc d 0 * x 0 * y 0
              = (d 0 * w 0 * x 0) * (d 0 * w 0 * y 0) / (d 0 * w 0 ^ 2) := by
                field_simp [hd0, hw0]
            _ = (-wDot (Fin.tail d) (Fin.tail w) (Fin.tail x)) *
                  (-wDot (Fin.tail d) (Fin.tail w) (Fin.tail y)) / (d 0 * w 0 ^ 2) := by
                rw [hx', hy']
            _ = 1 / (d 0 * w 0 ^ 2) *
                  wDot (Fin.tail d) (Fin.tail w) (Fin.tail x) *
                  wDot (Fin.tail d) (Fin.tail w) (Fin.tail y) := by ring
        rw [wDot_succ, hlead, add_comm, hφ' (Fin.tail x) (Fin.tail y)]
        refine Finset.sum_congr rfl fun r _ => ?_
        have hrx : rDot (Fin.cons 0 (φ_tail r)) x = rDot (φ_tail r) (Fin.tail x) := by
          rw [rDot_succ]; simp
        have hry : rDot (Fin.cons 0 (φ_tail r)) y = rDot (φ_tail r) (Fin.tail y) := by
          rw [rDot_succ]; simp
        rw [hrx, hry]
    refine ⟨hperp, ?_⟩
    intro d hd α hα w
    by_cases hw : w = 0
    · subst hw
      refine ⟨d, fun r => Pi.single r 1, hd, ?_⟩
      intro x y
      have hw0 : ∀ z, wDot d 0 z = 0 := fun z => by simp [wDot]
      simp only [hw0, mul_zero, add_zero]
      unfold wDot
      refine Finset.sum_congr rfl fun r _ => ?_
      have hrx : rDot (Pi.single r 1) x = x r := by simp [rDot, Pi.single_apply]
      have hry : rDot (Pi.single r 1) y = y r := by simp [rDot, Pi.single_apply]
      rw [hrx, hry]
    · set s := wDot d w w
      have hs : 0 < s := wDot_self_pos hd hw
      have hsne : s ≠ 0 := hs.ne'
      obtain ⟨d_perp, φ_perp, hd_perp, hφ_perp⟩ := hperp d hd w hw
      let π : (Fin (m + 1) → ℚ) → (Fin (m + 1) → ℚ) :=
        fun x i => x i - (wDot d w x / s) * w i
      have hπ_orth : ∀ x, wDot d w (π x) = 0 := by
        intro x
        have hsum : wDot d w (π x) =
            wDot d w x - (wDot d w x / s) * wDot d w w := by
          change (∑ r : Fin (m + 1), d r * w r * (x r - wDot d w x / s * w r)) = _
          have hterm : ∀ r : Fin (m + 1),
              d r * w r * (x r - wDot d w x / s * w r) =
                d r * w r * x r - (wDot d w x / s) * (d r * w r * w r) := by
            intro r; ring
          simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
          rfl
        rw [hsum]
        change wDot d w x - (wDot d w x / s) * s = 0
        field_simp [hsne]
        ring
      have hdecomp : ∀ x y,
          wDot d x y = (1 / s) * wDot d w x * wDot d w y + wDot d (π x) (π y) := by
        intro x y
        have hexp : wDot d (π x) (π y) =
            wDot d x y - (wDot d w x / s) * wDot d w y - (wDot d w y / s) * wDot d w x +
              (wDot d w x / s) * (wDot d w y / s) * s := by
          change (∑ r : Fin (m + 1),
              d r * (x r - wDot d w x / s * w r) * (y r - wDot d w y / s * w r)) = _
          have hterm : ∀ r, d r * (x r - (wDot d w x / s) * w r) *
              (y r - (wDot d w y / s) * w r) =
              d r * x r * y r - (wDot d w x / s) * (d r * w r * y r) -
                (wDot d w y / s) * (d r * w r * x r) +
                (wDot d w x / s) * (wDot d w y / s) * (d r * w r * w r) := by
            intro r; ring
          simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
          rfl
        rw [hexp]
        field_simp [hsne]
        ring
      let d0 : ℚ := 1 / s + α
      have hd0 : 0 < d0 := by positivity
      let ψ0 : Fin (m + 1) → ℚ := fun i => d i * w i
      let ψ : Fin m → Fin (m + 1) → ℚ :=
        fun r i => φ_perp r i - (rDot (φ_perp r) w / s) * (d i * w i)
      refine ⟨Fin.cons d0 d_perp, Fin.cons ψ0 ψ, ?_, ?_⟩
      · intro r
        exact Fin.cases hd0 hd_perp r
      · intro x y
        have hπ : wDot d (π x) (π y) =
            ∑ r : Fin m, d_perp r * rDot (φ_perp r) (π x) * rDot (φ_perp r) (π y) :=
          hφ_perp (π x) (π y) (hπ_orth x) (hπ_orth y)
        have hdot0 : ∀ z, rDot ψ0 z = wDot d w z := by
          intro z
          unfold rDot wDot ψ0
          refine Finset.sum_congr rfl fun i _ => by ring
        have hdotr : ∀ r z, rDot (ψ r) z = rDot (φ_perp r) (π z) := by
          intro r z
          unfold rDot π ψ
          have hterm : ∀ i, (φ_perp r i - rDot (φ_perp r) w / s * (d i * w i)) * z i =
              φ_perp r i * z i - (rDot (φ_perp r) w / s) * (d i * w i * z i) := by
            intro i; ring
          have hterm2 : ∀ i, φ_perp r i * (z i - wDot d w z / s * w i) =
              φ_perp r i * z i - (wDot d w z / s) * (φ_perp r i * w i) := by
            intro i; ring
          simp_rw [hterm, hterm2, Finset.sum_sub_distrib, ← Finset.mul_sum]
          change rDot (φ_perp r) z - rDot (φ_perp r) w / s * wDot d w z =
            rDot (φ_perp r) z - wDot d w z / s * rDot (φ_perp r) w
          ring
        rw [Fin.sum_univ_succ]
        simp only [Fin.cons_zero, Fin.cons_succ, hdot0, hdotr]
        rw [← hπ, hdecomp x y]
        dsimp [d0]
        ring

private theorem schur_hasBoundedGramFactor {n R' : ℕ}
    {G : Matrix (Fin (n + 1)) (Fin (n + 1)) ℚ}
    (hG : HasBoundedGramFactor G (R' + 1)) (p : Fin (n + 1)) (hp : 0 < G p p) :
    HasBoundedGramFactor (schurComp G p) R' := by
  rcases hG with ⟨k, hkR, d, L, hd, hL⟩
  cases k with
  | zero =>
    have hp0 : G p p = 0 := by simpa using hL p p
    linarith
  | succ k' =>
    have hk'R : k' ≤ R' := Nat.le_of_succ_le_succ hkR
    let w : Fin (k' + 1) → ℚ := fun r => L r p
    have hw : w ≠ 0 := by
      intro h0
      have hp0 : G p p = 0 := by
        rw [hL p p]
        refine Finset.sum_eq_zero fun r _ => ?_
        have hr : L r p = 0 := congrFun h0 r
        simp [hr]
      linarith
    have hGpp : G p p = wDot d w w := by
      rw [hL p p]
      rfl
    have hGpp_ne : G p p ≠ 0 := hp.ne'
    let col : Fin n → Fin (k' + 1) → ℚ := fun a r => L r (p.succAbove a)
    let proj : Fin n → Fin (k' + 1) → ℚ :=
      fun a r => col a r - (wDot d (col a) w / G p p) * w r
    have hproj_orth : ∀ a, wDot d w (proj a) = 0 := by
      intro a
      have hsum : wDot d w (proj a) =
          wDot d w (col a) - (wDot d (col a) w / G p p) * wDot d w w := by
        change (∑ r : Fin (k' + 1), d r * w r * (col a r - wDot d (col a) w / G p p * w r)) = _
        have hterm : ∀ r : Fin (k' + 1),
            d r * w r * (col a r - wDot d (col a) w / G p p * w r) =
              d r * w r * col a r - (wDot d (col a) w / G p p) * (d r * w r * w r) := by
          intro r; ring
        simp_rw [hterm, Finset.sum_sub_distrib, ← Finset.mul_sum]
        rfl
      rw [hsum, ← hGpp, wDot_symm d w (col a)]
      field_simp [hGpp_ne]
      ring
    have hschur : ∀ a b : Fin n, schurComp G p a b = wDot d (proj a) (proj b) := by
      intro a b
      have hGab : G (p.succAbove a) (p.succAbove b) = wDot d (col a) (col b) := by
        rw [hL]
        rfl
      have hGap : G (p.succAbove a) p = wDot d (col a) w := by
        rw [hL]
        rfl
      have hGpb : G p (p.succAbove b) = wDot d w (col b) := by
        rw [hL]
        rfl
      have hexp : wDot d (proj a) (proj b) =
          wDot d (col a) (col b) -
            (wDot d (col a) w / G p p) * wDot d w (col b) -
            (wDot d (col b) w / G p p) * wDot d (col a) w +
            (wDot d (col a) w / G p p) * (wDot d (col b) w / G p p) * wDot d w w := by
        change (∑ r : Fin (k' + 1),
            d r * (col a r - wDot d (col a) w / G p p * w r) *
              (col b r - wDot d (col b) w / G p p * w r)) = _
        have hterm : ∀ r, d r * (col a r - (wDot d (col a) w / G p p) * w r) *
            (col b r - (wDot d (col b) w / G p p) * w r) =
            d r * col a r * col b r -
              (wDot d (col a) w / G p p) * (d r * w r * col b r) -
              (wDot d (col b) w / G p p) * (d r * col a r * w r) +
              (wDot d (col a) w / G p p) * (wDot d (col b) w / G p p) * (d r * w r * w r) := by
          intro r; ring
        simp_rw [hterm, Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
        rfl
      rw [schurComp, hGab, hGap, hGpb, hexp, ← hGpp, wDot_symm d (col b) w]
      field_simp [hGpp_ne]
      ring
    obtain ⟨hperp, _⟩ := perp_and_rank1 (k' + 1)
    obtain ⟨d', φ, hd', hφ⟩ := hperp d hd w hw
    refine ⟨k', hk'R, d', fun r a => rDot (φ r) (proj a), hd', ?_⟩
    intro a b
    rw [hschur a b, hφ (proj a) (proj b) (hproj_orth a) (hproj_orth b)]
    rfl

/-- **Completeness:** every symmetric matrix with a rank-`≤ R` positive-diagonal
factorization is accepted by `decideGram G R`. -/
theorem decideGram_complete : ∀ {m : ℕ} {G : Matrix (Fin m) (Fin m) ℚ} {R : ℕ},
    HasBoundedGramFactor G R → decideGram G R = true
  | 0, _, _, _ => rfl
  | n + 1, G, R, hfac => by
    have hdiag : ∀ i : Fin (n + 1), 0 ≤ G i i := by
      rcases hfac with ⟨k, _, d, L, hd, hL⟩
      intro i
      rw [hL i i]
      exact Finset.sum_nonneg fun r _ => by
        have : d r * L r i * L r i = d r * (L r i) ^ 2 := by ring
        rw [this]
        exact mul_nonneg (hd r).le (sq_nonneg _)
    have hneg : hasNegDiag G = false := hasNegDiag_eq_false_of_nonneg hdiag
    unfold decideGram
    simp only [hneg, Bool.false_eq_true, ↓reduceIte]
    cases hfind : findPosDiag G with
    | none =>
      rw [isZeroMatrix_true_iff]
      rcases hfac with ⟨k, _, d, L, hd, hL⟩
      have hLzero : ∀ r i, L r i = 0 := by
        intro r i
        have hnot : ¬ 0 < G i i := findPosDiag_none hfind i
        have hi0 : G i i = 0 := le_antisymm (not_lt.mp hnot) (hdiag i)
        rw [hL i i] at hi0
        have hterm0 : d r * L r i * L r i = 0 := by
          have hall : ∀ s ∈ (Finset.univ : Finset (Fin k)), d s * L s i * L s i = 0 := by
            rw [← Finset.sum_eq_zero_iff_of_nonneg]
            · exact hi0
            · intro s _
              have : d s * L s i * L s i = d s * (L s i) ^ 2 := by ring
              rw [this]
              exact mul_nonneg (hd s).le (sq_nonneg _)
          exact hall r (Finset.mem_univ r)
        have hmul : d r * (L r i) ^ 2 = 0 := by
          have : d r * (L r i) ^ 2 = d r * L r i * L r i := by ring
          rw [this, hterm0]
        rcases mul_eq_zero.mp hmul with hdr | hl
        · exact False.elim ((hd r).ne' hdr)
        · exact sq_eq_zero_iff.mp hl
      intro i j
      rw [hL i j]
      exact Finset.sum_eq_zero fun r _ => by simp [hLzero r i]
    | some p =>
      have hp : 0 < G p p := findPosDiag_some hfind
      cases R with
      | zero =>
        rcases hfac with ⟨k, hk, d, L, _, hL⟩
        have hk0 : k = 0 := Nat.le_zero.mp hk
        subst hk0
        have hp0 : G p p = 0 := by simpa using hL p p
        linarith
      | succ R' =>
        exact decideGram_complete (schur_hasBoundedGramFactor hfac p hp)

/-- **Exact Soundness-and-Completeness Equivalence:** for every symmetric rational
matrix `G`, `decideGram G R = true` if and only if `G` is PSD of rank `≤ R`. -/
theorem decideGram_iff {m R : ℕ} {G : Matrix (Fin m) (Fin m) ℚ} (hG : Gᵀ = G) :
    decideGram G R = true ↔ HasBoundedGramFactor G R :=
  ⟨decideGram_sound hG, decideGram_complete⟩

/-- A negative diagonal entry refutes `IsRatPSD`. -/
theorem not_isRatPSD_of_neg_diag {m : ℕ} {G : Matrix (Fin m) (Fin m) ℚ} {i : Fin m}
    (hi : G i i < 0) : ¬ IsRatPSD G := by
  intro hpsd
  have h := hpsd (Pi.single i 1)
  let v : Fin m → ℚ := Pi.single i 1
  have h := hpsd v
  have hval : ratQuad G v = G i i := by
    unfold ratQuad
    have h1 : ∀ a : Fin m,
        (∑ b : Fin m, v a * G a b * v b) =
          if a = i then G i i else 0 := by
      intro a
      by_cases ha : a = i
      · subst ha
        simp [v, Pi.single_apply]
      · simp [v, Pi.single_apply, ha]
    simp_rw [h1]
    simp
  linarith

/-! ## 6. Executable ultrafinitist witness checks (axiom-free, no `native_decide`) -/

/-- The `2 × 2` Gram matrix from `Book/SolovayTensor.lean` (`⟨z₀, u⟩ = r`). -/
def twoChannelGram (r : ℚ) : Matrix (Fin 2) (Fin 2) ℚ :=
  !![1, r; r, 1]

theorem twoChannel_three_fifths_rank2 :
    decideGram (twoChannelGram (3 / 5)) 2 = true := by
  simp [decideGram, hasNegDiag, findPosDiag, isZeroMatrix, schurComp, twoChannelGram,
    List.finRange_succ]
  norm_num

theorem twoChannel_three_fifths_rank1_false :
    decideGram (twoChannelGram (3 / 5)) 1 = false := by
  simp [decideGram, hasNegDiag, findPosDiag, isZeroMatrix, schurComp, twoChannelGram,
    List.finRange_succ]
  norm_num

theorem twoChannel_one_rank1 :
    decideGram (twoChannelGram 1) 1 = true := by
  simp [decideGram, hasNegDiag, findPosDiag, isZeroMatrix, schurComp, twoChannelGram,
    List.finRange_succ]

theorem twoChannel_six_fifths_false :
    decideGram (twoChannelGram (6 / 5)) 2 = false := by
  simp [decideGram, hasNegDiag, findPosDiag, isZeroMatrix, schurComp, twoChannelGram,
    List.finRange_succ]
  norm_num

theorem id3_gram_rank3 :
    decideGram (1 : Matrix (Fin 3) (Fin 3) ℚ) 3 = true := by
  simp [decideGram, hasNegDiag, findPosDiag, schurComp, List.finRange_succ]

/-- Horizon-rejection witness: three orthonormal vectors cannot fit in capacity `R = 2`. -/
theorem id3_gram_rank2_false :
    decideGram (1 : Matrix (Fin 3) (Fin 3) ℚ) 2 = false := by
  simp [decideGram, hasNegDiag, findPosDiag, schurComp, List.finRange_succ]

end BookProof.Ultrafinitism.ChapterGramPolyDecision
