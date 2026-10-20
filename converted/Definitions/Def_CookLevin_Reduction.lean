/-
prove2.me platform library module `Definitions.Def_CookLevin_Reduction`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_CookLevin_Reduction.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

import Definitions.Def_CookLevin_Tableau
set_option autoImplicit true
/-
  CookLevinLean/Reduction.lean

  The Cook-Levin reduction.

  Given a verifier machine `Mv` and its parameters, `cookLevinReduction`
  produces, for each input `x`, the CNF tableau saying

      "there is a certificate `w` of length `polyBound cw dw |x|` such that
       `Mv` accepts `(x, w)` within `tabWidth` steps".

  The definition mentions only `Mv`, its parameters and `x`.  In particular it
  never mentions the language being reduced, and it never runs `Mv`: the
  previous version of this file defined the reduction as
  `fun x => if InLang x L' then encodeFormula [] else encodeFormula [[]]`,
  which decides `L'` in order to reduce it.
-/


namespace CookLevin

/-! ## Configurations are determined by their tapes -/

theorem config_ext {cfg1 cfg2 : Config} (hst : cfg1.1 = cfg2.1)
    (hlen : cfg1.2.length = cfg2.2.length)
    (h : ∀ j, j < cfg1.2.length → tapeAt cfg1 j = tapeAt cfg2 j) : cfg1 = cfg2 := by
  obtain ⟨q1, tps1⟩ := cfg1
  obtain ⟨q2, tps2⟩ := cfg2
  simp only at hst hlen h
  subst hst
  refine congrArg _ (List.ext_getElem hlen ?_)
  intro i hi1 hi2
  have e1 : tapeAt ((q1, tps1) : Config) i = tps1[i] := getD_of_lt _ _ hi1
  have e2 : tapeAt ((q1, tps2) : Config) i = tps2[i] := getD_of_lt _ _ hi2
  rw [← e1, ← e2]
  exact h i hi1

/-! ## The tapes of a two-input start configuration -/

/-- The contents of tape `j` in `startConfig2 k xs ws`. -/
def startTape (xs ws : List Symbol) (j : TapeIdx) : Nat → Symbol :=
  if j = 0 then contents xs else if j = 1 then contents ws else contents []

theorem tapeAt_startConfig2 {k : Nat} (hk : 2 ≤ k) (xs ws : List Symbol) {j : Nat}
    (hj : j < k) : tapeAt (startConfig2 k xs ws) j = (startTape xs ws j, 0) := by
  match j with
  | 0 => rfl
  | 1 => rfl
  | (n + 2) =>
    unfold tapeAt startConfig2 startTape
    rw [getD_of_lt _ _ (by simp; omega)]
    simp

theorem tapeFun_startConfig2 {k : Nat} (hk : 2 ≤ k) (xs ws : List Symbol) {j : Nat}
    (hj : j < k) (p : Nat) : tapeFun (startConfig2 k xs ws) j p = startTape xs ws j p := by
  rw [tapeFun_eq, tapeAt_startConfig2 hk xs ws hj]

theorem headPos_startConfig2 {k : Nat} (hk : 2 ≤ k) (xs ws : List Symbol) {j : Nat}
    (hj : j < k) : headPos (startConfig2 k xs ws) j = 0 := by
  rw [headPos_eq, tapeAt_startConfig2 hk xs ws hj]

/-! ## The start condition of the reduction

Tape `0` is pinned to the instance, tape `1` is left free on cells `1 … m`
(restricted to the two bit symbols), and every other cell is pinned. -/

/-- The allowed symbols of cell `p` of tape `j` at time `0`. -/
def reductionInit (xs : List Symbol) (m : Nat) : TapeIdx → Nat → List Symbol := fun j p =>
  if j = 0 then [contents xs p]
  else if j = 1 then
    (if p = 0 then [startSymbol]
     else if p ≤ m then [zeroSymbol, oneSymbol, blankSymbol]
     else [blankSymbol])
  else [contents [] p]

theorem reductionInit_lt {xs : List Symbol} {m G : Nat} (hG : 4 ≤ G)
    (hxs : ∀ s ∈ xs, s < G) (j p : Nat) : ∀ s ∈ reductionInit xs m j p, s < G := by
  have hcontents : ∀ (ys : List Symbol), (∀ s ∈ ys, s < G) → ∀ q, contents ys q < G := by
    intro ys hys q
    unfold contents
    split
    · show 1 < G; omega
    · split
      · rename_i h1 h2
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
        exact hys _ (List.getElem_mem _)
      · show 0 < G; omega
  intro s hs
  unfold reductionInit at hs
  split at hs
  · simp only [List.mem_singleton] at hs
    exact hs ▸ hcontents xs hxs p
  · split at hs
    · split at hs
      · simp only [List.mem_singleton] at hs
        exact hs ▸ (by show 1 < G; omega)
      · split at hs
        · simp only [List.mem_cons, List.not_mem_nil, or_false] at hs
          rcases hs with rfl | rfl | rfl
          · show 2 < G; omega
          · show 3 < G; omega
          · show 0 < G; omega
        · simp only [List.mem_singleton] at hs
          exact hs ▸ (by show 0 < G; omega)
    · simp only [List.mem_singleton] at hs
      exact hs ▸ hcontents [] (by simp) p

/-! ## Certificate tapes -/

/-- The bits a configuration holds on cells `1 … m` of its certificate tape. -/
def witnessOf (cfg : Config) (m : Nat) : List Bool :=
  (List.range m).map fun i => decide (tapeFun cfg 1 (i + 1) = oneSymbol)

@[simp] theorem length_witnessOf (cfg : Config) (m : Nat) : (witnessOf cfg m).length = m := by
  simp [witnessOf]

theorem boolSym_inj {b b' : Bool} (h : boolSym b = boolSym b') : b = b' := by
  cases b <;> cases b' <;> first | rfl | (exfalso; exact absurd h (by decide))

theorem boolsToSymbols_lt_four' {w : List Bool} : ∀ s ∈ boolsToSymbols w, s = 2 ∨ s = 3 := by
  intro s hs
  simp only [boolsToSymbols, List.mem_map] at hs
  obtain ⟨b, _, rfl⟩ := hs
  cases b
  · exact Or.inl rfl
  · exact Or.inr rfl

/-- A certificate string of *any* length up to `m`, laid out on the tape,
satisfies the start condition. -/
theorem startTape_mem_reductionInit {xs : List Symbol} {w : List Bool} {m : Nat}
    (hw : w.length ≤ m) (j p : Nat) :
    startTape xs (boolsToSymbols w) j p ∈ reductionInit xs m j p := by
  have hlen : (boolsToSymbols w).length ≤ m := by simp [hw]
  match j with
  | 0 => exact List.mem_cons_self
  | 1 =>
    show contents (boolsToSymbols w) p ∈
      (if p = 0 then [startSymbol]
       else if p ≤ m then [zeroSymbol, oneSymbol, blankSymbol] else [blankSymbol])
    by_cases hp0 : p = 0
    · rw [if_pos hp0, hp0, contents_zero]
      exact List.mem_cons_self
    · rw [if_neg hp0]
      by_cases hpm : p ≤ m
      · rw [if_pos hpm]
        by_cases hpw : p ≤ (boolsToSymbols w).length
        · rw [contents_of_lt _ (by omega) hpw]
          have hmem : (boolsToSymbols w)[p - 1]! ∈ boolsToSymbols w := by
            rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
            exact List.getElem_mem _
          rcases boolsToSymbols_lt_four' _ hmem with h | h
          · rw [h]; exact List.mem_cons_self
          · rw [h]; exact List.mem_cons_of_mem _ List.mem_cons_self
        · rw [contents_of_gt _ (by omega)]
          exact List.mem_cons_of_mem _ (List.mem_cons_of_mem _ List.mem_cons_self)
      · rw [if_neg hpm, contents_of_gt _ (by omega)]
        exact List.mem_cons_self
  | (n + 2) => exact List.mem_cons_self

/-- A bit string laid out on a tape has the blank-suffix property: the bits
occupy an initial segment, and everything after them is blank. -/
theorem blankSuffix_startConfig2 {k G Q T : Nat} (hk : 2 ≤ k) (xs : List Symbol)
    (w : List Bool) :
    BlankSuffix ⟨k, G, Q, T⟩ (startConfig2 k xs (boolsToSymbols w)) 1 := by
  intro p _ hb
  have h1k : (1 : Nat) < k := by omega
  rw [tapeFun_startConfig2 hk xs _ h1k] at hb
  rw [tapeFun_startConfig2 hk xs _ h1k]
  have hb' : contents (boolsToSymbols w) p = blankSymbol := hb
  show contents (boolsToSymbols w) (p + 1) = blankSymbol
  refine contents_of_gt _ ?_
  by_cases hgt : (boolsToSymbols w).length < p
  · omega
  · exfalso
    by_cases hp0 : p = 0
    · rw [hp0, contents_zero] at hb'
      exact absurd hb' (by decide)
    · rw [contents_of_lt _ (by omega) (by omega)] at hb'
      have hmem : (boolsToSymbols w)[p - 1]! ∈ boolsToSymbols w := by
        rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
        exact List.getElem_mem _
      rcases boolsToSymbols_lt_four' _ hmem with h | h <;> rw [h] at hb' <;>
        exact absurd hb' (by decide)

/-! ## The start configurations allowed by `reductionInit`

They are exactly the configurations `startConfig2 k xs (boolsToSymbols w)` with
`|w| = m`.  This is what turns the tableau's "some allowed start configuration
accepts" into "some certificate is accepted". -/

theorem contents_lt {G : Nat} (hG : 4 ≤ G) {ys : List Symbol} (hys : ∀ s ∈ ys, s < G)
    (q : Nat) : contents ys q < G := by
  unfold contents
  split
  · show 1 < G; omega
  · split
    · rw [List.getElem!_eq_getElem?_getD, List.getElem?_eq_getElem (by omega)]
      exact hys _ (List.getElem_mem _)
    · show 0 < G; omega

theorem startTape_of_gt {xs ws : List Symbol} {T p : Nat} (j : TapeIdx)
    (hx : xs.length ≤ T) (hws : ws.length ≤ T) (hp : T < p) :
    startTape xs ws j p = blankSymbol := by
  unfold startTape
  split
  · exact contents_of_gt _ (by omega)
  · split
    · exact contents_of_gt _ (by omega)
    · exact contents_of_gt _ (by simp; omega)

theorem startOK_startConfig2 {k G Q T m : Nat} {xs : List Symbol} {w : List Bool}
    (hk : 2 ≤ k) (hG : 4 ≤ G) (hxs : ∀ s ∈ xs, s < G) (hw : w.length ≤ m)
    (hxT : xs.length ≤ T) (hmT : m ≤ T) :
    StartOK ⟨k, G, Q, T⟩ (reductionInit xs m) (startConfig2 k xs (boolsToSymbols w)) := by
  have hlen : (boolsToSymbols w).length ≤ m := by simp [hw]
  refine ⟨startConfig2_length hk xs _, rfl, fun j hj => headPos_startConfig2 hk xs _ hj,
    ?_, ?_, ?_⟩
  · intro j hj p _
    rw [tapeFun_startConfig2 hk xs _ hj]
    exact startTape_mem_reductionInit hw j p
  · intro j hj p hp
    rw [tapeFun_startConfig2 hk xs _ hj]
    exact startTape_of_gt j hxT (by omega) hp
  · intro j hj p
    rw [tapeFun_startConfig2 hk xs _ hj]
    unfold startTape
    split
    · exact contents_lt hG hxs p
    · split
      · refine contents_lt hG ?_ p
        intro s hs
        rcases boolsToSymbols_lt_four' _ hs with h | h <;>
          (rw [h]; exact Nat.lt_of_lt_of_le (by omega) hG)
      · exact contents_lt hG (by simp) p

/-! ## Reading the certificate off a start configuration

The certificate region of tape `1` may hold blanks as well as bits, so the
certificate is the *initial run* of non-blank cells.  `BlankSuffix` guarantees
that this run really is initial, i.e. that there are no blanks in the middle. -/

/-- The length of the certificate on cells `1 … m` of tape `1`: the largest
index `≤ m` whose cell is non-blank. -/
def certRun (cfg : Config) : Nat → Nat
  | 0 => 0
  | n + 1 => if tapeFun cfg 1 (n + 1) = blankSymbol then certRun cfg n else n + 1

theorem certRun_succ (cfg : Config) (n : Nat) :
    certRun cfg (n + 1) =
      if tapeFun cfg 1 (n + 1) = blankSymbol then certRun cfg n else n + 1 := rfl

theorem certRun_le (cfg : Config) (m : Nat) : certRun cfg m ≤ m := by
  induction m with
  | zero => exact Nat.le_refl 0
  | succ n ih =>
    rw [certRun_succ]
    split
    · omega
    · exact Nat.le_refl _

theorem certRun_nonblank (cfg : Config) (m : Nat) (h : 0 < certRun cfg m) :
    tapeFun cfg 1 (certRun cfg m) ≠ blankSymbol := by
  induction m with
  | zero => exact absurd h (Nat.lt_irrefl 0)
  | succ n ih =>
    rw [certRun_succ] at h ⊢
    by_cases hb : tapeFun cfg 1 (n + 1) = blankSymbol
    · rw [if_pos hb] at h ⊢
      exact ih h
    · rw [if_neg hb] at h ⊢
      exact hb

theorem certRun_blank_of_gt (cfg : Config) (m : Nat) {p : Nat}
    (hlt : certRun cfg m < p) (hpm : p ≤ m) : tapeFun cfg 1 p = blankSymbol := by
  induction m with
  | zero => omega
  | succ n ih =>
    rw [certRun_succ] at hlt
    by_cases hb : tapeFun cfg 1 (n + 1) = blankSymbol
    · rw [if_pos hb] at hlt
      by_cases hpn : p ≤ n
      · exact ih hlt hpn
      · exact (show p = n + 1 by omega) ▸ hb
    · rw [if_neg hb] at hlt
      omega

theorem certRun_nonblank_of_le {k G Q T : Nat} {cfg : Config} {m : Nat}
    (hbs : BlankSuffix ⟨k, G, Q, T⟩ cfg 1) (hmT : m ≤ T) {p : Nat}
    (hp1 : 1 ≤ p) (hple : p ≤ certRun cfg m) : tapeFun cfg 1 p ≠ blankSymbol := by
  intro hblank
  have hcm : certRun cfg m ≤ m := certRun_le cfg m
  exact certRun_nonblank cfg m (by omega)
    (BlankSuffix.mono hbs hple (show certRun cfg m ≤ T by omega) hblank)

/-- The certificate written on tape `1`. -/
def certOf (cfg : Config) (m : Nat) : List Bool :=
  ((List.range m).map fun i => decide (tapeFun cfg 1 (i + 1) = oneSymbol)).take (certRun cfg m)

theorem length_certOf (cfg : Config) (m : Nat) : (certOf cfg m).length = certRun cfg m := by
  unfold certOf
  rw [List.length_take, List.length_map, List.length_range]
  exact Nat.min_eq_left (certRun_le cfg m)

theorem length_certOf_le (cfg : Config) (m : Nat) : (certOf cfg m).length ≤ m := by
  rw [length_certOf]
  exact certRun_le cfg m

theorem getElem!_boolsToSymbols_certOf {cfg : Config} {m i : Nat} (hi : i < certRun cfg m) :
    (boolsToSymbols (certOf cfg m))[i]! =
      boolSym (decide (tapeFun cfg 1 (i + 1) = oneSymbol)) := by
  have hlen : (certOf cfg m).length = certRun cfg m := length_certOf cfg m
  have hbit : (certOf cfg m)[i]'(by omega) = decide (tapeFun cfg 1 (i + 1) = oneSymbol) := by
    unfold certOf
    rw [List.getElem_take]
    simp
  rw [List.getElem!_eq_getElem?_getD]
  unfold boolsToSymbols
  rw [List.getElem?_map, List.getElem?_eq_getElem (show i < (certOf cfg m).length by omega), hbit]
  rfl

/-- **The certificate really is what the tape says.** -/
theorem contents_certOf {k G Q T m : Nat} {xs : List Symbol} {cfg : Config}
    (hk : 2 ≤ k) (hmT : m ≤ T)
    (h : StartOK ⟨k, G, Q, T⟩ (reductionInit xs m) cfg)
    (hbs : BlankSuffix ⟨k, G, Q, T⟩ cfg 1) (p : Nat) :
    contents (boolsToSymbols (certOf cfg m)) p = tapeFun cfg 1 p := by
  have h1k : (1 : Nat) < k := by omega
  have hLm : certRun cfg m ≤ m := certRun_le cfg m
  have hwslen : (boolsToSymbols (certOf cfg m)).length = certRun cfg m := by
    simp [length_certOf]
  by_cases hp0 : p = 0
  · subst hp0
    rw [contents_zero]
    have hc : tapeFun cfg 1 0 ∈ [startSymbol] := h.cells 1 h1k 0 (by omega)
    exact (by simpa using hc : tapeFun cfg 1 0 = startSymbol).symm
  · by_cases hpL : p ≤ certRun cfg m
    · rw [contents_of_lt _ (by omega) (by omega),
        getElem!_boolsToSymbols_certOf (show p - 1 < certRun cfg m by omega),
        show p - 1 + 1 = p by omega]
      have hmem : tapeFun cfg 1 p ∈
          (if p = 0 then [startSymbol]
           else if p ≤ m then [zeroSymbol, oneSymbol, blankSymbol] else [blankSymbol]) :=
        h.cells 1 h1k p (show p ≤ T by omega)
      rw [if_neg hp0, if_pos (show p ≤ m by omega)] at hmem
      have hnb : tapeFun cfg 1 p ≠ blankSymbol :=
        certRun_nonblank_of_le hbs hmT (by omega) hpL
      simp only [List.mem_cons, List.not_mem_nil, or_false] at hmem
      rcases hmem with h2 | h3 | hb
      · rw [h2]; rfl
      · rw [h3]; rfl
      · exact absurd hb hnb
    · by_cases hpm : p ≤ m
      · rw [contents_of_gt _ (by omega)]
        exact (certRun_blank_of_gt cfg m (by omega) hpm).symm
      · by_cases hpT : p ≤ T
        · rw [contents_of_gt _ (by omega)]
          have hmem : tapeFun cfg 1 p ∈
              (if p = 0 then [startSymbol]
               else if p ≤ m then [zeroSymbol, oneSymbol, blankSymbol] else [blankSymbol]) :=
            h.cells 1 h1k p hpT
          rw [if_neg hp0, if_neg hpm] at hmem
          exact (by simpa using hmem : tapeFun cfg 1 p = blankSymbol).symm
        · rw [contents_of_gt _ (by omega)]
          exact (h.blank 1 h1k p (show T < p by omega)).symm

theorem eq_startConfig2_of_startOK {k G Q T m : Nat} {xs : List Symbol} {cfg : Config}
    (hk : 2 ≤ k) (hxT : xs.length ≤ T) (hmT : m ≤ T)
    (h : StartOK ⟨k, G, Q, T⟩ (reductionInit xs m) cfg)
    (hbs : BlankSuffix ⟨k, G, Q, T⟩ cfg 1) :
    cfg = startConfig2 k xs (boolsToSymbols (certOf cfg m)) := by
  refine config_ext (by rw [h.st]; rfl) (by rw [h.len, startConfig2_length hk]) ?_
  intro j hj
  rw [h.len] at hj
  rw [tapeAt_startConfig2 hk xs _ hj]
  refine Prod.ext (funext fun p => ?_) (by rw [← headPos_eq, h.hd j hj])
  show tapeFun cfg j p = startTape xs (boolsToSymbols (certOf cfg m)) j p
  match j with
  | 0 =>
    show tapeFun cfg 0 p = contents xs p
    by_cases hpT : p ≤ T
    · have hc : tapeFun cfg 0 p ∈ [contents xs p] := h.cells 0 (by omega) p hpT
      simpa using hc
    · rw [h.blank 0 (by omega) p (show T < p by omega), contents_of_gt _ (by omega)]
  | 1 =>
    show tapeFun cfg 1 p = contents (boolsToSymbols (certOf cfg m)) p
    exact (contents_certOf hk hmT h hbs p).symm
  | (n + 2) =>
    show tapeFun cfg (n + 2) p = contents [] p
    by_cases hpT : p ≤ T
    · have hc : tapeFun cfg (n + 2) p ∈ [contents [] p] := h.cells (n + 2) hj p hpT
      simpa using hc
    · rw [h.blank (n + 2) hj p (show T < p by omega), contents_of_gt _ (by simp; omega)]

/-! ## Extending a halting computation -/

theorem decidesIn_of_le {M : Machine} {k : Nat} {xs ws : List Symbol} {t T : Nat} {b : Bool}
    (h : DecidesIn M k xs ws t b) (hle : t ≤ T) : DecidesIn M k xs ws T b := by
  obtain ⟨hst, hout⟩ := h
  have heq : execute M (startConfig2 k xs ws) T = execute M (startConfig2 k xs ws) t :=
    execute_of_halted_le hst hle
  exact ⟨by rw [heq]; exact hst, by rw [heq]; exact hout⟩

/-! ## The reduction -/

/-- The certificate length prescribed by the verifier's parameters. -/
def certLen (cw dw : Nat) (x : List Bool) : Nat := polyBound cw dw x.length

/-- The width of the tableau: wide enough for the verifier's running time, and
at least as wide as the input plus the certificate, so that every cell the
machine can reach is tracked. -/
def tabWidth (cw dw ct dt : Nat) (x : List Bool) : Nat :=
  max (polyBound ct dt (x.length + certLen cw dw x)) (x.length + certLen cw dw x + 1)

theorem le_tabWidth_time (cw dw ct dt : Nat) (x : List Bool) :
    polyBound ct dt (x.length + certLen cw dw x) ≤ tabWidth cw dw ct dt x :=
  Nat.le_max_left _ _

theorem le_tabWidth_len (cw dw ct dt : Nat) (x : List Bool) :
    x.length + certLen cw dw x + 1 ≤ tabWidth cw dw ct dt x :=
  Nat.le_max_right _ _

/-- **The Cook-Levin reduction.**

On input `x` it emits the tableau CNF of the verifier machine `Mv`, with the
instance pinned on tape `0` and the certificate left free on tape `1`, together
with the blank-suffix clauses that make the free region range over certificates
of *every* length up to the bound.  The definition consults `Mv`'s transition
function (through `tableauCNF`) but never runs it, and never mentions the
language being reduced. -/
def cookLevinReduction (Mv : Machine) (k G cw dw ct dt : Nat) (x : List Bool) : List Bool :=
  encodeFormula
    (tableauCNF ⟨k, G, Mv.length, tabWidth cw dw ct dt x⟩ Mv
        (reductionInit (boolsToSymbols x) (certLen cw dw x)) ++
      blankSuffixClauses ⟨k, G, Mv.length, tabWidth cw dw ct dt x⟩ 1)

/-- **Correctness of the reduction.**  The emitted formula is satisfiable
exactly when the verifier accepts some certificate.  `L'` appears nowhere, and
the certificate is quantified with `≤`, as the textbook definition of NP
requires. -/
theorem cookLevinReduction_correct {Mv : Machine} {k G cw dw ct dt : Nat}
    (hwf : TuringMachine k G Mv) {V : List Bool → List Bool → Bool}
    (hdec : ∀ x w : List Bool, DecidesIn Mv k (boolsToSymbols x) (boolsToSymbols w)
      (polyBound ct dt (x.length + w.length)) (V x w))
    (hlenV : ∀ x w : List Bool, V x w = true → w.length ≤ polyBound cw dw x.length)
    (x : List Bool) :
    SAT (cookLevinReduction Mv k G cw dw ct dt x) ↔ ∃ w : List Bool, V x w = true := by
  have hM : WellFormed k G Mv := hwf.wellFormed
  have hk : 2 ≤ k := hM.two_le
  have hG : 4 ≤ G := hM.four_le
  have hxs : ∀ s ∈ boolsToSymbols x, s < G :=
    fun s hs => Nat.lt_of_lt_of_le (boolsToSymbols_lt hs) hG
  have hlenbound := le_tabWidth_len cw dw ct dt x
  have hxT : (boolsToSymbols x).length ≤ tabWidth cw dw ct dt x := by
    simp only [length_boolsToSymbols]; omega
  have hmT : certLen cw dw x ≤ tabWidth cw dw ct dt x := by omega
  have h1T : 1 ≤ tabWidth cw dw ct dt x := by omega
  have h1k : (1 : Nat) < k := by omega
  /- Every certificate short enough for the tableau is decided in time at most
     the tableau's width, so `DecidesIn` at the bound transfers to width `T`. -/
  have hshift : ∀ w : List Bool, w.length ≤ certLen cw dw x →
      DecidesIn Mv k (boolsToSymbols x) (boolsToSymbols w)
        (tabWidth cw dw ct dt x) (V x w) := by
    intro w hw
    refine decidesIn_of_le (hdec x w) (Nat.le_trans ?_ (le_tabWidth_time cw dw ct dt x))
    exact polyBound_mono (by omega)
  rw [cookLevinReduction, SAT_encodeFormula_iff,
    tableau_correct_blank (sh := ⟨k, G, Mv.length, tabWidth cw dw ct dt x⟩) hM rfl h1T h1k
      (fun j _ p _ => reductionInit_lt hG hxs j p)]
  constructor
  · rintro ⟨cfg0, hstart, hbs, hacc⟩
    refine ⟨certOf cfg0 (certLen cw dw x), ?_⟩
    have hwlen : (certOf cfg0 (certLen cw dw x)).length ≤ certLen cw dw x :=
      length_certOf_le cfg0 _
    rw [eq_startConfig2_of_startOK hk hxT hmT hstart hbs] at hacc
    have htrue : DecidesIn Mv k (boolsToSymbols x)
        (boolsToSymbols (certOf cfg0 (certLen cw dw x))) (tabWidth cw dw ct dt x) true := hacc
    exact boolSym_inj ((hshift _ hwlen).2.symm.trans htrue.2)
  · rintro ⟨w, hw⟩
    have hwlen : w.length ≤ certLen cw dw x := hlenV x w hw
    have hdec' := hshift w hwlen
    rw [hw] at hdec'
    exact ⟨startConfig2 k (boolsToSymbols x) (boolsToSymbols w),
      startOK_startConfig2 hk hG hxs hwlen hxT hmT,
      blankSuffix_startConfig2 hk _ w, hdec'⟩

/-- The one ingredient of `cook_levin_nphard` that is not proved here: the
reduction is computable in polynomial time on the machine model.  It is stated
as an explicit hypothesis, not assumed as an axiom, and it mentions neither
`SAT` nor the language being reduced.

The verifier machine is assumed well formed.  That costs `cook_levin_nphard`
nothing -- it only ever applies this to an `Mv` that `InNP` already told it is
well formed -- and it is what a construction gets to rely on: `GoodCommand`
bounds what every command can write and where it can move. -/
def ReductionIsPolyTime : Prop :=
  ∀ (Mv : Machine) (k G cw dw ct dt : Nat), TuringMachine k G Mv →
    IsPolyTimeComputable (cookLevinReduction Mv k G cw dw ct dt)

/-! ## The fixed-input tableau

Specialising `reductionInit` to a start condition that pins *both* tapes gives
the tableau of a machine on a completely determined input, and the statement of
`reduction_correctness` in its classical form. -/

/-- The start condition pinning every cell of every tape. -/
def pinnedInit (xs ws : List Symbol) : TapeIdx → Nat → List Symbol :=
  fun j p => [startTape xs ws j p]

/-- The tableau CNF of `M` on the fixed input `xs` (tape `0`) and `ws`
(tape `1`), for `T` steps. -/
def buildTableauCNF (M : Machine) (k G : Nat) (xs ws : List Symbol) (T : Nat) : Formula :=
  tableauCNF ⟨k, G, M.length, T⟩ M (pinnedInit xs ws)

theorem eq_startConfig2_of_pinned {k G Q T : Nat} {xs ws : List Symbol} {cfg : Config}
    (hk : 2 ≤ k) (hxT : xs.length ≤ T) (hwT : ws.length ≤ T)
    (h : StartOK ⟨k, G, Q, T⟩ (pinnedInit xs ws) cfg) : cfg = startConfig2 k xs ws := by
  refine config_ext (by rw [h.st]; rfl) (by rw [h.len, startConfig2_length hk]) ?_
  intro j hj
  rw [h.len] at hj
  rw [tapeAt_startConfig2 hk xs ws hj]
  refine Prod.ext (funext fun p => ?_) (by rw [← headPos_eq, h.hd j hj])
  show tapeFun cfg j p = startTape xs ws j p
  by_cases hpT : p ≤ T
  · have hc : tapeFun cfg j p ∈ [startTape xs ws j p] := h.cells j hj p hpT
    simpa using hc
  · rw [h.blank j hj p (show T < p by omega),
      startTape_of_gt j hxT hwT (show T < p by omega)]

/-- **`reduction_correctness` in its classical form.**  The tableau of `M` on a
fixed input is satisfiable exactly when `M` accepts that input within `T`
steps.

Both directions are real: left to right extracts the run from the assignment
and shows by induction on time that it is *the* run of `M`; right to left
exhibits the assignment reading the accepting run off.  (The previous version of
this theorem was proved by running `M` inside `buildTableauCNF` and emitting
`[]` or `[[]]` accordingly.) -/
theorem reduction_correctness {M : Machine} {k G : Nat} (hwf : TuringMachine k G M)
    {xs ws : List Symbol} (hxs : ∀ s ∈ xs, s < G) (hws : ∀ s ∈ ws, s < G)
    {T : Nat} (h1T : 1 ≤ T) (hxT : xs.length ≤ T) (hwT : ws.length ≤ T) :
    Satisfiable (buildTableauCNF M k G xs ws T) ↔ AcceptsIn M k xs ws T := by
  have hM : WellFormed k G M := hwf.wellFormed
  have hk : 2 ≤ k := hM.two_le
  have hG : 4 ≤ G := hM.four_le
  have hinit : ∀ j, j < k → ∀ p, p ≤ T → ∀ s ∈ pinnedInit xs ws j p, s < G := by
    intro j _ p _ s hs
    simp only [pinnedInit, List.mem_singleton] at hs
    subst hs
    unfold startTape
    split
    · exact contents_lt hG hxs p
    · split
      · exact contents_lt hG hws p
      · exact contents_lt hG (by simp) p
  rw [buildTableauCNF,
    tableau_correct (sh := ⟨k, G, M.length, T⟩) hM rfl h1T hinit]
  constructor
  · rintro ⟨cfg0, hstart, hacc⟩
    rw [eq_startConfig2_of_pinned hk hxT hwT hstart] at hacc
    exact hacc
  · intro hacc
    refine ⟨startConfig2 k xs ws, ?_, hacc⟩
    refine ⟨startConfig2_length hk xs ws, rfl,
      fun j hj => headPos_startConfig2 hk xs ws hj, ?_, ?_, ?_⟩
    · intro j hj p _
      rw [tapeFun_startConfig2 hk xs ws hj]
      exact List.mem_cons_self
    · intro j hj p hp
      rw [tapeFun_startConfig2 hk xs ws hj]
      exact startTape_of_gt j hxT hwT hp
    · intro j hj p
      rw [tapeFun_startConfig2 hk xs ws hj]
      unfold startTape
      split
      · exact contents_lt hG hxs p
      · split
        · exact contents_lt hG hws p
        · exact contents_lt hG (by simp) p


/-! ## What the two input-facing groups are

`startClauses` is the one group whose clause *width* is not fixed by the shape:
it is `(init j p).length`, chosen by the caller.  That made it look like the
hardest group to emit after `transitionClauses`.  It is not, for the path that
actually matters.

`buildTableauCNF` -- the reduction's own entry point -- instantiates `init` at
`pinnedInit`, which hands back a **singleton** at every `(j, p)`.  So on that
path every clause of `startClauses` is a unit clause, and the group needs no
width machinery at all: a numeral, a one-index loop, and a two-index loop.

The generic `startClauses sh init` still has variable width, and `reductionInit`
really does use it -- the last theorem below is the witness. -/

/-- `acceptClauses` is not a loop of any kind: two unit clauses. -/
theorem acceptClauses_shape (sh : Shape) :
    acceptClauses sh =
      [[Literal.Pos (sh.stateVar sh.T sh.Q)],
       [Literal.Pos (sh.cellVar sh.T (verdictTape sh.k) 1 (boolSym true))]] := rfl

theorem acceptClauses_widths (sh : Shape) :
    (acceptClauses sh).map List.length = [1, 1] := rfl

/-- `startClauses` in its three parts. -/
theorem startClauses_shape (sh : Shape) (init : TapeIdx → Nat → List Symbol) :
    startClauses sh init =
      [[Literal.Pos (sh.stateVar 0 0)]] ++
      ((List.range sh.k).flatMap fun j => [[Literal.Pos (sh.headVar 0 j 0)]]) ++
      ((List.range sh.k).flatMap fun j =>
        (List.range (sh.T + 1)).flatMap fun p =>
          [(init j p).map fun s => Literal.Pos (sh.cellVar 0 j p s)]) := rfl

/-- Part 1 is a pure numeral -- independent of the entire shape. -/
theorem startClauses_part1 (sh : Shape) :
    clauseN [Literal.Pos (sh.stateVar 0 0)] = [5] := rfl

/-- Part 2 is one unit clause per tape, at the constant stride `8 * P`. -/
theorem startClauses_part2_stride (sh : Shape) (j : Nat) :
    2 * sh.headVar 0 j 0 + 1 = 3 + j * (8 * sh.P) := by
  unfold Shape.headVar pack
  -- conversion: the platform proof (`rw [Nat.mul_zero, …]; generalize sh.P * j = X; omega`)
  -- rewrites a different occurrence in Lean 4.28.0
  simp only [Nat.mul_zero, Nat.zero_add, Nat.add_zero]
  ring

/-- `pinnedInit` pins every cell: one symbol, never a choice. -/
theorem pinnedInit_singleton (xs ws : List Symbol) (j p : Nat) :
    (pinnedInit xs ws j p).length = 1 := rfl

/-- **Under `pinnedInit`, part 3 is one unit clause per `(j, p)`.**  This is
what `buildTableauCNF` uses, so on the reduction's own path `startClauses`
carries no init-dependent width at all. -/
theorem startClauses_part3_pinned (sh : Shape) (xs ws : List Symbol) :
    ((List.range sh.k).flatMap fun j =>
      (List.range (sh.T + 1)).flatMap fun p =>
        [(pinnedInit xs ws j p).map fun s => Literal.Pos (sh.cellVar 0 j p s)])
      = (List.range sh.k).flatMap fun j =>
          (List.range (sh.T + 1)).flatMap fun p =>
            [[Literal.Pos (sh.cellVar 0 j p (startTape xs ws j p))]] := rfl

/-- The generic case really is different: `reductionInit` leaves the
certificate tape free, so its width is 3 in the middle and 1 at the ends. -/
theorem reductionInit_width_varies (xs : List Symbol) {m : Nat} (hm : m ≠ 0) :
    (reductionInit xs m 1 0).length = 1 ∧ (reductionInit xs m 1 1).length = 3 := by
  refine ⟨rfl, ?_⟩
  show (if (1:Nat) = 0 then [startSymbol]
    else if 1 ≤ m then [zeroSymbol, oneSymbol, blankSymbol] else [blankSymbol]).length = 3
  rw [if_neg (by omega), if_pos (Nat.one_le_iff_ne_zero.mpr hm)]
  rfl

end CookLevin
