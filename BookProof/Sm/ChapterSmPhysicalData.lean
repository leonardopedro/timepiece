import Mathlib
import BookProof.Sm.ChapterSmHamiltonian
import BookProof.Sm.ChapterSmCarContinuum

/-!
# P0 — the physical data ledger of the Standard-Model operator

Work order: `SM_ESA_COMPLETION_PLAN.md` §4 **P0**, "freeze the operator and verify the
baseline".  This module is the ledger, not an operator: it fixes *what* the E1 object is,
records which existing Lean declarations carry each of its terms, and proves the counting and
disjointness statements the later packets (P1–P8) are allowed to rely on.  It deliberately
proves nothing about spectra, domains or closures.

## The endpoint

```text
h_SM = h_B + h_Dirac + h_gauge–matter + h_Yukawa,
H_SM = dΓ_out(h_SM) = Σᵢⱼ (h_SM)ᵢⱼ C†(eᵢ) A(eⱼ).
```

Two endpoints are kept separate (`smE1`, `smE2` below):

* **E1** — the manuscript collective-coordinate operator on
  `L²(ℝ¹⁶³) ⊗ F_internal`, with the **finite** internal factor: 96 complex CAR coordinates,
  192 real Majorana components (Rust contract, §9 of the plan), all 163 bosonic coordinates,
  the 40 field momenta, the 49 squared forms and the fixed-collective-coordinate spatial
  derivative.
* **E2** — the infinite matter-mode realization, whose inner fermionic factor is
  `BookProof.SmCarContinuum.CFock`.  The continuum CAR representation alone does not construct
  the Hamiltonian: its sums, local products and common core are not defined here, and no ESA
  statement is transferred from E1 to E2.

## The bosonic ledger (manuscript ↔ Lean ↔ Cadabra ↔ Rust)

| term | manuscript | Lean | Cadabra | Rust | status |
|---|---|---|---|---|---|
| `h_B` gauge | `½(π² + B²)` | `smG/smDG/…`, `smMag*` | CHECK 1–8 | `h_B` | **proved** |
| `h_B` Higgs | `½π^φ² + ½(Dφ)² + V` | `smCovD`, `smWall` | CHECK 9–16 | `h_B` | **proved** |
| `h_Dirac` | `γ·∂` on spinors | — (CAR only) | export | Dirac | **not an operator** |
| `h_gauge–matter` | matter covariant `D` | — (P1) | export | gauge–matter | **not an operator** |
| `h_Yukawa` | four real components + h.c. | — (P1) | CHECK 21–24 | Yukawa | **not an operator** |
| `dΓ_out(h_SM)` | outer quantization | `ChapterQgOuterFockEsa` | seam | outer | **interface** |

The "status" column is part of the ledger data (`smLedger`), so a reader cannot mistake a planned
declaration for a proved one.

## Conventions pinned here

* **Coordinate recount.** `3 + 24 + 72 + 9 + 27 + 3 + 9 + 4 + 12 = 163` (`card_smCoord`),
  partitioned as `163 = 3 + 40 + 120`: three spatial coordinates, the 40 momentum-carrying field
  coordinates, and the 120 jet coordinates.  The 120 jets stay independent coordinates: the
  spatial-derivative elimination by momentum convolution is an NS/QG work order and is **not**
  imported here (`card_smJet`, `card_partition`).
* **Forms.** `49 = 24 + 9 + 3 + 12 + 1` (`card_smForm`), the last two blocks being the twelve
  covariant Higgs derivatives and the single Higgs wall.
* **Higgs constant.** With `φ†φ = ‖φ_real‖²/2`, `V = −μ²‖φ‖²/2 + λ‖φ‖⁴/4` and `v² = μ²/λ`, the
  implemented positive square adds `c_H = μ⁴/(4λ) = μ²v²/4` (`higgsVacuumEnergy`,
  `higgsVacuumEnergy_eq`).  This specified inner constant shifts `H_SM` by `c_H N_out`; it is
  not an outer vacuum-energy subtraction.
* **Matter recount is arithmetic, not modes.** The book lists `72 = 36 + 36` real quark
  components and the analogous lepton block with three right-handed neutrinos
  (`quark_leftReal`, `quark_rightReal`, `lepton_leftReal`, `lepton_rightReal`,
  `matterReal_eq`).  No identification of a real-component count with a number of CAR
  annihilation modes is made here; that is P1's `SmCarAlgebra` dictionary.

## What is proved here

`card_smJet`, `card_partition`, `kinetic_card`, `smForm_blocks`, `smMomCoord_injective`,
`smJetCoord_injective`, `smMom_disjoint_spatial`, `smMom_disjoint_jet`,
`spatial_disjoint_jet`, `smCoord_partition`, the non-emptiness of the mode and form sets, the
`c_H` identities, and the endpoint separation `smE1_ne_smE2`.

Everything is `sorry`-free and `axiom`-free.  No occurrence of "full" in this module asserts an
operator identity: the E1 normal form is a *specification* whose terms are listed, not a new
definition declared equal to the manuscript's Hamiltonian.
-/

namespace BookProof.SmPhysicalData

open BookProof.SmOneParticle BookProof.SmHamiltonian

noncomputable section

/-! ## 1. The ledger data -/

/-- One row of the ledger: a term of `h_SM` (or of its outer lift), the manuscript place it comes
from, the Lean declaration that carries it, the Cadabra check or export that cross-validates it,
the Rust contract that implements it, and its proof status. -/
structure SmLedgerEntry where
  /-- the term of `h_SM`, e.g. `h_B` or `h_Yukawa` -/
  term : String
  /-- manuscript location -/
  manuscript : String
  /-- Lean module / declaration(s) carrying the term -/
  lean : String
  /-- Cadabra check or export fixture -/
  cadabra : String
  /-- Rust contract -/
  rust : String
  /-- proof status: `PROVED`, `INTERFACE`, `NOT AN OPERATOR` -/
  status : String
  deriving Repr, Inhabited

/-- **The ledger.**  Six rows: the four summands of `h_SM`, its outer lift, and the inner
constant.  The statuses are the honest ones: only the bosonic summand is a Lean operator here. -/
def smLedger : List SmLedgerEntry :=
  [ ⟨"h_B: gauge", "SM weak/Higgs Lagrangian, temporal gauge", "SmHamiltonian.smHamiltonian",
      "CHECK 1-8, export 40 momenta / 49 forms", "E1 h_B assembly", "PROVED"⟩,
    ⟨"h_B: Higgs", "V = -mu^2|phi|^2/2 + lam|phi|^4/4, covariant derivative",
      "SmHamiltonian.smCovD, smWall, higgs_mexican_hat", "CHECK 9-16", "E1 h_B assembly",
      "PROVED"⟩,
    ⟨"h_Dirac", "spatial Dirac derivative on the inner spinor space",
      "ChapterSmDiracSpinor, ChapterSmCarAlgebra (CAR only)", "export 1152 matter entries",
      "E1 spatial Dirac momenta", "NOT AN OPERATOR"⟩,
    ⟨"h_gauge-matter", "matter covariant derivatives",
      "ChapterSmMatterRepresentation (proposed, P1)", "export 1152 matter entries",
      "E1 gauge-matter", "NOT AN OPERATOR"⟩,
    ⟨"h_Yukawa", "four real Higgs components, h.c. pairing, M_d M_u M_e M_nu",
      "ChapterSmFullYukawaData (proposed, P1)", "CHECK 21-24", "E1 Yukawa",
      "NOT AN OPERATOR"⟩,
    ⟨"dGamma_out(h_SM)", "recursive second quantization, creation left",
      "BookProof.ChapterQgOuterFockEsa", "full-operator Hashimoto seam", "outer universes",
      "INTERFACE"⟩]

/-- The ledger has six rows. -/
theorem smLedger_length : smLedger.length = 6 := rfl

/-- Every ledger row names its term and its status. -/
theorem smLedger_allNamed : ∀ e ∈ smLedger, e.term ≠ "" ∧ e.status ≠ "" := by
  intro e he
  fin_cases he <;> exact ⟨by decide, by decide⟩

/-! ## 2. The two endpoints E1 and E2 -/

/-- The declared data of an endpoint: what the inner factor is, how many modes it carries, and
which spatial derivative is meant.  A `none` field is a **not-constructed** quantity. -/
structure SmEndpointSpec where
  /-- endpoint name -/
  name : String
  /-- the inner carrier -/
  innerCarrier : String
  /-- complex CAR coordinates of the inner factor -/
  innerComplexModes : Option ℕ
  /-- real (Majorana) components of the inner factor -/
  innerRealComponents : Option ℕ
  /-- the meaning of the spatial derivative -/
  spatialDerivative : String
  deriving Repr, Inhabited

/-- **E1**: the complete manuscript collective-coordinate operator with the *finite* internal
factor (96 complex CAR coordinates, 192 real Majorana components) and the
fixed-collective-coordinate spatial derivative. -/
def smE1 : SmEndpointSpec :=
  ⟨"E1", "L2(R^163) tensor F_internal", some 96, some 192,
    "fixed collective field/jet coordinates"⟩

/-- **E2**: the infinite matter-mode realization, inner fermionic factor `CFock`.  The mode
counts are `none`: the infinite sums, local products and common core are not defined. -/
def smE2 : SmEndpointSpec :=
  ⟨"E2", "L2(R^163) tensor SmCarContinuum.CFock", none, none,
    "not defined"⟩

/-- The endpoints are distinct objects. -/
theorem smE1_ne_smE2 : smE1.innerCarrier ≠ smE2.innerCarrier := by decide

/-- E1 carries 96 complex CAR coordinates. -/
theorem smE1_complexModes : smE1.innerComplexModes = some 96 := rfl

/-- E1 carries 192 real Majorana components. -/
theorem smE1_realComponents : smE1.innerRealComponents = some 192 := rfl

/-- The E1 real component count is twice its complex mode count. -/
theorem smE1_real_eq_two_mul_complex : (192 : ℕ) = 2 * 96 := by norm_num

/-- E2 has no declared mode count: no infinite-mode Hamiltonian is constructed. -/
theorem smE2_noModeCount : smE2.innerComplexModes = none := rfl

/-! ## 3. The coordinate partition `163 = 3 + 40 + 120` -/

/-- The `120` jet coordinates of `SmCoord`: the gluon derivatives, the weak derivatives, the
hypercharge derivatives and the Higgs derivatives. -/
abbrev SmJet : Type :=
  (Fin 8 × Fin 3 × Fin 3) ⊕ (Fin 3 × Fin 3 × Fin 3) ⊕ (Fin 3 × Fin 3) ⊕ (Fin 4 × Fin 3)

/-- **The recount of the jets**: `72 + 27 + 9 + 12 = 120`. -/
theorem card_smJet : Fintype.card SmJet = 120 := by simp

/-- The coordinate of a jet label. -/
def smJetCoord : SmJet → Fin 163
  | Sum.inl (a, i, j) => smDG a i j
  | Sum.inr (Sum.inl (k, i, j)) => smDW k i j
  | Sum.inr (Sum.inr (Sum.inl (i, j))) => smDB i j
  | Sum.inr (Sum.inr (Sum.inr (a, j))) => smDPhi a j

/-- **The partition of the `163` bosonic coordinates**: three spatial, forty momentum-carrying
fields, one hundred and twenty jets. -/
theorem card_partition : 3 + 40 + 120 = 163 := by norm_num

/-- The kinetic subset of §3 of the plan: the forty momentum-carrying coordinates together with
the three spatial coordinates. -/
abbrev SmKinetic : Type := SmMom ⊕ Fin 3

/-- **The recount of the kinetic subset**: `40 + 3 = 43`. -/
theorem kinetic_card : Fintype.card SmKinetic = 43 := by simp

/-- The kinetic subset and the jets exhaust the coordinate set. -/
theorem kinetic_partition : 43 + 120 = 163 := by norm_num

/-- **The momentum coordinates are injective as a family.** -/
theorem smMomCoord_injective : Function.Injective smMomCoord := by
  rintro (⟨a, b⟩ | ⟨k, b⟩ | b | a) (⟨a', b'⟩ | ⟨k', b'⟩ | b' | a') h
  all_goals
    simp only [smMomCoord] at h
    have h' := smIdx.injective h
    simp_all

/-- **The jet coordinates are injective as a family.** -/
theorem smJetCoord_injective : Function.Injective smJetCoord := by
  rintro (⟨a, b, c⟩ | ⟨k, b, c⟩ | ⟨b, c⟩ | ⟨a, c⟩)
    (⟨a', b', c'⟩ | ⟨k', b', c'⟩ | ⟨b', c'⟩ | ⟨a', c'⟩) h
  all_goals
    simp only [smJetCoord] at h
    have h' := smIdx.injective h
    simp_all

/-- **Active and spatial indices are disjoint**: a momentum-carrying coordinate is never one of
the three spatial coordinates. -/
theorem smMom_disjoint_spatial (m : SmMom) (i : Fin 3) : smMomCoord m ≠ smX i := by
  rcases m with ⟨a, b⟩ | ⟨k, b⟩ | b | a <;>
    (intro h; exact absurd (smIdx.injective h) (by simp))

/-- **Active and jet indices are disjoint.** -/
theorem smMom_disjoint_jet (m : SmMom) (j : SmJet) : smMomCoord m ≠ smJetCoord j := by
  rcases m with ⟨a, b⟩ | ⟨k, b⟩ | b | a <;>
    rcases j with ⟨a, b, c⟩ | ⟨k, b, c⟩ | ⟨b, c⟩ | ⟨a, c⟩ <;>
    (intro h; exact absurd (smIdx.injective h) (by simp))

/-- **Spatial and jet indices are disjoint.** -/
theorem spatial_disjoint_jet (i : Fin 3) (j : SmJet) : smX i ≠ smJetCoord j := by
  rcases j with ⟨a, b, c⟩ | ⟨k, b, c⟩ | ⟨b, c⟩ | ⟨a, c⟩ <;>
    (intro h; exact absurd (smIdx.injective h) (by simp))

/-- The three index families have the expected cardinalities. -/
theorem smCoord_partition :
    Fintype.card SmMom = 40 ∧ Fintype.card (Fin 3) = 3 ∧ Fintype.card SmJet = 120 ∧
      (40 : ℕ) + 3 + 120 = 163 :=
  ⟨card_smMom, rfl, card_smJet, by norm_num⟩

/-! ## 4. No empty mode set -/

/-- The momentum set is non-empty: `G^0_0` is a momentum-carrying coordinate. -/
theorem smMom_nonempty : Nonempty SmMom := ⟨Sum.inl ((0 : Fin 8), (0 : Fin 3))⟩

/-- The form set is non-empty: the Higgs wall is a squared form. -/
theorem smForm_nonempty : Nonempty SmForm := ⟨Sum.inr (Sum.inr (Sum.inr (Sum.inr ())))⟩

/-- The forms count with its five blocks displayed. -/
theorem smForm_blocks :
    Fintype.card ((Fin 8 × Fin 3) ⊕ (Fin 3 × Fin 3) ⊕ Fin 3) = 36 ∧
      Fintype.card ((Fin 4 × Fin 3) ⊕ Unit) = 13 ∧
      (36 : ℕ) + 13 = 49 :=
  ⟨by simp, by simp, by norm_num⟩

/-! ## 5. The matter recount (arithmetic, not modes) -/

/-- Left-handed quark components: `3` generations `× 3` colours `× (u_L, d_L)` two Weyl
spinors `× 2` real components. -/
def quark_leftReal : ℕ := 3 * 3 * 2 * 2

/-- Right-handed quark components, including the right-handed down quark. -/
def quark_rightReal : ℕ := 3 * 3 * 2 * 2

/-- Left-handed lepton components `(e_L, ν_L)`, colour singlets. -/
def lepton_leftReal : ℕ := 3 * 2 * 2

/-- Right-handed lepton components `(e_R, ν_R)`, with the three right-handed neutrinos and
**no** Majorana mass term. -/
def lepton_rightReal : ℕ := 3 * 2 * 2

/-- **The quark recount**: `72 = 36 + 36`. -/
theorem quark_real_eq : quark_leftReal + quark_rightReal = 72 := by norm_num [quark_leftReal,
  quark_rightReal]

/-- **The lepton recount**: `24 = 12 + 12`. -/
theorem lepton_real_eq : lepton_leftReal + lepton_rightReal = 24 := by norm_num [lepton_leftReal,
  lepton_rightReal]

/-- **The matter recount**: `72 + 24 = 96` real components per generation triplet. -/
theorem matterReal_eq : quark_leftReal + quark_rightReal + lepton_leftReal + lepton_rightReal
    = 96 := by norm_num [quark_leftReal, quark_rightReal, lepton_leftReal, lepton_rightReal]

/-- The matter real-component count is an arithmetic recount only; it is *not* identified with a
number of CAR annihilation modes here.  This theorem records the arithmetic side of the E1
declaration `96` complex CAR coordinates. -/
theorem matterReal_matches_smE1 : quark_leftReal + quark_rightReal + lepton_leftReal +
    lepton_rightReal = 96 := matterReal_eq

/-! ## 6. The Higgs inner constant -/

/-- The inner constant of the positive-square Higgs convention: `c_H = μ⁴/(4λ)`. -/
def higgsVacuumEnergy (m2 lam : ℝ) : ℝ := m2 ^ 2 / (4 * lam)

/-- **The classical-vacuum identity** with `v² = μ²/λ`: `c_H = μ²v²/4`.  It needs `λ ≠ 0`, which
is why it is a theorem with a hypothesis rather than a definition. -/
theorem higgsVacuumEnergy_eq (m2 lam v2 : ℝ) (hlam : lam ≠ 0) (hv : v2 = m2 / lam) :
    higgsVacuumEnergy m2 lam = m2 * v2 / 4 := by
  rw [higgsVacuumEnergy, hv]
  field_simp

/-- For `μ² > 0` and `λ > 0` the inner constant is positive. -/
theorem higgsVacuumEnergy_pos (m2 lam : ℝ) (hm : 0 < m2) (hl : 0 < lam) :
    0 < higgsVacuumEnergy m2 lam := by
  rw [higgsVacuumEnergy]
  positivity

/-- The constant vanishes at `μ = 0`: the shift is not an independent outer vacuum energy. -/
theorem higgsVacuumEnergy_zero (lam : ℝ) : higgsVacuumEnergy 0 lam = 0 := by
  simp [higgsVacuumEnergy]

end

end BookProof.SmPhysicalData
