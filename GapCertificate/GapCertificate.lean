/-
GapCertificate (T10): the instantiated T6 arithmetic, as closed certificates.

This file formalizes the *arithmetic instance* of the certified-gap theorem
(`MASS_GAP_CERTIFIED.md` §3.4, `BookProof/ChapterSirkCertifiedGap` T6) on the
recorded `g = 2`, `m = 4` `yang_mills_lattice` run.  The two numbers that are
data — transcribed from the emitted certificate of `MASS_GAP_CERTIFIED.md` —
are the measured sector gap `θᵒ − θᵉ = 1.9875` and the assembled width
`δᵒ + δᵉ = 0.0555`.  The T6 assembly

    lo = θᵒ − θᵉ − (δᵒ + δᵉ) = 1.9875 − 0.0555 = 1.932 > 0,
    hi = θᵒ − θᵉ + (δᵒ + δᵉ) = 1.9875 + 0.0555 = 2.043,

and the strong-coupling consistency check `g²/2 = 2 ∈ [1.932, 2.043]` at `g = 2`
(`ChapterSirkGapTable.qcdG2M4_strongCoupling_consistent`) are what the
certificates below witness.

The proof discipline follows `Layout/Layout.lean` (the S29/S31 pipeline): the
file has **no imports** — it is pure core Lean, so it compiles standalone and
the export needs no mathlib.  Every certificate is a **closed Bool expression**
closed by kernel reduction (`rfl`, `Eq.refl`).  No `native_decide`/`decide` —
those emit `Lean.ofReduceBool` / `_nativeDecide_*` terms that the independent
external checker nanoda (via the `lean4export` NDJSON pipeline) cannot reduce.

The decimals are read *exactly*: each literal is represented by its mantissa
and a power of ten (no `Float` anywhere, exactly as in
`BookProof/ChapterSirkCertificateReader`'s `Decimal`), and all arithmetic is
carried out on the common denominator `10⁴` as scaled naturals.

Regenerate the pinned fixture in unfer with (matching toolchain, official
lean4export 3.1.0):

  lean -o GapCertificate.olean GapCertificate/GapCertificate.lean
  LEAN_PATH=GapCertificate lean4export GapCertificate \
    -- GapCertificate.read_gap_verified \
    -- GapCertificate.read_width_verified \
    -- GapCertificate.gap_aggregate_verified \
    -- GapCertificate.width_aggregate_verified \
    -- GapCertificate.lower_verified \
    -- GapCertificate.upper_verified \
    -- GapCertificate.lower_pos_verified \
    -- GapCertificate.upper_gt_lower_verified \
    -- GapCertificate.strong_coupling_consistency_verified \
    > ../unfer/prob_kernel/tests/fixtures/gap_certificate.ndjson
-/

-- Powers of ten (the denominators).  `10^4 = 10000` is the common denominator
-- of every recorded decimal.
def pow10 : Nat → Nat
  | 0 => 1
  | n + 1 => 10 * pow10 n

-- The wire-format decimals of the recorded run, read exactly as (mantissa,
-- exponent) pairs — mirroring `BookProof/ChapterSirkCertificateReader`'s
-- `Decimal` (`"1.9875" ↦ (19875, 4)`, `"0.0555" ↦ (555, 4)`, ...).  The
-- example line pair of the reader chapter:
--
--   {"sector":"even","theta":0.0000,"delta":0.0255}
--   {"sector":"odd","theta":1.9875,"delta":0.0300}

def thetaEvenMantissa : Nat := 0      -- 0.0000
def thetaEvenExp : Nat := 4
def deltaEvenMantissa : Nat := 255    -- 0.0255
def deltaEvenExp : Nat := 4
def thetaOddMantissa : Nat := 19875   -- 1.9875
def thetaOddExp : Nat := 4
def deltaOddMantissa : Nat := 300     -- 0.0300
def deltaOddExp : Nat := 4

-- Common denominator of the example: all exponents are 4.
def denom : Nat := pow10 4

-- The two aggregates the theorem consumes, scaled by `denom`:
--   gap   = θᵒ − θᵉ = 1.9875  ↦  19875
--   width = δᵒ + δᵉ = 0.0555  ↦  555
def gapScaled : Nat := thetaOddMantissa - thetaEvenMantissa
def widthScaled : Nat := deltaOddMantissa + deltaEvenMantissa

-- The T6 assembly on the scaled naturals:
--   lo = gap − width,   hi = gap + width.
def lowerScaled : Nat := gapScaled - widthScaled
def upperScaled : Nat := gapScaled + widthScaled

-- Certificate 1: the mantissa reading of the odd-sector Ritz value.
def read_gap_checked : Bool := thetaOddMantissa == 19875 && thetaOddExp == 4
theorem read_gap_verified : read_gap_checked = true := by
  rfl

-- Certificate 2: the mantissa reading of the assembled width's odd part.
def read_width_checked : Bool := deltaOddMantissa == 300 && deltaOddExp == 4
theorem read_width_verified : read_width_checked = true := by
  rfl

-- Certificate 3: the measured sector gap aggregate is `1.9875` (scaled 19875).
def gap_aggregate_checked : Bool := gapScaled == 19875
theorem gap_aggregate_verified : gap_aggregate_checked = true := by
  rfl

-- Certificate 4: the assembled width aggregate is `0.0555` (scaled 555).
def width_aggregate_checked : Bool := widthScaled == 555
theorem width_aggregate_verified : width_aggregate_checked = true := by
  rfl

-- Certificate 5: the certified lower bound is `1.932` (scaled 19320).
def lower_checked : Bool := lowerScaled == 19320
theorem lower_verified : lower_checked = true := by
  rfl

-- Certificate 6: the certified upper bound is `2.043` (scaled 20430).
def upper_checked : Bool := upperScaled == 20430
theorem upper_verified : upper_checked = true := by
  rfl

-- Certificate 7: the stopping rule fires — the certified lower bound is
-- strictly positive, so the truncated Hamiltonian has a proof-carrying gap
-- (`ChapterSirkCertificateReader.formatExample_lower_pos`).
def lower_pos_checked : Bool := 0 < lowerScaled
theorem lower_pos_verified : lower_pos_checked = true := by
  rfl

-- Certificate 8: the window is non-trivial — `lo < hi`.
def upper_gt_lower_checked : Bool := lowerScaled < upperScaled
theorem upper_gt_lower_verified : upper_gt_lower_checked = true := by
  rfl

-- Certificate 9: the strong-coupling consistency check — at `g = 2` the
-- analytic value `g²/2 = 2` (scaled 20000) lies inside the certified window
-- `[19320, 20430] = [1.932, 2.043]`
-- (`ChapterSirkGapTable.qcdG2M4_strongCoupling_consistent`).
def strongCouplingScaled (g : Nat) : Nat := (g * g * denom) / 2
def strong_coupling_consistency_checked : Bool :=
  lowerScaled <= strongCouplingScaled 2 && strongCouplingScaled 2 <= upperScaled
theorem strong_coupling_consistency_verified : strong_coupling_consistency_checked = true := by
  rfl
