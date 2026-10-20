/-
prove2.me platform library module `Definitions.Def_ShorWiki_Defs`, converted to Lean 4.28.0.
Original text: `Downloads/_deps/Definitions/Def_ShorWiki_Defs.lean` (platform Mathlib rev 0df444a360ea).
Public prove2.me contributions are licensed under Apache 2.0 (https://prove2.me/terms).
-/
import Mathlib

open Matrix Kronecker

namespace ShorWiki

/-- The multiplicative order of `a` modulo `N`: the smallest positive integer `r` with
`a ^ r ≡ 1 (mod N)` (when `a` is coprime to `N`). -/
noncomputable def ord (N a : ℕ) : ℕ := orderOf (a : ZMod N)

/-- The number of qubits `n` of the second register: the smallest `n` with `N ≤ 2 ^ n`,
i.e. `n = ⌈log₂ N⌉`. -/
def regBits (N : ℕ) : ℕ := Nat.clog 2 N

/-- The computational basis state `|m⟩` in a register of dimension `d`
(the zero vector if `m ≥ d`). -/
def ket (d m : ℕ) : Fin d → ℂ := fun i => if (i : ℕ) = m then 1 else 0

/-- The tensor product `|u⟩ ⊗ |v⟩` of two register states. -/
def tensorState {d₁ d₂ : ℕ} (u : Fin d₁ → ℂ) (v : Fin d₂ → ℂ) : Fin d₁ × Fin d₂ → ℂ :=
  fun p => u p.1 * v p.2

/-- The `n`-qubit gate `U` of multiplication by `a` modulo `N`:
`U|k⟩ = |a k mod N⟩` for `0 ≤ k < N` and `U|k⟩ = |k⟩` for `N ≤ k < 2 ^ n`.
The entry `U i k` is the amplitude `⟨i|U|k⟩`. -/
noncomputable def mulModGate (N a n : ℕ) : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ :=
  fun i k =>
    if (k : ℕ) < N then (if (i : ℕ) = a * k % N then 1 else 0)
    else (if i = k then 1 else 0)

/-- The primitive `r`-th root of unity `ω_r = e^{2πi/r}`. -/
noncomputable def omega (r : ℕ) : ℂ := Complex.exp (2 * Real.pi * Complex.I / r)

/-- The state `|ψ_j⟩ = r^{-1/2} ∑_{k=0}^{r-1} ω_r^{-kj} |a^k mod N⟩` of the `n`-qubit
second register, where `r = ord N a`. -/
noncomputable def eigState (N a n j : ℕ) : Fin (2 ^ n) → ℂ :=
  fun i => (1 / Real.sqrt (ord N a) : ℂ) *
    ∑ k ∈ Finset.range (ord N a),
      (omega (ord N a) ^ (k * j))⁻¹ * (if (i : ℕ) = a ^ k % N then 1 else 0)

/-- The `m`-fold tensor power `H^{⊗m}` of the Hadamard gate:
`⟨x|H^{⊗m}|y⟩ = 2^{-m/2} (-1)^{x·y}`, where `x·y` is the number of bit positions
`b < m` at which both `x` and `y` have a `1`. -/
noncomputable def hadamardTensor (m : ℕ) : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ :=
  fun x y => (1 / Real.sqrt (2 ^ m) : ℂ) *
    (-1) ^ ((Finset.range m).filter (fun b => (x : ℕ).testBit b ∧ (y : ℕ).testBit b)).card

/-- The quantum Fourier transform on `m` qubits:
`⟨y|QFT_{2^m}|x⟩ = 2^{-m/2} e^{2πi x y / 2^m}`. -/
noncomputable def qft (m : ℕ) : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ :=
  fun y x => (1 / Real.sqrt (2 ^ m) : ℂ) *
    Complex.exp (2 * Real.pi * Complex.I * (x : ℕ) * (y : ℕ) / 2 ^ m)

/-- The inverse quantum Fourier transform `QFT_{2^m}^{-1} = QFT_{2^m}^†`. -/
noncomputable def qftInv (m : ℕ) : Matrix (Fin (2 ^ m)) (Fin (2 ^ m)) ℂ := (qft m)ᴴ

/-- The controlled gate `C-U^{2^j}`: qubit `j` of the first (`m`-qubit) register controls
the application of `U^{2^j}` to the second (`n`-qubit) register, where `U = mulModGate N a n`.
On `|x⟩|k⟩` it applies `U^{2^j}` to `|k⟩` if bit `j` of `x` is `1`, and does nothing otherwise. -/
noncomputable def controlledPowGate (N a n m j : ℕ) :
    Matrix (Fin (2 ^ m) × Fin (2 ^ n)) (Fin (2 ^ m) × Fin (2 ^ n)) ℂ :=
  fun p q =>
    if p.1 = q.1 then
      (if (q.1 : ℕ).testBit j then (mulModGate N a n ^ (2 ^ j)) p.2 q.2
       else (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ) p.2 q.2)
    else 0

/-- The modular-exponentiation stage of the circuit: the product of the controlled gates
`C-U^{2^0}, C-U^{2^1}, …, C-U^{2^{m-1}}`. -/
noncomputable def controlledPowers (N a n m : ℕ) :
    Matrix (Fin (2 ^ m) × Fin (2 ^ n)) (Fin (2 ^ m) × Fin (2 ^ n)) ℂ :=
  ((List.range m).map (fun j => controlledPowGate N a n m j)).prod

/-- The quantum phase estimation circuit for `U = mulModGate N a n` with an `m`-qubit first
register: Hadamard gates on the first register, then the controlled powers of `U`, then the
inverse quantum Fourier transform on the first register. -/
noncomputable def phaseEstimationCircuit (N a n m : ℕ) :
    Matrix (Fin (2 ^ m) × Fin (2 ^ n)) (Fin (2 ^ m) × Fin (2 ^ n)) ℂ :=
  (qftInv m ⊗ₖ (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ)) * controlledPowers N a n m *
    (hadamardTensor m ⊗ₖ (1 : Matrix (Fin (2 ^ n)) (Fin (2 ^ n)) ℂ))

/-- The output state of Shor's order-finding circuit: phase estimation with a `2n`-qubit
first register, `n = regBits N`, applied to the input `|0⟩^{⊗2n} ⊗ |1⟩`. -/
noncomputable def orderFindingOutput (N a : ℕ) :
    Fin (2 ^ (2 * regBits N)) × Fin (2 ^ regBits N) → ℂ :=
  (phaseEstimationCircuit N a (regBits N) (2 * regBits N)) *ᵥ
    tensorState (ket (2 ^ (2 * regBits N)) 0) (ket (2 ^ regBits N) 1)

/-- The probability of obtaining outcome `k` when measuring the first register of a
two-register state `Ψ` in the computational basis: `∑_i |⟨k, i|Ψ⟩|²`. -/
noncomputable def measureFirst {d₁ d₂ : ℕ} (Ψ : Fin d₁ × Fin d₂ → ℂ) (k : Fin d₁) : ℝ :=
  ∑ i : Fin d₂, ‖Ψ (k, i)‖ ^ 2

end ShorWiki
