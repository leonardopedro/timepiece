import BookProof.ChapterBookBrstYangMills
import BookProof.ChapterBookBrstGaugeFixing
import BookProof.ChapterBookBrstInstances
import BookProof.RoadmapAudit.AxiomAudit

/-!
Axiom audit for the implementation of the BRST formalism **as defined in `book.tex`**
(§"Pure SU(3) Yang-Mills theory"): the charge
`Ω = π^μ_a ∂_μψ†_a − π^μ_a f_{abc} A_{μb} ψ†_c − (i/2) f_{abc} ψ†_aψ†_bψ_c`, its canonical
relations, the Gauss-law constraint algebra, nilpotency, the gauge-fixing fermion
`Ψ = i ψ_a A_{0a}` and the gauge algebras it is instantiated with.  Each line must report only
`propext`, `Classical.choice`, `Quot.sound`.
-/

-- 1. The canonical (anti)commutation relations of the book's section.
#audit_axioms BookProof.BookBrstYangMills.bookCCR_poly
#audit_axioms BookProof.BookBrstYangMills.bookCCR
#audit_axioms BookProof.BookBrstYangMills.bookGhostCar
#audit_axioms BookProof.BookBrstYangMills.Afield_comm_chi
#audit_axioms BookProof.BookBrstYangMills.mom_comm_chi

-- 2. The Gauss-law constraint algebra, derived from those relations.
#audit_axioms BookProof.BookBrstYangMills.gauss_const_identity
#audit_axioms BookProof.BookBrstYangMills.gauss_field_identity
#audit_axioms BookProof.BookBrstYangMills.gaussDer_bracket
#audit_axioms BookProof.BookBrstYangMills.gaussGenPoly_bracket
#audit_axioms BookProof.BookBrstYangMills.gaussGen_bracket
#audit_axioms BookProof.BookBrstYangMills.gaussGenPoly_eq
#audit_axioms BookProof.BookBrstYangMills.bookConstraintAlgebra

-- 3. The book's charge and its nilpotency.
#audit_axioms BookProof.BookBrstYangMills.I_smul_gaussGen
#audit_axioms BookProof.BookBrstYangMills.bookOmega_eq_brstCharge
#audit_axioms BookProof.BookBrstYangMills.bookOmega_nilpotent

-- 4. The gauge-fixing fermion.
#audit_axioms BookProof.BookBrstGaugeFixing.glin_gf_anticomm
#audit_axioms BookProof.BookBrstGaugeFixing.Q_gf_anticomm
#audit_axioms BookProof.BookBrstGaugeFixing.brstCharge_gf_anticomm
#audit_axioms BookProof.BookBrstGaugeFixing.brst_exact_comm
#audit_axioms BookProof.BookBrstGaugeFixing.bookGfTerm_eq
#audit_axioms BookProof.BookBrstGaugeFixing.bookGfTerm_brst_closed

-- 4b. Accounting identity: vanishing at A_0 = 0 (QYM/SM; QG is non-ADM, see module docs).
#audit_axioms BookProof.BookBrstGaugeFixing.gfFermion_eq_zero
#audit_axioms BookProof.BookBrstGaugeFixing.bookGfFermion_eq_zero_of_Afield0
#audit_axioms BookProof.BookBrstGaugeFixing.bookGfTerm_eq_zero_of_Afield0
#audit_axioms BookProof.BookBrstInstances.su2_bookGfTerm_eq_zero_of_Afield0
#audit_axioms BookProof.BookBrstInstances.sm_bookGfTerm_eq_zero_of_Afield0

-- 5. The gauge algebras and non-vacuity.
#audit_axioms BookProof.BookBrstInstances.innerDeriv_leibniz
#audit_axioms BookProof.BookBrstInstances.su2_bookOmega_nilpotent
#audit_axioms BookProof.BookBrstInstances.sm_bookOmega_nilpotent
#audit_axioms BookProof.BookBrstInstances.su2_gaussGenPoly_ne_zero

-- 6. BRST cohomology of the book's charge.
#audit_axioms BookProof.BookBrstGaugeFixing.exactStates_le_physicalStates
#audit_axioms BookProof.BookBrstGaugeFixing.bookGfTerm_mem_physicalStates
#audit_axioms BookProof.BookBrstGaugeFixing.bookGfTerm_mem_exactStates

-- 7. Gauge-invariant observables.
#audit_axioms BookProof.BookBrstGaugeFixing.brstCharge_comm_of_comm
#audit_axioms BookProof.BookBrstGaugeFixing.bookOmega_comm_multOp
#audit_axioms BookProof.BookBrstGaugeFixing.casimir_bookOmega_comm
#audit_axioms BookProof.BookBrstInstances.su2_casimir_bookOmega_comm
