import BookProof.ChapterSqSumOuterSingleTime
namespace BookProof.SqSumOuterFamily
open BookProof.FarisLavine BookProof.EsaClosure BookProof.StoneBridge
open BookProof.ChapterStoneResolvent BookProof.DirectSumEsa BookProof.HermiteProductCore
noncomputable section

def truncHam (F : SqFamily) (N : ℕ) : outerCore F.dim →ₗ[ℂ] outerFock F.dim :=
  dsOp (fun n => (F.trunc N).secHam n)

set_option maxHeartbeats 1000000 in
theorem test_stmt (F : SqFamily) :
    ∃ (T : UnboundedSelfAdjoint (outerFock F.dim)),
      IsSelfAdjointExtension F.outerHam T.op ∧
        (∀ N, IsSelfAdjointExtension (truncHam F N) T.op) := by
  sorry
end
end BookProof.SqSumOuterFamily
