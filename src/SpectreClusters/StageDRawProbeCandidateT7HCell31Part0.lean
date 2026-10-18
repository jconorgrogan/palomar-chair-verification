module

public import SpectreClusters.StageDRawProbeCandidateT7HCell31Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeAlignedT7H31_part0 : alignedRangeChecks (clusterCells .t7h) (candidateList .t7h)
      ⟨(3,-1),0⟩ witnessesT7H31 0 70 = true := by rfl
end SpectreClusters.StageD.Raw
