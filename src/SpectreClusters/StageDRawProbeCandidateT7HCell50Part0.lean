module

public import SpectreClusters.StageDRawProbeCandidateT7HCell50Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeAlignedT7H50_part0 : alignedRangeChecks (clusterCells .t7h) (candidateList .t7h)
      ⟨(2,0),2⟩ witnessesT7H50 0 70 = true := by rfl
end SpectreClusters.StageD.Raw
