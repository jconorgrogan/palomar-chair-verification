module

public import SpectreClusters.StageDRawProbeCandidateT7HCell38Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeAlignedT7H38_part1 : alignedRangeChecks (clusterCells .t7h) (candidateList .t7h)
      ⟨(-1,2),5⟩ witnessesT7H38 70 70 = true := by rfl
end SpectreClusters.StageD.Raw
