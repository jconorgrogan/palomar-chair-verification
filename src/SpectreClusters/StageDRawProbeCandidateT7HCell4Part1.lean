module

public import SpectreClusters.StageDRawProbeCandidateT7HCell4Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeAlignedT7H4_part1 : alignedRangeChecks (clusterCells .t7h) (candidateList .t7h)
      ⟨(-2,1),4⟩ witnessesT7H4 70 70 = true := by rfl
end SpectreClusters.StageD.Raw
