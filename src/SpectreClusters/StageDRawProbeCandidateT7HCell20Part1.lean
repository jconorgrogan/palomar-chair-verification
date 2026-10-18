module

public import SpectreClusters.StageDRawProbeCandidateT7HCell20Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeAlignedT7H20_part1 : alignedRangeChecks (clusterCells .t7h) (candidateList .t7h)
      ⟨(2,-3),4⟩ witnessesT7H20 70 70 = true := by rfl
end SpectreClusters.StageD.Raw
