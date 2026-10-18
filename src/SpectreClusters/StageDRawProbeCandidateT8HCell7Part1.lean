module

public import SpectreClusters.StageDRawProbeCandidateT8HCell7Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeAlignedT8H7_part1 : alignedRangeChecks (clusterCells .t8h) (candidateList .t8h)
      ⟨(2,-3),4⟩ witnessesT8H7 70 70 = true := by rfl
end SpectreClusters.StageD.Raw
