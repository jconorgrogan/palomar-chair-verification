module

public import SpectreClusters.StageDRawProbeCandidateT8HCell35Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeAlignedT8H35_part1 : alignedRangeChecks (clusterCells .t8h) (candidateList .t8h)
      ⟨(-1,-1),0⟩ witnessesT8H35 70 70 = true := by rfl
end SpectreClusters.StageD.Raw
