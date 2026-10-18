module

public import SpectreClusters.StageDRawProbeCandidateT8HCell10Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeAlignedT8H10_part1 : alignedRangeChecks (clusterCells .t8h) (candidateList .t8h)
      ⟨(3,-3),2⟩ witnessesT8H10 70 70 = true := by rfl
end SpectreClusters.StageD.Raw
