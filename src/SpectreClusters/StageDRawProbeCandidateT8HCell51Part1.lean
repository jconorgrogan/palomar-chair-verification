module

public import SpectreClusters.StageDRawProbeCandidateT8HCell51Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeAlignedT8H51_part1 : alignedRangeChecks (clusterCells .t8h) (candidateList .t8h)
      ⟨(0,2),4⟩ witnessesT8H51 70 70 = true := by rfl
end SpectreClusters.StageD.Raw
