module

public import SpectreClusters.StageDRawProbeCandidateT8HCell8Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeAlignedT8H8_part1 : alignedRangeChecks (clusterCells .t8h) (candidateList .t8h)
      ⟨(1,-3),0⟩ witnessesT8H8 70 70 = true := by rfl
end SpectreClusters.StageD.Raw
