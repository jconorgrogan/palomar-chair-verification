module

public import SpectreClusters.StageDRawProbeCandidateT8HCell9Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeAlignedT8H9_part1 : alignedRangeChecks (clusterCells .t8h) (candidateList .t8h)
      ⟨(0,-2),3⟩ witnessesT8H9 70 70 = true := by rfl
end SpectreClusters.StageD.Raw
