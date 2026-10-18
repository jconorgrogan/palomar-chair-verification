module

public import SpectreClusters.StageDRawProbeCandidateT8HCell44Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeAlignedT8H44_part1 : alignedRangeChecks (clusterCells .t8h) (candidateList .t8h)
      ⟨(-1,2),1⟩ witnessesT8H44 70 70 = true := by rfl
end SpectreClusters.StageD.Raw
