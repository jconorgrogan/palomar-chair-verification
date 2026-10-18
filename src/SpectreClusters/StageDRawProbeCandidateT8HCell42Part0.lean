module

public import SpectreClusters.StageDRawProbeCandidateT8HCell42Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeAlignedT8H42_part0 : alignedRangeChecks (clusterCells .t8h) (candidateList .t8h)
      ⟨(-2,1),5⟩ witnessesT8H42 0 70 = true := by rfl
end SpectreClusters.StageD.Raw
