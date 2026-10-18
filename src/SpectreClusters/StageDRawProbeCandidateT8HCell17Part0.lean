module

public import SpectreClusters.StageDRawProbeCandidateT8HCell17Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeAlignedT8H17_part0 : alignedRangeChecks (clusterCells .t8h) (candidateList .t8h)
      ⟨(2,-2),4⟩ witnessesT8H17 0 70 = true := by rfl
end SpectreClusters.StageD.Raw
