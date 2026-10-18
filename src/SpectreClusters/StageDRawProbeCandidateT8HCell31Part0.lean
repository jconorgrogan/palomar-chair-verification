module

public import SpectreClusters.StageDRawProbeCandidateT8HCell31Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeAlignedT8H31_part0 : alignedRangeChecks (clusterCells .t8h) (candidateList .t8h)
      ⟨(-1,-1),5⟩ witnessesT8H31 0 70 = true := by rfl
end SpectreClusters.StageD.Raw
