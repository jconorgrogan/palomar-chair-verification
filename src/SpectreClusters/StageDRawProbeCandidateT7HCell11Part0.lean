module

public import SpectreClusters.StageDRawProbeCandidateT7HCell11Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeAlignedT7H11_part0 : alignedRangeChecks (clusterCells .t7h) (candidateList .t7h)
      ⟨(-1,-1),0⟩ witnessesT7H11 0 70 = true := by rfl
end SpectreClusters.StageD.Raw
