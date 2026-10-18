module

public import SpectreClusters.StageDRawProbeCandidateT8HCell28Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeAlignedT8H28_part0 : alignedRangeChecks (clusterCells .t8h) (candidateList .t8h)
      ⟨(1,2),4⟩ witnessesT8H28 0 70 = true := by rfl
end SpectreClusters.StageD.Raw
