module

public import SpectreClusters.StageDRawProbeCandidateT8HCell21Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeAlignedT8H21_part0 : alignedRangeChecks (clusterCells .t8h) (candidateList .t8h)
      ⟨(3,0),3⟩ witnessesT8H21 0 70 = true := by rfl
end SpectreClusters.StageD.Raw
