module

public import SpectreClusters.StageDRawProbeCandidateT8HCell41Data

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeAlignedT8H41_part0 : alignedRangeChecks (clusterCells .t8h) (candidateList .t8h)
      ⟨(-2,2),0⟩ witnessesT8H41 0 70 = true := by rfl
end SpectreClusters.StageD.Raw
