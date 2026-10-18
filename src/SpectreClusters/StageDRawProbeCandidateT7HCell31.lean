module

public import SpectreClusters.StageDRawProbeCandidateT7HCell31Part0
public import SpectreClusters.StageDRawProbeCandidateT7HCell31Part1

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeAlignedT7H31_checked : alignedChecks (clusterCells .t7h) (candidateList .t7h)
      ⟨(3,-1),0⟩ witnessesT7H31 = true := by
  apply alignedChecks_of_ranges _ _ _ _ (by rfl)
  intro b
  rcases b with ⟨b,hb⟩
  have he : b = 0 ∨ b = 1 := by omega
  rcases he with rfl | rfl
  · exact probeAlignedT7H31_part0
  · exact probeAlignedT7H31_part1
end SpectreClusters.StageD.Raw
