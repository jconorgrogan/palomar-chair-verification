module

public import SpectreClusters.StageDRawProbeCandidateT7HCell20Part0
public import SpectreClusters.StageDRawProbeCandidateT7HCell20Part1

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeAlignedT7H20_checked : alignedChecks (clusterCells .t7h) (candidateList .t7h)
      ⟨(2,-3),4⟩ witnessesT7H20 = true := by
  apply alignedChecks_of_ranges _ _ _ _ (by rfl)
  intro b
  rcases b with ⟨b,hb⟩
  have he : b = 0 ∨ b = 1 := by omega
  rcases he with rfl | rfl
  · exact probeAlignedT7H20_part0
  · exact probeAlignedT7H20_part1
end SpectreClusters.StageD.Raw
