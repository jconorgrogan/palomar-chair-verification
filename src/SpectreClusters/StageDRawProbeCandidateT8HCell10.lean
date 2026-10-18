module

public import SpectreClusters.StageDRawProbeCandidateT8HCell10Part0
public import SpectreClusters.StageDRawProbeCandidateT8HCell10Part1

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeAlignedT8H10_checked : alignedChecks (clusterCells .t8h) (candidateList .t8h)
      ⟨(3,-3),2⟩ witnessesT8H10 = true := by
  apply alignedChecks_of_ranges _ _ _ _ (by rfl)
  intro b
  rcases b with ⟨b,hb⟩
  have he : b = 0 ∨ b = 1 := by omega
  rcases he with rfl | rfl
  · exact probeAlignedT8H10_part0
  · exact probeAlignedT8H10_part1
end SpectreClusters.StageD.Raw
