module

public import SpectreClusters.StageDRawProbeCandidateT8HCell51Part0
public import SpectreClusters.StageDRawProbeCandidateT8HCell51Part1

@[expose] public section

namespace SpectreClusters.StageD.Raw
set_option maxRecDepth 100000 in
theorem probeAlignedT8H51_checked : alignedChecks (clusterCells .t8h) (candidateList .t8h)
      ⟨(0,2),4⟩ witnessesT8H51 = true := by
  apply alignedChecks_of_ranges _ _ _ _ (by rfl)
  intro b
  rcases b with ⟨b,hb⟩
  have he : b = 0 ∨ b = 1 := by omega
  rcases he with rfl | rfl
  · exact probeAlignedT8H51_part0
  · exact probeAlignedT8H51_part1
end SpectreClusters.StageD.Raw
