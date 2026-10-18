module

public import SpectreClusters.StageACandidateBCell0
public import SpectreClusters.StageACandidateBCell1
public import SpectreClusters.StageACandidateBCell2
public import SpectreClusters.StageACandidateBCell3
public import SpectreClusters.StageACandidateBCell4
public import SpectreClusters.StageACandidateBCell5
public import SpectreClusters.StageACandidateBCell6
public import SpectreClusters.StageACandidateBCell7
public import SpectreClusters.StageACandidateBCell8
public import SpectreClusters.StageACandidateBCell9

@[expose] public section

namespace SpectreClusters.StageA

set_option maxRecDepth 100000

theorem candidateB_raw_check :
    (rawNeighborPlacements (htCells .turtle)).all (candidateCheckB .turtle) = true := by
  apply rawChecks_from_cells
  apply List.all_eq_true.mpr
  intro c hc
  simp only [htCells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact candidateB_cell0_check
  · exact candidateB_cell1_check
  · exact candidateB_cell2_check
  · exact candidateB_cell3_check
  · exact candidateB_cell4_check
  · exact candidateB_cell5_check
  · exact candidateB_cell6_check
  · exact candidateB_cell7_check
  · exact candidateB_cell8_check
  · exact candidateB_cell9_check

theorem candidateB_complete (p : HTPlacement)
    (hp : ShapeContact (htCells .turtle) (placementCells p))
    (hd : DisjointCells (htCells .turtle) (placementCells p)) :
    p ∈ candidateList .turtle :=
  candidateList_complete_of_check .turtle candidateB_raw_check p hp hd
end SpectreClusters.StageA
