module

public import SpectreClusters.StageACandidateACell0
public import SpectreClusters.StageACandidateACell1
public import SpectreClusters.StageACandidateACell2
public import SpectreClusters.StageACandidateACell3
public import SpectreClusters.StageACandidateACell4
public import SpectreClusters.StageACandidateACell5
public import SpectreClusters.StageACandidateACell6
public import SpectreClusters.StageACandidateACell7

@[expose] public section

namespace SpectreClusters.StageA

set_option maxRecDepth 100000

theorem candidateA_raw_check :
    (rawNeighborPlacements (htCells .hat)).all (candidateCheckB .hat) = true := by
  apply rawChecks_from_cells
  apply List.all_eq_true.mpr
  intro c hc
  simp only [htCells,List.mem_cons,List.not_mem_nil,or_false] at hc
  rcases hc with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  · exact candidateA_cell0_check
  · exact candidateA_cell1_check
  · exact candidateA_cell2_check
  · exact candidateA_cell3_check
  · exact candidateA_cell4_check
  · exact candidateA_cell5_check
  · exact candidateA_cell6_check
  · exact candidateA_cell7_check

theorem candidateA_complete (p : HTPlacement)
    (hp : ShapeContact (htCells .hat) (placementCells p))
    (hd : DisjointCells (htCells .hat) (placementCells p)) :
    p ∈ candidateList .hat :=
  candidateList_complete_of_check .hat candidateA_raw_check p hp hd
end SpectreClusters.StageA
