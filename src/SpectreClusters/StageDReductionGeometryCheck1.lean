module

public import SpectreClusters.StageDReductionGeometryData

@[expose] public section

namespace SpectreClusters.StageD.Reduction
set_option maxRecDepth 100000 in
private theorem geometry_piece_0 : [64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_1 : [80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_2 : [96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_3 : [112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
theorem geometryPart1_checked : [64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79,80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95,96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111,112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127].all (fun n => geometryCheckB (geometryAt n)) = true := by
  change ([64,65,66,67,68,69,70,71,72,73,74,75,76,77,78,79] ++ [80,81,82,83,84,85,86,87,88,89,90,91,92,93,94,95] ++ [96,97,98,99,100,101,102,103,104,105,106,107,108,109,110,111] ++ [112,113,114,115,116,117,118,119,120,121,122,123,124,125,126,127]).all (fun n => geometryCheckB (geometryAt n)) = true
  simp only [List.all_append]
  rw [geometry_piece_0, geometry_piece_1, geometry_piece_2, geometry_piece_3] <;> rfl
end SpectreClusters.StageD.Reduction
