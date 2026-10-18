module

public import SpectreClusters.StageDReductionGeometryData

@[expose] public section

namespace SpectreClusters.StageD.Reduction
set_option maxRecDepth 100000 in
private theorem geometry_piece_0 : [448,449,450,451,452,453,454,455,456,457,458,459,460,461,462,463].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_1 : [464,465,466,467,468,469,470,471,472,473,474,475,476,477,478,479].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_2 : [480,481,482,483,484,485,486,487,488,489,490,491,492,493,494,495].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_3 : [496,497,498,499,500,501,502,503,504,505,506,507,508,509,510,511].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
theorem geometryPart7_checked : [448,449,450,451,452,453,454,455,456,457,458,459,460,461,462,463,464,465,466,467,468,469,470,471,472,473,474,475,476,477,478,479,480,481,482,483,484,485,486,487,488,489,490,491,492,493,494,495,496,497,498,499,500,501,502,503,504,505,506,507,508,509,510,511].all (fun n => geometryCheckB (geometryAt n)) = true := by
  change ([448,449,450,451,452,453,454,455,456,457,458,459,460,461,462,463] ++ [464,465,466,467,468,469,470,471,472,473,474,475,476,477,478,479] ++ [480,481,482,483,484,485,486,487,488,489,490,491,492,493,494,495] ++ [496,497,498,499,500,501,502,503,504,505,506,507,508,509,510,511]).all (fun n => geometryCheckB (geometryAt n)) = true
  simp only [List.all_append]
  rw [geometry_piece_0, geometry_piece_1, geometry_piece_2, geometry_piece_3] <;> rfl
end SpectreClusters.StageD.Reduction
