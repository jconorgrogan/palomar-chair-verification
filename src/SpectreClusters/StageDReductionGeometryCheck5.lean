module

public import SpectreClusters.StageDReductionGeometryData

@[expose] public section

namespace SpectreClusters.StageD.Reduction
set_option maxRecDepth 100000 in
private theorem geometry_piece_0 : [320,321,322,323,324,325,326,327,328,329,330,331,332,333,334,335].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_1 : [336,337,338,339,340,341,342,343,344,345,346,347,348,349,350,351].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_2 : [352,353,354,355,356,357,358,359,360,361,362,363,364,365,366,367].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_3 : [368,369,370,371,372,373,374,375,376,377,378,379,380,381,382,383].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
theorem geometryPart5_checked : [320,321,322,323,324,325,326,327,328,329,330,331,332,333,334,335,336,337,338,339,340,341,342,343,344,345,346,347,348,349,350,351,352,353,354,355,356,357,358,359,360,361,362,363,364,365,366,367,368,369,370,371,372,373,374,375,376,377,378,379,380,381,382,383].all (fun n => geometryCheckB (geometryAt n)) = true := by
  change ([320,321,322,323,324,325,326,327,328,329,330,331,332,333,334,335] ++ [336,337,338,339,340,341,342,343,344,345,346,347,348,349,350,351] ++ [352,353,354,355,356,357,358,359,360,361,362,363,364,365,366,367] ++ [368,369,370,371,372,373,374,375,376,377,378,379,380,381,382,383]).all (fun n => geometryCheckB (geometryAt n)) = true
  simp only [List.all_append]
  rw [geometry_piece_0, geometry_piece_1, geometry_piece_2, geometry_piece_3] <;> rfl
end SpectreClusters.StageD.Reduction
