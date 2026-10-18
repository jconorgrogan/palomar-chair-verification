module

public import SpectreClusters.StageDReductionGeometryData

@[expose] public section

namespace SpectreClusters.StageD.Reduction
set_option maxRecDepth 100000 in
private theorem geometry_piece_0 : [128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_1 : [144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_2 : [160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_3 : [176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
theorem geometryPart2_checked : [128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143,144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159,160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175,176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191].all (fun n => geometryCheckB (geometryAt n)) = true := by
  change ([128,129,130,131,132,133,134,135,136,137,138,139,140,141,142,143] ++ [144,145,146,147,148,149,150,151,152,153,154,155,156,157,158,159] ++ [160,161,162,163,164,165,166,167,168,169,170,171,172,173,174,175] ++ [176,177,178,179,180,181,182,183,184,185,186,187,188,189,190,191]).all (fun n => geometryCheckB (geometryAt n)) = true
  simp only [List.all_append]
  rw [geometry_piece_0, geometry_piece_1, geometry_piece_2, geometry_piece_3] <;> rfl
end SpectreClusters.StageD.Reduction
