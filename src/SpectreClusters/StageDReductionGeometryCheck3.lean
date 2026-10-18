module

public import SpectreClusters.StageDReductionGeometryData

@[expose] public section

namespace SpectreClusters.StageD.Reduction
set_option maxRecDepth 100000 in
private theorem geometry_piece_0 : [192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_1 : [208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_2 : [224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_3 : [240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
theorem geometryPart3_checked : [192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207,208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223,224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239,240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255].all (fun n => geometryCheckB (geometryAt n)) = true := by
  change ([192,193,194,195,196,197,198,199,200,201,202,203,204,205,206,207] ++ [208,209,210,211,212,213,214,215,216,217,218,219,220,221,222,223] ++ [224,225,226,227,228,229,230,231,232,233,234,235,236,237,238,239] ++ [240,241,242,243,244,245,246,247,248,249,250,251,252,253,254,255]).all (fun n => geometryCheckB (geometryAt n)) = true
  simp only [List.all_append]
  rw [geometry_piece_0, geometry_piece_1, geometry_piece_2, geometry_piece_3] <;> rfl
end SpectreClusters.StageD.Reduction
