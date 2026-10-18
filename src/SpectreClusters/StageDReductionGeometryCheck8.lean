module

public import SpectreClusters.StageDReductionGeometryData

@[expose] public section

namespace SpectreClusters.StageD.Reduction
set_option maxRecDepth 100000 in
private theorem geometry_piece_0 : [512,513,514,515,516,517,518,519,520,521,522,523,524,525,526,527].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_1 : [528,529,530,531,532,533,534,535,536,537,538,539,540,541,542,543].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_2 : [544,545,546,547,548,549,550,551,552,553,554,555,556,557,558,559].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_3 : [560,561,562,563,564,565,566,567,568,569,570,571,572,573,574,575].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
theorem geometryPart8_checked : [512,513,514,515,516,517,518,519,520,521,522,523,524,525,526,527,528,529,530,531,532,533,534,535,536,537,538,539,540,541,542,543,544,545,546,547,548,549,550,551,552,553,554,555,556,557,558,559,560,561,562,563,564,565,566,567,568,569,570,571,572,573,574,575].all (fun n => geometryCheckB (geometryAt n)) = true := by
  change ([512,513,514,515,516,517,518,519,520,521,522,523,524,525,526,527] ++ [528,529,530,531,532,533,534,535,536,537,538,539,540,541,542,543] ++ [544,545,546,547,548,549,550,551,552,553,554,555,556,557,558,559] ++ [560,561,562,563,564,565,566,567,568,569,570,571,572,573,574,575]).all (fun n => geometryCheckB (geometryAt n)) = true
  simp only [List.all_append]
  rw [geometry_piece_0, geometry_piece_1, geometry_piece_2, geometry_piece_3] <;> rfl
end SpectreClusters.StageD.Reduction
