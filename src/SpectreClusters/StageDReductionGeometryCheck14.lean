module

public import SpectreClusters.StageDReductionGeometryData

@[expose] public section

namespace SpectreClusters.StageD.Reduction
set_option maxRecDepth 100000 in
private theorem geometry_piece_0 : [896,897,898,899,900,901,902,903,904,905,906,907,908,909,910,911].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_1 : [912,913,914,915,916,917,918,919,920,921,922,923,924,925,926,927].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_2 : [928,929,930,931,932].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
theorem geometryPart14_checked : [896,897,898,899,900,901,902,903,904,905,906,907,908,909,910,911,912,913,914,915,916,917,918,919,920,921,922,923,924,925,926,927,928,929,930,931,932].all (fun n => geometryCheckB (geometryAt n)) = true := by
  change ([896,897,898,899,900,901,902,903,904,905,906,907,908,909,910,911] ++ [912,913,914,915,916,917,918,919,920,921,922,923,924,925,926,927] ++ [928,929,930,931,932]).all (fun n => geometryCheckB (geometryAt n)) = true
  simp only [List.all_append]
  rw [geometry_piece_0, geometry_piece_1, geometry_piece_2] <;> rfl
end SpectreClusters.StageD.Reduction
