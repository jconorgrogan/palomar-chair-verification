module

public import SpectreClusters.StageDReductionGeometryData

@[expose] public section

namespace SpectreClusters.StageD.Reduction
set_option maxRecDepth 100000 in
private theorem geometry_piece_0 : [832,833,834,835,836,837,838,839,840,841,842,843,844,845,846,847].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_1 : [848,849,850,851,852,853,854,855,856,857,858,859,860,861,862,863].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_2 : [864,865,866,867,868,869,870,871,872,873,874,875,876,877,878,879].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_3 : [880,881,882,883,884,885,886,887,888,889,890,891,892,893,894,895].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
theorem geometryPart13_checked : [832,833,834,835,836,837,838,839,840,841,842,843,844,845,846,847,848,849,850,851,852,853,854,855,856,857,858,859,860,861,862,863,864,865,866,867,868,869,870,871,872,873,874,875,876,877,878,879,880,881,882,883,884,885,886,887,888,889,890,891,892,893,894,895].all (fun n => geometryCheckB (geometryAt n)) = true := by
  change ([832,833,834,835,836,837,838,839,840,841,842,843,844,845,846,847] ++ [848,849,850,851,852,853,854,855,856,857,858,859,860,861,862,863] ++ [864,865,866,867,868,869,870,871,872,873,874,875,876,877,878,879] ++ [880,881,882,883,884,885,886,887,888,889,890,891,892,893,894,895]).all (fun n => geometryCheckB (geometryAt n)) = true
  simp only [List.all_append]
  rw [geometry_piece_0, geometry_piece_1, geometry_piece_2, geometry_piece_3] <;> rfl
end SpectreClusters.StageD.Reduction
