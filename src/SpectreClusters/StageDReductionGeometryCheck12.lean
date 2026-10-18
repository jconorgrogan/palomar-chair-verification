module

public import SpectreClusters.StageDReductionGeometryData

@[expose] public section

namespace SpectreClusters.StageD.Reduction
set_option maxRecDepth 100000 in
private theorem geometry_piece_0 : [768,769,770,771,772,773,774,775,776,777,778,779,780,781,782,783].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_1 : [784,785,786,787,788,789,790,791,792,793,794,795,796,797,798,799].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_2 : [800,801,802,803,804,805,806,807,808,809,810,811,812,813,814,815].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_3 : [816,817,818,819,820,821,822,823,824,825,826,827,828,829,830,831].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
theorem geometryPart12_checked : [768,769,770,771,772,773,774,775,776,777,778,779,780,781,782,783,784,785,786,787,788,789,790,791,792,793,794,795,796,797,798,799,800,801,802,803,804,805,806,807,808,809,810,811,812,813,814,815,816,817,818,819,820,821,822,823,824,825,826,827,828,829,830,831].all (fun n => geometryCheckB (geometryAt n)) = true := by
  change ([768,769,770,771,772,773,774,775,776,777,778,779,780,781,782,783] ++ [784,785,786,787,788,789,790,791,792,793,794,795,796,797,798,799] ++ [800,801,802,803,804,805,806,807,808,809,810,811,812,813,814,815] ++ [816,817,818,819,820,821,822,823,824,825,826,827,828,829,830,831]).all (fun n => geometryCheckB (geometryAt n)) = true
  simp only [List.all_append]
  rw [geometry_piece_0, geometry_piece_1, geometry_piece_2, geometry_piece_3] <;> rfl
end SpectreClusters.StageD.Reduction
