module

public import SpectreClusters.StageDReductionGeometryData

@[expose] public section

namespace SpectreClusters.StageD.Reduction
set_option maxRecDepth 100000 in
private theorem geometry_piece_0 : [704,705,706,707,708,709,710,711,712,713,714,715,716,717,718,719].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_1 : [720,721,722,723,724,725,726,727,728,729,730,731,732,733,734,735].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_2 : [736,737,738,739,740,741,742,743,744,745,746,747,748,749,750,751].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_3 : [752,753,754,755,756,757,758,759,760,761,762,763,764,765,766,767].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
theorem geometryPart11_checked : [704,705,706,707,708,709,710,711,712,713,714,715,716,717,718,719,720,721,722,723,724,725,726,727,728,729,730,731,732,733,734,735,736,737,738,739,740,741,742,743,744,745,746,747,748,749,750,751,752,753,754,755,756,757,758,759,760,761,762,763,764,765,766,767].all (fun n => geometryCheckB (geometryAt n)) = true := by
  change ([704,705,706,707,708,709,710,711,712,713,714,715,716,717,718,719] ++ [720,721,722,723,724,725,726,727,728,729,730,731,732,733,734,735] ++ [736,737,738,739,740,741,742,743,744,745,746,747,748,749,750,751] ++ [752,753,754,755,756,757,758,759,760,761,762,763,764,765,766,767]).all (fun n => geometryCheckB (geometryAt n)) = true
  simp only [List.all_append]
  rw [geometry_piece_0, geometry_piece_1, geometry_piece_2, geometry_piece_3] <;> rfl
end SpectreClusters.StageD.Reduction
