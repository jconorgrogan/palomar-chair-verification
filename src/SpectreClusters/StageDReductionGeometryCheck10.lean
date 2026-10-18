module

public import SpectreClusters.StageDReductionGeometryData

@[expose] public section

namespace SpectreClusters.StageD.Reduction
set_option maxRecDepth 100000 in
private theorem geometry_piece_0 : [640,641,642,643,644,645,646,647,648,649,650,651,652,653,654,655].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_1 : [656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_2 : [672,673,674,675,676,677,678,679,680,681,682,683,684,685,686,687].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_3 : [688,689,690,691,692,693,694,695,696,697,698,699,700,701,702,703].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
theorem geometryPart10_checked : [640,641,642,643,644,645,646,647,648,649,650,651,652,653,654,655,656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671,672,673,674,675,676,677,678,679,680,681,682,683,684,685,686,687,688,689,690,691,692,693,694,695,696,697,698,699,700,701,702,703].all (fun n => geometryCheckB (geometryAt n)) = true := by
  change ([640,641,642,643,644,645,646,647,648,649,650,651,652,653,654,655] ++ [656,657,658,659,660,661,662,663,664,665,666,667,668,669,670,671] ++ [672,673,674,675,676,677,678,679,680,681,682,683,684,685,686,687] ++ [688,689,690,691,692,693,694,695,696,697,698,699,700,701,702,703]).all (fun n => geometryCheckB (geometryAt n)) = true
  simp only [List.all_append]
  rw [geometry_piece_0, geometry_piece_1, geometry_piece_2, geometry_piece_3] <;> rfl
end SpectreClusters.StageD.Reduction
