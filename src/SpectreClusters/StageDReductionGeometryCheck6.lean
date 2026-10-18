module

public import SpectreClusters.StageDReductionGeometryData

@[expose] public section

namespace SpectreClusters.StageD.Reduction
set_option maxRecDepth 100000 in
private theorem geometry_piece_0 : [384,385,386,387,388,389,390,391,392,393,394,395,396,397,398,399].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_1 : [400,401,402,403,404,405,406,407,408,409,410,411,412,413,414,415].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_2 : [416,417,418,419,420,421,422,423,424,425,426,427,428,429,430,431].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_3 : [432,433,434,435,436,437,438,439,440,441,442,443,444,445,446,447].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
theorem geometryPart6_checked : [384,385,386,387,388,389,390,391,392,393,394,395,396,397,398,399,400,401,402,403,404,405,406,407,408,409,410,411,412,413,414,415,416,417,418,419,420,421,422,423,424,425,426,427,428,429,430,431,432,433,434,435,436,437,438,439,440,441,442,443,444,445,446,447].all (fun n => geometryCheckB (geometryAt n)) = true := by
  change ([384,385,386,387,388,389,390,391,392,393,394,395,396,397,398,399] ++ [400,401,402,403,404,405,406,407,408,409,410,411,412,413,414,415] ++ [416,417,418,419,420,421,422,423,424,425,426,427,428,429,430,431] ++ [432,433,434,435,436,437,438,439,440,441,442,443,444,445,446,447]).all (fun n => geometryCheckB (geometryAt n)) = true
  simp only [List.all_append]
  rw [geometry_piece_0, geometry_piece_1, geometry_piece_2, geometry_piece_3] <;> rfl
end SpectreClusters.StageD.Reduction
