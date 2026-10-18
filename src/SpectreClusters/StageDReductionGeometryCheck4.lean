module

public import SpectreClusters.StageDReductionGeometryData

@[expose] public section

namespace SpectreClusters.StageD.Reduction
set_option maxRecDepth 100000 in
private theorem geometry_piece_0 : [256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_1 : [272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_2 : [288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_3 : [304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
theorem geometryPart4_checked : [256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271,272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287,288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303,304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319].all (fun n => geometryCheckB (geometryAt n)) = true := by
  change ([256,257,258,259,260,261,262,263,264,265,266,267,268,269,270,271] ++ [272,273,274,275,276,277,278,279,280,281,282,283,284,285,286,287] ++ [288,289,290,291,292,293,294,295,296,297,298,299,300,301,302,303] ++ [304,305,306,307,308,309,310,311,312,313,314,315,316,317,318,319]).all (fun n => geometryCheckB (geometryAt n)) = true
  simp only [List.all_append]
  rw [geometry_piece_0, geometry_piece_1, geometry_piece_2, geometry_piece_3] <;> rfl
end SpectreClusters.StageD.Reduction
