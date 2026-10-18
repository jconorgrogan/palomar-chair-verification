module

public import SpectreClusters.StageDReductionGeometryData

@[expose] public section

namespace SpectreClusters.StageD.Reduction
set_option maxRecDepth 100000 in
private theorem geometry_piece_0 : [576,577,578,579,580,581,582,583,584,585,586,587,588,589,590,591].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_1 : [592,593,594,595,596,597,598,599,600,601,602,603,604,605,606,607].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_2 : [608,609,610,611,612,613,614,615,616,617,618,619,620,621,622,623].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
set_option maxRecDepth 100000 in
private theorem geometry_piece_3 : [624,625,626,627,628,629,630,631,632,633,634,635,636,637,638,639].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
theorem geometryPart9_checked : [576,577,578,579,580,581,582,583,584,585,586,587,588,589,590,591,592,593,594,595,596,597,598,599,600,601,602,603,604,605,606,607,608,609,610,611,612,613,614,615,616,617,618,619,620,621,622,623,624,625,626,627,628,629,630,631,632,633,634,635,636,637,638,639].all (fun n => geometryCheckB (geometryAt n)) = true := by
  change ([576,577,578,579,580,581,582,583,584,585,586,587,588,589,590,591] ++ [592,593,594,595,596,597,598,599,600,601,602,603,604,605,606,607] ++ [608,609,610,611,612,613,614,615,616,617,618,619,620,621,622,623] ++ [624,625,626,627,628,629,630,631,632,633,634,635,636,637,638,639]).all (fun n => geometryCheckB (geometryAt n)) = true
  simp only [List.all_append]
  rw [geometry_piece_0, geometry_piece_1, geometry_piece_2, geometry_piece_3] <;> rfl
end SpectreClusters.StageD.Reduction
