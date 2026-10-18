module

public import SpectreClusters.StageDReductionGeometryData

@[expose] public section


namespace SpectreClusters.StageD.Reduction

set_option maxRecDepth 100000 in
theorem geometryPart0_checked :
  [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37,38,39,40,41,42,43,44,45,46,47,48,49,50,51,52,53,54,55,56,57,58,59,60,61,62,63].all (fun n => geometryCheckB (geometryAt n)) = true := by rfl
end SpectreClusters.StageD.Reduction
