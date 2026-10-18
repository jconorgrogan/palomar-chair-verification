module

public import SpectreClusters.StageDReductionFastDecoder

@[expose] public section

namespace SpectreClusters.StageD.Reduction
set_option maxRecDepth 100000 in
theorem rowPart0T7H0_sub0_checked : [0,1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31].all (stepCheckB tables 0 .t7h) = true := by
  rw [← fastStepCheckB_eq_fun]
  rfl
end SpectreClusters.StageD.Reduction
