module

public import SpectreClusters.StageDReductionLiteralReplay

@[expose] public section

namespace SpectreClusters.StageD.Reduction
private theorem row_step_139 : stepCheckB tables 2 .t7h 139 = true := by
  rw [← fastStepCheckB_eq]
  simp only [fastStepCheckB,Bool.or_eq_true]
  left
  decide
private theorem row_step_140 : stepCheckB tables 2 .t7h 140 = true := by
  rw [← fastStepCheckB_eq]
  simp only [fastStepCheckB,Bool.or_eq_true]
  left
  decide
theorem rowPart2T7H0_checked : [139,140].all (stepCheckB tables 2 .t7h) = true := by
  simp only [List.all_cons,List.all_nil,row_step_139,row_step_140,Bool.true_and]
end SpectreClusters.StageD.Reduction
