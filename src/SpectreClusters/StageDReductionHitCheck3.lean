module

public import SpectreClusters.StageDReductionHitData
public import SpectreClusters.StageDReductionHitModel

@[expose] public section


namespace SpectreClusters.StageD.Reduction

set_option maxRecDepth 100000 in
theorem rawHit12_checked : allRawHitCheckB .t7h 9014 = true := by rfl
theorem hit12_checked : hitCheckB kept (hitAt 12) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit12_checked
set_option maxRecDepth 100000 in
theorem rawHit13_checked : allRawHitCheckB .t7h 9074 = true := by rfl
theorem hit13_checked : hitCheckB kept (hitAt 13) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit13_checked
set_option maxRecDepth 100000 in
theorem rawHit14_checked : allRawHitCheckB .t7h 9078 = true := by rfl
theorem hit14_checked : hitCheckB kept (hitAt 14) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit14_checked
set_option maxRecDepth 100000 in
theorem rawHit15_checked : allRawHitCheckB .t7h 9643 = true := by rfl
theorem hit15_checked : hitCheckB kept (hitAt 15) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit15_checked
end SpectreClusters.StageD.Reduction
