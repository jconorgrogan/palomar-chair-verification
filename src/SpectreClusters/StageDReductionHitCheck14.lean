module

public import SpectreClusters.StageDReductionHitData
public import SpectreClusters.StageDReductionHitModel

@[expose] public section


namespace SpectreClusters.StageD.Reduction

set_option maxRecDepth 100000 in
theorem rawHit56_checked : allRawHitCheckB .t8h 694306383483 = true := by rfl
theorem hit56_checked : hitCheckB kept (hitAt 56) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit56_checked
set_option maxRecDepth 100000 in
theorem rawHit57_checked : allRawHitCheckB .t8h 724320822363 = true := by rfl
theorem hit57_checked : hitCheckB kept (hitAt 57) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit57_checked
set_option maxRecDepth 100000 in
theorem rawHit58_checked : allRawHitCheckB .t8h 724337599579 = true := by rfl
theorem hit58_checked : hitCheckB kept (hitAt 58) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit58_checked
set_option maxRecDepth 100000 in
theorem rawHit59_checked : allRawHitCheckB .t8h 835451587790 = true := by rfl
theorem hit59_checked : hitCheckB kept (hitAt 59) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit59_checked
end SpectreClusters.StageD.Reduction
