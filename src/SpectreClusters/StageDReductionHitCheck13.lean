module

public import SpectreClusters.StageDReductionHitData
public import SpectreClusters.StageDReductionHitModel

@[expose] public section


namespace SpectreClusters.StageD.Reduction

set_option maxRecDepth 100000 in
theorem rawHit52_checked : allRawHitCheckB .t8h 660898734649 = true := by rfl
theorem hit52_checked : hitCheckB kept (hitAt 52) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit52_checked
set_option maxRecDepth 100000 in
theorem rawHit53_checked : allRawHitCheckB .t8h 660932289081 = true := by rfl
theorem hit53_checked : hitCheckB kept (hitAt 53) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit53_checked
set_option maxRecDepth 100000 in
theorem rawHit54_checked : allRawHitCheckB .t8h 660938580537 = true := by rfl
theorem hit54_checked : hitCheckB kept (hitAt 54) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit54_checked
set_option maxRecDepth 100000 in
theorem rawHit55_checked : allRawHitCheckB .t8h 660946969137 = true := by rfl
theorem hit55_checked : hitCheckB kept (hitAt 55) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit55_checked
end SpectreClusters.StageD.Reduction
