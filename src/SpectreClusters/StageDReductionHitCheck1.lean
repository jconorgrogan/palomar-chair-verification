module

public import SpectreClusters.StageDReductionHitData
public import SpectreClusters.StageDReductionHitModel

@[expose] public section


namespace SpectreClusters.StageD.Reduction

set_option maxRecDepth 100000 in
theorem rawHit4_checked : allRawHitCheckB .t7h 1737 = true := by rfl
theorem hit4_checked : hitCheckB kept (hitAt 4) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit4_checked
set_option maxRecDepth 100000 in
theorem rawHit5_checked : allRawHitCheckB .t7h 4363 = true := by rfl
theorem hit5_checked : hitCheckB kept (hitAt 5) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit5_checked
set_option maxRecDepth 100000 in
theorem rawHit6_checked : allRawHitCheckB .t7h 5903 = true := by rfl
theorem hit6_checked : hitCheckB kept (hitAt 6) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit6_checked
set_option maxRecDepth 100000 in
theorem rawHit7_checked : allRawHitCheckB .t7h 5963 = true := by rfl
theorem hit7_checked : hitCheckB kept (hitAt 7) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit7_checked
end SpectreClusters.StageD.Reduction
