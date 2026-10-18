module

public import SpectreClusters.StageDReductionHitData
public import SpectreClusters.StageDReductionHitModel

@[expose] public section


namespace SpectreClusters.StageD.Reduction

set_option maxRecDepth 100000 in
theorem rawHit32_checked : allRawHitCheckB .t7h 14319 = true := by rfl
theorem hit32_checked : hitCheckB kept (hitAt 32) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit32_checked
set_option maxRecDepth 100000 in
theorem rawHit33_checked : allRawHitCheckB .t7h 14901 = true := by rfl
theorem hit33_checked : hitCheckB kept (hitAt 33) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit33_checked
set_option maxRecDepth 100000 in
theorem rawHit34_checked : allRawHitCheckB .t7h 14961 = true := by rfl
theorem hit34_checked : hitCheckB kept (hitAt 34) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit34_checked
set_option maxRecDepth 100000 in
theorem rawHit35_checked : allRawHitCheckB .t7h 14965 = true := by rfl
theorem hit35_checked : hitCheckB kept (hitAt 35) = true := by
  apply hitCheckB_of_all_raw
  · intro i hi
    exact List.mem_range.mp hi
  · exact rawHit35_checked
end SpectreClusters.StageD.Reduction
